#lang rosette

(require rosette/lib/destruct)
(require "utils.rkt")

(provide  (all-defined-out))

; (output-smt #t) ; Debugging: output SMT formula to file.

;;; Prescription Verification and Synthesis Library ;;;

; Design considerations:
; - Our primary language goal is to expose the concept of *parameterized* compatibilities
;   between drugs. Existing drug databases are prone to two classes of errors:
;     - Incompleteness, where two drugs are incompatible due to some known fact
;         but this incompatibility is not in the database.
;     - Spurious errors, where two drugs have been found to be incompatible in
;         some studies of patients under certain conditions, but are in practice
;         widely used together because the conditions are not common.
;
;   We thus expose the primitive of being able to specify *when* two drugs are
;    compatible with each other, taking into account patients properties,
;    pre-existing conditions, and other medications.
;
; - Our primary *implementation* concern is scalability to a large drug database.
;    While patients in even the most complex cases take at most 50 different drugs,
;    the database of *known* drugs is large, and while the patient's drugs may interact
;    with many, many other drugs, only a few of those will be relevant.

; Patients have
; - Properties relevant to medication decisions (age)
; - Pre-existing conditions (allergies)
; - A set of illnesses that they need medication for (ailments)
(struct patient (age allergies ailments) #:transparent)

; Drugs have
; - a unique identifier
; - a set of unconditional requirements that must be met about
; the patient's conditions.
; - an unstructured list of properties that can be referenced when defining
; treatments programatically. Properties are usually symbols (e.g. 'ACE-Inhibitor, 'Diuretic)
;
; Notes:
; - We treat the list of requirements as a syntactic convenience for providing a
;   *conjunction* of all requirements in the list.
(struct drug (name requirements properties) #:transparent)

; A requirement can be any of following, where `f` is a predicate takes in
; a patient's information and returns true or false:
(struct AGE (f))
(struct ALLERGY (f))
(struct BLOOD-PRESSURE (f)) ; ... and so on.

; A known treatment has
; - A list of one or more ailments it treats
; - A set of requirements about the patient to be applicable
; - A formula depicting a drug combination that treats the ailments, i.e.
;     drug A, drug A /\ drug B, drug A /\ (drug B \/ (has-property 'ACE-inhibitor)), etc.
(struct treatment (ailments requirements formula) #:transparent)

; A formula literal can either be a specific drug, or it can be function that takes as input the
; drug's property list and returns true or false if the properties are satisfied. A property in
; a formula is considered to be true if any of the drugs satisfy the property.
(struct PROPERTY (f))


; This definition admits the following verifier:
(define (satisfies-requirement patient requirement)
  (define recurse (curry satisfies-requirement patient))
  (destruct requirement
            [ (AGE f) (f (patient-age patient))]
            [ (ALLERGY f) (f (patient-allergies patient))]
            [ (NOT r)   (not (recurse r)) ]
            [ (OR a b)  (or (recurse a) (recurse b)) ]
            [ (AND a b) (and (recurse a) (recurse b)) ]
            ))

; A conflict relation says that drug A conflicts with drug B,
; if the condition is true for a given patient and drug list.
(struct conflict (A B condition) #:transparent)

; A conflict-class says that any drug that satisfies the predicate A
; conflicts with any drug that satisfies predicate B, if condition is true.
; This desugars down to many individual conflict relations in our encoding.
(struct conflict-class (propertyA propertyB condition))

; A condition extends the `requirement` type with the ability to specify drugs as
; literals, which are interepreted as "true" values if the patient is taking a drug of
; that name. For example:
;     'REQUIREMENT(older-than 2) \/ (B C)
; says that the patient is be older than 2 or prescribed both B and C.
; Note that conditions are used in *conflicts*, so the drugs conflict when a condition is *true*
(struct REQUIREMENT (r) #:transparent)


; We also expose boolean combinations for requirements, conditions, and formulas.
(struct NOT (a))
(struct AND (a b))
(struct OR (a b))

; Together, these admit the following verifier, which verifies if two
; drugs conflict given a patient and existing series of drugs.
; (Note, this does not check if adding either of the two drugs to the
;  medications list would cause conflicts to occur with any there.)
(define (drugs-conflict patient medications condition)
  (define recurse (curry drugs-conflict patient medications))
  (destruct condition
            [ (REQUIREMENT r) (satisfies-requirement patient r) ]
            [ (NOT c)  (not (recurse c)) ]
            [ (OR a b) (or (recurse a) (recurse b)) ]
            [ (AND a b) (and (recurse a) (recurse b))  ]
            [ (list drugs ...) (andmap (curry contains? medications) drugs) ]
            [ drug (contains? medications drug) ]
            ))

; A drug database contains our "universe" of information -- these are all of the drugs we
; know about, all of the known conflicts in-between them, and all of the known treatments
; we have for different ailments making use of these drugs.
;
; While all "conflicts" in the database must be concrete conflict triples, we expose a
; construct (`conflict-class`) that allows us to define conflicts in a predicate style:
; i.e. drug A with property P conflicts with any drug B that has some property Q under
; certain conditions. Then this predicate is evaluated against each drug B != A in the
; database to create the relations.
(struct database (drugs conflicts treatments))


; We can check if a prescription (defined as a set of drugs) satisfies a formula to
; constitute a valid treatment application. Here, prescription is a list of names (or false)
; and treatment drugs is a list of #struct drug (or false)
(define (satisfies-treatment-formula treatment-drugs prescription formula)
  (define recurse (curry satisfies-treatment-formula treatment-drugs prescription))
  (destruct formula
            [ (PROPERTY f)
              (ormap (λ (d) (and d (f (drug-properties d)))) treatment-drugs) ]
            [ (NOT c) (not (recurse c)) ]
            [ (OR a b) (or (recurse a) (recurse b)) ]
            [ (AND a b) (and (recurse a) (recurse b)) ]
            [ (list drugs ...) (andmap (curry contains? prescription) drugs) ]))

; (trace satisfies-treatment-formula)

(define (query-drug all-drugs drug)
  (and drug (findf (λ (elt) (eq? (drug-name elt) drug)) all-drugs)))

; Also, check whether a treatment applies to a given patient/ailment combination:
(define (treats-ailment all-drugs treatment patient prescription ailment)
  (define (treatment-drugs) (map (curry query-drug all-drugs) prescription))
  (and
   ; The ailment is actually contained within the list of ailments this treatment treats
   (debug "\tcontains?" (contains? (treatment-ailments treatment) ailment))

   ; Patients satisfy all of the requirements for the treatment to apply
   (debug "\treqs?" (andmap (curry satisfies-requirement patient) (treatment-requirements treatment)))

   ; The prescription actually satisfied the treatment's requirements.
   (debug "\tformula?" (satisfies-treatment-formula (treatment-drugs) prescription (treatment-formula treatment)))
   ))

; Finally, we can write a procedure to verify a candidate prescription for a given patient.
; We assume the presence of a drug database.
;
; A valid prescription (list of drug-names) must satisfiy the following conditions:
; - Treat all of the patient's ailments.
; - Be compatible with the patient's properties and allergies.
; - Be internally consistent -- no drugs can conflict with each other.
;
; We assume prescriptions are well-formed, i.e. that all drugs are present in the database.
;
; Idea: we can extend the notion of a presecription to include dosage and time, and parameterize
;       conflicts between drugs not just on the presence of another drug, but also on some
;       property of its dosage. This changes nothing for verification, but makes synthesis more
;       challenging since now a synthesized prescription must come up with a model of reals (dosages)
;       for each drug as well as a boolean prescribed/not-prescribed.
(define (verify-prescription drug-database patient prescription)
  (destruct
   drug-database
   [(database drugs conflicts treatments)
    (begin
      (define ailments (patient-ailments patient))

      ; Note: naive implementation scans the whole conflict list, instead we probably want
      ; something with a dictionary that looks over just the conflicts of A.
      ; Since `conflicts(A,B) <=> conflicts(B,A)`, we can safely ignore the case where a
      ; conflict is only registered in one direction, since we will always check both.
      (define (query-conflicts a b)
        (filter (λ (c)
                  (&& (equal? (conflict-A c) a) (equal? (conflict-B c) b)))
                conflicts))

      (define (treats-all)
        ; Check that for each ailment the patient has, there is some known treatment
        ; that is applicable via this patient/prescription combination.
        (andmap
         (λ (ailment)
           (ormap (λ (treatment)
                    (treats-ailment drugs treatment patient prescription ailment))
                  treatments))
         ailments))

      (define (patient-compatible)
        (define requirements-list
          ; For each drug in the prescription, find the requirements for the drug with the same name
          ; in the database and aggregate them together.
          (apply append
                 (map (λ (drug)
                        (if drug
                            (begin
                              (define found (query-drug drugs drug))
                              (if found (drug-requirements found) '()))
                            '()))
                      prescription)))
        (andmap (curry satisfies-requirement patient) requirements-list))

      ; Futher optimization: fast exit on first failure since we know it's inconsistent.
      (define (internally-consistent)
        (andmap
         (λ (a)
           (andmap
            (λ (b)
              (or (not (and a b))
                  ; Query all of the relations from the database
                  (begin (define relations (query-conflicts a b))
                         ; No pairs of drugs causes a conflicts.
                         (define result (not (ormap
                                              (curry drugs-conflict patient prescription)
                                              (map conflict-condition relations))))
                         ;  (printf "\t\trelation [~a <-> ~a] ~a => ~a\n" a b relations result)
                         result)))
            prescription))
         prescription))

      ; Short circuit evaluation if a prior condition is false.
      (and
       (debug "treats-all" (treats-all))
       (debug "patient-compatible" (patient-compatible))
       (debug "internally-consistent" (internally-consistent))
       ))
    ]))

(define (satisfies-drug-property property drug)
  (define (recurse p) satisfies-drug-property p drug)
  (destruct property
            [(PROPERTY p) (p (drug-properties drug)) ]
            [ (NOT c) (not (recurse c)) ]
            [ (OR a b) (or (recurse a) (recurse b)) ]
            [ (AND a b) (and (recurse a) (recurse b)) ]
            ))

; Abstract over DB creation + syntax.
(define (make-database #:drugs drugs #:conflicts conflicts #:treatments treatments)
  (define expanded-conflicts
    ;Expand conflict-classes into individual conflicts
    (apply
     append
     (map (λ (cc)
            (destruct cc
                      [ (conflict-class pA pB condition)
                        (define drugs-a (filter (curry satisfies-drug-property pA) drugs))
                        (define drugs-b (filter (curry satisfies-drug-property pB) drugs))
                        (apply append
                               (map (λ (a)
                                      (apply append
                                             (map (λ (b)
                                                    (list (conflict (drug-name a) (drug-name b) condition))
                                                    ) drugs-b)))
                                    drugs-a))
                        ]
                      [ _ (list cc) ])
            ) conflicts)))
  (database drugs expanded-conflicts treatments))


; SYNTACTIC SUGAR for our DSL, allowing a natural encoding of requirements in the struct-function form
(define (younger-than a)
  (AGE (λ (b) (<= b a))))
(define (older-than a)
  (AGE (λ (b) (>= b a))))
(define (any-allergy . as)
  (ALLERGY (λ (allergies) (ormap (curry contains? allergies) as)) ))
(define (both-allergies . as)
  (ALLERGY (λ (allergies) (and (curry contains? allergies) as)) ))
(define (no-allergy . as)
  (ALLERGY (λ (allergies) (not (ormap (curry contains? allergies) as)) )))
(define (has-property . ps)
  (PROPERTY (λ (properties) (andmap (curry contains? properties) ps))))


(define (display-prescription prescription)
  (displayln (filter identity prescription)))

; Generate a prescription for a patient from a database, without taking into account any
; existing prescription.
(define (generate-prescription database patient)
  (define (new-variable name) (define-symbolic* name boolean?) name)
  (define all-drugs (map drug-name (database-drugs database)))
  (define symbolic-variables (map new-variable all-drugs))
  (define check (curry verify-prescription database patient))
  (define symbolic-prescription
    (map (λ (drug var) (if var drug #f)) all-drugs symbolic-variables))
  (define solution
    (solve (assert (check symbolic-prescription))))
  (match solution
    [ (model assignment)
      ; Rosette sometimes returns a partial assignment if it is enough to determine satisfiability,
      ; so here we add the default assignment (#f) for every declared variable.
      (evaluate symbolic-prescription (complete-solution solution symbolic-variables)) ]
    [ 'unsat ??? ]))

; Optimize a prescription modification that minimizes the change from an existing prescription.
(define (optimized-prescription database patient existing-prescription)
  (define (new-variable name) (define-symbolic* name boolean?) name)
  (define all-drugs (map drug-name (database-drugs database)))
  (define symbolic-variables (map new-variable all-drugs))
  (define check (curry verify-prescription database patient))
  (define symbolic-prescription
    (map (λ (drug var) (if var drug #f)) all-drugs symbolic-variables))

  ; We take a pairwise distance between our symbolic variables and current assignment.
  (define current-variables
    (map (λ (drug) (contains? existing-prescription drug)) all-drugs))
  (define symbolic-distance
    (foldl + 0 (map (λ (v1 v2) (if (eq? v1 v2) 0 1)) current-variables symbolic-variables)))

  (define solution
    (optimize
     #:minimize (list symbolic-distance)
     #:guarantee (assert (check symbolic-prescription))))
  (match solution
    [ (model assignment)
      (evaluate symbolic-prescription solution) ]
    [ 'unsat ??? ]))