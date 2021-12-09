#lang rosette

(require rosette/lib/destruct)

(require "utils.rkt")
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
; treatements programatically. Properties are usually symbols (e.g. 'ACE-Inhibitor, 'Diuretic)
;
; Notes:
; - We treat the list of requirements as a syntactic convenience for providing a
;   *conjunction* of all requirements in the list.
(struct drug (name requirements properties) #:transparent)

; A known treatment has
; - A list of one or more ailments it treats
; - A set of requirements about the patient to be applicable
; - A formula depicting a drug combination that treats the ailments, i.e.
;     drug A, drug A /\ drug B, drug A /\ (drug B \/ drug C), etc.
(struct treatment (ailments requirements formula))


; A requirement can be any of following, where `f` is a predicate takes in
; a patient's information and returns true or false:

(struct AGE (f))
(struct ALLERGY (f))
(struct NOT (requirement))
(struct AND (a b))
(struct OR (a b))

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

; A condition extends the `requirement` type with the ability to specify
; other drugs, which are interepreted as "true" values if the patient is taking a
; drug of that name. For example:
; '(drug-name)
(struct REQUIREMENT (r))

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

; A drug database contains our "universe" of information -- these
; are all of the drugs we know about, all of the known conflicts
; in-between them, and all of the known treatments we have for different
; ailments making use of these drugs.
;
; Idea: while all "conflicts" in the database must be concrete conflict
; triples, we can expose a DSL front-end that allows us to define conflicts
; in a predicate style: i.e. drug A with active ingredient I conflicts with
; any drug B that has some active ingredient J under certain conditions. Then
; this predicate is evaluated against each drug B != A in the database to create
; the relations. (This may be a reasonable way to generate data-sets.)
(struct database (drugs conflicts treatments))

; Attempt to reduce the size of the symbolic union
(define (prescription-contains prescription drug)
  (contains? prescription drug))

; We can check if a prescription (defined as a set of drugs) satisfies a formula to
; constitute a valid treatment application for a given patient/ailment combination:
(define (treats-ailment treatment patient prescription ailment)
  (and
   ; The ailment is actually contained within the list of ailments this treatment treats
   (contains? (treatment-ailments treatment) ailment)

   ; Patients satisfy all of the requirements for the treatment to apply
   (andmap (curry satisfies-requirement patient) (treatment-requirements treatment))

   ; The prescription actually satisfied the treatment's requirements.
   (begin
     (define (satisfies-formula prescription formula)
       (define recurse (curry satisfies-formula prescription))
       (destruct formula
                 [ (NOT c) (not (recurse c)) ]
                 [ (OR a b) (or (recurse a) (recurse b)) ]
                 [ (AND a b) (and (recurse a) (recurse b)) ]
                 [ (list drugs ...) (andmap (curry prescription-contains prescription) drugs) ]))
     (satisfies-formula prescription (treatment-formula treatment)))
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
                    (treats-ailment treatment patient prescription ailment))
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
                              (define found (findf (λ (elt) (eq? (drug-name elt) drug)) drugs))
                              (if found (drug-requirements found) '()))
                            '()))
                      prescription)))
        ; (printf "\t\tpatient-requirements: ~a\n" requirements-list)
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

; Abstract over DB creation + syntax.
(define (make-database #:drugs drugs #:conflicts conflicts #:treatments treatments)
  ; Optimize here to construct hash tables to reduce the amount of comparisons.
  (database drugs conflicts treatments))

(define (lte a) (λ (b) (<= b a)))
(define (gte a) (λ (b) (>= b a)))

(define (any-allergy . as)
  (ALLERGY (λ (allergies)
             (ormap (curry contains? allergies) as)) ))

; TODO: define a global database, or generate them on the fly from
;  random data and random global properties (see above)
(define drug-database
  (make-database
   #:drugs ; drug: name, patient requirements, properties
   (list
    (drug 'A  '() '())
    (drug 'B  '() '())
    (drug 'C  '() '())
    (drug 'D  '() '())
    (drug 'E  '() '())
    (drug 'A1  '() '())
    (drug 'B1  '() '())
    (drug 'C1  '() '())
    (drug 'D1  '() '())
    (drug 'E1  '() '())
    (drug 'A2  '() '())
    (drug 'B2  '() '())
    (drug 'C2  '() '())
    (drug 'D2  '() '())
    (drug 'E2  '() '())
    )
   #:conflicts ; conflict: two drug names and a condition
   (list

    (conflict 'A 'B '()) ; A and B unconditionally conflict.
    (conflict 'A 'C '(E)) ; A and C conflict in the presence of E
    (conflict 'C 'D (REQUIREMENT (any-allergy 'M 'N))) ; C and D conflict if patient has either allergy.
    (conflict 'A 'D (AND ; A and D conflict if the patient is less than age 50 and not taking C.
                     (REQUIREMENT (AGE (lte 50)))
                     (NOT 'C)))
    (conflict 'A1 'B1 '())
    (conflict 'A2 'B2 '())
    (conflict 'B1 'C1 '())
    (conflict 'B2 'C2 '())
    (conflict 'C1 'D1 '())
    (conflict 'C2 'D2 '())
    (conflict 'D1 'E1 '())
    (conflict 'D2 'E2 '())
    )
   #:treatments ; treatement: ailments treated, patient requirements, drug formula
   (list
    (treatment '(X) '() '(A)) ; Drug A treats ailment X unconditionally.
    (treatment '(Y) (list (AGE (gte 2))) '(B)) ; Drug B treats ailment Y if the patient is over age 2.
    (treatment '(Y Z) '() '(C A)) ; Drug C treats ailments Y and Z when used with A.
    (treatment '(W) '() '(D)) ; Drug D treats ailment W unconditionally.
    (treatment '(U) '() '(E (OR B C))) ; Drug E treats ailment U if used with B or C.

    (treatment '(X1) '() '(A1))
    (treatment '(Y1) (list (AGE (gte 2))) '(B1))
    (treatment '(Y1 Z1) '() '(C1 A1))
    (treatment '(W1) '() '(D1))
    (treatment '(U1) '() '(E1 (OR B1 C1)))
    )))


(define (test)
  (define marc (patient 42 '(K) '(X Y)))
  (define possible-prescription-1 '(A B))   ; Conflict
  (define possible-prescription-2 '(A D))   ; No conflict, but also doesn't fit the bill
  (define possible-prescription-3 '(A C E)) ; Transitive conflict
  (define possible-prescription-4 '(A C D)) ; A and D conflict due to age, but OK because of C
  (define possible-prescription-5 '(A C))   ; Treats X and Y, no conflict. Ship it!

  (displayln (verify-prescription drug-database marc possible-prescription-1))
  (displayln (verify-prescription drug-database marc possible-prescription-2))
  (displayln (verify-prescription drug-database marc possible-prescription-3))
  (displayln (verify-prescription drug-database marc possible-prescription-4))
  (displayln (verify-prescription drug-database marc possible-prescription-5)))

(test)

(define (display-prescription prescription)
  (displayln (filter identity prescription)))

; For testing purposes, we want to see if our verifier returns true/false on any
; possible permutation of input prescriptions. While this is mostly intended to make sure
; our verifier code doesn't crash, it also makes sense as an exhaustive search. This search
; is exponential in the size of the database, which is where the solver comes in.
(define (exhaustive-test all-drugs)
  (define marc (patient 42 '(K) '(X Y))) ; Our (ailing) hero returns!

  ; Lightly modified from:
  ; https://stackoverflow.com/questions/20622945/how-to-do-a-powerset-in-drracket/20623487
  (define (powerset aL)
    (if (empty? aL) '(())
        (let ([rst (powerset (rest aL))])
          (append (map (λ (x) (cons (first aL) x)) rst) rst))))

  (define all-possible-prescriptions
    (map (λ (ps)
           (map (λ (drug) (find ps drug)) all-drugs))
         (powerset all-drugs)))

  ;  (printf "Generated powerset of size ~a\n" (length all-possible-prescriptions))

  (define (check prescription)
    (define result (verify-prescription drug-database marc prescription))
    ; (printf "~a: ~a\n" prescription result)
    result)

  (define valid-prescriptions
    (map (curry filter identity)
         (filter check all-possible-prescriptions)))
  ; And indeed, we see that only ACD and AC are valid prescriptions :)
  (print-upto 5 "Exhaustive search" valid-prescriptions))

(define (test-permutations)
  (time (exhaustive-test '(A B C D E)))
  ; Uncomment this test for benchmarking (warning: takes a while!)
  ; (time (exhaustive-test (map drug-name (database-drugs drug-database))))
  )

(test-permutations)

; Generate a prescription for a patient from a database, without taking into account any
; existing prescription.
(define (generate-prescription database patient)
  (define (new-variable name) (define-symbolic* name boolean?) name)
  (define all-drugs (map drug-name (database-drugs database)))
  (define symbolic-variables (map new-variable all-drugs))
  (define check (curry verify-prescription drug-database patient))
  (define symbolic-prescription
    (map (λ (drug var) (if var drug #f)) all-drugs symbolic-variables))
  (define solution
    (solve (assert (check symbolic-prescription))))
  (match solution
    [ (model assignment)
      (evaluate symbolic-prescription solution) ]
    [ 'unsat ??? ]))

(define (test-automated)
  (define marc (patient 42 '(K) '(X Y)))
  (display-prescription (time (generate-prescription drug-database marc)))) ; (A C)

(test-automated)

; Optimize a prescription modification that minimizes the change from an existing prescription.
(define (optimized-prescription database patient existing-prescription)
  (define (new-variable name) (define-symbolic* name boolean?) name)
  (define all-drugs (map drug-name (database-drugs database)))
  (define symbolic-variables (map new-variable all-drugs))
  (define check (curry verify-prescription drug-database patient))
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

; Since Marc is already taking D, we expect to see ACD instead of the A C from before.
(define (test-optimization)
  (define marc (patient 42 '(K) '(X Y)))
  (display-prescription (time (optimized-prescription drug-database marc '(D))))) ; (A C D)

(test-optimization)