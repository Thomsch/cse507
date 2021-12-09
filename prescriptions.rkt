#lang rosette

(require rosette/lib/destruct)
; (output-smt #t)

(require "utils.rkt")

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
'('age f)
'('allergy f)
'('not requirement)
'('and a b ...)
'('or a b ...)

; This definition admits the following verifier:
(define (satisfies-requirement patient requirement)
  ; (printf "SATISFIES? ~a\n" requirement)
  (match requirement
    [ `('age ,f) (f (patient-age patient))]
    [ `('allergy ,f) (f (patient-allergies patient))]
    [ `('not ,r) (not (satisfies-requirement patient r)) ]
    [ `('or ,a ...)  (ormap (curry satisfies-requirement patient) a) ]
    [ `('and ,a ...)  (andmap (curry satisfies-requirement patient) a) ]
    ))

; A conflict relation says that drug A conflicts with drug B,
; if the condition is true for a given patient and drug list.
(struct conflict (A B condition) #:transparent)

; A condition extends the `requirement` type with the ability to specify
; other drugs, which are interepreted as "true" values if the patient is taking a
; drug of that name. For example:
'(drug-name)
'('requirement r)

; Together, these admit the following verifier, which verifies if two
; drugs conflict given a patient and existing series of drugs.
; (Note, this does not check if adding either of the two drugs to the
;  medications list would cause conflicts to occur with any there.)
(define (drugs-conflict patient medications condition)
  ; (printf "\t\tConflict? ~a\n" condition)
  (define result
    (match condition
      [ `('requirement ,r)
        ; (displayln "\t\t\tREQUIREMENT")
        (satisfies-requirement patient r) ]
      [ `('not ,c)
        ; (displayln "\t\t\tNOT")
        (not (drugs-conflict patient medications c)) ]
      [ `('or ,c ...)
        ; (displayln "\t\t\tOR")
        (ormap (curry drugs-conflict patient medications) c) ]
      [ `('and ,c ...)
        ; (displayln "\t\t\tAND")
        (andmap (curry drugs-conflict patient medications) c) ]
      [ `(,drugs ...)
        ; (displayln "\t\t\tGENERIC")
        (andmap (curry contains? medications) drugs) ]
      ))
  ; (printf "\t\t\tResult ~a: ~a\n" condition result)
  result)

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
       (match formula
         [ `('not ,f) (not (satisfies-formula prescription f)) ]
         [ `('or ,f ...) (apply || (map (curry satisfies-formula prescription) f)) ]
         [ `('and ,f ...) (andmap (curry satisfies-formula prescription) f) ]
         [ `(,drugs ...) (andmap (curry contains? prescription) drugs) ]
         ))
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
                        (define found (findf (λ (elt) (eq? (drug-name elt) drug)) drugs))
                        (if found (drug-requirements found) '()))
                      prescription)))
        ; (printf "\t\tpatient-requirements: ~a\n" requirements-list)
        (andmap (curry satisfies-requirement patient) requirements-list))

      ; Futher optimization: fast exit on first failure since we know it's inconsistent.
      (define (internally-consistent)
        (andmap
         (λ (a)
           (andmap
            (λ (b)
              ; Query all of the relations from the database
              (define relations (query-conflicts a b))
              ; No pairs of drugs causes a conflicts.
              (define result (not (ormap
                                   (curry drugs-conflict patient prescription)
                                   (map conflict-condition relations))))
              ;  (printf "\t\trelation [~a <-> ~a] ~a => ~a\n" a b relations result)
              result)
            prescription))
         prescription))

      ; Short circuit evaluation if a prior condition is false.
      (and
       (debug "treats-all" (treats-all))
       (debug "patient-compatible" (patient-compatible))
       (debug "internally-consistent" (internally-consistent))
       ))
    ]))

(define (debug message expr)
  (printf "\t~a: ~a\n" message expr)
  expr)

; Abstract over DB creation + syntax.
(define (make-database #:drugs drugs #:conflicts conflicts #:treatments treatments)
  ; Optimize here to construct hash tables to reduce the amount of comparisons.
  (database drugs conflicts treatments))


(define (lte a) (λ (b) (<= b a)))
(define (gte a) (λ (b) (>= b a)))

(define (any-allergy . as)
  `('allergy ,(λ (allergies)
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
    )
   #:conflicts ; conflict: two drug names and a condition
   (list

    (conflict 'A 'B '()) ; A and B unconditionally conflict.
    (conflict 'A 'C '(E)) ; A and C conflict in the presence of E
    (conflict 'C 'D `('requirement ,(any-allergy 'M 'N))) ; C and D conflict if patient has either allergy.
    (conflict 'A 'D `('and ; A and D conflict if the patient is less than age 50 and not taking C.
                      ('requirement ('age ,(lte 50)))
                      ('not (C))))
    )
   #:treatments ; treatement: ailments treated, patient requirements, drug formula
   (list
    (treatment '(X) '() '(A)) ; Drug A treats ailment X unconditionally.
    (treatment '(Y) `(('age ,(gte 2))) '(B)) ; Drug B treats ailment Y if the patient is over age 2.
    (treatment '(Y Z) '() '(C A)) ; Drug C treats ailments Y and Z when used with A.
    (treatment '(W) '() '(D)) ; Drug D treats ailment W unconditionally.
    (treatment '(U) '() '(E (or B C))) ; Drug E treats ailment U if used with B or C.
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

; (test)

(define (test-permutations)
  (define marc (patient 42 '(K) '(X Y))) ; Our (ailing) hero returns!

  ; For testing purposes, we want to see if our verifier returns true/false on any
  ; possible permutation of input prescriptions. Lightly modified from:
  ; https://stackoverflow.com/questions/20622945/how-to-do-a-powerset-in-drracket/20623487
  (define (powerset aL)
    (if (empty? aL) '(())
        (let ([rst (powerset (rest aL))])
          (append (map (λ (x) (cons (first aL) x)) rst) rst))))

  (define all-possible-prescriptions (powerset '(A B C D E)))
  (define check (curry verify-prescription drug-database marc))

  (define valid-prescriptions
    (filter (λ (p)
              (define result (check p))
              (printf "~a: ~a\n" p result)
              result)
            all-possible-prescriptions))
  ; And indeed, we see that only ACD and AC are valid prescriptions :)
  (printf "VALID PRESCRIPTIONS: ~a\n" valid-prescriptions))

; (test-permutations)

(define (test-synthesis)
  (define marc (patient 42 '(K) '(X Y))) ; Once more, for the cure...

  (define-symbolic a b c d e boolean?)

  (define check (curry verify-prescription drug-database marc))

  (define prescription
    (filter-map
     (λ (drug var) (if var drug #f))
     '(A B C D E)
     (list a b c d e)))

  ; (displayln (prescription))
  ; (displayln (check (prescription)))

  ; (displayln prescription)
  ; (displayln (check prescription))
  ; (displayln (check '(A C D)))

  (define solution
    (solve (begin
             (assert (check prescription))
             (printf "vc: ~a\n" (vc))
             )))

  (displayln solution)
  )

; (test)
; (test-permutations)
(test-synthesis)