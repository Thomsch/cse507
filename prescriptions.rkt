#lang rosette

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
; - a set of ailments that they treat
; - a set of unconditional requirements that must be met about
; the patient's conditions.
;
; Note: We treat the list of requirements as
; a syntactic convenience for providing a *conjunction* of all
; requirements in the list.
(struct drug (name ailments requirements) #:transparent)

; A requirement can be any of following, where `f` is a predicate takes in
; a patient's information and returns true or false:
'('age f)
'('allergies f)
'('not requirement)
'('and a b ...)
'('or a b ...)

; This definition admits the following verifier:
(define (satisfies-requirement patient requirement)
  (match requirement
    [ `('age ,f) (f (patient-age patient))]
    [ `('allergies ,f) (f (patient-allergies patient))]
    [ `('not ,r) (not (satisfies-requirement patient r)) ]
    [ `('or ,a ...)  (apply || (map (curry satisfies-requirement patient) a)) ]
    [ `('and ,a ...)  (apply && (map (curry satisfies-requirement patient) a)) ]
    ))

; A conflict relation says that drug A conflicts with drug B,
; if the condition is true for a given patient and drug list.
(struct conflict (condition A B) #:transparent)

; A condition extends the `requirement` type with the ability to specify
; other drugs, which are interepreted as "true" values if the patient is taking a
; drug of that name. For example:
'(drug-name)
'('requirement r)

; Together, these admit the following verifier, which verifies if two
; drugs conflict given a patient and existing series of drugs.
; (Note, this does not check if adding either of the two drugs to the
;  medications list would cause conflicts to occur with any there.)
(define (drugs-conflict patient medications relation)
  (match (conflict-condition relation)
    [ `('requirement ,r) (satisfies-requirement patient r) ]
    [ `('not ,c) (not (drugs-conflict patient medications c)) ]
    [ `('or ,c)
      (apply || (map (curry drugs-conflict patient medications) c)) ]
    [ `('and ,c)
      (apply && (map (curry drugs-conflict patient medications) c)) ]
    [ `(,drugs ...)
      (apply && (map (λ (drug) (member drug medications)) drugs)) ]
    ))

; A drug database contains our "universe" of information -- these
; are all of the drugs we know about, and all of the known conflicts
; in-between them.
;
; Idea: while all "conflicts" in the database must be concrete conflict
; triples, we can expose a DSL front-end that allows us to define conflicts
; in a predicate style: i.e. drug A with active ingredient I conflicts with
; any drug B that has some active ingredient J under certain conditions. Then
; this predicate is evaluated against each drug B != A in the database to create
; the relations. (This may be a reasonable way to generate data-sets.)
(struct database (drugs conflicts) #:transparent)

; From here, we can indeed write a procedure to verify a candidate
; prescription, here defined as a set of drugs, for a given patient.
; We assume the presence of a drug database,
;
; A valid prescription (list of drug-names) must satisfiy the following conditions:
; - Treat all of the patient's ailments.
; - Be compatible with the patient's properties and allergies.
; - Be internally consistent -- no drugs can conflict with each other.
;
; We assume prescriptions are well-formed, i.e. that all drugs are present in the database.
(define (verify-prescriptions database patient prescription)
  (define drugs (database-drugs database))
  (define conflicts (database-conflicts database))
  (define ailments (patient-ailments patient))

  (define (query-drugs selector)
    (apply append
           (map (λ (drug-name)
                  (selector (hash-ref drugs drug-name)))
                prescription)))

  ; Note: naive implementation scans the whole conflict list, instead we probably want
  ; something with a dictionary that looks over just the conflicts of A.
  ; Since `conflicts(A,B) <=> conflicts(B,A)`, we can safely ignore the case where a
  ; conflict is only registered in one direction, since we will always check both.
  (define (query-conflicts a b)
    (filter (λ (c)
              (&& (equal? (conflict-A c) a) (equal? (conflict-B c) b)))
            conflicts))

  (define (treats-all)
    (define treated-list (query-drugs drug-ailments))
    (apply && (map (λ (ailment) (member ailment treated-list)) ailments)))

  (define (patient-compatible)
    (define requirements-list (query-drugs drug-requirements))
    (apply && (map (curry satisfies-requirement patient) requirements-list)))


  ; Futher optimization: fast exit on first failure since we know it's inconsistent.
  (define (internally-consistent)
    (apply &&
           (for*/list ([a prescription]
                       [b prescription])
             ; Query all of the relations from the database
             (define relations (query-conflicts a b))
             ; No pairs of drugs causes a conflicts.
             (not (apply || (map (curry drugs-conflict patient prescription) relations))))))

  ; Short circuit evaluation if a prior condition is false.
  (and (treats-all) (patient-compatible) (internally-consistent)))


; TODO: define a global database, or generate them on the fly from
;  random data and random global properties (see above)
(define drug-database (database ??? ???))

(define ??? null)