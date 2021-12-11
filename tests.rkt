#lang rosette

(require "prescriptions.rkt")
(require "utils.rkt")

; Test drug database
(define drug-database
  (make-database

   #:drugs ; drug: name, patient requirements, properties
   (list
    (drug 'A  '() '())
    (drug 'B  '() '())
    (drug 'C  '() '())
    (drug 'D  '() '())
    (drug 'E  '() '())
    (drug 'A1  '() '(ACE-Inhibitor blue))
    (drug 'B1  '() '(sedative vasopressor blue))
    (drug 'C1  '() '(diuretic beta-blocker blue))
    (drug 'D1  (list (older-than 60)) '(inotropic NHE3-inhibitor blue))
    (drug 'E1  '() '(vasodilator beta-blocker blue))
    (drug 'A2  '() '(red))
    (drug 'B2  '() '(red))
    (drug 'C2  '() '(red))
    (drug 'D2  '() '(red))
    (drug 'E2  '() '(red))
    )

   #:conflicts ; conflict: two drug names and a condition
   (list
    (conflict 'A 'B '()) ; A and B unconditionally conflict.
    (conflict 'A 'C '(E)) ; A and C conflict in the presence of E
    (conflict 'C 'D (REQUIREMENT (any-allergy 'M 'N))) ; C and D conflict if patient has either allergy.
    (conflict 'A 'D (AND ; A and D conflict if the patient is less than age 50 and not taking C.
                     (REQUIREMENT (younger-than 50))
                     (NOT 'C)))
    ; Any vasodilator and any vasopressor unconditionally conflict.
    (conflict-class (has-property 'vasodilator) (has-property 'vasopressor) '())

    ; Any ACE inhibitor and any diuretic conflict if the patient is allergic to K.
    (conflict-class
     (has-property 'ACE-Inhibitor)
     (has-property 'diuretic)
     (REQUIREMENT (any-allergy 'K)))

    ; Dummy conflicts to test scaling
    (conflict-class
     (has-property 'blue)
     (has-property 'red)
     '())

    (conflict 'A2 'B2 '())
    (conflict 'B2 'C2 '())
    (conflict 'C2 'D2 '())
    (conflict 'D2 'E2 '())
    )

   #:treatments ; treatment: ailments treated, patient requirements, drug formula
   (list
    (treatment '(X) '() '(A)) ; Drug A treats ailment X unconditionally.
    (treatment '(Y) (list (older-than 2)) '(B)) ; Drug B treats ailment Y if the patient is over age 2.
    (treatment '(Y Z) '() '(C A)) ; Drug C treats ailments Y and Z when used with A.
    (treatment '(W) '() '(D)) ; Drug D treats ailment W unconditionally.
    (treatment '(U) '() '(E (OR B C))) ; Drug E treats ailment U if used with B or C.

    ; This treatment works if the patient isn't allergic to M
    (treatment '(X1) (list (no-allergy 'M))
               ; The treatment requires at least one drug in each property.
               ; Note: this is *different* than saying (has-property 'A B),
               ;       which would require one single drug to have both properties.
               (AND (has-property 'ACE-Inhibitor) (has-property 'beta-blocker)))
    )))

; Verification test
(displayln "~~~ Test Verification ~~~")
(define (test)
  (define marc (patient 42 '(K) '(X Y)))
  (define possible-prescription-1 '(A B))   ; Conflict
  (define possible-prescription-2 '(A D))   ; No conflict, but also doesn't fit the bill
  (define possible-prescription-3 '(A C E)) ; Transitive conflict
  (define possible-prescription-4 '(A C D)) ; A and D conflict due to age, but OK because of C
  (define possible-prescription-5 '(A C))   ; Treats X and Y, no conflict. Ship it!

  (displayln (time (verify-prescription drug-database marc possible-prescription-1)))
  (displayln (time (verify-prescription drug-database marc possible-prescription-2)))
  (displayln (time (verify-prescription drug-database marc possible-prescription-3)))
  (displayln (time (verify-prescription drug-database marc possible-prescription-4)))
  (displayln (time (verify-prescription drug-database marc possible-prescription-5))))

(test)

(displayln "\n~~~ Test Synthesis ~~~")
(define (test-automated)
  ; Test basic features
  (define marc (patient 42 '(K) '(X Y)))
  (display-prescription (time (generate-prescription drug-database marc))) ; (A C)

  ; Test that conflict-classes and treatment-formulas work well.
  (define jane (patient 31 '(K) '(X1)))
  (display-prescription (time (generate-prescription drug-database jane))) ; (A1 E1)
  )

(test-automated)

(displayln "\n~~~ Test Optimization ~~~")
; Since Marc is already taking D, we expect to see ACD instead of the A C from before.
(define (test-optimization)
  (define marc (patient 42 '(K) '(X Y)))
  (display-prescription (time (optimized-prescription drug-database marc '(D))))) ; (A C D)

(test-optimization)


(displayln "\n~~~ Exhaustive Search ~~~")
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

  (debug "Generated powerset of size ~a\n" (length all-possible-prescriptions))

  (define (check prescription)
    (verify-prescription drug-database marc prescription))

  (define valid-prescriptions
    (map (curry filter identity)
         (filter check all-possible-prescriptions)))
  ; And indeed, we see that only ACD and AC are valid prescriptions :)
  (print-upto 5 "Exhaustive search" valid-prescriptions))

(define (test-permutations)
  (time (exhaustive-test '(A B C D E)))
  ; Uncomment this test for benchmarking (warning: takes a while!)
  (time (exhaustive-test (map drug-name (database-drugs drug-database))))
  )

(test-permutations)
