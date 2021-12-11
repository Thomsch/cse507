#lang rosette

(require "prescriptions.rkt")
  
(define drug-database
  (make-database
   #:drugs ; drug: name, patient requirements, properties
   (list
    (drug 'Fasenra  (list (older-than 5)(any-allergy 'Cephalosporin)) '(Diuretic))
    (drug 'Vitamax  (list (no-allergy 'Folate)) '(Multivitamin)) ; Cannot be allergic to Folate. Drug is a multivitamin.
    (drug 'UltraVitamin  (list (no-allergy 'Folate)) '(Biological)) ; Cannot be allergic to Folate. Drug is biological.
    )

   #:conflicts ; conflict: two drug names and a condition
   (list
    (conflict 'Fasenra 'Vitamax (REQUIREMENT (any-allergy 'Cephalosporin))) ; Fasenra and Vitamax conflict is the patient is allergic to Cephalosporin 
    (conflict 'Vitamax 'UltraVitamin '()) ; Vitamax and UltraVitamin conflict unconditionally
    )

   #:treatments ; treatment: ailments treated, patient requirements, drug formula
   (list
    (treatment '(Asthma) (list (younger-than 70)) '(Fasenra)) ; Drug Fasenra treats Asthma if patient is younger than 70
    )))

(define (example)
  (define jessie (patient 26 '(Cephalosporin) '(Asthma))) ; Jessie is 26, is allergic to Cephalosporin, and has Asthma.
  (define baseline-prescription '(Fasenra))
  (define prescription-1 '(Fasenra Vitamax)) ; Conflict because Jessie is allergic to Cephalosporin.
  (define prescription-2 '(Fasenra UltraVitamin)) ; No conflict! Jessie can use this!

  (displayln (verify-prescription drug-database jessie baseline-prescription)) ; #t
  (displayln (time (verify-prescription drug-database jessie prescription-1))) ; #f (conflict)
  (displayln (verify-prescription drug-database jessie prescription-2)) ; #t (no conflict)
  (display-prescription (time (generate-prescription drug-database jessie))) ; Returns 'Fasenra to treat the asthma
  (display-prescription (time (optimized-prescription drug-database jessie '(Fasenra UltraVitamin Vitamax)))) ;  Returns '(Fasenra UltraVitamin) because Vitamax is not advisable
)

(example)