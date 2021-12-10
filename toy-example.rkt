#lang rosette

(require "prescriptions.rkt")

(define toy-database
  (make-database
   #:drugs ; drug: name, patient requirements, properties
   (list
    (drug 'Fasenra  '() '())
    (drug 'Vitamax  '() '())
    (drug 'UltraVitamin  '() '())
    )

   #:conflicts ; conflict: two drug names and a condition
   (list
    (conflict 'Fasenra 'Vitamax (REQUIREMENT (any-allergy 'Cephalosporin))) ; Fasenra and Vitamax conflict is the patient is allergic to Cephalosporin 
    (conflict 'Vitamax 'UltraVitamin '()) ; Vitamax and UltraVitamin conflict unconditionally
    )

   #:treatments ; treatment: ailments treated, patient requirements, drug formula
   (list
    (treatment '(Asthma) (list (older-than 10)) '(Fasenra)) ; Drug Fasenra treats Asthma if patient is over age 10.
    )))

(define (example-1)
  (define jessie (patient 26 '(Cephalosporin) '(Asthma))) ; Jessie is 26, is allergic to Cephalosporin, and has Asthma
  (define baseline-prescription '(Fasenra))
  (define prescription-1 '(Fasenra Vitamax)) ; Conflict because Jessie is allergic to Cephalosporin.
  (define prescription-2 '(Fasenra UltraVitamin)) ; No conflict! Jessie can use this!

  (displayln (verify-prescription toy-database jessie baseline-prescription)) ; #t
  (displayln (verify-prescription toy-database jessie prescription-1)) ; #f
  (displayln (verify-prescription toy-database jessie prescription-2)) ; #t
)

(example-1)