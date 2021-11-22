#lang rosette

;;; Verifiable prescription library ;;;
; Yes, this should/will be a separate file.

; Translate the doctor definitions to a Rosette program and verifies it.
(define (check-prescription prescription drug-database)
    (define translated (translate prescription drug-database))
    (verify translated)
)

(define (translate prescription drug-database)
    (assert #f) ; TBD
)

;;; The doctor 'writes' their knowledge of drugs and their patient prescription here ;;;

; Each drug is declared as a list of the format
; (id (active-ingredients) (uses) (incompatibilites))
(define drugs '(
    '('tylenol '('Acetaminophen) '('Fever 'Headache 'Body-ache) '('tylenol-ultra))
    '('tylenol-ultra '('Acetaminophen) '('Fever 'Headache 'Body-ache) '('tylenol))
))

; Each patient is defined with its own prescription
(define prescription-patient-1 '(
    '("Marc") ; Patient info (e.g., name, adress, phone)
    '('Peanuts 'Acetaminophen) ; Allergies
    
    ; Prescription
    '(
        'tylenol
    )
))

(pretty-print drugs)
(pretty-print prescription-patient-1)

; Check that the prescription is fine
(check-prescription prescription-patient-1 drugs) ; should by unsat.
