#lang rosette

(require "prescriptions.rkt")

(define drug-database
  (make-database
   #:drugs ; drug: name, patient requirements, properties
   (list
    (drug 'Lotensin  '() '(ACE-Inhibitor)) ; Angiotensin-converting enzyme inhibitors
    (drug 'Capoten  '() '(ACE-Inhibitor))
    (drug 'Vasotec  '() '(ACE-Inhibitor))
    (drug 'Monopril  '() '(ACE-Inhibitor))
    (drug 'Prinivil  '() '(ACE-Inhibitor))
    (drug 'Univasc  '() '(ACE-Inhibitor))
    (drug 'Aceon  '() '(ACE-Inhibitor))
    (drug 'Altace  '() '(ACE-Inhibitor))
    (drug 'Mavik  '() '(ACE-Inhibitor))
    (drug 'Edarbi  '() '(ARB)) ; Angiotensin II receptor blockers
    (drug 'Atacand  '() '(ARB))
    (drug 'Teveten  '() '(ARB))
    (drug 'Avapro  '() '(ARB))
    (drug 'Cozaar  '() '(ARB))
    (drug 'Benicar  '() '(ARB))
    (drug 'Micardis  '() '(ARB))
    (drug 'Diovan  '() '(ARB))
    (drug 'Norvasc  '() '(CCB)) ; Calcium channel blockers
    (drug 'Plendil  '() '(CCB))
    (drug 'DynaCirc  '() '(CCB))
    (drug 'Cardene  '() '(CCB))
    (drug 'Procardia  '() '(CCB))
    (drug 'Sular  '() '(CCB))
    (drug 'Hygroton  '() '(Diuretic)) ; Diuretics
    (drug 'Esidrix  '() '(Diuretic))
    (drug 'Oretic  '() '(Diuretic))
    (drug 'Lozol  '() '(Diuretic))
    (drug 'Mykrox  '() '(Diuretic))
    (drug 'Zaroxolyn  '() '(Diuretic))
    )

   #:conflicts ; conflict: two drug names and a condition
   (list
   	; overdose/repitition conflicts
    (conflict-class (has-property 'ACE-Inhibitor) (has-property 'ACE-Inhibitor) '())
    (conflict-class (has-property 'ARB) (has-property 'ARB) '())
    (conflict-class (has-property 'CCB) (has-property 'CCB) '())
    (conflict-class (has-property 'Diuretic) (has-property 'Diuretic) '())

    ; more relevant conflicts
    ;(conflict-class (has-property 'Diuretic) '() (REQUIREMENT (any-ailment 'low-sodium))) ; Diuretics shouldn't be used for someone with low sodium
    ;(conflict-class (has-property 'CCB) '() (REQUIREMENT (any-ailment 'heart-problem))) ; calcium channel blockers shouldn't be used
    																		; for someone with heart problems
    )

   #:treatments ; treatment: ailments treated, patient requirements, drug formula
   (list
    (treatment '(stage-1-hypertension) '() (OR ; Try monotherapy
                                             (has-property 'ACE-Inhibitor)
                                             (OR (has-property 'ARB)
                                                 (OR (has-property 'CCB)
                                                     (has-property 'Diuretic)))
                                             ))
    (treatment '(stage-2-hypertension) '() (AND ; Two drug combination
                                             (OR (has-property 'ACE-Inhibitor) (has-property 'ARB))
                                             (OR (has-property 'Diuretic) (has-property 'CCB))
                                             )) 
    )))

(define (example)
  (define jack (patient 26 '() '(stage-1-hypertension low-sodium)))
  (define diuretic-prescription '(Lozol))
  (define ccb-prescription '(Plendil))

  (displayln (verify-prescription drug-database jack diuretic-prescription)) ; jack shouldn't be given a diuretic
)

(example)

