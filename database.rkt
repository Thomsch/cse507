#lang rosette

;;; This is a list of 66 popular drugs that treats a veriety of ailements. 
;;; In reality, a doctor has significantly less than 68 drugs at their disposal since they
;;; can't memorize all the potential interactions. They only know a handful of interactions for 
;;; their domain.
(define drug-names '(
    Acetaminophen
    Adderall
    Amitriptyline
    Amlodipine
    Amoxicillin
    Ativan
    Atorvastatin
    Azithromycin
    Benzonatate
    Brilinta
    Bunavail
    Buprenorphine
    Cephalexin
    Ciprofloxacin
    Citalopram
    Clindamycin
    Clonazepam
    Cyclobenzaprine
    Cymbalta
    Doxycycline
    Dupixent
    Entresto
    Entyvio
    Farxiga
    Fentanyl
    Gabapentin
    Gilenya
    Humira
    Hydrochlorothiazide
    Hydroxychloroquine
    Ibuprofen
    Imbruvica
    Invokana
    Januvia
    Jardiance
    Kevzara
    Lexapro
    Lisinopril
    Lofexidine
    Loratadine
    Lyrica
    Melatonin
    Meloxicam
    Metformin
    Methadone
    Methotrexate
    Metoprolol
    Naloxone
    Naltrexone
    Naproxen
    Omeprazole
    Onpattro
    Otezla
    Ozempic
    Pantoprazole
    Prednisone
    Probuphine
    Rybelsus
    secukinumab
    Sublocade
    Tramadol
    Trazodone
    Viagra
    Wellbutrin
    Xanax
    Zubsolv
    )) 

;;; This is a list of 53 'popular' ailements.
;;; If this is not enough, there is a way longer list at https://www.nhsinform.scot/illnesses-and-conditions/a-to-z
(define ailements '(
    Acne
    ADHD
    HIV
    Allergies
    Alzheimer
    Angina
    Anxiety
    Arthritis
    Asthma
    Bipolar-Disorder
    Bronchitis
    Cancer
    Cholesterol
    Colds
    Flu
    Constipation
    COPD
    Covid-19
    Depression
    Diabetes-Type-1
    Diabetes-Type-2
    Diarrhea
    Eczema
    Erectile Dysfunction
    Fibromyalgia
    Gastrointestinal
    Gastroesophageal-Reflux-Disease
    Gout
    Hair-Loss
    Hayfever
    Heart-Disease
    Herpes
    Hypertension
    Hypothyroidism
    Headache
    Irritable-Bowel
    Incontinence
    Insomnia
    Menopause
    Migraine
    Osteoarthritis
    Osteoporosis
    Overweight
    Pain
    Pneumonia
    Psoriasis
    Rheumatoid-Arthritis
    Schizophrenia
    Seizures
    Stroke
    Swine-Flu
    UTI
    ))

;;; (for ([(group i) (in-indexed ailements)])
;;;   (printf "~a. ~a\n" (add1 i) group))