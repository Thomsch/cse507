#lang rosette

(provide ??? contains? debug find)

(define ??? null)

(define (contains? objects item) (if [member item objects] #t #f))

(define (find objects item)
  (define found (member item objects))
  (if found (car found) #f))

(define (debug message expr)
  ; (printf "\t~a: ~a\n" message expr)
  expr)