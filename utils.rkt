#lang rosette

(provide ??? contains? debug)

(define ??? null)

(define (contains? objects item) (if [member item objects] #t #f))

(define (debug message expr)
  ; (printf "\t~a: ~a\n" message expr)
  expr)