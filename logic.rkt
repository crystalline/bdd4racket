#lang racket

(require racket/vector)

(provide && xor2 -- ||
         bitlist+
         print-truth-table
         make-truth-table
         print-tt
         bsat)

(define-namespace-anchor a)
(define ns (namespace-anchor->namespace a))

(define (o F G)
  (lambda x (F (G x))))

;(define (>> bnum)
;  (

;(define (bin->vec bnum)
;  (for 

(define (tf->10 v)
  (if v
      1
      (if (eq? v #f)
          0
          'X)))

(define (is-bitlist lst)
  (eq? (length lst)
       (+ (count (λ (x) (eq? x 1)) lst)
          (count (λ (x) (eq? x 0)) lst))))

;(is-bitlist (list 1 0 1 1 1 1))
;(is-bitlist (list 1 0 0 0 'a 'b 'c))

(define (|| . bitlist)
  (if (>= (count (λ (x) (eq? x 1)) bitlist) 1)
      1
      0))

(define (&& . bitlist)
  (if (eq? (count (λ (x) (eq? x 1)) bitlist) (length bitlist))
      1
      0))

(define (-- v)
  (if (eq? v 1)
      0
      (if (eq? v 0)
          1
          'X)))

(define (xor2 a b)
  (|| (&& (-- a) b)
      (&& a (-- b))))

;Returns list: (result carry)
(define (adder a b)
  (list (xor2 a b)
        (&& a b)))

(define adder-out first)
(define adder-carry second)

;(adder 0 0)
;(adder 0 1)
;(adder 1 0)
;(adder 1 1)

;(printf "----------------\n")

;a b|o c
;0 0|0 0
;0 1|1 0
;1 0|1 0
;1 1|0 1

(define (full-adder a b cin)
  (let ((out (adder-out (adder a b)))
        (carry (adder-carry (adder a b))))
    (list (adder-out (adder out cin))
          (|| carry (adder-carry (adder out cin))))))

;(full-adder 0 0 0)
;(full-adder 0 0 1)
;(full-adder 0 1 0)
;(full-adder 1 0 0)
;(full-adder 0 1 1)
;(full-adder 1 1 0)
;(full-adder 1 0 1)
;(full-adder 1 1 1)

(define (bitlist+ a b)
  (define carry 0)
  (define result (build-vector (length a) (λ (x) 0)))
  (for ((i (in-range (- (length a) 1) -1 -1)))
    (let ((a+b (full-adder (list-ref a i)
                           (list-ref b i)
                           carry)))
      (set! carry (adder-carry a+b))
      (vector-set! result i (adder-out a+b))))
  ;(printf "[i ~s a ~s b ~s]\n" i (list-ref a i) (list-ref b i)))
  (if (eq? carry 1)
      (cons 1 (vector->list result))
      (vector->list result)))


;(printf "----------------\n")

;(bitlist+ '(1 0) '(1 0))

(define (n-of-bits num)
  (inexact->exact (floor (/ (log num) (log 2)))))

(define (broaden-bitlist lst N)
  (append (make-list (- N (length lst)) 0) lst))

(define (gen-bitlist-seq N)
  (define val (make-list (n-of-bits N) 0))
  (define incr (broaden-bitlist '(1) (n-of-bits N)))
  (define result (make-vector N))
  (for ((i (in-range 0 N)))
    (vector-set! result i val)
    (set! val (bitlist+ val incr)))
  (vector->list result))

;(gen-bitlist-seq 16)

;(define (print-truth-table func nargs)
;  (define args (gen-bitlist-seq (expt 2 nargs)))
;  (for ((i (in-range 0 (expt 2 nargs))))
;    (define arg (list-ref args i))
;    (printf "[ ~s : ~s ]\n" arg (apply func arg)))
;  (printf "----------------\n"))

(define (make-truth-table func nargs)
  (define args (gen-bitlist-seq (expt 2 nargs)))
  (map (λ (a) (list a (apply func a))) args))

(define (print-truth-table func nargs)
  (define table (make-truth-table func nargs))
  (for ((i (in-range 0 (expt 2 nargs))))
    (printf "[ ~s : ~s ]\n"
            (first (list-ref table i))
            (second (list-ref table i))))
  (printf "----------------\n"))



;(print-truth-table xor2 2)

(define (== a b)
  (tf->10 (eq? a b)))

;(print-truth-table == 2)

(define (=> a b)
  (-- (&& a (-- b))))

;(print-truth-table => 2)

(define (f1 x y z t)
  (xor2 (|| x y) (=> z t)))

;(printf "[f1]\n")

;(print-truth-table f1 4)

(define (SKNF proc symlist)
  (define table (make-truth-table proc (length symlist)))
  (define zeros (filter (λ (x) (eq? (second x) 0)) table))
  (define lexpr (append '(&&)
                        (map (λ (arglist) (append '(||)
                                                  (map (λ (arg sym) (if (eq? arg 1)
                                                                        (list '-- sym)
                                                                        sym))
                                                       arglist symlist)))
                             (map first zeros))))
  (append (list 'lambda symlist) (list lexpr)))

(define (SDNF proc symlist)
  (define table (make-truth-table proc (length symlist)))
  (define ones (filter (λ (x) (eq? (second x) 1)) table))
  (define lexpr (append '(||)
                        (map (λ (arglist) (append '(&&)
                                                  (map (λ (arg sym) (if (eq? arg 1)
                                                                        sym
                                                                        (list '-- sym)))
                                                       arglist symlist)))
                             (map first ones))))
  (append (list 'lambda symlist) (list lexpr)))

(define f1*  (eval (SDNF f1 '(x y z t)) ns))
(define f1#  (eval (SKNF f1 '(x y z t)) ns))

;Checking SDNF and SKNF
;(equal? 
; (make-truth-table f1 4)
; (make-truth-table f1* 4))
;
;(equal? 
; (make-truth-table f1 4)
; (make-truth-table f1# 4))

(define (some proc lst)
  (>= (count proc lst) 1))

(define (some-equal? val lst)
  (some (λ (x) (equal? val x)) lst))

(define (gen-all-sublists len lst)
  (if (eq? len 1)
      (map list lst)
      (let ((sublists@len-1 (gen-all-sublists (- len 1) lst)))
        (append*
         (map (λ (elem)
                (map (λ (l) (cons elem l))
                     (filter-not
                      (λ (sublist)
                        (some-equal? elem sublist))  sublists@len-1)))
              lst)))))

;(gen-all-sublists 3 '(a b c d))

(define (I x) x)

(define (repetitive? l)
  (some I (map (λ (elem) (>= (count (λ (x) (equal? x elem)) l) 2)) l)))

;(repetitive? '(a a b c))

;(equal? (filter-not repetitive? (gen-all-sublists 3 '(a b c d)))
;        (gen-all-sublists 3 '(a b c d)))

(define (fact n) 
  (if (eq? n 1)
      1
      (* n (fact (- n 1)))))

(define (Cnk n k) (/ (fact n) (fact (- n k))))

;(Cnk 4 3)

;(define (every-sublist-unique? lst)
;  (define (is-unique? 


;a b cin|o cout
;0 0   0|0 0
;0 0   1|1 0
;0 1   0|1 0
;0 1   1|0 1
;1 0   0|1 0
;1 0   1|0 1
;1 1   0|0 1
;1 1   1|1 1

;(define (add-bitlist A B)

;(define (&& . args)

;(filter-not repetitive? (gen-all-sublists 3 '(a b c)))

(define (pcats P S B O)
  (|| (&& (-- P) S B)
      (&& (-- P) S O)
      (&& P (-- S) (-- B))
      (&& (-- P) (-- O) B)
      (&& (-- P) (-- S) (-- O) (-- B))
      (&& (-- P) (-- S) O)))

;(print-truth-table pcats 4)

;(define (pcats~ P S B O)
;  (|| (&& P (-- S) (-- B))
;      
;      (&& (-- P)
;          (|| (&& S (|| B O))
;              (&& (-- O) B)
;              
;              (&& (-- S) (-- O) (-- B))
;              (&& (-- S) O)))))

;(define (pcats~ P S B O)
;  (|| (&& P (-- S) (-- B))
;      (&& (-- P)
;          (|| (&& S (|| B O))
;              (&& (-- O) B)
;              (&& (-- S)
;                  (|| (&& (-- O) (-- B))
;                      O))))))

;(define (pcats~ P S B O)
;  (|| (&& P (-- S) (-- B))
;      (&& (-- P)
;          (|| (&& S (|| B O))
;              (&& (-- O) B)
;              (&& (-- S)
;                  (|| (-- (|| O B))
;                      O))))))

;(define (pcats~ P S B O)
;  (|| (&& P (-- S) (-- B))
;      (&& (-- P)
;          (|| (&& S (|| B O))
;              (&& (-- O) B)
;              (-- S)))))

(define (pcats~ P S B O)
  (|| (&& P (-- S) (-- B))
      (&& (-- P)
          (|| (-- S) B O))))

;(print-truth-table pcats~ 4)

;(equal? (make-truth-table pcats 4)
;        (make-truth-table pcats~ 4))

(define (diploma Y B P)
  (&& (-- (&& Y B))
      (|| B P)
      (-- (&& Y P))))

;(print-truth-table diploma 3)

(define (dip~ Y B P)
  (&& (|| (-- Y) (&& (-- B) (-- P))) (|| B P)))

;(print-truth-table dip~ 3)

(define (print-tt f) (print-truth-table f (procedure-arity f)))

;(print-tt dip~)

(define (<=> a b) (-- (xor2 a b)))

(define (e2 x1 x2 x3 x4 x5 x6) (xor2 (&& (<=> x1 x2) (<=> x3 x4)) (xor2 x5 x6)))

;(print-tt e2)

(define (bsat proc)
  (filter (λ (x) (eq? (second x) 1))
          (make-truth-table proc (procedure-arity proc))))

(define (e3 x1 x2 x3 x4) (&& (<=> x1 x2) (<=> x3 x4)))

;(print-tt e3)

;(bsat e2)