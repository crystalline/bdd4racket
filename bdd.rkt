#lang racket

(require "logic.rkt")
(require "util.rkt")

(require racket/system)
(require racket/list)

(define-namespace-anchor a)
(define ns (namespace-anchor->namespace a))

;Basic binary operators
(define (conj a b)
  (if (and (eq? a 1) (eq? b 1)) 1 0))

(define (disj a b)
  (if (or (eq? a 1) (eq? b 1)) 1 0))

(define (neg a)
  (if (eq? a 1) 0 1))

(define (xor a b)
  (disj (conj a (neg b)) (conj b (neg a))))

(define (<=> a b)
  (disj (conj a b) (conj (neg a) (neg b))))

;N-ary versions, separated for performance
(define (conj~ . args)
  (if (null? args)
      1
      (conj (car args) (conj~ (cdr args)))))

(define (disj~ . args)
  (if (null? args)
      0
      (disj (car args) (disj~ (cdr args)))))

;BDD data structure implementation

;!IMPORTANT NOTE
;ARGUMENT INDEX SHOULD START FROM ZERO
;Indices are very important
;calling expr->bdd on expressions which contain
;arguments not beginning from zero may lead to very elusive bugs.
;Be careful when working with arguments

;Note that mkarg subtracts 2 from argument number,
;because 0 and 1 are reserved for terminals

;Also note that n-args is set to arbitrary value and doesn't make sense.
;I should do something about it, but it requires algorithm modification

(define T #f)     ;u -> (i l h)
(define H #f)     ;(i l h) -> u
(define max-u 0)  ;Next maximum node index
(define n-args 0) ;Number of arguments

(define (terminal-node? u) (or (eq? u 0) (eq? u 1)))

(define (add i l h)
  (hash-set! T max-u (list i l h))
  (set! max-u (+ max-u 1))
  (- max-u 1))

(define (node u)
  (let ((res (hash-ref T u 'null)))
    (if (list? res)
        res
        'null)))

(define (var u) (first (node u)))
(define (low u) (second (node u)))
(define (high u) (third (node u)))

(define (init N)
  (set! T (make-hash))
  (set! H (make-hash))
  (add N 'null 'null)
  (add N 'null 'null)
  (set! n-args N))

(define (member i l h)
  (if (eq? (hash-ref H (list i l h) 'null) 'null)
      #f
      #t))

(define (lookup i l h)
  (let ((result (hash-ref H (list i l h) 'null)))
    (if (number? result)
        result
        'null)))

(define (insert i l h u)
  (hash-set! H (list i l h) u))

(define (mk i l h)
  (cond ((eq? l h) l)
        ((member i l h) (lookup i l h))
        (else (let ((new-u (add i l h)))
                (insert i l h new-u)
                new-u))))

;Note that OP should be function : {0,1}^2 -> {0,1}
(define (bdd-apply op u1~ u2~)
  (let ((G (make-hash)))
    (define (app u1 u2)
      ;Memoization
      (let ((cached (hash-ref G (list u1 u2) 'null)))
        (if (not (eq? cached 'null))
            cached
            (let ((u (cond ((and (or (eq? u1 0) (eq? u1 1))
                                 (or (eq? u2 0) (eq? u2 1)))
                            (op u1 u2))
                           ((eq? (var u1) (var u2))
                            (mk (var u1)
                                (app (low u1) (low u2))
                                (app (high u1) (high u2))))
                           ((< (var u1) (var u2))
                            (mk (var u1)
                                (app (low u1) u2)
                                (app (high u1) u2)))
                           (else (mk (var u2)
                                     (app u1 (low u2))
                                     (app u1 (high u2)))))))
              (hash-set! G (list u1 u2) u)
              u))))
    (app u1~ u2~)))

;The only useful unary operation
(define (bdd-negate u)
  (cond ((terminal-node? u) (neg u))
        (else (mk (var u) (bdd-negate (low u)) (bdd-negate (high u))))))

(define (expr-subst expr var-index value)
  (tree-subst expr (list 'x var-index) value))

(define (build expr)
  (define (build~ expr i)
    (if (>= i n-args)
        (cond ((eq? expr 1) 1)
              ((eq? expr 0) 0)
              (else 'error))
        (mk i
            (build~ (expr-subst expr (list 'x i) 0) (+ i 1))
            (build~ (expr-subst expr (list 'x i) 1) (+ i 1)))))
  (build~ expr 0))

;Evaluate value of binary function represented with BDD
;with root at u. Arguments are applied from list of args
(define (bdd-eval u args)
  (define index (- (var u) 2))
  ;(printf "[bdd-eval ~s ~s]\n" index args)
  (cond ((terminal-node? u) u)                  ;If node is terminal, return it
        ((not (null? args))
         (cond ((eq? (@ args index) 0)
                (bdd-eval (low u) args))
               ((eq? (@ args index) 1)
                (bdd-eval (high u) args))
               (else 'error-not-bool-value)))   ;(first args) isn't boolean
        (else 'error-not-enough-args)))         ;There isn't enough args

(define (bdd-count-args u)
  (define (max-arg u)
    (cond ((terminal-node? u) 0)
          (else (max (var u)
                     (max-arg (low u))
                     (max-arg (high u))))))
  
  (define N (max-arg u))
  (if (< N 2)
      0
      (+ (- N 2) 1)))

(define (bdd-build-arglist node)
  (build-list (bdd-count-args node)
              (lambda (i) (string->symbol (format "x~a" i)))))

(define (bdd-compile u [N-args 'auto])
  (define N (if (eq? N-args 'auto)
                (bdd-count-args u)
                N-args))
  (define arglist
    (build-list N (lambda (i) (string->symbol (format "x~a" i)))))
  (define (build-ite-expr u)
    (if (terminal-node? u)
        u
        (list 'if (list 'eq? (@ arglist (- (var u) 2)) 1)
              (build-ite-expr (high u))
              (build-ite-expr (low u)))))
  (define body (build-ite-expr u))
  (eval (list 'lambda arglist body) ns))


;Visualize BDD node in graphviz
(define (viz-node u filename)
  (define traversed (make-hash))
  (define (set-traversed node) (hash-set! traversed node #t))
  (define (traversed? node) (hash-ref traversed node #f))
  (define (traverse node)
    (if (terminal-node? node)
        (format "~s ~n" node)
        (if (not (traversed? node))
            (begin
              (set-traversed node)
              (string-append
               (format "~s -> ~s [style=\"dashed\"]~n ~s -> ~s ~n ~s [label = <~a>]; ~n"
                       node (low node) node (high node) node (format "x<SUB>~s</SUB>" (- (var node) 2)))
               (traverse (low node))
               (traverse (high node))))
            "")))
  (let ((file (open-output-file filename #:exists 'replace)))
    (display
     (string-append
      "digraph BDD {"
      (traverse u)
      "}\n")
     file)
    (close-output-port file)))

;Visualize through temporary file
(define (viz-temp node)
  (viz-node node "temp.dot")
  (system (format "dot -Tpng -O temp.dot"))
  (shell-execute "open" "temp.dot.png" "" (current-directory) 'sw_shownormal))

(define (bdd->png node filename)
  (viz-node node (format "temp/~a.dot" filename))
  (system (format "dot -Tpng -O temp/~a.dot" filename)))

;Apply associative and commutative binary operation
;to list of BDDs
(define (bdd-apply* binop nodes)
  (cond ((null? nodes) 'error)
        ((eq? (length nodes) 2)
         (bdd-apply binop (first nodes) (second nodes)))
        (else (bdd-apply binop (first nodes)
                         (bdd-apply* binop (rest nodes))))))

;Doesn't work because (var 0) (var 1) are wrong
(define (satcount u)
  (define (scount u)
    (cond ((eq? u 0) 0)
          ((eq? u 1) 1)
          (else (+ (* (expt 2 (- (var (low u)) (var u) 1)) (scount (low u)))
                   (* (expt 2 (- (var (high u)) (var u) 1)) (scount (high u)))))))
  (* (expt 2 (- (var u) 1)) (scount u)))


(define (anysat-compact u)
  (cond ((eq? u 0) 'error-no-result)
        ((eq? u 1) '())
        ((eq? (low u) 0) (cons (list (- (var u) 2) 1) (anysat-compact (high u))))
        (else (cons (list (- (var u) 2) 0) (anysat-compact (low u))))))

(define (anysat u)
  (let ((vals (anysat-compact u))
        (N (bdd-count-args u)))
    (build-list N (lambda (i) (if (not (eq? #f (assoc i vals)))
                                  (second (assoc i vals))
                                  1)))))

(define (allsat-compact u)
  (cond ((eq? u 0) '())
        ((eq? u 1) '(()))
        (else (append (map (lambda (lst)
                             (cons (list (- (var u) 2) 0) lst))
                           (allsat-compact (low u)))
                      (map (lambda (lst)
                             (cons (list (- (var u) 2) 1) lst))
                           (allsat-compact (high u)))))))

;Note by default if some arguments don't influence
;the function value, they are set to 1
;so (length (allsat node)) is smaller
;than length of all SAT bitvectors
(define (allsat u [dont-care 1])
  (define compact (allsat-compact u))
  (define N (bdd-count-args u))
  (map (lambda (lst)
         (build-list N (lambda (i)
                         (if (not (eq? #f (assoc i lst)))
                             (second (assoc i lst))
                             dont-care))))
       compact))


;Make argument node
(define (mkarg index)
  (mk (+ index 2) 0 1))

(define op-table (hash
                  'conj conj
                  'disj disj
                  'neg neg
                  'xor xor
                  '<=> <=>))

(define (get-op expr)
  (hash-ref op-table (first expr)))

(define (arg? expr)
  (if (list? expr)
      (if (and (eq? (first expr) 'x)
               (number? (second expr)))
          #t
          #f)
      #f))

(define (neg? expr)
  (and (eq? (length expr) 2)
       (eq? (first expr) 'neg)))

(define (n-op? expr)
  (or (eq? (first expr) 'conj)
      (eq? (first expr) 'disj)))

(define (binop? expr)
  (in-list? (first expr) '(conj disj neg xor <=>)))

(define (expr->bdd expr)
  (cond ((null? expr) 'error)
        ((terminal-node? expr) expr)
        ((arg? expr) (mkarg (second expr)))
        ((neg? expr) (bdd-negate (expr->bdd (second expr))))
        ((n-op? expr) (bdd-apply* (get-op expr) (map expr->bdd (rest expr))))
        ((binop? expr) (bdd-apply (get-op expr)
                                  (expr->bdd (second expr))
                                  (expr->bdd (third expr))))
        (else 'error-unknown-expr)))

(define (expr->lambda~ expr)
  (define symbols '())
  (define phase1
    (tree-match-transform expr
                          (lambda (x)
                            (and (list? x)
                                 (eq? (first x) 'x)
                                 (number? (second x))))
                          (lambda (x)
                            (let* ((i (second x)) ;Push arg to symbol list
                                   (s (string->symbol (format "x~s" i))))
                              (pushf symbols (cons s i))
                              s))))
  (define args (map car
                    (sort symbols (lambda (a b) (< (cdr a) (cdr b))))))
  ;Eval and return lambda
  (eval (list 'lambda args phase1) ns))

(define (expr->lambda expr)
  (define symbols '())
  (define (arg? x)  (and (list? x)
                         (eq? (first x) 'x)
                         (number? (second x))))
  (define (nary-op? x)
    (and (list? x)
         (in-list? (car x) '(conj disj))
         (> (length x) 3)))
  (define phase1
    (tree-match-transform expr
                          (lambda (x)
                            (or (arg? x) (nary-op? x)))
                          (lambda (x)
                            (cond ((equal? (car x) 'conj) 'conj~)
                                  ((equal? (car x) 'disj) 'disj~)
                                  (else
                                   (let* ((i (second x)) ;Push arg to symbol list
                                          (s (string->symbol (format "x~s" i))))
                                     (pushf symbols (cons s i))
                                     s))))))
  (define args (map car
                    (sort symbols (lambda (a b) (< (cdr a) (cdr b))))))
  ;Eval and return lambda
  (eval (list 'lambda args phase1) ns))


;--------------------------------------------------------------------------
;                         N-QUEENS TASK FORMULATION
;--------------------------------------------------------------------------


;Returns argument index for board position
(define (arg-index i j N)
  (+ (* N i) j))

;If there is such position on NxN chess board
(define (on-board? i j N)
  (and (>= i 0) (< i N)
       (>= j 0) (< j N)))

(define (diagonals i j N)
  (define res '())
  (for ((k (in-range (- N) N)))
    (if (not (eq? k 0))
        (let ((p+ (list (+ i k) (+ j k)))
              (p- (list (- i k) (+ j k))))
          (if (on-board? (first p+) (second p+) N)
              (pushf res p+)
              #f)
          (if (on-board? (first p-) (second p-) N)
              (pushf res p-)
              #f))
        #f))
  res)

;Row, column and diagonals should be free
(define (queen-predicate i j N)
  (define res '())
  (define whole '())
  
  ;No queens on same column
  (for ((k (in-range 0 N)))
    (if (eq? k i)
        #f
        (set! res (cons (list 'neg (list 'x (arg-index k j N))) res))))
  (set! res (cons 'conj res))
  (set! whole (cons res whole))
  (set! res '())
  
  ;No queens on same row
  (for ((k (in-range 0 N)))
    (if (eq? k j)
        #f
        (set! res (cons (list 'neg (list 'x (arg-index i k N))) res))))
  (set! res (cons 'conj res))
  (set! whole (cons res whole))
  (set! res '())
  
  ;No queens on diagonals
  (let ((dias (diagonals i j N)))
    (map (lambda (index)
           (set! res (cons (list 'neg
                                 (list 'x (arg-index (first index)
                                                     (second index) N)))
                           res)))
         dias)
    #f)
  
  (set! whole (cons (cons 'conj res) whole))
  (set! res '())
  
  ;Final result is Xij => whole
  (list 'disj (list 'neg (list 'x (arg-index i j N)))
        (cons 'conj whole)))


;Argument naming scheme is as follows:
;linear, from upper-left board corner
;x0,      x1,        ... xN-1
;xN,      xN+1,      ... x2N-1
;         ........
;x(N-1)N, x(N-1)N+1, ... xNN-1
(define (build-n-queens-predicate N)
  
  (define cond-A '()) ;Non-attacking position
  (define cond-B '()) ;One queen in each row
  
  (for ((i (in-range 0 N)))
    (for ((j (in-range 0 N)))
      (pushf cond-A (queen-predicate i j N))))
  
  (for ((i (in-range 0 N)))
    (define temp '())
    (for ((j (in-range 0 N)))
      (pushf temp (list 'x (arg-index i j N))))
    (pushf cond-B (cons 'disj temp))
    (set! temp '()))
  
  (list 'conj
        (cons 'conj cond-A)
        (cons 'conj cond-B)))

;--------------------------------------------------------------------------
;                         TESTING AND EVALUATION
;--------------------------------------------------------------------------

(define (bdd->lambda node)
  (lambda args (bdd-eval node args)))

(define (print-tt-bdd node N)
  (print-truth-table (bdd->lambda node) N))

(define (make-tt-bdd node N)
  (make-truth-table (bdd->lambda node) N))

(define (gen-xorn N)
  (if (eq? N 1)
      (list 'xor (list 'x 1) (list 'x 0))
      (list 'xor (list 'x N) (gen-xorn (- N 1)))))

(define (gen-random-expr N)
  (define binops '(conj disj xor <=>))
  (define (choose-op) (@ binops (random (length binops))))
  (if (eq? N 1)
      (list (choose-op) (list 'x 1) (list 'x 0))
      (list (choose-op)
            (if (eq? 1 (random 2))
                (list 'neg (list 'x N))
                (list 'x N))
            (gen-random-expr (- N 1)))))


;Init BDD tables
(init 4096)

(random-seed 694129410)

(define exprs
  (list
   '(conj (<=> (x 0) (x 1)) (<=> (x 2) (x 3)))
   '(xor (conj
          (<=> (x 0) (x 1))
          (<=> (x 2) (x 3)))
         (xor (x 4) (x 5)))
   (gen-xorn 6)
   (gen-random-expr 4)
   ;   (gen-random-expr 5)
   ;   (gen-random-expr 6)
   ;   (gen-random-expr 7)
   ;   (gen-random-expr 8)
   ;   (gen-random-expr 9)
   ;   (gen-random-expr 10)
   ;   (gen-random-expr 10)
   ;   (gen-random-expr 10)
   ;   (gen-random-expr 10)
   ;   (gen-random-expr 10)
   (gen-random-expr 10)))


(define expr-lambdas (map expr->lambda exprs))

(define expr-bdds (map expr->bdd exprs))

(define e2l (@ expr-lambdas 1))
(define e2b (@ expr-bdds 1))

;BDD VS DIRECT EVALUATION

(define (compare index)
  (define N (procedure-arity (@ expr-lambdas index)))
  (filter (lambda (x)
            (not (equal? (second (car x))
                         (second (cdr x)))))
          (map cons
               (make-truth-table (@ expr-lambdas index) N)
               (make-truth-table (bdd-compile (@ expr-bdds index)) N))))

(define val-test-result (map compare (build-list (length exprs) I)))

(define (save-bdd-graphs)
  (map (λ (b) (bdd->png b (format "~a_~a" b (random 1000)))) expr-bdds))

(printf "[DIRECT VS BDD VALIDATION]\n")
(if (every? null? val-test-result)
    (printf "[TESTS PASSED: ~s EXPRESSIONS]\n" (length exprs))
    (printf "[WARNING: BDD VS DIRECT TESTS FAILED: ~s]\n" val-test-result))

;ANYSAT

(define anysat-test-res
  (map (lambda (proc bdd)
         (and (eq? (bdd-eval bdd (anysat bdd)) 1)
              (eq? (apply proc (anysat bdd)) 1)))
       expr-lambdas
       expr-bdds))

(define anysat-test-passed (every? I anysat-test-res))

(printf "[ANYSAT CHECK]\n")
(if anysat-test-passed
    (printf "[TESTS PASSED: ~s EXPRESSIONS]\n" (length exprs))
    (printf "[WARNING: ANYSAT TESTS FAILED: ~s]\n" anysat-test-res))

;ALLSAT

(define (=1 x) (eq? x 1))

(define allsat-test-res
  (map (lambda (proc bdd)
         (let ((satlst (allsat bdd)))
           (and (every? =1 (map (λ (x) (bdd-eval bdd x)) satlst))
                (every? =1 (map (λ (x) (apply proc x))
                                satlst)))))
       expr-lambdas
       expr-bdds))

(define allsat-test-passed (every? I allsat-test-res))

(printf "[ALLSAT CHECK]\n")
(if allsat-test-passed
    (printf "[TESTS PASSED: ~s EXPRESSIONS]\n" (length exprs))
    (printf "[WARNING: ALLSAT TESTS FAILED: ~s]\n" allsat-test-res))

;Try to find bitvectors satisfying function randomly
(define (random-sat proc [N 1000])
  (define N-args (procedure-arity proc))
  (define res (make-hash))
  (for ((i (in-range 0 N)))
    (let ((Xn (random-bitvector N-args)))
      (if (eq? (hash-ref res Xn 'null) 'null)
          (hash-set! res Xn (apply proc Xn))
          #f)))
  (map car (filter (λ (x) (eq? (cdr x) 1))
                   (hash->list res))))


;--------------------------------------------------------------------------
;                         N-QUEENS SOLUTION
;--------------------------------------------------------------------------


;Print chessboard
(define (vis-chess bitvector)
  (define N (sqrt (length bitvector)))
  (for ((i (in-range 0 (+ (* N 2) 3))))
    (printf "-"))
  (printf "\n")
  (for ((i (in-range 0 N)))
    (printf "|")
    (for ((j (in-range 0 N)))
      (printf "~a " (@ bitvector (arg-index i j N))))
    (printf "|\n"))
  (for ((i (in-range 0 (+ (* N 2) 3))))
    (printf "-"))
  (printf "\n"))

(define save-graphs? #f)

(define sol-data (make-hash))

(define (solve-N-queens N)
  (printf "[SOLVE ~a QUEENS PROBLEM]\n" N)
  
  (define t0 (current-inexact-milliseconds))
  
  (define pred (build-n-queens-predicate N))
  (define bdd (expr->bdd pred))
  (define solns (allsat bdd 'x))
  
  (define t1 (current-inexact-milliseconds))
  
  (define N-solns (length solns))
  
  (printf "[PROBLEM SOLVED IN ~a mSEC]\n" (- t1 t0))
  (printf "[NUMBER OF SOLUTIONS: ~a]\n" N-solns)
  (printf "SOLUTIONS:\n")
  
  (map vis-chess solns)
  
  (hash-set! sol-data N (list (list 'time (- t1 t0))
                              (list 'N-sols N-solns)))
  
  (if save-graphs?
      (begin
        (printf "[SAVING BDD GRAPH ... ")
        (bdd->png bdd (format "BDD_NQUEENS_~a" N))
        (printf "DONE]\n"))
      #f)
  #t)


;(solve-N-queens 1)
;(solve-N-queens 2)
(solve-N-queens 3)
(solve-N-queens 4)
(solve-N-queens 5)
(solve-N-queens 6)
(solve-N-queens 7)
(solve-N-queens 8)
;(solve-N-queens 9)

;(solve-N-queens 10)













