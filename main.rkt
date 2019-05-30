#lang racket

(require redex)

(provide (all-defined-out))

(define-language RC
  [e   ::= x v (e e ...) (if e e e) (p1 e) (p2 e e)
       (set! x e) (begin e e ...)
       (lambda (x_!_ ...) e) (let-values (((x_!_) e) ...) e)
       (raises e)] ;; expressiosn
  [v   ::= n b c (void)] ;; values
  [c   ::= (closure x ... e ε)]
  [n   ::= number]
  [b   ::= true false]
  [x cell ::= variable-not-otherwise-mentioned] ;; variables
  [p1  ::= add1]
  [p2  ::= + * <]
  [o   ::= p1 p2]
  [E   ::= hole (v ... E e ...) (o v ... E e ...) (if E e e)
       (begin v ... E e ...) (set! x E)
       (let-values (((x) v) ... ((x) E) ((x) e) ...) e)] ;; eval context

  [ε   ::= ((x any) ...)] ;; environment
  [Σ   ::= ((x any) ...)] ;; store

  [e-test ::= x n b (void) 
          (e-test e-test ...) (lambda (x_!_ ...) e-test) (if e-test e-test e-test) 
          (p2 e-test e-test) (p1 e-test) (set! x e-test) (begin e-test e-test ...) 
          (let-values (((x) e-test) ...) e-test) (raises e-test)] ;; to be used to generate test cases (i.e. exclude closures)

  [rc-result ::= v stuck]
  [exp-id ::= x (x x)]
  [C ::= cell uninit]

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let-values ([(x) e_x] ...) e_body #:refers-to (shadow x ...))
  )

(define-metafunction RC
  δ : (o any ...) -> v or true or false or (raises e)
  [(δ (add1 n)) ,(add1 (term n))]
  [(δ (< n_1 n_2)) ,(if (< (term n_1) (term n_2)) (term true) (term false))]
  [(δ (+ n_1 n_2)) ,(+ (term n_1) (term n_2))]
  [(δ (* n_1 n_2)) ,(* (term n_1) (term n_2))]
  [(δ (o any_1 any_2 ...)) (raises (o any_1 any_2 ...))])

(define-metafunction RC
  extend : ((x any) ...)  (x ...) (any ...) -> ((x any) ...)
  [(extend ((x any) ...) (x_1 ...) (any_1 ...))
   ((x_1 any_1) ... (x any) ...)])

(define-metafunction RC
  lookup : ((x any) ...) x -> any
  [(lookup ((x_1 any_1) ... (x any_t) (x_2 any_2) ...) x)
   any_t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup any_1 any_2)
   (check-the-current-instance any_1 any_2)])

(define-metafunction RC
  interpret-stack : e ε Σ -> rc-result
  [(interpret-stack rc-result ε Σ) rc-result]
  [(interpret-stack (raises e) ε Σ) stuck]
  [(interpret-stack x ε Σ) (lookup Σ (lookup ε x))])

(define-metafunction RC
  eval-stackful : e -> rc-result
  [(eval-stackful e) (interpret-stack e () ())])
  
