#lang racket

(require redex)

(provide (all-defined-out))

(define-language RC
  [e   ::= x v (e e ...) (if e e e) (op e ...)
       (set! x e) (begin e e ...)
       (lambda (x_!_ ...) e)
       (let-values (((x_!_) e) ...) e)
       (letrec-values (((x_!_) e) ...) e)
       (raises e)] ;; expressiosn
  [v   ::= n b c (void)] ;; values
  [c   ::= (closure x ... e ε)]
  [n   ::= number]
  [b   ::= true false]
  [x cell ::= variable-not-otherwise-mentioned] ;; variables
  [op  ::= add1 + * < sub1]

  [ε   ::= ((x any) ...)] ;; environment
  [Σ   ::= ((x any) ...)] ;; store

  [rc-result ::= v stuck]

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (let-values ([(x) e_x] ...) e_body #:refers-to (shadow x ...))
  (letrec-values ([(x) e_x] ...) #:refers-to (shadow x ...) e_body #:refers-to (shadow x ...))
  )

(define-metafunction RC
  δ : (op any ...) -> v or stuck
  [(δ (add1 n)) ,(add1 (term n))]
  [(δ (sub1 n)) ,(sub1 (term n))]
  [(δ (< n_1 n_2)) ,(if (< (term n_1) (term n_2)) (term true) (term false))]
  [(δ (+ n ...)) ,(apply + (term (n ...)))]
  [(δ (* n ...)) ,(apply * (term (n ...)))]
  [(δ (op any_1 any_2 ...)) stuck])

(define-metafunction RC
  extend : ((x any) ...)  (x ...) (any ...) -> ((x any) ...)
  [(extend ((x any) ...) (x_1 ...) (any_1 ...))
   ((x_1 any_1) ... (x any) ...)])

(define-metafunction RC
  overwrite : ((x any) ...) x v -> ((x any) ...)
  [(overwrite ((x_before v_before) ... (x any) (x_after v_after) ...) x_1 v)
   ((x_before v_before) ... (x v) (x_after v_after) ...)
   (side-condition (equal? (term x) (term x_1)))])

(define-metafunction RC
  lookup : ((x any) ...) x -> any
  [(lookup ((x_1 any_1) ... (x any_t) (x_2 any_2) ...) x)
   any_t
   (side-condition (not (member (term x) (term (x_1 ...)))))]
  [(lookup ((x any) ...) _) stuck])

(define-metafunction RC
  eval-stackful : e -> rc-result
  [(eval-stackful e) rc-result
                     (where (rc-result Σ) (interpret-stack e () ()))]
  [(eval-stackful _) stuck])

(define-metafunction RC
  interpret-stack : e ε Σ -> (rc-result Σ)
  [(interpret-stack (raises e) ε Σ) (stuck Σ)] ; for intermediate errors
  [(interpret-stack rc-result ε Σ) (rc-result Σ)]
  [(interpret-stack x ε Σ) ((lookup Σ (lookup ε x)) Σ)]
  [(interpret-stack (lambda (x ...) e) ε Σ) ((closure x ... e ε) Σ)]
  [(interpret-stack (set! x e) ε Σ) ((void) (overwrite Σ_1 (lookup ε x) v))
                                    (where (v Σ_1) (interpret-stack e ε Σ))]
  [(interpret-stack (op v ...) ε Σ) ((δ (op v ...)) Σ)]
  [(interpret-stack (op v ... e_1 e ...) ε Σ)
   (interpret-stack (op v ... v_1 e ...) ε Σ_1)
   (side-condition (not (redex-match? RC v (term e_1))))
   (where (v_1 Σ_1) (interpret-stack e_1 ε Σ))]
  [(interpret-stack (begin v ... v_1) ε Σ) (v_1 Σ)]
  [(interpret-stack (begin v ... e_1 e ...) ε Σ)
   (interpret-stack (begin v ... v_1 e ...) ε Σ_1)
   (side-condition (not (redex-match? RC v (term e_1))))
   (where (v_1 Σ_1) (interpret-stack e_1 ε Σ))]
  ; if
  [(interpret-stack (if e_test e_1 e_2) ε Σ)
   ,(if (equal? (term v_1) (term true))
        (term (interpret-stack e_1 ε Σ_1))
        (term (interpret-stack e_2 ε Σ_1)))
   (where (v_1 Σ_1) (interpret-stack e_test ε Σ))]
  ; let-values
  [(interpret-stack (let-values (((x) v) ...) v_body) ε Σ) (v_body Σ)]
  [(interpret-stack (let-values (((x) v) ...) e_body) ε Σ)
   (interpret-stack e_body (extend ε (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v ...)))
   (side-condition (not (redex-match? RC v (term e_body))))
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))]
  [(interpret-stack (let-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ε Σ)
   (interpret-stack (let-values (((x_1) v_1) ... ((x) v) ((x_r) e_r) ...) e_body) ε Σ_1)
   (side-condition (not (redex-match? RC v (term e))))
   (where (v Σ_1) (interpret-stack e ε Σ))]
  ; app
  [(interpret-stack (x_func e ...) ε Σ)
   (interpret-stack (v_func e ...) ε Σ)
   (where v_func (lookup Σ (lookup ε x_func)))]
  [(interpret-stack ((closure x ... e_body ε_closure) v_args ...) ε Σ)
   (interpret-stack e_body (extend ε_closure (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v_args ...)))
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))]
  [(interpret-stack ((closure x ... e_body ε_closure) v_args ... e_arg_1 e_args ...) ε Σ)
   (interpret-stack ((closure x ... e_body ε_closure) v_args ... v_arg_1 e_args ...) ε Σ_1)
   (side-condition (not (redex-match? RC v (term e_arg_1))))
   (where (v_arg_1 Σ_1) (interpret-stack e_arg_1 ε Σ))]
  ; letrec-values
  [(interpret-stack (letrec-values (((x) v) ...) v_body) ε Σ) (v_body Σ)]
  [(interpret-stack (letrec-values (((x) v) ...) e_body) ε Σ)
   (interpret-stack e_body (extend ε (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v ...)))
   (side-condition (not (redex-match? RC v (term e_body))))
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))]
  [(interpret-stack (letrec-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ε Σ)
   (interpret-stack (letrec-values (((x_1) v_1) ... ((x) v) ((x_r) e_r) ...) e_body) ε (extend Σ_1 (x_addr) (v)))
   (side-condition (not (redex-match? RC v (term e))))
   (where x_addr ,(variable-not-in (term (e_body x_1 ... x x_r ...)) (term x)))
   (where (v Σ_1) (interpret-stack e (extend ε (x) (x_addr)) Σ))]
  [(interpret-stack _ ε Σ) (stuck Σ)]
  )
