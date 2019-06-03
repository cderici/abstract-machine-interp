#lang racket

(require redex)

(provide (all-defined-out))

(define-language RC
  [e   ::= x v (e e ...) (if e e e) (op e ...)
       (set! x e) (begin e e ...)
       (lambda (x_!_ ...) e)
       (let-values (((x_!_) e) ...) e)
       (letrec-values (((x_!_) e) ...) e)
       (raises e) (raise-depth)] ;; expressiosn
  [v   ::= n b c (void)] ;; values
  [c   ::= (closure x ... e ε)]
  [n   ::= number]
  [b   ::= true false]
  [x cell ::= variable-not-otherwise-mentioned] ;; variables
  [op  ::= add1 + * < sub1]

  [ε   ::= ((x any) ...)] ;; environment
  [Σ   ::= ((x any) ...)] ;; store

  [exception ::= (stack-depth-exn n)]
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
  eval-stackful : e -> rc-result or exception
  [(eval-stackful e) rc-result
                     (where (rc-result Σ n) (interpret-stack e () () 0))]
  [(eval-stackful e) exception
                     (where exception (interpret-stack e () () 0))]
  [(eval-stackful _) stuck])

(define-metafunction RC
  ; (expr env store stack-depth) -> (result store stack-depth)
  interpret-stack : e ε Σ n -> (rc-result Σ n) or exception
  [(interpret-stack (raises e) ε Σ n) (stuck Σ n)] ; for intermediate errors
  [(interpret-stack (raise-depth) ε Σ n) (stack-depth-exn n)]
  [(interpret-stack rc-result ε Σ n) (rc-result Σ n)]
  [(interpret-stack x ε Σ n) ((lookup Σ (lookup ε x)) Σ n)]
  [(interpret-stack (lambda (x ...) e) ε Σ n) ((closure x ... e ε) Σ n)]
  ; set!
  [(interpret-stack (set! x e) ε Σ n)
   ((void) (overwrite Σ_1 (lookup ε x) v) n)
   (where (v Σ_1 n_1) (interpret-stack e ε Σ ,(add1 (term n))))]
  ; op
  [(interpret-stack (op v ...) ε Σ n) ((δ (op v ...)) Σ n)]
  [(interpret-stack (op v ... e_1 e ...) ε Σ n)
   (interpret-stack (op v ... v_1 e ...) ε Σ_1 n)
   (side-condition (not (redex-match? RC v (term e_1))))
   (where (v_1 Σ_1 n_1) (interpret-stack e_1 ε Σ ,(add1 (term n))))]
  [(interpret-stack (op v ... e_1 e ...) ε Σ n)
   (stuck Σ_1 n_1)
   (where (stuck Σ_1 n_1) (interpret-stack e_1 ε Σ ,(add1 (term n))))]
  [(interpret-stack (op v ... e_1 e ...) ε Σ n)
   exception
   (where exception (interpret-stack e_1 ε Σ ,(add1 (term n))))]
  ; begin
  [(interpret-stack (begin v ... e_1 e_2 e ...) ε Σ n)
   (interpret-stack (begin v ... v_1 e_2 e ...) ε Σ_1 n)
   (side-condition (not (redex-match? RC v (term e_1))))
   (where (v_1 Σ_1 n_1) (interpret-stack e_1 ε Σ ,(add1 (term n))))]
  [(interpret-stack (begin v ... e_1 e_2 e ...) ε Σ n)
   exception
   (where exception (interpret-stack e_1 ε Σ ,(add1 (term n))))]
  [(interpret-stack (begin v ... e) ε Σ n) ; tail
   (interpret-stack e ε Σ n)]
  ; if
  [(interpret-stack (if e_test e_1 e_2) ε Σ n)
   ,(if (equal? (term v_1) (term true))
        (term (interpret-stack e_1 ε Σ_1 n)) ;; tail
        (term (interpret-stack e_2 ε Σ_1 n)))
   (where (v_1 Σ_1 n_1) (interpret-stack e_test ε Σ n))]
  ; let-values
  [(interpret-stack (let-values (((x) v) ...) e_body) ε Σ n)
   (interpret-stack e_body (extend ε (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v ...)) n)
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))] ; tail
  [(interpret-stack (let-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ε Σ n)
   (interpret-stack (let-values (((x_1) v_1) ... ((x) v) ((x_r) e_r) ...) e_body) ε Σ_1 n)
   (side-condition (not (redex-match? RC v (term e))))
   (where (v Σ_1 n_1) (interpret-stack e ε Σ ,(add1 (term n))))]
  [(interpret-stack (let-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ε Σ n)
   exception
   (where exception (interpret-stack e ε Σ ,(add1 (term n))))]
  ; letrec-values
  [(interpret-stack (letrec-values (((x) v) ...) v_body) ε Σ n) (v_body Σ n)]
  [(interpret-stack (letrec-values (((x) v) ...) e_body) ε Σ n)
   (interpret-stack e_body (extend ε (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v ...)) n)
   (side-condition (not (redex-match? RC v (term e_body))))
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))]
  [(interpret-stack (letrec-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ε Σ n)
   (interpret-stack (letrec-values (((x_1) v_1) ... ((x) v) ((x_r) e_r) ...) e_body) ε (extend Σ_1 (x_addr) (v)) n)
   (side-condition (not (redex-match? RC v (term e))))
   (where x_addr ,(variable-not-in (term (e_body x_1 ... x x_r ...)) (term x)))
   (where (v Σ_1 n) (interpret-stack e (extend ε (x) (x_addr)) Σ n))]
  ; app
  [(interpret-stack (x_func e ...) ε Σ n)
   (interpret-stack (v_func e ...) ε Σ n)
   (where v_func (lookup Σ (lookup ε x_func)))]
  [(interpret-stack ((closure x ... e_body ε_closure) v_args ...) ε Σ n)
   (interpret-stack e_body (extend ε_closure (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v_args ...)) n)
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))]
  [(interpret-stack ((closure x ... e_body ε_closure) v_args ... e_arg_1 e_args ...) ε Σ n)
   (interpret-stack ((closure x ... e_body ε_closure) v_args ... v_arg_1 e_args ...) ε Σ_1 n)
   (side-condition (not (redex-match? RC v (term e_arg_1))))
   (where (v_arg_1 Σ_1 n_1) (interpret-stack e_arg_1 ε Σ ,(add1 (term n))))]
  [(interpret-stack ((closure x ... e_body ε_closure) v_args ... e_arg_1 e_args ...) ε Σ n)
   exception
   (where exception (interpret-stack e_arg_1 ε Σ ,(add1 (term n))))]
  [(interpret-stack (e_f e_args ...) ε Σ n)
   (interpret-stack (v_func e_args ...) ε Σ n)
   (where (v_func Σ_1 n_1) (interpret-stack e_f ε Σ ,(add1 (term n))))]
  [(interpret-stack (e_f e_args ...) ε Σ n)
   exception
   (where exception (interpret-stack e_f ε Σ ,(add1 (term n))))]
  )
