#lang racket

(require redex)

(provide (all-defined-out))

(define-language RC
  [e   ::= x v (e e ...) (if e e e) (op e ...)
       (set! x e) (begin e e ...)
       (lambda (x_!_ ...) e)
       (let-values (((x_!_) e) ...) e)
       (letrec-values (((x_!_) e) ...) e)
       (raises e) (raise-depth) (convert-to-stackful e) (convert-to-cek e)] ;; expressiosn
  [v   ::= n b c (void)] ;; values
  [c   ::= (closure x ... e ρ)]
  [n   ::= number]
  [b   ::= true false]
  [x cell ::= variable-not-otherwise-mentioned] ;; variables
  [op  ::= add1 + * < sub1]

  [ρ   ::= ((x any) ...)] ;; environment
  [Σ   ::= ((x any) ...)] ;; store

  ;[convert ::= (convert-stack e)]
  [exception ::= (stack-depth-exn n) (convert-to-cek-exn e ρ Σ)]
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
  dynamic-eval-stackful : e ρ Σ -> (rc-result Σ) or exception
  [(dynamic-eval-stackful e ρ Σ) (rc-result Σ_new)
                                 (where (rc-result Σ_new n_new) (interpret-stack e ρ Σ 0))]
  [(dynamic-eval-stackful e ρ Σ) exception
                                 (where exception (interpret-stack e ρ Σ 0))]
  [(dynamic-eval-stackful _ ρ Σ) (stuck Σ)])

(define-metafunction RC
  ; (expr env store stack-depth) -> (result store stack-depth)
  interpret-stack : e ρ Σ n -> (rc-result Σ n) or exception
  [(interpret-stack (raises e) ρ Σ n) (stuck Σ n)] ; for intermediate errors
  [(interpret-stack (raise-depth) ρ Σ n) (stack-depth-exn n)]
  [(interpret-stack (convert-to-cek e) ρ Σ n)
   (rc-result Σ_new n)
   (where (rc-result Σ_new) (run-cek (e ρ Σ ())))]
  [(interpret-stack rc-result ρ Σ n) (rc-result Σ n)]
  [(interpret-stack x ρ Σ n) ((lookup Σ (lookup ρ x)) Σ n)]
  [(interpret-stack (lambda (x ...) e) ρ Σ n) ((closure x ... e ρ) Σ n)]
  ; set!
  [(interpret-stack (set! x e) ρ Σ n)
   ((void) (overwrite Σ_1 (lookup ρ x) v) n)
   (where (v Σ_1 n_1) (interpret-stack e ρ Σ ,(add1 (term n))))]
  ; op
  [(interpret-stack (op v ...) ρ Σ n) ((δ (op v ...)) Σ n)]
  [(interpret-stack (op v ... e_1 e ...) ρ Σ n)
   (interpret-stack (op v ... v_1 e ...) ρ Σ_1 n)
   (side-condition (not (redex-match? RC v (term e_1))))
   (where (v_1 Σ_1 n_1) (interpret-stack e_1 ρ Σ ,(add1 (term n))))]
  [(interpret-stack (op v ... e_1 e ...) ρ Σ n)
   (stuck Σ_1 n_1)
   (where (stuck Σ_1 n_1) (interpret-stack e_1 ρ Σ ,(add1 (term n))))]
  [(interpret-stack (op v ... e_1 e ...) ρ Σ n)
   exception
   (where exception (interpret-stack e_1 ρ Σ ,(add1 (term n))))]
  ; begin
  [(interpret-stack (begin v ... e_1 e_2 e ...) ρ Σ n)
   (interpret-stack (begin v ... v_1 e_2 e ...) ρ Σ_1 n)
   (side-condition (not (redex-match? RC v (term e_1))))
   (where (v_1 Σ_1 n_1) (interpret-stack e_1 ρ Σ ,(add1 (term n))))]
  [(interpret-stack (begin v ... e_1 e_2 e ...) ρ Σ n)
   exception
   (where exception (interpret-stack e_1 ρ Σ ,(add1 (term n))))]
  [(interpret-stack (begin v ... e) ρ Σ n) ; tail
   (interpret-stack e ρ Σ n)]
  ; if
  [(interpret-stack (if e_test e_1 e_2) ρ Σ n)
   ,(if (equal? (term v_1) (term false))
        (term (interpret-stack e_2 ρ Σ_1 n)) ;; tail
        (term (interpret-stack e_1 ρ Σ_1 n)))
   (where (v_1 Σ_1 n_1) (interpret-stack e_test ρ Σ n))]
  ; let-values
  [(interpret-stack (let-values (((x) v) ...) e_body) ρ Σ n)
   (interpret-stack e_body (extend ρ (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v ...)) n)
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))] ; tail
  [(interpret-stack (let-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ρ Σ n)
   (interpret-stack (let-values (((x_1) v_1) ... ((x) v) ((x_r) e_r) ...) e_body) ρ Σ_1 n)
   (side-condition (not (redex-match? RC v (term e))))
   (where (v Σ_1 n_1) (interpret-stack e ρ Σ ,(add1 (term n))))]
  [(interpret-stack (let-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ρ Σ n)
   exception
   (where exception (interpret-stack e ρ Σ ,(add1 (term n))))]
  ; letrec-values
  [(interpret-stack (letrec-values (((x) v) ...) v_body) ρ Σ n) (v_body Σ n)]
  [(interpret-stack (letrec-values (((x) v) ...) e_body) ρ Σ n)
   (interpret-stack e_body (extend ρ (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v ...)) n)
   (side-condition (not (redex-match? RC v (term e_body))))
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))]
  [(interpret-stack (letrec-values (((x_1) v_1) ... ((x) e) ((x_r) e_r) ...) e_body) ρ Σ n)
   (interpret-stack (letrec-values (((x_1) v_1) ... ((x) v) ((x_r) e_r) ...) e_body) ρ (extend Σ_1 (x_addr) (v)) n)
   (side-condition (not (redex-match? RC v (term e))))
   (where x_addr ,(variable-not-in (term (e_body x_1 ... x x_r ...)) (term x)))
   (where (v Σ_1 n) (interpret-stack e (extend ρ (x) (x_addr)) Σ n))]
  ; app
  [(interpret-stack (x_func e ...) ρ Σ n)
   (interpret-stack (v_func e ...) ρ Σ n)
   (where v_func (lookup Σ (lookup ρ x_func)))]
  [(interpret-stack ((closure x ... e_body ρ_closure) v_args ...) ρ Σ n)
   (interpret-stack e_body (extend ρ_closure (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v_args ...)) n)
   (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...))))]
  [(interpret-stack ((closure x ... e_body ρ_closure) v_args ... e_arg_1 e_args ...) ρ Σ n)
   (interpret-stack ((closure x ... e_body ρ_closure) v_args ... v_arg_1 e_args ...) ρ Σ_1 n)
   (side-condition (not (redex-match? RC v (term e_arg_1))))
   (where (v_arg_1 Σ_1 n_1) (interpret-stack e_arg_1 ρ Σ ,(add1 (term n))))]
  [(interpret-stack ((closure x ... e_body ρ_closure) v_args ... e_arg_1 e_args ...) ρ Σ n)
   exception
   (where exception (interpret-stack e_arg_1 ρ Σ ,(add1 (term n))))]
  [(interpret-stack (e_f e_args ...) ρ Σ n)
   (interpret-stack (v_func e_args ...) ρ Σ n)
   (where (v_func Σ_1 n_1) (interpret-stack e_f ρ Σ ,(add1 (term n))))]
  [(interpret-stack (e_f e_args ...) ρ Σ n)
   exception
   (where exception (interpret-stack e_f ρ Σ ,(add1 (term n))))]
  )


;;; CEK

(define-extended-language CEK RC
  [e ::= .... stuck]
  [κ ::= (κ ...)
     (if-κ e e)
     (arg-κ (e ...))
     (fun-κ c (e ...) (v ...))
     (set-κ x)
     (seq-κ e ...)
     (op-κ op (v ...) (e ...) ρ)
     (let-κ (((x) e) ...) (x ...) (v ...) e)
     (letrec-κ (((x) e) ...) (x ...) (cell ...) (v ...) e)])

(define-metafunction CEK
  eval-cek : e -> rc-result or exception
  [(eval-cek e) rc-result
                (where (rc-result Σ) (run-cek (e () () ())))]
  [(eval-cek e) exception
                (where exception (run-cek (e () () ())))])

(define-metafunction CEK
  run-cek : (e ρ Σ κ) -> (rc-result Σ) or exception
  [(run-cek (rc-result ρ Σ ())) (rc-result Σ)]
  [(run-cek ((convert-to-stackful e) ρ Σ κ))
   (run-cek (e_again ρ Σ_again κ))
   (where (e_again Σ_again)
          (dynamic-eval-stackful e ρ Σ))]
  [(run-cek any_1)
   (run-cek (e_again ρ_again Σ_again κ_again))
   (where ((e_again ρ_again Σ_again κ_again))
          ,(apply-reduction-relation -->cek (term any_1)))]
  [(run-cek any) (stuck ())])

(define -->cek
  (reduction-relation
   CEK
   #:domain (e ρ Σ κ)
   ;; this is CESK-like, but only reason for store is to implement
   ;; letrec (we don't have cells)
   (--> [x ρ Σ κ] [(lookup Σ (lookup ρ x)) ρ Σ κ] lookup)
   (--> [(lambda (x ...) e) ρ Σ κ] [(closure x ... e ρ) ρ Σ κ] closure)
   ; plug
   (--> [v_1 ρ Σ ((op-κ op (v ...) () ρ_op) κ ...)]
        [(δ (op v ... v_1)) ρ_op Σ (κ ...)] op-plug)
   (--> [v ρ Σ ((if-κ e_1 e_2) κ ...)]
        [e ρ Σ (κ ...)]
        (where e ,(if (equal? (term v) (term false)) (term e_2) (term e_1)))
        if-true-plug)
   (--> [v ρ Σ ((set-κ x) κ ...)]
        [(void) ρ (overwrite Σ x v) (κ ...)] set-plug)
   (--> [v ρ Σ ((let-κ () (x_rhs ...) (v_rhs ...) e_body) κ ...)]
        [e_body (extend ρ (x_rhs ...) (x_addr ...))
                (extend Σ (x_addr ...) (v v_rhs ...)) (κ ...)]
        (where (x_addr ...) ,(variables-not-in (term e_body) (term (x_rhs ...)))) let-plug)
   (--> [v ρ Σ ((letrec-κ () (x_rhs ...) (cell_rhs ...) (v_rhs ...) e_body) κ ...)]
        [e_body (extend ρ (x_rhs ...) (cell_rhs ...))
                (extend Σ (cell_rhs ...) (v v_rhs ...))
                (κ ...)]
        letrec-plug)
   ; op
   (--> [v_1 ρ Σ ((op-κ op (v ...) (e_1 e ...) ρ_op) κ ...)]
        [e_1 ρ_op Σ ((op-κ op (v ... v_1) (e ...) ρ_op) κ ...)] op-switch)
   (--> [(op e_1 e ...) ρ Σ (κ ...)]
        [e_1 ρ Σ ((op-κ op () (e ...) ρ) κ ...)] op-push)
   ; if
   (--> [(if e_test e_1 e_2) ρ Σ (κ ...)]
        [e_test ρ Σ ((if-κ e_1 e_2) κ ...)] if-push)
   ; set!
   (--> [(set! x e) ρ Σ (κ ...)]
        [e ρ Σ ((set-κ (lookup ρ x)) κ ...)] set-push)
   ; begin
   (--> [(begin e_1 e ...) ρ Σ (κ ...)]
        [e_1 ρ Σ ((seq-κ e ...) κ ...)] begin-push)
   (--> [v ρ Σ ((seq-κ e_1 e ...) κ ...)]
        [e_1 ρ Σ ((seq-κ e ...) κ ...)] begin-switch)
   (--> [v ρ Σ ((seq-κ) κ ...)]
        [v ρ Σ (κ ...)] begin-plug)
   ; let-values
   (--> [v_rhs ρ Σ ((let-κ (((x_1) e_rhs_next) ((x_2) e_2) ...)
                           (x ...) (v ...) e_body) κ ...)]
        [e_rhs_next ρ Σ ((let-κ (((x_2) e_2) ...)
                                (x_1 x ...) (v_rhs v ...) e_body) κ ...)]
        let-rhs-switch)
   (--> [(let-values (((x_rhs) e_rhs) ((x_2) e_2) ...) e_body) ρ Σ (κ ...)]
        [e_rhs ρ Σ ((let-κ (((x_2) e_2) ...) (x_rhs) () e_body) κ ...)] let-push)
   ; letrec-values
   (--> [v_rhs
         ρ Σ ((letrec-κ (((x_rhs_next) e_rhs_next) ((x_2) e_2) ...)
                        (x_rhs x ...) (cell_rhs cell ...) (v ...)
                        e_body) κ ...)]
        [e_rhs_next
         (extend ρ (x_rhs) (cell_rhs_next)) Σ
         ((letrec-κ (((x_2) e_2) ...)
                    (x_rhs_next x_rhs x ...) (cell_rhs_next cell_rhs cell ...) (v_rhs v ...)
                    e_body) κ ...)]
        letrec-rhs-switch)
   (--> [(letrec-values (((x_rhs) e_rhs) ((x_2) e_2) ...) e_body) ρ Σ (κ ...)]
        [e_rhs
         (extend ρ (x_rhs) (cell_addr))
         Σ ((letrec-κ (((x_2) e_2) ...) (x_rhs) (cell_addr) () e_body) κ ...)]
        (where cell_addr ,(variable-not-in (term (e_body x_rhs x_2 ...)) (term cell)))
        letrec-push)
   ; app
   (--> [(e_rator e_rands ...) ρ Σ (κ ...)]
        [e_rator ρ Σ ((arg-κ (e_rands ...)) κ ...)] app-rator-push)
   (--> [(closure x ... e_body ρ_closure) ρ Σ ((arg-κ ()) κ ...)]
        [e_body ρ_closure Σ (κ ...)] app-no-rand-plug)
   (--> [v_closure ρ Σ ((arg-κ (e_rand_1 e_rands ...)) κ ...)]
        [e_rand_1 ρ Σ ((fun-κ v_closure (e_rand_1 e_rands ...) ()) κ ...)] app-rand-push)
   (--> [v_rand ρ Σ ((fun-κ v_closure (e_rand_1 e_rands ...) (v ...)) κ ...)]
        [e_rand_1 ρ Σ ((fun-κ v_closure (e_rands ...) (v_rand v ...)) κ ...)] app-rand-switch)
   (--> [v_rand ρ Σ ((fun-κ (closure x ... e_body ρ_closure) () (v ...)) κ ...)]
        [e_body (extend ρ_closure (x ...) (x_addr ...)) (extend Σ (x_addr ...) (v ...))
                (κ ...)]
        (where (x_addr ...) ,(variables-not-in (term e_body) (term (x ...)))) app-plug)

   ))
