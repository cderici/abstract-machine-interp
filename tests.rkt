#lang racket

(require redex "main.rkt")

(define-metafunction RC
  test-both : e rc-result -> any
  [(test-both e rc-result_expected)
   ,(begin (test-equal (term (eval-stackful e)) (term (eval-cek e)))
           (test-equal (term (eval-stackful e)) (term rc-result_expected)))])


(term (test-both 2 2))
(term (test-both true true))
(term (test-both (+ 1 true) stuck))
(term (test-both (+ 1 (+ 2 true)) stuck))
(term (test-both (begin 1) 1))
(term (test-both (begin 1 2) 2))
(term (test-both (begin 1 (+ 2 3)) 5))
(term (test-both (lambda (x) 3) (closure x 3 ())))
(term (test-both (+ 2 (* 3 2)) 8))
(term (test-both (if true 3 -3) 3))
(term (test-both (if false 3 -3) -3))
(term (test-both (if (< 0 1) 3 -3) 3))
(term (test-both (let-values (((a) 1)) 3) 3))
(term (test-both (let-values (((a) 1)) a) 1))
(term (test-both (let-values (((a) (+ 1 2))) a) 3))
(term (test-both (let-values (((a) 1) ((b) 2)) b) 2))
(term (test-both (let-values (((a) (+ 1 2)) ((b) 4)) (* a b)) 12))
(term (test-both (let-values (((a) 1)) (begin (set! a 35) a)) 35))
(term (test-both (let-values (((a) (+ 1 2))) (let-values (((b) (begin (set! a 1) 4))) (* a b))) 4))
(term (test-both (let-values (((a) (lambda (n) n))) (a 3)) 3))
(term (test-both (let-values (((a) (lambda (n) (if (< n 1) 1 3)))) (a 5)) 3))
(term (test-both (let-values (((a) 1)) (let-values (((bv) 3)) (+ a bv))) 4))
(term (test-both (let-values (((a) 1)) (let-values (((f) (lambda () a))) a)) 1))
(term (test-both (let-values (((a) 1)) (let-values (((a) 5)) a)) 5))
(term (test-both (let-values (((a) 1)) (let-values (((f) (lambda () a))) (f))) 1))
(term (test-both (let-values (((a) 1)) (let-values (((f) (lambda () a))) (let-values (((a) 5)) (f)))) 1))

;(term (test-both (letrec-values () 3) 3))
;(test-equal (term (eval-cek (letrec-values () 3))) 3)
(test-equal (term (eval-stackful (letrec-values () 3))) 3)
(test-equal (term (eval-stackful (letrec-values (((a) 2)) 3))) 3)
(term (test-both (letrec-values (((a) 1)) 3) 3))
(term (test-both (letrec-values (((a) 1)) a) 1))
(term (test-both (letrec-values (((a) 1) ((b) 2)) b) 2))
(test-equal (term (eval-stackful (letrec-values (((a) 2) ((b) 1)) a))) 2)
(test-equal (term (eval-stackful (letrec-values (((a) 2) ((b) 1)) b))) 1)
(test-equal (term (eval-stackful (letrec-values (((a) 2) ((b) a)) 3))) 3)
(test-equal (term (eval-stackful (letrec-values (((a) 2) ((b) a)) b))) 2)

(term (test-both (letrec-values (((a) (lambda (n) n))) 3) 3))
(term (test-both (letrec-values (((a) (lambda (n) n))) (a 3)) 3))
(term (test-both (letrec-values (((a) (lambda (n) (if (< n 1) 1 0)))) 1) 1))
(term (test-both (letrec-values (((a) (lambda (n) (if (< n 1) 1 (a 0))))) (a 5)) 1))
(term (test-both (letrec-values (((fact) (lambda (n) (if (< n 1) 1 (* n (fact (sub1 n)))))))
                                   (fact 5)) 120))
(term (test-both ((lambda (x) x) 3) 3))
(term (test-both (raises 1) stuck))


;; switch stuff

(test-equal (term (eval-cek (+ 1 (convert-to-stackful (+ 2 3))))) 6)
(test-equal (term (eval-cek (let-values (((a) (convert-to-stackful (+ 1 2)))) a))) 3)
(test-equal (term (eval-cek (let-values (((a) 3)) (convert-to-stackful (let-values (((b) 1)) (+ a b)))))) 4)
(test-equal (term (eval-cek (let-values (((a) 3)) (begin (convert-to-stackful (set! a 5)) a)))) 5)

(test-equal (term (eval-stackful (+ 1 (convert-to-cek (+ 2 3))))) 6)
(test-equal (term (eval-stackful (let-values (((a) (convert-to-cek (+ 1 2)))) a))) 3)
(test-equal (term (eval-stackful (let-values (((a) 3)) (convert-to-cek (let-values (((b) 1)) (+ a b)))))) 4)
(test-equal (term (eval-stackful (let-values (((a) 3)) (begin (convert-to-cek (set! a 5)) a)))) 5)

(test-equal (term (eval-stackful (letrec-values (((fact) (lambda (n) (if (< n 1) 1 (* n (fact (sub1 n)))))))
                                   (fact 20)))) 2432902008176640000)

;; convert stack to heap

(test-equal (term (eval-stackful (convert-stack (+ 1 2)))) 3)

(test-equal (term (interpret-stack (convert-stack (< 1 2)) () () 0))
            (term (convert-stack-to-heap (< 1 2) () () ())))
(test-equal (term (interpret-stack (if (< 1 2) 3 4) () () 0)) (term (3 () 0)))
(test-equal (term (interpret-stack (if (convert-stack (< 1 2)) 3 4) () () 0))
            (term (convert-stack-to-heap (< 1 2) () () ((if-κ 3 4)))))
(test-equal (term (eval-stackful (if (convert-stack (< 1 2)) 3 4))) 3)

(test-equal (term (eval-stackful (+ (convert-stack 1) 2))) 3)
(test-equal (term (eval-stackful (+ 1 (convert-stack 2)))) 3)
(test-equal (term (eval-stackful (if (< (convert-stack 1) 2) 3 4))) 3)
(test-equal (term (eval-stackful (begin (+ 1 (convert-stack (+ 2 3))) 4))) 4)

(test-equal (term (eval-stackful (let-values (((a) (convert-stack (+ 1 2)))) a))) 3)
(test-equal (term (eval-stackful (let-values (((a) (convert-stack (+ 1 2))) ((b) 4)) (+ a b)))) 7)
(test-equal (term (eval-stackful (let-values (((b) 4) ((a) (convert-stack (+ 1 2)))) (+ a b)))) 7)

#;(test-equal (term (eval-stackful (letrec-values (((a) (convert-stack (+ 1 2)))) a))) 3)
#;(test-equal (term (eval-stackful (letrec-values (((a) (convert-stack (+ 1 2))) ((b) 4)) (+ a b)))) 7)
#;(test-equal (term (eval-stackful (letrec-values (((b) 4) ((a) (convert-stack (+ 1 2)))) (+ a b)))) 7)
(test-equal (term (eval-stackful ((lambda (x) x) (convert-stack 3)))) 3)
(test-equal (term (eval-stackful ((convert-stack (lambda (x) x)) 3))) 3)
(test-equal (term (eval-stackful ((lambda (x y) x) (convert-stack 3) 4))) 3)
(test-equal (term (eval-stackful ((lambda (x y) x) 3 (convert-stack 4)))) 3)
(test-equal (term (eval-stackful (let-values (((a) 3)) (begin (convert-stack (set! a 5)) a)))) 5)
(test-equal (term (eval-stackful (let-values (((a) 3)) (begin (set! a (convert-stack 5)) a)))) 5)

(test-equal (term (eval-stackful (letrec-values (((fact) (lambda (n) (if (< n 1) (convert-stack 1) (* n (fact (sub1 n))))))) (fact 5)))) 120)


;;;;;;;;

(test-equal (term (interpret-stack a ((a s0) (b s1)) ((s0 1) (s1 2)) 0)) (term (1 ((s0 1) (s1 2)) 0)))
(test-equal (term (interpret-stack (+ 1 5) () () 0)) (term (6 () 0)))
(test-equal (term (interpret-stack (+ 1 5 (+ 2 3)) () () 0)) (term (11 () 0)))
(test-equal (term (interpret-stack (lambda (x) 3) ((a s0)) ((s0 1)) 0)) (term ((closure x 3 ((a s0))) ((s0 1)) 0)))
(test-equal (term (interpret-stack (set! a 35) ((a s0)) ((s0 1)) 0)) (term ((void) ((s0 35)) 0)))

(test-equal (term (eval-stackful (raise-depth))) (term (stack-depth-exn 0)))
(test-equal (term (eval-stackful (+ 1 (raise-depth)))) (term (stack-depth-exn 1)))
(test-equal (term (eval-stackful (+ 1 (+ 2 (raise-depth))))) (term (stack-depth-exn 2)))
(test-equal (term (eval-stackful (begin 1 (raise-depth) 3))) (term (stack-depth-exn 1)))
(test-equal (term (eval-stackful ((lambda (x y) x) 1 (raise-depth)))) (term (stack-depth-exn 1)))
(test-equal (term (eval-stackful (let-values (((a) (raise-depth))) 3))) (term (stack-depth-exn 1)))
(test-equal (term (eval-stackful (let-values (((a) 3)) (raise-depth)))) (term (stack-depth-exn 0)))
(test-equal (term (eval-stackful (let-values (((a) 3))
                                   (let-values (((b) 1))
                                     (raise-depth)))))
            (term (stack-depth-exn 0)))
(test-equal (term (eval-stackful (let-values (((a) (let-values (((b) (raise-depth)))
                                                     1)))
                                   2)))
            (term (stack-depth-exn 2)))
(test-equal (term (eval-stackful (letrec-values (((fact)
                                                  (lambda (n)
                                                    (if (< n 1)
                                                        (raise-depth)
                                                        (* n (fact (sub1 n)))))))
                                   (fact 5))))
            (term (stack-depth-exn 5)))
