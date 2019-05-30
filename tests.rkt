#lang racket

(require redex "main.rkt")

(test-equal (term (eval-stackful 2)) 2)
(test-equal (term (eval-stackful (raises 1))) (term stuck))
(test-equal (term (interpret-stack a ((a s0) (b s1)) ((s0 1) (s1 2)))) 1)
