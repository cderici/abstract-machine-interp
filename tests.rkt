#lang racket

(require redex "main.rkt")

(test-equal (term (eval-stackful 2)) 2)
(test-equal (term (eval-stackful (raises 1))) (term stuck))
