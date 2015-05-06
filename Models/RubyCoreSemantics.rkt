#lang racket
(require redex)

(define-language ruby-core
  (e 
     number
     string
     boolean
     empty
     (do e ...)
     (+ e ...)
     (list e ... empty)
     (if e e e)
     (lam (x ...) e)
     (proc (x ...) e)
     (app e (e ...))
     (app-b e e)
     (ret e)
     (let ((x e) ...) e)
     x) 
  (addr string)
  (sto ((addr e) ...))
  (env ((x addr) ...))
  (kont (x e env kont) 
        halt)
  (CF (e env sto kont))
  (x variable-not-otherwise-mentioned)
)  

(define rc-red
  (reduction-relation
   ruby-core
   
#|
(define postfix-red
  (reduction-relation
   PFL #:domain CF
   (--> ((N C ...) S)
        ((C ...) (N . S))
        PF-Num)
   (--> ((Q C ...) S)
        ((C ...) (Q . S))
        PF-CmdSeq)
   (--> ((pop C ...) (V_f V_r ...))
        ((C ...) (V_r ...))
        PF-Pop)
   (--> ((swap C ...) (V_1 V_2 V_r ...))
        ((C ...) (V_2 V_1 V_r ...))
        PF-Swap)
   (--> ((sel C ...) (V_f V_t 0 V_r ...))
        ((C ...) (V_f V_r ...))
        PF-SelFalse)
   (--> ((sel C ...) (V_f V_t N V_r ...))
        ((C ...) (V_t V_r ...))
        (side-condition (not (zero? (term N))))
        PF-SelTrue)
   (--> ((exec C ...) ((C_Q ...) V_r ...))
        ((C_Q ... C ...) (V_r ...))
        PF-Exec)
   (--> ((A C ...) (N_1 N_2 V_r ...))
        ((C ...) (N_ans V_r ...))
        (where N_ans (calculate A N_1 N_2))
        PF-Arith)
   (--> ((R C ...) (N_1 N_2 V_r ...))
        ((C ...) (N_ans V_r ...))
        (where N_ans (compare R N_1 N_2))
        PF-Rel)
   (--> ((nget C ...) (N_i V_r ...))
        ((C ...) (V_ans V_r ...))
        (side-condition (and (> (term N_i) 0) (<= (term N_i) (length (term (V_r ...))))))
        (where V_ans ,(list-ref (term (V_r ...)) (sub1 (term N_i))))
        PF-Nget)))
|#
