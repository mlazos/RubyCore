#lang racket
(require redex)

(define-language ruby-core
  ;atomic expressions
  (ae number
      string 
      boolean
      empty
      (list e ... empty)
      (lam (x ...) e)
      (proc (x ...) e)
      x)
  ;complex expressions
  (ce (do e ...)
     (+ e ...)
     (if e e e)
     ;apply
     (app e (e ...))
     ;apply with block
     (app-b e e)
     (ret e)
     (let ((x e) ...) e)
     x)
  ;all expressions
  (e ce
     ae) 
  ;configuration definitions
  (sto ((x e) ...))
  (env ((x x) ...))
  (kont (k-do x e env kont) ;keep environment if do
        (k-ret x e env kont) ;originating from a block call
        (k x e env kont) ;normal control point 
        halt) ;base case
  (CF (e env sto kont))
  (x variable-not-otherwise-mentioned))  

(define (rr x) (apply-reduction-relation rc-red x))

(define rc-red
  (reduction-relation
   ruby-core #:domain CF
   ;final configuration
   ;(--> (ae env sto halt)
   
   ;atomic expression - call current continuation
   (--> (ae env sto (k x e env_k kont))
        (e ((x addr) . env_k) ((addr ae) . sto) kont)
        (where addr ,(gensym)))
   (--> (ae env sto (k-do x e env_k kont))
        (e ((x addr) . env) ((addr ae) . sto) kont)
        (where addr ,(gensym)))
                
   ;id lookup
   (--> (x env sto kont)
        (ae_ans env sto kont)
        ;(side-condition (member (term x) (term env)))
        (where loc ,(assoc (term x) (term env)))
        (where ae_ans ,(assoc (term loc) (term sto))))
   
   ;if 
   (--> ((if #t e_t e_f) env sto kont)
        (e_t env sto kont))   
   (--> ((if #f e_t e_f) env sto kont)
        (e_f env sto kont))
   (--> ((if ce e_t e_f) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (if ce e_t e_f) env kont)))
   
   ;let            
   (--> ((let ((x e)) e_body) env sto kont)
        (e env sto (x e_body env kont)))   
   (--> ((app e_f (e_1 ...)) env sto kont)
        (e_f env sto kont_new)
        (where kont_new (gen-kont (app e_f (e_1 ...)) env kont)))
   
   ;do
   (--> ((do e_1 e_2 ...) env sto kont)
        (e_1 env sto kont_new)
        (where kont_new (gen-kont (do e_1 e_2 ...))))   
   (--> ((do e) env sto kont)
        (e env sto kont))

   ))



(define-metafunction ruby-core
  gen-kont : e env kont -> kont  
    [(gen-kont (app e_f (e_1 ...)) env kont)
     ,(let ((s (gensym))) (term (k ,s (app ,s (e_1 ...)) env kont)))]
    [(gen-kont (do e_1 e_2 ...) env kont)
     ,(let ((s (gensym))) (term (k-do ,s (do e_1 e_2 ...) env kont)))]
    [(gen-kont (if e e_t e_f) env kont)
     ,(let ((s (gensym))) (term (k ,s (if ,s e_t e_f) env kont)))])


