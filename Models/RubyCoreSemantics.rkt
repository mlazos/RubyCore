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
      (proc (x ...) e))
  ;complex expressions
  (ce (do e ...)
      (+ e ...)
      (if e e e)
      ;apply
      (app e (e ...))
      ;apply with block
      (app-b e e)
      (ret e)
      (let ((x e) ...) e))
  ;all expressions
  (e ce
     ae
     x) 
  ;configuration definitions
  (sto ((x ae) ...))
  (env ((x x) ...))
  (kont (k-do x e env kont) ;keep environment if do
        (k-ret kont) ;originating from a block call
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
        (e ((x x_a) . env_k) ((x_a ae) . sto) kont)
        (where x_a ,(gensym)))
   (--> (ae env sto (k-do x e env_k kont))
        (e ((x x_a) . env) ((x_a ae) . sto) kont)
        (where x_a ,(gensym)))
   
   ;id lookup
   (--> (x_1 ((x_2 x_3) ...) sto kont)
        (ae_ans ((x_2 x_3) ...) sto kont)
        ;(side-condition (member (term x) (term env)))
        (where x_ans (env-lookup x_1 ((x_2 x_3) ...)))
        (where ae_ans (sto-lookup x_ans sto)))
   
   ;if 
   (--> ((if #t e_t e_f) env sto kont)
        (e_t env sto kont))   
   (--> ((if #f e_t e_f) env sto kont)
        (e_f env sto kont))
   (--> ((if ce e_t e_f) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (if ce e_t e_f) env kont)))   
   (--> ((if x e_t e_f) env sto kont)
        ((if ae_new e_t e_f) env sto kont)
        (where ae_new (lookup x env sto)))
   
   ;let            
   (--> ((let ((x e)) e_body) env sto kont)
        (e env sto (x e_body env kont)))   
   (--> ((app e_f (e_1 ...)) env sto kont)
        (e_f env sto kont_new)
        (where kont_new (gen-kont (app e_f (e_1 ...)) env kont)))
   
   ;do
   (--> ((do e_1 e_2 ...) env sto kont)
        (e_1 env sto kont_new)
        (where kont_new (gen-kont (do e_1 e_2 ...) env kont)))   
   (--> ((do) env sto kont)
        (e env sto kont))
   
   ;return
   (--> ((ret ae) env sto (k-ret kont))
        (ae env sto kont))
   (--> ((ret ae) env sto (k x e env kont))
        ((ret ae) env sto kont))
   (--> ((ret ae) env sto (k-do x e env kont))
        ((ret ae) env sto kont))
   (--> ((ret ce) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (ret ce) env kont)))
   
   ;yield
   
   ))

(define-metafunction ruby-core
  gen-kont : e env kont -> kont  
  [(gen-kont (app e_f (e_1 ...)) env kont)
   ,(let ((s (gensym))) (term (k ,s (app ,s (e_1 ...)) env kont)))]
  [(gen-kont (do e_1 e_2 ...) env kont)
   ,(let ((s (gensym))) (term (k-do ,s (do e_2 ...) env kont)))]
  [(gen-kont (if e e_t e_f) env kont)
   ,(let ((s (gensym))) (term (k ,s (if ,s e_t e_f) env kont)))]
  [(gen-kont (ret ce) env kont)
   ,(let ((s (gensym))) (term (k ,s (ret ,s) env kont)))])

(define-metafunction ruby-core
  env-lookup : x env -> x
  [(env-lookup x_s ((x_1 x_2) (x_3 x_4) ...))
   ,(if (equal? (term x_s) (term x_1))
        (term x_2)
        (term (env-lookup (term x_s) (term ((x_3 x_4) ...)))))])

(define-metafunction ruby-core
  sto-lookup : x sto -> ae
  [(sto-lookup x_s ((x_1 ae_1) (x_2 ae_2) ...))
   ,(if (equal? (term x_s) (term x_1))
        (term ae_1)
        (term (sto-lookup (term x_s) (term ((x_2 ae_2) ...)))))])

(define-metafunction ruby-core
  lookup : x env sto -> ae
  [(lookup x_s env sto )
   (sto-lookup (env-lookup x_s env) sto)])


;if 
(test-->> rc-red (term ((if #t 3 5) () () halt)) (term (3 () () halt)))
(test-->> rc-red (term ((if #f 4 5) () () halt)) (term (5 () () halt)))

;id lookup
(test-->> rc-red (term (t ((t g123)) ((g123 #t)) halt))
          (term (#t ((t g123)) ((g123 #t)) halt)))




;test by eye
(rr (term ((if (if #t #f #t) 4 5) () () halt)))
(rr (term ((if #t #f #t)
   ()
   ()
   (k g409368 (if g409368 4 5) () halt))))
(rr (term (#f
   ()
   ()
   (k g409368 (if g409368 4 5) () halt))))
(rr (term ((if g409368 4 5)
   ((g409368 g413767))
   ((g413767 #f))
   halt)))
(rr (term ((do t) ((t g123)) ((g123 #f)) halt)))

(test-results)