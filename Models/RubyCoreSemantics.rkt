#lang racket
(require redex)

;qs for Stevie
;final configuration finishing?
;method of return acceptable?
;how to search through environments
;do return last value

(define-language ruby-core
  ;atomic expressions
  (ae number
      string 
      boolean
      empty
      (list e ... empty)
      (lam (x ...) e)
      (proc (x ...) e))
  (ce (do e ...)
      (+ e ...)
      (if e e e)
      ;apply
      (app e e ...)
      ;apply with block
      (app-b e e)
      (ret e)
      (let (x e) e))
  ;contexts         
  (E (do hole e ...)
      (+ hole e ...)
      (if hole e e)
      ;apply
      (app hole e ...)
      ;apply with block
      (app-b hole e)
      (ret hole)
      (let (x hole) e))
  ;all expressions
  (e ce
     ae
     x) 
  ;configuration definitions
  (sto ((x ae) ...))
  (env ((x x) ...))
  (kont (k-do E env kont) ;keep environment if do
        (k-ret kont) ;originating from a block call
        (k E env kont) ;normal control point 
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
   (--> (ae env sto (k E env_k kont))
        ((in-hole E ae) env sto kont))
   (--> (ae env sto (k-do x e env_k kont))
        ((in-hole E ae) env_k sto kont))
   
   ;id lookup
   (--> (x_1 env sto kont)
        (ae_ans env sto kont)
        ;(side-condition (member (term x) (term env)))
        (where ae_ans (lookup x_1 env sto)))
   
   ;if 
   (--> ((if #t e_t e_f) env sto kont)
        (e_t env sto kont))   
   (--> ((if #f e_t e_f) env sto kont)
        (e_f env sto kont))
   (--> ((if ce e_t e_f) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (if ce e_t e_f) env kont)))   
   
   ;let            
   ;; handle case where bind exp needs to be evaluated
   (--> ((let ((x ce)) e_body) env sto kont)
        (e env sto (e env kont_new))
        (where kont_new (gen-kont (let ((x e)) e_body) env kont)))
   ;; handle binding case
   (--> ((let ((x ae)) e_body) ((x_1 x_2) ...) ((x_3 ae_1) ...) kont)
        (e_body ((x addr) (x_1 x_2) ...) ((addr ae) (x_3 ae_1) ...) kont)
        (where addr ,(gensym)))
   
   ;app
   (--> ((app e_1 e_2 ...) env sto kont)
        (e_1 env sto kont_new)
        (where kont_new (gen-kont (app e_1 e_2 ...) env kont)))
   
   ;do
   (--> ((do e_1 e_2 ...) env sto kont)
        (e_1 env sto kont_new)
        (where kont_new (gen-kont (do e_1 e_2 ...) env kont)))
   
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
  [(gen-kont (app e_1 e_2 ...) env kont)
   (k (app hole e_2 ...) env kont)]
  [(gen-kont (do e_1 e_2 ...) env kont)
   (k-do (do e_2 ...) env kont)] ;remove first expression
  [(gen-kont (if e e_t e_f) env kont)
   (k (if hole e_t e_f) env kont)]
  [(gen-kont (ret ce) env kont)
   (k (ret hole) env kont)]
  [(gen-kont (let ((x e)) e_body) env kont)
   (k (let ((x hole)) e_body) env kont)])

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

(define-metafunction ruby-core
  bound? : x env -> boolean
  [(bound? x_f ((x_f x_fa) (x_2 x_2a) ...))
   #t]
  [(bound? x_f ((x_2 x_2a) (x_3 x_3a) ...))
   (bound? x_f ((x_3 x_3a) ...))]
  [(bound? x_f ())
   #f])

;;tests

;if 
(test--> rc-red (term ((if #t 3 5) () () halt)) (term (3 () () halt)))
(test--> rc-red (term ((if #f 4 5) () () halt)) (term (5 () () halt)))
(test--> rc-red (term ((if (if #t #f #t) 4 5) () () halt))
          (term ((if #t #f #t) () () (k (if hole 4 5) () halt))))
;id lookup
(test--> rc-red (term (t ((t g123)) ((g123 #t)) halt))
          (term (#t ((t g123)) ((g123 #t)) halt)))

;let binding
(test--> rc-red (term ((let ((t 5)) t) () () halt)) '())



(test-results)