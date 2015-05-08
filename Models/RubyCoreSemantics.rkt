#lang racket
(require redex)
(require test-engine/racket-tests)

(define-language ruby-core
  ;atomic expressions
  (ae number
      string 
      boolean
      empty
      (list e ... empty)
      (clo func env))
  (ce (do e ...)
      (+ e ...)
      (if e e e)
      ;apply
      (app e e ...)
      ;apply with block
      (app-b e e)
      (ret e)
      (let x e)
      func
      x)
  (func (lam (x ...) e)
        (proc (x ...) e))
  ;contexts         
  (E (do hole e ...)
      (+ hole e ...)
      (if hole e e)
      ;apply
      (app ae ... hole e ...)
      ;apply with block
      (app-b hole e)
      (ret hole)
      (let x hole))
  ;all expressions
  (e ce
     ae) 
  ;configuration definitions
  (sto ((x ae) ...))
  (env ((x x) ...))
  (kont (k-do E env kont) ;keep environment if do
        (k-ret kont) ;originating from a block call
        (k E env kont) ;normal control point 
        halt) ;base case
  (CF (e env sto kont))
  (x variable-not-otherwise-mentioned))  


(define rc-red
  (reduction-relation
   ruby-core #:domain CF
   ;final configuration
   ;(--> (ae env sto halt)
   
   ;atomic expression - call current continuation
   (--> (ae env sto (k E env_k kont))
        ((in-hole E ae) env_k sto kont)
        cont)
   (--> (ae env sto (k-do E env_k kont))
        ((in-hole E ae) env sto kont)
        cont-do)
   (--> (ae env sto (k-ret kont)) ;; if ret wasn't called, ignore
        (ae env sto kont)
        cont-ret)
   
   ;lambdas and procs - create closure
   (--> (func env sto kont)
        ((clo func env) env sto kont)
        func-create)
   
   ;id lookup
   (--> (x env sto kont)
        (ae_ans env sto kont)
        (side-condition (term (bound? x env)))
        (where ae_ans (lookup x env sto))
        id-lookup)
   
   ;if 
   (--> ((if #t e_t e_f) env sto kont)
        (e_t env sto kont)
        if-t)   
   (--> ((if #f e_t e_f) env sto kont)
        (e_f env sto kont)
        if-f)
   (--> ((if ce e_t e_f) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (if ce e_t e_f) env kont))
        if-expr)   
   
   ;let            
   ;; handle case where bind exp needs to be evaluated
   (--> ((let x ce) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (let x e) env kont))
        let-expr)
   ;; handle new binding case
   (--> ((let x ae) ((x_1 x_2) ...) ((x_3 ae_1) ...) kont)
        (ae ((x x_new) (x_1 x_2) ...) ((x_new ae) (x_3 ae_1) ...) kont)
        (side-condition (not (term (bound? x ((x_1 x_2) ...)))))
        (where x_new ,(gensym))
        let-bind)
   ;; handle update binding case
   (--> ((let x ae) env sto kont)
        (ae env sto_new kont)
        (side-condition (term (bound? x env)))
        (where sto_new (update-sto x ae env sto))
        let-update)
   
   ;app
   (--> ((app ae ... ce e ...) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (app ae ... ce e ...) env kont))
        app-exprs)
   (--> ((app (clo (lam (x_1 x_2 ...) e_body) 
                   ((x_id x_loc1) ...)) ae_1 ae_2 ...) 
         env
         ((x_loc2 ae_v) ...) kont)
        ((app (clo (lam (x_2 ...) e_body) 
                   ((x_1 x_new) (x_id x_loc1) ...)) ae_2 ...) 
         env
         ((x_new ae_1) (x_loc2 ae_v) ...) kont)
        (side-condition (= (length (term (x_1 x_2 ...))) (length (term (ae_1 ae_2 ...)))))
        (where x_new ,(gensym))
        app-lam)
   (--> ((app (clo (lam () e_body) env_c)) env sto kont)
        (e_body env_c sto kont)
        app-lam-no-args)
   
                                               
   
   ;do
   (--> ((do ce e_1 ...) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (do ce e_1 ...) env kont)))
   (--> ((do ae e_1 e_2 ...) env sto kont)
        ((do e_1 e_2 ...) env sto kont))
   (--> ((do ae) env sto kont)
        (ae env sto kont))
   
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

;;------------------ metafunctions -----------------
(define-metafunction ruby-core
  gen-kont : e env kont -> kont  
  [(gen-kont (app ae ... ce e ...) env kont)
   (k (app ae ... hole e ...) env kont)]
  [(gen-kont (do e_1 e_2 ...) env kont)
   (k-do (do hole e_2 ...) env kont)] ;remove first expression
  [(gen-kont (if e e_t e_f) env kont)
   (k (if hole e_t e_f) env kont)]
  [(gen-kont (ret ce) env kont)
   (k (ret hole) env kont)]
  [(gen-kont (let x e) env kont)
   (k (let x hole) env kont)])

;env can't be empty if this is called
(define-metafunction ruby-core
  env-lookup : x env -> x
  [(env-lookup x_s ((x_1 x_2) (x_3 x_4) ...))
   ,(if (equal? (term x_s) (term x_1))
        (term x_2)
        (term (env-lookup (term x_s) (term ((x_3 x_4) ...)))))])

;sto can't be empty due to side-cond
(define-metafunction ruby-core
  sto-lookup : x sto -> ae
  [(sto-lookup x_s ((x_1 ae_1) (x_2 ae_2) ...))
   ,(if (equal? (term x_s) (term x_1))
        (term ae_1)
        (term (sto-lookup x_s ((x_2 ae_2) ...))))])

;env can't be empty due to side-cond
(define-metafunction ruby-core
  lookup : x env sto -> ae
  [(lookup x_s env sto )
   (sto-lookup (env-lookup x_s env) sto)])

;store can't be empty due to side-cond
(define-metafunction ruby-core
  update-sto : x ae env sto -> sto
  [(update-sto x ae env sto)
   (update-helper (env-lookup x env) ae sto)])

;store can't be empty if this is called due to a side-cond
(define-metafunction ruby-core
  update-helper : x ae sto -> sto
[(update-helper x ae ((x ae_1) (x_2 ae_2) ...))
 ((x ae) (x_2 ae_2) ...)]
[(update-helper x ae ((x_1 ae_1) (x_2 ae_2) ...))
 (update-helper x ae ((x_2 ae_2) ...))])

(define-metafunction ruby-core
  bound? : x env -> boolean
  [(bound? x_f ((x_f x_fa) (x_2 x_2a) ...))
   #t]
  [(bound? x_f ((x_2 x_2a) (x_3 x_3a) ...))
   (bound? x_f ((x_3 x_3a) ...))]
  [(bound? x_f ())
   #f])

;output function
(define-metafunction ruby-core
  OF : CF -> ae
  [(OF (ae env sto kont)) ae])



;;testing functions

;short-hand to run rr
(define (rr x) (apply-reduction-relation rc-red x))
;;short-hand to test rr
(define (tc x y) (let ([final-configs (apply-reduction-relation* rc-red x)])
  (and (= (length final-configs) 1) 
          (equal? (term (OF ,(first final-configs))) y))))

;;test cases
;atomic expressions
(test--> rc-red (term (5 () () (k (do hole 5) () halt)))
         (term ((do 5 5) () () halt)))
(test--> rc-red (term ("fg" () () (k (do hole 5) () halt)))
         (term ((do "fg" 5) () () halt)))
(test--> rc-red (term ("fg" () () (k (if hole 4 5) () halt)))
         (term ((if "fg" 4 5) () () halt)))


;if 
(test--> rc-red (term ((if #t 3 5) () () halt)) (term (3 () () halt)))
(test--> rc-red (term ((if #f 4 5) () () halt)) (term (5 () () halt)))
(test--> rc-red (term ((if (if #t #f #t) 4 5) () () halt))
          (term ((if #t #f #t) () () (k (if hole 4 5) () halt))))
;id lookup
(test--> rc-red (term (t ((t g123)) ((g123 #t)) halt))
          (term (#t ((t g123)) ((g123 #t)) halt)))

;new binding
(check-expect (tc (term ((do (let x 5) x) () () halt)) (term 5))
              true)


;update binding
(test--> rc-red (term ((let t 5) ((t g123)) ((g123 3)) halt))
         (term (5 ((t g123)) ((g123 5)) halt)))

;app
(check-expect (tc (term ((app (lam (x) x) 5) () () halt)) (term 5))
              #t)
(check-expect (tc (term ((do (let y 5) (let x (lam (y) y))
                           (do (app x 7))) () () halt))
                  (term 7))
              #t)

(test-->> rc-red (term ((app (lam () 5)) () () halt))
         (term (5 () () halt)))

(check-expect (tc (term ((app (lam (x y) y) 4 5) () () halt))
    (term 5))
              #t)

                     


;do
(test--> rc-red (term ((do 5) () () halt)) (term (5 () () halt)))
(test--> rc-red (term ((do 5 (if #t 3 4)) () () halt))
         (term ((do (if #t 3 4)) () () halt)))
(test-->> rc-red (term ((do (if #t 3 4) 5) () () halt))
         (term (5 () () halt)))
(test--> rc-red (term ((do 5 5) () () halt))
         (term ((do 5) () () halt)))



(test-results)
(test)