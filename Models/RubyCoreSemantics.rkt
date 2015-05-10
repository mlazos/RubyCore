#lang racket
(require redex)
(require test-engine/racket-tests)

(define-language ruby-core
  ;atomic expressions
  (ae number
      string 
      boolean
      empty
      (e ...)
      (clo func env)
      nil)
  (ce (do e ...)
      (+ e ...)
      (if e e e)
      ;apply
      (app e (e ...))
      ;apply with block
      (yield (e ...))
      (app-b e (e ...) e)
      (ret e)
      (let x e)
      func
      x)
  (func (lam (x ...) e)
        (proc (x ...) e))
  ;contexts         
  (E  (do hole e ...)
      (+ number ... hole e ...)
      (if hole e e)
      ;apply
      (app hole (e ...))
      (app ae (e ... hole e ...))
      ;apply with block
      (app-b hole (e ...) e)
      (app-b ae (e ... hole ...) e)
      (app-b ae (ae ...) hole)
      (yield (e ... hole e ...))
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
  (x variable-not-otherwise-mentioned blk))  


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
   
   ;application --------
   ;unevaluated function position
   (--> ((app ce (e ...)) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (app ce (e ...)) env kont))
        app-func-expr)
   ;unevaluated args
   (--> ((app ae_f (ae_a ... ce e ...)) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (app ae_f (ae_a ... ce e ...)) env kont))
        app-arg-expr)
   ;unbound arguments
   (--> ((app (clo (lam (x_1 x_2 ...) e_body) ((x_id x_loc1) ...)) 
              (ae_1 ae_2 ...)) 
         env
         ((x_loc2 ae_v) ...) kont)
        ((app (clo (lam (x_2 ...) e_body) 
                   ((x_1 x_new) (x_id x_loc1) ...)) 
              (ae_2 ...)) 
         env
         ((x_new ae_1) (x_loc2 ae_v) ...) kont)
        (side-condition (= (length (term (x_1 x_2 ...))) (length (term (ae_1 ae_2 ...)))))
        (where x_new ,(gensym))
        app-lam)
   ;all bound arguments
   (--> ((app (clo (lam () e_body) env_c) ()) env sto kont)
        (e_body env_c sto kont)
        app-lam-no-args)
   
   
   ;procedure application unbound arguments
   (--> ((app (clo (proc (x_1 x_2 ...) e_body) ((x_id x_loc1) ...)) 
              (ae_1 ae_2 ...)) 
         env
         ((x_loc2 ae_v) ...) kont)
        ((app (clo (proc (x_2 ...) e_body) 
                   ((x_1 x_new) (x_id x_loc1) ...)) 
              (ae_2 ...)) 
         env
         ((x_new ae_1) (x_loc2 ae_v) ...) kont)
        (side-condition (not (and (= (length (term (ae_1 ae_2 ...))) 1)
                                  (> (length (term (x_1 x_2 ...))) 1)
                                  (term (list? ae_1))))) ;condition for splatting
        (where x_new ,(gensym))
        app-proc)
   
   ;all bound arguments
   (--> ((app (clo (proc () e_body) env_c) (ae ...)) env sto kont)
        (e_body env_c sto kont)
        app-proc-no-args)
   
   ;not enough args provided, bind to nil
   (--> ((app (clo (proc (x_1 x_2 ...) e_body) ((x_id x_loc) ...)) ())
              env ((x_locs ae_1) ...) kont)
        ((app (clo (proc (x_2 ...) e_body) ((x_1 x_new) (x_id x_loc) ...)) ())
              env ((x_new nil) (x_locs ae_1) ...) kont)
        (where x_new ,(gensym)))
        
         
   
   ;splat arguments
   (--> ((app (clo (proc (x_1 x_2 x_3 ...) e_body) env) ((e_1 ...)))
         env sto kont)
        ((app (clo (proc (x_1 x_2 x_3 ...) e_body) env) (e_1 ...))
         env sto kont)
        app-proc-splat)
   
   
   
   ;apply with block
   ;unevaluated function position
   (--> ((app-b ce (e_1 ...) e_2) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (app-b ce (e_1 ...) e_2) env kont))
        app-b-func-expr)
   ;unevaluated args + block
   (--> ((app-b ae_f (ae_a ... ce e_1 ...) e_2) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (app-b ae_f (ae_a ... ce e_1 ...) e_2) env kont))
        app-b-arg-expr)
   ;unevaluated block
   (--> ((app-b ae_f (ae_a ...) ce) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (app-b ae_f (ae_a ...) ce) env kont))
        app-b-b-expr)
   
   ;unbound arguments with block
   (--> ((app-b (clo (lam (x_1 x_2 ...) e_body) ((x_id x_loc1) ...)) 
              (ae_1 ae_2 ...)
              ae) 
         env
         ((x_loc2 ae_v) ...) kont)
        ((app-b (clo (lam (x_2 ...) e_body) 
                   ((x_1 x_new) (x_id x_loc1) ...)) 
              (ae_2 ...)
              ae) 
         env
         ((x_new ae_1) (x_loc2 ae_v) ...) kont)
        (side-condition (= (length (term (x_1 x_2 ...))) (length (term (ae_1 ae_2 ...)))))
        (where x_new ,(gensym))
        app-b-lam)
   
   ;all bound arguments with block
   (--> ((app-b (clo (lam () e_body) ((x_id x_loc) ...)) () ae)
         env ((x_loc2 ae_v) ...) kont)
        (e_body ((blk x_new) (x_id x_loc) ...)
                ((x_new ae) (x_loc2 ae_v) ...) 
                (k-ret kont))
        (where x_new ,(gensym))
        app-b-lam-no-args)
   
   
                                   
   ;do
   (--> ((do ce e_1 ...) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (do ce e_1 ...) env kont)))
   (--> ((do ae e_1 e_2 ...) env sto kont)
        ((do e_1 e_2 ...) env sto kont))
   (--> ((do ae) env sto kont)
        (ae env sto kont))
   
   ;return ------------
   ;arrived at correct kont
   (--> ((ret ae) env sto (k-ret kont))
        (ae env sto kont))
   ;pop frame
   (--> ((ret ae) env sto (k E env_k kont))
        ((ret ae) env sto kont))
   ;pop frame
   (--> ((ret ae) env sto (k-do E env_k kont))
        ((ret ae) env sto kont))
   ;eval return value
   (--> ((ret ce) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (ret ce) env kont)))
   
   ;yield
   ;evaluate arguments to yield
   (--> ((yield (ae ... ce e ...)) env sto kont)
        (ce env sto kont_new)
        (where kont_new (gen-kont (yield (ae ... ce e ...)) env kont))
        yield-exprs)
   ;apply block to evaulated arguments
   (--> ((yield (ae ...)) env sto kont)
        ((app blk (ae ...)) env sto kont))
   ))

;;------------------ metafunctions -----------------
(define-metafunction ruby-core
  gen-kont : e env kont -> kont 
  ;app
  [(gen-kont (app ce (e ...)) env kont)
   (k (app hole (e ...)) env kont)]
  [(gen-kont (app ae_f (ae ... ce e ...)) env kont)
   (k (app ae_f (ae ... hole e ...)) env kont)]
  ;do
  [(gen-kont (do ce e_1 ...) env kont)
   (k-do (do hole e_1 ...) env kont)] ;remove first expression
  ;if
  [(gen-kont (if ce e_t e_f) env kont)
   (k (if hole e_t e_f) env kont)]
  ;ret
  [(gen-kont (ret ce) env kont)
   (k (ret hole) env kont)]
  ;let
  [(gen-kont (let x ce) env kont)
   (k (let x hole) env kont)]
  ;yield
  [(gen-kont (yield (ae ... ce e ...)) env kont)
   (k (yield (ae ... hole e ...)) env kont)]
  ;ret
  [(gen-kont (ret ce) env kont)
   (k (ret hole) env kont)]
  ;app-b
  [(gen-kont (app-b ce (e_1 ...) e_2) env kont)
   (k (app-b hole (e_1 ...) e_2) env kont)]
  [(gen-kont (app-b ae_f (ae_1 ... ce e_1 ...) e_2) env kont)
   (k (app-b ae_f (ae_1 ... hole e_1 ...) e_2) env kont)]
  [(gen-kont (app-b ae_f (ae_a ...) ce) env kont)
   (k (app-b ae_f (ae_a ...) hole) env kont)])
  


;env can't be empty if this is called
(define-metafunction ruby-core
  env-lookup : x env -> x
  [(env-lookup x_s ((x_1 x_2) (x_3 x_4) ...))
   ,(if (equal? (term x_s) (term x_1))
        (term x_2)
        (term (env-lookup x_s ((x_3 x_4) ...))))])

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
[(update-helper x ae ((x_1 ae_1) ...))
 ((x ae) (x_1 ae_1) ...)])

(define-metafunction ruby-core
  bound? : x env -> boolean
  [(bound? x_f ((x_f x_fa) (x_2 x_2a) ...))
   #t]
  [(bound? x_f ((x_2 x_2a) (x_3 x_3a) ...))
   (bound? x_f ((x_3 x_3a) ...))]
  [(bound? x_f ())
   #f])

;list predicate
(define-metafunction ruby-core
  list? : ae -> boolean
  [(list? (e ...))
   #t]
  [(list? ae)
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
(test--> rc-red (term ((lam (x) x) ((t g123)) () halt))
         (term ((clo (lam (x) x) ((t g123))) ((t g123)) () halt)))


;if 
(test--> rc-red (term ((if #t 3 5) () () halt)) (term (3 () () halt)))
(test--> rc-red (term ((if #f 4 5) () () halt)) (term (5 () () halt)))
(test--> rc-red (term ((if (if #t #f #t) 4 5) () () halt))
          (term ((if #t #f #t) () () (k (if hole 4 5) () halt))))

;id lookup
(test--> rc-red (term (t ((t g123)) ((g123 #t)) halt))
          (term (#t ((t g123)) ((g123 #t)) halt)))
(test--> rc-red (term (t ((x g124) (t g123)) ((g123 #t) (g124 0)) halt))
         (term (#t ((x g124) (t g123)) ((g123 #t) (g124 0)) halt)))


;new binding
(check-expect (tc (term ((do (let x 5) x) () () halt)) (term 5))
              true)


;update binding
(test--> rc-red (term ((let t 5) ((t g123)) ((g123 3)) halt))
         (term (5 ((t g123)) ((g123 5) (g123 3)) halt)))
(test-->> rc-red (term ((do (let t 5) (let t 6)) ((t g123)) ((g123 0)) halt))
          (term (6 ((t g123)) ((g123 6) (g123 5) (g123 0)) halt)))

;app
(check-expect (tc (term ((app (lam (x) x) (5)) () () halt)) (term 5))
              #t)
(check-expect (tc (term ((do (let y 5) (let x (lam (y) y))
                           (do (app x (7)))) () () halt))
                  (term 7))
              #t)

(test-->> rc-red (term ((app (lam () 5) ()) () () halt))
         (term (5 () () halt)))

(check-expect (tc (term ((app (lam (x y) y) (4 5)) () () halt))
    (term 5))
              #t)

;app with block and yield
(check-expect (tc 
               (term ((app-b 
                       (lam (x) (do (let x 5) (yield (5)) (let x 6)))
                       (4)
                       (lam (x) (ret x))) () () halt))
               (term 5))
              #t)
(check-expect (tc 
               (term ((app-b 
                       (lam (x) (do (let x 5) (yield (x)) (let x 6)))
                       (4)
                       (lam (x) (ret x))) () () halt))
               (term 5))
              #t)
(check-expect (tc (term ((app (lam (x) 
                                   (app-b (lam (x) (yield (x))) (x) (proc (x) x)))
                              (0)) () () halt))
                  (term 0))
              #t)
(check-expect (tc (term ((app-b (lam (x) (do (let x 5) (yield (x)))) (3) (proc (x) x)) () () halt))
                  (term 5))
                  #t)
(check-expect (tc (term ((do (let x (lam (x) (do (let x 8) (let x 7) (yield (x)))))
                           (app-b x (0) (proc (x) (ret x)))) () () halt))
                  (term 7))
              #t)

              
                                                        
;do
(test--> rc-red (term ((do 5) () () halt)) (term (5 () () halt)))
(test--> rc-red (term ((do 5 (if #t 3 4)) () () halt))
         (term ((do (if #t 3 4)) () () halt)))
(test-->> rc-red (term ((do (if #t 3 4) 5) () () halt))
         (term (5 () () halt)))
(test--> rc-red (term ((do 5 5) () () halt))
         (term ((do 5) () () halt)))
(check-expect (tc (term ((app (do (let x 5) (let y 8) (let x 7)
                          (let y 4) (let x 5) (lam (x) y)) (4))
                        ()
                        ()
                        halt))
                  (term 4))
              #t)

;splat arguments
(check-expect (tc (term ((app (proc (x y) x) ((5 4))) () () halt))
         (term 5))
              #t)
(test--> rc-red (term ((app (clo (proc (x y) x) ()) ((5 4 3))) () () halt))
                 (term ((app (clo (proc (x y) x) ()) (5 4 3)) () () halt)))
(test--> rc-red (term ((app (clo (proc () 5) ()) ((5 4 3))) () () halt))
                 (term (5 () () halt)))
(test--> rc-red (term ((app (clo (proc (x y) x) ()) ((5 4))) () () halt))
                 (term ((app (clo (proc (x y) x) ()) (5 4)) () () halt)))
(test--> rc-red (term ((app (clo (proc (x y) x) ()) ((5))) () () halt))
                 (term ((app (clo (proc (x y) x) ()) (5)) () () halt)))

;bind extra args to nil in proc
(check-expect (tc (term ((app (proc (x y) y) (5)) () () halt))
                  (term nil))
                  #t)
(check-expect (tc (term ((app (proc (x y z) z) (5)) () () halt))
                  (term nil))
                  #t)
(check-expect (tc (term ((app (proc () 4) (5)) () () halt))
                  (term 4))
                  #t)



(test-results)
(test)