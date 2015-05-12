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
  (env x)
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
   
   ;plus
   (--> ((+ number ... ce e ...) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (+ number ... ce e ...) env kont)))
   (--> ((+ number_0 number_1 number_2 ...) env sto kont)
        (number_ans env sto kont)
        (where number_ans (sum (+ number_0 number_1 number_2 ...))))
         
         
   
   ;lambdas and procs - create closure
   (--> (func env sto kont)
        ((clo func env) env sto kont)
        func-create)
   
   ;id lookup
   (--> (x env sto kont)
        (ae_ans env sto kont)
        (side-condition (term (bound? x env sto)))
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
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto)) 
        (where kont_new (gen-kont (if ce e_t e_f) env kont))
        if-expr)   
   
   ;let            
   ;; handle case where bind exp needs to be evaluated
   (--> ((let x ce) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (let x e) env kont))
        let-expr)
   ;; handle new binding case
   (--> ((let x ae) env sto kont)
        (ae env sto_new kont)
        (side-condition (not (term (bound? x env sto))))
        (where x_new ,(gensym))
        (where sto_newenv (add-to-env x x_new env sto))
        (where sto_new (add-to-sto x_new ae sto_newenv))
        let-bind)
   ;; handle update binding case
   (--> ((let x ae) env sto kont)
        (ae env sto_new kont)
        (side-condition (term (bound? x env sto)))
        (where sto_new (update-sto x ae env sto))
        let-update)
   
   ;application --------
   ;unevaluated function position
   (--> ((app ce (e ...)) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (app ce (e ...)) env kont))
        app-func-expr)
   ;unevaluated args
   (--> ((app ae_f (ae_a ... ce e ...)) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (app ae_f (ae_a ... ce e ...)) env kont))
        app-arg-expr)
   ;unbound arguments
   (--> ((app (clo (lam (x_1 x_2 ...) e_body) env_c) (ae_1 ae_2 ...)) 
         env sto kont)
        ((app (clo (lam (x_2 ...) e_body) env_c) (ae_2 ...)) 
         env sto_new kont)
        (side-condition (= (length (term (x_1 x_2 ...))) (length (term (ae_1 ae_2 ...)))))
        (where x_new ,(gensym))
        (where sto_newenv (add-to-env x_1 x_new env_c sto))
        (where sto_new (add-to-sto x_new ae_1 sto_newenv))
        app-lam)
   ;all bound arguments
   (--> ((app (clo (lam () e_body) env_c) ()) env sto kont)
        (e_body env_c sto kont)
        app-lam-no-args)
   
   
   ;procedure application unbound arguments
   (--> ((app (clo (proc (x_1 x_2 ...) e_body) env_c) (ae_1 ae_2 ...)) 
         env sto kont)
        ((app (clo (proc (x_2 ...) e_body) env_c) (ae_2 ...)) 
         env sto_new kont)
        (side-condition (not (and (= (length (term (ae_1 ae_2 ...))) 1)
                                  (> (length (term (x_1 x_2 ...))) 1)
                                  (term (list? ae_1))))) ;condition for splatting
        (where x_new ,(gensym))
        (where sto_newenv (add-to-env x_1 x_new env_c sto))
        (where sto_new (add-to-sto x_new ae_1 sto_newenv))
        app-proc)
   
   ;all bound arguments
   (--> ((app (clo (proc () e_body) env_c) (ae ...)) env sto kont)
        (e_body env_c sto kont)
        app-proc-no-args)
   
   ;not enough args provided, bind to nil
   (--> ((app (clo (proc (x_1 x_2 ...) e_body) env_c) ())
              env sto kont)
        ((app (clo (proc (x_2 ...) e_body) env_c) ())
              env sto_new kont)
        (where x_new ,(gensym))
        (where sto_newenv (add-to-env x_1 x_new env_c sto))
        (where sto_new (add-to-sto x_new nil sto_newenv)))
        
         
   
   ;splat arguments
   (--> ((app (clo (proc (x_1 x_2 ...) e_body) env_c) ((e_1 e_2 ...)))
         env sto kont)
        ((app (clo (proc (x_1 x_2 ...) e_body) env_c) (e_1 e_2 ...))
         env sto kont)
        app-proc-splat)
   
   
   
   ;apply with block
   ;unevaluated function position
   (--> ((app-b ce (e_1 ...) e_2) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (app-b ce (e_1 ...) e_2) env kont))
        app-b-func-expr)
   ;unevaluated args + block
   (--> ((app-b ae_f (ae_a ... ce e_1 ...) e_2) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (app-b ae_f (ae_a ... ce e_1 ...) e_2) env kont))
        app-b-arg-expr)
   ;unevaluated block
   (--> ((app-b ae_f (ae_a ...) ce) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (app-b ae_f (ae_a ...) ce) env kont))
        app-b-b-expr)
   
   ;unbound arguments with block
   (--> ((app-b (clo (lam (x_1 x_2 ...) e_body) env_c) (ae_1 ae_2 ...) ae) 
         env sto kont)
        ((app-b (clo (lam (x_2 ...) e_body) env_c) (ae_2 ...) ae) 
         env sto_new kont)
        (side-condition (= (length (term (x_1 x_2 ...))) (length (term (ae_1 ae_2 ...)))))
        (where x_new ,(gensym))
        (where sto_newenv (add-to-env x_1 x_new env_c sto))
        (where sto_new (add-to-sto x_new ae_1 sto_newenv))
        app-b-lam)
   
   ;all bound arguments with block
   (--> ((app-b (clo (lam () e_body) env_c) () ae)
         env sto kont)
        (e_body env_c sto_new (k-ret kont))
        (where x_new ,(gensym))
        (where sto_newenv (add-to-env blk x_new env_c sto))
        (where sto_new (add-to-sto x_new ae sto_newenv))
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
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (ret ce) env kont)))
   ;yield
   ;evaluate arguments to yield
   (--> ((yield (ae ... ce e ...)) env sto kont)
        (ce env_new sto_new kont_new)
        (where env_new ,(gensym))
        (where sto_new (copy-env env env_new sto))
        (where kont_new (gen-kont (yield (ae ... ce e ...)) env kont))
        yield-exprs)
   ;apply block to evaulated arguments
   (--> ((yield (ae_1 ae_2 ...)) env sto kont)
        ((app blk (ae_1 ae_2 ...)) env sto kont))))

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
   (k (app-b ae_f (ae_a ...) hole) env kont)]
  ;add
  [(gen-kont (+ number ... ce e ...) env kont)
   (k (+ number ... hole e ...) env kont)])
  

;lookup in store
(define-metafunction ruby-core
  sto-lookup : x sto -> ae
  [(sto-lookup x_s ((x_1 ae_1) (x_2 ae_2) ...))
   ,(if (equal? (term x_s) (term x_1))
        (term ae_1)
        (term (sto-lookup x_s ((x_2 ae_2) ...))))]
  [(sto-lookup x_s ())
   ((HERE x_s))])

(test-equal (term (sto-lookup x123 ((x123 5))))
            (term 5))
(test-equal (term (sto-lookup g123 ((x123 5) (g123 4))))
            (term 4))
(test-equal (term (sto-lookup g123 ((x123 5) (g123 4) (g446 7))))
            (term 4))

;adds a given ae bound to x to the store
(define-metafunction ruby-core
  add-to-sto : x ae sto -> sto
[(add-to-sto x ae ((x_1 ae_1) ...))
 ((x ae) (x_1 ae_1) ...)])


;updates the value of x in the store
;looks up x's loc in the env, then 
;overwrites the original by adding the old loc with the new ae
;to the store
(define-metafunction ruby-core
  update-sto : x ae env sto -> sto
  [(update-sto x ae env sto)
   (add-to-sto (env-lookup x env sto) ae sto)])


;looks up x in the given env
(define-metafunction ruby-core
  env-lookup-helper : x ae -> x
  [(env-lookup-helper x_s ((x_1 x_2) (x_3 x_4) ...))
   ,(if (equal? (term x_s) (term x_1))
        (term x_2)
        (term (env-lookup-helper x_s ((x_3 x_4) ...))))])

(test-equal (term (env-lookup-helper x123 ((x123 g123))))
            (term g123))
(test-equal (term (env-lookup-helper x123 ((id456 loc123) 
                                           (id567 loc123) 
                                           (x123 loc1) 
                                           (x12 loc2))))
            (term loc1))


;retrieves the env and then
;looks up x in the env
(define-metafunction ruby-core
  env-lookup : x env sto -> x
  [(env-lookup x env sto)
   (env-lookup-helper x (sto-lookup env sto))])

(test-equal (term (env-lookup x123 env1 ((env1 ((x123 g123))))))
            (term g123))
(test-equal (term (env-lookup x123 env1 ((env2 ()) 
                                         (env1 ((loc456 x1) 
                                                (x123 g123)
                                                (loc786 x2))))))
            (term g123))
(test-equal (term (env-lookup x123 env1 ((env2 ((loc123 x1)
                                                (loc456 x2))) 
                                         (env1 ((loc456 x1) 
                                                (x123 g123)
                                                (loc786 x2)))
                                         (env3 ((loc789 x2)
                                                (loc578 x4))))))
            (term g123))


;copy env
;copies env into location x in the store, 
;returns the updated store
(define-metafunction ruby-core
  copy-env : env x sto -> sto
  [(copy-env env_old x_new ((x_1 ae_1) ...))
   ((x_new (sto-lookup env_old ((x_1 ae_1) ...))) (x_1 ae_1) ...)])

(test-equal (term (copy-env oldenv newenv ((x123 5) (y456 6) (oldenv ((x123 x456))))))
            (term ((newenv ((x123 x456))) (x123 5) (y456 6) (oldenv ((x123 x456))))))
(test-equal (term (copy-env oldenv newenv ((x123 5) (y456 6) (oldenv ()))))
            (term ((newenv ()) (x123 5) (y456 6) (oldenv ()))))

;should take new id, new loc, and add it to the list of lists
;that represents an environment
(define-metafunction ruby-core
  add-to-env-list : x x ae -> ae
  [(add-to-env-list x_idnew x_locnew ((x_id x_loc) ...))
   ((x_idnew x_locnew) (x_id x_loc) ...)])

(test-equal (term (add-to-env-list x123 x123 ()))
            (term ((x123 x123))))
(test-equal (term (add-to-env-list x123 x123 ((x123 x123))))
            (term ((x123 x123) (x123 x123))))
(test-equal (term (add-to-env-list x456 x123 ((x789 x876))))
            (term ((x456 x123) (x789 x876))))


;add-to-env 
;retrieves environment from store, adds id and location
;adds updated environment to store
(define-metafunction ruby-core
  add-to-env : x x env sto -> sto
  [(add-to-env x_newid x_newloc env sto)
   (add-to-sto env (add-to-env-list x_newid x_newloc (sto-lookup env sto)) sto)])


(test-equal (term (add-to-env xid xloc en1 ((en1 ()))))
            (term ((en1 ((xid xloc))) (en1 ()))))
(test-equal (term (add-to-env xid xloc en1 ((en1 ((xold xold2))))))
            (term ((en1 ((xid xloc) (xold xold2))) (en1 ((xold xold2))))))

;retrieves the current environment
;searches that environment for x to get loc
;searches the store for the loc of x
(define-metafunction ruby-core
  lookup : x env sto -> ae
  [(lookup x_s env sto)
   (sto-lookup (env-lookup x_s env sto) sto)])

(test-equal (term (lookup id env1 ((loc123 1)
                                   (loc456 2)
                                   (env2 ((x2 loc123)
                                          (x3 loc456)))
                                   (env1 ((x456 loc1)
                                          (id loc)
                                          (y45 loc2)))
                                   (loc (123))
                                   (loc789 "hi")
                                   )))
            (term (123)))
(test-equal (term (lookup id env2 ((loc123 1)
                                   (loc458 2)
                                   (env2 ((x2 loc123)
                                          (id loc456)))
                                   (env1 ((x456 loc1)
                                          (id loc)
                                          (y45 loc2)))
                                   (loc (123))
                                   (loc456 "hey")
                                   (loc789 "hi")
                                   )))
            (term "hey"))





;searches the retrieved environment list
(define-metafunction ruby-core
  bound-helper : x ae -> boolean
  [(bound-helper x_f ((x_f x_fa) (x_2 x_2a) ...))
   #t]
  [(bound-helper x_f ((x_2 x_2a) (x_3 x_3a) ...))
   (bound-helper x_f ((x_3 x_3a) ...))]
  [(bound-helper x_f ())
   #f])

(define-metafunction ruby-core
  bound? : x env sto -> boolean
  [(bound? x env sto)
   (bound-helper x (sto-lookup env sto))])

(test-equal (term (bound? id env1 ((loc123 1)
                                   (loc458 2)
                                   (env2 ((x2 loc123)
                                          (id loc456)))
                                   (env1 ((x456 loc1)
                                          (id loc)
                                          (y45 loc2)))
                                   (loc (123))
                                   (loc456 "hey")
                                   (loc789 "hi"))))
            (term #t))
(test-equal (term (bound? id1 env1 ((loc123 1)
                                   (loc458 2)
                                   (env2 ((x2 loc123)
                                          (id loc456)))
                                   (env1 ((x456 loc1)
                                          (id loc)
                                          (y45 loc2)))
                                   (loc (123))
                                   (loc456 "hey")
                                   (loc789 "hi"))))
            (term #f))
(test-equal (term (bound? id1 env2 ((loc123 1)
                                   (loc458 2)
                                   (env2 ((x2 loc123)
                                          (id loc456)))
                                   (env1 ((x456 loc1)
                                          (id loc)
                                          (y45 loc2)))
                                   (loc (123))
                                   (loc456 "hey")
                                   (loc789 "hi"))))
            (term #f))

                                   


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

;summing metafunction
(define-metafunction ruby-core
  sum : ce -> number
  [(sum (+ number_0 number_1 number_2 ...))
   ,(+ (term number_0) (term (sum (+ number_1 number_2 ...))))]
  [(sum (+ number_0))
   number_0])



;;testing functions

;short-hand to run rr once
(define (rr x) (apply-reduction-relation rc-red x))
;;short-hand to extract answer
(define (re x) 
  (let ([final-configs (apply-reduction-relation* rc-red x)])
    (if (= (length final-configs) 1)
        (term (OF ,(first final-configs)))
        (raise "multiple transitions"))))

;;test cases
;atomic expressions
(test-equal (re (term (5 env1 () (k (do hole 5) env2 halt))))
         5)
(test-equal (re (term ("fg" env1 () (k (do hole 5) env2 halt))))
         5)
(test-equal (re (term (#t env1 () (k (if hole 4 5) env2 halt))))
         4)


;if 
(test-equal (re (term ((if #t 3 5) env1 () halt))) 
            3)
(test-equal (re (term ((if #f 4 5) env1 ((env1 ())) halt))) 
            5)
(test-equal (re (term ((if (if #t #f #t) 4 5) env1 ((env1 ())) halt)))
            5)

;id lookup
(test-equal (re (term (t env1 ((g123 #t) (env1 ((t g123)))) halt)))
            #t)
(test-equal (re (term (t env1 ((g123 #t) 
                               (g124 0) 
                               (env1 ((x g124) (t g123)))) 
                         halt)))
            #t)


;new binding
(test-equal (re (term ((do (let x 5) x) env1 ((env1 ())) halt)))
            (term 5))
(test-equal (re (term ((do (let x 6) (let x (+ x 1)) x) 
                       env1 
                       ((env1 ())) 
                       halt)))
            (term 7))
(test-equal (re (term ((do (if #t (let x 5) 4) x) env1 ((env1 ()))
                                                  halt)))
                (term 5))
(test-equal (re (term ((do (if #t (if #t (let x 5) 3) 4) x) env1 ((env1 ()))
                                                  halt)))
                (term 5))
(test-equal (re (term ((do (let x 5) x) env1 ((env1 ())) halt)))
                      (term 5))
            
      

;update binding
(test-equal (re (term ((do (let t 5) t) env1 ((env1 ((t g123))) (g123 3)) halt)))
         5)
(test-equal (re (term ((do (let t 5) (let t 6)) env1 ((env1 ((t g123))) (g123 0)) halt)))
         6)

;app
(test-equal (re (term ((app (lam (x) x) (5)) env1 ((env1 ())) halt)))
    (term 5))

(test-equal (re (term ((do (let y 5) (let x (lam (y) y))
                           (do (app x (7)))) env1 ((env1 ())) halt)))
                  (term 7))

(test-equal (re (term ((app (lam () 5) ()) env1 ((env1 ())) halt)))
         (term 5))

(test-equal (re (term ((app (lam (x y) y) (4 5)) env1 ((env1 ())) halt)))
    (term 5))


;app with block and yield
(test-equal (re (term ((app-b (lam (x) x) (5) (lam (x) x)) env1 ((env1 ())) halt)))
                (term 5))
(test-equal (re (term ((app-b 
                       (lam (x) (do (let x 5) (yield (5)) (let x 6)))
                       (4)
                       (lam (x) (ret x))) env1 ((env1 ())) halt)))
               (term 5))
(test-equal (re (term ((app-b 
                       (lam (x) (do (let x 5) (yield (x)) (let x 6)))
                       (4)
                       (lam (x) (ret x))) env1 ((env1 ())) halt)))
               (term 5))
(test-equal (re (term ((app (lam (x) 
                                   (app-b (lam (x) (yield (x))) (x) (proc (x) x)))
                              (0)) env1 ((env1 ())) halt)))
                  (term 0))             
(test-equal (re (term 
                 ((app-b (lam (x) (do (let x 5) (yield (x)))) 
                         (3) 
                         (proc (x) x)) env1 ((env1 ())) halt)))
                  (term 5))                 
(test-equal (re (term ((do (let x (lam (x) (do (let x 8) (let x 7) (yield (x)))))
                           (app-b x (0) (proc (x) (ret x)))) env1 ((env1 ())) halt)))
                  (term 7))
              

           
                                                 
;do
(test-equal (re (term ((do 5) env1 ((env1 ())) halt)))
            (term 5))
(test-equal (re (term ((do 5 (if #t 3 4)) env1 ((env1 ())) halt)))
            (term 3))
(test-equal (re (term ((do (if #t 3 4) 5) env1 ((env1 ())) halt)))
            (term 5))
(test-equal (re (term ((do 5 5) env1 ((env1 ())) halt)))
                (term 5))
(test-equal (re (term ((app (do (let x 5) (let y 8) (let x 7)
                          (let y 4) (let x 5) (lam (x) y)) (4))
                        env1 ((env1 ()))
                        halt)))
                  (term 4))

;splat arguments
(test-equal (re (term ((app (proc (x y) x) ((5 4))) env1 ((env1 ())) halt)))
         (term 5))
              
(test-equal (re  (term ((app (clo (proc (x y) x) env1) ((5 4 3))) env1 ((env1 ())) halt)))
            (term 5))
                 
(test-equal (re (term ((app (clo (proc () 5) env1) ((5 4 3))) env1 ((env1 ())) halt)))
                 (term 5))
(test-equal (re (term ((app (clo (proc (x y) x) env1) ((5 4))) env1 ((env1 ())) halt)))
                 (term 5))
(test-equal (re (term ((app (clo (proc (x y) x) env1) ((5))) env1 ((env1 ())) halt)))
                 (term 5))

;bind extra args to nil in proc
(test-equal (re (term ((app (proc (x y) y) (5)) env1 ((env1 ())) halt)))
                  (term nil))
                  
(test-equal (re (term ((app (proc (x y z) z) (5)) env1 ((env1 ())) halt)))
                  (term nil))
                  
(test-equal (re (term ((app (proc () 4) (5)) env1 ((env1 ())) halt)))
                  (term 4))
                  

;plus
(test-equal (re (term ((+ 5 4) env1 ((env1 ())) halt)))
         (term 9))
(test-equal (re (term ((+ (+ 5 4) (+ 5 3)) env1 ((env1 ())) halt)))
         (term 17))


(test-results)
(test)