#lang racket
(require rosette)
(require rackunit)

;; ============================= Langauge Design =====================================
;
; e ::=                  Terms:
;   v                    Values
;   x                    Variables
;   (let x e e)          Let bindings
;   (lambda x T e)       Functions
;   (e x)                Application
;   (e : T)              Type-annotation

;
; v ::=                  Values:
;   num                  (... -2,-1,0,1,2 ...)
;   True | False         Boolean constants
;   (lambda x T e)       Abstraction value
;   add | sub            Primitive functions
;
; b ::=                  Atomic primitive type:
;   Int                  Integer
;   Bool                 Boolean
;
; T ::=                  Types:
;   b                    Atomic primitive type
;  (x : T -> T)          Dependent Funciton Type
;  (Refi b x p)          Refinement Type

; p, q::=                Predicate:
;  x                     variable
;  True | False          Boolean
;  Num
;  (< | <= | >= | >  p q)
;  (and p ...)
;  (or p ...)
;  (not q)
;  (if p then p else p)
;
; c ::=                  Constraints:
;   (forall x b p c)     Implication
;   (and c c)            Conjunction
;   p                    Predicate
;
; ctx ::=                Contexts:
;   '()                  empty context
;    (dict-ref ctx x T)  Term variable binding

;; ================================= Bidirectional Type Checking ===================================
(define (type-check v expected-type ctx)
  (match v
    ; CHK-LAM
    [`(lambda ,x ,T ,t)
     (match expected-type
       [`(,x_exp : ,T-in -> ,T-out)
        #:when (eq? x_exp x)
        (let ([T-term (type-check t T-out (dict-set ctx x T))])
          `(,x : ,T-in -> ,T-term))]
       [_ (error 'type-check "type mismatch: expected type: ~a, v: ~a" expected-type v)])]
    ; CHK-LET
    [`(let ,x1 ,e1 ,e2)
     (let ([T1 (type-infer e1 ctx)])
       (type-check e2 expected-type (dict-set ctx x1 T1)))]
    [`(,e : ,T)
     (let ([T-e (type-check e T ctx)])
       (if (subtype? T-e T)
           T
           (error 'type-check "type mismatch: expected ~a, got ~a" T T-e)))]
    [`(,t1 ,t2)
     (let* ([T1 (type-check t1 expected-type ctx)]
            [T2 (type-check t2 T1 ctx)])
       T2)]
    ; CHK-SYN
    [x
     (let ([actual-type (type-infer x ctx)])
       (if (subtype? actual-type expected-type)
           expected-type
           (error 'type-check "actual type: ~a is not a subtype of expected type: ~a" actual-type expected-type)))]
    ))

(define (type-infer e ctx)
  (match e
    [`(,e : ,T)    ; SYN-ANN
     (if (and (check-type-wellness T) (type-check e T ctx))
         T
         (error 'type-infer "~a can not ascribe with type ~a" e T))]
    [v             ; SYN-CON
     #:when (is-primitive-value? v)
     (prim v)]
    [`(lambda ,x ,T ,t)
     (let* ([_ (check-type-wellness T)]
            [T2 (type-infer t (dict-set ctx x T))])
       `(,x : ,T -> ,T2))]
    [`(,t1 ,t2)    ; (SYN-APP)
     (let ([T1 (type-infer t1 ctx)])
       (match T1
         [`(,x : ,T11 -> ,T12)
          (if (not (false? (type-check t2 T11 ctx)))
              (subst-type t2 x T12)
              (error 'type-infer "type infer error, SYN-APP fails type check"))]))]
    [`(let ,x ,e1 ,e2)
     (let ([T1 (type-infer e1 ctx)])
       (type-infer e2 (dict-set ctx x T1)))]
    [x              ; SYN-VAR
     (if (dict-has-key? ctx x)
         (dict-ref ctx x)
         (error 'type-infer "variable ~a not found in context" x))]))


;; ============================ Helper functions =============================
; value -> Boolean
; check if the given value is primitive value
(define (is-primitive-value? v)
  (match v
    ['True #t]
    ['False #t]
    [v #:when(number? v) #t]
    ['add #t]
    ['sub #t]
    [_ #f]))

(define (is-base-type? type)
  (match type
    ['Int #t]
    ['Bool #t]
    [_ #f]))

(define (is-refi-type? type)
  (match type
    [`(Refi ,b ,x ,p) (check-type-wellness type)]
    [_ #f]))

(define (prim v)
  (match v
    [v #:when (number? v) (let ([fresh 'x]) `(Refi Int ,fresh (= ,fresh ,v)))]
    ['True `(Refi Bool x True)]
    ['False `(Refi Bool x False)]
    ['sub `(x : Int -> (y : Int -> (Refi Int v (= v (- x y)))))]
    ['add `(x : Int -> (y : Int -> (Refi Int v (= v (+ x y)))))]
    [_ (error 'primitive-type "invalid primitive type: ~a" v)]))

(define (check-type-wellness type)
  (match type
    ['Int #t]
    ['Bool #t]
    [`(Refi ,b ,x ,p)
     (match b
       ['Int #t]
       ['Bool #t]
       [_ (error 'check-type-wellness "invalid type ~a" type)])]
    [_ #f]))

; check if T1 is a subtype of T2
(define (subtype? T1 T2)
  (match (cons T1 T2)
    ; a refinement type will be a subtype of its base type
    [`(,T1 . ,T2)
     #:when (and (is-refi-type? T1) (is-base-type? T2))
     (match T1 [`(Refi ,b ,x ,p) (eq? b T2)]
       [_ (error 'subtype? "Here")])]
    [`(Int . ,T2) (eq? T2 'Int)] ; Int is only a subtype of Int
    [`(Bool . ,T2) (eq? T2 'Bool)] ; Bool is only a subtype of Bool
    [`((,x1 : ,s1 -> ,t1) . (,x2 : ,s2 -> ,t2))
     ; SUB-FUN
     (and (subtype? s2 s1) (subtype? (subst-type x2 x1 t1) t2))]
    [`((Refi ,b1 ,x1 ,p1) . (Refi ,b2 ,x2 ,p2))
     ; SUB-BASE
     (if (eq? b1 b2)
         ;  Generate the VC and check the Constraints
         (check-constraint `(forall ,x1 ,b1 ,p1 ,(subst-pred x1 x2 p2)) '())
         #f)]
    [_ (error 'subtype? "invalid type ~a" (cons T1 T2))]))


;;  --------------- Substition 3.3.1 (Refinement Paper) ------------------
; substitude all instance of v2 with v1 in predicate
(define (subst-pred v1 v2 pred)
  (match pred
    ['True 'True]
    ['False 'False]
    [p #:when (eq? p v2) v1]
    [p #:when (or (number? p) (symbol? p)) p]
    [`(= ,p1 ,p2) `(= ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(<= ,p1 ,p2) `(<= ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(< ,p1 ,p2) `(< ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(> ,p1 ,p2) `(> ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(>= ,p1 ,p2) `(>= ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(not ,p1) `(not ,(subst-pred v1 v2 p1))]
    [`(and ,p ...) `(and ,@(map (lambda (p) (subst-pred v1 v2 p)) p))]
    [`(or ,p ...) `(or ,@(map (lambda (p) (subst-pred v1 v2 p)) p))]
    [`(if ,p1 ,p2 ,p3) `(if ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2) ,(subst-pred v1 v2 p3))]
    [`(+ ,p1 ,p2) `(+ ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [`(- ,p1 ,p2) `(- ,(subst-pred v1 v2 p1) ,(subst-pred v1 v2 p2))]
    [_ (error 'subst-pred "invalid predicate ~a" pred)]))

; all free occurrences of v2 are substituted with v1 in Type T.
(define (subst-type v1 v2 T)
  (match T
    [b #:when (is-base-type? b) b]
    [v #:when (eq? v v2) v1]
    [`(Refi, b ,v ,p) #:when (eq? v v2) T]
    [`(Refi ,b ,v ,p) `(Refi ,b ,v ,(subst-pred v1 v2 p))]
    [`(,x : ,s -> ,t) #:when (eq? v2 x) `(,x : ,(subst-type v1 v2 s) -> ,t)]
    [`(,x : ,s -> ,t) `(,x : ,(subst-type v1 v2 s) -> ,(subst-type v1 v2 t))]
    [_ (error 'subt-type "invalid type substituion: want to subst ~a with ~a in ~a" v2 v1 T)]))

;; ----------------------------------------------------------------------------------
; Use Rosette (z3) to check the constraints
(define (check-constraint c ctx)
  (define (define-symbolic-ctx ctx)
    (for ([key (in-dict-keys ctx)])
      (define symbolic-type (dict-ref ctx key))
      (match symbolic-type
        ['Int (eval `(define-symbolic ,key integer?))]
        ['Bool (eval `(define-symbolic ,key boolean?))]
        [_ (error "Unsupported type ~a" symbolic-type)])))
  (begin (define-symbolic-ctx ctx) (sat? (solve (eval `(assert ,(compile-constraint c ctx)))))))

(define (define-symbolic-func x T)
  (match T
    ['Int (eval `(define-symbolic ,x integer?))]
    ['Bool (eval `(define-symbolic ,x boolean?))]
    [_ (error "Unsupported type ~a" T)]))

(define (compile-predicate p)
  (match p
    ['True #t]
    ['False #f]
    [p #:when (or (number? p) (symbol? p)) p]
    [`(= ,p1 ,p2) `(= ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(<= ,p1 ,p2) `(<= ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(< ,p1 ,p2) `(< ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(> ,p1 ,p2) `(> ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(>= ,p1 ,p2) `(>= ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(not ,p1) `(not ,(compile-predicate p1))]
    [`(and ,p ...) `(and ,@(map compile-predicate p))]
    [`(or ,p ...) `(or ,@(map compile-predicate p))]
    [`(if ,p1 ,p2 ,p3)
     `(if ,(compile-predicate p1)
          ,(compile-predicate p2)
          ,(compile-predicate p3))]
    [`(+ ,p1 ,p2) `(+ ,(compile-predicate p1) ,(compile-predicate p2))]
    [`(- ,p1 ,p2) `(+ ,(compile-predicate p1) ,(compile-predicate p2))]
    [_ (error 'check-constraint "invalid predicate ~a" p)]))

(define (compile-constraint c ctx)
  (match c
    [`(forall ,x ,T ,p ,c^)
     #:when (memq T '(Int Bool))
     (let ([ctx^ (begin (define-symbolic-func x T) (dict-set ctx x T))])
       `(forall (list ,x) (=> ,(compile-predicate p) ,(compile-constraint c^ ctx^))))]
    [`(and ,c1 ,c2) `(and ,(compile-constraint c1 ctx) ,(compile-constraint c2 ctx))]
    [p (compile-predicate p)]
    [_ (error 'check-constraint "invalid constraint ~a" c)]))


;; ===========================  Test Cases ===============================



(define ctx1 '((x . Int)))
(define ctx2 '((x . Int) (y . Int)))
(define ctx3 '((x . Int) (y . Int) (z . Int)))
(define cst0 '(forall x Int (= x 5) (forall y Int (= y (+ 1 x)) (and (>= x 0) (< y x)))))
(define cst1 '(forall x Int (= x 5) (forall y Int (= y (+ 1 x)) (and (>= x 0) (> y x)))))
(define test-cases
  (test-suite
   "Sample test cases for check-constraint function"
   (check-equal? (check-constraint '(and (<= x 10) (>= x 0)) ctx1) #t "x is in range [0, 10]")
   (check-equal? (check-constraint '(and (< x 10) (> x 0)) ctx1) #t "x is in range (0, 10)")
   (check-equal? (check-constraint '(and (<= x 0) (>= x 10)) ctx1) #f "x is in contradictory range")
   (check-equal? (check-constraint '(and (<= x 10) (>= y 0)) ctx2) #t "x is in range [0, 10] and y is in range [0, +inf)")
   (check-equal? (check-constraint '(and (<= x 10) (>= x 0) (>= y 5)) ctx2) #t "x is in range [0, 10] and y is in range [5, +inf)")
   (check-equal? (check-constraint '(and (<= x y) (>= y z) (>= x 0)) ctx3) #t "x <= y, y >= z, x >= 0")
   (check-equal? (check-constraint '(and (< x y) (> y z) (> x 0)) ctx3) #t "x < y, y > z, x > 0")
   (check-equal? (check-constraint cst0 '()) #f "x = 5, y = x + 1, x >= 0 && y < x")
   (check-equal? (check-constraint cst1 '()) #t "x = 5, y = x + 1, x >= 0 && y > x")))
(run-test test-cases)


; values
(define val-T 'True)
(define val-F 'False)
(define val-fn-id-bool `(lambda x Bool x))
(define val-fn-id-int `(lambda x Int x))
(define val-fn-add `(lambda x Int (lambda y Int y)))

; Type



(define refi-prog0-bad '((lambda x (Refi Int x (<= x 0)) x) 5))
(define refi-prog1-bad '((lambda x (Refi Bool x (and x False)) x) True))


(define refi-app1-good '((lambda x (Refi Int x (<= x 0)) x) -5))
(define refi-ascr-good '(-5 : (Refi Int x (<= x 0))))
(define refi-app2-good '((lambda x (Refi Bool x True) x) True))


(define refi-let-good '(let x 5 ((lambda y (Refi Int y (>= y 4)) y) x)))
(define add-prog `(lambda x (Refi Int x (>= x 0)) (lambda y (Refi Int x (= y 1)) ((add x) y))))

(define tests-basic
  (test-suite "test for basic type infer on STLC"
              (check-equal? (type-infer val-F '()) '(Refi Bool x False) "False")
              (check-equal? (type-infer val-T '()) '(Refi Bool x True) "True")
              (check-equal? (type-infer val-fn-id-bool '()) '(x : Bool -> Bool) "boolean identity")
              (check-equal? (type-infer val-fn-id-int '()) '(x : Int -> Int) "boolean identity")
              (check-equal? (type-infer '(lambda x (Refi Int x (<= x 0)) x) '()) '(x : (Refi Int x (<= x 0)) -> (Refi Int x (<= x 0))) "Basic lambda on refinment type")
              (check-equal? (type-infer '(lambda x (Refi Int x (<= x 0)) x) '()) '(x : (Refi Int x (<= x 0)) -> (Refi Int x (<= x 0))) "Basic lambda on refinment type")
              (check-equal? (type-infer '(lambda x (Refi Int x (<= x 0)) x) '()) '(x : (Refi Int x (<= x 0)) -> (Refi Int x (<= x 0))) "Basic lambda on refinment type")
              (check-equal? (type-infer refi-app1-good '()) '(Refi Int x (<= x 0)) "refinement type good")
              (check-equal? (type-infer refi-app2-good '()) '(Refi Bool x True) "refinement type good")))

(run-test tests-basic)

; Program for Demo
; PART 1
; (type-infer 1 '())
; (type-infer 'add '())
; (type-infer 'sub '())

; (type-infer '(lambda x (Refi Int x (>= x 0)) (add x)) '())
; (type-infer '(lambda x (Refi Int x (>= x 2)) (sub x)) '())

; (type-infer '(let f (lambda x Int (lambda y Int ((add x) y))) (let x 5 (f x))) '())
; (type-infer '(let f (lambda x (Refi Int x (>= x 0)) (lambda y Int ((add x) y))) (let x 5 (f x))) '())
; (type-infer '(let f (lambda x (Refi Int x (>= x 0)) (lambda y (Refi Int y (>= y 10)) ((add x) y))) f) '())

; PART 2
;; Expect True
; (subtype? '(x : (Refi Int x (>= x 0)) -> (Refi Int x (>= x 10))) '(x : (Refi Int x (>= x 1)) -> (Refi Int x (>= x -10))))
;; Expect False
; (subtype? '(x : (Refi Int x (>= x 0)) -> (Refi Int x (>= x 10))) '(x : (Refi Int x (>= x -1)) -> (Refi Int x (>= x -10))))
;; Expect False
; (subtype? '(x : (Refi Int x (>= x 0)) -> (Refi Int x (>= x -10))) '(x : (Refi Int x (>= x 1)) -> (Refi Int x (>= x 10))))


; PART 3
; (type-infer '((lambda x (Refi Int x (>= x 0)) x) 5) '())


; (define func '(lambda x (Refi Int x (>= x 0)) x))
; (define apply-function-good '(lambda f (x : (Refi Int x (>= x 1)) -> (Refi Int x (>= x -10))) (lambda n (Refi Int x (>= x 2)) (f n))))
; (type-infer `(,apply-function-good ,func) '())

; (define apply-function-bad '(lambda f (x : (Refi Int x (>= x 1)) -> (Refi Int x (>= x 10))) (lambda n (Refi Int x (>= x 2)) (f n))))
; (type-infer `(,apply-function-bad ,func) '())


; PART 4
; Problem
; This should be a existential type, since my substitution on typing rules don't substitude right handside
; (type-infer '(let f (lambda x (Refi Int x (>= x 0)) (lambda y (Refi Int y (>= y 0)) ((add x) y))) (let x 2 (let y 3 ((f x) y)))) '())


; (type-infer '(let f (lambda x (Refi Int x (>= x 0)) (lambda y (Refi Int y (>= y 0)) ((add x) y))) ((f 3) 4)) '())
