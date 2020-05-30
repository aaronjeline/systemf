#lang racket
;; Implementation of The Polymorphic Lambda Calculus (AKA System F) in Redex
;; No type inference is supported
;; Features:
;;  unit type
;;  fixpoint combinator
;; Useful Functions
;;  typecheck?, computers the type of a given term, or #f is no type exists
;;  run, reduces a term to a value
;;  erase, remove all typing information from a term


(require redex) ;; Redex library
(provide erase typecheck? valid?)

(module+ test ;; This submodule will contain tests
  (require rackunit)) 


;; Defining the grammar for the Polyforphic Lambda Calculus
(define-language F
  ;; Types
  (t ::=
     x ;; Type Variable
     (∀ x t) ;; Universal Quantification
     (t -> t) ;; Function
     ;; Base types
     Bool 
     Int
     Unit)
  ;; Values
  (v ::= n
     b
     () ;; Unit  value
     (λ (x : t) e) ;; Value Abstraction
     (Λ x e)) ;; Type Abstraction
  (e ::=
     x
     v
     (e t) ;; Type Application
     (e e) ;; Vaue Application
     ;; Let-binding
     (let ((x : t e))
       e)
     (e binop e)
     (unop e)
     (if e e e)
     (fix e))
  ;; Evaluation Contexts
  (E ::= hole
     (E t)
     (E e)
     (v E)
     (E binop e)
     (v binop E)
     (unop E)
     (if E e e)
     (let ((x : t E))
       e)
     (let ((x : t v))
       E))
  (x ::= variable-not-otherwise-mentioned)
  (binop ::= * - +)
  (unop ::= zero? null)
  (n ::= number)
  (b ::= true false)
  (Γ ::= ((x t) ...))) ;; Type Enviornments

;; Metafunction for quering type enviornments
(define-metafunction F
  lookup : x Γ -> t
  [(lookup x Γ) ,(second (assoc (term x) (term Γ)))])

;; Metafunction for extending type enviornments
(define-metafunction F
  ext : x t Γ -> Γ
  [(ext x t ((x_1 t_1) ...)) ((x t) (x_1 t_1) ...)])

;; This judgment is true iff x is in the enviornment Γ
(define-judgment-form F
  #:mode (bound I I)
  #:contract (bound x Γ)
  [(side-condition ,(assoc (term x) (term Γ)))
   -----
   (bound x Γ)])

(module+ test
  (check-true (judgment-holds (bound x ((x Int)))))
  (check-true (judgment-holds (bound x ((y Int) (x Int)))))
  (check-false (judgment-holds (bound y ((x Int))))))


;; Mapping built-in operations to types
(define-judgment-form F
  #:mode (Δ I O)
  #:contract (Δ unop t)
  [(Δ zero? (Int -> Bool))]
  [(Δ null (Int -> Unit))])

  
;; Function for mapping built in operations to functions
(define (δ op)
  (match op
    ['+ +]
    ['- -]
    ['* *]
    ['zero? (λ (x) (if (zero? x)
                       'true
                       'false))]
    ['null (λ (x) `())]))



;; Typing Judgment
(define-judgment-form F
  #:mode (⊢ I I I O)
  #:contract (⊢ Γ e : t)

  ;; Literal Typings
  [----- t-true
   (⊢ Γ true : Bool)]
  
  [----- t-false
   (⊢ Γ false : Bool)]
  
  [----- t-int
   (⊢ Γ n : Int)]

  [------ t-unit
   (⊢ Γ () : Unit)]

  ;; Variables type check if they are bound
  [(bound x Γ)
   ----- t-var
   (⊢ Γ x : (lookup x Γ))]

  ;; Recursive Rules

  ;; Conditional
  [(⊢ Γ e_1 : Bool)
   (⊢ Γ e_2 : t)
   (⊢ Γ e_3 : t)
   ---- t-if
   (⊢ Γ (if e_1 e_2 e_3) : t)]

  ;; Binary Operations
  [(⊢ Γ e_1 : Int)
   (⊢ Γ e_1 : Int)
   ---- t-binop
   (⊢ Γ (e_1 binop e_2) : Int)]

  ;; Unary Operations
  [(Δ unop (t_1 -> t_2))
   (⊢ Γ e : t_1)
   ----- t-unop?
   (⊢ Γ (unop e) : t_2)]

  ;; Fixed-Point combinator
  [(⊢ Γ e : (t_1 -> t_1))
   ------ t-fixpoint
   (⊢ Γ (fix e) : t_1)]

  ;; Let binding
  [(⊢ Γ e_1 : t_1)
   (⊢ (ext x t_1 Γ) e_2 : t_2)
   ------ t-let
   (⊢ Γ (let ((x : t_1 e_1)) e_2) : t_2)]

  ;; Value Abstraction
  [(⊢ (ext x t_1 Γ) e : t_2)
   ---- t-abs
   (⊢ Γ (λ (x : t_1) e) : (t_1 -> t_2))]

  ;; Value Application
  [(⊢ Γ e_1 : (t_1 -> t_2))
   (⊢ Γ e_2 : t_1)
   ---- t-app
   (⊢ Γ (e_1 e_2) : t_2)]
  
  ;; System F Extensions
  ;; Type Abstraction
  [(⊢ Γ e : t)
   ------- t-Type_Abs
   (⊢ Γ (Λ x e) : (∀ x t))]

  ;; Type Application
  [(⊢ Γ e : (∀ x t))
   ------- t-Type-App
   (⊢ Γ (e t_′) : (subst/ty t x t_′))])

;; Examples
(define id
  (term
   (Λ X (λ (x : X) x))))
(define const
  (term
   (Λ A
      (Λ B
         (λ (x : A)
           (λ (y : B)
             x))))))
(define constapp
  `((((,const Bool) Int) true) 3))


(module+ test
  (check-equal?
   (typecheck? `((,id Int) 4))
   'Int)
  (check-equal?
   (typecheck? id)
   `(∀ X (X -> X)))
  (check-equal?
   (typecheck? constapp)
   `Bool)
  (check-equal?
   (typecheck? `(zero? 3))
   `Bool)
  (check-equal?
   (typecheck? `(null 3))
   `Unit))
  

;; Substituion of types
(define-metafunction F
  subst/ty : t x t -> t
  [(subst/ty Bool x t) Bool]
  [(subst/ty Int x t) Int]
  [(subst/ty (t_1 -> t_2) x t)
   ((subst/ty t_1 x t)
    ->
    (subst/ty t_2 x t))]
  [(subst/ty x_1 x_1 t) t]
  [(subst/ty x_1 x_2 t) x_1]
  [(subst/ty (∀ x_1 t_1) x_1 t) (∀ x_1 t_1)]
  [(subst/ty (∀ x_1 t_1) x_2 t) (∀ x_1 (subst/ty t_1 x_2 t))])
  

;; Substitution of terms
(define-metafunction F
  subst : e x e -> e
  [(subst n x e) n]
  [(subst b x e) b]
  [(subst () x e) ()]
  [(subst x_1 x_1 e) e]
  [(subst x_1 x_2 e) x_1]
  [(subst (λ (x_1 : t) e) x_1 e_1) (λ (x_1 : t) e)]
  [(subst (λ (x_1 : t) e) x_2 e_1) (λ (x_1 : t) (subst e x_2 e_1))]
  [(subst (e_1 e_2) x e) ((subst e_1 x e) (subst e_2 x e))]
  [(subst (e_1 t) x e) ((subst e_1 x e) t)]
  [(subst (unop e_1) x e) (unop (subst e_1 x e))]
  [(subst (e_1 binop e_2) x e)
   ((subst e_1 x e) binop (subst e_2 x e))]
  [(subst (if e_1 e_2 e_3) x e)
   (if (subst e_1 x e)
       (subst e_2 x e)
       (subst e_3 x e))]
  [(subst (fix e) x e_1)
   (fix (subst e x e_1))]
  [(subst (let ((x : t e_1))
            e_2)
          x
          e_3)
   ;; Let Shadowing
   (let ((x : t (subst e_1 x e_3))) e_2)]
  [(subst (let ((x_1 : t e_1)) e_2) x_2 e_3)
   (let ((x_1 : t (subst e_1 x_2 e_3)))
     (subst e_2 x_2 e_3))])
            

(module+ test
  (check-equal? (term (subst x y 3))
                (term x))
  (check-equal? (term (subst x x 3))
                (term 3))
  (check-equal? (term (subst (if x 2 3) x true))
                (term (if true 2 3)))
  (check-equal? (term (subst (λ (x : Int) (x + 1)) x 5))
                (term (λ (x : Int) (x + 1))))
  (check-equal? (term (subst (λ (x : Int) (y + x)) y 3))
                (term (λ (x : Int) (3 + x))))
  (check-equal? (term (subst (let ((x : Int 3)) (y + x)) y 5))
                (term (let ((x : Int 3)) (5 + x))))
  (check-equal? (term (subst (let ((x : Int 3)) (y + x)) x 5))
                (term (let ((x : Int 3)) (y + x)))))
                             

  

;; Runtime Sematnics
(define r
  (reduction-relation
   F #:domain e
   
   (--> (n_1 binop n_2)
        ,((δ (term binop))
          (term n_1)
          (term n_2))
        δ2)
   
   (--> (unop n_1)
        ,((δ (term unop)) (term n_1))
        δ1)

   
   (--> (if true e_1 e_2)
        e_1
        if-true)
   (--> (if false e_1 e_2)
        e_2
        if-false)

   (--> (let ((x : t v))
          e)
        (subst e x v)
        let-bind)


   (-->
    (fix (λ (x_f : t_f)
           (λ (x : t) e)))
    (subst (λ (x : t) e)
           x_f
           (fix (λ (x_f : t_f)
                  (λ (x : t) e))))
    fixed-point)
         
   
   
   (--> ((λ (x : t) e) v)
        (subst e x v)
        app)

   ;; System F extensions
   (--> (Λ x e)
        e
        Λ-Erasure)
   (--> (e t)
        e
        Type-App-Erasure)))
        
  
(define r*
  (context-closure r F E))

(define (valid? p)
  (redex-match? F e p))

(define (value? p)
  (redex-match? F v p))
                 

(define (type? t)
  (redex-match? F t t))

(define (binop? p)
  (redex-match? F binop p))

(define/contract (typecheck? p)
  (-> valid? (or/c type? false?))
  (let ((t (judgment-holds (⊢ () ,p : t) t)))
    (if (empty? t)
        #f
        (first t))))

(define/contract (run p)
  (-> typecheck? value?)
  (first (apply-reduction-relation* r* p)))

(define (erase e)
  (match e
    [(? number?) e]
    ['true 'true]
    ['false 'false]
    [(? symbol?) e]
    [`(,e1 ,(? binop? o) ,e2)
     `(,(erase e1) ,o ,(erase e2))]
    [`(,e1 ,(? type?)) (erase e1)]
    [`(Λ ,x ,e) (erase e)]
    [`(zero? ,e) `(zero? ,(erase e))]
    [`(if ,e1 ,e2 ,e3) `(if ,(erase e1)
                            ,(erase e2)
                            ,(erase e3))]
    [`(λ (,x : ,t) ,e) `(λ ,x ,e)]
    [`(,e1 ,e2) `(,(erase e1) ,(erase e2))]))



(module+ test
  (check-equal?
   (erase `(λ (x : Int) x))
   `(λ x x))
  (check-equal?
   (erase `(Λ X (λ (x : X) x)))
   `(λ x x)))

(define fact
  `(fix
    (λ (fact : (Int -> Int))
      (λ (x : Int)
        (if (zero? x)
            1
            (x * (fact (x - 1))))))))

(define factapp
  `(,fact 5))

(define letexample
  `(let ((id : (∀ X (X -> X))
             (Λ X (λ (x : X) x))))
     ((id Unit) ())))


(module+ test
  (check-equal?
   (typecheck? fact)
   `(Int -> Int))
  (check-equal?
   (run factapp)
   120)
  (check-equal?
   (typecheck? letexample)
   'Unit)
  (check-equal?
   (run letexample)
   `()))


                      



