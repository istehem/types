module Homework121004 where 

data Bool : Set where
  true false : Bool

data _×_ (A B : Set) : Set where
  <_,_> : A -> B -> A × B


_&_ : Set ->  Set -> Set  
A & B = A × B

data ⊥ : Set where 

¬ : Set -> Set 
¬ A = A -> ⊥ 

_<==>_ : Set -> Set -> Set 
A <==> B = (A -> B) & (B -> A)

data _∨_ (A B : Set ) : Set where  
  inl : A -> A ∨ B 
  inr : B -> A ∨ B 

∧-elimA : ∀ {A B} -> A & B -> A  
∧-elimA < A , B >  = A

∧-elimB : ∀ {A B} -> A & B -> B 
∧-elimB < A , B > = B 

∨-elim : {A B C : Set} -> (A ∨ B ) -> (A -> C ) -> (B -> C) -> C 
∨-elim (inl A) f _ = f A 
∨-elim (inr B) _ f = f B 

-------------------------------------

--Exercise 1

exercise1 : {A B C : Set} -> (A ∨ (B × C)) <==> ((A ∨ B) × (A ∨ C))      
exercise1 = < (λ prem → < ∨-elim prem (λ A -> inl A) (λ B×C -> inr (∧-elimA B×C)) , ∨-elim prem (λ A → inl A) (λ B×C → inr (∧-elimB B×C)) >) , 
           (λ prem → ∨-elim (∧-elimA prem) (λ A → inl A) (∨-elim (∧-elimB prem) (λ A B → inl A) (λ C B → inr < B , C >))) > 


--Exercise 2 
-------------------------------------

{-
exercise 2a. ; 

(a.1) : λ f x. f x 

λ . λ . 1 0 

---------------------------------

(a.2) : λ f . f (λ x.x )

λ . 0 (λ. 0) 

----------------------------------

(a.3) : λx. f x 

Γ = f ⟼ 0 

λ. 1 0 

----------------------------------

(a.4) : f x 

Γ = f ⟼ 1 
    x ⟼ 0 

1 0 

----------------------------------

(a.5) : Y = λf.(λx.f(x x))(λx.f(x x)) 

Y = λ.(λ.1(0 0))(λ.1(0 0)) 

----------------------------------

-}

----------------------------------

data ℕ : Set where 
  zero : ℕ 
  succ : ℕ -> ℕ 

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     succ  #-}

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (succ n)
  suc  : ∀ {n} → Fin n → Fin (succ n)

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  lam : Term (succ n) → Term n
  app : Term n → Term n → Term n

--2b.
-- λ . λ . 1 0 

2b-1 :  Term 0 
2b-1 = lam (lam (app (var (suc zero)) (var zero))) 

--λ . 0 (λ. 0) 

2b-2 : Term 0 
2b-2 = lam (app (var zero) (lam (var zero))) 

--λx. f x
--Γ = f ⟼ 0 
--λ. 1 0 

2b-3 : Term 1
2b-3 = lam (app (var (suc zero)) (var zero))  

{-
Γ = f ⟼ 1 
    x ⟼ 0 

1 0 
-}

2b-4 : Term 2
2b-4 = app (var (suc zero)) (var zero) 

--λf.(λx.f(x x))(λx.f(x x)) 
--Y = λ.(λ.1(0 0))(λ.1(0 0)) 

2b-5 : Term 0 
2b-5 = lam (app (lam (app (var (suc zero)) (app (var zero) (var zero)))) (lam (app (var (suc zero)) (app (var zero) (var zero)))))

--2c.
-------------------------------------

data LambdaTerm : Set where 
  var : ℕ -> LambdaTerm  
  lam : ℕ -> LambdaTerm -> LambdaTerm  
  app : LambdaTerm -> LambdaTerm -> LambdaTerm 

data List (A : Set) : Set where
  []   : List A 
  _::_ : A -> List A -> List A 

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x :: xs)  with p x
... | true  = x :: filter p xs
... | false = filter p xs

isEmpty : ∀ {A} -> List A -> Bool
isEmpty [] = true
isEmpty _  = false 

_++_ : ∀ {A} -> List A -> List A -> List A 
[] ++ Ys = Ys
(y :: y') ++ Ys = y :: (y' ++ Ys)

_/=_ : ℕ -> ℕ -> Bool 
zero /= zero      = false
succ y /= succ y' = y /= y'
_ /= _            = true

fV : LambdaTerm -> List ℕ 
fV (var y)     = y :: []
fV (lam x t)   = filter (λ y -> x /= y ) (fV t)
fV (app t₁ t₂) = fV t₁ ++ fV t₂ 
 
isClosed : LambdaTerm -> Bool 
isClosed t = isEmpty (fV t)

test₁ : Bool
test₁ = isClosed (var 0) 

--returns false since the last term "var 2" isn't bounded 
test₂ : Bool 
test₂ = isClosed (lam 0 (lam 1 (app (app (var 0) (app (lam 2 (app (var 1) (var 2))) (var 0))) (var 2))))
    
test₃ : Bool 
test₃ = isClosed (lam 0 (app (var 0) (var 1))) 

test₄ : Bool 
test₄ = isClosed (lam 0 (lam 1 (app (app (var 0) (var 1)) (var 1)))) 


--Exercise 3
-------------------------------------
{-

Y g = (λf.(λx.f(x x)) (λx.f(x x))) g #(1) By definition 
    => λx.g(x x) (λx.g(x x))          #(2) β-reduction           
    => g(λx.g(x x)(λx.g(x x)))        #(3) β-reduction 
    <= g (Y g)                        #(4) from step (2)    
-}

{-
Y g ->* t , g (Y g) ->* t      

Yes this is the case. For example can (Y g) reduce to 
g(λx.g(x x)(λx.g(x x))) in two steps (see above) and then g (Y g) reduces 
g(λx.g(x x)(λx.g(x x))) in one step (see above).  

-}

--Exercise 4 
-------------------------------------
{-
add =  λ x y -> if isZero x then y else (if isZero y then x else succ (succ (add (pred x) (pred y))))
-}

-------------------------------------

--Exercise 5
{-
--See file Boolean-Expressions.agda
  Holes filled:
    if-reduces 
    uniqueness-of-normal-forms (Not finished) 
-}



