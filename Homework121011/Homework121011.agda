{-# OPTIONS --no-positivity-check #-}


module Homework121011 where 

--exercise 1 
{- 
a) X and Bool 

unify[X = Bool] 

σ = X -> Bool 

b) X and Y 

unify[X = Y]

σ = X -> Y  

c) Bool and (X → Y) 

fail

d) X → Y and Y → Bool 

unify [X = Y , Y = Bool]

unify ([Y = Bool]) ○ [X → Y] = 
  [(Y -> Bool)] ○ [X -> Y]  = [Y ->  Bool, X -> Bool] = σ  

e) X and X → X

fail 

f) X → Bool → Z and (Y → Z) → X 

S = X → (Bool → Z) 
T = (Y → Z) → X 

unify [X = (Y → Z), (Bool → Z) = X] = 
----  

unify [X = (Y → Z)] = X -> (Y → Z) 

unify [Bool → Z = X] = X -> (Bool → Z) 

[X -> (Y→Z)] ○ [X -> (Bool → Z)]  = [X -> (Y→Z) , (Y → Z) -> (Bool → Z)] = σ   

-}


------------------------------------------------------------------------
-- The untyped λ-calculus
------------------------------------------------------------------------

-- Note: The following option is unsafe.

--{-# OPTIONS --no-positivity-check #-}

--module Untyped where

open import Prelude

------------------------------------------------------------------------
-- Syntax

-- Variables are represented using de Bruijn indices. Term n stands
-- for terms with at most n distinct free variables.

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  lam : Term (suc n) → Term n
  app : Term n → Term n → Term n

-- Examples.

id : Term zero
id = lam (var zero)  -- λx.x

ω : Term zero
ω = lam (app (var zero) (var zero))  -- λx.xx

Ω : Term zero
Ω = app ω ω  -- (λx.xx) (λx.xx)

β-sub : ∀ {n} -> Term n -> Term n 
β-sub = {!!} 




------------------------------------------------------------------------
-- Denotational semantics

-- Semantic domain. (Not proper Agda code.)

data Value : Set where
  fun : (Value → Value) → Value

-- Application.

_·_ : Value → Value → Value
fun f · x = f x

-- Environments.

Env : ℕ → Set
Env n = Vec Value n

-- Evaluator.

eval : ∀ {n} → Term n → Env n → Value
eval (var x)     ρ = lookup x ρ
eval (lam t)     ρ = fun (λ v → eval t (v ∷ ρ))
eval (app t₁ t₂) ρ = eval t₁ ρ · eval t₂ ρ

-- Examples.

test₁ : eval id [] ≡ fun (λ v → v)
test₁ = refl

test₂ : eval ω [] ≡ fun (λ v → v · v)
test₂ = refl

-- The "value" eval Ω [] does not terminate:
--
--   eval Ω []
-- = eval ω [] · eval ω []
-- = fun (λ v → v · v) · eval ω []
-- = eval ω [] · eval ω []
-- = fun (λ v → v · v) · eval ω []
-- = eval ω [] · eval ω []
-- ⋮
--
-- Isn't Agda code supposed to terminate? Yes, but the definition of
-- Value above isn't proper Agda code.

{-
data Value₁ {n : ℕ } : Set where 
  fun  : Term (suc n) -> Term n -> Value₁    
-}

data Value₁ : Set where 
  fun  : ∀ {n} -> Term (suc n) -> Term n -> Value₁    

⌜_⌝ : {n : ℕ} -> Value₁ -> Term n  
⌜ fun y y' ⌝ = lam {!y!}   

postulate
  subst : {n : ℕ} -> Term (suc n) -> Term n -> Term n


data _==>_ : Term zero -> Term zero -> Set where 
   E-app₁    : ∀ {t₁ t₁' t₂} -> (app t₁ t₂)  ==> (app t₁' t₂)   
   E-app₂    : ∀ {t₂ t₂'}  -> ∀ {v₁} -> (app ⌜  v₁  ⌝ t₂) ==> (app ⌜ v₁ ⌝ t₂') 
   E-app-abs : ∀ {t₁₂} -> ∀ {v₂} -> (app (lam t₁₂ )  ⌜ v₂ ⌝) ==> (subst t₁₂ ⌜ v₂ ⌝)  



