------------------------------------------------------------------------
-- The untyped λ-calculus
------------------------------------------------------------------------

-- Note: The following option is unsafe.

{-# OPTIONS --no-positivity-check #-}

module Untyped where

open import Prelude

------------------------------------------------------------------------
-- Syntax

-- Variables are represented using de Bruijn indices. Term n stands
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

-- The "value" eval Ω [] does not terminate:
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
