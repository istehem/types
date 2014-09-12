------------------------------------------------------------------------
-- Some useful definitions
------------------------------------------------------------------------

module Prelude where

------------------------------------------------------------------------
-- Repetition

-- Natural numbers.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 6 _+_

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}
{-# BUILTIN NATPLUS _+_  #-}

-- Lists.

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- Vectors.

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

-- The empty type.

data ⊥ : Set where

-- Equality.

infix 4 _≡_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

------------------------------------------------------------------------
-- Something new

-- Finite sets. Fin n represents natural numbers smaller than n.

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

private

  -- Examples.

  ′0 : ∀ {n} → Fin (1 + n)
  ′0 = zero

  ′1 : ∀ {n} → Fin (2 + n)
  ′1 = suc zero

  ′2 : ∀ {n} → Fin (3 + n)
  ′2 = suc (suc zero)

-- A safe lookup function.

lookup : ∀ {A n} → Fin n → Vec A n → A
lookup zero    (x ∷ xs) = x
lookup (suc i) (x ∷ xs) = lookup i xs
