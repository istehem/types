module Exercise6 where 

data ℕ : Set where 
  zero : ℕ 
  suc  : ℕ -> ℕ 

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN ZERO zero #-}

double : ℕ -> ℕ 
double zero    = zero
double (suc n) = suc (suc (double n)) 

--Exercise 6a
-----------------------------------------------------------------------------
data BinaryNumber : Set where 
     zero'    : BinaryNumber 
     twice    : BinaryNumber -> BinaryNumber
     sucTwice : BinaryNumber -> BinaryNumber  
-----------------------------------------------------------------------------
     
--Exercise 6b 
-----------------------------------------------------------------------------
bin2un : BinaryNumber ->  ℕ 
bin2un zero'        = zero
bin2un (sucTwice y) = suc (double (bin2un y))   
bin2un (twice y)    = double (bin2un y)
-----------------------------------------------------------------------------

sucBin : BinaryNumber -> BinaryNumber 
sucBin zero'            = sucTwice zero' 
sucBin (twice y)        = sucTwice y
sucBin (sucTwice y)     = twice (sucBin  y)

--Exercise 6c  
-----------------------------------------------------------------------------
un2bin : ℕ -> BinaryNumber 
un2bin zero    = zero'
un2bin (suc y) = sucBin (un2bin y) 
-----------------------------------------------------------------------------

data I (A : Set) (a : A) : A → Set where
  refl : I A a a

subst : {A : Set} -> {P : A → Set} → {a₁ a₂ : A} → I A a₁ a₂ -> P a₂ -> P a₁
subst refl pa₂ = pa₂

cong : {A B : Set} → {a₁ a₂ : A} → (f : A → B) → I A a₁ a₂ → I B (f a₁) (f a₂)
cong f refl = refl

--Exercise 6d 
-----------------------------------------------------------------------------

{-
  I get the following error 
  (bin2un (sucBin (un2bin y))) != (suc y) of type ℕ
  wich I don't know have to fix
-}
{-
  proof : (n : ℕ) -> I ℕ (bin2un (un2bin n)) n
  proof zero    = refl
  proof (suc y) = subst {ℕ} {λ x → I ℕ (bin2un (un2bin (suc x))) (suc y)} (proof y) refl
-}

{-
  You are for instance allowed to write the following function 
-}

foo : BinaryNumber 
foo = twice (twice (twice zero')) 
                 
{-
  (bin2un foo) will return 0 and (un2bin (bin2un foo)) will return zero' wich isn't the 
  original BinaryNumber. Therefor it will not pass a reflexivity check in agda. 
-}

