module Homework120927 where 

data Nat : Set where 
  zero : Nat 
  succ : Nat -> Nat 

{-# BUILTIN NATURAL Nat #-}

{-# BUILTIN SUC succ #-}

{-# BUILTIN ZERO zero #-}


--Boolean operators 
---

data Bool : Set where 
  true  false : Bool

_∨_ : Bool -> Bool -> Bool 
false ∨ false = false 
_  ∨ _        = true

_∧_ : Bool -> Bool -> Bool 
true ∧ true = true 
_ ∧  _      = false 

¬_ : Bool -> Bool 
¬ true = false 
¬ _    = true

_⟾_ : Bool -> Bool -> Bool 
true ⟾ false = false
_ ⟾ _        = true 


--exercise 1
----------------------------------------------------------------

pred : (n : Nat) -> Set 
pred zero       = Bool 
pred (succ n)   = Bool -> pred n  

taut : (n : Nat) -> pred n -> Bool 
taut zero     f = f
taut (succ y) f = (taut y (f true)) ∧ (taut y (f false))   

----------------------------------------------------------------

-- Data types taken from the course homepage 
data Unit : Set where 
  <> : Unit  

data _×_ (A B : Set) : Set where
  <_,_> : A -> B -> A × B

--exercise 2
----------------------------------------------------------------

vec : (A : Set) ->  (n : Nat) ->  Set
vec A zero      = Unit   
vec A (succ n)  =  A × vec A n  

head : ∀ {A n} -> vec A (succ n) -> A 
head < x , xs > = x     

tail : ∀ {A n} -> vec A (succ n) -> vec A n 
tail < x , xs > = xs

min : Nat -> Nat -> Nat 
min (succ n) (succ m)  = succ (min n m)     
min _ _ = zero 
 
zip : ∀ { A B } -> ∀ n m -> vec A n -> vec B m -> vec ( A × B ) (min n m) 
zip zero _ _ _ = <>
zip (succ _)  zero _ _ = <>
zip (succ n) (succ m) < x , xs > < y , ys > = < < x , y > , zip n m xs ys >  

--alternative zip function where the length of the input 
--vectors must be the same size 
{-
zip' : ∀ {A B } -> ∀ n -> vec A  n -> vec B n -> vec ( A × B ) n    
zip'  0 _ _  = <>
zip'  (succ n) < x , xs > < y , ys > = < < x , y > , zip' n xs ys >  
-}

--exercise 3
----------------------------------------------------------------

--3a 
--------------------------------

_&_ : Set ->  Set -> Set  
A & B = A × B

data ⊥ : Set where 

¬' : Set -> Set 
¬' A = A -> ⊥ 

_<==>_ : Set -> Set -> Set 
A <==> B = (A -> B) & (B -> A)

3a : (P : Set) ->  ¬' (¬' (¬' P)) -> (¬' P) 
3a P =  λ prem P → prem (λ ¬P → ¬P P)    

data Vec (A : Set) : Nat -> Set where 
  [] : Vec A zero 
  _∷_ : ∀ {n} -> A -> Vec A n -> Vec A (succ n) 

head' : {n : Nat} -> {A : Set} -> Vec A (succ n) -> A 
head' (x ∷ xs) = x  

_+₂_ : Nat -> Nat -> Nat 
zero +₂ m = m 
(succ n) +₂ m = succ (n +₂ m)

_++_ : ∀ {n m} -> {A : Set} -> Vec A n -> Vec A m -> Vec A (n +₂ m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys) 
--3b
--------------------------------

data _∨'_ (A B : Set ) : Set where  
  inl : A -> A ∨' B 
  inr : B -> A ∨' B 

∧-elimA : ∀ {A B} -> A & B -> A  
∧-elimA < A , B >  = A

∧-elimB : ∀ {A B} -> A & B -> B 
∧-elimB < A , B > = B 

∨-elim : {A B C : Set} -> (A ∨' B ) -> (A -> C ) -> (B -> C) -> C 
∨-elim (inl A) f _ = f A 
∨-elim (inr B) _ f = f B 

_+_ : Set -> Set -> Set
A + B = A ∨' B 

3b : (P Q : Set) -> ¬' (P + Q) <==> (( ¬' P) & (¬' Q))
3b P Q = < (λ prem → < (λ P → prem (inl P)) , (λ Q → prem (inr Q)) >) , 
  (λ prem P∨Q → ∨-elim P∨Q (λ P → ∧-elimA prem P) (λ Q' → ∧-elimB prem Q')) > 

--code taken from the course homepage  
--------------------------------

data ∀' (A : Set) (B : A → Set) : Set where
  ∀'i : ((x : A) → B x) → ∀' A B

∀'e : {A : Set} {B : A → Set} (f : ∀' A B) → (a : A) → B a
∀'e (∀'i f) a = f a

-- Existential quantifiers can be defined as Σ-types: a term z : ∃ A B is
-- a (dependent) pair consisting of a witness α : A and a proof p of B α.
-- Note that B is a "predicate".

data ∃ (A : Set) (B : A → Set) : Set where
 <_,_> : (α : A) → B α → ∃ A B

-- Existence elimination: d is merely the curried version of (f : ∃ A B → C).

∃-elim : {A : Set} → {B : A → Set} → {C : Set} → ((α : A) → B α → C) -> ∃ A B → C
∃-elim d < α , p > = d α p

--3c
--------------------------------
--what we want to prove 
-- ¬(∃ x ∈  D)P (x) <->  (∀ x  ∈  D)¬P (x) 

3c : {D : Set} {P : D -> Set} -> ¬' (∃ D P) <==> ∀' D (λ x → ¬' (P x))
3c = < (λ prem → ∀'i (λ x Px → prem < x , Px > )) , (λ prem x → ∃-elim (∀'e prem) x) >    

