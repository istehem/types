module Exercise5 where 

--Exercise 5a 

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x 

data Bool : Set where 
  true : Bool
  false : Bool

_∨'_ : Bool -> Bool -> Bool 
false ∨' false  = false 
_ ∨' _          = true 

_∧'_ : Bool -> Bool -> Bool 
true ∧' true = true
_ ∧'  _ = false

¬' : Bool -> Bool 
¬' true = false 
¬' _    = true

--Exercise 5a 
--------------------------------------------------------------

deMorgan₁ : (p q : Bool) -> (¬' (p ∨' q)) ≡ (¬' p ∧' ¬' q) 
deMorgan₁ true q = refl
deMorgan₁ false true = refl
deMorgan₁ false false = refl  

deMorgan₂ : (p q : Bool) -> ¬' (p ∧' q) ≡ (¬' p ∨' ¬' q)
deMorgan₂ false q = refl
deMorgan₂ true true = refl
deMorgan₂ true false = refl

data Nat : Set where 
  zero : Nat 
  suc  : Nat -> Nat 

_+_ : Nat -> Nat -> Nat 
n + zero = n 
n + (suc m)    = suc (n + m) 

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN ZERO zero #-}

--------------------------------------------------------------

--Exercise 5b 
data PropFormula : Set where 
  X     : Nat -> PropFormula 
  _∨''_ : PropFormula -> PropFormula -> PropFormula 
  ¬''   : PropFormula -> PropFormula 

--------------------------------------------------------------

Env : Set 
Env = Nat -> Bool

--Exercise 5c 
--------------------------------------------------------------
[[_]]_ : PropFormula -> Env -> Bool 
[[ X y ]] env = env y
[[ y ∨'' y' ]] env = ([[ y ]] env) ∨' ([[ y' ]] env)
[[ ¬'' y ]] env = ¬' ([[ y ]] env) 
--------------------------------------------------------------

assign : Env 
assign 0 = true
assign 1 = true 
assign _ = true 

propformula₁ : PropFormula 
propformula₁ = (X 0) ∨'' (X 1)  

and : PropFormula 
and = ¬'' ((¬'' (X 0)) ∨'' (¬'' (X 1)))

test₁ : Bool 
test₁ = [[ propformula₁ ]] assign  

test₂ : Bool 
test₂ = [[ and ]] assign 

--Alternativ 5a using Natural Deduction 
--Not the usage of postulate to handle double negation  
--------------------------------------------------------------

data _∧_ (A B : Set) : Set where 
  <_,_> : A -> B -> A ∧ B  

data _∨_ (A B : Set) : Set where 
  inl : A -> (A ∨ B)
  inr : B -> (A ∨ B)

data ⊥ : Set where
  
¬ : Set -> Set
¬ A = A -> ⊥

∧-elim-l : ∀ {A B} -> A ∧ B -> A
∧-elim-l < A , B > = A  

∧-elim-r : ∀ {A B} -> A ∧ B -> B 
∧-elim-r < A , B > = B 

∨-elim : ∀ {A B} {C : Set} -> A ∨ B -> (A -> C) -> (B -> C) -> C 
∨-elim (inl A) f _ = f A   
∨-elim (inr B) _ f = f B

_<==>_ : Set -> Set -> Set 
A <==> B = (A -> B) ∧ (B -> A)  

postulate 
  ¬¬ : {P : Set} -> ¬ (¬ P) -> P 
 
deMorgan₃ : {P Q : Set} -> ¬ (P ∨ Q) <==> (¬ P ∧ ¬ Q) 
deMorgan₃ = < (λ prem → < (λ P → prem (inl P)) , (λ Q → prem (inr Q)) >) , 
              (λ prem P∨Q → ∨-elim P∨Q (∧-elim-l prem) (∧-elim-r prem)) >  

deMorgan₄ : {P Q : Set} -> ¬ (P ∧ Q) <==> (¬ P ∨ ¬ Q)
deMorgan₄ = < (λ prem → ¬¬ (λ ¬goal → prem < (¬¬ (λ ¬P → ¬goal (inl ¬P))) , ¬¬ (λ ¬Q → ¬goal (inr ¬Q)) > )) , 
              (λ prem P∧Q → ∨-elim prem (λ ¬P → ¬P (∧-elim-l P∧Q)) (λ ¬Q → ¬Q (∧-elim-r P∧Q))) > 
