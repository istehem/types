module Homework120920 where 

---------------------------------------------------------------

data Bool : Set where 
  true : Bool 
  false : Bool 

data Nat : Set where 
  zero : Nat 
  succ : Nat → Nat 

data _≡_ {A : Set} (x : A)  : A -> Set where 
  refl : x ≡ x 
  
  --1
---------------------------------------------------------------

_&&_ : Bool → Bool → Bool 
true && true = true 
_ &&  _      = false  
 
_=>_ : Bool -> Bool -> Bool 
false => _ = true
true  => x = x 

--2
---------------------------------------------------------------

--a
_if_then_else_ : (a : Set) -> Bool -> a -> a -> a 
a if true then x else _ = x
a if _    then _ else y = y 

_=>₂_ : Bool -> Bool -> Bool  
x =>₂ y = Bool if x then y else true 

--b
if_then_else_ : {a : Set} -> Bool -> a -> a -> a 
if true then x else _ = x
if _    then _ else y = y 

_=>₃_ : Bool -> Bool -> Bool  
x =>₃ y = if x then y else true 

--3
---------------------------------------------------------------

_-_ : Nat -> Nat -> Nat 
zero - _        = zero 
x    - zero     = x
succ x - succ y = x - y      

--4
---------------------------------------------------------------

_+_ : Nat → Nat → Nat 
zero + y = y 
succ x + y = succ (x + y) 

P : (succ zero) + (succ (succ zero)) ≡ succ (succ (succ zero))  
P = refl 

_*_ : Nat → Nat → Nat 
zero * y   = zero 
succ x * y = x * y + y 

infixl 60 _+_ 
infixl 70 _*_  

rec :  {C : Set} → C -> (Nat → C → C) → (z : Nat) → C
rec d e zero     = d 
rec d e (succ y) = e y (rec d e y)

--a
_^_ : Nat → Nat → Nat 
_ ^ zero     = succ zero 
x ^ (succ y) = x * (x ^ y)   

--b
_^₂_ : Nat → Nat → Nat
_ ^₂ zero     = succ zero   
x ^₂ (succ p) = rec x (λ _ n -> n * x) p 

--5
---------------------------------------------------------------

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

--a
append : {A : Set} -> List A -> List A -> List A 
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

--b 
data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

append₂ : {A : Set} -> {n₁ n₂ : Nat} -> Vec A n₁ -> Vec A n₂ -> Vec A (n₁ +  n₂)    
append₂ [] ys        = ys
append₂ (x :: xs) ys = x :: append₂ xs ys         

--6
---------------------------------------------------------------

data _~_ : Nat  → Nat → Set where
    ~+ : {n : Nat} →     n ~ (succ n)
    ~0 : {n : Nat} →     n ~ n
    ~- : {n : Nat} →     (succ n) ~ n

max : {m n : Nat} -> m ~ n  -> Nat 
max (~+ {x}) = succ x  
max (~0 {x}) = x
max (~- {x}) = succ x 

data AVL-Tree (A : Set) : Nat -> Set where 
    Nul : A -> AVL-Tree A zero      
    Bin : {m n : Nat} -> (bal : m ~ n) -> A -> AVL-Tree A m 
          -> AVL-Tree A n -> AVL-Tree A (succ (max bal))
  

--simlpe test cases 

foo : AVL-Tree Bool (succ (succ zero))     
foo = Bin ~- true (Bin ~0 true (Nul true) (Nul false)) (Nul false)     
 
foo2 : AVL-Tree Bool (succ zero)
foo2 = Bin ~0 true (Nul true) (Nul false)

--7
---------------------------------------------------------------

{- 
case: t = 0 
... show P(0) 
 
case: succ t 
... show P(succ t), using P(t)

case: pred t
... show P(pred t), using P(t)

case: iszero t
... show P(iszero t), using P(t)
-}

--8
---------------------------------------------------------------
{-
nothing evaluated to normal form yet  

                 t₂ -> t₂' 
===================================================
  if t₁ then t₂ else t₃ -> if t₁ then t₂' else t₃


t₂ evaluated to normal form v₂   

                 t₃ -> t₃' 
===================================================
 if t₁ then v₂ else t₃ -> if t₁ then v₂ else t₃'


t₂ and t₃ evaluated to normal form v₂ and v₃

                 t₁ -> t₁' 
===================================================
if t₁ then v₂ else v₃ -> if t₁' then v₂ else v₃
 
if true then v₂ else v₃ -> v₂

if false then v₂ else v₃ -> v₃

-}