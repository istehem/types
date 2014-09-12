module Exercise4 where 

data ℕ : Set where 
  zero : ℕ 
  suc  : ℕ -> ℕ 

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN ZERO zero #-}

data List (A : Set) : Set where 
  []   : List A 
  _::_ : A -> List A -> List A

data Bool : Set where
  true false : Bool 

_≡_ : ℕ -> ℕ -> Bool 
zero ≡ zero = true
zero ≡ suc y = false
suc x ≡ zero = false
suc x ≡ suc y = x ≡ y 

¬ : Bool -> Bool 
¬ true = false 
¬ false = true 

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x :: xs)  with p x
... | true  = x :: filter p xs
... | false = filter p xs

null : {A : Set} -> List A -> Bool 
null [] = true 
null _  = false 

--Exercise 4a 
------------------------------------------------------------------------
record bagADT : Set₁ where 
  field 
    Bag : Set 
    add : ℕ -> Bag -> Bag 
    delete : ℕ -> Bag -> Bag 
    member : ℕ -> Bag -> Bool 

--Assuming that delete removes all occurrences of the first input parameter 
natBag : bagADT 
natBag = record { Bag = List ℕ 
                ; add =  λ x xs → x :: xs          
                ; delete = λ x xs → filter (λ y → ¬ (x ≡ y)) xs 
                ; member = λ x xs → ¬ (null (filter (λ y → x ≡ y) xs))   
                }

------------------------------------------------------------------------

record counterADT : Set1 where
  field
    Counter : Set
    new : Counter
    get : Counter -> ℕ
    inc : Counter -> Counter
    axiom₁ : ℕ  
    axiom₂ : Bool 
    axiom₃ : Bool 

-- a dependent record can be used instead of existential types in Pierce chapter 24

natCounter : counterADT
natCounter = record { Counter = ℕ
                    ; new = zero
                    ; get = λ n → n
                    ; inc = suc
                    ; axiom₁ = {!!} 
                    ; axiom₂ = {!!} 
                    ; axiom₃ = {!!} 
                    }

