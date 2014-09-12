module Exercise2 where 

data ℕ : Set where 
  zero : ℕ 
  suc  : ℕ -> ℕ  

{-# BUILTIN NATURAL ℕ    #-}
{-# BUILTIN ZERO    zero #-}
{-# BUILTIN SUC     suc  #-}

data Bool : Set where 
  true false : Bool

if_then_else : {A : Set} -> Bool -> A -> A -> A 
if true then x else _ = x 
if _ then _ else y    = y     

natrec : {C : Set} -> C -> (ℕ -> C -> C) -> ℕ -> C 
natrec  p f zero    = p 
natrec  p f (suc n) = f n (natrec p f n)   

-- Exercise 2a 
----------------------------------------------------------
isZero : ℕ -> Bool 
isZero = λ x → natrec true (λ _ _ → false) x

pred : ℕ -> ℕ 
pred x = natrec zero (λ y _ → y) x     

----------------------------------------------------------

_+_ : ℕ -> ℕ -> ℕ 
n + m = natrec m (λ x y -> suc y) n 

_*_ : ℕ -> ℕ -> ℕ 
n * m = natrec zero (λ x x' → x' + m) n  

-- Exercise 2b
----------------------------------------------------------
factorial : ℕ -> ℕ 
factorial x = natrec (suc zero) (λ y z -> (suc y) * z) x 

----------------------------------------------------------

_-_ : ℕ -> ℕ -> ℕ 
n - m = natrec n (λ x y -> pred y) m 

min : ℕ -> ℕ -> ℕ 
min m n = if (isZero (m - n)) then m else n  

test : ℕ -> ℕ 
test zero = 1
test 2    = 3
test 4    = 4 
test 5    = 2
test _    = 11  

-- Exercise 2c
----------------------------------------------------------
boundemin : (ℕ -> ℕ) -> ℕ -> ℕ 
boundemin f x = if (isZero x) then (f x) else (natrec zero (λ y z → if isZero z then (min (f (suc y)) (f z)) else (min (f (suc y)) z)) x)   
----------------------------------------------------------

