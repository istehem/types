
module Exercise4 where 

data Nat = Zero | Suc Nat
	deriving Show

isZero :: Nat -> Bool 
isZero Zero = True
isZero _    = False 

add :: Nat -> Nat -> Nat 
add Zero m    = m
add n Zero    = n 
add (Suc n) (Suc m) = Suc (Suc (n `add` m))

pre :: Nat -> Nat 
pre Zero    = Zero 
pre (Suc n) = n 


add' :: Nat -> Nat -> Nat 
add' =  \x y -> if isZero x then y else (if isZero y then x else Suc (Suc (add' (pre x) (pre y))))
