data Nat = Zero | Suc Nat 
	deriving Show 

fix :: (t -> t) -> t 
fix f = f (fix f)  

isZero :: Nat -> Bool 
isZero Zero = True 
isZero _    = False 

pred' :: Nat -> Nat 
pred' Zero   = Zero 
pred' (Suc x)  = x 

toInt :: Nat -> Integer 
toInt Zero    = 0 
toInt (Suc x) = (toInt x) + 1  

plus :: Nat -> Nat -> Nat 
plus = fix $ \p x y -> if isZero x then y else Suc (p (pred' x) y)    

times :: Nat -> Nat -> Nat 
times = fix $ \t x y -> if isZero x then x else ((t (pred' x) y) `plus` y)   

--1a 
factorial :: Nat -> Nat 
factorial = fix $ \f x -> if isZero x then Suc x else times x (f (pred' x))   

--1b 
ack :: Nat -> Nat -> Nat 
ack = fix $ \a m n -> if isZero m then Suc n else if isZero n then a (pred' m) (Suc Zero)  
	else a (pred' m) (a m (pred' n))

--1c 
infinity :: Nat 
infinity = fix Suc 
 
