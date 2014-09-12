import Prelude hiding (pred) 

data Nat = Zero | Suc Nat 
	deriving Show

fix :: (t -> t) ->  t 
fix f = f (fix f) 

isZero :: Nat -> Bool 
isZero Zero = True 
isZero _    = False 

pred :: Nat -> Nat 
pred Zero    = Zero 
pred (Suc n) = n 

natToInt :: Nat -> Integer 
natToInt Zero    = 0 
natToInt (Suc n) = 1 + natToInt n 

plus :: Nat -> Nat -> Nat  
plus n m = natrec m (\x y -> Suc y) n 

--Exercise 2d 
natrec :: t -> (Nat -> t -> t) -> Nat -> t 
natrec = fix $ \nr p f n  ->  if isZero n then p else f (pred n) (nr p f (pred n))   







