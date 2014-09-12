module Homework121004 where 

data LambdaTerm =   Var String 
				  | Lam String LambdaTerm  
				  | App LambdaTerm  LambdaTerm 
				deriving(Show, Eq)


isClosed :: LambdaTerm -> Bool 
isClosed t    =  isClosed' t == []  

isClosed' :: LambdaTerm -> [String] 
isClosed' (Var s)     = [s] 
isClosed' (Lam s t)   = filter (/=s) $ isClosed' t  
isClosed' (App t1 t2) = isClosed' t1 ++ isClosed' t2 

id' = isClosed (Var "x") 

testA = isClosed' $  Lam "x" (Lam "y" (App (App (Var "x") (Var "y")) (Var "z")))





   
