module Exercise3 where 

--Exercise 3a 
{-
  λ g f x . g x (f x). 
  
  S = λ X₀ . λ X₁ . λ X₂ . λ g : (X₂ -> X₁) . λ f : (X₂ -> X₁ -> X₀) . λ x : X₂ . g x (f x)    
  S : ∀ X₀ . ∀ X₁ . ∀ X₂. (X₂ -> X₁) -> (X₂ -> X₁ -> X₀) -> X₂ -> X₀
-}

--Exercise 3b 
{-
  Sexp X = ∀ R. (R -> R -> R) -> (X -> R) -> R -> R 
-}

--Exercise 3c 
{-
  Nil = λ X. (λ R . λ c : (R -> R -> R) . λ a : (X -> R) . λ n : R . n) as Sexp X 
  Nil : ∀ X. Sexp X 

  Cons = λ X. λ lc : Sexp X . λ rc : Sexp X . 
         (λ R . λ c : (R -> R -> R) . λ a : (X -> R) . λ n : R . c (lc [R] c a n) (rc [R] c a n)) as Sexp X  
  Cons : ∀ X. Sexp X -> Sexp X -> Sexp X   
-}

--Exercise 3d 
{-
  --Assuming that I have a type constructor Bool. The definition can be found in Pierce.
  
  isNil = λ X . λ s : Sexp X . l [Bool] (λ a : Sexp X . λ b : Sexp X . λ tl : Bool . false) (λ c : X . λ tl : Bool . false) true     
  isNil : ∀ X. Sexp X -> Bool 

-}

