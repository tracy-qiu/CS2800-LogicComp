-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11



-- read 20-undecidability.pdf 

-------------------------------------
-- THE HARDNESS OF PROVING THEOREMS
-------------------------------------

------------------------------
-- Fermat's Last Theorem
------------------------------

/- 
some of the claims that we can write in LEAN are easy to write, but very hard to prove! Fermat's "last theorem" was stated by Fermat in 1637 and was finally proved in 1994! that's more than 350 years later (https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem). no wonder it is hard to build tools to prove (or disprove) such statements automatically. 

but we can easily state the theorem in LEAN's logic (if the ^ (exponent) operator is not recognized in your LEAN installation, use our exponent function from previous lectures):
-/

def fermats_last_theorem := 
    ∀ n : ℕ, n > 2 → ¬ ∃ a b c : ℕ, a>0 ∧ b>0 ∧ c>0 ∧ a^n + b^n = c^n


/-
we can also write Fermat's last theorem without the ∃ quantifier:
-/
def fermats_last_theorem_without_exists := 
    ∀ n : ℕ, n > 2 → ∀ a b c : ℕ, a>0 ∧ b>0 ∧ c>0 → a^n + b^n ≠ c^n     

#check fermats_last_theorem_without_exists -- it's a Prop 

/-
we will not deal with equivalences in first-order logic, but note the following:

¬ ∃ x, P x
is equivalent to
∀ x, ¬ P x

and 

¬ ( (P x) ∧ (P y) )
is equivalent to
(¬ (P x)) ∨ (¬ (P y)) 
which is equivalent to
(P x) → (¬ (P y)) 

-/




-------------------------------------
-- DECIDABILITY and if-then-else 
-------------------------------------

/-
in the slides (20-undecidability.pdf) we talked about decidability and undecidability. now some things in LEAN should make more sense. for example, the type of if-then-else (ite) says that in order for an if-then-else expression to type-check, the condition c of the if-then-else must be decidable:
-/

#check ite 

/-
this is a reasonable restriction. LEAN's language is so expressive, that it allows us to write pretty much ANY Prop that we want. if we could also pass any Prop as the condition of an if-then-else, without any restrictions, we could write things like that:
-/

#check if (fermats_last_theorem) then 1 else 0  

/-
but the above expression does not type-check in LEAN. LEAN tells us that it cannot determine whether fermats_last_theorem is decidable.  

if the above expression was a valid LEAN expression, then in principle we could evaluate it, which means that we could ask LEAN to check whether Fermat's last theorem holds: if yes, then LEAN should return 1, else it should return 0! 
-/





------------------------------------------
-- weekday revisited (optional material)
------------------------------------------

/-
consider the weekday type we defined earlier:
-/

#check weekday 
open weekday 

-- we can prove things like that:
example: sunday ≠ monday := begin intro h, trivial, end 

-- but this expression yields a type error similar to the one above:
#check (if (sunday = monday) then 0 else 1)  

/-
to avoid this problem, we can do the following:
-/

@[derive decidable_eq]
inductive weekdaydec : Type
| sundaydec : weekdaydec
| mondaydec : weekdaydec
| tuesdaydec : weekdaydec
| wednesdaydec : weekdaydec
| thursdaydec : weekdaydec
| fridaydec : weekdaydec
| saturdaydec : weekdaydec

open weekdaydec 

-- now equality/inequality is decidable for this type 
#check (if (sundaydec = mondaydec) then 0 else 1)  
#reduce (if (sundaydec = mondaydec) then 0 else 1)  
#reduce (if (sundaydec ≠ mondaydec) then 0 else 1)  

/-
Here are some references (thanks to Yuhao!):

    - This is a series of tutorials on decidable type class: https://exlean.org/decidable-propositions-i/
    
    - 10.4 is the section of decidable: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html
    
    - Usage examples in mathlib basic: https://github.com/leanprover-community/mathlib/blob/master/src/logic/basic.lean
-/


