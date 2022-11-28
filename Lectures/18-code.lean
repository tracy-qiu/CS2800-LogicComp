-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 
import .ourlibrary12
import .ourlibrary14  
import .ourlibrary16 




/- some hints for hwk09 and in general

1. do not do nested inductions

2. try to get to a point where you can use the induction hypothesis, and use it.

3. try to understand what it is that you are proving, at each given step: this is sometimes difficult to see with standard LEAN notation of function calls, e.g., plus x (plus y z). you can write things down on paper using more humanly readable notation, e.g., x + (y + z). you can also use LEAN's notation feature to do that (see 17-code.lean and this file) if you think it's helpful. (if not, you don't have to use notation!)

4. writing things down on paper often helps in discovering lemmas. LEAN's notation might help so that you don't have to write things down yourselves. 

5. it's often easier to prove a more general lemma than a more specialized one, e.g., if you are trying to prove something about 0, maybe you can generalize it to any x? it may be easier to prove for any x, than just for 0!

6. if you have problems doing rw with arguments, do first a "have" and then the rw. this breaks up the two tasks of (1) calling the lemma with the right arguments, and (2) rewriting based on the lemma. for example:

  - instead of doing this:

    rw (app_assoc (app L1 L2) L3 L4),

  - you can do this:

    have h42 := app_assoc (app L1 L2) L3 L4,  -- first i instantiate the lemma
    rw h42, -- then i rewrite based on the equality of the lemma 

-/



-------------------------------------------------------
-- delaying introductions and choosing the induction variable revisited
--------------------------------------------------------

section local_notation
local notation x + y := plus x y 
local notation x ≤ y := leq x y = tt   


/- sometimes delaying introductions may lead to us choosing the wrong variable to induct on. for example: 
-/

-- lemma discoveries, proofs left as homework:

lemma leq_zero_plus_right: ∀ x y : ℕ, 0 ≤ y ↔ x ≤ x + y
:= sorry 

lemma not_succ_leq: ∀ x : ℕ, ¬ nat.succ x ≤ x
:= sorry 

lemma leq_plus_left_failed: 
    ∀ (x y z : ℕ), x ≤ y ↔ (z + x ≤ z + y)
:= begin
  intro,
  -- let's delay the intros of y and z and induct on x:
  induction x with w ih,
  {
    intros,
    rw plus_x_zero,
    -- lemma discovery 
    rw leq_zero_plus_right,
  },
  {
    intros,
    cases y with u,
    {
      rw plus_x_zero,
      rw leq,
      rw plus_commut,
      rw plus,
      cases w with v,
      {
        rw plus,
        split,
        {
          intro h,
          trivial,
        },
        {
          intro h,
          have h2 := not_succ_leq z,
          trivial,
        }
      },
      sorry, -- giving up ... 
    }, 
    sorry, -- giving up ... 
  }
end

-- if we induct on z, the proof becomes very easy! 
lemma leq_plus_left: 
    ∀ (x y z : ℕ), x ≤ y ↔ (z + x ≤ z + y)
:= begin
  intros,
  induction z with w ih,
  {
    rw plus,
    rw plus,
  },
  {
    rw plus,
    rw plus,
    rw leq,
    exact ih,
  },
end

/- NOTE:
the problem is not delaying introductions per se. the problem is the choice of the induction variable. we could delay the intros of x and y, and still complete the proof easily by induction on z: 
-/
example:     ∀ (x y z : ℕ), x ≤ y ↔ (z + x ≤ z + y)
:= begin
    intro,
    intro,
    intro,
    revert x,
    revert y,
    induction z with w ih,
    {
        intros,
        rw plus,
        rw plus,
    },
    {
        intros,
        rw plus,
        rw plus,
        have h := ih y x,
        rw leq,
        exact h,
    }
end


end local_notation
















----------------------------------------------------
-- nat.succ vs +1
----------------------------------------------------


/- sometimes (but maybe not in all installations!), LEAN treats (x+1) as (nat.succ x). for example, we could write the definition of plus in multiple ways:
-/

#check plus -- this is the one we have with nat.succ everywhere:
/-
def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  
-/

-- using x+1 instead of nat.succ x in the pattern: 
def plus1 : nat -> nat -> nat 
    | 0 y := y 
    | (x+1) y := nat.succ (plus1 x y) 

-- using +1 instead of nat.succ everywhere: 
def plus2 : nat -> nat -> nat 
    | 0 y := y 
    | (x+1) y := (plus2 x y) + 1

#print plus 
#print plus._main 
#print plus1._main -- internal representation seems identical to that of plus
#print plus2._main 

theorem plus_equiv_plus1: ∀ x y : ℕ, plus x y = plus1 x y 
:= begin 
    intros,
    induction x with z ih,
    refl,
    dunfold plus,
    dunfold plus1,
    rw ih,
end 

theorem plus_equiv_plus2: ∀ x y : ℕ, plus x y = plus2 x y 
:= begin 
    intros,
    induction x with z ih,
    refl,
    dunfold plus,
    dunfold plus2,
    rw ih,
end 


section local_plus_notation
local notation x + y := plus x y 

-- however, when we are within the notation section, using (x+1) in the pattern no longer works:
def plus3 : nat -> nat -> nat 
    | 0 y := y 
    | (x+1) y := nat.succ (plus3 x y) 
-- and the reason is that now "x+1" means "plus x 1" ! 

end local_plus_notation


-- and this of course is something we cannot do:
def plus4 : nat -> nat -> nat 
    | 0 y := y 
    | (plus x 1) y := nat.succ (plus4 x y) 

