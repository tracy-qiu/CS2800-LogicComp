-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary16


--------------------------------
-- MEASURE FUNCTIONS CONTINUED 
--------------------------------

/-
what is a measure function for app?

def app : list ℕ → list ℕ → list ℕ 
  | [] L := L
  | (x :: L1) L2 := x :: (app L1 L2)

-/

def m_app : list ℕ → list ℕ → ℕ := fun L1 L2, len L1 

lemma ltb_succ: ∀ x : ℕ,  ltb x (nat.succ x) = tt 
:= begin
    intro,
    induction x with z ih,
    refl,
    rw ltb,
    assumption,
end

/-
To show that m_app is a valid measure function for app we have to show that it decreases on every recursive call of app, under the conditions that led to that call.

app has just one recursive call, so we have to show:
-/
theorem m_app_decreases: forall (L1 L2 : list ℕ) (x : ℕ),
  ltb (m_app L1 L2) (m_app (x :: L1) L2) = tt 
:= begin
  intros,
  dunfold m_app,  -- gets rid of the lambdas 
  rw len,
--  rw ltb_succ (len L1),
  have h := ltb_succ (len L1),
  assumption,
end

/-
are there other possible measure functions we could use for app? for example, could we use this function?
-/

def m2_app: list ℕ → list ℕ → ℕ 
  | [] _ := 0 
  | (x :: L1) L2 := nat.succ (m2_app L1 L2) 

/- 
m2_app can be used as a measure function for app, BUT: m2_app is itself recursive, and in order to have a complete termination argument, we need to ensure that m2_app itself terminates! how? we should find a measure function for m2_app itself! if that measure function is itself recursive, we need to find another measure function for it, and so on. at some point, we need to stop, and come up with a measure function which is NOT recursive!
-/


/- WAIT A MINUTE ... what about termination of len? 

m_app is not recursive, but it calls len. how do we know that len itself terminates? we don't. len is iself recursive, so if we wanted to prove that it terminates, we would have to come up with a measure function for len. instead, we just _assume_ that len terminates. we take this to be an axiom. 

measure functions are only one way to prove termination, but it is not the only way. the termination of len is ensured by the way the inductive data type is defined. any inductive data type gives rise to a so-called _well-founded relation_ which is a relation that cannot have an infinite decreasing chain. we don't want to enter into a discussion of well-founded relations and type theory here, but basically inductive data types are more general than natural numbers. and measure functions use the ordering of natural numbers, so measure functions can be seen as a "poor man's" way of proving termination. it's effective in many cases, but not all cases. and yes, it relies on taking some things for granted, i.e., as axioms, such as the termination of len. 
-/



----------------------------------------
-- MEASURE FUNCTIONS: DEFINITION
----------------------------------------

/-

A function m is a valid measure function for another function f if all conditions below are satisfied:

  1. m has exactly the same input arguments/types as f

  2. The output of m is a  nat

  3. m is terminating (or "obviously terminating", like len)

  4. For EVERY recursive call to f, if we call m with the same arguments as f on that recursive call, and under the conditions that lead to that recursive call, then m decreases.

Notice that (4) says "on EVERY recursive call". Each recursive call results in a separate decreasing measure proof obligation. So, there are as many decreasing measure proof obligations, as there are recursive calls. 

We will soon see what "under the conditions that lead to the recursive call" means. 

-/

----------------------------------------
-- MEASURE FUNCTIONS: MORE EXAMPLES
----------------------------------------


/-  FOR EACH FUNCTION f GIVEN BELOW, DO THE FOLLOWING:

1. what is a measure function for f?

2. what are the decreasing measure proof obligations for your measure function?

3. prove these decreasing measure proof obligations that you came up with. 

-/

------------------------------------------------
#check rev 

/- ungraded quiz: what is a measure function for rev?

is it identical to m_app? 

def rev : list nat -> list nat 
  | [] := []
  | (a :: L) := app (rev L) [a] 

-/

-- ANSWER: m_rev is similar (but not identical! why?) to m_app:

-- the signatures of m_rev and m_app are different:
def m_rev : list ℕ → ℕ := fun L, len L 



/-
what are the decreasing measure proof obligations for m_rev?

To show that m_rev is a valid measure function for rev we have to show that it decreases on every recursive call of rev, under the conditions that led to that call.

rev has just one recursive call, so we have to show:
-/

-- we use notation so that we can write "<" for our ltb:
section local_notation
local notation (name := less_than) x < y := ltb x y = tt   

theorem m_rev_decreases: forall (L : list ℕ) (a : ℕ),
  (m_rev L) < (m_rev (a :: L)) 
:= begin
  intros,
  unfold m_rev,
  rw len,
  have h := ltb_succ (len L),
  assumption,
end


------------------------------------------------
#check plus 

/- ungraded quiz: what is a measure function for plus?

def plus : nat -> nat -> nat 
    | 0 y := y 
    | (nat.succ x) y := nat.succ (plus x y)

-/

-- ANSWER: 

def m_plus : ℕ → ℕ → ℕ := fun x y, x 

/-
what are the decreasing measure proof obligations for m_plus?

To show that m_plus is a valid measure function for plus we have to show that it decreases on every recursive call of plus, under the conditions that led to that call.

plus has just one recursive call, so we have to show:
-/

theorem m_plus_decreases: forall x y : ℕ,
  (m_plus x y) < (m_plus (nat.succ x) y) 
:= begin
  intros,
  unfold m_plus,
  rw ltb_succ x,
end



-----------------------------------------------------------
-- DECREASING MEASURE PROOF OBLIGATIONS
-----------------------------------------------------------

/- we call "decreasing measure proof obligations" all the theorems that we have to prove in order to show that a measure function is valid, i.e., in order to show that a measure function is decreasing on every recursive call. 

now, recall from the definition of measure function:

"On every recursive call to f, if we call m with the same arguments as f on that recursive call, and under the conditions that lead to that recursive call, then m decreases."

what exactly does "under the conditions that lead to that recursive call" mean?

let's illustrate this with an example. recall the sumall function:
-/

def sumall : ℕ → ℕ 
    | 0 := 0
    | (nat.succ n) := (nat.succ n) + (sumall n)
 

-- now consider an alternative definition of the function sumall:


-- x-y now means (minus x y)
local notation (name := minus ) x - y := minus x y 
#check minus 
#eval 3 - 2 
#eval 3 - 4 

def sumall_alt : ℕ → ℕ 
    | n := if (n = 0) then 0 else n + (sumall_alt (n-1))  

/- this definition seems perfectly OK (in fact, this is how you would define this function in many programming languages, including for example, ACL2s). but LEAN doesn't like it, because it cannot figure out it terminates. can we prove that it terminates using measure functions? and what would the measure decreasing proof obligations be in this case?

first, the measure function seems pretty obvious. it's the identity function on nats:
-/

def m_sumall_alt : ℕ → ℕ := λ n : ℕ, n 

/- what about the decreasing measure proof obligations? there's only one recursive call, so there will be only one decreasing measure proof obligation (we will see soon examples with multiple decreasing measure proof obligations). but notice that if we write the decreasing measure proof obligation in this way (after expanding the definition of m_sumall_alt):

  ∀ n : ℕ, n-1 < n

then we will _not_ be able to prove it. why? 
-/





























/-
ANSWER: it does NOT hold for n = 0 !
-/

/-
here's where the phrase "under the conditions that lead to that call" comes in. the recursive call (sumall (n-1)) does not occur in all cases. it only occurs in the _else_ case of the if-then-else. and that _else_ case only happens when the condition of the if-then-else is false, i.e., only when (n ≠ 0). this is the "condition that leads to this call". we should include this condition as an assumption to our descreasing measure proof obligation. so our measure decreasing proof obligation becomes:

  ∀ n : ℕ, n ≠ 0 → n-1 < n 

we can easily prove the above theorem with the help of some simple lemmas:
-/

theorem m_sumall_alt_decreases: 
  ∀ n : ℕ, n ≠ 0 → m_sumall_alt (n-1) < m_sumall_alt n 
:= begin
  intro,
  intro h,
  dunfold m_sumall_alt,
  -- interesting: does not need induction! 
  cases n with x,
  {
    trivial,
  },
  {
    dunfold minus,
    cases x with y,
    refl,
    dunfold minus,
    rw ltb_succ,
  }
end




-----------------------------------------------------------
-- MULTIPLE DECREASING MEASURE PROOF OBLIGATIONS
-----------------------------------------------------------

/-
consider the Fibonacci function that we defined earlier:
-/

def fib : ℕ → ℕ 
    | 0 := 0
    | 1 := 1
    | (nat.succ (nat.succ n)) := (fib n) + (fib (nat.succ n))

/-
this function has one recursive case (the 3rd one) with TWO recursive calls. we need to prove that the measure function decreases on EACH recursive call. therefore, we will have TWO decreasing measure proof obligations for this function. 

first, we need to devise a measure function. ungraded quiz: which one?
-/

def m_fib : ℕ → ℕ := fun n, n 

/-
now we have two decreasing measure proof obligations:
-/

theorem m_fib_decreases_call1: ∀ n : ℕ, 
  m_fib n < m_fib (nat.succ (nat.succ n)) 
:= begin
  intro,
  unfold m_fib,
  induction n with x ih,
  refl,
  rw ltb,
  assumption,
end

theorem m_fib_decreases_call2: ∀ n : ℕ, 
  m_fib (nat.succ n) < m_fib (nat.succ (nat.succ n)) 
:= begin
  intro,
  unfold m_fib,
  induction n with x ih,
  refl,
  rw ltb,
  assumption,
end

lemma ltb_plus_right : ∀ (x y z : ℕ), x < y → x + z < y + z
:= begin 
  intros,
  induction z with w ih, 
  {
    rw plus_x_zero, 
    exact a, 
  },
  {

  }
end 

lemma x_ltb_y_plus_z : ∀ (x y z : ℕ), ltb x y = tt → ltb x (plus y z) = tt 
-- lemma x_ltb_y_plus_z : ∀ (x y z : ℕ), x < y → x < y + z 
:= begin 
  intro x, 
  induction x with w ih, 
  {
    intros y z,
    intro h,  
    cases y with h2, 
    {
      rw ltb at h, 
      trivial,
    },
    rw plus, 
    rw ltb, 
  },
  {
    intros y z, 
    intro h, 

  }
end 


/- 
in general, a recursive function may have (1) multiple recursive cases, and (2) multiple recursive calls on each recursive case. each recursive call generates a different decreasing measure proof obligation! so if there are N cases for example, and case i has M_i recursive calls, then there will be M_1+M_2+...+M_N decreasing measure proof obligations. 
-/

end local_notation

def app_t4 : list ℕ → list ℕ → list ℕ → list ℕ 
  | [] [] acc := acc 
  | [] (b :: L) acc := app_t4 [] L (b :: acc)
  | (a :: L) [] acc := app_t4 [] (a:: L) acc
  | (a :: L1) (b :: L2) acc := app_t4 (a :: L1) [] (app_t4 acc [] (b:: L2))

def m4 : list ℕ → list ℕ → list ℕ → ℕ := λ L1 L2 L3, 0 

lemma m4_dmpo1: ∀ L acc : list ℕ, ∀ b : ℕ,
  (m4 [] L (b :: acc)) < (m4 [] (b :: L) acc)
  := sorry 

lemma m4_dmpo2: ∀ L acc : list ℕ, ∀ a : ℕ,
  (m4 [] (a :: L) acc ) < (m4 (a :: L) [] acc)
  := sorry 

lemma m4_dmpo3 : ∀ L2 L1 acc : list ℕ, ∀ b a : ℕ,
  (m4 acc [] (b:: L2)) < (m4 (a :: L1) (b :: L2) acc)
  := sorry 

lemma m4_dmpo4 : ∀ L1 L2 acc : list ℕ, ∀ a b: ℕ,
  (m4 (a :: L1) [] (app_t4 acc [] (b :: L2)) ) < (m4 (a :: L1) (b :: L2) acc)
  := sorry