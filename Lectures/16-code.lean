-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 
import .ourlibrary14
import .ourlibraryite


----------------------------------------------------
-- SIMPLIFYING if-then-else: itetrue and itefalse
----------------------------------------------------

/- when we know that some Prop p is true, we should be able to simplify (if p then x else y) to x. and if we know that p is false, we should be able to simplify the above if-then-else to y. 

we can use the lemmas itetrue and itefalse to do that: 
-/

#check itetrue 
#check itefalse 

example: ∀ x : ℕ, ∀ s1 s2 : string, 
    (if (x = x) then s1 else s2) = s1 
:= begin
    intros,
    have h1 : x = x := begin refl, end, 
    have h2 := itetrue (x = x) h1 string s1 s2 ,
    exact h2,
end

example: ∀ x y : ℕ, ∀ L : list ℕ, 
    (x ≠ y) → (x :: (if (x = y) then L else [])) = [x]  
:= begin
    intros x y L h1,
    have h2 := itefalse (x = y) h1 (list ℕ) L [] ,
    rw h2,
end




----------------------------------------------------
-- INDUCTION CONTINUED
----------------------------------------------------


---------------------------------
-- INDUCTION practice!!!
---------------------------------


#check leq  
#check len 

/-
formalize and prove in LEAN the following statements:

    - for all x nat, x is leb than x+1 (use our plus)

    - for all lists of nats L, the len of L is leb the len of (x :: L), for any x nat 

-/
-- ANSWERS:

-- for all x nat, x is leb than x+1 (use our plus):
example: ∀ x : ℕ, leq x (plus x 1) = tt 
:= begin
    intro,
    induction x with y ih,
    refl,
    dunfold plus,
    dunfold leq,
    exact ih,
end


-- helper lemma for below:
lemma leb_x_succ: ∀ x : ℕ, leq x (nat.succ x) = tt 
:= begin
    intro,
    induction x with y ih,
    refl,
    dunfold leq,
    exact ih,
end

-- for all lists of nats L, the len of L is leb the len of (x :: L), for any x nat 
example: ∀ L : list ℕ, ∀ x : ℕ, leq (len L) (len (x :: L)) = tt 
:= begin
    intros,
    dunfold len,
    -- lemma discovery 
    rw leb_x_succ,
end


----------------------------------------------------
-- DELAYING INTRODUCTIONS
----------------------------------------------------

#check double 

-- suppose we try to prove this:
theorem double_injective_1st_try: 
    ∀ x y : ℕ, double x = double y -> x = y 
:= begin
    intro,
    intro,
    intro h,
    induction x with z ih,
    {
        rw double at h,
        cases y,
        {
            refl,
        },
        {
            rw double at h,
            trivial, -- because the nat.succ of something cannot be 0 
        }
    },
    {
        rw double at h,
        -- now what? hypothesis "h" does not seem to match the assumption of the induction hypothesis. also the goal doesn't match the conclusion of the induction hypothesis. we could try _cases_ on y:
        cases y with w,
        {
            rw double at h,
            trivial,
        },
        {
            rw succeq,
            rw double at h,
            rw succeq at h,
            rw succeq at h,            
            -- now we have a simpler hypothesis "h", and a simpler goal, but now our induction hypothesis is more complicated! again, we can't seem to be able to use the induction hypothesis... we're stuck, we give up... 
            sorry,
        }
    }
end


-- what if we tried induction instead of cases for y in the induction step?
theorem double_injective_2nd_try: 
    ∀ x y : ℕ, double x = double y -> x = y 
:= begin
    intro,
    intro,
    intro h,
    induction x with z ih,
    { -- base case same as in double_injective_1st_try
        rw double at h,
        cases y,
        {
            refl,
        },
        {
            rw double at h,
            trivial, 
        }
    },
    {
        rw double at h,
        -- trying induction y here instead of cases y:
        induction y with w ih2,
        {
            rw double at h,
            trivial,
        },
        {
            rw succeq,
            rw double at h,
            rw succeq at h,
            rw succeq at h,
            -- it doesn't look like ih2 is helpful ... 
            sorry,
        }
    }
end

/-
the solution is to _delay_ the introduction of quantified variable y. doing so, we have a more general goal, and therefore a more powerful induction hypothesis. let's see how and why: 
-/

theorem double_injective: 
    ∀ x y : ℕ, double x = double y -> x = y 
:= begin
    intro, -- we only introduce x. we "delay" y !
    -- now our goal is more general, because it talks about "for all y": 
    induction x with z ih, -- we induct on x: observe the induction hypothesis! it also talks about "for all y". 
    {
        intro,  -- now we introduce y 
        intro h,
        cases y,
        {
            refl,
        },
        {
            unfold double at h,
            trivial,
        }
    },
    { -- now ih is much more powerful, because we can instantiate it with _any_ y!
        intro,
        intro h,
        rw double at h,
        cases y with w, -- notice that this has _no effect_ on ih! compare to the effect that this had on ih in the aborted proof of "double_injective_1st_try". in the latter, y was substituted. here, it's not substituted. why? because here y is a quantified variable. the induction hypothesis says "for ANY y, bla bla holds". earlier, the induction hypothesis said "for this particular y that we fixed, bla bla holds". 
        {
            trivial,
        },
        {
            rw succeq,
            rw double at h,
            rw succeq at h,
            rw succeq at h,
            have h := ih w h , 
            assumption,
        }
    },
end


/-
at this point you should stop and compare the goal and induction hypothesis in the proof state of double_injective_1st_try right after the 2nd "rw succeq at h", to those of double_injective at the same point. you will see that the goals are identical:

⊢ z = w

and hypothesis h is also the same in both proof states:

h : double z = double w

but the induction hypotheses are different:

ih : double z = double (nat.succ w) → z = nat.succ w,
vs
ih : ∀ (y : ℕ), double z = double y → z = y,

the ih with delayed y is much more powerful, because it works for any y!
-/





/-
in the proof of double_injective we were "lucky" to have the theorem stated as ∀ x y ..., and because of that, we could only introduce x, and delay the introduction of y. 

but what if the theorem were written as ∀ y x  ... ? would we still be able to prove it?

yes, in at least three ways: (1) using the tools we already know, doing induction on y instead of x, (2) again using the tools we already know, with the help of a lemma. (3) using a new tactic called "revert". we illustrate (1), (2) and (3) in turn:
-/

-- suppose the theorem was written like this:
theorem double_injective_y_x_method1: 
    ∀ y x : ℕ, double x = double y -> x = y 
-- method (1): induction on y instead of x: 
:= begin
    intro,
    induction y with z ih,
    {
        intro ,
        intro h,
        cases x with z,
        refl,
        dunfold double at h,
        trivial,
    },
    {
        intro,
        intro h,
        dunfold double at h,
        cases x with w,
        {
            dunfold double at h,
            trivial,
        },
        {
            dunfold double at h,
            rw succeq at h,
            rw succeq at h,
            have h2 := ih w h,
            rw h2,
        }
    },
end


theorem double_injective_y_x_method2: 
    ∀ y x : ℕ, double x = double y -> x = y 
-- method (2): first prove double_injective, then use it as a lemma
:= begin
    intros y x,
    have h := double_injective x y,
    assumption,
end


---------------------------
-- the tactic _revert_
---------------------------

theorem double_injective_y_x_revert: 
    ∀ y x : ℕ, double x = double y -> x = y 
-- method (3): use the tactic "revert"
:= begin
    intro, -- intro y
    intro, -- intro x
    revert y, -- put y back to the goal 
    /-
    now our proof state looks exactly like the state in the proof of double_injective, after the first "intro":
    1 goal
    x : ℕ
    ⊢ ∀ (y : ℕ), double x = double y → x = y
    so we could copy-paste the rest of the proof from there here.
    -/
    sorry, -- complete the proof!
end



/- NOTE:
we should NOT expect all three methods above to work in ALL situations. for example, method (1) works because the claim "double x = double y -> x = y" is essentially symmetric in x and y. so doing induction x or induction y makes no difference. if the claim we are trying to prove does not have this symmetry, we can use revert or lemmas. 
-/


------------------------------------------
-- delaying introductions practice!!!
------------------------------------------


#check leq 
#check len 

/-
formalize and prove in LEAN the following statement:

    - for all x y nats, if x is leb than y, then x is leb than y+1 (use our plus)

-/

... 


------------------------------
-- reverting implications 
------------------------------

-- revert can put hypotheses back into the goal too:
example : ∀ x : ℕ, x = 0 → x ≥ 0
:= begin
    intro,
    intro h,
    revert h,
    sorry,
end

/-
it now becomes apparent that the forall quantifier ∀ can be interpreted as an implication. meaning that when we say (∀ x : ℕ, P x) what we are essentially saying is (x : ℕ → P x) or "if x is some element of type nat, then (P x) is true". and because implication is also the same thing as a function (A → B can be seen as an implication, or as the type of functions from A to B!), now it becomes clear why lemmas that have types (∀ x:T, ...) take some x of type T as their first argument.

FOOD FOR THOUGHT: if the ∀ quantifier is essentially an implication, then what do you think the ∃ (exists) quantifier essentially is?
-/

