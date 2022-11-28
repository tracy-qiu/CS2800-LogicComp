-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 
import .ourlibrary12
import .ourlibrary14  
import .ourlibrary16 

/- a political thought:

Dear students,

You worry about exams and grades, and that's normal. 

I'm afraid your generation will face much more serious challenges. The two biggest ones being (1) environmental collapse, and (2) fascism. (I'm being optimistic and ignoring WW3, nuclear and biological weapons, etc.)

I wish you, and the rest of us, good luck!

Stavros

PS. Logic and CS have a lot to contribute to the political discourse. (If you want to discuss this more, contact me.) For example, one big lesson of logic and CS is that before we argue about something, we had better define that something:  
-/

-- "We hold these truths to be self-evident, that all men are created equal, ..."
-- does not type-check because things are undefined: 
-- example: ∀ x y : Man, CreatedEqual x y -- what is "Man"? what is "CreatedEqual"? 




------------------------------------------
-- delaying introductions practice!!!
------------------------------------------


#check leq 
#check len 

/-
formalize and prove in LEAN the following statement:

    - for all x y nats, if x is leq than y, then x is leq than y+1 (use our plus)

-/


-- for all x y nats, if x is leq than y, then x is leq than y+1 (use our plus):

-- monolithic proof:
example: ∀ x y : ℕ, leq x y = tt → leq x (plus y 1) = tt 
:= begin
    intro,
    -- delay intro of y!
    induction x with z ih,
    {
        intro,
        intro h,
        refl,
    },
    intro,
    intro h,
    cases y with w ,
    {
        dunfold leq at h,
        trivial,
    },
    {
        dunfold leq at h,
        dunfold plus,
        dunfold leq,
        have h1 := ih w h,
        assumption,
    },
end

-- using plus_commut and a lemma:
lemma leq_x_y_succ: 
    ∀ x y : ℕ, leq x y = tt → leq x (nat.succ y) = tt
:= begin
    intro,
    -- delay intro of y!
    induction x with z ih,
    {
        intro,
        intro h,
        refl,
    },
    {
        intro,
        intro h,
        rw leq,
        cases y with w,
        {
            rw leq at h,
            trivial,
        },
        {
            rw leq at h,
            have h2 := ih w h,
            exact h2,
        }
    },
end

example: ∀ x y : ℕ, leq x y = tt → leq x (plus y 1) = tt 
:= begin
    intro,
    intro,
    rw plus_commut,
    dunfold plus,
    have h := leq_x_y_succ x y ,
    exact h,
end


-- QUIZ TIME! 



/-      REVIEW HWK 07 
-/






----------------------------------------------------
-- HOW NOT TO LOSE YOUR BOOL CASES
----------------------------------------------------

/-
as we saw a while back already, we can do "cases" on any inductive data type. for example, we can do cases on bools:
-/

example: ∀ b : bool, b = tt ∨ b = ff 
:= begin
    intro,
    cases b,
    {
        right,
        refl,
    },
    {
        left,
        refl,
    },
end

/-
if a function f returns a bool, then we know that (f x) = tt or (f x) = ff, for any x. we can use that in proofs. sometimes, doing just "cases (f x)" suffices:
-/

example: ∀ f : ℕ → bool, ∀ x : ℕ, f x = tt ∨ f x = ff 
:= begin
    intros,
    cases (f x), -- (f x) is a bool, so we can do cases on it! 
    {
        -- here we "lost" the hypothesis that (f x) = ff 
        right,
        refl,
    },
    {
        -- here we "lost" the hypothesis that (f x) = tt 
        left,
        refl,
    },
end

/-
but notice that the above method "loses" the two cases in the sense that it does not keep them in the hypotheses. in the example above, this was not a problem. but in other situations it might be a problem. for example:
-/

#check leq 

def sortedb : list ℕ → bool 
  | [] := tt 
  | [_] := tt 
  | (x :: (y :: L)) := (leq x y) && (sortedb (y :: L)) 
--

lemma not_leq_leq: ∀ x y : ℕ, leq x y = ff → leq y x = tt 
:= sorry -- prove this at home! 


example: ∀ x y : ℕ, sortedb [x,y] = tt ∨ sortedb [y,x] = tt 
:= begin
    intros,
    dunfold sortedb,
    cases (leq x y),
    {
        -- here leq x y = ff, but we lost this hypothesis!
        right,
        -- we know that leq y x must be tt, because leq x y = ff, but since we lost the latter hypothesis, we are stuck... 
        sorry,
    },
    {
        -- this part is fine:
        left,
        refl,
    },
end

/- what to do so that we don't "lose our cases"? we could use classical.em, but that's an overkill (and also non-constructive):
-/
example: ∀ x y : ℕ, sortedb [x,y] = tt ∨ sortedb [y,x] = tt 
:= begin
    intros,
    dunfold sortedb,
    have h := classical.em (leq x y = tt),
    cases h,
    {
        left,
        rw h,
        refl,
    },
    {
        right,
        have h1 : leq x y = ff := begin
            cases (leq x y),
            refl,
            trivial,
        end,
        have h2 := not_leq_leq x y h1,
        rw h2,
        refl,        
    },
end

/- instead we can do this constructive proof: 
-/
example: ∀ x y : ℕ, sortedb [x,y] = tt ∨ sortedb [y,x] = tt 
:= begin
    intros,
    dunfold sortedb,
    have h : (leq x y = tt) ∨ (leq x y = ff) := begin
        cases (leq x y) ,
        right, refl,
        left, refl,
    end,
    cases h,
    -- notice that now the cases are "saved" in h 
    {
        left,
        rw h,
        refl,
    },
    {
        right,
        have h2 := not_leq_leq x y h,
        rw h2,
        refl,        
    },
end




---------------------------
-- the tactic _clear_
---------------------------

/-
sometimes we have hypotheses in our proof state that we don't need, or that we no longer need. we can remove those with the tactic "clear". this can help reduce clutter and make our proof state more readable. on the other hand, it also creates the risk of removing a hypothesis that turns out to be necessary. 
-/

-- we saw this in 12-code.lean:
def nat_induction := ∀ P : ℕ → Prop, 
    (P 0) → 
    (∀ n : ℕ, (P n) → (P (nat.succ n))) → 
    (∀ n : ℕ, P n)  

example: nat_induction → (∀ x : ℕ, plus x 0 = x)
:= begin
    intro h1,
    dunfold nat_induction at h1,
    have h2 := h1 (λ x : ℕ, plus x 0 = x),
    clear h1, -- h1 used in modus ponens; no longer needed 
    have fun1 : ((λ (x : ℕ), plus x 0 = x) 0) = (plus 0 0 = 0) := begin refl, end,
    rw fun1 at h2,
    have h3 : plus 0 0 = 0 := begin
        refl,
    end,
    have h4 := h2 h3,
    clear h2,
    clear h3,
    have h5 : (∀ (n : ℕ), (λ (x : ℕ), plus x 0 = x) n → (λ (x : ℕ), plus x 0 = x) (nat.succ n)) := begin
        intro,
        intro g1,
        dunfold plus,
        rw g1,
    end,
    have h6 := h4 h5,
    assumption,
end






----------------------------------------------------
-- NOTATION
----------------------------------------------------

/- LEAN allows us to define our own notation. this makes things more readable, but also somewhat implicit, so we must be careful with its usage. 
-/

section local_plus_notation

#eval plus 1 3      -- our addition on nats 
#eval nat.add 1 3   -- LEAN's addition on nats 
#eval 1+3           -- at this point, LEAN's addition still
#print notation +   

-- we now redefine + to mean our plus: 
local notation x + y := plus x y 
#eval 1+3  -- i don't really know which + is used here, but i can check:
#print notation +     -- now + denotes our plus function 


-- now we can state some theorems in a more concise and standard manner:

lemma plus_x_succ_y_with_notation: 
    ∀ x y : ℕ, nat.succ (x + y) = x + (nat.succ y) 
:= begin
    intros,
    induction x with z ih,
    {
        refl,
    },
    {
        dunfold plus,  -- notice that this works, because "+" is the function "plus" !
        rw ih,
    }
end

theorem plus_commutative_with_notation: 
    ∀ x y : ℕ, x + y = y + x 
:= begin
    intros,
    induction x with w ih,
    {
        dunfold plus,  -- notice that this works, because "+" is the function "plus" !
        rw plus_x_zero,
    },
    {
        dunfold plus,  -- notice that this works, because "+" is the function "plus" !
        rw ih,
        rw plus_x_succ_y_with_notation,
    }
end


/- when you use notation, make sure you don't confuse which symbol stands for which function! sometimes we don't know whether "+" refers to our own defined "plus" function, or to the built-in LEAN function. we need to be careful. ALWAYS enclose your own notation within _section blabla ... end blabla_ . 
-/

end local_plus_notation

/- once we exit the local notation section local_plus_notation, "+" becomes again LEAN's addition notation, and we cannot treat it anymore like our plus function:
-/

theorem plus_commutative_but_this_is_not_our_plus: 
    ∀ x y : ℕ, x + y = y + x 
:= begin
    intros,
    induction x with w ih,
    {
        dunfold plus,  -- this is not our plus! 
    },
    {
        sorry,
    }
end

