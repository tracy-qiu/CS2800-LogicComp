-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 5

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: ...
-/

/-
Technical instructions: same as in the last homework PLUS THE INSTRUCTIONS BELOW: 
-/

----------------------------- IMPORTANT !!! ------------------------------
/- 
when we say "prove this" we imply that you _can_ and _should_ complete the proof, using the tactics that we have seen so far. 

when we say "is the theorem below true? if so prove it, if not, exhibit a counterexample", there are two possible answers: either (1) "yes, it's true, and here's my proof in LEAN:" and you provide a complete proof in LEAN (no "sorry"s); or (2) "no, it's not true, and here's a counterexample:" and you provide a counterexample as a LEAN comment (you can also comment out the theorem so that it doesn't give LEAN errors). for example:

"is the theorem below true? if so prove it, if not, exhibit a counterexample:
theorem bla: ∀ P Q : Prop, P -> Q 
"
-- Answer:
No it is not true, because if P is true and Q is false, the implication P -> Q is false. The counterexample is P:=true, Q:=false. 

-/
--------------------------------------------------------------------------


/- HWK05-01: 
A. Construct the truth table for each of the following propositional logic formulas.
   Use alphabetical order for the variables in the formula, and create
   columns for all variables occurring in the formula AND for all
   intermediate subexpressions. For example, if your formula is

   (p → q) ∨ r

   your table should have 5 columns: for p, q, r, p → q, and (p → q) ∨ r .

   You can use 0 and 1, or F and T for false and true in your truth table. 

For each formula, you also have to:

B. Indicate if is satisfiable, unsatisfiable, valid, or falsifiable (exactly two of these characterizations will hold for each formula!).

C. Indicate how many assignments satisfy the formula (i.e., make the formula true).

D. Give another (different) formula which is equivalent to this formula. Any other equivalent formula would do. Remember: "true" and "false" (or "tt" and "ff") are formulas (Props or bools). 

E. Write a LEAN theorem stating that the original formula and the different formula that you provided in D are equivalent.
   This should _not_ be in a comment. Here we want LEAN code. Try to prove the theorem with Props. If you are able to, you are done. Otherwise, you should always be able to prove it with bools, so prove it with bools. If you prove it with Props, you don't have to prove it with bools. Even if you don't manage to prove it with Props, you should still include your incomplete proof with Props, properly ended with enough "sorry"s. 

you will NOT be penalized if the formula that you found in D cannot be proven equivalent to the original formula using Props, but there exists another equivalent formula that could be proven equivalent using Props. 

you WILL be penalized if the formula that you gave in D is NOT equivalent to the original formula. 

for your proofs with bools, use the boolean implication function "bimp" provided below:
-/

-- implication on bools:
def bimp (x y : bool) : bool := (bnot x) || y 

/-
Example: p ∧ (q ∨ ¬q)

ANSWER:

A: (Notice that we place T's and F's under the operator associated with the
   column, e.g., in the final column, we are taking a conjunction.)

p | q | ¬q | q ∨ ¬q | p ∧ (q ∨ ¬q)
-----------------------------
T | T | F  |   T    |   T
T | F | T  |   T    |   T
F | T | F  |   T    |   F
F | F | T  |   T    |   F

B: satisfiable and falsifiable

C: 2

D: p

E: first we try to do it with Props:
-/
theorem p_and_q_or_not_q_equiv_p_Prop: ∀ p q : Prop, p ∧ (q ∨ ¬ q) ↔ p 
:= begin
    intros,
    split,
    {
        intro h,
        cases h with h1 h2,
        assumption,
    },
    {
        intro h,
        split,
        assumption,
        sorry, -- we haven't learned how to deal with that yet, so we give up
    }
end

-- E: we didn't manage to complete the proof with Props, so we do it with bools:
theorem p_and_q_or_not_q_equiv_p_bool: ∀ p q : bool, p && (q || bnot q) = p 
:= begin
    intros,
    cases p,
    repeat {
        cases q,
        refl,
        refl,
    }
end




/- HWK05-01 continued:

Do the above A,B,C,D,E steps for each of the following formulas:
1. x → (y → x)
2. x → (y → z)
3. (x → y) → z  
4. (p → (q ∧ r)) ∧ (r → ¬q)

-/

-- ANSWERS:

/- 1. x → (y → x) is ... 
-/
... 


/- 2. x → (y → z)  is ... 
-/
... 


/- 3. (x → y) → z  is ... 
-/
... 


/- 4. (p → (q ∧ r)) ∧ (r → ¬q)  is ... 
-/
... 




/- HWK05-02:
prove the following:
-/
theorem conjunction_right: ∀ P Q : Prop, (P ∧ Q) → Q 
:= begin
-- ANSWER:
    ... 
end




/- HWK05-03:
prove the following:
-/

theorem p_and_q_implies_q_and_p: ∀ p q : Prop, (p ∧ q) → (q ∧ p) 
:= begin
-- ANSWER:
    ... 
end





-- recall our weekday example:

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

open weekday 

def next_workday : weekday → weekday 
    | sunday := monday
    | monday := tuesday
    | tuesday := wednesday
    | wednesday := thursday
    | thursday := friday
    | friday := monday
    | saturday := monday
--


/- HWK05-04-1:
prove the following:
-/

theorem next_workday_is_a_5day_weekday: ∀ d : weekday, 
    next_workday d = monday ∨ 
    next_workday d = tuesday ∨ 
    next_workday d = wednesday ∨ 
    next_workday d = thursday ∨ 
    next_workday d = friday 
:= begin
-- ANSWER:
 ... 
end


/- HWK05-04-2:
prove the following:
-/

theorem next_workday_not_weekend: 
    ∀ d : weekday, next_workday d ≠ sunday ∧ next_workday d ≠ saturday 
:= begin
-- ANSWER:
   ... 
end



/- HWK05-05:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem p_or_p: ∀ P : Prop, (P ∨ P) ↔ P 
-- ANSWER:
... 



/- HWK05-06:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem p_and_p: ∀ P : Prop, (P ∧ P) ↔ P 
-- ANSWER:
... 



/- HWK05-07:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem or_commut: ∀ P Q : Prop, (P ∨ Q) ↔ (Q ∨ P) 
-- ANSWER:
... 




/- HWK05-08:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem iff_commut: ∀ P Q : Prop, (P ↔ Q) ↔ (Q ↔ P) 
-- ANSWER:
... 



/- HWK05-09:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem or_associat: ∀ A B C : Prop, A ∨ (B ∨ C) ↔ (A ∨ B) ∨ C
-- ANSWER:
... 





/- HWK05-10:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem or_distrib_and: ∀ A B C : Prop, A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C)
-- ANSWER:
... 



/- HWK05-11:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem and_absorb_or: ∀ P Q : Prop, P ∧ (P ∨ Q) ↔ P 
-- ANSWER:
... 


/- HWK05-12:
the lemma nat.zero_lt_succ is defined (proven) in the LEAN library. you don't have to know how it's proven. you only need to be able to understand (1) what it says, and (2) how to use it. 
-/

#check nat.zero_lt_succ   -- move your cursor here to see what this lemma states 

/- HWK05-12 continued:
prove that 0 < 2 by using the "have" tactic to call lemma nat.zero_lt_succ 
-/
example: 0 < 2  
:= begin
-- ANSWER:
    ... 
end







/- HWK05-13: 
let's continue formalizing the correctness of sorting programs like isort from your hwk01. in HWK04 we asked you to define functions leq and sorted. correct implementations of those are given below: 
-/
-- ANSWER:
def leq : ℕ → ℕ → bool 
  | 0 y := tt 
  | (nat.succ x) 0 := ff 
  | (nat.succ x) (nat.succ y) := leq x y 
--

def sorted : list ℕ → bool 
  | [] := tt 
  | [_] := tt 
  | (x :: (y :: L)) := (leq x y) && (sorted (y :: L)) 
--

/- HWK05-13-1:
claiming that a sorting program f : list ℕ → list ℕ always produces sorted lists is not enough to show that f is a correct sorting program. for example: (1) the program that always returns the empty list always produces sorted lists: show that. (2) the program that always returns the list [1,2,3] also always produces sorted lists: show that too. 
-/

def fsrtempty: list ℕ → list ℕ := λ L, [] 
def fsrt123: list ℕ → list ℕ := λ L, [1,2,3] 

theorem fsrtempty_sorted: ∀ L : list ℕ, sorted (fsrtempty L) = tt  
:= begin
-- ANSWER:
... 
end

theorem fsrt123_sorted: ∀ L : list ℕ, sorted (fsrt123 L) = tt  
:= begin
-- ANSWER:
  ... 
end

/- HWK05-13-2:
now we know that producing sorted lists is not enough to make a sorting program correct. what other properties should a sorting program f satisfy then? the answer is, that (f L) should be a "permutation" of L, for any input list L. we will formalize permutation in two steps. 

define a function occurno : ℕ → list ℕ → ℕ  which takes a nat x and a list of nats L, and returns the number of times x occurs in L. as usual, all tests below must pass. 
-/

-- ANSWER:
def occurno : ℕ → list ℕ → ℕ  
  ... 

-- DO NOT DELETE:
example: occurno 0 [] = 0 := begin refl, end 
example: occurno 0 [1] = 0 := begin refl, end 
example: occurno 0 [1,2] = 0 := begin refl, end 
example: occurno 0 [1,2,3] = 0 := begin refl, end 
example: occurno 0 [0] = 1 := begin refl, end 
example: occurno 0 [0,1] = 1 := begin refl, end 
example: occurno 0 [0,0] = 2 := begin refl, end 
example: occurno 1 [1,0] = 1 := begin refl, end 
example: occurno 10 [10,0,10,10,10] = 4 := begin refl, end 

/- HWK05-13-3:
define a function permutation : list ℕ → list ℕ → Prop which takes two lists of nats L1 and L2, and returns the proposition "the number of occurrences of x in L1 is equal to those in L2, for any nat x".  
-/

-- ANSWER:
def permutation (L1 L2 : list ℕ) : Prop := 
  ... 

#check permutation 

/- HWK05-13-4:
formalize the correctness of isort, given below, in terms of the function permutation that you defined above. you do NOT have to prove the theorem isort_correct, just state it. 
-/
def insrt : ℕ → list ℕ → list ℕ
  | x [] := [x] 
  | x (y :: L) := if (leq x y = tt) 
                  then x :: (y :: L) 
                  else y :: (insrt x L) 
--

def isort : list ℕ → list ℕ
  | [] := []  
  | (x :: L) := insrt x (isort L) 
--

-- ANSWER:
theorem isort_correct: ... 
:= begin
    -- do not delete! 
    intro,
    sorry,
end







/- HWK05-14: 
we will prove that plus x 0 = x, with a little help from our friends, the lemmas. 
-/

def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  
--

/- HWK05-14-1: 
prove the lemma plusind0:
-/
lemma plusind0: plus 0 0 = 0 
:= begin 
-- ANSWER:
   ... 
end

/- HWK05-14-2: 
prove the lemma plusind1:
-/
lemma plusind1: ∀ (x : ℕ), plus x 0 = x → plus (nat.succ x) 0 = nat.succ x
:= begin
-- ANSWER:
    ... 
end

/-
suppose the lemma plusind2 is given to you. you do NOT have to prove it. 
-/
lemma plusind2: 
    plus 0 0 = 0 → 
    (∀ x : ℕ, plus x 0 = x → plus (nat.succ x) 0 = nat.succ x) → 
    (∀ x : ℕ, plus x 0 = x)
:= begin
    sorry, -- leave this here 
end

/- HWK05-14-3: 
use the above three lemmas, and the "have" tactic, in order to prove the theorem plus_x_0. you can also use any other tactics that we have learned. 
-/
theorem plus_x_0: ∀ x : ℕ, plus x 0 = x 
:= begin
-- ANSWER:
    ... 
end



