-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


/-
    QUIZZES:
    - they are worth 24 points! that's too much!!!
    - they are worth 20% of the final grade! that's too much!!!
-/



/-
    RECAP: WHERE WE STAND

At a minimum, you should be able to:

- write functions with types in LEAN (including recursive functions using pattern matching)

- write and prove examples-tests with refl

- write forall specifications, which include functions, =, and any of the logical connectives (→ , ¬ , ∧ , ∨ , ↔ , ...) 

- prove some of those forall specifications using the tactics we've seen: 
intro, refl, dunfold, rw, cases, assumption, exact, trivial 


If any of the above sounds strange, weird, never-heard-of, etc, COME TO OFFICE HOURS RIGHT AWAY!

consult the lecture notes regularly, especially sections 7 and 8:
    https://course.ccs.neu.edu/cs2800f22/lecture-notes.pdf
-/





-- we can now prove things about general Props:

theorem p_implies_p: ∀ P : Prop, P → P
:= begin
    intro,
    intro h,
    assumption, -- or "exact h" 
end

theorem p_implies__p_implies_p: ∀ P : Prop, P → (P → P)
:= begin
    intro,
    intro h1,
    intro h2,
    assumption, -- or exact h1, or exact h2  -- NOTE: "trivial" does not work here for some reason... 
end

-- but this doesn't hold:
theorem p__implies_p_implies_p: ∀ P : Prop, (P → P) → P    -- NOT VALID !!!  (e.g., when P is false)
:= begin
    intro,
    intro h,
    try {assumption, },  -- "P → P" is not the same as "P" !!!
    try { exact h,},     -- "P → P" is not the same as "P" !!!
    sorry ,
end


----------------------------------------------------
-- true
----------------------------------------------------

#check true     -- this is _not_ the same as tt 

/- we have already said that "true" is the proposition taken for granted to be true. but can we prove that? which tactic should we use when our goal is "true"? we can use "trivial":
-/

theorem true_trivially_holds: true
:= begin
    trivial, -- trivial recognizes true in the goal
end

theorem anything_implies_true: ∀ p : Prop, p → true
:= begin
    intro,
    intro h, 
    trivial, 
end 




----------------------------------------------------
-- false
----------------------------------------------------

#check false    -- this is _not_ the same as ff 



/- "false" is the proposition which is taken for granted to be false. we cannot prove false. false should be unprovable in any sound system. if you manage to prove false (without any assumptions) in LEAN, you have found a LEAN bug. i will then give you automatically an A, and you can probably graduate and go work for the LEAN team. 
-/

theorem false_implies_false: false → false 
:= begin 
    intro h, 
    assumption 
end

theorem false_by_itself_cannot_be_proven: false 
:= begin
    sorry,
end



/- SOUNDNESS and COMPLETENESS

we should be glad we are not able to prove false. if we were able to do that, then our proof system would be _unsound_. in general, a logic / proof system is _sound_ if it is only able to prove statements that are (semantically) valid. meaning, if it can prove a statement φ, then φ is valid, i.e., φ is indeed true. the reverse is called _completeness_: a logic / proof system is _complete_ if it is able to prove all (semantically) valid statements. meaning, if φ is valid, then φ can be proven in that system. we always want soundness, but completeness is sometimes too much to ask. many systems are sound but incomplete. we will talk about this a bit later. 
-/

/-
now, false cannot be proven, but starting from false you can prove anything you want! so false → P is true for any P : Prop!

(politicians know that starting from false premises you can prove anything you want, and they exploit this marvellously.)  
-/

-- which tactic should we use when one of our assumptions is "false"? "trivial" works for that too:

theorem false_implies_anything: ∀ P : Prop, false → P
:= begin
    intro,
    intro h,
    trivial, -- here trivial recognizes false in the hypotheses 
end

theorem false_implies_false: false → false
:= begin
    intro h,
    trivial, -- or "assumption" or "exact h"
end




-- sometimes trivial also works for "obviously true" goals:
example: 1 = 1 
:= begin 
    trivial, -- we could also use "refl" here of course 
end 

-- but sometimes it doesn't, which is a LEAN "feature" that we will ignore:
example: ∀ p : Prop, p → (p → p)
:= begin
    intros p h1 h2,
    try {trivial,}, -- fails to do anything ... 
    assumption,
end


-- sometimes trivial also works for "obviously false" hypotheses:
theorem one_equals_zero_implies_anything: ∀ P : Prop, 1 = 0 → P 
:= begin
    intro,
    intro h,
    trivial,
end

-- but "obviously false" is not always so "obvious" to LEAN:
example: ∀ P : Prop, 1 = 2 → P 
:= begin
    intro,
    intro h,
    try {trivial,}, -- doesn't work!
    sorry,
end

-- the "cases" tactic to the rescue!
theorem one_equals_two_implies_anything: ∀ P : Prop, 1 = 2 → P 
:= begin
    intro,
    intro h,
    cases h, -- don't ask "why" this works 
end


/-
now let's see how to deal with the rest of the logical connectives: or, and, not, iff, xor. 

we have to know how to handle each of those when we encounter it: either in the goal; or in one of our hypotheses. 
-/

----------------------------------------------------
-- disjunction in the goal 
----------------------------------------------------

-- which tactic should we use when our goal is an "or" (i.e., a disjunction)?

----------------------------------------------------
-- left, right
----------------------------------------------------

theorem disjunction_left: ∀ P Q : Prop, P → P ∨ Q 
:= begin
    intro,
    intro,
    intro,
    left,       -- we choose to prove the left part of the disjunction
    assumption,
end

theorem disjunction_right: ∀ P Q : Prop, Q → P ∨ Q 
:= begin
    intro,
    intro,
    intro,
    right,      -- we choose to prove the right part of the disjunction
    assumption,
end



/- tactics = moves

a legal move (tactic that applies) is NOT always a good move!
-/

/- NOTE: tactics are _local_ in the sense that whether or not they apply only depends on _the current proof state_! meaning the current goal, and the current set of hypotheses. a tactic is just one step in a proof. a tactic does not have a "global view" of neither what we are trying to prove, nor how we go about proving it. applying a tactic is like making a legal move in a game of chess. when a tactic applies, it means that the rules of chess are followed. when a tactic gives an error, it means that i tried to do something that violates the rules of the game. LEAN won't let me do that. but the fact that i make a move that doesn't break the rules of chess does not necessarily mean that this is a smart move to make! it doesn't necessarily mean that i will end up winning the game! it only means that i have made one move. same thing when proving in LEAN. applying a tactic does not necessarily mean it's the right tactic to apply, and that it will necessarily lead us to completing the proof. 

one or more tactics may apply, and yet lead to a dead-end, where we cannot complete the proof (either because the proof cannot be completed because the result is false, or simply because we didn't take the right steps / choose the right tactics). 

as an example, consider the left / right tactics that we learned. they apply but might lead to a dead-end:
-/

theorem true_theorem_but_bad_choice_tactic: ∀ p q : Prop, p → (p ∨ q) 
:= begin
    intros p q h,
    right, -- bad choice, now the theorem cannot be proven anymore ... 
    sorry,
end

theorem false_theorem_but_i_can_still_go_ahead_several_steps_in_the_proof: ∀ p q r : Prop, p → (q ∨ r ∨ q ∨ r) 
:= begin
    intros p q r h,
    -- from now on, i could follow many paths, but none of them leads anywhere ... 
    right,
    right,
    left,
    sorry,
end





----------------------------------------------------
-- conjunction in the goal 
----------------------------------------------------

-- which tactic should we use when our goal is a conjunction?

----------------------------------------------------
-- split
----------------------------------------------------

theorem p_implies_q_implies_q_and_p: ∀ p q : Prop, p → q → (p ∧ q) 
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    split,  -- when the goal is of the form P ∧ Q, _split_ splits the proof in two, one where the goal is P and another where the goal is Q
    {
        assumption,
    },
    {
        assumption,
    }
end



----------------------------------------------------
-- disjunction in the hypotheses 
----------------------------------------------------

-- which tactic should we use when one of our _hypotheses_ is a disjunction?

----------------------------------------------------
-- cases, again
----------------------------------------------------

theorem p_or_q_implies_q_or_p: ∀ P Q : Prop, P ∨ Q → Q ∨ P 
:= begin
    intro,
    intro,
    intro h,
    try {assumption}, -- does nothing 
    cases h,  -- when _h_ is an assumption of the form P ∨ Q, _cases h_ splits the goal into two subgoals, one where we assume P and another where we assume Q
    -- we can also use "cases h with ... ..." to rename the hypotheses 
    {
        right,
        assumption,
    },
    {
        left,
        exact h,
    }
end


----------------------------------------------------
-- conjunction in the hypotheses 
----------------------------------------------------


-- which tactic should we use when one of our hypotheses is a conjunction?

----------------------------------------------------
-- cases, again
----------------------------------------------------

theorem p_and_q_implies_p: ∀ p q : Prop, (p ∧ q) → p 
:= begin
    intros p q h,
    cases h, -- when _h_ is an assumption of the form P ∧ Q, _cases h_ "splits" _h_ into two separate hypotheses, one for P and one for Q 
    -- we can also use "cases h with h1 h2" to rename the hypotheses
    -- exact h1,
    assumption, 
end

-- we can use "with h1 h2" to rename the hypotheses:
theorem p_and_q_implies_p_with: ∀ p q : Prop, (p ∧ q) → p 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2, -- "with" renames the cases, with h1 h2 not necessary to have 
    exact h1, 
end



----------------------------------------------------
-- NEGATION: not ¬ 
----------------------------------------------------

/- what is negation? it is fascinating that it can be defined not as a primitive, but in terms of implication, namely: ¬ P := (P → false).  read: "not P" is the same as "if P then false". 
-/
#check not  -- you can CTRL-click on "not" to see how it's defined

/- 
so not is really implication!!! since we know how to treat implication, we can use this fact to prove stuff involving not:
-/

theorem not_false_: ¬ false 
:= begin
    -- ¬ is an implication, so _intro_ should apply:
    intro,
    trivial, -- assumption also works
end

-- so, ¬ false and false → false are the same thing!
theorem false_implies_false_: false → false 
:= begin
    intro,
    assumption,
end

-- ¬ is implication independently of the Prop it is applied to:

theorem thm3: ∀ x : nat, ¬ (x = x+1) 
:= begin
    intro,
    intro h,
    sorry,
end

-- ≠ is the same as ¬ ( ... = ... )  
theorem thm4: ∀ x : nat,  (x  ≠  x+1) 
:= begin
    intro,
    intro h,
    sorry,
end





----------------------------------------------------
-- iff (if and only if)
----------------------------------------------------

-- P ↔ Q is equivalent to (P → Q) ∧ (Q → P). so we treat it just like a conjunction:

theorem p_iff_p: ∀ P : Prop, P ↔ P 
:= begin
    intro,
    split, -- from A ↔ B it generates two goals: A → B and B → A
    {
        intro,
        assumption,
        -- could also be 
        -- intro h, 
        -- exact h,
    },
    {
        intro,
        assumption,
    }
end



----------------------------------------------------
-- repeat 
----------------------------------------------------

-- we can use _repeat_ to keep applying a block of tactics as many times as they can be applied:
theorem p_iff_p_with_repeat: ∀ P : Prop, P ↔ P 
:= begin
    intro,
    split, 
    repeat -- repeat whatever is between { ... } 
    {
        intro,
        assumption,
    },
end



----------------------------------------------------
-- are "try", "sorry", and "repeat" tactics?
----------------------------------------------------

/-
let's not consider "try", "sorry" and "repeat" to be tactics. sorry always "applies" to any proof state, and "aborts" trying to prove the corresponding goal. try also always "succeeds" in the sense that if the attempted tactic(s) fail(s) then "trying" them simply does nothing. idem with repeat.  
-/


----------------------------------------------------
-- xor 
----------------------------------------------------

-- (xor P Q) is equivalent to (P ∧ ¬ Q) ∨ (Q ∧ ¬ P). so we treat it just like a disjunction:

theorem not_xor_p_p: ∀ P : Prop, ¬ xor P P 
:= begin
    intro,
    intro h,
    -- xor is really a disjunction:
    cases h,
    {
        cases h with h1 h2,
        -- now what? we don't know how to deal with this yet. we give up:
        sorry,
    },
    {
        cases h with h1 h2,
        sorry,
    }
end


------------------------------------------
-- equality = in propositional logic
------------------------------------------

-- we can write this:
example: ∀ p : Prop, p = p 
:= begin
    intro,
    refl,
end

-- but the equals symbol "=" is not really part of propositional logic, so we prefer to write this:
example: ∀ p : Prop, p ↔ p 
:= begin
    intro,
    refl,
end

-- similarly, we can write this:
example: ∀ p : Prop, ¬ (p ≠ p) 
:= begin
    intro,
    intro,
    trivial,
end

-- but we prefer to write this:
example: ∀ p : Prop, ¬ ¬ (p ↔ p) 
:= begin
    intro,
    intro,
    trivial,
end



-------------------------------------------------------
-- PROPOSITIONAL LOGIC IN LEAN 
-------------------------------------------------------

/-
LEAN "supports" propositional logic in at least two ways. 
-/

-- one way is to think of all propositional variables as of type bool:

section boolean_logic    -- everything within a section are local definitions

variable p : bool 
variable q : bool 

#check p && q   -- boolean and 
#check band p q -- boolean and
#check band 

#check p || q   -- boolean or 
#check bor p q  -- boolean or

#check bnot p   -- boolean not 

end boolean_logic

-- another way is to think of propositional variables as of type Prop:

section propositional_logic

variable p : Prop 
variable q : Prop 

#check p ∧ q   -- Prop and 
#check and p q -- Prop and
#check and 

#check p ∨ q   -- Prop or 
#check or p q  -- Prop or

#check ¬ p     -- Prop not 
#check not p   -- Prop not 

end propositional_logic

/-
is there a difference? yes! bools and Props are different types!

which "method" is better? to answer this, let's look at how we would prove tautologies using the two views:
-/

-------------------------------------------------------
-- PROVING TAUTOLOGIES using Props vs using bools
-------------------------------------------------------
/-
let's say we want to prove that a propositional logic formula like 
    p → (p → p) 
is valid (i.e., a tautology, i.e., "always true"). 

we can show this using the truth table method:

TRUTH TABLE FOR p → (p → p) :

    +---+-------+-------------+
    | p | p → p | p → (p → p) |
    +---+-------+-------------+
    | T |   T   |      T      |
    | F |   T   |      T      |
    +---+-------+-------------+

since the column for p → (p → p) only has Ts, the formula is valid. 

in LEAN we can prove this in two ways: either treating p as a Prop, or treating p as a bool: 
-/

-- if we treat p as a Prop, we can do it in this way:
theorem p_imp_p_imp_p_Prop: ∀ p : Prop, p → (p → p) 
:= begin
    intros p h1 h2,
    assumption,
end

#check ∀ p : bool, p → (p → p) -- not good we dont like casting instead do it the way below 

-- if we treat p as a bool, we can do it in this way:

-- first we define implies for bools:
def bimplies := λ x y : bool, (bnot x) || y 

-- then we state and prove our theorem with cases:
theorem p_imp_p_imp_p_bool: ∀ p : bool, bimplies p (bimplies p p) = tt 
:= begin
    intro,
    cases p,
    refl,
    refl,
end



/- which proof is "easier" or "prettier"? it's a matter of opinion/taste. 

however, the proof with Props is, as we shall see, more useful. that's because we will be able to _use_ theorem p_imp_p_imp_p_Prop, for ANY Prop p. for example, we will be able to use it (we will see how later) to prove:
    ∀ x : ℕ, x > 0 → (x > 0 → x > 0)

that's not the case for theorem p_imp_p_imp_p_bool. the latter applies ONLY to bools (we are not allowing coercions). 
-/




-- bool and Prop are different:
#check bool 
#check Prop 

#check tt 
#check true 
#check ff 
#check false  

#check ff && tt 
#check false ∧ true

#eval ff && tt 
#eval false ∧ true -- can't do
#reduce false ∧ true -- nothing useful happens 

#check and false true 
#check xor false true 


#check false ∨ tt   -- horrible type coercion! avoid at all costs! 




/-
SUMMARY: 

- which tactic to use when the goal is of the form A = A ?
    refl

- which tactic to use when the goal is of the form ∀ x ... ?
    intro

- which tactic to use when the goal is of the form A → B ?
    intro

- which tactic to use when the goal is the Prop true?
    trivial

- which tactic to use when a hypothesis is the Prop false?
    trivial

- which tactic to use when a hypothesis H is identical to the goal?
    assumption or exact H

- which tactic to use when the goal is of the form A ∨ B ?
    left or right, depending whether we want to continue with A or B

- which tactic to use when the goal is of the form A ∧ B ?
    split

- which tactic to use when a hypothesis is of the form H : A ∨ B ?
    cases H [with ...]

- which tactic to use when a hypothesis is of the form H : A ∧ B ?
    cases H [with ...]

- which tactic to use when the goal is of the form ¬ A ?
    intro 

- which tactic to use when the goal is of the form A ↔ B ?
    split  (or rw, as we will see later), since iff is really a conjunction 

- which tactic to use when a hypothesis is of the form H : A ↔ B ?
    cases H, since iff is really a conjunction 

- which tactic to use when the goal is of the form (xor A B) ?
    left or right, since xor is really a disjunction 

- which tactic to use when a hypothesis is of the form H : xor A B ?
    cases H, since xor is really a disjunction 

-/


def plus : nat -> nat -> nat
  | nat.zero y := y
  | (nat.succ x) y := nat.succ (plus x y)
--

----------------------------------------------------
-- rewrite revisited 
----------------------------------------------------

-- we have already seen how the tactic rw (rewrite) can be used in proofs by simplification (and also for "debugging"): 

example: plus 3 1 = 4 
:= begin
    rw plus,
    rw plus,
    rw plus,
    rw plus,
end


/- but rw can be used in other situations as well. for example, suppose one of our hypotheses is h : x = 0, meaning that we know that x is 0. then, we can replace x in our goal with 0! rw can be used to do exactly that:
-/

example: ∀ x y : nat, x = 0 → plus x y = y 
:= begin
    intro,  -- introduce x
    intro,  -- introduce y
    intro h,  -- introduce the hypothesis x = 0
    rw h,  -- rewrite x to 0, according to the equality in hypothesis h
    refl,
end

-- by default rw rewrites from left to right. if we want to rewrite in the opposite direction, we can use "rw <-" :
example: ∀ x y : nat, 0 = x → plus x y = y 
:= begin
    intros x y H,  
    rw <- H, -- by default, rewrite rewrites in the left-to-right direction. here we want the opposite direction
    refl,
end

-- now we can prove things like that: 
theorem plus_id: ∀ x y : ℕ, x = y → plus x x = plus y y 
:= begin
    intros x y H,
    rewrite H, 
end

-- in fact this holds for all functions (make sure you are able to "read in english" what the theorem below states!): 
theorem functions_are_functions: 
    ∀ T : Type, ∀ f : T → T, ∀ x y : T, x = y → f x = f y 
:= begin 
    intros T f x y H,
    rw H,
end




-- rw works not just with equalities x = y, but also with equivalences p ↔ q :
theorem iff_rw: ∀ P Q : Prop, (P ↔ Q) → (P → Q) 
:= begin
    intros P Q h1,
    rw <- h1,
    intro h2,
    assumption, --conjunction of implications (A<->B h(A->B)^(B->A))
end

-- we can use rw to rewrite not just the goal, but also a hypothesis using "rw H1 at H2":
theorem iff_rw_hyp: ∀ P Q : Prop, (P ↔ Q) → (P → Q) 
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    rw h1 at h2,
    assumption,
end



-- TIME FOR SOME PRACTICE!!! let's apply all the stuff we have learned to our weekday example:

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



-- remember this theorem? we couldn't prove them earlier. perhaps we can prove them now?



theorem nxtwkdaynotsunday: ∀ d : weekday, not (next_workday d = sunday) 
:= begin
    intro, 
    intro h,
    cases d,
    repeat {
        rw next_workday at h,
        trivial,
    },
end

theorem next_workday_not_sunday: ∀ d : weekday, next_workday d ≠ sunday ∧ next_workday d ≠ saturday 
:= begin
    intro,
    cases d,
    repeat {
        split,
        repeat {
            intro h,
            rw next_workday at h,
            trivial,
        },
    },
end


theorem next_workday_is_a_5day_weekday: ∀ d : weekday, 
    next_workday d = monday ∨ 
    next_workday d = tuesday ∨ 
    next_workday d = wednesday ∨ 
    next_workday d = thursday ∨ 
    next_workday d = friday 
:= begin
  intro,
  cases d,
  {
    dunfold next_workday,
    left,
    refl,
  },
  -- COMPLETE THE PROOF AT HOME!!! 
  repeat { sorry, },
end


