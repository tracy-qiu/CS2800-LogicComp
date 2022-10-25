-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


import .ourlibrary06

----------------------------------------------------
-- cases on lists    
----------------------------------------------------

/- note that the _cases x_ tactic where x is a member of an inductive data type applies for any such inductive data type. in particular, it applies also when x is a list:
-/

example: ∀ L : list ℕ, L = [] → len L = 0 
:= begin
    intro,
    intro h,
    -- the rest is just for illustration! typically, we would continue the proof using "rw h" to replace L with []. but we can also do "cases L": 
    cases L with x L2,
    {
        refl,
    },
    {
        unfold len,
        trivial, -- "cases h" also works here. both these tactics essentially recognize that a nonempty list cannot be equal to an empty list, therefore our assumption h is equivalent to false. this is like having 1 = 0 in our hypotheses (nat.succ of something cannot be equal to nat.zero). 
    }
end




----------------------------------------------------
-- CALLING LEMMAS & THEOREMS LIKE FUNCTIONS continued
----------------------------------------------------

-------------------------------
-- have: proofs within proofs
-------------------------------

-- here's an example of a "mini-proof" within a proof, using _have_:
theorem true_implies_p: ∀ P : Prop, (true → P) ↔ P 
:= begin
    intro,
    split,
    {
        intro h,
        -- now what? we have true → P as an assumption. we know that true holds, so we could use modus ponens to get P. but even if we know that true holds, we don't have a proof of true in our list of hypotheses! how do we get one? like this:
        have h1 : true -- we state that we will prove "true"
        := begin -- we begin the proof-within-the-proof
            trivial, -- we prove it
        end, -- we end the proof-within-the-proof, and we now have h1 : true in our list of hypotheses!
        
        -- this "have" pattern with a begin ... end proof section is very useful because we can have proofs within proofs. but try not to abuse this feature: if the proof within a proof gets too long, it means you should probably separate it into a lemma (modularity & reuse principle).

        have h2 := h h1,
        assumption,
    },
    {
        intro h1,
        intro h2,
        assumption,
    }
end




----------------------------------------------
-- CLASSIC LOGIC vs. CONSTRUCTIVE LOGIC
----------------------------------------------

/- 
recall the propositional logic tautology P ∨ ¬P. this tautology is also called the _law of excluded middle_, meaning there's nothing "in between" P and ¬P. so either one or the other must hold. we can prove this easily when P is of type bool:
-/
theorem excluded_middle_bool: ∀ P : bool, P || bnot P = tt 
:= begin
    intro,
    cases P,
    refl,
    refl,
end

-- but can we prove it for any Prop?  let's see if we can prove it with the tactics that we have learned so far:
theorem excluded_middle_1st_try: ∀ P : Prop, P ∨ ¬ P 
:= begin
    intro,
    -- now what? our goal is a disjunction, so we have to choose "left" or "right". but no matter what we choose, we cannot complete the proof... 
    try {cases P},  -- this doesn't work ... 
    sorry
end

/- in fact, the law of excluded middle is something that cannot be proven for Props with the tactics we have seen so far. in classic logic, this is an _axiom_. an axiom is something that can be taken for granted, without having to be proven. in terms of the discussion about proof rules that we had above, we can write:
    ⊢ P ∨ ¬P 
meaning that starting even with an empty left-hand side to ⊢ (i.e., no hypotheses at all) we can still prove P ∨ ¬P, for any P. 

this is an axiom of _classic_ logic, but it is not an axiom of other logics. in particular, it is not an axiom of so-called _constructive_ or _intuitionistic_ logic, which forms the foundation of the so-called _calculus of constructions_ and tools like Coq. the same logic is behind LEAN, but LEAN includes the law of excluded middle as an axiom in its library. 

You may wonder why on earth would there be a logic like constructive logic which doesn't have the law of excluded middle? Constructive logic, like its name implied, stemmed from a desire for more "constructive" mathematics, where for instance, proofs of existence of something not only proved that this something must exist, but also offered concrete ways to find it. Here's a nice example of this, taken from the _Handbook of Practical Logic and Reasoning_ by Harrison. 

Here's a non-constructive proof of the following theorem: _There are irrational numbers x and y such that x^y (x to the power y) is rational._ "Proof: Let z denote the square root of 2. Either z^z is rational, or it is irrational. If z^z is rational, then we have found x = y = z. If z^z is irrational, then let x = z^z and y = z. Then x^y = 2, which is rational. QED" Now, you may be satisfied with this proof, but in the end, we don't really know what x and y are. We know that _either_ they are something, _or_ they are something else, but we don't know which. Such proofs displeased the proponents of constructive logic. The above proof is non-constructive, because it uses the axiom "either z^z is rational, or it is not rational", i.e., an instance of P ∨ ¬P (with P in this case being "z^z is rational"). 

We will not delve much into constructive logic, but it is useful to do some exercises in order to understand what can be proven using what. we will also need to be using axioms such as P ∨ ¬P in our proofs, so we will also illustrate how to appeal to those in LEAN. 
-/


-- LEAN already provides the law of excluded middle as an axiom:
#check classical.em 

/-
can we now re-prove the law of excluded middle? yes we can, using classical.em. this is trivial, since classical.em _is_ exactly the law of excluded middle. so we are proving something assuming itself, which is uninteresting. still, we show how this is done for the sake of illustrating also the usage of _have_:
-/

-- "function-oriented" proof:
theorem excluded_middle: ∀ P : Prop, P ∨ ¬ P := classical.em 

-- standard proof with begin ... end and have:
theorem excluded_middle_std_proof: ∀ P : Prop, P ∨ ¬ P 
:= begin
    intro,
    have h := classical.em P, -- we call classical.em and pass P to it 
    assumption,
end

#check excluded_middle
#check excluded_middle_std_proof


/-
as with other theorems/functions that take Props as inputs, we can call classical.em with any Prop. for example:
-/

example: ∀ x : ℕ, x = 0 ∨ x ≠ 0 
:= begin
    intro,
    have h := classical.em (x = 0),
    assumption,
end

-- another way of doing it
example: ∀ x : ℕ, x = 0 ∨ x ≠ 0 
:= begin
    intro,
    cases x, 
    {
        left, 
        refl, 
    },
    {
        right, 
        intro h, 
        trivial,
    }
end

------------------------------------------------------------
-- HOW DO I KNOW WHETHER I HAVE TO USE classical.em ?
------------------------------------------------------------

/- 
many facts can be proven in both classic logic and constructive logic. we have been proving many things already, without the need for classical.em. but there are some tautologies that need classical.em. in fact, there are cases where some statement (a) may look very similar to another statement (b), while in fact (a) does not need classical.em but (b) does. 

how do we know whether or not we have to use classical.em? 

you will learn this by practice. in general you will:
(1) start trying to do the proof using the tactics that we learned. try to finish the proof without using classical.em. 
(2) what if you get stuck? first, try to see whether what you are trying to prove is valid to begin with! here, you can try to do some boolean reasoning: "either p will be true, or p will be false. if p is true then .... if p is false then  .... "
(3) if you are convinced that what you are trying to prove is indeed true (your boolean reasoning didn't reveal a counterexample) then you can formalize your boolean reasoning using classical.em, e.g., as in: 
    have h := classical.em p,
then you can do cases h and try to continue your proof for both the cases when p is true and when ¬ p is true (i.e., p is false). 

let us now look at some examples of this method:
-/

-- let's try to prove this:
theorem p_implies_not_not_p: ∀ P : Prop, P → (¬ ¬ P) 
:= begin
    intro, 
    intro h1, 
    dunfold not,
    intro h2, 
    have h3 := h2 h1,
    trivial, 
end

-- now let's try to prove this:
theorem not_not_p_implies_p_1st_try: ∀ P : Prop, (¬ ¬ P) → P 
:= begin
    intro, 
    intro h1, 
    have h2:= classical.em (¬ P),
    cases h2, 
    {

    }

end



theorem p_implies_not_not_p: ∀ P : Prop, P → (¬ ¬ P) 
:= begin
    intro,
    intro h1,
    intro h2,
    have h := h2 h1,
    trivial,
    -- we succeeded without using classical.em !
end

-- now let's try to prove this:
theorem not_not_p_implies_p_1st_try: ∀ P : Prop, (¬ ¬ P) → P 
:= begin
    intro,
    intro h1,
    -- recall that ¬ ¬ P is the same as (¬ P) → false, which is the same as (P → false) → false:
    dunfold not at h1, -- not needed, here just to unfold ¬ 
    -- but how to proceed from here? we are stuck!
    try {cases h1, }, -- does nothing, h1 is not an ∨ or an ∧ !
    try {cases P,}, -- does nothing, cases doesn't work on Props!
    sorry,
end

/-
at this point, we have to stop and think. is what i am trying to prove really true? we can do boolean reasoning: 
    - either P will be true, in which case the implication (¬¬P) → P will be trivially true;
    - or P will be false, in which case ¬P will be true, and therefore ¬¬P will be false, so the implication (¬¬P) → P will be true again. 
so we are convinced that what we are trying to prove is indeed true. we can then try the proof one more time, this time using classical.em: 
-/
theorem not_not_p_implies_p_using_em: ∀ P : Prop, (¬ ¬ P) → P 
:= begin
    intro,
    intro h1,
    have h2 := classical.em P, -- we are "calling" classical.em with argument P
    cases h2,
    {
        assumption,
    },
    {
        have h3 := h1 h2,
        trivial,
    }
end


/-
it's interesting that although (P → ¬¬P) and (¬¬P → P) look similar, one of them needs classical.em while the other one does not! 
-/




/- REMINDER: STRONGER, WEAKER, EQUIVALENT FORMULAS

suppose A and B are propositional logic formulas. we say that:

    - _A is stronger than B_ if A → B is valid / a tautology. if A is stronger than B, then whenever A is true, B is also true. in other words, A implies B. 

    - _A is weaker than B_ if B → A is valid / a tautology. in other words, A is weaker than B iff B is stronger than A. 

    - _A is equivalent to B_ if both A → B and B → A are valid, that is, both A is stronger and weaker than B. in other words, A ↔ B is valid. 

the same terminology applies to more general (not just propositional) logic formulas. for example, (x ≥ 10) is stronger than (x ≥ 0). 

-/



-- PRACTICE!

/- let's practice the method we described earlier. consider the formulas (a) and (b) below:

    (a)  p → q 
    (b)  ¬(p ∨ q) 

answer the questions below:

1. are these two formulas equivalent?

2. is (a) stronger than (b)? if it is, prove it. did you have to use classical.em? if (a) is not stronger than (b), find a counterexample. 

3. is (b) stronger than (a)? if it is, prove it. did you have to use classical.em? if (b) is not stronger than (a), find a counterexample. 

-/

example: ∀ p q : Prop, (p → q) → ¬(p ∨ q)
:= begin 
    intros p q, 
    intro h1, 
    intro h2, 
    

end
-- ANSWERS:
/- the two formulas are not equivalent. ¬(p ∨ q) is strictly stronger (strictly stronger means that it is stronger and not equivalent). we can prove it, without using classical.em:
-/
example: ∀ p q : Prop, ¬(p ∨ q) → (p → q) 
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    have h : p ∨ q 
    := begin
        left,
        assumption,
    end,
    have h3 := h1 h,
    trivial,
end

/-
(p → q) is not stronger than ¬(p ∨ q). for example, the assignment p := true and q := true makes (p → q) true, but it makes ¬(p ∨ q) false. 
-/



----------------------------------------------
-- CLASSIC vs. CONSTRUCTIVE LOGIC CONTINUED
----------------------------------------------

/- as it turns out, ¬¬P → P is also an axiom of classic logic. it is the rule of "proof by contradiction". it says: "in order to prove P, I will assume ¬P, and I will reach a contradiction (i.e., false)". in other words, "if I can prove (¬P → false) then I have proven P". but (¬P → false) is exactly ¬¬P ! the proof by contradiction rule is also an axiom in LEAN:
-/

#check classical.by_contradiction   

/-
note that the type of classical.by_contradiction looks different from the type of classical.em. the latter has a (∀ p : Prop) in the front, which means it takes a Prop as input. but  classical.by_contradiction  does not take a Prop as input. it takes as input a proof of ¬¬P, for some (any) Prop P, and it returns a proof of P: 
-/

example: ∀ x : ℕ, ¬ (x ≠ 0) → x = 0 
:= begin
  intro,
  intro h1,
  have h2 := classical.by_contradiction h1,
  assumption,
end



/- do we need both axioms classical.em and classical.by_contradiction? no we don't. as we saw just above, if we have classical.em, then we can prove classical.by_contradiction: we did that in the theorem "not_not_p_implies_p_using_em". conversely, if we have classical.by_contradiction, then we can prove classical.em (this will be in your homework). so only one of them is really needed. but LEAN provides both for convenience, so that users don't have to re-prove them. 
-/



/- THEOREMS vs FORMULAS
  
    BE CAREFUL!!!  
-/

-- consider theorems thm1 and thm2:

def thm1: ∀ p q : Prop, p -> q -> p 
:= begin intros, assumption, end 

def thm2: ∀ p q : Prop, (p ∧ q) -> (q ∧ p) 
:= begin intros p q h, cases h, split, assumption, assumption, end 

/-
since thm1 and thm2 are both valid, they are both equivalent to Prop true. so they must themselves be equivalent. but we cannot just write
    thm1 <-> thm2
-/

#check (thm1 ↔ thm2)     -- type error!


/-
why is that the case?

because ↔ (iff) is a function that applies to Props, but neither thm1 nor thm2 are of type Prop!

recall what the type of theorems is:
-/

#check thm1 -- thm1 : ∀ (p q : Prop), p → q → p
#check thm2 -- thm2 : ∀ (p q : Prop), p ∧ q → q ∧ p


/-
so thm1 is of type ∀ (p q : Prop), p → q → p
and thm2 is of type ∀ (p q : Prop), p ∧ q → q ∧ p

each of these types are themselves of type Prop:
-/

#check ∀ (p q : Prop), p → q → p 
#check ∀ (p q : Prop), p ∧ q → q ∧ p 

/-
so thm1 is of type (∀ ...) and the latter is of type Prop. 
and similarly for thm2. 

(this is a nice illustration how types are a very useful tool to help us avoid mixing up concepts which are not the same. natural languages like english or greek are very loosely typed (verb, noun, etc.) which often leads to confusion. politicians sow confusion and exploit it deliberately.)

now, going back to what we started with: how can we prove that thm1 and thm2 are equivalent?

there are a couple of ways to do that. one is to just copy the claims of the theorems and paste them to the left and right sides of an ↔ : 
-/
example: ( ∀ (p q : Prop), p → q → p )
                ↔ 
        ( ∀ (p q : Prop), p ∧ q → q ∧ p ) 
:= begin
    split,
    {
        intro h1,
        intro,
        intro,
        intro h2,
        cases h2 with h3 h4,
        split,
        assumption,
        assumption,
        -- notice we didn't use h1 at all. why?
    },
    {
        intro h1,
        intro,
        intro,
        intro h2,
        intro h3,
        assumption,
        -- again, we didn't use h1 at all. why?
    },
end

/-
a better way is to give names to each of these statements, so that we don't have to copy the statements themselves, but we can use their names instead: 
-/

def taut1 := ( ∀ (p q : Prop), p → q → p )
def taut2 := ( ∀ (p q : Prop), p ∧ q → q ∧ p ) 

#check taut1 
#check taut2 

/-
notice that taut1 is NOT the same thing as thm1! thm1 has type ( ∀ (p q : Prop), p → q → p ), but taut1 has type Prop! thm1 is a function that receives a bunch of stuff and returns a proof. taut1 is not a function. taut1 is the proposition itself. taut1 is a logical formula, a logical claim. 

idem for thm2 vs taut2. 

now we can state and prove this, in the same way as with the copy-paste example above:
-/

example: taut1 ↔ taut2 
:= begin
    split,
    {
        intro h1,
        intro,
        intro,
        intro h2,
        cases h2 with h3 h4,
        split,
        assumption,
        assumption,
    },
    {
        intro h1,
        intro,
        intro,
        intro h2,
        intro h3,
        assumption,
    },
end

/-
to conclude this discussion, proving taut1 ↔ taut2 is not  interesting, once we have proven that taut1 and taut2 are both tautologies. but in general, we may have two statements formula1 and formula2, which we want to prove equivalent, without knowing whether they are true or not. 
-/



-- QUIZ TIME!

/-
HWK03 and HWK04 REVIEW 
-/

