-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 


/- EXAM 1 is in one week!

EXAM 1: Mon Oct 24 2022 6:00 pm - 8:00 pm, SN 108

    - in person

    - on gradescope: 2 hours limit (+ any DRC extensions)

    - DRC students: you should have received email from me

    - on LEAN: bring your laptops, batteries FULLY CHARGED!

    - lecture notes, code, slides, homeworks available. 

-/

/-  TEST EXAM !!!

a test exam should be available / ready to take on gradescope.

this exam is just for testing and practice purposes, and will not be graded.

the test exam has no time limit but the real exam will have a time limit (2 hours). the real exam will also be much harder. the test exam should take you 20-30min max. 

    TAKE THIS EXAM ON GRADESCOPE ASAP!

    LET US KNOW IF YOU ENCOUNTER ANY PROBLEMS!

For example:

    Make sure you can read all symbols in the exam, including unicode symbols. 
    
    Make sure you can copy-paste, both FROM gradescope into your LEAN installation, and BACK from your LEAN into gradescope.

-/





/-
HWK03, HWK04 and HWK05 REVIEW 
-/






















----------------------------------------------------
-- MISC 
----------------------------------------------------


-------------------------------------------------
-- unfolding, rewriting, etc, "at" hypotheses
-------------------------------------------------

/-
many of the tactics we have seen apply not just to the goal, but also to any hypothesis. we can tell LEAN to apply a tactic to a hypothesis using "at": 
-/

example: ∀ x y : ℕ, plus 0 x = y → x = y 
:= begin
    intros x y h,
    dunfold plus at h,
    assumption,
end

example: ∀ x y z : ℕ, x = y → y = z → x = z 
:= begin
    intros x y z h1 h2,
    rw <- h1 at h2,
    assumption,
end




--------------------------------
-- the power of rewrite 
--------------------------------

-- this is a theorem we have already proven:
#check zero_plus  -- it's in ourlibrary11.lean 

-- suppose we want to prove this:
theorem mult_0_plus_v1: 
    ∀ (x y : nat), mult (plus 0 x) y = mult x y 
:= begin
    intros, 
    -- normally we would prove this by first using have:
    have h := zero_plus x, 
    -- and then rw:
    rw h,
end

-- as it turns out, rw is enough: 
theorem mult_0_plus_v2: 
    ∀ (x y : nat), mult (plus 0 x) y = mult x y 
:= begin
    intros,
    rw (zero_plus x),  -- just "rw zero_plus" also works!
end

theorem mult_0_plus_v3: 
    ∀ (a b : nat), mult (plus 0 a) b = mult a b 
:= begin
    intros,
    rw zero_plus, -- does name matching too
end



/-
this is nice, because it matches our intuitive way of doing simplifications by hand. for example, suppose we wanted to show that formulas (a) and (b) below are equivalent:

    (a)    x ∧ ((x → z) ∧ true) ∧ y
    (b)     x ∧ y ∧ (x → z) 

if we did this by hand, we would start with (a), and keep simplifying it until we get (b):

(a)
=
x ∧ ((x → z) ∧ true) ∧ y
= A ∧ true is equivalent to A, so ((x → z) ∧ true) becomes (x → z)
x ∧ (x → z) ∧ y
= (A ∧ B) ↔ (B ∧ A), so (x → z) ∧ y becomes y ∧ (x → z)
x ∧ y ∧ (x → z) 
=
(b)

rw allows us to do exactly that, by rewriting based on theorems we have proved previously:
-/


-- theorems from the LEAN library: USE ONLY WHEN ALLOWED TO!
#check and_self
#check or_self
#check and_comm 
#check or_comm 
#check and_assoc
#check or_assoc 
#check or_false 
#check false_or 
#check or_true 
#check true_or 
#check and_true
#check true_and 
#check and_false 
#check false_and

theorem power_of_rw: 
  ∀ x y z : Prop, x ∧ ((x → z) ∧ true) ∧ y ↔ x ∧ y ∧ (x → z) 
:= begin
    intros,
    rw and_true,  
    rw and_comm, -- oops! I didn't want to rewrite that!
    rw <- and_comm, -- let me undo what i've done
    rw (and_comm y (x → z)), 
end

/-
CAREFUL: rewrite does NOT work with implications! indeed, it should NOT!
-/

theorem trying_rw_on_implies:
    ∀ p q : Prop, p -> (p -> q) -> q
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    try { rw h2 }, -- nothing: p cannot be "rewritten" into q based on h2
    -- instead, we can use modus ponens:
    have h3 := h2 h1,
    assumption,
end








----------------------------------
-- The dangers of overlapping
----------------------------------

-- definition of list_delete without overlapping cases:
def ld : list nat -> nat -> list nat
  | [ ] _ := [ ]
  | (x :: L) 0 := L
  | (x :: L) (nat.succ i) := x :: (ld L i)  -- non-overlapping!
--

example: ld [1,2,3] 2 = [1,2] 
:= begin
  rw ld, -- unnecessary, but does not do any harm
  refl,
end

-- definition of list_delete with overlapping cases:
def ldov : list nat -> nat -> list nat
  | [ ] _ := [ ]
  | (x :: L) 0 := L
  | (x :: L) i := x :: (ldov L (i-1))  -- overlapping!
--

-- this will mess up the rewrite of this function, see below:
example: ldov [1,2,3] 2 = [1,2] 
:= begin
  rw ldov, -- unnecessary, but shouldn't hurt!!! 
  -- ???  how come we got two goals!?  because of overlapping!
  refl,
  intro h,
  trivial, 
end





-----------------------------------------------
-- simplifying equalities with constructors 
-----------------------------------------------

/-
by definition of inductive data types, two elements x and y of such a type T can only be equal if they are built using the same constructor. for example, nat.zero and (nat.succ x) CANNOT be equal, for any x. and also, (nat.succ x) and (nat.succ y) are equal iff x is equal to y. 

the lemma succeq asserts that. (this lemma is proved in ourlibrary11.lean. don't mind how it is proven. you must NOT use tactic "simp" unless we tell you to.)
-/

#check succeq  

-- now we can prove these:

example: ∀ x y : nat,  (nat.succ x) = (nat.succ y) → x = y 
:= begin
    intro,
    intro,
    intro h,
    rw succeq at h,
    assumption,
end

example: ∀ p : Prop, 100 = 200 → p 
:= begin
    intro,
    intro h,
    try {trivial}, -- does nothing!
    rw succeq at h,
    repeat {rw succeq at h},
    trivial, -- now it works!
end



/-
the same principle holds for any inductive data type. for example, [] is not equal to [1], because the former is constructed with list.nil and the latter with list.cons.

the lemma listeq allows us to simplify list equalities:
-/

#check listeq  

-- for example, now we can prove these:

example: ∀ x : ℕ, ∀ L1 L2 : list ℕ, (x :: L1) = (x :: L2) → L1 = L2 
:= begin
    intro,
    intro,
    intro,
    intro h,
    rw listeq at h,
    cases h,
    assumption,
end

example: ∀ x y : ℕ, ∀ L : list ℕ, (x :: L) = (y :: L) → x = y 
:= begin
    intro,
    intro,
    intro,
    intro h,
    rw listeq at h,
    cases h,
    assumption,
end

example: ∀ (x y : ℕ) (L : list ℕ) (p : Prop), x :: y :: L = [x] → p 
:= begin
    intro,
    intro,
    intro,
    intro,
    intro h,
    try {trivial,}, -- does nothing!
    rw listeq at h,
    cases h,
    trivial,
end










-------------------------------------------------------
-- TACTICS, DEDUCTION SYSTEMS, AND THE MEANING OF LOGIC 
-------------------------------------------------------

/- 
TACTICS & DEDUCTION SYSTEMS:

tactics are also known as _inference rules, proof rules, or sequents_. all these are also collectively known as _deduction systems_. we have seen many tactics already (refl, intro, cases, split, left, ...). these tactics manipulate the proof state and help us finish our proofs. 

but what is the _meaning_ of these tactics? are they completely arbitrary? if they are, why not introduce a _superduper_ tactic which just completes any proof? well, that wouldn't be valid, because then we would be able to also proof untrue things, so our logic / proof system would be _unsound_! (more on soundness below)

the tactics that we have are sound because they implement basic inference rules of logic. for example, the _left_ tactic implements the inference rule P ⊢ P ∨ Q. you can read this "backwards", as follows: "if you want to prove P ∨ Q (i.e., if your goal is P ∨ Q) then it suffices to prove P (i.e., it's OK to change your goal to P)". that's exactly what _left_ does. 

the other tactics are similar. _right_ implements the rule Q ⊢ P ∨ Q. _split_ implements the rule "if ⊢ P and ⊢ Q then ⊢ P ∧ Q", which you can read as: "if you prove P and you also prove Q, then you have proven P ∧ Q". in fact, usually the left hand side of the ⊢ symbol contains other hypotheses (these are exactly the hypotheses that we have in our proof states), like:
    H1, H2, H3, ... ⊢ P ∧ Q 
so the above rule is in reality:
    "if H1, H2, H3, ... ⊢ P and H1, H2, H3, ... ⊢ Q then H1, H2, H3, ... ⊢ P ∧ Q",
and similar with the other tactics. 


PROVABILITY:

tactics (like those of LEAN) are formalisms. they have no "meaning" other than that they _implement_ the meaning of ∨, ∧, ¬, ∀, →, etc. so, in a way, inference rules give themselves meaning to logic. it is more correct to say that they give meaning to the notion of _proof_. they define formally what a proof is. they also define what it means for a statement to be _provable_: it is provable if and only if it can be proved using the tactics. provability is the one of the two meanings of logic. 


(SEMANTIC) TRUTH: 

provability says that some proposition P can be proved (using the tactics). but does that really mean that P is "true"? in logic we have not only the notion of proof (which is symbolic/syntactic), but also the notion of semantic truth. how is semantic truth defined? that depends on the logic. in propositional logic, it is defined by truth tables, boolean functions, validity, and satisfiability, as we saw (see 07-propositional-logic.pdf). for example, we can say that the formula P → P is "true" because it's valid. 

in other logics, semantic truth is defined more or less similarly, except that things become a bit more complicated, because we cannot build truth tables, because some things are infinite! for example, consider this first-order logic formula:

    ∀ x, P(x) → P(x) 

intuitively, this formula says "for any x, if P(x) holds, then P(x) holds". this sounds true, but we cannot build a truth table to verify it! first, we don't know what x is. it's a variable, but of what type? second, if x is a nat, say, then x can take infinitely many values. so we cannot build a complete truth table. third, we also don't know what P is! it's a _predicate_, meaning it takes some x and returns true or false, but we don't know how it's defined. in order to define the semantics (truth) of first-order logic, we need to define all these things: the domain of x, the meaning of P, etc. these are called _models_ or _interpretations_. once we define those, we realize that the formula ∀ x, P(x) → P(x) is true in all interpretations! so we say that it is _valid_, just like P → P in propositional logic is valid. 


FIRST-ORDER LOGIC:

there are (many!) other valid formulas in first-order logic, for example:

    ¬ (∀ x, P(x)) ↔ (∃ x, ¬ P(x))

the above formula has both the ∀ and ∃ quantifiers. in this class we will not study the ∃ quantifier much, but in your next homework you will get to think about it a little bit. 


PROVABILITY vs. SEMANTIC TRUTH: SOUNDNESS vs COMPLETENESS

when i prove something, can i be sure that what i proved is really (semantically) true? yes, provided that the deduction system you used to prove your claim is _sound_. as we said earlier:

    soundness: provable → true 

LEAN is sound, unless you find a bug in it! let me know if you do!

the other direction is called _completeness_:

    completeness: true → provable 

LEAN is complete for propositional logic: there is a way to prove any valid formula of the form
     ∀ p q r ... : Prop, ... some boolean expression on p q r ... 

what about completeness for other logics? There are fundamental impossibility results that say that we cannot have both soundness and completeness in general for more powerful logics. we may revisit those results later. 


THE "MEANING" OF LEAN:

LEAN is a deduction system. like any other deduction system, it only "understands" symbols and syntax (proofs). LEAN does not understand semantics. semantics is the domain of human interpretation only. 

this shouldn't shock you. we saw it already when we talked about inductive types like ℕ, mynat, and their constructors. the constructor "nat.zero" is just a symbol. we (humans) take it to mean "0". in fact, "0" itself is just a symbol! in our mind, it means "the number zero". 

in fact, every language, written or oral, is based on symbols. the word "chair" is a symbol. to someone who can read english, this symbol invokes meaning: you read "chair" and you form some image of some chair in your brain. "chair" is the symbol, the image in your brain is its "meaning". 
-/



/- some student asked: is there a way to "break up" an assumption h : p → q ?  we learned modus ponens. but for modus ponens to apply, we need to know that p holds. otherwise we cannot derive q. what if we don't have p? would it be legal to have a tactic, say, tactic _rubbish_ which "breaks up" the assumption p → q into two separate assumptions, one for p, and another for q?

no, that wouldn't be legal: such a tactic would lead to UNSOUNDNESS! how?

first, we can already prove false → false:
-/
lemma lem1: false → false := begin intro, trivial, end 

-- now we can easily derive false on its own:
theorem false_using_rubbish: false :=
begin
    have H := lem1, 
    try {/- rubbish H, -/ }, -- if _rubbish_ were a tactic, this would break up hypothesis H into two hypotheses, h1 : false and h2 : false. 
    try {trivial}, -- then we could just complete the proof with _trivial_
    sorry, -- luckily we don't have _rubbish_ 
end



-------------------------------------------------------
-- FORMAL PROOFS BY HAND: DEDUCTION SYSTEMS
-------------------------------------------------------

/- 
Do we need LEAN in order to do formal proofs? – or any other software, or even computers at all!?

As I often claimed in class, we don't need LEAN, or in fact any other software, or even computers at all! We can do formal proofs "by hand". It's tedious, but it's doable in principle. 

The same holds for any kind of computation, by the way. People did calculations way before computers were invented. Computers "only" made those calculations faster. 

Human "computers" were used by NASA up to at least 1960, c.f. the film: https://en.wikipedia.org/wiki/Hidden_Figures

So how do we actually do formal proofs by hand? Pretty much in the same way we do them with LEAN, except that we have to write things down. An example is given in the slides:

    11-deductions.pdf

This example mimics the LEAN inference rules (tactics): split, intro, cases, left, right, etc. It also uses "em" (excluded middle), "MP" (modus ponens) as an axiom, "contra" as an axiom, and "hyp" as an axiom. 

The set of inference rules that we are allowed to use is called a "deduction system". There are many of those. LEAN is one, but there are many others, and they have been studied in the area of logic: natural deduction, Hilbert-style, Gentzen-style, resolution, ... 

We don't have to know these deduction systems. We already have LEAN. The point is that, in principle, we don't need LEAN, and we should be able to do everything we do in LEAN by hand. 

-/

