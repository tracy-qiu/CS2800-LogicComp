-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary06


---------------------------------------------------------
-- implication
---------------------------------------------------------

-- consider the predefined LEAN division operator on nats:

#eval 4/2 
#eval 4/3 
#eval 3/4 
#eval 2/0 -- a nat divided by 0 yields 0. let's say we don't like that. 

-- let's say we want to define our own function, called "mydivide", which returns -1 when a division by 0 is attempted:
def mydivide (x y : int) : int := if (y = 0) then -1 else x/y 
#check mydivide 

#eval mydivide 2 0 

-- now suppose we want to state the property that mydivide is "almost equivalent" to LEAN's /, specifically, that behaves like "/", provided that the denominator (2nd argument) is not zero. how to write that? we use logical _implication_. as it turns out (and for good reasons, which we will discuss later) the implication symbol is the same "right arrow" -> or → as the one we use for functions:

#check ∀ x y : int, (y ≠ 0) -> (mydivide x y = x/y)

#check ∀ x y : int, implies (y ≠ 0) (mydivide x y = x/y)   
--                             A               B 
--                             A     implies   B
--                             A        ->     B
--                             A        →      B


/- ENGLISH AND IMPLICATION

"A only if B"    =     A -> B
"B if A"         =     A -> B
"A if B"         =     B -> A
"if A then B"    =     A -> B

"A if and only if B"    =   A <-> B  =  A -> B and B -> A 

-/



#check ite  -- this is the "if then else" function, which is different from implies !
#check implies 



-- QUIZ TIME!






----------------------------------------------------
-- LOGIC
----------------------------------------------------
/-
our course is called "logic and computation". you have probably already seen basic logic (propositional logic) previously. in this course we will go further. in fact we have already used more advanced logic statements, with the "for all" quantifier ∀. we also talked briefly about the difference between propositional ("quantifier-free") logic, first-order logic, higher-order logic, and dependent type theory (LEAN). 

logic is important, because it is a precise and formal language, which allows little to no ambiguity. it is therefore the perfect medium to express statements that we want to make about the programs that we write: what does it mean for our program to be correct? what exactly is the "specification" of our program? we can write this spec in english, but that's often inadequate. english (or any other natural language) is not precise enough, and its ambiguities can lead to miscommunication and ultimately errors. 

before returning to proving logical statements with LEAN, let's do a quick review of some basic concepts in logic, starting with propositional logic. 
-/


/-




READ SLIDES: 07-propositional-logic.pdf




-/



---------------------------------------------------------
-- PROOF TACTICS TO DEAL WITH BASIC LOGICAL CONNECTIVES
---------------------------------------------------------

-- logical connectives:

#check implies -- implication, → 
#check and -- conjunction, ∧ 
#check or -- disjunction, ∨ 
#check not -- negation, ¬ 
#check iff -- logical equivalence, ↔ 
#check xor -- exclusive or

--------------------------------
-- intro with implication
--------------------------------

theorem mydivide_divide: 
  ∀ x y : int, y ≠ 0 → mydivide x y = x/y 
:= begin
    intro,
    intro,
    intro, -- WORKS FOR IMPLICATION TOO!
    try {refl},
    sorry,
end
/- as can be seen in the incomplete proof above, the intro tactic also transforms a goal of the form A → B into the goal B, while moving A into the list of hypotheses. this shouldn't shock us. how would we prove A → B by paper and pencil? we would say something like: "Assume A is true. Let us then prove B." that's exactly what intro does. the "Assume A is true" part is moving A into the hypotheses. the "Let's then prove B" part is the new goal B. 

you will also notice in the example above that A was not just moved into the hypotheses, but it was also given a "label". indeed, the hypotheses now include*

a : y ≠ 0

and not just "y ≠ 0". why is that? for now, think of "a" as simply a label which allows us to refer to the hypothesis y ≠ 0. later, we will discover that this is really the same thing as "a has type blabla". but for now, let's just think of the "a" above as just a label. 

* NOTE: depending on your computer's fonts, etc, LEAN might decide to give another label to y ≠ 0, and not "a". to avoid not knowing which label LEAN will decide to assign, which might lead to not being able to share proofs, we will assign the label ourselves. we can do that with "intro h":
-/

theorem mydivide_divide_correctly_labeled: 
  ∀ x y : int, y ≠ 0 → mydivide x y = x/y 
:= begin
    intro,
    intro,
    intro h, -- we will use h, h1, h2, ..., H, H1, H2, ... for labeling hypotheses
    try {refl},
    sorry,
end


-- can we now prove this?
example: ∀ x : ℕ, x ≠ 0 → x = x 
:= begin
    intro,
    intro h,
    refl,
end

-- the above example is silly because the assumption x ≠ 0 is not needed to prove the conclusion. but what about this?
example: ∀ x : ℕ, x ≠ 0 → x ≠ 0 
:= begin
    intro,
    intro h,
    -- now what?
    try {refl,}, -- does nothing 
    sorry, 
end


/- if we already have the goal in our list of hypotheses, we can use one of these tactics:
-/

----------------------------------------------------
-- trivial, assumption, exact
----------------------------------------------------

example: ∀ x : ℕ, x ≠ 0 → x ≠ 0 
:= begin
    intro,
    intro h,
    trivial,
end

example: ∀ x : ℕ, x ≠ 0 → x ≠ 0 
:= begin
    intro,
    intro h,
    assumption,
end

example: ∀ x : ℕ, x ≠ 0 → x ≠ 0 
:= begin
    intro,
    intro h,
    exact h,
end


/-
but notice that P → P should hold for _any_ statement P, that is, for any proposition P! can we prove that? yes:
-/

theorem p_implies_p: ∀ P : Prop, P → P
:= begin
    intro,
    intro h,
    assumption, -- or "trivial", or "exact h" 
end

/-
this is powerful, because it allows us to prove things like P → P once and for all for any P, instead of separately proving x = 1 → x = 1, x = 2 → x = 2, x+1>0 → x+1>0, etc. 

so from now on, we will illustrate how to deal with basic logical connectives by proving general logical statements involving Props. this will be very useful later on, because concrete theorems about programs will often have a _propositional skeleton_ (or _logical skeleton_) which maps to a basic theorem of logic. for example, the statement "∀ x : ℕ, x = 0 ∨ x ≠ 0" maps to the purely logical statement "∀ p : Prop, p ∨ ¬ p". we will see how to use propositional skeletons later. let us now return to our basic logical connectives. we continue with implication. 
-/



---------------------------------------------------------
-- implication continued 
---------------------------------------------------------

-- just like in types, the implications A → B → C are interpreted as A → (B → C), that is, "A implies (B implies C)", or in other words, "if A holds, then if B holds then C must hold". so, in the case of P → P → P, this gives "if P holds, then if P holds then P must hold", which is true: 
theorem p_implies__p_implies_p: ∀ P : Prop, P → (P → P)
:= begin
    intro,
    intro h1,
    intro h2,
    assumption,
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


