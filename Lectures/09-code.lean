-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary06

/-
    FOR SECTION 5: read the parts we didn't get to cover in last lecture:
    -- equality = in propositional logic
    -- PROPOSITIONAL LOGIC IN LEAN 
    -- PROVING TAUTOLOGIES using Props vs using bools
    -- SUMMARY OF TACTICS
    -- rewrite revisited 

-/




-- TIME FOR SOME PRACTICE!!! 

-- ERASE ALL PROOFS AND TRY THEM ON YOUR OWN!

-- practice is the way to learn!


-- let's apply all the stuff we have learned so far:

lemma p_and_true: ∀ P : Prop, (P ∧ true) ↔ P 
:= begin
    intro, 
    split,
    {
        intro h,
        cases h with h1 h2, 
        assumption,
    },
    {
        intro h, 
        split,
        {
            assumption,
        },
        {
            trivial, 
        }
    }
end 


lemma p_or_true: ∀ P : Prop, (P ∨ true) ↔ true
:= begin
    intro, 
    split, 
    {
        intro h, 
        trivial,
    },
    {
        intro h, 
        right, 
        trivial,
    }
end 


lemma p_and_q_implies_q_and_p: ∀ p q : Prop, (p ∧ q) → (q ∧ p) 
:= begin
    intro, 

end 











lemma p_and_true: ∀ P : Prop, (P ∧ true) ↔ P 
:= begin
    intro,
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
        trivial,
    },
end



lemma p_or_true: ∀ P : Prop, (P ∨ true) ↔ true 
:= begin
    intro,
    split,
    {
        intro h,
        trivial,
    },
    {
        intro h,
        right,
        trivial,
    },
end


theorem p_and_q_implies_q_and_p: ∀ p q : Prop, (p ∧ q) → (q ∧ p) 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    split,
    assumption,
    assumption,
end



/-  THEOREMS ARE FUNCTIONS, PROPOSITIONS ARE TYPES!

what is a theorem, really? what is a proposition? one amazing fact linking logic and computer science, theorem proving and programming, is that theorems are functions and propositions are types! although we will not delve into the theory of this fundamental insight, we will use it extensively in practice. in particular, when we "appeal" to other theorems or lemmas, we will be essentially "calling" those theorems/lemmas as if they were functions! let us now explain these insights: 
-/

#check plus -- defined in ourlibrary06.lean imported above 

-- recall this theorem that we have already proved:
theorem zero_plus0: ∀ x : nat, plus 0 x = x 
:= begin
    intro,
    refl,
end



-- first, the keyword "theorem" is just syntactic sugar for "def":
def zero_plus1: ∀ x : nat, plus 0 x = x 
:= begin
    intro,
    refl,
end

-- second, we can replace the ∀ (forall) with an argument:
def zero_plus2  (x : nat) : plus 0 x = x 
:= begin 
    -- now we don't have to say _intro_ anymore, because x : nat is already introduced !
    refl,
end

/- the above looks a lot like a function definition, where x of type nat is the input argument. but what is the return type? the return type is actually "plus 0 x = x". recall that the latter is a "proposition" (a Prop). this is another fundamental insight, that "propositions are types"! 

but if zero_plus2 is actually a function which returns something of type "plus 0 x = x", what exactly is that returned object? it's a proof! in general, if we have a proposition P, i.e., if P : Prop (P is of type Prop) and if we manage to construct an object H of type P, i.e., H : P, then H can be considered a proof of P. and in that case, we can consider that we have proven P. this should now make clearer the meaning of things like "h : P" in the list of hypotheses in our proof states! 

if all this sounds too vague and abstract right now, don't worry. this is normal at this stage. we will see applications of all these concepts soon. 

now, you might object that the body of this "function-theorem" looks very different from the bodies of functions that we defined so far. functions don't have "begin ... end" sections. also functions don't have "calls" to tactics like "reflexivity". so is our "function-theorem" really a function? 

the answer is yes! in fact, the "begin ... end" section with all its tactics is not strictly necessary. the same theorem can be proven by a different kind of "proof":

(zeroplus2 42) : plus 0 42 = 42 
    expression       type (prop that it proves)
this expression is a proof of that type 
every proposition if a type 
-/

def zero_plus3  (x : nat) : plus 0 x = x := eq.refl (plus 0 x)
-- the above proof ("eq.refl (plus 0 x)") basically appeals to the same reflexivity-of-equality rule: eq.refl is the theorem/function implementing that rule:

#check eq.refl -- you can think of eq.refl as an _axiom_ (something which is taken for granted without need to be proven) or as a theorem which has already been proven in the LEAN library. in both cases, we "appeal to" ("call") that existing result.

/- now zero_plus3 really looks like a normal function, which in its body calls two other functions, namely, plus and eq.refl. plus is a function that we defined, while eq.refl is a predefined function. given what we said above, you can think of eq.refl as the function that takes as input a term "A" and returns as output a proof that A = A. and zero_plus1 is a function that takes as input x of type nat, and returns a proof that (plus 0 x) equals x. 
-/

-- as an extra indication that the above three definitions are the same, looking at the types (signatures) below, we see that they are all identical:
#check zero_plus0 
#check zero_plus1 
#check zero_plus2  
#check zero_plus3 

-- in fact, we can show that the above are all identical:
example: zero_plus0 = zero_plus1 := begin refl, end 
example: zero_plus0 = zero_plus2 := begin refl, end 
example: zero_plus0 = zero_plus3 := begin refl, end 


/- now, looking at the definition of zero_plus1 vs. the one of zero_plus3, i think we will agree that the latter is not very readable, as a theorem with its proof. we will therefore use the "theorem ... begin ... end" style, instead of the "def ..." style, when defining and proving our theorems.
-/

/- besides being just awesome, the theorems = functions insight is also useful, in many ways. in particular, we will use it all the time when we apply/use existing results (theorems or lemmas that we have proven, or predefined axioms), to prove new results. in such cases, it is really helpful to think of applying an existing theorem in the same way as calling a function. here's a simple example of that:
-/

-- let's suppose we want to prove that 0 + 3 = 3. we can prove this directly:
example: plus 0 3 = 3 := begin refl, end 

-- but we can also prove it by using (or "instantiating" or "applying" or "calling") any of the zero_plus theorems above:
example: plus 0 3 = 3 := zero_plus0 3 
example: plus 0 3 = 3 := zero_plus1 3 
example: plus 0 3 = 3 := zero_plus2 3 
example: plus 0 3 = 3 := zero_plus3 3 

#check zero_plus0 
#check zero_plus0 333

/- we will soon see other ways of "calling" previously proven theorems/lemmas within _begin_ ... _end_ blocks, using the tactic _have_. 
-/

-- see more at https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html




-- MODUS PONENS
/- the famous modus ponens rule of logic says that if we know that A is true, and that A implies B, then we know that B is also true. let's see an illustration of this principle and at the same time see an application of the propositions-as-types principle. first, we introduce some convenience mechanisms that we haven't seen yet:
-/

section local_definitions   

variable x : ℕ      -- let's assume that x is a nat 
variable f : ℕ → bool  -- let's assume that f is a function from nat to bool

#check (f x)      -- then (f x), the application of f to x, is of type bool

end local_definitions



section modus_ponens   

variable P : Prop   -- let's assume that P is a proposition, i.e., a Prop
variable Q : Prop   -- let's assume that Q is also a Prop 

variable h1 : P     -- let's assume that P holds, i.e., that h1 is of type P (h1 can be seen as a proof that P is true)
variable h2 : P → Q -- let's assume that P → Q holds, i.e., that h2 is of type P → Q (h2 is a proof that P implies Q)

#check h2   -- notice how h2 looks very much like a function. in fact it is! h2 can be seen as a function from P to Q: h2 takes as input a proof that P holds, and returns as output a proof that Q holds!  WOW!


#check (h2 h1)      -- then (h2 h1), the application of h2 to h1, is of type Q, meaning that we have now constructed a proof that Q holds !!! 

/-
this should now also clarify why the logical implication symbol -> (or →) is exactly the same as the arrow in type definitions like f : ℕ → bool !!!
-/

end modus_ponens




----------------------------------------------------
-- have 
----------------------------------------------------

/-
the _have_ tactic allows us to do what we did above, but within the usual begin ... end block that we employ for proofs:
-/

theorem modus_ponens: ∀ P Q : Prop, ((P → Q) ∧ P) → Q 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,  -- we can use cases with renaming the labels to what we want
    -- at this point we know that P is true, and also that P → Q is true. how can we derive Q from these two hypotheses?
    have h3 : Q := h1 h2, /- the _have_ tactic allows to add new hypotheses in the list of hypotheses. here we are adding a new hypothesis, namely, that Q holds. h3 can be seen as just a label for this new hypothesis. but given what we said above, h3 can also be seen as a proof that Q holds. now, we cannot just add whatever hypothesis we want without justification. this would render our proof system useless (in fact, unsound). therefore, whenever we claim to have found say h3 of type Q, we _must_ provide a proof for Q. in other words, we must define the proof h3. we do that using := followed by either "begin ... end" and the usual tactics that we know, or by application of other known facts, as in the example above. 
    -/
    -- now that we have derived Q in the hypotheses, we can conclude the proof:
    assumption,
end

-- here's another formulation of the modus ponens rule, which also illustrates the fact that (A ∧ B) → C is equivalent to A → (B → C), which is the same as A → B → C:

theorem modus_ponens_with_implications: ∀ P Q : Prop, P → ((P → Q) → Q) 
:= begin
    intro, 
    intro,
    intro h1, 
    intro h2,   
    have h3 := h2 h1,  -- the type Q of H3 can be omitted 
    assumption,
end




-- practice: use "have" to prove this:
theorem not_p_and_not_p: ∀ P : Prop, ¬ (P ∧ ¬P) 
:= begin
    intro,
    intro h,
    cases h with h1 h2,
    -- now recall that ¬P is the same as P → false:
    dunfold not at h2,
    -- therefore, we can apply modus ponens:
    have h3 : false := h2 h1,
    trivial,
end



----------------------------------------------------
-- CALLING LEMMAS & THEOREMS LIKE FUNCTIONS
----------------------------------------------------

/-
we are now able to see how we can use previously proven lemmas or theorems, in order to prove new lemmas or theorems. we can simply "call" those existing (proven) lemmas/theorems like functions (because that's what they are!). we can call them inside the proofs of our new lemmas/theorems using "have": 
-/

-- we re-prove ¬ (P ∧ ¬P) by "calling" the previously proven theorem "modus_ponens_with_implications":
theorem not_p_and_not_p_bis: ∀ P : Prop, ¬ (P ∧ ¬P) 
:= begin
    intro,
    intro h,
    cases h with h1 h2,
    dunfold not at h2, -- not needed, should remember what ¬ is 
    have h3 : false := modus_ponens_with_implications P false h1 h2,
    /- to see what's going on in the above line, remove the ": false" part, and observe what happens as you start with just this:

    have h3 := modus_ponens_with_implications,

    and then keep adding arguments one by one to modus_ponens_with_implications:

    have h3 := modus_ponens_with_implications P,

    have h3 := modus_ponens_with_implications P false,

    have h3 := modus_ponens_with_implications P false h1, 

    have h3 := modus_ponens_with_implications P false h1 h2,
    -/
    trivial,
end


-- we can also do it in multiple steps:
theorem not_p_and_not_p_tris: ∀ P : Prop, ¬ (P ∧ ¬P) 
:= begin
    intro,
    intro h,
    cases h with h1 h2,
    -- in multiple steps:
    have h3 := modus_ponens_with_implications,
    have h4 := h3 P,
    have h5 := h4 false,
    have h6 := h5 h1,
    have h7 := h6 h2,
    trivial,
end








-- practice: ERASE ALL PROOFS AND TRY THEM ON YOUR OWN!

theorem thm1: ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
-- try to prove this directly:
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    assumption,
end

theorem p_and_q_implies_p: ∀ p q : Prop, (p ∧ q) → p 
:= begin
    intro,
    intro,
    intro h,
    cases h with h1 h2,
    assumption,
end

theorem thm2: ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
-- proof by "calling" theorem p_and_q_implies_p:
:= begin
    intro,
    intro,
    intro h1,
    have h2 := p_and_q_implies_p (x > 0) (y > 0) h1,
    assumption,
end


theorem thm3: ∀ x y : ℕ, x > 0 ∧ y > 0 → x > 0 
-- same proof but calling happens in multiple steps:
:= begin
    intro,
    intro,
    intro h,
    have h1 := p_and_q_implies_p,
    have h2 := h1 (x > 0),
    have h3 := h2 (y > 0),
    have h4 := h3 h, 
    assumption,
end



theorem thm4: ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
:= begin
    intro,
    intro,
    have h := p_and_q_implies_p (x > 0) (y > 0),
    -- we could also stop here and just issue assumption: 
    assumption,
end


theorem thm1: ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
-- try to prove this directly:
:= begin
    intro,
    intro,
    intro h,
    cases h, 
    assumption,
end

theorem p_and_q_implies_p': ∀ p q : Prop, (p ∧ q) → p 
:= begin
   intro, 
   intro, 
   intro h, 
   cases h, 
   assumption, 
end

theorem thm2': ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
-- proof by "calling" theorem p_and_q_implies_p:
:= begin
    intros x y, 
    have h := p_and_q_implies_p (x > 0) (y > 0),
    assumption
end


theorem thm3': ∀ x y : ℕ, x > 0 ∧ y > 0 → x > 0 
-- same proof but calling happens in multiple steps:
:= begin
    intro, 
    
end



theorem thm4': ∀ x y : ℕ, (x > 0 ∧ y > 0) → x > 0 
:= begin
    
end

