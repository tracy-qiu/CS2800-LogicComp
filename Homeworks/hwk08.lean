-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 8

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Tracy Qiu, Anushka Mantri, Erica Sammarco
-/




/-
Technical instructions: same as in the last homework plus ADDITIONAL INSTRUCTIONS:

you are NOT allowed to use functional induction in this homework. 
-/


/- IMPORTANT: 

for ALL problems in this and following homework sets, you should do two things: 

first, try to prove whatever it is you are proving _without_ induction. you don't always need induction. you often do, but not always. if you did use induction in your proof, go back and check: did you ever actually use the induction hypothesis? if you didn't, you don't need induction. go back and remove it from your proof (e.g., replace it by cases) and see whether you can complete the proof without induction. 

second, every time you use induction, try to MANUALLY GENERATE the following without LEAN's help:
1. BASE CASE(S)
2. INDUCTION STEP(S)
3. INDUCTION HYPOTHESI(E)S 

then you can check to see whether what you got is the same thing as what LEAN generates. if they are not the same, ask yourselves why. 

YOU WILL BE ASKED TO DO THIS TYPE OF MANUAL GENERATION IN EXAMS AND QUIZZES!
-/

import .ourlibrary11 
import .ourlibrary12 
import .ourlibrary14 



/- HWK08-01: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem mult_1_x: ∀ x : ℕ, mult 1 x = x
-- ANSWER:
:= begin
  intro x, 
  cases x, 
  {
    refl, 
  },
  {
    dunfold mult, 
    rw plus_x_zero,
  }
end 

/- HWK08-02: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem mult_2_x: ∀ x : ℕ, mult 2 x = plus x x
-- ANSWER:
:= begin
  intro x, 
  cases x,
  {
    refl, 
  },
  {
    dunfold mult, 
    rw plus_x_zero, 
  }
end

/- HWK08-03: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem genzeros_n_len_n: ∀ n : ℕ, len (genzeros n) = n 
-- ANSWER:
:= begin
  intro n, 
  induction n with x ih, 
  {
    refl, 
  },
  {
    dunfold genzeros, 
    dunfold len, 
    rw ih, 
  }
end 
       
/- HWK08-04: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem map_identity: ∀ L : list ℕ, apply L (λ x, x) = L 
-- ANSWER:
:= begin
  intro L, 
  induction L with x L' ih, 
  {
    refl, 
  },
  {
    dunfold apply, 
    rw listeq, 
    split, 
    {
      trivial, 
    },
    {
      assumption, 
    }
  }
end   

/- HWK08-05: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem even_double: ∀ x : ℕ, even (double x) = tt 
-- ANSWER:
:= begin
  intro x, 
  induction x with y ih, 
  {
    refl, 
  },
  {
    dunfold double, 
    dunfold even, 
    assumption, 
  }
end

/- HWK08-06:
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem plus_assoc: 
    ∀ x y z : ℕ, plus x (plus y z) = plus (plus x y) z 
-- ANSWER:
:= begin
  intros x y z, 
  induction x with x' ih, 
  {
    refl, 
  },
  {
    dunfold plus, 
    rw succeq, 
    assumption, 
  }
end

/- HWK08-07:
is the claim below true? if so prove it, if not, exhibit a counterexample:

theorem rev_app_distr: ∀ L1 L2 : list ℕ,
    rev (app L1 L2) = app (rev L2) (rev L1) 

-/
-- ANSWER: 

theorem app_assoc: ∀ L1 L2 L3 : list ℕ, app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
  intros L1 L2 L3,
  induction L1 with x L4 ih,
  {
    refl,
  },
  {
    dunfold app,
    rw ih,
  }
end

theorem rev_app_distr: ∀ L1 L2 : list ℕ,
    rev (app L1 L2) = app (rev L2) (rev L1) 
:= begin
  intros L1 L2,
  induction L1 with x L3 ih,
  {
    dunfold app,
    dunfold rev,
    rw app_L_nil,
  },
  {
    dunfold app,
    dunfold rev,
    rw ih,
    rw app_assoc,
  }
end   

/- HWK08-08:
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem rev_involutive : ∀ L : list nat, rev (rev L) = L 
-- ANSWER:
:= begin
  intros L, 
  induction L with x L' ih, 
  {
    dunfold rev, 
    refl, 
  },
  { 
    dunfold rev, 
    rw rev_app_distr,
    rw ih, 
    dunfold rev, 
    refl, 
  }
end

/- HWK08-09:
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
theorem rev_left_right: ∀ L1 L2 : list nat, rev L1 = L2 → L1 = rev L2 
-- ANSWER:
:= begin 
  intros L1 L2, 
  intro h, 
  cases L1, 
  {
    dunfold rev at h, 
    rw <- h, 
    refl, 
  },
  {
    dunfold rev at h, 
    rw <- h, 
    rw rev_app_distr, 
    rw rev_involutive,
    dunfold rev,
    refl,
  }
end


/- HWK08-10:
is the claim below true? if so prove it, if not, exhibit a counterexample:

theorem rev_length: ∀ L : list ℕ, len (rev L) = len L 

-/
-- ANSWER: 

lemma len_app_distrib: ∀ x : ℕ , ∀ L: list ℕ, len (app L [x]) = len L + len [x]
:= begin
  intros x L, 
  induction L with y L' ih, 
  {
    refl, 
  },
  {
    dunfold app, 
    dunfold len, 
    rw succeq, 
    rw ih, 
    refl,  
  }
end


theorem rev_length: ∀ L : list ℕ, len (rev L) = len L 
:= begin
  intro L, 
  induction L with x L' ih, 
  {
    refl, 
  },
  {
    dunfold len, 
    dunfold rev, 
    have h1 := len_app_distrib x (rev L'),
    rw h1, 
    dunfold len, 
    rw succeq, 
    assumption, 
  }
end 

/- HWK08-11:
is the claim below true? if so prove it, if not, exhibit a counterexample:

theorem mult_commut: ∀ x y : ℕ, mult x y = mult y x 

-/
-- ANSWER: 

lemma plus_y_succ_z: ∀ y z : ℕ, nat.succ (plus y z) = plus y (nat.succ z) 
:= begin
  intros,
  induction y with w ih,
  {
    refl,
  },
  {
    dunfold plus,
    rw ih,
  }
end

theorem plus_commut: ∀ x y : ℕ, plus x y = plus y x 
:= begin
  intros,
  induction x with z ih,
  {
    rw plus_x_zero, 
    refl,
  },
  {
    dunfold plus,
    rw ih,
    rw plus_y_succ_z, 
  }
end

theorem mult_x_zero: ∀ x : ℕ, mult x 0 = 0 
:= begin
  intros,
  induction x with y,
  {
    refl,
  },
  {
    unfold mult,
    rw x_ih,
    refl,
  }
end

lemma mult_lemma: ∀ y z : ℕ, plus y (mult y z) = mult y z.succ
:= begin 
  intros y z, 
  induction y with x ih,
  {
    dunfold plus,
    refl,
  },
  {
    dunfold mult, 
    dunfold plus, 
    rw succeq, 
    rw <- ih, 
    rw plus_assoc, 
    rw plus_assoc, 
    rw plus_commut x z,
  }
end 

theorem mult_commut: ∀ x y : ℕ, mult x y = mult y x 
:= begin 
  intros x y, 
  induction x with z ih, 
  {
    dunfold mult, 
    rw mult_x_zero,
  },
  {
    dunfold mult, 
    rw ih, 
    rw mult_lemma,
  }
end

/- HWK08-12:
 prove app_assoc4:

HINT: There is a (really really) short proof for this one. If you find yourself getting tangled up, step back and try to look for a simpler way. 
-/

theorem app_assoc4: ∀ L1 L2 L3 L4 : list nat, 
    app L1 (app L2 (app L3 L4)) = app (app (app L1 L2) L3) L4 
:= begin
-- ANSWER:
  intros L1 L2 L3 L4, 
  rw app_assoc,
  rw app_assoc,
end


/- HWK08-13:
 prove that functions even and even_v2 are equivalent:

 theorem even_equiv_even_v2: ∀ x : ℕ, even x = even_v2 x 

-/
-- defined in library:
#check even 
#check even_v2 

-- ANSWER: 
theorem negb_involutive : ∀ x : bool, negb (negb x) = x 
:= begin
  intro,
  cases x, 
  {
    refl,
  },
  { 
    refl,
  }
end

lemma even_succ_even_negb : ∀ y : ℕ, even y.succ = negb (even y)
:= begin 
  intros, 
  induction y with x ih, 
  {
    refl, 
  },
  {
    rw ih, 
    rw negb_involutive,
    refl,
  }
end 

theorem even_equiv_even_v2: ∀ x : ℕ, even x = even_v2 x 
:= begin 
  intros x, 
  induction x with y ih, 
  {
    refl,
  },
  {
    dunfold even_v2, 
    rw <- ih, 
    rw even_succ_even_negb,
  }
end



/- HWK08-14:
prove that xor is associative. 

theorem xor_assoc: ∀ x y z : Prop, (xor x (xor y z)) ↔ (xor (xor x y) z) 

note: my proof uses many lemmas. 
-/
-- ANSWER:

theorem p_and_not_p_eq_false: ∀ p : Prop, (p ∧ ¬ p) ↔ false 
-- ANSWER: 
:= begin 
  intro p, 
  split, 
  {
    intro h1, 
    cases h1, 
    {
      trivial, 
    },
  },
  {
    intro, 
    trivial, 
  }
end

theorem xor_assoc: ∀ x y z : Prop, (xor x (xor y z)) ↔ (xor (xor x y) z) 
:= begin 
  intros x y z,  
  dunfold xor,
  rw deMorgan_or, 
  rw deMorgan_and, 
  rw deMorgan_and, 
  rw <- not_not z,
  rw <- not_not y,
  rw deMorgan_or,
  rw deMorgan_and,
  rw deMorgan_and,
  rw <- not_not y, 
  rw <- not_not x,
  rw and_distrib_or (¬x ∨ y) (¬y) x,
  rw and_comm (¬x ∨ y) ¬y, 
  rw and_distrib_or (¬y) (¬x) y, 
  rw and_comm (¬y) y, 
  rw p_and_not_p_eq_false y,
  rw or_false, 
  rw and_comm (¬x ∨ y) x, 
  rw and_distrib_or x (¬x) y, 
  rw p_and_not_p_eq_false x,
  rw or_comm false (x ∧ y),
  rw or_false, 
  rw and_comm, 
  rw and_distrib_or,
  rw and_distrib_or, 
  rw and_comm (y ∧ ¬z ∨ z ∧ ¬y) (¬x), 
  rw and_distrib_or (¬x) (y ∧ ¬z) (z ∧ ¬y), 
  rw and_comm (¬y ∨ z) ¬z, 
  rw and_distrib_or, 
  rw and_comm (¬y ∨ z) y, 
  rw and_distrib_or, 
  rw and_comm (¬z) z,
  rw p_and_not_p_eq_false z, 
  rw or_false, 
  rw p_and_not_p_eq_false y,
  rw or_comm false (y ∧ z), 
  rw or_false, 
  rw and_comm, 
  rw and_distrib_or, 
  rw or_assoc, 
  rw and_comm (x ∧ ¬y ∨ y ∧ ¬x) ¬z,
  rw and_distrib_or,
  rw or_assoc, 
  rw and_comm (¬z) (x ∧ ¬y),
  rw and_assoc, 
  rw and_comm (¬z) (¬y),
  rw or_comm (¬z ∧ y ∧ ¬x) (z ∧ ¬y ∧ ¬x ∨ z ∧ x ∧ y),
  rw or_comm (z ∧ ¬y ∧ ¬x) (z ∧ x ∧ y), 
  rw or_assoc, 
  rw and_comm z (x ∧ y),
  rw and_assoc, 
  rw or_comm (z ∧ ¬y ∧ ¬x) (¬z ∧ y ∧ ¬x),
  rw and_comm (¬z) (y ∧ ¬x),
  rw and_comm y ¬x,
  rw and_assoc, 
  rw and_comm z (¬y ∧ ¬x),
  rw and_comm (¬y) (¬x),
  rw and_assoc, 
  rw and_comm (¬y) z, 
end 



/- HWK08-15: 

in this problem we will formalize the so-called "drinker's paradox" which goes like this: "There is someone in the pub such that, if they are drinking milk, then everyone in the pub is drinking milk." write a LEAN theorem expressing this fact. do not prove the theorem, just state it. 

notes: 
  - you can represent people in the pub by nats, so that "everyone in the pub" can be written as ∀ x : ℕ 
  - use the existential quantifier ∃ (exists) for "there is someone" 
  - you can represent the fact that someone drinks milk as a predicate Milk : ℕ → Prop, so that (Milk x) holds if x drinks milk, otherwise (Milk x) does not hold
  - think about why this statement is true (it is!) and notice that the truth of the statement doesn't depend on what everyone is drinking: milk, water, vodka, or anything else! so in fact the statement holds for _any_ predicate Drinks : ℕ → Prop. use the higher-order capability of LEAN to quantify your claim over all possible such predicates. 

you don't have to prove the theorem. just state it. (for those of you who are curious and want to go further, the theorem can be proven using LEAN's exists.elim axiom and existsi tactic.) 
-/

-- ANSWER:
theorem drinker: ∃ x : ℕ, ∀ Drinks: ℕ → Prop, (Drinks x) → ∀ y : ℕ, (Drinks y)
:= begin
  sorry,
end

/- HWK08-16-1:
define the finite inductive type "binop" which represents the 5 binary logical connectives: "and", "or", "imp" (implies), "iff", "xor". use these 5 names for the constructors of "binop". 
-/

inductive binop : Type 
-- ANSWER:
  | and : binop  
  | or : binop 
  | imp : binop 
  | iff : binop 
  | xor : binop
--

/- HWK08-16-2:
define the inductive type "bx" which represents all boolean expressions. bx will have 4 constructors, corresponding to the following 4 kinds of boolean expressions:
    1. if b is a bool, then (bxconst b) is a bx  (constant tt or ff) 
    2. if s is a string, then (bxvar s) is a bx  (variable)
    3. if e is a bx then (bxnot e) is a bx 
    4. if o is a binop, and e1 and e2 are both bx, then (bxbin o e1 e2) is a bx
-/
inductive bx : Type 
-- ANSWER:
  | bxconst : bool → bx
  | bxvar : string → bx
  | bxnot : bx → bx
  | bxbin : binop → bx → bx → bx
--

open binop
open bx

/- HWK08-16-3:
write each of the boolean expressions below as elements of the type bx:
-/
-- (x → y) → x 
-- ANSWER:
#check (bxbin imp (bxbin imp (bxvar "x") (bxvar "y")) (bxvar "x"))

-- (p ∨ q) ∧ (p ∧ ¬r)
-- ANSWER:
#check (bxbin and (bxbin or (bxvar "p") (bxvar "q")) (bxbin and (bxvar "p") (bxnot (bxvar "r")))) 


