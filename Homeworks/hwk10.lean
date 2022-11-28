-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 10

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Tracy Qiu, Anushka Mantri, Erica Sammarco
-/

/-
Technical instructions: same as in the last homework.

IN THIS HOMEWORK YOU ARE ALLOWED TO USE FUNCTIONAL INDUCTION. (this does NOT imply that you need it). WE WILL CUT POINTS for illegal use of the induction hypothesis in functional induction proofs. 
-/


import .ourlibrary16 
import .ourlibraryite




/- HWK10-01: 
Prove the theorem treesize_len given below:
-/

inductive tree : Type 
  | leaf : ℕ → tree 
  | node : ℕ → tree → tree → tree 
--

open tree 

def treesize : tree → ℕ 
  | (leaf x) := 1 
  | (node x t1 t2) := nat.succ (plus (treesize t1) (treesize t2))
--

def tree2list : tree → list ℕ 
  | (leaf x) := [x] 
  | (node x t1 t2) := x :: (app (tree2list t1) (tree2list t2))
--

-- ANSWER:

lemma len_app_distr: ∀ L1 L2 : list ℕ, len (app L1 L2) = plus (len L1) (len L2) :=
begin
    intro,
    intro,
    induction L1 with h T ih,
    {
        refl,
    },
    {
        dunfold app,
        dunfold len,
        dunfold plus,
        rw ih,
    },
end

theorem treesize_len: ∀ t : tree, treesize t = len (tree2list t) 
  | (leaf x) := begin 
    refl, 
  end 
  | (node x t1 t2) := begin 
    dunfold treesize, 
    rw treesize_len t1,
    rw treesize_len t2, 
    dunfold tree2list, 
    dunfold len, 
    rw succeq, 
    rw len_app_distr,
  end

/- HWK10-02: 
Consider the following function:
-/
def list_delete : list ℕ → ℕ → list ℕ 
    | [] _ := []
    | (x :: L) 0 := L 
    | (x :: L) (nat.succ i) := x :: (list_delete L i)
--

example: list_delete [1,2,3] 0 = [2,3] := begin refl, end 
example: list_delete [1,2,3] 1 = [1,3] := begin refl, end 
example: list_delete [1,2,3] 2 = [1,2] := begin refl, end 
example: list_delete [1,2,3] 3 = [1,2,3] := begin refl, end 


/- HWK10-02-1: 
is the following claim true? if so prove it, if not, exhibit a counterexample:
-/
theorem list_delete_len:
  ∀ (L : list ℕ), list_delete L (len L) = L 
-- ANSWER:
  | [] := begin 
    refl,
  end 
  | (x :: L) := begin 
    dunfold len,
    dunfold list_delete, 
    rw list_delete_len L,      
  end 


/- HWK10-02-2: 
is the following claim true? if so prove it, if not, exhibit a counterexample:
-/

theorem list_delete_outofbounds:
  ∀ (L : list ℕ) (i : ℕ), 
    leq (len L) i = tt → list_delete L i = L 
-- ANSWER:
  | [] _ := begin 
    intro h, 
    refl,
  end 
  | (x :: L) 0 := begin 
    intro h, 
    dunfold len at h,
    dunfold leq at h, 
    trivial, 
  end 
  | (x :: L) (nat.succ i) := begin 
    intro h, 
    dunfold list_delete, 
    dunfold len at h, 
    have h1 := list_delete_outofbounds L i, 
    dunfold leq at h, 
    have h2 := h1 h, 
    rw h2, 
  end 



/- HWK10-03: 

prove the following interesting result about functions on booleans. 

HINT: follow the method in "how not to lose your bool cases", 17-code.lean 
-/
--
theorem bool_fn_applied_thrice: 
    forall (f : bool -> bool) (b : bool), f (f (f b)) = f b
-- ANSWER:
:= begin
  intro f, 
  intro b, 
  have h : f ff = tt ∨ f ff = ff
  := begin
    cases f ff,
    {
      right, 
      refl,
    },
    {
      left,
      refl,
    }
  end,
  have h1 : f tt = ff ∨ f tt = tt
  := begin
    cases f tt,
    {
      left,
      refl, 
    },
    {
      right,
      refl,
    }
  end,

  cases h, 
  {
    cases h1, 
    {
      cases b, 
      {
        rw h, 
        rw h1, 
        rw h,
      },
      {
        rw h1, 
        rw h, 
        rw h1, 
      }
    },
    {
      cases b, 
      {
        rw h, 
        rw h1, 
        rw h1, 
      },
      {
        rw h1, 
        rw h1, 
        rw h1, 
      }
    },
  },
  {
    cases h1, 
    {
      cases b, 
      {
        rw h, 
        rw h, 
        rw h,
      },
      {
        rw h1, 
        rw h, 
        rw h, 
      }
    },
    {
      cases b, 
      {
        rw h, 
        rw h, 
        rw h, 
      },
      {
        rw h1, 
        rw h1, 
        rw h1, 
      }
    },
  },
end

/- HWK10-04: 
define the function "eleml" which takes a nat x and a list of nats L and returns bool tt if x is in L and bool ff otherwise. 

as usual, all given tests must pass. 

also make sure that your eleml satisfies the lemma given below. prove that it does. 
-/
-- ANSWER:
def eleml : nat → list nat → bool 
  | _ [] := ff
  | x (y :: L) := ite (x = y) tt (eleml x L)
-- 

example: eleml 3 [] = ff := begin refl, end 
example: eleml 0 [1,2,3] = ff := begin refl, end 
example: eleml 1 [1,2,3] = tt := begin refl, end
example: eleml 2 [1,2,3] = tt := begin refl, end
example: eleml 3 [1,2,3] = tt := begin refl, end


lemma eleml_app: ∀ x : ℕ, ∀ L1 L2 : list ℕ, 
  eleml x (app L1 L2) = (eleml x L1) || (eleml x L2)
  | _ [] := begin
    intro L2,
    refl,  
  end
  | x (y :: L) := begin
    intro L2, 
    dunfold app, 
    dunfold eleml, 
    have h := classical.em (x = y),
    cases h, 
    {
      have h1 := itetrue (x = y) h bool tt (eleml x (app L L2)),
      rw h1, 
      have h2 := itetrue (x = y) h bool tt (eleml x L),
      rw h2, 
      refl, 
    },
    {
      have h1 := itefalse (x = y) h bool tt (eleml x (app L L2)),
      rw h1,
      have h2 := itefalse (x = y) h bool tt (eleml x L),
      rw h2, 
      have h3 := eleml_app x L L2, 
      exact h3, 
    }
  end




/- HWK10-05: 
define the function "removedups" which takes a list of nats L and removes all duplicate elements from it. 

as usual, all given tests must pass: complete the proofs of the ones given below.  

also make sure that your removedups satisfies the lemma given below. prove that it does. 
-/
-- ANSWER:
def removedups : list nat → list nat 
  | [] := []
  | (x :: L) := ite (eleml x L = tt) (removedups L) (x :: removedups L)
--

example: removedups [] = [] := begin refl, end 
example: removedups [1,2,3] = [1,2,3] := begin refl, end 
example: removedups [1,2,3,3] = [1,2,3] := begin refl, end 
example: removedups [2,2,1,1,3,3] = [2,1,3] := begin refl, end 
example: removedups [2,1,1,2,3,2] = [1,2,3] 
        ∨ removedups [2,1,1,2,3,2] = [1,3,2] 
        ∨ removedups [2,1,1,2,3,2] = [2,1,3] 
:= begin 
  right, 
  left, 
  refl
end 


lemma eleml_removedups: ∀ x : ℕ, ∀ L : list ℕ, 
  eleml x (removedups L) = eleml x L  
  | _ [] := begin 
    refl, 
  end
  | x (y :: L) := begin 
    dunfold eleml,
    dunfold removedups,
    have h1 := classical.em (x = y),
    have h2 := classical.em (eleml y L = tt),
    cases h1,
    {
      have h3 := itetrue (x = y) h1 (bool) tt (eleml x L),
      rw h3, 
      cases h2, 
      {
        have h4 := itetrue (eleml y L = tt) h2 (list ℕ) (removedups L) (y :: removedups L),
        rw h4, 
        rw eleml_removedups x, 
        rw h1,
        exact h2,
      },
      {
        have h5 := itefalse (eleml y L = tt) h2 (list ℕ) (removedups L) (y :: removedups L),
        rw h5,
        dunfold eleml,
        have h6 := itetrue (x = y) h1 (bool) tt (eleml x (removedups L)),
        rw h6,
      }
    },
    {
      have h3 := itefalse (x = y) h1 (bool) tt (eleml x L),
      rw h3, 
      cases h2, 
      {
        have h4 := itetrue (eleml y L = tt) h2 (list ℕ) (removedups L) (y :: removedups L),
        rw h4, 
        rw eleml_removedups,
      },
      {
        have h5 := itefalse (eleml y L = tt) h2 (list ℕ) (removedups L) (y :: removedups L),
        rw h5, 
        dunfold eleml,
        have h6 := itefalse (x = y) h1 (bool) tt (eleml x (removedups L)),
        rw h6, 
        rw eleml_removedups,
      }
    }
  end


/-
we are now starting to build our SAT solver!

we first introduce our boolean expressions, with a small change: vars are now constructed with nats. we can discuss why in class. 
-/

inductive binop : Type 
  | and : binop 
  | or  : binop 
  | imp : binop 
  | iff : binop 
  | xor : binop 
--

inductive bx : Type 
  | bxconst : bool → bx 
  | bxvar : nat → bx 
  | bxnot : bx → bx 
  | bxbin : binop → bx → bx → bx   -- binary operator 
--

open bx 

-- you will probably need to use this simplification function later
def bx_and_simp : bx → bx 
  | (bxconst b) := (bxconst b) 
  | (bxvar n) := (bxvar n)
  | (bxnot e) := (bxnot e)
  | (bxbin binop.and (bxconst tt) e2) := bx_and_simp e2 
  | (bxbin binop.and e1 (bxconst tt)) := bx_and_simp e1 
  | (bxbin binop.and (bxconst ff) e2) := (bxconst ff)
  | (bxbin binop.and e1 (bxconst ff)) := (bxconst ff)
  | (bxbin o e1 e2) := bxbin o (bx_and_simp e1) (bx_and_simp e2)
--

/-
notation is supposed to make your life easier. you can use the definitions below (for older or more recent LEAN versions). 

if notation does not work for you, you can remove it, but you need to adapt all subsequent tests! 
-/

-- local notation `T` := bx.bxconst tt
-- local notation `F` := bx.bxconst ff
-- local notation `x` n := bx.bxvar n
-- local notation `~` a := bx.bxnot a
-- local notation  a ` => ` b := bx.bxbin binop.imp a b
-- local notation  a ` ⬝ ` b := bx.bxbin binop.and a b
-- local notation  a ` + ` b := bx.bxbin binop.or a b
-- local notation  a ` <=> ` b := bx.bxbin binop.iff a b
-- local notation  a ` ⊕ ` b := bx.bxbin binop.xor a b
--  or in recent LEAN versions:
local notation (name := b_const_t) `T` := bx.bxconst tt
local notation (name := b_const_f) `F` := bx.bxconst ff
local notation (name := b_var) `x` n := bx.bxvar n
local notation (name := b_not) `~` a := bx.bxnot a
local notation (name := b_imp)  a ` => ` b := bx.bxbin binop.imp a b
local notation (name := b_and)  a ` ⬝ ` b := bx.bxbin binop.and a b
local notation (name := b_or)  a ` + ` b := bx.bxbin binop.or a b
local notation (name := b_iff)  a ` <=> ` b := bx.bxbin binop.iff a b
local notation (name := b_xor)  a ` ⊕ ` b := bx.bxbin binop.xor a b


-- a boolean expression written without notation:
#check bx.bxbin binop.and (bx.bxbin binop.or (bx.bxvar 1) (bx.bxvar 2)) (bx.bxbin binop.imp (bx.bxvar 1) (bx.bxnot (bx.bxvar 2)))
-- the same boolean expression written with notation:
#check ((x 1) + x 2) ⬝ (x 1 => ~x 2) 



open bx 



/- HWK10-06: 

define a function bxvars : bx → list nat, which takes as input a bx e and returns the list of all variables (variable IDs) appearing in e. the list should not have duplicates. 

as usual, you are allowed to define your own helper functions. 

as usual all given tests must pass. 

your bxvars must also satisfy all the lemmas given below: prove them. hint: you shouldn't need induction for any of these lemmas. use lemmas, including those proven earlier in this homework. 
-/

-- ANSWER:

def bxvars : bx → list nat
  | (bxconst b) := []
  | (bxvar v) := [v]
  | (bxnot bx) := (bxvars bx)
  | (bxbin bn bx1 bx2) := (removedups (app (bxvars bx1) (bxvars bx2))) 

example: bxvars T = [] := begin refl, end 
example: bxvars F = [] := begin refl, end 
example: bxvars ((F + T) ⬝ (F => ~F)) = [] 
:= begin refl, end 
example: bxvars (((x 1) + x 2) ⬝ (x 1 => ~x 2)) = [1,2] 
:= begin refl, end 
example: bxvars ((T + x 2) ⬝ (x 1 => ~x 2)) = [1,2] 
:= begin refl, end 


lemma bxvars_not: ∀ e : bx, bxvars (bxnot e) = bxvars e 
:= begin
  intro e, 
  dunfold bxvars, 
  trivial, 
end


lemma eleml_bxvars_var_ff: 
∀ n m : ℕ, ∀ e : bx, ∀ o : binop,
  eleml n (bxvars (bxbin o (bxvar m) e)) = ff
    → n ≠ m 
:= begin
  intros n m, 
  intro e, 
  intro o, 
  dunfold bxvars,
  rw eleml_removedups,
  rw eleml_app,
  rw bor_eq_false_eq_eq_ff_and_eq_ff,
  intro h, 
  cases h with h1 h2, 
  dunfold eleml at h1, 
  have h3 := classical.em (n = m),
  cases h3, 
  {
    have h4 := itetrue (n = m) h3 bool tt ff, 
    rw h4 at h1, 
    trivial, 
  },
  {
    assumption, 
  }
end


lemma eleml_bxvars_not_ff: 
∀ n : ℕ, ∀ e1 e2 : bx, ∀ o : binop,
  eleml n (bxvars (bxbin o (bxnot e1) e2)) = ff
    → eleml n (bxvars (bxbin o e1 e2)) = ff 
:= begin
  intros n e1 e2 o, 
  dunfold bxvars, 
  intro h, 
  exact h, 
end


lemma eleml_bxvars_binop_ff: 
∀ e1 e2 : bx, ∀ o : binop, ∀ n : ℕ, 
  eleml n (bxvars (bxbin o e1 e2)) = ff 
    → (eleml n (bxvars e1)) = ff 
        ∧ 
      (eleml n (bxvars e2)) = ff 
:= begin
  intros e1 e2 o n, 
  dunfold bxvars, 
  rw eleml_removedups,
  rw eleml_app, 
  rw bor_eq_false_eq_eq_ff_and_eq_ff,
  intro h, 
  exact h, 
end








/- HWK10-07: 

define a function bxsubst : bx → nat → bool → bx, which takes as input a bx e, a nat n, and a bool b, and returns a new bx f, such that all occurrences of variable with ID n in e are replaced by (bxconst b) in f. if e does not contain variable with ID n, then f is the same as e. 

as usual, all tests given below must pass. your bxsubst also needs to satisfy theorem bxsubst_no_change given below. prove this. hint: use induction on the bx e, and some of the lemmas you proved above. 
-/

-- ANSWER:
def bxsubst : bx → nat → bool → bx 
  | (bxconst b) _ _ := (bxconst b)
  | (bxvar v) n b := ite (v = n) (bxconst b) (bxvar v)
  | (bxnot bx) n b := (bxnot (bxsubst bx n b))
  | (bxbin bn bx1 bx2) n b := (bxbin bn (bxsubst bx1 n b) (bxsubst bx2 n b))
--

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 1 tt 
=  ((T + x 2) ⬝ (T => ~x 2))
:= begin refl, end

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 1 ff 
=  ((F + x 2) ⬝ (F => ~x 2))
:= begin refl, end

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 2 tt 
=  (((x 1) + T) ⬝ ((x 1) => ~T))
:= begin refl, end

example: bxsubst  (((x 1) + x 2) ⬝ (x 1 => ~x 2)) 3 tt 
= (((x 1) + x 2) ⬝ (x 1 => ~x 2))
:= begin refl, end


theorem bxsubst_no_change: ∀ e : bx, ∀ n : ℕ, ∀ b : bool,
  eleml n (bxvars e) = ff → bxsubst e n b = e 
  | (bxconst b) _ _ := begin 
    intro h, 
    dunfold bxvars at h, 
    refl,
  end 
  | (bxvar v) n b := begin 
    intro h, 
    dunfold bxvars at h, 
    dunfold eleml at h, 
    dunfold bxsubst, 
    have h2 := classical.em (v = n),
    cases h2, 
    {
      rw eq_comm at h2, 
      have h3 := itetrue (n = v) h2 bool tt ff, 
      rw h3 at h, 
      trivial, 
    },
    {
      have h3 := itefalse (v = n) h2 bx (bxconst b) (x v), 
      rw h3, 
    }
  end 
  | (bxnot bx) n b := begin 
    intro h,
    dunfold bxsubst,
    rw bxsubst_no_change,
    rw bxvars_not at h,
    assumption,
  end 
    | (bxbin bn bx1 bx2) n b := begin
    intro h, 
    dunfold bxvars at h, 
    rw eleml_removedups at h, 
    rw eleml_app at h, 
    dunfold bxsubst, 
    rw bor_eq_false_eq_eq_ff_and_eq_ff at h, 
    cases h with h1 h2, 
    have h3 := bxsubst_no_change bx1 n b h1,
    rw h3, 
    have h4 := bxsubst_no_change bx2 n b h2,
    rw h4, 
  end





/- HWK10-08: 

define a function bxeval : bx → bool, which takes as input a bx e without any variables, and evaluates it to tt or ff, according to the usual semantics of propositional logic. 

if e has variables, they should be evaluated to ff. 

as usual, all tests given below must pass. 

also prove that your bxeval satisfies the theorem bxeval_not given below. 
-/

-- ANSWER: 

def binop_eval : binop → bool → bool → bool 
  | binop.and b1 b2 := (b1 && b2) 
  | binop.or  b1 b2 := (b1 || b2) 
  | binop.imp b1 b2 := (b1 → b2) 
  | binop.iff b1 b2 := (b1 ↔ b2) 
  | binop.xor b1 b2 := (bxor b1 b2)

def bxeval : bx → bool 
  | (bxconst b) := b
  | (bxvar v) := ff
  | (bxnot bx) := (bnot (bxeval bx))
  | (bxbin bn bx1 bx2) := (binop_eval bn (bxeval bx1) (bxeval bx2))
--

example: bxeval F = ff := begin refl, end
example: bxeval T = tt := begin refl, end

example: bxeval ((F + T) ⬝ (F => ~T)) = tt 
:= begin refl, end

example: bxeval ((F + T) ⬝ (T => ~T)) = ff 
:= begin refl, end

example: bxeval (((x 1) + T) ⬝ (x 1 => ~T))  = tt 
:= begin refl, end

example: bxeval (((x 1) + x 2) ⬝ (x 1 => ~x 2)) = ff 
:= begin refl, end



theorem bxeval_not: ∀ e : bx, bxeval e = tt ↔ bxeval (bxnot e) = ff 
:= begin
intro e,
split,
{
  intro h,
  dunfold bxeval,
  rw h,
  rw bnot,
},
{
  intro h,
  dunfold bxeval at h,
  cases (bxeval e),
  {
    trivial,
  },
  {
    rw bnot at h,
  },
},
end






/-
a brute-force way to solve the SAT problem is to check all possible assignments: if we find one that satisfies the formula, the formula is SAT. otherwise it's UNSAT. recall that an assignment is a function that maps each variable to the formula to either T or F (true or false). if the formula has k variables, there are 2^k possible assignments. 

assignments can be partial, meaning that some, but not all, of the variables of a given formula have been assigned values. 

we can represent (complete or partial) assignments as bx's. an assignment can be represented as a special bx which is a conjunction of literals. a literal is either a variable or a negated variable. for example, these are some assignments represented as bx's: 
-/

-- x1, x2 and x3 are all true: 
#check (x 1) ⬝ (x 2) ⬝ (x 3)

-- x1 and x2 are true, x3 is false: 
#check (x 1) ⬝ (x 2) ⬝ (~x 3)

-- x1, x2 and x3 are all false: 
#check (~x 1) ⬝ (~x 2) ⬝ (~x 3)




/- HWK10-09: 

define a function

   sath : bx → list nat → bx → (bool × bx) 

sath is a helper to the main sat function. sath takes as inputs:
  - a bx e 
  - a list of nats (variable IDs) L: L is the list of unassigned variables of e. 
  - a bx g: g is the tentative partial assignment that we have so far. 
  
if e is SAT, then sath returns a pair (tt, d) where d is a satisfying assignment of e. otherwise, sath returns the pair (ff, (bxconst ff)). 

you can follow the following logic:
  - if L is empty, it means all variables have been assigned and e has no more variables. then we can just evaluate e. 

  - if L has at least one variable, say x, then:
    - assign x to (bxconst tt), and check recursively if the new formula obtained by substituting x by T in e is SAT. (remember also to update the assignment passed to the recursive call of sath!).  if the new formula is SAT, you are done!
    - if not, try the assignment where x is assigned to (bxconst ff) instead. if this works, you're done! if not, the formula is UNSAT. 

all tests given below must pass. 

you must also prove that your sath function satisfies the theorems given below. 
-/

-- ANSWER: 

def sath : bx → list nat → bx → (bool × bx) 
  | e1 [] e2 := ite (bxeval e1 = tt) (tt, e2) (ff, (bxconst ff))
  | e (y :: L) e2 := 
    (ite 
      ((sath (bxsubst e y tt) L (bxbin binop.and e2 (bxvar y))).fst = tt) 
      -- tt
      (sath (bxsubst e y tt) L (bxbin binop.and e2 (bxvar y)))
      -- ff
      (ite 
        ((sath (bxsubst e y ff) L (bxbin binop.and e2 (bxnot (bxvar y)))).fst = tt) 
        -- tt
        (sath (bxsubst e y ff) L (bxbin binop.and e2 (bxnot (bxvar y))))
        -- ff
        (ff, (bxconst ff)))) 
--


example: sath F [] F = (ff, F) := begin refl, end
example: sath T [] T = (tt, T) := begin refl, end
example: ∀ a : bx, sath T [] a = (tt, a) := begin intro, refl, end

theorem sath_bxeval_tt: ∀ e a : bx, 
  bxvars e = [] → bxeval e = tt → sath e [] a = (tt, a) :=
begin  
  intro e,
  intro a, 
  intros h h1,
  dunfold sath, 
  rw itetrue, 
  exact h1, 
end

theorem sath_bxeval_ff: ∀ e a : bx, 
  bxvars e = [] → bxeval e = ff → sath e [] a = (ff, (bxconst ff)) := 
begin
  intros e a h h1, 
  dunfold sath,
  rw h1, 
  rw itefalse, 
  intro,
  trivial, 
end            






/- HWK10-10: 

with the help of sath, write the main "sat" function. sat takes as input a bx e and returns a pair (bool × bx):

  - if e is satisfiable, then sat returns a pair (tt, g), where g is a satisfying assignment of e. 

  - if e is unsatisfiable, then sat returns the pair (ff, (bxconst ff)). 

also write the following functions, derivatives of "sat":

  - the function satyesno: bx → bool, which takes a bx e and returns tt if e is SAT and ff otherwise. use the output of sat and ".fst" to extract the first element of a pair (see 03-code.lean). 

  - the function satasgn: bx → bx, which takes a bx e and returns a satisfying assignment of e if e is SAT and (bxconst ff) otherwise. use the output of sat and ".snd" to extract the second element of a pair (see 03-code.lean). if e is SAT, make sure the satisfying assignment that you return doesn't have any redundant "T ⬝" part, otherwise your tests below will fail. hint: use bx_and_simp to simplify. 

  - the function valid: bx → (bool × bx), which takes a bx e and checks whether e is valid (see 07-propositional-logic.pdf if you don't remember what that means). "valid" should return (tt, (bxconst tt)) if e is valid. otherwise it should return (ff, g), where g is a falsifying assignment, i.e., an assignment that makes e false. 


all tests given below must pass. HOWEVER, NOTE: the given tests are far from being exhaustive. the satisfiable formulas we use have only one satisfying assignment, so that no matter how you implement your own solver, the answer in those cases is unique. 

write more tests on your own to make sure your SAT solver is correct!
-/

-- ANSWERS:

-- the main SAT solver functions:

def sat (e : bx) : (bool × bx) := sath e (bxvars e) T

-- yes/no version
def satyesno (e : bx) : bool := (sat e).fst 

-- the assignment returned by sat:
def satasgn (e : bx) : bx := (bx_and_simp ((sat e).snd))

-- check validity and return a falsifying assignment if not valid: 
def valid (e : bx) : (bool × bx) := ite ((satyesno ~e) = ff) (tt, (bxconst tt)) (ff, (satasgn ~e))
 
example: satasgn F = F := begin refl, end
example: satasgn T = T := begin refl, end
example: satasgn (T + F) = T := begin refl, end
example: satasgn (T ⬝ F) = F := begin refl, end

example: satasgn ((x 1) ⬝ (x 2) ⬝ (x 3)) = (((x 1) ⬝ x 2) ⬝ (x 3))
:= begin refl, end

example: satasgn (~((x 1) + (x 2) + (x 3))) = (((~x 1) ⬝ ~x 2) ⬝ (~x 3))
:= begin refl, end

example: satyesno (((x 1) ⊕ (x 2)) ⬝ ((x 1) <=> (x 2))) 
= ff := begin refl, end

example: satyesno  
(
  ((x 1) => x 2) <=> ((~x 1) + x 2)
) 
= tt := begin refl, end 

example: valid 
(
  ((x 1) => x 2) <=> ((~x 1) + x 2)
) 
= (tt, T) := begin refl, end 

example: valid 
(
  ((~x 1) + x 1)
) 
= (tt, T) := begin refl, end 

example: valid 
(
  ((~x 1) + x 2)
) 
= (ff, (x 1) ⬝ ~x 2) := begin refl, end 

example: valid 
(
  ((x 1) ⊕ x 2) <=> ~((x 1) <=> x 2)
) 
= (tt, T) := begin refl, end 



