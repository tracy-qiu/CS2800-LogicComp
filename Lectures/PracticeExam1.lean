-- Tracy Qiu Practice Exam 1 10/24/22

import .ourlibrary11
import .ourlibrary12 

def even : nat → bool 
    | 0 := tt 
    | 1 := ff 
    | (nat.succ (nat.succ x)) := even x

def reverse: list ℕ -> list ℕ 
  | [] := []
  | (x :: L) := app (reverse L) [x]

#eval reverse [1, 2, 3]
#eval reverse [13]
#eval reverse [] 

example: reverse [1, 2, 3] = [3, 2, 1] := begin refl end 
example: reverse [13] = [13]  := begin refl end 
example: reverse [] = []  := begin refl end

theorem len_reverse: ∀ L: list ℕ, len (reverse L) = len L
:= begin
  intro L, 
  cases L with x L, 
  {
    unfold len,
    trivial,
  }, 
  {
    dunfold reverse, 
    dunfold len,
    try { refl, },
    sorry
  }
end

#eval reverse (1 :: 2 :: [])

theorem reverse_two_element_list: ∀ x y : ℕ, reverse [x,y] = [y, x]
:= begin
  intros x y, 
  dunfold reverse,
  dunfold app,
  trivial,
end

theorem app_reverse: forall L1 L2 : list nat, 
  reverse (app L1 L2) = app (reverse L2) (reverse L1) :=
begin
  intros,
  sorry,
end

lemma p_and_false: ∀ P : Prop, P ∧ false ↔ false :=
-- ANSWER:
begin
    intro P, 
    split, 
    {
      intro h, 
      cases h, 
      {
        trivial, 
      },
    },
    {
      intro h, 
      trivial, 
    }
end

theorem or_absorb_and: ∀ P Q : Prop, P ∨ (P ∧ Q) ↔ P :=
-- ANSWER:
begin
  intros P Q, 
  split, 
  {
    intro h, 
    cases h, 
    {
      assumption, 
    },
    {
      cases h, 
      {
        assumption,
      },
    }
  },
  {
    intro h, 
    left, 
    assumption, 
  }
end

theorem p_and_q_implies_p_and_q: ∀ P Q : Prop, P ∧ Q → P ∧ Q :=
begin
    intros P Q, 
    intro h, 
    assumption, 
end


 -- xor (p → q) (q → p)
 -- satisfiable - true for at least one case 
  -- unsatisfiable - false for all cases 
-- valid - true for all cases 
  -- falsifiable - false for at least one case

-- implies  
-- T F -> F every other case T


-- Practice HQ 7 

-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!




-- from ourlibrary12.lean: 
#check deMorgan_or
#check deMorgan_and
#check not_p_or_q_iff_p_implies_q
#check not_not
#check and_distrib_or
#check or_distrib_and

-- from the LEAN library: 
#check and_comm 
#check or_comm 
#check or_false 
#check false_or 
#check or_true 
#check true_or 
#check and_true
#check true_and 






/- HWK07-01: 
is the claim below true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
The claim is true and our proof is constructive. 
-/
theorem p_iff_false: ∀ P : Prop, (P ↔ false) ↔ ¬ P 
-- ANSWER: 
:= begin 
  
end


/- HWK07-02: 
is the claim below true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
The claim is true and our proof is constructive.
-/
theorem p_and_not_p_eq_false: ∀ p : Prop, (p ∧ ¬ p) ↔ false 
-- ANSWER: 
:= begin 

end



/- HWK07-03: 
is the claim below true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
The claim is true and out proof is not constructive. 
-/
lemma or_absorb_and_or: ∀ p q : Prop, p ∨ (¬ p ∧ q) ↔ (p ∨ q) 
-- ANSWER: 
:= begin 
  
end 


/- HWK07-04: 
is the claim below true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
The claim is true and our proof is constructive. 
-/
lemma redundant_and: ∀ p q : Prop, (p ∨ q) ∧ (p ∨ ¬ q) ↔ p 
-- ANSWER: 
:=
begin
intros p q,
split,
{
  intro h,
  cases h with h1 h2,
  {
    cases h1,
    {
      assumption,
    },
    {
      cases h2,
      {
        assumption,
      },
      {
        trivial,
      }
    }
  },
},
{
  intro h,
  split,
  repeat {
    left,
    assumption,
  },
}
end



/- HWK07-05: 
is the claim below true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
This claim is true and our proof is not constructive. 
-/
lemma not_p_implies_p: ∀ P : Prop, (¬ P → P) ↔ P 
-- ANSWER: 
:= begin 
  intro P,
  split,
  {
  intro h,
  have h1:= classical.em P,
  cases h1,
  {
    assumption,
  },
  {
    have h2:= h h1,
    assumption,
  }
  },
  {
    intros h h1,
    assumption,
  }
end



/- HWK07-06: 
is the claim below true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
This claim is true and our proof is not constructive. 
-/
lemma or_if: ∀ (P Q : Prop), P ∨ Q ↔ (¬ P → Q) 
-- ANSWER: 
:= begin 
  intros P Q, 
  split, 
  {
    intro h1, 
    intro h2, 
    cases h1, 
    {
      trivial, 
    },
    {
      assumption,
    }
  },
  {
    intro h1, 
    have h2 := classical.em P, 
    cases h2, 
    {
      left, 
      assumption,
    }, 
    {
      right, 
      have h3:= h1 h2, 
      assumption,
    }
  }
end


/- HWK07-07: 
is the claim below true? if so prove it and answer the question: is your proof constructive? if you believe the claim is not true, exhibit a counterexample. 
This claim is true and our proof is constructive.
-/
theorem exportation: ∀ A B C : Prop, (A → B → C) ↔ (A ∧ B → C) 
-- ANSWER:
:= begin 
  intros A B C, 
  split, 
  {
    intro h1, 
    intro h2, 
    cases h2 with h3 h4, 
    {
      have h5 := h1 h3 h4,
      assumption, 
    },
  },
  {
    intro h1, 
    intro h2, 
    intro h3, 
    have h4 : A ∧ B := begin 
      split,
      repeat
      {
        assumption, 
      },
    end,
    have h5 := h1 h4,
    assumption,
  }
end 



/- HWK07-08: 
consider the following formulas:
(1) (A → B) ∧ (¬A → C)  
(2) (A ∧ B) ∨ (¬A ∧ C) 
are they equivalent? or is one stronger than the other? which one?

if you think they are equivalent, prove it, using Props. is your proof constructive?

if you think one is strictly stronger than the other, prove the implication that holds, and provide counterexample for the implication that does not hold. 
-/
-- ANSWER: 
 
/-
The two formulas are equivalent. 
A | B | C | A → B | ¬A | ¬A → C | (A → B) ∧ (¬A → C)  
 t | t | t |   t   | f  |    t   |       t
 t | f | f |   f   | f  |    t   |       f
 f | t | t |   t   | t  |    t   |       t
 f | f | f |   t   | t  |    f   |       f

 A | B | C | A ∧ B | ¬A | ¬A ∧ C | (A ∧ B) ∨ (¬A ∧ C)  
 t | t | t |   t   | f  |    f   |       t
 t | f | f |   f   | f  |    f   |       f
 f | t | t |   f   | t  |    t   |       t
 f | f | f |   f   | t  |    f   |       f
-/

theorem equiv: ∀ A B C : Prop, (A → B) ∧ (¬A → C) ↔ (A ∧ B) ∨ (¬A ∧ C)
:= begin 
  intros, 
  split,
  {
    intro h1, 
    cases h1 with h2 h3, 
    {
      have h2 := classical.em A,
      cases h2 with h3 h4,
      {
        left, 
        have h4 := h2 h3,
        split, 
        repeat
        {
          assumption,
        }
      },
      {
        right, 
        have h5 := h3 h4, 
        split,
        repeat
        {
          assumption
        }
      }
    },
  },
  {
    intro h1, 
    split, 
    {
      intro h2, 
      cases h1, 
      {
        cases h1, 
        {
          assumption
        },
      },
      {
        cases h1, 
        trivial,
      },
    },
    {
      intro h2, 
      cases h1, 
      {
        cases h1, 
        {
          trivial, 
        },
      },
      {
        cases h1, 
        {
          assumption,
        }
      }
    }
  }
end



/- HWK07-09: 
you will now prove the law of excluded middle assuming the law of contradiction.
-/

def contra              := ( ∀ p : Prop, ¬¬p → p )
def law_excluded_middle := ( ∀ p : Prop, p ∨ ¬ p )

/- HWK07-09-1: 

prove the theorem "contra_implies_em" given below. 

you are NOT allowed to use neither classical.em, nor classical.by_contradiction! 
-/

theorem contra_implies_em: contra → law_excluded_middle
:= begin 
-- ANSWER:
   intro h, 
   intro, 
   have h1 := h p,
       
end

/- HWK07-09-2:
can you prove theorem not_not_p_implies_p_implies_p_or_not_p below constructively?

theorem not_not_p_implies_p_implies_p_or_not_p:
  ∀ p : Prop, (¬ ¬ p → p) → (p ∨ ¬ p)

explain the difference between not_not_p_implies_p_implies_p_or_not_p and contra_implies_em.
-/

-- ANSWER:
theorem not_not_p_implies_p_implies_p_or_not_p: ∀ p : Prop, ¬¬ p → p ∨ ¬ p 
:= begin 
  intro p, 
  intro h, 
  
end 



/- HWK07-10: 
use _rewrite_ to prove the following. 

NOTE: for this problem we want you to learn to use the _rewrite_ tactic. there is a very short proof (4 lines!) using _rewrite_ and other tactics that we learned. there are also longer proofs. try to find the short one. we will cut points off for too long proofs.  
-/
theorem iff_trans: ∀ A B C : Prop, (A ↔ B) ∧ (B ↔ C) → (A ↔ C) 
:= begin
-- ANSWER:
  intros A B C,
  intro h,
  cases h with h2 h3,
  {
    rw h3 at h2,
    assumption,
  }
end




/- HWK07-11-1: 

prove the following theorem:

∀ (p q : Prop), (¬ xor p q) ↔ ((p ∧ q) ∨ (¬ p ∧ ¬ q))

for this problem, you can prove the result in any way you want. in particular, you can use any of the theorems listed above. 
-/


theorem not_xor: ∀ (p q : Prop), (¬ xor p q) ↔ ((p ∧ q) ∨ (¬ p ∧ ¬ q))
:= begin
-- ANSWER:
  intros p q, 
  split, 
  {
    dunfold xor,
    


    dunfold not,
    dunfold xor,
    dunfold not,

    intro h, 
    right,
    split,
    {
      
    }

    dunfold not at h, 
    
    split,
    {
      
    }
    
  } 
end



/- HWK07-11-2:
prove the same result, by completing the proof below, using ONLY the rw (rewrite) tactic! 

NOTES:
  - as always, you are allowed to use ANY previously proven result in class, in given libraries, in previous homeworks, or in the same homework. in particular, you ARE allowed to use De Morgan's laws and any of the theorems listed above. 

  - you may have to do a lot of rewrites. this is normal. in my proof i used rw 17 times, but there might be shorter proofs. 

  - for proofs like this one, it might be a good idea to FIRST WORK OUT THE PROOF ON PAPER AND PENCIL. see how you would prove this using the logical equivalences you know (de Morgan, etc). then try to re-do the same proof in LEAN. 
-/



theorem not_xor_rw: ∀ (p q : Prop), (¬ xor p q) ↔ ((p ∧ q) ∨ (¬ p ∧ ¬ q))  
:= begin
  intro,
  intro,
  unfold xor,
-- use only the "rw" tactic (as many times as you want) in the rest of the proof. 
-- ANSWER: 
  ... 
end



/- HWK07-12: 

prove the following. 

hint: use listeq:
-/

#check listeq 

example: ∀ (x y z : ℕ) (L : list ℕ) (p : Prop), x :: y :: L = [z] → p 
:= begin
-- ANSWER: 
    ... 
end


--------------------



section a_bit_of_first_order_logic 

/- beyond propositional logic 
-/

-- let P and Q be arbitrary first-order logic predicates on ℕ:
variable P : ℕ → Prop 
variable Q : ℕ → Prop 

-- consider the following two formulas: 
def formula1 := (∀ x, P x) → (∀ x, Q x) 
def formula2 := (∀ x, P x → Q x) 

/- HWK07-13: 

are formula1 and formula2 equivalent? or is one stronger than the other? which one?

if you think they are equivalent, prove it. you will have to prove this:
       ∀ P Q, (formula1 P Q) ↔ (formula2 P Q) 
did you have to use classical.em?

if you think one is strictly stronger than the other, prove the implication that holds, and provide counterexample for the implication that does not hold. to provide a counterexample, you will have to provide definitions for predicates P and Q, and example nats that make the formulas above true or false! (c.f. 11-code.lean, "(SEMANTIC) TRUTH")
-/

-- ANSWER:
... 



end a_bit_of_first_order_logic




/- HWK07-14: 
prove the following:
-/
lemma plus_one_succ: ∀ x : ℕ, plus x 1 = nat.succ x 
:= begin
-- ANSWER:
    ... 
end



/- HWK07-15:
 prove associativity of app:
-/
theorem app_associative: ∀ L1 L2 L3 : list ℕ, 
    app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
-- ANSWER: 
    ... 
end




-- recall the definition of minus (subtraction on nats):
def minus : ℕ → ℕ → ℕ 
    | 0 _ := 0
    | (nat.succ x) 0 := (nat.succ x)
    | (nat.succ x) (nat.succ y) := minus x y


/- HWK07-16:
 prove the following:
-/
theorem minus_x_x: ∀ x : ℕ, minus x x = 0 
:= begin
    ... 
end


