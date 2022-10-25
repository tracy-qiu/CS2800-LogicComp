-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 6

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Tracy Qiu, Erica Sammarco, Anushka Mantri
-/

/-
Technical instructions: same as in the last homework, PLUS ADDITIONAL INSTRUCTIONS BELOW:
-/



/- ADDITIONAL INSTRUCTIONS:

Just like you are welcome to use any function defined in class or in previous homeworks or in the current homework, you are also welcome to use any lemma/theorem/example proved in class or in previous homeworks or in the current homework. 

You are also allowed to define and use your own helper functions and you are also allowed to define and use/"call" your own lemmas/theorems, in order to prove other theorems. 

WE WILL CUT POINTS OFF IF YOU USE classical.em or classical.by_contradiction UNNECESSARILY.  

-/




/- HWK06-01:
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem not_false_true: ¬ false ↔ true :=
-- ANSWER: 

begin
split, 
repeat {
intro h,
trivial,
},
end


/- HWK06-02: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem xor_commut: ∀ P Q : Prop, (xor P Q) ↔ (xor Q P) :=
-- ANSWER:
begin
intros,
split, 
repeat {
  intro h,
  cases h, {
    right,
    assumption,
  },
  {
    left,
    assumption,
  },
}
end 


/- HWK06-03: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem p_implies_xor: ∀ p q : Prop, p → ((xor p q) ↔ ¬q) :=

begin
intros,
split, {
  intro h,
  cases h, {
    cases h, {
      assumption,
    }
  }, 
  {
    cases h, {
      trivial,
    },
  },
},
{
  intro h,
  left,
  split, 
  repeat {
    assumption,
  }
}
end  



/- HWK06-04: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem and_elim: ∀ p q r : Prop, (p ∧ q) → (p → q → r) → r :=
-- ANSWER:
begin
intros p q r,
intro h1,
intro h2,

cases h1 with h3 h4, {
  have h5 := h2 h3 h4,
  assumption,
},
end


/- HWK06-05: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem or_elim: ∀ p q r : Prop, (p ∨ q) → (p → r) → (q → r) → r :=
-- ANSWER:
begin
intros p q r,
intros h1 h2 h3,

cases h1, {
  have h4 := h2 h1,
  assumption,
}, 
{
  have h4 := h3 h1,
  assumption,
}
end




/- HWK06-06: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem not_p_not_q_iff: ∀ P Q : Prop, ¬ P → ¬ Q → (P ↔ Q) :=
-- ANSWER:
begin
intros P Q,
intros h1 h2,
split, {
  intro h,
  have h3 := classical.em Q,
  cases h3, {
    assumption,
  },
  {
    trivial,
  }
},
{
  intro h,
  have h3 := classical.em P,
  cases h3, {
    assumption,
  },
  {
    trivial,
  }
}
end


/- HWK06-07: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem mp_eq: ∀ P Q : Prop, ((P → Q) ∧ P) ↔ (P ∧ Q) :=
-- ANSWER:
begin
intros P Q,
split, {
  intro h,
  cases h with h1 h2, {
    split, {
      assumption,
    },
    {
      have h3 := h1 h2,
      assumption,
    }
  }
},
{
intro h,
  cases h with h1 h2, {
    split, {
      intro h3,
      assumption,
    },
    {
      assumption,
    }
  }
}
 
end


/- HWK06-08: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem contraposition: ∀ P Q : Prop, (P → Q) → (¬ Q → ¬ P) :=
-- ANSWER:
begin
intros P Q,
intros h1 h2 h3,
dunfold not at h2,
have h4 := h1 h3,
have h5 := h2 h4,
assumption,
end


/- HWK06-09: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem iff_and: ∀ P Q : Prop, (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) :=
-- ANSWER:
begin
intros P Q,
split, 
repeat {
  intro h,
  split, 
  repeat {
    cases h, {
      assumption,
    }
  },
}

end

/- HWK06-10: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem implies_trans: ∀ A B C : Prop, (A → B) ∧ (B → C) → (A → C):=
-- ANSWER:
begin
intros A B C,
intros h1 h2,
cases h1 with h3 h4, {
  have h5 := h3 h2,
  have h6 := h4 h5,
  assumption,
}
end


/- HWK06-11: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem p_xor_true: ∀ P : Prop, (xor P true) ↔ ¬ P :=
-- ANSWER:
begin
intro P,
split, 
{
  intro h,
  cases h with h1 h2, {
    dunfold not at h1,
    intro,
    cases h1 with h3 h4, {
      have h5 : true := begin trivial, end, 
      have h6 := h4 h5,
      trivial,
    },
  },
  {
    dunfold not at h2,
    intro,
    cases h2 with h3 h4, {
      trivial,
    },
  }
},
{
  intro h,
  -- dunfold not at h,
  right,
  -- dunfold not,
  split, {
    trivial,
  },
  {
    assumption,
  }
}
end



/- HWK06-12: 
is the theorem below true? if so prove it, if not, exhibit a counterexample:
-/
theorem p_xor_not_p: ∀ P : Prop, xor P ¬P :=

begin
intro P,
have h := classical.em P,
cases h, {
  left,
  split, 
  {
    assumption,
  },
  {
    intro h1,
    have h2 := h1 h,
    assumption,
  },
},
{
  right,
  split,
  repeat {
    assumption,
  }
}
end




/- HWK06-13-1: 
prove the following in two ways:

1. directly, without calling any other lemmas/theorems. 
-/
example: ∀ x : nat, x = 0 ∧ x ≠ 0 → x > 10 
:= begin
intro x,
intro h,
cases h, {
  trivial,
},
end

/- HWK06-13-2: 
2. by calling a lemma/theorem that we proved already in class. you must find which lemma or theorem you want to use among those that we proved in class already. read the lecture code and decide. copy the lemma/theorem that you chose here, and then use it. 
-/
-- ANSWER: proof using the following result proven in class:
theorem not_p_and_not_p: ∀ P : Prop, ¬ (P ∧ ¬P) 
:= begin
    intro,
    intro h,
    cases h with h1 h2,
    dunfold not at h2,
    have h3 : false := h2 h1,
    trivial,
end

example: ∀ x : nat, x = 0 ∧ x ≠ 0 → x > 10 
:= begin
  intro x, 
  intro h,
  have h1 := not_p_and_not_p (x = 0), 
  trivial, 
end




/- HWK06-14: 
is the claim below true? if so prove it, if not, exhibit a counterexample:
-/
example: ∀ x y : ℕ, x = y+1 → x > 0 → (x > 0 ∧ y+1 > 0) := 
-- ANSWER: 
begin
intros x y,
intros h1 h2,
split, 
{
  assumption,
},
{
  rw h1 at h2,
  assumption,
}
end


/- HWK06-15-1: 
a classic equivalence in (classical) logic is that (p → q) is equivalent to (¬p ∨ q). we will prove this in two steps. one (and only one!) of these steps requires the law of excluded middle. which one?

first, prove the following. did you have to use classical.em?
Yes, we had to use classical.em.
-/

theorem p_implies_q_implies_not_p_or_q: 
    ∀ p q : Prop, (p → q) → (¬p ∨ q) 
:= begin
  intros p q, 
  intro h1,
  have h4 := classical.em (¬p ∨ q),
  cases h4, 
  {
    assumption, 
  },
  {
    have h5 := classical.em p,
    cases h5, 
    {
      right, 
      have h6 := classical.em q, 
      have h6 := h1 h5, 
      assumption,
    }, 
    {
      left, 
      assumption, 
    }
  }
end


/- HWK06-15-2: 
now, prove the following. did you have to use classical.em?
No, we did not have to use classical.em.
-/
theorem not_p_or_q_implies_p_implies_q: 
    ∀ p q : Prop, (¬p ∨ q) → (p → q)
:= begin
  intros p q, 
  intro h1, 
  cases h1, 
  {
    dunfold not at h1, 
    intro h2, 
    have h3 := h1 h2, 
    trivial, 
  },
  {
    intro h2,
    assumption, 
  }
end


/- HWK06-16: 
prove the following. did you have to use classical.em? (answer YES/NO to the latter question). 
-/
lemma and_absorb_or_and: ∀ p q : Prop, p ∧ (¬ p ∨ q) ↔ (p ∧ q) 
:= begin
  intros p q, 
  split, 
  {
    intro h1, 
    cases h1 with h2 h3, 
    {
      split, 
      {
        assumption,
      },
      {
        cases h3, 
        {
          have h4 := h3 h2, 
          trivial, 
        },
        {
          assumption, 
        }
      }
    }
  },
  {
    intro h1, 
    cases h1, 
    {
      split, 
      {
        assumption,
      },
      {
        right, 
        assumption,
      }
    }
  }
end




/- HWK06-17-1: 
the famous _De Morgan's laws_ of propositional logic state that:

  1. ¬ (p ∨ q) is equivalent to (¬ p) ∧ (¬ q) 
  2. ¬ (p ∧ q) is equivalent to (¬ p) ∨ (¬ q) 

thou shalt (you shall) prove these laws. we will first split each equivalence into two implications, so you will first have 4 separate lemmas to prove. try to prove as many of those 4 as you can using only constructive logic, that is, _without_ using classical.em, nor classical.by_contradiction. how many and which ones did you manage to prove without these axioms?

We managed to prove 3 (deMorgan1, deMorgan2, deMorgan3) without these axioms.
-/

lemma deMorgan1: ∀ (p q : Prop), (¬ p ∧ ¬ q) → ¬ (p ∨ q) 
:= begin
  intros p q, 
  intro h1, 
  cases h1, 
  {
    intro h2, 
    cases h2, 
    repeat
    {
      trivial, 
    } 
  }
end

lemma deMorgan2: ∀ (p q : Prop), (¬ p ∨ ¬ q) → ¬ (p ∧ q) 
:= begin
  intros p q, 
  intro h1, 
  intro h2, 
  {
    cases h1,
    repeat 
    {
      cases h2, 
      {
        trivial, 
      }
    }
  }
end


lemma deMorgan3: ∀ (p q : Prop), ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
begin
  intros p q,
  intro h,
  split,
  {
    intro h1,
    have h2 : (p ∨ q) := begin
      left,
      assumption,
    end,
    have h3 := h h2,
    trivial,
  },
  {
    intro h1,
    have h2 : (p ∨ q) := begin
      right,
      assumption,
    end,
    have h3 := h h2,
    trivial,
  },
end


lemma deMorgan4: ∀ (p q : Prop), ¬ (p ∧ q) → (¬ p ∨ ¬ q) 
:= begin
  intros p q, 
  intro h1, 
  have h2 := classical.em p, 
  have h3 := classical.em q, 
  cases h2, 
  {
    cases h3, 
    {
      have h4 : p ∧ q
      := begin
        split, 
        repeat
        {
          assumption, 
        },
      end, 
      have h5 := h1 h4, 
      trivial, 
    },
    {
      right, 
      assumption, 
    }
  }, 
  {
    left, 
    assumption, 
  }
end


/- HWK06-17-2: 
combine the 4 lemmas above to prove the two deMorgan theorems below (in this problem we are not asking you to re-do the proofs by copy-pasting everything you already wrote above, but instead to call the above lemmas at the appropriate places in your proof):
-/
theorem deMorgan_or: ∀ p q : Prop, ¬ (p ∨ q) ↔ (¬p ∧ ¬q)
:= begin
  intros p q, 
  split, 
  {
    have h1 := deMorgan3 p q, 
    assumption, 
  },
  {
    have h2 := deMorgan1 p q, 
    assumption, 
  }
end


theorem deMorgan_and: ∀ p q : Prop, ¬ (p ∧ q) ↔ (¬p ∨ ¬q) 
:= begin
  intros p q, 
  split, 
  {
    have h1 := deMorgan4 p q, 
    assumption, 
  },
  {
    have h2 := deMorgan2 p q, 
    assumption, 
  }
end




/- HWK06-18: 
the theorems "le_transitive" and "lt_implies_le" below are given to you. you don't need to know how they have been proven. consider them part of some "black-box" library. you can call stuff from that library, but you don't need to know how they are implemented. 

use these theorems to prove theorem "hwk06_18": 
-/

theorem le_transitive: ∀ x y z : ℕ, x ≤ y → y ≤ z → x ≤ z 
:= begin
    intro,
    intro,
    intro,
    intro h1,
    intro h2,
    apply nat.le_trans h1 h2,
end

theorem lt_implies_le: ∀ x y : ℕ, x < y → x ≤ y 
:= begin
    intro,
    intro,
    intro h,
    apply le_of_lt h,
end

theorem hwk06_18: ∀ a b c : ℕ, (a < b ∧ b < c) → a ≤ c 
:= begin
  intros a b c, 
  intro h1, 
  have h4 := le_transitive,
  have h5 := lt_implies_le,
  cases h1 with h2 h3, 
  {
    have h6 := h5 a b, 
    have h7 := h5 b c, 
    have h8 := h6 h2, 
    have h9 := h7 h3, 
    have h10 := h4 a b c, 
    have h11 := h10 h8 h9,
    assumption, 
  }, 
end


/- HWK06-19: 
consider the following functions:
-/

def len : list nat -> nat 
  | [] := 0
  | (_ :: L) := (len L) + 1 
--

def app : list nat -> list nat -> list nat 
  | [] L := L 
  | (a :: L1) L2 := a :: (app L1 L2)
--

def tail: list nat -> list nat 
  | [] := []
  | (x :: L) := L
--

def minus1: nat -> nat 
    | 0 := 0 
    | (nat.succ x) := x 
--



/- HWK06-19-1:
write the LEAN theorem "len_tail_or" stating that for any list of nats L, either L is empty and the length of the tail of L is zero, or the length of the tail of L is one less than the length of L. use the "minus1" function above to express "one less". use "or" (and not "xor") to combine the two parts. 

then prove the theorem "len_tail_or". 
-/
-- ANSWER:
theorem len_tail_or: ∀ L : list ℕ, 
or ((L = []) ∧ (len (tail L) = 0)) ((minus1 (len L)) = (len (tail L)))
:= begin
  intro,
  cases L,
  {
    left,
    dunfold tail,
    split,
    {
      refl,
    },
    {
      refl,
    },
  },
  {
    right,
    dunfold tail,
    refl,
  },
end

/- HWK06-19-2:
does the statetement hold if we use "xor" instead of "or"? if yes, prove it also with "xor". if not, provide a counterexample. 
-/
-- ANSWER:
/-
The empty list [] is a counterexample.

When the list is empty, the length of the tail = 0, so the first part of the expression ((L = []) ∧ (len (tail L) = 0)) is true.

Also, ((minus1 (len L)) = (len (tail L))) is true since 
(minus1 (len [])) = minus1(0) = 0, and (len (tail [])) = len([]) = 0. 

Since both the first and the second expressions are true, xor does not hold.
-/
   


