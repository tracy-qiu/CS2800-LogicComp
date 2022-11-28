import .ourlibrary11
-- Q.1
theorem or_assc: ∀ A B C : Prop, or A (or B C) ↔ or (or A B) C 
:= begin 
  intros A B C, 
  split, 
  {
    intro h,
    cases h,
    {
      left, 
      left, 
      assumption, 
    },
    {
      cases h, 
      {
        left, 
        right,
        assumption
      },
      {
        right, 
        assumption, 
      }
    }
  },
  {
    intro h, 
    cases h, 
    {
      cases h, 
      {
        left, 
        assumption,
      },
      {
        right, 
        left, 
        assumption, 
      }
    },
    {
      right, 
      right, 
      assumption, 
    }
  }
end

-- Q1.2
theorem and_distrib_or: ∀ A B C : Prop, and A (or B C) ↔  or (and A B) (and A C) := begin 
  intros A B C, 
  split,
  {
    intro h, 
    cases h with h2 h3, 
    {
      cases h3, 
      {
        left, 
        split, 
        repeat
        {
          assumption, 
        }
      },
      {
        right, 
        split, 
        repeat
        {
          assumption, 
        }
      }
    },
  },
  {
    intro h, 
    cases h, 
    {
      cases h with h2 h3,
      {
        split,
        {
          assumption, 
        },
        {
          left,
          assumption
        }
      },
    },
    {
      cases h with h2 h3, 
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
  }
end

-- Q1.3 
theorem not_p_implies_xor: ∀ p q : Prop, (not p) -> ((xor p q) ↔ q) 
:= begin 
  intros p q, 
  intro h, 
  split, 
  {
    intro h2, 
    cases h2, 
    {
      cases h2, 
      {
        trivial, 
      },
    },
    {
      cases h2, 
      {
        assumption,
      }
    }
  },
  {
    intro h2, 
    right, 
    split, 
    repeat
    {
      assumption
    }
  }
end

-- Q1.4
lemma not_true_false: (not true) ↔ false := begin 
  split, 
  {
    intro h, 
    have h1 : true := begin 
      trivial,
    end, 
    trivial, 
  },
  {
    intro h,
    intro, 
    trivial, 
  }
end 


-- Q1.5
theorem not_xor_p_p: ∀ P : Prop, not (xor P P) := begin 
  intros P, 
  intro h, 
  cases h, 
  repeat
  {
    cases h, 
    {
      trivial,
    },
  },
end 






-- Q1.6 

/-
the lemmas nat.left_distrib and nat.le_add_right from the LEAN library are given to you. use those lemmas (and any other tactic that we have learned) to prove the following: 
-/

#check nat.left_distrib 
#check nat.le_add_right 

example: ∀ x y z w : nat, x * (y + z) <= (x * y + x * z) + w := begin 
  intros x y z w, 
  have h := nat.left_distrib x y z, 
  have h2 := nat.le_add_right (x * (y + z)) w,
  rw h at h2, 
  rw h,
  assumption, 
end








-- Q1.7
lemma cancelsucc: forall x y : nat, (nat.succ x) = (nat.succ y) -> x = y 
:= begin
  intros x y h,
  simp at h,
  assumption,
end

def plus : nat -> nat -> nat
  | nat.zero y := y
  | (nat.succ x) y := nat.succ (plus x y)



example: forall x : nat, ¬(x = plus x 1) -> not (nat.succ x = plus (nat.succ x) 1) := begin 
  intros x, 
  intro h, 
  dunfold plus, 
  intro h2, 
  have h3 := cancelsucc x (plus x 1),
  have h4 := h3 h2, 
  trivial, 
end

-- Q2.1 
inductive ternary : Type 
  | ttt : ternary   -- true 
  | fff : ternary   -- false
  | mbe : ternary   -- maybe 
-- finite 

-- Q2.2 
  -- we define the operators and/or/not on ternary:
open ternary 

def tnot : ternary -> ternary 
  | ttt := fff 
  | mbe := mbe 
  | fff := ttt 

def tand : ternary -> ternary -> ternary 
  | ttt x := x
  | mbe ttt := mbe 
  | mbe mbe := mbe 
  | mbe fff := fff 
  | fff _ := fff 

def tor : ternary -> ternary -> ternary 
  | ttt x := ttt 
  | mbe ttt := ttt 
  | mbe mbe := mbe 
  | mbe fff := mbe 
  | fff x := x 

-- is the claim below true? if so prove it in LEAN. if not, exhibit a counterexample. 

theorem deMorgan_tand: forall x y : ternary,
  tnot (tand x y) = tor (tnot x) (tnot y) := begin 
  intros x y, 
  cases x, 
  {
    cases y, 
    {
      refl, 
    },
    {
      refl, 
    }, 
    {
      refl, 
    }
  },
  {
    cases y,
    {
      refl, 
    },
    {
      refl,
    },
    {
      refl,
    },
  },
  {
    cases y, 
    {
      refl, 
    },
    {
      refl,
    },
    {
      refl,
    },
  }
end

-- Q2.3
/- 
define the function timp, which is implication for ternary. 

complete the definition started below, using pattern matching only, and so that the theorem timp_tor given in the next question holds. 
-/

def timp : ternary -> ternary -> ternary 
  | ttt x := x
  | mbe ttt := ttt 
  | mbe mbe := mbe 
  | mbe fff := mbe 
  | fff _ := ttt  

-- Q2.4
-- prove the theorem timp_tor in LEAN. 

theorem timp_tor: forall x y : ternary, timp x y = tor (tnot x) y := begin 
  intros x y, 
  cases x, 
  {
    cases y, 
    {
      refl, 
    },
    {
      refl, 
    }, 
    {
      refl, 
    }
  },
  {
    cases y,
    {
      refl, 
    },
    {
      refl,
    },
    {
      refl,
    },
  },
  {
    cases y, 
    {
      refl, 
    },
    {
      refl,
    },
    {
      refl,
    },
  }
end

-- Q3.1 
/-
#check (F (λ b : bool, 10) 10)
(bool -> nat) -> (nat -> bool)
-/

-- Q3.2 
/-
#check nat.succ (G nat.zero [(fun x : nat, x+2) 13] tt)
nat -> (list nat) -> bool -> nat
nat -> (nat -> nat) -> nat -> bool -> nat 
-/


-- Q4.1
def len : list nat -> nat 
  | [] := 0 
  | (_ :: L) := nat.succ (len L)

def elem: nat -> list ℕ -> bool 
  | _ [] := ff
  | y (x :: L) := if ( y = x ) then tt else elem y L
  -- | x L := len L ≥ x

example: elem 3 [] = ff := begin refl, end 
example: elem 3 [1] = ff := begin refl, end 
example: elem 3 [1,2] = ff := begin refl, end 
example: elem 3 [1,2,3] = tt := begin refl, end 
example: elem 3 [1,3,2,3] = tt := begin refl, end

-- Q4.2 
theorem elemEmpty: ∀ x : ℕ, elem x [] = ff := begin 
  sorry
end

-- Q4.3 
/-
using the function elem defined above, write as a LEAN theorem the property "if nat x is an element of list L, then x is also an element of (y :: L), for any nat y". 

do not prove your theorem, just state it.
-/

theorem elemInList: ∀ y z: ℕ, ∀ L : list ℕ, elem z (L) == elem (z-1) (y :: L)  := begin 
  sorry
end

theorem elemInList2: ∀ x y: ℕ, ∀ L : list ℕ, (x :: L) == (y :: (x :: L))  := begin 
  sorry,
end

theorem elemInListCorrect: ∀ x: ℕ, ∀ L1 L2 : list ℕ, elem x (app L1 L2) = (elem x L1) || (elem x L2)  := begin 
  sorry,
end

-- Q4.4
/- complete the right-hand side of the equality in the theorem below, so that (1) the right-hand side contains no "app"; and (2) the completed theorem is true (this implies that it also type-checks). 

do not prove the completed theorem, just state it.

"app" is the append function on lists that we defined, given again below. 

copy the theorem and the incomplete proof in the box below and replace the "..." with your code.
-/


theorem elemapp: forall x : nat, forall L1 L2 : list nat, 
  elem x (app L1 L2) = (plus (len L1) (len L2) ≥ x)
:= sorry


-- Q5.1 
/-
satisfiable and falsifiable 
-/

-- Q5.2 
/-
x y z 
T T F
T F T
T F F
F T T
F T F
F F T
F F F
-/

-- Q5.3 
/-
x y z 
T T T
-/

-- Q5.4 
/-
2^3 = 8 rows 
2^8 possibilities
-/


-- Q6.1
 
def duplicateLast: list ℕ -> list ℕ
  | [] := []
  | [x] := [x, x]
  | (x :: L) := x :: (duplicateLast L)

def duplicateLastCorrect: list ℕ -> list ℕ
  | [] := []
  | (x :: []) := [x, x]
  | (x :: y :: L) := x :: (x :: duplicateLast (y :: L))

-- Q6.2 
example: duplicateLast [ ] = [ ] := begin refl, end
example: duplicateLast [13] = [13,13] := begin refl, end
example: duplicateLast [1,2,3] = [1,2,3,3] := begin refl, end


-- Q6.3
/- 
define the function "lastElement" which takes a list of nats and returns the last element in that list. if the list is empty, it returns 0. for example: 

  lastElement [ ] = 0 
  lastElement [13] = 13 
  lastElement [1,2,3] = 3

-/

 
def lastElement: list ℕ -> ℕ
  | [] := 0
  | (x :: []) := x
  | (x :: y :: L) := lastElement L

-- Q6.4 
example: lastElement [ ] = 0 := begin refl, end
example: lastElement [13] = 13 := begin refl, end
example: lastElement [1,2,3] = 3 := begin refl, end

-- Q6.5
/-
write the LEAN theorem that for any nonempty list of nats L, (duplicateLast L) is equal to an expression involving app, L, and the last element of L. you have to discover what that expression is.

 don't prove the theorem. just state it. 

app is the usual append function, given again below.
-/

-- def app : list nat -> list nat -> list nat 
--   | [] L := L 
--   | (a :: L1) L2 := a :: (app L1 L2)

theorem nonempty_list_equals: ∀ L : list ℕ, L ≠ [] → duplicateLast L = app L [lastElement L] := begin 
  sorry
end