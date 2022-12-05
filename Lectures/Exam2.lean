import .ourlibrary16 
import .ourlibraryite

section local_notation

local notation (name := local_plus) x + y := plus x y
local notation (name := local_minus) x - y := minus x y
local notation (name := local_mult) x * y := mult x y
local notation (name := local_leq) x ≤ y := leq x y = tt
local notation (name := local_ltb) x < y := ltb x y = tt

end local_notation

-- Q2.1 
-- ∀ x y : ℕ, 0 ≤ y ↔ x ≤ x + y 
lemma leq_zero_plus_right: 
  forall x y : nat, 
    (leq 0 y = tt) <-> leq x (plus x y) = tt 
:= begin 
  intros x y, 
  split, 
  {
    intro h, 
    induction x with z ih, 
    {
      dunfold plus, 
      exact h,
    },
    {
      cases y, 
      {
        rw plus_x_zero,
        rw plus_x_zero at ih, 
        dunfold leq, 
        exact ih, 
      },
      {
        cases y, 
        {
          cases z, 
          {
            trivial, 
          },
          {
            rw <- plus_x_succ_y, 
            rw plus_x_zero, 
            dunfold leq, 
            rw <- plus_x_succ_y at ih, 
            rw plus_x_zero at ih, 
            dunfold leq at ih, 
            exact ih, 
          }
        },
        {
          rw <- plus_x_succ_y,
          dunfold leq, 
          dunfold plus, 
          rw plus_x_succ_y, 
          exact ih, 
        }
      }
    }
  },
  {
    intro h, 
    induction x with z ih, 
    {
      rw plus_commut at h,
      rw plus_x_zero at h, 
      exact h, 
    },
    {
      cases y, 
      {
        dunfold leq, 
        trivial, 
      },
      {
        rw <- plus_x_succ_y at h, 
        dunfold leq at h, 
        rw <- plus_x_succ_y at ih, 
        dunfold plus at h, 
        have h2 := ih h, 
        exact h2, 
      }
    }
  }
end 


lemma ltb_leq_ltb: 
--  ∀ x y z : ℕ, x < y → y ≤ z → x < z 
  forall x y z : nat, 
    (ltb x y = tt) -> (leq y z = tt) -> (ltb x z = tt)
:= begin 
  intro x, 
  induction x with w ih, 
  {
    intros y z, 
    intros h1 h2, 
    cases y, 
    {
      cases z, 
      {
        exact h1, 
      },
      {
        dunfold leq at h2,
        trivial, 
      }
    },
    {
      cases y, 
      {
        dunfold ltb at h1, 
        cases z, 
        {
          trivial,
        },
        {
          dunfold ltb, 
          trivial, 
        }
      },
      {
        dunfold ltb at h1, 
        cases z, 
        {
          trivial,
        },
        {
          dunfold ltb, 
          trivial, 
        }
      }
    }
  }, 
  {
    intros y z, 
    intros h1 h2, 
    cases y,
    {
      dunfold ltb at h1, 
      trivial, 
    },
    {
      dunfold ltb at h1, 
      have h3 := ih y z, 
      have h4 := h3 h1, 
      -- have h5 := h4 h2, 
      sorry
    }
  }
end



-- Q2.3 
-- ∀ x y : ℕ, x ≤ nat.succ y → (x ≤ y ∨ x = nat.succ y)
lemma leq_or: forall x y : nat, 
  (leq x (nat.succ y) = tt) -> or (leq x y = tt) (x = nat.succ y) 
:= begin 
  intro x,
  induction x with w ih, 
  {
    intro y, 
    intro h, 
    left, 
    dunfold leq, 
    trivial,
  },
  {
    intro y,
    intro h,
    right, 
    cases y, 
    {
      dunfold leq at h, 
      have h2 := ih 0, 
      
    }
    
  } 

end 


-- Q3
-- ∀ x y : ℕ, x = y ∨ x ≠ y
lemma x_eq_or_ne_y: forall x y : nat, or (x = y) (not (x = y))
:= begin 
  intro x, 
  intro y, 
  have h : (x = y) ∨ ¬(x = y) 
  := begin 
    left, 
    cases x, 
    {
      cases y, 
      {
        trivial, 
      },
      {
        sorry
      }
    },
    {
      cases y, 
      {
        sorry
      },
      {
        sorry
      }
    }
  end,
  cases h, 
  {
    left, 
    exact h
  }, 
  {
    right, 
    exact h, 
  }
end 


-- Q4 
/-
consider the function listDelete defined below:
-/
def listDelete : list nat -> nat -> list nat
    | [] _ := []
    | (x :: L) 0 := L 
    | (x :: L) (nat.succ i) := x :: (listDelete L i)

/-
prove this:
-/
theorem listDelete_withinbounds:
  forall (L : list nat) (i : nat), 
    ltb i (len L)= tt -> 
    nat.succ(len (listDelete L i)) = len L 
    := begin 
    
  -- | [] _ := begin 
  --   intro h, 
  --   dunfold len,
  --   dunfold len at h, 
  --   dunfold listDelete, 
  --   dunfold len, 
  --   dunfold ltb at h, 
  -- end 
  -- | (x :: L) 0 := begin 

  -- end 
  -- | (x :: L) (nat.succ i) := begin 

  -- end 


  intro L, 
  intro i, 
  revert L, 
  induction i with x ih, 
  {
    intro L, 
    intro h, 

    dunfold listDelete, 
    dunfold len, 

    try {trivial}, 
    sorry 
  },
  {
    intro i, 
    intro h, 
    dunfold len, 
    
  }
end  


-- Q5
/-
consider the functions duplicateLast and lastElement defined below:
-/

def duplicateLast: list nat -> list nat 
  | [] := [] 
  | [x] := [x,x]
  | (x :: (y :: L)) := x :: (duplicateLast (y :: L))

def lastElement : list nat -> nat 
  | [] := 0 
  | [x] := x 
  | (x :: (y :: L)) := lastElement (y :: L) 

/-
prove this:
-/
theorem duplicateLast_app_if: forall L : list nat, 
  (not (L = [])) -> (duplicateLast L = app L [(lastElement L)])
:= begin 
  intro L, 
  intro h, 
  induction L with x L' ih, 
  {
    dunfold duplicateLast,
    dunfold app, 
    trivial, 
  },
  {
    dunfold app, 

  }
end 


-- Q6
/-
prove the theorem below. 
hint: do not use induction! use a result we have proven in our homeworks.
-/
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


theorem rev_injective: 
    ∀ L1 L2 : list nat, rev L1 = rev L2 -> L1 = L2
:= begin 
  intros L1 L2,
  intro h, 
  have h2 := rev_left_right L1 (rev L2), 
  have h3 := h2 h, 
  rw rev_involutive at h3, 
  exact h3, 
end 


-- Q7
/-
prove the theorem below. 
hint: do not use induction! use a result we have proven in our homeworks.
-/

def rl : list ℕ → ℕ → list ℕ 
 | [] 0 := []
 | [] (nat.succ n) := [] 
 | (x :: L) 0 := (x :: L)
 | (x :: L) (nat.succ n) := rl (app L [x]) n 

lemma rl_L1_L2: ∀ L1 L2: list ℕ, rl (app L1 L2) (len L1) = app L2 L1
:= begin
  intro L1, 
  induction L1 with x L1' ih, 
  {
    intro L2,
    cases L2, 
    {
      refl, 
    },
    {
      dunfold app, 
      dunfold len, 
      dunfold rl, 
      rw app_L_nil, 
    }
  },
  {
    intro L2, 
    dunfold app, 
    dunfold len, 
    dunfold rl, 
    have h1 := ih (app L2 [x]),
    rw app_assoc at h1, 
    rw h1, 
    rw <- app_assoc, 
    dunfold app, 
    trivial, 
  }
end

theorem rl_L_len_L: ∀ L : list ℕ, rl L (len L) = L 
:= begin
  intro L, 
  cases L with x L1, 
  {
    refl, 
  },
  {
    dunfold len, 
    dunfold rl, 
    have h1 := rl_L1_L2 L1 [x],
    rw h1, 
    dunfold app, 
    trivial, 
  }
end

lemma len_app_commut: 
    ∀ L1 L2 : list nat, len (app L1 L2) = len (app L2 L1)
:= begin 
  intros L1 L2, 
  have h := rl_L1_L2 L1 L2, 
  rw <- h, 
  have h2 := rl_L_len_L (app L1 L2),
  rw <- h2,  
  
end 


/-
consider the functions eleml and subset defined below:
-/

-- Q8 
def eleml : nat -> list nat -> bool 
  | _ [] := ff 
  | n (x :: L) := if (n = x) then tt else (eleml n L) 

def subset : list nat -> list nat -> Prop 
  | [] _ := true
  | (x :: L1) L2 := and (eleml x L2 = tt) (subset L1 L2)

-- Q8.1 
/-
prove the lemma below.
hint: you don't need induction.
-/
lemma subset_drop_head : 
forall L1 L2 : list nat, forall x : nat, 
    subset (x :: L1) L2 -> subset L1 L2 
:= begin 
  intros L1 L2, 
  intros h1 h2, 
  dunfold subset at h2, 
  cases h2 with h3 h4, 
  {
    exact h4, 
  },
end 

-- Q8.2 
/-
prove theorem subset_refl. 
hint: you will need a lemma that you will discover by generalization. that generalization resembles the one we did for app_L_3_times_failed in 14-code.lean. 
-/

lemma subset_L1_L2: ∀ L : list ℕ, subset [] L 
:= begin 
  intro L, 
  dunfold subset, 
  trivial, 
end 

theorem subset_refl: forall L : list nat, subset L L
:= begin 
  intro L, 
  have h := subset_L1_L2 L, 
  
end 



--  Q9 
/-
consider the function app_t3 given below:
-/

def app_t3 : list nat -> list nat -> list nat -> list nat 
  | list.nil list.nil acc := acc
  | [ ] (b :: L) acc := app_t3 [ ] L (b :: acc)
  | (a :: L) [ ] acc := app_t3 L [ ] (a :: acc)
  | (a :: L1) (b :: L2) acc := app_t3 (a :: L1) [ ] (app_t3 [ ] (b :: L2) acc) 

/-
suppose m3 is a candidate measure function for app_t3. write down the decreasing measure proof obligation(s) for m3.

do not define m3, and do not try to prove anything. just write down the proof obligation(s). 
-/
def m3 : list ℕ → list ℕ → list ℕ → ℕ := λ L1 L2 L3, 0 

lemma m3_dmpo1: ∀ L acc : list ℕ, ∀ b : ℕ,
  (m3 [] L (b :: acc)) < (m3 [] (b :: L) acc)
  := sorry 

lemma m3_dmpo2: ∀ L acc : list ℕ, ∀ a : ℕ,
  (m3 L [ ] (a :: acc)) < (m3 (a :: L) [ ] acc)
  := sorry 

lemma m3_dmpo3: ∀ L1 L2 acc : list ℕ, ∀ a b : ℕ,
  (m3 [ ] (b :: L2) acc) < (m3 (a :: L1) (b :: L2) acc)
  := sorry 

lemma m3_dmpo4: ∀ L1 L2 acc : list ℕ, ∀ a b : ℕ,
  (m3 (a :: L1) [ ] (app_t3 [ ] (b :: L2) acc)) < (m3 (a :: L1) (b :: L2) acc)
  := sorry 