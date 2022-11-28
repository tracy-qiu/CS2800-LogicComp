-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, Prof. Tripakis' Section

import .ourlibrary11
import .ourlibrary12
import .ourlibrary14


lemma plus_x_succ_y: ∀ x y : ℕ, nat.succ (plus x y) = plus x (nat.succ y) 
:= begin
    intros,
    induction x with z ih,
    {
        refl,
    },
    {
        dunfold plus,
        rw ih,
    }
end

lemma plus_commut: ∀ x y : ℕ, plus x y = plus y x 
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
        rw plus_x_succ_y, 
    }
end

lemma plus_assoc: 
    ∀ x y z : ℕ, plus x (plus y z) = plus (plus x y) z 
:= begin
    intros,
    induction x with w IH,
    {
        dunfold plus,
        refl,
    },
    {
        dunfold plus,
        rewrite IH,
    }
end

lemma mult_x_zero: ∀ x : ℕ, mult x 0 = 0 
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

lemma mult_succ: ∀ y z : ℕ, 
    plus y (mult y z) = mult y (nat.succ z)
:= begin
    intros,
    induction y with x ih,
    refl,
    dunfold plus,
    dunfold mult,
    dunfold plus,
    rw succeq,
    rw <- ih,
    rw plus_assoc,
    rw plus_assoc,
    rw plus_commut x z, 
end

lemma mult_commut: ∀ x y : ℕ, mult x y = mult y x 
:= begin
    intros,
    induction x with z ih,
    {
        dunfold mult,
        rw mult_x_zero,
    },
    {
        dunfold mult,
        rw ih,
        -- lemma discovery here!
        rw mult_succ,
    },
end

lemma app_assoc: ∀ L1 L2 L3 : list ℕ, 
    app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
    intros,
    induction L1 with x L IH,
    {
        refl,
    },
    {
        dunfold app,
        rw IH,
    }
end


def eqb : ℕ → ℕ → bool 
    | 0 0 := tt 
    | 0 (nat.succ y) := ff     
    | (nat.succ x) 0 := ff 
    | (nat.succ x) (nat.succ y) := eqb x y 
--

def ltb : ℕ → ℕ → bool 
    | 0 0 := ff 
    | 0 (nat.succ y) := tt 
    | (nat.succ x) 0 := ff 
    | (nat.succ x) (nat.succ y) := ltb x y 
--

def minus : ℕ → ℕ → ℕ 
    | 0 _ := 0
    | (nat.succ x) 0 := (nat.succ x)
    | (nat.succ x) (nat.succ y) := minus x y
--


def insrt : ℕ → list ℕ → list ℕ
  | x [] := [x] 
  | x (y :: L) := if (leq x y = tt) 
                  then x :: (y :: L) 
                  else y :: (insrt x L) 
-- 

def isort : list ℕ → list ℕ
  | [] := []  
  | (x :: L) := insrt x (isort L) 
-- 

