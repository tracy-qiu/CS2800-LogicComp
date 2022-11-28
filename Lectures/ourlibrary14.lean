-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 

lemma plus_x_zero: ∀ x : ℕ, plus x 0 = x 
:= begin
    intros,
    induction x with y ih,
    {
        refl,
    },
    {
        dunfold plus,
        rw ih,
    }
end

lemma app_L_nil: ∀ L : list ℕ, app L [] = L 
:= begin
    intro,
    induction L with x L2 ih,
    { 
        refl,
    },
    { 
        unfold app,
        rewrite ih,
    }
end



def genzeros : ℕ → list ℕ 
  | 0 := []
  | (nat.succ n) := 0 :: (genzeros n)
--

def apply : list ℕ → (ℕ → ℕ) → list ℕ 
    | [] _ := []
    | (x :: L) f := (f x) :: (apply L f)
--

def even : nat → bool 
    | 0 := tt 
    | 1 := ff 
    | (nat.succ (nat.succ x)) := even x 
--

def even_v2 : nat → bool
    | 0 := tt 
    | (nat.succ x) := negb (even_v2 x)
--


def double : ℕ → ℕ 
    | 0 := 0
    | (nat.succ x) := nat.succ (nat.succ (double x))
--

def rev : list nat -> list nat 
  | [] := []
  | (a :: L) := app (rev L) [a] 
--

def leq : ℕ → ℕ → bool 
  | 0 y := tt 
  | (nat.succ x) 0 := ff 
  | (nat.succ x) (nat.succ y) := leq x y 
--
