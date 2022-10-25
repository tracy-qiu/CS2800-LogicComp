-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  
--

theorem zero_plus: ∀ x : nat, plus 0 x = x 
:= begin
    intro,
    reflexivity,
end

def mult : ℕ → ℕ → ℕ 
  | nat.zero _ := nat.zero 
  | (nat.succ x) y := plus y (mult x y)  
--

def len : list nat -> nat 
  | [] := 0 
  | (_ :: L) := nat.succ (len L)
--

def app : list ℕ → list ℕ → list ℕ 
  | [] L := L 
  | (x :: L1) L2 := x :: (app L1 L2)
--

def negb : bool -> bool 
    | tt := ff 
    | ff := tt 
--

def andb : bool -> bool -> bool 
    | ff _ := ff 
    | tt x := x 
--

def orb : bool -> bool -> bool 
    | tt _ := tt 
    | ff x := x 
--

inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

open weekday 

def next_workday : weekday → weekday 
    | sunday := monday
    | monday := tuesday
    | tuesday := wednesday
    | wednesday := thursday
    | thursday := friday
    | friday := monday
    | saturday := monday
--


lemma succeq: ∀ x y : ℕ, (nat.succ x) = (nat.succ y) ↔ x = y 
:= begin
  intros,
  split,
  intro h,
  simp at h,
  assumption,
  intro h,
  rw h,
end


lemma listeq: ∀ x y : ℕ, ∀ L1 L2 : list ℕ, (x :: L1) = (y :: L2) ↔ (x = y) ∧ (L1 = L2)
:= begin
  intros,
  split,
  {
    intro h,
    simp at h,
    assumption,
  },
  {
    intro h,
    simp,
    assumption,
  },
end
