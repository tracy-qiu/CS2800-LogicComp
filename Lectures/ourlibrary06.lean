-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  
--

def len : list nat -> nat 
  | [] := 0 
  | (_ :: L) := nat.succ (len L)
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
