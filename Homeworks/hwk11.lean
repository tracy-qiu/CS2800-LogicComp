-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 11

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: ...
-/

/-
Technical instructions: same as in the last homework.
-/


import .ourlibrary16


-- feel free to remove the notation if it bothers you
section local_notation

local notation x + y := plus x y 
local notation x - y := minus x y 
local notation x * y := mult x y 
local notation x ≤ y := leq x y = tt  
local notation x < y := ltb x y = tt  




/- HWK11-01: 
prove the following theorems and lemmas. 

NOTE: -, +, *, ≤, <, is notation for our own functions minus, plus, mult, leq, ltb. 
-/

lemma leq_x_zero: ∀ x : ℕ, x ≤ 0 → x = 0 
 ... 

lemma ltb_zero_false: ∀ x : ℕ, ¬ x < 0 
 ... 

lemma ltb_trans: ∀ x y z : ℕ, x < y → y < z → x < z 
 ... 

lemma leq_ltb_ltb: ∀ x y z : ℕ, x ≤ y → y < z → x < z 
 ... 

lemma ltb_succ_succ: ∀ x : ℕ, x < nat.succ (nat.succ x)
 ... 

lemma x_lt_x_plus_succ_y: ∀ x y : ℕ, x < x + nat.succ y
 ... 

lemma x_minus_0: ∀ x : ℕ, x - 0 = x
 ... 

lemma minuslem2: ∀ x y : ℕ, 
  x < y → y - (x+1) = (y-1) - x 
 ...

lemma minuslem3: ∀ x y z : ℕ, 
  x < y → z ≤ x → x - z < y - z 
 ...

lemma ltb_1_leb: ∀ x y : ℕ, x < y → x+1 ≤ y 
 ... 

lemma minuslem4: ∀ x y : ℕ, x < y → x ≤ (y-1) 
 ... 

lemma ltb_plus_left: ∀ (x y z : ℕ), x < y <-> (z + x < z + y)
 ... 

lemma ltb_leq: ∀ x y : ℕ, x < y → x ≤ y 
 ... 

lemma minus_plus_cancel: 
  ∀ x y : ℕ, x ≤ y → (y - x) + x = y 
 ... 

lemma x_ltb_x_plus_y: ∀ x y : ℕ, y ≠ 0 → x < x + y 
 ... 

lemma ltb_x_y_0: ∀ x y : ℕ, 0 < y → x < x + y 
 ... 


/- HWK11-02: 

does the function drop_last below terminate?

if you claim yes, provide a measure function for it, write down all decreasing measure proof obligations for it, and prove them.

if you claim no, provide a counterexample: i.e., an input for which drop_last does not terminate. 
-/

def drop_last : list ℕ → list ℕ 
  | [] := []
  | [a] := []
  | (a :: b :: L) := a :: (drop_last (b :: L))

-- ANSWER: 
... 


/- HWK11-03: 

does the function prefixes below terminate?

if you claim yes, provide a measure function for it, write down all decreasing measure proof obligations for it, and prove them.

if you claim no, provide a counterexample: i.e., an input for which drop_last does not terminate. 
-/

def prefixes : list ℕ → list (list ℕ) 
  | [] := [[]]
  | (a :: L) := (a :: L) :: (prefixes (drop_last (a :: L)))

-- [1,2,3]   ----->  [ [1, 2, 3], [1, 2], [1], [] ]

-- ANSWER: 
 ... 



/- HWK11-04: 
for the function f2 given below, and regardless of whether LEAN can prove its termination, do the following:

1. devise a measure function m_f2 for f2. 
2. write the decreasing measure proof obligation(s) for m_f2. 
3. prove the decreasing measure proof obligation(s) that you came up with in step 2. 
-/

def f2 : list ℕ → ℕ → ℕ 
  | [] 0 := 0
  | [] (nat.succ y) := 1 + (f2 [] (y-1))
  | (a :: L) y := 1 + (f2 L y) 

-- ANSWER: 

-- measure function for f3:
def m_f2 ... 

-- decreasing measure proof obligations
 ... 



/- HWK11-05: 
for the function f3 given below, and regardless of whether LEAN can prove its termination, do the following:

1. devise a measure function m_f3 for f3. 
2. write the decreasing measure proof obligation(s) for m_f3. 
3. prove the decreasing measure proof obligation(s) that you came up with in step 2. 
-/


def f3: ℕ → list ℕ 
  | n := if (n < 100) then (n :: (f3 (n+1))) else [n] 

-- ANSWER: 

-- measure function for f3:
def m_f3 ... 


-- decreasing measure proof obligations:
 ... 


/- HWK11-06: 
for the function f5 given below, and regardless of whether LEAN can prove its termination, do the following:

1. devise a measure function m_f5 for f5. 
2. write the decreasing measure proof obligation(s) for m_f5. 
3. prove the decreasing measure proof obligation(s) that you came up with in step 2. 
-/

def f5: ℕ → ℕ → ℕ 
  | 0 0 := 0
  | x y := if (x < y) then (1 + (f5 y x)) else (2 + (f5 (x-1) y))

-- ANSWER: 

-- measure function for f5:
def m_f5 ... 

-- decreasing measure proof obligations:




/- HWK11-07:

consider the function f7 defined below, where:
-/

def div2: ℕ → ℕ 
    | 0 := 0
    | 1 := 0 
    | (nat.succ (nat.succ x)) := nat.succ (div2 x)    


def f7 : nat -> nat -> nat 
  | x y := if (x = 0 ∨ y = 0 ∨ x = y) then 0
           else if (even x = tt) then f7 (div2 x) y
           else if (even y = tt) then f7 x (div2 y)
           else if (x < y) then f7 x (y - x) 
           else f7 (x - y) y 

/- 
does f7 terminate? if not, provide a counterexample, that is, an input which leads to non-termination. if yes then:

 1. provide a measure function for f7 

 2. write down the decreasing measure proof obligation(s) (notice that this question is independent from question 1, that is, independent from how exactly the measure function is defined -- although it does depend on the signature of the measure function) 

OPTIONAL CHALLENGE: (this part is optional and will not be graded)
 3. prove the decreasing measure proof obligation(s)  

-/

-- ANSWER: 
... 




/- HWK11-08:

consider the function app_t2 defined below:
-/
def app_t2 : list ℕ → list ℕ → list ℕ → list ℕ 
  | [] [] acc := acc
  | [] (b :: L) acc := app_t2 [] L (b :: acc)
  | (a :: L1) L2 acc := app_t2 L1 L2 (a :: acc)


/- 
suppose m_app_t2 is a candidate measure function for app_t2. write down the decreasing measure proof obligations for m_app_t2. you do not have to prove them, and you do not have to define what m_app_t2 is. 

OPTIONAL CHALLENGE: (this part is optional and will not be graded)
 define m_app_t2 and prove its decreasing measure proof obligations. 

-/

-- ANSWER: 
... 




/- HWK11-09: 

consider the function app_t4 defined below:
-/

def app_t4 : list ℕ → list ℕ → list ℕ → list ℕ 
  | [] [] acc := acc
  | [] (b :: L) acc := app_t4 [] L (b :: acc)
  | (a :: L) [] acc := app_t4 [] (a :: L) acc
  | (a :: L1) (b :: L2) acc := app_t4 (a :: L1) [] (app_t4 acc [] (b :: L2)) 


/- 
suppose mt4 is a candidate measure function for app_t4. write down the decreasing measure proof obligations for mt4. you do not have to prove them, and you do not have to define what mt4 is. 

OPTIONAL CHALLENGE: (this part is optional and will not be graded)
 do you think app_t4 is terminating? if yes, define mt4 and prove its decreasing measure proof obligations. if not, why not? 

-/

-- ANSWER: 

... 


end local_notation
