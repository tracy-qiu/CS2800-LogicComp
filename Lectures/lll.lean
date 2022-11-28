-- CS 2800 LOGIC AND COMPUTATION, FALL 2021
-- COPYRIGHT 2021 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 


/-

how's hwk09 going?

-/







/-

ANY QUESTIONS ABOUT THE MATERIAL IN 17-code.lean and 18-code.lean?



- how not to lose your bool cases

- the tactic clear 

- notation



-/





--  QUIZ TIME!





/- 
Qz24Sec4: Does the claim given in class hold?

  ∀ L1 L2 : list nat, len (app L1 L2) = len (app L2 L1) 

ANSWERS:
 YES
 NO

-- respond at: https://pollev.com/tripakis
-/















/- 
Qz25Sec4: Answer the question posed in class:

Suppose we are given lemma lem:

lem : ∀ L1 L2 : list nat, len (app L1 L2) = len (app L2 L1) 

Then can we prove the claim below?

  ∀ L : list nat, ∀ x : nat, len (app L [x]) = nat.succ (len L) 

ANSWERS:
1. we can prove it using lem and function rewrites (without other lemmas or induction)
2. we can prove it but we need other lemmas or induction 
3. we cannot prove it because it does not hold 

-- respond at: https://pollev.com/tripakis
-/















----------------------------------------------------
-- FUNCTIONAL INDUCTION 
----------------------------------------------------

/-
-/

-- are two natural numbers equal?
def eqb : ℕ → ℕ → bool 
    | 0 0 := tt 
    | 0 (nat.succ y) := ff     
    | (nat.succ x) 0 := ff 
    | (nat.succ x) (nat.succ y) := eqb x y 


-- equality is symmetric -- proof by standard induction, delaying intro of y: 
theorem eqb_sym: ∀ x y : ℕ, eqb x y = eqb y x 
:= begin
  intro,
  induction x with z ih,
  {
    intro,
    cases y with w,
    {
      refl,
    },
    {
      refl,
    }
  },
  {
    intro,
    cases y with w,
    {
      refl,
    },
    {
      rw eqb,
      rw eqb,
      rw ih w,
    }
  }
end



-- proof using _functional induction_:
theorem eqb_sym_funind: ∀ x y : ℕ, eqb x y = eqb y x 
  | 0 0 := begin
    refl,
  end
  | 0 (nat.succ w) := begin
    rw eqb,
    rw eqb,
  end
  | (nat.succ u) 0 := begin
    refl,
  end
  | (nat.succ u) (nat.succ w) := begin
    rw eqb,
    rw eqb,
    have h := eqb_sym_funind u w ,
    exact h,
  end

theorem eqb_sym_funind2: ∀ x y : ℕ, eqb x y = eqb y x 
  | 0 y := begin
    cases y with w,
    {
      refl,
    },
    {
      refl,
    }
  end
  | (nat.succ u) 0 := begin
    refl,
  end
  | (nat.succ u) (nat.succ w) := begin
    rw eqb,
    rw eqb,
    have h := eqb_sym_funind2 u w ,
    exact h,
  end
--



theorem eqb_sym_funind3: ∀ x y : ℕ, eqb x y = eqb y x 
  | 0 y := begin
    cases y with w,
    {
      refl,
    },
    {
      refl,
    }
  end
  | (nat.succ z) u := begin
    have h := eqb_sym_funind3 (nat.succ z) u ,
    exact h,
  end

--




theorem eqb_sym_funind: ∀ x y : ℕ, eqb x y = eqb y x 
  | x y := begin
    rw eqb_sym_funind  ,
  end

--

/- WOW! THEOREMS WITH PATTERN MATCHING!
-/

theorem bool_tt_or_ff: ∀ b : bool, b = tt ∨ b = ff 
  | tt := begin
    left,
    refl,
  end
  | ff := begin
    right,
    refl,
  end

--

/- WOW!   INDUCTION = RECURSION!

BUT: CAREFUL WITH TERMINATION! 

-/


theorem eqb_sym_funind_illegal: ∀ x y : ℕ, eqb x y = eqb y x
    | x y := begin
        have h := eqb_sym_funind_illegal x y, -- illegal recursive call, arguments don't decrease! 
        assumption, 
    end




-- luckily for soundness, we cannot use functional induction to prove false:
theorem false_funind_attempt: ∀ x : ℕ, false
    | x := begin
        have h := false_funind_attempt x, 
        trivial,
    end





theorem eqb_sym_w_funind_fewer_cases: ∀ x y : ℕ, eqb x y = eqb y x
    -- we can combine the first two cases into a single one:


theorem eqb_sym_w_funind_even_fewer_cases: ∀ x y : ℕ, eqb x y = eqb y x
    -- we can combine the first two cases into a single one:
    | 0 x := begin
        cases x,
        refl,
        refl,
    end
    -- we can also combine the last two cases into a single one:







----------------------------------------------------
-- how powerful is functional induction?  
----------------------------------------------------

/-
how powerful is functional induction?  is it more powerful than standard induction (the one using the "induction" tactic). meaning, are there any theorems that CANNOT be proven with standard induction (and enough lemmas) but that CAN be proven with functional induction?

the answer is no. however, functional induction makes some proofs look extremely easy, whereas the same proof requires some ingenuity to complete with standard induction. let us illustrate this with an example: 
-/


/-
keep odd positions:
-/
def kop : list ℕ → list ℕ 
  | [] := []
  | [x] := [] 
  | (x :: y :: L) := y :: (kop L) 
--

example: kop [] = [] := begin refl, end 
example: kop [1] = [] := begin refl, end 
example: kop [1,2] = [2] := begin refl, end 
example: kop [1,2,3] = [2] := begin refl, end 
example: kop [1,2,3,4] = [2,4] := begin refl, end 
example: kop [0,1,2,3,4] = [1,3] := begin refl, end 
example: kop [0,1,2,3,4,5] = [1,3,5] := begin refl, end 


/-
nat division by two:
-/
def div2 : ℕ → ℕ 
  | 0 := 0 
  | 1 := 0 
  | (nat.succ (nat.succ x)) := nat.succ (div2 x) 
--

example: div2 0 = 0 := begin refl, end 
example: div2 1 = 0 := begin refl, end 
example: div2 2 = 1 := begin refl, end 
example: div2 3 = 1 := begin refl, end 
example: div2 100 = 50 := begin refl, end 
example: div2 101 = 50 := begin refl, end 


/-
practice!!! try to prove this here in class:

  ∀ L : list ℕ, len (kop L) = div2 (len L)

hint: use functional induction. 


CHALLENGE PROBLEM!
try to prove the above claim at home WITHOUT functional induction. 
hint: you will need an awesome lemma! 
-/
theorem lenkopfunind': ∀ L : list ℕ, len (kop L) = div2 (len L)
:= begin 
  intro L, 
  cases L with L1 L2, 
  {
    dunfold kop, 
    refl,
  },
  {
    dunfold len,
    
  }
end 

-- with functional induction the proof is incredibly simple and uses no lemmas at all!
theorem lenkopfunind: ∀ L : list ℕ, len (kop L) = div2 (len L)
  | [] := begin 
    refl,
  end 
  | [x] := begin 
    rw kop, 
    rw len, 
    rw len, 
    rw div2, 
    -- or just refl
  end 
  | (x :: y :: L) := begin 
    rw kop, 
    rw len, 
    rw len, 
    rw len, 
    rw div2, 
    rw succeq, 
    have h := lenkopfunind L, 
    exact h, 
  end

