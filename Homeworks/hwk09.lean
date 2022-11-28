-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 9

/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Tracy Qiu, Erica Sammarco, Anushka Mantri
-/

/-
Technical instructions: same as in the last homework.

in particular, you are still NOT allowed to use functional induction in this homework. 
-/


import .ourlibrary11
import .ourlibrary12 
import .ourlibrary16 
import .ourlibraryite


-- GENERAL HINT FOR THIS AND FOLLOWING HOMEWORKS: IN SEVERAL PROBLEMS YOU WILL NEED TO DELAY INTRODUCTIONS (c.f. 16-code.lean)


/- HWK09-01: 
prove each of the following theorems. 

think: which ones need induction?
-/

theorem eqb_succ_inj: 
∀ x y : ℕ, eqb (nat.succ x) (nat.succ y) = tt → eqb x y = tt 
:= begin
-- ANSWER:
intros x y,
intro h,
cases x,
{
  cases y,
  {
    refl,
  },
  {
    dunfold eqb,
    trivial,
  }
},
{
  cases y,
  {
    trivial,
  },
  {
    dunfold eqb,
    dunfold eqb at h,
    assumption,
  }
}
end


theorem eqb_refl: ∀ x : ℕ, eqb x x = tt 
:= begin
-- ANSWER:
intro x,
induction x with y ih,
{
  refl,
},
{
  dunfold eqb,
  rw ih,
}
end

theorem leq_x_succ_x: ∀ x : ℕ, leq x (nat.succ x) = tt 
:= begin
-- ANSWER:
intro x,
induction x with y ih,
{
  refl,
},
{
  dunfold leq,
  assumption,
}
end


theorem eqb_eq_zero: ∀ x : ℕ, eqb x 0 = tt → x = 0 
:= begin
-- ANSWER:
intro x,
intro h,
cases x,
{
  refl,
},
{
  dunfold eqb at h,
  trivial,
}
end





/- HWK09-02: 
prove the following theorem:
-/
theorem eqb_iff_eq: ∀ x y : ℕ, eqb x y = tt ↔ x = y 
:= begin
  intros x, 
  induction x with x' ih, 
  {
    intro y,
    split, 
    {
      cases y, 
      {
        intro h, 
        trivial,  
      },
      {
        intro h, 
        trivial, 
      }
    },
    {
      intro h, 
      cases y, 
      repeat
      {
        trivial, 
      },
    }
  },
  {
    intro y, 
    split, 
    {
      cases y, 
      {
        intro h, 
        trivial, 
      },
      {
        intro h, 
        rw eqb at h, 
        have h1 := ih y, 
        cases h1 with h2 h3, 
        {
          have h4 := h2 h, 
          rw succeq,
          assumption, 
        }
      }
    },
    {
      cases y, 
      {
        intro h, 
        trivial, 
      },
      {
        intro h, 
        rw succeq at h, 
        have h1 := ih y, 
        cases h1 with h2 h3, 
        {
          have h4 := h3 h, 
          rw eqb, 
          assumption, 
        }
      }
    }
  }
end




/- HWK09-03:
 prove the following:
-/
lemma plus_1_eq: ∀ x y: ℕ, (plus x y.succ) = (plus x y).succ
:= begin
  intro x,
  induction x with y ih, 
  {
    intro y,
    refl,   
  },
  {
    intro y, 
    have h2 := ih y, 
    dunfold plus, 
    rw succeq,
    assumption, 
  }
end

theorem double_plus: ∀ x : ℕ, double x = plus x x 
-- ANSWER: 
:= begin
  intro x, 
  induction x with z ih, 
  {
    refl, 
  },
  {
    dunfold double, 
    dunfold plus,
    rw succeq, 
    have h1 := plus_1_eq z z,
    rw h1, 
    rw succeq, 
    exact ih, 
  }
end




/- HWK09-04:
 prove that our mult is associative. 
-/
-- ANSWER: 
lemma distrib_mult_plus: ∀ x y z : ℕ, mult (plus x y) z = plus (mult x z) (mult y z) :=
begin
  intros x y z,
  induction x with a ih,
  {
    refl,
  },
  {
    dunfold plus,
    dunfold mult,
    rw ih,
    rw plus_assoc,
  }
end

theorem mult_assoc: 
   ∀ x y z : ℕ, mult x (mult y z) = mult (mult x y) z 
:= begin
  intros x y z,
  induction x with a ih,
  {
    refl,
  },
  {
    dunfold mult,
    rw ih,
    rw distrib_mult_plus,
  }
end



/- HWK09-05:
 prove the following WITHOUT USING INDUCTION:

 hint: rewrite the goal several times, using the definition of square and the commutativity and associatity laws of mult. 
-/
def square (n : ℕ) := mult n n

lemma square_mult : forall n m, square (mult n m) = mult (square n) (square m) 
:= begin
-- ANSWER:
  intros n m, 
  dunfold square, 
  rw mult_assoc,
  rw mult_commut n m, 
  rw <- mult_assoc m n n,
  rw mult_commut, 
  rw mult_assoc,
  rw mult_commut,
end






/- HWK09-06:

earlier, we saw different ways to define "plus". we will revisit one of those definitions in this problem. 

suppose we define plus in this way:
-/

def plus4: nat -> nat -> nat 
  | x nat.zero := x
  | x (nat.succ y) := plus4 (nat.succ x) y   
    -- x + (y+1)  =  (x+1) + y 
--


/- HWK09-06-1:

prove the following: did you need induction? 
No, we did not need induction.
-/
theorem plus4_x_zero: ∀ x : ℕ, plus4 x 0 = x 
:= begin 
-- ANSWER:
  intro x, 
  refl, 
end


/- HWK09-06-2:

prove the following:

theorem plus4_zero_x: ∀ x : ℕ, plus4 0 x = x 

hint: use lemma discovery by generalization. 
-/
-- ANSWER:

lemma plus_equiv_plus4: ∀ x y : ℕ, plus x y = plus4 y x :=
begin
intro x,
induction x with z ih,
{
  intro,
  refl,
},
{
  intro,
  cases y,
  {
    dunfold plus,
    dunfold plus4,
    rw plus_commut,
    dunfold plus,
    rw <- ih 1,
    rw plus_commut,
    dunfold plus,
    rw succeq,
  },
  {
    dunfold plus,
    dunfold plus4,
    rw plus_commut,
    dunfold plus,
    have h1 := ih y.succ.succ,
    rw <- h1,
    rw plus_commut z,
    dunfold plus,
    rw succeq,
  }
}
end


theorem plus4_zero_x: ∀ x : ℕ, plus4 0 x = x := 
begin
intro x,
cases x with y z,
{
  refl,
},
{
  dunfold plus4,
  rw <- plus_equiv_plus4 y 1,
  rw plus_commut,
  dunfold plus,
  rw succeq,
}
end

lemma lem1: ∀ y : ℕ, plus4 1 y = nat.succ y := begin 
  intro, 
  induction y with x ih, 
  {
    refl,
  },
  {
    rw plus4, 
    sorry,
  }
end 

lemma lem2: ∀ x y : ℕ, plus4 (nat.succ x) y = nat.succ(plus4 x y) 
:= begin 
  intros, 
  revert x, 
  induction y with z ih,
  {
    intro, 
    refl, 
  },
  {
    intro, 
    rw plus4, 
    rw plus4, 
    have h := ih (nat.succ x),
    exact h,
  }
end 

theorem plus4_zero_x': ∀ x : ℕ, plus4 0 x = x := 
begin
intro x,
induction x with y ih,
{
  refl,
},
{
  
}
end

/- HWK09-07: 

prove that all four versions of plus, functions plus1, plus, plus3, and plus4, are equivalent. that is, prove the following three theorems:

theorem plus1_equiv_plus: ∀ x y : nat, plus1 x y = plus x y 

theorem plus_equiv_plus3: ∀ x y : nat, plus x y = plus3 x y

theorem plus3_equiv_plus4: ∀ x y : nat, plus3 x y = plus4 x y

-/

def plus1: nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := (plus1 x (nat.succ y))     
    -- (x+1) + y  =  x + (y+1)   

/-
def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  
    -- (x+1) + y  =  (x+y) + 1  
-/

def plus3: nat -> nat -> nat 
  | x nat.zero := x
  | x (nat.succ y) := nat.succ (plus3 x y)   
    -- x + (y+1)  =  (x+y) + 1 



theorem plus1_equiv_plus: ∀ x y : nat, plus1 x y = plus x y 
:= begin
  intro x, 
  induction x with x' ih, 
  {
    intro y, 
    refl, 
  },
  {
    intro y, 
    cases y, 
    {
      dunfold plus1, 
      dunfold plus, 
      have h := ih 1, 
      rw h, 
      rw <- plus_x_succ_y,
    },
    {
      dunfold plus1, 
      have h := ih y.succ.succ, 
      rw h, 
      dunfold plus, 
      rw plus_x_succ_y,
    }
  }
end


theorem plus_equiv_plus3: ∀ x y : nat, plus x y = plus3 x y
:= begin
  intros x y, 
  induction y with y' ih, 
  {
    dunfold plus3,
    rw plus_x_zero,
  },
  {
    dunfold plus3, 
    rw plus_1_eq,
    rw succeq,
    exact ih,  
  }
end

theorem plus3_equiv_plus4: ∀ x y : nat, plus3 x y = plus4 x y := 
begin
intros x y,
have h1 := plus_equiv_plus4 y x,
have h2 := plus_equiv_plus3 x y,
rw <- h2,
rw <- h1,
rw plus_commut,
end


/- HWK09-08: 
prove the following:
-/

theorem plus_n_n_injective: ∀ n m : ℕ, (plus n n = plus m m) → n = m 
:= begin
-- ANSWER:
intro,
induction n with a ih,
{
  intro,
  intro h,
  cases m,
  {
    refl,
  },
  {
    dunfold plus at h,
    trivial,
  },
},
{
  intro,
  intro h,
  cases m,
  {
    dunfold plus at h,
    trivial,
  },
  {
    have h1 := ih m,
    dunfold plus at h,
    rw succeq at h,
    rw plus_1_eq at h,
    rw plus_1_eq at h,
    rw succeq at h,
    have h2 := h1 h,
    rw succeq,
    assumption,
  },
},
end




/- HWK09-09:
Prove the theorem rev_nil_implies_nil:
-/
-- ANSWER: 

lemma not_app_L_x_is_empty: ∀ (x : ℕ) (L : list ℕ), ¬app L [x] = [] :=
begin
intros x L,
intro h,
cases L,
repeat {
  trivial,
}
end

theorem rev_nil_implies_nil: ∀ L : list nat, rev L = [] → L = [] 
:= begin
intro L,
intro h,
cases L with x L2,
{
  refl,
},
{
  have h1 := not_app_L_x_is_empty x (rev L2),
  trivial,
}
end



/- HWK09-10: 

for the function rl given below, prove the theorem

theorem rl_L_len_L: ∀ L : list ℕ, rl L (len L) = L 

hint: you need lemmas. one of them relates rl, app, and len. discover that lemma by generalization. 
-/

def rl : list ℕ → ℕ → list ℕ 
 | [] 0 := []
 | [] (nat.succ n) := [] 
 | (x :: L) 0 := (x :: L)
 | (x :: L) (nat.succ n) := rl (app L [x]) n 
--
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

/- HWK09-11: 

we are now strong enough magicians to start proving the correctness of isort! in this homework we will prove the first part, namely that isort always produces sorted lists. 

the isort implementation is given in ourlibrary16.lean: 
-/

#check insrt 
#check isort 

/-
for this problem, you can choose between two options:

  - option A: prove theorem isort_sortedp, which uses sortedp 
  
      theorem isort_sortedp:  ∀ L : list ℕ, sortedp (isort L)

  or

  - option B: prove theorem isort_sortedb, which uses sortedb

      theorem isort_sortedb:  ∀ L : list ℕ, sortedb (isort L)


you ONLY HAVE TO PROVE ONE OF THEM! but feel free to prove both if you like! each of them is educational in its own way, and we will review both of them later in class. 

if you prove only one of them (this is fine) we recommend that you comment-out the definition of sorted that you DON'T want to use, so that you don't use it by accident. 

you allowed to use any of the lemmas in our lecture notes from the LEAN library, and in particular the two lemmas below:

#check band_eq_false_eq_eq_ff_or_eq_ff 
#check band_eq_true_eq_eq_tt_and_eq_tt

-/
#check band_eq_false_eq_eq_ff_or_eq_ff 
#check band_eq_true_eq_eq_tt_and_eq_tt

def sortedp : list ℕ → Prop -- note: returns Prop, not bool 
  | [] := true
  | [_] := true  
  | (x :: (y :: L)) := (leq x y = tt) ∧ (sortedp (y :: L)) 
-- 

def sortedb : list ℕ → bool 
  | [] := tt 
  | [_] := tt 
  | (x :: (y :: L)) := (leq x y) && (sortedb (y :: L)) 
--


-- choose one of the two theorems below to prove: 

-- theorem isort_sortedp:  ∀ L : list ℕ, sortedp (isort L)
-- := sorry 

lemma not_leq_x_y_imp_leq_y_x: ∀ x y : ℕ, ¬(leq x y) = tt → (leq y x) = tt
:= begin
  intro x, 
  induction x with x1 ih, 
  {
    intro y,
    intro h,  
    dunfold not at h, 
    dunfold leq at h, 
    trivial, 
  },
  {
    intro y, 
    cases y, 
    {
      intro h, 
      refl, 
    },
    {
      dunfold leq, 
      have h1 := ih y,
      exact h1, 
    }
  }
end

lemma insrt_sortedb: ∀ L : list ℕ, ∀ x : ℕ, sortedb L  = tt → sortedb (insrt x L) = tt
:= begin
  intro L, 
  induction L with y L1 ih,
  {
    intro x, 
    intro h, 
    refl, 
  },
  {
    intro x, 
    intro h, 
    dunfold insrt, 
    have h1 := classical.em (leq x y = tt),
    cases h1, 
    {
      have h2 := itetrue ((leq x y) = tt) h1 (list ℕ) (x :: y :: L1) (y :: insrt x L1),
      rw h2, 
      dunfold sortedb, 
      rw band_eq_true_eq_eq_tt_and_eq_tt,
      split, 
      repeat
      {
        assumption, 
      },
    },
    {
      have h2 := itefalse ((leq x y) = tt) h1 (list ℕ) (x :: y :: L1) (y :: insrt x L1),
      rw h2,
      cases L1 with head tail,
      {
        dunfold insrt, 
        dunfold sortedb, 
        rw band_eq_true_eq_eq_tt_and_eq_tt,
        split, 
        {
          have h3 := not_leq_x_y_imp_leq_y_x x y, 
          have h4 := h3 h1,
          assumption, 
        },
        {
          trivial, 
        }
      },
      {
        clear h2, 
        dunfold insrt, 
        dunfold sortedb at h, 
        have h2 := classical.em (leq x head = tt), 
        cases h2, 
        {
          have h3 := itetrue (leq x head = tt) h2 (list ℕ) (x :: head :: tail) (head :: insrt x tail),
          rw h3, 
          dunfold sortedb, 
          have h4 := not_leq_x_y_imp_leq_y_x x y, 
          have h5 := h4 h1, 
          rw band_eq_true_eq_eq_tt_and_eq_tt,
          split, 
          {
            assumption, 
          },
          {
            rw band_eq_true_eq_eq_tt_and_eq_tt,
            split, 
            {
              assumption, 
            },
            {
              rw band_eq_true_eq_eq_tt_and_eq_tt at h, 
              cases h, 
              assumption, 
            }
          }
        },
        {
          have h3 := itefalse (leq x head = tt) h2 (list ℕ) (x :: head :: tail) (head :: insrt x tail),
          rw h3,  
          dunfold sortedb, 
          rw band_eq_true_eq_eq_tt_and_eq_tt,
          split, 
          {
            rw band_eq_true_eq_eq_tt_and_eq_tt at h, 
            cases h, 
            assumption,
          },
          {
            have ih_1 := ih x, 
            rw band_eq_true_eq_eq_tt_and_eq_tt at h, 
            cases h, 
            have h4 := ih_1 h_right, 
            dunfold insrt at h4, 
            rw h3 at h4, 
            assumption, 
          }
        }
      }
    },
  }
end


theorem isort_sortedb:  ∀ L : list ℕ, sortedb (isort L) = tt :=
begin
  intro L,
  induction L with x L2 ih,
  {
    refl,
  },
  {
    dunfold isort,
    have h1 := insrt_sortedb (isort L2) x, 
    rw h1, 
    exact ih, 
  }
end





-- in class solution

lemma leq_xy_ff: ∀ x y : ℕ, leq x y = ff → leq y x = tt := begin 
  intro, 
  induction x with z ih, 
  {
    intro, 
    intro h, 
    rw leq at h, 
    trivial, 
  },
  {
    intro, 
    intro h, 
    cases y with w, 
    {
      refl, 
    },
    {
      rw leq, 
      rw leq at h, 
      have h2 := ih w h, 
      exact h2, 
    }
  }
end 

-- lemma insrt_sortedb': ∀ L : list ℕ, ∀ x : ℕ, sortedb L  = tt → sortedb (insrt x L) = tt
-- := begin
--   intro, 
--   intro,
--   intro h, 
--   induction L with y L1 ih, 
--   {
--     dunfold insrt, 
--     dunfold sortedb, 
--     refl,
--   },
--   {
--     dunfold insrt,  have h1 : (leq x y = tt) ∨ (leq x y = ff) 
--     := begin
--       cases (leq x y),
--       {
--         right, 
--         refl,
--       },
--       {
--         left, 
--         refl,
--       },
--     end,
--     cases h1, 
--     {
--       rw h1, 
--       rw itetrue, 
--       {
--         dunfold sortedb, 
--         rw h1, 
--         rw tt-band, 
--         exact h, 
--       },
--       {
--         refl,
--       }
--     },
--     {
--       rw h1, 
--       rw itefalse, 
--       {
--         have h2 := leq_xy_ff x y h1, 
--         cases L1, 
--         {
--           dunfold insrt, 
--           dunfold sortedb, 
--           rw band_tt, 
--           exact h2, 
--         },
--         {
--           have h3: (leq x z = tt) ∨ (leq x z = ff) 
--           := begin
--             cases (leq x z),
--             {
--               right, 
--               refl,
--             },
--             {
--               left, 
--               refl,
--             },
--           end,
--           cases h3,
--           {
--             rw h3, 
--             rw itetrue, 
--             {
--               dunfold sortedb, 
--               rw h2, 
--               rw tt_band, 
--               rw h3, 
--               rw tt_band,
--               dunfold sortedb at h, 
--               rw band_eq_true_eq_eq_tt_and_eq_tt at h,
--               cases h with h11 h22, 
--               exact h22, 
--             },
--             {
--               refl,
--             }
--           },
--           {
--             rw h3, 
--             rw itefalse, 
--             {
--               dunfold sortedb,
--               dunfold sorted b at h, 
--               rw band_eq_true_eq_eq_tt_and_eq_tt at h, 
--               cases hs with h11 h22, 
--               rw h11, 
--               rw tt_band, 
--               have h4 := ih h22, 
--               dunfold insert at h4, 
--               rw h3 at h4, 
--               rw itefalse at h4, 
--               exact h4, 
--               intro, trivial, 
--             },
--             intro, 
--             trivial,
--           }
--         }
--       },
--       intro, 
--       trivial,
--   }
   
-- end 


lemma insrt_sortedb': ∀ L : list ℕ, ∀ x : ℕ, sortedb L  = tt → sortedb (insrt x L) = tt
:= begin
  intro, 
  intro,
  intro h, 
  induction L with y L1 ih, 
  {
    dunfold insrt, 
    dunfold sortedb, 
    refl,
  },
  {
    dunfold insrt, 
    have h1 : (leq x y = tt) ∨ (leq x y = ff) 
    := begin
      cases (leq x y),
      {
        right, 
        refl,
      },
      {
        left, 
        refl,
      },
    end,

    sorry
  },
end 


-- lemma insrt_sortedb': ∀ L : list ℕ, ∀ x : ℕ, sortedb L  = tt → sortedb (insrt x L) = tt
-- := begin
--   intro, 
--   intro,
--   intro h, 
--   induction L with y L1 ih, 
--   {
--     dunfold insrt, 
--     dunfold sortedb, 
--     refl,
--   },
--   {
--     dunfold insrt,  
--     have h1 : (leq x y = tt) ∨ (leq x y = ff) 
--     := begin
--       cases (leq x y),
--       {
--         right, 
--         refl,
--       },
--       {
--         left, 
--         refl,
--       },
--     end,
--     cases h1, 
--     {
--       rw h1, 
--       rw itetrue, 
--       {
--         dunfold sortedb, 
--         rw h1, 
--         rw tt-band, 
--         exact h, 
--       },
--       {
--         refl,
--       }
--     },
--     {
--       rw h1, 
--       rw itefalse, 
--       {
--         have h2 := leq_xy_ff x y h1, 
--         cases L1, 
--         {
--           dunfold insrt, 
--           dunfold sortedb, 
--           rw band_tt, 
--           exact h2, 
--         },
--         {
--           have h3: (leq x z = tt) ∨ (leq x z = ff) 
--           := begin
--             cases (leq x z),
--             {
--               right, 
--               refl,
--             },
--             {
--               left, 
--               refl,
--             },
--           end,
--           cases h3,
--           {
--             rw h3, 
--             rw itetrue, 
--             {
--               dunfold sortedb, 
--               rw h2, 
--               rw tt_band, 
--               rw h3, 
--               rw tt_band,
--               dunfold sortedb at h, 
--               rw band_eq_true_eq_eq_tt_and_eq_tt at h,
--               cases h with h11 h22, 
--               exact h22, 
--             },
--             {
--               refl,
--             }
--           },
--           {
--             rw h3, 
--             rw itefalse, 
--             {
--               dunfold sortedb,
--               dunfold sorted b at h, 
--               rw band_eq_true_eq_eq_tt_and_eq_tt at h, 
--               cases hs with h11 h22, 
--               rw h11, 
--               rw tt_band, 
--               have h4 := ih h22, 
--               dunfold insert at h4, 
--               rw h3 at h4, 
--               rw itefalse at h4, 
--               exact h4, 
--               intro, trivial, 
--             },
--             intro, 
--             trivial,
--           }
--         }
--       },
--       intro, 
--       trivial,
--   }
   
-- end 

theorem isort_sortedb':  ∀ L : list ℕ, sortedb (isort L) = tt :=
begin
  intro L,
  induction L with x L2 ih,
  {
    refl,
  },
  {
    dunfold isort,
    have h1 := insrt_sortedb' (isort L2) x, 
    rw h1, 
    exact ih, 
  }
end