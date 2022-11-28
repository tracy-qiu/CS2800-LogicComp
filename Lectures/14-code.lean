-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11
import .ourlibrary14


----------------------------------------------------
-- INDUCTION continued
----------------------------------------------------




---------------------
-- LEMMA DISCOVERY 
---------------------

/- 
lemmas are like "helper" functions. often we reach a point in the proof where we have a goal which seems plausible, given the hypotheses that we have. we can go ahead and prove that goal within the proof of the main theorem using the "have" mechanism that we have already seen. but this leads to unreasonably long proofs, which are unreadable, and non-reusable. just like in programming, in proving also we need a principle of modularity. this is given to us by lemmas. instead of proving what we need within the main theorem, we separate it and prove it outside as a lemma. let us illustrate this:
-/

#check plus_x_zero 

lemma lem1 : ∀ y z : ℕ, (plus y z).succ = plus y z.succ 
:= begin 
    intros, 
    induction y with x ih, 
    {
        dunfold plus, 
        refl,
    },
    {
        dunfold plus, 
        rw succeq, 
        exact ih, 
    }
end 


-- let's try to prove that plus is commutative: 
theorem plus_commut_try: ∀ (x y : nat), plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        dunfold plus,
        -- rw plus also works instead of dunfold plus 
        /-
        have := plus_x_zero y, 
        rw this, 
        -/
        -- rw plus_x_zero y,
        rw plus_x_zero,
    },
    {
        dunfold plus,
        rw ih,
        -- copy paste goal and prove it outside
        rw lem1, 
        /-
        -- current goal: (y+z) + 1 = y + (z+1) 
        -- we reached a point where we have something that looks true, but just _refl_ won't cut it:
        try {refl}, -- nothing happens
        -- indeed, dunfold doesn't apply:
        try {dunfold plus,},
        /- this is a case of "lemma discovery". we will face this situation very often, in fact, almost always. we realize that in order to prove a "bigger" result, we need "smaller" results. just like when defining "main" programs we need "helper" functions, also when we prove "main" theorems, we need "helper" theorems, or lemmas. 
        -/
        sorry,
        -/
    }
end

-- we can more/less "copy-paste" the goal that we were stuck-with above, and try to prove it separately as a lemma:
lemma plus_y_succ_z: ∀ y z : ℕ, nat.succ (plus y z) = plus y (nat.succ z) 
:= begin
    intros,
    induction y with w ih,
    {
        refl,
    },
    {
        dunfold plus,
        rw ih,
    }
end

-- now we can return to our theorem and complete the proof:
theorem plus_commut: ∀ x y : ℕ, plus x y = plus y x 
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
        rw plus_y_succ_z, -- we call the new lemma
    }
end

/- note that variable names in the lemma don't have to be identical to those in the theorem. a lemma is like a function. we can "call" it with any arguments that we want. let us illustrate this by restating and reproving the same lemma with different variable names:
-/
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

-- we can reprove our theorem using the modified lemma:
theorem plus_commut_2: ∀ x y : ℕ, plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        rw plus_x_zero, 
        dunfold plus,
        refl,
    },
    {
        dunfold plus,
        rw ih,
        rw plus_x_succ_y, -- even though our variables are called y and z, LEAN can still match them ("unify" them) with the names x and y used in the lemma plus_x_succ_y
    }
end

theorem plus_commut_3: ∀ x y : ℕ, plus x y = plus y x 
:= begin
    intros,
    induction x with z ih,
    {
        rw plus_x_zero, 
        dunfold plus,
        refl,
    },
    {
        dunfold plus,
        rw ih,
        rw plus_x_succ_y, 
    }
end


-- yet another proof of the same theorem, with a more explicit "call" to lemma plus_x_succ_y :
theorem plus_commut_5: ∀ x y : ℕ, plus x y = plus y x 
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
        have h := plus_x_succ_y y z, 
        assumption,
    }
end



--------------------
-- GENERALIZATION
--------------------

/-
lemma discovery is not always so easy. if it was always easy (mechanical) then we could program computers to do it automatically. we shall see later that this is not possible in general. 

lemma discovery is often a creative process. for example, we sometimes need to discover a _generalized_ version of the theorem we are trying to prove. this is called "generalization" and it illustrates an amazing thing about proving theorems: that sometimes a _stronger_, (more general) result is easier to prove than its weaker (more specialized) version! how can this be? let's look at a couple of examples. 

consider the theorem below: 
-/

theorem app_L_3_times_failed: 
    ∀ L : list ℕ, app (app L L) L = app L (app L L) 
:= begin
  intro,
  induction L with x L2 ih,
  {
    refl,
  },
  {
    rw app,
    rw app,
    rw app,
    rw listeq,
    split,
    refl,
    -- stuck! the induction hypothesis doesn't help!!! the problem is that i have L2 everywhere... i should have some other lists for the 2nd and 3rd list, not L2 ... 
    sorry,
  }
end


/- solution: generalization! 

astonishingly, the _more general_ result is easier to prove!!! :
-/
theorem app_assoc: ∀ L1 L2 L3 : list ℕ, app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
    intros,
    induction L1 with x L4 ih,
    {
        refl,
    }    ,
    {
        rw app,
        rw ih,
        rw app,
        rw app,
    }
end

-- now the specialized result follows easily from the general result:
theorem app_L_3_times: ∀ L : list ℕ, app (app L L) L = app L (app L L) 
:= begin
  intro,
  rw app_assoc,
end


----------------------------------------------------
-- CHOOSING THE INDUCTION VARIABLE
----------------------------------------------------

-- let's revisit the proof of app_assoc:
#check app_assoc

/- one good question is why did we choose to induct on L1, rather than L2 or L3? this is part of the "art" of proving. there is no 100% deterministic recipe for choosing the right variable, just like there is no 100% guaranteed recipe for choosing the right tactic (if there were, we could program it and have a fully automated theorem prover, which is impossible in general -- we will see why later in this course). 

but a good rule of thumb is to choose to induct on the variable which "controls the recursion" of the corresponding function. in the case of app_assoc, L1 "controls the recursion" of the outer app on the left-hand side, and also of the inner one on the right-hand side. so it seems that L1 is a better choice than L2 or L3. 

but still, what if we chose L2 or L3 instead? we illustrate what would happen below:
-/

-- what if we inducted on L2?
theorem app_assoc_inductL2: ∀ L1 L2 L3 : list ℕ, app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
    intros,
    induction L2 with x L4 ih,
    {
        dunfold app,
        -- lemma discovery here! prove/use app_L_nil
        rw app_L_nil,
    },
    {
        dunfold app,
        try {rw ih,}, -- no can do 
        try {rw <- ih,}, -- no can do 
        -- we cannot use our induction hypothesis ... giving up ...
        sorry,
    },
end


-- what if we inducted on L3?
theorem app_assoc_inductL3: ∀ L1 L2 L3 : list ℕ, app L1 (app L2 L3) = app (app L1 L2) L3 
:= begin
    intros,
    induction L3 with x L4 ih,
    {
        -- lemma discovery here! prove/use app_L_nil
        rw app_L_nil,
        rw app_L_nil,
    },
    {
        try {rw ih,}, -- no can do 
        try {rw <- ih,}, -- no can do 
        -- we cannot use our induction hypothesis ... giving up ...
        sorry,
    },
end



---------------------------------
-- INDUCTION and HYPOTHESES 
---------------------------------

/-
when we use the induction tactic on some x : T, we implicitly have a predicate P on x in mind. what we are saying is "i will prove (∀ x : T, P x) by induction on x". note "induction x" does not specify P explicitly. this is a good thing because it makes our life easier: if we have to specify P explicitly, we would get heavier proofs (c.f. the proof of nat_induction → (∀ x : ℕ, plus x 0 = x) in 12-code.lean). instead of us specifying P explicitly, we let LEAN take care of it. 

on the other hand, we need to understand what P is, so that we don't find ourselves surprised by what LEAN generates, especially as induction hypotheses. we illustrate this by example, and then provide the general principle: 
-/

-- suppose we have to prove this:
theorem x_diff_x_plus_1: ∀ x : nat,  (x  ≠  plus x 1) 
:= begin
    intro,
    -- we can do induction directly on the ¬(x = plus x 1) claim: 
    induction x with y ih,
    -- what is our P here? it's ¬(x = plus x 1)  (which is the same as (x ≠ plus x 1))
    {
        dunfold plus,
        intro h,
        trivial,
    },
    {
        dunfold plus,
        intro h,
        rw succeq at h,
        trivial, -- skipping the modus ponens, which trivial does under the hood
    }
end


-- but what if we did _intro_ before _induction_?
theorem x_diff_x_plus_1_induct_after_intro: ∀ x : nat,  (x  ≠  plus x 1) 
:= begin
    intro,
    intro h,
    -- stop and think before you do induction: what is P in this case?
    -- P is ((x = plus x 1) → false), so the same as before!
    induction x with y ih,
    { -- base case: x = 0
        dunfold plus at h,
        trivial,
    },
    { -- induction step: x = nat.succ y
        /- NOTICE INDUCTION HYPOTHESIS ih! why is the induction hypothesis an implication, and not just "y = plus y 1" ? well, first of all let's agree that it would be wrong to have "y = plus y 1" be the induction hypothesis, since what we are trying to prove is "y ≠ plus y 1", which is the opposite! second, as we noted above, P is ((x = plus x 1) → false). LEAN recognizes that, and generates the correct induction hypothesis, which consists in replacing x with y in ((x = plus x 1) → false). 
        -/
        dunfold plus at h,
        rw succeq at h,
        have h2 := ih h,
        trivial,
    }
end


/- in general, if we have a bunch of hypotheses, say H1, H2, H3, and goal G, then what we are trying to prove is really H1 -> H2 -> H3 -> G (which is the same as (H1 ∧ H2 ∧ H3) → G). so our P is H1 -> H2 -> H3 -> G, and this is what serves as the basis for generating the induction hypothesis. 

note that some of these hypotheses Hi may refer to the variable x that we induct on, and some may not. the ones that refer to x become part of the induction hypotheses. the ones that don't, don't. 

the following example illustrates this:
-/

theorem induction_many_hypotheses_before_intros: 
    ∀ x y : ℕ, x > 0 → x > 1 → y > 0 → x > 6 → x > 5 
:= begin
    intros x y,
    induction x with z ih,
    {
        intro h1,
        intro h2,
        intro h3,
        sorry,
    },
    {
        intro h1,
        intro h2,
        intro h3,
        sorry,
    }
end


theorem induction_many_hypotheses_after_intros: 
    ∀ x y : ℕ, x > 0 → x > 1 → y > 0 → x > 6 → x > 5 
:= begin
    intros x y,
    intro h1,
    intro h2,
    intro h3,
    intro h4,
    induction x with z ih,
    {
        sorry,
    },
    {
        sorry,
    }
end



---------------------------------
-- INDUCTION practice!!!
---------------------------------


#check leq 
#check len 

/-
formalize and prove in LEAN the following statements:

    - for all x nat, x is leq than x+1 (use our plus)

    - for all lists of nats L, the len of L is leq the len of (x :: L), for any x nat 

-/

-- ANSWERS:

... 













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