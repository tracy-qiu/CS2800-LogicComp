-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 

----------------------------------------------------
-- INDUCTION
----------------------------------------------------

-- plus and mult on nats
#check plus -- imported 
#check mult -- imported


-- remember that we could easily prove this:
theorem plus_0_x: ∀ x : ℕ, plus 0 x = x := 
begin
    intros,
    dunfold plus,
    refl,
end

-- but we couldn't prove this, even though it looks just as trivial:
theorem plus_x_zero_1st_try: ∀ x : ℕ, plus x 0 = x :=
begin
    intros,
    try {refl},         -- nothing happens, as should be expected 
    try {unfold plus},  -- nothing happens, as should be expected 
    try {rw plus},      -- nothing happens, as should be expected 
    sorry
end


/-
the problem is the way plus is defined:

def plus : nat -> nat -> nat 
    | 0 y := y 
    | (nat.succ x) y := nat.succ (plus x y)

so, "plus 0 x" is easy to simplify based on the first case of the definition, but "plus x 0" is not.

now, we could say that plus x 0 = plus 0 x, by commutativity of addition. but we have not yet proved commutativity of addition! (this will also require induction!)

we also tried proof by cases:
-/
theorem plus_x_zero_2nd_try: ∀ x : ℕ, plus x 0 = x :=
begin
    intros,
    cases x with y, 
    { -- case x = 0
        refl,
    },
    { -- case x is of the form "nat.succ y" for some y
        unfold plus,
        -- let's get rid of the nat.succ's so that they don't bother us:
        rw succeq,  
        /- now what? we would still like to show that "plus y 0" equals y, but this is the same goal as showing plus x 0 = x ... !
        -/
        sorry,
    }
end

/-
the solution is a powerful tool called "induction". you have already seen mathematical induction on natural numbers, in your math courses. in this course, we will learn much more general and powerful induction methods.
-/

/-
let's start with recalling induction on nats. intuitively, induction says this:

1. suppose i want to prove that some property P(x) holds for any nat x.  

2. so, i have to prove that P(0) holds, and also that P(1) holds, and also that P(2) holds, and so on. 

3. let me start by proving that P(0) holds. this is the _base case_.

4. now let me prove that, for any nat n, _if P(n) holds then P(n+1) holds_. this is the _induction step_. and the part _P(n) holds_ is the _induction hypothesis_.

5. if i manage to prove both the base case and the induction step, then i claim that P(x) indeed holds for _any_ nat x. why? well, because i have proven the induction step _for any n_. let me instantiate the induction step with n := 0. then i get:
    _if P(0) holds then P(0+1) holds_, i.e., _if P(0) holds then P(1) holds_
but i know that P(0) holds because i have proven the base case. so i can apply modus ponens and i get that P(1) holds too! now i go on, and instantiate the induction step with n := 1. then i get:
    _if P(1) holds then P(2) holds_
but i know that P(1) holds. so i apply modus ponens and i get that P(2) holds too. i can continue this way for as long as necessary, to prove P(x) for any x. if x is very very large, say 100000000000000, then i have to do many instantiations and modus ponens, but i don't really have to do them. i just know that they can be done! so i can conclude that P(x) indeed holds for any nat x. 

in fact, we can express the induction principle for natural numbers in LEAN, as follows:
-/

def nat_induction := ∀ P : ℕ → Prop, -- for any property P of nats 
    (P 0) → -- if the base case holds 
    (∀ n : ℕ, (P n) → (P (nat.succ n))) → -- and if the induction step also holds
    (∀ n : ℕ, P n)  -- then P holds for all nats! 


/- we can use nat_induction to prove stuff, as in the example below. 

NOTE: if the proof that follows is unreadable to you, don't worry! we will NOT do proofs by induction like this! we will use the induction tactic instead. the example that follows is only meant to illustrate how we COULD use the induction axiom to prove stuff. 
-/

example: nat_induction → (∀ x : ℕ, plus x 0 = x)
:= begin
    intro h1,
    dunfold nat_induction at h1,
    have h2 := h1 (λ x : ℕ, plus x 0 = x),
    have fun1 : ((λ (x : ℕ), plus x 0 = x) 0) = (plus 0 0 = 0) := begin refl, end,
    rw fun1 at h2,
    have h3 : plus 0 0 = 0 := begin
        refl,
    end,
    have h4 := h2 h3,
    have h5 : (∀ (n : ℕ), (λ (x : ℕ), plus x 0 = x) n → (λ (x : ℕ), plus x 0 = x) (nat.succ n)) := begin
        intro,
        intro g1,
        dunfold plus,
        rw g1,
    end,
    have h6 := h4 h5,
    assumption,
end


-- in class approach 
example: nat_induction → (∀ x : ℕ, plus x 0 = x)
:= begin
    intro h1,
    dunfold nat_induction at h1,
    have h2 := h1 (λ x : ℕ, plus x 0 = x),
    have fun1 : ((λ (x : ℕ), plus x 0 = x) 0) := begin refl, end,
    have h3 := h2 fun1, 
    have h5 : (∀ (n : ℕ), (λ (x : ℕ), plus x 0 = x) n → (λ (x : ℕ), plus x 0 = x) (nat.succ n)) := begin
        intro,
        intro g1,
        dunfold plus,
        rw g1,
    end,
    have h6 := h3 h5,
    assumption,
end

/-
but the above is too complicated, in many ways. 

first, we have to add nat_induction as a hypothesis to every theorem that we want to prove about nats! this would be easy to fix. we could simply define nat_induction as an axiom (like with classical.em). 

second, and more importantly, the proof itself is complex. we have to instantiate nat_induction with the predicate we want to talk about, and there are all these λ's in our proof, and long formulas! can we simplify all that? yes! luckily, LEAN provides us with a built-in tactic to do induction:
-/

----------------------------------------------------
-- the _induction_ tactic 
----------------------------------------------------

-- let's prove the above theorem using the _induction_ tactic:
theorem plus_x_zero: ∀ x : ℕ, plus x 0 = x 
:= begin
    intros,
    induction x, -- LEAN automatically generates two goals
    { -- base case: x = 0
        /- the base case goal is generated by replacing x (the variable we induct on) by the base case constructor 0 (nat.zero)-/
        refl,
    },
    { -- induction step: x = nat.succ x_n
        /- the induction step goal is generated by replacing x (the variable we induct on) by the recursive case construction (nat.succ x_n). the inductive hypothesis is generated by replacing x by the "smaller nat" x_n. -/
        unfold plus,
        rewrite x_ih, -- x_ih is the "induction hypothesis"
    }
end



-- LEAN automatically chooses names such as x_n, x_ih, etc. if we don't like them, we can change them:
theorem plus_x_zero_alt_names: ∀ x : ℕ, plus x 0 = x 
:= begin
    intros,
    induction x with y ih, -- the "smaller" nat is now called "y" and the induction hypothesis is now called "ih"
    { -- base case: x = 0
        refl,
    },
    { -- induction step: x = nat.succ y
        unfold plus,
        rewrite ih, 
    }
end

/- at this point you should stop and compare: (1) the failed proof attempt by cases, and (2) the successful proof by induction. where do the two differ? only in one thing: in the proof by induction, in the case x = nat.succ y, we have an extra hypothesis, the induction hypothesis ih, which we don't have in the proof by cases. it's the induction hypothesis which allows us to "make the jump to infinity"! 

see also:
https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html
-/



/- with induction, we have lift off. we can now pretty much prove everything that can be proven, and fly to the stars!

let's exercise this new power of ours and do more proofs by induction:
-/

theorem mult_x_zero: ∀ x : ℕ, mult x 0 = 0 
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

theorem mult_x_one: ∀ x : ℕ, mult x 1 = x 
:= begin
    intros,
    induction x,
    {
        refl,
    },
    {
        unfold mult,
        rw x_ih,
        dunfold plus,
        refl,
    }
end



----------------------------------------------------
-- INDUCTION ON LISTS 
----------------------------------------------------

/- the induction proofs we have done so far might not look very impressive. after all, we already saw induction on natural numbers at school. but our induction principle is more general, and it applies not just to nats, but also to any other inductive data type. for instance, we can do induction on lists.
-/


-- length of a list:
#check len -- imported 

-- concatenate two lists:
#check app -- imported

-- now let's prove some things about app. as you will notice, some of the theorems below seem reminiscent of some theorems about functions like plus!

-- just like we can prove plus 0 x = x, we can also prove app [] L = L without induction:
theorem nil_app: ∀ L : list nat, app [] L = L 
:= begin
    intros,
    dunfold app,
    refl,
end

-- but for app L [] = L, we need induction, just like we need induction for plus x 0 = x:
theorem app_nil: ∀ L : list ℕ, app L [] = L 
:= begin
    intro,
    induction L with x L2 ih,
    { -- base case: L = list.nil = [] 
        /- the base case goal is generated by replacing _L_ (the variable we induct on) by the base case constructor [] (list.nil). -/
        refl,
    },
    { -- induction step: L = list.cons x L2 = (x :: L2) 
        /- the induction step goal is generated by replacing _L_ (the variable we induct on) by the recursive case data construction _list.cons x L2_ . the inductive hypothesis is generated by replacing _L_ by the "smaller list" _L2_. -/
        unfold app,
        rewrite ih,
    }
end



----------------------------------------------------
-- PROOF BY INDUCTION vs PROOF BY CASES 
----------------------------------------------------

/- induction applies to any inductive data type. we have already seen it apply to nats and lists. what if we try induction on a simple enumerative data type like _weekday_? in that case, proof by induction trivially becomes proof by cases, since _weekday_ is not a recursive data type. so the induction proof only contains _base cases_:
-/

#check weekday -- imported 
#check next_workday -- imported 

open weekday 

theorem next_workday_not_saturday: ∀ d : weekday, next_workday d ≠ saturday 
:= begin
    intro,
    induction d, -- here has same effect as _cases d_
    -- all the cases are _base cases_ because the data type is a simple enumerative type:
    repeat {
        intro,
        trivial,
    } 
end

