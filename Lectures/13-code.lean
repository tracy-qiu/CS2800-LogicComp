-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 

--------------------------------
-- INDUCTION continued
--------------------------------



--------------------------------------------
-- INDUCTION is ONLY for INDUCTIVE TYPES!
--------------------------------------------

-- just like we cannot do cases on Props, we CANNOT do induction on non-inductive types, like Prop: 

example: ∀ p : Prop, true 
:= begin
    intro,
    induction p, -- error: "inductive datatype expected"!
end


-----------------------------------------------
-- INDUCTION on ARBITRARY INDUCTIVE TYPES
-----------------------------------------------

/- what does induction on an arbitrary inductive type T look like?

the principle is: 
    - we can assume that what we are trying to prove holds for "smaller" elements of T 
    - we prove that it holds for "bigger" elements of T 
where "bigger" means "constructed from the smaller using T's constructors". 

in particular, suppose that x : T (i.e., x is of type T) and that T has k constructors.

then, "induction x" will generate k subgoals, one for each constructor. these subgoals are also called _proof obligations_. 

suppose constructor i is as follows: 

    | foo : T → T → T → ℕ → bool → T 

meaning that foo consumes 3 elements of type T, one nat, and one bool, and produces a new element of type T. 

then the i-th proof obligation of the induction will look like this:

    - assume that the goal holds for some x1 of type T (induction hypothesis 1)
    - assume that the goal holds for some x2 of type T (induction hypothesis 2)
    - assume that the goal holds for some x3 of type T (induction hypothesis 3)
    - prove that the goal holds for (foo x1 x2 x3 n b), for all n : ℕ, and all b : bool. 

let us look at examples of this below: 
-/



--------------------------------------------------------
-- MULTIPLE BASE CASES AND MULTIPLE INDUCTION STEPS 
--------------------------------------------------------

/- just like in a proof by cases we can have multiple cases/subgoals to prove, in a proof by induction, we might have multiple base cases and multiple induction steps. suppose we have a data type with two base cases and two inductive cases:
-/

inductive type3 : Type 
    | bla : type3                           -- 1st base case
    | blu : nat -> type3                    -- 2nd base case
    | foo : nat -> type3 -> type3           -- 1st inductive case
    | bar : bool -> type3 -> type3          -- 2nd inductive case
    | bor : nat -> type3 -> bool -> type3   -- 3rd inductive case

/- what does induction on an element of type3 look like? well, we would have to prove 5 cases, corresponding to the 5 constructors: _bla_, _blu_, _foo_, _bar_ and _bor_. _bla_ and _blu_ are both base cases because their constructors do not take another element of type3 as input, but _foo_, _bar_ and _bor_ are inductive cases. so in this case, we expect to have _two_ base cases and _three_ induction steps! indeed:
-/



variable f1 : type3 -> type3 
variable f2 : type3 -> type3 

-- never mind whether the theorem below holds or not, it's just for illustration:
theorem illustration_many_induction_steps: 
    ∀ t : type3, f1 t = f2 t 
:= begin
    intro,
    induction t with x y t1 ih1 b t2 ih2 z t3 c ih3, -- generates 5 subgoals
    { -- base case: t = type3.bla 
        sorry,
    },
    { -- 2nd base case: t = type3.blu x, for some x : ℕ 
        sorry,
    },
    { -- induction step: t = type3.foo y t1, for some y : ℕ and some t1 : type3
        sorry,
    },
    { -- induction step: t = type3.bar b t2, for some b : bool and some t2 : type3
        sorry,
    },
    { -- induction step: t = type3.bor z t3 c, for some z : ℕ and some t3 : type3 and some c : bool  
        sorry,
    }
end





--------------------------------------------------------
-- MULTIPLE INDUCTION HYPOTHESES -- INDUCTION ON TREES
--------------------------------------------------------

/- so far we have talked about the "smaller" element that some element x that we induct on is replaced with in the induction hypothesis. for example, if x is a nat, and x = nat.succ y, then the "smaller" element is y. if x is a list of nats, and x = (a :: L), then the "smaller" element is the list L. if x is a type3, and x = type3.foo z t1, then the "smaller" element is t1. etc. 

but what if x is a tree? recall the type bton: 
-/

inductive bton : Type 
  | leaf : nat -> bton 
  | node : bton -> bton -> bton 


/- what would induction on an element of type bton look like? if t is of type bton, what would be the "smaller" element? to answer this question, we first note that bton has two constructors, so we must consider two cases:

    1. "leaf" is a base case, since constructor _leaf_ doesn't take as input another bton. 

    2. "node" is an inductive case, because constructor _node_ takes as input another bton. in fact, _node_ takes as input _two_ btons. 

because constructor _node_ takes as input two btons, there are _two_ smaller elements. intuitively, each subtree of a binary tree is a "smaller" tree. 

the beauty of induction is that it allows us to assume an induction hypothesis for _every_ "smaller" element. if there's just one smaller element, we have just one induction hypothesis. but if there's more, we have more than one induction hypotheses. in the case of bton, we expect to have _two_ induction hypotheses, one for each subtree. 

let us see this:
-/

-- recall this function:
def bton2natlist: bton -> list nat 
  | (bton.leaf x) := [x] 
  | (bton.node t1 t2) := app (bton2natlist t2) (bton2natlist t1) 


-- this is a simple example that we can prove without induction:
theorem easytree: ∀ x y : ℕ, 
    bton2natlist (bton.node (bton.leaf x) (bton.leaf y)) = [y,x] 
:= begin
    intros,
    unfold bton2natlist,
    refl,
end

/- now let's look at some theorems which need induction. 

(we will not actually prove these, because we don't know how to reason about LEAN's > relation. but we can see how the induction tactic works on the bton data type.)
-/

theorem inducttree: ∀ t : bton, 
    len (bton2natlist t) > 0 
:= begin
    intro,
    induction t with x t1 t2 ih1 ih2,  
    sorry,
    sorry 
end


theorem inducttree2: ∀ t1 t2 : bton, 
    len (bton2natlist (bton.node t1 t2)) > 0 
:= begin
    intros,
    induction t1 with x t3 t4 ih1 ih2, 
    {
        unfold bton2natlist,
        sorry,  
    },
    { -- the induction step has two induction hypotheses:
        -- ih1: assume that the result holds for the left subtree t3
        -- ih2: assume that the result holds for the right subtree t4
        -- goal: prove that the result holds for the parent tree (bton.node t3 t4) 
        unfold bton2natlist,
        sorry,  
    }
end



-- here's another data type whose last constructor "bor" generates multiple induction hypotheses:
inductive type4 : Type 
    | bla : type4   
    | blu : nat -> type4   
    | foo : nat -> type4 -> type4       
    | bar : bool -> type4 -> type4      
    | bor : nat -> type4 -> bool -> type4 -> type4 

/- the difference with type3 is constructor bor:

    | bor : nat -> type3 -> bool -> type3   

type3.bor takes only one element of type3. type4.bor takes two elements of type4. therefore, when we are trying to prove something by induction on type4, we shoule expect the 5th subgoal (3rd induction step) to have _two_ induction hypotheses:
-/

variable g1 : type4 -> type4 
variable g2 : type4 -> type4 

theorem many_induction_steps_many_induction_hypotheses: 
    ∀ t : type4, g1 t = g2 t 
:= begin
    intro,
    induction t with x y t1 ih1 b t2 ih2 z t3 c t4 ih3 ih4,
    { -- base case: t = type4.bla 
        sorry,
    },
    { -- base case: t = type4.blu x for some x : ℕ 
        sorry,
    },
    { -- induction step: t = type4.foo y t1, for some y : ℕ and some t1 : type4 
        -- ih1: assume that the result holds for t1
        -- goal: prove that the result holds for type4.foo y t1
        sorry,
    },
    { -- induction step: t = type4.bar b t2, for some b : bool and some t2 : type4
        -- ih2: assume that the result holds for t2
        -- goal: prove that the result holds for type4.bar b t2
        sorry,
    },
    { -- induction step: t = type4.bor z t3 c t4, for some z : ℕ and some t3 : type4 and some c : bool and some t4 : type4
        -- ih3: assume that the result holds for t3
        -- ih4: assume that the result holds for t4
        -- goal: prove that the result holds for type4.bor z t3 c t4 
        sorry,
    },
end


/- IMPORTANT: LEARN TO GENERATE THE INDUCTION PROOF OBLIGATIONS BY HAND!

you will be asked in quizzes, homeworks, exam, etc, things like "how many proof obligations does this induction generate and which ones?". 
-/



/-
induction is a powerful tool. we are not done with induction. we will learn how to "smell" which induction scheme to use (we will see what that means), which variable to induct on, and other tricks. we will also learn something called "functional induction". but before that, we must address one important topic: lemmas and lemma discovery. 
-/

