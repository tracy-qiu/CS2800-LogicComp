-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- so that we don't have to define some functions that we use constantly every time, we put them in a separate file that we can "import" here: 
import .ourlibrary06 

-- control-clicking on the names of functions below, vscode takes you to the file ourlibrary06.lean where they are defined
#check plus
#check len 


---------------------------------------------------
-- PROVING FORALL SPECIFICATIONS continued
---------------------------------------------------

-- last time we managed to prove some interesting things:
theorem plus_0_x_equals_x: forall x : nat, plus 0 x = x 
:= begin
  intro,
  dunfold plus, 
  refl,
end

theorem len_list_of_one: forall x : nat, len [x] = 1
:= begin
  intro,
  dunfold len,
  refl, 
end


/-
but our proving skills seem limited. for example, we cannot prove this!
-/

theorem plus_x_0_equals_x: forall x : nat, plus x 0 = x :=
begin
    intro,
    try {refl}, -- it doesn't work! 
    /- but why? why is refl able to prove "plus 0 x = x" but not able to prove "plus x 0 = x" ?
    the reason lies in the definition of the function plus. recall how plus is defined:
    
    def plus : nat -> nat -> nat  
    | nat.zero y := y 
    | (nat.succ x) y := nat.succ (plus x y)

    and recall that nat.zero is the same as 0. therefore, "plus 0 x" matches the first case of the definition of plus (by matching y with x), and refl can simplify it to just "x". then the equality becomes "x = x" and refl concludes the proof. 

    but "plus x 0" does _not_ match the first case of the definition of function plus. and it does not match the second case either. so refl cannot simplify anything in this case, and gives up. 

    we can also see this better if we try to apply dunfold:
    -/
    try {dunfold plus}, -- nothing happens, dunfold cannot simplify 
    sorry,
end

-- what about this?
theorem plus_commutative: ∀ (x y : nat), plus x y = plus y x :=
begin
    intro,
    intro,
  -- x : ℕ     hypothesis 1 
  -- y : ℕ     hypothesis 2 
  -- ⊢ ... goal ... 
    try {refl}, -- merde, alors!
    sorry,
end

-- what about this?
theorem plus_associative: ∀ (x y z : nat), plus (plus x y) z = plus x (plus y z) :=
begin
    intro,
    intro,
    intro,
    try {refl}, -- !@#$%$#!@#
    sorry,
end

/- it looks like we are not strong enough magicians yet to complete these proofs. we simply don't know enough tactics. as Master Yoda would put it: "much to learn you still have my young apprentice"! not to worry. by the end of the course such proofs will be a piece of cake for us. 

let's continue learning more tactics and more proof methods right away then! 
-/



----------------------------------------------------
-- intros
----------------------------------------------------

-- the _intros_ tactic applies the _intro_ tactic repeatedly:

theorem plus_commutative_w_intros: ∀ (x y : nat), plus x y = plus y x :=
begin
    intros,
    sorry,
end

theorem plus_associative_w_intros: ∀ (x y z : nat), plus (plus x y) z = plus x (plus y z) :=
begin
    intros,
    sorry,
end

-- intros also works if there's only one intro to do:
theorem plus_0_x_equals_x_w_intros: forall x : nat, plus 0 x = x :=
begin
    intros,
    refl,
end





--------------------------------------------------------
-- PROOF BY SIMPLIFICATION (a.k.a. EQUATIONAL REASONING)
--------------------------------------------------------

/-
very often our goal is of the form A = B, but we know that we can reduce it to B = B, or A = A, or even C = C, by 'simplifying' A or B (or both). in the Software Foundations series, this is called "proof by simplification":
https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab34
(for those of you who have taken a previous version of CS2800 with ACL2s, there it was called "equational reasoning"). 

we have already implicitly done proof by simplification. ("simplification", "reduction", "equational reasoning", "unfolding", ... are taken to be synonyms in this course.)
recall:
-/

-- we proved this already above:
example: forall x : nat, len [x] = 1
:= begin
  intro,
  -- goal is A = B, but A can be simplified with dunfold:
  dunfold len,
  refl, 
end

-- notice what happens if we wrote len slightly differently:
def len1plus : list nat -> nat 
  | [] := 0 
  | (_ :: L) := 1 + (len1plus L)
--

example: forall x : nat, len1plus [x] = 1
:= begin
  intro,
  -- goal is A = B, but A can be simplified with dunfold:
  dunfold len1plus, -- great, we got rid of len1plus, but the goal is stil not 1 = 1, why? because _dunfold len1plus_ only unfolds _len1plus_, not +
  -- goal is C = D, but refl can discharge it:
  refl, 
end


/-
LEAN tactics can sometimes exhibit surprising (and weird) behavior. for example:
-/

-- this is the standard way to define append on lists:
def app: list ℕ -> list ℕ -> list ℕ
  | [] L := L 
  | (x :: L1) L2 := list.cons x (app L1 L2)
--

-- everything seems fine with the above definition:
example: app [] [] = []
:= begin
  dunfold app,
  refl,
end

example: app [1, 2, 3] [4, 5, 6] = [1,2,3,4,5,6]
:= begin
  dunfold app,
  refl,
end

-- but let's suppose we defined append like this instead:
def appred: list ℕ -> list ℕ -> list ℕ
  | [] [] := []
  | [] (y :: L) := list.cons y (appred [] L)
  | (x :: L1) L2 := list.cons x (appred L1 L2)

-- there is nothing wrong with the above definition (the cases are non-overlapping) and it seems to work correctly:
#reduce appred [1, 2, 3] [4, 5, 6] 

-- and yet dunfold doesn't work!
example: appred [1, 2, 3] [4, 5, 6] = [1,2,3,4,5,6] 
:= begin
  try { dunfold appred, },
  refl, -- luckily refl works 
end 

-- in fact it's even more embarrassing! 
example: appred [] [] = [] 
:= begin
  try { dunfold appred, },
  refl, -- luckily refl works 
end

-- i have no idea why this happens! LEAN mystery ... 



----------------------------------------------------
-- rewrite, rw
----------------------------------------------------

/-
luckily, we don't have to rely on dunfold to do our simplifications, and we don't have to rely on refl either to do them "under the hood". we can use the _rewrite_ tactic instead, abbreviated _rw_. 
-/

example: appred [] [] = [] 
:= begin
  rewrite appred, -- does also the refl part ... 
end

example: appred [1, 2, 3] [4, 5, 6] = [1,2,3,4,5,6] 
:= begin
  rewrite appred,
  rewrite appred,
  rw appred, -- rw is abbreviation for rewrite 
  rw appred,
  rw appred,
  rw appred, -- it's long, but you can think of it as step-by-step debugging!
  rw appred,
end 



/- 
in this course, you can use _any_ of these tactics (unfold, refl, rw) to discharge goals of the form A = B. we will not penalize you for using one vs the other, unless we explicitly ask you to use a particular one for training purposes. 

we will also not insist on manual equational reasoning in this course, since it is something that theorem provers can help us with pretty well, so that we don't have to do it "by hand". but we need to know what it is, because in principle we should be able to do everything by hand, even if we didn't have LEAN! indeed, LEAN is just a proof _assistant_ which makes our lives easier so that we don't have to write stuff down, remember all the goals that we have to prove, do the simple reductions, etc. but in principle we could do all these things ourselves with paper and pencil. it would just be tedious. to see this, let's do a few examples:
-/

/- reducing the expression "len []":

len []
= by definition of len, 1st case
0
-/

/- reducing the expression "len [1]":

len [1] 
= by definition of notation "[1]"
len (1 :: [])
= by definition of len, 2nd case
1 + (len [])
= by definition of len, 1st case
1 + 0
= "arithmetic"  (this is actually a bit misleading, because "arithmetic" already hides a lot of stuff! e.g., how is + defined?) 
1
-/

/- reducing the expression "len [x]":

len [x] 
= by definition of notation [x] 
len (x :: [])   -- or len (list.cons x [])   or len (list.cons x list.nil) 
= by definition of len, 2nd case
1 + len [] 
= by definition of len, 1st case
1 + 0
= by arithmetic
1

-/

-- you can think of #reduce as performing the above reductions. you can think of #eval as a more efficient #reduce (never mind how it's implemented):


def exponent : ℕ → ℕ → ℕ  
    | _ nat.zero  := 1
    | x (nat.succ n) := x * (exponent x n) 

-- #reduce exponent 2 15  -- out of time/memory
#eval exponent 2 1000 -- ok 





---------------------------------
-- PROOF BY CASES 
---------------------------------

def negb : bool → bool
    | tt := ff 
    | ff := tt 
--

-- how can we prove this?
example: ∀ x : bool, negb (negb x) = x 
:= begin
  intro,
  try {rw negb}, -- make sure you understand why this does nothing!
  try {refl}, -- does nothing!  why?
  sorry,
end

/- we can make progress if we "reason by cases": since x is a bool, by definition of the inductive data type bool, either x = bool.ff, or x = bool.tt. then we can try to see if we can finish the proof in each of these two cases. to generate these two cases, we use the _cases_ tactic:
-/

----------------------------------------------------
-- cases
----------------------------------------------------

theorem negb_involutive : ∀ x : bool, negb (negb x) = x 
:= begin
  intro,
  cases x, -- generates two cases, so we now have 2 proof subgoals. these are also called _proof obligations_
  { -- we begin the first subgoal
    refl,
  }, -- first subgoal done!
  { -- we begin the second subgoal
    refl,
  } -- second subgoal done! proof complete!
end

/-
cases applies to any inductive data type, e.g., nat: 
-/

def silly (x : nat) : nat := if (x = 0) then 0 else 0 

theorem silly_is_silly: ∀ x : ℕ, silly x = 0
:= begin
  intro,
  try {refl,}, 
  cases x with y, -- remove "with y" to see what happens!
  {
    refl,
  },
  {
    refl,
  }
end


--------------------------------------------
-- when a tactic _applies_ to a proof state
--------------------------------------------

/-
we will say that a tactic _applies_ to a certain proof state if we can issue that tactic successfully at that proof state, i.e., without a LEAN error. for example:
-/

lemma silly_of_nonzero_is_0: ∀ x : nat, silly (nat.succ x) = 0 
:= begin
    -- the refl tactic does not apply here:
    -- refl, -- if we try it we get an error 
    -- "cases x"  does not apply here either:
    -- cases x, -- if we try it we get an error
    -- the intro tactic applies here:
    intro,
    -- intro does not apply here:
    -- intro, -- if we try it we get an error 
    -- "cases x" applies here:
    -- cases x, -- OK! 
    -- "dunfold silly" also applies here:
    -- dunfold silly, -- OK!
    -- refl also applies here (and in fact finishes the proof):
    refl,
end

/-
when we say that a tactic _applies_ we do NOT necessarily mean that it's the right thing to do. we do NOT necessarily mean that by applying this tactic we will make progress towards proving our goal. all we are saying is that it is OK to issue this tactic in that particular proof state, and the tactic will do something in that proof state. whether this is a good idea or not is a whole different story. in fact, there are cases where the goal may not be provable at all, because it's wrong! still, some tactics apply, until we reach a deadlock. sometimes, no matter what we do, we reach a deadlock, because there's no way to complete the proof, because what we are trying to prove is wrong, for example. at other times, we may take a wrong direction, and reach a deadlock. then we have to go back at an earlier point in the proof, and try another path, and we may succeed. 

here's an example of a wrong claim, but where a tactic still applies:
-/

example: ∀ x : nat, x = 0 := begin
    -- the intro tactic applies here:
    intro,
    cases x,
    {
      refl,
    },
    {
      cases x,
      {
        sorry,
      },
      {
        sorry,
      }
    }
    -- but now what? obviously i cannot make progress
end

/-
we will later see examples of claims which are true and provable, but where if we issue the wrong tactic we will reach a deadlock and not be able to prove them!
-/




--------------------------------------
-- are "try" and "sorry" tactics?
--------------------------------------

/-
let's not consider "try" and "sorry" to be tactics. sorry always "applies" to any proof state, and "aborts" trying to prove the corresponding goal. try also always "succeeds" in the sense that if the attempted tactic(s) fail(s) then "trying" them simply does nothing. 
-/


/-
      NESTED CASES
-/

def andb : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff tt := ff
    | ff ff := ff
--

-- we can have cases within cases:
theorem andb_commutative : ∀ x y : bool, andb x y = andb y x 
:= begin
    intros,
    try {refl}, -- does nothing 
    cases x,
    {
        try {refl}, -- does nothing
        cases y,
        {
            refl,
        },
        {
            refl,
        }
    },
    {
        cases y,
        {
            refl,
        },
        {
            refl,
        }
    }
end

-- this short hand is ok too, more messy but if understandable it is fine  
example: ∀ x y : bool, andb x y = andb y x 
:= begin 
  intros, 
  cases x, 
  cases y, 
  refl, 
  refl, 
  cases y, 
  refl, 
  refl, 
end

theorem plus_x_0_equals_x_by_cases': forall x : nat, plus x 0 = x :=
begin
    intro,
    cases x with y, -- the "with y" renames the variable "x" to "y" in the 2nd case
    {
        refl, -- this was easy!
    },
    { 
      rw plus,
      cases y with z, 
      {
        refl, 
      } 
      {
        rw plus, -- cant solve this prood without induction
        sorry, 
      }
    }
end


-- perhaps we can now prove this using proof by cases?
theorem plus_x_0_equals_x_by_cases: forall x : nat, plus x 0 = x :=
begin
    intro,
    cases x with y, -- the "with y" renames the variable "x" to "y" in the 2nd case
    {
        refl, -- this was easy!
    },
    { -- but wait, there's one more case ... 
        try {refl}, -- does nothing  
        dunfold plus,
        try {refl}, -- does nothing
        -- perhaps more cases?
        cases y,
        {
            refl, -- phew ... 
        },
        { -- but wait, there's still one more case ... 
            dunfold plus,
            try {refl}, -- nothing
            -- i can keep generating cases, but i will never finish! why?
            -- i give up ...
            sorry,
        },
    },
end




--------------------------------------------------------------
-- MORE SPECIFICATIONS, INTRO TO LOGIC, LOGICAL CONNECTIVES
--------------------------------------------------------------

/- so far our specifications have been pretty simple: either examples/tests, or simple forall specifications of the form "∀ (x y ...), f1 x y ... = f2 x y ...". 

let's write some more sophisticated specifications. we won't be able to prove those yet, but we should get use to be able to write more complicated logic statements. in the process, we introduce the basic logic connectives: implication, conjunction, disjunction, negation, and so on. 
-/

-- recall our weekday example (it's in ourlibrary06.lean):
#check weekday
#check next_workday
open weekday

/- remember the property that we stated about this function? "for any weekday d, (next_workday d) is never a saturday nor a sunday". how can we express this? there is actually several different ways to write this formally:
-/

-- these two are identical:
#check ∀ d : weekday, not (next_workday d = saturday) 
#check ∀ d : weekday, ¬ (next_workday d = saturday) 

-- A ≠ B ("A not equals B", or "A different from B") is actually the same as ¬ (A = B), as we shall see later
#check ∀ d : weekday, next_workday d ≠ saturday

#check ∀ d : weekday, next_workday d ≠ sunday


--------------------------
-- NEGATION: not ¬ 
--------------------------


#check not 
#check not (1 = 2) 
#check ¬ (1 = 2) 
#check 1 ≠ 2    -- same as ¬(1 = 2), we'll see why later 

theorem next_workday_not_saturday: 
  ∀ d : weekday, next_workday d ≠ saturday 
:= begin
  intro,
  try {refl},
  cases d,
  {
    try {refl}, -- nothing
    dunfold next_workday,
    try {refl}, -- still nothing
    sorry, -- we don't know how to handle negation yet!
  },
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
end

theorem next_workday_not_saturday': 
  ∀ d : weekday, next_workday d ≠ saturday 
:= begin
  intro,
  try {refl},
  cases d,
  repeat {
    sorry,
  },
end

theorem nxtwkdaynotsaturday: 
  ∀ d : weekday, not (next_workday d = saturday) 
:= begin
    intro,
    sorry,
    /-
    cases d,
    {
        dunfold next_workday,
        try {refl,}, -- doesn't apply here
        sorry,
    },
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    -/
end


-- notice that the "not" above is _not_ the same as the boolean negation:
#check not  -- this works on Props
#check bnot -- this works on bools (same as our negb!)
#eval bnot tt 
#eval bnot ff 

#check not tt  -- COERCIONS! TO BE AVOIDED AT ALL COSTS!



------------------------------
-- CONJUNCTION: and, ∧ , /\ 
------------------------------
/- above, we wrote two separate theorems for our property that (next_workday d) never falls on the weekend. what if we wanted to combine the two? we can use _conjunction_ (logical _AND_). 
-/

#check and 
#check ∀ d : weekday, and (next_workday d ≠ saturday) (next_workday d ≠ sunday)

-- infix notation for conjunction: ∧ or /\ 
#check ∀ d : weekday,  (next_workday d ≠ sunday)    ∧    (next_workday d ≠ saturday) 
#check ∀ d : weekday,  (next_workday d ≠ sunday)   /\   (next_workday d ≠ saturday) 

-- parentheses can be dropped in this case:
#check ∀ d : weekday, next_workday d ≠ saturday ∧ next_workday d ≠ sunday



theorem next_workday_not_weekend: 
    ∀ d : weekday, next_workday d ≠ saturday ∧ next_workday d ≠ sunday 
:= begin
    intro,
    -- cases d,
    sorry,
end



-- mini-quiz: can you think of another way to write the same spec?
/- there is another way, and that's to just list all possible days of the week, except the weekend: "the next workday is either a monday, or a tuesday, or a wed...". but how do we say "or"? we use _disjunction_ (logical _OR_). 
-/

-----------------------------
-- DISJUNCTION: or, ∨, \/ 
-----------------------------

#check or 

#check ∀ d : weekday, or (next_workday d = monday) (next_workday d = tuesday) 

-- infix notation for disjunction: ∨ or \/
#check ∀ d : weekday, (next_workday d = monday) ∨ (next_workday d = tuesday)
#check ∀ d : weekday, (next_workday d = monday) \/ (next_workday d = tuesday)

-- parentheses can be dropped in this case:
#check ∀ d : weekday, next_workday d = monday ∨ next_workday d = tuesday

-- the joys of infix notations:
#check ∀ d : weekday, next_workday d = monday ∨ 
                      next_workday d = tuesday ∨ 
                      next_workday d = wednesday ∨ next_workday d = thursday ∨ 
                      next_workday d = friday


theorem next_workday_is_a_5day_weekday: ∀ d : weekday, 
    next_workday d = monday ∨ 
    next_workday d = tuesday ∨ 
    next_workday d = wednesday ∨ 
    next_workday d = thursday ∨ 
    next_workday d = friday 
:= begin
    intro,
    sorry,
end


--------------------------------
-- IMPLICATION: implies, ->, → 
--------------------------------

#check implies 

#check ∀ x : nat, implies (x = 0) (not (x=1)) 
#check ∀ x : nat, x = 0 → ¬ x=1 
#check ∀ x : nat, x = 0 → x ≠ 1

#eval 4/2 
#eval 4/3 
#eval 3/4 
#eval 2/0 -- a nat divided by 0 yields 0. let's say we don't like that. 

-- we define our own function which returns -1 when a division by 0 is attempted:
def mydivide (x y : int) : int := if (y = 0) then -1 else x/y 
#check mydivide 

#eval mydivide 2 0 

-- now we want to state the property that mydivide behaves like "/", provided that the denominator (2nd argument) is not zero. how to write that? we use logical _implication_. as it turns out (and for good reasons, which we will discuss later) the implication symbol is the same "right arrow" -> or → as the one we say for functions:

#check ∀ x y : int, (y ≠ 0) -> (mydivide x y = x/y)

#check implies 

#check ∀ x y : int, implies (y ≠ 0) (mydivide x y = x/y)   
--                             A               B 
--                   A          implies        B
--                        A -> B
--                        A → B


#check ite  -- this is the "if then else" function, which is different from implies !
#check implies 

/- ENGLISH AND IMPLICATION

"A only if B"    =     A -> B
"B if A"         =     A -> B
"A if B"         =     B -> A
"if A then B"    =     A -> B

"A if and only if B"    =   A <-> B  =  A -> B and B -> A 

-/

--------------------------------
-- intro with implication
--------------------------------

theorem mydivide_divide: 
  ∀ x y : int, y ≠ 0 → mydivide x y = x/y 
:= begin
    intro,
    intro,
    intro, -- WORKS FOR IMPLICATION TOO!
    try {refl},
    sorry,
end
/- as can be seen in the incomplete proof above, the intro tactic also transforms a goal of the form A → B into the goal B, while moving A into the list of hypotheses. this shouldn't shock us. how would we prove A → B by paper and pencil? we would say something like: "Assume A is true. Let us then prove B." that's exactly what intro does. the "Assume A is true" part is moving A into the hypotheses. the "Let's then prove B" part is the new goal B. 

you will also notice in the example above that A was not just moved into the hypotheses, but it was also given a "label". indeed, the hypotheses now include

a : y ≠ 0

and not just "y ≠ 0". why is that? for now, think of "a" as simply a label which allows us to refer to the hypothesis y ≠ 0. later, we will discover that this is really the same thing as "a has type blabla". but for now, let's just think of the "a" above as just a label. 
-/
