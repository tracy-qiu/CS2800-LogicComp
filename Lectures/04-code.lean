-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!



---------------------------------------------------
-- TESTING AS PROVING
---------------------------------------------------
/-
there are two basic ways of checking the correctness of our programs: testing and proving. although this course focuses on proving, testing is very important too. moreover, (simple) testing can be seen as (simple) proving. we illustrate this and at the same time introduce the basic proof concepts in LEAN.
-/

----------------------------------------------------
-- reflexivity, refl
----------------------------------------------------

-- consider the len function that we defined earlier:
def len : list ℕ → ℕ 
    | [] := 0
    | (_ :: L) := 1 + (len L)

/- we want to test this function, to make sure that it works as intended. one way to do that is simply to evaluate the function on a bunch of inputs:
-/

#eval len [] 
#eval len [1] 
#eval len [13] 
#eval len [1,2] 

#eval len [1,2,3]
#eval len [1,1,1,2,22,0,0,0]

/- the problem with this testing approach is that it requires a human to check ("eyeball") the results. if we later change the code for some reason, we have to go over all our tests to make sure they are all still returning what they are supposed to return. a better way is to assert what we know a-priori that the function is supposed to return in each case. then, if later we change the function and introduce a bug, some of these assertions might fail automatically. in LEAN, we can use the "example" mechanism to do that. an "example" is actually a "mini-theorem" (or in fact not so mini, since we can write whatever we want inside an example), with a proof and all:
-/

example: len [] = 0 
:= begin
    reflexivity,  -- _reflexivity_ is a _tactic_ 
end

/-
yeah! we just did our first proof in this course! let's explain a bit what just went on. first, everything between "begin" and "end" is a _proof_. a proof will be essentially a sequence of "commands", that we call _tactics_. so a proof is essentially a program! 

now, place your cursor at the end of the "begin" above, and look at LEAN's "Infoview" window. you should see something called "Tactic state", which in this course we will also call _proof state_: it's the current state of our proof. at the end of "begin", i.e., at the beginning of the proof, the proof state should look like this:

1 goal
⊢ len list.nil = 0

LEAN tells us that we still have 1 goal to prove (sometimes we will "split" proofs into multiple goals, we'll see this later) and that this goal is to prove the equality "len list.nil = 0", without assuming anything. in general, the proof state will look like this:

h1 : ... some assumption here ... 
h2 : ... another assumption here ... 
... a bunch of more assumptions here ...
⊢ ... some goal here ... 

the assumptions are also called _hypotheses_. 

in our example we have no assumptions, so there is nothing above the ⊢ symbol (type "\entails" to generate this symbol - by the way, in VS Code you can hover your pointer on top of a symbol, and it tells you how to generate it).

now move your cursor at the next line of "begin" but _before_ the word "reflexivity". as you should see, the proof state doesn't change. 

now move your cursor at the end of the line "reflexivity,". the proof state should change. in fact, you should see 

goals accomplished

this is the moment every prover awaits: the proof is done, and we can close it with an "end"!

but how exactly did we accomplish this? we accomplished it with a sort of magic spell, which is this case was the command _reflexivity_. from now on we will call "magic spells" _tactics_.  _reflexivity_, also abbreviated _refl_, is our first and perhaps the most basic tactic. it applies to goals of the form A = A, that is, goals that state that a certain expression is identical to itself. that A = A is a basic axiom of equality (the axiom of reflexivity) and it's built into the logic of LEAN. 
-/


example: len [] = 0 := -- where you put the ":=" is a matter of taste
begin
    refl,  -- _refl_ is an abbreviation for _reflexivity_
end

/-
but wait! in the case of the example above, the goal is _not_ of the form A = A! it's "len list.nil = 0". the left-hand-side of that equality looks nothing like the right-hand-side. you are absolutely right, it doesn't. but reflexivity still works. the reason is that reflexivity actually does a bit more. it sometimes tries to simplify the two sides, to a point where they are identical. in this case, "simplify" means "compute" (or "reduce") the expression "len list.nil". indeed, this expression reduces to 0, and then reflexivity applies, to the simplified goal 0 = 0. we will say more about simplifications later. 
-/


-- if we really want to see what's going on, we can issue the _dunfold_ tactic prior to _refl_:

example: len [] = 0  := 
begin
    -- start issuing magic spells!
--    dunfold len,  -- not needed, but useful to illustrate what _reflexivity_ does under the hood  
    refl,  
end 


example: len [1,2,3] = 3  := 
begin
    -- comment / uncomment the things below to see what they do:
    -- dunfold len, -- interesting, why doesn't it simplify it more?  
    -- unfold len, -- wow!
    refl,  
end 

example: 0 = 0 := 
begin
    refl,  -- the goal is of the form A = A 
end




/-
one thing to note is the comma "," at the end of reflexivity. do we need this? in general we need it when we issue many tactics one after another. for the last tactic in the proof, we don't really need it, but adding it is useful. if you remove it, you have to switch to the next line (where the "end" is) to see "goals accomplished". as a stylistic convention, it's useful to add it even after the last tactic in the proof. 

admittedly, this proof was too simple. this is fine for now. we will see more complicated proofs soon. be patient. for now, we are not really doing proofs, we are really doing regression testing disguised as proofs. 
-/

-- note that these work outside proofs:
#reduce len list.nil 
#reduce len [1,2,3] 

-- but not inside proofs:
example: len [1,2,3] = 3  := 
begin
    -- #reduce [1,2,3],  -- don't use inside proof
    -- #reduce,          -- don't use inside proof
    -- #eval [1,2,3],    -- don't use inside proof
    -- #print nat,       -- don't use inside proof
    refl,  
end 






/-
if we claim something false, our proof doesn't go through:
-/

example: len [1,2,3] = 4 := begin refl, end  
example: len [1,1,1,2,22,0,0,0] = 10 := begin refl end



---------------------------------------------------
-- REGRESSION TESTING:
---------------------------------------------------

/-
our testing-as-proving approach is based on the above fact: we cannot prove false equalities! so, if we change the function and make a mistake, some tests may no longer pass:
-/

def len_bad : list ℕ → ℕ 
    | [] := 0
    | (_ :: L) := len_bad L -- bug!

-- now some of the test cases would fail (notice that some would still pass):
example: len_bad [] = 0 := begin refl, end             -- this test still passes
example: len_bad [1,2,3] = 3 := begin refl end         -- this test fails
example: len_bad [1,1,1,2,22,0,0,0] = 8 := begin refl end  -- this fails too



-- from now on, for every function we define, instead of testing it with #eval, we will test it with "example": 
example: len [1,2,3] = 3 := begin refl end
example: len [1,1,1,2,22,0,0,0] = 8 := begin refl end




---------------------------------------------------
-- BOOL
---------------------------------------------------

-- "bool" (Booleans) is a predefined type that contains only two elements, "tt" ("true") and "ff" ("false"). we can see how bool is defined using #print:
#check bool 
#print bool -- you don't need to understand everything that this is saying, we'll come back to discuss type constructors later. 
#check tt 
#check bool.tt -- same as tt
#eval if (tt = bool.tt) then 0 else 1 
#check ff 
#check bool.ff -- same as ff

-- NOTE: "true" and "false" are _not_ the same as "tt" and "ff":
#check true
#check false 
#eval if (tt = true) then 0 else 1 -- the fact that this works is misleading. ignore it and don't use it. it shouldn't work, because tt is of type bool, whereas true is of type Prop.


-- we will return to discuss type constructors and Prop later. for now, let's focus on the definition of bool: it tells us that the data type bool has two elements (or more precisely _constructors_),  namely tt (or bool.tt) and ff (or bool.ff). then, every time we define a function taking a bool as input, we can define that function by doing pattern-matching on the two possible cases for each bool argument: it can be either tt or ff. 

-- for example, let's define the Boolean negation function:
def negb : bool → bool
    | tt := ff -- if the input is tt, return ff
    | ff := tt -- if the input is ff, return tt

#eval negb tt 
#eval negb ff 
#print bool 
#eval bool.tt 
#eval tt 
#check bool.tt 
#check tt 
#check ff 
#check bool.ff 

def negbbis (b : bool) : bool := if (b = tt) then ff else tt 


/-
can we _prove_, using the methods that we have defined so far, that negb and negbbis are equivalent? two functions are equivalent if for any given input, they both return the same output when run on that input. 

in general, we cannot prove that two functions are equivalent using testing, because in general the number of possible inputs is infinite. 

but in the case of negb and negbbis, there's only two possible inputs!
those are tt and ff. because there's only two inputs, we can exhaustively test them:
-/


example: negb tt = negbbis tt := begin refl, end    -- test 1
example: negb ff = negbbis ff := begin refl, end    -- test 2 


-- this shows us a bit what's going on under the hood:
example: negb tt = negbbis tt 
:= begin 
  dunfold negb,
  dunfold negbbis,
  refl, 
end 


-- specification by finite testing:
example: negb tt = ff := begin refl, end    
example: negb ff = tt := begin refl, end    

/-
the above two tests are sufficient to _specify_ negb, because they exhaustively cover all possible inputs to negb. we will talk more about _specification_ later. specification of functions like negb is possible via testing because the number of possible inputs to negb is finite. this is not always the case (e.g., think of a function on nats). 
-/


/-
how exactly does reflexivity work? reflexivity relies on the axiom of logic that the equality relation = is _reflexive_, meaning that x = x, for any x. 

we are not going to worry about _how exactly_ reflexivity is _implemented_ in LEAN. we will only learn to use it. we will learn _what_ it does, not _how_ it does it. 

here's some examples of other cases where reflexivity applies. we will see more of those later, and for now, ignore the rest ("forall", "intro", etc). only focus on what happens to the proof state right before and right after issuing reflexivity:
-/

example: [1,2,3] = [1,2,3] := begin 
    refl,  
end 

example: forall x : nat, x = x := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: forall L : list nat, L = L := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: forall f : nat -> nat, f = f := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: forall x : nat, 2*x+1 = 2*x+1 := begin 
    intro, -- check the proof state here
    refl,  -- and here 
end 

example: 2*10+1 = 21 := begin refl, end  -- refl does some arithmetic 

example: forall x : nat, 1+x+1 = x+2
:= begin
    intro,
    refl, -- but refl cannot do too much arithmetic!
end




---------------------------------------------------
-- BOOL CONTINUED
---------------------------------------------------

/- 
what if we want to define Boolean AND (_conjunction_), which takes two bools as input arguments? we can do this simply by exhausting all possible cases (like in a _truth table_):
-/
def andb : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff tt := ff
    | ff ff := ff

-- we can exhaustively test andb:
example: andb tt tt = tt := begin refl, end 
example: andb tt ff = ff := begin refl, end 
example: andb ff tt = ff := begin refl, end 
example: andb ff ff = ff := begin refl, end 


---------------------------------------------------
-- MORE ON PATTERN MATCHING
---------------------------------------------------

-- what if we forget a case? LEAN complains:
def andb_incomplete : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff ff := ff

-- what if we repeat a case redundantly? LEAN complains:
def andb_redundant : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff tt := ff
    | tt tt := tt 
    | ff ff := ff

-- what if we repeat a case but define a different output? LEAN complains:
def andb_ambiguous : bool → bool → bool
    | tt tt := tt 
    | tt ff := ff
    | ff tt := ff
    | tt tt := ff  
    | ff ff := ff


-- here's another (correct) way to define andb:
def andbbis : bool → bool → bool 
    | ff _ := ff 
    | tt ff := ff 
    | tt tt := tt 

-- and another:
def andanother : bool -> bool -> bool 
    | tt tt := tt 
    | _ _ := ff 

#eval andanother ff tt 
#eval andanother tt ff 
#eval andanother ff ff 
#eval andanother tt tt  

-- and yet another:
def andsome : bool -> bool -> bool 
    | ff _ := ff 
    | tt x := x 


/- 
mini-quiz (ungraded): 

can we use the exhaustive testing method (_example:_) to prove that all these definitions are equivalent? how? how many tests will we need?
-/

-- for example, let's do it to show that andsome is equivalent to andb:

example: andsome tt tt = andb tt tt := begin refl, end 
example: andsome tt ff = andb tt ff := begin refl, end 
example: andsome ff tt = andb ff tt := begin refl, end 
example: andsome ff ff = andb ff ff := begin refl, end 



-- boolean implication ("if a then b"):
def ifb : bool → bool → bool 
    | tt tt := tt
    | tt ff := ff 
    | ff tt := tt 
    | ff ff := tt 

def ifbbis: bool -> bool -> bool 
    | tt tt := tt 
    | tt ff := ff 
    | ff _ := tt 








---------------------------------------------------
-- A NOTE ABOUT PERFORMANCE
---------------------------------------------------

/-
program performance is of course critical to computer programming. but we will not worry much about it in this class. in particular, you will _never_ lose points in this class because your implementation of something is "inefficient". in this class we primarily care about correctness, not about efficiency. 

no matter what the function and its inputs are, we expect examples/tests to be discharged/proved just by using refl. this happens most of the times, but for some "large" examples, LEAN may timeout:
-/

def exponent : ℕ → ℕ → ℕ  
    | _ nat.zero  := 1
    | x (nat.succ n) := x * (exponent x n) 

example: exponent 2 5 = 32 := begin refl, end 

example: exponent 2 10 = 1024 := begin refl, end  -- takes some time, see the yellow bars to the left 

-- sometimes we might see "timeout". this is ok. it just means that LEAN ran out of steam. we can try smaller inputs. 
-- example: exponent 2 12 = 4096 := begin refl, end  -- this times out on my laptop 

-- #reduce exponent 2 14 -- #reduce is not very fast 

#eval exponent 2 100 -- #eval is much faster (because it bypasses the LEAN kernel, which is an "unsafe" thing to do)

/-
one reason why we don't care much about performance in this class is this: checking the proof of a theorem does not need to happen very often. in fact, in principle, it only needs to happen once! once a proof is checked to be correct (and assuming the proof checker is also correct) it doesn't have to be checked again, ever. this is very different from other kinds of programs, which need to run again and again, possibly on the same inputs. for such programs, we worry about performance a lot, because we need to run them all the time. for proof checkers, we worry less. still, this is only half of the story. we may not run the proof checker on the _same_ proof again and again, but we may still run it on many _different_ proofs. we want the proof checker to be efficient if we have many proofs to check. but in this course we are not going to worry about implementation and performance of proof checkers. 
-/

