-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!



---------------------------------------------------
-- DEFINING OUR OWN (INDUCTIVE DATA) TYPES
---------------------------------------------------

/-
"Algorithms + Data Structures = Programs" is a 1976 book written by Niklaus Wirth, a famous computer scientist who among other things created the Pascal programming language. we have already defined many programs, but have we defined any data structures? not really. we have been using the basic predefined data types of LEAN, like nat, bool, and list nat. these can only take us so far. sometimes we need more elaborate data structures. sometimes we need more complex data types. although we will not focus on this topic in this course, let us still gain some basic understanding on how to define our own data types in LEAN. 
-/

-- Defining our own types, and function definitions on those by case matching:

-- as an example, let's define a new type called "weekday": 
inductive weekday : Type
| sunday : weekday
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday
| saturday : weekday

#check weekday -- weekday is indeed a type 
#print weekday -- weekday has 7 "constructors" 

-- recall the predefined type bool:
#print bool -- bool has 2 constructors 

-- we can check the type of the new elements we just defined:
#check weekday.friday -- friday is the best day!
-- we cannot #eval them:
#eval weekday.friday
-- but we can #reduce them (in fact they don't reduce to anything else but themselves):
#reduce weekday.friday


-- let's define a function on the newly defined type:
def next_workday_too_much_typing : weekday → weekday 
    | weekday.sunday := weekday.monday
    | weekday.monday := weekday.tuesday
    | weekday.tuesday := weekday.wednesday
    | weekday.wednesday := weekday.thursday
    | weekday.thursday := weekday.friday
    | weekday.friday := weekday.monday
    | weekday.saturday := weekday.monday

open weekday -- so that we can write just "sunday" instead of "weekday.sunday" 

def next_workday : weekday → weekday 
    | sunday := monday
    | monday := tuesday
    | tuesday := wednesday
    | wednesday := thursday
    | thursday := friday
    | friday := monday
    | saturday := monday

example: next_workday friday = monday := begin refl, end
example: next_workday saturday = monday := begin refl, end
example: next_workday (next_workday monday) = wednesday := begin refl, end

/-
observations 
- (f x) never equals x - never returns the day you give 
- never returns saturday or sunday 
- friday saturday and sunday all return monday 
-/

#check for all x : weekday, next_workday x not equal x 



#check monday 
#check weekday.monday 



---------------------------------------------------
-- RE-DEFINING THE NAT DATA TYPE
---------------------------------------------------

-- now let's look at a more interesting definition of an inductive data type (by the way, why are these called "inductive"? because they are strongly related to "induction", a fundamental proof technique that we will see later). 
-- let's re-define the natural numbers:
-- (for a similar treatment with Coq, see https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#lab31)

inductive mynat : Type   -- we give it the name "mynat" because "nat" is taken
    | Z : mynat 
    | S : mynat -> mynat 


/- what does the above definition do? it provides a step-by-step method to "construct" natural numbers. this is part of the "constructive" philosophy in mathematics and computer science. the method is: you can construct a mynat in two ways (and only those two ways):
  - either by calling the constructor mynat.Z
  - or, if you already have constructed another mynat, say x, by calling (mynat.S x)
-/

#check mynat.Z -- just Z here doesn't work

#check mynat.Z -- 0
#check mynat.S (mynat.Z) -- 1
#check mynat.S (mynat.S mynat.Z) -- 2  
-- etc ...

-- continuing this way ad infinitum, we can construct all the mynats! 


open mynat -- this allows us to omit "mynat." 


#check Z -- zero
#check S Z -- one
#check S (S Z) -- two
#check S S Z -- notice that this doesn't work. why?


#check (S S) Z -- type error 




-- NOTE: the constructors of a newly defined data type must return that type:

inductive bla : Type 
    | bli : bla 
    | blu : bla → nat   -- constructor blu is invalid, because it returns a nat! it should return a bla



---------------------------------------------------
-- DEFINING BASIC ARITHMETIC OPERATIONS ON mynats:
---------------------------------------------------

-- addition on mynat :
def myplus: mynat -> mynat -> mynat 
  | mynat.Z y := y 
  | (S x) y := S (myplus x y)    -- (x+1) + y  =  (x+y) + 1  
--  | (mynat.S x) y := (myplus x (S y))     -- (x+1) + y  =  x + (y+1)   


#check myplus 

example: myplus Z Z = Z := begin refl, end 
example: myplus Z (S Z) = S Z := begin refl, end 
example: myplus (S Z) Z = S Z := begin refl, end 
example: myplus (S Z) (S Z) = S (S Z) := begin refl, end 




/- this is great, but mynats are unreadable. so we will continue by defining functions on nats. we will re-define the well-known operations like addition and multiplication on nats, so that we can reason about them. notice that we know how nats are defined. we can see that using #print:
-/

#print nat 

/- in fact, if we use something called a "namespace" we can redefine exactly the same type ourselves:
-/
namespace nat_playground
-- every name defined between here and "end nat_playground" is prefixed by "nat_playground." now we can re-define the type "nat" (i.e., "nat_playground.nat")  without worrying that it will clash with the predefined type nat:

inductive nat : Type 
    | zero : nat 
    | succ : nat → nat 

end nat_playground

/- so from now on, we will assume that nat is defined as above, and we will re-define the same operations on nat instead of mynat. the advantage is that we can use 0, 1, 2, etc, instead of nat.zero, nat.succ nat.zero, etc. 
-/

example: 3 = nat.succ (nat.succ (nat.succ nat.zero)) := begin refl, end 

-- addition: 
def plus : nat -> nat -> nat 
  | nat.zero y := y 
  | (nat.succ x) y := nat.succ (plus x y)  

#eval plus 110 33  

#check plus 
example: plus 0 0 = 0 := begin refl, end 
example: plus 0 1 = 1 := begin refl, end 
example: plus 1 0 = 1 := begin refl, end 
example: plus 1 1 = 2 := begin refl, end 
example: plus 111 1111 = 1222 := begin refl, end 

-- we could also have defined plus like this:
def plusbis : nat -> nat -> nat 
    | 0 y := y 
    | (x+1) y := (plus x y) + 1

-- but we will avoid the above definition, because it's not immediate obvious that "x+1" is the same as "nat.succ x". now that we know how nats are defined, we will use the constructors for nats. we will make an exception for 0: we can use 0 instead of nat.zero. 





def len : list ℕ → ℕ 
    | [] := 0
    | (_ :: L) := 1 + len L 


---------------------------------------------------
-- INTRODUCTION TO SPECIFICATIONS
---------------------------------------------------

/- 
enough with programming for now! let's start now talking about specs (specifications)! specifications are _properties that we want our programs to have_. we have already written some simple specifications, with "example:". 
-/

example: len [] = 0 := begin refl, end 
/- in english, we can read the above as saying "len should return zero when called with the empty list as input" or something like that. 

specs written in english are fine, but they are not precise enough. in this class, we will write specs in logic. specs written in logic are called _formal_ specifications. 
-/


---------------------------------------------------
-- THE TYPE Prop 
---------------------------------------------------

/- what exactly can we write after "example:" ? we can write any statement of type "Prop" (for "Proposition"). a proposition is something that can be either true or false, but it is _not_ a boolean. for example, claims of equality are propositions:
-/

#check (0 = 0)  -- we can drop the parentheses, but note that what is being checked is the entire expression "0 = 0"
#check 0 = 0 
#check 2*3 = 6 
#check len [] = 0 
#check len [1,2,3] = 3

/-
we read the above in the usual way: "0 = 0" is of type Prop, "2*3 = 6" is of type Prop, etc. 

you can think of Prop as the type of all logical claims that we might want to make in LEAN. in particular, everything we might want to prove in LEAN will be a Prop. every theorem, lemma, example, etc. (we'll see theorems and lemmas below). 

Prop does not include just true claims. it includes ALL claims: 
-/

#check 0 = 1 
#check 2*3 = 7 
#check len [] = 1
/- you may find it shocking that obviously false statements such as "0 = 1" are well-typed expressions in LEAN. but you shouldn't be shocked. "0 = 1" is just an expression. it is a logical statement which _claims_ that 0 is equal to 1. this statement may be true, but it may also be false. we don't know yet, until we try to prove it. but we can always claim something, even if we don't know how to prove it. after all, there are many open problems in mathematics. we can state them, but we cannot prove them yet. the beauty of LEAN and similar logics is that everything has a type, including logical statements like "A = B". 
-/

/- "true" and "false" are predefined statements of type Prop. you can think of "true" as "a statement which is true" and of "false" as "a statement which is false". they are like canonical representatives of truth and falsehood. 
-/
#check true     -- not to be confused with tt of type bool
#check false    -- not to be confused with ff of type bool 

#check tt 
#check ff 




---------------------------------------------------
-- EQUALITY
---------------------------------------------------

/-
the = symbol in LEAN is infix notation for equality. it turns out that equality is just a predefined function in LEAN, called _eq_: 
-/

#check eq 
#print eq 

/-
what is the type of eq? it is interesting that the two statements above output the type of eq in a different manner, but you can think of eq as a function that takes two elements x and y both of some type α and returns an element of type Prop. 

now we can understand better what we write when we write things like "0 = 0", and why this is of type Prop. 
-/

#check 0 = 0   -- this is syntactic sugar for "eq 0 0" 
#check eq 0 0  

#check len [1,2,3] = 3 
#check eq (len [1,2,3]) 3 
example: eq (len [1,2,3]) 3 := begin refl, end 

#check eq 0 1   -- this is perfectly well typed, even though it's a false claim 



---------------------------------------------------
-- SPECIFICATIONS
---------------------------------------------------

/- equalities of the form "len [1,2,3] = 3" are "mini-specifications". they are examples of properties that we want our programs to have. sure, these are simple properties/specifications, for now. but they are specifications nevertheless. later, we will learn to write more interesting specifications, for example, specifications involving forall quantifiers, ∀, like the one below: 
-/

#check ∀ x : ℕ, len [x] = 1 
#check forall x : nat, len [x] = 1 

/- these more interesting specifications are also of type Prop. so it should be clear that the type Prop is much "larger" than the type bool. poor type bool only contains two elements, tt and ff. but type Prop contains many, many elements. in fact it contains infinitely many elements, since there's an infinite set of logical statements like the one above that we can write. but for now, don't worry if you cannot write (or even read) such statements. we'll get back to that soon. in fact, we will not only learn to read and write such statements. we will also learn how to prove them!
-/

-- all these are logical claims (Props). some of them are true, some not!

#check ∀ x y : ℕ, x + y = y + x 
#check ∀ x y : ℕ, plus x y = plus y x 

#check ∀ x y z : ℕ, (x + y) + z = x + (y + z)
#check ∀ x y z : ℕ, plus (plus x y) z = plus x (plus y z) 

#check ∀ x y : ℕ, x = y 
#check ∀ x y : ℕ, x * y = y * x 
#check ∀ a b : bool, a && b = b && a 
#check ∀ a : bool, a = tt 


/- you should start thinking about properties (specifications) of the programs you write. even simple functions like next_workday have some interesting properties. can you think of a property that next_workday has? just express the property in english for now. later we'll see how to formalize it (i.e., write it down in logic). 

-- ANSWER:






























- one property is "for any weekday d, (next_workday d) is never a saturday nor a sunday". 

- another property: for any input day x the output day should be different from x.  

-/


----------------------------------------------------
-- sorry
----------------------------------------------------

example: ∀ x : nat, len [x] = 1 := begin sorry, end -- sorry, don't know how to prove it yet
-- sorry placeholder that it is not finished but doesnt give an error just a warning 


#check len [x] = 1   -- i cannot write this, what is x ? 


#check len [_] = 1  -- it's weird that this works ... 
-- but it's hard / impossible to use: 
example: len [_] = 1 := begin refl, end 



---------------------------------------------------
-- EXAMPLES, LEMMAS, THEOREMS
---------------------------------------------------

/- in LEAN, apart from "example", we can use "lemma" and "theorem" to write down propositions. the only difference is that "lemma" and "theorem" require the proposition to have a name / label. for instance:
-/
example: len (0 :: [1,2,3]) = 4 := begin refl, end 
lemma my_first_lemma: len (0 :: [1,2,3]) = 4 := begin refl, end 
theorem my_first_theorem: len (0 :: [1,2,3]) = 4 := begin refl, end 

example: ∀ x : nat, len [x] = 1 := begin sorry, end 
lemma cant_prove_this_yet: ∀ x : nat, len [x] = 1 := begin sorry, end 
theorem but_it_must_be_true: ∀ x : nat, len [x] = 1 := begin sorry, end 



lemma a_simple_lemma: 1 = 1 := begin refl, end 

theorem a_simple_theorem: 2 + 2 = 4 := begin refl, end 



---------------------------------------------------
-- FOR-ALL PROPOSITIONS
---------------------------------------------------

/- we have written quite a few functions already, yet we have done very few proofs, and these were very trivial examples. they were tests, rather than general theorems. can we prove something more general? first, let's learn how to write more general properties. we will not give a complete formal description of the logic of LEAN (which is one of the most advanced/powerful logics out there). instead, following our learning-by-doing philosophy, we will give examples. 
-/

-- what general thing can we say about plus? for example, we can say that (plus 0 x) should return x. we write this formally as follows:

#check (forall x : nat, plus 0 x = x)

/- the property is the "(forall x : nat, plus 0 x = x)" (with or without the parentheses, which are not needed in this case). the #check part just tells us the type of this expression, which is Prop, as we said earlier. 

we can read the above statement in english as _"for any x of type nat, (plus 0 x) is equal to x"_. the "forall" is the so-called _universal quantifier_ in logic. we can also write it as unicode ∀ :
-/
#check (∀ x : nat, plus 0 x = x)

-- we can omit the type of x because LEAN can infer it from the fact that we pass it to plus, and plus takes two nats:
#check (forall x, plus 0 x = x)

-- but as we said earlier, in this class we will insist on not omitting the types. 


-- can you think of other specifications that we can write about plus?

-- here's some:

#check ∀ x : nat, plus x 0 = x
#check ∀ (x y : nat), plus x y = plus y x       -- this is called commutativity
#check ∀ (x y z : nat), plus (plus x y) z = plus x (plus y z)   -- associativity



---------------------------------------------------
-- OTHER FORALL SPECIFICATIONS 
---------------------------------------------------

#check forall x : nat, plus 0 x = x   
#check forall x : nat, plus x 0 = x 
-- ... 



---------------------------------------------------
-- A BRIEF NOTE ON THE EXISTS QUANTIFIER ∃ 
---------------------------------------------------
/-
like many logics (e.g., first-order logic), LEAN's logic includes not just the forall quantifier ∀, but also the _exists_ quantifier:
-/

#check exists x : bool, x = tt 
#check ∃ x : bool, x = tt 

/-
we will not have to use the ∃ quantifier in this class. in your next homework you will see how to write a specification which you might initially think requires ∃ without using ∃. 

you will also see how to write formally the so-called "drinker's paradox" which goes like this: "There is someone in the pub such that, if they are drinking milk, then everyone in the pub is drinking milk." in order to formalize the drinker's paradox you will need ∃. 
-/




---------------------------------------------------
-- PROPOSITIONS COMBINING FORALL, EXISTS, FUNCTIONS, etc
---------------------------------------------------

#check forall x : nat, exists y : nat, x = y + 1 

#check forall x : nat, exists y : nat, x = plus y 1 

#check ∀ x : nat, ∃ y : nat, plus x 1 = y 


#check ∀ x : nat, ∃ y : nat, y = x   

#check ∀ x : nat, ∃ y : nat, y = plus x x 
#check ∀ x : nat, ∃ y : nat, x = plus y y   
  

---------------------------------------------------
-- FORMAL SPECIFICATION
---------------------------------------------------

#check (forall x : nat, plus 0 x = x)
#check ∀ x : nat, plus 0 x = x   



---------------------------------------------------
-- FORMAL VERIFICATION = PROVE THAT THE PROGRAM SATISFIES THE SPECIFICATION 
---------------------------------------------------


/-
    SPECIFICATION AND FORMAL SPECIFICATION

A set of properties like the ones above is called a _specification_. We usually use the term _property_ to mean one statement of type Prop, like for example, the property (∀ x : nat, plus x 0 = x). We usually use the term _specification_ (sometimes abbreviated _spec_) to mean more than one properties. But we can always construct a BIG property by taking the _conjunction_ (logical AND) of many properties, so the distinction between one or many is not essential. 

Specifications can be written in many languages. They can be written in English, for example. These are "informal" specifications. In this course we will write _formal_ specifications, that is, specifications written in logic. English is imprecise and can lead to miscommunication and catastrophic errors. Logic is precise and unambiguous.

Funny: all yes/no questions in English have the same answer: it depends. :)
-/

/- FORMAL VERIFICATION

Writing down a formal specification / property is one thing, and proving it is another. The fact that we believe that our program has some property, doesn't mean that our program indeed has that property. We need to check. We need to _verify_. This process is called _verification_, and in the case of proving formally that (formal) programs satisfy their formal specifications, it is called _formal verification_. Formal verification is what we are doing in this course. 
-/

/- FORMAL PROOFS

We have already done a bit of formal verification, by proving simple theorems with "example" and "refl". These were pretty trivial: they were just tests (but still useful, as we said, for example, for regression testing). We don't need the entire LEAN machinery to prove such simple examples, since we can just evaluate (compute) a function and compare its output to the expected result (the function still needs to be guaranteed to terminate though). 

We will now start getting a bit more serious about proving program correctness. Proving is partly a science and partly an art. It is a science because it is precisely, formally, and mathematically defined. But it is also an art because theorem proving is not always easy, and cannot always be automated. Human creativity is often needed. We will understand why this is unavoidable later in the course. 

Sometimes this theorem-proving creativity is beyond the grasp of most humans and requires the expertise, intuition, and talent of top mathematicians and computer scientists. But often this creativity is also something that can be taught, just like one can be taught to improvise, say, a jazz solo in a music class. This is what we aim to do in the rest of this course. 

Let us then begin to do more interesting formal verification, by proving more interesting properties. 
-/



----------------------------------------------------
-- try
----------------------------------------------------

-- let's start with something pretty trivial:
def identity (x : nat) : nat :=  x   -- the identity function

theorem identity_x_equals_x_first_attempt: ∀ x : nat, identity x = x :=
begin
    try {refl}, -- "try" attempts to apply a tactic but doesn't fail if that tactic fails
    -- the proof state hasn't changed, which means that the tactic refl failed to do anything useful. since that's the only tactic we have learned so far, we give up:
    sorry,
end



----------------------------------------------------
-- intro
----------------------------------------------------


theorem id_theorem: ∀ x : nat, identity x = x 
:= 
begin   
  try { refl, }, -- remember that refl didn't work, 

  intro, -- eliminates the ∀ quantifier and introduces x in the hypotheses

  dunfold identity,  -- can be uncommented to show the simplification that refl does under the hood

  refl, -- hurray! we're done!

end

/- so what is the meaning of "intro"? into is a tactic. it's one of our "magic spells". it applies to a number of situations, and in particular when the goal is of the form "∀ x, ...". in that case, intro introduces x in the assumptions, together with its type. in this case, we see above the ⊢ symbol in the proof state:

x : ℕ

this is an _assumption_ (also called _hypothesis_). it can be read as "let x be some object of type nat". 

this matches the way we would go about proving something like the above theorem with paper and pencil. we might write something like: "Let x be a nat. Then I have to prove that (identity x) equals x." That's exactly what we do here. the "Let x be a nat" is what intro does. 
-/

-- we can also prove this:
theorem plus_0_x_equals_x: forall x : nat, plus 0 x = x :=
begin
    intro,
    dunfold plus,  -- can be uncommented to show the simplification that refl does under the hood
    refl,
end

/-
-- in this case refl isnt able to simplify x + 0 but was able to do 0 + x above
-- we need to redefine plus fuction 
-- we can also prove this:
theorem plus_x_0_equals_x: forall x : nat, plus x 0 = x :=
begin
    intro,
--    dunfold plus,  -- can be uncommented to show the simplification that refl does under the hood
    refl,
end
-/

def plus2 : nat -> nat -> nat
    | x 0 := x
    | x (y+1) := nat.succ (plus2 x y) 

def negb : bool -> bool 
    | tt := ff 
    | ff := tt 

theorem negb_x_ne_x : ∀ x:bool , negb x ≠ x := begin 
    intro, 
    try {refl,}
    sorry, 
    end 
    
def andb: bool -> bool -> bool 
| tt tt := tt
| tt ff := tt
| ff tt := tt
| ff ff := tt

theorem andb_commut:
 ∀ x:bool, ∀ y : bool, andb x y  = andb y x 
 := begin 
  intro, 
  intro,
  try {refl,},
  sorry
end

theorem len_of_list_of_one: ∀ z : ℕ, len [z] = 1 
:= begin 
    intro, 
    dunfold len,
    refl, 
end

theorem len_of_list_of_three: ∀ z : ℕ, len [z, z, z] = 3 
:= begin 
    intro, 
    dunfold len,
    refl, 
end