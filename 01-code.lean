-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- this is a comment


/-
this is also a comment

it's a multiple line comment.

it's 
a 
multiple 
line 
comment.

-/



/-

EXAM DATES: MARK YOUR CALENDARS!

EXAM 1: Mon Oct 24 2022 6:00 pm - 8:00 pm, SN 108   

EXAM 2: Wed Nov 30 2022 6:00 pm - 8:00 pm, HT 129 and BK 320

If you ABSOLUTELY CANNOT make one of those dates, email Prof. Tripakis ASAP!

-/



-- Is there anyone who has NOT JOINED PIAZZA?



-- Is there anyone who has NOT BEEN ABLE TO INSTALL LEAN?



-- Is there anyone who has NOT JOINED A HOMEWORK GROUP?












-----------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN
-----------------------------------------------------------------
/-
    In your previous programming courses you have already seen functional programming (in Racket, Scheme, Lisp, ...).   But you may have not seen types. Types can be seen as "input-output contracts" between a program (a function f) and its environment (the functions that call f).  Types are useful because they allow the compiler to catch at compile-time many errors that would otherwise need to be caught at run-time. 

    Let's see a few examples of functional programs in LEAN, and how these use types.

    First, we begin with some basic LEAN commands:
    #eval
    #reduce
    #check

-/

-------------------------------------------------------------------
-- BASIC EXPRESSIONS, PREDEFINED OPERATORS, #eval, #reduce, #check
-------------------------------------------------------------------

-- first let's see some basic expressions and predefined operations in LEAN:

-- addition:
#eval 2+3  -- #eval is a "compute" command
#reduce 2+3 -- #reduce is another compute command; we won't worry about the difference between #eval and #reduce for now

-- subtraction:
#eval 3-2  

#eval 2-3 -- weird! subtraction defined over natural numbers
#eval 2-300 
#check 2-3 


#eval (2:int)-(3:int) -- by default, "2" is a nat, but "(2:int)" is an int
#eval (2:int) - (3 : int) 
#eval (2:int) - 3 
#eval 2 - (3 : int) 
#eval ((2-3):int) 


-- multiplication:
#eval 2*3  


-- division:
#eval 4/2 
#eval 4/3 -- integer division!
#eval 2/3 -- integer division!
#check 2/3



-- exponentiation:
-- in some installations ^ is not defined. i don't know why. you need not worry about it, because we will redefine all these basic mathematic operations ourselves anyhow, before we prove things about them. 
#eval 2^10   
#eval 2^100 -- big number
#eval 2^1000 -- YUGE number!



-- if-then-else
#eval ( if (0 = 1) then (10*2) else 1 )  
#eval ite (0 = 1) (10*2) 1 -- if-then-else is actually the ternary function "ite"
#eval if (0 = 1) then (0+2) else (1+13) 
#eval ite (0 = 1) 2 14 

#eval if (0 = 0) then 10 else 20 
#eval ite (0 = 1) 10 (ite (0 = 10) 10 (20+10))



-- #check  gives the type of an expression:

#check 2 
#check (2+3) 
#check (2-3) 
#check (2:int) 
#check (2:int) - 3  

#check bla -- bla is undefined, you see an error message




-----------------------------------------------------------------
-- FUNCTIONS
-----------------------------------------------------------------


def f (x : nat) : nat := x + 1 
-- function f takes x of type nat and returns a result also of type nat; the result is x + 1

-- nat and ℕ are the same, so we could have defined f also as:
def f2 (x : ℕ) : ℕ := x+1   
def f3 (x : nat) : ℕ := x+1
def f4 (x : ℕ) : nat := x+1 


-- all these functions have the same type
#check f  
#check f2 
#check f3
#check f4 

#eval f4 10 

/-
 in fact, f, f2, f3, f4 are _equivalent_ meaning that they return the same output given the same input. we shall be able to prove this formally later in this course. for now, we can convince ourselves that these functions return the same thing by doing a bit of testing, i.e., evaluating them on a few inputs:
-/


-----------------------------------------------------------------
-- FUNCTION APPLICATION 
-----------------------------------------------------------------


#eval (f 100)  -- (f 0) is function application (instead of f(0) we write (f 0))
#eval f 0  -- often parentheses are not needed
#eval f(0) -- this also works, but not necessary
#reduce f 130  -- we will see the difference between #eval and #reduce later 

#eval f2 0
#eval f3 0
#eval f4 0 



-- omitting parentheses is fine, except when they are needed to change the priority of operations:

def d (x : nat) : nat := 2*x
#eval (d 2)  
#eval d 2 + 3    -- function application has higher priority than + so this is (d 2) + 3
#eval (d 2) + 3 
#eval d (2+3)    



-----------------------------------------------------------------
-- WHY FUNCTIONAL PROGRAMMING INSTEAD OF IMPERATIVE PROGRAMMING?
-----------------------------------------------------------------
/- 
brief discussion: why are we using a functional programming language in this course?

 answer:
 mainly because it's easier. it's easier to explain verification and proofs using a functional programming language, because the latter is closer to standard math than an imperative language, say C or Java. also, functional programming languages like LEAN's don't have some "hacky" features like pointers, memory allocation, side effects, etc, which make things complicated. having said that, reasoning about imperative code is both necessary and interesting. time permitting, we will touch upon this towards the end of the semester. 
-/





/-
PollEv: let's take a test quiz!

go to link:

https://pollev.com/tripakis


-/






-----------------------------------------------------------------
-- TYPES
-----------------------------------------------------------------

-- LEAN's programming language is typed
-- we have already briefly talked about types and seen #check

#check 0 -- LEAN tells us (see infoview window) that 0 is of type nat (or ℕ)
        -- in general, the notation "x : T" means "x is of type T"

-- #check can be used to show the type of any expression
#check (3 + 2*7) -- this expression is also of type nat 

-- nat is the type of natural numbers: 0, 1, 2, ... 
-- even types are of some type:
#check nat  -- nat is of type "Type"
#check ℕ -- nat and ℕ are the same thing; in LEAN we can also use unicode symbols, in addition to ASCII

-- if all types are of some type, does it mean that "Type" also has a type? let's find out! 
#check Type -- "Type" is of type "Type 1"
#check Type 1 -- "Type 1" is of type "Type 2"

/- the types of types (like Type, Type 1, Type 2, etc.) are sometimes called _sorts_. what are Type, Type 1, Type 2, etc.? think of them as a type _hierarchy_. we do not need to know more about it (for more, see the references in the lecture notes on type theory). 

we will have more to say about types, but we will only discuss as much about them as we need for the purposes of this course. 
-/



-- functions also have types, as we also saw earlier: 

#check f  -- f is a function from ℕ to ℕ 
#check ℕ → ℕ 
#check d 

-- what about the predefined operators like +, *, etc?
#check +    -- doesn't work: + is not really a function, but a generic infix notation for an "add" operation


#check nat.add  -- nat.add is the predefined addition function on nats
#eval nat.add 2 3 



#check nat.sub -- subtraction
#check nat.mul -- multiplication
#check nat.div -- division

#eval nat.sub 3 2
#eval nat.sub 2 3
#eval nat.mul 3 2
#eval nat.div 3 2


/-
how can we know what functions +, *, etc correspond to?

we can't. that's why we will re-define everything from scratch before proving things. 
-/

#check ite   -- this shows the type of the function ite, which is "Π (c : Prop) [h : decidable c] {α : Sort u_1}, α → α → α". 
/-
you DON'T have to understand what this says! we will not talk much about type theory in this class. if you want to learn more, check the references to type theory in the lecture notes (https://course.ccs.neu.edu/cs2800f22/lecture-notes.pdf) where you can find pointers to books and online notes. in particular, the type system of LEAN is briefly described here: https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html (this is actually a nice description, accessible to your level). 
-/

#check int.add 


-- question: if all types have a type, what is the type of (ℕ → ℕ) ?
-- let's find out!
#check ℕ → ℕ   -- the type (ℕ → ℕ) has type "Type", just like ℕ has type "Type"
#check nat -> nat   -- this is the same as ℕ → ℕ 
#check ℕ -> nat     -- same thing
#check ℕ → nat      -- same thing, etc. 




-----------------------------------------------------------------
-- FUNCTION TYPES ARE "CONTRACTS"
-----------------------------------------------------------------

-- like we said earlier, types are input-output contracts:

#check f 

/- 
 the type of f is ℕ → ℕ (or nat -> nat), that is, naturals to naturals. this means that f takes as input a natural number, and returns as output also a natural number. the type of a function f (also called its "signature") can be seen as an input-output contract: it is the responsibility of the caller to call f with a natural number as argument. it is the responsibility of f to return a natural number as a result. 
-/



-----------------------------------------------------------------
-- TYPE ERRORS
-----------------------------------------------------------------

-- when type contracts are violated, we get type errors:


#check 0 
#eval f 0  -- all good

#check (-1:int)  -- (-1:int) is of type int
#eval f (-1:int) -- type error: f expects a nat, but we give it an int. the environment (the callers of f) has "broken" the contract. 


#check (1:int)
#eval f (1:int) -- type error, again, the fault is with the environment 


-- here function fg breaks the output contract, the fault is with fg 
def fg (x:nat) : nat := x-(20:int)  
#eval fg 18 


#eval f [1,2] -- type error 
-- the error message of LEAN is pretty understandable: it tells us that [1,2] 
-- is a list, but f expects a nat as input. we'll look more at lists later. 



#eval f (f 0)  -- all good, because (f 0) is guaranteed to be a nat, because of f's type 

#check d  

#eval f (d 0)   




#eval (f f) 0  -- type error: this is parsed as (f f) 0, because function application is _left associative_ ("stacks to the left") 
#eval (f f)  -- type error: f is not of type nat, so it cannot be passed to f which expects a nat
#eval (f d)  -- type error: d is not of type nat, so it cannot be passed to f which expects a nat
#eval f d 0    -- same problem as with (f f) 0 
#eval (f d) 0 -- same problem as with (f f) 0 

/- 
LEAN's programming language is typed. when programming in LEAN, we must be careful about types, and we must resolve any typing errors. other languages are more flexible about types.  LEAN has strong typing, meaning that typing errors are not tolerated. we (in this class) will not accept programs with type errors (in homeworks, exams, etc). 
-/





-----------------------------------------------------------------
-- SOME BASIC TYPES IN LEAN
-----------------------------------------------------------------

/-
we can (and will later) define our own types in LEAN. for now, let's go over LEAN's basic predefined types:
-/

-- natural numbers:
#check 0 
#check 1
#check 22


-- we also have negative integers, but we will not deal with them too much:
#eval -1 -- this fails
#eval (-1:int)
#check (-1:int) 
#check ((-1):int)


#check 103.5 -- weird! we will not deal much with non-integers
#eval 103.5 -- weird!


-- we also have booleans:
#check tt -- boolean "true"
#check ff -- boolean "false"


-- we also have strings:
#check "abc" 
#check "hello i love you" 



-- we also have lists:

#check [] 
#check list.nil   

#check [1] 
#check list.cons 1 list.nil 
#check 1 :: [] 
#check list.cons 1 1  -- cryptic message, but 2nd argument of cons must be a list! 

#eval list.cons 1 (list.cons 2 (list.cons 3 list.nil))   
#eval [1,2,3]   



#check [1,2,3]   
#eval list.cons 0 [1,2,3]   -- this should be similar to what you've seen already in lisp/scheme
#eval 0 :: [1,2,3]          -- infix notation for cons 

#check [1,2,3]  -- LEAN infers that this is a list of nats
#check ["hello","bye"] -- LEAN infers that this is a list of strings 
#check [ [1,2], [3,4,5], []  ]   -- a list of lists of nats 

#check [1,"hello"] -- this is allowed in some languages, but not in LEAN (at least not directly, without defining some sort of union/sum type)

#check [(-1:int),2,3]   



-----------------------------------------------------------------
-- POLYMORPHISM
-----------------------------------------------------------------

-- LEAN has a "polymorphic" type system:
#check list.nil -- this is the empty list: its type can be read as "list of something / list of some type"
#check []   -- same as list.nil 

-- we will not talk much about polymorphism, so you can ignore that for now
#eval 0 :: [] 
#check 0 :: []  -- this is a "list of nats" 

#check list.cons 

-----------------------------------------------------------------
-- TYPE INFERENCE 
-----------------------------------------------------------------

-- LEAN can sometimes infer the types in function definitions too:
def f5 (x : nat)  := x + 1  -- notice that we omitted the output type
#check f5  -- LEAN infers that the output type is nat 

-- we could also have omitted both:
def f6 (x) := x+1 
#check f6  -- LEAN is still able to infer the types. how? not the topic of this course, but probably because 1 is by default a nat. 

def f7 (x) := x + (1:int) 
#check f7  -- now that we forced 1 to be an int, the inferred type changes

-- type inference doesn't always work, and sometimes it might result in unexpected results that don't necessarily capture the intention of the programmer. _in this course, we will insist on specifying the type of every function, including input and output._


-----------------------------------------------------------------
-- FUNCTIONS WITH MORE THAN ONE INPUTS
-----------------------------------------------------------------

-- here's a function that takes as input two nats, x and y, and returns a nat:
def g (x y : nat) : nat := x+y 

-- we could also have written it equivalently like this:
def gg (x : nat) (y : nat) : nat  := x+y 


-- the type of g is interesting:
#check g -- you should see "g : ℕ → ℕ → ℕ"    
        -- adding the dropped parentheses, this is the same as: "g : ℕ → (ℕ → ℕ)"
        
-- indeed ℕ → ℕ → ℕ is the same as ℕ → (ℕ → ℕ):
#check ℕ → (ℕ → ℕ)     
#check ℕ → ℕ → ℕ 

/- 
what the def of g says is: "g is a function that takes as input a nat, and returns another function that takes as input another nat and returns a nat". 

you might object here that this doesn't make sense. how can g take as input just one nat, since we just defined it to take as input TWO nats?
but if you think about it a little bit, you will see that the two interpretations are equivalent:
-/
#eval (g 4 3)
#eval g 3 4 -- this is the same as (g 3) 4
#eval (g 3) 4 

#check (g 3)  -- just (g 3) is a legal expression! it's a function from ℕ to ℕ. sometimes this is called "partial evaluation" 
#check g 3  -- this works and is the same as the above. it should give "g 3 : ℕ → ℕ"

#eval (g 3) -- this doesn't work, because (g 3) is a function. we cannot "#eval" functions
#eval f    -- same problem
#eval g    -- same problem 

-- but we can #reduce functions:
#reduce (g 3)   -- don't worry about the λ stuff, we'll learn that later
#reduce f 
#reduce g 




-- #eval g (3 4)    ERROR !  






-- note that this doesn't work:
#eval g (4,3) -- type error: (4,3) is a pair, of type ℕ × ℕ 
#check (4,3) 
/-
from your previous experience with math courses, you might expect that functions that take two arguments are functions over pairs, like 

    f : A × B → C

where A × B is the cartesian product of A and B. we can also have this in LEAN, but for the most part, it is far more useful to define functions with many arguments in the way we did above. we will return to this point later in the course. 
-/


-- note: these are different types, we'll return to that later:
#check nat -> (nat -> nat) 
#check (nat -> nat) -> nat 
#check (ℕ → ℕ) → ℕ     



-- here's a function which mixes a few types:
def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 
#check h -- h : ℕ → bool → ℤ   
#eval (h 3) tt 
#eval h 3 ff 

#check h 4 

#check h 4 tt 
#eval h 4 ff 
#check h tt -- type error


#check nat -> (bool -> int) -- OK   
#check (nat -> bool -> int) 
#check nat -> bool -> int  


#check (nat bool -> int) -- wrong syntax



-- note: again, these are different types, we'll return to that later:
#check nat -> (bool -> nat) 
#check (nat -> bool) -> nat 



-- a function with many inputs:
def fgh (x : nat) (y : bool) (z : int) : string := "hello" 
#check fgh 


-- REMEMBER: in types, parentheses implicitly "stack" to the right:
#check ℕ → bool → ℤ → string       -- this ... 
#check ℕ → (bool → (ℤ → string))   -- ... means this!


-- REMEMBER: in function applications, parentheses implicitly "stack" to the left:
#eval fgh 34 tt (-1)             -- this ... 
#eval ((fgh 34) tt) (-1)         -- ... means this! 





-- note: LEAN accepts this definition (although it probably shouldn't):
-- def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 
def h2 (x : nat) (b : bool) : int :=  if (b) then x else -x 
/-
the difference with h is that here we say "if (b)" instead of "if (b = tt)". 

we don't like the definition of h2 because it uses implicit "casting" (also called _coercion_) of bool b into a Prop. we will talk later about the difference between bool and Prop. for now, we want to stick to the pattern "(b = tt)", "(b = ff)", etc., in if-then-else conditions.  
-/


-- here's a function with 3 arguments:
def add3 (x : nat) (y : nat) (z : nat) : nat := x+y+z 
#check add3 

-- another (equivalent) way to define add3:
def add3alt (x y z : nat) : nat := x+y+z 
#check add3alt 

#check ℕ → (ℕ → (ℕ → ℕ))    
#check ℕ → ℕ → ℕ → ℕ      

#check add3 10 100 1000   
#check ((add3 10) 100) 1000   


-----------------------------------------------------------------
-- PATTERN MATCHING
-----------------------------------------------------------------

-- we've defined this function above:
-- def f (x : nat) : nat := x + 1 

-- here's another way to define the same function:
def fpat : nat -> nat -- we start by giving the type/contract
    | x := x + 1    -- then we define the function by "pattern matching"
-- in this case pattern matching is trivial: we basically say
-- "let the input be x" (| x), "then the output is x+1" (:= x+1)

#eval fpat 10 
#check fpat 


-- recall g: 
-- def g (x y : nat) : nat := x+y 
-- let's redefine g by pattern matching:
def gpat : nat -> ( nat -> nat )   
        | x y := x+y 
#eval gpat 4 3 
#check gpat 


-- recall h:
-- def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 
-- we can also redefine h by pattern matching:
def hpat : nat -> bool -> int 
        | x y := if (y = tt) then x else -x 
        -- does it matter that the second input is called "y" here instead of "b" above? no. 

#check hpat 
#eval hpat 4 tt 
#eval hpat 4 ff 

/-
the above pattern matching examples are simple because there's only one pattern so there's not a lot of "matching" to be done. we will see more interesting pattern matching next. an example is below: we can rewrite hpat by getting rid of the if-then-else and replacing it with two cases, one where the bool argument is tt, and the other when it is ff:
-/

def hpat' : nat -> bool -> int 
    | x tt := x 
    | x ff := -x 


-----------------------------------------------------------------
-- RECURSION
-----------------------------------------------------------------

-- all the functions we defined so far are pretty simple, in the sense that they do not make use of perhaps the most powerful mechanism in programming: repetition. in imperative programming (C, Java, etc) repetition is achieved mainly using loops, like "while" and "for". in functional programming, it is achieved by _recursion_: a function calling itself. you have already seen recursive functions in your earlier courses. let us now look at how these are defined in LEAN:

-- here's a function that computes the sum 0+1+...+n for given nat n:
def sumall : ℕ → ℕ 
    | 0 := 0
    | (n+1) := (n+1) + (sumall n) -- recursive call


/-
this is a more interesting case of pattern matching, with two cases instead of one. what this is saying is the following:
    - if the input is 0 ("| 0") then output 0 (":= 0")
    - otherwise, if the input is n+1, then output (n+1) + (sumall n)
-/

#eval sumall 0 
#eval sumall 1 
#eval sumall 2 
#eval sumall 4 
#check sumall 


-- now, we might be tempted to define the same function without using pattern matching:
def sumall2 (n : ℕ) : ℕ := if (n = 0) then 0 else n + (sumall2 (n-1)) -- we see error "unknown identifier 'sumall2'"
-- what's going on? aren't the two definitions equivalent? in a sense yes, they are. but LEAN only accepts recursive definitions using the pattern-matching way of defining them. for non-recursive definitions, we can use both pattern-matching and ":=", but for recursive definitions, we must use pattern-matching. 


-----------------------------------------------------------------
-- A WORD ABOUT TERMINATION 
-----------------------------------------------------------------
-- maybe we can "cheat" LEAN into accepting this definition:
def sumall3 : ℕ → ℕ 
    | n := if (n = 0) then 0 else n + (sumall3 (n-1)) 

/- 
why doesn't LEAN accept this? we used pattern-matching, so what's the problem? well, the problem is that even though this definition uses patter-matching, it is really the same as the one for sumall2. and the problem with both these definitions is that they are not "obviously terminating". we will have a lot more to say about termination later in the course. it's one of the main topics of this course. 

for now, compare the definition of sumall3 with that of sumall. you will see that sumall is more "obviously terminating" than sumall3. first, because sumall's pattern-matching contains explicitly the base case n = 0. in sumall3, this is not the case: LEAN has to infer that from the structure of the if-then-else. this is too complicated for LEAN to do (as we will learn later, this is in fact an undecidable problem in general, so generally impossible to solve by an algorithm). 

second, sumall goes from (n+1) to n in the recursive call, whereas sumall3 goes from n to (n-1). now this might not look like a big difference, but as we will see later, it is. (n+1) is the same as (nat.succ n) which refers to the constructor for nats (we'll see what this is later). whereas (n-1) refers to the subtraction function for nats. what if n is 0? then n-1 is also 0, so nothing decreases here. 

to make a long story short, in your recursive definitions, use pattern-matching and break the definition into multiple cases, starting from the simple, base cases, with no recursive calls, and then adding cases with recursive calls, where at least one argument to the recursive call is getting "smaller" (like n is smaller than (n+1) in the definition of exponent above). 
-/


-- for the same reasons explained above, LEAN does not accept the definition below:
def sumall4 : ℕ → ℕ 
    | 0 := 0
    | x := x + (sumall4 (x-1)) 



-- _can we define non-terminating functions in LEAN?_ no we cannot. there are good reasons why we don't allow this, which we will explain later. for now, notice that this is not accepted:
def nonterminating : ℕ → ℕ 
    | 0 := 1 
    | (n+1) := n + (nonterminating (n+1))



-- is this terminating? 
def sumall5 : int -> int  
  | 0 := 0
  | n := n + (sumall5 (n-1)) 


/-

question: _what if i define a function which is obviously terminating to me, but LEAN does not accept it? will i lose points in the homeworks? in the exams?_ 

answer: we expect you to give us valid LEAN code (without errors) unless we explicitly ask for something that has errors (for exercise purposes). if you think that your function is terminating, but LEAN cannot figure it out, you can _transform_ your function into a terminating function using the trick that we will show you below. then, your code should be free of errors. if indeed your (original, prior to transformation) function is terminating, you will not lose points. if your function is not terminating, you will lose points. 

this transformation also allows you to continue your work, and to be able to call this function from other functions, etc. 
-/
