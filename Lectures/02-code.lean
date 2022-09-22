-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-----------------------------------------------------------------
-- FUNCTIONAL PROGRAMMING WITH TYPES, IN LEAN, CONTINUED
-----------------------------------------------------------------

-----------------------------------------------------------------
-- RECURSION CONTINUED
-----------------------------------------------------------------

def sumall : ℕ → ℕ 
    | 0 := 0
    | (n+1) := (n+1) + (sumall n) -- recursive call


def sumall2 (n : ℕ) : ℕ := if (n = 0) then 0 else n + (sumall2 (n-1)) -- doesn't work: must use pattern matching to define recursive functions!

def sumall3 : ℕ → ℕ 
    | n := if (n = 0) then 0 else n + (sumall3 (n-1))   -- doesn't work: LEAN cannot prove termination!

def sumall4 : ℕ → ℕ 
    | 0 := 0
    | x := x + (sumall4 (x-1)) -- doesn't work: LEAN cannot prove termination! 



-- _can we define non-terminating functions in LEAN?_ no we cannot. there are good reasons why we don't allow this, which we will explain later. for now, notice that this is not accepted:
def nonterminating : ℕ → ℕ 
    | 0 := 1 
    | (n+1) := n + (nonterminating (n+1))




/-

question: _what if i define a function which is obviously terminating to me, but LEAN does not accept it? will i lose points in the homeworks? in the exams?_ 

answer: we expect you to give us valid LEAN code (without errors) unless we explicitly ask for something that has errors (for exercise purposes). if you think that your function is terminating, but LEAN cannot figure it out, you can _transform_ your function into a terminating function using the trick that we will show you below. then, your code should be free of errors. if indeed your (original, prior to transformation) function is terminating, you will not lose points. if your function is not terminating, you will lose points. 

this transformation also allows you to continue your work, and to be able to call this function from other functions, etc. 
-/




------------------------------------------------------------------------------------------
-- TRANSFORMING A NON-TERMINATING FUNCTION INTO A TERMINATING ONE SO THAT LEAN ACCEPTS IT
------------------------------------------------------------------------------------------

/- we will transform the function _nonterminating_ above so that it terminates. the idea is to add a _bound_ as an extra argument (a nat). the caller of the function is now forced to provide a bound on the max no. recursive calls: 
-/

def nonterminatingbounded : ℕ → ℕ → ℕ   -- the bound is the 2nd argument
    | 0 _ := 1 -- the first case of the original function is not recursive, so we leave it as it was (the _ means "i don't care what the value of the second argument is")
    | (n+1) 0 := 42  -- when the second argument (the bound) reaches 0, we MUST terminate. we can choose to return anything we want (something that makes sense for the function we are trying to define). here we chose 42 ... 
    | (n+1) (bound+1) := n + (nonterminatingbounded (n+1) bound)   -- at every recursive call, bound decreases by 1, so termination is guaranteed and "obvious" for LEAN to figure out

#eval nonterminatingbounded 10 10




---------------------------------------------------
-- EXPONENT
---------------------------------------------------

#eval 2^10
#eval 2^0 
#eval 0^10 
#eval 0^0   -- interesting case! 


-- in some of your LEAN installations, the exponent operation x^n is not predefined. 
-- let's define this function ourselves:

def exponent : nat -> nat -> nat 
  | x 0 := 1 
  | x (e+1) := x * (exponent x e)

#eval exponent 2 10 
#eval exponent 0 10 
#eval exponent 10 0 
#eval exponent 0 0 




-- notice that in the first case of the pattern-matching: "| x 0 := 1", we don't use the "x" anywhere in the result. in such a case, we can leave this argument anonymous, or "un-named":
def exponent_ : ℕ → ℕ → ℕ 
    | _ 0 := 1
    | x (n+1) := x * (exponent_ x n)
#eval exponent_ 2 10
#eval exponent_ 2 100
#eval exponent_ 2 1000 
#eval exponent_ 0 0  





---------------------------------------------------
-- MORE ON PATTERN MATCHING
---------------------------------------------------

-- sometimes LEAN doesn't complain about overlapping cases that give different results:
def badchoice : ℕ → ℕ 
    | 0 := 0
    | 1 := 1
    | 2 := 2
    | (x+1) := badchoice x  -- this overlaps with case "1" if x=0 and with case "2" if x=1 

#eval badchoice 0
#eval badchoice 1
#eval badchoice 2
#eval badchoice 3
#eval badchoice 4
-- in this class we will insist on _not_ having overlapping cases. try to define your functions such as cases are mutually-exclusive (i.e., non-overlapping) and complete, in order to avoid any ambiguities. here's for example one way to fix the above:
    
def goodchoice : ℕ → ℕ 
    | 0 := 0
    | 1 := 1
    | 2 := 2
    | (x+3) := goodchoice (x+2)  -- no overlap with any of the base cases

#eval goodchoice 0
#eval goodchoice 1
#eval goodchoice 2
#eval goodchoice 3
#eval goodchoice 4

/-
note that there are limits to the pattern matching that LEAN allows. 
for example, we might be tempted to try this:
-/

def even : ℕ → bool    -- a function that checks whether a given nat is even or odd 
    | (2*n) := tt       -- if the input is of the form 2*n then it's even
    | (2*n+1) := ff     -- if the input is of the form 2*n+1 then it's odd 

-- writing it this way doesn't help either:
def evenbis : ℕ → bool    
    | (n*2) := tt       
    | (n*2+1) := ff     

/-
the reason why the above don't work will become more clear when we explain inductive data types. let us get a glimpse of that right away: 
-/



-----------------------------------------------------------------
-- A BRIEF PREVIEW OF INDUCTIVE DATA TYPES 
-----------------------------------------------------------------

-- we will see how to define our own so-called inductive data types later, and we will also (re)define natural numbers and functions on those. 
-- as a preview, we can see how natural numbers are already defined in LEAN:
#check nat 
#print nat -- this says that natural numbers can be "constructed" in two ways:
/-  
- nat.zero is a (constructor that returns a) natural number
- nat.succ is a constructor that takes a natural number, and returns a new natural number 
-/
#check nat.zero  -- 0 is shorthand notation for nat.zero 
#check nat.succ nat.zero -- 1 is shorthand for )nat.succ nat.zero)
#check nat.succ (nat.succ nat.zero) -- and so on 


-- nat.succ is the same as the "+1". so when we write (n+1) in our recursive case definitions, what we really mean is (nat.succ n):

def sumallagain : ℕ → ℕ 
    | 0 := 0
    | (nat.succ n) := (n+1) + (sumallagain n) 

/- 
this hopefully makes it clearer why LEAN finds it easy to accept that the above definition is terminating. you can think of LEAN as "reasoning" like this:
  - i know what to return in the base case where the input is the simplest possible natural number, namely nat.zero
  - if the input is a natural number other than nat.zero, then it can only be of the form (nat.succ n), because that's the only other constructor for natural numbers
  - so in that second case, i have to call myself recursively with n instead of (nat.succ n) as the second argument
  - since n is a strictly "smaller" / "simpler" natural number than (nat.succ n), eventually i will "hit" the simplest natural number, which is nat.zero, so eventually the process will terminate. 
-/

def exponentagain : ℕ → ℕ → ℕ  
    | x nat.zero  := 1
    | x (nat.succ n) := x * (exponentagain x n) 


#check exponent 2 

#eval exponent 2 10 
#eval exponent 0 0   -- note that this is different from how we defined exponent in 04-code.lean. WHY?


-- and what we really say when we define goodchoice is this:
def goodchoicebis : ℕ → ℕ 
    | nat.zero := 0
    | (nat.succ nat.zero) := 1
    | (nat.succ (nat.succ nat.zero)) := 2
    | (nat.succ (nat.succ (nat.succ x))) := goodchoicebis x  




/-
this hopefully also makes it clear why (2*n) and (2*n+1) are not acceptable patterns by LEAN. LEAN has no way to "deconstruct" a nat m into 2*n or 2*n+1, although it is easy to "deconstruct" m into either 0 (i.e., nat.zero) or (n+1) (i.e., nat.succ n). 
-/





-----------------------------------------------------------------
-- RECURSION ON LISTS
-----------------------------------------------------------------

-- let's look at another example of recursion, this time on lists:
def len : list ℕ → ℕ 
    | [] := 0
    | (a :: L) := 1 + (len L)
#eval len [] 
#eval len [1,2,3]
#eval len [1,1,1]


/- the above definition of len can be read as follows, line by line:
def len : list ℕ → ℕ          READ: len is a function that takes a list of nat and returns a nat
    | [] := 0                  READ: if the input list is empty, return 0
    | (a :: L) := 1 + (len L)  READ: if the input list is of the form (a :: L) then return 1+(len L)
-/


-- again, since we are not using "a" in the pattern above, we can omit it and replace it with "_":
def len2 : list ℕ → ℕ 
        | [] := 0
        | (_ :: L) := 1 + len2 L 
#eval len2 [1,2,3] 

#print nat 
#print list -- takes two arguments 

#eval 0 :: [] 
#eval 0 :: (1 :: []) -- equivalent to line below 
#eval list.cons 0 (list.cons 1 list.nil) 
#eval [1,2,3,4,5,6,7]

-- the type "list ℕ" can be seen as denoting "a list whose elements are all natural numbers"
#check list ℕ 
#check list string
#check [1,2,3]
#check ["hi","bye"]
-- [] denotes the empty list (the list with no elements, and length 0)
-- [] is actually notation for list.nil:
#check list.nil -- ignore "?M_1" for now, it means the empty list is polymorphic

-- [1,2,3] is also notation for this:
#check list.cons 1 (list.cons 2 (list.cons 3 []))
-- arguably, [1,2,3] is much easier to write, but it's good to know where it comes from:
#check list 
#print list -- ignore the weird Π ... for now 
-- another equivalent notation is this:
#check 1 :: (2 :: (3 :: []))  -- so "::" is infix notation for list.cons 


-- just like with pattern matching on nats, pattern matching on lists is also based on the inductive data type definition of lists. so what we really wrote when we defined len above is this:
def lenbis : list ℕ → ℕ 
    | list.nil := 0
    | (list.cons a L) := 1 + (lenbis L)


def len3 : list nat -> nat 
  | list.nil := 0 
  | (list.cons _ L) := 1 + (len3 L) 


def mylen : list nat -> nat 
  | [] := 0 
  | [x] := 1 
  | (x :: (y :: L)) := 2 + (mylen L) 

#eval mylen [1,2,3]
#eval mylen [1,2,3,4,4,5,6] 



def mylen2 : list nat -> nat 
  | list.nil := 0 
  | (x :: []) := 1 
  | (x :: (y :: L)) := 2 + (mylen2 L) 



def mylen3 : list nat -> nat 
  | list.nil := 0 
  | (list.cons x list.nil) := 1 
  | (x :: (y :: L)) := 2 + (mylen3 L) 




/- CONCLUSIONS (FOR NOW) ABOUT DEFINING RECURSIVE FUNCTIONS:

again, we will talk more about termination later in the course. for now, just stick to this recipe for defining recursive functions over nats and lists of nats:

RECIPE:
1. use the pattern matching style
2. for recursion on nats, use 0 as the base case, and (x+1), (n+1), (x+2), etc, for recursive cases
3. for recursion on lists, use [] as the base case, and (x :: L), (x :: (y :: L)), etc, for recursive cases
4. if you need more than one base cases, that's OK, e.g., you can use 0 and 1 as two distinct base cases
5. (if you follow steps 1-4 above, you should not need to use this 5th option) if LEAN complains about termination, but you believe that your function is terminating, use the bounding transformation described above 

this recipe should be pretty much the same as the "data-driven definitions" style you learned in fundies 1?
-/


-----------------------------------------------------------------
-- ANONYMOUS FUNCTIONS - LAMBDAS
-----------------------------------------------------------------

-- in all the examples so far, every function that we defined has
-- a name, like f, f13, f15, etc:
def f (x : nat) : nat := x+1
def f13 (x) := x+1 
def f15 : nat -> nat
    | x := x + 1

-- then we can call the function as follows:
#eval f 0
#eval f13 0
#eval (f (f13 0))
#eval (f (f13 11) + (f15 7))
-- "calling a function" is also called "function application".
-- we "apply" the function to a given argument. for example,
-- in (f 0) we apply f to 0. in (f (f13 0)) we apply f to (f13 0),
-- and we also apply f13 to 0. etc. 

-- it is often useful to be able to define functions without names, "anonymous functions" so to speak. why would we ever want to do that? this is useful, for example, when treating functions as "first-class citizens". for example, we might want to pass a function as an argument to another function. or a function might return a function as a result. we will see several examples of this later in this course. 
-- functions without names can be defined using "fun" or (unicode) λ (\lambda). you may encounter this under the term "lambda abstraction":
#eval (fun x : ℕ, x+1) 0 -- "(fun x, x+1)" is the unamed/anonymous function that takes x as input and returns x+1 as output. NOTE: we didn't have to define anything, we just went ahead and evaluated this anonymous function applied to 0.  
#check (fun x : ℕ, x+1) -- we can check the type of an anonymous function
#eval (fun x, x+1) 0 -- sometimes we can omit types (but we don't want to do that in this course)
#check (fun x, x+1)  -- same as above: λ (x : ℕ), x + 1 : ℕ → ℕ 
#eval (fun (x:ℕ), (x+1 : ℕ)) 0 -- here we specify the types of both input and output, the latter seems a bit redundant in this case
#check (fun (x:ℕ), (x+1 : ℕ)) -- same as above: λ (x : ℕ), x + 1 : ℕ → ℕ
#eval (λ (x:ℕ), (x+1 : ℕ)) 17 -- "fun" can be replaced by λ 
#check λ (x:ℕ), x+1

#check (fun x : nat, x+1) -- doesnt explicity say the output type but x+1 inferred as nat outpy type 
#eval (fun x : nat, x+1) 0 
#eval f 0 
#eval (λ x : nat, x+1) (2+3) 



-----------------------------------------------------------------
-- FUNCTIONS ARE FIRST-CLASS CITIZENS
-----------------------------------------------------------------

-- functions in LEAN are not different from other objects. just like we can pass to a function a number, say 0 or 1, or a bool, say tt, we can pass a function, provided that this is allowed by the input-output contract. let us illustrate this by example.
-- here's a function g which takes as input a nat x and a function f : nat -> nat and returns as output (f x):
def gg (x : ℕ) (f : ℕ → ℕ) : ℕ := f x 
#check gg 

#eval gg 10 f -- f is the function we defined earlier
#eval gg 3 f 

#eval gg 10 (fun x : nat, x+3) 
#eval gg 10 (λ x, x+3) -- here we pass an unamed function as input to gg 

#eval gg 10 f15 

-- what is the type of gg? let's ask LEAN:
#check gg -- LEAN says "gg : ℕ → (ℕ → ℕ) → ℕ", which means that gg takes something of type ℕ, and something of type "(ℕ → ℕ)", and returns something of type ℕ. this is as we would expect. the second input to gg, of type "(ℕ → ℕ)" (the parentheses aren't needed here), is a function that takes a nat and returns a nat. gg can be called with any function that has this type, for example:

#eval gg 10 (exponent 2)  -- here we see an example of "partial evaluation". remember the function exponent that we defined above? what is its type?
#check exponent 
#eval exponent 2 10 

-- we cannot pass "exponent" to gg, because "exponent" doesn't have the required type, ℕ → ℕ. indeed, if we try, we get a type error:
#eval gg 10 exponent -- type error

-- but we can pass "(exponent 2)". why? what is the type of "(exponent 2)"?
#check exponent 2 -- (exponent 2) is a function! it takes a nat n, and returns 2^n, another nat. 

#eval (gg 10) (exponent 2) 




-- which of these three types are the same?
#check nat -> bool -> nat 
#check nat -> (bool -> nat) 
#check (nat -> bool) -> nat
-- ANSWER: the first two types are the same, but the third one is different

-- can we find some functions that have the above types?


def h (f : nat -> bool) : nat :=
  if f 0 = tt then
    0
  else
    1
#check h 




-----------------------------------------------------------------
-- TYPES ARE FIRST-CLASS CITIZENS TOO
-----------------------------------------------------------------

-- g is a function that takes as input some type x and returns as output the same type x 
def g (x : Type) : Type := x 
#check g 
#check g nat 
#eval g nat  -- doesn't work, just like "#eval nat" doesn't work 
#reduce g nat 
#reduce g (list nat) 
#reduce g (nat -> bool)

def GH (x: Type) : Type := x -> x 
#reduce GH bool 

/-
again, we will not delve much into type theory. for more info, see the lecture notes or https://leanprover.github.io/theorem_proving_in_lean/dependent_type_theory.html

-/

-- can we find some functions that have the above types?

/-

A. (nat -> int) -> (nat -> int) --> lean drops last two paraentheses (nat -> int) -> nat -> int
B. nat -> int -> nat -> int 
D. nat -> (int -> nat) -> int -> bool 

-/

def fA (f: ℕ -> ℤ) : ℕ -> ℤ := f
def fA' (f: ℕ -> ℤ) (x : ℕ) : ℤ := f x 

#check fA
#check fA'

def fB: ℕ ℤ ℕ := ℤ 

#check fB


