-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

-- CS 2800 Fall 2022, HOMEWORK 3


/-
This homework is done in groups. Same logistic instructions as in the last homework apply.

Replace "..." below with the names of the people in your group.

Names of ALL group members: Erica Sammarco, Tracy Qiu, Anushka Mantri
-/

/-
Technical instructions: same as in the last homework BUT NOTICE THAT WE REQUEST TESTING BY _example:_ AT SEVERAL PLACES IN THIS HOMEWORK! 
-/




/- HWK03-01:
Define the function "orb" which implements boolean _disjunction_, i.e. boolean OR (result is tt when either of the two arguments is tt, or both are tt). 
Prove the correctness of your function by exhaustive testing using "example:" and "refl"! 
-/
-- ANSWER:
def orb : bool → bool → bool 
  | tt _ := tt
  | ff b := b

example: orb tt tt = tt := begin refl, end 
example: orb tt ff = tt := begin refl, end 
example: orb ff tt = tt := begin refl, end 
example: orb ff ff = ff := begin refl, end 




/- HWK03-02:
Define the function "xorb" which implements boolean _exclusive or_, XOR (result is tt when exactly one of the two arguments is tt, but not both). Then:
    1. Prove the correctness of your function by exhaustive testing using "example:" and "refl"! 
    2. Write as a formal specification in LEAN the property "(xorb x x) is always false for any boolean x"
    3. Prove the property in 2. by exhaustive testing, using "example:" and "refl". 
-/
-- ANSWER:
def xorb : bool → bool → bool 
  | tt x := not (x)
  | ff x := x



-- 1. 
example: xorb tt tt = ff := begin refl, end 
example: xorb tt ff = tt := begin refl, end 
example: xorb ff tt = tt := begin refl, end 
example: xorb ff ff = ff := begin refl, end  

-- 2. 
#check  ∀ x : bool, (xorb x x) = ff

-- 3. 
example: xorb tt tt = ff := begin refl, end 
example: xorb ff ff = ff := begin refl, end  

example: ∀ x : bool, xorb x x = ff := 
begin 
intro,
cases x,
{
  refl,
},
{
  refl,
}
end 



/- HWK03-03:
Define a _ternary_ logical OR function, called or3b. The function takes as input 3 booleans, and returns tt (true) if any of the three are tt, and ff (false) otherwise. Define this function explicitly, by listing all possible cases (truth table method). (If you want to merge multiple cases into one using "_" or variables, that's OK, but overlapping cases are not allowed!).
-/
-- ANSWER:
def or3b  : bool → bool → bool → bool 
  | ff ff ff := ff
  | ff ff tt := tt
  | ff tt ff := tt
  | ff tt tt := tt
  | tt ff ff := tt
  | tt ff tt := tt
  | tt tt ff := tt
  | tt tt tt := tt


/- HWK03-04-1:
Define a function lenmul4 which takes as input a list of nats and returns bool tt if the list's length is a multiple of 4, and bool ff otherwise. An empty list has length 0, which is a multiple of 4: 0*4=4. Define the function directly using pattern matching and recursion, without using any previously defined length-of-list function (not even the len function we defined in class), nor the "modulo" function. 
-/
-- ANSWER:
def lenmul4 : list ℕ → bool
  | [] := tt
  | (a :: []) := ff
  | (b :: (a :: [])) := ff
  | (c :: (b :: (a :: []))) := ff
  | (d :: (c :: (b :: (a :: L)))) := lenmul4 L



/- HWK03-04-2:
Use "example" and "refl" to test your function on the above inputs (all tests below must pass!):
-/
-- DO NOT DELETE:
example: lenmul4 [] = tt := begin refl, end
example: lenmul4 [1] = ff := begin refl, end
example: lenmul4 [1,2] = ff := begin refl, end
example: lenmul4 [1,2,3] = ff := begin refl, end
example: lenmul4 [1,2,3,4] = tt := begin refl, end
example: lenmul4 [1,2,3,4,5,6,7,8,9] = ff := begin refl, end
example: lenmul4 [1,2,3,4,5,6,7,8,9,10,11,12] = tt := begin refl, end


/- HWK03-05:
Define the function list_delete which takes a list of nats L, and an index i which is a nat, and deletes the i-th element of L.  We index L starting from 0, so that if L=[1,2,3], then (list_delete L 0) should return [2,3], (list_delete L 1) should return [1,3], etc. If L is empty, then the result is empty. If i is "out of bounds" then the output list should be the same as the input list.  So (list_delete [1,2,3] 3) should return [1,2,3]. All tests given below must pass! 
-/
-- ANSWER:
def list_delete : list ℕ → ℕ → list ℕ 
  | [] _ := []
  | (x :: L) 0 := L 
  | (x :: L) (i + 1) := (x :: (list_delete L i))

-- DO NOT DELETE:
example: list_delete [] 0 = [] := begin refl, end 
example: list_delete [] 10 = [] := begin refl, end 
example: list_delete [] 100 = [] := begin refl, end 
example: list_delete [1,2,3] 0 = [2,3] := begin refl, end 
example: list_delete [1,2,3] 1 = [1,3] := begin refl, end 
example: list_delete [1,2,3] 2 = [1,2] := begin refl, end 
example: list_delete [1,2,3] 3 = [1,2,3] := begin refl, end 
example: list_delete [1,2,3] 3000 = [1,2,3] := begin refl, end 


/- HWK03-06:
Define the function "rl" which takes a list of nats L and a nat n, and rotates L to the left n times. For example, 
    rl [1,2,3] 1    should return [2,3,1]
    rl [1,2,3] 2    should return [3,1,2]
and so on. Note that n can be 0. Rotating a list 0 times means doing nothing to the list. Note that n can also be greater than the length of the list, in which case we "keep rotating" the list until n becomes 0. Examples are provided for you below. These are tests. Your function definition must pass those tests. Passing those tests means that "refl" is able to prove the example-theorem. 

HINT: use a helper function, in particular, one of the functions we defined in HOMEWORK 02. In general, you can always use helper functions, either those that we defined already in class, or in previous homeworks, or in the current homework. 

What's a "helper function"? A helper function is just another function, a "subroutine" if you want, which is called by the "main" program/function. The helper function takes care of part of the problem, so that the main function can focus on other parts and not get too complicated. The main function can call several helper functions. Helper functions can themselves call other helper functions, and so on. 
-/
-- ANSWER:
def app: list ℕ → list ℕ → list ℕ 
  | [] l := l
  | (x :: L) l := x :: app L l

def rl : list ℕ → ℕ → list ℕ 
  | L 0 := L
  | [] (n + 1) := []
  | (x :: L) (n + 1) := rl (app L [x]) n

#check rl 

-- DO NOT DELETE:
example : rl [1,2,3] 0 = [1,2,3] := begin refl end
example : rl [1,2,3] 1 = [2,3,1] := begin refl end
example : rl [1,2,3] 2 = [3,1,2] := begin refl end
example : rl [1,2,3] 3 = [1,2,3] := begin refl end
example : rl [1,2,3] 30 = [1,2,3] := begin refl end
example : rl [] 13 = [] := begin refl end
example : rl [1] 130 = [1] := begin refl end



/- HWK03-07:
In a previous homework we asked you to define the function 
    apply : list ℕ → (ℕ → ℕ) → list ℕ 
-/
def apply : list ℕ → (ℕ → ℕ) → list ℕ 
    | [] _ := []
    | (x :: L) f := (f x) :: (apply L f)

/- HWK03-07-1:
Test apply (using "example") three times on the list [1,2,3] and with f being the following three functions: (1) the function that doubles its argument, (2) the function that squares its argument, (3) the function that bounds its argument to be at most 2. Do not first define these three functions and then pass them to apply. Instead, pass each of them directly as an anonymous function (lambda abstraction). 
-/
-- ANSWER:
example: apply [1,2,3] (fun n, (n * 2)) = [2, 4, 6] := begin refl, end 
example: apply [1,2,3] (fun n, (n * n)) = [1, 4, 9] := begin refl, end 
example: apply [1,2,3] (fun n, (ite (n <= 2) n 2)) = [1, 2, 2] := begin refl, end  


/- HWK03-07-2:
Use apply to turn all the elements of the input list to zeroes. That is, complete the "..." in the examples below with the appropriate anonymous function such that the example-theorems hold.
NOTE: the anonymous function must be the same in all examples below. 
-/
example: apply [1,2,3] (fun n, 0) = [0,0,0] := begin refl, end 
example: apply [21,2,3,3] (fun n, 0) = [0,0,0,0] := begin refl, end 
example: apply [1,2,3,4,5,6,7] (fun n, 0) = [0,0,0,0,0,0,0] := begin refl, end 




/- HWK03-08-1:
Define the function "curry" which takes as input a function f and returns as output a function g, such that:
- f takes as input a _pair_ of nats (x,y) and returns a nat f(x,y)
- g takes as input two nats x and y, and returns as output a nat which is the same as f(x,y).
-/
-- ANSWER:
def curry (f : (ℕ × ℕ → ℕ)) : (ℕ → ℕ → ℕ) := (fun (x : ℕ) (y : ℕ), f (x, y))

/- HWK03-08-2:
Check that your function "curry" is correct on the following example:
-/
def addpair : ℕ × ℕ → ℕ
  | (x,y) := x + y

def add2 : ℕ → ℕ → ℕ 
  | x y := x + y 

-- make sure your definition of curry passes the test below:
example: (curry addpair) 1 2 = add2 1 2 := begin refl, end 





/- HWK03-09-1:
define an inductive data type "btn" which represents a binary tree of nats. in particular, we want to:

define an inductive data type called "btn" which represents a binary tree whose leaves and internal nodes contain natural numbers. you can think about this type as defined by the following rules: (a) a natural number is such a tree (a leaf); (b) if i have two such trees, t1 and t2, and a natural number x, i can build a new tree t, whose left branch is t1 and whose right branch is t2, and which contains x at its root node. based on these two rules, your inductive type bton should have two constructors, called "bton.leaf" and "bton.node". 

-/
-- ANSWER:
inductive btn : Type 
  | leaf : ℕ → btn 
  | node : ℕ → btn → btn → btn


/- HWK03-09-2:
use #check to construct a few trees of type btn, and make sure they are of type btn. 
-/
-- ANSWER:
#check btn.leaf 5
#check btn.node 5 (btn.leaf 5) (btn.leaf 10)

#check (btn.node 1 (btn.node 10 (btn.leaf 15) (btn.leaf 20)) (btn.node 15 (btn.leaf 25) (btn.leaf 30)))

#check (btn.node 2 (btn.node 3 (btn.leaf 5) (btn.leaf 10)) (btn.leaf 5))


/- HWK03-09-3:
Define the function btn2natlist which takes a btn and returns a list of nats containing all the nats appearing in all nodes of the tree (including both leaves and internal nodes).

The order in which the nats appear in the list does not matter, but all the nats must appear in the list exactly the same number of times as they appear in the tree. 

Evaluate your function on the tests given below: you must find which arguments to pass to your function so that all tests pass! note: there could be different trees that all result in the same list. we don't care which of those you pass to your function, as long as it returns the right list. 
-/
-- ANSWER:

open btn
def btn2natlist : btn → list ℕ 
  | (leaf x) := [x]
  | (node x t1 t2) := x :: (app (btn2natlist t1) (btn2natlist t2))

#check btn2natlist


example: btn2natlist (leaf 10) = [10] := begin refl, end 
example: btn2natlist (node 0 (leaf 1) (leaf 2)) = [0,1,2] := begin refl, end 
example: btn2natlist (node 0 (node 0 (leaf 1) (leaf 2)) (leaf 2)) = [0,0,1,2,2] := begin refl, end 
example: btn2natlist (node 0 (node 1 (leaf 0) (leaf 1)) (leaf 2)) = [0,1,0,1,2] := begin refl, end 

/- HWK03-09-4:
Define the function btnleaves2natlist which takes a btn and returns a list of nats containing all the nats appearing in all _leaves_ of the tree (only the leaves).

The order in which the nats appear in the list does not matter, but all the nats must appear in the list exactly the same number of times as they appear in the leaves of the tree. 

Evaluate your function on the tests given below: you must find which arguments to pass to your function so that all tests pass! note: there could be different trees that all result in the same list. we don't care which of those you pass to your function, as long as it returns the right list. 
-/
-- ANSWER:
def btnleaves2natlist : btn → list ℕ 
  | (leaf x) := [x]
  | (node x t1 t2) := app (btnleaves2natlist t1) (btnleaves2natlist t2)

#check btn2natlist 

example: btnleaves2natlist (leaf 10) = [10] := begin refl, end 
example: btnleaves2natlist (node 0 (leaf 1) (leaf 2)) = [1,2] := begin refl, end 
example: btnleaves2natlist (node 0 (node 0 (leaf 1) (leaf 2)) (leaf 2)) = [1,2,2] := begin refl, end 
example: btnleaves2natlist (node 13 (node 9 (leaf 0) (leaf 0)) (node 7 (leaf 0) (leaf 0))) = [0,0,0,0] := begin refl, end 

/- HWK03-09-5:
Define the function btnnodes2natlist which takes a btn and returns a list of nats containing all the nats appearing in all _internal nodes_ of the tree (not the leaves).

The order in which the nats appear in the list does not matter, but all the nats must appear in the list exactly the same number of times as they appear in the internal nodes of the tree. 

Evaluate your function on the tests given below: you must find which arguments to pass to your function so that all tests pass! note: there could be different trees that all result in the same list. we don't care which of those you pass to your function, as long as it returns the right list. 
-/
-- ANSWER:
def btnnodes2natlist : btn → list ℕ 
  | (leaf x) := []
  | (node x t1 t2) := x :: (app (btnnodes2natlist t1) (btnnodes2natlist t2))

example: btnnodes2natlist (node 10 (leaf 0) (leaf 0)) = [10] := begin refl, end 
example: btnnodes2natlist (node 1 (leaf 0) (node 2 (leaf 0) (leaf 0))) = [1,2] := begin refl, end 
example: btnnodes2natlist (node 0 (leaf 9) (node 0 (leaf 8) (node 0 (leaf 7) (leaf 7)))) = [0,0,0] := begin refl, end 
example: btnnodes2natlist (node 0 (leaf 9) (node 0 (leaf 8) (node 0 (node 0 (leaf 7) (leaf 7)) (leaf 7)))) = [0,0,0,0] := begin refl, end 




-- consider the inductive data type mynat that we also defined in class:
inductive mynat : Type   
    | Z : mynat 
    | S : mynat → mynat 

open mynat -- leave this line here so you can type Z and S instead of mynat.Z and mynat.S 

/- HWK03-10:
Define the function "myeven" which takes a mynat x and returns a bool, tt if x is even, ff if x is odd. "even" and "odd" are defined on mynat just like on nat: Z is even, (S Z) is odd, S (S Z) is even, etc. 
All tests below must pass!
-/
-- ANSWER:
def myeven : mynat → bool 
  | Z := tt
  | (S Z) := ff
  | (S (S x)) := myeven x

-- DO NOT DELETE:
example: myeven Z = tt := begin refl, end 
example: myeven (S Z) = ff := begin refl, end 
example: myeven (S (S (S Z))) = ff := begin refl, end 
example: myeven (S (S (S (S Z)))) = tt := begin refl, end 


/- HWK03-11:
Define the function "myodd" which takes a mynat x and returns a bool, tt if x is odd (i.e., not even), ff if x is not odd (i.e., it is even). Do NOT use recursion to define myodd. You can define a "helper function" on bools, or just copy one that we have already defined in class. 
All tests below must pass!
-/
-- ANSWER:
def myodd (n: mynat) : bool := ¬ (myeven n)

-- DO NOT DELETE:
example: myodd Z = ff := begin refl, end 
example: myodd (S Z) = tt := begin refl, end 
example: myodd (S (S (S Z))) = tt := begin refl, end 
example: myodd (S (S (S (S Z)))) = ff := begin refl, end 


/- HWK03-12:
Define two versions of the function "minustwo" which takes a mynat x and returns the mynat "x-2", bounded by zero. that is, minustwo Z should be Z, minustwo (S Z) should be also Z, etc. the tests below provide more examples. complete the proofs of these _example:_. make sure all these tests pass. 

Define _two_ versions of minustwo, called _minustwo1_ and _minustwo2_. they should be equivalent in terms of input-output behavior, but should differ in the way they are defined: define _minustwo1_ without any use of helper functions, simply by pattern matching on mynat. define _minustwo2_ by defining and calling a helper function _decr_ which decrements a mynat by one, bounded by zero of course. 
-/
-- ANSWER:

-- decrement by two, direct definition:
def minustwo1 : mynat → mynat 
  | Z := Z
  | (S Z) := Z
  | (S (S x)) := x 

-- decrement by one, bounded by zero:
def decr : mynat → mynat 
  | Z := Z
  | (S Z) := Z
  | (S (S x)) := (S x)

-- decrement by two, definition in terms of decr:
def minustwo2 (x : mynat) : mynat := (decr (decr x)) 



-- DO NOT DELETE:
example: minustwo1 Z = Z := begin refl, end  
example: minustwo1 (S Z) = Z := begin refl, end  
example: minustwo1 (S (S Z)) = Z := begin refl, end  
example: minustwo1 (S (S (S Z))) = S Z := begin refl, end  
example: minustwo1 (S (S (S (S Z)))) = S (S Z) := begin refl, end  


-- DO NOT DELETE:
example: minustwo2 Z = Z := begin refl, end  
example: minustwo2 (S Z) = Z := begin refl, end  
example: minustwo2 (S (S Z)) = Z := begin refl, end  
example: minustwo2 (S (S (S Z))) = S Z := begin refl, end  
example: minustwo2 (S (S (S (S Z)))) = S (S Z) := begin refl, end  



theorem minustwo1_equiv_minustwo2:  ∀ x : mynat, minustwo1 x = minustwo2 x 
:= begin sorry, end 


/- HWK03-13-1:

define multiplication on mynats. that is, define a function

 mymult : mynat → mynat → mynat 

which takes two mynats and returns their product, as a mynat. 

make sure your function passes all the tests given below. 

your definition of mymult is allowed to use myplus (addition on mynats) as a helper function. 
-/

def myplus: mynat -> mynat -> mynat 
  | mynat.Z y := y 
  | (S x) y := S (myplus x y)

def mymult : mynat → mynat → mynat 
  | Z y := Z
  | (S Z) y := y
  | (S (S x)) y := (myplus y (myplus y (mymult x y)))

-- TESTS: DO NOT REMOVE!
-- 2*0 = 0
example: mymult (S (S Z)) Z = Z := begin refl, end 
-- 2*1 = 2
example: mymult (S (S Z)) (S Z) =  (S (S Z)) := begin refl, end 
-- 2*2 = 4
example: mymult (S (S Z)) (S (S Z)) = (S (S (S (S Z)))) := begin refl, end 
-- 0*3 = 0
example: mymult Z (S (S (S Z))) = Z := begin refl, end 
-- 1*3 = 3
example: mymult (S Z) (S (S (S Z))) = (S (S (S Z))) := begin refl, end 


/- HWK03-13-2:

because mynats are unreadable and untypable, redefine multiplication on nats. that is, define a function

 mult : nat → nat → nat 

which takes two nats and returns their product, as a nat. hint: do the same thing you did in mymult, but using the nat constructors instead of the mynat constructors. 

make sure your function passes all the tests given below. 

your definition of mult is allowed to use plus (addition on nats that we defined in class) as a helper function, but it is NOT allowed to use predefined LEAN functions like +, *, etc. 
-/
-- ANSWER:

def plus : nat -> nat -> nat 
  | nat.zero y := y
  | (nat.succ x) y := nat.succ (plus x y)  

def mult : ℕ → ℕ → ℕ 
  | nat.zero y := nat.zero
  | (nat.succ nat.zero) y := y
  | (nat.succ (nat.succ x)) y := (plus y (plus y (mult x y))) 

-- TESTS: DO NOT REMOVE!
example: mult 0 3 = 0 := begin refl, end 
example: mult 1 3 = 3 := begin refl, end 
example: mult 2 3 = 6 := begin refl, end 
example: mult 7 0 = 0 := begin refl, end 
example: mult 7 1 = 7 := begin refl, end 
example: mult 7 2 = 14 := begin refl, end 
example: mult 111 3 = 333 := begin refl, end 





/- HWK03-14:

for each of the types given below, define a function that has exactly that type. any function with the given type is OK. we don't care what the function returns, or how it's written, as long as it returns the right type. however, we _do_ want all arguments to be used somehow (we don't care how). for example, if you are given the type bool → ℕ, here's a couple of correct answers:
-/
def f1 (b : bool) : ℕ := if (b = tt) then 0 else 1 
def f2 : bool → ℕ 
    | tt := 42
    | ff := 10 

-- and here's a couple of incorrect answers:
def f3 (b : bool) (x : ℕ) := if (b = tt) then x else 2*x -- wrong type
def f4 (b : bool) : ℕ := 42    -- b is not used 

/-
here's the requested types:

A. (nat -> int) -> (nat -> int)
B. nat -> int -> nat -> int
C. nat -> (int -> nat) -> bool
D. nat -> (int -> nat) -> int -> bool 
E. bool -> (nat -> (int -> nat) -> int)

call your functions fA, fB, fC, fD, and fE, respectively. 
-/
-- ANSWER:
def fA (a : ℕ → int) : (ℕ → int) := a

#check (nat -> int) -> (nat -> int)
#check fA 

def fB (a: ℕ) (b: int) (c: ℕ) : int := a + b + c 

#check nat -> int -> nat -> int 
#check fB 

def fC (a: ℕ) (f: int → ℕ) : bool := (f 10) > a 

#check nat -> (int -> nat) -> bool  
#check fC 

def fD (a: ℕ) (f: int → ℕ) (c: int) : bool := (f c) > a

#check nat -> (int -> nat) -> int -> bool 
#check fD  

def fE (a: bool) (b: ℕ) (f: int → ℕ) : int := ite (a ∧ (b > (f 10))) 5 10

#check bool -> (nat -> (int -> nat) -> int)
#check fE 



/- HWK03-15-1:

define the inductive data type myint, of integers, using the following two constructors:

nat2int : ℕ → myint   
nat2negint : ℕ → myint

nat2int takes a nat x and returns the same x but now of type myint. thus, (myint.nat2int 0) is the myint 0, (myint.nat2int 1) is the myint 1, etc. 

nat2negint takes a nat x and returns (-x-1) of type myint. thus, (myint.nat2negint 0) is the myint -1, (myint.nat2negint 1) is the myint -2, etc. 
-/

inductive myint : Type   
  | nat2int : ℕ → myint 
  | nat2negint : ℕ → myint  

#check (myint.nat2int 0)
#check (myint.nat2negint 0) 


/- HWK03-15-2:
define the function myabs : myint → ℕ which takes a myint x and returns the absolute value of x as a nat. all tests below must pass! 
-/ 

open myint
def myabs: myint → ℕ 
  | (nat2int x) := x
  | (nat2negint x) := x + 1


-- DO NOT DELETE:
example: myabs (myint.nat2int 10) = 10 := begin refl, end 
example: myabs (myint.nat2int 0) = 0 := begin refl, end 
example: myabs (myint.nat2negint 0) = 1 := begin refl, end 
example: myabs (myint.nat2negint 10) = 11 := begin refl, end 



