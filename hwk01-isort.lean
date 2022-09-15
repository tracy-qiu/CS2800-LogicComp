-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


/-

Your first proof assignment! Insertion sort is a simple sorting method. Consider the implementation of insertion sort in LEAN below. Prove, using any method of your choice, that this implementation is correct. You have to do three things:
    (1) State clearly what you mean by "correct". 
    (2) Prove correctness.
    (3) Check whether your definition of "correct" is "complete".     If it is, then buggy implementations should not satisfy your definition of "correct". Provide at least two buggy implementations and argue why they are buggy and where they fail your proof. 

This assignment in intentionally open-ended. The goal is to make you think what a "proof" is. We are not expecting you to write proofs in LEAN, although if you want to try, please do! We are also not necessarily expecting mathematical proofs. Ultimately, a proof is an argument that tries to convince somebody about something. Try to convince yourself that this code is correct. Try to convince us as well. At the end of the semester, you can go back and compare the formal proofs (including of insertion sort!) that we will have done by then, to the answers you gave in this first assignment. Then you will appreciate better what a formal proof is.

However, we do expect some reasonable amount of thought in your answers. We will cut points for generic answers like this:
"A "correct" implementation of an algorithm will always produce correct, expected solutions for valid input instances of the problem."

Provide a single PDF file with your answers. 

This assignment is individual (one answer per student, no groups).

-/

def insrt : ℕ → list ℕ → list ℕ
-- insrt is a function that takes as input a natural number (i.e., of type ℕ),
-- and a list of natural numbers, and returns as output a list of natural numbers
  | x [] := [x] -- if the input number is x and the input list is empty,
                -- then return the list [x] (that contains just the number x)
  | x (y :: L) := if (x ≤ y) -- if the input list has head y and tail L, and x <= y
                  then x :: (y :: L) -- then return the list [x, y, elements of L]
                  else y :: (insrt x L) -- else return the list with head y and tail 
                                        -- the list that (insrt x L) returns

#eval insrt 1 [1,2,3]
#eval insrt 10 [1,2,3]
#eval insrt 10 [1, 2, 30]
#eval insrt 10 [100,50,0,20]


def isort : list ℕ → list ℕ
-- isort is a function that takes a list of nats and returns a list of nats
  | [] := []  -- if the input list is empty, return the empty list
  | (x :: L) := insrt x (isort L) -- otherwise, sort the tail L, and then insert the head x in the sorted tail

#eval isort [2,1,4,1,3,5,1,2] -- move cursor here to see result
#eval isort [3,1,3,4,5,1,1,0,2,3,4,2,3,6,3,45,3,0,4,5,1,3,4]

example: isort [3,1,3,4,5,1,1,0,2,3,4,2,3,6,3,45,3,0,4,5,1,3,4] =
[0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 6, 45]
:= begin refl, end



/- 
1) A "correct" implementation of an algorithm will produce the expected correct answers to the problem, holding true for all base and edge cases. 
A correct implementation of an algorithm will hold true for all cases and can be proven for the base case and for all k+1 cases. 

2) This algorithm is correct and can be proven by proof by induction 
The base case of this algorithm covered in which there is only one element and a one element array is sorted. 
We can assume that the first n-1 elements are sorted after n-1 iterations of insertion sort because each iteration.
It can be seen as a subarray in which the elements are sorted which begins as empty. 
Elements are then added to it and placed in the correct index using insertionto find the index where the element above is greater than or equal to and the one below is less than or equal to.

3) insrtBuggy1 implementation does not have a base case for inserting into an empty array so that algorithm does not produce the expected output and is not correct. 
It also fails in the case where the element being inserted is greater than all the elements in the array because after it is done comparing to all the elements and is left with no elements left to compare with it has nowhere to insert. 
insrtBuggy2 implementation is not a correct implementation because it holds true for some cases such as the base case and a case when all the elements in the array already begins in decreasing order but fails in all other cases.
This shows how it can hold true and produce the expected value in some cases but not in all cases which does not satisfy my definition of "correctness".
-/

def insrtBuggy1 : ℕ → list ℕ → list ℕ
-- insrt is a function that takes as input a natural number (i.e., of type ℕ),
-- and a list of natural numbers, and returns as output a list of natural numbers
  | x (y :: L) := if (x ≤ y) -- if the input list has head y and tail L, and x <= y
                  then x :: (y :: L) -- then return the list [x, y, elements of L]
                  else y :: (insrtBuggy1 x L) -- else return the list with head y and tail 
                                        -- the list that (insrt x L) returns

#eval insrtBuggy1 1 [1,2,3]
#eval insrtBuggy1 10 [1,2,3]
#eval insrtBuggy1 50 [1, 2, 30]
#eval insrtBuggy1 10 [1, 2, 30]
#eval insrtBuggy1 10 [100,50,0,20]
#eval insrtBuggy1 1 []


def isortBuggy1 : list ℕ → list ℕ
  | [] := []  -- if the input list is empty, return the empty list
-- isort is a function that takes a list of nats and returns a list of nats
  | (x :: L) := insrtBuggy1 x (isortBuggy1 L) -- otherwise, sort the tail L, and then insert the head x in the sorted tail

#eval isortBuggy1 [2,1,4,1,3,5,1,2] -- move cursor here to see result
#eval isortBuggy1 [3,1,3,4,5,1,1,0,2,3,4,2,3,6,3,45,3,0,4,5,1,3,4]
#eval isortBuggy1 []


def insrtBuggy2 : ℕ → list ℕ → list ℕ
-- insrt is a function that takes as input a natural number (i.e., of type ℕ),
-- and a list of natural numbers, and returns as output a list of natural numbers
  | x [] := [x] -- if the input number is x and the input list is empty,
                -- then return the list [x] (that contains just the number x)
  | x (y :: L) := if (x ≤ y) -- if the input list has head y and tail L, and x <= y
                  then x :: (insrtBuggy2 y L)  -- then return the list [y, x, elements of L]
                  else y :: (x :: L) -- else return the list with head x and tail 
                                        -- the list that (insrt y L) returns

#eval insrtBuggy2 1 [1,2,3]
#eval insrtBuggy2 10 [1,2,3]
#eval insrtBuggy2 10 [1, 2, 30]
#eval insrtBuggy2 10 [100,50,0,20]
#eval insrtBuggy2 10 [1,10,0,20]


def isortBuggy2 : list ℕ → list ℕ
-- isort is a function that takes a list of nats and returns a list of nats
  | [] := []  -- if the input list is empty, return the empty list
  | (x :: L) := insrtBuggy2 x (isortBuggy2 L) -- otherwise, sort the tail L, and then insert the head x in the sorted tail

#eval isortBuggy2 [2,1,4,1,3,5,1,2] -- move cursor here to see result
#eval isortBuggy2 [3,1,3,4,5,1,1,0,2,3,4,2,3,6,3,45,3,0,4,5,1,3,4]
#eval isortBuggy2 [1,2,3,4,5]