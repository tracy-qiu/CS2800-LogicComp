-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


import .ourlibrary16


--------------------------
-- PROVING TERMINATION
--------------------------

/- 
most programs are written to terminate. (most, but not all: many programs implement so-called _reactive systems_ which are meant to pretty-much run forever, or almost forever, e.g., car/airplane/robot controllers, web sites, etc. but even these reactive programs contain non-reactive parts which perform short-term computations which must terminate).

but checking program termination is not obvious. in fact, checking program termination is the prototypical _undecidable_ computation proble. this is the famous _undecidability theorem of the halting problem for Turing machines_ by the father of computer science, Alan Turing. we saw a simple proof of this amazing result in class (see terminator.pdf posted on canvas). 

even though checking termination is undecidable in general, that doesn't mean we cannot develop techniques to prove termination. in fact, there are many such techniques. some are automated, although they cannot always give a definite answer (they might keep working forever or answer "I don't know"). in this course, we will see one way to prove termination, using so-called "measure functions". 

we start with an example: 
-/


----------------------
-- MEASURE FUNCTIONS
----------------------

/-
what is a measure function for app?

def app : list ℕ → list ℕ → list ℕ 
  | [] L := L
  | (x :: L1) L2 := x :: (app L1 L2)

-/

def m_app : list ℕ → list ℕ → ℕ := fun L1 L2, len L1 

/-
To show that m_app is a valid measure function for app we have to show that it decreases on every recursive call of app, under the conditions that led to that call.

app has just one recursive call, so we have to show:
-/
theorem m_app_decreases: forall (L1 L2 : list ℕ) (x : ℕ),
  ltb (m_app L1 L2) (m_app (x :: L1) L2) = tt 
:= begin
  -- COMPLETE THE PROOF AT HOME! 
end


