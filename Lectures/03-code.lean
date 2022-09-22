-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

---------------------------------------------------
-- LOGISTICS
---------------------------------------------------

/-

please form teams on the handins web site !

-/


/-
GENERAL NOTE:
 the lecture code that i post on canvas has sometimes stuff that we didn't get to cover during the lecture. you are supposed to read _everything_ in the lecture code files posted on canvas. if you don't understand something, ask us. 
-/



---------------------------------------------------
-- PRODUCT TYPES AND CURRYING
---------------------------------------------------

-- earlier we saw how functions taking multiple arguments have types of the form A → B → C → ... there's another way to pass multiple arguments to a function, namely by passing pairs, triples, etc. this is like we're used to in math, where we write f(x,y), g(x,y,z), etc. for this, we need to use so-called "product types". we will not deal with such types almost at all, but we illustrate them briefly by example. 

def h (x : nat) (b : bool) : int := if (b = tt) then x else -x 

#check h

#eval h 0 tt 
#eval (h 13 ff) 


-- let's define another version of function h above using a product type and pattern matching:
def hprod : ℕ × bool → int 
    | (x, tt) := x
    | (x, ff) := -x 

#check hprod -- hprod : ℕ × bool → ℤ

#eval hprod (3,tt) 
#eval hprod (3,ff)

-- compare to calling h:
#eval h 3 ff  -- this seems simpler: we don't need parentheses, comma

-- NOTE: h and hprod are NOT the same function. they have different types. 
-- indeed, we cannot call them in the same way:
#eval h (3,tt) -- type error
#eval hprod 3 tt -- type error


-- NOTE: product types and pattern matching are independent concepts. we could very well have defined h using pattern matching also: 
def h2 : ℕ → bool → ℤ 
    | x tt := x 
    | x ff := -x 

#check h2 -- same type as h



/- now let's suppose we wish to define another version of addition that takes a product type:
def addprod : ℕ × ℕ → ℕ 

how can we access the numbers x and y in a given pair (x,y)?

this doesn't work:
-/
def addprodfail ((x,y) : ℕ × ℕ) : ℕ := x+y 

-- we can define it using pattern matching:
def addprodpat : ℕ × ℕ → ℕ 
    | (x,y) := x+y 

---------------------------------------------------
-- .fst and .snd for extracting elements from pairs
---------------------------------------------------

#eval (1,2).fst 
#eval (1,2).snd
#eval (1,2,3).fst
#eval (1,2,3).snd
#eval (1,2,3).snd.fst
#eval (1,2,3).snd.snd

-- we can also define it like this:
def addprod (x : ℕ × ℕ) : ℕ := x.fst + x.snd  

-- as we can see, for programming, pairs and triples seem less convenient than just passing the arguments one after the other. moreover, the latter way allows also for not passing all the arguments, which is useful for partial evaluation (we saw an example of that last week). so, as it turns out, taking a function of type A × B → C and turning into a function of type A → B → C is beneficial as the function becomes more convenient to use. this is called "currying" (not from the Indian dishes, and not from the basketball player, but from Haskell Curry: https://en.wikipedia.org/wiki/Haskell_Curry). 

