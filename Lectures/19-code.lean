-- CS 2800 LOGIC AND COMPUTATION, FALL 2021
-- COPYRIGHT 2021 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .ourlibrary11 





/-

ANY QUESTIONS ABOUT THE MATERIAL IN 17-code.lean and 18-code.lean?



- how not to lose your bool cases

- the tactic clear 

- notation



-/





----------------------------------------------------
-- FUNCTIONAL INDUCTION 
----------------------------------------------------



/-
functional induction is an extremely cool and powerful technique which builds on our earlier insight that theorems are functions. now we will see that theorems that use induction are really recursive functions! and induction hypotheses correspond to recursive calls of the theorem, with "smaller" arguments!! let's illustrate all that by example:
-/

-- are two natural numbers equal?
def eqb : ℕ → ℕ → bool 
    | 0 0 := tt 
    | 0 (nat.succ y) := ff     
    | (nat.succ x) 0 := ff 
    | (nat.succ x) (nat.succ y) := eqb x y 


-- equality is symmetric -- proof by standard induction, delaying intro of y: 
theorem eqb_sym: ∀ x y : ℕ, eqb x y = eqb y x 
:= begin
    intro, -- we only introduce x!
    induction x with z ih,
    {
        intro, 
        cases y with w,
        refl,
        refl,
    },
    {
        intro, 
        cases y with w, 
        refl, 
        rw eqb,
        rw eqb,
--        rw ih,  -- this also works 
        have h := ih w, 
        assumption,
    }
end



-- proof using _functional induction_ (also called _well-founded induction_):
theorem eqb_sym_funind: ∀ x y : ℕ, eqb x y = eqb y x 
    | 0 0 := begin -- base case, corresponding to the 1st case in the definition of eqb
        refl, 
    end
    | 0 (nat.succ y) := begin -- base case, corresponding to the 2nd case in the definition of eqb
        rw eqb,
        rw eqb,
    end
    | (nat.succ x) 0 := begin -- base case, corresponding to the 3rd case in the definition of eqb
        refl, 
    end  
    | (nat.succ x) (nat.succ y) := begin -- induction step, corresponding to the 4th (and only recursive) case in the definition of eqb. notice the induction hypothesis, which is called "eqb_sym_funind". it not only has the same name as the theorem we are trying to prove, but it looks identical to the theorem itself!!!
        rw eqb,
        rw eqb,
--        rw eqb_sym_w_funind,
        have h := eqb_sym_funind x y,  -- using the induction hypothesis = recursive call to eqb_sym_funind. wow!
        assumption,
    end  
--

/- WOW! THEOREMS WITH PATTERN MATCHING!

functional induction looks cool, with its pattern-matching style. this follows from the fact that theorems are functions (09-code.lean). since we can use pattern-matching to define functions, we can also use pattern-matching to define theorems (recall that we can change "theorem" above to "def" -- try it!). 

in fact, we can prove other theorems with this pattern matching style, even theorems that don't need induction. for example, the proof of the theorem below is like a proof by cases: 
-/

theorem bool_tt_or_ff: ∀ b : bool, b = tt ∨ b = ff 
  | tt := begin
    left,
    refl,
  end
  | ff := begin
    right,
    refl,
  end
--

/- WOW!   INDUCTION = RECURSION!

even more awesomely, functional induction shows us that induction is recursion!  theorems that use induction are recursive functions: the induction hypothesis is a recursive call! 

but when we use recursion we need to be careful about termination. looking at a proof state like this:

eqb_sym_funind : ∀ (x y : ℕ), eqb x y = eqb y x,
x y : ℕ
⊢ eqb x y = eqb y x

we may be a bit shocked. with the assumption

eqb_sym_funind : ∀ (x y : ℕ), eqb x y = eqb y x,

it looks as if LEAN allow us to prove eqb_sym_funind by assuming eqb_sym_funind itself! shouldn't this be illegal? indeed, this is illegal. if it were legal, LEAN's proof system would be unsound! fortunately, LEAN makes sure that we cannot use the induction hypothesis (i.e., make a recursive call to our theorem/function) in any way we want: we can only make a recursive call with "smaller" arguments! in the proof of eqb_sym_funind, we call eqb_sym_funind with x and y, which are both smaller than (nat.succ x) and (nat.succ y) which are in the pattern. this is legal, just like in a recursive call, because the arguments are decreasing.

the way the induction hypothesis is written is a bit misleading, because it looks exactly like the theorem we are trying to prove. but LEAN imposes additional conditions, which makes it impossible to use the induction hypothesis, unless it's done in a sound way. for example, LEAN does not let us do this: 
-/


theorem eqb_sym_funind_illegal: ∀ x y : ℕ, eqb x y = eqb y x
    | x y := begin
        have h := eqb_sym_funind_illegal x y, -- illegal recursive call, arguments don't decrease! 
        assumption, 
    end


/- when you move your cursor to the end of the line with the "have", you see a long error message starting with: "failed to prove recursive application is decreasing, well founded relation". this tells you that you are trying to use the induction hypothesis in an illegal way. in particular, you are trying to prove something about x and y, and you are using as an assumption the same thing about x and y, instead of using it on _smaller_ objects. recall that the induction hypothesis is valid only because it applies to a _smaller_ object than the object we are trying to prove the result on. 

in the case of the proof of "eqb_sym_funind" above, the induction hypothesis is used in a legal manner. we are trying to prove something about the _bigger_ objects (nat.succ x) and (nat.succ y), and we are "calling" the theorem itself on _smaller_ objects x and y. in a nutshell, we are assuming that the property that we want holds on x and y (the smaller objects) and then we are proving that it holds on the bigger objects (nat.succ x) and (nat.succ y). so we are good. 

this also illustrates the need for termination and the strong link between soundness and termination. 
-/


-- so, luckily for soundness, we cannot use functional induction to prove false:
theorem false_funind_attempt: ∀ x : ℕ, false
    | x := begin
        have h := false_funind_attempt x, 
        trivial,
    end





theorem eqb_sym_w_funind_fewer_cases: ∀ x y : ℕ, eqb x y = eqb y x
    -- we can combine the first two cases into a single one:
    | 0 x := begin
        cases x,
        refl,
        refl,
    end
    | (nat.succ x) 0 := begin
        refl,
    end
    | (nat.succ x) (nat.succ y) := begin
        rw eqb,
        rw eqb,
--        rw eqb_sym_w_funind,
        have h := eqb_sym_w_funind_fewer_cases x y,
        assumption,
    end


theorem eqb_sym_w_funind_even_fewer_cases: ∀ x y : ℕ, eqb x y = eqb y x
    -- we can combine the first two cases into a single one:
    | 0 x := begin
        cases x,
        refl,
        refl,
    end
    -- we can also combine the last two cases into a single one:
    | (nat.succ x) y := begin
        cases y with z,
        {
            refl,
        },
        {
            dunfold eqb,
            have h := eqb_sym_w_funind_even_fewer_cases x z,
            assumption,
        }
    end




----------------------------------------------------
-- how powerful is functional induction?  
----------------------------------------------------

/-
how powerful is functional induction?  is it more powerful than standard induction (the one using the "induction" tactic). meaning, are there any theorems that CANNOT be proven with standard induction (and enough lemmas) but that CAN be proven with functional induction?

the answer is no. however, functional induction makes some proofs look extremely easy, whereas the same proof requires some ingenuity to complete with standard induction. let us illustrate this with an example: 
-/


/-
keep odd positions:
-/
def kop : list ℕ → list ℕ 
  | [] := []
  | [x] := [] 
  | (x :: y :: L) := y :: (kop L) 
--

example: kop [] = [] := begin refl, end 
example: kop [1] = [] := begin refl, end 
example: kop [1,2] = [2] := begin refl, end 
example: kop [1,2,3] = [2] := begin refl, end 
example: kop [1,2,3,4] = [2,4] := begin refl, end 
example: kop [0,1,2,3,4] = [1,3] := begin refl, end 
example: kop [0,1,2,3,4,5] = [1,3,5] := begin refl, end 


/-
nat division by two:
-/
def div2 : ℕ → ℕ 
  | 0 := 0 
  | 1 := 0 
  | (nat.succ (nat.succ x)) := nat.succ (div2 x) 
--

example: div2 0 = 0 := begin refl, end 
example: div2 1 = 0 := begin refl, end 
example: div2 2 = 1 := begin refl, end 
example: div2 3 = 1 := begin refl, end 
example: div2 100 = 50 := begin refl, end 
example: div2 101 = 50 := begin refl, end 


/-
practice!!! try to prove this here in class:

  ∀ L : list ℕ, len (kop L) = div2 (len L)

hint: use functional induction. 


CHALLENGE PROBLEM!
try to prove the above claim at home WITHOUT functional induction. 
hint: you will need an awesome lemma! 
-/


-- with functional induction the proof is incredibly simple and uses no lemmas at all!
theorem lenkopfunind: ∀ L : list ℕ, len (kop L) = div2 (len L)
  | [] := begin refl, end 
  | [x] := begin refl, end 
  | (x :: y :: L) := begin
    rw len,
    rw len,
    rw div2,
    rw kop,
    rw len,
    rw lenkopfunind ,
  end
--


