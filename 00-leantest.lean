-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


-- move your cursor at the end of each line and observe what happens
-- in the window to the right called "Lean Infoview"

#check bool  -- you should see in the Lean Infoview window something like: "bool : Type"

#check nat   --  you should see: "ℕ : Type"   

#check ℕ -- type "\nat" to get ℕ 

#check ℕ → ℤ  -- "\to" to get → 



#eval 3+5    -- you should see: 8

#eval 2*33

#eval tt && ff 


-- this is a comment   

/-

multiple line comment

multiple line comment

-/

/-

NOTE: there's an annoying bug that makes some blue squiggly/wavy lines appear underlining comments like this one. this is caused by bad interaction between the version of Lean and the version of the VS Code extension of Lean. it can be fixed by installing an earlier version of the VS Code extension, e.g., 0.16.46, as we saw in class. 
-/


def f (x : nat) : nat := x+1
#check f              

#eval f 2

-- #eval f [1,2]   -- if you uncomment this, you should get an error 

example: f 5 = 6 := 
begin
--    dunfold f,
    refl,
end

theorem f_2_equals_3: f 2 = 3 := 
begin 
    refl, 
end 

example: f 2 = 3 := begin refl, end 

theorem f_nonnegative: forall x : nat, f x >= 0 :=
begin
    intro,
    simp [f],
    apply nat.zero_le, 
    -- move your cursor here, you should see "goals accomplished"
end

theorem f_strictly_positive: forall x : nat, f x > 0 :=
begin
    intro,
    simp [f],
    sorry, -- "goals accomplished" but the theorem is not proven!
end



def ff (n : nat) : int := n-1
#eval ff 0
example: ff 3 = 2 := begin refl, end 
theorem f_positive_nonnegative:
    forall x, x > 0 -> ff x >= 0 :=
begin
    sorry,
end

#eval lean.version 
