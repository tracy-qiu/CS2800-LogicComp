-- CS 2800 LOGIC AND COMPUTATION, FALL 2022
-- COPYRIGHT 2022 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!


lemma deMorgan1: ∀ (p q : Prop), (¬ p ∧ ¬ q) → ¬ (p ∨ q) 
:= begin
-- ANSWER:
-- constructive logic suffices:
  intro,
  intro,
  intro a,
  intro a_1,
  cases a with h1 h2,
  cases a_1,
  {
    have h3 := h1 a_1,
    trivial,
  },
  {
    have h3 := h2 a_1,
    trivial,
  }
end


lemma deMorgan2: ∀ (p q : Prop), (¬ p ∨ ¬ q) → ¬ (p ∧ q) 
:= begin
-- ANSWER:
-- constructive logic suffices:
  intro,
  intro,
  intro a,
  intro a_1,
  cases a_1 with h1 h2,
  cases a,
  {
    have h3 := a h1,
    trivial,
  },
  {
    have h3 := a h2,
    trivial,
  }
end


lemma deMorgan3: ∀ (p q : Prop), ¬ (p ∨ q) → (¬ p ∧ ¬ q) 
:= begin
-- ANSWER:
-- constructive logic suffices:
  intro,
  intro,
  intro h1,
  split,
  {
    intro h2,
    have h3 : p ∨ q := begin left, assumption, end,
    have h4 := h1 h3,
    trivial,
  },
  {
    intro h2,
    have h3 : p ∨ q := begin right, assumption, end,
    have h4 := h1 h3,
    trivial,
  }
end


lemma deMorgan4: ∀ (p q : Prop), ¬ (p ∧ q) → (¬ p ∨ ¬ q) 
:= begin
-- ANSWER:
-- for this last one, we need classical logic: constructive/intuitionistic logic is not enough:
  intro,
  intro,
  intro a,
  cases classical.em p, -- here we use law of excluded middle
  {
    right,
    intro,
    have h1 : p ∧ q := begin
      split,
      assumption,
      assumption,
    end,
    have h2 := a h1,
    trivial,
  },
  {
    left,
    assumption,
  }
end


theorem deMorgan_or: ∀ p q : Prop, ¬ (p ∨ q) ↔ (¬p ∧ ¬q)
:= begin
-- ANSWER:
  intros,
  split,
  {
    have h := deMorgan3 p q,
    assumption,
  },
  {
    have h := deMorgan1 p q,
    assumption,
  }
end


theorem deMorgan_and: ∀ p q : Prop, ¬ (p ∧ q) ↔ (¬p ∨ ¬q) 
:= begin
-- ANSWER:
  intros,
  split,
  {
    have h := deMorgan4 p q,
    assumption,
  },
  {
    have h := deMorgan2 p q,
    assumption,
  }
end




theorem p_implies_q_implies_not_p_or_q: 
    ∀ p q : Prop, (p → q) → (¬p ∨ q) 
:= begin
-- ANSWER:  
-- yes, the -> direction needed classical.em 
    intro,
    intro,
        intro h,
        cases (classical.em p) with h1 h2, 
        {
            right,
            have h1 := h h1,
            assumption,
        },
        {
            left,
            assumption,
        },
end



theorem not_p_or_q_implies_p_implies_q: 
    ∀ p q : Prop, (¬p ∨ q) → (p → q)
:= begin
-- ANSWER:  
-- no, the <- direction did not need classical.em 
    intro,
    intro,
        intro h1,
        intro h2,
        cases h1,
        {
            have h3 := h1 h2,
            trivial,
        },
        {
            assumption,
        },
end

theorem not_p_or_q_iff_p_implies_q: 
    ∀ p q : Prop, (¬p ∨ q) ↔ (p → q)
:= begin
  intros,
  split,
  have h1 := not_p_or_q_implies_p_implies_q p q,
  assumption,
  have h2 := p_implies_q_implies_not_p_or_q p q ,
  assumption,
end



lemma not_not (p : Prop) : p ↔ ¬ ¬ p 
:= iff.intro not_not_intro classical.by_contradiction



theorem and_distrib_or: ∀ A B C : Prop, A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) 
:= begin
    intros,
    split,
    {
        intro a,
        cases a,
        cases a_right,
        {
            left,
            split,
            assumption,
            assumption,
        },
        {
            right,
            split,
            assumption,
            assumption,
        },
    },
    {
        intro a,
        cases a,
        {
            cases a,
            split,
            assumption,
            left,
            assumption,
        },
        {
            cases a,
            split,
            assumption,
            right,
            assumption,
        }
    }
end

theorem or_distrib_and: ∀ A B C : Prop, A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) 
:= begin
    intros,
    split,
    {
        intro a,
        cases a,
        {
            split,
            left, assumption,
            left, assumption,
        },
        {
            cases a,
            split,
            right, assumption,
            right, assumption,
        }
    },
    {
        intro a,
        cases a,
        cases a_left,
        {
            left,
            assumption,
        },
        {
            cases a_right,
            {
                left,
                assumption,
            },
            {
                right,
                split,
                assumption,
                assumption,
            }
        }
    }
end
