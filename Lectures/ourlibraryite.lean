-- simplifying if-then-else expressions

lemma itetrue (p : Prop) [decidable p] : 
  p → ∀ T : Type, ∀ x y : T, (if p then x else y) = x
:= begin
  intros h T x y,
  simp [h],
end

lemma itefalse (p : Prop) [decidable p] : 
  ¬p → ∀ T : Type, ∀ x y : T, (if p then x else y) = y
:= begin
  intros h T x y,
  simp [h],
end
