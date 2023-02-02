import .base_language .typing_rules .type_inferencer

/-
# Exercise 7 (2)
Prove completeness of your type checker.
-/

lemma type_infer_complete (Γ : ctx) (e : exp) (A : ty) : typed Γ e A → type_infer Γ e = option.some A :=
  λ e_judge : typed Γ e A,
    begin
      cases Γ,
      {
        sorry
      },
      {
        sorry
      }
    end

-----