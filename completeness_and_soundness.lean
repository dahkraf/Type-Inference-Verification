import .base_language .typing_rules .type_inferencer

/-
# Exercise 7
Prove completeness and soundness of your type checker.
-/

lemma type_infer_complete (Γ : ctx) (e : exp) (A : ty) : typed Γ e A → type_infer Γ e = option.some A :=
  λ e_judge : typed Γ e A,
    sorry

lemma type_infer_sound (Γ : ctx) (e : exp) (A : ty) : type_infer Γ e = option.some A → typed Γ e A :=
  λ e_inf : type_infer Γ e = option.some A,
    (
      match e with
      | (exp.EVar x) := typed.Var_typed Γ x A (sorry)
      | _ := sorry
      end
    )
