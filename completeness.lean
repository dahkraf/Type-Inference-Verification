import .base_language .typing_rules .type_inferencer

/-
# Exercise 7 (2)
Prove completeness of your type checker.
-/
lemma complete_in_empty_ctx (e : exp) (A : ty) : typed (ctx.ctx_nil) e A → type_infer (ctx.ctx_nil) e = option.some A :=
  λ e_typ : typed ctx.ctx_nil e A,
    begin
      cases e,
      {
        unfold type_infer,
        unfold ctx_lookup,
        cases A,
        {
          sorry
        },
        {
          sorry
        },
        {
          sorry
        },
        {
          sorry
        }
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      }
    end

lemma type_infer_complete (Γ : ctx) (e : exp) (A : ty) : typed Γ e A → type_infer Γ e = option.some A :=
  begin
    cases Γ,
    { exact (complete_in_empty_ctx e A) },
    {
      sorry
    }
  end

-----