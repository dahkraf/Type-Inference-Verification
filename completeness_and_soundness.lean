import .base_language .typing_rules .type_inferencer

/-
# Exercise 7
Prove completeness and soundness of your type checker.
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

lemma type_infer_sound (Γ : ctx) (e : exp) (A : ty) : type_infer Γ e = option.some A → typed Γ e A :=
  λ e_inf : type_infer Γ e = option.some A,
    begin
      cases Γ,
      {
        cases e,
        {
          -- EVar
          apply typed.Var_typed,
          sorry -- Need to generate falsity to ex falso quodlibet it
        },
        {
          -- ELam
          sorry -- Do cases A to make sure it's a function type
        },
        {
          -- ERec
          sorry -- Do cases A to make sure it's a function type
        },
        {
          -- EApp
          sorry
        },
        {
          -- ETrue
          cases A,
          {
            sorry -- How to show falsity for all other non-boolean cases
          },
          {
            apply typed.True_typed
          },
          {
            sorry
          },
          {
            sorry
          }
        },
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
      },
      {
        cases e,
        {
          apply typed.Var_typed,
          sorry
        },
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {sorry}
      }
    end
