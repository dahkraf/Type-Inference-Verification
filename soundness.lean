import .base_language .typing_rules .type_inferencer

/-
# Exercise 7 (1)
Prove soundness of your type checker.
-/

lemma sound_in_non_empty_ctx (Γ : ctx) (x : string) (e : exp) (A B : ty) : type_infer (ctx.ctx_snoc Γ x B) e = option.some A → typed (ctx.ctx_snoc Γ x B) e A :=
  λ e_inf : type_infer (ctx.ctx_snoc Γ x B) e = option.some A,
    begin
      cases e,
        {
          apply typed.Var_typed,
          unfold type_infer at e_inf,
          exact e_inf -- cc works as well. Of course, it bloody does
        },
        {
          -- ELam
          sorry
        },
        {
          -- ERec
          sorry
        },
        {
          -- EApp
          sorry
        },
        {
          -- ETrue
          cases A,
          {
            unfold type_infer at e_inf,
            cc -- How to show falsity for all other non-boolean cases
          },
          {
            apply typed.True_typed
          },
          {
            unfold type_infer at e_inf,
            cc
          },
          {
            unfold type_infer at e_inf,
            cc
          }
        },
        {
          -- EFalse
          cases A,
          {
            unfold type_infer at e_inf,
            cc -- How to show falsity for all other non-boolean cases
          },
          {
            apply typed.False_typed
          },
          {
            unfold type_infer at e_inf,
            cc
          },
          {
            unfold type_infer at e_inf,
            cc
          }
        },
        {
          -- EIf
          sorry
        },
        {sorry},
        {sorry},
        {sorry},
        {sorry},
        {
          -- EPair
          sorry
        },
        {
          -- Fst
          sorry
        },
        {
          -- Snd
          sorry
        }
    end


lemma sound_in_empty_ctx (e : exp) (A : ty) : type_infer (ctx.ctx_nil) e = option.some A → typed (ctx.ctx_nil) e A :=
  λ e_inf : type_infer (ctx.ctx_nil) e = option.some A,
    begin
      cases e,
      {
        -- EVar
        apply typed.Var_typed,
        unfold type_infer at e_inf,
        unfold ctx_lookup at e_inf,
        cc -- Need to generate falsity to ex falso quodlibet it (Woah... cc is magic)
      },
      {
        -- ELam
        sorry
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
          unfold type_infer at e_inf,
          cc -- How to show falsity for all other non-boolean cases
        },
        {
          apply typed.True_typed
        },
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          unfold type_infer at e_inf,
          cc
        }
      },
      {
        -- EFalse
        cases A,
        {
          unfold type_infer at e_inf,
          cc -- How to show falsity for all other non-boolean cases
        },
        {
          apply typed.False_typed
        },
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          unfold type_infer at e_inf,
          cc
        }
      },
      {sorry},
      {
        -- EZero
        cases A,
        {
          apply typed.Zero_typed
        },
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          unfold type_infer at e_inf,
          cc
        }
      },
      {
        -- ESucc
        cases A,
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          cases A_ᾰ,
          {
            cases A_ᾰ_1,
            {
              apply typed.Succ_typed
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          }
        },
        {
          unfold type_infer at e_inf,
          cc
        }
      },
      {
        -- EPred
        cases A,
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          cases A_ᾰ,
          {
            cases A_ᾰ_1,
            {
              apply typed.Pred_typed
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          }
        },
        {
          unfold type_infer at e_inf,
          cc
        }
      },
      {
        -- EIsZero
        cases A,
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          unfold type_infer at e_inf,
          cc
        },
        {
          {
          cases A_ᾰ,
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              apply typed.IsZero_typed
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          },
          {
            cases A_ᾰ_1,
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            },
            {
              unfold type_infer at e_inf,
              cc
            }
          }
        }
        },
        {
          unfold type_infer at e_inf,
          cc
        }
      },
      {
        -- EPair
        sorry
      },
      {
        -- Fst
        sorry
      },
      {
        -- Snd
        sorry
      }
    end

lemma type_infer_sound (Γ : ctx) (e : exp) (A : ty) : type_infer Γ e = option.some A → typed Γ e A :=
  begin
    cases Γ,
    { exact (sound_in_empty_ctx e A) },
    { exact (sound_in_non_empty_ctx Γ_Γ Γ_x e A Γ_A) }
  end
  