import .base_language .typing_rules

/-
# Exercise 3
Write a function of type ℕ → ℕ → Bool that checks if two natural numbers are equal.
-/

/-
Function "eq_nat" in the object language:
eq_nat : ℕ → ℕ → Bool
eq_nat := λ (x : ℕ),
            λ (y : ℕ),
              if (x == 0)
              then
                if (y == 0)
                then "true"
                else "false"
              else
                if (y == 0)
                then "false"
                else eq_nat (pred x) (pred y)
-/

variables (Γ : ctx)

def f : string := "f"
def x : string := "x"
def y : string := "y"

def eq_nat : exp :=
  exp.ERec
    f
    x
    ty.TNat
    (ty.TFun ty.TNat ty.TBool)
    (
      exp.ELam
        y
        ty.TNat
        (
          exp.EIf
            (exp.EApp exp.EIsZero (exp.EVar x)) -- x == 0
            (
              exp.EIf
                (exp.EApp exp.EIsZero (exp.EVar y)) -- y == 0
                exp.ETrue
                exp.EFalse
            )
            (
              exp.EIf
                (exp.EApp exp.EIsZero (exp.EVar y)) -- y == 0
                exp.EFalse
                (
                  exp.EApp
                    (
                      exp.EApp
                        (exp.EVar f)
                        (exp.EApp exp.EPred (exp.EVar x)) -- x := x - 1
                    ) -- eq_nat(x) : ℕ → ℕ
                    (exp.EApp exp.EPred (exp.EVar y)) -- y := y - 1
                )
            )
        )
    )
-- Write down the typing judgment as a lemma in Lean and prove it.
lemma l_eq_nat :
  typed Γ eq_nat (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) :=
  begin
  apply typed.Rec_typed,
  apply typed.Lam_typed,
  apply typed.EIf_typed,
  { -- x == 0
    apply typed.App_typed,
    {
      apply typed.IsZero_typed
    },
    {
      apply typed.Var_typed,
      unfold ctx_lookup,
      unfold y,
      unfold x,
      rw if_neg,
      unfold f,
      rw if_neg,
      {
        rw if_pos,
        exact rfl
      },
      {
        cc
      },
      {
        cc
      }
    }
  },
  {
    apply typed.EIf_typed,
    {
      apply typed.App_typed,
      {
        apply typed.IsZero_typed
      },
      {
        apply typed.Var_typed,
        unfold ctx_lookup,
        unfold y,
        rw if_pos,
        exact rfl
      }
    },
    {
      apply typed.True_typed
    },
    {
      apply typed.False_typed
    }
  },
  {
    apply typed.EIf_typed,
    { -- y == 0
      apply typed.App_typed,
      apply typed.IsZero_typed,
      apply typed.Var_typed,
      unfold ctx_lookup,
      unfold y,
      rw if_pos,
      exact rfl
    },
    {
      apply typed.False_typed
    },
    {
      apply typed.App_typed,
      {
        apply typed.App_typed,
        apply typed.Var_typed,
        unfold ctx_lookup,
        unfold y,
        unfold f,
        rw if_neg,
        rw if_pos,
        { exact rfl },
        { cc },
        {
          apply typed.App_typed,
          apply typed.Pred_typed,
          apply typed.Var_typed,
          unfold ctx_lookup,
          unfold y,
          unfold x,
          rw if_neg,
          {
            unfold f,
            rw if_neg,
            rw if_pos,
            exact rfl,
            cc
          },
          { cc }
        }
      },
      {
        apply typed.App_typed,
        {
          apply typed.Pred_typed
        },
        {
          apply typed.Var_typed,
          unfold ctx_lookup,
          rw if_pos,
          exact rfl
        }
      }
    }
  }
  end
------------