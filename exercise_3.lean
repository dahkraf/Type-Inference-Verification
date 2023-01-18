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

variables (Γ : ctx) (f_eq_nat x y : string) -- ℚ: Why does it fail when using "constants" keyword?

def eq_nat : exp :=
  exp.ERec
    f_eq_nat
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
                        (exp.EVar f_eq_nat)
                        (exp.EApp exp.EPred (exp.EVar x)) -- x := x - 1
                    ) -- eq_nat(x) : ℕ → ℕ
                    (exp.EApp exp.EPred (exp.EVar y)) -- y := y - 1
                )
            )
        )
    )
-- Write down the typing judgment as a lemma in Lean and prove it.
lemma l_eq_nat : -- ℚ: Does it need to only prove the typing judgement or also that the function actually compares for equality?
  typed Γ (eq_nat f_eq_nat x y) (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) := sorry

------------