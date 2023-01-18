import .base_language .type_inferencer

/-
# Exercise 6
-/
-- Positive tests:
def legal₁_exp : exp := exp.ELam "x" ty.TNat (exp.EIsZero)
lemma legal₁ : (type_infer ctx.ctx_nil legal₁_exp) = (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) := sorry

-- Negative tests:
def illegal₁_exp : exp := exp.EIf exp.Ezero exp.ETrue exp.EFalse
lemma illegal₁ : (type_infer ctx.ctx_nil illegal₁_exp) = none := sorry