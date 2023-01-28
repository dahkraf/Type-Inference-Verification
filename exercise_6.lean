import .base_language .type_inferencer

/-
# Exercise 6
-/

-- Define some standard contexts:
def Γ₀ : ctx := ctx.ctx_nil
def Γ₁ : ctx := ctx.ctx_snoc Γ₀ "x" ty.TNat 

-- Positive tests:
def legal₁_exp : exp := exp.ELam "x" ty.TNat (exp.EIsZero)
lemma legal₁ : (type_infer Γ₀ legal₁_exp) = (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) := sorry

def legal₂_exp : exp := exp.ELam "x" ty.TNat (exp.EIsZero)
lemma legal₂ : (type_infer Γ₀ legal₂_exp) = (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) := sorry

def legal₃_exp : exp := sorry
lemma legal₃ : (type_infer Γ₁ legal₃_exp) = sorry := sorry

def legal₄_exp : exp := sorry
lemma legal₄ : (type_infer Γ₁ legal₄_exp) = sorry := sorry

-- Negative tests:
-- Illegal test 1 ⇒ if 0 then 'true' else 'false'
def illegal₁_exp : exp := exp.EIf exp.Ezero exp.ETrue exp.EFalse
lemma illegal₁ : (type_infer ctx.ctx_nil illegal₁_exp) = none :=
  let h₁ : (type_infer ctx.ctx_nil illegal₁_exp) = sorry :=
      sorry in
  sorry

def illegal₂_exp : exp := sorry
lemma illegal₂ : (type_infer Γ₀ illegal₂_exp) = none :=
  let h₁ : (type_infer Γ₀ illegal₂_exp) = sorry :=
      sorry in
  sorry