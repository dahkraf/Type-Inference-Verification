import .base_language .type_inferencer

/-
# Exercise 6
-/

-- Define some standard contexts:
def f : string := "f"
def x : string := "x"
def Γ₀ : ctx := ctx.ctx_nil
def Γ₁ : ctx := ctx.ctx_snoc Γ₀ x ty.TNat 

-- Positive tests:
def legal₁_exp : exp := exp.ELam x ty.TNat (exp.EIsZero)
lemma legal₁ : (type_infer Γ₀ legal₁_exp) = some (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) :=
  begin
    unfold Γ₀,
    unfold legal₁_exp,
    unfold type_infer,
    unfold bind,
    exact rfl
  end

def legal₂_exp : exp := (exp.ELam x ty.TNat (exp.EVar x))
lemma legal₂ : (type_infer Γ₀ legal₂_exp) = (ty.TFun ty.TNat ty.TNat) :=
  begin
    unfold Γ₀,
    unfold legal₂_exp,
    unfold type_infer,
    unfold bind,
    exact rfl
  end

def legal₃_exp : exp := exp.ERec
      f
      x
      ty.TNat
      ty.TNat
      (
        exp.EIf
          (exp.EApp exp.EIsZero (exp.EVar x))
          exp.Ezero
          (
            exp.EApp
              exp.ESucc
              (
                exp.EApp
                  exp.ESucc
                  (exp.EApp (exp.EVar f) (exp.EApp exp.EPred (exp.EVar x)))
              )
          )
      )
lemma legal₃ : (type_infer Γ₁ legal₃_exp) = ty.TFun ty.TNat ty.TNat :=
  begin
    unfold Γ₁,
    unfold legal₃_exp,
    unfold type_infer,
    unfold bind,
    exact rfl
  end

def legal₄_exp : exp := exp.EApp exp.ESucc exp.Ezero
lemma legal₄ : (type_infer Γ₁ legal₄_exp) = ty.TNat :=
  begin
    exact rfl
  end

-- Negative tests:
-- Illegal test 1 ⇒ if 0 then 'true' else 'false'
def illegal₁_exp : exp := exp.EIf exp.Ezero exp.ETrue exp.EFalse
lemma illegal₁ : (type_infer ctx.ctx_nil illegal₁_exp) = none :=
  begin
    unfold illegal₁_exp,
    unfold type_infer,
    unfold bind,
    exact rfl
  end

def illegal₂_exp : exp := exp.EApp (exp.ELam x ty.TNat exp.ESucc) exp.ETrue
lemma illegal₂ : (type_infer Γ₀ illegal₂_exp) = none :=
  begin
    exact rfl
  end