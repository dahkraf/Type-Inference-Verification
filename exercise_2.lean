import .base_language .typing_rules

/-
## Exercise 2
Translate the following typing judgments into lemmas in Lean and prove them.
-/

constants (Γ : ctx) (f x : string)

-- ⊢ (λ(x : ℕ). x) : ℕ → ℕ
lemma l₁ : typed Γ (exp.ELam x ty.TNat (exp.EVar x)) (ty.TFun ty.TNat ty.TNat) :=
  typed.Lam_typed
    Γ
    x
    ty.TNat
    ty.TNat -- ℚ: Can these arguments be set to TNat directly or need to be inferred somehow?
    (exp.EVar x)
    (
      typed.Var_typed -- ?
        (ctx.ctx_snoc Γ x ty.TNat)
        x
        ty.TNat
        sorry -- ?
    )
-- ⊢ (λ(x : ℕ). is_zero) : ℕ → ℕ → Bool
lemma l₂ : typed Γ (exp.ELam x ty.TNat (exp.EIsZero)) (ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)) :=
  typed.Lam_typed
    Γ
    x
    ty.TNat
    (ty.TFun ty.TNat ty.TBool)
    (exp.EIsZero)
    (
      typed.IsZero_typed
        Γ
    )
-- ⊢ (rec f (x : ℕ) : ℕ := if (is_zero x) then 0 else (succ (succ (f (pred x))))) : ℕ → ℕ
lemma l₃ :
  typed Γ
  (
    exp.ERec
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
  ) 
  (ty.TFun ty.TNat ty.TNat):=
  typed.Rec_typed
    Γ
    f
    x
    ty.TNat
    ty.TNat
    sorry -- How to seperate the expression in the lemma into a def? Lean complains in that case.
    sorry
    
------------