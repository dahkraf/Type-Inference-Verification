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
      typed.Var_typed
        (ctx.ctx_snoc Γ x ty.TNat)
        x
        ty.TNat
        (
          let h₁ : ctx_lookup x (Γ.ctx_snoc x ty.TNat) = if x = x then option.some ty.TNat else ctx_lookup x Γ
              := eq.refl _ in
          -- let h_dec : decidable (x = x)
          --     := string.has_decidable_eq x x in
          let h₂ : x = x -- ℚ: How does this compare with having a proposition (x = x) = true instead?
              := eq.refl _ in
          let h₃ : (if x = x then option.some ty.TNat else ctx_lookup x Γ) = option.some ty.TNat
              := by rw [if_pos h₂] in
          eq.trans h₁ h₃
        )
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
        (ctx.ctx_snoc Γ x ty.TNat)
    )
-- ⊢ (rec f (x : ℕ) : ℕ := if (is_zero x) then 0 else (succ (succ (f (pred x))))) : ℕ → ℕ
noncomputable def exp₃ : exp :=
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
def type₃ : ty := ty.TFun ty.TNat ty.TNat
lemma l₃ : typed Γ exp₃ type₃ :=
  typed.Rec_typed
    Γ
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
    (
      typed.EIf_typed
        Γ
        (exp.EApp exp.EIsZero (exp.EVar x))
        (exp.Ezero)
        (
          exp.EApp
            exp.ESucc
            (
              exp.EApp
                exp.ESucc
                (exp.EApp (exp.EVar f) (exp.EApp exp.EPred (exp.EVar x)))
            )
        )
        ty.TNat
        sorry
        (typed.Zero_typed)
        sorry
    )
------------