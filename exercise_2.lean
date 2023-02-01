import .base_language .typing_rules

/-
## Exercise 2
Translate the following typing judgments into lemmas in Lean and prove them.
-/

constants (Γ : ctx) (A B C: ty)

-- ℚ: How to show f ≠ x ≠ y without explicity definitions?
def f : string := "f"
def x : string := "x"
def y : string := "y"

lemma immediate_context (A : ty) : ctx_lookup x (ctx.ctx_snoc Γ x A) = some A :=
  let h₁ : ctx_lookup x (ctx.ctx_snoc Γ x A) = if x = x then option.some A else ctx_lookup x Γ
      := rfl in
  let h₂ : x = x
      := rfl in
  let h₃ : (if x = x then option.some A else ctx_lookup x Γ) = some A
      := by rw (if_pos h₂) in
  eq.trans h₁ h₃

-- lemma ctx_order_exchangability : (Γ.ctx_snoc x A).ctx_snoc y B = (Γ.ctx_snoc y B).ctx_snoc x A :=
--   sorry

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
              := rfl in
          let h₂ : x = x
              := rfl in
          let h₃ : (if x = x then option.some ty.TNat else ctx_lookup x Γ) = option.some ty.TNat
              := by rw (if_pos h₂) in
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
def exp₃ : exp := -- If f, x, y are defined as constants, without corresponding literal definitions, this definition becomes non-computable.
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
  begin
  apply typed.Rec_typed,
  apply typed.EIf_typed,
  {
    apply typed.App_typed,
    apply typed.IsZero_typed,
    apply typed.Var_typed,
    unfold ctx_lookup,
    unfold f,
    unfold x,
    rw if_neg,
    rw if_pos,
    { exact rfl },
    { cc } -- Shows contradiction (somehow from the LoVe video lectures)
  },
  {
    apply typed.Zero_typed
  },
  {
    apply typed.App_typed,
    {
      apply typed.Succ_typed
    },
    {
      apply typed.App_typed,
      {
        apply typed.Succ_typed
      },
      {
        apply typed.App_typed,
        {
          apply typed.Var_typed,
          unfold ctx_lookup,
          unfold f,
          rw if_pos,
          exact rfl
        },
        {
          apply typed.App_typed,
          {
            apply typed.Pred_typed
          },
          {
            apply typed.Var_typed,
            unfold ctx_lookup,
            unfold f,
            unfold x,
            rw if_neg,
            rw if_pos,
            { exact rfl },
            { cc }
          }
        }
      }
    }
  }
  end
------------