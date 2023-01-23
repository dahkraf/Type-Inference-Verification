import .base_language

/-
## Exercise 1
Represent the typing judgment Γ ⊢ e : A as an inductively defined proposition.
-/
inductive typed : ctx → exp → ty → Prop
| Var_typed (Γ : ctx) (x : string) (A : ty)
            (p : ctx_lookup x Γ = option.some A) : typed Γ (exp.EVar x) A
-- Lamda expression:
| Lam_typed (Γ : ctx) (x : string) (A B : ty) (e : exp) -- ℚ: Does Lam require the output type B to match up with the declared type B? Does it even need the declared type?
            (p : typed (ctx.ctx_snoc Γ x A) e B) : typed Γ (exp.ELam x A e) (ty.TFun A B) -- ℚ: How can the new context Γ₂ := ctx.ctx_snoc Γ x A be placed as an argument to declutter the proposition p?
-- Recursive function:
| Rec_typed (Γ : ctx) (f x : string) (A B : ty) (e : exp)
            (p : typed (ctx.ctx_snoc (ctx.ctx_snoc Γ x A) f (ty.TFun A B)) e B) : typed Γ (exp.ERec f x A B e) (ty.TFun A B)
-- Function application:
| App_typed (Γ : ctx) (e1 e2 : exp) (A B : ty)
            (p₁ : typed Γ e1 (ty.TFun A B))
            (p₂ : typed Γ e2 A) : typed Γ (exp.EApp e1 e2) B
-- Boolean literal have type TBool in any context:
| True_typed (Γ : ctx) : typed Γ (exp.ETrue) ty.TBool
| False_typed (Γ : ctx) : typed Γ (exp.EFalse) ty.TBool
-- If-expression:
| EIf_typed (Γ : ctx) (e1 e2 e3 : exp) (A : ty)
            (p₁ : typed Γ e1 ty.TBool)
            (p₂ : typed Γ e2 A)
            (p₃ : typed Γ e3 A) : typed Γ (exp.EIf e1 e2 e3) A
-- Natural numbers have type TNat in any context:
| Zero_typed (Γ : ctx) : typed Γ (exp.Ezero) ty.TNat
| Succ_typed (Γ : ctx) : typed Γ (exp.ESucc) (ty.TFun ty.TNat ty.TNat)
| Pred_typed (Γ : ctx) : typed Γ (exp.EPred) (ty.TFun ty.TNat ty.TNat)
-- Is-zero:
| IsZero_typed (Γ : ctx) : typed Γ (exp.EIsZero) (ty.TFun ty.TNat ty.TBool)
-- Pairing:
-- | Pair_typed (Γ : ctx) (A B : ty) : typed Γ (exp.EPair) (ty.TFun A (ty.TFun B (ty.TProd A B))) -- Is using TFun's necessary to have partial application of EPair?
-- | Fst_typed (Γ : ctx) (A B : ty) : typed Γ (exp.EFst) (ty.TFun (ty.TProd A B) A)
-- | Snd_typed (Γ : ctx) (A B : ty) : typed Γ (exp.ESnd) (ty.TFun (ty.TProd A B) B)
-------------
