/-
  # LANGUAGE DEFINITION
-/

-- Define language types:
@[derive decidable_eq] inductive ty : Type -- "derive" tag automatically derives decidable equality
| TNat : ty
| TBool : ty
| TFun : ty → ty → ty
| TProd : ty → ty → ty
-- Define language expressions:
inductive exp : Type
| EVar (x : string) : exp
| ELam (x : string) (A : ty) (e : exp) : exp
| ERec (f x : string) (A B : ty) (e : exp) : exp
| EApp (e1 e2 : exp) : exp
| ETrue : exp
| EFalse : exp
| EIf (e1 e2 e3 : exp) : exp
| Ezero : exp
| ESucc : exp
| EPred : exp
| EIsZero : exp
| EPair (e1 e2 : exp) : exp
| EFst (e : exp) : exp
| ESnd (e : exp) : exp
-- Define language context:
inductive ctx : Type
| ctx_nil : ctx
| ctx_snoc (Γ : ctx) (x : string) (A : ty) : ctx

-- Get the type of variable x in the context:
def ctx_lookup (x : string) : ctx → option ty
| ctx.ctx_nil          := option.none
| (ctx.ctx_snoc Γ y A) := if y = x then option.some A else ctx_lookup Γ

-- Introduce decidability of equality over types "ty": (alternative to @[derive decidable_eq])
/-
  instance decidable_eq_ty : decidable_eq ty :=
    λ (A B : ty),
      match A, B with
      | ty.TNat, ty.TNat := is_true rfl
      | ty.TBool, ty.TBool := is_true rfl
      | (ty.TFun A B), (ty.TFun C D) := sorry
      | (ty.TProd A B), (ty.TProd C D) := sorry
      | x, y := is_false sorry
      end
-/
-------------
