import .base_language

/-
# Exercise 4
Implement a type inferencer.
-/
def type_infer : ctx → exp → option ty :=
  λ Γ : ctx,
    λ e,
      match e with
        | (exp.EVar x) := ctx_lookup x Γ
        -- These cause issues with Lean's recursion termination: -- ℚ: How to fix it if I need recursion to descend the AST?
        -- | (exp.ELam x A e) := bind (type_infer ctx.ctx_nil e) (λ o, ty.TFun A o) -- need monads to wrap/unwrap types inside "option"
        -- | (exp.ERec f x A B e) := bind (type_infer ctx.ctx_nil e) (λ o, ty.TFun A o) -- add a check against declared output type B
        /-
        | (exp.EApp e1 e2) := let input_type := (type_infer ctx.ctx_nil e2) in
                              match (type_infer ctx.ctx_nil e1) with
                              | (some (ty.TFun A B)) := (match input_type with
                                                        | (some T) := if (A = T) then (some B) else none
                                                        | _ := none
                                                        end
                              )
                              | _ := none
                              end
        -/
        | (exp.ETrue) := some ty.TBool
        | (exp.EFalse) := some ty.TBool
        | (exp.Ezero) := some ty.TNat
        | (exp.ESucc) := some (ty.TFun ty.TNat ty.TNat)
        | (exp.EPred) := some (ty.TFun ty.TNat ty.TNat)
        | (exp.EIsZero) := some (ty.TFun ty.TNat ty.TBool)
        | (exp.EPair e1 e2) := sorry -- Here, having e1 and e2 as arguments seems necessary, because the overall type depends on the arguments (unlike in ESucc)
        | (exp.EFst e) := sorry
        | (exp.ESnd e) := sorry
        | _ := none
      end

------------