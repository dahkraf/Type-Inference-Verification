import .base_language

/-
# Exercise 4
Implement a type inferencer.
-/
def type_infer [decidable_eq ty] : ctx → exp → option ty
| Γ (exp.EVar x) := ctx_lookup x Γ
| Γ (exp.ELam x A e) := let Γ' : ctx := (ctx.ctx_snoc Γ x A) in
                        bind (type_infer Γ' e) (λ o, ty.TFun A o) -- need monads to wrap/unwrap types inside "option"
| Γ (exp.ERec f x A B e) := let Γ' : ctx := (ctx.ctx_snoc (ctx.ctx_snoc Γ x A) f (ty.TFun A B)) in
                            bind (type_infer Γ' e) (λ o, ty.TFun A o) -- add a check against declared output type B
| Γ (exp.EApp e1 e2) := let input_type : option ty := (type_infer Γ e2) in
                        let output_type : option ty := (type_infer Γ e1) in
                        match output_type with
                        | (some (ty.TFun A B)) :=
                            match input_type with
                            | (some T) := if (A = T) then (some B) else none -- ℚ: How to define deiceability over inductive type ty?
                            | _ := none                                      -- ℚ: How to check types for equality (A = T)?
                            end
                        | _ := none
                        end
| Γ (exp.ETrue) := some ty.TBool
| Γ (exp.EFalse) := some ty.TBool
| Γ (exp.EIf e1 e2 e3) := let cond_type : option ty := (type_infer Γ e1) in
                          let if_branch_type : option ty := (type_infer Γ e2) in
                          let else_branch_type : option ty := (type_infer Γ e3) in
                          match cond_type with
                          | (some ty.TBool) :=
                              match if_branch_type, else_branch_type with
                              | (some A), (some B) := if (A = B) then (some A) else none -- same issue as in EApp
                              | _, _ := none
                              end
                          | _ := none
                          end
| Γ (exp.Ezero) := some ty.TNat
| Γ (exp.ESucc) := some (ty.TFun ty.TNat ty.TNat)
| Γ (exp.EPred) := some (ty.TFun ty.TNat ty.TNat)
| Γ (exp.EIsZero) := some (ty.TFun ty.TNat ty.TBool)
| Γ (exp.EPair e1 e2) := let l_type : option ty := (type_infer Γ e1) in
                         let r_type : option ty := (type_infer Γ e2) in
                         match l_type, r_type with
                         | (some A), (some B) := some (ty.TProd A B) -- Here, having e1 and e2 as arguments seems necessary, because the overall type depends on the arguments (unlike in ESucc)
                         | _, _ := none
                         end
| Γ (exp.EFst e) := let pair_type : option ty := (type_infer Γ e) in
                    match pair_type with
                    | some (ty.TProd A B) := some A
                    | _ := none
                    end
| Γ (exp.ESnd e) := let pair_type : option ty := (type_infer Γ e) in
                    match pair_type with
                    | some (ty.TProd A B) := some B
                    | _ := none
                    end
------------

#eval type_infer (ctx.ctx_nil) (exp.ETrue) -- requires instance of decidable_eq ty