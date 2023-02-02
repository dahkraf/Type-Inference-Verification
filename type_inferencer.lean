import .base_language

/-
# Exercise 4
Implement a type inferencer.
-/

def elam_helper : option ty → option ty
| (some A) := some A
| none := none

-- def eif_helper : option ty → option ty
-- | (some ty.TBool) :=
--     match if_branch_type, else_branch_type with
--     | (some A), (some B) := if (A = B) then (some A) else none
--     | _, _ := none
--     end
-- | _ := none
-- end
-- ℚ: No idea how to pattern match as an expression!

def type_infer [decidable_eq ty] : ctx → exp → option ty
| Γ (exp.EVar x) := ctx_lookup x Γ
| Γ (exp.ELam x A e) := (
                            λ Γ' : ctx,
                                (
                                    (
                                        λ output_type : option ty,
                                            (elam_helper output_type)
                                    )
                                    (type_infer Γ' e)
                                )
                        )
                        (ctx.ctx_snoc Γ x A)
| Γ (exp.ERec f x A B e) := 
                            (
                            λ Γ' : ctx,
                                (
                                    (
                                        λ output_type : option ty,
                                            bind (output_type) (λ o, some (ty.TFun A o))
                                    )
                                    (type_infer Γ' e)
                                )
                        )
                        (ctx.ctx_snoc (ctx.ctx_snoc Γ x A) f (ty.TFun A B))
| Γ (exp.EApp e1 e2) := let input_type : option ty := (type_infer Γ e2) in
                        let output_type : option ty := (type_infer Γ e1) in
                        match output_type with
                        | (some (ty.TFun A B)) :=
                            match input_type with
                            | (some T) := if (A = T) then (some B) else none
                            | _ := none
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
                              | (some A), (some B) := if (A = B) then (some A) else none
                              | _, _ := none
                              end
                          | _ := none
                          end
                          /-
                          Alternative:
                          (
                            λ cond_type : option ty,
                                (
                                    (
                                        λ if_branch_type : option ty,
                                            (
                                                (
                                                    λ else_branch_type : option ty,
                                                        (
                                                            eif_helper
                                                        )
                                                )
                                                (type_infer Γ e3)
                                            )
                                    )
                                    (type_infer Γ e2)
                                )
                          ) 
                          ((type_infer Γ e1))
                          -/
| Γ (exp.Ezero) := some ty.TNat
| Γ (exp.ESucc) := some (ty.TFun ty.TNat ty.TNat)
| Γ (exp.EPred) := some (ty.TFun ty.TNat ty.TNat)
| Γ (exp.EIsZero) := some (ty.TFun ty.TNat ty.TBool)
| Γ (exp.EPair e1 e2) := let l_type : option ty := (type_infer Γ e1) in
                         let r_type : option ty := (type_infer Γ e2) in
                         match l_type, r_type with
                         | (some A), (some B) := some (ty.TProd A B)
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

-- Sanity check:
#eval type_infer (ctx.ctx_nil) (exp.ELam "x" ty.TNat (exp.EIsZero))
#eval some $ ty.TFun ty.TNat (ty.TFun ty.TNat ty.TBool)