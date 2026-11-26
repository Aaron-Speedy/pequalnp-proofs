import StarBudget5208
set_option maxHeartbeats 1200000
set_option maxRecDepth 60000
open Lean Elab Command in
elab "kernel_recheck_budget" : command => do
  let env ← getEnv
  let source := `StarBudget5208.impossible
  let ax := `StarBudget5208.impossible._native.bv_decide.ax_1_5
  let some (.thmInfo info) := env.find? source | throwError "missing search theorem"
  let some decl := env.find? ax | throwError "missing reflection check"
  let name := `StarBudget5208.kernelCertificate
  let eqProof := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool) (mkConst ``Bool.true)
  liftCoreM <| addDecl (.thmDecl { name,levelParams:=[],type:=decl.type,value:=eqProof })
  let proof := info.value.replace fun e => if e.isConstOf ax then some (mkConst name) else none
  liftCoreM <| addDecl (.thmDecl {info with name := `StarBudget5208.kernelLower, value := proof})
kernel_recheck_budget
#print axioms StarBudget5208.kernelLower
