import Polarized4928
import PEqualNP.Outside.L_meta_7945
open PEqualNP.CircuitLowerBounds LocalFano4126
namespace Local4928
noncomputable local instance : DecidableEq GateOp := Classical.decEq _
theorem gateChart (pre post : List Gate) (g : Gate) (out a b : ℕ)
    (val : Valid ⟨pre ++ g :: post,out⟩) (ins : g.inputs = [a,b])
    (ha : a < 14+pre.length) (hb : b < 14+pre.length) (side : Bool) :
    ∃ x, (if g.op = .or then positiveRow x else negativeRow x) ∧
      valAt pre x a = side ∧ valAt pre x b = !side := by
  classical
  have shape := (shapeOf val.2.1 g (List.mem_append_right _ List.mem_cons_self)).1
  have red (j) (hj : j < 14+pre.length) := polarized PEqualNP.Outside.L_meta_7945.fano27 pre post g out j val hj
  rcases shape with op|op <;> cases side
  · rcases red b hb with ⟨x,_,on,off⟩|⟨x,n,off,on⟩
    · simp [nextVal,op,ins,GateOp.eval,off] at on
    · exact ⟨x,by simpa [op] using n,by simpa [nextVal,op,ins,GateOp.eval,on] using off,on⟩
  · rcases red a ha with ⟨x,_,on,off⟩|⟨x,n,off,on⟩
    · simp [nextVal,op,ins,GateOp.eval,off] at on
    · exact ⟨x,by simpa [op] using n,on,by simpa [nextVal,op,ins,GateOp.eval,on] using off⟩
  · rcases red a ha with ⟨x,p,on,off⟩|⟨x,_,off,on⟩
    · exact ⟨x,by simpa [op] using p,off,by simpa [nextVal,op,ins,GateOp.eval,off] using on⟩
    · simp [nextVal,op,ins,GateOp.eval,on] at off
  · rcases red b hb with ⟨x,p,on,off⟩|⟨x,_,off,on⟩
    · exact ⟨x,by simpa [op] using p,by simpa [nextVal,op,ins,GateOp.eval,off] using on,off⟩
    · simp [nextVal,op,ins,GateOp.eval,on] at off
end Local4928
#print axioms Local4928.gateChart
