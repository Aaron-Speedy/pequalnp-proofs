import Mathlib
import PEqualNP.Defs


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_18232_aux

def network : Circuit :=
  ⟨[⟨.and, [0, 7]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.and, [4, 8]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.and, [9, 12]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.and, [11, 14]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [13, 16]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.and, [15, 10]⟩,
    ⟨.or, [15, 10]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.or, [19, 23]⟩,
    ⟨.and, [18, 22]⟩,
    ⟨.and, [20, 24]⟩,
    ⟨.and, [25, 26]⟩,
    ⟨.or, [25, 26]⟩,
    ⟨.and, [28, 6]⟩,
    ⟨.or, [28, 6]⟩,
    ⟨.and, [27, 31]⟩,
    ⟨.or, [27, 31]⟩,
    ⟨.and, [30, 32]⟩,
    ⟨.or, [33, 29]⟩,
    ⟨.and, [35, 34]⟩,
    ⟨.or, [36, 37]⟩], 38⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem correct (a b c d e f g h i : Bool) :
    network.eval [a, b, c, d, e, f, g, h, i] = decide (5 ≤ [a, b, c, d, e, f, g, h, i].count true) := by
  simp only [network, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.cons_append, List.nil_append, GateOp.eval, List.map_cons, List.map_nil,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.all_cons, List.any_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  revert a b c d e f g h i
  decide

end PEqualNP.Outside.L_meta_18232_aux

open PEqualNP.Outside.L_meta_18232_aux

theorem PEqualNP.Outside.L_meta_18232 : (PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => decide (5 ≤ (List.ofFn x).count true)) 35) := by
  refine ⟨network, ?_, by decide, fun x => ?_⟩
  · simp [FanInTwo, network]
  · exact correct (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)
