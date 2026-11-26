import Mathlib
namespace StarBudget5208
set_option maxRecDepth 12000
set_option maxHeartbeats 4000000
abbrev T := BitVec 64
def gate (op : Bool) (a b : T) : T := bif op then a ||| b else a &&& b
def mark (op : Bool) (a b : T) (side : BitVec 64) : Bool :=
  !op && ((a &&& b &&& 8) == 8) && (((a ||| b) &&& side) == 0)
def pick7 (k : BitVec 4) : T :=
  bif k == 1 then 14757395258967641292 else bif k == 2 then 17361641481138401520 else bif k == 3 then 18374966859414961920 else bif k == 4 then 18446462603027742720 else bif k == 5 then 18446744069414584320 else bif k == 6 then 18446744072850558156 else 12297829382473034410
def pick8 (k : BitVec 4) (w7 : T) : T :=
  bif k == 1 then 14757395258967641292 else bif k == 2 then 17361641481138401520 else bif k == 3 then 18374966859414961920 else bif k == 4 then 18446462603027742720 else bif k == 5 then 18446744069414584320 else bif k == 6 then 18446744072850558156 else bif k == 7 then w7 else 12297829382473034410
def pick9 (k : BitVec 4) (w7 w8 : T) : T :=
  bif k == 1 then 14757395258967641292 else bif k == 2 then 17361641481138401520 else bif k == 3 then 18374966859414961920 else bif k == 4 then 18446462603027742720 else bif k == 5 then 18446744069414584320 else bif k == 6 then 18446744072850558156 else bif k == 7 then w7 else bif k == 8 then w8 else 12297829382473034410
def pick10 (k : BitVec 4) (w7 w8 w9 : T) : T :=
  bif k == 1 then 14757395258967641292 else bif k == 2 then 17361641481138401520 else bif k == 3 then 18374966859414961920 else bif k == 4 then 18446462603027742720 else bif k == 5 then 18446744069414584320 else bif k == 6 then 18446744072850558156 else bif k == 7 then w7 else bif k == 8 then w8 else bif k == 9 then w9 else 12297829382473034410
def pick11 (k : BitVec 4) (w7 w8 w9 w10 : T) : T :=
  bif k == 1 then 14757395258967641292 else bif k == 2 then 17361641481138401520 else bif k == 3 then 18374966859414961920 else bif k == 4 then 18446462603027742720 else bif k == 5 then 18446744069414584320 else bif k == 6 then 18446744072850558156 else bif k == 7 then w7 else bif k == 8 then w8 else bif k == 9 then w9 else bif k == 10 then w10 else 12297829382473034410
theorem impossible (o0 : Bool) (x0 y0 : BitVec 4) (o1 : Bool) (x1 y1 : BitVec 4) (o2 : Bool) (x2 y2 : BitVec 4) (o3 : Bool) (x3 y3 : BitVec 4) (o4 : Bool) (x4 y4 : BitVec 4) :
  let a0 := pick7 x0 
  let b0 := pick7 y0 
  let w7 := gate o0 a0 b0
  let a1 := pick8 x1 w7
  let b1 := pick8 y1 w7
  let w8 := gate o1 a1 b1
  let a2 := pick9 x2 w7 w8
  let b2 := pick9 y2 w7 w8
  let w9 := gate o2 a2 b2
  let a3 := pick10 x3 w7 w8 w9
  let b3 := pick10 y3 w7 w8 w9
  let w10 := gate o3 a3 b3
  let a4 := pick11 x4 w7 w8 w9 w10
  let b4 := pick11 y4 w7 w8 w9 w10
  let w11 := gate o4 a4 b4
  w11 = 12297829373883099816 → ((mark o0 a0 b0 2 && mark o1 a1 b1 4) || (mark o0 a0 b0 2 && mark o2 a2 b2 4) || (mark o0 a0 b0 2 && mark o3 a3 b3 4) || (mark o0 a0 b0 2 && mark o4 a4 b4 4) || (mark o1 a1 b1 2 && mark o2 a2 b2 4) || (mark o1 a1 b1 2 && mark o3 a3 b3 4) || (mark o1 a1 b1 2 && mark o4 a4 b4 4) || (mark o2 a2 b2 2 && mark o3 a3 b3 4) || (mark o2 a2 b2 2 && mark o4 a4 b4 4) || (mark o3 a3 b3 2 && mark o4 a4 b4 4)) = false := by
  dsimp only
  unfold gate mark pick11 pick10 pick9 pick8 pick7
  bv_decide
end StarBudget5208
#print axioms StarBudget5208.impossible
