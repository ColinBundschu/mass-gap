import MassGap.Cellbox
/-!
The check module for `lem:cellcount`'s box cover: the batteries
re-read the two-variable reads by kernel `decide` at the pencil
`S(t, s) = [[3 + t + s, 1], [1, 5]]`, the inner variable `t` and the
outer `s`.  The shape read at the order two and the two clearing
powers one, refused at the order one, at the outer power nought and
at the inner power nought; the symmetry read, refused at an
exchanged entry; the inner evaluation at `t = 1/2` (the pencil
`[[7 + 2s, 2], [2, 10]]` at the clearing two) decided, with its shape
and symmetry through the theorems; the once-cleared deflation at
the pivot `[0]` double-evaluated against the evaluated pencil's own
once-cleared deflation, decided and through the theorem, its value
`14` at the origin, its swap so, and at a three-by-three pencil the
order-two pivot's deflation so; the two deflations' shapes at the
doubled clearings decided and through the theorems with the outer
shape refused one power low; the polynomial adjugate evaluated
against the evaluated adjugate.  The box cover on
`[0, 1/4] × [0, 1/4]`: the pivot `3 + t + s` on its upper side over
the box at the bounds one, beneath it the once-cleared deflation
`14 + 5t + 5s` its own piece with the order-nought deflation
beneath, decided whole, the constancy theorem run at the origin
against the interior point `(1/8, 1/8)` with both counts the
positive-definite `0` at the pencil's shape and symmetry reads, the
same cover refused on the box `[0, 1] × [0, 37/20]` at the bounds
one and two, where the deflation's price outruns its corner value
`14` while the pivot's own read holds, the unit box covered at the
quarter grid of sixteen cuts with the constancy theorem run across
opposite corners, a cut refused at a point off the bracket, the
flipped side refused, the piece frame decided at the designated
place with its refusals at repeated and out-of-order places, the
mixed order-two piece at `[[3 + t + s, 1], [1, -5]]`, the count at
the origin one, and the upper order-two piece at the first pencil,
the count at the origin nought, each decided with the constancy
theorem; the transport of a sampled count across the box
(`cellCount2`); and the refusals of the order-nought read at an
occupied order, of the mixed row and of the lower leading entry at
the first pencil, with the lower one-piece read decided at the
constant `-5`.  Integers enter as one-member balance data,
`BPair.ofNat n`. -/

namespace cellcount
open ground poly elim inertia

private def u : BPair := BPair.unit

/-- `3 + t + s`. -/
private def e3ts : PPoly := [[BPair.ofNat 3, BPair.ofNat 1], [BPair.ofNat 1]]
/-- `1`. -/
private def e1 : PPoly := [[BPair.ofNat 1]]
/-- `5`. -/
private def e5 : PPoly := [[BPair.ofNat 5]]
/-- `7`. -/
private def e7 : PPoly := [[BPair.ofNat 7]]
/-- `-5`. -/
private def em5 : PPoly := [[(BPair.ofNat 5).swap]]
/-- The sum's unit. -/
private def e0 : PPoly := [[u]]

/-- `[[3 + t + s, 1], [1, 5]]`. -/
private def sB : split.PPMat := [[e3ts, e1], [e1, e5]]
/-- `[[3 + t + s, 1], [1, -5]]`. -/
private def sM : split.PPMat := [[e3ts, e1], [e1, em5]]
/-- `[[3 + t + s, 1], [5, 5]]`, off the symmetry read. -/
private def sX : split.PPMat := [[e3ts, e1], [e5, e5]]
/-- `[[3 + t + s, 1, 0], [1, 5, 1], [0, 1, 7]]`. -/
private def sC : split.PPMat := [[e3ts, e1, e0], [e1, e5, e1], [e0, e1, e7]]

private def c0 : CPair := ⟨u, 1⟩
private def q1 : CPair := ⟨BPair.ofNat 1, 4⟩
private def h1 : CPair := ⟨BPair.ofNat 1, 2⟩
private def tq : CPair := ⟨BPair.ofNat 3, 4⟩
private def c1 : CPair := ⟨BPair.ofNat 1, 1⟩
private def c2 : CPair := ⟨BPair.ofNat 2, 1⟩
private def N1 : BPair := BPair.ofNat 1

/-! The shape and symmetry reads, decided and refused. -/

theorem pin125 : ppShapeAt sB 2 1 1 := by decide +kernel
theorem pin126 : ¬ ppShapeAt sB 1 1 1 := by decide +kernel
theorem pin127 : ¬ ppShapeAt sB 2 0 1 := by decide +kernel
theorem pin128 : ¬ ppShapeAt sB 2 1 0 := by decide +kernel
theorem pin129 : split.ppSymAt sB 2 := by decide +kernel
theorem pin130 : ¬ split.ppSymAt sX 2 := by decide +kernel
theorem pin131 : ppShapeAt sC 3 1 1 := by decide +kernel
theorem pin132 : ppShapeAt sM 2 1 1 := by decide +kernel
theorem pin133 : split.ppSymAt sM 2 := by decide +kernel

/-! The inner evaluation at `t = 1/2`, its shape and symmetry through
the theorems. -/

theorem pin134 : split.pmatOneValue (ppevalPC sB (BPair.ofNat 1) 2 1)
    [[[BPair.ofNat 7, BPair.ofNat 2], [BPair.ofNat 2]],
     [[BPair.ofNat 2], [BPair.ofNat 10]]] := by decide +kernel
theorem pin135 : pShapeAt (ppevalPC sB (BPair.ofNat 1) 2 1) 2 1 := by
  decide +kernel
theorem pin136 : pShapeAt (ppevalPC sB (BPair.ofNat 1) 2 1) 2 1 :=
  pShapeAt_ppevalPC pin125 (BPair.ofNat 1) 2
theorem pin137 : split.pSymAt (ppevalPC sB (BPair.ofNat 1) 2 1) 2 := by
  decide +kernel
theorem pin138 : split.pSymAt (ppevalPC sB (BPair.ofNat 1) 2 1) 2 :=
  pSymAt_ppevalPC pin129 (BPair.ofNat 1) 2 1

/-! The once-cleared deflation's double evaluation against the
evaluated pencil's own once-cleared deflation, decided and through
the theorem, at the pivot `[0]` and at the three-by-three pencil's
pivot `[0, 1]`; the deflation's value at the origin; the polynomial
adjugate against the evaluated adjugate. -/

theorem pin139 : split.pmatOneValue
    (ppevalPC (pdeflP2 [0] [1] sB) (BPair.ofNat 1) 2 2)
    (pdeflP [0] [1] (ppevalPC sB (BPair.ofNat 1) 2 1)) := by decide +kernel
theorem pin140 : split.pmatOneValue
    (ppevalPC (pdeflP2 [0] [1] sB) (BPair.ofNat 1) 2
      ((([0] : List Nat).length + 1) * 1))
    (pdeflP [0] [1] (ppevalPC sB (BPair.ofNat 1) 2 1)) :=
  ppevalPC_pdeflP2 (o := 2) (Ks := 1) sB [0] [1] (BPair.ofNat 1) 2 pin125
    (Nat.succ_pos 0)
theorem pin141 : split.pmatOneValue
    (ppevalPC (pdeflP2 [0, 1] [2] sC) (BPair.ofNat 1) 2 3)
    (pdeflP [0, 1] [2] (ppevalPC sC (BPair.ofNat 1) 2 1)) := by decide +kernel
theorem pin142 : split.pmatOneValue
    (ppevalPC (pdeflP2 [0, 1] [2] sC) (BPair.ofNat 1) 2
      ((([0, 1] : List Nat).length + 1) * 1))
    (pdeflP [0, 1] [2] (ppevalPC sC (BPair.ofNat 1) 2 1)) :=
  ppevalPC_pdeflP2 (o := 3) (Ks := 1) sC [0, 1] [2] (BPair.ofNat 1) 2 pin131
    (Nat.succ_pos 1)
theorem pin143 : elim.matOneValue
    (evalPC (ppevalPC (pdeflP2 [0] [1] sB) u 1 2) u 1 2) [[BPair.ofNat 14]] := by
  decide +kernel
theorem pin144 : split.pmatOneValue (ppevalPC (split.ppadj sB) (BPair.ofNat 1) 2 1)
    (split.padj (ppevalPC sB (BPair.ofNat 1) 2 1)) := by decide +kernel

/-! The box cover on `[0, 1/4] × [0, 1/4]`: the pivot piece with the
deflation's piece beneath it, decided, with the constancy theorem at
the origin against the interior point. -/

private def cvLeaf : Cover2 :=
  .one 0 true N1 N1 N1 N1 (.one 0 true N1 N1 N1 N1 .nought)

theorem pin145 : coverRead2 sB 2 1 1 c0 q1 c0 q1 cvLeaf := by decide +kernel

private def e8n : BPair := BPair.ofNat 1
private def e8c : Pos := 8

/-- The first pencil's double evaluation at the interior point is
square at the order. -/
private theorem sqB8 : elim.sqAt (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1) 2 := by
  decide +kernel
/-- The first pencil's double evaluation at the interior point is
symmetric. -/
private theorem symB8 : elim.matOneValue
    (elim.transposeM (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1))
    (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1) := by decide +kernel
/-- The first pencil's double evaluation at the origin is square at
the order. -/
private theorem sqBu : elim.sqAt (evalPC (ppevalPC sB u 1 1) u 1 1) 2 := by
  decide +kernel
/-- The first pencil's double evaluation at the origin is
symmetric. -/
private theorem symBu : elim.matOneValue
    (elim.transposeM (evalPC (ppevalPC sB u 1 1) u 1 1))
    (evalPC (ppevalPC sB u 1 1) u 1 1) := by decide +kernel
/-- The first pencil's double evaluation at the unit corner is
square at the order. -/
private theorem sqB1 : elim.sqAt
    (evalPC (ppevalPC sB (BPair.ofNat 1) 1 1) (BPair.ofNat 1) 1 1) 2 := by
  decide +kernel
/-- The first pencil's double evaluation at the unit corner is
symmetric. -/
private theorem symB1 : elim.matOneValue
    (elim.transposeM (evalPC (ppevalPC sB (BPair.ofNat 1) 1 1) (BPair.ofNat 1) 1 1))
    (evalPC (ppevalPC sB (BPair.ofNat 1) 1 1) (BPair.ofNat 1) 1 1) := by
  decide +kernel

theorem pin146 : inertia.revAt (inertia.mkSplit 2
    (evalPC (ppevalPC sB u 1 1) u 1 1)) = 0 := by decide +kernel
theorem pin147 : inertia.revAt (inertia.mkSplit 2
    (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1)) = 0 := by decide +kernel
theorem pin148 : inertia.revAt (inertia.mkSplit 2
      (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1))
    = inertia.revAt (inertia.mkSplit 2 (evalPC (ppevalPC sB u 1 1) u 1 1)) :=
  cover2_const (o := 2) sB 1 1 c0 q1 c0 q1 cvLeaf pin145 pin125 pin129
    e8n e8c e8n e8c u 1 u 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1))
    (inertia.mkSplit 2 (evalPC (ppevalPC sB u 1 1) u 1 1))
    (inertia.mkSplit_read 2 _ sqB8 symB8)
    (inertia.mkSplit_read 2 _ sqBu symBu)

/-! The refusals: the one-piece cover on the box `[0, 1] × [0, 37/20]`
at the bounds one and two, where the deflation's price `9 + 37/4`
outruns its corner value `14` while the pivot's own read holds at
`2` against `37/20`; a cut at a point off the bracket; and the
flipped side. -/

private def s37 : CPair := ⟨BPair.ofNat 37, 20⟩
private def N2 : BPair := BPair.ofNat 2
private def cvLeafW : Cover2 :=
  .one 0 true N1 N1 N2 N1 (.one 0 true N1 N1 N2 N1 .nought)

theorem pin149 : ¬ coverRead2 sB 2 1 1 c0 c1 c0 s37 cvLeafW
    ∧ stage.keepUpperBox (split.ppminor (split.ppselM [0] [0] sB))
      c0 c1 c0 s37 N1 N1 N2 N1 := by decide +kernel
theorem pin150 : ¬ coverRead2 sB 2 1 1 c0 c1 c0 c1 (.cutT c2 cvLeaf cvLeaf) := by
  decide +kernel

private def cvFlip : Cover2 :=
  .one 0 false N1 N1 N1 N1 (.one 0 true N1 N1 N1 N1 .nought)

theorem pin151 : ¬ coverRead2 sB 2 1 1 c0 q1 c0 q1 cvFlip := by decide +kernel

/-! The unit box at the quarter grid: sixteen cuts, each leaf the
one-piece cover, decided, with the constancy theorem across opposite
corners. -/

private def strip : Cover2 :=
  .cutS h1 (.cutS q1 cvLeaf cvLeaf) (.cutS tq cvLeaf cvLeaf)
private def cvGrid : Cover2 :=
  .cutT h1 (.cutT q1 strip strip) (.cutT tq strip strip)

theorem pin152 : coverRead2 sB 2 1 1 c0 c1 c0 c1 cvGrid := by decide +kernel
theorem pin153 : inertia.revAt (inertia.mkSplit 2
    (evalPC (ppevalPC sB (BPair.ofNat 1) 1 1) (BPair.ofNat 1) 1 1)) = 0 := by
  decide +kernel
theorem pin154 : inertia.revAt (inertia.mkSplit 2
      (evalPC (ppevalPC sB (BPair.ofNat 1) 1 1) (BPair.ofNat 1) 1 1))
    = inertia.revAt (inertia.mkSplit 2 (evalPC (ppevalPC sB u 1 1) u 1 1)) :=
  cover2_const (o := 2) sB 1 1 c0 c1 c0 c1 cvGrid pin152 pin125 pin129
    (BPair.ofNat 1) 1 (BPair.ofNat 1) 1 u 1 u 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC (ppevalPC sB (BPair.ofNat 1) 1 1) (BPair.ofNat 1) 1 1))
    (inertia.mkSplit 2 (evalPC (ppevalPC sB u 1 1) u 1 1))
    (inertia.mkSplit_read 2 _ sqB1 symB1)
    (inertia.mkSplit_read 2 _ sqBu symBu)

/-! The piece frame refused at a place off the order, beside the
first module's reads at the designated place and at repeated
places. -/

theorem pin155 : ¬ pieceRead 2 [2] := by decide +kernel

/-! The mixed order-two piece at `[[3 + t + s, 1], [1, -5]]`, the
count one, and the upper order-two piece at the first pencil, the
count nought, each decided with the constancy theorem. -/

private def cvMix : Cover2 := .mixed 0 1 N1 N1 N1 N1 .nought

/-- The mixed pencil's double evaluation at the interior point is
square at the order. -/
private theorem sqM8 : elim.sqAt (evalPC (ppevalPC sM e8n e8c 1) e8n e8c 1) 2 := by
  decide +kernel
/-- The mixed pencil's double evaluation at the interior point is
symmetric. -/
private theorem symM8 : elim.matOneValue
    (elim.transposeM (evalPC (ppevalPC sM e8n e8c 1) e8n e8c 1))
    (evalPC (ppevalPC sM e8n e8c 1) e8n e8c 1) := by decide +kernel
/-- The mixed pencil's double evaluation at the origin is square at
the order. -/
private theorem sqMu : elim.sqAt (evalPC (ppevalPC sM u 1 1) u 1 1) 2 := by
  decide +kernel
/-- The mixed pencil's double evaluation at the origin is
symmetric. -/
private theorem symMu : elim.matOneValue
    (elim.transposeM (evalPC (ppevalPC sM u 1 1) u 1 1))
    (evalPC (ppevalPC sM u 1 1) u 1 1) := by decide +kernel

theorem pin156 : coverRead2 sM 2 1 1 c0 q1 c0 q1 cvMix := by decide +kernel
theorem pin157 : inertia.revAt (inertia.mkSplit 2
    (evalPC (ppevalPC sM u 1 1) u 1 1)) = 1 := by decide +kernel
theorem pin158 : inertia.revAt (inertia.mkSplit 2
      (evalPC (ppevalPC sM e8n e8c 1) e8n e8c 1))
    = inertia.revAt (inertia.mkSplit 2 (evalPC (ppevalPC sM u 1 1) u 1 1)) :=
  cover2_const (o := 2) sM 1 1 c0 q1 c0 q1 cvMix pin156 pin132 pin133
    e8n e8c e8n e8c u 1 u 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC (ppevalPC sM e8n e8c 1) e8n e8c 1))
    (inertia.mkSplit 2 (evalPC (ppevalPC sM u 1 1) u 1 1))
    (inertia.mkSplit_read 2 _ sqM8 symM8)
    (inertia.mkSplit_read 2 _ sqMu symMu)

private def cvTwo : Cover2 := .twoUp 0 1 N1 N1 N1 N1 true N1 N1 N1 N1 .nought

theorem pin159 : coverRead2 sB 2 1 1 c0 q1 c0 q1 cvTwo := by decide +kernel
theorem pin160 : inertia.revAt (inertia.mkSplit 2
      (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1))
    = inertia.revAt (inertia.mkSplit 2 (evalPC (ppevalPC sB u 1 1) u 1 1)) :=
  cover2_const (o := 2) sB 1 1 c0 q1 c0 q1 cvTwo pin159 pin125 pin129
    e8n e8c e8n e8c u 1 u 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (inertia.mkSplit 2 (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1))
    (inertia.mkSplit 2 (evalPC (ppevalPC sB u 1 1) u 1 1))
    (inertia.mkSplit_read 2 _ sqB8 symB8)
    (inertia.mkSplit_read 2 _ sqBu symBu)

/-! The transport (`cellCount2`): the sampled vacant count at the
origin holds at the interior point through the cover. -/

theorem pin161 : inertia.revAt (inertia.mkSplit 2
    (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1)) = 0 :=
  cellCount2 sB 1 1 0 c0 q1 c0 q1 cvLeaf pin145 pin125 pin129
    u 1 u 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (inertia.mkSplit 2 (evalPC (ppevalPC sB u 1 1) u 1 1))
    (by decide +kernel)
    e8n e8c e8n e8c (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    (inertia.mkSplit 2 (evalPC (ppevalPC sB e8n e8c 1) e8n e8c 1))
    (inertia.mkSplit_read 2 _ sqB8 symB8)

/-! The refusals of the order-nought read at an occupied order, of
the mixed order-two row at the first pencil, whose determinant sits
on its upper side, and of the lower leading entry beneath the upper
determinant; and the lower one-piece read at the constant `-5`. -/

theorem pin162 : ¬ coverRead2 sB 2 1 1 c0 q1 c0 q1 .nought := by decide +kernel
theorem pin163 : ¬ coverRead2 sB 2 1 1 c0 q1 c0 q1 cvMix := by decide +kernel
theorem pin164 : ¬ coverRead2 sB 2 1 1 c0 q1 c0 q1
    (.twoUp 0 1 N1 N1 N1 N1 false N1 N1 N1 N1 .nought) := by decide +kernel

private def sN : split.PPMat := [[em5]]

theorem pin165 : coverRead2 sN 1 1 1 c0 q1 c0 q1
    (.one 0 false N1 N1 N1 N1 .nought) := by decide +kernel

/-! The swapped deflation's double evaluation against the evaluated
pencil's own swapped deflation, decided and through the theorem; the
two deflations' shapes at the doubled clearings through the
theorems, the outer shape refused one power low. -/

theorem pin193 : split.pmatOneValue
    (ppevalPC (pdeflM2 [0] [1] sB) (BPair.ofNat 1) 2 2)
    (pdeflM [0] [1] (ppevalPC sB (BPair.ofNat 1) 2 1)) := by decide +kernel
theorem pin194 : split.pmatOneValue
    (ppevalPC (pdeflM2 [0] [1] sB) (BPair.ofNat 1) 2
      ((([0] : List Nat).length + 1) * 1))
    (pdeflM [0] [1] (ppevalPC sB (BPair.ofNat 1) 2 1)) :=
  ppevalPC_pdeflM2 (o := 2) (Ks := 1) sB [0] [1] (BPair.ofNat 1) 2 pin125
    (Nat.succ_pos 0)
theorem pin195 : ppShapeAt (pdeflP2 [0] [1] sB) 1 2 2 := by decide +kernel
theorem pin196 : ppShapeAt (pdeflP2 [0] [1] sB) 1
    ((([0] : List Nat).length + 1) * 1) ((([0] : List Nat).length + 1) * 1) :=
  ppShape_pdeflP2 sB 2 1 1 [0] [1] pin125
theorem pin197 : ppShapeAt (pdeflM2 [0] [1] sB) 1
    ((([0] : List Nat).length + 1) * 1) ((([0] : List Nat).length + 1) * 1) :=
  ppShape_pdeflM2 sB 2 1 1 [0] [1] pin125
theorem pin198 : ¬ ppShapeAt (pdeflP2 [0] [1] sB) 1 0 2 := by decide +kernel

end cellcount
