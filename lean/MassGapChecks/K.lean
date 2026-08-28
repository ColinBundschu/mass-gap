import MassGap.K
import MassGapChecks.Carrier
/-!
The check module for `def:K`: the batteries re-read the cut at the
free end by kernel `decide`, the free-end reading closing through
the chain — the floor's certificate at the equal-membered floor
(the unit line the ground, `lem:freeend`), and the cut's tests at
the committed windows: at the member floor (`κ` at `ĉ₂(f)`'s
cleared read, `E₀ = 4` at `prop:E0`'s count, the threshold the
fundamental loop's own content) the pair is positive semidefinite
with the floor's entry on the kernel — the edge neutral — at the
square at two and three letters (the three-letter window two
loops, the anti-fundamental's beside the fundamental's at one
content) and at the theta graph at one shared value; beyond the
floor the cut fails, the split's
lower-side unit with `thm:certconstruct`'s witness vector reading
the exceeded pair, `thm:levelequiv`'s shape at the instance.  The
free-gap coherences read the committed enumerations at the
carrier check module's pins through the named displays, the theta
window's at the tabulated lookup route.  The descent tier closes
the module: the cut at the doubled scale reads the base count,
decided at the scaled certificate and routed through
`thm:unitschain`'s descent both ways, the forged scaled block
refusing the stated split. -/
set_option maxHeartbeats 16000000

open ground lattice fusion elim inertia K

private def u : BPair := BPair.unit

/-- The square's free-end level gap at two letters, cutoff 32:
`diag(0, 12, 32)`, the committed enumeration's own read at the
named displays. -/
private def etSq : Mat := [[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]]

example : freeGap (dataA 2) square 32 = etSq :=
  freeGap_ofDiag (dataA 2) square 32 [0, 12, 32] etSq
    (pairpencil.windowDiag_at (dataA 2) square 32 carrier.sqIx2
      [0, 12, 32] carrier.sqIx2_pin (by decide +kernel))
    (by decide +kernel)

/-- The rotation moving the unit line's head entry to the trailing
kernel block. -/
private def rot3 : Mat :=
  [[u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u]]

/-- The rotation reading the occupied contents first with the unit
line trailing. -/
private def rotF : Mat :=
  [[u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u]]

/-! The floor's certificate at the free end: the pair `(H : 0·G)`
positive semidefinite with the unit line the ground. -/

example : floorRead etSq (idMat 3) u 1
    (⟨⟨rotF, by decide +kernel⟩, ⟨rot3, by decide +kernel⟩,
      [.one ⟨13, 1⟩, .one ⟨33, 1⟩], 1, rfl⟩ : Split 3) := by decide +kernel

/-! The cut at the member floor: `κ = 3` in the window's cleared
units (`ĉ₂(f) = [3 : 8]` at the clearing eight), `E₀ = 4`, the
threshold twelve the fundamental loop's own content — the pair
`(Ẽ² : 12 Ẽ)` diagonal at `(0, 0, 640)`, the floor's entry on the
kernel, the edge neutral. -/

example : cutRead (matMul etSq etSq) etSq 4 3 1
    (⟨⟨rot3, by decide +kernel⟩, ⟨rotF, by decide +kernel⟩, [.one ⟨641, 1⟩], 2, rfl⟩
      : Split 3) := by decide +kernel

/-! Beyond the floor the cut fails: at `κ = 4` the datum reads
`diag(0, -48, 512)`, one lower-side unit, and the witness vector at
the fundamental loop reads the exceeded pair,
`thm:levelequiv`'s shape at the instance. -/

private def rot3' : Mat :=
  [[u, u, ⟨2, 1⟩], [u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, u]]

/-- The exchange's adjugate: the exchange itself on the lower side,
the determinant's own member. -/
private def rot3w : Mat :=
  [[u, u, ⟨1, 2⟩], [u, ⟨1, 2⟩, u], [⟨1, 2⟩, u, u]]

example : splitRead
    (siteDatum (matScale 1 (matMul etSq etSq)) (matScale 16 etSq))
    (⟨⟨rot3', by decide +kernel⟩, ⟨rot3w, by decide +kernel⟩,
      [.one ⟨513, 1⟩, .one ⟨1, 49⟩], 1, rfl⟩ : Split 3) := by decide +kernel
example : ¬ cutRead (matMul etSq etSq) etSq 4 4 1
    (⟨⟨rot3', by decide +kernel⟩, ⟨rot3w, by decide +kernel⟩,
      [.one ⟨513, 1⟩, .one ⟨1, 49⟩], 1, rfl⟩ : Split 3) := by decide +kernel
example : certconstruct.witnessRead (matMul etSq etSq)
    (matScale 16 etSq) [u, ⟨2, 1⟩, u] := by decide +kernel

/-! The pair-order refusal: mismatched compressed forms are refused
at the cut's own conjuncts, the truncation off the claim. -/

example : ¬ cutRead [[⟨3, 1⟩, u, u], [u, ⟨3, 1⟩, u], [u, u, ⟨3, 1⟩]]
    [[⟨2, 1⟩, u], [u, ⟨2, 1⟩]] 1 1 1
    (⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one ⟨2, 1⟩, .one ⟨2, 1⟩], 0,
      rfl⟩ : Split 2) := by decide +kernel

/-! The theta graph reads the cut at the same floor, one value at
every window: the level gap `diag(0, 12, 18, 12)` at cutoff
eighteen, the hexagon's entry cleared at the floor's read. -/

private def etTh : Mat :=
  [[u, u, u, u], [u, ⟨13, 1⟩, u, u], [u, u, ⟨19, 1⟩, u],
   [u, u, u, ⟨13, 1⟩]]

example : freeGap (tabulate (dataA 2) 18) thetaG 18 = etTh :=
  freeGap_ofDiag (tabulate (dataA 2) 18) thetaG 18 [0, 12, 18, 12] etTh
    (pairpencil.windowDiag_at (tabulate (dataA 2) 18) thetaG 18
      carrier.thIx18 [0, 12, 18, 12] carrier.thIx18_pin
      (by decide +kernel))
    (by decide +kernel)

private def rot4 : Mat :=
  [[u, ⟨2, 1⟩, u, u], [u, u, ⟨2, 1⟩, u],
   [⟨2, 1⟩, u, u, u], [u, u, u, ⟨2, 1⟩]]

/-- The four-order rotation's adjugate, the inverse rotation at the
unit determinant. -/
private def rot4w : Mat :=
  [[u, u, ⟨2, 1⟩, u], [⟨2, 1⟩, u, u, u],
   [u, ⟨2, 1⟩, u, u], [u, u, u, ⟨2, 1⟩]]

example : cutRead (matMul etTh etTh) etTh 4 3 1
    (⟨⟨rot4, by decide +kernel⟩, ⟨rot4w, by decide +kernel⟩, [.one ⟨109, 1⟩], 3, rfl⟩
      : Split 4) := by decide +kernel

/-! At three letters the floor moves with the member: `κ = 8` at
`ĉ₂(f) = [8 : 18]`'s cleared read, the threshold thirty-two — and
the window is two loops, the fundamental's with the
anti-fundamental's at one content, both entries at the edge, the
kernel the whole window. -/

private def et3 : Mat := [[u, u, u], [u, ⟨33, 1⟩, u], [u, u, ⟨33, 1⟩]]

example : freeGap (dataA 3) square 32 = et3 :=
  freeGap_ofDiag (dataA 3) square 32 [0, 32, 32] et3
    (pairpencil.windowDiag_at (dataA 3) square 32 carrier.sqIx3
      [0, 32, 32] carrier.sqIx3_pin (by decide +kernel))
    (by decide +kernel)

example : pairpencil.windowDiag (dataA 3) square 32
    = [0, 32, 32] :=
  pairpencil.windowDiag_at (dataA 3) square 32 carrier.sqIx3
    [0, 32, 32] carrier.sqIx3_pin (by decide +kernel)

example : cutRead (matMul et3 et3) et3 4 8 1
    (⟨⟨idMat 3, rfl⟩, ⟨idMat 3, rfl⟩, [], 3, rfl⟩ : Split 3) := by decide +kernel

example : floorRead et3 (idMat 3) u 1
    (⟨⟨rotF, by decide +kernel⟩, ⟨rot3, by decide +kernel⟩,
      [.one ⟨33, 1⟩, .one ⟨33, 1⟩], 1, rfl⟩ : Split 3) := by decide +kernel

/-! The cut descends along the ray (`thm:unitschain`): at the
doubled scale — the square at four, the gap at two, the level's
first member at its double — the cut reads the base count, decided
at the scaled certificate and routed through the descent both
ways.  The refusals isolate the descent's arithmetic at the stated
scaled certificate: the square at the bare factor, the gap
unscaled, the level's first member unscaled, and the level's
second member moved with the ray, each off the certificate's read;
the forged block refuses the split conjunct itself. -/

private def spCutBase : Split 3 :=
  ⟨⟨rot3, by decide +kernel⟩, ⟨rotF, by decide +kernel⟩,
    [.one ⟨641, 1⟩], 2, rfl⟩

private def spCutScaled : Split 3 :=
  ⟨⟨rot3, by decide +kernel⟩, ⟨rotF, by decide +kernel⟩,
    [.one ⟨2561, 1⟩], 2, rfl⟩

private theorem cutBase :
    cutRead (matMul etSq etSq) etSq 4 3 1 spCutBase := by
  decide +kernel

private theorem cutScaledRead : splitRead
    (siteDatum (matScale 1 (matScale (2 * 2) (matMul etSq etSq)))
      (matScale (4 * (2 * 3)) (matScale 2 etSq))) spCutScaled := by
  decide +kernel

example : cutRead (matScale (2 * 2) (matMul etSq etSq))
    (matScale 2 etSq) 4 (2 * 3) 1 spCutScaled := by decide +kernel

example : cutRead (matScale (2 * 2) (matMul etSq etSq))
    (matScale 2 etSq) 4 (2 * 3) 1 spCutScaled :=
  cutRead_scale 2 (matMul etSq etSq) etSq 4 3 1 spCutBase _
    cutBase cutScaledRead

example : cutRead (matMul etSq etSq) etSq 4 3 1 spCutBase :=
  cutRead_unscale 2 (matMul etSq etSq) etSq 4 3 1 _ spCutScaled
    (cutRead_scale 2 (matMul etSq etSq) etSq 4 3 1 spCutBase _
      cutBase cutScaledRead)
    cutBase.2.2.1

/-! The arithmetic refusals, each at the stated scaled
certificate. -/

example : ¬ cutRead (matScale 2 (matMul etSq etSq))
    (matScale 2 etSq) 4 (2 * 3) 1 spCutScaled := by decide +kernel
example : ¬ cutRead (matScale (2 * 2) (matMul etSq etSq))
    etSq 4 (2 * 3) 1 spCutScaled := by decide +kernel
example : ¬ cutRead (matScale (2 * 2) (matMul etSq etSq))
    (matScale 2 etSq) 4 3 1 spCutScaled := by decide +kernel
example : ¬ cutRead (matScale (2 * 2) (matMul etSq etSq))
    (matScale 2 etSq) 4 (2 * 3) (2 * 1) spCutScaled := by
  decide +kernel

/-! The forged scaled block refuses the split conjunct. -/

example : ¬ cutRead (matScale (2 * 2) (matMul etSq etSq))
    (matScale 2 etSq) 4 (2 * 3) 1
    (⟨⟨rot3, by decide +kernel⟩, ⟨rotF, by decide +kernel⟩,
      [.one ⟨2562, 1⟩], 2, rfl⟩ : Split 3) := by decide +kernel

/-! The descent's base binder isolated: the beyond-floor pair
transports to the doubled scale off the cut — the scaled split
valid, committed with its lower-side unit kept, and the cut
refused at it. -/

private def spBeyondScaled : Split 3 :=
  ⟨⟨rot3', by decide +kernel⟩, ⟨rot3w, by decide +kernel⟩,
    [.one ⟨2049, 1⟩, .one ⟨1, 193⟩], 1, rfl⟩

example : splitRead
    (siteDatum (matScale 1 (matScale (2 * 2) (matMul etSq etSq)))
      (matScale (4 * (2 * 4)) (matScale 2 etSq)))
    spBeyondScaled := by decide +kernel

example : ¬ cutRead (matScale (2 * 2) (matMul etSq etSq))
    (matScale 2 etSq) 4 (2 * 4) 1 spBeyondScaled := by
  decide +kernel
