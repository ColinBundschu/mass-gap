import MassGap.Levelequiv
/-!
The check module for `thm:levelequiv`: the batteries re-read the
two characterization theorems at the free window `diag(0, 12, 32)`
by kernel `decide` — at the member floor's edge `probe_intro`
carries the operator read's split (the pair `(Ẽ² : 12 Ẽ)` at the
kernel-riding diagonal) onto the probes, each requirement decided
raw beside it, and beyond the edge `probe_elim` carries the
occupied count's split onto a sector vector whose probe fails the
requirement outright, `thm:certconstruct`(2)'s read paired with
the requirement's own refusal.  The occupancy hypothesis is
isolated at the edge's split: its count is unoccupied and no
vector witnesses the pair's failure there. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground elim inertia levelequiv

private def u : BPair := BPair.unit

private def et3 : Mat :=
  [[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]]

private def et3s : SqMat 3 := ⟨et3, rfl⟩

private def esq3 : SqMat 3 := ⟨matMul et3 et3, by decide +kernel⟩

private def rot3 : Mat :=
  [[u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u]]

/-- The rotation's adjugate, the inverse rotation at the unit
determinant. -/
private def rot3w : Mat :=
  [[u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u]]

/-- The split at the edge `γ = 12`: the pair's datum
`diag(0, 0, 640)` at the kernel-riding congruence. -/
private def sp12 : Split 3 :=
  ⟨⟨rot3, by decide +kernel⟩, ⟨rot3w, by decide +kernel⟩, [.one ⟨641, 1⟩], 2, rfl⟩

/-- The split beyond the edge at `γ = 16`: the pair's datum
`diag(0, -48, 512)` at the reversing congruence, one lower-side
block. -/
private def sp16 : Split 3 :=
  ⟨⟨rot3w, by decide +kernel⟩, ⟨rot3, by decide +kernel⟩,
   [.one ⟨1, 49⟩, .one ⟨513, 1⟩], 1, rfl⟩

/-! The operator read at the edge `γ = 12`, with the requirement
carried onto the coordinate probes and each read decided raw. -/

example : opRead (matMul et3 et3) et3 12 1 sp12 := by decide +kernel
example : psdAt sp12 := by decide +kernel

example : reqReadAt esq3 et3s ⟨[u, ⟨2, 1⟩, u], rfl⟩ 12 1 :=
  probe_intro esq3 et3s 12 1 sp12 (by decide +kernel) ⟨[u, ⟨2, 1⟩, u], rfl⟩
example : reqReadAt esq3 et3s ⟨[u, ⟨2, 1⟩, u], rfl⟩ 12 1 := by decide +kernel
example : reqReadAt esq3 et3s ⟨[u, ⟨2, 1⟩, ⟨2, 1⟩], rfl⟩ 12 1 :=
  probe_intro esq3 et3s 12 1 sp12 (by decide +kernel)
    ⟨[u, ⟨2, 1⟩, ⟨2, 1⟩], rfl⟩
example : reqReadAt esq3 et3s ⟨[u, ⟨2, 1⟩, ⟨2, 1⟩], rfl⟩ 12 1 := by
  decide +kernel
example : reqReadAt esq3 et3s ⟨[⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], rfl⟩
    12 1 := by decide +kernel
example : momentform.reqRead et3s ⟨[u, ⟨2, 1⟩, u], rfl⟩ 12 1 := by
  decide +kernel

/-! The occupancy hypothesis at the edge: the split's count is
unoccupied, and the pair's lower-side read is refused at the
fundamental loop's vector — the edge admits no witness. -/

example : ¬ (1 ≤ revAt sp12) := by decide +kernel
example : ¬ certconstruct.witnessRead (matScale 1 (matMul et3 et3))
    (matScale 12 et3) [u, ⟨2, 1⟩, u] := by decide +kernel

/-! Beyond the edge at `γ = 16`: the occupied count's split carries
a witness vector, and the fundamental loop's own probe fails the
requirement, the count's read off the elimination paired with the
refusal. -/

example : splitRead (siteDatum (matScale 1 (matMul et3 et3))
    (matScale 16 et3)) sp16 := by decide +kernel
example : 1 ≤ revAt sp16 := by decide +kernel

example : ∃ y : Vec 3, ¬ reqReadAt esq3 et3s y 16 1 :=
  probe_elim esq3 et3s 16 1 sp16 (by decide +kernel) (by decide +kernel)

example : certconstruct.witnessRead (matScale 1 (matMul et3 et3))
    (matScale 16 et3) [u, ⟨2, 1⟩, u] := by decide +kernel
example : ¬ reqReadAt esq3 et3s ⟨[u, ⟨2, 1⟩, u], rfl⟩ 16 1 := by
  decide +kernel
