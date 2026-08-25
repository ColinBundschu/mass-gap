import MassGap.Momentdivisor
/-!
The check module for `cor:momentdivisor`: the batteries re-read the
window statement's two directions at the free window `diag(0, 12,
32)` at the moment spelling — at the edge `window_intro` carries
the compressed pair's split onto the probes, the moments'
requirement decided raw beside it, and beyond the edge
`window_elim` carries the occupied count's split onto a probe whose
moments refuse the requirement, the refusal decided raw at the
exhibited vector.  The split's positivity is isolated at the
occupied count: beyond the edge the semidefinite read fails
outright, so the spectrum direction has no hypothesis there. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground elim inertia momentdivisor

private def u : BPair := BPair.unit

private def et3 : Mat :=
  [[u, u, u], [u, ⟨13, 1⟩, u], [u, u, ⟨33, 1⟩]]

private def et3s : SqMat 3 := ⟨et3, rfl⟩

private def rot3 : Mat :=
  [[u, ⟨2, 1⟩, u], [u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u]]

/-- The rotation's adjugate, the inverse rotation at the unit
determinant. -/
private def rot3w : Mat :=
  [[u, u, ⟨2, 1⟩], [⟨2, 1⟩, u, u], [u, ⟨2, 1⟩, u]]

/-- The split at the edge `γ = 12`: the moment pair's datum
`diag(0, 0, 640)` at the kernel-riding congruence. -/
private def sp12 : Split 3 :=
  ⟨⟨rot3, by decide +kernel⟩, ⟨rot3w, by decide +kernel⟩, [.one ⟨641, 1⟩], 2, rfl⟩

/-- The split beyond the edge at `γ = 16`: the moment pair's datum
`diag(0, -48, 512)` at the reversing congruence, one lower-side
block. -/
private def sp16 : Split 3 :=
  ⟨⟨rot3w, by decide +kernel⟩, ⟨rot3, by decide +kernel⟩,
   [.one ⟨1, 49⟩, .one ⟨513, 1⟩], 1, rfl⟩

/-! The spectrum direction at the edge: the requirement carried
onto the probes, each moment read decided raw beside it. -/

example : momentform.reqRead et3s ⟨[u, ⟨2, 1⟩, u], rfl⟩ 12 1 :=
  window_intro et3s 12 1 sp12 (by decide +kernel) (by decide +kernel)
    ⟨[u, ⟨2, 1⟩, u], rfl⟩
example : momentform.reqRead et3s ⟨[u, ⟨2, 1⟩, u], rfl⟩ 12 1 := by
  decide +kernel
example : momentform.reqRead et3s ⟨[u, ⟨2, 1⟩, ⟨2, 1⟩], rfl⟩ 12 1 :=
  window_intro et3s 12 1 sp12 (by decide +kernel) (by decide +kernel)
    ⟨[u, ⟨2, 1⟩, ⟨2, 1⟩], rfl⟩
example : momentform.reqRead et3s ⟨[u, ⟨2, 1⟩, ⟨2, 1⟩], rfl⟩ 12 1 := by
  decide +kernel

/-! The failing direction beyond the edge: the occupied count's
split carries a probe refusing the requirement, the refusal
decided raw at the fundamental loop's vector. -/

example : ∃ y : Vec 3, ¬ momentform.reqRead et3s y 16 1 :=
  window_elim et3s 16 1 sp16 (by decide +kernel) (by decide +kernel)
example : ¬ momentform.reqRead et3s ⟨[u, ⟨2, 1⟩, u], rfl⟩ 16 1 := by
  decide +kernel

/-! The semidefinite read is isolated at the occupied count: beyond
the edge the split's own positivity is refused. -/

example : ¬ psdAt sp16 := by decide +kernel
