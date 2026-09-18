import MassGap.Channelreads
/-!
The check module for `def:channelreads`: the batteries re-read the
channel's derived objects by kernel `decide` at the two committed
bases — the series' displayed head at the polynomial carrier, the
renewal witness's two-list read with a forged base and a forged
depth refusing beside it, the mass point's witness, the
conjugation read at the factor list with the unreversed forgery
refusing, the factors' base reads — the leading coefficient and
the root, a forged list at the base's cube passing the shape reads
while both base reads refuse it — and the order count at three,
the pole order with the factor count.
-/

namespace channelreads
set_option maxHeartbeats 4000000

open ground poly

/-! The series' displayed head at the carrier, and the renewal
witness's read at the two bases; a forged base inside the scale
refuses the read, and a depth misalignment refuses it beside. -/

theorem pin1 : oneValue (g0List 2 3)
    [BPair.unit, BPair.ofNat 1, BPair.ofNat 2, BPair.ofNat 4,
     BPair.ofNat 8] := by decide +kernel

theorem pin2 : renewalRead 1 6 := by decide +kernel
theorem pin3 : renewalRead 2 6 := by decide +kernel

theorem pin4 : ¬ oneValue (g0List 2 7)
    (add (mono 1) (scaleP (BPair.ofPos 3) (shiftUp 1 (g0List 2 6)))) := by
  decide +kernel
theorem pin5 : ¬ oneValue (g0List 2 6)
    (add (mono 1) (scaleP (BPair.ofPos 2) (shiftUp 1 (g0List 2 6)))) := by
  decide +kernel

/-! The mass point's witness at the two bases, and the pole
order's multiplicity-gap witness at the stated factor's top. -/

theorem pin6 : massRead 1 := by decide +kernel
theorem pin7 : massRead 2 := by decide +kernel
theorem pin8 : poleOrderRead 1 := by decide +kernel
theorem pin9 : poleOrderRead 2 := by decide +kernel

/-! The conjugation read at the factor list, with the unreversed
forgery refusing. -/

theorem pin10 : conjRead 1 := by decide +kernel
theorem pin11 : conjRead 2 := by decide +kernel
theorem pin12 : ¬ oneValue (getAt [] (factors 2) 0) (getAt [] (factors 2) 1) := by
  decide +kernel

/-! Each factor reads the base once: `⟨1 : c₁z⟩` at its leading
coefficient and `⟨z : c₁⟩` at its root `c₁`, the two reads decided
at the stated list — and a forged list at the base's cube passes
the conjugation and pole-order shapes while both base reads refuse
it, the reads' own isolation. -/

theorem pin13 : (top (getAt [] (factors 2) 0)).oneValue
    ((BPair.ofPos 2).swap) := by decide +kernel
theorem pin14 : (eval (getAt [] (factors 2) 1) (BPair.ofPos 2)).oneValue
    BPair.unit := by decide +kernel

private def factorsForge (c1 : Pos) : List Poly :=
  [[BPair.ofPos Pos.one, (BPair.ofPos (c1 * c1 * c1)).swap],
   [(BPair.ofPos (c1 * c1 * c1)).swap, BPair.ofPos Pos.one]]

theorem pin15 : oneValue ((getAt [] (factorsForge 2) 0).reverse)
    (getAt [] (factorsForge 2) 1) := by decide +kernel
theorem pin16 : (top (getAt [] (factorsForge 2) 0)).offUnit := by decide +kernel
theorem pin17 : ¬ (top (getAt [] (factorsForge 2) 0)).oneValue
    ((BPair.ofPos 2).swap) := by decide +kernel
theorem pin18 : ¬ (eval (getAt [] (factorsForge 2) 1) (BPair.ofPos 2)).oneValue
    BPair.unit := by decide +kernel

/-! The order count: the pole order with the factor count, three
at either base. -/

theorem pin19 : orderCount 1 = 3 := by decide +kernel
theorem pin20 : orderCount 2 = 3 := by decide +kernel

end channelreads
