import MassGap.Generators
/-!
The check module for `def:generators`: the displayed list's count
join at the small widths with the theorem route and the vacant
width's refusal; the anti-Hermitian fold decided and through the
theorem; the companion read at the displayed entries and through
`iT_entry`; the Gram's values at the fundamental width (the
diagonal at the balance pair of two, the determinant at the
partner of eight), its realness read, and the adjugate identity —
the solve's whole verification; and the cleared Fierz read decided
whole at the fundamental width.
-/

namespace generators
set_option maxHeartbeats 4000000

open ground

/-! The count join at the small widths, decided and through the
theorem, with the vacant width's refusal. -/

theorem pin1 : (genList 2).length = 3 := by decide +kernel
theorem pin2 : (genList 3).length = 8 := by decide +kernel
theorem pin3 : (genList 4).length = 15 := by decide +kernel
theorem pin4 : (genList 2).length + 1 = 2 * 2 :=
  genList_length 2 (Nat.le_succ 1)
theorem pin5 : (genList 3).length + 1 = 3 * 3 :=
  genList_length 3 (Nat.le.step (Nat.le_succ 1))
theorem pin6 : (genList 4).length + 1 = 4 * 4 :=
  genList_length 4 (Nat.le.step (Nat.le.step (Nat.le_succ 1)))
theorem pin7 : ¬ ((genList 0).length + 1 = 0 * 0) := by decide +kernel

/-! The anti-Hermitian fold, decided and through the theorem. -/

theorem pin8 : antiHAll 2 := by decide +kernel
theorem pin9 : antiHAll 3 := by decide +kernel
theorem pin10 : antiHAll 2 := antiHAll_holds 2
theorem pin11 : antiHAll 3 := antiHAll_holds 3

/-! The companion read at the small widths, with `iT_entry`'s route
at two concrete pairs. -/

theorem pin12 : iTRead 2 := by decide +kernel
theorem pin13 : iTRead 3 := by decide +kernel
theorem pin14 : poly.oneValue
    (poly.remMul stagesplit.iList [BPair.unit, BPair.ofNat 1]
      [(⟨9, 4⟩ : BPair), (⟨2, 7⟩ : BPair).swap])
    [(⟨2, 7⟩ : BPair), (⟨9, 4⟩ : BPair)] :=
  iT_entry ⟨2, 7⟩ ⟨9, 4⟩
theorem pin15 : poly.oneValue
    (poly.remMul stagesplit.iList [BPair.unit, BPair.ofNat 1]
      [BPair.unit, (BPair.ofNat 5).swap])
    [BPair.ofNat 5, BPair.unit] :=
  iT_entry (BPair.ofNat 5) BPair.unit

/-! The Gram's values at the fundamental width: the diagonal at the
balance pair of two, one off-diagonal at the sum's unit, the
determinant at the partner of eight. -/

theorem pin16 : BPair.oneValue
    (ground.getAt BPair.unit (ground.getAt [] (gramR 2) 0) 0)
    ⟨1, 3⟩ := by decide +kernel
theorem pin17 : BPair.oneValue
    (ground.getAt BPair.unit (ground.getAt [] (gramR 2) 1) 1)
    ⟨1, 3⟩ := by decide +kernel
theorem pin18 : BPair.oneValue
    (ground.getAt BPair.unit (ground.getAt [] (gramR 2) 0) 1)
    BPair.unit := by decide +kernel
theorem pin19 : BPair.oneValue (detG 2) ⟨1, 9⟩ := by decide +kernel

/-! The realness read, the adjugate identity's coherence, and the
independence read at the determinant off the sum's unit — with the
determinant's value pinned at both widths, the width-three
determinant the non-scalar Gram's own. -/

theorem pin20 : gramReal 2 := by decide +kernel
theorem pin21 : gramReal 3 := by decide +kernel
theorem pin22 : gramSolve 2 := by decide +kernel
theorem pin23 : gramSolve 3 := by decide +kernel
theorem pin24 : gramIndep 2 := by decide +kernel
theorem pin25 : gramIndep 3 := by decide +kernel
theorem pin26 : BPair.oneValue (detG 3) ⟨193, 1⟩ := by decide +kernel

/-! The companions' `ξ` read: the companion pairing is the
displayed pairing's memberwise swap, the Gram exchange decided
whole at the fundamental width. -/

theorem pin27 : ((genList 2).all (fun X => (genList 2).all (fun Y =>
    decide (BPair.oneValue
      (ground.getAt BPair.unit (traceMul 2 (tOf X) (tOf Y)) 0)
      ((ground.getAt BPair.unit (traceMul 2 X Y) 0).swap))))) = true
  := by decide +kernel

/-! The cleared Fierz read, decided whole.  The width-three
instances here and above are the first at a non-scalar Gram — the
adjugate's weights do their work only there, so the eight-by-eight
solve's cost is the reads' own discriminating content. -/

theorem pin28 : fierzRead 2 := by decide +kernel
theorem pin29 : fierzRead 3 := by decide +kernel

/-! The reads' refusals, each at a forged variant: the swap
combination at the diagonal collision (the anti-Hermitian read's
own boundary), a partner without the balance swap, the companion
read at the uncompanioned list, and the Fierz display at the
exchanged delta weights and at the moved width. -/

theorem pin30 : ¬ antiH 2 (swapX 2 0 0) := by decide +kernel
theorem pin31 : ¬ antiH 3 (swapX 3 1 1) := by decide +kernel

private def swapBad (d p q : Nat) : List (List poly.Poly) :=
  ground.matOf d d (fun i j =>
    if i == p && j == q then entryOne
    else if i == q && j == p then entryOne else [])

theorem pin32 : ¬ antiH 2 (swapBad 2 0 1) := by decide +kernel

theorem pin33 : ¬ ((((genList 2).zip (genList 2)).all (fun XT =>
    (List.range 2).all (fun i => (List.range 2).all (fun j =>
      decide (poly.oneValue
        (poly.remMul stagesplit.iList entryI
          (ground.getAt [] (ground.getAt [] XT.2 i) j))
        (ground.getAt [] (ground.getAt [] XT.1 i) j)))))) = true) := by
  decide +kernel

private def fierzBad (d : Nat) : Prop :=
  let dg := [detG d]
  ((List.range d).all (fun p => (List.range d).all (fun q =>
    (List.range d).all (fun r => (List.range d).all (fun s =>
      decide (poly.oneValue
        (poly.scaleP (dl p q * dl r s * BPair.ofNat d) dg)
        (poly.add (poly.scaleP (dl p q * dl r s) dg)
          (poly.scaleP (BPair.ofNat d)
            (fierzS d p q r s))))))))) = true

private instance instGeneratorsChk1 (d : Nat) : Decidable (fierzBad d) :=
  inferInstanceAs (Decidable (_ = _))

private def fierzWide (d : Nat) : Prop :=
  let dg := [detG d]
  ((List.range d).all (fun p => (List.range d).all (fun q =>
    (List.range d).all (fun r => (List.range d).all (fun s =>
      decide (poly.oneValue
        (poly.scaleP (dl p s * dl r q * BPair.ofNat (d + 1)) dg)
        (poly.add (poly.scaleP (dl p q * dl r s) dg)
          (poly.scaleP (BPair.ofNat (d + 1))
            (fierzS d p q r s))))))))) = true

private instance instGeneratorsChk2 (d : Nat) : Decidable (fierzWide d) :=
  inferInstanceAs (Decidable (_ = _))

theorem pin34 : ¬ fierzBad 2 := by decide +kernel
theorem pin35 : ¬ fierzWide 2 := by decide +kernel

end generators
