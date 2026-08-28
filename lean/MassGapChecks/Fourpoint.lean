import MassGap.Fourpoint
import MassGap.Memberdata
/-!
The check module for `lem:fourpoint`: the side and the collection
re-read by kernel `decide` at the members' adjoint squares.  At
`SU(2)` the channel list runs `2θ`, `θ`, the unit at the weights
`[5 : 9]`, `[3 : 9]`, `[1 : 9]` and the contents `9`, `7`, `6`, so
the pair fold reads `S = 145/1134` and eight times it exceeds one
by `26/1134`, the three pair terms `20/1701 + 5/486 + 1/1134` — the
margin `[c₁ : 42 d_θ³] = 1/1134` the unit channel's term against
`θ`'s alone, the fold decided exact at `26` and refused one beyond;
the jet's free moments read `1, 0, 1, 1, 3`, the fourth-order data
`D₂₂ = 3793/4536` and `D₂₀ = 7/24`, and the partition fold at the
displayed orders the unit at `τ⁰` and `τ²` with
`c₁² ⟨S : [1 : 8]⟩ = 13/4536` at `τ⁴`, decided exact at `13` and
refused one beyond.  The side, the margin and the collection then
read at `SU(2)`, `SU(3)`, `SU(4)`, `Spin(5)`, `Spin(7)`, `Sp(3)`,
`Spin(8)`, `G₂`, `F₄` and `E₆` through the theorem routes, each
member's twelve hypotheses and its square row's Casimir positivity
one kernel evaluation and the routes reading its projections, at
the member's own Casimir scale, adjoint dimension, `θ` weight,
channel positions, first, pair and cubic moments and `θ`-count in
the square.  The refusals isolate the binders one at a time: the
completeness at a row grown by a second unit, the drift at one
channel's Casimir raised, the normalization at every Casimir
raised, the `θ` weight at a forged base — each parting the side or
the margin — beside the index datum pins at the unit and `θ`
channels; and the collection's first, cubic and `θ`-count reads at
forged label equalities and involutions, each parting its read and
the `τ⁴` read, with the pair read's refusal-free record beside
them, the fold reading one value across its forgery.  The jet's
pairing reads at `SU(2)`: `⟨ψ₂, q₁² q₂²⟩ = 523/2268`, the pairing
polynomial at `(2, 2)` the unit, one and `545/567 = D₂₂ + 1/8`, the
gram `1, 0, 1/8`, the jet moments the normalized pairing decided and
through `jetRead` at every member, a window's read at a far datum
through `jetWindow`, and the gram-side refusals — the `τ²` and `τ⁴`
reads parting at the nonunit `θ`'s forgery and the `τ⁴` read at the
pair read's, the window's `τ⁴` read at both.  The tail's residual tier
at a two-key pencil fixture: the jet's identity at the ray `[5 : 32]`,
the solve floor at `4`, the residual's weight against the magnetic
square cap `65`, the count's fold of squares at two copies, and the
off-line bound at the drift's clearing `879` — each decided and
through its theorem, with the refusals parting the three reads, the
floor, the cap, the perpendicularity and the clearance one at a time.
-/

open ground fusion fourpoint

/-! `SU(2)`: the channel list, the pair fold and the pair sum at
their values. -/

example : chanList (dataA 2)
    = [(posOfSucc 4, posOfSucc 71), (posOfSucc 2, posOfSucc 55),
       (Pos.one, posOfSucc 47)] := by decide +kernel
example : ((pairFold (dataA 2)).1.scale 1134).oneValue
    ((BPair.ofPos 145).scale (pairFold (dataA 2)).2) := by decide +kernel

/-- The side at `SU(2)`, decided raw and through the theorem. -/
example : ((BPair.ofPos 8 * (pairFold (dataA 2)).1).scale
      ((pairRead (dataA 2)).2 * (posOfSucc 2 * posOfSucc 2
        * (posOfSucc 2 * posOfSucc 2)))).oneValue
    (((BPair.ofPos Pos.one).scale
        ((pairRead (dataA 2)).2 * (posOfSucc 2 * posOfSucc 2
          * (posOfSucc 2 * posOfSucc 2)))
      + (pairRead (dataA 2)).1).scale (pairFold (dataA 2)).2) := by
  decide +kernel
example : ((BPair.ofPos 8 * (pairFold (dataA 2)).1).scale
      ((pairRead (dataA 2)).2 * (posOfSucc 2 * posOfSucc 2
        * (posOfSucc 2 * posOfSucc 2)))).oneValue
    (((BPair.ofPos Pos.one).scale
        ((pairRead (dataA 2)).2 * (posOfSucc 2 * posOfSucc 2
          * (posOfSucc 2 * posOfSucc 2)))
      + (pairRead (dataA 2)).1).scale (pairFold (dataA 2)).2) :=
  side (dataA 2) 7 2 rfl (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The margin at `SU(2)` decided raw: `1 + 1/1134 ≤ 8 S`; the
fold's own value `26/1134` reads exact and one beyond refuses. -/
example : ((BPair.ofPos Pos.one).scale
      (42 * (posOfSucc 2 * posOfSucc 2 * posOfSucc 2))
    + BPair.ofNat (dataA 2).c1).scale (pairFold (dataA 2)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataA 2)).1).scale
      (42 * (posOfSucc 2 * posOfSucc 2 * posOfSucc 2)) := by decide +kernel
example : ((BPair.ofPos Pos.one).scale 1134 + BPair.ofPos 26).scale
      (pairFold (dataA 2)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataA 2)).1).scale 1134 := by decide +kernel
example : ¬ (((BPair.ofPos Pos.one).scale 1134 + BPair.ofPos 27).scale
      (pairFold (dataA 2)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataA 2)).1).scale 1134) := by
  decide +kernel

/-- The index datum pins: the unit channel at index `2` and `θ` at
`1`, the unit off index `1`. -/
example : getAt (Pos.one, Pos.one) (chanList (dataA 2)) 2
    = (Pos.one, posOfSucc 47) := by decide +kernel
example : getAt (Pos.one, Pos.one) (chanList (dataA 2)) 1
    = (posOfSucc 2, posOfSucc 55) := by decide +kernel
example : ¬ (getAt (Pos.one, Pos.one) (chanList (dataA 2)) 1
    = (Pos.one, posOfSucc 47)) := by decide +kernel

/-! The refusals, each parting one binder alone at `SU(2)`. -/

/-- The completeness: the row grown by a second unit label keeps
the drift, the normalization and the `θ` weight and parts the
completeness and the side. -/
private def rowGrown : Data places.Shape :=
  { dataA 2 with row := fun a b => (dataA 2).row a b ++ [(dataA 2).unit] }

example : ¬ dimLaw rowGrown rowGrown.theta rowGrown.theta := by decide +kernel
example : driftLaw rowGrown rowGrown.theta := by decide +kernel
example : rowGrown.c2N rowGrown.theta = 7 + 1 := by decide +kernel
example : ¬ ((BPair.ofPos 8 * (pairFold rowGrown).1).scale
      ((pairRead rowGrown).2 * (posOfSucc 2 * posOfSucc 2
        * (posOfSucc 2 * posOfSucc 2)))).oneValue
    (((BPair.ofPos Pos.one).scale
        ((pairRead rowGrown).2 * (posOfSucc 2 * posOfSucc 2
          * (posOfSucc 2 * posOfSucc 2)))
      + (pairRead rowGrown).1).scale (pairFold rowGrown).2) := by
  decide +kernel

/-- The drift: the `2θ` channel's Casimir raised by one keeps the
completeness and the normalization and parts the drift and the
side. -/
private def casRaised : Data places.Shape :=
  { dataA 2 with c2N := fun s =>
      if c2hat.dfQ s == 24 then 25 else c2hat.dfQ s }

example : ¬ driftLaw casRaised casRaised.theta := by decide +kernel
example : dimLaw casRaised casRaised.theta casRaised.theta := by decide +kernel
example : casRaised.c2N casRaised.theta = 7 + 1 := by decide +kernel
example : ¬ ((BPair.ofPos 8 * (pairFold casRaised).1).scale
      ((pairRead casRaised).2 * (posOfSucc 2 * posOfSucc 2
        * (posOfSucc 2 * posOfSucc 2)))).oneValue
    (((BPair.ofPos Pos.one).scale
        ((pairRead casRaised).2 * (posOfSucc 2 * posOfSucc 2
          * (posOfSucc 2 * posOfSucc 2)))
      + (pairRead casRaised).1).scale (pairFold casRaised).2) := by
  decide +kernel

/-- The normalization: every Casimir raised by one keeps both
closures and moves `θ`'s Casimir off the scale, parting the
side. -/
private def casShifted : Data places.Shape :=
  { dataA 2 with c2N := fun s => c2hat.dfQ s + 1 }

example : ¬ (casShifted.c2N casShifted.theta = 7 + 1) := by decide +kernel
example : dimLaw casShifted casShifted.theta casShifted.theta := by decide +kernel
example : driftLaw casShifted casShifted.theta := by decide +kernel
example : ¬ ((BPair.ofPos 8 * (pairFold casShifted).1).scale
      ((pairRead casShifted).2 * (posOfSucc 2 * posOfSucc 2
        * (posOfSucc 2 * posOfSucc 2)))).oneValue
    (((BPair.ofPos Pos.one).scale
        ((pairRead casShifted).2 * (posOfSucc 2 * posOfSucc 2
          * (posOfSucc 2 * posOfSucc 2)))
      + (pairRead casShifted).1).scale (pairFold casShifted).2) := by
  decide +kernel

/-- The `θ` weight: a forged base keeps every closure and the side
and parts the `θ` weight read and the margin. -/
private def baseForged : Data places.Shape := { dataA 2 with c1 := 27 }

example : ¬ (baseForged.c1 * baseForged.dim baseForged.theta = 2 + 1) := by
  decide +kernel
example : ¬ (((BPair.ofPos Pos.one).scale
      (42 * (posOfSucc 2 * posOfSucc 2 * posOfSucc 2))
    + BPair.ofNat baseForged.c1).scale (pairFold baseForged).2
    ≤ (BPair.ofPos 8 * (pairFold baseForged).1).scale
      (42 * (posOfSucc 2 * posOfSucc 2 * posOfSucc 2))) := by decide +kernel

/-! The collection's conclusion at a datum, its three reads named:
the partition fold's unit at `τ⁰` and at `τ²`, and its `τ⁴` read
`c₁² ⟨S : [1 : 8]⟩` at the pair fold. -/

/-- The `τ⁰` read: the partition fold's key zero is the unit. -/
private def tauZero (F : Data places.Shape) : Prop :=
  (getAt bpairQOps.unit
    (kappa4 (poly.polyO bpairQOps) (jetMoment F)) 0).1.oneValue BPair.unit

private instance (F : Data places.Shape) : Decidable (tauZero F) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The `τ²` read: the partition fold's key one is the unit. -/
private def tauTwo (F : Data places.Shape) : Prop :=
  (getAt bpairQOps.unit
    (kappa4 (poly.polyO bpairQOps) (jetMoment F)) 1).1.oneValue BPair.unit

private instance (F : Data places.Shape) : Decidable (tauTwo F) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The `τ⁴` read: the partition fold's key two is
`c₁² ⟨S : [1 : 8]⟩` at the pair fold. -/
private def tauFour (F : Data places.Shape) : Prop :=
  ((getAt bpairQOps.unit
        (kappa4 (poly.polyO bpairQOps) (jetMoment F)) 2).1.scale
        (8 * (pairFold F).2)).oneValue
      (((BPair.ofNat F.c1 * BPair.ofNat F.c1)
          * ((pairFold F).1.scale 8 + (BPair.ofPos (pairFold F).2).swap)).scale
        (getAt bpairQOps.unit
          (kappa4 (poly.polyO bpairQOps) (jetMoment F)) 2).2)

private instance (F : Data places.Shape) : Decidable (tauFour F) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-- The jet moments as the normalized pairing at a datum, the three
key reads of `jetRead`'s conclusion. -/
private def jetReadAt (F : Data places.Shape) (a b : Nat) : Prop :=
  bpairQRead.rel (getAt bpairQOps.unit (jetPair F a b) 0)
      (getAt bpairQOps.unit
        ((poly.polyO bpairQOps).mul (jetMoment F a b) (jetPair F 0 0)) 0)
    ∧ bpairQRead.rel (getAt bpairQOps.unit (jetPair F a b) 1)
      (getAt bpairQOps.unit
        ((poly.polyO bpairQOps).mul (jetMoment F a b) (jetPair F 0 0)) 1)
    ∧ bpairQRead.rel (getAt bpairQOps.unit (jetPair F a b) 2)
      (getAt bpairQOps.unit
        ((poly.polyO bpairQOps).mul (jetMoment F a b) (jetPair F 0 0)) 2)

private instance (F : Data places.Shape) (a b : Nat) : Decidable (jetReadAt F a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! The margin and the collection through the theorem routes at ten
members, each at one kernel evaluation of its thirteen reads: the
routes' twelve hypotheses and the square row's Casimir positivity,
`con:fusion`'s `casPos` at every channel of `row θ θ`, the datum
`chanTerm`'s vacant-Casimir arm reads off at the members. -/

private theorem hypsA2 : (dataA 2).c2D = 7 + 1
    ∧ (dataA 2).dim (dataA 2).theta = 2 + 1
    ∧ (dataA 2).c2N (dataA 2).theta = 7 + 1
    ∧ dimLaw (dataA 2) (dataA 2).theta (dataA 2).theta
    ∧ driftLaw (dataA 2) (dataA 2).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataA 2)) 2
        = (Pos.one, posOfSucc (6 * 7 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataA 2)) 1
        = (posOfSucc 2, posOfSucc (6 * 7 + 5 + (7 + 1)))
    ∧ (dataA 2).c1 * (dataA 2).dim (dataA 2).theta = 2 + 1
    ∧ moment (dataA 2) 1 = 0
    ∧ moment (dataA 2) 2 = 1
    ∧ moment (dataA 2) 3 = (dataA 2).c1
    ∧ powCount (dataA 2) 2 (dataA 2).theta = (dataA 2).c1
    ∧ ((dataA 2).row (dataA 2).theta (dataA 2).theta).all
        (fun k => if casPos (dataA 2) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 2 * posOfSucc 2 * posOfSucc 2))
    + BPair.ofNat (dataA 2).c1).scale (pairFold (dataA 2)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataA 2)).1).scale (42 * (posOfSucc 2 * posOfSucc 2 * posOfSucc 2)) :=
  margin (dataA 2) 7 2 2 hypsA2.1 hypsA2.2.1 hypsA2.2.2.1
    hypsA2.2.2.2.1 hypsA2.2.2.2.2.1 2 1 hypsA2.2.2.2.2.2.1
    hypsA2.2.2.2.2.2.2.1 hypsA2.2.2.2.2.2.2.2.1

example : tauZero (dataA 2) ∧ tauTwo (dataA 2) ∧ tauFour (dataA 2) :=
  collection (dataA 2) hypsA2.2.2.2.2.2.2.2.2.1 hypsA2.2.2.2.2.2.2.2.2.2.1
    hypsA2.2.2.2.2.2.2.2.2.2.2.1 hypsA2.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataA 2) 2 2 :=
  jetRead (dataA 2) 2 2 hypsA2.2.2.2.2.2.2.2.2.1 hypsA2.2.2.2.2.2.2.2.2.2.1

private theorem hypsA3 : (dataA 3).c2D = 17 + 1
    ∧ (dataA 3).dim (dataA 3).theta = 7 + 1
    ∧ (dataA 3).c2N (dataA 3).theta = 17 + 1
    ∧ dimLaw (dataA 3) (dataA 3).theta (dataA 3).theta
    ∧ driftLaw (dataA 3) (dataA 3).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataA 3)) 4
        = (Pos.one, posOfSucc (6 * 17 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataA 3)) 3
        = (posOfSucc 15, posOfSucc (6 * 17 + 5 + (17 + 1)))
    ∧ (dataA 3).c1 * (dataA 3).dim (dataA 3).theta = 15 + 1
    ∧ moment (dataA 3) 1 = 0
    ∧ moment (dataA 3) 2 = 1
    ∧ moment (dataA 3) 3 = (dataA 3).c1
    ∧ powCount (dataA 3) 2 (dataA 3).theta = (dataA 3).c1
    ∧ ((dataA 3).row (dataA 3).theta (dataA 3).theta).all
        (fun k => if casPos (dataA 3) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 7 * posOfSucc 7 * posOfSucc 7))
    + BPair.ofNat (dataA 3).c1).scale (pairFold (dataA 3)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataA 3)).1).scale (42 * (posOfSucc 7 * posOfSucc 7 * posOfSucc 7)) :=
  margin (dataA 3) 17 7 15 hypsA3.1 hypsA3.2.1 hypsA3.2.2.1
    hypsA3.2.2.2.1 hypsA3.2.2.2.2.1 4 3 hypsA3.2.2.2.2.2.1
    hypsA3.2.2.2.2.2.2.1 hypsA3.2.2.2.2.2.2.2.1

example : tauZero (dataA 3) ∧ tauTwo (dataA 3) ∧ tauFour (dataA 3) :=
  collection (dataA 3) hypsA3.2.2.2.2.2.2.2.2.1 hypsA3.2.2.2.2.2.2.2.2.2.1
    hypsA3.2.2.2.2.2.2.2.2.2.2.1 hypsA3.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataA 3) 2 2 :=
  jetRead (dataA 3) 2 2 hypsA3.2.2.2.2.2.2.2.2.1 hypsA3.2.2.2.2.2.2.2.2.2.1

private theorem hypsA4 : (dataA 4).c2D = 31 + 1
    ∧ (dataA 4).dim (dataA 4).theta = 14 + 1
    ∧ (dataA 4).c2N (dataA 4).theta = 31 + 1
    ∧ dimLaw (dataA 4) (dataA 4).theta (dataA 4).theta
    ∧ driftLaw (dataA 4) (dataA 4).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataA 4)) 5
        = (Pos.one, posOfSucc (6 * 31 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataA 4)) 4
        = (posOfSucc 29, posOfSucc (6 * 31 + 5 + (31 + 1)))
    ∧ (dataA 4).c1 * (dataA 4).dim (dataA 4).theta = 29 + 1
    ∧ moment (dataA 4) 1 = 0
    ∧ moment (dataA 4) 2 = 1
    ∧ moment (dataA 4) 3 = (dataA 4).c1
    ∧ powCount (dataA 4) 2 (dataA 4).theta = (dataA 4).c1
    ∧ ((dataA 4).row (dataA 4).theta (dataA 4).theta).all
        (fun k => if casPos (dataA 4) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 14 * posOfSucc 14 * posOfSucc 14))
    + BPair.ofNat (dataA 4).c1).scale (pairFold (dataA 4)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataA 4)).1).scale (42 * (posOfSucc 14 * posOfSucc 14 * posOfSucc 14)) :=
  margin (dataA 4) 31 14 29 hypsA4.1 hypsA4.2.1 hypsA4.2.2.1
    hypsA4.2.2.2.1 hypsA4.2.2.2.2.1 5 4 hypsA4.2.2.2.2.2.1
    hypsA4.2.2.2.2.2.2.1 hypsA4.2.2.2.2.2.2.2.1

example : tauZero (dataA 4) ∧ tauTwo (dataA 4) ∧ tauFour (dataA 4) :=
  collection (dataA 4) hypsA4.2.2.2.2.2.2.2.2.1 hypsA4.2.2.2.2.2.2.2.2.2.1
    hypsA4.2.2.2.2.2.2.2.2.2.2.1 hypsA4.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataA 4) 2 2 :=
  jetRead (dataA 4) 2 2 hypsA4.2.2.2.2.2.2.2.2.1 hypsA4.2.2.2.2.2.2.2.2.2.1

private theorem hypsB2 : (dataB 2).c2D = 23 + 1
    ∧ (dataB 2).dim (dataB 2).theta = 9 + 1
    ∧ (dataB 2).c2N (dataB 2).theta = 23 + 1
    ∧ dimLaw (dataB 2) (dataB 2).theta (dataB 2).theta
    ∧ driftLaw (dataB 2) (dataB 2).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataB 2)) 0
        = (Pos.one, posOfSucc (6 * 23 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataB 2)) 1
        = (posOfSucc 9, posOfSucc (6 * 23 + 5 + (23 + 1)))
    ∧ (dataB 2).c1 * (dataB 2).dim (dataB 2).theta = 9 + 1
    ∧ moment (dataB 2) 1 = 0
    ∧ moment (dataB 2) 2 = 1
    ∧ moment (dataB 2) 3 = (dataB 2).c1
    ∧ powCount (dataB 2) 2 (dataB 2).theta = (dataB 2).c1
    ∧ ((dataB 2).row (dataB 2).theta (dataB 2).theta).all
        (fun k => if casPos (dataB 2) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 9 * posOfSucc 9 * posOfSucc 9))
    + BPair.ofNat (dataB 2).c1).scale (pairFold (dataB 2)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataB 2)).1).scale (42 * (posOfSucc 9 * posOfSucc 9 * posOfSucc 9)) :=
  margin (dataB 2) 23 9 9 hypsB2.1 hypsB2.2.1 hypsB2.2.2.1
    hypsB2.2.2.2.1 hypsB2.2.2.2.2.1 0 1 hypsB2.2.2.2.2.2.1
    hypsB2.2.2.2.2.2.2.1 hypsB2.2.2.2.2.2.2.2.1

example : tauZero (dataB 2) ∧ tauTwo (dataB 2) ∧ tauFour (dataB 2) :=
  collection (dataB 2) hypsB2.2.2.2.2.2.2.2.2.1 hypsB2.2.2.2.2.2.2.2.2.2.1
    hypsB2.2.2.2.2.2.2.2.2.2.2.1 hypsB2.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataB 2) 2 2 :=
  jetRead (dataB 2) 2 2 hypsB2.2.2.2.2.2.2.2.2.1 hypsB2.2.2.2.2.2.2.2.2.2.1

private theorem hypsB3 : (dataB 3).c2D = 39 + 1
    ∧ (dataB 3).dim (dataB 3).theta = 20 + 1
    ∧ (dataB 3).c2N (dataB 3).theta = 39 + 1
    ∧ dimLaw (dataB 3) (dataB 3).theta (dataB 3).theta
    ∧ driftLaw (dataB 3) (dataB 3).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataB 3)) 0
        = (Pos.one, posOfSucc (6 * 39 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataB 3)) 2
        = (posOfSucc 20, posOfSucc (6 * 39 + 5 + (39 + 1)))
    ∧ (dataB 3).c1 * (dataB 3).dim (dataB 3).theta = 20 + 1
    ∧ moment (dataB 3) 1 = 0
    ∧ moment (dataB 3) 2 = 1
    ∧ moment (dataB 3) 3 = (dataB 3).c1
    ∧ powCount (dataB 3) 2 (dataB 3).theta = (dataB 3).c1
    ∧ ((dataB 3).row (dataB 3).theta (dataB 3).theta).all
        (fun k => if casPos (dataB 3) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 20 * posOfSucc 20 * posOfSucc 20))
    + BPair.ofNat (dataB 3).c1).scale (pairFold (dataB 3)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataB 3)).1).scale (42 * (posOfSucc 20 * posOfSucc 20 * posOfSucc 20)) :=
  margin (dataB 3) 39 20 20 hypsB3.1 hypsB3.2.1 hypsB3.2.2.1
    hypsB3.2.2.2.1 hypsB3.2.2.2.2.1 0 2 hypsB3.2.2.2.2.2.1
    hypsB3.2.2.2.2.2.2.1 hypsB3.2.2.2.2.2.2.2.1

example : tauZero (dataB 3) ∧ tauTwo (dataB 3) ∧ tauFour (dataB 3) :=
  collection (dataB 3) hypsB3.2.2.2.2.2.2.2.2.1 hypsB3.2.2.2.2.2.2.2.2.2.1
    hypsB3.2.2.2.2.2.2.2.2.2.2.1 hypsB3.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataB 3) 2 2 :=
  jetRead (dataB 3) 2 2 hypsB3.2.2.2.2.2.2.2.2.1 hypsB3.2.2.2.2.2.2.2.2.2.1

private theorem hypsC3 : (dataC 3).c2D = 31 + 1
    ∧ (dataC 3).dim (dataC 3).theta = 20 + 1
    ∧ (dataC 3).c2N (dataC 3).theta = 31 + 1
    ∧ dimLaw (dataC 3) (dataC 3).theta (dataC 3).theta
    ∧ driftLaw (dataC 3) (dataC 3).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataC 3)) 0
        = (Pos.one, posOfSucc (6 * 31 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataC 3)) 3
        = (posOfSucc 20, posOfSucc (6 * 31 + 5 + (31 + 1)))
    ∧ (dataC 3).c1 * (dataC 3).dim (dataC 3).theta = 20 + 1
    ∧ moment (dataC 3) 1 = 0
    ∧ moment (dataC 3) 2 = 1
    ∧ moment (dataC 3) 3 = (dataC 3).c1
    ∧ powCount (dataC 3) 2 (dataC 3).theta = (dataC 3).c1
    ∧ ((dataC 3).row (dataC 3).theta (dataC 3).theta).all
        (fun k => if casPos (dataC 3) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 20 * posOfSucc 20 * posOfSucc 20))
    + BPair.ofNat (dataC 3).c1).scale (pairFold (dataC 3)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataC 3)).1).scale (42 * (posOfSucc 20 * posOfSucc 20 * posOfSucc 20)) :=
  margin (dataC 3) 31 20 20 hypsC3.1 hypsC3.2.1 hypsC3.2.2.1
    hypsC3.2.2.2.1 hypsC3.2.2.2.2.1 0 3 hypsC3.2.2.2.2.2.1
    hypsC3.2.2.2.2.2.2.1 hypsC3.2.2.2.2.2.2.2.1

example : tauZero (dataC 3) ∧ tauTwo (dataC 3) ∧ tauFour (dataC 3) :=
  collection (dataC 3) hypsC3.2.2.2.2.2.2.2.2.1 hypsC3.2.2.2.2.2.2.2.2.2.1
    hypsC3.2.2.2.2.2.2.2.2.2.2.1 hypsC3.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataC 3) 2 2 :=
  jetRead (dataC 3) 2 2 hypsC3.2.2.2.2.2.2.2.2.1 hypsC3.2.2.2.2.2.2.2.2.2.1

private theorem hypsD4 : (dataD 4).c2D = 95 + 1
    ∧ (dataD 4).dim (dataD 4).theta = 27 + 1
    ∧ (dataD 4).c2N (dataD 4).theta = 95 + 1
    ∧ dimLaw (dataD 4) (dataD 4).theta (dataD 4).theta
    ∧ driftLaw (dataD 4) (dataD 4).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataD 4)) 0
        = (Pos.one, posOfSucc (6 * 95 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataD 4)) 3
        = (posOfSucc 27, posOfSucc (6 * 95 + 5 + (95 + 1)))
    ∧ (dataD 4).c1 * (dataD 4).dim (dataD 4).theta = 27 + 1
    ∧ moment (dataD 4) 1 = 0
    ∧ moment (dataD 4) 2 = 1
    ∧ moment (dataD 4) 3 = (dataD 4).c1
    ∧ powCount (dataD 4) 2 (dataD 4).theta = (dataD 4).c1
    ∧ ((dataD 4).row (dataD 4).theta (dataD 4).theta).all
        (fun k => if casPos (dataD 4) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 27 * posOfSucc 27 * posOfSucc 27))
    + BPair.ofNat (dataD 4).c1).scale (pairFold (dataD 4)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataD 4)).1).scale (42 * (posOfSucc 27 * posOfSucc 27 * posOfSucc 27)) :=
  margin (dataD 4) 95 27 27 hypsD4.1 hypsD4.2.1 hypsD4.2.2.1
    hypsD4.2.2.2.1 hypsD4.2.2.2.2.1 0 3 hypsD4.2.2.2.2.2.1
    hypsD4.2.2.2.2.2.2.1 hypsD4.2.2.2.2.2.2.2.1

example : tauZero (dataD 4) ∧ tauTwo (dataD 4) ∧ tauFour (dataD 4) :=
  collection (dataD 4) hypsD4.2.2.2.2.2.2.2.2.1 hypsD4.2.2.2.2.2.2.2.2.2.1
    hypsD4.2.2.2.2.2.2.2.2.2.2.1 hypsD4.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataD 4) 2 2 :=
  jetRead (dataD 4) 2 2 hypsD4.2.2.2.2.2.2.2.2.1 hypsD4.2.2.2.2.2.2.2.2.2.1

private theorem hypsG2 : (dataG2).c2D = 47 + 1
    ∧ (dataG2).dim (dataG2).theta = 13 + 1
    ∧ (dataG2).c2N (dataG2).theta = 47 + 1
    ∧ dimLaw (dataG2) (dataG2).theta (dataG2).theta
    ∧ driftLaw (dataG2) (dataG2).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataG2)) 0
        = (Pos.one, posOfSucc (6 * 47 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataG2)) 1
        = (posOfSucc 13, posOfSucc (6 * 47 + 5 + (47 + 1)))
    ∧ (dataG2).c1 * (dataG2).dim (dataG2).theta = 13 + 1
    ∧ moment (dataG2) 1 = 0
    ∧ moment (dataG2) 2 = 1
    ∧ moment (dataG2) 3 = (dataG2).c1
    ∧ powCount (dataG2) 2 (dataG2).theta = (dataG2).c1
    ∧ ((dataG2).row (dataG2).theta (dataG2).theta).all
        (fun k => if casPos (dataG2) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 13 * posOfSucc 13 * posOfSucc 13))
    + BPair.ofNat (dataG2).c1).scale (pairFold (dataG2)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataG2)).1).scale (42 * (posOfSucc 13 * posOfSucc 13 * posOfSucc 13)) :=
  margin (dataG2) 47 13 13 hypsG2.1 hypsG2.2.1 hypsG2.2.2.1
    hypsG2.2.2.2.1 hypsG2.2.2.2.2.1 0 1 hypsG2.2.2.2.2.2.1
    hypsG2.2.2.2.2.2.2.1 hypsG2.2.2.2.2.2.2.2.1

example : tauZero (dataG2) ∧ tauTwo (dataG2) ∧ tauFour (dataG2) :=
  collection (dataG2) hypsG2.2.2.2.2.2.2.2.2.1 hypsG2.2.2.2.2.2.2.2.2.2.1
    hypsG2.2.2.2.2.2.2.2.2.2.2.1 hypsG2.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataG2) 2 2 :=
  jetRead (dataG2) 2 2 hypsG2.2.2.2.2.2.2.2.2.1 hypsG2.2.2.2.2.2.2.2.2.2.1

private theorem hypsF4 : (dataF4).c2D = 35 + 1
    ∧ (dataF4).dim (dataF4).theta = 51 + 1
    ∧ (dataF4).c2N (dataF4).theta = 35 + 1
    ∧ dimLaw (dataF4) (dataF4).theta (dataF4).theta
    ∧ driftLaw (dataF4) (dataF4).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataF4)) 0
        = (Pos.one, posOfSucc (6 * 35 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataF4)) 3
        = (posOfSucc 51, posOfSucc (6 * 35 + 5 + (35 + 1)))
    ∧ (dataF4).c1 * (dataF4).dim (dataF4).theta = 51 + 1
    ∧ moment (dataF4) 1 = 0
    ∧ moment (dataF4) 2 = 1
    ∧ moment (dataF4) 3 = (dataF4).c1
    ∧ powCount (dataF4) 2 (dataF4).theta = (dataF4).c1
    ∧ ((dataF4).row (dataF4).theta (dataF4).theta).all
        (fun k => if casPos (dataF4) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 51 * posOfSucc 51 * posOfSucc 51))
    + BPair.ofNat (dataF4).c1).scale (pairFold (dataF4)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataF4)).1).scale (42 * (posOfSucc 51 * posOfSucc 51 * posOfSucc 51)) :=
  margin (dataF4) 35 51 51 hypsF4.1 hypsF4.2.1 hypsF4.2.2.1
    hypsF4.2.2.2.1 hypsF4.2.2.2.2.1 0 3 hypsF4.2.2.2.2.2.1
    hypsF4.2.2.2.2.2.2.1 hypsF4.2.2.2.2.2.2.2.1

example : tauZero (dataF4) ∧ tauTwo (dataF4) ∧ tauFour (dataF4) :=
  collection (dataF4) hypsF4.2.2.2.2.2.2.2.2.1 hypsF4.2.2.2.2.2.2.2.2.2.1
    hypsF4.2.2.2.2.2.2.2.2.2.2.1 hypsF4.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataF4) 2 2 :=
  jetRead (dataF4) 2 2 hypsF4.2.2.2.2.2.2.2.2.1 hypsF4.2.2.2.2.2.2.2.2.2.1

private theorem hypsE6 : (dataE6).c2D = 143 + 1
    ∧ (dataE6).dim (dataE6).theta = 77 + 1
    ∧ (dataE6).c2N (dataE6).theta = 143 + 1
    ∧ dimLaw (dataE6) (dataE6).theta (dataE6).theta
    ∧ driftLaw (dataE6) (dataE6).theta
    ∧ getAt (Pos.one, Pos.one) (chanList (dataE6)) 0
        = (Pos.one, posOfSucc (6 * 143 + 5))
    ∧ getAt (Pos.one, Pos.one) (chanList (dataE6)) 2
        = (posOfSucc 77, posOfSucc (6 * 143 + 5 + (143 + 1)))
    ∧ (dataE6).c1 * (dataE6).dim (dataE6).theta = 77 + 1
    ∧ moment (dataE6) 1 = 0
    ∧ moment (dataE6) 2 = 1
    ∧ moment (dataE6) 3 = (dataE6).c1
    ∧ powCount (dataE6) 2 (dataE6).theta = (dataE6).c1
    ∧ ((dataE6).row (dataE6).theta (dataE6).theta).all
        (fun k => if casPos (dataE6) k then true else false) = true := by
  decide +kernel

example : ((BPair.ofPos Pos.one).scale (42 * (posOfSucc 77 * posOfSucc 77 * posOfSucc 77))
    + BPair.ofNat (dataE6).c1).scale (pairFold (dataE6)).2
    ≤ (BPair.ofPos 8 * (pairFold (dataE6)).1).scale (42 * (posOfSucc 77 * posOfSucc 77 * posOfSucc 77)) :=
  margin (dataE6) 143 77 77 hypsE6.1 hypsE6.2.1 hypsE6.2.2.1
    hypsE6.2.2.2.1 hypsE6.2.2.2.2.1 0 2 hypsE6.2.2.2.2.2.1
    hypsE6.2.2.2.2.2.2.1 hypsE6.2.2.2.2.2.2.2.1

example : tauZero (dataE6) ∧ tauTwo (dataE6) ∧ tauFour (dataE6) :=
  collection (dataE6) hypsE6.2.2.2.2.2.2.2.2.1 hypsE6.2.2.2.2.2.2.2.2.2.1
    hypsE6.2.2.2.2.2.2.2.2.2.2.1 hypsE6.2.2.2.2.2.2.2.2.2.2.2.1

example : jetReadAt (dataE6) 2 2 :=
  jetRead (dataE6) 2 2 hypsE6.2.2.2.2.2.2.2.2.1 hypsE6.2.2.2.2.2.2.2.2.2.1

/-! The jet tier at `SU(2)`: the free moments `1, 0, 1, 1, 3` (the
square's pairing three at the three channels), the pair's own count
in the square one, the jet moments at their displayed coefficients,
and the partition fold at the displayed orders — the unit at `τ⁰`
and `τ²`, and `c₁²⟨S : [1 : 8]⟩ = 13/4536` at `τ⁴`, decided exact
at `13` and refused one beyond. -/

example : moment (dataA 2) 0 = 1 := by decide +kernel
example : moment (dataA 2) 1 = 0 := by decide +kernel
example : moment (dataA 2) 2 = 1 := by decide +kernel
example : moment (dataA 2) 3 = 1 := by decide +kernel
example : moment (dataA 2) 4 = 3 := by decide +kernel
example : powCount (dataA 2) 2 (dataA 2).theta = 1 := by decide +kernel
example : powCount (dataA 2) 2 [4, 0] = 1 := by decide +kernel
example : powCount (dataA 2) 0 (dataA 2).theta = 0 := by decide +kernel
example : jetMoment (dataA 2) 1 0
    = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), jetD (dataA 2) 1 0] := by
  decide +kernel
example : jetMoment (dataA 2) 2 2
    = [(BPair.ofNat 1, Pos.one), (BPair.ofNat 2, 2), jetD (dataA 2) 2 2] := by
  decide +kernel
/-- `D₂₂ = 3793/4536` and `D₂₀ = 7/24` at `SU(2)`. -/
example : ((jetD (dataA 2) 2 2).1.scale 4536).oneValue
    ((BPair.ofPos 3793).scale (jetD (dataA 2) 2 2).2) := by decide +kernel
example : ((jetD (dataA 2) 2 0).1.scale 24).oneValue
    ((BPair.ofPos 7).scale (jetD (dataA 2) 2 0).2) := by decide +kernel
example : tauZero (dataA 2) := by decide +kernel
example : tauTwo (dataA 2) := by decide +kernel
example : ((getAt bpairQOps.unit
      (kappa4 (poly.polyO bpairQOps) (jetMoment (dataA 2))) 2).1.scale 4536).oneValue
    ((BPair.ofPos 13).scale (getAt bpairQOps.unit
      (kappa4 (poly.polyO bpairQOps) (jetMoment (dataA 2))) 2).2) := by
  decide +kernel
example : ¬ (((getAt bpairQOps.unit
      (kappa4 (poly.polyO bpairQOps) (jetMoment (dataA 2))) 2).1.scale 4536).oneValue
    ((BPair.ofPos 14).scale (getAt bpairQOps.unit
      (kappa4 (poly.polyO bpairQOps) (jetMoment (dataA 2))) 2).2)) := by
  decide +kernel

/-! The jet's pairing reads at `SU(2)`: the module's first-order read
`⟨ψ₁, q₁³ q₂²⟩ = 1`, the second-order solve's `⟨ψ₂, q₁² q₂²⟩ = 523/2268`
(the single-plaquette channels' `8/3` at `[1 : 16]` with the pair
sectors' `145/2268`, half the pair fold), the pairing polynomial at
`(2, 2)` the unit, one and `545/567` at its three keys — `D₂₂ + 1/8`
exactly — and the gram `1, 0, 1/8`; the jet moments then read as the
normalized pairing through the theorem at the members, and a window's
read at a far datum through `jetWindow`. -/

example : ((oneRead (dataA 2) 3 2).1.scale 1).oneValue
    ((BPair.ofPos 1).scale (oneRead (dataA 2) 3 2).2) := by decide +kernel
example : ((twoRead (dataA 2) 2 2).1.scale 2268).oneValue
    ((BPair.ofPos 523).scale (twoRead (dataA 2) 2 2).2) := by decide +kernel
example : ((getAt bpairQOps.unit (jetPair (dataA 2) 2 2) 0).1.scale 1).oneValue
    ((BPair.ofPos 1).scale (getAt bpairQOps.unit (jetPair (dataA 2) 2 2) 0).2) := by
  decide +kernel
example : ((getAt bpairQOps.unit (jetPair (dataA 2) 2 2) 1).1.scale 1).oneValue
    ((BPair.ofPos 1).scale (getAt bpairQOps.unit (jetPair (dataA 2) 2 2) 1).2) := by
  decide +kernel
example : ((getAt bpairQOps.unit (jetPair (dataA 2) 2 2) 2).1.scale 567).oneValue
    ((BPair.ofPos 545).scale (getAt bpairQOps.unit (jetPair (dataA 2) 2 2) 2).2) := by
  decide +kernel
example : bpairQRead.rel (getAt bpairQOps.unit (jetPair (dataA 2) 2 2) 2)
    (BPair.addQ (jetD (dataA 2) 2 2) (BPair.ofNat 1, 8)) := by decide +kernel
example : (getAt bpairQOps.unit (jetPair (dataA 2) 0 0) 0) = (BPair.ofNat 1, Pos.one) := by
  decide +kernel
example : bpairQRead.rel (getAt bpairQOps.unit (jetPair (dataA 2) 0 0) 1) bpairQOps.unit := by
  decide +kernel
example : bpairQRead.rel (getAt bpairQOps.unit (jetPair (dataA 2) 0 0) 2) (BPair.ofNat 1, 8) := by
  decide +kernel

example : jetReadAt (dataA 2) 2 2 := by decide +kernel
example : jetReadAt (dataA 2) 1 0 := by decide +kernel

/-- A window's read at a far datum, the three key reads of
`jetWindow`'s conclusion. -/
private def jetWindowAt (F : Data places.Shape) (a b : Nat) (f : BPair × Pos) : Prop :=
  bpairQRead.rel (getAt bpairQOps.unit (farPair F a b f) 0)
      (getAt bpairQOps.unit
        ((poly.polyO bpairQOps).mul (jetMoment F a b) (farPair F 0 0 f)) 0)
    ∧ bpairQRead.rel (getAt bpairQOps.unit (farPair F a b f) 1)
      (getAt bpairQOps.unit
        ((poly.polyO bpairQOps).mul (jetMoment F a b) (farPair F 0 0 f)) 1)
    ∧ bpairQRead.rel (getAt bpairQOps.unit (farPair F a b f) 2)
      (getAt bpairQOps.unit
        ((poly.polyO bpairQOps).mul (jetMoment F a b) (farPair F 0 0 f)) 2)

private instance (F : Data places.Shape) (a b : Nat) (f : BPair × Pos) :
    Decidable (jetWindowAt F a b f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A window's read at a far datum, decided and through the theorem. -/
example : jetWindowAt (dataA 2) 2 2 (BPair.ofNat 3, 5) := by decide +kernel
example : jetWindowAt (dataA 2) 2 2 (BPair.ofNat 3, 5) :=
  jetWindow (dataA 2) 2 2 (BPair.ofNat 3, 5) (by decide +kernel) (by decide +kernel)

/-! The collection's refusals, each parting one read alone at
`SU(2)` with the `τ⁴` read parting beside it, and the pair read's
refusal-free record. -/

/-- The nonunit `θ`: `θ` read equal to the unit one way parts the
first moment alone, the `τ⁴` read with it, and the jet's `τ²` and
`τ⁴` reads at the gram and the window's `τ⁴` read — the unit read is
binder-free, one value at every datum. -/
private def unitTheta : Data places.Shape :=
  { dataA 2 with
    eqL := fun a b => (dataA 2).eqL a b
      || ((dataA 2).eqL a [2, 0] && (dataA 2).eqL b [0, 0]),
    eqLRefl := fun l => by
      show ((dataA 2).eqL l l || _) = true
      rw [(dataA 2).eqLRefl l]
      rfl }

example : ¬ (moment unitTheta 1 = 0) := by decide +kernel
example : moment unitTheta 3 = unitTheta.c1 := by decide +kernel
example : powCount unitTheta 2 unitTheta.theta = unitTheta.c1 := by decide +kernel
example : ¬ tauFour unitTheta := by decide +kernel
example : bpairQRead.rel (getAt bpairQOps.unit (jetPair unitTheta 0 0) 0)
    (getAt bpairQOps.unit
      ((poly.polyO bpairQOps).mul (jetMoment unitTheta 0 0) (jetPair unitTheta 0 0)) 0) := by
  decide +kernel
example : ¬ bpairQRead.rel (getAt bpairQOps.unit (jetPair unitTheta 0 0) 1)
    (getAt bpairQOps.unit
      ((poly.polyO bpairQOps).mul (jetMoment unitTheta 0 0) (jetPair unitTheta 0 0)) 1) := by
  decide +kernel
example : ¬ bpairQRead.rel (getAt bpairQOps.unit (jetPair unitTheta 0 0) 2)
    (getAt bpairQOps.unit
      ((poly.polyO bpairQOps).mul (jetMoment unitTheta 0 0) (jetPair unitTheta 0 0)) 2) := by
  decide +kernel
example : ¬ bpairQRead.rel (getAt bpairQOps.unit (farPair unitTheta 0 0 (BPair.ofNat 3, 5)) 2)
    (getAt bpairQOps.unit
      ((poly.polyO bpairQOps).mul (jetMoment unitTheta 0 0)
        (farPair unitTheta 0 0 (BPair.ofNat 3, 5))) 2) := by
  decide +kernel

/-- The pair read's refusal-free record: at the involution moved
to `2θ` (its count one at `SU(2)`) the pair read parts alone and
the `τ⁴` read survives.  The record is exact: the partition fold's
key-two read is `c₁² S` against `[c₁² : 8]` joined to
`[m₂² : 8]` against `[m₂³ : 8]` at every family, and the pair read
is the unit law's Kronecker read, one of two values, at either of
which the last join reads equal members — so the binder `m₂ = 1`
is the tex's stated read at `prop:repring`, with the fold reading
one value across its forgery; the jet's `τ⁴` read at the gram and
the window's part at it, the gram's eighth the pair read's, while the
`τ²` read survives. -/
private def dualMoved : Data places.Shape :=
  { dataA 2 with
    dual := fun l => if (dataA 2).eqL l [2, 0] then [4, 0] else (dataA 2).dual l }

example : ¬ (moment dualMoved 2 = 1) := by decide +kernel
example : moment dualMoved 1 = 0 := by decide +kernel
example : moment dualMoved 3 = dualMoved.c1 := by decide +kernel
example : powCount dualMoved 2 dualMoved.theta = dualMoved.c1 := by decide +kernel
example : tauFour dualMoved := by decide +kernel
example : bpairQRead.rel (getAt bpairQOps.unit (jetPair dualMoved 0 0) 1)
    (getAt bpairQOps.unit
      ((poly.polyO bpairQOps).mul (jetMoment dualMoved 0 0) (jetPair dualMoved 0 0)) 1) := by
  decide +kernel
example : ¬ bpairQRead.rel (getAt bpairQOps.unit (jetPair dualMoved 0 0) 2)
    (getAt bpairQOps.unit
      ((poly.polyO bpairQOps).mul (jetMoment dualMoved 0 0) (jetPair dualMoved 0 0)) 2) := by
  decide +kernel
example : ¬ bpairQRead.rel (getAt bpairQOps.unit (farPair dualMoved 0 0 (BPair.ofNat 3, 5)) 2)
    (getAt bpairQOps.unit
      ((poly.polyO bpairQOps).mul (jetMoment dualMoved 0 0)
        (farPair dualMoved 0 0 (BPair.ofNat 3, 5))) 2) := by
  decide +kernel

/-- The cubic read: the involution at `θ`'s full-column twin with
`2θ` read equal to the twin one way parts the cubic moment alone,
and the `τ⁴` read with it. -/
private def cubicMoved : Data places.Shape :=
  { dataA 2 with
    dual := fun l => if (dataA 2).eqL l [2, 0] then [2, 1] else (dataA 2).dual l,
    eqL := fun a b => (dataA 2).eqL a b
      || ((dataA 2).eqL a [4, 0] && b == [2, 1]),
    eqLRefl := fun l => by
      show ((dataA 2).eqL l l || _) = true
      rw [(dataA 2).eqLRefl l]
      rfl }

example : ¬ (moment cubicMoved 3 = cubicMoved.c1) := by decide +kernel
example : moment cubicMoved 1 = 0 := by decide +kernel
example : powCount cubicMoved 2 cubicMoved.theta = cubicMoved.c1 := by decide +kernel
example : ¬ tauFour cubicMoved := by decide +kernel

/-- The square's `θ`-count: the involution at `θ`'s twin with `2θ`
read equal to `θ` one way parts the square's count alone, and the
`τ⁴` read with it. -/
private def squareMoved : Data places.Shape :=
  { dataA 2 with
    dual := fun l => if (dataA 2).eqL l [2, 0] then [2, 1] else (dataA 2).dual l,
    eqL := fun a b => (dataA 2).eqL a b
      || ((dataA 2).eqL a [4, 0] && b == [2, 0]),
    eqLRefl := fun l => by
      show ((dataA 2).eqL l l || _) = true
      rw [(dataA 2).eqLRefl l]
      rfl }

example : ¬ (powCount squareMoved 2 squareMoved.theta = squareMoved.c1) := by
  decide +kernel
example : moment squareMoved 1 = 0 := by decide +kernel
example : moment squareMoved 3 = squareMoved.c1 := by decide +kernel
example : ¬ tauFour squareMoved := by decide +kernel

/-! The tail's residual tier at a two-key pencil: `E = diag(0, 4)`,
`M = [[0, 4], [4, 64]]`, the reads `E𝟏 = 0`, `Eψ₁ = M𝟏` and
`4Eψ₂ + 16·𝟏 = 4Mψ₁` at `ψ₁ = (0, 1)`, `ψ₂ = (0, 16)`, `#p = 16`, the
ray `τ = [5 : 32]`; the cleared pencil `1024 E − 25 M` has the roots
`−4` and `2500`, the ground column `(25, 1)` and the clearance
`2504`, the magnetic square cap `W = 65` (`‖M‖² < 65²`, refused at
`64`), the solve floor `4` and the drift's clearing
`2504 − 25·65 = 879`. -/

open elim inertia

private def uT : BPair := ⟨1, 1⟩
private def oneT : List BPair := [⟨2, 1⟩, uT]
private def psi1T : List BPair := [uT, ⟨2, 1⟩]
private def psi2T : List BPair := [uT, ⟨17, 1⟩]
private def eT : Mat := [[uT, uT], [uT, ⟨5, 1⟩]]
private def mT : Mat := [[uT, ⟨5, 1⟩], [⟨5, 1⟩, ⟨65, 1⟩]]
private def etT : Mat := [[⟨5, 1⟩, ⟨1, 101⟩], [⟨1, 101⟩, ⟨2501, 1⟩]]
private def tT : SqMat 2 :=
  ⟨[[⟨26, 1⟩, ⟨2, 1⟩], [⟨2, 1⟩, ⟨1, 26⟩]], by decide +kernel⟩
private def twT : SqMat 2 :=
  ⟨[[⟨1, 26⟩, ⟨1, 2⟩], [⟨1, 2⟩, ⟨26, 1⟩]], by decide +kernel⟩
private def lT : List (BPair × Pos × BPair) :=
  [(uT, 1, ⟨627, 1⟩), (⟨2505, 1⟩, 1, ⟨627, 1⟩)]
private def e0T : BPair := ⟨1, 5⟩
private def jT : List BPair := jetVec 5 32 oneT psi1T psi2T
private def rT : List BPair := residVec 5 32 16 mT psi1T psi2T
private def mm : Mat := matScale Pos.one (matMul (transposeM mT) mT)
private def spET : Split 2 := mkSplit 2 eT
private def spUT : Split 2 := mkSplit 2 (siteDatum (matScale (65 * 65) (idMat 2)) mm)
private def spLT : Split 2 := mkSplit 2 (matAdd (matScale (65 * 65) (idMat 2)) mm)
private def psiT : List BPair := matVec tT.val (elim.idRow 2 0)

/-- The reads at the fixture. -/
private theorem hE0T : poly.unitTail (matVec eT oneT) := by decide +kernel
private theorem hE1T : poly.oneValue (matVec eT psi1T) (matVec mT oneT) := by decide +kernel
private theorem hE2T : poly.oneValue
    (vecAdd (vecScale (BPair.ofNat 4) (matVec eT psi2T)) (vecScale (BPair.ofNat 16) oneT))
    (vecScale (BPair.ofNat 4) (matVec mT psi1T)) := by decide +kernel
private theorem hcapT : capAt mm (matScale (65 * 65) (idMat 2)) spUT spLT := by decide +kernel
private theorem hdT : split.diagRead etT (idMat 2) tT twT lT := by decide +kernel
private theorem hclT : groundreads.clearRead lT 0 2504 1 := by decide +kernel
private theorem htieT : matOneValue etT
    (siteDatum (matScale Pos.one (rayH 5 32 eT mT)) (matScaleB e0T (idMat 2))) := by
  decide +kernel

/-- The jet's identity decided and through the theorem. -/
example : poly.oneValue (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eT mT) jT))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 16) jT).map BPair.swap) rT) := by
  decide +kernel
example : poly.oneValue (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eT mT) jT))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 16) jT).map BPair.swap) rT) :=
  jetResidual (n := 2) eT mT (by decide +kernel) (by decide +kernel) oneT psi1T psi2T
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 16 5 32 hE0T hE1T hE2T

/-- The refusals isolating the three reads: the unit off the electric
kernel, the module read at an asymmetric magnetic member, and the
second-order read at a plaquette count one beyond, each parting the
identity alone. -/
private def eK : Mat := [[⟨2, 1⟩, uT], [uT, ⟨5, 1⟩]]
example : ¬ poly.unitTail (matVec eK oneT) := by decide +kernel
example : poly.oneValue (matVec eK psi1T) (matVec mT oneT) := by decide +kernel
example : poly.oneValue
    (vecAdd (vecScale (BPair.ofNat 4) (matVec eK psi2T)) (vecScale (BPair.ofNat 16) oneT))
    (vecScale (BPair.ofNat 4) (matVec mT psi1T)) := by decide +kernel
example : ¬ poly.oneValue (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eK mT) jT))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 16) jT).map BPair.swap) rT) := by
  decide +kernel
private def mA : Mat := [[uT, ⟨5, 1⟩], [⟨6, 1⟩, ⟨65, 1⟩]]
example : ¬ poly.oneValue (matVec eT psi1T) (matVec mA oneT) := by decide +kernel
example : poly.oneValue
    (vecAdd (vecScale (BPair.ofNat 4) (matVec eT psi2T)) (vecScale (BPair.ofNat 16) oneT))
    (vecScale (BPair.ofNat 4) (matVec mA psi1T)) := by decide +kernel
example : ¬ poly.oneValue (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eT mA) jT))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 16) jT).map BPair.swap)
      (residVec 5 32 16 mA psi1T psi2T)) := by decide +kernel
example : ¬ poly.oneValue
    (vecAdd (vecScale (BPair.ofNat 4) (matVec eT psi2T)) (vecScale (BPair.ofNat 17) oneT))
    (vecScale (BPair.ofNat 4) (matVec mT psi1T)) := by decide +kernel
example : ¬ poly.oneValue (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eT mT) jT))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 17) jT).map BPair.swap)
      (residVec 5 32 17 mT psi1T psi2T)) := by decide +kernel

/-- The solve floor at `ℓ = 4`, decided and through the theorem; the
floor forged to `5` refuses beside its own read's refusal, the cap
forged to `64` parts the cap read and to `63` the display, and the
perpendicularity forged at a unit off the kernel at a tied magnetic
member parts the display alone. -/
example : (dotN psi2T psi2T).scale 4 ≤ (quadForm eT psi2T).scale 1 := by decide +kernel
example : (dotN psi2T psi2T).scale (4 * 4)
    ≤ (BPair.ofPos (65 * 65) * dotN psi1T psi1T).scale (1 * 1) := by decide +kernel
example : (dotN psi2T psi2T).scale (4 * 4)
    ≤ (BPair.ofPos (65 * 65) * dotN psi1T psi1T).scale (1 * 1) :=
  solveFloor eT mT (by decide +kernel) (by decide +kernel) oneT psi1T psi2T
    (by decide +kernel) (by decide +kernel) (by decide +kernel) 16 hE2T (by decide +kernel)
    4 1 (by decide +kernel) 65 spUT spLT hcapT
example : ¬ ((dotN psi2T psi2T).scale 5 ≤ (quadForm eT psi2T).scale 1) := by decide +kernel
example : ¬ ((dotN psi2T psi2T).scale (5 * 5)
    ≤ (BPair.ofPos (65 * 65) * dotN psi1T psi1T).scale (1 * 1)) := by decide +kernel
example : ¬ capAt mm (matScale (64 * 64) (idMat 2))
    (mkSplit 2 (siteDatum (matScale (64 * 64) (idMat 2)) mm))
    (mkSplit 2 (matAdd (matScale (64 * 64) (idMat 2)) mm)) := by decide +kernel
example : ¬ ((dotN psi2T psi2T).scale (4 * 4)
    ≤ (BPair.ofPos (63 * 63) * dotN psi1T psi1T).scale (1 * 1)) := by decide +kernel
private def oneP : List BPair := [⟨2, 1⟩, ⟨1, 2⟩]
private def mP : Mat := [[uT, ⟨5, 1⟩], [⟨5, 1⟩, ⟨61, 1⟩]]
private def mmP : Mat := matScale Pos.one (matMul (transposeM mP) mP)
example : poly.oneValue
    (vecAdd (vecScale (BPair.ofNat 4) (matVec eT psi2T)) (vecScale (BPair.ofNat 16) oneP))
    (vecScale (BPair.ofNat 4) (matVec mP psi1T)) := by decide +kernel
example : ¬ (dotN psi2T oneP).oneValue BPair.unit := by decide +kernel
example : capAt mmP (matScale (63 * 63) (idMat 2))
    (mkSplit 2 (siteDatum (matScale (63 * 63) (idMat 2)) mmP))
    (mkSplit 2 (matAdd (matScale (63 * 63) (idMat 2)) mmP)) := by decide +kernel

/-- The residual's weight decided and through the theorem; the cap
forged at a magnetic member grown past it parts the cap read and the
display. -/
example : dotN rT rT
    ≤ (BPair.ofNat (4 * (16 * 16)) * dotN psi1T psi1T).scale (Pos.pow 32 4 * Pos.pow 5 12)
      + (BPair.ofPos (64 * (65 * 65)) * dotN psi2T psi2T).scale (Pos.pow 32 4 * Pos.pow 5 12)
      + (BPair.ofNat (2 * (16 * 16)) * dotN psi2T psi2T).scale (Pos.pow 5 16) := by
  decide +kernel
example : dotN rT rT
    ≤ (BPair.ofNat (4 * (16 * 16)) * dotN psi1T psi1T).scale (Pos.pow 32 4 * Pos.pow 5 12)
      + (BPair.ofPos (64 * (65 * 65)) * dotN psi2T psi2T).scale (Pos.pow 32 4 * Pos.pow 5 12)
      + (BPair.ofNat (2 * (16 * 16)) * dotN psi2T psi2T).scale (Pos.pow 5 16) :=
  residWeight mT (by decide +kernel) psi1T psi2T (by decide +kernel) (by decide +kernel)
    16 5 32 65 spUT spLT hcapT
private def mG : Mat := [[uT, ⟨5, 1⟩], [⟨5, 1⟩, ⟨1001, 1⟩]]
private def mmG : Mat := matScale Pos.one (matMul (transposeM mG) mG)
example : ¬ capAt mmG (matScale (65 * 65) (idMat 2))
    (mkSplit 2 (siteDatum (matScale (65 * 65) (idMat 2)) mmG))
    (mkSplit 2 (matAdd (matScale (65 * 65) (idMat 2)) mmG)) := by decide +kernel
example : ¬ (dotN (residVec 5 32 16 mG psi1T psi2T) (residVec 5 32 16 mG psi1T psi2T)
    ≤ (BPair.ofNat (4 * (16 * 16)) * dotN psi1T psi1T).scale (Pos.pow 32 4 * Pos.pow 5 12)
      + (BPair.ofPos (64 * (65 * 65)) * dotN psi2T psi2T).scale (Pos.pow 32 4 * Pos.pow 5 12)
      + (BPair.ofNat (2 * (16 * 16)) * dotN psi2T psi2T).scale (Pos.pow 5 16)) := by
  decide +kernel

/-- The count's fold of squares at two copies of the magnetic member:
the displayed identity decided, the sum's square cap decided and
through the theorem at the per-term caps read off the committed
certificate, and the certificate's two directions through
`inertia.cap_vec` and `inertia.capAt_of_sq`. -/
example : (dotN (vecSumL 2 [psi1T, psi2T]) (vecSumL 2 [psi1T, psi2T])
      + gapFold [psi1T, psi2T]).oneValue
    (BPair.ofNat 2 * selfSumL [psi1T, psi2T]) := by decide +kernel
example : ¬ (BPair.ofNat (2 * 2) * (BPair.ofPos (65 * 65) * dotN psi1T psi1T)
    < dotN (matVec (matSumL 2 [mT, mT]) psi1T) (matVec (matSumL 2 [mT, mT]) psi1T)) := by
  decide +kernel
private theorem hMsT : ∀ i, i < ([mT, mT] : List Mat).length →
    ground.getAt [] [mT, mT] i = mT := by decide +kernel
example : ¬ (BPair.ofNat (2 * 2) * (BPair.ofPos (65 * 65) * dotN psi1T psi1T)
    < dotN (matVec (matSumL 2 [mT, mT]) psi1T) (matVec (matSumL 2 [mT, mT]) psi1T)) :=
  matSumL_sq_cap 2 [mT, mT]
    (fun i hi => by rw [hMsT i hi]; exact (by decide +kernel : sqAt mT 2)) 65
    (fun i hi x hx => by
      rw [hMsT i hi]
      exact ground.leB_not_lt
        (inertia.cap_vec mT (by decide +kernel) 65 spUT spLT hcapT x hx))
    psi1T (by decide +kernel)
example : dotN (matVec mT psi2T) (matVec mT psi2T)
    ≤ BPair.ofPos (65 * 65) * dotN psi2T psi2T := by decide +kernel
example : dotN (matVec mT psi2T) (matVec mT psi2T)
    ≤ BPair.ofPos (65 * 65) * dotN psi2T psi2T :=
  inertia.cap_vec mT (by decide +kernel) 65 spUT spLT hcapT psi2T (by decide +kernel)
example : capAt mm (matScale (65 * 65) (idMat 2)) spUT spLT :=
  inertia.capAt_of_sq mT (by decide +kernel) 65
    (fun v hv => inertia.cap_vec mT (by decide +kernel) 65 spUT spLT hcapT v hv)
    spUT spLT (by decide +kernel) (by decide +kernel)
example : dotN (vecAdd psi1T psi2T) (vecAdd psi1T psi2T)
    ≤ BPair.ofNat 2 * (dotN psi1T psi1T + dotN psi2T psi2T) := by decide +kernel

/-- The off-line bound at the drift, decided and through the theorem:
the ground column `(25, 1)`, the jet's part off its line priced by the
residual at the drift's clearing `879`; and at the excited column
`(1, −25)` as the vector, its residual read by construction, the
display holds with the clearance forged to `8000` parting it beside
the clearance read's own refusal. -/
private theorem hEsT : splitRead eT spET ∧ psdAt spET := by decide +kernel
private theorem hresT : poly.oneValue
    (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eT mT) jT))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 16) jT).map BPair.swap) rT) := by
  decide +kernel
example : ((BPair.ofPos 2504 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * (BPair.ofPos 2504 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * dotN (residD [psiT] jT) (residD [psiT] jT)).scale (16 * Pos.pow 32 4)
    ≤ (dotN psiT psiT * dotN psiT psiT * dotN rT rT).scale (1 * 1 * (1 * 1)) := by
  decide +kernel
example : ((BPair.ofPos 2504 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * (BPair.ofPos 2504 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * dotN (residD [matVec tT.val (elim.idRow 2 0)] jT)
          (residD [matVec tT.val (elim.idRow 2 0)] jT)).scale (16 * Pos.pow 32 4)
    ≤ (dotN (matVec tT.val (elim.idRow 2 0)) (matVec tT.val (elim.idRow 2 0))
        * dotN (matVec tT.val (elim.idRow 2 0)) (matVec tT.val (elim.idRow 2 0))
        * dotN rT rT).scale (1 * 1 * (1 * 1)) :=
  offLine_drift eT mT etT (by decide +kernel) (by decide +kernel) tT twT lT hdT 0
    (by decide +kernel) 1 ⟨627, 1⟩ (by decide +kernel) 2504 1 hclT 5 32 1 e0T htieT
    spET hEsT.1 hEsT.2 65 spUT spLT hcapT 16 jT rT (by decide +kernel) (by decide +kernel)
    hresT (by decide +kernel)
private def jX : List BPair := [⟨2, 1⟩, ⟨1, 26⟩]
private def rX : List BPair :=
  vecAdd (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eT mT) jX))
    (vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 16) jX)
example : poly.oneValue (vecScale (BPair.ofPos (4 * (32 * 32))) (matVec (rayH 5 32 eT mT) jX))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 5 4) * BPair.ofNat 16) jX).map BPair.swap) rX) := by
  decide +kernel
example : ((BPair.ofPos 2504 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * (BPair.ofPos 2504 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * dotN (residD [psiT] jX) (residD [psiT] jX)).scale (16 * Pos.pow 32 4)
    ≤ (dotN psiT psiT * dotN psiT psiT * dotN rX rX).scale (1 * 1 * (1 * 1)) := by
  decide +kernel
example : ¬ groundreads.clearRead lT 0 8000 1 := by decide +kernel
example : ¬ (((BPair.ofPos 8000 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * (BPair.ofPos 8000 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap)
      * dotN (residD [psiT] jX) (residD [psiT] jX)).scale (16 * Pos.pow 32 4)
    ≤ (dotN psiT psiT * dotN psiT psiT * dotN rX rX).scale (1 * 1 * (1 * 1))) := by
  decide +kernel

/-- The truncation bracket at the jet, decided and through the theorem:
the observable `diag(1, 3)` at the cap `[3 : 1]`, the second-order weight
`256` under the cap `[4225 : 16]`, the display cleared at `q⁴ cd zd` with
`p = 5`, `q = 32`.  The refusals part the binders at the conclusion: the
cap read at the observable grown to `diag(1, 300)` against the cap `3`,
the weight cap forged to `1`, the unit read at `ψ₀` of self-pairing four,
the perpendicular read at `ψ₁` tilted onto the unit, and the second-order
perpendicular read at `ψ₂` on the unit's line, the weight cap at its own
value exposing the key-two residue. -/
private def aT : Mat := [[⟨2, 1⟩, uT], [uT, ⟨4, 1⟩]]
private def spAT : Split 2 := mkSplit 2 (siteDatum (matScale 3 (idMat 2)) (matScale 1 aT))
private def spAT' : Split 2 := mkSplit 2 (matAdd (matScale 3 (idMat 2)) (matScale 1 aT))
private theorem hAT : capAt (matScale 1 aT) (matScale 3 (idMat 2)) spAT spAT' := by
  decide +kernel
example : windowsep.mag
      ((dotN jT (matVec aT jT)).scale (Pos.pow 32 4 * (1 * 16))
        + ((jetDisplay aT oneT psi1T psi2T 5 32 * dotN jT jT).scale (1 * 16)).swap)
    ≤ truncCap 3 1 16 (dotN oneT (matVec aT oneT))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi1T))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi2T) + dotN psi1T (matVec aT psi1T)
          + (dotN oneT (matVec aT oneT) * dotN psi1T psi1T).swap)
        (dotN psi1T psi1T) (BPair.ofNat 4225) 5 32 := by decide +kernel
example : windowsep.mag
      ((dotN jT (matVec aT jT)).scale (Pos.pow 32 4 * (1 * 16))
        + ((jetDisplay aT oneT psi1T psi2T 5 32 * dotN jT jT).scale (1 * 16)).swap)
    ≤ truncCap 3 1 16 (dotN oneT (matVec aT oneT))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi1T))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi2T) + dotN psi1T (matVec aT psi1T)
          + (dotN oneT (matVec aT oneT) * dotN psi1T psi1T).swap)
        (dotN psi1T psi1T) (BPair.ofNat 4225) 5 32 :=
  truncBracket (n := 2) aT 3 1 spAT spAT' hAT oneT psi1T psi2T (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (BPair.ofNat 4225) 16 (by decide +kernel) 5 32
private def aB : Mat := [[⟨2, 1⟩, uT], [uT, ⟨301, 1⟩]]
example : ¬ capAt (matScale 1 aB) (matScale 3 (idMat 2))
    (mkSplit 2 (siteDatum (matScale 3 (idMat 2)) (matScale 1 aB)))
    (mkSplit 2 (matAdd (matScale 3 (idMat 2)) (matScale 1 aB))) := by decide +kernel
example : ¬ windowsep.mag
      ((dotN jT (matVec aB jT)).scale (Pos.pow 32 4 * (1 * 16))
        + ((jetDisplay aB oneT psi1T psi2T 5 32 * dotN jT jT).scale (1 * 16)).swap)
    ≤ truncCap 3 1 16 (dotN oneT (matVec aB oneT))
        (BPair.ofNat 2 * dotN oneT (matVec aB psi1T))
        (BPair.ofNat 2 * dotN oneT (matVec aB psi2T) + dotN psi1T (matVec aB psi1T)
          + (dotN oneT (matVec aB oneT) * dotN psi1T psi1T).swap)
        (dotN psi1T psi1T) (BPair.ofNat 4225) 5 32 := by decide +kernel
example : ¬ ((dotN psi2T psi2T).scale 16 ≤ BPair.ofNat 1) := by decide +kernel
example : ¬ windowsep.mag
      ((dotN jT (matVec aT jT)).scale (Pos.pow 32 4 * (1 * 16))
        + ((jetDisplay aT oneT psi1T psi2T 5 32 * dotN jT jT).scale (1 * 16)).swap)
    ≤ truncCap 3 1 16 (dotN oneT (matVec aT oneT))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi1T))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi2T) + dotN psi1T (matVec aT psi1T)
          + (dotN oneT (matVec aT oneT) * dotN psi1T psi1T).swap)
        (dotN psi1T psi1T) (BPair.ofNat 1) 5 32 := by decide +kernel
private def fourT : List BPair := [⟨3, 1⟩, uT]
private def jF : List BPair := jetVec 5 32 fourT psi1T psi2T
example : ¬ (dotN fourT fourT).oneValue (BPair.ofNat 1) := by decide +kernel
example : ¬ windowsep.mag
      ((dotN jF (matVec aT jF)).scale (Pos.pow 32 4 * (1 * 16))
        + ((jetDisplay aT fourT psi1T psi2T 5 32 * dotN jF jF).scale (1 * 16)).swap)
    ≤ truncCap 3 1 16 (dotN fourT (matVec aT fourT))
        (BPair.ofNat 2 * dotN fourT (matVec aT psi1T))
        (BPair.ofNat 2 * dotN fourT (matVec aT psi2T) + dotN psi1T (matVec aT psi1T)
          + (dotN fourT (matVec aT fourT) * dotN psi1T psi1T).swap)
        (dotN psi1T psi1T) (BPair.ofNat 4225) 5 32 := by decide +kernel
private def tiltT : List BPair := [⟨2, 1⟩, ⟨2, 1⟩]
private def jP : List BPair := jetVec 5 32 oneT tiltT psi2T
example : ¬ (dotN oneT tiltT).oneValue BPair.unit := by decide +kernel
example : ¬ windowsep.mag
      ((dotN jP (matVec aT jP)).scale (Pos.pow 32 4 * (1 * 16))
        + ((jetDisplay aT oneT tiltT psi2T 5 32 * dotN jP jP).scale (1 * 16)).swap)
    ≤ truncCap 3 1 16 (dotN oneT (matVec aT oneT))
        (BPair.ofNat 2 * dotN oneT (matVec aT tiltT))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi2T) + dotN tiltT (matVec aT tiltT)
          + (dotN oneT (matVec aT oneT) * dotN tiltT tiltT).swap)
        (dotN tiltT tiltT) (BPair.ofNat 4225) 5 32 := by decide +kernel

/-- The moments' bracket at the jet, decided and through the theorem: the
observable `diag(1, 3)` at the cap `[3 : 1]`, the drift's clearing `879`
at `2504 − 25 · 65`, the root caps `2081` and `91`.  The refusals part the
binders at the conclusion: the first root cap forged to `1`, the drift's
datum forged to `10¹⁵` against the read `879`, and the clearance forged
to `10¹²` with its datum tied, the clearance read refusing at the
list's second root `2505`. -/
example : (windowsep.mag (groundreads.readGap (groundreads.read aT psiT)
      (groundreads.read aT jT))).scale (2504 * (879 * Pos.pow 32 6) * 1)
    ≤ (dotN psiT psiT * dotN jT jT).scale
        (4 * (3 * (2504 * 1 * Pos.pow 5 6 * (2081 * (32 * 32) + 91 * (5 * 5))) * 1)) := by
  decide +kernel
example : (windowsep.mag (groundreads.readGap
      (groundreads.read aT (matVec tT.val (elim.idRow 2 0)))
      (groundreads.read aT (jetVec 5 32 oneT psi1T psi2T)))).scale
      (2504 * (879 * Pos.pow 32 6) * 1)
    ≤ (dotN (matVec tT.val (elim.idRow 2 0)) (matVec tT.val (elim.idRow 2 0))
        * dotN (jetVec 5 32 oneT psi1T psi2T) (jetVec 5 32 oneT psi1T psi2T)).scale
        (4 * (3 * (2504 * 1 * Pos.pow 5 6 * (2081 * (32 * 32) + 91 * (5 * 5))) * 1)) :=
  momentBracket (n := 2) eT mT etT (by decide +kernel) (by decide +kernel) tT twT lT hdT 0
    (by decide +kernel) 1 ⟨627, 1⟩ (by decide +kernel) 2504 1 hclT 5 32 1 e0T htieT
    spET hEsT.1 hEsT.2 65 spUT spLT hcapT oneT psi1T psi2T (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 16 hE0T hE1T hE2T (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 879 (by decide +kernel) 2081 91
    (by decide +kernel) (by decide +kernel) aT 3 1 spAT spAT' hAT
example : ¬ (BPair.ofNat (4 * (16 * 16)) * dotN psi1T psi1T
    + BPair.ofPos (64 * (65 * 65)) * dotN psi2T psi2T ≤ BPair.ofPos (16 * (1 * 1))) := by
  decide +kernel
example : ¬ (windowsep.mag (groundreads.readGap (groundreads.read aT psiT)
      (groundreads.read aT jT))).scale (2504 * (879 * Pos.pow 32 6) * 1)
    ≤ (dotN psiT psiT * dotN jT jT).scale
        (4 * (3 * (2504 * 1 * Pos.pow 5 6 * (1 * (32 * 32) + 91 * (5 * 5))) * 1)) := by
  decide +kernel
example : ¬ (BPair.ofPos 2504 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap).oneValue
    (BPair.ofPos 1000000000000000) := by decide +kernel
example : ¬ (windowsep.mag (groundreads.readGap (groundreads.read aT psiT)
      (groundreads.read aT jT))).scale (2504 * (1000000000000000 * Pos.pow 32 6) * 1)
    ≤ (dotN psiT psiT * dotN jT jT).scale
        (4 * (3 * (2504 * 1 * Pos.pow 5 6 * (2081 * (32 * 32) + 91 * (5 * 5))) * 1)) := by
  decide +kernel
example : ¬ groundreads.clearRead lT 0 1000000000000 1 := by decide +kernel
example : (BPair.ofPos 1000000000000 + (BPair.ofPos (1 * 1 * (5 * 5) * 65)).swap).oneValue
    (BPair.ofPos 999999998375) := by decide +kernel
example : ¬ (windowsep.mag (groundreads.readGap (groundreads.read aT psiT)
      (groundreads.read aT jT))).scale (1000000000000 * (999999998375 * Pos.pow 32 6) * 1)
    ≤ (dotN psiT psiT * dotN jT jT).scale
        (4 * (3 * (1000000000000 * 1 * Pos.pow 5 6 * (2081 * (32 * 32) + 91 * (5 * 5))) * 1)) := by
  decide +kernel

/-- The partition fold's bracket, decided and through the theorem: the
constant families at one against one half, the caps at the unit base,
the datum `[1 : 2]` — `κ₄` of the first family reads equal members, of
the second the balance partner of `[1 : 8]`, the gap `[1 : 8]` under
`75 · [1 : 2]`.  The refusals part the binders at the conclusion: the
cap read at the constant family three against the unit base, and the
gap datum forged to `[1 : 1000]` against the families' gap `[1 : 2]`. -/
private def muF : Nat → Nat → BPair × Pos := fun _ _ => (BPair.ofNat 1, Pos.one)
private def nuF : Nat → Nat → BPair × Pos := fun _ _ => (BPair.ofNat 1, 2)
private def DF : BPair × Pos := (BPair.ofNat 1, 2)
private theorem hcapF : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      windowsep.mag (muF a b).1 ≤ (BPair.ofPos (Pos.pow 1 (a + b))).scale (muF a b).2
      ∧ windowsep.mag (nuF a b).1 ≤ (BPair.ofPos (Pos.pow 1 (a + b))).scale (nuF a b).2 := by
  decide +kernel
private theorem hgapF : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      ∀ e : Nat, e ≤ 4 → a + b + e = 4 →
      (windowsep.mag (BPair.addQ (muF a b) (bpairQOps.swap (nuF a b))).1).scale
          (DF.2 * Pos.pow 1 e)
        ≤ DF.1.scale (BPair.addQ (muF a b) (bpairQOps.swap (nuF a b))).2 := by
  decide +kernel
example : (windowsep.mag (BPair.addQ (kappa4 bpairQOps muF)
        (bpairQOps.swap (kappa4 bpairQOps nuF))).1).scale (poly.nsmulO bpairQOps DF 75).2
      ≤ (poly.nsmulO bpairQOps DF 75).1.scale
          (BPair.addQ (kappa4 bpairQOps muF) (bpairQOps.swap (kappa4 bpairQOps nuF))).2 := by
  decide +kernel
example : (windowsep.mag (BPair.addQ (kappa4 bpairQOps muF)
        (bpairQOps.swap (kappa4 bpairQOps nuF))).1).scale (poly.nsmulO bpairQOps DF 75).2
      ≤ (poly.nsmulO bpairQOps DF 75).1.scale
          (BPair.addQ (kappa4 bpairQOps muF) (bpairQOps.swap (kappa4 bpairQOps nuF))).2 :=
  foldBracket muF nuF 1 DF hcapF hgapF
private def muB : Nat → Nat → BPair × Pos := fun _ _ => (BPair.ofNat 3, Pos.one)
example : ¬ (∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      windowsep.mag (muB a b).1 ≤ (BPair.ofPos (Pos.pow 1 (a + b))).scale (muB a b).2
      ∧ windowsep.mag (nuF a b).1 ≤ (BPair.ofPos (Pos.pow 1 (a + b))).scale (nuF a b).2) := by
  decide +kernel
example : ¬ (windowsep.mag (BPair.addQ (kappa4 bpairQOps muB)
        (bpairQOps.swap (kappa4 bpairQOps nuF))).1).scale (poly.nsmulO bpairQOps DF 75).2
      ≤ (poly.nsmulO bpairQOps DF 75).1.scale
          (BPair.addQ (kappa4 bpairQOps muB) (bpairQOps.swap (kappa4 bpairQOps nuF))).2 := by
  decide +kernel
private def DG : BPair × Pos := (BPair.ofNat 1, 1000)
example : ¬ (∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      ∀ e : Nat, e ≤ 4 → a + b + e = 4 →
      (windowsep.mag (BPair.addQ (muF a b) (bpairQOps.swap (nuF a b))).1).scale
          (DG.2 * Pos.pow 1 e)
        ≤ DG.1.scale (BPair.addQ (muF a b) (bpairQOps.swap (nuF a b))).2) := by
  decide +kernel
example : ¬ (windowsep.mag (BPair.addQ (kappa4 bpairQOps muF)
        (bpairQOps.swap (kappa4 bpairQOps nuF))).1).scale (poly.nsmulO bpairQOps DG 75).2
      ≤ (poly.nsmulO bpairQOps DG 75).1.scale
          (BPair.addQ (kappa4 bpairQOps muF) (bpairQOps.swap (kappa4 bpairQOps nuF))).2 := by
  decide +kernel

/-- The np-dominant window (`lem:fourpoint`'s tail): `E = diag(0, 1)`,
`M` at the coupling `4` and the datum `7`, `W = 9`, the states `(1, 0)`,
`(0, 4)` and `(0, 28)` at `np = 64`, the ray `p = q = 1` with the
drift's clearance one, and the root caps at parity — `K₀ = 520` at its
cap's own equality against the committed window's four-percent share,
`K₁ = 634` with `2 np² ⟨ψ₂, ψ₂⟩ = 6422528` under `16 K₁² = 6431296`.
The moments' bracket lands through the theorem with both root caps'
boundaries parted, `K₀` at `519` and `K₁` at `633`.  The factor's move
bracket lands decided and through the theorem with the weight cap's
boundary parted at `783`; either summand alone prices the read — the
moment term and the truncation term each cover the gap's magnitude
here as at the committed window, the two decided cover pins — so no
single forge parts the two-term conclusion and the binders' isolation
lives at the constituent brackets' own refusals.  The fold's bracket
at the window carrier lands decided and through the theorem at the
constant observable family with the display tight at the cap base
`33` and parted at `32`, the datum tied at `512164636632`'s own
equality and parted one below, and the conclusion parted at the datum
`89223` against `89224` — the fold's denominator the states' read's
seventy-fifth power, one clearing per moment factor.  The tie binder
is frame: the states' read enters both members of every composite
pair and the cross-multiplied comparison is blind to the shared
clearing, so no forge of the tie parts the conclusion. -/
private def psi1W : List BPair := [uT, ⟨5, 1⟩]
private def psi2W : List BPair := [uT, ⟨29, 1⟩]
private def eW : Mat := [[uT, uT], [uT, ⟨2, 1⟩]]
private def mW : Mat := [[uT, ⟨5, 1⟩], [⟨5, 1⟩, ⟨8, 1⟩]]
private def etW : Mat := [[⟨9, 1⟩, ⟨1, 5⟩], [⟨1, 5⟩, ⟨3, 1⟩]]
private def tW : SqMat 2 := ⟨[[⟨2, 1⟩, ⟨3, 1⟩], [⟨3, 1⟩, ⟨1, 2⟩]], by decide +kernel⟩
private def twW : SqMat 2 := ⟨[[⟨1, 2⟩, ⟨1, 3⟩], [⟨1, 3⟩, ⟨2, 1⟩]], by decide +kernel⟩
private def lW : List (BPair × Pos × BPair) :=
  [(uT, 1, ⟨6, 1⟩), (⟨11, 1⟩, 1, ⟨6, 1⟩)]
private def e0W : BPair := ⟨1, 9⟩
private def mmW : Mat := matScale Pos.one (matMul (transposeM mW) mW)
private def spEW : Split 2 := mkSplit 2 eW
private def spUW : Split 2 := mkSplit 2 (siteDatum (matScale (9 * 9) (idMat 2)) mmW)
private def spLW : Split 2 := mkSplit 2 (matAdd (matScale (9 * 9) (idMat 2)) mmW)
private def psiW : List BPair := matVec tW.val (elim.idRow 2 0)
private def jW : List BPair := jetVec 1 1 oneT psi1W psi2W
private theorem hdW : split.diagRead etW (idMat 2) tW twW lW := by decide +kernel
private theorem hclW : groundreads.clearRead lW 0 10 1 := by decide +kernel
private theorem htieW : matOneValue etW
    (siteDatum (matScale 1 (rayH 1 1 eW mW)) (matScaleB e0W (idMat 2))) := by decide +kernel
private theorem hEsW : splitRead eW spEW ∧ psdAt spEW := by decide +kernel
private theorem hcapMW : capAt mmW (matScale (9 * 9) (idMat 2)) spUW spLW := by
  decide +kernel
private theorem hE0W : poly.unitTail (matVec eW oneT) := by decide +kernel
private theorem hE1W : poly.oneValue (matVec eW psi1W) (matVec mW oneT) := by decide +kernel
private theorem hE2W : poly.oneValue
    (vecAdd (vecScale (BPair.ofNat 4) (matVec eW psi2W)) (vecScale (BPair.ofNat 64) oneT))
    (vecScale (BPair.ofNat 4) (matVec mW psi1W)) := by decide +kernel

-- the moments' bracket through the theorem, the root caps' boundaries parted
example : (windowsep.mag (groundreads.readGap (groundreads.read aT psiW)
      (groundreads.read aT jW))).scale (10 * (1 * Pos.pow 1 6) * 1)
    ≤ (dotN psiW psiW * dotN jW jW).scale
        (4 * (3 * (10 * 1 * Pos.pow 1 6 * (520 * (1 * 1) + 634 * (1 * 1))) * 1)) :=
  momentBracket (n := 2) eW mW etW (by decide +kernel) (by decide +kernel) tW twW lW hdW 0
    (by decide +kernel) 1 ⟨6, 1⟩ (by decide +kernel) 10 1 hclW 1 1 1 e0W htieW
    spEW hEsW.1 hEsW.2 9 spUW spLW hcapMW oneT psi1W psi2W (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 64 hE0W hE1W hE2W (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) 520 634
    (by decide +kernel) (by decide +kernel) aT 3 1 spAT spAT' hAT
example : ¬ (BPair.ofNat (4 * (64 * 64)) * dotN psi1W psi1W
    + BPair.ofPos (64 * (9 * 9)) * dotN psi2W psi2W ≤ BPair.ofPos (16 * (519 * 519))) := by
  decide +kernel
example : ¬ (BPair.ofNat (2 * (64 * 64)) * dotN psi2W psi2W
    ≤ BPair.ofPos (16 * (633 * 633))) := by decide +kernel

-- the factor's move bracket, decided and through the theorem, the weight
-- cap's boundary and the two cover pins
example : (windowsep.mag (groundreads.readGap
      (groundreads.read aT psiW)
      (jetDisplay aT oneT psi1W psi2W 1 1, BPair.ofPos (Pos.pow 1 4)))).scale
      (10 * (1 * Pos.pow 1 6) * 1 * (1 * 1 * Pos.pow 1 8))
    ≤ (dotN psiW psiW * dotN jW jW).scale
        (4 * (3 * (10 * 1 * Pos.pow 1 6 * (520 * (1 * 1) + 634 * (1 * 1))) * 1)
          * (Pos.pow 1 4 * (1 * 1)))
      + (truncCap 3 1 1 (dotN oneT (matVec aT oneT))
            (BPair.ofNat 2 * dotN oneT (matVec aT psi1W))
            (BPair.ofNat 2 * dotN oneT (matVec aT psi2W) + dotN psi1W (matVec aT psi1W)
              + (dotN oneT (matVec aT oneT) * dotN psi1W psi1W).swap)
            (dotN psi1W psi1W) (BPair.ofNat 784) 1 1
          * dotN psiW psiW).scale (10 * (1 * Pos.pow 1 6) * 1) := by decide +kernel
example : (windowsep.mag (groundreads.readGap
      (groundreads.read aT (matVec tW.val (elim.idRow 2 0)))
      (jetDisplay aT oneT psi1W psi2W 1 1, BPair.ofPos (Pos.pow 1 4)))).scale
      (10 * (1 * Pos.pow 1 6) * 1 * (1 * 1 * Pos.pow 1 8))
    ≤ (dotN (matVec tW.val (elim.idRow 2 0)) (matVec tW.val (elim.idRow 2 0))
          * dotN (jetVec 1 1 oneT psi1W psi2W) (jetVec 1 1 oneT psi1W psi2W)).scale
        (4 * (3 * (10 * 1 * Pos.pow 1 6 * (520 * (1 * 1) + 634 * (1 * 1))) * 1)
          * (Pos.pow 1 4 * (1 * 1)))
      + (truncCap 3 1 1 (dotN oneT (matVec aT oneT))
            (BPair.ofNat 2 * dotN oneT (matVec aT psi1W))
            (BPair.ofNat 2 * dotN oneT (matVec aT psi2W) + dotN psi1W (matVec aT psi1W)
              + (dotN oneT (matVec aT oneT) * dotN psi1W psi1W).swap)
            (dotN psi1W psi1W) (BPair.ofNat 784) 1 1
          * dotN (matVec tW.val (elim.idRow 2 0))
              (matVec tW.val (elim.idRow 2 0))).scale (10 * (1 * Pos.pow 1 6) * 1) :=
  gapBracket (n := 2) eW mW etW (by decide +kernel) (by decide +kernel) tW twW lW hdW 0
    (by decide +kernel) 1 ⟨6, 1⟩ (by decide +kernel) 10 1 hclW 1 1 1 e0W htieW
    spEW hEsW.1 hEsW.2 9 spUW spLW hcapMW oneT psi1W psi2W (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 64 hE0W hE1W hE2W (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) 520 634
    (by decide +kernel) (by decide +kernel) aT 3 1 spAT spAT' hAT
    (BPair.ofNat 784) 1 (by decide +kernel)
example : ¬ ((dotN psi2W psi2W).scale 1 ≤ BPair.ofNat 783) := by decide +kernel
example : (windowsep.mag (groundreads.readGap
      (groundreads.read aT psiW)
      (jetDisplay aT oneT psi1W psi2W 1 1, BPair.ofPos (Pos.pow 1 4)))).scale
      (10 * (1 * Pos.pow 1 6) * 1 * (1 * 1 * Pos.pow 1 8))
    ≤ (dotN psiW psiW * dotN jW jW).scale
        (4 * (3 * (10 * 1 * Pos.pow 1 6 * (520 * (1 * 1) + 634 * (1 * 1))) * 1)
          * (Pos.pow 1 4 * (1 * 1))) := by decide +kernel
example : (windowsep.mag (groundreads.readGap
      (groundreads.read aT psiW)
      (jetDisplay aT oneT psi1W psi2W 1 1, BPair.ofPos (Pos.pow 1 4)))).scale
      (10 * (1 * Pos.pow 1 6) * 1 * (1 * 1 * Pos.pow 1 8))
    ≤ (truncCap 3 1 1 (dotN oneT (matVec aT oneT))
          (BPair.ofNat 2 * dotN oneT (matVec aT psi1W))
          (BPair.ofNat 2 * dotN oneT (matVec aT psi2W) + dotN psi1W (matVec aT psi1W)
            + (dotN oneT (matVec aT oneT) * dotN psi1W psi1W).swap)
          (dotN psi1W psi1W) (BPair.ofNat 784) 1 1
        * dotN psiW psiW).scale (10 * (1 * Pos.pow 1 6) * 1) := by decide +kernel

-- the fold's bracket at the window carrier, decided and through the
-- theorem, the datum's equality and both partings
private def dW : BPair × Pos := (BPair.ofPos 512164636632, 1)
example : (windowsep.mag (BPair.addQ
      (kappa4 bpairQOps (fun _ _ => (quadForm aT psiW, (5 : Pos))))
      (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
        (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).1).scale
      (poly.nsmulO bpairQOps dW 75).2
    ≤ (poly.nsmulO bpairQOps dW 75).1.scale
        (BPair.addQ
          (kappa4 bpairQOps (fun _ _ => (quadForm aT psiW, (5 : Pos))))
          (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
            (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).2 := by decide +kernel
example : (windowsep.mag (BPair.addQ
      (kappa4 bpairQOps (fun _ _ =>
        (quadForm aT (matVec tW.val (elim.idRow 2 0)), (5 : Pos))))
      (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
        (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).1).scale
      (poly.nsmulO bpairQOps dW 75).2
    ≤ (poly.nsmulO bpairQOps dW 75).1.scale
        (BPair.addQ
          (kappa4 bpairQOps (fun _ _ =>
            (quadForm aT (matVec tW.val (elim.idRow 2 0)), (5 : Pos))))
          (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
            (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).2 :=
  kappaBracket (n := 2) eW mW etW (by decide +kernel) (by decide +kernel) tW twW lW hdW 0
    (by decide +kernel) 1 ⟨6, 1⟩ (by decide +kernel) 10 1 hclW 1 1 1 e0W htieW
    spEW hEsW.1 hEsW.2 9 spUW spLW hcapMW oneT psi1W psi2W (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 64 hE0W hE1W hE2W (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) 520 634
    (by decide +kernel) (by decide +kernel) 5 (by decide +kernel) 33
    (fun _ _ => aT) (fun _ _ => 3) (fun _ _ => 1) (fun _ _ => spAT) (fun _ _ => spAT')
    (fun _ _ _ _ _ => hAT) (fun _ _ => BPair.ofNat 784) (fun _ _ => 1)
    (fun _ _ _ _ _ => by decide +kernel) dW (by decide +kernel) (by decide +kernel)
example : ¬ (∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
    windowsep.mag (quadForm aT psiW)
        ≤ (BPair.ofPos (Pos.pow 32 (a + b))).scale 5
      ∧ windowsep.mag (jetDisplay aT oneT psi1W psi2W 1 1)
        ≤ (BPair.ofPos (Pos.pow 32 (a + b))).scale (Pos.pow 1 4)) := by decide +kernel
example : ¬ ((dotN psiW psiW).oneValue (BPair.ofPos 4)) := by decide +kernel
private def dV : BPair × Pos := (BPair.ofPos 512164636631, 1)
example : ¬ (∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
    ∀ e : Nat, e ≤ 4 → a + b + e = 4 →
    ((dotN psiW psiW * dotN jW jW).scale
          (4 * (3 * (10 * 1 * Pos.pow 1 6 * (520 * (1 * 1) + 634 * (1 * 1))) * 1)
            * (Pos.pow 1 4 * (1 * 1)))
        + (truncCap 3 1 1 (dotN oneT (matVec aT oneT))
              (BPair.ofNat 2 * dotN oneT (matVec aT psi1W))
              (BPair.ofNat 2 * dotN oneT (matVec aT psi2W) + dotN psi1W (matVec aT psi1W)
                + (dotN oneT (matVec aT oneT) * dotN psi1W psi1W).swap)
              (dotN psi1W psi1W) (BPair.ofNat 784) 1 1
            * dotN psiW psiW).scale (10 * (1 * Pos.pow 1 6) * 1)).scale
        (dV.2 * Pos.pow 33 e)
      ≤ (dV.1.scale (5 * Pos.pow 1 4)).scale
          (10 * (1 * Pos.pow 1 6) * 1 * (1 * 1 * Pos.pow 1 8))) := by decide +kernel
private def dR : BPair × Pos := (BPair.ofPos 89223, 1)
example : ¬ (windowsep.mag (BPair.addQ
      (kappa4 bpairQOps (fun _ _ => (quadForm aT psiW, (5 : Pos))))
      (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
        (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).1).scale
      (poly.nsmulO bpairQOps dR 75).2
    ≤ (poly.nsmulO bpairQOps dR 75).1.scale
        (BPair.addQ
          (kappa4 bpairQOps (fun _ _ => (quadForm aT psiW, (5 : Pos))))
          (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
            (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).2 := by decide +kernel
private def dS : BPair × Pos := (BPair.ofPos 89224, 1)
example : (windowsep.mag (BPair.addQ
      (kappa4 bpairQOps (fun _ _ => (quadForm aT psiW, (5 : Pos))))
      (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
        (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).1).scale
      (poly.nsmulO bpairQOps dS 75).2
    ≤ (poly.nsmulO bpairQOps dS 75).1.scale
        (BPair.addQ
          (kappa4 bpairQOps (fun _ _ => (quadForm aT psiW, (5 : Pos))))
          (bpairQOps.swap (kappa4 bpairQOps (fun _ _ =>
            (jetDisplay aT oneT psi1W psi2W 1 1, Pos.pow 1 4))))).2 := by decide +kernel

/-- The comparison polynomial and the cell's floor, decided and through
the theorems: the fixture `γ' = 4`, `W = 1`, `c = 2`, the caps' folds the
unit lists, the crossing at `[4 : 1]`, the priced side certificate on the
segment to `[1 : 512]`, the ray `[1 : 32]` at the tied read
`K4 = τ⁴c`.  The refusals part the binders at the conclusion: the
certificate at the observable's balance partner (the leading read on its
lower side at the free end), the bracket at the read's balance partner,
and the segment at the ray one, the further binders held. -/
private def stF : poly.Poly := [BPair.ofNat 1]
private def cF : BPair := BPair.ofNat 2
private def compF : poly.Poly := compPoly 4 1 1 1 1 1 cF stF stF
example : stage.evalC compF ⟨BPair.ofPos 4, 1 * 1⟩ < stage.unitC := by decide +kernel
example : stage.evalC compF ⟨BPair.ofPos 4, 1 * 1⟩ < stage.unitC :=
  compCross 4 1 1 1 1 1 cF stF stF
example : stage.evalC (compPoly 9 2 3 2 5 1 (BPair.ofNat 11).swap
      [(BPair.ofNat 5).swap, (BPair.ofNat 7).swap] [BPair.ofNat 3])
    ⟨BPair.ofPos 9, 2 * 3⟩ < stage.unitC :=
  compCross 9 2 3 2 5 1 (BPair.ofNat 11).swap
    [(BPair.ofNat 5).swap, (BPair.ofNat 7).swap] [BPair.ofNat 3]
private theorem hkeepF : stage.keepUpper compF stage.unitC ⟨BPair.ofPos 1, 512⟩
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
example : ¬ stage.keepUpper compF stage.unitC ⟨BPair.ofPos 1, 256⟩
    (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
example : cF.scale (1048576 * Pos.pow 1 4)
    ≤ (BPair.ofNat 2 * BPair.ofNat 2).scale (Pos.pow 32 4) := by decide +kernel
example : cF.scale (1048576 * Pos.pow 1 4)
    ≤ (BPair.ofNat 2 * BPair.ofNat 2).scale (Pos.pow 32 4) :=
  cellFloor 4 1 1 1 1 1 cF stF stF ⟨BPair.ofPos 1, 512⟩ (BPair.ofNat 1) (BPair.ofNat 1)
    hkeepF 1 32 (by decide +kernel) (BPair.ofNat 2) 1048576 1 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- the certificate's refusal at the observable's balance partner, the
-- conclusion refused at the tied read
example : ¬ stage.keepUpper (compPoly 4 1 1 1 1 1 (cF.swap) stF stF) stage.unitC
    ⟨BPair.ofPos 1, 512⟩ (BPair.ofNat 1) (BPair.ofNat 1) := by decide +kernel
example : ((((BPair.ofPos 4).scale (32 * 32)
      + ((BPair.ofPos (1 * 1)).scale (1 * 1)).swap)
    * windowsep.mag ((cF.swap).scale (Pos.pow 32 4)
        + ((cF.swap).scale (1048576 * Pos.pow 1 4)).swap)).scale (Pos.pow 32 (2 * 1))
  ≤ (poly.evalClear (tailPoly 4 1 1 1 1 1 stF stF)
        (BPair.ofPos (1 * 1)) (32 * 32) 1).scale (1048576 * Pos.pow 1 6)) := by
  decide +kernel
example : ¬ ((cF.swap).scale (1048576 * Pos.pow 1 4)
    ≤ (BPair.ofNat 2 * cF.swap).scale (Pos.pow 32 4)) := by decide +kernel
-- the bracket's refusal at the read's balance partner
example : ¬ ((((BPair.ofPos 4).scale (32 * 32)
      + ((BPair.ofPos (1 * 1)).scale (1 * 1)).swap)
    * windowsep.mag (((BPair.ofNat 2).swap).scale (Pos.pow 32 4)
        + (cF.scale (1048576 * Pos.pow 1 4)).swap)).scale (Pos.pow 32 (2 * 1))
  ≤ (poly.evalClear (tailPoly 4 1 1 1 1 1 stF stF)
        (BPair.ofPos (1 * 1)) (32 * 32) 1).scale (1048576 * Pos.pow 1 6)) := by
  decide +kernel
example : ¬ (cF.scale (1048576 * Pos.pow 1 4)
    ≤ (BPair.ofNat 2 * (BPair.ofNat 2).swap).scale (Pos.pow 32 4)) := by decide +kernel
-- the segment's refusal at the ray one, the further binders held at the
-- unit read
example : ¬ ((⟨BPair.ofPos (1 * 1), 1 * 1⟩ : CPair) ≤ ⟨BPair.ofPos 1, 512⟩) := by
  decide +kernel
example : ((((BPair.ofPos 4).scale (1 * 1)
      + ((BPair.ofPos (1 * 1)).scale (1 * 1)).swap)
    * windowsep.mag (BPair.unit.scale (Pos.pow 1 4)
        + (cF.scale (1048576 * Pos.pow 1 4)).swap)).scale (Pos.pow 1 (2 * 1))
  ≤ (poly.evalClear (tailPoly 4 1 1 1 1 1 stF stF)
        (BPair.ofPos (1 * 1)) (1 * 1) 1).scale (1048576 * Pos.pow 1 6)) := by
  decide +kernel
example : ¬ (cF.scale (1048576 * Pos.pow 1 4)
    ≤ (BPair.ofNat 2 * BPair.unit).scale (Pos.pow 1 4)) := by decide +kernel

/-- The second-order perpendicular read's refusal at `ψ₂` on the unit's
line: the datum `N_A` gains the key-two residue `2μ̂₀⟨ψ₀,ψ₂⟩`, off the
caps' keys, and the tight weight cap `[1 : 1]` parts the conclusion with
every further binder held. -/
private def psi2Z : List BPair := [⟨2, 1⟩, uT]
private def jZ : List BPair := jetVec 5 32 oneT psi1T psi2Z
example : (dotN psi2Z psi2Z).scale 1 ≤ BPair.ofNat 1 := by decide +kernel
example : ¬ (dotN oneT psi2Z).oneValue BPair.unit := by decide +kernel
example : ¬ (windowsep.mag
      ((dotN jZ (matVec aT jZ)).scale (Pos.pow 32 4 * (1 * 1))
        + ((jetDisplay aT oneT psi1T psi2Z 5 32 * dotN jZ jZ).scale (1 * 1)).swap)
    ≤ truncCap 3 1 1 (dotN oneT (matVec aT oneT))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi1T))
        (BPair.ofNat 2 * dotN oneT (matVec aT psi2Z) + dotN psi1T (matVec aT psi1T)
          + (dotN oneT (matVec aT oneT) * dotN psi1T psi1T).swap)
        (dotN psi1T psi1T) (BPair.ofNat 1) 5 32) := by decide +kernel

/-- The off-line bound's electric refusal: at the electric member
`diag(−4, 1)`, off the positive-semidefinite read, with the magnetic
member vacant, the ray one and every further binder held — the drift
floor's Rayleigh read fails and the display parts. -/
private def eN : Mat := [[⟨1, 5⟩, uT], [uT, ⟨2, 1⟩]]
private def mN : Mat := [[uT, uT], [uT, uT]]
private def etN : Mat := [[uT, uT], [uT, ⟨6, 1⟩]]
private def tN : SqMat 2 := ⟨idMat 2, by decide +kernel⟩
private def lN : List (BPair × Pos × BPair) :=
  [(BPair.unit, 1, BPair.ofNat 1), (BPair.ofNat 5, 1, BPair.ofNat 1)]
private def spEN : Split 2 := mkSplit 2 eN
private def mmN : Mat := matScale Pos.one (matMul (transposeM mN) mN)
private def spUN : Split 2 := mkSplit 2 (siteDatum (matScale (1 * 1) (idMat 2)) mmN)
private def spLN : Split 2 := mkSplit 2 (matAdd (matScale (1 * 1) (idMat 2)) mmN)
private def jN : List BPair := [uT, ⟨2, 1⟩]
private def rN : List BPair := [uT, ⟨5, 1⟩]
private def psiN : List BPair := matVec tN.val (elim.idRow 2 0)
example : split.diagRead etN (idMat 2) tN tN lN := by decide +kernel
example : groundreads.clearRead lN 0 5 1 := by decide +kernel
example : matOneValue etN
    (siteDatum (matScale Pos.one (rayH 1 1 eN mN)) (matScaleB ⟨1, 5⟩ (idMat 2))) := by
  decide +kernel
example : splitRead eN spEN := by decide +kernel
example : capAt mmN (matScale (1 * 1) (idMat 2)) spUN spLN := by decide +kernel
example : poly.oneValue (vecScale (BPair.ofPos (4 * (1 * 1))) (matVec (rayH 1 1 eN mN) jN))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 1 4) * BPair.ofNat 0) jN).map BPair.swap) rN) := by
  decide +kernel
example : BPair.ofPos (1 * Pos.one * (1 * 1) * 1) < BPair.ofPos 5 := by decide +kernel
example : ¬ psdAt spEN := by decide +kernel
example : ¬ (((BPair.ofPos 5 + (BPair.ofPos (1 * Pos.one * (1 * 1) * 1)).swap)
      * (BPair.ofPos 5 + (BPair.ofPos (1 * Pos.one * (1 * 1) * 1)).swap)
      * dotN (residD [psiN] jN) (residD [psiN] jN)).scale (16 * Pos.pow 1 4)
    ≤ (dotN psiN psiN * dotN psiN psiN * dotN rN rN).scale
        (1 * 1 * (Pos.one * Pos.one))) := by
  decide +kernel

/-- The off-line bound's side refusal: at a clearance below the ray's
magnetic weight, `τ²W = 3` against `γ' = 1`, every further binder held
including the electric positive read — the squared comparison's side
condition parts the display. -/
private def eS : Mat := [[uT, uT], [uT, ⟨5, 1⟩]]
private def mS : Mat := [[uT, uT], [uT, ⟨4, 1⟩]]
private def etS : Mat := [[uT, uT], [uT, ⟨2, 1⟩]]
private def lS : List (BPair × Pos × BPair) :=
  [(BPair.unit, 1, BPair.ofNat 1), (BPair.ofNat 1, 1, BPair.ofNat 1)]
private def spES : Split 2 := mkSplit 2 eS
private def mmS : Mat := matScale Pos.one (matMul (transposeM mS) mS)
private def spUS : Split 2 := mkSplit 2 (siteDatum (matScale (3 * 3) (idMat 2)) mmS)
private def spLS : Split 2 := mkSplit 2 (matAdd (matScale (3 * 3) (idMat 2)) mmS)
example : split.diagRead etS (idMat 2) tN tN lS := by decide +kernel
example : groundreads.clearRead lS 0 1 1 := by decide +kernel
example : matOneValue etS
    (siteDatum (matScale Pos.one (rayH 1 1 eS mS)) (matScaleB BPair.unit (idMat 2))) := by
  decide +kernel
example : splitRead eS spES ∧ psdAt spES := by decide +kernel
example : capAt mmS (matScale (3 * 3) (idMat 2)) spUS spLS := by decide +kernel
example : poly.oneValue (vecScale (BPair.ofPos (4 * (1 * 1))) (matVec (rayH 1 1 eS mS) jN))
    (vecAdd ((vecScale (BPair.ofPos (Pos.pow 1 4) * BPair.ofNat 0) jN).map BPair.swap) rN) := by
  decide +kernel
example : ¬ (BPair.ofPos (1 * Pos.one * (1 * 1) * 3) < BPair.ofPos 1) := by decide +kernel
example : ¬ (((BPair.ofPos 1 + (BPair.ofPos (1 * Pos.one * (1 * 1) * 3)).swap)
      * (BPair.ofPos 1 + (BPair.ofPos (1 * Pos.one * (1 * 1) * 3)).swap)
      * dotN (residD [psiN] jN) (residD [psiN] jN)).scale (16 * Pos.pow 1 4)
    ≤ (dotN psiN psiN * dotN psiN psiN * dotN rN rN).scale
        (1 * 1 * (Pos.one * Pos.one))) := by
  decide +kernel
