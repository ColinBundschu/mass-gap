import MassGap.Ground
/-!
The check module for `def:ground`: the committed batteries re-read
the ground carrier's identity instances by kernel `decide` — the
arithmetic on the successor-count carrier, the trichotomy and gap
reads, the scalar-pair, balance-pair and composite displays with
the balance pair's margin at the count carrier, the cleared
pair's read at the cross-multiplied first data with its
composition, the homogeneity instances, and the harmonic numbers.  The
large-magnitude
products pin the carrier's kernel feasibility at the committed
magnitudes, machine integers under the stored counts.  The
partition tier closes the module: the weighted partition applied
whole at a repeated family over its distinct index with both
binders isolated at their refusals, and the constant-one fold's
length read.  The double count and the repeated key's occupancy
read stand beside it, each applied through its theorem with the
distinct keys' binder isolated at its refusal.  The gap fold's
exhaustion of a dominating bound and the family fold's domination
of its members stand beside them, each with its binder refused.
The matrix tier closes the module: the entry-formula builder's
displayed rows with the length, row, width, entry and congruence
reads at their theorem routes, and the refusals isolating the
range binders and the congruence's box.  The box at stated
per-key bounds closes it: the successor product's count and the
member count's one-at-the-bound read, each decided beside its
theorem route, with the vacant-bound instances beside them.  The
written key's read closes it: a write keeps the family's length,
the written key reads the written value and every further key is
kept, decided at an in-range write and at a key beyond the family
with the key binder refused there, each landed by the theorem
route.  The Pascal count and the binomial theorem close the
module: the count's interior values with its edge reads at the
nought key, at its own height and above its height, each beside its
theorem route, and the sum's power against the fold of the count
times the two members' complementary powers, decided raw and by its
theorem at two positive members and at a partner-signed pair with
the value pins beside them, the second power's key binder refused
at the first member's own key.  The halving search closes the
module: the least held key at a read stepping up the keys, read by
the halving and by the walk at the square's threshold and at the
budget `10²⁰`, one key through its theorem, with the stepping binder
refused at a read parting the two searches and the segment search's
binders refused in turn.  The polynomial device closes the module:
two count expressions at one normal form read one value at stated
data through the theorem, the value through the normal form, and a
third expression at a parted count refused at both.
-/

namespace ground


/-! The carrier's arithmetic, at numerals. -/

theorem pin1 : (2 : Pos) + 3 = 5 := by decide +kernel
theorem pin2 : (35 : Pos) * 35 = 1225 := by decide +kernel
theorem pin3 : succ (4 : Pos) = 5 := by decide +kernel
theorem pin4 : (5 : Pos) * 7 + 1 = 6 * 6 := by decide +kernel

/-- The kernel-feasibility exhibit at the Weingarten magnitude:
`d_f^4 · d_f^4` at `r = 5`. -/
theorem pin5 : (1296 : Pos) * 1296 = 1679616 := by decide +kernel

/-- The kernel-feasibility exhibit past the elimination's entry
growth: a 60-bit product at the stored counts' machine integers. -/
theorem pin6 : (123456789 : Pos) * 987654321 = 121932631112635269 := by
  decide +kernel

/-! The division with remainder, its naming read at the output. -/

theorem pin7 : divMod 13 3 = (some 4, some 1) := rfl
theorem pin8 : divMod 12 3 = (some 4, none) := rfl
theorem pin9 : divMod 2 5 = (none, some 2) := rfl
theorem pin10 : divModRead 13 3 := by decide +kernel
theorem pin11 : divModRead 12 3 := by decide +kernel
theorem pin12 : divModRead 2 5 := by decide +kernel
theorem pin13 : divModRead 1225 35 := by decide +kernel

/-! The quotient kit: the vacant divisor's and the vacant value's
quotients, a quotient at or below its dividend, the divisor joined once
at the remainder and at the quotient, and a divisor's own remainder and
quotient, each decided beside its theorem. -/
theorem pin14 : (7 : Nat) / 0 = 0 := by decide +kernel
theorem pin15 : (7 : Nat) / 0 = 0 := divZero 7
theorem pin16 : (0 : Nat) / 5 = 0 := divZeroLeft 5
theorem pin17 : (17 : Nat) / 5 ≤ 17 ∧ (17 : Nat) / 0 ≤ 17 := by decide +kernel
theorem pin18 : (17 : Nat) / 5 ≤ 17 := divLeSelf 17 5
theorem pin19 : (17 + 5) % 5 = 17 % 5 := modAddSelf 17 5
theorem pin20 : (15 + 5) / 5 = 15 / 5 + 1 := divAddSelf 15 5 (by decide +kernel) (by decide +kernel)
theorem pin21 : (15 + 5) / 5 = 4 := by decide +kernel
theorem pin22 : 5 % 5 = 0 ∧ 5 / 5 = 1 := ⟨modSelf 5, divSelf 5 (by decide +kernel)⟩

/-! The quotient's bracket: an occupied quotient brackets the
dividend between its own multiple and the next, a vacant quotient
prices the dividend below the divisor, and the bracket names the
quotient back — the theorem routes beside the decides. -/

theorem pin23 : (3 : Pos) * 4 ≤ 13 ∧ (13 : Pos) < 3 * ground.succ 4 :=
  divQuot_read 13 3 4 (by decide +kernel)
theorem pin24 : (3 : Pos) * 4 ≤ 13 ∧ (13 : Pos) < 3 * ground.succ 4 := by
  decide +kernel
theorem pin25 : (2 : Pos) < 5 := divQuot_vac 2 5 (by decide +kernel)
theorem pin26 : (ground.divMod 13 3).1 = some 4 :=
  divQuot_eq 13 3 4 (by decide +kernel) (by decide +kernel)
/-- The refusal isolating the bracket's upper end: at the forged
quotient the strict step refuses and the naming with it. -/
theorem pin27 : ¬ ((13 : Pos) < 3 * ground.succ 3) := by decide +kernel
theorem pin28 : ¬ ((ground.divMod 13 3).1 = some 3) := by decide +kernel

/-! Order as gap-existence, and the trichotomy: the read is data,
the gap constructed with the outcome. -/

theorem pin29 : (5 : Pos) < 12 := by decide +kernel
theorem pin30 : (5 : Pos) + 7 = 12 := by decide +kernel
theorem pin31 : ¬ ((12 : Pos) < 12) := by decide +kernel
theorem pin32 : (12 : Pos) ≤ 12 := by decide +kernel
theorem pin33 : (5 : Pos) ≤ 12 := by decide +kernel
theorem pin34 : (match trich (5 : Pos) 12 with
  | .lt g _ => some g | .eq _ => none | .gt _ _ => none) = some 7 := rfl
theorem pin35 : (match trich (12 : Pos) 5 with
  | .lt _ _ => none | .eq _ => none | .gt g _ => some g) = some 7 := rfl
theorem pin36 : (match BPair.side ⟨9, 9⟩ with
  | .lt _ _ => false | .eq _ => true | .gt _ _ => false) = true := rfl

/-! The scalar pair's displayed reads. -/

theorem pin37 : Pair.oneValue (⟨1, 2⟩ + ⟨1, 3⟩) ⟨5, 6⟩ := by decide +kernel
theorem pin38 : Pair.oneValue ((⟨2, 3⟩ : Pair) * ⟨3, 2⟩) (Pair.ofPos 1) := by
  decide +kernel
theorem pin39 : (⟨1, 3⟩ : Pair) < ⟨1, 2⟩ := by decide +kernel
theorem pin40 : Pair.oneValue (Pair.cofactor ⟨3, 4⟩ ⟨1, 2⟩) ⟨3, 2⟩ := by decide +kernel

/-- A homogeneity instance: the sum's read at a rescaled
representative. -/
theorem pin41 : Pair.oneValue (⟨2, 4⟩ : Pair) ⟨1, 2⟩
    ∧ Pair.oneValue ((⟨2, 4⟩ : Pair) + ⟨1, 3⟩) ((⟨1, 2⟩ : Pair) + ⟨1, 3⟩)
    := by decide +kernel

/-! The harmonic numbers. -/

theorem pin42 : Pair.oneValue (harmonic 1) (Pair.ofPos 1) := by decide +kernel
theorem pin43 : Pair.oneValue (harmonic 3) ⟨11, 6⟩ := by decide +kernel
theorem pin44 : Pair.oneValue (harmonic 5) ⟨137, 60⟩ := by decide +kernel
theorem pin45 : harmonic (succ 2) = harmonic 2 + ⟨1, succ 2⟩ := harmonic_succ 2
theorem pin46 : Pair.oneValue (harmonic 2 + ⟨1, 3⟩) (harmonic 3) := by decide +kernel

/-! The balance pair's displayed reads. -/

theorem pin47 : BPair.oneValue ((⟨3, 1⟩ : BPair) * ⟨5, 2⟩) ⟨7, 1⟩ := by decide +kernel
theorem pin48 : BPair.oneValue ((⟨5, 2⟩ : BPair) + BPair.swap ⟨5, 2⟩)
    BPair.unit := by decide +kernel
theorem pin49 : BPair.oneValue (BPair.addPos ⟨2, 5⟩ 3) BPair.unit := by decide +kernel
theorem pin50 : (⟨2, 5⟩ : BPair) < ⟨4, 1⟩ := by decide +kernel
theorem pin51 : BPair.oneValue (BPair.sum [⟨2, 1⟩, ⟨1, 3⟩, ⟨5, 1⟩]) ⟨4, 1⟩ := by
  decide +kernel

/-! The canonical representative at a witnessed gap: the side's
one-member display reads the gap's successor at the exceeding
member either way, decided and through its theorem, with the
forged gap refused. -/

theorem pin52 : (⟨2, 5⟩ : BPair).norm = ⟨Pos.one, succ 3⟩ := by decide +kernel
theorem pin53 : (⟨2, 5⟩ : BPair).norm = ⟨Pos.one, succ 3⟩ :=
  BPair.norm_of_gapLt (g := 3) (by decide +kernel)
theorem pin54 : ¬ (⟨2, 5⟩ : BPair).norm = ⟨Pos.one, succ 2⟩ := by decide +kernel

theorem pin55 : (⟨5, 2⟩ : BPair).norm = ⟨succ 3, Pos.one⟩ := by decide +kernel
theorem pin56 : (⟨5, 2⟩ : BPair).norm = ⟨succ 3, Pos.one⟩ :=
  BPair.norm_of_gapGt (g := 3) (by decide +kernel)
theorem pin57 : ¬ (⟨5, 2⟩ : BPair).norm = ⟨succ 4, Pos.one⟩ := by decide +kernel

/-! The stored count's injectivity read, the literal-multiplier
expansions, and the unit summands' sum, each decided and through
its theorem. -/

theorem pin58 : (1 + 1 : Nat) = 2 := by decide +kernel
theorem pin59 : (1 + 1 : Nat) = 2 :=
  ground.posMkInj (a := 1 + 1) (b := 2) rfl

theorem pin60 : 3 * 7 = 7 + 7 + 7 := by decide +kernel
theorem pin61 : 3 * 7 = 7 + 7 + 7 := ground.threeMul 7
theorem pin62 : 4 * 7 = 2 * 7 + 2 * 7 := by decide +kernel
theorem pin63 : 4 * 7 = 2 * 7 + 2 * 7 := ground.fourMul 7

theorem pin64 : ((⟨2, 2⟩ : BPair) + ⟨5, 5⟩).oneValue BPair.unit := by
  decide +kernel
theorem pin65 : ((⟨2, 2⟩ : BPair) + ⟨5, 5⟩).oneValue BPair.unit :=
  BPair.add_units (by decide +kernel) (by decide +kernel)
theorem pin66 : ¬ ((⟨3, 2⟩ : BPair) + ⟨5, 5⟩).oneValue BPair.unit := by
  decide +kernel

/-! The margin at the count carrier: the exceeding member's gap
either way, an equal-membered pair at nought. -/

theorem pin67 : BPair.marginN ⟨3, 1⟩ = 2 := by decide +kernel
theorem pin68 : BPair.marginN ⟨2, 2⟩ = 0 := by decide +kernel
theorem pin69 : BPair.marginN ⟨1, 5⟩ = 4 := by decide +kernel

/-! The margin kit's instances: the class read at one count on
either side, the sum at unit-dominant pairs, the natural entries'
counts, and the return to the entry at one value — each beside its
kernel value pin. -/

theorem pin70 : BPair.marginN ⟨6, 2⟩ = BPair.marginN ⟨5, 1⟩ :=
  BPair.marginN_congr (by decide +kernel)
theorem pin71 : BPair.marginN ⟨2, 6⟩ = BPair.marginN ⟨1, 5⟩ :=
  BPair.marginN_congr (by decide +kernel)
theorem pin72 : BPair.marginN (BPair.add ⟨5, 2⟩ ⟨4, 1⟩)
    = BPair.marginN ⟨5, 2⟩ + BPair.marginN ⟨4, 1⟩ := by decide +kernel
theorem pin73 : BPair.marginN (BPair.add ⟨5, 2⟩ ⟨4, 1⟩)
    = BPair.marginN ⟨5, 2⟩ + BPair.marginN ⟨4, 1⟩ :=
  BPair.marginN_add (by decide +kernel) (by decide +kernel)
theorem pin74 : (BPair.ofNat 3).marginN = 3 := by decide +kernel
theorem pin75 : (BPair.ofNat 0).marginN = 0 := by decide +kernel
theorem pin76 : (⟨5, 2⟩ : BPair).oneValue
    (BPair.ofNat (BPair.marginN ⟨5, 2⟩)) := by decide +kernel
theorem pin77 : (⟨5, 2⟩ : BPair).oneValue
    (BPair.ofNat (BPair.marginN ⟨5, 2⟩)) :=
  BPair.ofNat_marginN (by decide +kernel)

/-! The composite pair's displayed reads. -/

theorem pin78 : CPair.oneValue ((⟨⟨1, 2⟩, 3⟩ : CPair) + ⟨⟨2, 1⟩, 4⟩)
    ⟨⟨10, 11⟩, 12⟩ := by decide +kernel
theorem pin79 : CPair.oneValue ((⟨⟨2, 1⟩, 3⟩ : CPair) * ⟨⟨1, 2⟩, 2⟩)
    ⟨⟨1, 2⟩, 6⟩ := by decide +kernel
theorem pin80 : CPair.oneValue (CPair.ofPair ⟨3, 4⟩ 1) (CPair.ofPair ⟨3, 4⟩ 7)
    := by decide +kernel
theorem pin81 : CPair.oneValue (CPair.ofPair ⟨1, 2⟩ 1) ⟨⟨3, 2⟩, 2⟩ := by decide +kernel
theorem pin82 : (⟨⟨1, 2⟩, 3⟩ : CPair) < ⟨⟨2, 1⟩, 4⟩ := by decide +kernel
theorem pin83 : CPair.oneValue ((⟨⟨5, 2⟩, 3⟩ : CPair) + ⟨⟨4, 4⟩, 7⟩)
    ⟨⟨5, 2⟩, 3⟩ := by decide +kernel

/-! The cleared pair's read: a balance datum at its stated positive
clearing, two such data reading one value exactly at the
cross-multiplied first data, with the join at the cross-multiplied
numerators and the read's composition. -/

theorem pin84 : ground.keysBelow 5 [(0, BPair.ofNat 2), (4, BPair.unit)] := by
  decide +kernel
theorem pin85 : ¬ ground.keysBelow 4 [(0, BPair.ofNat 2), (4, BPair.unit)] := by
  decide +kernel

private theorem qHalfRead :
    qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 3, (1 : Pos)) := by
  decide +kernel

theorem pin86 : qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 3, (1 : Pos)) :=
  qHalfRead

/-- The cross multiplication is load-bearing: at the clearings `2`
and `1` the first data `6` and `4` read `6` against `8`. -/
theorem pin87 : ¬ qOneValue (BPair.ofNat 6, (2 : Pos))
    (BPair.ofNat 4, (1 : Pos)) := by decide +kernel

theorem pin88 : (BPair.addQ (BPair.ofNat 6, (2 : Pos))
    (BPair.ofNat 3, (1 : Pos))).1.oneValue (BPair.ofNat 12) := by
  decide +kernel
theorem pin89 : (BPair.addQ (BPair.ofNat 6, (2 : Pos))
    (BPair.ofNat 3, (1 : Pos))).2 = 2 := by decide +kernel

theorem pin90 : qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 9, (3 : Pos)) := by
  decide +kernel

theorem pin91 : qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 9, (3 : Pos)) :=
  qOneValue_trans qHalfRead (by decide +kernel)

/-! The collect-by-count fold's decided pin: the family's fold
against the multiplicity-weighted base read. -/

theorem pin92 : ground.famFold Nat.add 0 (fun x => x * x) [2, 1, 2]
    = ground.famFold Nat.add 0
      (fun m => ground.countOf m [2, 1, 2] * (m * m))
      [1, 2, 3] := by decide +kernel

theorem pin93 : ground.famFold Nat.add 0 (fun x => x * x) [2, 1, 2]
    = ground.famFold Nat.add 0
      (fun m => ground.countOf m [2, 1, 2] * (m * m))
      [1, 2, 3] :=
  ground.famFold_countCollect (fun x => x * x) [2, 1, 2] [1, 2, 3]
    (fun x hx => by
      by_cases h2 : x = 2
      · rw [h2]
        decide +kernel
      · by_cases h1 : x = 1
        · rw [h1]
          decide +kernel
        · rw [show ground.countOf x [2, 1, 2]
              = (if x = 2 then 1 else 0) + ((if x = 1 then 1 else 0)
                + ((if x = 2 then 1 else 0)
                  + ground.countOf x ([] : List Nat)))
              from by
                rw [ground.countOf_cons, ground.countOf_cons,
                  ground.countOf_cons],
            if_neg h2, if_neg h1] at hx
          exact absurd hx (Nat.lt_irrefl 0))

/-! The signed-count tier (`thm:memberchar`'s subset-fold carrier):
the count pair's reads, the graded entry, and the pairing-off
fold. -/

theorem pin94 : (BPair.ofCounts 2 3).oneValue
    (BPair.ofNat 2 + (BPair.ofNat 3).swap) := by decide +kernel
theorem pin95 : (BPair.ofCounts 4 4).oneValue BPair.unit := by decide +kernel
theorem pin96 : (BPair.ofCounts 0 0).oneValue BPair.unit :=
  BPair.ofCounts_zero
theorem pin97 : (BPair.ofCounts (1 + 3) (2 + 1)).oneValue
    (BPair.ofCounts 1 2 + BPair.ofCounts 3 1) :=
  BPair.ofCounts_add 1 2 3 1
theorem pin98 : (BPair.ofCounts
      (ground.famFold Nat.add 0 (fun x => x) [1, 2])
      (ground.famFold Nat.add 0 (fun x => x + 1) [1, 2])).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun x => BPair.ofCounts x (x + 1)) [1, 2]) :=
  ground.foldB_ofCounts (fun x => x) (fun x => x + 1) [1, 2]
theorem pin99 : ground.signedAt false (BPair.ofNat 7) = BPair.ofNat 7 := by
  decide +kernel
theorem pin100 : ground.signedAt true (BPair.ofNat 7)
    = (BPair.ofNat 7).swap := by decide +kernel
theorem pin101 : (ground.signedAt true (BPair.ofCounts 5 5)).oneValue
    BPair.unit :=
  ground.signedAt_unit true (by decide +kernel)
theorem pin102 : (ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2 (BPair.ofCounts 3 1))
      [(true, true), (true, false)]).oneValue BPair.unit :=
  ground.signedFold_null (fun _ => BPair.ofCounts 3 1) 2
    [(true, true), (true, false)] (by decide +kernel)
    (fun k _ => by
      cases k with
      | true => exact Or.inl (by decide +kernel)
      | false => exact Or.inl (by decide +kernel))
theorem pin103 : (ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2 (BPair.ofCounts 2 2))
      [(false, true)]).oneValue BPair.unit :=
  ground.signedFold_null (fun _ => BPair.ofCounts 2 2) 1
    [(false, true)] (by decide +kernel)
    (fun k _ => Or.inr (by decide +kernel))
theorem pin104 : ¬ (ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2
        (BPair.ofCounts (vp.1 + 2) 0))
      [(3, true), (3, true)]).oneValue BPair.unit := by decide +kernel

/-! The partition tier's pins: the weighted partition applied whole
at a repeated family over its distinct index, the two binders
isolated at their refusals, and the constant-one fold's length
read.  The covering binder is taken at the count's occupancy and
carried to membership by `mem_of_countOf_pos`, the kernel's own
clean read of the list. -/

/-- The weighted partition at `[2, 1, 2, 3]` over the distinct
index `[1, 2, 3]`, the doubling weight: the theorem's own instance
with the shared value beside it. -/
theorem pin105 : ground.famFold Nat.add 0 (fun k => 2 * k) [2, 1, 2, 3]
    = ground.famFold Nat.add 0
      (fun k => ground.countOf k [2, 1, 2, 3] * (2 * k)) [1, 2, 3] := by
  have hcov : ∀ x ∈ [2, 1, 2, 3], 0 < ground.countOf x [1, 2, 3] := by
    decide +kernel
  exact ground.famFold_partition (fun k => 2 * k) [2, 1, 2, 3] [1, 2, 3]
    (by decide +kernel)
    (fun x hx => ground.mem_of_countOf_pos x [1, 2, 3] (hcov x hx))

theorem pin106 : ground.famFold Nat.add 0 (fun k => 2 * k) [2, 1, 2, 3] = 16 := by
  decide +kernel

theorem pin107 : ground.famFold Nat.add 0
    (fun k => ground.countOf k [2, 1, 2, 3] * (2 * k)) [1, 2, 3] = 16 := by
  decide +kernel

/-- Refusal isolating `distinctList D`: at the repeated index
`[1, 1]` the weighted fold counts the member twice and the two
sides part, the covering binder surviving beside it. -/
theorem pin108 : ¬ (ground.famFold Nat.add 0 (fun k => 2 * k) [1]
    = ground.famFold Nat.add 0
      (fun k => ground.countOf k [1] * (2 * k)) [1, 1]) := by decide +kernel

theorem pin109 : ∀ x ∈ [1], 0 < ground.countOf x [1, 1] := by decide +kernel

theorem pin110 : ¬ ground.distinctList [1, 1] := by decide +kernel

/-- Refusal isolating the covering binder: at the vacant index the
weighted fold reads the count's unit against an occupied family,
the distinctness surviving beside it. -/
theorem pin111 : ¬ (ground.famFold Nat.add 0 (fun k => 2 * k) [1]
    = ground.famFold Nat.add 0
      (fun k => ground.countOf k [1] * (2 * k)) ([] : List Nat)) := by
  decide +kernel

theorem pin112 : ground.distinctList ([] : List Nat) := by decide +kernel

/-- The constant-one fold at its length, the theorem's instance
with the value beside it. -/
theorem pin113 : ground.famFold Nat.add 0 (fun _ => (1 : Nat)) [7, 7, 3]
    = [7, 7, 3].length := ground.famFold_length [7, 7, 3]

theorem pin114 : ground.famFold Nat.add 0 (fun _ => (1 : Nat)) [7, 7, 3] = 3 := by
  decide +kernel
/-! The list kit's adjacent exchange (`adjSwap`): the pair at a key
and its successor trade places, a key beyond the list's top and a
list of one member reading the list itself. -/

theorem pin115 : adjSwap 0 ([1, 2, 3] : List Nat) = [2, 1, 3] := by decide +kernel
theorem pin116 : adjSwap 1 ([1, 2, 3] : List Nat) = [1, 3, 2] := by decide +kernel
theorem pin117 : adjSwap 0 ([] : List Nat) = [] := by decide +kernel
theorem pin118 : adjSwap 2 ([1, 2] : List Nat) = [1, 2] := by decide +kernel

/-! The power's computing read against the displayed fold: the
value agreement at stated data, the theorem route, the unit base,
and the exponents' join at a depth the fold's step count sits far
beyond, read through the displayed product alone. -/

theorem pin119 : Pos.powC (3 : Pos) 7 = Pos.pow (3 : Pos) 7 := by decide +kernel
theorem pin120 : Pos.powC (3 : Pos) 7 = Pos.pow (3 : Pos) 7 :=
  Pos.powC_eq (3 : Pos) 7
theorem pin121 : Pos.powC Pos.one 12 = Pos.one := by decide +kernel
theorem pin122 : Pos.powC (2 : Pos) 200
    = Pos.powC (2 : Pos) 120 * Pos.powC (2 : Pos) 80 := by decide +kernel

/-! The positive power at the balance carrier: the sited power
against the balance power of its entry, decided and through the
theorem. -/

theorem pin123 : (BPair.ofPos (Pos.pow 3 2)).oneValue (bpow (BPair.ofPos 3) 2) := by
  decide +kernel
theorem pin124 : (BPair.ofPos (Pos.pow 3 2)).oneValue (bpow (BPair.ofPos 3) 2) :=
  ofPos_pow 3 2

/-! The successor power's read at the base against the power, the
unit base's absorbed read, and the power's side at a base at or
beyond the sum's unit — each through the theorem beside its decided
instance, the order read with its binder's isolating refusal. -/

theorem pin125 : (bpow (BPair.ofNat 2) 3).oneValue
    (BPair.ofNat 2 * bpow (BPair.ofNat 2) 2) := by decide +kernel
theorem pin126 : (bpow (BPair.ofNat 2) 3).oneValue
    (BPair.ofNat 2 * bpow (BPair.ofNat 2) 2) :=
  bpow_succ_read (BPair.ofNat 2) 2
theorem pin127 : ¬ ((bpow (BPair.ofNat 2) 3).oneValue
    (BPair.ofNat 2 * bpow (BPair.ofNat 2) 1)) := by decide +kernel

theorem pin128 : (bpow BPair.unit 3).oneValue BPair.unit := by decide +kernel
theorem pin129 : (bpow BPair.unit 3).oneValue BPair.unit := bpow_unit_succ 2
theorem pin130 : ¬ ((bpow (BPair.ofNat 2) 3).oneValue BPair.unit) := by
  decide +kernel

theorem pin131 : BPair.unit ≤ bpow (BPair.ofNat 2) 3 := by decide +kernel
theorem pin132 : BPair.unit ≤ bpow (BPair.ofNat 2) 3 :=
  unitLeBpow (unitLeOfNat 2) 3
theorem pin133 : ¬ (BPair.unit ≤ (BPair.ofNat 2).swap) := by decide +kernel
theorem pin134 : ¬ (BPair.unit ≤ bpow ((BPair.ofNat 2).swap) 1) := by
  decide +kernel

/-! The order's scaling tier: the strict read at a factor strictly
above the sum's unit, the cancellation back off that factor, and
the squared comparison's read back at the trichotomy — each at a
committed pair with the binder's own isolating refusal. -/

/-- The strict read scales: `1 < 3` against the factor `2` reads
`2 < 6`, decided and through the theorem. -/
theorem pin135 : (⟨2, 1⟩ : BPair) < ⟨4, 1⟩ := by decide +kernel

theorem pin136 : (⟨2, 1⟩ : BPair) * ⟨3, 1⟩ < ⟨4, 1⟩ * ⟨3, 1⟩ := by decide +kernel

theorem pin137 : (⟨2, 1⟩ : BPair) * ⟨3, 1⟩ < ⟨4, 1⟩ * ⟨3, 1⟩ :=
  ground.ltB_mulPos (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hc`: at the sum's unit the factor collapses
both sides to that unit and the strict conclusion refuses, the
strict read on the data surviving beside it. -/
theorem pin138 : ¬ (BPair.unit < BPair.unit) := by decide +kernel

theorem pin139 : ¬ ((⟨2, 1⟩ : BPair) * BPair.unit
    < ⟨4, 1⟩ * BPair.unit) := by decide +kernel

/-- The cancellation: at the factor `2` the scaled read `2 ≤ 6`
returns `1 ≤ 3`, decided and through the theorem. -/
theorem pin140 : (⟨2, 1⟩ : BPair) * ⟨3, 1⟩ ≤ ⟨4, 1⟩ * ⟨3, 1⟩ := by decide +kernel

theorem pin141 : (⟨2, 1⟩ : BPair) ≤ ⟨4, 1⟩ := by decide +kernel

theorem pin142 : (⟨2, 1⟩ : BPair) ≤ ⟨4, 1⟩ :=
  ground.leB_unscale (c := ⟨3, 1⟩) (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hc` at the cancellation: the sum's unit
carries the scaled read at every pair, `2` against `-2` included,
while the returned order refuses. -/
theorem pin143 : (⟨3, 1⟩ : BPair) * BPair.unit ≤ ⟨1, 3⟩ * BPair.unit := by
  decide +kernel

theorem pin144 : ¬ ((⟨3, 1⟩ : BPair) ≤ ⟨1, 3⟩) := by decide +kernel

/-- The squared comparison's read back: at `a = -1` against
`b = 1` the squares tie at `1`, the strict read refuses, and the
data read `-1 ≤ 1`, decided and through the theorem. -/
theorem pin145 : BPair.unit ≤ (⟨2, 1⟩ : BPair) := by decide +kernel

theorem pin146 : ¬ ((⟨2, 1⟩ : BPair) * ⟨2, 1⟩ < (⟨2, 3⟩ : BPair) * ⟨2, 3⟩) := by
  decide +kernel

theorem pin147 : (⟨2, 3⟩ : BPair) ≤ ⟨2, 1⟩ := by decide +kernel

theorem pin148 : (⟨2, 3⟩ : BPair) ≤ ⟨2, 1⟩ :=
  ground.leB_of_sq_le (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hb`: at `b = -1` the squares still tie at
`1` and the strict read still refuses, yet the datum at or above
the sum's unit is the missing read and the conclusion refuses. -/
theorem pin149 : ¬ (BPair.unit ≤ (⟨1, 2⟩ : BPair)) := by decide +kernel

theorem pin150 : ¬ ((⟨1, 2⟩ : BPair) * ⟨1, 2⟩ < (⟨2, 1⟩ : BPair) * ⟨2, 1⟩) := by
  decide +kernel

theorem pin151 : ¬ ((⟨2, 1⟩ : BPair) ≤ ⟨1, 2⟩) := by decide +kernel

/-! The subtraction exchanges, the product's left and four-factor
exchanges and the family dropped at its own width — the
hand-rolled reads at the poisoned core neighborhood. -/

theorem pin152 : 7 + 4 - (2 + 4) = 7 - 2 := ground.addSubAddR 7 2 4
theorem pin153 : (7 - 2) * 3 = 7 * 3 - 2 * 3 := ground.subMulR 7 2 3
theorem pin154 : 3 * (5 * 4) = 5 * (3 * 4) := ground.mulLeftComm 3 5 4
theorem pin155 : 2 * 3 * (5 * 7) = 210 := by decide +kernel
theorem pin156 : 2 * 3 * (5 * 7) = 2 * 5 * (3 * 7) :=
  ground.mulMulMulComm 2 3 5 7

/-! The sum's rearrangements: the triple's ends exchanged, the
joined pair's head opened at the front with and without the
standing second withdrawn to the tail, and the second summand
rotated past the tail pair. -/

theorem pin157 : 2 + 3 + 5 = 5 + 3 + 2 := ground.addSwapEnds 2 3 5
theorem pin158 : 2 + 3 + (5 + 7) = 5 + (2 + 7) + 3 :=
  ground.addJoinHeadOut 2 3 5 7
theorem pin159 : 2 + 3 + (5 + 7) = 5 + 2 + (3 + 7) :=
  ground.addJoinHeadFront 2 3 5 7
theorem pin160 : 2 + 3 + 5 + 7 = 2 + 5 + 7 + 3 := ground.addRotTail3 2 3 5 7

/-! The balance carrier's own rearrangements: the seeded sum and
the seeded product each exchanging their two trailing members,
three factors read at their reversal with the middle standing, the
head passing inside the trailing product, the trailing factors
exchanging across the head, and the leftward rotation.
Each stands beside its perturbed refusal, the exchanged member
replaced by a member off its own value. -/

theorem pin161 : (⟨2, 1⟩ : BPair) + ⟨1, 3⟩ + ⟨5, 1⟩ = ⟨8, 5⟩ := by decide +kernel
theorem pin162 : (⟨2, 1⟩ : BPair) + ⟨1, 3⟩ + ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) + ⟨5, 1⟩ + ⟨1, 3⟩ :=
  BPair.add_right_comm ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
theorem pin163 : ¬ ((⟨2, 1⟩ : BPair) + ⟨1, 3⟩ + ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) + ⟨5, 1⟩ + ⟨3, 1⟩) := by decide +kernel

theorem pin164 : (⟨2, 1⟩ : BPair) * ⟨1, 3⟩ * ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨1, 3⟩ :=
  BPair.mul_right_comm ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
theorem pin165 : ¬ ((⟨2, 1⟩ : BPair) * ⟨1, 3⟩ * ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨3, 1⟩) := by decide +kernel

theorem pin166 : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨5, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨2, 1⟩) :=
  BPair.mul_rot3r ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
theorem pin167 : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨5, 1⟩ : BPair) * (⟨3, 1⟩ * ⟨2, 1⟩)) := by decide +kernel

theorem pin168 : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨1, 3⟩ : BPair) * ⟨2, 1⟩ * ⟨5, 1⟩ :=
  BPair.mul_left_comm' ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
theorem pin169 : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨3, 1⟩ : BPair) * ⟨2, 1⟩ * ⟨5, 1⟩) := by decide +kernel

theorem pin170 : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨1, 3⟩ :=
  BPair.mul_right_comm' ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
theorem pin171 : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨3, 1⟩) := by decide +kernel

theorem pin172 : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨1, 3⟩ : BPair) * (⟨5, 1⟩ * ⟨2, 1⟩) :=
  BPair.mul_rot3l ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
theorem pin173 : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨1, 3⟩ : BPair) * (⟨5, 1⟩ * ⟨3, 1⟩)) := by decide +kernel

/-! The componentwise walk at a vacant second family, vacant at
every first family, beside the occupied second family's refusal. -/

theorem pin174 : List.zipWith (· + ·) [3, 1, 4] ([] : List Nat) = [] :=
  ground.zipWith_nil_right (· + ·) [3, 1, 4]
theorem pin175 : ¬ (List.zipWith (· + ·) [3, 1, 4] [1, 5] = []) := by decide +kernel

theorem pin176 : ([3, 1, 4] : List Nat).drop ([3, 1, 4] : List Nat).length = [] :=
  ground.dropLength [3, 1, 4]
theorem pin177 : ([3, 1, 4] : List Nat).drop 2 = [4] := by decide +kernel
theorem pin178 : ¬ ((!true) = true) := ground.boolNotSelf true
theorem pin179 : ¬ ((!false) = false) := ground.boolNotSelf false
theorem pin180 : (true && true) = true := ground.andIntroB rfl rfl
theorem pin181 : ¬ ((true && false) = true) := by decide +kernel

/-! The guard kit at withheld values: two values at one guard sum
at the guard, and nested guards exchange — each at a concrete
value with its refusal, the second guard's own test and the
withheld arm's vanishing the two load-bearing conjuncts. -/

theorem pin182 : (if 2 < 5 then 3 else 0) + (if 2 < 5 then 4 else 0) = 7 := by
  decide +kernel
theorem pin183 : (if 2 < 5 then 3 else 0) + (if 2 < 5 then 4 else 0)
    = if 2 < 5 then 3 + 4 else 0 := ground.if_add (2 < 5) 3 4
theorem pin184 : ¬ ((if 2 < 5 then 3 else 0) + (if 5 < 2 then 4 else 0)
    = if 2 < 5 then 3 + 4 else 0) := by decide +kernel

theorem pin185 : (if 2 < 5 then (if 1 < 4 then 7 else 0) else 0) = 7 := by
  decide +kernel
theorem pin186 : (if 2 < 5 then (if 1 < 4 then 7 else 0) else 0)
    = if 1 < 4 then (if 2 < 5 then 7 else 0) else 0 :=
  ground.if_swap (2 < 5) (1 < 4) 7
theorem pin187 : ¬ ((if 5 < 2 then (if 1 < 4 then 7 else 0) else 9)
    = if 1 < 4 then (if 5 < 2 then 7 else 0) else 9) := by decide +kernel

/-! The count carrier's key-list and reversal kit: the totals, the
leading segments at the vacant, full and complement-join reads,
the reversed display's counts and entries, the join's reversal
with the involution, and the struck unit family's total.  The
leading segment's two arithmetic reads close the section: the
memberwise sum's prefix at matched counts, with the refusal at
parted counts where the truncated join drops the second family's
tail, and the constant block's prefix at the key count against the
repeated entry, with the refusal past the block where the prefix
caps at the total against the linear read. -/

theorem pin188 : sumNat [3, 1, 4, 1, 5] = 14 := by decide +kernel
theorem pin189 : prefixAt 0 [3, 1, 4] = 0 := by decide +kernel
theorem pin190 : prefixAt 2 [3, 1, 4] = 4 := by decide +kernel
theorem pin191 : prefixAt 3 [3, 1, 4] = 8 := by decide +kernel
theorem pin192 : prefixAt 3 [5, 1, 7, 9] = 13 := by decide +kernel
theorem pin193 : prefixAt 5 [3, 1, 4] = sumNat [3, 1, 4] := by decide +kernel
theorem pin194 : getAt 0 ([3, 1, 4].reverse) 0 = getAt 0 [3, 1, 4] 2 := by
  decide +kernel
theorem pin195 : getAt 0 ([1, 2, 3] : List Nat).reverse 0 = 3 := by decide +kernel
theorem pin196 : prefixAt 1 ([3, 1, 4].reverse) + prefixAt 2 [3, 1, 4]
    = sumNat [3, 1, 4] := by decide +kernel
theorem pin197 : prefixAt 1 ([3, 1, 4].reverse) + prefixAt 2 [3, 1, 4]
    = sumNat [3, 1, 4] :=
  prefix_reverse_join 1 [3, 1, 4] 2 (by decide +kernel)
theorem pin198 : ([1, 2, 3] : List Nat).reverse = [3, 2, 1] := by decide +kernel
theorem pin199 : countOf 2 ([1, 2, 2, 3].reverse) = 2 := by decide +kernel
theorem pin200 : (([4, 5] : List Nat) ++ [6, 7]).reverse = [7, 6, 5, 4] := by
  decide +kernel
theorem pin201 : ([2, 4, 6] : List Nat).reverse.reverse = [2, 4, 6] := by
  decide +kernel
theorem pin202 : sumNat (List.replicate 2 1 ++ 0 :: List.replicate 3 1)
    = 5 := by decide +kernel
theorem pin203 : sumNat (List.replicate 2 1 ++ 0 :: List.replicate 3 1)
    = 5 := sumNat_replicate_strike 2 5 (by decide +kernel)

theorem pin204 : prefixAt 0 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 0 [2, 1] + prefixAt 0 [0, 3] := by decide +kernel
theorem pin205 : prefixAt 1 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 1 [2, 1] + prefixAt 1 [0, 3] := by decide +kernel
theorem pin206 : prefixAt 2 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 2 [2, 1] + prefixAt 2 [0, 3] := by decide +kernel
theorem pin207 : prefixAt 3 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 3 [2, 1] + prefixAt 3 [0, 3] := by decide +kernel
theorem pin208 : prefixAt 2 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 2 [2, 1] + prefixAt 2 [0, 3] :=
  prefixAt_zipAdd [2, 1] [0, 3] (by decide +kernel) 2

/-- Refusal isolating the matched counts: at a parted pair the
join truncates to the shorter family and the read misses the
longer family's tail. -/
theorem pin209 : ¬ (prefixAt 2 (List.zipWith (fun u w => u + w) [2, 1] [0])
    = prefixAt 2 [2, 1] + prefixAt 2 [0]) := by decide +kernel

theorem pin210 : prefixAt 2 (List.replicate 3 2) = 2 * 2 := by decide +kernel
theorem pin211 : prefixAt 2 (List.replicate 3 2) = 2 * 2 :=
  prefixAt_replicate 3 2 2 (by decide +kernel)

/-- Refusal isolating `k ≤ d`: one key past the block the prefix
caps at the block's total while the linear read runs on. -/
theorem pin212 : ¬ (prefixAt 4 (List.replicate 3 2) = 4 * 2) := by decide +kernel

/-! The unit family at a key: the total one inside the width, the
width binder's refusal at a key beyond it (the vacant family's
total misses the one). -/

theorem pin213 : sumNat (unitAt 3 1) = 1 := by decide +kernel
theorem pin214 : sumNat (unitAt 3 1) = 1 := sumNat_unitAt 3 1 (by decide +kernel)
theorem pin215 : ¬ (sumNat (unitAt 2 5) = 1) := by decide +kernel
theorem pin216 : dotNat [1, 2, 3] [4, 5, 6] = 32 := by decide +kernel

/-! The double count: one family's counts in the other folded at
either order, the indicator's double fold both ways. -/

theorem pin217 : ground.famFold Nat.add 0
    (fun a => ground.countOf a [2, 3, 3]) [1, 2, 2, 3] = 4 := by decide +kernel

theorem pin218 : ground.famFold Nat.add 0
    (fun s => ground.countOf s [1, 2, 2, 3]) [2, 3, 3] = 4 := by decide +kernel

theorem pin219 : ground.famFold Nat.add 0
      (fun a => ground.countOf a [2, 3, 3]) [1, 2, 2, 3]
    = ground.famFold Nat.add 0
      (fun s => ground.countOf s [1, 2, 2, 3]) [2, 3, 3] :=
  ground.famFold_countSwap [1, 2, 2, 3] [2, 3, 3]

/-! Two distinct keys at one value: the value's count at two or
beyond. -/

theorem pin220 : ground.countOf (ground.getAt 0 [5, 7, 5] 0) [5, 7, 5] = 2 := by
  decide +kernel

theorem pin221 : 2 ≤ ground.countOf (ground.getAt 0 [5, 7, 5] 0) [5, 7, 5] :=
  ground.countOf_two_pos 0 [5, 7, 5] 0 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hne`: at one key read against itself the
singleton carries its value once, and the two-or-beyond read
refuses. -/
theorem pin222 : ¬ 2 ≤ ground.countOf 1 [1] := by decide +kernel

/-! A mapped family's count as the guarded fold over the source,
decided at one instance and applied through the theorem. -/

theorem pin223 : ground.countOf 4 ([1, 2, 3].map (fun x => x + x)) = 1 := by
  decide +kernel

theorem pin224 : ground.countOf 4 ([1, 2, 3].map (fun x => x + x))
    = ground.famFold Nat.add 0
      (fun j => if 4 = j + j then 1 else 0) [1, 2, 3] :=
  ground.countOf_map_famFold 4 (fun x => x + x) [1, 2, 3]

/-! The repeated family's counts: its own member at the repeat
count, a further letter at the fold's unit — decided at an instance
each beside the theorems' routes. -/

theorem pin225 : ground.countOf 7 (List.replicate 4 7) = 4 := by decide +kernel

theorem pin226 : ground.countOf 7 (List.replicate 4 7) = 4 :=
  ground.countOf_replicate 7 4

theorem pin227 : ground.countOf 5 (List.replicate 4 7) = 0 := by decide +kernel

theorem pin228 : ground.countOf 5 (List.replicate 4 7) = 0 :=
  ground.countOf_replicate_ne 5 7 (by decide +kernel) 4

/-! The adjacent exchange of the key list: the entry read at the
traded keys, and the exchange naming its own key. -/

theorem pin229 : ground.getAt 0 (ground.adjSwap 1 (List.range 4)) 2 = 1 := by
  decide +kernel

theorem pin230 : ground.getAt 0 (ground.adjSwap 1 (List.range 4)) 2
    = if 2 = 1 then 1 + 1 else if 2 = 1 + 1 then 1 else 2 :=
  ground.getAt_adjSwap_range 4 1 2 (by decide +kernel) (by decide +kernel)

theorem pin231 : (1 : Nat) = 1 :=
  ground.adjSwap_range_inj 4 1 1 (by decide +kernel) (by decide +kernel) rfl

/-- The naming's own read: two keys' exchanges of the key list
differ. -/
theorem pin232 : ¬ ground.adjSwap 0 (List.range 4)
    = ground.adjSwap 1 (List.range 4) := by decide +kernel

/-! The exchange's tie witness: the doubled place at the key, the
vacancy at its successor, the unit at every further place. -/

theorem pin233 : ground.getAt 0
    (List.replicate 1 1 ++ 2 :: 0 :: List.replicate 2 1) 2 = 0 := by
  decide +kernel

theorem pin234 : ground.getAt 0
      (List.replicate 1 1 ++ 2 :: 0 :: List.replicate 2 1) 2
    = if 2 = 1 then 2 else if 2 = 1 + 1 then 0 else 1 :=
  ground.getAt_swapWit 1 2 2 (by decide +kernel)

/-! The comparison counts at a stated value, the multiplicative
fold over a key list, and the prefix occupancy family, each at a
value with its refusal; the depth step's hypothesis isolated at a
depth outside the height. -/

theorem pin235 : ground.countAbove 1 [0, 2, 3, 1] = 2 := by decide +kernel
theorem pin236 : ¬ ground.countAbove 1 [0, 2, 3, 1] = 3 := by decide +kernel
theorem pin237 : ground.countBelow 2 [0, 2, 3, 1] = 2 := by decide +kernel
theorem pin238 : ¬ ground.countBelow 2 [0, 2, 3, 1] = 1 := by decide +kernel
theorem pin239 : ground.prodOver (fun x => x + 1) [1, 2, 3] = 24 := by decide +kernel
theorem pin240 : ¬ ground.prodOver (fun x => x + 1) [1, 2, 3] = 12 := by decide +kernel
theorem pin241 : ground.onesRows 2 3 = [1, 1, 0, 0, 0] := by decide +kernel
theorem pin242 : ¬ ground.onesRows 3 2 = [1, 1, 0, 0, 0] := by decide +kernel
theorem pin243 : ¬ ((1 : Nat) - (3 + 1) + 1 = 1 - 3) := by decide +kernel

/-! The keyed entry edit's value reads at the write and off it,
with the refusals isolating the self read's range binder, the
off-key read's distinctness binder, the exchange's distinct-keys
binder, the entry congruence's hypothesis, the total read's range
binder, and the sum distribution's entry read at each
summand. -/

theorem pin244 : ground.editAt (fun x => x * 2) 1 [5, 3, 4] = [5, 6, 4] := by decide +kernel

theorem pin245 : ground.editAt (fun x => x * 2) 3 [5, 3, 4] = [5, 3, 4] := by decide +kernel

theorem pin246 : ¬ (ground.getAt 0 (ground.editAt (fun x => x + 5) 3 [2]) 3
    = ground.getAt 0 [2] 3 + 5) := by decide +kernel

theorem pin247 : ¬ (ground.getAt 0 (ground.editAt (fun x => x + 1) 0 [7]) 0
    = ground.getAt 0 [7] 0) := by decide +kernel

theorem pin248 : ¬ (ground.editAt (fun x => x + 1) 0
      (ground.editAt (fun x => x - 1) 0 [0])
    = ground.editAt (fun x => x - 1) 0
      (ground.editAt (fun x => x + 1) 0 [0])) := by decide +kernel

theorem pin249 : ¬ (ground.editAt (fun x => x + 1) 0 [1]
    = ground.editAt (fun x => x) 0 [1]) := by decide +kernel

theorem pin250 : ¬ (ground.sumNat (ground.editAt (fun x => x + 5) 0 [])
      + ground.getAt 0 ([] : List Nat) 0
    = ground.sumNat [] + (ground.getAt 0 ([] : List Nat) 0 + 5)) := by decide +kernel

theorem pin251 : ¬ (List.zipWith (fun x y => x + y)
      (ground.editAt (fun x => x - 1) 0 [0]) [3]
    = ground.editAt (fun x => x - 1) 0
      (List.zipWith (fun x y => x + y) [0] [3])) := by decide +kernel

theorem pin252 : ¬ (List.zipWith (fun x y => x + y) [3]
      (ground.editAt (fun x => x - 1) 0 [0])
    = ground.editAt (fun x => x - 1) 0
      (List.zipWith (fun x y => x + y) [3] [0])) := by decide +kernel

/-! The reversal's zip kit: the componentwise walk of two
reversals is the walk's own reversal at matched lengths, the length
binder isolated at a ragged pair where the two reads differ; the
repeated family is its own reversal; and the sum's zip exchanges
its arguments at every pair, ragged pairs among them. -/

theorem pin253 : (List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]).reverse
    = [9, 7, 5] := by decide +kernel

theorem pin254 : (List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]).reverse
    = List.zipWith (fun u w => u + w) ([1, 2, 3] : List Nat).reverse
      ([4, 5, 6] : List Nat).reverse :=
  ground.reverse_zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6] rfl

theorem pin255 : ¬ ((List.zipWith (fun u w => u + w) [1, 2] [4, 5, 6]).reverse
    = List.zipWith (fun u w => u + w) ([1, 2] : List Nat).reverse
      ([4, 5, 6] : List Nat).reverse) := by decide +kernel

theorem pin256 : (List.replicate 3 (7 : Nat)).reverse = [7, 7, 7] := by decide +kernel

theorem pin257 : (List.replicate 3 (7 : Nat)).reverse = List.replicate 3 7 :=
  ground.reverse_replicate 3 7

theorem pin258 : List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]
    = [5, 7, 9] := by decide +kernel

theorem pin259 : List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]
    = List.zipWith (fun u w => u + w) [4, 5, 6] [1, 2, 3] :=
  ground.zipWith_add_comm [1, 2, 3] [4, 5, 6]

theorem pin260 : List.zipWith (fun u w => u + w) [1, 2] [4, 5, 6]
    = List.zipWith (fun u w => u + w) [4, 5, 6] [1, 2] :=
  ground.zipWith_add_comm [1, 2] [4, 5, 6]

/-! The gap fold against the total: at a dominating bound the
list's gaps and its own sum exhaust the bound once per place, the
domination binder isolated at a bound the head clears, where the
truncated gaps overshoot.  Beside it the family fold dominates each
of its members, the membership binder isolated at a value beyond
the fold. -/

theorem pin261 : [2, 1, 0].foldl (fun acc y => acc + (3 - y)) 0 + ground.sumNat [2, 1, 0]
    = ([2, 1, 0] : List Nat).length * 3 :=
  ground.gapFold_total 3 [2, 1, 0] (by decide +kernel)

theorem pin262 : ¬ ([2, 1, 0].foldl (fun acc y => acc + (1 - y)) 0
    + ground.sumNat [2, 1, 0] = ([2, 1, 0] : List Nat).length * 1) := by decide +kernel

theorem pin263 : (5 : Nat) ≤ ground.famFold Nat.add 0 (fun n => n) [4, 5, 6] :=
  ground.famFold_mem_le (fun n => n) [4, 5, 6] 5
    (List.Mem.tail 4 (List.Mem.head [6]))

theorem pin264 : ¬ ((20 : Nat) ≤ ground.famFold Nat.add 0 (fun n => n) [4, 5, 6]) := by decide +kernel

/-! The matrix at an entry formula: the builder's displayed rows,
its length, row, width and entry reads decided and routed through
their theorems, the congruence at formulas agreeing on the box,
and the refusals — an off-count row or entry reads the stated
default against the formula's value, and formulas differing inside
the box build distinct matrices. -/

theorem pin265 : ground.matOf 2 3 (fun i j => i + 2 * j)
    = [[0, 2, 4], [1, 3, 5]] := by decide +kernel
theorem pin266 : (ground.matOf 2 3 (fun i j => i + 2 * j)).length = 2 :=
  ground.matOf_length 2 3 _
theorem pin267 : ground.getAt [] (ground.matOf 2 3 (fun i j => i + 2 * j)) 1
    = [1, 3, 5] := by decide +kernel
theorem pin268 : ground.getAt [] (ground.matOf 2 3 (fun i j => i + 2 * j)) 1
    = (List.range 3).map (fun j => 1 + 2 * j) :=
  ground.matOf_row [] 2 3 _ 1 (by decide +kernel)
theorem pin269 : (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 1).length = 3 :=
  ground.matOf_rowLength [] 2 3 _ 1 (by decide +kernel)
theorem pin270 : ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 1) 2 = 5 := by
  decide +kernel
theorem pin271 : ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 1) 2 = 5 :=
  ground.matOf_entry [] 0 2 3 _ 1 2 (by decide +kernel)
    (by decide +kernel)
theorem pin272 : ground.matOf 2 2 (fun i j => i + j)
    = ground.matOf 2 2 (fun i j => if i < 2 then i + j else 7) :=
  ground.matOf_congr 2 2 _ _ (fun i j hi _ => by rw [if_pos hi])
theorem pin273 : ground.matOf 2 2 (fun i j => i + j)
    = ground.matOf 2 2 (fun i j => if j < 2 then i + j else 9) :=
  ground.matOf_congr 2 2 _ _ (fun i j _ hj => by rw [if_pos hj])

theorem pin274 : ¬ (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 2
      = (List.range 3).map (fun j => 2 + 2 * j)) := by decide +kernel
theorem pin275 : ¬ ((ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 2).length = 3) := by
  decide +kernel
theorem pin276 : ¬ (ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun _ _ => 7)) 1) 3 = 7) := by decide +kernel
theorem pin277 : ¬ (ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun _ _ => 7)) 2) 0 = 7) := by decide +kernel
theorem pin278 : ¬ (ground.matOf 2 2 (fun i j => i + j)
    = ground.matOf 2 2 (fun i j => i * j)) := by decide +kernel

/-! The box at stated per-key bounds: its count the bounds'
successor product, and a member's count one exactly at the matched
length with every key at or below its bound — decided at an inside
list, at a list past the head bound, and at the two vacant-bound
instances where the box is the seed alone. -/

theorem pin279 : (ground.boxAll [2, 1]).length
    = ground.prodOver (fun x => x + 1) [2, 1] := by decide +kernel
theorem pin280 : (ground.boxAll [2, 1]).length
    = ground.prodOver (fun x => x + 1) [2, 1] :=
  ground.boxAll_length [2, 1]

theorem pin281 : ground.countOf [1, 1] (ground.boxAll [2, 1])
    = if ([1, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [1, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 := by decide +kernel
theorem pin282 : ground.countOf [1, 1] (ground.boxAll [2, 1])
    = if ([1, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [1, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 :=
  ground.boxAll_countOf [2, 1] [1, 1]

theorem pin283 : ground.countOf [3, 1] (ground.boxAll [2, 1])
    = if ([3, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [3, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 := by decide +kernel
theorem pin284 : ground.countOf [3, 1] (ground.boxAll [2, 1])
    = if ([3, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [3, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 :=
  ground.boxAll_countOf [2, 1] [3, 1]

theorem pin285 : ground.boxAll [] = [[]] := by decide +kernel
theorem pin286 : (ground.boxAll ([] : List Nat)).length
    = ground.prodOver (fun x => x + 1) ([] : List Nat) :=
  ground.boxAll_length []
theorem pin287 : ground.boxAll [0] = [[0]] := by decide +kernel
theorem pin288 : (ground.boxAll [0]).length
    = ground.prodOver (fun x => x + 1) [0] :=
  ground.boxAll_length [0]
theorem pin289 : ground.countOf [1] (ground.boxAll [0])
    = if ([1] : List Nat).length = ([0] : List Nat).length
        ∧ (∀ i, i < ([0] : List Nat).length →
            ground.getAt 0 [1] i ≤ ground.getAt 0 [0] i)
      then 1 else 0 := by decide +kernel

/-! `thm:groundreads`(v)'s cleared displays: the split's square
identity at `2 + 3 = 5` reading `3·7 + 4 = 25`, and the Bernoulli
display's two sides at `1 + 2 = 3` and the count three — the upper
`27 ≤ 8 + 27` at the datum's own prior power, the lower
`8 + 12 ≤ 27` at the gap's — each decided and landed by the theorem
route. -/

theorem pin290 : (3 : Pos) * ((5 : Pos) + 2) + 2 * 2 = 5 * 5 := by
  decide +kernel

theorem pin291 : (3 : Pos) * ((5 : Pos) + 2) + 2 * 2 = 5 * 5 :=
  Pos.sq_split 2 3 5 (by decide +kernel)

theorem pin292 : Pos.pow (3 : Pos) 3
    ≤ Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (3 : Pos) 2 := by
  decide +kernel

theorem pin293 : Pos.pow (3 : Pos) 3
    ≤ Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (3 : Pos) 2 :=
  Pos.bernoulli_le 1 2 3 (by decide +kernel) 2

theorem pin294 : Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (2 : Pos) 2
    ≤ Pos.pow (3 : Pos) 3 := by
  decide +kernel

theorem pin295 : Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (2 : Pos) 2
    ≤ Pos.pow (3 : Pos) 3 :=
  Pos.bernoulli_ge 1 2 3 (by decide +kernel) 2

/-- The Bernoulli display's two sides carry their own directions: the
lower side's display read upward refuses at the same data, the
datum's power `27` above the gap's power joined to the count's
multiple, `8 + 12 = 20`. -/
theorem pin296 : ¬ (Pos.pow (3 : Pos) 3
    ≤ Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (2 : Pos) 2) := by
  decide +kernel

/-! The written key's read: a write keeps the family's length, the
written key reads the written value, and every further key is
kept — decided at an in-range write and at a key beyond the
family, each landed by the theorem route. -/

theorem pin297 : (([5, 6, 7] : List Nat).set 1 9).length
    = ([5, 6, 7] : List Nat).length := by decide +kernel

theorem pin298 : (([5, 6, 7] : List Nat).set 4 9).length
    = ([5, 6, 7] : List Nat).length := by decide +kernel

theorem pin299 : (([5, 6, 7] : List Nat).set 4 9).length
    = ([5, 6, 7] : List Nat).length := length_set 9 [5, 6, 7] 4

theorem pin300 : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 1 = 9 := by
  decide +kernel

theorem pin301 : getAt 0 (([5, 6, 7] : List Nat).set 0 9) 0 = 9 := by
  decide +kernel

theorem pin302 : getAt 0 (([5, 6, 7] : List Nat).set 2 9) 2 = 9 :=
  getAt_set_self 0 9 [5, 6, 7] 2 (by decide +kernel)

/-- The write's key binder is load-bearing: at a key beyond the
family the write is a no-op and the key reads the vacant
default. -/
theorem pin303 : ¬ (getAt 0 (([5, 6, 7] : List Nat).set 4 9) 4 = 9) := by
  decide +kernel

theorem pin304 : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 2 = 7 := by
  decide +kernel

theorem pin305 : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 5 = 0 := by
  decide +kernel

theorem pin306 : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 0
    = getAt 0 ([5, 6, 7] : List Nat) 0 :=
  getAt_set_ne 0 [5, 6, 7] 1 0 9 (by decide +kernel)

/-! The two cleared displays' join binders refused: at the parted
join each display parts. -/

theorem pin307 : ¬ ((1 : Pos) + 1 = 5) := by decide +kernel
theorem pin308 : ¬ ((1 : Pos) * ((5 : Pos) + 1) + 1 * 1 = 5 * 5) := by
  decide +kernel
theorem pin309 : ¬ (Pos.pow (5 : Pos) 3
    ≤ Pos.pow (1 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (5 : Pos) 2) := by
  decide +kernel

/-! The Pascal count and the binomial theorem at the pair carrier. -/

theorem pin310 : pasc 4 2 = 6 := by decide +kernel
theorem pin311 : pasc 6 3 = 20 := by decide +kernel

theorem pin312 : pasc 5 0 = 1 := by decide +kernel
theorem pin313 : pasc 5 5 = 1 := by decide +kernel
theorem pin314 : pasc 3 5 = 0 := by decide +kernel

theorem pin315 : pasc 7 7 = 1 := by decide +kernel
theorem pin316 : pasc 7 7 = 1 := pasc_self 7

theorem pin317 : pasc 2 9 = 0 := by decide +kernel
theorem pin318 : pasc 2 9 = 0 := pasc_beyond 2 9 (by decide +kernel)

theorem pin319 : (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (bsum (fun t => BPair.ofNat (pasc 3 t)
      * (bpow (BPair.ofNat 2) t * bpow (BPair.ofNat 3) (3 - t)))
      (List.range 4)) := by decide +kernel

theorem pin320 : (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (bsum (fun t => BPair.ofNat (pasc 3 t)
      * (bpow (BPair.ofNat 2) t * bpow (BPair.ofNat 3) (3 - t)))
      (List.range 4)) :=
  bpow_binom (BPair.ofNat 2) (BPair.ofNat 3) 3

theorem pin321 : (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (BPair.ofNat 125) := by decide +kernel

/-! The partner-signed instance: the second member enters memberwise
swapped and the square reads the two members' gap against itself. -/

theorem pin322 : (bpow (BPair.ofNat 2 + (BPair.ofNat 3).swap) 2).oneValue
    (bsum (fun t => BPair.ofNat (pasc 2 t)
      * (bpow (BPair.ofNat 2) t * bpow ((BPair.ofNat 3).swap) (2 - t)))
      (List.range 3)) := by decide +kernel

theorem pin323 : (bpow (BPair.ofNat 2 + (BPair.ofNat 3).swap) 2).oneValue
    (bsum (fun t => BPair.ofNat (pasc 2 t)
      * (bpow (BPair.ofNat 2) t * bpow ((BPair.ofNat 3).swap) (2 - t)))
      (List.range 3)) :=
  bpow_binom (BPair.ofNat 2) ((BPair.ofNat 3).swap) 2

theorem pin324 : (bpow (BPair.ofNat 2 + (BPair.ofNat 3).swap) 2).oneValue
    (BPair.ofNat 1) := by decide +kernel

/-- The second power's key binder is load-bearing: read at the first
member's own key the fold sums to 343 against the power's 125. -/
theorem pin325 : ¬ (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (bsum (fun t => BPair.ofNat (pasc 3 t)
      * (bpow (BPair.ofNat 2) t * bpow (BPair.ofNat 3) t))
      (List.range 4)) := by decide +kernel

/-! ## The monomial engine

A natural product identity read at the monomial carrier: the two
sides' coefficients and exponent lists decided equal at the
variable list `[en, ed, r + 1]`, the identity's route through
`monEq`, and the two data load-bearing at parted exponents and at a
parted coefficient. -/

theorem pin326 (en ed r : Nat) :
    4 * (en * en) * 80 * 630 * (11 * (r + 1) * ed)
      = 6930 * (en * ed * (r + 1) * 16) * (20 * en) :=
  monEq [en, ed, r + 1]
    (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4)
        (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.cst 80)) (Mon.cst 630))
      (Mon.mul (Mon.mul (Mon.cst 11) (Mon.var 2)) (Mon.var 1)))
    (Mon.mul (Mon.mul (Mon.cst 6930)
        (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))
          (Mon.cst 16)))
      (Mon.mul (Mon.cst 20) (Mon.var 0)))
    (by decide +kernel) (by decide +kernel)

theorem pin327 : (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.var 0)))
    (Mon.var 1)).exps = [2, 1] := by decide +kernel
theorem pin328 : (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.var 0)))
    (Mon.var 1)).coef = 4 := by decide +kernel
theorem pin329 : (Mon.mul (Mon.cst 2) (Mon.var 0)).val [7] = 14 := by decide +kernel

/-- The exponent lists are load-bearing: `2·x` against `x·x` share the
coefficient and part at the exponents. -/
theorem pin330 : ¬ ((Mon.mul (Mon.cst 2) (Mon.var 0)).exps
    = (Mon.mul (Mon.var 0) (Mon.var 0)).exps) := by decide +kernel
/-- The coefficients are load-bearing: `2·x` against `3·x` share the
exponents and part at the coefficient. -/
theorem pin331 : ¬ ((Mon.mul (Mon.cst 2) (Mon.var 0)).coef
    = (Mon.mul (Mon.cst 3) (Mon.var 0)).coef) := by decide +kernel

/-! The keyed store's memo read: a read stored over a key list reads
back at a stored key and at a key off the store alike, decided and
by its theorem, and a store holding a further value at a key reads
that value, the store's contents the theorem's binder. -/

theorem pin332 : keyAt (fun a b => a == b) (3 * 3) 3 ([1, 2, 3].map (fun s => (s, s * s))) = 9
    ∧ keyAt (fun a b => a == b) (5 * 5) 5 ([1, 2, 3].map (fun s => (s, s * s))) = 25
    ∧ keyAt (fun a b => a == b) (3 * 3) 3 [(3, 7)] = 7 := by decide
theorem pin333 : keyAt (fun a b => a == b) (3 * 3) 3 ([1, 2, 3].map (fun s => (s, s * s))) = 3 * 3 :=
  keyAt_memo (fun a b => a == b) (fun _ _ h => beqEqOf h) (fun s => s * s) 3 [1, 2, 3]
theorem pin334 : keyAt (fun a b => a == b) (3 * 3) 3 [(1, 1), (3, 9)] = 3 * 3 :=
  keyAt_store (fun a b => a == b) (fun _ _ h => beqEqOf h) (fun s => s * s) 3
    [(1, 1), (3, 9)] (fun e he => by
      cases he with
      | head => rfl
      | tail _ h2 =>
        cases h2 with
        | head => rfl
        | tail _ h3 => exact nomatch h3)

/-! `def:ground`'s completing of the square at `δ = 5`, `u = 2`,
`v = 7`: the left member reads `25 + 7 - 20 = 12` and the right
`(5 - 2)^2 + (7 - 4) = 12`, the theorem route beside the kernel. -/
theorem pin335 : BPair.oneValue (BPair.ofNat 5 * BPair.ofNat 5 + BPair.ofNat 7
    + (BPair.ofNat 2 * BPair.ofNat 5 + BPair.ofNat 2 * BPair.ofNat 5).swap)
    (BPair.ofNat 12) := by decide +kernel
theorem pin336 : ((BPair.ofNat 5 + (BPair.ofNat 2).swap) * (BPair.ofNat 5 + (BPair.ofNat 2).swap)
    + (BPair.ofNat 7 + (BPair.ofNat 2 * BPair.ofNat 2).swap)).oneValue
    (BPair.ofNat 12) := by decide +kernel
theorem pin337 : (BPair.ofNat 5 * BPair.ofNat 5 + BPair.ofNat 7
      + (BPair.ofNat 2 * BPair.ofNat 5 + BPair.ofNat 2 * BPair.ofNat 5).swap).oneValue
    ((BPair.ofNat 5 + (BPair.ofNat 2).swap) * (BPair.ofNat 5 + (BPair.ofNat 2).swap)
      + (BPair.ofNat 7 + (BPair.ofNat 2 * BPair.ofNat 2).swap)) :=
  complete_sq (BPair.ofNat 5) (BPair.ofNat 2) (BPair.ofNat 7)

/-! The keyed families' folds at a key through the sort kit: the
collected family's fold at every key the family's own, two families
one value at the walk one value at every key's fold, decided at a
family with a repeated key against its collected form and through
the theorem, refused at a family parting at one key, and a family
one value with itself. -/

private def kfA : List (Nat × BPair) :=
  [(2, BPair.ofNat 3), (1, (BPair.ofNat 2).swap), (2, BPair.ofNat 4)]
private def kfB : List (Nat × BPair) :=
  [(1, (BPair.ofNat 2).swap), (2, BPair.ofNat 7)]
private def kfC : List (Nat × BPair) :=
  [(1, (BPair.ofNat 2).swap), (2, BPair.ofNat 6)]

theorem pin338 : oneValueBy (fun x y => x < y) (fun x y => x == y) kfA kfB = true
    ∧ (keyFoldB (fun x y => x == y) 2 kfA).oneValue (BPair.ofNat 7)
    ∧ (keyFoldB (fun x y => x == y) 2 (collectBy (fun x y => x < y)
        (fun x y => x == y) kfA)).oneValue (keyFoldB (fun x y => x == y) 2 kfA)
    ∧ (keyFoldB (fun x y => x == y) 2 kfA).oneValue
        (keyFoldB (fun x y => x == y) 2 kfB)
    ∧ oneValueBy (fun x y => x < y) (fun x y => x == y) kfA kfC = false
    ∧ ¬ (keyFoldB (fun x y => x == y) 2 kfA).oneValue
        (keyFoldB (fun x y => x == y) 2 kfC)
    ∧ oneValueBy (fun x y => x < y) (fun x y => x == y) kfA kfA = true := by
  decide +kernel
theorem pin339 : (keyFoldB (fun x y => x == y) 2 kfA).oneValue
    (keyFoldB (fun x y => x == y) 2 kfB) :=
  keyFoldB_oneValueBy (fun x y => x < y) (fun x y => x == y)
    (fun _ _ h => beqEqOf h) kfA kfB (by decide +kernel) 2
theorem pin340 : oneValueBy (fun x y => x < y) (fun x y => x == y) kfA kfA = true :=
  oneValueBy_refl (fun x y => x < y) (fun x y => x == y) (fun _ => eqBeqOf rfl) kfA

/-! The reads' binders refused: at a key test passing at adjacency
two families read one value at the walk while their folds at a key
part, the merge at a join reading the unit parts from the sum, the
walk against itself refuses at a fuel below its count at an
occupied last member and at a key test refusing every key, and the
replaced store's read at a further key parts at the adjacency
test. -/

private def eqAdj (a b : Nat) : Bool := a ≤ b + 1 && b ≤ a + 1
private def kfD : List (Nat × BPair) := [(2, BPair.ofNat 5), (1, BPair.ofNat 2)]
private def kfE : List (Nat × BPair) := [(2, BPair.ofNat 7)]

theorem pin341 : eqAdj 1 2 = true
    ∧ oneValueBy (fun x y => x < y) eqAdj kfD kfE = true
    ∧ ¬ (keyFoldB eqAdj 3 kfD).oneValue (keyFoldB eqAdj 3 kfE)
    ∧ ¬ (keyFoldB (fun x y : Nat => x == y) 2 (mergeJoin (fun x y : Nat => x < y)
        (fun x y => x == y) (fun _ _ => BPair.unit) 2
        [(2, BPair.ofNat 5)] [(2, BPair.ofNat 2)])).oneValue
        (keyFoldB (fun x y : Nat => x == y) 2 [(2, BPair.ofNat 5)]
          + keyFoldB (fun x y : Nat => x == y) 2 [(2, BPair.ofNat 2)])
    ∧ mergeEqBy (fun x y : Nat => x < y) (fun x y => x == y)
        (fun c : BPair => decide (c.oneValue BPair.unit))
        (fun x y => decide (x.oneValue y)) 1
        [(1, BPair.ofNat 3), (2, BPair.ofNat 4)]
        [(1, BPair.ofNat 3), (2, BPair.ofNat 4)] = false
    ∧ mergeEqBy (fun x y : Nat => x < y) (fun x y => x == y)
        (fun c : BPair => decide (c.oneValue BPair.unit))
        (fun x y => decide (x.oneValue y)) 2
        [(1, BPair.ofNat 3), (2, BPair.ofNat 4)]
        [(1, BPair.ofNat 3), (2, BPair.ofNat 4)] = true
    ∧ oneValueBy (fun x y : Nat => x < y) (fun _ _ => false)
        [(1, BPair.ofNat 3)] [(1, BPair.ofNat 3)] = false
    ∧ keyAt eqAdj 0 0 (keyPut eqAdj 2 7 [(1, 5)])
        ≠ cond (eqAdj 2 0) 7 (keyAt eqAdj 0 0 [(1, 5)]) := by decide +kernel

/-! The keyed walkers (`mergeWith`) at their three instances: the
join at a shared key with the further keys kept, the run product at
the shared keys alone, and the one-value read with the stated unit
off the shared keys, refused at an occupied key one list alone
holds; the keys' order read strict and reflexive at a repeated key;
the runs gathered in place at keys in order and sorted into runs
otherwise; and the collection at a cancelling pair read to the
canonical representative on both of its paths, the sorted join and
the in-order skip. -/

theorem pin342 : mergeJoin (fun x y => x < y) (fun x y => x == y) Nat.add 4
    [(1, 10), (3, 30)] [(2, 20), (3, 3)] = [(1, 10), (2, 20), (3, 33)] := by decide +kernel
theorem pin343 : mergeCross (fun x y => x < y) (fun x y => x == y) Prod.mk 4
    [(1, [10, 11]), (2, [12])] [(1, [20, 21]), (3, [22])]
    = [(10, 20), (10, 21), (11, 20), (11, 21)] := by decide +kernel
theorem pin344 : mergeEqBy (fun x y => x < y) (fun x y => x == y) (fun v => v == 0)
    (fun v w => v == w) 4 [(1, 5), (2, 0)] [(1, 5), (3, 0)] = true := by decide +kernel
theorem pin345 : mergeEqBy (fun x y => x < y) (fun x y => x == y) (fun v => v == 0)
    (fun v w => v == w) 3 [(1, 5), (2, 4)] [(1, 5)] = false := by decide +kernel
theorem pin346 : keysInOrder (fun x y => x < y) [(1, 0), (2, 0), (2, 0)] = false
    ∧ keysInOrder (fun x y => x ≤ y) [(1, 0), (2, 0), (2, 0)] = true := by decide +kernel
theorem pin347 : groupRuns (fun x y => x == y) [(2, 1), (2, 2), (5, 3)] = [(2, [1, 2]), (5, [3])]
    ∧ sortRuns (fun x y => x < y) (fun x y => x == y) [(2, 1), (2, 2), (5, 3)]
      = [(2, [1, 2]), (5, [3])]
    ∧ sortRuns (fun x y => x < y) (fun x y => x == y) [(5, 3), (2, 1), (2, 2)]
      = [(2, [2, 1]), (5, [3])] := by decide +kernel
theorem pin348 : collectBy (fun x y => x < y) (fun x y => x == y)
    [(3, BPair.ofNat 1), (1, BPair.ofNat 2), (3, (BPair.ofNat 1).swap),
     (2, BPair.ofNat 3 + (BPair.ofNat 3).swap)] = [(1, BPair.ofNat 2)] := by decide +kernel
theorem pin349 : collectBy (fun x y => x < y) (fun x y => x == y)
    [(1, BPair.ofNat 2 + BPair.ofNat 2 + (BPair.ofNat 2).swap),
     (2, BPair.ofNat 3 + (BPair.ofNat 3).swap)] = [(1, BPair.ofNat 2)] := by decide +kernel

/-! The sorted walk's pairing (`mergeDot`): two sorted families'
walk reads the coordinate fold at the shared keys, decided and
through the theorem, and refused at a first list off the order, at
a second list off the order, and at a fuel below the walk's steps;
a head below a key folds away at the key and a head at the key
enters the fold (`keyFoldB_cons_off`); and the family read at
canonical representatives with the unit members withdrawn keeps
every key's fold with its members canonical and off the unit
(`keyFoldB_normFilter`, `mem_normFilter`). -/

private def kdU : List (List Nat × BPair) :=
  [([1], BPair.ofNat 2), ([3], BPair.ofNat 5), ([4], (BPair.ofNat 1).swap)]
private def kdV : List (List Nat × BPair) :=
  [([2], BPair.ofNat 7), ([3], BPair.ofNat 2), ([4], BPair.ofNat 3)]
private def kdFold (u v : List (List Nat × BPair)) : BPair :=
  famFold BPair.add BPair.unit (fun p => p.2 * keyFoldB (fun a b : List Nat => a == b) p.1 v) u
private def kdN : List (List Nat × BPair) :=
  [([1], BPair.ofNat 3 + (BPair.ofNat 3).swap), ([2], ⟨5, 2⟩)]

theorem pin384 : (mergeDot lexLt (fun a b => a == b) 6 kdU kdV).oneValue (kdFold kdU kdV)
    ∧ (mergeDot lexLt (fun a b => a == b) 6 kdU kdV).oneValue (BPair.ofNat 7)
    ∧ ¬ (mergeDot lexLt (fun a b => a == b) 6 kdU.reverse kdV).oneValue
        (kdFold kdU.reverse kdV)
    ∧ ¬ (mergeDot lexLt (fun a b => a == b) 6 kdU kdV.reverse).oneValue
        (kdFold kdU kdV.reverse)
    ∧ ¬ (mergeDot lexLt (fun a b => a == b) 3 kdU kdV).oneValue (kdFold kdU kdV)
    ∧ (keyFoldB (fun a b : List Nat => a == b) [3] (([2], BPair.ofNat 4) :: kdV)).oneValue
        (keyFoldB (fun a b : List Nat => a == b) [3] kdV)
    ∧ ¬ (keyFoldB (fun a b : List Nat => a == b) [3] (([3], BPair.ofNat 4) :: kdV)).oneValue
        (keyFoldB (fun a b : List Nat => a == b) [3] kdV)
    ∧ (kdN.map (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep)
      = [([2], BPair.ofNat 3)]
    ∧ (keyFoldB (fun a b : List Nat => a == b) [1]
        ((kdN.map (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep))).oneValue
        (keyFoldB (fun a b : List Nat => a == b) [1] kdN)
    ∧ (keyFoldB (fun a b : List Nat => a == b) [2]
        ((kdN.map (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep))).oneValue
        (keyFoldB (fun a b : List Nat => a == b) [2] kdN) := by decide +kernel
theorem pin385 : (mergeDot lexLt (fun a b => a == b) 6 kdU kdV).oneValue (kdFold kdU kdV) :=
  mergeDot_read lexLt (fun a b => a == b) lexLt_trans (fun _ _ h => listBeqEq h)
    lexLt_irrefl 6 kdU kdV (by decide) (by decide) (by decide)
theorem pin386 : (keyFoldB (fun a b : List Nat => a == b) [3] (([2], BPair.ofNat 4) :: kdV)).oneValue
    (keyFoldB (fun a b : List Nat => a == b) [3] kdV) :=
  keyFoldB_cons_off lexLt (fun a b => a == b) (fun _ _ h => listBeqEq h) lexLt_irrefl
    [3] ([2], BPair.ofNat 4) kdV (by decide)
theorem pin387 : (keyFoldB (fun a b : List Nat => a == b) [2]
    ((kdN.map (fun p => (p.1, p.2.norm))).filter (fun p => !p.2.isUnitRep))).oneValue
    (keyFoldB (fun a b : List Nat => a == b) [2] kdN) :=
  keyFoldB_normFilter (fun a b : List Nat => a == b) [2] kdN
theorem pin388 : (([2], BPair.ofNat 3) : List Nat × BPair).2.norm = (BPair.ofNat 3)
    ∧ (BPair.ofNat 3).isUnitRep = false :=
  mem_normFilter kdN ([2], BPair.ofNat 3) (mem_of_countOf_pos _ _ (by decide +kernel))

/-! The walk's three order reads isolated: a key test off the
equality (the walk zips where the fold multiplies the sums), an
order off the transitivity (the cyclic order, both lists in order at
it, the walk missing a shared key), and an order off the
irreflexivity (the reflexive order at a repeated key); and a repeated
key on either side refused at the order read with the walk dropping a
member. -/

private def mdFold (eq : Nat → Nat → Bool) (u v : List (Nat × BPair)) : BPair :=
  famFold BPair.add BPair.unit (fun p => p.2 * keyFoldB eq p.1 v) u
private def mdLt (a b : Nat) : Bool := a < b
private def mdEqT (_ _ : Nat) : Bool := true
private def mdEq (a b : Nat) : Bool := a == b
private def mdCyc (a b : Nat) : Bool := b == (a + 1) % 3
private def mdLe (a b : Nat) : Bool := a ≤ b
private def mdNt (a b : Nat) : Bool := a + 1 == b
private def mdU1 : List (Nat × BPair) := [(1, BPair.ofNat 1), (2, BPair.ofNat 1)]
private def mdU2 : List (Nat × BPair) :=
  [(0, BPair.ofNat 1), (1, BPair.ofNat 1), (2, BPair.ofNat 1)]
private def mdV2 : List (Nat × BPair) := [(2, BPair.ofNat 1), (0, BPair.ofNat 1)]
private def mdU3 : List (Nat × BPair) := [(1, BPair.ofNat 1), (1, BPair.ofNat 2)]
private def mdV3 : List (Nat × BPair) := [(1, BPair.ofNat 1)]

theorem pin389 : keysInOrder mdLt mdU1 = true
    ∧ (mergeDot mdLt mdEqT 4 mdU1 mdU1).oneValue (BPair.ofNat 2)
    ∧ (mdFold mdEqT mdU1 mdU1).oneValue (BPair.ofNat 4)
    ∧ ¬ (mergeDot mdLt mdEqT 4 mdU1 mdU1).oneValue (mdFold mdEqT mdU1 mdU1)
    ∧ keysInOrder mdCyc mdU2 = true ∧ keysInOrder mdCyc mdV2 = true
    ∧ (mergeDot mdCyc mdEq 5 mdU2 mdV2).oneValue (BPair.ofNat 1)
    ∧ (mdFold mdEq mdU2 mdV2).oneValue (BPair.ofNat 2)
    ∧ ¬ (mergeDot mdCyc mdEq 5 mdU2 mdV2).oneValue (mdFold mdEq mdU2 mdV2)
    ∧ keysInOrder mdLe mdU3 = true ∧ keysInOrder mdLe mdV3 = true
    ∧ ¬ (mergeDot mdLe mdEq 3 mdU3 mdV3).oneValue (mdFold mdEq mdU3 mdV3)
    ∧ keysInOrder mdLt mdU3 = false
    ∧ (mergeDot mdLt mdEq 3 mdU3 mdV3).oneValue (BPair.ofNat 1)
    ∧ (mdFold mdEq mdU3 mdV3).oneValue (BPair.ofNat 3)
    ∧ (mergeDot mdLt mdEq 3 mdV3 mdU3).oneValue (BPair.ofNat 1)
    ∧ (mdFold mdEq mdV3 mdU3).oneValue (BPair.ofNat 3) := by decide +kernel

/-! The segment move: the moved members last in their order at the
key reads, the exchanges' count, and the iterated balance partner. -/

theorem pin390 : moveK 1 2 2 [0, 1, 2, 3, 4] = [0, 3, 4, 1, 2]
    ∧ moveOne 1 2 [0, 1, 2, 3] = [0, 2, 3, 1]
    ∧ moveK 0 0 3 [5, 6, 7] = [5, 6, 7] ∧ moveK 2 1 0 [5, 6, 7] = [5, 6, 7]
    ∧ moveCount 2 2 = 6 ∧ moveCount 1 3 = 3 ∧ moveCount 0 4 = 0
    ∧ (List.range 5).map (mvIx 1 2 2) = [0, 3, 4, 1, 2]
    ∧ mvIx 1 2 2 7 = 7
    ∧ BPair.swapN 2 (BPair.ofNat 3) = BPair.ofNat 3
    ∧ BPair.swapN 3 (BPair.ofNat 3) = (BPair.ofNat 3).swap := by decide +kernel
theorem pin391 : getAt 0 (moveK 1 2 2 [0, 1, 2, 3, 4]) 3 = getAt 0 [0, 1, 2, 3, 4] (mvIx 1 2 2 3) :=
  getAt_moveK 0 1 2 2 [0, 1, 2, 3, 4] 3 (by decide) (by decide)

/-! The telescope, Bernoulli and Bernstein reads at the pair `2` with its
partner `-1` summing to one (`lem:cornerkey`'s positive reads): the
telescope at three keys, the Bernoulli display at four, and the
Bernstein partition's read at the key one of three, each decided and
through its theorem; and the power's gap read at the pair `2` at the
keys two and one, `4 + (3 + 2) ≡ 1 + 8`, decided and through its
theorem. -/
theorem pin350 : (bpow (BPair.ofNat 1).swap 3
    + BPair.ofNat 2 * bsum (bpow (BPair.ofNat 1).swap) (List.range 3)).oneValue
      (BPair.ofPos .one) := by decide +kernel
theorem pin351 : (bpow (BPair.ofNat 1).swap 3
    + BPair.ofNat 2 * bsum (bpow (BPair.ofNat 1).swap) (List.range 3)).oneValue
      (BPair.ofPos .one) :=
  bpow_telescope (BPair.ofNat 2) (BPair.ofNat 1).swap (by decide +kernel) 3
theorem pin352 : (bpow (BPair.ofNat 1).swap 4 + BPair.ofNat 4 * BPair.ofNat 2).oneValue
    (BPair.ofPos .one + BPair.ofNat 2 * BPair.ofNat 2
      * bsum (fun i => bsum (bpow (BPair.ofNat 1).swap) (List.range i)) (List.range 4)) := by
  decide +kernel
theorem pin353 : (bpow (BPair.ofNat 1).swap 4 + BPair.ofNat 4 * BPair.ofNat 2).oneValue
    (BPair.ofPos .one + BPair.ofNat 2 * BPair.ofNat 2
      * bsum (fun i => bsum (bpow (BPair.ofNat 1).swap) (List.range i)) (List.range 4)) :=
  bpow_bernoulli (BPair.ofNat 2) (BPair.ofNat 1).swap (by decide +kernel) 4
theorem pin354 : (BPair.ofNat (pasc 3 1) * (bpow (BPair.ofNat 2) 1 * bpow (BPair.ofNat 1).swap 3)
    + bsum (fun t => if t = 1
        then BPair.ofNat (pasc 3 1) * (bpow (BPair.ofNat 2) 1 * bpow (BPair.ofNat 1).swap 2)
          * (BPair.ofNat 2 * bsum (bpow (BPair.ofNat 1).swap) (List.range 1))
        else BPair.ofNat (pasc 3 t) * (bpow (BPair.ofNat 2) t * bpow (BPair.ofNat 1).swap (3 - t)))
      (List.range 4)).oneValue (BPair.ofPos .one) :=
  bernstein_bound (BPair.ofNat 2) (BPair.ofNat 1).swap (by decide +kernel) 1 2
theorem pin355 : (bpow (BPair.ofNat 2) 2
    + ((BPair.ofPos .one + (BPair.ofNat 2).swap) * (BPair.ofPos .one + (BPair.ofNat 2).swap)
        * bsum (bpow (BPair.ofNat 2)) (List.range 2) * bsum (bpow (BPair.ofNat 2)) (List.range 1)
      + bpow (BPair.ofNat 2) 1)).oneValue (BPair.ofPos .one + bpow (BPair.ofNat 2) 3) := by
  decide +kernel
theorem pin356 : (bpow (BPair.ofNat 2) 2
    + ((BPair.ofPos .one + (BPair.ofNat 2).swap) * (BPair.ofPos .one + (BPair.ofNat 2).swap)
        * bsum (bpow (BPair.ofNat 2)) (List.range 2) * bsum (bpow (BPair.ofNat 2)) (List.range 1)
      + bpow (BPair.ofNat 2) 1)).oneValue (BPair.ofPos .one + bpow (BPair.ofNat 2) 3) :=
  bpow_gap_read (BPair.ofNat 2) 2 1

/-! The chain and near-scale reads (`lem:cornerkey`'s near mass and near
scale): the ascending quotients, the chain power at the unit clearing,
the binomial member and the power's join at constant and small data
through their theorems; the chain gap at the constant list at the unit
clearing and tolerance, at the list seeded at two at the clearing two
and the tolerance `[4 : 2]`, its seed binder isolated at the unit
clearing, and the conclusion parting at the vacant tolerance; the near
scale read at `A = 4, B = 1, C = 4, z = [2 : 1]` and at
`A = 2, B = 1, C = 1, z = [2 : 2]`, and its cap binder isolated at
`C = 6, A = 5`. -/
private def cOne : Nat → BPair := fun _ => BPair.ofNat 1
private def cTwo : Nat → BPair := fun i => if i = 0 then BPair.ofNat 2 else BPair.ofNat 1
theorem pin357 : ∀ i, i + 1 < 3 → cOne (i + 1) * cOne 2 ≤ cOne i * cOne 3 :=
  quotients_ascend cOne 3 (by decide +kernel) (by decide +kernel)
theorem pin358 : bpow (cOne 1) 2 ≤ BPair.ofNat 1 * bpow (cOne 2) 1 :=
  chain_power cOne 1 (BPair.ofNat 1) (by decide +kernel) (by decide +kernel)
    (fun _ _ => leB_refl _)
theorem pin359 : BPair.ofNat (pasc 2 1) * (bpow (BPair.ofNat 1) 1 * bpow (BPair.ofNat 2) 1)
    ≤ bpow (BPair.ofNat 1 + BPair.ofNat 2) 2 :=
  binom_member _ _ 1 1 (by decide +kernel) (by decide +kernel)
theorem pin360 : bpow (BPair.ofNat 2) 1 ≤ BPair.ofPos .one + bpow (BPair.ofNat 2) 2 :=
  bpow_le_one_add _ 1 1 (by decide +kernel)
theorem pin361 : BPair.ofNat 1 * cOne 0 ≤ BPair.ofNat 1 * cOne 0 + BPair.ofNat 1 * cOne 1 :=
  chain_gap cOne 0 0 (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ h => nomatch h)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin399 : BPair.ofNat 2 * cTwo 0 ≤ BPair.ofNat 4 * cTwo 0 + BPair.ofNat 2 * cTwo 1 :=
  chain_gap cTwo 0 0 (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 4) (BPair.ofNat 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun _ h => nomatch h)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin362 : ¬ (cTwo 0 ≤ BPair.ofNat 1) := by decide +kernel
theorem pin363 : ¬ (BPair.ofNat 1 * cTwo 0 ≤ BPair.unit * cTwo 0 + BPair.ofNat 1 * cTwo 1) := by
  decide +kernel
theorem pin364 : BPair.ofNat 4 * bpow (BPair.ofNat 1) 1
    ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 2) 1 * BPair.ofNat 1) :=
  near_scale_read (BPair.ofNat 4) (BPair.ofNat 1) (BPair.ofNat 4) (BPair.ofNat 2) (BPair.ofNat 1)
    1 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin400 : BPair.ofNat 2 * bpow (BPair.ofNat 2) 1
    ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 2) 1 * BPair.ofNat 1) :=
  near_scale_read (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 2)
    1 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin365 : ¬ (BPair.ofNat 6 ≤ bpow (BPair.ofNat 2) 2 * BPair.ofNat 1) := by decide +kernel
theorem pin366 : ¬ (BPair.ofNat 5 ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 2) 1 * BPair.ofNat 1)) := by
  decide +kernel

/-! The halving search (`bisectFrom`) against the walk (`firstAt`) at a
read stepping up the keys: the square's threshold at the budget twenty
and at the budget `10²⁰`, the least key read by the halving in
sixty-six steps where the walk runs a million, each decided and one
key with the walk through `bisectFrom_eq_firstAt`; the stepping binder
isolated at a read holding at one and refusing at two, the two
searches parting; a read refusing throughout, both searches at the
budget's end through the theorem; and the segment search's three
binders (`bisect_read`) isolated in turn, the budget below the
segment's length, the foot holding, and the top refusing, each
answer parting from a held key whose predecessor refuses. -/
private def sqTen (k : Nat) : Prop := 10 ≤ k * k
private instance instGroundChk1 : DecidablePred sqTen := fun _ => inferInstanceAs (Decidable (_ ≤ _))
private theorem sqTen_step (k : Nat) (h : sqTen k) : sqTen (k + 1) :=
  Nat.le_trans h (Nat.mul_le_mul (Nat.le_succ k) (Nat.le_succ k))
theorem pin367 : bisectFrom sqTen 0 20 = 4 := by decide +kernel
theorem pin368 : bisectFrom sqTen 0 20 = firstAt sqTen 0 20 :=
  bisectFrom_eq_firstAt sqTen sqTen_step 0 20
private def sqBig (k : Nat) : Prop := 1000000000000 ≤ k * k
private instance instGroundChk2 : DecidablePred sqBig := fun _ => inferInstanceAs (Decidable (_ ≤ _))
private theorem sqBig_step (k : Nat) (h : sqBig k) : sqBig (k + 1) :=
  Nat.le_trans h (Nat.mul_le_mul (Nat.le_succ k) (Nat.le_succ k))
theorem pin369 : bisectFrom sqBig 0 (10 ^ 20) = 1000000 := by decide +kernel
theorem pin370 : firstAt sqBig 0 (10 ^ 20) = 1000000 := by
  rw [← bisectFrom_eq_firstAt sqBig sqBig_step 0 _]
  decide +kernel
private def oneOrFive (k : Nat) : Prop := k = 1 ∨ 5 ≤ k
private instance instGroundChk3 : DecidablePred oneOrFive := fun _ => inferInstanceAs (Decidable (_ ∨ _))
theorem pin371 : oneOrFive 1 ∧ ¬ oneOrFive 2 := by decide +kernel
theorem pin372 : bisectFrom oneOrFive 0 8 = 5 ∧ firstAt oneOrFive 0 8 = 1 := by decide +kernel
private def hundred (k : Nat) : Prop := 100 ≤ k
private instance instGroundChk4 : DecidablePred hundred := fun _ => inferInstanceAs (Decidable (_ ≤ _))
private theorem hundred_step (k : Nat) (h : hundred k) : hundred (k + 1) :=
  Nat.le_succ_of_le h
theorem pin373 : ¬ hundred 8 := by decide +kernel
theorem pin374 : bisectFrom hundred 0 8 = 8 ∧ firstAt hundred 0 8 = 8 := by decide +kernel
theorem pin375 : bisectFrom hundred 0 8 = firstAt hundred 0 8 :=
  bisectFrom_eq_firstAt hundred hundred_step 0 8
theorem pin376 : bisect sqTen 4 0 20 = 5 ∧ sqTen 4 := by decide +kernel
theorem pin377 : bisect sqTen 20 4 20 = 5 ∧ sqTen 4 := by decide +kernel
theorem pin378 : bisect hundred 20 0 20 = 20 ∧ ¬ hundred 20 := by decide +kernel

-- the count expressions enter the pair carrier at the one-member site
-- (`Pol.ofNat_val`): `(2 + 3) · 4 = 20` at the data `[2, 3, 4]` reads one
-- value with the carrier's `([2 : 1] + [3 : 1]) [4 : 1]`, and the Horner
-- read's growth past the clearing (`hread_grow`) at `[1, 1, 1, 1, 1]`,
-- `K = 6`, `b = 1`: `6⁴ · 2801 = 3630096` under `7⁴ · 1555 = 3733555`
theorem pin379 : (BPair.ofNat (Pol.val [2, 3, 4] (Pol.mul (Pol.add (Pol.mon (Mon.var 0))
    (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))))).oneValue
    ((BPair.ofNat 2 + BPair.ofNat 3) * BPair.ofNat 4) := by decide +kernel
theorem pin380 : (BPair.ofNat (Pol.val [2, 3, 4] (Pol.mul (Pol.add (Pol.mon (Mon.var 0))
    (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))))).oneValue
    ((BPair.ofNat 2 + BPair.ofNat 3) * BPair.ofNat 4) :=
  Pol.ofNat_val [2, 3, 4] _
theorem pin381 : 6 ^ 4 * hread [1, 1, 1, 1, 1] (6 + 1) ≤ 7 ^ 4 * hread [1, 1, 1, 1, 1] 6 := by
  decide +kernel
theorem pin382 : 6 ^ 4 * hread [1, 1, 1, 1, 1] (6 + 1) ≤ 7 ^ 4 * hread [1, 1, 1, 1, 1] 6 :=
  hread_grow 6 1 (by decide +kernel) [1, 1, 1, 1] 1
theorem pin383 : ¬ (6 ^ 4 * hread [0, 0, 0, 0, 1] (5 + 1) ≤ 7 ^ 4 * hread [0, 0, 0, 0, 1] 5) := by
  decide +kernel

-- the polynomial device (`polEq`): `(x + y) (x + y)` and `x x + 2 x y + y y`
-- read one collected display and one value at the data `[3, 5]`, `64`;
-- the count is load-bearing: at `x x + x y + y y` the displays part and
-- the values, `64` against `49`
private def pSq : Pol :=
  Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))
    (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))
private def pExp : Pol :=
  Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))
    (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))))
    (Pol.mon (Mon.mul (Mon.var 1) (Mon.var 1)))
private def pOff : Pol :=
  Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))
    (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 1))))
    (Pol.mon (Mon.mul (Mon.var 1) (Mon.var 1)))
theorem pin392 : pSq.nf = pExp.nf := by decide +kernel
theorem pin393 : Pol.val [3, 5] pSq = 64 ∧ Pol.val [3, 5] pExp = 64 := by decide +kernel
theorem pin394 : Pol.val [3, 5] pSq = Pol.val [3, 5] pExp := polEq [3, 5] pSq pExp (by decide +kernel)
theorem pin397 : ¬ (pSq.nf = pOff.nf) := by decide +kernel
theorem pin398 : ¬ (Pol.val [3, 5] pSq = Pol.val [3, 5] pOff) := by decide +kernel

-- the device at the pair carrier (`polEqB`): the two formulas read one
-- value at the pair list `[3, 5]` and at a list whose first datum sits
-- on its lower side, `⟨1 : 3⟩` (the square reading `9` either way), the
-- read through the display's pair read (`Pol.valB_nf`, `nfValB`); the
-- parted count refuses
theorem pin427 : (Pol.valB [BPair.ofNat 3, BPair.ofNat 5] pSq).oneValue
    (Pol.valB [BPair.ofNat 3, BPair.ofNat 5] pExp) := by decide +kernel
theorem pin428 : (Pol.valB [BPair.ofNat 3, BPair.ofNat 5] pSq).oneValue
    (Pol.valB [BPair.ofNat 3, BPair.ofNat 5] pExp) :=
  polEqB [BPair.ofNat 3, BPair.ofNat 5] pSq pExp (by decide +kernel)
theorem pin429 : (Pol.valB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pSq).oneValue
      (Pol.valB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pExp)
    ∧ (Pol.valB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pSq).oneValue (BPair.ofNat 9) := by
  decide +kernel
theorem pin430 : (Pol.valB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pSq).oneValue
    (Pol.valB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pExp) :=
  polEqB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pSq pExp (by decide +kernel)
theorem pin431 : (nfValB [BPair.ofNat 3, BPair.ofNat 5] pSq.nf).oneValue (BPair.ofNat 64) := by
  decide +kernel
theorem pin432 : (Pol.valB [BPair.ofNat 3, BPair.ofNat 5] pSq).oneValue
    (nfValB [BPair.ofNat 3, BPair.ofNat 5] pSq.nf) :=
  Pol.valB_nf [BPair.ofNat 3, BPair.ofNat 5] pSq
theorem pin433 : ¬ (Pol.valB [BPair.ofNat 3, BPair.ofNat 5] pSq).oneValue
    (Pol.valB [BPair.ofNat 3, BPair.ofNat 5] pOff) := by decide +kernel
theorem pin434 : ¬ (Pol.valB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pSq).oneValue
    (Pol.valB [⟨.one, posOfSucc 2⟩, BPair.ofNat 5] pOff) := by decide +kernel
-- the atoms any pair terms: a power and a swapped product, `x = 2³` and
-- `y = (2 · 5).swap`, the square reading `4` at `8 + (−10)`
theorem pin435 : (Pol.valB [bpow (BPair.ofNat 2) 3, (BPair.ofNat 2 * BPair.ofNat 5).swap] pSq).oneValue
      (Pol.valB [bpow (BPair.ofNat 2) 3, (BPair.ofNat 2 * BPair.ofNat 5).swap] pExp)
    ∧ (Pol.valB [bpow (BPair.ofNat 2) 3, (BPair.ofNat 2 * BPair.ofNat 5).swap] pSq).oneValue
      (BPair.ofNat 4) := by decide +kernel
theorem pin436 : (Pol.valB [bpow (BPair.ofNat 2) 3, (BPair.ofNat 2 * BPair.ofNat 5).swap] pSq).oneValue
    (Pol.valB [bpow (BPair.ofNat 2) 3, (BPair.ofNat 2 * BPair.ofNat 5).swap] pExp) :=
  polEqB [bpow (BPair.ofNat 2) 3, (BPair.ofNat 2 * BPair.ofNat 5).swap] pSq pExp (by decide +kernel)

/-! The factorial and the Pascal count (`factorial_pos`,
`factorial_add_le`, `ffall`, `factorial_pasc`, `ffall_pow`, `pasc_pow`):
`5! = 120` under `5³ · 2! = 250`, the falling product `5 · 4 · 3 = 60` at
`3! · C(5, 3) = 6 · 10` and the sum's unit beyond the natural, the
comparison `5² · 3 · 2 = 150` under `3² · 5 · 4 = 180` with its order
binder refused at the naturals exchanged, and `5² = 25` under
`2² · C(5, 2) = 40` with its key binder refused at the key beyond the
height, and the count's fast read (`pascD`) at `60 / 6 = 10`, one
value with the count through its theorem; the pair carrier's power `[8 : 1]` at `2³` (`bpow_ofNat`), the
power at or beyond one (`oneLeBpow`), the base under its cube
(`le_bpow_self`) refused at the vacant key, and the self-capped square
(`leB_sq_selfcap`) at `X = 3, A = 3, M = 2`, `9 ≤ 3 + 6` reading
`9 ≤ 6 + 4`, refused at `A = 1`. -/
theorem pin401 : 0 < factorial 4 := factorial_pos 4
theorem pin402 : factorial (2 + 3) ≤ (2 + 3) ^ 3 * factorial 2 := by decide +kernel
theorem pin403 : factorial (2 + 3) ≤ (2 + 3) ^ 3 * factorial 2 := factorial_add_le 2 3
theorem pin404 : ffall 5 3 = 60 ∧ ffall 3 5 = 0 := by decide +kernel
theorem pin405 : factorial 3 * pasc 5 3 = ffall 5 3 := by decide +kernel
theorem pin406 : factorial 3 * pasc 5 3 = ffall 5 3 := factorial_pasc 5 3
theorem pin407 : 5 ^ 2 * ffall 3 2 ≤ 3 ^ 2 * ffall 5 2 := by decide +kernel
theorem pin408 : 5 ^ 2 * ffall 3 2 ≤ 3 ^ 2 * ffall 5 2 := ffall_pow 5 3 (by decide) 2 (by decide)
theorem pin409 : ¬ (3 ^ 2 * ffall 5 2 ≤ 5 ^ 2 * ffall 3 2) := by decide +kernel
theorem pin410 : 5 ^ 2 ≤ 2 ^ 2 * pasc 5 2 := by decide +kernel
theorem pin411 : 5 ^ 2 ≤ 2 ^ 2 * pasc 5 2 := pasc_pow 5 2 (by decide)
theorem pin412 : ¬ (2 ^ 3 ≤ 3 ^ 3 * pasc 2 3) := by decide +kernel
theorem pin421 : pascD 5 3 = 10 := by decide +kernel
theorem pin422 : pascD 5 3 = pasc 5 3 := pascD_eq 5 3
theorem pin423 : ffall (2 + 3) 2 * factorial 3 = factorial (2 + 3) := by decide +kernel
theorem pin424 : ffall (2 + 3) 2 * factorial 3 = factorial (2 + 3) := ffall_factorial 2 3
theorem pin413 : (BPair.ofNat (2 ^ 3)).oneValue (bpow (BPair.ofNat 2) 3) := by decide +kernel
theorem pin414 : (BPair.ofNat (2 ^ 3)).oneValue (bpow (BPair.ofNat 2) 3) := bpow_ofNat 2 3
theorem pin415 : BPair.ofPos .one ≤ bpow (BPair.ofNat 2) 3 := oneLeBpow (by decide +kernel) 3
theorem pin416 : BPair.ofNat 2 ≤ bpow (BPair.ofNat 2) 3 :=
  le_bpow_self (by decide +kernel) 3 (by decide)
theorem pin417 : ¬ (BPair.ofNat 2 ≤ bpow (BPair.ofNat 2) 0) := by decide +kernel
theorem pin418 : BPair.ofNat 3 * BPair.ofNat 3
    ≤ BPair.ofNat 2 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 2 := by decide +kernel
theorem pin419 : BPair.ofNat 3 * BPair.ofNat 3
    ≤ BPair.ofNat 2 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 2 :=
  leB_sq_selfcap (by decide +kernel)
theorem pin420 : ¬ (BPair.ofNat 3 * BPair.ofNat 3
    ≤ BPair.ofNat 2 * BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat 2) := by decide +kernel

/-! The collection's idempotence at its order reads: at the cyclic
relation the collection is off its own collection (transitivity
refused), and at the successor relation as well (trichotomy refused),
while the strict order collects once. -/

theorem pin425 : ¬ (collectBy mdCyc mdEq (collectBy mdCyc mdEq
        [(3, BPair.ofNat 1), (0, BPair.ofNat 1), (1, BPair.ofNat 1)])
      = collectBy mdCyc mdEq [(3, BPair.ofNat 1), (0, BPair.ofNat 1), (1, BPair.ofNat 1)])
    ∧ ¬ (collectBy mdNt mdEq (collectBy mdNt mdEq
        [(0, BPair.ofNat 1), (2, BPair.ofNat 1), (1, BPair.ofNat 1)])
      = collectBy mdNt mdEq [(0, BPair.ofNat 1), (2, BPair.ofNat 1), (1, BPair.ofNat 1)])
    ∧ collectBy mdLt mdEq (collectBy mdLt mdEq
        [(3, BPair.ofNat 1), (0, BPair.ofNat 1), (1, BPair.ofNat 1)])
      = collectBy mdLt mdEq [(3, BPair.ofNat 1), (0, BPair.ofNat 1), (1, BPair.ofNat 1)] := by
  decide +kernel
theorem pin426 : collectBy mdLt mdEq (collectBy mdLt mdEq
        [(3, BPair.ofNat 1), (0, BPair.ofNat 1), (1, BPair.ofNat 1)])
      = collectBy mdLt mdEq [(3, BPair.ofNat 1), (0, BPair.ofNat 1), (1, BPair.ofNat 1)] :=
  collectBy_idem mdLt mdEq
    (fun _ _ _ h1 h2 =>
      decide_eq_true (Nat.lt_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
    (fun _ _ h => of_decide_eq_true h)
    (fun _ _ he hl => decide_eq_true (Nat.lt_of_le_of_ne
      (Nat.le_of_not_lt (of_decide_eq_false hl))
      (fun hba => Bool.noConfusion (he.symm.trans (decide_eq_true hba.symm)))))
    _

/-! The off-key fold at the balance-pair bundle with the identity
map: the family `(1, 2, 4)` at the keys nought, one and two, and a
key beyond the family the whole fold. -/

theorem pin437 : (offFoldO bpairOps (fun x => x) 0 [⟨2, 1⟩, ⟨3, 1⟩, ⟨5, 1⟩]).oneValue ⟨7, 1⟩
    ∧ (offFoldO bpairOps (fun x => x) 1 [⟨2, 1⟩, ⟨3, 1⟩, ⟨5, 1⟩]).oneValue ⟨6, 1⟩
    ∧ (offFoldO bpairOps (fun x => x) 2 [⟨2, 1⟩, ⟨3, 1⟩, ⟨5, 1⟩]).oneValue ⟨4, 1⟩
    ∧ (offFoldO bpairOps (fun x => x) 5 [⟨2, 1⟩, ⟨3, 1⟩, ⟨5, 1⟩]).oneValue ⟨8, 1⟩ := by
  decide +kernel

/-! The products of every member but one at one pass (`othersAll`,
the prefix products against the suffix products): the family
`(2, 3, 5)` at the unit one reads `(15, 10, 6)`, a one-member family
reads the unit, the vacant family reads vacant, and the four-member
family its three-member products. -/

theorem pin438 : othersAll (fun a b : Nat => a * b) 1 [2, 3, 5] = [15, 10, 6]
    ∧ othersAll (fun a b : Nat => a * b) 1 [7] = [1]
    ∧ othersAll (fun a b : Nat => a * b) 1 [] = []
    ∧ othersAll (fun a b : Nat => a * b) 1 [2, 3, 5, 7] = [105, 70, 42, 30] := by
  decide +kernel

/-! The product lists filtered at a pointwise read are the filtered
domains' product lists, through the theorem and decided at two
domains with one member refused, and a flat map over a filtered
list reads the kept members' rows alone. -/

theorem pin439 : (prodLists [[1, 2, 3], [4, 5]]).filter (fun l => l.all (fun x => x != 2))
    = prodLists [[1, 3], [4, 5]] := filter_prodLists _ _
theorem pin440 : (prodLists [[1, 2, 3], [4, 5]]).filter (fun l => l.all (fun x => x != 2))
    = [[1, 4], [1, 5], [3, 4], [3, 5]] := by decide +kernel
theorem pin441 : ([1, 2, 3].filter (fun x => x != 2)).flatMap (fun x => [x, x])
    = [1, 1, 3, 3] := by decide +kernel

/-! The coroot range box has distinct selections, including the
zero-coordinate box's unit selection. -/

theorem pin442 : distinctList (boxAll [1, 2]) := boxAll_distinct [1, 2]
theorem pin443 : boxAll [1, 2] = [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2]] := by
  decide +kernel
theorem pin444 : distinctList (boxAll []) := boxAll_distinct []

/-! Keyed insertion preserves counts at tied and distinct keys. -/

theorem pin445 : countOf 2 (insertKeyDesc (fun x : Nat => x) 2 [4, 2, 1])
    = countOf 2 [2, 4, 2, 1] := countOf_insertKeyDesc _ 2 2 [4, 2, 1]
theorem pin446 : insertKeyDesc (fun x : Nat => x) 2 [4, 2, 1] = [4, 2, 2, 1] := by
  decide +kernel
theorem pin447 : countOf 2 (insertKeyDesc (fun x : Nat => 10 - x) 2 [1, 2, 4])
    = countOf 2 [2, 1, 2, 4] := countOf_insertKeyDesc _ 2 2 [1, 2, 4]

/-! A cutoff predicate confined to the smaller box keeps that
box's exact product order inside the larger enumeration. -/

theorem pin448 : (boxAll [2, 3]).filter (fun m => decide (sumNat m ≤ 1))
    = (boxAll [1, 1]).filter (fun m => decide (sumNat m ≤ 1)) := by
  apply boxAll_filter_eq [1, 1] [2, 3] rfl (by decide +kernel)
  intro m _ hp i hi
  have hb : ∀ j, j < 2 → 1 ≤ getAt 0 [1, 1] j := by decide +kernel
  exact Nat.le_trans (Nat.le_trans (getAt_le_sumNat m i) (of_decide_eq_true hp)) (hb i hi)
theorem pin449 : (boxAll [2, 3]).filter (fun m => decide (sumNat m ≤ 1))
    = [[0, 0], [0, 1], [1, 0]] := by decide +kernel
theorem pin450 : ¬ (boxAll [2]).filter (fun _ => true)
    = (boxAll [1]).filter (fun _ => true) := by decide +kernel
theorem pin451 : ¬ (boxAll [0]).filter (fun _ => true)
    = (boxAll []).filter (fun _ => true) := by decide +kernel
theorem pin452 : ¬ (boxAll [0]).filter (fun m => decide (sumNat m ≤ 1))
    = (boxAll [1]).filter (fun m => decide (sumNat m ≤ 1)) := by decide +kernel
theorem pin453 (d : Nat) : 7 / d ≤ 11 / d := divMono 7 11 d (by decide)
theorem pin454 : 7 / 2 = 3 ∧ 11 / 2 = 5 ∧ 7 / 0 = 0 := by decide +kernel

/-! Digit codes, distinct-list counts, and margin parity. -/

theorem pin455 : dedupF [2, 1, 2, 3, 1] = [2, 1, 3]
    ∧ (dedupF [2, 1, 2, 3, 1]).length ≤ ([2, 1, 2, 3, 1] : List Nat).length :=
  ⟨by decide +kernel, length_dedupF_le _⟩
theorem pin456 (n : Nat) (hn : n < 16)
    (h : ∀ i, i < 4 → baseDigit 2 i n = getAt 0 [1, 0, 1, 1] i) : n = 13 := by
  apply baseDigit_ext 2 (by decide) 4 n 13 hn (by decide)
  have hd : ∀ i, i < 4 → getAt 0 [1, 0, 1, 1] i = baseDigit 2 i 13 := by decide +kernel
  exact fun i hi => (h i hi).trans (hd i hi)
theorem pin457 : ∃ n, n < 16 ∧ ∀ i, i < 4 → baseDigit 2 i n = getAt 0 [1, 0, 1, 1] i :=
  baseDigit_exists 2 (by decide) 4 _ (by decide +kernel)
theorem pin458 : (∀ i, i < 4 → baseDigit 2 i 13 = baseDigit 2 i 29) ∧ 13 ≠ 29 := by
  decide +kernel
theorem pin459 : ¬ (∃ n, n < 4 ∧ baseDigit 2 0 n = 2) := by decide +kernel
theorem pin460 (n : Nat) : (List.range n).foldl (fun a k => a * (k + 1)) 1 = factorial n :=
  factorial_foldl n
theorem pin461 (x : BPair) : x.swap.marginN = x.marginN := BPair.marginN_swap x
theorem pin462 (x y : BPair) : (x + y).marginN % 2 = (x.marginN + y.marginN) % 2 :=
  BPair.marginN_add_mod_two x y
theorem pin463 (x : BPair) : (x + x).marginN % 2 = 0 := BPair.marginN_double x
theorem pin464 : ((⟨4, 8⟩ : BPair) + ⟨10, 3⟩).marginN = 3
    ∧ ((⟨4, 8⟩ : BPair) + ⟨10, 3⟩).marginN % 2 = 1 := by decide +kernel
theorem pin465 : ¬ (∀ j, j < 2 → ∀ i, i < j →
    getAt BPair.unit [BPair.ofNat 2, BPair.ofNat 2] j
      < getAt BPair.unit [BPair.ofNat 2, BPair.ofNat 2] i) := by decide +kernel
theorem pin466 : famFold Nat.add 0 (fun n => n + 6) [1, 2, 4] % 3
    = famFold Nat.add 0 (fun n => n) [1, 2, 4] % 3 := by
  apply famFold_mod_congr 3 _ _ _
  decide +kernel

/-! The scalar pairing increases at the reflection's coordinate
exchange or exchanged partners, with both strictness premises read. -/

theorem pin467 (a b r s : BPair) (hab : a < b) (hsr : s < r) :
    a * r + b * s < b * r + a * s := BPair.exchange_lt a b r s hab hsr
theorem pin468 (a b r s : BPair) (hab : a + b < BPair.unit) (hrs : BPair.unit < r + s) :
    a * r + b * s < b.swap * r + a.swap * s := BPair.pair_flip_lt a b r s hab hrs
theorem pin469 : ¬ (BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1) := by decide +kernel
theorem pin470 : ¬ (BPair.unit * BPair.ofNat 1 + BPair.ofNat 1 * BPair.ofNat 2
    < BPair.ofNat 1 * BPair.ofNat 1 + BPair.unit * BPair.ofNat 2) := by decide +kernel
theorem pin471 : ¬ (BPair.ofNat 1 * BPair.ofNat 2 + (BPair.ofNat 1).swap * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 2 + (BPair.ofNat 1).swap * BPair.ofNat 1) := by decide +kernel
theorem pin472 : ¬ ((BPair.ofNat 2).swap * BPair.unit + BPair.ofNat 1 * BPair.unit
    < (BPair.ofNat 1).swap * BPair.unit + BPair.ofNat 2 * BPair.unit) := by decide +kernel

/-! Magnitudes identify nonnegative balance values, while the
sign hypotheses distinguish an ordered display from its final
sign change. Adjacent exchanges preserve the natural dot pairing. -/

theorem pin473 {x y : BPair} (hx : BPair.unit ≤ x) (hy : BPair.unit ≤ y)
    (h : x.marginN = y.marginN) : x.oneValue y := BPair.oneValue_of_marginN hx hy h
theorem pin474 {x y : BPair} (hx : BPair.unit ≤ x) (h : x < y) : x.marginN < y.marginN :=
  BPair.marginN_lt hx h
theorem pin475 {x y : BPair} (h : x < y) (hs : x.swap < y) : x.marginN < y.marginN :=
  BPair.marginN_lt_of_sides h hs
theorem pin476 : (BPair.ofNat 3).marginN = ((BPair.ofNat 3).swap).marginN
    ∧ ¬ (BPair.ofNat 3).oneValue (BPair.ofNat 3).swap := by decide +kernel
theorem pin477 : (BPair.ofNat 4).swap < BPair.ofNat 2
    ∧ ¬ ((BPair.ofNat 4).swap).marginN < (BPair.ofNat 2).marginN := by decide +kernel
theorem pin478 (k : Nat) (u v : List Nat) (h : u.length = v.length) :
    dotNat u (adjSwap k v) = dotNat (adjSwap k u) v := dotNat_adjSwap k u v h
theorem pin479 : dotNat [2, 5, 7] (adjSwap 1 [11, 13, 17])
    = dotNat (adjSwap 1 [2, 5, 7]) [11, 13, 17] := by decide +kernel
theorem pin480 : dotNat [2] (adjSwap 0 [3, 5]) ≠ dotNat (adjSwap 0 [2]) [3, 5] := by decide +kernel

/-! The recursion's exact cofactor is forced by its trace balance,
including shifted pair representatives and a zero multiplicity. -/

theorem pin481 : (⟨13, 4⟩ : BPair) > ⟨7, 4⟩
    ∧ ((⟨13, 4⟩ : BPair) * BPair.ofNat 5).oneValue ((⟨7, 4⟩ : BPair) * BPair.ofNat 5 + ⟨37, 7⟩)
    ∧ ((⟨37, 7⟩ : BPair).norm.marginN / ((⟨13, 4⟩ : BPair) + (⟨7, 4⟩ : BPair).swap).norm.marginN) = 5 := by
  decide +kernel
theorem pin482 (Q P G : BPair) (c : Nat) (h : P < Q)
    (hr : (Q * BPair.ofNat c).oneValue (P * BPair.ofNat c + G)) :
    G.norm.marginN % (Q + P.swap).norm.marginN = 0
      ∧ G.norm.marginN / (Q + P.swap).norm.marginN = c := (BPair.rec_count c h hr).2
theorem pin483 : ((BPair.ofNat 9 * BPair.ofNat 0).oneValue (BPair.ofNat 3 * BPair.ofNat 0 + BPair.unit))
    ∧ BPair.unit.marginN / (BPair.ofNat 9 + (BPair.ofNat 3).swap).norm.marginN = 0 := by decide +kernel
theorem pin484 : ¬ (BPair.ofNat 9 * BPair.ofNat 5).oneValue (BPair.ofNat 3 * BPair.ofNat 5 + BPair.ofNat 31)
    ∧ (BPair.ofNat 31).marginN % (BPair.ofNat 9 + (BPair.ofNat 3).swap).norm.marginN ≠ 0 := by decide +kernel
theorem pin485 : (BPair.ofNat 3 * BPair.ofNat 5).oneValue (BPair.ofNat 3 * BPair.ofNat 5 + BPair.unit)
    ∧ ¬ 0 < (BPair.ofNat 3 + (BPair.ofNat 3).swap).norm.marginN := by decide +kernel

theorem pin486 (n : Nat) : (BPair.ofNat n).norm = BPair.ofNat n := BPair.norm_ofNat n

/-- Equal keys remain separate and insertion follows the
existing equal-key entry. -/
theorem pin487 : insertKeyDesc Prod.fst (1, true) [(2, false), (1, false), (0, false)]
    = [(2, false), (1, false), (1, true), (0, false)] := by decide +kernel

theorem pin488 : keysInOrder (fun a b : Nat × Bool => decide (b.1 ≤ a.1))
    ((insertKeyDesc Prod.fst (1, true) [(2, false), (1, false), (0, false)]).map (fun a => (a, ()))) = true :=
  insertKeyDesc_order Prod.fst (1, true) _ (by decide +kernel)

/-- Inserting into an unordered list does not sort its tail. -/
theorem pin489 : ¬ keysInOrder (fun a b : Nat × Bool => decide (b.1 ≤ a.1))
    ((insertKeyDesc Prod.fst (3, true) [(0, false), (2, false)]).map (fun a => (a, ()))) = true := by decide +kernel

/-- Weak order identifies repeated entries and trailing zeros
from the occurrence counts. -/
theorem pin490 (y : List Nat) (hy : y.length = 5)
    (ho : ∀ i, i + 1 < y.length → getAt 0 y (i + 1) ≤ getAt 0 y i)
    (hc : ∀ v, countOf v y = countOf v [4, 4, 1, 0, 0]) : y = [4, 4, 1, 0, 0] :=
  descLeUnique y _ hy ho (by decide +kernel) hc

/-- The same counts at a different order do not identify a list. -/
theorem pin491 : countOf 1 [1, 2, 1] = countOf 1 [2, 1, 1]
    ∧ ¬ (∀ i, i + 1 < 3 → getAt 0 [1, 2, 1] (i + 1) ≤ getAt 0 [1, 2, 1] i) := by decide +kernel

/-- Width and weak order alone do not fix the multiplicities. -/
theorem pin492 : (∀ i, i + 1 < 3 → getAt 0 [2, 2, 0] (i + 1) ≤ getAt 0 [2, 2, 0] i)
    ∧ countOf 2 [2, 2, 0] ≠ countOf 2 [2, 0, 0] := by decide +kernel

theorem pin493 (x y : BPair) (hx : BPair.unit ≤ x) (h : x ≤ y) :
    x.marginN ≤ y.marginN := BPair.marginN_le hx h

theorem pin494 : (BPair.ofNat 3).swap ≤ BPair.ofNat 1
    ∧ ¬ (BPair.ofNat 3).swap.marginN ≤ (BPair.ofNat 1).marginN := by decide +kernel

/-- The zero box contains exactly the zero list at every width,
including the vacant coordinate list. -/
theorem pin495 (n : Nat) : boxAll (List.replicate n 0) = [List.replicate n 0] := boxAll_zero n

theorem pin496 : boxAll [0, 1] ≠ [[0, 0]] := by decide +kernel


/-- Natural pairing monotonicity includes truncation of the
first list and an occupied growth in a later coordinate. -/
theorem pin497 (m x y : List Nat) (h : x.length = y.length)
    (he : ∀ i, i < x.length → getAt 0 x i ≤ getAt 0 y i) :
    dotNat m x ≤ dotNat m y := dotNat_mono_right m x y h he

theorem pin498 : dotNat [2, 3, 5] [1, 2] = 8 ∧ dotNat [2, 3, 5] [1, 4] = 14 := by decide +kernel

/-- Memberwise count equality reads every key, including keys
off both families, while repeated members keep their multiplicity. -/
theorem pin499 (A B : List Nat) (hA : ∀ x ∈ A, countOf x A = countOf x B)
    (hB : ∀ x ∈ B, countOf x A = countOf x B) (x : Nat) : countOf x A = countOf x B :=
  countOf_eq_of_members A B hA hB x

/-- A closure keeps an invariant at every round, including
fresh lists shorter than its accumulated pool. -/
theorem pin500 {α : Type} (P : α → Prop) (step : α → List α)
    (join : List α → α → List α)
    (hs : ∀ a, P a → ∀ b ∈ step a, P b)
    (hj : ∀ l a, (∀ b ∈ l, P b) → P a → ∀ b ∈ join l a, P b)
    (fuel : Nat) (pool fresh : List α)
    (hp : ∀ a ∈ pool, P a) (hf : ∀ a ∈ fresh, P a) :
    ∀ a ∈ closeBy step join fuel pool fresh, P a :=
  closeBy_all P step join hs hj fuel pool fresh hp hf

theorem pin501 : closeBy (fun n : Nat => [n + 1]) (fun l a => l ++ [a]) 2 [0] [0] = [0, 1, 2] := by
  decide +kernel

/-- A closure's appended members inherit the step's own read. -/
theorem pin502 {α : Type} (Q R : α → Prop) (step : α → List α) (join : List α → α → List α)
    (hj : ∀ l a, join l a = l ∨ join l a = l ++ [a])
    (hs : ∀ a, Q a → ∀ b ∈ step a, Q b ∧ R b)
    (fuel : Nat) (pool fresh : List α) (hp : ∀ a ∈ pool, Q a) (hf : ∀ a ∈ fresh, Q a) :
    ∃ tail, closeBy step join fuel pool fresh = pool ++ tail ∧ ∀ a ∈ tail, Q a ∧ R a :=
  closeBy_reads Q R step join hj hs fuel pool fresh hp hf

theorem pin503 (l : List (Nat × BPair)) (fuel : Nat) (h : l.length ≤ fuel) :
    mergeDot (fun a b => a < b) (fun a b => a == b) fuel l l = bsum (fun p => p.2 * p.2) l :=
  mergeDot_self _ _ (fun _ => ground.eqBeqOf rfl) fuel l h

/-- Starved pairing fuel misses an occupied square. -/
theorem pin504 : mergeDot (fun a b : Nat => a < b) (fun a b => a == b)
    0 [(0, BPair.ofNat 1)] [(0, BPair.ofNat 1)] = BPair.unit := by decide +kernel

/-- A collected family preserves linear reads through shared keys
and coefficients on both sides. -/
theorem pin505 {α : Type} [DecidableEq α] (lt eq : α → α → Bool)
    (he : ∀ a b, eq a b = true → a = b) (f : α → BPair) (l : List (α × BPair)) :
    (bsum (fun p => p.2 * f p.1) (collectBy lt eq l)).oneValue
      (bsum (fun p => p.2 * f p.1) l) := foldB_collectBy lt eq he f l

theorem pin506 :
    (bsum (fun p => p.2 * BPair.ofNat (p.1 + 1))
      (collectBy (fun a b : Nat => a < b) (fun a b => a == b)
        [(2, BPair.ofNat 3), (0, BPair.ofNat 4), (2, (BPair.ofNat 3).swap)] )).oneValue
      (BPair.ofNat 4)
    ∧ ([0, 1] ++ [2, 3]).set 1 9 = [0, 9, 2, 3]
    ∧ ([0, 1] ++ [2, 3]).set 3 9 = [0, 1, 2, 9] := by decide +kernel

/-- The descending-height fuel bound reads arbitrary pools and
fresh lists at the stated join. -/
theorem pin507 {α : Type} (step : α → List α) (join : List α → α → List α)
    (height : α → Nat) (hj : ∀ l a, join l a = l ∨ join l a = l ++ [a])
    (hs : ∀ a b, b ∈ step a → height b < height a)
    (fuel extra : Nat) (pool fresh : List α) (hf : ∀ a ∈ fresh, height a < fuel) :
    closeBy step join (fuel + extra) pool fresh = closeBy step join fuel pool fresh :=
  closeBy_fuel step join height hj hs fuel extra pool fresh hf

/-- An ascending step, a join changing its input, and insufficient
fuel refuse stabilization. An omitted fresh source has its child
outside the returned pool. -/
theorem pin508 :
    closeBy (fun n : Nat => [n + 1]) (fun l n => l ++ [n]) 2 [] [0]
      ≠ closeBy (fun n : Nat => [n + 1]) (fun l n => l ++ [n]) 1 [] [0]
    ∧ closeBy (fun n : Nat => if n == 0 then [] else [n - 1])
      (fun l n => l ++ [n + 1]) 4 [] [2]
      ≠ closeBy (fun n : Nat => if n == 0 then [] else [n - 1])
        (fun l n => l ++ [n + 1]) 3 [] [2]
    ∧ closeBy (fun n : Nat => if n == 0 then [] else [n - 1])
      (fun l n => l ++ [n]) 1 [] [1]
      ≠ closeBy (fun n : Nat => if n == 0 then [] else [n - 1])
        (fun l n => l ++ [n]) 0 [] [1]
    ∧ countOf 0 (closeBy (fun n : Nat => if n == 0 then [] else [n - 1])
      (fun l n => l ++ [n]) 3 [1] []) = 0 := by decide +kernel

/-- Finite-key contraction includes repeated raw coefficients
and a key list in an independent order. -/
theorem pin509 :
    (bsum (fun k => BPair.ofNat (k + 1) * keyFoldB (fun a b : Nat => a == b) k
      [(2, BPair.ofNat 3), (0, BPair.ofNat 4), (2, (BPair.ofNat 1).swap)]) [2, 0]).oneValue
      (BPair.ofNat 10) := by decide +kernel

/-- Repeated contributing keys, unsound equality and nonreflexive
equality each change the linear contraction. -/
theorem pin510 :
    ¬ (bsum (fun k => BPair.ofNat (k + 1) * keyFoldB (fun a b : Nat => a == b) k
      [(2, BPair.ofNat 3)]) [2, 2]).oneValue (BPair.ofNat 9)
    ∧ ¬ (bsum (fun k => BPair.ofNat (k + 1) * keyFoldB (fun _ _ : Nat => true) k
      [(2, BPair.ofNat 3)]) [2, 0]).oneValue (BPair.ofNat 9)
    ∧ ¬ (bsum (fun k => BPair.ofNat (k + 1) * keyFoldB (fun _ _ : Nat => false) k
      [(2, BPair.ofNat 3)]) [2]).oneValue (BPair.ofNat 9) := by decide +kernel

/-- The shared string coefficient identity reads every depth gap. -/
theorem pin511 (b g m : Nat) :
    (b + 1) * ((b + 1 + g) - b) + (m + g)
      = (b + 1 + 1) * ((b + 1 + g) - (b + 1)) + (m + (b + 1)) := coeffCross b g m

/-- Distinct list writes commute at every element type and index. -/
theorem pin512 {α : Type} (l : List α) (p q : Nat) (u v : α) (h : p ≠ q) :
    (l.set p u).set q v = (l.set q v).set p u := set_comm l p q u v h

/-- Distinct-position writes exchange inside and beyond the list;
two different writes at one position refuse the exchange. -/
theorem pin513 :
    ((([7, 4, 9] : List Nat).set 0 2).set 2 5 = ([7, 4, 9].set 2 5).set 0 2) ∧
    ((([7, 4] : List Nat).set 8 2).set 0 5 = ([7, 4].set 0 5).set 8 2) ∧
    ((([7] : List Nat).set 0 2).set 0 5 ≠ ([7].set 0 5).set 0 2) := by decide +kernel

end ground
