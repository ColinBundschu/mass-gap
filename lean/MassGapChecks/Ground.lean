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
at the first member's own key.
-/

open ground

/-! The carrier's arithmetic, at numerals. -/

example : (2 : Pos) + 3 = 5 := by decide +kernel
example : (35 : Pos) * 35 = 1225 := by decide +kernel
example : succ (4 : Pos) = 5 := by decide +kernel
example : (5 : Pos) * 7 + 1 = 6 * 6 := by decide +kernel

/-- The kernel-feasibility exhibit at the Weingarten magnitude:
`d_f^4 · d_f^4` at `r = 5`. -/
example : (1296 : Pos) * 1296 = 1679616 := by decide +kernel

/-- The kernel-feasibility exhibit past the elimination's entry
growth: a 60-bit product at the stored counts' machine integers. -/
example : (123456789 : Pos) * 987654321 = 121932631112635269 := by
  decide +kernel

/-! The division with remainder, its naming read at the output. -/

example : divMod 13 3 = (some 4, some 1) := rfl
example : divMod 12 3 = (some 4, none) := rfl
example : divMod 2 5 = (none, some 2) := rfl
example : divModRead 13 3 := by decide +kernel
example : divModRead 12 3 := by decide +kernel
example : divModRead 2 5 := by decide +kernel
example : divModRead 1225 35 := by decide +kernel

/-! The quotient's bracket: an occupied quotient brackets the
dividend between its own multiple and the next, a vacant quotient
prices the dividend below the divisor, and the bracket names the
quotient back — the theorem routes beside the decides. -/

example : (3 : Pos) * 4 ≤ 13 ∧ (13 : Pos) < 3 * ground.succ 4 :=
  divQuot_read 13 3 4 (by decide +kernel)
example : (3 : Pos) * 4 ≤ 13 ∧ (13 : Pos) < 3 * ground.succ 4 := by
  decide +kernel
example : (2 : Pos) < 5 := divQuot_vac 2 5 (by decide +kernel)
example : (ground.divMod 13 3).1 = some 4 :=
  divQuot_eq 13 3 4 (by decide +kernel) (by decide +kernel)
/-- The refusal isolating the bracket's upper end: at the forged
quotient the strict step refuses and the naming with it. -/
example : ¬ ((13 : Pos) < 3 * ground.succ 3) := by decide +kernel
example : ¬ ((ground.divMod 13 3).1 = some 3) := by decide +kernel

/-! Order as gap-existence, and the trichotomy: the read is data,
the gap constructed with the outcome. -/

example : (5 : Pos) < 12 := by decide +kernel
example : (5 : Pos) + 7 = 12 := by decide +kernel
example : ¬ ((12 : Pos) < 12) := by decide +kernel
example : (12 : Pos) ≤ 12 := by decide +kernel
example : (5 : Pos) ≤ 12 := by decide +kernel
example : (match trich (5 : Pos) 12 with
  | .lt g _ => some g | .eq _ => none | .gt _ _ => none) = some 7 := rfl
example : (match trich (12 : Pos) 5 with
  | .lt _ _ => none | .eq _ => none | .gt g _ => some g) = some 7 := rfl
example : (match BPair.side ⟨9, 9⟩ with
  | .lt _ _ => false | .eq _ => true | .gt _ _ => false) = true := rfl

/-! The scalar pair's displayed reads. -/

example : Pair.oneValue (⟨1, 2⟩ + ⟨1, 3⟩) ⟨5, 6⟩ := by decide +kernel
example : Pair.oneValue ((⟨2, 3⟩ : Pair) * ⟨3, 2⟩) (Pair.ofPos 1) := by
  decide +kernel
example : (⟨1, 3⟩ : Pair) < ⟨1, 2⟩ := by decide +kernel
example : Pair.oneValue (Pair.cofactor ⟨3, 4⟩ ⟨1, 2⟩) ⟨3, 2⟩ := by decide +kernel

/-- A homogeneity instance: the sum's read at a rescaled
representative. -/
example : Pair.oneValue (⟨2, 4⟩ : Pair) ⟨1, 2⟩
    ∧ Pair.oneValue ((⟨2, 4⟩ : Pair) + ⟨1, 3⟩) ((⟨1, 2⟩ : Pair) + ⟨1, 3⟩)
    := by decide +kernel

/-! The harmonic numbers. -/

example : Pair.oneValue (harmonic 1) (Pair.ofPos 1) := by decide +kernel
example : Pair.oneValue (harmonic 3) ⟨11, 6⟩ := by decide +kernel
example : Pair.oneValue (harmonic 5) ⟨137, 60⟩ := by decide +kernel
example : harmonic (succ 2) = harmonic 2 + ⟨1, succ 2⟩ := harmonic_succ 2
example : Pair.oneValue (harmonic 2 + ⟨1, 3⟩) (harmonic 3) := by decide +kernel

/-! The balance pair's displayed reads. -/

example : BPair.oneValue ((⟨3, 1⟩ : BPair) * ⟨5, 2⟩) ⟨7, 1⟩ := by decide +kernel
example : BPair.oneValue ((⟨5, 2⟩ : BPair) + BPair.swap ⟨5, 2⟩)
    BPair.unit := by decide +kernel
example : BPair.oneValue (BPair.addPos ⟨2, 5⟩ 3) BPair.unit := by decide +kernel
example : (⟨2, 5⟩ : BPair) < ⟨4, 1⟩ := by decide +kernel
example : BPair.oneValue (BPair.sum [⟨2, 1⟩, ⟨1, 3⟩, ⟨5, 1⟩]) ⟨4, 1⟩ := by
  decide +kernel

/-! The canonical representative at a witnessed gap: the side's
one-member display reads the gap's successor at the exceeding
member either way, decided and through its theorem, with the
forged gap refused. -/

example : (⟨2, 5⟩ : BPair).norm = ⟨Pos.one, succ 3⟩ := by decide +kernel
example : (⟨2, 5⟩ : BPair).norm = ⟨Pos.one, succ 3⟩ :=
  BPair.norm_of_gapLt (g := 3) (by decide +kernel)
example : ¬ (⟨2, 5⟩ : BPair).norm = ⟨Pos.one, succ 2⟩ := by decide +kernel

example : (⟨5, 2⟩ : BPair).norm = ⟨succ 3, Pos.one⟩ := by decide +kernel
example : (⟨5, 2⟩ : BPair).norm = ⟨succ 3, Pos.one⟩ :=
  BPair.norm_of_gapGt (g := 3) (by decide +kernel)
example : ¬ (⟨5, 2⟩ : BPair).norm = ⟨succ 4, Pos.one⟩ := by decide +kernel

/-! The stored count's injectivity read, the literal-multiplier
expansions, and the unit summands' sum, each decided and through
its theorem. -/

example : (1 + 1 : Nat) = 2 := by decide +kernel
example : (1 + 1 : Nat) = 2 :=
  ground.posMkInj (a := 1 + 1) (b := 2) rfl

example : 3 * 7 = 7 + 7 + 7 := by decide +kernel
example : 3 * 7 = 7 + 7 + 7 := ground.threeMul 7
example : 4 * 7 = 2 * 7 + 2 * 7 := by decide +kernel
example : 4 * 7 = 2 * 7 + 2 * 7 := ground.fourMul 7

example : ((⟨2, 2⟩ : BPair) + ⟨5, 5⟩).oneValue BPair.unit := by
  decide +kernel
example : ((⟨2, 2⟩ : BPair) + ⟨5, 5⟩).oneValue BPair.unit :=
  BPair.add_units (by decide +kernel) (by decide +kernel)
example : ¬ ((⟨3, 2⟩ : BPair) + ⟨5, 5⟩).oneValue BPair.unit := by
  decide +kernel

/-! The margin at the count carrier: the exceeding member's gap
either way, an equal-membered pair at nought. -/

example : BPair.marginN ⟨3, 1⟩ = 2 := by decide +kernel
example : BPair.marginN ⟨2, 2⟩ = 0 := by decide +kernel
example : BPair.marginN ⟨1, 5⟩ = 4 := by decide +kernel

/-! The margin kit's instances: the class read at one count on
either side, the sum at unit-dominant pairs, the natural entries'
counts, and the return to the entry at one value — each beside its
kernel value pin. -/

example : BPair.marginN ⟨6, 2⟩ = BPair.marginN ⟨5, 1⟩ :=
  BPair.marginN_congr (by decide +kernel)
example : BPair.marginN ⟨2, 6⟩ = BPair.marginN ⟨1, 5⟩ :=
  BPair.marginN_congr (by decide +kernel)
example : BPair.marginN (BPair.add ⟨5, 2⟩ ⟨4, 1⟩)
    = BPair.marginN ⟨5, 2⟩ + BPair.marginN ⟨4, 1⟩ := by decide +kernel
example : BPair.marginN (BPair.add ⟨5, 2⟩ ⟨4, 1⟩)
    = BPair.marginN ⟨5, 2⟩ + BPair.marginN ⟨4, 1⟩ :=
  BPair.marginN_add (by decide +kernel) (by decide +kernel)
example : (BPair.ofNat 3).marginN = 3 := by decide +kernel
example : (BPair.ofNat 0).marginN = 0 := by decide +kernel
example : (⟨5, 2⟩ : BPair).oneValue
    (BPair.ofNat (BPair.marginN ⟨5, 2⟩)) := by decide +kernel
example : (⟨5, 2⟩ : BPair).oneValue
    (BPair.ofNat (BPair.marginN ⟨5, 2⟩)) :=
  BPair.ofNat_marginN (by decide +kernel)

/-! The composite pair's displayed reads. -/

example : CPair.oneValue ((⟨⟨1, 2⟩, 3⟩ : CPair) + ⟨⟨2, 1⟩, 4⟩)
    ⟨⟨10, 11⟩, 12⟩ := by decide +kernel
example : CPair.oneValue ((⟨⟨2, 1⟩, 3⟩ : CPair) * ⟨⟨1, 2⟩, 2⟩)
    ⟨⟨1, 2⟩, 6⟩ := by decide +kernel
example : CPair.oneValue (CPair.ofPair ⟨3, 4⟩ 1) (CPair.ofPair ⟨3, 4⟩ 7)
    := by decide +kernel
example : CPair.oneValue (CPair.ofPair ⟨1, 2⟩ 1) ⟨⟨3, 2⟩, 2⟩ := by decide +kernel
example : (⟨⟨1, 2⟩, 3⟩ : CPair) < ⟨⟨2, 1⟩, 4⟩ := by decide +kernel
example : CPair.oneValue ((⟨⟨5, 2⟩, 3⟩ : CPair) + ⟨⟨4, 4⟩, 7⟩)
    ⟨⟨5, 2⟩, 3⟩ := by decide +kernel

/-! The cleared pair's read: a balance datum at its stated positive
clearing, two such data reading one value exactly at the
cross-multiplied first data, with the join at the cross-multiplied
numerators and the read's composition. -/

example : ground.keysBelow 5 [(0, BPair.ofNat 2), (4, BPair.unit)] := by
  decide +kernel
example : ¬ ground.keysBelow 4 [(0, BPair.ofNat 2), (4, BPair.unit)] := by
  decide +kernel

private theorem qHalfRead :
    qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 3, (1 : Pos)) := by
  decide +kernel

example : qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 3, (1 : Pos)) :=
  qHalfRead

/-- The cross multiplication is load-bearing: at the clearings `2`
and `1` the first data `6` and `4` read `6` against `8`. -/
example : ¬ qOneValue (BPair.ofNat 6, (2 : Pos))
    (BPair.ofNat 4, (1 : Pos)) := by decide +kernel

example : (BPair.addQ (BPair.ofNat 6, (2 : Pos))
    (BPair.ofNat 3, (1 : Pos))).1.oneValue (BPair.ofNat 12) := by
  decide +kernel
example : (BPair.addQ (BPair.ofNat 6, (2 : Pos))
    (BPair.ofNat 3, (1 : Pos))).2 = 2 := by decide +kernel

example : qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 9, (3 : Pos)) := by
  decide +kernel

example : qOneValue (BPair.ofNat 6, (2 : Pos)) (BPair.ofNat 9, (3 : Pos)) :=
  qOneValue_trans qHalfRead (by decide +kernel)

/-! The collect-by-count fold's decided pin: the family's fold
against the multiplicity-weighted base read. -/

example : ground.famFold Nat.add 0 (fun x => x * x) [2, 1, 2]
    = ground.famFold Nat.add 0
      (fun m => ground.countOf m [2, 1, 2] * (m * m))
      [1, 2, 3] := by decide +kernel

example : ground.famFold Nat.add 0 (fun x => x * x) [2, 1, 2]
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

example : (BPair.ofCounts 2 3).oneValue
    (BPair.ofNat 2 + (BPair.ofNat 3).swap) := by decide +kernel
example : (BPair.ofCounts 4 4).oneValue BPair.unit := by decide +kernel
example : (BPair.ofCounts 0 0).oneValue BPair.unit :=
  BPair.ofCounts_zero
example : (BPair.ofCounts (1 + 3) (2 + 1)).oneValue
    (BPair.ofCounts 1 2 + BPair.ofCounts 3 1) :=
  BPair.ofCounts_add 1 2 3 1
example : (BPair.ofCounts
      (ground.famFold Nat.add 0 (fun x => x) [1, 2])
      (ground.famFold Nat.add 0 (fun x => x + 1) [1, 2])).oneValue
    (ground.famFold BPair.add BPair.unit
      (fun x => BPair.ofCounts x (x + 1)) [1, 2]) :=
  ground.foldB_ofCounts (fun x => x) (fun x => x + 1) [1, 2]
example : ground.signedAt false (BPair.ofNat 7) = BPair.ofNat 7 := by
  decide +kernel
example : ground.signedAt true (BPair.ofNat 7)
    = (BPair.ofNat 7).swap := by decide +kernel
example : (ground.signedAt true (BPair.ofCounts 5 5)).oneValue
    BPair.unit :=
  ground.signedAt_unit true (by decide +kernel)
example : (ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2 (BPair.ofCounts 3 1))
      [(true, true), (true, false)]).oneValue BPair.unit :=
  ground.signedFold_null (fun _ => BPair.ofCounts 3 1) 2
    [(true, true), (true, false)] (by decide +kernel)
    (fun k _ => by
      cases k with
      | true => exact Or.inl (by decide +kernel)
      | false => exact Or.inl (by decide +kernel))
example : (ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2 (BPair.ofCounts 2 2))
      [(false, true)]).oneValue BPair.unit :=
  ground.signedFold_null (fun _ => BPair.ofCounts 2 2) 1
    [(false, true)] (by decide +kernel)
    (fun k _ => Or.inr (by decide +kernel))
example : ¬ (ground.famFold BPair.add BPair.unit
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
example : ground.famFold Nat.add 0 (fun k => 2 * k) [2, 1, 2, 3]
    = ground.famFold Nat.add 0
      (fun k => ground.countOf k [2, 1, 2, 3] * (2 * k)) [1, 2, 3] := by
  have hcov : ∀ x ∈ [2, 1, 2, 3], 0 < ground.countOf x [1, 2, 3] := by
    decide +kernel
  exact ground.famFold_partition (fun k => 2 * k) [2, 1, 2, 3] [1, 2, 3]
    (by decide +kernel)
    (fun x hx => ground.mem_of_countOf_pos x [1, 2, 3] (hcov x hx))

example : ground.famFold Nat.add 0 (fun k => 2 * k) [2, 1, 2, 3] = 16 := by
  decide +kernel

example : ground.famFold Nat.add 0
    (fun k => ground.countOf k [2, 1, 2, 3] * (2 * k)) [1, 2, 3] = 16 := by
  decide +kernel

/-- Refusal isolating `distinctList D`: at the repeated index
`[1, 1]` the weighted fold counts the member twice and the two
sides part, the covering binder surviving beside it. -/
example : ¬ (ground.famFold Nat.add 0 (fun k => 2 * k) [1]
    = ground.famFold Nat.add 0
      (fun k => ground.countOf k [1] * (2 * k)) [1, 1]) := by decide +kernel

example : ∀ x ∈ [1], 0 < ground.countOf x [1, 1] := by decide +kernel

example : ¬ ground.distinctList [1, 1] := by decide +kernel

/-- Refusal isolating the covering binder: at the vacant index the
weighted fold reads the count's unit against an occupied family,
the distinctness surviving beside it. -/
example : ¬ (ground.famFold Nat.add 0 (fun k => 2 * k) [1]
    = ground.famFold Nat.add 0
      (fun k => ground.countOf k [1] * (2 * k)) ([] : List Nat)) := by
  decide +kernel

example : ground.distinctList ([] : List Nat) := by decide +kernel

/-- The constant-one fold at its length, the theorem's instance
with the value beside it. -/
example : ground.famFold Nat.add 0 (fun _ => (1 : Nat)) [7, 7, 3]
    = [7, 7, 3].length := ground.famFold_length [7, 7, 3]

example : ground.famFold Nat.add 0 (fun _ => (1 : Nat)) [7, 7, 3] = 3 := by
  decide +kernel
/-! The list kit's adjacent exchange (`adjSwap`): the pair at a key
and its successor trade places, a key beyond the list's top and a
list of one member reading the list itself. -/

example : adjSwap 0 ([1, 2, 3] : List Nat) = [2, 1, 3] := by decide +kernel
example : adjSwap 1 ([1, 2, 3] : List Nat) = [1, 3, 2] := by decide +kernel
example : adjSwap 0 ([] : List Nat) = [] := by decide +kernel
example : adjSwap 2 ([1, 2] : List Nat) = [1, 2] := by decide +kernel

/-! The power's computing read against the displayed fold: the
value agreement at stated data, the theorem route, the unit base,
and the exponents' join at a depth the fold's step count sits far
beyond, read through the displayed product alone. -/

example : Pos.powC (3 : Pos) 7 = Pos.pow (3 : Pos) 7 := by decide +kernel
example : Pos.powC (3 : Pos) 7 = Pos.pow (3 : Pos) 7 :=
  Pos.powC_eq (3 : Pos) 7
example : Pos.powC Pos.one 12 = Pos.one := by decide +kernel
example : Pos.powC (2 : Pos) 200
    = Pos.powC (2 : Pos) 120 * Pos.powC (2 : Pos) 80 := by decide +kernel

/-! The positive power at the balance carrier: the sited power
against the balance power of its entry, decided and through the
theorem. -/

example : (BPair.ofPos (Pos.pow 3 2)).oneValue (bpow (BPair.ofPos 3) 2) := by
  decide +kernel
example : (BPair.ofPos (Pos.pow 3 2)).oneValue (bpow (BPair.ofPos 3) 2) :=
  ofPos_pow 3 2

/-! The successor power's read at the base against the power, the
unit base's absorbed read, and the power's side at a base at or
beyond the sum's unit — each through the theorem beside its decided
instance, the order read with its binder's isolating refusal. -/

example : (bpow (BPair.ofNat 2) 3).oneValue
    (BPair.ofNat 2 * bpow (BPair.ofNat 2) 2) := by decide +kernel
example : (bpow (BPair.ofNat 2) 3).oneValue
    (BPair.ofNat 2 * bpow (BPair.ofNat 2) 2) :=
  bpow_succ_read (BPair.ofNat 2) 2
example : ¬ ((bpow (BPair.ofNat 2) 3).oneValue
    (BPair.ofNat 2 * bpow (BPair.ofNat 2) 1)) := by decide +kernel

example : (bpow BPair.unit 3).oneValue BPair.unit := by decide +kernel
example : (bpow BPair.unit 3).oneValue BPair.unit := bpow_unit_succ 2
example : ¬ ((bpow (BPair.ofNat 2) 3).oneValue BPair.unit) := by
  decide +kernel

example : BPair.unit ≤ bpow (BPair.ofNat 2) 3 := by decide +kernel
example : BPair.unit ≤ bpow (BPair.ofNat 2) 3 :=
  unitLeBpow (unitLeOfNat 2) 3
example : ¬ (BPair.unit ≤ (BPair.ofNat 2).swap) := by decide +kernel
example : ¬ (BPair.unit ≤ bpow ((BPair.ofNat 2).swap) 1) := by
  decide +kernel

/-! The order's scaling tier: the strict read at a factor strictly
above the sum's unit, the cancellation back off that factor, and
the squared comparison's read back at the trichotomy — each at a
committed pair with the binder's own isolating refusal. -/

/-- The strict read scales: `1 < 3` against the factor `2` reads
`2 < 6`, decided and through the theorem. -/
example : (⟨2, 1⟩ : BPair) < ⟨4, 1⟩ := by decide +kernel

example : (⟨2, 1⟩ : BPair) * ⟨3, 1⟩ < ⟨4, 1⟩ * ⟨3, 1⟩ := by decide +kernel

example : (⟨2, 1⟩ : BPair) * ⟨3, 1⟩ < ⟨4, 1⟩ * ⟨3, 1⟩ :=
  ground.ltB_mulPos (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hc`: at the sum's unit the factor collapses
both sides to that unit and the strict conclusion refuses, the
strict read on the data surviving beside it. -/
example : ¬ (BPair.unit < BPair.unit) := by decide +kernel

example : ¬ ((⟨2, 1⟩ : BPair) * BPair.unit
    < ⟨4, 1⟩ * BPair.unit) := by decide +kernel

/-- The cancellation: at the factor `2` the scaled read `2 ≤ 6`
returns `1 ≤ 3`, decided and through the theorem. -/
example : (⟨2, 1⟩ : BPair) * ⟨3, 1⟩ ≤ ⟨4, 1⟩ * ⟨3, 1⟩ := by decide +kernel

example : (⟨2, 1⟩ : BPair) ≤ ⟨4, 1⟩ := by decide +kernel

example : (⟨2, 1⟩ : BPair) ≤ ⟨4, 1⟩ :=
  ground.leB_unscale (c := ⟨3, 1⟩) (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hc` at the cancellation: the sum's unit
carries the scaled read at every pair, `2` against `-2` included,
while the returned order refuses. -/
example : (⟨3, 1⟩ : BPair) * BPair.unit ≤ ⟨1, 3⟩ * BPair.unit := by
  decide +kernel

example : ¬ ((⟨3, 1⟩ : BPair) ≤ ⟨1, 3⟩) := by decide +kernel

/-- The squared comparison's read back: at `a = -1` against
`b = 1` the squares tie at `1`, the strict read refuses, and the
data read `-1 ≤ 1`, decided and through the theorem. -/
example : BPair.unit ≤ (⟨2, 1⟩ : BPair) := by decide +kernel

example : ¬ ((⟨2, 1⟩ : BPair) * ⟨2, 1⟩ < (⟨2, 3⟩ : BPair) * ⟨2, 3⟩) := by
  decide +kernel

example : (⟨2, 3⟩ : BPair) ≤ ⟨2, 1⟩ := by decide +kernel

example : (⟨2, 3⟩ : BPair) ≤ ⟨2, 1⟩ :=
  ground.leB_of_sq_le (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hb`: at `b = -1` the squares still tie at
`1` and the strict read still refuses, yet the datum at or above
the sum's unit is the missing read and the conclusion refuses. -/
example : ¬ (BPair.unit ≤ (⟨1, 2⟩ : BPair)) := by decide +kernel

example : ¬ ((⟨1, 2⟩ : BPair) * ⟨1, 2⟩ < (⟨2, 1⟩ : BPair) * ⟨2, 1⟩) := by
  decide +kernel

example : ¬ ((⟨2, 1⟩ : BPair) ≤ ⟨1, 2⟩) := by decide +kernel

/-! The subtraction exchanges, the product's left and four-factor
exchanges and the family dropped at its own width — the
hand-rolled reads at the poisoned core neighborhood. -/

example : 7 + 4 - (2 + 4) = 7 - 2 := ground.addSubAddR 7 2 4
example : (7 - 2) * 3 = 7 * 3 - 2 * 3 := ground.subMulR 7 2 3
example : 3 * (5 * 4) = 5 * (3 * 4) := ground.mulLeftComm 3 5 4
example : 2 * 3 * (5 * 7) = 210 := by decide +kernel
example : 2 * 3 * (5 * 7) = 2 * 5 * (3 * 7) :=
  ground.mulMulMulComm 2 3 5 7

/-! The sum's rearrangements: the triple's ends exchanged, the
joined pair's head opened at the front with and without the
standing second withdrawn to the tail, and the second summand
rotated past the tail pair. -/

example : 2 + 3 + 5 = 5 + 3 + 2 := ground.addSwapEnds 2 3 5
example : 2 + 3 + (5 + 7) = 5 + (2 + 7) + 3 :=
  ground.addJoinHeadOut 2 3 5 7
example : 2 + 3 + (5 + 7) = 5 + 2 + (3 + 7) :=
  ground.addJoinHeadFront 2 3 5 7
example : 2 + 3 + 5 + 7 = 2 + 5 + 7 + 3 := ground.addRotTail3 2 3 5 7

/-! The balance carrier's own rearrangements: the seeded sum and
the seeded product each exchanging their two trailing members,
three factors read at their reversal with the middle standing, the
head passing inside the trailing product, the trailing factors
exchanging across the head, and the leftward rotation.
Each stands beside its perturbed refusal, the exchanged member
replaced by a member off its own value. -/

example : (⟨2, 1⟩ : BPair) + ⟨1, 3⟩ + ⟨5, 1⟩ = ⟨8, 5⟩ := by decide +kernel
example : (⟨2, 1⟩ : BPair) + ⟨1, 3⟩ + ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) + ⟨5, 1⟩ + ⟨1, 3⟩ :=
  BPair.add_right_comm ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
example : ¬ ((⟨2, 1⟩ : BPair) + ⟨1, 3⟩ + ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) + ⟨5, 1⟩ + ⟨3, 1⟩) := by decide +kernel

example : (⟨2, 1⟩ : BPair) * ⟨1, 3⟩ * ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨1, 3⟩ :=
  BPair.mul_right_comm ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
example : ¬ ((⟨2, 1⟩ : BPair) * ⟨1, 3⟩ * ⟨5, 1⟩
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨3, 1⟩) := by decide +kernel

example : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨5, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨2, 1⟩) :=
  BPair.mul_rot3r ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
example : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨5, 1⟩ : BPair) * (⟨3, 1⟩ * ⟨2, 1⟩)) := by decide +kernel

example : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨1, 3⟩ : BPair) * ⟨2, 1⟩ * ⟨5, 1⟩ :=
  BPair.mul_left_comm' ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
example : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨3, 1⟩ : BPair) * ⟨2, 1⟩ * ⟨5, 1⟩) := by decide +kernel

example : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨1, 3⟩ :=
  BPair.mul_right_comm' ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
example : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨2, 1⟩ : BPair) * ⟨5, 1⟩ * ⟨3, 1⟩) := by decide +kernel

example : (⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨1, 3⟩ : BPair) * (⟨5, 1⟩ * ⟨2, 1⟩) :=
  BPair.mul_rot3l ⟨2, 1⟩ ⟨1, 3⟩ ⟨5, 1⟩
example : ¬ ((⟨2, 1⟩ : BPair) * (⟨1, 3⟩ * ⟨5, 1⟩)
    = (⟨1, 3⟩ : BPair) * (⟨5, 1⟩ * ⟨3, 1⟩)) := by decide +kernel

/-! The componentwise walk at a vacant second family, vacant at
every first family, beside the occupied second family's refusal. -/

example : List.zipWith (· + ·) [3, 1, 4] ([] : List Nat) = [] :=
  ground.zipWith_nil_right (· + ·) [3, 1, 4]
example : ¬ (List.zipWith (· + ·) [3, 1, 4] [1, 5] = []) := by decide +kernel

example : ([3, 1, 4] : List Nat).drop ([3, 1, 4] : List Nat).length = [] :=
  ground.dropLength [3, 1, 4]
example : ([3, 1, 4] : List Nat).drop 2 = [4] := by decide +kernel
example : ¬ ((!true) = true) := ground.boolNotSelf true
example : ¬ ((!false) = false) := ground.boolNotSelf false
example : (true && true) = true := ground.andIntroB rfl rfl
example : ¬ ((true && false) = true) := by decide +kernel

/-! The guard kit at withheld values: two values at one guard sum
at the guard, and nested guards exchange — each at a concrete
value with its refusal, the second guard's own test and the
withheld arm's vanishing the two load-bearing conjuncts. -/

example : (if 2 < 5 then 3 else 0) + (if 2 < 5 then 4 else 0) = 7 := by
  decide +kernel
example : (if 2 < 5 then 3 else 0) + (if 2 < 5 then 4 else 0)
    = if 2 < 5 then 3 + 4 else 0 := ground.if_add (2 < 5) 3 4
example : ¬ ((if 2 < 5 then 3 else 0) + (if 5 < 2 then 4 else 0)
    = if 2 < 5 then 3 + 4 else 0) := by decide +kernel

example : (if 2 < 5 then (if 1 < 4 then 7 else 0) else 0) = 7 := by
  decide +kernel
example : (if 2 < 5 then (if 1 < 4 then 7 else 0) else 0)
    = if 1 < 4 then (if 2 < 5 then 7 else 0) else 0 :=
  ground.if_swap (2 < 5) (1 < 4) 7
example : ¬ ((if 5 < 2 then (if 1 < 4 then 7 else 0) else 9)
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

example : sumNat [3, 1, 4, 1, 5] = 14 := by decide +kernel
example : prefixAt 0 [3, 1, 4] = 0 := by decide +kernel
example : prefixAt 2 [3, 1, 4] = 4 := by decide +kernel
example : prefixAt 3 [3, 1, 4] = 8 := by decide +kernel
example : prefixAt 3 [5, 1, 7, 9] = 13 := by decide +kernel
example : prefixAt 5 [3, 1, 4] = sumNat [3, 1, 4] := by decide +kernel
example : getAt 0 ([3, 1, 4].reverse) 0 = getAt 0 [3, 1, 4] 2 := by
  decide +kernel
example : getAt 0 ([1, 2, 3] : List Nat).reverse 0 = 3 := by decide +kernel
example : prefixAt 1 ([3, 1, 4].reverse) + prefixAt 2 [3, 1, 4]
    = sumNat [3, 1, 4] := by decide +kernel
example : prefixAt 1 ([3, 1, 4].reverse) + prefixAt 2 [3, 1, 4]
    = sumNat [3, 1, 4] :=
  prefix_reverse_join 1 [3, 1, 4] 2 (by decide +kernel)
example : ([1, 2, 3] : List Nat).reverse = [3, 2, 1] := by decide +kernel
example : countOf 2 ([1, 2, 2, 3].reverse) = 2 := by decide +kernel
example : (([4, 5] : List Nat) ++ [6, 7]).reverse = [7, 6, 5, 4] := by
  decide +kernel
example : ([2, 4, 6] : List Nat).reverse.reverse = [2, 4, 6] := by
  decide +kernel
example : sumNat (List.replicate 2 1 ++ 0 :: List.replicate 3 1)
    = 5 := by decide +kernel
example : sumNat (List.replicate 2 1 ++ 0 :: List.replicate 3 1)
    = 5 := sumNat_replicate_strike 2 5 (by decide +kernel)

example : prefixAt 0 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 0 [2, 1] + prefixAt 0 [0, 3] := by decide +kernel
example : prefixAt 1 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 1 [2, 1] + prefixAt 1 [0, 3] := by decide +kernel
example : prefixAt 2 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 2 [2, 1] + prefixAt 2 [0, 3] := by decide +kernel
example : prefixAt 3 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 3 [2, 1] + prefixAt 3 [0, 3] := by decide +kernel
example : prefixAt 2 (List.zipWith (fun u w => u + w) [2, 1] [0, 3])
    = prefixAt 2 [2, 1] + prefixAt 2 [0, 3] :=
  prefixAt_zipAdd [2, 1] [0, 3] (by decide +kernel) 2

/-- Refusal isolating the matched counts: at a parted pair the
join truncates to the shorter family and the read misses the
longer family's tail. -/
example : ¬ (prefixAt 2 (List.zipWith (fun u w => u + w) [2, 1] [0])
    = prefixAt 2 [2, 1] + prefixAt 2 [0]) := by decide +kernel

example : prefixAt 2 (List.replicate 3 2) = 2 * 2 := by decide +kernel
example : prefixAt 2 (List.replicate 3 2) = 2 * 2 :=
  prefixAt_replicate 3 2 2 (by decide +kernel)

/-- Refusal isolating `k ≤ d`: one key past the block the prefix
caps at the block's total while the linear read runs on. -/
example : ¬ (prefixAt 4 (List.replicate 3 2) = 4 * 2) := by decide +kernel

/-! The unit family at a key: the total one inside the width, the
width binder's refusal at a key beyond it (the vacant family's
total misses the one). -/

example : sumNat (unitAt 3 1) = 1 := by decide +kernel
example : sumNat (unitAt 3 1) = 1 := sumNat_unitAt 3 1 (by decide +kernel)
example : ¬ (sumNat (unitAt 2 5) = 1) := by decide +kernel
example : dotNat [1, 2, 3] [4, 5, 6] = 32 := by decide +kernel

/-! The double count: one family's counts in the other folded at
either order, the indicator's double fold both ways. -/

example : ground.famFold Nat.add 0
    (fun a => ground.countOf a [2, 3, 3]) [1, 2, 2, 3] = 4 := by decide +kernel

example : ground.famFold Nat.add 0
    (fun s => ground.countOf s [1, 2, 2, 3]) [2, 3, 3] = 4 := by decide +kernel

example : ground.famFold Nat.add 0
      (fun a => ground.countOf a [2, 3, 3]) [1, 2, 2, 3]
    = ground.famFold Nat.add 0
      (fun s => ground.countOf s [1, 2, 2, 3]) [2, 3, 3] :=
  ground.famFold_countSwap [1, 2, 2, 3] [2, 3, 3]

/-! Two distinct keys at one value: the value's count at two or
beyond. -/

example : ground.countOf (ground.getAt 0 [5, 7, 5] 0) [5, 7, 5] = 2 := by
  decide +kernel

example : 2 ≤ ground.countOf (ground.getAt 0 [5, 7, 5] 0) [5, 7, 5] :=
  ground.countOf_two_pos 0 [5, 7, 5] 0 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- Refusal isolating `hne`: at one key read against itself the
singleton carries its value once, and the two-or-beyond read
refuses. -/
example : ¬ 2 ≤ ground.countOf 1 [1] := by decide +kernel

/-! A mapped family's count as the guarded fold over the source,
decided at one instance and applied through the theorem. -/

example : ground.countOf 4 ([1, 2, 3].map (fun x => x + x)) = 1 := by
  decide +kernel

example : ground.countOf 4 ([1, 2, 3].map (fun x => x + x))
    = ground.famFold Nat.add 0
      (fun j => if 4 = j + j then 1 else 0) [1, 2, 3] :=
  ground.countOf_map_famFold 4 (fun x => x + x) [1, 2, 3]

/-! The repeated family's counts: its own member at the repeat
count, a further letter at the fold's unit — decided at an instance
each beside the theorems' routes. -/

example : ground.countOf 7 (List.replicate 4 7) = 4 := by decide +kernel

example : ground.countOf 7 (List.replicate 4 7) = 4 :=
  ground.countOf_replicate 7 4

example : ground.countOf 5 (List.replicate 4 7) = 0 := by decide +kernel

example : ground.countOf 5 (List.replicate 4 7) = 0 :=
  ground.countOf_replicate_ne 5 7 (by decide +kernel) 4

/-! The adjacent exchange of the key list: the entry read at the
traded keys, and the exchange naming its own key. -/

example : ground.getAt 0 (ground.adjSwap 1 (List.range 4)) 2 = 1 := by
  decide +kernel

example : ground.getAt 0 (ground.adjSwap 1 (List.range 4)) 2
    = if 2 = 1 then 1 + 1 else if 2 = 1 + 1 then 1 else 2 :=
  ground.getAt_adjSwap_range 4 1 2 (by decide +kernel) (by decide +kernel)

example : (1 : Nat) = 1 :=
  ground.adjSwap_range_inj 4 1 1 (by decide +kernel) (by decide +kernel) rfl

/-- The naming's own read: two keys' exchanges of the key list
differ. -/
example : ¬ ground.adjSwap 0 (List.range 4)
    = ground.adjSwap 1 (List.range 4) := by decide +kernel

/-! The exchange's tie witness: the doubled place at the key, the
vacancy at its successor, the unit at every further place. -/

example : ground.getAt 0
    (List.replicate 1 1 ++ 2 :: 0 :: List.replicate 2 1) 2 = 0 := by
  decide +kernel

example : ground.getAt 0
      (List.replicate 1 1 ++ 2 :: 0 :: List.replicate 2 1) 2
    = if 2 = 1 then 2 else if 2 = 1 + 1 then 0 else 1 :=
  ground.getAt_swapWit 1 2 2 (by decide +kernel)

/-! The comparison counts at a stated value, the multiplicative
fold over a key list, and the prefix occupancy family, each at a
value with its refusal; the depth step's hypothesis isolated at a
depth outside the height. -/

example : ground.countAbove 1 [0, 2, 3, 1] = 2 := by decide +kernel
example : ¬ ground.countAbove 1 [0, 2, 3, 1] = 3 := by decide +kernel
example : ground.countBelow 2 [0, 2, 3, 1] = 2 := by decide +kernel
example : ¬ ground.countBelow 2 [0, 2, 3, 1] = 1 := by decide +kernel
example : ground.prodOver (fun x => x + 1) [1, 2, 3] = 24 := by decide +kernel
example : ¬ ground.prodOver (fun x => x + 1) [1, 2, 3] = 12 := by decide +kernel
example : ground.onesRows 2 3 = [1, 1, 0, 0, 0] := by decide +kernel
example : ¬ ground.onesRows 3 2 = [1, 1, 0, 0, 0] := by decide +kernel
example : ¬ ((1 : Nat) - (3 + 1) + 1 = 1 - 3) := by decide +kernel

/-! The keyed entry edit's value reads at the write and off it,
with the refusals isolating the self read's range binder, the
off-key read's distinctness binder, the exchange's distinct-keys
binder, the entry congruence's hypothesis, the total read's range
binder, and the sum distribution's entry read at each
summand. -/

example : ground.editAt (fun x => x * 2) 1 [5, 3, 4] = [5, 6, 4] := by decide +kernel

example : ground.editAt (fun x => x * 2) 3 [5, 3, 4] = [5, 3, 4] := by decide +kernel

example : ¬ (ground.getAt 0 (ground.editAt (fun x => x + 5) 3 [2]) 3
    = ground.getAt 0 [2] 3 + 5) := by decide +kernel

example : ¬ (ground.getAt 0 (ground.editAt (fun x => x + 1) 0 [7]) 0
    = ground.getAt 0 [7] 0) := by decide +kernel

example : ¬ (ground.editAt (fun x => x + 1) 0
      (ground.editAt (fun x => x - 1) 0 [0])
    = ground.editAt (fun x => x - 1) 0
      (ground.editAt (fun x => x + 1) 0 [0])) := by decide +kernel

example : ¬ (ground.editAt (fun x => x + 1) 0 [1]
    = ground.editAt (fun x => x) 0 [1]) := by decide +kernel

example : ¬ (ground.sumNat (ground.editAt (fun x => x + 5) 0 [])
      + ground.getAt 0 ([] : List Nat) 0
    = ground.sumNat [] + (ground.getAt 0 ([] : List Nat) 0 + 5)) := by decide +kernel

example : ¬ (List.zipWith (fun x y => x + y)
      (ground.editAt (fun x => x - 1) 0 [0]) [3]
    = ground.editAt (fun x => x - 1) 0
      (List.zipWith (fun x y => x + y) [0] [3])) := by decide +kernel

example : ¬ (List.zipWith (fun x y => x + y) [3]
      (ground.editAt (fun x => x - 1) 0 [0])
    = ground.editAt (fun x => x - 1) 0
      (List.zipWith (fun x y => x + y) [3] [0])) := by decide +kernel

/-! The reversal's zip kit: the componentwise walk of two
reversals is the walk's own reversal at matched lengths, the length
binder isolated at a ragged pair where the two reads differ; the
repeated family is its own reversal; and the sum's zip exchanges
its arguments at every pair, ragged pairs among them. -/

example : (List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]).reverse
    = [9, 7, 5] := by decide +kernel

example : (List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]).reverse
    = List.zipWith (fun u w => u + w) ([1, 2, 3] : List Nat).reverse
      ([4, 5, 6] : List Nat).reverse :=
  ground.reverse_zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6] rfl

example : ¬ ((List.zipWith (fun u w => u + w) [1, 2] [4, 5, 6]).reverse
    = List.zipWith (fun u w => u + w) ([1, 2] : List Nat).reverse
      ([4, 5, 6] : List Nat).reverse) := by decide +kernel

example : (List.replicate 3 (7 : Nat)).reverse = [7, 7, 7] := by decide +kernel

example : (List.replicate 3 (7 : Nat)).reverse = List.replicate 3 7 :=
  ground.reverse_replicate 3 7

example : List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]
    = [5, 7, 9] := by decide +kernel

example : List.zipWith (fun u w => u + w) [1, 2, 3] [4, 5, 6]
    = List.zipWith (fun u w => u + w) [4, 5, 6] [1, 2, 3] :=
  ground.zipWith_add_comm [1, 2, 3] [4, 5, 6]

example : List.zipWith (fun u w => u + w) [1, 2] [4, 5, 6]
    = List.zipWith (fun u w => u + w) [4, 5, 6] [1, 2] :=
  ground.zipWith_add_comm [1, 2] [4, 5, 6]

/-! The gap fold against the total: at a dominating bound the
list's gaps and its own sum exhaust the bound once per place, the
domination binder isolated at a bound the head clears, where the
truncated gaps overshoot.  Beside it the family fold dominates each
of its members, the membership binder isolated at a value beyond
the fold. -/

example : [2, 1, 0].foldl (fun acc y => acc + (3 - y)) 0 + ground.sumNat [2, 1, 0]
    = ([2, 1, 0] : List Nat).length * 3 :=
  ground.gapFold_total 3 [2, 1, 0] (by decide +kernel)

example : ¬ ([2, 1, 0].foldl (fun acc y => acc + (1 - y)) 0
    + ground.sumNat [2, 1, 0] = ([2, 1, 0] : List Nat).length * 1) := by decide +kernel

example : (5 : Nat) ≤ ground.famFold Nat.add 0 (fun n => n) [4, 5, 6] :=
  ground.famFold_mem_le (fun n => n) [4, 5, 6] 5
    (List.Mem.tail 4 (List.Mem.head [6]))

example : ¬ ((20 : Nat) ≤ ground.famFold Nat.add 0 (fun n => n) [4, 5, 6]) := by decide +kernel

/-! The matrix at an entry formula: the builder's displayed rows,
its length, row, width and entry reads decided and routed through
their theorems, the congruence at formulas agreeing on the box,
and the refusals — an off-count row or entry reads the stated
default against the formula's value, and formulas differing inside
the box build distinct matrices. -/

example : ground.matOf 2 3 (fun i j => i + 2 * j)
    = [[0, 2, 4], [1, 3, 5]] := by decide +kernel
example : (ground.matOf 2 3 (fun i j => i + 2 * j)).length = 2 :=
  ground.matOf_length 2 3 _
example : ground.getAt [] (ground.matOf 2 3 (fun i j => i + 2 * j)) 1
    = [1, 3, 5] := by decide +kernel
example : ground.getAt [] (ground.matOf 2 3 (fun i j => i + 2 * j)) 1
    = (List.range 3).map (fun j => 1 + 2 * j) :=
  ground.matOf_row [] 2 3 _ 1 (by decide +kernel)
example : (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 1).length = 3 :=
  ground.matOf_rowLength [] 2 3 _ 1 (by decide +kernel)
example : ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 1) 2 = 5 := by
  decide +kernel
example : ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 1) 2 = 5 :=
  ground.matOf_entry [] 0 2 3 _ 1 2 (by decide +kernel)
    (by decide +kernel)
example : ground.matOf 2 2 (fun i j => i + j)
    = ground.matOf 2 2 (fun i j => if i < 2 then i + j else 7) :=
  ground.matOf_congr 2 2 _ _ (fun i j hi _ => by rw [if_pos hi])
example : ground.matOf 2 2 (fun i j => i + j)
    = ground.matOf 2 2 (fun i j => if j < 2 then i + j else 9) :=
  ground.matOf_congr 2 2 _ _ (fun i j _ hj => by rw [if_pos hj])

example : ¬ (ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 2
      = (List.range 3).map (fun j => 2 + 2 * j)) := by decide +kernel
example : ¬ ((ground.getAt []
    (ground.matOf 2 3 (fun i j => i + 2 * j)) 2).length = 3) := by
  decide +kernel
example : ¬ (ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun _ _ => 7)) 1) 3 = 7) := by decide +kernel
example : ¬ (ground.getAt 0 (ground.getAt []
    (ground.matOf 2 3 (fun _ _ => 7)) 2) 0 = 7) := by decide +kernel
example : ¬ (ground.matOf 2 2 (fun i j => i + j)
    = ground.matOf 2 2 (fun i j => i * j)) := by decide +kernel

/-! The box at stated per-key bounds: its count the bounds'
successor product, and a member's count one exactly at the matched
length with every key at or below its bound — decided at an inside
list, at a list past the head bound, and at the two vacant-bound
instances where the box is the seed alone. -/

example : (ground.boxAll [2, 1]).length
    = ground.prodOver (fun x => x + 1) [2, 1] := by decide +kernel
example : (ground.boxAll [2, 1]).length
    = ground.prodOver (fun x => x + 1) [2, 1] :=
  ground.boxAll_length [2, 1]

example : ground.countOf [1, 1] (ground.boxAll [2, 1])
    = if ([1, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [1, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 := by decide +kernel
example : ground.countOf [1, 1] (ground.boxAll [2, 1])
    = if ([1, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [1, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 :=
  ground.boxAll_countOf [2, 1] [1, 1]

example : ground.countOf [3, 1] (ground.boxAll [2, 1])
    = if ([3, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [3, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 := by decide +kernel
example : ground.countOf [3, 1] (ground.boxAll [2, 1])
    = if ([3, 1] : List Nat).length = ([2, 1] : List Nat).length
        ∧ (∀ i, i < ([2, 1] : List Nat).length →
            ground.getAt 0 [3, 1] i ≤ ground.getAt 0 [2, 1] i)
      then 1 else 0 :=
  ground.boxAll_countOf [2, 1] [3, 1]

example : ground.boxAll [] = [[]] := by decide +kernel
example : (ground.boxAll ([] : List Nat)).length
    = ground.prodOver (fun x => x + 1) ([] : List Nat) :=
  ground.boxAll_length []
example : ground.boxAll [0] = [[0]] := by decide +kernel
example : (ground.boxAll [0]).length
    = ground.prodOver (fun x => x + 1) [0] :=
  ground.boxAll_length [0]
example : ground.countOf [1] (ground.boxAll [0])
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

example : (3 : Pos) * ((5 : Pos) + 2) + 2 * 2 = 5 * 5 := by
  decide +kernel

example : (3 : Pos) * ((5 : Pos) + 2) + 2 * 2 = 5 * 5 :=
  Pos.sq_split 2 3 5 (by decide +kernel)

example : Pos.pow (3 : Pos) 3
    ≤ Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (3 : Pos) 2 := by
  decide +kernel

example : Pos.pow (3 : Pos) 3
    ≤ Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (3 : Pos) 2 :=
  Pos.bernoulli_le 1 2 3 (by decide +kernel) 2

example : Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (2 : Pos) 2
    ≤ Pos.pow (3 : Pos) 3 := by
  decide +kernel

example : Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (2 : Pos) 2
    ≤ Pos.pow (3 : Pos) 3 :=
  Pos.bernoulli_ge 1 2 3 (by decide +kernel) 2

/-- The Bernoulli display's two sides carry their own directions: the
lower side's display read upward refuses at the same data, the
datum's power `27` above the gap's power joined to the count's
multiple, `8 + 12 = 20`. -/
example : ¬ (Pos.pow (3 : Pos) 3
    ≤ Pos.pow (2 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (2 : Pos) 2) := by
  decide +kernel

/-! The written key's read: a write keeps the family's length, the
written key reads the written value, and every further key is
kept — decided at an in-range write and at a key beyond the
family, each landed by the theorem route. -/

example : (([5, 6, 7] : List Nat).set 1 9).length
    = ([5, 6, 7] : List Nat).length := by decide +kernel

example : (([5, 6, 7] : List Nat).set 4 9).length
    = ([5, 6, 7] : List Nat).length := by decide +kernel

example : (([5, 6, 7] : List Nat).set 4 9).length
    = ([5, 6, 7] : List Nat).length := length_set 9 [5, 6, 7] 4

example : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 1 = 9 := by
  decide +kernel

example : getAt 0 (([5, 6, 7] : List Nat).set 0 9) 0 = 9 := by
  decide +kernel

example : getAt 0 (([5, 6, 7] : List Nat).set 2 9) 2 = 9 :=
  getAt_set_self 0 9 [5, 6, 7] 2 (by decide +kernel)

/-- The write's key binder is load-bearing: at a key beyond the
family the write is a no-op and the key reads the vacant
default. -/
example : ¬ (getAt 0 (([5, 6, 7] : List Nat).set 4 9) 4 = 9) := by
  decide +kernel

example : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 2 = 7 := by
  decide +kernel

example : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 5 = 0 := by
  decide +kernel

example : getAt 0 (([5, 6, 7] : List Nat).set 1 9) 0
    = getAt 0 ([5, 6, 7] : List Nat) 0 :=
  getAt_set_ne 0 [5, 6, 7] 1 0 9 (by decide +kernel)

/-! The two cleared displays' join binders refused: at the parted
join each display parts. -/

example : ¬ ((1 : Pos) + 1 = 5) := by decide +kernel
example : ¬ ((1 : Pos) * ((5 : Pos) + 1) + 1 * 1 = 5 * 5) := by
  decide +kernel
example : ¬ (Pos.pow (5 : Pos) 3
    ≤ Pos.pow (1 : Pos) 3 + posOfSucc 2 * 1 * Pos.pow (5 : Pos) 2) := by
  decide +kernel

/-! The Pascal count and the binomial theorem at the pair carrier. -/

example : pasc 4 2 = 6 := by decide +kernel
example : pasc 6 3 = 20 := by decide +kernel

example : pasc 5 0 = 1 := by decide +kernel
example : pasc 5 5 = 1 := by decide +kernel
example : pasc 3 5 = 0 := by decide +kernel

example : pasc 7 7 = 1 := by decide +kernel
example : pasc 7 7 = 1 := pasc_self 7

example : pasc 2 9 = 0 := by decide +kernel
example : pasc 2 9 = 0 := pasc_beyond 2 9 (by decide +kernel)

example : (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (bsum (fun t => BPair.ofNat (pasc 3 t)
      * (bpow (BPair.ofNat 2) t * bpow (BPair.ofNat 3) (3 - t)))
      (List.range 4)) := by decide +kernel

example : (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (bsum (fun t => BPair.ofNat (pasc 3 t)
      * (bpow (BPair.ofNat 2) t * bpow (BPair.ofNat 3) (3 - t)))
      (List.range 4)) :=
  bpow_binom (BPair.ofNat 2) (BPair.ofNat 3) 3

example : (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (BPair.ofNat 125) := by decide +kernel

/-! The partner-signed instance: the second member enters memberwise
swapped and the square reads the two members' gap against itself. -/

example : (bpow (BPair.ofNat 2 + (BPair.ofNat 3).swap) 2).oneValue
    (bsum (fun t => BPair.ofNat (pasc 2 t)
      * (bpow (BPair.ofNat 2) t * bpow ((BPair.ofNat 3).swap) (2 - t)))
      (List.range 3)) := by decide +kernel

example : (bpow (BPair.ofNat 2 + (BPair.ofNat 3).swap) 2).oneValue
    (bsum (fun t => BPair.ofNat (pasc 2 t)
      * (bpow (BPair.ofNat 2) t * bpow ((BPair.ofNat 3).swap) (2 - t)))
      (List.range 3)) :=
  bpow_binom (BPair.ofNat 2) ((BPair.ofNat 3).swap) 2

example : (bpow (BPair.ofNat 2 + (BPair.ofNat 3).swap) 2).oneValue
    (BPair.ofNat 1) := by decide +kernel

/-- The second power's key binder is load-bearing: read at the first
member's own key the fold sums to 343 against the power's 125. -/
example : ¬ (bpow (BPair.ofNat 2 + BPair.ofNat 3) 3).oneValue
    (bsum (fun t => BPair.ofNat (pasc 3 t)
      * (bpow (BPair.ofNat 2) t * bpow (BPair.ofNat 3) t))
      (List.range 4)) := by decide +kernel
