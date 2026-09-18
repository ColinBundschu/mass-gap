import MassGap.Cornermoment
import MassGapChecks.Cornerkey
/-!
The check module for `lem:cornerkey`'s moment tier.  The near scale: the
stated coefficient's read at the power three and the bit count five,
refused at the power five; the key comparison at the power two and the
unit data; the weight's read at the power three, the scale `[1 : 2]`,
the coefficient `48` and the moment `13824` at the tie, each decided and
through its theorem with the moment's binder refused at the parting
value, and the near read at the near scale `48` beside it.  The near
mass at one plaquette: the chain `6, 4`, the key nought, the exponent
nought, the mass's second member `24`, the tolerance `8`, the clearing
`12` under `4 · 6`, the raised power's binder refused at the clearing
`25`.  The tier's reads at the moments' key read's data, the scale
`[1 : 5]`, the mass `[1 : 1]`, the bit count one and the near scale
`12` at five plaquettes and the profile square `10`, the unit member
reads and the deficits' and mode weight's pairs `3` and `26`: the unit
weight's near-scale reads at both powers, the deficit cell's read, the
remainder cell's two reads, the mode square's lower weight, the
variance floor with its side, the mode mean's read, the mode weight's
square moment, its leading member and the deficits' fold at it, each
decided and through its theorem with one datum forged so that a
load-bearing binder refuses and the conclusion parts (`A` at `near_read_one`, `A` at `near_read_two`, `mD` at `deficit_read` with its two cell comparisons each refused alone, `r1` at `remainder_one` with its two cell comparisons each refused alone, `r2` at `remainder_two` with its two cell comparisons each refused alone, `Del` at `mode_lower`, `D` at `variance_floor`, `muQ` at `variance_side`, `muQ` at `mode_mean_read`, `mZD2` at `weight_square`, `T3l` at `weight_lead` with the variance side refused alone, `mZD` at `weight_deficit`);
and the moments' key read whole at those data, its binders its
components' own.  The tail read at the four-link unit Tail (the
profile's count vacant, four links, every further read one): the key's
list at the halving `152`, the least, the bit count `6761` and the near
scale `324720`, the unit's moment `2³⁰⁴`, the mode square's moment
`2¹⁵²`, the near mass's chain constant at the clearing with the
support weight one (the chain's positivity and convexity the constant's
own reads at every index), and the two reads
at the unit, the reads' sum under the floor `[10⁷ : 1]`'s multiple of the
scale `[1 : 2¹⁵²]` through the theorem, and its join refuses at the
excess one, the excess identity parting.  The key read holds at the
mass `[1 : 2]` as well, the bit count two and the near scale `32`, and
the near read at the mass's second member two; and the cell
comparisons refuse one by one at forged data, the conclusion parting
with each.
-/

namespace cornerkey.cornermoment

open ground cornerkey

open cornerkey (tFour)

theorem pin1 : Tail.pos tFour := by decide +kernel

-- the stated near scale's read (`near_scale_stated`) at the power three and
-- the bit count five: `2 · 6 · 8 = 96` under `48 · 9 = 432`, decided and
-- through the theorem; the power's binder refuses at five, `2 · 120 · 6 = 1440`
-- beyond `48 · 5 = 240`
theorem pin2 : 2 * factorial 3 * (3 + 5) ≤ 48 * (4 + 5) := by decide +kernel
theorem pin3 : 2 * factorial 3 * (3 + 5) ≤ 48 * (4 + 5) := near_scale_stated 3 5 (by decide)
theorem pin4 : ¬ (2 * factorial 5 * (5 + 1) ≤ 48 * (4 + 1)) := by decide +kernel

-- near_scale_key: the power two, the bit count one and the unit data: `3! · 1 ≤ 12`
theorem pin5 : BPair.ofNat (factorial (2 + 1)) * (bpow (BPair.ofNat 1) 2 * (BPair.ofNat 1)) ≤ bpow (BPair.ofNat (2 * factorial 2 * (2 + 1))) 1 * (BPair.ofNat 1) := by decide +kernel
theorem pin6 : BPair.ofNat (factorial (2 + 1)) * (bpow (BPair.ofNat 1) 2 * (BPair.ofNat 1)) ≤ bpow (BPair.ofNat (2 * factorial 2 * (2 + 1))) 1 * (BPair.ofNat 1) :=
  near_scale_key 2 1 (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- at E = 2 the binder `hbit` refuses and the conclusion parts
theorem pin7 : ¬ (bpow (BPair.ofNat 2) 2 * (BPair.ofNat 1) ≤ bpow (BPair.ofNat 2) 1 * (BPair.ofNat 1)) := by decide +kernel
theorem pin8 : ¬ (BPair.ofNat (factorial (2 + 1)) * (bpow (BPair.ofNat 2) 2 * (BPair.ofNat 1)) ≤ bpow (BPair.ofNat (2 * factorial 2 * (2 + 1))) 1 * (BPair.ofNat 1)) := by decide +kernel

-- near_scale_moment: the power three, the bit count one, the scale `[1 : 2]`, the near scale's coefficient `48 = 2 · 3! · 4` and the moment `13824` at the tie: `13824 · 8 ≤ 2 · 48³`
theorem pin9 : (BPair.ofNat 13824) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow ((BPair.ofNat 48) * (BPair.ofNat 1) * (BPair.ofNat 1)) 3 * (BPair.ofNat 1)) := by decide +kernel
theorem pin10 : (BPair.ofNat 13824) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow ((BPair.ofNat 48) * (BPair.ofNat 1) * (BPair.ofNat 1)) 3 * (BPair.ofNat 1)) :=
  near_scale_moment (BPair.ofNat 13824) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
  (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 48) (BPair.ofNat 1) (BPair.ofNat 1) 3 1
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)
-- at A = 138240 the binder `hA` refuses and the conclusion parts
theorem pin11 : ¬ ((BPair.ofNat 138240) * bpow ((BPair.ofNat 48) * (BPair.ofNat 1) * (BPair.ofNat 1)) 1 * bpow (BPair.ofNat 2) 3 ≤ bpow ((BPair.ofNat 48) * (BPair.ofNat 1) * (BPair.ofNat 1)) (3 + 1) * (BPair.ofNat 1) + bpow (BPair.ofNat 2) (3 + 1) * (BPair.ofNat 1)) := by decide +kernel
theorem pin12 : ¬ ((BPair.ofNat 138240) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow ((BPair.ofNat 48) * (BPair.ofNat 1) * (BPair.ofNat 1)) 3 * (BPair.ofNat 1))) := by decide +kernel

-- near_read: the same data at the near scale `48` and the unit clearing
theorem pin13 : (BPair.ofNat 13824) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 48) 3 * bpow (BPair.ofNat 1) 3 * (BPair.ofNat 1)) := by decide +kernel
theorem pin14 : (BPair.ofNat 13824) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 48) 3 * bpow (BPair.ofNat 1) 3 * (BPair.ofNat 1)) :=
  near_read (BPair.ofNat 13824) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2)
  (BPair.ofNat 1) (BPair.ofNat 48) (BPair.ofNat 48) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat
  1) 3 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- at K = 24 the binder `hK` refuses and the conclusion parts
theorem pin15 : ¬ (((BPair.ofNat 48) * (BPair.ofNat 1)).oneValue (BPair.ofNat 24)) := by decide +kernel
theorem pin16 : ¬ ((BPair.ofNat 13824) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 24) 3 * bpow (BPair.ofNat 1) 3 * (BPair.ofNat 1))) := by decide +kernel
-- near_read at the mass's second member two, the power three, the bit count
-- three, the scale `[1 : 2]` and the near scale `72 · 2 = 144`
theorem pin73 : (BPair.ofNat 373248) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 144) 3 * bpow (BPair.ofNat 1) 3 * (BPair.ofNat 1)) := by decide +kernel
theorem pin74 : (BPair.ofNat 373248) * bpow (BPair.ofNat 2) 3 ≤ BPair.ofNat 2 * (bpow (BPair.ofNat 144) 3 * bpow (BPair.ofNat 1) 3 * (BPair.ofNat 1)) :=
  near_read (BPair.ofNat 373248) (BPair.ofNat 1) (BPair.ofNat 720) (BPair.ofNat 1) (BPair.ofNat
  2) (BPair.ofNat 2) (BPair.ofNat 72) (BPair.ofNat 144) (BPair.ofNat 1) (BPair.ofNat 1)
  (BPair.ofNat 1) 3 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)


-- the near mass (`near_mass`) at one plaquette, the concentration key
-- nought, the exponent nought and the coefficient two: the return read's
-- chain `6, 4` (decreasing, the convexity read vacant at the key nought),
-- its evaluation `6` at the key, the clearing `12` at or below `W₊ = 3`
-- against the raised power's `4`, the deficit's read `4 = 2 · (6 − 4)`, the
-- tolerance `τ_D = 8` at the mass's second member `24` and the side nought,
-- the key comparison `3 · 8 ≤ 1 · 24`, the support weight `W_k = 2` and the
-- unit's moment `6`: `12 ≤ 4 · 6`, decided and through the theorem; at the
-- clearing `25` the raised power's binder refuses and the conclusion parts,
-- `25` beyond `24`
private def bChain : Nat → Nat → BPair := fun _ j => BPair.ofNat (ground.getAt 1 [6, 4] j)
theorem pin17 : BPair.ofNat 12 ≤ BPair.ofNat (2 * 2 * 0 ^ 0) * BPair.ofNat 6 := by decide +kernel
theorem pin18 : BPair.ofNat 12 ≤ BPair.ofNat (2 * 2 * 0 ^ 0) * BPair.ofNat 6 :=
  near_mass 1 0 0 2 bChain (fun _ => BPair.ofNat 4) (BPair.ofNat 12) (BPair.ofNat 6) (BPair.ofNat 3)
    (BPair.ofNat 2) (BPair.ofNat 6) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 24) BPair.unit
    (BPair.ofNat 1) (BPair.ofNat 8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (fun _ _ i hi => absurd hi (Nat.not_succ_le_zero i))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin19 : ¬ (∀ p, p < 1 → BPair.ofNat 25 ≤ BPair.ofNat 3 * bChain p (0 + 1)) := by decide +kernel
theorem pin20 : ¬ (BPair.ofNat 25 ≤ BPair.ofNat (2 * 2 * 0 ^ 0) * BPair.ofNat 6) := by decide +kernel

-- near_read_one: the unit weight at the key read's data below
theorem pin21 : (BPair.ofNat 1) * (BPair.ofNat 5) ≤ BPair.ofNat 2 * (BPair.ofNat 12) * (BPair.ofNat 1) * (BPair.ofNat 1) := by decide +kernel
theorem pin22 : (BPair.ofNat 1) * (BPair.ofNat 5) ≤ BPair.ofNat 2 * (BPair.ofNat 12) * (BPair.ofNat 1) * (BPair.ofNat 1) :=
  near_read_one (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit (BPair.ofNat 1) (BPair.ofNat 5)
  (BPair.ofNat 1) (BPair.ofNat 12) (BPair.ofNat 12) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat
  1) 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- at A = 6 the binder `hA` refuses and the conclusion parts
theorem pin23 : ¬ ((BPair.ofNat 6) * bpow ((BPair.ofNat 12) * (BPair.ofNat 1) * (BPair.ofNat 1)) 1 * (BPair.ofNat 5) ≤ bpow ((BPair.ofNat 12) * (BPair.ofNat 1) * (BPair.ofNat 1)) (1 + 1) * (BPair.ofNat 1) + bpow (BPair.ofNat 5) (1 + 1) * BPair.unit) := by decide +kernel
theorem pin24 : ¬ ((BPair.ofNat 6) * (BPair.ofNat 5) ≤ BPair.ofNat 2 * (BPair.ofNat 12) * (BPair.ofNat 1) * (BPair.ofNat 1)) := by decide +kernel

-- near_read_two: the unit weight at the second power
theorem pin25 : BPair.unit * ((BPair.ofNat 5) * (BPair.ofNat 5)) ≤ BPair.ofNat 2 * ((BPair.ofNat 12) * (BPair.ofNat 12)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) := by decide +kernel
theorem pin26 : BPair.unit * ((BPair.ofNat 5) * (BPair.ofNat 5)) ≤ BPair.ofNat 2 * ((BPair.ofNat 12) * (BPair.ofNat 12)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) :=
  near_read_two BPair.unit (BPair.ofNat 1) BPair.unit (BPair.ofNat 1) (BPair.ofNat 5)
  (BPair.ofNat 1) (BPair.ofNat 12) (BPair.ofNat 12) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat
  1) 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- at A = 100 the binder `hA` refuses and the conclusion parts
theorem pin27 : ¬ ((BPair.ofNat 100) * bpow ((BPair.ofNat 12) * (BPair.ofNat 1) * (BPair.ofNat 1)) 1 * ((BPair.ofNat 5) * (BPair.ofNat 5)) ≤ bpow ((BPair.ofNat 12) * (BPair.ofNat 1) * (BPair.ofNat 1)) (2 + 1) * (BPair.ofNat 1) + bpow (BPair.ofNat 5) (2 + 1) * BPair.unit) := by decide +kernel
theorem pin28 : ¬ ((BPair.ofNat 100) * ((BPair.ofNat 5) * (BPair.ofNat 5)) ≤ BPair.ofNat 2 * ((BPair.ofNat 12) * (BPair.ofNat 12)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1)) := by decide +kernel

-- deficit_read: the deficits' fold `μ[D] ≤ C_D #p η μ[1]` at the key read's data
theorem pin29 : (BPair.ofNat 1) * (BPair.ofNat 5) ≤ (BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.ofNat 1) * (BPair.ofNat 1) := by decide +kernel
theorem pin30 : (BPair.ofNat 1) * (BPair.ofNat 5) ≤ (BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.ofNat 1) * (BPair.ofNat 1) :=
  deficit_read (BPair.ofNat 1) BPair.unit (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
  BPair.unit (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 1) (BPair.ofNat 1)
  (BPair.ofNat 1) BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit (BPair.ofNat 1)
  (BPair.ofNat 12) (BPair.ofNat 5) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)
-- at mD = 6 the binder `hdef` refuses and the conclusion parts
theorem pin31 : ¬ (BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 6) ≤ (BPair.ofNat 1) * (BPair.ofNat 2) + BPair.ofNat 2 * (BPair.ofNat 1) * BPair.unit * BPair.unit) := by decide +kernel
theorem pin32 : ¬ ((BPair.ofNat 6) * (BPair.ofNat 5) ≤ (BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.ofNat 1) * (BPair.ofNat 1)) := by decide +kernel
-- at the scale `[1 : 10007]`, `C₁ = ϱ₁ = 1000` and four plaquettes the deficit
-- cell's first comparison `hD1` refuses alone and the conclusion parts
theorem pin75 : ¬ (BPair.ofNat 2 * (BPair.ofNat 4) * (BPair.ofNat 1) * (BPair.ofNat 1000) * (BPair.ofNat 1000) ≤ (BPair.ofNat 1) * (BPair.ofNat 10007)) := by decide +kernel
theorem pin76 : ¬ ((BPair.ofNat 1) * (BPair.ofNat 10007) ≤ (BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 4) * (BPair.ofNat 1) * (BPair.ofNat 1)) := by decide +kernel
-- at forged data (the scale `[1 : 103]`, eleven plaquettes, `C₁ = 10004`,
-- `T_R = 9001`, the clearing `1101`, the near scale `907`) the deficit cell's
-- second comparison `hD2` refuses alone and the conclusion parts
theorem pin81 : ¬ ((BPair.ofNat 1) * ((BPair.ofNat 907) * (BPair.ofNat 907)) * (BPair.ofNat 8 * (BPair.ofNat 1101) * ((BPair.ofNat 10004) * (BPair.ofNat 10004) * (BPair.ofNat 9001) * (BPair.ofNat 9001)) + BPair.ofNat 4 * (BPair.ofNat 1101) * (BPair.ofNat 12) + BPair.ofNat 4 * (BPair.ofNat 11) * (BPair.ofNat 110)) ≤ (BPair.ofNat 11) * (BPair.ofNat 1101) * (BPair.ofNat 103)) := by decide +kernel
theorem pin82 : ¬ ((BPair.ofNat 200) * (BPair.ofNat 103) ≤ (BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) + BPair.ofNat 1) * (BPair.ofNat 11) * (BPair.ofNat 1) * (BPair.ofNat 106)) := by decide +kernel



-- remainder_one: the first identity's remainder at the key read's data
theorem pin33 : BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag BPair.unit ≤ (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1) := by decide +kernel
theorem pin34 : BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag BPair.unit ≤ (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1) :=
  remainder_one BPair.unit BPair.unit BPair.unit (BPair.ofNat 1) BPair.unit (BPair.ofNat 1)
  BPair.unit (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 12) (BPair.ofNat 1)
  BPair.unit BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 30) (BPair.ofNat
  3) (BPair.ofNat 10) (BPair.ofNat 1) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)
-- at r1 = 1 the binder `hr1` refuses and the conclusion parts
theorem pin35 : ¬ (windowsep.mag (BPair.ofNat 1) ≤ BPair.unit * (BPair.ofNat 1) + BPair.unit) := by decide +kernel
theorem pin36 : ¬ (BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag (BPair.ofNat 1) ≤ (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1)) := by decide +kernel
-- at `a₁ = 10`, the remainder `r₁ = 10` and `ν[Q] = 2` the remainder cell's second comparison `hR2` refuses alone and the conclusion parts
theorem pin83 : ¬ (BPair.ofNat 32 * (BPair.ofNat 10) * (BPair.ofNat 12) * (BPair.ofNat 1) * ((BPair.ofNat 1) + BPair.ofNat 2) ≤ (BPair.ofNat 1) * (BPair.ofNat 10) * (BPair.ofNat 5)) := by decide +kernel
theorem pin84 : ¬ (BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag (BPair.ofNat 10) ≤ (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1)) := by decide +kernel

-- at `C_W = T_R = 1`, the remainder `r₁ = 10` at the deviation `X = 10`, `Y = 1`, `ν[Q] = 2`, `ν[D²] = 1` and `μ[D²] = 1` the remainder cell's first comparison `hR1` refuses alone and the conclusion parts
theorem pin85 : ¬ (BPair.ofNat 1024 * (((BPair.ofNat 1) + BPair.ofNat 2) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (BPair.ofNat 16 * (((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1))) * ((BPair.ofNat 12) * (BPair.ofNat 12)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 10) * (BPair.ofNat 1) * (BPair.ofNat 5) + BPair.ofNat 2 * BPair.unit * (BPair.ofNat 12) * ((BPair.ofNat 1) * (BPair.ofNat 1))) + BPair.ofNat 64 * (((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1))) * ((BPair.ofNat 12) * (BPair.ofNat 12) * (BPair.ofNat 12) * (BPair.ofNat 12)) * ((BPair.ofNat 1) * (BPair.ofNat 1))) ≤ BPair.ofNat 4 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 10) * (BPair.ofNat 10)) * ((BPair.ofNat 5) * (BPair.ofNat 5))) := by decide +kernel
theorem pin86 : ¬ (BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag (BPair.ofNat 10) ≤ (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1)) := by decide +kernel


-- remainder_two: the second identity's remainder at the key read's data
theorem pin37 : BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag BPair.unit ≤ BPair.ofNat 3 * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1) := by decide +kernel
theorem pin38 : BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag BPair.unit ≤ BPair.ofNat 3 * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1) :=
  remainder_two BPair.unit BPair.unit BPair.unit BPair.unit (BPair.ofNat 3) BPair.unit
  (BPair.ofNat 1) BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 12)
  (BPair.ofNat 1) BPair.unit BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat
  30) (BPair.ofNat 3) (BPair.ofNat 10) (BPair.ofNat 1) BPair.unit BPair.unit (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)
-- at r2 = 5 the binder `hr2` refuses and the conclusion parts
theorem pin39 : ¬ (windowsep.mag (BPair.ofNat 5) ≤ BPair.unit * BPair.unit + windowsep.mag BPair.unit + BPair.unit) := by decide +kernel
theorem pin40 : ¬ (BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag (BPair.ofNat 5) ≤ BPair.ofNat 3 * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1)) := by decide +kernel
-- at `a₁ = 10`, `μ[QD] = 1`, the remainder `r₂ = 10` and `ν[Q²] = 4` the remainder cell's third comparison `hR3` refuses alone and the conclusion parts
theorem pin87 : ¬ (BPair.ofNat 8 * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 2 * (BPair.ofNat 10) * (BPair.ofNat 1) * (BPair.ofNat 10) + BPair.ofNat 16 * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * BPair.unit * BPair.unit * BPair.unit * BPair.unit) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (BPair.ofNat 12) * (BPair.ofNat 1) ≤ (BPair.ofNat 1) * (BPair.ofNat 1) * ((BPair.ofNat 10) * (BPair.ofNat 10)) * (BPair.ofNat 5)) := by decide +kernel
theorem pin88 : ¬ (BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag (BPair.ofNat 10) ≤ BPair.ofNat 3 * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1)) := by decide +kernel

-- at `C_W = T_R = 1`, the remainder `r₂ = 10` at the deviation `X = 10`, `Y = 1`, `ν[Q²] = 4`, `ν[QD²] = 1` and `μ[QD²] = 1` the remainder cell's fourth comparison `hR4` refuses alone and the conclusion parts
theorem pin89 : ¬ (BPair.ofNat 1088 * (((BPair.ofNat 1) + BPair.ofNat 2) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1))) * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * ((BPair.ofNat 10) * (BPair.ofNat 10)) * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1) * (BPair.ofNat 5) + BPair.ofNat 1024 * (((BPair.ofNat 1) + BPair.ofNat 2) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1))) * (BPair.ofNat 2 * BPair.unit * (BPair.ofNat 1) * (BPair.ofNat 10) + BPair.ofNat 16 * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * BPair.unit * BPair.unit) * ((BPair.ofNat 1) + BPair.ofNat 2)) * ((BPair.ofNat 12) * (BPair.ofNat 12) * (BPair.ofNat 12)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) + BPair.ofNat 4096 * (((BPair.ofNat 1) + BPair.ofNat 2) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1))) * (BPair.ofNat 1) * (BPair.ofNat 10) * ((BPair.ofNat 12) * (BPair.ofNat 12) * (BPair.ofNat 12) * (BPair.ofNat 12)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) ≤ (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * ((BPair.ofNat 10) * (BPair.ofNat 10) * (BPair.ofNat 10)) * ((BPair.ofNat 5) * (BPair.ofNat 5))) := by decide +kernel
theorem pin90 : ¬ (BPair.ofNat 16 * (BPair.ofNat 3) * windowsep.mag (BPair.ofNat 10) ≤ BPair.ofNat 3 * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1)) := by decide +kernel


-- mode_lower: the mode square's lower weight at the key read's data
theorem pin41 : (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 10) ≤ BPair.ofNat 4 * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 5) * (BPair.ofNat 1) * (BPair.ofNat 1) := by decide +kernel
theorem pin42 : (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 10) ≤ BPair.ofNat 4 * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 5) * (BPair.ofNat 1) * (BPair.ofNat 1) :=
  mode_lower (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
  (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 30) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat
  1) (BPair.ofNat 10) (BPair.ofNat 1) BPair.unit (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)
-- at Del = 10 the binder `hvth` refuses and the conclusion parts
theorem pin43 : ¬ ((BPair.ofNat 10) ≤ (BPair.ofNat 1) * (BPair.ofNat 1)) := by decide +kernel
theorem pin44 : ¬ ((BPair.ofNat 10) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 10) ≤ BPair.ofNat 4 * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 5) * (BPair.ofNat 1) * (BPair.ofNat 1)) := by decide +kernel

-- variance_floor: the variance floor at the key read's data
theorem pin45 : BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1) ≤ BPair.ofNat 8 * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 2) := by decide +kernel
theorem pin46 : BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1) ≤ BPair.ofNat 8 * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 2) :=
  variance_floor (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1)
  (BPair.ofNat 5) (BPair.ofNat 30) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit
  BPair.unit (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- at D = 1 the binder `hD` refuses and the conclusion parts
theorem pin47 : ¬ (((BPair.ofNat 1) * (BPair.ofNat 1)).oneValue ((BPair.ofNat 3) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 1)).swap)) := by decide +kernel
theorem pin48 : ¬ (BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 1) ≤ BPair.ofNat 8 * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 1)) := by decide +kernel

-- variance_side: the variance floor's side at the key read's data
theorem pin49 : BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 10) * (BPair.ofNat 1) ≤ BPair.ofNat 4 * (BPair.ofNat 5) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 2) := by decide +kernel
theorem pin50 : BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 10) * (BPair.ofNat 1) ≤ BPair.ofNat 4 * (BPair.ofNat 5) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 2) :=
  variance_side (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 30)
  (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 10) (BPair.ofNat 1) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)
-- at muQ = 6 the binder `hvf` refuses and the conclusion parts
theorem pin51 : ¬ (BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 30) * (BPair.ofNat 6) ≤ BPair.ofNat 8 * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 2)) := by decide +kernel
theorem pin52 : ¬ (BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 10) * (BPair.ofNat 6) ≤ BPair.ofNat 4 * (BPair.ofNat 5) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 2)) := by decide +kernel

-- mode_mean_read: the mode mean's read at the key read's data
theorem pin53 : (BPair.ofNat 1) * (BPair.ofNat 1) ≤ (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 2) := by decide +kernel
theorem pin54 : (BPair.ofNat 1) * (BPair.ofNat 1) ≤ (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 2) :=
  mode_mean_read (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1)
  (BPair.ofNat 5) (BPair.ofNat 30) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- at muQ = 2 the binder `hle` refuses and the conclusion parts
theorem pin55 : ¬ ((BPair.ofNat 2) ≤ (BPair.ofNat 1)) := by decide +kernel
theorem pin56 : ¬ ((BPair.ofNat 2) * (BPair.ofNat 2) ≤ (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 2)) := by decide +kernel

-- weight_square: the mode weight's square moment at the key read's data
theorem pin57 : BPair.unit * ((BPair.ofNat 5) * (BPair.ofNat 5)) ≤ BPair.ofNat 4 * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 2) := by decide +kernel
theorem pin58 : BPair.unit * ((BPair.ofNat 5) * (BPair.ofNat 5)) ≤ BPair.ofNat 4 * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 2) :=
  weight_square BPair.unit (BPair.ofNat 1) BPair.unit (BPair.ofNat 1) (BPair.ofNat 3)
  (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 12) (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat
  1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)
-- at mZD2 = 10000 the binder `hZ` refuses and the conclusion parts
theorem pin59 : ¬ ((BPair.ofNat 10000) * ((BPair.ofNat 1) * (BPair.ofNat 1)) ≤ BPair.ofNat 2 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) + BPair.ofNat 2 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * BPair.unit) := by decide +kernel
theorem pin60 : ¬ ((BPair.ofNat 10000) * ((BPair.ofNat 5) * (BPair.ofNat 5)) ≤ BPair.ofNat 4 * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 2)) := by decide +kernel

-- weight_lead: the mode weight identity's leading member at the key read's data
theorem pin61 : (BPair.ofNat 5) * windowsep.mag (BPair.ofNat 8).swap ≤ (BPair.ofNat 2) * (BPair.ofNat 4 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 5) + BPair.ofNat 13 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 12) * (BPair.ofNat 1) + BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * (BPair.ofNat 1)) := by decide +kernel
theorem pin62 : (BPair.ofNat 5) * windowsep.mag (BPair.ofNat 8).swap ≤ (BPair.ofNat 2) * (BPair.ofNat 4 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 5) + BPair.ofNat 13 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 12) * (BPair.ofNat 1) + BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * (BPair.ofNat 1)) :=
  weight_lead (BPair.ofNat 8).swap (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat
  1) BPair.unit BPair.unit BPair.unit BPair.unit (BPair.ofNat 3) (BPair.ofNat 1) BPair.unit
  (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat
  12) (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 30) (BPair.ofNat 3) (BPair.ofNat 10)
  (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 10) (BPair.ofNat
  1) BPair.unit BPair.unit (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel)
-- at T3l = 9992 the binder `hF` refuses and the conclusion parts
theorem pin63 : ¬ (((BPair.ofNat 9992) * (BPair.ofNat 1)).oneValue (BPair.ofNat 4 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 3)).swap))) := by decide +kernel
theorem pin64 : ¬ ((BPair.ofNat 5) * windowsep.mag (BPair.ofNat 9992) ≤ (BPair.ofNat 2) * (BPair.ofNat 4 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 5) + BPair.ofNat 13 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 12) * (BPair.ofNat 1) + BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * (BPair.ofNat 1))) := by decide +kernel
-- at `|W|² = 1000`, `μ[Y] = 201`, the deviation `2000` at `ν[D] = 2` and the
-- leading member `792` the variance side `hvs` refuses alone and the
-- conclusion parts
theorem pin91 : ¬ (BPair.ofNat 5 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1000) * (BPair.ofNat 1) ≤ BPair.ofNat 4 * (BPair.ofNat 5) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 2)) := by decide +kernel
theorem pin92 : ¬ ((BPair.ofNat 5) * windowsep.mag (BPair.ofNat 792) ≤ (BPair.ofNat 2) * (BPair.ofNat 4 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 5) + BPair.ofNat 13 * (BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 12) * (BPair.ofNat 1) + BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * (BPair.ofNat 1))) := by decide +kernel


-- weight_deficit: the deficits' fold at the mode weight at the key read's data
theorem pin65 : (BPair.ofNat 1) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) ≤ ((BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 5) + BPair.ofNat 8 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (BPair.ofNat 1) * (BPair.ofNat 5) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) + (BPair.ofNat 4 * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) + (BPair.ofNat 26 * (BPair.ofNat 5) * (BPair.unit * BPair.unit) * BPair.unit * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1) + BPair.ofNat 26 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1)) * (BPair.ofNat 12) + (BPair.ofNat 32 * (BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.unit * BPair.unit) * (BPair.unit * BPair.unit) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * (BPair.ofNat 1) + (BPair.ofNat 8 * (BPair.ofNat 1) * (BPair.ofNat 1) * BPair.unit + BPair.ofNat 8 * BPair.unit) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1))) * ((BPair.ofNat 12) * (BPair.ofNat 12))) * ((BPair.ofNat 1) * (BPair.ofNat 1))) * (BPair.ofNat 2) := by decide +kernel
theorem pin66 : (BPair.ofNat 1) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) ≤ ((BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 5) + BPair.ofNat 8 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (BPair.ofNat 1) * (BPair.ofNat 5) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) + (BPair.ofNat 4 * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) + (BPair.ofNat 26 * (BPair.ofNat 5) * (BPair.unit * BPair.unit) * BPair.unit * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1) + BPair.ofNat 26 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1)) * (BPair.ofNat 12) + (BPair.ofNat 32 * (BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.unit * BPair.unit) * (BPair.unit * BPair.unit) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * (BPair.ofNat 1) + (BPair.ofNat 8 * (BPair.ofNat 1) * (BPair.ofNat 1) * BPair.unit + BPair.ofNat 8 * BPair.unit) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1))) * ((BPair.ofNat 12) * (BPair.ofNat 12))) * ((BPair.ofNat 1) * (BPair.ofNat 1))) * (BPair.ofNat 2) :=
  weight_deficit (BPair.ofNat 1) BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 1)
  BPair.unit BPair.unit (BPair.ofNat 8).swap BPair.unit (BPair.ofNat 1) (BPair.ofNat 2)
  (BPair.ofNat 12) (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat
  1) (BPair.ofNat 1) BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  (BPair.ofNat 1) (BPair.ofNat 5) BPair.unit (BPair.ofNat 1) (BPair.ofNat 10) BPair.unit
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- the profile's read `|W|_∞ ≤ |W|` (`hWinf`) is the frame's own, the sup norm at
-- or below the Euclidean norm at every profile
-- at mZD = 101 the binder `hZD` refuses and the conclusion parts
theorem pin67 : ¬ ((BPair.ofNat 1) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 101) ≤ (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) + (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1) * BPair.unit * BPair.unit + (BPair.ofNat 1) * BPair.unit * BPair.unit) := by decide +kernel
theorem pin68 : ¬ ((BPair.ofNat 101) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) ≤ ((BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 5) + BPair.ofNat 8 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2)) * (BPair.ofNat 1) * (BPair.ofNat 5) * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 1)) + (BPair.ofNat 4 * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) + (BPair.ofNat 26 * (BPair.ofNat 5) * (BPair.unit * BPair.unit) * BPair.unit * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1) + BPair.ofNat 26 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1)) * (BPair.ofNat 12) + (BPair.ofNat 32 * (BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.unit * BPair.unit) * (BPair.unit * BPair.unit) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)) * (BPair.ofNat 1) + (BPair.ofNat 8 * (BPair.ofNat 1) * (BPair.ofNat 1) * BPair.unit + BPair.ofNat 8 * BPair.unit) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1))) * ((BPair.ofNat 12) * (BPair.ofNat 12))) * ((BPair.ofNat 1) * (BPair.ofNat 1))) * (BPair.ofNat 2)) := by decide +kernel

-- the moments' key read (`key_moments`) at the scale `[1 : 5]`, the mass
-- `[1 : 1]`, the bit count one, the near scale `12`, five plaquettes, the
-- profile square `10`, the unit member reads, the deficits' pair `3`, the
-- mode weight's pair `26`, the stated pair `P' = 948`, the unit's moment one,
-- the mode square's moment one at its square's three, the variance two, the
-- solves `[30 : 3]` and `[10 : 1]`, the excess `192` and the mode read `193`
-- at the mode read's pair `[1 : 3]`: the excess and the mode read hold,
-- decided and through the theorem; its binders are its components' own,
-- each refused at its component's battery above
theorem pin69 : (BPair.ofNat 192) * ((BPair.ofNat 5) * (BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) ≤ BPair.ofNat 192 * ((BPair.ofNat 1) * (BPair.ofNat 1) * ((BPair.ofNat 3) * BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 24 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12))) + BPair.ofNat 3 * ((BPair.ofNat 3) * BPair.ofNat 5) + BPair.unit * ((BPair.ofNat 3) * BPair.ofNat 5)) + BPair.ofNat 2 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12))) + BPair.unit) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 5) ∧ (BPair.ofNat 193) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 3) * (BPair.ofNat 1) ≤ BPair.ofNat 16 * (BPair.ofNat 1) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 5) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) + BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 34)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 32 * ((BPair.ofNat 12) * BPair.unit * BPair.unit * ((BPair.ofNat 1) + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 34) + BPair.ofNat 96 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)))) + (BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1)) + BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 948) + BPair.ofNat 4 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1))) + BPair.unit) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 3) := by decide +kernel
theorem pin70 : (BPair.ofNat 192) * ((BPair.ofNat 5) * (BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) ≤ BPair.ofNat 192 * ((BPair.ofNat 1) * (BPair.ofNat 1) * ((BPair.ofNat 3) * BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 24 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12))) + BPair.ofNat 3 * ((BPair.ofNat 3) * BPair.ofNat 5) + BPair.unit * ((BPair.ofNat 3) * BPair.ofNat 5)) + BPair.ofNat 2 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12))) + BPair.unit) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 5) ∧ (BPair.ofNat 193) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 3) * (BPair.ofNat 1) ≤ BPair.ofNat 16 * (BPair.ofNat 1) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 5) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) + BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 34)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 32 * ((BPair.ofNat 12) * BPair.unit * BPair.unit * ((BPair.ofNat 1) + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 34) + BPair.ofNat 96 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)))) + (BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1)) + BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 948) + BPair.ofNat 4 * (BPair.unit * ((BPair.ofNat 12) * (BPair.ofNat 12)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1))) + BPair.unit) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 3) :=
  key_moments 5 1 (BPair.ofNat 192) (BPair.ofNat 193) (BPair.ofNat 192) BPair.unit (BPair.ofNat
  1) (BPair.ofNat 2) (BPair.ofNat 1) BPair.unit (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1)
  (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit (BPair.ofNat 2) (BPair.ofNat 386)
  (BPair.ofNat 26) (BPair.ofNat 192) BPair.unit (BPair.ofNat 1) BPair.unit BPair.unit
  (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit BPair.unit (BPair.ofNat 1) BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit ((BPair.ofNat 8).swap) BPair.unit (BPair.ofNat 1)
  (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 3) BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 1) (BPair.ofNat 1)
  (BPair.ofNat 12) (BPair.ofNat 12) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat
  10) BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit (BPair.ofNat 3) (BPair.ofNat 34) (BPair.ofNat 948)
  (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 1)
  BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 30) (BPair.ofNat 3)
  (BPair.ofNat 10) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel)
-- the key read at the mass `[1 : 2]`, the bit count two, the near scale `32`,
-- the pair `P' = 2508`, the excess `48` and the mode read `49`
theorem pin77 : (BPair.ofNat 48) * ((BPair.ofNat 5) * (BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * (BPair.ofNat 1) ≤ BPair.ofNat 192 * ((BPair.ofNat 1) * (BPair.ofNat 1) * ((BPair.ofNat 3) * BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 24 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32))) + BPair.ofNat 3 * ((BPair.ofNat 3) * BPair.ofNat 5) + BPair.unit * ((BPair.ofNat 3) * BPair.ofNat 5)) + BPair.ofNat 2 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32))) + BPair.unit) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 5) ∧ (BPair.ofNat 49) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * (BPair.ofNat 3) * (BPair.ofNat 1) ≤ BPair.ofNat 16 * (BPair.ofNat 1) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 5) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * (BPair.ofNat 1) + BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 34)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 32 * ((BPair.ofNat 32) * BPair.unit * BPair.unit * ((BPair.ofNat 1) + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 34) + BPair.ofNat 96 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)))) + (BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1)) + BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 2508) + BPair.ofNat 4 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1))) + BPair.unit) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 3) := by decide +kernel
theorem pin78 : (BPair.ofNat 48) * ((BPair.ofNat 5) * (BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * (BPair.ofNat 1) ≤ BPair.ofNat 192 * ((BPair.ofNat 1) * (BPair.ofNat 1) * ((BPair.ofNat 3) * BPair.ofNat 5)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 24 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32))) + BPair.ofNat 3 * ((BPair.ofNat 3) * BPair.ofNat 5) + BPair.unit * ((BPair.ofNat 3) * BPair.ofNat 5)) + BPair.ofNat 2 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32))) + BPair.unit) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 5) ∧ (BPair.ofNat 49) * ((BPair.ofNat 5) * (BPair.ofNat 5)) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * (BPair.ofNat 3) * (BPair.ofNat 1) ≤ BPair.ofNat 16 * (BPair.ofNat 1) * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 5) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * (BPair.ofNat 1) + BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1) * (BPair.ofNat 34)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 1) * (BPair.ofNat 5) * (BPair.ofNat 3) * (BPair.ofNat 1) + ((BPair.ofNat 1) * (BPair.ofNat 32 * ((BPair.ofNat 32) * BPair.unit * BPair.unit * ((BPair.ofNat 1) + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 34) + BPair.ofNat 96 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1)))) + (BPair.ofNat 384 * ((BPair.ofNat 1) * (BPair.ofNat 1)) + BPair.ofNat 6 + BPair.unit) * (BPair.ofNat 2508) + BPair.ofNat 4 * (BPair.unit * ((BPair.ofNat 32) * (BPair.ofNat 32)) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat 1))) + BPair.unit) * ((BPair.ofNat 2) * (BPair.ofNat 2)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 3) :=
  key_moments 5 2 (BPair.ofNat 48) (BPair.ofNat 49) (BPair.ofNat 48) BPair.unit (BPair.ofNat 1)
  (BPair.ofNat 2) (BPair.ofNat 1) BPair.unit (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1)
  (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit (BPair.ofNat 2) (BPair.ofNat 98)
  (BPair.ofNat 26) (BPair.ofNat 48) BPair.unit (BPair.ofNat 1) BPair.unit BPair.unit
  (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit BPair.unit (BPair.ofNat 1) BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit (BPair.ofNat 8).swap BPair.unit (BPair.ofNat 1) (BPair.ofNat
  3) (BPair.ofNat 1) (BPair.ofNat 3) BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit (BPair.ofNat 1) (BPair.ofNat 5) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 16)
  (BPair.ofNat 32) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 10) BPair.unit
  BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit (BPair.ofNat 3) (BPair.ofNat 34) (BPair.ofNat 2508) (BPair.ofNat 1)
  (BPair.ofNat 1) BPair.unit BPair.unit (BPair.ofNat 1) (BPair.ofNat 1) BPair.unit BPair.unit
  (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 30) (BPair.ofNat 3) (BPair.ofNat 10) (BPair.ofNat
  1) (BPair.ofNat 1) (BPair.ofNat 3) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)


-- the tail read (`moment_tail`) at the four-link unit Tail `tFour`, the side
-- one, the mass `[1 : 1]`, the floor `[10⁷ : 1]` and the halving `152`, the
-- least at the key's list (the bit count `6761`, the near scale `324720`):
-- the unit's moment `2³⁰⁴`, the mode square's moment `2¹⁵²` at its square's
-- three, the variance two, the solves `[2 : 1]` and `[0 : 1]`, the near mass's
-- chain constant at the clearing `2³⁰⁴` with the support weight one, every
-- further moment at the unit, and the two reads at the unit: the reads' sum
-- under the floor's multiple of the scale, decided and through the theorem
-- at every one of its 103 reads by kernel
theorem pin71 : (BPair.unit + BPair.unit) * BPair.ofNat (2 ^ 152) * BPair.ofNat 1 < BPair.ofNat 1 * BPair.ofNat 10000000 := by decide +kernel
-- the tail read's binder proofs at the pin's data, one private theorem per
-- binder in the theorem's own order
private theorem mt1 : tFour.pos :=
  by decide +kernel
private theorem mt2 : 1 ≤ 1 :=
  by decide +kernel
private theorem mt3 : tFour.dG ≤ 32 * tFour.dth * tFour.np * (1 + 2) :=
  by decide +kernel
private theorem mt4 : tFour.Winf * tFour.Winf ≤ tFour.W2 :=
  by decide +kernel
private theorem mt5 : sideRead tFour.kappa 10000000 1 1 :=
  by decide +kernel
private theorem mt6 : massRead tFour 1 10000000 1 0 :=
  by decide +kernel
private theorem mt7 : tailRead tFour 1 0 10000000 1 152 :=
  by decide +kernel
private theorem mt8 : ∀ p, p < tFour.np → (fun _ _ => BPair.ofNat (2 ^ 304)) p 0 ≤ (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt9 : ∀ p, p < tFour.np → ∀ j, j ≤ kc tFour 1 0 152 + 1 → BPair.unit < (fun _ _ => BPair.ofNat (2 ^ 304)) p j :=
  fun _ _ _ _ => unitLtNat (@Nat.pow_pos 2 304 (by decide))
private theorem mt10 : ∀ p, p < tFour.np → (fun _ _ => BPair.ofNat (2 ^ 304)) p (kc tFour 1 0 152 + 1) ≤ (fun _ _ => BPair.ofNat (2 ^ 304)) p (kc tFour 1 0 152) :=
  by decide +kernel
private theorem mt11 : ∀ p, p < tFour.np → ∀ j, j + 1 ≤ kc tFour 1 0 152 → (fun _ _ => BPair.ofNat (2 ^ 304)) p (j + 1) * (fun _ _ => BPair.ofNat (2 ^ 304)) p (j + 1) ≤ (fun _ _ => BPair.ofNat (2 ^ 304)) p j * (fun _ _ => BPair.ofNat (2 ^ 304)) p (j + 2) :=
  fun _ _ _ _ => leB_refl _
private theorem mt12 : ∀ p, p < tFour.np → ((fun _ _ => BPair.ofNat (2 ^ 304)) p (kc tFour 1 0 152)).oneValue (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt13 : ∀ p, p < tFour.np → (BPair.ofNat (2 ^ 304)) ≤ (BPair.ofNat 1) * (fun _ _ => BPair.ofNat (2 ^ 304)) p (kc tFour 1 0 152 + 1) :=
  by decide +kernel
private theorem mt14 : ∀ p, p < tFour.np → (fun _ =>
  BPair.unit) p ≤ BPair.ofNat 2 * BPair.ofNat tFour.dth * ((fun _ _ => BPair.ofNat (2 ^ 304)) p (kc tFour 1 0 152) + ((fun _ _ => BPair.ofNat (2 ^ 304)) p (kc tFour 1 0 152 + 1)).swap) :=
  by decide +kernel
private theorem mt15 : BPair.ofNat 1 * BPair.ofNat (2 ^ 0) * (BPair.ofNat (2 ^ 304)) + (BPair.ofNat (2 ^ 152) * (BPair.ofNat 1 * BPair.ofNat (2 ^ 0) + BPair.ofNat 2) * bsum (fun _ =>
  BPair.unit) (List.range tFour.np)).swap ≤ BPair.ofNat 1 * BPair.ofNat (2 ^ 0) * (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt16 : (BPair.ofNat (2 ^ 304)) ≤ (BPair.ofNat 1) * (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt17 : (BPair.ofNat 1) ≤ BPair.ofNat (cW tFour * kc tFour 1 0 152 ^ exK tFour) :=
  by decide +kernel
private theorem mt18 : BPair.unit ≤ (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt19 : BPair.unit ≤ (BPair.ofNat 1) :=
  by decide +kernel
private theorem mt20 : BPair.unit ≤ (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt21 : BPair.unit < (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt22 : (BPair.ofNat (2 ^ 304)) ≤ (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt23 : BPair.unit < (BPair.ofNat 2) :=
  by decide +kernel
private theorem mt24 : BPair.unit < (BPair.ofNat 1) :=
  by decide +kernel
private theorem mt25 : BPair.unit < (BPair.ofNat 1) :=
  by decide +kernel
private theorem mt26 : BPair.unit ≤ (BPair.ofNat 2) :=
  by decide +kernel
private theorem mt27 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt28 : BPair.unit ≤ (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt29 : BPair.unit ≤ (BPair.ofNat
  3) :=
  by decide +kernel
private theorem mt30 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt31 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt32 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt33 : BPair.unit ≤ (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt34 : BPair.unit ≤ (BPair.ofNat 3) :=
  by decide +kernel
private theorem mt35 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt36 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt37 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt38 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt39 : (BPair.unit * (BPair.ofNat (2 ^ 304))).oneValue (BPair.unit + BPair.unit) :=
  by decide +kernel
private theorem mt40 : BPair.unit * ((BPair.ofNat (2 ^ 0)) * (BPair.ofNat (2 ^ 0))) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) ≤ BPair.ofNat 96 * ((BPair.ofNat tFour.g) * (((BPair.ofNat 1) * (BPair.ofNat 1)) * BPair.unit)) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) + BPair.ofNat 12 * ((BPair.ofNat (thetaR tFour 1)) * BPair.unit) * ((BPair.ofNat (2 ^ 0)) * (BPair.ofNat (2 ^ 0))) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) + BPair.ofNat 3 * (((BPair.ofNat 1) * (BPair.ofNat 1)) * BPair.unit) * ((BPair.ofNat (2 ^ 0)) * (BPair.ofNat (2 ^ 0))) * (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt41 : BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) * (BPair.ofNat (pairClr tFour)) ≤ (BPair.ofNat (cq tFour 1)) * BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) + (BPair.ofNat (pairClr tFour)) * ((BPair.ofNat 1) * (BPair.ofNat tFour.Om) * BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)))) + (BPair.ofNat (wq tFour)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat (2 ^ 304)) * (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt42 : BPair.unit ≤ BPair.ofNat 2 * (BPair.ofNat tFour.kappa) * BPair.unit :=
  by decide +kernel
private theorem mt43 : (BPair.unit * (BPair.ofNat 2)).oneValue BPair.unit :=
  by decide +kernel
private theorem mt44 : BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) ≤ BPair.ofNat 2 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * BPair.unit + BPair.ofNat 2 * BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) + BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) :=
  by decide +kernel
private theorem mt45 : BPair.unit * (BPair.ofNat (1 * 1 + 2 * 1 + 2)) ≤ BPair.ofNat 8 * ((BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.kappa)) * (BPair.ofNat 20) * (BPair.ofNat tFour.W2) * (BPair.ofNat (2 ^ 152)) + BPair.ofNat 8 * (BPair.ofNat (rho2 tFour 1)) * (BPair.ofNat tFour.nl) * (BPair.ofNat (tFour.Winf * tFour.Winf)) * BPair.unit * (BPair.ofNat (1 * 1 + 2 * 1 + 2)) :=
  by decide +kernel
private theorem mt46 : BPair.unit * ((BPair.ofNat (2 ^ 0)) * (BPair.ofNat (2 ^ 0))) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) ≤ BPair.ofNat 192 * ((BPair.ofNat tFour.g) * (BPair.ofNat tFour.kappa) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * BPair.unit) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) + BPair.ofNat 12 * ((BPair.ofNat (thetaR tFour 1)) * BPair.unit) * ((BPair.ofNat (2 ^ 0)) * (BPair.ofNat (2 ^ 0))) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) + BPair.ofNat 3 * ((BPair.ofNat 1) * (BPair.ofNat 1) * BPair.unit) * ((BPair.ofNat (2 ^ 0)) * (BPair.ofNat (2 ^ 0))) :=
  by decide +kernel
private theorem mt47 : BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) * (BPair.ofNat (pairClr tFour)) ≤ (BPair.ofNat (cq tFour 1)) * BPair.unit * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) + (BPair.ofNat (pairClr tFour)) * ((BPair.ofNat 1) * (BPair.ofNat tFour.Om) * BPair.unit * (BPair.ofNat (2 ^ 152))) + (BPair.ofNat (wq tFour)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * (BPair.ofNat 2) :=
  by decide +kernel
private theorem mt48 : (BPair.ofNat 2) ≤ (BPair.ofNat (w0 tFour)) * (BPair.ofNat tFour.W2) * (BPair.ofNat 1) :=
  by decide +kernel
private theorem mt49 : BPair.ofNat 2 * (BPair.ofNat tFour.W2) * (BPair.ofNat 1) ≤ (BPair.ofNat 2) * ((BPair.ofNat 1) + BPair.ofNat 2) :=
  by decide +kernel
private theorem mt50 : BPair.unit ≤ (BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour)) * (BPair.ofNat tFour.W2) * (BPair.ofNat 1) :=
  by decide +kernel
private theorem mt51 : (BPair.ofNat (2 ^ 152)) ≤ (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt52 : BPair.ofNat 2 * (BPair.ofNat 3) * (BPair.ofNat (2 ^ 152)) ≤ BPair.ofNat 2 * (BPair.ofNat
  3) * (BPair.ofNat (2 ^ 152)) + (BPair.ofNat 1) * (BPair.ofNat 3) :=
  by decide +kernel
private theorem mt53 : BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) + (BPair.ofNat 1) * (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt54 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt55 : BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit + (BPair.ofNat 1) * BPair.unit :=
  by decide +kernel
private theorem mt56 : BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit + (BPair.ofNat 1) * BPair.unit :=
  by decide +kernel
private theorem mt57 : BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit + (BPair.ofNat 1) * BPair.unit :=
  by decide +kernel
private theorem mt58 : BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * BPair.unit + (BPair.ofNat 1) * BPair.unit :=
  by decide +kernel
private theorem mt59 : BPair.unit ≤ BPair.unit :=
  by decide +kernel
private theorem mt60 : BPair.unit ≤ BPair.ofNat 2 * BPair.unit :=
  by decide +kernel
private theorem mt61 : BPair.unit ≤ BPair.ofNat 2 * BPair.unit :=
  by decide +kernel
private theorem mt62 : BPair.unit ≤ BPair.ofNat 2 * BPair.unit :=
  by decide +kernel
private theorem mt63 : (BPair.ofNat 3) ≤ BPair.ofNat 2 * (BPair.ofNat
  3) :=
  by decide +kernel
private theorem mt64 : (BPair.ofNat (2 ^ 152)) ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt65 : BPair.unit ≤ BPair.ofNat 2 * BPair.unit :=
  by decide +kernel
private theorem mt66 : BPair.unit ≤ BPair.ofNat 2 * BPair.unit :=
  by decide +kernel
private theorem mt67 : (BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat 1)).oneValue ((BPair.ofNat 1) * ((BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.dG) * (BPair.ofNat 2) * (BPair.ofNat (2 ^ 304)) + BPair.unit * (BPair.ofNat 1))) :=
  by decide +kernel
private theorem mt68 : (BPair.ofNat 2 * (BPair.ofNat 3) * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat 1)).oneValue ((BPair.ofNat 1) * ((BPair.ofNat tFour.kappa) * ((BPair.ofNat tFour.dG) + BPair.ofNat 2) * (BPair.ofNat 2) * (BPair.ofNat (2 ^ 152)) + BPair.unit * (BPair.ofNat 1))) :=
  by decide +kernel
private theorem mt69 : (BPair.ofNat 2 * BPair.unit * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat 1)).oneValue ((BPair.ofNat 1) * ((BPair.ofNat tFour.kappa) * ((BPair.ofNat tFour.dG) + BPair.ofNat 2) * BPair.unit * (BPair.ofNat (2 ^ 152)) + BPair.unit * (BPair.ofNat 1))) :=
  by decide +kernel
private theorem mt70 : (BPair.ofNat 2 * BPair.unit * (BPair.ofNat (2 ^ 152)) * (BPair.ofNat 1)).oneValue ((BPair.ofNat 1) * ((BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.dG) * BPair.unit * (BPair.ofNat (2 ^ 304)) + BPair.unit * (BPair.ofNat 1))) :=
  by decide +kernel
private theorem mt71 : ((BPair.ofNat 2) * (BPair.ofNat (2 ^ 304))).oneValue ((BPair.ofNat
  3) * (BPair.ofNat (2 ^ 304)) + ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))).swap) :=
  by decide +kernel
private theorem mt72 : (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) ≤ (BPair.ofNat
  3) * (BPair.ofNat (2 ^ 304)) :=
  by decide +kernel
private theorem mt73 : (BPair.unit * (BPair.ofNat (2 ^ 304))).oneValue (BPair.ofNat 4 * (BPair.ofNat tFour.kappa) * ((BPair.ofNat (2 ^ 152)) * BPair.unit + ((BPair.ofNat (2 ^ 304)) * BPair.unit).swap)) :=
  by decide +kernel
private theorem mt74 : (BPair.ofNat 2 * BPair.unit * (BPair.ofNat (2 ^ 152)) + (BPair.ofNat 1) * (BPair.unit + BPair.unit + BPair.unit + BPair.unit)).oneValue ((BPair.ofNat 1) * (BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.dG) * BPair.unit * (BPair.ofNat 2)) :=
  by decide +kernel
private theorem mt75 : BPair.unit * (BPair.ofNat (2 ^ 152)) ≤ BPair.ofNat tFour.np * ((BPair.ofNat 1) * ((BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.dG) * (BPair.ofNat (w0 tFour)) * (BPair.ofNat (2 ^ 304)) + (BPair.ofNat (c1 tFour)) * (BPair.ofNat (rho1 tFour 1)) * BPair.unit) + (BPair.ofNat (c1 tFour)) * (BPair.ofNat (c1 tFour)) * (BPair.ofNat (tR tFour 1)) * (BPair.ofNat (tR tFour 1)) * BPair.unit * (BPair.ofNat (2 ^ 152))) :=
  by decide +kernel
private theorem mt76 : BPair.unit ≤ BPair.ofNat 2 * BPair.unit + BPair.ofNat 2 * (BPair.ofNat (cOff tFour 1)) * BPair.unit :=
  by decide +kernel
private theorem mt77 : BPair.ofNat 2 * (BPair.ofNat tFour.kappa) * (BPair.ofNat (pairClr tFour)) * BPair.unit ≤ (BPair.ofNat (pairClr tFour)) * BPair.unit + BPair.ofNat 2 * (BPair.ofNat tFour.kappa) * (BPair.ofNat (cqp tFour)) * BPair.unit :=
  by decide +kernel
private theorem mt78 : windowsep.mag BPair.unit ≤ (BPair.ofNat (a1 tFour 1)) * BPair.unit + BPair.unit :=
  by decide +kernel
private theorem mt79 : BPair.unit * (BPair.ofNat 1) ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * ((BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour)) * (BPair.ofNat (cWd tFour)) * (BPair.ofNat (tR tFour 1))) * BPair.unit :=
  by decide +kernel
private theorem mt80 : BPair.unit * BPair.unit ≤ (BPair.ofNat (2 ^ 152)) * BPair.unit :=
  by decide +kernel
private theorem mt81 : windowsep.mag BPair.unit ≤ (BPair.ofNat (a1 tFour 1)) * BPair.unit + windowsep.mag BPair.unit + BPair.unit :=
  by decide +kernel
private theorem mt82 : windowsep.mag BPair.unit * (BPair.ofNat 8 * ((BPair.ofNat 1) + BPair.ofNat 2) * (BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.W2)) ≤ (BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.kappa) * ((BPair.ofNat tFour.W2) * (BPair.ofNat tFour.W2)) * (BPair.ofNat (2 ^ 152)) + BPair.ofNat 64 * ((BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour)) * (BPair.ofNat (cWd tFour)) * (BPair.ofNat (cWd tFour)) * (BPair.ofNat (rho2 tFour 1)) * (BPair.ofNat (tFour.Winf * tFour.Winf))) * (((BPair.ofNat 1) + BPair.ofNat 2) * ((BPair.ofNat 1) + BPair.ofNat 2)) * BPair.unit :=
  by decide +kernel
private theorem mt83 : BPair.unit * (BPair.ofNat 1) ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ 152)) * ((BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour)) * (BPair.ofNat (cWd tFour)) * (BPair.ofNat (tR tFour 1))) * BPair.unit :=
  by decide +kernel
private theorem mt84 : BPair.unit * BPair.unit ≤ (BPair.ofNat 3) * BPair.unit :=
  by decide +kernel
private theorem mt85 : BPair.unit * ((BPair.ofNat (2 ^ 304)) * (BPair.ofNat (2 ^ 304))) ≤ BPair.ofNat 2 * ((BPair.ofNat (2 ^ 304)) * (BPair.ofNat (2 ^ 304))) * BPair.unit + BPair.ofNat 2 * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) * BPair.unit :=
  by decide +kernel
private theorem mt86 : BPair.ofNat 2 * BPair.unit ≤ BPair.ofNat 2 * (BPair.ofNat tFour.kappa) * ((BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour))) * (BPair.ofNat tFour.W2) * BPair.unit + (BPair.ofNat 3) :=
  by decide +kernel
private theorem mt87 : BPair.ofNat 2 * BPair.unit ≤ BPair.ofNat 2 * (BPair.ofNat tFour.kappa) * ((BPair.ofNat (w0 tFour)) * (BPair.ofNat (w0 tFour))) * (BPair.ofNat tFour.W2) * BPair.unit + (BPair.ofNat (2 ^ 152)) :=
  by decide +kernel
private theorem mt88 : BPair.unit ≤ BPair.ofNat tFour.np * (BPair.ofNat (w0 tFour)) :=
  by decide +kernel
private theorem mt89 : windowsep.mag BPair.unit ≤ BPair.ofNat tFour.np * (BPair.ofNat (c1 tFour)) * (BPair.ofNat (rho1 tFour 1)) * BPair.unit :=
  by decide +kernel
private theorem mt90 : BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat (2 ^ 152)) * windowsep.mag BPair.unit ≤ (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * BPair.unit + BPair.ofNat 16 * BPair.ofNat tFour.np * ((BPair.ofNat (c1 tFour)) * (BPair.ofNat (c1 tFour))) * (BPair.ofNat (rho2 tFour 1)) * (BPair.ofNat (tFour.Winf * tFour.Winf)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * BPair.unit :=
  by decide +kernel
private theorem mt91 : BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat (2 ^ 152)) * windowsep.mag BPair.unit ≤ (BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)) * BPair.unit + BPair.ofNat 4 * BPair.ofNat tFour.np * ((BPair.ofNat (c1 tFour)) * (BPair.ofNat (c1 tFour))) * ((BPair.ofNat (tR tFour 1)) * (BPair.ofNat (tR tFour 1))) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) * BPair.unit :=
  by decide +kernel
private theorem mt92 : (BPair.ofNat tFour.kappa) * ((BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.kappa) * (BPair.ofNat (2 * tFour.dth))) * BPair.unit ≤ (BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.kappa) * (BPair.ofNat (2 * tFour.dth)) * BPair.unit + (BPair.ofNat tFour.kappa) * (BPair.ofNat tFour.kappa) * (BPair.ofNat (2 * tFour.dth)) * (BPair.ofNat (cOff tFour 1)) * BPair.unit + (BPair.ofNat tFour.kappa) * (BPair.ofNat (cqp tFour)) * BPair.unit :=
  by decide +kernel
private theorem mt93 : BPair.unit * bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152) * (BPair.ofNat (2 ^ 152)) ≤ bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (1 + (jp tFour 1 0 152)) * (BPair.ofNat (2 ^ 304)) + bpow (BPair.ofNat (2 ^ 152)) (1 + (jp tFour 1 0 152)) * BPair.unit := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.unit_mul (bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152)))) (BPair.unit_mul (BPair.ofNat (2 ^ 152))))) ?_
  exact (unitLeAdd (unitLeMul (unitLeBpow (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeOfNat _)) (unitLeOfNat _)) (1 + (jp tFour 1 0 152))) (unitLeOfNat _)) (unitLeMul (unitLeBpow (unitLeOfNat _) (1 + (jp tFour 1 0 152))) (leB_refl _)))
private theorem mt94 : bpow (BPair.ofNat (2 ^ 152)) (1 + (jp tFour 1 0 152)) * BPair.unit ≤ BPair.ofNat (factorial (1 + (jp tFour 1 0 152))) * bpow (BPair.ofNat 1) (1 + (jp tFour 1 0 152)) * bpow (BPair.ofNat (2 ^ 0)) (1 + (jp tFour 1 0 152)) * (BPair.ofNat (2 ^ 304)) := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.mul_unit (bpow (BPair.ofNat (2 ^ 152)) (1 + (jp tFour 1 0 152))))) ?_
  exact (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeBpow (unitLeOfNat _) (1 + (jp tFour 1 0 152)))) (unitLeBpow (unitLeOfNat _) (1 + (jp tFour 1 0 152)))) (unitLeOfNat _))
private theorem mt95 : BPair.unit * bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) ≤ bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (2 + (jp tFour 1 0 152)) * (BPair.ofNat (2 ^ 304)) + bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152)) * BPair.unit := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.unit_mul (bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152)))) (BPair.unit_mul ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)))))) ?_
  exact (unitLeAdd (unitLeMul (unitLeBpow (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeOfNat _)) (unitLeOfNat _)) (2 + (jp tFour 1 0 152))) (unitLeOfNat _)) (unitLeMul (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152))) (leB_refl _)))
private theorem mt96 : bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152)) * BPair.unit ≤ BPair.ofNat (factorial (2 + (jp tFour 1 0 152))) * bpow (BPair.ofNat 1) (2 + (jp tFour 1 0 152)) * bpow (BPair.ofNat (2 ^ 0)) (2 + (jp tFour 1 0 152)) * (BPair.ofNat (2 ^ 304)) := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.mul_unit (bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152))))) ?_
  exact (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152)))) (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152)))) (unitLeOfNat _))
private theorem mt97 : BPair.unit * bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152) * (BPair.ofNat (2 ^ 152)) ≤ bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (1 + (jp tFour 1 0 152)) * (BPair.ofNat (2 ^ 152)) + bpow (BPair.ofNat (2 ^ 152)) (1 + (jp tFour 1 0 152)) * BPair.unit := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.unit_mul (bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152)))) (BPair.unit_mul (BPair.ofNat (2 ^ 152))))) ?_
  exact (unitLeAdd (unitLeMul (unitLeBpow (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeOfNat _)) (unitLeOfNat _)) (1 + (jp tFour 1 0 152))) (unitLeOfNat _)) (unitLeMul (unitLeBpow (unitLeOfNat _) (1 + (jp tFour 1 0 152))) (leB_refl _)))
private theorem mt98 : bpow (BPair.ofNat (2 ^ 152)) (1 + (jp tFour 1 0 152)) * BPair.unit ≤ BPair.ofNat (factorial (1 + (jp tFour 1 0 152))) * bpow (BPair.ofNat 1) (1 + (jp tFour 1 0 152)) * bpow (BPair.ofNat (2 ^ 0)) (1 + (jp tFour 1 0 152)) * ((BPair.ofNat (2 ^ 304)) * (BPair.ofNat (qPlus tFour))) := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.mul_unit (bpow (BPair.ofNat (2 ^ 152)) (1 + (jp tFour 1 0 152))))) ?_
  exact (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeBpow (unitLeOfNat _) (1 + (jp tFour 1 0 152)))) (unitLeBpow (unitLeOfNat _) (1 + (jp tFour 1 0 152)))) (unitLeMul (unitLeOfNat _) (unitLeOfNat _)))
private theorem mt99 : BPair.unit * bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) ≤ bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (2 + (jp tFour 1 0 152)) * (BPair.ofNat (2 ^ 152)) + bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152)) * BPair.unit := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.unit_mul (bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152)))) (BPair.unit_mul ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)))))) ?_
  exact (unitLeAdd (unitLeMul (unitLeBpow (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeOfNat _)) (unitLeOfNat _)) (2 + (jp tFour 1 0 152))) (unitLeOfNat _)) (unitLeMul (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152))) (leB_refl _)))
private theorem mt100 : bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152)) * BPair.unit ≤ BPair.ofNat (factorial (2 + (jp tFour 1 0 152))) * bpow (BPair.ofNat 1) (2 + (jp tFour 1 0 152)) * bpow (BPair.ofNat (2 ^ 0)) (2 + (jp tFour 1 0 152)) * ((BPair.ofNat (2 ^ 304)) * (BPair.ofNat (qPlus tFour))) := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.mul_unit (bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152))))) ?_
  exact (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152)))) (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152)))) (unitLeMul (unitLeOfNat _) (unitLeOfNat _)))
private theorem mt101 : BPair.unit * bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152) * ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152))) ≤ bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (2 + (jp tFour 1 0 152)) * (BPair.ofNat
  3) + bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152)) * BPair.unit := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.unit_mul (bpow ((BPair.ofNat (48 * (4 + jp tFour 1 0 152))) * (BPair.ofNat (2 ^ 0)) * (BPair.ofNat 1)) (jp tFour 1 0 152)))) (BPair.unit_mul ((BPair.ofNat (2 ^ 152)) * (BPair.ofNat (2 ^ 152)))))) ?_
  exact (unitLeAdd (unitLeMul (unitLeBpow (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeOfNat _)) (unitLeOfNat _)) (2 + (jp tFour 1 0 152))) (unitLeOfNat _)) (unitLeMul (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152))) (leB_refl _)))
private theorem mt102 : bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152)) * BPair.unit ≤ BPair.ofNat (factorial (2 + (jp tFour 1 0 152))) * bpow (BPair.ofNat 1) (2 + (jp tFour 1 0 152)) * bpow (BPair.ofNat (2 ^ 0)) (2 + (jp tFour 1 0 152)) * ((BPair.ofNat (2 ^ 304)) * ((BPair.ofNat (qPlus tFour)) * (BPair.ofNat (qPlus tFour)))) := by
  refine leB_congr_left (BPair.oneValue_symm (BPair.mul_unit (bpow (BPair.ofNat (2 ^ 152)) (2 + (jp tFour 1 0 152))))) ?_
  exact (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat _) (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152)))) (unitLeBpow (unitLeOfNat _) (2 + (jp tFour 1 0 152)))) (unitLeMul (unitLeOfNat _) (unitLeMul (unitLeOfNat _) (unitLeOfNat _))))
theorem pin72 : (BPair.unit + BPair.unit) * BPair.ofNat (2 ^ 152) * BPair.ofNat 1 < BPair.ofNat 1 * BPair.ofNat 10000000 :=
  moment_tail tFour 1 0 10000000 1 152 mt1 mt2 mt3 mt4 mt5 mt6 mt7 BPair.unit BPair.unit
  BPair.unit BPair.unit (BPair.ofNat (2 ^ 304)) BPair.unit BPair.unit BPair.unit
  (BPair.ofNat (2 ^ 152)) (BPair.ofNat
  3) (BPair.ofNat (2 ^ 152)) (BPair.ofNat 3) BPair.unit
  BPair.unit BPair.unit (BPair.ofNat 2) BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit BPair.unit
  (BPair.ofNat (2 ^ 304)) (BPair.ofNat 2) (BPair.ofNat 1) BPair.unit (BPair.ofNat 1)
  (fun _ _ => BPair.ofNat (2 ^ 304)) (fun _ =>
  BPair.unit) (BPair.ofNat (2 ^ 304))
  (BPair.ofNat 1) mt8 mt9 mt10 mt11 mt12 mt13 mt14 mt15 mt16 mt17 mt18 mt19 mt20 mt21 mt22 mt23
  mt24 mt25 mt26 mt27 mt28 mt29 mt30 mt31 mt32 mt33 mt34 mt35 mt36 mt37 mt38 mt39 mt40 mt41 mt42
  mt43 mt44 mt45 mt46 mt47 mt48 mt49 mt50 mt51 mt52 mt53 mt54 mt55 mt56 mt57 mt58 mt59 mt60 mt61
  mt62 mt63 mt64 mt65 mt66 mt67 mt68 mt69 mt70 mt71 mt72 mt73 mt74 mt75 mt76 mt77 mt78 mt79 mt80
  mt81 mt82 mt83 mt84 mt85 mt86 mt87 mt88 mt89 mt90 mt91 mt92 mt93 mt94 mt95 mt96 mt97 mt98 mt99
  mt100 mt101 mt102

-- at the excess one the binder `hru` refuses and the conclusion parts, the
-- join's own refusal
theorem pin79 : ¬ ((BPair.ofNat 1 * BPair.ofNat (2 ^ 304)).oneValue (BPair.unit + BPair.unit)) := by
  decide +kernel
theorem pin80 : ¬ ((BPair.ofNat 1 + BPair.unit) * BPair.ofNat (2 ^ 152) * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 10000000) := by decide +kernel

end cornerkey.cornermoment
