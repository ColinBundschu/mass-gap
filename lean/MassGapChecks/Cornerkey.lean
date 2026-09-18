import MassGap.Cornerkey
/-!
The check module for `lem:cornerkey`'s key.  The data are the unit
member and window reads `tOne` (every field one), positive by kernel.
The polynomial kit reads at `K = 2`: the sum `⟨1,2,3,4,5⟩ + ⟨5,4,3,2,1⟩`
at `6 + 12 + 24 + 48 + 96 = 186` against the two reads `129 + 57`, and
the triple's `387 = 3 · 129`.  The growth past the clearing at the
fourth power: at `K = 6`, `b = 1` the read `7⁴ = 2401` sits under
`2 · 6⁴ = 2592`, and at `K = 5` the clearing's binder refuses, `6⁴ =
1296` beyond `2 · 5⁴ = 1250`; the comparison's half read runs through
the theorem at `S = 1296`, `K = 6` to `S = 2592`, `K = 7`, and the
witness at `t = 32` from `K = 0`, `b = 1` reads `32⁴ ≤ 2³²`, refused
at `t = 10` where `10⁴` sits beyond `2¹⁰`, at the vacant cap, at the
vacant scale, and at the read `5000` beyond the halving count.  The
near scale at the side one and the mass `[1 : 8]`: the concentration
key `64072265625` at the first halving, the bit count `338`, the near
scale `48 · 342 · 8 = 131328`, the bit count `380` at the next halving
(the growth `42` at `b = 42`), `b_K = 16128`, the second member's bit
count `0` at the unit data and `400` at the forged `dim G = 2²⁰⁰`, the
chain's read at the first two halvings, and the clearing `6 b_K =
96768` under the near scale at the `126`-th halving, the `3b`-th.
The stated pairs at the side one: `Θ_R = 24 + 24 + 6 = 54`, `T_R =
55`, `ϱ₁ = 1 + 3 · 3 = 10`, `ϱ₂ = 12 + 24 + 6 = 42`, `C₁ = 3`, `W₀ =
9`, `C_D = 19`, `C_Z = 18 + 8 · 81 · 3 = 1962`, `c_off` the sum's
unit at one direction, `a₁ = 81 · 3 · 10 = 2430`, the clearing `2`,
`c'_q = c_q = 5`, `W_q = 9`, and the two scale pairs at `K = 5`, `P_u`
at `65211` reading its group through the theorem, `P_v` at
`51237895101` at `P'`'s `131041044`.  The keys: at the floor
`[100 : 1]` the side key `13` (`1280 · 15 = 19200` under `100 · 197`,
refused at the side `12`, `17920` beyond `17000`), at the floor
`[100000 : 1]` the side key `1`, the mass key `3` at the coefficient
`3028224` (under `100000 · 64`, refused at the halving `2`), the
list's caps at or beyond one and refused at the vacant floor, the
extent read at `d₁ = 3`, `n₁ = 1`, `i = 2` passing at both spellings
and refused at `i = 1`, and the scale key `158` through the walk's
computing read by kernel and through the theorem at the list's read
at `158` and its refusal at `157`; at the member read `C₂(θ) = 10¹²`
and the mass `[1 : 1]` the remainder cell's `a₁` decides the key
`147`, refused at `146`; and the tail read at the unit reads through
the theorem, the reads' sum under the floor's multiple of the scale
`[1 : 2¹⁵⁸]`.  The key's reads at the moment tier stand at
the four-link unit Tail `tFour` (the profile's count vacant, four
links) at the first halving: the concentration key at or beyond the
far read's natural five and its clearing of the cleared comparison
(decided at the Pascal count's fast read `pascD`, the key at the
order `10¹⁴`), and the three bit comparisons at the bit count `419`,
each decided and through its theorem, the unit weight's refused at
`tBig`, where the member read `dim G ≤ 32 d_θ #p (L + 2)` refuses and
the bit count falls to `19`.

The cap block's batteries close the module, each decided beside its
theorem route with one binder refused: the mode's variance read at
the scale `[1 : 3]` and the solve `[3 : 2]` (`1296 ≤ 1296`, the
profile's second read refused at the square's square's moment `4`),
the coordinate identity at one link and one generator index (the
parts identity refused at the gradient read at the unit), the excess
read at the scale `[1 : 2]` and the mass `[1 : 2]` (the excess `31`
at the squares' cap `60`, the cap's binder refused at `62`), the mode
read at the same scale and mass (the excess `76` at the range read
`10`, the second moments' binder refused at `11`), and the key's
quarters at the floor `[1700 : 1]` (the reads' sum `214` under the
floor, the scale comparison refused at the floor `[200 : 1]`).
-/

namespace cornerkey

open ground cornerkey cornercert

private def tOne : Tail := ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

private def tBig : Tail := ⟨1, 1, 2 ^ 200, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

private def tC : Tail := ⟨1, 1, 1, 1, 10 ^ 12, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩

-- the data's positivity
theorem pin1 : Tail.pos tOne := by decide +kernel

-- the polynomial kit at `K = 2`
theorem pin2 : (Poly4.add ⟨1, 2, 3, 4, 5⟩ ⟨5, 4, 3, 2, 1⟩).at 2 = 186 := by decide +kernel
theorem pin3 : (⟨1, 2, 3, 4, 5⟩ : Poly4).at 2 + (⟨5, 4, 3, 2, 1⟩ : Poly4).at 2 = 186 := by
  decide +kernel
theorem pin4 : (Poly4.scale 3 ⟨1, 2, 3, 4, 5⟩).at 2 = 387 := by decide +kernel

-- the growth past the clearing, and its refusal at the clearing
theorem pin5 : (⟨0, 0, 0, 0, 1⟩ : Poly4).at (6 + 1) ≤ 2 * (⟨0, 0, 0, 0, 1⟩ : Poly4).at 6 := by
  decide +kernel
theorem pin6 : (⟨0, 0, 0, 0, 1⟩ : Poly4).at (6 + 1) ≤ 2 * (⟨0, 0, 0, 0, 1⟩ : Poly4).at 6 :=
  Poly4.at_grow ⟨0, 0, 0, 0, 1⟩ 6 1 (by decide +kernel)
theorem pin7 : ¬ ((⟨0, 0, 0, 0, 1⟩ : Poly4).at (5 + 1) ≤ 2 * (⟨0, 0, 0, 0, 1⟩ : Poly4).at 5) := by
  decide +kernel

-- the comparison's half read and the witness, with the refusals of the
-- halving count, the cap, the scale and the read at one step
theorem pin8 : Cmp.read ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ (2 * 1296) 7 := by decide +kernel
theorem pin9 : Cmp.read ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ (2 * 1296) 7 :=
  Cmp.read_half ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ 1296 6 7 1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin10 : Cmp.read ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ (1 * 2 ^ 32) (0 + 1 * 32) := by decide +kernel
theorem pin11 : Cmp.read ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ (1 * 2 ^ 32) (0 + 1 * 32) :=
  Cmp.read_witness ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ 1 0 1 32 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin12 : ¬ Cmp.read ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ (1 * 2 ^ 10) (0 + 1 * 10) := by decide +kernel
theorem pin13 : ¬ Cmp.read ⟨⟨0, 0, 0, 0, 1⟩, 0⟩ (1 * 2 ^ 32) (0 + 1 * 32) := by decide +kernel
theorem pin14 : ¬ Cmp.read ⟨⟨0, 0, 0, 0, 1⟩, 1⟩ (0 * 2 ^ 32) (0 + 1 * 32) := by decide +kernel
theorem pin15 : ¬ Cmp.read ⟨⟨0, 0, 0, 0, 5000⟩, 1⟩ (1 * 2 ^ 32) (0 + 1 * 32) := by decide +kernel

-- the near scale at the side one and the mass `[1 : 8]`
theorem pin16 : kc tOne 1 3 0 = 64072265625 := by decide +kernel
theorem pin17 : jp tOne 1 3 0 = 338 := by decide +kernel
theorem pin18 : nearScale tOne 1 3 0 = 131328 := by decide +kernel
theorem pin19 : jp tOne 1 3 1 = 380 := by decide +kernel
theorem pin20 : bGrow tOne = 42 := by decide +kernel
theorem pin21 : bK tOne 3 = 16128 := by decide +kernel
theorem pin22 : denBits tOne = 0 := by decide +kernel
theorem pin23 : denBits tBig = 400 := by decide +kernel
theorem pin24 : bitWalk tOne 1 3 1 = 380 := by decide +kernel
theorem pin25 : bitWalk tOne 1 3 1 = jp tOne 1 3 1 := bitWalk_eq tOne 1 3 (by decide +kernel) 1
theorem pin26 : 6 * bK tOne 3 ≤ nearScale tOne 1 3 (3 * bGrow tOne) := by decide +kernel
theorem pin27 : 6 * bK tOne 3 ≤ nearScale tOne 1 3 (3 * bGrow tOne + denBits tOne + 0) :=
  nearScale_clear tOne 1 3 0 (by decide +kernel)

-- the stated pairs at the side one
theorem pin28 : thetaR tOne 1 = 54 := by decide +kernel
theorem pin29 : tR tOne 1 = 55 := by decide +kernel
theorem pin30 : rho1 tOne 1 = 10 := by decide +kernel
theorem pin31 : rho2 tOne 1 = 42 := by decide +kernel
theorem pin32 : c1 tOne = 3 := by decide +kernel
theorem pin33 : w0 tOne = 9 := by decide +kernel
theorem pin34 : cD tOne = 19 := by decide +kernel
theorem pin35 : cZ tOne 1 = 1962 := by decide +kernel
theorem pin36 : cOff tOne 1 = 0 := by decide +kernel
theorem pin37 : a1 tOne 1 = 2430 := by decide +kernel
theorem pin38 : pairClr tOne = 2 := by decide +kernel
theorem pin39 : cqp tOne = 5 := by decide +kernel
theorem pin40 : cq tOne 1 = 5 := by decide +kernel
theorem pin41 : wq tOne = 9 := by decide +kernel
theorem pin42 : (ppC tOne 1).at 5 = 131041044 := by decide +kernel
theorem pin43 : (puC tOne 1).at 5 = 65211 := by decide +kernel
theorem pin44 : (puC tOne 1).at 5 = pairClr tOne * (24 * (thetaR tOne 1 * (5 * 5))
    + 3 * (cD tOne * tOne.np) + tOne.Om * (cD tOne * tOne.np)) + 2 * (cq tOne 1 * (5 * 5))
    + wq tOne := puC_read tOne 1 5
theorem pin45 : (pvC tOne 1).at 5 = 51237895101 := by decide +kernel
theorem pin46 : (pvC tOne 1).at 5 = pairClr tOne * (32 * (5 * rho2 tOne 1 * tOne.nl * (1 + 2))
    + (6 + tOne.Om) * cZ tOne 1 + 96 * (thetaR tOne 1 * (5 * 5) * (1 + 2 * tOne.dG)))
    + (384 * (tOne.g * tOne.kappa) + 6 + tOne.Om) * (ppC tOne 1).at 5
    + 4 * (cq tOne 1 * (5 * 5) * (1 + 2 * tOne.dG)) + wq tOne := pvC_read tOne 1 5

-- the keys
theorem pin47 : sideKey 1 100 1 = 13 := by decide +kernel
theorem pin48 : sideRead 1 100 1 13 := by decide +kernel
theorem pin49 : ¬ sideRead 1 100 1 12 := by decide +kernel
theorem pin50 : sideRead 1 100 1 (sideKey 1 100 1) := sideKey_hit 1 100 1 (by decide +kernel)
theorem pin51 : sideKey 1 100000 1 = 1 := by decide +kernel
theorem pin52 : massX tOne 1 = 3028224 := by decide +kernel
theorem pin53 : massKey tOne 1 100000 1 = 3 := by decide +kernel
theorem pin54 : massRead tOne 1 100000 1 3 := by decide +kernel
theorem pin55 : ¬ massRead tOne 1 100000 1 2 := by decide +kernel
theorem pin56 : 3 ≤ 1 * 2 ^ 2 := by decide +kernel
theorem pin57 : 1 * (3 * 3) ≤ 1 * 1 * 4 ^ 2 := by decide +kernel
theorem pin58 : 1 * (3 * 3) ≤ 1 * 1 * 4 ^ 2 := (extent_read 1 3 2).1 (by decide +kernel)
theorem pin59 : ¬ 3 ≤ 1 * 2 ^ 1 := by decide +kernel
theorem pin60 : listCaps (tailCmps tOne 1 100000 1) := by decide +kernel
theorem pin61 : listCaps (tailCmps tOne 1 100000 1) :=
  tailCaps tOne 1 100000 1 (by decide +kernel) (by decide +kernel)
theorem pin62 : ¬ listCaps (tailCmps tOne 1 0 1) := by decide +kernel
theorem pin63 : tailRead tOne 1 3 100000 1 158 := by decide +kernel
theorem pin64 : ¬ tailRead tOne 1 3 100000 1 157 := by decide +kernel
theorem pin65 : tailKeyC tOne 1 3 100000 1 = 158 := by decide +kernel
theorem pin66 : tailKey tOne 1 3 100000 1 = 158 :=
  (tailKeyC_eq tOne 1 3 100000 1 (by decide +kernel)).symm.trans (by decide +kernel)
theorem pin67 : tailKey tOne 1 3 100000 1 = 158 :=
  Nat.le_antisymm (tailKey_le tOne 1 3 100000 1 158 (by decide +kernel))
    (tailKey_ge tOne 1 3 100000 1 157 (by decide +kernel) (by decide +kernel) (by decide +kernel))
theorem pin68 : tailRead tC 1 0 100000 1 147 := by decide +kernel
theorem pin69 : ¬ tailRead tC 1 0 100000 1 146 := by decide +kernel

-- the tail read at the unit reads
theorem pin70 : (BPair.unit + BPair.unit) * BPair.ofNat (2 ^ 158) * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 100000 :=
  tail_read tOne 1 3 100000 1 158 BPair.unit BPair.unit (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- the key's reads at the moment tier at the four-link unit Tail `tFour`
-- (the profile's count vacant, four links), the side one, the mass `[1 : 1]`
-- and the first halving: the concentration key at or beyond the far read's
-- natural five, its clearing of the cleared comparison through the falling
-- products (decided at the Pascal count's fast read), and the three bit
-- comparisons at the bit count `419`, each decided and through its
-- theorem; the unit weight's comparison refuses at
-- the forged `dim G = 2²⁰⁰`, where the member read `dim G ≤ 32 d_θ #p (L + 2)`
-- refuses and the bit count falls to `19`
/-- The four-link unit Tail, the profile's count vacant. -/
def tFour : Tail := ⟨1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 4, 1, 1, 1, 1, 1⟩
theorem pin71 : Tail.pos tFour := by decide +kernel
theorem pin72 : 1 ≤ qPlus tFour := qPlus_pos tFour (by decide +kernel)
theorem pin73 : 2 ^ 0 ≤ tauD tFour 1 0 1 := by decide +kernel
theorem pin74 : 2 ^ 0 ≤ tauD tFour 1 0 1 := tauD_ge tFour 1 0 1 (by decide +kernel) (by decide)
theorem pin75 : jK tFour ≤ kc tFour 1 0 1 := by decide +kernel
theorem pin76 : jK tFour ≤ kc tFour 1 0 1 := kc_ge_jK tFour 1 0 1 (by decide +kernel) (by decide)
theorem pin77 : cW tFour * kc tFour 1 0 1 ^ exK tFour * tauD tFour 1 0 1 ^ jK tFour
    ≤ pasc (kc tFour 1 0 1 + 1) (jK tFour) * (2 ^ 0) ^ jK tFour := by
  rw [← pascD_eq]
  decide +kernel
theorem pin78 : cW tFour * kc tFour 1 0 1 ^ exK tFour * tauD tFour 1 0 1 ^ jK tFour
    ≤ pasc (kc tFour 1 0 1 + 1) (jK tFour) * (2 ^ 0) ^ jK tFour :=
  conc_key_read tFour 1 0 1 (by decide +kernel) (by decide)
theorem pin79 : jp tFour 1 0 1 = 419 := by decide +kernel
theorem pin80 : 2 ^ (2 * 0) * (2 * cW tFour * kc tFour 1 0 1 ^ exK tFour) ≤ 2 ^ jp tFour 1 0 1 := by
  decide +kernel
theorem pin81 : 2 ^ (2 * 0) * (2 * cW tFour * kc tFour 1 0 1 ^ exK tFour) ≤ 2 ^ jp tFour 1 0 1 :=
  bit_unit tFour 1 0 1 (by decide +kernel) (by decide)
theorem pin82 : 2 ^ (2 * 0) * pairX tFour 1 0 1 * qPlus tFour
    ≤ 2 ^ jp tFour 1 0 1 * (tFour.kappa * tFour.dG * tFour.W2) := by decide +kernel
theorem pin83 : 2 ^ (2 * 0) * pairX tFour 1 0 1 * qPlus tFour
    ≤ 2 ^ jp tFour 1 0 1 * (tFour.kappa * tFour.dG * tFour.W2) :=
  bit_mode tFour 1 0 1 (by decide +kernel)
theorem pin84 : 2 ^ (2 * 0) * (pairX tFour 1 0 1 * pairX tFour 1 0 1) * (qPlus tFour * qPlus tFour)
    ≤ 2 ^ jp tFour 1 0 1 * pairDen tFour := by decide +kernel
theorem pin85 : 2 ^ (2 * 0) * (pairX tFour 1 0 1 * pairX tFour 1 0 1) * (qPlus tFour * qPlus tFour)
    ≤ 2 ^ jp tFour 1 0 1 * pairDen tFour := bit_msq tFour 1 0 1 (by decide +kernel)
theorem pin86 : jp tBig 1 0 1 = 19 := by decide +kernel
theorem pin87 : ¬ (tBig.dG ≤ 32 * tBig.dth * tBig.np * (1 + 2)) := by decide +kernel
theorem pin88 : ¬ (2 ^ (2 * 0) * (2 * cW tBig * kc tBig 1 0 1 ^ exK tBig) ≤ 2 ^ jp tBig 1 0 1) := by
  decide +kernel

-- the mode's variance read (`mode_variance`) at the scale `[1 : 3]` and
-- the solve `[3 : 2]`: the mode square's moment 3 at the solve against
-- the unit's moment 3, the square's square's moment 5 at the profile's two
-- reads 3 and 6, the side 2 at `dim G = 2`, the remainders and their caps
-- at the unit: 1296 ≤ 1296 decided and through the theorem; at the
-- square's square's moment 4 the profile's second read refuses and the
-- conclusion parts, 1296 against 1080
theorem pin89 : BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 + BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 2
    ≤ BPair.ofNat 4 * BPair.ofNat 5 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 * (BPair.ofNat 2 + BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 := by
  decide +kernel
theorem pin90 : BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 + BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 2
    ≤ BPair.ofNat 4 * BPair.ofNat 5 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 * (BPair.ofNat 2 + BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 :=
  mode_variance
    (BPair.ofNat 3) (BPair.ofNat 5) (BPair.ofNat 3) (BPair.ofNat 6) (BPair.ofNat 3) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 3) (BPair.ofNat 2) BPair.unit BPair.unit BPair.unit BPair.unit
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
theorem pin91 : ¬ (BPair.ofNat 2 * BPair.ofNat 6 * BPair.ofNat 3 ≤ BPair.ofNat 2 * BPair.ofNat 4 * BPair.ofNat 3 + BPair.ofNat 1 * BPair.ofNat 6) := by decide +kernel
theorem pin92 : ¬ (BPair.ofNat 4 * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 + BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 2
    ≤ BPair.ofNat 4 * BPair.ofNat 4 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 2 + BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 * (BPair.ofNat 2 + BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3 + BPair.ofNat 2 * BPair.ofNat 1 * BPair.ofNat 3 * BPair.unit * BPair.ofNat 2 * BPair.ofNat 3) := by
  decide +kernel

-- the coordinate identity (`coord_identity`) at one link and one generator
-- index: every weight one, the remainders at the unit, the exponent's
-- gradient read the coordinate's balance partner, decided and through the
-- theorem; at the gradient read at the unit the parts identity refuses and
-- the conclusion parts at the remainder's read one, 2 against 1
theorem pin93 : (BPair.ofNat 1 * BPair.ofNat 1
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + BPair.ofNat 1 * bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)).oneValue
    (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1) := by decide +kernel
theorem pin94 : (BPair.ofNat 1 * BPair.ofNat 1
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + BPair.ofNat 1 * bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)).oneValue
    (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1) :=
  coord_identity 1 1 (fun _ => BPair.ofNat 1) (fun _ => BPair.ofNat 1) (fun _ => BPair.unit)
    (fun _ => BPair.unit) (fun _ => BPair.ofNat 1) (fun _ => BPair.unit)
    (fun _ _ => (BPair.ofNat 1).swap) (fun _ _ => BPair.ofNat 1)
    (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (fun _ _ _ _ => by decide +kernel)
theorem pin95 : ¬ ((BPair.unit + BPair.ofNat 1 * BPair.ofNat 1).oneValue BPair.unit) := by decide +kernel
theorem pin96 : ¬ ((BPair.ofNat 1 * BPair.ofNat 1
      + bsum (fun _ => BPair.ofNat 1 * BPair.ofNat 1) (List.range 1)
      + bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)
      + BPair.ofNat 1 * bsum (fun _ => BPair.ofNat 1 * BPair.unit) (List.range 1)).oneValue
    (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1)) := by decide +kernel

-- the excess read (`excess_read`) at the scale `[1 : 2]`, the mass
-- `[1 : 2]`, the stated pairs' clearing 3 (the slack's cap and the cap
-- `W_q` at 3, the pairs one), every further coefficient one and the unit's
-- moment two: the flux moments' fold 2 at the deficit's moment 1, the
-- gradient deficit at the index one, the deficit caps 1 and 1 at the
-- clearing, the squares' cap 60 with the slack's 2 read the excess 31,
-- its clearing 2976 at or below the displayed cap 3048, decided and
-- through the theorem; at the squares' cap 62 the cap's binder refuses
-- and the excess 32's clearing 3072 parts
theorem pin97 : BPair.ofNat 31 * (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3
    ≤ BPair.ofNat 192 * (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 + (BPair.ofNat 3 * (BPair.ofNat 24 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 2 * (BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3) * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2 := by
  decide +kernel
theorem pin98 : BPair.ofNat 31 * (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3
    ≤ BPair.ofNat 192 * (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 + (BPair.ofNat 3 * (BPair.ofNat 24 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 2 * (BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3) * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2 :=
  excess_read
    (BPair.ofNat 31) (BPair.ofNat 60) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin99 : ¬ (BPair.ofNat 62 * (BPair.ofNat 2 * BPair.ofNat 2) *
    (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) ≤ BPair.ofNat 96 *
    (BPair.ofNat 1 * ((BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2)) *
    (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) + BPair.ofNat 12 *
    (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 2 * BPair.ofNat 2) *
    (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) + BPair.ofNat 3 *
    ((BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1) * (BPair.ofNat 2 * BPair.ofNat 2) *
    BPair.ofNat 2) := by decide +kernel
theorem pin100 : ¬ (BPair.ofNat 32 * (BPair.ofNat 2 * BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3
    ≤ BPair.ofNat 192 * (BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 + (BPair.ofNat 3 * (BPair.ofNat 24 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 2 * (BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1)) + BPair.ofNat 3) * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 2) := by decide +kernel

-- the mode read (`mode_read`) at the scale `[1 : 2]`, the mass `[1 : 2]`,
-- the solve `[2 : 2]`, the mode read `[1 : 3]`, the side one, `dim G = 1`,
-- the stated pairs' clearing 3 (the slack's cap, `W_q` and `P'` at 3, the
-- pairs one) and the deficits' moment 2: the deficit moments 1 and 2 at
-- the mode weight, the mode square's 1, the squares' cap 72, the slack 3
-- and the fluxes' range read 10 read the form 152 at the deficits'
-- moment, the excess 76, its clearing 10944 at or below the displayed cap
-- 36684, decided and through the theorem; at the range read 11 the second
-- moments' binder refuses and the excess 255's clearing 36720 parts
theorem pin101 : BPair.ofNat 76 * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3
    ≤ BPair.ofNat 16 * BPair.ofNat 1 * (BPair.ofNat 1 + BPair.ofNat 2) * BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 + BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 + (BPair.ofNat 3 * (BPair.ofNat 32 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.ofNat 1) * BPair.ofNat 1 + BPair.ofNat 96 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat 1))) + (BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 6 + BPair.ofNat 1) * BPair.ofNat 3 + BPair.ofNat 4 * (BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat 1)) + BPair.ofNat 3) * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 3 := by
  decide +kernel
theorem pin102 : BPair.ofNat 76 * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3
    ≤ BPair.ofNat 16 * BPair.ofNat 1 * (BPair.ofNat 1 + BPair.ofNat 2) * BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 + BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 + (BPair.ofNat 3 * (BPair.ofNat 32 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.ofNat 1) * BPair.ofNat 1 + BPair.ofNat 96 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat 1))) + (BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 6 + BPair.ofNat 1) * BPair.ofNat 3 + BPair.ofNat 4 * (BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat 1)) + BPair.ofNat 3) * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 3 :=
  mode_read
    (BPair.ofNat 76) (BPair.ofNat 2) (BPair.ofNat 152) (BPair.ofNat 10) (BPair.ofNat 72) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
theorem pin103 : ¬ (BPair.ofNat 11 * BPair.ofNat 3 ≤ BPair.ofNat 8 * (BPair.ofNat 1 * BPair.ofNat 1) *
    BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 + BPair.ofNat 8 * BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 3) := by decide +kernel
theorem pin104 : ¬ (BPair.ofNat 255 * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 * BPair.ofNat 3
    ≤ BPair.ofNat 16 * BPair.ofNat 1 * (BPair.ofNat 1 + BPair.ofNat 2) * BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 * (BPair.ofNat 2 * BPair.ofNat 2) * BPair.ofNat 3 + BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * BPair.ofNat 2 * BPair.ofNat 3 * BPair.ofNat 3 + (BPair.ofNat 3 * (BPair.ofNat 32 * (BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 1 * (BPair.ofNat 1 + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.ofNat 1) * BPair.ofNat 1 + BPair.ofNat 96 * (BPair.ofNat 1 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat 1))) + (BPair.ofNat 384 * (BPair.ofNat 1 * BPair.ofNat 1) + BPair.ofNat 6 + BPair.ofNat 1) * BPair.ofNat 3 + BPair.ofNat 4 * (BPair.ofNat 3 * (BPair.ofNat 1 * BPair.ofNat 1) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat 1)) + BPair.ofNat 3) * (BPair.ofNat 2 * BPair.ofNat 2) * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 3) := by decide +kernel

-- the key's quarters (`key_quarters`) at the excess and the mode read
-- themselves, the two assemblies' conclusions its first two binders with
-- `P_u` and `P_v` read off their groups at the mass's clearing, 372 and
-- 9540: the scale `[1 : 2]`, the mass `[1 : 2]`, the mode read `[1 : 3]`,
-- the stated pairs' clearing 3 and the floor `[1700 : 1]`, the side, mass
-- and scale comparisons at 192 < 5100, 2304 < 6800 and 39648 < 40800, the
-- reads' sum's clearing 214 under the floor's 1700, decided and through
-- the theorem; at the floor `[200 : 1]` the scale comparison refuses,
-- 39648 against 4800, and the sum's 214 parts from 200
theorem pin105 : (BPair.ofNat 31 + BPair.ofNat 76) * BPair.ofNat 2 * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 1700 := by decide +kernel
theorem pin106 : (BPair.ofNat 31 + BPair.ofNat 76) * BPair.ofNat 2 * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 1700 :=
  key_quarters (BPair.ofNat 31) (BPair.ofNat 76) _ _ (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2)
    (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1700) (BPair.ofNat 1) (BPair.ofNat 3)
    (excess_read
    (BPair.ofNat 31) (BPair.ofNat 60) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (mode_read
    (BPair.ofNat 76) (BPair.ofNat 2) (BPair.ofNat 152) (BPair.ofNat 10) (BPair.ofNat 72) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 2) (BPair.ofNat 2) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 1) (BPair.ofNat 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem pin107 : ¬ (BPair.ofNat 4 * (BPair.ofNat 372 + BPair.ofNat 9540) * BPair.ofNat 1 * BPair.ofNat 1
    < BPair.ofNat 3 * BPair.ofNat 200 * BPair.ofNat 2 * (BPair.ofNat 2 * BPair.ofNat 2)) := by decide +kernel
theorem pin108 : ¬ ((BPair.ofNat 31 + BPair.ofNat 76) * BPair.ofNat 2 * BPair.ofNat 1
    < BPair.ofNat 1 * BPair.ofNat 200) := by decide +kernel

end cornerkey
