import MassGap.Cornerkey

/-!
`lem:cornerkey`'s moment tier: the near mass, the near scale, the deficit
cell, the remainder cell and the mode's variance floor, each the tex's
displayed derivation at the trial's moments, the moments and the
displayed reads pair data cleared at the stated pairs' second members.

The near scale: a weight's key comparison reads at its two pairs and
its bit count, the least natural at or beyond one at `2^{j'}` clearing
`P_+` against `ε^k P_-`; at `K := [2 k! (k + j') : ε]` the comparison
`K^{j'} ε^{k+j'} P_- ≥ (k + j')! P_+` holds through the factorial at
the joined key (`near_scale_key`, `ground.factorial_add_le`), the stated
near scale `48 (4 + j')` sits at or beyond `2 k! (k + j')` at every
power at or below four (`near_scale_stated`), and the weight's read at
the power, `μ[P D^k] ≤ 2 (Kη)^k μ[P]`, is the cleared near-scale read
(`ground.near_scale_read`) at the gap read's moment and the far read
against the key comparison (`near_scale_moment`).

The near mass: at every plaquette the return read's chain, the
per-plaquette powers' evaluations, decreasing and convex with its head
at or below the clearing, prices the deficit's read at the return read
through the chain's gap at the concentration key (`ground.chain_gap`),
the deficits' fold then sits under the tolerance's multiple of the
return read's evaluation at the count, and the trial's mass reads at
the near read against the return read: the unit's moment sits at or
beyond the near mass `[1 : 2 c_W k^e]` (`near_mass`).

The deficit cell: the second moments' display doubled at the range
parts and folded over the plaquettes, the deficit's second-order read
and the near scale's read at the second-order members, on the cell's
two comparisons the self-read withdraws at the factor two and the
second-order members read at half the count's multiple of the scale,
`μ[D] ≤ C_D #p η μ[1]` at `C_D := 2 dim G W₀ + 1` (`deficit_read`).

The remainder cell: the first identity's remainder, the derivative's
remainder within `a₁ μ[D]` and the deviation within the dual weights'
fold against `ν[|y_W| D]`, its square at the evaluation's squared
Cauchy--Schwarz and the near scale's reads at the unit weight, reads
its deviation's square at the first identity's own read of `ν[Q]`,
the two-member fold of squares (`ground.leB_sq_selfcap`) and the
cell's first comparison, so `|r₁| ≤ [1 : 16] κ σ_W μ[1]` at the second
comparison (`remainder_one`); the second identity's remainder reads its
three members at the mode square's moments, the derivative's remainder
with the gap's second member within `a₂ μ[Q]` at the third comparison,
the gap's first member at the two-member square, and the deviation at
the fourth, so `|r₂| ≤ [3 : 16] κ σ_W μ[Q]` (`remainder_two`); each
magnitude the sorted pair's (`windowsep.mag`).

The variance floor: at the two remainders' caps and `η (dim G + 2) ≤ 1`
the mode's variance (`mode_variance`) sits at or beyond five eighths of
its leading member (`variance_floor`), its side read at the roots'
floor's solve (`variance_side`), the mode square's moment at or beyond
the lower weight `Q_-` (`mode_lower`), the mode mean's read
`μ[Q]² ≤ dim G μ[1] ⟨v, v⟩` (`mode_mean_read`), and the moments' join at
the variance identity (`mode_square_join`).

The mode weight: its square moment at the near scale on the weights
`Q²` and the unit (`weight_square`), the coordinate identity's leading
member at the mode weight folded over the plaquettes at the two
identities at `u = ω`, `u' = W` (`weight_lead`), and the deficits' fold
at the mode weight, `μ[ZD] ≤ (C_Z η + P' η²) ⟨v, v⟩` at the coordinate
identity summed over the plaquettes and the deficit's second-order read
(`weight_deficit`).

The join: the moments' key read joins the tier's reads to the excess
and the mode read at the stated pairs and the clearing
(`key_moments`), and the tail read at the key's data instantiates it at
the member and window reads, the scale `[1 : 2^i]`, the mass
`[1 : 2^{i_ε}]` and the near scale, the concentration key's and bit
comparisons' reads (`kc_ge_jK`, `conc_key_read`, `bit_unit`, `bit_mode`,
`bit_msq`) and the key's list read at the cell's comparisons, closing
at the tail read (`moment_tail`, `tail_read`).
-/
namespace cornerkey
open ground

/-! The near scale. -/

/-- The near scale's key comparison at a weight's two pairs and its
bit count, the display at the mass's second member `E` at
`ε = [1 : E]`: at `2^{j'} P_- ≥ E^k P_+`, the factorial at the joined
key against `E^k P_+` sits at or below `(2 k! (k + j'))^{j'} P_-`, the
factorial under the shift's power against the head's
(`ground.factorial_add_le`) and the head's factorial under its own
power at an occupied bit count. -/
theorem near_scale_key (k j' : Nat) (E Pp Pm : BPair) (hj : 1 ≤ j')
    (hE : BPair.unit ≤ E) (hPp : BPair.unit ≤ Pp)
    (hbit : bpow E k * Pp ≤ bpow (BPair.ofNat 2) j' * Pm) :
    BPair.ofNat (factorial (k + j')) * (bpow E k * Pp)
      ≤ bpow (BPair.ofNat (2 * factorial k * (k + j'))) j' * Pm := by
  have hfk : BPair.ofPos .one ≤ BPair.ofNat (factorial k) := leB_ofNat (factorial_pos k)
  have hkj : BPair.unit ≤ bpow (BPair.ofNat (k + j')) j' := unitLeBpow (unitLeOfNat _) j'
  have hkf : BPair.unit ≤ bpow (BPair.ofNat (factorial k)) j' := unitLeBpow (unitLeOfNat _) j'
  -- the factorial at the joined key under the two powers
  have h2 : BPair.ofNat (factorial (k + j'))
      ≤ bpow (BPair.ofNat (factorial k)) j' * bpow (BPair.ofNat (k + j')) j' := by
    refine leB_trans (leB_ofNat (factorial_add_le k j')) ?_
    refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (bpow_ofNat (k + j') j') (BPair.oneValue_refl _)))) ?_
    refine leB_congr_left (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
    exact leB_mulL hkj (le_bpow_self hfk j' hj)
  -- the stated near scale's power at its three factors
  have e1 : (bpow (BPair.ofNat (2 * factorial k * (k + j'))) j').oneValue
      (bpow (BPair.ofNat 2) j' * bpow (BPair.ofNat (factorial k)) j'
        * bpow (BPair.ofNat (k + j')) j') := by
    refine BPair.oneValue_trans (bpow_congr (BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (BPair.ofNat_mul _ _) (BPair.oneValue_refl _))) j') ?_
    refine BPair.oneValue_trans (bpow_mul _ _ j') ?_
    exact BPair.mul_congr (bpow_mul _ _ j') (BPair.oneValue_refl _)
  refine leB_trans (leB_mulL (unitLeMul (unitLeBpow hE k) hPp) h2) ?_
  refine leB_trans (leB_mulR (unitLeMul hkf hkj) hbit) ?_
  refine leB_congr_right (BPair.oneValue_symm (BPair.mul_congr_left e1)) ?_
  refine leB_congr_left (BPair.oneValue_of_eq ?_) (leB_refl _)
  rw [← BPair.mul_assoc, BPair.mul_comm (bpow (BPair.ofNat (factorial k)) j'
    * bpow (BPair.ofNat (k + j')) j') (bpow (BPair.ofNat 2) j'), ← BPair.mul_assoc]

/-- The stated near scale's coefficient `48 (4 + j')` sits at or beyond
`2 k! (k + j')` at every power `k` at or below four, the fourth power's
own read at equality. -/
theorem near_scale_stated (k j' : Nat) (hk : k ≤ 4) :
    2 * factorial k * (k + j') ≤ 48 * (4 + j') := by
  have hf : ∀ k', k' < 5 → factorial k' ≤ 24 := by decide
  have h1 : 2 * factorial k ≤ 48 := Nat.mul_le_mul_left 2 (hf k (Nat.lt_succ_of_le hk))
  exact Nat.mul_le_mul h1 (Nat.add_le_add_right hk j')

/-- A weight's read at a power at the near scale, `μ[P D^k] ≤ 2 (Kη)^k
μ[P]`, cleared at the scale pair `[n : s]` and the mass's second member
`E`: the gap read's moment `μ[P D^k] ≤ (Kη)^k μ[P] + μ[P D^{k+j'}] /
(Kη)^{j'}` at the near scale `K := Kn E` beyond the key's coefficient,
the far read `μ[P D^{k+j'}] ≤ (k + j')! η^{k+j'} [1 : ε^{k+j'}] P_+`,
and the weight's bit count: the far read against the key comparison
puts the raised moment under the raised power's multiple of the weight's
moment, at or beyond `P_-`, and the cleared near-scale read closes
(`ground.near_scale_read`). -/
theorem near_scale_moment (A B C n s E Kn Pp Pm : BPair) (k j' : Nat) (hj : 1 ≤ j')
    (hn : BPair.unit < n) (hE : BPair.ofPos .one ≤ E)
    (hKn : BPair.ofNat (2 * factorial k * (k + j')) ≤ Kn) (hPp : BPair.unit ≤ Pp)
    (hA : A * bpow (Kn * E * n) j' * bpow s k
      ≤ bpow (Kn * E * n) (k + j') * B + bpow s (k + j') * C)
    (hfar : bpow s (k + j') * C
      ≤ BPair.ofNat (factorial (k + j')) * bpow n (k + j') * bpow E (k + j') * Pp)
    (hbit : bpow E k * Pp ≤ bpow (BPair.ofNat 2) j' * Pm)
    (hPm : Pm ≤ B) :
    A * bpow s k ≤ BPair.ofNat 2 * (bpow (Kn * E * n) k * B) := by
  have hone : BPair.unit ≤ BPair.ofPos .one := leB_of_lt (unitLtOfPos .one)
  have hE0 : BPair.unit ≤ E := leB_trans hone hE
  have hE1 : BPair.unit < E := ltB_trans_le (unitLtOfPos .one) hE
  have hKn1 : BPair.ofPos .one ≤ Kn :=
    leB_trans (leB_ofNat (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) (factorial_pos k))
      (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hj) (Nat.le_add_left j' k)))) hKn
  have hKn0 : BPair.unit ≤ Kn := leB_trans hone hKn1
  have hKnp : BPair.unit < Kn := ltB_trans_le (unitLtOfPos .one) hKn1
  have hz : BPair.unit < Kn * E * n := unitLtMul (unitLtMul hKnp hE1) hn
  have hPm0 : BPair.unit ≤ Pm := by
    have h0 : BPair.unit ≤ bpow (BPair.ofNat 2) j' * Pm :=
      leB_trans (unitLeMul (unitLeBpow hE0 k) hPp) hbit
    exact leB_unscale_left (unitLtBpow (unitLtOfNat 1) j')
      (leB_congr_left (BPair.oneValue_symm (BPair.mul_unit _)) h0)
  have hB : BPair.unit ≤ B := leB_trans hPm0 hPm
  have hkey := near_scale_key k j' E Pp Pm hj hE0 hPp hbit
  -- the far read's members regrouped at the key comparison's read
  have e1 : (BPair.ofNat (factorial (k + j')) * bpow n (k + j') * bpow E (k + j') * Pp).oneValue
      (bpow n (k + j') * bpow E j' * (BPair.ofNat (factorial (k + j')) * (bpow E k * Pp))) := by
    refine BPair.oneValue_trans (BPair.mul_congr_left
      (BPair.mul_congr (BPair.oneValue_refl _) (bpow_add E k j'))) ?_
    exact polEqB [(BPair.ofNat (factorial (k + j'))), (bpow n (k + j')), (bpow E k), (bpow E j'), Pp]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 3))) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 3)) (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 2) (Mon.var 4))))) (by decide +kernel)
  have hC : bpow s (k + j') * C ≤ bpow (Kn * E * n) (k + j') * B := by
    refine leB_trans hfar (leB_congr_left (BPair.oneValue_symm e1) ?_)
    have hnE : BPair.unit ≤ bpow n (k + j') * bpow E j' :=
      unitLeMul (unitLeBpow (leB_of_lt hn) _) (unitLeBpow hE0 _)
    refine leB_trans (leB_mulR hnE hkey) ?_
    refine leB_trans (leB_mulR hnE (leB_mul_mono hPm0 (unitLeBpow hKn0 j')
      (bpow_mono (unitLeOfNat _) hKn j') hPm)) ?_
    -- the two powers at the bit count under the raised key's
    have hEp : bpow E j' ≤ bpow E (k + j') := by
      refine leB_congr_right (BPair.oneValue_symm (bpow_add E k j')) ?_
      refine leB_congr_left (BPair.ofPos_one_mul _) ?_
      exact leB_mulL (unitLeBpow hE0 j') (oneLeBpow hE k)
    have hKp : bpow Kn j' ≤ bpow Kn (k + j') := by
      refine leB_congr_right (BPair.oneValue_symm (bpow_add Kn k j')) ?_
      refine leB_congr_left (BPair.ofPos_one_mul _) ?_
      exact leB_mulL (unitLeBpow hKn0 j') (oneLeBpow hKn1 k)
    have hstep : bpow Kn j' * bpow E j' * (bpow n (k + j') * B)
        ≤ bpow Kn (k + j') * bpow E (k + j') * (bpow n (k + j') * B) :=
      leB_mulL (unitLeMul (unitLeBpow (leB_of_lt hn) _) hB)
        (leB_mul_mono (unitLeBpow hE0 j') (unitLeBpow hKn0 _) hKp hEp)
    refine leB_congr (?_) ?_ hstep
    · exact polEqB [(bpow Kn j'), (bpow E j'), (bpow n (k + j')), B]
          (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 3))))
          (Pol.mon (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 1)) (Mon.mul (Mon.var 0) (Mon.var 3)))) (by decide +kernel)
    · refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
      refine BPair.mul_congr_left ?_
      refine BPair.oneValue_symm ?_
      exact BPair.oneValue_trans (bpow_mul _ _ _) (BPair.mul_congr (bpow_mul _ _ _)
        (BPair.oneValue_refl _))
  exact near_scale_read A B C (Kn * E * n) s k j' hz hA hC

/-- The near-scale read at a weight cleared at a stated datum `c`: the
weight's cap `P_+` and lower weight `P_-` enter at the clearing,
`E^k (c P_+) ≤ 2^{j'} P_-` and `P_- ≤ c μ[P]`, the gap read's moment and
the far read scaled by `c` through the product's monotonicity, the
near scale `K := K_n E` the product of its coefficient with the mass's
second member (`ground.bpow_mul`), and the clearing withdraws at the
conclusion: `μ[P D^k] s^k ≤ 2 K^k n^k μ[P]`. -/
theorem near_read (A B C n s E Kn K Pp Pm c : BPair) (k j' : Nat) (hj : 1 ≤ j')
    (hn : BPair.unit < n) (hE : BPair.ofPos .one ≤ E)
    (hKn : BPair.ofNat (2 * factorial k * (k + j')) ≤ Kn) (hK : (Kn * E).oneValue K)
    (hPp : BPair.unit ≤ Pp) (hc : BPair.unit < c)
    (hA : A * bpow (Kn * E * n) j' * bpow s k
      ≤ bpow (Kn * E * n) (k + j') * B + bpow s (k + j') * C)
    (hfar : bpow s (k + j') * C
      ≤ BPair.ofNat (factorial (k + j')) * bpow n (k + j') * bpow E (k + j') * Pp)
    (hbit : bpow E k * (c * Pp) ≤ bpow (BPair.ofNat 2) j' * Pm)
    (hPm : Pm ≤ c * B) :
    A * bpow s k ≤ BPair.ofNat 2 * (bpow K k * bpow n k * B) := by
  have hc0 : BPair.unit ≤ c := leB_of_lt hc
  have hA' : c * A * bpow (Kn * E * n) j' * bpow s k
      ≤ bpow (Kn * E * n) (k + j') * (c * B) + bpow s (k + j') * (c * C) := by
    have h := leB_mulR hc0 hA
    rw [BPair.left_distrib] at h
    refine leB_congr (?_)
      (BPair.add_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_)) h
    · exact BPair.oneValue_of_eq (show c * (A * bpow (Kn * E * n) j' * bpow s k) = c * A * bpow (Kn * E * n) j' * bpow s k by repeat rw [← BPair.mul_assoc])
    · exact BPair.mul_left_comm _ _ _
    · exact BPair.mul_left_comm _ _ _
  have hfar' : bpow s (k + j') * (c * C)
      ≤ BPair.ofNat (factorial (k + j')) * bpow n (k + j') * bpow E (k + j') * (c * Pp) := by
    have h := leB_mulR hc0 hfar
    refine leB_congr (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _))
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) h
  have h := near_scale_moment (c * A) (c * B) (c * C) n s E Kn (c * Pp) Pm k j' hj hn hE hKn
    (unitLeMul hc0 hPp) hA' hfar' hbit hPm
  refine leB_unscale_left hc ?_
  refine leB_congr (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_ h
  have hPQ : (bpow (Kn * E * n) k).oneValue (bpow K k * bpow n k) :=
    BPair.oneValue_trans (bpow_mul (Kn * E) n k) (BPair.mul_congr_left (bpow_congr hK k))
  refine BPair.oneValue_trans ((polEqB [(bpow (Kn * E * n) k), c, B]
    (Pol.mon (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 2)))))
    (Pol.mon (Mon.mul (Mon.var 1) (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 2))))) (by decide +kernel))) ?_
  exact BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.mul_congr_left hPQ))

/-- The near-scale read at the first power, `μ[P D] s ≤ 2 K n μ[P]`. -/
theorem near_read_one (A B C n s E Kn K Pp Pm c : BPair) (j' : Nat) (hj : 1 ≤ j')
    (hn : BPair.unit < n) (hE : BPair.ofPos .one ≤ E)
    (hKn : BPair.ofNat (2 * (1 + j')) ≤ Kn) (hK : (Kn * E).oneValue K)
    (hPp : BPair.unit ≤ Pp) (hc : BPair.unit < c)
    (hA : A * bpow (Kn * E * n) j' * s ≤ bpow (Kn * E * n) (1 + j') * B + bpow s (1 + j') * C)
    (hfar : bpow s (1 + j') * C
      ≤ BPair.ofNat (factorial (1 + j')) * bpow n (1 + j') * bpow E (1 + j') * Pp)
    (hbit : E * (c * Pp) ≤ bpow (BPair.ofNat 2) j' * Pm)
    (hPm : Pm ≤ c * B) :
    A * s ≤ BPair.ofNat 2 * K * n * B := by
  have h := near_read A B C n s E Kn K Pp Pm c 1 j' hj hn hE
    (by
      refine leB_congr_left (BPair.oneValue_of_eq ?_) hKn
      show BPair.ofNat (2 * (1 + j')) = BPair.ofNat (2 * 1 * (1 + j'))
      rw [Nat.mul_one]) hK hPp hc
    (leB_congr_left (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (bpow_one_read s)))
      hA) hfar
    (leB_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (bpow_one_read E))) hbit) hPm
  refine leB_congr (BPair.mul_congr (BPair.oneValue_refl _) (bpow_one_read s)) ?_ h
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.mul_congr (BPair.mul_congr (bpow_one_read K) (bpow_one_read n)) (BPair.oneValue_refl _))) ?_
  exact BPair.oneValue_of_eq (show BPair.ofNat 2 * (K * n * B) = BPair.ofNat 2 * K * n * B by repeat rw [← BPair.mul_assoc])

/-- The near-scale read at the second power,
`μ[P D²] s² ≤ 2 K² n² μ[P]`. -/
theorem near_read_two (A B C n s E Kn K Pp Pm c : BPair) (j' : Nat) (hj : 1 ≤ j')
    (hn : BPair.unit < n) (hE : BPair.ofPos .one ≤ E)
    (hKn : BPair.ofNat (4 * (2 + j')) ≤ Kn) (hK : (Kn * E).oneValue K)
    (hPp : BPair.unit ≤ Pp) (hc : BPair.unit < c)
    (hA : A * bpow (Kn * E * n) j' * (s * s)
      ≤ bpow (Kn * E * n) (2 + j') * B + bpow s (2 + j') * C)
    (hfar : bpow s (2 + j') * C
      ≤ BPair.ofNat (factorial (2 + j')) * bpow n (2 + j') * bpow E (2 + j') * Pp)
    (hbit : E * E * (c * Pp) ≤ bpow (BPair.ofNat 2) j' * Pm)
    (hPm : Pm ≤ c * B) :
    A * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * B := by
  have e2 : ∀ x : BPair, (bpow x 2).oneValue (x * x) := fun x =>
    BPair.oneValue_trans (bpow_succ_read x 1)
      (BPair.mul_congr (BPair.oneValue_refl _) (bpow_one_read x))
  have h := near_read A B C n s E Kn K Pp Pm c 2 j' hj hn hE
    (by
      refine leB_congr_left (BPair.oneValue_of_eq ?_) hKn
      show BPair.ofNat (4 * (2 + j')) = BPair.ofNat (2 * 2 * (2 + j'))
      rfl) hK hPp hc
    (leB_congr_left (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (e2 s))) hA) hfar
    (leB_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (e2 E))) hbit) hPm
  refine leB_congr (BPair.mul_congr (BPair.oneValue_refl _) (e2 s)) ?_ h
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.mul_congr (BPair.mul_congr (e2 K) (e2 n)) (BPair.oneValue_refl _))) ?_
  exact BPair.oneValue_of_eq (show BPair.ofNat 2 * (K * K * (n * n) * B) = BPair.ofNat 2 * (K * K) * (n * n) * B by repeat rw [← BPair.mul_assoc])

/-! The near mass. -/

/-- The near mass, `μ[1] ≥ ϑ := [1 : 2 c_W k^e]`, cleared at the
moments' clearing `Δ`, the scale pair `[n : s]` and the mass's second
member `E`: at every plaquette the return read's chain `b`, its head
at or below the clearing, occupied to the raised power, decreasing
there and convex, with the return read's evaluation `E_Q` at the power,
the raised power's evaluation at or beyond the clearing against the
support weight `W_+`, and the key comparison at the tolerance
`τ := [n E : τ_D]`, `W_+ τ_D^{e+1} ≤ C(k + 1, e + 1) (n E)^{e+1}`
(`ground.chain_gap`), prices the deficit's read at the return read,
`Eval(δ_p Q) ≤ 2 d_θ (b_k − b_{k+1})`, at the tolerance's multiple of
`E_Q`; the near read, `μ[1] ≥ E_Q − 2 [s : n] ([L : 2] + ε) Σ_p
Eval(δ_p Q)` cleared at `n E`, at the tolerance's second member
`τ_D = 4 d_θ #p (L E + 2) s` then reads `2 μ[1] ≥ E_Q`, and `E_Q` at or
beyond the support weight's reciprocal closes at
`W_k ≤ c_W k^e`. -/
theorem near_mass (P k e cW : Nat) (b : Nat → Nat → BPair) (dQ : Nat → BPair)
    (Δ EQ Wp Wk mu1 n s E L dth τD : BPair)
    (hn : BPair.unit < n) (hE : BPair.unit < E) (hτD : BPair.unit < τD)
    (hdth : BPair.unit ≤ dth) (hL : BPair.unit ≤ L) (hs : BPair.unit ≤ s) (hWk0 : BPair.unit ≤ Wk)
    (hb0 : ∀ p, p < P → b p 0 ≤ Δ)
    (hpos : ∀ p, p < P → ∀ i, i ≤ k + 1 → BPair.unit < b p i)
    (hdec : ∀ p, p < P → b p (k + 1) ≤ b p k)
    (hconv : ∀ p, p < P → ∀ i, i + 1 ≤ k → b p (i + 1) * b p (i + 1) ≤ b p i * b p (i + 2))
    (hEQ : ∀ p, p < P → (b p k).oneValue EQ)
    (hW : ∀ p, p < P → Δ ≤ Wp * b p (k + 1))
    (hkey : Wp * bpow τD (e + 1) ≤ BPair.ofNat (pasc (k + 1) (e + 1)) * bpow (n * E) (e + 1))
    (he : e + 1 ≤ k + 1)
    (hδ : ∀ p, p < P → dQ p ≤ BPair.ofNat 2 * dth * (b p k + (b p (k + 1)).swap))
    (hnear : n * E * EQ + (s * (L * E + BPair.ofNat 2) * bsum dQ (List.range P)).swap
      ≤ n * E * mu1)
    (hτ : τD.oneValue (BPair.ofNat 4 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s))
    (hEW : Δ ≤ Wk * EQ) (hWk : Wk ≤ BPair.ofNat (cW * k ^ e)) (hEQ0 : BPair.unit ≤ EQ) :
    Δ ≤ BPair.ofNat (2 * cW * k ^ e) * mu1 := by
  have hnE0 : BPair.unit < n * E := unitLtMul hn hE
  have hnE : BPair.unit ≤ n * E := leB_of_lt hnE0
  have h2d : BPair.unit ≤ BPair.ofNat 2 * dth := unitLeMul (unitLeOfNat 2) hdth
  -- per plaquette the deficit's read at the tolerance's multiple of the evaluation
  have hgap : ∀ p, p < P → τD * dQ p ≤ BPair.ofNat 2 * dth * (n * E) * EQ := by
    intro p hp
    have hcg := chain_gap (b p) k e Δ Wp (n * E) τD (hb0 p hp) (hpos p hp) (hdec p hp)
      (hconv p hp) hnE hτD he (hW p hp) hkey
    have h1 : τD * (b p k + (b p (k + 1)).swap) ≤ n * E * b p k := by
      rw [BPair.left_distrib, BPair.mul_swap]
      have h := leB_add hcg (leB_refl (τD * b p (k + 1)).swap)
      refine leB_congr_right ?_ h
      refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_swap_null _)) (BPair.add_unit _)
    refine leB_trans (leB_mulR (leB_of_lt hτD) (hδ p hp)) ?_
    refine leB_congr_left (BPair.oneValue_of_eq
      (BPair.mul_left_comm τD (BPair.ofNat 2 * dth) (b p k + (b p (k + 1)).swap)).symm) ?_
    refine leB_trans (leB_mulR h2d h1) ?_
    refine leB_congr_left (BPair.oneValue_of_eq
      (BPair.mul_assoc (BPair.ofNat 2 * dth) (n * E) (b p k))) ?_
    exact leB_congr_right (BPair.mul_congr (BPair.oneValue_refl _) (hEQ p hp)) (leB_refl _)
  -- the deficits' fold at the count
  have hsum : τD * bsum dQ (List.range P)
      ≤ BPair.ofNat P * (BPair.ofNat 2 * dth * (n * E) * EQ) := by
    refine leB_congr_left (foldB_mul_left τD dQ (List.range P)) ?_
    refine leB_trans (bsum_le_of_mem (fun p => τD * dQ p)
      (fun _ => BPair.ofNat 2 * dth * (n * E) * EQ) (List.range P)
      (fun p hp => hgap p (ltOfMemRange hp))) ?_
    refine leB_congr_left (BPair.oneValue_symm (foldB_const _ (List.range P))) ?_
    rw [length_range]
    exact leB_refl _
  -- the tolerance's second member at its half
  have hτ2 : τD.oneValue (BPair.ofNat 2
      * (BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s)) := by
    refine BPair.oneValue_trans hτ ?_
    exact polEqB [dth, (BPair.ofNat P), L, E, s]
        (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4)))
        (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4)))) (by decide +kernel)
  have hH : BPair.unit < BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s :=
    unitLt_unscale (unitLeOfNat 2) (BPair.lt_congr (BPair.oneValue_refl _) hτ2 hτD)
  -- the near read at the tolerance
  have h3 : τD * (n * E * EQ)
      ≤ τD * (n * E * mu1) + τD * (s * (L * E + BPair.ofNat 2) * bsum dQ (List.range P)) := by
    have h := leB_mulR (leB_of_lt hτD) (leB_swapL hnear)
    rw [BPair.left_distrib] at h
    exact h
  have h4 : τD * (s * (L * E + BPair.ofNat 2) * bsum dQ (List.range P))
      ≤ BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s * (n * E * EQ) := by
    have hsL : BPair.unit ≤ s * (L * E + BPair.ofNat 2) :=
      unitLeMul hs (unitLeAdd (unitLeMul hL (leB_of_lt hE)) (unitLeOfNat 2))
    refine leB_congr_left (BPair.oneValue_of_eq
      (BPair.mul_left_comm τD (s * (L * E + BPair.ofNat 2)) (bsum dQ (List.range P))).symm) ?_
    refine leB_trans (leB_mulR hsL hsum) ?_
    refine leB_congr_left (?_) (leB_refl _)
    exact polEqB [dth, (BPair.ofNat P), L, E, s, n, EQ]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 3)) (Mon.var 6))))
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 1) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.mul (Mon.var 5) (Mon.var 3))) (Mon.var 6))))) (by decide +kernel)
  -- the evaluation under twice the unit's moment
  have h5 : BPair.ofNat 2 * (BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s)
        * (n * E * EQ)
      ≤ BPair.ofNat 2 * (BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s)
          * (n * E * mu1)
        + BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s * (n * E * EQ) :=
    leB_congr (BPair.mul_congr_left hτ2)
      (BPair.add_congr (BPair.mul_congr_left hτ2) (BPair.oneValue_refl _))
      (leB_trans h3 (leB_add (leB_refl _) h4))
  have h6 : n * E * EQ ≤ BPair.ofNat 2 * (n * E * mu1) := by
    have h7 : BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s * (n * E * EQ)
          + BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s * (n * E * EQ)
        ≤ BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s
            * (BPair.ofNat 2 * (n * E * mu1))
          + BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2) * s * (n * E * EQ) := by
      refine leB_congr ?_ (BPair.add_congr ?_ (BPair.oneValue_refl _)) h5
      · exact polEqB [dth, (BPair.ofNat P), L, E, s, n, EQ]
            (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4)))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 3)) (Mon.var 6))))
            (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 3)) (Mon.var 6)))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 3))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 3)) (Mon.var 6))))) (by decide +kernel)
      · exact BPair.oneValue_of_eq (BPair.mul_left_comm' _ _ _).symm
    have h8 := leB_cancelL (x := BPair.ofNat 2 * dth * BPair.ofNat P * (L * E + BPair.ofNat 2)
      * s * (n * E * EQ)) (leB_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq (BPair.add_comm _ _)) h7)
    exact leB_unscale_left hH h8
  have hEQ2 : EQ ≤ BPair.ofNat 2 * mu1 :=
    leB_unscale_left hnE0 (leB_congr_right (BPair.oneValue_of_eq
      (BPair.mul_left_comm (BPair.ofNat 2) (n * E) mu1)) h6)
  have hmu0 : BPair.unit ≤ mu1 :=
    unitLeUnscale (unitLtOfNat 1) (leB_trans hEQ0 hEQ2)
  refine leB_trans hEW ?_
  refine leB_trans (leB_mulR hWk0 hEQ2) ?_
  refine leB_trans (leB_mulL (unitLeMul (unitLeOfNat 2) hmu0) hWk) ?_
  refine leB_congr_right ?_ (leB_refl _)
  refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_mul cW (k ^ e))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (BPair.mul_left_comm' (BPair.ofNat cW * BPair.ofNat (k ^ e)) (BPair.ofNat 2) mu1)) ?_
  refine BPair.mul_congr_left ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.ofNat_mul (2 * cW) (k ^ e)) ?_
  refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_mul 2 cW)) ?_
  exact BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)


/-! The deficit cell. -/

/-- The deficit cell's read, `μ[D] ≤ C_D #p η μ[1]` at `C_D := 2 dim G
W₀ + 1`, cleared at the scale pair `[n : s]`, the index `κ` and the
stated pairs' clearing `cc`: the second moments' display folded over
the plaquettes, `Σ_p ν[|y_Π e_p|²] ≤ #p (η κ dim G W₀ μ[1] + η C₁ ϱ₁
μ[D] + C₁² T_R² ν[D²])`, the fluxes' range parts against the deficits
`Σ_p μ[|f_p|²] ≤ 2 Σ_p μ[|y_Π e_p|²] + 2 c_off μ[D²]` at `μ ≤ ν` and
`ν[D²] ≤ 2 μ[D²]`, the near scale's read `μ[D²] ≤ 2 (Kη)² μ[1]`, and the
deficit's second-order read `μ[D] ≤ [1 : 2κ] Σ_p μ[|f_p|²] + c'_q μ[D²]`
at `c'_q = [cqp : cc]`; on the cell's two comparisons, `2 #p η C₁ ϱ₁
≤ κ` and `η K² (8 [1 : κ] C₁² T_R² + 4 [1 : κ] c_off + 4 c'_q) ≤ 1`, the
self-read withdraws at the factor two and the second-order members
read at or below half the count's multiple of the scale's multiple of
`μ[1]`. -/
theorem deficit_read (mD mD2 mu1 nuY muY nuD2 sf n s kappa dG W0 C1 rho1 TR coff cqp cc K P
      : BPair)
    (hy : nuY * s ≤ P * (n * (kappa * dG * W0 * mu1 + C1 * rho1 * mD)
      + C1 * C1 * TR * TR * nuD2 * s))
    (hmuY : muY ≤ nuY)
    (hf : sf ≤ BPair.ofNat 2 * muY + BPair.ofNat 2 * coff * mD2)
    (hnuD2 : nuD2 ≤ BPair.ofNat 2 * mD2)
    (hmD2 : mD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * mu1)
    (hdef : BPair.ofNat 2 * kappa * cc * mD ≤ cc * sf + BPair.ofNat 2 * kappa * cqp * mD2)
    (hD1 : BPair.ofNat 2 * P * n * C1 * rho1 ≤ kappa * s)
    (hD2 : n * (K * K) * (BPair.ofNat 8 * cc * (C1 * C1 * TR * TR) + BPair.ofNat 4 * cc * coff
      + BPair.ofNat 4 * kappa * cqp) ≤ kappa * cc * s)
    (hn : BPair.unit ≤ n) (hs0 : BPair.unit < s) (hkappa0 : BPair.unit < kappa)
    (hcc0 : BPair.unit < cc) (hP : BPair.ofPos .one ≤ P) (hmu1 : BPair.unit ≤ mu1)
    (hmD : BPair.unit ≤ mD) (hC1 : BPair.unit ≤ C1)
    (hTR : BPair.unit ≤ TR) (hcoff : BPair.unit ≤ coff) (hcqp : BPair.unit ≤ cqp)
    (hK : BPair.unit ≤ K) :
    mD * s ≤ (BPair.ofNat 2 * dG * W0 + BPair.ofNat 1) * P * n * mu1 := by
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hkappa : BPair.unit ≤ kappa := leB_of_lt hkappa0
  have hcc : BPair.unit ≤ cc := leB_of_lt hcc0
  have hP0 : BPair.unit ≤ P := leB_trans (leB_of_lt (unitLtOfPos .one)) hP
  have hss : BPair.unit ≤ s * s := unitLeMul hs hs
  have h2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  -- the second-order read at the scale's square
  have S1 : BPair.ofNat 2 * kappa * cc * mD * s * s
      ≤ cc * sf * s * s + BPair.ofNat 2 * kappa * cqp * mD2 * s * s := by
    have h := leB_mulL hss hdef
    rw [BPair.right_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    exact h
  -- the range parts' fold
  have S2 : cc * sf * s * s
      ≤ cc * BPair.ofNat 2 * muY * s * s + cc * BPair.ofNat 2 * coff * mD2 * s * s := by
    have h := leB_mulL hss (leB_mulR hcc hf)
    rw [BPair.left_distrib, BPair.right_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    exact h
  -- the moments' order at the range parts
  have S3 : cc * BPair.ofNat 2 * muY * s * s ≤ cc * BPair.ofNat 2 * nuY * s * s :=
    leB_mulL hs (leB_mulL hs (leB_mulR (unitLeMul hcc h2) hmuY))
  -- the second moments' display at the count
  have S4 : cc * BPair.ofNat 2 * nuY * s * s
      ≤ cc * BPair.ofNat 2 * P * n * kappa * dG * W0 * mu1 * s
        + cc * BPair.ofNat 2 * P * n * C1 * rho1 * mD * s
        + cc * BPair.ofNat 2 * P * C1 * C1 * TR * TR * nuD2 * s * s := by
    have h := leB_mulL hs (leB_mulR (unitLeMul hcc h2) hy)
    repeat rw [BPair.left_distrib] at h
    repeat rw [BPair.right_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    exact h
  -- the fluxes' second moment at the near scale
  have S5 : cc * BPair.ofNat 2 * P * C1 * C1 * TR * TR * nuD2 * s * s
      ≤ P * BPair.ofNat 8 * cc * C1 * C1 * TR * TR * K * K * n * n * mu1 := by
    have a : nuD2 * (s * s) ≤ BPair.ofNat 2 * (BPair.ofNat 2 * (K * K) * (n * n) * mu1) := by
      refine leB_trans (leB_mulL hss hnuD2) ?_
      rw [BPair.mul_assoc]
      exact leB_mulR h2 hmD2
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul hcc h2) hP0) hC1) hC1) hTR) hTR) a
    repeat rw [← BPair.mul_assoc] at h
    refine leB_congr_right ?_ h
    exact polEqB [cc, P, C1, TR, K, n, mu1]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.cst 2)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 8)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  -- the self-read at the cell's first comparison
  have S6 : cc * BPair.ofNat 2 * P * n * C1 * rho1 * mD * s ≤ kappa * cc * mD * s * s := by
    have h := leB_mulL (unitLeMul (unitLeMul hcc hmD) hs) hD1
    repeat rw [← BPair.mul_assoc] at h
    refine leB_congr (?_) (?_) h
    · exact polEqB [P, n, C1, rho1, cc, mD, s]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
    · exact polEqB [kappa, s, cc, mD]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1))) (by decide +kernel)
  -- the two remaining second-order members at the near scale and the count
  have hX : BPair.unit ≤ K * K * n * n * mu1 :=
    unitLeMul (unitLeMul (unitLeMul (unitLeMul hK hK) hn) hn) hmu1
  have S7a : cc * BPair.ofNat 2 * coff * mD2 * s * s
      ≤ P * BPair.ofNat 4 * cc * coff * K * K * n * n * mu1 := by
    have h := leB_mulR (unitLeMul (unitLeMul hcc h2) hcoff) hmD2
    repeat rw [← BPair.mul_assoc] at h
    refine leB_trans (leB_congr_right
      (y' := BPair.ofNat 4 * cc * coff * K * K * n * n * mu1) ?_ h) ?_
    · exact polEqB [cc, coff, K, n, mu1]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
    · have h' := leB_congr_left (BPair.mul_congr_left (BPair.ofPos_one_mul _))
        (leB_mulL hX (leB_mulL (unitLeMul (unitLeMul (unitLeOfNat 4) hcc) hcoff) hP))
      repeat rw [← BPair.mul_assoc] at h'
      exact h'
  have S7b : BPair.ofNat 2 * kappa * cqp * mD2 * s * s
      ≤ P * BPair.ofNat 4 * kappa * cqp * K * K * n * n * mu1 := by
    have h := leB_mulR (unitLeMul (unitLeMul h2 hkappa) hcqp) hmD2
    repeat rw [← BPair.mul_assoc] at h
    refine leB_trans (leB_congr_right
      (y' := BPair.ofNat 4 * kappa * cqp * K * K * n * n * mu1) ?_ h) ?_
    · exact polEqB [kappa, cqp, K, n, mu1]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
    · have h' := leB_congr_left (BPair.mul_congr_left (BPair.ofPos_one_mul _))
        (leB_mulL hX (leB_mulL (unitLeMul (unitLeMul (unitLeOfNat 4) hkappa) hcqp) hP))
      repeat rw [← BPair.mul_assoc] at h'
      exact h'
  -- the second-order members' sum at the cell's second comparison
  have S8 : P * BPair.ofNat 8 * cc * C1 * C1 * TR * TR * K * K * n * n * mu1
        + P * BPair.ofNat 4 * cc * coff * K * K * n * n * mu1
        + P * BPair.ofNat 4 * kappa * cqp * K * K * n * n * mu1
      ≤ P * n * mu1 * kappa * cc * s := by
    have h := leB_mulR (unitLeMul (unitLeMul hP0 hn) hmu1) hD2
    repeat rw [← BPair.mul_assoc] at h
    refine leB_congr_left (?_) h
    exact polEqB [P, n, mu1, K, cc, C1, TR, coff, kappa, cqp]
        (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 3))) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 8)) (Mon.var 9)))))
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 3)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 4)) (Mon.var 4)) (Mon.var 7)) (Mon.var 3)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 4)) (Mon.var 8)) (Mon.var 9)) (Mon.var 3)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))) (by decide +kernel)
  -- the assembly: the second-order read at the reads' sum
  have S9 : BPair.ofNat 2 * kappa * cc * mD * s * s
      ≤ cc * BPair.ofNat 2 * P * n * kappa * dG * W0 * mu1 * s + kappa * cc * mD * s * s
        + P * n * mu1 * kappa * cc * s := by
    refine leB_trans S1 (leB_trans (leB_add S2 (leB_refl _)) ?_)
    refine leB_trans (leB_add (leB_add S3 (leB_refl _)) (leB_refl _)) ?_
    refine leB_trans (leB_add (leB_add S4 (leB_refl _)) (leB_refl _)) ?_
    refine leB_trans (leB_add (leB_add (leB_add (leB_add (leB_refl _) S6) S5) S7a) S7b) ?_
    refine leB_trans ?_ (leB_add (leB_refl _) S8)
    repeat rw [← BPair.add_assoc]
    exact leB_refl _
  -- the self-read withdraws at the factor two, the clearing then cancels
  have S10 : kappa * cc * mD * s * s
      ≤ cc * BPair.ofNat 2 * P * n * kappa * dG * W0 * mu1 * s + P * n * mu1 * kappa * cc * s := by
    have e : (BPair.ofNat 2 * kappa * cc * mD * s * s).oneValue
        (kappa * cc * mD * s * s + kappa * cc * mD * s * s) :=
      polEqB [kappa, cc, mD, s]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)))) (by decide +kernel)
    have h := leB_congr_left e S9
    refine leB_cancelL (x := kappa * cc * mD * s * s) (leB_congr_right (?_) h)
    exact polEqB [cc, P, n, kappa, dG, W0, mu1, s, mD]
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 0)) (Mon.var 8)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 6)) (Mon.var 3)) (Mon.var 0)) (Mon.var 7))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 0)) (Mon.var 8)) (Mon.var 7)) (Mon.var 7))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 6)) (Mon.var 3)) (Mon.var 0)) (Mon.var 7))))) (by decide +kernel)
  have hkcs : BPair.unit < kappa * cc * s := unitLtMul (unitLtMul hkappa0 hcc0) hs0
  refine leB_unscale_left hkcs ?_
  refine leB_congr (?_) (BPair.oneValue_symm ?_) S10
  · exact polEqB [kappa, cc, mD, s]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 3)) (Mon.mul (Mon.var 2) (Mon.var 3)))) (by decide +kernel)
  · repeat rw [BPair.right_distrib]
    rw [BPair.left_distrib]
    repeat rw [← BPair.mul_assoc]
    refine BPair.add_congr (?_) ?_
    · exact polEqB [kappa, cc, s, dG, W0, P, n, mu1]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 2)) (Mon.var 5)) (Mon.var 6)) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 7)) (Mon.var 2))) (by decide +kernel)
    · exact polEqB [kappa, cc, s, P, n, mu1]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.cst 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)


/-! The remainder cell. -/

/-- The first identity's remainder on the remainder cell,
`|r₁| ≤ [1 : 16] κ σ_W μ[1]`, cleared at the scale pair `[n : s]`, the
profile's solve `[sn : sd]` and the roots' floor `σ_- = |W|² [2 : L + 2]`:
the remainder within the derivative's remainder `a₁ μ[D]` joined to the
deviation `X`, the deviation within `2 [s : n] W₀² C_W T_R ν[|y_W| D]`
whose square the evaluation's squared Cauchy--Schwarz prices at
`ν[Q] ν[D²]`, the near scale's reads at the unit weight, `ν[D²] ≤ 2 μ[D²]`,
`μ[D²] ≤ 2 (Kη)² μ[1]` and `μ[D] ≤ 2 Kη μ[1]`, the first identity
`2 [s : n] ν[Q] ≡ κ dim G σ_W μ[1] + r₁` at the solve between its floor
and its cap `W₀ |W|²`; the deviation's square then sits at or below
`M (κ dim G σ_+ + 2 a₁ K η) μ[1] + M X` at `M := 8 W₀⁴ C_W² T_R² K² η μ[1]`,
the two-member fold of squares (`ground.leB_sq_selfcap`) and the cell's
first comparison put it at or below `[1 : 1024] κ² σ_-² μ[1]²`, the
deviation at `[1 : 32] κ σ_- μ[1]` at the trichotomy of squares, and
the cell's second comparison caps the derivative's remainder at
`[1 : 32] κ σ_- μ[1]`, the two joining at `σ_- ≤ σ_W`; the magnitude
the sorted pair's (`windowsep.mag`). -/
theorem remainder_one (r1 X Y nuQ nuD2 mD mD2 mu1 n s K W0 CW TR a1 kappa dG sn sd W2 L : BPair)
    (hr1 : windowsep.mag r1 ≤ a1 * mD + X)
    (hX : X * n ≤ BPair.ofNat 2 * s * (W0 * W0 * CW * TR) * Y)
    (hY : Y * Y ≤ nuQ * nuD2)
    (hnuD2 : nuD2 ≤ BPair.ofNat 2 * mD2)
    (hmD2 : mD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * mu1)
    (hmD : mD * s ≤ BPair.ofNat 2 * K * n * mu1)
    (hid1 : (BPair.ofNat 2 * nuQ * s * sd).oneValue (n * (kappa * dG * sn * mu1 + r1 * sd)))
    (hsigp : sn ≤ W0 * W2 * sd)
    (hsigm : BPair.ofNat 2 * W2 * sd ≤ sn * (L + BPair.ofNat 2))
    (hR1 : BPair.ofNat 1024 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2))
        * (BPair.ofNat 16 * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)) * (K * K)
            * (kappa * dG * W0 * W2 * n * s + BPair.ofNat 2 * a1 * K * (n * n))
          + BPair.ofNat 64 * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)
              * (W0 * W0 * CW * TR)) * (K * K * K * K) * (n * n))
      ≤ BPair.ofNat 4 * (kappa * kappa) * (W2 * W2) * (s * s))
    (hR2 : BPair.ofNat 32 * a1 * K * n * (L + BPair.ofNat 2) ≤ kappa * W2 * s)
    (hn0 : BPair.unit < n) (hs0 : BPair.unit < s) (hsd0 : BPair.unit < sd)
    (hX0 : BPair.unit ≤ X) (hY0 : BPair.unit ≤ Y) (hnuQ : BPair.unit ≤ nuQ)
    (hmu1 : BPair.unit ≤ mu1)
    (hK : BPair.unit ≤ K) (hW0 : BPair.unit ≤ W0) (hCW : BPair.unit ≤ CW) (hTR : BPair.unit ≤ TR)
    (ha1 : BPair.unit ≤ a1) (hkappa : BPair.unit ≤ kappa) (hdG : BPair.unit ≤ dG)
    (hW2 : BPair.unit ≤ W2) (hL : BPair.unit ≤ L) :
    BPair.ofNat 16 * sd * windowsep.mag r1 ≤ kappa * sn * mu1 := by
  have hn : BPair.unit ≤ n := leB_of_lt hn0
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hsd : BPair.unit ≤ sd := leB_of_lt hsd0
  have hG : BPair.unit ≤ W0 * W0 * CW * TR := unitLeMul (unitLeMul (unitLeMul hW0 hW0) hCW) hTR
  have hL2 : BPair.unit < L + BPair.ofNat 2 := unitLtAdd (unitLtOfNat 1) hL |> fun h =>
    BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq (BPair.add_comm _ _)) h
  generalize hGdef : W0 * W0 * CW * TR = G at hX hR1 hG
  generalize hLdef : L + BPair.ofNat 2 = L2 at hsigm hR1 hR2 hL2
  have hL2' : BPair.unit ≤ L2 := leB_of_lt hL2
  have h2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  have Ea : (BPair.ofNat 2 * s * G * Y * BPair.ofNat 2 * s * G * Y).oneValue
      (BPair.ofNat 4 * s * s * G * G * Y * Y) :=
    polEqB [s, G, Y]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Eb : (BPair.ofNat 4 * s * s * G * G * nuQ * BPair.ofNat 2 * mD2).oneValue
      (BPair.ofNat 8 * G * G * nuQ * mD2 * s * s) :=
    polEqB [s, G, nuQ, mD2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0))) (by decide +kernel)
  have Ec : (BPair.ofNat 8 * G * G * nuQ * BPair.ofNat 2 * K * K * n * n * mu1).oneValue
      (BPair.ofNat 16 * G * G * K * K * n * n * mu1 * nuQ) :=
    polEqB [G, nuQ, K, n, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 1))) (by decide +kernel)
  have Ed1 : (X * n * X * n).oneValue
      (X * X * n * n) :=
    polEqB [X, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 0)) (Mon.var 1)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1))) (by decide +kernel)
  have Ed2 : (BPair.ofNat 16 * G * G * K * K * n * n * mu1 * nuQ).oneValue
      (BPair.ofNat 16 * G * G * K * K * mu1 * nuQ * n * n) :=
    polEqB [G, K, n, mu1, nuQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Ee : (BPair.ofNat 16 * G * G * K * K * mu1 * nuQ * s * s).oneValue
      (BPair.ofNat 8 * G * G * K * K * mu1 * BPair.ofNat 2 * nuQ * s * s) :=
    polEqB [G, K, mu1, nuQ, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4))) (by decide +kernel)
  have Ef1 : (BPair.ofNat 8 * G * G * K * K * mu1 * n * kappa * dG * W0 * W2 * mu1 * s).oneValue
      (BPair.ofNat 8 * G * G * K * K * n * mu1 * kappa * dG * W0 * W2 * s * mu1) :=
    polEqB [G, K, mu1, n, kappa, dG, W0, W2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 2)) (Mon.var 8)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 2))) (by decide +kernel)
  have Ef2 : (BPair.ofNat 8 * G * G * K * K * mu1 * n * a1 * BPair.ofNat 2 * K * n * mu1).oneValue
      (BPair.ofNat 8 * G * G * K * K * n * mu1 * BPair.ofNat 2 * a1 * K * n * mu1) :=
    polEqB [G, K, mu1, n, a1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Ef3 : (BPair.ofNat 8 * G * G * K * K * mu1 * n * X * s).oneValue
      (BPair.ofNat 8 * G * G * K * K * n * mu1 * X * s) :=
    polEqB [G, K, mu1, n, X, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  -- the deviation's square at the two moments
  have d1 : X * n * (X * n) ≤ BPair.ofNat 2 * s * G * Y * (BPair.ofNat 2 * s * G * Y) :=
    leB_mul_mono (unitLeMul hX0 hn) (unitLeMul (unitLeMul (unitLeMul h2 hs) hG) hY0) hX hX
  have d2 : X * X * (n * n) ≤ BPair.ofNat 16 * G * G * K * K * mu1 * nuQ * (n * n) := by
    have a : BPair.ofNat 4 * s * s * G * G * (Y * Y)
        ≤ BPair.ofNat 4 * s * s * G * G * (nuQ * (BPair.ofNat 2 * mD2)) :=
      leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 4) hs) hs) hG) hG)
        (leB_trans hY (leB_mulR hnuQ hnuD2))
    have b : BPair.ofNat 8 * G * G * nuQ * (mD2 * (s * s))
        ≤ BPair.ofNat 8 * G * G * nuQ * (BPair.ofNat 2 * (K * K) * (n * n) * mu1) :=
      leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 8) hG) hG) hnuQ) hmD2
    repeat rw [← BPair.mul_assoc] at a
    repeat rw [← BPair.mul_assoc] at b
    repeat rw [← BPair.mul_assoc] at d1
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (Ed1) (Ed2) ?_
    have ta := leB_congr_left (BPair.oneValue_symm Ea) a
    have tb := leB_congr_left (BPair.oneValue_symm Eb) b
    have tc : BPair.ofNat 8 * G * G * nuQ * BPair.ofNat 2 * K * K * n * n * mu1
        ≤ BPair.ofNat 16 * G * G * K * K * n * n * mu1 * nuQ :=
      leB_congr_left (BPair.oneValue_symm Ec)
        (leB_refl (BPair.ofNat 16 * G * G * K * K * n * n * mu1 * nuQ))
    exact leB_trans d1 (leB_trans ta (leB_trans tb tc))
  have d3 : X * X ≤ BPair.ofNat 16 * G * G * K * K * mu1 * nuQ :=
    leB_unscale (unitLtMul hn0 hn0) d2
  -- the first identity's own read of ν[Q] at the caps
  have e3 : BPair.ofNat 2 * nuQ * s * s
      ≤ n * (kappa * dG * W0 * W2 * mu1 * s + a1 * (BPair.ofNat 2 * K * n * mu1) + X * s) := by
    have e1 : BPair.ofNat 2 * nuQ * s * sd
        ≤ n * (kappa * dG * (W0 * W2 * sd) * mu1 + (a1 * mD + X) * sd) := by
      refine leB_congr_left (BPair.oneValue_symm hid1) ?_
      refine leB_mulR hn (leB_add ?_ ?_)
      · exact leB_mulL hmu1 (leB_mulR (unitLeMul hkappa hdG) hsigp)
      · exact leB_mulL hsd (leB_trans (windowsep.le_mag r1) hr1)
    have e2 : BPair.ofNat 2 * nuQ * s ≤ n * (kappa * dG * W0 * W2 * mu1 + a1 * mD + X) := by
      refine leB_unscale hsd0 (leB_congr_right (?_) e1)
      exact polEqB [n, kappa, dG, W0, W2, sd, mu1, a1, mD, X]
          (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 5))) (Mon.var 6))) (Pol.mul (Pol.add (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 8))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 5)))))
          (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 8)))) (Pol.mon (Mon.var 9)))) (Pol.mon (Mon.var 5))) (by decide +kernel)
    have e2' := leB_mulL hs e2
    rw [BPair.mul_assoc n _ s, BPair.right_distrib, BPair.right_distrib] at e2'
    refine leB_trans e2' (leB_mulR hn (leB_add (leB_add (leB_refl _) ?_) (leB_refl _)))
    exact leB_congr_left (BPair.oneValue_of_eq (BPair.mul_assoc a1 mD s).symm) (leB_mulR ha1 hmD)
  have Exs : (X * s * X * s).oneValue
      (X * X * s * s) :=
    polEqB [X, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 0)) (Mon.var 1)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1))) (by decide +kernel)
  have Eh1 : (BPair.ofNat 1024 * L2 * L2 * X * s * X * s).oneValue
      (BPair.ofNat 4 * BPair.ofNat 16 * L2 * X * s * BPair.ofNat 16 * L2 * X * s) :=
    polEqB [L2, X, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1024) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.cst 16)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 16)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Eh2 : (BPair.ofNat 4 * kappa * kappa * W2 * W2 * s * s * mu1 * mu1).oneValue
      (BPair.ofNat 4 * kappa * W2 * s * mu1 * kappa * W2 * s * mu1) :=
    polEqB [kappa, W2, s, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3))) (by decide +kernel)
  have Ei1 : (kappa * W2 * s * mu1).oneValue
      (kappa * W2 * mu1 * s) :=
    polEqB [kappa, W2, s, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Ei2 : (BPair.ofNat 16 * L2 * a1 * BPair.ofNat 2 * K * n * mu1).oneValue
      (BPair.ofNat 32 * a1 * K * n * L2 * mu1) :=
    polEqB [L2, a1, K, n, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 4))) (by decide +kernel)
  have Ei3 : (BPair.ofNat 2 * kappa * W2 * mu1 * sd).oneValue
      (kappa * mu1 * BPair.ofNat 2 * W2 * sd) :=
    polEqB [kappa, W2, mu1, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 3))) (by decide +kernel)
  have Ei4 : (kappa * mu1 * sn * L2).oneValue
      (kappa * sn * mu1 * L2) :=
    polEqB [kappa, mu1, sn, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 1)) (Mon.var 3))) (by decide +kernel)
  have Ei5 : (BPair.ofNat 16 * L2 * windowsep.mag r1 * sd).oneValue
      (BPair.ofNat 16 * sd * windowsep.mag r1 * L2) :=
    polEqB [L2, (windowsep.mag r1), sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 2)) (Mon.var 1)) (Mon.var 0))) (by decide +kernel)
  -- the deviation's square at the identity's read: the self-capped square
  have d4 : X * s * (X * s)
      ≤ BPair.ofNat 8 * G * G * K * K * n * mu1 * (kappa * dG * W0 * W2 * s + BPair.ofNat 2 * a1 * K * n)
          * mu1
        + BPair.ofNat 8 * G * G * K * K * n * mu1 * (X * s) := by
    have h := leB_mulL (unitLeMul hs hs) d3
    have h' := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 8) hG)
      hG) hK) hK) hmu1) e3
    repeat rw [BPair.left_distrib] at h'
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.mul_assoc] at h'
    repeat first | rw [BPair.left_distrib] | rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left ((BPair.oneValue_symm Exs)) h) ?_
    refine leB_trans (leB_congr_left (BPair.oneValue_symm Ee) h') ?_
    refine leB_add (leB_add ?_ ?_) ?_
    · exact leB_congr_left ((BPair.oneValue_symm Ef1)) (leB_refl _)
    · exact leB_congr_left (BPair.oneValue_symm Ef2) (leB_refl _)
    · exact leB_congr_left ((BPair.oneValue_symm Ef3)) (leB_refl _)
  have d5 := leB_sq_selfcap d4
  -- the cell's first comparison at the unit's moment squared
  have d6 : BPair.ofNat 1024 * L2 * L2 * X * s * X * s
      ≤ BPair.ofNat 4 * kappa * kappa * W2 * W2 * s * s * mu1 * mu1 := by
    have hR := leB_mulL (unitLeMul hmu1 hmu1) hR1
    have hL2L2 : BPair.unit ≤ BPair.ofNat 1024 * (L2 * L2) :=
      unitLeMul (unitLeOfNat 1024) (unitLeMul hL2' hL2')
    have e5 : (BPair.ofNat 2 * (BPair.ofNat 8 * G * G * K * K * n * mu1 * (kappa * dG * W0 * W2 * s + BPair.ofNat 2 * a1 * K * n) * mu1) + BPair.ofNat 8 * G * G * K * K * n * mu1 * (BPair.ofNat 8 * G * G * K * K * n * mu1)).oneValue
        ((BPair.ofNat 16 * (G * G) * (K * K) * (kappa * dG * W0 * W2 * n * s + BPair.ofNat 2 * a1 * K * (n * n)) + BPair.ofNat 64 * (G * G * G * G) * (K * K * K * K) * (n * n)) * (mu1 * mu1)) :=
      polEqB [G, K, n, mu1, kappa, dG, W0, W2, s, a1]
        (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 9)) (Mon.var 1)) (Mon.var 2))))) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))))
        (Pol.mul (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.var 1) (Mon.var 1)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 2)) (Mon.var 8))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 9)) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 2)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 0))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 1)) (Mon.var 1))) (Mon.mul (Mon.var 2) (Mon.var 2))))) (Pol.mon (Mon.mul (Mon.var 3) (Mon.var 3)))) (by decide +kernel)
    have h := leB_mulR hL2L2 (leB_trans d5 (leB_congr_left (BPair.oneValue_symm e5) (leB_refl _)))
    repeat first | rw [BPair.left_distrib] at h | rw [BPair.right_distrib] at h
    repeat first | rw [BPair.left_distrib] at hR | rw [BPair.right_distrib] at hR
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.mul_assoc] at hR
    repeat rw [← BPair.add_assoc] at h
    repeat rw [← BPair.add_assoc] at hR
    repeat rw [← BPair.mul_assoc]
    exact leB_trans h hR
  -- the deviation at the trichotomy of squares
  have d7 : BPair.ofNat 16 * L2 * X * s ≤ kappa * W2 * s * mu1 := by
    have hb : BPair.unit ≤ kappa * W2 * s * mu1 := unitLeMul (unitLeMul (unitLeMul hkappa hW2) hs) hmu1
    refine leB_of_sq_le hb (leB_not_lt ?_)
    refine leB_unscale_left (unitLtNat (by decide : 0 < 4)) ?_
    refine leB_congr (BPair.oneValue_trans Eh1 (?_))
      (BPair.oneValue_trans (Eh2) (?_)) d6
    · exact BPair.oneValue_of_eq (show BPair.ofNat 4 * BPair.ofNat 16 * L2 * X * s * BPair.ofNat 16 * L2 * X * s = BPair.ofNat 4 * (BPair.ofNat 16 * L2 * X * s * (BPair.ofNat 16 * L2 * X * s)) by repeat rw [← BPair.mul_assoc])
    · exact BPair.oneValue_of_eq (show BPair.ofNat 4 * kappa * W2 * s * mu1 * kappa * W2 * s * mu1 = BPair.ofNat 4 * (kappa * W2 * s * mu1 * (kappa * W2 * s * mu1)) by repeat rw [← BPair.mul_assoc])
  have d8 : BPair.ofNat 16 * L2 * X ≤ kappa * W2 * mu1 :=
    leB_unscale hs0 (leB_congr_right (Ei1) d7)
  -- the derivative's remainder at the cell's second comparison
  have d9 : BPair.ofNat 16 * L2 * a1 * mD ≤ kappa * W2 * mu1 := by
    refine leB_unscale hs0 ?_
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeOfNat 16) hL2') ha1) hmD
    have h' := leB_mulL hmu1 hR2
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.mul_assoc] at h'
    refine leB_trans h ?_
    refine leB_trans (leB_congr_left (BPair.oneValue_symm Ei2) h') ?_
    exact leB_congr_left ((BPair.oneValue_symm Ei1)) (leB_refl _)
  -- the two members joined, the floor's solve at the profile's own
  have d10 : BPair.ofNat 16 * L2 * windowsep.mag r1 ≤ BPair.ofNat 2 * kappa * W2 * mu1 := by
    refine leB_trans (leB_mulR (unitLeMul (unitLeOfNat 16) hL2') hr1) ?_
    rw [BPair.left_distrib, ← BPair.mul_assoc]
    refine leB_trans (leB_add d9 d8) ?_
    refine leB_congr_right (BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofNat_two_mul _))
      (?_)) (leB_refl _)
    exact BPair.oneValue_of_eq (show BPair.ofNat 2 * (kappa * W2 * mu1) = BPair.ofNat 2 * kappa * W2 * mu1 by repeat rw [← BPair.mul_assoc])
  refine leB_unscale hL2 ?_
  have h := leB_mulL hsd d10
  repeat rw [← BPair.mul_assoc] at h
  refine leB_trans (leB_congr_left (Ei5) h) ?_
  have h' := leB_mulR (unitLeMul hkappa hmu1) hsigm
  repeat rw [← BPair.mul_assoc] at h'
  refine leB_trans (leB_congr_left ((BPair.oneValue_symm Ei3)) h') ?_
  exact leB_congr_left ((BPair.oneValue_symm Ei4)) (leB_refl _)


/-- The second identity's remainder on the remainder cell,
`|r₂| ≤ [3 : 16] κ σ_W μ[Q]`, cleared at the scale pair `[n : s]`, the
profile's solve `[sn : sd]` and the roots' floor `σ_- = |W|² [2 : L + 2]`:
the remainder within the derivative's remainder `a₁ μ[QD]` joined to
the generator's gap `g₂` and the deviation `X₂`; the gap split at the
two-member square at `t := κ σ_- [1 : 16 W₀² C_W]`, its first member
within `[1 : 16] κ σ_- μ[Q]` and its second within
`64 W₀⁴ C_W² ϱ₂ (L + 2)² μ[QD]` at the clearing `8 (L + 2) κ |W|²`; the
deviation within `2 [s : n] W₀² C_W T_R ν[|y_W| D]` whose square the
evaluation's squared Cauchy--Schwarz prices at `ν[Q²] ν[QD²]`, the near
scale's reads at the weight `Q`, the second identity
`2 [s : n] ν[Q²] ≡ κ (dim G + 2) σ_W μ[Q] + r₂` at the solve between its
floor and its cap `W₀ |W|²`, the two-member fold of squares
(`ground.leB_sq_selfcap`) and the cell's fourth comparison put the
deviation's square at or below `[1 : 256] κ² σ_-² μ[Q]²`, the deviation
at `[1 : 16] κ σ_- μ[Q]` at the trichotomy of squares; the cell's third
comparison caps the derivative's remainder with the gap's second
member at `[1 : 16] κ σ_- μ[Q]`; and the three members join at
`σ_- ≤ σ_W`, the magnitude the sorted pair's (`windowsep.mag`). -/
theorem remainder_two (r2 g2 X2 Y2 nuQ2 nuQD2 mQ mQD mQD2 n s K W0 CW TR a1 kappa dG sn sd W2 L
      rho2 Winf2 : BPair)
    (hr2 : windowsep.mag r2 ≤ a1 * mQD + windowsep.mag g2 + X2)
    (hg2 : windowsep.mag g2 * (BPair.ofNat 8 * (L + BPair.ofNat 2) * kappa * W2)
      ≤ kappa * kappa * (W2 * W2) * mQ
        + BPair.ofNat 64 * (W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2)
          * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2)) * mQD)
    (hX : X2 * n ≤ BPair.ofNat 2 * s * (W0 * W0 * CW * TR) * Y2)
    (hY : Y2 * Y2 ≤ nuQ2 * nuQD2)
    (hnuQD2 : nuQD2 ≤ BPair.ofNat 2 * mQD2)
    (hmQD2 : mQD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * mQ)
    (hmQD : mQD * s ≤ BPair.ofNat 2 * K * n * mQ)
    (hid2 : (BPair.ofNat 2 * nuQ2 * s * sd).oneValue
      (n * (kappa * (dG + BPair.ofNat 2) * sn * mQ + r2 * sd)))
    (hsigp : sn ≤ W0 * W2 * sd)
    (hsigm : BPair.ofNat 2 * W2 * sd ≤ sn * (L + BPair.ofNat 2))
    (hR3 : BPair.ofNat 8 * (L + BPair.ofNat 2)
        * (BPair.ofNat 2 * a1 * kappa * W2
          + BPair.ofNat 16 * (W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2) * (L + BPair.ofNat 2))
        * K * n
      ≤ kappa * kappa * (W2 * W2) * s)
    (hR4 : BPair.ofNat 1088 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2))
          * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)) * W0 * (kappa * kappa)
          * (dG + BPair.ofNat 2) * (W2 * W2) * (K * K) * n * s
        + BPair.ofNat 1024 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2))
          * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR))
          * (BPair.ofNat 2 * a1 * kappa * W2
            + BPair.ofNat 16 * (W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2) * (L + BPair.ofNat 2))
          * (K * K * K) * (n * n)
        + BPair.ofNat 4096 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2))
          * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)
            * (W0 * W0 * CW * TR))
          * kappa * W2 * (K * K * K * K) * (n * n)
      ≤ kappa * kappa * kappa * (W2 * W2 * W2) * (s * s))
    (hn0 : BPair.unit < n) (hs0 : BPair.unit < s) (hsd0 : BPair.unit < sd)
    (hkappa0 : BPair.unit < kappa) (hW20 : BPair.unit < W2) (hW0 : BPair.ofPos .one ≤ W0)
    (hX0 : BPair.unit ≤ X2) (hY0 : BPair.unit ≤ Y2) (hnuQ : BPair.unit ≤ nuQ2)
    (hmQ : BPair.unit ≤ mQ) (hK : BPair.unit ≤ K)
    (hCW : BPair.unit ≤ CW) (hTR : BPair.unit ≤ TR) (ha1 : BPair.unit ≤ a1)
    (hdG : BPair.unit ≤ dG) (hrho2 : BPair.unit ≤ rho2) (hWinf2 : BPair.unit ≤ Winf2)
    (hL : BPair.unit ≤ L) :
    BPair.ofNat 16 * sd * windowsep.mag r2 ≤ BPair.ofNat 3 * kappa * sn * mQ := by
  have hn : BPair.unit ≤ n := leB_of_lt hn0
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hsd : BPair.unit ≤ sd := leB_of_lt hsd0
  have hkappa : BPair.unit ≤ kappa := leB_of_lt hkappa0
  have hW2 : BPair.unit ≤ W2 := leB_of_lt hW20
  have hW0u : BPair.unit ≤ W0 := leB_trans (leB_of_lt (unitLtOfPos .one)) hW0
  have hG : BPair.unit ≤ W0 * W0 * CW * TR := unitLeMul (unitLeMul (unitLeMul hW0u hW0u) hCW) hTR
  have hV : BPair.unit ≤ W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2 :=
    unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul hW0u hW0u) hW0u)
      hW0u) hCW) hCW) hrho2) hWinf2
  have hL2 : BPair.unit < L + BPair.ofNat 2 := unitLtAdd (unitLtOfNat 1) hL |> fun h =>
    BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq (BPair.add_comm _ _)) h
  have h2L2 : BPair.ofNat 2 ≤ L + BPair.ofNat 2 :=
    leB_congr_left (BPair.unit_add _) (leB_add hL (leB_refl (BPair.ofNat 2)))
  have h2D2 : BPair.ofNat 2 ≤ dG + BPair.ofNat 2 :=
    leB_congr_left (BPair.unit_add _) (leB_add hdG (leB_refl (BPair.ofNat 2)))
  generalize hGdef : W0 * W0 * CW * TR = G at hX hR4 hG
  generalize hVdef : W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2 = V at hg2 hR3 hR4 hV
  generalize hLdef : L + BPair.ofNat 2 = L2 at hg2 hsigm hR3 hR4 hL2 h2L2
  generalize hDdef : dG + BPair.ofNat 2 = D2 at hid2 hR4 h2D2
  have hL2' : BPair.unit ≤ L2 := leB_of_lt hL2
  have hD2 : BPair.unit ≤ D2 := leB_trans (unitLeOfNat 2) h2D2
  have h2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  have hc : BPair.unit ≤ BPair.ofNat 8 * L2 * kappa * W2 :=
    unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 8) hL2') hkappa) hW2
  have Ea : (BPair.ofNat 2 * s * G * Y2 * BPair.ofNat 2 * s * G * Y2).oneValue
      (BPair.ofNat 4 * s * s * G * G * Y2 * Y2) :=
    polEqB [s, G, Y2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Eb : (BPair.ofNat 4 * s * s * G * G * nuQ2 * BPair.ofNat 2 * mQD2).oneValue
      (BPair.ofNat 8 * G * G * nuQ2 * mQD2 * s * s) :=
    polEqB [s, G, nuQ2, mQD2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0))) (by decide +kernel)
  have Ec : (BPair.ofNat 8 * G * G * nuQ2 * BPair.ofNat 2 * K * K * n * n * mQ).oneValue
      (BPair.ofNat 16 * G * G * K * K * n * n * mQ * nuQ2) :=
    polEqB [G, nuQ2, K, n, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 1))) (by decide +kernel)
  have Ed1 : (X2 * n * X2 * n).oneValue
      (X2 * X2 * n * n) :=
    polEqB [X2, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 0)) (Mon.var 1)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1))) (by decide +kernel)
  have Ed2 : (BPair.ofNat 16 * G * G * K * K * n * n * mQ * nuQ2).oneValue
      (BPair.ofNat 16 * G * G * K * K * mQ * nuQ2 * n * n) :=
    polEqB [G, K, n, mQ, nuQ2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Ee1 : (BPair.ofNat 8 * L2 * kappa * W2 * BPair.ofNat 2 * nuQ2 * s * s).oneValue
      (BPair.ofNat 16 * L2 * kappa * W2 * nuQ2 * s * s) :=
    polEqB [L2, kappa, W2, nuQ2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4))) (by decide +kernel)
  have Ef1 : (BPair.ofNat 8 * L2 * kappa * W2 * n * kappa * D2 * W0 * W2 * mQ * s).oneValue
      (BPair.ofNat 8 * L2 * kappa * kappa * D2 * W0 * W2 * W2 * mQ * s * n) :=
    polEqB [L2, kappa, W2, n, D2, W0, mQ, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 2)) (Mon.var 6)) (Mon.var 7)) (Mon.var 3))) (by decide +kernel)
  have Ef2 : (BPair.ofNat 8 * L2 * kappa * W2 * n * a1 * BPair.ofNat 2 * K * n * mQ).oneValue
      (BPair.ofNat 16 * L2 * kappa * W2 * a1 * K * mQ * n * n) :=
    polEqB [L2, kappa, W2, n, a1, K, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 2)) (Mon.var 5)) (Mon.var 3)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have Ef3 : (windowsep.mag g2 * BPair.ofNat 8 * L2 * kappa * W2 * n * s).oneValue
      (BPair.ofNat 8 * L2 * kappa * W2 * n * windowsep.mag g2 * s) :=
    polEqB [(windowsep.mag g2), L2, kappa, W2, n, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 0)) (Mon.var 5))) (by decide +kernel)
  have Ef4 : (BPair.ofNat 64 * V * L2 * L2 * n * BPair.ofNat 2 * K * n * mQ).oneValue
      (BPair.ofNat 128 * V * L2 * L2 * K * mQ * n * n) :=
    polEqB [V, L2, n, K, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Ef5 : (BPair.ofNat 64 * V * L2 * L2 * mQD * n * s).oneValue
      (BPair.ofNat 64 * V * L2 * L2 * n * mQD * s) :=
    polEqB [V, L2, mQD, n, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel)
  have Ef6 : (kappa * kappa * W2 * W2 * mQ * n * s).oneValue
      (kappa * kappa * W2 * W2 * mQ * s * n) :=
    polEqB [kappa, W2, mQ, n, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 4)) (Mon.var 3))) (by decide +kernel)
  have Ef7 : (BPair.ofNat 8 * L2 * kappa * W2 * n * X2 * s).oneValue
      (BPair.ofNat 8 * L2 * kappa * W2 * X2 * s * n) :=
    polEqB [L2, kappa, W2, n, X2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5)) (Mon.var 3))) (by decide +kernel)
  have Eg0 : (BPair.ofNat 16 * L2 * kappa * W2 * X2 * s * BPair.ofNat 16 * L2 * kappa * W2 * X2 * s).oneValue
      (BPair.ofNat 256 * L2 * L2 * kappa * kappa * W2 * W2 * s * s * X2 * X2) :=
    polEqB [L2, kappa, W2, X2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 16)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4)) (Mon.var 4)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have Eg1 : (BPair.ofNat 256 * L2 * L2 * kappa * kappa * W2 * W2 * s * s * BPair.ofNat 16 * G * G * K * K * mQ * nuQ2).oneValue
      (BPair.ofNat 256 * G * G * K * K * mQ * L2 * kappa * W2 * BPair.ofNat 16 * L2 * kappa * W2 * nuQ2 * s * s) :=
    polEqB [L2, kappa, W2, s, G, K, mQ, nuQ2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.cst 16)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 16)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 7)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have Eh1 : (BPair.ofNat 256 * G * G * K * K * mQ * L2 * kappa * W2 * BPair.ofNat 8 * L2 * kappa * kappa * D2 * W0 * W2 * W2 * mQ * s * n).oneValue
      (BPair.ofNat 2048 * G * G * K * K * mQ * mQ * L2 * L2 * kappa * kappa * kappa * D2 * W0 * W2 * W2 * W2 * s * n) :=
    polEqB [G, K, mQ, L2, kappa, W2, D2, W0, s, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 8)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)) (Mon.var 7)) (Mon.var 5)) (Mon.var 5)) (Mon.var 2)) (Mon.var 8)) (Mon.var 9)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2048) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)) (Mon.var 7)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 8)) (Mon.var 9))) (by decide +kernel)
  have Eh2 : (BPair.ofNat 256 * G * G * K * K * mQ * L2 * kappa * W2 * BPair.ofNat 16 * L2 * kappa * W2 * a1 * K * mQ * n * n).oneValue
      (BPair.ofNat 4096 * G * G * K * K * K * mQ * mQ * L2 * L2 * kappa * kappa * W2 * W2 * a1 * n * n) :=
    polEqB [G, K, mQ, L2, kappa, W2, a1, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 16)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 1)) (Mon.var 2)) (Mon.var 7)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4096) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7))) (by decide +kernel)
  have Eh3 : (BPair.ofNat 256 * G * G * K * K * mQ * L2 * kappa * W2 * kappa * kappa * W2 * W2 * mQ * s * n).oneValue
      (BPair.ofNat 256 * G * G * K * K * mQ * mQ * L2 * kappa * kappa * kappa * W2 * W2 * W2 * s * n) :=
    polEqB [G, K, mQ, L2, kappa, W2, s, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 2)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (by decide +kernel)
  have Eh4 : (BPair.ofNat 256 * G * G * K * K * mQ * L2 * kappa * W2 * BPair.ofNat 128 * V * L2 * L2 * K * mQ * n * n).oneValue
      (BPair.ofNat 32768 * G * G * K * K * K * mQ * mQ * L2 * L2 * L2 * kappa * W2 * V * n * n) :=
    polEqB [G, K, mQ, L2, kappa, W2, V, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 128)) (Mon.var 6)) (Mon.var 3)) (Mon.var 3)) (Mon.var 1)) (Mon.var 2)) (Mon.var 7)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32768) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7))) (by decide +kernel)
  have Eh5 : (BPair.ofNat 256 * G * G * K * K * mQ * L2 * kappa * W2 * BPair.ofNat 8 * L2 * kappa * W2 * X2 * s * n).oneValue
      (BPair.ofNat 128 * L2 * kappa * W2 * G * G * K * K * mQ * n * BPair.ofNat 16 * L2 * kappa * W2 * X2 * s) :=
    polEqB [G, K, mQ, L2, kappa, W2, X2, s, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 8)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 8)) (Mon.cst 16)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (by decide +kernel)
  have Ei1 : (BPair.ofNat 2 * BPair.ofNat 2048 * G * G * K * K * mQ * mQ * L2 * L2 * kappa * kappa * kappa * D2 * W0 * W2 * W2 * W2 * s * n).oneValue
      (BPair.ofNat 4096 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K * n * s * mQ * mQ) :=
    polEqB [G, K, mQ, L2, kappa, D2, W0, W2, s, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.cst 2048)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4096) (Mon.var 3)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 7)) (Mon.var 7)) (Mon.var 7)) (Mon.var 1)) (Mon.var 1)) (Mon.var 9)) (Mon.var 8)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Ei2 : (BPair.ofNat 2 * BPair.ofNat 4096 * G * G * K * K * K * mQ * mQ * L2 * L2 * kappa * kappa * W2 * W2 * a1 * n * n).oneValue
      (BPair.ofNat 8192 * L2 * L2 * G * G * a1 * kappa * kappa * W2 * W2 * K * K * K * n * n * mQ * mQ) :=
    polEqB [G, K, mQ, L2, kappa, W2, a1, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.cst 4096)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8192) (Mon.var 3)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 7)) (Mon.var 7)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Ei3 : (BPair.ofNat 2 * BPair.ofNat 256 * G * G * K * K * mQ * mQ * L2 * kappa * kappa * kappa * W2 * W2 * W2 * s * n).oneValue
      (BPair.ofNat 512 * L2 * G * G * kappa * kappa * kappa * W2 * W2 * W2 * K * K * n * s * mQ * mQ) :=
    polEqB [G, K, mQ, L2, kappa, W2, s, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.cst 256)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 512) (Mon.var 3)) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 1)) (Mon.var 1)) (Mon.var 7)) (Mon.var 6)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Ei4 : (BPair.ofNat 2 * BPair.ofNat 32768 * G * G * K * K * K * mQ * mQ * L2 * L2 * L2 * kappa * W2 * V * n * n).oneValue
      (BPair.ofNat 65536 * L2 * L2 * L2 * G * G * V * kappa * W2 * K * K * K * n * n * mQ * mQ) :=
    polEqB [G, K, mQ, L2, kappa, W2, V, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.cst 32768)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 65536) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 4)) (Mon.var 5)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 7)) (Mon.var 7)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Ei5 : (BPair.ofNat 128 * L2 * kappa * W2 * G * G * K * K * mQ * n * BPair.ofNat 128 * L2 * kappa * W2 * G * G * K * K * mQ * n).oneValue
      (BPair.ofNat 16384 * L2 * L2 * G * G * G * G * kappa * kappa * W2 * W2 * K * K * K * K * n * n * mQ * mQ) :=
    polEqB [L2, kappa, W2, G, K, mQ, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.cst 128)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16384) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)) (Mon.var 6)) (Mon.var 5)) (Mon.var 5))) (by decide +kernel)
  have Ei6 : (BPair.ofNat 256 * L2 * W0 * D2 * L2 * G * G * kappa * kappa * kappa * W2 * W2 * W2 * K * K * n * s * mQ * mQ).oneValue
      (BPair.ofNat 256 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K * n * s * mQ * mQ) :=
    polEqB [L2, W0, D2, G, kappa, W2, K, n, s, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 9)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 1)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 2)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 9))) (by decide +kernel)
  have Ej1 : (BPair.ofNat 1088 * L2 * L2 * G * G * W0 * kappa * kappa * D2 * W2 * W2 * K * K * n * s * BPair.ofNat 4 * kappa * W2 * mQ * mQ).oneValue
      (BPair.ofNat 4352 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K * n * s * mQ * mQ) :=
    polEqB [L2, G, W0, kappa, D2, W2, K, n, s, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1088) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.cst 4)) (Mon.var 3)) (Mon.var 5)) (Mon.var 9)) (Mon.var 9)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4352) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 9))) (by decide +kernel)
  have Ej2 : (BPair.ofNat 1024 * L2 * L2 * G * G * BPair.ofNat 2 * a1 * kappa * W2 * K * K * K * n * n * BPair.ofNat 4 * kappa * W2 * mQ * mQ).oneValue
      (BPair.ofNat 8192 * L2 * L2 * G * G * a1 * kappa * kappa * W2 * W2 * K * K * K * n * n * mQ * mQ) :=
    polEqB [L2, G, a1, kappa, W2, K, n, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1024) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.cst 4)) (Mon.var 3)) (Mon.var 4)) (Mon.var 7)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8192) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7))) (by decide +kernel)
  have Ej3 : (BPair.ofNat 1024 * L2 * L2 * G * G * BPair.ofNat 16 * V * L2 * K * K * K * n * n * BPair.ofNat 4 * kappa * W2 * mQ * mQ).oneValue
      (BPair.ofNat 65536 * L2 * L2 * L2 * G * G * V * kappa * W2 * K * K * K * n * n * mQ * mQ) :=
    polEqB [L2, G, V, K, n, kappa, W2, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1024) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.cst 16)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.cst 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 65536) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 5)) (Mon.var 6)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)) (Mon.var 7))) (by decide +kernel)
  have Ej4 : (BPair.ofNat 4096 * L2 * L2 * G * G * G * G * kappa * W2 * K * K * K * K * n * n * BPair.ofNat 4 * kappa * W2 * mQ * mQ).oneValue
      (BPair.ofNat 16384 * L2 * L2 * G * G * G * G * kappa * kappa * W2 * W2 * K * K * K * K * n * n * mQ * mQ) :=
    polEqB [L2, G, kappa, W2, K, n, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4096) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.cst 4)) (Mon.var 2)) (Mon.var 3)) (Mon.var 6)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16384) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6))) (by decide +kernel)
  have Ej5 : (kappa * kappa * kappa * W2 * W2 * W2 * s * s * BPair.ofNat 4 * kappa * W2 * mQ * mQ).oneValue
      (BPair.ofNat 4 * kappa * kappa * kappa * kappa * W2 * W2 * W2 * W2 * s * s * mQ * mQ) :=
    polEqB [kappa, W2, s, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.cst 4)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have Ek1 : (BPair.ofNat 2 * kappa * kappa * W2 * W2 * s * mQ * BPair.ofNat 2 * kappa * kappa * W2 * W2 * s * mQ).oneValue
      (BPair.ofNat 4 * kappa * kappa * kappa * kappa * W2 * W2 * W2 * W2 * s * s * mQ * mQ) :=
    polEqB [kappa, W2, s, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have Ek2 : (BPair.ofNat 16 * L2 * kappa * W2 * X2 * s).oneValue
      (BPair.ofNat 8 * L2 * X2 * BPair.ofNat 2 * kappa * W2 * s) :=
    polEqB [L2, kappa, W2, X2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel)
  have Ek3 : (BPair.ofNat 2 * kappa * kappa * W2 * W2 * s * mQ).oneValue
      (kappa * W2 * mQ * BPair.ofNat 2 * kappa * W2 * s) :=
    polEqB [kappa, W2, s, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have El1 : (BPair.ofNat 8 * L2 * BPair.ofNat 2 * a1 * kappa * W2 * K * n * mQ).oneValue
      (BPair.ofNat 16 * L2 * kappa * W2 * a1 * K * n * mQ) :=
    polEqB [L2, a1, kappa, W2, K, n, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have El2 : (BPair.ofNat 8 * L2 * BPair.ofNat 16 * V * L2 * K * n * mQ).oneValue
      (BPair.ofNat 128 * V * L2 * L2 * K * n * mQ) :=
    polEqB [L2, V, K, n, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.cst 16)) (Mon.var 1)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 1)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Em1 : (BPair.ofNat 8 * L2 * kappa * W2 * X2).oneValue
      (kappa * W2 * BPair.ofNat 8 * L2 * X2) :=
    polEqB [L2, kappa, W2, X2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.cst 8)) (Mon.var 0)) (Mon.var 3))) (by decide +kernel)
  have Em2 : (kappa * W2 * kappa * W2 * mQ).oneValue
      (kappa * kappa * W2 * W2 * mQ) :=
    polEqB [kappa, W2, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Em4 : (BPair.ofNat 8 * L2 * kappa * W2 * windowsep.mag r2).oneValue
      (BPair.ofNat 8 * L2 * windowsep.mag r2 * kappa * W2) :=
    polEqB [L2, kappa, W2, (windowsep.mag r2)]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 3)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Em5 : (BPair.ofNat 3 * kappa * kappa * W2 * W2 * mQ).oneValue
      (BPair.ofNat 3 * kappa * W2 * mQ * kappa * W2) :=
    polEqB [kappa, W2, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 1))) (by decide +kernel)
  have En1 : (BPair.ofNat 16 * sd * windowsep.mag r2 * L2).oneValue
      (BPair.ofNat 2 * sd * BPair.ofNat 8 * L2 * windowsep.mag r2) :=
    polEqB [sd, (windowsep.mag r2), L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.cst 8)) (Mon.var 2)) (Mon.var 1))) (by decide +kernel)
  have En2 : (BPair.ofNat 2 * sd * BPair.ofNat 3 * kappa * W2 * mQ).oneValue
      (BPair.ofNat 3 * kappa * mQ * BPair.ofNat 2 * W2 * sd) :=
    polEqB [sd, kappa, W2, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.cst 3)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 1)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 0))) (by decide +kernel)
  have En3 : (BPair.ofNat 3 * kappa * mQ * sn * L2).oneValue
      (BPair.ofNat 3 * kappa * sn * mQ * L2) :=
    polEqB [kappa, mQ, sn, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 0)) (Mon.var 2)) (Mon.var 1)) (Mon.var 3))) (by decide +kernel)
  have El3 : (BPair.ofNat 8 * L2 * kappa * W2 * a1 * BPair.ofNat 2 * K * n * mQ).oneValue
      (BPair.ofNat 16 * L2 * kappa * W2 * a1 * K * n * mQ) :=
    polEqB [L2, kappa, W2, a1, K, n, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have El4 : (BPair.ofNat 64 * V * L2 * L2 * BPair.ofNat 2 * K * n * mQ).oneValue
      (BPair.ofNat 128 * V * L2 * L2 * K * n * mQ) :=
    polEqB [V, L2, K, n, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have El5 : (kappa * kappa * W2 * W2 * s * mQ).oneValue
      (kappa * kappa * W2 * W2 * mQ * s) :=
    polEqB [kappa, W2, s, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Em0 : (windowsep.mag g2 * BPair.ofNat 8 * L2 * kappa * W2).oneValue
      (BPair.ofNat 8 * L2 * kappa * W2 * windowsep.mag g2) :=
    polEqB [(windowsep.mag g2), L2, kappa, W2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0))) (by decide +kernel)
  have Eadd : (BPair.ofNat 4352 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K * n * s * mQ * mQ).oneValue
      (BPair.ofNat 4096 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K * n * s * mQ * mQ + BPair.ofNat 256 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K * n * s * mQ * mQ) :=
    polEqB [L2, G, W0, kappa, D2, W2, K, n, s, mQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4352) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 9)))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4096) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 9))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 256) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 9)))) (by decide +kernel)
  -- the deviation's square at the two moments
  have d1 : X2 * n * (X2 * n) ≤ BPair.ofNat 2 * s * G * Y2 * (BPair.ofNat 2 * s * G * Y2) :=
    leB_mul_mono (unitLeMul hX0 hn) (unitLeMul (unitLeMul (unitLeMul h2 hs) hG) hY0) hX hX
  have d2 : X2 * X2 * (n * n) ≤ BPair.ofNat 16 * G * G * K * K * mQ * nuQ2 * (n * n) := by
    have a : BPair.ofNat 4 * s * s * G * G * (Y2 * Y2)
        ≤ BPair.ofNat 4 * s * s * G * G * (nuQ2 * (BPair.ofNat 2 * mQD2)) :=
      leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 4) hs) hs) hG) hG)
        (leB_trans hY (leB_mulR hnuQ hnuQD2))
    have b : BPair.ofNat 8 * G * G * nuQ2 * (mQD2 * (s * s))
        ≤ BPair.ofNat 8 * G * G * nuQ2 * (BPair.ofNat 2 * (K * K) * (n * n) * mQ) :=
      leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 8) hG) hG) hnuQ) hmQD2
    repeat rw [← BPair.mul_assoc] at a
    repeat rw [← BPair.mul_assoc] at b
    repeat rw [← BPair.mul_assoc] at d1
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (Ed1) (Ed2) ?_
    have ta := leB_congr_left (BPair.oneValue_symm Ea) a
    have tb := leB_congr_left (BPair.oneValue_symm Eb) b
    have tc : BPair.ofNat 8 * G * G * nuQ2 * BPair.ofNat 2 * K * K * n * n * mQ
        ≤ BPair.ofNat 16 * G * G * K * K * n * n * mQ * nuQ2 :=
      leB_congr_left (BPair.oneValue_symm Ec)
        (leB_refl (BPair.ofNat 16 * G * G * K * K * n * n * mQ * nuQ2))
    exact leB_trans d1 (leB_trans ta (leB_trans tb tc))
  have d3 : X2 * X2 ≤ BPair.ofNat 16 * G * G * K * K * mQ * nuQ2 :=
    leB_unscale (unitLtMul hn0 hn0) d2
  -- the second identity's own read of ν[Q²] at the caps
  have e3 : BPair.ofNat 2 * nuQ2 * s * s
      ≤ n * (kappa * D2 * W0 * W2 * mQ * s + a1 * (BPair.ofNat 2 * K * n * mQ)
        + windowsep.mag g2 * s + X2 * s) := by
    have e1 : BPair.ofNat 2 * nuQ2 * s * sd
        ≤ n * (kappa * D2 * (W0 * W2 * sd) * mQ
          + (a1 * mQD + windowsep.mag g2 + X2) * sd) := by
      refine leB_congr_left (BPair.oneValue_symm hid2) ?_
      refine leB_mulR hn (leB_add ?_ ?_)
      · exact leB_mulL hmQ (leB_mulR (unitLeMul hkappa hD2) hsigp)
      · exact leB_mulL hsd (leB_trans (windowsep.le_mag r2) hr2)
    have e2 : BPair.ofNat 2 * nuQ2 * s
        ≤ n * (kappa * D2 * W0 * W2 * mQ + a1 * mQD + windowsep.mag g2 + X2) := by
      refine leB_unscale hsd0 (leB_congr_right (?_) e1)
      exact polEqB [n, kappa, D2, W0, W2, sd, mQ, a1, mQD, (windowsep.mag g2), X2]
          (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 5))) (Mon.var 6))) (Pol.mul (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 8))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 10))) (Pol.mon (Mon.var 5)))))
          (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 8)))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 10)))) (Pol.mon (Mon.var 5))) (by decide +kernel)
    have e2' := leB_mulL hs e2
    rw [BPair.mul_assoc n _ s, BPair.right_distrib, BPair.right_distrib, BPair.right_distrib] at e2'
    refine leB_trans e2' (leB_mulR hn (leB_add (leB_add (leB_add (leB_refl _) ?_) (leB_refl _))
      (leB_refl _)))
    exact leB_congr_left (BPair.oneValue_of_eq (BPair.mul_assoc a1 mQD s).symm) (leB_mulR ha1 hmQD)
  -- the identity's read at the gap term's clearing, the gap term at its two members
  have e5 : BPair.ofNat 16 * L2 * kappa * W2 * nuQ2 * s * s
      ≤ BPair.ofNat 8 * L2 * kappa * kappa * D2 * W0 * W2 * W2 * mQ * s * n
        + BPair.ofNat 16 * L2 * kappa * W2 * a1 * K * mQ * n * n
        + kappa * kappa * W2 * W2 * mQ * s * n
        + BPair.ofNat 128 * V * L2 * L2 * K * mQ * n * n
        + BPair.ofNat 8 * L2 * kappa * W2 * X2 * s * n := by
    have h := leB_mulR hc e3
    repeat first | rw [BPair.left_distrib] at h | rw [BPair.right_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.add_assoc] at h
    have g1 : BPair.ofNat 8 * L2 * kappa * W2 * n * windowsep.mag g2 * s
        ≤ kappa * kappa * W2 * W2 * mQ * s * n + BPair.ofNat 128 * V * L2 * L2 * K * mQ * n * n := by
      have h1 := leB_mulL (unitLeMul hn hs) hg2
      repeat first | rw [BPair.left_distrib] at h1 | rw [BPair.right_distrib] at h1
      repeat rw [← BPair.mul_assoc] at h1
      refine leB_congr_left (Ef3) (leB_trans h1 (leB_add
        (leB_congr_left ((BPair.oneValue_symm Ef6)) (leB_refl _)) ?_))
      have h2' := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 64) hV) hL2')
        hL2') hn) hmQD
      repeat rw [← BPair.mul_assoc] at h2'
      exact leB_congr ((BPair.oneValue_symm Ef5)) Ef4 h2'
    have h3 : BPair.ofNat 8 * L2 * kappa * W2 * n * kappa * D2 * W0 * W2 * mQ * s
          + BPair.ofNat 8 * L2 * kappa * W2 * n * a1 * BPair.ofNat 2 * K * n * mQ
          + BPair.ofNat 8 * L2 * kappa * W2 * n * windowsep.mag g2 * s
          + BPair.ofNat 8 * L2 * kappa * W2 * n * X2 * s
        ≤ BPair.ofNat 8 * L2 * kappa * kappa * D2 * W0 * W2 * W2 * mQ * s * n
          + BPair.ofNat 16 * L2 * kappa * W2 * a1 * K * mQ * n * n
          + (kappa * kappa * W2 * W2 * mQ * s * n + BPair.ofNat 128 * V * L2 * L2 * K * mQ * n * n)
          + BPair.ofNat 8 * L2 * kappa * W2 * X2 * s * n :=
      leB_add (leB_add (leB_add (leB_congr_left ((BPair.oneValue_symm Ef1)) (leB_refl _))
        (leB_congr_left (BPair.oneValue_symm Ef2) (leB_refl _))) g1)
        (leB_congr_left ((BPair.oneValue_symm Ef7)) (leB_refl _))
    refine leB_congr_left Ee1 (leB_trans h (leB_congr_right (?_) h3))
    exact polEqB [L2, kappa, D2, W0, W2, mQ, s, n, a1, K, V, X2]
        (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 8)) (Mon.var 9)) (Mon.var 5)) (Mon.var 7)) (Mon.var 7)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 10)) (Mon.var 0)) (Mon.var 0)) (Mon.var 9)) (Mon.var 5)) (Mon.var 7)) (Mon.var 7))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 11)) (Mon.var 6)) (Mon.var 7))))
        (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 8)) (Mon.var 9)) (Mon.var 5)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 10)) (Mon.var 0)) (Mon.var 0)) (Mon.var 9)) (Mon.var 5)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 11)) (Mon.var 6)) (Mon.var 7)))) (by decide +kernel)
  -- the self-capped square at the clearing
  have hF : BPair.unit ≤ BPair.ofNat 256 * L2 * L2 * kappa * kappa * W2 * W2 * s * s :=
    unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeOfNat 256) hL2') hL2') hkappa) hkappa) hW2) hW2) hs) hs
  have hF' : BPair.unit ≤ BPair.ofNat 256 * G * G * K * K * mQ * L2 * kappa * W2 :=
    unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeOfNat 256) hG) hG) hK) hK) hmQ) hL2') hkappa) hW2
  have d4 : BPair.ofNat 16 * L2 * kappa * W2 * X2 * s * (BPair.ofNat 16 * L2 * kappa * W2 * X2 * s)
      ≤ BPair.ofNat 2048 * G * G * K * K * mQ * mQ * L2 * L2 * kappa * kappa * kappa * D2 * W0
            * W2 * W2 * W2 * s * n
          + BPair.ofNat 4096 * G * G * K * K * K * mQ * mQ * L2 * L2 * kappa * kappa * W2 * W2 * a1
            * n * n
          + BPair.ofNat 256 * G * G * K * K * mQ * mQ * L2 * kappa * kappa * kappa * W2 * W2 * W2
            * s * n
          + BPair.ofNat 32768 * G * G * K * K * K * mQ * mQ * L2 * L2 * L2 * kappa * W2 * V * n * n
        + BPair.ofNat 128 * L2 * kappa * W2 * G * G * K * K * mQ * n
          * (BPair.ofNat 16 * L2 * kappa * W2 * X2 * s) := by
    have h := leB_mulR hF d3
    repeat rw [← BPair.mul_assoc] at h
    have h2 := leB_mulR hF' e5
    repeat first | rw [BPair.left_distrib] at h2 | rw [BPair.right_distrib] at h2
    repeat rw [← BPair.mul_assoc] at h2
    repeat rw [← BPair.add_assoc] at h2
    repeat rw [← BPair.mul_assoc]
    refine leB_congr_left (BPair.oneValue_symm Eg0) ?_
    refine leB_trans h ?_
    refine leB_trans (leB_congr_left ((BPair.oneValue_symm Eg1)) h2) ?_
    exact leB_add (leB_add (leB_add (leB_add (leB_congr_left (BPair.oneValue_symm Eh1) (leB_refl _))
      (leB_congr_left (BPair.oneValue_symm Eh2) (leB_refl _)))
      (leB_congr_left ((BPair.oneValue_symm Eh3)) (leB_refl _)))
      (leB_congr_left (BPair.oneValue_symm Eh4) (leB_refl _)))
      (leB_congr_left (BPair.oneValue_symm Eh5) (leB_refl _))
  have d5 := leB_sq_selfcap d4
  -- the doubled members against the fourth comparison, the two doubled reads absorbed
  have hab : BPair.ofNat 512 ≤ BPair.ofNat 256 * L2 * W0 * D2 := by
    refine leB_trans (leB_ofNat (by decide : 512 ≤ 256 * 2 * 1 * 2)) ?_
    refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (BPair.oneValue_trans (BPair.ofNat_mul _ _) (BPair.mul_congr
        (BPair.ofNat_mul _ _) (BPair.oneValue_refl _))) (BPair.oneValue_refl _)))) ?_
    refine leB_mul_mono (unitLeOfNat 2) (unitLeMul (unitLeMul (unitLeOfNat 256) hL2') hW0u) ?_ h2D2
    refine leB_mul_mono (unitLeOfNat 1) (unitLeMul (unitLeOfNat 256) hL2') ?_
      (leB_trans (leB_ofNat (Nat.le_refl 1)) hW0)
    exact leB_mulR (unitLeOfNat 256) h2L2
  have d6 : BPair.ofNat 2
        * (BPair.ofNat 2048 * G * G * K * K * mQ * mQ * L2 * L2 * kappa * kappa * kappa * D2 * W0
            * W2 * W2 * W2 * s * n
          + BPair.ofNat 4096 * G * G * K * K * K * mQ * mQ * L2 * L2 * kappa * kappa * W2 * W2 * a1
            * n * n
          + BPair.ofNat 256 * G * G * K * K * mQ * mQ * L2 * kappa * kappa * kappa * W2 * W2 * W2
            * s * n
          + BPair.ofNat 32768 * G * G * K * K * K * mQ * mQ * L2 * L2 * L2 * kappa * W2 * V * n * n)
        + BPair.ofNat 128 * L2 * kappa * W2 * G * G * K * K * mQ * n
          * (BPair.ofNat 128 * L2 * kappa * W2 * G * G * K * K * mQ * n)
      ≤ BPair.ofNat 4 * kappa * kappa * kappa * kappa * W2 * W2 * W2 * W2 * s * s * mQ * mQ := by
    have hR := leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 4) hkappa) hW2)
      (unitLeMul hmQ hmQ)) hR4
    repeat first | rw [BPair.left_distrib] at hR | rw [BPair.right_distrib] at hR
    repeat rw [← BPair.mul_assoc] at hR
    repeat rw [← BPair.add_assoc] at hR
    have hR' := leB_congr (BPair.add_congr (BPair.add_congr (BPair.add_congr Ej1 Ej2) Ej3) Ej4)
      Ej5 hR
    have t1 : BPair.ofNat 2 * BPair.ofNat 2048 * G * G * K * K * mQ * mQ * L2 * L2 * kappa * kappa
          * kappa * D2 * W0 * W2 * W2 * W2 * s * n
        ≤ BPair.ofNat 4096 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K
          * n * s * mQ * mQ :=
      leB_congr_left (BPair.oneValue_symm Ei1) (leB_refl _)
    have t3 : BPair.ofNat 2 * BPair.ofNat 256 * G * G * K * K * mQ * mQ * L2 * kappa * kappa * kappa
          * W2 * W2 * W2 * s * n
        ≤ BPair.ofNat 256 * L2 * L2 * G * G * W0 * kappa * kappa * kappa * D2 * W2 * W2 * W2 * K * K
          * n * s * mQ * mQ := by
      refine leB_congr_left (BPair.oneValue_symm Ei3) ?_
      have h := leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
        (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
        hL2' hG) hG) hkappa) hkappa) hkappa) hW2) hW2) hW2) hK) hK) hn) hs) hmQ) hmQ) hab
      repeat rw [← BPair.mul_assoc] at h
      exact leB_congr_right (Ei6) h
    have t13 := leB_congr_right (BPair.oneValue_symm Eadd) (leB_add t1 t3)
    have t2 : BPair.ofNat 2 * BPair.ofNat 4096 * G * G * K * K * K * mQ * mQ * L2 * L2 * kappa * kappa
          * W2 * W2 * a1 * n * n
        ≤ BPair.ofNat 8192 * L2 * L2 * G * G * a1 * kappa * kappa * W2 * W2 * K * K * K * n * n * mQ
          * mQ :=
      leB_congr_left (BPair.oneValue_symm Ei2) (leB_refl _)
    have t4 : BPair.ofNat 2 * BPair.ofNat 32768 * G * G * K * K * K * mQ * mQ * L2 * L2 * L2 * kappa
          * W2 * V * n * n
        ≤ BPair.ofNat 65536 * L2 * L2 * L2 * G * G * V * kappa * W2 * K * K * K * n * n * mQ * mQ :=
      leB_congr_left (BPair.oneValue_symm Ei4) (leB_refl _)
    have t5 : BPair.ofNat 128 * L2 * kappa * W2 * G * G * K * K * mQ * n * BPair.ofNat 128 * L2
          * kappa * W2 * G * G * K * K * mQ * n
        ≤ BPair.ofNat 16384 * L2 * L2 * G * G * G * G * kappa * kappa * W2 * W2 * K * K * K * K * n
          * n * mQ * mQ :=
      leB_congr_left (BPair.oneValue_symm Ei5) (leB_refl _)
    repeat first | rw [BPair.left_distrib] | rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
    repeat rw [← BPair.add_assoc]
    rw [BPair.add_right_comm (BPair.ofNat 2 * BPair.ofNat 2048 * G * G * K * K * mQ * mQ * L2 * L2
      * kappa * kappa * kappa * D2 * W0 * W2 * W2 * W2 * s * n)
      (BPair.ofNat 2 * BPair.ofNat 4096 * G * G * K * K * K * mQ * mQ * L2 * L2 * kappa * kappa
        * W2 * W2 * a1 * n * n)
      (BPair.ofNat 2 * BPair.ofNat 256 * G * G * K * K * mQ * mQ * L2 * kappa * kappa * kappa
        * W2 * W2 * W2 * s * n)]
    exact leB_trans (leB_add (leB_add (leB_add t13 t2) t4) t5) hR'
  -- the deviation at the trichotomy of squares
  have d7 : BPair.ofNat 16 * L2 * kappa * W2 * X2 * s
      ≤ BPair.ofNat 2 * kappa * kappa * W2 * W2 * s * mQ := by
    have hb : BPair.unit ≤ BPair.ofNat 2 * kappa * kappa * W2 * W2 * s * mQ :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul h2 hkappa) hkappa) hW2)
        hW2) hs) hmQ
    refine leB_of_sq_le hb (leB_not_lt ?_)
    refine leB_trans d5 (leB_trans d6 ?_)
    repeat rw [← BPair.mul_assoc]
    exact leB_congr_right (BPair.oneValue_symm Ek1) (leB_refl _)
  have d8 : BPair.ofNat 8 * L2 * X2 ≤ kappa * W2 * mQ := by
    have hpos : BPair.unit < BPair.ofNat 2 * kappa * W2 * s :=
      unitLtMul (unitLtMul (unitLtMul (unitLtNat (by decide : 0 < 2)) hkappa0) hW20) hs0
    refine leB_unscale hpos ?_
    repeat rw [← BPair.mul_assoc]
    exact leB_congr Ek2 (Ek3) d7
  -- the derivative's remainder with the gap's second member at the third comparison
  have d9 : BPair.ofNat 8 * L2 * kappa * W2 * a1 * mQD + BPair.ofNat 64 * V * L2 * L2 * mQD
      ≤ kappa * kappa * W2 * W2 * mQ := by
    refine leB_unscale hs0 ?_
    have h := leB_mulR (unitLeAdd (unitLeMul hc ha1)
      (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 64) hV) hL2') hL2')) hmQD
    have h' := leB_mulL hmQ hR3
    repeat first | rw [BPair.left_distrib] at h | rw [BPair.right_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    repeat first | rw [BPair.left_distrib] at h' | rw [BPair.right_distrib] at h'
    repeat rw [← BPair.mul_assoc] at h'
    repeat first | rw [BPair.left_distrib] | rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
    refine leB_trans h ?_
    refine leB_trans (leB_add (leB_congr_left (BPair.oneValue_symm El3) (leB_refl _))
      (leB_congr_left (BPair.oneValue_symm El4) (leB_refl _))) ?_
    refine leB_trans (leB_congr_left (BPair.add_congr El1 El2) h') ?_
    exact leB_congr_left ((BPair.oneValue_symm El5)) (leB_refl _)
  -- the three members joined
  have d10 : BPair.ofNat 8 * L2 * kappa * W2 * windowsep.mag r2
      ≤ BPair.ofNat 3 * kappa * kappa * W2 * W2 * mQ := by
    have h := leB_mulR hc hr2
    rw [BPair.left_distrib, BPair.left_distrib] at h
    have p2 := hg2
    have p3 := leB_mulR (unitLeMul hkappa hW2) d8
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.mul_assoc] at p2
    repeat rw [← BPair.mul_assoc] at p3
    have p2' : BPair.ofNat 8 * L2 * kappa * W2 * windowsep.mag g2
        ≤ kappa * kappa * W2 * W2 * mQ + BPair.ofNat 64 * V * L2 * L2 * mQD :=
      leB_congr_left (Em0) p2
    have p3' : BPair.ofNat 8 * L2 * kappa * W2 * X2 ≤ kappa * kappa * W2 * W2 * mQ :=
      leB_congr ((BPair.oneValue_symm Em1)) (Em2) p3
    have e3x : (BPair.ofNat 3 * kappa * kappa * W2 * W2 * mQ).oneValue
        (kappa * kappa * W2 * W2 * mQ + kappa * kappa * W2 * W2 * mQ + kappa * kappa * W2 * W2 * mQ) :=
      polEqB [kappa, W2, mQ]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))) (by decide +kernel)
    refine leB_trans h ?_
    refine leB_trans (leB_add (leB_add (leB_refl _) p2') p3') ?_
    refine leB_congr_right (BPair.oneValue_symm e3x) ?_
    refine leB_congr_left (BPair.oneValue_of_eq ?_) (leB_add (leB_add d9 (leB_refl _)) (leB_refl _))
    rw [BPair.add_comm (kappa * kappa * W2 * W2 * mQ) (BPair.ofNat 64 * V * L2 * L2 * mQD),
      ← BPair.add_assoc]
  have d11 : BPair.ofNat 8 * L2 * windowsep.mag r2 ≤ BPair.ofNat 3 * kappa * W2 * mQ := by
    refine leB_unscale (unitLtMul hkappa0 hW20) ?_
    repeat rw [← BPair.mul_assoc]
    exact leB_congr (Em4) Em5 d10
  refine leB_unscale hL2 ?_
  have h := leB_mulR (unitLeMul h2 hsd) d11
  have h' := leB_mulR (unitLeMul (unitLeMul (unitLeOfNat 3) hkappa) hmQ) hsigm
  repeat rw [← BPair.mul_assoc] at h
  repeat rw [← BPair.mul_assoc] at h'
  repeat rw [← BPair.mul_assoc]
  exact leB_congr (BPair.oneValue_symm En1) (En3)
    (leB_trans h (leB_congr_left (BPair.oneValue_symm En2) h'))

/-! The variance floor and the mode weight. -/

/-- The variance floor at the remainder cell: at the two remainders'
caps, `|r₁| ≤ [1 : 16] κ σ_W μ[1]` and `|r₂| ≤ [3 : 16] κ σ_W μ[Q]`, and
`η (dim G + 2) ≤ 1`, the mode's variance read (`mode_variance`) puts the
variance `⟨v, v⟩`, at `⟨v, v⟩ μ[1] ≡ μ[Q²] μ[1] + (μ[Q]²)^∨`, at or beyond
five eighths of its leading member, `5 n κ sn μ[Q] ≤ 8 s sd ⟨v, v⟩`,
cleared at the scale pair `[n : s]` and the solve `[sn : sd]`. -/
theorem variance_floor (muQ muQ2 mu1 D n s sn sd kappa dG R1 R2 : BPair)
    (hvar : BPair.ofNat 4 * n * kappa * sn * muQ * mu1 * s + BPair.ofNat 4 * muQ * muQ * s * s * sd
      ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd
        + n * n * kappa * (dG + BPair.ofNat 2) * sn * muQ * mu1
        + BPair.ofNat 2 * n * s * R2 * sd * mu1 + BPair.ofNat 2 * n * muQ * R1 * sd * s)
    (hR1 : BPair.ofNat 16 * sd * R1 ≤ kappa * sn * mu1)
    (hR2 : BPair.ofNat 16 * sd * R2 ≤ BPair.ofNat 3 * kappa * sn * muQ)
    (heta : n * (dG + BPair.ofNat 2) ≤ s)
    (hD : (D * mu1).oneValue (muQ2 * mu1 + (muQ * muQ).swap))
    (hmu1 : BPair.unit < mu1) (hs0 : BPair.unit < s) (hn : BPair.unit ≤ n)
    (hkappa : BPair.unit ≤ kappa) (hsn : BPair.unit ≤ sn)
    (hmuQ : BPair.unit ≤ muQ) :
    BPair.ofNat 5 * n * kappa * sn * muQ ≤ BPair.ofNat 8 * s * sd * D := by
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hmu : BPair.unit ≤ mu1 := leB_of_lt hmu1
  generalize hDdef : dG + BPair.ofNat 2 = D2 at hvar heta
  have Ea1 : (BPair.ofNat 16 * n * kappa * sn * muQ * mu1 * n * D2).oneValue
      (BPair.ofNat 16 * n * n * kappa * D2 * sn * muQ * mu1) :=
    polEqB [n, kappa, sn, muQ, mu1, D2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 0)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 5)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Eb1 : (BPair.ofNat 2 * n * s * mu1 * BPair.ofNat 16 * sd * R2).oneValue
      (BPair.ofNat 16 * BPair.ofNat 2 * n * s * R2 * sd * mu1) :=
    polEqB [n, s, mu1, sd, R2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 16)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Eb2 : (BPair.ofNat 2 * n * s * mu1 * BPair.ofNat 3 * kappa * sn * muQ).oneValue
      (BPair.ofNat 6 * n * kappa * sn * muQ * mu1 * s) :=
    polEqB [n, s, mu1, kappa, sn, muQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 1))) (by decide +kernel)
  have Ec1 : (BPair.ofNat 2 * n * muQ * s * BPair.ofNat 16 * sd * R1).oneValue
      (BPair.ofNat 16 * BPair.ofNat 2 * n * muQ * R1 * sd * s) :=
    polEqB [n, muQ, s, sd, R1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 16)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Ec2 : (BPair.ofNat 2 * n * muQ * s * kappa * sn * mu1).oneValue
      (BPair.ofNat 2 * n * kappa * sn * muQ * mu1 * s) :=
    polEqB [n, muQ, s, kappa, sn, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 1)) (Mon.var 5)) (Mon.var 2))) (by decide +kernel)
  have Eg1 : (BPair.ofNat 8 * s * sd * muQ2 * mu1).oneValue
      (BPair.ofNat 8 * muQ2 * mu1 * s * sd) :=
    polEqB [s, sd, muQ2, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 1))) (by decide +kernel)
  have Eg2 : (BPair.ofNat 8 * s * sd * muQ * muQ).oneValue
      (BPair.ofNat 8 * muQ * muQ * s * sd) :=
    polEqB [s, sd, muQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 2)) (Mon.var 2)) (Mon.var 0)) (Mon.var 1))) (by decide +kernel)
  -- the three trailing members at the caps and the scale comparison
  have ta : BPair.ofNat 16 * n * n * kappa * D2 * sn * muQ * mu1
      ≤ BPair.ofNat 16 * n * kappa * sn * muQ * mu1 * s := by
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 16) hn)
      hkappa) hsn) hmuQ) hmu) heta
    repeat rw [← BPair.mul_assoc] at h
    exact leB_congr_left (Ea1) h
  have tb : BPair.ofNat 16 * BPair.ofNat 2 * n * s * R2 * sd * mu1
      ≤ BPair.ofNat 6 * n * kappa * sn * muQ * mu1 * s := by
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hn) hs) hmu) hR2
    repeat rw [← BPair.mul_assoc] at h
    exact leB_congr (Eb1) Eb2 h
  have tc : BPair.ofNat 16 * BPair.ofNat 2 * n * muQ * R1 * sd * s
      ≤ BPair.ofNat 2 * n * kappa * sn * muQ * mu1 * s := by
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hn) hmuQ) hs) hR1
    repeat rw [← BPair.mul_assoc] at h
    exact leB_congr (Ec1) (Ec2) h
  have h := leB_mulR (unitLeOfNat 16) hvar
  repeat first | rw [BPair.left_distrib] at h | rw [BPair.right_distrib] at h
  repeat rw [← BPair.mul_assoc] at h
  repeat rw [← BPair.add_assoc] at h
  have h' := leB_trans h (leB_add (leB_add (leB_add (leB_refl _) ta) tb) tc)
  have hL : (BPair.ofNat 16 * BPair.ofNat 4 * n * kappa * sn * muQ * mu1 * s + BPair.ofNat 16 * BPair.ofNat 4 * muQ * muQ * s * s * sd).oneValue
      (BPair.ofNat 24 * n * kappa * sn * muQ * mu1 * s + (BPair.ofNat 40 * n * kappa * sn * muQ * mu1 * s + BPair.ofNat 64 * muQ * muQ * s * s * sd)) :=
    polEqB [n, kappa, sn, muQ, mu1, s, sd]
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.cst 4)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.cst 4)) (Mon.var 3)) (Mon.var 3)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 24) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 3)) (Mon.var 3)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))))) (by decide +kernel)
  have hR : (BPair.ofNat 16 * BPair.ofNat 4 * muQ2 * mu1 * s * s * sd + BPair.ofNat 16 * n * kappa * sn * muQ * mu1 * s + BPair.ofNat 6 * n * kappa * sn * muQ * mu1 * s + BPair.ofNat 2 * n * kappa * sn * muQ * mu1 * s).oneValue
      (BPair.ofNat 24 * n * kappa * sn * muQ * mu1 * s + BPair.ofNat 64 * muQ2 * mu1 * s * s * sd) :=
    polEqB [muQ2, mu1, s, sd, n, kappa, sn, muQ]
      (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.cst 4)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 1)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 1)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 1)) (Mon.var 2))))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 24) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 1)) (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)))) (by decide +kernel)
  have h'' := leB_cancelL (leB_congr hL hR h')
  -- the clearing at eight times the scale, the variance's own read at the moments
  have e8L : (BPair.ofNat 8 * s * (BPair.ofNat 5 * n * kappa * sn * muQ * mu1 + BPair.ofNat 8 * muQ * muQ * s * sd)).oneValue
      (BPair.ofNat 40 * n * kappa * sn * muQ * mu1 * s + BPair.ofNat 64 * muQ * muQ * s * s * sd) :=
    polEqB [s, n, kappa, sn, muQ, mu1, sd]
      (Pol.mul (Pol.mon (Mon.mul (Mon.cst 8) (Mon.var 0))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 4)) (Mon.var 4)) (Mon.var 0)) (Mon.var 6)))))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 4)) (Mon.var 4)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)))) (by decide +kernel)
  have e8R : (BPair.ofNat 8 * s * (BPair.ofNat 8 * muQ2 * mu1 * s * sd)).oneValue
      (BPair.ofNat 64 * muQ2 * mu1 * s * s * sd) :=
    polEqB [s, muQ2, mu1, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3))))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 3))) (by decide +kernel)
  have h3 := leB_unscale_left (unitLtMul (unitLtNat (by decide : 0 < 8)) hs0)
    (leB_congr (BPair.oneValue_symm e8L) (BPair.oneValue_symm e8R) h'')
  have h4 := leB_swapL (Y := (BPair.ofNat 8 * muQ * muQ * s * sd).swap) h3
  have e9 : (BPair.ofNat 8 * s * sd * D * mu1).oneValue
      (BPair.ofNat 8 * muQ2 * mu1 * s * sd + (BPair.ofNat 8 * muQ * muQ * s * sd).swap) := by
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hD) ?_
    rw [BPair.left_distrib, BPair.mul_swap]
    repeat rw [← BPair.mul_assoc]
    exact BPair.add_congr (Eg1) (swap_congr (Eg2))
  refine leB_unscale hmu1 ?_
  repeat rw [← BPair.mul_assoc]
  exact leB_congr_right (BPair.oneValue_symm e9) h4


/-- The variance floor at the roots' floor: `η κ |W|² μ[Q] ≤ [4 : 5]
(L + 2) ⟨v, v⟩`, the floor's solve against the profile's own
(`σ_- ≤ σ_W`), cleared. -/
theorem variance_side (muQ D n s sn sd kappa W2 L : BPair)
    (hvf : BPair.ofNat 5 * n * kappa * sn * muQ ≤ BPair.ofNat 8 * s * sd * D)
    (hsigm : BPair.ofNat 2 * W2 * sd ≤ sn * (L + BPair.ofNat 2))
    (hsd0 : BPair.unit < sd) (hn : BPair.unit ≤ n) (hkappa : BPair.unit ≤ kappa)
    (hmuQ : BPair.unit ≤ muQ) (hL : BPair.unit ≤ L) :
    BPair.ofNat 5 * n * kappa * W2 * muQ ≤ BPair.ofNat 4 * s * (L + BPair.ofNat 2) * D := by
  have hL2 : BPair.unit ≤ L + BPair.ofNat 2 := unitLeAdd hL (unitLeOfNat 2)
  generalize hLdef : L + BPair.ofNat 2 = L2 at hsigm hL2 ⊢
  have Ehg1 : (BPair.ofNat 5 * n * kappa * W2 * muQ * BPair.ofNat 2 * sd).oneValue
      (BPair.ofNat 10 * n * kappa * W2 * muQ * sd) :=
    polEqB [n, kappa, W2, muQ, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 10) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Ehg2 : (BPair.ofNat 5 * n * kappa * muQ * BPair.ofNat 2 * W2 * sd).oneValue
      (BPair.ofNat 10 * n * kappa * W2 * muQ * sd) :=
    polEqB [n, kappa, muQ, W2, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 10) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel)
  have Ehg3 : (BPair.ofNat 5 * n * kappa * muQ * sn * L2).oneValue
      (BPair.ofNat 5 * n * kappa * sn * muQ * L2) :=
    polEqB [n, kappa, muQ, sn, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel)
  have Ehg4 : (BPair.ofNat 8 * s * sd * D * L2).oneValue
      (BPair.ofNat 8 * s * L2 * D * sd) :=
    polEqB [s, sd, D, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 3)) (Mon.var 2)) (Mon.var 1))) (by decide +kernel)
  have Ehg5 : (BPair.ofNat 4 * s * L2 * D * BPair.ofNat 2 * sd).oneValue
      (BPair.ofNat 8 * s * L2 * D * sd) :=
    polEqB [s, L2, D, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3))) (by decide +kernel)
  have h1 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 5) hn) hkappa) hmuQ) hsigm
  have h2 := leB_mulL hL2 hvf
  repeat rw [← BPair.mul_assoc] at h1
  repeat rw [← BPair.mul_assoc] at h2
  refine leB_unscale (unitLtMul (unitLtNat (by decide : 0 < 2)) hsd0) ?_
  repeat rw [← BPair.mul_assoc]
  refine leB_congr (BPair.oneValue_symm Ehg1) (BPair.oneValue_symm Ehg5) ?_
  refine leB_trans (leB_congr_left Ehg2 h1) ?_
  refine leB_trans (leB_congr_left ((BPair.oneValue_symm Ehg3)) h2) ?_
  exact leB_congr_left ((BPair.oneValue_symm Ehg4)) (leB_refl _)

/-- The mode square's lower weight: at the first identity
`2 [s : n] ν[Q] ≡ κ dim G σ_W μ[1] + r₁` at the remainder's cap, the
profile's display `μ[Q] ≥ [1 : 2] ν[Q]` at `2 ν[Q] s ≤ 2 μ[Q] s + n ν[Q]`,
the solve's floor `σ_W ≥ |W|² [2 : L + 2]` and the near mass
`Δ ≤ vd μ[1]` at a clearing `Δ`, the moment sits at or beyond
`Q_- := η κ dim G |W|² ϑ [1 : 4 (L + 2)]`, cleared:
`Δ n κ dim G |W|² ≤ 4 (L + 2) s vd μ[Q]`. -/
theorem mode_lower (muQ nuQ mu1 Del vd n s sn sd kappa dG W2 L r1 : BPair)
    (hid1 : (BPair.ofNat 2 * nuQ * s * sd).oneValue (n * (kappa * dG * sn * mu1 + r1 * sd)))
    (hQ : BPair.ofNat 2 * nuQ * s ≤ BPair.ofNat 2 * muQ * s + n * nuQ)
    (hr1 : BPair.ofNat 16 * sd * windowsep.mag r1 ≤ kappa * sn * mu1)
    (hsigm : BPair.ofNat 2 * W2 * sd ≤ sn * (L + BPair.ofNat 2))
    (hvth : Del ≤ vd * mu1)
    (hns : n ≤ s) (hdG : BPair.ofPos .one ≤ dG) (hsd0 : BPair.unit < sd)
    (hn : BPair.unit ≤ n) (hkappa : BPair.unit ≤ kappa) (hsn : BPair.unit ≤ sn)
    (hmu1 : BPair.unit ≤ mu1) (hnuQ : BPair.unit ≤ nuQ) (hvd : BPair.unit ≤ vd)
    (hW2 : BPair.unit ≤ W2) (hL : BPair.unit ≤ L) :
    Del * n * kappa * dG * W2 ≤ BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd * muQ := by
  have hL2 : BPair.unit ≤ L + BPair.ofNat 2 := unitLeAdd hL (unitLeOfNat 2)
  generalize hLdef : L + BPair.ofNat 2 = L2 at hsigm hL2 ⊢
  have hdG0 : BPair.unit ≤ dG := leB_trans (leB_of_lt (unitLtOfPos .one)) hdG
  have hsd : BPair.unit ≤ sd := leB_of_lt hsd0
  have Eb1 : (n * BPair.ofNat 16 * sd * windowsep.mag r1).oneValue
      (BPair.ofNat 16 * n * sd * windowsep.mag r1) :=
    polEqB [n, sd, (windowsep.mag r1)]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 16)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Eb2 : (n * kappa * sn * mu1 * BPair.ofNat 8 * dG).oneValue
      (BPair.ofNat 8 * n * kappa * dG * sn * mu1) :=
    polEqB [n, kappa, sn, mu1, dG]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 8)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 2)) (Mon.var 3))) (by decide +kernel)
  have Ec1 : (BPair.ofNat 16 * n * kappa * dG * sn * mu1).oneValue
      (BPair.ofNat 8 * n * kappa * dG * sn * mu1 + BPair.ofNat 8 * n * kappa * dG * sn * mu1) :=
    polEqB [n, kappa, dG, sn, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))) (by decide +kernel)
  have Ec2 : (BPair.ofNat 16 * BPair.ofNat 2 * nuQ * s * sd).oneValue
      (BPair.ofNat 32 * nuQ * s * sd) :=
    polEqB [nuQ, s, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Ed1 : (BPair.ofNat 32 * sd * BPair.ofNat 2 * muQ * s).oneValue
      (BPair.ofNat 64 * muQ * s * sd) :=
    polEqB [sd, muQ, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 1)) (Mon.var 2)) (Mon.var 0))) (by decide +kernel)
  have Ed2 : (BPair.ofNat 32 * sd * nuQ * s).oneValue
      (BPair.ofNat 32 * nuQ * s * sd) :=
    polEqB [sd, nuQ, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 1)) (Mon.var 2)) (Mon.var 0))) (by decide +kernel)
  have Ed4 : (BPair.ofNat 64 * muQ * s * sd).oneValue
      (BPair.ofNat 8 * BPair.ofNat 8 * muQ * s * sd) :=
    polEqB [muQ, s, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.cst 8)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Ee1 : (n * kappa * dG * mu1 * BPair.ofNat 2 * W2 * sd).oneValue
      (BPair.ofNat 2 * n * kappa * dG * W2 * mu1 * sd) :=
    polEqB [n, kappa, dG, mu1, W2, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 4)) (Mon.var 3)) (Mon.var 5))) (by decide +kernel)
  have Ee2 : (n * kappa * dG * mu1 * sn * L2).oneValue
      (n * kappa * dG * sn * mu1 * L2) :=
    polEqB [n, kappa, dG, mu1, sn, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 4)) (Mon.var 3)) (Mon.var 5))) (by decide +kernel)
  have Ee3 : (BPair.ofNat 8 * muQ * s * sd * L2).oneValue
      (BPair.ofNat 8 * muQ * s * L2 * sd) :=
    polEqB [muQ, s, sd, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Ee4 : (BPair.ofNat 2 * n * kappa * dG * W2 * mu1).oneValue
      (n * kappa * dG * W2 * mu1 * BPair.ofNat 2) :=
    polEqB [n, kappa, dG, W2, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 2))) (by decide +kernel)
  have Ee5 : (BPair.ofNat 8 * muQ * s * L2).oneValue
      (BPair.ofNat 4 * muQ * s * L2 * BPair.ofNat 2) :=
    polEqB [muQ, s, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2))) (by decide +kernel)
  have Ef1 : (vd * mu1 * n * kappa * dG * W2).oneValue
      (vd * n * kappa * dG * W2 * mu1) :=
    polEqB [vd, mu1, n, kappa, dG, W2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 1))) (by decide +kernel)
  have Ef2 : (vd * BPair.ofNat 4 * muQ * s * L2).oneValue
      (BPair.ofNat 4 * L2 * s * vd * muQ) :=
    polEqB [vd, muQ, s, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 4)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 3)) (Mon.var 2)) (Mon.var 0)) (Mon.var 1))) (by decide +kernel)
  -- the first identity read from below at the remainder's cap
  have c1 : (n * sd * windowsep.mag r1).swap ≤ n * r1 * sd := by
    have h := leB_swap (leB_mulR (unitLeMul hn hsd) (windowsep.swap_le_mag r1))
    rw [BPair.mul_swap, BPair.swap_swap, BPair.mul_right_comm n sd r1] at h
    exact h
  have a1 : n * kappa * dG * sn * mu1
      ≤ BPair.ofNat 2 * nuQ * s * sd + n * sd * windowsep.mag r1 := by
    refine leB_swapL ?_
    refine leB_congr_right (BPair.oneValue_symm hid1) ?_
    rw [BPair.left_distrib]
    repeat rw [← BPair.mul_assoc]
    exact leB_add (leB_refl _) c1
  have a2 : BPair.ofNat 16 * n * sd * windowsep.mag r1
      ≤ BPair.ofNat 8 * n * kappa * dG * sn * mu1 := by
    have h := leB_mulR hn hr1
    have h1 : BPair.ofNat 1 ≤ BPair.ofNat 8 * dG :=
      leB_trans (leB_ofNat (by decide : 1 ≤ 8))
        (leB_congr_left (BPair.mul_ofNat_one _) (leB_mulR (unitLeOfNat 8) hdG))
    have h8 := leB_mulR (unitLeMul (unitLeMul (unitLeMul hn hkappa) hsn) hmu1) h1
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.mul_assoc] at h8
    refine leB_congr_left (Eb1) (leB_trans h ?_)
    exact leB_trans (leB_congr_left (BPair.mul_ofNat_one _) h8)
      (leB_congr_left (BPair.oneValue_symm Eb2) (leB_refl _))
  have a3 : BPair.ofNat 8 * n * kappa * dG * sn * mu1 ≤ BPair.ofNat 32 * nuQ * s * sd := by
    have h := leB_mulR (unitLeOfNat 16) a1
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    have h' := leB_trans h (leB_add (leB_congr_left (BPair.oneValue_symm Ec2) (leB_refl _)) a2)
    have h'' := leB_congr_left Ec1 h'
    refine leB_cancelL (x := BPair.ofNat 8 * n * kappa * dG * sn * mu1) ?_
    exact leB_congr_right (BPair.oneValue_of_eq (BPair.add_comm _ _)) h''
  -- the mode square's moment at half its read
  have a4 : nuQ * s ≤ BPair.ofNat 2 * muQ * s := by
    have h : nuQ * s + nuQ * s ≤ BPair.ofNat 2 * muQ * s + nuQ * s := by
      refine leB_congr (BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_two_mul nuQ))
          (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)))
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq (BPair.mul_comm s nuQ)))
        (leB_trans hQ (leB_add (leB_refl _) (leB_mulL hnuQ hns)))
    refine leB_cancelL (x := nuQ * s) ?_
    exact leB_congr_right (BPair.oneValue_of_eq (BPair.add_comm _ _)) h
  have a5 : n * kappa * dG * sn * mu1 ≤ BPair.ofNat 8 * muQ * s * sd := by
    refine leB_unscale_left (unitLtNat (by decide : 0 < 8)) ?_
    repeat rw [← BPair.mul_assoc]
    refine leB_trans a3 ?_
    refine leB_congr_left (Ed2) ?_
    have h := leB_mulR (unitLeMul (unitLeOfNat 32) hsd) a4
    repeat rw [← BPair.mul_assoc] at h
    exact leB_trans h (leB_congr_right Ed4 (leB_congr_left (BPair.oneValue_symm Ed1) (leB_refl _)))
  -- the floor's solve at the roots' floor
  have a6 : n * kappa * dG * W2 * mu1 ≤ BPair.ofNat 4 * muQ * s * L2 := by
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul hn hkappa) hdG0) hmu1) hsigm
    have h' := leB_mulL hL2 a5
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.mul_assoc] at h'
    have t : BPair.ofNat 2 * n * kappa * dG * W2 * mu1 * sd ≤ BPair.ofNat 8 * muQ * s * L2 * sd := by
      refine leB_congr_left Ee1 (leB_trans h ?_)
      refine leB_congr_left ((BPair.oneValue_symm Ee2)) (leB_trans h' ?_)
      exact leB_congr_left ((BPair.oneValue_symm Ee3)) (leB_refl _)
    have t' := leB_unscale hsd0 t
    refine leB_unscale (unitLtNat (by decide : 0 < 2)) ?_
    exact leB_congr Ee4 Ee5 t'
  have h := leB_mulL (unitLeMul (unitLeMul (unitLeMul hn hkappa) hdG0) hW2) hvth
  have h' := leB_mulR hvd a6
  repeat rw [← BPair.mul_assoc] at h
  repeat rw [← BPair.mul_assoc] at h'
  refine leB_trans h (leB_congr_left ((BPair.oneValue_symm Ef1)) ?_)
  exact leB_trans h' (leB_congr_left ((BPair.oneValue_symm Ef2)) (leB_refl _))

/-- The mode mean's read, `μ[Q]² ≤ dim G μ[1] ⟨v, v⟩`: at the first
identity at the remainder's cap, `μ[Q] ≤ ν[Q] ≤ [17 η : 32] κ dim G σ_W
μ[1]`, read against the variance's floor
`5 n κ sn μ[Q] ≤ 8 s sd ⟨v, v⟩`, cleared at the scale pair and the
solve. -/
theorem mode_mean_read (muQ nuQ mu1 D n s sn sd kappa dG r1 : BPair)
    (hid1 : (BPair.ofNat 2 * nuQ * s * sd).oneValue (n * (kappa * dG * sn * mu1 + r1 * sd)))
    (hle : muQ ≤ nuQ)
    (hr1 : BPair.ofNat 16 * sd * windowsep.mag r1 ≤ kappa * sn * mu1)
    (hvf : BPair.ofNat 5 * n * kappa * sn * muQ ≤ BPair.ofNat 8 * s * sd * D)
    (hdG : BPair.ofPos .one ≤ dG) (hs0 : BPair.unit < s) (hsd0 : BPair.unit < sd)
    (hn : BPair.unit ≤ n) (hkappa : BPair.unit ≤ kappa) (hsn : BPair.unit ≤ sn)
    (hmu1 : BPair.unit ≤ mu1) (hmuQ : BPair.unit ≤ muQ) :
    muQ * muQ ≤ dG * mu1 * D := by
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hsd : BPair.unit ≤ sd := leB_of_lt hsd0
  have hdG0 : BPair.unit ≤ dG := leB_trans (leB_of_lt (unitLtOfPos .one)) hdG
  have Ea1 : (BPair.ofNat 16 * BPair.ofNat 2 * nuQ * s * sd).oneValue
      (BPair.ofNat 32 * nuQ * s * sd) :=
    polEqB [nuQ, s, sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Eb1 : (BPair.ofNat 16 * n * windowsep.mag r1 * sd).oneValue
      (n * BPair.ofNat 16 * sd * windowsep.mag r1) :=
    polEqB [n, (windowsep.mag r1), sd]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 16)) (Mon.var 2)) (Mon.var 1))) (by decide +kernel)
  have Eb2 : (n * kappa * sn * mu1 * dG).oneValue
      (n * kappa * dG * sn * mu1) :=
    polEqB [n, kappa, sn, mu1, dG]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 2)) (Mon.var 3))) (by decide +kernel)
  have Ec1 : (BPair.ofNat 17 * n * kappa * dG * sn * mu1).oneValue
      (BPair.ofNat 16 * n * kappa * dG * sn * mu1 + BPair.ofNat 1 * n * kappa * dG * sn * mu1) :=
    polEqB [n, kappa, dG, sn, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 17) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))) (by decide +kernel)
  have Ec2 : (BPair.ofNat 32 * s * sd * muQ * nuQ).oneValue
      (muQ * BPair.ofNat 32 * nuQ * s * sd) :=
    polEqB [s, sd, muQ, nuQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.cst 32)) (Mon.var 3)) (Mon.var 0)) (Mon.var 1))) (by decide +kernel)
  have Ed1 : (muQ * BPair.ofNat 17 * n * kappa * dG * sn * mu1).oneValue
      (BPair.ofNat 17 * n * kappa * dG * sn * mu1 * muQ) :=
    polEqB [muQ, n, kappa, dG, sn, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 17)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 17) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0))) (by decide +kernel)
  have Ed2 : (BPair.ofNat 5 * n * kappa * sn * muQ * BPair.ofNat 4 * dG * mu1).oneValue
      (BPair.ofNat 20 * n * kappa * dG * sn * mu1 * muQ) :=
    polEqB [n, kappa, sn, muQ, dG, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 4)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 20) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 2)) (Mon.var 5)) (Mon.var 3))) (by decide +kernel)
  have Ed3 : (BPair.ofNat 8 * s * sd * D * BPair.ofNat 4 * dG * mu1).oneValue
      (BPair.ofNat 32 * s * sd * dG * mu1 * D) :=
    polEqB [s, sd, D, dG, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 4)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 2))) (by decide +kernel)
  -- the first identity's read of the mode square's moment at the remainder's cap
  have b1 : BPair.ofNat 32 * nuQ * s * sd ≤ BPair.ofNat 17 * n * kappa * dG * sn * mu1 := by
    have h : BPair.ofNat 16 * (BPair.ofNat 2 * nuQ * s * sd)
        ≤ BPair.ofNat 16 * (n * (kappa * dG * sn * mu1 + r1 * sd)) :=
      leB_congr_left (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hid1))
        (leB_refl _)
    repeat first | rw [BPair.left_distrib] at h | rw [BPair.right_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    have t1 : BPair.ofNat 16 * n * r1 * sd ≤ BPair.ofNat 16 * n * windowsep.mag r1 * sd :=
      leB_mulL hsd (leB_mulR (unitLeMul (unitLeOfNat 16) hn) (windowsep.le_mag r1))
    have t2 := leB_mulR hn hr1
    repeat rw [← BPair.mul_assoc] at t2
    have h1 : BPair.ofNat 1 ≤ dG := hdG
    have t3 := leB_mulR (unitLeMul (unitLeMul (unitLeMul hn hkappa) hsn) hmu1) h1
    repeat rw [← BPair.mul_assoc] at t3
    have t4 : BPair.ofNat 16 * n * r1 * sd ≤ n * kappa * dG * sn * mu1 := by
      refine leB_trans t1 (leB_congr_left ((BPair.oneValue_symm Eb1)) (leB_trans t2 ?_))
      exact leB_trans (leB_congr_left (BPair.mul_ofNat_one _) t3)
        (leB_congr_left ((BPair.oneValue_symm Eb2)) (leB_refl _))
    refine leB_congr_left Ea1 (leB_trans h ?_)
    refine leB_trans (leB_add (leB_refl _) t4) ?_
    refine leB_congr_right (BPair.oneValue_symm (BPair.oneValue_trans Ec1
      (BPair.add_congr (BPair.oneValue_refl _) ?_))) (leB_refl _)
    exact polEqB [n, kappa, dG, sn, mu1]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  -- the mode square's square against the variance's floor
  have b2 : BPair.ofNat 32 * s * sd * muQ * muQ
      ≤ BPair.ofNat 20 * n * kappa * dG * sn * mu1 * muQ := by
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 32) hs) hsd) hmuQ) hle
    have h' := leB_mulR hmuQ b1
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.mul_assoc] at h'
    have t : BPair.ofNat 17 * (n * kappa * dG * sn * mu1 * muQ)
        ≤ BPair.ofNat 20 * (n * kappa * dG * sn * mu1 * muQ) :=
      leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul hn hkappa) hdG0) hsn) hmu1)
        hmuQ) (leB_ofNat (by decide : 17 ≤ 20))
    repeat rw [← BPair.mul_assoc] at t
    refine leB_trans h (leB_congr_left ((BPair.oneValue_symm Ec2)) (leB_trans h' ?_))
    exact leB_trans (leB_congr_left (BPair.oneValue_symm Ed1) (leB_refl _)) t
  have b3 := leB_mulL (unitLeMul (unitLeMul (unitLeOfNat 4) hdG0) hmu1) hvf
  repeat rw [← BPair.mul_assoc] at b3
  refine leB_unscale_left (unitLtMul (unitLtMul (unitLtNat (by decide : 0 < 32)) hs0) hsd0) ?_
  repeat rw [← BPair.mul_assoc]
  refine leB_trans b2 ?_
  refine leB_trans (leB_congr_left Ed2 b3) ?_
  exact leB_congr_left (BPair.oneValue_symm Ed3) (leB_refl _)

/-- The moments' join at the variance and the mode mean's read:
`μ[1] μ[Q²] + μ[Q]² ≤ (1 + 2 dim G) μ[1] ⟨v, v⟩`, the variance identity
`⟨v, v⟩ μ[1] ≡ μ[Q²] μ[1] + (μ[Q]²)^∨` joined to twice the mode mean's
read `μ[Q]² ≤ dim G μ[1] ⟨v, v⟩`. -/
theorem mode_square_join (muQ muQ2 mu1 D dG : BPair)
    (hmean : muQ * muQ ≤ dG * mu1 * D)
    (hD : (D * mu1).oneValue (muQ2 * mu1 + (muQ * muQ).swap)) :
    mu1 * muQ2 + muQ * muQ ≤ (BPair.ofNat 1 + BPair.ofNat 2 * dG) * (mu1 * D) := by
  have c4 : (mu1 * muQ2 + muQ * muQ).oneValue (D * mu1 + (muQ * muQ + muQ * muQ)) := by
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.add_congr hD (BPair.oneValue_refl _))
      (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.add_swap_self _ _)
      (BPair.oneValue_refl _)) ?_
    exact BPair.add_congr (BPair.oneValue_of_eq (BPair.mul_comm _ _)) (BPair.oneValue_refl _)
  refine leB_congr_left (BPair.oneValue_symm c4) ?_
  refine leB_congr_right (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.right_distrib _ _ _))
    (BPair.add_congr (BPair.ofNat_one_mul _)
      (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
        (BPair.ofNat_two_mul _))))) ?_
  refine leB_add (leB_congr_left (BPair.oneValue_of_eq (BPair.mul_comm _ _)) (leB_refl _)) ?_
  refine leB_add ?_ ?_
  · exact leB_congr_right (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) hmean
  · exact leB_congr_right (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) hmean


/-- The mode weight's square moment at the near scale,
`μ[Z D²] ≤ 4 (Kη)² (1 + 2 dim G) ⟨v, v⟩`: the mode weight
`Z := ⟨Q : q̄⟩² ≤ 2 Q² + 2 q̄²` reads `μ[ZD²] μ[1]² ≤ 2 μ[1]² μ[Q²D²]
+ 2 μ[Q]² μ[D²]` at the mode mean `q̄ μ[1] = μ[Q]`, the near scale's
reads at the weights `Q²` and the unit, and the moments' join
(`mode_square_join`), cleared at the scale pair `[n : s]`. -/
theorem weight_square (mZD2 mQ2D2 mD2 muQ muQ2 mu1 D K n s dG : BPair)
    (hZ : mZD2 * (mu1 * mu1)
      ≤ BPair.ofNat 2 * (mu1 * mu1) * mQ2D2 + BPair.ofNat 2 * (muQ * muQ) * mD2)
    (hQ2 : mQ2D2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * muQ2)
    (hD2 : mD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * mu1)
    (hmean : muQ * muQ ≤ dG * mu1 * D)
    (hD : (D * mu1).oneValue (muQ2 * mu1 + (muQ * muQ).swap))
    (hmu1 : BPair.unit < mu1) (hn : BPair.unit ≤ n) (hs : BPair.unit ≤ s)
    (hK : BPair.unit ≤ K) (hmuQ : BPair.unit ≤ muQ) :
    mZD2 * (s * s)
      ≤ BPair.ofNat 4 * (K * K) * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * (n * n) * D := by
  have hmu : BPair.unit ≤ mu1 := leB_of_lt hmu1
  have h2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  generalize hEdef : BPair.ofNat 1 + BPair.ofNat 2 * dG = E2
  have Ea1 : (BPair.ofNat 2 * mu1 * mu1 * BPair.ofNat 2 * K * K * n * n * muQ2).oneValue
      (BPair.ofNat 4 * K * K * n * n * mu1 * mu1 * muQ2) :=
    polEqB [mu1, K, n, muQ2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 3))) (by decide +kernel)
  have Ea2 : (BPair.ofNat 2 * muQ * muQ * BPair.ofNat 2 * K * K * n * n * mu1).oneValue
      (BPair.ofNat 4 * K * K * n * n * mu1 * muQ * muQ) :=
    polEqB [muQ, K, n, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0))) (by decide +kernel)
  have Eb1 : (mZD2 * mu1 * mu1 * s * s).oneValue
      (mu1 * mu1 * mZD2 * s * s) :=
    polEqB [mZD2, mu1, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
  have Eb2 : (BPair.ofNat 4 * K * K * n * n * mu1 * E2 * mu1 * D).oneValue
      (mu1 * mu1 * BPair.ofNat 4 * K * K * E2 * n * n * D) :=
    polEqB [K, n, mu1, E2, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.cst 4)) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1)) (Mon.var 4))) (by decide +kernel)
  -- the two weights at the near scale
  have c1 := leB_mulL (unitLeMul hs hs) hZ
  rw [BPair.right_distrib] at c1
  repeat rw [← BPair.mul_assoc] at c1
  have c2 := leB_mulR (unitLeMul (unitLeMul h2 hmu) hmu) hQ2
  have c3 := leB_mulR (unitLeMul (unitLeMul h2 hmuQ) hmuQ) hD2
  repeat rw [← BPair.mul_assoc] at c2
  repeat rw [← BPair.mul_assoc] at c3
  -- the moments' join at the variance and the mode mean's read
  have c5 : mu1 * muQ2 + muQ * muQ ≤ E2 * (mu1 * D) := by
    rw [← hEdef]
    exact mode_square_join muQ muQ2 mu1 D dG hmean hD
  have c6 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 4) hK) hK)
    hn) hn) hmu) c5
  rw [BPair.left_distrib] at c6
  repeat rw [← BPair.mul_assoc] at c6
  refine leB_unscale_left (unitLtMul hmu1 hmu1) ?_
  repeat rw [← BPair.mul_assoc]
  refine leB_congr (Eb1) (Eb2) ?_
  refine leB_trans c1 (leB_trans (leB_add c2 c3) ?_)
  exact leB_trans (leB_add (leB_congr_left (BPair.oneValue_symm Ea1) (leB_refl _))
    (leB_congr_left (BPair.oneValue_symm Ea2) (leB_refl _))) c6

/-- The mode weight identity's leading member: the third summand's
leading member folds over the plaquettes to
`4 κ μ[(Q − q̄) ⟨y_ω, y_W⟩]`, at `T3l μ[1] ≡ 4 κ (μ[Q] μ[⟨y_ω,y_W⟩]
+ (μ[1] μ[Q ⟨y_ω,y_W⟩])^∨)`, read at the two identities at `u = ω`,
`u' = W`, `2 [s : n] ν[Q ⟨y_W,y_ω⟩] ≡ κ (dim G + 2) σ₂ μ[Q] + r₂` and
`2 [s : n] ν[⟨y_W,y_ω⟩] ≡ κ dim G σ₂ μ[1] + r₁` at
`σ₂ := ωᵀω ≤ W₀² |W|²`, their remainders at the remainder cell, and the
profile's display `|μ[F] − ν[F]| ≤ [η : 2] ν[|F|]` at
`|⟨y_ω, y_W⟩| ≤ κ W₀² |W|² D + [1 : 2] Q`, so the leading summand
`κ dim G σ₂ μ[1] μ[Q]` withdraws against its balance partner and the
fold sits within `4 η κ² σ₂ μ[Q]` joined to the remainders' reads and
the display's reads, at or below `4 κ W₀² (L + 2) ⟨v, v⟩` joined to
`(13 κ W₀² (L + 2) K + 2 κ (1 + 2 dim G)) η ⟨v, v⟩` at the variance's
floor, its side read at the solve's floor, and the moments' join
(`mode_square_join`); cleared at the scale pair `[n : s]` and the two
solves `[sn : sd]`, `[sn₂ : sd₂]`, the magnitude the sorted pair's
(`windowsep.mag`). -/
theorem weight_lead (T3l mQY mY nuQY nuY nuAQY nuAY nuQD nuD nuQ2 nuQ mQD mD muQ muQ2 mu1 D K n s
      sn sd sn2 sd2 kappa dG W0 W2 L r1 r2 : BPair)
    (hF : (T3l * mu1).oneValue (BPair.ofNat 4 * kappa * (muQ * mY + (mu1 * mQY).swap)))
    (hidQ : (BPair.ofNat 2 * nuQY * s * sd2).oneValue
      (n * (kappa * (dG + BPair.ofNat 2) * sn2 * muQ + r2 * sd2)))
    (hidY : (BPair.ofNat 2 * nuY * s * sd2).oneValue (n * (kappa * dG * sn2 * mu1 + r1 * sd2)))
    (hr1 : BPair.ofNat 16 * sd * windowsep.mag r1 ≤ kappa * sn * mu1)
    (hr2 : BPair.ofNat 16 * sd * windowsep.mag r2 ≤ BPair.ofNat 3 * kappa * sn * muQ)
    (hpQY : BPair.ofNat 2 * s * mQY ≤ BPair.ofNat 2 * s * nuQY + n * nuAQY)
    (hpQY' : BPair.ofNat 2 * s * nuQY ≤ BPair.ofNat 2 * s * mQY + n * nuAQY)
    (hpY : BPair.ofNat 2 * s * mY ≤ BPair.ofNat 2 * s * nuY + n * nuAY)
    (hpY' : BPair.ofNat 2 * s * nuY ≤ BPair.ofNat 2 * s * mY + n * nuAY)
    (hAQY : BPair.ofNat 2 * nuAQY ≤ BPair.ofNat 2 * kappa * (W0 * W0) * W2 * nuQD + nuQ2)
    (hAY : BPair.ofNat 2 * nuAY ≤ BPair.ofNat 2 * kappa * (W0 * W0) * W2 * nuD + nuQ)
    (hnuQD : nuQD ≤ BPair.ofNat 2 * mQD) (hnuD : nuD ≤ BPair.ofNat 2 * mD)
    (hnuQ2 : nuQ2 ≤ BPair.ofNat 2 * muQ2) (hnuQ : nuQ ≤ BPair.ofNat 2 * muQ)
    (hmQD : mQD * s ≤ BPair.ofNat 2 * K * n * muQ) (hmD : mD * s ≤ BPair.ofNat 2 * K * n * mu1)
    (hsig2 : sn2 ≤ W0 * W0 * W2 * sd2)
    (hvf : BPair.ofNat 5 * n * kappa * sn * muQ ≤ BPair.ofNat 8 * s * sd * D)
    (hvs : BPair.ofNat 5 * n * kappa * W2 * muQ ≤ BPair.ofNat 4 * s * (L + BPair.ofNat 2) * D)
    (hmean : muQ * muQ ≤ dG * mu1 * D)
    (hD : (D * mu1).oneValue (muQ2 * mu1 + (muQ * muQ).swap))
    (hmu1 : BPair.unit < mu1) (hs0 : BPair.unit < s) (hsd0 : BPair.unit < sd)
    (hsd20 : BPair.unit < sd2) (hW0 : BPair.ofPos .one ≤ W0)
    (hn : BPair.unit ≤ n) (hK : BPair.unit ≤ K) (hW2 : BPair.unit ≤ W2) (hL : BPair.unit ≤ L)
    (hmuQ : BPair.unit ≤ muQ) (hD0 : BPair.unit ≤ D) (hkappa : BPair.unit ≤ kappa)
    (hsn2 : BPair.unit ≤ sn2) (hdG : BPair.unit ≤ dG) :
    s * windowsep.mag T3l
      ≤ D * (BPair.ofNat 4 * kappa * (W0 * W0) * (L + BPair.ofNat 2) * s
        + BPair.ofNat 13 * kappa * (W0 * W0) * (L + BPair.ofNat 2) * K * n
        + BPair.ofNat 2 * kappa * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * n) := by
  have hmu : BPair.unit ≤ mu1 := leB_of_lt hmu1
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hsd : BPair.unit ≤ sd := leB_of_lt hsd0
  have hsd2 : BPair.unit ≤ sd2 := leB_of_lt hsd20
  have hW0u : BPair.unit ≤ W0 := leB_trans (leB_of_lt (unitLtOfPos .one)) hW0
  have hL2 : BPair.unit ≤ L + BPair.ofNat 2 := unitLeAdd hL (unitLeOfNat 2)
  have h2L2 : BPair.ofNat 2 ≤ L + BPair.ofNat 2 :=
    leB_congr_left (BPair.unit_add _) (leB_add hL (leB_refl (BPair.ofNat 2)))
  have h2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  have hW01 : BPair.ofNat 1 ≤ W0 := hW0
  have h1L2 : BPair.ofNat 1 ≤ W0 * W0 * (L + BPair.ofNat 2) := by
    have hW : BPair.ofNat 1 * BPair.ofNat 1 ≤ W0 * W0 :=
      leB_mul_mono (unitLeOfNat 1) hW0u hW01 hW01
    have h11 : BPair.ofNat 1 * BPair.ofNat 1 * BPair.ofNat 2 ≤ W0 * W0 * (L + BPair.ofNat 2) :=
      leB_mul_mono h2 (unitLeMul hW0u hW0u) hW h2L2
    refine leB_trans (leB_ofNat (by decide : 1 ≤ 2)) ?_
    exact leB_congr_left (BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_one_mul _))
      (BPair.ofNat_one_mul _)) h11
  have hE2 : BPair.unit ≤ BPair.ofNat 1 + BPair.ofNat 2 * dG :=
    unitLeAdd (unitLeOfNat 1) (unitLeMul h2 hdG)
  have hjoin := mode_square_join muQ muQ2 mu1 D dG hmean hD
  generalize hLdef : L + BPair.ofNat 2 = L2 at hvs hL2 h1L2 ⊢
  generalize hEdef : BPair.ofNat 1 + BPair.ofNat 2 * dG = E2 at hjoin hE2 ⊢
  have Ed4 : (BPair.ofNat 2 * kappa * W0 * W0 * W2 * sd2 * mu1 * n * BPair.ofNat 2 * BPair.ofNat 2 * K * n * muQ).oneValue
      (BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1) :=
    polEqB [kappa, W0, W2, sd2, mu1, n, K, muQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 2)) (Mon.cst 2)) (Mon.var 6)) (Mon.var 5)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 6)) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 7)) (Mon.var 4))) (by decide +kernel)
  have Ed6 : (BPair.ofNat 2 * kappa * W0 * W0 * W2 * sd2 * muQ * n * BPair.ofNat 2 * BPair.ofNat 2 * K * n * mu1).oneValue
      (BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1) :=
    polEqB [kappa, W0, W2, sd2, muQ, n, K, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 2)) (Mon.cst 2)) (Mon.var 6)) (Mon.var 5)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 6)) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 4)) (Mon.var 7))) (by decide +kernel)
  have Ed8 : (s * sd2 * n * mu1 * BPair.ofNat 2 * muQ2).oneValue
      (BPair.ofNat 2 * s * sd2 * n * mu1 * muQ2) :=
    polEqB [s, sd2, n, mu1, muQ2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Ed10 : (s * sd2 * n * muQ * BPair.ofNat 2 * muQ).oneValue
      (BPair.ofNat 2 * s * sd2 * n * muQ * muQ) :=
    polEqB [s, sd2, n, muQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have Ed11 : (BPair.ofNat 16 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1).oneValue
      (BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1 + BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1) :=
    polEqB [kappa, W0, W2, K, n, sd2, muQ, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))) (by decide +kernel)
  have Ef1 : (BPair.ofNat 80 * kappa * s * sd * mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).oneValue
      (BPair.ofNat 160 * kappa * kappa * n * s * sd * sn2 * muQ * mu1) :=
    polEqB [kappa, s, sd, mu1, n, sn2, muQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 0)) (Mon.cst 2)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 160) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 1)) (Mon.var 2)) (Mon.var 5)) (Mon.var 6)) (Mon.var 3))) (by decide +kernel)
  have Ef2 : (BPair.ofNat 160 * kappa * kappa * n * s * sd * W0 * W0 * W2 * sd2 * muQ * mu1).oneValue
      (BPair.ofNat 32 * kappa * W0 * W0 * s * sd * sd2 * mu1 * BPair.ofNat 5 * n * kappa * W2 * muQ) :=
    polEqB [kappa, n, s, sd, W0, W2, sd2, muQ, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 160) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 4)) (Mon.var 4)) (Mon.var 2)) (Mon.var 3)) (Mon.var 6)) (Mon.var 8)) (Mon.cst 5)) (Mon.var 1)) (Mon.var 0)) (Mon.var 5)) (Mon.var 7))) (by decide +kernel)
  have Ef3 : (BPair.ofNat 32 * kappa * W0 * W0 * s * sd * sd2 * mu1 * BPair.ofNat 4 * s * L2 * D).oneValue
      (BPair.ofNat 128 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D) :=
    polEqB [kappa, W0, s, sd, sd2, mu1, L2, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 4)) (Mon.var 2)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 6)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 7))) (by decide +kernel)
  have Ef4 : (BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2).oneValue
      (BPair.ofNat 5 * kappa * s * BPair.ofNat 16 * sd * mu1 * n * r2 * sd2) :=
    polEqB [kappa, s, sd, mu1, n, r2, sd2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.cst 16)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ef5 : (BPair.ofNat 5 * kappa * s * BPair.ofNat 3 * n * kappa * sd2 * sn * muQ * mu1).oneValue
      (BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1) :=
    polEqB [kappa, s, n, sd2, sn, muQ, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.cst 3)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 15) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ef6 : (BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2).oneValue
      (BPair.ofNat 5 * kappa * s * BPair.ofNat 16 * sd * muQ * n * r1 * sd2) :=
    polEqB [kappa, s, sd, muQ, n, r1, sd2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.cst 16)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ef7 : (BPair.ofNat 5 * kappa * s * n * kappa * sd2 * sn * muQ * mu1).oneValue
      (BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1) :=
    polEqB [kappa, s, n, sd2, sn, muQ, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ef8 : (BPair.ofNat 20 * kappa * kappa * n * s * sd2 * sn * muQ * mu1).oneValue
      (BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 + BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1) :=
    polEqB [kappa, n, s, sd2, sn, muQ, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 20) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 15) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (by decide +kernel)
  have Ef9 : (BPair.ofNat 20 * kappa * kappa * n * s * sd2 * sn * muQ * mu1).oneValue
      (BPair.ofNat 4 * kappa * s * sd2 * mu1 * BPair.ofNat 5 * n * kappa * sn * muQ) :=
    polEqB [kappa, n, s, sd2, sn, muQ, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 20) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 6)) (Mon.cst 5)) (Mon.var 1)) (Mon.var 0)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  have Ef10 : (BPair.ofNat 4 * kappa * s * sd2 * mu1 * BPair.ofNat 8 * s * sd * D).oneValue
      (BPair.ofNat 32 * kappa * s * s * sd * sd2 * mu1 * D) :=
    polEqB [kappa, s, sd2, mu1, sd, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 8)) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 4)) (Mon.var 2)) (Mon.var 3)) (Mon.var 5))) (by decide +kernel)
  have Ef11 : (BPair.ofNat 32 * kappa * s * s * sd * sd2 * mu1 * D * W0 * W0 * L2).oneValue
      (BPair.ofNat 32 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D) :=
    polEqB [kappa, s, sd, sd2, mu1, D, W0, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  have Ef12 : (BPair.ofNat 160 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D).oneValue
      (BPair.ofNat 128 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D + BPair.ofNat 32 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D) :=
    polEqB [kappa, W0, L2, s, sd, sd2, mu1, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 160) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))) (by decide +kernel)
  have Ef13 : (BPair.ofNat 80 * kappa * s * sd * sd2 * mu1 * n * nuAQY).oneValue
      (BPair.ofNat 40 * kappa * sd * BPair.ofNat 2 * s * sd2 * mu1 * n * nuAQY) :=
    polEqB [kappa, s, sd, sd2, mu1, n, nuAQY]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ef14 : (BPair.ofNat 80 * kappa * s * sd * sd2 * muQ * n * nuAY).oneValue
      (BPair.ofNat 40 * kappa * sd * BPair.ofNat 2 * s * sd2 * muQ * n * nuAY) :=
    polEqB [kappa, s, sd, sd2, muQ, n, nuAY]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ef15 : (BPair.ofNat 40 * kappa * sd * BPair.ofNat 16 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1).oneValue
      (BPair.ofNat 128 * kappa * W0 * W0 * K * n * sd * sd2 * mu1 * BPair.ofNat 5 * n * kappa * W2 * muQ) :=
    polEqB [kappa, sd, W0, W2, K, n, sd2, muQ, mu1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.cst 16)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5)) (Mon.var 1)) (Mon.var 6)) (Mon.var 8)) (Mon.cst 5)) (Mon.var 5)) (Mon.var 0)) (Mon.var 3)) (Mon.var 7))) (by decide +kernel)
  have Ef16 : (BPair.ofNat 128 * kappa * W0 * W0 * K * n * sd * sd2 * mu1 * BPair.ofNat 4 * s * L2 * D).oneValue
      (BPair.ofNat 512 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D) :=
    polEqB [kappa, W0, K, n, sd, sd2, mu1, s, L2, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.cst 4)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 512) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 8)) (Mon.var 2)) (Mon.var 3)) (Mon.var 7)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 9))) (by decide +kernel)
  have Ef17 : (BPair.ofNat 40 * kappa * sd * BPair.ofNat 2 * s * sd2 * n * E2 * mu1 * D).oneValue
      (BPair.ofNat 80 * kappa * E2 * n * s * sd * sd2 * mu1 * D) :=
    polEqB [kappa, sd, s, sd2, n, E2, mu1, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 0)) (Mon.var 5)) (Mon.var 4)) (Mon.var 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 6)) (Mon.var 7))) (by decide +kernel)
  have Eg1 : (BPair.ofNat 40 * s * sd * sd2 * mu1 * D * BPair.ofNat 4 * kappa * W0 * W0 * L2 * s).oneValue
      (BPair.ofNat 160 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D) :=
    polEqB [s, sd, sd2, mu1, D, kappa, W0, L2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 0)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 160) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Eg2 : (BPair.ofNat 40 * s * sd * sd2 * mu1 * D * BPair.ofNat 13 * kappa * W0 * W0 * L2 * K * n).oneValue
      (BPair.ofNat 520 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D) :=
    polEqB [s, sd, sd2, mu1, D, kappa, W0, L2, K, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 13)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 520) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Eg3 : (BPair.ofNat 40 * s * sd * sd2 * mu1 * D * BPair.ofNat 2 * kappa * E2 * n).oneValue
      (BPair.ofNat 80 * kappa * E2 * n * s * sd * sd2 * mu1 * D) :=
    polEqB [s, sd, sd2, mu1, D, kappa, E2, n]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 2)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Eg4 : (BPair.ofNat 40 * s * sd * sd2 * BPair.ofNat 4 * kappa * s * mu1 * mQY).oneValue
      (BPair.ofNat 80 * kappa * s * sd * BPair.ofNat 2 * s * sd2 * mu1 * mQY) :=
    polEqB [s, sd, sd2, kappa, mu1, mQY]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 4)) (Mon.var 3)) (Mon.var 0)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 3)) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  have Eg5 : (BPair.ofNat 40 * s * sd * sd2 * BPair.ofNat 4 * kappa * s * muQ * mY).oneValue
      (BPair.ofNat 80 * kappa * s * sd * BPair.ofNat 2 * s * sd2 * muQ * mY) :=
    polEqB [s, sd, sd2, kappa, muQ, mY]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 40) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 4)) (Mon.var 3)) (Mon.var 0)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 80) (Mon.var 3)) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  -- the units at the clearings
  have hc80 : BPair.unit ≤ BPair.ofNat 80 * kappa * s * sd := (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 80) hkappa) hs) hsd)
  have hc5 : BPair.unit ≤ BPair.ofNat 5 * kappa * s := (unitLeMul (unitLeMul (unitLeOfNat 5) hkappa) hs)
  have hc40 : BPair.unit < BPair.ofNat 40 * s * sd * sd2 :=
    unitLtMul (unitLtMul (unitLtMul (unitLtNat (by decide : 0 < 40)) hs0) hsd0) hsd20
  -- the two identities distributed at the moments' clearings
  have I1 : (mu1 * BPair.ofNat 2 * nuQY * s * sd2).oneValue (mu1 * n * kappa * dG * sn2 * muQ + mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ + mu1 * n * r2 * sd2) := by
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (show mu1 * BPair.ofNat 2 * nuQY * s * sd2 = mu1 * (BPair.ofNat 2 * nuQY * s * sd2) by repeat rw [← BPair.mul_assoc])) (?_ : ((mu1 * (BPair.ofNat 2 * nuQY * s * sd2))).oneValue (mu1 * n * kappa * dG * sn2 * muQ + mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ + mu1 * n * r2 * sd2))
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hidQ) ?_
    exact polEqB [mu1, n, kappa, dG, sn2, muQ, r2, sd2]
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 7))))))
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 6)) (Mon.var 7)))) (by decide +kernel)
  have I2 : (muQ * BPair.ofNat 2 * nuY * s * sd2).oneValue (muQ * n * kappa * dG * sn2 * mu1 + muQ * n * r1 * sd2) := by
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (show muQ * BPair.ofNat 2 * nuY * s * sd2 = muQ * (BPair.ofNat 2 * nuY * s * sd2) by repeat rw [← BPair.mul_assoc])) (?_ : ((muQ * (BPair.ofNat 2 * nuY * s * sd2))).oneValue (muQ * n * kappa * dG * sn2 * mu1 + muQ * n * r1 * sd2))
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hidY) ?_
    exact polEqB [muQ, n, kappa, dG, sn2, mu1, r1, sd2]
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 7))))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 6)) (Mon.var 7)))) (by decide +kernel)
  -- the profile reads at the two moments' clearings
  have Pa1 : BPair.ofNat 2 * s * sd2 * mu1 * mQY ≤ mu1 * n * kappa * dG * sn2 * muQ + mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ + mu1 * n * r2 * sd2 + sd2 * mu1 * n * nuAQY := by
    have h := leB_mulR (unitLeMul hsd2 hmu) hpQY
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    have h : (BPair.ofNat 2 * s * sd2 * mu1 * mQY) ≤ (mu1 * BPair.ofNat 2 * nuQY * s * sd2) + sd2 * mu1 * n * nuAQY :=
      leB_congr (polEqB [sd2, mu1, s, mQY]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3))) (by decide +kernel))
        (polEqB [sd2, mu1, s, nuQY, n, nuAQY]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 2)) (Mon.var 3)) (Mon.var 2)) (Mon.var 0))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)))) (by decide +kernel)) h
    exact leB_trans h (leB_add (leB_congr_left (BPair.oneValue_symm I1) (leB_refl _)) (leB_refl _))
  have Pa2 : muQ * n * kappa * dG * sn2 * mu1 + muQ * n * r1 * sd2 ≤ BPair.ofNat 2 * s * sd2 * muQ * mY + sd2 * muQ * n * nuAY := by
    have h := leB_mulR (unitLeMul hsd2 hmuQ) hpY'
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    have h : (muQ * BPair.ofNat 2 * nuY * s * sd2) ≤ (BPair.ofNat 2 * s * sd2 * muQ * mY) + sd2 * muQ * n * nuAY :=
      leB_congr (polEqB [sd2, muQ, s, nuY]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 2)) (Mon.var 3)) (Mon.var 2)) (Mon.var 0))) (by decide +kernel))
        (polEqB [sd2, muQ, s, mY, n, nuAY]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)))) (by decide +kernel)) h
    exact leB_congr_left I2 h
  have Pb1 : BPair.ofNat 2 * s * sd2 * muQ * mY ≤ muQ * n * kappa * dG * sn2 * mu1 + muQ * n * r1 * sd2 + sd2 * muQ * n * nuAY := by
    have h := leB_mulR (unitLeMul hsd2 hmuQ) hpY
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    have h : (BPair.ofNat 2 * s * sd2 * muQ * mY) ≤ (muQ * BPair.ofNat 2 * nuY * s * sd2) + sd2 * muQ * n * nuAY :=
      leB_congr (polEqB [sd2, muQ, s, mY]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3))) (by decide +kernel))
        (polEqB [sd2, muQ, s, nuY, n, nuAY]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 2)) (Mon.var 3)) (Mon.var 2)) (Mon.var 0))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)))) (by decide +kernel)) h
    exact leB_trans h (leB_add (leB_congr_left (BPair.oneValue_symm I2) (leB_refl _)) (leB_refl _))
  have Pb2 : mu1 * n * kappa * dG * sn2 * muQ + mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ + mu1 * n * r2 * sd2 ≤ BPair.ofNat 2 * s * sd2 * mu1 * mQY + sd2 * mu1 * n * nuAQY := by
    have h := leB_mulR (unitLeMul hsd2 hmu) hpQY'
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    have h : (mu1 * BPair.ofNat 2 * nuQY * s * sd2) ≤ (BPair.ofNat 2 * s * sd2 * mu1 * mQY) + sd2 * mu1 * n * nuAQY :=
      leB_congr (polEqB [sd2, mu1, s, nuQY]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 2)) (Mon.var 3)) (Mon.var 2)) (Mon.var 0))) (by decide +kernel))
        (polEqB [sd2, mu1, s, mQY, n, nuAQY]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)))) (by decide +kernel)) h
    exact leB_congr_left I1 h
  have swapT : ∀ {a b c : BPair}, a ≤ b + c → b.swap ≤ a.swap + c := fun h =>
    leB_swapL (by rw [BPair.swap_add]; exact leB_swap h)
  -- the two sides, the leading member withdrawn against its balance partner
  have hRa : BPair.ofNat 2 * s * sd2 * mu1 * mQY + (BPair.ofNat 2 * s * sd2 * muQ * mY).swap ≤ mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ + mu1 * n * r2 * sd2 + (muQ * n * r1 * sd2).swap + sd2 * mu1 * n * nuAQY + sd2 * muQ * n * nuAY := by
    have h2 := swapT Pa2
    rw [← BPair.swap_add] at h2
    have h2 : (BPair.ofNat 2 * s * sd2 * muQ * mY).swap ≤ ((mu1 * n * kappa * dG * sn2 * muQ)).swap + (muQ * n * r1 * sd2).swap + sd2 * muQ * n * nuAY :=
      leB_congr (BPair.oneValue_refl _)
        ((BPair.add_congr (BPair.add_congr (swap_congr (polEqB [muQ, n, kappa, dG, sn2, mu1]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 0))) (by decide +kernel))) (BPair.oneValue_refl _)) (BPair.oneValue_refl _))) h2
    have h := leB_add Pa1 h2
    repeat rw [← BPair.add_assoc] at h
    have h : BPair.ofNat 2 * s * sd2 * mu1 * mQY + (BPair.ofNat 2 * s * sd2 * muQ * mY).swap ≤ ((mu1 * n * kappa * dG * sn2 * muQ + (mu1 * n * kappa * dG * sn2 * muQ).swap + (mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ + mu1 * n * r2 * sd2 + (muQ * n * r1 * sd2).swap + sd2 * mu1 * n * nuAQY + sd2 * muQ * n * nuAY))) :=
      leB_congr (BPair.oneValue_refl _)
        (polEqB [mu1, n, kappa, dG, sn2, muQ, r2, sd2, nuAQY, ((mu1 * n * kappa * dG * sn2 * muQ).swap), ((muQ * n * r1 * sd2).swap), nuAY]
        (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 0)) (Mon.var 1)) (Mon.var 8)))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 10))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 5)) (Mon.var 1)) (Mon.var 11))))
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.var 9))) (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.var 10))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 0)) (Mon.var 1)) (Mon.var 8)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 5)) (Mon.var 1)) (Mon.var 11))))) (by decide +kernel)) h
    exact leB_congr_right (BPair.oneValue_trans (BPair.add_congr (BPair.add_swap_null _)
      (BPair.oneValue_refl _)) (BPair.unit_add _)) h
  have hRb : BPair.ofNat 2 * s * sd2 * muQ * mY + (BPair.ofNat 2 * s * sd2 * mu1 * mQY).swap ≤ (mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap + (mu1 * n * r2 * sd2).swap + muQ * n * r1 * sd2 + sd2 * mu1 * n * nuAQY + sd2 * muQ * n * nuAY := by
    have h2 := swapT Pb2
    rw [← BPair.swap_add, ← BPair.swap_add] at h2
    have h := leB_add h2 Pb1
    have h : (BPair.ofNat 2 * s * sd2 * mu1 * mQY).swap + BPair.ofNat 2 * s * sd2 * muQ * mY ≤ (mu1 * n * kappa * dG * sn2 * muQ).swap + (mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap + (mu1 * n * r2 * sd2).swap + sd2 * mu1 * n * nuAQY + ((mu1 * n * kappa * dG * sn2 * muQ) + muQ * n * r1 * sd2 + sd2 * muQ * n * nuAY) :=
      leB_congr (BPair.oneValue_refl _)
        (polEqB [((mu1 * n * kappa * dG * sn2 * muQ).swap), ((mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap), ((mu1 * n * r2 * sd2).swap), sd2, mu1, n, nuAQY, muQ, kappa, dG, sn2, r1, nuAY]
        (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 5)) (Mon.var 8)) (Mon.var 9)) (Mon.var 10)) (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 5)) (Mon.var 11)) (Mon.var 3)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 7)) (Mon.var 5)) (Mon.var 12)))))
        (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.var 8)) (Mon.var 9)) (Mon.var 10)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 5)) (Mon.var 11)) (Mon.var 3)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 7)) (Mon.var 5)) (Mon.var 12))))) (by decide +kernel)) h
    repeat rw [← BPair.add_assoc] at h
    have h : (BPair.ofNat 2 * s * sd2 * mu1 * mQY).swap + BPair.ofNat 2 * s * sd2 * muQ * mY ≤ (((mu1 * n * kappa * dG * sn2 * muQ).swap + mu1 * n * kappa * dG * sn2 * muQ + ((mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap + (mu1 * n * r2 * sd2).swap + muQ * n * r1 * sd2 + sd2 * mu1 * n * nuAQY + sd2 * muQ * n * nuAY))) :=
      leB_congr (BPair.oneValue_refl _)
        (polEqB [((mu1 * n * kappa * dG * sn2 * muQ).swap), ((mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap), ((mu1 * n * r2 * sd2).swap), sd2, mu1, n, nuAQY, kappa, dG, sn2, muQ, r1, nuAY]
        (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 10)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 5)) (Mon.var 11)) (Mon.var 3)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 10)) (Mon.var 5)) (Mon.var 12))))
        (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)) (Mon.var 10)))) (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 5)) (Mon.var 11)) (Mon.var 3)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 10)) (Mon.var 5)) (Mon.var 12))))) (by decide +kernel)) h
    refine leB_congr_left (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    exact leB_congr_right (BPair.oneValue_trans (BPair.add_congr
      (BPair.swap_add_null (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) (BPair.unit_add _)) h
  -- the leading member's read at the solve's cap and the variance's side
  have Ta2 : BPair.ofNat 80 * kappa * s * sd * mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ ≤ BPair.ofNat 128 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D := by
    refine leB_congr_left (BPair.oneValue_symm Ef1) ?_
    have h1 := leB_mulL hmu (leB_mulL hmuQ (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 160) hkappa) hkappa) hn) hs) hsd) hsig2))
    repeat rw [← BPair.mul_assoc] at h1
    refine leB_trans h1 ?_
    refine leB_congr_left (BPair.oneValue_symm Ef2) ?_
    have h2 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 32) hkappa) hW0u) hW0u) hs) hsd) hsd2) hmu) hvs
    repeat rw [← BPair.mul_assoc] at h2
    exact leB_trans h2 (leB_congr_left (BPair.oneValue_symm Ef3) (leB_refl _))
  have Tb2 : (BPair.ofNat 80 * kappa * s * sd * mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap ≤ BPair.unit := by
    refine leUnitOfSwap ?_
    rw [BPair.swap_swap]
    exact (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 80) hkappa) hs) hsd) hmu) hn) hkappa) (unitLeOfNat 2)) hsn2) hmuQ)
  -- the remainders at their caps
  have T3core : BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * mu1 * n * sd2 * windowsep.mag r2) ≤ BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 := by
    refine leB_congr (polEqB [kappa, s, mu1, n, sd2, sd, (windowsep.mag r2)]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 4)) (Mon.cst 16)) (Mon.var 5)) (Mon.var 6))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 5)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6)))) (by decide +kernel))
      (BPair.oneValue_refl _) (?_ : BPair.ofNat 5 * kappa * s * ((mu1 * n * sd2 * BPair.ofNat 16 * sd * windowsep.mag r2)) ≤ BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    have h := leB_mulR (unitLeMul (unitLeMul hmu hn) hsd2) hr2
    repeat rw [← BPair.mul_assoc] at h
    refine leB_trans (leB_mulR hc5 h) ?_
    refine leB_congr (polEqB [kappa, s, n, sd2, sn, muQ, mu1]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 2)) (Mon.var 3)) (Mon.cst 3)) (Mon.var 0)) (Mon.var 4)) (Mon.var 5)))) (by decide +kernel))
      (BPair.oneValue_refl _) (?_ : BPair.ofNat 5 * kappa * s * ((BPair.ofNat 3 * n * kappa * sd2 * sn * muQ * mu1)) ≤ BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    refine leB_congr_left (BPair.oneValue_of_eq (show BPair.ofNat 5 * kappa * s * BPair.ofNat 3 * n * kappa * sd2 * sn * muQ * mu1
      = BPair.ofNat 5 * kappa * s * (BPair.ofNat 3 * n * kappa * sd2 * sn * muQ * mu1) by repeat rw [← BPair.mul_assoc])) ?_
    exact leB_congr_left (BPair.oneValue_symm Ef5) (leB_refl _)
  have Ncore : BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * muQ * n * sd2 * windowsep.mag r1) ≤ BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 := by
    refine leB_congr (polEqB [kappa, s, muQ, n, sd2, sd, (windowsep.mag r1)]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 4)) (Mon.cst 16)) (Mon.var 5)) (Mon.var 6))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 5)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6)))) (by decide +kernel))
      (BPair.oneValue_refl _) (?_ : BPair.ofNat 5 * kappa * s * ((muQ * n * sd2 * BPair.ofNat 16 * sd * windowsep.mag r1)) ≤ BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    have h := leB_mulR (unitLeMul (unitLeMul hmuQ hn) hsd2) hr1
    repeat rw [← BPair.mul_assoc] at h
    refine leB_trans (leB_mulR hc5 h) ?_
    refine leB_congr (polEqB [kappa, s, n, sd2, sn, muQ, mu1]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 4)) (Mon.var 6)))) (by decide +kernel))
      (BPair.oneValue_refl _) (?_ : BPair.ofNat 5 * kappa * s * ((n * kappa * sd2 * sn * muQ * mu1)) ≤ BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    refine leB_congr_left (BPair.oneValue_of_eq (show BPair.ofNat 5 * kappa * s * n * kappa * sd2 * sn * muQ * mu1
      = BPair.ofNat 5 * kappa * s * (n * kappa * sd2 * sn * muQ * mu1) by repeat rw [← BPair.mul_assoc])) ?_
    exact leB_congr_left (BPair.oneValue_symm Ef7) (leB_refl _)
  have Er2 : (BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * mu1 * n * sd2 * r2)).oneValue
      (BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * mu1 * n * r2 * sd2)) :=
    polEqB [kappa, s, sd, mu1, n, sd2, r2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6)) (Mon.var 5)))) (by decide +kernel)
  have Ta3 : BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2 ≤ BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 := by
    refine leB_congr_left (BPair.oneValue_symm Ef4) ?_
    refine leB_congr_left (BPair.oneValue_of_eq (show BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * mu1 * n * r2 * sd2)
      = BPair.ofNat 5 * kappa * s * BPair.ofNat 16 * sd * mu1 * n * r2 * sd2 by repeat rw [← BPair.mul_assoc])) ?_
    refine leB_congr Er2
      (BPair.oneValue_refl _) (?_ : BPair.ofNat 5 * kappa * s * ((BPair.ofNat 16 * sd * mu1 * n * sd2 * r2)) ≤ BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    exact leB_trans (leB_mulR hc5 (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 16) hsd) hmu) hn) hsd2) (windowsep.le_mag r2))) T3core
  have Tb3 : (BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2).swap ≤ BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 := by
    refine leB_congr_left (swap_congr (BPair.oneValue_symm Ef4)) ?_
    refine leB_congr_left (swap_congr (BPair.oneValue_of_eq (show BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * mu1 * n * r2 * sd2)
      = BPair.ofNat 5 * kappa * s * BPair.ofNat 16 * sd * mu1 * n * r2 * sd2 by repeat rw [← BPair.mul_assoc]))) ?_
    refine leB_congr ((swap_congr Er2))
      (BPair.oneValue_refl _) (?_ : (BPair.ofNat 5 * kappa * s * ((BPair.ofNat 16 * sd * mu1 * n * sd2 * r2))).swap ≤ BPair.ofNat 15 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    rw [← BPair.mul_swap, ← BPair.mul_swap]
    exact leB_trans (leB_mulR hc5 (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 16) hsd) hmu) hn) hsd2) (windowsep.swap_le_mag r2)))
      T3core
  have Er1 : (BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * muQ * n * sd2 * r1)).oneValue
      (BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * muQ * n * r1 * sd2)) :=
    polEqB [kappa, s, sd, muQ, n, sd2, r1]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6)) (Mon.var 5)))) (by decide +kernel)
  have TbN : BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2 ≤ BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 := by
    refine leB_congr_left (BPair.oneValue_symm Ef6) ?_
    refine leB_congr_left (BPair.oneValue_of_eq (show BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * muQ * n * r1 * sd2)
      = BPair.ofNat 5 * kappa * s * BPair.ofNat 16 * sd * muQ * n * r1 * sd2 by repeat rw [← BPair.mul_assoc])) ?_
    refine leB_congr Er1
      (BPair.oneValue_refl _) (?_ : BPair.ofNat 5 * kappa * s * ((BPair.ofNat 16 * sd * muQ * n * sd2 * r1)) ≤ BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    exact leB_trans (leB_mulR hc5 (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 16) hsd) hmuQ) hn) hsd2) (windowsep.le_mag r1))) Ncore
  have TaN : (BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2).swap ≤ BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 := by
    refine leB_congr_left (swap_congr (BPair.oneValue_symm Ef6)) ?_
    refine leB_congr_left (swap_congr (BPair.oneValue_of_eq (show BPair.ofNat 5 * kappa * s * (BPair.ofNat 16 * sd * muQ * n * r1 * sd2)
      = BPair.ofNat 5 * kappa * s * BPair.ofNat 16 * sd * muQ * n * r1 * sd2 by repeat rw [← BPair.mul_assoc]))) ?_
    refine leB_congr ((swap_congr Er1))
      (BPair.oneValue_refl _) (?_ : (BPair.ofNat 5 * kappa * s * ((BPair.ofNat 16 * sd * muQ * n * sd2 * r1))).swap ≤ BPair.ofNat 5 * kappa * kappa * n * s * sd2 * sn * muQ * mu1)
    rw [← BPair.mul_swap, ← BPair.mul_swap]
    exact leB_trans (leB_mulR hc5 (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 16) hsd) hmuQ) hn) hsd2) (windowsep.swap_le_mag r1)))
      Ncore
  -- the remainders' sum at the variance floor and the solve's floor
  have T20 : BPair.ofNat 20 * kappa * kappa * n * s * sd2 * sn * muQ * mu1 ≤ BPair.ofNat 32 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D := by
    refine leB_congr_left (BPair.oneValue_symm Ef9) ?_
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 4) hkappa) hs) hsd2) hmu) hvf
    repeat rw [← BPair.mul_assoc] at h
    refine leB_trans h ?_
    refine leB_congr_left (BPair.oneValue_symm Ef10) ?_
    have h' := leB_congr_left (BPair.mul_ofNat_one _)
      (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 32) hkappa) hs) hs) hsd) hsd2) hmu) hD0) h1L2)
    repeat rw [← BPair.mul_assoc] at h'
    exact leB_trans h' (leB_congr_left ((BPair.oneValue_symm Ef11)) (leB_refl _))
  have T35a : BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2 + (BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2).swap ≤ BPair.ofNat 32 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D :=
    leB_trans (leB_add Ta3 TaN) (leB_congr_left Ef8 T20)
  have T35b : (BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2).swap + BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2 ≤ BPair.ofNat 32 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D :=
    leB_trans (leB_add Tb3 TbN) (leB_congr_left Ef8 T20)
  -- the profile parts at the near scale and the moments' join
  have TQA : BPair.ofNat 2 * s * sd2 * mu1 * n * nuAQY ≤ BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1 + BPair.ofNat 2 * s * sd2 * n * mu1 * muQ2 := by
    refine leB_congr (polEqB [s, sd2, mu1, n, nuAQY]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel))
      (BPair.oneValue_refl _) (?_ : (s * sd2 * mu1 * n * BPair.ofNat 2 * nuAQY) ≤ BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1 + BPair.ofNat 2 * s * sd2 * n * mu1 * muQ2)
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul hs hsd2) hmu) hn) hAQY
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    refine leB_trans h (leB_add ?_ ?_)
    · refine leB_congr (polEqB [kappa, W0, W2, sd2, mu1, n, nuQD, s]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 6))) (by decide +kernel))
        (BPair.oneValue_refl _) (?_ : (BPair.ofNat 2 * kappa * W0 * W0 * W2 * sd2 * mu1 * n * nuQD * s) ≤ BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1)
      have h1 := leB_mulL hs (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hkappa) hW0u) hW0u) hW2) hsd2) hmu) hn) hnuQD)
      repeat rw [← BPair.mul_assoc] at h1
      refine leB_trans h1 ?_
      have h2 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hkappa) hW0u) hW0u) hW2) hsd2) hmu) hn) (unitLeOfNat 2)) hmQD
      repeat rw [← BPair.mul_assoc] at h2
      exact leB_trans h2 (leB_congr_left (BPair.oneValue_symm Ed4) (leB_refl _))
    · refine leB_congr (polEqB [s, sd2, n, mu1, nuQ2]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel))
        (BPair.oneValue_refl _) (?_ : (s * sd2 * n * mu1 * nuQ2) ≤ BPair.ofNat 2 * s * sd2 * n * mu1 * muQ2)
      have h1 := leB_mulR (unitLeMul (unitLeMul (unitLeMul hs hsd2) hn) hmu) hnuQ2
      repeat rw [← BPair.mul_assoc] at h1
      exact leB_trans h1 (leB_congr_left (BPair.oneValue_symm Ed8) (leB_refl _))
  have TQB : BPair.ofNat 2 * s * sd2 * muQ * n * nuAY ≤ BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1 + BPair.ofNat 2 * s * sd2 * n * muQ * muQ := by
    refine leB_congr (polEqB [s, sd2, muQ, n, nuAY]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel))
      (BPair.oneValue_refl _) (?_ : (s * sd2 * muQ * n * BPair.ofNat 2 * nuAY) ≤ BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1 + BPair.ofNat 2 * s * sd2 * n * muQ * muQ)
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul hs hsd2) hmuQ) hn) hAY
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    refine leB_trans h (leB_add ?_ ?_)
    · refine leB_congr (polEqB [kappa, W0, W2, sd2, muQ, n, nuD, s]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 6))) (by decide +kernel))
        (BPair.oneValue_refl _) (?_ : (BPair.ofNat 2 * kappa * W0 * W0 * W2 * sd2 * muQ * n * nuD * s) ≤ BPair.ofNat 8 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1)
      have h1 := leB_mulL hs (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hkappa) hW0u) hW0u) hW2) hsd2) hmuQ) hn) hnuD)
      repeat rw [← BPair.mul_assoc] at h1
      refine leB_trans h1 ?_
      have h2 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hkappa) hW0u) hW0u) hW2) hsd2) hmuQ) hn) (unitLeOfNat 2)) hmD
      repeat rw [← BPair.mul_assoc] at h2
      exact leB_trans h2 (leB_congr_left (BPair.oneValue_symm Ed6) (leB_refl _))
    · refine leB_congr (polEqB [s, sd2, n, muQ, nuQ]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel))
        (BPair.oneValue_refl _) (?_ : (s * sd2 * n * muQ * nuQ) ≤ BPair.ofNat 2 * s * sd2 * n * muQ * muQ)
      have h1 := leB_mulR (unitLeMul (unitLeMul (unitLeMul hs hsd2) hn) hmuQ) hnuQ
      repeat rw [← BPair.mul_assoc] at h1
      exact leB_trans h1 (leB_congr_left (BPair.oneValue_symm Ed10) (leB_refl _))
  have TQ : BPair.ofNat 2 * s * sd2 * mu1 * n * nuAQY + BPair.ofNat 2 * s * sd2 * muQ * n * nuAY ≤ BPair.ofNat 16 * kappa * W0 * W0 * W2 * K * n * n * sd2 * muQ * mu1 + BPair.ofNat 2 * s * sd2 * n * E2 * mu1 * D := by
    refine leB_trans (leB_add TQA TQB) ?_
    rw [BPair.add_add_comm]
    refine leB_add (leB_congr_left Ed11 (leB_refl _)) ?_
    have hj := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hs) hsd2) hn) hjoin
    rw [BPair.left_distrib] at hj
    repeat rw [← BPair.mul_assoc] at hj
    exact hj
  have TQ' : BPair.ofNat 80 * kappa * s * sd * sd2 * mu1 * n * nuAQY + BPair.ofNat 80 * kappa * s * sd * sd2 * muQ * n * nuAY ≤ BPair.ofNat 512 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D + BPair.ofNat 80 * kappa * E2 * n * s * sd * sd2 * mu1 * D := by
    refine leB_congr_left (BPair.add_congr (BPair.oneValue_symm Ef13) (BPair.oneValue_symm Ef14)) ?_
    refine leB_congr_left (BPair.oneValue_of_eq (show BPair.ofNat 40 * kappa * sd * (BPair.ofNat 2 * s * sd2 * mu1 * n * nuAQY)
      + BPair.ofNat 40 * kappa * sd * (BPair.ofNat 2 * s * sd2 * muQ * n * nuAY) = BPair.ofNat 40 * kappa * sd * BPair.ofNat 2 * s * sd2 * mu1 * n * nuAQY
      + BPair.ofNat 40 * kappa * sd * BPair.ofNat 2 * s * sd2 * muQ * n * nuAY by repeat rw [← BPair.mul_assoc])) ?_
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeOfNat 40) hkappa) hsd) TQ
    rw [BPair.left_distrib, BPair.left_distrib] at h
    refine leB_trans h ?_
    repeat rw [← BPair.mul_assoc]
    refine leB_add ?_ (leB_congr_left (BPair.oneValue_symm Ef17) (leB_refl _))
    refine leB_congr_left (BPair.oneValue_symm Ef15) ?_
    have h2 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 128) hkappa) hW0u) hW0u) hK) hn) hsd) hsd2) hmu) hvs
    repeat rw [← BPair.mul_assoc] at h2
    exact leB_trans h2 (leB_congr_left (BPair.oneValue_symm Ef16) (leB_refl _))
  -- the coefficients' order at the target's monomials
  have h512 : BPair.ofNat 512 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D ≤ BPair.ofNat 520 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D := by
    refine leB_congr ((BPair.oneValue_of_eq (show BPair.ofNat 512 * (kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D) = BPair.ofNat 512 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D by repeat rw [← BPair.mul_assoc])))
      ((BPair.oneValue_of_eq (show BPair.ofNat 520 * (kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D) = BPair.ofNat 520 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D by repeat rw [← BPair.mul_assoc]))) ?_
    exact leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul hkappa hW0u) hW0u) hL2) hK) hn) hs) hsd) hsd2) hmu) hD0) (leB_ofNat (by decide : 512 ≤ 520))
  have h32 : BPair.ofNat 32 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D ≤ BPair.ofNat 160 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D := by
    refine leB_congr ((BPair.oneValue_of_eq (show BPair.ofNat 32 * (kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D) = BPair.ofNat 32 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D by repeat rw [← BPair.mul_assoc])))
      ((BPair.oneValue_of_eq (show BPair.ofNat 160 * (kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D) = BPair.ofNat 160 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D by repeat rw [← BPair.mul_assoc]))) ?_
    exact leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul hkappa hW0u) hW0u) hL2) hs) hs) hsd) hsd2) hmu) hD0) (leB_ofNat (by decide : 32 ≤ 160))
  -- the two sides assembled at the clearing
  have Sa : BPair.ofNat 80 * kappa * s * sd * BPair.ofNat 2 * s * sd2 * mu1 * mQY + (BPair.ofNat 80 * kappa * s * sd * BPair.ofNat 2 * s * sd2 * muQ * mY).swap ≤ BPair.ofNat 160 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D + BPair.ofNat 520 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D + BPair.ofNat 80 * kappa * E2 * n * s * sd * sd2 * mu1 * D := by
    have h := leB_mulR hc80 hRa
    rw [BPair.left_distrib] at h
    repeat rw [BPair.left_distrib] at h
    repeat rw [BPair.mul_swap] at h
    repeat rw [← BPair.mul_assoc] at h
    rw [BPair.add_assoc (BPair.ofNat 80 * kappa * s * sd * mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ + BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2 + (BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2).swap) (BPair.ofNat 80 * kappa * s * sd * sd2 * mu1 * n * nuAQY) (BPair.ofNat 80 * kappa * s * sd * sd2 * muQ * n * nuAY),
      BPair.add_assoc (BPair.ofNat 80 * kappa * s * sd * mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ) (BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2) ((BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2).swap)] at h
    refine leB_trans h ?_
    refine leB_trans (leB_add (leB_add Ta2 T35a) TQ') ?_
    refine leB_congr_left (BPair.add_congr Ef12 (BPair.oneValue_refl _)) ?_
    rw [← BPair.add_assoc]
    exact leB_add (leB_add (leB_refl _) h512) (leB_refl _)
  have Sb : BPair.ofNat 80 * kappa * s * sd * BPair.ofNat 2 * s * sd2 * muQ * mY + (BPair.ofNat 80 * kappa * s * sd * BPair.ofNat 2 * s * sd2 * mu1 * mQY).swap ≤ BPair.ofNat 160 * kappa * W0 * W0 * L2 * s * s * sd * sd2 * mu1 * D + BPair.ofNat 520 * kappa * W0 * W0 * L2 * K * n * s * sd * sd2 * mu1 * D + BPair.ofNat 80 * kappa * E2 * n * s * sd * sd2 * mu1 * D := by
    have h := leB_mulR hc80 hRb
    rw [BPair.left_distrib] at h
    repeat rw [BPair.left_distrib] at h
    repeat rw [BPair.mul_swap] at h
    repeat rw [← BPair.mul_assoc] at h
    rw [BPair.add_assoc ((BPair.ofNat 80 * kappa * s * sd * mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap + (BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2).swap + BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2) (BPair.ofNat 80 * kappa * s * sd * sd2 * mu1 * n * nuAQY) (BPair.ofNat 80 * kappa * s * sd * sd2 * muQ * n * nuAY),
      BPair.add_assoc ((BPair.ofNat 80 * kappa * s * sd * mu1 * n * kappa * BPair.ofNat 2 * sn2 * muQ).swap) ((BPair.ofNat 80 * kappa * s * sd * mu1 * n * r2 * sd2).swap) (BPair.ofNat 80 * kappa * s * sd * muQ * n * r1 * sd2)] at h
    refine leB_trans h ?_
    refine leB_trans (leB_add (leB_add Tb2 T35b) TQ') ?_
    refine leB_congr_left (BPair.add_congr (BPair.oneValue_symm (BPair.unit_add _))
      (BPair.oneValue_refl _)) ?_
    rw [← BPair.add_assoc]
    exact leB_add (leB_add h32 h512) (leB_refl _)
  -- the fold's two members at the target
  have Cb : BPair.ofNat 40 * s * sd * sd2 * (BPair.ofNat 4 * kappa * s * muQ * mY + (BPair.ofNat 4 * kappa * s * mu1 * mQY).swap) ≤ BPair.ofNat 40 * s * sd * sd2 * (mu1 * (D * (BPair.ofNat 4 * kappa * (W0 * W0) * L2 * s + BPair.ofNat 13 * kappa * (W0 * W0) * L2 * K * n + BPair.ofNat 2 * kappa * E2 * n))) := by
    rw [BPair.left_distrib, BPair.mul_swap]
    repeat first | rw [BPair.left_distrib] | rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
    exact leB_congr (BPair.add_congr (BPair.oneValue_symm Eg5) (swap_congr (BPair.oneValue_symm Eg4)))
      (BPair.add_congr (BPair.add_congr (BPair.oneValue_symm Eg1) (BPair.oneValue_symm Eg2))
        (BPair.oneValue_symm Eg3)) Sb
  have Ca : BPair.ofNat 40 * s * sd * sd2 * (BPair.ofNat 4 * kappa * s * mu1 * mQY + (BPair.ofNat 4 * kappa * s * muQ * mY).swap) ≤ BPair.ofNat 40 * s * sd * sd2 * (mu1 * (D * (BPair.ofNat 4 * kappa * (W0 * W0) * L2 * s + BPair.ofNat 13 * kappa * (W0 * W0) * L2 * K * n + BPair.ofNat 2 * kappa * E2 * n))) := by
    rw [BPair.left_distrib, BPair.mul_swap]
    repeat first | rw [BPair.left_distrib] | rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
    exact leB_congr (BPair.add_congr (BPair.oneValue_symm Eg4) (swap_congr (BPair.oneValue_symm Eg5)))
      (BPair.add_congr (BPair.add_congr (BPair.oneValue_symm Eg1) (BPair.oneValue_symm Eg2))
        (BPair.oneValue_symm Eg3)) Sa
  have hUb : (s * mu1 * T3l).oneValue (BPair.ofNat 4 * kappa * s * muQ * mY + (BPair.ofNat 4 * kappa * s * mu1 * mQY).swap) := by
    refine BPair.oneValue_trans (polEqB [s, mu1, T3l]
      (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
      (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 2) (Mon.var 1)))) (by decide +kernel)) ?_
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hF) ?_
    rw [BPair.left_distrib, BPair.left_distrib, BPair.mul_swap, BPair.mul_swap]
    exact BPair.add_congr (polEqB [s, kappa, muQ, mY]
      (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 3)))))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3))) (by decide +kernel))
      (swap_congr (polEqB [s, kappa, mu1, mQY]
        (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 3)))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3))) (by decide +kernel)))
  have hUa : (s * mu1 * T3l.swap).oneValue (BPair.ofNat 4 * kappa * s * mu1 * mQY + (BPair.ofNat 4 * kappa * s * muQ * mY).swap) := by
    rw [BPair.mul_swap]
    refine BPair.oneValue_trans (swap_congr hUb) ?_
    rw [← BPair.swap_add, BPair.swap_swap]
    exact BPair.oneValue_of_eq (BPair.add_comm _ _)
  refine leB_unscale hmu1 ?_
  refine leB_congr (BPair.oneValue_of_eq (BPair.mul_right_comm s mu1 (windowsep.mag T3l)))
    (BPair.oneValue_of_eq (BPair.mul_comm mu1 (D * (BPair.ofNat 4 * kappa * (W0 * W0) * L2 * s + BPair.ofNat 13 * kappa * (W0 * W0) * L2 * K * n + BPair.ofNat 2 * kappa * E2 * n)))) ?_
  refine windowsep.mag_mul_le ?_ ?_
  · refine leB_unscale_left hc40 ?_
    exact leB_congr_left (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hUb)) Cb
  · refine leB_unscale_left hc40 ?_
    exact leB_congr_left (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hUa)) Ca

/-- The deficits' fold at the mode weight,
`μ[ZD] ≤ (C_Z η + P' η²) ⟨v, v⟩` at `C_Z := 2 dim G W₀ #p + 8 W₀² (L + 2)`
and the stated pair `P'`, cleared at the scale pair `[n : s]`, the near
scale `K` and the stated pairs' clearing `c₀` (`2 d_θ` at the member):
the coordinate identity at the mode weight summed over the plaquettes
reads `2 ν[Z ⟨y_Π e_p, y_Π e_p⟩]` joined to the derivative's remainder,
the deviation, the generator's read's gap and the fold's leading member
against `κ dim G Σ_p (𝖲 + ε)⁻¹_{pp} ⟨v, v⟩` at the diagonal's cap `W₀`;
the derivative's remainder within `#p C₁ ϱ₁ μ[ZD]`, the deviation and
the generator's gap each a quarter of the leading read joined to their
near-scale members, the leading member at the fold's cap
(`weight_lead`), the two quarters withdrawn; the deficit's second-order
read at the fluxes' range parts against the off-range fold,
`κ c₀ μ[ZD] ≤ c₀ Σ_p μ[Z|f_p|²] [1 : 2κ] + (c₀ c_off [1 : 2κ] + c'_q)
μ[ZD²]`, and the self-read withdraws at the factor two at the deficit
cell's first comparison. -/
theorem weight_deficit (mZD mZD2 nuZD2 mZY nuZY T2 T3g T3l T4 Sd D K n s kappa dG W0 L C1 rho1
      rho2 TR coff cqp c0 P mQD muQ W2 Winf2 : BPair)
    (hsum : (BPair.ofNat 2 * nuZY * s + n * (T2 + T3g + T3l + T4)).oneValue
      (n * kappa * dG * Sd * D))
    (hSd : Sd ≤ P * W0)
    (hT2 : windowsep.mag T2 ≤ P * C1 * rho1 * mZD)
    (hT3g : BPair.ofNat 2 * n * s * windowsep.mag T3g
      ≤ s * s * nuZY + BPair.ofNat 16 * P * (C1 * C1) * rho2 * Winf2 * (n * n) * mQD)
    (hT4 : BPair.ofNat 2 * n * s * windowsep.mag T4
      ≤ s * s * nuZY + BPair.ofNat 4 * P * (C1 * C1) * (TR * TR) * (s * s) * nuZD2)
    (hlead : s * windowsep.mag T3l
      ≤ D * (BPair.ofNat 4 * kappa * (W0 * W0) * (L + BPair.ofNat 2) * s
        + BPair.ofNat 13 * kappa * (W0 * W0) * (L + BPair.ofNat 2) * K * n
        + BPair.ofNat 2 * kappa * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * n))
    (hZD : kappa * (kappa * kappa * c0) * mZD
      ≤ kappa * kappa * c0 * mZY + kappa * kappa * c0 * coff * mZD2 + kappa * cqp * mZD2)
    (hmn : mZY ≤ nuZY)
    (hZD2 : mZD2 * (s * s)
      ≤ BPair.ofNat 4 * (K * K) * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * (n * n) * D)
    (hnuZD2 : nuZD2 ≤ BPair.ofNat 2 * mZD2)
    (hmQD : mQD * s ≤ BPair.ofNat 2 * K * n * muQ)
    (hvs : BPair.ofNat 5 * n * kappa * W2 * muQ ≤ BPair.ofNat 4 * s * (L + BPair.ofNat 2) * D)
    (hWinf : Winf2 ≤ W2)
    (hD1 : BPair.ofNat 2 * P * n * C1 * rho1 ≤ kappa * s)
    (hkappa0 : BPair.unit < kappa) (hs0 : BPair.unit < s)
    (hn : BPair.unit ≤ n) (hD : BPair.unit ≤ D) (hK : BPair.unit ≤ K) (hdG : BPair.unit ≤ dG)
    (hL : BPair.unit ≤ L) (hC1 : BPair.unit ≤ C1)
    (hrho2 : BPair.unit ≤ rho2) (hTR : BPair.unit ≤ TR)
    (hcoff : BPair.unit ≤ coff) (hcqp : BPair.unit ≤ cqp) (hc0 : BPair.unit ≤ c0)
    (hP : BPair.unit ≤ P) (hmQD0 : BPair.unit ≤ mQD) (hW2 : BPair.unit ≤ W2)
    (hmZD0 : BPair.unit ≤ mZD) :
    mZD * (s * s) * (kappa * kappa * c0)
      ≤ ((BPair.ofNat 2 * dG * W0 * P + BPair.ofNat 8 * (W0 * W0) * (L + BPair.ofNat 2)) * n * s
            * (kappa * kappa * c0)
          + (BPair.ofNat 4 * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * (kappa * kappa) * c0
            + (BPair.ofNat 26 * P * (C1 * C1) * rho2 * (L + BPair.ofNat 2) * c0
              + BPair.ofNat 26 * (kappa * kappa) * (W0 * W0) * (L + BPair.ofNat 2) * c0) * K
            + (BPair.ofNat 32 * kappa * P * (C1 * C1) * (TR * TR)
                  * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * c0
                + (BPair.ofNat 8 * kappa * c0 * coff + BPair.ofNat 8 * cqp)
                  * (BPair.ofNat 1 + BPair.ofNat 2 * dG)) * (K * K)) * (n * n)) * D := by
  have hkappa : BPair.unit ≤ kappa := leB_of_lt hkappa0
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hL2 : BPair.unit ≤ L + BPair.ofNat 2 := unitLeAdd hL (unitLeOfNat 2)
  have hE2 : BPair.unit ≤ BPair.ofNat 1 + BPair.ofNat 2 * dG :=
    unitLeAdd (unitLeOfNat 1) (unitLeMul (unitLeOfNat 2) hdG)
  generalize hLdef : L + BPair.ofNat 2 = L2 at hlead hvs hL2 ⊢
  generalize hEdef : BPair.ofNat 1 + BPair.ofNat 2 * dG = E2 at hlead hZD2 hE2 ⊢
  have h2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  have Ea1 : (BPair.ofNat 2 * s * kappa * n * kappa * dG * P * W0 * D).oneValue
      (BPair.ofNat 2 * kappa * kappa * dG * P * W0 * n * s * D) :=
    polEqB [s, kappa, n, dG, P, W0, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 0)) (Mon.var 6))) (by decide +kernel)
  have Ea2 : (BPair.ofNat 2 * s * kappa * n * P * C1 * rho1 * mZD).oneValue
      (BPair.ofNat 2 * kappa * n * s * P * C1 * rho1 * mZD) :=
    polEqB [s, kappa, n, P, C1, rho1, mZD]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ea3 : (BPair.ofNat 2 * s * kappa * n * windowsep.mag T3g).oneValue
      (kappa * BPair.ofNat 2 * n * s * windowsep.mag T3g) :=
    polEqB [s, kappa, n, (windowsep.mag T3g)]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 2)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3))) (by decide +kernel)
  have Ea4 : (BPair.ofNat 2 * s * kappa * n * windowsep.mag T4).oneValue
      (kappa * BPair.ofNat 2 * n * s * windowsep.mag T4) :=
    polEqB [s, kappa, n, (windowsep.mag T4)]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 2)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3))) (by decide +kernel)
  have Ea5 : (BPair.ofNat 2 * s * kappa * n * windowsep.mag T3l).oneValue
      (BPair.ofNat 2 * kappa * n * s * windowsep.mag T3l) :=
    polEqB [s, kappa, n, (windowsep.mag T3l)]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 3))) (by decide +kernel)
  have Eb1 : (kappa * BPair.ofNat 16 * P * C1 * C1 * rho2 * Winf2 * n * n * mQD).oneValue
      (BPair.ofNat 16 * kappa * P * C1 * C1 * rho2 * Winf2 * n * n * mQD) :=
    polEqB [kappa, P, C1, rho2, Winf2, n, mQD]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 16)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Eb2 : (BPair.ofNat 5 * s * BPair.ofNat 16 * kappa * P * C1 * C1 * rho2 * Winf2 * n * n * mQD).oneValue
      (BPair.ofNat 16 * P * C1 * C1 * rho2 * n * n * BPair.ofNat 5 * kappa * Winf2 * mQD * s) :=
    polEqB [s, kappa, P, C1, rho2, Winf2, n, mQD]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.cst 16)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6)) (Mon.var 6)) (Mon.cst 5)) (Mon.var 1)) (Mon.var 5)) (Mon.var 7)) (Mon.var 0))) (by decide +kernel)
  have Eb3 : (BPair.ofNat 16 * P * C1 * C1 * rho2 * n * n * BPair.ofNat 5 * kappa * W2 * BPair.ofNat 2 * K * n * muQ).oneValue
      (BPair.ofNat 32 * P * C1 * C1 * rho2 * K * n * n * BPair.ofNat 5 * n * kappa * W2 * muQ) :=
    polEqB [P, C1, rho2, n, kappa, W2, K, muQ]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.cst 5)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 2)) (Mon.var 6)) (Mon.var 3)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 6)) (Mon.var 3)) (Mon.var 3)) (Mon.cst 5)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 7))) (by decide +kernel)
  have Eb4 : (BPair.ofNat 32 * P * C1 * C1 * rho2 * K * n * n * BPair.ofNat 4 * s * L2 * D).oneValue
      (BPair.ofNat 128 * P * C1 * C1 * rho2 * L2 * K * n * n * D * s) :=
    polEqB [P, C1, rho2, K, n, s, L2, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.cst 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 128) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 6)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)) (Mon.var 5))) (by decide +kernel)
  have Eb5 : (BPair.ofNat 5 * s * BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * K * n * n * D).oneValue
      (BPair.ofNat 130 * P * C1 * C1 * rho2 * L2 * K * n * n * D * s) :=
    polEqB [s, P, C1, rho2, L2, K, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 5) (Mon.var 0)) (Mon.cst 26)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 130) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 0))) (by decide +kernel)
  have Ec1 : (kappa * BPair.ofNat 4 * P * C1 * C1 * TR * TR * s * s * nuZD2).oneValue
      (BPair.ofNat 4 * kappa * P * C1 * C1 * TR * TR * nuZD2 * s * s) :=
    polEqB [kappa, P, C1, TR, s, nuZD2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 4)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 5)) (Mon.var 4)) (Mon.var 4))) (by decide +kernel)
  have Ec2 : (BPair.ofNat 4 * kappa * P * C1 * C1 * TR * TR * BPair.ofNat 2 * mZD2 * s * s).oneValue
      (BPair.ofNat 8 * kappa * P * C1 * C1 * TR * TR * mZD2 * s * s) :=
    polEqB [kappa, P, C1, TR, mZD2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5))) (by decide +kernel)
  have Ec3 : (BPair.ofNat 8 * kappa * P * C1 * C1 * TR * TR * BPair.ofNat 4 * K * K * E2 * n * n * D).oneValue
      (BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * K * K * E2 * n * n * D) :=
    polEqB [kappa, P, C1, TR, K, E2, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.cst 4)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7))) (by decide +kernel)
  have Ed1 : (BPair.ofNat 2 * kappa * n * D * BPair.ofNat 4 * kappa * W0 * W0 * L2 * s).oneValue
      (BPair.ofNat 8 * kappa * kappa * W0 * W0 * L2 * n * s * D) :=
    polEqB [kappa, n, D, W0, L2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 4)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 1)) (Mon.var 5)) (Mon.var 2))) (by decide +kernel)
  have Ed2 : (BPair.ofNat 2 * kappa * n * D * BPair.ofNat 13 * kappa * W0 * W0 * L2 * K * n).oneValue
      (BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * K * n * n * D) :=
    polEqB [kappa, n, D, W0, L2, K]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 13)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 1)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 26) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Ed3 : (BPair.ofNat 2 * kappa * n * D * BPair.ofNat 2 * kappa * E2 * n).oneValue
      (BPair.ofNat 4 * kappa * kappa * E2 * n * n * D) :=
    polEqB [kappa, n, D, E2]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 1)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have Ee1 : (BPair.ofNat 2 * s * kappa * BPair.ofNat 2 * nuZY * s).oneValue
      (BPair.ofNat 4 * kappa * s * s * nuZY) :=
    polEqB [s, kappa, nuZY]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 0)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2))) (by decide +kernel)
  have Ee2 : (BPair.ofNat 4 * kappa * s * s * nuZY).oneValue
      (BPair.ofNat 2 * kappa * s * s * nuZY + BPair.ofNat 2 * kappa * s * s * nuZY) :=
    polEqB [kappa, s, nuZY]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)))) (by decide +kernel)
  have Ef1 : (kappa * kappa * kappa * c0 * mZD * BPair.ofNat 2 * s * s).oneValue
      (BPair.ofNat 2 * kappa * kappa * kappa * c0 * s * s * mZD) :=
    polEqB [kappa, c0, mZD, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Ef2 : (kappa * kappa * c0 * nuZY * BPair.ofNat 2 * s * s).oneValue
      (kappa * c0 * BPair.ofNat 2 * kappa * s * s * nuZY) :=
    polEqB [kappa, c0, nuZY, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Ef3 : (kappa * kappa * c0 * coff * mZD2 * BPair.ofNat 2 * s * s).oneValue
      (BPair.ofNat 2 * kappa * kappa * c0 * coff * mZD2 * s * s) :=
    polEqB [kappa, c0, coff, mZD2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4))) (by decide +kernel)
  have Ef4 : (kappa * cqp * mZD2 * BPair.ofNat 2 * s * s).oneValue
      (BPair.ofNat 2 * kappa * cqp * mZD2 * s * s) :=
    polEqB [kappa, cqp, mZD2, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have Ef5 : (BPair.ofNat 2 * kappa * kappa * c0 * coff * BPair.ofNat 4 * K * K * E2 * n * n * D).oneValue
      (BPair.ofNat 8 * kappa * kappa * c0 * coff * K * K * E2 * n * n * D) :=
    polEqB [kappa, c0, coff, K, E2, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.cst 4)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Ef6 : (BPair.ofNat 2 * kappa * cqp * BPair.ofNat 4 * K * K * E2 * n * n * D).oneValue
      (BPair.ofNat 8 * kappa * cqp * K * K * E2 * n * n * D) :=
    polEqB [kappa, cqp, K, E2, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.cst 4)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  have Eg1 : (kappa * c0 * BPair.ofNat 2 * kappa * n * s * P * C1 * rho1 * mZD).oneValue
      (kappa * kappa * c0 * mZD * s * BPair.ofNat 2 * P * n * C1 * rho1) :=
    polEqB [kappa, c0, n, s, P, C1, rho1, mZD]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 7)) (Mon.var 3)) (Mon.cst 2)) (Mon.var 4)) (Mon.var 2)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Eg2 : (kappa * kappa * c0 * mZD * s * kappa * s).oneValue
      (kappa * kappa * kappa * c0 * s * s * mZD) :=
    polEqB [kappa, c0, mZD, s]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 3)) (Mon.var 2))) (by decide +kernel)
  have Eh1 : (kappa * c0 * BPair.ofNat 2 * kappa * kappa * dG * P * W0 * n * s * D).oneValue
      (kappa * BPair.ofNat 2 * dG * W0 * P * n * s * kappa * kappa * c0 * D) :=
    polEqB [kappa, c0, dG, P, W0, n, s, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 2)) (Mon.var 4)) (Mon.var 3)) (Mon.var 5)) (Mon.var 6)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 7))) (by decide +kernel)
  have Eh2 : (kappa * c0 * BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * K * n * n * D).oneValue
      (kappa * BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * c0 * K * n * n * D) :=
    polEqB [kappa, c0, P, C1, rho2, L2, K, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 26)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 26)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 1)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8))) (by decide +kernel)
  have Eh3 : (kappa * c0 * BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * K * K * E2 * n * n * D).oneValue
      (kappa * BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * E2 * c0 * K * K * n * n * D) :=
    polEqB [kappa, c0, P, C1, TR, K, E2, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 32)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 32)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)) (Mon.var 1)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8))) (by decide +kernel)
  have Eh4 : (kappa * c0 * BPair.ofNat 8 * kappa * kappa * W0 * W0 * L2 * n * s * D).oneValue
      (kappa * BPair.ofNat 8 * W0 * W0 * L2 * n * s * kappa * kappa * c0 * D) :=
    polEqB [kappa, c0, W0, L2, n, s, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 8)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 6))) (by decide +kernel)
  have Eh5 : (kappa * c0 * BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * K * n * n * D).oneValue
      (kappa * BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * c0 * K * n * n * D) :=
    polEqB [kappa, c0, W0, L2, K, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 26)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 26)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Eh6 : (kappa * c0 * BPair.ofNat 4 * kappa * kappa * E2 * n * n * D).oneValue
      (kappa * BPair.ofNat 4 * E2 * kappa * kappa * c0 * n * n * D) :=
    polEqB [kappa, c0, E2, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 4)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 4)) (Mon.var 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4))) (by decide +kernel)
  have Eh7 : (BPair.ofNat 8 * kappa * kappa * c0 * coff * K * K * E2 * n * n * D).oneValue
      (kappa * BPair.ofNat 8 * kappa * c0 * coff * E2 * K * K * n * n * D) :=
    polEqB [kappa, c0, coff, K, E2, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 4)) (Mon.var 3)) (Mon.var 3)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
  have Eh8 : (BPair.ofNat 8 * kappa * cqp * K * K * E2 * n * n * D).oneValue
      (kappa * BPair.ofNat 8 * cqp * E2 * K * K * n * n * D) :=
    polEqB [kappa, cqp, K, E2, n, D]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  have Eh9 : (kappa * kappa * kappa * c0 * s * s * mZD).oneValue
      (kappa * mZD * s * s * kappa * kappa * c0) :=
    polEqB [kappa, c0, s, mZD]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 3)) (Mon.var 2)) (Mon.var 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1))) (by decide +kernel)
  have Ep2 : (kappa * BPair.ofNat 2 * dG * W0 * P * n * s * kappa * kappa * c0 * D + kappa * BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * c0 * K * n * n * D + kappa * BPair.ofNat 8 * W0 * W0 * L2 * n * s * kappa * kappa * c0 * D + kappa * BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * c0 * K * n * n * D + kappa * BPair.ofNat 4 * E2 * kappa * kappa * c0 * n * n * D + kappa * BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * E2 * c0 * K * K * n * n * D + kappa * BPair.ofNat 8 * kappa * c0 * coff * E2 * K * K * n * n * D + kappa * BPair.ofNat 8 * cqp * E2 * K * K * n * n * D).oneValue
      (kappa * BPair.ofNat 2 * dG * W0 * P * n * s * kappa * kappa * c0 * D + kappa * BPair.ofNat 8 * W0 * W0 * L2 * n * s * kappa * kappa * c0 * D + kappa * BPair.ofNat 4 * E2 * kappa * kappa * c0 * n * n * D + kappa * BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * c0 * K * n * n * D + kappa * BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * c0 * K * n * n * D + kappa * BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * E2 * c0 * K * K * n * n * D + kappa * BPair.ofNat 8 * kappa * c0 * coff * E2 * K * K * n * n * D + kappa * BPair.ofNat 8 * cqp * E2 * K * K * n * n * D) :=
    polEqB [kappa, dG, W0, P, n, s, c0, D, C1, rho2, L2, K, E2, TR, coff, cqp]
      (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 26)) (Mon.var 3)) (Mon.var 8)) (Mon.var 8)) (Mon.var 9)) (Mon.var 10)) (Mon.var 6)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 2)) (Mon.var 2)) (Mon.var 10)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 26)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 10)) (Mon.var 6)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 4)) (Mon.var 12)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 32)) (Mon.var 0)) (Mon.var 3)) (Mon.var 8)) (Mon.var 8)) (Mon.var 13)) (Mon.var 13)) (Mon.var 12)) (Mon.var 6)) (Mon.var 11)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 0)) (Mon.var 6)) (Mon.var 14)) (Mon.var 12)) (Mon.var 11)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 15)) (Mon.var 12)) (Mon.var 11)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7))))
      (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 2)) (Mon.var 2)) (Mon.var 10)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 4)) (Mon.var 12)) (Mon.var 0)) (Mon.var 0)) (Mon.var 6)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 26)) (Mon.var 3)) (Mon.var 8)) (Mon.var 8)) (Mon.var 9)) (Mon.var 10)) (Mon.var 6)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 26)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 10)) (Mon.var 6)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 32)) (Mon.var 0)) (Mon.var 3)) (Mon.var 8)) (Mon.var 8)) (Mon.var 13)) (Mon.var 13)) (Mon.var 12)) (Mon.var 6)) (Mon.var 11)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 0)) (Mon.var 6)) (Mon.var 14)) (Mon.var 12)) (Mon.var 11)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8)) (Mon.var 15)) (Mon.var 12)) (Mon.var 11)) (Mon.var 11)) (Mon.var 4)) (Mon.var 4)) (Mon.var 7)))) (by decide +kernel)
  -- the summed identity read at the members' magnitudes
  have S1 : BPair.ofNat 2 * nuZY * s
      ≤ n * kappa * dG * Sd * D
        + n * (windowsep.mag T2 + windowsep.mag T3g + windowsep.mag T3l + windowsep.mag T4) := by
    have h0 : BPair.ofNat 2 * nuZY * s + n * (T2 + T3g + T3l + T4) ≤ n * kappa * dG * Sd * D :=
      leB_congr_right hsum (leB_refl _)
    have h1 := leB_swapL (Y := (n * (T2 + T3g + T3l + T4)).swap) h0
    refine leB_trans h1 (leB_add (leB_refl _) ?_)
    rw [← BPair.mul_swap, ← BPair.swap_add, ← BPair.swap_add, ← BPair.swap_add]
    exact leB_mulR hn (leB_add (leB_add (leB_add (windowsep.swap_le_mag T2)
      (windowsep.swap_le_mag T3g)) (windowsep.swap_le_mag T3l)) (windowsep.swap_le_mag T4))
  -- the read at the clearing twice the scale's multiple of the index
  have S2 := leB_mulR (unitLeMul (unitLeMul h2 hs) hkappa) S1
  repeat first | rw [BPair.left_distrib] at S2 | rw [BPair.right_distrib] at S2
  repeat rw [← BPair.mul_assoc] at S2
  repeat rw [← BPair.add_assoc] at S2
  -- the leading member at the diagonal's cap
  have tSd : BPair.ofNat 2 * s * kappa * n * kappa * dG * Sd * D
      ≤ BPair.ofNat 2 * kappa * kappa * dG * P * W0 * n * s * D := by
    have h := leB_mulL hD (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul h2 hs) hkappa) hn) hkappa) hdG) hSd)
    repeat rw [← BPair.mul_assoc] at h
    exact leB_trans h (leB_congr_left (BPair.oneValue_symm Ea1) (leB_refl _))
  -- the derivative's remainder
  have t2 : BPair.ofNat 2 * s * kappa * n * windowsep.mag T2
      ≤ BPair.ofNat 2 * kappa * n * s * P * C1 * rho1 * mZD := by
    have h := leB_mulR (unitLeMul (unitLeMul (unitLeMul h2 hs) hkappa) hn) hT2
    repeat rw [← BPair.mul_assoc] at h
    exact leB_trans h (leB_congr_left ((BPair.oneValue_symm Ea2)) (leB_refl _))
  -- the gap member at the near scale and the variance's side
  have t3g : BPair.ofNat 2 * s * kappa * n * windowsep.mag T3g
      ≤ kappa * s * s * nuZY + BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * K * n * n * D := by
    have h := leB_mulR hkappa hT3g
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    refine leB_congr_left (BPair.oneValue_symm Ea3) (leB_trans h (leB_add (leB_refl _) ?_))
    refine leB_congr_left (BPair.oneValue_symm Eb1) ?_
    refine leB_unscale_left (unitLtMul (unitLtNat (by decide : 0 < 5)) hs0) ?_
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_symm Eb2) (BPair.oneValue_symm Eb5) ?_
    have hA := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeOfNat 16) hP) hC1) hC1) hrho2) hn) hn) (unitLeMul (unitLeOfNat 5) hkappa))
      (leB_mul_mono (unitLeMul hmQD0 hs) hW2 hWinf hmQD)
    have hB := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeOfNat 32) hP) hC1) hC1) hrho2) hK) hn) hn) hvs
    have hC := leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeMul (unitLeMul hP hC1) hC1) hrho2) hL2) hK) hn) hn) hD) hs)
      (leB_ofNat (by decide : 128 ≤ 130))
    repeat rw [← BPair.mul_assoc] at hA
    repeat rw [← BPair.mul_assoc] at hB
    repeat rw [← BPair.mul_assoc] at hC
    exact leB_trans hA (leB_trans (leB_congr_left (BPair.oneValue_symm Eb3) hB)
      (leB_trans (leB_congr_left (BPair.oneValue_symm Eb4) (leB_refl _)) hC))
  -- the deviation member at the mode weight's square moment
  have t4 : BPair.ofNat 2 * s * kappa * n * windowsep.mag T4
      ≤ kappa * s * s * nuZY
        + BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * K * K * E2 * n * n * D := by
    have h := leB_mulR hkappa hT4
    rw [BPair.left_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    refine leB_congr_left (BPair.oneValue_symm Ea4) (leB_trans h (leB_add (leB_refl _) ?_))
    refine leB_congr_left (BPair.oneValue_symm Ec1) ?_
    have h1 := leB_mulL (unitLeMul hs hs) (leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeMul (unitLeOfNat 4) hkappa) hP) hC1) hC1) hTR) hTR) hnuZD2)
    have h2 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeOfNat 8) hkappa) hP) hC1) hC1) hTR) hTR) hZD2
    repeat rw [← BPair.mul_assoc] at h1
    repeat rw [← BPair.mul_assoc] at h2
    exact leB_trans h1 (leB_trans (leB_congr_left (BPair.oneValue_symm Ec2) h2)
      (leB_congr_left (BPair.oneValue_symm Ec3) (leB_refl _)))
  -- the fold's cap at the clearing
  have t3l : BPair.ofNat 2 * s * kappa * n * windowsep.mag T3l
      ≤ BPair.ofNat 8 * kappa * kappa * W0 * W0 * L2 * n * s * D
        + BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * K * n * n * D
        + BPair.ofNat 4 * kappa * kappa * E2 * n * n * D := by
    have h := leB_mulR (unitLeMul (unitLeMul h2 hkappa) hn) hlead
    repeat first | rw [BPair.left_distrib] at h | rw [BPair.right_distrib] at h
    repeat rw [← BPair.mul_assoc] at h
    repeat rw [← BPair.add_assoc] at h
    refine leB_congr_left (BPair.oneValue_symm Ea5) (leB_trans h ?_)
    exact leB_add (leB_add (leB_congr_left (BPair.oneValue_symm Ed1) (leB_refl _))
      (leB_congr_left (BPair.oneValue_symm Ed2) (leB_refl _)))
      (leB_congr_left (BPair.oneValue_symm Ed3) (leB_refl _))
  -- the assembly, the two quarters withdrawn from the leading read
  have S2' := leB_trans S2 (leB_add (leB_add (leB_add (leB_add tSd t2) t3g) t3l) t4)
  repeat rw [← BPair.add_assoc] at S2'
  have S2' : BPair.ofNat 2 * s * kappa * BPair.ofNat 2 * nuZY * s ≤ ((kappa * s * s * nuZY + kappa * s * s * nuZY + (BPair.ofNat 2 * kappa * kappa * dG * P * W0 * n * s * D + BPair.ofNat 2 * kappa * n * s * P * C1 * rho1 * mZD + BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * K * n * n * D + BPair.ofNat 8 * kappa * kappa * W0 * W0 * L2 * n * s * D + BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * K * n * n * D + BPair.ofNat 4 * kappa * kappa * E2 * n * n * D + BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * K * K * E2 * n * n * D))) :=
    leB_congr (BPair.oneValue_refl _)
      (polEqB [kappa, dG, P, W0, n, s, D, C1, rho1, mZD, nuZY, rho2, L2, K, E2, TR]
      (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 5)) (Mon.var 5)) (Mon.var 10)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 26) (Mon.var 2)) (Mon.var 7)) (Mon.var 7)) (Mon.var 11)) (Mon.var 12)) (Mon.var 13)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 12)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 26) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 12)) (Mon.var 13)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 14)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 5)) (Mon.var 5)) (Mon.var 10)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 2)) (Mon.var 7)) (Mon.var 7)) (Mon.var 15)) (Mon.var 15)) (Mon.var 13)) (Mon.var 13)) (Mon.var 14)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6))))
      (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 5)) (Mon.var 5)) (Mon.var 10))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 5)) (Mon.var 5)) (Mon.var 10)))) (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 7)) (Mon.var 8)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 26) (Mon.var 2)) (Mon.var 7)) (Mon.var 7)) (Mon.var 11)) (Mon.var 12)) (Mon.var 13)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 12)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 26) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 12)) (Mon.var 13)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 0)) (Mon.var 14)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 2)) (Mon.var 7)) (Mon.var 7)) (Mon.var 15)) (Mon.var 15)) (Mon.var 13)) (Mon.var 13)) (Mon.var 14)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6))))) (by decide +kernel)) S2'
  have e2C : (kappa * s * s * nuZY + kappa * s * s * nuZY).oneValue
      (BPair.ofNat 2 * kappa * s * s * nuZY) :=
    polEqB [kappa, s, nuZY]
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2))) (by decide +kernel)
  have hR0 : BPair.ofNat 2 * kappa * s * s * nuZY
      ≤ BPair.ofNat 2 * kappa * kappa * dG * P * W0 * n * s * D
        + BPair.ofNat 2 * kappa * n * s * P * C1 * rho1 * mZD
        + BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * K * n * n * D
        + BPair.ofNat 8 * kappa * kappa * W0 * W0 * L2 * n * s * D
        + BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * K * n * n * D
        + BPair.ofNat 4 * kappa * kappa * E2 * n * n * D
        + BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * K * K * E2 * n * n * D := by
    refine leB_cancelL (x := kappa * s * s * nuZY + kappa * s * s * nuZY) ?_
    refine leB_congr_left (BPair.oneValue_trans Ee1 (BPair.oneValue_trans Ee2
      (BPair.add_congr (BPair.oneValue_symm e2C) (BPair.oneValue_refl _)))) S2'
  -- the second-order read at the mode weight, the self-read withdrawn
  have hZD' : kappa * (kappa * kappa * c0) * mZD
      ≤ kappa * kappa * c0 * nuZY + kappa * kappa * c0 * coff * mZD2 + kappa * cqp * mZD2 :=
    leB_trans hZD (leB_add (leB_add (leB_mulR (unitLeMul (unitLeMul hkappa hkappa) hc0) hmn)
      (leB_refl _)) (leB_refl _))
  have h := leB_mulL (unitLeMul (unitLeMul h2 hs) hs) hZD'
  repeat first | rw [BPair.left_distrib] at h | rw [BPair.right_distrib] at h
  repeat rw [← BPair.mul_assoc] at h
  repeat rw [← BPair.add_assoc] at h
  have u1 := leB_mulR (unitLeMul hkappa hc0) hR0
  repeat first | rw [BPair.left_distrib] at u1 | rw [BPair.right_distrib] at u1
  repeat rw [← BPair.mul_assoc] at u1
  repeat rw [← BPair.add_assoc] at u1
  have u2 := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul h2 hkappa) hkappa) hc0) hcoff) hZD2
  have u3 := leB_mulR (unitLeMul (unitLeMul h2 hkappa) hcqp) hZD2
  repeat rw [← BPair.mul_assoc] at u2
  repeat rw [← BPair.mul_assoc] at u3
  have uSelf : kappa * c0 * BPair.ofNat 2 * kappa * n * s * P * C1 * rho1 * mZD
      ≤ kappa * kappa * kappa * c0 * s * s * mZD := by
    have h' := leB_mulR (unitLeMul (unitLeMul (unitLeMul (unitLeMul hkappa hkappa) hc0) hmZD0) hs) hD1
    repeat rw [← BPair.mul_assoc] at h'
    refine leB_congr_left (BPair.oneValue_symm Eg1) (leB_trans h' ?_)
    exact leB_congr_left (BPair.oneValue_symm Eg2) (leB_refl _)
  have h' := leB_trans h (leB_add (leB_add (leB_congr_left (BPair.oneValue_symm Ef2) u1)
    (leB_congr_left (BPair.oneValue_symm Ef3) u2)) (leB_congr_left (BPair.oneValue_symm Ef4) u3))
  repeat rw [← BPair.add_assoc] at h'
  have h'' := leB_trans h' (leB_add (leB_add (leB_add (leB_add (leB_add (leB_add (leB_add
    (leB_add (leB_refl _) uSelf) (leB_refl _)) (leB_refl _)) (leB_refl _)) (leB_refl _)) (leB_refl _))
    (leB_congr_left (BPair.oneValue_symm Ef5) (leB_refl _)))
    (leB_congr_left (BPair.oneValue_symm Ef6) (leB_refl _)))
  have h'' : kappa * kappa * kappa * c0 * mZD * BPair.ofNat 2 * s * s ≤ ((kappa * kappa * kappa * c0 * s * s * mZD + (kappa * c0 * BPair.ofNat 2 * kappa * kappa * dG * P * W0 * n * s * D + kappa * c0 * BPair.ofNat 26 * P * C1 * C1 * rho2 * L2 * K * n * n * D + kappa * c0 * BPair.ofNat 8 * kappa * kappa * W0 * W0 * L2 * n * s * D + kappa * c0 * BPair.ofNat 26 * kappa * kappa * W0 * W0 * L2 * K * n * n * D + kappa * c0 * BPair.ofNat 4 * kappa * kappa * E2 * n * n * D + kappa * c0 * BPair.ofNat 32 * kappa * P * C1 * C1 * TR * TR * K * K * E2 * n * n * D + BPair.ofNat 8 * kappa * kappa * c0 * coff * K * K * E2 * n * n * D + BPair.ofNat 8 * kappa * cqp * K * K * E2 * n * n * D))) :=
    leB_congr (BPair.oneValue_refl _)
      (polEqB [kappa, c0, dG, P, W0, n, s, D, mZD, C1, rho2, L2, K, E2, TR, coff, cqp]
      (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 6)) (Mon.var 6)) (Mon.var 8)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 26)) (Mon.var 3)) (Mon.var 9)) (Mon.var 9)) (Mon.var 10)) (Mon.var 11)) (Mon.var 12)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 8)) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 4)) (Mon.var 11)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 26)) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 4)) (Mon.var 11)) (Mon.var 12)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 4)) (Mon.var 0)) (Mon.var 0)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 32)) (Mon.var 0)) (Mon.var 3)) (Mon.var 9)) (Mon.var 9)) (Mon.var 14)) (Mon.var 14)) (Mon.var 12)) (Mon.var 12)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 15)) (Mon.var 12)) (Mon.var 12)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 16)) (Mon.var 12)) (Mon.var 12)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7))))
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 6)) (Mon.var 6)) (Mon.var 8))) (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 26)) (Mon.var 3)) (Mon.var 9)) (Mon.var 9)) (Mon.var 10)) (Mon.var 11)) (Mon.var 12)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 8)) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 4)) (Mon.var 11)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 26)) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 4)) (Mon.var 11)) (Mon.var 12)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 4)) (Mon.var 0)) (Mon.var 0)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.cst 32)) (Mon.var 0)) (Mon.var 3)) (Mon.var 9)) (Mon.var 9)) (Mon.var 14)) (Mon.var 14)) (Mon.var 12)) (Mon.var 12)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 15)) (Mon.var 12)) (Mon.var 12)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 16)) (Mon.var 12)) (Mon.var 12)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 7))))) (by decide +kernel)) h''
  have e2X : (kappa * kappa * kappa * c0 * s * s * mZD + kappa * kappa * kappa * c0 * s * s * mZD).oneValue
      (BPair.ofNat 2 * kappa * kappa * kappa * c0 * s * s * mZD) :=
    polEqB [kappa, c0, s, mZD]
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3))))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3))) (by decide +kernel)
  have hX := leB_cancelL (x := kappa * kappa * kappa * c0 * s * s * mZD)
    (leB_congr_left (BPair.oneValue_trans Ef1 (BPair.oneValue_symm e2X)) h'')
  -- the index withdrawn at the conclusion's monomials
  refine leB_unscale_left hkappa0 ?_
  repeat first | rw [BPair.left_distrib] | rw [BPair.right_distrib]
  repeat rw [← BPair.mul_assoc]
  repeat rw [← BPair.add_assoc]
  refine leB_congr_left (Eh9) ?_
  refine leB_trans hX ?_
  refine leB_congr_right (Ep2) ?_
  exact leB_add (leB_add (leB_add (leB_add (leB_add (leB_add (leB_add
    (leB_congr_left (BPair.oneValue_symm Eh1) (leB_refl _))
    (leB_congr_left (BPair.oneValue_symm Eh2) (leB_refl _)))
    (leB_congr_left (BPair.oneValue_symm Eh4) (leB_refl _)))
    (leB_congr_left (BPair.oneValue_symm Eh5) (leB_refl _)))
    (leB_congr_left (BPair.oneValue_symm Eh6) (leB_refl _)))
    (leB_congr_left (BPair.oneValue_symm Eh3) (leB_refl _)))
    (leB_congr_left (BPair.oneValue_symm Eh7) (leB_refl _)))
    (leB_congr_left (BPair.oneValue_symm Eh8) (leB_refl _))

/-! The moments' key read, and the tail read at the key. -/

/-- The moments' key read: at the key's data, the near scale's reads of
the unit weight, the mode square and its square (`near_read_one`,
`near_read_two` at the near mass's read `Δ ≤ ϑ⁻¹ μ[1]`, the mode square's
lower weight `Q_-` at `mode_lower` and its square's at the mode mean's
read `μ[Q]² ≤ μ[Q²] μ[1]`), the deficit cell's read (`deficit_read`), the
remainder cell's two reads (`remainder_one`, `remainder_two`), the
variance floor with its side (`variance_floor`, `variance_side`), the
mode mean's read (`mode_mean_read`), the mode weight's square moment,
its leading member and the deficits' fold at it (`weight_square`,
`weight_lead`, `weight_deficit`) join to the excess and the mode read
(`excess_read`, `mode_read`) at the stated pairs `C_D`, `C_Z`, `P'` and
the clearing `2 κ² d_θ`, cleared at the scale pair `[n : s]`, the mass's
second member `m`, the mode read's pair `[e_W : e_W']` and the two
solves. -/
theorem key_moments (P j' : Nat)
    (ru rv TT mq mu1 sf mD mD2 muQ muQ2 nuQ nuQ2 muY nuY nuD2 D N mXQ mZt mZq mZD mZD2 nuZD2 mZY
      nuZY mQD mQD2 mQ2D2 nuQD nuQD2 nuD T2 T3g T3l T4 Sd mQY mY nuQY nuAQY nuAY r1 r2 g2 X Y X2
      Y2 Cu1 Cu2 CQ1 CQ2 CQQ2 n s e m Kn K kappa dG W0 W2 Winf2 C1 rho1 rho2 TR ThR coff cqp cq
      Om Wq CD CZ Pp cc c0 CW a1 g L nl Qp Del vd sn sd sn2 sd2 eWn eWd : BPair)
    -- the scale, the mass and the near scale
    (hn0 : BPair.unit < n) (hs0 : BPair.unit < s) (hns : n ≤ s) (he : BPair.unit ≤ e)
    (hm1 : BPair.ofPos .one ≤ m) (hem : e ≤ m) (hj : 1 ≤ j')
    (hKn1 : BPair.ofNat (2 * (1 + j')) ≤ Kn) (hKn2 : BPair.ofNat (4 * (2 + j')) ≤ Kn)
    (hK : (Kn * m).oneValue K)
    -- the member and window data, and the stated pairs
    (hP : 1 ≤ P) (hkappa1 : BPair.ofNat 1 ≤ kappa) (hdG1 : BPair.ofPos .one ≤ dG)
    (hW0 : BPair.ofPos .one ≤ W0) (hW20 : BPair.unit < W2) (hWinf2 : BPair.unit ≤ Winf2)
    (hWinf : Winf2 ≤ W2) (hC1 : BPair.unit ≤ C1) (hrho2 : BPair.unit ≤ rho2)
    (hTR : BPair.unit ≤ TR) (hThR : BPair.unit ≤ ThR) (hcoff : BPair.unit ≤ coff)
    (hcqp : BPair.unit ≤ cqp) (hcq : BPair.unit ≤ cq) (hOm : BPair.unit ≤ Om)
    (hg : BPair.unit ≤ g) (hL : BPair.unit ≤ L) (hnl : BPair.unit ≤ nl) (ha1 : BPair.unit ≤ a1)
    (hCW : BPair.unit ≤ CW) (heWn : BPair.unit ≤ eWn) (heWd : BPair.unit ≤ eWd)
    (hc0 : BPair.ofPos .one ≤ c0) (hcc : (kappa * kappa * c0).oneValue cc)
    (hCZ : ((BPair.ofNat 2 * dG * W0 * BPair.ofNat P + BPair.ofNat 8 * (W0 * W0) * (L + BPair.ofNat 2))).oneValue CZ)
    (hPp : ((BPair.ofNat 4 * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * (kappa * kappa) * c0
        + (BPair.ofNat 26 * BPair.ofNat P * (C1 * C1) * rho2 * (L + BPair.ofNat 2) * c0
          + BPair.ofNat 26 * (kappa * kappa) * (W0 * W0) * (L + BPair.ofNat 2) * c0) * K
        + (BPair.ofNat 32 * kappa * BPair.ofNat P * (C1 * C1) * (TR * TR) * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * c0
          + (BPair.ofNat 8 * kappa * c0 * coff + BPair.ofNat 8 * cqp) * (BPair.ofNat 1 + BPair.ofNat 2 * dG)) * (K * K))).oneValue Pp)
    (hCD : (BPair.ofNat 2 * dG * W0 + BPair.ofNat 1).oneValue CD)
    (hQp : BPair.unit ≤ Qp) (hDel0 : BPair.unit ≤ Del) (hvd1 : BPair.ofPos .one ≤ vd)
    -- the moments' positivity and the unit's cap
    (hmu1 : BPair.unit < mu1) (hmu1Del : mu1 ≤ Del) (hD0 : BPair.unit < D)
    (hsd0 : BPair.unit < sd) (hsd20 : BPair.unit < sd2) (hsn : BPair.unit ≤ sn)
    (hsn2 : BPair.unit ≤ sn2) (hmuQ : BPair.unit ≤ muQ) (hmuQ2 : BPair.unit ≤ muQ2)
    (hmD0 : BPair.unit ≤ mD) (hmQD0 : BPair.unit ≤ mQD) (hmZD0 : BPair.unit ≤ mZD)
    (hnuQ0 : BPair.unit ≤ nuQ) (hnuQ20 : BPair.unit ≤ nuQ2) (hX0 : BPair.unit ≤ X)
    (hY0 : BPair.unit ≤ Y) (hX20 : BPair.unit ≤ X2) (hY20 : BPair.unit ≤ Y2)
    -- the trial's and the mode member's reads
    (hru : (ru * mu1).oneValue (TT + mq))
    (hTT : TT * (m * m) * (s * s * s) ≤ BPair.ofNat 96 * (g * ((e * e) * sf)) * (s * s * s)
      + BPair.ofNat 12 * (ThR * mD2) * (m * m) * (s * s * s)
      + BPair.ofNat 3 * ((n * n) * mD) * (m * m) * s)
    (hmq : mq * (s * s * s) * cc ≤ cq * mD2 * (s * s * s) + cc * (n * Om * mD * (s * s))
      + Wq * (n * n) * mu1 * s)
    (hfp : sf ≤ BPair.ofNat 2 * kappa * mD)
    (hrv : (rv * D).oneValue N)
    (hN : N * (s * s) ≤ BPair.ofNat 2 * (n * n) * mXQ + BPair.ofNat 2 * mZt * (s * s)
      + mZq * (s * s))
    (hXQ : mXQ * eWd ≤ BPair.ofNat 8 * (kappa * kappa) * eWn * W2 * muQ
      + BPair.ofNat 8 * rho2 * nl * Winf2 * mQD * eWd)
    (hZt : mZt * (m * m) * (s * s) ≤ BPair.ofNat 192 * (g * kappa * (e * e) * mZD) * (s * s)
      + BPair.ofNat 12 * (ThR * mZD2) * (m * m) * (s * s)
      + BPair.ofNat 3 * (n * n * mZD) * (m * m))
    (hZq : mZq * (s * s) * cc ≤ cq * mZD2 * (s * s) + cc * (n * Om * mZD * s) + Wq * (n * n) * D)
    -- the solves
    (hsigp : sn ≤ W0 * W2 * sd) (hsigm : BPair.ofNat 2 * W2 * sd ≤ sn * (L + BPair.ofNat 2))
    (hsig2 : sn2 ≤ W0 * W0 * W2 * sd2)
    -- the profile's displays and the moments' order
    (h3 : muQ ≤ nuQ) (h4 : BPair.ofNat 2 * nuQ2 * s ≤ BPair.ofNat 2 * muQ2 * s + n * nuQ2)
    (hQ : BPair.ofNat 2 * nuQ * s ≤ BPair.ofNat 2 * muQ * s + n * nuQ) (hmuY : muY ≤ nuY)
    (hpQY : BPair.ofNat 2 * s * mQY ≤ BPair.ofNat 2 * s * nuQY + n * nuAQY)
    (hpQY' : BPair.ofNat 2 * s * nuQY ≤ BPair.ofNat 2 * s * mQY + n * nuAQY)
    (hpY : BPair.ofNat 2 * s * mY ≤ BPair.ofNat 2 * s * nuY + n * nuAY)
    (hpY' : BPair.ofNat 2 * s * nuY ≤ BPair.ofNat 2 * s * mY + n * nuAY)
    (hmn : mZY ≤ nuZY)
    (hnuD2 : nuD2 ≤ BPair.ofNat 2 * mD2) (hnuQD : nuQD ≤ BPair.ofNat 2 * mQD)
    (hnuD : nuD ≤ BPair.ofNat 2 * mD) (hnuQ2 : nuQ2 ≤ BPair.ofNat 2 * muQ2)
    (hnuQ : nuQ ≤ BPair.ofNat 2 * muQ) (hnuQD2 : nuQD2 ≤ BPair.ofNat 2 * mQD2)
    (hnuZD2 : nuZD2 ≤ BPair.ofNat 2 * mZD2)
    -- the identities
    (hid1 : (BPair.ofNat 2 * nuQ * s * sd).oneValue (n * (kappa * dG * sn * mu1 + r1 * sd)))
    (hid2 : (BPair.ofNat 2 * nuQ2 * s * sd).oneValue
      (n * (kappa * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd)))
    (hidQ : (BPair.ofNat 2 * nuQY * s * sd2).oneValue
      (n * (kappa * (dG + BPair.ofNat 2) * sn2 * muQ + r2 * sd2)))
    (hidY : (BPair.ofNat 2 * nuY * s * sd2).oneValue (n * (kappa * dG * sn2 * mu1 + r1 * sd2)))
    (hD : (D * mu1).oneValue (muQ2 * mu1 + (muQ * muQ).swap))
    (hCS : muQ * muQ ≤ muQ2 * mu1)
    (hF : (T3l * mu1).oneValue (BPair.ofNat 4 * kappa * (muQ * mY + (mu1 * mQY).swap)))
    (hsum : (BPair.ofNat 2 * nuZY * s + n * (T2 + T3g + T3l + T4)).oneValue
      (n * kappa * dG * Sd * D))
    -- the deficit cell's reads
    (hy : nuY * s ≤ BPair.ofNat P * (n * (kappa * dG * W0 * mu1 + C1 * rho1 * mD)
      + C1 * C1 * TR * TR * nuD2 * s))
    (hf : sf ≤ BPair.ofNat 2 * muY + BPair.ofNat 2 * coff * mD2)
    (hdef : BPair.ofNat 2 * kappa * cc * mD ≤ cc * sf + BPair.ofNat 2 * kappa * cqp * mD2)
    -- the remainder cell's reads
    (hr1 : windowsep.mag r1 ≤ a1 * mD + X)
    (hX : X * n ≤ BPair.ofNat 2 * s * (W0 * W0 * CW * TR) * Y) (hY : Y * Y ≤ nuQ * nuD2)
    (hr2 : windowsep.mag r2 ≤ a1 * mQD + windowsep.mag g2 + X2)
    (hg2 : windowsep.mag g2 * (BPair.ofNat 8 * (L + BPair.ofNat 2) * kappa * W2)
      ≤ kappa * kappa * (W2 * W2) * muQ + BPair.ofNat 64 * (W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2) * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2)) * mQD)
    (hX2 : X2 * n ≤ BPair.ofNat 2 * s * (W0 * W0 * CW * TR) * Y2) (hY2 : Y2 * Y2 ≤ nuQ2 * nuQD2)
    -- the mode weight's reads
    (hZ : mZD2 * (mu1 * mu1)
      ≤ BPair.ofNat 2 * (mu1 * mu1) * mQ2D2 + BPair.ofNat 2 * (muQ * muQ) * mD2)
    (hAQY : BPair.ofNat 2 * nuAQY ≤ BPair.ofNat 2 * kappa * (W0 * W0) * W2 * nuQD + nuQ2)
    (hAY : BPair.ofNat 2 * nuAY ≤ BPair.ofNat 2 * kappa * (W0 * W0) * W2 * nuD + nuQ)
    (hSd : Sd ≤ BPair.ofNat P * W0)
    (hT2 : windowsep.mag T2 ≤ BPair.ofNat P * C1 * rho1 * mZD)
    (hT3g : BPair.ofNat 2 * n * s * windowsep.mag T3g
      ≤ s * s * nuZY + BPair.ofNat 16 * BPair.ofNat P * (C1 * C1) * rho2 * Winf2 * (n * n) * mQD)
    (hT4 : BPair.ofNat 2 * n * s * windowsep.mag T4
      ≤ s * s * nuZY + BPair.ofNat 4 * BPair.ofNat P * (C1 * C1) * (TR * TR) * (s * s) * nuZD2)
    (hZD : kappa * (kappa * kappa * c0) * mZD
      ≤ kappa * kappa * c0 * mZY + kappa * kappa * c0 * coff * mZD2 + kappa * cqp * mZD2)
    -- the near mass
    (hvth : Del ≤ vd * mu1)
    -- the near scale's reads at the unit weight, the mode square and its square
    (hAu1 : mD * bpow (Kn * m * n) j' * s ≤ bpow (Kn * m * n) (1 + j') * mu1 + bpow s (1 + j') * Cu1)
    (hfaru1 : bpow s (1 + j') * Cu1
      ≤ BPair.ofNat (factorial (1 + j')) * bpow n (1 + j') * bpow m (1 + j') * Del)
    (hbitu1 : m * (vd * Del) ≤ bpow (BPair.ofNat 2) j' * Del)
    (hAu2 : mD2 * bpow (Kn * m * n) j' * (s * s)
      ≤ bpow (Kn * m * n) (2 + j') * mu1 + bpow s (2 + j') * Cu2)
    (hfaru2 : bpow s (2 + j') * Cu2
      ≤ BPair.ofNat (factorial (2 + j')) * bpow n (2 + j') * bpow m (2 + j') * Del)
    (hbitu2 : m * m * (vd * Del) ≤ bpow (BPair.ofNat 2) j' * Del)
    (hAQ1 : mQD * bpow (Kn * m * n) j' * s
      ≤ bpow (Kn * m * n) (1 + j') * muQ + bpow s (1 + j') * CQ1)
    (hfarQ1 : bpow s (1 + j') * CQ1
      ≤ BPair.ofNat (factorial (1 + j')) * bpow n (1 + j') * bpow m (1 + j') * (Del * Qp))
    (hbitQ1 : m * (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd * (Del * Qp)) ≤ bpow (BPair.ofNat 2) j' * (Del * n * kappa * dG * W2))
    (hAQ2 : mQD2 * bpow (Kn * m * n) j' * (s * s)
      ≤ bpow (Kn * m * n) (2 + j') * muQ + bpow s (2 + j') * CQ2)
    (hfarQ2 : bpow s (2 + j') * CQ2
      ≤ BPair.ofNat (factorial (2 + j')) * bpow n (2 + j') * bpow m (2 + j') * (Del * Qp))
    (hbitQ2 : m * m * (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd * (Del * Qp)) ≤ bpow (BPair.ofNat 2) j' * (Del * n * kappa * dG * W2))
    (hAQQ2 : mQ2D2 * bpow (Kn * m * n) j' * (s * s)
      ≤ bpow (Kn * m * n) (2 + j') * muQ2 + bpow s (2 + j') * CQQ2)
    (hfarQQ2 : bpow s (2 + j') * CQQ2
      ≤ BPair.ofNat (factorial (2 + j')) * bpow n (2 + j') * bpow m (2 + j') * (Del * (Qp * Qp)))
    (hbitQQ2 : m * m * (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd * (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd) * Del * (Del * (Qp * Qp)))
      ≤ bpow (BPair.ofNat 2) j' * ((Del * n * kappa * dG * W2) * (Del * n * kappa * dG * W2)))
    -- the cell's comparisons
    (hD1 : BPair.ofNat 2 * BPair.ofNat P * n * C1 * rho1 ≤ kappa * s)
    (hD2 : n * (K * K) * (BPair.ofNat 8 * cc * (C1 * C1 * TR * TR) + BPair.ofNat 4 * cc * coff
      + BPair.ofNat 4 * kappa * cqp) ≤ kappa * cc * s)
    (heta : n * (dG + BPair.ofNat 2) ≤ s)
    (hR1 : BPair.ofNat 1024 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2))
        * (BPair.ofNat 16 * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)) * (K * K)
            * (kappa * dG * W0 * W2 * n * s + BPair.ofNat 2 * a1 * K * (n * n))
          + BPair.ofNat 64 * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR) * (W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)) * (K * K * K * K) * (n * n))
      ≤ BPair.ofNat 4 * (kappa * kappa) * (W2 * W2) * (s * s))
    (hR2 : BPair.ofNat 32 * a1 * K * n * (L + BPair.ofNat 2) ≤ kappa * W2 * s)
    (hR3 : BPair.ofNat 8 * (L + BPair.ofNat 2)
        * (BPair.ofNat 2 * a1 * kappa * W2 + BPair.ofNat 16 * (W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2) * (L + BPair.ofNat 2)) * K * n
      ≤ kappa * kappa * (W2 * W2) * s)
    (hR4 : BPair.ofNat 1088 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2)) * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)) * W0 * (kappa * kappa)
          * (dG + BPair.ofNat 2) * (W2 * W2) * (K * K) * n * s
        + BPair.ofNat 1024 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2)) * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR))
          * (BPair.ofNat 2 * a1 * kappa * W2 + BPair.ofNat 16 * (W0 * W0 * W0 * W0 * CW * CW * rho2 * Winf2) * (L + BPair.ofNat 2)) * (K * K * K) * (n * n)
        + BPair.ofNat 4096 * ((L + BPair.ofNat 2) * (L + BPair.ofNat 2)) * ((W0 * W0 * CW * TR) * (W0 * W0 * CW * TR) * (W0 * W0 * CW * TR) * (W0 * W0 * CW * TR)) * kappa * W2 * (K * K * K * K)
          * (n * n)
      ≤ kappa * kappa * kappa * (W2 * W2 * W2) * (s * s)) :
    ru * (s * s * s) * (m * m) * cc
        ≤ BPair.ofNat 192 * (g * kappa * (CD * BPair.ofNat P)) * (e * e) * n * (s * s) * cc
          + (cc * (BPair.ofNat 24 * (ThR * (K * K)) + BPair.ofNat 3 * (CD * BPair.ofNat P) + Om * (CD * BPair.ofNat P))
            + BPair.ofNat 2 * (cq * (K * K)) + Wq) * (m * m) * (n * n) * s
      ∧ rv * (s * s) * (m * m) * eWd * cc
        ≤ BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * (m * m) * cc
          + BPair.ofNat 384 * (g * kappa * CZ) * (e * e) * n * s * eWd * cc
          + (cc * (BPair.ofNat 32 * (K * rho2 * nl * (L + BPair.ofNat 2))
              + (BPair.ofNat 6 + Om) * CZ
              + BPair.ofNat 96 * (ThR * (K * K) * (BPair.ofNat 1 + BPair.ofNat 2 * dG)))
            + (BPair.ofNat 384 * (g * kappa) + BPair.ofNat 6 + Om) * Pp
            + BPair.ofNat 4 * (cq * (K * K) * (BPair.ofNat 1 + BPair.ofNat 2 * dG)) + Wq)
            * (m * m) * (n * n) * eWd := by
  have hone : BPair.unit ≤ BPair.ofPos .one := leB_of_lt (unitLtOfPos .one)
  have hn : BPair.unit ≤ n := leB_of_lt hn0
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hsd : BPair.unit ≤ sd := leB_of_lt hsd0
  have hmu : BPair.unit ≤ mu1 := leB_of_lt hmu1
  have hDu : BPair.unit ≤ D := leB_of_lt hD0
  have hkappa : BPair.unit ≤ kappa := leB_trans (unitLeOfNat 1) hkappa1
  have hkappa0 : BPair.unit < kappa := ltB_trans_le (unitLtOfNat 0) hkappa1
  have hdG : BPair.unit ≤ dG := leB_trans hone hdG1
  have hW0u : BPair.unit ≤ W0 := leB_trans hone hW0
  have hW2 : BPair.unit ≤ W2 := leB_of_lt hW20
  have hm : BPair.unit ≤ m := leB_trans hone hm1
  have hL2 : BPair.unit ≤ L + BPair.ofNat 2 := unitLeAdd hL (unitLeOfNat 2)
  have hE2 : BPair.unit ≤ BPair.ofNat 1 + BPair.ofNat 2 * dG :=
    unitLeAdd (unitLeOfNat 1) (unitLeMul (unitLeOfNat 2) hdG)
  have hPB : BPair.ofPos .one ≤ BPair.ofNat P := leB_ofNat hP
  have hPu : BPair.unit ≤ BPair.ofNat P := unitLeOfNat P
  have hKn0 : BPair.unit ≤ Kn := leB_trans (unitLeOfNat _) hKn1
  have hK0 : BPair.unit ≤ K := leB_congr_right hK (unitLeMul hKn0 hm)
  have hc00 : BPair.unit ≤ c0 := leB_trans hone hc0
  have hcc0 : BPair.unit < cc :=
    BPair.lt_congr (BPair.oneValue_refl _) hcc
      (unitLtMul (unitLtMul hkappa0 hkappa0) (ltB_trans_le (unitLtOfPos .one) hc0))
  have hcc1 : BPair.unit ≤ cc := leB_of_lt hcc0
  have hvd : BPair.unit ≤ vd := leB_trans hone hvd1
  have hvd0 : BPair.unit < vd := ltB_trans_le (unitLtOfPos .one) hvd1
  have hcQ0 : BPair.unit < BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd :=
    unitLtMul (unitLtMul (unitLtMul (unitLtNat (by decide : 0 < 4))
      (unitLtAdd (unitLtOfNat 1) hL |> fun h =>
        BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq (BPair.add_comm _ _)) h)) hs0) hvd0
  have hcQ : BPair.unit ≤ BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd := leB_of_lt hcQ0
  have hPmQ : BPair.unit ≤ Del * n * kappa * dG * W2 :=
    unitLeMul (unitLeMul (unitLeMul (unitLeMul hDel0 hn) hkappa) hdG) hW2
  -- the near scale at the unit weight
  have hmD : mD * s ≤ BPair.ofNat 2 * K * n * mu1 :=
    near_read_one mD mu1 Cu1 n s m Kn K Del Del vd j' hj hn0 hm1 hKn1 hK hDel0 hvd0 hAu1 hfaru1
      hbitu1 hvth
  have hmD2 : mD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * mu1 :=
    near_read_two mD2 mu1 Cu2 n s m Kn K Del Del vd j' hj hn0 hm1 hKn2 hK hDel0 hvd0 hAu2 hfaru2
      hbitu2 hvth
  -- the deficit cell
  have hmDc := deficit_read mD mD2 mu1 nuY muY nuD2 sf n s kappa dG W0 C1 rho1 TR coff cqp cc K
    (BPair.ofNat P) hy hmuY hf hnuD2 hmD2 hdef hD1 hD2 hn hs0 hkappa0 hcc0 hPB hmu hmD0 hC1 hTR
    hcoff hcqp hK0
  have hmDe : mD * s ≤ CD * BPair.ofNat P * n * mu1 :=
    leB_congr_right (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left hCD))) hmDc
  -- the remainder cell's first read, the mode square's lower weight and its near-scale reads
  have hr1c := remainder_one r1 X Y nuQ nuD2 mD mD2 mu1 n s K W0 CW TR a1 kappa dG sn sd W2 L hr1
    hX hY hnuD2 hmD2 hmD hid1 hsigp hsigm hR1 hR2 hn0 hs0 hsd0 hX0 hY0 hnuQ0 hmu hK0 hW0u hCW hTR
    ha1 hkappa hdG hW2 hL
  have hlow := mode_lower muQ nuQ mu1 Del vd n s sn sd kappa dG W2 L r1 hid1 hQ hr1c hsigm hvth
    hns hdG1 hsd0 hn hkappa hsn hmu hnuQ0 hvd hW2 hL
  have hQD : mQD * s ≤ BPair.ofNat 2 * K * n * muQ :=
    near_read_one mQD muQ CQ1 n s m Kn K (Del * Qp) (Del * n * kappa * dG * W2) (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd) j' hj hn0 hm1 hKn1 hK
      (unitLeMul hDel0 hQp) hcQ0 hAQ1 hfarQ1 hbitQ1 hlow
  have hQD2 : mQD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * muQ :=
    near_read_two mQD2 muQ CQ2 n s m Kn K (Del * Qp) (Del * n * kappa * dG * W2) (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd) j' hj hn0 hm1 hKn2 hK
      (unitLeMul hDel0 hQp) hcQ0 hAQ2 hfarQ2 hbitQ2 hlow
  have hlowQ2 : Del * n * kappa * dG * W2 * (Del * n * kappa * dG * W2) ≤ BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd * (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd) * Del * muQ2 := by
    refine leB_trans (leB_mul_mono hPmQ (unitLeMul hcQ hmuQ) hlow hlow) ?_
    refine leB_congr_left (BPair.oneValue_of_eq (BPair.mul_mul_mul_comm _ _ _ _).symm) ?_
    refine leB_trans (leB_mulR (unitLeMul hcQ hcQ) hCS) ?_
    refine leB_trans (leB_mulR (unitLeMul hcQ hcQ) (leB_mulR hmuQ2 hmu1Del)) ?_
    exact leB_congr_left (BPair.oneValue_of_eq
      (BPair.mul_right_comm' (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd * (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd)) muQ2 Del).symm) (leB_refl _)
  have hQQ2 : mQ2D2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * muQ2 :=
    near_read_two mQ2D2 muQ2 CQQ2 n s m Kn K (Del * (Qp * Qp)) (Del * n * kappa * dG * W2 * (Del * n * kappa * dG * W2))
      (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd * (BPair.ofNat 4 * (L + BPair.ofNat 2) * s * vd) * Del) j' hj hn0 hm1 hKn2 hK (unitLeMul hDel0 (unitLeMul hQp hQp))
      (unitLtMul (unitLtMul hcQ0 hcQ0) (ltB_trans_le hmu1 hmu1Del)) hAQQ2 hfarQQ2 hbitQQ2 hlowQ2
  -- the remainder cell's second read
  have hr2c := remainder_two r2 g2 X2 Y2 nuQ2 nuQD2 muQ mQD mQD2 n s K W0 CW TR a1 kappa dG sn sd
    W2 L rho2 Winf2 hr2 hg2 hX2 hY2 hnuQD2 hQD2 hQD hid2 hsigp hsigm hR3 hR4 hn0 hs0 hsd0 hkappa0
    hW20 hW0 hX20 hY20 hnuQ20 hmuQ hK0 hCW hTR ha1 hdG hrho2 hWinf2 hL
  -- the variance floor, its side and the mode mean's read
  have hvar := mode_variance muQ muQ2 nuQ nuQ2 mu1 kappa dG n s sn sd r1 r2 (windowsep.mag r1)
    (windowsep.mag r2) hid1 hid2 h3 h4 (windowsep.le_mag r1) (windowsep.swap_le_mag r2) hns hn hs
    hsd hmu hmuQ (windowsep.unitLe_mag r2)
  have hvf := variance_floor muQ muQ2 mu1 D n s sn sd kappa dG (windowsep.mag r1)
    (windowsep.mag r2) hvar hr1c hr2c heta hD hmu1 hs0 hn hkappa hsn hmuQ
  have hvs := variance_side muQ D n s sn sd kappa W2 L hvf hsigm hsd0 hn hkappa hmuQ hL
  have hmean := mode_mean_read muQ nuQ mu1 D n s sn sd kappa dG r1 hid1 h3 hr1c hvf hdG1 hs0 hsd0
    hn hkappa hsn hmu hmuQ
  -- the mode weight's square moment, the fold's leading member and the deficits' fold
  have hZD2 := weight_square mZD2 mQ2D2 mD2 muQ muQ2 mu1 D K n s dG hZ hQQ2 hmD2 hmean hD hmu1 hn
    hs hK0 hmuQ
  have hlead := weight_lead T3l mQY mY nuQY nuY nuAQY nuAY nuQD nuD nuQ2 nuQ mQD mD muQ muQ2 mu1 D K
    n s sn sd sn2 sd2 kappa dG W0 W2 L r1 r2 hF hidQ hidY hr1c hr2c hpQY hpQY' hpY hpY' hAQY hAY
    hnuQD hnuD hnuQ2 hnuQ hQD hmD hsig2 hvf hvs hmean hD hmu1 hs0 hsd0 hsd20 hW0 hn hK0 hW2 hL hmuQ
    hDu hkappa hsn2 hdG
  have hZDc := weight_deficit mZD mZD2 nuZD2 mZY nuZY T2 T3g T3l T4 Sd D K n s kappa dG W0 L C1
    rho1 rho2 TR coff cqp c0 (BPair.ofNat P) mQD muQ W2 Winf2 hsum hSd hT2 hT3g hT4 hlead hZD hmn
    hZD2 hnuZD2 hQD hvs hWinf hD1 hkappa0 hs0 hn hDu hK0 hdG hL hC1 hrho2 hTR hcoff hcqp hc00 hPu
    hmQD0 hW2 hmZD0
  have hZDm : mZD * (s * s) * cc ≤ (CZ * n * s * cc + Pp * (n * n)) * D :=
    leB_congr (BPair.mul_congr (BPair.oneValue_refl _) hcc)
      (BPair.mul_congr_left (BPair.add_congr
        (BPair.mul_congr (BPair.mul_congr_left (BPair.mul_congr_left hCZ)) hcc)
        (BPair.mul_congr_left hPp))) hZDc
  -- the variance's side at the mode read's spelling
  have hDmr : n * kappa * sn * muQ ≤ D * s * (BPair.ofNat 2 * sd) := by
    have h8 : BPair.ofNat 8 * s * sd * D ≤ BPair.ofNat 10 * s * sd * D := by
      refine leB_congr (BPair.oneValue_of_eq (show BPair.ofNat 8 * (s * sd * D)
          = BPair.ofNat 8 * s * sd * D by repeat rw [← BPair.mul_assoc]))
        (BPair.oneValue_of_eq (show BPair.ofNat 10 * (s * sd * D)
          = BPair.ofNat 10 * s * sd * D by repeat rw [← BPair.mul_assoc])) ?_
      exact leB_mulL (unitLeMul (unitLeMul hs hsd) hDu) (leB_ofNat (by decide : 8 ≤ 10))
    have h := leB_trans hvf h8
    have e10 : (BPair.ofNat 10 * s * sd * D).oneValue
        (BPair.ofNat 5 * (D * s * (BPair.ofNat 2 * sd))) :=
      polEqB [s, sd, D]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 10) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)))
        (Pol.mon (Mon.mul (Mon.cst 5) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 0)) (Mon.mul (Mon.cst 2) (Mon.var 1))))) (by decide +kernel)
    have e5 : (BPair.ofNat 5 * n * kappa * sn * muQ).oneValue
        (BPair.ofNat 5 * (n * kappa * sn * muQ)) :=
      BPair.oneValue_of_eq (show BPair.ofNat 5 * n * kappa * sn * muQ = BPair.ofNat 5 * (n * kappa * sn * muQ) by repeat rw [← BPair.mul_assoc])
    exact leB_unscale_left (unitLtNat (by decide : 0 < 5))
      (leB_congr (e5) e10 h)
  have hsig' : W2 * (BPair.ofNat 2 * sd) ≤ sn * (L + BPair.ofNat 2) :=
    leB_congr_left (BPair.oneValue_of_eq (BPair.mul_left_comm' _ _ _).symm) hsigm
  -- the excess and the mode read
  refine ⟨?_, ?_⟩
  · exact excess_read ru TT mq mu1 sf mD mD2 K ThR cq Om Wq CD (BPair.ofNat P) g kappa n s e m cc
      hru hTT hmq hfp hmDe hmD2 hmu1 hns hn hs he hm hg hkappa hThR hcq hOm
      (leB_congr_right hCD (unitLeAdd (unitLeMul (unitLeMul (unitLeOfNat 2) hdG) hW0u)
        (unitLeOfNat 1))) hPu hcc1
  · exact mode_read rv D N mXQ mZt mZq mZD mZD2 mQD muQ K n s e m g kappa CZ ThR cq Om Wq Pp dG
      eWn eWd W2 Winf2 sn sd L nl rho2 cc hrv hN hXQ hQD hZt hZq hZDm hZD2 hDmr hsig' hWinf hem
      hD0 hs0 hns hn he hm hkappa1 hg hThR hcq hOm
      (leB_congr_right hPp (unitLeAdd (unitLeAdd
        (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 4) hE2) (unitLeMul hkappa hkappa)) hc00)
        (unitLeMul (unitLeAdd
          (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 26) hPu)
            (unitLeMul hC1 hC1)) hrho2) hL2) hc00)
          (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 26) (unitLeMul hkappa hkappa))
            (unitLeMul hW0u hW0u)) hL2) hc00)) hK0))
        (unitLeMul (unitLeAdd
          (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 32) hkappa)
            hPu) (unitLeMul hC1 hC1)) (unitLeMul hTR hTR)) hE2) hc00)
          (unitLeMul (unitLeAdd (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 8) hkappa) hc00) hcoff)
            (unitLeMul (unitLeOfNat 8) hcqp)) hE2)) (unitLeMul hK0 hK0))))
      heWn heWd hW2 hsd0 hL hnl hrho2
      (leB_congr_right hCZ (unitLeAdd
        (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 2) hdG) hW0u) hPu)
        (unitLeMul (unitLeMul (unitLeOfNat 8) (unitLeMul hW0u hW0u)) hL2)))
      hK0 hmuQ hmQD0 hcc1

/-- The tail read at the key's data: at a member and window read with
the member read `dim G ≤ 32 d_θ #p (L + 2)`, at a side, a mass and a halving at the three key comparisons
(`sideRead`, `massRead`, `tailRead`), the near mass's chain data at the
concentration key and the moments' reads at the scale `[1 : 2^i]`, the
mass `[1 : 2^{i_ε}]` and the near scale, the reads' sum sits under the
floor's multiple of the scale: the concentration key sits at or beyond
the far read's natural and clears the cleared comparison
(`kc_ge_jK`, `conc_key_read`), the near mass reads at the chain
(`near_mass`), the bit comparisons hold at the second power (`bit_unit`,
`bit_mode`, `bit_msq`), the cell's comparisons read off the key's list
(`tailRead`, `listRead_mem`), the stated pairs' identities and the
comparisons enter the pair carrier at the count expressions' one-member
reads (`ground.Pol.ofNat_val`, `ground.polEq`), the moments' key read
(`key_moments`) reads its two scale pairs off their groups (`puC_read`,
`pvC_read`), and the tail read closes (`tail_read`). -/
theorem moment_tail (t : Tail) (L ie fn fd i : Nat) (tp : t.pos) (hL1 : 1 ≤ L)
    (hdG32 : t.dG ≤ 32 * t.dth * t.np * (L + 2)) (hWinfN : t.Winf * t.Winf ≤ t.W2)
    (hLs : sideRead t.kappa fn fd L) (hie : massRead t L fn fd ie) (hi : tailRead t L ie fn fd i)
    (ru rv TT mq mu1 sf mD mD2 muQ muQ2 nuQ nuQ2 muY nuY nuD2 D N mXQ mZt mZq mZD mZD2 nuZD2
    mZY nuZY mQD mQD2 mQ2D2 nuQD nuQD2 nuD T2 T3g T3l T4 Sd mQY mY nuQY nuAQY nuAY r1 r2 g2 X Y
    X2 Y2 Cu1 Cu2 CQ1 CQ2 CQQ2 Del sn sd sn2 sd2 : BPair)
    (b : Nat → Nat → BPair) (dQ : Nat → BPair) (EQ Wk : BPair)
    (hb0 : ∀ p, p < t.np → b p 0 ≤ Del)
    (hpos : ∀ p, p < t.np → ∀ j, j ≤ kc t L ie i + 1 → BPair.unit < b p j)
    (hdec : ∀ p, p < t.np → b p (kc t L ie i + 1) ≤ b p (kc t L ie i))
    (hconv : ∀ p, p < t.np → ∀ j, j + 1 ≤ kc t L ie i → b p (j + 1) * b p (j + 1) ≤ b p j * b p (j + 2))
    (hEQ : ∀ p, p < t.np → (b p (kc t L ie i)).oneValue EQ)
    (hW : ∀ p, p < t.np → Del ≤ Wk * b p (kc t L ie i + 1))
    (hδ : ∀ p, p < t.np → dQ p ≤ BPair.ofNat 2 * BPair.ofNat t.dth * (b p (kc t L ie i) + (b p (kc t L ie i + 1)).swap))
    (hnear : BPair.ofNat 1 * BPair.ofNat (2 ^ ie) * EQ + (BPair.ofNat (2 ^ i) * (BPair.ofNat L * BPair.ofNat (2 ^ ie) + BPair.ofNat 2) * bsum dQ (List.range t.np)).swap ≤ BPair.ofNat 1 * BPair.ofNat (2 ^ ie) * mu1)
    (hEW : Del ≤ Wk * EQ) (hWk : Wk ≤ BPair.ofNat (cW t * kc t L ie i ^ exK t)) (hEQ0 : BPair.unit ≤ EQ) (hWk0 : BPair.unit ≤ Wk)
    (hDel0 : BPair.unit ≤ Del)
    (hmu1 : BPair.unit < mu1)
    (hmu1Del : mu1 ≤ Del)
    (hD0 : BPair.unit < D)
    (hsd0 : BPair.unit < sd)
    (hsd20 : BPair.unit < sd2)
    (hsn : BPair.unit ≤ sn)
    (hsn2 : BPair.unit ≤ sn2)
    (hmuQ : BPair.unit ≤ muQ)
    (hmuQ2 : BPair.unit ≤ muQ2)
    (hmD0 : BPair.unit ≤ mD)
    (hmQD0 : BPair.unit ≤ mQD)
    (hmZD0 : BPair.unit ≤ mZD)
    (hnuQ0 : BPair.unit ≤ nuQ)
    (hnuQ20 : BPair.unit ≤ nuQ2)
    (hX0 : BPair.unit ≤ X)
    (hY0 : BPair.unit ≤ Y)
    (hX20 : BPair.unit ≤ X2)
    (hY20 : BPair.unit ≤ Y2)
    (hru : (ru * mu1).oneValue (TT + mq))
    (hTT : TT * ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie))) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) ≤ BPair.ofNat 96 * ((BPair.ofNat t.g) * (((BPair.ofNat 1) * (BPair.ofNat 1)) * sf)) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) + BPair.ofNat 12 * ((BPair.ofNat (thetaR t L)) * mD2) * ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie))) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) + BPair.ofNat 3 * (((BPair.ofNat 1) * (BPair.ofNat 1)) * mD) * ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie))) * (BPair.ofNat (2 ^ i)))
    (hmq : mq * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) * (BPair.ofNat (pairClr t)) ≤ (BPair.ofNat (cq t L)) * mD2 * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) + (BPair.ofNat (pairClr t)) * ((BPair.ofNat 1) * (BPair.ofNat t.Om) * mD * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)))) + (BPair.ofNat (wq t)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * mu1 * (BPair.ofNat (2 ^ i)))
    (hfp : sf ≤ BPair.ofNat 2 * (BPair.ofNat t.kappa) * mD)
    (hrv : (rv * D).oneValue N)
    (hN : N * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) ≤ BPair.ofNat 2 * ((BPair.ofNat 1) * (BPair.ofNat 1)) * mXQ + BPair.ofNat 2 * mZt * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) + mZq * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))))
    (hXQ : mXQ * (BPair.ofNat (L * L + 2 * L + 2)) ≤ BPair.ofNat 8 * ((BPair.ofNat t.kappa) * (BPair.ofNat t.kappa)) * (BPair.ofNat 20) * (BPair.ofNat t.W2) * muQ + BPair.ofNat 8 * (BPair.ofNat (rho2 t L)) * (BPair.ofNat t.nl) * (BPair.ofNat (t.Winf * t.Winf)) * mQD * (BPair.ofNat (L * L + 2 * L + 2)))
    (hZt : mZt * ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie))) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) ≤ BPair.ofNat 192 * ((BPair.ofNat t.g) * (BPair.ofNat t.kappa) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * mZD) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) + BPair.ofNat 12 * ((BPair.ofNat (thetaR t L)) * mZD2) * ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie))) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) + BPair.ofNat 3 * ((BPair.ofNat 1) * (BPair.ofNat 1) * mZD) * ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie))))
    (hZq : mZq * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) * (BPair.ofNat (pairClr t)) ≤ (BPair.ofNat (cq t L)) * mZD2 * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) + (BPair.ofNat (pairClr t)) * ((BPair.ofNat 1) * (BPair.ofNat t.Om) * mZD * (BPair.ofNat (2 ^ i))) + (BPair.ofNat (wq t)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * D)
    (hsigp : sn ≤ (BPair.ofNat (w0 t)) * (BPair.ofNat t.W2) * sd)
    (hsigm : BPair.ofNat 2 * (BPair.ofNat t.W2) * sd ≤ sn * ((BPair.ofNat L) + BPair.ofNat 2))
    (hsig2 : sn2 ≤ (BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat t.W2) * sd2)
    (h3 : muQ ≤ nuQ)
    (h4 : BPair.ofNat 2 * nuQ2 * (BPair.ofNat (2 ^ i)) ≤ BPair.ofNat 2 * muQ2 * (BPair.ofNat (2 ^ i)) + (BPair.ofNat 1) * nuQ2)
    (hQ : BPair.ofNat 2 * nuQ * (BPair.ofNat (2 ^ i)) ≤ BPair.ofNat 2 * muQ * (BPair.ofNat (2 ^ i)) + (BPair.ofNat 1) * nuQ)
    (hmuY : muY ≤ nuY)
    (hpQY : BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * mQY ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * nuQY + (BPair.ofNat 1) * nuAQY)
    (hpQY' : BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * nuQY ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * mQY + (BPair.ofNat 1) * nuAQY)
    (hpY : BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * mY ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * nuY + (BPair.ofNat 1) * nuAY)
    (hpY' : BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * nuY ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * mY + (BPair.ofNat 1) * nuAY)
    (hmn : mZY ≤ nuZY)
    (hnuD2 : nuD2 ≤ BPair.ofNat 2 * mD2)
    (hnuQD : nuQD ≤ BPair.ofNat 2 * mQD)
    (hnuD : nuD ≤ BPair.ofNat 2 * mD)
    (hnuQ2 : nuQ2 ≤ BPair.ofNat 2 * muQ2)
    (hnuQ : nuQ ≤ BPair.ofNat 2 * muQ)
    (hnuQD2 : nuQD2 ≤ BPair.ofNat 2 * mQD2)
    (hnuZD2 : nuZD2 ≤ BPair.ofNat 2 * mZD2)
    (hid1 : (BPair.ofNat 2 * nuQ * (BPair.ofNat (2 ^ i)) * sd).oneValue ((BPair.ofNat 1) * ((BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * sn * mu1 + r1 * sd)))
    (hid2 : (BPair.ofNat 2 * nuQ2 * (BPair.ofNat (2 ^ i)) * sd).oneValue ((BPair.ofNat 1) * ((BPair.ofNat t.kappa) * ((BPair.ofNat t.dG) + BPair.ofNat 2) * sn * muQ + r2 * sd)))
    (hidQ : (BPair.ofNat 2 * nuQY * (BPair.ofNat (2 ^ i)) * sd2).oneValue ((BPair.ofNat 1) * ((BPair.ofNat t.kappa) * ((BPair.ofNat t.dG) + BPair.ofNat 2) * sn2 * muQ + r2 * sd2)))
    (hidY : (BPair.ofNat 2 * nuY * (BPair.ofNat (2 ^ i)) * sd2).oneValue ((BPair.ofNat 1) * ((BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * sn2 * mu1 + r1 * sd2)))
    (hD : (D * mu1).oneValue (muQ2 * mu1 + (muQ * muQ).swap))
    (hCS : muQ * muQ ≤ muQ2 * mu1)
    (hF : (T3l * mu1).oneValue (BPair.ofNat 4 * (BPair.ofNat t.kappa) * (muQ * mY + (mu1 * mQY).swap)))
    (hsum : (BPair.ofNat 2 * nuZY * (BPair.ofNat (2 ^ i)) + (BPair.ofNat 1) * (T2 + T3g + T3l + T4)).oneValue ((BPair.ofNat 1) * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * Sd * D))
    (hy : nuY * (BPair.ofNat (2 ^ i)) ≤ BPair.ofNat t.np * ((BPair.ofNat 1) * ((BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat (w0 t)) * mu1 + (BPair.ofNat (c1 t)) * (BPair.ofNat (rho1 t L)) * mD) + (BPair.ofNat (c1 t)) * (BPair.ofNat (c1 t)) * (BPair.ofNat (tR t L)) * (BPair.ofNat (tR t L)) * nuD2 * (BPair.ofNat (2 ^ i))))
    (hf : sf ≤ BPair.ofNat 2 * muY + BPair.ofNat 2 * (BPair.ofNat (cOff t L)) * mD2)
    (hdef : BPair.ofNat 2 * (BPair.ofNat t.kappa) * (BPair.ofNat (pairClr t)) * mD ≤ (BPair.ofNat (pairClr t)) * sf + BPair.ofNat 2 * (BPair.ofNat t.kappa) * (BPair.ofNat (cqp t)) * mD2)
    (hr1 : windowsep.mag r1 ≤ (BPair.ofNat (a1 t L)) * mD + X)
    (hX : X * (BPair.ofNat 1) ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * Y)
    (hY : Y * Y ≤ nuQ * nuD2)
    (hr2 : windowsep.mag r2 ≤ (BPair.ofNat (a1 t L)) * mQD + windowsep.mag g2 + X2)
    (hg2 : windowsep.mag g2 * (BPair.ofNat 8 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat t.kappa) * (BPair.ofNat t.W2)) ≤ (BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * ((BPair.ofNat t.W2) * (BPair.ofNat t.W2)) * muQ + BPair.ofNat 64 * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (rho2 t L)) * (BPair.ofNat (t.Winf * t.Winf))) * (((BPair.ofNat L) + BPair.ofNat 2) * ((BPair.ofNat L) + BPair.ofNat 2)) * mQD)
    (hX2 : X2 * (BPair.ofNat 1) ≤ BPair.ofNat 2 * (BPair.ofNat (2 ^ i)) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * Y2)
    (hY2 : Y2 * Y2 ≤ nuQ2 * nuQD2)
    (hZ : mZD2 * (mu1 * mu1) ≤ BPair.ofNat 2 * (mu1 * mu1) * mQ2D2 + BPair.ofNat 2 * (muQ * muQ) * mD2)
    (hAQY : BPair.ofNat 2 * nuAQY ≤ BPair.ofNat 2 * (BPair.ofNat t.kappa) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t))) * (BPair.ofNat t.W2) * nuQD + nuQ2)
    (hAY : BPair.ofNat 2 * nuAY ≤ BPair.ofNat 2 * (BPair.ofNat t.kappa) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t))) * (BPair.ofNat t.W2) * nuD + nuQ)
    (hSd : Sd ≤ BPair.ofNat t.np * (BPair.ofNat (w0 t)))
    (hT2 : windowsep.mag T2 ≤ BPair.ofNat t.np * (BPair.ofNat (c1 t)) * (BPair.ofNat (rho1 t L)) * mZD)
    (hT3g : BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat (2 ^ i)) * windowsep.mag T3g ≤ (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)) * nuZY + BPair.ofNat 16 * BPair.ofNat t.np * ((BPair.ofNat (c1 t)) * (BPair.ofNat (c1 t))) * (BPair.ofNat (rho2 t L)) * (BPair.ofNat (t.Winf * t.Winf)) * ((BPair.ofNat 1) * (BPair.ofNat 1)) * mQD)
    (hT4 : BPair.ofNat 2 * (BPair.ofNat 1) * (BPair.ofNat (2 ^ i)) * windowsep.mag T4 ≤ (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i)) * nuZY + BPair.ofNat 4 * BPair.ofNat t.np * ((BPair.ofNat (c1 t)) * (BPair.ofNat (c1 t))) * ((BPair.ofNat (tR t L)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) * nuZD2)
    (hZD : (BPair.ofNat t.kappa) * ((BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * (BPair.ofNat (2 * t.dth))) * mZD ≤ (BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * (BPair.ofNat (2 * t.dth)) * mZY + (BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * (BPair.ofNat (2 * t.dth)) * (BPair.ofNat (cOff t L)) * mZD2 + (BPair.ofNat t.kappa) * (BPair.ofNat (cqp t)) * mZD2)
    (hAu1 : mD * bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (jp t L ie i) * (BPair.ofNat (2 ^ i)) ≤ bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (1 + (jp t L ie i)) * mu1 + bpow (BPair.ofNat (2 ^ i)) (1 + (jp t L ie i)) * Cu1)
    (hfaru1 : bpow (BPair.ofNat (2 ^ i)) (1 + (jp t L ie i)) * Cu1 ≤ BPair.ofNat (factorial (1 + (jp t L ie i))) * bpow (BPair.ofNat 1) (1 + (jp t L ie i)) * bpow (BPair.ofNat (2 ^ ie)) (1 + (jp t L ie i)) * Del)
    (hAu2 : mD2 * bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (jp t L ie i) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) ≤ bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (2 + (jp t L ie i)) * mu1 + bpow (BPair.ofNat (2 ^ i)) (2 + (jp t L ie i)) * Cu2)
    (hfaru2 : bpow (BPair.ofNat (2 ^ i)) (2 + (jp t L ie i)) * Cu2 ≤ BPair.ofNat (factorial (2 + (jp t L ie i))) * bpow (BPair.ofNat 1) (2 + (jp t L ie i)) * bpow (BPair.ofNat (2 ^ ie)) (2 + (jp t L ie i)) * Del)
    (hAQ1 : mQD * bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (jp t L ie i) * (BPair.ofNat (2 ^ i)) ≤ bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (1 + (jp t L ie i)) * muQ + bpow (BPair.ofNat (2 ^ i)) (1 + (jp t L ie i)) * CQ1)
    (hfarQ1 : bpow (BPair.ofNat (2 ^ i)) (1 + (jp t L ie i)) * CQ1 ≤ BPair.ofNat (factorial (1 + (jp t L ie i))) * bpow (BPair.ofNat 1) (1 + (jp t L ie i)) * bpow (BPair.ofNat (2 ^ ie)) (1 + (jp t L ie i)) * (Del * (BPair.ofNat (qPlus t))))
    (hAQ2 : mQD2 * bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (jp t L ie i) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) ≤ bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (2 + (jp t L ie i)) * muQ + bpow (BPair.ofNat (2 ^ i)) (2 + (jp t L ie i)) * CQ2)
    (hfarQ2 : bpow (BPair.ofNat (2 ^ i)) (2 + (jp t L ie i)) * CQ2 ≤ BPair.ofNat (factorial (2 + (jp t L ie i))) * bpow (BPair.ofNat 1) (2 + (jp t L ie i)) * bpow (BPair.ofNat (2 ^ ie)) (2 + (jp t L ie i)) * (Del * (BPair.ofNat (qPlus t))))
    (hAQQ2 : mQ2D2 * bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (jp t L ie i) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) ≤ bpow ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 1)) (2 + (jp t L ie i)) * muQ2 + bpow (BPair.ofNat (2 ^ i)) (2 + (jp t L ie i)) * CQQ2)
    (hfarQQ2 : bpow (BPair.ofNat (2 ^ i)) (2 + (jp t L ie i)) * CQQ2 ≤ BPair.ofNat (factorial (2 + (jp t L ie i))) * bpow (BPair.ofNat 1) (2 + (jp t L ie i)) * bpow (BPair.ofNat (2 ^ ie)) (2 + (jp t L ie i)) * (Del * ((BPair.ofNat (qPlus t)) * (BPair.ofNat (qPlus t)))))
    : (ru + rv) * BPair.ofNat (2 ^ i) * BPair.ofNat fd < BPair.ofNat 1 * BPair.ofNat fn := by
  have hS : 0 < 2 ^ i := Nat.pow_pos (by decide : 0 < 2)
  have hM : 0 < 2 ^ ie := Nat.pow_pos (by decide : 0 < 2)
  have hm0 : BPair.unit < BPair.ofNat (2 ^ ie) := unitLtNat hM
  have hτD0 : BPair.unit < BPair.ofNat (tauD t L ie i) :=
    unitLtNat (Nat.lt_of_lt_of_le hM (tauD_ge t L ie i tp hL1))
  have he' : exK t + 1 ≤ kc t L ie i + 1 := Nat.le_succ_of_le (kc_ge_jK t L ie i tp hL1)
  have hτ : (BPair.ofNat (tauD t L ie i)).oneValue (BPair.ofNat 4 * BPair.ofNat t.dth * BPair.ofNat t.np * (BPair.ofNat L * BPair.ofNat (2 ^ ie) + BPair.ofNat 2) * BPair.ofNat (2 ^ i)) :=
    BPair.oneValue_symm (BPair.oneValue_trans (BPair.oneValue_symm (Pol.ofNat_val [t.dth, t.np, L, 2 ^ i, 2 ^ ie]
      (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 4))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 3)))))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (polEq [t.dth, t.np, L, 2 ^ i, 2 ^ ie]
        (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 4))) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 3)))
        (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 4))) (Pol.mon (Mon.cst 2)))))
        (by decide +kernel)))))
  have hkey : Wk * bpow (BPair.ofNat (tauD t L ie i)) (exK t + 1)
      ≤ BPair.ofNat (pasc (kc t L ie i + 1) (exK t + 1))
        * bpow (BPair.ofNat 1 * BPair.ofNat (2 ^ ie)) (exK t + 1) := by
    have hN := conc_key_read t L ie i tp hL1
    have hB : BPair.ofNat (cW t * kc t L ie i ^ exK t) * BPair.ofNat (tauD t L ie i ^ (exK t + 1))
        ≤ BPair.ofNat (pasc (kc t L ie i + 1) (exK t + 1)) * BPair.ofNat ((2 ^ ie) ^ (exK t + 1)) :=
      leB_congr (BPair.ofNat_mul _ _) (BPair.ofNat_mul _ _) (leB_ofNat hN)
    refine leB_trans (leB_mulL (unitLeBpow (unitLeOfNat _) _) hWk) ?_
    exact leB_congr (BPair.mul_congr (BPair.oneValue_refl _) (bpow_ofNat _ _))
      (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_trans (bpow_ofNat _ _)
        (bpow_congr (BPair.oneValue_symm (BPair.ofNat_one_mul _)) _))) hB
  have hun := bit_unit t L ie i tp hdG32
  have hM2 : 2 ^ ie ≤ 2 ^ (2 * ie) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_mul_of_pos_left ie (by decide : 0 < 2))
  have hu2n := bit_unit t L ie i tp hdG32
  rw [Nat.two_mul ie, powAdd 2 ie ie] at hu2n
  have hQn := bit_mode t L ie i tp
  have hQ2n := bit_mode t L ie i tp
  rw [Nat.two_mul ie, powAdd 2 ie ie] at hQ2n
  have hQQn := bit_msq t L ie i tp
  rw [Nat.two_mul ie, powAdd 2 ie ie] at hQQn
  have hXp : 4 * (L + 2) * 2 ^ i * (2 * cW t * kc t L ie i ^ exK t) = pairX t L ie i :=
    polEq [L, 2 ^ i, cW t, kc t L ie i ^ exK t]
    (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3))))
    (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.cst 8)) (Mon.var 2)) (Mon.var 3))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))))
    (by decide +kernel)
  have hn0 : BPair.unit < (BPair.ofNat 1) := unitLtNat (by decide : 0 < 1)
  have hs0 : BPair.unit < (BPair.ofNat (2 ^ i)) := unitLtNat hS
  have hns : (BPair.ofNat 1) ≤ (BPair.ofNat (2 ^ i)) := leB_ofNat hS
  have he : BPair.unit ≤ (BPair.ofNat 1) := unitLeOfNat 1
  have hm1 : BPair.ofPos .one ≤ (BPair.ofNat (2 ^ ie)) := leB_ofNat hM
  have hem : (BPair.ofNat 1) ≤ (BPair.ofNat (2 ^ ie)) := leB_ofNat hM
  have hj : 1 ≤ (jp t L ie i) := jp_ge1 t L ie i
  have hKn1 : BPair.ofNat (2 * (1 + (jp t L ie i))) ≤ (BPair.ofNat (48 * (4 + jp t L ie i))) := leB_ofNat (near_scale_stated 1 (jp t L ie i) (by decide))
  have hKn2 : BPair.ofNat (4 * (2 + (jp t L ie i))) ≤ (BPair.ofNat (48 * (4 + jp t L ie i))) := leB_ofNat (near_scale_stated 2 (jp t L ie i) (by decide))
  have hK : ((BPair.ofNat (48 * (4 + jp t L ie i))) * (BPair.ofNat (2 ^ ie))).oneValue (BPair.ofNat (nearScale t L ie i)) := BPair.oneValue_symm (BPair.ofNat_mul _ _)
  have hP : 1 ≤ t.np := tp.2.2.2.2.2.1
  have hkappa1 : BPair.ofNat 1 ≤ (BPair.ofNat t.kappa) := leB_ofNat tp.1
  have hdG1 : BPair.ofPos .one ≤ (BPair.ofNat t.dG) := leB_ofNat tp.2.2.1
  have hW0 : BPair.ofPos .one ≤ (BPair.ofNat (w0 t)) := leB_ofNat (Nat.le_add_right 1 _)
  have hW20 : BPair.unit < (BPair.ofNat t.W2) := unitLtNat tp.2.2.2.2.2.2.1
  have hWinf2 : BPair.unit ≤ (BPair.ofNat (t.Winf * t.Winf)) := unitLeOfNat _
  have hWinf : (BPair.ofNat (t.Winf * t.Winf)) ≤ (BPair.ofNat t.W2) := leB_ofNat hWinfN
  have hC1 : BPair.unit ≤ (BPair.ofNat (c1 t)) := unitLeOfNat _
  have hrho2 : BPair.unit ≤ (BPair.ofNat (rho2 t L)) := unitLeOfNat _
  have hTR : BPair.unit ≤ (BPair.ofNat (tR t L)) := unitLeOfNat _
  have hThR : BPair.unit ≤ (BPair.ofNat (thetaR t L)) := unitLeOfNat _
  have hcoff : BPair.unit ≤ (BPair.ofNat (cOff t L)) := unitLeOfNat _
  have hcqp : BPair.unit ≤ (BPair.ofNat (cqp t)) := unitLeOfNat _
  have hcq : BPair.unit ≤ (BPair.ofNat (cq t L)) := unitLeOfNat _
  have hOm : BPair.unit ≤ (BPair.ofNat t.Om) := unitLeOfNat _
  have hg : BPair.unit ≤ (BPair.ofNat t.g) := unitLeOfNat _
  have hL : BPair.unit ≤ (BPair.ofNat L) := unitLeOfNat _
  have hnl : BPair.unit ≤ (BPair.ofNat t.nl) := unitLeOfNat _
  have ha1 : BPair.unit ≤ (BPair.ofNat (a1 t L)) := unitLeOfNat _
  have hCW : BPair.unit ≤ (BPair.ofNat (cWd t)) := unitLeOfNat _
  have heWn : BPair.unit ≤ (BPair.ofNat 20) := unitLeOfNat _
  have heWd : BPair.unit ≤ (BPair.ofNat (L * L + 2 * L + 2)) := unitLeOfNat _
  have hc0 : BPair.ofPos .one ≤ (BPair.ofNat (2 * t.dth)) := leB_ofNat (Nat.mul_pos (by decide : 0 < 2) tp.2.2.2.1)
  have hcc : ((BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * (BPair.ofNat (2 * t.dth))).oneValue (BPair.ofNat (pairClr t)) :=
    BPair.oneValue_trans (BPair.oneValue_symm (Pol.ofNat_val [t.kappa, 2 * t.dth]
      (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 1)))))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (polEq [t.kappa, t.dth]
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.cst 2) (Mon.var 1))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 1)))
        (by decide +kernel))))
  have hCZ : ((BPair.ofNat 2 * (BPair.ofNat t.dG) * (BPair.ofNat (w0 t)) * BPair.ofNat t.np + BPair.ofNat 8 * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t))) * ((BPair.ofNat L) + BPair.ofNat 2))).oneValue (BPair.ofNat (cZ t L)) :=
    BPair.oneValue_trans (BPair.oneValue_symm (Pol.ofNat_val [t.dG, t.np, L, w0 t]
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 3)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 8) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))))))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (polEq [t.dG, t.np, L, w0 t]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 3)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 8) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 3)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 8) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))))
        (by decide +kernel))))
  have hPp : ((BPair.ofNat 4 * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat t.dG)) * ((BPair.ofNat t.kappa) * (BPair.ofNat t.kappa)) * (BPair.ofNat (2 * t.dth)) + (BPair.ofNat 26 * BPair.ofNat t.np * ((BPair.ofNat (c1 t)) * (BPair.ofNat (c1 t))) * (BPair.ofNat (rho2 t L)) * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 * t.dth)) + BPair.ofNat 26 * ((BPair.ofNat t.kappa) * (BPair.ofNat t.kappa)) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t))) * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 * t.dth))) * (BPair.ofNat (nearScale t L ie i)) + (BPair.ofNat 32 * (BPair.ofNat t.kappa) * BPair.ofNat t.np * ((BPair.ofNat (c1 t)) * (BPair.ofNat (c1 t))) * ((BPair.ofNat (tR t L)) * (BPair.ofNat (tR t L))) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat t.dG)) * (BPair.ofNat (2 * t.dth)) + (BPair.ofNat 8 * (BPair.ofNat t.kappa) * (BPair.ofNat (2 * t.dth)) * (BPair.ofNat (cOff t L)) + BPair.ofNat 8 * (BPair.ofNat (cqp t))) * (BPair.ofNat 1 + BPair.ofNat 2 * (BPair.ofNat t.dG))) * ((BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i))))).oneValue (BPair.ofNat ((ppC t L).at (nearScale t L ie i))) :=
    BPair.oneValue_trans (BPair.oneValue_symm (Pol.ofNat_val [t.kappa, t.dG, t.np, L, nearScale t L ie i, c1 t, rho2 t L, tR t L, cOff t L, w0 t, cqp t, 2 * t.dth]
      (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1))))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.mon (Mon.var 11))) (Pol.mul (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 26) (Mon.var 2)) (Mon.mul (Mon.var 5) (Mon.var 5))) (Mon.var 6))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 11))) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 26) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 11)))) (Pol.mon (Mon.var 4)))) (Pol.mul (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 2)) (Mon.mul (Mon.var 5) (Mon.var 5))) (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1))))) (Pol.mon (Mon.var 11))) (Pol.mul (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.var 11)) (Mon.var 8))) (Pol.mon (Mon.mul (Mon.cst 8) (Mon.var 10)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1)))))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 4)))))))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (polEq [t.kappa, t.dG, t.dth, t.np, L, nearScale t L ie i, c1 t, rho2 t L, tR t L, cOff t L, w0 t, cqp t]
        (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1))))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 2)))) (Pol.mul (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 26) (Mon.var 3)) (Mon.mul (Mon.var 6) (Mon.var 6))) (Mon.var 7))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 2)))) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 26) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.var 10) (Mon.var 10)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 2))))) (Pol.mon (Mon.var 5)))) (Pol.mul (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 3)) (Mon.mul (Mon.var 6) (Mon.var 6))) (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1))))) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 2)))) (Pol.mul (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 0)) (Mon.mul (Mon.cst 2) (Mon.var 2))) (Mon.var 9))) (Pol.mon (Mon.mul (Mon.cst 8) (Mon.var 11)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1)))))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5)))))
        (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 8) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1))))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 52) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.var 6) (Mon.var 6))) (Mon.var 7))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 52) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2)) (Mon.mul (Mon.var 10) (Mon.var 10)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.var 6) (Mon.var 6))) (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1))))) (Pol.mul (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 2)) (Mon.var 9))) (Pol.mon (Mon.mul (Mon.cst 8) (Mon.var 11)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1)))))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 5) (Mon.cst 0))))))))))))
        (by decide +kernel))))
  have hCD : (BPair.ofNat 2 * (BPair.ofNat t.dG) * (BPair.ofNat (w0 t)) + BPair.ofNat 1).oneValue (BPair.ofNat (cD t)) :=
    BPair.oneValue_trans (BPair.oneValue_symm (Pol.ofNat_val [t.dG, w0 t]
      (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.mon (Mon.cst 1)))))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (polEq [t.dG, w0 t]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.mon (Mon.cst 1)))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.mon (Mon.cst 1)))
        (by decide +kernel))))
  have hQp : BPair.unit ≤ (BPair.ofNat (qPlus t)) := unitLeOfNat _
  have hvd1 : BPair.ofPos .one ≤ (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) := leB_ofNat (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) (cW_pos t tp)) (Nat.pow_pos (kc_pos t L ie i tp)))
  have hvth : Del ≤ (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * mu1 :=
    near_mass t.np (kc t L ie i) (exK t) (cW t) b dQ Del EQ Wk Wk mu1 (BPair.ofNat 1)
      (BPair.ofNat (2 ^ i)) (BPair.ofNat (2 ^ ie)) (BPair.ofNat L) (BPair.ofNat t.dth)
      (BPair.ofNat (tauD t L ie i)) hn0 hm0 hτD0 (unitLeOfNat _) (unitLeOfNat _) (leB_of_lt hs0) hWk0 hb0
      hpos hdec hconv hEQ hW hkey he' hδ hnear hτ hEW hWk hEQ0
  have hbitu1 : (BPair.ofNat (2 ^ ie)) * ((BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * Del) ≤ bpow (BPair.ofNat 2) (jp t L ie i) * Del := by
    have hNn : Pol.val [2 ^ ie, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 2)))
        ≤ Pol.val [2 ^ ie, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mon (Mon.var 1)) := by
      show 2 ^ ie * (2 * cW t * kc t L ie i ^ exK t) ≤ 2 ^ jp t L ie i
      exact Nat.le_trans (Nat.mul_le_mul_right _ hM2) hun
    have hBn : BPair.ofNat (2 ^ ie) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) ≤ BPair.ofNat (2 ^ jp t L ie i) :=
      leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
    have hCn := leB_mulL hDel0 hBn
    have eL : (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * Del).oneValue
        ((BPair.ofNat (2 ^ ie)) * ((BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * Del)) :=
      BPair.oneValue_of_eq (show BPair.ofNat (2 ^ ie) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * Del = BPair.ofNat (2 ^ ie) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * Del) by repeat rw [← BPair.mul_assoc])
    exact leB_congr (eL) (BPair.mul_congr_left (bpow_ofNat 2 (jp t L ie i))) hCn
  have hbitu2 : (BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie)) * ((BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * Del) ≤ bpow (BPair.ofNat 2) (jp t L ie i) * Del := by
    have hNn : Pol.val [2 ^ ie, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 2)))
        ≤ Pol.val [2 ^ ie, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mon (Mon.var 1)) := by
      show 2 ^ ie * 2 ^ ie * (2 * cW t * kc t L ie i ^ exK t) ≤ 2 ^ jp t L ie i
      exact hu2n
    have hBn : BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) ≤ BPair.ofNat (2 ^ jp t L ie i) :=
      leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
    have hCn := leB_mulL hDel0 hBn
    have eL : (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * Del).oneValue
        ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie)) * ((BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * Del)) :=
      BPair.oneValue_of_eq (show BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * Del = BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * Del) by repeat rw [← BPair.mul_assoc])
    exact leB_congr (eL) (BPair.mul_congr_left (bpow_ofNat 2 (jp t L ie i))) hCn
  have eRQ : (BPair.ofNat (2 ^ jp t L ie i) * (BPair.ofNat t.kappa * BPair.ofNat t.dG * BPair.ofNat t.W2) * Del).oneValue
      (BPair.ofNat (2 ^ jp t L ie i) * (Del * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat t.W2))) :=
    polEqB [(BPair.ofNat (2 ^ jp t L ie i)), (BPair.ofNat t.kappa), (BPair.ofNat t.dG), (BPair.ofNat t.W2), Del]
      (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3))) (Mon.var 4)))
      (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))) (by decide +kernel)
  have hbitQ1 : (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * (Del * (BPair.ofNat (qPlus t)))) ≤ bpow (BPair.ofNat 2) (jp t L ie i) * (Del * (BPair.ofNat 1) * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat t.W2)) := by
    have hNn : Pol.val [t.kappa, t.dG, t.W2, L, 2 ^ i, 2 ^ ie, qPlus t, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mul (Pol.mul (Pol.mon (Mon.var 5)) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 8)))) (Pol.mon (Mon.var 6)))
        ≤ Pol.val [t.kappa, t.dG, t.W2, L, 2 ^ i, 2 ^ ie, qPlus t, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mon (Mon.mul (Mon.var 7) (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))) := by
      show 2 ^ ie * (4 * (L + 2) * 2 ^ i * (2 * cW t * kc t L ie i ^ exK t)) * qPlus t ≤ 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2)
      rw [hXp]
      exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hM2)) hQn
    have hBn : BPair.ofNat (2 ^ ie) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * BPair.ofNat (qPlus t) ≤ BPair.ofNat (2 ^ jp t L ie i) * (BPair.ofNat t.kappa * BPair.ofNat t.dG * BPair.ofNat t.W2) :=
      leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
    have hCn := leB_mulL hDel0 hBn
    have eL : (BPair.ofNat (2 ^ ie) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * BPair.ofNat (qPlus t) * Del).oneValue
        ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * (Del * (BPair.ofNat (qPlus t))))) :=
      polEqB [(BPair.ofNat (2 ^ ie)), (BPair.ofNat L), (BPair.ofNat (2 ^ i)), (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)), (BPair.ofNat (qPlus t)), Del]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5)))
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 4))))) (by decide +kernel)
    exact leB_congr (eL) (BPair.oneValue_trans (eRQ)
      (BPair.mul_congr (bpow_ofNat 2 (jp t L ie i)) (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.mul_ofNat_one Del))))))) hCn
  have hbitQ2 : (BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * (Del * (BPair.ofNat (qPlus t)))) ≤ bpow (BPair.ofNat 2) (jp t L ie i) * (Del * (BPair.ofNat 1) * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat t.W2)) := by
    have hNn : Pol.val [t.kappa, t.dG, t.W2, L, 2 ^ i, 2 ^ ie, qPlus t, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 8)))) (Pol.mon (Mon.var 6)))
        ≤ Pol.val [t.kappa, t.dG, t.W2, L, 2 ^ i, 2 ^ ie, qPlus t, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mon (Mon.mul (Mon.var 7) (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))) := by
      show 2 ^ ie * 2 ^ ie * (4 * (L + 2) * 2 ^ i * (2 * cW t * kc t L ie i ^ exK t)) * qPlus t ≤ 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2)
      rw [hXp]
      exact hQ2n
    have hBn : BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * BPair.ofNat (qPlus t) ≤ BPair.ofNat (2 ^ jp t L ie i) * (BPair.ofNat t.kappa * BPair.ofNat t.dG * BPair.ofNat t.W2) :=
      leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
    have hCn := leB_mulL hDel0 hBn
    have eL : (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * BPair.ofNat (qPlus t) * Del).oneValue
        ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * (Del * (BPair.ofNat (qPlus t))))) :=
      polEqB [(BPair.ofNat (2 ^ ie)), (BPair.ofNat L), (BPair.ofNat (2 ^ i)), (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)), (BPair.ofNat (qPlus t)), Del]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5)))
        (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 4))))) (by decide +kernel)
    exact leB_congr (eL) (BPair.oneValue_trans (eRQ)
      (BPair.mul_congr (bpow_ofNat 2 (jp t L ie i)) (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.mul_ofNat_one Del))))))) hCn
  have hbitQQ2 : (BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t))) * Del * (Del * ((BPair.ofNat (qPlus t)) * (BPair.ofNat (qPlus t))))) ≤ bpow (BPair.ofNat 2) (jp t L ie i) * ((Del * (BPair.ofNat 1) * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat t.W2)) * (Del * (BPair.ofNat 1) * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat t.W2))) := by
    have hNn : Pol.val [t.kappa, t.dG, t.W2, L, 2 ^ i, 2 ^ ie, qPlus t, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 8))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 8))))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6))))
        ≤ Pol.val [t.kappa, t.dG, t.W2, L, 2 ^ i, 2 ^ ie, qPlus t, 2 ^ jp t L ie i, 2 * cW t * kc t L ie i ^ exK t] (Pol.mon (Mon.mul (Mon.var 7) (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))))) := by
      show 2 ^ ie * 2 ^ ie * (4 * (L + 2) * 2 ^ i * (2 * cW t * kc t L ie i ^ exK t) * (4 * (L + 2) * 2 ^ i * (2 * cW t * kc t L ie i ^ exK t))) * (qPlus t * qPlus t) ≤ 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2 * (t.kappa * t.dG * t.W2))
      rw [hXp, ← sqRead (t.kappa * t.dG * t.W2)]
      exact hQQn
    have hBn : BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t))) * (BPair.ofNat (qPlus t) * BPair.ofNat (qPlus t)) ≤ BPair.ofNat (2 ^ jp t L ie i) * (BPair.ofNat t.kappa * BPair.ofNat t.dG * BPair.ofNat t.W2 * (BPair.ofNat t.kappa * BPair.ofNat t.dG * BPair.ofNat t.W2)) :=
      leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
    have hCn := leB_mulL (unitLeMul hDel0 hDel0) hBn
    have eL : (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t) * (BPair.ofNat 4 * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 * cW t * kc t L ie i ^ exK t))) * (BPair.ofNat (qPlus t) * BPair.ofNat (qPlus t)) * (Del * Del)).oneValue
        ((BPair.ofNat (2 ^ ie)) * (BPair.ofNat (2 ^ ie)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) * (BPair.ofNat 4 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t))) * Del * (Del * ((BPair.ofNat (qPlus t)) * (BPair.ofNat (qPlus t)))))) :=
      polEqB [(BPair.ofNat (2 ^ ie)), (BPair.ofNat L), (BPair.ofNat (2 ^ i)), (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)), (BPair.ofNat (qPlus t)), Del]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5))))
        (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.mul (Mon.var 4) (Mon.var 4)))))) (by decide +kernel)
    have eR : (BPair.ofNat (2 ^ jp t L ie i) * (BPair.ofNat t.kappa * BPair.ofNat t.dG * BPair.ofNat t.W2 * (BPair.ofNat t.kappa * BPair.ofNat t.dG * BPair.ofNat t.W2)) * (Del * Del)).oneValue
        (BPair.ofNat (2 ^ jp t L ie i) * ((Del * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat t.W2)) * (Del * (BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat t.W2)))) :=
      polEqB [(BPair.ofNat (2 ^ jp t L ie i)), (BPair.ofNat t.kappa), (BPair.ofNat t.dG), (BPair.ofNat t.W2), Del]
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)))) (Mon.mul (Mon.var 4) (Mon.var 4))))
        (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 1)) (Mon.var 2)) (Mon.var 3))))) (by decide +kernel)
    exact leB_congr (eL) (BPair.oneValue_trans (eR)
      (BPair.mul_congr (bpow_ofNat 2 (jp t L ie i)) (BPair.mul_congr (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.mul_ofNat_one Del))))) (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.mul_ofNat_one Del)))))))) hCn
  have hD1 : BPair.ofNat 2 * BPair.ofNat t.np * (BPair.ofNat 1) * (BPair.ofNat (c1 t)) * (BPair.ofNat (rho1 t L)) ≤ (BPair.ofNat t.kappa) * (BPair.ofNat (2 ^ i)) := by
    have rr := listRead_mem _ _ _ hi.1 _ (List.Mem.tail _ (List.Mem.head _))
    have rN : Pol.val [t.kappa, t.np, nearScale t L ie i, 2 ^ i, c1 t, rho1 t L] (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 4)) (Mon.var 5))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 2) (Mon.cst 0))))))))))))
        ≤ Pol.val [t.kappa, t.np, nearScale t L ie i, 2 ^ i, c1 t, rho1 t L] (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 3))) := rr
    have hNn : Pol.val [t.kappa, t.np, 2 ^ i, c1 t, rho1 t L] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.cst 1)) (Mon.var 3)) (Mon.var 4)))
        ≤ Pol.val [t.kappa, t.np, 2 ^ i, c1 t, rho1 t L] (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 2))) := by
      show Pol.val [t.kappa, t.np, nearScale t L ie i, 2 ^ i, c1 t, rho1 t L] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.cst 1)) (Mon.var 4)) (Mon.var 5)))
        ≤ Pol.val [t.kappa, t.np, nearScale t L ie i, 2 ^ i, c1 t, rho1 t L] (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 3)))
      rw [polEq [t.kappa, t.np, nearScale t L ie i, 2 ^ i, c1 t, rho1 t L]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.cst 1)) (Mon.var 4)) (Mon.var 5)))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 4)) (Mon.var 5))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 2) (Mon.cst 0))))))))))))
        (by decide +kernel), polEq [t.kappa, t.np, nearScale t L ie i, 2 ^ i, c1 t, rho1 t L]
        (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 3)))
        (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 3)))
        (by decide +kernel)]
      exact rN
    exact leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
  have hD2 : (BPair.ofNat 1) * ((BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i))) * (BPair.ofNat 8 * (BPair.ofNat (pairClr t)) * ((BPair.ofNat (c1 t)) * (BPair.ofNat (c1 t)) * (BPair.ofNat (tR t L)) * (BPair.ofNat (tR t L))) + BPair.ofNat 4 * (BPair.ofNat (pairClr t)) * (BPair.ofNat (cOff t L)) + BPair.ofNat 4 * (BPair.ofNat t.kappa) * (BPair.ofNat (cqp t))) ≤ (BPair.ofNat t.kappa) * (BPair.ofNat (pairClr t)) * (BPair.ofNat (2 ^ i)) := by
    have rr := listRead_mem _ _ _ hi.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have rN : Pol.val [t.kappa, t.dG, t.dth, t.c2, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L] (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.var 6) (Mon.var 6))) (Mon.mul (Mon.var 7) (Mon.var 7))) (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 8)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.cst 4) (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 4) (Mon.cst 0))))))))))))
        ≤ Pol.val [t.kappa, t.dG, t.dth, t.c2, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 2)) (Mon.var 5))) := rr
    have hNn : Pol.val [t.kappa, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L, cqp t, pairClr t] (Pol.mul (Pol.mon (Mon.mul (Mon.cst 1) (Mon.mul (Mon.var 1) (Mon.var 1)))) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 7)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 7)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 6)))))
        ≤ Pol.val [t.kappa, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L, cqp t, pairClr t] (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 7)) (Mon.var 2))) := by
      show Pol.val [t.kappa, t.dG, t.dth, t.c2, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L] (Pol.mul (Pol.mon (Mon.mul (Mon.cst 1) (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 8) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2))) (Mon.var 8)))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 4) (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 3)) (Mon.var 2))) (Pol.mon (Mon.var 0)))))))
        ≤ Pol.val [t.kappa, t.dG, t.dth, t.c2, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L] (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2))) (Mon.var 5)))
      rw [polEq [t.kappa, t.dG, t.dth, t.c2, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L]
        (Pol.mul (Pol.mon (Mon.mul (Mon.cst 1) (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 8) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2))) (Mon.var 8)))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 4) (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 3)) (Mon.var 2))) (Pol.mon (Mon.var 0)))))))
        (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0))) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.var 6) (Mon.var 6))) (Mon.mul (Mon.var 7) (Mon.var 7))) (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.cst 8) (Mon.var 8)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 1)) (Mon.var 3)) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.cst 4) (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 4) (Mon.cst 0)))))))))))))
        (by decide +kernel), polEq [t.kappa, t.dG, t.dth, t.c2, nearScale t L ie i, 2 ^ i, c1 t, tR t L, cOff t L]
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 2))) (Mon.var 5)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 2)) (Mon.var 5))))
        (by decide +kernel)]
      exact Nat.mul_le_mul_left _ rN
    exact leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
  have heta : (BPair.ofNat 1) * ((BPair.ofNat t.dG) + BPair.ofNat 2) ≤ (BPair.ofNat (2 ^ i)) := by
    have rr := listRead_mem _ _ _ hi.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have rN : Pol.val [t.dG, nearScale t L ie i, 2 ^ i] (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 1) (Mon.cst 0))))))))))))
        ≤ Pol.val [t.dG, nearScale t L ie i, 2 ^ i] (Pol.mon (Mon.mul (Mon.cst 1) (Mon.var 2))) := rr
    have hNn : Pol.val [t.dG, 2 ^ i] (Pol.mul (Pol.mon (Mon.cst 1)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))))
        ≤ Pol.val [t.dG, 2 ^ i] (Pol.mon (Mon.var 1)) := by
      show Pol.val [t.dG, nearScale t L ie i, 2 ^ i] (Pol.mul (Pol.mon (Mon.cst 1)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))))
        ≤ Pol.val [t.dG, nearScale t L ie i, 2 ^ i] (Pol.mon (Mon.var 2))
      rw [polEq [t.dG, nearScale t L ie i, 2 ^ i]
        (Pol.mul (Pol.mon (Mon.cst 1)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))))
        (Pol.add (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 1) (Mon.cst 0))))))))))))
        (by decide +kernel), polEq [t.dG, nearScale t L ie i, 2 ^ i]
        (Pol.mon (Mon.var 2))
        (Pol.mon (Mon.mul (Mon.cst 1) (Mon.var 2)))
        (by decide +kernel)]
      exact rN
    exact leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
  have hR1 : BPair.ofNat 1024 * (((BPair.ofNat L) + BPair.ofNat 2) * ((BPair.ofNat L) + BPair.ofNat 2)) * (BPair.ofNat 16 * (((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L)))) * ((BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i))) * ((BPair.ofNat t.kappa) * (BPair.ofNat t.dG) * (BPair.ofNat (w0 t)) * (BPair.ofNat t.W2) * (BPair.ofNat 1) * (BPair.ofNat (2 ^ i)) + BPair.ofNat 2 * (BPair.ofNat (a1 t L)) * (BPair.ofNat (nearScale t L ie i)) * ((BPair.ofNat 1) * (BPair.ofNat 1))) + BPair.ofNat 64 * (((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L)))) * ((BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i))) * ((BPair.ofNat 1) * (BPair.ofNat 1))) ≤ BPair.ofNat 4 * ((BPair.ofNat t.kappa) * (BPair.ofNat t.kappa)) * ((BPair.ofNat t.W2) * (BPair.ofNat t.W2)) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) := by
    have rr := listRead_mem _ _ _ hi.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))
    rw [pow4Read (w0 t), pow5Read (w0 t), pow8Read (w0 t), pow4Read (cWd t), pow4Read (tR t L)] at rr
    have rN : Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8192)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 8))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 16384)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 7)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 6)) (Mon.var 6)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.cst 0))))))))))))
        ≤ Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 5))) := rr
    have hNn : Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)))) (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 9)) (Mon.var 2)) (Mon.cst 1)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 8)) (Mon.var 4)) (Mon.mul (Mon.cst 1) (Mon.cst 1)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)) (Mon.var 4))) (Mon.mul (Mon.cst 1) (Mon.cst 1))))))
        ≤ Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 5) (Mon.var 5)))) := by
      show Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)))) (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 9)) (Mon.var 2)) (Mon.cst 1)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 8)) (Mon.var 4)) (Mon.mul (Mon.cst 1) (Mon.cst 1)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)) (Mon.var 4))) (Mon.mul (Mon.cst 1) (Mon.cst 1))))))
        ≤ Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 5) (Mon.var 5))))
      rw [polEq [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t]
        (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)))) (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 9)) (Mon.var 2)) (Mon.cst 1)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 8)) (Mon.var 4)) (Mon.mul (Mon.cst 1) (Mon.cst 1)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 7)) (Mon.var 6)))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)) (Mon.var 4))) (Mon.mul (Mon.cst 1) (Mon.cst 1))))))
        (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 16384)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.mon (Mon.var 5))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 32768)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4))))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 65536)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 7)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 6)) (Mon.var 6)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)))))
        (by decide +kernel), polEq [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 5) (Mon.var 5))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 5)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 5))))
        (by decide +kernel)]
      have r4 : Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.mul (Pol.mon (Mon.mul (Mon.cst 4) (Mon.var 5))) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8192)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 8))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 16384)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 7)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 6)) (Mon.var 6)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.cst 0)))))))))))))
          ≤ Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 5)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 5)))) :=
        Nat.mul_le_mul_left _ rN
      rw [polEq [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, tR t L, cWd t, a1 t L, w0 t]
        (Pol.mul (Pol.mon (Mon.mul (Mon.cst 4) (Mon.var 5))) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8192)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 8))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 16384)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 7)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 6)) (Mon.var 6)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.cst 0)))))))))))))
        (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 16384)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.mon (Mon.var 5))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 32768)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)))) (Pol.mon (Mon.var 5)))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 65536)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.var 7)) (Mon.var 7)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 6)) (Mon.var 6)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)))) (Pol.mon (Mon.var 5))))
        (by decide +kernel)] at r4
      refine Nat.le_trans ?_ r4
      show 16384 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * t.kappa * t.dG * t.W2 * (nearScale t L ie i * nearScale t L ie i) * 2 ^ i + 32768 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * a1 t L * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i) + 65536 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t * cWd t * cWd t) * (tR t L * tR t L * tR t L * tR t L) * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i * nearScale t L ie i)
        ≤ 16384 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * t.kappa * t.dG * t.W2 * (nearScale t L ie i * nearScale t L ie i) * 2 ^ i + 32768 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * a1 t L * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i) * 2 ^ i + 65536 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t * cWd t * cWd t) * (tR t L * tR t L * tR t L * tR t L) * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i * nearScale t L ie i) * 2 ^ i
      exact Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (Nat.le_mul_of_pos_right _ hS))
        (Nat.le_mul_of_pos_right _ hS)
    exact leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
  have hR2 : BPair.ofNat 32 * (BPair.ofNat (a1 t L)) * (BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat 1) * ((BPair.ofNat L) + BPair.ofNat 2) ≤ (BPair.ofNat t.kappa) * (BPair.ofNat t.W2) * (BPair.ofNat (2 ^ i)) := by
    have rr := listRead_mem _ _ _ hi.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    have rN : Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L] (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.cst 32) (Mon.var 5))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 3) (Mon.cst 0))))))))))))
        ≤ Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L] (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4))) := rr
    have hNn : Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L] (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 5)) (Mon.var 3)) (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2))))
        ≤ Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L] (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4))) := by
      show Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L] (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 5)) (Mon.var 3)) (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2))))
        ≤ Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L] (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)))
      rw [polEq [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L]
        (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 5)) (Mon.var 3)) (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2))))
        (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mul (Pol.mon (Mon.mul (Mon.cst 32) (Mon.var 5))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 3) (Mon.cst 0))))))))))))
        (by decide +kernel), polEq [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, a1 t L]
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 4)))
        (by decide +kernel)]
      exact rN
    exact leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
  have hR3 : BPair.ofNat 8 * ((BPair.ofNat L) + BPair.ofNat 2) * (BPair.ofNat 2 * (BPair.ofNat (a1 t L)) * (BPair.ofNat t.kappa) * (BPair.ofNat t.W2) + BPair.ofNat 16 * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (rho2 t L)) * (BPair.ofNat (t.Winf * t.Winf))) * ((BPair.ofNat L) + BPair.ofNat 2)) * (BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat 1) ≤ (BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * ((BPair.ofNat t.W2) * (BPair.ofNat t.W2)) * (BPair.ofNat (2 ^ i)) := by
    have rr := listRead_mem _ _ _ hi.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
    rw [pow4Read (w0 t)] at rr
    have rN : Pol.val [t.kappa, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t] (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 8)) (Mon.var 0)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9))) (Mon.mul (Mon.var 7) (Mon.var 7))) (Mon.var 6)) (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 4) (Mon.cst 0))))))))))))
        ≤ Pol.val [t.kappa, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 5))) := rr
    have hNn : Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t, t.Winf * t.Winf] (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 7)) (Mon.var 0)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 8) (Mon.var 8)) (Mon.var 8)) (Mon.var 8)) (Mon.var 6)) (Mon.var 6)) (Mon.var 5)) (Mon.var 9)))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.cst 1)))
        ≤ Pol.val [t.kappa, t.W2, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t, t.Winf * t.Winf] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 4))) := by
      show Pol.val [t.kappa, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t] (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 8)) (Mon.var 0)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 7)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.var 2) (Mon.var 2))))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.cst 1)))
        ≤ Pol.val [t.kappa, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 5)))
      rw [polEq [t.kappa, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 8)) (Mon.var 0)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)) (Mon.var 7)) (Mon.var 7)) (Mon.var 6)) (Mon.mul (Mon.var 2) (Mon.var 2))))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.cst 1)))
        (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 8)) (Mon.var 0)) (Mon.var 1))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9))) (Mon.mul (Mon.var 7) (Mon.var 7))) (Mon.var 6)) (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))))) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mon (Mon.mul (Mon.var 4) (Mon.cst 0))))))))))))
        (by decide +kernel), polEq [t.kappa, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, cWd t, a1 t L, w0 t]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 5)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 5)))
        (by decide +kernel)]
      exact rN
    exact leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
  have hR4 : BPair.ofNat 1088 * (((BPair.ofNat L) + BPair.ofNat 2) * ((BPair.ofNat L) + BPair.ofNat 2)) * (((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L)))) * (BPair.ofNat (w0 t)) * ((BPair.ofNat t.kappa) * (BPair.ofNat t.kappa)) * ((BPair.ofNat t.dG) + BPair.ofNat 2) * ((BPair.ofNat t.W2) * (BPair.ofNat t.W2)) * ((BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i))) * (BPair.ofNat 1) * (BPair.ofNat (2 ^ i)) + BPair.ofNat 1024 * (((BPair.ofNat L) + BPair.ofNat 2) * ((BPair.ofNat L) + BPair.ofNat 2)) * (((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L)))) * (BPair.ofNat 2 * (BPair.ofNat (a1 t L)) * (BPair.ofNat t.kappa) * (BPair.ofNat t.W2) + BPair.ofNat 16 * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (rho2 t L)) * (BPair.ofNat (t.Winf * t.Winf))) * ((BPair.ofNat L) + BPair.ofNat 2)) * ((BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i))) * ((BPair.ofNat 1) * (BPair.ofNat 1)) + BPair.ofNat 4096 * (((BPair.ofNat L) + BPair.ofNat 2) * ((BPair.ofNat L) + BPair.ofNat 2)) * (((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L))) * ((BPair.ofNat (w0 t)) * (BPair.ofNat (w0 t)) * (BPair.ofNat (cWd t)) * (BPair.ofNat (tR t L)))) * (BPair.ofNat t.kappa) * (BPair.ofNat t.W2) * ((BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat (nearScale t L ie i))) * ((BPair.ofNat 1) * (BPair.ofNat 1)) ≤ (BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * (BPair.ofNat t.kappa) * ((BPair.ofNat t.W2) * (BPair.ofNat t.W2) * (BPair.ofNat t.W2)) * ((BPair.ofNat (2 ^ i)) * (BPair.ofNat (2 ^ i))) := by
    have rr := listRead_mem _ _ _ hi.1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))
    rw [pow4Read (w0 t), pow5Read (w0 t), pow8Read (w0 t), pow4Read (cWd t), pow4Read (tR t L)] at rr
    have rN : Pol.val [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t] (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 10)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11))) (Mon.mul (Mon.var 9) (Mon.var 9))) (Mon.var 7)) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 8) (Mon.var 8)) (Mon.var 8)) (Mon.var 8)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.cst 0))))))))))))
        ≤ Pol.val [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2))) (Mon.var 6))) := rr
    have hNn : Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t, t.Winf * t.Winf] (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7))))) (Pol.mon (Mon.var 10))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 4)))) (Pol.mon (Mon.cst 1))) (Pol.mon (Mon.var 5))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7))))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 9)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 10)) (Mon.var 10)) (Mon.var 8)) (Mon.var 8)) (Mon.var 6)) (Mon.var 11)))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)))) (Pol.mon (Mon.mul (Mon.cst 1) (Mon.cst 1))))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 10) (Mon.var 10)) (Mon.var 8)) (Mon.var 7))))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 4)) (Mon.var 4)))) (Pol.mon (Mon.mul (Mon.cst 1) (Mon.cst 1)))))
        ≤ Pol.val [t.kappa, t.dG, t.W2, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t, t.Winf * t.Winf] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2))) (Mon.mul (Mon.var 5) (Mon.var 5)))) := by
      show Pol.val [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t] (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))))) (Pol.mon (Mon.var 11))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5)))) (Pol.mon (Mon.cst 1))) (Pol.mon (Mon.var 6))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 10)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 9)) (Mon.var 9)) (Mon.var 7)) (Mon.mul (Mon.var 3) (Mon.var 3))))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.cst 1) (Mon.cst 1))))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.cst 1) (Mon.cst 1)))))
        ≤ Pol.val [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2))) (Mon.mul (Mon.var 6) (Mon.var 6))))
      rw [polEq [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t]
        (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))))) (Pol.mon (Mon.var 11))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5)))) (Pol.mon (Mon.cst 1))) (Pol.mon (Mon.var 6))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 10)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 9)) (Mon.var 9)) (Mon.var 7)) (Mon.mul (Mon.var 3) (Mon.var 3))))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.cst 1) (Mon.cst 1))))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8)) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 9)) (Mon.var 8))))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.cst 1) (Mon.cst 1)))))
        (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5)))) (Pol.mon (Mon.var 6))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 10)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11))) (Mon.mul (Mon.var 9) (Mon.var 9))) (Mon.var 7)) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5))))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 8) (Mon.var 8)) (Mon.var 8)) (Mon.var 8)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)))))
        (by decide +kernel), polEq [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2))) (Mon.mul (Mon.var 6) (Mon.var 6))))
        (Pol.mon (Mon.mul (Mon.var 6) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2))) (Mon.var 6))))
        (by decide +kernel)]
      have r4 : Pol.val [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t] (Pol.mul (Pol.mon (Mon.var 6)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 10)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11))) (Mon.mul (Mon.var 9) (Mon.var 9))) (Mon.var 7)) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 8) (Mon.var 8)) (Mon.var 8)) (Mon.var 8)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.cst 0)))))))))))))
          ≤ Pol.val [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t] (Pol.mon (Mon.mul (Mon.var 6) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2))) (Mon.var 6)))) :=
        Nat.mul_le_mul_left _ rN
      rw [polEq [t.kappa, t.dG, t.W2, t.Winf, L, nearScale t L ie i, 2 ^ i, rho2 t L, tR t L, cWd t, a1 t L, w0 t]
        (Pol.mul (Pol.mon (Mon.var 6)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mon (Mon.cst 0)) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 10)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11))) (Mon.mul (Mon.var 9) (Mon.var 9))) (Mon.var 7)) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))))) (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 8) (Mon.var 8)) (Mon.var 8)) (Mon.var 8)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.cst 0)))))))))))))
        (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1088)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5)))) (Pol.mon (Mon.var 6))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 1024)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 10)) (Mon.var 0)) (Mon.var 2))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11))) (Mon.mul (Mon.var 9) (Mon.var 9))) (Mon.var 7)) (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2)))))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5)))) (Pol.mon (Mon.var 6)))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4096)) (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 11) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)) (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 9) (Mon.var 9)) (Mon.var 9)) (Mon.var 9)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 8) (Mon.var 8)) (Mon.var 8)) (Mon.var 8)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 5)) (Mon.var 5)) (Mon.var 5)))) (Pol.mon (Mon.var 6))))
        (by decide +kernel)] at r4
      refine Nat.le_trans ?_ r4
      show 1088 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * (t.kappa * t.kappa) * (t.dG + 2) * (t.W2 * t.W2) * (nearScale t L ie i * nearScale t L ie i) * 2 ^ i + 1024 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * (2 * a1 t L * t.kappa * t.W2 + 16 * (w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * rho2 t L * (t.Winf * t.Winf) * (L + 2)) * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i) + 4096 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t * cWd t * cWd t) * (tR t L * tR t L * tR t L * tR t L) * t.kappa * t.W2 * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i * nearScale t L ie i)
        ≤ 1088 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * (t.kappa * t.kappa) * (t.dG + 2) * (t.W2 * t.W2) * (nearScale t L ie i * nearScale t L ie i) * 2 ^ i + 1024 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * (tR t L * tR t L) * (2 * a1 t L * t.kappa * t.W2 + 16 * (w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t) * rho2 t L * (t.Winf * t.Winf) * (L + 2)) * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i) * 2 ^ i + 4096 * ((L + 2) * (L + 2)) * (w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t * w0 t) * (cWd t * cWd t * cWd t * cWd t) * (tR t L * tR t L * tR t L * tR t L) * t.kappa * t.W2 * (nearScale t L ie i * nearScale t L ie i * nearScale t L ie i * nearScale t L ie i) * 2 ^ i
      exact Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) (Nat.le_mul_of_pos_right _ hS))
        (Nat.le_mul_of_pos_right _ hS)
    exact leB_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (leB_ofNat hNn)
  have hKM := key_moments t.np ((jp t L ie i)) ru rv TT mq mu1 sf mD mD2 muQ muQ2 nuQ nuQ2 muY nuY nuD2 D N mXQ mZt
    mZq mZD mZD2 nuZD2 mZY nuZY mQD mQD2 mQ2D2 nuQD nuQD2 nuD T2 T3g T3l T4 Sd mQY mY nuQY
    nuAQY nuAY r1 r2 g2 X Y X2 Y2 Cu1 Cu2 CQ1 CQ2 CQQ2 (BPair.ofNat 1) (BPair.ofNat (2 ^ i))
    (BPair.ofNat 1) (BPair.ofNat (2 ^ ie)) (BPair.ofNat (48 * (4 + jp t L ie i)))
    (BPair.ofNat (nearScale t L ie i)) (BPair.ofNat t.kappa) (BPair.ofNat t.dG)
    (BPair.ofNat (w0 t)) (BPair.ofNat t.W2) (BPair.ofNat (t.Winf * t.Winf))
    (BPair.ofNat (c1 t)) (BPair.ofNat (rho1 t L)) (BPair.ofNat (rho2 t L))
    (BPair.ofNat (tR t L)) (BPair.ofNat (thetaR t L)) (BPair.ofNat (cOff t L))
    (BPair.ofNat (cqp t)) (BPair.ofNat (cq t L)) (BPair.ofNat t.Om) (BPair.ofNat (wq t))
    (BPair.ofNat (cD t)) (BPair.ofNat (cZ t L))
    (BPair.ofNat ((ppC t L).at (nearScale t L ie i))) (BPair.ofNat (pairClr t))
    (BPair.ofNat (2 * t.dth)) (BPair.ofNat (cWd t)) (BPair.ofNat (a1 t L)) (BPair.ofNat t.g)
    (BPair.ofNat L) (BPair.ofNat t.nl) (BPair.ofNat (qPlus t)) Del
    (BPair.ofNat (2 * cW t * kc t L ie i ^ exK t)) sn sd sn2 sd2 (BPair.ofNat 20)
    (BPair.ofNat (L * L + 2 * L + 2)) hn0 hs0 hns he hm1 hem hj hKn1 hKn2 hK hP hkappa1 hdG1
    hW0 hW20 hWinf2 hWinf hC1 hrho2 hTR hThR hcoff hcqp hcq hOm hg hL hnl ha1 hCW heWn heWd hc0
    hcc hCZ hPp hCD hQp hDel0 hvd1 hmu1 hmu1Del hD0 hsd0 hsd20 hsn hsn2 hmuQ hmuQ2 hmD0 hmQD0
    hmZD0 hnuQ0 hnuQ20 hX0 hY0 hX20 hY20 hru hTT hmq hfp hrv hN hXQ hZt hZq hsigp hsigm hsig2
    h3 h4 hQ hmuY hpQY hpQY' hpY hpY' hmn hnuD2 hnuQD hnuD hnuQ2 hnuQ hnuQD2 hnuZD2 hid1 hid2
    hidQ hidY hD hCS hF hsum hy hf hdef hr1 hX hY hr2 hg2 hX2 hY2 hZ hAQY hAY hSd hT2 hT3g hT4
    hZD hvth hAu1 hfaru1 hbitu1 hAu2 hfaru2 hbitu2 hAQ1 hfarQ1 hbitQ1 hAQ2 hfarQ2 hbitQ2 hAQQ2
    hfarQQ2 hbitQQ2 hD1 hD2 heta hR1 hR2 hR3 hR4
  have hPu : (BPair.ofNat (pairClr t) * (BPair.ofNat 24 * (BPair.ofNat (thetaR t L) * (BPair.ofNat (nearScale t L ie i) * BPair.ofNat (nearScale t L ie i))) + BPair.ofNat 3 * (BPair.ofNat (cD t) * BPair.ofNat t.np) + BPair.ofNat t.Om * (BPair.ofNat (cD t) * BPair.ofNat t.np)) + BPair.ofNat 2 * (BPair.ofNat (cq t L) * (BPair.ofNat (nearScale t L ie i) * BPair.ofNat (nearScale t L ie i))) + BPair.ofNat (wq t)).oneValue (BPair.ofNat ((puC t L).at (nearScale t L ie i))) :=
    BPair.oneValue_trans (BPair.oneValue_symm (Pol.ofNat_val [t.np, t.Om, nearScale t L ie i, thetaR t L, cq t L, wq t, cD t, pairClr t]
      (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 7)) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.cst 24) (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 2) (Mon.var 2))))) (Pol.mon (Mon.mul (Mon.cst 3) (Mon.mul (Mon.var 6) (Mon.var 0))))) (Pol.mon (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 6) (Mon.var 0)))))) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 4) (Mon.mul (Mon.var 2) (Mon.var 2)))))) (Pol.mon (Mon.var 5)))))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (puC_read t L (nearScale t L ie i)).symm))
  have hPv : (BPair.ofNat (pairClr t) * (BPair.ofNat 32 * (BPair.ofNat (nearScale t L ie i) * BPair.ofNat (rho2 t L) * BPair.ofNat t.nl * (BPair.ofNat L + BPair.ofNat 2)) + (BPair.ofNat 6 + BPair.ofNat t.Om) * BPair.ofNat (cZ t L) + BPair.ofNat 96 * (BPair.ofNat (thetaR t L) * (BPair.ofNat (nearScale t L ie i) * BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat t.dG))) + (BPair.ofNat 384 * (BPair.ofNat t.g * BPair.ofNat t.kappa) + BPair.ofNat 6 + BPair.ofNat t.Om) * BPair.ofNat ((ppC t L).at (nearScale t L ie i)) + BPair.ofNat 4 * (BPair.ofNat (cq t L) * (BPair.ofNat (nearScale t L ie i) * BPair.ofNat (nearScale t L ie i)) * (BPair.ofNat 1 + BPair.ofNat 2 * BPair.ofNat t.dG)) + BPair.ofNat (wq t)).oneValue (BPair.ofNat ((pvC t L).at (nearScale t L ie i))) :=
    BPair.oneValue_trans (BPair.oneValue_symm (Pol.ofNat_val [t.kappa, t.dG, t.Om, t.g, t.nl, L, nearScale t L ie i, rho2 t L, thetaR t L, cq t L, wq t, cZ t L, pairClr t, (ppC t L).at (nearScale t L ie i)]
      (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 12)) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 32)) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 7)) (Mon.var 4))) (Pol.add (Pol.mon (Mon.var 5)) (Pol.mon (Mon.cst 2))))) (Pol.mul (Pol.add (Pol.mon (Mon.cst 6)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 11)))) (Pol.mul (Pol.mon (Mon.cst 96)) (Pol.mul (Pol.mon (Mon.mul (Mon.var 8) (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1)))))))) (Pol.mul (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.cst 384) (Mon.mul (Mon.var 3) (Mon.var 0)))) (Pol.mon (Mon.cst 6))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 13)))) (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.mul (Pol.mon (Mon.mul (Mon.var 9) (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 1))))))) (Pol.mon (Mon.var 10)))))
      (BPair.oneValue_of_eq (congrArg BPair.ofNat (pvC_read t L (nearScale t L ie i)).symm))
  have hru' := leB_congr_right (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left hPu)))) hKM.1
  have hrv' := leB_congr_right (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left hPv)))) hKM.2
  exact tail_read t L ie fn fd i ru rv tp hLs hie hi hru' hrv'

end cornerkey
