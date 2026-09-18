import MassGap.Cornercert

/-!
`lem:cornerkey`'s key: at a floor pair the side, the mass and the scale
under which the chain's height sits below the floor at every further
scale, each the first member of its family at a stated comparison,
one bounded search per floor pair.

The key's list: a comparison is a polynomial in the near scale of
degree at most four at natural coefficients against a cap (`Poly4`
at the Horner read `ground.hread`, `Cmp`), read at a scale's second
member `S` and a near scale `K` as `P(K) ≤ c S` (`Cmp.read`, the
scale `[1 : S]`); the list's read is the fold over its members
(`listRead`).  A comparison holding at a scale holds at its half
past the clearing, the monomials' growth under two at
`ground.hread_grow` (`Cmp.read_half`, `listRead_half`), and holds at
the witness past the clearing, the halving count at or beyond `32`
and the list's reads summed, the fifth power under the halving from
`32` (`pow5_le_two_pow`, the step `(i + 1)^5 ≤ 2 i^5` from `i = 7`;
`Cmp.read_witness`, `listRead_witness`).

The near scale down the halving family at the stated member and
window data (`Tail`): the concentration key `kc`, the clearing
quotient of the cleared comparison (`ground.ceilAt`), the compared
pair's first member `pairNum` against its second `pairDen`, the bit
count `jp`, the least natural at or beyond one at `2^j` clearing the
pair, and the near scale `nearScale := 48 (4 + j') 2^{i_ε}` with the
growth pair: at most `b_K := 48 b 2^{i_ε}` per halving at `b := 2 +
2 (e + 1) e` (`nearScale_step`), monotone down the family
(`nearScale_mono`), the pair quadrupling per halving (`pairNum_quad`)
so that the bit count joined to the second member's bit count
`denBits` sits at or beyond twice the halving count (`jp_low`), and
the near scale clearing `6 b_K` from the `(3b + d)`-th halving on
(`nearScale_clear`).  The bit count read from the prior halving's
within the growth is the bit count (`jp_succ_read`), the chain
`bitWalk` its computing read (`bitWalk_eq`).
The key's reads at the
moment tier: the concentration key sits at or beyond the far read's
natural (`kc_ge_jK`) and clears the cleared comparison through the
falling products, the support weight's cap against the comparison's
second member's power at or below the Pascal count at the raised
key against the mass's power (`conc_key_read`); and the three bit
comparisons at the second power, the mass's second power against the
near mass's second member under the bit count's power at the member
read `dim G ≤ 32 d_θ #p (L + 2)`
(`bit_unit`), the mode square's against the compared pair's root
(`bit_mode`) and its square's (`bit_msq`).

The stated pairs at the key's side, each a natural read of the
member and window data (`thetaR`, `tR`, `rho1`, `rho2`, `c1`, `w0`,
`cD`, `cZ`, `cOff`, `cWd`, `a1`), and the pairs at one clearing
`2 κ² d_θ` (`pairClr`): `c'_q`, `c_q`, `W_q` (`cqp`, `cq`, `wq`) and the
polynomials `P'`, `P_u`, `P_v` in the near scale (`ppC`, `puC`, `pvC`),
the two scale pairs reading the cap block's groups (`puC_read`,
`pvC_read` against `excess_read` and `mode_read`).

The keys: the side key `sideKey`, the least side at or beyond one at
`1280 κ (L + 2) f_d < f_n (L² + 2L + 2)` (`sideRead`), holding at
every side at or beyond the witness `1280 κ f_d` (`sideRead_beyond`);
the mass key `massKey`, the least halving index at `4 g κ (192 C_D #p
+ 384 C_Z) f_d < f_n 4^i` (`massRead`), holding at every index at or
beyond the exponent itself (`massRead_beyond`); the key's list
`tailCmps` at the key's side, the scale comparison `4 (P_u + P_v) η <
φ` first, then the deficit cell, `η (dim G + 2) ≤ 1`, the remainder
cell and the corner cell's extent (`extent_read`, the read at the
squares' order), cleared at the pairs' second members with every cap
at or beyond one (`tailCaps`); and the scale key `tailKey`, the least
halving index at the list with the near scale's clearing
(`tailRead`), its witness the `(3b + d)`-th halving joined to `32`
and the list's reads summed (`tailWit`, `tailRead_witness`), the
comparison passing to the next halving (`tailRead_step`) and so
holding at every index at or beyond the key (`tailKey_all`), the key
least at the comparison both ways (`tailKey_least`, `tailKey_le`,
`tailKey_ge`), and the search walked with the bit count's chain its
computing read (`keyWalk`, `tailKeyC`, `tailKeyC_eq`).  The scale
comparison off the list's read is `tail_scale`, and the tail read
`tail_read` joins the three key comparisons, cast into the pair
carrier at `ground.Pol.ofNat_val`, to the excess and the mode read
at the scale through `key_quarters`: the reads' sum sits under the
floor's multiple of the scale.

The cap block, `lem:cornerkey`'s trial and mode member at their moments: the mode's variance read `mode_variance` (the
chi-square read at `dim G` degrees, cleared at the scale pair and the
profile's solve), the coordinate identity `coord_identity` (the parts
identity folded over the links and the generator index at the dual
weights), the excess read `excess_read` (the trial's form against
the floor line at the moments, the flux moments' fold read at the
gradient deficit against the deficits' fold) and the mode read
`mode_read` (the mode member's form at the moments, its scale reads'
coefficients collected at one group), each cleared at the scale
pair, the mass, the solve, the mode read and the stated pairs'
clearing (`c_q`, `W_q` and `P'` entering as their numerators at one
clearing `cc`, the tex's pairs at their second members), and the
key's quarters `key_quarters` (the excess and the mode read joined at
the cap, the three key comparisons putting the reads' sum under the
floor's multiple of the scale; the count read at the line beyond the
reads' sum is `momentfold.cap_line`'s, and the key itself, the side,
the mass and the scale at every floor pair, is the key below).
-/

namespace cornerkey
open ground elim inertia cornercert

/-- `lem:cornerkey`'s moment identities at the tail read: the parts
identity `m^X_{la} + s_n ν^G_{la} ≡ 1` folded over the generator
index and over the links reads the sum's unit, so each link's
moment fold joined to its leading member `c_l k_d K^T_l μ_Z`, the
link weight's multiple of the remainder and the generator's read of
`Z`, against the gradient fold's link read `c_l (ν^{ZG}_l +
ν^{ZR}_l)` collects, at the weighted folds `ν_Zyy` and `σ`, to the
four collected members against the leading members' own fold
`k_d σ μ_Z`. -/
theorem coord_identity (Lk A : Nat) (c KTu mZr mXZ nuZG nuZR : Nat → BPair)
    (mX nuG : Nat → Nat → BPair) (nuZyy sigma muZ sn kd : BPair)
    (h1 : ∀ l, l < Lk → (bsum (fun a => mX l a) (List.range A) + c l * kd * KTu l * muZ).oneValue
        (c l * (mZr l + mXZ l)))
    (h2 : ∀ l, l < Lk → (bsum (fun a => nuG l a) (List.range A)).oneValue
        (c l * (nuZG l + nuZR l)))
    (h3 : (bsum (fun l => c l * nuZG l) (List.range Lk)).oneValue nuZyy)
    (h4 : (bsum (fun l => c l * KTu l) (List.range Lk)).oneValue sigma)
    (h5 : ∀ l a, l < Lk → a < A → (mX l a + sn * nuG l a).oneValue BPair.unit) :
    (sn * nuZyy + bsum (fun l => c l * mZr l) (List.range Lk)
      + bsum (fun l => c l * mXZ l) (List.range Lk)
      + sn * bsum (fun l => c l * nuZR l) (List.range Lk)).oneValue (kd * sigma * muZ) := by
  -- the parts identity folded over the generator index, one link at a time
  have hInner : ∀ l, l < Lk →
      (bsum (fun a => mX l a) (List.range A)
        + sn * bsum (fun a => nuG l a) (List.range A)).oneValue BPair.unit := by
    intro l hl
    have hnull : (bsum (fun a => mX l a + sn * nuG l a) (List.range A)).oneValue BPair.unit :=
      foldB_nullRange (fun a => mX l a + sn * nuG l a) A (fun a ha => h5 l a hl ha)
    refine BPair.oneValue_trans (BPair.oneValue_symm ?_) hnull
    show (ground.famFold BPair.add BPair.unit (fun a => mX l a + sn * nuG l a)
      (List.range A)).oneValue _
    exact BPair.oneValue_trans
      (famFold_add_ov bpairFoldLaws (fun a => mX l a) (fun a => sn * nuG l a) (List.range A))
      (BPair.add_congr (BPair.oneValue_refl _)
        (foldB_mul_left sn (fun a => nuG l a) (List.range A)))
  -- the leading members' fold at the collected weights
  have hK : (bsum (fun l => c l * kd * KTu l * muZ) (List.range Lk)).oneValue
      (kd * sigma * muZ) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (foldB_mul_right muZ (fun l => c l * kd * KTu l) (List.range Lk))) ?_
    refine BPair.mul_congr_left ?_
    refine BPair.oneValue_trans (bsum_congr_range_ov _
      (fun l => kd * (c l * KTu l)) Lk (fun l _ => ?_)) ?_
    · rw [BPair.mul_comm (c l) kd, BPair.mul_assoc kd (c l) (KTu l)]
      exact BPair.oneValue_refl _
    · exact BPair.oneValue_trans (foldB_mul_left kd (fun l => c l * KTu l) (List.range Lk))
        (BPair.mul_congr (BPair.oneValue_refl kd) h4)
  -- each link's read at the moment and the gradient identities
  have hER : ∀ l, l < Lk →
      (bsum (fun a => mX l a) (List.range A)
        + sn * bsum (fun a => nuG l a) (List.range A)
        + c l * kd * KTu l * muZ).oneValue
      (sn * (c l * nuZG l) + c l * mZr l + c l * mXZ l + sn * (c l * nuZR l)) := by
    intro l hl
    rw [BPair.add_right_comm (bsum (fun a => mX l a) (List.range A))
      (sn * bsum (fun a => nuG l a) (List.range A)) (c l * kd * KTu l * muZ)]
    refine BPair.oneValue_trans
      (BPair.add_congr (h1 l hl) (BPair.mul_congr (BPair.oneValue_refl sn) (h2 l hl))) ?_
    exact polEqB [(c l), (mZr l), (mXZ l), sn, (nuZG l), (nuZR l)]
        (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 2)))) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 5))))))
        (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 0) (Mon.var 4)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 1)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 0) (Mon.var 5))))) (by decide +kernel)
  -- the links' fold at the leading members withdrawn
  have hE : (bsum (fun l => bsum (fun a => mX l a) (List.range A)
      + sn * bsum (fun a => nuG l a) (List.range A)
      + c l * kd * KTu l * muZ) (List.range Lk)).oneValue (kd * sigma * muZ) := by
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => bsum (fun a => mX l a) (List.range A)
        + sn * bsum (fun a => nuG l a) (List.range A))
      (fun l => c l * kd * KTu l * muZ) (List.range Lk)) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (foldB_nullRange _ Lk hInner) hK) ?_
    exact BPair.unit_add _
  -- the read side's fold splits at the four members
  have hRfold : (bsum (fun l => sn * (c l * nuZG l) + c l * mZr l + c l * mXZ l
      + sn * (c l * nuZR l)) (List.range Lk)).oneValue
      (sn * nuZyy + bsum (fun l => c l * mZr l) (List.range Lk)
        + bsum (fun l => c l * mXZ l) (List.range Lk)
        + sn * bsum (fun l => c l * nuZR l) (List.range Lk)) := by
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => sn * (c l * nuZG l) + c l * mZr l + c l * mXZ l)
      (fun l => sn * (c l * nuZR l)) (List.range Lk)) ?_
    refine BPair.add_congr ?_
      (foldB_mul_left sn (fun l => c l * nuZR l) (List.range Lk))
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => sn * (c l * nuZG l) + c l * mZr l)
      (fun l => c l * mXZ l) (List.range Lk)) ?_
    refine BPair.add_congr ?_ (BPair.oneValue_refl _)
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => sn * (c l * nuZG l)) (fun l => c l * mZr l) (List.range Lk)) ?_
    refine BPair.add_congr ?_ (BPair.oneValue_refl _)
    exact BPair.oneValue_trans (foldB_mul_left sn (fun l => c l * nuZG l) (List.range Lk))
      (BPair.mul_congr (BPair.oneValue_refl sn) h3)
  refine BPair.oneValue_trans (BPair.oneValue_symm hRfold) ?_
  exact BPair.oneValue_trans (BPair.oneValue_symm (bsum_congr_range_ov _ _ Lk hER)) hE

/-- `lem:cornerkey`'s excess: at the moment's read `r_u μ_1 ≡ T^T +
m_q` with the two members priced at the deficit caps, the flux
moments' fold read at the gradient deficit against the deficits' fold
(`lem:loopcap`'s `|f_p|² ≤ 2 κ δ_p` at every plaquette, folded at the
moments), the caps for `m_D` and `m_D2` entering their coefficient
data, every read cleared at the scale pair `[n : s]` (the scale's cube
at the squares' cap and the slack, its square at the deficit's square
moment and the scale itself at the first-order caps) and the mass
`[e : m]` (the mass's square at the leading summand), the stated
pairs `c_q` and `W_q` entering at their clearing `cc`, the slack's
read and the excess cleared at it, the moment `μ_1` withdrawn at its
strict read above the sum's unit and the scale's first member at or
below its second: the excess at the clearing `s³ m² cc` sits at or
below the leading summand `192 g κ C_D n_p e² n s² cc` joined to the
coefficient fold `(cc (24 Θ_R K² + 3 C_D n_p + Ω C_D n_p) + 2 c_q K² +
W_q) m² n² s`, `P_u`'s display at the clearing, the substituted
members' coefficients `g`, `κ`, `Θ_R`, `c_q`, `Ω`, `C_D`, `n_p` and
the clearing at or above the sum's unit as the substitutions' own
binders. -/
theorem excess_read (ru TT mq mu1 sf mD mD2 K ThR cq Om Wq CD np g kappa n s e m cc : BPair)
    (hru : (ru * mu1).oneValue (TT + mq))
    (hTT : TT * (m * m) * (s * s * s) ≤ BPair.ofNat 96 * (g * ((e * e) * sf)) * (s * s * s)
      + BPair.ofNat 12 * (ThR * mD2) * (m * m) * (s * s * s)
      + BPair.ofNat 3 * ((n * n) * mD) * (m * m) * s)
    (hmq : mq * (s * s * s) * cc ≤ cq * mD2 * (s * s * s) + cc * (n * Om * mD * (s * s))
      + Wq * (n * n) * mu1 * s)
    (hfp : sf ≤ BPair.ofNat 2 * kappa * mD)
    (hmD : mD * s ≤ CD * np * n * mu1)
    (hmD2 : mD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * mu1)
    (hmu : BPair.unit < mu1) (hns : n ≤ s)
    (hn : BPair.unit ≤ n) (hs : BPair.unit ≤ s) (he : BPair.unit ≤ e) (hm : BPair.unit ≤ m)
    (hg : BPair.unit ≤ g) (hkappa : BPair.unit ≤ kappa) (hThR : BPair.unit ≤ ThR)
    (hcq : BPair.unit ≤ cq) (hOm : BPair.unit ≤ Om) (hCD : BPair.unit ≤ CD)
    (hnp : BPair.unit ≤ np) (hcc : BPair.unit ≤ cc) :
    ru * (s * s * s) * (m * m) * cc
      ≤ BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s) * cc
        + (cc * (BPair.ofNat 24 * (ThR * (K * K)) + BPair.ofNat 3 * (CD * np) + Om * (CD * np))
          + BPair.ofNat 2 * (cq * (K * K)) + Wq) * (m * m) * (n * n) * s := by
  have hmu1 : BPair.unit ≤ mu1 := leB_of_lt hmu
  have hpos2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  -- the flux moments' fold at the gradient deficit against the deficits' fold
  have hsf : sf * s ≤ BPair.ofNat 2 * kappa * (CD * np * n * mu1) :=
    leB_trans (leB_mulL hs hfp)
      (leB_congr_left (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm)
        (leB_mulR (unitLeMul hpos2 hkappa) hmD))
  -- the three cap members at the moments
  have b1 : BPair.ofNat 96 * (g * ((e * e) * sf)) * (s * s * s) * cc
      ≤ mu1 * BPair.ofNat 192 * g * kappa * CD * np * e * e * n * s * s * cc := by
    have t := leB_mulL (unitLeMul (unitLeMul hs hs) hcc)
      (leB_mulR (unitLeMul (unitLeMul (unitLeOfNat 96) hg) (unitLeMul he he)) hsf)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_refl _) ?_ t
    exact polEqB [g, e, kappa, CD, np, n, mu1, s, cc]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 96) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.cst 192)) (Mon.var 0)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 1)) (Mon.var 1)) (Mon.var 5)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8))) (by decide +kernel)
  have b2 : BPair.ofNat 12 * (ThR * mD2) * (m * m) * (s * s * s) * cc
      ≤ mu1 * cc * BPair.ofNat 24 * ThR * K * K * m * m * n * n * s := by
    have t := leB_mulL (unitLeMul (unitLeMul (unitLeMul hm hm) hs) hcc)
      (leB_mulR (unitLeMul (unitLeOfNat 12) hThR) hmD2)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · exact polEqB [ThR, mD2, s, m, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 12) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 2)) (Mon.var 4)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 12) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.var 3)) (Mon.var 2)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel)
    · exact polEqB [ThR, K, n, mu1, m, s, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 12) (Mon.var 0)) (Mon.cst 2)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 6)) (Mon.cst 24)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 4)) (Mon.var 4)) (Mon.var 2)) (Mon.var 2)) (Mon.var 5))) (by decide +kernel)
  have b3 : BPair.ofNat 3 * ((n * n) * mD) * (m * m) * s * cc
      ≤ mu1 * cc * BPair.ofNat 3 * CD * np * m * m * n * n * s := by
    have t := leB_mulL (unitLeMul (unitLeMul hm hm) hcc)
      (leB_mulR (unitLeMul (unitLeOfNat 3) (unitLeMul hn hn)) hmD)
    have t3 := leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeMul (unitLeOfNat 3) hCD) hnp) hm) hm) hn) hn) hmu1) hcc) hns
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc] at t3
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left (BPair.oneValue_of_eq ?_) t)
      (leB_congr ?_ ?_ t3)
    · rw [BPair.mul_right_comm (BPair.ofNat 3 * n * n * mD) s m,
        BPair.mul_right_comm (BPair.ofNat 3 * n * n * mD * m) s m]
    · exact polEqB [n, CD, np, m, mu1, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 3)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 3) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 4)) (Mon.var 3)) (Mon.var 3)) (Mon.var 5))) (by decide +kernel)
    · exact polEqB [s, CD, np, m, n, mu1, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 3)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 6)) (Mon.cst 3)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 0))) (by decide +kernel)
  -- the slack's three members at the moments
  have c1 : cq * mD2 * (s * s * s) * (m * m)
      ≤ mu1 * BPair.ofNat 2 * cq * K * K * m * m * n * n * s := by
    have t := leB_mulL (unitLeMul hs (unitLeMul hm hm)) (leB_mulR hcq hmD2)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_refl _) ?_ t
    exact polEqB [cq, K, n, mu1, s, m]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.cst 2)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 5)) (Mon.var 5)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4))) (by decide +kernel)
  have c2 : cc * (n * Om * mD * (s * s)) * (m * m)
      ≤ mu1 * cc * Om * CD * np * m * m * n * n * s := by
    have t := leB_mulL (unitLeMul hs (unitLeMul (unitLeMul hm hm) hcc)) (leB_mulR (unitLeMul hn hOm) hmD)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · exact polEqB [n, Om, mD, s, m, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4))) (by decide +kernel)
    · exact polEqB [n, Om, CD, np, mu1, s, m, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 7)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 6)) (Mon.var 6)) (Mon.var 0)) (Mon.var 0)) (Mon.var 5))) (by decide +kernel)
  have hWq : (Wq * (n * n) * mu1 * s * (m * m)).oneValue
      (mu1 * Wq * m * m * n * n * s) :=
    polEqB [Wq, n, mu1, s, m]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.var 4) (Mon.var 4))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 0)) (Mon.var 4)) (Mon.var 4)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3))) (by decide +kernel)
  have hmq2 : mq * (s * s * s) * cc * (m * m) ≤ cq * mD2 * (s * s * s) * (m * m)
      + cc * (n * Om * mD * (s * s)) * (m * m) + Wq * (n * n) * mu1 * s * (m * m) := by
    have t := leB_mulL (unitLeMul hm hm) hmq
    rw [BPair.right_distrib, BPair.right_distrib] at t
    exact t
  have hTT2 : TT * (m * m) * (s * s * s) * cc ≤ BPair.ofNat 96 * (g * ((e * e) * sf)) * (s * s * s) * cc
      + BPair.ofNat 12 * (ThR * mD2) * (m * m) * (s * s * s) * cc
      + BPair.ofNat 3 * ((n * n) * mD) * (m * m) * s * cc := by
    have t := leB_mulL hcc hTT
    rw [BPair.right_distrib, BPair.right_distrib] at t
    exact t
  -- the moment's clearing on both sides
  have hL : (mu1 * (ru * (s * s * s) * (m * m) * cc)).oneValue
      (TT * (m * m) * (s * s * s) * cc + mq * (s * s * s) * cc * (m * m)) := by
    refine BPair.oneValue_trans (polEqB [mu1, ru, s, m, cc]
        (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2))) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 0)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 2)) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4)))) (by decide +kernel)) (?_ : (ru * mu1 * (s * s * s * (m * m) * cc)).oneValue (TT * (m * m) * (s * s * s) * cc + mq * (s * s * s) * cc * (m * m)))
    refine BPair.oneValue_trans (BPair.mul_congr_left hru) ?_
    rw [BPair.right_distrib]
    refine BPair.add_congr ?_ (BPair.oneValue_of_eq ?_)
    · exact polEqB [TT, s, m, cc]
          (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 3))))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 1))) (Mon.var 3))) (by decide +kernel)
    · repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (mq * s * s * s * m) m cc,
        BPair.mul_right_comm (mq * s * s * s) m cc]
  have hR : (mu1 * (BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s) * cc + (cc
      * (BPair.ofNat 24 * (ThR * (K * K)) + BPair.ofNat 3 * (CD * np) + Om * (CD * np)) +
      BPair.ofNat 2 * (cq * (K * K)) + Wq) * (m * m) * (n * n) * s)).oneValue (mu1 * BPair.ofNat 192
      * g * kappa * CD * np * e * e * n * s * s * cc + mu1 * cc * BPair.ofNat 24 * ThR * K * K *
      m * m * n * n * s + mu1 * cc * BPair.ofNat 3 * CD * np * m * m * n * n * s + (mu1 *
      BPair.ofNat 2 * cq * K * K * m * m * n * n * s + mu1 * cc * Om * CD * np * m * m * n * n *
      s + mu1 * Wq * m * m * n * n * s)) :=
    polEqB [mu1, g, kappa, CD, np, e, n, s, cc, ThR, K, Om, cq, Wq, m]
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 192) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.mul (Mon.var 3) (Mon.var 4)))) (Mon.mul (Mon.var 5) (Mon.var 5))) (Mon.var 6)) (Mon.mul (Mon.var 7) (Mon.var 7))) (Mon.var 8))) (Pol.mul (Pol.mul (Pol.mul (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 8)) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.cst 24) (Mon.mul (Mon.var 9) (Mon.mul (Mon.var 10) (Mon.var 10))))) (Pol.mon (Mon.mul (Mon.cst 3) (Mon.mul (Mon.var 3) (Mon.var 4))))) (Pol.mon (Mon.mul (Mon.var 11) (Mon.mul (Mon.var 3) (Mon.var 4)))))) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 12) (Mon.mul (Mon.var 10) (Mon.var 10)))))) (Pol.mon (Mon.var 13))) (Pol.mon (Mon.mul (Mon.var 14) (Mon.var 14)))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 6)))) (Pol.mon (Mon.var 7)))))
        (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 192)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)) (Mon.var 8))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 8)) (Mon.cst 24)) (Mon.var 9)) (Mon.var 10)) (Mon.var 10)) (Mon.var 14)) (Mon.var 14)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 8)) (Mon.cst 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 14)) (Mon.var 14)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))) (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.var 12)) (Mon.var 10)) (Mon.var 10)) (Mon.var 14)) (Mon.var 14)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 8)) (Mon.var 11)) (Mon.var 3)) (Mon.var 4)) (Mon.var 14)) (Mon.var 14)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 13)) (Mon.var 14)) (Mon.var 14)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7))))) (by decide +kernel)
  refine leB_unscale_left hmu ?_
  refine leB_congr (BPair.oneValue_symm hL) (BPair.oneValue_symm hR) ?_
  exact leB_add (leB_trans hTT2 (leB_add (leB_add b1 b2) b3))
    (leB_trans hmq2 (leB_add (leB_add c1 c2)
      (leB_congr_right hWq (leB_refl _))))

/-- The mode's variance read (`lem:cornerkey`'s mode member, the
chi-square read at `dim G` degrees), cleared at the scale `[n : s]`
and the profile's solve `[sn : sd]`: at the coordinate identity's
two reads, the mode square's moment at the solve against the unit's
and the square's square's against the mode square's, the mode mean
below its moment read and the profile's two reads a scale apart,
the member's self-pairing, the mode's variance cleared at the unit's
moment, sits at or beyond the scale's multiple of the solve against
the two moments at the gap `1 - η (dim G + 2) / 4`, less half the
scale's multiple of the remainders' caps, the mode mean's at the
first and the unit's at the second, every read cleared at four, the
scale's square and the solve's clearing. -/
theorem mode_variance (muQ muQ2 nuQ nuQ2 mu1 K dG n s sn sd r1 r2 R1 R2 : BPair)
    (h1 : (BPair.ofNat 2 * nuQ * s * sd).oneValue (n * (K * dG * sn * mu1 + r1 * sd)))
    (h2 : (BPair.ofNat 2 * nuQ2 * s * sd).oneValue
      (n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd)))
    (h3 : muQ ≤ nuQ)
    (h4 : BPair.ofNat 2 * nuQ2 * s ≤ BPair.ofNat 2 * muQ2 * s + n * nuQ2)
    (hr1 : r1 ≤ R1) (hr2 : r2.swap ≤ R2)
    (hns : n ≤ s) (hn : BPair.unit ≤ n) (hs : BPair.unit ≤ s) (hsd : BPair.unit ≤ sd)
    (hmu1 : BPair.unit ≤ mu1) (hmuQ : BPair.unit ≤ muQ)
    (hR2 : BPair.unit ≤ R2) :
    BPair.ofNat 4 * n * K * sn * muQ * mu1 * s + BPair.ofNat 4 * muQ * muQ * s * s * sd
      ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd
        + n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1
        + BPair.ofNat 2 * n * s * R2 * sd * mu1 + BPair.ofNat 2 * n * muQ * R1 * sd * s := by
  have h22 : (BPair.ofNat 4).oneValue (BPair.ofNat 2 * BPair.ofNat 2) := BPair.ofNat_mul 2 2
  have hpos2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  -- S1: 4 μQ μQ s s sd ≤ 2 n K dG sn μQ μ1 s + 2 n μQ R1 sd s
  have s1 : BPair.ofNat 4 * muQ * muQ * s * s * sd
      ≤ BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 * s + BPair.ofNat 2 * n * muQ * R1 * sd * s := by
    have a1 : BPair.ofNat 4 * muQ * muQ * s * sd ≤ BPair.ofNat 2 * muQ * (BPair.ofNat 2 * nuQ * s * sd) := by
      have hm : BPair.ofNat 2 * muQ * (BPair.ofNat 2 * muQ * s * sd)
          = BPair.ofNat 2 * BPair.ofNat 2 * muQ * muQ * s * sd := by
        repeat rw [← BPair.mul_assoc]
        rw [BPair.mul_right_comm (BPair.ofNat 2) muQ (BPair.ofNat 2)]
      refine leB_congr_left (BPair.oneValue_trans (BPair.oneValue_of_eq hm)
        (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left
          (BPair.mul_congr_left (BPair.oneValue_symm h22)))))) ?_
      exact leB_mulR (unitLeMul hpos2 hmuQ) (leB_mulL hsd (leB_mulL hs (leB_mulR hpos2 h3)))
    have hm2 : (BPair.ofNat 2 * muQ * (n * (K * dG * sn * mu1 + r1 * sd))).oneValue
        (BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 + BPair.ofNat 2 * n * muQ * r1 * sd) :=
      polEqB [muQ, n, K, dG, sn, mu1, r1, sd]
          (Pol.mul (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.var 6) (Mon.var 7))))))
          (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 0)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 0)) (Mon.var 6)) (Mon.var 7)))) (by decide +kernel)
    have a2 : BPair.ofNat 2 * muQ * (BPair.ofNat 2 * nuQ * s * sd)
        ≤ BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 + BPair.ofNat 2 * n * muQ * R1 * sd :=
      leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) h1) hm2))
        (leB_add (leB_refl _) (leB_mulL hsd (leB_mulR (unitLeMul (unitLeMul hpos2 hn) hmuQ) hr1)))
    have a3 := leB_mulL hs (leB_trans a1 a2)
    rw [BPair.right_distrib] at a3
    exact leB_congr_left (BPair.oneValue_of_eq (BPair.mul_right_comm (BPair.ofNat 4 * muQ * muQ * s) sd s)) a3
  -- S2: 2 n B' μ1 s ≤ 4 μQ2 μ1 s s sd + n n B' μ1 at B' := K (dG+2) sn μQ + r2 sd
  have s2 : BPair.ofNat 2 * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1 * s
      ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd
        + n * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1 := by
    have b1 := leB_mulL (unitLeMul (unitLeMul (unitLeMul hpos2 hmu1) hsd) hs) h4
    rw [BPair.right_distrib] at b1
    have b1 : BPair.ofNat 2 * nuQ2 * s * sd * (BPair.ofNat 2 * mu1 * s) ≤ BPair.ofNat 2 *
        BPair.ofNat 2 * muQ2 * mu1 * s * s * sd + n * (BPair.ofNat 2 * nuQ2 * s * sd) * mu1 :=
      leB_congr (polEqB [nuQ2, s, mu1, sd]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3)) (Mon.var 1))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 3)) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 1)))) (by decide +kernel))
        (polEqB [muQ2, s, mu1, sd, n, nuQ2]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 5)) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)))))
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.cst 2)) (Mon.var 0)) (Mon.var 2)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 4) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 5)) (Mon.var 1)) (Mon.var 3))) (Mon.var 2)))) (by decide +kernel)) b1
    refine leB_congr_right (BPair.add_congr (BPair.mul_congr_left (BPair.mul_congr_left
      (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left
        (BPair.oneValue_symm h22)))))) ?_) (leB_congr_left ?_ b1)
    · exact BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr (BPair.oneValue_refl n) h2)
        (BPair.oneValue_refl mu1)) (BPair.oneValue_of_eq (by rw [← BPair.mul_assoc n n]))
    · refine BPair.oneValue_trans (BPair.mul_congr h2 (BPair.oneValue_refl _))
        (BPair.oneValue_of_eq ?_)
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm n _ (BPair.ofNat 2), BPair.mul_comm n (BPair.ofNat 2)]
  -- the B' terms opened
  have hL : BPair.ofNat 4 * n * K * sn * muQ * mu1 * s + BPair.ofNat 4 * muQ * muQ * s * s * sd
      ≤ BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
        + BPair.ofNat 2 * n * muQ * R1 * sd * s := by
    refine leB_trans (leB_add (leB_refl _) s1) ?_
    refine leB_congr (BPair.oneValue_refl _)
      (polEqB [n, K, dG, sn, muQ, mu1, s, R1, sd]
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 4)) (Mon.var 7)) (Mon.var 8)) (Mon.var 6))))
        (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 4)) (Mon.var 7)) (Mon.var 8)) (Mon.var 6)))) (by decide +kernel)) (?_ : BPair.ofNat 4 * n * K * sn * muQ * mu1 * s + (BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 * s + BPair.ofNat 2 * n * muQ * R1 * sd * s) ≤ BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 * s + BPair.ofNat 2 * n * K * BPair.ofNat 2 * sn * muQ * mu1 * s + BPair.ofNat 2 * n * muQ * R1 * sd * s)
    refine leB_congr_right ?_ (leB_refl _)
    exact polEqB [n, K, sn, muQ, mu1, s, dG, R1, sd]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 6)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 3)) (Mon.var 7)) (Mon.var 8)) (Mon.var 5)))))
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.var 6)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.cst 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 3)) (Mon.var 7)) (Mon.var 8)) (Mon.var 5)))) (by decide +kernel)
  -- the second identity opened: the leading read with the remainder's scale
  -- multiple at or below the square's moment with the remainder's square-scale read
  have s2' : BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
        + BPair.ofNat 2 * n * r2 * sd * mu1 * s
      ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd + n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1
        + n * n * r2 * sd * mu1 := by
    have t := s2
    have t : BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s + BPair.ofNat 2 *
        n * r2 * sd * mu1 * s ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd + n * n * K * (dG +
        BPair.ofNat 2) * sn * muQ * mu1 + n * n * r2 * sd * mu1 :=
      leB_congr (polEqB [n, K, dG, sn, muQ, r2, sd, mu1, s]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 0))) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 6))))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 8)))
        (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)))) (by decide +kernel))
        (polEqB [muQ2, mu1, s, sd, n, K, dG, sn, muQ, r2]
        (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 4))) (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 5)) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.mul (Mon.var 9) (Mon.var 3))))) (Pol.mon (Mon.var 1))))
        (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 5))) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.var 1)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.var 4)) (Mon.var 9)) (Mon.var 3)) (Mon.var 1)))) (by decide +kernel)) t
    exact t
  -- the scale's gap: the first member at or below twice the second
  have h2s : n ≤ BPair.ofNat 2 * s :=
    leB_trans hns (leB_congr_right (BPair.oneValue_symm (BPair.ofNat_two_mul s))
      (leB_congr_left (BPair.unit_add s) (leB_add hs (leB_refl s))))
  have hT : BPair.unit ≤ BPair.ofNat 2 * s + n.swap := leB_unit_add (V := n.swap) h2s
  have hsum : (BPair.ofNat 2 * s).oneValue (n + (BPair.ofNat 2 * s + n.swap)) :=
    BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm n (BPair.ofNat 2 * s + n.swap)))
      (BPair.add_swap_self (BPair.ofNat 2 * s) n))
  -- the remainder's two reads join at the gap's multiple of its partner, capped
  have core : n * r2 + (BPair.ofNat 2 * s * r2).swap ≤ BPair.ofNat 2 * s * R2 := by
    have step1 : (n * r2 + (BPair.ofNat 2 * s * r2).swap).oneValue
        (n * r2 + (n * r2.swap + (BPair.ofNat 2 * s + n.swap) * r2.swap)) := by
      rw [← BPair.mul_swap]
      refine BPair.add_congr (BPair.oneValue_refl _) ?_
      refine BPair.oneValue_trans (BPair.mul_congr_left hsum) (BPair.oneValue_of_eq ?_)
      rw [BPair.right_distrib]
    have step2 : (n * r2 + (n * r2.swap + (BPair.ofNat 2 * s + n.swap) * r2.swap)).oneValue
        ((BPair.ofNat 2 * s + n.swap) * r2.swap) := by
      rw [← BPair.add_assoc, ← BPair.left_distrib]
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl n) (BPair.add_swap_null r2)) (BPair.mul_unit n))
        (BPair.oneValue_refl _)) (BPair.unit_add _)
    have step3 : (BPair.ofNat 2 * s + n.swap) * r2.swap ≤ BPair.ofNat 2 * s * R2 := by
      refine leB_trans (leB_mulR hT hr2) ?_
      rw [BPair.right_distrib, BPair.swap_mul]
      refine leB_congr_right (BPair.add_unit _) (leB_add (leB_refl _) (leUnitOfSwap ?_))
      exact unitLeMul hn hR2
    exact leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans step1 step2)) step3
  have f1 : n * n * r2 * sd * mu1 + (BPair.ofNat 2 * n * r2 * sd * mu1 * s).swap
      ≤ BPair.ofNat 2 * n * s * R2 * sd * mu1 := by
    have hX : BPair.unit ≤ n * sd * mu1 := unitLeMul (unitLeMul hn hsd) hmu1
    have t := leB_mulL hX core
    rw [BPair.right_distrib, BPair.swap_mul] at t
    refine leB_congr (BPair.add_congr (BPair.oneValue_of_eq ?_)
      (swap_congr ?_)) (BPair.oneValue_of_eq ?_) t
    · repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (n) r2 n]
    · exact polEqB [s, r2, n, sd, mu1]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 1)) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 4))))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 0))) (by decide +kernel)
    · repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (BPair.ofNat 2 * s) R2 n,
        BPair.mul_right_comm (BPair.ofNat 2) s n]
  -- the leading read crosses the second remainder to the upper side
  have hR2 : BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
      ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd + n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1
        + BPair.ofNat 2 * n * s * R2 * sd * mu1 := by
    have t := leB_swapL (Y := (BPair.ofNat 2 * n * r2 * sd * mu1 * s).swap) s2'
    refine leB_trans t ?_
    rw [BPair.add_assoc (BPair.ofNat 4 * muQ2 * mu1 * s * s * sd
      + n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1) (n * n * r2 * sd * mu1)]
    exact leB_add (leB_refl _) f1
  exact leB_trans hL (leB_add hR2 (leB_refl _))

/-- The mode read (`lem:cornerkey`'s mode member): the member's form
against the floor line reads the squares' cap at the mode weight,
the slack at the mode weight and the mode read at the closed sums,
each at the two deficit moments at the mode weight (`μ[ZD]` at the
side pair `C_Z` with the near-scale pair `P'`, `μ[ZD²]` at the near
scale's square against `1 + 2 dim G`) and the mode square's deficit
moment at the near scale, against the variance read on the cell, the
variance at or beyond half its leading member, and at the profile's
solve floored at the roots' floor `|W|² [2 : L + 2]`; every read
cleared at the scale pair `[n : s]`, the mass `[e : m]` at or below
one, the profile's solve `[sn : sd]` and the mode read `[eWn : eWd]`,
the stated pairs `c_q`, `W_q` and `P'` at their clearing `cc`, the
scale's first member at or below its second: the excess per gram at
the clearing `s² m² eWd cc` sits at or below the mode's frequency
read at the side, `16 κ (L + 2) eWn n s m² cc`, the mass gradient's
read at the mode weight's deficit moment, `384 g κ C_Z e² n s eWd
cc`, and the scale reads' one group at `m² n² eWd`, `P_v`'s display
at the clearing: the mode square's deficit term `32 K ϱ₂ n_ℓ (L + 2)`,
the mass gradient's near-scale member `384 g κ P'` joined to the
further `P'` reads at `6 + Ω`, the side pair at `6 + Ω`, the caps
`(96 Θ_R + 4 c_q)(1 + 2 dim G) K²` and `W_q`, every cap displayed,
the mass's square read through one at the near-scale member. -/
theorem mode_read (rv D N mXQ mZt mZq mZD mZD2 mQD muQ K n s e m g kappa CZ ThR cq Om Wq
    Pp dG eWn eWd W2 Winf2 sn sd L nl rho2 cc : BPair)
    (hrv : (rv * D).oneValue N)
    (hN : N * (s * s) ≤ BPair.ofNat 2 * (n * n) * mXQ + BPair.ofNat 2 * mZt * (s * s)
      + mZq * (s * s))
    (hXQ : mXQ * eWd ≤ BPair.ofNat 8 * (kappa * kappa) * eWn * W2 * muQ
      + BPair.ofNat 8 * rho2 * nl * Winf2 * mQD * eWd)
    (hQD : mQD * s ≤ BPair.ofNat 2 * K * n * muQ)
    (hZt : mZt * (m * m) * (s * s) ≤ BPair.ofNat 192 * (g * kappa * (e * e) * mZD) * (s * s)
      + BPair.ofNat 12 * (ThR * mZD2) * (m * m) * (s * s)
      + BPair.ofNat 3 * (n * n * mZD) * (m * m))
    (hZq : mZq * (s * s) * cc ≤ cq * mZD2 * (s * s) + cc * (n * Om * mZD * s) + Wq * (n * n) * D)
    (hZD : mZD * (s * s) * cc ≤ (CZ * n * s * cc + Pp * (n * n)) * D)
    (hZD2 : mZD2 * (s * s)
      ≤ BPair.ofNat 4 * (K * K) * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * (n * n) * D)
    (hD : n * kappa * sn * muQ ≤ D * s * (BPair.ofNat 2 * sd))
    (hsig : W2 * (BPair.ofNat 2 * sd) ≤ sn * (L + BPair.ofNat 2))
    (hWinf : Winf2 ≤ W2) (hem : e ≤ m)
    (hD0 : BPair.unit < D) (hs0 : BPair.unit < s) (hns : n ≤ s)
    (hn : BPair.unit ≤ n) (he : BPair.unit ≤ e) (hm : BPair.unit ≤ m)
    (hkappa : BPair.ofNat 1 ≤ kappa)
    (hg : BPair.unit ≤ g) (hThR : BPair.unit ≤ ThR) (hcq : BPair.unit ≤ cq)
    (hOm : BPair.unit ≤ Om) (hPp : BPair.unit ≤ Pp)
    (heWn : BPair.unit ≤ eWn) (heWd : BPair.unit ≤ eWd) (hW2 : BPair.unit ≤ W2)
    (hsd0 : BPair.unit < sd) (hL : BPair.unit ≤ L) (hnl : BPair.unit ≤ nl)
    (hrho2 : BPair.unit ≤ rho2) (hCZ : BPair.unit ≤ CZ)
    (hK : BPair.unit ≤ K) (hmuQ : BPair.unit ≤ muQ) (hmQD : BPair.unit ≤ mQD)
    (hcc : BPair.unit ≤ cc) :
    rv * (s * s) * (m * m) * eWd * cc
      ≤ BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * (m * m) * cc
        + BPair.ofNat 384 * (g * kappa * CZ) * (e * e) * n * s * eWd * cc
        + (cc * (BPair.ofNat 32 * (K * rho2 * nl * (L + BPair.ofNat 2))
            + (BPair.ofNat 6 + Om) * CZ
            + BPair.ofNat 96 * (ThR * (K * K) * (BPair.ofNat 1 + BPair.ofNat 2 * dG)))
          + (BPair.ofNat 384 * (g * kappa) + BPair.ofNat 6 + Om) * Pp
          + BPair.ofNat 4 * (cq * (K * K) * (BPair.ofNat 1 + BPair.ofNat 2 * dG)) + Wq)
          * (m * m) * (n * n) * eWd := by
  have hpos2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  have hkap : BPair.unit ≤ kappa := leB_trans (unitLeOfNat 1) hkappa
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hL2 : BPair.unit ≤ L + BPair.ofNat 2 := unitLeAdd hL hpos2
  have hD1 : BPair.unit ≤ D := leB_of_lt hD0
  have hc0 : BPair.unit < D * (s * s) := unitLtMul hD0 (unitLtMul hs0 hs0)
  have hEM : e * e ≤ m * m := leB_mul_mono he hm hem hem
  -- the flux read at the solve's floor: W2 n κ μQ ≤ (L + 2) D s
  have hcoreK : W2 * n * kappa * muQ ≤ (L + BPair.ofNat 2) * D * s := by
    have c1 : W2 * (BPair.ofNat 2 * sd) * (n * kappa * muQ)
        ≤ sn * (L + BPair.ofNat 2) * (n * kappa * muQ) :=
      leB_mulL (unitLeMul (unitLeMul hn hkap) hmuQ) hsig
    have c2 : (L + BPair.ofNat 2) * (n * kappa * sn * muQ)
        ≤ (L + BPair.ofNat 2) * (D * s * (BPair.ofNat 2 * sd)) := leB_mulR hL2 hD
    have c1 : W2 * (BPair.ofNat 2 * sd) * (n * kappa * muQ) ≤ (L + BPair.ofNat 2) * (n * kappa *
        sn * muQ) :=
      leB_congr (BPair.oneValue_refl _)
        (polEqB [sn, L, n, kappa, muQ]
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 4))))
        (Pol.mul (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 0)) (Mon.var 4)))) (by decide +kernel)) c1
    have c3 := leB_trans c1 c2
    have c3 : W2 * n * kappa * muQ * (BPair.ofNat 2 * sd) ≤ (L + BPair.ofNat 2) * D * s *
        (BPair.ofNat 2 * sd) :=
      leB_congr (polEqB [W2, sd, n, kappa, muQ]
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.cst 2) (Mon.var 1))) (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 4))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.mul (Mon.cst 2) (Mon.var 1)))) (by decide +kernel))
        (polEqB [L, D, s, sd]
        (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.mul (Mon.cst 2) (Mon.var 3)))))
        (Pol.mul (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 3)))) (by decide +kernel)) c3
    exact leB_unscale (unitLtMul (unitLtNat (by decide)) hsd0) c3
  have hcore : W2 * n * muQ ≤ (L + BPair.ofNat 2) * D * s :=
    leB_trans (leB_congr_left (BPair.mul_ofNat_one (W2 * n * muQ))
      (leB_congr_right (BPair.oneValue_of_eq (BPair.mul_right_comm (W2 * n) muQ kappa))
        (leB_mulR (unitLeMul (unitLeMul hW2 hn) hmuQ) hkappa))) hcoreK
  -- the leading term
  have hA1 : BPair.ofNat 2 * (n * n) * (s * s * (m * m)) * cc
        * (BPair.ofNat 8 * (kappa * kappa) * eWn * W2 * muQ)
      ≤ BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * m * m * cc * D * s * s := by
    have hM : BPair.unit ≤ BPair.ofNat 16 * kappa * eWn * n * s * m * m * s * cc :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
        (unitLeOfNat 16) hkap) heWn) hn) hs) hm) hm) hs) hcc
    have t := leB_mulR hM hcoreK
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · exact polEqB [kappa, eWn, n, s, m, cc, W2, muQ]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 3)) (Mon.var 5)) (Mon.var 6)) (Mon.var 2)) (Mon.var 0)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 8)) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 6)) (Mon.var 7))) (by decide +kernel)
    · exact polEqB [kappa, eWn, n, s, m, cc, L, D]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 16) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 3)) (Mon.var 5))) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 3)))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.var 0))) (Pol.add (Pol.mon (Mon.var 6)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 3))) (by decide +kernel)
  -- the mode square's deficit term
  have hA2 : BPair.ofNat 2 * (n * n) * (s * s * (m * m)) * cc
        * (BPair.ofNat 8 * rho2 * nl * Winf2 * mQD * eWd)
      ≤ cc * BPair.ofNat 32 * K * rho2 * nl * (L + BPair.ofNat 2) * m * m * n * n * eWd
          * D * s * s := by
    have hY : BPair.unit ≤ BPair.ofNat 2 * (n * n) * (s * s * (m * m)) * cc :=
      unitLeMul (unitLeMul (unitLeMul hpos2 (unitLeMul hn hn))
        (unitLeMul (unitLeMul hs hs) (unitLeMul hm hm))) hcc
    have u1 := leB_mulR hY
      (leB_mulL heWd (leB_mulL hmQD (leB_mulR (unitLeMul (unitLeMul (unitLeOfNat 8) hrho2) hnl) hWinf)))
    have hX : BPair.unit ≤ BPair.ofNat 2 * (n * n) * (s * (m * m)) * cc
        * (BPair.ofNat 8 * rho2 * nl * W2 * eWd) :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul hpos2 (unitLeMul hn hn)) (unitLeMul hs (unitLeMul hm hm))) hcc)
        (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 8) hrho2) hnl) hW2) heWd)
    have u2 := leB_mulR hX hQD
    have hM : BPair.unit ≤ BPair.ofNat 32 * K * rho2 * nl * m * m * n * n * eWd * s * cc :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
        (unitLeMul (unitLeMul (unitLeOfNat 32) hK) hrho2) hnl) hm) hm) hn) hn) heWd) hs) hcc
    have t := leB_mulR hM hcore
    repeat rw [← BPair.mul_assoc] at u1
    repeat rw [← BPair.mul_assoc] at u2
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_trans u1 (leB_trans (leB_congr ?_ ?_ u2) (leB_congr_right ?_ t))
    · exact polEqB [n, s, m, cc, rho2, nl, W2, eWd, mQD]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 8)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)) (Mon.var 1)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 8)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 8)) (Mon.var 7))) (by decide +kernel)
    · exact polEqB [n, s, m, cc, rho2, nl, W2, eWd, K, muQ]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 8)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.cst 2)) (Mon.var 8)) (Mon.var 0)) (Mon.var 9)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 8)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 7)) (Mon.var 1)) (Mon.var 3)) (Mon.var 6)) (Mon.var 0)) (Mon.var 9))) (by decide +kernel)
    · exact polEqB [K, rho2, nl, m, n, eWd, s, cc, L, D]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7))) (Pol.add (Pol.mon (Mon.var 8)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 6)))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 7) (Mon.cst 32)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))) (Pol.add (Pol.mon (Mon.var 8)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 6))) (by decide +kernel)
  -- the squares' cap at the mode weight: the three members
  have hZ : BPair.unit ≤ BPair.ofNat 2 * eWd * (s * s) * cc :=
    unitLeMul (unitLeMul (unitLeMul hpos2 heWd) (unitLeMul hs hs)) hcc
  have tB := leB_mulR hZ hZt
  rw [BPair.left_distrib, BPair.left_distrib] at tB
  have hB1 : BPair.ofNat 2 * eWd * (s * s) * cc * (BPair.ofNat 192 * (g * kappa * (e * e) * mZD) * (s * s))
      ≤ BPair.ofNat 384 * g * kappa * CZ * e * e * n * s * eWd * cc * D * s * s
        + BPair.ofNat 384 * g * kappa * Pp * m * m * n * n * eWd * D * s * s := by
    have hW : BPair.unit ≤ BPair.ofNat 384 * (g * kappa * (e * e)) * eWd * (s * s) :=
      unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 384) (unitLeMul (unitLeMul hg hkap)
        (unitLeMul he he))) heWd) (unitLeMul hs hs)
    have t := leB_mulR hW hZD
    rw [BPair.right_distrib, BPair.left_distrib] at t
    have hQ : BPair.unit ≤ BPair.ofNat 384 * g * kappa * eWd * s * s * Pp * n * n * D :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
        (unitLeMul (unitLeOfNat 384) hg) hkap) heWd) hs) hs) hPp) hn) hn) hD1
    have t2 := leB_mulR hQ hEM
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc] at t2
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left ?_ t) (leB_add (leB_congr_right ?_ (leB_refl _))
      (leB_trans (leB_congr_left ?_ t2) (leB_congr_right ?_ (leB_refl _))))
    · exact polEqB [g, kappa, e, eWd, s, mZD, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 6)) (Mon.cst 192)) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 5)) (Mon.var 4)) (Mon.var 4))) (by decide +kernel)
    · exact polEqB [g, kappa, e, eWd, s, CZ, n, cc, D]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 4)) (Mon.var 7)) (Mon.var 8)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 0)) (Mon.var 1)) (Mon.var 5)) (Mon.var 2)) (Mon.var 2)) (Mon.var 6)) (Mon.var 4)) (Mon.var 3)) (Mon.var 7)) (Mon.var 8)) (Mon.var 4)) (Mon.var 4))) (by decide +kernel)
    · exact polEqB [g, kappa, eWd, s, Pp, n, D, e]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 0)) (Mon.var 1)) (Mon.var 7)) (Mon.var 7)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6))) (by decide +kernel)
    · exact polEqB [g, kappa, eWd, s, Pp, n, D, m]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)) (Mon.var 6)) (Mon.var 7)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 0)) (Mon.var 1)) (Mon.var 4)) (Mon.var 7)) (Mon.var 7)) (Mon.var 5)) (Mon.var 5)) (Mon.var 2)) (Mon.var 6)) (Mon.var 3)) (Mon.var 3))) (by decide +kernel)
  have hB2 : BPair.ofNat 2 * eWd * (s * s) * cc * (BPair.ofNat 12 * (ThR * mZD2) * (m * m) * (s * s))
      ≤ cc * BPair.ofNat 96 * ThR * K * K * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * m * m * n * n
          * eWd * D * s * s := by
    have hV : BPair.unit ≤ BPair.ofNat 24 * (ThR * eWd) * (s * s) * (m * m) * cc :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 24) (unitLeMul hThR heWd))
        (unitLeMul hs hs)) (unitLeMul hm hm)) hcc
    have t := leB_mulR hV hZD2
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · exact polEqB [ThR, eWd, s, m, cc, mZD2]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 24) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 2)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4)) (Mon.cst 12)) (Mon.var 0)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
    · exact polEqB [ThR, eWd, s, m, cc, K, dG, n, D]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 24) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.cst 4)) (Mon.var 5)) (Mon.var 5))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 6))))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 8)))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 4) (Mon.cst 96)) (Mon.var 0)) (Mon.var 5)) (Mon.var 5))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 6))))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 2))) (by decide +kernel)
  have hB3 : BPair.ofNat 2 * eWd * (s * s) * cc * (BPair.ofNat 3 * (n * n * mZD) * (m * m))
      ≤ cc * BPair.ofNat 6 * CZ * m * m * n * n * eWd * D * s * s
        + BPair.ofNat 6 * Pp * m * m * n * n * eWd * D * s * s := by
    have hU : BPair.unit ≤ BPair.ofNat 6 * (n * n) * (m * m) * eWd :=
      unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 6) (unitLeMul hn hn)) (unitLeMul hm hm)) heWd
    have t := leB_mulR hU hZD
    rw [BPair.right_distrib, BPair.left_distrib] at t
    have hQ1 : BPair.unit ≤ BPair.ofNat 6 * CZ * (n * n) * (m * m) * eWd * D * s * cc :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 6)
        hCZ) (unitLeMul hn hn)) (unitLeMul hm hm)) heWd) hD1) hs) hcc
    have t1 := leB_mulL hQ1 hns
    have hQ2 : BPair.unit ≤ BPair.ofNat 6 * Pp * (n * n) * (m * m) * eWd * D :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 6) hPp)
        (unitLeMul hn hn)) (unitLeMul hm hm)) heWd) hD1
    have t2 := leB_mulR hQ2 (leB_mul_mono hn hs hns hns)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc] at t1
    repeat rw [← BPair.mul_assoc] at t2
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left ?_ t) (leB_add (leB_congr ?_ ?_ t1) (leB_congr ?_ ?_ t2))
    · exact polEqB [n, m, eWd, mZD, s, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 0)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.cst 3)) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1))) (by decide +kernel)
    · exact polEqB [n, CZ, m, eWd, D, s, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 6)) (Mon.var 1)) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 0)) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 1)) (Mon.var 0)) (Mon.var 5)) (Mon.var 6)) (Mon.var 4))) (by decide +kernel)
    · exact polEqB [s, CZ, n, m, eWd, D, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 6)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.cst 6)) (Mon.var 1)) (Mon.var 3)) (Mon.var 3)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0))) (by decide +kernel)
    · exact polEqB [Pp, n, m, eWd, D]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 1)) (Mon.var 1)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 4))) (by decide +kernel)
    · exact polEqB [Pp, n, m, eWd, D, s]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 0)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 0)) (Mon.var 2)) (Mon.var 2)) (Mon.var 1)) (Mon.var 1)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 5))) (by decide +kernel)
  -- the slack at the mode weight: the three members
  have hX : BPair.unit ≤ s * s * (m * m) * eWd :=
    unitLeMul (unitLeMul (unitLeMul hs hs) (unitLeMul hm hm)) heWd
  have tC := leB_mulR hX hZq
  rw [BPair.left_distrib, BPair.left_distrib] at tC
  have hC1 : s * s * (m * m) * eWd * (cq * mZD2 * (s * s))
      ≤ BPair.ofNat 4 * cq * K * K * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * m * m * n * n * eWd
          * D * s * s := by
    have hQ : BPair.unit ≤ cq * (s * s) * (m * m) * eWd :=
      unitLeMul (unitLeMul (unitLeMul hcq (unitLeMul hs hs)) (unitLeMul hm hm)) heWd
    have t := leB_mulR hQ hZD2
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · exact polEqB [cq, s, m, eWd, mZD2]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 1)) (Mon.var 1)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 0)) (Mon.var 4)) (Mon.var 1)) (Mon.var 1))) (by decide +kernel)
    · exact polEqB [cq, s, m, eWd, K, dG, n, D]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.cst 4)) (Mon.var 4)) (Mon.var 4))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 5))))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 7)))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 4)) (Mon.var 4))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 5))))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 1))) (by decide +kernel)
  have hC2 : s * s * (m * m) * eWd * (cc * (n * Om * mZD * s))
      ≤ cc * Om * CZ * m * m * n * n * eWd * D * s * s
        + Om * Pp * m * m * n * n * eWd * D * s * s := by
    have hR : BPair.unit ≤ n * Om * s * (m * m) * eWd :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul hn hOm) hs) (unitLeMul hm hm)) heWd
    have t := leB_mulR hR hZD
    rw [BPair.right_distrib, BPair.left_distrib] at t
    have hQ3 : BPair.unit ≤ Om * Pp * (n * n) * (m * m) * eWd * D * s :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul hOm hPp)
        (unitLeMul hn hn)) (unitLeMul hm hm)) heWd) hD1) hs
    have t2 := leB_mulL hQ3 hns
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc] at t2
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left ?_ t)
      (leB_add (leB_congr_right ?_ (leB_refl _)) (leB_congr ?_ ?_ t2))
    · exact polEqB [n, Om, s, m, eWd, mZD, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 2)) (Mon.var 2)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 6)) (Mon.var 0)) (Mon.var 1)) (Mon.var 5)) (Mon.var 2))) (by decide +kernel)
    · exact polEqB [n, Om, s, m, eWd, CZ, cc, D]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 0)) (Mon.var 2)) (Mon.var 6)) (Mon.var 7)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 1)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 0)) (Mon.var 0)) (Mon.var 4)) (Mon.var 7)) (Mon.var 2)) (Mon.var 2))) (by decide +kernel)
    · exact polEqB [n, Om, Pp, m, eWd, D, s]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 6)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 2)) (Mon.var 0)) (Mon.var 0)) (Mon.var 5))) (by decide +kernel)
    · exact polEqB [s, Om, Pp, n, m, eWd, D]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 0)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 4)) (Mon.var 4)) (Mon.var 3)) (Mon.var 3)) (Mon.var 5)) (Mon.var 6)) (Mon.var 0)) (Mon.var 0))) (by decide +kernel)
  have hC3 : (s * s * (m * m) * eWd * (Wq * (n * n) * D)).oneValue
      (Wq * m * m * n * n * eWd * D * s * s) :=
    polEqB [s, m, eWd, Wq, n, D]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 4) (Mon.var 4))) (Mon.var 5))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 1)) (Mon.var 1)) (Mon.var 4)) (Mon.var 4)) (Mon.var 2)) (Mon.var 5)) (Mon.var 0)) (Mon.var 0))) (by decide +kernel)
  -- the three groups
  have hA : BPair.ofNat 2 * (n * n) * mXQ * (s * s * (m * m) * eWd * cc)
      ≤ BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * m * m * cc * D * s * s
        + cc * BPair.ofNat 32 * K * rho2 * nl * (L + BPair.ofNat 2) * m * m * n * n * eWd
          * D * s * s := by
    have hY : BPair.unit ≤ BPair.ofNat 2 * (n * n) * (s * s * (m * m)) * cc :=
      unitLeMul (unitLeMul (unitLeMul hpos2 (unitLeMul hn hn))
        (unitLeMul (unitLeMul hs hs) (unitLeMul hm hm))) hcc
    have t := leB_mulR hY hXQ
    rw [BPair.left_distrib] at t
    refine leB_trans (leB_congr_left ?_ t) (leB_add hA1 hA2)
    exact polEqB [n, s, m, cc, mXQ, eWd]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 2)))) (Mon.var 3)) (Mon.mul (Mon.var 4) (Mon.var 5))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 4)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 5)) (Mon.var 3)))) (by decide +kernel)
  have hB : BPair.ofNat 2 * mZt * (s * s) * (s * s * (m * m) * eWd * cc)
      ≤ (BPair.ofNat 384 * g * kappa * CZ * e * e * n * s * eWd * cc * D * s * s
          + BPair.ofNat 384 * g * kappa * Pp * m * m * n * n * eWd * D * s * s)
        + cc * BPair.ofNat 96 * ThR * K * K * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * m * m * n * n
          * eWd * D * s * s
        + (cc * BPair.ofNat 6 * CZ * m * m * n * n * eWd * D * s * s
          + BPair.ofNat 6 * Pp * m * m * n * n * eWd * D * s * s) := by
    refine leB_trans (leB_congr_left ?_ tB) (leB_add (leB_add hB1 hB2) hB3)
    exact polEqB [eWd, s, cc, mZt, m]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 4) (Mon.var 4))) (Mon.mul (Mon.var 1) (Mon.var 1)))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 3)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.mul (Mon.var 4) (Mon.var 4))) (Mon.var 0)) (Mon.var 2)))) (by decide +kernel)
  have hC : mZq * (s * s) * (s * s * (m * m) * eWd * cc)
      ≤ BPair.ofNat 4 * cq * K * K * (BPair.ofNat 1 + BPair.ofNat 2 * dG) * m * m * n * n * eWd
          * D * s * s
        + (cc * Om * CZ * m * m * n * n * eWd * D * s * s
          + Om * Pp * m * m * n * n * eWd * D * s * s)
        + Wq * m * m * n * n * eWd * D * s * s := by
    refine leB_trans (leB_congr_left (polEqB [s, m, eWd, mZq, cc]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 4))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 3) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.var 2)) (Mon.var 4)))) (by decide +kernel)) tC)
      (leB_add (leB_add hC1 hC2) (leB_congr_right hC3 (leB_refl _)))
  -- the assembly at the clearing D s², the excess against the members joined
  have hXc : BPair.unit ≤ s * s * (m * m) * eWd * cc := unitLeMul hX hcc
  have hN2 := leB_mulL hXc hN
  rw [BPair.right_distrib, BPair.right_distrib] at hN2
  have hsum := leB_trans hN2 (leB_add (leB_add hA hB) hC)
  have hL' : (rv * (s * s) * (m * m) * eWd * cc * (D * (s * s))).oneValue
      (N * (s * s) * (s * s * (m * m) * eWd * cc)) := by
    have e : (rv * (s * s) * (m * m) * eWd * cc * (D * (s * s))).oneValue
        (rv * D * (s * s) * (s * s * (m * m) * eWd * cc)) :=
      polEqB [rv, s, m, eWd, cc, D]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 3)) (Mon.var 4)) (Mon.mul (Mon.var 5) (Mon.mul (Mon.var 1) (Mon.var 1)))))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 5)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 3)) (Mon.var 4)))) (by decide +kernel)
    exact BPair.oneValue_trans e
      (BPair.mul_congr_left (BPair.mul_congr_left hrv))
  refine leB_unscale hc0 (leB_congr (BPair.oneValue_symm hL') ?_ hsum)
  exact polEqB [kappa, L, eWn, n, s, m, cc, D, K, rho2, nl, eWd, g, CZ, e, Pp, ThR, dG, cq, Om, Wq]
      (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.var 0))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 4))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.cst 32)) (Mon.var 8)) (Mon.var 9)) (Mon.var 10))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 11))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 4)))) (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 12)) (Mon.var 0)) (Mon.var 13)) (Mon.var 14)) (Mon.var 14)) (Mon.var 3)) (Mon.var 4)) (Mon.var 11)) (Mon.var 6)) (Mon.var 7)) (Mon.var 4)) (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.var 12)) (Mon.var 0)) (Mon.var 15)) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 11)) (Mon.var 7)) (Mon.var 4)) (Mon.var 4)))) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.cst 96)) (Mon.var 16)) (Mon.var 8)) (Mon.var 8))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 17))))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 11))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 4)))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.cst 6)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 11)) (Mon.var 7)) (Mon.var 4)) (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 6) (Mon.var 15)) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 11)) (Mon.var 7)) (Mon.var 4)) (Mon.var 4)))))) (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 18)) (Mon.var 8)) (Mon.var 8))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 17))))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 11))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 4))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 6) (Mon.var 19)) (Mon.var 13)) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 11)) (Mon.var 7)) (Mon.var 4)) (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 19) (Mon.var 15)) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 11)) (Mon.var 7)) (Mon.var 4)) (Mon.var 4))))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 20) (Mon.var 5)) (Mon.var 5)) (Mon.var 3)) (Mon.var 3)) (Mon.var 11)) (Mon.var 7)) (Mon.var 4)) (Mon.var 4)))))
      (Pol.mul (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.cst 16) (Mon.var 0))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5)))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 384) (Mon.mul (Mon.mul (Mon.var 12) (Mon.var 0)) (Mon.var 13))) (Mon.mul (Mon.var 14) (Mon.var 14))) (Mon.var 3)) (Mon.var 4)) (Mon.var 11)) (Mon.var 6)))) (Pol.mul (Pol.mul (Pol.mul (Pol.add (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 6)) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 32)) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.var 8) (Mon.var 9)) (Mon.var 10))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2))))) (Pol.mul (Pol.add (Pol.mon (Mon.cst 6)) (Pol.mon (Mon.var 19))) (Pol.mon (Mon.var 13)))) (Pol.mul (Pol.mon (Mon.cst 96)) (Pol.mul (Pol.mon (Mon.mul (Mon.var 16) (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 17)))))))) (Pol.mul (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.cst 384) (Mon.mul (Mon.var 12) (Mon.var 0)))) (Pol.mon (Mon.cst 6))) (Pol.mon (Mon.var 19))) (Pol.mon (Mon.var 15)))) (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.mul (Pol.mon (Mon.mul (Mon.var 18) (Mon.mul (Mon.var 8) (Mon.var 8)))) (Pol.add (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.mul (Mon.cst 2) (Mon.var 17))))))) (Pol.mon (Mon.var 20))) (Pol.mon (Mon.mul (Mon.var 5) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.mon (Mon.var 11)))) (Pol.mon (Mon.mul (Mon.var 7) (Mon.mul (Mon.var 4) (Mon.var 4))))) (by decide +kernel)

/-- `lem:cornerkey`'s cap and key at one scale: the excess and the mode
read joined, the reads' sum at or below `η (16 κ (L + 2) e_W + g κ
(192 C_D n_p + 384 C_Z) ε² + (P_u + P_v) η)` (the excess at the mode
read's clearing, the two mass reads joined at one coefficient), and
at the three key comparisons, the side's `64 κ (L + 2) e_W < φ`, the
mass's `4 g κ (192 C_D n_p + 384 C_Z) ε² < φ` and the scale's
`4 (P_u + P_v) η < φ`, each at its pair cross-multiplied: the reads'
sum sits under three quarters of the floor's multiple of the scale,
`r_u + r_v < η φ`, read at the clearing `s fd` against `n fn`; every
datum cleared at the scale pair `[n : s]`, the mass `[e : m]`, the
mode read `[eWn : eWd]` and the floor pair `[fn : fd]`, with `P_u`
and `P_v` the two scale reads' coefficients at the mass's clearing
and the stated pairs' clearing `cc`, the scale comparison read at
it. -/
theorem key_quarters (ru rv Pu Pv g kappa CD np CZ e m n s eWn eWd L fn fd cc : BPair)
    (hru : ru * (s * s * s) * (m * m) * cc
      ≤ BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s) * cc + Pu * (n * n) * s)
    (hrv : rv * (s * s) * (m * m) * eWd * cc
      ≤ BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * (m * m) * cc
        + BPair.ofNat 384 * (g * kappa * CZ) * (e * e) * n * s * eWd * cc
        + Pv * (n * n) * eWd)
    (hside : BPair.ofNat 64 * kappa * (L + BPair.ofNat 2) * eWn * fd < fn * eWd)
    (hmass : BPair.ofNat 4 * (g * kappa * (BPair.ofNat 192 * (CD * np) + BPair.ofNat 384 * CZ))
      * (e * e) * fd < fn * (m * m))
    (hscale : BPair.ofNat 4 * (Pu + Pv) * n * fd < cc * fn * s * (m * m))
    (hn0 : BPair.unit < n) (hs0 : BPair.unit < s) (hm0 : BPair.unit < m)
    (heWd0 : BPair.unit < eWd) (hcc0 : BPair.unit < cc) (hfd : BPair.unit ≤ fd)
    (hfn : BPair.unit ≤ fn) :
    (ru + rv) * s * fd < n * fn := by
  have hn : BPair.unit ≤ n := leB_of_lt hn0
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hm : BPair.unit ≤ m := leB_of_lt hm0
  have heWd : BPair.unit ≤ eWd := leB_of_lt heWd0
  have hcc : BPair.unit ≤ cc := leB_of_lt hcc0
  have hC0 : BPair.unit < s * s * (m * m) * eWd * cc :=
    unitLtMul (unitLtMul (unitLtMul (unitLtMul hs0 hs0) (unitLtMul hm0 hm0)) heWd0) hcc0
  have hC : BPair.unit ≤ s * s * (m * m) * eWd * cc := leB_of_lt hC0
  have hFc : BPair.unit ≤ fn * (n * (s * s) * (m * m) * eWd * cc) :=
    unitLeMul hfn (unitLeMul (unitLeMul (unitLeMul (unitLeMul hn (unitLeMul hs hs))
      (unitLeMul hm hm)) heWd) hcc)
  -- the excess at the mode read's clearing
  have hru' : ru * (s * s) * (m * m) * eWd * cc
      ≤ BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd * cc
        + Pu * (n * n) * eWd := by
    have t := leB_mulL heWd hru
    rw [BPair.right_distrib] at t
    refine leB_unscale hs0 ?_
    rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_
      (BPair.add_congr ?_ (BPair.oneValue_of_eq ?_)) t
    · exact polEqB [ru, s, m, cc, eWd]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 2)) (Mon.var 4)) (Mon.var 3)) (Mon.var 1))) (by decide +kernel)
    · exact polEqB [g, kappa, CD, np, e, n, s, cc, eWd]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 192) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 6)) (Mon.var 7)) (Mon.var 8)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 192) (Mon.var 0)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)) (Mon.var 6)) (Mon.var 8)) (Mon.var 7)) (Mon.var 6))) (by decide +kernel)
    · rw [BPair.mul_right_comm (Pu * n * n) s eWd]
  -- the two mass reads joined at one coefficient
  have hM : (BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd * cc
        + BPair.ofNat 384 * (g * kappa * CZ) * (e * e) * n * s * eWd * cc).oneValue
      (g * kappa * (BPair.ofNat 192 * (CD * np) + BPair.ofNat 384 * CZ) * (e * e) * n * s * eWd
        * cc) := by
    rw [BPair.left_distrib (g * kappa)]
    repeat rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
    refine BPair.add_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_)
    · rw [BPair.mul_comm (BPair.ofNat 192) g,
        BPair.mul_right_comm (g) (BPair.ofNat 192) kappa]
    · rw [BPair.mul_comm (BPair.ofNat 384) g,
        BPair.mul_right_comm (g) (BPair.ofNat 384) kappa]
  -- the reads' sum at the cap: the excess and the mode read joined
  have hsum : (ru + rv) * (s * s) * (m * m) * eWd * cc
      ≤ BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * (m * m) * cc
        + g * kappa * (BPair.ofNat 192 * (CD * np) + BPair.ofNat 384 * CZ) * (e * e) * n * s * eWd
          * cc
        + (Pu + Pv) * (n * n) * eWd := by
    have t := leB_add hru' hrv
    have hac5 : ∀ a b c d f : BPair, a + b + (c + d + f) = c + (a + d) + (b + f) := by
      intro a b c d f
      repeat rw [← BPair.add_assoc]
      rw [BPair.add_right_comm (a) (b) (c),
        BPair.add_comm (a) (c),
        BPair.add_right_comm (c + a) (b) (d)]
    rw [hac5] at t
    refine leB_congr ?_ (BPair.add_congr (BPair.add_congr
      (BPair.oneValue_refl _) hM) (BPair.oneValue_of_eq ?_)) t
    · exact polEqB [ru, s, m, eWd, cc, rv]
          (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 3)) (Mon.var 4))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 5) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.var 3)) (Mon.var 4))))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.mul (Mon.var 1) (Mon.var 1)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (by decide +kernel)
    · rw [BPair.right_distrib, BPair.right_distrib]
  -- the three quarters, each strictly under the floor's multiple of the clearing
  have t1 : BPair.ofNat 4 * (BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * (m * m) * cc)
        * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd * cc) := by
    have hb := ltB_mulPos hside (unitLtMul (unitLtMul hn0 (unitLtMul (unitLtMul hs0 hs0)
      (unitLtMul hm0 hm0))) hcc0)
    repeat rw [← BPair.mul_assoc] at hb
    repeat rw [← BPair.mul_assoc]
    refine BPair.lt_congr ?_ ?_ hb
    · exact polEqB [kappa, L, eWn, fd, n, s, m, cc]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.cst 64) (Mon.var 0))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 7)))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.cst 16)) (Mon.var 0))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 3))) (by decide +kernel)
    · exact polEqB [fn, eWd, n, s, m, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 4)) (Mon.var 1)) (Mon.var 5))) (by decide +kernel)
  have t2 : BPair.ofNat 4 * (g * kappa * (BPair.ofNat 192 * (CD * np) + BPair.ofNat 384 * CZ) * (e * e)
        * n * s * eWd * cc) * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd * cc) := by
    have hb := ltB_mulPos hmass (unitLtMul (unitLtMul (unitLtMul hn0 (unitLtMul hs0 hs0)) heWd0) hcc0)
    repeat rw [← BPair.mul_assoc] at hb
    repeat rw [← BPair.mul_assoc]
    refine BPair.lt_congr ?_ ?_ hb
    · exact polEqB [g, kappa, CD, np, CZ, e, fd, n, s, eWd, cc]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 192) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.cst 384) (Mon.var 4))))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 10)))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.var 1))) (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.cst 192) (Mon.var 2)) (Mon.var 3))) (Pol.mon (Mon.mul (Mon.cst 384) (Mon.var 4))))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 7))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.var 9))) (Pol.mon (Mon.var 10))) (Pol.mon (Mon.var 8))) (Pol.mon (Mon.var 6))) (by decide +kernel)
    · exact polEqB [fn, m, n, s, eWd, cc]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 1)) (Mon.var 1)) (Mon.var 4)) (Mon.var 5))) (by decide +kernel)
  have t3 : BPair.ofNat 4 * ((Pu + Pv) * (n * n) * eWd) * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd * cc) := by
    have hb := ltB_mulPos hscale (unitLtMul hn0 (unitLtMul hs0 heWd0))
    repeat rw [← BPair.mul_assoc] at hb
    repeat rw [← BPair.mul_assoc]
    refine BPair.lt_congr ?_ ?_ hb
    · exact polEqB [Pu, Pv, n, fd, s, eWd]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5)))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 3))) (by decide +kernel)
    · exact polEqB [cc, fn, s, m, n, eWd]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 4)) (Mon.var 2)) (Mon.var 5)))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 4)) (Mon.var 2)) (Mon.var 2)) (Mon.var 3)) (Mon.var 3)) (Mon.var 5)) (Mon.var 0))) (by decide +kernel)
  -- the sum under three quarters, under the whole
  have hR : BPair.ofNat 4 * (BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * (m * m) * cc
        + g * kappa * (BPair.ofNat 192 * (CD * np) + BPair.ofNat 384 * CZ) * (e * e) * n * s * eWd
          * cc
        + (Pu + Pv) * (n * n) * eWd) * (s * fd)
      < BPair.ofNat 4 * (fn * (n * (s * s) * (m * m) * eWd * cc)) := by
    rw [BPair.left_distrib, BPair.left_distrib, BPair.right_distrib, BPair.right_distrib]
    have h3 := ltB_add (ltB_add t1 (leB_of_lt t2)) (leB_of_lt t3)
    refine ltB_trans_le h3 ?_
    have e4 : (BPair.ofNat 4 * (fn * (n * (s * s) * (m * m) * eWd * cc))).oneValue (fn * (n * (s
        * s) * (m * m) * eWd * cc) + fn * (n * (s * s) * (m * m) * eWd * cc) + (fn * (n * (s *
        s) * (m * m) * eWd * cc) + fn * (n * (s * s) * (m * m) * eWd * cc))) :=
      polEqB [fn, n, s, m, eWd, cc]
          (Pol.mon (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4)) (Mon.var 5)))))
          (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4)) (Mon.var 5))))) (Pol.add (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4)) (Mon.var 5)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4)) (Mon.var 5)))))) (by decide +kernel)
    refine leB_congr_right (BPair.oneValue_symm e4) ?_
    exact leB_add (leB_refl _) (leB_congr_left (BPair.add_unit _) (leB_add (leB_refl _) hFc))
  have h4 : (BPair.ofNat 16 * kappa * (L + BPair.ofNat 2) * eWn * n * s * (m * m) * cc
        + g * kappa * (BPair.ofNat 192 * (CD * np) + BPair.ofNat 384 * CZ) * (e * e) * n * s * eWd
          * cc
        + (Pu + Pv) * (n * n) * eWd) * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd * cc) := by
    have c4 : ∀ X Y : BPair, BPair.ofNat 4 * X * Y = X * Y * BPair.ofNat 4 := fun X Y => by
      rw [BPair.mul_comm (BPair.ofNat 4) X, BPair.mul_right_comm X (BPair.ofNat 4) Y]
    refine ltB_unscale (unitLeOfNat 4) ?_
    exact BPair.lt_congr (BPair.oneValue_of_eq (c4 _ _))
      (BPair.oneValue_of_eq (BPair.mul_comm _ _)) hR
  -- the clearing withdrawn
  have h5 := leB_ltB_trans (leB_mulL (unitLeMul hs hfd) hsum) h4
  refine ltB_unscale hC ?_
  refine BPair.lt_congr ?_ (BPair.oneValue_of_eq ?_) h5
  · exact polEqB [ru, rv, s, m, eWd, cc, fd]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.var 3) (Mon.var 3)))) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 5))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 6))))
        (Pol.mul (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 6))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.mul (Mon.var 3) (Mon.var 3))) (Mon.var 4)) (Mon.var 5)))) (by decide +kernel)
  · repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_comm fn n]


/-! The fifth power under the halving. -/

/-- The fifth power's halving step from seven: `(i + 1)^5 ≤ 2 i^5`. -/
private theorem stepPow5 (i : Nat) (h : 7 ≤ i) : (i + 1) ^ 5 ≤ 2 * i ^ 5 := by
  have h1 : 7 * (i + 1) ≤ 8 * i := by
    have e : 8 * i = 7 * i + i := Nat.succ_mul 7 i
    rw [Nat.mul_add, Nat.mul_one, e]
    exact Nat.add_le_add_left h (7 * i)
  have h2 := Nat.pow_le_pow_left h1 5
  rw [mulPow, mulPow] at h2
  have h3 : 8 ^ 5 * i ^ 5 ≤ 7 ^ 5 * (2 * i ^ 5) := by
    rw [mulHeadComm (7 ^ 5) 2 (i ^ 5)]
    exact Nat.mul_le_mul_right (i ^ 5) (by decide : 8 ^ 5 ≤ 2 * 7 ^ 5)
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans h2 h3) (by decide : 0 < 7 ^ 5)

/-- The fifth power under the halving from `32`. -/
private theorem pow5_le_two_pow : ∀ t : Nat, (32 + t) ^ 5 ≤ 2 ^ (32 + t)
  | 0 => by decide +kernel
  | t + 1 => by
    rw [← Nat.add_assoc 32 t 1, Nat.pow_succ 2 (32 + t)]
    refine Nat.le_trans (stepPow5 (32 + t) (Nat.le_trans (by decide) (Nat.le_add_right 32 t))) ?_
    rw [Nat.mul_comm 2 ((32 + t) ^ 5)]
    exact Nat.mul_le_mul_right 2 (pow5_le_two_pow t)

/-- The fifth power under the halving at every count at or beyond `32`. -/
private theorem pow5_le (i : Nat) (h : 32 ≤ i) : i ^ 5 ≤ 2 ^ i := by
  obtain ⟨t, ht⟩ := Nat.le.dest h
  rw [← ht]
  exact pow5_le_two_pow t

/-! The key's list: the comparisons and their propagation. -/

set_option genInjectivity false in
/-- A polynomial in the near scale of degree at most four at natural
coefficients, the key's list's shape. -/
structure Poly4 where
  p0 : Nat
  p1 : Nat
  p2 : Nat
  p3 : Nat
  p4 : Nat

/-- The polynomial's read at a near scale, the Horner read of its
coefficient family. -/
def Poly4.at (P : Poly4) (K : Nat) : Nat := hread [P.p0, P.p1, P.p2, P.p3, P.p4] K

/-- Two polynomials' sum, coefficientwise. -/
def Poly4.add (P Q : Poly4) : Poly4 :=
  ⟨P.p0 + Q.p0, P.p1 + Q.p1, P.p2 + Q.p2, P.p3 + Q.p3, P.p4 + Q.p4⟩

/-- A polynomial's multiple. -/
def Poly4.scale (c : Nat) (P : Poly4) : Poly4 :=
  ⟨c * P.p0, c * P.p1, c * P.p2, c * P.p3, c * P.p4⟩

/-- The sum's read is the reads' sum. -/
theorem Poly4.at_add (P Q : Poly4) (K : Nat) : (P.add Q).at K = P.at K + Q.at K := by
  show hread (hadd [P.p0, P.p1, P.p2, P.p3, P.p4] [Q.p0, Q.p1, Q.p2, Q.p3, Q.p4]) K = _
  exact hread_add _ _ K

/-- The multiple's read is the read's multiple. -/
theorem Poly4.at_scale (c : Nat) (P : Poly4) (K : Nat) : (P.scale c).at K = c * P.at K := by
  show hread ([P.p0, P.p1, P.p2, P.p3, P.p4].map (fun d => c * d)) K = _
  exact hread_scale _ c K

/-- The read is monotone in the near scale. -/
theorem Poly4.at_mono (P : Poly4) {K K' : Nat} (h : K ≤ K') : P.at K ≤ P.at K' :=
  hread_mono h _

/-- The read at a growth past the clearing sits under twice the read:
seven sixths' fourth power under two. -/
theorem Poly4.at_grow (P : Poly4) (K b : Nat) (h : 6 * b ≤ K) :
    P.at (K + b) ≤ 2 * P.at K := by
  have hg : 6 ^ 4 * P.at (K + b) ≤ 7 ^ 4 * P.at K :=
    hread_grow K b h [P.p1, P.p2, P.p3, P.p4] P.p0
  have h2 : 7 ^ 4 * P.at K ≤ 6 ^ 4 * (2 * P.at K) := by
    rw [mulHeadComm (6 ^ 4) 2 (P.at K)]
    exact Nat.mul_le_mul_right _ (by decide : 7 ^ 4 ≤ 2 * 6 ^ 4)
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans hg h2) (by decide : 0 < 6 ^ 4)

/-- The read at a linear growth against the halving count's fourth
power of the read at one step. -/
theorem Poly4.at_lin (P : Poly4) (K b t : Nat) (ht : 1 ≤ t) :
    P.at (K + b * t) ≤ t ^ 4 * P.at (K + b) :=
  hread_growLin K b t ht [P.p1, P.p2, P.p3, P.p4] P.p0

/-- The read at the top two coefficients vacant. -/
theorem Poly4.at_three (p0 p1 p2 K : Nat) :
    (⟨p0, p1, p2, 0, 0⟩ : Poly4).at K = p0 + p1 * K + p2 * (K * K) := by
  show p0 + K * (p1 + K * (p2 + K * (0 + K * (0 + K * 0)))) = p0 + p1 * K + p2 * (K * K)
  rw [Nat.mul_zero K, Nat.add_zero 0, Nat.mul_zero K, Nat.add_zero 0, Nat.mul_zero K,
    Nat.add_zero p2, Nat.mul_add K p1 (K * p2), ← Nat.add_assoc, Nat.mul_comm K p1,
    ← mulAssoc K K p2, Nat.mul_comm (K * K) p2]

/-- The read at the constant alone. -/
theorem Poly4.at_cst (p0 K : Nat) : (⟨p0, 0, 0, 0, 0⟩ : Poly4).at K = p0 := by
  rw [Poly4.at_three, Nat.zero_mul K, Nat.zero_mul (K * K)]
  exact (Nat.add_zero _).trans (Nat.add_zero _)

set_option genInjectivity false in
/-- A comparison of the key's list: a polynomial in the near scale
against a cap, read at the scale's second member. -/
structure Cmp where
  P : Poly4
  c : Nat

/-- The comparison's read at a scale's second member `S` and a near
scale `K`: `P(K) ≤ c S`, the scale `[1 : S]`. -/
def Cmp.read (q : Cmp) (S K : Nat) : Prop := q.P.at K ≤ q.c * S

instance instCornerkey1 (q : Cmp) (S K : Nat) : Decidable (q.read S K) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A comparison's read at a smaller near scale. -/
theorem Cmp.read_le (q : Cmp) (S K K' : Nat) (h : q.read S K) (hK : K' ≤ K) : q.read S K' :=
  Nat.le_trans (q.P.at_mono hK) h

/-- A comparison holding at a scale holds at its half past the
clearing: the near scale at most one growth beyond, the growth's
read under two. -/
theorem Cmp.read_half (q : Cmp) (S K K' b : Nat) (h : q.read S K) (hK : 6 * b ≤ K)
    (hK' : K' ≤ K + b) : q.read (2 * S) K' := by
  show q.P.at K' ≤ q.c * (2 * S)
  rw [mulHeadComm q.c 2 S, mulAssoc 2 q.c S]
  exact Nat.le_trans (q.P.at_mono hK') (Nat.le_trans (q.P.at_grow K b hK)
    (Nat.mul_le_mul_left 2 h))

/-- A comparison holds at the witness past the clearing: at the
halving count `t` at or beyond `32` with the read at one step at or
below it, the read at `t` steps sits under the fifth power, under the
halving. -/
theorem Cmp.read_witness (q : Cmp) (S K b t : Nat) (hc : 1 ≤ q.c) (hS : 1 ≤ S)
    (ht : 32 ≤ t) (hq : q.P.at (K + b) ≤ t) : q.read (S * 2 ^ t) (K + b * t) := by
  show q.P.at (K + b * t) ≤ q.c * (S * 2 ^ t)
  have h1 : 1 ≤ t := Nat.le_trans (by decide) ht
  have h2 : q.P.at (K + b * t) ≤ t ^ 4 * t := Nat.le_trans (q.P.at_lin K b t h1)
    (Nat.mul_le_mul_left _ hq)
  rw [← Nat.pow_succ] at h2
  refine Nat.le_trans h2 (Nat.le_trans (pow5_le t ht) ?_)
  have h3 : 1 * (1 * 2 ^ t) ≤ q.c * (S * 2 ^ t) :=
    Nat.mul_le_mul hc (Nat.mul_le_mul hS (Nat.le_refl _))
  rw [Nat.one_mul, Nat.one_mul] at h3
  exact h3

/-- The list's read: every comparison at the scale's second member
and the near scale. -/
def listRead (qs : List Cmp) (S K : Nat) : Prop :=
  qs.all (fun q => decide (q.read S K)) = true

instance instCornerkey2 (qs : List Cmp) (S K : Nat) : Decidable (listRead qs S K) :=
  inferInstanceAs (Decidable (_ = _))

/-- The list's read from the members' reads. -/
theorem listRead_intro (qs : List Cmp) (S K : Nat) (h : ∀ q, q ∈ qs → q.read S K) :
    listRead qs S K :=
  all_of_mem_intro _ qs (fun q hq => decide_eq_true (h q hq))

/-- A member's read off the list's. -/
theorem listRead_mem (qs : List Cmp) (S K : Nat) (h : listRead qs S K) (q : Cmp)
    (hq : q ∈ qs) : q.read S K :=
  of_decide_eq_true (all_of_mem _ qs h q hq)

/-- The list's read at a smaller near scale. -/
theorem listRead_le (qs : List Cmp) (S K K' : Nat) (h : listRead qs S K) (hK : K' ≤ K) :
    listRead qs S K' :=
  listRead_intro qs _ _ (fun q hq => q.read_le S K K' (listRead_mem qs S K h q hq) hK)

/-- The list's read at a scale holds at its half past the clearing. -/
theorem listRead_half (qs : List Cmp) (S K K' b : Nat) (h : listRead qs S K)
    (hK : 6 * b ≤ K) (hK' : K' ≤ K + b) : listRead qs (2 * S) K' :=
  listRead_intro qs _ _ (fun q hq => q.read_half S K K' b (listRead_mem qs S K h q hq) hK hK')

/-- The list's reads at a near scale, summed. -/
def listAt (qs : List Cmp) (K : Nat) : Nat := sumNat (qs.map (fun q => q.P.at K))

/-- A member's read sits at or below the summed reads. -/
theorem listAt_mem (K : Nat) (qs : List Cmp) (q : Cmp) (hq : q ∈ qs) : q.P.at K ≤ listAt qs K :=
  mem_le_sumNat _ _ (mem_map_to (fun q => q.P.at K) hq)

/-- Every cap at or beyond one. -/
def listCaps (qs : List Cmp) : Prop := qs.all (fun q => decide (1 ≤ q.c)) = true

instance instCornerkey3 (qs : List Cmp) : Decidable (listCaps qs) := inferInstanceAs (Decidable (_ = _))

/-- A member's cap off the caps' read. -/
theorem listCaps_mem (qs : List Cmp) (q : Cmp) (h : listCaps qs) (hq : q ∈ qs) : 1 ≤ q.c :=
  of_decide_eq_true (all_of_mem _ qs h q hq)

/-- The list holds at the witness past the clearing: the halving
count at or beyond `32` and at or beyond the list's reads summed at
one step. -/
theorem listRead_witness (qs : List Cmp) (S K b t : Nat) (hc : listCaps qs) (hS : 1 ≤ S)
    (ht : 32 ≤ t) (hq : listAt qs (K + b) ≤ t) : listRead qs (S * 2 ^ t) (K + b * t) :=
  listRead_intro qs _ _ (fun q hqm => q.read_witness S K b t (listCaps_mem qs q hc hqm) hS ht
    (Nat.le_trans (listAt_mem (K + b) qs q hqm) hq))

/-! The near scale down the halving family. -/

set_option genInjectivity false in
/-- The tail read's stated data at the key: the member reads (the
adjoint's index `κ_θ`, the direction gap `g`, `dim G`, `d_θ`,
`C_2(θ)`, `h_θ`, `c_θ²`, the count reads `A` and `℘`) and the
window's at the key's side (`#p`, `#ℓ`, `|W|²`, `|W|_∞`, the
covering count `Ω`, the corner cell's extent `[n_1 : d_1]`). -/
structure Tail where
  kappa : Nat
  g : Nat
  dG : Nat
  dth : Nat
  C2 : Nat
  hth : Nat
  c2 : Nat
  A : Nat
  wp : Nat
  np : Nat
  nl : Nat
  W2 : Nat
  Winf : Nat
  Om : Nat
  n1 : Nat
  d1 : Nat

/-- The data's positivity: the member and window reads the searches
divide by at or beyond one, the window's link count occupied. -/
def Tail.pos (t : Tail) : Prop :=
  1 ≤ t.kappa ∧ 1 ≤ t.g ∧ 1 ≤ t.dG ∧ 1 ≤ t.dth ∧ 1 ≤ t.A ∧ 1 ≤ t.np ∧ 1 ≤ t.W2 ∧ 1 ≤ t.n1
    ∧ 1 ≤ t.nl

instance instCornerkey4 (t : Tail) : Decidable t.pos :=
  @instDecidableAnd _ _ (Nat.decLe _ _) (@instDecidableAnd _ _ (Nat.decLe _ _)
    (@instDecidableAnd _ _ (Nat.decLe _ _) (@instDecidableAnd _ _ (Nat.decLe _ _)
      (@instDecidableAnd _ _ (Nat.decLe _ _) (@instDecidableAnd _ _ (Nat.decLe _ _)
        (@instDecidableAnd _ _ (Nat.decLe _ _) (@instDecidableAnd _ _ (Nat.decLe _ _)
          (Nat.decLe _ _))))))))

/-- The support weight's exponent `e := (3℘ + 1) #ℓ`. -/
def exK (t : Tail) : Nat := (3 * t.wp + 1) * t.nl

/-- The support weight's coefficient `c_W := A^{3#ℓ} (9g)^e`. -/
def cW (t : Tail) : Nat := t.A ^ (3 * t.nl) * (9 * t.g) ^ exK t

/-- The far read's natural `j := e + 1`. -/
def jK (t : Tail) : Nat := exK t + 1

/-- The concentration key's cleared comparison's second member at the
`i`-th halving: `T(i) := 2^i · 4 d_θ #p (L 2^{i_ε} + 2)`, the pair
`τ = [2^{i_ε} : T(i)]` at the mass `[1 : 2^{i_ε}]`. -/
def tauD (t : Tail) (L ie i : Nat) : Nat := 2 ^ i * (4 * t.dth * t.np * (L * 2 ^ ie + 2))

/-- The cleared comparison's first member `c_W j^j T(i)^j`. -/
def keyNum (t : Tail) (L ie i : Nat) : Nat := cW t * jK t ^ jK t * tauD t L ie i ^ jK t

/-- The concentration key, the least natural at the cleared
comparison `k 2^{i_ε j} ≥ c_W j^j T(i)^j`. -/
def kc (t : Tail) (L ie i : Nat) : Nat := ceilAt (keyNum t L ie i) (2 ^ (ie * jK t))

/-- The mode square's upper weight `Q_+ := 4 κ d_θ #p |W|²`. -/
def qPlus (t : Tail) : Nat := 4 * t.kappa * t.dth * t.np * t.W2

/-- The lower weight's second member at the `i`-th halving, the
compared pair's root `2^i 8 c_W k^e (L + 2)` at the scale `[1 : 2^i]`
and the near mass `[1 : 2 c_W k^e]`. -/
def pairX (t : Tail) (L ie i : Nat) : Nat := 2 ^ i * 8 * cW t * kc t L ie i ^ exK t * (L + 2)

/-- The bit count's compared pair's first member,
`Q_+² 2^{4 i_ε} (2^i 8 c_W k^e (L + 2))²`. -/
def pairNum (t : Tail) (L ie i : Nat) : Nat := qPlus t ^ 2 * 2 ^ (4 * ie) * pairX t L ie i ^ 2

/-- The compared pair's second member `(κ dim G |W|²)²`. -/
def pairDen (t : Tail) : Nat := (t.kappa * t.dG * t.W2) ^ 2

/-- The bit count: the least natural at or beyond one at `2^j`
clearing the compared pair, the search bounded at the first member. -/
def jp (t : Tail) (L ie i : Nat) : Nat :=
  firstAt (fun j => pairNum t L ie i ≤ 2 ^ j * pairDen t) 1 (pairNum t L ie i)

/-- The near scale `K := 48 (4 + j') 2^{i_ε}` at the mass `[1 : 2^{i_ε}]`. -/
def nearScale (t : Tail) (L ie i : Nat) : Nat := 48 * (4 + jp t L ie i) * 2 ^ ie

/-- The bit count's growth natural `b := 2 + 2 (e + 1) e`. -/
def bGrow (t : Tail) : Nat := 2 + 2 * (exK t + 1) * exK t

/-- The near scale's growth per halving `b_K := 48 b 2^{i_ε}`. -/
def bK (t : Tail) (ie : Nat) : Nat := 48 * bGrow t * 2 ^ ie

/-- The second member's bit count `d`, the least natural at `2^d`
at or beyond the member, the search bounded at the member. -/
def denBits (t : Tail) : Nat := firstAt (fun d => pairDen t ≤ 2 ^ d) 0 (pairDen t)

/-- The halved scale doubles the cleared comparison's second member. -/
theorem tauD_succ (t : Tail) (L ie i : Nat) : tauD t L ie (i + 1) = 2 * tauD t L ie i := by
  show 2 ^ (i + 1) * (4 * t.dth * t.np * (L * 2 ^ ie + 2))
    = 2 * (2 ^ i * (4 * t.dth * t.np * (L * 2 ^ ie + 2)))
  rw [Nat.pow_succ 2 i, Nat.mul_comm (2 ^ i) 2, mulAssoc]

/-- The second member is occupied. -/
theorem tauD_pos (t : Tail) (L ie i : Nat) (tp : t.pos) : 1 ≤ tauD t L ie i :=
  Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2))
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 4) tp.2.2.2.1) tp.2.2.2.2.2.1)
      (Nat.lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_add_left 2 _)))

/-- The support weight's coefficient is occupied. -/
theorem cW_pos (t : Tail) (tp : t.pos) : 1 ≤ cW t :=
  Nat.mul_pos (Nat.pow_pos tp.2.2.2.2.1)
    (Nat.pow_pos (Nat.le_trans tp.2.1 (Nat.le_mul_of_pos_left t.g (by decide : 0 < 9))))

/-- The halved scale multiplies the cleared comparison's first
member by `2^j`. -/
theorem keyNum_succ (t : Tail) (L ie i : Nat) :
    keyNum t L ie (i + 1) = 2 ^ jK t * keyNum t L ie i := by
  show cW t * jK t ^ jK t * tauD t L ie (i + 1) ^ jK t
    = 2 ^ jK t * (cW t * jK t ^ jK t * tauD t L ie i ^ jK t)
  rw [tauD_succ, mulPow, mulLeftComm]

/-- The first member is occupied. -/
theorem keyNum_pos (t : Tail) (L ie i : Nat) (tp : t.pos) : 1 ≤ keyNum t L ie i :=
  Nat.mul_pos (Nat.mul_pos (cW_pos t tp) (Nat.pow_pos (Nat.succ_pos _)))
    (Nat.pow_pos (tauD_pos t L ie i tp))

/-- The concentration key clears the cleared comparison. -/
theorem kc_ge (t : Tail) (L ie i : Nat) :
    keyNum t L ie i ≤ 2 ^ (ie * jK t) * kc t L ie i :=
  ceilAt_ge (keyNum t L ie i) (2 ^ (ie * jK t)) (Nat.pow_pos (by decide : 0 < 2))

/-- The concentration key is least at the comparison. -/
theorem kc_least (t : Tail) (L ie i q : Nat) (hq : keyNum t L ie i ≤ 2 ^ (ie * jK t) * q) :
    kc t L ie i ≤ q :=
  ceilAt_least (keyNum t L ie i) (2 ^ (ie * jK t)) q (Nat.pow_pos (by decide : 0 < 2)) hq

/-- The concentration key is occupied. -/
theorem kc_pos (t : Tail) (L ie i : Nat) (tp : t.pos) : 1 ≤ kc t L ie i :=
  (mulPosSplit (Nat.lt_of_lt_of_le (keyNum_pos t L ie i tp) (kc_ge t L ie i))).2

/-- The halved scale multiplies the concentration key by at most `2^j`. -/
theorem kc_step (t : Tail) (L ie i : Nat) : kc t L ie (i + 1) ≤ 2 ^ jK t * kc t L ie i := by
  refine kc_least t L ie (i + 1) _ ?_
  rw [keyNum_succ, mulLeftComm]
  exact Nat.mul_le_mul_left _ (kc_ge t L ie i)

/-- The concentration key is monotone down the family. -/
theorem kc_mono (t : Tail) (L ie i : Nat) : kc t L ie i ≤ kc t L ie (i + 1) := by
  refine kc_least t L ie i _ ?_
  refine Nat.le_trans ?_ (kc_ge t L ie (i + 1))
  rw [keyNum_succ]
  exact Nat.le_mul_of_pos_left (keyNum t L ie i) (Nat.pow_pos (by decide : 0 < 2))

/-- The halved scale doubles the compared pair's root at the least. -/
theorem pairX_double (t : Tail) (L ie i : Nat) :
    2 * pairX t L ie i ≤ pairX t L ie (i + 1) := by
  show 2 * (2 ^ i * 8 * cW t * kc t L ie i ^ exK t * (L + 2))
    ≤ 2 ^ (i + 1) * 8 * cW t * kc t L ie (i + 1) ^ exK t * (L + 2)
  have e : 2 * (2 ^ i * 8 * cW t * kc t L ie i ^ exK t * (L + 2))
      = 2 ^ (i + 1) * 8 * cW t * kc t L ie i ^ exK t * (L + 2) := by
    rw [Nat.pow_succ 2 i]
    exact ground.monEq [2 ^ i, cW t, kc t L ie i ^ exK t, L + 2]
      (Mon.mul (Mon.cst 2) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 8))
        (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.cst 8))
        (Mon.var 1)) (Mon.var 2)) (Mon.var 3))
      (by decide +kernel) (by decide +kernel)
  rw [e]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (kc_mono t L ie i) _))

/-- The compared pair's root is occupied. -/
theorem pairX_pos (t : Tail) (L ie i : Nat) (tp : t.pos) : 1 ≤ pairX t L ie i :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2))
    (by decide : 0 < 8)) (cW_pos t tp)) (Nat.pow_pos (kc_pos t L ie i tp)))
    (Nat.lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_add_left 2 L))

/-- The halved scale multiplies the compared pair's root by at most
`2^{1 + j e}`. -/
theorem pairX_step (t : Tail) (L ie i : Nat) :
    pairX t L ie (i + 1) ≤ 2 ^ (1 + jK t * exK t) * pairX t L ie i := by
  show 2 ^ (i + 1) * 8 * cW t * kc t L ie (i + 1) ^ exK t * (L + 2)
    ≤ 2 ^ (1 + jK t * exK t) * (2 ^ i * 8 * cW t * kc t L ie i ^ exK t * (L + 2))
  have hk : kc t L ie (i + 1) ^ exK t ≤ 2 ^ (jK t * exK t) * kc t L ie i ^ exK t := by
    rw [← powPow, ← mulPow]
    exact Nat.pow_le_pow_left (kc_step t L ie i) _
  have e : 2 ^ (1 + jK t * exK t) * (2 ^ i * 8 * cW t * kc t L ie i ^ exK t * (L + 2))
      = 2 ^ i * 2 * 8 * cW t * (2 ^ (jK t * exK t) * kc t L ie i ^ exK t) * (L + 2) := by
    rw [powAdd 2 1 (jK t * exK t), powOne]
    exact ground.monEq [2 ^ i, cW t, kc t L ie i ^ exK t, L + 2, 2 ^ (jK t * exK t)]
      (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 4)) (Mon.mul (Mon.mul (Mon.mul (Mon.mul
        (Mon.var 0) (Mon.cst 8)) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.cst 2)) (Mon.cst 8))
        (Mon.var 1)) (Mon.mul (Mon.var 4) (Mon.var 2))) (Mon.var 3))
      (by decide +kernel) (by decide +kernel)
  rw [e, Nat.pow_succ 2 i]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)

/-- The growth natural is twice the root's growth exponent. -/
theorem bGrow_read (t : Tail) : 2 * (1 + jK t * exK t) = bGrow t := by
  show 2 * (1 + (exK t + 1) * exK t) = 2 + 2 * (exK t + 1) * exK t
  rw [Nat.mul_add, Nat.mul_one, ← mulAssoc 2 (exK t + 1) (exK t)]

/-- The halved scale multiplies the compared pair by at most `2^b`. -/
theorem pairNum_step (t : Tail) (L ie i : Nat) :
    pairNum t L ie (i + 1) ≤ 2 ^ bGrow t * pairNum t L ie i := by
  show qPlus t ^ 2 * 2 ^ (4 * ie) * pairX t L ie (i + 1) ^ 2
    ≤ 2 ^ bGrow t * (qPlus t ^ 2 * 2 ^ (4 * ie) * pairX t L ie i ^ 2)
  have h1 : pairX t L ie (i + 1) ^ 2 ≤ 2 ^ (2 * (1 + jK t * exK t)) * pairX t L ie i ^ 2 := by
    rw [Nat.mul_comm 2 (1 + jK t * exK t), ← powPow, ← mulPow]
    exact Nat.pow_le_pow_left (pairX_step t L ie i) 2
  rw [bGrow_read] at h1
  rw [mulLeftComm]
  exact Nat.mul_le_mul_left _ h1

/-- The halved scale quadruples the compared pair at the least. -/
theorem pairNum_quad (t : Tail) (L ie i : Nat) :
    4 * pairNum t L ie i ≤ pairNum t L ie (i + 1) := by
  show 4 * (qPlus t ^ 2 * 2 ^ (4 * ie) * pairX t L ie i ^ 2)
    ≤ qPlus t ^ 2 * 2 ^ (4 * ie) * pairX t L ie (i + 1) ^ 2
  rw [mulLeftComm]
  refine Nat.mul_le_mul_left _ ?_
  have h := Nat.pow_le_pow_left (pairX_double t L ie i) 2
  rw [mulPow] at h
  exact h

/-- The compared pair's first member is occupied. -/
theorem pairNum_pos (t : Tail) (L ie i : Nat) (tp : t.pos) : 1 ≤ pairNum t L ie i :=
  Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos
    (Nat.mul_pos (by decide : 0 < 4) tp.1) tp.2.2.2.1) tp.2.2.2.2.2.1) tp.2.2.2.2.2.2.1))
    (Nat.pow_pos (by decide : 0 < 2))) (Nat.pow_pos (pairX_pos t L ie i tp))

/-- The compared pair's first member grows at least by the powers of
four down the family. -/
theorem pairNum_pow (t : Tail) (L ie : Nat) (tp : t.pos) :
    ∀ i : Nat, 4 ^ i ≤ pairNum t L ie i
  | 0 => by rw [Nat.pow_zero]; exact pairNum_pos t L ie 0 tp
  | i + 1 => by
    rw [Nat.pow_succ 4 i, Nat.mul_comm (4 ^ i) 4]
    exact Nat.le_trans (Nat.mul_le_mul_left 4 (pairNum_pow t L ie tp i)) (pairNum_quad t L ie i)

/-- The compared pair's second member is occupied. -/
theorem pairDen_pos (t : Tail) (tp : t.pos) : 1 ≤ pairDen t :=
  Nat.pow_pos (Nat.mul_pos (Nat.mul_pos tp.1 tp.2.2.1) tp.2.2.2.2.2.2.1)

/-- The second member sits at or below the halving's power at its bit
count. -/
theorem denBits_hit (t : Tail) : pairDen t ≤ 2 ^ denBits t := by
  refine firstAt_hit (fun d => pairDen t ≤ 2 ^ d) (pairDen t) 0 ?_
  show pairDen t ≤ 2 ^ (0 + pairDen t)
  rw [Nat.zero_add]
  exact Nat.le_of_lt Nat.lt_two_pow_self

/-- The bit count's comparison holds at every larger natural. -/
theorem pairRead_mono (t : Tail) (L ie i j j' : Nat) (hj : j ≤ j')
    (h : pairNum t L ie i ≤ 2 ^ j * pairDen t) : pairNum t L ie i ≤ 2 ^ j' * pairDen t :=
  Nat.le_trans h (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 2 > 0) hj))

/-- The bit count clears the compared pair. -/
theorem jp_hit (t : Tail) (L ie i : Nat) (tp : t.pos) :
    pairNum t L ie i ≤ 2 ^ jp t L ie i * pairDen t := by
  refine firstAt_hit (fun j => pairNum t L ie i ≤ 2 ^ j * pairDen t) (pairNum t L ie i) 1 ?_
  show pairNum t L ie i ≤ 2 ^ (1 + pairNum t L ie i) * pairDen t
  refine Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self) ?_
  refine Nat.le_trans (Nat.pow_le_pow_right (by decide : 2 > 0) (Nat.le_add_left _ 1)) ?_
  exact Nat.le_mul_of_pos_right _ (pairDen_pos t tp)

/-- The bit count sits at or beyond one. -/
theorem jp_ge1 (t : Tail) (L ie i : Nat) : 1 ≤ jp t L ie i :=
  firstAt_ge (fun j => pairNum t L ie i ≤ 2 ^ j * pairDen t) (pairNum t L ie i) 1

/-- The bit count is least at the comparison. -/
theorem jp_least (t : Tail) (L ie i j : Nat) (hj : 1 ≤ j) (hlt : j < jp t L ie i) :
    ¬ pairNum t L ie i ≤ 2 ^ j * pairDen t :=
  firstAt_below (fun j => pairNum t L ie i ≤ 2 ^ j * pairDen t) (pairNum t L ie i) 1 j hj hlt

/-- The halved scale grows the bit count by at most `b`. -/
theorem jp_step (t : Tail) (L ie i : Nat) (tp : t.pos) :
    jp t L ie (i + 1) ≤ jp t L ie i + bGrow t := by
  refine Nat.le_of_not_lt (fun hlt => jp_least t L ie (i + 1) _
    (Nat.le_trans (jp_ge1 t L ie i) (Nat.le_add_right _ _)) hlt ?_)
  refine Nat.le_trans (pairNum_step t L ie i) ?_
  rw [powAdd 2 (jp t L ie i) (bGrow t), Nat.mul_comm (2 ^ jp t L ie i) (2 ^ bGrow t), mulAssoc]
  exact Nat.mul_le_mul_left _ (jp_hit t L ie i tp)

/-- The bit count is monotone down the family. -/
theorem jp_mono (t : Tail) (L ie i : Nat) (tp : t.pos) : jp t L ie i ≤ jp t L ie (i + 1) := by
  refine Nat.le_of_not_lt (fun hlt => jp_least t L ie i _ (jp_ge1 t L ie (i + 1)) hlt ?_)
  refine Nat.le_trans ?_ (jp_hit t L ie (i + 1) tp)
  exact Nat.le_trans (Nat.le_mul_of_pos_left (pairNum t L ie i) (by decide : 0 < 4))
    (pairNum_quad t L ie i)

/-- The bit count joined to the second member's sits at or beyond
twice the halving count. -/
theorem jp_low (t : Tail) (L ie i : Nat) (tp : t.pos) : 2 * i ≤ jp t L ie i + denBits t := by
  have h1 : 2 ^ (2 * i) ≤ 2 ^ (jp t L ie i + denBits t) := by
    rw [← fourPow, powAdd]
    exact Nat.le_trans (pairNum_pow t L ie tp i) (Nat.le_trans (jp_hit t L ie i tp)
      (Nat.mul_le_mul_left _ (denBits_hit t)))
  exact leOfTwoPowLe _ _ h1

/-- The bit count at the next halving is the search from the prior
bit count within the growth: the comparison holds at the growth's end
and the least natural at or beyond one is the least at or beyond the
prior. -/
theorem jp_succ_read (t : Tail) (L ie i : Nat) (tp : t.pos) :
    firstAt (fun j => pairNum t L ie (i + 1) ≤ 2 ^ j * pairDen t) (jp t L ie i) (bGrow t)
      = jp t L ie (i + 1) := by
  have hP : pairNum t L ie (i + 1) ≤ 2 ^ (jp t L ie i + bGrow t) * pairDen t :=
    pairRead_mono t L ie (i + 1) _ _ (jp_step t L ie i tp) (jp_hit t L ie (i + 1) tp)
  have hhit := firstAt_hit (fun j => pairNum t L ie (i + 1) ≤ 2 ^ j * pairDen t) (bGrow t)
    (jp t L ie i) hP
  have hge := firstAt_ge (fun j => pairNum t L ie (i + 1) ≤ 2 ^ j * pairDen t) (bGrow t)
    (jp t L ie i)
  refine Nat.le_antisymm ?_ ?_
  · refine Nat.le_of_not_lt (fun hlt => ?_)
    exact firstAt_below (fun j => pairNum t L ie (i + 1) ≤ 2 ^ j * pairDen t) (bGrow t)
      (jp t L ie i) _ (jp_mono t L ie i tp) hlt (jp_hit t L ie (i + 1) tp)
  · refine Nat.le_of_not_lt (fun hlt => ?_)
    exact jp_least t L ie (i + 1) _ (Nat.le_trans (jp_ge1 t L ie i) hge) hlt hhit

/-- The bit count's chain down the family, each halving's search from
the prior bit count within the growth. -/
def bitWalk (t : Tail) (L ie : Nat) : Nat → Nat
  | 0 => jp t L ie 0
  | i + 1 => firstAt (fun j => pairNum t L ie (i + 1) ≤ 2 ^ j * pairDen t) (bitWalk t L ie i)
      (bGrow t)

/-- The chain reads the bit count. -/
theorem bitWalk_eq (t : Tail) (L ie : Nat) (tp : t.pos) : ∀ i : Nat, bitWalk t L ie i = jp t L ie i
  | 0 => rfl
  | i + 1 => by
    show firstAt (fun j => pairNum t L ie (i + 1) ≤ 2 ^ j * pairDen t) (bitWalk t L ie i)
      (bGrow t) = jp t L ie (i + 1)
    rw [bitWalk_eq t L ie tp i]
    exact jp_succ_read t L ie i tp

/-- The near scale grows by at most `b_K` per halving. -/
theorem nearScale_step (t : Tail) (L ie i : Nat) (tp : t.pos) :
    nearScale t L ie (i + 1) ≤ nearScale t L ie i + bK t ie := by
  show 48 * (4 + jp t L ie (i + 1)) * 2 ^ ie ≤ 48 * (4 + jp t L ie i) * 2 ^ ie + 48 * bGrow t * 2 ^ ie
  rw [← mulAddR, ← Nat.mul_add, Nat.add_assoc 4 (jp t L ie i) (bGrow t)]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left (jp_step t L ie i tp) 4))

/-- The near scale is monotone down the family. -/
theorem nearScale_mono (t : Tail) (L ie i : Nat) (tp : t.pos) :
    nearScale t L ie i ≤ nearScale t L ie (i + 1) :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left (jp_mono t L ie i tp) 4))

/-- The near scale past a halving count sits at or below the linear
growth from it. -/
theorem nearScale_lin (t : Tail) (L ie i : Nat) (tp : t.pos) :
    ∀ u : Nat, nearScale t L ie (i + u) ≤ nearScale t L ie i + bK t ie * u
  | 0 => by rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero]; exact Nat.le_refl _
  | u + 1 => by
    rw [← Nat.add_assoc i u 1, Nat.mul_succ, ← Nat.add_assoc]
    exact Nat.le_trans (nearScale_step t L ie (i + u) tp)
      (Nat.add_le_add_right (nearScale_lin t L ie i tp u) _)

/-- The near scale clears `6 b_K` from the `(3b + d)`-th halving on. -/
theorem nearScale_clear (t : Tail) (L ie u : Nat) (tp : t.pos) :
    6 * bK t ie ≤ nearScale t L ie (3 * bGrow t + denBits t + u) := by
  show 6 * (48 * bGrow t * 2 ^ ie)
    ≤ 48 * (4 + jp t L ie (3 * bGrow t + denBits t + u)) * 2 ^ ie
  have h1 : 6 * bGrow t ≤ 4 + jp t L ie (3 * bGrow t + denBits t + u) := by
    refine Nat.le_trans ?_ (Nat.le_add_left _ 4)
    have h2 := jp_low t L ie (3 * bGrow t + denBits t + u) tp
    have e : 2 * (3 * bGrow t + denBits t + u) = 6 * bGrow t + denBits t + (denBits t + 2 * u) := by
      rw [Nat.mul_add, Nat.mul_add, ← mulAssoc 2 3 (bGrow t), show 2 * 3 = 6 from rfl,
        Nat.mul_comm 2 (denBits t), Nat.mul_two (denBits t),
        ← Nat.add_assoc (6 * bGrow t) (denBits t) (denBits t),
        Nat.add_assoc (6 * bGrow t + denBits t) (denBits t) (2 * u)]
    rw [e] at h2
    exact leCancelR (denBits t) (Nat.le_trans (Nat.le_add_right _ _) h2)
  have e : 6 * (48 * bGrow t * 2 ^ ie) = 48 * (6 * bGrow t) * 2 ^ ie :=
    ground.monEq [bGrow t, 2 ^ ie]
      (Mon.mul (Mon.cst 6) (Mon.mul (Mon.mul (Mon.cst 48) (Mon.var 0)) (Mon.var 1)))
      (Mon.mul (Mon.mul (Mon.cst 48) (Mon.mul (Mon.cst 6) (Mon.var 0))) (Mon.var 1))
      (by decide +kernel) (by decide +kernel)
  rw [e]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 48 h1)

/-! The key's reads at the moment tier. -/

/-- The mode square's cap is occupied. -/
theorem qPlus_pos (t : Tail) (tp : t.pos) : 1 ≤ qPlus t :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 4) tp.1) tp.2.2.2.1)
    tp.2.2.2.2.2.1) tp.2.2.2.2.2.2.1

/-- The comparison's second member sits at or beyond the mass's second
member: the scale's power against the count and the side's multiple
of the mass's power joined to two. -/
theorem tauD_ge (t : Tail) (L ie i : Nat) (tp : t.pos) (hL : 1 ≤ L) : 2 ^ ie ≤ tauD t L ie i := by
  show 2 ^ ie ≤ 2 ^ i * (4 * t.dth * t.np * (L * 2 ^ ie + 2))
  refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide : 0 < 2)))
  refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _
    (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 4) tp.2.2.2.1) tp.2.2.2.2.2.1))
  refine Nat.le_trans ?_ (Nat.le_add_right _ 2)
  exact Nat.le_mul_of_pos_left _ hL

/-- The concentration key sits at or beyond the far read's natural. -/
theorem kc_ge_jK (t : Tail) (L ie i : Nat) (tp : t.pos) (hL : 1 ≤ L) : jK t ≤ kc t L ie i := by
  have h := kc_ge t L ie i
  have hj : 2 ^ (ie * jK t) * jK t ≤ keyNum t L ie i := by
    show 2 ^ (ie * jK t) * jK t ≤ cW t * jK t ^ jK t * tauD t L ie i ^ jK t
    have h1 : 2 ^ (ie * jK t) ≤ tauD t L ie i ^ jK t := by
      rw [← powPow 2 ie (jK t)]
      exact Nat.pow_le_pow_left (tauD_ge t L ie i tp hL) _
    have h2 : jK t ≤ cW t * jK t ^ jK t := by
      refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _ (cW_pos t tp))
      show jK t ≤ jK t ^ (exK t + 1)
      rw [Nat.pow_succ]
      exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.succ_pos _))
    rw [Nat.mul_comm (2 ^ (ie * jK t)) (jK t)]
    exact Nat.mul_le_mul h2 h1
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans hj h) (Nat.pow_pos (by decide : 0 < 2))

/-- The concentration key's read: at the key the support weight's cap
against the comparison's second member's power sits at or below the
Pascal count at the raised key against the mass's power, the key's
clearing of the cleared comparison through the falling products'
comparison (`ground.pasc_pow`). -/
theorem conc_key_read (t : Tail) (L ie i : Nat) (tp : t.pos) (hL : 1 ≤ L) :
    cW t * kc t L ie i ^ exK t * tauD t L ie i ^ jK t
      ≤ pasc (kc t L ie i + 1) (jK t) * (2 ^ ie) ^ jK t := by
  have h := kc_ge t L ie i
  have hjK : 0 < jK t ^ jK t := Nat.pow_pos (Nat.succ_pos _)
  have h1 : keyNum t L ie i * kc t L ie i ^ exK t ≤ 2 ^ (ie * jK t) * kc t L ie i ^ jK t := by
    refine Nat.le_trans (Nat.mul_le_mul_right _ h) ?_
    rw [mulAssoc]
    refine Nat.mul_le_mul_left _ ?_
    show kc t L ie i * kc t L ie i ^ exK t ≤ kc t L ie i ^ (exK t + 1)
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.le_refl _
  have h2 : kc t L ie i ^ jK t ≤ jK t ^ jK t * pasc (kc t L ie i + 1) (jK t) := by
    refine Nat.le_trans (Nat.pow_le_pow_left (Nat.le_succ _) _) ?_
    exact pasc_pow (kc t L ie i + 1) (jK t) (Nat.le_succ_of_le (kc_ge_jK t L ie i tp hL))
  have h3 : jK t ^ jK t * (cW t * kc t L ie i ^ exK t * tauD t L ie i ^ jK t)
      ≤ jK t ^ jK t * (pasc (kc t L ie i + 1) (jK t) * (2 ^ ie) ^ jK t) := by
    have e1 : jK t ^ jK t * (cW t * kc t L ie i ^ exK t * tauD t L ie i ^ jK t)
        = keyNum t L ie i * kc t L ie i ^ exK t := by
      show _ = cW t * jK t ^ jK t * tauD t L ie i ^ jK t * kc t L ie i ^ exK t
      exact polEq [jK t ^ jK t, cW t, kc t L ie i ^ exK t, tauD t L ie i ^ jK t]
          (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3))))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 0)) (Mon.var 3)) (Mon.var 2)))
          (by decide +kernel)
    have e2 : 2 ^ (ie * jK t) * (jK t ^ jK t * pasc (kc t L ie i + 1) (jK t))
        = jK t ^ jK t * (pasc (kc t L ie i + 1) (jK t) * (2 ^ ie) ^ jK t) := by
      rw [powPow 2 ie (jK t)]
      exact polEq [2 ^ (ie * jK t), jK t ^ jK t, pasc (kc t L ie i + 1) (jK t)]
          (Pol.mon (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 2))))
          (Pol.mon (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 0))))
          (by decide +kernel)
    rw [e1, ← e2]
    exact Nat.le_trans h1 (Nat.mul_le_mul_left _ h2)
  exact Nat.le_of_mul_le_mul_left h3 hjK

/-- The mode square's square's bit comparison at the second power: the
compared pair's read (`jp_hit`) at the mass's fourth power against its
second. -/
theorem bit_msq (t : Tail) (L ie i : Nat) (tp : t.pos) :
    2 ^ (2 * ie) * (pairX t L ie i * pairX t L ie i) * (qPlus t * qPlus t)
      ≤ 2 ^ jp t L ie i * pairDen t := by
  refine Nat.le_trans ?_ (jp_hit t L ie i tp)
  show 2 ^ (2 * ie) * (pairX t L ie i * pairX t L ie i) * (qPlus t * qPlus t)
    ≤ qPlus t ^ 2 * 2 ^ (4 * ie) * pairX t L ie i ^ 2
  rw [sqRead, sqRead, show 4 * ie = 2 * ie + 2 * ie from fourMul ie, powAdd]
  have e : qPlus t * qPlus t * (2 ^ (2 * ie) * 2 ^ (2 * ie)) * (pairX t L ie i * pairX t L ie i)
      = 2 ^ (2 * ie) * (pairX t L ie i * pairX t L ie i) * (qPlus t * qPlus t) * 2 ^ (2 * ie) :=
    polEq [qPlus t, 2 ^ (2 * ie), pairX t L ie i]
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.mul (Mon.var 2) (Mon.var 2))))
      (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.var 1)))
      (by decide +kernel)
  rw [e]
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0 < 2))

/-- The mode square's bit comparison at the second power: the mass's
second power against the compared pair's root, the trichotomy of
squares at the compared pair's read (`jp_hit`). -/
theorem bit_mode (t : Tail) (L ie i : Nat) (tp : t.pos) :
    2 ^ (2 * ie) * pairX t L ie i * qPlus t ≤ 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2) := by
  refine leOfSqLe ?_
  have hp : 2 ^ (2 * ie) * pairX t L ie i * qPlus t * (2 ^ (2 * ie) * pairX t L ie i * qPlus t)
      = pairNum t L ie i := by
    show _ = qPlus t ^ 2 * 2 ^ (4 * ie) * pairX t L ie i ^ 2
    rw [sqRead, sqRead, show 4 * ie = 2 * ie + 2 * ie from fourMul ie, powAdd]
    exact polEq [2 ^ (2 * ie), pairX t L ie i, qPlus t]
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)) (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2))))
          (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 2)) (Mon.mul (Mon.var 0) (Mon.var 0))) (Mon.mul (Mon.var 1) (Mon.var 1))))
          (by decide +kernel)
  have hd : 2 ^ jp t L ie i * pairDen t
      ≤ 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2) * (2 ^ jp t L ie i * (t.kappa * t.dG * t.W2)) := by
    show 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2) ^ 2 ≤ _
    rw [sqRead]
    have e : 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2) * (2 ^ jp t L ie i * (t.kappa * t.dG * t.W2))
        = 2 ^ jp t L ie i * (t.kappa * t.dG * t.W2 * (t.kappa * t.dG * t.W2)) * 2 ^ jp t L ie i :=
      polEq [2 ^ jp t L ie i, t.kappa, t.dG, t.W2]
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3))) (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 2)) (Mon.var 3)))) (Mon.var 0)))
        (by decide +kernel)
    rw [e]
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide : 0 < 2))
  rw [hp]
  exact Nat.le_trans (jp_hit t L ie i tp) hd

/-- The unit weight's bit comparison at the second power: at the
member read `dim G ≤ 32 d_θ #p (L + 2)` and the near mass at or below
`[1 : 4]` (the support weight's coefficient at or beyond two at the
occupied link count), the compared pair's read
puts the mass's second power against the near mass's second member
under the bit count's power. -/
theorem bit_unit (t : Tail) (L ie i : Nat) (tp : t.pos)
    (hdG : t.dG ≤ 32 * t.dth * t.np * (L + 2)) :
    2 ^ (2 * ie) * (2 * cW t * kc t L ie i ^ exK t) ≤ 2 ^ jp t L ie i := by
  have hkc : 1 ≤ kc t L ie i ^ exK t := Nat.pow_pos (kc_pos t L ie i tp)
  have hcW : 2 ≤ cW t := by
    show 2 ≤ t.A ^ (3 * t.nl) * (9 * t.g) ^ exK t
    refine Nat.le_trans ?_ (Nat.le_mul_of_pos_left _ (Nat.pow_pos tp.2.2.2.2.1))
    have h1 : 1 ≤ exK t :=
      Nat.mul_pos (Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_add_left 1 _))
        tp.2.2.2.2.2.2.2.2
    refine Nat.le_trans ?_ (Nat.pow_le_pow_right (Nat.mul_pos (by decide : 0 < 9) tp.2.1) h1)
    rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    exact Nat.le_trans (by decide : 2 ≤ 9) (Nat.le_mul_of_pos_right 9 tp.2.1)
  have hvd : 4 ≤ 2 * cW t * kc t L ie i ^ exK t := by
    refine Nat.le_trans ?_ (Nat.le_mul_of_pos_right _ hkc)
    exact Nat.mul_le_mul_left 2 hcW
  have hden : pairDen t ≤ 64 * (L + 2) * (L + 2) * (qPlus t * qPlus t) := by
    show (t.kappa * t.dG * t.W2) ^ 2 ≤ _
    rw [sqRead]
    have h1 : t.kappa * t.dG * t.W2 ≤ 8 * (L + 2) * qPlus t := by
      have e : 8 * (L + 2) * qPlus t = t.kappa * (32 * t.dth * t.np * (L + 2)) * t.W2 := by
        show 8 * (L + 2) * (4 * t.kappa * t.dth * t.np * t.W2) = _
        exact polEq [L, t.kappa, t.dth, t.np, t.W2]
          (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 1)) (Mon.var 2)) (Mon.var 3)) (Mon.var 4))))
          (Pol.mul (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.cst 32) (Mon.var 2)) (Mon.var 3))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))))) (Pol.mon (Mon.var 4)))
          (by decide +kernel)
      rw [e]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdG)
    refine Nat.le_trans (Nat.mul_le_mul h1 h1) (Nat.le_of_eq ?_)
    exact polEq [L, qPlus t]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mul (Pol.mon (Mon.cst 8)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.var 1))))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 64)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 1) (Mon.var 1))))
          (by decide +kernel)
  have hnum : pairNum t L ie i
      = 16 * (L + 2) * (L + 2) * (qPlus t * qPlus t)
        * (2 ^ (2 * ie) * 2 ^ (2 * ie) * (2 ^ i * 2 ^ i)
          * (2 * cW t * kc t L ie i ^ exK t * (2 * cW t * kc t L ie i ^ exK t))) := by
    show qPlus t ^ 2 * 2 ^ (4 * ie) * (2 ^ i * 8 * cW t * kc t L ie i ^ exK t * (L + 2)) ^ 2 = _
    rw [sqRead, sqRead, show 4 * ie = 2 * ie + 2 * ie from fourMul ie, powAdd]
    exact polEq [qPlus t, 2 ^ (2 * ie), 2 ^ i, cW t, kc t L ie i ^ exK t, L]
          (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1)))) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.cst 8)) (Mon.var 3)) (Mon.var 4))) (Pol.add (Pol.mon (Mon.var 5)) (Pol.mon (Mon.cst 2)))) (Pol.mul (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 2) (Mon.cst 8)) (Mon.var 3)) (Mon.var 4))) (Pol.add (Pol.mon (Mon.var 5)) (Pol.mon (Mon.cst 2))))))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 16)) (Pol.add (Pol.mon (Mon.var 5)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.var 5)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 1) (Mon.var 1)) (Mon.mul (Mon.var 2) (Mon.var 2))) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 3)) (Mon.var 4)) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 3)) (Mon.var 4))))))
          (by decide +kernel)
  have hq : 1 ≤ 16 * (L + 2) * (L + 2) * (qPlus t * qPlus t) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 16) (Nat.succ_pos _)) (Nat.succ_pos _))
      (Nat.mul_pos (qPlus_pos t tp) (qPlus_pos t tp))
  have h1 : 2 ^ (2 * ie) * 2 ^ (2 * ie) * (2 ^ i * 2 ^ i)
        * (2 * cW t * kc t L ie i ^ exK t * (2 * cW t * kc t L ie i ^ exK t))
      ≤ 4 * 2 ^ jp t L ie i := by
    refine Nat.le_of_mul_le_mul_left ?_ hq
    rw [← hnum]
    refine Nat.le_trans (jp_hit t L ie i tp) ?_
    refine Nat.le_trans (Nat.mul_le_mul_left _ hden) (Nat.le_of_eq ?_)
    exact polEq [2 ^ jp t L ie i, L, qPlus t]
          (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 64)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))))
          (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 16)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) (Pol.mon (Mon.mul (Mon.cst 4) (Mon.var 0))))
          (by decide +kernel)
  have h2 : 4 * (2 ^ (2 * ie) * (2 * cW t * kc t L ie i ^ exK t))
      ≤ 2 ^ (2 * ie) * 2 ^ (2 * ie) * (2 ^ i * 2 ^ i)
        * (2 * cW t * kc t L ie i ^ exK t * (2 * cW t * kc t L ie i ^ exK t)) := by
    have e : 2 ^ (2 * ie) * 2 ^ (2 * ie) * (2 ^ i * 2 ^ i)
          * (2 * cW t * kc t L ie i ^ exK t * (2 * cW t * kc t L ie i ^ exK t))
        = 2 * cW t * kc t L ie i ^ exK t * (2 ^ (2 * ie) * (2 * cW t * kc t L ie i ^ exK t))
          * (2 ^ (2 * ie) * (2 ^ i * 2 ^ i)) :=
      polEq [2 ^ (2 * ie), 2 ^ i, cW t, kc t L ie i ^ exK t]
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0)) (Mon.mul (Mon.var 1) (Mon.var 1))) (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3)))))
        (Pol.mon (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3)) (Mon.mul (Mon.var 0) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 2)) (Mon.var 3)))) (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 1) (Mon.var 1)))))
        (by decide +kernel)
    rw [e]
    refine Nat.le_trans (Nat.mul_le_mul_right _ hvd) ?_
    exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2))
      (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) (Nat.pow_pos (by decide : 0 < 2))))
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans h2 h1) (by decide : 0 < 4)

/-! The stated pairs at the key's side. -/

/-- The deviation's member pair `m_θ := c_θ² κ_θ + h_θ + 1`. -/
def mth (t : Tail) : Nat := t.c2 * t.kappa + t.hth + 1

/-- The deviation's pair in the side,
`Θ_R := 24 κ g² L³ + 24 g h_θ² L² + 3 g (g + 1) c_θ² L⁴`. -/
def thetaR (t : Tail) (L : Nat) : Nat :=
  24 * t.kappa * (t.g * t.g) * (L * L * L) + 24 * t.g * (t.hth * t.hth) * (L * L)
    + 3 * t.g * (t.g + 1) * t.c2 * (L * L * L * L)

/-- The deviation's square's read `T_R := 1 + Θ_R`. -/
def tR (t : Tail) (L : Nat) : Nat := 1 + thetaR t L

/-- The derivative's remainder's pair `ϱ₁ := C₂(θ) + m_θ (1 + 2 g² L)`. -/
def rho1 (t : Tail) (L : Nat) : Nat := t.C2 + mth t * (1 + 2 * (t.g * t.g) * L)

/-- The generator's read's gap pair
`ϱ₂ := 12 g h_θ² + 24 κ² g³ L + 6 κ g L c_θ²`. -/
def rho2 (t : Tail) (L : Nat) : Nat :=
  12 * t.g * (t.hth * t.hth) + 24 * (t.kappa * t.kappa) * (t.g * t.g * t.g) * L
    + 6 * t.kappa * t.g * L * t.c2

/-- The dual weights' fold `C₁ := 1 + 2 κ #ℓ`. -/
def c1 (t : Tail) : Nat := 1 + 2 * t.kappa * t.nl

/-- The roots' floor's pair `W₀ := 1 + 8 κ g`. -/
def w0 (t : Tail) : Nat := 1 + 8 * t.kappa * t.g

/-- The deficits' fold's pair `C_D := 2 dim G W₀ + 1`. -/
def cD (t : Tail) : Nat := 2 * t.dG * w0 t + 1

/-- The mode weight's deficit moment's pair
`C_Z := 2 dim G W₀ #p + 8 W₀² (L + 2)`. -/
def cZ (t : Tail) (L : Nat) : Nat := 2 * t.dG * w0 t * t.np + 8 * (w0 t * w0 t) * (L + 2)

/-- The off-range residual's pair `c_off` at the direction gap's
predecessor, the sum's unit at two directions. -/
def cOff (t : Tail) (L : Nat) : Nat :=
  2 * t.kappa * (t.g - 1) * (L * L)
    * (216 * (7 + 6 * t.dth) ^ 8
      + 12 * (3 + t.dth) ^ 2 * (8 * (t.g * t.g * t.g) * (L * L * L) + 1))

/-- The dual weights' fold at the profile `C_W := C₁ |W|²`. -/
def cWd (t : Tail) : Nat := c1 t * t.W2

/-- The remainder's pair `a₁ := W₀² C_W |W|_∞ ϱ₁`. -/
def a1 (t : Tail) (L : Nat) : Nat := w0 t * w0 t * cWd t * t.Winf * rho1 t L

/-- The stated pairs' clearing `2 κ² d_θ`, the second members of `c'_q`,
`c_q`, `W_q` and `P'` at one product. -/
def pairClr (t : Tail) : Nat := 2 * (t.kappa * t.kappa) * t.dth

/-- The deficit's second-order pair `c'_q := c_ϱ [1 : 2] + [1 : 2 d_θ]`
at the clearing, `κ (4 dim G c_θ² d_θ + κ)`. -/
def cqp (t : Tail) : Nat := t.kappa * (4 * t.dG * t.c2 * t.dth + t.kappa)

/-- The slack's pair `c_q := c'_q + c_off [1 : 2 κ]` at the clearing. -/
def cq (t : Tail) (L : Nat) : Nat := cqp t + t.kappa * cOff t L * t.dth

/-- The slack's cap `W_q := [1 : 2] d_θ #p (C₂(θ) D₊ + Ω)²` at the
clearing, `D₊ = 2 g`. -/
def wq (t : Tail) : Nat :=
  t.kappa * t.kappa * t.dth * (t.dth * t.np * (2 * t.C2 * t.g + t.Om) ^ 2)

/-- The mode weight's remainder pair `P'` at the clearing, a polynomial
in the near scale. -/
def ppC (t : Tail) (L : Nat) : Poly4 :=
  ⟨8 * (t.kappa * t.kappa) * t.dth * (1 + 2 * t.dG),
    52 * t.dth * t.np * (c1 t * c1 t) * rho2 t L * (L + 2)
      + 52 * (t.kappa * t.kappa) * t.dth * (w0 t * w0 t) * (L + 2),
    64 * t.kappa * t.dth * t.np * (c1 t * c1 t) * (tR t L * tR t L) * (1 + 2 * t.dG)
      + (16 * t.kappa * t.dth * cOff t L + 8 * cqp t) * (1 + 2 * t.dG),
    0, 0⟩

/-- The excess's scale pair `P_u` at the clearing: the clearing's
multiple of `24 Θ_R K² + 3 C_D #p + Ω C_D #p` joined to `2 c_q K² + W_q`
at their own. -/
def puC (t : Tail) (L : Nat) : Poly4 :=
  (Poly4.scale (pairClr t)
    ⟨3 * (cD t * t.np) + t.Om * (cD t * t.np), 0, 24 * thetaR t L, 0, 0⟩).add
    ⟨wq t, 0, 2 * cq t L, 0, 0⟩

/-- The mode read's scale pair `P_v` at the clearing: the clearing's
multiple of `32 K ϱ₂ #ℓ (L + 2) + (6 + Ω) C_Z + 96 Θ_R (1 + 2 dim G) K²`
joined to `(384 g κ + 6 + Ω) P'` and to `4 c_q (1 + 2 dim G) K² + W_q`
at their own. -/
def pvC (t : Tail) (L : Nat) : Poly4 :=
  (Poly4.scale (pairClr t) ⟨(6 + t.Om) * cZ t L, 32 * (rho2 t L * t.nl * (L + 2)),
      96 * (thetaR t L * (1 + 2 * t.dG)), 0, 0⟩).add
    ((Poly4.scale (384 * (t.g * t.kappa) + 6 + t.Om) (ppC t L)).add
      ⟨wq t, 0, 4 * (cq t L * (1 + 2 * t.dG)), 0, 0⟩)

/-- The excess's pair reads `excess_read`'s group: the clearing's
multiple of `24 Θ_R K² + 3 C_D #p + Ω C_D #p` joined to `2 c_q K²` and
`W_q` at the clearing. -/
theorem puC_read (t : Tail) (L K : Nat) :
    (puC t L).at K
      = pairClr t * (24 * (thetaR t L * (K * K)) + 3 * (cD t * t.np) + t.Om * (cD t * t.np))
        + 2 * (cq t L * (K * K)) + wq t := by
  show Poly4.at ((Poly4.scale (pairClr t)
      ⟨3 * (cD t * t.np) + t.Om * (cD t * t.np), 0, 24 * thetaR t L, 0, 0⟩).add
      ⟨wq t, 0, 2 * cq t L, 0, 0⟩) K = _
  rw [Poly4.at_add, Poly4.at_scale, Poly4.at_three, Poly4.at_three, Nat.zero_mul K,
    Nat.add_zero (3 * (cD t * t.np) + t.Om * (cD t * t.np)), Nat.add_zero (wq t),
    mulAssoc 24 (thetaR t L) (K * K), mulAssoc 2 (cq t L) (K * K),
    Nat.add_comm (3 * (cD t * t.np) + t.Om * (cD t * t.np)) (24 * (thetaR t L * (K * K))),
    ← Nat.add_assoc (24 * (thetaR t L * (K * K))), ← Nat.add_assoc,
    Nat.add_right_comm _ (wq t) (2 * (cq t L * (K * K)))]

/-- The mode read's pair reads `mode_read`'s group at `P'`'s own read. -/
theorem pvC_read (t : Tail) (L K : Nat) :
    (pvC t L).at K
      = pairClr t * (32 * (K * rho2 t L * t.nl * (L + 2)) + (6 + t.Om) * cZ t L
          + 96 * (thetaR t L * (K * K) * (1 + 2 * t.dG)))
        + (384 * (t.g * t.kappa) + 6 + t.Om) * (ppC t L).at K
        + 4 * (cq t L * (K * K) * (1 + 2 * t.dG)) + wq t := by
  show Poly4.at ((Poly4.scale (pairClr t) ⟨(6 + t.Om) * cZ t L,
      32 * (rho2 t L * t.nl * (L + 2)), 96 * (thetaR t L * (1 + 2 * t.dG)), 0, 0⟩).add
      ((Poly4.scale (384 * (t.g * t.kappa) + 6 + t.Om) (ppC t L)).add
        ⟨wq t, 0, 4 * (cq t L * (1 + 2 * t.dG)), 0, 0⟩)) K = _
  rw [Poly4.at_add, Poly4.at_add, Poly4.at_scale, Poly4.at_scale, Poly4.at_three,
    Poly4.at_three, Nat.zero_mul K, Nat.add_zero (wq t)]
  have e1 : 32 * (rho2 t L * t.nl * (L + 2)) * K = 32 * (K * rho2 t L * t.nl * (L + 2)) :=
    ground.monEq [rho2 t L, t.nl, L + 2, K]
      (Mon.mul (Mon.mul (Mon.cst 32) (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.var 2)))
        (Mon.var 3))
      (Mon.mul (Mon.cst 32) (Mon.mul (Mon.mul (Mon.mul (Mon.var 3) (Mon.var 0)) (Mon.var 1))
        (Mon.var 2)))
      (by decide +kernel) (by decide +kernel)
  have e2 : 96 * (thetaR t L * (1 + 2 * t.dG)) * (K * K)
      = 96 * (thetaR t L * (K * K) * (1 + 2 * t.dG)) :=
    ground.monEq [thetaR t L, 1 + 2 * t.dG, K]
      (Mon.mul (Mon.mul (Mon.cst 96) (Mon.mul (Mon.var 0) (Mon.var 1)))
        (Mon.mul (Mon.var 2) (Mon.var 2)))
      (Mon.mul (Mon.cst 96) (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 2) (Mon.var 2)))
        (Mon.var 1)))
      (by decide +kernel) (by decide +kernel)
  have e3 : 4 * (cq t L * (1 + 2 * t.dG)) * (K * K) = 4 * (cq t L * (K * K) * (1 + 2 * t.dG)) :=
    ground.monEq [cq t L, 1 + 2 * t.dG, K]
      (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.var 1)))
        (Mon.mul (Mon.var 2) (Mon.var 2)))
      (Mon.mul (Mon.cst 4) (Mon.mul (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 2) (Mon.var 2)))
        (Mon.var 1)))
      (by decide +kernel) (by decide +kernel)
  rw [e1, e2, e3, Nat.add_comm ((6 + t.Om) * cZ t L) (32 * (K * rho2 t L * t.nl * (L + 2))),
    ← Nat.add_assoc, ← Nat.add_assoc,
    Nat.add_right_comm _ (wq t) (4 * (cq t L * (K * K) * (1 + 2 * t.dG)))]

/-! The key. -/

/-- The side key's comparison: the mode read under a quarter of the
floor, `1280 κ (L + 2) f_d < f_n (L² + 2L + 2)` at `e_W`'s pair. -/
def sideRead (kappa fn fd L : Nat) : Prop :=
  1280 * kappa * (L + 2) * fd < fn * (L * L + 2 * L + 2)

instance instCornerkey5 (kappa fn fd L : Nat) : Decidable (sideRead kappa fn fd L) :=
  inferInstanceAs (Decidable (_ < _))

/-- The comparison holds at every side at or beyond the witness
`1280 κ f_d`: there `L (L + 2)` sits at or beyond `1280 κ f_d (L + 2)`,
under `L² + 2L + 2`. -/
theorem sideRead_beyond (kappa fn fd L : Nat) (hfn : 1 ≤ fn) (hW : 1280 * kappa * fd ≤ L) :
    sideRead kappa fn fd L := by
  show 1280 * kappa * (L + 2) * fd < fn * (L * L + 2 * L + 2)
  have e : 1280 * kappa * (L + 2) * fd = 1280 * kappa * fd * (L + 2) :=
    ground.monEq [kappa, L + 2, fd]
      (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1280) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))
      (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1280) (Mon.var 0)) (Mon.var 2)) (Mon.var 1))
      (by decide +kernel) (by decide +kernel)
  rw [e]
  have h1 : 1280 * kappa * fd * (L + 2) ≤ L * (L + 2) := Nat.mul_le_mul_right _ hW
  have h2 : L * (L + 2) < L * L + 2 * L + 2 := by
    rw [Nat.mul_add, Nat.mul_comm L 2]
    exact Nat.lt_add_of_pos_right (by decide : 0 < 2)
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt h1 h2) (Nat.le_mul_of_pos_left _ hfn)

/-- The side key, the least side at or beyond one at the comparison,
its witness the side `1280 κ f_d`. -/
def sideKey (kappa fn fd : Nat) : Nat := firstAt (sideRead kappa fn fd) 1 (1280 * kappa * fd)

/-- The comparison holds at the side key. -/
theorem sideKey_hit (kappa fn fd : Nat) (hfn : 1 ≤ fn) :
    sideRead kappa fn fd (sideKey kappa fn fd) :=
  firstAt_hit (sideRead kappa fn fd) (1280 * kappa * fd) 1
    (sideRead_beyond kappa fn fd _ hfn (Nat.le_add_left _ 1))

/-- The side key sits at or beyond one. -/
theorem sideKey_ge (kappa fn fd : Nat) : 1 ≤ sideKey kappa fn fd :=
  firstAt_ge (sideRead kappa fn fd) (1280 * kappa * fd) 1

/-- The side key is least at the comparison. -/
theorem sideKey_least (kappa fn fd L : Nat) (hL : 1 ≤ L) (hlt : L < sideKey kappa fn fd) :
    ¬ sideRead kappa fn fd L :=
  firstAt_below (sideRead kappa fn fd) (1280 * kappa * fd) 1 L hL hlt

/-- The two mass reads' coefficient `4 g κ (192 C_D #p + 384 C_Z)`. -/
def massX (t : Tail) (L : Nat) : Nat :=
  4 * (t.g * t.kappa * (192 * (cD t * t.np) + 384 * cZ t L))

/-- The mass key's comparison at the `i`-th halving: the two mass reads
under a further quarter of the floor, `4 g κ (192 C_D #p + 384 C_Z) f_d <
f_n 4^i` at the mass `[1 : 2^i]`. -/
def massRead (t : Tail) (L fn fd i : Nat) : Prop := massX t L * fd < fn * 4 ^ i

instance instCornerkey6 (t : Tail) (L fn fd i : Nat) : Decidable (massRead t L fn fd i) :=
  inferInstanceAs (Decidable (_ < _))

/-- The comparison holds at every halving index at or beyond the
exponent `4 g κ (192 C_D #p + 384 C_Z) f_d`, the power of four beyond
its exponent at every natural. -/
theorem massRead_beyond (t : Tail) (L fn fd i : Nat) (hfn : 1 ≤ fn)
    (hi : massX t L * fd ≤ i) : massRead t L fn fd i := by
  show massX t L * fd < fn * 4 ^ i
  exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hi (Nat.lt_pow_self (by decide : 1 < 4)))
    (Nat.le_mul_of_pos_left _ hfn)

/-- The mass key, the least halving index at the comparison, its
witness the exponent itself. -/
def massKey (t : Tail) (L fn fd : Nat) : Nat :=
  firstAt (massRead t L fn fd) 0 (massX t L * fd)

/-- The comparison holds at the mass key. -/
theorem massKey_hit (t : Tail) (L fn fd : Nat) (hfn : 1 ≤ fn) :
    massRead t L fn fd (massKey t L fn fd) :=
  firstAt_hit (massRead t L fn fd) (massX t L * fd) 0
    (massRead_beyond t L fn fd _ hfn (Nat.le_add_left _ 0))

/-- The mass key is least at the comparison. -/
theorem massKey_least (t : Tail) (L fn fd i : Nat) (hlt : i < massKey t L fn fd) :
    ¬ massRead t L fn fd i :=
  firstAt_below (massRead t L fn fd) (massX t L * fd) 0 i (Nat.zero_le i) hlt

/-- The corner cell's extent read at the scale `[1 : 2^i]`: the read
`d₁ ≤ n₁ 2^i` at the trichotomy of squares is the scale's ray
`[η² : 1] = [1 : 4^i]` in the extent at the squares' read,
`1 · d₁² ≤ n₁² 4^i`. -/
theorem extent_read (n1 d1 i : Nat) :
    d1 ≤ n1 * 2 ^ i ↔ 1 * (d1 * d1) ≤ n1 * n1 * 4 ^ i := by
  have e : n1 * n1 * 4 ^ i = n1 * 2 ^ i * (n1 * 2 ^ i) := by
    rw [fourPow, Nat.mul_comm 2 i, Nat.mul_two, powAdd, mulMulMulComm]
  rw [Nat.one_mul, e]
  constructor
  · intro h
    exact Nat.mul_le_mul h h
  · intro h
    refine Nat.le_of_not_lt (fun hlt => ?_)
    have h1 : n1 * 2 ^ i * (n1 * 2 ^ i) < d1 * d1 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt hlt))
        (Nat.mul_lt_mul_of_pos_right hlt (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt))
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h h1)

/-- The key's list at a side and a floor pair, each comparison cleared
at the pairs' second members: the scale comparison `4 (P_u + P_v) η <
φ` first, then the deficit cell's two comparisons, `η (dim G + 2) ≤ 1`,
the remainder cell's four, and the corner cell's extent at the
trichotomy of squares (`extent_read`). -/
def tailCmps (t : Tail) (L fn fd : Nat) : List Cmp :=
  [⟨(Poly4.scale (2 * fd) ((puC t L).add (pvC t L))).add ⟨1, 0, 0, 0, 0⟩,
      t.kappa * t.kappa * t.dth * fn⟩,
   ⟨⟨2 * t.np * c1 t * rho1 t L, 0, 0, 0, 0⟩, t.kappa⟩,
   ⟨⟨0, 0, 16 * (c1 t * c1 t) * (tR t L * tR t L) * t.dth + 8 * cOff t L * t.dth
      + 16 * t.dG * t.c2 * t.dth + 4 * t.kappa, 0, 0⟩, 2 * t.kappa * t.dth⟩,
   ⟨⟨t.dG + 2, 0, 0, 0, 0⟩, 1⟩,
   ⟨⟨0, 32 * a1 t L * (L + 2), 0, 0, 0⟩, t.kappa * t.W2⟩,
   ⟨⟨0, 8 * (L + 2) * (2 * a1 t L * t.kappa * t.W2
      + 16 * w0 t ^ 4 * (cWd t * cWd t) * rho2 t L * (t.Winf * t.Winf) * (L + 2)), 0, 0, 0⟩,
     t.kappa * t.kappa * (t.W2 * t.W2)⟩,
   ⟨⟨0, 0, 4096 * ((L + 2) * (L + 2)) * w0 t ^ 5 * (cWd t * cWd t) * (tR t L * tR t L)
        * t.kappa * t.dG * t.W2,
      8192 * ((L + 2) * (L + 2)) * w0 t ^ 4 * (cWd t * cWd t) * (tR t L * tR t L) * a1 t L,
      16384 * ((L + 2) * (L + 2)) * w0 t ^ 8 * cWd t ^ 4 * tR t L ^ 4⟩,
     t.kappa * t.kappa * (t.W2 * t.W2)⟩,
   ⟨⟨0, 0, 1088 * ((L + 2) * (L + 2)) * w0 t ^ 5 * (cWd t * cWd t) * (tR t L * tR t L)
        * (t.kappa * t.kappa) * (t.dG + 2) * (t.W2 * t.W2),
      1024 * ((L + 2) * (L + 2)) * w0 t ^ 4 * (cWd t * cWd t) * (tR t L * tR t L)
        * (2 * a1 t L * t.kappa * t.W2
          + 16 * w0 t ^ 4 * (cWd t * cWd t) * rho2 t L * (t.Winf * t.Winf) * (L + 2)),
      4096 * ((L + 2) * (L + 2)) * w0 t ^ 8 * cWd t ^ 4 * tR t L ^ 4 * t.kappa * t.W2⟩,
     t.kappa * t.kappa * t.kappa * (t.W2 * t.W2 * t.W2)⟩,
   ⟨⟨t.d1, 0, 0, 0, 0⟩, t.n1⟩]

/-- Every cap of the list sits at or beyond one at the stated data. -/
theorem tailCaps (t : Tail) (L fn fd : Nat) (tp : t.pos) (hfn : 1 ≤ fn) :
    listCaps (tailCmps t L fn fd) := by
  have hk : 1 ≤ t.kappa := tp.1
  have hd : 1 ≤ t.dth := tp.2.2.2.1
  have hW : 1 ≤ t.W2 := tp.2.2.2.2.2.2.1
  have hkW : 1 ≤ t.kappa * t.W2 := Nat.mul_pos hk hW
  have hkW2 : 1 ≤ t.kappa * t.kappa * (t.W2 * t.W2) :=
    Nat.mul_pos (Nat.mul_pos hk hk) (Nat.mul_pos hW hW)
  have h0 : 1 ≤ t.kappa * t.kappa * t.dth * fn := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hk hk) hd) hfn
  have h2 : 1 ≤ 2 * t.kappa * t.dth := Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hk) hd
  have h7 : 1 ≤ t.kappa * t.kappa * t.kappa * (t.W2 * t.W2 * t.W2) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hk hk) hk) (Nat.mul_pos (Nat.mul_pos hW hW) hW)
  have h8 : 1 ≤ t.n1 := tp.2.2.2.2.2.2.2.1
  show (decide (1 ≤ t.kappa * t.kappa * t.dth * fn) && (decide (1 ≤ t.kappa)
    && (decide (1 ≤ 2 * t.kappa * t.dth) && (decide (1 ≤ 1) && (decide (1 ≤ t.kappa * t.W2)
    && (decide (1 ≤ t.kappa * t.kappa * (t.W2 * t.W2))
    && (decide (1 ≤ t.kappa * t.kappa * (t.W2 * t.W2))
    && (decide (1 ≤ t.kappa * t.kappa * t.kappa * (t.W2 * t.W2 * t.W2))
    && (decide (1 ≤ t.n1) && true))))))))) = true
  rw [decide_eq_true h0, decide_eq_true hk, decide_eq_true h2, decide_eq_true (Nat.le_refl 1),
    decide_eq_true hkW, decide_eq_true hkW2, decide_eq_true h7, decide_eq_true h8]
  rfl

/-- The key's comparison at the `i`-th halving and a near scale: the
key's list at the scale `[1 : 2^i]` and the near scale, with the near
scale clearing `6 b_K`. -/
def tailReadAt (t : Tail) (L ie fn fd i K : Nat) : Prop :=
  listRead (tailCmps t L fn fd) (2 ^ i) K ∧ 6 * bK t ie ≤ K

instance instCornerkey7 (t : Tail) (L ie fn fd i K : Nat) : Decidable (tailReadAt t L ie fn fd i K) :=
  @instDecidableAnd _ _ (inferInstanceAs (Decidable (listRead _ _ _))) (Nat.decLe _ _)

/-- The scale key's comparison at the `i`-th halving: the key's
comparison at the near scale there. -/
def tailRead (t : Tail) (L ie fn fd i : Nat) : Prop :=
  tailReadAt t L ie fn fd i (nearScale t L ie i)

instance instCornerkey8 (t : Tail) (L ie fn fd i : Nat) : Decidable (tailRead t L ie fn fd i) :=
  inferInstanceAs (Decidable (tailReadAt _ _ _ _ _ _ _))

/-- The scale key's witness: the `(3b + d)`-th halving joined to `32`
and to the list's reads summed at one growth past the near scale
there. -/
def tailWit (t : Tail) (L ie fn fd : Nat) : Nat :=
  3 * bGrow t + denBits t + 32
    + listAt (tailCmps t L fn fd) (nearScale t L ie (3 * bGrow t + denBits t) + bK t ie)

/-- The comparison holds at the witness, read at the search's own
start, the count from the unit index. -/
theorem tailRead_witness (t : Tail) (L ie fn fd : Nat) (tp : t.pos) (hfn : 1 ≤ fn) :
    tailRead t L ie fn fd (0 + tailWit t L ie fn fd) := by
  show tailRead t L ie fn fd (0 + (3 * bGrow t + denBits t + 32
    + listAt (tailCmps t L fn fd) (nearScale t L ie (3 * bGrow t + denBits t) + bK t ie)))
  rw [Nat.zero_add, Nat.add_assoc]
  refine ⟨?_, nearScale_clear t L ie _ tp⟩
  have hw := listRead_witness (tailCmps t L fn fd) (2 ^ (3 * bGrow t + denBits t))
    (nearScale t L ie (3 * bGrow t + denBits t)) (bK t ie)
    (32 + listAt (tailCmps t L fn fd) (nearScale t L ie (3 * bGrow t + denBits t) + bK t ie))
    (tailCaps t L fn fd tp hfn) (Nat.pow_pos (by decide : 0 < 2)) (Nat.le_add_right 32 _)
    (Nat.le_add_left _ 32)
  rw [← powAdd 2 (3 * bGrow t + denBits t)] at hw
  exact listRead_le _ _ _ _ hw (nearScale_lin t L ie (3 * bGrow t + denBits t) tp _)

/-- The comparison holding at a halving holds at the next: the list at
its half past the clearing and the clearing at the monotone near scale. -/
theorem tailRead_step (t : Tail) (L ie fn fd i : Nat) (tp : t.pos)
    (h : tailRead t L ie fn fd i) : tailRead t L ie fn fd (i + 1) := by
  refine ⟨?_, Nat.le_trans h.2 (nearScale_mono t L ie i tp)⟩
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ i) 2]
  exact listRead_half _ _ _ _ (bK t ie) h.1 h.2 (nearScale_step t L ie i tp)

/-- The comparison holding at a halving holds at every further one. -/
theorem tailRead_all (t : Tail) (L ie fn fd i : Nat) (tp : t.pos) (h : tailRead t L ie fn fd i) :
    ∀ u : Nat, tailRead t L ie fn fd (i + u)
  | 0 => h
  | u + 1 => tailRead_step t L ie fn fd (i + u) tp (tailRead_all t L ie fn fd i tp h u)

/-- The scale key, the least halving index at the comparison, one
bounded search at the witness's halving count. -/
def tailKey (t : Tail) (L ie fn fd : Nat) : Nat :=
  firstAt (tailRead t L ie fn fd) 0 (tailWit t L ie fn fd)

/-- The comparison holds at the scale key. -/
theorem tailKey_hit (t : Tail) (L ie fn fd : Nat) (tp : t.pos) (hfn : 1 ≤ fn) :
    tailRead t L ie fn fd (tailKey t L ie fn fd) :=
  firstAt_hit (tailRead t L ie fn fd) (tailWit t L ie fn fd) 0
    (tailRead_witness t L ie fn fd tp hfn)

/-- The scale key is least at the comparison. -/
theorem tailKey_least (t : Tail) (L ie fn fd i : Nat) (hlt : i < tailKey t L ie fn fd) :
    ¬ tailRead t L ie fn fd i :=
  firstAt_below (tailRead t L ie fn fd) (tailWit t L ie fn fd) 0 i (Nat.zero_le i) hlt

/-- At every scale under the key the key's list holds with the
clearing. -/
theorem tailKey_all (t : Tail) (L ie fn fd : Nat) (tp : t.pos) (hfn : 1 ≤ fn) (u : Nat) :
    tailRead t L ie fn fd (tailKey t L ie fn fd + u) :=
  tailRead_all t L ie fn fd _ tp (tailKey_hit t L ie fn fd tp hfn) u

/-- A halving at the comparison sits at or beyond the key. -/
theorem tailKey_le (t : Tail) (L ie fn fd i : Nat) (h : tailRead t L ie fn fd i) :
    tailKey t L ie fn fd ≤ i := by
  cases Nat.lt_or_ge i (tailKey t L ie fn fd) with
  | inl hlt => exact absurd h (tailKey_least t L ie fn fd i hlt)
  | inr hge => exact hge

/-- A halving off the comparison sits under the key. -/
theorem tailKey_ge (t : Tail) (L ie fn fd i : Nat) (tp : t.pos) (hfn : 1 ≤ fn)
    (h : ¬ tailRead t L ie fn fd i) : i < tailKey t L ie fn fd := by
  cases Nat.lt_or_ge i (tailKey t L ie fn fd) with
  | inl hlt => exact hlt
  | inr hge =>
    obtain ⟨u, hu⟩ := Nat.le.dest hge
    rw [← hu] at h
    exact absurd (tailKey_all t L ie fn fd tp hfn u) h

/-- The scale key's search walked with the bit count's chain: at a
halving and its bit count, the key's comparison at the near scale
there, or the walk one halving on at the bit count searched from the
prior within the growth. -/
def keyWalk (t : Tail) (L ie fn fd : Nat) : Nat → Nat → Nat → Nat
  | i, _, 0 => i
  | i, j, f + 1 =>
    if tailReadAt t L ie fn fd i (48 * (4 + j) * 2 ^ ie) then i
    else keyWalk t L ie fn fd (i + 1)
      (firstAt (fun j' => pairNum t L ie (i + 1) ≤ 2 ^ j' * pairDen t) j (bGrow t)) f

/-- The walk from a halving at its bit count is the search from that
halving. -/
theorem keyWalk_read (t : Tail) (L ie fn fd : Nat) (tp : t.pos) :
    ∀ (f i : Nat), keyWalk t L ie fn fd i (jp t L ie i) f = firstAt (tailRead t L ie fn fd) i f
  | 0, _ => rfl
  | f + 1, i => by
    show (if tailReadAt t L ie fn fd i (48 * (4 + jp t L ie i) * 2 ^ ie) then i
      else keyWalk t L ie fn fd (i + 1)
        (firstAt (fun j' => pairNum t L ie (i + 1) ≤ 2 ^ j' * pairDen t) (jp t L ie i)
          (bGrow t)) f)
      = (if tailRead t L ie fn fd i then i else firstAt (tailRead t L ie fn fd) (i + 1) f)
    rw [jp_succ_read t L ie i tp, keyWalk_read t L ie fn fd tp f (i + 1)]
    rfl

/-- The scale key's computing read, the walk from the first halving
at its bit count. -/
def tailKeyC (t : Tail) (L ie fn fd : Nat) : Nat :=
  keyWalk t L ie fn fd 0 (jp t L ie 0) (tailWit t L ie fn fd)

/-- The computing read is the scale key. -/
theorem tailKeyC_eq (t : Tail) (L ie fn fd : Nat) (tp : t.pos) :
    tailKeyC t L ie fn fd = tailKey t L ie fn fd :=
  keyWalk_read t L ie fn fd tp (tailWit t L ie fn fd) 0

/-- The scale comparison off the list's read: `4 (P_u + P_v) f_d < f_n
2^i`, the Nat read at the cleared pairs against the clearing's multiple. -/
theorem tail_scale (t : Tail) (L ie fn fd i : Nat) (h : tailRead t L ie fn fd i) :
    4 * ((puC t L).at (nearScale t L ie i) + (pvC t L).at (nearScale t L ie i)) * 1 * fd
      < pairClr t * fn * 2 ^ i := by
  have hm : ((Poly4.scale (2 * fd) ((puC t L).add (pvC t L))).add ⟨1, 0, 0, 0, 0⟩).at
      (nearScale t L ie i) ≤ t.kappa * t.kappa * t.dth * fn * 2 ^ i :=
    listRead_mem _ _ _ h.1 _ (List.Mem.head _)
  rw [Poly4.at_add, Poly4.at_scale, Poly4.at_add, Poly4.at_cst] at hm
  have e1 : 4 * ((puC t L).at (nearScale t L ie i) + (pvC t L).at (nearScale t L ie i)) * 1 * fd
      = 2 * (2 * fd * ((puC t L).at (nearScale t L ie i) + (pvC t L).at (nearScale t L ie i))) :=
    ground.monEq [(puC t L).at (nearScale t L ie i) + (pvC t L).at (nearScale t L ie i), fd]
      (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.cst 1)) (Mon.var 1))
      (Mon.mul (Mon.cst 2) (Mon.mul (Mon.mul (Mon.cst 2) (Mon.var 1)) (Mon.var 0)))
      (by decide +kernel) (by decide +kernel)
  have e2 : pairClr t * fn * 2 ^ i = 2 * (t.kappa * t.kappa * t.dth * fn * 2 ^ i) :=
    ground.monEq [t.kappa, t.dth, fn, 2 ^ i]
      (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 2) (Mon.mul (Mon.var 0) (Mon.var 0)))
        (Mon.var 1)) (Mon.var 2)) (Mon.var 3))
      (Mon.mul (Mon.cst 2) (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 0))
        (Mon.var 1)) (Mon.var 2)) (Mon.var 3)))
      (by decide +kernel) (by decide +kernel)
  rw [e1, e2]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) (by decide : 0 < 2))
    (Nat.mul_le_mul_left 2 hm)

/-- The tail read: at a side, a mass and a scale at which the three key
comparisons hold, the excess and the mode read at the scale
(`excess_read` and `mode_read`'s conclusions at the key's data, the
scale `[1 : 2^i]`, the mass `[1 : 2^{i_ε}]`, the mode read `[20 : L² +
2L + 2]`, the stated pairs at their clearing and `P_u`, `P_v` the
cleared pairs at the mass's clearing) put the reads' sum under the
floor's multiple of the scale, `r_u + r_v < η φ` (`key_quarters`); the
three comparisons enter the pair carrier at the one-member site
(`ground.Pol.ofNat_val`). -/
theorem tail_read (t : Tail) (L ie fn fd i : Nat) (ru rv : BPair) (tp : t.pos)
    (hL : sideRead t.kappa fn fd L)
    (hie : massRead t L fn fd ie) (hi : tailRead t L ie fn fd i)
    (hru : ru * (BPair.ofNat (2 ^ i) * BPair.ofNat (2 ^ i) * BPair.ofNat (2 ^ i))
        * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie)) * BPair.ofNat (pairClr t)
      ≤ BPair.ofNat 192 * (BPair.ofNat t.g * BPair.ofNat t.kappa
            * (BPair.ofNat (cD t) * BPair.ofNat t.np))
          * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1
          * (BPair.ofNat (2 ^ i) * BPair.ofNat (2 ^ i)) * BPair.ofNat (pairClr t)
        + BPair.ofNat ((puC t L).at (nearScale t L ie i))
            * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie))
          * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat (2 ^ i))
    (hrv : rv * (BPair.ofNat (2 ^ i) * BPair.ofNat (2 ^ i))
        * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie)) * BPair.ofNat (L * L + 2 * L + 2)
        * BPair.ofNat (pairClr t)
      ≤ BPair.ofNat 16 * BPair.ofNat t.kappa * (BPair.ofNat L + BPair.ofNat 2) * BPair.ofNat 20
          * BPair.ofNat 1 * BPair.ofNat (2 ^ i) * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie))
          * BPair.ofNat (pairClr t)
        + BPair.ofNat 384 * (BPair.ofNat t.g * BPair.ofNat t.kappa * BPair.ofNat (cZ t L))
          * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat 1 * BPair.ofNat (2 ^ i)
          * BPair.ofNat (L * L + 2 * L + 2) * BPair.ofNat (pairClr t)
        + BPair.ofNat ((pvC t L).at (nearScale t L ie i))
            * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie))
          * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat (L * L + 2 * L + 2)) :
    (ru + rv) * BPair.ofNat (2 ^ i) * BPair.ofNat fd < BPair.ofNat 1 * BPair.ofNat fn := by
  have hs0 : BPair.unit < BPair.ofNat (2 ^ i) := unitLtNat (Nat.pow_pos (by decide : 0 < 2))
  have hm0 : BPair.unit < BPair.ofNat (2 ^ ie) := unitLtNat (Nat.pow_pos (by decide : 0 < 2))
  have hn0 : BPair.unit < BPair.ofNat 1 := unitLtNat (by decide : 0 < 1)
  have heWd0 : BPair.unit < BPair.ofNat (L * L + 2 * L + 2) :=
    unitLtNat (Nat.lt_of_lt_of_le (by decide : 0 < 2) (Nat.le_add_left 2 _))
  have hcc0 : BPair.unit < BPair.ofNat (pairClr t) :=
    unitLtNat (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) (Nat.mul_pos tp.1 tp.1)) tp.2.2.2.1)
  -- the side comparison at the mode read's pair
  have hside : BPair.ofNat 64 * BPair.ofNat t.kappa * (BPair.ofNat L + BPair.ofNat 2)
      * BPair.ofNat 20 * BPair.ofNat fd < BPair.ofNat fn * BPair.ofNat (L * L + 2 * L + 2) := by
    have e : 1280 * t.kappa * (L + 2) * fd = 64 * t.kappa * (L + 2) * 20 * fd :=
      ground.monEq [t.kappa, L + 2, fd]
        (Mon.mul (Mon.mul (Mon.mul (Mon.cst 1280) (Mon.var 0)) (Mon.var 1)) (Mon.var 2))
        (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 64) (Mon.var 0)) (Mon.var 1)) (Mon.cst 20))
          (Mon.var 2))
        (by decide +kernel) (by decide +kernel)
    have h : Pol.val [t.kappa, L, fd, fn, L * L + 2 * L + 2]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 64)) (Pol.mon (Mon.var 0)))
          (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 2)))) (Pol.mon (Mon.cst 20)))
          (Pol.mon (Mon.var 2)))
        < Pol.val [t.kappa, L, fd, fn, L * L + 2 * L + 2]
          (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 4))) := by
      show 64 * t.kappa * (L + 2) * 20 * fd < fn * (L * L + 2 * L + 2)
      rw [← e]
      exact hL
    exact BPair.lt_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (ltB_ofNat h)
  -- the mass comparison at the joined coefficient
  have hmass : BPair.ofNat 4 * (BPair.ofNat t.g * BPair.ofNat t.kappa
        * (BPair.ofNat 192 * (BPair.ofNat (cD t) * BPair.ofNat t.np)
          + BPair.ofNat 384 * BPair.ofNat (cZ t L)))
      * (BPair.ofNat 1 * BPair.ofNat 1) * BPair.ofNat fd
      < BPair.ofNat fn * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie)) := by
    have h : Pol.val [t.g, t.kappa, cD t, t.np, cZ t L, fd, fn, 2 ^ ie]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4))
          (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))
            (Pol.add (Pol.mul (Pol.mon (Mon.cst 192))
                (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3))))
              (Pol.mul (Pol.mon (Mon.cst 384)) (Pol.mon (Mon.var 4))))))
          (Pol.mul (Pol.mon (Mon.cst 1)) (Pol.mon (Mon.cst 1)))) (Pol.mon (Mon.var 5)))
        < Pol.val [t.g, t.kappa, cD t, t.np, cZ t L, fd, fn, 2 ^ ie]
          (Pol.mul (Pol.mon (Mon.var 6)) (Pol.mul (Pol.mon (Mon.var 7)) (Pol.mon (Mon.var 7)))) := by
      show 4 * (t.g * t.kappa * (192 * (cD t * t.np) + 384 * cZ t L)) * (1 * 1) * fd
        < fn * (2 ^ ie * 2 ^ ie)
      have h0 : massX t L * fd < fn * 4 ^ ie := hie
      rw [fourPow ie, Nat.mul_comm 2 ie, Nat.mul_two, powAdd] at h0
      rw [Nat.mul_one]
      exact h0
    exact BPair.lt_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (ltB_ofNat h)
  -- the scale comparison at the cleared pairs, the mass's clearing joined
  have hscale : BPair.ofNat 4
      * (BPair.ofNat ((puC t L).at (nearScale t L ie i))
          * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie))
        + BPair.ofNat ((pvC t L).at (nearScale t L ie i))
          * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie)))
      * BPair.ofNat 1 * BPair.ofNat fd
      < BPair.ofNat (pairClr t) * BPair.ofNat fn * BPair.ofNat (2 ^ i)
        * (BPair.ofNat (2 ^ ie) * BPair.ofNat (2 ^ ie)) := by
    have hN := Nat.mul_lt_mul_of_pos_right (k := 2 ^ ie * 2 ^ ie) (tail_scale t L ie fn fd i hi)
      (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2)) (Nat.pow_pos (by decide : 0 < 2)))
    have e : 4 * ((puC t L).at (nearScale t L ie i) + (pvC t L).at (nearScale t L ie i)) * 1 * fd
        * (2 ^ ie * 2 ^ ie)
        = 4 * ((puC t L).at (nearScale t L ie i) * (2 ^ ie * 2 ^ ie)
          + (pvC t L).at (nearScale t L ie i) * (2 ^ ie * 2 ^ ie)) * 1 * fd := by
      rw [← mulAddR]
      exact ground.monEq [(puC t L).at (nearScale t L ie i) + (pvC t L).at (nearScale t L ie i),
          fd, 2 ^ ie]
        (Mon.mul (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.var 0)) (Mon.cst 1)) (Mon.var 1))
          (Mon.mul (Mon.var 2) (Mon.var 2)))
        (Mon.mul (Mon.mul (Mon.mul (Mon.cst 4) (Mon.mul (Mon.var 0) (Mon.mul (Mon.var 2)
          (Mon.var 2)))) (Mon.cst 1)) (Mon.var 1))
        (by decide +kernel) (by decide +kernel)
    rw [e] at hN
    have h : Pol.val [(puC t L).at (nearScale t L ie i), (pvC t L).at (nearScale t L ie i),
        2 ^ ie, fd, pairClr t, fn, 2 ^ i]
        (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4))
          (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2))))
            (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2))))))
          (Pol.mon (Mon.cst 1))) (Pol.mon (Mon.var 3)))
        < Pol.val [(puC t L).at (nearScale t L ie i), (pvC t L).at (nearScale t L ie i),
          2 ^ ie, fd, pairClr t, fn, 2 ^ i]
          (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 5)))
            (Pol.mon (Mon.var 6))) (Pol.mon (Mon.mul (Mon.var 2) (Mon.var 2)))) := hN
    exact BPair.lt_congr (Pol.ofNat_val _ _) (Pol.ofNat_val _ _) (ltB_ofNat h)
  exact key_quarters ru rv _ _ (BPair.ofNat t.g) (BPair.ofNat t.kappa) (BPair.ofNat (cD t))
    (BPair.ofNat t.np) (BPair.ofNat (cZ t L)) (BPair.ofNat 1) (BPair.ofNat (2 ^ ie))
    (BPair.ofNat 1) (BPair.ofNat (2 ^ i)) (BPair.ofNat 20) (BPair.ofNat (L * L + 2 * L + 2))
    (BPair.ofNat L) (BPair.ofNat fn) (BPair.ofNat fd) (BPair.ofNat (pairClr t)) hru hrv hside
    hmass hscale hn0 hs0 hm0 heWd0 hcc0 (unitLeOfNat fd) (unitLeOfNat fn)

end cornerkey
