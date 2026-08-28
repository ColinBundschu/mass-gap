import MassGap.Deck
/-!
The check module for `def:deck`: the batteries re-read the deck
families and the column reads by kernel `decide`.  The families'
first four members (`p = w, w²-2, w³-3w, w⁴-4w²+2` and
`Q = 1, w, w²-1, w³-2w`), the degree and parity shapes among them;
the remainder carrier's reduction (`y² = w y - 1`); the plus and
word reads at the first four keys; and the root pair `(1/2, 2)` at
chord `5/2` — the collected read `z³ + z'³ = p₃(5/2) = 65/8`
cleared at the shared clearing, with the off-chord refusal.  The
geometric word's deck symbol rides beside them: `P_L` at the first
three sides (`1`, `w + 1`, `w² + w - 1` at `L = 1, 3, 5`), its value
at the chord `2` the side itself — the general theorem `pSum_two`
discharged at each — and the division display at the monic
`⟨x : 2⟩`, the remainder the side, with the refusal at a wrong
remainder.  The residue's wrap identities close the module: the
three general theorems discharged at the committed sides (`L = 5`
and `L = 7`), the multiples their witnesses exhibited by hand at
side five — `p_4 - p_1 = (x²-x-2) P_5`, `p_3 - p_2 = (x-2) P_5`,
`p_5 - 2 = ((x-2) P_5) P_5` and `p_6 - p_1 = (x⁴-x³-4x²+3x+2) P_5`
— the third's exhibited multiple the cofactor `(x-2) P_5` —
and the symbol shown load-bearing by the wrong-side refusal, the
same multiple against `P_3`.  The membership bridge rides last: the
divisor read at sides three and five, the division display carrying
a polynomial into its own class, a landed wrap congruence
collapsing onto a residue equality, an equal-residue pair read back
as a congruence, and the collapse's contrapositive refusing an
incongruent pair. -/
set_option maxHeartbeats 4000000

open ground poly deck

private def u : BPair := BPair.unit

/-! The families' first members. -/

example : poly.oneValue (pFam 1) [u, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (pFam 2) [⟨1, 3⟩, u, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (pFam 3) [u, ⟨1, 4⟩, u, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (pFam 4)
    [⟨3, 1⟩, u, ⟨1, 5⟩, u, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (qFam 1) [⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (qFam 2) [u, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (qFam 3) [⟨1, 2⟩, u, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (qFam 4) [u, ⟨1, 3⟩, u, ⟨2, 1⟩] := by decide +kernel

/-! The remainder carrier's reduction: `y² = w y - 1`. -/

example : dNull (dAdd (dPow yE 2)
    (dSwap ([⟨1, 2⟩], wPoly))) := by decide +kernel

/-! The plus and word reads at the first four keys. -/

example : plusRead 0 := by decide +kernel
example : plusRead 1 := by decide +kernel
example : plusRead 2 := by decide +kernel
example : plusRead 3 := by decide +kernel
example : wordRead 0 := by decide +kernel
example : wordRead 1 := by decide +kernel
example : wordRead 2 := by decide +kernel
example : wordRead 3 := by decide +kernel

/-! The root pair `(1/2, 2)` at chord `5/2`, the collected read
`z³ + z'³ = p₃(5/2) = 65/8` at the shared clearing, with the
off-chord refusal. -/

example : pairRead ⟨2, 1⟩ ⟨5, 1⟩ ⟨6, 1⟩ 2 2 := by decide +kernel
example : ¬ pairRead ⟨2, 1⟩ ⟨5, 1⟩ ⟨7, 1⟩ 2 2 := by decide +kernel

/-! The deck symbol at the first three sides, its value at the
chord `2`, and the division display there. -/

example : poly.oneValue (pSum 0) [⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (pSum 1) [⟨2, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (pSum 2) [⟨1, 2⟩, ⟨2, 1⟩, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue (pSum 3)
    [⟨1, 2⟩, ⟨1, 3⟩, ⟨2, 1⟩, ⟨2, 1⟩] := by decide +kernel

example : (poly.eval (pSum 2) (BPair.ofNat 2)).oneValue
    (BPair.ofNat 5) := pSum_two 2
example : (poly.eval (pSum 3) (BPair.ofNat 2)).oneValue
    (BPair.ofNat 7) := pSum_two 3
example : (poly.eval (pFam 4) (BPair.ofNat 2)).oneValue
    (BPair.ofNat 2) := pFam_two 4

example : divTwoRead 1 := by decide +kernel
example : divTwoRead 2 := by decide +kernel
example : divTwoRead 3 := by decide +kernel

example : ¬ poly.oneValue (poly.div [(BPair.ofNat 2).swap] (pSum 2)).2
    [BPair.ofNat 6] := by decide +kernel

/-! The chord end's display is a theorem at every side (`divTwo`),
the three decided sides reading it off that theorem. -/

example : divTwoRead 1 := divTwo 1
example : divTwoRead 2 := divTwo 2
example : divTwoRead 3 := divTwo 3

/-! The band's partner end.  The seeded family at the partner chord
alternates with its own depth (`pFamN_partner`), the deck symbol
there reads the depth's parity member, and the partner division
display holds at the three sides — decided and read off the general
theorem alike (`divPartner`).  The parity is load-bearing at both
parities: at side five the remainder refuses the odd member and at
side seven it refuses the even one. -/

example : (poly.eval (pFamN 0) ((BPair.ofNat 2).swap)).oneValue
    (BPair.ofNat 2 * parityMember 0) := by decide +kernel
example : (poly.eval (pFamN 1) ((BPair.ofNat 2).swap)).oneValue
    (BPair.ofNat 2 * parityMember 1) := by decide +kernel
example : (poly.eval (pFamN 2) ((BPair.ofNat 2).swap)).oneValue
    (BPair.ofNat 2 * parityMember 2) := by decide +kernel
example : (poly.eval (pFamN 3) ((BPair.ofNat 2).swap)).oneValue
    (BPair.ofNat 2 * parityMember 3) := by decide +kernel
example : (poly.eval (pFamN 4) ((BPair.ofNat 2).swap)).oneValue
    (BPair.ofNat 2 * parityMember 4) := pFamN_partner 4

example : (poly.eval (pSum 2) ((BPair.ofNat 2).swap)).oneValue
    (parityMember 2) := pSum_partner 2
example : (poly.eval (pSum 3) ((BPair.ofNat 2).swap)).oneValue
    (parityMember 3) := pSum_partner 3

example : divPartnerRead 1 := by decide +kernel
example : divPartnerRead 2 := by decide +kernel
example : divPartnerRead 3 := by decide +kernel
example : divPartnerRead 1 := divPartner 1
example : divPartnerRead 2 := divPartner 2
example : divPartnerRead 3 := divPartner 3

example : ¬ poly.oneValue (poly.div [BPair.ofNat 2] (pSum 2)).2
    [(BPair.ofNat 1).swap] := by decide +kernel
example : ¬ poly.oneValue (poly.div [BPair.ofNat 2] (pSum 3)).2
    [BPair.ofNat 1] := by decide +kernel

/-! The two ends' cofactors at side five, each divisor against its
own quotient exhibited by kernel `decide`: the chord end leaves the
side `5` and the partner end the parity member `1`
(`cofTwo_pCong`, `cofPartner_pCong`), and their product is the
band's Gram witness. -/

example : poly.oneValue (pSum 2)
    (poly.add (poly.mul chordTwo
      (poly.div [(BPair.ofNat 2).swap] (pSum 2)).1)
      [BPair.ofNat 5]) := by decide +kernel

example : poly.oneValue (pSum 2)
    (poly.add (poly.mul chordPartner
      (poly.div [BPair.ofNat 2] (pSum 2)).1)
      [deck.parityMember 2]) := by decide +kernel

example : poly.oneValue (gramCof 2)
    (poly.mul (poly.div [(BPair.ofNat 2).swap] (pSum 2)).1
      (poly.div [BPair.ofNat 2] (pSum 2)).1) := by decide +kernel

example : ∃ c, pCong 2 c
    (poly.mul chordTwo (poly.div [(BPair.ofNat 2).swap] (pSum 2)).1)
    (poly.neg [BPair.ofNat 5]) := cofTwo_pCong 2

example : ∃ c, pCong 2 c
    (poly.mul chordPartner (poly.div [BPair.ofNat 2] (pSum 2)).1)
    (poly.neg [parityMember 2]) := cofPartner_pCong 2

example : parityMember 3 = (parityMember 2).swap := parityMember_succ 2

/-! The doubling identity `p_L = ⟨x:2⟩ P_L² + 2` at the first three
odd sides (`L = 3, 5, 7` at `m = 1, 2, 3`): the general theorem
`pFamN_pSum` discharged at each, the seeded family's own values
beside them (`p₀ = 2`, `p₁ = w`, `p₃ = w³ - 3w`), and the identity
refused at a moved coefficient — the linear factor at the chord
`3` in place of `2`, and the constant `3` in place of `2` — the two
places the display's data enter. -/

example : poly.oneValue (pFamN 0) [BPair.ofNat 2] := by decide +kernel
example : poly.oneValue (pFamN 1) wPoly := by decide +kernel
example : poly.oneValue (pFamN 3) [u, ⟨1, 4⟩, u, ⟨2, 1⟩] := by decide +kernel
example : poly.oneValue chordTwo [⟨1, 3⟩, ⟨2, 1⟩] := by decide +kernel

example : poly.oneValue (pFamN 3)
    (poly.add (poly.mul chordTwo (poly.mul (pSum 1) (pSum 1)))
      [BPair.ofNat 2]) := pFamN_pSum 1
example : poly.oneValue (pFamN 5)
    (poly.add (poly.mul chordTwo (poly.mul (pSum 2) (pSum 2)))
      [BPair.ofNat 2]) := pFamN_pSum 2
example : poly.oneValue (pFamN 7)
    (poly.add (poly.mul chordTwo (poly.mul (pSum 3) (pSum 3)))
      [BPair.ofNat 2]) := pFamN_pSum 3

example : ¬ poly.oneValue (pFamN 5)
    (poly.add
      (poly.mul (poly.monic [(BPair.ofNat 3).swap])
        (poly.mul (pSum 2) (pSum 2)))
      [BPair.ofNat 2]) := by decide +kernel
example : ¬ poly.oneValue (pFamN 5)
    (poly.add (poly.mul chordTwo (poly.mul (pSum 2) (pSum 2)))
      [BPair.ofNat 3]) := by decide +kernel

/-! The two product families the identity rides on, at the first
keys: the square `p_j p_j = p_{2j} + 2` and the neighbour cross
`p_j p_{j+1} = p_{2j+1} + w`, with the recursion's own display
`p_b + p_{b+2} = w p_{b+1}` beside them. -/

example : poly.oneValue (poly.mul (pFamN 3) (pFamN 3))
    (poly.add (pFamN 6) [BPair.ofNat 2]) := (deckProducts 3).1
example : poly.oneValue (poly.mul (pFamN 3) (pFamN 4))
    (poly.add (pFamN 7) wPoly) := (deckProducts 3).2.1
example : poly.oneValue (poly.add (pFamN 4) (pFamN 6))
    (poly.mul wPoly (pFamN 5)) := pFamN_rec 4
example : poly.oneValue
    (poly.add (poly.mul chordTwo (pSum 3)) (pFamN 3))
    (pFamN 4) := chordTwo_pSum 3

/-! The residue's wrap identities at the committed sides: the three
general theorems discharged at `L = 5` and `L = 7`, with the index
read beside them. -/

example : ∃ c, pCong 2 c (pFamN 5) (pFamN 0) := pFamN_side 2
example : ∃ c, pCong 2 c (pFamN 4) (pFamN 1) := pFamN_wrapDown 2 1 1 rfl
example : ∃ c, pCong 2 c (pFamN 3) (pFamN 2) := pFamN_wrapDown 2 0 2 rfl
example : ∃ c, pCong 2 c (pFamN 6) (pFamN 1) := pFamN_wrapUp 2 1
example : ∃ c, pCong 2 c (pFamN 7) (pFamN 2) := pFamN_wrapUp 2 2
example : ∃ c, pCong 3 c (pFamN 7) (pFamN 0) := pFamN_side 3
example : ∃ c, pCong 3 c (pFamN 6) (pFamN 1) := pFamN_wrapDown 3 2 1 rfl
example : ∃ c, pCong 3 c (pFamN 8) (pFamN 1) := pFamN_wrapUp 3 1

example : 2 + 1 + 1 + 1 = 2 * 2 + 1 := pFamN_wrapIndex 2 1 1 rfl
example : 3 + 2 + 1 + 1 = 2 * 3 + 1 := pFamN_wrapIndex 3 2 1 rfl

/-! The recursion read cyclically at the residue: the interior
display and the two boundary rows discharged at `L = 5` — every row
of the cycle's chord action on the family column — and the boundary
rows again at `L = 7`. -/

example : ∃ c, pCong 2 c (poly.add (pFamN 0) (pFamN 2))
    (poly.mul wPoly (pFamN 1)) := pFamN_cycMid 2 0
example : ∃ c, pCong 2 c (poly.add (pFamN 1) (pFamN 3))
    (poly.mul wPoly (pFamN 2)) := pFamN_cycMid 2 1
example : ∃ c, pCong 2 c (poly.add (pFamN 2) (pFamN 4))
    (poly.mul wPoly (pFamN 3)) := pFamN_cycMid 2 2
example : ∃ c, pCong 2 c (poly.add (pFamN 1) (pFamN 4))
    (poly.mul wPoly (pFamN 0)) := pFamN_cycBot 2
example : ∃ c, pCong 2 c (poly.add (pFamN 5) (pFamN 3))
    (poly.mul wPoly (pFamN 4)) := pFamN_cycTop 2 3 rfl
example : ∃ c, pCong 3 c (poly.add (pFamN 1) (pFamN 6))
    (poly.mul wPoly (pFamN 0)) := pFamN_cycBot 3
example : ∃ c, pCong 3 c (poly.add (pFamN 7) (pFamN 5))
    (poly.mul wPoly (pFamN 6)) := pFamN_cycTop 3 5 rfl

/-! The congruence's two-member joins at side five
(`pCong_addBoth`, `pCong_mulBoth`): the wrapped pair `p_4 = p_1` and
`p_3 = p_2` composes under the sum and under the product alike, each
composite the two witnesses' own. -/

example : ∃ c, pCong 2 c (poly.add (pFamN 4) (pFamN 3))
    (poly.add (pFamN 1) (pFamN 2)) :=
  pCong_addBoth (pFamN_wrapDown 2 1 1 rfl) (pFamN_wrapDown 2 0 2 rfl)

example : ∃ c, pCong 2 c (poly.mul (pFamN 4) (pFamN 3))
    (poly.mul (pFamN 1) (pFamN 2)) :=
  pCong_mulBoth (pFamN_wrapDown 2 1 1 rfl) (pFamN_wrapDown 2 0 2 rfl)

/-! The reflected join's wrap at both orders and at side three,
the below-`m` keys and the beyond-`m` keys one display. -/

example : ∃ c, pCong 2 c (pFamN 1) (pFamN 4) := pFamN_wrapRefl 2 1 4 rfl
example : ∃ c, pCong 2 c (pFamN 4) (pFamN 1) := pFamN_wrapRefl 2 4 1 rfl
example : ∃ c, pCong 1 c (pFamN 1) (pFamN 2) := pFamN_wrapRefl 1 1 2 rfl
example : ∃ c, pCong 1 c (pFamN 2) (pFamN 1) := pFamN_wrapRefl 1 2 1 rfl

/-! The multiples the congruences carry, exhibited at side five by
kernel `decide`: each wrapped key differs from its own by a stated
multiple of `P_5 = x² + x - 1`. -/

example : pCong 2 [⟨1, 3⟩, ⟨1, 2⟩, ⟨2, 1⟩] (pFamN 4) (pFamN 1) := by decide +kernel
example : pCong 2 [⟨1, 3⟩, ⟨2, 1⟩] (pFamN 3) (pFamN 2) := by decide +kernel
example : pCong 2 [⟨3, 1⟩, ⟨1, 4⟩, ⟨1, 2⟩, ⟨2, 1⟩] (pFamN 5)
    (pFamN 0) := by decide +kernel
example : pCong 2 [⟨3, 1⟩, ⟨4, 1⟩, ⟨1, 5⟩, ⟨1, 2⟩, ⟨2, 1⟩] (pFamN 6)
    (pFamN 1) := by decide +kernel

/-! The symbol is load-bearing: the side-five multiple against the
side-three symbol is no congruence. -/

example : ¬ pCong 1 [⟨1, 3⟩, ⟨1, 2⟩, ⟨2, 1⟩] (pFamN 4) (pFamN 1) := by decide +kernel

/-! A located root's own reads are the congruences' evaluations
(`pCong_eval`): at side three the symbol `P_3 = x + 1` has the
ground root `-1`, where the wrapped keys read their own — `p_4`
and `p_2` both read `p_1`'s value there — and the seed `p_0` does
not. -/

example : (poly.eval (pFamN 4) ⟨1, 2⟩).oneValue
    (poly.eval (pFamN 1) ⟨1, 2⟩) :=
  pCong_eval (pFamN_wrapUp 1 1) ⟨1, 2⟩ (by decide +kernel)

example : (poly.eval (pFamN 2) ⟨1, 2⟩).oneValue
    (poly.eval (pFamN 1) ⟨1, 2⟩) :=
  pCong_eval (pFamN_wrapDown 1 0 1 rfl) ⟨1, 2⟩ (by decide +kernel)

example : ¬ (poly.eval (pFamN 0) ⟨1, 2⟩).oneValue
    (poly.eval (pFamN 1) ⟨1, 2⟩) := by decide +kernel

/-! The membership bridge at the deck symbol, discharged at the
committed sides.  The divisor read is a theorem at every side
(`pSum_monic`), the sides three through nine reading it off that
theorem with one kernel twin beside them — the decided instance the
value read's own coherence pin, the display's top read at its
landed representative rather than at the canonical one; the
division display carries every
polynomial into its own class (`redP_pCong`), a landed wrap
congruence collapses onto a residue equality (`redP_congr`), an
exhibited equal-residue pair is itself a congruence
(`pCong_of_redP`), and the collapse's contrapositive refuses the
incongruent pair `p_1`, `p_0` at side five. -/

example : monicRead 1 := pSum_monic 1
example : monicRead 2 := pSum_monic 2
example : monicRead 3 := pSum_monic 3
example : monicRead 4 := pSum_monic 4
example : monicRead 2 := by decide +kernel

example : ∃ c, pCong 2 c (pFamN 4) (redP 2 (pFamN 4)) :=
  redP_pCong 2 _

example : poly.oneValue (redP 2 (pFamN 4)) (redP 2 (pFamN 1)) :=
  redP_congr 2 (pFamN_wrapDown 2 1 1 rfl)

example : ∃ c, pCong 2 c (pFamN 4) (pFamN 1) :=
  pCong_of_redP 2 (by decide +kernel)

example : ¬ ∃ c, pCong 2 c (pFamN 1) (pFamN 0) :=
  fun h => absurd (redP_congr 2 h) (by decide +kernel)

/-! The side-seven residues, past the key where the divisor read's
former equality spelling refused: the wraps read one residue at
every reflected pair, with the refusal at an incongruent pair. -/

example : poly.oneValue (redP 3 (pFamN 7)) (redP 3 (pFamN 0)) := by decide +kernel
example : poly.oneValue (redP 3 (pFamN 6)) (redP 3 (pFamN 1)) := by decide +kernel
example : poly.oneValue (redP 3 (pFamN 5)) (redP 3 (pFamN 2)) := by decide +kernel
example : poly.oneValue (redP 3 (pFamN 4)) (redP 3 (pFamN 3)) := by decide +kernel
example : ¬ poly.oneValue (redP 3 (pFamN 5)) (redP 3 (pFamN 1)) := by decide +kernel

/-! The families' shape at their keys: the length the degree's
successor and the top the scalar one off the seed, the seed's own
top the scalar two (`pFamN_len`, `pFamN_top`), decided beside the
theorem routes. -/

example : (pFamN 0).length = 1 := by decide +kernel
example : (pFamN 3).length = 4 := by decide +kernel
example : (pFamN 5).length = 6 := pFamN_len 5
example : (ground.getAt BPair.unit (pFamN 3) 3).oneValue
    (BPair.ofPos Pos.one) := by decide +kernel
example : (ground.getAt BPair.unit (pFamN 4) 4).oneValue
    (BPair.ofPos Pos.one) := pFamN_top 3
example : (ground.getAt BPair.unit (pFamN 0) 0).oneValue
    (BPair.ofNat 2) := by decide +kernel
example : ¬ (ground.getAt BPair.unit (pFamN 0) 0).oneValue
    (BPair.ofPos Pos.one) := by decide +kernel
