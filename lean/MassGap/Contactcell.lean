import MassGap.Deckfactor
import MassGap.Truncation
import MassGap.Cellcount
import MassGap.Pieri
import MassGap.Dualread
import MassGap.Fusion
import MassGap.Pathsquare
import MassGap.Casfloor
import MassGap.Windowfinite
import MassGap.Rankstable
/-!
`lem:contactcell` — the near-contact cell's truncation pair, its
count tier.

On the `X`-sector cell's chain the count at a level is bracketed by
two finite divisors.  The first is the plain truncation, a
compression, its counts at or below the chain's
(`truncation.count_head_le` at the fiber datum's site tie).  The
second is the frontier-bordered pencil: the head carries one
auxiliary row per frontier label, its coupling one and its auxiliary
diagonal the pair `[⟨4σc₊ : d_ϑ + λ⟩ : ϰ_B]`, and the seed floor
`F = ⟨4σc₊ : d_ϑ⟩` floors the whole excluded block, so at every level
below `F` eliminating that block puts the larger head's read at or
above the bordered pencil's own Schur read.  `count_bord_le` is that
comparison at the site data: the whole datum's count sits at or below
the supported-shift head's, the head's shift the supported diagonal
`c_W·D₁` withdrawn from the plain head, the removed block's count
vacant at the level raised by the witness gap `ς`, and the difference
site's weighting reading the shift site at the cofactor tie
`ς c_W = W²` (`thm:truncation`'s polarization through
`truncation.shift_psd`, the monotone side and the join through
`truncation.count_full_le`).

`bord_schur` reads the bordered pencil's own count: the auxiliary
pivots are positive at every level below `F` and inertia is additive
there (`lem:inertia`'s addition clause at a nonsingular principal
pivot), so the assembled datum's reversal count is its deflation's
alone, the pivot block's vacant.

`pin_pair` closes the sandwich: at a level whose two counts agree the
compression from below and the bordered comparison from above meet at
one integer, and that integer is a located count of the chain itself,
the count beyond every cutoff (`lem:dualtrunc`).

`extRead` is the contact cell's extent certificate: the `σ`-extent
`σ₁` is the divisor's first positive root, committed as a bracket
over the divisor's squarefree witness (`lem:cellcount`'s `divRead`),
the segment from the unit up to the bracket's bottom holding a vacant
root count and the bracket itself holding one — the two segment
counts of `lem:hermitesign`'s bracket pencil at `lem:deckfactor`'s
cleared variable, the endpoints rescaled by the top's magnitude.

The frontier tier reads the seed floor's own data.  `boxRow` is the
stencil membership: an excluded label of the closure moves, and one
move within the adjoint stencil — the moved pair entering as its
letter-pair-move content, one place raised and one lowered — reads
the target's count occupied, the fundamental against its complement
collecting that count through the associativity at the two one-box
rows, the full-column summand reading the sum's unit at the moved
target and the withdrawn box's row read against the added one's
(`lem:pieri`; `lem:adjchar`; `con:labels`;
`lem:blockcount`(iii); `lem:dualread`(ii)).  `frontierTargets`
enumerates the frontier's targets — over the `X`-sector chain's
head, the unit label with the below-cutoff labels at the unit class,
the adjoint row's members beyond the cutoff, the row read at
`lem:rankstable`'s word list `rankstable.adjRow` and its membership
transported through `rankstable.adjRow_eq` — and `cPlusN` is `c₊`,
the least Casimir beyond the cutoff among the frontier's targets,
the auxiliary diagonal's first member.

`dualPMat` carries the dual pencil over the coupling coordinate: the
pair `(σE : M)`'s site datum is affine in `σ`, its constant key the
level datum's magnetic partner and its linear key the electric
member, so the whole cell enters `lem:cellcount`'s reads as one
polynomial-entried site datum.
-/

namespace contactcell
open ground poly elim inertia certconstruct truncation

/-- `lem:contactcell`'s bordered comparison: at a level the whole
datum's count sits at or below the supported-shift head's count, the
head's shift the supported diagonal `c_W·D₁` withdrawn from the plain
head, the removed block's count vacant at the level raised by the
witness gap `ς`, and the difference site's weighting reading the
shift site at the cofactor tie `ς c_W = W²` absorbed in the stated
weighting (`thm:truncation`'s polarization at the cap's supported
diagonal, the monotone side and the vacant coupling's join closing
the comparison). -/
theorem count_bord_le {k m : Nat} (H G M M1 M2 P G1 D1 Q G2 B : Mat)
    (x y cw W s : Pos) (nf nb : Nat)
    (spU spL : Split (k + m))
    (spF spD spd : Split (k + m)) (spB : Split k) (spR : Split m)
    (hcap : capAt M (matScale W (blockJoin D1 (elim.nullMat k m) G2))
      spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hD1 : sqAt D1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (htieD : matOneValue (matScale s (siteDatum
        (siteDatum (matAdd H (matScale y G)) (matScale x G))
        (blockJoin
          (siteDatum (matAdd (siteDatum P (matScale cw D1))
            (matScale y G1)) (matScale x G1))
          (elim.nullMat k m)
          (siteDatum (matAdd Q (matScale y G2))
            (matScale (x + s) G2)))))
      (shiftSite W s B D1 G2))
    (hf : countAtPair H G x y nf spF)
    (hb : countAtPair (siteDatum P (matScale cw D1)) G1 x y nb spB)
    (hr : countAtPair Q G2 (x + s) y 0 spR)
    (hD : splitRead (blockJoin
      (siteDatum (matAdd (siteDatum P (matScale cw D1))
        (matScale y G1)) (matScale x G1))
      (elim.nullMat k m)
      (siteDatum (matAdd Q (matScale y G2))
        (matScale (x + s) G2))) spD)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd (siteDatum P (matScale cw D1))
          (matScale y G1)) (matScale x G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale y G2))
          (matScale (x + s) G2)))) spd) :
    nf ≤ nb :=
  truncation.count_full_le H G (siteDatum P (matScale cw D1)) G1 Q G2
    x y x y (x + s) y nf nb
    spF spB spR spD spd hf hb hr hD hd
    (truncation.shift_psd M
      (blockJoin D1 (elim.nullMat k m) G2) M1 M2 B D1 G2
      (blockJoin
        (siteDatum (matAdd (siteDatum P (matScale cw D1))
          (matScale y G1)) (matScale x G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale y G2))
          (matScale (x + s) G2)))
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      W s spU spL hcap hMt
      (elim.matOne_refl (blockJoin D1 (elim.nullMat k m) G2))
      hM1 hM2l hD1 hG2 hB hBr htieD spd hd)

/-- `lem:contactcell`'s bordered pencil at positive auxiliary
pivots: the assembled datum's reversal count is its deflation's
alone, the auxiliary block's count vacant at the level below the seed
floor `F`, so the bordered read is the Schur complement's own
(`lem:inertia`'s addition clause at the solve witness, the pivot's
count the positive-semidefinite split's). -/
theorem bord_schur {k m : Nat} (Daux Bc P' Cw : Mat)
    (spJ : Split (k + m)) (spA : Split k) (spD : Split m)
    (hA : sqAt Daux k) (hBl : Bc.length = k) (hBr : rowsLen m Bc)
    (hP : sqAt P' m) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hAs : matOneValue (transposeM Daux) Daux)
    (hAw : matOneValue (matMul Daux Cw) (matScaleB (minor Daux) Bc))
    (hAnz : ¬ (minor Daux).oneValue BPair.unit)
    (hJ : splitRead (blockJoin Daux Bc P') spJ)
    (ha : splitRead Daux spA) (hpa : psdAt spA)
    (hd : splitRead (deflMat Daux Bc P' Cw) spD) :
    revAt spJ = revAt spD := by
  have hzero : revAt spA = 0 := hpa
  have hsum := inertia.rev_add Daux Bc P' Cw hA hBl hBr hP hCl hCr
    hAs hAw hAnz spJ hJ spA ha spD hd
  rw [hzero, Nat.zero_add] at hsum
  exact hsum

/-- `lem:contactcell`'s bordered arm: at a level below the seed
floor the whole datum's count sits at or below the bordered
pencil's own.  The removed block leads the stated join at a
positive split, so inertia adds at its pivot and the whole reads
its eliminated head's count; eliminating it puts the head's read
at or above the bordered pencil's Schur read at the stated
positive-semidefinite certificate of the cross-scaled deflations,
the counts monotone there and one value at the positive
rescalings' committed splits; and the bordered join's count is its
deflation's at positive auxiliary pivots (`lem:inertia`;
`bord_schur`). -/
theorem chain_le_bord {k m j : Nat}
    (Qs Bt Ps Cw1 Daux Bc Ph Cw2 : Mat) (q1 q2 : Pos)
    (spW : Split (m + k)) (spQ : Split m) (spE spE2 : Split k)
    (spJ : Split (j + k)) (spA : Split j)
    (spD spD2 spdiff : Split k)
    (hQ : sqAt Qs m) (hBtl : Bt.length = m) (hBtr : rowsLen k Bt)
    (hPs : sqAt Ps k) (hC1l : Cw1.length = m) (hC1r : rowsLen k Cw1)
    (hQsym : matOneValue (transposeM Qs) Qs)
    (hQw : matOneValue (matMul Qs Cw1) (matScaleB (minor Qs) Bt))
    (hQnz : ¬ (minor Qs).oneValue BPair.unit)
    (hW : splitRead (inertia.blockJoin Qs Bt Ps) spW)
    (hq : splitRead Qs spQ) (hpsdQ : psdAt spQ)
    (hE : splitRead (deflMat Qs Bt Ps Cw1) spE)
    (hE2 : splitRead (inertia.matScale q2 (deflMat Qs Bt Ps Cw1))
      spE2)
    (hrevE : revAt spE2 = revAt spE)
    (hD2 : splitRead (inertia.matScale q1 (deflMat Daux Bc Ph Cw2))
      spD2)
    (hrevD : revAt spD2 = revAt spD)
    (hdiff : splitRead (siteDatum
      (inertia.matScale q2 (deflMat Qs Bt Ps Cw1))
      (inertia.matScale q1 (deflMat Daux Bc Ph Cw2))) spdiff)
    (hpsd : psdAt spdiff)
    (hA : sqAt Daux j) (hBl : Bc.length = j) (hBr : rowsLen k Bc)
    (hP : sqAt Ph k) (hC2l : Cw2.length = j) (hC2r : rowsLen k Cw2)
    (hAs : matOneValue (transposeM Daux) Daux)
    (hAw : matOneValue (matMul Daux Cw2) (matScaleB (minor Daux) Bc))
    (hAnz : ¬ (minor Daux).oneValue BPair.unit)
    (hJ : splitRead (inertia.blockJoin Daux Bc Ph) spJ)
    (ha : splitRead Daux spA) (hpa : psdAt spA)
    (hD : splitRead (deflMat Daux Bc Ph Cw2) spD) :
    revAt spW ≤ revAt spJ := by
  have hadd := inertia.rev_add Qs Bt Ps Cw1 hQ hBtl hBtr hPs hC1l
    hC1r hQsym hQw hQnz spW hW spQ hq spE hE
  rw [show revAt spQ = 0 from hpsdQ, Nat.zero_add] at hadd
  rw [bord_schur Daux Bc Ph Cw2 spJ spA spD hA hBl hBr hP hC2l
    hC2r hAs hAw hAnz hJ ha hpa hD, hadd, ← hrevE, ← hrevD]
  exact inertia.rev_mono
    (inertia.matScale q1 (deflMat Daux Bc Ph Cw2))
    (inertia.matScale q2 (deflMat Qs Bt Ps Cw1))
    spdiff spD2 spE2 hdiff hpsd hD2 hE2

/-- `lem:contactcell`'s sandwich pin: the plain truncation's count
and the bordered-Schur head's count agreeing at one integer pin the
whole datum's count there, the compression side reading from below at
the fiber datum's site tie and the bordered comparison from above at
the supported shift.  A level whose two counts agree is a located
count of the chain itself, the count beyond every cutoff
(`lem:dualtrunc`). -/
theorem pin_pair {k m : Nat}
    (H G M M1 M2 P G1 D1 Q G2 B Bt : Mat)
    (x y cw W s : Pos) (n nf : Nat)
    (spU spL : Split (k + m))
    (spF spD spd : Split (k + m))
    (spH1 spB : Split k) (spR : Split m)
    (hBt : Bt.length = k)
    (htie : matOneValue
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd P (matScale y G1)) (matScale x G1)) Bt
        (siteDatum (matAdd Q (matScale y G2)) (matScale x G2))))
    (hlow : countAtPair P G1 x y n spH1)
    (hcap : capAt M (matScale W (blockJoin D1 (elim.nullMat k m) G2))
      spU spL)
    (hMt : matOneValue M (blockJoin M1 B M2))
    (hM1 : sqAt M1 k) (hM2l : M2.length = m)
    (hD1 : sqAt D1 k) (hG2 : sqAt G2 m)
    (hB : B.length = k) (hBr : rowsLen m B)
    (htieD : matOneValue (matScale s (siteDatum
        (siteDatum (matAdd H (matScale y G)) (matScale x G))
        (blockJoin
          (siteDatum (matAdd (siteDatum P (matScale cw D1))
            (matScale y G1)) (matScale x G1))
          (elim.nullMat k m)
          (siteDatum (matAdd Q (matScale y G2))
            (matScale (x + s) G2)))))
      (shiftSite W s B D1 G2))
    (hf : countAtPair H G x y nf spF)
    (hb : countAtPair (siteDatum P (matScale cw D1)) G1 x y n spB)
    (hr : countAtPair Q G2 (x + s) y 0 spR)
    (hD : splitRead (blockJoin
      (siteDatum (matAdd (siteDatum P (matScale cw D1))
        (matScale y G1)) (matScale x G1))
      (elim.nullMat k m)
      (siteDatum (matAdd Q (matScale y G2))
        (matScale (x + s) G2))) spD)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd (siteDatum P (matScale cw D1))
          (matScale y G1)) (matScale x G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale y G2))
          (matScale (x + s) G2)))) spd) :
    nf = n :=
  Nat.le_antisymm
    (count_bord_le H G M M1 M2 P G1 D1 Q G2 B x y cw W s nf n
      spU spL spF spD spd spB spR hcap hMt hM1 hM2l hD1 hG2 hB hBr
      htieD hf hb hr hD hd)
    (truncation.count_head_le H G P G1 Bt Q G2 x y n nf spH1 spF
      hBt htie hlow hf)

/-- `lem:contactcell`'s extent certificate: the contact cell's
`σ`-extent `σ₁` is the divisor's first positive root, committed as
the bracket `[lo, hi]` over the divisor's squarefree witness — the
segment from the unit up to the bracket's bottom at a vacant root
count and the bracket itself at one, the two segment counts of the
squarefree part's cleared variable with the endpoints rescaled by the
top's magnitude (`lem:hermitesign`'s bracket pencil at
`deckfactor.clearVarBT`, `lem:deckfactor`'s clearing at the value's
representative). -/
def extRead {o1 o2 o3 o4 : Nat} (D : Poly) (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos)
    (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4) : Prop :=
  cellcount.divRead D ct
  ∧ hermitesign.segCountRead (deckfactor.clearVarBT ct.sq)
      (deckfactor.clearAt ct.sq BPair.unit)
      (deckfactor.clearAt ct.sq lo) c 0 spH1 spB1
  ∧ hermitesign.segCountRead (deckfactor.clearVarBT ct.sq)
      (deckfactor.clearAt ct.sq lo)
      (deckfactor.clearAt ct.sq hi) c 1 spH2 spB2

instance {o1 o2 o3 o4 : Nat} (D : Poly) (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos) (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4) :
    Decidable (extRead D ct lo hi c spH1 spB1 spH2 spB2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The extension read is one value across the divisor's
representatives: the certificate conjunct carries
(`cellcount.divRead_congr`) and the two counts read the
certificate's own squarefree part. -/
theorem extRead_congr {o1 o2 o3 o4 : Nat} {D D' : Poly}
    (h : poly.oneValue D D') (ct : cellcount.DivCert)
    (lo hi : BPair) (c : Pos) (spH1 : Split o1) (spB1 : Split o2)
    (spH2 : Split o3) (spB2 : Split o4) :
    extRead D ct lo hi c spH1 spB1 spH2 spB2
      ↔ extRead D' ct lo hi c spH1 spB1 spH2 spB2 :=
  ⟨fun hr => ⟨(cellcount.divRead_congr h ct).mp hr.1, hr.2⟩,
   fun hr => ⟨(cellcount.divRead_congr h ct).mpr hr.1, hr.2⟩⟩

/-! ## The full column's row -/

/-- `lem:pieri`'s complement row at the one-box factor: the
complement column's one-box additions are exactly the adjoint's
shape and the full column. -/
private theorem complRow_mem (d : Nat) (hd : 2 ≤ d) (x : places.Shape)
    (hpos : 0 < ground.countOf x (pieri.row (pieri.complBox d))) :
    x = adjchar.theta d ∨ x = dualread.fulls d 1 := by
  match d, hd with
  | g + 2, _ =>
    rw [adjchar.countOf_row_complBox g x] at hpos
    by_cases h1 : x = adjchar.theta (g + 2)
    · exact Or.inl h1
    · rw [if_neg h1, Nat.zero_add] at hpos
      by_cases h2 : x = dualread.fulls (g + 2) 1
      · exact Or.inr h2
      · rw [if_neg h2] at hpos
        exact absurd hpos (Nat.lt_irrefl 0)

/-- The full-column line's occupied content is the unit-monomial
one, `dualread.occ_line`'s membership read. -/
private theorem occ_fullCol (d : Nat) (m : List Nat)
    (hm : 0 < blockcount.occupancyAt
      (blockcount.blockSpan (dualread.fulls d 1)) m) :
    m = List.replicate d 1 := by
  rw [blockcount.occupancyAt_eq_occ, dualread.occ_line d 1 m] at hm
  by_cases h : m = List.replicate d 1
  · exact h
  · rw [if_neg h] at hm
    exact absurd hm (Nat.lt_irrefl 0)

private theorem foldl_fix {α β : Type} (F : β → α → β) :
    ∀ (L : List α) (a : β), (∀ x ∈ L, ∀ acc, F acc x = acc) →
      L.foldl F a = a
  | [], a, _ => rfl
  | x :: t, a, h => by
    show t.foldl F (F a x) = a
    rw [h x (List.Mem.head t) a]
    exact foldl_fix F t a (fun y hy => h y (List.Mem.tail x hy))

/-- `lem:contactcell`'s full-column summand at the sum's unit: off
the raised display the full column's fusion count is vacant — every
tie of the wedge block carries the all-ones content, and that
content forces the identity permutation with the target's display
the source's raised at every letter (`places.tieOnes`). -/
private theorem fullColVanish (d : Nat) (mu c : places.Shape)
    (hmu : mu.length = d) (hca : c.length = d)
    (hne : ¬ places.display c
      = (places.display mu).map (fun x => x + 1)) :
    blockcount.fusionCount (dualread.fulls d 1) mu c = 0 := by
  have hgs : steinberg.gradedSums (dualread.fulls d 1) mu c = (0, 0) := by
    show steinberg.sumsWith
        (blockcount.occupancyAt (blockcount.blockSpan (dualread.fulls d 1)))
        (dualread.fulls d 1).length mu c = (0, 0)
    rw [dualread.length_fulls d 1]
    show (places.perms d).foldl
      (fun acc p =>
        match ground.tieGap (places.display c)
            (places.expo (places.display mu) p) with
        | none => acc
        | some m =>
          if places.parity p then
            (acc.1, acc.2 + blockcount.occupancyAt
              (blockcount.blockSpan (dualread.fulls d 1)) m)
          else
            (acc.1 + blockcount.occupancyAt
              (blockcount.blockSpan (dualread.fulls d 1)) m, acc.2))
      (0, 0) = (0, 0)
    refine foldl_fix _ (places.perms d) (0, 0) ?_
    intro p hp acc
    cases hg : ground.tieGap (places.display c)
        (places.expo (places.display mu) p) with
    | none => rfl
    | some m =>
      have hz : blockcount.occupancyAt
          (blockcount.blockSpan (dualread.fulls d 1)) m = 0 := by
        match hh : blockcount.occupancyAt
            (blockcount.blockSpan (dualread.fulls d 1)) m with
        | 0 => rfl
        | n + 1 =>
          have hm1 := occ_fullCol d m (by rw [hh]; exact Nat.succ_pos n)
          exact absurd (places.tieOnes d mu c hmu p
            (ground.countOf_pos_of_mem hp) m hg
            (fun k hk => by
              rw [hm1]
              exact ground.getAt_replicate 0 1 d k hk)).2 hne
      show (if places.parity p then
          (acc.1, acc.2 + blockcount.occupancyAt
            (blockcount.blockSpan (dualread.fulls d 1)) m)
        else
          (acc.1 + blockcount.occupancyAt
            (blockcount.blockSpan (dualread.fulls d 1)) m, acc.2)) = acc
      rw [hz]
      cases places.parity p with
      | true =>
        show ((acc.1, acc.2 + 0) : Nat × Nat) = acc
        rw [Nat.add_zero]
      | false =>
        show ((acc.1 + 0, acc.2) : Nat × Nat) = acc
        rw [Nat.add_zero]
  have h2 : blockcount.fusionCount (dualread.fulls d 1) mu c
      + (steinberg.gradedSums (dualread.fulls d 1) mu c).2
    = (steinberg.gradedSums (dualread.fulls d 1) mu c).1 :=
    steinberg.readAll (dualread.fulls d 1) mu c
      (by rw [dualread.length_fulls]; exact hmu)
      (by rw [dualread.length_fulls]; exact hca)
  rw [hgs] at h2
  have h3 : blockcount.fusionCount (dualread.fulls d 1) mu c + 0 = 0 := h2
  rw [Nat.add_zero] at h3
  exact h3

/-! ## The moved pair's two rows -/

private theorem removals_head_mem (s : places.Shape) (hd : 0 < s.length)
    (ho : 0 < ground.getAt 0 s 0) :
    0 < ground.countOf (ground.dipAt 0 s) (units.removals s) := by
  match s, hd, ho with
  | a :: t, _, ho =>
    rw [units.removals_split a t (ground.dipAt 0 (a :: t))]
    refine Nat.lt_of_lt_of_le ?_
      (Nat.le_add_right _ (ground.famFold Nat.add 0 _ _))
    rw [if_pos (show 0 < a from ho)]
    show 0 < ground.countOf ((a - 1) :: t) [(a - 1) :: t]
    rw [ground.countOf_head]
    exact Nat.succ_pos _

private theorem removals_flat_mem (s : places.Shape) (i : Nat)
    (hi : i + 1 < s.length) (ho : 0 < ground.getAt 0 s (i + 1)) :
    0 < ground.countOf (units.moveUp i s) (units.removals s) := by
  match s, hi, ho with
  | a :: t, hi, ho =>
    have hit : i < t.length := Nat.lt_of_succ_lt_succ hi
    rw [units.removals_split a t (units.moveUp i (a :: t))]
    refine Nat.lt_of_lt_of_le ?_
      (Nat.le_add_left _ (ground.countOf _ (if 0 < a then _ else _)))
    refine Nat.lt_of_lt_of_le ?_
      (ground.famFold_mem_le _ (List.range t.length) i
        (ground.mem_of_countOf_pos i _ (ground.countOf_range_pos hit)))
    rw [if_pos ho, ground.countOf_head]
    exact Nat.succ_pos _

/-- The box withdrawn at a stated row: the head column dropped, or
the column above the row shortened by one — `con:units`' removal at
the row's own key. -/
private def dropRow : Nat → places.Shape → places.Shape
  | 0, x => ground.dipAt 0 x
  | p + 1, x => units.moveUp p x

private theorem length_dropRow : ∀ (p : Nat) (x : places.Shape),
    (dropRow p x).length = x.length
  | 0, x => ground.length_dipAt 0 x
  | _ + 1, x => units.length_moveUp _ x

private theorem rowList_dropRow : ∀ (p : Nat) (x : places.Shape),
    p < x.length → 0 < ground.getAt 0 x p →
    places.rowList (dropRow p x) = ground.dipAt p (places.rowList x)
  | 0, x, hp, ho => by
    show places.rowList (ground.dipAt 0 x)
      = ground.dipAt 0 (places.rowList x)
    match x, hp, ho with
    | a :: t, _, ho =>
      have hsub : a - 1 + 1 = a := ground.subAdd ho
      have h := units.rowList_grow (a - 1) t
      rw [hsub] at h
      show places.rowList ((a - 1) :: t)
        = ground.dipAt 0 (places.rowList (a :: t))
      rw [h, ground.dipAt_bumpAt_self]
  | p + 1, x, hp, ho =>
    units.rowList_moveUp p x hp ho

private theorem removals_dropRow : ∀ (p : Nat) (x : places.Shape),
    p < x.length → 0 < ground.getAt 0 x p →
    0 < ground.countOf (dropRow p x) (units.removals x)
  | 0, x, hp, ho => removals_head_mem x hp ho
  | p + 1, x, hp, ho => removals_flat_mem x p hp ho

private theorem row_dropRow (p : Nat) (x : places.Shape)
    (hp : p < x.length) (ho : 0 < ground.getAt 0 x p) :
    0 < ground.countOf x (pieri.row (dropRow p x)) := by
  rw [pathsquare.row_removals (dropRow p x) x]
  exact removals_dropRow p x hp ho

private theorem fullCol_addS (mu : places.Shape) (d : Nat)
    (hmu : mu.length = d) (hd : 0 < d) :
    places.addS mu (dualread.fulls d 1) = ground.bumpAt (d - 1) mu := by
  rw [dualread.fulls_one_unitAt d hd]
  have hlen : (places.addS mu (ground.unitAt d (d - 1))).length = d :=
    ground.length_zipWith (fun x y => x + y) mu (ground.unitAt d (d - 1))
      d hmu (ground.length_unitAt d (d - 1))
  have hpd : d - 1 < d := ground.subOneLt hd
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [hlen, ground.length_bumpAt, hmu]
  · intro k hk
    rw [hlen] at hk
    rw [show places.addS mu (ground.unitAt d (d - 1))
        = List.zipWith (fun x y => x + y) mu (ground.unitAt d (d - 1))
        from rfl,
      ground.getAt_zipWith 0 0 0 (fun x y => x + y) mu
        (ground.unitAt d (d - 1)) k
        (by rw [hmu]; exact hk) (by rw [ground.length_unitAt]; exact hk),
      ground.getAt_unitAt d (d - 1) k, if_pos hk]
    by_cases he : k = d - 1
    · rw [if_pos he, he,
        ground.getAt_bumpAt_self (d - 1) mu (by rw [hmu]; exact hpd)]
    · rw [if_neg he, ground.getAt_bumpAt_ne (d - 1) mu k he,
        Nat.add_zero]

private theorem rowList_bumpTop (mu : places.Shape) (d : Nat)
    (hmu : mu.length = d) (hd : 0 < d) (k : Nat) (hk : k < d) :
    ground.getAt 0 (places.rowList (ground.bumpAt (d - 1) mu)) k
      = ground.getAt 0 (places.rowList mu) k + 1 := by
  rw [← fullCol_addS mu d hmu hd,
    places.rowList_addS mu (dualread.fulls d 1)
      (by rw [dualread.length_fulls, hmu]),
    ground.getAt_zipWith 0 0 0 (fun x y => x + y)
      (places.rowList mu) (places.rowList (dualread.fulls d 1)) k
      (by rw [places.length_rowList, hmu]; exact hk)
      (by rw [places.length_rowList, dualread.length_fulls]; exact hk),
    dualread.rowList_fulls d 1, ground.getAt_replicate 0 1 d k hk]


/-- `lem:contactcell`'s moved pair as an occupied row read: at the
letter-pair-move tie the withdrawn box's row and the added one's
name one intermediate shape — the target's display lowered by one
at the raised place, equivalently the source's full-column raise
withdrawn at the lowered place. -/
private theorem moveWitness (d : Nat) (mu c : places.Shape) (m : List Nat)
    (hd : 2 ≤ d) (hmul : mu.length = d) (hcl : c.length = d)
    (htie : ground.tieGap (places.display c) (places.display mu)
      = some m)
    (hml : m.length = d) (hc0 : ground.countOf 0 m = 1)
    (hc2 : ground.countOf 2 m = 1) (hc1 : ground.countOf 1 m + 2 = d) :
    ∃ e : places.Shape, e.length = d
      ∧ 0 < ground.countOf e (pieri.rowD mu)
      ∧ 0 < ground.countOf c (pieri.row e)
      ∧ ¬ places.display c
          = (places.display mu).map (fun x => x + 1) := by
  have hdz : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_two hd
  have hpd : d - 1 < d := ground.subOneLt hdz
  obtain ⟨i, hi, hiv⟩ := ground.getAt_of_mem 0
    (ground.mem_of_countOf_pos 2 m (by rw [hc2]; exact Nat.succ_pos 0))
  obtain ⟨j, hj, hjv⟩ := ground.getAt_of_mem 0
    (ground.mem_of_countOf_pos 0 m (by rw [hc0]; exact Nat.succ_pos 0))
  have hid : i < d := by rw [← hml]; exact hi
  have hjd : j < d := by rw [← hml]; exact hj
  have hij : ¬ i = j := by
    intro he
    rw [he, hjv] at hiv
    exact absurd hiv (by decide +kernel)
  have hji : ¬ j = i := fun he => hij he.symm
  have hone : ∀ k, k < d → ¬ k = i → ¬ k = j →
      ground.getAt 0 m k = 1 := by
    intro k hk hki hkj
    have hkm : k < m.length := by rw [hml]; exact hk
    have hcap := (adjchar.multRead_flat d m
      (by rw [adjchar.multRead_move d m hml hc0 hc2 hc1]
          exact Nat.succ_pos 0)).1 k
    match hv : ground.getAt 0 m k with
    | 0 =>
      have hp2 := ground.countOf_two_pos 0 m k j hkm hj hkj
        (by rw [hv, hjv])
      rw [hv, hc0] at hp2
      exact absurd hp2 (Nat.not_succ_le_self 1)
    | 1 => rfl
    | 2 =>
      have hp2 := ground.countOf_two_pos 0 m k i hkm hi hki
        (by rw [hv, hiv])
      rw [hv, hc2] at hp2
      exact absurd hp2 (Nat.not_succ_le_self 1)
    | v + 3 =>
      rw [hv] at hcap
      exact absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hcap))
        (Nat.not_succ_le_zero v)
  have hclen : (places.display c).length = d := by
    rw [places.length_display, hcl]
  obtain ⟨_, _, hent⟩ := ground.tieGap_reads _ _ _ htie
  have hrow : ∀ k, k < d →
      ground.getAt 0 (places.rowList c) k
        = ground.getAt 0 m k + ground.getAt 0 (places.rowList mu) k := by
    intro k hk
    have he := hent k (by rw [hclen]; exact hk)
    rw [places.getAt_display c k (by rw [hcl]; exact hk),
      places.getAt_display mu k (by rw [hmul]; exact hk), hcl, hmul,
      ← Nat.add_assoc] at he
    exact (ground.addCancelR (d - k) he).symm
  have hsucc : ∀ x : Nat, x < d → ¬ x = d - 1 → x + 1 < d := by
    intro x hx hne
    by_cases hc : x + 1 < d
    · exact hc
    · refine absurd (show x = d - 1 from ?_) hne
      rw [← Nat.le_antisymm hx (Nat.le_of_not_lt hc)]
      rfl
  have hocci : 0 < ground.getAt 0 c i := by
    have hgap := places.rowList_gap c i (by rw [hcl]; exact hid)
    match hv : ground.getAt 0 c i with
    | 0 =>
      rw [hv, Nat.zero_add] at hgap
      have h1 := hrow i hid
      rw [hiv] at h1
      by_cases hie : i = d - 1
      · have hover : ground.getAt 0 (places.rowList c) (i + 1) = 0 :=
          ground.getAt_over 0 (places.rowList c) (i + 1)
            (by rw [places.length_rowList, hcl, hie]
                exact Nat.le_of_eq (ground.subAdd hdz).symm)
        rw [hover, h1] at hgap
        have hposi : 0 < 2 + ground.getAt 0 (places.rowList mu) i :=
          Nat.lt_of_lt_of_le (Nat.succ_pos 1) (Nat.le_add_right 2 _)
        rw [hgap] at hposi
        exact absurd hposi (Nat.lt_irrefl 0)
      · have hi1 : i + 1 < d := hsucc i hid hie
        have h2 := hrow (i + 1) hi1
        have hle : ground.getAt 0 m (i + 1) ≤ 1 := by
          by_cases he : i + 1 = j
          · rw [he, hjv]
            exact Nat.zero_le 1
          · rw [hone (i + 1) hi1 (fun hh => Nat.noConfusion
              (ground.addCancelL i (show i + 1 = i + 0 by
                rw [Nat.add_zero]; exact hh))) he]
            exact Nat.le_refl 1
        have hmono := places.rowList_le mu i (by rw [hmul]; exact hi1)
        rw [h1, h2] at hgap
        have hbad : 2 + ground.getAt 0 (places.rowList mu) i
            ≤ 1 + ground.getAt 0 (places.rowList mu) i := by
          rw [hgap]
          exact Nat.add_le_add hle hmono
        rw [Nat.add_comm 2 _, Nat.add_comm 1 _] at hbad
        exact absurd (ground.leCancelL _ hbad) (by decide +kernel)
    | n + 1 => exact Nat.succ_pos n
  have hoccw : 0 < ground.getAt 0 (ground.bumpAt (d - 1) mu) j := by
    by_cases he : j = d - 1
    · rw [he, ground.getAt_bumpAt_self (d - 1) mu
        (by rw [hmul]; exact hpd)]
      exact Nat.succ_pos _
    · rw [ground.getAt_bumpAt_ne (d - 1) mu j he]
      have hj1 : j + 1 < d := hsucc j hjd he
      match hv : ground.getAt 0 mu j with
      | 0 =>
        have hgapmu := places.rowList_gap mu j (by rw [hmul]; exact hjd)
        rw [hv, Nat.zero_add] at hgapmu
        have h1 := hrow j hjd
        rw [hjv, Nat.zero_add] at h1
        have h2 := hrow (j + 1) hj1
        have hmono := places.rowList_le c j (by rw [hcl]; exact hj1)
        rw [h1, h2, hgapmu] at hmono
        have hmz : ground.getAt 0 m (j + 1) = 0 :=
          Nat.eq_zero_of_le_zero (ground.leCancelR _
            (show ground.getAt 0 m (j + 1)
                + ground.getAt 0 (places.rowList mu) (j + 1)
              ≤ 0 + ground.getAt 0 (places.rowList mu) (j + 1) by
              rw [Nat.zero_add]
              exact hmono))
        have hp2 := ground.countOf_two_pos 0 m (j + 1) j
          (by rw [hml]; exact hj1) hj
          (fun hh => Nat.noConfusion (ground.addCancelL j
            (show j + 1 = j + 0 by rw [Nat.add_zero]; exact hh)))
          (by rw [hmz, hjv])
        rw [hmz, hc0] at hp2
        exact absurd hp2 (Nat.not_succ_le_self 1)
      | n + 1 => exact Nat.succ_pos n
  have hwlen : (ground.bumpAt (d - 1) mu).length = d := by
    rw [ground.length_bumpAt, hmul]
  have hEq : dropRow j (ground.bumpAt (d - 1) mu) = dropRow i c := by
    refine places.rowList_inj _ _ ?_
    rw [rowList_dropRow j (ground.bumpAt (d - 1) mu)
        (by rw [hwlen]; exact hjd) hoccw,
      rowList_dropRow i c (by rw [hcl]; exact hid) hocci]
    have hrw : ∀ k, k < d →
        ground.getAt 0 (places.rowList (ground.bumpAt (d - 1) mu)) k
          = ground.getAt 0 (places.rowList mu) k + 1 :=
      fun k hk => rowList_bumpTop mu d hmul hdz k hk
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [ground.length_dipAt, ground.length_dipAt,
        places.length_rowList, places.length_rowList, hwlen, hcl]
    · intro k hk
      rw [ground.length_dipAt, places.length_rowList, hwlen] at hk
      by_cases hkj : k = j
      · have hL : ground.getAt 0 (ground.dipAt j
            (places.rowList (ground.bumpAt (d - 1) mu))) j + 1
            = ground.getAt 0
              (places.rowList (ground.bumpAt (d - 1) mu)) j :=
          ground.getAt_dipAt_self j _
            (by rw [hrw j hjd]; exact Nat.succ_pos _)
        rw [hrw j hjd] at hL
        rw [hkj, ground.getAt_dipAt_ne i (places.rowList c) j hji,
          hrow j hjd, hjv, Nat.zero_add]
        exact Nat.succ.inj hL
      · by_cases hki : k = i
        · have hR : ground.getAt 0 (ground.dipAt i
              (places.rowList c)) i + 1
              = ground.getAt 0 (places.rowList c) i :=
            ground.getAt_dipAt_self i _
              (by rw [hrow i hid, hiv]
                  exact Nat.lt_of_lt_of_le (Nat.succ_pos 1)
                    (Nat.le_add_right 2 _))
          rw [hrow i hid, hiv] at hR
          have hval : ground.getAt 0
              (ground.dipAt i (places.rowList c)) i
              = ground.getAt 0 (places.rowList mu) i + 1 := by
            refine ground.addCancelR 1 ?_
            rw [hR, Nat.add_comm 2 (ground.getAt 0
              (places.rowList mu) i), Nat.add_assoc]
          rw [hki, ground.getAt_dipAt_ne j
            (places.rowList (ground.bumpAt (d - 1) mu)) i
            hij, hrw i hid, hval]
        · rw [ground.getAt_dipAt_ne j _ k hkj,
            ground.getAt_dipAt_ne i _ k hki, hrw k hk,
            hrow k hk, hone k hk hki hkj, Nat.add_comm 1 _]
  refine ⟨dropRow i c, by rw [length_dropRow, hcl], ?_,
    row_dropRow i c (by rw [hcl]; exact hid) hocci, ?_⟩
  · show 0 < ground.countOf (dropRow i c)
      (units.removals (ground.bumpAt (mu.length - 1) mu))
    rw [hmul, ← hEq]
    exact removals_dropRow j (ground.bumpAt (d - 1) mu)
      (by rw [hwlen]; exact hjd) hoccw
  · intro heq
    have h1 : ground.getAt 0 (places.display c) j
        = ground.getAt 0 (places.display mu) j + 1 := by
      rw [heq, ground.getAt_map 0 0 (fun x => x + 1)
        (places.display mu) j
        (by rw [places.length_display, hmul]; exact hjd)]
    have h2 := hent j (by rw [hclen]; exact hjd)
    rw [hjv, Nat.zero_add] at h2
    rw [← h2] at h1
    exact absurd h1 (Nat.ne_of_lt (Nat.lt_succ_self _))

/-- `lem:contactcell`'s stencil membership: at a letter-pair-move
tie between two shapes of one width the adjoint's fusion count at
the target is occupied — the fundamental against its complement
collects the target's count through the associativity at the two
one-box rows (`lem:pieri`; `lem:blockcount`(iii)), the complement
row carrying exactly the adjoint's shape and the full column, and
the full-column summand reads the sum's unit at the moved target
(`lem:adjchar`'s letter-pair content; `con:labels`). -/
theorem boxRow (d : Nat) (mu c : places.Shape) (m : List Nat)
    (hmul : mu.length = d) (hcl : c.length = d)
    (htie : ground.tieGap (places.display c) (places.display mu)
      = some m)
    (hml : m.length = d)
    (hc0 : ground.countOf 0 m = 1)
    (hc2 : ground.countOf 2 m = 1)
    (hc1 : ground.countOf 1 m + 2 = d) :
    0 < blockcount.fusionCount mu (adjchar.theta d) c := by
  have hd : 2 ≤ d := by
    rw [← hc1]
    exact Nat.le_add_left 2 _
  have hdz : 0 < d := Nat.lt_of_lt_of_le Nat.zero_lt_two hd
  have hoblen : (pieri.oneBox d).length = d := pieri.length_oneBox d
  have hcblen : (pieri.complBox d).length = d := pieri.length_complBox d
  obtain ⟨e, helen, herow, hcrow, hnd⟩ :=
    moveWitness d mu c m hd hmul hcl htie hml hc0 hc2 hc1
  have hRD : blockcount.fusionCount mu (pieri.complBox mu.length) e
      = ground.countOf e (pieri.rowD mu) :=
    pieri.readAllD mu e (by rw [hmul]; exact hd) (by rw [helen, hmul])
  rw [hmul] at hRD
  have h1 : 0 < blockcount.fusionCount (pieri.complBox d) mu e := by
    rw [← blockcount.fusionCount_comm mu (pieri.complBox d) e
      (by rw [hcblen, hmul]), hRD]
    exact herow
  have hR : blockcount.fusionCount e (pieri.oneBox e.length) c
      = ground.countOf c (pieri.row e) :=
    pieri.readAll e c (by rw [helen]; exact hdz) (by rw [hcl, helen])
  rw [helen] at hR
  have h2 : 0 < blockcount.fusionCount (pieri.oneBox d) e c := by
    rw [← blockcount.fusionCount_comm e (pieri.oneBox d) c
      (by rw [hoblen, helen]), hR]
    exact hcrow
  have hassoc := blockcount.fusionCount_assoc (pieri.oneBox d)
    (pieri.complBox d) mu c (by rw [hcblen, hoblen])
    (by rw [hoblen]; exact hmul) (by rw [hoblen]; exact hcl)
  rw [hoblen] at hassoc
  obtain ⟨hsz2, hwid2, hcl2, _⟩ :=
    blockcount.fusedSpan_pack (pieri.complBox d) mu
      (by rw [hcblen]; exact hmul)
  rw [hcblen] at hwid2 hcl2
  have hmem2 : places.rowList e ∈ ground.dedupL
      ((blockcount.exhaust d (blockcount.fusedAt
        (blockcount.blockSpan (pieri.complBox d))
        (blockcount.blockSpan mu))).map blockcount.HVec.content) := by
    refine ground.mem_dedupL (ground.mem_of_countOf_pos _ _ ?_)
    have hcnt := blockcount.fusionCount_countAt (pieri.complBox d) mu e
      (by rw [hcblen]; exact hmul)
    have hex := blockcount.countAt_exhaust d _ hsz2 hwid2 hcl2
      (places.rowList e)
    rw [hcnt, hex, blockcount.occ_eq_countOf] at h1
    exact h1
  have hshape : places.shapeOf (places.rowList e) = e := places.shapeOf_rowList e
  have hRHSpos : 0 < ground.famFold Nat.add 0
      (fun nu => blockcount.fusionCount (pieri.complBox d) mu
          (places.shapeOf nu)
        * blockcount.fusionCount (pieri.oneBox d) (places.shapeOf nu) c)
      (ground.dedupL
        ((blockcount.exhaust d (blockcount.fusedAt
          (blockcount.blockSpan (pieri.complBox d))
          (blockcount.blockSpan mu))).map blockcount.HVec.content)) := by
    refine Nat.lt_of_lt_of_le ?_ (ground.famFold_mem_le _ _ _ hmem2)
    show 0 < blockcount.fusionCount (pieri.complBox d) mu
        (places.shapeOf (places.rowList e))
      * blockcount.fusionCount (pieri.oneBox d)
        (places.shapeOf (places.rowList e)) c
    rw [hshape]
    exact Nat.mul_pos h1 h2
  have hLHSpos : 0 < ground.famFold Nat.add 0
      (fun nu => blockcount.fusionCount (pieri.oneBox d)
          (pieri.complBox d) (places.shapeOf nu)
        * blockcount.fusionCount (places.shapeOf nu) mu c)
      (ground.dedupL
        ((blockcount.exhaust d (blockcount.fusedAt
          (blockcount.blockSpan (pieri.oneBox d))
          (blockcount.blockSpan (pieri.complBox d)))).map
          blockcount.HVec.content)) := by
    rw [hassoc]
    exact hRHSpos
  obtain ⟨nu, hnu, hfnu⟩ := ground.famFold_pos_mem _ _ hLHSpos
  obtain ⟨hfa, hfb⟩ := ground.mulPosSplit hfnu
  obtain ⟨hsz1, hwid1, hcl1, _⟩ :=
    blockcount.fusedSpan_pack (pieri.oneBox d) (pieri.complBox d)
      (by rw [hcblen, hoblen])
  rw [hoblen] at hwid1 hcl1
  have hnulen : nu.length = d :=
    blockcount.exhaust_width d _ hsz1 hwid1 hcl1 nu
      (ground.mem_of_dedupL hnu)
  have hsnlen : (places.shapeOf nu).length = d := by
    rw [places.length_shapeOf]
    exact hnulen
  have hcm : 0 < ground.countOf (places.shapeOf nu)
      (pieri.row (pieri.complBox d)) := by
    have hrd : blockcount.fusionCount (pieri.complBox d)
        (pieri.oneBox (pieri.complBox d).length) (places.shapeOf nu)
        = ground.countOf (places.shapeOf nu)
          (pieri.row (pieri.complBox d)) :=
      pieri.readAll (pieri.complBox d) (places.shapeOf nu)
        (by rw [hcblen]; exact hdz) (by rw [hcblen, hsnlen])
    rw [hcblen] at hrd
    rw [← hrd, ← blockcount.fusionCount_comm (pieri.oneBox d)
      (pieri.complBox d) (places.shapeOf nu) (by rw [hcblen, hoblen])]
    exact hfa
  cases complRow_mem d hd (places.shapeOf nu) hcm with
  | inl hth =>
    rw [hth] at hfb
    rw [blockcount.fusionCount_comm mu (adjchar.theta d) c
      (by rw [adjchar.length_theta, hmul])]
    exact hfb
  | inr hfc =>
    rw [hfc, fullColVanish d mu c hmul hcl hnd] at hfb
    exact absurd hfb (Nat.lt_irrefl 0)

/-- `lem:contactcell`'s frontier: the head's adjoint rows beyond
the cutoff.  The head is the `X`-sector chain's — the unit label
with the below-cutoff labels at the unit class
(`lem:chargedcell`(i)'s own sector) — and a target is a frontier
target when its cleared Casimir leaves the cutoff
(`prop:fusionfinite`).  The row is `lem:rankstable`'s word list
(`rankstable.adjRow`), the enumeration's own at every head label
(`rankstable.adjRow_eq`). -/
def frontierTargets (d K : Nat) : List places.Shape :=
  ((fusion.dataA d).unit :: ((fusion.dataA d).below K).filter
      (fun l => Nat.beq ((fusion.dataA d).cls l) 0)).flatMap
    (fun l => (rankstable.adjRow d l).filter
      (fun c => decide (K < c2hat.dfQ c)))

/-- `c₊`, the least Casimir beyond the cutoff among the frontier's
targets: the seed floor `F = ⟨4σc₊ : d_ϑ⟩`'s own numerator datum,
the auxiliary diagonal's first member.  At an occupied frontier it
sits beyond the cutoff itself (`cPlusN_beyond`). -/
def cPlusN (d K : Nat) : Nat :=
  match frontierTargets d K with
  | [] => 0
  | h :: tl =>
    tl.foldl (fun a c => ground.natMin a (c2hat.dfQ c)) (c2hat.dfQ h)

/-- Every frontier target's cleared Casimir leaves the cutoff, the
enumeration's own filter. -/
private theorem frontierBeyond (d K : Nat) :
    ∀ c ∈ frontierTargets d K, K < c2hat.dfQ c := by
  refine ground.all_of_flatMap (fun c => K < c2hat.dfQ c) _
    (fun l x hx => ?_) _
  exact of_decide_eq_true
    (ground.all_of_filter (fun _ => True)
      (fun c => decide (K < c2hat.dfQ c)) (rankstable.adjRow d l)
      (fun _ _ => trivial) x hx).2

/-- The least of a walk's Casimirs stays beyond the cutoff at a
seed beyond it and members beyond it. -/
private theorem foldMinBeyond (K : Nat) :
    ∀ (l : List places.Shape) (s : Nat), K < s →
      (∀ c ∈ l, K < c2hat.dfQ c) →
      K < l.foldl (fun a c => ground.natMin a (c2hat.dfQ c)) s
  | [], _, hs, _ => hs
  | c :: t, s, hs, hall =>
    foldMinBeyond K t (ground.natMin s (c2hat.dfQ c))
      (ground.le_natMin hs (hall c (List.Mem.head t)))
      (fun z hz => hall z (List.Mem.tail c hz))

/-- An occupied frontier's least Casimir sits beyond its cutoff:
every target's cleared Casimir exceeds `K`, so the fold's least
does (`lem:corner`'s frontier family, the parenthetical's own
read). -/
theorem cPlusN_beyond (d K : Nat)
    (h : frontierTargets d K ≠ []) : K < cPlusN d K := by
  have hall := frontierBeyond d K
  show K < (match frontierTargets d K with
    | [] => 0
    | hd :: tl =>
      tl.foldl (fun a c => ground.natMin a (c2hat.dfQ c))
        (c2hat.dfQ hd))
  cases hft : frontierTargets d K with
  | nil => exact absurd hft h
  | cons hd tl =>
    rw [hft] at hall
    exact foldMinBeyond K tl (c2hat.dfQ hd)
      (hall hd (List.Mem.head tl))
      (fun z hz => hall z (List.Mem.tail hd hz))

/-! The frontier landing's walk kit: an excluded unit-class label
descends the cleared Casimir along `lem:casfloor`'s moves, each
move an occupied adjoint-row read at the two-point tie display,
and the walk lands the label in a head label's adjoint row at a
frontier target at or below the label's own read —
`lem:contactcell`'s "a minimal excluded label sits in the head, a
frontier target's source". -/

/-- A weakly descending list reads its head at or beyond every
entry. -/
private theorem desc_ge (l : List Nat)
    (hdesc : ∀ p, p + 1 < l.length →
      ground.getAt 0 l (p + 1) ≤ ground.getAt 0 l p) :
    ∀ q, q < l.length → ground.getAt 0 l q ≤ ground.getAt 0 l 0 := by
  intro q
  induction q with
  | zero => intro _; exact Nat.le_refl _
  | succ p ih =>
    intro hq
    exact Nat.le_trans (hdesc p hq) (ih (Nat.lt_of_succ_lt hq))

/-- The occupancy total sits at or below the degree: the first row
already counts every column. -/
private theorem sumNat_le_degree : ∀ s : places.Shape,
    ground.sumNat s ≤ places.degree s
  | [] => Nat.le_refl 0
  | n :: t =>
    Nat.le_add_right (n + ground.sumNat t)
      (ground.sumNat (places.rowList t))

/-- The row list's last entry is the shape's own last occupancy,
the off-list read vacant. -/
private theorem d_le_of_mod (d n : Nat) (hn : 0 < n)
    (hmod : n % d = 0) : d ≤ n := by
  cases Nat.lt_or_ge n d with
  | inl hlt =>
    rw [ground.modOfLt n d hlt] at hmod
    rw [hmod] at hn
    exact absurd hn (Nat.lt_irrefl 0)
  | inr hge => exact hge

/-- A total beyond the length names an entry at or beyond two. -/
private theorem exists_two_of_gt : ∀ l : List Nat,
    l.length + 1 ≤ ground.sumNat l →
    ∃ k, k < l.length ∧ 2 ≤ ground.getAt 0 l k
  | [], h => absurd h (Nat.not_succ_le_zero 0)
  | x :: t, h => by
    cases Nat.lt_or_ge x 2 with
    | inr h2 => exact ⟨0, Nat.succ_pos t.length, h2⟩
    | inl hx =>
      have hx1 : x ≤ 1 := Nat.le_of_lt_succ hx
      have ht : t.length + 1 ≤ ground.sumNat t := by
        have h1 : t.length + 1 + 1 ≤ x + ground.sumNat t := h
        have h2 : x + ground.sumNat t ≤ 1 + ground.sumNat t :=
          Nat.add_le_add_right hx1 _
        have h3 : t.length + 1 + 1 ≤ 1 + ground.sumNat t :=
          Nat.le_trans h1 h2
        rw [Nat.add_comm 1 (ground.sumNat t)] at h3
        exact Nat.le_of_succ_le_succ h3
      match exists_two_of_gt t ht with
      | ⟨k, hk, hk2⟩ => exact ⟨k + 1, Nat.succ_lt_succ hk, hk2⟩

/-- A reduced list at a total at or beyond its length names an
entry at or beyond two: some column repeats a length. -/
private theorem exists_two_red : ∀ (l : List Nat) (z : Nat),
    z < l.length → ground.getAt 0 l z = 0 →
    l.length ≤ ground.sumNat l →
    ∃ k, k < l.length ∧ 2 ≤ ground.getAt 0 l k
  | [], z, hz, _, _ => absurd hz (Nat.not_lt_zero z)
  | x :: t, 0, _, h0, hs => by
    have hx : x = 0 := h0
    have ht : t.length + 1 ≤ ground.sumNat t := by
      have h1 : t.length + 1 ≤ x + ground.sumNat t := hs
      rw [hx, Nat.zero_add] at h1
      exact h1
    match exists_two_of_gt t ht with
    | ⟨k, hk, hk2⟩ => exact ⟨k + 1, Nat.succ_lt_succ hk, hk2⟩
  | x :: t, z + 1, hz, h0, hs => by
    cases Nat.lt_or_ge x 2 with
    | inr h2 => exact ⟨0, Nat.succ_pos t.length, h2⟩
    | inl hx =>
      have hx1 : x ≤ 1 := Nat.le_of_lt_succ hx
      have ht : t.length ≤ ground.sumNat t := by
        have h1 : t.length + 1 ≤ x + ground.sumNat t := hs
        have h2 : x + ground.sumNat t ≤ 1 + ground.sumNat t :=
          Nat.add_le_add_right hx1 _
        have h3 : t.length + 1 ≤ 1 + ground.sumNat t :=
          Nat.le_trans h1 h2
        rw [Nat.add_comm 1 (ground.sumNat t)] at h3
        exact Nat.le_of_succ_le_succ h3
      match exists_two_red t z (Nat.lt_of_succ_lt_succ hz) h0 ht with
      | ⟨k, hk, hk2⟩ => exact ⟨k + 1, Nat.succ_lt_succ hk, hk2⟩

/-- The move tie's display: one entry at two (the withdrawn box's
row), one vacant (the added box's), the rest at one — the
letter-pair move's gap list. -/
private def tieM (i g' e : Nat) : List Nat :=
  List.replicate i 1
    ++ 2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1)

private theorem tie_arith (i g' e : Nat) :
    i + (g' + 1) + e + 1 = i + (g' + (e + 2)) := by
  rw [Nat.add_assoc (i + (g' + 1)) e 1,
    Nat.add_assoc i (g' + 1) (e + 1),
    Nat.add_assoc g' 1 (e + 1), Nat.add_comm 1 (e + 1)]

private theorem length_tieM (i g' e : Nat) :
    (tieM i g' e).length = i + (g' + (e + 2)) := by
  show (List.replicate i 1
    ++ 2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1)).length
    = i + (g' + (e + 2))
  rw [ground.length_append, ground.length_replicate]
  show i + ((List.replicate g' 1
    ++ 0 :: List.replicate e 1).length + 1) = i + (g' + (e + 2))
  rw [ground.length_append, ground.length_replicate]
  show i + (g' + ((List.replicate e 1).length + 1) + 1)
    = i + (g' + (e + 2))
  rw [ground.length_replicate, Nat.add_assoc g' (e + 1) 1]

private theorem countOf0_tieM (i g' e : Nat) :
    ground.countOf 0 (tieM i g' e) = 1 := by
  show ground.countOf 0 (List.replicate i 1
    ++ 2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1)) = 1
  rw [ground.countOf_append,
    ground.countOf_replicate_ne 0 1 (by decide +kernel) i,
    ground.countOf_head_ne (show (0 : Nat) ≠ 2 by decide +kernel),
    ground.countOf_append,
    ground.countOf_replicate_ne 0 1 (by decide +kernel) g',
    ground.countOf_head,
    ground.countOf_replicate_ne 0 1 (by decide +kernel) e]

private theorem countOf2_tieM (i g' e : Nat) :
    ground.countOf 2 (tieM i g' e) = 1 := by
  show ground.countOf 2 (List.replicate i 1
    ++ 2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1)) = 1
  rw [ground.countOf_append,
    ground.countOf_replicate_ne 2 1 (by decide +kernel) i,
    ground.countOf_head,
    ground.countOf_append,
    ground.countOf_replicate_ne 2 1 (by decide +kernel) g',
    ground.countOf_head_ne (show (2 : Nat) ≠ 0 by decide +kernel),
    ground.countOf_replicate_ne 2 1 (by decide +kernel) e]

private theorem countOf1_tieM (i g' e : Nat) :
    ground.countOf 1 (tieM i g' e) + 2 = i + (g' + (e + 2)) := by
  show ground.countOf 1 (List.replicate i 1
    ++ 2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1)) + 2
    = i + (g' + (e + 2))
  rw [ground.countOf_append, ground.countOf_replicate 1 i,
    ground.countOf_head_ne (show (1 : Nat) ≠ 2 by decide +kernel),
    ground.countOf_append, ground.countOf_replicate 1 g',
    ground.countOf_head_ne (show (1 : Nat) ≠ 0 by decide +kernel),
    ground.countOf_replicate 1 e,
    Nat.add_assoc i (g' + e) 2, Nat.add_assoc g' e 2]

/-- The tie display's entries: two at the withdrawn row's key,
vacant at the added row's, one elsewhere. -/
private theorem getAt_tieM (i g' e p : Nat)
    (hp : p < i + (g' + (e + 2))) :
    ground.getAt 0 (tieM i g' e) p
      = if p = i then 2
        else if p = i + (g' + 1) then 0 else 1 := by
  cases Nat.lt_or_ge p i with
  | inl hpi =>
    have h1 : ground.getAt 0 (tieM i g' e) p = 1 := by
      show ground.getAt 0 (List.replicate i 1
        ++ 2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1)) p
        = 1
      rw [ground.getAt_append 0 (List.replicate i 1) _ p,
        ground.length_replicate, if_pos hpi]
      exact ground.getAt_replicate 0 1 i p hpi
    rw [h1,
      if_neg (show ¬ p = i by
        intro he
        rw [he] at hpi
        exact absurd hpi (Nat.lt_irrefl i)),
      if_neg (show ¬ p = i + (g' + 1) by
        intro he
        rw [he] at hpi
        exact absurd
          (Nat.lt_of_le_of_lt (Nat.le_add_right i (g' + 1)) hpi)
          (Nat.lt_irrefl i))]
  | inr hge =>
    match Nat.le.dest hge with
    | ⟨q, hq⟩ =>
      have hread : ground.getAt 0 (tieM i g' e) p
          = ground.getAt 0
            (2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1))
            q := by
        rw [← hq]
        have h := ground.getAt_append_add 0 (List.replicate i 1)
          (2 :: (List.replicate g' 1 ++ 0 :: List.replicate e 1)) q
        rw [ground.length_replicate] at h
        exact h
      match q, hq with
      | 0, hq =>
        have hpi : p = i := by
          rw [← hq]
          rfl
        rw [hread, hpi, if_pos rfl]
        rfl
      | q2 + 1, hq =>
        have hpne : ¬ p = i := by
          intro he
          rw [he] at hq
          exact absurd hq (Nat.ne_of_gt
            (Nat.lt_add_of_pos_right (Nat.succ_pos q2)))
        have hread2 : ground.getAt 0 (tieM i g' e) p
            = ground.getAt 0
              (List.replicate g' 1 ++ 0 :: List.replicate e 1)
              q2 := hread
        cases Nat.lt_or_ge q2 g' with
        | inl hq2 =>
          have hv : ground.getAt 0 (tieM i g' e) p = 1 := by
            rw [hread2,
              ground.getAt_append 0 (List.replicate g' 1) _ q2,
              ground.length_replicate, if_pos hq2]
            exact ground.getAt_replicate 0 1 g' q2 hq2
          have hpne2 : ¬ p = i + (g' + 1) := by
            intro he
            rw [he] at hq
            have h1 : q2 + 1 = g' + 1 := ground.addCancelL i hq
            rw [Nat.succ.inj h1] at hq2
            exact absurd hq2 (Nat.lt_irrefl g')
          rw [hv, if_neg hpne, if_neg hpne2]
        | inr hge2 =>
          match Nat.le.dest hge2 with
          | ⟨q3, hq3⟩ =>
            have hread3 : ground.getAt 0 (tieM i g' e) p
                = ground.getAt 0 (0 :: List.replicate e 1) q3 := by
              rw [hread2, ← hq3]
              have h := ground.getAt_append_add 0
                (List.replicate g' 1) (0 :: List.replicate e 1) q3
              rw [ground.length_replicate] at h
              exact h
            match q3, hq3 with
            | 0, hq3 =>
              have hpg : p = i + (g' + 1) := by
                rw [← hq, ← hq3]
              rw [hread3, hpg,
                if_neg (Nat.ne_of_gt
                  (Nat.lt_add_of_pos_right (Nat.succ_pos g'))),
                if_pos rfl]
              rfl
            | q4 + 1, hq3 =>
              have hq4 : q4 < e := by
                have h1 : i + (q2 + 1) < i + (g' + (e + 2)) := by
                  rw [hq]
                  exact hp
                have h2 : q2 + 1 < g' + (e + 2) := by
                  have h3 : i + ((q2 + 1) + 1)
                      ≤ i + (g' + (e + 2)) := by
                    rw [← Nat.add_assoc i (q2 + 1) 1]
                    exact h1
                  exact ground.leCancelL i h3
                have h4 : g' + (q4 + 1) + 1 < g' + (e + 2) := by
                  rw [hq3]
                  exact h2
                have h5 : g' + ((q4 + 1) + (1 + 1))
                    ≤ g' + (e + 2) := by
                  rw [← Nat.add_assoc g' (q4 + 1) (1 + 1),
                    ← Nat.add_assoc (g' + (q4 + 1)) 1 1]
                  exact h4
                have h6 : (q4 + 1) + (1 + 1) ≤ e + 2 :=
                  ground.leCancelL g' h5
                have h7 : q4 + 2 < e + 2 := h6
                exact Nat.lt_of_succ_lt_succ
                  (Nat.lt_of_succ_lt_succ h7)
              have hv : ground.getAt 0 (tieM i g' e) p = 1 := by
                rw [hread3]
                show ground.getAt 0 (List.replicate e 1) q4 = 1
                exact ground.getAt_replicate 0 1 e q4 hq4
              have hpne2 : ¬ p = i + (g' + 1) := by
                intro he
                rw [he] at hq
                have h1 : q2 + 1 = g' + 1 := ground.addCancelL i hq
                have h2 : q2 = g' := Nat.succ.inj h1
                rw [h2] at hq3
                have h3 : q4 + 1 = 0 := by
                  have h4 : g' + (q4 + 1) = g' + 0 := hq3
                  exact ground.addCancelL g' h4
                exact Nat.noConfusion h3
              rw [hv, if_neg hpne, if_neg hpne2]

/-- The tie's core relation at the moved row list: the display
entry joins the moved row back to the source row's successor. -/
private theorem tie_core (d i g' e : Nat) (l m' : List Nat)
    (hde : i + (g' + (e + 2)) = d)
    (hi : ground.getAt 0 m' i + 1 = ground.getAt 0 l i)
    (hg : ground.getAt 0 m' (i + (g' + 1))
      = ground.getAt 0 l (i + (g' + 1)) + 1)
    (hoff : ∀ p, ¬ p = i → ¬ p = i + (g' + 1) →
      ground.getAt 0 m' p = ground.getAt 0 l p) :
    ∀ p, p < d →
      ground.getAt 0 (tieM i g' e) p + ground.getAt 0 m' p
        = ground.getAt 0 l p + 1 := by
  intro p hp
  rw [getAt_tieM i g' e p (by rw [hde]; exact hp)]
  by_cases hpi : p = i
  · rw [if_pos hpi, hpi, ← hi,
      Nat.add_comm 2 (ground.getAt 0 m' i)]
  · rw [if_neg hpi]
    by_cases hpg : p = i + (g' + 1)
    · rw [if_pos hpg, hpg, hg, Nat.zero_add]
    · rw [if_neg hpg, hoff p hpi hpg,
        Nat.add_comm 1 (ground.getAt 0 l p)]

/-- The stencil membership at the tie display: the two-point tie
between matched-width shapes reads the occupied adjoint-row count
through `boxRow`. -/
private theorem boxRow_move (d i g' e : Nat) (mu c : places.Shape)
    (hde : i + (g' + (e + 2)) = d)
    (hmul : mu.length = d) (hcl : c.length = d)
    (hent : ∀ p, p < d →
      ground.getAt 0 (tieM i g' e) p
          + ground.getAt 0 (places.display mu) p
        = ground.getAt 0 (places.display c) p) :
    0 < blockcount.fusionCount mu (adjchar.theta d) c := by
  refine boxRow d mu c (tieM i g' e) hmul hcl ?_ ?_ ?_ ?_ ?_
  · refine ground.tieGap_make (places.display c) (places.display mu)
      (tieM i g' e) ?_ ?_ ?_
    · rw [length_tieM, hde, places.length_display, hcl]
    · rw [places.length_display, places.length_display, hmul, hcl]
    · intro p hpd
      rw [places.length_display, hcl] at hpd
      exact hent p hpd
  · rw [length_tieM, hde]
  · exact countOf0_tieM i g' e
  · exact countOf2_tieM i g' e
  · rw [countOf1_tieM i g' e]
    exact hde

/-- A shape of the stated width splits off its last occupancy. -/
private theorem snoc_last (d : Nat) (x : places.Shape)
    (hd1 : d - 1 + 1 = d) (hxlen : x.length = d) :
    ∃ w, w.length = d - 1
      ∧ x = w ++ [ground.getAt 0 x (d - 1)] := by
  obtain ⟨w, y, hx, hwlen⟩ := ground.snoc_split (d - 1) x
    (by rw [hxlen, hd1])
  have hy : ground.getAt 0 x (d - 1) = y := by
    rw [hx, ← hwlen]
    have h := ground.getAt_append_add 0 w [y] 0
    rw [Nat.add_zero] at h
    exact h
  exact ⟨w, hwlen, by rw [hy]; exact hx⟩

/-- The appended vacant occupancy reads vacant at the seam. -/
private theorem last_snoc_zero (w : List Nat) :
    ground.getAt 0 (w ++ [0]) w.length = 0 := by
  have h := ground.getAt_append_add 0 w [0] 0
  rw [Nat.add_zero] at h
  exact h

/-- The head's labels carry the stated width: the unit is the
vacant word of that width and a below-cutoff label is a
one-shorter shape with its vacant last occupancy appended. -/
private theorem head_len (d K : Nat) (hd : 1 ≤ d)
    (mu : places.Shape)
    (hmuMem : mu ∈ (fusion.dataA d).unit ::
      ((fusion.dataA d).below K).filter
        (fun l => Nat.beq ((fusion.dataA d).cls l) 0)) :
    mu.length = d := by
  cases hmuMem with
  | head =>
    show (List.replicate d (0 : Nat)).length = d
    exact ground.length_replicate 0 d
  | tail _ hm =>
    have hb : mu ∈ (List.range (K + 1)).flatMap
        (fun j => (places.allShapes (d - 1) j).filterMap
          (fun sh => if 0 < j && c2hat.dfQ (sh ++ [0]) ≤ K
            then some (sh ++ [0]) else none)) :=
      (ground.mem_filter_of _ _ mu hm).1
    obtain ⟨j, _, hj⟩ := ground.mem_flatMap_of _ _ mu hb
    obtain ⟨w, hw, hfw⟩ := ground.mem_filterMap_of _ _ mu hj
    by_cases hg : (0 < j && c2hat.dfQ (w ++ [0]) ≤ K) = true
    · rw [if_pos hg] at hfw
      have hmuw : mu = w ++ [0] := (Option.some.inj hfw).symm
      rw [hmuw, ground.length_append,
        (places.allShapes_sound (d - 1) j w hw).1]
      exact ground.subAdd hd
    · rw [if_neg hg] at hfw
      exact nomatch hfw

/-- The frontier membership's assembly: a head label's occupied
adjoint-row read at a matched-degree source lands its reduction
among the frontier's targets when the reduction's Casimir leaves
the cutoff, the definitional read transported to the word list at
`rankstable.adjRow_eq`'s count identity. -/
private theorem frontier_mem (d K : Nat) (s mu c' : places.Shape)
    (hmuMem : mu ∈ (fusion.dataA d).unit ::
      ((fusion.dataA d).below K).filter
        (fun l => Nat.beq ((fusion.dataA d).cls l) 0))
    (hd : 2 ≤ d)
    (hc'len : c'.length = d)
    (hdegc : places.degree c'
      = places.degree mu + places.degree (adjchar.theta d))
    (hstein : 0 < steinberg.count mu (adjchar.theta d) c')
    (hredc : labels.reduce c' = s)
    (hKs : K < c2hat.dfQ s) :
    s ∈ frontierTargets d K := by
  have hmulen : mu.length = d :=
    head_len d K (Nat.le_trans (Nat.le_succ 1) hd) mu hmuMem
  show s ∈ ((fusion.dataA d).unit ::
      ((fusion.dataA d).below K).filter
        (fun l => Nat.beq ((fusion.dataA d).cls l) 0)).flatMap
    (fun l => (rankstable.adjRow d l).filter
      (fun c => decide (K < c2hat.dfQ c)))
  refine ground.mem_flatMap_to _ hmuMem ?_
  refine ground.mem_filter_to _ ?_ (decide_eq_true hKs)
  have hmem : c' ∈ places.allShapes d
      (places.degree mu + places.degree (adjchar.theta d)) := by
    rw [← hdegc]
    exact places.mem_allShapes d c' hc'len
  have himg : (if 0 < steinberg.count mu (adjchar.theta d) c'
      then some (labels.reduce c') else none) = some s := by
    rw [if_pos hstein, hredc]
  have hdef : s ∈ (places.allShapes d
      (places.degree mu + places.degree (adjchar.theta d))).filterMap
    (fun c => if 0 < steinberg.count mu (adjchar.theta d) c
      then some (labels.reduce c) else none) :=
    ground.mem_filterMap_to _ hmem himg
  have hcnt := ground.countOf_pos_of_mem hdef
  rw [rankstable.adjRow_eq d mu hmulen hd s] at hcnt
  exact ground.mem_of_countOf_pos s (rankstable.adjRow d mu) hcnt

/-- The head membership: a reduced occupied unit-class shape at a
Casimir at or below the cutoff sits among the head's labels, its
degree inside the enumeration window
(`prop:windowfinite`'s bound). -/
private theorem head_mem (d K : Nat) (mu : places.Shape)
    (hd : 2 ≤ d) (hmulen : mu.length = d)
    (hmured : ground.getAt 0 mu (d - 1) = 0)
    (hmuocc : 0 < ground.sumNat mu)
    (hmucls : places.degree mu % d = 0)
    (hmuK : c2hat.dfQ mu ≤ K) :
    mu ∈ (fusion.dataA d).unit ::
      ((fusion.dataA d).below K).filter
        (fun l => Nat.beq ((fusion.dataA d).cls l) 0) := by
  have hd1 : d - 1 + 1 = d :=
    ground.subAdd (Nat.le_trans (Nat.le_succ 1) hd)
  refine List.Mem.tail _ (ground.mem_filter_to _ ?_ ?_)
  · obtain ⟨w, hwlen, hmu⟩ := snoc_last d mu hd1 hmulen
    rw [hmured] at hmu
    have hdegmu : places.degree mu = places.degree w := by
      rw [hmu, places.degree_snoc w 0, Nat.zero_mul, Nat.add_zero]
    have hjK : places.degree w < K + 1 := by
      refine Nat.lt_succ_of_le ?_
      rw [← hdegmu]
      exact Nat.le_trans
        (Nat.le_trans
          (Nat.le_mul_of_pos_left (places.degree mu)
            (by rw [hmulen]
                exact Nat.lt_of_lt_of_le Nat.zero_lt_two hd))
          (windowfinite.degree_le_dfQ mu (d - 1)
            (by rw [hmulen, hd1]) hmured))
        hmuK
    have hjmem : places.degree w ∈ List.range (K + 1) := by
      have h1 := ground.mem_getAt 0 (List.range (K + 1))
        (places.degree w)
        (by rw [ground.length_range]; exact hjK)
      rw [ground.getAt_range (K + 1) (places.degree w) hjK] at h1
      exact h1
    show mu ∈ (List.range (K + 1)).flatMap
      (fun j => (places.allShapes (d - 1) j).filterMap
        (fun sh => if 0 < j && c2hat.dfQ (sh ++ [0]) ≤ K
          then some (sh ++ [0]) else none))
    refine ground.mem_flatMap_to _ hjmem ?_
    refine ground.mem_filterMap_to _
      (places.mem_allShapes (d - 1) w hwlen) ?_
    have hocc' : 0 < places.degree w := by
      rw [← hdegmu]
      exact Nat.lt_of_lt_of_le hmuocc (sumNat_le_degree mu)
    have hdk : c2hat.dfQ (w ++ [0]) ≤ K := by
      rw [← hmu]
      exact hmuK
    have hguard : (0 < places.degree w
        && c2hat.dfQ (w ++ [0]) ≤ K) = true := by
      rw [decide_eq_true hocc', decide_eq_true hdk]
      rfl
    rw [if_pos hguard, hmu]
  · show Nat.beq (places.degree mu % d) 0 = true
    rw [hmucls]
    rfl

/-- The fold's transport along a raised bound: a member at or
below the smaller read stays at or below the larger. -/
private theorem any_le_trans (L : List places.Shape) (a b : Nat)
    (hab : a ≤ b) :
    L.any (fun c => decide (c2hat.dfQ c ≤ a)) = true →
    L.any (fun c => decide (c2hat.dfQ c ≤ b)) = true := by
  induction L with
  | nil => intro h; exact Bool.noConfusion h
  | cons z t ih =>
    intro h
    show (decide (c2hat.dfQ z ≤ b)
      || t.any (fun c => decide (c2hat.dfQ c ≤ b))) = true
    have h' : (decide (c2hat.dfQ z ≤ a)
        || t.any (fun c => decide (c2hat.dfQ c ≤ a))) = true := h
    cases hz : decide (c2hat.dfQ z ≤ a) with
    | true =>
      rw [decide_eq_true
        (Nat.le_trans (of_decide_eq_true hz) hab)]
      rfl
    | false =>
      rw [hz] at h'
      have ht : t.any (fun c => decide (c2hat.dfQ c ≤ a))
          = true := h'
      rw [ih ht]
      cases decide (c2hat.dfQ z ≤ b) <;> rfl

/-- The reduction keeps the unit class: the withdrawn full column
moves the degree by the width. -/
private theorem reduce_cls (d : Nat) (t w2 : places.Shape)
    (hd1 : d - 1 + 1 = d) (hw2len : w2.length = d - 1)
    (ht2 : t = w2 ++ [1])
    (hclst : places.degree t % d = 0) :
    places.degree (w2 ++ [0]) % d = 0 := by
  have hdg1 : places.degree t = places.degree w2 + d := by
    rw [ht2, places.degree_snoc w2 1, Nat.one_mul, hw2len, hd1]
  have hdg2 : places.degree (w2 ++ [0]) = places.degree w2 := by
    rw [places.degree_snoc w2 0, Nat.zero_mul, Nat.add_zero]
  have h := ground.modAddMul (places.degree w2) 1 d
  rw [Nat.one_mul] at h
  rw [hdg2, ← h, ← hdg1]
  exact hclst

/-- The plain arm's landing: a moved shape kept reduced at a
Casimir at or below the cutoff is a head label, and the source
shape reaches its adjoint row through the raised full column. -/
private theorem step_plain (d K i g' e : Nat) (s t : places.Shape)
    (hlen : s.length = d)
    (hred : ground.getAt 0 s (d - 1) = 0)
    (hK : K < c2hat.dfQ s) (hcls : places.degree s % d = 0)
    (hde : i + (g' + (e + 2)) = d)
    (htlen : t.length = d)
    (hti : ground.getAt 0 (places.rowList t) i + 1
      = ground.getAt 0 (places.rowList s) i)
    (htg : ground.getAt 0 (places.rowList t) (i + (g' + 1))
      = ground.getAt 0 (places.rowList s) (i + (g' + 1)) + 1)
    (htoff : ∀ p, ¬ p = i → ¬ p = i + (g' + 1) →
      ground.getAt 0 (places.rowList t) p
        = ground.getAt 0 (places.rowList s) p)
    (htred : ground.getAt 0 t (d - 1) = 0)
    (htocc : 0 < ground.sumNat t)
    (hdegt : places.degree t = places.degree s)
    (htK : c2hat.dfQ t ≤ K) :
    s ∈ frontierTargets d K := by
  have hd : 2 ≤ d := by
    rw [← hde]
    exact Nat.le_trans (Nat.le_add_left 2 e)
      (Nat.le_trans (Nat.le_add_left (e + 2) g')
        (Nat.le_add_left (g' + (e + 2)) i))
  have hd1 : d - 1 + 1 = d :=
    ground.subAdd (Nat.le_trans (Nat.le_succ 1) hd)
  have hmuMem := head_mem d K t hd htlen htred htocc
    (by rw [hdegt]; exact hcls) htK
  obtain ⟨w, hwlen, hs2⟩ := snoc_last d s hd1 hlen
  rw [hred] at hs2
  have hbump : ground.bumpAt (d - 1) s = w ++ [1] := by
    rw [hs2, ← hwlen]
    exact ground.bumpAt_snoc w 0
  have hc'len : (ground.bumpAt (d - 1) s).length = d := by
    rw [ground.length_bumpAt]
    exact hlen
  have hredc : labels.reduce (ground.bumpAt (d - 1) s) = s := by
    rw [hbump, labels.reduce_snoc w 1, ← hs2]
  have hdegc : places.degree (ground.bumpAt (d - 1) s)
      = places.degree t + places.degree (adjchar.theta d) := by
    rw [places.degree_bumpAt (d - 1) s
        (by rw [hlen, ← hd1]; exact Nat.lt_succ_self (d - 1)),
      hd1, hdegt, adjchar.degree_theta d hd]
  have hdf := places.display_full s
  rw [hlen] at hdf
  have hstein : 0 < steinberg.count t (adjchar.theta d)
      (ground.bumpAt (d - 1) s) := by
    rw [steinberg.count_fusion t (adjchar.theta d)
      (ground.bumpAt (d - 1) s)
      (by rw [adjchar.length_theta]; exact htlen.symm)
      (by rw [hc'len]; exact htlen.symm)]
    refine boxRow_move d i g' e t (ground.bumpAt (d - 1) s)
      hde htlen hc'len ?_
    intro p hp
    have hXc : ground.getAt 0
        (places.display (ground.bumpAt (d - 1) s)) p
        = ground.getAt 0 (places.display s) p + 1 := by
      rw [hdf]
      exact ground.getAt_map 0 0 (fun x => x + 1)
        (places.display s) p
        (by rw [places.length_display, hlen]; exact hp)
    have hXt := places.getAt_display t p
      (by rw [htlen]; exact hp)
    rw [htlen] at hXt
    have hXs := places.getAt_display s p
      (by rw [hlen]; exact hp)
    rw [hlen] at hXs
    have hcore := tie_core d i g' e (places.rowList s)
      (places.rowList t) hde hti htg htoff p hp
    rw [hXc, hXt, hXs,
      ← Nat.add_assoc (ground.getAt 0 (tieM i g' e) p)
        (ground.getAt 0 (places.rowList t) p) (d - p),
      hcore,
      Nat.add_assoc (ground.getAt 0 (places.rowList s) p) 1 (d - p),
      Nat.add_comm 1 (d - p),
      ← Nat.add_assoc (ground.getAt 0 (places.rowList s) p)
        (d - p) 1]
  exact frontier_mem d K s t (ground.bumpAt (d - 1) s)
    hmuMem hd hc'len hdegc hstein hredc hK

/-- The exit arm's landing: the move raising the last row fills a
column, the reduction is the head label, and the source shape is
its adjoint row's own target. -/
private theorem step_exit (d K i g' e : Nat) (s t : places.Shape)
    (hlen : s.length = d)
    (hred : ground.getAt 0 s (d - 1) = 0)
    (hK : K < c2hat.dfQ s) (hcls : places.degree s % d = 0)
    (hde : i + (g' + (e + 2)) = d)
    (htlen : t.length = d)
    (hti : ground.getAt 0 (places.rowList t) i + 1
      = ground.getAt 0 (places.rowList s) i)
    (htg : ground.getAt 0 (places.rowList t) (i + (g' + 1))
      = ground.getAt 0 (places.rowList s) (i + (g' + 1)) + 1)
    (htoff : ∀ p, ¬ p = i → ¬ p = i + (g' + 1) →
      ground.getAt 0 (places.rowList t) p
        = ground.getAt 0 (places.rowList s) p)
    (htlast1 : ground.getAt 0 t (d - 1) = 1)
    (hdegt : places.degree t = places.degree s)
    (htK : c2hat.dfQ t ≤ K) :
    s ∈ frontierTargets d K := by
  have hd : 2 ≤ d := by
    rw [← hde]
    exact Nat.le_trans (Nat.le_add_left 2 e)
      (Nat.le_trans (Nat.le_add_left (e + 2) g')
        (Nat.le_add_left (g' + (e + 2)) i))
  have hd1 : d - 1 + 1 = d :=
    ground.subAdd (Nat.le_trans (Nat.le_succ 1) hd)
  obtain ⟨w2, hw2len, ht2⟩ := snoc_last d t hd1 htlen
  rw [htlast1] at ht2
  have hredt : labels.reduce t = w2 ++ [0] := by
    rw [ht2]
    exact labels.reduce_snoc w2 1
  have hmulen : (w2 ++ [0]).length = d := by
    rw [ground.length_append, hw2len]
    exact hd1
  have hmured : ground.getAt 0 (w2 ++ [0]) (d - 1) = 0 := by
    rw [← hw2len]
    exact last_snoc_zero w2
  have hcc : c2hat.dfQ t = c2hat.dfQ (labels.reduce t) :=
    labels.c2Class_all t
  rw [hredt] at hcc
  have hmucls : places.degree (w2 ++ [0]) % d = 0 :=
    reduce_cls d t w2 hd1 hw2len ht2
      (by rw [hdegt]; exact hcls)
  have hmuMem : (w2 ++ [0]) ∈ (fusion.dataA d).unit ::
      ((fusion.dataA d).below K).filter
        (fun l => Nat.beq ((fusion.dataA d).cls l) 0) := by
    match hsm : ground.sumNat (w2 ++ [0]) with
    | 0 =>
      have hz : w2 ++ [0] = List.replicate d 0 := by
        have h := ground.replicate_of_sum_zero (w2 ++ [0]) hsm
        rw [hmulen] at h
        exact h
      rw [hz]
      exact List.Mem.head _
    | n2 + 1 =>
      refine head_mem d K (w2 ++ [0]) hd hmulen hmured
        (by rw [hsm]; exact Nat.succ_pos n2) hmucls ?_
      rw [← hcc]
      exact htK
  have hlen1 : (w2 ++ [0]).length - 1 = d - 1 := by rw [hmulen]
  have hbump2 : ground.bumpAt (d - 1) (w2 ++ [0]) = w2 ++ [1] := by
    rw [← hw2len]
    exact ground.bumpAt_snoc w2 0
  have hrf := places.rowList_full (w2 ++ [0])
  rw [hlen1, hbump2, ← ht2] at hrf
  have hmap : ∀ p, p < d →
      ground.getAt 0 (places.rowList t) p
        = ground.getAt 0 (places.rowList (w2 ++ [0])) p + 1 := by
    intro p hp
    rw [hrf]
    exact ground.getAt_map 0 0 (fun x => x + 1)
      (places.rowList (w2 ++ [0])) p
      (by rw [places.length_rowList, hmulen]; exact hp)
  have hstein : 0 < steinberg.count (w2 ++ [0])
      (adjchar.theta d) s := by
    rw [steinberg.count_fusion (w2 ++ [0]) (adjchar.theta d) s
      (by rw [adjchar.length_theta]; exact hmulen.symm)
      (by rw [hlen]; exact hmulen.symm)]
    refine boxRow_move d i g' e (w2 ++ [0]) s hde hmulen
      hlen ?_
    intro p hp
    have hXm := places.getAt_display (w2 ++ [0]) p
      (by rw [hmulen]; exact hp)
    rw [hmulen] at hXm
    have hXs := places.getAt_display s p
      (by rw [hlen]; exact hp)
    rw [hlen] at hXs
    have hcore := tie_core d i g' e (places.rowList s)
      (places.rowList t) hde hti htg htoff p hp
    rw [hmap p hp] at hcore
    have hcore2 : ground.getAt 0 (tieM i g' e) p
        + ground.getAt 0 (places.rowList (w2 ++ [0])) p
        = ground.getAt 0 (places.rowList s) p := by
      refine ground.addCancelR 1 ?_
      rw [Nat.add_assoc (ground.getAt 0 (tieM i g' e) p)
        (ground.getAt 0 (places.rowList (w2 ++ [0])) p) 1]
      exact hcore
    rw [hXm, hXs,
      ← Nat.add_assoc (ground.getAt 0 (tieM i g' e) p)
        (ground.getAt 0 (places.rowList (w2 ++ [0])) p) (d - p),
      hcore2]
  have hdg1 : places.degree t = places.degree w2 + d := by
    rw [ht2, places.degree_snoc w2 1, Nat.one_mul, hw2len, hd1]
  have hdg2 : places.degree (w2 ++ [0]) = places.degree w2 := by
    rw [places.degree_snoc w2 0, Nat.zero_mul, Nat.add_zero]
  have hdegc : places.degree s
      = places.degree (w2 ++ [0])
        + places.degree (adjchar.theta d) := by
    rw [hdg2, adjchar.degree_theta d hd, ← hdegt, hdg1]
  obtain ⟨w, hwlen, hs2⟩ := snoc_last d s hd1 hlen
  rw [hred] at hs2
  have hredc : labels.reduce s = s := by
    rw [hs2, labels.reduce_snoc w 0]
  exact frontier_mem d K s (w2 ++ [0]) s hmuMem hd hlen hdegc
    hstein hredc hK

/-- The frontier walk: an excluded unit-class label descends by
`lem:casfloor`'s moves, one per fuel step, to a frontier target at
or below its own cleared Casimir. -/
private theorem excludedFloorGo :
    ∀ (n d K : Nat) (s : places.Shape),
    2 ≤ d → s.length = d →
    ground.getAt 0 s (d - 1) = 0 →
    0 < ground.sumNat s → places.degree s % d = 0 →
    K < c2hat.dfQ s → c2hat.dfQ s ≤ n →
    ((frontierTargets d K).any
      (fun c => decide (c2hat.dfQ c ≤ c2hat.dfQ s))) = true
  | 0, _, K, _, _, _, _, _, _, hK, hn =>
    absurd (Nat.lt_of_lt_of_le hK hn) (Nat.not_lt_zero K)
  | n + 1, d, K, s, hd, hlen, hred, hocc, hcls, hK, hfuel => by
    have hd1 : d - 1 + 1 = d :=
      ground.subAdd (Nat.le_trans (Nat.le_succ 1) hd)
    have hlen' : s.length = d - 1 + 1 := by rw [hlen, hd1]
    have hlr : (places.rowList s).length = d - 1 + 1 := by
      rw [places.length_rowList]
      exact hlen'
    have hldesc : ∀ p, p + 1 < (places.rowList s).length →
        ground.getAt 0 (places.rowList s) (p + 1)
          ≤ ground.getAt 0 (places.rowList s) p :=
      fun p hp => places.rowList_le s p
        (by rw [← places.length_rowList]; exact hp)
    have hll : ground.getAt 0 (places.rowList s) (d - 1) = 0 := by
      rw [places.rowList_last s (d - 1) hlen']
      exact hred
    have hdegs : 0 < places.degree s :=
      Nat.lt_of_lt_of_le hocc (sumNat_le_degree s)
    have hdd : d ≤ places.degree s := d_le_of_mod d _ hdegs hcls
    obtain ⟨k, hk, hk2⟩ := exists_two_red (places.rowList s)
      (d - 1) (by rw [hlr]; exact Nat.lt_succ_self _) hll
      (by rw [hlr, hd1]; exact hdd)
    obtain ⟨i, g, hg0, hig, h2i, hmlen, hmdesc, hi, hgread, hoff⟩ :=
      casfloor.boxMove (d - 1) (places.rowList s) hlr hldesc hll
        k hk hk2
    obtain ⟨g', rfl⟩ : ∃ g'', g = g'' + 1 :=
      ⟨g - 1, (Nat.succ_pred_eq_of_pos hg0).symm⟩
    obtain ⟨e, he⟩ := Nat.le.dest hig
    have hde : i + (g' + (e + 2)) = d := by
      rw [← tie_arith i g' e, ← hd1, ← he]
    have hrt : places.rowList (places.shapeOf
        (ground.bumpAt (i + (g' + 1))
          (ground.dipAt i (places.rowList s))))
        = ground.bumpAt (i + (g' + 1))
          (ground.dipAt i (places.rowList s)) :=
      places.rowList_shapeOf _ hmdesc
    rw [← hrt] at hi hgread hoff hmdesc
    have htlen : (places.shapeOf (ground.bumpAt (i + (g' + 1))
        (ground.dipAt i (places.rowList s)))).length = d := by
      rw [places.length_shapeOf, hmlen, places.length_rowList,
        hlen]
    have htlen' : (places.shapeOf (ground.bumpAt (i + (g' + 1))
        (ground.dipAt i (places.rowList s)))).length
        = d - 1 + 1 := by
      rw [htlen, hd1]
    have hfall : c2hat.dfQ (places.shapeOf (ground.bumpAt
        (i + (g' + 1)) (ground.dipAt i (places.rowList s))))
        < c2hat.dfQ s :=
      casfloor.fallStrict s _ i (g' + 1)
        (htlen.trans hlen.symm) hi hgread
        (fun p _ hpi hpg => hoff p hpi hpg)
    have hb1 : i + (g' + 1)
        < (ground.dipAt i (places.rowList s)).length := by
      rw [ground.length_dipAt, hlr]
      exact Nat.lt_succ_of_le hig
    have hpos : 0 < ground.getAt 0 (places.rowList s) i :=
      Nat.lt_of_lt_of_le Nat.zero_lt_two h2i
    have hsum : ground.sumNat (ground.bumpAt (i + (g' + 1))
        (ground.dipAt i (places.rowList s)))
        = ground.sumNat (places.rowList s) := by
      rw [ground.sumNat_bumpAt (i + (g' + 1))
        (ground.dipAt i (places.rowList s)) hb1]
      exact ground.sumNat_dipAt i (places.rowList s) hpos
    have hdegt : places.degree (places.shapeOf (ground.bumpAt
        (i + (g' + 1)) (ground.dipAt i (places.rowList s))))
        = places.degree s := by
      show ground.sumNat (places.rowList (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s)))))
        = ground.sumNat (places.rowList s)
      rw [hrt]
      exact hsum
    have hoccT : 0 < ground.sumNat (places.shapeOf
        (ground.bumpAt (i + (g' + 1))
          (ground.dipAt i (places.rowList s)))) := by
      have h1 : 0 < ground.getAt 0 (places.rowList
          (places.shapeOf (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s)))))
          (i + (g' + 1)) := by
        rw [hgread]
        exact Nat.succ_pos _
      have h2 := desc_ge (places.rowList (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s))))) hmdesc
        (i + (g' + 1))
        (by rw [places.length_rowList, htlen]
            exact Nat.lt_of_le_of_lt hig
              (by rw [← hd1]; exact Nat.lt_succ_self (d - 1)))
      have h3 := places.rowList_head (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s))))
        (by rw [htlen]
            exact Nat.lt_of_lt_of_le Nat.zero_lt_two hd)
      rw [← h3]
      exact Nat.lt_of_lt_of_le h1 h2
    have hlastT : ground.getAt 0 (places.rowList
        (places.shapeOf (ground.bumpAt (i + (g' + 1))
          (ground.dipAt i (places.rowList s))))) (d - 1)
        = ground.getAt 0 (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s)))) (d - 1) :=
      places.rowList_last _ (d - 1) htlen'
    cases Nat.lt_or_ge (i + (g' + 1)) (d - 1) with
    | inl hlt =>
      have hne1 : ¬ d - 1 = i := by
        intro heq
        rw [← heq] at h2i
        rw [hll] at h2i
        exact absurd h2i (Nat.not_succ_le_zero 1)
      have hne2 : ¬ d - 1 = i + (g' + 1) := by
        intro heq
        rw [heq] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
      have htred : ground.getAt 0 (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s)))) (d - 1) = 0 := by
        rw [← hlastT, hoff (d - 1) hne1 hne2]
        exact hll
      cases Nat.lt_or_ge K (c2hat.dfQ (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s))))) with
      | inl hKt =>
        have hrec := excludedFloorGo n d K
          (places.shapeOf (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s))))
          hd htlen htred hoccT
          (by rw [hdegt]; exact hcls) hKt
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hfall hfuel))
        exact any_le_trans (frontierTargets d K) _ _
          (Nat.le_of_lt hfall) hrec
      | inr hKt =>
        exact ground.any_of_mem _
          (step_plain d K i g' e s
            (places.shapeOf (ground.bumpAt (i + (g' + 1))
              (ground.dipAt i (places.rowList s))))
            hlen hred hK hcls hde htlen hi hgread hoff
            htred hoccT hdegt hKt)
          (decide_eq_true (Nat.le_refl _))
    | inr hge =>
      have heq : i + (g' + 1) = d - 1 := Nat.le_antisymm hig hge
      have htlast1 : ground.getAt 0 (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s)))) (d - 1)
          = 1 := by
        rw [← hlastT, ← heq, hgread, heq, hll]
      have hcc : c2hat.dfQ (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s))))
          = c2hat.dfQ (labels.reduce (places.shapeOf
            (ground.bumpAt (i + (g' + 1))
              (ground.dipAt i (places.rowList s))))) :=
        labels.c2Class_all _
      cases Nat.lt_or_ge K (c2hat.dfQ (places.shapeOf
          (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s))))) with
      | inl hKt =>
        obtain ⟨w2, hw2len, ht2⟩ := snoc_last d
          (places.shapeOf (ground.bumpAt (i + (g' + 1))
            (ground.dipAt i (places.rowList s)))) hd1 htlen
        rw [htlast1] at ht2
        have hredt : labels.reduce (places.shapeOf
            (ground.bumpAt (i + (g' + 1))
              (ground.dipAt i (places.rowList s))))
            = w2 ++ [0] := by
          rw [ht2]
          exact labels.reduce_snoc w2 1
        rw [hredt] at hcc
        have hlenw : (w2 ++ [0]).length = d := by
          rw [ground.length_append, hw2len]
          exact hd1
        match hsm : ground.sumNat (w2 ++ [0]) with
        | 0 =>
          have hz : w2 ++ [0] = List.replicate d 0 := by
            have h := ground.replicate_of_sum_zero (w2 ++ [0]) hsm
            rw [hlenw] at h
            exact h
          have hdfz : c2hat.dfQ (places.shapeOf
              (ground.bumpAt (i + (g' + 1))
                (ground.dipAt i (places.rowList s)))) = 0 := by
            rw [hcc, hz]
            exact c2hat.dfQ_replicate_zero d
          rw [hdfz] at hKt
          exact absurd hKt (Nat.not_lt_zero K)
        | n2 + 1 =>
          have hmured : ground.getAt 0 (w2 ++ [0]) (d - 1)
              = 0 := by
            rw [← hw2len]
            exact last_snoc_zero w2
          have hclsw : places.degree (w2 ++ [0]) % d = 0 :=
            reduce_cls d (places.shapeOf
              (ground.bumpAt (i + (g' + 1))
                (ground.dipAt i (places.rowList s)))) w2
              hd1 hw2len ht2 (by rw [hdegt]; exact hcls)
          have hrec := excludedFloorGo n d K (w2 ++ [0]) hd
            hlenw hmured (by rw [hsm]; exact Nat.succ_pos n2)
            hclsw (by rw [← hcc]; exact hKt)
            (by rw [← hcc]
                exact Nat.le_of_lt_succ
                  (Nat.lt_of_lt_of_le hfall hfuel))
          exact any_le_trans (frontierTargets d K) _ _
            (by rw [← hcc]; exact Nat.le_of_lt hfall) hrec
      | inr hKt =>
        exact ground.any_of_mem _
          (step_exit d K i g' e s
            (places.shapeOf (ground.bumpAt (i + (g' + 1))
              (ground.dipAt i (places.rowList s))))
            hlen hred hK hcls hde htlen hi hgread hoff
            htlast1 hdegt hKt)
          (decide_eq_true (Nat.le_refl _))

/-- `lem:contactcell`'s frontier landing: an excluded label — a
reduced occupied unit-class shape whose cleared Casimir leaves the
cutoff — descends by `lem:casfloor`'s moves through occupied
adjoint-row reads to a frontier target at or below its own read,
the walk's landing the lemma's "a minimal excluded label sits in
the head, a frontier target's source". -/
theorem excludedFloor (d K : Nat) (s : places.Shape) (hd : 2 ≤ d)
    (hlen : s.length = d)
    (hred : ground.getAt 0 s (d - 1) = 0)
    (hcls : places.degree s % d = 0)
    (hK : K < c2hat.dfQ s) :
    ((frontierTargets d K).any
      (fun c => decide (c2hat.dfQ c ≤ c2hat.dfQ s))) = true := by
  refine excludedFloorGo (c2hat.dfQ s) d K s hd hlen hred ?_
    hcls hK (Nat.le_refl _)
  match hsm : ground.sumNat s with
  | 0 =>
    have hz : s = List.replicate d 0 := by
      have h := ground.replicate_of_sum_zero s hsm
      rw [hlen] at h
      exact h
    rw [hz, c2hat.dfQ_replicate_zero d] at hK
    exact absurd hK (Nat.not_lt_zero K)
  | n + 1 => exact Nat.succ_pos n

/-- The min fold sits at or below its seed. -/
private theorem foldMin_le_init : ∀ (tl : List places.Shape) (a : Nat),
    tl.foldl (fun b c => ground.natMin b (c2hat.dfQ c)) a ≤ a
  | [], a => Nat.le_refl a
  | _ :: tl, a =>
    Nat.le_trans (foldMin_le_init tl _) (ground.natMin_le_left a _)

/-- The min fold sits at or below every member's read. -/
private theorem foldMin_le_mem : ∀ (tl : List places.Shape) (a : Nat)
    (x : places.Shape), x ∈ tl →
    tl.foldl (fun b c => ground.natMin b (c2hat.dfQ c)) a
      ≤ c2hat.dfQ x
  | [], _, _, h => nomatch h
  | _ :: tl, a, x, h => by
    cases h with
    | head =>
      exact Nat.le_trans (foldMin_le_init tl _)
        (ground.natMin_le_right a _)
    | tail _ hm => exact foldMin_le_mem tl _ x hm

/-- `lem:contactcell`'s seed floor: `c₊` sits at or below the whole
excluded block, every excluded label's cleared Casimir at or beyond
the frontier's least — the walk's landing read at the min fold. -/
theorem cPlus_floors (d K : Nat) (s : places.Shape) (hd : 2 ≤ d)
    (hlen : s.length = d)
    (hred : ground.getAt 0 s (d - 1) = 0)
    (hcls : places.degree s % d = 0)
    (hK : K < c2hat.dfQ s) :
    cPlusN d K ≤ c2hat.dfQ s := by
  obtain ⟨c, hcmem, hcle⟩ := ground.mem_of_any _ (frontierTargets d K)
    (excludedFloor d K s hd hlen hred hcls hK)
  refine Nat.le_trans ?_ (of_decide_eq_true hcle)
  cases hft : frontierTargets d K with
  | nil =>
    rw [hft] at hcmem
    exact nomatch hcmem
  | cons h tl =>
    rw [hft] at hcmem
    show (match frontierTargets d K with
      | [] => 0
      | h :: tl =>
        tl.foldl (fun a c => ground.natMin a (c2hat.dfQ c))
          (c2hat.dfQ h)) ≤ c2hat.dfQ c
    rw [hft]
    cases hcmem with
    | head => exact foldMin_le_init tl _
    | tail _ hm => exact foldMin_le_mem tl _ c hm

/-- The dual pencil's cell carrier over the coupling coordinate: at a
stated electric matrix, magnetic matrix and level pair, the
polynomial-entried site datum in `σ` — the level datum's magnetic
partner at the constant key and the electric member at the linear
key, `lem:contactcell`'s affine list, the pair `(σE : M)`'s site
datum `P(σ)`. -/
def dualPMat (E M G : Mat) (x y : Pos) : split.PMat :=
  cellcount.levelPMat (elim.matSwap M) E G x y []

/-- The contact end's own read at the cell's carrier: at the
coupling's unit point the cleared evaluation of the dual cell keeps
the constant key alone at the clearing's stated power, so the
cell's matrix there is the magnetic member's balance partner at the
level datum, rescaled by that power — the contact end's pencil its
magnetic member alone with the reads the fusion matrix's own
(`lem:contactcell`; `lem:cellcount`'s `evalPC`). -/
theorem endEval (E M G : Mat) (x y c : Pos) (o : Nat)
    (hE : sqAt E o) (hM : sqAt M o) (hG : sqAt G o) :
    elim.matOneValue
      (cellcount.evalPC (dualPMat E M G x y) BPair.unit c 1)
      (inertia.matScaleB (ground.bpow (BPair.ofPos c) 1)
        (inertia.siteDatum
          (elim.matAdd (elim.matSwap M) (inertia.matScale y G))
          (inertia.matScale x G))) :=
  cellcount.levelPMat_endEval (elim.matSwap M) E G x y c [] o
    (elim.sqAt_matSwap o M hM) hE hG

end contactcell
