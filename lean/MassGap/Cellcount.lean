import MassGap.Stagesplit
import MassGap.Split
/-!
`lem:cellcount` — the count is a cell function.  The pencil along a
segment enters as a polynomial-entried symmetric site datum
(`split.PMat`), its shape read the stated order with every entry's
degree within the stated clearing power (`pShapeAt`); a stage point
enters at composite coordinates `[ln : c]` and the evaluation
clears at the shared power, `Σ_k p_k ln^k c^(K-k)`, a positive
rescaling fixing every count (`poly.evalClear` at `evalPC`).  The
pointwise count is the reversal count at the cleared evaluation
(`countAt` at `lem:inertia`'s splits).  The divisor is the site
datum's determinant (`split.pminor`), and its certificate is the
squarefree witness: the squarefree part with its gcd and Bézout
data (`DivCert`, `divRead`, `lem:stagesplit`'s read).  The
avoidance's certificate is the pivot cover (`Cover`, `coverRead`):
finitely many subintervals chained at shared endpoints, each with a
designated principal minor of order at most two whose determinant
keeps its side along the subinterval at the priced side read
(`lem:stage`'s `keepUpper`/`keepLower`) at a bound containing the
subinterval, at order two its leading entry so as well where the
determinant sits on its upper side, and beneath it the cleared
deflation's own cover — the determinant's root-freeness the cover's
read, the chain's end tying the endpoints (`pieceRead` the one
piece's frame, the designated places inside the order and
pairwise distinct with the places' permutation entering the leading
position at its decided products).  The constancy theorem
`cover_const` reads one integer at every point of the segment at the
pencil's shape and symmetry reads, hence one per
piecewise-linearly connected cell: order one is the priced side read, at order `N` `lem:inertia`
adds at the designated pivot (`inertia.rev_places`), the pivot's
count is the block
table's at the kept sides, the cleared deflation's count is its own
cover's, and the overlaps chain the subintervals, a boundary point
entering as its own split.  The boundary clause is
`boundary_psd_lo`/`boundary_psd_hi`: at a stage point of the locus
adjacent to a cell whose pair is positive semidefinite the point
reads positive semidefinite at its own split, every lower witness
of the point's split carrying its quadratic-form polynomial
(`quadP`, the pencil read against the direction both sides, its
cleared evaluation the evaluated pencil's own quadratic form at
`evalClear_quadP`) on its lower side across the segment into the
cell (`stage.keepLower` at the boundary endpoint, `keepLowerTop`
at the other), against the cell's count.
The recorded consumers are `thm:decimation`'s emitted complex,
`thm:divisorid`(iii), `thm:gappos`, `lem:contactcell` and
`lem:freecell`'s cells, and `lem:corner`'s base, the reads here
their displays.
`lem:inertia`'s deflation lands at the same carrier, one family at
the entry bundle (`inertia.deflPO`, `def:poly`'s reads over the
polynomials as the entry carrier in turn): the deflation cleared
once at a designated pivot of every order is `lem:inertia`'s
deflation at the pivot's determinant against the polynomial
adjugate's solved witness (`pdeflW` the witness, `pdeflP` the
deflation, `split.padj` the adjugate), its shape at the clearing
`(k + 1) K` (`pShape_pdeflP`), its evaluation the evaluated blocks'
once-cleared deflation at the evaluated witness (`evalPC_pdeflP`)
with the witness's solve read (`pdeflW_solve`, `def:elim`'s
adjugate identity at the stage point through `evalPC_pdiag_repl`)
and the evaluated head symmetric where the pivot's determinant sits
off the unit (`evalPC_pdeflP_symm`); at a pivot whose determinant
keeps its lower side, or at the mixed block, the deflation cleared
once at the determinant's magnitude is that deflation's memberwise
swap (`pdeflM`, `evalPC_pdeflM`, `evalPC_pdeflM_symm`), the
positive factor fixing every count; and the order-one deflation at
value-unit couplings reads the pivot entry on the trailing block
outright (`pdeflP_offC`, `pdeflM_offC` at the entry's swap).  The
cover's constancy holds at a pencil symmetric at every point of the
segment (`cellCountP`), the evaluated head's own form, the pivot
cover reading the once-cleared deflation beneath a piece whose
determinant keeps its upper side, its memberwise swap beneath a
lower or mixed piece, and the trailing block itself beneath a pivot
whose coupling to the trailing places reads the sum's unit
(`Cover.diag`). -/

namespace cellcount
open ground poly elim inertia

/-- The pencil's shape read: square at the stated order with every
entry's degree within the stated clearing power. -/
def pShapeAt (S : split.PMat) (o K : Nat) : Prop :=
  elim.shapeAtO (fun p => Nat.ble p.length (K + 1)) S o

instance instCellcount1 (S : split.PMat) (o K : Nat) : Decidable (pShapeAt S o K) :=
  inferInstanceAs (Decidable (elim.shapeAtO _ _ _))

/-- The shape read assembled from its three conjunct reads: the
order at the length, the rows at the width, and every entry's
degree within the clearing power. -/
theorem pShapeAt_of {S : split.PMat} {o K : Nat}
    (hlen : S.length = o) (hrows : elim.rowsLen o S)
    (hble : (S.all (fun r => r.all
      (fun p => Nat.ble p.length (K + 1)))) = true) :
    pShapeAt S o K :=
  elim.shapeAtO_of _ hlen hrows hble

/-- The pencil at a stage point, the cleared evaluations
entrywise (`poly.evalClear`, the composite-point Horner). -/
def evalPC (S : split.PMat) (ln : BPair) (c : Pos) (K : Nat) : Mat :=
  S.map (fun r => r.map (fun p => poly.evalClear p ln c K))

/-- One row's cleared evaluation at the sum's unit point: each
entry keeps its constant key alone at the clearing's stated power
(`poly.evalClear_unit` entrywise). -/
private theorem row_unit (c : Pos) (K : Nat) : ∀ r : List Poly,
    poly.oneValue
      (r.map (fun p => poly.evalClear p BPair.unit c K))
      (poly.scaleP (ground.bpow (BPair.ofPos c) K)
        (r.map (fun p => ground.getAt BPair.unit p 0)))
  | [] => trivial
  | p :: r =>
    ⟨BPair.oneValue_trans (poly.evalClear_unit p c K)
      (BPair.oneValue_symm (BPair.norm_oneValue _)),
     row_unit c K r⟩

/-- The cleared evaluation at the sum's unit point, the matrix
read: the evaluated matrix is the entries' head matrix rescaled by
the clearing's stated power (`poly.evalClear_unit`). -/
theorem evalPC_unit (c : Pos) (K : Nat) : ∀ S : split.PMat,
    elim.matOneValue (evalPC S BPair.unit c K)
      (inertia.matScaleB (ground.bpow (BPair.ofPos c) K)
        (S.map (fun r => r.map
          (fun p => ground.getAt BPair.unit p 0))))
  | [] => trivial
  | r :: S => ⟨row_unit c K r, evalPC_unit c K S⟩

/-- The base's cleared evaluation of a two-variable pencil: each
entry's base coefficients read at the composite point, leaving the
outer variable's polynomial matrix
(`lem:cellcount`'s entries polynomial in the stated variables). -/
def ppevalPC (S : split.PPMat) (ln : BPair) (c : Pos) (K : Nat) :
    split.PMat :=
  S.map (fun r => evalPC r ln c K)

/-- The level-carrying cell carrier: the pencil's site datum at the
balance-pair level `⟨x : y⟩` on the constant key, the stated middle
keys, and the trailing datum's entry at the top key — the pair
`(H(x) : aG(x))`'s one shape at the record representatives. -/
def levelPMat (A B G : elim.Mat) (x y : Pos) (mid : List BPair) :
    split.PMat :=
  List.zipWith (List.zipWith (fun a b => a :: (mid ++ [b])))
    (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
      (inertia.matScale x G)) B

/-- At the coupling's unit point the cleared evaluation of the
level carrier keeps the constant key alone at the clearing's
stated power: the carrier's matrix there is the level datum at
that positive rescaling. -/
theorem levelPMat_endEval (A B G : elim.Mat) (x y c : Pos)
    (mid : List BPair) (o : Nat)
    (hA : elim.sqAt A o) (hB : elim.sqAt B o) (hG : elim.sqAt G o) :
    elim.matOneValue
      (evalPC (levelPMat A B G x y mid) BPair.unit c
        (mid.length + 1))
      (inertia.matScaleB
        (ground.bpow (BPair.ofPos c) (mid.length + 1))
        (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
          (inertia.matScale x G))) := by
  have hD : elim.sqAt (inertia.siteDatum
      (elim.matAdd A (inertia.matScale y G))
      (inertia.matScale x G)) o :=
    inertia.sqAt_siteDatum o _ _
      (elim.sqAt_matAdd o A (inertia.matScale y G) hA
        (inertia.sqAt_matScale o y G hG))
      (inertia.sqAt_matScale o x G hG)
  have hle : (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
      (inertia.matScale x G)).length ≤ B.length := by
    rw [elim.sqAt_len hD, elim.sqAt_len hB]
    exact Nat.le_refl o
  have hheads : (levelPMat A B G x y mid).map (fun r => r.map
      (fun p => ground.getAt BPair.unit p 0))
      = inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
        (inertia.matScale x G) := by
    show (List.zipWith (List.zipWith (fun a b => a :: (mid ++ [b])))
      (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
        (inertia.matScale x G)) B).map (fun r => r.map
      (fun p => ground.getAt BPair.unit p 0)) = _
    rw [ground.map2_getAt_zipWith BPair.unit (fun a b => a :: (mid ++ [b])) 0
      (fun a _ => a) (fun a b => rfl)]
    exact ground.zipWith2_left _ _ hle
      (elim.rowsLen_widths_le _ _ (elim.rowsLen_of_sqAt hD)
        (elim.rowsLen_of_sqAt hB) hle)
  rw [← hheads]
  exact evalPC_unit c (mid.length + 1) (levelPMat A B G x y mid)


/-- One row's cleared evaluation at a point: each level-carrier
entry collects its constant key at the clearing's full power and
its top key at the point's, the unit middles absorbing
(`poly.evalClear_ends` entrywise). -/
private theorem rowLE (mid : List BPair) (hmid : poly.unitTail mid)
    (ln : BPair) (c : Pos) :
    ∀ (sr br : List BPair), sr.length = br.length →
    poly.oneValue
      ((List.zipWith (fun a b => a :: (mid ++ [b])) sr br).map
        (fun p => poly.evalClear p ln c (mid.length + 1)))
      (List.zipWith ground.bpairOps.add
        (poly.scaleP (ground.bpow (BPair.ofPos c) (mid.length + 1)) sr)
        (poly.scaleP (ground.bpow ln (mid.length + 1)) br))
  | [], [], _ => trivial
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | s :: sr, b :: br, h =>
    ⟨BPair.oneValue_trans (poly.evalClear_ends s b mid hmid ln c)
      (BPair.add_congr
        (BPair.oneValue_symm (BPair.norm_oneValue _))
        (BPair.oneValue_symm (BPair.norm_oneValue _))),
     rowLE mid hmid ln c sr br (Nat.succ.inj h)⟩

private theorem matLE (mid : List BPair) (hmid : poly.unitTail mid)
    (ln : BPair) (c : Pos) (o : Nat) :
    ∀ (S B : elim.Mat), S.length = B.length →
    elim.rowsLen o S → elim.rowsLen o B →
    elim.matOneValue
      ((List.zipWith (List.zipWith (fun a b => a :: (mid ++ [b]))) S B).map
        (fun r => r.map (fun p => poly.evalClear p ln c (mid.length + 1))))
      (List.zipWith (List.zipWith ground.bpairOps.add)
        (S.map (poly.scaleP (ground.bpow (BPair.ofPos c) (mid.length + 1))))
        (B.map (poly.scaleP (ground.bpow ln (mid.length + 1)))))
  | [], [], _, _, _ => trivial
  | [], _ :: _, h, _, _ => Nat.noConfusion h
  | _ :: _, [], h, _, _ => Nat.noConfusion h
  | sr :: S, br :: B, h, hS, hB =>
    ⟨rowLE mid hmid ln c sr br (hS.1.trans hB.1.symm),
     matLE mid hmid ln c o S B (Nat.succ.inj h) hS.2 hB.2⟩

/-- The cleared evaluation of the level carrier at any point: the
evaluated matrix is the level datum at the clearing's full power
joined to the magnetic member at the point's own, the unit middles
absorbing — `def:pencil`'s root coordinate, the coupling-evaluated
pencil read off the carrier. -/
theorem levelPMat_eval (A B G : elim.Mat) (x y : Pos)
    (mid : List BPair) (o : Nat)
    (hA : elim.sqAt A o) (hB : elim.sqAt B o) (hG : elim.sqAt G o)
    (hmid : poly.unitTail mid) (ln : BPair) (c : Pos) :
    elim.matOneValue
      (evalPC (levelPMat A B G x y mid) ln c (mid.length + 1))
      (elim.matAdd
        (inertia.matScaleB
          (ground.bpow (BPair.ofPos c) (mid.length + 1))
          (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
            (inertia.matScale x G)))
        (inertia.matScaleB (ground.bpow ln (mid.length + 1)) B)) := by
  have hD : elim.sqAt (inertia.siteDatum
      (elim.matAdd A (inertia.matScale y G))
      (inertia.matScale x G)) o :=
    inertia.sqAt_siteDatum o _ _
      (elim.sqAt_matAdd o A (inertia.matScale y G) hA
        (inertia.sqAt_matScale o y G hG))
      (inertia.sqAt_matScale o x G hG)
  exact matLE mid hmid ln c o _ B
    ((elim.sqAt_len hD).trans (elim.sqAt_len hB).symm)
    (elim.rowsLen_of_sqAt hD) (elim.rowsLen_of_sqAt hB)

/-- `lem:freecell`'s display read entrywise: the level carrier's
entry at a key pair inside the order is the one polynomial list —
the level datum's entry at the constant key
(`thm:certconstruct`'s balance-pair level cross-added,
`def:pencil`'s join at `lem:inertia`'s entrywise site structure),
the stated middle keys, and the trailing member's entry at the top
key. -/
theorem levelPMat_entry (A B G : elim.Mat) (x y : Pos)
    (mid : List BPair) (o : Nat) (hA : elim.sqAt A o)
    (hB : elim.sqAt B o) (hG : elim.sqAt G o) (i j : Nat)
    (hi : i < o) (hj : j < o) :
    ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (levelPMat A B G x y mid) i) j
      = ground.getAt BPair.unit (ground.getAt ([] : List BPair)
          (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
            (inertia.matScale x G)) i) j
        :: (mid ++ [ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) B i) j]) := by
  have hD : elim.sqAt (inertia.siteDatum
      (elim.matAdd A (inertia.matScale y G))
      (inertia.matScale x G)) o :=
    inertia.sqAt_siteDatum o _ _
      (elim.sqAt_matAdd o A (inertia.matScale y G) hA
        (inertia.sqAt_matScale o y G hG))
      (inertia.sqAt_matScale o x G hG)
  show ground.getAt ([] : Poly) (ground.getAt ([] : List Poly)
      (List.zipWith (List.zipWith (fun a b => a :: (mid ++ [b])))
        (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
          (inertia.matScale x G)) B) i) j = _
  rw [ground.getAt_zipWith ([] : List BPair) ([] : List BPair)
      ([] : List Poly)
      (List.zipWith (fun a b => a :: (mid ++ [b]))) _ B i
      (by rw [elim.sqAt_len hD]; exact hi)
      (by rw [elim.sqAt_len hB]; exact hi),
    ground.getAt_zipWith BPair.unit BPair.unit ([] : Poly)
      (fun a b => a :: (mid ++ [b])) _ _ j
      (by rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hD)
            (by rw [elim.sqAt_len hD]; exact hi)]
          exact hj)
      (by rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hB)
            (by rw [elim.sqAt_len hB]; exact hi)]
          exact hj)]

/-- The level carrier's shape read: the stated order with every
entry inside the affine list's own clearing degree, the
construction's length data (`lem:freecell`'s entries, one
polynomial list each). -/
theorem pShapeAt_levelPMat (A B G : elim.Mat) (x y : Pos)
    (mid : List BPair) (o : Nat) (hA : elim.sqAt A o)
    (hB : elim.sqAt B o) (hG : elim.sqAt G o) :
    pShapeAt (levelPMat A B G x y mid) o (mid.length + 1) := by
  have hD : elim.sqAt (inertia.siteDatum
      (elim.matAdd A (inertia.matScale y G))
      (inertia.matScale x G)) o :=
    inertia.sqAt_siteDatum o _ _
      (elim.sqAt_matAdd o A (inertia.matScale y G) hA
        (inertia.sqAt_matScale o y G hG))
      (inertia.sqAt_matScale o x G hG)
  have hlen : (levelPMat A B G x y mid).length = o :=
    ground.length_zipWith _ _ _ o (elim.sqAt_len hD) (elim.sqAt_len hB)
  have hrow : ∀ i, i < o →
      ground.getAt ([] : List Poly) (levelPMat A B G x y mid) i
        = List.zipWith (fun a b => a :: (mid ++ [b]))
            (ground.getAt ([] : List BPair)
              (inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
                (inertia.matScale x G)) i)
            (ground.getAt ([] : List BPair) B i) := fun i hi =>
    ground.getAt_zipWith ([] : List BPair) ([] : List BPair)
      ([] : List Poly)
      (List.zipWith (fun a b => a :: (mid ++ [b]))) _ B i
      (by rw [elim.sqAt_len hD]; exact hi)
      (by rw [elim.sqAt_len hB]; exact hi)
  have hrows : elim.rowsLen o (levelPMat A B G x y mid) := by
    refine elim.rowsLen_intro _ (fun i hi => ?_)
    rw [hlen] at hi
    rw [hrow i hi]
    exact ground.length_zipWith _ _ _ o
      (elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hD)
        (by rw [elim.sqAt_len hD]; exact hi))
      (elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hB)
        (by rw [elim.sqAt_len hB]; exact hi))
  refine pShapeAt_of hlen hrows ?_
  refine ground.all_of_getAt ([] : List Poly) _ _ (fun i hi => ?_)
  rw [hlen] at hi
  rw [hrow i hi]
  refine ground.all_of_getAt ([] : Poly) _ _ (fun j hj => ?_)
  have hjo : j < o := by
    rw [ground.length_zipWith _ _ _ o
        (elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hD)
          (by rw [elim.sqAt_len hD]; exact hi))
        (elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hB)
          (by rw [elim.sqAt_len hB]; exact hi))] at hj
    exact hj
  rw [ground.getAt_zipWith BPair.unit BPair.unit ([] : Poly)
      (fun a b => a :: (mid ++ [b])) _ _ j
      (by rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hD)
            (by rw [elim.sqAt_len hD]; exact hi)]
          exact hjo)
      (by rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hB)
            (by rw [elim.sqAt_len hB]; exact hi)]
          exact hjo)]
  refine ground.leBle ?_
  show (mid ++ [ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) B i) j]).length + 1
    ≤ mid.length + 1 + 1
  rw [ground.length_append]
  exact Nat.le_refl _

/-! `lem:inertia`'s deflation at this module's polynomial carrier:
the entrywise calculus of `def:elim`'s displayed operations passes
the cleared evaluation through the entry bundle's graded map
(`evalPC_pmatAdd`, `evalPC_pswapM`, `evalPC_pscaleM`,
`evalPC_pmatMul`, the powers splitting at the factors' own degree
reads), and the pivot blocks' reads at a symmetric square datum
(`inertia.pivotBlocks`). -/

/-- The evaluated matrix's entry at two keys: the site datum's entry
there, cleared at the stated power. -/
theorem getAt_evalPC (ln : BPair) (c : Pos) (K : Nat) :
    ∀ (S : split.PMat) (i j : Nat),
      ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (evalPC S ln c K) i) j
        = poly.evalClear
            (ground.getAt ([] : Poly)
              (ground.getAt ([] : List Poly) S i) j) ln c K :=
  elim.getAt_mapRowsO ([] : Poly) BPair.unit
    (fun p => poly.evalClear p ln c K) rfl

/-- The cleared evaluation keeps the row count (`lem:cellcount`'s
shape discipline at the evaluated family). -/
theorem length_evalPC (S : split.PMat) (ln : BPair) (c : Pos)
    (K : Nat) : (evalPC S ln c K).length = S.length :=
  ground.length_map _ S

/-- The cleared evaluation keeps every row's width (`lem:cellcount`'s
shape discipline at the evaluated family). -/
theorem rowsLen_evalPC (n : Nat) (S : split.PMat) (ln : BPair)
    (c : Pos) (K : Nat) (h : elim.rowsLen n S) :
    elim.rowsLen n (evalPC S ln c K) :=
  elim.rowsLen_mapRowsO (fun p => poly.evalClear p ln c K) S n h

/-- The polynomial product's row width is the second factor's own. -/
private theorem rowLen_pmatMul (a b : split.PMat) (i : Nat)
    (hi : i < a.length) :
    (ground.getAt ([] : List Poly) (split.pmatMul a b) i).length
      = (b.headD ([] : List Poly)).length :=
  elim.rowsLen_getAt _ i (elim.rowsLen_matMulO poly.polyOps a b _ rfl)
    (by rw [show (split.pmatMul a b).length = a.length from
      elim.length_matMulO poly.polyOps a b]; exact hi)

/-- Every entry's degree sits within the shape read's clearing power, a
key beyond the datum reading the vacant list. -/
theorem ent_ble {S : split.PMat} {o K : Nat} (hsh : pShapeAt S o K) :
    ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1 :=
  fun i j => ground.bleLe (elim.shapeAt_entry hsh ([] : Poly) rfl i j)

/-- One row's cleared evaluations at a scaled point read the
scale's power on the row (`poly.evalClear_scalePoint` entrywise). -/
private theorem scalePoint_row (xN : BPair) (c w : ground.Pos)
    (K : Nat) : ∀ r : List Poly,
    (r.all (fun p => Nat.ble p.length (K + 1))) = true →
    poly.oneValue
      (r.map (fun p => poly.evalClear p (xN * BPair.ofPos w) (c * w) K))
      (poly.scaleP (ground.bpow (BPair.ofPos w) K)
        (r.map (fun p => poly.evalClear p xN c K)))
  | [], _ => trivial
  | p :: r, h =>
    have hs := ground.andSplitB h
    ⟨BPair.oneValue_trans
      (poly.evalClear_scalePoint p xN c w K (ground.bleLe hs.1))
      (BPair.oneValue_symm (BPair.norm_oneValue _)),
     scalePoint_row xN c w K r hs.2⟩

private theorem scalePointGo (o K : Nat) (xN : BPair)
    (c w : ground.Pos) : ∀ S : List (List Poly),
    (S.all (fun r => Nat.beq r.length o
      && r.all (fun p => Nat.ble p.length (K + 1)))) = true →
    elim.matOneValue
      (evalPC S (xN * BPair.ofPos w) (c * w) K)
      (inertia.matScaleB (ground.bpow (BPair.ofPos w) K)
        (evalPC S xN c K))
  | [], _ => trivial
  | r :: t, h =>
    have hs := ground.andSplitB h
    have hr := ground.andSplitB hs.1
    ⟨scalePoint_row xN c w K r hr.2, scalePointGo o K xN c w t hs.2⟩

/-- The cleared evaluation at a scaled point, the matrix read: the
scale's power at the clearing entrywise. -/
theorem evalPC_scalePoint (S : split.PMat) (o K : Nat)
    (xN : BPair) (c w : ground.Pos) (hsh : pShapeAt S o K) :
    elim.matOneValue
      (evalPC S (xN * BPair.ofPos w) (c * w) K)
      (inertia.matScaleB (ground.bpow (BPair.ofPos w) K)
        (evalPC S xN c K)) :=
  scalePointGo o K xN c w S (ground.andSplitB hsh).2

/-- One row's cleared evaluations move across the point's one-value
read (`poly.evalClear_congrPoint` entrywise). -/
private theorem congrPoint_row {x y : BPair} (h : x.oneValue y)
    (c : ground.Pos) (K : Nat) : ∀ r : List Poly,
    poly.oneValue (r.map (fun p => poly.evalClear p x c K))
      (r.map (fun p => poly.evalClear p y c K))
  | [] => trivial
  | p :: r =>
    ⟨poly.evalClear_congrPoint p h c K, congrPoint_row h c K r⟩

/-- The evaluation moves across the point's one-value read, the
matrices entrywise one value. -/
theorem evalPC_congrPoint {x y : BPair} (h : x.oneValue y)
    (c : ground.Pos) (K : Nat) : ∀ S : split.PMat,
    elim.matOneValue (evalPC S x c K) (evalPC S y c K)
  | [] => trivial
  | r :: t => ⟨congrPoint_row h c K r, evalPC_congrPoint h c K t⟩

/-- The pencil's counts move across the point's one-value read: two
splits at the two representatives' cleared evaluations read one
count, the scale's power cleared at `lem:inertia`'s scaled split
with the congruence at the shared representative
(`lem:cellcount`'s stage points at the homogeneity principle). -/
theorem evalPC_pointCongr {o : Nat} (S : split.PMat) (K : Nat)
    (vn wn : BPair) (vc wc : ground.Pos)
    (sp sp' : inertia.Split o)
    (hsh : pShapeAt S o K)
    (h : (⟨vn, vc⟩ : ground.CPair).oneValue ⟨wn, wc⟩)
    (hv : inertia.splitRead (evalPC S vn vc K) sp)
    (hw : inertia.splitRead (evalPC S wn wc K) sp') :
    inertia.revAt sp = inertia.revAt sp' := by
  have hw1 : BPair.unit < ground.bpow (BPair.ofPos wc) K :=
    ground.unitLtBpow (ground.unitLtOfPos wc) K
  have hw2 : BPair.unit < ground.bpow (BPair.ofPos vc) K :=
    ground.unitLtBpow (ground.unitLtOfPos vc) K
  have hpt : (vn * BPair.ofPos wc).oneValue (wn * BPair.ofPos vc) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm vn (BPair.ofPos wc))) ?_
    refine BPair.oneValue_trans (BPair.ofPos_scale wc vn) ?_
    refine BPair.oneValue_trans
      (show (vn.scale wc).oneValue (wn.scale vc) from h) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofPos_scale vc wn)) ?_
    exact BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos vc) wn)
  have h3 := evalPC_scalePoint S o K wn wc vc hsh
  rw [ground.mul_comm wc vc] at h3
  have hM : elim.matOneValue
      (inertia.matScaleB (ground.bpow (BPair.ofPos wc) K)
        (evalPC S vn vc K))
      (inertia.matScaleB (ground.bpow (BPair.ofPos vc) K)
        (evalPC S wn wc K)) :=
    elim.matOne_trans
      (elim.matOne_symm (evalPC_scalePoint S o K vn vc wc hsh))
      (elim.matOne_trans (evalPC_congrPoint hpt (vc * wc) K S) h3)
  have hsq2 : elim.sqAt
      (inertia.matScaleB (ground.bpow (BPair.ofPos vc) K)
        (evalPC S wn wc K)) o :=
    inertia.sqAt_scaleB _ o _ hw.1
  have hsp1 := inertia.scaleSplit_read
    (ground.bpow (BPair.ofPos wc) K)
    (ground.offOfUnitLt hw1) (evalPC S vn vc K) sp hv
  have hsp1' := inertia.splitRead_congr _ _ hsq2 hM _ hsp1
  have hrev1 := inertia.scaleSplit_rev
    (ground.bpow (BPair.ofPos wc) K) hw1 sp
  have hrev2 := inertia.rev_scale
    (ground.bpow (BPair.ofPos vc) K) hw2
    (evalPC S wn wc K) sp' (inertia.scaleSplit
      (ground.bpow (BPair.ofPos wc) K) sp) hw hsp1'
  exact hrev1.symm.trans hrev2

/-- The shape read's row count. -/
theorem pShape_len {S : split.PMat} {o K : Nat}
    (h : pShapeAt S o K) : S.length = o :=
  elim.shapeAt_len h

/-- The shape read's row widths. -/
theorem pShape_rows {S : split.PMat} {o K : Nat}
    (h : pShapeAt S o K) : elim.rowsLen o S :=
  elim.shapeAt_rows h

/-- The evaluation of a shaped pencil is square at the stated
order. -/
theorem evalPC_sqAt {S : split.PMat} {o K : Nat}
    (hsh : pShapeAt S o K) (x : BPair) (c : Pos) :
    elim.sqAt (evalPC S x c K) o :=
  elim.sqAt_of ((length_evalPC S x c K).trans (pShape_len hsh))
    (rowsLen_evalPC o S x c K (pShape_rows hsh))

/-- The entrywise sum's cleared evaluation is the evaluations' own sum
(`lem:cellcount`'s cleared evaluation at `def:elim`'s displayed sum). -/
theorem evalPC_pmatAdd (ln : BPair) (c : Pos) (N : Nat) :
    ∀ A B : split.PMat,
      elim.matOneValue (evalPC (split.pmatAdd A B) ln c N)
        (elim.matAdd (evalPC A ln c N) (evalPC B ln c N)) :=
  fun A B => elim.matOne_of_matched
    (elim.matAddO_mapRowsO poly.polyOps ground.bpairOps ground.bpairRead
      (fun p => poly.evalClear p ln c N)
      (fun x y => evalClear_add x y ln c N) A B)

/-- Two polynomial matrices reading one value entrywise have cleared
evaluations reading one value entrywise, at the shared point and the
shared clearing power (`lem:cellcount`'s cleared evaluation across a
representative). -/
theorem evalPC_pcongr (ln : BPair) (c : Pos) (N : Nat) :
    ∀ {A B : split.PMat}, split.pmatOneValue A B →
      elim.matOneValue (evalPC A ln c N) (evalPC B ln c N) :=
  fun h => elim.matOne_of_matched
    (elim.mapRowsO_congr poly.polyRead ground.bpairRead
      (fun p => poly.evalClear p ln c N)
      (fun h => poly.evalClear_congr h ln c N) h)

/-- The memberwise swap's cleared evaluation is the evaluation's own
swap (`lem:cellcount`'s cleared evaluation at `def:elim`'s displayed
balance partner). -/
theorem evalPC_pswapM (ln : BPair) (c : Pos) (N : Nat) :
    ∀ S : split.PMat,
      elim.matOneValue (evalPC (split.pswapM S) ln c N)
        (elim.matSwap (evalPC S ln c N)) :=
  fun S => elim.matOne_of_matched
    (elim.matSwapO_mapRowsO poly.polyOps ground.bpairOps ground.bpairRead
      (fun p => poly.evalClear p ln c N)
      (fun x => evalClear_neg x ln c N) S)

/-- A rescaling's cleared evaluation is the scale's evaluation weighting
the evaluated matrix, the powers splitting at the representatives'
caps — the canonical key counts, one value's own read
(`def:ground`'s homogeneity principle). -/
theorem evalPC_pscaleM (f : Poly) (ln : BPair) (c : Pos)
    (K1 K2 : Nat) (hf : (poly.vnorm f).length ≤ K1 + 1) :
    ∀ S : split.PMat,
      (∀ i j, (poly.vnorm (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) j)).length ≤ K2 + 1) →
      elim.matOneValue (evalPC (split.pscaleM f S) ln c (K1 + K2))
        (inertia.matScaleB (poly.evalClear f ln c K1) (evalPC S ln c K2)) :=
  fun S h => elim.matOne_trans
    (elim.matOne_of_matched
      (elim.scaleO_mapRowsO poly.polyOps ground.bpairOps ground.bpairRead
        (fun K p => poly.evalClear p ln c K)
        (fun p K => (poly.vnorm p).length ≤ K + 1)
        (fun K1 K2 x y hx hy => poly.evalClear_mulCap x y ln c K1 K2 hx hy)
        f K1 K2 hf S h))
    (inertia.scaleO_matScaleB _ _)

/-- The polynomial product's cleared evaluation is the evaluated
factors' product, the powers splitting and every entry's canonical
representative within its factor's own cap (`def:ground`'s
homogeneity principle, the value-identical key count): the bundle's
graded product read against the canonical-representative product. -/
theorem evalPC_pmatMul (a b : split.PMat) (ln : BPair) (c : Pos)
    (K1 K2 w n : Nat) (ha : elim.rowsLen w a) (hbl : b.length = w)
    (hw : 0 < w) (hb : elim.rowsLen n b)
    (hda : ∀ i j, (poly.vnorm (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) a i) j)).length ≤ K1 + 1)
    (hdb : ∀ i j, (poly.vnorm (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) b i) j)).length ≤ K2 + 1) :
    elim.matOneValue (evalPC (split.pmatMul a b) ln c (K1 + K2))
      (elim.matMul (evalPC a ln c K1) (evalPC b ln c K2)) :=
  elim.matOne_trans
    (elim.matOne_of_matched
      (elim.matMulO_mapRowsO poly.polyOps ground.bpairOps ground.bpairRead
        BPair.oneValue_refl (fun h1 h2 => BPair.oneValue_trans h1 h2)
        (fun h1 h2 => BPair.add_congr h1 h2)
        (fun K p => poly.evalClear p ln c K)
        (fun p K => (poly.vnorm p).length ≤ K + 1)
        (fun _ => rfl) (fun K x y => evalClear_add x y ln c K)
        (fun K1 K2 x y hx hy => poly.evalClear_mulCap x y ln c K1 K2 hx hy)
        a b K1 K2 w n hbl hw hb hda hdb))
    (elim.matMulO_matMul (evalPC a ln c K1) (evalPC b ln c K2) w n
      (rowsLen_evalPC w a ln c K1 ha) ((length_evalPC b ln c K2).trans hbl)
      hw (rowsLen_evalPC n b ln c K2 hb))

/-- The selection passes the cleared evaluation: the evaluated
matrix's selected block is the selected pencil's own evaluation. -/
theorem selM_evalPC (ln : BPair) (c : Pos) (K : Nat)
    (S : split.PMat) (J : List Nat) : ∀ I : List Nat,
    elim.selM I J (evalPC S ln c K) = evalPC (split.pselM I J S) ln c K :=
  fun I => elim.selMO_mapRowsO ([] : Poly) BPair.unit
    (fun p => poly.evalClear p ln c K) rfl S J I

/-! The pivot at every order over the polynomial carrier
(`thm:decimation`'s tower block, one nonsingular principal pivot at
its designated places, `lem:inertia`'s deflation at the pivot order
`k`): the polynomial minor's degree inside the order's multiple of
the cap and its cleared evaluation the evaluated pencil's own minor
(`elim.deg_minorO`, `elim.minorO_gmap` at the cleared evaluation's
graded map), the polynomial adjugate's entries one order below
(`split.padj`, the transposed cofactors), the adjugate-solved
witness `pdeflW` and the deflation cleared once `pdeflP`
(`inertia.deflPO` at the polynomial carrier) with its shape at the
clearing `(k + 1) K`, its evaluation the evaluated blocks' own
once-cleared deflation at the evaluated witness, the witness's solve
read, and the evaluated deflation's symmetry at a pivot off the
unit; at a vacant pivot list the deflation is the pencil itself. -/

/-- The cleared evaluation of the polynomial minor at the order's
multiple of the cap is the evaluated pencil's own minor
(`elim.minorO_gmap` at the cleared evaluation's graded map). -/
theorem evalClear_pminor (S : split.PMat) (ln : BPair) (c : Pos) (K : Nat)
    (hsq : elim.rowsLen S.length S)
    (h : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1) :
    (poly.evalClear (split.pminor S) ln c (S.length * K)).oneValue
      (elim.minor (evalPC S ln c K)) :=
  elim.minorO_gmap poly.polyOps ground.bpairOps ground.bpairRead poly.pnorm id
    BPair.norm BPair.norm (fun K p => poly.evalClear p ln c K)
    (fun p K => p.length ≤ K + 1)
    BPair.oneValue_refl (fun h => BPair.oneValue_symm h)
    (fun h1 h2 => BPair.oneValue_trans h1 h2)
    (fun h1 h2 => BPair.add_congr h1 h2)
    (fun h1 h2 => BPair.mul_congr h1 h2)
    (fun h => ground.swap_congr h)
    (fun _ => rfl) (evalClear_one ln c)
    (fun K x y => evalClear_add x y ln c K)
    (fun K1 K2 x y hx hy => evalClear_mul x y ln c K1 K2 hx hy)
    (fun K x => evalClear_neg x ln c K)
    (fun K x => poly.evalClear_congr (pnorm_oneValue x) ln c K)
    (fun _ _ => BPair.oneValue_refl _)
    (fun y => BPair.norm_oneValue y) (fun y => BPair.norm_oneValue y)
    (fun _ _ _ hK hx => Nat.le_trans hx (Nat.succ_le_succ hK))
    (fun K x y hx hy => poly.add_len_le x y (K + 1) hx hy)
    (fun K1 K2 x y hx hy => poly.mul_len_le x y K1 K2 hx hy)
    (fun _ x h => by rw [show (poly.polyOps.swap x).length = x.length from
      poly.length_neg x]; exact h)
    (fun _ x h => by rw [poly.pnorm_length]; exact h)
    (fun _ _ h => h) (fun _ => Nat.zero_le _) (Nat.le_refl 1) K S hsq h

/-- The adjugate-solved witness at a pivot list: the pivot block's
polynomial adjugate against the coupling
(`lem:inertia`'s solve `P C_P = B`, the adjugate against the
determinant, at the polynomial carrier). -/
def pdeflW (idx rest : List Nat) (S : split.PMat) : split.PMat :=
  split.pmatMul (split.padj (split.pselM idx idx S)) (split.pselM idx rest S)

/-- The deflation cleared once at a pivot of every order
(`lem:cellcount`'s deflation cleared once at the pivot's
determinant's magnitude, the read at a pivot whose determinant keeps
its upper side): the trailing block at the pivot minor against the
coupling's solved correction, `inertia.deflPO` at the upper side over
the polynomial carrier and adjugate, the clearing `(k + 1) K` at the
pivot order `k`; at a vacant pivot list the trailing block at the
vacant minor, `lem:inertia`'s display at a vacant coupling. -/
def pdeflP (idx rest : List Nat) (S : split.PMat) : split.PMat :=
  deflPO poly.polyOps poly.pnorm id split.padj false idx rest S

/-- The witness's row count is the pivot list's. -/
theorem length_pdeflW (idx rest : List Nat) (S : split.PMat) :
    (pdeflW idx rest S).length = idx.length :=
  (elim.length_matMulO poly.polyOps _ _).trans
    ((split.length_padj _).trans (split.length_pselM idx idx S))

/-- The witness's rows sit at the trailing list's count. -/
theorem rowsLen_pdeflW (idx rest : List Nat) (S : split.PMat)
    (hk0 : 0 < idx.length) :
    elim.rowsLen rest.length (pdeflW idx rest S) :=
  elim.rowsLen_matMulO poly.polyOps _ _ rest.length
    (elim.headD_width rest.length _
      (by rw [split.length_pselM]; exact hk0) (split.rowsLen_pselM rest S idx))

/-- The once-cleared deflation's row count is the trailing list's. -/
theorem length_pdeflP (idx rest : List Nat) (S : split.PMat) :
    (pdeflP idx rest S).length = rest.length :=
  length_deflPO poly.polyOps poly.pnorm id split.padj false idx rest S

/-- The once-cleared deflation's rows sit at the trailing list's
count. -/
theorem rowsLen_pdeflP (idx rest : List Nat) (S : split.PMat) :
    elim.rowsLen rest.length (pdeflP idx rest S) :=
  rowsLen_deflPO poly.polyOps poly.pnorm id split.padj false idx rest S
    ((split.length_padj _).trans (split.length_pselM idx idx S))

/-- The correction's cap at the coupling's against the witness's:
`(k+1)K = K + kK`. -/
private theorem clearCoup (k K : Nat) : (k + 1) * K = K + k * K := by
  rw [Nat.succ_mul, Nat.add_comm]

/-- The selected block keeps the pencil's entry cap. -/
theorem deg_pselM (S : split.PMat) (K : Nat)
    (h : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1)
    (I J : List Nat) : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (split.pselM I J S) i) j).length ≤ K + 1 :=
  elim.deg_selMO ([] : Poly) (fun p K => p.length ≤ K + 1) h I J

/-- The selected square block's shape: the block at its key list's
order at the pencil's own clearing. -/
theorem pShape_pselM (S : split.PMat) (K : Nat) (I : List Nat)
    (h : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1) :
    pShapeAt (split.pselM I I S) I.length K := by
  refine pShapeAt_of (split.length_pselM _ _ _) (split.rowsLen_pselM I S I) ?_
  refine ground.all_of_getAt ([] : List Poly) _ _ (fun a _ => ?_)
  refine ground.all_of_getAt ([] : Poly) _ _ (fun c _ => ?_)
  exact ground.leBle (deg_pselM S K h _ _ a c)

/-- The polynomial product's entries sit within the factors' caps'
sum. -/
private theorem deg_pmatMul (a b : split.PMat) (K1 K2 : Nat)
    (ha : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) a i) j).length ≤ K1 + 1)
    (hb : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) b i) j).length ≤ K2 + 1) :
    ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (split.pmatMul a b) i) j).length
        ≤ K1 + K2 + 1 :=
  elim.deg_matMulO poly.polyOps (fun p K => p.length ≤ K + 1)
    (fun x y hx hy => poly.add_len_le x y (K1 + K2 + 1) hx hy)
    (fun x y hx hy => poly.mul_len_le x y K1 K2 hx hy)
    (Nat.zero_le _) a b ha hb

/-- The once-cleared deflation's shape at either side and a pivot of
every order: the trailing order at the clearing `(k + 1) K`, the
pivot minor's cap joined to the trailing block's and the
correction's own (`inertia.deg_deflPO` at the polynomial carrier's
degree). -/
private theorem pShape_deflS (lower : Bool) (S : split.PMat) (o K : Nat)
    (idx rest : List Nat) (hS : pShapeAt S o K) :
    pShapeAt (deflPO poly.polyOps poly.pnorm id split.padj lower idx rest S)
      rest.length ((idx.length + 1) * K) := by
  match idx with
  | [] =>
    have hd := ent_ble hS
    have hm : (split.pminor (split.pselM [] [] S)).length ≤ 0 * K + 1 := by
      have h := split.pminor_len (split.pselM [] [] S) K (deg_pselM S K hd [] [])
      rw [split.length_pselM] at h
      exact h
    have hmc : (cond lower (poly.neg (split.pminor (split.pselM [] [] S)))
        (split.pminor (split.pselM [] [] S))).length ≤ 0 * K + 1 := by
      cases lower with
      | false => exact hm
      | true =>
        show (poly.neg (split.pminor (split.pselM [] [] S))).length ≤ 0 * K + 1
        rw [poly.length_neg]; exact hm
    have hdeg := elim.deg_scaleO poly.polyOps (fun p K => p.length ≤ K + 1)
      (fun x y hx hy => poly.mul_len_le x y (0 * K) K hx hy) (Nat.zero_le _)
      _ hmc _ (deg_pselM S K hd rest rest)
    have hK : (([] : List Nat).length + 1) * K = 0 * K + K := Nat.succ_mul 0 K
    rw [hK]
    refine pShapeAt_of (length_deflPO _ _ _ _ lower [] rest S)
      (rowsLen_deflPO _ _ _ _ lower [] rest S
        ((split.length_padj _).trans (split.length_pselM [] [] S))) ?_
    refine ground.all_of_getAt ([] : List Poly) _ _ (fun a _ => ?_)
    refine ground.all_of_getAt ([] : Poly) _ _ (fun b _ => ?_)
    exact ground.leBle (hdeg a b)
  | i :: t =>
    have hd := ent_ble hS
    have hP := deg_pselM S K hd (i :: t) (i :: t)
    have hPl : (split.pselM (i :: t) (i :: t) S).length = t.length + 1 :=
      split.length_pselM _ _ _
    have hm : (split.pminor (split.pselM (i :: t) (i :: t) S)).length
        ≤ (t.length + 1) * K + 1 := by
      have h := split.pminor_len (split.pselM (i :: t) (i :: t) S) K hP
      rw [hPl] at h
      exact h
    have hA := split.padj_len (split.pselM (i :: t) (i :: t) S) K t.length hPl hP
    have hdeg := deg_deflPO poly.polyOps poly.pnorm id split.padj
      (fun p K => p.length ≤ K + 1)
      (fun K x y hx hy => poly.add_len_le x y (K + 1) hx hy)
      (fun K1 K2 x y hx hy => poly.mul_len_le x y K1 K2 hx hy)
      (fun _ x h => by rw [show (poly.polyOps.swap x).length = x.length from
        poly.length_neg x]; exact h)
      (fun _ => Nat.zero_le _) lower
      S K ((t.length + 1) * K) (t.length * K) (i :: t) rest hd
      (Nat.succ_mul t.length K).symm hm hA
    have hdeg' : ∀ a b, (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly)
        (deflPO poly.polyOps poly.pnorm id split.padj lower (i :: t) rest S) a) b).length
        ≤ (t.length + 1 + 1) * K + 1 := by
      intro a b
      rw [Nat.succ_mul (t.length + 1) K]
      exact hdeg a b
    show pShapeAt (deflPO poly.polyOps poly.pnorm id split.padj lower (i :: t) rest S)
      rest.length ((t.length + 1 + 1) * K)
    refine pShapeAt_of (length_deflPO _ _ _ _ lower (i :: t) rest S)
      (rowsLen_deflPO _ _ _ _ lower (i :: t) rest S
        ((split.length_padj _).trans (split.length_pselM (i :: t) (i :: t) S))) ?_
    refine ground.all_of_getAt ([] : List Poly) _ _ (fun a _ => ?_)
    refine ground.all_of_getAt ([] : Poly) _ _ (fun b _ => ?_)
    exact ground.leBle (hdeg' a b)

/-- The once-cleared deflation's shape at a pivot of every order: the
trailing order at the clearing `(k + 1) K`, the pivot minor's cap
joined to the trailing block's and the correction's own
(`inertia.deg_deflPO` at the polynomial carrier's degree). -/
theorem pShape_pdeflP (S : split.PMat) (o K : Nat) (idx rest : List Nat)
    (hS : pShapeAt S o K) :
    pShapeAt (pdeflP idx rest S) rest.length ((idx.length + 1) * K) :=
  pShape_deflS false S o K idx rest hS

/-- The replicated diagonal's cleared evaluation is the entry's
evaluation weighting the identity, `def:elim`'s adjugate identity's
right side read at a stage point. -/
theorem evalPC_pdiag_repl (f : Poly) (n : Nat) (ln : BPair) (c : Pos)
    (N : Nat) :
    elim.matOneValue (evalPC (split.pdiag (List.replicate n f)) ln c N)
      (inertia.matScaleB (poly.evalClear f ln c N) (elim.idMat n)) := by
  have hrl : (List.replicate n f).length = n := ground.length_replicate f n
  have hDl : (split.pdiag (List.replicate n f)).length = n :=
    (elim.diagO_len poly.polyOps _).trans hrl
  have hDr : elim.rowsLen n (split.pdiag (List.replicate n f)) := by
    have h := elim.diagO_rows poly.polyOps (List.replicate n f)
    rw [hrl] at h
    exact h
  have hEl : (evalPC (split.pdiag (List.replicate n f)) ln c N).length = n :=
    (length_evalPC _ ln c N).trans hDl
  have hEr : elim.rowsLen n (evalPC (split.pdiag (List.replicate n f)) ln c N) :=
    rowsLen_evalPC n _ ln c N hDr
  have hIl : (inertia.matScaleB (poly.evalClear f ln c N) (elim.idMat n)).length
      = n := (inertia.length_scaleB _ _).trans (elim.length_idMat n)
  have hIr : elim.rowsLen n
      (inertia.matScaleB (poly.evalClear f ln c N) (elim.idMat n)) :=
    inertia.rowsLen_scaleB _ n _ (elim.rowsLen_idMat n)
  refine elim.matOne_of_entries _ _ n hEl hEr hIl hIr (fun i j hi hj => ?_)
  rw [getAt_evalPC ln c N _ i j,
    show inertia.matScaleB (poly.evalClear f ln c N) (elim.idMat n)
      = (elim.idMat n).map (fun r => r.map
          (fun x => (poly.evalClear f ln c N * x).norm)) from rfl,
    ground.getAt_map ([] : List BPair) ([] : List BPair) _ (elim.idMat n) i
      (by rw [elim.length_idMat]; exact hi),
    elim.idMat_row n i hi]
  show (poly.evalClear (ground.getAt poly.polyOps.unit (ground.getAt []
      (elim.diagO poly.polyOps (List.replicate n f)) i) j) ln c N).oneValue
    (ground.getAt BPair.unit ((elim.idRow n i).map
      (fun x => (poly.evalClear f ln c N * x).norm)) j)
  rw [elim.diagO_entry poly.polyOps (List.replicate n f) i j
      (by rw [hrl]; exact hi) (by rw [hrl]; exact hj),
    ground.getAt_replicate poly.polyOps.unit f n i hi,
    ground.getAt_map BPair.unit BPair.unit _ (elim.idRow n i) j
      (by rw [elim.length_idRow]; exact hj),
    elim.getAt_idRow n i j hj]
  cases Nat.decEq j i with
  | isTrue h =>
    rw [if_pos h, if_pos h]
    show (poly.evalClear f ln c N).oneValue
      (poly.evalClear f ln c N * BPair.ofPos Pos.one).norm
    exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.mul_one_read _))
  | isFalse h =>
    rw [if_neg h, if_neg h]
    show (poly.evalClear ([] : Poly) ln c N).oneValue
      (poly.evalClear f ln c N * BPair.unit).norm
    rw [poly.evalClear_nil]
    exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.mul_unit _))

/-- The witness's cleared evaluation is the evaluated adjugate against
the evaluated coupling, at the clearing `kK = (k−1)K + K`. -/
private theorem evalPC_pdeflW (S : split.PMat) (K : Nat) (i : Nat)
    (t rest : List Nat) (ln : BPair) (c : Pos)
    (hd : ∀ a b, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S a) b).length ≤ K + 1) :
    elim.matOneValue
      (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K))
      (elim.matMul
        (evalPC (split.padj (split.pselM (i :: t) (i :: t) S)) ln c
          (t.length * K))
        (elim.selM (i :: t) rest (evalPC S ln c K))) := by
  have hP := deg_pselM S K hd (i :: t) (i :: t)
  have hPl : (split.pselM (i :: t) (i :: t) S).length = t.length + 1 :=
    split.length_pselM _ _ _
  have hA := split.padj_len (split.pselM (i :: t) (i :: t) S) K t.length hPl hP
  have hAr : elim.rowsLen (t.length + 1)
      (split.padj (split.pselM (i :: t) (i :: t) S)) :=
    hPl ▸ split.rowsLen_padj (split.pselM (i :: t) (i :: t) S)
  rw [Nat.succ_mul, selM_evalPC ln c K S rest (i :: t)]
  exact evalPC_pmatMul _ _ ln c (t.length * K) K (t.length + 1) rest.length hAr
    (split.length_pselM _ _ _) (Nat.succ_pos _) (split.rowsLen_pselM rest S (i :: t))
    (fun a b => poly.capOfLen (hA a b))
    (fun a b => poly.capOfLen (deg_pselM S K hd (i :: t) rest a b))

/-- The witness's solve read at the evaluated blocks: the evaluated
pivot against the evaluated witness is the pivot's determinant
weighting the evaluated coupling (`lem:inertia`'s solve `P C_P = B`
at the adjugate against the determinant, `def:elim`'s adjugate
identity read at the stage point through `split.adjRead_all`). -/
theorem pdeflW_solve (S : split.PMat) (K : Nat) (idx rest : List Nat)
    (ln : BPair) (c : Pos)
    (hd : ∀ a b, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S a) b).length ≤ K + 1)
    (hk0 : 0 < idx.length) :
    elim.matOneValue
      (elim.matMul (elim.selM idx idx (evalPC S ln c K))
        (evalPC (pdeflW idx rest S) ln c (idx.length * K)))
      (inertia.matScaleB (elim.minor (elim.selM idx idx (evalPC S ln c K)))
        (elim.selM idx rest (evalPC S ln c K))) := by
  match idx, hk0 with
  | [], h => exact absurd h (Nat.lt_irrefl 0)
  | i :: t, _ =>
    have hk : 0 < t.length + 1 := Nat.succ_pos _
    have hP := deg_pselM S K hd (i :: t) (i :: t)
    have hPl : (split.pselM (i :: t) (i :: t) S).length = t.length + 1 :=
      split.length_pselM _ _ _
    have hPr : elim.rowsLen (t.length + 1) (split.pselM (i :: t) (i :: t) S) :=
      split.rowsLen_pselM (i :: t) S (i :: t)
    have hPsq : elim.rowsLen (split.pselM (i :: t) (i :: t) S).length
        (split.pselM (i :: t) (i :: t) S) := by
      rw [hPl]
      exact hPr
    have hA := split.padj_len (split.pselM (i :: t) (i :: t) S) K t.length hPl hP
    have hAl : (split.padj (split.pselM (i :: t) (i :: t) S)).length
        = t.length + 1 := (split.length_padj _).trans hPl
    have hAr : elim.rowsLen (t.length + 1)
        (split.padj (split.pselM (i :: t) (i :: t) S)) :=
      hPl ▸ split.rowsLen_padj (split.pselM (i :: t) (i :: t) S)
    have hPe : evalPC (split.pselM (i :: t) (i :: t) S) ln c K
        = elim.selM (i :: t) (i :: t) (evalPC S ln c K) :=
      (selM_evalPC ln c K S (i :: t) (i :: t)).symm
    have hPeSq : elim.sqAt (elim.selM (i :: t) (i :: t) (evalPC S ln c K))
        (t.length + 1) :=
      elim.sqAt_of (elim.length_selM _ _ _)
        (elim.rowsLen_selM (i :: t) (evalPC S ln c K) (i :: t))
    have hAel : (evalPC (split.padj (split.pselM (i :: t) (i :: t) S)) ln c
        (t.length * K)).length = t.length + 1 :=
      (length_evalPC _ _ _ _).trans hAl
    have hAer : elim.rowsLen (t.length + 1)
        (evalPC (split.padj (split.pselM (i :: t) (i :: t) S)) ln c
          (t.length * K)) :=
      rowsLen_evalPC _ _ ln c _ hAr
    have hBel : (elim.selM (i :: t) rest (evalPC S ln c K)).length = t.length + 1 :=
      elim.length_selM _ _ _
    have hBer : elim.rowsLen rest.length (elim.selM (i :: t) rest (evalPC S ln c K)) :=
      elim.rowsLen_selM _ _ _
    have hdet : (poly.evalClear (split.pminor (split.pselM (i :: t) (i :: t) S)) ln c
        ((t.length + 1) * K)).oneValue
        (elim.minor (elim.selM (i :: t) (i :: t) (evalPC S ln c K))) := by
      have h := evalClear_pminor (split.pselM (i :: t) (i :: t) S) ln c K hPsq hP
      rw [hPl, hPe] at h
      exact h
    have hAdj : elim.matOneValue
        (elim.matMul (elim.selM (i :: t) (i :: t) (evalPC S ln c K))
          (evalPC (split.padj (split.pselM (i :: t) (i :: t) S)) ln c
            (t.length * K)))
        (inertia.matScaleB (elim.minor (elim.selM (i :: t) (i :: t) (evalPC S ln c K)))
          (elim.idMat (t.length + 1))) := by
      have hrd : split.pmatOneValue
          (split.pmatMul (split.pselM (i :: t) (i :: t) S)
            (split.padj (split.pselM (i :: t) (i :: t) S)))
          (split.pdiag (List.replicate (split.pselM (i :: t) (i :: t) S).length
            (split.pminor (split.pselM (i :: t) (i :: t) S)))) :=
        split.adjRead_all _ hPsq
      rw [hPl] at hrd
      have hEv := evalPC_pmatMul (split.pselM (i :: t) (i :: t) S)
        (split.padj (split.pselM (i :: t) (i :: t) S)) ln c K (t.length * K)
        (t.length + 1) (t.length + 1) hPr hAl hk hAr
        (fun a b => poly.capOfLen (hP a b)) (fun a b => poly.capOfLen (hA a b))
      rw [← clearCoup, hPe] at hEv
      refine elim.matOne_trans (elim.matOne_symm hEv) ?_
      refine elim.matOne_trans (evalPC_pcongr ln c _ hrd) ?_
      refine elim.matOne_trans (evalPC_pdiag_repl _ _ ln c _) ?_
      exact inertia.matScaleB_congr hdet _
    have hW := evalPC_pdeflW S K i t rest ln c hd
    have hCwl : (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K)).length
        = t.length + 1 :=
      (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
    have hCwr : elim.rowsLen rest.length
        (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K)) :=
      rowsLen_evalPC _ _ ln c _ (rowsLen_pdeflW (i :: t) rest S hk)
    have hABl : (elim.matMul
        (evalPC (split.padj (split.pselM (i :: t) (i :: t) S)) ln c
          (t.length * K))
        (elim.selM (i :: t) rest (evalPC S ln c K))).length = t.length + 1 :=
      (elim.length_matMul _ _).trans hAel
    have hABr : elim.rowsLen rest.length (elim.matMul
        (evalPC (split.padj (split.pselM (i :: t) (i :: t) S)) ln c
          (t.length * K))
        (elim.selM (i :: t) rest (evalPC S ln c K))) :=
      elim.rowsLen_cast
        (elim.length_transposeM _ hBer (by rw [hBel]; exact hk))
        (elim.rowsLen_matMul _ _)
    show elim.matOneValue
      (elim.matMul (elim.selM (i :: t) (i :: t) (evalPC S ln c K))
        (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K))) _
    refine elim.matOne_trans (elim.matMul_congrR (n := t.length + 1)
      (k := rest.length) _ _ _ hCwr hABr hCwl hABl hW) ?_
    refine elim.matOne_trans (elim.matOne_symm
      (elim.matMul_assoc (n := t.length + 1) (k := t.length + 1) (s := rest.length)
        _ _ _ (elim.rowsLen_of_sqAt hPeSq) hAer hBer hAel hBel hk hk)) ?_
    refine elim.matOne_trans (elim.matMul_congrL _ _ _ hAdj) ?_
    refine elim.matOne_trans (inertia.matMul_scaleL _ _ _) ?_
    exact inertia.matOne_scaleB _
      (inertia.idMat_matMul (t.length + 1) _ hBer hBel hk)

/-- The once-cleared deflation's evaluation at an occupied pivot list
of every order (`lem:cellcount`'s designated minor) is the evaluated
blocks' once-cleared deflation at the evaluated witness
(`inertia.deflMatP`), the clearing `(k + 1) K` at the pivot order
`k`: the trailing block's scaling at the evaluated minor and the
correction at the evaluated coupling against the evaluated witness. -/
theorem evalPC_pdeflP {o : Nat} (S : split.PMat) (K : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hsh : pShapeAt S o K)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S ln c K)) (evalPC S ln c K))
    (hk0 : 0 < idx.length)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true) :
    elim.matOneValue
      (evalPC (pdeflP idx rest S) ln c ((idx.length + 1) * K))
      (inertia.deflMatP (elim.selM idx idx (evalPC S ln c K))
        (elim.selM idx rest (evalPC S ln c K))
        (elim.selM rest rest (evalPC S ln c K))
        (evalPC (pdeflW idx rest S) ln c (idx.length * K))) := by
  match idx, hk0 with
  | [], h => exact absurd h (Nat.lt_irrefl 0)
  | i :: t, hk =>
    have hd := ent_ble hsh
    have hMsq : elim.sqAt (evalPC S ln c K) o := evalPC_sqAt hsh ln c
    have hP := deg_pselM S K hd (i :: t) (i :: t)
    have hPl : (split.pselM (i :: t) (i :: t) S).length = t.length + 1 :=
      split.length_pselM _ _ _
    have hPsq : elim.rowsLen (split.pselM (i :: t) (i :: t) S).length
        (split.pselM (i :: t) (i :: t) S) := by
      rw [hPl]
      exact split.rowsLen_pselM (i :: t) S (i :: t)
    have hPe : evalPC (split.pselM (i :: t) (i :: t) S) ln c K
        = elim.selM (i :: t) (i :: t) (evalPC S ln c K) :=
      (selM_evalPC ln c K S (i :: t) (i :: t)).symm
    have hdet : (poly.evalClear (split.pminor (split.pselM (i :: t) (i :: t) S)) ln c
        ((t.length + 1) * K)).oneValue
        (elim.minor (elim.selM (i :: t) (i :: t) (evalPC S ln c K))) := by
      have h := evalClear_pminor (split.pselM (i :: t) (i :: t) S) ln c K hPsq hP
      rw [hPl, hPe] at h
      exact h
    have hm : (split.pminor (split.pselM (i :: t) (i :: t) S)).length
        ≤ (t.length + 1) * K + 1 := by
      have h := split.pminor_len (split.pselM (i :: t) (i :: t) S) K hP
      rw [hPl] at h
      exact h
    have hA := split.padj_len (split.pselM (i :: t) (i :: t) S) K t.length hPl hP
    have hWd : ∀ a b, (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly)
        (pdeflW (i :: t) rest S) a) b).length ≤ (t.length + 1) * K + 1 := by
      rw [Nat.succ_mul]
      exact deg_pmatMul _ _ _ _ hA (deg_pselM S K hd (i :: t) rest)
    have hWl : (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K)).length
        = t.length + 1 :=
      (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
    have hWr : elim.rowsLen rest.length
        (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K)) :=
      rowsLen_evalPC _ _ ln c _ (rowsLen_pdeflW (i :: t) rest S hk)
    have hX : elim.matOneValue
        (evalPC (split.pscaleM (split.pminor (split.pselM (i :: t) (i :: t) S))
          (split.pselM rest rest S)) ln c ((t.length + 1 + 1) * K))
        (inertia.matScaleB
          (elim.minor (elim.selM (i :: t) (i :: t) (evalPC S ln c K)))
          (elim.selM rest rest (evalPC S ln c K))) := by
      rw [Nat.succ_mul (t.length + 1) K, selM_evalPC ln c K S rest rest]
      refine elim.matOne_trans (evalPC_pscaleM _ ln c ((t.length + 1) * K) K
        (poly.capOfLen hm) _
        (fun a b => poly.capOfLen (deg_pselM S K hd rest rest a b))) ?_
      exact inertia.matScaleB_congr hdet _
    have hMul : elim.matOneValue
        (evalPC (split.pmatMul (split.pselM rest (i :: t) S) (pdeflW (i :: t) rest S))
          ln c ((t.length + 1 + 1) * K))
        (elim.matMul (elim.transposeM (elim.selM (i :: t) rest (evalPC S ln c K)))
          (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K))) := by
      rw [clearCoup]
      refine elim.matOne_trans (evalPC_pmatMul _ _ ln c K ((t.length + 1) * K)
        (t.length + 1) rest.length (split.rowsLen_pselM (i :: t) S rest)
        (length_pdeflW _ _ _) hk (rowsLen_pdeflW (i :: t) rest S hk)
        (fun a b => poly.capOfLen (deg_pselM S K hd rest (i :: t) a b))
        (fun a b => poly.capOfLen (hWd a b))) ?_
      rw [← selM_evalPC ln c K S (i :: t) rest]
      exact elim.matMul_congrL _ _ _ (elim.matOne_symm
        (elim.transposeM_selM (i :: t) rest (evalPC S ln c K) o hMsq hMsym hk
          hidx hrest))
    have hY : elim.matOneValue
        (evalPC (split.pswapM (split.pmatMul (split.pselM rest (i :: t) S)
          (pdeflW (i :: t) rest S))) ln c ((t.length + 1 + 1) * K))
        (elim.matSwap
          (elim.matMul (elim.transposeM (elim.selM (i :: t) rest (evalPC S ln c K)))
            (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K)))) :=
      elim.matOne_trans (evalPC_pswapM ln c _ _) (elim.matSwap_congr hMul)
    have hXr : elim.rowsLen rest.length
        (evalPC (split.pscaleM (split.pminor (split.pselM (i :: t) (i :: t) S))
          (split.pselM rest rest S)) ln c ((t.length + 1 + 1) * K)) :=
      rowsLen_evalPC _ _ ln c _
        (elim.rowsLen_mapRowsO _ _ _ (split.rowsLen_pselM rest S rest))
    have hYr : elim.rowsLen rest.length
        (evalPC (split.pswapM (split.pmatMul (split.pselM rest (i :: t) S)
          (pdeflW (i :: t) rest S))) ln c ((t.length + 1 + 1) * K)) :=
      rowsLen_evalPC _ _ ln c _
        (elim.rowsLen_mapRowsO _ _ _
          (elim.rowsLen_matMulO poly.polyOps _ _ rest.length
            (elim.headD_width rest.length _ (by rw [length_pdeflW]; exact hk)
              (rowsLen_pdeflW (i :: t) rest S hk))))
    have hX'r : elim.rowsLen rest.length (inertia.matScaleB
        (elim.minor (elim.selM (i :: t) (i :: t) (evalPC S ln c K)))
        (elim.selM rest rest (evalPC S ln c K))) :=
      inertia.rowsLen_scaleB _ _ _ (elim.rowsLen_selM _ _ _)
    have hY'r : elim.rowsLen rest.length (elim.matSwap
        (elim.matMul (elim.transposeM (elim.selM (i :: t) rest (evalPC S ln c K)))
          (evalPC (pdeflW (i :: t) rest S) ln c ((t.length + 1) * K)))) :=
      elim.rowsLen_matSwap _ _
        (elim.rowsLen_cast (elim.length_transposeM _ hWr (by rw [hWl]; exact hk))
          (elim.rowsLen_matMul _ _))
    show elim.matOneValue (evalPC (split.pmatAdd _ _) ln c ((t.length + 1 + 1) * K))
      (elim.matAdd _ (elim.matSwap _))
    refine elim.matOne_trans (evalPC_pmatAdd ln c _ _ _) ?_
    exact elim.matAdd_cong2 rest.length _ _ _ _ hXr hYr hX'r hY'r hX hY

/-- The evaluated once-cleared deflation of a symmetric evaluated
pencil at a pivot off the unit is symmetric at every point:
`inertia.deflMatP_symm` at the evaluated blocks and the evaluated
witness, carried across the evaluation's read. -/
theorem evalPC_pdeflP_symm {o : Nat} (S : split.PMat) (K : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hsh : pShapeAt S o K)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S ln c K)) (evalPC S ln c K))
    (hk0 : 0 < idx.length)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true)
    (hPnz : ¬ (elim.minor (elim.selM idx idx (evalPC S ln c K))).oneValue BPair.unit) :
    elim.matOneValue
      (elim.transposeM (evalPC (pdeflP idx rest S) ln c ((idx.length + 1) * K)))
      (evalPC (pdeflP idx rest S) ln c ((idx.length + 1) * K)) := by
  have hMsq : sqAt (evalPC S ln c K) o := evalPC_sqAt hsh ln c
  have hD := evalPC_pdeflP S K idx rest ln c hsh hMsym hk0 hidx hrest
  have hDsq : sqAt (evalPC (pdeflP idx rest S) ln c ((idx.length + 1) * K))
      rest.length :=
    evalPC_sqAt (pShape_pdeflP S o K idx rest hsh) ln c
  have hCwl : (evalPC (pdeflW idx rest S) ln c (idx.length * K)).length = idx.length :=
    (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
  have hCwr : rowsLen rest.length (evalPC (pdeflW idx rest S) ln c (idx.length * K)) :=
    rowsLen_evalPC _ _ ln c _ (rowsLen_pdeflW idx rest S hk0)
  have hPw := pdeflW_solve S K idx rest ln c (ent_ble hsh) hk0
  have hsym := inertia.deflMatP_symm (evalPC S ln c K) idx rest hk0 hMsq hMsym
    hidx hrest _ hCwl hCwr hPw hPnz
  have hBel : (selM idx rest (evalPC S ln c K)).length = idx.length :=
    length_selM _ _ _
  have hDefSq := inertia.sqAt_deflMatP
    (selM idx idx (evalPC S ln c K)) (selM idx rest (evalPC S ln c K))
    (selM rest rest (evalPC S ln c K))
    (evalPC (pdeflW idx rest S) ln c (idx.length * K)) rest.length
    (length_transposeM _ (rowsLen_selM _ _ _) (by rw [hBel]; exact hk0))
    (length_transposeM _ hCwr (by rw [hCwl]; exact hk0))
    (length_selM _ _ _) (rowsLen_selM _ _ _)
  have hT := transposeM_congrM rest.length _ _ (rowsLen_of_sqAt hDsq)
    (rowsLen_of_sqAt hDefSq) ((sqAt_len hDsq).trans (sqAt_len hDefSq).symm) hD
  exact matOne_trans hT (matOne_trans hsym (matOne_symm hD))

/-! The deflation cleared once at the pivot's determinant's
magnitude at a pivot whose determinant keeps its lower side or at
the mixed block (`lem:cellcount`): the trailing block at the minor's
swap joined to the correction, the once-cleared deflation's
memberwise swap collected at the swap's laws, its shape, its read as
that swap, its evaluation the evaluated blocks' once-cleared
deflation swapped, and the evaluated head's symmetry at a pivot off
the unit. -/

/-- The deflation cleared once at the pivot's determinant's
magnitude at a pivot whose determinant keeps its lower side or at
the mixed block: the trailing block at the minor's swap joined to the
coupling's transpose against the witness, `inertia.deflPO` at the
lower side (`lem:cellcount`'s collected display of the once-cleared
deflation's memberwise swap). -/
def pdeflM (idx rest : List Nat) (S : split.PMat) : split.PMat :=
  deflPO poly.polyOps poly.pnorm id split.padj true idx rest S

/-- The swapped deflation's row count is the trailing list's. -/
theorem length_pdeflM (idx rest : List Nat) (S : split.PMat) :
    (pdeflM idx rest S).length = rest.length :=
  length_deflPO poly.polyOps poly.pnorm id split.padj true idx rest S

/-- The swapped deflation's rows sit at the trailing list's count. -/
theorem rowsLen_pdeflM (idx rest : List Nat) (S : split.PMat) :
    elim.rowsLen rest.length (pdeflM idx rest S) :=
  rowsLen_deflPO poly.polyOps poly.pnorm id split.padj true idx rest S
    ((split.length_padj _).trans (split.length_pselM idx idx S))

/-- The swapped deflation's shape at a pivot of every order: the
trailing order at the clearing `(k + 1) K`, the swapped minor's cap
joined to the trailing block's and the correction's own. -/
theorem pShape_pdeflM (S : split.PMat) (o K : Nat) (idx rest : List Nat)
    (hS : pShapeAt S o K) :
    pShapeAt (pdeflM idx rest S) rest.length ((idx.length + 1) * K) :=
  pShape_deflS true S o K idx rest hS

/-- One row's swap of a rescaling is the rescaling at the swapped
scale. -/
private theorem prow_swap_scale (f : Poly) : ∀ r : List Poly,
    split.prowOneValue ((r.map (poly.mul f)).map poly.neg)
      (r.map (poly.mul (poly.neg f)))
  | [] => trivial
  | p :: r => ⟨poly.oneValue_symm (poly.neg_prod_left f p), prow_swap_scale f r⟩

/-- The swap of a rescaling is the rescaling at the swapped scale. -/
private theorem pmat_swap_scale (f : Poly) : ∀ X : split.PMat,
    split.pmatOneValue (split.pswapM (split.pscaleM f X))
      (split.pscaleM (poly.neg f) X)
  | [] => trivial
  | r :: X => ⟨prow_swap_scale f r, pmat_swap_scale f X⟩

/-- The memberwise swap of a sum is the swaps' sum, entry by entry. -/
private theorem pswap_add : ∀ A B : split.PMat,
    split.pmatOneValue (split.pswapM (split.pmatAdd A B))
      (split.pmatAdd (split.pswapM A) (split.pswapM B))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | r :: A, q :: B =>
    ⟨prow_swap_add r q, pswap_add A B⟩
where
  prow_swap_add : ∀ r q : List Poly,
      split.prowOneValue ((List.zipWith poly.polyOps.add r q).map poly.neg)
        (List.zipWith poly.polyOps.add (r.map poly.neg) (q.map poly.neg))
    | [], _ => trivial
    | _ :: _, [] => trivial
    | x :: r, y :: q =>
      ⟨poly.oneValue_of_eq (poly.neg_sum x y), prow_swap_add r q⟩

/-- The memberwise swap of a memberwise swap is the datum itself. -/
private theorem pswap_swap : ∀ A : split.PMat,
    split.pmatOneValue (split.pswapM (split.pswapM A)) A
  | [] => trivial
  | r :: A => ⟨prow_swap_swap r, pswap_swap A⟩
where
  prow_swap_swap : ∀ r : List Poly,
      split.prowOneValue ((r.map poly.neg).map poly.neg) r
    | [] => trivial
    | x :: r => ⟨poly.oneValue_of_eq (poly.neg_neg x), prow_swap_swap r⟩

/-- The swapped deflation reads the once-cleared deflation's
memberwise swap: the swap of the display's sum is the swaps' sum, the
scaling's swap the scaling at the swapped minor, and the correction's
swap's swap the correction (`lem:cellcount`'s collected display at
`def:ground`'s swap laws). -/
theorem pdeflM_swap (idx rest : List Nat) (S : split.PMat) :
    split.pmatOneValue (pdeflM idx rest S) (split.pswapM (pdeflP idx rest S)) := by
  have mtrans : ∀ {A B C : split.PMat}, split.pmatOneValue A B →
      split.pmatOneValue B C → split.pmatOneValue A C :=
    fun h1 h2 => ground.matched_trans
      (fun h1 h2 => ground.matched_trans poly.oneValue_trans h1 h2) h1 h2
  match idx with
  | [] =>
    show split.pmatOneValue (split.pscaleM (poly.neg _) _)
      (split.pswapM (split.pscaleM _ _))
    exact ground.matched_symm (fun h => ground.matched_symm poly.oneValue_symm h)
      (pmat_swap_scale _ _)
  | i :: t =>
    show split.pmatOneValue
      (split.pmatAdd (split.pscaleM (poly.neg _) _) _)
      (split.pswapM (split.pmatAdd (split.pscaleM _ _) (split.pswapM _)))
    refine mtrans ?_ (ground.matched_symm
      (fun h => ground.matched_symm poly.oneValue_symm h) (pswap_add _ _))
    refine elim.matAddO_congr poly.polyOps poly.polyRead
      (fun h1 h2 => poly.add_congr h1 h2) ?_ ?_
    · exact ground.matched_symm (fun h => ground.matched_symm poly.oneValue_symm h)
        (pmat_swap_scale _ _)
    · exact ground.matched_symm (fun h => ground.matched_symm poly.oneValue_symm h)
        (pswap_swap _)

/-- The swapped deflation's evaluation is the evaluated blocks'
once-cleared deflation's memberwise swap at the evaluated witness. -/
theorem evalPC_pdeflM {o : Nat} (S : split.PMat) (K : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hsh : pShapeAt S o K)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S ln c K)) (evalPC S ln c K))
    (hk0 : 0 < idx.length)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true) :
    elim.matOneValue
      (evalPC (pdeflM idx rest S) ln c ((idx.length + 1) * K))
      (elim.matSwap (inertia.deflMatP (elim.selM idx idx (evalPC S ln c K))
        (elim.selM idx rest (evalPC S ln c K))
        (elim.selM rest rest (evalPC S ln c K))
        (evalPC (pdeflW idx rest S) ln c (idx.length * K)))) :=
  elim.matOne_trans (evalPC_pcongr ln c _ (pdeflM_swap idx rest S))
    (elim.matOne_trans (evalPC_pswapM ln c _ _)
      (elim.matSwap_congr (evalPC_pdeflP S K idx rest ln c hsh hMsym hk0 hidx hrest)))

/-- The evaluated swapped deflation of a symmetric evaluated pencil
at a pivot off the unit is symmetric at every point: the once-cleared
deflation's symmetry (`evalPC_pdeflP_symm`) carried across the
swap's transpose (`inertia.transposeM_matSwap`). -/
theorem evalPC_pdeflM_symm {o : Nat} (S : split.PMat) (K : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hsh : pShapeAt S o K)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S ln c K)) (evalPC S ln c K))
    (hk0 : 0 < idx.length)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true)
    (hPnz : ¬ (elim.minor (elim.selM idx idx (evalPC S ln c K))).oneValue BPair.unit) :
    elim.matOneValue
      (elim.transposeM (evalPC (pdeflM idx rest S) ln c ((idx.length + 1) * K)))
      (evalPC (pdeflM idx rest S) ln c ((idx.length + 1) * K)) := by
  have hE : elim.matOneValue (evalPC (pdeflM idx rest S) ln c ((idx.length + 1) * K))
      (elim.matSwap (evalPC (pdeflP idx rest S) ln c ((idx.length + 1) * K))) :=
    elim.matOne_trans (evalPC_pcongr ln c _ (pdeflM_swap idx rest S))
      (evalPC_pswapM ln c _ _)
  have hP := evalPC_pdeflP_symm S K idx rest ln c hsh hMsym hk0 hidx hrest hPnz
  have hPsq : sqAt (evalPC (pdeflP idx rest S) ln c ((idx.length + 1) * K)) rest.length :=
    evalPC_sqAt (pShape_pdeflP S o K idx rest hsh) ln c
  have hMsq : sqAt (evalPC (pdeflM idx rest S) ln c ((idx.length + 1) * K)) rest.length :=
    evalPC_sqAt (pShape_pdeflM S o K idx rest hsh) ln c
  have hSsq := elim.sqAt_matSwap rest.length _ hPsq
  refine matOne_trans (transposeM_congrM rest.length _ _ (rowsLen_of_sqAt hMsq)
    (rowsLen_of_sqAt hSsq) ((sqAt_len hMsq).trans (sqAt_len hSsq).symm) hE) ?_
  refine matOne_trans (inertia.transposeM_matSwap rest.length _ (rowsLen_of_sqAt hPsq)) ?_
  exact matOne_trans (elim.matSwap_congr hP) (matOne_symm hE)

/-! `lem:cellcount`'s pivot cover: the avoidance's certificate at a
segment is a chain of subintervals meeting at shared endpoints, each
with a designated principal minor of order at most two whose
determinant keeps its side along the subinterval at `lem:stage`'s
priced side read (at a bound containing the subinterval), at order
two its leading entry so as well where the determinant sits on its
upper side, and beneath it the cleared deflation's own cover. -/

/-- The complement places at a stated order, the range's members off
the designated list. -/
def compl (idx : List Nat) (o : Nat) : List Nat :=
  (List.range o).filter (fun j => !(idx.contains j))

/-- The membership at the cons splits at the head comparison. -/
private theorem contains_cons (t : List Nat) (j a : Nat) :
    (a :: t).contains j = ((j == a) || t.contains j) := by
  cases hja : j == a with
  | true =>
    show List.elem j (a :: t) = _
    rw [List.elem, hja]
    rfl
  | false =>
    show List.elem j (a :: t) = _
    rw [List.elem, hja]
    rfl

/-- An occupied count reads the membership. -/
private theorem contains_of_countOf {j : Nat} : ∀ idx : List Nat,
    0 < ground.countOf j idx → idx.contains j = true
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: t, h => by
    rw [contains_cons t j a]
    match Nat.decEq j a with
    | isTrue he => rw [ground.eqBeqOf he]; rfl
    | isFalse hne =>
      rw [ground.neBeqOf hne]
      rw [ground.countOf_head_ne hne t] at h
      rw [contains_of_countOf t h]
      rfl

/-- A vacant count reads the membership's refusal. -/
private theorem contains_none {j : Nat} : ∀ idx : List Nat,
    ground.countOf j idx = 0 → idx.contains j = false
  | [], _ => rfl
  | a :: t, h => by
    rw [contains_cons t j a]
    match Nat.decEq j a with
    | isTrue he =>
      rw [he, ground.countOf_head a t] at h
      exact Nat.noConfusion h
    | isFalse hne =>
      rw [ground.neBeqOf hne]
      rw [ground.countOf_head_ne hne t] at h
      rw [contains_none t h]
      rfl

/-- The membership count over the enumeration is the places' own,
each distinct place inside the order counted once. -/
private theorem countBy_contains : ∀ (idx : List Nat) {o : Nat},
    ground.distinctList idx →
    (idx.all (fun i => Nat.blt i o)) = true →
    ground.countBy (fun j => idx.contains j) (List.range o)
      = idx.length
  | [], o, _, _ => by
    rw [countBy_congr (List.range o)
      (fun x _ => (rfl : ([] : List Nat).contains x = false))]
    exact countBy_false (List.range o)
  | a :: t, o, hd, hb => by
    have hsplit := ground.andSplitB
      (show (Nat.blt a o && t.all (fun i => Nat.blt i o)) = true
        from hb)
    have hat : ground.countOf a t = 0 := by
      have h1 : ground.countOf a t + 1 ≤ 1 := by
        rw [← ground.countOf_head a t]
        exact ground.distinctList_all hd a
      match Nat.eq_zero_or_pos (ground.countOf a t) with
      | Or.inl hz => exact hz
      | Or.inr hp =>
        exact absurd (Nat.lt_of_lt_of_le
          (Nat.succ_lt_succ hp) h1) (Nat.lt_irrefl _)
    have hstep : ground.countBy (fun j => (a :: t).contains j)
        (List.range o)
        = ground.countBy (fun j => (j == a) || t.contains j)
          (List.range o) :=
      countBy_congr (List.range o)
        (fun x _ => contains_cons t x a)
    rw [hstep,
      countBy_or (List.range o) (fun x _ hx => by
        rw [ground.beqEqOf hx]
        exact contains_none t hat),
      countBy_beq a (List.range o), ground.countOf_range a o,
      if_pos (ground.bltLt hsplit.1),
      countBy_contains t (ground.distinct_tail hd) hsplit.2,
      Nat.add_comm]
    rfl

/-- The designated places and their complement total the order. -/
theorem compl_length {o : Nat} {idx : List Nat}
    (hd : ground.distinctList idx)
    (hb : (idx.all (fun i => Nat.blt i o)) = true) :
    idx.length + (compl idx o).length = o := by
  rw [show compl idx o = (List.range o).filter
      (fun j => !(idx.contains j)) from rfl,
    length_filterBy (fun j => !(idx.contains j)) (List.range o),
    ← countBy_contains idx hd hb,
    countBy_split (fun j => idx.contains j) (List.range o),
    ground.length_range]

/-- The join with the complement is distinct. -/
theorem distinct_append_compl {o : Nat} {idx : List Nat}
    (hd : ground.distinctList idx) :
    ground.distinctList (idx ++ compl idx o) := by
  intro x _
  rw [ground.countOf_append x idx (compl idx o)]
  have hcompl : ground.countOf x (compl idx o)
      ≤ ground.countOf x (List.range o) := by
    rw [show compl idx o = (List.range o).filter
        (fun j => !(idx.contains j)) from rfl,
      ground.countOf_filter (fun j => !(idx.contains j)) x
        (List.range o)]
    cases !(idx.contains x) with
    | true => rw [if_pos rfl]; exact Nat.le_refl _
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h)]
      exact Nat.zero_le _
  have hrange : ground.countOf x (List.range o) ≤ 1 := by
    rw [ground.countOf_range x o]
    cases Nat.decLt x o with
    | isTrue h => rw [if_pos h]; exact Nat.le_refl 1
    | isFalse h => rw [if_neg h]; exact Nat.zero_le 1
  match Nat.eq_zero_or_pos (ground.countOf x idx) with
  | Or.inl hz =>
    rw [hz, Nat.zero_add]
    exact Nat.le_trans hcompl hrange
  | Or.inr hp =>
    have hone : ground.countOf x idx = 1 :=
      Nat.le_antisymm (ground.distinctList_all hd x) hp
    have hzc : ground.countOf x (compl idx o) = 0 := by
      rw [show compl idx o = (List.range o).filter
          (fun j => !(idx.contains j)) from rfl,
        ground.countOf_filter (fun j => !(idx.contains j)) x
          (List.range o),
        contains_of_countOf idx hp]
      rfl
    rw [hone, hzc]
    exact Nat.le_refl _

/-- One piece's frame: the designated places inside the order and
pairwise distinct; the places' permutation enters the leading
position at `elim.permM_orthL`'s identity reads, the transpose the
witness. -/
def pieceRead (o : Nat) (idx : List Nat) : Prop :=
  (idx.all (fun i => Nat.blt i o)) = true ∧ ground.distinctList idx

instance instCellcount2 (o : Nat) (idx : List Nat) :
    Decidable (pieceRead o idx) :=
  inferInstanceAs (Decidable (_ = _ ∧ _))

set_option genInjectivity false in
/-- The pivot cover: the chain's end, the order-nought deflation, and
one subinterval per designation — the piece's upper endpoint, the
designated places, the determinant's priced side certificate at a
stated bound (the lower side the mixed order-two row), at order two
with the determinant upper the leading entry's own, and beneath it
the cleared deflation's cover with the chain's remainder beside it,
the deflation cleared once at the pivot's determinant's magnitude,
the once-cleared deflation at a pivot whose determinant keeps its
upper side and its memberwise swap at a pivot keeping its lower side
or at the mixed block; and at a pivot whose coupling to the trailing
places reads the sum's unit the trailing block's own cover in the
deflation's place. -/
inductive Cover where
  | done : Cover
  | nought : Cover
  | one (b : CPair) (i : Nat) (up : Bool) (N D : BPair)
      (sub rest : Cover) : Cover
  | mixed (b : CPair) (i j : Nat) (N D : BPair)
      (sub rest : Cover) : Cover
  | twoUp (b : CPair) (i j : Nat) (N D : BPair)
      (eUp : Bool) (eN eD : BPair) (sub rest : Cover) : Cover
  | diag (b : CPair) (i : Nat) (up : Bool) (N D : BPair)
      (sub rest : Cover) : Cover

/-- The diagonal deflation nest at a stated bound: one upper read
at the leading place per level, the cleared deflations' priced side
reads down to the vacant order, one piece per level at the shared
segment. -/
def diagNest (top : CPair) (N D : ground.BPair) : Nat → Cover
  | 0 => .nought
  | d + 1 => .one top 0 true N D (diagNest top N D d) .done

/-- The diagonal pivot cover at a stated bound: the leading place's
lower read over the one piece with the deflation nest beneath it,
the chained one-place pieces of the pivot cover at a diagonal
pencil. -/
def diagCover (top : CPair) (N D : ground.BPair) (d : Nat) : Cover :=
  .one top 0 false N D (diagNest top N D d) .done

/-- The vacant-coupling nest at a stated bound: one upper read at
the leading place per level with the place's coupling to the
trailing places at the sum's unit, the trailing block's own cover
beneath it down to the vacant order, one piece per level at the
shared segment (`lem:cellcount`'s cover at a pivot whose coupling
reads the sum's unit). -/
def vacNest (top : CPair) (N D : ground.BPair) : Nat → Cover
  | 0 => .nought
  | d + 1 => .diag top 0 true N D (vacNest top N D d) .done

/-- The vacant-coupling pivot cover at a stated bound: the leading
place's lower read over the one piece with the vacant-coupling nest
beneath it, the cover of a pencil whose couplings off the leading
place read the sum's unit. -/
def vacCover (top : CPair) (N D : ground.BPair) (d : Nat) : Cover :=
  .one top 0 false N D (vacNest top N D d) .done

/-- The vacant-coupling read at a pivot: every trailing entry of the
pivot's row a unit tail (`lem:cellcount`'s pivot whose coupling to
the trailing places reads the sum's unit). -/
def coupVac (S : split.PMat) (o i : Nat) : Bool :=
  (compl [i] o).all (fun j =>
    decide (poly.unitTail (ground.getAt [] (ground.getAt [] S i) j)))

/-- The cover's read at a pencil, an order, a clearing and a
segment: the chain's end ties the endpoints, the order-nought
deflation reads its order, and a piece reads its chained endpoints,
its places' bounds with the permutation products, the designated
minor's priced side reads, and the two covers beneath and beside
it. -/
def coverRead (S : split.PMat) (o K : Nat) (lo hi : CPair) :
    Cover → Prop
  | .done => lo.oneValue hi
  | .nought => Nat.beq o 0 = true
  | .one b i up N D sub rest =>
      pieceRead o [i]
      ∧ (if up then
          stage.keepUpper (split.pminor (split.pselM [i] [i] S)) lo b N D
        else
          stage.keepLower (split.pminor (split.pselM [i] [i] S)) lo b N D)
      ∧ (if up then
          coverRead (pdeflP [i] (compl [i] o) S) (o - 1) (2 * K) lo b sub
        else
          coverRead (pdeflM [i] (compl [i] o) S) (o - 1) (2 * K) lo b sub)
      ∧ coverRead S o K b hi rest
  | .mixed b i j N D sub rest =>
      pieceRead o [i, j]
      ∧ stage.keepLower (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D
      ∧ coverRead (pdeflM [i, j] (compl [i, j] o) S) (o - 2) (3 * K) lo b sub
      ∧ coverRead S o K b hi rest
  | .twoUp b i j N D eUp eN eD sub rest =>
      pieceRead o [i, j]
      ∧ stage.keepUpper (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D
      ∧ (if eUp then
          stage.keepUpper (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD
        else
          stage.keepLower (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD)
      ∧ coverRead (pdeflP [i, j] (compl [i, j] o) S) (o - 2) (3 * K) lo b sub
      ∧ coverRead S o K b hi rest
  | .diag b i up N D sub rest =>
      pieceRead o [i]
      ∧ (if up then
          stage.keepUpper (split.pminor (split.pselM [i] [i] S)) lo b N D
        else
          stage.keepLower (split.pminor (split.pselM [i] [i] S)) lo b N D)
      ∧ coupVac S o i = true
      ∧ coverRead (split.pselM (compl [i] o) (compl [i] o) S) (o - 1) K lo b sub
      ∧ coverRead S o K b hi rest

/-- The cover read's decision, one arm per constructor with the
chain's two covers decided beneath, a side read decided at its own
guard. -/
instance decCoverRead (S : split.PMat) (o K : Nat) (lo hi : CPair) :
    ∀ cov : Cover, Decidable (coverRead S o K lo hi cov)
  | .done => inferInstanceAs (Decidable (lo.oneValue hi))
  | .nought => inferInstanceAs (Decidable (Nat.beq o 0 = true))
  | .one b i up N D sub rest =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead o [i])))
      (@instDecidableAnd _ _
        (match up with
          | true => inferInstanceAs (Decidable (stage.keepUpper
              (split.pminor (split.pselM [i] [i] S)) lo b N D))
          | false => inferInstanceAs (Decidable (stage.keepLower
              (split.pminor (split.pselM [i] [i] S)) lo b N D)))
        (@instDecidableAnd _ _
          (match up with
            | true => decCoverRead (pdeflP [i] (compl [i] o) S) (o - 1) (2 * K)
                lo b sub
            | false => decCoverRead (pdeflM [i] (compl [i] o) S) (o - 1) (2 * K)
                lo b sub)
          (decCoverRead S o K b hi rest)))
  | .mixed b i j N D sub rest =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead o [i, j])))
      (@instDecidableAnd _ _
        (inferInstanceAs (Decidable (stage.keepLower
          (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)))
        (@instDecidableAnd _ _
          (decCoverRead (pdeflM [i, j] (compl [i, j] o) S) (o - 2) (3 * K)
            lo b sub)
          (decCoverRead S o K b hi rest)))
  | .twoUp b i j N D eUp eN eD sub rest =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead o [i, j])))
      (@instDecidableAnd _ _
        (inferInstanceAs (Decidable (stage.keepUpper
          (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)))
        (@instDecidableAnd _ _
          (match eUp with
            | true => inferInstanceAs (Decidable (stage.keepUpper
                (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD))
            | false => inferInstanceAs (Decidable (stage.keepLower
                (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD)))
          (@instDecidableAnd _ _
            (decCoverRead (pdeflP [i, j] (compl [i, j] o) S) (o - 2) (3 * K)
              lo b sub)
            (decCoverRead S o K b hi rest))))
  | .diag b i up N D sub rest =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead o [i])))
      (@instDecidableAnd _ _
        (match up with
          | true => inferInstanceAs (Decidable (stage.keepUpper
              (split.pminor (split.pselM [i] [i] S)) lo b N D))
          | false => inferInstanceAs (Decidable (stage.keepLower
              (split.pminor (split.pselM [i] [i] S)) lo b N D)))
        (@instDecidableAnd _ _
          (instDecidableEqBool _ _)
          (@instDecidableAnd _ _
            (decCoverRead (split.pselM (compl [i] o) (compl [i] o) S) (o - 1) K
              lo b sub)
            (decCoverRead S o K b hi rest))))

/-! The cover's proof tier: the list and matrix joins' class reads,
the selection's passage through the cleared evaluation, the
clearing power's shift, the composite order's totality and
transitivity, and the block table's side reads. -/

/-- A filtered family keeps a fold read every member passes. -/
private theorem all_filter (P Q : Nat → Bool) :
    ∀ l : List Nat, l.all Q = true → (l.filter P).all Q = true
  | [], _ => rfl
  | a :: t, h => by
    have hs := ground.andSplitB (show (Q a && t.all Q) = true from h)
    cases hp : P a with
    | true =>
      rw [ground.filter_cons_true hp]
      show (Q a && (t.filter P).all Q) = true
      rw [hs.1, all_filter P Q t hs.2]
      rfl
    | false =>
      rw [ground.filter_cons_false hp]
      exact all_filter P Q t hs.2

/-- The key range sits inside its own order. -/
private theorem all_range (o : Nat) :
    ((List.range o).all (fun j => Nat.blt j o)) = true := by
  refine ground.all_of_getAt (0 : Nat) _ _ (fun k hk => ?_)
  rw [ground.length_range] at hk
  rw [ground.getAt_range o k hk]
  exact ground.ltBlt hk

/-- The keys' complement lies inside the order. -/
theorem all_compl (idx : List Nat) (o : Nat) :
    ((compl idx o).all (fun j => Nat.blt j o)) = true :=
  all_filter _ _ (List.range o) (all_range o)

/-- The lower side at the polynomial's own clearing carries to
every higher clearing power. -/
theorem sideDown_shift (p : Poly) (l : BPair) (c : Pos) (K : Nat)
    (hp : p.length ≤ K + 1)
    (h : poly.evalClear p l c (p.length - 1) < BPair.unit) :
    poly.evalClear p l c K < BPair.unit := by
  have hsw : BPair.unit < (poly.evalClear p l c (p.length - 1)).swap :=
    ground.ltB_swap h
  have hmul : BPair.unit
      < ground.bpow (BPair.ofPos c) (K - (p.length - 1))
        * (poly.evalClear p l c (p.length - 1)).swap :=
    ground.unitLtMul
      (ground.unitLtBpow (ground.unitLtOfPos c) _) hsw
  have heq : ground.bpow (BPair.ofPos c) (K - (p.length - 1))
        * (poly.evalClear p l c (p.length - 1)).swap
      = (ground.bpow (BPair.ofPos c) (K - (p.length - 1))
        * poly.evalClear p l c (p.length - 1)).swap := rfl
  rw [heq] at hmul
  have hFs : BPair.unit < (poly.evalClear p l c K).swap :=
    BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm
        (ground.swap_congr
          (poly.evalClear_pow p l c K (p.length - 1) (ground.lePredSucc p.length)
            (Nat.pred_le_pred hp))))
      hmul
  exact ground.ltB_swap (x := BPair.unit)
    (y := (poly.evalClear p l c K).swap) hFs

/-- The composite point's lower side at its stated representative is
the cleared evaluation's at the polynomial's own clearing. -/
theorem sideDown_rep (p : Poly) (l : BPair) (c : Pos)
    (h : stage.evalC p ⟨l, c⟩ < stage.unitC) :
    poly.evalClear p l c (p.length - 1) < BPair.unit := by
  have hsw : ∀ v : CPair, v < stage.unitC →
      stage.unitC < CPair.swap v := by
    intro v hv
    obtain ⟨vn, vc⟩ := v
    exact ground.ltB_swap (x := vn.scale Pos.one)
      (y := BPair.unit.scale vc) hv
  have h3 : stage.unitC
      < (⟨(poly.evalClear p l c (p.length - 1)).swap,
          ground.Pos.pow c (p.length - 1)⟩ : CPair) :=
    CPair.lt_congr (CPair.oneValue_refl _)
      (CPair.swap_congr (stage.evalC_evalClear p l c)) (hsw _ h)
  exact ground.ltB_swap ((stage.unitC_lt_num _ _).mp h3)

/-- The symmetric pencil's cleared evaluation keeps the entrywise
symmetry at every point (`split.pSymAt` read through the
evaluation), at the shape's two count reads. -/
theorem evalPC_symAt (S : split.PMat) (o K : Nat) (x : BPair)
    (c : Pos) (hSl : S.length = o) (hSr : elim.rowsLen o S)
    (hsym : split.pSymAt S o) :
    elim.matOneValue (evalPC S x c K)
      (elim.transposeM (evalPC S x c K)) := by
  have hEl : (evalPC S x c K).length = o :=
    (length_evalPC S x c K).trans hSl
  have hEr : elim.rowsLen o (evalPC S x c K) :=
    rowsLen_evalPC o S x c K hSr
  have hTl : (elim.transposeM (evalPC S x c K)).length = o :=
    elim.transposeLen _ hEr hEl
  have hTr : elim.rowsLen o (elim.transposeM (evalPC S x c K)) := by
    have h0 := elim.rowsLen_transposeM (evalPC S x c K)
    rw [hEl] at h0
    exact h0
  refine elim.matOne_of_entries _ _ o hEl hEr hTl hTr ?_
  intro i j hi hj
  rw [elim.getAt_transposeM BPair.unit _ hEr i j hi
      (by rw [hEl]; exact hj),
    getAt_evalPC x c K S i j, getAt_evalPC x c K S j i]
  exact poly.evalClear_congr (elim.symAtO_at hsym i j hi hj) x c K

/-- The cleared evaluations at two representatives of one composite
point: each weighted by the other's clearing power, one value —
the homogeneity principle at the shared clearing. -/
private theorem evalClear_pointOne (p : Poly) (K : Nat)
    (hp : p.length ≤ K + 1) (xn : BPair) (xc : Pos) (yn : BPair)
    (yc : Pos) (h : CPair.oneValue ⟨xn, xc⟩ ⟨yn, yc⟩) :
    (ground.bpow (BPair.ofPos yc) K
        * poly.evalClear p xn xc K).oneValue
      (ground.bpow (BPair.ofPos xc) K
        * poly.evalClear p yn yc K) := by
  have hLK : p.length - 1 ≤ K := Nat.pred_le_pred hp
  have hKL : (K - (p.length - 1)) + (p.length - 1) = K :=
    ground.subJoin (Nat.zero_le (p.length - 1)) hLK
  have hXY : (⟨poly.evalClear p xn xc (p.length - 1),
        ground.Pos.pow xc (p.length - 1)⟩ : CPair).oneValue
      ⟨poly.evalClear p yn yc (p.length - 1),
        ground.Pos.pow yc (p.length - 1)⟩ :=
    CPair.oneValue_trans
      (CPair.oneValue_symm (stage.evalC_evalClear p xn xc))
      (CPair.oneValue_trans (stage.evalC_point_congr p h)
        (stage.evalC_evalClear p yn yc))
  have hXY' : ((poly.evalClear p xn xc (p.length - 1)).scale
        (ground.Pos.pow yc (p.length - 1))).oneValue
      ((poly.evalClear p yn yc (p.length - 1)).scale
        (ground.Pos.pow xc (p.length - 1))) := hXY
  have hL : (ground.bpow (BPair.ofPos yc) (p.length - 1)
        * poly.evalClear p xn xc (p.length - 1)).oneValue
      (ground.bpow (BPair.ofPos xc) (p.length - 1)
        * poly.evalClear p yn yc (p.length - 1)) :=
    BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_symm (ground.ofPos_pow yc (p.length - 1)))
        (BPair.oneValue_refl _))
      (BPair.oneValue_trans
        (BPair.ofPos_scale (ground.Pos.pow yc (p.length - 1)) _)
        (BPair.oneValue_trans hXY'
          (BPair.oneValue_trans
            (BPair.oneValue_symm
              (BPair.ofPos_scale (ground.Pos.pow xc (p.length - 1)) _))
            (BPair.mul_congr
              (ground.ofPos_pow xc (p.length - 1))
              (BPair.oneValue_refl _)))))
  have hsplit : ∀ w : Pos, (ground.bpow (BPair.ofPos w) K).oneValue
      (ground.bpow (BPair.ofPos w) (K - (p.length - 1))
        * ground.bpow (BPair.ofPos w) (p.length - 1)) := by
    intro w
    have hb := ground.bpow_add (BPair.ofPos w) (K - (p.length - 1))
      (p.length - 1)
    rw [hKL] at hb
    exact hb
  refine BPair.oneValue_trans
    (BPair.mul_congr (hsplit yc)
      (poly.evalClear_pow p xn xc K (p.length - 1) (ground.lePredSucc p.length) hLK)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (ground.BPair.mul_mul_mul_comm _ _ _ _)) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _) hL) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (congrArg
      (fun z => z * (ground.bpow (BPair.ofPos xc) (p.length - 1)
        * poly.evalClear p yn yc (p.length - 1)))
      (BPair.mul_comm (ground.bpow (BPair.ofPos yc)
          (K - (p.length - 1)))
        (ground.bpow (BPair.ofPos xc) (K - (p.length - 1)))))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (ground.BPair.mul_mul_mul_comm _ _ _ _).symm) ?_
  exact BPair.mul_congr (BPair.oneValue_symm (hsplit xc))
    (BPair.oneValue_symm
      (poly.evalClear_pow p yn yc K (p.length - 1) (ground.lePredSucc p.length) hLK))

/-- The cleared evaluations at two representatives of one composite
point, the matrix read at the mirrored positive scalings. -/
private theorem evalPC_pointOne {o : Nat} (S : split.PMat) (K : Nat)
    (hlen : S.length = o) (hrows : elim.rowsLen o S)
    (hdeg : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1)
    (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos)
    (h : CPair.oneValue ⟨xn, xc⟩ ⟨yn, yc⟩) :
    elim.matOneValue
      (inertia.matScaleB (ground.bpow (BPair.ofPos yc) K)
        (evalPC S xn xc K))
      (inertia.matScaleB (ground.bpow (BPair.ofPos xc) K)
        (evalPC S yn yc K)) := by
  have hXl : (evalPC S xn xc K).length = o :=
    (length_evalPC S xn xc K).trans hlen
  have hYl : (evalPC S yn yc K).length = o :=
    (length_evalPC S yn yc K).trans hlen
  have hXr : elim.rowsLen o (evalPC S xn xc K) :=
    rowsLen_evalPC o S xn xc K hrows
  have hYr : elim.rowsLen o (evalPC S yn yc K) :=
    rowsLen_evalPC o S yn yc K hrows
  refine elim.matOne_getAt _ _
    (by rw [inertia.length_scaleB, inertia.length_scaleB, hXl, hYl]) ?_
  intro i hi
  rw [inertia.length_scaleB, hXl] at hi
  have hrL : (ground.getAt ([] : List BPair)
      (inertia.matScaleB (ground.bpow (BPair.ofPos yc) K)
        (evalPC S xn xc K)) i).length = o :=
    elim.rowsLen_getAt _ i
      (inertia.rowsLen_scaleB _ o _ hXr)
      (by rw [inertia.length_scaleB, hXl]; exact hi)
  have hrR : (ground.getAt ([] : List BPair)
      (inertia.matScaleB (ground.bpow (BPair.ofPos xc) K)
        (evalPC S yn yc K)) i).length = o :=
    elim.rowsLen_getAt _ i
      (inertia.rowsLen_scaleB _ o _ hYr)
      (by rw [inertia.length_scaleB, hYl]; exact hi)
  refine poly.oneValue_of_entries _ _ (hrL.trans hrR.symm) ?_
  intro j hj
  rw [hrL] at hj
  rw [inertia.entry_scaleB _ (evalPC S xn xc K) o hXr i j (by rw [hXl]; exact hi) hj,
    inertia.entry_scaleB _ (evalPC S yn yc K) o hYr i j (by rw [hYl]; exact hi) hj,
    getAt_evalPC xn xc K S i j, getAt_evalPC yn yc K S i j]
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans
      (evalClear_pointOne _ K (hdeg i j) xn xc yn yc h)
      (BPair.oneValue_symm (BPair.norm_oneValue _)))

/-- Two splits at two representatives of one composite point read
one count: the two cleared evaluations differ by the mirrored
positive scalings. -/
private theorem rev_point {o : Nat} (S : split.PMat) (K : Nat)
    (hlen : S.length = o) (hrows : elim.rowsLen o S)
    (hdeg : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1)
    (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos)
    (h : CPair.oneValue ⟨xn, xc⟩ ⟨yn, yc⟩)
    (spx spy : inertia.Split o)
    (hx : inertia.splitRead (evalPC S xn xc K) spx)
    (hy : inertia.splitRead (evalPC S yn yc K) spy) :
    inertia.revAt spx = inertia.revAt spy := by
  have hWy : BPair.unit < ground.bpow (BPair.ofPos yc) K :=
    ground.unitLtBpow (ground.unitLtOfPos yc) K
  have hWx : BPair.unit < ground.bpow (BPair.ofPos xc) K :=
    ground.unitLtBpow (ground.unitLtOfPos xc) K
  have hsc : inertia.splitRead
      (inertia.matScaleB (ground.bpow (BPair.ofPos yc) K)
        (evalPC S xn xc K))
      (inertia.scaleSplit (ground.bpow (BPair.ofPos yc) K) spx) :=
    inertia.scaleSplit_read _ (ground.offOfUnitLt hWy) _ spx hx
  have hsq' : elim.sqAt (inertia.matScaleB (ground.bpow (BPair.ofPos xc) K)
      (evalPC S yn yc K)) o :=
    elim.sqAt_of
      (by rw [inertia.length_scaleB, length_evalPC, hlen])
      (inertia.rowsLen_scaleB _ o _
        (rowsLen_evalPC o S yn yc K hrows))
  have hsc' := inertia.splitRead_congr _ _ hsq'
    (evalPC_pointOne S K hlen hrows hdeg xn xc yn yc h) _ hsc
  have hA := inertia.rev_scale (ground.bpow (BPair.ofPos yc) K) hWy
    (evalPC S xn xc K) spx _ hx hsc
  have hB := inertia.rev_scale (ground.bpow (BPair.ofPos xc) K) hWx
    (evalPC S yn yc K) spy _ hy hsc'
  exact hA.symm.trans hB

/-- A fold of sums over a key range keeps the unit tail at
unit-tailed summands and seed. -/
private theorem foldRange_unit (f : Nat → Poly)
    (hf : ∀ l, poly.unitTail (f l)) :
    ∀ (n : Nat) (acc : Poly), poly.unitTail acc →
      poly.unitTail ((List.range n).foldl (fun s l => poly.add s (f l)) acc)
  | 0, _, hacc => hacc
  | n + 1, acc, hacc => by
    rw [ground.range_cons n,
      show ((0 : Nat) :: (List.range n).map (fun j => j + 1)).foldl
          (fun s l => poly.add s (f l)) acc
        = ((List.range n).map (fun j => j + 1)).foldl
          (fun s l => poly.add s (f l)) (poly.add acc (f 0)) from rfl,
      ground.foldl_map (fun j => j + 1) (fun s l => poly.add s (f l))
        (List.range n) (poly.add acc (f 0))]
    exact foldRange_unit (fun l => f (l + 1)) (fun l => hf (l + 1)) n
      (poly.add acc (f 0)) (poly.unitTail_sum hacc (hf 0))

/-- One row's entrywise map keeps the unit tail wherever its own
step does. -/
private theorem mapRow_unit (f : Poly → Poly)
    (hf : ∀ p, poly.unitTail p → poly.unitTail (f p)) :
    ∀ (s : List Poly),
      (∀ k, poly.unitTail (ground.getAt ([] : Poly) s k)) →
      ∀ k, poly.unitTail (ground.getAt ([] : Poly) (s.map f) k)
  | [], _, _ => trivial
  | p :: _, h, 0 => hf p (h 0)
  | _ :: s, h, k + 1 => mapRow_unit f hf s (fun l => h (l + 1)) k

/-- An entrywise map keeps the unit tail wherever its own step
does, at every key of every row. -/
private theorem mapRows_unit (f : Poly → Poly)
    (hf : ∀ p, poly.unitTail p → poly.unitTail (f p)) :
    ∀ (X : split.PMat), (∀ r k, poly.unitTail (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) X r) k)) →
      ∀ r k, poly.unitTail (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (X.map (fun s => s.map f)) r) k)
  | [], _, _, _ => trivial
  | s :: _, h, 0, k => mapRow_unit f hf s (fun l => h 0 l) k
  | _ :: X, h, r + 1, k =>
    mapRows_unit f hf X (fun p l => h (p + 1) l) r k

/-- The polynomial product's entries carry a unit-tailed first
factor: every term of the row-against-column fold keeps the
factor's own tail. -/
private theorem pmatMul_unitL (a b : split.PMat)
    (ha : ∀ p q, poly.unitTail (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) a p) q)) :
    ∀ p q, poly.unitTail (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (split.pmatMul a b) p) q) := by
  intro p q
  match Nat.lt_or_ge p a.length with
  | Or.inr h =>
    rw [ground.getAt_over ([] : List Poly) _ p
      (by rw [show (split.pmatMul a b).length = a.length from
        elim.length_matMulO poly.polyOps a b]; exact h)]
    exact trivial
  | Or.inl h =>
    match Nat.lt_or_ge q (b.headD ([] : List Poly)).length with
    | Or.inr h2 =>
      rw [ground.getAt_over ([] : Poly) _ q
        (by rw [rowLen_pmatMul a b p h]; exact h2)]
      exact trivial
    | Or.inl h2 =>
      rw [show ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly) (split.pmatMul a b) p) q = _ from
        elim.getAt_matMulO poly.polyOps a b p q h h2]
      exact foldRange_unit _
        (fun l => poly.of_unitTail_mul (Or.inl (ha p l))) _ [] trivial

/-- An entrywise sum against a unit-tailed summand reads its other
summand, row by row at a shared width. -/
private theorem row_add_unit : ∀ a b : List Poly,
    a.length = b.length →
    (∀ k, poly.unitTail (ground.getAt ([] : Poly) b k)) →
    split.prowOneValue (List.zipWith poly.add a b) a
  | [], [], _, _ => trivial
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl
  | p :: a, _ :: b, hl, h =>
    ⟨poly.add_unitTail p (h 0),
     row_add_unit a b (Nat.succ.inj hl) (fun k => h (k + 1))⟩

/-- An entrywise sum against a unit-tailed matrix reads its other
summand. -/
private theorem pmatAdd_unit : ∀ A B : split.PMat,
    A.length = B.length →
    (∀ r, r < A.length → (ground.getAt ([] : List Poly) A r).length
      = (ground.getAt ([] : List Poly) B r).length) →
    (∀ r k, poly.unitTail (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) B r) k)) →
    split.pmatOneValue (split.pmatAdd A B) A
  | [], [], _, _, _ => trivial
  | [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, [], hl, _, _ => nomatch hl
  | a :: A, b :: B, hl, hr, h =>
    ⟨row_add_unit a b (hr 0 (Nat.succ_pos _)) (fun k => h 0 k),
     pmatAdd_unit A B (Nat.succ.inj hl)
       (fun r hrr => hr (r + 1) (Nat.succ_lt_succ hrr))
       (fun r k => h (r + 1) k)⟩

/-- The once-cleared order-one deflation at value-unit couplings:
with the pivot's row reading the sum's unit against every trailing
key, the correction term's every entry keeps that tail — one
unit-tailed factor carrying the whole product — and the deflation
reads the pivot entry on the trailing block, a key beyond the datum
reading the vacant list. -/
theorem pdeflP_offC (S : split.PMat) (i : Nat) (rest : List Nat)
    (hoffR : ∀ k, k < rest.length → poly.unitTail
      (ground.getAt [] (ground.getAt [] S (ground.getAt 0 rest k)) i)) :
    split.pmatOneValue (pdeflP [i] rest S)
      (split.pscaleM (ground.getAt [] (ground.getAt [] S i) i)
        (split.pselM rest rest S)) := by
  have hBpl : (split.pselM [i] rest S).length = ([i] : List Nat).length :=
    split.length_pselM _ _ _
  have hBpr : elim.rowsLen rest.length (split.pselM [i] rest S) :=
    split.rowsLen_pselM _ _ _
  have hhdBp : ((split.pselM [i] rest S).headD ([] : List Poly)).length
      = rest.length :=
    elim.headD_width rest.length _
      (by rw [hBpl]; exact Nat.one_pos) hBpr
  have hWl : (split.pmatMul (split.padj (split.pselM [i] [i] S))
      (split.pselM [i] rest S)).length = ([i] : List Nat).length :=
    (elim.length_matMulO poly.polyOps _ _).trans
      ((split.length_padj _).trans (split.length_pselM _ _ _))
  have hWr : elim.rowsLen rest.length
      (split.pmatMul (split.padj (split.pselM [i] [i] S))
        (split.pselM [i] rest S)) := by
    rw [← hhdBp]
    exact elim.rowsLen_matMulO poly.polyOps _ _ _ rfl
  have hhdW : ((split.pmatMul (split.padj (split.pselM [i] [i] S))
      (split.pselM [i] rest S)).headD ([] : List Poly)).length = rest.length :=
    elim.headD_width rest.length _
      (by rw [hWl]; exact Nat.one_pos) hWr
  have hZr : elim.rowsLen rest.length
      (split.pmatMul (split.pselM rest [i] S)
        (split.pmatMul (split.padj (split.pselM [i] [i] S))
          (split.pselM [i] rest S))) := by
    rw [← hhdW]
    exact elim.rowsLen_matMulO poly.polyOps _ _ _ rfl
  have hAl : (split.pscaleM (split.pminor (split.pselM [i] [i] S))
      (split.pselM rest rest S)).length = rest.length :=
    (ground.length_map _ _).trans (split.length_pselM rest rest S)
  have hAr : elim.rowsLen rest.length
      (split.pscaleM (split.pminor (split.pselM [i] [i] S))
        (split.pselM rest rest S)) :=
    elim.rowsLen_mapRowsO _ _ _ (split.rowsLen_pselM _ _ _)
  have hBl : (split.pswapM (split.pmatMul (split.pselM rest [i] S)
      (split.pmatMul (split.padj (split.pselM [i] [i] S))
        (split.pselM [i] rest S)))).length = rest.length :=
    (ground.length_map _ _).trans
      ((elim.length_matMulO poly.polyOps _ _).trans (split.length_pselM rest [i] S))
  have hBr : elim.rowsLen rest.length (split.pswapM (split.pmatMul (split.pselM rest [i] S)
      (split.pmatMul (split.padj (split.pselM [i] [i] S))
        (split.pselM [i] rest S)))) :=
    elim.rowsLen_mapRowsO _ _ _ hZr
  have hSelR : ∀ p q, poly.unitTail (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (split.pselM rest [i] S) p) q) := by
    intro p q
    match Nat.lt_or_ge p rest.length with
    | Or.inr hp =>
      rw [ground.getAt_over ([] : List Poly) _ p
        (by rw [split.length_pselM]; exact hp)]
      exact trivial
    | Or.inl hp =>
      match q with
      | 0 =>
        rw [split.getAt_pselM rest [i] S p 0 hp Nat.one_pos]
        exact hoffR p hp
      | q + 1 =>
        rw [ground.getAt_over ([] : Poly) _ (q + 1)
          (by rw [elim.rowsLen_getAt _ p (split.rowsLen_pselM [i] S rest)
                (by rw [split.length_pselM]; exact hp)]
              exact Nat.succ_le_succ (Nat.zero_le q))]
        exact trivial
  have hunit : ∀ r k, poly.unitTail (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (split.pswapM (split.pmatMul (split.pselM rest [i] S)
        (split.pmatMul (split.padj (split.pselM [i] [i] S))
          (split.pselM [i] rest S)))) r) k) :=
    mapRows_unit poly.neg (fun _ hp => poly.unitTail_swapMap _ hp) _
      (pmatMul_unitL _ _ hSelR)
  show split.pmatOneValue
    (split.pmatAdd
      (split.pscaleM (split.pminor (split.pselM [i] [i] S)) (split.pselM rest rest S))
      (split.pswapM (split.pmatMul (split.pselM rest [i] S)
        (split.pmatMul (split.padj (split.pselM [i] [i] S)) (split.pselM [i] rest S)))))
    (split.pscaleM (split.pminor (split.pselM [i] [i] S)) (split.pselM rest rest S))
  refine pmatAdd_unit _ _ (hAl.trans hBl.symm) (fun r hr => ?_) hunit
  rw [hAl] at hr
  rw [elim.rowsLen_getAt _ r hAr (by rw [hAl]; exact hr),
    elim.rowsLen_getAt _ r hBr (by rw [hBl]; exact hr)]

/-- The swapped order-one deflation at value-unit couplings reads
the pivot entry's swap on the trailing block (`pdeflP_offC` at the
memberwise swap). -/
theorem pdeflM_offC (S : split.PMat) (i : Nat) (rest : List Nat)
    (hoffR : ∀ k, k < rest.length → poly.unitTail
      (ground.getAt [] (ground.getAt [] S (ground.getAt 0 rest k)) i)) :
    split.pmatOneValue (pdeflM [i] rest S)
      (split.pscaleM (poly.neg (ground.getAt [] (ground.getAt [] S i) i))
        (split.pselM rest rest S)) :=
  ground.matched_trans (fun h1 h2 => ground.matched_trans poly.oneValue_trans h1 h2)
    (pdeflM_swap [i] rest S)
    (ground.matched_trans (fun h1 h2 => ground.matched_trans poly.oneValue_trans h1 h2)
      (elim.matSwapO_congr poly.polyOps poly.polyRead (fun h => poly.neg_congr h)
        (pdeflP_offC S i rest hoffR))
      (pmat_swap_scale _ _))

/-- The order-one designated minor's evaluation is the evaluated
selected block's own. -/
theorem minor1_bridge (S : split.PMat) (K i : Nat) (xn : BPair)
    (xc : Pos) :
    (poly.evalClear (split.pminor (split.pselM [i] [i] S))
        xn xc K).oneValue
      (elim.minor (elim.selM [i] [i] (evalPC S xn xc K))) := by
  rw [selM_evalPC xn xc K S [i] [i]]
  exact BPair.oneValue_refl _

/-- The order-two designated minor's degree sits within the doubled
clearing power, the bundle's cap read. -/
private theorem pminor2_len {S : split.PMat} {o K : Nat}
    (hsh : pShapeAt S o K) (i0 i1 : Nat) :
    (split.pminor (split.pselM [i0, i1] [i0, i1] S)).length
      ≤ K + K + 1 :=
  deg_minorO_two poly.polyOps poly.pnorm id (fun p K => p.length ≤ K + 1)
    (fun x y hx hy => poly.add_len_le x y (K + K + 1) hx hy)
    (fun x y hx hy => poly.mul_len_le x y K K hx hy)
    (fun x h => by rw [show (poly.polyOps.swap x).length = x.length from
      poly.length_neg x]; exact h)
    (fun x h => by rw [poly.pnorm_length]; exact h)
    (fun _ h => h) (Nat.zero_le _) (ent_ble hsh) i0 i1

/-- The order-two designated minor's evaluation is the evaluated
selected block's own, at the doubled clearing power. -/
theorem minor2_bridge {S : split.PMat} {o K : Nat}
    (hsh : pShapeAt S o K) (i0 i1 : Nat) (xn : BPair) (xc : Pos) :
    (poly.evalClear (split.pminor (split.pselM [i0, i1] [i0, i1] S))
        xn xc (K + K)).oneValue
      (elim.minor
        (elim.selM [i0, i1] [i0, i1] (evalPC S xn xc K))) := by
  rw [selM_evalPC xn xc K S [i0, i1] [i0, i1]]
  have hL : (poly.evalClear (split.pminor
      (split.pselM [i0, i1] [i0, i1] S)) xn xc (K + K)).oneValue
      (poly.evalClear
          (ground.getAt ([] : Poly)
            (ground.getAt ([] : List Poly) S i0) i0) xn xc K
        * poly.evalClear
          (ground.getAt ([] : Poly)
            (ground.getAt ([] : List Poly) S i1) i1) xn xc K
      + (poly.evalClear
          (ground.getAt ([] : Poly)
            (ground.getAt ([] : List Poly) S i0) i1) xn xc K
        * poly.evalClear
          (ground.getAt ([] : Poly)
            (ground.getAt ([] : List Poly) S i1) i0)
          xn xc K).swap) := by
    show (poly.evalClear (poly.add (poly.pnorm (poly.mul
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i0)
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i1)))
      (poly.add (poly.neg (poly.pnorm (poly.mul
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i1)
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i0))))
        [])) xn xc (K + K)).oneValue _
    rw [poly.add_nil]
    exact BPair.oneValue_trans (evalClear_add _ _ xn xc (K + K))
      (BPair.add_congr
        (BPair.oneValue_trans
          (poly.evalClear_congr (poly.pnorm_oneValue _) xn xc (K + K))
          (evalClear_mul _ _ xn xc K K (ent_ble hsh i0 i0)
            (ent_ble hsh i1 i1)))
        (BPair.oneValue_trans (evalClear_neg _ xn xc (K + K))
          (ground.swap_congr
            (BPair.oneValue_trans
              (poly.evalClear_congr (poly.pnorm_oneValue _) xn xc (K + K))
              (evalClear_mul _ _ xn xc K K (ent_ble hsh i0 i1)
                (ent_ble hsh i1 i0))))))
  exact BPair.oneValue_trans hL
    (BPair.oneValue_symm (elim.minor_two _ _ _ _))

/-- One subinterval's addition at a pivot whose determinant keeps its
upper side: the count splits at the pivot's own split and the
once-cleared deflation's (`lem:cellcount`'s deflation cleared once,
`inertia.rev_placesP`), the positive factor fixing every count, the
deflation read across the evaluated blocks at the polynomial
adjugate's witness. -/
theorem piece_addP {o m : Nat} (S : split.PMat) (K KK : Nat)
    (idx : List Nat) (hpc : pieceRead o idx) (hsh : pShapeAt S o K)
    (hk0 : 0 < idx.length)
    (hm : (compl idx o).length = m)
    (hKK : KK = (idx.length + 1) * K)
    (xn : BPair) (xc : Pos)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S xn xc K))
      (evalPC S xn xc K))
    (hPpos : BPair.unit < elim.minor
      (elim.selM idx idx (evalPC S xn xc K)))
    (spx : inertia.Split o)
    (hx : inertia.splitRead (evalPC S xn xc K) spx)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (evalPC (pdeflP idx (compl idx o) S) xn xc KK) spD) :
    inertia.revAt spx
      = inertia.revAt (inertia.mkSplit idx.length
          (elim.selM idx idx (evalPC S xn xc K)))
        + inertia.revAt spD := by
  subst hKK
  have hidx := hpc.1
  have hdix := hpc.2
  have hMsq : elim.sqAt (evalPC S xn xc K) o := evalPC_sqAt hsh xn xc
  have hsgl : (idx ++ compl idx o).length = o := by
    rw [ground.length_append]
    exact compl_length hdix hidx
  have hPvsq : elim.sqAt (elim.selM idx idx (evalPC S xn xc K))
      idx.length :=
    elim.sqAt_of (elim.length_selM idx idx _) (elim.rowsLen_selM idx _ idx)
  have hPvsym : elim.matOneValue
      (elim.transposeM (elim.selM idx idx (evalPC S xn xc K)))
      (elim.selM idx idx (evalPC S xn xc K)) :=
    elim.transposeM_selM idx idx _ o hMsq hMsym hk0 hidx hidx
  have hPread := inertia.mkSplit_read idx.length _ hPvsq hPvsym
  obtain ⟨_, _, _, hQsq, _, hTBl, _, _⟩ :=
    pivotBlocks (evalPC S xn xc K) idx (compl idx o) o hMsq hMsym hk0 hidx
      (all_compl idx o)
  have hDefl := evalPC_pdeflP (o := o) S K idx (compl idx o) xn xc hsh hMsym
    hk0 hidx (all_compl idx o)
  have hPw := pdeflW_solve S K idx (compl idx o) xn xc (ent_ble hsh) hk0
  have hCwl : (evalPC (pdeflW idx (compl idx o) S) xn xc
      (idx.length * K)).length = idx.length :=
    (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
  have hCwr : elim.rowsLen (compl idx o).length
      (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K)) :=
    rowsLen_evalPC _ _ _ _ _ (rowsLen_pdeflW idx _ _ hk0)
  have hDsq := inertia.sqAt_deflMatP
    (elim.selM idx idx (evalPC S xn xc K))
    (elim.selM idx (compl idx o) (evalPC S xn xc K))
    (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
    (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K))
    (compl idx o).length hTBl
    (elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0))
    (elim.sqAt_len hQsq) (elim.rowsLen_of_sqAt hQsq)
  have hb : ((idx ++ compl idx o).all (fun i => Nat.blt i o)) = true := by
    rw [ground.all_append, hidx, all_compl idx o]
    rfl
  subst hm
  have hD' := inertia.splitRead_congr _ _ hDsq hDefl spD hD
  exact inertia.rev_placesP (evalPC S xn xc K) idx (compl idx o) hk0 hMsq hMsym
    hsgl (distinct_append_compl (o := o) hdix) hb _ hCwl hCwr hPw hPpos
    spx hx _ hPread spD hD'

/-- One subinterval's addition at a pivot whose determinant keeps its
lower side or at the mixed block: the count splits at the pivot's own
split and the swapped once-cleared deflation's (`lem:cellcount`'s
deflation cleared once at the determinant's magnitude,
`inertia.rev_placesM`), the positive factor fixing every count, the
deflation read across the evaluated blocks at the polynomial
adjugate's witness. -/
theorem piece_addM {o m : Nat} (S : split.PMat) (K KK : Nat)
    (idx : List Nat) (hpc : pieceRead o idx) (hsh : pShapeAt S o K)
    (hk0 : 0 < idx.length)
    (hm : (compl idx o).length = m)
    (hKK : KK = (idx.length + 1) * K)
    (xn : BPair) (xc : Pos)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S xn xc K))
      (evalPC S xn xc K))
    (hPneg : elim.minor (elim.selM idx idx (evalPC S xn xc K)) < BPair.unit)
    (spx : inertia.Split o)
    (hx : inertia.splitRead (evalPC S xn xc K) spx)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (evalPC (pdeflM idx (compl idx o) S) xn xc KK) spD) :
    inertia.revAt spx
      = inertia.revAt (inertia.mkSplit idx.length
          (elim.selM idx idx (evalPC S xn xc K)))
        + inertia.revAt spD := by
  subst hKK
  have hidx := hpc.1
  have hdix := hpc.2
  have hMsq : elim.sqAt (evalPC S xn xc K) o := evalPC_sqAt hsh xn xc
  have hsgl : (idx ++ compl idx o).length = o := by
    rw [ground.length_append]
    exact compl_length hdix hidx
  have hPvsq : elim.sqAt (elim.selM idx idx (evalPC S xn xc K))
      idx.length :=
    elim.sqAt_of (elim.length_selM idx idx _) (elim.rowsLen_selM idx _ idx)
  have hPvsym : elim.matOneValue
      (elim.transposeM (elim.selM idx idx (evalPC S xn xc K)))
      (elim.selM idx idx (evalPC S xn xc K)) :=
    elim.transposeM_selM idx idx _ o hMsq hMsym hk0 hidx hidx
  have hPread := inertia.mkSplit_read idx.length _ hPvsq hPvsym
  obtain ⟨_, _, _, hQsq, _, hTBl, _, _⟩ :=
    pivotBlocks (evalPC S xn xc K) idx (compl idx o) o hMsq hMsym hk0 hidx
      (all_compl idx o)
  have hDefl := evalPC_pdeflM (o := o) S K idx (compl idx o) xn xc hsh hMsym
    hk0 hidx (all_compl idx o)
  have hPw := pdeflW_solve S K idx (compl idx o) xn xc (ent_ble hsh) hk0
  have hCwl : (evalPC (pdeflW idx (compl idx o) S) xn xc
      (idx.length * K)).length = idx.length :=
    (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
  have hCwr : elim.rowsLen (compl idx o).length
      (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K)) :=
    rowsLen_evalPC _ _ _ _ _ (rowsLen_pdeflW idx _ _ hk0)
  have hDsq := inertia.sqAt_deflMatP
    (elim.selM idx idx (evalPC S xn xc K))
    (elim.selM idx (compl idx o) (evalPC S xn xc K))
    (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
    (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K))
    (compl idx o).length hTBl
    (elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0))
    (elim.sqAt_len hQsq) (elim.rowsLen_of_sqAt hQsq)
  have hb : ((idx ++ compl idx o).all (fun i => Nat.blt i o)) = true := by
    rw [ground.all_append, hidx, all_compl idx o]
    rfl
  subst hm
  have hD' := inertia.splitRead_congr _ _ (elim.sqAt_matSwap _ _ hDsq) hDefl spD hD
  exact inertia.rev_placesM (evalPC S xn xc K) idx (compl idx o) hk0 hMsq hMsym
    hsgl (distinct_append_compl (o := o) hdix) hb _ hCwl hCwr hPw hPneg
    spx hx _ hPread spD hD'

/-- The vacant-coupling pivot's once-cleared deflation is the trailing
block at the pivot's determinant: the coupling reads the sum's unit,
so the deflation's correction term is vacant (`lem:cellcount`'s pivot
whose coupling to the trailing places reads the sum's unit,
`lem:inertia`'s display at a vacant coupling). -/
private theorem diag_defl {o : Nat} (S : split.PMat) (K : Nat)
    (i : Nat) (hpc : pieceRead o [i]) (hsh : pShapeAt S o K)
    (hoff : coupVac S o i = true)
    (xn : BPair) (xc : Pos)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S xn xc K))
      (evalPC S xn xc K)) :
    elim.matOneValue
      (inertia.deflMatP (elim.selM [i] [i] (evalPC S xn xc K))
        (elim.selM [i] (compl [i] o) (evalPC S xn xc K))
        (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K))
        (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K)))
      (inertia.matScaleB (elim.minor (elim.selM [i] [i] (evalPC S xn xc K)))
        (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K))) := by
  have hidx := hpc.1
  have hMsq : elim.sqAt (evalPC S xn xc K) o := evalPC_sqAt hsh xn xc
  have hk0 : 0 < ([i] : List Nat).length := Nat.succ_pos 0
  obtain ⟨_, _, _, hQsq, _, hTBl, _, _⟩ :=
    pivotBlocks (evalPC S xn xc K) [i] (compl [i] o) o hMsq hMsym hk0 hidx
      (all_compl [i] o)
  have hCwl : (evalPC (pdeflW [i] (compl [i] o) S) xn xc
      (([i] : List Nat).length * K)).length = ([i] : List Nat).length :=
    (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
  have hCwr : elim.rowsLen (compl [i] o).length
      (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K)) :=
    rowsLen_evalPC _ _ _ _ _ (rowsLen_pdeflW [i] _ _ hk0)
  have hCt : (elim.transposeM (evalPC (pdeflW [i] (compl [i] o) S) xn xc
      (([i] : List Nat).length * K))).length = (compl [i] o).length :=
    elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0)
  have hBnull : elim.matNull
      (elim.selM [i] (compl [i] o) (evalPC S xn xc K)) := by
    refine elim.matNull_of_getAt _ ?_
    intro p hp
    have hp1 : p < 1 := by
      rw [elim.length_selM] at hp
      exact hp
    have hp0 : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp1)
    subst hp0
    show poly.unitTail ((compl [i] o).map (fun j => ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (evalPC S xn xc K) i) j))
    refine poly.unitTail_map _ _ ?_
    intro j hj
    have hoff' : ((compl [i] o).all (fun j => decide (poly.unitTail
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i) j)))) = true :=
      hoff
    have h1 := ground.all_of_mem _ (compl [i] o) hoff' j hj
    have hut : poly.unitTail (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) j) :=
      of_decide_eq_true h1
    show (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (evalPC S xn xc K) i) j).oneValue
      BPair.unit
    rw [getAt_evalPC xn xc K S i j]
    exact BPair.oneValue_trans
      (poly.evalClear_congr
        (poly.unitTail_oneValue hut (show poly.unitTail ([] : Poly) from trivial))
        xn xc K)
      (BPair.oneValue_of_eq (poly.evalClear_nil xn xc K))
  have hBCnull : elim.matNull (elim.matMul
      (elim.transposeM (elim.selM [i] (compl [i] o) (evalPC S xn xc K)))
      (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K))) :=
    elim.matNull_mul_left _ _ (elim.matNull_transposeM _ hBnull)
  have hBCsq : elim.sqAt (elim.matMul
      (elim.transposeM (elim.selM [i] (compl [i] o) (evalPC S xn xc K)))
      (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K)))
      (compl [i] o).length :=
    elim.sqAt_of ((elim.length_matMul _ _).trans hTBl)
      (elim.rowsLen_cast hCt (elim.rowsLen_matMul _ _))
  delta inertia.deflMatP inertia.siteDatum
  exact elim.matAdd_nullR _ _
    (inertia.sqAt_scaleB _ _ _ hQsq)
    (elim.sqAt_matSwap _ _ hBCsq)
    (elim.matNull_matSwap _ hBCnull)

/-- One subinterval's addition at a pivot whose coupling to the
trailing places reads the sum's unit (`lem:cellcount`): the
once-cleared deflation reads the trailing block at the pivot's
determinant and its memberwise swap the block at the determinant's
swap, so the count splits at the pivot's own split and the trailing
block's own (`inertia.rev_placesP` and `inertia.rev_placesM` at the
deflation read as the weighted block, `inertia.scaleSplit_rev` the
positive weight's passage). -/
private theorem piece_addD {o m : Nat} (S : split.PMat) (K : Nat)
    (i : Nat) (up : Bool) (hpc : pieceRead o [i]) (hsh : pShapeAt S o K)
    (hm : (compl [i] o).length = m)
    (hoff : coupVac S o i = true)
    (xn : BPair) (xc : Pos)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S xn xc K))
      (evalPC S xn xc K))
    (hs : if up = true
      then BPair.unit < elim.minor (elim.selM [i] [i] (evalPC S xn xc K))
      else elim.minor (elim.selM [i] [i] (evalPC S xn xc K)) < BPair.unit)
    (spx : inertia.Split o)
    (hx : inertia.splitRead (evalPC S xn xc K) spx)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (evalPC (split.pselM (compl [i] o) (compl [i] o) S) xn xc K) spD) :
    inertia.revAt spx
      = inertia.revAt (inertia.mkSplit 1
          (elim.selM [i] [i] (evalPC S xn xc K)))
        + inertia.revAt spD := by
  subst hm
  have hidx := hpc.1
  have hdix := hpc.2
  have hMsq : elim.sqAt (evalPC S xn xc K) o := evalPC_sqAt hsh xn xc
  have hk0 : 0 < ([i] : List Nat).length := Nat.succ_pos 0
  have hsgl : ([i] ++ compl [i] o).length = o := by
    rw [ground.length_append]
    exact compl_length hdix hidx
  have hPvsq : elim.sqAt (elim.selM [i] [i] (evalPC S xn xc K)) 1 :=
    elim.sqAt_of (elim.length_selM [i] [i] _) (elim.rowsLen_selM [i] _ [i])
  have hPvsym : elim.matOneValue
      (elim.transposeM (elim.selM [i] [i] (evalPC S xn xc K)))
      (elim.selM [i] [i] (evalPC S xn xc K)) :=
    elim.transposeM_selM [i] [i] _ o hMsq hMsym hk0 hidx hidx
  have hPread := inertia.mkSplit_read 1 _ hPvsq hPvsym
  obtain ⟨_, _, _, hQsq, _, hTBl, _, _⟩ :=
    pivotBlocks (evalPC S xn xc K) [i] (compl [i] o) o hMsq hMsym hk0 hidx
      (all_compl [i] o)
  have hPw := pdeflW_solve S K [i] (compl [i] o) xn xc (ent_ble hsh) hk0
  have hCwl : (evalPC (pdeflW [i] (compl [i] o) S) xn xc
      (([i] : List Nat).length * K)).length = ([i] : List Nat).length :=
    (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
  have hCwr : elim.rowsLen (compl [i] o).length
      (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K)) :=
    rowsLen_evalPC _ _ _ _ _ (rowsLen_pdeflW [i] _ _ hk0)
  have hCt : (elim.transposeM (evalPC (pdeflW [i] (compl [i] o) S) xn xc
      (([i] : List Nat).length * K))).length = (compl [i] o).length :=
    elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0)
  have hdefl := diag_defl S K i hpc hsh hoff xn xc hMsym
  have hD0 : inertia.splitRead
      (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K)) spD := by
    rw [selM_evalPC xn xc K S (compl [i] o) (compl [i] o)]
    exact hD
  have hDsq := inertia.sqAt_deflMatP
    (elim.selM [i] [i] (evalPC S xn xc K))
    (elim.selM [i] (compl [i] o) (evalPC S xn xc K))
    (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K))
    (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K))
    (compl [i] o).length hTBl hCt (elim.sqAt_len hQsq)
    (elim.rowsLen_of_sqAt hQsq)
  have hb : (([i] ++ compl [i] o).all (fun k => Nat.blt k o)) = true := by
    rw [ground.all_append, hidx, all_compl [i] o]
    rfl
  match up, hs with
  | true, hPpos =>
    have hDQ := inertia.scaleSplit_read _ (ground.offOfUnitLt hPpos) _ spD hD0
    have hD' := inertia.splitRead_congr _ _ hDsq (elim.matOne_symm hdefl) _ hDQ
    have h := inertia.rev_placesP (evalPC S xn xc K) [i] (compl [i] o) hk0 hMsq
      hMsym hsgl (distinct_append_compl (o := o) hdix) hb _ hCwl hCwr hPw hPpos
      spx hx _ hPread _ hD'
    rw [h, inertia.scaleSplit_rev _ hPpos spD]
  | false, hPneg =>
    have hsw : BPair.unit
        < (elim.minor (elim.selM [i] [i] (evalPC S xn xc K))).swap :=
      ground.ltB_swap hPneg
    have hDQ := inertia.scaleSplit_read _ (ground.offOfUnitLt hsw) _ spD hD0
    have hsc : elim.matOneValue
        (inertia.matScaleB
          (elim.minor (elim.selM [i] [i] (evalPC S xn xc K))).swap
          (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K)))
        (elim.matSwap (inertia.deflMatP (elim.selM [i] [i] (evalPC S xn xc K))
          (elim.selM [i] (compl [i] o) (evalPC S xn xc K))
          (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K))
          (evalPC (pdeflW [i] (compl [i] o) S) xn xc
            (([i] : List Nat).length * K)))) := by
      have h1 := inertia.matScaleB_swap
        (elim.minor (elim.selM [i] [i] (evalPC S xn xc K))).swap
        (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K))
      rw [BPair.swap_swap] at h1
      exact elim.matOne_trans h1
        (elim.matOne_trans
          (inertia.matScaleB_neg (elim.minor (elim.selM [i] [i] (evalPC S xn xc K)))
            (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K)))
          (elim.matSwap_congr (elim.matOne_symm hdefl)))
    have hD' := inertia.splitRead_congr _ _ (elim.sqAt_matSwap _ _ hDsq) hsc _ hDQ
    have h := inertia.rev_placesM (evalPC S xn xc K) [i] (compl [i] o) hk0 hMsq
      hMsym hsgl (distinct_append_compl (o := o) hdix) hb _ hCwl hCwr hPw hPneg
      spx hx _ hPread _ hD'
    rw [h, inertia.scaleSplit_rev _ hsw spD]

/-- The order-one designated block's frame at a stage point: the
minor's side is the block table's entry side, and the pivot's split
reads the table. -/
private theorem side_one {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (i : Nat) (up : Bool) (N D : BPair)
    (hsh : pShapeAt S o K)
    (hidx : (([i] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : if up = true
      then stage.keepUpper (split.pminor (split.pselM [i] [i] S)) lo b N D
      else stage.keepLower (split.pminor (split.pselM [i] [i] S)) lo b N D)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S zn zc K))
      (evalPC S zn zc K)) :
    (¬ (elim.minor
        (elim.selM [i] [i] (evalPC S zn zc K))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i] : List Nat).length
        (elim.selM [i] [i] (evalPC S zn zc K)))
      = (if up = true then 0 else 1)
    ∧ (up = true → BPair.unit
        < elim.minor (elim.selM [i] [i] (evalPC S zn zc K)))
    ∧ (up = false → elim.minor (elim.selM [i] [i] (evalPC S zn zc K))
        < BPair.unit) := by
  have hMsq : elim.sqAt (evalPC S zn zc K) o := evalPC_sqAt hsh zn zc
  have hi : i < o := ground.bltLt (ground.andSplitB hidx).1
  match up, hside with
  | true, hs =>
    have h2 : BPair.unit
        < poly.evalClear (split.pminor (split.pselM [i] [i] S))
            zn zc K :=
      stage.evalFloor
        (fun d hd => BPair.oneValue_of_eq
          (ground.getAt_over BPair.unit _ d
            (Nat.le_trans (ent_ble hsh i i) hd)))
        zn zc
        (stage.keepUpper_all _ lo b N D hs ⟨zn, zc⟩ hlz hzb)
    have h3 : BPair.unit
        < ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) i :=
      BPair.lt_congr (BPair.oneValue_refl _) (minor1_bridge S K i zn zc) h2
    have hr := inertia.revSel_one (evalPC S zn zc K) hMsq hMsym i hi true h3
    exact ⟨hr.1, hr.2, fun _ => h3, fun h => Bool.noConfusion h⟩
  | false, hs =>
    have h2 : poly.evalClear (split.pminor (split.pselM [i] [i] S))
        zn zc K < BPair.unit :=
      sideDown_shift _ zn zc K (ent_ble hsh i i)
        (sideDown_rep _ zn zc
          (stage.keepLower_all _ lo b N D hs ⟨zn, zc⟩ hlz hzb))
    have h3 : ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) i
        < BPair.unit :=
      BPair.lt_congr (minor1_bridge S K i zn zc) (BPair.oneValue_refl _) h2
    have hr := inertia.revSel_one (evalPC S zn zc K) hMsq hMsym i hi false h3
    exact ⟨hr.1, hr.2, fun h => Bool.noConfusion h, fun _ => h3⟩

/-- The mixed order-two block's frame: the determinant on its lower
side reads one unit per side. -/
private theorem side_mixed {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (i j : Nat) (N D : BPair)
    (hsh : pShapeAt S o K)
    (hidx : (([i, j] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : stage.keepLower
      (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S zn zc K))
      (evalPC S zn zc K)) :
    (¬ (elim.minor (elim.selM [i, j] [i, j]
        (evalPC S zn zc K))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i, j] : List Nat).length
        (elim.selM [i, j] [i, j] (evalPC S zn zc K))) = 1
    ∧ elim.minor (elim.selM [i, j] [i, j] (evalPC S zn zc K)) < BPair.unit := by
  have hs1 := ground.andSplitB hidx
  have hs2 := ground.andSplitB hs1.2
  have hi : i < o := ground.bltLt hs1.1
  have hj : j < o := ground.bltLt hs2.1
  have hMsq : elim.sqAt (evalPC S zn zc K) o := evalPC_sqAt hsh zn zc
  have h2 : poly.evalClear (split.pminor (split.pselM [i, j] [i, j] S))
      zn zc (K + K) < BPair.unit :=
    sideDown_shift _ zn zc (K + K) (pminor2_len hsh i j)
      (sideDown_rep _ zn zc
        (stage.keepLower_all _ lo b N D hside ⟨zn, zc⟩ hlz hzb))
  have h3 : elim.minor (elim.selM [i, j] [i, j]
      (evalPC S zn zc K)) < BPair.unit :=
    BPair.lt_congr (minor2_bridge hsh i j zn zc) (BPair.oneValue_refl _) h2
  have hr := inertia.revSel_mixed (evalPC S zn zc K) hMsq hMsym i j hi hj h3
  exact ⟨hr.1, hr.2, h3⟩

/-- The upper order-two block's frame: the determinant on its upper
side with the leading entry's own side reading the table. -/
private theorem side_twoUp {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (i j : Nat) (N D : BPair) (eUp : Bool) (eN eD : BPair)
    (hsh : pShapeAt S o K)
    (hidx : (([i, j] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : stage.keepUpper
      (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)
    (hent : if eUp = true
      then stage.keepUpper (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) i) lo b eN eD
      else stage.keepLower (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) i) lo b eN eD)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S zn zc K))
      (evalPC S zn zc K)) :
    (¬ (elim.minor (elim.selM [i, j] [i, j]
        (evalPC S zn zc K))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i, j] : List Nat).length
        (elim.selM [i, j] [i, j] (evalPC S zn zc K)))
      = (if eUp = true then 0 else 2)
    ∧ BPair.unit < elim.minor (elim.selM [i, j] [i, j] (evalPC S zn zc K)) := by
  have hs1 := ground.andSplitB hidx
  have hs2 := ground.andSplitB hs1.2
  have hi : i < o := ground.bltLt hs1.1
  have hj : j < o := ground.bltLt hs2.1
  have hMsq : elim.sqAt (evalPC S zn zc K) o := evalPC_sqAt hsh zn zc
  have h2 : BPair.unit
      < poly.evalClear (split.pminor (split.pselM [i, j] [i, j] S))
          zn zc (K + K) :=
    stage.evalFloor
      (fun d hd => BPair.oneValue_of_eq
        (ground.getAt_over BPair.unit _ d
          (Nat.le_trans (pminor2_len hsh i j) hd)))
      zn zc
      (stage.keepUpper_all _ lo b N D hside ⟨zn, zc⟩ hlz hzb)
  have h3 : BPair.unit < elim.minor (elim.selM [i, j] [i, j]
      (evalPC S zn zc K)) :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (minor2_bridge hsh i j zn zc) h2
  match eUp, hent with
  | true, he =>
    have e2 : BPair.unit
        < poly.evalClear (ground.getAt ([] : Poly)
            (ground.getAt ([] : List Poly) S i) i) zn zc K :=
      stage.evalFloor
        (fun d hd => BPair.oneValue_of_eq
          (ground.getAt_over BPair.unit _ d
            (Nat.le_trans (ent_ble hsh i i) hd)))
        zn zc
        (stage.keepUpper_all _ lo b eN eD he ⟨zn, zc⟩ hlz hzb)
    have e3 : BPair.unit < ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) i := by
      rw [getAt_evalPC zn zc K S i i]
      exact e2
    have hr := inertia.revSel_twoUp (evalPC S zn zc K) hMsq hMsym i j hi hj h3
      true e3
    exact ⟨hr.1, hr.2, h3⟩
  | false, he =>
    have e2 : poly.evalClear (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) i) zn zc K
        < BPair.unit :=
      sideDown_shift _ zn zc K (ent_ble hsh i i)
        (sideDown_rep _ zn zc
          (stage.keepLower_all _ lo b eN eD he ⟨zn, zc⟩ hlz hzb))
    have e3 : ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) i
        < BPair.unit := by
      rw [getAt_evalPC zn zc K S i i]
      exact e2
    have hr := inertia.revSel_twoUp (evalPC S zn zc K) hMsq hMsym i j hi hj h3
      false e3
    exact ⟨hr.1, hr.2, h3⟩

/-- The vacant-coupling piece's order-one frame at a stage point is
the designated block's own (`side_one`): the minor off the unit, the
pivot's split read, and the minor's strict side at the piece's
side. -/
private theorem side_diag {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (i : Nat) (up : Bool) (N D : BPair)
    (hsh : pShapeAt S o K)
    (hidx : (([i] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : if up = true
      then stage.keepUpper (split.pminor (split.pselM [i] [i] S)) lo b N D
      else stage.keepLower (split.pminor (split.pselM [i] [i] S)) lo b N D)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S zn zc K))
      (evalPC S zn zc K)) :
    (¬ (elim.minor
        (elim.selM [i] [i] (evalPC S zn zc K))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i] : List Nat).length
        (elim.selM [i] [i] (evalPC S zn zc K)))
      = (if up = true then 0 else 1)
    ∧ (if up = true
        then BPair.unit < elim.minor (elim.selM [i] [i] (evalPC S zn zc K))
        else elim.minor (elim.selM [i] [i] (evalPC S zn zc K)) < BPair.unit) :=
  let h := side_one S K lo b i up N D hsh hidx hside zn zc hlz hzb hMsym
  ⟨h.1, h.2.1, match up, h.2.2 with
    | true, hs => hs.1 rfl
    | false, hs => hs.2 rfl⟩

/-- A cover at an occupied order orders its segment's two ends, each
piece's bracket chained to the top. -/
private theorem cover_le : ∀ (cov : Cover) (o : Nat) (S : split.PMat)
    (K : Nat) (lo hi : CPair), coverRead S o K lo hi cov → 0 < o → lo ≤ hi
  | .done, _, _, _, _, _, h, _ => Or.inl h
  | .nought, _, _, _, _, _, h, ho =>
    absurd (ground.beqEq _ _ h) (Nat.ne_of_gt ho)
  | .one b _ up _ _ _ rest, o, S, K, lo, hi, h, ho =>
    have hlt : lo < b := by
      match up, h.2.1 with
      | true, hs => exact hs.2.1
      | false, hs => exact hs.2.1
    CPair.le_trans (Or.inr hlt) (cover_le rest o S K b hi h.2.2.2 ho)
  | .mixed b _ _ _ _ _ rest, o, S, K, lo, hi, h, ho =>
    CPair.le_trans (Or.inr h.2.1.2.1) (cover_le rest o S K b hi h.2.2.2 ho)
  | .twoUp b _ _ _ _ _ _ _ _ rest, o, S, K, lo, hi, h, ho =>
    CPair.le_trans (Or.inr h.2.1.2.1) (cover_le rest o S K b hi h.2.2.2.2 ho)
  | .diag b _ up _ _ _ rest, o, S, K, lo, hi, h, ho =>
    have hlt : lo < b := by
      match up, h.2.1 with
      | true, hs => exact hs.2.1
      | false, hs => exact hs.2.1
    CPair.le_trans (Or.inr hlt) (cover_le rest o S K b hi h.2.2.2.2 ho)

/-- One subinterval's step in the chain at a stated sub-pencil beneath
the piece: inside it every point reads the piece's fixed value against
the sub-pencil's own constant count, past it the chain's remainder
moves the count to the shared endpoint; the two pencils' symmetry is
read on the segment alone. -/
private theorem chain_stepG {o m : Nat} (S D : split.PMat) (K KK : Nat)
    (lo b hi : CPair) (r : Nat)
    (hsh : pShapeAt S o K)
    (hsymF : ∀ (zn : BPair) (zc : Pos),
      lo ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ hi →
      elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K))
    (hshD : pShapeAt D m KK)
    (hDsymF : ∀ (zn : BPair) (zc : Pos),
      lo ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ b →
      elim.matOneValue (elim.transposeM (evalPC D zn zc KK)) (evalPC D zn zc KK))
    (hlt : lo < b) (hbhi : b ≤ hi)
    (hpiece : ∀ (zn : BPair) (zc : Pos),
      lo ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ b →
      ∀ (spz : inertia.Split o), inertia.splitRead (evalPC S zn zc K) spz →
      ∀ (spD : inertia.Split m), inertia.splitRead (evalPC D zn zc KK) spD →
      inertia.revAt spz = r + inertia.revAt spD)
    (ihSub : ∀ (un : BPair) (uc : Pos) (vn : BPair) (vc : Pos),
      lo ≤ ⟨un, uc⟩ → (⟨un, uc⟩ : CPair) ≤ b →
      lo ≤ ⟨vn, vc⟩ → (⟨vn, vc⟩ : CPair) ≤ b →
      ∀ (spu spv : inertia.Split m),
        inertia.splitRead (evalPC D un uc KK) spu →
        inertia.splitRead (evalPC D vn vc KK) spv →
        inertia.revAt spu = inertia.revAt spv)
    (ihRest : ∀ (un : BPair) (uc : Pos) (vn : BPair) (vc : Pos),
      b ≤ ⟨un, uc⟩ → (⟨un, uc⟩ : CPair) ≤ hi →
      b ≤ ⟨vn, vc⟩ → (⟨vn, vc⟩ : CPair) ≤ hi →
      ∀ (spu spv : inertia.Split o),
        inertia.splitRead (evalPC S un uc K) spu →
        inertia.splitRead (evalPC S vn vc K) spv →
        inertia.revAt spu = inertia.revAt spv)
    (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos)
    (hlx : lo ≤ ⟨xn, xc⟩) (hxh : (⟨xn, xc⟩ : CPair) ≤ hi)
    (hly : lo ≤ ⟨yn, yc⟩) (hyh : (⟨yn, yc⟩ : CPair) ≤ hi)
    (spx spy : inertia.Split o)
    (hx : inertia.splitRead (evalPC S xn xc K) spx)
    (hy : inertia.splitRead (evalPC S yn yc K) spy) :
    inertia.revAt spx = inertia.revAt spy := by
  obtain ⟨lon, loc⟩ := lo
  obtain ⟨bn, bc⟩ := b
  have mkD : ∀ (zn : BPair) (zc : Pos),
      (⟨lon, loc⟩ : CPair) ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ ⟨bn, bc⟩ →
      inertia.splitRead (evalPC D zn zc KK)
        (inertia.mkSplit m (evalPC D zn zc KK)) :=
    fun zn zc hlz hzb =>
      inertia.mkSplit_read m _ (evalPC_sqAt hshD zn zc) (hDsymF zn zc hlz hzb)
  have hbread : inertia.splitRead (evalPC S bn bc K)
      (inertia.mkSplit o (evalPC S bn bc K)) :=
    inertia.mkSplit_read o _ (evalPC_sqAt hsh bn bc)
      (hsymF bn bc (Or.inr hlt) hbhi)
  have key : ∀ (zn : BPair) (zc : Pos),
      (⟨lon, loc⟩ : CPair) ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ ⟨bn, bc⟩ →
      ∀ (spz : inertia.Split o),
        inertia.splitRead (evalPC S zn zc K) spz →
        inertia.revAt spz = r + inertia.revAt (inertia.mkSplit m
          (evalPC D lon loc KK)) := by
    intro zn zc hlz hzb spz hz
    rw [hpiece zn zc hlz hzb spz hz _ (mkD zn zc hlz hzb)]
    exact congrArg (fun t => r + t)
      (ihSub zn zc lon loc hlz hzb (CPair.le_refl ⟨lon, loc⟩) (Or.inr hlt)
        _ _ (mkD zn zc hlz hzb) (mkD lon loc (CPair.le_refl _) (Or.inr hlt)))
  have final : ∀ (zn : BPair) (zc : Pos),
      (⟨lon, loc⟩ : CPair) ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ hi →
      ∀ (spz : inertia.Split o),
        inertia.splitRead (evalPC S zn zc K) spz →
        inertia.revAt spz = r + inertia.revAt (inertia.mkSplit m
          (evalPC D lon loc KK)) := by
    intro zn zc hlz hzh spz hz
    match CPair.le_total ⟨zn, zc⟩ ⟨bn, bc⟩ with
    | Or.inl hzb => exact key zn zc hlz hzb spz hz
    | Or.inr hbz =>
      have hr := ihRest zn zc bn bc hbz hzh (CPair.le_refl ⟨bn, bc⟩)
        (CPair.le_trans hbz hzh) spz _ hz hbread
      rw [hr]
      exact key bn bc (Or.inr hlt) (CPair.le_refl ⟨bn, bc⟩) _ hbread
  exact (final xn xc hlx hxh spx hx).trans
    (final yn yc hly hyh spy hy).symm

/-- `lem:cellcount`'s constancy at a shaped pencil symmetric at every
point of the segment, the evaluated symmetry the hypothesis on the
segment alone: the chain's end at one composite point, the
order-nought deflation at the vacant count, and each piece at its own
block value with the cover beneath it, the deflation cleared once at
the pivot's determinant's magnitude, the once-cleared deflation at a
pivot keeping its upper side (`evalPC_pdeflP_symm` at the piece's
side read) and its memberwise swap at a pivot keeping its lower side
or at the mixed block (`evalPC_pdeflM_symm`), and the trailing block
itself at a vacant coupling, with the chain's remainder beside it;
two stated points' splits at the cleared evaluations read one
count. -/
private theorem cover_constP : ∀ (cov : Cover) (o : Nat) (S : split.PMat)
    (K : Nat) (lo hi : CPair), coverRead S o K lo hi cov →
    pShapeAt S o K →
    (∀ (zn : BPair) (zc : Pos),
      lo ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ hi →
      elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K)) →
    ∀ (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos),
      lo ≤ ⟨xn, xc⟩ → (⟨xn, xc⟩ : CPair) ≤ hi →
      lo ≤ ⟨yn, yc⟩ → (⟨yn, yc⟩ : CPair) ≤ hi →
    ∀ (spx spy : inertia.Split o),
      inertia.splitRead (evalPC S xn xc K) spx →
      inertia.splitRead (evalPC S yn yc K) spy →
      inertia.revAt spx = inertia.revAt spy
  | .done => by
    intro o S K lo hi h hsh _ xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hxlo : lo.oneValue ⟨xn, xc⟩ :=
      CPair.le_antisymm hlx (CPair.le_trans hxh (Or.inl (CPair.oneValue_symm h)))
    have hylo : lo.oneValue ⟨yn, yc⟩ :=
      CPair.le_antisymm hly (CPair.le_trans hyh (Or.inl (CPair.oneValue_symm h)))
    exact rev_point S K (pShape_len hsh) (pShape_rows hsh) (ent_ble hsh)
      xn xc yn yc
      (CPair.oneValue_trans (CPair.oneValue_symm hxlo) hylo) spx spy hx hy
  | .nought => by
    intro o S K lo hi h _ _ xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have h0 : o = 0 := ground.beqEq _ _ h
    subst h0
    rw [inertia.revAt_zero spx, inertia.revAt_zero spy]
  | .one b i true N D sub rest => by
    intro o S K lo hi h hsh hsymF xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hs : stage.keepUpper (split.pminor (split.pselM [i] [i] S)) lo b N D :=
      h.2.1
    have hsub : coverRead (pdeflP [i] (compl [i] o) S) (o - 1) (2 * K) lo b sub :=
      h.2.2.1
    have hlt : lo < b := hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi := cover_le rest o S K b hi h.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans (congrArg (fun t => t - 1) hsum)
    have hshS : pShapeAt (pdeflP [i] (compl [i] o) S) (o - 1) (2 * K) := by
      have h1 := pShape_pdeflP S o K [i] (compl [i] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM (evalPC (pdeflP [i] (compl [i] o) S) zn zc (2 * K)))
          (evalPC (pdeflP [i] (compl [i] o) S) zn zc (2 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflP_symm S K [i] (compl [i] o) zn zc hsh (hsymB zn zc hlz hzb)
          (Nat.succ_pos 0) h.1.1 (all_compl [i] o)
          (side_one S K lo b i true N D hsh h.1.1 hs zn zc hlz hzb
            (hsymB zn zc hlz hzb)).1
    exact chain_stepG S (pdeflP [i] (compl [i] o) S) K (2 * K) lo b hi
      (if true = true then 0 else 1) hsh hsymF hshS hDsymF hlt hbhi
      (fun zn zc hlz hzb spz hz spD hD => by
        have hsd := side_one S K lo b i true N D hsh h.1.1 hs zn zc hlz hzb
          (hsymB zn zc hlz hzb)
        rw [← hsd.2.1]
        exact piece_addP S K (2 * K) [i] h.1 hsh (Nat.succ_pos 0) hcl rfl zn zc
          (hsymB zn zc hlz hzb) (hsd.2.2.1 rfl) spz hz spD hD)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP sub (o - 1) (pdeflP [i] (compl [i] o) S) (2 * K) lo b
          hsub hshS hDsymF un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP rest o S K b hi h.2.2.2 hsh
          (fun zn zc hlz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hlz) hzh)
          un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy
  | .one b i false N D sub rest => by
    intro o S K lo hi h hsh hsymF xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hs : stage.keepLower (split.pminor (split.pselM [i] [i] S)) lo b N D :=
      h.2.1
    have hsub : coverRead (pdeflM [i] (compl [i] o) S) (o - 1) (2 * K) lo b sub :=
      h.2.2.1
    have hlt : lo < b := hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi := cover_le rest o S K b hi h.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans (congrArg (fun t => t - 1) hsum)
    have hshS : pShapeAt (pdeflM [i] (compl [i] o) S) (o - 1) (2 * K) := by
      have h1 := pShape_pdeflM S o K [i] (compl [i] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM (evalPC (pdeflM [i] (compl [i] o) S) zn zc (2 * K)))
          (evalPC (pdeflM [i] (compl [i] o) S) zn zc (2 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflM_symm S K [i] (compl [i] o) zn zc hsh (hsymB zn zc hlz hzb)
          (Nat.succ_pos 0) h.1.1 (all_compl [i] o)
          (side_one S K lo b i false N D hsh h.1.1 hs zn zc hlz hzb
            (hsymB zn zc hlz hzb)).1
    exact chain_stepG S (pdeflM [i] (compl [i] o) S) K (2 * K) lo b hi
      (if false = true then 0 else 1) hsh hsymF hshS hDsymF hlt hbhi
      (fun zn zc hlz hzb spz hz spD hD => by
        have hsd := side_one S K lo b i false N D hsh h.1.1 hs zn zc hlz hzb
          (hsymB zn zc hlz hzb)
        rw [← hsd.2.1]
        exact piece_addM S K (2 * K) [i] h.1 hsh (Nat.succ_pos 0) hcl rfl zn zc
          (hsymB zn zc hlz hzb) (hsd.2.2.2 rfl) spz hz spD hD)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP sub (o - 1) (pdeflM [i] (compl [i] o) S) (2 * K) lo b
          hsub hshS hDsymF un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP rest o S K b hi h.2.2.2 hsh
          (fun zn zc hlz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hlz) hzh)
          un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy
  | .mixed b i j N D sub rest => by
    intro o S K lo hi h hsh hsymF xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hlt : lo < b := h.2.1.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi := cover_le rest o S K b hi h.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans (congrArg (fun t => t - 2) hsum)
    have hshS : pShapeAt (pdeflM [i, j] (compl [i, j] o) S) (o - 2) (3 * K) := by
      have h1 := pShape_pdeflM S o K [i, j] (compl [i, j] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM (evalPC (pdeflM [i, j] (compl [i, j] o) S) zn zc (3 * K)))
          (evalPC (pdeflM [i, j] (compl [i, j] o) S) zn zc (3 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflM_symm S K [i, j] (compl [i, j] o) zn zc hsh
          (hsymB zn zc hlz hzb) (Nat.succ_pos 1) h.1.1 (all_compl [i, j] o)
          (side_mixed S K lo b i j N D hsh h.1.1 h.2.1 zn zc hlz hzb
            (hsymB zn zc hlz hzb)).1
    exact chain_stepG S (pdeflM [i, j] (compl [i, j] o) S) K (3 * K) lo b hi 1
      hsh hsymF hshS hDsymF hlt hbhi
      (fun zn zc hlz hzb spz hz spD hD => by
        have hsd := side_mixed S K lo b i j N D hsh h.1.1 h.2.1 zn zc hlz hzb
          (hsymB zn zc hlz hzb)
        rw [← hsd.2.1]
        exact piece_addM S K (3 * K) [i, j] h.1 hsh (Nat.succ_pos 1) hcl rfl zn zc
          (hsymB zn zc hlz hzb) hsd.2.2 spz hz spD hD)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP sub (o - 2) (pdeflM [i, j] (compl [i, j] o) S) (3 * K) lo b
          h.2.2.1 hshS hDsymF un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP rest o S K b hi h.2.2.2 hsh
          (fun zn zc hlz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hlz) hzh)
          un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy
  | .twoUp b i j N D eUp eN eD sub rest => by
    intro o S K lo hi h hsh hsymF xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hlt : lo < b := h.2.1.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi :=
      cover_le rest o S K b hi h.2.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans (congrArg (fun t => t - 2) hsum)
    have hshS : pShapeAt (pdeflP [i, j] (compl [i, j] o) S) (o - 2) (3 * K) := by
      have h1 := pShape_pdeflP S o K [i, j] (compl [i, j] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM
            (evalPC (pdeflP [i, j] (compl [i, j] o) S) zn zc (3 * K)))
          (evalPC (pdeflP [i, j] (compl [i, j] o) S) zn zc (3 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflP_symm S K [i, j] (compl [i, j] o) zn zc hsh
          (hsymB zn zc hlz hzb) (Nat.succ_pos 1) h.1.1 (all_compl [i, j] o)
          (side_twoUp S K lo b i j N D eUp eN eD hsh h.1.1 h.2.1 h.2.2.1
            zn zc hlz hzb (hsymB zn zc hlz hzb)).1
    exact chain_stepG S (pdeflP [i, j] (compl [i, j] o) S) K (3 * K) lo b hi
      (if eUp = true then 0 else 2) hsh hsymF hshS hDsymF hlt hbhi
      (fun zn zc hlz hzb spz hz spD hD => by
        have hsd := side_twoUp S K lo b i j N D eUp eN eD hsh h.1.1 h.2.1
          h.2.2.1 zn zc hlz hzb (hsymB zn zc hlz hzb)
        rw [← hsd.2.1]
        exact piece_addP S K (3 * K) [i, j] h.1 hsh (Nat.succ_pos 1) hcl rfl zn zc
          (hsymB zn zc hlz hzb) hsd.2.2 spz hz spD hD)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP sub (o - 2) (pdeflP [i, j] (compl [i, j] o) S) (3 * K) lo b
          h.2.2.2.1 hshS hDsymF un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP rest o S K b hi h.2.2.2.2 hsh
          (fun zn zc hlz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hlz) hzh)
          un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy
  | .diag b i up N D sub rest => by
    intro o S K lo hi h hsh hsymF xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hlt : lo < b := by
      match up, h.2.1 with
      | true, hs => exact hs.2.1
      | false, hs => exact hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi :=
      cover_le rest o S K b hi h.2.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans (congrArg (fun t => t - 1) hsum)
    have hshS : pShapeAt (split.pselM (compl [i] o) (compl [i] o) S) (o - 1) K := by
      rw [← hcl]
      exact pShape_pselM S K (compl [i] o) (ent_ble hsh)
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM
            (evalPC (split.pselM (compl [i] o) (compl [i] o) S) zn zc K))
          (evalPC (split.pselM (compl [i] o) (compl [i] o) S) zn zc K) := by
      intro zn zc hlz hzb
      rw [← selM_evalPC zn zc K S (compl [i] o) (compl [i] o)]
      rcases Nat.eq_zero_or_pos (compl [i] o).length with hz | hpos
      · cases hc : compl [i] o with
        | nil => exact trivial
        | cons c cs =>
          rw [hc] at hz
          exact Nat.noConfusion hz
      · exact elim.transposeM_selM _ _ _ o (evalPC_sqAt hsh zn zc)
          (hsymB zn zc hlz hzb) hpos (all_compl [i] o) (all_compl [i] o)
    exact chain_stepG S (split.pselM (compl [i] o) (compl [i] o) S) K K lo b hi
      (if up = true then 0 else 1) hsh hsymF hshS hDsymF hlt hbhi
      (fun zn zc hlz hzb spz hz spD hD => by
        have hsd := side_diag S K lo b i up N D hsh h.1.1 h.2.1 zn zc hlz hzb
          (hsymB zn zc hlz hzb)
        rw [← hsd.2.1]
        exact piece_addD S K i up h.1 hsh hcl h.2.2.1 zn zc (hsymB zn zc hlz hzb)
          hsd.2.2 spz hz spD hD)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP sub (o - 1) (split.pselM (compl [i] o) (compl [i] o) S) K
          lo b h.2.2.2.1 hshS hDsymF un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_constP rest o S K b hi h.2.2.2.2 hsh
          (fun zn zc hlz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hlz) hzh)
          un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy

/-- `lem:cellcount`'s constancy: at a valid cover of a shaped
symmetric pencil (the symmetry binder the lemma's hypothesis, a
symmetric pencil whose entries are polynomial in the coordinate) the
reversal count reads one integer at every point of the segment, any
two stated points' splits at the cleared evaluations reading one
count, the representatives entering as data. -/
theorem cover_const {o : Nat} (S : split.PMat) (K : Nat)
    (lo hi : CPair) (cov : Cover)
    (h : coverRead S o K lo hi cov)
    (hsh : pShapeAt S o K) (hsym : split.pSymAt S o)
    (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos)
    (hlx : lo ≤ ⟨xn, xc⟩) (hxh : (⟨xn, xc⟩ : CPair) ≤ hi)
    (hly : lo ≤ ⟨yn, yc⟩) (hyh : (⟨yn, yc⟩ : CPair) ≤ hi)
    (spx spy : Split o)
    (hx : splitRead (evalPC S xn xc K) spx)
    (hy : splitRead (evalPC S yn yc K) spy) :
    revAt spx = revAt spy :=
  cover_constP cov o S K lo hi h hsh
    (fun zn zc _ _ => elim.matOne_symm
      (evalPC_symAt S o K zn zc (pShape_len hsh) (pShape_rows hsh) hsym))
    xn xc yn yc hlx hxh hly hyh spx spy hx hy

/-- The pointwise count: the reversal count at the cleared
evaluation, the shape read a conjunct. -/
def countAt {o : Nat} (S : split.PMat) (K : Nat) (ln : BPair)
    (c : Pos) (n : Nat) (sp : Split o) : Prop :=
  pShapeAt S o K
  ∧ splitRead (evalPC S ln c K) sp
  ∧ revAt sp = n

instance instCellcount3 {o : Nat} (S : split.PMat) (K : Nat) (ln : BPair) (c : Pos)
    (n : Nat) (sp : Split o) :
    Decidable (countAt S K ln c n sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _))

/-- The count is a cell function, read once, at a pencil symmetric
at every point of the segment, the symmetry read on the segment
alone (`lem:cellcount`'s constancy at the count certificate,
`cover_constP`, the tower deflation's form): a sampled count holds at every point, the target's stated
split reading the sample's value, the shape the sample's own read. -/
theorem cellCountP {o : Nat} (S : split.PMat) (K n : Nat)
    (lo hi : CPair) (cov : Cover)
    (hc : coverRead S o K lo hi cov)
    (hsym : ∀ (zn : BPair) (zc : Pos),
      lo ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ hi →
      elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K))
    (sn : BPair) (sc : Pos)
    (hls : lo ≤ (⟨sn, sc⟩ : CPair)) (hsu : (⟨sn, sc⟩ : CPair) ≤ hi)
    (sps : inertia.Split o)
    (hs : countAt S K sn sc n sps)
    (tn : BPair) (tc : Pos)
    (hlt : lo ≤ (⟨tn, tc⟩ : CPair)) (hth : (⟨tn, tc⟩ : CPair) ≤ hi)
    (spt : inertia.Split o)
    (ht : inertia.splitRead (evalPC S tn tc K) spt) :
    inertia.revAt spt = n :=
  (cover_constP cov o S K lo hi hc hs.1 hsym tn tc sn sc hlt hth hls hsu
    spt sps ht hs.2.1).trans hs.2.2

/-- The count is a cell function, read once (`lem:cellcount`'s
constancy at the count certificate): on a covered segment of a
symmetric pencil (the symmetry binder the lemma's hypothesis) a
sampled count holds at every point, the target's stated split
reading the sample's value, the shape the sample's own read. -/
theorem cellCount {o : Nat} (S : split.PMat) (K n : Nat)
    (lo hi : CPair) (cov : Cover)
    (hc : coverRead S o K lo hi cov) (hsym : split.pSymAt S o)
    (sn : BPair) (sc : Pos)
    (hls : lo ≤ (⟨sn, sc⟩ : CPair)) (hsu : (⟨sn, sc⟩ : CPair) ≤ hi)
    (sps : inertia.Split o)
    (hs : countAt S K sn sc n sps)
    (tn : BPair) (tc : Pos)
    (hlt : lo ≤ (⟨tn, tc⟩ : CPair)) (hth : (⟨tn, tc⟩ : CPair) ≤ hi)
    (spt : inertia.Split o)
    (ht : inertia.splitRead (evalPC S tn tc K) spt) :
    inertia.revAt spt = n :=
  cellCountP S K n lo hi cov hc
    (fun zn zc _ _ => elim.matOne_symm
      (evalPC_symAt S o K zn zc (pShape_len hs.1) (pShape_rows hs.1) hsym))
    sn sc hls hsu sps hs tn tc hlt hth spt ht

/-- A read holding on a piece and, past it, on the chain's remainder
holds at every point of the segment: consecutive pieces meeting at a
shared point (`lem:cellcount`'s subintervals chained at shared
endpoints). -/
theorem seg_split (P : CPair → Prop) (lo b hi : CPair)
    (hpiece : ∀ y : CPair, lo ≤ y → y ≤ b → P y)
    (hrest : b < hi → ∀ y : CPair, b ≤ y → y ≤ hi → P y)
    (x : CPair) (hlx : lo ≤ x) (hxh : x ≤ hi) : P x := by
  match CPair.le_total x b with
  | Or.inl hxb => exact hpiece x hlx hxb
  | Or.inr hbx =>
    match CPair.le_total hi b with
    | Or.inl hhb => exact hpiece x hlx (CPair.le_trans hxh hhb)
    | Or.inr (Or.inl hov) =>
      exact hpiece x hlx (CPair.le_trans hxh (Or.inl (CPair.oneValue_symm hov)))
    | Or.inr (Or.inr hlt) => exact hrest hlt x hbx hxh

/-- The determinant off the sum's unit at a pivot and at its
deflation puts the whole list's determinant off the unit: the pivot's
determinant against the deflation's is the pivot's power against the
joined blocks' (`lem:inertia`'s determinant split at a nonsingular
principal pivot), the joined blocks are the list at the places
(`inertia.selM_blockJoin`), and a permutation's selection keeps the
determinant off the unit (`elim.minor_selM_perm_off`). -/
theorem rootfree_of_defl {o : Nat} (M : elim.Mat) (idx cpl : List Nat)
    (hM : elim.sqAt M o) (hMsym : elim.matOneValue (elim.transposeM M) M)
    (hk0 : 0 < idx.length)
    (hlen : (idx ++ cpl).length = o)
    (hb : ((idx ++ cpl).all (fun k => Nat.blt k o)) = true)
    (Cw : elim.Mat) (hCl : Cw.length = idx.length) (hCr : elim.rowsLen cpl.length Cw)
    (hPw : elim.matOneValue (elim.matMul (elim.selM idx idx M) Cw)
      (inertia.matScaleB (elim.minor (elim.selM idx idx M)) (elim.selM idx cpl M)))
    (hPnz : ¬ (elim.minor (elim.selM idx idx M)).oneValue BPair.unit)
    (hD : ¬ (elim.minor (inertia.deflMat (elim.selM idx idx M) (elim.selM idx cpl M)
      (elim.selM cpl cpl M) Cw)).oneValue BPair.unit) :
    ¬ (elim.minor M).oneValue BPair.unit := by
  have hsplit := hb
  rw [ground.all_append] at hsplit
  have hidx : (idx.all (fun k => Nat.blt k o)) = true := (ground.andSplitB hsplit).1
  have hcpl : (cpl.all (fun k => Nat.blt k o)) = true := (ground.andSplitB hsplit).2
  have hPsq : elim.sqAt (elim.selM idx idx M) idx.length :=
    elim.sqAt_of (elim.length_selM _ _ _) (elim.rowsLen_selM idx _ idx)
  have hPsym := elim.transposeM_selM idx idx M o hM hMsym hk0 hidx hidx
  have hBl : (elim.selM idx cpl M).length = idx.length := elim.length_selM _ _ _
  have hBr : elim.rowsLen cpl.length (elim.selM idx cpl M) := elim.rowsLen_selM cpl M idx
  have hQsq : elim.sqAt (elim.selM cpl cpl M) cpl.length :=
    elim.sqAt_of (elim.length_selM _ _ _) (elim.rowsLen_selM cpl _ cpl)
  have hmd := inertia.minor_deflMat (elim.selM idx idx M) (elim.selM idx cpl M)
    (elim.selM cpl cpl M) Cw hPsq hBl hBr hQsq hCl hCr hPsym hPw hPnz
  have hJ : ¬ (elim.minor (inertia.blockJoin (elim.selM idx idx M)
      (elim.selM idx cpl M) (elim.selM cpl cpl M))).oneValue BPair.unit := by
    intro h0
    apply ground.mulOffUnit hPnz hD
    exact BPair.oneValue_trans hmd
      (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) h0)
        (BPair.mul_unit _))
  have hJsq := inertia.sqAt_selM_blockJoin M idx cpl hk0
  have hSsq : elim.sqAt (elim.selM (idx ++ cpl) (idx ++ cpl) M)
      (idx.length + cpl.length) := by
    refine elim.sqAt_of ((elim.length_selM _ _ _).trans (ground.length_append _ _)) ?_
    rw [← ground.length_append]
    exact elim.rowsLen_selM (idx ++ cpl) M (idx ++ cpl)
  have hS : ¬ (elim.minor (elim.selM (idx ++ cpl) (idx ++ cpl) M)).oneValue BPair.unit := by
    intro h0
    apply hJ
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (elim.minor_congr _ _ hSsq hJsq
        (inertia.selM_blockJoin M idx cpl o hM hMsym hk0 hidx hcpl))) h0
  exact elim.minor_selM_perm_off (idx ++ cpl) M hM hlen hb hS

/-- The determinant off the sum's unit at a pivot off the unit and at
its once-cleared deflation is off the unit at the evaluated pencil:
the doubled deflation is the cleared one at the pivot's determinant
(`inertia.deflMat_scaleP`), its determinant the pivot's power against
the cleared deflation's (`inertia.minor_scaleB`), and the split
closes at the places (`rootfree_of_defl`). -/
theorem pdeflP_rootfree {o : Nat} (S : split.PMat) (K : Nat) (idx : List Nat)
    (hpc : pieceRead o idx) (hsh : pShapeAt S o K) (hk0 : 0 < idx.length)
    (xn : BPair) (xc : Pos)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S xn xc K)) (evalPC S xn xc K))
    (hPnz : ¬ (elim.minor (elim.selM idx idx (evalPC S xn xc K))).oneValue BPair.unit)
    (hD : ¬ (elim.minor (evalPC (pdeflP idx (compl idx o) S) xn xc
      ((idx.length + 1) * K))).oneValue BPair.unit) :
    ¬ (elim.minor (evalPC S xn xc K)).oneValue BPair.unit := by
  have hidx := hpc.1
  have hdix := hpc.2
  have hMsq : elim.sqAt (evalPC S xn xc K) o := evalPC_sqAt hsh xn xc
  have hsgl : (idx ++ compl idx o).length = o := by
    rw [ground.length_append]
    exact compl_length hdix hidx
  have hb : ((idx ++ compl idx o).all (fun k => Nat.blt k o)) = true := by
    rw [ground.all_append, hidx, all_compl idx o]
    rfl
  have hdefl := evalPC_pdeflP S K idx (compl idx o) xn xc hsh hMsym hk0 hidx
    (all_compl idx o)
  have hPw := pdeflW_solve S K idx (compl idx o) xn xc (ent_ble hsh) hk0
  have hCwl : (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K)).length
      = idx.length :=
    (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
  have hCwr : elim.rowsLen (compl idx o).length
      (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K)) :=
    rowsLen_evalPC _ _ _ _ _ (rowsLen_pdeflW idx _ _ hk0)
  obtain ⟨_, _, _, hQsq, _, hTBl, _, _⟩ :=
    pivotBlocks (evalPC S xn xc K) idx (compl idx o) o hMsq hMsym hk0 hidx
      (all_compl idx o)
  have hCt : (elim.transposeM (evalPC (pdeflW idx (compl idx o) S) xn xc
      (idx.length * K))).length = (compl idx o).length :=
    elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0)
  have hDPsq := inertia.sqAt_deflMatP
    (elim.selM idx idx (evalPC S xn xc K))
    (elim.selM idx (compl idx o) (evalPC S xn xc K))
    (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
    (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K))
    (compl idx o).length hTBl hCt (elim.length_selM _ _ _) (elim.rowsLen_selM _ _ _)
  have hDsq := inertia.sqAt_deflMat
    (elim.selM idx idx (evalPC S xn xc K))
    (elim.selM idx (compl idx o) (evalPC S xn xc K))
    (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
    (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K))
    (compl idx o).length hTBl hCt (elim.sqAt_len hQsq) (elim.rowsLen_of_sqAt hQsq)
  have hshD := pShape_pdeflP S o K idx (compl idx o) hsh
  have hDP : ¬ (elim.minor (inertia.deflMatP
      (elim.selM idx idx (evalPC S xn xc K))
      (elim.selM idx (compl idx o) (evalPC S xn xc K))
      (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
      (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K)))).oneValue
      BPair.unit := by
    intro h0
    apply hD
    exact BPair.oneValue_trans (elim.minor_congr _ _ (evalPC_sqAt hshD xn xc) hDPsq hdefl) h0
  have hMr : elim.rowsLen (compl idx o).length
      (elim.matMul (elim.transposeM (elim.selM idx (compl idx o) (evalPC S xn xc K)))
        (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K))) :=
    elim.rowsLen_cast hCt (elim.rowsLen_matMul _ _)
  have hscale := inertia.deflMat_scaleP
    (elim.selM idx idx (evalPC S xn xc K))
    (elim.selM idx (compl idx o) (evalPC S xn xc K))
    (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
    (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K))
    (compl idx o).length (elim.rowsLen_of_sqAt hQsq) hMr
  have hDm : ¬ (elim.minor (inertia.deflMat
      (elim.selM idx idx (evalPC S xn xc K))
      (elim.selM idx (compl idx o) (evalPC S xn xc K))
      (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
      (evalPC (pdeflW idx (compl idx o) S) xn xc (idx.length * K)))).oneValue
      BPair.unit := by
    intro h0
    apply ground.mulOffUnit (ground.bpow_off _ hPnz (compl idx o).length) hDP
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (inertia.minor_scaleB (elim.minor (elim.selM idx idx (evalPC S xn xc K))) _ _
        hDPsq)) ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (elim.minor_congr _ _ hDsq (inertia.sqAt_scaleB _ _ _ hDPsq)
        hscale)) h0
  exact rootfree_of_defl (evalPC S xn xc K) idx (compl idx o) hMsq hMsym hk0 hsgl hb
    _ hCwl hCwr hPw hPnz hDm

/-- The determinant off the sum's unit at a pivot off the unit and at
its swapped once-cleared deflation is off the unit at the evaluated
pencil: the swap is the weighting at the one's swap
(`inertia.matSwap_scaleB`), its determinant that weight's power
against the once-cleared deflation's (`inertia.minor_scaleB`), and
the once-cleared read closes (`pdeflP_rootfree`). -/
theorem pdeflM_rootfree {o : Nat} (S : split.PMat) (K : Nat) (idx : List Nat)
    (hpc : pieceRead o idx) (hsh : pShapeAt S o K) (hk0 : 0 < idx.length)
    (xn : BPair) (xc : Pos)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S xn xc K)) (evalPC S xn xc K))
    (hPnz : ¬ (elim.minor (elim.selM idx idx (evalPC S xn xc K))).oneValue BPair.unit)
    (hD : ¬ (elim.minor (evalPC (pdeflM idx (compl idx o) S) xn xc
      ((idx.length + 1) * K))).oneValue BPair.unit) :
    ¬ (elim.minor (evalPC S xn xc K)).oneValue BPair.unit := by
  refine pdeflP_rootfree S K idx hpc hsh hk0 xn xc hMsym hPnz (fun h0 => hD ?_)
  have hPsq : elim.sqAt (evalPC (pdeflP idx (compl idx o) S) xn xc ((idx.length + 1) * K))
      (compl idx o).length :=
    evalPC_sqAt (pShape_pdeflP S o K idx (compl idx o) hsh) xn xc
  have hMsq : elim.sqAt (evalPC (pdeflM idx (compl idx o) S) xn xc ((idx.length + 1) * K))
      (compl idx o).length :=
    evalPC_sqAt (pShape_pdeflM S o K idx (compl idx o) hsh) xn xc
  refine BPair.oneValue_trans
    (elim.minor_congr _ _ hMsq (elim.sqAt_matSwap _ _ hPsq)
      (elim.matOne_trans (evalPC_pcongr xn xc _ (pdeflM_swap idx (compl idx o) S))
        (evalPC_pswapM xn xc _ _))) ?_
  refine BPair.oneValue_trans
    (elim.minor_congr _ _ (elim.sqAt_matSwap _ _ hPsq) (inertia.sqAt_scaleB _ _ _ hPsq)
      (inertia.matSwap_scaleB _)) ?_
  refine BPair.oneValue_trans (inertia.minor_scaleB _ _ _ hPsq) ?_
  exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) h0) (BPair.mul_unit _)

/-- The determinant off the sum's unit at a vacant-coupling pivot and
at its trailing block is off the unit at the evaluated pencil: the
once-cleared deflation is the trailing block at the pivot's
determinant (`diag_defl`), its determinant the determinant's power
against the block's (`inertia.minor_scaleB`), and the once-cleared
read closes (`pdeflP_rootfree`). -/
theorem pselM_rootfree {o : Nat} (S : split.PMat) (K : Nat) (i : Nat)
    (hpc : pieceRead o [i]) (hsh : pShapeAt S o K)
    (hoff : coupVac S o i = true)
    (xn : BPair) (xc : Pos)
    (hMsym : elim.matOneValue (elim.transposeM (evalPC S xn xc K)) (evalPC S xn xc K))
    (hPnz : ¬ (elim.minor (elim.selM [i] [i] (evalPC S xn xc K))).oneValue BPair.unit)
    (hD : ¬ (elim.minor (evalPC (split.pselM (compl [i] o) (compl [i] o) S) xn xc K)).oneValue
      BPair.unit) :
    ¬ (elim.minor (evalPC S xn xc K)).oneValue BPair.unit := by
  have hidx := hpc.1
  have hMsq : elim.sqAt (evalPC S xn xc K) o := evalPC_sqAt hsh xn xc
  have hk0 : 0 < ([i] : List Nat).length := Nat.succ_pos 0
  obtain ⟨_, _, _, hQsq, _, hTBl, _, _⟩ :=
    pivotBlocks (evalPC S xn xc K) [i] (compl [i] o) o hMsq hMsym hk0 hidx
      (all_compl [i] o)
  have hCwl : (evalPC (pdeflW [i] (compl [i] o) S) xn xc
      (([i] : List Nat).length * K)).length = ([i] : List Nat).length :=
    (length_evalPC _ _ _ _).trans (length_pdeflW _ _ _)
  have hCwr : elim.rowsLen (compl [i] o).length
      (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K)) :=
    rowsLen_evalPC _ _ _ _ _ (rowsLen_pdeflW [i] _ _ hk0)
  have hCt : (elim.transposeM (evalPC (pdeflW [i] (compl [i] o) S) xn xc
      (([i] : List Nat).length * K))).length = (compl [i] o).length :=
    elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0)
  have hdefl := evalPC_pdeflP (o := o) S K [i] (compl [i] o) xn xc hsh hMsym hk0 hidx
    (all_compl [i] o)
  have hone := diag_defl S K i hpc hsh hoff xn xc hMsym
  have hDPsq := inertia.sqAt_deflMatP
    (elim.selM [i] [i] (evalPC S xn xc K))
    (elim.selM [i] (compl [i] o) (evalPC S xn xc K))
    (elim.selM (compl [i] o) (compl [i] o) (evalPC S xn xc K))
    (evalPC (pdeflW [i] (compl [i] o) S) xn xc (([i] : List Nat).length * K))
    (compl [i] o).length hTBl hCt (elim.sqAt_len hQsq) (elim.rowsLen_of_sqAt hQsq)
  have hD0 : ¬ (elim.minor (elim.selM (compl [i] o) (compl [i] o)
      (evalPC S xn xc K))).oneValue BPair.unit := by
    rw [selM_evalPC xn xc K S (compl [i] o) (compl [i] o)]
    exact hD
  have hshD := pShape_pdeflP S o K [i] (compl [i] o) hsh
  refine pdeflP_rootfree S K [i] hpc hsh hk0 xn xc hMsym hPnz (fun h0 => ?_)
  apply ground.mulOffUnit (ground.bpow_off _ hPnz (compl [i] o).length) hD0
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (inertia.minor_scaleB (elim.minor (elim.selM [i] [i] (evalPC S xn xc K))) _ _
      hQsq)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (elim.minor_congr _ _ hDPsq (inertia.sqAt_scaleB _ _ _ hQsq) hone)) ?_
  exact BPair.oneValue_trans (BPair.oneValue_symm
    (elim.minor_congr _ _ (evalPC_sqAt hshD xn xc) hDPsq hdefl)) h0

/-- The cover's read is the determinant's root-freeness at a pencil
symmetric at every point of the segment: at every point of an
occupied segment covered at the pieces the evaluated pencil's
determinant sits off the sum's unit, each piece's designated minor
keeping its side there and the cover beneath it reading the
deflation's determinant off the unit (`lem:cellcount`). -/
theorem cover_rootfreeP : ∀ (cov : Cover) (o : Nat) (S : split.PMat)
    (K : Nat) (lo hi : CPair), coverRead S o K lo hi cov →
    pShapeAt S o K →
    (∀ (zn : BPair) (zc : Pos),
      lo ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ hi →
      elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K)) →
    lo < hi →
    ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ hi →
    ¬ (elim.minor (evalPC S zn zc K)).oneValue BPair.unit
  | .done, _, _, _, _, _, h, _, _, hlt, _, _, _, _ =>
    (CPair.not_lt_of_one h hlt).elim
  | .nought, o, S, K, _, _, h, hsh, _, _, zn, zc, _, _ => by
    have h0 : o = 0 := ground.beqEq _ _ h
    subst h0
    have hl : (evalPC S zn zc K).length = 0 :=
      (length_evalPC S zn zc K).trans (pShape_len hsh)
    revert hl
    match evalPC S zn zc K with
    | [] => intro _; decide
    | _ :: _ => intro hl; exact Nat.noConfusion hl
  | .one b i true N D sub rest, o, S, K, lo, hi, h, hsh, hsymF, _, zn, zc, hlz, hzh => by
    have hs : stage.keepUpper (split.pminor (split.pselM [i] [i] S)) lo b N D :=
      h.2.1
    have hsub : coverRead (pdeflP [i] (compl [i] o) S) (o - 1) (2 * K) lo b sub :=
      h.2.2.1
    have hlt : lo < b := hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi := cover_le rest o S K b hi h.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans (congrArg (fun t => t - 1) hsum)
    have hshS : pShapeAt (pdeflP [i] (compl [i] o) S) (o - 1) (2 * K) := by
      have h1 := pShape_pdeflP S o K [i] (compl [i] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM (evalPC (pdeflP [i] (compl [i] o) S) zn zc (2 * K)))
          (evalPC (pdeflP [i] (compl [i] o) S) zn zc (2 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflP_symm S K [i] (compl [i] o) zn zc hsh (hsymB zn zc hlz hzb)
          (Nat.succ_pos 0) h.1.1 (all_compl [i] o)
          (side_one S K lo b i true N D hsh h.1.1 hs zn zc hlz hzb
            (hsymB zn zc hlz hzb)).1
    refine seg_split (fun y => ¬ (elim.minor (evalPC S y.1 y.2 K)).oneValue BPair.unit)
      lo b hi ?_ ?_ ⟨zn, zc⟩ hlz hzh
    · intro y hly hyb
      obtain ⟨yn, yc⟩ := y
      have hsd := side_one S K lo b i true N D hsh h.1.1 hs yn yc hly hyb
        (hsymB yn yc hly hyb)
      have hD := cover_rootfreeP sub (o - 1) (pdeflP [i] (compl [i] o) S) (2 * K)
        lo b hsub hshS hDsymF hlt yn yc hly hyb
      exact pdeflP_rootfree S K [i] h.1 hsh (Nat.succ_pos 0) yn yc
        (hsymB yn yc hly hyb) hsd.1 hD
    · intro hlt' y hby hyh
      obtain ⟨yn, yc⟩ := y
      exact cover_rootfreeP rest o S K b hi h.2.2.2 hsh
        (fun zn zc hbz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hbz) hzh)
        hlt' yn yc hby hyh
  | .one b i false N D sub rest, o, S, K, lo, hi, h, hsh, hsymF, _, zn, zc, hlz, hzh => by
    have hs : stage.keepLower (split.pminor (split.pselM [i] [i] S)) lo b N D :=
      h.2.1
    have hsub : coverRead (pdeflM [i] (compl [i] o) S) (o - 1) (2 * K) lo b sub :=
      h.2.2.1
    have hlt : lo < b := hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi := cover_le rest o S K b hi h.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans (congrArg (fun t => t - 1) hsum)
    have hshS : pShapeAt (pdeflM [i] (compl [i] o) S) (o - 1) (2 * K) := by
      have h1 := pShape_pdeflM S o K [i] (compl [i] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM (evalPC (pdeflM [i] (compl [i] o) S) zn zc (2 * K)))
          (evalPC (pdeflM [i] (compl [i] o) S) zn zc (2 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflM_symm S K [i] (compl [i] o) zn zc hsh (hsymB zn zc hlz hzb)
          (Nat.succ_pos 0) h.1.1 (all_compl [i] o)
          (side_one S K lo b i false N D hsh h.1.1 hs zn zc hlz hzb
            (hsymB zn zc hlz hzb)).1
    refine seg_split (fun y => ¬ (elim.minor (evalPC S y.1 y.2 K)).oneValue BPair.unit)
      lo b hi ?_ ?_ ⟨zn, zc⟩ hlz hzh
    · intro y hly hyb
      obtain ⟨yn, yc⟩ := y
      have hsd := side_one S K lo b i false N D hsh h.1.1 hs yn yc hly hyb
        (hsymB yn yc hly hyb)
      have hD := cover_rootfreeP sub (o - 1) (pdeflM [i] (compl [i] o) S) (2 * K)
        lo b hsub hshS hDsymF hlt yn yc hly hyb
      exact pdeflM_rootfree S K [i] h.1 hsh (Nat.succ_pos 0) yn yc
        (hsymB yn yc hly hyb) hsd.1 hD
    · intro hlt' y hby hyh
      obtain ⟨yn, yc⟩ := y
      exact cover_rootfreeP rest o S K b hi h.2.2.2 hsh
        (fun zn zc hbz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hbz) hzh)
        hlt' yn yc hby hyh
  | .mixed b i j N D sub rest, o, S, K, lo, hi, h, hsh, hsymF, _, zn, zc, hlz, hzh => by
    have hs : stage.keepLower (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D :=
      h.2.1
    have hsub : coverRead (pdeflM [i, j] (compl [i, j] o) S) (o - 2) (3 * K) lo b sub :=
      h.2.2.1
    have hlt : lo < b := hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi := cover_le rest o S K b hi h.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans (congrArg (fun t => t - 2) hsum)
    have hshS : pShapeAt (pdeflM [i, j] (compl [i, j] o) S) (o - 2) (3 * K) := by
      have h1 := pShape_pdeflM S o K [i, j] (compl [i, j] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM (evalPC (pdeflM [i, j] (compl [i, j] o) S) zn zc (3 * K)))
          (evalPC (pdeflM [i, j] (compl [i, j] o) S) zn zc (3 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflM_symm S K [i, j] (compl [i, j] o) zn zc hsh
          (hsymB zn zc hlz hzb) (Nat.succ_pos 1) h.1.1 (all_compl [i, j] o)
          (side_mixed S K lo b i j N D hsh h.1.1 hs zn zc hlz hzb
            (hsymB zn zc hlz hzb)).1
    refine seg_split (fun y => ¬ (elim.minor (evalPC S y.1 y.2 K)).oneValue BPair.unit)
      lo b hi ?_ ?_ ⟨zn, zc⟩ hlz hzh
    · intro y hly hyb
      obtain ⟨yn, yc⟩ := y
      have hsd := side_mixed S K lo b i j N D hsh h.1.1 hs yn yc hly hyb
        (hsymB yn yc hly hyb)
      have hD := cover_rootfreeP sub (o - 2) (pdeflM [i, j] (compl [i, j] o) S) (3 * K)
        lo b hsub hshS hDsymF hlt yn yc hly hyb
      exact pdeflM_rootfree S K [i, j] h.1 hsh (Nat.succ_pos 1) yn yc
        (hsymB yn yc hly hyb) hsd.1 hD
    · intro hlt' y hby hyh
      obtain ⟨yn, yc⟩ := y
      exact cover_rootfreeP rest o S K b hi h.2.2.2 hsh
        (fun zn zc hbz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hbz) hzh)
        hlt' yn yc hby hyh
  | .twoUp b i j N D eUp eN eD sub rest, o, S, K, lo, hi, h, hsh, hsymF, _, zn, zc,
      hlz, hzh => by
    have hs : stage.keepUpper (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D :=
      h.2.1
    have hsub : coverRead (pdeflP [i, j] (compl [i, j] o) S) (o - 2) (3 * K) lo b sub :=
      h.2.2.2.1
    have hlt : lo < b := hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi :=
      cover_le rest o S K b hi h.2.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans (congrArg (fun t => t - 2) hsum)
    have hshS : pShapeAt (pdeflP [i, j] (compl [i, j] o) S) (o - 2) (3 * K) := by
      have h1 := pShape_pdeflP S o K [i, j] (compl [i, j] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM
            (evalPC (pdeflP [i, j] (compl [i, j] o) S) zn zc (3 * K)))
          (evalPC (pdeflP [i, j] (compl [i, j] o) S) zn zc (3 * K)) :=
      fun zn zc hlz hzb =>
        evalPC_pdeflP_symm S K [i, j] (compl [i, j] o) zn zc hsh
          (hsymB zn zc hlz hzb) (Nat.succ_pos 1) h.1.1 (all_compl [i, j] o)
          (side_twoUp S K lo b i j N D eUp eN eD hsh h.1.1 h.2.1 h.2.2.1
            zn zc hlz hzb (hsymB zn zc hlz hzb)).1
    refine seg_split (fun y => ¬ (elim.minor (evalPC S y.1 y.2 K)).oneValue BPair.unit)
      lo b hi ?_ ?_ ⟨zn, zc⟩ hlz hzh
    · intro y hly hyb
      obtain ⟨yn, yc⟩ := y
      have hsd := side_twoUp S K lo b i j N D eUp eN eD hsh h.1.1 h.2.1 h.2.2.1
        yn yc hly hyb (hsymB yn yc hly hyb)
      have hD := cover_rootfreeP sub (o - 2) (pdeflP [i, j] (compl [i, j] o) S) (3 * K)
        lo b hsub hshS hDsymF hlt yn yc hly hyb
      exact pdeflP_rootfree S K [i, j] h.1 hsh (Nat.succ_pos 1) yn yc
        (hsymB yn yc hly hyb) hsd.1 hD
    · intro hlt' y hby hyh
      obtain ⟨yn, yc⟩ := y
      exact cover_rootfreeP rest o S K b hi h.2.2.2.2 hsh
        (fun zn zc hbz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hbz) hzh)
        hlt' yn yc hby hyh
  | .diag b i up N D sub rest, o, S, K, lo, hi, h, hsh, hsymF, _, zn, zc, hlz, hzh => by
    have hs : (if up = true
        then stage.keepUpper (split.pminor (split.pselM [i] [i] S)) lo b N D
        else stage.keepLower (split.pminor (split.pselM [i] [i] S)) lo b N D) :=
      h.2.1
    have hoff : coupVac S o i = true := h.2.2.1
    have hsub : coverRead (split.pselM (compl [i] o) (compl [i] o) S) (o - 1) K lo b sub :=
      h.2.2.2.1
    have hlt : lo < b := by
      match up, hs with
      | true, hs => exact hs.2.1
      | false, hs => exact hs.2.1
    have hi0 : i < o := ground.bltLt (ground.andSplitB h.1.1).1
    have hbhi : b ≤ hi :=
      cover_le rest o S K b hi h.2.2.2.2 (Nat.zero_lt_of_lt hi0)
    have hsymB : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue (elim.transposeM (evalPC S zn zc K)) (evalPC S zn zc K) :=
      fun zn zc hlz hzb => hsymF zn zc hlz (CPair.le_trans hzb hbhi)
    have hsum := compl_length h.1.2 h.1.1
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans (congrArg (fun t => t - 1) hsum)
    have hshS : pShapeAt (split.pselM (compl [i] o) (compl [i] o) S) (o - 1) K := by
      rw [← hcl]
      exact pShape_pselM S K (compl [i] o) (ent_ble hsh)
    have hDsymF : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
        (⟨zn, zc⟩ : CPair) ≤ b →
        elim.matOneValue
          (elim.transposeM
            (evalPC (split.pselM (compl [i] o) (compl [i] o) S) zn zc K))
          (evalPC (split.pselM (compl [i] o) (compl [i] o) S) zn zc K) := by
      intro zn zc hlz hzb
      rw [← selM_evalPC zn zc K S (compl [i] o) (compl [i] o)]
      rcases Nat.eq_zero_or_pos (compl [i] o).length with hz | hpos
      · cases hc : compl [i] o with
        | nil => exact trivial
        | cons c cs =>
          rw [hc] at hz
          exact Nat.noConfusion hz
      · exact elim.transposeM_selM _ _ _ o (evalPC_sqAt hsh zn zc)
          (hsymB zn zc hlz hzb) hpos (all_compl [i] o) (all_compl [i] o)
    refine seg_split (fun y => ¬ (elim.minor (evalPC S y.1 y.2 K)).oneValue BPair.unit)
      lo b hi ?_ ?_ ⟨zn, zc⟩ hlz hzh
    · intro y hly hyb
      obtain ⟨yn, yc⟩ := y
      have hsd := side_diag S K lo b i up N D hsh h.1.1 hs yn yc hly hyb
        (hsymB yn yc hly hyb)
      have hD := cover_rootfreeP sub (o - 1) (split.pselM (compl [i] o) (compl [i] o) S) K
        lo b hsub hshS hDsymF hlt yn yc hly hyb
      exact pselM_rootfree S K i h.1 hsh hoff yn yc (hsymB yn yc hly hyb) hsd.1 hD
    · intro hlt' y hby hyh
      obtain ⟨yn, yc⟩ := y
      exact cover_rootfreeP rest o S K b hi h.2.2.2.2 hsh
        (fun zn zc hbz hzh => hsymF zn zc (CPair.le_trans (Or.inr hlt) hbz) hzh)
        hlt' yn yc hby hyh

/-- The cover's read at a symmetric pencil is the determinant's
root-freeness over the segment (`lem:cellcount`): `cover_rootfreeP`
at the pencil's symmetry read. -/
theorem cover_rootfree {o : Nat} (S : split.PMat) (K : Nat)
    (lo hi : CPair) (cov : Cover)
    (hc : coverRead S o K lo hi cov) (hsh : pShapeAt S o K)
    (hsym : split.pSymAt S o) (hlt : lo < hi)
    (zn : BPair) (zc : Pos)
    (hlz : lo ≤ (⟨zn, zc⟩ : CPair)) (hzh : (⟨zn, zc⟩ : CPair) ≤ hi) :
    ¬ (elim.minor (evalPC S zn zc K)).oneValue BPair.unit :=
  cover_rootfreeP cov o S K lo hi hc hsh
    (fun zn zc _ _ => elim.matOne_symm
      (evalPC_symAt S o K zn zc (pShape_len hsh) (pShape_rows hsh) hsym))
    hlt zn zc hlz hzh


/-- The direction's quadratic-form polynomial: the pencil read
against the vector both sides, the coefficient family folded into
each row and the rows' fold read against it again. -/
def quadP (S : split.PMat) (u : List ground.BPair) : poly.Poly :=
  poly.scaleDot u (S.map (fun r => poly.scaleDot u r))

/-- The cleared evaluation of a coefficient fold is the evaluated
family's own fold: the scales ride outside and the sums split. -/
private theorem evalClear_scaleDot (ln : BPair) (c : Pos) (K : Nat) :
    ∀ (u : List BPair) (ps : List Poly),
      (poly.evalClear (poly.scaleDot u ps) ln c K).oneValue
        (elim.dotP u (ps.map (fun p => poly.evalClear p ln c K)))
  | [], _ => BPair.oneValue_refl _
  | _ :: _, [] => BPair.oneValue_refl _
  | a :: u, p :: ps => by
    show (poly.evalClear
        (poly.add (poly.scaleP a p) (poly.scaleDot u ps)) ln c K).oneValue
      (a * poly.evalClear p ln c K
        + elim.dotP u (ps.map (fun q => poly.evalClear q ln c K)))
    exact BPair.oneValue_trans
      (evalClear_add (poly.scaleP a p) (poly.scaleDot u ps) ln c K)
      (BPair.add_congr (evalClear_scaleP a p ln c K)
        (evalClear_scaleDot ln c K u ps))

/-- The quadratic-form polynomial's degree sits within the shape
read's clearing power, the fold's bound at the entries' own. -/
private theorem quadP_len {S : split.PMat} {o K : Nat}
    (hsh : pShapeAt S o K) (u : List BPair) :
    (quadP S u).length ≤ K + 1 := by
  refine poly.scaleDot_len_le u (S.map (fun r => poly.scaleDot u r))
    (fun j hj => ?_)
  rw [ground.length_map] at hj
  rw [ground.getAt_map ([] : List Poly) ([] : Poly)
    (fun r => poly.scaleDot u r) S j hj]
  exact poly.scaleDot_len_le u (ground.getAt ([] : List Poly) S j)
    (fun i _ => ent_ble hsh j i)

/-- The quadratic-form polynomial's cleared evaluation is the
evaluated pencil's own quadratic form at the direction. -/
theorem evalClear_quadP (S : split.PMat) (K : Nat)
    (u : List ground.BPair) (ln : ground.BPair) (c : ground.Pos) :
    (poly.evalClear (quadP S u) ln c K).oneValue
      (elim.dotN u (elim.matVec (evalPC S ln c K) u)) := by
  refine BPair.oneValue_trans
    (evalClear_scaleDot ln c K u (S.map (fun r => poly.scaleDot u r)))
    (BPair.oneValue_trans ?_
      (BPair.oneValue_symm (elim.quadP_read (evalPC S ln c K) u)))
  rw [ground.map_map (fun r => poly.scaleDot u r)
      (fun p => poly.evalClear p ln c K) S,
    show (evalPC S ln c K).map (fun r => elim.dotP r u)
        = S.map (fun r =>
            elim.dotP (r.map (fun p => poly.evalClear p ln c K)) u) from
      ground.map_map _ _ S]
  exact elim.dotP_oneValue_right u _ _
    (poly.oneValue_map _ _ S (fun r _ =>
      BPair.oneValue_trans (evalClear_scaleDot ln c K u r)
        (BPair.oneValue_of_eq
          (elim.dotP_comm u
            (r.map (fun p => poly.evalClear p ln c K))))))

/-- At an off-unit count the lower list is occupied and its leading
witness reads the split's own order. -/
private theorem lower_head {o : Nat} (S : split.PMat) (K : Nat)
    (bn : BPair) (bc : Pos) (spb : inertia.Split o)
    (hb : inertia.splitRead (evalPC S bn bc K) spb)
    (hz : ¬ inertia.revAt spb = 0) :
    0 < (inertia.lowerList spb).length
      ∧ (ground.getAt ([] : List BPair)
          (inertia.lowerList spb) 0).length = o := by
  have hpos : 0 < (inertia.lowerList spb).length := by
    rw [inertia.lowerList_length (evalPC S bn bc K) spb hb]
    exact Nat.pos_of_ne_zero hz
  exact ⟨hpos, elim.rowsLen_getAt (inertia.lowerList spb) 0
    (inertia.lowerList_rowsLen spb) hpos⟩

/-- The contradiction at the interior point: a witness whose
quadratic-form polynomial sits on its lower side there prices the
cell's own datum below the sum's unit, against the cell's
positive-semidefinite count. -/
private theorem boundary_core {o : Nat} (S : split.PMat) (K : Nat)
    (tn : BPair) (tc : Pos) (spt : inertia.Split o)
    (hsh : pShapeAt S o K)
    (ht : inertia.splitRead (evalPC S tn tc K) spt)
    (hpsd : inertia.psdAt spt)
    (u0 : List BPair) (hu0 : u0.length = o)
    (hval : stage.evalC (quadP S u0) ⟨tn, tc⟩ < stage.unitC) : False := by
  have hdn : poly.evalClear (quadP S u0) tn tc K < BPair.unit :=
    sideDown_shift (quadP S u0) tn tc K (quadP_len hsh u0)
      (sideDown_rep (quadP S u0) tn tc hval)
  have hdot : elim.dotN u0 (elim.matVec (evalPC S tn tc K) u0) < BPair.unit :=
    BPair.lt_congr (evalClear_quadP S K u0 tn tc)
      (BPair.oneValue_refl BPair.unit) hdn
  exact absurd hdot
    (inertia.psd_all (evalPC S tn tc K) spt ht hpsd u0 hu0)

/-- `lem:cellcount`'s boundary clause at the segment's foot: a stage
point beside a positive-semidefinite cell reads positive
semidefinite at its own split, every lower witness's quadratic-form
polynomial priced on its lower side across the segment
(`stage.keepLower`, the boundary point the priced endpoint). -/
theorem boundary_psd_lo {o : Nat} (S : split.PMat) (K : Nat)
    (bn : ground.BPair) (bc : ground.Pos) (tn : ground.BPair)
    (tc : ground.Pos) (N D : ground.BPair) (spb spt : inertia.Split o)
    (hsh : pShapeAt S o K)
    (hb : inertia.splitRead (evalPC S bn bc K) spb)
    (ht : inertia.splitRead (evalPC S tn tc K) spt)
    (hpsd : inertia.psdAt spt)
    (htie : ((inertia.lowerList spb).all (fun u => decide
      (stage.keepLower (quadP S u) ⟨bn, bc⟩ ⟨tn, tc⟩ N D))) = true) :
    inertia.psdAt spb := by
  by_cases hz : inertia.revAt spb = 0
  · exact hz
  · have hhd := lower_head S K bn bc spb hb hz
    have hkey : stage.keepLower
        (quadP S (ground.getAt ([] : List BPair)
          (inertia.lowerList spb) 0)) ⟨bn, bc⟩ ⟨tn, tc⟩ N D :=
      of_decide_eq_true (ground.all_getAt ([] : List BPair)
        (inertia.lowerList spb) htie 0 hhd.1)
    exact (boundary_core S K tn tc spt hsh ht hpsd _ hhd.2
      (stage.keepLower_all _ ⟨bn, bc⟩ ⟨tn, tc⟩ N D hkey ⟨tn, tc⟩
        (Or.inr hkey.2.1) (CPair.le_refl _))).elim

/-- `lem:cellcount`'s boundary clause at the segment's head: the
same read with the segment's roles exchanged, the boundary point
the upper endpoint and the cell's interior point the lower
(`stage.keepLowerTop`). -/
theorem boundary_psd_hi {o : Nat} (S : split.PMat) (K : Nat)
    (bn : ground.BPair) (bc : ground.Pos) (tn : ground.BPair)
    (tc : ground.Pos) (N D : ground.BPair) (spb spt : inertia.Split o)
    (hsh : pShapeAt S o K)
    (hb : inertia.splitRead (evalPC S bn bc K) spb)
    (ht : inertia.splitRead (evalPC S tn tc K) spt)
    (hpsd : inertia.psdAt spt)
    (htie : ((inertia.lowerList spb).all (fun u => decide
      (stage.keepLowerTop (quadP S u) ⟨tn, tc⟩ ⟨bn, bc⟩ N D))) = true) :
    inertia.psdAt spb := by
  by_cases hz : inertia.revAt spb = 0
  · exact hz
  · have hhd := lower_head S K bn bc spb hb hz
    have hkey : stage.keepLowerTop
        (quadP S (ground.getAt ([] : List BPair)
          (inertia.lowerList spb) 0)) ⟨tn, tc⟩ ⟨bn, bc⟩ N D :=
      of_decide_eq_true (ground.all_getAt ([] : List BPair)
        (inertia.lowerList spb) htie 0 hhd.1)
    exact (boundary_core S K tn tc spt hsh ht hpsd _ hhd.2
      (stage.keepLowerTop_all _ ⟨tn, tc⟩ ⟨bn, bc⟩ N D hkey ⟨tn, tc⟩
        (CPair.le_refl _) (Or.inr hkey.2.1))).elim

set_option genInjectivity false in
/-- The divisor's certificate data: the squarefree part's gcd and
Bézout witnesses. -/
structure DivCert where
  g : Poly
  a : Poly
  b : Poly
  u : Poly
  v : Poly
  sq : Poly
  u2 : Poly
  v2 : Poly
  cg : Pos
  cA : Pos
  cB : Pos
  cS : Pos
  cb : BPair
  c2 : BPair

/-- The divisor's witness read: the squarefree part at the gcd's
data, the certificate's fields at `lem:stagesplit`'s read. -/
def divRead (D : Poly) (ct : DivCert) : Prop :=
  stagesplit.sqfreeRead D ct.g ct.a ct.b ct.sq ct.u ct.v ct.u2 ct.v2
    ct.cg ct.cA ct.cB ct.cS ct.cb ct.c2

instance instCellcount4 (D : Poly) (ct : DivCert) : Decidable (divRead D ct) :=
  inferInstanceAs
    (Decidable (stagesplit.sqfreeRead _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))

/-- The divisor's certificate read is one value across the
divisor's representatives (`stagesplit.sqfreeRead_congr`). -/
theorem divRead_congr {D D' : Poly} (h : poly.oneValue D D')
    (ct : DivCert) : divRead D ct ↔ divRead D' ct :=
  stagesplit.sqfreeRead_congr h ct.g ct.a ct.b ct.sq ct.u ct.v
    ct.u2 ct.v2 ct.cg ct.cA ct.cB ct.cS ct.cb ct.c2


end cellcount
