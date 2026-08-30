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
read, the chain's end reading the pencil's shape at the tied
endpoints (`pieceRead` the one subinterval's frame, the designated
places inside the order and pairwise distinct with the places'
permutation entering the leading position at its decided products).
The constancy theorem `cover_const` reads one integer at every
point of the segment, hence one per piecewise-linearly connected
cell: order one is the priced side read, at order `N` `lem:inertia`
adds at the designated pivot, the pivot's count is the block
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
`lem:inertia`'s deflation lands at the same carrier: the entrywise
calculus passes the cleared evaluation, the pivot's adjugate stands
at orders one and two with its solve (`adj2v_solve`), and the
cleared deflation's evaluation is the evaluated blocks' own
(`pdefl`, `evalPC_pdefl`), the cleared deflation's shape at the
trailing order and the pivot's odd-multiple clearing
(`pShape_pdefl`), and the order-one deflation at value-unit
couplings reading the pivot entry's square on the trailing block
outright (`pdefl_offC`). -/

namespace cellcount
open ground poly elim inertia

/-- The pencil's shape read: square at the stated order with every
entry's degree within the stated clearing power. -/
def pShapeAt (S : split.PMat) (o K : Nat) : Prop :=
  (Nat.beq S.length o
    && S.all (fun r => Nat.beq r.length o
      && r.all (fun p => Nat.ble p.length (K + 1)))) = true

instance (S : split.PMat) (o K : Nat) : Decidable (pShapeAt S o K) :=
  inferInstanceAs (Decidable (_ = _))

/-- The shape read assembled from its three conjunct reads: the
order at the length, the rows at the width, and every entry's
degree within the clearing power. -/
theorem pShapeAt_of {S : split.PMat} {o K : Nat}
    (hlen : S.length = o) (hrows : elim.rowsLen o S)
    (hble : (S.all (fun r => r.all
      (fun p => Nat.ble p.length (K + 1)))) = true) :
    pShapeAt S o K := by
  have hall : (S.all (fun r => Nat.beq r.length o
      && r.all (fun p => Nat.ble p.length (K + 1)))) = true := by
    refine ground.all_of_getAt ([] : List poly.Poly) _ _ (fun k hk => ?_)
    have hrow : (ground.getAt ([] : List poly.Poly) S k).length = o :=
      elim.rowsLen_getAt _ k hrows hk
    have hrble : ((ground.getAt ([] : List poly.Poly) S k).all
        (fun p => Nat.ble p.length (K + 1))) = true :=
      ground.all_getAt ([] : List poly.Poly) _ hble k hk
    show (Nat.beq (ground.getAt ([] : List poly.Poly) S k).length o
      && (ground.getAt ([] : List poly.Poly) S k).all
        (fun p => Nat.ble p.length (K + 1))) = true
    rw [hrow, ground.beqRefl o, hrble]
    rfl
  show (Nat.beq S.length o
    && S.all (fun r => Nat.beq r.length o
      && r.all (fun p => Nat.ble p.length (K + 1)))) = true
  rw [hlen, ground.beqRefl o, hall]
  rfl

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
  have hheads : (levelPMat A B G x y mid).map (fun r => r.map
      (fun p => ground.getAt BPair.unit p 0))
      = inertia.siteDatum (elim.matAdd A (inertia.matScale y G))
        (inertia.matScale x G) := by
    refine ground.map2_getAt_zipWith BPair.unit
      (fun a b => a :: (mid ++ [b])) (fun a b => rfl) _ _
      (by rw [elim.sqAt_len hD, elim.sqAt_len hB]
          exact Nat.le_refl o)
      (fun i hi => ?_)
    rw [elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hD) hi,
      elim.rowsLen_getAt _ i (elim.rowsLen_of_sqAt hB)
        (by rw [elim.sqAt_len hB, ← elim.sqAt_len hD]; exact hi)]
    exact Nat.le_refl o
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
the cleared evaluation (`evalPC_pmatAdd`, `evalPC_pswapM`,
`evalPC_pscaleM`, `evalPC_pmatMul`, the powers splitting at the
factors' own degree reads), the pivot's adjugate stands at orders
one and two over both carriers (`padj2`, `adj2v`) with its solve
`P adj(P) = det P·1` (`adj2v_solve`), and the cleared deflation
`d² Q − d (Bᵀ adj(P) B)` at the selected blocks (`pdefl`) evaluates
to the evaluated blocks' own `inertia.deflMat` at the
adjugate-solved witness, the clearing power `(2k+1) K` at pivot
order `k` (`evalPC_pdefl`). -/

/-- A row's cleared evaluations at a key: the key's own entry evaluated,
a key beyond the row reading the sum's unit at both sides. -/
private theorem getAt_rowEC (ln : BPair) (c : Pos) (K : Nat) :
    ∀ (r : List Poly) (j : Nat),
      ground.getAt BPair.unit (r.map (fun p => poly.evalClear p ln c K)) j
        = poly.evalClear (ground.getAt ([] : Poly) r j) ln c K
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: t, j + 1 => getAt_rowEC ln c K t j

/-- The evaluated matrix's entry at two keys: the site datum's entry
there, cleared at the stated power. -/
theorem getAt_evalPC (ln : BPair) (c : Pos) (K : Nat) :
    ∀ (S : split.PMat) (i j : Nat),
      ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (evalPC S ln c K) i) j
        = poly.evalClear
            (ground.getAt ([] : Poly)
              (ground.getAt ([] : List Poly) S i) j) ln c K
  | [], _, _ => rfl
  | r :: _, 0, j => getAt_rowEC ln c K r j
  | _ :: t, i + 1, j => getAt_evalPC ln c K t i j

/-- The evaluated matrix's row at a key: the row's own entrywise
evaluation. -/
private theorem getAt_evalPCrow (ln : BPair) (c : Pos) (K : Nat) :
    ∀ (S : split.PMat) (i : Nat),
      ground.getAt ([] : List BPair) (evalPC S ln c K) i
        = (ground.getAt ([] : List Poly) S i).map
            (fun p => poly.evalClear p ln c K)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: t, i + 1 => getAt_evalPCrow ln c K t i

/-- The cleared evaluation keeps the row count. -/
private theorem length_evalPC (S : split.PMat) (ln : BPair) (c : Pos)
    (K : Nat) : (evalPC S ln c K).length = S.length :=
  ground.length_map _ S

/-- The cleared evaluation keeps every row's width. -/
private theorem rowsLen_evalPC (n : Nat) (S : split.PMat) (ln : BPair)
    (c : Pos) (K : Nat) (h : elim.rowsLen n S) :
    elim.rowsLen n (evalPC S ln c K) :=
  elim.rowsLen_mapRowsO (fun p => poly.evalClear p ln c K) S n h

/-- The cleared evaluation passes a fold over a key range: the
polynomial family's collected sum reads the evaluated family's,
every summand and the seed within the stated power. -/
private theorem ec_foldRange (ln : BPair) (c : Pos) (N : Nat) :
    ∀ (n : Nat) (f : Nat → Poly) (g : Nat → BPair),
      (∀ l, (f l).length ≤ N + 1) →
      (∀ l, (poly.evalClear (f l) ln c N).oneValue (g l)) →
      ∀ (acc : Poly) (accB : BPair), acc.length ≤ N + 1 →
        (poly.evalClear acc ln c N).oneValue accB →
      (poly.evalClear
          ((List.range n).foldl (fun s l => poly.add s (f l)) acc)
          ln c N).oneValue
        ((List.range n).foldl (fun s l => s + g l) accB)
  | 0, _, _, _, _, _, _, _, hacc => hacc
  | n + 1, f, g, hd, hfg, acc, accB, hal, hacc => by
    rw [ground.range_cons n,
      show ((0 : Nat) :: (List.range n).map (fun j => j + 1)).foldl
          (fun s l => poly.add s (f l)) acc
        = ((List.range n).map (fun j => j + 1)).foldl
          (fun s l => poly.add s (f l)) (poly.add acc (f 0)) from rfl,
      show ((0 : Nat) :: (List.range n).map (fun j => j + 1)).foldl
          (fun s l => s + g l) accB
        = ((List.range n).map (fun j => j + 1)).foldl
          (fun s l => s + g l) (accB + g 0) from rfl,
      ground.foldl_map (fun j => j + 1) (fun s l => poly.add s (f l))
        (List.range n) (poly.add acc (f 0)),
      ground.foldl_map (fun j => j + 1) (fun s l => s + g l)
        (List.range n) (accB + g 0)]
    exact ec_foldRange ln c N n (fun l => f (l + 1)) (fun l => g (l + 1))
      (fun l => hd (l + 1)) (fun l => hfg (l + 1))
      (poly.add acc (f 0)) (accB + g 0)
      (poly.add_len_le acc (f 0) (N + 1) hal (hd 0))
      (BPair.oneValue_trans (evalClear_add acc (f 0) ln c N)
        (BPair.add_congr hacc (hfg 0)))

/-- The range fold at two families' entries is the plain
row-against-column fold, the seed riding outside. -/
private theorem foldRange_dotP :
    ∀ (n : Nat) (u v : List BPair), u.length = n → v.length = n →
      ∀ acc : BPair,
      ((List.range n).foldl (fun s l =>
          s + ground.getAt BPair.unit u l * ground.getAt BPair.unit v l)
        acc).oneValue (acc + elim.dotP u v)
  | 0, [], [], _, _, acc => BPair.oneValue_symm (BPair.add_unit acc)
  | 0, _ :: _, _, h, _, _ => nomatch h
  | 0, [], _ :: _, _, h, _ => nomatch h
  | _ + 1, [], _, h, _, _ => nomatch h
  | _ + 1, _ :: _, [], _, h, _ => nomatch h
  | n + 1, a :: u, b :: v, hu, hv, acc => by
    rw [ground.range_cons n,
      show ((0 : Nat) :: (List.range n).map (fun j => j + 1)).foldl
          (fun s l => s + ground.getAt BPair.unit (a :: u) l
            * ground.getAt BPair.unit (b :: v) l) acc
        = ((List.range n).map (fun j => j + 1)).foldl
          (fun s l => s + ground.getAt BPair.unit (a :: u) l
            * ground.getAt BPair.unit (b :: v) l) (acc + a * b) from rfl,
      ground.foldl_map (fun j => j + 1) _ (List.range n) (acc + a * b)]
    refine BPair.oneValue_trans
      (foldRange_dotP n u v (Nat.succ.inj hu) (Nat.succ.inj hv)
        (acc + a * b)) ?_
    exact BPair.oneValue_of_eq (BPair.add_assoc acc (a * b) (elim.dotP u v))

/-- A fold of sums over a key range stays within the stated degree at
summands and seed within it. -/
private theorem foldRange_len (N : Nat) (f : Nat → Poly)
    (hf : ∀ l, (f l).length ≤ N + 1) :
    ∀ (n : Nat) (acc : Poly), acc.length ≤ N + 1 →
      ((List.range n).foldl (fun s l => poly.add s (f l)) acc).length ≤ N + 1
  | 0, _, hacc => hacc
  | n + 1, acc, hacc => by
    rw [ground.range_cons n,
      show ((0 : Nat) :: (List.range n).map (fun j => j + 1)).foldl
          (fun s l => poly.add s (f l)) acc
        = ((List.range n).map (fun j => j + 1)).foldl
          (fun s l => poly.add s (f l)) (poly.add acc (f 0)) from rfl,
      ground.foldl_map (fun j => j + 1) (fun s l => poly.add s (f l))
        (List.range n) (poly.add acc (f 0))]
    exact foldRange_len N (fun l => f (l + 1)) (fun l => hf (l + 1)) n
      (poly.add acc (f 0)) (poly.add_len_le acc (f 0) (N + 1) hacc (hf 0))

/-- The polynomial product's displayed rows: the column keys at the
second factor's width, each entry the row-against-column fold. -/
private theorem pmatMul_unfold (a b : split.PMat) :
    split.pmatMul a b
      = a.map (fun r => (List.range (b.headD ([] : List Poly)).length).map
        (fun t => (List.range r.length).foldl (fun s l =>
          poly.add s (poly.mul (ground.getAt ([] : Poly) r l)
            (ground.getAt ([] : Poly)
              (ground.getAt ([] : List Poly) b l) t))) [])) := rfl

/-- The polynomial product's row width is the second factor's own. -/
private theorem rowLen_pmatMul (a b : split.PMat) (i : Nat)
    (hi : i < a.length) :
    (ground.getAt ([] : List Poly) (split.pmatMul a b) i).length
      = (b.headD ([] : List Poly)).length := by
  rw [pmatMul_unfold a b,
    ground.getAt_map ([] : List Poly) ([] : List Poly) _ a i hi,
    ground.length_map, ground.length_range]

/-- The product's row width is the second factor's exchanged row count. -/
private theorem rowLen_matMul (X Y : elim.Mat) (i : Nat) (hi : i < X.length) :
    (ground.getAt ([] : List BPair) (elim.matMul X Y) i).length
      = (elim.transposeM Y).length := by
  rw [elim.getAt_matMul X Y i hi, ground.length_map]

/-- The polynomial product's entry: the row-against-column fold over the
row's key range. -/
private theorem getAt_pmatMul (a b : split.PMat) (i j : Nat)
    (hi : i < a.length) (hj : j < (b.headD ([] : List Poly)).length) :
    ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (split.pmatMul a b) i) j
      = (List.range (ground.getAt ([] : List Poly) a i).length).foldl
          (fun s l => poly.add s (poly.mul
            (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) a i) l)
            (ground.getAt ([] : Poly)
              (ground.getAt ([] : List Poly) b l) j))) [] := by
  rw [pmatMul_unfold a b,
    ground.getAt_map ([] : List Poly) ([] : List Poly) _ a i hi,
    ground.getAt_map 0 ([] : Poly) _
      (List.range (b.headD ([] : List Poly)).length)
      j (by rw [ground.length_range]; exact hj),
    ground.getAt_range _ j hj]

/-- The product's entry: the row's fold against the second factor's
column. -/
private theorem entry_matMul (X Y : elim.Mat) (i j : Nat)
    (hi : i < X.length) (hj : j < (elim.transposeM Y).length) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (elim.matMul X Y) i) j
      = elim.dotN (ground.getAt ([] : List BPair) X i)
          (ground.getAt ([] : List BPair) (elim.transposeM Y) j) := by
  rw [elim.getAt_matMul X Y i hi]
  exact ground.getAt_map ([] : List BPair) BPair.unit _ _ j hj

/-- The polynomial product's row count is the first factor's. -/
private theorem length_pmatMul (a b : split.PMat) :
    (split.pmatMul a b).length = a.length := ground.length_map _ a

/-- The polynomial product's rows read the second factor's leading
width. -/
private theorem rowsLen_pmatMul (a b : split.PMat) :
    elim.rowsLen (b.headD ([] : List Poly)).length (split.pmatMul a b) := by
  rw [pmatMul_unfold a b]
  refine elim.rowsLen_map _ _ a (fun r _ => ?_)
  rw [ground.length_map, ground.length_range]

/-- An occupied matrix's leading row reads the stated width. -/
private theorem headD_width : ∀ (b : split.PMat) (w n : Nat),
    b.length = w → 0 < w → elim.rowsLen n b →
    (b.headD ([] : List Poly)).length = n
  | [], w, _, hbl, hw, _ => by
    rw [show w = 0 from hbl.symm] at hw
    exact absurd hw (Nat.lt_irrefl 0)
  | _ :: _, _, _, _, _, hb => hb.1

/-- Every entry's degree sits within the shape read's clearing power, a
key beyond the datum reading the vacant list. -/
theorem ent_ble {S : split.PMat} {o K : Nat} (hsh : pShapeAt S o K) :
    ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1 := by
  intro i j
  have hall : (S.all (fun r => Nat.beq r.length o
      && r.all (fun p => Nat.ble p.length (K + 1)))) = true :=
    (ground.andSplitB
      (show (Nat.beq S.length o && S.all (fun r => Nat.beq r.length o
        && r.all (fun p => Nat.ble p.length (K + 1)))) = true from hsh)).2
  match Nat.lt_or_ge i S.length with
  | Or.inr h =>
    rw [ground.getAt_over ([] : List Poly) S i h]
    exact Nat.zero_le _
  | Or.inl h =>
    have hrow := (ground.andSplitB
      (ground.all_getAt ([] : List Poly) S hall i h)).2
    match Nat.lt_or_ge j (ground.getAt ([] : List Poly) S i).length with
    | Or.inr h2 =>
      rw [ground.getAt_over ([] : Poly) _ j h2]
      exact Nat.zero_le _
    | Or.inl h2 =>
      exact ground.bleLe (ground.all_getAt ([] : Poly) _ hrow j h2)

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

/-- The selected block's entries carry the datum's own degree read. -/
private theorem deg_pselM {S : split.PMat} {K : Nat}
    (hd : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1)
    (I J : List Nat) : ∀ p q, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (split.pselM I J S) p) q).length
        ≤ K + 1 := by
  intro p q
  match Nat.lt_or_ge p I.length with
  | Or.inr h =>
    rw [ground.getAt_over ([] : List Poly) _ p
      (by rw [split.length_pselM]; exact h)]
    exact Nat.zero_le _
  | Or.inl h =>
    match Nat.lt_or_ge q J.length with
    | Or.inr h2 =>
      rw [ground.getAt_over ([] : Poly) _ q
        (by rw [elim.rowsLen_getAt _ p (split.rowsLen_pselM J S I)
          (by rw [split.length_pselM]; exact h)]; exact h2)]
      exact Nat.zero_le _
    | Or.inl h2 =>
      rw [split.getAt_pselM I J S p q h h2]
      exact hd _ _

/-- The polynomial product's entries carry the factors' joined degree. -/
private theorem deg_pmatMul (a b : split.PMat) (K1 K2 : Nat)
    (hda : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) a i) j).length ≤ K1 + 1)
    (hdb : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) b i) j).length ≤ K2 + 1) :
    ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (split.pmatMul a b) i) j).length
        ≤ K1 + K2 + 1 := by
  intro i j
  match Nat.lt_or_ge i a.length with
  | Or.inr h =>
    rw [ground.getAt_over ([] : List Poly) _ i
      (by rw [length_pmatMul]; exact h)]
    exact Nat.zero_le _
  | Or.inl h =>
    match Nat.lt_or_ge j (b.headD ([] : List Poly)).length with
    | Or.inr h2 =>
      rw [ground.getAt_over ([] : Poly) _ j
        (by rw [rowLen_pmatMul a b i h]; exact h2)]
      exact Nat.zero_le _
    | Or.inl h2 =>
      rw [getAt_pmatMul a b i j h h2]
      exact foldRange_len (K1 + K2) _
        (fun l => poly.mul_len_le _ _ K1 K2 (hda i l) (hdb l j)) _ []
        (Nat.zero_le _)

/-- One row of the entrywise sum's cleared evaluation: the two rows'
evaluations summed. -/
private theorem row_pmatAdd (ln : BPair) (c : Pos) (N : Nat) :
    ∀ r s : List Poly,
      poly.oneValue
        ((List.zipWith poly.add r s).map (fun p => poly.evalClear p ln c N))
        (elim.vecAdd (r.map (fun p => poly.evalClear p ln c N))
          (s.map (fun p => poly.evalClear p ln c N)))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | p :: r, q :: s => ⟨evalClear_add p q ln c N, row_pmatAdd ln c N r s⟩

/-- The entrywise sum's cleared evaluation is the evaluations' own sum. -/
private theorem evalPC_pmatAdd (ln : BPair) (c : Pos) (N : Nat) :
    ∀ A B : split.PMat,
      elim.matOneValue (evalPC (split.pmatAdd A B) ln c N)
        (elim.matAdd (evalPC A ln c N) (evalPC B ln c N))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | r :: A, s :: B => ⟨row_pmatAdd ln c N r s, evalPC_pmatAdd ln c N A B⟩

/-- One row of the memberwise swap's cleared evaluation: the row's
evaluations swapped. -/
private theorem row_pswapM (ln : BPair) (c : Pos) (N : Nat) :
    ∀ r : List Poly,
      poly.oneValue ((r.map poly.neg).map (fun p => poly.evalClear p ln c N))
        ((r.map (fun p => poly.evalClear p ln c N)).map BPair.swap)
  | [] => trivial
  | p :: r => ⟨evalClear_neg p ln c N, row_pswapM ln c N r⟩

/-- The memberwise swap's cleared evaluation is the evaluation's own
swap. -/
private theorem evalPC_pswapM (ln : BPair) (c : Pos) (N : Nat) :
    ∀ S : split.PMat,
      elim.matOneValue (evalPC (split.pswapM S) ln c N)
        (elim.matSwap (evalPC S ln c N))
  | [] => trivial
  | r :: S => ⟨row_pswapM ln c N r, evalPC_pswapM ln c N S⟩

/-- The memberwise swap keeps every row's width. -/
private theorem rowsLen_pswapM (n : Nat) (S : split.PMat)
    (h : elim.rowsLen n S) : elim.rowsLen n (split.pswapM S) :=
  elim.rowsLen_mapRowsO poly.neg S n h

/-- One row of a rescaling's cleared evaluation: the scale's own
evaluation against the row's, the powers splitting. -/
private theorem row_pscaleM (f : Poly) (ln : BPair) (c : Pos)
    (K1 K2 : Nat) (hf : f.length ≤ K1 + 1) :
    ∀ r : List Poly,
      (∀ j, (ground.getAt ([] : Poly) r j).length ≤ K2 + 1) →
      poly.oneValue
        ((r.map (poly.mul f)).map (fun p => poly.evalClear p ln c (K1 + K2)))
        (poly.scaleP (poly.evalClear f ln c K1)
          (r.map (fun p => poly.evalClear p ln c K2)))
  | [], _ => trivial
  | p :: r, h =>
    ⟨BPair.oneValue_trans
        (evalClear_mul f p ln c K1 K2 hf (h 0))
        (BPair.oneValue_symm (BPair.norm_oneValue _)),
     row_pscaleM f ln c K1 K2 hf r (fun j => h (j + 1))⟩

/-- A rescaling's cleared evaluation is the scale's evaluation weighting
the evaluated matrix, the powers splitting. -/
private theorem evalPC_pscaleM (f : Poly) (ln : BPair) (c : Pos)
    (K1 K2 : Nat) (hf : f.length ≤ K1 + 1) :
    ∀ S : split.PMat,
      (∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) j).length ≤ K2 + 1) →
      elim.matOneValue (evalPC (split.pscaleM f S) ln c (K1 + K2))
        (inertia.matScaleB (poly.evalClear f ln c K1) (evalPC S ln c K2))
  | [], _ => trivial
  | r :: S, h =>
    ⟨row_pscaleM f ln c K1 K2 hf r (fun j => h 0 j),
     evalPC_pscaleM f ln c K1 K2 hf S (fun i j => h (i + 1) j)⟩

/-- The rescaling keeps every row's width. -/
private theorem rowsLen_pscaleM (f : Poly) (n : Nat) (S : split.PMat)
    (h : elim.rowsLen n S) : elim.rowsLen n (split.pscaleM f S) :=
  elim.rowsLen_mapRowsO (poly.mul f) S n h

/-- The polynomial product's cleared evaluation is the evaluated
factors' product, the powers splitting and every entry within its
factor's own. -/
private theorem evalPC_pmatMul (a b : split.PMat) (ln : BPair) (c : Pos)
    (K1 K2 w n : Nat) (ha : elim.rowsLen w a) (hbl : b.length = w)
    (hw : 0 < w) (hb : elim.rowsLen n b)
    (hda : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) a i) j).length ≤ K1 + 1)
    (hdb : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) b i) j).length ≤ K2 + 1) :
    elim.matOneValue (evalPC (split.pmatMul a b) ln c (K1 + K2))
      (elim.matMul (evalPC a ln c K1) (evalPC b ln c K2)) := by
  have hhd : (b.headD ([] : List Poly)).length = n :=
    headD_width b w n hbl hw hb
  have hBvl : (evalPC b ln c K2).length = w :=
    (length_evalPC b ln c K2).trans hbl
  have hBvr : elim.rowsLen n (evalPC b ln c K2) :=
    rowsLen_evalPC n b ln c K2 hb
  have hTl : (elim.transposeM (evalPC b ln c K2)).length = n :=
    elim.length_transposeM (evalPC b ln c K2) hBvr (by rw [hBvl]; exact hw)
  have hTr : elim.rowsLen w (elim.transposeM (evalPC b ln c K2)) := by
    rw [← hBvl]
    exact elim.rowsLen_transposeM (evalPC b ln c K2)
  have hLl : (evalPC (split.pmatMul a b) ln c (K1 + K2)).length = a.length :=
    (length_evalPC _ ln c (K1 + K2)).trans (ground.length_map _ a)
  refine elim.matOne_getAt _ _ ?_ ?_
  · rw [hLl, elim.length_matMul, length_evalPC]
  · intro i hi
    rw [hLl] at hi
    have hiA : i < (evalPC a ln c K1).length := by
      rw [length_evalPC]; exact hi
    have hrowW : (ground.getAt ([] : List Poly) a i).length = w :=
      elim.rowsLen_getAt a i ha hi
    have hUl : (ground.getAt ([] : List BPair) (evalPC a ln c K1) i).length
        = w := by
      rw [getAt_evalPCrow, ground.length_map, hrowW]
    have hLrow : (ground.getAt ([] : List BPair)
        (evalPC (split.pmatMul a b) ln c (K1 + K2)) i).length = n := by
      rw [getAt_evalPCrow, ground.length_map, rowLen_pmatMul a b i hi, hhd]
    have hRrow : (ground.getAt ([] : List BPair)
        (elim.matMul (evalPC a ln c K1) (evalPC b ln c K2)) i).length = n := by
      rw [rowLen_matMul _ _ i hiA, hTl]
    refine poly.oneValue_of_entries _ _ (hLrow.trans hRrow.symm) ?_
    intro j hj
    rw [hLrow] at hj
    have hjT : j < (elim.transposeM (evalPC b ln c K2)).length := by
      rw [hTl]; exact hj
    have hVl : (ground.getAt ([] : List BPair)
        (elim.transposeM (evalPC b ln c K2)) j).length = w :=
      elim.rowsLen_getAt _ j hTr hjT
    rw [getAt_evalPC ln c (K1 + K2) (split.pmatMul a b) i j,
      getAt_pmatMul a b i j hi (by rw [hhd]; exact hj),
      entry_matMul (evalPC a ln c K1) (evalPC b ln c K2) i j hiA hjT,
      hrowW]
    refine BPair.oneValue_trans
      (ec_foldRange ln c (K1 + K2) w
        (fun l => poly.mul
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) a i) l)
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) b l) j))
        (fun l => ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) (evalPC a ln c K1) i) l
          * ground.getAt BPair.unit
            (ground.getAt ([] : List BPair)
              (elim.transposeM (evalPC b ln c K2)) j) l)
        (fun l => poly.mul_len_le _ _ K1 K2 (hda i l) (hdb l j))
        (fun l => ?_) [] BPair.unit (Nat.zero_le _)
        (BPair.oneValue_refl _)) ?_
    · match Nat.lt_or_ge l w with
      | Or.inl hlw =>
        rw [getAt_evalPCrow, getAt_rowEC,
          elim.getAt_transposeM BPair.unit (evalPC b ln c K2) hBvr j l hj
            (by rw [hBvl]; exact hlw),
          getAt_evalPC ln c K2 b l j]
        exact evalClear_mul _ _ ln c K1 K2 (hda i l) (hdb l j)
      | Or.inr hlw =>
        rw [ground.getAt_over ([] : Poly) _ l (by rw [hrowW]; exact hlw),
          ground.getAt_over BPair.unit _ l (by rw [hUl]; exact hlw)]
        exact BPair.oneValue_symm (BPair.unit_mul _)
    · exact BPair.oneValue_trans
        (foldRange_dotP w _ _ hUl hVl BPair.unit)
        (BPair.oneValue_trans (BPair.unit_add _)
          (BPair.oneValue_symm (elim.dotN_read _ _)))

/-- The pivot's adjugate at orders one and two, the cofactor family
displayed. -/
def padj2 : Nat → split.PMat → split.PMat
  | 1, _ => [[poly.one]]
  | 2, P => [[ground.getAt [] (ground.getAt [] P 1) 1,
              poly.neg (ground.getAt [] (ground.getAt [] P 0) 1)],
             [poly.neg (ground.getAt [] (ground.getAt [] P 1) 0),
              ground.getAt [] (ground.getAt [] P 0) 0]]
  | 0, _ => []
  | _ + 3, _ => []

/-- The pivot's adjugate at the evaluated carrier, orders one and
two. -/
def adj2v : Nat → elim.Mat → elim.Mat
  | 1, _ => [[BPair.ofPos .one]]
  | 2, P => [[ground.getAt BPair.unit (ground.getAt [] P 1) 1,
              BPair.swap (ground.getAt BPair.unit (ground.getAt [] P 0) 1)],
             [BPair.swap (ground.getAt BPair.unit (ground.getAt [] P 1) 0),
              ground.getAt BPair.unit (ground.getAt [] P 0) 0]]
  | 0, _ => []
  | _ + 3, _ => []

/-- A list of one key is its entry's own. -/
private theorem list1E {α : Type} : ∀ l : List α, l.length = 1 →
    ∃ a, l = [a]
  | [], h => Nat.noConfusion h
  | [a], _ => ⟨a, rfl⟩
  | _ :: _ :: _, h => Nat.noConfusion (Nat.succ.inj h)

/-- A list of two keys is its two entries' own. -/
private theorem list2E {α : Type} : ∀ l : List α, l.length = 2 →
    ∃ a b, l = [a, b]
  | [], h => Nat.noConfusion h
  | [_], h => Nat.noConfusion (Nat.succ.inj h)
  | [a, b], _ => ⟨a, b, rfl⟩
  | _ :: _ :: _ :: _, h => Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))

/-- The leading entry is the entry at the first key. -/
private theorem headD_getAt : ∀ r : List BPair,
    r.headD BPair.unit = ground.getAt BPair.unit r 0
  | [] => rfl
  | _ :: _ => rfl

/-- The plain fold at one-key families is the entries' product. -/
private theorem dotP_one : ∀ u v : List BPair,
    u.length = 1 → v.length = 1 →
    (elim.dotP u v).oneValue
      (ground.getAt BPair.unit u 0 * ground.getAt BPair.unit v 0)
  | [_], [_], _, _ => BPair.add_unit _
  | [], _, h, _ => Nat.noConfusion h
  | _ :: _ :: _, _, h, _ => Nat.noConfusion (Nat.succ.inj h)
  | [_], [], _, h => Nat.noConfusion h
  | [_], _ :: _ :: _, _, h => Nat.noConfusion (Nat.succ.inj h)

/-- The plain fold at two-key families is the two products' sum. -/
private theorem dotP_two : ∀ u v : List BPair,
    u.length = 2 → v.length = 2 →
    (elim.dotP u v).oneValue
      (ground.getAt BPair.unit u 0 * ground.getAt BPair.unit v 0
        + ground.getAt BPair.unit u 1 * ground.getAt BPair.unit v 1)
  | [_, _], [_, _], _, _ =>
    BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)
  | [], _, h, _ => Nat.noConfusion h
  | [_], _, h, _ => Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _ :: _, _, h, _ =>
    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))
  | [_, _], [], _, h => Nat.noConfusion h
  | [_, _], [_], _, h => Nat.noConfusion (Nat.succ.inj h)
  | [_, _], _ :: _ :: _ :: _, _, h =>
    Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))

/-- The weighted matrix's entry is the weight against the entry, at its
representative. -/
private theorem entry_scaleB (w : BPair) (M : elim.Mat) (i j : Nat)
    (hi : i < M.length)
    (hj : j < (ground.getAt ([] : List BPair) M i).length) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (inertia.matScaleB w M) i) j
      = (w * ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) M i) j).norm := by
  rw [show inertia.matScaleB w M
      = M.map (fun r => r.map (fun x => (w * x).norm)) from rfl,
    ground.getAt_map ([] : List BPair) ([] : List BPair) _ M i hi]
  exact ground.getAt_map BPair.unit BPair.unit _ _ j hj

/-- The order-two minor reads the diagonal product against the exchanged
product's balance partner. -/
private theorem minor2_read (a b c d : BPair) :
    (elim.minor [[a, b], [c, d]]).oneValue (a * d + (b * c).swap) := by
  show (((a * d).norm + (((b * c).norm).swap + BPair.unit).norm).norm).oneValue
    (a * d + (b * c).swap)
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.add_congr (BPair.norm_oneValue _)
      (BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_trans
          (BPair.add_congr (ground.swap_congr (BPair.norm_oneValue _))
            (BPair.oneValue_refl _))
          (BPair.add_unit _))))

/-- The pivot's first row against the adjugate's action: the coupling's
second key cancels at the swapped pair and the first reads the
determinant. -/
private theorem cross2 (a b c d x y : BPair) :
    (a * (d * x + b.swap * y) + b * (c.swap * x + a * y)).oneValue
      ((a * d + (b * c).swap) * x) := by
  have e : a * (d * x + b.swap * y) + b * (c.swap * x + a * y)
      = (a * d + b * c.swap) * x + ((a * b).swap + a * b) * y := by
    rw [BPair.left_distrib a (d * x) (b.swap * y),
      BPair.left_distrib b (c.swap * x) (a * y),
      ← BPair.mul_assoc a d x, ← BPair.mul_assoc a b.swap y,
      ← BPair.mul_assoc b c.swap x, ← BPair.mul_assoc b a y,
      BPair.add_add_comm (a * d * x) (a * b.swap * y) (b * c.swap * x)
        (b * a * y),
      ← BPair.right_distrib (a * d) (b * c.swap) x,
      BPair.mul_swap a b, BPair.mul_comm b a,
      ← BPair.right_distrib ((a * b).swap) (a * b) y]
  rw [e]
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.swap_add_null (BPair.oneValue_refl (a * b))))
      (BPair.unit_mul y))) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.mul_congr_left (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_of_eq (BPair.mul_swap b c)))

/-- The pivot's second row against the adjugate's action: the coupling's
first key cancels at the swapped pair and the second reads the
determinant. -/
private theorem cross2' (a b c d x y : BPair) :
    (c * (d * x + b.swap * y) + d * (c.swap * x + a * y)).oneValue
      ((a * d + (b * c).swap) * y) := by
  have e : c * (d * x + b.swap * y) + d * (c.swap * x + a * y)
      = ((c * d).swap + c * d) * x + ((b * c).swap + a * d) * y := by
    rw [BPair.left_distrib c (d * x) (b.swap * y),
      BPair.left_distrib d (c.swap * x) (a * y),
      ← BPair.mul_assoc c d x, ← BPair.mul_assoc c b.swap y,
      ← BPair.mul_assoc d c.swap x, ← BPair.mul_assoc d a y,
      BPair.add_add_comm (c * d * x) (c * b.swap * y) (d * c.swap * x)
        (d * a * y),
      ← BPair.right_distrib (c * d) (d * c.swap) x,
      ← BPair.right_distrib (c * b.swap) (d * a) y,
      BPair.mul_swap d c, BPair.mul_comm d c,
      BPair.mul_swap c b, BPair.mul_comm c b, BPair.mul_comm d a,
      BPair.add_comm (c * d) ((c * d).swap)]
  rw [e]
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.swap_add_null (BPair.oneValue_refl (c * d))))
      (BPair.unit_mul x))
    (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  exact BPair.mul_congr_left (BPair.add_comm ((b * c).swap) (a * d) ▸
    BPair.oneValue_refl _)

/-- The adjugate's solve at order one. -/
private theorem solve_one {m : Nat} (P B : elim.Mat) (hP : elim.sqAt P 1)
    (hBl : B.length = 1) (hBr : elim.rowsLen m B) :
    elim.matOneValue (elim.matMul P (elim.matMul (adj2v 1 P) B))
      (inertia.matScaleB (elim.minor P) B) := by
  have hPl : P.length = 1 := elim.sqAt_len hP
  have hPr : elim.rowsLen 1 P := elim.rowsLen_of_sqAt hP
  match list1E P hPl with
  | ⟨r, hPe⟩ =>
  subst hPe
  have hrl : r.length = 1 := hPr.1
  have hB0 : 0 < B.length := by rw [hBl]; exact Nat.succ_pos 0
  have hBtl : (elim.transposeM B).length = m :=
    elim.length_transposeM B hBr hB0
  have hCwl : (elim.matMul (adj2v 1 [r]) B).length = 1 :=
    elim.length_matMul _ _
  have hCwr : elim.rowsLen m (elim.matMul (adj2v 1 [r]) B) := by
    rw [← hBtl]
    exact elim.rowsLen_matMul _ _
  have hCw0 : 0 < (elim.matMul (adj2v 1 [r]) B).length := by
    rw [hCwl]; exact Nat.succ_pos 0
  have hCtl : (elim.transposeM (elim.matMul (adj2v 1 [r]) B)).length = m :=
    elim.length_transposeM _ hCwr hCw0
  have hCtr : elim.rowsLen 1
      (elim.transposeM (elim.matMul (adj2v 1 [r]) B)) := by
    rw [← hCwl]
    exact elim.rowsLen_transposeM _
  have hSr : elim.rowsLen m (inertia.matScaleB (elim.minor [r]) B) :=
    inertia.rowsLen_scaleB _ m B hBr
  have hSl : (inertia.matScaleB (elim.minor [r]) B).length = 1 :=
    (inertia.length_scaleB _ B).trans hBl
  refine elim.matOne_getAt _ _ ?_ ?_
  · rw [elim.length_matMul, hSl]
    rfl
  · intro i hi
    rw [elim.length_matMul] at hi
    match i, hi with
    | 0, _ =>
      have hiP : (0 : Nat) < ([r] : elim.Mat).length := Nat.succ_pos 0
      have hi0 : (0 : Nat) < B.length := hB0
      refine poly.oneValue_of_entries _ _ ?_ ?_
      · rw [rowLen_matMul _ _ 0 hiP, hCtl,
          elim.rowsLen_getAt _ 0 hSr (by rw [hSl]; exact Nat.succ_pos 0)]
      · intro j hj
        rw [rowLen_matMul _ _ 0 hiP, hCtl] at hj
        have hjT : j < (elim.transposeM
            (elim.matMul (adj2v 1 [r]) B)).length := by rw [hCtl]; exact hj
        have hjB : j < (elim.transposeM B).length := by rw [hBtl]; exact hj
        rw [entry_matMul _ _ 0 j hiP hjT,
          entry_scaleB (elim.minor [r]) B 0 j hi0
            (by rw [elim.rowsLen_getAt B 0 hBr hi0]; exact hj),
          show elim.minor ([r] : elim.Mat) = ground.getAt BPair.unit r 0
            from headD_getAt r]
        refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
        refine BPair.oneValue_trans
          (dotP_one _ _ hrl (elim.rowsLen_getAt _ j hCtr hjT)) ?_
        rw [elim.getAt_transposeM BPair.unit
            (elim.matMul (adj2v 1 [r]) B) hCwr j 0 hj hCw0,
          entry_matMul (adj2v 1 [r]) B 0 j (Nat.succ_pos 0) hjB]
        refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (elim.dotN_read _ _)
            (dotP_one _ _ rfl (elim.rowsLen_getAt _ j
              (by rw [← hBl]; exact elim.rowsLen_transposeM B) hjB)))) ?_
        rw [elim.getAt_transposeM BPair.unit B hBr j 0 hj hB0]
        refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos Pos.one) _))
            (BPair.mul_one_read _))) ?_
        exact BPair.oneValue_symm (BPair.norm_oneValue _)
    | _ + 1, h => exact absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)

/-- The adjugate's solve at order two. -/
private theorem solve_two {m : Nat} (P B : elim.Mat) (hP : elim.sqAt P 2)
    (hBl : B.length = 2) (hBr : elim.rowsLen m B) :
    elim.matOneValue (elim.matMul P (elim.matMul (adj2v 2 P) B))
      (inertia.matScaleB (elim.minor P) B) := by
  have hPl : P.length = 2 := elim.sqAt_len hP
  have hPr : elim.rowsLen 2 P := elim.rowsLen_of_sqAt hP
  match list2E P hPl with
  | ⟨r0, r1, hPe⟩ =>
  subst hPe
  match list2E r0 hPr.1, list2E r1 hPr.2.1 with
  | ⟨a, b, e0⟩, ⟨c, d, e1⟩ =>
  subst e0
  subst e1
  match list2E B hBl with
  | ⟨b0, b1, hBe⟩ =>
  subst hBe
  have hB0 : 0 < ([b0, b1] : elim.Mat).length := Nat.succ_pos 1
  have hBtl : (elim.transposeM ([b0, b1] : elim.Mat)).length = m :=
    elim.length_transposeM _ hBr hB0
  have hBtr : elim.rowsLen 2 (elim.transposeM ([b0, b1] : elim.Mat)) := by
    rw [← hBl]
    exact elim.rowsLen_transposeM _
  have hAr : elim.rowsLen 2 (adj2v 2 ([[a, b], [c, d]] : elim.Mat)) :=
    ⟨rfl, rfl, trivial⟩
  have hCwl : (elim.matMul (adj2v 2 [[a, b], [c, d]])
      ([b0, b1] : elim.Mat)).length = 2 := elim.length_matMul _ _
  have hCwr : elim.rowsLen m (elim.matMul (adj2v 2 [[a, b], [c, d]])
      ([b0, b1] : elim.Mat)) := by
    rw [← hBtl]
    exact elim.rowsLen_matMul _ _
  have hCw0 : 0 < (elim.matMul (adj2v 2 [[a, b], [c, d]])
      ([b0, b1] : elim.Mat)).length := by
    rw [hCwl]; exact Nat.succ_pos 1
  have hCtl : (elim.transposeM (elim.matMul (adj2v 2 [[a, b], [c, d]])
      ([b0, b1] : elim.Mat))).length = m :=
    elim.length_transposeM _ hCwr hCw0
  have hCtr : elim.rowsLen 2 (elim.transposeM
      (elim.matMul (adj2v 2 [[a, b], [c, d]]) ([b0, b1] : elim.Mat))) := by
    rw [← hCwl]
    exact elim.rowsLen_transposeM _
  have hSr : elim.rowsLen m
      (inertia.matScaleB (elim.minor ([[a, b], [c, d]] : elim.Mat))
        ([b0, b1] : elim.Mat)) := inertia.rowsLen_scaleB _ m _ hBr
  have hSl : (inertia.matScaleB (elim.minor ([[a, b], [c, d]] : elim.Mat))
      ([b0, b1] : elim.Mat)).length = 2 := inertia.length_scaleB _ _
  have hCwE : ∀ l : Nat, l < 2 → ∀ j : Nat, j < m →
      (ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (elim.matMul (adj2v 2 [[a, b], [c, d]])
          ([b0, b1] : elim.Mat)) l) j).oneValue
        (ground.getAt BPair.unit (ground.getAt ([] : List BPair)
            (adj2v 2 [[a, b], [c, d]]) l) 0 * ground.getAt BPair.unit b0 j
          + ground.getAt BPair.unit (ground.getAt ([] : List BPair)
            (adj2v 2 [[a, b], [c, d]]) l) 1
            * ground.getAt BPair.unit b1 j) := by
    intro l hl j hj
    have hjB : j < (elim.transposeM ([b0, b1] : elim.Mat)).length := by
      rw [hBtl]; exact hj
    have hlA : l < (adj2v 2 ([[a, b], [c, d]] : elim.Mat)).length := hl
    rw [entry_matMul (adj2v 2 ([[a, b], [c, d]] : elim.Mat))
      ([b0, b1] : elim.Mat) l j hlA hjB]
    refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
    refine BPair.oneValue_trans
      (dotP_two _ _
        (elim.rowsLen_getAt (adj2v 2 ([[a, b], [c, d]] : elim.Mat)) l hAr hlA)
        (elim.rowsLen_getAt _ j hBtr hjB)) ?_
    rw [elim.getAt_transposeM BPair.unit ([b0, b1] : elim.Mat) hBr j 0 hj
        (Nat.succ_pos 1),
      elim.getAt_transposeM BPair.unit ([b0, b1] : elim.Mat) hBr j 1 hj
        (Nat.succ_lt_succ (Nat.succ_pos 0))]
    exact BPair.oneValue_refl _
  refine elim.matOne_getAt _ _ ?_ ?_
  · rw [elim.length_matMul, hSl]
    rfl
  · intro i hi
    have hi2 : i < 2 := hi
    have hiB : i < ([b0, b1] : elim.Mat).length := hi2
    have hiP : i < ([[a, b], [c, d]] : elim.Mat).length := hi2
    have hrowL : (ground.getAt ([] : List BPair)
        (elim.matMul ([[a, b], [c, d]] : elim.Mat)
          (elim.matMul (adj2v 2 [[a, b], [c, d]])
            ([b0, b1] : elim.Mat))) i).length = m := by
      rw [rowLen_matMul ([[a, b], [c, d]] : elim.Mat) _ i hiP, hCtl]
    have hrowR : (ground.getAt ([] : List BPair)
        (inertia.matScaleB (elim.minor ([[a, b], [c, d]] : elim.Mat))
          ([b0, b1] : elim.Mat)) i).length = m :=
      elim.rowsLen_getAt _ i hSr (by rw [hSl]; exact hi2)
    refine poly.oneValue_of_entries _ _ (hrowL.trans hrowR.symm) ?_
    intro j hj
    rw [hrowL] at hj
    have hjT : j < (elim.transposeM (elim.matMul (adj2v 2 [[a, b], [c, d]])
        ([b0, b1] : elim.Mat))).length := by rw [hCtl]; exact hj
    rw [entry_matMul ([[a, b], [c, d]] : elim.Mat) _ i j hiP hjT,
      entry_scaleB (elim.minor ([[a, b], [c, d]] : elim.Mat))
        ([b0, b1] : elim.Mat) i j hiB
        (by rw [elim.rowsLen_getAt ([b0, b1] : elim.Mat) i hBr hiB]; exact hj)]
    refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
    refine BPair.oneValue_trans
      (dotP_two _ _
        (elim.rowsLen_getAt ([[a, b], [c, d]] : elim.Mat) i hPr hiP)
        (elim.rowsLen_getAt _ j hCtr hjT)) ?_
    have hCw1 : 1 < (elim.matMul (adj2v 2 [[a, b], [c, d]])
        ([b0, b1] : elim.Mat)).length := by
      rw [hCwl]; exact Nat.succ_lt_succ (Nat.succ_pos 0)
    rw [elim.getAt_transposeM BPair.unit _ hCwr j 0 hj hCw0,
      elim.getAt_transposeM BPair.unit _ hCwr j 1 hj hCw1]
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (hCwE 0 (Nat.succ_pos 1) j hj))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (hCwE 1 (Nat.succ_lt_succ (Nat.succ_pos 0)) j hj))) ?_
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.mul_congr_left (minor2_read a b c d))))
    match i, hi2 with
    | 0, _ => exact cross2 a b c d _ _
    | 1, _ => exact cross2' a b c d _ _
    | _ + 2, h =>
      exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))
        (Nat.not_lt_zero _)

/-- The adjugate's solve at the small orders: the pivot against its
adjugate's action reads the minor's rescaling, `P adj(P) = det P·1`
at every coupling slab. -/
theorem adj2v_solve {k m : Nat} (P B : elim.Mat) (hk : k = 1 ∨ k = 2)
    (hP : elim.sqAt P k) (hBl : B.length = k) (hBr : elim.rowsLen m B) :
    elim.matOneValue (elim.matMul P (elim.matMul (adj2v k P) B))
      (inertia.matScaleB (elim.minor P) B) := by
  match hk with
  | Or.inl h =>
    subst h
    exact solve_one P B hP hBl hBr
  | Or.inr h =>
    subst h
    exact solve_two P B hP hBl hBr

/-- The cleared deflation at polynomial entries: the trailing block
at the pivot minor's square against the pivot minor's multiple of
the coupling's solved correction, the selected blocks' read. -/
def pdefl (idx rest : List Nat) (S : split.PMat) : split.PMat :=
  split.pmatAdd
    (split.pscaleM (poly.mul (split.pminor (split.pselM idx idx S))
      (split.pminor (split.pselM idx idx S))) (split.pselM rest rest S))
    (split.pswapM (split.pscaleM (split.pminor (split.pselM idx idx S))
      (split.pmatMul (split.pselM rest idx S)
        (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
          (split.pselM idx rest S)))))

/-- The symmetry read at two occupied keys: the entry against its
exchanged entry. -/
private theorem sym_at {S : split.PMat} {o : Nat} (hsym : split.pSymAt S o)
    (i j : Nat) (hi : i < o) (hj : j < o) :
    poly.oneValue
      (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i) j)
      (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S j) i) := by
  have h1 := ground.all_getAt (0 : Nat) (List.range o)
    (show ((List.range o).all (fun i => (List.range o).all (fun j =>
      decide (poly.oneValue
        (ground.getAt ([] : Poly) (ground.getAt [] S i) j)
        (ground.getAt ([] : Poly) (ground.getAt [] S j) i))))) = true
      from hsym) i (by rw [ground.length_range]; exact hi)
  rw [ground.getAt_range o i hi] at h1
  have h2 := ground.all_getAt (0 : Nat) (List.range o) h1 j
    (by rw [ground.length_range]; exact hj)
  rw [ground.getAt_range o j hj] at h2
  exact of_decide_eq_true h2

/-- The exchanged coupling block's cleared evaluation is the evaluated
coupling's key-list exchange, the symmetry read entry by entry. -/
private theorem sym_transpose (S : split.PMat) (o K : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hsym : split.pSymAt S o)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true)
    (hk0 : 0 < idx.length) :
    elim.matOneValue (evalPC (split.pselM rest idx S) ln c K)
      (elim.transposeM (evalPC (split.pselM idx rest S) ln c K)) := by
  have hBvr : elim.rowsLen rest.length
      (evalPC (split.pselM idx rest S) ln c K) :=
    rowsLen_evalPC _ _ ln c K (split.rowsLen_pselM _ _ _)
  have hBvl : (evalPC (split.pselM idx rest S) ln c K).length = idx.length :=
    (length_evalPC _ ln c K).trans (split.length_pselM _ _ _)
  have hTl : (elim.transposeM
      (evalPC (split.pselM idx rest S) ln c K)).length = rest.length :=
    elim.length_transposeM _ hBvr (by rw [hBvl]; exact hk0)
  have hCl : (evalPC (split.pselM rest idx S) ln c K).length = rest.length :=
    (length_evalPC _ ln c K).trans (split.length_pselM _ _ _)
  have hTr : elim.rowsLen idx.length
      (elim.transposeM (evalPC (split.pselM idx rest S) ln c K)) := by
    rw [← hBvl]
    exact elim.rowsLen_transposeM _
  refine elim.matOne_getAt _ _ (hCl.trans hTl.symm) ?_
  intro r hr
  rw [hCl] at hr
  have hLrow : (ground.getAt ([] : List BPair)
      (evalPC (split.pselM rest idx S) ln c K) r).length = idx.length :=
    elim.rowsLen_getAt _ r (rowsLen_evalPC _ _ ln c K (split.rowsLen_pselM _ _ _))
      (by rw [hCl]; exact hr)
  have hRrow : (ground.getAt ([] : List BPair)
      (elim.transposeM (evalPC (split.pselM idx rest S) ln c K)) r).length
      = idx.length := elim.rowsLen_getAt _ r hTr (by rw [hTl]; exact hr)
  refine poly.oneValue_of_entries _ _ (hLrow.trans hRrow.symm) ?_
  intro l hl
  rw [hLrow] at hl
  rw [getAt_evalPC ln c K (split.pselM rest idx S) r l,
    split.getAt_pselM rest idx S r l hr hl,
    elim.getAt_transposeM BPair.unit (evalPC (split.pselM idx rest S) ln c K)
      hBvr r l hr (by rw [hBvl]; exact hl),
    getAt_evalPC ln c K (split.pselM idx rest S) l r,
    split.getAt_pselM idx rest S l r hl hr]
  exact poly.evalClear_congr (sym_at hsym _ _
    (ground.bltLt (ground.all_getAt 0 rest hrest r hr))
    (ground.bltLt (ground.all_getAt 0 idx hidx l hl))) ln c K

/-- The product's unit at the vacant clearing power reads the unit
member. -/
private theorem evalClear_one (ln : BPair) (c : Pos) :
    (poly.evalClear poly.one ln c 0).oneValue (BPair.ofPos Pos.one) := by
  refine BPair.oneValue_trans (poly.evalClear_read poly.one ln c 0) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  refine BPair.oneValue_trans (BPair.mul_one_read _) ?_
  exact BPair.mul_one_read _

/-- The cleared deflation's evaluation at the stated powers: the pivot
minor's evaluation the evaluated pivot's minor, the coupling block's
evaluation the transposed evaluated coupling, and the adjugate's
evaluation the evaluated adjugate — the two arms then the evaluated
blocks' own deflation. -/
private theorem pdefl_read (S : split.PMat) (K kk ka : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hk0 : 0 < idx.length)
    (hdeg : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) S i) j).length ≤ K + 1)
    (hka : ka + K = kk)
    (hsymT : elim.matOneValue (evalPC (split.pselM rest idx S) ln c K)
      (elim.transposeM (evalPC (split.pselM idx rest S) ln c K)))
    (hdmin : (split.pminor (split.pselM idx idx S)).length ≤ kk + 1)
    (hmin : (poly.evalClear (split.pminor (split.pselM idx idx S))
        ln c kk).oneValue
      (elim.minor (evalPC (split.pselM idx idx S) ln c K)))
    (hadjl : (padj2 idx.length (split.pselM idx idx S)).length = idx.length)
    (hadjr : elim.rowsLen idx.length
      (padj2 idx.length (split.pselM idx idx S)))
    (hadjd : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly)
        (padj2 idx.length (split.pselM idx idx S)) i) j).length ≤ ka + 1)
    (hadj : elim.matOneValue
      (evalPC (padj2 idx.length (split.pselM idx idx S)) ln c ka)
      (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))) :
    elim.matOneValue (evalPC (pdefl idx rest S) ln c (kk + kk + K))
      (inertia.deflMat (evalPC (split.pselM idx idx S) ln c K)
        (evalPC (split.pselM idx rest S) ln c K)
        (evalPC (split.pselM rest rest S) ln c K)
        (elim.matMul (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
          (evalPC (split.pselM idx rest S) ln c K))) := by
  have hBpl : (split.pselM idx rest S).length = idx.length :=
    split.length_pselM _ _ _
  have hBpr : elim.rowsLen rest.length (split.pselM idx rest S) :=
    split.rowsLen_pselM _ _ _
  have hCpr : elim.rowsLen idx.length (split.pselM rest idx S) :=
    split.rowsLen_pselM _ _ _
  have hCpl : (split.pselM rest idx S).length = rest.length :=
    split.length_pselM _ _ _
  have hQr : elim.rowsLen rest.length (split.pselM rest rest S) :=
    split.rowsLen_pselM _ _ _
  have hBvl : (evalPC (split.pselM idx rest S) ln c K).length = idx.length :=
    (length_evalPC _ ln c K).trans hBpl
  have hBvr : elim.rowsLen rest.length
      (evalPC (split.pselM idx rest S) ln c K) :=
    rowsLen_evalPC _ _ ln c K hBpr
  have hTBl : (elim.transposeM
      (evalPC (split.pselM idx rest S) ln c K)).length = rest.length :=
    elim.length_transposeM _ hBvr (by rw [hBvl]; exact hk0)
  have hCwr : elim.rowsLen rest.length
      (elim.matMul (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
        (evalPC (split.pselM idx rest S) ln c K)) := by
    rw [← hTBl]
    exact elim.rowsLen_matMul _ _
  have hAvl : (adj2v idx.length
      (evalPC (split.pselM idx idx S) ln c K)).length = idx.length := by
    rw [← elim.matOne_length hadj, length_evalPC, hadjl]
  have hCwl : (elim.matMul (adj2v idx.length
      (evalPC (split.pselM idx idx S) ln c K))
      (evalPC (split.pselM idx rest S) ln c K)).length = idx.length :=
    (elim.length_matMul _ _).trans hAvl
  have hhdBp : ((split.pselM idx rest S).headD ([] : List Poly)).length
      = rest.length :=
    headD_width _ idx.length rest.length hBpl hk0 hBpr
  have hWl : (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
      (split.pselM idx rest S)).length = idx.length :=
    (length_pmatMul _ _).trans hadjl
  have hWr : elim.rowsLen rest.length
      (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
        (split.pselM idx rest S)) := by
    rw [← hhdBp]
    exact rowsLen_pmatMul _ _
  have hWd : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly)
        (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
          (split.pselM idx rest S)) i) j).length ≤ ka + K + 1 :=
    deg_pmatMul _ _ ka K hadjd (deg_pselM hdeg idx rest)
  have hhdW : ((split.pmatMul (padj2 idx.length (split.pselM idx idx S))
      (split.pselM idx rest S)).headD ([] : List Poly)).length = rest.length :=
    headD_width _ idx.length rest.length hWl hk0 hWr
  have hZr : elim.rowsLen rest.length
      (split.pmatMul (split.pselM rest idx S)
        (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
          (split.pselM idx rest S))) := by
    rw [← hhdW]
    exact rowsLen_pmatMul _ _
  have hz : kk + K = K + (ka + K) := by
    rw [← hka]
    exact Nat.add_comm (ka + K) K
  have hZd : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly)
        (split.pmatMul (split.pselM rest idx S)
          (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
            (split.pselM idx rest S))) i) j).length ≤ kk + K + 1 := by
    rw [hz]
    exact deg_pmatMul _ _ K (ka + K) (deg_pselM hdeg rest idx) hWd
  have stepZ : elim.matOneValue
      (evalPC (split.pmatMul (split.pselM rest idx S)
        (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
          (split.pselM idx rest S))) ln c (kk + K))
      (elim.matMul (elim.transposeM (evalPC (split.pselM idx rest S) ln c K))
        (elim.matMul (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
          (evalPC (split.pselM idx rest S) ln c K))) := by
    rw [hz]
    refine elim.matOne_trans
      (evalPC_pmatMul (split.pselM rest idx S) _ ln c K (ka + K)
        idx.length rest.length hCpr hWl hk0 hWr
        (deg_pselM hdeg rest idx) hWd) ?_
    refine elim.matOne_trans (elim.matMul_congrL _ _ _ hsymT) ?_
    refine elim.matMul_congrR (n := idx.length) (k := rest.length)
      (elim.transposeM (evalPC (split.pselM idx rest S) ln c K)) _ _
      (rowsLen_evalPC _ _ ln c (ka + K) hWr) hCwr
      (by rw [length_evalPC, hWl]) hCwl hk0 ?_
    exact elim.matOne_trans
      (evalPC_pmatMul (padj2 idx.length (split.pselM idx idx S))
        (split.pselM idx rest S) ln c ka K idx.length rest.length
        hadjr hBpl hk0 hBpr hadjd (deg_pselM hdeg idx rest))
      (elim.matMul_congrL _ _ _ hadj)
  have stepU : elim.matOneValue
      (evalPC (split.pscaleM (poly.mul (split.pminor (split.pselM idx idx S))
        (split.pminor (split.pselM idx idx S))) (split.pselM rest rest S))
        ln c (kk + kk + K))
      (inertia.matScaleB (elim.minor (evalPC (split.pselM idx idx S) ln c K)
          * elim.minor (evalPC (split.pselM idx idx S) ln c K))
        (evalPC (split.pselM rest rest S) ln c K)) :=
    elim.matOne_trans
      (evalPC_pscaleM _ ln c (kk + kk) K
        (poly.mul_len_le _ _ kk kk hdmin hdmin)
        (split.pselM rest rest S) (deg_pselM hdeg rest rest))
      (inertia.matScaleB_congr
        (BPair.oneValue_trans (evalClear_mul _ _ ln c kk kk hdmin hdmin)
          (BPair.mul_congr hmin hmin)) _)
  have stepV : elim.matOneValue
      (evalPC (split.pswapM (split.pscaleM
        (split.pminor (split.pselM idx idx S))
        (split.pmatMul (split.pselM rest idx S)
          (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
            (split.pselM idx rest S))))) ln c (kk + kk + K))
      (elim.matSwap (inertia.matScaleB
        (elim.minor (evalPC (split.pselM idx idx S) ln c K))
        (elim.matMul
          (elim.transposeM (evalPC (split.pselM idx rest S) ln c K))
          (elim.matMul
            (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
            (evalPC (split.pselM idx rest S) ln c K))))) := by
    refine elim.matOne_trans (evalPC_pswapM ln c (kk + kk + K) _) ?_
    refine elim.matSwap_congr ?_
    rw [Nat.add_assoc kk kk K]
    exact elim.matOne_trans
      (evalPC_pscaleM _ ln c kk (kk + K) hdmin _ hZd)
      (elim.matOne_trans (inertia.matScaleB_congr hmin _)
        (inertia.matOne_scaleB _ stepZ))
  have hCwT : (elim.transposeM (elim.matMul
      (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
      (evalPC (split.pselM idx rest S) ln c K))).length = rest.length :=
    elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0)
  have hMr : elim.rowsLen rest.length (elim.matMul
      (elim.transposeM (evalPC (split.pselM idx rest S) ln c K))
      (elim.matMul (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
        (evalPC (split.pselM idx rest S) ln c K))) := by
    rw [← hCwT]
    exact elim.rowsLen_matMul _ _
  show elim.matOneValue (evalPC (pdefl idx rest S) ln c (kk + kk + K))
    (elim.matAdd
      (inertia.matScaleB (elim.minor (evalPC (split.pselM idx idx S) ln c K)
          * elim.minor (evalPC (split.pselM idx idx S) ln c K))
        (evalPC (split.pselM rest rest S) ln c K))
      (elim.matSwap (inertia.matScaleB
        (elim.minor (evalPC (split.pselM idx idx S) ln c K))
        (elim.matMul
          (elim.transposeM (evalPC (split.pselM idx rest S) ln c K))
          (elim.matMul
            (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
            (evalPC (split.pselM idx rest S) ln c K))))))
  exact elim.matOne_trans (evalPC_pmatAdd ln c (kk + kk + K) _ _)
    (elim.matAdd_cong2 rest.length _ _ _ _
      (rowsLen_evalPC _ _ ln c (kk + kk + K)
        (rowsLen_pscaleM _ _ _ hQr))
      (rowsLen_evalPC _ _ ln c (kk + kk + K)
        (rowsLen_pswapM _ _ (rowsLen_pscaleM _ _ _ hZr)))
      (inertia.rowsLen_scaleB _ _ _ (rowsLen_evalPC _ _ ln c K hQr))
      (elim.rowsLen_mapRows BPair.swap _ _
        (inertia.rowsLen_scaleB _ _ _ hMr))
      stepU stepV)

/-- The deflation's cleared evaluation at a pivot of order one. -/
private theorem pdefl_one (S : split.PMat) (o K i0 : Nat) (rest : List Nat)
    (ln : BPair) (c : Pos)
    (hsh : pShapeAt S o K) (hsym : split.pSymAt S o)
    (hidx : (([i0] : List Nat).all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true) :
    elim.matOneValue
      (evalPC (pdefl [i0] rest S) ln c
        ((2 * ([i0] : List Nat).length + 1) * K))
      (inertia.deflMat (evalPC (split.pselM [i0] [i0] S) ln c K)
        (evalPC (split.pselM [i0] rest S) ln c K)
        (evalPC (split.pselM rest rest S) ln c K)
        (elim.matMul (adj2v ([i0] : List Nat).length
            (evalPC (split.pselM [i0] [i0] S) ln c K))
          (evalPC (split.pselM [i0] rest S) ln c K))) := by
  have hk0 : 0 < ([i0] : List Nat).length := Nat.succ_pos 0
  have h3 : (2 * ([i0] : List Nat).length + 1) * K = K + K + K := by
    show 3 * K = K + K + K
    rw [Nat.mul_comm 3 K]
    show 0 + K + K + K = K + K + K
    rw [Nat.zero_add]
  rw [h3]
  exact pdefl_read S K K 0 [i0] rest ln c hk0 (ent_ble hsh) (Nat.zero_add K)
    (sym_transpose S o K [i0] rest ln c hsym hidx hrest hk0)
    (ent_ble hsh i0 i0) (BPair.oneValue_refl _) rfl ⟨rfl, trivial⟩
    (by
      intro i j
      match i, j with
      | 0, 0 => exact Nat.le_refl 1
      | 0, _ + 1 => exact Nat.zero_le _
      | _ + 1, _ => exact Nat.zero_le _)
    ⟨⟨evalClear_one ln c, trivial⟩, trivial⟩

/-- The deflation's cleared evaluation at a pivot of order two. -/
private theorem pdefl_two (S : split.PMat) (o K i0 i1 : Nat)
    (rest : List Nat) (ln : BPair) (c : Pos)
    (hsh : pShapeAt S o K) (hsym : split.pSymAt S o)
    (hidx : (([i0, i1] : List Nat).all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true) :
    elim.matOneValue
      (evalPC (pdefl [i0, i1] rest S) ln c
        ((2 * ([i0, i1] : List Nat).length + 1) * K))
      (inertia.deflMat (evalPC (split.pselM [i0, i1] [i0, i1] S) ln c K)
        (evalPC (split.pselM [i0, i1] rest S) ln c K)
        (evalPC (split.pselM rest rest S) ln c K)
        (elim.matMul (adj2v ([i0, i1] : List Nat).length
            (evalPC (split.pselM [i0, i1] [i0, i1] S) ln c K))
          (evalPC (split.pselM [i0, i1] rest S) ln c K))) := by
  have hk0 : 0 < ([i0, i1] : List Nat).length := Nat.succ_pos 1
  have h5 : (2 * ([i0, i1] : List Nat).length + 1) * K
      = K + K + (K + K) + K := by
    show 5 * K = K + K + (K + K) + K
    rw [Nat.mul_comm 5 K]
    show 0 + K + K + K + K + K = K + K + (K + K) + K
    rw [Nat.zero_add, Nat.add_assoc (K + K) K K]
  have hdmin : (split.pminor (split.pselM [i0, i1] [i0, i1] S)).length
      ≤ K + K + 1 := by
    show (poly.add (poly.pnorm (poly.mul
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i0)
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i1)))
      (poly.add (poly.neg (poly.pnorm (poly.mul
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i1)
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i0))))
        [])).length ≤ K + K + 1
    rw [poly.add_nil]
    refine poly.add_len_le _ _ (K + K + 1) ?_ ?_
    · rw [poly.pnorm_length]
      exact poly.mul_len_le _ _ K K (ent_ble hsh i0 i0) (ent_ble hsh i1 i1)
    · rw [poly.length_neg, poly.pnorm_length]
      exact poly.mul_len_le _ _ K K (ent_ble hsh i0 i1) (ent_ble hsh i1 i0)
  have hL : (poly.evalClear (split.pminor (split.pselM [i0, i1] [i0, i1] S))
      ln c (K + K)).oneValue
      (poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i0)
          ln c K
        * poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i1)
          ln c K
      + (poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i1)
          ln c K
        * poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i0)
          ln c K).swap) := by
    show (poly.evalClear (poly.add (poly.pnorm (poly.mul
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i0)
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i1)))
      (poly.add (poly.neg (poly.pnorm (poly.mul
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i1)
        (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i0))))
        [])) ln c (K + K)).oneValue _
    rw [poly.add_nil]
    exact BPair.oneValue_trans (evalClear_add _ _ ln c (K + K))
      (BPair.add_congr
        (BPair.oneValue_trans
          (poly.evalClear_congr (poly.pnorm_oneValue _) ln c (K + K))
          (evalClear_mul _ _ ln c K K (ent_ble hsh i0 i0) (ent_ble hsh i1 i1)))
        (BPair.oneValue_trans (evalClear_neg _ ln c (K + K))
          (ground.swap_congr
            (BPair.oneValue_trans
              (poly.evalClear_congr (poly.pnorm_oneValue _) ln c (K + K))
              (evalClear_mul _ _ ln c K K (ent_ble hsh i0 i1)
                (ent_ble hsh i1 i0))))))
  have hR : (elim.minor
      (evalPC (split.pselM [i0, i1] [i0, i1] S) ln c K)).oneValue
      (poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i0)
          ln c K
        * poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i1)
          ln c K
      + (poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i1)
          ln c K
        * poly.evalClear
          (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i0)
          ln c K).swap) := minor2_read _ _ _ _
  rw [h5]
  exact pdefl_read S K (K + K) K [i0, i1] rest ln c hk0 (ent_ble hsh) rfl
    (sym_transpose S o K [i0, i1] rest ln c hsym hidx hrest hk0)
    hdmin (BPair.oneValue_trans hL (BPair.oneValue_symm hR))
    rfl ⟨rfl, rfl, trivial⟩
    (by
      intro i j
      match i, j with
      | 0, 0 => exact ent_ble hsh i1 i1
      | 0, 1 =>
        show (poly.neg (ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly) S i0) i1)).length ≤ K + 1
        rw [poly.length_neg]
        exact ent_ble hsh i0 i1
      | 0, _ + 2 => exact Nat.zero_le _
      | 1, 0 =>
        show (poly.neg (ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly) S i1) i0)).length ≤ K + 1
        rw [poly.length_neg]
        exact ent_ble hsh i1 i0
      | 1, 1 => exact ent_ble hsh i0 i0
      | 1, _ + 2 => exact Nat.zero_le _
      | _ + 2, _ => exact Nat.zero_le _)
    ⟨⟨BPair.oneValue_refl _, evalClear_neg _ ln c K, trivial⟩,
     ⟨evalClear_neg _ ln c K, BPair.oneValue_refl _, trivial⟩, trivial⟩

/-- The deflation's cleared evaluation is the evaluated blocks' own
deflation at the adjugate-solved witness: the clearing power
`(2k+1) K` at the pivot order `k`, the two arms exact. -/
theorem evalPC_pdefl {o : Nat} (S : split.PMat) (K : Nat)
    (idx rest : List Nat) (ln : BPair) (c : Pos)
    (hsh : pShapeAt S o K) (hsym : split.pSymAt S o)
    (hk : idx.length = 1 ∨ idx.length = 2)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hrest : (rest.all (fun j => Nat.blt j o)) = true) :
    elim.matOneValue
      (evalPC (pdefl idx rest S) ln c ((2 * idx.length + 1) * K))
      (inertia.deflMat (evalPC (split.pselM idx idx S) ln c K)
        (evalPC (split.pselM idx rest S) ln c K)
        (evalPC (split.pselM rest rest S) ln c K)
        (elim.matMul (adj2v idx.length (evalPC (split.pselM idx idx S) ln c K))
          (evalPC (split.pselM idx rest S) ln c K))) := by
  match idx, hk, hidx with
  | [], Or.inl h, _ => exact Nat.noConfusion h
  | [], Or.inr h, _ => exact Nat.noConfusion h
  | [i0], _, hi => exact pdefl_one S o K i0 rest ln c hsh hsym hi hrest
  | [i0, i1], _, hi => exact pdefl_two S o K i0 i1 rest ln c hsh hsym hi hrest
  | _ :: _ :: _ :: _, Or.inl h, _ =>
    exact Nat.noConfusion (Nat.succ.inj h)
  | _ :: _ :: _ :: _, Or.inr h, _ =>
    exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h))

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

/-- The predicate count at pointwise-equal reads over the members. -/
private theorem countBy_congr {p q : Nat → Bool} : ∀ l : List Nat,
    (∀ x, 0 < ground.countOf x l → p x = q x) →
    ground.countBy p l = ground.countBy q l
  | [], _ => rfl
  | a :: t, h => by
    have ha := h a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    have ht := countBy_congr t
      (fun x hx => h x (ground.countOf_cons_pos hx))
    cases hqa : q a with
    | true =>
      rw [ground.countBy_cons_true p t (ha.trans hqa),
        ground.countBy_cons_true q t hqa, ht]
    | false =>
      rw [ground.countBy_cons_false p t (ha.trans hqa),
        ground.countBy_cons_false q t hqa, ht]

/-- Two predicates refusing together count at the join. -/
private theorem countBy_or {p q : Nat → Bool} : ∀ l : List Nat,
    (∀ x, 0 < ground.countOf x l → p x = true → q x = false) →
    ground.countBy (fun x => p x || q x) l
      = ground.countBy p l + ground.countBy q l
  | [], _ => rfl
  | a :: t, h => by
    have ht := countBy_or t
      (fun x hx => h x (ground.countOf_cons_pos hx))
    have hmem := h a (by rw [ground.countOf_head]; exact Nat.succ_pos _)
    cases hpa : p a with
    | true =>
      rw [ground.countBy_cons_true (fun x => p x || q x) t
          (by rw [hpa]; rfl),
        ground.countBy_cons_true p t hpa,
        ground.countBy_cons_false q t (hmem hpa), ht,
        Nat.add_assoc]
    | false =>
      cases hqa : q a with
      | true =>
        rw [ground.countBy_cons_true (fun x => p x || q x) t
            (by rw [hpa, hqa]; rfl),
          ground.countBy_cons_false p t hpa,
          ground.countBy_cons_true q t hqa, ht,
          Nat.add_left_comm]
      | false =>
        rw [ground.countBy_cons_false (fun x => p x || q x) t
            (by rw [hpa, hqa]; rfl),
          ground.countBy_cons_false p t hpa,
          ground.countBy_cons_false q t hqa, ht]

/-- The predicate and its refusal split the length. -/
private theorem countBy_split (p : Nat → Bool) : ∀ l : List Nat,
    ground.countBy p l + ground.countBy (fun x => !(p x)) l
      = l.length
  | [] => rfl
  | a :: t => by
    cases hpa : p a with
    | true =>
      rw [ground.countBy_cons_true p t hpa,
        ground.countBy_cons_false (fun x => !(p x)) t
          (by rw [hpa]; rfl),
        Nat.add_assoc, countBy_split p t,
        show (a :: t).length = t.length + 1 from rfl,
        Nat.add_comm]
    | false =>
      rw [ground.countBy_cons_false p t hpa,
        ground.countBy_cons_true (fun x => !(p x)) t
          (by rw [hpa]; rfl),
        Nat.add_left_comm, countBy_split p t,
        show (a :: t).length = t.length + 1 from rfl,
        Nat.add_comm]

/-- The filter's length is the predicate's count. -/
private theorem length_filterBy (p : Nat → Bool) : ∀ l : List Nat,
    (l.filter p).length = ground.countBy p l
  | [] => rfl
  | a :: t => by
    cases hpa : p a with
    | true =>
      rw [ground.filter_cons_true hpa,
        ground.countBy_cons_true p t hpa,
        show (a :: t.filter p).length = (t.filter p).length + 1
          from rfl,
        length_filterBy p t, Nat.add_comm]
    | false =>
      rw [ground.filter_cons_false hpa,
        ground.countBy_cons_false p t hpa, length_filterBy p t]

/-- The vacant predicate counts at the sum's unit. -/
private theorem countBy_false : ∀ l : List Nat,
    ground.countBy (fun _ => false) l = 0
  | [] => rfl
  | a :: t => by
    rw [ground.countBy_cons_false (fun _ => false) t rfl,
      countBy_false t]

/-- The key comparison's count is the key's own. -/
private theorem countBy_beq (a : Nat) (l : List Nat) :
    ground.countBy (fun j => j == a) l = ground.countOf a l :=
  countBy_congr l (fun x _ => ground.beqSymm x a)

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
private theorem compl_length {o : Nat} {idx : List Nat}
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
private theorem distinct_append_compl {o : Nat} {idx : List Nat}
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

/-- The join with the complement covers the order. -/
private theorem cover_append_compl {o : Nat} {idx : List Nat} :
    ∀ j, j < o → 0 < ground.countOf j (idx ++ compl idx o) := by
  intro j hj
  rw [ground.countOf_append j idx (compl idx o)]
  match Nat.eq_zero_or_pos (ground.countOf j idx) with
  | Or.inr hp => exact Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _)
  | Or.inl hz =>
    have hcc : ground.countOf j (compl idx o) = 1 := by
      rw [show compl idx o = (List.range o).filter
          (fun j => !(idx.contains j)) from rfl,
        ground.countOf_filter (fun x => !(idx.contains x)) j
          (List.range o),
        contains_none idx hz]
      rw [if_pos (show (!false) = true from rfl),
        ground.countOf_range j o, if_pos hj]
    rw [hcc]
    exact Nat.lt_of_lt_of_le (Nat.zero_lt_one)
      (Nat.le_add_left 1 _)

/-- One subinterval's frame: the chained endpoints, the designated
places inside the order and pairwise distinct, and the pencil's
shape and symmetry reads; the places' permutation enters the
leading position at `elim.permM_orthL`'s identity reads, the
transpose the witness. -/
def pieceRead (S : split.PMat) (o K : Nat) (lo b : CPair)
    (idx : List Nat) : Prop :=
  lo ≤ b
  ∧ (idx.all (fun i => Nat.blt i o)) = true
  ∧ ground.distinctList idx
  ∧ pShapeAt S o K ∧ split.pSymAt S o

instance (S : split.PMat) (o K : Nat) (lo b : CPair) (idx : List Nat) :
    Decidable (pieceRead S o K lo b idx) :=
  inferInstanceAs (Decidable (_ ∧ _ = _ ∧ _ ∧ _ ∧ _))

set_option genInjectivity false in
/-- The pivot cover: the chain's end, the order-nought deflation, and
one subinterval per designation — the piece's upper endpoint, the
designated places, the determinant's priced side certificate at a
stated bound (the lower side the mixed order-two row), at order two
with the determinant upper the leading entry's own, and beneath it
the cleared deflation's cover with the chain's remainder beside it. -/
inductive Cover where
  | done : Cover
  | nought : Cover
  | one (b : CPair) (i : Nat) (up : Bool) (N D : BPair)
      (sub rest : Cover) : Cover
  | mixed (b : CPair) (i j : Nat) (N D : BPair)
      (sub rest : Cover) : Cover
  | twoUp (b : CPair) (i j : Nat) (N D : BPair)
      (eUp : Bool) (eN eD : BPair) (sub rest : Cover) : Cover

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

/-- The cover's read at a pencil, an order, a clearing and a
segment: the chain's end reads the pencil's shape and ties the
endpoints, the order-nought
deflation reads its order, and a piece reads its chained endpoints,
its places' bounds with the permutation products, the pencil's
shape and symmetry, the designated minor's priced side reads, and
the two covers beneath and beside it. -/
def coverRead (S : split.PMat) (o K : Nat) (lo hi : CPair) :
    Cover → Prop
  | .done => pShapeAt S o K ∧ lo.oneValue hi
  | .nought => Nat.beq o 0 = true
  | .one b i up N D sub rest =>
      pieceRead S o K lo b [i]
      ∧ (if up then
          stage.keepUpper (ground.getAt [] (ground.getAt [] S i) i)
            lo b N D
        else
          stage.keepLower (ground.getAt [] (ground.getAt [] S i) i)
            lo b N D)
      ∧ coverRead (pdefl [i] (compl [i] o) S) (o - 1) (3 * K) lo b sub
      ∧ coverRead S o K b hi rest
  | .mixed b i j N D sub rest =>
      pieceRead S o K lo b [i, j]
      ∧ stage.keepLower (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D
      ∧ coverRead (pdefl [i, j] (compl [i, j] o) S) (o - 2) (5 * K) lo b sub
      ∧ coverRead S o K b hi rest
  | .twoUp b i j N D eUp eN eD sub rest =>
      pieceRead S o K lo b [i, j]
      ∧ stage.keepUpper (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D
      ∧ (if eUp then
          stage.keepUpper (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD
        else
          stage.keepLower (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD)
      ∧ coverRead (pdefl [i, j] (compl [i, j] o) S) (o - 2) (5 * K) lo b sub
      ∧ coverRead S o K b hi rest

/-- The cover read's decision, one arm per constructor with the
chain's two covers decided beneath. -/
instance decCoverRead (S : split.PMat) (o K : Nat) (lo hi : CPair) :
    ∀ cov : Cover, Decidable (coverRead S o K lo hi cov)
  | .done =>
    @instDecidableAnd _ _ (inferInstanceAs (Decidable (pShapeAt S o K)))
      (inferInstanceAs (Decidable (lo.oneValue hi)))
  | .nought => inferInstanceAs (Decidable (Nat.beq o 0 = true))
  | .one b i up N D sub rest =>
    match up with
    | true =>
      @instDecidableAnd _ _
        (inferInstanceAs (Decidable (pieceRead S o K lo b [i])))
        (@instDecidableAnd _ _
          (inferInstanceAs (Decidable (stage.keepUpper
            (split.pminor (split.pselM [i] [i] S)) lo b N D)))
          (@instDecidableAnd _ _
            (decCoverRead (pdefl [i] (compl [i] o) S) (o - 1) (3 * K) lo b sub)
            (decCoverRead S o K b hi rest)))
    | false =>
      @instDecidableAnd _ _
        (inferInstanceAs (Decidable (pieceRead S o K lo b [i])))
        (@instDecidableAnd _ _
          (inferInstanceAs (Decidable (stage.keepLower
            (split.pminor (split.pselM [i] [i] S)) lo b N D)))
          (@instDecidableAnd _ _
            (decCoverRead (pdefl [i] (compl [i] o) S) (o - 1) (3 * K) lo b sub)
            (decCoverRead S o K b hi rest)))
  | .mixed b i j N D sub rest =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead S o K lo b [i, j])))
      (@instDecidableAnd _ _
        (inferInstanceAs (Decidable (stage.keepLower
          (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)))
        (@instDecidableAnd _ _
          (decCoverRead (pdefl [i, j] (compl [i, j] o) S) (o - 2) (5 * K)
            lo b sub)
          (decCoverRead S o K b hi rest)))
  | .twoUp b i j N D eUp eN eD sub rest =>
    match eUp with
    | true =>
      @instDecidableAnd _ _
        (inferInstanceAs (Decidable (pieceRead S o K lo b [i, j])))
        (@instDecidableAnd _ _
          (inferInstanceAs (Decidable (stage.keepUpper
            (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)))
          (@instDecidableAnd _ _
            (inferInstanceAs (Decidable (stage.keepUpper
              (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD)))
            (@instDecidableAnd _ _
              (decCoverRead (pdefl [i, j] (compl [i, j] o) S) (o - 2) (5 * K)
                lo b sub)
              (decCoverRead S o K b hi rest))))
    | false =>
      @instDecidableAnd _ _
        (inferInstanceAs (Decidable (pieceRead S o K lo b [i, j])))
        (@instDecidableAnd _ _
          (inferInstanceAs (Decidable (stage.keepUpper
            (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)))
          (@instDecidableAnd _ _
            (inferInstanceAs (Decidable (stage.keepLower
              (ground.getAt [] (ground.getAt [] S i) i) lo b eN eD)))
            (@instDecidableAnd _ _
              (decCoverRead (pdefl [i, j] (compl [i, j] o) S) (o - 2) (5 * K)
                lo b sub)
              (decCoverRead S o K b hi rest))))

/-! The cover's proof tier: the list and matrix joins' class reads,
the selection's passage through the cleared evaluation, the
clearing power's shift, the composite order's totality and
transitivity, and the block table's side reads. -/

/-- A row's selection passes the cleared evaluation. -/
private theorem selRow_evalPC (ln : BPair) (c : Pos) (K : Nat)
    (r : List Poly) : ∀ J : List Nat,
    J.map (fun j => ground.getAt BPair.unit
        (r.map (fun p => poly.evalClear p ln c K)) j)
      = (J.map (fun j => ground.getAt ([] : Poly) r j)).map
          (fun p => poly.evalClear p ln c K)
  | [] => rfl
  | j :: t => by
    show ground.getAt BPair.unit
        (r.map (fun p => poly.evalClear p ln c K)) j
        :: t.map (fun j => ground.getAt BPair.unit
          (r.map (fun p => poly.evalClear p ln c K)) j)
      = poly.evalClear (ground.getAt ([] : Poly) r j) ln c K
        :: (t.map (fun j => ground.getAt ([] : Poly) r j)).map
          (fun p => poly.evalClear p ln c K)
    rw [selRow_evalPC ln c K r t, getAt_rowEC ln c K r j]

/-- The selection passes the cleared evaluation: the evaluated
matrix's selected block is the selected pencil's own evaluation. -/
private theorem selM_evalPC (ln : BPair) (c : Pos) (K : Nat)
    (S : split.PMat) (J : List Nat) : ∀ I : List Nat,
    elim.selM I J (evalPC S ln c K) = evalPC (split.pselM I J S) ln c K
  | [] => rfl
  | i :: t => by
    show J.map (fun j => ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (evalPC S ln c K) i) j)
        :: elim.selM t J (evalPC S ln c K)
      = (J.map (fun j => ground.getAt ([] : Poly)
            (ground.getAt ([] : List Poly) S i) j)).map
          (fun p => poly.evalClear p ln c K)
        :: evalPC (split.pselM t J S) ln c K
    rw [selM_evalPC ln c K S J t, getAt_evalPCrow ln c K S i,
      selRow_evalPC ln c K (ground.getAt ([] : List Poly) S i) J]

/-- The cleared evaluation of a symmetric pencil is symmetric. -/
private theorem evalPC_sym {S : split.PMat} {o : Nat} (ln : BPair)
    (c : Pos) (K : Nat) (hlen : S.length = o) (hrows : elim.rowsLen o S)
    (hsym : split.pSymAt S o) :
    elim.matOneValue (elim.transposeM (evalPC S ln c K))
      (evalPC S ln c K) := by
  have hEl : (evalPC S ln c K).length = o :=
    (length_evalPC S ln c K).trans hlen
  have hEr : elim.rowsLen o (evalPC S ln c K) :=
    rowsLen_evalPC o S ln c K hrows
  cases Nat.eq_zero_or_pos o with
  | inl h0 =>
    have hnil : evalPC S ln c K = [] := by
      match hE : evalPC S ln c K with
      | [] => rfl
      | _ :: _ => exact Nat.noConfusion ((hE ▸ hEl).trans h0)
    rw [hnil]
    exact trivial
  | inr hpos =>
    have hTl : (elim.transposeM (evalPC S ln c K)).length = o :=
      elim.length_transposeM _ hEr (by rw [hEl]; exact hpos)
    refine elim.matOne_getAt _ _ (by rw [hTl, hEl]) ?_
    intro p hp
    rw [hTl] at hp
    have hL : (ground.getAt ([] : List BPair)
        (elim.transposeM (evalPC S ln c K)) p).length = o :=
      elim.rowsLen_getAt _ p
        (elim.rowsLen_cast hEl (elim.rowsLen_transposeM _))
        (by rw [hTl]; exact hp)
    have hR : (ground.getAt ([] : List BPair) (evalPC S ln c K) p).length
        = o := elim.rowsLen_getAt _ p hEr (by rw [hEl]; exact hp)
    refine poly.oneValue_of_entries _ _ (hL.trans hR.symm) ?_
    intro q hq
    rw [hL] at hq
    rw [elim.getAt_transposeM BPair.unit (evalPC S ln c K) hEr p q hp
        (by rw [hEl]; exact hq),
      getAt_evalPC ln c K S q p, getAt_evalPC ln c K S p q]
    exact poly.evalClear_congr (sym_at hsym q p hq hp) ln c K

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
private theorem all_compl (idx : List Nat) (o : Nat) :
    ((compl idx o).all (fun j => Nat.blt j o)) = true :=
  all_filter _ _ (List.range o) (all_range o)

/-- The lower side at the polynomial's own clearing carries to
every higher clearing power. -/
private theorem sideDown_shift (p : Poly) (l : BPair) (c : Pos) (K : Nat)
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
private theorem sideDown_rep (p : Poly) (l : BPair) (c : Pos)
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

/-- The pivot's addition at a stated whole order, the block orders'
total the order's own. -/
private theorem rev_addN {k m n : Nat} (hn : k + m = n)
    (P B Q Cw : elim.Mat)
    (hP : elim.sqAt P k) (hBl : B.length = k) (hBr : elim.rowsLen m B)
    (hQ : elim.sqAt Q m) (hCl : Cw.length = k) (hCr : elim.rowsLen m Cw)
    (hPs : elim.matOneValue (elim.transposeM P) P)
    (hPw : elim.matOneValue (elim.matMul P Cw)
      (inertia.matScaleB (elim.minor P) B))
    (hPnz : ¬ (elim.minor P).oneValue BPair.unit)
    (spS : inertia.Split n)
    (hS : inertia.splitRead (inertia.blockJoin P B Q) spS)
    (spP : inertia.Split k) (hp : inertia.splitRead P spP)
    (spD : inertia.Split m)
    (hd : inertia.splitRead (inertia.deflMat P B Q Cw) spD) :
    inertia.revAt spS = inertia.revAt spP + inertia.revAt spD := by
  subst hn
  exact inertia.rev_add P B Q Cw hP hBl hBr hQ hCl hCr hPs hPw hPnz
    spS hS spP hp spD hd

/-- The shape read's row count. -/
theorem pShape_len {S : split.PMat} {o K : Nat}
    (h : pShapeAt S o K) : S.length = o :=
  ground.beqEq _ _ (ground.andSplitB
    (show (Nat.beq S.length o
      && S.all (fun r => Nat.beq r.length o
        && r.all (fun p => Nat.ble p.length (K + 1)))) = true from h)).1

/-- A width fold at a leading conjunct reads the rows' shape. -/
private theorem rowsLen_of_all (o : Nat) (f : List Poly → Bool) :
    ∀ S : split.PMat,
      (S.all (fun r => Nat.beq r.length o && f r)) = true →
      elim.rowsLen o S
  | [], _ => trivial
  | r :: t, hh => by
    have hs := ground.andSplitB hh
    have hs2 := ground.andSplitB hs.1
    exact ⟨ground.beqEq _ _ hs2.1, rowsLen_of_all o f t hs.2⟩

/-- The shape read's row widths. -/
theorem pShape_rows {S : split.PMat} {o K : Nat}
    (h : pShapeAt S o K) : elim.rowsLen o S :=
  rowsLen_of_all o (fun r => r.all (fun p => Nat.ble p.length (K + 1))) S
    (ground.andSplitB
      (show (Nat.beq S.length o
        && S.all (fun r => Nat.beq r.length o
          && r.all (fun p => Nat.ble p.length (K + 1)))) = true from h)).2

/-- The evaluation of a shaped pencil is square at the stated
order. -/
theorem evalPC_sqAt {S : split.PMat} {o K : Nat}
    (hsh : pShapeAt S o K) (x : BPair) (c : Pos) :
    elim.sqAt (evalPC S x c K) o :=
  elim.sqAt_of ((length_evalPC S x c K).trans (pShape_len hsh))
    (rowsLen_evalPC o S x c K (pShape_rows hsh))

/-- The symmetric pencil's cleared evaluation keeps the entrywise
symmetry at every point (`split.pSymAt` read through the
evaluation). -/
theorem evalPC_symAt (S : split.PMat) (o K : Nat) (x : BPair)
    (c : Pos) (hsh : pShapeAt S o K) (hsym : split.pSymAt S o) :
    elim.matOneValue (evalPC S x c K)
      (elim.transposeM (evalPC S x c K)) := by
  have hSl := pShape_len hsh
  have hSr := pShape_rows hsh
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
  exact poly.evalClear_congr (sym_at hsym i j hi hj) x c K

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
  rw [entry_scaleB _ (evalPC S xn xc K) i j (by rw [hXl]; exact hi)
      (by rw [elim.rowsLen_getAt _ i hXr (by rw [hXl]; exact hi)]; exact hj),
    entry_scaleB _ (evalPC S yn yc K) i j (by rw [hYl]; exact hi)
      (by rw [elim.rowsLen_getAt _ i hYr (by rw [hYl]; exact hi)]; exact hj),
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

/-- The adjugate's row count at the small orders. -/
private theorem length_adj2v {k : Nat} (P : elim.Mat)
    (hk : k = 1 ∨ k = 2) : (adj2v k P).length = k := by
  match hk with
  | Or.inl h => rw [h]; rfl
  | Or.inr h => rw [h]; rfl

/-- `lem:inertia`'s addition at the designated places: the count at
the permuted datum splits at the pivot and the cleared deflation,
the places' permutation entering the leading position. -/
private theorem rev_perm_add {o k m : Nat} (M : elim.Mat)
    (idx cpl : List Nat)
    (hk : idx.length = k) (hcl : cpl.length = m) (hkm : k + m = o)
    (hk12 : k = 1 ∨ k = 2)
    (hMsq : elim.sqAt M o)
    (hMsym : elim.matOneValue (elim.transposeM M) M)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hcpl : (cpl.all (fun j => Nat.blt j o)) = true)
    (hjd : ground.distinctList (idx ++ cpl))
    (hjc : ∀ j, j < o → 0 < ground.countOf j (idx ++ cpl))
    (hPnz : ¬ (elim.minor (elim.selM idx idx M)).oneValue BPair.unit)
    (spx : inertia.Split o) (hx : inertia.splitRead M spx)
    (spP : inertia.Split k)
    (hP : inertia.splitRead (elim.selM idx idx M) spP)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (inertia.deflMat (elim.selM idx idx M) (elim.selM idx cpl M)
        (elim.selM cpl cpl M)
        (elim.matMul (adj2v k (elim.selM idx idx M))
          (elim.selM idx cpl M))) spD) :
    inertia.revAt spx = inertia.revAt spP + inertia.revAt spD := by
  have hMl : M.length = o := elim.sqAt_len hMsq
  have hMr : elim.rowsLen o M := elim.rowsLen_of_sqAt hMsq
  have hk0 : 0 < k := by
    match hk12 with
    | Or.inl h => rw [h]; exact Nat.succ_pos 0
    | Or.inr h => rw [h]; exact Nat.succ_pos 1
  have hidxl : 0 < idx.length := by rw [hk]; exact hk0
  have hopos : 0 < o := by
    rw [← hkm]
    exact Nat.lt_of_lt_of_le hk0 (Nat.le_add_right k m)
  have hsg : ((idx ++ cpl).all (fun j => Nat.blt j o)) = true :=
    (by rw [ground.all_append _ idx cpl, hidx, hcpl]; rfl)
  have hsgl : (idx ++ cpl).length = o := by
    rw [ground.length_append, hk, hcl]; exact hkm
  have hp1 : elim.matOneValue
      (elim.matMul (elim.permM o (idx ++ cpl))
        (elim.transposeM (elim.permM o (idx ++ cpl))))
      (inertia.matScaleB (BPair.ofPos .one) (inertia.idMat o)) :=
    elim.matOne_trans (elim.permM_orthL o (idx ++ cpl) hsgl hjd hsg)
      (elim.matOne_symm (inertia.matScaleB_one (inertia.idMat o)))
  have hp2 : elim.matOneValue
      (elim.matMul (elim.transposeM (elim.permM o (idx ++ cpl)))
        (elim.permM o (idx ++ cpl)))
      (inertia.matScaleB (BPair.ofPos .one) (inertia.idMat o)) :=
    elim.matOne_trans
      (elim.permM_orthR o (idx ++ cpl) hsgl hjd hsg hjc)
      (elim.matOne_symm (inertia.matScaleB_one (inertia.idMat o)))
  have hPil : (elim.permM o (idx ++ cpl)).length = o :=
    (ground.length_map _ _).trans hsgl
  have hPir : elim.rowsLen o (elim.permM o (idx ++ cpl)) :=
    elim.rowsLen_permM o _
  have hPisq : elim.sqAt (elim.permM o (idx ++ cpl)) o :=
    elim.sqAt_of hPil hPir
  have hTl : (elim.transposeM (elim.permM o (idx ++ cpl))).length = o :=
    elim.length_transposeM _ hPir (by rw [hPil]; exact hopos)
  have hTr : elim.rowsLen o
      (elim.transposeM (elim.permM o (idx ++ cpl))) :=
    elim.rowsLen_cast hPil (elim.rowsLen_transposeM _)
  have hTsq : elim.sqAt (elim.transposeM (elim.permM o (idx ++ cpl))) o :=
    elim.sqAt_of hTl hTr
  have hTT : elim.transposeM
        (elim.transposeM (elim.permM o (idx ++ cpl)))
      = elim.permM o (idx ++ cpl) :=
    elim.transposeM_transposeM _ hPir hopos (by rw [hPil]; exact hopos)
  have hTTl : (elim.transposeM
      (elim.transposeM (elim.permM o (idx ++ cpl)))).length = o := by
    rw [hTT]; exact hPil
  have hSelsq : elim.sqAt (elim.selM (idx ++ cpl) (idx ++ cpl) M) o :=
    elim.sqAt_of ((elim.length_selM _ _ M).trans hsgl)
      (elim.rowsLen_cast hsgl (elim.rowsLen_selM _ M _))
  have hSelsym : elim.matOneValue
      (elim.transposeM (elim.selM (idx ++ cpl) (idx ++ cpl) M))
      (elim.selM (idx ++ cpl) (idx ++ cpl) M) :=
    elim.transposeM_selM (idx ++ cpl) (idx ++ cpl) M o hMsq hMsym
      (by rw [hsgl]; exact hopos) hsg hsg
  have spJread : inertia.splitRead (elim.selM (idx ++ cpl) (idx ++ cpl) M)
      (inertia.mkSplit o (elim.selM (idx ++ cpl) (idx ++ cpl) M)) :=
    inertia.mkSplit_read o _ hSelsq hSelsym
  have hMTl : (elim.matMul M
      (elim.transposeM (elim.permM o (idx ++ cpl)))).length = o :=
    (elim.length_matMul _ _).trans hMl
  have hMTr : elim.rowsLen o
      (elim.matMul M (elim.transposeM (elim.permM o (idx ++ cpl)))) :=
    elim.rowsLen_cast hTTl (elim.rowsLen_matMul _ _)
  have hMTt : (elim.transposeM (elim.matMul M
      (elim.transposeM (elim.permM o (idx ++ cpl))))).length = o :=
    elim.length_transposeM _ hMTr (by rw [hMTl]; exact hopos)
  have hGl : (elim.matMul
      (elim.transposeM (elim.transposeM (elim.permM o (idx ++ cpl))))
      (elim.matMul M
        (elim.transposeM (elim.permM o (idx ++ cpl))))).length = o :=
    (elim.length_matMul _ _).trans hTTl
  have hGr : elim.rowsLen o (elim.matMul
      (elim.transposeM (elim.transposeM (elim.permM o (idx ++ cpl))))
      (elim.matMul M
        (elim.transposeM (elim.permM o (idx ++ cpl))))) :=
    elim.rowsLen_cast hMTt (elim.rowsLen_matMul _ _)
  have hGsq := elim.sqAt_of hGl hGr
  have hGone : elim.matOneValue (elim.selM (idx ++ cpl) (idx ++ cpl) M)
      (elim.matMul
        (elim.transposeM (elim.transposeM (elim.permM o (idx ++ cpl))))
        (elim.matMul M
          (elim.transposeM (elim.permM o (idx ++ cpl))))) := by
    rw [hTT]
    exact elim.matOne_symm (elim.permM_conj o (idx ++ cpl) M hMsq hsg)
  have spG := inertia.splitRead_congr _ _ hGsq hGone _ spJread
  have hcongr := inertia.rev_congr (n := o) M
    (elim.transposeM (elim.permM o (idx ++ cpl)))
    (elim.permM o (idx ++ cpl)) (BPair.ofPos Pos.one)
    (ground.offOfUnitLt (ground.unitLtOfPos Pos.one))
    hMsq hTsq hPisq hp2 hp1 spx hx _ spG
  have hPvl : (elim.selM idx idx M).length = k :=
    (elim.length_selM idx idx M).trans hk
  have hPvr : elim.rowsLen k (elim.selM idx idx M) :=
    elim.rowsLen_cast hk (elim.rowsLen_selM idx M idx)
  have hPvsq : elim.sqAt (elim.selM idx idx M) k := elim.sqAt_of hPvl hPvr
  have hBvl : (elim.selM idx cpl M).length = k :=
    (elim.length_selM idx cpl M).trans hk
  have hBvr : elim.rowsLen m (elim.selM idx cpl M) :=
    elim.rowsLen_cast hcl (elim.rowsLen_selM cpl M idx)
  have hQvl : (elim.selM cpl cpl M).length = m :=
    (elim.length_selM cpl cpl M).trans hcl
  have hQvr : elim.rowsLen m (elim.selM cpl cpl M) :=
    elim.rowsLen_cast hcl (elim.rowsLen_selM cpl M cpl)
  have hQvsq : elim.sqAt (elim.selM cpl cpl M) m := elim.sqAt_of hQvl hQvr
  have hCvr : elim.rowsLen k (elim.selM cpl idx M) :=
    elim.rowsLen_cast hk (elim.rowsLen_selM idx M cpl)
  have hTBl : (elim.transposeM (elim.selM idx cpl M)).length = m :=
    elim.length_transposeM _ hBvr (by rw [hBvl]; exact hk0)
  have hTBr : elim.rowsLen k (elim.transposeM (elim.selM idx cpl M)) :=
    elim.rowsLen_cast hBvl (elim.rowsLen_transposeM _)
  have hCT : elim.matOneValue (elim.selM cpl idx M)
      (elim.transposeM (elim.selM idx cpl M)) :=
    elim.matOne_symm
      (elim.transposeM_selM idx cpl M o hMsq hMsym hidxl hidx hcpl)
  have hJoin : elim.matOneValue (elim.selM (idx ++ cpl) (idx ++ cpl) M)
      (inertia.blockJoin (elim.selM idx idx M) (elim.selM idx cpl M)
        (elim.selM cpl cpl M)) := by
    rw [elim.selM_append idx cpl M]
    show elim.matOneValue
      (List.zipWith (· ++ ·) (elim.selM idx idx M) (elim.selM idx cpl M)
        ++ List.zipWith (· ++ ·) (elim.selM cpl idx M)
          (elim.selM cpl cpl M))
      (List.zipWith (· ++ ·) (elim.selM idx idx M) (elim.selM idx cpl M)
        ++ List.zipWith (· ++ ·)
          (elim.transposeM (elim.selM idx cpl M)) (elim.selM cpl cpl M))
    exact elim.matOne_append _ _ _ _ (elim.matOne_refl _)
      (elim.matOne_rowJoin _ _ _ _ hCvr hTBr hCT
        (elim.matOne_refl _))
  have hJsq : elim.sqAt (inertia.blockJoin (elim.selM idx idx M)
      (elim.selM idx cpl M) (elim.selM cpl cpl M)) o :=
    elim.sqAt_of
      (by rw [inertia.length_blockJoin _ _ _ k m hPvl hBvl hTBl hQvl]
          exact hkm)
      (elim.rowsLen_cast hkm
        (inertia.rowsLen_blockJoin _ _ _ k m hPvr hBvr hTBr hQvr))
  have spJoin := inertia.splitRead_congr _ _ hJsq hJoin _ spJread
  have hCwl : (elim.matMul (adj2v k (elim.selM idx idx M))
      (elim.selM idx cpl M)).length = k :=
    (elim.length_matMul _ _).trans (length_adj2v _ hk12)
  have hCwr : elim.rowsLen m (elim.matMul (adj2v k (elim.selM idx idx M))
      (elim.selM idx cpl M)) :=
    elim.rowsLen_cast hTBl (elim.rowsLen_matMul _ _)
  have hPs : elim.matOneValue (elim.transposeM (elim.selM idx idx M))
      (elim.selM idx idx M) :=
    elim.transposeM_selM idx idx M o hMsq hMsym hidxl hidx hidx
  have hPw := adj2v_solve (k := k) (m := m) (elim.selM idx idx M)
    (elim.selM idx cpl M) hk12 hPvsq hBvl hBvr
  exact hcongr.symm.trans
    (rev_addN hkm (elim.selM idx idx M) (elim.selM idx cpl M)
      (elim.selM cpl cpl M) _ hPvsq hBvl hBvr hQvsq hCwl hCwr hPs hPw
      hPnz _ spJoin spP hP spD hD)

/-- The entrywise sum's row count at a shared order. -/
private theorem length_pmatAdd (n : Nat) (A B : split.PMat)
    (hA : A.length = n) (hB : B.length = n) :
    (split.pmatAdd A B).length = n :=
  ground.length_zipWith (List.zipWith poly.add) A B n hA hB

/-- The entrywise sum's rows at a shared width. -/
private theorem rowsLen_pmatAdd (n : Nat) : ∀ A B : split.PMat,
    elim.rowsLen n A → elim.rowsLen n B →
    elim.rowsLen n (split.pmatAdd A B)
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | a :: t, b :: u, hA, hB =>
    ⟨ground.length_zipWith poly.add a b n hA.1 hB.1,
     rowsLen_pmatAdd n t u hA.2 hB.2⟩

/-- The rescaling keeps the row count. -/
private theorem length_pscaleM (f : Poly) (S : split.PMat) :
    (split.pscaleM f S).length = S.length := ground.length_map _ S

/-- The memberwise swap keeps the row count. -/
private theorem length_pswapM (S : split.PMat) :
    (split.pswapM S).length = S.length := ground.length_map _ S

/-- The adjugate's row count at the small orders. -/
private theorem length_padj2 {k : Nat} (P : split.PMat)
    (hk : k = 1 ∨ k = 2) : (padj2 k P).length = k := by
  match hk with
  | Or.inl h => rw [h]; rfl
  | Or.inr h => rw [h]; rfl

/-- The cleared deflation's row count is the trailing key list's. -/
private theorem length_pdefl (idx rest : List Nat) (S : split.PMat) :
    (pdefl idx rest S).length = rest.length :=
  length_pmatAdd rest.length _ _
    ((length_pscaleM _ _).trans (split.length_pselM rest rest S))
    ((length_pswapM _).trans ((length_pscaleM _ _).trans
      ((length_pmatMul _ _).trans (split.length_pselM rest idx S))))

/-- The cleared deflation's rows sit at the trailing key list's
count. -/
private theorem rowsLen_pdefl (idx rest : List Nat) (S : split.PMat)
    (hk0 : 0 < idx.length) (hk : idx.length = 1 ∨ idx.length = 2) :
    elim.rowsLen rest.length (pdefl idx rest S) := by
  have hBpl : (split.pselM idx rest S).length = idx.length :=
    split.length_pselM _ _ _
  have hBpr : elim.rowsLen rest.length (split.pselM idx rest S) :=
    split.rowsLen_pselM _ _ _
  have hhdBp : ((split.pselM idx rest S).headD ([] : List Poly)).length
      = rest.length :=
    headD_width _ idx.length rest.length hBpl hk0 hBpr
  have hWl : (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
      (split.pselM idx rest S)).length = idx.length :=
    (length_pmatMul _ _).trans (length_padj2 _ hk)
  have hWr : elim.rowsLen rest.length
      (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
        (split.pselM idx rest S)) := by
    rw [← hhdBp]
    exact rowsLen_pmatMul _ _
  have hhdW : ((split.pmatMul (padj2 idx.length (split.pselM idx idx S))
      (split.pselM idx rest S)).headD ([] : List Poly)).length
      = rest.length :=
    headD_width _ idx.length rest.length hWl hk0 hWr
  have hZr : elim.rowsLen rest.length
      (split.pmatMul (split.pselM rest idx S)
        (split.pmatMul (padj2 idx.length (split.pselM idx idx S))
          (split.pselM idx rest S))) := by
    rw [← hhdW]
    exact rowsLen_pmatMul _ _
  exact rowsLen_pmatAdd rest.length _ _
    (rowsLen_pscaleM _ _ _ (split.rowsLen_pselM _ _ _))
    (rowsLen_pswapM _ _ (rowsLen_pscaleM _ _ _ hZr))

/-- One row pair's entrywise sum keeps a shared degree bound, a key
beyond either row reading the vacant list. -/
private theorem deg_rowAdd (N : Nat) : ∀ (r s : List Poly),
    (∀ k, (ground.getAt ([] : Poly) r k).length ≤ N)
    → (∀ k, (ground.getAt ([] : Poly) s k).length ≤ N)
    → ∀ k, (ground.getAt ([] : Poly)
        (List.zipWith poly.add r s) k).length ≤ N
  | [], _, _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _, _ => Nat.zero_le _
  | p :: _, q :: _, hr, hs, 0 => poly.add_len_le p q N (hr 0) (hs 0)
  | _ :: r, _ :: s, hr, hs, k + 1 =>
    deg_rowAdd N r s (fun l => hr (l + 1)) (fun l => hs (l + 1)) k

/-- The entrywise sum keeps a shared degree bound at every key of
every row. -/
private theorem deg_pmatAdd (N : Nat) : ∀ (A B : split.PMat),
    (∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) A i) j).length ≤ N)
    → (∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) B i) j).length ≤ N)
    → ∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (split.pmatAdd A B) i) j).length
          ≤ N
  | [], _, _, _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _, _, _ => Nat.zero_le _
  | r :: _, u :: _, hA, hB, 0, j =>
    deg_rowAdd N r u (fun l => hA 0 l) (fun l => hB 0 l) j
  | _ :: A, _ :: B, hA, hB, i + 1, j =>
    deg_pmatAdd N A B (fun l m => hA (l + 1) m)
      (fun l m => hB (l + 1) m) i j

/-- The memberwise swap keeps every entry's degree, the map's
length read. -/
private theorem deg_pswapM (N : Nat) : ∀ (X : split.PMat),
    (∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) X i) j).length ≤ N)
    → ∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (split.pswapM X) i) j).length ≤ N
  | [], _, _, _ => Nat.zero_le _
  | r :: _, h, 0, j =>
    match Nat.lt_or_ge j r.length with
    | Or.inl hj => by
      show (ground.getAt ([] : Poly)
        (r.map poly.polyOps.swap) j).length ≤ N
      rw [ground.getAt_map ([] : Poly) ([] : Poly) _ r j hj]
      show ((ground.getAt ([] : Poly) r j).map
        ground.bpairOps.swap).length ≤ N
      rw [ground.length_map]
      exact h 0 j
    | Or.inr hj => by
      show (ground.getAt ([] : Poly)
        (r.map poly.polyOps.swap) j).length ≤ N
      rw [ground.getAt_over ([] : Poly) _ j
        (by rw [ground.length_map]; exact hj)]
      exact Nat.zero_le _
  | _ :: X, h, i + 1, j => deg_pswapM N X (fun l m => h (l + 1) m) i j

/-- The scale keeps a joined degree bound, the product's length
read entrywise. -/
private theorem deg_pscaleM (f : Poly) (a N : Nat)
    (hf : f.length ≤ a + 1) : ∀ (X : split.PMat),
    (∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) X i) j).length ≤ N + 1)
    → ∀ i j, (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (split.pscaleM f X) i) j).length
          ≤ a + N + 1
  | [], _, _, _ => Nat.zero_le _
  | r :: _, h, 0, j =>
    match Nat.lt_or_ge j r.length with
    | Or.inl hj => by
      show (ground.getAt ([] : Poly)
        (r.map (poly.mul f)) j).length ≤ a + N + 1
      rw [ground.getAt_map ([] : Poly) ([] : Poly) _ r j hj]
      exact poly.mul_len_le f _ a N hf (h 0 j)
    | Or.inr hj => by
      show (ground.getAt ([] : Poly)
        (r.map (poly.mul f)) j).length ≤ a + N + 1
      rw [ground.getAt_over ([] : Poly) _ j
        (by rw [ground.length_map]; exact hj)]
      exact Nat.zero_le _
  | _ :: X, h, i + 1, j =>
    deg_pscaleM f a N hf X (fun l m => h (l + 1) m) i j

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
      (by rw [length_pmatMul]; exact h)]
    exact trivial
  | Or.inl h =>
    match Nat.lt_or_ge q (b.headD ([] : List Poly)).length with
    | Or.inr h2 =>
      rw [ground.getAt_over ([] : Poly) _ q
        (by rw [rowLen_pmatMul a b p h]; exact h2)]
      exact trivial
    | Or.inl h2 =>
      rw [getAt_pmatMul a b p q h h2]
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

/-- The order-one deflation at value-unit couplings: with the
pivot's row reading the sum's unit against every trailing key, the
correction term's every entry keeps that tail — one unit-tailed
factor carrying the whole product — and the deflation reads the
pivot entry's square on the trailing block, a key beyond the datum
reading the vacant list. -/
theorem pdefl_offC (S : split.PMat) (i : Nat) (rest : List Nat)
    (hoffR : ∀ k, k < rest.length → poly.unitTail
      (ground.getAt [] (ground.getAt [] S (ground.getAt 0 rest k)) i)) :
    split.pmatOneValue (pdefl [i] rest S)
      (split.pscaleM
        (poly.mul (ground.getAt [] (ground.getAt [] S i) i)
          (ground.getAt [] (ground.getAt [] S i) i))
        (split.pselM rest rest S)) := by
  have hBpl : (split.pselM [i] rest S).length = ([i] : List Nat).length :=
    split.length_pselM _ _ _
  have hBpr : elim.rowsLen rest.length (split.pselM [i] rest S) :=
    split.rowsLen_pselM _ _ _
  have hhdBp : ((split.pselM [i] rest S).headD ([] : List Poly)).length
      = rest.length :=
    headD_width _ ([i] : List Nat).length rest.length hBpl Nat.one_pos hBpr
  have hWl : (split.pmatMul (padj2 ([i] : List Nat).length
      (split.pselM [i] [i] S)) (split.pselM [i] rest S)).length
      = ([i] : List Nat).length :=
    (length_pmatMul _ _).trans (length_padj2 _ (Or.inl rfl))
  have hWr : elim.rowsLen rest.length
      (split.pmatMul (padj2 ([i] : List Nat).length (split.pselM [i] [i] S))
        (split.pselM [i] rest S)) := by
    rw [← hhdBp]
    exact rowsLen_pmatMul _ _
  have hhdW : ((split.pmatMul (padj2 ([i] : List Nat).length
      (split.pselM [i] [i] S)) (split.pselM [i] rest S)).headD
      ([] : List Poly)).length = rest.length :=
    headD_width _ ([i] : List Nat).length rest.length hWl Nat.one_pos hWr
  have hZr : elim.rowsLen rest.length
      (split.pmatMul (split.pselM rest [i] S)
        (split.pmatMul (padj2 ([i] : List Nat).length
          (split.pselM [i] [i] S)) (split.pselM [i] rest S))) := by
    rw [← hhdW]
    exact rowsLen_pmatMul _ _
  have hAl : (split.pscaleM (poly.mul (split.pminor (split.pselM [i] [i] S))
      (split.pminor (split.pselM [i] [i] S)))
      (split.pselM rest rest S)).length = rest.length :=
    (length_pscaleM _ _).trans (split.length_pselM rest rest S)
  have hAr : elim.rowsLen rest.length
      (split.pscaleM (poly.mul (split.pminor (split.pselM [i] [i] S))
        (split.pminor (split.pselM [i] [i] S)))
        (split.pselM rest rest S)) :=
    rowsLen_pscaleM _ _ _ (split.rowsLen_pselM _ _ _)
  have hBl : (split.pswapM (split.pscaleM
      (split.pminor (split.pselM [i] [i] S))
      (split.pmatMul (split.pselM rest [i] S)
        (split.pmatMul (padj2 ([i] : List Nat).length
          (split.pselM [i] [i] S))
          (split.pselM [i] rest S))))).length = rest.length :=
    (length_pswapM _).trans ((length_pscaleM _ _).trans
      ((length_pmatMul _ _).trans (split.length_pselM rest [i] S)))
  have hBr : elim.rowsLen rest.length (split.pswapM (split.pscaleM
      (split.pminor (split.pselM [i] [i] S))
      (split.pmatMul (split.pselM rest [i] S)
        (split.pmatMul (padj2 ([i] : List Nat).length
          (split.pselM [i] [i] S))
          (split.pselM [i] rest S))))) :=
    rowsLen_pswapM _ _ (rowsLen_pscaleM _ _ _ hZr)
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
      (ground.getAt ([] : List Poly) (split.pswapM (split.pscaleM
        (split.pminor (split.pselM [i] [i] S))
        (split.pmatMul (split.pselM rest [i] S)
          (split.pmatMul (padj2 ([i] : List Nat).length
            (split.pselM [i] [i] S))
            (split.pselM [i] rest S))))) r) k) :=
    mapRows_unit poly.neg (fun _ hp => poly.unitTail_swapMap _ hp) _
      (mapRows_unit (poly.mul (split.pminor (split.pselM [i] [i] S)))
        (fun _ hp => poly.of_unitTail_mul (Or.inr hp)) _
        (pmatMul_unitL _ _ hSelR))
  show split.pmatOneValue
    (split.pmatAdd
      (split.pscaleM (poly.mul (split.pminor (split.pselM [i] [i] S))
        (split.pminor (split.pselM [i] [i] S))) (split.pselM rest rest S))
      (split.pswapM (split.pscaleM (split.pminor (split.pselM [i] [i] S))
        (split.pmatMul (split.pselM rest [i] S)
          (split.pmatMul (padj2 ([i] : List Nat).length
            (split.pselM [i] [i] S)) (split.pselM [i] rest S))))))
    (split.pscaleM (poly.mul (split.pminor (split.pselM [i] [i] S))
      (split.pminor (split.pselM [i] [i] S))) (split.pselM rest rest S))
  refine pmatAdd_unit _ _ (hAl.trans hBl.symm) (fun r hr => ?_) hunit
  rw [hAl] at hr
  rw [elim.rowsLen_getAt _ r hAr (by rw [hAl]; exact hr),
    elim.rowsLen_getAt _ r hBr (by rw [hBl]; exact hr)]

/-- A cover on an occupied segment reads its pencil's symmetry: the
chain's end is refused there and the order-nought deflation reads
the vacant square. -/
private theorem cover_pSym {o : Nat} (S : split.PMat) (K : Nat)
    (lo hi : CPair) (hlt : lo < hi) :
    ∀ cov : Cover, coverRead S o K lo hi cov → split.pSymAt S o
  | .done, h => absurd hlt (fun hl => CPair.not_lt_of_one h.2 hl)
  | .nought, h => by
    have h0 : o = 0 := ground.beqEq _ _ h
    rw [h0]
    rfl
  | .one _ _ _ _ _ _ _, h => h.1.2.2.2.2
  | .mixed _ _ _ _ _ _ _, h => h.1.2.2.2.2
  | .twoUp _ _ _ _ _ _ _ _ _ _, h => h.1.2.2.2.2

/-- The order-one designated minor's evaluation is the evaluated
selected block's own. -/
private theorem minor1_bridge (S : split.PMat) (K i : Nat) (xn : BPair)
    (xc : Pos) :
    (poly.evalClear (split.pminor (split.pselM [i] [i] S))
        xn xc K).oneValue
      (elim.minor (elim.selM [i] [i] (evalPC S xn xc K))) := by
  rw [selM_evalPC xn xc K S [i] [i]]
  exact BPair.oneValue_refl _

/-- The order-two designated minor's degree sits within the doubled
clearing power. -/
private theorem pminor2_len {S : split.PMat} {o K : Nat}
    (hsh : pShapeAt S o K) (i0 i1 : Nat) :
    (split.pminor (split.pselM [i0, i1] [i0, i1] S)).length
      ≤ K + K + 1 := by
  show (poly.add (poly.pnorm (poly.mul
      (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i0)
      (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i1)))
    (poly.add (poly.neg (poly.pnorm (poly.mul
      (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i0) i1)
      (ground.getAt ([] : Poly) (ground.getAt ([] : List Poly) S i1) i0))))
      [])).length ≤ K + K + 1
  rw [poly.add_nil]
  refine poly.add_len_le _ _ (K + K + 1) ?_ ?_
  · rw [poly.pnorm_length]
    exact poly.mul_len_le _ _ K K (ent_ble hsh i0 i0) (ent_ble hsh i1 i1)
  · rw [poly.length_neg, poly.pnorm_length]
    exact poly.mul_len_le _ _ K K (ent_ble hsh i0 i1) (ent_ble hsh i1 i0)

/-- The cleared deflation's shape read at the pivot orders one and
two: the trailing key list's order at the pivot's odd-multiple
clearing `(2k + 1) K`, each entry the squared minor's scale of the
trailing block joined to the correction's swap at the products'
degree reads. -/
theorem pShape_pdefl (S : split.PMat) (o K : Nat) (idx rest : List Nat)
    (hS : pShapeAt S o K)
    (hk : idx.length = 1 ∨ idx.length = 2) :
    pShapeAt (pdefl idx rest S) rest.length
      ((2 * idx.length + 1) * K) := by
  have hk0 : 0 < idx.length := by
    cases hk with
    | inl h => rw [h]; exact Nat.succ_pos 0
    | inr h => rw [h]; exact Nat.succ_pos 1
  have hent := ent_ble hS
  have hdeg : ∀ i j, (ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly) (pdefl idx rest S) i) j).length
        ≤ (2 * idx.length + 1) * K + 1 := by
    cases hk with
    | inl h1 =>
      refine Exists.elim (list1E idx h1) (fun i0 hidx => ?_)
      subst hidx
      have hm : (split.pminor
          (split.pselM [i0] [i0] S)).length ≤ K + 1 := hent i0 i0
      have hadj : ∀ i j, (ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly)
            (padj2 ([i0] : List Nat).length
              (split.pselM [i0] [i0] S)) i) j).length ≤ 0 + 1 := by
        intro i j
        match i, j with
        | 0, 0 => exact Nat.le_refl 1
        | 0, _ + 1 => exact Nat.zero_le _
        | _ + 1, _ => exact Nat.zero_le _
      have hW := deg_pmatMul _ _ 0 K hadj
        (deg_pselM (K := K) hent [i0] rest)
      have hZ := deg_pmatMul _ _ K (0 + K)
        (deg_pselM (K := K) hent rest [i0]) hW
      have hAA := deg_pscaleM _ (K + K) K
        (poly.mul_len_le _ _ K K hm hm) _
        (deg_pselM (K := K) hent rest rest)
      have hBB := deg_pswapM _ _
        (deg_pscaleM _ K (K + (0 + K)) hm _ hZ)
      have he : (2 * ([i0] : List Nat).length + 1) * K
          = K + K + K := by
        show 3 * K = K + K + K
        rw [Nat.mul_comm 3 K]
        show 0 + K + K + K = K + K + K
        rw [Nat.zero_add]
      have heB : K + (K + (0 + K)) + 1 = K + K + K + 1 := by
        rw [Nat.zero_add, ← Nat.add_assoc]
      intro i j
      refine Nat.le_trans
        (deg_pmatAdd (K + K + K + 1) _ _ hAA
          (fun a b => Nat.le_trans (hBB a b) (Nat.le_of_eq heB)) i j)
        (Nat.le_of_eq (congrArg (· + 1) he.symm))
    | inr h2 =>
      refine Exists.elim (list2E idx h2) (fun i0 hex => ?_)
      refine Exists.elim hex (fun i1 hidx => ?_)
      subst hidx
      have hm := pminor2_len hS i0 i1
      have hP := deg_pselM (K := K) hent [i0, i1] [i0, i1]
      have hadj : ∀ i j, (ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly)
            (padj2 ([i0, i1] : List Nat).length
              (split.pselM [i0, i1] [i0, i1] S)) i) j).length
            ≤ K + 1 := by
        intro i j
        match i, j with
        | 0, 0 => exact hP 1 1
        | 0, 1 =>
            show (poly.neg (ground.getAt ([] : Poly)
              (ground.getAt ([] : List Poly)
                (split.pselM [i0, i1] [i0, i1] S) 0) 1)).length ≤ K + 1
            rw [poly.length_neg]
            exact hP 0 1
        | 1, 0 =>
            show (poly.neg (ground.getAt ([] : Poly)
              (ground.getAt ([] : List Poly)
                (split.pselM [i0, i1] [i0, i1] S) 1) 0)).length ≤ K + 1
            rw [poly.length_neg]
            exact hP 1 0
        | 1, 1 => exact hP 0 0
        | 0, _ + 2 => exact Nat.zero_le _
        | 1, _ + 2 => exact Nat.zero_le _
        | _ + 2, _ => exact Nat.zero_le _
      have hW := deg_pmatMul _ _ K K hadj
        (deg_pselM (K := K) hent [i0, i1] rest)
      have hZ := deg_pmatMul _ _ K (K + K)
        (deg_pselM (K := K) hent rest [i0, i1]) hW
      have hAA := deg_pscaleM _ (K + K + (K + K)) K
        (poly.mul_len_le _ _ (K + K) (K + K) hm hm) _
        (deg_pselM (K := K) hent rest rest)
      have hBB := deg_pswapM _ _
        (deg_pscaleM _ (K + K) (K + (K + K)) hm _ hZ)
      have he : (2 * ([i0, i1] : List Nat).length + 1) * K
          = K + K + (K + K) + K := by
        show 5 * K = K + K + (K + K) + K
        rw [Nat.mul_comm 5 K]
        show 0 + K + K + K + K + K = K + K + (K + K) + K
        rw [Nat.zero_add, Nat.add_assoc (K + K) K K]
      have heB : K + K + (K + (K + K)) + 1
          = K + K + (K + K) + K + 1 := by
        rw [← Nat.add_assoc (K + K) K (K + K),
          Nat.add_right_comm (K + K) K (K + K)]
      intro i j
      refine Nat.le_trans
        (deg_pmatAdd (K + K + (K + K) + K + 1) _ _ hAA
          (fun a b => Nat.le_trans (hBB a b) (Nat.le_of_eq heB)) i j)
        (Nat.le_of_eq (congrArg (· + 1) he.symm))
  refine pShapeAt_of (length_pdefl idx rest S)
    (rowsLen_pdefl idx rest S hk0 hk) ?_
  refine ground.all_of_getAt ([] : List Poly) _ _ (fun i hi => ?_)
  refine ground.all_of_getAt ([] : Poly) _ _ (fun j hj => ?_)
  exact ground.leBle (hdeg i j)

/-- The order-two designated minor's evaluation is the evaluated
selected block's own, at the doubled clearing power. -/
private theorem minor2_bridge {S : split.PMat} {o K : Nat}
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
    (BPair.oneValue_symm (minor2_read _ _ _ _))

/-- One subinterval's addition at a stage point: at a designated
minor off equal members the count splits at the pivot's own split
and the cleared deflation's, the deflation carried across the
evaluated blocks' read. -/
private theorem piece_add {o m : Nat} (S : split.PMat) (K KK : Nat)
    (lo b : CPair) (idx : List Nat)
    (hpc : pieceRead S o K lo b idx)
    (hk : idx.length = 1 ∨ idx.length = 2)
    (hm : (compl idx o).length = m)
    (hKK : KK = (2 * idx.length + 1) * K)
    (xn : BPair) (xc : Pos)
    (hPnz : ¬ (elim.minor
      (elim.selM idx idx (evalPC S xn xc K))).oneValue BPair.unit)
    (spx : inertia.Split o)
    (hx : inertia.splitRead (evalPC S xn xc K) spx)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (evalPC (pdefl idx (compl idx o) S) xn xc KK) spD) :
    inertia.revAt spx
      = inertia.revAt (inertia.mkSplit idx.length
          (elim.selM idx idx (evalPC S xn xc K)))
        + inertia.revAt spD := by
  subst hKK
  have hidx := hpc.2.1
  have hdix := hpc.2.2.1
  have hsh := hpc.2.2.2.1
  have hsym := hpc.2.2.2.2
  have hSl := pShape_len hsh
  have hSr := pShape_rows hsh
  have hMl : (evalPC S xn xc K).length = o :=
    (length_evalPC S xn xc K).trans hSl
  have hMr : elim.rowsLen o (evalPC S xn xc K) :=
    rowsLen_evalPC o S xn xc K hSr
  have hMsq : elim.sqAt (evalPC S xn xc K) o := elim.sqAt_of hMl hMr
  have hMsym := evalPC_sym (S := S) (o := o) xn xc K hSl hSr hsym
  have hk0 : 0 < idx.length := by
    match hk with
    | Or.inl h => rw [h]; exact Nat.succ_pos 0
    | Or.inr h => rw [h]; exact Nat.succ_pos 1
  have hsgl : (idx ++ compl idx o).length = o := by
    rw [ground.length_append]
    exact compl_length hpc.2.2.1 hpc.2.1
  have hkm : idx.length + m = o := by
    rw [← hm, ← ground.length_append]
    exact hsgl
  have hPvl : (elim.selM idx idx (evalPC S xn xc K)).length
      = idx.length := elim.length_selM idx idx _
  have hPvr : elim.rowsLen idx.length
      (elim.selM idx idx (evalPC S xn xc K)) :=
    elim.rowsLen_selM idx _ idx
  have hPvsq : elim.sqAt (elim.selM idx idx (evalPC S xn xc K))
      idx.length := elim.sqAt_of hPvl hPvr
  have hPvsym : elim.matOneValue
      (elim.transposeM (elim.selM idx idx (evalPC S xn xc K)))
      (elim.selM idx idx (evalPC S xn xc K)) :=
    elim.transposeM_selM idx idx _ o hMsq hMsym hk0 hidx hidx
  have hPread := inertia.mkSplit_read idx.length _ hPvsq hPvsym
  have hBvl : (elim.selM idx (compl idx o) (evalPC S xn xc K)).length
      = idx.length := elim.length_selM idx _ _
  have hBvr : elim.rowsLen m
      (elim.selM idx (compl idx o) (evalPC S xn xc K)) :=
    elim.rowsLen_cast hm (elim.rowsLen_selM (compl idx o) _ idx)
  have hQvl : (elim.selM (compl idx o) (compl idx o)
      (evalPC S xn xc K)).length = m :=
    (elim.length_selM _ _ _).trans hm
  have hQvr : elim.rowsLen m (elim.selM (compl idx o) (compl idx o)
      (evalPC S xn xc K)) :=
    elim.rowsLen_cast hm (elim.rowsLen_selM (compl idx o) _ (compl idx o))
  have hTBl : (elim.transposeM (elim.selM idx (compl idx o)
      (evalPC S xn xc K))).length = m :=
    elim.length_transposeM _ hBvr (by rw [hBvl]; exact hk0)
  have hCwl : (elim.matMul (adj2v idx.length
      (elim.selM idx idx (evalPC S xn xc K)))
      (elim.selM idx (compl idx o) (evalPC S xn xc K))).length
      = idx.length :=
    (elim.length_matMul _ _).trans (length_adj2v _ hk)
  have hCwr : elim.rowsLen m (elim.matMul (adj2v idx.length
      (elim.selM idx idx (evalPC S xn xc K)))
      (elim.selM idx (compl idx o) (evalPC S xn xc K))) :=
    elim.rowsLen_cast hTBl (elim.rowsLen_matMul _ _)
  have hTCwl : (elim.transposeM (elim.matMul (adj2v idx.length
      (elim.selM idx idx (evalPC S xn xc K)))
      (elim.selM idx (compl idx o) (evalPC S xn xc K)))).length = m :=
    elim.length_transposeM _ hCwr (by rw [hCwl]; exact hk0)
  have hDefl : elim.matOneValue
      (evalPC (pdefl idx (compl idx o) S) xn xc
        ((2 * idx.length + 1) * K))
      (inertia.deflMat (elim.selM idx idx (evalPC S xn xc K))
        (elim.selM idx (compl idx o) (evalPC S xn xc K))
        (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
        (elim.matMul (adj2v idx.length
            (elim.selM idx idx (evalPC S xn xc K)))
          (elim.selM idx (compl idx o) (evalPC S xn xc K)))) := by
    rw [selM_evalPC xn xc K S idx idx,
      selM_evalPC xn xc K S (compl idx o) idx,
      selM_evalPC xn xc K S (compl idx o) (compl idx o)]
    exact evalPC_pdefl (o := o) S K idx (compl idx o) xn xc hsh hsym
      hk hidx (all_compl idx o)
  have hDsq := inertia.sqAt_deflMat
    (elim.selM idx idx (evalPC S xn xc K))
    (elim.selM idx (compl idx o) (evalPC S xn xc K))
    (elim.selM (compl idx o) (compl idx o) (evalPC S xn xc K))
    (elim.matMul (adj2v idx.length
        (elim.selM idx idx (evalPC S xn xc K)))
      (elim.selM idx (compl idx o) (evalPC S xn xc K)))
    m hTBl hTCwl hQvl hQvr
  have hD' := inertia.splitRead_congr _ _ hDsq hDefl spD hD
  exact rev_perm_add (evalPC S xn xc K) idx (compl idx o) rfl hm hkm
    hk hMsq hMsym hidx (all_compl idx o)
    (distinct_append_compl (o := o) hdix)
    (cover_append_compl (o := o) (idx := idx)) hPnz spx hx _ hPread
    spD hD'

/-- One subinterval's constancy: at a designated minor keeping its
side along the subinterval the count reads the pivot's fixed block
value joined to the cleared deflation's. -/
private theorem piece_key {o m : Nat} (S : split.PMat) (K KK : Nat)
    (lo b : CPair) (idx : List Nat) (r : Nat)
    (hpc : pieceRead S o K lo b idx)
    (hk : idx.length = 1 ∨ idx.length = 2)
    (hm : (compl idx o).length = m)
    (hKK : KK = (2 * idx.length + 1) * K)
    (hside : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
      (⟨zn, zc⟩ : CPair) ≤ b →
      (¬ (elim.minor
          (elim.selM idx idx (evalPC S zn zc K))).oneValue BPair.unit)
      ∧ inertia.revAt (inertia.mkSplit idx.length
          (elim.selM idx idx (evalPC S zn zc K))) = r)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b)
    (spz : inertia.Split o)
    (hz : inertia.splitRead (evalPC S zn zc K) spz)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (evalPC (pdefl idx (compl idx o) S) zn zc KK) spD) :
    inertia.revAt spz = r + inertia.revAt spD := by
  have hs := hside zn zc hlz hzb
  rw [← hs.2]
  exact piece_add S K KK lo b idx hpc hk hm hKK zn zc hs.1 spz hz spD hD

/-- The order-one designated block's frame at a stage point: the
minor's side is the block table's entry side, and the pivot's split
reads the table. -/
private theorem side_one {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (i : Nat) (up : Bool) (N D : BPair)
    (hsh : pShapeAt S o K) (hsym : split.pSymAt S o)
    (hidx : (([i] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : if up = true
      then stage.keepUpper (ground.getAt [] (ground.getAt [] S i) i)
        lo b N D
      else stage.keepLower (ground.getAt [] (ground.getAt [] S i) i)
        lo b N D)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b) :
    (¬ (elim.minor
        (elim.selM [i] [i] (evalPC S zn zc K))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i] : List Nat).length
        (elim.selM [i] [i] (evalPC S zn zc K)))
      = (if up = true then 0 else 1) := by
  have hSl := pShape_len hsh
  have hSr := pShape_rows hsh
  have hMsq : elim.sqAt (evalPC S zn zc K) o :=
    elim.sqAt_of ((length_evalPC S zn zc K).trans hSl)
      (rowsLen_evalPC o S zn zc K hSr)
  have hMsym := evalPC_sym (S := S) (o := o) zn zc K hSl hSr hsym
  have hPvsq : elim.sqAt (elim.selM [i] [i] (evalPC S zn zc K)) 1 :=
    elim.sqAt_of (elim.length_selM [i] [i] (evalPC S zn zc K))
      (elim.rowsLen_selM [i] (evalPC S zn zc K) [i])
  have hPvsym := elim.transposeM_selM [i] [i] (evalPC S zn zc K) o
    hMsq hMsym (Nat.succ_pos 0) hidx hidx
  have hPread := inertia.mkSplit_read 1 _ hPvsq hPvsym
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
    refine And.intro (ground.offOfUnitLt h3) ?_
    exact (inertia.rev_one (d := ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) i)
      (ground.offOfUnitLt h3)
      (inertia.mkSplit 1 (elim.selM [i] [i] (evalPC S zn zc K)))
      hPread).trans (inertia.rev_one_le (ground.leB_of_lt h3))
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
    refine And.intro (ground.offOfLtUnit h3) ?_
    exact (inertia.rev_one (d := ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) i)
      (ground.offOfLtUnit h3)
      (inertia.mkSplit 1 (elim.selM [i] [i] (evalPC S zn zc K)))
      hPread).trans (inertia.rev_one_lt h3)

/-- The order-two designated block's frame at a stage point: the
coupling's exchange reads its partner and the block's determinant
reads the selected minor. -/
private theorem two_frame {o : Nat} (S : split.PMat) (K : Nat) (i j : Nat)
    (hsym : split.pSymAt S o) (hi : i < o) (hj : j < o) (zn : BPair)
    (zc : Pos) :
    (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) j)
        i).oneValue
      (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) j)
    ∧ ((inertia.SBlock.two
        (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) i)
        (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) j)
        (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (evalPC S zn zc K) j)
          j)).det).oneValue
      (elim.minor (elim.selM [i, j] [i, j] (evalPC S zn zc K))) := by
  have hb : (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (evalPC S zn zc K) j) i).oneValue
      (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (evalPC S zn zc K) i) j) := by
    rw [getAt_evalPC zn zc K S j i, getAt_evalPC zn zc K S i j]
    exact poly.evalClear_congr (sym_at hsym j i hj hi) zn zc K
  refine And.intro hb ?_
  exact BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (ground.swap_congr
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_symm hb))))
      (BPair.oneValue_symm (minor2_read _ _ _ _)))

/-- The mixed order-two block's frame: the determinant on its lower
side reads one unit per side. -/
private theorem side_mixed {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (i j : Nat) (N D : BPair)
    (hsh : pShapeAt S o K) (hsym : split.pSymAt S o)
    (hidx : (([i, j] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : stage.keepLower
      (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b) :
    (¬ (elim.minor (elim.selM [i, j] [i, j]
        (evalPC S zn zc K))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i, j] : List Nat).length
        (elim.selM [i, j] [i, j] (evalPC S zn zc K))) = 1 := by
  have hs1 := ground.andSplitB hidx
  have hs2 := ground.andSplitB hs1.2
  have hi : i < o := ground.bltLt hs1.1
  have hj : j < o := ground.bltLt hs2.1
  have hSl := pShape_len hsh
  have hSr := pShape_rows hsh
  have hMsq : elim.sqAt (evalPC S zn zc K) o :=
    elim.sqAt_of ((length_evalPC S zn zc K).trans hSl)
      (rowsLen_evalPC o S zn zc K hSr)
  have hMsym := evalPC_sym (S := S) (o := o) zn zc K hSl hSr hsym
  have hPvsq : elim.sqAt (elim.selM [i, j] [i, j]
      (evalPC S zn zc K)) 2 :=
    elim.sqAt_of (elim.length_selM [i, j] [i, j] (evalPC S zn zc K))
      (elim.rowsLen_selM [i, j] (evalPC S zn zc K) [i, j])
  have hPvsym := elim.transposeM_selM [i, j] [i, j]
    (evalPC S zn zc K) o hMsq hMsym (Nat.succ_pos 1) hidx hidx
  have hPread := inertia.mkSplit_read 2 _ hPvsq hPvsym
  have hfr := two_frame S K i j hsym hi hj zn zc
  have h2 : poly.evalClear (split.pminor (split.pselM [i, j] [i, j] S))
      zn zc (K + K) < BPair.unit :=
    sideDown_shift _ zn zc (K + K) (pminor2_len hsh i j)
      (sideDown_rep _ zn zc
        (stage.keepLower_all _ lo b N D hside ⟨zn, zc⟩ hlz hzb))
  have h3 : elim.minor (elim.selM [i, j] [i, j]
      (evalPC S zn zc K)) < BPair.unit :=
    BPair.lt_congr (minor2_bridge hsh i j zn zc) (BPair.oneValue_refl _) h2
  have h4 := BPair.lt_congr (BPair.oneValue_symm hfr.2)
    (BPair.oneValue_refl BPair.unit) h3
  refine And.intro (ground.offOfLtUnit h3) ?_
  exact (inertia.rev_two hfr.1 (ground.offOfLtUnit h4)
    (inertia.mkSplit 2 (elim.selM [i, j] [i, j] (evalPC S zn zc K)))
    hPread).trans (inertia.rev_two_detLt h4)

/-- The upper order-two block's frame: the determinant on its upper
side with the leading entry's own side reading the table. -/
private theorem side_twoUp {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (i j : Nat) (N D : BPair) (eUp : Bool) (eN eD : BPair)
    (hsh : pShapeAt S o K) (hsym : split.pSymAt S o)
    (hidx : (([i, j] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : stage.keepUpper
      (split.pminor (split.pselM [i, j] [i, j] S)) lo b N D)
    (hent : if eUp = true
      then stage.keepUpper (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) i) lo b eN eD
      else stage.keepLower (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) S i) i) lo b eN eD)
    (zn : BPair) (zc : Pos) (hlz : lo ≤ ⟨zn, zc⟩)
    (hzb : (⟨zn, zc⟩ : CPair) ≤ b) :
    (¬ (elim.minor (elim.selM [i, j] [i, j]
        (evalPC S zn zc K))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i, j] : List Nat).length
        (elim.selM [i, j] [i, j] (evalPC S zn zc K)))
      = (if eUp = true then 0 else 2) := by
  have hs1 := ground.andSplitB hidx
  have hs2 := ground.andSplitB hs1.2
  have hi : i < o := ground.bltLt hs1.1
  have hj : j < o := ground.bltLt hs2.1
  have hSl := pShape_len hsh
  have hSr := pShape_rows hsh
  have hMsq : elim.sqAt (evalPC S zn zc K) o :=
    elim.sqAt_of ((length_evalPC S zn zc K).trans hSl)
      (rowsLen_evalPC o S zn zc K hSr)
  have hMsym := evalPC_sym (S := S) (o := o) zn zc K hSl hSr hsym
  have hPvsq : elim.sqAt (elim.selM [i, j] [i, j]
      (evalPC S zn zc K)) 2 :=
    elim.sqAt_of (elim.length_selM [i, j] [i, j] (evalPC S zn zc K))
      (elim.rowsLen_selM [i, j] (evalPC S zn zc K) [i, j])
  have hPvsym := elim.transposeM_selM [i, j] [i, j]
    (evalPC S zn zc K) o hMsq hMsym (Nat.succ_pos 1) hidx hidx
  have hPread := inertia.mkSplit_read 2 _ hPvsq hPvsym
  have hfr := two_frame S K i j hsym hi hj zn zc
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
  have h4 := BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm hfr.2) h3
  refine And.intro (ground.offOfUnitLt h3) ?_
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
    exact (inertia.rev_two hfr.1 (ground.offOfUnitLt h4)
      (inertia.mkSplit 2 (elim.selM [i, j] [i, j] (evalPC S zn zc K)))
      hPread).trans (inertia.rev_two_nil (ground.leB_of_lt h4) (ground.leB_of_lt e3))
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
    exact (inertia.rev_two hfr.1 (ground.offOfUnitLt h4)
      (inertia.mkSplit 2 (elim.selM [i, j] [i, j] (evalPC S zn zc K)))
      hPread).trans (inertia.rev_two_cols h4 e3)

/-- The designated places and their complement total the order, the
places' permutation the warrant. -/
private theorem compl_len {o : Nat} (S : split.PMat) (K : Nat)
    (lo b : CPair) (idx : List Nat) (hpc : pieceRead S o K lo b idx) :
    idx.length + (compl idx o).length = o :=
  compl_length hpc.2.2.1 hpc.2.1

/-- One subinterval's step in the chain: inside it every point reads
the piece's fixed value against the deflation's own constant count,
past it the chain's remainder carries the count to the shared
endpoint. -/
private theorem chain_step {o m : Nat} (S : split.PMat) (K KK : Nat)
    (lo b hi : CPair) (idx : List Nat) (r : Nat)
    (hpc : pieceRead S o K lo b idx)
    (hk : idx.length = 1 ∨ idx.length = 2)
    (hm : (compl idx o).length = m)
    (hKK : KK = (2 * idx.length + 1) * K)
    (hlt : lo < b)
    (hside : ∀ (zn : BPair) (zc : Pos), lo ≤ ⟨zn, zc⟩ →
      (⟨zn, zc⟩ : CPair) ≤ b →
      (¬ (elim.minor
          (elim.selM idx idx (evalPC S zn zc K))).oneValue BPair.unit)
      ∧ inertia.revAt (inertia.mkSplit idx.length
          (elim.selM idx idx (evalPC S zn zc K))) = r)
    (hDsym : split.pSymAt (pdefl idx (compl idx o) S) m)
    (ihSub : ∀ (un : BPair) (uc : Pos) (vn : BPair) (vc : Pos),
      lo ≤ ⟨un, uc⟩ → (⟨un, uc⟩ : CPair) ≤ b →
      lo ≤ ⟨vn, vc⟩ → (⟨vn, vc⟩ : CPair) ≤ b →
      ∀ (spu spv : inertia.Split m),
        inertia.splitRead
          (evalPC (pdefl idx (compl idx o) S) un uc KK) spu →
        inertia.splitRead
          (evalPC (pdefl idx (compl idx o) S) vn vc KK) spv →
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
  have hk0 : 0 < idx.length := by
    match hk with
    | Or.inl h => rw [h]; exact Nat.succ_pos 0
    | Or.inr h => rw [h]; exact Nat.succ_pos 1
  have hDl : (pdefl idx (compl idx o) S).length = m :=
    (length_pdefl idx (compl idx o) S).trans hm
  have hDr : elim.rowsLen m (pdefl idx (compl idx o) S) := by
    rw [← hm]
    exact rowsLen_pdefl idx (compl idx o) S hk0 hk
  have mkD : ∀ (zn : BPair) (zc : Pos), inertia.splitRead
      (evalPC (pdefl idx (compl idx o) S) zn zc KK)
      (inertia.mkSplit m
        (evalPC (pdefl idx (compl idx o) S) zn zc KK)) := by
    intro zn zc
    refine inertia.mkSplit_read m _
      (elim.sqAt_of
        ((length_evalPC (pdefl idx (compl idx o) S) zn zc KK).trans hDl)
        (rowsLen_evalPC m (pdefl idx (compl idx o) S) zn zc KK hDr))
      ?_
    exact evalPC_sym (S := pdefl idx (compl idx o) S) (o := m)
      zn zc KK hDl hDr hDsym
  have hsh := hpc.2.2.2.1
  have hsym := hpc.2.2.2.2
  have hSl := pShape_len hsh
  have hSr := pShape_rows hsh
  have hbread : inertia.splitRead (evalPC S bn bc K)
      (inertia.mkSplit o (evalPC S bn bc K)) :=
    inertia.mkSplit_read o _
      (elim.sqAt_of ((length_evalPC S bn bc K).trans hSl)
        (rowsLen_evalPC o S bn bc K hSr))
      (evalPC_sym (S := S) (o := o) bn bc K hSl hSr hsym)
  have key : ∀ (zn : BPair) (zc : Pos),
      (⟨lon, loc⟩ : CPair) ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ ⟨bn, bc⟩ →
      ∀ (spz : inertia.Split o),
        inertia.splitRead (evalPC S zn zc K) spz →
        inertia.revAt spz = r + inertia.revAt (inertia.mkSplit m
          (evalPC (pdefl idx (compl idx o) S) lon loc KK)) := by
    intro zn zc hlz hzb spz hz
    have h1 := piece_key S K KK ⟨lon, loc⟩ ⟨bn, bc⟩ idx r hpc hk hm hKK
      hside zn zc hlz hzb
      spz hz (inertia.mkSplit m
        (evalPC (pdefl idx (compl idx o) S) zn zc KK)) (mkD zn zc)
    rw [h1]
    exact congrArg (fun t => r + t)
      (ihSub zn zc lon loc hlz hzb (CPair.le_refl ⟨lon, loc⟩) (Or.inr hlt)
        _ _ (mkD zn zc) (mkD lon loc))
  have final : ∀ (zn : BPair) (zc : Pos),
      (⟨lon, loc⟩ : CPair) ≤ ⟨zn, zc⟩ → (⟨zn, zc⟩ : CPair) ≤ hi →
      ∀ (spz : inertia.Split o),
        inertia.splitRead (evalPC S zn zc K) spz →
        inertia.revAt spz = r + inertia.revAt (inertia.mkSplit m
          (evalPC (pdefl idx (compl idx o) S) lon loc KK)) := by
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

/-- The cover's constancy walk: the chain's end at one composite
point, the order-nought deflation at the vacant count, and each
piece at its own block value with the deflation's cover beneath and
the chain's remainder beside it. -/
private theorem cover_go : ∀ (cov : Cover) (o : Nat) (S : split.PMat)
    (K : Nat) (lo hi : CPair), coverRead S o K lo hi cov →
    ∀ (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos),
      lo ≤ ⟨xn, xc⟩ → (⟨xn, xc⟩ : CPair) ≤ hi →
      lo ≤ ⟨yn, yc⟩ → (⟨yn, yc⟩ : CPair) ≤ hi →
    ∀ (spx spy : inertia.Split o),
      inertia.splitRead (evalPC S xn xc K) spx →
      inertia.splitRead (evalPC S yn yc K) spy →
      inertia.revAt spx = inertia.revAt spy
  | .done => by
    intro o S K lo hi h xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hxlo : lo.oneValue ⟨xn, xc⟩ :=
      CPair.le_antisymm hlx (CPair.le_trans hxh (Or.inl (CPair.oneValue_symm h.2)))
    have hylo : lo.oneValue ⟨yn, yc⟩ :=
      CPair.le_antisymm hly (CPair.le_trans hyh (Or.inl (CPair.oneValue_symm h.2)))
    exact rev_point S K (pShape_len h.1) (pShape_rows h.1) (ent_ble h.1)
      xn xc yn yc
      (CPair.oneValue_trans (CPair.oneValue_symm hxlo) hylo) spx spy hx hy
  | .nought => by
    intro o S K lo hi h xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have h0 : o = 0 := ground.beqEq _ _ h
    subst h0
    rw [inertia.revAt_zero spx, inertia.revAt_zero spy]
  | .one b i up N D sub rest => by
    intro o S K lo hi h xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hlt : lo < b := by
      match up, h.2.1 with
      | true, hs => exact hs.2.1
      | false, hs => exact hs.2.1
    have hsum := compl_len S K lo b [i] h.1
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans (congrArg (fun t => t - 1) hsum)
    exact chain_step S K (3 * K) lo b hi [i] (if up = true then 0 else 1)
      h.1 (Or.inl rfl) hcl rfl hlt
      (side_one S K lo b i up N D h.1.2.2.2.1 h.1.2.2.2.2 h.1.2.1 h.2.1)
      (cover_pSym (pdefl [i] (compl [i] o) S) (3 * K) lo b hlt sub h.2.2.1)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_go sub (o - 1) (pdefl [i] (compl [i] o) S) (3 * K) lo b
          h.2.2.1
          un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_go rest o S K b hi h.2.2.2 un uc vn vc h1 h2 h3 h4
          spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy
  | .mixed b i j N D sub rest => by
    intro o S K lo hi h xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hlt : lo < b := h.2.1.2.1
    have hsum := compl_len S K lo b [i, j] h.1
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans (congrArg (fun t => t - 2) hsum)
    exact chain_step S K (5 * K) lo b hi [i, j] 1
      h.1 (Or.inr rfl) hcl rfl hlt
      (side_mixed S K lo b i j N D h.1.2.2.2.1 h.1.2.2.2.2 h.1.2.1 h.2.1)
      (cover_pSym (pdefl [i, j] (compl [i, j] o) S) (5 * K) lo b hlt sub
        h.2.2.1)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_go sub (o - 2) (pdefl [i, j] (compl [i, j] o) S) (5 * K) lo b
          h.2.2.1 un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_go rest o S K b hi h.2.2.2 un uc vn vc h1 h2 h3 h4
          spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy
  | .twoUp b i j N D eUp eN eD sub rest => by
    intro o S K lo hi h xn xc yn yc hlx hxh hly hyh spx spy hx hy
    have hlt : lo < b := h.2.1.2.1
    have hsum := compl_len S K lo b [i, j] h.1
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans (congrArg (fun t => t - 2) hsum)
    exact chain_step S K (5 * K) lo b hi [i, j] (if eUp = true then 0 else 2)
      h.1 (Or.inr rfl) hcl rfl hlt
      (side_twoUp S K lo b i j N D eUp eN eD h.1.2.2.2.1 h.1.2.2.2.2
        h.1.2.1 h.2.1 h.2.2.1)
      (cover_pSym (pdefl [i, j] (compl [i, j] o) S) (5 * K) lo b hlt sub
        h.2.2.2.1)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_go sub (o - 2) (pdefl [i, j] (compl [i, j] o) S) (5 * K) lo b
          h.2.2.2.1 un uc vn vc h1 h2 h3 h4 spu spv hu hv)
      (fun un uc vn vc h1 h2 h3 h4 spu spv hu hv =>
        cover_go rest o S K b hi h.2.2.2.2 un uc vn vc h1 h2 h3 h4
          spu spv hu hv)
      xn xc yn yc hlx hxh hly hyh spx spy hx hy

/-- `lem:cellcount`'s constancy: at a valid cover the reversal count
reads one integer at every point of the segment — any two stated
points' splits at the cleared evaluations read one count, the
representatives entering as data. -/
theorem cover_const {o : Nat} (S : split.PMat) (K : Nat)
    (lo hi : CPair) (cov : Cover)
    (h : coverRead S o K lo hi cov)
    (xn : BPair) (xc : Pos) (yn : BPair) (yc : Pos)
    (hlx : lo ≤ ⟨xn, xc⟩) (hxh : (⟨xn, xc⟩ : CPair) ≤ hi)
    (hly : lo ≤ ⟨yn, yc⟩) (hyh : (⟨yn, yc⟩ : CPair) ≤ hi)
    (spx spy : Split o)
    (hx : splitRead (evalPC S xn xc K) spx)
    (hy : splitRead (evalPC S yn yc K) spy) :
    revAt spx = revAt spy :=
  cover_go cov o S K lo hi h xn xc yn yc hlx hxh hly hyh spx spy hx hy

/-- The pointwise count: the reversal count at the cleared
evaluation, the shape read a conjunct. -/
def countAt {o : Nat} (S : split.PMat) (K : Nat) (ln : BPair)
    (c : Pos) (n : Nat) (sp : Split o) : Prop :=
  pShapeAt S o K
  ∧ splitRead (evalPC S ln c K) sp
  ∧ revAt sp = n

instance {o : Nat} (S : split.PMat) (K : Nat) (ln : BPair) (c : Pos)
    (n : Nat) (sp : Split o) :
    Decidable (countAt S K ln c n sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _))

/-- The count is a cell function, read once (`lem:cellcount`'s
constancy at the count certificate): on a covered segment a sampled
count holds at every point, the target's stated split reading the
sample's value. -/
theorem cellCount {o : Nat} (S : split.PMat) (K n : Nat)
    (lo hi : CPair) (cov : Cover)
    (hc : coverRead S o K lo hi cov)
    (sn : BPair) (sc : Pos)
    (hls : lo ≤ (⟨sn, sc⟩ : CPair)) (hsh : (⟨sn, sc⟩ : CPair) ≤ hi)
    (sps : inertia.Split o)
    (hs : countAt S K sn sc n sps)
    (tn : BPair) (tc : Pos)
    (hlt : lo ≤ (⟨tn, tc⟩ : CPair)) (hth : (⟨tn, tc⟩ : CPair) ≤ hi)
    (spt : inertia.Split o)
    (ht : inertia.splitRead (evalPC S tn tc K) spt) :
    inertia.revAt spt = n :=
  (cover_const S K lo hi cov hc tn tc sn sc hlt hth hls hsh
    spt sps ht hs.2.1).trans hs.2.2

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

instance (D : Poly) (ct : DivCert) : Decidable (divRead D ct) :=
  inferInstanceAs
    (Decidable (stagesplit.sqfreeRead _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))

/-- The divisor's certificate read is one value across the
divisor's representatives (`stagesplit.sqfreeRead_congr`). -/
theorem divRead_congr {D D' : Poly} (h : poly.oneValue D D')
    (ct : DivCert) : divRead D ct ↔ divRead D' ct :=
  stagesplit.sqfreeRead_congr h ct.g ct.a ct.b ct.sq ct.u ct.v
    ct.u2 ct.v2 ct.cg ct.cA ct.cB ct.cS ct.cb ct.c2


end cellcount
