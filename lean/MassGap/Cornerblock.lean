import MassGap.Cornerpivot
import MassGap.Spectator
/-!
`lem:cornerblock` — the block chain's ball tier: the center
family with its pairs (`CenterFam`, its read `famRead`) on the
decimated head's chain, the per-depth stated centers the family's
own evaluations, one matrix polynomial in the scale and the depth's
pair reads.  `ball_step_of` is the one-depth
transport: `lem:spectator`(iii)'s image deviation joined to the defect at
the deviation's triangle, the modulus absorbing the contracted
image inside the radius.  `crossing_rebound` is the crossing's rank-one
read: the join's withdrawn term is the recursion witness's
sandwich of the crossing pivot, priced by the withdrawn diagonal —
the positive part at the crossing's stated order-one-lower
presentation — the following pivot at or beyond its diagonal less
the transfer at the congruence determinant's squared clearing.  `strict_lift` and `cap_lift` read the ground
witness and the cap pair through the compression unchanged: a
compressed strict vector occupies the count, and the compressed
two-member cap reads force it at two, the congruence transporting
the forms.  `rebound_floor` is the rebound's seed floor: the
diagonal's floor less the transfer's cap clears the following
pivot, the two comparisons carried through the rebound and closed
against the seed comparison with the crossing's congruence
determinant cancelling.  `domRead` walks the dominance tail
deep-first in lockstep with the chain — per depth the diagonal's
floor at the coordinates' fold of squares and the depth's floor
pair, per bond the square's cap, each deeper depth one
cross-multiplied comparison, and the seed arm at the crossing's
following depth, whose floor is the rebound's own.  `domTail_psd`
reads past the crossing every deep pivot's stated split on the
upper side throughout, the floor list's read, and `domTail_cross`
locates the seed arm's crossing split at the region length's
position.
`famChainRead` reads the chain's stated data at the center family
over the segment's depth range, deep-first — position `p` at depth
`m0 + (diag.length - 1 - p)`, the boundary seed at `m0` the last
position — each stated diagonal at the clearing's stated power
against the family's evaluated diagonal at its position's own
depth, each bond the stated bond, and the four walks' and three
clearing certificates' boxes holding every segment depth's scale
point; `famYc` is the family's evaluated center at a depth with its
clearing's own margin, and `famChain_psd` walks the segment at the
family: from the boundary seed's cap at depth `m0` the one-depth
transport hands each ball from the shallower center to the deeper,
every pivot at its position's own depth in its center's ball, and
every pivot's every stated split reads the upper side throughout,
the slab fold at the count's unit.  `famChainCount` closes the
chain's count at the certificate, the center family its data: the
count splits over the depth pivots (`lem:greenprod`(ii)), the
walked segment's stated splits read vacant at the family's balls,
the crossing's split reads its one lower unit and the dominance
tail's floors read every deeper split vacant, so every split of
the assembled datum reads the count at one.

`lem:cornerblock`'s reads at the carrier are the evaluated glue.  A profile's collapse evaluated
at a composite point and cleared at a stated power is `evalProf`, a
site datum's entrywise shape read at that power is `pfmShape`,
and the evaluated site datum is `evalPfm` — the family's per-depth
collapse read entrywise (`cellcount.evalPC` at `pfmDepth`).  The
magnitude price is `evalProf_mag`: the slab walk's weights are
natural, so the entrywise magnitude profile's collapse dominates
the profile's own key by key, and the positive point prices the two
folds (`thm:windowsep`'s sum and product laws).  The row glue
`domRow_le` reads one row certificate — `boxRead_pos` prices the
gap profile's collapse strictly above the sum's unit at the
certificate's own clearing, `poly.evalClear_pow` transports that
read to the shared power, and the gap profile's split prices the
diagonal entry above the off-row magnitude fold's own evaluation —
so `domCert_domAt` walks the certificate list into
`thm:decimation`(ii)'s dominance read on the evaluated site datum,
and `domCert_form` closes the form at or above the sum's unit at
every vector of the site's order, `decimation.dom_unit` at the
dominance read.  Everything evaluates at one stated
clearing power, each row certificate's own transported up; the
square and symmetry reads are `decimation.dom_unit`'s own binders,
the dominance walk reading the magnitudes alone, and the per-entry
shape binders are the site's frame — the derivations consume each
row certificate's own shape alone.
-/

namespace cornerblock
open ground poly elim inertia greenprod spectator cornerpivot

/-- The family's shape read at the stated clearing: every entry's
slab keys sit inside the clearing power, the cleared evaluation's
faithfulness conjunct at the matrix carrier (`lem:cellcount`'s
shape discipline at `lem:cornerblock`'s center family). -/
def pfmShape (A : List (List (poly.PPoly × poly.PPoly)))
    (K : Nat) : Prop :=
  (A.all (fun r => r.all (fun e =>
    bleGo K 0 e.1 && bleGo K 1 e.2))) = true

instance instCornerblock4 (A : List (List (poly.PPoly × poly.PPoly))) (K : Nat) :
    Decidable (pfmShape A K) := inferInstanceAs (Decidable (_ = _))

/-- The family's shape read prices every entry's collapse inside the
stated clearing power at every depth, a key beyond the family's own
lists reading the vacant profile's collapse. -/
theorem pfmShape_le {A : List (List (poly.PPoly × poly.PPoly))}
    {K : Nat} (h : pfmShape A K) (m : Nat) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ K + 1 := by
  intro i j
  match Nat.lt_or_ge i A.length with
  | Or.inr hge =>
    rw [ground.getAt_over ([] : List (poly.PPoly × poly.PPoly)) A i hge]
    exact Nat.zero_le _
  | Or.inl hlt =>
    have hrow := ground.all_getAt ([] : List (poly.PPoly × poly.PPoly))
      A h i hlt
    match Nat.lt_or_ge j
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).length with
    | Or.inr hge =>
      rw [ground.getAt_over vacProf _ j hge]
      exact Nat.zero_le _
    | Or.inl hjlt =>
      exact poly.capOfLen (depthPoly_ble
        (show profShape (ground.getAt vacProf
          (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j) K from
          ground.all_getAt vacProf _ hrow j hjlt) m)
/-! `lem:cornerblock`'s center family at the canonical carrier:
the block chain's center is one matrix in the scale and the depth's
pair reads, so its operations are the carrier-generic fold layer's
(`elim.matMulO`, `elim.matAddO`, `elim.matSwapO`, `elim.transposeO`)
at the profile entry bundle, and the family's per-depth read
collapses entrywise to the balance-pair polynomial matrices, where
the same fold layer runs at the polynomial entries. -/

/-- The canonical carrier's entry bundle: the profile sum and the
kernel-reduced product, the vacant slabs the sum's unit and the
constant profile the product's, and the profile's memberwise swap
the balance partner. -/
def profOps : ground.DOps (poly.PPoly × poly.PPoly) :=
  ⟨⟨profAdd, profMul, vacProf, constProf (BPair.ofPos .one)⟩, profNeg⟩

/-- The center families' product, the row-against-column folds at the
canonical carrier. -/
def pfmMul (A B : List (List (poly.PPoly × poly.PPoly))) :
    List (List (poly.PPoly × poly.PPoly)) :=
  elim.matMulO profOps A B

/-- The center families' entrywise sum over shared key lists. -/
def pfmAdd (A B : List (List (poly.PPoly × poly.PPoly))) :
    List (List (poly.PPoly × poly.PPoly)) :=
  elim.matAddO profOps A B

/-- The center family's memberwise swap, entrywise. -/
def pfmSwap (A : List (List (poly.PPoly × poly.PPoly))) :
    List (List (poly.PPoly × poly.PPoly)) :=
  elim.matSwapO profOps A

/-- The exchange of the center family's row and column key lists. -/
def pfmTr (A : List (List (poly.PPoly × poly.PPoly))) :
    List (List (poly.PPoly × poly.PPoly)) :=
  elim.transposeO profOps A

/-- The center family's depth shift, entrywise at the profile's own
shift. -/
def pfmShift (A : List (List (poly.PPoly × poly.PPoly))) :
    List (List (poly.PPoly × poly.PPoly)) :=
  A.map (fun r => r.map profShift)

/-- The center family's per-depth read: the entries' collapses at the
depth's pair reads, one polynomial matrix in the scale per depth. -/
def pfmDepth (m : Nat) (A : List (List (poly.PPoly × poly.PPoly))) :
    split.PMat :=
  A.map (fun r => r.map (fun e => depthPoly e m))

/-- The constant family at a stated matrix: each entry the matrix's
own coefficient at the constant profile. -/
def ofMatProf (X : elim.Mat) : List (List (poly.PPoly × poly.PPoly)) :=
  X.map (fun r => r.map constProf)
/-! The center family's collapse bridges: every matrix operation of
the canonical carrier reads the balance-pair polynomial matrices'
own at each depth, the entrywise collapse bridges lifted through the
fold layer's folds. -/

/-- A row's key read collapses to the collapsed row's own, a key
beyond the row reading the vacant slabs' profile against the vacant
polynomial. -/
private theorem depthGetAt (m : Nat) :
    ∀ (r : List (poly.PPoly × poly.PPoly)) (k : Nat),
      poly.oneValue (depthPoly (ground.getAt profOps.unit r k) m)
        (ground.getAt ([] : poly.Poly)
          (r.map (fun e => depthPoly e m)) k)
  | [], _ => poly.oneValue_refl _
  | _ :: _, 0 => poly.oneValue_refl _
  | _ :: t, k + 1 => depthGetAt m t k

/-- The collapsed family's row at a key is the family's own row
collapsed, a key beyond the family reading the vacant row. -/
private theorem depthRow (m : Nat) :
    ∀ (M : List (List (poly.PPoly × poly.PPoly))) (k : Nat),
      ground.getAt ([] : List poly.Poly) (pfmDepth m M) k
        = (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) M k).map
            (fun e => depthPoly e m) :=
  ground.getAt_mapT ([] : List (poly.PPoly × poly.PPoly))
    ([] : List poly.Poly) (fun r => r.map (fun e => depthPoly e m))
    rfl

/-- An entry's collapse at two keys, the row read chained onto the
key read. -/
private theorem depthGetAt2 (m : Nat)
    (M : List (List (poly.PPoly × poly.PPoly))) (k j : Nat) :
    poly.oneValue
      (depthPoly (ground.getAt profOps.unit
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) M k) j) m)
      (ground.getAt ([] : poly.Poly)
        (ground.getAt ([] : List poly.Poly) (pfmDepth m M) k) j) := by
  rw [depthRow m M k]
  exact depthGetAt m (ground.getAt [] M k) j

/-- The collapsed family's leading row carries the family's own
width. -/
private theorem headD_pfmDepth (m : Nat) :
    ∀ M : List (List (poly.PPoly × poly.PPoly)),
      ((pfmDepth m M).headD ([] : List poly.Poly)).length
        = (M.headD ([] : List (poly.PPoly × poly.PPoly))).length
  | [] => rfl
  | r :: _ => ground.length_map _ r

/-- One row of the sum's collapse, the entrywise bridge over the
shared key lists. -/
private theorem depthAddRow (m : Nat) :
    ∀ r s : List (poly.PPoly × poly.PPoly),
      ground.matchedOV poly.polyRead
        ((List.zipWith profAdd r s).map (fun e => depthPoly e m))
        (List.zipWith poly.add (r.map (fun e => depthPoly e m))
          (s.map (fun e => depthPoly e m)))
  | [], [] => trivial
  | [], _ :: _ => trivial
  | _ :: _, [] => trivial
  | a :: r, b :: s => ⟨depthPoly_profAdd a b m, depthAddRow m r s⟩

/-- The sum's collapse, the rows' bridges over the shared key
lists. -/
private theorem depthAddM (m : Nat) :
    ∀ A B : List (List (poly.PPoly × poly.PPoly)),
      split.pmatOneValue (pfmDepth m (pfmAdd A B))
        (split.pmatAdd (pfmDepth m A) (pfmDepth m B))
  | [], [] => trivial
  | [], _ :: _ => trivial
  | _ :: _, [] => trivial
  | a :: A, b :: B => ⟨depthAddRow m a b, depthAddM m A B⟩

/-- One row of the memberwise swap's collapse. -/
private theorem depthSwapRow (m : Nat) :
    ∀ r : List (poly.PPoly × poly.PPoly),
      ground.matchedOV poly.polyRead
        ((r.map profNeg).map (fun e => depthPoly e m))
        ((r.map (fun e => depthPoly e m)).map poly.neg)
  | [] => trivial
  | a :: r => ⟨depthPoly_profNeg a m, depthSwapRow m r⟩

/-- The memberwise swap's collapse, the rows' bridges. -/
private theorem depthSwapM (m : Nat) :
    ∀ A : List (List (poly.PPoly × poly.PPoly)),
      split.pmatOneValue (pfmDepth m (pfmSwap A))
        (split.pswapM (pfmDepth m A))
  | [] => trivial
  | r :: A => ⟨depthSwapRow m r, depthSwapM m A⟩

/-- One row of the depth shift's collapse, the successor depth's own
read. -/
private theorem depthShiftRow (m : Nat) :
    ∀ r : List (poly.PPoly × poly.PPoly),
      ground.matchedOV poly.polyRead
        ((r.map profShift).map (fun e => depthPoly e m))
        (r.map (fun e => depthPoly e (m + 1)))
  | [] => trivial
  | a :: r => ⟨depthPoly_profShift a m, depthShiftRow m r⟩

/-- The depth shift's collapse, the rows' bridges. -/
private theorem depthShiftM (m : Nat) :
    ∀ A : List (List (poly.PPoly × poly.PPoly)),
      split.pmatOneValue (pfmDepth m (pfmShift A)) (pfmDepth (m + 1) A)
  | [] => trivial
  | r :: A => ⟨depthShiftRow m r, depthShiftM m A⟩

/-- The constant entry's collapse: the vacant slabs' origin reads the
stated coefficient at every depth. -/
private theorem depthConst (c : BPair) (m : Nat) :
    poly.oneValue (depthPoly (constProf c) m)
      ([c] : poly.Poly) := poly.scaleP_one [c]

/-- One row of the constant family's collapse. -/
private theorem depthOfMatRow (m : Nat) :
    ∀ r : List BPair,
      ground.matchedOV poly.polyRead
        ((r.map constProf).map
          (fun e => depthPoly e m))
        (r.map (fun c => ([c] : poly.Poly)))
  | [] => trivial
  | c :: r => ⟨depthConst c m, depthOfMatRow m r⟩

/-- The constant family's collapse, the rows' bridges. -/
private theorem depthOfMatM (m : Nat) :
    ∀ X : elim.Mat,
      split.pmatOneValue (pfmDepth m (ofMatProf X))
        (elim.embedP X)
  | [] => trivial
  | r :: X => ⟨depthOfMatRow m r, depthOfMatM m X⟩

/-- The leading column's collapse: the family's head reads are the
collapsed family's own. -/
private theorem depthColHead (m : Nat) :
    ∀ M : List (List (poly.PPoly × poly.PPoly)),
      ground.matchedOV poly.polyRead
        ((elim.colHead profOps.unit M).map (fun e => depthPoly e m))
        (elim.colHead ([] : poly.Poly) (pfmDepth m M))
  | [] => trivial
  | r :: M => ⟨depthGetAt m r 0, depthColHead m M⟩

/-- The withdrawn leading column commutes with the per-depth read. -/
private theorem depthDropCol (m : Nat)
    (M : List (List (poly.PPoly × poly.PPoly))) :
    elim.dropCol (pfmDepth m M) = pfmDepth m (elim.dropCol M) := by
  show (M.map (fun r => r.map (fun e => depthPoly e m))).map
      (fun r => r.drop 1)
    = (M.map (fun r => r.drop 1)).map
        (fun r => r.map (fun e => depthPoly e m))
  rw [ground.map_map, ground.map_map]
  exact ground.map_congr_all _ _
    (fun r => ground.map_drop (fun e => depthPoly e m) r 1) M

/-- The key exchange's collapse at an occupied family, the walk down
the leading columns: the head column's collapse beside the withdrawn
family's own, the recursion the head row's. -/
private theorem depthTrGo (m : Nat) :
    ∀ (r : List (poly.PPoly × poly.PPoly))
      (t : List (List (poly.PPoly × poly.PPoly))) (u : split.PMat),
      u = pfmDepth m t →
      split.pmatOneValue
        ((elim.transposeO profOps (r :: t)).map
          (fun row => row.map (fun e => depthPoly e m)))
        (elim.transposeO poly.polyOps
          ((r.map (fun e => depthPoly e m)) :: u))
  | [], _, _, _ => trivial
  | a :: r, t, u, h => by
    subst h
    exact ⟨depthColHead m ((a :: r) :: t),
      depthTrGo m r (elim.dropCol t) (elim.dropCol (pfmDepth m t))
        (depthDropCol m t)⟩

/-- The accumulating fold's collapse: a fold of profile summands
reads the polynomial fold at every seed pair the collapse relates,
one sum bridge per step. -/
private theorem depthFold (m : Nat) (f : Nat → poly.PPoly × poly.PPoly)
    (g : Nat → poly.Poly)
    (hfg : ∀ k, poly.oneValue (depthPoly (f k) m) (g k)) :
    ∀ (l : List Nat) (a : poly.PPoly × poly.PPoly) (b : poly.Poly),
      poly.oneValue (depthPoly a m) b →
      poly.oneValue
        (depthPoly (l.foldl (fun acc k => profAdd acc (f k)) a) m)
        (l.foldl (fun acc k => poly.add acc (g k)) b)
  | [], _, _, h => h
  | k :: l, a, b, h =>
    depthFold m f g hfg l (profAdd a (f k)) (poly.add b (g k))
      (poly.oneValue_trans (depthPoly_profAdd a (f k) m)
        (poly.add_congr h (hfg k)))

/-- The product's entry collapse: the row-against-column fold at the
canonical carrier reads the polynomial fold, each summand's product
bridge at the two entries' own key reads. -/
private theorem depthMulEntry (m : Nat)
    (B : List (List (poly.PPoly × poly.PPoly)))
    (r : List (poly.PPoly × poly.PPoly)) (j : Nat) :
    poly.oneValue
      (depthPoly ((List.range r.length).foldl (fun acc k =>
        profAdd acc (profMul (ground.getAt profOps.unit r k)
          (ground.getAt profOps.unit
            (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) B k) j)))
        profOps.unit) m)
      ((List.range r.length).foldl (fun acc k =>
        poly.add acc (poly.mul
          (ground.getAt ([] : poly.Poly)
            (r.map (fun e => depthPoly e m)) k)
          (ground.getAt ([] : poly.Poly)
            (ground.getAt ([] : List poly.Poly) (pfmDepth m B) k) j)))
        ([] : poly.Poly)) :=
  depthFold m
    (fun k => profMul (ground.getAt profOps.unit r k)
      (ground.getAt profOps.unit
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) B k) j))
    (fun k => poly.mul
      (ground.getAt ([] : poly.Poly) (r.map (fun e => depthPoly e m)) k)
      (ground.getAt ([] : poly.Poly)
        (ground.getAt ([] : List poly.Poly) (pfmDepth m B) k) j))
    (fun k => poly.oneValue_trans (depthPoly_profMul _ _ m)
      (poly.oneValue_trans
        (poly.mul_congr_left (depthGetAt m r k) _)
        (poly.mul_congr _ (depthGetAt2 m B k j))))
    (List.range r.length) profOps.unit ([] : poly.Poly)
    (poly.oneValue_refl _)

/-- One row of the product's collapse: the second factor's head width
is the collapsed factor's own, and the row's entries collapse at
every column key. -/
private theorem depthMulRow (m : Nat)
    (B : List (List (poly.PPoly × poly.PPoly)))
    (r : List (poly.PPoly × poly.PPoly)) :
    ground.matchedOV poly.polyRead
      (((List.range
          (B.headD ([] : List (poly.PPoly × poly.PPoly))).length).map
        (fun j => (List.range r.length).foldl (fun acc k =>
          profAdd acc (profMul (ground.getAt profOps.unit r k)
            (ground.getAt profOps.unit
              (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) B k) j)))
          profOps.unit)).map (fun e => depthPoly e m))
      ((List.range ((pfmDepth m B).headD ([] : List poly.Poly)).length).map
        (fun j => (List.range (r.map (fun e => depthPoly e m)).length).foldl
          (fun acc k => poly.add acc (poly.mul
            (ground.getAt ([] : poly.Poly)
              (r.map (fun e => depthPoly e m)) k)
            (ground.getAt ([] : poly.Poly)
              (ground.getAt ([] : List poly.Poly) (pfmDepth m B) k) j)))
          ([] : poly.Poly))) := by
  rw [headD_pfmDepth m B, ground.length_map, ground.map_map]
  exact ground.matched_map _ _ (fun j => depthMulEntry m B r j)
    (List.range (B.headD ([] : List (poly.PPoly × poly.PPoly))).length)

/-- The product's collapse, the rows' bridges at the shared second
factor. -/
private theorem depthMulM (m : Nat)
    (B : List (List (poly.PPoly × poly.PPoly))) :
    ∀ A : List (List (poly.PPoly × poly.PPoly)),
      split.pmatOneValue (pfmDepth m (pfmMul A B))
        (split.pmatMul (pfmDepth m A) (pfmDepth m B))
  | [] => trivial
  | r :: A => ⟨depthMulRow m B r, depthMulM m B A⟩

/-- The product's per-depth read is the collapsed factors' polynomial
product. -/
theorem pfmDepth_mul (A B : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) :
    split.pmatOneValue (pfmDepth m (pfmMul A B))
      (split.pmatMul (pfmDepth m A) (pfmDepth m B)) :=
  depthMulM m B A

/-- The sum's per-depth read is the collapsed summands' polynomial
sum. -/
theorem pfmDepth_add (A B : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) :
    split.pmatOneValue (pfmDepth m (pfmAdd A B))
      (split.pmatAdd (pfmDepth m A) (pfmDepth m B)) :=
  depthAddM m A B

/-- The memberwise swap's per-depth read is the collapsed family's
own swap. -/
theorem pfmDepth_swap (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) :
    split.pmatOneValue (pfmDepth m (pfmSwap A))
      (split.pswapM (pfmDepth m A)) :=
  depthSwapM m A

/-- The depth shift's read at a depth is the family's read at the
successor depth. -/
theorem pfmDepth_shift (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) :
    split.pmatOneValue (pfmDepth m (pfmShift A)) (pfmDepth (m + 1) A) :=
  depthShiftM m A

/-- The key exchange's per-depth read is the collapsed family's own
exchange. -/
theorem pfmDepth_tr (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) :
    split.pmatOneValue (pfmDepth m (pfmTr A))
      (elim.transposeO poly.polyOps (pfmDepth m A)) := by
  cases A with
  | nil => trivial
  | cons r t => exact depthTrGo m r t (pfmDepth m t) rfl

/-- The constant family's per-depth read is the stated matrix's own
entries, at every depth. -/
theorem pfmDepth_ofMat (X : elim.Mat) (m : Nat) :
    split.pmatOneValue (pfmDepth m (ofMatProf X))
      (elim.embedP X) :=
  depthOfMatM m X
/-! `lem:cornerblock`'s dominance tier at the canonical
carrier: the family rescaled at a stated profile, the carrier's own
one-value reads, the cleared family — the matrix with its clearing,
the centers' determinants the clearings' reads — and the dominance
comparison's certificate walk at the four counts' site data, one
walk per row with the stated caps' box reads. -/

/-- The center family rescaled at a stated profile, entrywise at the
canonical carrier's reduced product. -/
def pfmScale (f : poly.PPoly × poly.PPoly)
    (A : List (List (poly.PPoly × poly.PPoly))) :
    List (List (poly.PPoly × poly.PPoly)) :=
  A.map (fun r => r.map (profMul f))

/-- The profile carrier's one-value read, slabwise at the iterated
carrier's own. -/
def profOneValue (V W : poly.PPoly × poly.PPoly) : Prop :=
  poly.ppOneValue V.1 W.1 ∧ poly.ppOneValue V.2 W.2

instance instCornerblock5 (V W : poly.PPoly × poly.PPoly) :
    Decidable (profOneValue V W) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The profile read's decision as a bare family, the read datum's
own field. -/
def decProfOneValue : ∀ a b, Decidable (profOneValue a b) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The profile carrier's read datum: the one-value read with its
decision. -/
def profDRead : ground.DRead (poly.PPoly × poly.PPoly) :=
  ⟨profOneValue, decProfOneValue⟩

/-- The per-depth collapse is one value across the profile's
representatives, slab by slab. -/
private theorem depthPoly_congr (V W : poly.PPoly × poly.PPoly) (m : Nat)
    (h : profOneValue V W) :
    poly.oneValue (depthPoly V m) (depthPoly W m) :=
  poly.add_congr (slabGo_congr (m * m) 0 1 V.1 W.1 h.1)
    (slabGo_congr (m * m) 1 m V.2 W.2 h.2)

/-- The canonical representative's collapse is the profile's own at
every depth (`def:ground`'s homogeneity principle at the profile
carrier). -/
theorem depthPoly_profReduce (V : poly.PPoly × poly.PPoly) (m : Nat) :
    poly.oneValue (depthPoly (profReduce V) m) (depthPoly V m) :=
  depthPoly_congr (profReduce V) V m
    ⟨slabReduce_ov V.1, slabReduce_ov V.2⟩

/-- The center families' entrywise read at stated shapes: the key
lists matched and the entries read at the profile carrier's own. -/
def pfmOneValue :
    List (List (poly.PPoly × poly.PPoly)) →
    List (List (poly.PPoly × poly.PPoly)) → Prop :=
  ground.matchedOV (ground.matchedRead profDRead)

instance instCornerblock6 (A B : List (List (poly.PPoly × poly.PPoly))) :
    Decidable (pfmOneValue A B) :=
  ground.decMatchedOV (ground.matchedRead profDRead) A B

/-! The cleared family: the matrix with its clearing, the centers'
determinants the clearings' reads — the four carrier operations at
the pair, and the cross-multiplied read. -/

/-- The cleared family: a center family with its clearing profile. -/
abbrev PfMQ :=
  List (List (poly.PPoly × poly.PPoly)) × (poly.PPoly × poly.PPoly)

/-- A family at the unit clearing. -/
def ofPfm (A : List (List (poly.PPoly × poly.PPoly))) : PfMQ :=
  (A, constProf (BPair.ofPos .one))

/-- The cleared families' product: the matrices' own at the
clearings' product. -/
def pfmQmul (a b : PfMQ) : PfMQ := (pfmMul a.1 b.1, profMul a.2 b.2)

/-- The cleared families' sum: each matrix against the other's
clearing, over the clearings' product. -/
def pfmQadd (a b : PfMQ) : PfMQ :=
  (pfmAdd (pfmScale b.2 a.1) (pfmScale a.2 b.1), profMul a.2 b.2)

/-- The cleared family's memberwise swap, the matrix's own — the
clearing positive throughout. -/
def pfmQswap (a : PfMQ) : PfMQ := (pfmSwap a.1, a.2)

/-- The families' entrywise canonical representative, the profile's
own at every entry. -/
def pfmReduce (A : List (List (poly.PPoly × poly.PPoly))) :
    List (List (poly.PPoly × poly.PPoly)) :=
  A.map (fun r => r.map profReduce)

/-- The cleared family's depth shift at the canonical
representative: the matrix's and the clearing's own shifts, every
entry reduced — the shift's compounded representative withdrawn to
the canonical size, a constant clearing shifting to itself. -/
def pfmQshift (a : PfMQ) : PfMQ :=
  (pfmReduce (pfmShift a.1), profReduce (profShift a.2))

/-- The cleared families' one-value read, cross-multiplied: each
matrix against the other's clearing — the read blind to a shared
clearing. -/
def pfmQOneValue (a b : PfMQ) : Prop :=
  pfmOneValue (pfmScale b.2 a.1) (pfmScale a.2 b.1)

instance instCornerblock7 (a b : PfMQ) : Decidable (pfmQOneValue a b) :=
  inferInstanceAs (Decidable (pfmOneValue _ _))

/-! The dominance comparison's certificate walk at the profile
carrier (`thm:decimation`(ii)): each count's site datum read row by
row, one box read per row at the diagonal's entry less the off-row
magnitude fold, the magnitudes the coefficients' own
(`thm:windowsep`). -/

/-- The entrywise magnitude profile: each coefficient at the
magnitude carrier (`thm:windowsep`), both slabs — its collapse
prices the collapse's coefficient magnitudes, the depth walk's
weights natural. -/
def magProf (V : poly.PPoly × poly.PPoly) :
    poly.PPoly × poly.PPoly :=
  (V.1.map (fun p => p.map windowsep.mag),
   V.2.map (fun p => p.map windowsep.mag))

/-- The off-row magnitude fold: the row's entrywise magnitude
profiles summed at the stated key withdrawn, the walk counting the
key down (`thm:decimation`(ii)'s fold at the profile carrier,
`ground.offFoldO` at the profile bundle). -/
def offMagFold : Nat → List (poly.PPoly × poly.PPoly) →
    poly.PPoly × poly.PPoly :=
  ground.offFoldO profOps magProf

/-- One row's dominance read: the diagonal's entry less the off-row
magnitude fold at its own box read. -/
def domRowRead (e0n : BPair) (e0d : Pos) (i : Nat)
    (srow : List (poly.PPoly × poly.PPoly)) (gap : BoxCert) : Prop :=
  boxRead (profAdd (ground.getAt vacProf srow i)
      (profNeg (offMagFold i srow))) e0n e0d gap

instance instCornerblock8 (e0n : BPair) (e0d : Pos) (i : Nat)
    (srow : List (poly.PPoly × poly.PPoly)) (gap : BoxCert) :
    Decidable (domRowRead e0n e0d i srow gap) :=
  inferInstanceAs (Decidable (boxRead _ _ _ _))

/-- The dominance comparison's certificate walk over a site datum:
one box read per row at the diagonal's entry less the off-row
magnitude fold, the row key its own diagonal slot — the site datum
diagonally dominant on the box, so `thm:decimation`(ii)'s
comparison reads the count at the profile carrier. -/
def domCertGo (e0n : BPair) (e0d : Pos) :
    Nat → List (List (poly.PPoly × poly.PPoly)) →
    List BoxCert → Prop
  | _, [], [] => True
  | _, [], _ :: _ => False
  | _, _ :: _, [] => False
  | i, sr :: srs, g :: gs =>
      domRowRead e0n e0d i sr g ∧ domCertGo e0n e0d (i + 1) srs gs

/-- The dominance walk's decision, the rows' own joined at the
recursion. -/
def decDomCertGo (e0n : BPair) (e0d : Pos) :
    ∀ (i : Nat) (S : List (List (poly.PPoly × poly.PPoly)))
      (gs : List BoxCert),
    Decidable (domCertGo e0n e0d i S gs)
  | _, [], [] => isTrue trivial
  | _, [], _ :: _ => isFalse (fun h => h)
  | _, _ :: _, [] => isFalse (fun h => h)
  | i, _ :: srs, _ :: gs =>
      @instDecidableAnd _ _ inferInstance
        (decDomCertGo e0n e0d (i + 1) srs gs)

instance instCornerblock9 (e0n : BPair) (e0d : Pos) (i : Nat)
    (S : List (List (poly.PPoly × poly.PPoly)))
    (gs : List BoxCert) :
    Decidable (domCertGo e0n e0d i S gs) :=
  decDomCertGo e0n e0d i S gs

/-! The four counts' site data at the profile carrier: the
contraction's, the floor's and the two cap arms', each the stated
read's own scale spelling with the cleared family's clearing
carried. -/

/-- The contraction certificate's site datum at the profile carrier
(`spectator.contractRead`'s scale spelling at `lem:spectator`(iii)'s
bulk data, the one repeating gram): the transfer factor's image
form cleared at the denominator's square withdrawn from the gram's
multiple at the numerator's square and the factor's own clearing
squared. -/
def contrSiteF (Wf : PfMQ) (G : elim.Mat) (ln ld : Pos) :
    List (List (poly.PPoly × poly.PPoly)) :=
  pfmAdd
    (pfmScale (profMul (profMul Wf.2 Wf.2)
      (constProf (BPair.ofPos (ln * ln)))) (ofMatProf G))
    (pfmSwap (pfmScale (constProf (BPair.ofPos (ld * ld)))
      (pfmMul (pfmTr (pfmSwap Wf.1))
        (pfmMul (ofMatProf G) (pfmSwap Wf.1)))))

/-- The center's floor site datum at the profile carrier
(`spectator.floorRead`'s scale spelling): the center cleared at the
floor and radius denominators' product, less the gram's multiple at
the center's clearing and the two pairs' cross-added numerator. -/
def floorSiteF (Cf : PfMQ) (G : elim.Mat) (y0n y0d rn rd : Pos) :
    List (List (poly.PPoly × poly.PPoly)) :=
  pfmAdd (pfmScale (constProf (BPair.ofPos (y0d * rd))) Cf.1)
    (pfmSwap (pfmScale
      (profMul Cf.2 (constProf (BPair.ofPos (y0n * rd + rn * y0d))))
      (ofMatProf G)))

/-- The center defect at the profile carrier: the image family less
the center, the deviation's cleared datum (`spectator.devQ`) at the
center's own clearing — the deeper center's transfer image against
the slab's own center, the centers' consecutive drift the defect's
own summand (`lem:cornerblock`). -/
def devFam (Cf If : PfMQ) : PfMQ := pfmQadd If (pfmQswap Cf)

/-- The defect cap's upper site datum at the profile carrier
(`spectator.capQ`'s scale spelling): the gram's multiple at the cap
numerator and the defect's clearing, less the defect cleared at the
cap denominator. -/
def dcapHiSiteF (Cf If : PfMQ) (G : elim.Mat) (r0n r0d : Pos) :
    List (List (poly.PPoly × poly.PPoly)) :=
  pfmAdd
    (pfmScale (profMul (devFam Cf If).2 (constProf (BPair.ofPos r0n)))
      (ofMatProf G))
    (pfmSwap (pfmScale (constProf (BPair.ofPos r0d)) (devFam Cf If).1))

/-- The defect cap's lower site datum at the profile carrier, the
upper's memberwise swap on the defect: the gram's multiple joined to
the defect cleared at the cap denominator. -/
def dcapLoSiteF (Cf If : PfMQ) (G : elim.Mat) (r0n r0d : Pos) :
    List (List (poly.PPoly × poly.PPoly)) :=
  pfmAdd
    (pfmScale (profMul (devFam Cf If).2 (constProf (BPair.ofPos r0n)))
      (ofMatProf G))
    (pfmScale (constProf (BPair.ofPos r0d)) (devFam Cf If).1)

/-- One row of the rescaling's collapse, the entrywise product
bridge at the shared left factor. -/
private theorem depthScaleRow (f : poly.PPoly × poly.PPoly) (m : Nat) :
    ∀ r : List (poly.PPoly × poly.PPoly),
      ground.matchedOV poly.polyRead
        ((r.map (profMul f)).map (fun e => depthPoly e m))
        ((r.map (fun e => depthPoly e m)).map
          (poly.mul (depthPoly f m)))
  | [] => trivial
  | a :: r => ⟨depthPoly_profMul f a m, depthScaleRow f m r⟩

/-- The rescaling's collapse, the rows' bridges. -/
private theorem depthScaleM (f : poly.PPoly × poly.PPoly) (m : Nat) :
    ∀ A : List (List (poly.PPoly × poly.PPoly)),
      split.pmatOneValue (pfmDepth m (pfmScale f A))
        (split.pscaleM (depthPoly f m) (pfmDepth m A))
  | [] => trivial
  | r :: A => ⟨depthScaleRow f m r, depthScaleM f m A⟩

/-- The rescaling's per-depth read is the collapsed family rescaled
at the stated profile's own collapse. -/
theorem pfmDepth_scale (f : poly.PPoly × poly.PPoly)
    (A : List (List (poly.PPoly × poly.PPoly))) (m : Nat) :
    split.pmatOneValue (pfmDepth m (pfmScale f A))
      (split.pscaleM (depthPoly f m) (pfmDepth m A)) :=
  depthScaleM f m A

/-! `lem:cornerblock`'s evaluated glue: the dominance walk's row
certificates, read at one shared clearing power, make the evaluated
site matrix diagonally dominant at every depth of the box, so
`thm:decimation`(ii) prices its form. -/

/-- The profile's evaluated collapse at a depth and a composite
point, cleared at the stated power — the evaluated site datum's
entry, `lem:cellcount`'s cleared evaluation at the depth's own
collapse. -/
def evalProf (V : poly.PPoly × poly.PPoly) (m : Nat) (en : Pos)
    (ed : Pos) (K : Nat) : BPair :=
  poly.evalClear (depthPoly V m) (BPair.ofPos en) ed K

/-- The slab walk carries domination: its weights are natural, its
shifts and sums the domination laws' own. -/
private theorem slabGo_magDom (mm : Nat) :
    ∀ (b w : Nat) (P : poly.PPoly),
      windowsep.magDom (slabGo mm b w P)
        (slabGo mm b w (P.map (fun p => p.map windowsep.mag)))
  | _, _, [] =>
    windowsep.magDom_of (fun _ => by
      show windowsep.mag BPair.unit ≤ BPair.unit
      rw [windowsep.mag_unitLe (ground.leB_refl BPair.unit)]
      exact ground.leB_refl _)
  | b, w, p :: t =>
    windowsep.magDom_add
      (windowsep.magDom_shiftUp b
        (windowsep.magDom_scaleP (windowsep.mag_unitLe (ground.unitLeOfNat w))
          (windowsep.magDom_map p)))
      (slabGo_magDom mm (b + 1) (w * mm) t)

/-- The entrywise magnitude profile's collapse dominates the
profile's own, key by key at every depth. -/
private theorem depthPoly_magDom (V : poly.PPoly × poly.PPoly) (m : Nat) :
    windowsep.magDom (depthPoly V m) (depthPoly (magProf V) m) :=
  windowsep.magDom_add (slabGo_magDom (m * m) 0 1 V.1)
    (slabGo_magDom (m * m) 1 m V.2)

/-- The evaluated collapse's magnitude sits at or below the
entrywise magnitude profile's own evaluation: the slab walk's
weights are natural, so the depth's collapse is dominated key by
key and the positive point prices the two folds
(`thm:windowsep`'s sum and product laws). -/
theorem evalProf_mag (V : poly.PPoly × poly.PPoly) (m : Nat)
    (en ed : Pos) (K : Nat) :
    windowsep.mag (evalProf V m en ed K)
      ≤ evalProf (magProf V) m en ed K :=
  windowsep.evalClear_magDom (BPair.ofPos en)
    (ground.leB_of_lt (ground.unitLtOfPos en)) ed K (depthPoly_magDom V m)

/-- The profile sum's evaluated collapse is the summands' own, the
one clearing power shared. -/
private theorem evalProf_profAdd (V W : poly.PPoly × poly.PPoly)
    (m : Nat) (en ed : Pos) (K : Nat) :
    (evalProf (profAdd V W) m en ed K).oneValue
      (evalProf V m en ed K + evalProf W m en ed K) :=
  BPair.oneValue_trans
    (poly.evalClear_congr (depthPoly_profAdd V W m) (BPair.ofPos en) ed K)
    (poly.evalClear_add _ _ _ _ _)

/-- The swapped profile's evaluated collapse is the collapse's
balance partner. -/
private theorem evalProf_profNeg (V : poly.PPoly × poly.PPoly)
    (m : Nat) (en ed : Pos) (K : Nat) :
    (evalProf (profNeg V) m en ed K).oneValue
      (evalProf V m en ed K).swap :=
  BPair.oneValue_trans
    (poly.evalClear_congr (depthPoly_profNeg V m) (BPair.ofPos en) ed K)
    (poly.evalClear_neg _ _ _ _)

/-- The magnitude profiles' fold at a row reads its evaluated
collapse as the entries' evaluated magnitude profiles' fold. -/
private theorem magSumProf_eval (m : Nat) (en ed : Pos) (K : Nat) :
    ∀ l : List (poly.PPoly × poly.PPoly),
      (evalProf (ground.famFold profAdd vacProf magProf l) m en ed K).oneValue
        (ground.famFold BPair.add BPair.unit
          (fun e => evalProf (magProf e) m en ed K) l)
  | [] => BPair.oneValue_refl _
  | c :: t =>
    BPair.oneValue_trans
      (evalProf_profAdd (magProf c) (ground.famFold profAdd vacProf magProf t)
        m en ed K)
      (BPair.add_congr (BPair.oneValue_refl _)
        (magSumProf_eval m en ed K t))

/-- The vacant profile's evaluated collapse is the sum's unit, both
slabs' walks vacant. -/
private theorem evalProf_vac (m : Nat) (en ed : Pos) (K : Nat) :
    evalProf vacProf m en ed K = BPair.unit := rfl

/-- The off-row magnitude fold's evaluated collapse prices the
evaluated row's own off-key fold: the walk's two arms are the sum
law and the entrywise magnitude price. -/
private theorem offMagFold_le (m : Nat) (en ed : Pos) (K : Nat) :
    ∀ (i : Nat) (l : List (poly.PPoly × poly.PPoly)),
      decimation.offFold i (l.map (fun e => evalProf e m en ed K))
        ≤ evalProf (offMagFold i l) m en ed K
  | 0, [] => by
    show BPair.unit ≤ evalProf vacProf m en ed K
    rw [evalProf_vac m en ed K]
    exact ground.leB_refl _
  | _ + 1, [] => by
    show BPair.unit ≤ evalProf vacProf m en ed K
    rw [evalProf_vac m en ed K]
    exact ground.leB_refl _
  | 0, _ :: t => by
    show decimation.magSum (t.map (fun e => evalProf e m en ed K))
      ≤ evalProf (ground.famFold profAdd vacProf magProf t) m en ed K
    refine ground.leB_congr_right
      (BPair.oneValue_symm (magSumProf_eval m en ed K t)) ?_
    show ground.famFold BPair.add BPair.unit windowsep.mag
        (t.map (fun e => evalProf e m en ed K))
      ≤ ground.famFold BPair.add BPair.unit
        (fun e => evalProf (magProf e) m en ed K) t
    rw [ground.famFold_map BPair.add BPair.unit windowsep.mag
      (fun e => evalProf e m en ed K) t]
    exact ground.bsum_le_of_mem _ _ t
      (fun e _ => evalProf_mag e m en ed K)
  | i + 1, x :: t => by
    show windowsep.mag (evalProf x m en ed K)
        + decimation.offFold i (t.map (fun e => evalProf e m en ed K))
      ≤ evalProf (profAdd (magProf x) (offMagFold i t)) m en ed K
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (evalProf_profAdd (magProf x) (offMagFold i t) m en ed K)) ?_
    exact ground.leB_add (evalProf_mag x m en ed K)
      (offMagFold_le m en ed K i t)

/-- The evaluated row's key read is the row entry's own evaluated
collapse, the vacant profile's collapse the sum's unit past the
row's length. -/
private theorem getAt_evalRow (m : Nat) (en ed : Pos) (K : Nat)
    (srow : List (poly.PPoly × poly.PPoly)) (i : Nat) :
    ground.getAt BPair.unit (srow.map (fun e => evalProf e m en ed K)) i
      = evalProf (ground.getAt vacProf srow i) m en ed K :=
  ground.getAt_mapT vacProf BPair.unit
    (fun e => evalProf e m en ed K) rfl srow i

/-! `lem:cornerblock`'s bridge tier: the canonical carrier's
operations pass the evaluated collapse — the profile reads at their
one-value classes, the canonical representative, the depth shift, the
product at split clearing powers, and the matrix carrier's sum,
memberwise swap, product, key exchange, rescaling and constant family
at the evaluated site datum. -/

/-- The constant profile's collapse is one key long at every depth. -/
private theorem depthConst_len (c : BPair) (m : Nat) :
    (depthPoly (constProf c) m).length = 1 := rfl

/-- The constant profile's evaluated collapse is its coefficient
against the whole clearing power, at every depth. -/
private theorem evalProf_const (c : BPair) (m : Nat) (en ed : Pos) (K : Nat) :
    (evalProf (constProf c) m en ed K).oneValue
      (c * ground.bpow (BPair.ofPos ed) K) :=
  BPair.oneValue_trans
    (poly.evalClear_congr (depthConst c m) (BPair.ofPos en) ed K)
    (poly.evalClear_single c (BPair.ofPos en) ed K)

/-- A pair against the clearing's vacant power is the pair itself. -/
private theorem mulBpowZero (ed : Pos) (z : BPair) :
    (z * ground.bpow (BPair.ofPos ed) 0).oneValue z :=
  BPair.oneValue_trans (BPair.mul_ofPos z Pos.one)
    (BPair.oneValue_of_eq (BPair.scale_one z))

/-- The depth shift's evaluated collapse is the collapse at the
successor depth. -/
private theorem evalProf_profShift (V : poly.PPoly × poly.PPoly) (m : Nat)
    (en ed : Pos) (K : Nat) :
    (evalProf (profShift V) m en ed K).oneValue
      (evalProf V (m + 1) en ed K) :=
  poly.evalClear_congr (depthPoly_profShift V m) (BPair.ofPos en) ed K

/-- The canonical representative's evaluated collapse is the
profile's own. -/
private theorem evalProf_profReduce (V : poly.PPoly × poly.PPoly) (m : Nat)
    (en ed : Pos) (K : Nat) :
    (evalProf (profReduce V) m en ed K).oneValue
      (evalProf V m en ed K) :=
  poly.evalClear_congr (depthPoly_profReduce V m) (BPair.ofPos en) ed K

/-- The reduced product's evaluated collapse is the factors' own at
split clearing powers, the entries read at their representatives'
caps (`def:ground`'s homogeneity principle at the profile
carrier). -/
private theorem evalProf_profMul (V W : poly.PPoly × poly.PPoly) (m : Nat)
    (en ed : Pos) (K1 K2 : Nat)
    (hV : (poly.vnorm (depthPoly V m)).length ≤ K1 + 1)
    (hW : (poly.vnorm (depthPoly W m)).length ≤ K2 + 1) :
    (evalProf (profMul V W) m en ed (K1 + K2)).oneValue
      (evalProf V m en ed K1 * evalProf W m en ed K2) :=
  BPair.oneValue_trans
    (poly.evalClear_congr (depthPoly_profMul V W m) (BPair.ofPos en) ed
      (K1 + K2))
    (poly.evalClear_mulCap (depthPoly V m) (depthPoly W m)
      (BPair.ofPos en) ed K1 K2 hV hW)

/-- The unit clearing's product reads the profile's own collapse. -/
private theorem evalProf_unitMul (V : poly.PPoly × poly.PPoly) (m : Nat)
    (en ed : Pos) (K : Nat)
    (hV : (poly.vnorm (depthPoly V m)).length ≤ K + 1) :
    (evalProf (profMul (constProf (BPair.ofPos Pos.one)) V)
        m en ed K).oneValue (evalProf V m en ed K) := by
  have h := evalProf_profMul (constProf (BPair.ofPos Pos.one)) V m en ed 0 K
    (poly.capOfLen (Nat.le_of_eq (depthConst_len (BPair.ofPos Pos.one) m)))
    hV
  rw [Nat.zero_add] at h
  refine BPair.oneValue_trans h ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr
      (BPair.oneValue_trans
        (evalProf_const (BPair.ofPos Pos.one) m en ed 0)
        (mulBpowZero ed (BPair.ofPos Pos.one)))
      (BPair.oneValue_refl _)) ?_
  exact BPair.ofPos_one_mul (evalProf V m en ed K)

/-- The clearing's evaluated collapse above the sum's unit at the
stated power: the certificate prices it strictly above at its own
power (`boxRead_pos`) and `poly.evalClear_pow` transports that read
up to the stated one. -/
theorem clearPos (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (C : BoxCert) (m K : Nat) (en ed : Pos)
    (hr : boxRead V e0n e0d C)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hlo : C.lo ≤ ⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩)
    (hhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair) ≤ C.hi)
    (hK : C.K + 1 ≤ K + 1) :
    BPair.unit < evalProf V m en ed K := by
  have hpos := boxRead_pos V e0n e0d C hr m en ed he hlo hhi
  have hup := poly.evalClear_pow (depthPoly V m) (BPair.ofPos en) ed K C.K
    (depthPoly_ble hr.1 m) (Nat.le_of_succ_le_succ hK)
  exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hup)
    (ground.unitLtMul
      (ground.unitLtBpow (ground.unitLtOfPos ed) (K - C.K)) hpos)

/-- One row's evaluated dominance comparison at the shared clearing
power: the row's box certificate prices its gap profile's collapse
strictly above the sum's unit at the stated power (`clearPos`), and
the gap profile's split prices the diagonal entry above the off-row
magnitude fold's own evaluation. -/
private theorem domRowCore (e0n : BPair) (e0d : Pos) (i m K : Nat)
    (en ed : Pos) (srow : List (poly.PPoly × poly.PPoly))
    (gap : BoxCert)
    (hr : domRowRead e0n e0d i srow gap)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hlo : gap.lo ≤ ⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩)
    (hhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
      ≤ gap.hi)
    (hK : gap.K + 1 ≤ K + 1) :
    decimation.offFold i (srow.map (fun e => evalProf e m en ed K))
      ≤ evalProf (ground.getAt vacProf srow i) m en ed K := by
  have hposK : BPair.unit
      < evalProf (profAdd (ground.getAt vacProf srow i)
          (profNeg (offMagFold i srow))) m en ed K :=
    clearPos _ e0n e0d gap m K en ed hr he hlo hhi hK
  have hsplit := BPair.oneValue_trans
    (evalProf_profAdd (ground.getAt vacProf srow i)
      (profNeg (offMagFold i srow)) m en ed K)
    (BPair.add_congr (BPair.oneValue_refl _)
      (evalProf_profNeg (offMagFold i srow) m en ed K))
  refine ground.leB_trans (offMagFold_le m en ed K i srow) ?_
  exact ground.leB_of_unit_add
    (ground.leB_of_lt
      (BPair.lt_congr (BPair.oneValue_refl _) hsplit hposK))

/-- `lem:cornerblock`'s row glue: at a row certificate read on
a box holding the depth's composite point, and a shared clearing
power at or beyond the certificate's own, the evaluated row's
off-key magnitude fold sits at or below its diagonal entry —
`thm:decimation`(ii)'s per-row comparison at the evaluated site
datum. -/
theorem domRow_le (e0n : BPair) (e0d : Pos) (i m K : Nat)
    (en ed : Pos) (srow : List (poly.PPoly × poly.PPoly))
    (gap : BoxCert)
    (hr : domRowRead e0n e0d i srow gap)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hlo : gap.lo ≤ ⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩)
    (hhi : (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩ : CPair)
      ≤ gap.hi)
    (hK : gap.K + 1 ≤ K + 1)
    (hi : i < srow.length) :
    decimation.offFold i (srow.map (fun e => evalProf e m en ed K))
      ≤ ground.getAt BPair.unit
        (srow.map (fun e => evalProf e m en ed K)) i := by
  rw [ground.getAt_map vacProf BPair.unit
    (fun e => evalProf e m en ed K) srow i hi]
  exact domRowCore e0n e0d i m K en ed srow gap hr he hlo hhi hK

/-- The evaluated site datum: the family's per-depth collapse
evaluated entrywise at the composite point, cleared at the one
shared power (`cellcount.evalPC` at `pfmDepth`). -/
def evalPfm (S : List (List (poly.PPoly × poly.PPoly))) (m : Nat)
    (en ed : Pos) (K : Nat) : elim.Mat :=
  cellcount.evalPC (pfmDepth m S) (BPair.ofPos en) ed K

/-- The evaluated site datum's rows are the family's rows evaluated
entrywise, the two maps' composition per row (`ground.map_map`). -/
private theorem evalPfm_rows (m : Nat) (en ed : Pos) (K : Nat) :
    ∀ S : List (List (poly.PPoly × poly.PPoly)),
      evalPfm S m en ed K
        = S.map (fun r => r.map (fun e => evalProf e m en ed K))
  | [] => rfl
  | r :: S => by
    show (r.map (fun e => depthPoly e m)).map
          (fun p => poly.evalClear p (BPair.ofPos en) ed K)
        :: evalPfm S m en ed K
      = r.map (fun e => evalProf e m en ed K)
        :: S.map (fun r => r.map (fun e => evalProf e m en ed K))
    rw [ground.map_map (fun e => depthPoly e m)
      (fun p => poly.evalClear p (BPair.ofPos en) ed K) r,
      evalPfm_rows m en ed K S]
    rfl

/-- The collapsed row's entry at a key is the entry's own collapse,
a key beyond the row reading the vacant profile's collapse. -/
private theorem depthEntryEq (m : Nat) :
    ∀ (r : List (poly.PPoly × poly.PPoly)) (k : Nat),
      ground.getAt ([] : poly.Poly) (r.map (fun e => depthPoly e m)) k
        = depthPoly (ground.getAt vacProf r k) m :=
  ground.getAt_mapT vacProf ([] : poly.Poly) (fun e => depthPoly e m) rfl

/-- The collapsed family's entry at two keys is the family's own
entry collapsed. -/
private theorem getAt_pfmDepth (m : Nat)
    (A : List (List (poly.PPoly × poly.PPoly))) (i j : Nat) :
    ground.getAt ([] : poly.Poly)
        (ground.getAt ([] : List poly.Poly) (pfmDepth m A) i) j
      = depthPoly (ground.getAt vacProf
          (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j) m := by
  rw [depthRow m A i]
  exact depthEntryEq m (ground.getAt [] A i) j

/-- The collapsed family's row count is the family's own. -/
private theorem length_pfmDepth (m : Nat)
    (A : List (List (poly.PPoly × poly.PPoly))) :
    (pfmDepth m A).length = A.length := ground.length_map _ A

/-- The collapsed family keeps every row's width. -/
private theorem rowsLen_pfmDepth (m n : Nat)
    (A : List (List (poly.PPoly × poly.PPoly))) (h : elim.rowsLen n A) :
    elim.rowsLen n (pfmDepth m A) :=
  elim.rowsLen_mapRowsO (fun e => depthPoly e m) A n h

/-- One row of two matched families' collapses. -/
private theorem depthCongrRow (m : Nat) :
    ∀ r s : List (poly.PPoly × poly.PPoly),
      ground.matchedOV (ground.matchedRead profDRead) [r] [s] →
      ground.matchedOV poly.polyRead (r.map (fun e => depthPoly e m))
        (s.map (fun e => depthPoly e m))
  | [], [], _ => trivial
  | [], _ :: _, h => False.elim h.1
  | _ :: _, [], h => False.elim h.1
  | a :: r, b :: s, h =>
    ⟨depthPoly_congr a b m h.1.1, depthCongrRow m r s ⟨h.1.2, trivial⟩⟩

/-- Two matched families' collapses read one value entrywise at
every depth. -/
private theorem depthCongrM (m : Nat) :
    ∀ A B : List (List (poly.PPoly × poly.PPoly)), pfmOneValue A B →
      split.pmatOneValue (pfmDepth m A) (pfmDepth m B)
  | [], [], _ => trivial
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h
  | r :: A, s :: B, h =>
    ⟨depthCongrRow m r s ⟨h.1, trivial⟩, depthCongrM m A B h.2⟩

/-- The evaluated site datum is one value across the family's
representatives, at every depth, point and clearing power. -/
private theorem evalPfm_congr (A B : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K : Nat) (h : pfmOneValue A B) :
    elim.matOneValue (evalPfm A m en ed K) (evalPfm B m en ed K) :=
  cellcount.evalPC_pcongr (BPair.ofPos en) ed K (depthCongrM m A B h)

/-- The families' sum evaluates to the evaluated data's own sum. -/
private theorem evalPfm_add (A B : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K : Nat) :
    elim.matOneValue (evalPfm (pfmAdd A B) m en ed K)
      (elim.matAdd (evalPfm A m en ed K) (evalPfm B m en ed K)) :=
  elim.matOne_trans
    (cellcount.evalPC_pcongr (BPair.ofPos en) ed K (pfmDepth_add A B m))
    (cellcount.evalPC_pmatAdd (BPair.ofPos en) ed K (pfmDepth m A)
      (pfmDepth m B))

/-- The family's memberwise swap evaluates to the evaluated datum's
own swap. -/
private theorem evalPfm_swap (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K : Nat) :
    elim.matOneValue (evalPfm (pfmSwap A) m en ed K)
      (elim.matSwap (evalPfm A m en ed K)) :=
  elim.matOne_trans
    (cellcount.evalPC_pcongr (BPair.ofPos en) ed K (pfmDepth_swap A m))
    (cellcount.evalPC_pswapM (BPair.ofPos en) ed K (pfmDepth m A))

/-- The canonical representative's family reads the family's own
entries. -/
private theorem pfmReduce_ovRow :
    ∀ r : List (poly.PPoly × poly.PPoly),
      ground.matchedOV (ground.matchedRead profDRead)
        [r.map profReduce] [r]
  | [] => ⟨trivial, trivial⟩
  | e :: r => ⟨⟨⟨slabReduce_ov e.1, slabReduce_ov e.2⟩,
      (pfmReduce_ovRow r).1⟩, trivial⟩

/-- The canonical representative's family reads the family back. -/
private theorem pfmReduce_ov :
    ∀ A : List (List (poly.PPoly × poly.PPoly)),
      pfmOneValue (pfmReduce A) A
  | [] => trivial
  | r :: A => ⟨(pfmReduce_ovRow r).1, pfmReduce_ov A⟩

/-- The canonically represented family's evaluated datum is the
family's own. -/
private theorem evalPfm_reduce (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K : Nat) :
    elim.matOneValue (evalPfm (pfmReduce A) m en ed K)
      (evalPfm A m en ed K) :=
  evalPfm_congr (pfmReduce A) A m en ed K (pfmReduce_ov A)

/-- The family's depth shift evaluates to the family's evaluated
datum at the successor depth. -/
private theorem evalPfm_shift (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K : Nat) :
    elim.matOneValue (evalPfm (pfmShift A) m en ed K)
      (evalPfm A (m + 1) en ed K) :=
  cellcount.evalPC_pcongr (BPair.ofPos en) ed K (pfmDepth_shift A m)

/-- The rescaled family's evaluated datum is the scale's own
evaluated collapse weighting the evaluated family, the clearing
powers splitting at the representatives' caps — the canonical key
counts, one value's own read (`def:ground`'s homogeneity
principle). -/
private theorem evalPfm_scale (f : poly.PPoly × poly.PPoly)
    (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K1 K2 : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K1 + 1)
    (hA : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ K2 + 1) :
    elim.matOneValue (evalPfm (pfmScale f A) m en ed (K1 + K2))
      (inertia.matScaleB (evalProf f m en ed K1)
        (evalPfm A m en ed K2)) :=
  elim.matOne_trans
    (cellcount.evalPC_pcongr (BPair.ofPos en) ed (K1 + K2)
      (pfmDepth_scale f A m))
    (cellcount.evalPC_pscaleM (depthPoly f m) (BPair.ofPos en) ed K1 K2 hf
      (pfmDepth m A)
      (fun i j => by rw [getAt_pfmDepth m A i j]; exact hA i j))

/-- The families' product's evaluated datum is the evaluated
factors' own product, the clearing powers splitting at the entries'
representatives' caps (`def:ground`'s homogeneity principle). -/
private theorem evalPfm_mul (A B : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K1 K2 w n : Nat)
    (ha : elim.rowsLen w A) (hbl : B.length = w) (hw : 0 < w)
    (hb : elim.rowsLen n B)
    (hda : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ K1 + 1)
    (hdb : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) B i) j)
        m)).length ≤ K2 + 1) :
    elim.matOneValue (evalPfm (pfmMul A B) m en ed (K1 + K2))
      (elim.matMul (evalPfm A m en ed K1) (evalPfm B m en ed K2)) :=
  elim.matOne_trans
    (cellcount.evalPC_pcongr (BPair.ofPos en) ed (K1 + K2)
      (pfmDepth_mul A B m))
    (cellcount.evalPC_pmatMul (pfmDepth m A) (pfmDepth m B)
      (BPair.ofPos en) ed K1 K2 w n (rowsLen_pfmDepth m w A ha)
      (by rw [length_pfmDepth m B]; exact hbl) hw
      (rowsLen_pfmDepth m n B hb)
      (fun i j => by rw [getAt_pfmDepth m A i j]; exact hda i j)
      (fun i j => by rw [getAt_pfmDepth m B i j]; exact hdb i j))

/-- One row of the constant family's evaluation: each entry's
one-key list reads its coefficient against the whole clearing
power. -/
private theorem ofMatRowEval (ln : BPair) (ed : Pos) (K : Nat) :
    ∀ r : List BPair,
      poly.oneValue
        ((r.map (fun c => ([c] : poly.Poly))).map
          (fun p => poly.evalClear p ln ed K))
        (poly.scaleP (ground.bpow (BPair.ofPos ed) K) r)
  | [] => trivial
  | c :: r =>
    ⟨BPair.oneValue_trans (poly.evalClear_single c ln ed K)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.mul_comm c (ground.bpow (BPair.ofPos ed) K)))
        (BPair.oneValue_symm (BPair.norm_oneValue _))),
     ofMatRowEval ln ed K r⟩

/-- The constant family's evaluation is the stated matrix weighted
by the whole clearing power. -/
private theorem ofMatEval (ln : BPair) (ed : Pos) (K : Nat) :
    ∀ X : elim.Mat,
      elim.matOneValue
        (cellcount.evalPC
          (elim.embedP X) ln ed K)
        (inertia.matScaleB (ground.bpow (BPair.ofPos ed) K) X)
  | [] => trivial
  | r :: X => ⟨ofMatRowEval ln ed K r, ofMatEval ln ed K X⟩

/-- The constant family's evaluated datum is the stated matrix
weighted by the clearing's whole power, at every depth. -/
private theorem evalPfm_ofMat (X : elim.Mat) (m : Nat) (en ed : Pos) (K : Nat) :
    elim.matOneValue (evalPfm (ofMatProf X) m en ed K)
      (inertia.matScaleB (ground.bpow (BPair.ofPos ed) K) X) :=
  elim.matOne_trans
    (cellcount.evalPC_pcongr (BPair.ofPos en) ed K (pfmDepth_ofMat X m))
    (ofMatEval (BPair.ofPos en) ed K X)

/-- The key exchange passes the cleared evaluation: the exchanged
family's evaluated matrix is the evaluated matrix's own exchange, at
stated rectangular shape. -/
private theorem evalPC_transposeO (ln : BPair) (c : Pos) (K : Nat)
    (o : Nat) (S : split.PMat) (hl : S.length = o)
    (hr : elim.rowsLen o S) :
    elim.matOneValue
      (cellcount.evalPC (elim.transposeO poly.polyOps S) ln c K)
      (elim.transposeM (cellcount.evalPC S ln c K)) := by
  cases S with
  | nil => trivial
  | cons r t =>
    have hS : 0 < (r :: t).length := Nat.succ_pos _
    have hEl : (cellcount.evalPC (r :: t) ln c K).length = (r :: t).length :=
      cellcount.length_evalPC (r :: t) ln c K
    have hEr : elim.rowsLen o (cellcount.evalPC (r :: t) ln c K) :=
      cellcount.rowsLen_evalPC o (r :: t) ln c K hr
    have hLl : (cellcount.evalPC
        (elim.transposeO poly.polyOps (r :: t)) ln c K).length = o := by
      rw [cellcount.length_evalPC]
      exact elim.length_transposeO poly.polyOps (r :: t) hr hS
    have hRl : (elim.transposeM (cellcount.evalPC (r :: t) ln c K)).length
        = o :=
      elim.length_transposeM (cellcount.evalPC (r :: t) ln c K) hEr
        (by rw [hEl]; exact hS)
    refine elim.matOne_getAt _ _ (by rw [hLl, hRl]) ?_
    intro p hp
    rw [hLl] at hp
    refine poly.ov_of_getAt ?_
    intro q
    rw [cellcount.getAt_evalPC ln c K (elim.transposeO poly.polyOps (r :: t)) p q]
    match Nat.lt_or_ge q (r :: t).length with
    | Or.inl hq =>
      rw [elim.getAt_transposeO poly.polyOps ([] : poly.Poly) (r :: t) hr p q hp hq,
        elim.getAt_transposeM BPair.unit
          (cellcount.evalPC (r :: t) ln c K) hEr p q hp (by rw [hEl]; exact hq),
        cellcount.getAt_evalPC ln c K (r :: t) q p]
      exact BPair.oneValue_refl _
    | Or.inr hq =>
      have hLrow : (ground.getAt ([] : List poly.Poly)
          (elim.transposeO poly.polyOps (r :: t)) p).length = (r :: t).length :=
        elim.rowsLen_getAt (elim.transposeO poly.polyOps (r :: t)) p
          (elim.rowsLen_transposeO poly.polyOps (r :: t))
          (by rw [elim.length_transposeO poly.polyOps (r :: t) hr hS]; exact hp)
      have hRrow : (ground.getAt ([] : List BPair)
          (elim.transposeM (cellcount.evalPC (r :: t) ln c K)) p).length
          = (cellcount.evalPC (r :: t) ln c K).length :=
        elim.rowsLen_getAt (elim.transposeM (cellcount.evalPC (r :: t) ln c K)) p
          (elim.rowsLen_transposeO ground.bpairOps
            (cellcount.evalPC (r :: t) ln c K))
          (by rw [hRl]; exact hp)
      rw [ground.getAt_over ([] : poly.Poly) _ q (by rw [hLrow]; exact hq),
        ground.getAt_over BPair.unit _ q (by rw [hRrow, hEl]; exact hq)]
      exact BPair.oneValue_refl _

/-- The family's key exchange evaluates to the evaluated site
datum's own exchange, at stated rectangular shape. -/
private theorem evalPfm_tr (A : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (en ed : Pos) (K : Nat) (o : Nat)
    (hl : A.length = o) (hr : elim.rowsLen o A) :
    elim.matOneValue (evalPfm (pfmTr A) m en ed K)
      (elim.transposeM (evalPfm A m en ed K)) :=
  elim.matOne_trans
    (cellcount.evalPC_pcongr (BPair.ofPos en) ed K (pfmDepth_tr A m))
    (evalPC_transposeO (BPair.ofPos en) ed K o (pfmDepth m A)
      (by rw [length_pfmDepth m A]; exact hl) (rowsLen_pfmDepth m o A hr))

/-- The dominance walk's evaluated read at a stated row key: the
row's comparison holds at the walked key, the certificate list
stepping with the rows. -/
private theorem domIdx (e0n : BPair) (e0d : Pos) (m K : Nat)
    (en ed : Pos)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed) :
    ∀ (i : Nat) (S : List (List (poly.PPoly × poly.PPoly)))
      (gs : List BoxCert),
      domCertGo e0n e0d i S gs →
      (gs.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (K + 1))) = true →
      ∀ j, j < S.length →
        decimation.offFold (i + j)
            (ground.getAt ([] : List BPair)
              (S.map (fun r =>
                r.map (fun e => evalProf e m en ed K))) j)
          ≤ ground.getAt BPair.unit
            (ground.getAt ([] : List BPair)
              (S.map (fun r =>
                r.map (fun e => evalProf e m en ed K))) j) (i + j)
  | _, [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | _, _ :: _, [], hc, _, _, _ => False.elim hc
  | i, sr :: _, g :: _, hc, hb, 0, _ => by
    have hg := ground.andSplitB (ground.andSplitB hb).1
    have hg2 := ground.andSplitB hg.1
    show decimation.offFold (i + 0)
        (sr.map (fun e => evalProf e m en ed K))
      ≤ ground.getAt BPair.unit
        (sr.map (fun e => evalProf e m en ed K)) (i + 0)
    rw [Nat.add_zero, getAt_evalRow m en ed K sr i]
    exact domRowCore e0n e0d i m K en ed sr g hc.1 he
      (of_decide_eq_true hg2.1) (of_decide_eq_true hg2.2)
      (ground.bleLe hg.2)
  | i, _ :: srs, _ :: gs, hc, hb, j + 1, hj => by
    have e : i + (j + 1) = i + 1 + j := by
      rw [Nat.add_assoc i 1 j, Nat.add_comm 1 j]
    show decimation.offFold (i + (j + 1))
        (ground.getAt ([] : List BPair)
          (srs.map (fun r =>
            r.map (fun e => evalProf e m en ed K))) j)
      ≤ ground.getAt BPair.unit
        (ground.getAt ([] : List BPair)
          (srs.map (fun r =>
            r.map (fun e => evalProf e m en ed K))) j) (i + (j + 1))
    rw [e]
    exact domIdx e0n e0d m K en ed he (i + 1) srs gs hc.2
      (ground.andSplitB hb).2 j (Nat.lt_of_succ_lt_succ hj)

/-- `lem:cornerblock`'s site glue: at a dominance certificate
walk over a site datum, with every row certificate's box holding the
depth's composite point and its clearing power inside the shared
one, the evaluated site datum is diagonally dominant
(`thm:decimation`(ii)'s comparison at the evaluated family). -/
theorem domCert_domAt (e0n : BPair) (e0d : Pos) (m K : Nat)
    (en ed : Pos) (S : List (List (poly.PPoly × poly.PPoly)))
    (gs : List BoxCert)
    (hc : domCertGo e0n e0d 0 S gs)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (gs.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (K + 1))) = true) :
    decimation.domAt (evalPfm S m en ed K) := by
  refine decimation.domAt_of_rows (n := S.length) (evalPfm S m en ed K)
    (by rw [evalPfm_rows m en ed K S]; exact ground.length_map _ _) ?_
  intro i hi
  rw [evalPfm_rows m en ed K S]
  have h0 := domIdx e0n e0d m K en ed he 0 S gs hc hbox i hi
  rw [Nat.zero_add] at h0
  exact h0

open elim inertia in
/-- `lem:cornerblock`'s form glue: the evaluated site datum's
dominance prices its quadratic form at or above the sum's unit at
every vector of the site's order — `thm:decimation`(ii)'s display at
the dominance read.  The square and symmetry reads are
`decimation.dom_unit`'s own binders: the dominance walk reads the
magnitudes alone. -/
theorem domCert_form (e0n : BPair) (e0d : Pos) (m K : Nat)
    (en ed : Pos) (S : List (List (poly.PPoly × poly.PPoly)))
    (gs : List BoxCert)
    (hc : domCertGo e0n e0d 0 S gs)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (gs.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (K + 1))) = true)
    (hsq : elim.sqAt (evalPfm S m en ed K) S.length)
    (hsym : matOneValue (evalPfm S m en ed K)
      (transposeM (evalPfm S m en ed K))) :
    ∀ v : List BPair, v.length = S.length →
      BPair.unit ≤ quadForm (evalPfm S m en ed K) v :=
  fun v hv => decimation.dom_unit (evalPfm S m en ed K) hsq hsym
    (domCert_domAt e0n e0d m K en ed S gs hc he hbox) v hv

/-! `lem:cornerblock`'s four count reshapes: each site datum's
dominance certificate walk prices its evaluated form at or above the
sum's unit, and the form's decomposition reads that price as the
pointwise count the tex states — the floor's center comparison, the
contraction's transfer comparison and the defect cap's two arms, the
margins the clearings' own evaluated reads. -/

/-! The clearing cap: a scale polynomial's canonical representative
sits inside the stated power.  The cap is a class read — the
representative is one value's own (`poly.vnorm_congr`) — so it rides
every one-value bridge, and it prices the cleared evaluation's
faithfulness exactly where the literal key count does. -/

/-- The cap is one value's own read. -/
private theorem capCongr {p q : poly.Poly} {K : Nat}
    (h : poly.oneValue p q) (hq : (poly.vnorm q).length ≤ K + 1) :
    (poly.vnorm p).length ≤ K + 1 := by
  rw [poly.vnorm_congr h]
  exact hq

/-- The memberwise swap keeps the cap. -/
private theorem capNeg {p : poly.Poly} {K : Nat}
    (h : (poly.vnorm p).length ≤ K + 1) :
    (poly.vnorm (poly.neg p)).length ≤ K + 1 := by
  rw [poly.vnorm_neg p, poly.length_neg (poly.vnorm p)]
  exact h

/-- The sum's cap is the summands' own. -/
private theorem capAdd {p q : poly.Poly} {K : Nat}
    (hp : (poly.vnorm p).length ≤ K + 1)
    (hq : (poly.vnorm q).length ≤ K + 1) :
    (poly.vnorm (poly.add p q)).length ≤ K + 1 :=
  capCongr
    (poly.add_congr (poly.oneValue_symm (poly.vnorm_ov p))
      (poly.oneValue_symm (poly.vnorm_ov q)))
    (poly.capOfLen (poly.add_len_le _ _ (K + 1) hp hq))

/-- The product's cap: the factors' caps add. -/
private theorem capMul {p q : poly.Poly} {K1 K2 : Nat}
    (hp : (poly.vnorm p).length ≤ K1 + 1)
    (hq : (poly.vnorm q).length ≤ K2 + 1) :
    (poly.vnorm (poly.mul p q)).length ≤ K1 + K2 + 1 :=
  capCongr (poly.mul_vnorm_ov p q)
    (poly.capOfLen (poly.mul_len_le _ _ K1 K2 hp hq))

/-- A profile against two constant profiles, evaluated at the doubled
clearing power: the profile's own collapse against the two
coefficients, the clearing's whole power riding. -/
private theorem evalMulConst (f : poly.PPoly × poly.PPoly) (x c : BPair)
    (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1) :
    (evalProf (profMul (profMul f (constProf x)) (constProf c))
        m en ed (K + K)).oneValue
      ((evalProf f m en ed K * x * ground.bpow (BPair.ofPos ed) K) * c) := by
  have hQ : (poly.vnorm (depthPoly (constProf x) m)).length ≤ 0 + 1 :=
    poly.capOfLen (Nat.le_of_eq (depthConst_len x m))
  have hR : (poly.vnorm (depthPoly (constProf c) m)).length ≤ K + 1 :=
    poly.capOfLen (Nat.le_trans (Nat.le_of_eq (depthConst_len c m))
      (Nat.succ_le_succ (Nat.zero_le K)))
  have hPQ : (poly.vnorm (poly.mul (depthPoly f m)
      (depthPoly (constProf x) m))).length ≤ K + 1 := by
    have h := capMul hf hQ
    rw [Nat.add_zero] at h
    exact h
  have hcol : poly.oneValue
      (depthPoly (profMul (profMul f (constProf x)) (constProf c)) m)
      (poly.mul (poly.mul (depthPoly f m) (depthPoly (constProf x) m))
        (depthPoly (constProf c) m)) :=
    poly.oneValue_trans
      (depthPoly_profMul (profMul f (constProf x)) (constProf c) m)
      (poly.mul_congr_left (depthPoly_profMul f (constProf x) m)
        (depthPoly (constProf c) m))
  have hsplit : (poly.evalClear
      (poly.mul (depthPoly f m) (depthPoly (constProf x) m))
      (BPair.ofPos en) ed K).oneValue
      (evalProf f m en ed K * evalProf (constProf x) m en ed 0) := by
    have h := poly.evalClear_mulCap (depthPoly f m)
      (depthPoly (constProf x) m) (BPair.ofPos en) ed K 0 hf hQ
    rw [Nat.add_zero] at h
    exact h
  refine BPair.oneValue_trans
    (poly.evalClear_congr hcol (BPair.ofPos en) ed (K + K)) ?_
  refine BPair.oneValue_trans
    (poly.evalClear_mulCap _ (depthPoly (constProf c) m) (BPair.ofPos en) ed
      K K hPQ hR) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr hsplit (evalProf_const c m en ed K)) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr
      (BPair.mul_congr (BPair.oneValue_refl _) (evalProf_const x m en ed 0))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr
      (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_ofPos x Pos.one))
      (BPair.oneValue_refl _)) ?_
  rw [BPair.scale_one x, BPair.mul_comm c (ground.bpow (BPair.ofPos ed) K),
    ← BPair.mul_assoc (evalProf f m en ed K * x)
      (ground.bpow (BPair.ofPos ed) K) c]
  exact BPair.oneValue_refl _

/-- One row of the constant family rescaled at a profile against a
constant profile: the row's coefficients weighted by the profile's
own evaluated collapse against the constant and the clearing. -/
private theorem evalScaleOfMatRow (f : poly.PPoly × poly.PPoly) (x : BPair)
    (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1) :
    ∀ r : List BPair,
      poly.oneValue
        (((r.map constProf).map (profMul (profMul f (constProf x)))).map
          (fun e => evalProf e m en ed (K + K)))
        (poly.scaleP
          (evalProf f m en ed K * x * ground.bpow (BPair.ofPos ed) K) r)
  | [] => trivial
  | c :: r =>
    ⟨BPair.oneValue_trans (evalMulConst f x c m en ed K hf)
      (BPair.oneValue_symm (BPair.norm_oneValue _)),
     evalScaleOfMatRow f x m en ed K hf r⟩

/-- The constant family rescaled at a profile against a constant
profile, evaluated row by row. -/
private theorem evalScaleOfMatGo (f : poly.PPoly × poly.PPoly) (x : BPair)
    (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1) :
    ∀ X : elim.Mat,
      elim.matOneValue
        ((pfmScale (profMul f (constProf x)) (ofMatProf X)).map
          (fun r => r.map (fun e => evalProf e m en ed (K + K))))
        (inertia.matScaleB
          (evalProf f m en ed K * x * ground.bpow (BPair.ofPos ed) K) X)
  | [] => trivial
  | r :: X =>
    ⟨evalScaleOfMatRow f x m en ed K hf r,
     evalScaleOfMatGo f x m en ed K hf X⟩

/-- The constant family rescaled at a profile against a constant
profile: the stated matrix weighted by the profile's evaluated
collapse, the constant and the clearing's whole power. -/
private theorem evalScaleOfMat (f : poly.PPoly × poly.PPoly) (x : BPair)
    (X : elim.Mat) (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1) :
    elim.matOneValue
      (evalPfm (pfmScale (profMul f (constProf x)) (ofMatProf X))
        m en ed (K + K))
      (inertia.matScaleB
        (evalProf f m en ed K * x * ground.bpow (BPair.ofPos ed) K) X) := by
  rw [evalPfm_rows m en ed (K + K)
    (pfmScale (profMul f (constProf x)) (ofMatProf X))]
  exact evalScaleOfMatGo f x m en ed K hf X

/-- The evaluated site datum's row count is the family's own. -/
theorem length_evalPfm (m : Nat)
    (A : List (List (poly.PPoly × poly.PPoly))) (en ed : Pos) (K : Nat) :
    (evalPfm A m en ed K).length = A.length :=
  (cellcount.length_evalPC (pfmDepth m A) (BPair.ofPos en) ed K).trans
    (length_pfmDepth m A)

/-- The evaluated site datum keeps every row's width. -/
theorem rowsLen_evalPfm (n m : Nat)
    (A : List (List (poly.PPoly × poly.PPoly))) (en ed : Pos) (K : Nat)
    (h : elim.rowsLen n A) : elim.rowsLen n (evalPfm A m en ed K) :=
  cellcount.rowsLen_evalPC n (pfmDepth m A) (BPair.ofPos en) ed K
    (rowsLen_pfmDepth m n A h)

/-- The rescaled family's row count is the family's own. -/
private theorem length_pfmScale (f : poly.PPoly × poly.PPoly)
    (A : List (List (poly.PPoly × poly.PPoly))) :
    (pfmScale f A).length = A.length := ground.length_map _ A

/-- The rescaled family keeps every row's width. -/
private theorem rowsLen_pfmScale (f : poly.PPoly × poly.PPoly) (n : Nat)
    (A : List (List (poly.PPoly × poly.PPoly))) (h : elim.rowsLen n A) :
    elim.rowsLen n (pfmScale f A) :=
  elim.rowsLen_mapRowsO (profMul f) A n h

/-- The swapped family's row count is the family's own. -/
private theorem length_pfmSwap (A : List (List (poly.PPoly × poly.PPoly))) :
    (pfmSwap A).length = A.length := ground.length_map _ A

/-- The swapped family keeps every row's width. -/
private theorem rowsLen_pfmSwap (n : Nat)
    (A : List (List (poly.PPoly × poly.PPoly))) (h : elim.rowsLen n A) :
    elim.rowsLen n (pfmSwap A) :=
  elim.rowsLen_mapRowsO profOps.swap A n h

/-- The constant family's row count is the stated matrix's own. -/
private theorem length_ofMatProf (X : elim.Mat) :
    (ofMatProf X).length = X.length := ground.length_map _ X

/-- The constant family keeps every row's width. -/
private theorem rowsLen_ofMatProf (n : Nat) (X : elim.Mat)
    (h : elim.rowsLen n X) : elim.rowsLen n (ofMatProf X) :=
  elim.rowsLen_mapRowsO constProf X n h

/-- The families' sum keeps the shared row count. -/
private theorem length_pfmAdd
    (A B : List (List (poly.PPoly × poly.PPoly)))
    (h : A.length = B.length) : (pfmAdd A B).length = A.length :=
  ground.length_zipWith (List.zipWith profOps.add) A B A.length rfl h.symm

/-- The families' sum keeps the shared row width. -/
private theorem rowsLen_pfmAdd (n : Nat) :
    ∀ A B : List (List (poly.PPoly × poly.PPoly)),
      elim.rowsLen n A → elim.rowsLen n B → elim.rowsLen n (pfmAdd A B)
  | [], _, _, _ => trivial
  | _ :: _, [], _, _ => trivial
  | r :: A, s :: B, ha, hb =>
    ⟨(ground.length_zipWith profOps.add r s r.length rfl
        ((ha.1.trans hb.1.symm)).symm).trans ha.1,
     rowsLen_pfmAdd n A B ha.2 hb.2⟩

/-- The swapped family's entry at two keys is the entry's own
memberwise swap. -/
private theorem getAt_pfmSwapRow :
    ∀ (r : List (poly.PPoly × poly.PPoly)) (j : Nat),
      ground.getAt vacProf (r.map profOps.swap) j
        = profNeg (ground.getAt vacProf r j) :=
  ground.getAt_mapT vacProf vacProf profOps.swap rfl

/-- The swapped family's rows are the family's own rows swapped. -/
private theorem getAt_pfmSwap
    (A : List (List (poly.PPoly × poly.PPoly))) (i j : Nat) :
    ground.getAt vacProf
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
          (pfmSwap A) i) j
      = profNeg (ground.getAt vacProf
          (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j) := by
  rw [show ground.getAt ([] : List (poly.PPoly × poly.PPoly))
      (pfmSwap A) i
      = (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).map
          profOps.swap from
    ground.getAt_mapT ([] : List (poly.PPoly × poly.PPoly))
      ([] : List (poly.PPoly × poly.PPoly))
      (fun r => r.map profOps.swap) rfl A i]
  exact getAt_pfmSwapRow _ j

/-- Two matched rows read one value at every key. -/
private theorem matchedEntry : ∀ {r s : List poly.Poly},
    ground.matchedOV poly.polyRead r s →
    ∀ j, poly.oneValue (ground.getAt ([] : poly.Poly) r j)
      (ground.getAt ([] : poly.Poly) s j)
  | [], [], _, _ => poly.oneValue_refl _
  | [], _ :: _, h, _ => False.elim h
  | _ :: _, [], h, _ => False.elim h
  | _ :: _, _ :: _, h, 0 => h.1
  | _ :: r, _ :: s, h, j + 1 => matchedEntry (r := r) (s := s) h.2 j

/-- Two matched polynomial matrices read one value at every key
pair. -/
private theorem pmatEntry : ∀ {A B : split.PMat}, split.pmatOneValue A B →
    ∀ i j, poly.oneValue
      (ground.getAt ([] : poly.Poly)
        (ground.getAt ([] : List poly.Poly) A i) j)
      (ground.getAt ([] : poly.Poly)
        (ground.getAt ([] : List poly.Poly) B i) j)
  | [], [], _, _, _ => poly.oneValue_refl _
  | [], _ :: _, h, _, _ => False.elim h
  | _ :: _, [], h, _, _ => False.elim h
  | _ :: _, _ :: _, h, 0, j => matchedEntry h.1 j
  | _ :: A, _ :: B, h, i + 1, j => pmatEntry (A := A) (B := B) h.2 i j

/-- A family fold of sums carries the summands' shared cap. -/
private theorem capFamFold {N : Nat} (f : Nat → poly.Poly)
    (h : ∀ s, (poly.vnorm (f s)).length ≤ N + 1) :
    ∀ l : List Nat,
      (poly.vnorm (ground.famFold poly.add ([] : poly.Poly) f l)).length
        ≤ N + 1
  | [] => Nat.zero_le _
  | a :: t => capAdd (h a) (capFamFold f h t)

/-- The families' product's entries carry the factors' caps added:
the entry is the row-against-column fold of the factors' own
entries, so the sum's cap is the products' shared one. -/
private theorem capPfmMul (A B : List (List (poly.PPoly × poly.PPoly)))
    (m : Nat) (Ka Kb w n : Nat)
    (ha : elim.rowsLen w A) (hbl : B.length = w) (hw : 0 < w)
    (hb : elim.rowsLen n B)
    (hA : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ Ka + 1)
    (hB : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) B i) j)
        m)).length ≤ Kb + 1) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmMul A B) i) j) m)).length ≤ Ka + Kb + 1 := by
  intro i j
  have hbh : ((pfmDepth m B).headD ([] : List poly.Poly)).length = n :=
    elim.headD_width n (pfmDepth m B)
      (by rw [length_pfmDepth m B, hbl]; exact hw)
      (rowsLen_pfmDepth m n B hb)
  rw [← getAt_pfmDepth m (pfmMul A B) i j]
  refine capCongr (pmatEntry (pfmDepth_mul A B m) i j) ?_
  match Nat.lt_or_ge i (pfmDepth m A).length with
  | Or.inr hge =>
    rw [ground.getAt_over ([] : List poly.Poly) _ i
      (by
        rw [show (split.pmatMul (pfmDepth m A) (pfmDepth m B)).length
            = (pfmDepth m A).length from ground.length_map _ _]
        exact hge)]
    exact Nat.zero_le _
  | Or.inl hi =>
    match Nat.lt_or_ge j n with
    | Or.inr hge =>
      rw [ground.getAt_over ([] : poly.Poly) _ j
        (by
          rw [elim.rowsLen_getAt (split.pmatMul (pfmDepth m A) (pfmDepth m B))
            i (elim.rowsLen_matMulO poly.polyOps (pfmDepth m A)
              (pfmDepth m B) n hbh)
            (by
              rw [show (split.pmatMul (pfmDepth m A) (pfmDepth m B)).length
                  = (pfmDepth m A).length from ground.length_map _ _]
              exact hi)]
          exact hge)]
      exact Nat.zero_le _
    | Or.inl hj =>
      refine capCongr
        (elim.matMulP_entry (pfmDepth m A) (pfmDepth m B) w n
          (rowsLen_pfmDepth m w A ha) hbh i j hi hj) ?_
      refine capFamFold _ (fun s => ?_) (List.range w)
      refine capMul ?_ ?_
      · rw [getAt_pfmDepth m A i s]
        exact hA i s
      · rw [getAt_pfmDepth m B s j]
        exact hB s j

/-- The constant family's rows are the stated matrix's own rows at
the constant profile. -/
private theorem getAt_ofMatRows : ∀ (X : elim.Mat) (i : Nat),
    ground.getAt ([] : List (poly.PPoly × poly.PPoly)) (ofMatProf X) i
      = (ground.getAt ([] : List BPair) X i).map constProf :=
  ground.getAt_mapT ([] : List BPair)
    ([] : List (poly.PPoly × poly.PPoly)) (fun r => r.map constProf)
    rfl

/-- The constant family's entries collapse to one key at every
depth. -/
private theorem ofMatEntryLen (X : elim.Mat) (m : Nat) (i j : Nat) :
    (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (ofMatProf X) i) j) m).length ≤ 0 + 1 := by
  rw [getAt_ofMatRows X i]
  match Nat.lt_or_ge j (ground.getAt ([] : List BPair) X i).length with
  | Or.inr hge =>
    rw [ground.getAt_over vacProf _ j (by rw [ground.length_map]; exact hge)]
    exact Nat.zero_le _
  | Or.inl hj =>
    rw [ground.getAt_map BPair.unit vacProf constProf _ j hj,
      depthConst_len]
    exact Nat.le_refl 1

/-- The exchanged family's entries collapse at the family's own key
counts, the two keys exchanged. -/
private theorem pfmTrEntryLen
    (A : List (List (poly.PPoly × poly.PPoly))) (o m K : Nat)
    (hl : A.length = o) (hr : elim.rowsLen o A)
    (h : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ K + 1) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmTr A) i) j) m)).length ≤ K + 1 := by
  intro i j
  match A, hl with
  | [], hl0 =>
    rw [ground.getAt_over ([] : List (poly.PPoly × poly.PPoly))
      (pfmTr ([] : List (List (poly.PPoly × poly.PPoly)))) i
      (Nat.zero_le i)]
    exact Nat.zero_le _
  | r :: t, hl1 =>
    have hpos : 0 < (r :: t).length := Nat.succ_pos _
    have htl : (pfmTr (r :: t)).length = o :=
      elim.length_transposeO profOps (r :: t) hr hpos
    match Nat.lt_or_ge i o with
    | Or.inr hge =>
      rw [ground.getAt_over ([] : List (poly.PPoly × poly.PPoly))
        (pfmTr (r :: t)) i (by rw [htl]; exact hge)]
      exact Nat.zero_le _
    | Or.inl hi =>
      match Nat.lt_or_ge j o with
      | Or.inr hge =>
        rw [ground.getAt_over vacProf _ j
          (by
            rw [elim.rowsLen_getAt (pfmTr (r :: t)) i
              (elim.rowsLen_transposeO profOps (r :: t))
              (by rw [htl]; exact hi), hl1]
            exact hge)]
        exact Nat.zero_le _
      | Or.inl hj =>
        rw [show pfmTr (r :: t) = elim.transposeO profOps (r :: t) from rfl,
          elim.getAt_transposeO profOps vacProf (r :: t) hr i j hi
            (by rw [hl1]; exact hj)]
        exact h j i

/-- The rescaled family's rows are the family's own rows rescaled. -/
private theorem getAt_pfmScaleRows (f : poly.PPoly × poly.PPoly) :
    ∀ (A : List (List (poly.PPoly × poly.PPoly))) (i : Nat),
      ground.getAt ([] : List (poly.PPoly × poly.PPoly))
          (pfmScale f A) i
        = (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).map
            (profMul f) :=
  ground.getAt_mapT ([] : List (poly.PPoly × poly.PPoly))
    ([] : List (poly.PPoly × poly.PPoly)) (fun r => r.map (profMul f))
    rfl

/-- The rescaled family's entries carry the scale's cap added to the
family's own. -/
private theorem capPfmScale (f : poly.PPoly × poly.PPoly)
    (A : List (List (poly.PPoly × poly.PPoly))) (m Ka Kb : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ Ka + 1)
    (hA : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ Kb + 1) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmScale f A) i) j) m)).length ≤ Ka + Kb + 1 := by
  intro i j
  rw [getAt_pfmScaleRows f A i]
  match Nat.lt_or_ge j
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).length with
  | Or.inr hge =>
    rw [ground.getAt_over vacProf _ j (by rw [ground.length_map]; exact hge)]
    exact Nat.zero_le _
  | Or.inl hj =>
    rw [ground.getAt_map vacProf vacProf (profMul f) _ j hj]
    exact capCongr (depthPoly_profMul f _ m) (capMul hf (hA i j))

/-- One row of a componentwise profile sum carries the summands'
shared cap. -/
private theorem capZipRow (m K : Nat) :
    ∀ r s : List (poly.PPoly × poly.PPoly),
      (∀ j, (poly.vnorm (depthPoly (ground.getAt vacProf r j) m)).length
        ≤ K + 1) →
      (∀ j, (poly.vnorm (depthPoly (ground.getAt vacProf s j) m)).length
        ≤ K + 1) →
      ∀ j, (poly.vnorm (depthPoly (ground.getAt vacProf
        (List.zipWith profOps.add r s) j) m)).length ≤ K + 1
  | [], _, _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _, _ => Nat.zero_le _
  | _ :: _, _ :: _, ha, hb, 0 =>
    capCongr (depthPoly_profAdd _ _ m) (capAdd (ha 0) (hb 0))
  | _ :: r, _ :: s, ha, hb, j + 1 =>
    capZipRow m K r s (fun k => ha (k + 1)) (fun k => hb (k + 1)) j

/-- The families' sum's entries carry the summands' shared cap. -/
private theorem capPfmAdd (m K : Nat) :
    ∀ A B : List (List (poly.PPoly × poly.PPoly)),
      (∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
          m)).length ≤ K + 1) →
      (∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) B i) j)
          m)).length ≤ K + 1) →
      ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
          (pfmAdd A B) i) j) m)).length ≤ K + 1
  | [], _, _, _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _, _, _ => Nat.zero_le _
  | _ :: _, _ :: _, ha, hb, 0, j =>
    capZipRow m K _ _ (fun k => ha 0 k) (fun k => hb 0 k) j
  | _ :: A, _ :: B, ha, hb, i + 1, j =>
    capPfmAdd m K A B (fun p q => ha (p + 1) q) (fun p q => hb (p + 1) q) i j

/-- The canonically represented family's rows are the family's own
rows represented. -/
private theorem getAt_pfmReduceRows :
    ∀ (A : List (List (poly.PPoly × poly.PPoly))) (i : Nat),
      ground.getAt ([] : List (poly.PPoly × poly.PPoly))
          (pfmReduce A) i
        = (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).map
            profReduce :=
  ground.getAt_mapT ([] : List (poly.PPoly × poly.PPoly))
    ([] : List (poly.PPoly × poly.PPoly)) (fun r => r.map profReduce)
    rfl

/-- The canonically represented family's entries carry the family's
own caps. -/
private theorem capPfmReduce (A : List (List (poly.PPoly × poly.PPoly)))
    (m K : Nat)
    (hA : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ K + 1) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmReduce A) i) j) m)).length ≤ K + 1 := by
  intro i j
  rw [getAt_pfmReduceRows A i]
  match Nat.lt_or_ge j
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).length with
  | Or.inr hge =>
    rw [ground.getAt_over vacProf _ j (by rw [ground.length_map]; exact hge)]
    exact Nat.zero_le _
  | Or.inl hj =>
    rw [ground.getAt_map vacProf vacProf profReduce _ j hj]
    exact capCongr (depthPoly_profReduce _ m) (hA i j)

/-- The shifted family's rows are the family's own rows shifted. -/
private theorem getAt_pfmShiftRows :
    ∀ (A : List (List (poly.PPoly × poly.PPoly))) (i : Nat),
      ground.getAt ([] : List (poly.PPoly × poly.PPoly))
          (pfmShift A) i
        = (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).map
            profShift :=
  ground.getAt_mapT ([] : List (poly.PPoly × poly.PPoly))
    ([] : List (poly.PPoly × poly.PPoly)) (fun r => r.map profShift)
    rfl

/-- The shifted family's entries at a depth carry the family's own
caps at the successor depth. -/
private theorem capPfmShift (A : List (List (poly.PPoly × poly.PPoly)))
    (m K : Nat)
    (hA : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        (m + 1))).length ≤ K + 1) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmShift A) i) j) m)).length ≤ K + 1 := by
  intro i j
  rw [getAt_pfmShiftRows A i]
  match Nat.lt_or_ge j
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i).length with
  | Or.inr hge =>
    rw [ground.getAt_over vacProf _ j (by rw [ground.length_map]; exact hge)]
    exact Nat.zero_le _
  | Or.inl hj =>
    rw [ground.getAt_map vacProf vacProf profShift _ j hj]
    exact capCongr (depthPoly_profShift _ m) (hA i j)

/-- The swapped family's entries carry the family's own caps. -/
private theorem capPfmSwap (A : List (List (poly.PPoly × poly.PPoly)))
    (m K : Nat)
    (hA : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) A i) j)
        m)).length ≤ K + 1) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmSwap A) i) j) m)).length ≤ K + 1 := by
  intro i j
  rw [getAt_pfmSwap A i j]
  exact capCongr (depthPoly_profNeg _ m) (capNeg (hA i j))

/-- The two-armed sites' shared core: at a dominance certificate
walk whose site datum evaluates to a sum of two blocks symmetric at
the site's order, the evaluated form sits at or beyond the sum's
unit — the walk's comparison (`domCert_form`) closed at the
evaluated datum, the sum's exchange read carried by the summands'
own. -/
private theorem siteUnit (e0n : BPair) (e0d : Pos) (m N : Nat)
    (en ed : Pos) (S : List (List (poly.PPoly × poly.PPoly)))
    (gs : List BoxCert) (o : Nat) (P Q : elim.Mat) (ho : 0 < o)
    (hSl : S.length = o) (hSr : elim.rowsLen o S)
    (hPl : P.length = o) (hPr : elim.rowsLen o P)
    (hQl : Q.length = o) (hQr : elim.rowsLen o Q)
    (hEv : elim.matOneValue (evalPfm S m en ed N) (elim.matAdd P Q))
    (hsymP : elim.matOneValue (elim.transposeM P) P)
    (hsymQ : elim.matOneValue (elim.transposeM Q) Q)
    (hc : domCertGo e0n e0d 0 S gs)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (gs.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (N + 1))) = true) :
    ∀ u : List BPair, u.length = S.length →
      BPair.unit ≤ inertia.quadForm (evalPfm S m en ed N) u := by
  have hDr : elim.rowsLen o (elim.matAdd P Q) :=
    elim.rowsLen_matAdd o _ _ hPr hQr
  have hDl : (elim.matAdd P Q).length = o :=
    (elim.length_matAdd _ _ (by rw [hPl, hQl])).trans hPl
  have hEr : elim.rowsLen o (evalPfm S m en ed N) :=
    rowsLen_evalPfm o m S en ed N hSr
  have hEl : (evalPfm S m en ed N).length = o :=
    (length_evalPfm m S en ed N).trans hSl
  have hTPr : elim.rowsLen o (elim.transposeM P) := by
    have h := elim.rowsLen_transposeO ground.bpairOps P
    rw [hPl] at h
    exact h
  have hTQr : elim.rowsLen o (elim.transposeM Q) := by
    have h := elim.rowsLen_transposeO ground.bpairOps Q
    rw [hQl] at h
    exact h
  have hTD : elim.matOneValue (elim.transposeM (elim.matAdd P Q))
      (elim.matAdd P Q) := by
    rw [elim.transposeM_matAdd P Q hPr hQr (by rw [hPl, hQl])
      (by rw [hPl]; exact ho)]
    exact elim.matAdd_cong2 o _ _ _ _ hTPr hTQr hPr hQr hsymP hsymQ
  have hsymE : elim.matOneValue (evalPfm S m en ed N)
      (elim.transposeM (evalPfm S m en ed N)) :=
    elim.matOne_trans hEv
      (elim.matOne_symm
        (elim.matOne_trans
          (elim.transposeM_congrM o (evalPfm S m en ed N) _ hEr hDr
            (by rw [hEl, hDl]) hEv)
          hTD))
  have hsq : elim.sqAt (evalPfm S m en ed N) S.length :=
    elim.sqAt_of (length_evalPfm m S en ed N) (by rw [hSl]; exact hEr)
  exact domCert_form e0n e0d m N en ed S gs hc he hbox hsq hsymE

/-- The two-armed site's pointwise count: at a dominance certificate
walk whose site datum evaluates to a weighted block joined to a
second weighted block's memberwise swap, both blocks symmetric at
the site's order, the second block's weighted form sits at or below
the first's — `thm:decimation`(ii)'s price read through the form's
decomposition (`inertia.quadForm_add`, `quadForm_swap`,
`quadForm_scaleB`) and the sum's own comparison. -/
private theorem siteTwoArm (e0n : BPair) (e0d : Pos) (m N : Nat)
    (en ed : Pos) (S : List (List (poly.PPoly × poly.PPoly)))
    (gs : List BoxCert) (o : Nat) (X Y : elim.Mat) (w1 w2 : BPair)
    (hSl : S.length = o) (hSr : elim.rowsLen o S)
    (hXl : X.length = o) (hXr : elim.rowsLen o X)
    (hYl : Y.length = o) (hYr : elim.rowsLen o Y)
    (hEv : elim.matOneValue (evalPfm S m en ed N)
      (elim.matAdd (inertia.matScaleB w1 X)
        (elim.matSwap (inertia.matScaleB w2 Y))))
    (hsymX : elim.matOneValue (elim.transposeM X) X)
    (hsymY : elim.matOneValue (elim.transposeM Y) Y)
    (hc : domCertGo e0n e0d 0 S gs)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (gs.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (N + 1))) = true) :
    ∀ u : List BPair, u.length = o →
      w2 * inertia.quadForm Y u ≤ w1 * inertia.quadForm X u := by
  intro u hu
  cases u with
  | nil =>
    exact ground.leB_congr_left (BPair.oneValue_symm (BPair.mul_unit w2))
      (ground.leB_congr_right (BPair.oneValue_symm (BPair.mul_unit w1))
        (ground.leB_refl BPair.unit))
  | cons a t =>
    have ho : 0 < o := by rw [← hu]; exact Nat.succ_pos _
    have hXs : elim.rowsLen o (inertia.matScaleB w1 X) :=
      inertia.rowsLen_scaleB w1 o X hXr
    have hXsl : (inertia.matScaleB w1 X).length = o :=
      (inertia.length_scaleB w1 X).trans hXl
    have hYs : elim.rowsLen o (elim.matSwap (inertia.matScaleB w2 Y)) :=
      elim.rowsLen_mapRows BPair.swap (inertia.matScaleB w2 Y) o
        (inertia.rowsLen_scaleB w2 o Y hYr)
    have hYsl : (elim.matSwap (inertia.matScaleB w2 Y)).length = o :=
      (elim.length_matSwap (inertia.matScaleB w2 Y)).trans
        ((inertia.length_scaleB w2 Y).trans hYl)
    have hTX : elim.matOneValue
        (elim.transposeM (inertia.matScaleB w1 X))
        (inertia.matScaleB w1 X) :=
      elim.matOne_trans (inertia.transposeM_scaleB w1 o X hXr)
        (inertia.matOne_scaleB w1 hsymX)
    have hTY : elim.matOneValue
        (elim.transposeM (elim.matSwap (inertia.matScaleB w2 Y)))
        (elim.matSwap (inertia.matScaleB w2 Y)) := by
      rw [elim.transposeM_swap (inertia.matScaleB w2 Y)]
      exact elim.matSwap_congr
        (elim.matOne_trans (inertia.transposeM_scaleB w2 o Y hYr)
          (inertia.matOne_scaleB w2 hsymY))
    have hpos : BPair.unit
        ≤ inertia.quadForm (evalPfm S m en ed N) (a :: t) :=
      siteUnit e0n e0d m N en ed S gs o _ _ ho hSl hSr
        hXsl hXs hYsl hYs hEv hTX hTY hc he hbox (a :: t)
        (by rw [hSl]; exact hu)
    have hq : (inertia.quadForm (evalPfm S m en ed N) (a :: t)).oneValue
        (w1 * inertia.quadForm X (a :: t)
          + (w2 * inertia.quadForm Y (a :: t)).swap) :=
      BPair.oneValue_trans
        (inertia.quadMatOne _ _ (a :: t) hEv)
        (BPair.oneValue_trans
          (inertia.quadForm_add (inertia.matScaleB w1 X)
            (elim.matSwap (inertia.matScaleB w2 Y)) (a :: t)
            (by rw [hXsl, hu]) (by rw [hu]; exact hXs)
            (by rw [hYsl, hu]) (by rw [hu]; exact hYs))
          (BPair.add_congr
            (inertia.quadForm_scaleB w1 X (a :: t))
            (BPair.oneValue_trans
              (inertia.quadForm_swap (inertia.matScaleB w2 Y) (a :: t))
              (ground.swap_congr
                (inertia.quadForm_scaleB w2 Y (a :: t))))))
    have hsum : BPair.unit ≤ w1 * inertia.quadForm X (a :: t)
        + (w2 * inertia.quadForm Y (a :: t)).swap :=
      ground.leB_congr_right hq hpos
    have hfin := ground.leB_of_unit_add hsum
    rw [BPair.swap_swap] at hfin
    exact hfin

/-- A profile pair against a constant profile, evaluated at the
doubled clearing power against a further coefficient: the two
profiles' collapses at the shared power with the constants riding
outside. -/
private theorem evalMulPairConst (f g : poly.PPoly × poly.PPoly)
    (x c : BPair) (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1)
    (hg : (poly.vnorm (depthPoly g m)).length ≤ K + 1) :
    (evalProf (profMul (profMul (profMul f g) (constProf x))
        (constProf c)) m en ed (K + K)).oneValue
      (((evalProf f m en ed K * evalProf g m en ed K) * x) * c) := by
  have cXp : (poly.vnorm (depthPoly (constProf x) m)).length ≤ 0 + 1 :=
    poly.capOfLen (Nat.le_of_eq (depthConst_len x m))
  have cR : (poly.vnorm (depthPoly (constProf c) m)).length ≤ 0 + 1 :=
    poly.capOfLen (Nat.le_of_eq (depthConst_len c m))
  have cPQ : (poly.vnorm (poly.mul (depthPoly f m) (depthPoly g m))).length
      ≤ K + K + 1 := capMul hf hg
  have cPQX : (poly.vnorm (poly.mul
      (poly.mul (depthPoly f m) (depthPoly g m))
      (depthPoly (constProf x) m))).length ≤ K + K + 1 := by
    have h := capMul cPQ cXp
    rw [Nat.add_zero] at h
    exact h
  have hcol : poly.oneValue
      (depthPoly (profMul (profMul (profMul f g) (constProf x))
        (constProf c)) m)
      (poly.mul (poly.mul (poly.mul (depthPoly f m) (depthPoly g m))
        (depthPoly (constProf x) m)) (depthPoly (constProf c) m)) :=
    poly.oneValue_trans
      (depthPoly_profMul (profMul (profMul f g) (constProf x))
        (constProf c) m)
      (poly.mul_congr_left
        (poly.oneValue_trans
          (depthPoly_profMul (profMul f g) (constProf x) m)
          (poly.mul_congr_left (depthPoly_profMul f g m)
            (depthPoly (constProf x) m)))
        (depthPoly (constProf c) m))
  have hmid : (poly.evalClear (poly.mul
      (poly.mul (depthPoly f m) (depthPoly g m))
      (depthPoly (constProf x) m)) (BPair.ofPos en) ed (K + K)).oneValue
      ((evalProf f m en ed K * evalProf g m en ed K)
        * evalProf (constProf x) m en ed 0) := by
    have h := poly.evalClear_mulCap (poly.mul (depthPoly f m) (depthPoly g m))
      (depthPoly (constProf x) m) (BPair.ofPos en) ed (K + K) 0 cPQ cXp
    rw [Nat.add_zero] at h
    exact BPair.oneValue_trans h
      (BPair.mul_congr
        (poly.evalClear_mulCap (depthPoly f m) (depthPoly g m) (BPair.ofPos en)
          ed K K hf hg)
        (BPair.oneValue_refl _))
  have houter := poly.evalClear_mulCap
    (poly.mul (poly.mul (depthPoly f m) (depthPoly g m))
      (depthPoly (constProf x) m)) (depthPoly (constProf c) m)
    (BPair.ofPos en) ed (K + K) 0 cPQX cR
  rw [Nat.add_zero] at houter
  refine BPair.oneValue_trans
    (poly.evalClear_congr hcol (BPair.ofPos en) ed (K + K)) ?_
  refine BPair.oneValue_trans houter ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr hmid (evalProf_const c m en ed 0)) ?_
  exact BPair.mul_congr
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (evalProf_const x m en ed 0)
        (mulBpowZero ed x)))
    (mulBpowZero ed c)

/-- One row of the constant family rescaled at a profile pair
against a constant profile. -/
private theorem evalScalePairRow (f g : poly.PPoly × poly.PPoly)
    (x : BPair) (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1)
    (hg : (poly.vnorm (depthPoly g m)).length ≤ K + 1) :
    ∀ r : List BPair,
      poly.oneValue
        (((r.map constProf).map
          (profMul (profMul (profMul f g) (constProf x)))).map
          (fun e => evalProf e m en ed (K + K)))
        (poly.scaleP
          ((evalProf f m en ed K * evalProf g m en ed K) * x) r)
  | [] => trivial
  | c :: r =>
    ⟨BPair.oneValue_trans (evalMulPairConst f g x c m en ed K hf hg)
      (BPair.oneValue_symm (BPair.norm_oneValue _)),
     evalScalePairRow f g x m en ed K hf hg r⟩

/-- The constant family rescaled at a profile pair against a
constant profile, evaluated row by row. -/
private theorem evalScalePairGo (f g : poly.PPoly × poly.PPoly)
    (x : BPair) (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1)
    (hg : (poly.vnorm (depthPoly g m)).length ≤ K + 1) :
    ∀ X : elim.Mat,
      elim.matOneValue
        ((pfmScale (profMul (profMul f g) (constProf x))
          (ofMatProf X)).map
          (fun r => r.map (fun e => evalProf e m en ed (K + K))))
        (inertia.matScaleB
          ((evalProf f m en ed K * evalProf g m en ed K) * x) X)
  | [] => trivial
  | r :: X =>
    ⟨evalScalePairRow f g x m en ed K hf hg r,
     evalScalePairGo f g x m en ed K hf hg X⟩

/-- The constant family rescaled at a profile pair against a
constant profile: the stated matrix weighted by the two collapses
and the constant. -/
private theorem evalScalePair (f g : poly.PPoly × poly.PPoly) (x : BPair)
    (X : elim.Mat) (m : Nat) (en ed : Pos) (K : Nat)
    (hf : (poly.vnorm (depthPoly f m)).length ≤ K + 1)
    (hg : (poly.vnorm (depthPoly g m)).length ≤ K + 1) :
    elim.matOneValue
      (evalPfm (pfmScale (profMul (profMul f g) (constProf x))
        (ofMatProf X)) m en ed (K + K))
      (inertia.matScaleB
        ((evalProf f m en ed K * evalProf g m en ed K) * x) X) := by
  rw [evalPfm_rows m en ed (K + K)
    (pfmScale (profMul (profMul f g) (constProf x)) (ofMatProf X))]
  exact evalScalePairGo f g x m en ed K hf hg X

/-- The two-armed site's pointwise count at an unswapped second
arm: at a dominance certificate walk whose site datum evaluates to
two weighted blocks joined, both symmetric at the site's order, the
first block's weighted form's balance partner sits at or below the
second's — `thm:decimation`(ii)'s price read through the form's
decomposition and the sum's own comparison at the commuted order. -/
private theorem siteTwoArmLo (e0n : BPair) (e0d : Pos) (m N : Nat)
    (en ed : Pos) (S : List (List (poly.PPoly × poly.PPoly)))
    (gs : List BoxCert) (o : Nat) (X Y : elim.Mat) (w1 w2 : BPair)
    (hSl : S.length = o) (hSr : elim.rowsLen o S)
    (hXl : X.length = o) (hXr : elim.rowsLen o X)
    (hYl : Y.length = o) (hYr : elim.rowsLen o Y)
    (hEv : elim.matOneValue (evalPfm S m en ed N)
      (elim.matAdd (inertia.matScaleB w1 X) (inertia.matScaleB w2 Y)))
    (hsymX : elim.matOneValue (elim.transposeM X) X)
    (hsymY : elim.matOneValue (elim.transposeM Y) Y)
    (hc : domCertGo e0n e0d 0 S gs)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (gs.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (N + 1))) = true) :
    ∀ u : List BPair, u.length = o →
      (w1 * inertia.quadForm X u).swap ≤ w2 * inertia.quadForm Y u := by
  intro u hu
  cases u with
  | nil =>
    refine ground.leB_congr_left
      (ground.swap_congr (BPair.oneValue_symm (BPair.mul_unit w1))) ?_
    exact ground.leB_congr_right
      (BPair.oneValue_symm (BPair.mul_unit w2)) (ground.leB_refl BPair.unit)
  | cons a t =>
    have ho : 0 < o := by rw [← hu]; exact Nat.succ_pos _
    have hXs : elim.rowsLen o (inertia.matScaleB w1 X) :=
      inertia.rowsLen_scaleB w1 o X hXr
    have hXsl : (inertia.matScaleB w1 X).length = o :=
      (inertia.length_scaleB w1 X).trans hXl
    have hYs : elim.rowsLen o (inertia.matScaleB w2 Y) :=
      inertia.rowsLen_scaleB w2 o Y hYr
    have hYsl : (inertia.matScaleB w2 Y).length = o :=
      (inertia.length_scaleB w2 Y).trans hYl
    have hTX : elim.matOneValue
        (elim.transposeM (inertia.matScaleB w1 X))
        (inertia.matScaleB w1 X) :=
      elim.matOne_trans (inertia.transposeM_scaleB w1 o X hXr)
        (inertia.matOne_scaleB w1 hsymX)
    have hTY : elim.matOneValue
        (elim.transposeM (inertia.matScaleB w2 Y))
        (inertia.matScaleB w2 Y) :=
      elim.matOne_trans (inertia.transposeM_scaleB w2 o Y hYr)
        (inertia.matOne_scaleB w2 hsymY)
    have hpos : BPair.unit
        ≤ inertia.quadForm (evalPfm S m en ed N) (a :: t) :=
      siteUnit e0n e0d m N en ed S gs o _ _ ho hSl hSr
        hXsl hXs hYsl hYs hEv hTX hTY hc he hbox (a :: t)
        (by rw [hSl]; exact hu)
    have hq : (inertia.quadForm (evalPfm S m en ed N) (a :: t)).oneValue
        (w1 * inertia.quadForm X (a :: t)
          + w2 * inertia.quadForm Y (a :: t)) :=
      BPair.oneValue_trans
        (inertia.quadMatOne _ _ (a :: t) hEv)
        (BPair.oneValue_trans
          (inertia.quadForm_add (inertia.matScaleB w1 X)
            (inertia.matScaleB w2 Y) (a :: t)
            (by rw [hXsl, hu]) (by rw [hu]; exact hXs)
            (by rw [hYsl, hu]) (by rw [hu]; exact hYs))
          (BPair.add_congr
            (inertia.quadForm_scaleB w1 X (a :: t))
            (inertia.quadForm_scaleB w2 Y (a :: t))))
    have hsum : BPair.unit ≤ w2 * inertia.quadForm Y (a :: t)
        + w1 * inertia.quadForm X (a :: t) := by
      rw [BPair.add_comm (w2 * inertia.quadForm Y (a :: t))
        (w1 * inertia.quadForm X (a :: t))]
      exact ground.leB_congr_right hq hpos
    exact ground.leB_of_unit_add hsum

/-- The center defect's entries carry the image's and the center's
caps added. -/
private theorem devCaps (Cf If : PfMQ) (m K : Nat)
    (hshI : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) If.1 i) j)
        m)).length ≤ K + 1)
    (hshIcl : (poly.vnorm (depthPoly If.2 m)).length ≤ K + 1)
    (hshC : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Cf.1 i) j)
        m)).length ≤ K + 1)
    (hshCl : (poly.vnorm (depthPoly Cf.2 m)).length ≤ K + 1) :
    ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (devFam Cf If).1 i) j) m)).length ≤ K + K + 1 :=
  capPfmAdd m (K + K) _ _
    (capPfmScale Cf.2 If.1 m K K hshCl hshI)
    (capPfmScale If.2 (pfmSwap Cf.1) m K K
      hshIcl
      (capPfmSwap Cf.1 m K hshC))

/-- The center defect's evaluated datum: the image weighted by the
center clearing's collapse joined to the center's swap weighted by
the image's own, both at the shared clearing power. -/
private theorem devEval (Cf If : PfMQ) (o : Nat)
    (m K : Nat) (en ed : Pos)
    (hIr : elim.rowsLen o If.1) (hCr : elim.rowsLen o Cf.1)
    (hshI : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) If.1 i) j)
        m)).length ≤ K + 1)
    (hshIcl : (poly.vnorm (depthPoly If.2 m)).length ≤ K + 1)
    (hshC : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Cf.1 i) j)
        m)).length ≤ K + 1)
    (hshCl : (poly.vnorm (depthPoly Cf.2 m)).length ≤ K + 1) :
    elim.matOneValue (evalPfm (devFam Cf If).1 m en ed (K + K))
      (elim.matAdd
        (inertia.matScaleB (evalProf Cf.2 m en ed K)
          (evalPfm If.1 m en ed K))
        (inertia.matScaleB (evalProf If.2 m en ed K)
          (elim.matSwap (evalPfm Cf.1 m en ed K)))) :=
  elim.matOne_trans (evalPfm_add _ _ m en ed (K + K))
    (elim.matAdd_cong2 o _ _ _ _
      (rowsLen_evalPfm o m _ en ed (K + K)
        (rowsLen_pfmScale _ o If.1 hIr))
      (rowsLen_evalPfm o m _ en ed (K + K)
        (rowsLen_pfmScale _ o _ (rowsLen_pfmSwap o _ hCr)))
      (inertia.rowsLen_scaleB _ o _ (rowsLen_evalPfm o m If.1 en ed K hIr))
      (inertia.rowsLen_scaleB _ o _
        (elim.rowsLen_mapRows BPair.swap _ o
          (rowsLen_evalPfm o m Cf.1 en ed K hCr)))
      (evalPfm_scale Cf.2 If.1 m en ed K K hshCl hshI)
      (elim.matOne_trans
        (evalPfm_scale If.2 (pfmSwap Cf.1) m en ed K K
          hshIcl
          (capPfmSwap Cf.1 m K hshC))
        (inertia.matOne_scaleB _ (evalPfm_swap Cf.1 m en ed K))))

/-- The center defect's family carries the site's order. -/
private theorem devLen (Cf If : PfMQ) (o : Nat)
    (hIl : If.1.length = o) (hCl : Cf.1.length = o) :
    (devFam Cf If).1.length = o := by
  have h1 : (pfmScale Cf.2 If.1).length = o := by
    rw [length_pfmScale]
    exact hIl
  have h2 : (pfmScale If.2 (pfmSwap Cf.1)).length = o := by
    rw [length_pfmScale, length_pfmSwap]
    exact hCl
  show (pfmAdd (pfmScale Cf.2 If.1)
      (pfmScale If.2 (pfmSwap Cf.1))).length = o
  rw [length_pfmAdd _ _ (h1.trans h2.symm)]
  exact h1

/-- The center defect's family carries the site's row width. -/
private theorem devRows (Cf If : PfMQ) (o : Nat)
    (hIr : elim.rowsLen o If.1) (hCr : elim.rowsLen o Cf.1) :
    elim.rowsLen o (devFam Cf If).1 :=
  rowsLen_pfmAdd o _ _ (rowsLen_pfmScale _ o If.1 hIr)
    (rowsLen_pfmScale _ o _ (rowsLen_pfmSwap o _ hCr))

/-- The evaluated center's exchange at every depth. -/
theorem evalSymOf (A : List (List (poly.PPoly × poly.PPoly)))
    (o m K : Nat) (en ed : Pos) (hl : A.length = o)
    (hr : elim.rowsLen o A) (h : pfmOneValue (pfmTr A) A) :
    elim.matOneValue (elim.transposeM (evalPfm A m en ed K))
      (evalPfm A m en ed K) :=
  elim.matOne_trans
    (elim.matOne_symm (evalPfm_tr A m en ed K o hl hr))
    (evalPfm_congr (pfmTr A) A m en ed K h)

/-- The center defect's evaluated datum keeps the exchange: the
image's own and the center's ride the weighting and the memberwise
swap. -/
private theorem devSym (Cf If : PfMQ) (o m K : Nat) (en ed : Pos)
    (cSh cIf : BPair)
    (hIl : If.1.length = o) (hIr : elim.rowsLen o If.1)
    (hCl : Cf.1.length = o) (hCr : elim.rowsLen o Cf.1) (ho : 0 < o)
    (hsymC : pfmOneValue (pfmTr Cf.1) Cf.1)
    (hsymI : pfmOneValue (pfmTr If.1) If.1) :
    elim.matOneValue
      (elim.transposeM (elim.matAdd
        (inertia.matScaleB cSh (evalPfm If.1 m en ed K))
        (inertia.matScaleB cIf
          (elim.matSwap (evalPfm Cf.1 m en ed K)))))
      (elim.matAdd
        (inertia.matScaleB cSh (evalPfm If.1 m en ed K))
        (inertia.matScaleB cIf
          (elim.matSwap (evalPfm Cf.1 m en ed K)))) := by
  have hMIl : (evalPfm If.1 m en ed K).length = o :=
    (length_evalPfm m If.1 en ed K).trans hIl
  have hMIr : elim.rowsLen o (evalPfm If.1 m en ed K) :=
    rowsLen_evalPfm o m If.1 en ed K hIr
  have hMCl : (evalPfm Cf.1 m en ed K).length = o :=
    (length_evalPfm m Cf.1 en ed K).trans hCl
  have hMCr : elim.rowsLen o (evalPfm Cf.1 m en ed K) :=
    rowsLen_evalPfm o m Cf.1 en ed K hCr
  have hSCl : (elim.matSwap (evalPfm Cf.1 m en ed K)).length = o :=
    (elim.length_matSwap _).trans hMCl
  have hSCr : elim.rowsLen o (elim.matSwap (evalPfm Cf.1 m en ed K)) :=
    elim.rowsLen_mapRows BPair.swap _ o hMCr
  have hAl : (inertia.matScaleB cSh (evalPfm If.1 m en ed K)).length = o :=
    (inertia.length_scaleB _ _).trans hMIl
  have hAr : elim.rowsLen o (inertia.matScaleB cSh (evalPfm If.1 m en ed K)) :=
    inertia.rowsLen_scaleB _ o _ hMIr
  have hBl : (inertia.matScaleB cIf
      (elim.matSwap (evalPfm Cf.1 m en ed K))).length = o :=
    (inertia.length_scaleB _ _).trans hSCl
  have hBr : elim.rowsLen o (inertia.matScaleB cIf
      (elim.matSwap (evalPfm Cf.1 m en ed K))) :=
    inertia.rowsLen_scaleB _ o _ hSCr
  have hTAr : elim.rowsLen o (elim.transposeM
      (inertia.matScaleB cSh (evalPfm If.1 m en ed K))) := by
    have h := elim.rowsLen_transposeO ground.bpairOps
      (inertia.matScaleB cSh (evalPfm If.1 m en ed K))
    rw [hAl] at h
    exact h
  have hTBr : elim.rowsLen o (elim.transposeM (inertia.matScaleB cIf
      (elim.matSwap (evalPfm Cf.1 m en ed K)))) := by
    have h := elim.rowsLen_transposeO ground.bpairOps
      (inertia.matScaleB cIf (elim.matSwap (evalPfm Cf.1 m en ed K)))
    rw [hBl] at h
    exact h
  rw [elim.transposeM_matAdd (inertia.matScaleB cSh (evalPfm If.1 m en ed K))
    (inertia.matScaleB cIf (elim.matSwap (evalPfm Cf.1 m en ed K)))
    hAr hBr (by rw [hAl, hBl]) (by rw [hAl]; exact ho)]
  refine elim.matAdd_cong2 o _ _ _ _ hTAr hTBr hAr hBr ?_ ?_
  · exact elim.matOne_trans (inertia.transposeM_scaleB cSh o _ hMIr)
      (inertia.matOne_scaleB cSh
        (evalSymOf If.1 o m K en ed hIl hIr hsymI))
  · refine elim.matOne_trans (inertia.transposeM_scaleB cIf o _ hSCr) ?_
    refine inertia.matOne_scaleB cIf ?_
    rw [elim.transposeM_swap (evalPfm Cf.1 m en ed K)]
    exact elim.matSwap_congr
      (evalSymOf Cf.1 o m K en ed hCl hCr hsymC)

/-- The defect site's second arm's evaluated datum: the defect
cleared at the cap denominator. -/
private theorem dcapArm2 (Cf If : PfMQ) (o : Nat) (r0d : Pos)
    (m K : Nat) (en ed : Pos)
    (hIr : elim.rowsLen o If.1) (hCr : elim.rowsLen o Cf.1)
    (hshI : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) If.1 i) j)
        m)).length ≤ K + 1)
    (hshIcl : (poly.vnorm (depthPoly If.2 m)).length ≤ K + 1)
    (hshC : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Cf.1 i) j)
        m)).length ≤ K + 1)
    (hshCl : (poly.vnorm (depthPoly Cf.2 m)).length ≤ K + 1) :
    elim.matOneValue
      (evalPfm (pfmScale (constProf (BPair.ofPos r0d)) (devFam Cf If).1)
        m en ed (K + K))
      (inertia.matScaleB
        (evalProf (constProf (BPair.ofPos r0d)) m en ed 0)
        (elim.matAdd
          (inertia.matScaleB (evalProf Cf.2 m en ed K)
            (evalPfm If.1 m en ed K))
          (inertia.matScaleB (evalProf If.2 m en ed K)
            (elim.matSwap (evalPfm Cf.1 m en ed K))))) := by
  have h := evalPfm_scale (constProf (BPair.ofPos r0d))
    (devFam Cf If).1 m en ed 0 (K + K)
    (poly.capOfLen (Nat.le_of_eq (depthConst_len (BPair.ofPos r0d) m)))
    (devCaps Cf If m K hshI hshIcl hshC hshCl)
  rw [Nat.zero_add] at h
  exact elim.matOne_trans h
    (inertia.matOne_scaleB _
      (devEval Cf If o m K en ed hIr hCr hshI hshIcl hshC hshCl))

/-- The defect datum's two spellings: the cleared matrix datum's own
sum against the evaluated clearings' weighting. -/
private theorem devBridge (Cf If : PfMQ) (o m K : Nat) (en ed : Pos)
    (cI cC : Pos)
    (hIr : elim.rowsLen o If.1) (hCr : elim.rowsLen o Cf.1)
    (hcI : (BPair.ofPos cI).oneValue (evalProf If.2 m en ed K))
    (hcC : (BPair.ofPos cC).oneValue
      (evalProf Cf.2 m en ed K)) :
    elim.matOneValue
      (elim.matAdd (inertia.matScale cC (evalPfm If.1 m en ed K))
        (inertia.matScale cI
          (elim.matSwap (evalPfm Cf.1 m en ed K))))
      (elim.matAdd
        (inertia.matScaleB (evalProf Cf.2 m en ed K)
          (evalPfm If.1 m en ed K))
        (inertia.matScaleB (evalProf If.2 m en ed K)
          (elim.matSwap (evalPfm Cf.1 m en ed K)))) := by
  have hMIr : elim.rowsLen o (evalPfm If.1 m en ed K) :=
    rowsLen_evalPfm o m If.1 en ed K hIr
  have hSCr : elim.rowsLen o (elim.matSwap (evalPfm Cf.1 m en ed K)) :=
    elim.rowsLen_mapRows BPair.swap _ o
      (rowsLen_evalPfm o m Cf.1 en ed K hCr)
  refine elim.matAdd_cong2 o _ _ _ _
    (elim.rowsLen_mapRows (fun x => x.scale cC) _ o hMIr)
    (elim.rowsLen_mapRows (fun x => x.scale cI) _ o hSCr)
    (inertia.rowsLen_scaleB _ o _ hMIr)
    (inertia.rowsLen_scaleB _ o _ hSCr) ?_ ?_
  · exact elim.matOne_trans (inertia.matScale_scaleB cC _)
      (inertia.matScaleB_congr hcC _)
  · exact elim.matOne_trans (inertia.matScale_scaleB cI _)
      (inertia.matScaleB_congr hcI _)

/-- `lem:cornerblock`'s floor count at the evaluated data: at a
dominance certificate walk over the center's floor site datum, with
the center's exchange and the gram's own, the center's evaluated
form prices the gram's at the floor and radius numerators' cross-sum
against the denominators' product, the center's clearing entering at
its stated margin — `lem:spectator`(iii)'s floor comparison read
pointwise at every vector of the site's order. -/
theorem floorCount_ptw (Cf : PfMQ) (G : elim.Mat) (o : Nat)
    (y0n y0d rn rd : Pos) (e0n : BPair) (e0d : Pos)
    (bxF : List BoxCert) (m K : Nat) (en ed : Pos) (cC : Pos)
    (hCl : Cf.1.length = o) (hCr : elim.rowsLen o Cf.1)
    (hGq : elim.sqAt G o)
    (hsymC : pfmOneValue (pfmTr Cf.1) Cf.1)
    (hsymG : elim.matOneValue (elim.transposeM G) G)
    (hshC : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Cf.1 i) j)
        m)).length ≤ K + 1)
    (hshCl : (poly.vnorm (depthPoly Cf.2 m)).length ≤ K + 1)
    (hwalk : domCertGo e0n e0d 0 (floorSiteF Cf G y0n y0d rn rd) bxF)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (bxF.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (K + K + 1))) = true)
    (hcC : (BPair.ofPos cC).oneValue (evalProf Cf.2 m en ed K)) :
    ∀ u : List BPair, u.length = o →
      (inertia.quadForm G u).scale (cC * (y0n * rd + rn * y0d))
        ≤ (inertia.quadForm (evalPfm Cf.1 m en ed K) u).scale
            (y0d * rd) := by
  intro u hu
  have hGl : G.length = o := elim.sqAt_len hGq
  have hGr : elim.rowsLen o G := elim.rowsLen_of_sqAt hGq
  have hCstLen : (depthPoly (constProf (BPair.ofPos (y0d * rd))) m).length
      ≤ K + 1 := by
    rw [depthConst_len]
    exact Nat.succ_le_succ (Nat.zero_le K)
  have hMCl : (evalPfm Cf.1 m en ed K).length = o :=
    (length_evalPfm m Cf.1 en ed K).trans hCl
  have hMCr : elim.rowsLen o (evalPfm Cf.1 m en ed K) :=
    rowsLen_evalPfm o m Cf.1 en ed K hCr
  have hsymMC : elim.matOneValue
      (elim.transposeM (evalPfm Cf.1 m en ed K)) (evalPfm Cf.1 m en ed K) :=
    elim.matOne_trans
      (elim.matOne_symm (evalPfm_tr Cf.1 m en ed K o hCl hCr))
      (evalPfm_congr (pfmTr Cf.1) Cf.1 m en ed K hsymC)
  have h1l : (pfmScale (constProf (BPair.ofPos (y0d * rd))) Cf.1).length = o :=
    (length_pfmScale _ Cf.1).trans hCl
  have h1r : elim.rowsLen o
      (pfmScale (constProf (BPair.ofPos (y0d * rd))) Cf.1) :=
    rowsLen_pfmScale _ o Cf.1 hCr
  have h2l : (pfmSwap (pfmScale
      (profMul Cf.2 (constProf (BPair.ofPos (y0n * rd + rn * y0d))))
      (ofMatProf G))).length = o :=
    (length_pfmSwap _).trans
      ((length_pfmScale _ (ofMatProf G)).trans
        ((length_ofMatProf G).trans hGl))
  have h2r : elim.rowsLen o (pfmSwap (pfmScale
      (profMul Cf.2 (constProf (BPair.ofPos (y0n * rd + rn * y0d))))
      (ofMatProf G))) :=
    rowsLen_pfmSwap o _
      (rowsLen_pfmScale _ o (ofMatProf G) (rowsLen_ofMatProf o G hGr))
  have hSl : (floorSiteF Cf G y0n y0d rn rd).length = o :=
    (length_pfmAdd _ _ (by rw [h1l, h2l])).trans h1l
  have hSr : elim.rowsLen o (floorSiteF Cf G y0n y0d rn rd) :=
    rowsLen_pfmAdd o _ _ h1r h2r
  have hev1 : elim.matOneValue
      (evalPfm (pfmScale (constProf (BPair.ofPos (y0d * rd))) Cf.1)
        m en ed (K + K))
      (inertia.matScaleB
        (evalProf (constProf (BPair.ofPos (y0d * rd))) m en ed K)
        (evalPfm Cf.1 m en ed K)) :=
    evalPfm_scale (constProf (BPair.ofPos (y0d * rd))) Cf.1 m en ed K K
      (poly.capOfLen hCstLen) hshC
  have hev2 : elim.matOneValue
      (evalPfm (pfmSwap (pfmScale
        (profMul Cf.2 (constProf (BPair.ofPos (y0n * rd + rn * y0d))))
        (ofMatProf G))) m en ed (K + K))
      (elim.matSwap (inertia.matScaleB
        (evalProf Cf.2 m en ed K * BPair.ofPos (y0n * rd + rn * y0d)
          * ground.bpow (BPair.ofPos ed) K) G)) :=
    elim.matOne_trans (evalPfm_swap _ m en ed (K + K))
      (elim.matSwap_congr
        (evalScaleOfMat Cf.2 (BPair.ofPos (y0n * rd + rn * y0d)) G
          m en ed K hshCl))
  have hEv : elim.matOneValue
      (evalPfm (floorSiteF Cf G y0n y0d rn rd) m en ed (K + K))
      (elim.matAdd
        (inertia.matScaleB
          (evalProf (constProf (BPair.ofPos (y0d * rd))) m en ed K)
          (evalPfm Cf.1 m en ed K))
        (elim.matSwap (inertia.matScaleB
          (evalProf Cf.2 m en ed K * BPair.ofPos (y0n * rd + rn * y0d)
            * ground.bpow (BPair.ofPos ed) K) G))) :=
    elim.matOne_trans (evalPfm_add _ _ m en ed (K + K))
      (elim.matAdd_cong2 o _ _ _ _
        (rowsLen_evalPfm o m _ en ed (K + K) h1r)
        (rowsLen_evalPfm o m _ en ed (K + K) h2r)
        (inertia.rowsLen_scaleB _ o _ hMCr)
        (elim.rowsLen_mapRows BPair.swap _ o
          (inertia.rowsLen_scaleB _ o G hGr))
        hev1 hev2)
  have hcmp := siteTwoArm e0n e0d m (K + K) en ed
    (floorSiteF Cf G y0n y0d rn rd) bxF o (evalPfm Cf.1 m en ed K) G
    (evalProf (constProf (BPair.ofPos (y0d * rd))) m en ed K)
    (evalProf Cf.2 m en ed K * BPair.ofPos (y0n * rd + rn * y0d)
      * ground.bpow (BPair.ofPos ed) K)
    hSl hSr hMCl hMCr hGl hGr hEv hsymMC hsymG hwalk he hbox u hu
  have hstep1 : (evalProf Cf.2 m en ed K
      * BPair.ofPos (y0n * rd + rn * y0d)
      * ground.bpow (BPair.ofPos ed) K) * inertia.quadForm G u
      ≤ (BPair.ofPos (y0d * rd) * ground.bpow (BPair.ofPos ed) K)
        * inertia.quadForm (evalPfm Cf.1 m en ed K) u :=
    ground.leB_congr_right
      (BPair.mul_congr (evalProf_const (BPair.ofPos (y0d * rd)) m en ed K)
        (BPair.oneValue_refl _)) hcmp
  have hstep2 : (BPair.ofPos cC * BPair.ofPos (y0n * rd + rn * y0d)
      * ground.bpow (BPair.ofPos ed) K) * inertia.quadForm G u
      ≤ (BPair.ofPos (y0d * rd) * ground.bpow (BPair.ofPos ed) K)
        * inertia.quadForm (evalPfm Cf.1 m en ed K) u :=
    ground.leB_congr_left
      (BPair.mul_congr
        (BPair.mul_congr
          (BPair.mul_congr (BPair.oneValue_symm hcC) (BPair.oneValue_refl _))
          (BPair.oneValue_refl _))
        (BPair.oneValue_refl _)) hstep1
  have hL : (BPair.ofPos cC * BPair.ofPos (y0n * rd + rn * y0d)
      * ground.bpow (BPair.ofPos ed) K) * inertia.quadForm G u
      = (BPair.ofPos cC * BPair.ofPos (y0n * rd + rn * y0d)
          * inertia.quadForm G u) * ground.bpow (BPair.ofPos ed) K := by
    rw [BPair.mul_assoc, BPair.mul_comm (ground.bpow (BPair.ofPos ed) K)
      (inertia.quadForm G u), ← BPair.mul_assoc]
  have hR : (BPair.ofPos (y0d * rd) * ground.bpow (BPair.ofPos ed) K)
      * inertia.quadForm (evalPfm Cf.1 m en ed K) u
      = (BPair.ofPos (y0d * rd)
          * inertia.quadForm (evalPfm Cf.1 m en ed K) u)
        * ground.bpow (BPair.ofPos ed) K := by
    rw [BPair.mul_assoc, BPair.mul_comm (ground.bpow (BPair.ofPos ed) K)
      (inertia.quadForm (evalPfm Cf.1 m en ed K) u), ← BPair.mul_assoc]
  rw [hL, hR] at hstep2
  have hstep3 := ground.leB_unscale
    (ground.unitLtBpow (ground.unitLtOfPos ed) K) hstep2
  refine ground.leB_congr_left
    (BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofPos_mul cC (y0n * rd + rn * y0d)))
      (BPair.ofPos_scale (cC * (y0n * rd + rn * y0d))
        (inertia.quadForm G u))) ?_
  exact ground.leB_congr_right
    (BPair.ofPos_scale (y0d * rd)
      (inertia.quadForm (evalPfm Cf.1 m en ed K) u)) hstep3

/-- The exchanged family's row count at a stated order. -/
private theorem length_pfmTr (A : List (List (poly.PPoly × poly.PPoly)))
    (o : Nat) (hl : A.length = o) (hr : elim.rowsLen o A) (ho : 0 < o) :
    (pfmTr A).length = o :=
  elim.length_transposeO profOps A hr (by rw [hl]; exact ho)

/-- `lem:cornerblock`'s contraction count at the evaluated
data: at a dominance certificate walk over the transfer factor's
contraction site datum, with the gram's exchange, the transferred
vector's form at the factor's denominator square sits at or below
the gram's own at the numerator square and the factor's clearing
squared — `lem:spectator`(iii)'s contraction comparison read
pointwise at every vector of the site's order. -/
theorem contrCount_ptw (Wf : PfMQ) (G : elim.Mat) (o : Nat)
    (ln ld : Pos) (e0n : BPair) (e0d : Pos)
    (bxC : List BoxCert) (m K : Nat) (en ed : Pos) (cW : Pos)
    (hWl : Wf.1.length = o) (hWr : elim.rowsLen o Wf.1)
    (hGq : elim.sqAt G o)
    (hsymG : elim.matOneValue (elim.transposeM G) G)
    (hshW : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Wf.1 i) j)
        m)).length ≤ K + 1)
    (hshWcl : (poly.vnorm (depthPoly Wf.2 m)).length ≤ K + 1)
    (hwalk : domCertGo e0n e0d 0 (contrSiteF Wf G ln ld) bxC)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (bxC.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (K + K + 1))) = true)
    (hcW : (BPair.ofPos cW).oneValue (evalProf Wf.2 m en ed K)) :
    ∀ u : List BPair, u.length = o →
      (inertia.quadForm G
        (elim.matVec (elim.matSwap (evalPfm Wf.1 m en ed K)) u)).scale
          (ld * ld)
        ≤ (inertia.quadForm G u).scale (ln * ln * (cW * cW)) := by
  intro u hu
  cases u with
  | nil =>
    have hW0 : Wf.1 = [] :=
      ground.nil_of_length_zero Wf.1 (hWl.trans hu.symm)
    rw [hW0]
    exact ground.leB_congr_left (ground.unitScale _)
      (ground.leB_congr_right (ground.unitScale _)
        (ground.leB_refl BPair.unit))
  | cons a t =>
    have ho : 0 < o := by rw [← hu]; exact Nat.succ_pos _
    have hGl : G.length = o := elim.sqAt_len hGq
    have hGr : elim.rowsLen o G := elim.rowsLen_of_sqAt hGq
    have hMWl : (evalPfm Wf.1 m en ed K).length = o :=
      (length_evalPfm m Wf.1 en ed K).trans hWl
    have hMWr : elim.rowsLen o (evalPfm Wf.1 m en ed K) :=
      rowsLen_evalPfm o m Wf.1 en ed K hWr
    have hSWl : (elim.matSwap (evalPfm Wf.1 m en ed K)).length = o :=
      (elim.length_matSwap _).trans hMWl
    have hSWr : elim.rowsLen o (elim.matSwap (evalPfm Wf.1 m en ed K)) :=
      elim.rowsLen_mapRows BPair.swap _ o hMWr
    -- the swapped and exchanged profile families
    have hSwl : (pfmSwap Wf.1).length = o := (length_pfmSwap Wf.1).trans hWl
    have hSwr : elim.rowsLen o (pfmSwap Wf.1) := rowsLen_pfmSwap o Wf.1 hWr
    have hTrl : (pfmTr (pfmSwap Wf.1)).length = o :=
      length_pfmTr (pfmSwap Wf.1) o hSwl hSwr ho
    have hTrr : elim.rowsLen o (pfmTr (pfmSwap Wf.1)) := by
      have h := elim.rowsLen_transposeO profOps (pfmSwap Wf.1)
      rw [hSwl] at h
      exact h
    have hOMl : (ofMatProf G).length = o := (length_ofMatProf G).trans hGl
    have hOMr : elim.rowsLen o (ofMatProf G) := rowsLen_ofMatProf o G hGr
    have hBl : (pfmMul (ofMatProf G) (pfmSwap Wf.1)).length = o :=
      (ground.length_map _ (ofMatProf G)).trans hOMl
    have hBr : elim.rowsLen o (pfmMul (ofMatProf G) (pfmSwap Wf.1)) :=
      elim.rowsLen_matMulO profOps (ofMatProf G) (pfmSwap Wf.1) o
        (elim.headD_width o (pfmSwap Wf.1) (by rw [hSwl]; exact ho) hSwr)
    have hIl : (pfmMul (pfmTr (pfmSwap Wf.1))
        (pfmMul (ofMatProf G) (pfmSwap Wf.1))).length = o :=
      (ground.length_map _ (pfmTr (pfmSwap Wf.1))).trans hTrl
    have hIr : elim.rowsLen o (pfmMul (pfmTr (pfmSwap Wf.1))
        (pfmMul (ofMatProf G) (pfmSwap Wf.1))) :=
      elim.rowsLen_matMulO profOps (pfmTr (pfmSwap Wf.1))
        (pfmMul (ofMatProf G) (pfmSwap Wf.1)) o
        (elim.headD_width o (pfmMul (ofMatProf G) (pfmSwap Wf.1))
          (by rw [hBl]; exact ho) hBr)
    -- the entry reads of the two inner factors
    have hSwLen := capPfmSwap Wf.1 m K hshW
    have hTrLen := pfmTrEntryLen (pfmSwap Wf.1) o m K hSwl hSwr hSwLen
    have hBcap : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
          (pfmMul (ofMatProf G) (pfmSwap Wf.1)) i) j) m)).length ≤ K + 1 := by
      have h := capPfmMul (ofMatProf G) (pfmSwap Wf.1) m 0 K o o hOMr hSwl ho
        hSwr (fun i j => poly.capOfLen (ofMatEntryLen G m i j))
        hSwLen
      intro i j
      have hij := h i j
      rw [Nat.zero_add] at hij
      exact hij
    have hIcap : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
        (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
          (pfmMul (pfmTr (pfmSwap Wf.1))
            (pfmMul (ofMatProf G) (pfmSwap Wf.1))) i) j) m)).length
        ≤ K + K + 1 :=
      capPfmMul (pfmTr (pfmSwap Wf.1))
        (pfmMul (ofMatProf G) (pfmSwap Wf.1)) m K K o o hTrr hBl ho hBr
        hTrLen hBcap
    -- the inner product's evaluated datum
    have hBev : elim.matOneValue
        (evalPfm (pfmMul (ofMatProf G) (pfmSwap Wf.1)) m en ed K)
        (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K))) := by
      have h := evalPfm_mul (ofMatProf G) (pfmSwap Wf.1) m en ed 0 K o o
        hOMr hSwl ho hSwr (fun i j => poly.capOfLen (ofMatEntryLen G m i j))
        hSwLen
      rw [Nat.zero_add] at h
      refine elim.matOne_trans h ?_
      refine elim.matOne_trans
        (elim.matMul_congrL _ G _
          (elim.matOne_trans (evalPfm_ofMat G m en ed 0)
            (inertia.matScaleB_one G))) ?_
      exact elim.matMul_congrR (n := o) (k := o) G _ _
        (rowsLen_evalPfm o m (pfmSwap Wf.1) en ed K hSwr) hSWr
        ((length_evalPfm m (pfmSwap Wf.1) en ed K).trans hSwl) hSWl
        (evalPfm_swap Wf.1 m en ed K)
    have hTrev : elim.matOneValue
        (evalPfm (pfmTr (pfmSwap Wf.1)) m en ed K)
        (elim.transposeM (elim.matSwap (evalPfm Wf.1 m en ed K))) :=
      elim.matOne_trans (evalPfm_tr (pfmSwap Wf.1) m en ed K o hSwl hSwr)
        (elim.transposeM_congrM o _ _
          (rowsLen_evalPfm o m (pfmSwap Wf.1) en ed K hSwr) hSWr
          ((length_evalPfm m (pfmSwap Wf.1) en ed K).trans
            (hSwl.trans hSWl.symm))
          (evalPfm_swap Wf.1 m en ed K))
    have hIev : elim.matOneValue
        (evalPfm (pfmMul (pfmTr (pfmSwap Wf.1))
          (pfmMul (ofMatProf G) (pfmSwap Wf.1))) m en ed (K + K))
        (elim.matMul (elim.transposeM
            (elim.matSwap (evalPfm Wf.1 m en ed K)))
          (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K)))) := by
      refine elim.matOne_trans
        (evalPfm_mul (pfmTr (pfmSwap Wf.1))
          (pfmMul (ofMatProf G) (pfmSwap Wf.1)) m en ed K K o o
          hTrr hBl ho hBr hTrLen hBcap) ?_
      refine elim.matOne_trans (elim.matMul_congrL _ _ _ hTrev) ?_
      exact elim.matMul_congrR (n := o) (k := o) _ _ _
        (rowsLen_evalPfm o m (pfmMul (ofMatProf G) (pfmSwap Wf.1)) en ed K
          hBr)
        (elim.rowsLen_matMul_of G _ (fun _ => by rw [hSWl]; exact ho) hSWr)
        ((length_evalPfm m (pfmMul (ofMatProf G) (pfmSwap Wf.1)) en ed
          K).trans hBl)
        ((elim.length_matMul G _).trans hGl) hBev
    -- the two arms' evaluated data
    have hev1 : elim.matOneValue
        (evalPfm (pfmScale (profMul (profMul Wf.2 Wf.2)
          (constProf (BPair.ofPos (ln * ln)))) (ofMatProf G)) m en ed (K + K))
        (inertia.matScaleB
          ((evalProf Wf.2 m en ed K * evalProf Wf.2 m en ed K)
            * BPair.ofPos (ln * ln)) G) :=
      evalScalePair Wf.2 Wf.2 (BPair.ofPos (ln * ln)) G m en ed K
        hshWcl hshWcl
    have hscale : elim.matOneValue
        (evalPfm (pfmScale (constProf (BPair.ofPos (ld * ld)))
          (pfmMul (pfmTr (pfmSwap Wf.1))
            (pfmMul (ofMatProf G) (pfmSwap Wf.1)))) m en ed (K + K))
        (inertia.matScaleB
          (evalProf (constProf (BPair.ofPos (ld * ld))) m en ed 0)
          (elim.matMul (elim.transposeM
              (elim.matSwap (evalPfm Wf.1 m en ed K)))
            (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K))))) := by
      have h := evalPfm_scale (constProf (BPair.ofPos (ld * ld)))
        (pfmMul (pfmTr (pfmSwap Wf.1))
          (pfmMul (ofMatProf G) (pfmSwap Wf.1))) m en ed 0 (K + K)
        (poly.capOfLen (Nat.le_of_eq (depthConst_len (BPair.ofPos (ld * ld)) m)))
        hIcap
      rw [Nat.zero_add] at h
      exact elim.matOne_trans h
        (inertia.matOne_scaleB _ hIev)
    have hev2 : elim.matOneValue
        (evalPfm (pfmSwap (pfmScale (constProf (BPair.ofPos (ld * ld)))
          (pfmMul (pfmTr (pfmSwap Wf.1))
            (pfmMul (ofMatProf G) (pfmSwap Wf.1))))) m en ed (K + K))
        (elim.matSwap (inertia.matScaleB
          (evalProf (constProf (BPair.ofPos (ld * ld))) m en ed 0)
          (elim.matMul (elim.transposeM
              (elim.matSwap (evalPfm Wf.1 m en ed K)))
            (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K)))))) :=
      elim.matOne_trans (evalPfm_swap _ m en ed (K + K))
        (elim.matSwap_congr hscale)
    -- the site's shapes
    have h1l : (pfmScale (profMul (profMul Wf.2 Wf.2)
        (constProf (BPair.ofPos (ln * ln)))) (ofMatProf G)).length = o :=
      (length_pfmScale _ (ofMatProf G)).trans hOMl
    have h1r : elim.rowsLen o (pfmScale
        (profMul (profMul Wf.2 Wf.2)
          (constProf (BPair.ofPos (ln * ln)))) (ofMatProf G)) :=
      rowsLen_pfmScale _ o (ofMatProf G) hOMr
    have h2l : (pfmSwap (pfmScale (constProf (BPair.ofPos (ld * ld)))
        (pfmMul (pfmTr (pfmSwap Wf.1))
          (pfmMul (ofMatProf G) (pfmSwap Wf.1))))).length = o :=
      (length_pfmSwap _).trans ((length_pfmScale _ _).trans hIl)
    have h2r : elim.rowsLen o (pfmSwap (pfmScale
        (constProf (BPair.ofPos (ld * ld)))
        (pfmMul (pfmTr (pfmSwap Wf.1))
          (pfmMul (ofMatProf G) (pfmSwap Wf.1))))) :=
      rowsLen_pfmSwap o _ (rowsLen_pfmScale _ o _ hIr)
    have hSl : (contrSiteF Wf G ln ld).length = o :=
      (length_pfmAdd _ _ (by rw [h1l, h2l])).trans h1l
    have hSr : elim.rowsLen o (contrSiteF Wf G ln ld) :=
      rowsLen_pfmAdd o _ _ h1r h2r
    have hYl : (elim.matMul (elim.transposeM
        (elim.matSwap (evalPfm Wf.1 m en ed K)))
        (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K)))).length
        = o :=
      (elim.length_matMul _ _).trans (elim.transposeLen _ hSWr hSWl)
    have hYr : elim.rowsLen o (elim.matMul (elim.transposeM
        (elim.matSwap (evalPfm Wf.1 m en ed K)))
        (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K)))) :=
      elim.rowsLen_matMul_of _ _
        (fun _ => by rw [(elim.length_matMul G _).trans hGl]; exact ho)
        (elim.rowsLen_matMul_of G _ (fun _ => by rw [hSWl]; exact ho) hSWr)
    have hEv : elim.matOneValue
        (evalPfm (contrSiteF Wf G ln ld) m en ed (K + K))
        (elim.matAdd
          (inertia.matScaleB
            ((evalProf Wf.2 m en ed K * evalProf Wf.2 m en ed K)
              * BPair.ofPos (ln * ln)) G)
          (elim.matSwap (inertia.matScaleB
            (evalProf (constProf (BPair.ofPos (ld * ld))) m en ed 0)
            (elim.matMul (elim.transposeM
                (elim.matSwap (evalPfm Wf.1 m en ed K)))
              (elim.matMul G
                (elim.matSwap (evalPfm Wf.1 m en ed K))))))) :=
      elim.matOne_trans (evalPfm_add _ _ m en ed (K + K))
        (elim.matAdd_cong2 o _ _ _ _
          (rowsLen_evalPfm o m _ en ed (K + K) h1r)
          (rowsLen_evalPfm o m _ en ed (K + K) h2r)
          (inertia.rowsLen_scaleB _ o G hGr)
          (elim.rowsLen_mapRows BPair.swap _ o
            (inertia.rowsLen_scaleB _ o _ hYr))
          hev1 hev2)
    have hcmp := siteTwoArm e0n e0d m (K + K) en ed
      (contrSiteF Wf G ln ld) bxC o G
      (elim.matMul (elim.transposeM
        (elim.matSwap (evalPfm Wf.1 m en ed K)))
        (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K))))
      ((evalProf Wf.2 m en ed K * evalProf Wf.2 m en ed K)
        * BPair.ofPos (ln * ln))
      (evalProf (constProf (BPair.ofPos (ld * ld))) m en ed 0)
      hSl hSr hGl hGr hYl hYr hEv hsymG
      (elim.congrSym G (elim.matSwap (evalPfm Wf.1 m en ed K)) hGr hGl
        hSWr hSWl ho ho hsymG)
      hwalk he hbox (a :: t) hu
    -- the congruated form reads the transferred vector's own
    have hqY : (inertia.quadForm
        (elim.matMul (elim.transposeM
          (elim.matSwap (evalPfm Wf.1 m en ed K)))
          (elim.matMul G (elim.matSwap (evalPfm Wf.1 m en ed K))))
        (a :: t)).oneValue
        (inertia.quadForm G
          (elim.matVec (elim.matSwap (evalPfm Wf.1 m en ed K))
            (a :: t))) :=
      BPair.oneValue_trans
        (elim.dotN_read (a :: t) _)
        (BPair.oneValue_trans
          (BPair.oneValue_symm
            (inertia.congrPair G (elim.matSwap (evalPfm Wf.1 m en ed K))
              o o hGl hGr hSWl hSWr (a :: t) (a :: t) hu hu))
          (BPair.oneValue_symm (elim.dotN_read _ _)))
    refine ground.leB_congr_left
      (BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (evalProf_const (BPair.ofPos (ld * ld)) m en ed 0)
            (mulBpowZero ed (BPair.ofPos (ld * ld))))
          hqY)
        (BPair.ofPos_scale (ld * ld) _)) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (BPair.mul_congr
              (BPair.mul_congr (BPair.oneValue_symm hcW)
                (BPair.oneValue_symm hcW))
              (BPair.oneValue_refl _))
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.ofPos_mul cW cW)
                (BPair.oneValue_refl _))
              (BPair.oneValue_trans (BPair.ofPos_mul (cW * cW) (ln * ln))
                (BPair.oneValue_of_eq (congrArg BPair.ofPos
                  (ground.mul_comm (cW * cW) (ln * ln)))))))
          (BPair.oneValue_refl _))
        (BPair.ofPos_scale (ln * ln * (cW * cW)) _)) ?_
    exact hcmp

/-- `lem:cornerblock`'s defect cap at the evaluated data, the
upper arm: at a dominance certificate walk over the defect cap's
upper site datum, with the center's and the image's exchanges and
the gram's own, the defect's evaluated form at the cap denominator
sits at or below the gram's at the cap numerator and the defect's
own clearing — `thm:decimation`(ii)'s comparison at the deviation's
cleared datum, the center defect the drift's slot. -/
theorem dcapCount_hi (Cf If : PfMQ) (G : elim.Mat) (o : Nat)
    (r0n r0d : Pos) (e0n : BPair) (e0d : Pos)
    (bxU : List BoxCert) (m K : Nat) (en ed : Pos) (cI cC : Pos)
    (hIl : If.1.length = o) (hIr : elim.rowsLen o If.1)
    (hCl : Cf.1.length = o) (hCr : elim.rowsLen o Cf.1)
    (hGq : elim.sqAt G o)
    (hsymC : pfmOneValue (pfmTr Cf.1) Cf.1)
    (hsymI : pfmOneValue (pfmTr If.1) If.1)
    (hsymG : elim.matOneValue (elim.transposeM G) G)
    (hshI : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) If.1 i) j)
        m)).length ≤ K + 1)
    (hshIcl : (poly.vnorm (depthPoly If.2 m)).length ≤ K + 1)
    (hshC : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Cf.1 i) j)
        m)).length ≤ K + 1)
    (hshCl : (poly.vnorm (depthPoly Cf.2 m)).length ≤ K + 1)
    (hwalk : domCertGo e0n e0d 0 (dcapHiSiteF Cf If G r0n r0d) bxU)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (bxU.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (K + K + 1))) = true)
    (hcI : (BPair.ofPos cI).oneValue (evalProf If.2 m en ed K))
    (hcC : (BPair.ofPos cC).oneValue
      (evalProf Cf.2 m en ed K)) :
    ∀ w : List BPair, w.length = o →
      (inertia.quadForm (spectator.devQ (evalPfm If.1 m en ed K, cI)
          (evalPfm Cf.1 m en ed K, cC)).1 w).scale r0d
        ≤ (inertia.quadForm G w).scale
            (r0n * (spectator.devQ (evalPfm If.1 m en ed K, cI)
              (evalPfm Cf.1 m en ed K, cC)).2) := by
  intro w hw
  cases w with
  | nil =>
    exact ground.leB_congr_left (ground.unitScale _)
      (ground.leB_congr_right (ground.unitScale _)
        (ground.leB_refl BPair.unit))
  | cons a t =>
    have ho : 0 < o := by rw [← hw]; exact Nat.succ_pos _
    have hGl : G.length = o := elim.sqAt_len hGq
    have hGr : elim.rowsLen o G := elim.rowsLen_of_sqAt hGq
    have hMIr : elim.rowsLen o (evalPfm If.1 m en ed K) :=
      rowsLen_evalPfm o m If.1 en ed K hIr
    have hMIl : (evalPfm If.1 m en ed K).length = o :=
      (length_evalPfm m If.1 en ed K).trans hIl
    have hSCr : elim.rowsLen o
        (elim.matSwap (evalPfm Cf.1 m en ed K)) :=
      elim.rowsLen_mapRows BPair.swap _ o
        (rowsLen_evalPfm o m Cf.1 en ed K hCr)
    have hSCl : (elim.matSwap (evalPfm Cf.1 m en ed K)).length = o :=
      (elim.length_matSwap _).trans
        ((length_evalPfm m Cf.1 en ed K).trans hCl)
    have hDl : (elim.matAdd
        (inertia.matScaleB (evalProf Cf.2 m en ed K)
          (evalPfm If.1 m en ed K))
        (inertia.matScaleB (evalProf If.2 m en ed K)
          (elim.matSwap (evalPfm Cf.1 m en ed K)))).length = o :=
      (elim.length_matAdd _ _
        (by rw [inertia.length_scaleB, inertia.length_scaleB,
          hMIl, hSCl])).trans
        ((inertia.length_scaleB _ _).trans hMIl)
    have hDr : elim.rowsLen o (elim.matAdd
        (inertia.matScaleB (evalProf Cf.2 m en ed K)
          (evalPfm If.1 m en ed K))
        (inertia.matScaleB (evalProf If.2 m en ed K)
          (elim.matSwap (evalPfm Cf.1 m en ed K)))) :=
      elim.rowsLen_matAdd o _ _ (inertia.rowsLen_scaleB _ o _ hMIr)
        (inertia.rowsLen_scaleB _ o _ hSCr)
    have h1l : (pfmScale (profMul (devFam Cf If).2
        (constProf (BPair.ofPos r0n))) (ofMatProf G)).length = o :=
      (length_pfmScale _ (ofMatProf G)).trans
        ((length_ofMatProf G).trans hGl)
    have h1r : elim.rowsLen o (pfmScale (profMul (devFam Cf If).2
        (constProf (BPair.ofPos r0n))) (ofMatProf G)) :=
      rowsLen_pfmScale _ o (ofMatProf G) (rowsLen_ofMatProf o G hGr)
    have h2l : (pfmSwap (pfmScale (constProf (BPair.ofPos r0d))
        (devFam Cf If).1)).length = o :=
      (length_pfmSwap _).trans
        ((length_pfmScale _ _).trans (devLen Cf If o hIl hCl))
    have h2r : elim.rowsLen o (pfmSwap (pfmScale
        (constProf (BPair.ofPos r0d)) (devFam Cf If).1)) :=
      rowsLen_pfmSwap o _
        (rowsLen_pfmScale _ o _ (devRows Cf If o hIr hCr))
    have hSl : (dcapHiSiteF Cf If G r0n r0d).length = o :=
      (length_pfmAdd _ _ (by rw [h1l, h2l])).trans h1l
    have hSr : elim.rowsLen o (dcapHiSiteF Cf If G r0n r0d) :=
      rowsLen_pfmAdd o _ _ h1r h2r
    have hEv : elim.matOneValue
        (evalPfm (dcapHiSiteF Cf If G r0n r0d) m en ed (K + K))
        (elim.matAdd
          (inertia.matScaleB
            ((evalProf If.2 m en ed K
              * evalProf Cf.2 m en ed K) * BPair.ofPos r0n) G)
          (elim.matSwap (inertia.matScaleB
            (evalProf (constProf (BPair.ofPos r0d)) m en ed 0)
            (elim.matAdd
              (inertia.matScaleB (evalProf Cf.2 m en ed K)
                (evalPfm If.1 m en ed K))
              (inertia.matScaleB (evalProf If.2 m en ed K)
                (elim.matSwap (evalPfm Cf.1 m en ed K))))))) :=
      elim.matOne_trans (evalPfm_add _ _ m en ed (K + K))
        (elim.matAdd_cong2 o _ _ _ _
          (rowsLen_evalPfm o m _ en ed (K + K) h1r)
          (rowsLen_evalPfm o m _ en ed (K + K) h2r)
          (inertia.rowsLen_scaleB _ o G hGr)
          (elim.rowsLen_mapRows BPair.swap _ o
            (inertia.rowsLen_scaleB _ o _ hDr))
          (evalScalePair If.2 Cf.2 (BPair.ofPos r0n) G m en ed K
            hshIcl hshCl)
          (elim.matOne_trans (evalPfm_swap _ m en ed (K + K))
            (elim.matSwap_congr
              (dcapArm2 Cf If o r0d m K en ed hIr hCr hshI hshIcl hshC
                hshCl))))
    have hcmp := siteTwoArm e0n e0d m (K + K) en ed
      (dcapHiSiteF Cf If G r0n r0d) bxU o G _
      ((evalProf If.2 m en ed K
        * evalProf Cf.2 m en ed K) * BPair.ofPos r0n)
      (evalProf (constProf (BPair.ofPos r0d)) m en ed 0)
      hSl hSr hGl hGr hDl hDr hEv hsymG
      (devSym Cf If o m K en ed _ _ hIl hIr hCl hCr ho hsymC hsymI)
      hwalk he hbox (a :: t) hw
    have hL : ((evalProf (constProf (BPair.ofPos r0d)) m en ed 0)
        * inertia.quadForm (elim.matAdd
          (inertia.matScaleB (evalProf Cf.2 m en ed K)
            (evalPfm If.1 m en ed K))
          (inertia.matScaleB (evalProf If.2 m en ed K)
            (elim.matSwap (evalPfm Cf.1 m en ed K))))
          (a :: t)).oneValue
        ((inertia.quadForm (elim.matAdd
          (inertia.matScale cC (evalPfm If.1 m en ed K))
          (inertia.matScale cI
            (elim.matSwap (evalPfm Cf.1 m en ed K))))
          (a :: t)).scale r0d) :=
      BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (evalProf_const (BPair.ofPos r0d) m en ed 0)
            (mulBpowZero ed (BPair.ofPos r0d)))
          (BPair.oneValue_symm
            (inertia.quadMatOne _ _ (a :: t)
              (devBridge Cf If o m K en ed cI cC hIr hCr hcI hcC))))
        (BPair.ofPos_scale r0d _)
    have hR : (((evalProf If.2 m en ed K
        * evalProf Cf.2 m en ed K) * BPair.ofPos r0n)
        * inertia.quadForm G (a :: t)).oneValue
        ((inertia.quadForm G (a :: t)).scale (r0n * (cI * cC))) :=
      BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (BPair.mul_congr
              (BPair.mul_congr (BPair.oneValue_symm hcI)
                (BPair.oneValue_symm hcC))
              (BPair.oneValue_refl _))
            (BPair.oneValue_trans
              (BPair.mul_congr_left (BPair.ofPos_mul cI cC))
              (BPair.oneValue_trans (BPair.ofPos_mul (cI * cC) r0n)
                (BPair.oneValue_of_eq
                  (congrArg BPair.ofPos
                    (ground.mul_comm (cI * cC) r0n))))))
          (BPair.oneValue_refl _))
        (BPair.ofPos_scale (r0n * (cI * cC)) _)
    exact ground.leB_congr_left hL (ground.leB_congr_right hR hcmp)

/-- `lem:cornerblock`'s defect cap at the evaluated data, the
lower arm: at a dominance certificate walk over the defect cap's
lower site datum the gram's evaluated form at the cap numerator and
the deviation's clearing has its balance partner at or below the
deviation's own form at the cap denominator — the deviation's
cleared datum, the center defect the drift's slot. -/
theorem dcapCount_lo (Cf If : PfMQ) (G : elim.Mat) (o : Nat)
    (r0n r0d : Pos) (e0n : BPair) (e0d : Pos)
    (bxL : List BoxCert) (m K : Nat) (en ed : Pos) (cI cC : Pos)
    (hIl : If.1.length = o) (hIr : elim.rowsLen o If.1)
    (hCl : Cf.1.length = o) (hCr : elim.rowsLen o Cf.1)
    (hGq : elim.sqAt G o)
    (hsymC : pfmOneValue (pfmTr Cf.1) Cf.1)
    (hsymI : pfmOneValue (pfmTr If.1) If.1)
    (hsymG : elim.matOneValue (elim.transposeM G) G)
    (hshI : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) If.1 i) j)
        m)).length ≤ K + 1)
    (hshIcl : (poly.vnorm (depthPoly If.2 m)).length ≤ K + 1)
    (hshC : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Cf.1 i) j)
        m)).length ≤ K + 1)
    (hshCl : (poly.vnorm (depthPoly Cf.2 m)).length ≤ K + 1)
    (hwalk : domCertGo e0n e0d 0 (dcapLoSiteF Cf If G r0n r0d) bxL)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hbox : (bxL.all (fun g =>
        decide (g.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ g.hi)
        && Nat.ble (g.K + 1) (K + K + 1))) = true)
    (hcI : (BPair.ofPos cI).oneValue (evalProf If.2 m en ed K))
    (hcC : (BPair.ofPos cC).oneValue
      (evalProf Cf.2 m en ed K)) :
    ∀ w : List BPair, w.length = o →
      ((inertia.quadForm G w).scale
          (r0n * (spectator.devQ (evalPfm If.1 m en ed K, cI)
            (evalPfm Cf.1 m en ed K, cC)).2)).swap
        ≤ (inertia.quadForm
            (spectator.devQ (evalPfm If.1 m en ed K, cI)
              (evalPfm Cf.1 m en ed K, cC)).1 w).scale r0d := by
  intro w hw
  cases w with
  | nil =>
    refine ground.leB_congr_left
      (ground.swap_congr (ground.unitScale _)) ?_
    exact ground.leB_congr_right (ground.unitScale _)
      (ground.leB_refl BPair.unit)
  | cons a t =>
    have ho : 0 < o := by rw [← hw]; exact Nat.succ_pos _
    have hGl : G.length = o := elim.sqAt_len hGq
    have hGr : elim.rowsLen o G := elim.rowsLen_of_sqAt hGq
    have hMIr : elim.rowsLen o (evalPfm If.1 m en ed K) :=
      rowsLen_evalPfm o m If.1 en ed K hIr
    have hMIl : (evalPfm If.1 m en ed K).length = o :=
      (length_evalPfm m If.1 en ed K).trans hIl
    have hSCr : elim.rowsLen o
        (elim.matSwap (evalPfm Cf.1 m en ed K)) :=
      elim.rowsLen_mapRows BPair.swap _ o
        (rowsLen_evalPfm o m Cf.1 en ed K hCr)
    have hSCl : (elim.matSwap (evalPfm Cf.1 m en ed K)).length = o :=
      (elim.length_matSwap _).trans
        ((length_evalPfm m Cf.1 en ed K).trans hCl)
    have hDl : (elim.matAdd
        (inertia.matScaleB (evalProf Cf.2 m en ed K)
          (evalPfm If.1 m en ed K))
        (inertia.matScaleB (evalProf If.2 m en ed K)
          (elim.matSwap (evalPfm Cf.1 m en ed K)))).length = o :=
      (elim.length_matAdd _ _
        (by rw [inertia.length_scaleB, inertia.length_scaleB,
          hMIl, hSCl])).trans
        ((inertia.length_scaleB _ _).trans hMIl)
    have hDr : elim.rowsLen o (elim.matAdd
        (inertia.matScaleB (evalProf Cf.2 m en ed K)
          (evalPfm If.1 m en ed K))
        (inertia.matScaleB (evalProf If.2 m en ed K)
          (elim.matSwap (evalPfm Cf.1 m en ed K)))) :=
      elim.rowsLen_matAdd o _ _ (inertia.rowsLen_scaleB _ o _ hMIr)
        (inertia.rowsLen_scaleB _ o _ hSCr)
    have h1l : (pfmScale (profMul (devFam Cf If).2
        (constProf (BPair.ofPos r0n))) (ofMatProf G)).length = o :=
      (length_pfmScale _ (ofMatProf G)).trans
        ((length_ofMatProf G).trans hGl)
    have h1r : elim.rowsLen o (pfmScale (profMul (devFam Cf If).2
        (constProf (BPair.ofPos r0n))) (ofMatProf G)) :=
      rowsLen_pfmScale _ o (ofMatProf G) (rowsLen_ofMatProf o G hGr)
    have h2l : (pfmScale (constProf (BPair.ofPos r0d))
        (devFam Cf If).1).length = o :=
      (length_pfmScale _ _).trans (devLen Cf If o hIl hCl)
    have h2r : elim.rowsLen o (pfmScale (constProf (BPair.ofPos r0d))
        (devFam Cf If).1) :=
      rowsLen_pfmScale _ o _ (devRows Cf If o hIr hCr)
    have hSl : (dcapLoSiteF Cf If G r0n r0d).length = o :=
      (length_pfmAdd _ _ (by rw [h1l, h2l])).trans h1l
    have hSr : elim.rowsLen o (dcapLoSiteF Cf If G r0n r0d) :=
      rowsLen_pfmAdd o _ _ h1r h2r
    have hEv : elim.matOneValue
        (evalPfm (dcapLoSiteF Cf If G r0n r0d) m en ed (K + K))
        (elim.matAdd
          (inertia.matScaleB
            ((evalProf If.2 m en ed K
              * evalProf Cf.2 m en ed K) * BPair.ofPos r0n) G)
          (inertia.matScaleB
            (evalProf (constProf (BPair.ofPos r0d)) m en ed 0)
            (elim.matAdd
              (inertia.matScaleB (evalProf Cf.2 m en ed K)
                (evalPfm If.1 m en ed K))
              (inertia.matScaleB (evalProf If.2 m en ed K)
                (elim.matSwap (evalPfm Cf.1 m en ed K)))))) :=
      elim.matOne_trans (evalPfm_add _ _ m en ed (K + K))
        (elim.matAdd_cong2 o _ _ _ _
          (rowsLen_evalPfm o m _ en ed (K + K) h1r)
          (rowsLen_evalPfm o m _ en ed (K + K) h2r)
          (inertia.rowsLen_scaleB _ o G hGr)
          (inertia.rowsLen_scaleB _ o _ hDr)
          (evalScalePair If.2 Cf.2 (BPair.ofPos r0n) G m en ed K
            hshIcl hshCl)
          (dcapArm2 Cf If o r0d m K en ed hIr hCr hshI hshIcl hshC
            hshCl))
    have hcmp := siteTwoArmLo e0n e0d m (K + K) en ed
      (dcapLoSiteF Cf If G r0n r0d) bxL o G _
      ((evalProf If.2 m en ed K
        * evalProf Cf.2 m en ed K) * BPair.ofPos r0n)
      (evalProf (constProf (BPair.ofPos r0d)) m en ed 0)
      hSl hSr hGl hGr hDl hDr hEv hsymG
      (devSym Cf If o m K en ed _ _ hIl hIr hCl hCr ho hsymC hsymI)
      hwalk he hbox (a :: t) hw
    have hL : ((evalProf (constProf (BPair.ofPos r0d)) m en ed 0)
        * inertia.quadForm (elim.matAdd
          (inertia.matScaleB (evalProf Cf.2 m en ed K)
            (evalPfm If.1 m en ed K))
          (inertia.matScaleB (evalProf If.2 m en ed K)
            (elim.matSwap (evalPfm Cf.1 m en ed K))))
          (a :: t)).oneValue
        ((inertia.quadForm (elim.matAdd
          (inertia.matScale cC (evalPfm If.1 m en ed K))
          (inertia.matScale cI
            (elim.matSwap (evalPfm Cf.1 m en ed K))))
          (a :: t)).scale r0d) :=
      BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (evalProf_const (BPair.ofPos r0d) m en ed 0)
            (mulBpowZero ed (BPair.ofPos r0d)))
          (BPair.oneValue_symm
            (inertia.quadMatOne _ _ (a :: t)
              (devBridge Cf If o m K en ed cI cC hIr hCr hcI hcC))))
        (BPair.ofPos_scale r0d _)
    have hR : (((evalProf If.2 m en ed K
        * evalProf Cf.2 m en ed K) * BPair.ofPos r0n)
        * inertia.quadForm G (a :: t)).oneValue
        ((inertia.quadForm G (a :: t)).scale (r0n * (cI * cC))) :=
      BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans
            (BPair.mul_congr
              (BPair.mul_congr (BPair.oneValue_symm hcI)
                (BPair.oneValue_symm hcC))
              (BPair.oneValue_refl _))
            (BPair.oneValue_trans
              (BPair.mul_congr_left (BPair.ofPos_mul cI cC))
              (BPair.oneValue_trans (BPair.ofPos_mul (cI * cC) r0n)
                (BPair.oneValue_of_eq
                  (congrArg BPair.ofPos
                    (ground.mul_comm (cI * cC) r0n))))))
          (BPair.oneValue_refl _))
        (BPair.ofPos_scale (r0n * (cI * cC)) _)
    exact ground.leB_congr_left (ground.swap_congr hR)
      (ground.leB_congr_right hL hcmp)

open elim inertia greenprod in
/-- `lem:cornerblock`'s witness tie at the evaluated data: the
family's stated recursion witness identity — the shallower center
against the transfer factor reading the bond's exchange — read at a
depth is the cleared pivots' own tie, each clearing entering at its
stated margin and the shared clearing power cancelling across the
cross-multiplied comparison. -/
theorem witTie_ptw (Cf Wf : PfMQ) (B : elim.Mat) (o m K : Nat)
    (en ed cC cWs : Pos)
    (hCr : elim.rowsLen o Cf.1)
    (hWl : Wf.1.length = o) (hWr : elim.rowsLen o Wf.1) (ho : 0 < o)
    (hshC : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Cf.1 i) j)
        m)).length ≤ K + 1)
    (hshCl : (poly.vnorm (depthPoly Cf.2 m)).length ≤ K + 1)
    (hshW : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Wf.1 i) j)
        (m + 1))).length ≤ K + 1)
    (hshWcl : (poly.vnorm (depthPoly Wf.2 (m + 1))).length ≤ K + 1)
    (hcC : (BPair.ofPos cC).oneValue (evalProf Cf.2 m en ed K))
    (hcW : (BPair.ofPos cWs).oneValue (evalProf Wf.2 (m + 1) en ed K))
    (hwit : pfmQOneValue (pfmQmul Cf (pfmQshift Wf))
      (ofPfm (ofMatProf (elim.transposeM B)))) :
    greenprod.oneValueQ
      (greenprod.mulQ (evalPfm Cf.1 m en ed K, cC)
        (evalPfm Wf.1 (m + 1) en ed K, cWs))
      (greenprod.ofM (elim.transposeM B)) := by
  have hRSr : elim.rowsLen o (pfmReduce (pfmShift Wf.1)) :=
    elim.rowsLen_mapRowsO profReduce (pfmShift Wf.1) o
      (elim.rowsLen_mapRowsO profShift Wf.1 o hWr)
  have hRSl : (pfmReduce (pfmShift Wf.1)).length = o :=
    (ground.length_map _ _).trans ((ground.length_map _ _).trans hWl)
  have hRScap := capPfmReduce (pfmShift Wf.1) m K (capPfmShift Wf.1 m K hshW)
  have hMulCap := capPfmMul Cf.1 (pfmReduce (pfmShift Wf.1)) m K K o o
    hCr hRSl ho hRSr hshC hRScap
  have hClCap : (poly.vnorm
      (depthPoly (profReduce (profShift Wf.2)) m)).length ≤ K + 1 :=
    capCongr (depthPoly_profReduce (profShift Wf.2) m)
      (capCongr (depthPoly_profShift Wf.2 m) hshWcl)
  have hProdCl : (poly.vnorm (depthPoly
      (profMul Cf.2 (profReduce (profShift Wf.2))) m)).length ≤ K + K + 1 :=
    capCongr (depthPoly_profMul Cf.2 (profReduce (profShift Wf.2)) m)
      (capMul hshCl hClCap)
  have hEq := evalPfm_congr _ _ m en ed (K + K) hwit
  -- the left side: the unit clearing weights the evaluated product
  have hL0 : elim.matOneValue
      (evalPfm (pfmScale (constProf (BPair.ofPos Pos.one))
        (pfmMul Cf.1 (pfmReduce (pfmShift Wf.1)))) m en ed (K + K))
      (inertia.matScaleB
        (evalProf (constProf (BPair.ofPos Pos.one)) m en ed 0)
        (evalPfm (pfmMul Cf.1 (pfmReduce (pfmShift Wf.1)))
          m en ed (K + K))) := by
    have h := evalPfm_scale (constProf (BPair.ofPos Pos.one))
      (pfmMul Cf.1 (pfmReduce (pfmShift Wf.1))) m en ed 0 (K + K)
      (poly.capOfLen (Nat.le_of_eq
        (depthConst_len (BPair.ofPos Pos.one) m)))
      hMulCap
    rw [Nat.zero_add] at h
    exact h
  have hL1 : elim.matOneValue
      (evalPfm (pfmMul Cf.1 (pfmReduce (pfmShift Wf.1))) m en ed (K + K))
      (elim.matMul (evalPfm Cf.1 m en ed K)
        (evalPfm Wf.1 (m + 1) en ed K)) :=
    elim.matOne_trans
      (evalPfm_mul Cf.1 (pfmReduce (pfmShift Wf.1)) m en ed K K o o
        hCr hRSl ho hRSr hshC hRScap)
      (elim.matMul_congrR (n := o) (k := o) (evalPfm Cf.1 m en ed K)
        (evalPfm (pfmReduce (pfmShift Wf.1)) m en ed K)
        (evalPfm Wf.1 (m + 1) en ed K)
        (rowsLen_evalPfm o m _ en ed K hRSr)
        (rowsLen_evalPfm o (m + 1) Wf.1 en ed K hWr)
        ((length_evalPfm m _ en ed K).trans hRSl)
        ((length_evalPfm (m + 1) Wf.1 en ed K).trans hWl)
        (elim.matOne_trans
          (evalPfm_reduce (pfmShift Wf.1) m en ed K)
          (evalPfm_shift Wf.1 m en ed K)))
  have hL : elim.matOneValue
      (evalPfm (pfmScale (constProf (BPair.ofPos Pos.one))
        (pfmMul Cf.1 (pfmReduce (pfmShift Wf.1)))) m en ed (K + K))
      (elim.matMul (evalPfm Cf.1 m en ed K)
        (evalPfm Wf.1 (m + 1) en ed K)) :=
    elim.matOne_trans hL0
      (elim.matOne_trans
        (inertia.matScaleB_congr
          (BPair.oneValue_trans
            (evalProf_const (BPair.ofPos Pos.one) m en ed 0)
            (mulBpowZero ed (BPair.ofPos Pos.one))) _)
        (elim.matOne_trans (inertia.matScaleB_one _)
          hL1))
  -- the right side: the two margins weight the stated bond's exchange
  have hR0 : elim.matOneValue
      (evalPfm (pfmScale (profMul Cf.2 (profReduce (profShift Wf.2)))
        (ofMatProf (elim.transposeM B))) m en ed (K + K))
      (inertia.matScaleB
        (evalProf (profMul Cf.2 (profReduce (profShift Wf.2)))
          m en ed (K + K))
        (evalPfm (ofMatProf (elim.transposeM B)) m en ed 0)) :=
    evalPfm_scale (profMul Cf.2 (profReduce (profShift Wf.2)))
      (ofMatProf (elim.transposeM B)) m en ed (K + K) 0 hProdCl
      (fun i j => poly.capOfLen (ofMatEntryLen (elim.transposeM B) m i j))
  have hRw : (evalProf (profMul Cf.2 (profReduce (profShift Wf.2)))
      m en ed (K + K)).oneValue (BPair.ofPos (cC * cWs)) :=
    BPair.oneValue_trans
      (evalProf_profMul Cf.2 (profReduce (profShift Wf.2)) m en ed K K
        hshCl hClCap)
      (BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_symm hcC)
          (BPair.oneValue_symm
            (BPair.oneValue_trans hcW
              (BPair.oneValue_symm
                (BPair.oneValue_trans
                  (evalProf_profReduce (profShift Wf.2) m en ed K)
                  (evalProf_profShift Wf.2 m en ed K))))))
        (BPair.ofPos_mul cC cWs))
  have hR : elim.matOneValue
      (evalPfm (pfmScale (profMul Cf.2 (profReduce (profShift Wf.2)))
        (ofMatProf (elim.transposeM B))) m en ed (K + K))
      (inertia.matScaleB (BPair.ofPos (cC * cWs))
        (elim.transposeM B)) :=
    elim.matOne_trans hR0
      (elim.matOne_trans
        (inertia.matScaleB_congr hRw _)
        (inertia.matOne_scaleB (BPair.ofPos (cC * cWs))
          (elim.matOne_trans
            (evalPfm_ofMat (elim.transposeM B) m en ed 0)
            (inertia.matScaleB_one (elim.transposeM B)))))
  show elim.matOneValue
    (inertia.matScale Pos.one
      (elim.matMul (evalPfm Cf.1 m en ed K) (evalPfm Wf.1 (m + 1) en ed K)))
    (inertia.matScale (cC * cWs) (elim.transposeM B))
  rw [inertia.matScale_one]
  exact elim.matOne_trans (elim.matOne_symm hL)
    (elim.matOne_trans hEq
      (elim.matOne_trans hR
        (elim.matOne_symm
          (inertia.matScale_scaleB (cC * cWs) (elim.transposeM B)))))

open elim inertia greenprod in
/-- `lem:cornerblock`'s image tie at the evaluated data: the
family's stated recursion join — the image family joined to the
bond's multiple of the transfer factor's balance partner against the
diagonal family — read at a depth is the cleared pivots' own join
against the stated diagonal, the diagonal's stated scale carrying the
evaluated family's clearing power, each clearing entering at its
stated margin and the shared clearing power cancelling across the
cross-multiplied comparison. -/
theorem joinTie_ptw (Af : List (List (poly.PPoly × poly.PPoly)))
    (Wf If : PfMQ) (A B : elim.Mat) (o m K : Nat)
    (en ed edK cI cW : Pos)
    (hAl : Af.length = o) (hAr : elim.rowsLen o Af)
    (hWl : Wf.1.length = o) (hWr : elim.rowsLen o Wf.1)
    (hIl : If.1.length = o) (hIr : elim.rowsLen o If.1)
    (hBq : elim.sqAt B o) (hAq : elim.sqAt A o) (ho : 0 < o)
    (hshA : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Af i) j)
        m)).length ≤ K + 1)
    (hshW : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) Wf.1 i) j)
        m)).length ≤ K + 1)
    (hshWcl : (poly.vnorm (depthPoly Wf.2 m)).length ≤ K + 1)
    (hshI : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) If.1 i) j)
        m)).length ≤ K + 1)
    (hshIcl : (poly.vnorm (depthPoly If.2 m)).length ≤ K + 1)
    (hcI : (BPair.ofPos cI).oneValue (evalProf If.2 m en ed K))
    (hcW : (BPair.ofPos cW).oneValue (evalProf Wf.2 m en ed K))
    (hedK : (BPair.ofPos edK).oneValue (ground.bpow (BPair.ofPos ed) K))
    (hdiag : elim.matOneValue (inertia.matScale edK A)
      (evalPfm Af m en ed K))
    (hjoin : pfmQOneValue If
      (pfmQadd (ofPfm Af)
        (pfmQmul (ofPfm (ofMatProf B)) (pfmQswap Wf)))) :
    greenprod.oneValueQ
      (greenprod.addQ (evalPfm If.1 m en ed K, cI)
        (greenprod.mulQ (greenprod.ofM B) (evalPfm Wf.1 m en ed K, cW)))
      (greenprod.ofM A) := by
  -- the evaluated pivots and their order reads
  have hMIl : (evalPfm If.1 m en ed K).length = o :=
    (length_evalPfm m If.1 en ed K).trans hIl
  have hMIr : elim.rowsLen o (evalPfm If.1 m en ed K) :=
    rowsLen_evalPfm o m If.1 en ed K hIr
  have hMIq : elim.sqAt (evalPfm If.1 m en ed K) o := elim.sqAt_of hMIl hMIr
  have hMWl : (evalPfm Wf.1 m en ed K).length = o :=
    (length_evalPfm m Wf.1 en ed K).trans hWl
  have hMWr : elim.rowsLen o (evalPfm Wf.1 m en ed K) :=
    rowsLen_evalPfm o m Wf.1 en ed K hWr
  have hMAl : (evalPfm Af m en ed K).length = o :=
    (length_evalPfm m Af en ed K).trans hAl
  have hMAr : elim.rowsLen o (evalPfm Af m en ed K) :=
    rowsLen_evalPfm o m Af en ed K hAr
  have hMAq : elim.sqAt (evalPfm Af m en ed K) o := elim.sqAt_of hMAl hMAr
  have hBMWq : elim.sqAt (elim.matMul B (evalPfm Wf.1 m en ed K)) o :=
    elim.sqAt_of ((elim.length_matMul B _).trans (elim.sqAt_len hBq))
      (elim.rowsLen_matMul_of B _ (fun _ => by rw [hMWl]; exact ho) hMWr)
  -- the caps
  have hc1 : (poly.vnorm
      (depthPoly (constProf (BPair.ofPos Pos.one)) m)).length ≤ 0 + 1 :=
    poly.capOfLen (Nat.le_of_eq (depthConst_len (BPair.ofPos Pos.one) m))
  have hc1K : (poly.vnorm
      (depthPoly (constProf (BPair.ofPos Pos.one)) m)).length ≤ K + 1 :=
    Nat.le_trans hc1 (Nat.succ_le_succ (Nat.zero_le K))
  have hUW : (poly.vnorm (depthPoly
      (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) m)).length
      ≤ K + 1 := by
    have h := capCongr
      (depthPoly_profMul (constProf (BPair.ofPos Pos.one)) Wf.2 m)
      (capMul hc1 hshWcl)
    rw [Nat.zero_add] at h
    exact h
  have hUUW : (poly.vnorm (depthPoly
      (profMul (constProf (BPair.ofPos Pos.one))
        (profMul (constProf (BPair.ofPos Pos.one)) Wf.2)) m)).length
      ≤ K + 1 := by
    have h := capCongr
      (depthPoly_profMul (constProf (BPair.ofPos Pos.one))
        (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) m)
      (capMul hc1 hUW)
    rw [Nat.zero_add] at h
    exact h
  have hOMr : elim.rowsLen o (ofMatProf B) :=
    rowsLen_ofMatProf o B (elim.rowsLen_of_sqAt hBq)
  have hSwl : (pfmSwap Wf.1).length = o := (length_pfmSwap Wf.1).trans hWl
  have hSwr : elim.rowsLen o (pfmSwap Wf.1) := rowsLen_pfmSwap o Wf.1 hWr
  have hSwCap := capPfmSwap Wf.1 m K hshW
  have hOMcap : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (ofMatProf B) i) j) m)).length ≤ K + 1 :=
    fun i j => Nat.le_trans (poly.capOfLen (ofMatEntryLen B m i j))
      (Nat.succ_le_succ (Nat.zero_le K))
  have hcapBW : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmMul (ofMatProf B) (pfmSwap Wf.1)) i) j) m)).length
      ≤ K + K + 1 := by
    intro i j
    have h := capPfmMul (ofMatProf B) (pfmSwap Wf.1) m 0 K o o
      hOMr hSwl ho hSwr
      (fun p q => poly.capOfLen (ofMatEntryLen B m p q)) hSwCap i j
    rw [Nat.zero_add] at h
    exact Nat.le_trans h (Nat.succ_le_succ (Nat.le_add_left K K))
  have hcapS1 := capPfmScale
    (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) Af m K K hUW hshA
  have hcapS2 : ∀ i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly))
        (pfmScale (constProf (BPair.ofPos Pos.one))
          (pfmMul (ofMatProf B) (pfmSwap Wf.1))) i) j) m)).length
      ≤ K + K + 1 := by
    intro i j
    have h := capPfmScale (constProf (BPair.ofPos Pos.one))
      (pfmMul (ofMatProf B) (pfmSwap Wf.1)) m 0 (K + K) hc1 hcapBW i j
    rw [Nat.zero_add] at h
    exact h
  have hcapR1 := capPfmAdd m (K + K) _ _ hcapS1 hcapS2
  -- the family identity evaluated at the shared power
  have hEq := evalPfm_congr _ _ m en ed (K + K + K) hjoin
  -- the left side
  have hL0 : elim.matOneValue
      (evalPfm (pfmScale (profMul (constProf (BPair.ofPos Pos.one))
        (profMul (constProf (BPair.ofPos Pos.one)) Wf.2)) If.1)
        m en ed (K + K + K))
      (inertia.matScaleB
        (evalProf (profMul (constProf (BPair.ofPos Pos.one))
          (profMul (constProf (BPair.ofPos Pos.one)) Wf.2))
          m en ed (K + K))
        (evalPfm If.1 m en ed K)) :=
    evalPfm_scale _ If.1 m en ed (K + K) K
      (Nat.le_trans hUUW (Nat.succ_le_succ (Nat.le_add_right K K))) hshI
  have hLw : (evalProf (profMul (constProf (BPair.ofPos Pos.one))
      (profMul (constProf (BPair.ofPos Pos.one)) Wf.2))
      m en ed (K + K)).oneValue
      (BPair.ofPos edK * BPair.ofPos cW) :=
    BPair.oneValue_trans
      (evalProf_profMul (constProf (BPair.ofPos Pos.one))
        (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) m en ed K K
        hc1K hUW)
      (BPair.mul_congr
        (BPair.oneValue_trans
          (BPair.oneValue_trans
            (evalProf_const (BPair.ofPos Pos.one) m en ed K)
            (BPair.ofPos_one_mul (ground.bpow (BPair.ofPos ed) K)))
          (BPair.oneValue_symm hedK))
        (BPair.oneValue_symm
          (BPair.oneValue_trans hcW
            (BPair.oneValue_symm
              (evalProf_unitMul Wf.2 m en ed K hshWcl)))))
  have hL : elim.matOneValue
      (evalPfm (pfmScale (profMul (constProf (BPair.ofPos Pos.one))
        (profMul (constProf (BPair.ofPos Pos.one)) Wf.2)) If.1)
        m en ed (K + K + K))
      (inertia.matScale (edK * cW) (evalPfm If.1 m en ed K)) :=
    elim.matOne_trans hL0
      (elim.matOne_trans
        (inertia.matScaleB_congr
          (BPair.oneValue_trans hLw (BPair.ofPos_mul edK cW)) _)
        (elim.matOne_symm
          (inertia.matScale_scaleB (edK * cW) (evalPfm If.1 m en ed K))))
  -- the right side
  have hR0 : elim.matOneValue
      (evalPfm (pfmScale If.2
        (pfmAdd (pfmScale (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) Af)
          (pfmScale (constProf (BPair.ofPos Pos.one))
            (pfmMul (ofMatProf B) (pfmSwap Wf.1)))))
        m en ed (K + K + K))
      (inertia.matScaleB (evalProf If.2 m en ed K)
        (evalPfm (pfmAdd
          (pfmScale (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) Af)
          (pfmScale (constProf (BPair.ofPos Pos.one))
            (pfmMul (ofMatProf B) (pfmSwap Wf.1)))) m en ed (K + K))) := by
    have h := evalPfm_scale If.2 _ m en ed K (K + K) hshIcl hcapR1
    rw [← Nat.add_assoc] at h
    exact h
  have hS1 : elim.matOneValue
      (evalPfm (pfmScale (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) Af)
        m en ed (K + K))
      (inertia.matScaleB (BPair.ofPos cW) (evalPfm Af m en ed K)) :=
    elim.matOne_trans
      (evalPfm_scale (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) Af
        m en ed K K hUW hshA)
      (inertia.matScaleB_congr
        (BPair.oneValue_trans (evalProf_unitMul Wf.2 m en ed K hshWcl)
          (BPair.oneValue_symm hcW)) _)
  have hS2 : elim.matOneValue
      (evalPfm (pfmScale (constProf (BPair.ofPos Pos.one))
        (pfmMul (ofMatProf B) (pfmSwap Wf.1))) m en ed (K + K))
      (elim.matSwap (inertia.matScaleB (BPair.ofPos edK)
        (elim.matMul B (evalPfm Wf.1 m en ed K)))) := by
    have h := evalPfm_scale (constProf (BPair.ofPos Pos.one))
      (pfmMul (ofMatProf B) (pfmSwap Wf.1)) m en ed 0 (K + K) hc1 hcapBW
    rw [Nat.zero_add] at h
    refine elim.matOne_trans h ?_
    refine elim.matOne_trans
      (inertia.matScaleB_congr
        (BPair.oneValue_trans
          (evalProf_const (BPair.ofPos Pos.one) m en ed 0)
          (mulBpowZero ed (BPair.ofPos Pos.one))) _) ?_
    refine elim.matOne_trans (inertia.matScaleB_one _) ?_
    refine elim.matOne_trans
      (evalPfm_mul (ofMatProf B) (pfmSwap Wf.1) m en ed K K o o
        hOMr hSwl ho hSwr hOMcap hSwCap) ?_
    refine elim.matOne_trans
      (elim.matMul_congrL _ _ _
        (elim.matOne_trans (evalPfm_ofMat B m en ed K)
          (inertia.matScaleB_congr (BPair.oneValue_symm hedK) B))) ?_
    refine elim.matOne_trans
      (elim.matMul_congrR (n := o) (k := o) _ _ _
        (rowsLen_evalPfm o m (pfmSwap Wf.1) en ed K hSwr)
        (elim.rowsLen_mapRows BPair.swap _ o hMWr)
        ((length_evalPfm m (pfmSwap Wf.1) en ed K).trans hSwl)
        ((elim.length_matSwap _).trans hMWl)
        (evalPfm_swap Wf.1 m en ed K)) ?_
    rw [show elim.matMul (inertia.matScaleB (BPair.ofPos edK) B)
          ((evalPfm Wf.1 m en ed K).map (fun r => r.map BPair.swap))
        = elim.matSwap (elim.matMul (inertia.matScaleB (BPair.ofPos edK) B)
            (evalPfm Wf.1 m en ed K)) from
      elim.matMul_swap _ _]
    exact elim.matSwap_congr
      (inertia.matMul_scaleL (BPair.ofPos edK) B (evalPfm Wf.1 m en ed K))
  have hR : elim.matOneValue
      (evalPfm (pfmScale If.2
        (pfmAdd (pfmScale (profMul (constProf (BPair.ofPos Pos.one)) Wf.2) Af)
          (pfmScale (constProf (BPair.ofPos Pos.one))
            (pfmMul (ofMatProf B) (pfmSwap Wf.1)))))
        m en ed (K + K + K))
      (elim.matAdd (inertia.matScale (cI * cW) (evalPfm Af m en ed K))
        (elim.matSwap (inertia.matScale (cI * edK)
          (elim.matMul B (evalPfm Wf.1 m en ed K))))) := by
    refine elim.matOne_trans hR0 ?_
    refine elim.matOne_trans
      (inertia.matOne_scaleB (evalProf If.2 m en ed K)
        (elim.matOne_trans
          (evalPfm_add _ _ m en ed (K + K))
          (elim.matAdd_cong2 o _ _ _ _
            (rowsLen_evalPfm o m _ en ed (K + K)
              (rowsLen_pfmScale _ o Af hAr))
            (rowsLen_evalPfm o m _ en ed (K + K)
              (rowsLen_pfmScale _ o _
                (elim.rowsLen_matMulO profOps (ofMatProf B) (pfmSwap Wf.1) o
                  (elim.headD_width o (pfmSwap Wf.1)
                    (by rw [hSwl]; exact ho) hSwr))))
            (inertia.rowsLen_scaleB _ o _ hMAr)
            (elim.rowsLen_mapRows BPair.swap _ o
              (inertia.rowsLen_scaleB _ o _
                (elim.rowsLen_of_sqAt hBMWq)))
            hS1 hS2))) ?_
    refine elim.matOne_trans
      (inertia.matScaleB_congr (BPair.oneValue_symm hcI) _) ?_
    refine elim.matOne_trans (matScaleB_sum (BPair.ofPos cI) _ _) ?_
    refine elim.matAdd_cong2 o _ _ _ _
      (inertia.rowsLen_scaleB _ o _
        (inertia.rowsLen_scaleB _ o _ hMAr))
      (inertia.rowsLen_scaleB _ o _
        (elim.rowsLen_mapRows BPair.swap _ o
          (inertia.rowsLen_scaleB _ o _ (elim.rowsLen_of_sqAt hBMWq))))
      (elim.rowsLen_of_sqAt
        (inertia.sqAt_matScale o (cI * cW) _ hMAq))
      (elim.rowsLen_mapRows BPair.swap _ o
        (elim.rowsLen_of_sqAt
          (inertia.sqAt_matScale o (cI * edK) _ hBMWq)))
      ?_ ?_
    · exact elim.matOne_trans
        (inertia.scaleB_scaleB (BPair.ofPos cI) (BPair.ofPos cW)
          (evalPfm Af m en ed K))
        (elim.matOne_trans
          (inertia.matScaleB_congr (BPair.ofPos_mul cI cW) _)
          (elim.matOne_symm
            (inertia.matScale_scaleB (cI * cW) (evalPfm Af m en ed K))))
    · refine elim.matOne_trans
        (matScaleB_neg (BPair.ofPos cI)
          (inertia.matScaleB (BPair.ofPos edK)
            (elim.matMul B (evalPfm Wf.1 m en ed K)))) ?_
      exact elim.matSwap_congr
        (elim.matOne_trans
          (inertia.scaleB_scaleB (BPair.ofPos cI) (BPair.ofPos edK)
            (elim.matMul B (evalPfm Wf.1 m en ed K)))
          (elim.matOne_trans
            (inertia.matScaleB_congr (BPair.ofPos_mul cI edK) _)
            (elim.matOne_symm
              (inertia.matScale_scaleB (cI * edK)
                (elim.matMul B (evalPfm Wf.1 m en ed K))))))
  -- the swapped summand moves across the balance
  have hmove := matSwapMove (o := o)
    (inertia.matScale (edK * cW) (evalPfm If.1 m en ed K))
    (inertia.matScale (cI * cW) (evalPfm Af m en ed K))
    (inertia.matScale (cI * edK) (elim.matMul B (evalPfm Wf.1 m en ed K)))
    (inertia.sqAt_matScale o _ _ hMIq)
    (inertia.sqAt_matScale o _ _ hMAq)
    (inertia.sqAt_matScale o _ _ hBMWq)
    (elim.matOne_trans (elim.matOne_symm hL) (elim.matOne_trans hEq hR))
  -- the diagonal's stated scale and the shared clearing power's cancel
  have hmove2 : elim.matOneValue
      (elim.matAdd (inertia.matScale (edK * cW) (evalPfm If.1 m en ed K))
        (inertia.matScale (cI * edK)
          (elim.matMul B (evalPfm Wf.1 m en ed K))))
      (inertia.matScale (cI * cW) (inertia.matScale edK A)) :=
    elim.matOne_trans hmove
      (elim.matOne_symm
        (inertia.matScale_matOne (cI * cW) hdiag))
  rw [inertia.matScale_matScale edK (cI * cW) A,
    ground.mul_comm (cI * cW) edK,
    show cI * edK = edK * cI from ground.mul_comm cI edK,
    ← inertia.matScale_matScale cW edK (evalPfm If.1 m en ed K),
    ← inertia.matScale_matScale cI edK
      (elim.matMul B (evalPfm Wf.1 m en ed K)),
    ← inertia.matScale_matAdd edK,
    ← inertia.matScale_matScale (cI * cW) edK A] at hmove2
  have hfin := inertia.matOne_unscale edK o _ _
    ((elim.length_matAdd _ _
      (by rw [inertia.length_matScale, inertia.length_matScale,
        hMIl, (elim.length_matMul B _).trans (elim.sqAt_len hBq)])).trans
      ((inertia.length_matScale cW _).trans hMIl))
    (elim.rowsLen_matAdd o _ _
      (elim.rowsLen_of_sqAt (inertia.sqAt_matScale o cW _ hMIq))
      (elim.rowsLen_of_sqAt (inertia.sqAt_matScale o cI _ hBMWq)))
    ((inertia.length_matScale (cI * cW) A).trans (elim.sqAt_len hAq))
    (elim.rowsLen_of_sqAt (inertia.sqAt_matScale o (cI * cW) _ hAq))
    hmove2
  show elim.matOneValue
    (inertia.matScale Pos.one
      (elim.matAdd (inertia.matScale (Pos.one * cW) (evalPfm If.1 m en ed K))
        (inertia.matScale cI (elim.matMul B (evalPfm Wf.1 m en ed K)))))
    (inertia.matScale (cI * (Pos.one * cW)) A)
  rw [inertia.matScale_one, ground.one_mul cW]
  exact hfin

set_option genInjectivity false in
/-- `lem:cornerblock`'s center family with its pairs, read at the
canonical carrier: the order, the diagonal family, and the center,
witness and image families at their clearings; the contraction, the
floor, the defect and the modulus pairs with the shared ball pair
and the ceiling; and the four counts' certificate lists — one box
certificate per row, the diagonal's entry less the off-row
magnitude fold — beside the three clearings' own box certificates,
the centers' determinants the clearings' reads. -/
structure CenterFam where
  o : Nat
  Af : List (List (poly.PPoly × poly.PPoly))
  Cf : PfMQ
  Wf : PfMQ
  If : PfMQ
  lam : Pos × Pos
  y0 : Pos × Pos
  rho : Pos × Pos
  dft : Pos × Pos
  lc : Pos × Pos
  e0 : BPair × Pos
  bxC : List BoxCert
  bxF : List BoxCert
  bxU : List BoxCert
  bxL : List BoxCert
  bxClC : BoxCert
  bxClW : BoxCert
  bxClI : BoxCert

/-- The center family's read: the diagonal, center, witness and
image families square at the order with the two stated matrices;
the gram its own exchange, the center its own and the image family
its own — the located symmetric center's read (`lem:spectator`(iii))
with the dominance comparison's symmetric datum
(`thm:decimation`(ii)); the
recursion's two ties — the shallower center's witness against the
bond's exchange, and the image joined to the bond's multiple of
the witness against the diagonal — cross-multiplied at the
clearings; the four counts' site data diagonally dominant on
the box, one box read per row at the diagonal's entry less the
off-row magnitude fold (`lem:spectator`(iii)'s three counts with
the cap's two arms); the center's, the witness's and the image's
clearings positive on the box at their own certificates — the
centers' determinants the clearings' reads; and the modulus
pair's two comparisons — the tie at the floor and radius pairs'
cross-added numerator, and the defect's cap inside the radius at
the modulus's square. -/
def famRead (F : CenterFam) (B G : elim.Mat) : Prop :=
  F.Af.length = F.o ∧ elim.rowsLen F.o F.Af
  ∧ F.Cf.1.length = F.o ∧ elim.rowsLen F.o F.Cf.1
  ∧ F.Wf.1.length = F.o ∧ elim.rowsLen F.o F.Wf.1
  ∧ F.If.1.length = F.o ∧ elim.rowsLen F.o F.If.1
  ∧ elim.sqAt B F.o ∧ elim.sqAt G F.o
  ∧ matOneValue (transposeM G) G
  ∧ pfmOneValue (pfmTr F.Cf.1) F.Cf.1
  ∧ pfmOneValue (pfmTr F.If.1) F.If.1
  ∧ pfmQOneValue (pfmQmul F.Cf (pfmQshift F.Wf))
      (ofPfm (ofMatProf (transposeM B)))
  ∧ pfmQOneValue F.If
      (pfmQadd (ofPfm F.Af)
        (pfmQmul (ofPfm (ofMatProf B)) (pfmQswap F.Wf)))
  ∧ domCertGo F.e0.1 F.e0.2 0 (contrSiteF F.Wf G F.lam.1 F.lam.2)
      F.bxC
  ∧ domCertGo F.e0.1 F.e0.2 0
      (floorSiteF F.Cf G F.y0.1 F.y0.2 F.rho.1 F.rho.2) F.bxF
  ∧ domCertGo F.e0.1 F.e0.2 0 (dcapHiSiteF F.Cf F.If G F.dft.1 F.dft.2)
      F.bxU
  ∧ domCertGo F.e0.1 F.e0.2 0 (dcapLoSiteF F.Cf F.If G F.dft.1 F.dft.2)
      F.bxL
  ∧ boxRead F.Cf.2 F.e0.1 F.e0.2 F.bxClC
  ∧ boxRead F.Wf.2 F.e0.1 F.e0.2 F.bxClW
  ∧ boxRead F.If.2 F.e0.1 F.e0.2 F.bxClI
  ∧ F.y0.1 * (F.lc.1 * (F.lam.2 * F.rho.2))
      = F.lam.1 * ((F.y0.1 * F.rho.2 + F.rho.1 * F.y0.2) * F.lc.2)
  ∧ F.dft.1 * ((F.lc.2 * F.lc.2) * F.rho.2)
        + (F.lc.1 * F.lc.1) * (F.rho.1 * F.dft.2)
      ≤ F.rho.1 * (F.dft.2 * (F.lc.2 * F.lc.2))

instance instCornerblock1 (F : CenterFam) (B G : elim.Mat) :
    Decidable (famRead F B G) :=
  inferInstanceAs (Decidable
    (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
      ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The modulus' own reassociation: the triangle's out-cap weight
against the target's cross-product. -/
private theorem posM1 (rn r0d lcd rd : Pos) :
    rn * (r0d * (lcd * lcd)) * rd = rn * (lcd * lcd * rd * r0d) := by
  rw [ground.mul_assoc rn (r0d * (lcd * lcd)) rd,
    ground.mul_comm r0d (lcd * lcd),
    ground.mul_assoc (lcd * lcd) r0d rd,
    ground.mul_comm r0d rd,
    ← ground.mul_assoc (lcd * lcd) rd r0d]

/-- The triangle's summed numerator at the modulus' own spelling. -/
private theorem posM2 (lcn rn r0d r0n lcd rd : Pos) :
    lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)
      = r0n * (lcd * lcd * rd) + lcn * lcn * (rn * r0d) := by
  rw [ground.add_comm (lcn * lcn * rn * r0d) (r0n * (lcd * lcd * rd)),
    ground.mul_assoc (lcn * lcn) rn r0d]

/-- `lem:cornerblock`'s one-depth transport at the pointwise reads: the
floor, the contraction, the defect's two cap arms and the gram's
symmetry enter as their own reads with the orders' guard at the
truncating folds, and the member's ball at the shallower center
carries to the deeper center's ball — `lem:spectator`(iii)'s image
deviation joined to the center defect at the deviation's triangle,
the modulus absorbing the contracted image inside the radius. -/
theorem ball_step_of {o o' : Nat} (X Xdp Yc Ymid Ycd Cx Cc : MatQ)
    (A B G G' : Mat)
    (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (hX : sqAt X.1 o) (hXdp : sqAt Xdp.1 o') (hYc : sqAt Yc.1 o)
    (hYmid : sqAt Ymid.1 o') (hYcd : sqAt Ycd.1 o')
    (hCx : rectAt Cx.1 o o') (hCc : rectAt Cc.1 o o')
    (hA : sqAt A o') (hB : rectAt B o' o) (hG : sqAt G o)
    (hsymX : matOneValue (transposeM X.1) X.1)
    (hsymYc : matOneValue (transposeM Yc.1) Yc.1)
    (hw : oneValueQ (mulQ X Cx) (ofM (transposeM B)))
    (hj : oneValueQ (addQ Xdp (mulQ (ofM B) Cx)) (ofM A))
    (hwc : oneValueQ (mulQ Yc Cc) (ofM (transposeM B)))
    (hjc : oneValueQ (addQ Ymid (mulQ (ofM B) Cc)) (ofM A))
    (hDhi : ∀ u : List BPair, u.length = o →
      (quadForm (devQ X Yc).1 u).scale rd
        ≤ (quadForm G u).scale (rn * (devQ X Yc).2))
    (hDlo : ∀ u : List BPair, u.length = o →
      ((quadForm G u).scale (rn * (devQ X Yc).2)).swap
        ≤ (quadForm (devQ X Yc).1 u).scale rd)
    (hFp : ∀ u : List BPair, u.length = o →
      (quadForm G u).scale (Yc.2 * (y0n * rd + rn * y0d))
        ≤ (quadForm Yc.1 u).scale (y0d * rd))
    (hconp : ∀ u : List BPair, u.length = o' →
      (quadForm G (matVec (transfer Cc).1 u)).scale (ld * ld)
        ≤ (quadForm G' u).scale (ln * ln * (Cc.2 * Cc.2)))
    (hsymG : matOneValue (transposeM G) G)
    (hnz : o = 0 → o' = 0)
    (hdefHi : ∀ w : List BPair, w.length = o' →
      (quadForm (devQ Ymid Ycd).1 w).scale r0d
        ≤ (quadForm G' w).scale (r0n * (devQ Ymid Ycd).2))
    (hdefLo : ∀ w : List BPair, w.length = o' →
      ((quadForm G' w).scale (r0n * (devQ Ymid Ycd).2)).swap
        ≤ (quadForm (devQ Ymid Ycd).1 w).scale r0d)
    (htie : y0n * (lcn * (ld * rd))
      = ln * ((y0n * rd + rn * y0d) * lcd))
    (hmod : r0n * ((lcd * lcd) * rd) + (lcn * lcn) * (rn * r0d)
      ≤ rn * (r0d * (lcd * lcd))) :
    (∀ u : List BPair, u.length = o' →
      (quadForm (devQ Xdp Ycd).1 u).scale rd
        ≤ (quadForm G' u).scale (rn * (devQ Xdp Ycd).2))
    ∧ (∀ u : List BPair, u.length = o' →
      ((quadForm G' u).scale (rn * (devQ Xdp Ycd).2)).swap
        ≤ (quadForm (devQ Xdp Ycd).1 u).scale rd) := by
  have hI := spectator.image_contract_of X Xdp Yc Ymid Cx Cc A B G G'
    ln ld y0n y0d rn rd lcn lcd hX hXdp hYc hYmid hCx hCc
    hA hB hG hsymX hsymYc hw hj hwc hjc hDhi hDlo hFp hconp hsymG
    hnz htie
  have htri := spectator.dev_triangle Xdp Ymid Ycd G'
    (lcn * lcn * rn) (lcd * lcd * rd) r0n r0d hXdp hYmid hYcd
    hI.1 hI.2 hdefHi hdefLo
  have hpos : ∀ u : List BPair, u.length = o' →
      BPair.unit ≤ quadForm G' u := by
    intro u hu
    exact ground.unitLeOfScale
      (ground.unitLeOfSwap (ground.leB_trans (hdefLo u hu) (hdefHi u hu)))
  have hcle : lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)
      ≤ rn * (r0d * (lcd * lcd)) := by
    rw [posM2 lcn rn r0d r0n lcd rd]
    exact hmod
  have hcrd : (lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)) * rd
      ≤ rn * (lcd * lcd * rd * r0d) := by
    have h := ground.mul_le_mul_right rd hcle
    rw [posM1 rn r0d lcd rd] at h
    exact h
  have hkey : (lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd))
        * (devQ Xdp Ycd).2 * rd
      ≤ rn * (devQ Xdp Ycd).2 * (lcd * lcd * rd * r0d) := by
    have h := ground.mul_le_mul_right (devQ Xdp Ycd).2 hcrd
    rw [ground.mul_right_comm
        (lcn * lcn * rn * r0d + r0n * (lcd * lcd * rd)) rd
        (devQ Xdp Ycd).2,
      ground.mul_right_comm rn (lcd * lcd * rd * r0d)
        (devQ Xdp Ycd).2] at h
    exact h
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · refine ground.leB_of_scale (w := lcd * lcd * rd * r0d) ?_
    rw [BPair.scale_scale, BPair.scale_scale]
    refine ground.leB_trans ?_ (ground.leB_scaleMono (hpos u hu) hkey)
    have h1 := ground.leB_scale (htri.1 u hu) rd
    rw [BPair.scale_scale, BPair.scale_scale] at h1
    rw [ground.mul_comm rd (lcd * lcd * rd * r0d)]
    exact h1
  · refine ground.leB_of_scale (w := lcd * lcd * rd * r0d) ?_
    rw [← BPair.scale_swap, BPair.scale_scale, BPair.scale_scale]
    refine ground.leB_trans
      (ground.leB_swap (ground.leB_scaleMono (hpos u hu) hkey)) ?_
    have h2 := ground.leB_scale (htri.2 u hu) rd
    rw [← BPair.scale_swap, BPair.scale_scale, BPair.scale_scale] at h2
    rw [ground.mul_comm rd (lcd * lcd * rd * r0d)]
    exact h2

/-- The seed's weight move: the member's clearing rides out of the
boundary block's own expansion. -/
private theorem seedShift (a b : BPair) (x y : Pos) :
    (a.scale x).scale y + b.scale x
      = (a.scale y + b.scale Pos.one).scale x := by
  rw [BPair.scale_add, BPair.scale_scale a x y,
    BPair.scale_scale a y x, BPair.scale_scale b Pos.one x,
    ground.one_mul x, ground.mul_comm y x]

/-- The seed's radius weight at the member's clearing. -/
private theorem posSeed (rn y x : Pos) :
    rn * (Pos.one * y) * x = rn * (x * y) := by
  rw [ground.one_mul y, ground.mul_assoc rn y x, ground.mul_comm y x]

/-- The seed arm's transport: the boundary seed's cap at the boundary
block carries to the seed pivot, the two deviations congruent at
the pivot's own clearing. -/
private theorem seedCap {o : Nat} (X Yc : MatQ) (A G : Mat)
    (rn rd : Pos)
    (hX : sqAt X.1 o) (hYc : sqAt Yc.1 o) (hA : sqAt A o)
    (hXA : oneValueQ X (ofM A))
    (hhi : ∀ u : List BPair, u.length = o →
      (quadForm (devQ (ofM A) Yc).1 u).scale rd
        ≤ (quadForm G u).scale (rn * (devQ (ofM A) Yc).2))
    (hlo : ∀ u : List BPair, u.length = o →
      ((quadForm G u).scale (rn * (devQ (ofM A) Yc).2)).swap
        ≤ (quadForm (devQ (ofM A) Yc).1 u).scale rd) :
    (∀ u : List BPair, u.length = o →
      (quadForm (devQ X Yc).1 u).scale rd
        ≤ (quadForm G u).scale (rn * (devQ X Yc).2))
    ∧ (∀ u : List BPair, u.length = o →
      ((quadForm G u).scale (rn * (devQ X Yc).2)).swap
        ≤ (quadForm (devQ X Yc).1 u).scale rd) := by
  have hXAm : matOneValue X.1 (matScale X.2 A) := by
    have h0 : matOneValue (matScale Pos.one X.1) (matScale X.2 A) :=
      hXA
    rw [matScale_one] at h0
    exact h0
  have hcg : ∀ u : List BPair, u.length = o →
      (quadForm (devQ X Yc).1 u).oneValue
        ((quadForm (devQ (ofM A) Yc).1 u).scale X.2) := by
    intro u hu
    have hq : (quadForm X.1 u).oneValue ((quadForm A u).scale X.2) :=
      BPair.oneValue_trans
        (dotN_matVec_congrM X.1 (matScale X.2 A) u u hXAm)
        (quadForm_scale X.2 A u)
    refine BPair.oneValue_trans
      (spectator.dev_expand X Yc u ((sqAt_len hX).trans hu.symm)
        (by rw [hu]; exact rowsLen_of_sqAt hX)
        ((sqAt_len hYc).trans hu.symm)
        (by rw [hu]; exact rowsLen_of_sqAt hYc)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.scale_congr Yc.2 hq)
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (seedShift (quadForm A u) ((quadForm Yc.1 u).swap)
          X.2 Yc.2)) ?_
    exact BPair.scale_congr X.2
      (BPair.oneValue_symm
        (spectator.dev_expand (ofM A) Yc u
          ((sqAt_len hA).trans hu.symm)
          (by rw [hu]; exact rowsLen_of_sqAt hA)
          ((sqAt_len hYc).trans hu.symm)
          (by rw [hu]; exact rowsLen_of_sqAt hYc)))
  have hps : rn * (devQ (ofM A) Yc).2 * X.2 = rn * (devQ X Yc).2 :=
    posSeed rn Yc.2 X.2
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.scale_congr rd (hcg u hu))) ?_
    refine ground.leB_congr
      (BPair.oneValue_of_eq
        (BPair.scale_comm (quadForm (devQ (ofM A) Yc).1 u) rd X.2))
      (BPair.oneValue_of_eq
        ((BPair.scale_scale (quadForm G u)
            (rn * (devQ (ofM A) Yc).2) X.2).trans
          (congrArg (BPair.scale (quadForm G u)) hps)))
      (ground.leB_scale (hhi u hu) X.2)
  · refine ground.leB_congr_right
      (BPair.oneValue_symm (BPair.scale_congr rd (hcg u hu))) ?_
    refine ground.leB_congr
      (BPair.oneValue_of_eq
        ((BPair.scale_swap
            ((quadForm G u).scale (rn * (devQ (ofM A) Yc).2)) X.2).trans
          (congrArg BPair.swap
            ((BPair.scale_scale (quadForm G u)
                (rn * (devQ (ofM A) Yc).2) X.2).trans
              (congrArg (BPair.scale (quadForm G u)) hps)))))
      (BPair.oneValue_of_eq
        (BPair.scale_comm (quadForm (devQ (ofM A) Yc).1 u) rd X.2))
      (ground.leB_scale (hlo u hu) X.2)

/-- The tail recursion's read at the deeper segment. -/
private theorem tailTail {A A' B : Mat} {As Bs : List Mat}
    {X X' R : MatQ} {Xt Rt : List MatQ} {n n' : Nat} {nt : List Nat}
    (h : tailRead (A :: A' :: As) (B :: Bs) (X :: X' :: Xt) (R :: Rt)
      (n :: n' :: nt)) :
    tailRead (A' :: As) Bs (X' :: Xt) Rt (n' :: nt) :=
  ⟨h.1.2.2.2, h.2.1.2, h.2.2.1.2, h.2.2.2.2⟩

/-- `lem:cornerblock`'s rebound at the crossing block: the join's
withdrawn term is the recursion witness's sandwich of the crossing
pivot, whose form the withdrawn-diagonal read prices — the
positive part at the crossing's stated presentation, the lower
unit at an order-one block — so the following pivot sits at or
beyond its diagonal less the transfer, the crossing pivot's
symmetry the split's own read and the display cleared at the
congruence determinant's square with the witness clearing entering
squared. -/
theorem crossing_rebound {o o' : Nat} (Xf Xc R : MatQ) (A B : Mat)
    (sp : Split o')
    (hk : 0 < o) (hk' : 0 < o')
    (hXf : sqAt Xf.1 o)
    (hB : rectAt B o o') (hR : rectAt R.1 o' o)
    (hwit : oneValueQ (mulQ Xc R) (ofM (transposeM B)))
    (hjoin : oneValueQ (addQ Xf (mulQ (ofM B) R)) (ofM A))
    (hsp : splitRead Xc.1 sp) :
    ∀ u : List BPair, u.length = o →
      minor sp.T.val * minor sp.T.val
          * ((quadForm A u).scale (Xc.2 * (Xf.2 * (R.2 * R.2))))
        ≤ minor sp.T.val * minor sp.T.val
            * ((quadForm Xf.1 u).scale (Xc.2 * (R.2 * R.2)))
          + (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
              (matVec sp.Tw.val (matVec R.1 u))).scale Xf.2 := by
  intro u hu
  have hXc : sqAt Xc.1 o' := hsp.1
  have hsymC : matOneValue (transposeM Xc.1) Xc.1 :=
    matOne_symm (splitRead_symm Xc.1 sp hsp)
  have hRl : R.1.length = o' := rectAt_len hR
  have hRr : rowsLen o R.1 := rectAt_rows hR
  have hXcl : Xc.1.length = o' := sqAt_len hXc
  have hXcr : rowsLen o' Xc.1 := rowsLen_of_sqAt hXc
  have hRTr : rowsLen o' (transposeM R.1) :=
    rowsLen_cast hRl (rowsLen_transposeM R.1)
  have hv : (matVec R.1 u).length = o' :=
    (matVec_length R.1 u).trans hRl
  have hS := greenprod.withdrawn_sandwich (k := o) (k' := o') Xc R B
    hk hk' hXc hB hR hsymC hwit
  have hAs : matOneValue (matMul (matMul (transposeM R.1) Xc.1) R.1)
      (matMul (transposeM R.1) (matMul Xc.1 R.1)) :=
    matMul_assoc (transposeM R.1) Xc.1 R.1 hRTr hXcr hRr hXcl hRl
      hk' hk'
  have hBRX : ((quadForm (matMul B R.1) u).scale
      (Xc.2 * R.2)).oneValue (quadForm Xc.1 (matVec R.1 u)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (quadForm_scale (Xc.2 * R.2) (matMul B R.1) u)) ?_
    refine BPair.oneValue_trans (quadMatOne _ _ u hS) ?_
    refine BPair.oneValue_trans (quadMatOne _ _ u hAs) ?_
    exact BPair.oneValue_symm
      (congQuad Xc.1 R.1 o' o hXc hRr hRl u hu)
  have hJF := greenprod.join_quadSplit Xf R A B hk' hXf hB hR hjoin u hu
  have hEqL : (Xf.2 * R.2) * (Xc.2 * R.2)
      = Xc.2 * (Xf.2 * (R.2 * R.2)) := by
    rw [ground.mul_comm (Xf.2 * R.2) (Xc.2 * R.2),
      ground.mul_assoc Xc.2 R.2 (Xf.2 * R.2),
      ground.mul_comm Xf.2 R.2, ← ground.mul_assoc R.2 R.2 Xf.2,
      ground.mul_comm (R.2 * R.2) Xf.2]
  have hEqR : R.2 * (Xc.2 * R.2) = Xc.2 * (R.2 * R.2) := by
    rw [ground.mul_comm Xc.2 R.2,
      ← ground.mul_assoc R.2 R.2 Xc.2,
      ground.mul_comm (R.2 * R.2) Xc.2]
  have hStep1 : (quadForm A u).scale (Xc.2 * (Xf.2 * (R.2 * R.2)))
      = ((quadForm A u).scale (Xf.2 * R.2)).scale
          (Xc.2 * R.2) := by
    rw [BPair.scale_scale, hEqL]
  have hStep3 : ((quadForm Xf.1 u).scale R.2
        + (quadForm (matMul B R.1) u).scale Xf.2).scale (Xc.2 * R.2)
      = (quadForm Xf.1 u).scale (Xc.2 * (R.2 * R.2))
        + ((quadForm (matMul B R.1) u).scale (Xc.2 * R.2)).scale
            Xf.2 := by
    rw [BPair.scale_add, BPair.scale_scale, hEqR, BPair.scale_comm]
  have hL : (minor sp.T.val * minor sp.T.val
      * ((quadForm A u).scale
          (Xc.2 * (Xf.2 * (R.2 * R.2))))).oneValue
      (minor sp.T.val * minor sp.T.val
          * ((quadForm Xf.1 u).scale (Xc.2 * (R.2 * R.2)))
        + minor sp.T.val * minor sp.T.val
          * ((quadForm Xc.1 (matVec R.1 u)).scale Xf.2)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl
        (minor sp.T.val * minor sp.T.val)) ?_)
      (BPair.oneValue_of_eq (BPair.left_distrib _ _ _))
    refine BPair.oneValue_trans (BPair.oneValue_of_eq hStep1) ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (Xc.2 * R.2) hJF) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq hStep3) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.scale_congr Xf.2 hBRX)
  have hle2 : minor sp.T.val * minor sp.T.val
      * ((quadForm Xc.1 (matVec R.1 u)).scale Xf.2)
      ≤ (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec sp.Tw.val (matVec R.1 u))).scale Xf.2 := by
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq
        (BPair.mul_scale (minor sp.T.val * minor sp.T.val)
          (quadForm Xc.1 (matVec R.1 u)) Xf.2).symm) ?_
    exact ground.leB_scale
      (split_posPart Xc.1 sp hsp (matVec R.1 u) hv) Xf.2
  exact ground.leB_congr_left (BPair.oneValue_symm hL)
    (ground.leB_add (ground.leB_refl _) hle2)

set_option genInjectivity false in
/-- One deep depth's dominance data: the order, the diagonal's
floor pair, the depth's floor pair, and the floor's split. -/
structure DomStep where
  ord : Nat
  dg : Pos × Pos
  fl : Pos × Pos
  spM : Split ord

/-- The dominance tail's read, deep-first in lockstep with the
chain: per depth the diagonal's floor at the coordinates' fold of
squares and the depth's floor pair, per bond the square's cap, each
deeper depth one cross-multiplied comparison, and the seed arm at
the crossing's following depth — the crossing's split, the
transfer's cap at the congruence witness's solve, and the seed
comparison, the diagonal's floor at or beyond the seed floor joined
to the transfer's cap (`lem:cornerblock`). -/
def domRead (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    List Mat → List Mat → List MatQ → List MatQ → List Nat →
    List DomStep → List ((k : Nat) × (Pos × Pos) × Split k) → Prop
  | A :: _ :: _, _ :: _, _ :: X' :: _, R :: _, n :: n' :: _,
      [D], [] =>
      D.ord = n ∧ spc.1 = n' ∧ spT.1 = n
      ∧ splitRead X'.1 spc.2
      ∧ leAt (matScale D.dg.1 (idMat n)) (matScale D.dg.2 A) D.spM
      ∧ leAt
          (matScale td (matMul
            (transposeM (matMul spc.2.Tw.val R.1))
            (matMul (blockMat (posBlocks spc.2.blocks) spc.2.kern)
              (matMul spc.2.Tw.val R.1))))
          (matScaleB
            ((minor spc.2.T.val * minor spc.2.T.val)
              * BPair.ofPos (tn * (X'.2 * (R.2 * R.2))))
            (idMat n))
          spT.2
      ∧ (D.fl.1 * td + tn * D.fl.2) * D.dg.2 ≤ D.dg.1 * (D.fl.2 * td)
  | A :: A' :: As, B :: Bs, _ :: X' :: Xs, _ :: Rs, n :: n' :: ns,
      D :: D' :: Ds, C :: Cs =>
      (D.ord = n ∧ C.1 = n
       ∧ leAt (matScale D.dg.1 (idMat n)) (matScale D.dg.2 A) D.spM
       ∧ leAt (matScale C.2.1.2 (matMul B (transposeM B)))
           (matScale C.2.1.1 (idMat n)) C.2.2
       ∧ D.fl.1 * (D.dg.2 * (C.2.1.2 * D'.fl.1))
           + C.2.1.1 * (D'.fl.2 * (D.dg.2 * D.fl.2))
         ≤ D.dg.1 * (D.fl.2 * (C.2.1.2 * D'.fl.1)))
      ∧ domRead spc spT tn td (A' :: As) Bs (X' :: Xs) Rs
          (n' :: ns) (D' :: Ds) Cs
  | [], _, _, _, _, _, _ => False
  | [_], _, _, _, _, _, _ => False
  | _ :: _ :: _, [], _, _, _, _, _ => False
  | _ :: _ :: _, _ :: _, [], _, _, _, _ => False
  | _ :: _ :: _, _ :: _, [_], _, _, _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [],
      _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [] => False

def decDomRead (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
    Decidable (domRead spc spT tn td diag off Xs Rs ns Ds Cs)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [] =>
      inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xs, _ :: Rs, _ :: n' :: ns,
      _ :: D' :: Ds, _ :: Cs =>
      @instDecidableAnd _ _
        (inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _)))
        (decDomRead spc spT tn td (A' :: As) Bs (X' :: Xs) Rs
          (n' :: ns) (D' :: Ds) Cs)
  | [], _, _, _, _, _, _ => isFalse (fun h => h)
  | [_], _, _, _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, [], _, _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [], _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [_], _, _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _ =>
      isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _ =>
      isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _ =>
      isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [],
      _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [] => isFalse (fun h => h)

instance instCornerblock2 (spc spT : (k : Nat) × Split k) (tn td : Pos)
    (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
    (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)) :
    Decidable (domRead spc spT tn td diag off Xs Rs ns Ds Cs) :=
  decDomRead spc spT tn td diag off Xs Rs ns Ds Cs

/-! The seed floor's weights: the diagonal comparison, the rebound
and the transfer's cap meet at one clearing, the seed comparison's
two terms priced there and the conclusion's own weight the shared
clearing's cofactor. -/

/-- The diagonal comparison's weight at the tail's clearing. -/
private theorem posD1 (md f W fd td : Pos) :
    md * (f * W * fd * td) = f * W * fd * md * td := by
  rw [ground.mul_left_comm md (f * W * fd) td,
    ← ground.mul_assoc (f * W * fd) md td]

/-- The rebound's weight at the tail's clearing. -/
private theorem posD2 (f W fd md td : Pos) :
    f * W * (fd * md * td) = f * W * fd * md * td := by
  rw [← ground.mul_assoc (f * W) (fd * md) td,
    ← ground.mul_assoc (f * W) fd md]

/-- The seed comparison's upper weight at the tail's clearing. -/
private theorem posD4 (mn fd td f W : Pos) :
    mn * (fd * td) * (f * W) = mn * (f * W * fd * td) := by
  rw [ground.mul_assoc mn (fd * td) (f * W),
    ground.mul_comm (fd * td) (f * W),
    ← ground.mul_assoc (f * W) fd td]

/-- The seed comparison's lower weight splits at its two terms. -/
private theorem posD5 (fn tn td fd md f W : Pos) :
    (fn * td + tn * fd) * md * (f * W)
      = fn * td * md * (f * W) + tn * fd * md * (f * W) := by
  rw [ground.right_distrib (fn * td) (tn * fd) md,
    ground.right_distrib (fn * td * md) (tn * fd * md) (f * W)]

/-- The comparison's transfer term reads the cap's own weight. -/
private theorem posD6 (tn fd md f W : Pos) :
    tn * fd * md * (f * W) = tn * W * (f * (fd * md)) := by
  rw [ground.mul_assoc (tn * fd) md (f * W),
    ground.mul_assoc tn fd (md * (f * W)),
    ground.mul_left_comm md f W,
    ground.mul_left_comm fd f (md * W),
    ground.mul_comm md W,
    ground.mul_assoc tn W (f * (fd * md)),
    ground.mul_left_comm W f (fd * md),
    ground.mul_left_comm W fd md]

/-- The comparison's floor term reads the conclusion's weight at
the shared clearing. -/
private theorem posD7 (fn td md f W : Pos) :
    fn * td * md * (f * W) = fn * f * (td * md * W) := by
  rw [ground.mul_assoc (fn * td) md (f * W),
    ground.mul_assoc fn td (md * (f * W)),
    ground.mul_left_comm md f W,
    ground.mul_left_comm td f (md * W),
    ground.mul_assoc fn f (td * md * W),
    ground.mul_assoc td md W]

/-- The rebound's pivot term reads the conclusion's weight at the
shared clearing. -/
private theorem posD8 (W fd md td : Pos) :
    W * (fd * md * td) = fd * (td * md * W) := by
  rw [ground.mul_assoc fd md td,
    ground.mul_left_comm W fd (md * td),
    ground.mul_assoc td md W,
    ground.mul_left_comm W md td,
    ground.mul_left_comm td md W,
    ground.mul_comm W td]

/-- The dominance step's close: the diagonal's floor carried
through the rebound and priced against the transfer's cap leaves
the following pivot's own floor, the shared transfer term and the
crossing clearing withdrawing at the cross-multiplied
comparison. -/
private theorem domClose {M n qa qf p : BPair}
    (f W mn md tn td fn fd : Pos)
    (hMu : BPair.unit < M) (hn : BPair.unit ≤ n)
    (hD : n.scale mn ≤ qa.scale md)
    (hR : M * qa.scale (f * W) ≤ M * qf.scale W + p.scale f)
    (hT : p.scale td ≤ M * n.scale (tn * W))
    (hC : (fn * td + tn * fd) * md ≤ mn * (fd * td)) :
    n.scale (fn * f) ≤ qf.scale fd := by
  have hM : BPair.unit ≤ M := ground.leB_of_lt hMu
  have hMN : BPair.unit ≤ M * n := ground.unitLeMul hM hn
  have s1 : (M * n).scale (mn * (f * W * fd * td))
      ≤ (M * qa).scale (f * W * fd * md * td) := by
    have h := ground.leB_mulR hM (ground.leB_scale hD (f * W * fd * td))
    rw [BPair.scale_scale, BPair.scale_scale, BPair.mul_scale,
      BPair.mul_scale, posD1 md f W fd td] at h
    exact h
  have s2 : (M * qa).scale (f * W * fd * md * td)
      ≤ (M * qf).scale (W * (fd * md * td))
        + p.scale (f * (fd * md * td)) := by
    have h := ground.leB_scale hR (fd * md * td)
    rw [BPair.scale_add, BPair.mul_scale, BPair.scale_scale,
      BPair.mul_scale, BPair.scale_scale, BPair.scale_scale,
      posD2 f W fd md td] at h
    exact h
  have s3 : p.scale (f * (fd * md * td))
      ≤ (M * n).scale (tn * W * (f * (fd * md))) := by
    have h := ground.leB_scale hT (f * (fd * md))
    rw [BPair.scale_scale, BPair.mul_scale, BPair.scale_scale,
      ground.mul_rotate f (fd * md) td] at h
    exact h
  have s4 : (M * n).scale (mn * (f * W * fd * td))
      ≤ (M * qf).scale (W * (fd * md * td))
        + (M * n).scale (tn * W * (f * (fd * md))) :=
    ground.leB_trans (ground.leB_trans s1 s2)
      (ground.leB_add (ground.leB_refl _) s3)
  have hC2 : (fn * td + tn * fd) * md * (f * W)
      ≤ mn * (fd * td) * (f * W) :=
    ground.mul_le_mul_right (f * W) hC
  have s5 : (M * n).scale (fn * td * md * (f * W))
        + (M * n).scale (tn * W * (f * (fd * md)))
      ≤ (M * n).scale (mn * (f * W * fd * td)) := by
    have h := ground.leB_scaleMono hMN hC2
    rw [posD5 fn tn td fd md f W, BPair.scale_addW,
      posD6 tn fd md f W, posD4 mn fd td f W] at h
    exact h
  have s6 : (M * n).scale (tn * W * (f * (fd * md)))
        + (M * n).scale (fn * td * md * (f * W))
      ≤ (M * n).scale (tn * W * (f * (fd * md)))
        + (M * qf).scale (W * (fd * md * td)) :=
    ground.leB_congr (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (ground.leB_trans s5 s4)
  have s7 : (M * n).scale (fn * td * md * (f * W))
      ≤ (M * qf).scale (W * (fd * md * td)) := ground.leB_cancelL s6
  have s8 : ((M * n).scale (fn * f)).scale (td * md * W)
      ≤ ((M * qf).scale fd).scale (td * md * W) := by
    rw [BPair.scale_scale, BPair.scale_scale, ← posD7 fn td md f W,
      ← posD8 W fd md td]
    exact s7
  refine ground.leB_unscale_left hMu ?_
  rw [BPair.mul_scale, BPair.mul_scale]
  exact ground.leB_of_scale s8

/-- The rebound's seed floor: the following pivot clears the
diagonal's floor less the transfer's cap. -/
theorem rebound_floor {o o' : Nat} (Xf Xc R : MatQ) (A B : Mat)
    (sp : Split o') (mn md tn td fn fd : Pos) :
    0 < o → 0 < o' →
    sqAt Xf.1 o → rectAt B o o' → rectAt R.1 o' o →
    oneValueQ (mulQ Xc R) (ofM (transposeM B)) →
    oneValueQ (addQ Xf (mulQ (ofM B) R)) (ofM A) →
    splitRead Xc.1 sp →
    (∀ u : List BPair, u.length = o →
      (dotN u u).scale mn ≤ (quadForm A u).scale md) →
    (∀ u : List BPair, u.length = o →
      (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec (matMul sp.Tw.val R.1) u)).scale td
        ≤ minor sp.T.val * minor sp.T.val
            * ((dotN u u).scale (tn * (Xc.2 * (R.2 * R.2))))) →
    (fn * td + tn * fd) * md ≤ mn * (fd * td) →
    ∀ u : List BPair, u.length = o →
      (dotN u u).scale (fn * Xf.2)
        ≤ (quadForm Xf.1 u).scale fd := by
  intro hk hk' hXf hB hR hwit hjoin hsp hdiag htcap hcomp u hu
  have hMu : BPair.unit < minor sp.T.val * minor sp.T.val :=
    ground.sq_pos hsp.2.1.1
  have hn : BPair.unit ≤ dotN u u :=
    ground.leB_of_not_lt (elim.dotN_self_side u)
  have hrb := crossing_rebound Xf Xc R A B sp hk hk' hXf hB hR hwit
    hjoin hsp u hu
  rw [ground.mul_left_comm Xc.2 Xf.2 (R.2 * R.2)] at hrb
  have hT := ground.leB_congr_left
    (BPair.scale_congr td
      (inertia.quadForm_congr (blockMat (posBlocks sp.blocks) sp.kern)
        (elim.matVec_matMul sp.Tw.val R.1 o (rectAt_rows hR) u hu)))
    (htcap u hu)
  exact domClose Xf.2 (Xc.2 * (R.2 * R.2)) mn md tn td fn fd hMu hn
    (hdiag u hu) hrb hT hcomp

/-! The dominance walk's reads: the slab's own order, the two
floor data at the coordinates' fold of squares, and the transfer's
cap at the crossing's compression. -/

/-- The withdrawn diagonal keeps the block widths: the withdrawn
order-one entry and every further block carry their own order. -/
private theorem widthOf_posBlocks : ∀ (bs : List SBlock) (k : Nat),
    widthOf (posBlocks bs) k = widthOf bs k
  | [], _ => rfl
  | SBlock.one a :: bs, k =>
    match (inferInstance : Decidable (a < BPair.unit)) with
    | isTrue hg => by
      have hpos := posBlocks_cons_lt bs hg
      rw [hpos]
      exact widthOf_posBlocks bs (k + 1)
    | isFalse hg => by
      have hpos := posBlocks_cons_ge bs hg
      rw [hpos]
      exact widthOf_posBlocks bs (k + 1)
  | SBlock.two _ _ _ :: bs, k => widthOf_posBlocks bs (k + 2)

/-- The withdrawn diagonal's block matrix keeps the split's stated
order. -/
private theorem sqAt_posBlockMat {m : Nat} (sp : Split m) :
    sqAt (blockMat (posBlocks sp.blocks) sp.kern) m := by
  have hw : widthOf (posBlocks sp.blocks) sp.kern = m :=
    (widthOf_posBlocks sp.blocks sp.kern).trans
      (ground.beqEq _ _ sp.width)
  exact sqAt_of ((blockMat_len _ _).trans hw)
    (rowsLen_cast hw (blockMat_rows _ _))

/-- The diagonal's floor at a slab: the comparison's read prices
the coordinates' fold of squares against the slab's own form. -/
private theorem diagFloor {k n : Nat} (A : Mat) (dn dd : Pos)
    (sp : Split k) (hk : k = n) (hA : sqAt A n)
    (h : leAt (matScale dn (idMat n)) (matScale dd A) sp) :
    ∀ u : List BPair, u.length = n →
      (dotN u u).scale dn ≤ (quadForm A u).scale dd := by
  subst hk
  intro u hu
  refine ground.leB_congr ?_ (quadForm_scale dd A u)
    (le_all (matScale dn (idMat k)) (matScale dd A) sp
      (sqAt_matScale k dn (idMat k) (sqAt_idMat k))
      (sqAt_matScale k dd A hA) h u hu)
  exact BPair.oneValue_trans (quadForm_scale dn (idMat k) u)
    (BPair.scale_congr dn (quadForm_idMat k u hu))

/-- The bond's square cap at a slab: the comparison's read prices
the bond square's form against the coordinates' fold of squares. -/
private theorem bondCap {k n n' : Nat} (B : Mat) (bn bd : Pos)
    (sp : Split k) (hk : k = n) (hn : 0 < n) (hn' : 0 < n')
    (hB : rectAt B n n')
    (h : leAt (matScale bd (matMul B (transposeM B)))
      (matScale bn (idMat n)) sp) :
    ∀ u : List BPair, u.length = n →
      (quadForm (matMul B (transposeM B)) u).scale bd
        ≤ (dotN u u).scale bn := by
  subst hk
  intro u hu
  have hBl : B.length = k := rectAt_len hB
  have hBTl : (transposeM B).length = n' :=
    length_transposeM B (rectAt_rows hB) (by rw [hBl]; exact hn)
  have hBTr : rowsLen k (transposeM B) :=
    rowsLen_cast hBl (rowsLen_transposeM B)
  have hBB : sqAt (matMul B (transposeM B)) k :=
    sqAt_of ((length_matMul B (transposeM B)).trans hBl)
      (rowsLen_matMul_of B (transposeM B)
        (fun _ => by rw [hBTl]; exact hn') hBTr)
  refine ground.leB_congr (quadForm_scale bd _ u) ?_
    (le_all (matScale bd (matMul B (transposeM B)))
      (matScale bn (idMat k)) sp
      (sqAt_matScale k bd _ hBB)
      (sqAt_matScale k bn (idMat k) (sqAt_idMat k)) h u hu)
  exact BPair.oneValue_trans (quadForm_scale bn (idMat k) u)
    (BPair.scale_congr bn (quadForm_idMat k u hu))

/-- The transfer's cap at the crossing's compression: the
comparison's read prices the withdrawn diagonal's form at the
carried vector against the coordinates' fold of squares, the
congruence determinant's square riding on the cap. -/
private theorem transferCap {j m n : Nat} (sp : Split m) (P : Mat)
    (w td : Pos) (spT : Split j) (hj : j = n)
    (hm : 0 < m) (hPl : P.length = m) (hPr : rowsLen n P)
    (h : leAt (matScale td (matMul (transposeM P)
        (matMul (blockMat (posBlocks sp.blocks) sp.kern) P)))
      (matScaleB ((minor sp.T.val * minor sp.T.val) * BPair.ofPos w)
        (idMat n)) spT) :
    ∀ u : List BPair, u.length = n →
      (quadForm (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec P u)).scale td
        ≤ minor sp.T.val * minor sp.T.val * ((dotN u u).scale w) := by
  subst hj
  intro u hu
  have hBM : sqAt (blockMat (posBlocks sp.blocks) sp.kern) m :=
    sqAt_posBlockMat sp
  have hPpos : 0 < P.length := by rw [hPl]; exact hm
  have hYl : (matMul (blockMat (posBlocks sp.blocks) sp.kern) P).length
      = m := (length_matMul _ P).trans (sqAt_len hBM)
  have hYr : rowsLen j
      (matMul (blockMat (posBlocks sp.blocks) sp.kern) P) :=
    rowsLen_matMul_of _ P (fun _ => hPpos) hPr
  have hPTl : (transposeM P).length = j :=
    length_transposeM P hPr hPpos
  refine ground.leB_congr ?_ ?_
    (le_all _ _ spT
      (sqAt_matScale j td _
        (sqAt_of ((length_matMul _ _).trans hPTl)
          (rowsLen_matMul_of _ _ (fun _ => by rw [hYl]; exact hm) hYr)))
      (sqAt_scaleB _ j (idMat j) (sqAt_idMat j)) h u hu)
  · exact BPair.oneValue_trans (quadForm_scale td _ u)
      (BPair.scale_congr td
        (BPair.oneValue_symm (congQuad _ P m j hBM hPr hPl u hu)))
  · refine BPair.oneValue_trans (quadForm_scaleB _ (idMat j) u) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (elim.dotN_congrR u (matVec (idMat j) u) u
          (matVec_idMat j u hu))) ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.ofPos_scale w (dotN u u)))

/-- The step comparison's upper weight at the depth's clearing. -/
private theorem posE1 (mn fd G f r : Pos) :
    mn * (fd * G) * (f * r) = mn * (f * r) * (G * fd) := by
  rw [ground.mul_assoc mn (fd * G) (f * r),
    ground.mul_comm (fd * G) (f * r),
    ground.mul_comm fd G,
    ← ground.mul_assoc mn (f * r) (G * fd)]

/-- The step comparison's bond term reads the sandwich's own
weight. -/
private theorem posE3 (b1 g2 md fd f r : Pos) :
    b1 * (g2 * (md * fd)) * (f * r) = b1 * (g2 * r) * (f * md * fd) := by
  rw [ground.mul_assoc b1 (g2 * (md * fd)) (f * r),
    ground.mul_assoc g2 (md * fd) (f * r),
    ground.mul_assoc b1 (g2 * r) (f * md * fd),
    ground.mul_assoc g2 r (f * md * fd),
    ground.mul_mul_mul_comm md fd f r,
    ground.mul_left_comm r (f * md) fd,
    ground.mul_comm md f,
    ground.mul_comm fd r]

/-- The join's pivot term reads the conclusion's weight at the
shared clearing. -/
private theorem posE4 (r md G fd : Pos) :
    r * md * (G * fd) = fd * (md * G * r) := by
  rw [ground.mul_comm fd (md * G * r),
    ground.mul_assoc (md * G) r fd,
    ground.mul_mul_mul_comm md G r fd,
    ground.mul_comm r md]

/-- The dominance step's close: the diagonal's floor carried
through the join and priced against the bond's sandwich leaves the
depth's own floor, the shared bond term and the witness clearing
withdrawing at the cross-multiplied comparison. -/
private theorem domStepClose {n0 qa qf p : BPair}
    (f r mn md fn fd g2 b1 G : Pos)
    (hn : BPair.unit ≤ n0)
    (hD : n0.scale mn ≤ qa.scale md)
    (hJ : (qa.scale (f * r)).oneValue (qf.scale r + p.scale f))
    (hT : p.scale G ≤ n0.scale (b1 * (g2 * r)))
    (hC : fn * (md * G) + b1 * (g2 * (md * fd))
      ≤ mn * (fd * G)) :
    n0.scale (fn * f) ≤ qf.scale fd := by
  have s1 : n0.scale (mn * (f * r)) ≤ (qa.scale (f * r)).scale md := by
    have h := ground.leB_scale hD (f * r)
    rw [BPair.scale_scale, BPair.scale_comm qa md (f * r)] at h
    exact h
  have s2 : n0.scale (mn * (f * r))
      ≤ qf.scale (r * md) + p.scale (f * md) := by
    refine ground.leB_congr_right ?_ s1
    refine BPair.oneValue_trans (BPair.scale_congr md hJ) ?_
    rw [BPair.scale_add, BPair.scale_scale, BPair.scale_scale]
    exact BPair.oneValue_refl _
  have s3 : n0.scale (mn * (f * r) * (G * fd))
      ≤ qf.scale (r * md * (G * fd)) + p.scale (f * md * (G * fd)) := by
    have h := ground.leB_scale s2 (G * fd)
    rw [BPair.scale_scale, BPair.scale_add, BPair.scale_scale,
      BPair.scale_scale] at h
    exact h
  have s4 : p.scale (f * md * (G * fd))
      ≤ n0.scale (b1 * (g2 * r) * (f * md * fd)) := by
    have h := ground.leB_scale hT (f * md * fd)
    rw [BPair.scale_scale, BPair.scale_scale,
      ground.mul_left_comm G (f * md) fd] at h
    exact h
  have s5 : n0.scale (mn * (f * r) * (G * fd))
      ≤ qf.scale (r * md * (G * fd))
        + n0.scale (b1 * (g2 * r) * (f * md * fd)) :=
    ground.leB_trans s3 (ground.leB_add (ground.leB_refl _) s4)
  have hC2 : (fn * (md * G) + b1 * (g2 * (md * fd))) * (f * r)
      ≤ mn * (fd * G) * (f * r) :=
    ground.mul_le_mul_right (f * r) hC
  have s6 : n0.scale (fn * f * (md * G * r))
        + n0.scale (b1 * (g2 * r) * (f * md * fd))
      ≤ n0.scale (mn * (f * r) * (G * fd)) := by
    have h := ground.leB_scaleMono hn hC2
    rw [ground.right_distrib (fn * (md * G)) (b1 * (g2 * (md * fd)))
        (f * r),
      BPair.scale_addW, ground.mul_mul_mul_comm fn (md * G) f r,
      posE3 b1 g2 md fd f r,
      posE1 mn fd G f r] at h
    exact h
  have s7 : n0.scale (b1 * (g2 * r) * (f * md * fd))
        + n0.scale (fn * f * (md * G * r))
      ≤ n0.scale (b1 * (g2 * r) * (f * md * fd))
        + qf.scale (r * md * (G * fd)) :=
    ground.leB_congr (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (ground.leB_trans s6 s5)
  have s8 : n0.scale (fn * f * (md * G * r))
      ≤ qf.scale (r * md * (G * fd)) := ground.leB_cancelL s7
  have s9 : (n0.scale (fn * f)).scale (md * G * r)
      ≤ (qf.scale fd).scale (md * G * r) := by
    rw [BPair.scale_scale, BPair.scale_scale, ← posE4 r md G fd]
    exact s8
  exact ground.leB_of_scale s9

/-- The dominance walk's per-position read: the pivot's form at or
beyond its floor multiple of the coordinates' fold of squares, at
every default the floor list is blind to. -/
private def domAt (Xs : List MatQ) (ns : List Nat) (Ds : List DomStep)
    (i : Nat) : Prop :=
  ∀ d : DomStep, ∀ u : List BPair,
    u.length = ground.getAt 0 ns i →
      (dotN u u).scale ((ground.getAt d Ds i).fl.1
          * (ground.getAt dM Xs i).2)
        ≤ (quadForm (ground.getAt dM Xs i).1 u).scale
          (ground.getAt d Ds i).fl.2

/-- The dominance tail's floor list pairs one depth per pivot below
the crossing's own. -/
private theorem domLen (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
      domRead spc spT tn td diag off Xs Rs ns Ds Cs →
      Ds.length < Xs.length
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [], _ =>
    Nat.succ_lt_succ (Nat.succ_pos _)
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xt, _ :: Rs, _ :: n' :: nt,
      _ :: D' :: Ds, _ :: Cs, hread =>
    Nat.succ_lt_succ
      (domLen spc spT tn td (A' :: As) Bs (X' :: Xt) Rs (n' :: nt)
        (D' :: Ds) Cs hread.2)
  | [], _, _, _, _, _, _, hread => hread.elim
  | [_], _, _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, [], _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [_], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [], _,
      hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [], hread => hread.elim

/-- The seed arm's crossing split sits at the floor list's own
position, the walk shifting one pivot per depth. -/
theorem domTail_cross (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
      domRead spc spT tn td diag off Xs Rs ns Ds Cs →
      splitRead (ground.getAt dM Xs Ds.length).1 spc.2
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [],
      hread => hread.2.2.2.1
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xt, _ :: Rs, _ :: n' :: nt,
      _ :: D' :: Ds, _ :: Cs, hread =>
    domTail_cross spc spT tn td (A' :: As) Bs (X' :: Xt) Rs (n' :: nt)
      (D' :: Ds) Cs hread.2
  | [], _, _, _, _, _, _, hread => hread.elim
  | [_], _, _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, [], _, _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, [_], _, _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _, hread =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [], _,
      hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _, hread => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [], hread => hread.elim

/-- `lem:cornerblock`'s dominance walk at the read's own arm
enumeration: the seed arm reads the rebound's floor at the
crossing's following depth and the step arm carries the deeper
floor up through the join, the bond's sandwich pricing the
withdrawn term. -/
private theorem domGo (spc spT : (k : Nat) × Split k) (tn td : Pos) :
    ∀ (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
      (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
      domRead spc spT tn td diag off Xs Rs ns Ds Cs →
      tailRead diag off Xs Rs ns →
      ∀ i, i < Ds.length → domAt Xs ns Ds i
  | A :: A2 :: As, B :: Bs, X :: X' :: Xt, R :: Rs, n :: n' :: nt,
      [D], [], hread, ht, 0, _ => by
    obtain ⟨hDord, hspc, hspT, hsplit, hdg, htr, hcmp⟩ := hread
    intro _ u hu
    have hn : 0 < n := ht.1.1
    have hn' : 0 < n' :=
      greenprod.slab_pos ht.1.2.2.2 0 (Nat.succ_pos _)
    have hRl : R.1.length = n' := rectAt_len ht.2.2.1.1
    refine rebound_floor (o := n) (o' := spc.1) X X' R A B spc.2
      D.dg.1 D.dg.2 tn td D.fl.1 D.fl.2 hn (by rw [hspc]; exact hn')
      ht.2.1.1 (by rw [hspc]; exact ht.1.2.2.1)
      (by rw [hspc]; exact ht.2.2.1.1)
      ht.2.2.2.1.2.1 ht.2.2.2.1.2.2 hsplit
      (diagFloor A D.dg.1 D.dg.2 D.spM hDord ht.1.2.1 hdg)
      (transferCap spc.2 (matMul spc.2.Tw.val R.1)
        (tn * (X'.2 * (R.2 * R.2))) td spT.2 hspT
        (by rw [hspc]; exact hn')
        ((length_matMul _ R.1).trans spc.2.Tw.rows)
        (rowsLen_matMul_of _ R.1
          (fun _ => by rw [hRl]; exact hn') (rectAt_rows ht.2.2.1.1))
        htr)
      hcmp u hu
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_], [],
      _, _, _ + 1, hi =>
    absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero _)
  | A :: A' :: As, B :: Bs, X :: X' :: Xt, R :: Rs, n :: n' :: nt,
      D :: D' :: Ds, C :: Cs, hread, ht, 0, _ => by
    obtain ⟨⟨hDord, hCord, hdg, hbd, hcmp⟩, hrest⟩ := hread
    intro d u hu
    have hn : 0 < n := ht.1.1
    have hn' : 0 < n' :=
      greenprod.slab_pos ht.1.2.2.2 0 (Nat.succ_pos _)
    have hrec := domGo spc spT tn td (A' :: As) Bs (X' :: Xt) Rs
      (n' :: nt) (D' :: Ds) Cs hrest (tailTail ht) 0
      (Nat.succ_pos _) d
    have h2 := greenprod.sandwich_cap X' R B D'.fl.1 D'.fl.2
      C.2.1.1 C.2.1.2 hn ht.1.2.2.1 ht.2.2.1.1 ht.2.2.2.1.2.1 hrec
      (bondCap (n' := n') B C.2.1.1 C.2.1.2 C.2.2 hCord hn hn'
        ht.1.2.2.1 hbd)
      u hu
    rw [ground.mul_comm D'.fl.1 C.2.1.2] at h2
    exact domStepClose X.2 R.2 D.dg.1 D.dg.2 D.fl.1 D.fl.2 D'.fl.2
      C.2.1.1 (C.2.1.2 * D'.fl.1)
      (ground.leB_of_not_lt (elim.dotN_self_side u))
      (diagFloor A D.dg.1 D.dg.2 D.spM hDord ht.1.2.1 hdg u hu)
      (greenprod.join_quadSplit X R A B hn' ht.2.1.1 ht.1.2.2.1
        ht.2.2.1.1 ht.2.2.2.1.2.2 u hu)
      h2 hcmp
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xt, _ :: Rs, _ :: n' :: nt,
      _ :: D' :: Ds, _ :: Cs, hread, ht, i + 1, hi =>
    domGo spc spT tn td (A' :: As) Bs (X' :: Xt) Rs (n' :: nt)
      (D' :: Ds) Cs hread.2 (tailTail ht) i
      (Nat.lt_of_succ_lt_succ hi)
  | [], _, _, _, _, _, _, hread, _, _, _ => hread.elim
  | [_], _, _, _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, [], _, _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, [], _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, [_], _, _, _, _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, _, hread, _, _, _ =>
    hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [], _, _, hread, _, _,
      _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, [_], _, _, hread, _, _,
      _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [], _,
      hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _, [_],
      _ :: _, hread, _, _, _ => hread.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, _ :: _ :: _,
      _ :: _ :: _, [], hread, _, _, _ => hread.elim

/-- The floor list's blind default. -/
private def dDom : DomStep :=
  ⟨0, (Pos.one, Pos.one), (Pos.one, Pos.one),
    ⟨⟨idMat 0, rfl⟩, ⟨idMat 0, rfl⟩, [], 0, rfl⟩⟩

/-- Past the crossing every deep pivot's stated split reads the
upper side throughout, the floor list's read. -/
theorem domTail_psd : ∀ (spc spT : (k : Nat) × Split k) (tn td : Pos)
    (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat)
    (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k)),
    domRead spc spT tn td diag off Xs Rs ns Ds Cs →
    tailRead diag off Xs Rs ns →
    ∀ i, i < Ds.length →
      ∀ s : (k : Nat) × Split k,
        splitRead (ground.getAt dM Xs i).1 s.2 → psdAt s.2 := by
  intro spc spT tn td diag off Xs Rs ns Ds Cs hread ht i hi s hs
  have hiX : i < Xs.length :=
    Nat.lt_trans hi (domLen spc spT tn td diag off Xs Rs ns Ds Cs hread)
  have hlen : s.1 = ground.getAt 0 ns i :=
    (sqAt_len hs.1).symm.trans (sqAt_len (qShape_at ht.2.1 i hiX))
  refine inertia.psd_of_all (ground.getAt dM Xs i).1 s.2 hs ?_
  intro u hu
  refine ground.leB_not_lt
    (ground.unitLeOfScale (w := (ground.getAt dDom Ds i).fl.2) ?_)
  exact ground.leB_trans
    (ground.unitLeScale _
      (ground.leB_of_not_lt (elim.dotN_self_side u)))
    (domGo spc spT tn td diag off Xs Rs ns Ds Cs hread ht i hi dDom u
      (hu.trans hlen))

/-! The count's suffix reads: the dropped chain's leading entry
peeled off the trailing segment, the segment's occupancy at the
withdrawn count, and the center family's own nonempty slab
list. -/

/-! `lem:cornerblock`'s walked segment at the family: the stated chain
data read against the family's evaluated reads over a depth range,
the per-depth centers, witnesses and images the family's own
evaluations with their clearings' margins, and the transport run
down the recursion at the pointwise counts. -/

/-- The evaluated center at a depth: the center family's matrix with
its clearing's own margin. -/
def famYc (F : CenterFam) (en ed : Pos) (K d : Nat) : MatQ :=
  (evalPfm F.Cf.1 d en ed K,
   BPair.marginPos (evalProf F.Cf.2 d en ed K))

/-- The evaluated witness at a depth. -/
private def famW (F : CenterFam) (en ed : Pos) (K d : Nat) : MatQ :=
  (evalPfm F.Wf.1 d en ed K,
   BPair.marginPos (evalProf F.Wf.2 d en ed K))

/-- The evaluated image at a depth. -/
private def famI (F : CenterFam) (en ed : Pos) (K d : Nat) : MatQ :=
  (evalPfm F.If.1 d en ed K,
   BPair.marginPos (evalProf F.If.2 d en ed K))

/-- The chain's stated data read at the family over the segment's
depth range, deep-first: position `p` sits at depth
`m0 + (diag.length - 1 - p)`, the boundary seed at depth `m0` the
last position and the deep end the first; the order list constant at
the family's order; each stated diagonal, scaled by the clearing's
stated power, the family's evaluated diagonal at its position's own
depth; each bond the stated bond; the four walks' boxes holding
every segment depth's scale point at clearing powers inside the
counts' own, and the three clearing certificates' boxes holding them
at powers inside the stated one. -/
def famChainRead (F : CenterFam) (B : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (ns : List Nat) : Prop :=
  ns = List.replicate diag.length F.o
  ∧ ((List.range diag.length).all (fun p =>
      decide (elim.matOneValue
        (inertia.matScale (Pos.powC ed K) (ground.getAt [] diag p))
        (evalPfm F.Af (m0 + (diag.length - 1 - p)) en ed K)))) = true
  ∧ ((List.range off.length).all (fun p =>
      decide (elim.matOneValue (ground.getAt [] off p) B))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxC.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxF.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxU.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p => F.bxL.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1)))) = true
  ∧ ((List.range diag.length).all (fun p =>
      decide (F.bxClC.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClC.hi)
      && Nat.ble (F.bxClC.K + 1) (K + 1))) = true
  ∧ ((List.range diag.length).all (fun p =>
      decide (F.bxClW.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClW.hi)
      && Nat.ble (F.bxClW.K + 1) (K + 1))) = true
  ∧ ((List.range diag.length).all (fun p =>
      decide (F.bxClI.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClI.hi)
      && Nat.ble (F.bxClI.K + 1) (K + 1))) = true

instance instCornerblock3 (F : CenterFam) (B : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (ns : List Nat) :
    Decidable (famChainRead F B en ed K m0 diag off ns) :=
  inferInstanceAs
    (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The clearing's margin reads its family's evaluated clearing back
at a depth the certificate's box holds. -/
private theorem clTie (V : poly.PPoly × poly.PPoly) (e0n : BPair)
    (e0d : Pos) (C : BoxCert) (m K : Nat) (en ed : Pos)
    (hr : boxRead V e0n e0d C)
    (he : BPair.ofPos en * BPair.ofPos e0d ≤ e0n * BPair.ofPos ed)
    (hb : (decide (C.lo ≤ (⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair))
        && decide ((⟨BPair.ofNat (m * m) * BPair.ofPos en, ed⟩
          : CPair) ≤ C.hi)
        && Nat.ble (C.K + 1) (K + 1)) = true) :
    (BPair.ofPos (BPair.marginPos (evalProf V m en ed K))).oneValue
      (evalProf V m en ed K) := by
  have h2 := ground.andSplitB hb
  have h3 := ground.andSplitB h2.1
  exact BPair.marginPos_read (clearPos V e0n e0d C m K en ed hr he
    (of_decide_eq_true h3.1) (of_decide_eq_true h3.2)
    (ground.bleLe h2.2))

/-- The chain's stated data read position by position: the orders,
the diagonal and bond ties, and the seven certificate boxes at each
segment position's own depth. -/
private def famChainPt (F : CenterFam) (B : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (ns : List Nat) : Prop :=
  (∀ i, i < ns.length → ground.getAt 0 ns i = F.o)
  ∧ (∀ p, p < diag.length → elim.matOneValue
      (inertia.matScale (Pos.powC ed K) (ground.getAt [] diag p))
      (evalPfm F.Af (m0 + (diag.length - 1 - p)) en ed K))
  ∧ (∀ p, p < off.length →
      elim.matOneValue (ground.getAt [] off p) B)
  ∧ (∀ p, p < diag.length → (F.bxC.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length → (F.bxF.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length → (F.bxU.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length → (F.bxL.all (fun g =>
      decide (g.lo ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ g.hi)
      && Nat.ble (g.K + 1) (K + K + 1))) = true)
  ∧ (∀ p, p < diag.length →
      (decide (F.bxClC.lo
        ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
          * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩
            : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClC.hi)
      && Nat.ble (F.bxClC.K + 1) (K + 1)) = true)
  ∧ (∀ p, p < diag.length →
      (decide (F.bxClW.lo
        ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
          * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩
            : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClW.hi)
      && Nat.ble (F.bxClW.K + 1) (K + 1)) = true)
  ∧ (∀ p, p < diag.length →
      (decide (F.bxClI.lo
        ≤ (⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
          * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩
            : CPair))
      && decide ((⟨BPair.ofNat ((m0 + (diag.length - 1 - p))
        * (m0 + (diag.length - 1 - p))) * BPair.ofPos en, ed⟩ : CPair)
          ≤ F.bxClI.hi)
      && Nat.ble (F.bxClI.K + 1) (K + 1)) = true)

/-- The stated read's pointwise reads, the range folds walked. -/
private theorem famChainRead_pt (F : CenterFam) (B : elim.Mat)
    (en ed : Pos) (K m0 : Nat) (diag off : List elim.Mat)
    (ns : List Nat) (h : famChainRead F B en ed K m0 diag off ns) :
    famChainPt F B en ed K m0 diag off ns := by
  obtain ⟨hns, hdg, hof, hbC, hbF, hbU, hbL, hcC, hcW, hcI⟩ := h
  refine ⟨fun i hi => ?_,
    fun p hp => of_decide_eq_true
      (ground.all_range_read diag.length hdg p hp),
    fun p hp => of_decide_eq_true
      (ground.all_range_read off.length hof p hp),
    fun p hp => ground.all_range_read diag.length hbC p hp,
    fun p hp => ground.all_range_read diag.length hbF p hp,
    fun p hp => ground.all_range_read diag.length hbU p hp,
    fun p hp => ground.all_range_read diag.length hbL p hp,
    fun p hp => ground.all_range_read diag.length hcC p hp,
    fun p hp => ground.all_range_read diag.length hcW p hp,
    fun p hp => ground.all_range_read diag.length hcI p hp⟩
  rw [hns] at hi ⊢
  rw [ground.length_replicate] at hi
  exact ground.getAt_replicate 0 F.o diag.length i hi

/-- The pointwise read at the deeper segment, the depth formula
stable under the peel: the boundary depth `m0` is the tail's own. -/
private theorem famChainPt_tail (F : CenterFam) (B : elim.Mat)
    (en ed : Pos) (K m0 : Nat) (A B0 : elim.Mat)
    (diag' off' : List elim.Mat) (n : Nat) (ns' : List Nat)
    (h : famChainPt F B en ed K m0 (A :: diag') (B0 :: off')
      (n :: ns')) :
    famChainPt F B en ed K m0 diag' off' ns' := by
  obtain ⟨hno, hdg, hof, hbC, hbF, hbU, hbL, hcC, hcW, hcI⟩ := h
  refine ⟨fun i hi => hno (i + 1) (Nat.succ_lt_succ hi),
    fun p hp => ?_, fun p hp => hof (p + 1) (Nat.succ_lt_succ hp),
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hdg (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbC (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbF (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbU (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hbL (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hcC (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hcW (p + 1) (Nat.succ_lt_succ hp)
  · rw [ground.subSub diag'.length 1 p, Nat.add_comm 1 p]
    exact hcI (p + 1) (Nat.succ_lt_succ hp)

/-- The walk's per-position ball: the pivot in its depth's evaluated
center's ball at the family's radius pair. -/
private def famBallAt (F : CenterFam) (G : elim.Mat) (en ed : Pos)
    (K : Nat) (X : MatQ) (d : Nat) : Prop :=
  (∀ u : List BPair, u.length = F.o →
      (quadForm (devQ X (famYc F en ed K d)).1 u).scale F.rho.2
        ≤ (quadForm G u).scale
            (F.rho.1 * (devQ X (famYc F en ed K d)).2))
  ∧ (∀ u : List BPair, u.length = F.o →
      ((quadForm G u).scale
          (F.rho.1 * (devQ X (famYc F en ed K d)).2)).swap
        ≤ (quadForm (devQ X (famYc F en ed K d)).1 u).scale F.rho.2)

/-- `lem:cornerblock`'s segment walk at the family, deep-first: the seed
arm converts the boundary seed's cap onto the seed pivot at the
boundary depth `m0`, and the step arm hands the ball from the
shallower position's center to the deeper outright, every read the
family's own evaluation at the position's own depth. -/
private theorem famChainGo (F : CenterFam) (B G : elim.Mat)
    (en ed : Pos) (K : Nat)
    (hfam : famRead F B G)
    (he : BPair.ofPos en * BPair.ofPos F.e0.2
      ≤ F.e0.1 * BPair.ofPos ed)
    (hshA : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Af i) j)
        d)).length ≤ K + 1)
    (hshC : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Cf.1 i) j)
        d)).length ≤ K + 1)
    (hshCl : ∀ d, (poly.vnorm (depthPoly F.Cf.2 d)).length ≤ K + 1)
    (hshW : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Wf.1 i) j)
        d)).length ≤ K + 1)
    (hshWcl : ∀ d, (poly.vnorm (depthPoly F.Wf.2 d)).length ≤ K + 1)
    (hshI : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.If.1 i) j)
        d)).length ≤ K + 1)
    (hshIcl : ∀ d, (poly.vnorm (depthPoly F.If.2 d)).length ≤ K + 1) :
    ∀ (diag : List Mat) (m0 : Nat) (off : List Mat) (ns : List Nat)
      (Xs Rs : List MatQ),
      famChainPt F B en ed K m0 diag off ns →
      tailRead diag off Xs Rs ns →
      (∀ i, i < Xs.length → matOneValue
        (transposeM (ground.getAt dM Xs i).1) (ground.getAt dM Xs i).1) →
      (∀ p, p + 1 = diag.length → ∀ u : List BPair, u.length = F.o →
        (quadForm (devQ (ofM (ground.getAt [] diag p))
            (famYc F en ed K m0)).1 u).scale F.rho.2
          ≤ (quadForm G u).scale (F.rho.1
              * (devQ (ofM (ground.getAt [] diag p))
                  (famYc F en ed K m0)).2)) →
      (∀ p, p + 1 = diag.length → ∀ u : List BPair, u.length = F.o →
        ((quadForm G u).scale (F.rho.1
            * (devQ (ofM (ground.getAt [] diag p))
                (famYc F en ed K m0)).2)).swap
          ≤ (quadForm (devQ (ofM (ground.getAt [] diag p))
              (famYc F en ed K m0)).1 u).scale F.rho.2) →
      ∀ i, i < Xs.length →
        famBallAt F G en ed K (ground.getAt dM Xs i)
          (m0 + (diag.length - 1 - i))
  | [], _, _, _, _, _, _, ht, _, _, _, _, _ => ht.1.elim
  | _ :: _, _, _, [], _, _, _, ht, _, _, _, _, _ => ht.1.elim
  | [_], _, _ :: _, [_], _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | [_], _, _ :: _, _ :: _ :: _, _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | [_], _, [], _ :: _ :: _, _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | _ :: _ :: _, _, [], [_], _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | _ :: _ :: _, _, [], _ :: _ :: _, _, _, _, ht, _, _, _, _, _ =>
    False.elim ht.1
  | _ :: _ :: _, _, _ :: _, [_], _, _, _, ht, _, _, _, _, _ => ht.1.elim
  | [_], _, [], [_], [], _, _, ht, _, _, _, _, _ => ht.2.1.elim
  | [_], _, [], [_], _ :: _ :: _, _, _, ht, _, _, _, _, _ =>
    ht.2.1.2.elim
  | [_], _, [], [_], [_], _ :: _, _, ht, _, _, _, _, _ =>
    ht.2.2.1.elim
  | [_], _, [], [_], [_], [], _, _, _, _, _, _ + 1, hi =>
    absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero _)
  | [A], m0, [], [n], [X], [], hpt, ht, _, hsdHi, hsdLo, 0, _ => by
    have hn : n = F.o := hpt.1 0 (Nat.succ_pos 0)
    have hXsq : sqAt X.1 F.o := by rw [← hn]; exact ht.2.1.1
    have hAsq : sqAt A F.o := by rw [← hn]; exact ht.1.2
    have hYcq : sqAt (famYc F en ed K m0).1 F.o :=
      elim.sqAt_of ((length_evalPfm m0 F.Cf.1 en ed K).trans hfam.2.2.1)
        (rowsLen_evalPfm F.o m0 F.Cf.1 en ed K hfam.2.2.2.1)
    exact seedCap X (famYc F en ed K m0) A G F.rho.1 F.rho.2
      hXsq hYcq hAsq ht.2.2.2 (hsdHi 0 rfl) (hsdLo 0 rfl)
  | _ :: _ :: _, _, _ :: _, _ :: _ :: _, [], _, _, ht, _, _, _, _, _ =>
    ht.2.1.elim
  | _ :: _ :: _, _, _ :: _, _ :: _ :: _, [_], _, _, ht, _, _, _, _, _ =>
    ht.2.1.2.elim
  | _ :: _ :: _, _, _ :: _, _ :: _ :: _, _ :: _ :: _, [], _, ht, _, _,
      _, _, _ => ht.2.2.1.elim
  | A :: A' :: As, m0, B0 :: Bs, n :: n' :: nt, X :: X' :: Xt, R :: Rt,
      hpt, ht, hsx, hsdHi, hsdLo, 0, _ => by
    obtain ⟨hAl, hAr, hCl, hCr, hWl, hWr, hIl, hIr, hBq, hGq, hsymG,
      hsymCf, hsymIf, hwitF, hjoinF, hwC, hwF, hwU, hwL, hbrC, hbrW,
      hbrI, htie, hmod⟩ := id hfam
    have hn : n = F.o := hpt.1 0 (Nat.succ_pos _)
    have hn' : n' = F.o := hpt.1 1 (Nat.succ_lt_succ (Nat.succ_pos _))
    have ho : 0 < F.o := by rw [← hn]; exact ht.1.1
    -- the deeper and shallower pivots and the segment's data
    have hXq : sqAt X.1 F.o := by rw [← hn]; exact ht.2.1.1
    have hX'q : sqAt X'.1 F.o := by rw [← hn']; exact ht.2.1.2.1
    have hApos : sqAt A F.o := by rw [← hn]; exact ht.1.2.1
    have hRq : rectAt R.1 F.o F.o := by
      have h := ht.2.2.1.1
      rw [hn', hn] at h
      exact h
    have hB0q : rectAt B0 F.o F.o := by
      have h := ht.1.2.2.1
      rw [hn, hn'] at h
      exact h
    have hBr : rectAt B F.o F.o :=
      elim.rectAt_of (elim.sqAt_len hBq) (elim.rowsLen_of_sqAt hBq)
    -- the evaluated centers, witness and image at the step's depths
    have hYcSq : sqAt (famYc F en ed K (m0 + As.length)).1 F.o :=
      elim.sqAt_of
        ((length_evalPfm (m0 + As.length) F.Cf.1 en ed K).trans hCl)
        (rowsLen_evalPfm F.o (m0 + As.length) F.Cf.1 en ed K hCr)
    have hYcTq : sqAt (famYc F en ed K (m0 + (As.length + 1))).1 F.o :=
      elim.sqAt_of
        ((length_evalPfm (m0 + (As.length + 1)) F.Cf.1 en ed K).trans
          hCl)
        (rowsLen_evalPfm F.o (m0 + (As.length + 1)) F.Cf.1 en ed K hCr)
    have hIq : sqAt (famI F en ed K (m0 + (As.length + 1))).1 F.o :=
      elim.sqAt_of
        ((length_evalPfm (m0 + (As.length + 1)) F.If.1 en ed K).trans
          hIl)
        (rowsLen_evalPfm F.o (m0 + (As.length + 1)) F.If.1 en ed K hIr)
    have hCcq : rectAt (famW F en ed K (m0 + (As.length + 1))).1
        F.o F.o :=
      elim.rectAt_of
        ((length_evalPfm (m0 + (As.length + 1)) F.Wf.1 en ed K).trans
          hWl)
        (rowsLen_evalPfm F.o (m0 + (As.length + 1)) F.Wf.1 en ed K hWr)
    -- the clearings' margins at their certificates' boxes
    have hcCS := clTie F.Cf.2 F.e0.1 F.e0.2 F.bxClC (m0 + As.length) K
      en ed hbrC he
      (hpt.2.2.2.2.2.2.2.1 1 (Nat.succ_lt_succ (Nat.succ_pos _)))
    have hcCT := clTie F.Cf.2 F.e0.1 F.e0.2 F.bxClC
      (m0 + (As.length + 1)) K en ed hbrC he
      (hpt.2.2.2.2.2.2.2.1 0 (Nat.succ_pos _))
    have hcWT := clTie F.Wf.2 F.e0.1 F.e0.2 F.bxClW
      (m0 + (As.length + 1)) K en ed hbrW he
      (hpt.2.2.2.2.2.2.2.2.1 0 (Nat.succ_pos _))
    have hcIT := clTie F.If.2 F.e0.1 F.e0.2 F.bxClI
      (m0 + (As.length + 1)) K en ed hbrI he
      (hpt.2.2.2.2.2.2.2.2.2 0 (Nat.succ_pos _))
    -- the bond conversion onto the stated bond
    have hoff : matOneValue B0 B := hpt.2.2.1 0 (Nat.succ_pos _)
    have hw : oneValueQ (mulQ X' R) (ofM (transposeM B)) :=
      elim.matOne_trans ht.2.2.2.1.2.1
        (inertia.matScale_matOne (X'.2 * R.2)
          (elim.transposeM_congrM F.o B0 B (rectAt_rows hB0q)
            (elim.rowsLen_of_sqAt hBq)
            ((rectAt_len hB0q).trans (elim.sqAt_len hBq).symm) hoff))
    have hRrow : rowsLen F.o (matMul B0 R.1) :=
      elim.rowsLen_matMul_of B0 R.1
        (fun _ => by rw [rectAt_len hRq]; exact ho) (rectAt_rows hRq)
    have hRrow' : rowsLen F.o (matMul B R.1) :=
      elim.rowsLen_matMul_of B R.1
        (fun _ => by rw [rectAt_len hRq]; exact ho) (rectAt_rows hRq)
    have hj : oneValueQ (addQ X (mulQ (ofM B) R)) (ofM A) :=
      elim.matOne_trans
        (inertia.matScale_matOne Pos.one
          (elim.matAdd_cong2 F.o _ _ _ _
            (elim.rowsLen_mapRows _ X.1 F.o (elim.rowsLen_of_sqAt hXq))
            (elim.rowsLen_mapRows _ _ F.o hRrow')
            (elim.rowsLen_mapRows _ X.1 F.o (elim.rowsLen_of_sqAt hXq))
            (elim.rowsLen_mapRows _ _ F.o hRrow)
            (elim.matOne_refl _)
            (inertia.matScale_matOne X.2
              (elim.matMul_congrL B B0 R.1 (elim.matOne_symm hoff)))))
        ht.2.2.2.1.2.2
    -- the family's own two ties at the step's two depths
    have hwc := witTie_ptw F.Cf F.Wf B F.o (m0 + As.length) K en ed
      (BPair.marginPos (evalProf F.Cf.2 (m0 + As.length) en ed K))
      (BPair.marginPos (evalProf F.Wf.2 (m0 + As.length + 1) en ed K))
      hCr hWl hWr ho (fun i j => hshC (m0 + As.length) i j)
      (hshCl (m0 + As.length))
      (fun i j => hshW (m0 + As.length + 1) i j)
      (hshWcl (m0 + As.length + 1)) hcCS hcWT hwitF
    have hpow : (BPair.ofPos (Pos.powC ed K)).oneValue
        (ground.bpow (BPair.ofPos ed) K) := by
      rw [Pos.powC_eq]
      exact ground.ofPos_pow ed K
    have hjc := joinTie_ptw F.Af F.Wf F.If A B F.o
      (m0 + (As.length + 1)) K en ed (Pos.powC ed K)
      (BPair.marginPos (evalProf F.If.2 (m0 + (As.length + 1)) en ed K))
      (BPair.marginPos (evalProf F.Wf.2 (m0 + (As.length + 1)) en ed K))
      hAl hAr hWl hWr hIl hIr hBq hApos ho
      (fun i j => hshA (m0 + (As.length + 1)) i j)
      (fun i j => hshW (m0 + (As.length + 1)) i j)
      (hshWcl (m0 + (As.length + 1)))
      (fun i j => hshI (m0 + (As.length + 1)) i j)
      (hshIcl (m0 + (As.length + 1))) hcIT hcWT hpow
      (hpt.2.1 0 (Nat.succ_pos _)) hjoinF
    -- the four pointwise counts
    have hFp := floorCount_ptw F.Cf G F.o F.y0.1 F.y0.2 F.rho.1 F.rho.2
      F.e0.1 F.e0.2 F.bxF (m0 + As.length) K en ed
      (BPair.marginPos (evalProf F.Cf.2 (m0 + As.length) en ed K))
      hCl hCr hGq hsymCf hsymG (fun i j => hshC (m0 + As.length) i j)
      (hshCl (m0 + As.length)) hwF he
      (hpt.2.2.2.2.1 1 (Nat.succ_lt_succ (Nat.succ_pos _))) hcCS
    have hconp := contrCount_ptw F.Wf G F.o F.lam.1 F.lam.2
      F.e0.1 F.e0.2 F.bxC (m0 + (As.length + 1)) K en ed
      (BPair.marginPos (evalProf F.Wf.2 (m0 + (As.length + 1)) en ed K))
      hWl hWr hGq hsymG (fun i j => hshW (m0 + (As.length + 1)) i j)
      (hshWcl (m0 + (As.length + 1))) hwC he
      (hpt.2.2.2.1 0 (Nat.succ_pos _)) hcWT
    have hdefHi := dcapCount_hi F.Cf F.If G F.o F.dft.1 F.dft.2
      F.e0.1 F.e0.2 F.bxU (m0 + (As.length + 1)) K en ed
      (BPair.marginPos (evalProf F.If.2 (m0 + (As.length + 1)) en ed K))
      (BPair.marginPos (evalProf F.Cf.2 (m0 + (As.length + 1)) en ed K))
      hIl hIr hCl hCr hGq hsymCf hsymIf hsymG
      (fun i j => hshI (m0 + (As.length + 1)) i j)
      (hshIcl (m0 + (As.length + 1)))
      (fun i j => hshC (m0 + (As.length + 1)) i j)
      (hshCl (m0 + (As.length + 1))) hwU he
      (hpt.2.2.2.2.2.1 0 (Nat.succ_pos _)) hcIT hcCT
    have hdefLo := dcapCount_lo F.Cf F.If G F.o F.dft.1 F.dft.2
      F.e0.1 F.e0.2 F.bxL (m0 + (As.length + 1)) K en ed
      (BPair.marginPos (evalProf F.If.2 (m0 + (As.length + 1)) en ed K))
      (BPair.marginPos (evalProf F.Cf.2 (m0 + (As.length + 1)) en ed K))
      hIl hIr hCl hCr hGq hsymCf hsymIf hsymG
      (fun i j => hshI (m0 + (As.length + 1)) i j)
      (hshIcl (m0 + (As.length + 1)))
      (fun i j => hshC (m0 + (As.length + 1)) i j)
      (hshCl (m0 + (As.length + 1))) hwL he
      (hpt.2.2.2.2.2.2.1 0 (Nat.succ_pos _)) hcIT hcCT
    -- the shallower position's ball
    have hrec := famChainGo F B G en ed K hfam he
      hshA hshC hshCl hshW hshWcl hshI hshIcl
      (A' :: As) m0 Bs (n' :: nt) (X' :: Xt) Rt
      (famChainPt_tail F B en ed K m0 A B0 (A' :: As) Bs n
        (n' :: nt) hpt)
      (tailTail ht) (fun j hj => hsx (j + 1) (Nat.succ_lt_succ hj))
      (fun p hp => hsdHi (p + 1) (congrArg Nat.succ hp))
      (fun p hp => hsdLo (p + 1) (congrArg Nat.succ hp))
      0 (Nat.succ_pos _)
    exact ball_step_of (o := F.o) (o' := F.o)
      X' X (famYc F en ed K (m0 + As.length))
      (famI F en ed K (m0 + (As.length + 1)))
      (famYc F en ed K (m0 + (As.length + 1))) R
      (famW F en ed K (m0 + (As.length + 1))) A B G G
      F.lam.1 F.lam.2 F.y0.1 F.y0.2 F.rho.1 F.rho.2 F.dft.1 F.dft.2
      F.lc.1 F.lc.2 hX'q hXq hYcSq hIq hYcTq hRq hCcq hApos hBr hGq
      (hsx 1 (Nat.succ_lt_succ (Nat.succ_pos _)))
      (evalSymOf F.Cf.1 F.o (m0 + As.length) K en ed hCl hCr hsymCf)
      hw hj hwc hjc hrec.1 hrec.2 hFp hconp hsymG (fun h => h)
      hdefHi hdefLo htie hmod
  | A :: A' :: As, m0, B0 :: Bs, n :: n' :: nt, X :: X' :: Xt, R :: Rt,
      hpt, ht, hsx, hsdHi, hsdLo, i + 1, hi => by
    have h := famChainGo F B G en ed K hfam he hshA hshC hshCl
      hshW hshWcl hshI hshIcl (A' :: As) m0 Bs (n' :: nt)
      (X' :: Xt) Rt
      (famChainPt_tail F B en ed K m0 A B0 (A' :: As) Bs n
        (n' :: nt) hpt)
      (tailTail ht) (fun j hj => hsx (j + 1) (Nat.succ_lt_succ hj))
      (fun p hp => hsdHi (p + 1) (congrArg Nat.succ hp))
      (fun p hp => hsdLo (p + 1) (congrArg Nat.succ hp))
      i (Nat.lt_of_succ_lt_succ hi)
    have hd : (A :: A' :: As).length - 1 - (i + 1) = As.length - i :=
      Nat.succ_sub_succ As.length i
    rw [hd]
    exact h

/-- `lem:cornerblock`'s walked segment at the family: from the boundary
seed's cap at depth `m0`, the last position, the one-depth transport
hands the ball from each position's center to the deeper position's
down the recursion at the family's evaluated reads — every pivot at
its position's own depth in the ball of the family's center there,
the centers' consecutive drift riding the defect — and every pivot's
every stated split reads the upper side throughout, the slab fold at
the count's unit. -/
theorem famChain_psd (F : CenterFam) (B G : elim.Mat) (en ed : Pos)
    (K m0 : Nat) (diag off : List elim.Mat) (Xs Rs : List MatQ)
    (ns : List Nat) (sps : List ((n : Nat) × Split n))
    (spSU spSL : Split F.o)
    (hfam : famRead F B G)
    (he : BPair.ofPos en * BPair.ofPos F.e0.2
      ≤ F.e0.1 * BPair.ofPos ed)
    (hshA : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Af i) j)
        d)).length ≤ K + 1)
    (hshC : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Cf.1 i) j)
        d)).length ≤ K + 1)
    (hshCl : ∀ d, (poly.vnorm (depthPoly F.Cf.2 d)).length ≤ K + 1)
    (hshW : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Wf.1 i) j)
        d)).length ≤ K + 1)
    (hshWcl : ∀ d, (poly.vnorm (depthPoly F.Wf.2 d)).length ≤ K + 1)
    (hshI : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.If.1 i) j)
        d)).length ≤ K + 1)
    (hshIcl : ∀ d, (poly.vnorm (depthPoly F.If.2 d)).length ≤ K + 1)
    (hchain : famChainRead F B en ed K m0 diag off ns)
    (ht : tailRead diag off Xs Rs ns)
    (hsymD : greenprod.symRead diag)
    (hseed : spectator.capQ
      (spectator.devQ
        (greenprod.ofM (ground.getAt [] diag (diag.length - 1)))
        (famYc F en ed K m0)) G F.rho.1 F.rho.2 spSU spSL)
    (hl : revListRead Xs sps) :
    revFold sps = 0 := by
  obtain ⟨hAl, hAr, hCl, hCr, hWl, hWr, hIl, hIr, hBq, hGq, hsymG,
    hsymCf, hsymIf, hwitF, hjoinF, hwC, hwF, hwU, hwL, hbrC, hbrW,
    hbrI, htie, hmod⟩ := id hfam
  have hpt := famChainRead_pt F B en ed K m0 diag off ns hchain
  have hball := famChainGo F B G en ed K hfam he
    hshA hshC hshCl hshW hshWcl hshI hshIcl diag m0 off ns Xs Rs hpt ht
    (greenprod.tailSym diag off Xs Rs ns ht hsymD)
    (fun p hp u hu => by
      have hp' : p = diag.length - 1 := by rw [← hp]; rfl
      subst hp'
      exact spectator.cap_hi _ G F.rho.1 F.rho.2 spSU spSL hseed u hu)
    (fun p hp u hu => by
      have hp' : p = diag.length - 1 := by rw [← hp]; rfl
      subst hp'
      exact spectator.cap_lo _ G F.rho.1 F.rho.2 spSU spSL hseed u hu)
  have hlen : Xs.length = diag.length :=
    (greenprod.qShape_len ht.2.1).trans
      (greenprod.slabShape_len_ns ht.1)
  refine greenprod.revFold_vacant Xs sps 0 hl (fun i hi s hs => ?_)
  have hid : i < diag.length := by rw [← hlen]; exact hi
  have hin : i < ns.length := by
    rw [greenprod.slabShape_len_ns ht.1]; exact hid
  have hXo : sqAt (ground.getAt dM Xs i).1 F.o := by
    have h := greenprod.qShape_at ht.2.1 i hi
    rw [hpt.1 i hin] at h
    exact h
  have hYcq : sqAt (famYc F en ed K (m0 + (diag.length - 1 - i))).1
      F.o :=
    elim.sqAt_of ((length_evalPfm (m0 + (diag.length - 1 - i)) F.Cf.1
        en ed K).trans hCl)
      (rowsLen_evalPfm F.o (m0 + (diag.length - 1 - i)) F.Cf.1
        en ed K hCr)
  have hb := hball i hi
  exact spectator.ball_psd_ptw (ground.getAt dM Xs i)
    (famYc F en ed K (m0 + (diag.length - 1 - i))) G F.y0.1 F.y0.2
    F.rho.1 F.rho.2 s.2 hXo hYcq hGq
    (floorCount_ptw F.Cf G F.o F.y0.1 F.y0.2 F.rho.1 F.rho.2
      F.e0.1 F.e0.2 F.bxF (m0 + (diag.length - 1 - i)) K en ed
      (BPair.marginPos (evalProf F.Cf.2 (m0 + (diag.length - 1 - i))
        en ed K))
      hCl hCr hGq hsymCf hsymG
      (fun a b => hshC (m0 + (diag.length - 1 - i)) a b)
      (hshCl (m0 + (diag.length - 1 - i))) hwF he
      (hpt.2.2.2.2.1 i hid)
      (clTie F.Cf.2 F.e0.1 F.e0.2 F.bxClC (m0 + (diag.length - 1 - i))
        K en ed hbrC he (hpt.2.2.2.2.2.2.2.1 i hid)))
    hb.1 hb.2 hs

/-- The walked segment's boundary key past the withdrawn count: the
trailing segment's last key is the family's own last. -/
private theorem seedIdx : ∀ (L k n : Nat), L + (k + 1) = n →
    k + 1 < n → k + 1 + (L - 1) = n - 1
  | 0, _, _, hL, hlt => by
    rw [← hL, Nat.zero_add] at hlt
    exact absurd hlt (Nat.lt_irrefl _)
  | L' + 1, k, _, hL, _ => by
    rw [← hL]
    show k + 1 + L' = L' + 1 + k
    rw [Nat.add_right_comm k 1 L', Nat.add_right_comm L' 1 k,
      Nat.add_comm k L']

/-- The chain's count closes at the certificate, the center family
its data: the count splits over the depth pivots
(`lem:greenprod`(ii)), the walked segment's stated splits read
vacant at the family's balls from the seed's stated ball at the
boundary block, the crossing's split reads its one lower unit, the
dominance tail's floors read every deeper split vacant, and every
split of the assembled datum reads the count at one. -/
theorem famChainCount {n : Nat} (F : CenterFam) (B G : elim.Mat)
    (en ed : Pos) (K m0 : Nat)
    (spc spT : (k : Nat) × Split k) (tn td : Pos)
    (diag off : List elim.Mat) (ns : List Nat) (Xs Rs : List MatQ)
    (Ds : List DomStep) (Cs : List ((k : Nat) × (Pos × Pos) × Split k))
    (sps : List ((k : Nat) × Split k)) (SP : Split n)
    (spSU spSL : Split F.o)
    (hfam : famRead F B G)
    (he : BPair.ofPos en * BPair.ofPos F.e0.2
      ≤ F.e0.1 * BPair.ofPos ed)
    (hshA : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Af i) j)
        d)).length ≤ K + 1)
    (hshC : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Cf.1 i) j)
        d)).length ≤ K + 1)
    (hshCl : ∀ d, (poly.vnorm (depthPoly F.Cf.2 d)).length ≤ K + 1)
    (hshW : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.Wf.1 i) j)
        d)).length ≤ K + 1)
    (hshWcl : ∀ d, (poly.vnorm (depthPoly F.Wf.2 d)).length ≤ K + 1)
    (hshI : ∀ d i j, (poly.vnorm (depthPoly (ground.getAt vacProf
      (ground.getAt ([] : List (poly.PPoly × poly.PPoly)) F.If.1 i) j)
        d)).length ≤ K + 1)
    (hshIcl : ∀ d, (poly.vnorm (depthPoly F.If.2 d)).length ≤ K + 1)
    (hchain : famChainRead F B en ed K m0 (diag.drop (Ds.length + 1))
      (off.drop (Ds.length + 1)) (ns.drop (Ds.length + 1)))
    (ht : tailRead diag off Xs Rs ns)
    (hl : revListRead Xs sps)
    (hS : splitRead (assemble diag off) SP)
    (hdom : domRead spc spT tn td diag off Xs Rs ns Ds Cs)
    (hone : ∀ d : (k : Nat) × Split k,
      revAt (ground.getAt d sps Ds.length).2 = 1)
    (hsymD : greenprod.symRead (diag.drop (Ds.length + 1)))
    (hseed : spectator.capQ
      (spectator.devQ
        (greenprod.ofM (ground.getAt [] diag (diag.length - 1)))
        (famYc F en ed K m0)) G F.rho.1 F.rho.2 spSU spSL) :
    revAt SP = 1 := by
  have hlen : Ds.length < Xs.length :=
    domLen spc spT tn td diag off Xs Rs ns Ds Cs hdom
  have hc : Ds.length < sps.length := by
    rw [← greenprod.revListRead_length Xs sps hl]
    exact hlen
  have hpsd : ∀ i, i < (Xs.take Ds.length).length →
      ∀ s : (k : Nat) × Split k,
        splitRead (ground.getAt dM (Xs.take Ds.length) i).1 s.2 →
        psdAt s.2 := by
    intro i hi s hs
    rw [ground.length_take Ds.length Xs (Nat.le_of_lt hlen)] at hi
    rw [ground.getAt_take dM Ds.length Xs i hi] at hs
    exact domTail_psd spc spT tn td diag off Xs Rs ns Ds Cs hdom ht i hi
      s hs
  have htake : revFold (sps.take Ds.length) = 0 :=
    greenprod.revFold_vacant (Xs.take Ds.length) (sps.take Ds.length) 0
      (greenprod.revListRead_take Xs sps Ds.length hl) hpsd
  have hXd : Xs.length = diag.length :=
    (greenprod.qShape_len ht.2.1).trans
      (greenprod.slabShape_len_ns ht.1)
  have hdrop : revFold (sps.drop (Ds.length + 1)) = 0 := by
    match Nat.lt_or_ge (Ds.length + 1) diag.length with
    | Or.inl hlt =>
      have hent : ground.getAt ([] : elim.Mat)
          (diag.drop (Ds.length + 1))
          ((diag.drop (Ds.length + 1)).length - 1)
          = ground.getAt [] diag (diag.length - 1) := by
        rw [ground.getAt_drop, seedIdx
          (diag.drop (Ds.length + 1)).length Ds.length diag.length
          (ground.length_drop (Ds.length + 1) diag (Nat.le_of_lt hlt))
          hlt]
      exact famChain_psd F B G en ed K m0 (diag.drop (Ds.length + 1))
        (off.drop (Ds.length + 1)) (Xs.drop (Ds.length + 1))
        (Rs.drop (Ds.length + 1)) (ns.drop (Ds.length + 1))
        (sps.drop (Ds.length + 1)) spSU spSL hfam he
        hshA hshC hshCl hshW hshWcl hshI hshIcl hchain
        (greenprod.tailRead_drop diag off Xs Rs ns (Ds.length + 1)
          hlt ht)
        hsymD (by rw [hent]; exact hseed)
        (greenprod.revListRead_drop Xs sps (Ds.length + 1) hl)
    | Or.inr hge =>
      have hsl : sps.length = diag.length :=
        (greenprod.revListRead_length Xs sps hl).symm.trans hXd
      have heq : sps.length = Ds.length + 1 :=
        Nat.le_antisymm (by rw [hsl]; exact hge) hc
      rw [← heq, ground.dropLength sps]
      rfl
  rw [greenprod.countSplit diag off Xs Rs ns sps SP ht hl hS,
    greenprod.revFold_split sps Ds.length, htake,
    ground.drop_getAt_cons (⟨n, SP⟩ : (k : Nat) × Split k)
      Ds.length sps hc,
    greenprod.revFold_cons, hone ⟨n, SP⟩, hdrop]

/-! The compression lifts: a family read at the compressed datum is
the count's own witness at the full datum, the congruence
transporting every form.  The compression's shape binders (`hPl`,
`hPr`) are the certificate-shape frame at the truncating folds. -/

/-- The compressed cross pairing reads the datum's own at the two
carried vectors, the congruence transporting the pairing. -/
private theorem tiePair {n m : Nat} (S P W : Mat)
    (hS : sqAt S n) (hPl : P.length = n) (hPr : rowsLen m P)
    (htie : matOneValue (matMul (transposeM P) (matMul S P)) W)
    (x y : List BPair) (hx : x.length = m) (hy : y.length = m) :
    (dotN (matVec P x) (matVec S (matVec P y))).oneValue
      (dotN x (matVec W y)) :=
  BPair.oneValue_trans (dotN_read _ _)
    (BPair.oneValue_trans
      (congrPair S P n m (sqAt_len hS) (rowsLen_of_sqAt hS) hPl hPr
        x y hx hy)
      (BPair.oneValue_trans
        (dotP_oneValue_right x _ _ (matVec_matOne _ _ y htie))
        (BPair.oneValue_symm (dotN_read x (matVec W y)))))

/-- The compressed strict vector occupies the count: a vector whose
form at the compression reads below the sum's unit forces the
reversal count of every split of the datum, the congruence
transporting the form and the forcing clause reading the family. -/
theorem strict_lift {n m : Nat} (S P W : Mat) (sp : Split n)
    (x : List BPair)
    (hsp : splitRead S sp)
    (hPl : P.length = n) (hPr : rowsLen m P)
    (htie : matOneValue (matMul (transposeM P) (matMul S P)) W)
    (hx : x.length = m)
    (hq : quadForm W x < BPair.unit) :
    1 ≤ revAt sp := by
  refine inertia.strictForcing S (matVec P x)
    ((matVec_length P x).trans hPl) ?_ sp hsp
  exact BPair.lt_congr
    (BPair.oneValue_symm (tieQuad S P W hsp.1 hPl hPr htie x hx))
    (BPair.oneValue_refl BPair.unit) hq

/-- The compressed cap pair occupies the count at two: the two
members' reads at the compression — the leading form below the
sum's unit and the doubled cross read below the diagonal product's
quadruple — force the reversal count at two or beyond at every
split of the datum, the congruence transporting the three reads. -/
theorem cap_lift {n m : Nat} (S P W : Mat) (sp : Split n)
    (x x' : List BPair)
    (hsp : splitRead S sp)
    (hPl : P.length = n) (hPr : rowsLen m P)
    (htie : matOneValue (matMul (transposeM P) (matMul S P)) W)
    (hx : x.length = m) (hx' : x'.length = m)
    (hq : quadForm W x < BPair.unit)
    (hd : (dotN x (matVec W x') + dotN x' (matVec W x))
        * (dotN x (matVec W x') + dotN x' (matVec W x))
      < BPair.ofNat 4 * (quadForm W x * quadForm W x')) :
    2 ≤ revAt sp := by
  have hqx := tieQuad S P W hsp.1 hPl hPr htie x hx
  have hqx' := tieQuad S P W hsp.1 hPl hPr htie x' hx'
  have hc1 := tiePair S P W hsp.1 hPl hPr htie x x' hx hx'
  have hc2 := tiePair S P W hsp.1 hPl hPr htie x' x hx' hx
  refine inertia.capForcing S (matVec P x) (matVec P x')
    ((matVec_length P x).trans hPl) ((matVec_length P x').trans hPl)
    (BPair.lt_congr (BPair.oneValue_symm hqx)
      (BPair.oneValue_refl BPair.unit) hq) ?_ sp hsp
  refine BPair.lt_congr
    (BPair.mul_congr
      (BPair.add_congr (BPair.oneValue_symm hc1)
        (BPair.oneValue_symm hc2))
      (BPair.add_congr (BPair.oneValue_symm hc1)
        (BPair.oneValue_symm hc2)))
    (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 4))
      (BPair.mul_congr (BPair.oneValue_symm hqx)
        (BPair.oneValue_symm hqx')))
    hd

end cornerblock
