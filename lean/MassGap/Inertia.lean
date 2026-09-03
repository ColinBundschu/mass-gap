import MassGap.Elim
/-!
`lem:inertia` — the reversal count of a form pair, read off a pivot
split of the pair's elimination datum `S` at `A = B + S`
(`siteDatum`).  A split's certificate data are a congruence `T` with
its invertibility witness — the determinant off equal members, the
adjugate against it the stage's solved inverse — the nonsingular
blocks of orders one and two in their order, and the trailing kernel
block (`Split`; the tex's stage entries clear to the integer carrier
by the homogeneity principle, a positive rescaling fixing every
count, so the congruence enters cleared with the block diagonal
absorbing the clearing).  The split read (`splitRead`) is the
congruence identity `Tᵀ S T = D` at the assembled block diagonal
(`blockMat`) with the witness's two products `T Tw = det · I` and
`Tw T = det · I` and each block's determinant off equal members; the
reversal count is the blocks' lower-side unit fold (`SBlock.rev`,
`revAt`) — an order-1 block its entry's side, a 2×2 block one unit
per side at the determinant's lower side (the mixed block) and the
diagonal's shared side at the upper, the identity
`S₁₁S₂₂ = det + S₁₂²` its warrant — and the positive-semidefinite
and positive-definite reads are the upper side throughout
(`psdAt`, `pdAt`); the two-sided cap at `C` is the two splits' read
(`capAt`, the decimation and the spectator tier its consumers).  Jacobi's
rule is the fast route (`jacobiRev` at `minorsUnequal`): at leading
principal minors of unequal members the count is the minor
sequence's own orientation-reversal count along `1, m₁, …, m_N`,
the coherence with the split reads the check module's pins — each
leading minor its own first-row fold, the Gauss descent's shared
route (`elim.sdescend`'s Sylvester cofactors) the recorded headroom
at orders beyond the batteries'.  Inertia's addition at a
nonsingular principal pivot lands here (`rev_add` at the assembled
datum `blockJoin` and the cleared deflation `deflMat`, the solve
witness `P C ~ (det P) B` the clause's own datum) with the
determinant's split beside it (`minor_deflMat`: the pivot's
determinant against the cleared deflation's reads the pivot's
determinant at twice the deflation's order against the assembled
datum's, the slab reduction `elim.detL_slabReduce` and the
block-triangular read `elim.detL_blockTri` its two steps), and its
instance at a block diagonal beside it (`rev_join`, the join's
off-block reading equal members throughout, the lift a padding
`padR` and the pricing without the solve).  The existence clause
lands at this owner (`mkSplit` with its read `mkSplit_read`,
`thm:certconstruct`'s emission clause): every symmetric square
datum carries a split, closed by the leftmost admissible pivot's
descent in at most `N` steps — one pivot block of order at most two
per step with the deflation beneath it, the datum's vacant
remainder the kernel block.  The certificate is carried by the
congruence's column list, whose pairing table against the block
diagonal is the split read outright and whose determinant is read
at every step: an adjacent exchange moves a pivot's places to the
front and swaps the determinant's members
(`elim.detL_swapAdj`), and the cleared clearing at the pivot is
block triangular, its determinant the diagonal blocks' product
against the scale's power (`elim.detL_blockTri` over
`elim.detL_slabReduce`); the stored witness is the adjugate at its
two identity reads
(`elim.adjM_row_diag`, `elim.adjM_col_diag` with their off-diagonal
twins), which is also the solve witness of the clearing.  The
general-theorem tier's engine
sits here: a split's two lists (`lowerList` at the reversal
count, one vector per lower-side unit, and `complList` at the rest
of the order with the kernel block's columns), the congruence's
images of raw vectors supported at the blocks' own places, with the
lower list pricing every off-unit combination strictly below the
sum's unit (`lowerList_strict`), the complement list pricing every
combination at or above it (`complList_side`) and reading the unit
tail only at unit coefficients (`complList_indep`) — and on it the
forcing clause (`forcing`, a family pricing every off-unit
combination strictly below the unit counting at or below the
reversal count, the joined complement list's independence its
whole content) with the three general reads it carries: the
two-splits-one-count exchange (`rev_exchange`), the monotonicity
`S ⪯ S'` at `rev(S) ≥ rev(S')` (`rev_mono`, the site datum's form
decomposition the joint), and the compression comparison
(`rev_compress`, the quadratic form's transport at a rectangular
congruence).  The tier closes at two further members: the dual
forcing clause (`forcing_upper`, an independent family pricing every
combination at or above the sum's unit joined to the split's own
lower list, `L.length + rev(S) ≤ n` the width bound's read) and the
positive rescaling's transport (`scaleSplit` at a pair strictly
above the sum's unit, with its read `scaleSplit_read` and its count
identity `scaleSplit_rev`, the consumable corollary `rev_scale`).
The scalar certificate stands beside it (`scalarSplit` at a stated
order and a positive scalar): the identity congruence with one
positive block per key, the upper side throughout
(`scalarSplit_psd`), and every datum reading the unit gram's scalar copy
splitting at it (`scalarSplit_read`) — `lem:corner`'s join read
consumes it at the two levels' difference site.  The diagonal
certificate at a stated entry list is the block-diagonal addition's
instance at order-one blocks (`oneSplit`, one block per entry with
the kernel vacant, the table's order-one row reading each block's
side): a datum reading the list's block diagonal splits at it
(`oneSplit_read`) and its count is the list's own side fold
(`revAt_oneSplit`), `rev_one` the instance at one entry.
The tier closes at the transports and the joined form reads: a
split moves across the one-value read at a square datum
(`splitRead_congr`), a congruence at a two-sided witness
`T W ~ c I ~ W T` reads the datum's own count (`rev_congr`, the
compression each way at the witness round trip), and a split's
datum reads its own symmetry (`splitRead_symm`, the block
diagonal's pairing carried back through the certificate's witness
with the determinant's square clearing); the join's pairing splits
into the four block reads at stated row counts (`quadJoin` — the
width frames alone admit the truncating folds, the committed
refusal's read), and the two scale spellings meet entrywise
(`matScale_scaleB`).
The count engine's shared kit is public at this owner
(`matVec_blockJoin`, `quadJoin`, `quadAdd`, `quad_congr`,
`quadNull`, `vecAdd_app`, the unit-tail sum reads, `ltUnitAddLe`,
`leAddLtUnit`, `adjB`, `padR` with its reads), the slab tier's consumption beside the addition's own.
The addition consumes both directions at one pair of families: the
two splits' lower lists carried through the padding and the
deflation's lift force the count from below at `forcing`, and their
complement counterparts force it from above at `forcing_upper`, the
lift's solve read (`pivotSolve`) and the coupling's transpose
adjoint (`adjB`) killing every cross pairing (`quadSplit`).
The monotonicity's form decomposition stands here at its own
carrier: the quadratic form's fold (`quadForm`) with its additivity
over the entrywise row sum (`quadForm_add`), its walk of the
memberwise swap (`quadForm_swap`), its positive rescaling
(`quadForm_scale`) and the site datum's own split
(`quadForm_site`), the two order corollaries (`site_gap`,
`site_side`) and their cleared spellings (`scaledSite_gap`,
`scaledSite_side`) — the tier `certconstruct`'s counts and
`thm:certconstruct`'s witness read their requirement through, the
matrix-level plumbing beneath it `elim`'s (`matAdd_dotPmap`,
`dotP_swapMap`, `rowsLen_mapRows`, with the skipping
fold's twins `matVec_add`, `dotN_addRow`, `matVec_swapM` and
`dotN_matVec_swapMap` beside them).  The rescaling tier's own
carriers likewise stand at their owners: the entrywise rescaling
itself is `poly.scaleP`, `matScaleB` its row map with the scalar
kit (`matScaleB_congr`, `matScaleB_add`, `matScaleB_one`) reading
the `poly` kit rowwise, the weighted matrix's action
(`matVec_scaleB`) and the weighted identity's (`scaleId_act`) here
at `matScaleB`'s own module, the one-value matrix kit and the
scaled row's pairing at `elim`.
The carriers decline the generated
injectivity lemmas (`genInjectivity false` on `SBlock` with the
structures), the guard's completion across the tree: every
structure and inductive of the development carries it, the
declarations at the empty axiom set with the auto-generated tier
included.
-/

namespace inertia
open ground elim

/-- The form pair's elimination datum `S` at `A = B + S`, the
entrywise site structure. -/
def siteDatum (A B : Mat) : Mat := matAdd A (matSwap B)

/-- The positive rescaling entrywise, the clearing's read. -/
def matScale (w : Pos) (m : Mat) : Mat :=
  m.map (fun r => r.map (fun x => x.scale w))

/-- The rescaling keeps the row count. -/
theorem length_matScale (w : Pos) (M : Mat) :
    (matScale w M).length = M.length := ground.length_map _ M

/-- The balance-pair weighting entrywise, a level's member entering
at either side: the polynomial rescaling `poly.scaleP` read row by
row. -/
def matScaleB (w : BPair) (m : Mat) : Mat :=
  m.map (poly.scaleP w)

/-- The weighting's congruence in its weight: two weights of one
value scale a matrix to one value, entry by entry. -/
theorem matScaleB_congr {a b : BPair} (h : a.oneValue b) :
    ∀ M : Mat, matOneValue (matScaleB a M) (matScaleB b M)
  | [] => trivial
  | r :: t => ⟨poly.scaleP_congr h r, matScaleB_congr h t⟩

/-- The balance weighting distributes over the entrywise vector
sum. -/
private theorem vecScaleB_sum (w : BPair) : ∀ p q : List BPair,
    poly.oneValue (poly.scaleP w (vecAdd p q))
      (vecAdd (poly.scaleP w p) (poly.scaleP w q))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | a :: p, b :: q =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.left_distrib w a b))
        (BPair.add_congr (BPair.oneValue_symm (BPair.norm_oneValue _))
          (BPair.oneValue_symm (BPair.norm_oneValue _)))),
     vecScaleB_sum w p q⟩

/-- The balance weighting distributes over the entrywise matrix
sum. -/
theorem matScaleB_sum (w : BPair) : ∀ P Q : Mat,
    matOneValue (matScaleB w (matAdd P Q))
      (matAdd (matScaleB w P) (matScaleB w Q))
  | [], _ => trivial
  | _ :: _, [] => trivial
  | r :: P, s :: Q => ⟨vecScaleB_sum w r s, matScaleB_sum w P Q⟩

/-- The balance weighting passes the memberwise swap, entry by
entry. -/
private theorem vecScaleB_neg (w : BPair) : ∀ p : List BPair,
    poly.oneValue (poly.scaleP w (p.map BPair.swap))
      ((poly.scaleP w p).map BPair.swap)
  | [] => trivial
  | x :: p =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_symm
        (ground.swap_congr (BPair.norm_oneValue (w * x)))),
     vecScaleB_neg w p⟩

/-- The balance weighting passes the matrix's memberwise swap. -/
theorem matScaleB_neg (w : BPair) : ∀ M : Mat,
    matOneValue (matScaleB w (matSwap M))
      (matSwap (matScaleB w M))
  | [] => trivial
  | r :: M => ⟨vecScaleB_neg w r, matScaleB_neg w M⟩

private theorem levelEntryB (y x : Pos) (e : BPair) :
    (e.scale y + (e.scale x).swap).oneValue ((BPair.mk y x * e).norm) :=
  BPair.oneValue_trans
    (BPair.oneValue_of_eq (by
      show BPair.mk (e.fst * y + e.snd * x) (e.snd * y + e.fst * x)
        = BPair.mk (y * e.fst + x * e.snd) (y * e.snd + x * e.fst)
      rw [ground.mul_comm e.fst y, ground.mul_comm e.snd x,
        ground.mul_comm e.snd y, ground.mul_comm e.fst x]))
    (BPair.oneValue_symm (BPair.norm_oneValue _))

private theorem levelRowB (y x : Pos) : ∀ r : List BPair,
    poly.oneValue
      (List.zipWith (fun a b => a + b) (r.map (fun z => z.scale y))
        ((r.map (fun z => z.scale x)).map BPair.swap))
      (poly.scaleP (BPair.mk y x) r)
  | [] => trivial
  | e :: r => ⟨levelEntryB y x e, levelRowB y x r⟩

/-- The level pair's weighting: a level's two members cross-added
onto the sides read the pair weighting of the gram, entry by entry —
the site datum's level part is the balance weighting at the level
pair. -/
theorem levelScaleB (y x : Pos) : ∀ G : Mat,
    matOneValue (matAdd (matScale y G) (matSwap (matScale x G)))
      (matScaleB (BPair.mk y x) G)
  | [] => trivial
  | r :: G => ⟨levelRowB y x r, levelScaleB y x G⟩

private theorem scaleOneRow : ∀ r : List BPair,
    r.map (fun x => x.scale Pos.one) = r
  | [] => rfl
  | a :: t => by
    show a.scale Pos.one :: t.map (fun x => x.scale Pos.one) = a :: t
    rw [BPair.scale_one, scaleOneRow t]

/-- The unit rescaling is the matrix itself. -/
theorem matScale_one : ∀ m : Mat, matScale Pos.one m = m
  | [] => rfl
  | r :: t => by
    show r.map (fun x => x.scale Pos.one) :: matScale Pos.one t = r :: t
    rw [scaleOneRow r, matScale_one t]

/-- The rescaling at a joined weight splits at the sum: each entry
distributes over the weight's two summands. -/
private theorem scaleRow_addW (a b : Pos) : ∀ r : List BPair,
    r.map (fun x => x.scale (a + b))
      = List.zipWith (fun x y => x + y)
          (r.map (fun x => x.scale a)) (r.map (fun x => x.scale b))
  | [] => rfl
  | e :: t => by
    show e.scale (a + b) :: t.map (fun x => x.scale (a + b))
      = (e.scale a + e.scale b)
        :: List.zipWith (fun x y => x + y)
            (t.map (fun x => x.scale a)) (t.map (fun x => x.scale b))
    rw [BPair.scale_addW e a b, scaleRow_addW a b t]

/-- The matrix rescaling at a joined weight is the two rescalings'
sum. -/
theorem matScale_addW (a b : Pos) : ∀ M : Mat,
    matScale (a + b) M = matAdd (matScale a M) (matScale b M)
  | [] => rfl
  | r :: t => by
    show r.map (fun x => x.scale (a + b)) :: matScale (a + b) t
      = List.zipWith (fun x y => x + y)
          (r.map (fun x => x.scale a)) (r.map (fun x => x.scale b))
        :: matAdd (matScale a t) (matScale b t)
    rw [scaleRow_addW a b r, matScale_addW a b t]

/-- The rescaling keeps the order read. -/
theorem sqAt_matScale (o : Nat) (w : Pos) (M : Mat)
    (hM : sqAt M o) : sqAt (matScale w M) o :=
  elim.sqAt_of ((length_matScale w M).trans (elim.sqAt_len hM))
    (elim.rowsLen_mapRows (fun x => x.scale w) M o
      (elim.rowsLen_of_sqAt hM))

/-- The site datum keeps the stated order, the join of the first
member with the second's swap. -/
theorem sqAt_siteDatum (o : Nat) (X Y : Mat) (hX : elim.sqAt X o)
    (hY : elim.sqAt Y o) : elim.sqAt (siteDatum X Y) o :=
  elim.sqAt_matAdd o X (elim.matSwap Y) hX (elim.sqAt_matSwap o Y hY)

/-- The site structure read entrywise: the datum's entry at a key
pair is the first member's own joined to the second's memberwise
swap — `def:pencil`'s join `α E = β M + H` at `lem:inertia`'s
elimination datum, `A = B + S` read entry by entry. -/
theorem siteDatum_entry (A B : Mat) (n : Nat) (hA : elim.rowsLen n A)
    (hB : elim.rowsLen n B) (i j : Nat) (hiA : i < A.length)
    (hiB : i < B.length) (hj : j < n) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (siteDatum A B) i) j
      = ground.getAt BPair.unit (ground.getAt ([] : List BPair) A i) j
        + (ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) B i) j).swap := by
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
      (elim.matAdd A (elim.matSwap B)) i) j = _
  rw [elim.entry_matAdd A (elim.matSwap B) n hA
      (elim.rowsLen_mapRows BPair.swap B n hB) i j hiA
      (by rw [elim.length_matSwap]; exact hiB) hj,
    elim.entry_matSwap B n hB i j hiB hj]

/-- The rescaling distributes over the entrywise sum, row by row. -/
private theorem scaleRow_add (c : Pos) : ∀ r s : List BPair,
    (List.zipWith (fun x y => x + y) r s).map (fun z => z.scale c)
      = List.zipWith (fun x y => x + y)
          (r.map (fun z => z.scale c)) (s.map (fun z => z.scale c))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: r, b :: s => by
    show (a + b).scale c
        :: (List.zipWith (fun x y => x + y) r s).map (fun z => z.scale c)
      = (a.scale c + b.scale c)
        :: List.zipWith (fun x y => x + y)
            (r.map (fun z => z.scale c)) (s.map (fun z => z.scale c))
    rw [BPair.scale_add a b c, scaleRow_add c r s]

/-- The rescaling distributes over the entrywise sum. -/
theorem matScale_matAdd (c : Pos) : ∀ A B : Mat,
    matScale c (matAdd A B) = matAdd (matScale c A) (matScale c B)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | r :: A, s :: B => by
    show (List.zipWith (fun x y => x + y) r s).map (fun z => z.scale c)
        :: matScale c (matAdd A B)
      = List.zipWith (fun x y => x + y)
          (r.map (fun z => z.scale c)) (s.map (fun z => z.scale c))
        :: matAdd (matScale c A) (matScale c B)
    rw [scaleRow_add c r s, matScale_matAdd c A B]

/-- The rescaling commutes with the memberwise swap, row by row: at
each entry both spellings read `⟨v w : u w⟩`. -/
private theorem scaleRow_swap (c : Pos) : ∀ r : List BPair,
    (r.map BPair.swap).map (fun z => z.scale c)
      = (r.map (fun z => z.scale c)).map BPair.swap
  | [] => rfl
  | a :: r =>
    congrArg (fun t => a.swap.scale c :: t) (scaleRow_swap c r)

/-- The rescaling commutes with the memberwise swap. -/
theorem matScale_matSwap (c : Pos) : ∀ A : Mat,
    matScale c (matSwap A) = matSwap (matScale c A)
  | [] => rfl
  | r :: A => by
    show (r.map BPair.swap).map (fun z => z.scale c)
        :: matScale c (matSwap A)
      = (r.map (fun z => z.scale c)).map BPair.swap
        :: matSwap (matScale c A)
    rw [scaleRow_swap c r, matScale_matSwap c A]

/-- Two rescalings compose at their weights' product, row by row. -/
private theorem scaleRow_scale (a b : Pos) : ∀ r : List BPair,
    (r.map (fun z => z.scale a)).map (fun z => z.scale b)
      = r.map (fun z => z.scale (b * a))
  | [] => rfl
  | z :: r => by
    show (z.scale a).scale b
        :: (r.map (fun w => w.scale a)).map (fun w => w.scale b)
      = z.scale (b * a) :: r.map (fun w => w.scale (b * a))
    rw [BPair.scale_scale z a b, ground.mul_comm a b, scaleRow_scale a b r]

/-- A datum joined to itself is its rescaling by two. -/
theorem matScale_two (M : Mat) : matAdd M M = matScale 2 M := by
  rw [show (2 : Pos) = Pos.one + Pos.one from rfl, matScale_addW,
    matScale_one]

/-- Two rescalings compose at their weights' product. -/
theorem matScale_matScale (a b : Pos) : ∀ M : Mat,
    matScale b (matScale a M) = matScale (b * a) M
  | [] => rfl
  | r :: M => by
    show (r.map (fun z => z.scale a)).map (fun z => z.scale b)
        :: matScale b (matScale a M)
      = r.map (fun z => z.scale (b * a)) :: matScale (b * a) M
    rw [scaleRow_scale a b r, matScale_matScale a b M]

/-- A positive rescaling reads back: two matrices whose rescalings by
one weight read one value read one value themselves, entry by entry
at the product's injectivity. -/
theorem matOne_unscale (w : Pos) (n : Nat) (A B : Mat)
    (hAl : A.length = n) (hAr : rowsLen n A)
    (hBl : B.length = n) (hBr : rowsLen n B)
    (h : matOneValue (matScale w A) (matScale w B)) : matOneValue A B := by
  refine matOne_of_entries A B n hAl hAr hBl hBr ?_
  intro i j hi hj
  have hiA : i < A.length := by rw [hAl]; exact hi
  have hiB : i < B.length := by rw [hBl]; exact hi
  have hi' : i < (matScale w A).length := by rw [length_matScale]; exact hiA
  have hrow := poly.oneValue_getAt j (matOne_entries _ _ h i hi')
  have eA : matScale w A = A.map (fun r => r.map (fun x => x.scale w)) := rfl
  have eB : matScale w B = B.map (fun r => r.map (fun x => x.scale w)) := rfl
  rw [eA, eB, ground.getAt_map [] [] _ A i hiA, ground.getAt_map [] [] _ B i hiB,
    ground.getAt_map BPair.unit BPair.unit _ _ j
      (by rw [rowsLen_getAt A i hAr hiA]; exact hj),
    ground.getAt_map BPair.unit BPair.unit _ _ j
      (by rw [rowsLen_getAt B i hBr hiB]; exact hj)] at hrow
  exact BPair.scale_cancel hrow

/-- The rescaling's rows keep their column counts, so the square
read reflects: the scaled matrix at the stated order reads the
matrix at it. -/
private theorem sqAtRows (c : Pos) (o : Nat) : ∀ H : Mat,
    (List.all (matScale c H) (fun r => Nat.beq r.length o)) = true →
    (List.all H (fun r => Nat.beq r.length o)) = true
  | [], _ => rfl
  | r :: t, h => by
    have hs := ground.andSplitB h
    have hh : Nat.beq r.length o = true := by
      have hm : Nat.beq (List.map (fun x => BPair.scale x c) r).length
          o = true := hs.1
      rw [ground.length_map (fun x => BPair.scale x c) r] at hm
      exact hm
    show (Nat.beq r.length o
      && List.all t (fun r => Nat.beq r.length o)) = true
    rw [hh, sqAtRows c o t hs.2]
    rfl

/-- The square read reflects across the rescaling, the row count
and every row's width the scaled matrix's own — `sqAt_matScale`'s
converse, the stated pair. -/
theorem sqAt_matScale_reflect {o : Nat} (c : Pos) (H : Mat)
    (h : sqAt (matScale c H) o) : sqAt H o := by
  have hs := ground.andSplitB h
  have hl : Nat.beq H.length o = true := by
    have hm := hs.1
    rw [inertia.length_matScale c H] at hm
    exact hm
  show (Nat.beq H.length o
    && List.all H (fun r => Nat.beq r.length o)) = true
  rw [hl, sqAtRows c o H hs.2]
  rfl

/-- The identity at an order. -/
def idMat (n : Nat) : Mat :=
  (List.range n).map (elim.idRow n)

/-- The identity's row is its key's indicator. -/
theorem idMat_row (n i : Nat) (hi : i < n) :
    ground.getAt ([] : List BPair) (idMat n) i = elim.idRow n i :=
  ground.matOf_row [] n n _ i hi

/-- The identity's entry: the key comparison's own indicator. -/
theorem getAt_idMat (n i j : Nat) (hi : i < n) (hj : j < n) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (idMat n) i) j
      = if j = i then BPair.ofNat 1 else BPair.unit :=
  ground.matOf_entry [] BPair.unit n n _ i j hi hj

/-- A split enters cleared: over pair data the congruence reads at
an integer `T`, its determinant off equal members with the adjugate
against the determinant the witness's solve — the two product reads
`T Tw = det · I` and `Tw T = det · I` at that carrier
(`lem:inertia`).  The carrier's shape datum makes every frame
square, so the instance decides the determinant at the descent's
read outright (`elim.detD_eq` with `elim.minor_detL`, the weight
moved by `matScaleB_congr`). -/
def clearedCongr {o : Nat} (T Tw : SqMat o) : Prop :=
  (minor T.val).offUnit
  ∧ matOneValue (matMul T.val Tw.val)
      (matScaleB (minor T.val) (idMat o))
  ∧ matOneValue (matMul Tw.val T.val)
      (matScaleB (minor T.val) (idMat o))

instance {o : Nat} (T Tw : SqMat o) : Decidable (clearedCongr T Tw) :=
  have hsq : rowsLen T.val.length T.val := by
    rw [sqAt_len T.shape]
    exact rowsLen_of_sqAt T.shape
  have hDM : (elim.detD T.val).oneValue (minor T.val) :=
    BPair.oneValue_trans (elim.detD_eq T.val hsq)
      (BPair.oneValue_symm (elim.minor_detL T.val hsq))
  have hSc : matOneValue (matScaleB (elim.detD T.val) (idMat o))
      (matScaleB (minor T.val) (idMat o)) :=
    matScaleB_congr hDM (idMat o)
  decidable_of_iff
    ((elim.detD T.val).offUnit
     ∧ matOneValue (matMul T.val Tw.val)
         (matScaleB (elim.detD T.val) (idMat o))
     ∧ matOneValue (matMul Tw.val T.val)
         (matScaleB (elim.detD T.val) (idMat o)))
    ⟨fun x => ⟨fun hu => x.1 (BPair.oneValue_trans hDM hu),
      matOne_trans x.2.1 hSc, matOne_trans x.2.2 hSc⟩,
     fun x =>
      ⟨fun hu =>
        x.1 (BPair.oneValue_trans (BPair.oneValue_symm hDM) hu),
       matOne_trans x.2.1 (matOne_symm hSc),
       matOne_trans x.2.2 (matOne_symm hSc)⟩⟩

set_option genInjectivity false in
/-- A split's nonsingular block: an order-1 entry, or a symmetric
order-2 block at its three data. -/
inductive SBlock where
  | one (a : BPair)
  | two (a b c : BPair)

/-- The block's order. -/
def SBlock.order : SBlock → Nat
  | .one _ => 1
  | .two _ _ _ => 2

/-- The block's determinant: the entry at order one, and
`a c + (b²)`'s balance partner collected at order two. -/
def SBlock.det : SBlock → BPair
  | .one a => a
  | .two a b c => (a * c + (b * b).swap).norm

/-- The block's lower-side unit count: an order-1 block its entry's
side; a 2×2 block one per side at the determinant's lower side, the
mixed block, and the diagonal's shared side at the upper, the
identity `S₁₁S₂₂ = det + S₁₂²` its warrant. -/
def SBlock.rev : SBlock → Nat
  | .one a =>
    match a.side with
    | .lt _ _ => 1
    | .eq _ => 0
    | .gt _ _ => 0
  | .two a b c =>
    match (SBlock.det (.two a b c)).side with
    | .lt _ _ => 1
    | .eq _ => 0
    | .gt _ _ =>
      match a.side with
      | .lt _ _ => 2
      | .eq _ => 0
      | .gt _ _ => 0

/-- The block orders' total with the kernel's, the split's order. -/
def widthOf (bs : List SBlock) (k : Nat) : Nat :=
  bs.foldl (fun n b => n + b.order) k

/-- The block diagonal assembled at the blocks with the trailing
kernel block, every kernel entry the sum's unit. -/
def blockMat : List SBlock → Nat → Mat
  | [], k => (List.range k).map (fun _ => List.replicate k BPair.unit)
  | .one a :: bs, k =>
    (a :: List.replicate (widthOf bs k) BPair.unit)
      :: (blockMat bs k).map (fun r => BPair.unit :: r)
  | .two a b c :: bs, k =>
    (a :: b :: List.replicate (widthOf bs k) BPair.unit)
      :: (b :: c :: List.replicate (widthOf bs k) BPair.unit)
      :: (blockMat bs k).map (fun r => BPair.unit :: BPair.unit :: r)

set_option genInjectivity false in
/-- A pivot split's certificate data at a stated order: the
congruence at the square carrier with its invertibility witness at
the same carrier — the adjugate, the cleared stage's solved inverse
against the determinant — the nonsingular blocks in their order, and
the kernel block's order, the block widths' tie the constructor's
own read. -/
structure Split (n : Nat) where
  T : SqMat n
  Tw : SqMat n
  blocks : List SBlock
  kern : Nat
  width : Nat.beq (widthOf blocks kern) n = true

/-- The split read at a datum: the datum square at the certificate's
stated order — the carrier's read at the one chokepoint every count
runs through — with the congruence entering cleared
(`clearedCongr`), the congruence identity
`Tᵀ S T = D` at the assembled block diagonal, and the blocks'
nonsingularity; the congruence's own order and the block widths' tie
are the certificate type's constructor reads, an off-order
certificate unrepresentable. -/
def splitRead {n : Nat} (S : Mat) (sp : Split n) : Prop :=
  sqAt S n
  ∧ clearedCongr sp.T sp.Tw
  ∧ matOneValue (matMul (transposeM sp.T.val) (matMul S sp.T.val))
      (blockMat sp.blocks sp.kern)
  ∧ (sp.blocks.all (fun b => !(decide (b.det.oneValue BPair.unit)))) = true

instance {n : Nat} (S : Mat) (sp : Split n) :
    Decidable (splitRead S sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ = _))

/-- The reversal count at a split, the blocks' lower-side fold. -/
def revAt {n : Nat} (sp : Split n) : Nat :=
  sp.blocks.foldl (fun m b => m + b.rev) 0

/-- The positive-semidefinite read: the nonsingular blocks read the
upper side throughout, the lower-side fold at the sum's unit. -/
def psdAt {n : Nat} (sp : Split n) : Prop := revAt sp = 0

instance {n : Nat} (sp : Split n) : Decidable (psdAt sp) :=
  inferInstanceAs (Decidable (_ = _))

/-- The positive-definite read: the upper side throughout with the
nonsingular orders summing to the datum's, the kernel block's order
read off. -/
def pdAt {n : Nat} (sp : Split n) : Prop := revAt sp = 0 ∧ sp.kern = 0

instance {n : Nat} (sp : Split n) : Decidable (pdAt sp) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The rank at a split, the kernel block's complement. -/
def rankAt {n : Nat} (sp : Split n) : Nat := widthOf sp.blocks 0

/-! The transport tier, the certificate read back at the datum's own
quadratic form: the positive-semidefinite read prices the form at or
above the sum's unit at every vector (`psd_all`), and an occupied
reversal count exhibits a vector pricing it strictly below
(`rev_witness`) — the requirement layer's two consumptions.  The
congruence inverts through the certificate's adjugate witness: the
witness's product read carries a vector back at the determinant's
clearing, and the clearing's square sits strictly above the unit at
the determinant off equal members, so the cleared read transports
both ways.  The block diagonal's own reads are the induction over
the block list at the peeled form (`bQuad`) — a kernel block the
sum's unit, an order-1 block its entry's square multiple, and a 2×2
block the completed square `a q = (a x + b y)² + det y²` at the
cleared leading entry, the nonsingularity conjunct refusing the
equal-membered leading entry at a strictly upper determinant; the
witnesses at an occupied count are the mixed-block recipe, the
lower-side entry's own place, the exchanged pair `(b, ǎ)` at a
strictly upper entry reading `a det`, and the doubled pair
`((c + 1)ˇ, b + b)` at the equal-membered entry reading `(b + b)²`
swapped. -/

/-- A strictly positive datum against a strictly negative one lands
strictly below the sum's unit. -/
private theorem mulNegPos {s q : BPair} (hs : BPair.unit < s)
    (hq : q < BPair.unit) : s * q < BPair.unit :=
  ground.BPair.lt_congr
    (ground.BPair.oneValue_of_eq (ground.BPair.mul_comm q s))
    (ground.BPair.oneValue_refl BPair.unit)
    (ground.mulNegPos hq hs)

/-- A strictly positive clearing reflects the at-or-above read. -/
theorem scaleRefl {s q : BPair} (hs : BPair.unit < s)
    (h : BPair.unit ≤ s * q) : BPair.unit ≤ q :=
  ground.leB_of_not_lt (fun hq => ground.leB_not_lt h (mulNegPos hs hq))

/-! The block diagonal's peeled quadratic form: the pairing against
the block matrix's own action at the plain fold, peeled one block at
a time with the padded rows dropping at the sum's unit. -/

/-- The block diagonal's quadratic form at the plain fold. -/
private def bQuad (bs : List SBlock) (k : Nat) (c : List BPair) : BPair :=
  dotP c ((blockMat bs k).map (fun r => dotP r c))

private theorem peel_nil (k : Nat) (c : List BPair) :
    (bQuad [] k c).oneValue BPair.unit := by
  show (dotP c (((List.range k).map
      (fun _ => List.replicate k BPair.unit)).map
    (fun r => dotP r c))).oneValue BPair.unit
  rw [ground.map_map]
  exact dotP_null_tail_right c _
    (poly.unitTail_map _ (List.range k)
      (fun _ _ => dotP_null_tail_left _ c (poly.unitTail_replicate k)))

private theorem peel_one (a : BPair) (bs : List SBlock) (k : Nat)
    (x : BPair) (c' : List BPair) :
    (bQuad (SBlock.one a :: bs) k (x :: c')).oneValue
      (x * (a * x) + bQuad bs k c') := by
  show (x * dotP (a :: List.replicate (widthOf bs k) BPair.unit)
        (x :: c')
      + dotP c' (((blockMat bs k).map (fun r => BPair.unit :: r)).map
        (fun r => dotP r (x :: c')))).oneValue
    (x * (a * x) + dotP c' ((blockMat bs k).map (fun r => dotP r c')))
  rw [ground.map_map]
  refine BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl x) ?_)
    (dotP_oneValue_right c' _ _ (poly.oneValue_map _ _ _ (fun r _ => ?_)))
  · show (a * x + dotP (List.replicate (widthOf bs k) BPair.unit)
      c').oneValue (a * x)
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (a * x))
        (dotP_null_tail_left _ c' (poly.unitTail_replicate _)))
      (BPair.add_unit (a * x))
  · show (BPair.unit * x + dotP r c').oneValue (dotP r c')
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul x) (BPair.oneValue_refl _))
      (BPair.unit_add _)

private theorem peel_two (a b d : BPair) (bs : List SBlock) (k : Nat)
    (x y : BPair) (c' : List BPair) :
    (bQuad (SBlock.two a b d :: bs) k (x :: y :: c')).oneValue
      ((x * (a * x + b * y) + y * (b * x + d * y)) + bQuad bs k c') := by
  show (x * dotP (a :: b :: List.replicate (widthOf bs k) BPair.unit)
        (x :: y :: c')
      + (y * dotP (b :: d :: List.replicate (widthOf bs k) BPair.unit)
          (x :: y :: c')
        + dotP c' (((blockMat bs k).map
            (fun r => BPair.unit :: BPair.unit :: r)).map
          (fun r => dotP r (x :: y :: c'))))).oneValue
    ((x * (a * x + b * y) + y * (b * x + d * y))
      + dotP c' ((blockMat bs k).map (fun r => dotP r c')))
  rw [ground.map_map, BPair.add_assoc]
  refine BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl x) ?_)
    (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl y) ?_)
      (dotP_oneValue_right c' _ _ (poly.oneValue_map _ _ _ (fun r _ => ?_))))
  · show (a * x + (b * y
      + dotP (List.replicate (widthOf bs k) BPair.unit) c')).oneValue
        (a * x + b * y)
    exact BPair.add_congr (BPair.oneValue_refl (a * x))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (b * y))
          (dotP_null_tail_left _ c' (poly.unitTail_replicate _)))
        (BPair.add_unit (b * y)))
  · show (b * x + (d * y
      + dotP (List.replicate (widthOf bs k) BPair.unit) c')).oneValue
        (b * x + d * y)
    exact BPair.add_congr (BPair.oneValue_refl (b * x))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (d * y))
          (dotP_null_tail_left _ c' (poly.unitTail_replicate _)))
        (BPair.add_unit (d * y)))
  · show (BPair.unit * x + (BPair.unit * y + dotP r c')).oneValue
      (dotP r c')
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul x)
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul y) (BPair.oneValue_refl _))
          (BPair.unit_add _)))
      (BPair.unit_add _)

private theorem peel_two1 (a b d : BPair) (bs : List SBlock) (k : Nat)
    (x : BPair) :
    (bQuad (SBlock.two a b d :: bs) k [x]).oneValue (x * (a * x)) := by
  show (x * dotP (a :: b :: List.replicate (widthOf bs k) BPair.unit)
      [x] + BPair.unit).oneValue (x * (a * x))
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  refine BPair.mul_congr (BPair.oneValue_refl x) ?_
  show (a * x + BPair.unit).oneValue (a * x)
  exact BPair.add_unit (a * x)

/-! The block reads at the split's own hypotheses: the nonsingularity
conjunct and the reversal fold read block by block. -/



/-- The reversal fold peels its head block. -/
theorem revSplit {b : SBlock} {bs : List SBlock} :
    (b :: bs).foldl (fun m z => m + z.rev) 0
      = b.rev + bs.foldl (fun m z => m + z.rev) 0 := by
  show bs.foldl (fun m z => m + z.rev) (0 + b.rev)
    = b.rev + bs.foldl (fun m z => m + z.rev) 0
  rw [ground.foldlSeed (fun z => z.rev) bs (0 + b.rev), Nat.zero_add]

/-- The block widths' fold carries a seed shift out. -/
theorem widthOf_shift : ∀ (bs : List SBlock) (a d : Nat),
    widthOf bs (a + d) = widthOf bs a + d
  | [], _, _ => rfl
  | b :: t, a, d => by
    show widthOf t (a + d + b.order) = widthOf t (a + b.order) + d
    rw [Nat.add_right_comm a d b.order]
    exact widthOf_shift t (a + b.order) d

/-- An order-1 block at a vanishing reversal count with its entry off
equal members reads the entry strictly above the sum's unit. -/
theorem oneUp {a : BPair} (hdet : ¬ a.oneValue BPair.unit)
    (hrev : (SBlock.one a).rev = 0) : BPair.unit < a := by
  match hs : a.side with
  | Trich.lt g hg =>
    exfalso
    have hone : (SBlock.one a).rev = 1 := by
      show (match a.side with
        | Trich.lt _ _ => 1
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = 1
      rw [hs]
    rw [hone] at hrev
    exact Nat.noConfusion hrev
  | Trich.eq he =>
    exact absurd (show a.fst + Pos.one = Pos.one + a.snd by
      rw [he, ground.add_comm]) hdet
  | Trich.gt g hg => exact unitLtOfSide ⟨g, hg⟩

private theorem detRead (a b d : BPair) :
    ((SBlock.two a b d).det).oneValue (a * d + (b * b).swap) :=
  BPair.norm_oneValue _

/-- A 2×2 block at a vanishing reversal count with its determinant off
equal members reads both the determinant and the leading entry
strictly above the sum's unit. -/
private theorem twoUp {a b d : BPair}
    (hdet : ¬ ((SBlock.two a b d).det).oneValue BPair.unit)
    (hrev : (SBlock.two a b d).rev = 0) :
    BPair.unit < a ∧ BPair.unit < (SBlock.two a b d).det := by
  match hD : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exfalso
    have hone : (SBlock.two a b d).rev = 1 := by
      show (match ((SBlock.two a b d).det).side with
        | Trich.lt _ _ => 1
        | Trich.eq _ => 0
        | Trich.gt _ _ =>
          match a.side with
          | Trich.lt _ _ => 2
          | Trich.eq _ => 0
          | Trich.gt _ _ => 0) = 1
      rw [hD]
    rw [hone] at hrev
    exact Nat.noConfusion hrev
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) hdet
  | Trich.gt gD hgD =>
    have hDpos : BPair.unit < (SBlock.two a b d).det :=
      unitLtOfSide ⟨gD, hgD⟩
    refine ⟨?_, hDpos⟩
    match hs : a.side with
    | Trich.lt g hg =>
      exfalso
      have htwo : (SBlock.two a b d).rev = 2 := by
        show (match ((SBlock.two a b d).det).side with
          | Trich.lt _ _ => 1
          | Trich.eq _ => 0
          | Trich.gt _ _ =>
            match a.side with
            | Trich.lt _ _ => 2
            | Trich.eq _ => 0
            | Trich.gt _ _ => 0) = 2
        rw [hD, hs]
      rw [htwo] at hrev
      exact Nat.noConfusion hrev
    | Trich.eq he =>
      exfalso
      have ha : a.oneValue BPair.unit := by
        show a.fst + Pos.one = Pos.one + a.snd
        rw [he, ground.add_comm]
      have hDs : ((SBlock.two a b d).det).oneValue ((b * b).swap) :=
        BPair.oneValue_trans (detRead a b d)
          (BPair.oneValue_trans
            (BPair.add_congr
              (BPair.oneValue_trans (BPair.mul_congr_left ha)
                (BPair.unit_mul d))
              (BPair.oneValue_refl ((b * b).swap)))
            (BPair.unit_add ((b * b).swap)))
      exact ground.leB_not_lt (unitLeSq b)
        (ground.ltUnitOfSide (show (b * b).fst < (b * b).snd from
          ground.sideOfUnitLt (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
            hDs hDpos)))
    | Trich.gt g hg => exact unitLtOfSide ⟨g, hg⟩

/-! The completed square at the cleared leading entry: the block's
quadratic times its leading entry is the linear form's square joined
to the determinant against the second entry's square. -/

private theorem sqFill (a b d x y : BPair) :
    a * (x * (a * x + b * y) + y * (b * x + d * y)) + b * b * (y * y)
      = (a * x + b * y) * (a * x + b * y) + a * d * (y * y) := by
  have hi : a * (x * (a * x + b * y) + y * (b * x + d * y))
      = a * x * (a * x + b * y) + a * y * (b * x + d * y) := by
    rw [BPair.left_distrib, ← BPair.mul_assoc, ← BPair.mul_assoc]
  have hii : (a * x + b * y) * (a * x + b * y)
      = a * x * (a * x + b * y) + b * y * (a * x + b * y) :=
    BPair.right_distrib _ _ _
  have hiii : a * y * (b * x + d * y) + b * b * (y * y)
      = b * y * (a * x + b * y) + a * d * (y * y) := by
    rw [BPair.left_distrib (a * y) (b * x) (d * y),
      BPair.left_distrib (b * y) (a * x) (b * y),
      BPair.mul_mul_mul_comm a y b x, BPair.mul_mul_mul_comm a y d y,
      BPair.mul_mul_mul_comm b y a x, BPair.mul_mul_mul_comm b b y y,
      BPair.mul_comm b a,
      BPair.add_assoc (a * b * (y * x)) (a * d * (y * y))
        (b * y * (b * y)),
      BPair.add_comm (a * d * (y * y)) (b * y * (b * y)),
      ← BPair.add_assoc (a * b * (y * x)) (b * y * (b * y))
        (a * d * (y * y))]
  rw [hi, hii, BPair.add_assoc, hiii, ← BPair.add_assoc]

private theorem sqComplete (a b d x y : BPair) :
    (a * (x * (a * x + b * y) + y * (b * x + d * y))).oneValue
      ((a * x + b * y) * (a * x + b * y)
        + (a * d + (b * b).swap) * (y * y)) := by
  refine ground.BPair.add_cancel (c := b * b * (y * y)) ?_
  rw [sqFill a b d x y, BPair.right_distrib (a * d) ((b * b).swap)
      (y * y), BPair.swap_mul (b * b) (y * y),
    BPair.add_assoc ((a * x + b * y) * (a * x + b * y))
      (a * d * (y * y) + (b * b * (y * y)).swap) (b * b * (y * y)),
    BPair.add_assoc (a * d * (y * y)) ((b * b * (y * y)).swap)
      (b * b * (y * y))]
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  exact BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl (a * d * (y * y)))
      (BPair.swap_add_null (BPair.oneValue_refl (b * b * (y * y)))))
    (BPair.add_unit (a * d * (y * y))))

/-! The block list's two reads: the at-or-above price at a vanishing
count, and the witness at an occupied one. -/

private theorem block_psd : ∀ (bs : List SBlock) (k : Nat),
    (bs.all (fun z => !(decide (z.det.oneValue BPair.unit)))) = true →
    bs.foldl (fun m z => m + z.rev) 0 = 0 →
    ∀ c : List BPair, BPair.unit ≤ bQuad bs k c
  | [], k, _, _, c =>
    ground.leB_congr_right (BPair.oneValue_symm (peel_nil k c))
      (ground.leB_refl BPair.unit)
  | SBlock.one _ :: _, _, _, _, [] => ground.leB_refl BPair.unit
  | SBlock.one a :: bs, k, hall, hrev, x :: c' => by
    have ha : BPair.unit < a :=
      oneUp (ground.notOfBang ((ground.andSplitB hall).1))
        ((ground.addZeroN (revSplit.symm.trans hrev)).1)
    refine ground.leB_congr_right
      (BPair.oneValue_symm (peel_one a bs k x c')) ?_
    refine unitLeAdd ?_
      (block_psd bs k ((ground.andSplitB hall).2)
        ((ground.addZeroN (revSplit.symm.trans hrev)).2) c')
    rw [BPair.mul_left_comm x a x]
    exact unitLeMul (ground.leB_of_lt ha) (unitLeSq x)
  | SBlock.two _ _ _ :: _, _, _, _, [] => ground.leB_refl BPair.unit
  | SBlock.two a b d :: bs, k, hall, hrev, [x] => by
    have hu := twoUp (ground.notOfBang ((ground.andSplitB hall).1))
      ((ground.addZeroN (revSplit.symm.trans hrev)).1)
    refine ground.leB_congr_right
      (BPair.oneValue_symm (peel_two1 a b d bs k x)) ?_
    rw [BPair.mul_left_comm x a x]
    exact unitLeMul (ground.leB_of_lt hu.1) (unitLeSq x)
  | SBlock.two a b d :: bs, k, hall, hrev, x :: y :: c' => by
    have hu := twoUp (ground.notOfBang ((ground.andSplitB hall).1))
      ((ground.addZeroN (revSplit.symm.trans hrev)).1)
    refine ground.leB_congr_right
      (BPair.oneValue_symm (peel_two a b d bs k x y c')) ?_
    refine unitLeAdd ?_
      (block_psd bs k ((ground.andSplitB hall).2)
        ((ground.addZeroN (revSplit.symm.trans hrev)).2) c')
    refine scaleRefl hu.1 ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm (sqComplete a b d x y)) ?_
    refine unitLeAdd (unitLeSq _) ?_
    refine unitLeMul (ground.leB_of_lt ?_) (unitLeSq y)
    exact BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (detRead a b d) hu.2

/-! The weighted identity's action, the congruence's inversion at the
adjugate witness, and the split's two transport theorems. -/

private theorem scaleId_row (w : BPair) (n i : Nat) (hi : i < n) :
    ground.getAt ([] : List BPair) (matScaleB w (idMat n)) i
      = (elim.idRow n i).map (fun x => (w * x).norm) := by
  have hid : (idMat n).length = n :=
    ground.length_mapRange _ n
  rw [show matScaleB w (idMat n)
      = (idMat n).map (fun r => r.map (fun x => (w * x).norm)) from rfl,
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (fun r => r.map (fun x => (w * x).norm)) (idMat n) i
      (by rw [hid]; exact hi),
    idMat_row n i hi]

private theorem scaleRow_entry (w : BPair) (n i q : Nat) (hq : q < n) :
    ground.getAt BPair.unit
        ((elim.idRow n i).map (fun x => (w * x).norm)) q
      = (w * (if q = i then BPair.ofNat 1 else BPair.unit)).norm := by
  rw [ground.getAt_map BPair.unit BPair.unit _ (elim.idRow n i) q
      (by rw [elim.length_idRow]; exact hq),
    elim.getAt_idRow n i q hq]

/-- The weighted identity's action is the weighting itself. -/
theorem scaleId_act (w : BPair) (n : Nat) (u : List BPair)
    (hu : u.length = n) :
    poly.oneValue (matVec (matScaleB w (idMat n)) u) (vecScale w u) := by
  have hr : (List.range n).length = n := ground.length_range n
  have hid : (idMat n).length = n :=
    (ground.length_map _ (List.range n)).trans hr
  have hMl : (matScaleB w (idMat n)).length = n :=
    (ground.length_map _ (idMat n)).trans hid
  refine poly.oneValue_of_entries _ _ ?_ ?_
  · rw [matVec_length, hMl, length_vecScale, hu]
  · intro i hi
    rw [matVec_length, hMl] at hi
    have hRl : ((elim.idRow n i).map
        (fun x => (w * x).norm)).length = n :=
      (ground.length_map _ (elim.idRow n i)).trans
        (elim.length_idRow n i)
    have hoff : ∀ q, q < ((elim.idRow n i).map
          (fun x => (w * x).norm)).length → ¬ q = i →
        (ground.getAt BPair.unit ((elim.idRow n i).map
          (fun x => (w * x).norm)) q).oneValue BPair.unit := by
      intro q hq hne
      rw [hRl] at hq
      rw [scaleRow_entry w n i q hq, if_neg hne]
      exact BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_unit w)
    have hdiag : (ground.getAt BPair.unit ((elim.idRow n i).map
        (fun x => (w * x).norm)) i).oneValue w := by
      rw [scaleRow_entry w n i i hi, if_pos rfl]
      exact BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_ofNat_one w)
    rw [show matVec (matScaleB w (idMat n)) u
        = (matScaleB w (idMat n)).map (fun r => dotN r u) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit (fun r => dotN r u)
        (matScaleB w (idMat n)) i (by rw [hMl]; exact hi),
      scaleId_row w n i hi,
      show vecScale w u = u.map (fun x => w * x) from rfl,
      ground.getAt_map BPair.unit BPair.unit (fun x => w * x) u i
        (by rw [hu]; exact hi)]
    refine BPair.oneValue_trans (dotN_read _ u) ?_
    rw [dotP_comm _ u]
    refine BPair.oneValue_trans
      (dotP_oneIndex u _ i (by rw [hu, hRl]) (by rw [hRl]; exact hi)
        hoff) ?_
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hdiag)
      (BPair.oneValue_of_eq (BPair.mul_comm _ w))

/-- The adjugate identity at the column side, carried to the action:
the adjugate's product against the list acts as the determinant's
scale, `adj(G) G v` the determinant against `v` at every vector of
the order (`def:elim`'s adjugate identity, `elim.adjM_col_diag` and
`elim.adjM_col_off` entrywise). -/
theorem adjM_col_read (G : Mat) {n : Nat} (hsq : sqAt G n) :
    matOneValue (matMul (adjM G) G) (matScaleB (detL G) (idMat n)) := by
  have hGl : G.length = n := sqAt_len hsq
  have hGr : rowsLen n G := rowsLen_of_sqAt hsq
  cases Nat.eq_zero_or_pos n with
  | inl hz =>
    have hcof : ((List.range G.length).map (fun k => cofVec G k)) = [] :=
      ground.nil_of_length_zero _ ((cofRows_len G).trans (hGl.trans hz))
    have hA : adjM G = [] := by
      show transposeM ((List.range G.length).map (fun k => cofVec G k)) = []
      rw [hcof]
      rfl
    have hI : idMat n = [] :=
      ground.nil_of_length_zero _ ((ground.length_mapRange _ n).trans hz)
    rw [hA, hI]
    trivial
  | inr hpos =>
    have hnG : 0 < ((List.range G.length).map (fun k => cofVec G k)).length := by
      rw [cofRows_len G, hGl]
      exact hpos
    have hAl : (adjM G).length = n := by
      show (transposeM ((List.range G.length).map
        (fun k => cofVec G k))).length = n
      rw [length_transposeM _ (cofRows_rowsLen G) hnG]
      exact hGl
    have hMl : (matMul (adjM G) G).length = n :=
      (length_matMul (adjM G) G).trans hAl
    have hMr : rowsLen n (matMul (adjM G) G) :=
      rowsLen_cast (transposeLen G hGr hGl) (rowsLen_matMul (adjM G) G)
    have hRl : (matScaleB (detL G) (idMat n)).length = n :=
      (ground.length_map _ (idMat n)).trans (ground.length_mapRange _ n)
    have hRr : rowsLen n (matScaleB (detL G) (idMat n)) :=
      rowsLen_mapRows (fun z => (detL G * z).norm) (idMat n) n
        (rowsLen_map (idRow n) n (List.range n)
          (fun k _ => length_idRow n k))
    refine matOne_of_entries _ _ n hMl hMr hRl hRr ?_
    intro i j hi hj
    rw [scaleId_row (detL G) n i hi, scaleRow_entry (detL G) n i j hj]
    by_cases hji : j = i
    · rw [if_pos hji, hji]
      exact BPair.oneValue_trans (adjM_col_diag G hsq i hi)
        (BPair.oneValue_symm
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.mul_ofNat_one (detL G))))
    · rw [if_neg hji]
      exact BPair.oneValue_trans
        (adjM_col_off G hsq i j hi hj (fun he => hji he.symm))
        (BPair.oneValue_symm
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.mul_unit (detL G))))

/-- The adjugate's action against a list's own action pins a vector
at the determinant's scale: the adjugate identity's action read
(`adjM_col_read`) at the vector, the determinant's scaled identity
acting as the scale itself (`def:elim`'s adjugate identity read at a
vector). -/
theorem det_pin {n : Nat} (S : Mat) (hsq : sqAt S n)
    (z : List BPair) (hz : z.length = n) :
    poly.oneValue (matVec (matMul (adjM S) S) z)
      (vecScale (detL S) z) :=
  poly.oneValue_trans
    (matVec_matOne _ _ z (adjM_col_read S hsq))
    (scaleId_act (detL S) n z hz)

/-- The solve read: at a list's action on a vector reading stated
data, the adjugate's action on the data returns the vector at the
determinant's scale, `def:elim`'s adjugate against the list at the
solved column. -/
theorem adj_solve {n : Nat} (S : Mat) (hsq : sqAt S n)
    (z w : List BPair) (hz : z.length = n)
    (h : poly.oneValue (matVec S z) w) :
    poly.oneValue (matVec (adjM S) w) (vecScale (detL S) z) :=
  poly.oneValue_trans
    (matVec_congr (adjM S) w _ (poly.oneValue_symm h))
    (poly.oneValue_trans
      (poly.oneValue_symm
        (matVec_matMul (adjM S) S n (rowsLen_of_sqAt hsq) z hz))
      (det_pin S hsq z hz))

/-- A determinant off equal members refuses every kernel vector but the
unit family: the adjugate carries `X v` back to the determinant's
multiple of `v`, and the determinant withdraws at the product's
injectivity. -/
theorem matVec_null_of_det (X : Mat) {n : Nat} (hsq : sqAt X n)
    (hdet : ¬ (minor X).oneValue BPair.unit)
    (v : List BPair) (hv : v.length = n)
    (h : poly.unitTail (matVec X v)) : poly.unitTail v := by
  have hXl : X.length = n := sqAt_len hsq
  have hXr : rowsLen n X := rowsLen_of_sqAt hsq
  have hAr : rowsLen n (adjM X) :=
    rowsLen_cast hXl (rowsLen_cast (cofRows_len X) (rowsLen_transposeM _))
  have h1 : poly.unitTail (matVec (adjM X) (matVec X v)) :=
    matVec_null (adjM X) _ h
  have h2 : poly.unitTail (matVec (matMul (adjM X) X) v) :=
    poly.unitTail_oneValue_right h1
      (matVec_comp (adjM X) X v n hXr hv (rowsLen_cast hXl.symm hAr))
  have h4 : poly.unitTail (vecScale (detL X) v) :=
    poly.unitTail_oneValue_right h2 (det_pin X hsq v hv)
  have hdet' : ¬ (detL X).oneValue BPair.unit := fun hzero =>
    hdet (BPair.oneValue_trans
      (minor_detL X (rowsLen_cast hXl.symm hXr)) hzero)
  exact unitTail_unscale (detL X) hdet' v h4

/-- Two matrices reading one value price one quadratic form. -/
theorem quadMatOne (A B : Mat) (c : List BPair)
    (h : matOneValue A B) :
    (dotN c (matVec A c)).oneValue (dotN c (matVec B c)) :=
  BPair.oneValue_trans (dotN_read c _)
    (BPair.oneValue_trans
      (dotP_oneValue_right c _ _ (matVec_matOne A B c h))
      (BPair.oneValue_symm (dotN_read c _)))

/-- The congruated pairing at a rectangular carrier: the
congruence's own datum against two vectors is the datum against the
two carried vectors, no invertibility anywhere. -/
theorem congrPair (M T : Mat) (n m : Nat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hTl : T.length = n) (hTr : rowsLen m T)
    (x y : List BPair) (hx : x.length = m) (hy : y.length = m) :
    (dotP (matVec T x) (matVec M (matVec T y))).oneValue
      (dotP x (matVec (matMul (transposeM T) (matMul M T)) y)) := by
  match T, hTl, hTr with
  | [], hTl0, _ =>
    have hM0 : M = [] :=
      ground.nil_of_length_zero M (hMl.trans hTl0.symm)
    rw [hM0]
    match x with
    | [] => exact BPair.oneValue_refl _
    | _ :: _ => exact BPair.oneValue_refl _
  | r :: t, hTl1, hTr1 =>
  have hMTl : (matMul M (r :: t)).length = n := by
    rw [show (matMul M (r :: t)).length = M.length from ground.length_map _ M]
    exact hMl
  have hTtl : (transposeM (r :: t)).length = m :=
    length_transposeM (r :: t) hTr1 (Nat.succ_pos _)
  refine BPair.oneValue_trans
    (dotP_matVec_transpose m (r :: t) x (matVec M (matVec (r :: t) y)) hTr1 hx
      (by rw [matVec_length, hMl, hTl1])) ?_
  refine dotP_oneValue_right x _ _ ?_
  refine poly.oneValue_trans
    (matVec_congr (transposeM (r :: t)) _ _
      (matVec_comp M (r :: t) y m hTr1 hy (rowsLen_cast hTl1.symm hMr))) ?_
  exact matVec_comp (transposeM (r :: t)) (matMul M (r :: t)) y m
    (rowsLen_cast hTtl (rowsLen_matMul M (r :: t))) hy
    (rowsLen_cast hMTl.symm (rowsLen_cast hTl1 (rowsLen_transposeM (r :: t))))

/-- The congruence transports the quadratic form at a rectangular
carrier: the image's form at the datum is the compressed datum's own,
no invertibility anywhere. -/
theorem congQuad (S P : Mat) (n m : Nat) (hsq : sqAt S n)
    (hPr : rowsLen m P) (hPl : P.length = n)
    (c : List BPair) (hc : c.length = m) :
    (dotN (matVec P c) (matVec S (matVec P c))).oneValue
      (dotN c (matVec (matMul (transposeM P) (matMul S P)) c)) := by
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (congrPair S P n m (sqAt_len hsq) (rowsLen_of_sqAt hsq) hPl hPr
      c c hc hc) ?_
  exact BPair.oneValue_symm (dotN_read _ _)

/-- The tied compression's form reads the datum's own at the
carried vector: the congruence transports the read through the
tie, at every rectangular carrier. -/
theorem tieQuad {n m : Nat} (S P W : Mat)
    (hS : sqAt S n) (hPl : P.length = n) (hPr : rowsLen m P)
    (htie : matOneValue (matMul (transposeM P) (matMul S P)) W)
    (x : List BPair) (hx : x.length = m) :
    (dotN (matVec P x) (matVec S (matVec P x))).oneValue
      (dotN x (matVec W x)) :=
  BPair.oneValue_trans (congQuad S P n m hS hPr hPl x hx)
    (quadMatOne _ _ x htie)

/-- The congruence transports the datum's quadratic form to the block
diagonal's, at every vector of the stated order. -/
private theorem congTransport {n : Nat} (S : Mat) (sp : Split n)
    (hsq : sqAt S n)
    (hcong : matOneValue
      (matMul (transposeM sp.T.val) (matMul S sp.T.val))
      (blockMat sp.blocks sp.kern))
    (c : List BPair) (hc : c.length = n) :
    (dotN (matVec sp.T.val c) (matVec S (matVec sp.T.val c))).oneValue
      (dotN c (matVec (blockMat sp.blocks sp.kern) c)) :=
  tieQuad S sp.T.val (blockMat sp.blocks sp.kern) hsq sp.T.rows
    (rowsLen_of_sqAt sp.T.shape) hcong c hc

/-- The positive-semidefinite read at a split prices the datum's
quadratic form at or above the sum's unit at every vector of the
stated order (`lem:inertia`'s first transport clause). -/
theorem psd_all {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) (hp : psdAt sp) :
    ∀ u : List BPair, u.length = n →
      ¬ (dotN u (matVec S u) < BPair.unit) := by
  intro u hu
  obtain ⟨hsq, ⟨hdetT, hprod, _⟩, hcong, hns⟩ := h
  have hTrows : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
  have hTwrows : rowsLen n sp.Tw.val := rowsLen_of_sqAt sp.Tw.shape
  have hTlen : sp.T.val.length = n := sp.T.rows
  have hTwlen : sp.Tw.val.length = n := sp.Tw.rows
  have hSrows : rowsLen n S := rowsLen_of_sqAt hsq
  have hcl : (matVec sp.Tw.val u).length = n := by
    rw [matVec_length]; exact hTwlen
  have hA : poly.oneValue (matVec sp.T.val (matVec sp.Tw.val u))
      (vecScale (minor sp.T.val) u) := by
    refine poly.oneValue_trans
      (matVec_comp sp.T.val sp.Tw.val u n hTwrows hu
        (by rw [hTwlen]; exact hTrows)) ?_
    refine poly.oneValue_trans (matVec_matOne _ _ u hprod) ?_
    exact scaleId_act (minor sp.T.val) n u hu
  have hBlock : BPair.unit ≤ dotN (matVec sp.Tw.val u)
      (matVec (blockMat sp.blocks sp.kern) (matVec sp.Tw.val u)) :=
    ground.leB_congr_right (BPair.oneValue_symm (quadP_read _ _))
      (block_psd sp.blocks sp.kern hns hp _)
  have hUp : BPair.unit ≤ dotN (matVec sp.T.val (matVec sp.Tw.val u))
      (matVec S (matVec sp.T.val (matVec sp.Tw.val u))) :=
    ground.leB_congr_right
      (BPair.oneValue_symm
        (congTransport S sp hsq hcong (matVec sp.Tw.val u) hcl))
      hBlock
  have hwl : (matVec sp.T.val (matVec sp.Tw.val u)).length
      = (vecScale (minor sp.T.val) u).length := by
    rw [matVec_length, hTlen, length_vecScale, hu]
  have hScale : (dotN (matVec sp.T.val (matVec sp.Tw.val u))
      (matVec S (matVec sp.T.val (matVec sp.Tw.val u)))).oneValue
      (minor sp.T.val * minor sp.T.val * dotN u (matVec S u)) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    refine BPair.oneValue_trans (dotP_oneValue_left _ _ _ hA) ?_
    refine BPair.oneValue_trans
      (dotP_oneValue_right _ _ _ (matVec_congr S _ _ hA)) ?_
    refine BPair.oneValue_trans
      (dotP_oneValue_right _ _ _
        (matVec_vecScale_free S (minor sp.T.val) u)) ?_
    refine BPair.oneValue_trans
      (dotP_vecScale_right (vecScale (minor sp.T.val) u)
        (matVec S u) (minor sp.T.val)) ?_
    have hinner : (dotP (vecScale (minor sp.T.val) u)
        (matVec S u)).oneValue
        (minor sp.T.val * dotN u (matVec S u)) := by
      rw [dotP_comm (vecScale (minor sp.T.val) u) (matVec S u)]
      refine BPair.oneValue_trans
        (dotP_vecScale_right (matVec S u) u (minor sp.T.val)) ?_
      refine BPair.mul_congr (BPair.oneValue_refl _) ?_
      rw [dotP_comm (matVec S u) u]
      exact BPair.oneValue_symm (dotN_read u (matVec S u))
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (minor sp.T.val)) hinner) ?_
    exact BPair.oneValue_of_eq
      (BPair.mul_assoc (minor sp.T.val) (minor sp.T.val)
        (dotN u (matVec S u))).symm
  exact ground.leB_not_lt
    (scaleRefl (ground.sq_pos hdetT)
      (ground.leB_congr_right hScale hUp))

/-! The witness tier at an occupied count: the block's own recipe at
the lower-side entry, the exchanged pair, and the doubled pair. -/

private theorem bQuad_null (bs : List SBlock) (k : Nat)
    (c : List BPair) (hc : poly.unitTail c) :
    (bQuad bs k c).oneValue BPair.unit :=
  dotP_null_tail_left c _ hc

private theorem revOcc {b : SBlock} {bs : List SBlock}
    (h : 1 ≤ (b :: bs).foldl (fun m z => m + z.rev) 0) :
    1 ≤ b.rev ∨ 1 ≤ bs.foldl (fun m z => m + z.rev) 0 := by
  have key : 1 ≤ b.rev + bs.foldl (fun m z => m + z.rev) 0 := by
    rw [← revSplit]; exact h
  match hb : b.rev with
  | 0 =>
    refine Or.inr ?_
    rw [hb, Nat.zero_add] at key
    exact key
  | _ + 1 => exact Or.inl (Nat.succ_le_succ (Nat.zero_le _))

private theorem oneDown {a : BPair} (hrev : 1 ≤ (SBlock.one a).rev) :
    a < BPair.unit := by
  match hs : a.side with
  | Trich.lt g hg => exact ground.ltUnitOfSide ⟨g, hg⟩
  | Trich.eq _ =>
    exfalso
    have hz : (SBlock.one a).rev = 0 := by
      show (match a.side with
        | Trich.lt _ _ => 1
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = 0
      rw [hs]
    rw [hz] at hrev
    exact Nat.not_lt_zero 0 hrev
  | Trich.gt _ _ =>
    exfalso
    have hz : (SBlock.one a).rev = 0 := by
      show (match a.side with
        | Trich.lt _ _ => 1
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = 0
      rw [hs]
    rw [hz] at hrev
    exact Nat.not_lt_zero 0 hrev

private theorem twoOcc {a b d : BPair}
    (hdet : ¬ ((SBlock.two a b d).det).oneValue BPair.unit)
    (hrev : 1 ≤ (SBlock.two a b d).rev) :
    a < BPair.unit
      ∨ ((SBlock.two a b d).det < BPair.unit
          ∧ (BPair.unit < a ∨ a.oneValue BPair.unit)) := by
  match hD : ((SBlock.two a b d).det).side with
  | Trich.lt gD hgD =>
    have hdlt : (SBlock.two a b d).det < BPair.unit :=
      ground.ltUnitOfSide ⟨gD, hgD⟩
    match hs : a.side with
    | Trich.lt g hg => exact Or.inl (ground.ltUnitOfSide ⟨g, hg⟩)
    | Trich.eq he =>
      refine Or.inr ⟨hdlt, Or.inr ?_⟩
      show a.fst + Pos.one = Pos.one + a.snd
      rw [he, ground.add_comm]
    | Trich.gt g hg => exact Or.inr ⟨hdlt, Or.inl (unitLtOfSide ⟨g, hg⟩)⟩
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) hdet
  | Trich.gt _ _ =>
    match hs : a.side with
    | Trich.lt g hg => exact Or.inl (ground.ltUnitOfSide ⟨g, hg⟩)
    | Trich.eq _ =>
      exfalso
      have hz : (SBlock.two a b d).rev = 0 := by
        show (match ((SBlock.two a b d).det).side with
          | Trich.lt _ _ => 1
          | Trich.eq _ => 0
          | Trich.gt _ _ =>
            match a.side with
            | Trich.lt _ _ => 2
            | Trich.eq _ => 0
            | Trich.gt _ _ => 0) = 0
        rw [hD, hs]
      rw [hz] at hrev
      exact Nat.not_lt_zero 0 hrev
    | Trich.gt _ _ =>
      exfalso
      have hz : (SBlock.two a b d).rev = 0 := by
        show (match ((SBlock.two a b d).det).side with
          | Trich.lt _ _ => 1
          | Trich.eq _ => 0
          | Trich.gt _ _ =>
            match a.side with
            | Trich.lt _ _ => 2
            | Trich.eq _ => 0
            | Trich.gt _ _ => 0) = 0
        rw [hD, hs]
      rw [hz] at hrev
      exact Nat.not_lt_zero 0 hrev

private theorem swapAddCancel (X Y : BPair) :
    ((X + Y).swap + X).oneValue Y.swap := by
  show X.snd + Y.snd + X.fst + Y.fst = Y.snd + (X.fst + Y.fst + X.snd)
  rw [ground.add_assoc (X.snd + Y.snd) X.fst Y.fst,
    ground.add_comm (X.fst + Y.fst) X.snd,
    ← ground.add_assoc Y.snd X.snd (X.fst + Y.fst),
    ground.add_comm Y.snd X.snd]

private theorem oneSlot (a : BPair) :
    (BPair.ofPos Pos.one * (a * BPair.ofPos Pos.one)).oneValue a := by
  rw [BPair.mul_left_comm (BPair.ofPos Pos.one) a (BPair.ofPos Pos.one)]
  exact BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl a)
      (BPair.mul_ofNat_one (BPair.ofPos Pos.one)))
    (BPair.mul_ofNat_one a)

private theorem twoSlotE1 (a b d : BPair) :
    (BPair.ofPos Pos.one * (a * BPair.ofPos Pos.one + b * BPair.unit)
      + BPair.unit
        * (b * BPair.ofPos Pos.one + d * BPair.unit)).oneValue a := by
  refine BPair.oneValue_trans
    (BPair.add_congr ?_ (BPair.unit_mul _)) (BPair.add_unit a)
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.mul_unit b))
      (BPair.add_unit _))) ?_
  exact oneSlot a

/-- The exchanged pair `(b, ǎ)` reads the leading entry against the
determinant. -/
private theorem twoSlotEx (a b d : BPair) :
    (b * (a * b + b * a.swap)
      + a.swap * (b * b + d * a.swap)).oneValue
      (a * (a * d + (b * b).swap)) := by
  have h1 : (b * (a * b + b * a.swap)).oneValue BPair.unit := by
    refine BPair.oneValue_trans (BPair.mul_congr
      (BPair.oneValue_refl b) ?_) (BPair.mul_unit b)
    rw [BPair.mul_swap b a, BPair.mul_comm b a]
    exact ground.unitOfOne (BPair.oneValue_refl (a * b))
  have h2 : a.swap * (b * b + d * a.swap)
      = (a * (b * b)).swap + d * (a * a) := by
    rw [BPair.left_distrib, BPair.swap_mul a (b * b),
      BPair.mul_left_comm a.swap d a.swap, BPair.swap_sq a]
  have h3 : a * (a * d + (b * b).swap)
      = d * (a * a) + (a * (b * b)).swap := by
    rw [BPair.left_distrib, BPair.mul_swap a (b * b),
      ← BPair.mul_assoc a a d, BPair.mul_comm (a * a) d]
  rw [h2, h3, BPair.add_comm (d * (a * a)) ((a * (b * b)).swap)]
  exact BPair.oneValue_trans
    (BPair.add_congr h1 (BPair.oneValue_refl _))
    (BPair.unit_add _)

/-- The doubled pair `((c + 1)ˇ, b + b)` at an equal-membered leading
entry reads the doubled off-diagonal's square, swapped. -/
private theorem twoSlotDb (a b d x y : BPair)
    (ha : a.oneValue BPair.unit) (hy : y = b + b)
    (hxd : (x + d).oneValue (BPair.ofPos Pos.one).swap) :
    (x * (a * x + b * y) + y * (b * x + d * y)).oneValue ((y * y).swap) := by
  have s1 : (x * (a * x + b * y)).oneValue (x * (b * y)) :=
    BPair.mul_congr (BPair.oneValue_refl x)
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.mul_congr_left ha)
            (BPair.unit_mul x))
          (BPair.oneValue_refl (b * y)))
        (BPair.unit_add (b * y)))
  have s2 : y * (b * x + d * y) = y * (b * x) + y * (d * y) :=
    BPair.left_distrib y (b * x) (d * y)
  have s3 : x * (b * y) + y * (b * x) = x * (y * y) := by
    rw [BPair.mul_left_comm x b y, BPair.mul_left_comm y b x,
      BPair.mul_comm y x, ← BPair.right_distrib b b (x * y), ← hy,
      BPair.mul_left_comm y x y]
  have s4 : y * (d * y) = d * (y * y) := BPair.mul_left_comm y d y
  refine BPair.oneValue_trans
    (BPair.add_congr s1 (BPair.oneValue_of_eq s2)) ?_
  rw [← BPair.add_assoc, s3, s4, ← BPair.right_distrib x d (y * y)]
  refine BPair.oneValue_trans (BPair.mul_congr_left hxd) ?_
  rw [BPair.swap_mul (BPair.ofPos Pos.one) (y * y)]
  refine ground.swap_congr ?_
  rw [BPair.mul_comm (BPair.ofPos Pos.one) (y * y)]
  exact BPair.mul_ofNat_one (y * y)

private theorem twoOffB {a b d : BPair} (ha : a.oneValue BPair.unit)
    (hdet : ¬ ((SBlock.two a b d).det).oneValue BPair.unit) :
    ¬ b.oneValue BPair.unit := by
  intro hb
  refine hdet (BPair.oneValue_trans (detRead a b d) ?_)
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_trans (BPair.mul_congr_left ha) (BPair.unit_mul d))
    (ground.swap_congr (BPair.oneValue_trans (BPair.mul_congr_left hb)
      (BPair.unit_mul b)))) ?_
  exact BPair.unit_add BPair.unit

private theorem doubleSqPos {b : BPair} (hb : ¬ b.oneValue BPair.unit) :
    BPair.unit < (b + b) * (b + b) := by
  rw [BPair.right_distrib b b (b + b), BPair.left_distrib b b b]
  exact unitLtAdd (unitLtAdd (ground.sq_pos hb) (unitLeSq b))
    (unitLeAdd (unitLeSq b) (unitLeSq b))

private theorem swapLtUnit {z : BPair} (h : BPair.unit < z) :
    z.swap < BPair.unit :=
  ground.ltUnitOfSide (show z.swap.fst < z.swap.snd from ground.sideOfUnitLt h)

private theorem block_witness : ∀ (bs : List SBlock) (k : Nat),
    (bs.all (fun z => !(decide (z.det.oneValue BPair.unit)))) = true →
    1 ≤ bs.foldl (fun m z => m + z.rev) 0 →
    ∃ c : List BPair, c.length = widthOf bs k ∧ bQuad bs k c < BPair.unit
  | [], _, _, hrev => absurd hrev (Nat.not_lt_zero 0)
  | SBlock.one a :: bs, k, hall, hrev => by
    match revOcc hrev with
    | Or.inl hhead =>
      refine ⟨BPair.ofPos Pos.one
        :: List.replicate (widthOf bs k) BPair.unit, ?_, ?_⟩
      · show (List.replicate (widthOf bs k) BPair.unit).length + 1
          = widthOf bs (k + 1)
        rw [ground.length_replicate, widthOf_shift bs k 1]
      · refine BPair.lt_congr (BPair.oneValue_symm ?_)
          (BPair.oneValue_refl BPair.unit) (oneDown hhead)
        refine BPair.oneValue_trans
          (peel_one a bs k (BPair.ofPos Pos.one) _) ?_
        exact BPair.oneValue_trans
          (BPair.add_congr (oneSlot a)
            (bQuad_null bs k _ (poly.unitTail_replicate _)))
          (BPair.add_unit a)
    | Or.inr htail =>
      obtain ⟨c', hcl, hlt⟩ := block_witness bs k ((ground.andSplitB hall).2) htail
      refine ⟨BPair.unit :: c', ?_, ?_⟩
      · show c'.length + 1 = widthOf bs (k + 1)
        rw [hcl, widthOf_shift bs k 1]
      · refine BPair.lt_congr (BPair.oneValue_symm ?_)
          (BPair.oneValue_refl BPair.unit) hlt
        refine BPair.oneValue_trans (peel_one a bs k BPair.unit c') ?_
        exact BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_mul (a * BPair.unit))
            (BPair.oneValue_refl _))
          (BPair.unit_add _)
  | SBlock.two a b d :: bs, k, hall, hrev => by
    match revOcc hrev with
    | Or.inl hhead =>
      have hdet : ¬ ((SBlock.two a b d).det).oneValue BPair.unit :=
        ground.notOfBang ((ground.andSplitB hall).1)
      match twoOcc hdet hhead with
      | Or.inl halt =>
        refine ⟨BPair.ofPos Pos.one :: BPair.unit
          :: List.replicate (widthOf bs k) BPair.unit, ?_, ?_⟩
        · show (List.replicate (widthOf bs k) BPair.unit).length + 1 + 1
            = widthOf bs (k + 2)
          rw [ground.length_replicate, widthOf_shift bs k 2]
        · refine BPair.lt_congr (BPair.oneValue_symm ?_)
            (BPair.oneValue_refl BPair.unit) halt
          refine BPair.oneValue_trans
            (peel_two a b d bs k (BPair.ofPos Pos.one) BPair.unit _) ?_
          exact BPair.oneValue_trans
            (BPair.add_congr (twoSlotE1 a b d)
              (bQuad_null bs k _ (poly.unitTail_replicate _)))
            (BPair.add_unit a)
      | Or.inr ⟨hdlt, Or.inl hapos⟩ =>
        refine ⟨b :: a.swap
          :: List.replicate (widthOf bs k) BPair.unit, ?_, ?_⟩
        · show (List.replicate (widthOf bs k) BPair.unit).length + 1 + 1
            = widthOf bs (k + 2)
          rw [ground.length_replicate, widthOf_shift bs k 2]
        · refine BPair.lt_congr (BPair.oneValue_symm ?_)
            (BPair.oneValue_refl BPair.unit)
            (mulNegPos hapos (BPair.lt_congr (detRead a b d)
              (BPair.oneValue_refl BPair.unit) hdlt))
          refine BPair.oneValue_trans
            (peel_two a b d bs k b a.swap _) ?_
          exact BPair.oneValue_trans
            (BPair.add_congr (twoSlotEx a b d)
              (bQuad_null bs k _ (poly.unitTail_replicate _)))
            (BPair.add_unit _)
      | Or.inr ⟨_, Or.inr haeq⟩ =>
        refine ⟨(d + BPair.ofPos Pos.one).swap :: (b + b)
          :: List.replicate (widthOf bs k) BPair.unit, ?_, ?_⟩
        · show (List.replicate (widthOf bs k) BPair.unit).length + 1 + 1
            = widthOf bs (k + 2)
          rw [ground.length_replicate, widthOf_shift bs k 2]
        · refine BPair.lt_congr (BPair.oneValue_symm ?_)
            (BPair.oneValue_refl BPair.unit)
            (swapLtUnit (doubleSqPos (twoOffB haeq hdet)))
          refine BPair.oneValue_trans
            (peel_two a b d bs k (d + BPair.ofPos Pos.one).swap (b + b) _) ?_
          exact BPair.oneValue_trans
            (BPair.add_congr
              (twoSlotDb a b d (d + BPair.ofPos Pos.one).swap (b + b)
                haeq rfl (swapAddCancel d (BPair.ofPos Pos.one)))
              (bQuad_null bs k _ (poly.unitTail_replicate _)))
            (BPair.add_unit _)
    | Or.inr htail =>
      obtain ⟨c', hcl, hlt⟩ := block_witness bs k ((ground.andSplitB hall).2) htail
      refine ⟨BPair.unit :: BPair.unit :: c', ?_, ?_⟩
      · show c'.length + 1 + 1 = widthOf bs (k + 2)
        rw [hcl, widthOf_shift bs k 2]
      · refine BPair.lt_congr (BPair.oneValue_symm ?_)
          (BPair.oneValue_refl BPair.unit) hlt
        refine BPair.oneValue_trans
          (peel_two a b d bs k BPair.unit BPair.unit c') ?_
        refine BPair.oneValue_trans
          (BPair.add_congr
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.unit_mul _) (BPair.unit_mul _))
              (BPair.unit_add BPair.unit))
            (BPair.oneValue_refl _)) ?_
        exact BPair.unit_add _

/-- An occupied reversal count at a split exhibits a vector pricing
the datum's quadratic form strictly below the sum's unit
(`lem:inertia`'s second transport clause). -/
theorem rev_witness {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) (hocc : 1 ≤ revAt sp) :
    ∃ u : List BPair, u.length = n ∧ dotN u (matVec S u) < BPair.unit := by
  obtain ⟨hsq, ⟨_, _, _⟩, hcong, hns⟩ := h
  obtain ⟨c, hcl, hlt⟩ := block_witness sp.blocks sp.kern hns hocc
  have hcn : c.length = n := by
    rw [hcl]; exact Nat.eq_of_beq_eq_true sp.width
  refine ⟨matVec sp.T.val c, ?_, ?_⟩
  · rw [matVec_length]; exact sp.T.rows
  · refine BPair.lt_congr
      (BPair.oneValue_symm (congTransport S sp hsq hcong c hcn))
      (BPair.oneValue_refl BPair.unit) ?_
    exact BPair.lt_congr (BPair.oneValue_symm (quadP_read _ c))
      (BPair.oneValue_refl BPair.unit) hlt

/-- The one-sided comparison's read at one split: `S ⪯ C`, the
split the statement's witness (`lem:inertia`). -/
def leAt {n : Nat} (S C : Mat) (sp : Split n) : Prop :=
  splitRead (siteDatum C S) sp ∧ psdAt sp

instance {n : Nat} (S C : Mat) (sp : Split n) :
    Decidable (leAt S C sp) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The two-sided cap at `C`: `S ⪯ C` with `C + S` positive
semidefinite, two splits the statement's witnesses. -/
def capAt {n : Nat} (S C : Mat) (spU spL : Split n) : Prop :=
  sqAt S n ∧ sqAt C n
  ∧ leAt S C spU
  ∧ splitRead (matAdd C S) spL ∧ psdAt spL

instance {n : Nat} (S C : Mat) (spU spL : Split n) :
    Decidable (capAt S C spU spL) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! Jacobi's rule, the fast route: at leading principal minors of
unequal members the pivots are the minors' successive cofactors, so
the reversal count is the minor sequence's own orientation-reversal
count along `1, m₁, …, m_N`. -/

/-- The minor route's validity: every leading principal minor off
equal members. -/
def minorsUnequal (S : Mat) : Prop :=
  ((List.range S.length).all (fun k =>
    !(decide ((leading S (k + 1)).oneValue BPair.unit)))) = true

instance (S : Mat) : Decidable (minorsUnequal S) :=
  inferInstanceAs (Decidable (_ = _))

private def revGo : Bool → List BPair → Nat
  | _, [] => 0
  | prev, m :: rest =>
    match m.side with
    | .lt _ _ => (if prev then 0 else 1) + revGo true rest
    | .eq _ => revGo prev rest
    | .gt _ _ => (if prev then 1 else 0) + revGo false rest

/-- The orientation-reversal count along the leading minors, seeded
at the upper side, the display's `1`. -/
def jacobiRev (S : Mat) : Nat :=
  revGo false ((List.range S.length).map (fun k => leading S (k + 1)))


/-! `lem:inertia`'s two lists at a split: from a split at lower-side
count `ν` the lower list carries one vector per lower-side unit —
each lower-side order-1 column, both columns of a 2×2 block at the
shared lower side, and each mixed block's lower-side witness — and
the complement list carries the rest of the order: the upper-side
order-1 columns, both columns of a 2×2 at the shared upper side,
each mixed block's upper-side vector (the memberwise swap's own
lower-side witness, the recipe read there) and the kernel block's
columns.  Both lists are the congruence's images of raw vectors
supported at the blocks' own places, so the datum's quadratic form
at a combination is the block diagonal's at the raw combination:
the lower list prices every off-unit combination strictly below the
sum's unit, the complement list prices every combination at or
above it, and the complement's combinations read the unit tail only
at unit coefficients, the witness's clearing the transport.  The
count kit's general tier — the forcing clause, the two-splits
exchange, monotonicity and the compression comparison — is these
two lists' consumer. -/

private theorem sideOfLeUnit {x : BPair} (h : x ≤ BPair.unit) :
    x.fst ≤ x.snd := by
  refine ground.posLeCancelR (c := Pos.one) ?_
  rw [ground.add_comm x.snd Pos.one]
  exact h

private theorem leUnitOfSide {x : BPair} (h : x.fst ≤ x.snd) :
    x ≤ BPair.unit := by
  show x.fst + Pos.one ≤ Pos.one + x.snd
  rw [ground.add_comm Pos.one x.snd]
  exact ground.posLeAdd h (Or.inl rfl)

private theorem leUnitAdd {x y : BPair} (hx : x ≤ BPair.unit)
    (hy : y ≤ BPair.unit) : x + y ≤ BPair.unit :=
  leUnitOfSide (ground.posLeAdd (sideOfLeUnit hx) (sideOfLeUnit hy))

/-- A datum strictly below the sum's unit joined to one at or below
it sits strictly below. -/
theorem ltUnitAddLe {x y : BPair} (hx : x < BPair.unit)
    (hy : y ≤ BPair.unit) : x + y < BPair.unit :=
  ground.ltUnitOfSide (posLtAddLe (ground.sideOfLtUnit hx) (sideOfLeUnit hy))

/-- A datum at or below the sum's unit joined to one strictly below
it sits strictly below. -/
theorem leAddLtUnit {x y : BPair} (hx : x ≤ BPair.unit)
    (hy : y < BPair.unit) : x + y < BPair.unit := by
  rw [BPair.add_comm]
  exact ltUnitAddLe hy hx

private theorem unitLeAddLt {x y : BPair} (hx : BPair.unit ≤ x)
    (hy : BPair.unit < y) : BPair.unit < x + y := by
  rw [BPair.add_comm]
  exact unitLtAdd hy hx

private theorem mulLeUnit {s q : BPair} (hs : BPair.unit ≤ s)
    (hq : q ≤ BPair.unit) : s * q ≤ BPair.unit :=
  leUnitOfSide (ground.crossLe (ground.sideOfUnitLe hs) (sideOfLeUnit hq))

/-- A strictly positive clearing reflects the strictly-above read,
`scaleRefl`'s strict twin. -/
theorem scaleReflLt {s q : BPair} (hs : BPair.unit < s)
    (h : BPair.unit < s * q) : BPair.unit < q := by
  match hq : q.side with
  | Trich.lt g hg =>
    exact absurd h (ground.leB_not_lt
      (ground.leB_of_lt (mulNegPos hs (ground.ltUnitOfSide ⟨g, hg⟩))))
  | Trich.eq he =>
    have hqu : q.oneValue BPair.unit := by
      show q.fst + Pos.one = Pos.one + q.snd
      rw [he, ground.add_comm]
    exact absurd
      (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl s) hqu)
          (BPair.mul_unit s)) h)
      (ground.leB_not_lt (ground.leB_refl BPair.unit))
  | Trich.gt g hg => exact unitLtOfSide ⟨g, hg⟩

private theorem swapOff {x : BPair} (h : ¬ x.oneValue BPair.unit) :
    ¬ x.swap.oneValue BPair.unit := by
  intro hs
  have hs' : x.snd + Pos.one = Pos.one + x.fst := hs
  refine h ?_
  show x.fst + Pos.one = Pos.one + x.snd
  rw [ground.add_comm x.fst Pos.one, ← hs', ground.add_comm]

private theorem ltUnitOfSwap {z : BPair} (h : BPair.unit < z.swap) :
    z < BPair.unit := ground.ltUnitOfSide (ground.sideOfUnitLt h)

private theorem unitLtOfSwapLt {z : BPair} (h : z.swap < BPair.unit) :
    BPair.unit < z := unitLtOfSide (ground.sideOfLtUnit h)

private theorem dblOff {b : BPair} (hb : ¬ b.oneValue BPair.unit) :
    ¬ (b + b).oneValue BPair.unit := fun hz =>
  ground.leB_not_lt (ground.leB_refl BPair.unit)
    (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (elim.oneValue_unit_mul hz) (doubleSqPos hb))

/-! The vector kit at the combinations: the memberwise sum's
congruence, the unit summand's collapse, and the padded family's
combination reading its own shorter one. -/

/-- A unit-tail first summand leaves the second's own value. -/
private theorem vecAddUnitLeft : ∀ {u v : List BPair},
    poly.unitTail u → u.length = v.length →
    poly.oneValue (vecAdd u v) v
  | [], [], _, _ => trivial
  | [], _ :: _, _, hl => nomatch hl
  | _ :: _, [], _, hl => nomatch hl
  | _ :: _, b :: _, h, hl =>
    ⟨BPair.oneValue_trans (BPair.add_congr h.1 (BPair.oneValue_refl b))
       (BPair.unit_add b),
     vecAddUnitLeft h.2 (Nat.succ.inj hl)⟩

private theorem rowsLenConsU (w : Nat) : ∀ M : Mat, rowsLen w M →
    rowsLen (w + 1) (M.map (fun v => BPair.unit :: v))
  | [], _ => trivial
  | r :: t, h =>
    ⟨by show r.length + 1 = w + 1; rw [h.1],
     rowsLenConsU w t h.2⟩

private theorem rowsLenConsU2 (w : Nat) : ∀ M : Mat, rowsLen w M →
    rowsLen (w + 2) (M.map (fun v => BPair.unit :: BPair.unit :: v))
  | [], _ => trivial
  | r :: t, h =>
    ⟨by show r.length + 1 + 1 = w + 2; rw [h.1],
     rowsLenConsU2 w t h.2⟩

private theorem bQuad_congr (bs : List SBlock) (k : Nat)
    {c c' : List BPair} (h : poly.oneValue c c') :
    (bQuad bs k c).oneValue (bQuad bs k c') :=
  BPair.oneValue_trans
    (dotP_oneValue_left c c' _ h)
    (dotP_oneValue_right c' _ _
      (poly.oneValue_map _ _ _ (fun x _ => (fun r => dotP_oneValue_right r c c' h) x)))

/-- The form fold passes a class read of its vector. -/
theorem quad_congr (S : Mat) (u u' : List BPair)
    (h : poly.oneValue u u') :
    (dotN u (matVec S u)).oneValue (dotN u' (matVec S u')) := by
  refine BPair.oneValue_trans (dotN_read u (matVec S u)) ?_
  refine BPair.oneValue_trans (dotP_oneValue_left u u' _ h) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_right u' _ _ (matVec_congr S u u' h)) ?_
  exact BPair.oneValue_symm (dotN_read u' (matVec S u'))

private theorem comboConsU (w : Nat) : ∀ (cs : List BPair) (M : Mat),
    rowsLen w M →
    poly.oneValue (combo (w + 1) cs (M.map (fun v => BPair.unit :: v)))
      (BPair.unit :: combo w cs M)
  | [], _, _ => poly.oneValue_refl _
  | _ :: _, [], _ => poly.oneValue_refl _
  | c :: cs, r :: M, hM => by
    have hK : rowsLen (w + 1) (M.map (fun v => BPair.unit :: v)) :=
      rowsLenConsU w M hM.2
    have hl : (combo (w + 1) cs (M.map (fun v => BPair.unit :: v))).length
        = (BPair.unit :: combo w cs M).length := by
      rw [length_combo (w + 1) cs _ hK]
      show w + 1 = (combo w cs M).length + 1
      rw [length_combo w cs M hM.2]
    refine poly.oneValue_trans
      (elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl (vecScale c (BPair.unit :: r)))
        (comboConsU w cs M hM.2) rfl hl) ?_
    show poly.oneValue ((c * BPair.unit + BPair.unit)
        :: vecAdd (vecScale c r) (combo w cs M))
      (BPair.unit :: vecAdd (vecScale c r) (combo w cs M))
    exact ⟨BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_unit c)
          (BPair.oneValue_refl BPair.unit))
        (BPair.unit_add BPair.unit),
      poly.oneValue_refl _⟩

private theorem comboConsU2 (w : Nat) (cs : List BPair) (M : Mat)
    (hM : rowsLen w M) :
    poly.oneValue
      (combo (w + 2) cs (M.map (fun v => BPair.unit :: BPair.unit :: v)))
      (BPair.unit :: BPair.unit :: combo w cs M) := by
  have hmm : M.map (fun v => BPair.unit :: BPair.unit :: v)
      = (M.map (fun v => BPair.unit :: v)).map
        (fun v => BPair.unit :: v) := by
    rw [ground.map_map]
  rw [hmm]
  refine poly.oneValue_trans
    (comboConsU (w + 1) cs (M.map (fun v => BPair.unit :: v))
      (rowsLenConsU w M hM)) ?_
  exact ⟨BPair.oneValue_refl BPair.unit, comboConsU w cs M hM⟩

private theorem shape1 (w : Nat) (p x : BPair) (cs : List BPair)
    (M : Mat) (hM : rowsLen w M) :
    poly.oneValue
      (combo (w + 1) (x :: cs)
        ((p :: List.replicate w BPair.unit)
          :: M.map (fun v => BPair.unit :: v)))
      ((x * p) :: combo w cs M) := by
  have hK : rowsLen (w + 1) (M.map (fun v => BPair.unit :: v)) :=
    rowsLenConsU w M hM
  have hl : (combo (w + 1) cs (M.map (fun v => BPair.unit :: v))).length
      = (BPair.unit :: combo w cs M).length := by
    rw [length_combo (w + 1) cs _ hK]
    show w + 1 = (combo w cs M).length + 1
    rw [length_combo w cs M hM]
  have hpad : (vecScale x (List.replicate w BPair.unit)).length
      = (combo w cs M).length := by
    rw [length_vecScale, ground.length_replicate,
      length_combo w cs M hM]
  refine poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      (poly.oneValue_refl (vecScale x (p :: List.replicate w BPair.unit)))
      (comboConsU w cs M hM) rfl hl) ?_
  show poly.oneValue ((x * p + BPair.unit)
      :: vecAdd (vecScale x (List.replicate w BPair.unit))
        (combo w cs M))
    ((x * p) :: combo w cs M)
  exact ⟨BPair.add_unit (x * p),
    vecAddUnitLeft (elim.unitTail_vecScale x _ (poly.unitTail_replicate w)) hpad⟩

private theorem shape2 (w : Nat) (p q x : BPair) (cs : List BPair)
    (M : Mat) (hM : rowsLen w M) :
    poly.oneValue
      (combo (w + 2) (x :: cs)
        ((p :: q :: List.replicate w BPair.unit)
          :: M.map (fun v => BPair.unit :: BPair.unit :: v)))
      ((x * p) :: (x * q) :: combo w cs M) := by
  have hK : rowsLen (w + 2)
      (M.map (fun v => BPair.unit :: BPair.unit :: v)) :=
    rowsLenConsU2 w M hM
  have hl : (combo (w + 2) cs
        (M.map (fun v => BPair.unit :: BPair.unit :: v))).length
      = (BPair.unit :: BPair.unit :: combo w cs M).length := by
    rw [length_combo (w + 2) cs _ hK]
    show w + 2 = (combo w cs M).length + 1 + 1
    rw [length_combo w cs M hM]
  have hpad : (vecScale x (List.replicate w BPair.unit)).length
      = (combo w cs M).length := by
    rw [length_vecScale, ground.length_replicate,
      length_combo w cs M hM]
  refine poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      (poly.oneValue_refl
        (vecScale x (p :: q :: List.replicate w BPair.unit)))
      (comboConsU2 w cs M hM) rfl hl) ?_
  show poly.oneValue ((x * p + BPair.unit) :: (x * q + BPair.unit)
      :: vecAdd (vecScale x (List.replicate w BPair.unit))
        (combo w cs M))
    ((x * p) :: (x * q) :: combo w cs M)
  exact ⟨BPair.add_unit (x * p), BPair.add_unit (x * q),
    vecAddUnitLeft (elim.unitTail_vecScale x _ (poly.unitTail_replicate w)) hpad⟩

private theorem shape2cols (w : Nat) (x y : BPair) (cs : List BPair)
    (M : Mat) (hM : rowsLen w M) :
    poly.oneValue
      (combo (w + 2) (x :: y :: cs)
        ((BPair.ofPos Pos.one :: BPair.unit
            :: List.replicate w BPair.unit)
          :: (BPair.unit :: BPair.ofPos Pos.one
            :: List.replicate w BPair.unit)
          :: M.map (fun v => BPair.unit :: BPair.unit :: v)))
      (x :: y :: combo w cs M) := by
  have hK : rowsLen (w + 2)
      (M.map (fun v => BPair.unit :: BPair.unit :: v)) :=
    rowsLenConsU2 w M hM
  have hrow : rowsLen (w + 2)
      ((BPair.unit :: BPair.ofPos Pos.one
          :: List.replicate w BPair.unit)
        :: M.map (fun v => BPair.unit :: BPair.unit :: v)) :=
    ⟨by show (List.replicate w BPair.unit).length + 1 + 1 = w + 2
        rw [ground.length_replicate]
      , hK⟩
  have hl : (combo (w + 2) (y :: cs)
        ((BPair.unit :: BPair.ofPos Pos.one
            :: List.replicate w BPair.unit)
          :: M.map (fun v => BPair.unit :: BPair.unit :: v))).length
      = ((y * BPair.unit) :: (y * BPair.ofPos Pos.one)
          :: combo w cs M).length := by
    rw [length_combo (w + 2) (y :: cs) _ hrow]
    show w + 2 = (combo w cs M).length + 1 + 1
    rw [length_combo w cs M hM]
  have hpad : (vecScale x (List.replicate w BPair.unit)).length
      = (combo w cs M).length := by
    rw [length_vecScale, ground.length_replicate,
      length_combo w cs M hM]
  refine poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      (poly.oneValue_refl
        (vecScale x (BPair.ofPos Pos.one :: BPair.unit
          :: List.replicate w BPair.unit)))
      (shape2 w BPair.unit (BPair.ofPos Pos.one) y cs M hM) rfl hl) ?_
  show poly.oneValue
      ((x * BPair.ofPos Pos.one + y * BPair.unit)
        :: (x * BPair.unit + y * BPair.ofPos Pos.one)
        :: vecAdd (vecScale x (List.replicate w BPair.unit))
          (combo w cs M))
      (x :: y :: combo w cs M)
  exact ⟨BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_ofNat_one x) (BPair.mul_unit y))
      (BPair.add_unit x),
    BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_unit x) (BPair.mul_ofNat_one y))
      (BPair.unit_add y),
    vecAddUnitLeft (elim.unitTail_vecScale x _ (poly.unitTail_replicate w)) hpad⟩

/-! The blocks' emissions: the order-1 column at its own side, the
2×2 block's two columns at the shared side, and the mixed block's
witness pair — the memberwise swap's own pair the upper-side one. -/

/-- The mixed block's lower-side pair at the leading entry's
trichotomy: the first place at a lower-side entry, the exchanged
pair `(b, ǎ)` at a strictly upper one, and the doubled pair
`((d + 1)ˇ, b + b)` at an equal-membered one. -/
private def mixWit (a b d : BPair) : BPair × BPair :=
  match a.side with
  | Trich.lt _ _ => (BPair.ofPos Pos.one, BPair.unit)
  | Trich.eq _ => ((d + BPair.ofPos Pos.one).swap, b + b)
  | Trich.gt _ _ => (b, a.swap)

private def oneLow (a : BPair) : List BPair :=
  match a.side with
  | Trich.lt _ _ => [BPair.ofPos Pos.one]
  | Trich.eq _ => []
  | Trich.gt _ _ => []

private def oneCompl (a : BPair) : List BPair :=
  match a.side with
  | Trich.lt _ _ => []
  | Trich.eq _ => [BPair.ofPos Pos.one]
  | Trich.gt _ _ => [BPair.ofPos Pos.one]

private def twoLow (a b d : BPair) : List (BPair × BPair) :=
  match ((SBlock.two a b d).det).side with
  | Trich.lt _ _ => [mixWit a b d]
  | Trich.eq _ => []
  | Trich.gt _ _ =>
    match a.side with
    | Trich.lt _ _ =>
      [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
    | Trich.eq _ => []
    | Trich.gt _ _ => []

private def twoCompl (a b d : BPair) : List (BPair × BPair) :=
  match ((SBlock.two a b d).det).side with
  | Trich.lt _ _ => [mixWit a.swap b.swap d.swap]
  | Trich.eq _ =>
    [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
  | Trich.gt _ _ =>
    match a.side with
    | Trich.lt _ _ => []
    | Trich.eq _ =>
      [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
    | Trich.gt _ _ =>
      [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]

/-- The kernel block's own columns, the trailing identity. -/
private def kerRows : Nat → Mat
  | 0 => []
  | k + 1 =>
    (BPair.ofPos Pos.one :: List.replicate k BPair.unit)
      :: (kerRows k).map (fun v => BPair.unit :: v)

/-- The lower list's raw vectors, supported at the blocks' own
places and padded to the split's order. -/
private def rawLower : List SBlock → Nat → Mat
  | [], _ => []
  | SBlock.one a :: bs, k =>
    (oneLow a).map (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
      ++ (rawLower bs k).map (fun v => BPair.unit :: v)
  | SBlock.two a b d :: bs, k =>
    (twoLow a b d).map (fun p =>
        p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
      ++ (rawLower bs k).map (fun v => BPair.unit :: BPair.unit :: v)

/-- The complement list's raw vectors, the kernel block's columns
trailing. -/
private def rawCompl : List SBlock → Nat → Mat
  | [], k => kerRows k
  | SBlock.one a :: bs, k =>
    (oneCompl a).map (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
      ++ (rawCompl bs k).map (fun v => BPair.unit :: v)
  | SBlock.two a b d :: bs, k =>
    (twoCompl a b d).map (fun p =>
        p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
      ++ (rawCompl bs k).map (fun v => BPair.unit :: BPair.unit :: v)

/-! The emissions' reads at the sides, the reversal counts beside
them. -/

private theorem oneLow_of_lt {a : BPair} (h : a < BPair.unit) :
    oneLow a = [BPair.ofPos Pos.one] := by
  match hs : a.side with
  | Trich.lt _ _ =>
    show (match a.side with
      | Trich.lt _ _ => [BPair.ofPos Pos.one]
      | Trich.eq _ => ([] : List BPair)
      | Trich.gt _ _ => ([] : List BPair)) = _
    rw [hs]
  | Trich.eq he =>
    exact absurd (show a.fst + Pos.one = Pos.one + a.snd by
      rw [he, ground.add_comm]) (ground.offOfLtUnit h)
  | Trich.gt g hg =>
    exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt h))

private theorem oneLow_of_le {a : BPair} (h : BPair.unit ≤ a) :
    oneLow a = [] := by
  match hs : a.side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt h)
  | Trich.eq _ =>
    show (match a.side with
      | Trich.lt _ _ => [BPair.ofPos Pos.one]
      | Trich.eq _ => ([] : List BPair)
      | Trich.gt _ _ => ([] : List BPair)) = _
    rw [hs]
  | Trich.gt _ _ =>
    show (match a.side with
      | Trich.lt _ _ => [BPair.ofPos Pos.one]
      | Trich.eq _ => ([] : List BPair)
      | Trich.gt _ _ => ([] : List BPair)) = _
    rw [hs]

private theorem oneCompl_of_lt {a : BPair} (h : a < BPair.unit) :
    oneCompl a = [] := by
  match hs : a.side with
  | Trich.lt _ _ =>
    show (match a.side with
      | Trich.lt _ _ => ([] : List BPair)
      | Trich.eq _ => [BPair.ofPos Pos.one]
      | Trich.gt _ _ => [BPair.ofPos Pos.one]) = _
    rw [hs]
  | Trich.eq he =>
    exact absurd (show a.fst + Pos.one = Pos.one + a.snd by
      rw [he, ground.add_comm]) (ground.offOfLtUnit h)
  | Trich.gt g hg =>
    exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt h))

private theorem oneCompl_of_le {a : BPair} (h : BPair.unit ≤ a) :
    oneCompl a = [BPair.ofPos Pos.one] := by
  match hs : a.side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt h)
  | Trich.eq _ =>
    show (match a.side with
      | Trich.lt _ _ => ([] : List BPair)
      | Trich.eq _ => [BPair.ofPos Pos.one]
      | Trich.gt _ _ => [BPair.ofPos Pos.one]) = _
    rw [hs]
  | Trich.gt _ _ =>
    show (match a.side with
      | Trich.lt _ _ => ([] : List BPair)
      | Trich.eq _ => [BPair.ofPos Pos.one]
      | Trich.gt _ _ => [BPair.ofPos Pos.one]) = _
    rw [hs]

/-- An order-one block below the unit reads one reversal. -/
theorem rev_one_lt {a : BPair} (h : a < BPair.unit) :
    (SBlock.one a).rev = 1 := by
  match hs : a.side with
  | Trich.lt _ _ =>
    show (match a.side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ => 0) = 1
    rw [hs]
  | Trich.eq he =>
    exact absurd (show a.fst + Pos.one = Pos.one + a.snd by
      rw [he, ground.add_comm]) (ground.offOfLtUnit h)
  | Trich.gt g hg =>
    exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt h))

/-- An order-one block at or above the unit reads the table's vacant side. -/
theorem rev_one_le {a : BPair} (h : BPair.unit ≤ a) :
    (SBlock.one a).rev = 0 := by
  match hs : a.side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt h)
  | Trich.eq _ =>
    show (match a.side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ => 0) = 0
    rw [hs]
  | Trich.gt _ _ =>
    show (match a.side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ => 0) = 0
    rw [hs]

private theorem twoLow_of_detLt {a b d : BPair}
    (hD : (SBlock.two a b d).det < BPair.unit) :
    twoLow a b d = [mixWit a b d] := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt _ _ =>
    show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a b d]
      | Trich.eq _ => ([] : List (BPair × BPair))
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.eq _ => ([] : List (BPair × BPair))
        | Trich.gt _ _ => ([] : List (BPair × BPair))) = _
    rw [hs]
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) (ground.offOfLtUnit hD)
  | Trich.gt g hg =>
    exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt hD))

private theorem twoLow_of_cols {a b d : BPair}
    (hD : BPair.unit < (SBlock.two a b d).det) (ha : a < BPair.unit) :
    twoLow a b d
      = [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)] := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt hD))
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) (ground.offOfUnitLt hD)
  | Trich.gt _ _ =>
    match hsa : a.side with
    | Trich.lt _ _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a b d]
      | Trich.eq _ => ([] : List (BPair × BPair))
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.eq _ => ([] : List (BPair × BPair))
        | Trich.gt _ _ => ([] : List (BPair × BPair))) = _
      rw [hs, hsa]
    | Trich.eq hea =>
      exact absurd (show a.fst + Pos.one = Pos.one + a.snd by
        rw [hea, ground.add_comm]) (ground.offOfLtUnit ha)
    | Trich.gt g hg =>
      exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt ha))

private theorem twoLow_of_nil {a b d : BPair}
    (hD : BPair.unit ≤ (SBlock.two a b d).det) (ha : BPair.unit ≤ a) :
    twoLow a b d = [] := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt hD)
  | Trich.eq _ =>
    show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a b d]
      | Trich.eq _ => ([] : List (BPair × BPair))
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.eq _ => ([] : List (BPair × BPair))
        | Trich.gt _ _ => ([] : List (BPair × BPair))) = _
    rw [hs]
  | Trich.gt _ _ =>
    match hsa : a.side with
    | Trich.lt g hg =>
      exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt ha)
    | Trich.eq _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a b d]
      | Trich.eq _ => ([] : List (BPair × BPair))
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.eq _ => ([] : List (BPair × BPair))
        | Trich.gt _ _ => ([] : List (BPair × BPair))) = _
      rw [hs, hsa]
    | Trich.gt _ _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a b d]
      | Trich.eq _ => ([] : List (BPair × BPair))
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.eq _ => ([] : List (BPair × BPair))
        | Trich.gt _ _ => ([] : List (BPair × BPair))) = _
      rw [hs, hsa]

private theorem twoCompl_of_detLt {a b d : BPair}
    (hD : (SBlock.two a b d).det < BPair.unit) :
    twoCompl a b d = [mixWit a.swap b.swap d.swap] := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt _ _ =>
    show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a.swap b.swap d.swap]
      | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => ([] : List (BPair × BPair))
        | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.gt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]) = _
    rw [hs]
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) (ground.offOfLtUnit hD)
  | Trich.gt g hg =>
    exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt hD))

private theorem twoCompl_of_nil {a b d : BPair}
    (hD : BPair.unit < (SBlock.two a b d).det) (ha : a < BPair.unit) :
    twoCompl a b d = [] := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt hD))
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) (ground.offOfUnitLt hD)
  | Trich.gt _ _ =>
    match hsa : a.side with
    | Trich.lt _ _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a.swap b.swap d.swap]
      | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => ([] : List (BPair × BPair))
        | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.gt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]) = _
      rw [hs, hsa]
    | Trich.eq hea =>
      exact absurd (show a.fst + Pos.one = Pos.one + a.snd by
        rw [hea, ground.add_comm]) (ground.offOfLtUnit ha)
    | Trich.gt g hg =>
      exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt ha))

private theorem twoCompl_of_cols {a b d : BPair}
    (hD : BPair.unit ≤ (SBlock.two a b d).det) (ha : BPair.unit ≤ a) :
    twoCompl a b d
      = [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)] := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt hD)
  | Trich.eq _ =>
    show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a.swap b.swap d.swap]
      | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => ([] : List (BPair × BPair))
        | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.gt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]) = _
    rw [hs]
  | Trich.gt _ _ =>
    match hsa : a.side with
    | Trich.lt g hg =>
      exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt ha)
    | Trich.eq _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a.swap b.swap d.swap]
      | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => ([] : List (BPair × BPair))
        | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.gt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]) = _
      rw [hs, hsa]
    | Trich.gt _ _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => [mixWit a.swap b.swap d.swap]
      | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => ([] : List (BPair × BPair))
        | Trich.eq _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]
        | Trich.gt _ _ => [(BPair.ofPos Pos.one, BPair.unit), (BPair.unit, BPair.ofPos Pos.one)]) = _
      rw [hs, hsa]

/-- A mixed block, the determinant on its lower side, reads one unit per side. -/
theorem rev_two_detLt {a b d : BPair}
    (hD : (SBlock.two a b d).det < BPair.unit) :
    (SBlock.two a b d).rev = 1 := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt _ _ =>
    show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => 2
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = _
    rw [hs]
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) (ground.offOfLtUnit hD)
  | Trich.gt g hg =>
    exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt hD))

/-- An upper-determinant block at a lower-side entry reads both units below. -/
theorem rev_two_cols {a b d : BPair}
    (hD : BPair.unit < (SBlock.two a b d).det) (ha : a < BPair.unit) :
    (SBlock.two a b d).rev = 2 := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt hD))
  | Trich.eq he =>
    exact absurd (show ((SBlock.two a b d).det).fst + Pos.one
        = Pos.one + ((SBlock.two a b d).det).snd by
      rw [he, ground.add_comm]) (ground.offOfUnitLt hD)
  | Trich.gt _ _ =>
    match hsa : a.side with
    | Trich.lt _ _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => 2
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = _
      rw [hs, hsa]
    | Trich.eq hea =>
      exact absurd (show a.fst + Pos.one = Pos.one + a.snd by
        rw [hea, ground.add_comm]) (ground.offOfLtUnit ha)
    | Trich.gt g hg =>
      exact absurd (unitLtOfSide ⟨g, hg⟩) (ground.leB_not_lt (ground.leB_of_lt ha))

/-- An upper-determinant block at an entry at or above the unit reads the vacant side. -/
theorem rev_two_nil {a b d : BPair}
    (hD : BPair.unit ≤ (SBlock.two a b d).det) (ha : BPair.unit ≤ a) :
    (SBlock.two a b d).rev = 0 := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt hD)
  | Trich.eq _ =>
    show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => 2
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = _
    rw [hs]
  | Trich.gt _ _ =>
    match hsa : a.side with
    | Trich.lt g hg =>
      exact absurd (ground.ltUnitOfSide ⟨g, hg⟩) (ground.leB_not_lt ha)
    | Trich.eq _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => 2
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = _
      rw [hs, hsa]
    | Trich.gt _ _ =>
      show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => 2
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = _
      rw [hs, hsa]

/-! The raw lists' reads at the head block: the emission's own
shape with the padded tail. -/

private theorem rawLower_one_lt {a : BPair} (h : a < BPair.unit)
    (bs : List SBlock) (k : Nat) :
    rawLower (SBlock.one a :: bs) k
      = (BPair.ofPos Pos.one :: List.replicate (widthOf bs k) BPair.unit)
        :: (rawLower bs k).map (fun v => BPair.unit :: v) := by
  have e : rawLower (SBlock.one a :: bs) k
      = (oneLow a).map
          (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawLower bs k).map (fun v => BPair.unit :: v) := rfl
  rw [e, oneLow_of_lt h]
  rfl

private theorem rawLower_one_le {a : BPair} (h : BPair.unit ≤ a)
    (bs : List SBlock) (k : Nat) :
    rawLower (SBlock.one a :: bs) k
      = (rawLower bs k).map (fun v => BPair.unit :: v) := by
  have e : rawLower (SBlock.one a :: bs) k
      = (oneLow a).map
          (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawLower bs k).map (fun v => BPair.unit :: v) := rfl
  rw [e, oneLow_of_le h]
  rfl

private theorem rawCompl_one_lt {a : BPair} (h : a < BPair.unit)
    (bs : List SBlock) (k : Nat) :
    rawCompl (SBlock.one a :: bs) k
      = (rawCompl bs k).map (fun v => BPair.unit :: v) := by
  have e : rawCompl (SBlock.one a :: bs) k
      = (oneCompl a).map
          (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawCompl bs k).map (fun v => BPair.unit :: v) := rfl
  rw [e, oneCompl_of_lt h]
  rfl

private theorem rawCompl_one_le {a : BPair} (h : BPair.unit ≤ a)
    (bs : List SBlock) (k : Nat) :
    rawCompl (SBlock.one a :: bs) k
      = (BPair.ofPos Pos.one :: List.replicate (widthOf bs k) BPair.unit)
        :: (rawCompl bs k).map (fun v => BPair.unit :: v) := by
  have e : rawCompl (SBlock.one a :: bs) k
      = (oneCompl a).map
          (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawCompl bs k).map (fun v => BPair.unit :: v) := rfl
  rw [e, oneCompl_of_le h]
  rfl

private theorem rawLower_two_mix {a b d : BPair}
    (hD : (SBlock.two a b d).det < BPair.unit) (bs : List SBlock)
    (k : Nat) :
    rawLower (SBlock.two a b d :: bs) k
      = ((mixWit a b d).1 :: (mixWit a b d).2
          :: List.replicate (widthOf bs k) BPair.unit)
        :: (rawLower bs k).map (fun v => BPair.unit :: BPair.unit :: v) := by
  have e : rawLower (SBlock.two a b d :: bs) k
      = (twoLow a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawLower bs k).map
          (fun v => BPair.unit :: BPair.unit :: v) := rfl
  rw [e, twoLow_of_detLt hD]
  rfl

private theorem rawLower_two_cols {a b d : BPair}
    (hD : BPair.unit < (SBlock.two a b d).det) (ha : a < BPair.unit)
    (bs : List SBlock) (k : Nat) :
    rawLower (SBlock.two a b d :: bs) k
      = (BPair.ofPos Pos.one :: BPair.unit
          :: List.replicate (widthOf bs k) BPair.unit)
        :: (BPair.unit :: BPair.ofPos Pos.one
          :: List.replicate (widthOf bs k) BPair.unit)
        :: (rawLower bs k).map (fun v => BPair.unit :: BPair.unit :: v) := by
  have e : rawLower (SBlock.two a b d :: bs) k
      = (twoLow a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawLower bs k).map
          (fun v => BPair.unit :: BPair.unit :: v) := rfl
  rw [e, twoLow_of_cols hD ha]
  rfl

private theorem rawLower_two_nil {a b d : BPair}
    (hD : BPair.unit ≤ (SBlock.two a b d).det) (ha : BPair.unit ≤ a)
    (bs : List SBlock) (k : Nat) :
    rawLower (SBlock.two a b d :: bs) k
      = (rawLower bs k).map (fun v => BPair.unit :: BPair.unit :: v) := by
  have e : rawLower (SBlock.two a b d :: bs) k
      = (twoLow a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawLower bs k).map
          (fun v => BPair.unit :: BPair.unit :: v) := rfl
  rw [e, twoLow_of_nil hD ha]
  rfl

private theorem rawCompl_two_mix {a b d : BPair}
    (hD : (SBlock.two a b d).det < BPair.unit) (bs : List SBlock)
    (k : Nat) :
    rawCompl (SBlock.two a b d :: bs) k
      = ((mixWit a.swap b.swap d.swap).1 :: (mixWit a.swap b.swap d.swap).2
          :: List.replicate (widthOf bs k) BPair.unit)
        :: (rawCompl bs k).map (fun v => BPair.unit :: BPair.unit :: v) := by
  have e : rawCompl (SBlock.two a b d :: bs) k
      = (twoCompl a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawCompl bs k).map
          (fun v => BPair.unit :: BPair.unit :: v) := rfl
  rw [e, twoCompl_of_detLt hD]
  rfl

private theorem rawCompl_two_nil {a b d : BPair}
    (hD : BPair.unit < (SBlock.two a b d).det) (ha : a < BPair.unit)
    (bs : List SBlock) (k : Nat) :
    rawCompl (SBlock.two a b d :: bs) k
      = (rawCompl bs k).map (fun v => BPair.unit :: BPair.unit :: v) := by
  have e : rawCompl (SBlock.two a b d :: bs) k
      = (twoCompl a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawCompl bs k).map
          (fun v => BPair.unit :: BPair.unit :: v) := rfl
  rw [e, twoCompl_of_nil hD ha]
  rfl

private theorem rawCompl_two_cols {a b d : BPair}
    (hD : BPair.unit ≤ (SBlock.two a b d).det) (ha : BPair.unit ≤ a)
    (bs : List SBlock) (k : Nat) :
    rawCompl (SBlock.two a b d :: bs) k
      = (BPair.ofPos Pos.one :: BPair.unit
          :: List.replicate (widthOf bs k) BPair.unit)
        :: (BPair.unit :: BPair.ofPos Pos.one
          :: List.replicate (widthOf bs k) BPair.unit)
        :: (rawCompl bs k).map (fun v => BPair.unit :: BPair.unit :: v) := by
  have e : rawCompl (SBlock.two a b d :: bs) k
      = (twoCompl a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawCompl bs k).map
          (fun v => BPair.unit :: BPair.unit :: v) := rfl
  rw [e, twoCompl_of_cols hD ha]
  rfl

/-! The raw lists' shapes and counts: every raw vector at the
split's order, the lower list's count the reversal fold, and the
two counts joining to the order. -/

private theorem kerRows_length : ∀ k : Nat, (kerRows k).length = k
  | 0 => rfl
  | k + 1 => by
    show ((kerRows k).map (fun v => BPair.unit :: v)).length + 1 = k + 1
    rw [ground.length_map, kerRows_length k]

private theorem kerRows_rows : ∀ k : Nat, rowsLen k (kerRows k)
  | 0 => trivial
  | k + 1 =>
    ⟨by show (List.replicate k BPair.unit).length + 1 = k + 1
        rw [ground.length_replicate],
     rowsLenConsU k (kerRows k) (kerRows_rows k)⟩

private theorem rawLower_rows : ∀ (bs : List SBlock) (k : Nat),
    rowsLen (widthOf bs k) (rawLower bs k)
  | [], _ => trivial
  | SBlock.one a :: bs, k => by
    have hw : widthOf (SBlock.one a :: bs) k = widthOf bs k + 1 :=
      widthOf_shift bs k 1
    rw [hw]
    show rowsLen (widthOf bs k + 1)
      ((oneLow a).map
          (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawLower bs k).map (fun v => BPair.unit :: v))
    exact rowsLen_append (widthOf bs k + 1)
      (rowsLen_map _ (widthOf bs k + 1) (oneLow a) (fun x _ => (fun _ => by
          show (List.replicate (widthOf bs k) BPair.unit).length + 1
            = widthOf bs k + 1
          rw [ground.length_replicate]) x))
      (rowsLenConsU (widthOf bs k) (rawLower bs k) (rawLower_rows bs k))
  | SBlock.two a b d :: bs, k => by
    have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
      widthOf_shift bs k 2
    rw [hw]
    show rowsLen (widthOf bs k + 2)
      ((twoLow a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawLower bs k).map (fun v => BPair.unit :: BPair.unit :: v))
    exact rowsLen_append (widthOf bs k + 2)
      (rowsLen_map _ (widthOf bs k + 2) (twoLow a b d) (fun x _ => (fun _ => by
          show (List.replicate (widthOf bs k) BPair.unit).length + 1 + 1
            = widthOf bs k + 2
          rw [ground.length_replicate]) x))
      (rowsLenConsU2 (widthOf bs k) (rawLower bs k) (rawLower_rows bs k))

private theorem rawCompl_rows : ∀ (bs : List SBlock) (k : Nat),
    rowsLen (widthOf bs k) (rawCompl bs k)
  | [], k => kerRows_rows k
  | SBlock.one a :: bs, k => by
    have hw : widthOf (SBlock.one a :: bs) k = widthOf bs k + 1 :=
      widthOf_shift bs k 1
    rw [hw]
    show rowsLen (widthOf bs k + 1)
      ((oneCompl a).map
          (fun p => p :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawCompl bs k).map (fun v => BPair.unit :: v))
    exact rowsLen_append (widthOf bs k + 1)
      (rowsLen_map _ (widthOf bs k + 1) (oneCompl a) (fun x _ => (fun _ => by
          show (List.replicate (widthOf bs k) BPair.unit).length + 1
            = widthOf bs k + 1
          rw [ground.length_replicate]) x))
      (rowsLenConsU (widthOf bs k) (rawCompl bs k) (rawCompl_rows bs k))
  | SBlock.two a b d :: bs, k => by
    have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
      widthOf_shift bs k 2
    rw [hw]
    show rowsLen (widthOf bs k + 2)
      ((twoCompl a b d).map (fun p =>
          p.1 :: p.2 :: List.replicate (widthOf bs k) BPair.unit)
        ++ (rawCompl bs k).map (fun v => BPair.unit :: BPair.unit :: v))
    exact rowsLen_append (widthOf bs k + 2)
      (rowsLen_map _ (widthOf bs k + 2) (twoCompl a b d) (fun x _ => (fun _ => by
          show (List.replicate (widthOf bs k) BPair.unit).length + 1 + 1
            = widthOf bs k + 2
          rw [ground.length_replicate]) x))
      (rowsLenConsU2 (widthOf bs k) (rawCompl bs k) (rawCompl_rows bs k))

private theorem rawLower_length : ∀ (bs : List SBlock) (k : Nat),
    (bs.all (fun z => !(decide (z.det.oneValue BPair.unit)))) = true →
    (rawLower bs k).length = bs.foldl (fun m z => m + z.rev) 0
  | [], _, _ => rfl
  | SBlock.one a :: bs, k, hall => by
    have hIH := rawLower_length bs k ((ground.andSplitB hall).2)
    rw [revSplit]
    if hlt : a < BPair.unit then
      rw [rawLower_one_lt hlt bs k, rev_one_lt hlt]
      show ((rawLower bs k).map (fun v => BPair.unit :: v)).length + 1
        = 1 + bs.foldl (fun m z => m + z.rev) 0
      rw [ground.length_map, hIH, Nat.add_comm]
    else
      have hge : BPair.unit ≤ a := ground.leB_of_not_lt hlt
      rw [rawLower_one_le hge bs k, rev_one_le hge, Nat.zero_add,
        ground.length_map, hIH]
  | SBlock.two a b d :: bs, k, hall => by
    have hns : ¬ ((SBlock.two a b d).det).oneValue BPair.unit :=
      ground.notOfBang ((ground.andSplitB hall).1)
    have hIH := rawLower_length bs k ((ground.andSplitB hall).2)
    rw [revSplit]
    if hD : (SBlock.two a b d).det < BPair.unit then
      rw [rawLower_two_mix hD bs k, rev_two_detLt hD]
      show ((rawLower bs k).map
          (fun v => BPair.unit :: BPair.unit :: v)).length + 1
        = 1 + bs.foldl (fun m z => m + z.rev) 0
      rw [ground.length_map, hIH, Nat.add_comm]
    else
      have hDge : BPair.unit ≤ (SBlock.two a b d).det :=
        ground.leB_of_not_lt hD
      if ha : a < BPair.unit then
        have hDgt : BPair.unit < (SBlock.two a b d).det := ground.ltOfLeOff hDge hns
        rw [rawLower_two_cols hDgt ha bs k, rev_two_cols hDgt ha]
        show ((rawLower bs k).map
            (fun v => BPair.unit :: BPair.unit :: v)).length + 1 + 1
          = 2 + bs.foldl (fun m z => m + z.rev) 0
        rw [ground.length_map, hIH, Nat.add_assoc, Nat.add_comm]
      else
        have hage : BPair.unit ≤ a := ground.leB_of_not_lt ha
        rw [rawLower_two_nil hDge hage bs k, rev_two_nil hDge hage,
          Nat.zero_add, ground.length_map, hIH]

private theorem raw_length_sum : ∀ (bs : List SBlock) (k : Nat),
    (bs.all (fun z => !(decide (z.det.oneValue BPair.unit)))) = true →
    (rawLower bs k).length + (rawCompl bs k).length = widthOf bs k
  | [], k, _ => by
    show 0 + (kerRows k).length = k
    rw [Nat.zero_add, kerRows_length k]
  | SBlock.one a :: bs, k, hall => by
    have hIH := raw_length_sum bs k ((ground.andSplitB hall).2)
    have hw : widthOf (SBlock.one a :: bs) k = widthOf bs k + 1 :=
      widthOf_shift bs k 1
    rw [hw]
    if hlt : a < BPair.unit then
      rw [rawLower_one_lt hlt bs k, rawCompl_one_lt hlt bs k]
      show ((rawLower bs k).map (fun v => BPair.unit :: v)).length + 1
          + ((rawCompl bs k).map (fun v => BPair.unit :: v)).length
        = widthOf bs k + 1
      rw [ground.length_map, ground.length_map,
        Nat.add_right_comm (rawLower bs k).length 1 (rawCompl bs k).length,
        hIH]
    else
      have hge : BPair.unit ≤ a := ground.leB_of_not_lt hlt
      rw [rawLower_one_le hge bs k, rawCompl_one_le hge bs k]
      show ((rawLower bs k).map (fun v => BPair.unit :: v)).length
          + (((rawCompl bs k).map (fun v => BPair.unit :: v)).length + 1)
        = widthOf bs k + 1
      rw [ground.length_map, ground.length_map, ← Nat.add_assoc, hIH]
  | SBlock.two a b d :: bs, k, hall => by
    have hns : ¬ ((SBlock.two a b d).det).oneValue BPair.unit :=
      ground.notOfBang ((ground.andSplitB hall).1)
    have hIH := raw_length_sum bs k ((ground.andSplitB hall).2)
    have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
      widthOf_shift bs k 2
    rw [hw]
    if hD : (SBlock.two a b d).det < BPair.unit then
      rw [rawLower_two_mix hD bs k, rawCompl_two_mix hD bs k]
      show ((rawLower bs k).map
            (fun v => BPair.unit :: BPair.unit :: v)).length + 1
          + (((rawCompl bs k).map
            (fun v => BPair.unit :: BPair.unit :: v)).length + 1)
        = widthOf bs k + 2
      rw [ground.length_map, ground.length_map, ← Nat.add_assoc,
        Nat.add_right_comm (rawLower bs k).length 1 (rawCompl bs k).length,
        hIH]
    else
      have hDge : BPair.unit ≤ (SBlock.two a b d).det :=
        ground.leB_of_not_lt hD
      if ha : a < BPair.unit then
        have hDgt : BPair.unit < (SBlock.two a b d).det := ground.ltOfLeOff hDge hns
        rw [rawLower_two_cols hDgt ha bs k, rawCompl_two_nil hDgt ha bs k]
        show ((rawLower bs k).map
              (fun v => BPair.unit :: BPair.unit :: v)).length + 1 + 1
            + ((rawCompl bs k).map
              (fun v => BPair.unit :: BPair.unit :: v)).length
          = widthOf bs k + 2
        rw [ground.length_map, ground.length_map,
          Nat.add_right_comm ((rawLower bs k).length + 1) 1
            (rawCompl bs k).length,
          Nat.add_right_comm (rawLower bs k).length 1
            (rawCompl bs k).length,
          hIH]
      else
        have hage : BPair.unit ≤ a := ground.leB_of_not_lt ha
        rw [rawLower_two_nil hDge hage bs k, rawCompl_two_cols hDge hage bs k]
        show ((rawLower bs k).map
              (fun v => BPair.unit :: BPair.unit :: v)).length
            + (((rawCompl bs k).map
              (fun v => BPair.unit :: BPair.unit :: v)).length + 1 + 1)
          = widthOf bs k + 2
        rw [ground.length_map, ground.length_map, ← Nat.add_assoc,
          ← Nat.add_assoc, hIH]

/-! The blocks' quadratic reads at a coefficient pair: the order-1
entry's square multiple and the 2×2 block's own form, with the
memberwise swap exchanging the sides and the coefficient's square
factoring out. -/

private def blkQ1 (a x : BPair) : BPair := x * (a * x)

private def blkQ2 (a b d x y : BPair) : BPair :=
  x * (a * x + b * y) + y * (b * x + d * y)

private theorem blkQ1_null {a x : BPair} (hx : x.oneValue BPair.unit) :
    (blkQ1 a x).oneValue BPair.unit := elim.oneValue_unit_mul hx

private theorem blkQ1_le {a : BPair} (ha : a ≤ BPair.unit) (x : BPair) :
    blkQ1 a x ≤ BPair.unit := by
  show x * (a * x) ≤ BPair.unit
  rw [BPair.mul_left_comm x a x, BPair.mul_comm a (x * x)]
  exact mulLeUnit (unitLeSq x) ha

private theorem blkQ1_ge {a : BPair} (ha : BPair.unit ≤ a) (x : BPair) :
    BPair.unit ≤ blkQ1 a x := by
  show BPair.unit ≤ x * (a * x)
  rw [BPair.mul_left_comm x a x]
  exact unitLeMul ha (unitLeSq x)

private theorem blkQ1_lt {a x : BPair} (ha : a < BPair.unit)
    (hx : ¬ x.oneValue BPair.unit) : blkQ1 a x < BPair.unit := by
  show x * (a * x) < BPair.unit
  rw [BPair.mul_left_comm x a x, BPair.mul_comm a (x * x)]
  exact mulNegPos (ground.sq_pos hx) ha

private theorem blkQ2_null {a b d x y : BPair}
    (hx : x.oneValue BPair.unit) (hy : y.oneValue BPair.unit) :
    (blkQ2 a b d x y).oneValue BPair.unit :=
  BPair.oneValue_trans
    (BPair.add_congr (elim.oneValue_unit_mul hx)
      (elim.oneValue_unit_mul hy))
    (BPair.unit_add BPair.unit)

private theorem blkQ2_swap (a b d x y : BPair) :
    blkQ2 a.swap b.swap d.swap x y = (blkQ2 a b d x y).swap := by
  show x * (a.swap * x + b.swap * y) + y * (b.swap * x + d.swap * y)
    = (x * (a * x + b * y) + y * (b * x + d * y)).swap
  rw [BPair.swap_mul a x, BPair.swap_mul b y, BPair.swap_mul b x, BPair.swap_mul d y,
    BPair.swap_add (a * x) (b * y), BPair.swap_add (b * x) (d * y),
    BPair.mul_swap x (a * x + b * y), BPair.mul_swap y (b * x + d * y),
    BPair.swap_add (x * (a * x + b * y)) (y * (b * x + d * y))]

private theorem blkQ2_scale (a b d x p q : BPair) :
    blkQ2 a b d (x * p) (x * q) = x * x * blkQ2 a b d p q := by
  show (x * p) * (a * (x * p) + b * (x * q))
      + (x * q) * (b * (x * p) + d * (x * q))
    = x * x * (p * (a * p + b * q) + q * (b * p + d * q))
  rw [BPair.mul_left_comm a x p, BPair.mul_left_comm b x q,
    BPair.mul_left_comm b x p, BPair.mul_left_comm d x q,
    ← BPair.left_distrib x (a * p) (b * q),
    ← BPair.left_distrib x (b * p) (d * q),
    BPair.mul_mul_mul_comm x p x (a * p + b * q),
    BPair.mul_mul_mul_comm x q x (b * p + d * q),
    ← BPair.left_distrib (x * x) (p * (a * p + b * q))
      (q * (b * p + d * q))]

private theorem detSwapEq (a b d : BPair) :
    (SBlock.two a.swap b.swap d.swap).det = (SBlock.two a b d).det := by
  show ((a.swap * d.swap) + ((b.swap * b.swap)).swap).norm
    = ((a * d) + ((b * b)).swap).norm
  rw [BPair.swap_mul_swap a d, BPair.swap_mul_swap b b]

private theorem blk2_psd {a b d : BPair} (ha : BPair.unit < a)
    (hD : BPair.unit < (SBlock.two a b d).det) (x y : BPair) :
    BPair.unit ≤ blkQ2 a b d x y := by
  refine scaleRefl ha ?_
  refine ground.leB_congr_right
    (BPair.oneValue_symm (sqComplete a b d x y)) ?_
  refine unitLeAdd (unitLeSq _) ?_
  refine unitLeMul (ground.leB_of_lt ?_) (unitLeSq y)
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit) (detRead a b d) hD

private theorem blk2_pdlt {a b d : BPair} (ha : BPair.unit < a)
    (hD : BPair.unit < (SBlock.two a b d).det) {x y : BPair}
    (hxy : ¬ (x.oneValue BPair.unit ∧ y.oneValue BPair.unit)) :
    BPair.unit < blkQ2 a b d x y := by
  have hdet : BPair.unit < a * d + (b * b).swap :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit) (detRead a b d) hD
  refine scaleReflLt ha ?_
  refine BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm (sqComplete a b d x y)) ?_
  if hy : y.oneValue BPair.unit then
    have hx : ¬ x.oneValue BPair.unit := fun hx => hxy ⟨hx, hy⟩
    have hby : (b * y).oneValue BPair.unit :=
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl b) hy) (BPair.mul_unit b)
    have hax : (a * x + b * y).oneValue (a * x) :=
      BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (a * x)) hby)
        (BPair.add_unit (a * x))
    have hterm2 : (((a * d + (b * b).swap)) * (y * y)).oneValue
        BPair.unit :=
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (a * d + (b * b).swap))
          (elim.oneValue_unit_mul hy))
        (BPair.mul_unit _)
    refine unitLtAdd
      (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
        (BPair.oneValue_symm (BPair.mul_congr hax hax))
        (ground.sq_pos (ground.mulOffUnit (ground.offOfUnitLt ha) hx))) ?_
    exact ground.leB_congr_right (BPair.oneValue_symm hterm2)
      (ground.leB_refl BPair.unit)
  else
    exact unitLeAddLt (unitLeSq _) (unitLtMul hdet (ground.sq_pos hy))

private theorem blk2_low_le {a b d : BPair} (ha : a < BPair.unit)
    (hD : BPair.unit < (SBlock.two a b d).det) (x y : BPair) :
    blkQ2 a b d x y ≤ BPair.unit := by
  have ha' : BPair.unit < a.swap := unitLtOfSide (ground.sideOfLtUnit ha)
  have hD' : BPair.unit < (SBlock.two a.swap b.swap d.swap).det := by
    rw [detSwapEq]; exact hD
  have h := blk2_psd ha' hD' x y
  rw [blkQ2_swap] at h
  exact ground.leUnitOfSwap h

private theorem blk2_low_lt {a b d : BPair} (ha : a < BPair.unit)
    (hD : BPair.unit < (SBlock.two a b d).det) {x y : BPair}
    (hxy : ¬ (x.oneValue BPair.unit ∧ y.oneValue BPair.unit)) :
    blkQ2 a b d x y < BPair.unit := by
  have ha' : BPair.unit < a.swap := unitLtOfSide (ground.sideOfLtUnit ha)
  have hD' : BPair.unit < (SBlock.two a.swap b.swap d.swap).det := by
    rw [detSwapEq]; exact hD
  have h := blk2_pdlt ha' hD' hxy
  rw [blkQ2_swap] at h
  exact ltUnitOfSwap h

private theorem twoLeadPos {a b d : BPair}
    (hD : BPair.unit < (SBlock.two a b d).det)
    (hage : BPair.unit ≤ a) : BPair.unit < a := by
  refine ground.ltOfLeOff hage ?_
  intro ha
  have hDs : ((SBlock.two a b d).det).oneValue ((b * b).swap) :=
    BPair.oneValue_trans (detRead a b d)
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_trans (BPair.mul_congr_left ha) (BPair.unit_mul d))
          (BPair.oneValue_refl ((b * b).swap)))
        (BPair.unit_add ((b * b).swap)))
  exact ground.leB_not_lt (unitLeSq b)
    (ground.ltUnitOfSide (show (b * b).fst < (b * b).snd from
      ground.sideOfUnitLt (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
        hDs hD)))

/-! The mixed block's witness pair: its own strictly lower read and
the coefficient extraction at its off-unit place. -/

private theorem mixWit_lt {a b d : BPair}
    (hns : ¬ ((SBlock.two a b d).det).oneValue BPair.unit)
    (hD : (SBlock.two a b d).det < BPair.unit) :
    blkQ2 a b d (mixWit a b d).1 (mixWit a b d).2 < BPair.unit := by
  match hs : a.side with
  | Trich.lt g hg =>
    have hw : mixWit a b d = (BPair.ofPos Pos.one, BPair.unit) := by
      show (match a.side with
        | Trich.lt _ _ => (BPair.ofPos Pos.one, BPair.unit)
        | Trich.eq _ => ((d + BPair.ofPos Pos.one).swap, b + b)
        | Trich.gt _ _ => (b, a.swap)) = _
      rw [hs]
    rw [hw]
    exact BPair.lt_congr (BPair.oneValue_symm (twoSlotE1 a b d))
      (BPair.oneValue_refl BPair.unit) (ground.ltUnitOfSide ⟨g, hg⟩)
  | Trich.eq he =>
    have hae : a.oneValue BPair.unit := by
      show a.fst + Pos.one = Pos.one + a.snd
      rw [he, ground.add_comm]
    have hw : mixWit a b d = ((d + BPair.ofPos Pos.one).swap, b + b) := by
      show (match a.side with
        | Trich.lt _ _ => (BPair.ofPos Pos.one, BPair.unit)
        | Trich.eq _ => ((d + BPair.ofPos Pos.one).swap, b + b)
        | Trich.gt _ _ => (b, a.swap)) = _
      rw [hs]
    rw [hw]
    exact BPair.lt_congr
      (BPair.oneValue_symm
        (twoSlotDb a b d (d + BPair.ofPos Pos.one).swap (b + b) hae rfl
          (swapAddCancel d (BPair.ofPos Pos.one))))
      (BPair.oneValue_refl BPair.unit)
      (swapLtUnit (doubleSqPos (twoOffB hae hns)))
  | Trich.gt g hg =>
    have hw : mixWit a b d = (b, a.swap) := by
      show (match a.side with
        | Trich.lt _ _ => (BPair.ofPos Pos.one, BPair.unit)
        | Trich.eq _ => ((d + BPair.ofPos Pos.one).swap, b + b)
        | Trich.gt _ _ => (b, a.swap)) = _
      rw [hs]
    rw [hw]
    exact BPair.lt_congr (BPair.oneValue_symm (twoSlotEx a b d))
      (BPair.oneValue_refl BPair.unit)
      (mulNegPos (unitLtOfSide ⟨g, hg⟩)
        (BPair.lt_congr (detRead a b d) (BPair.oneValue_refl BPair.unit) hD))

private theorem mixWit_gt {a b d : BPair}
    (hns : ¬ ((SBlock.two a b d).det).oneValue BPair.unit)
    (hD : (SBlock.two a b d).det < BPair.unit) :
    BPair.unit < blkQ2 a b d (mixWit a.swap b.swap d.swap).1
      (mixWit a.swap b.swap d.swap).2 := by
  have hns' : ¬ ((SBlock.two a.swap b.swap d.swap).det).oneValue
      BPair.unit := by
    rw [detSwapEq]; exact hns
  have hD' : (SBlock.two a.swap b.swap d.swap).det < BPair.unit := by
    rw [detSwapEq]; exact hD
  have h := mixWit_lt hns' hD'
  rw [blkQ2_swap] at h
  exact unitLtOfSwapLt h

private theorem mixWit_extract {a b d x : BPair}
    (hns : ¬ ((SBlock.two a b d).det).oneValue BPair.unit)
    (h1 : (x * (mixWit a b d).1).oneValue BPair.unit)
    (h2 : (x * (mixWit a b d).2).oneValue BPair.unit) :
    x.oneValue BPair.unit := by
  match hs : a.side with
  | Trich.lt _ _ =>
    have hw : mixWit a b d = (BPair.ofPos Pos.one, BPair.unit) := by
      show (match a.side with
        | Trich.lt _ _ => (BPair.ofPos Pos.one, BPair.unit)
        | Trich.eq _ => ((d + BPair.ofPos Pos.one).swap, b + b)
        | Trich.gt _ _ => (b, a.swap)) = _
      rw [hs]
    rw [hw] at h1
    exact BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_ofNat_one x)) h1
  | Trich.eq he =>
    have hae : a.oneValue BPair.unit := by
      show a.fst + Pos.one = Pos.one + a.snd
      rw [he, ground.add_comm]
    have hw : mixWit a b d = ((d + BPair.ofPos Pos.one).swap, b + b) := by
      show (match a.side with
        | Trich.lt _ _ => (BPair.ofPos Pos.one, BPair.unit)
        | Trich.eq _ => ((d + BPair.ofPos Pos.one).swap, b + b)
        | Trich.gt _ _ => (b, a.swap)) = _
      rw [hs]
    rw [hw] at h2
    refine ground.mul_cancel_unit (dblOff (twoOffB hae hns)) ?_
    rw [BPair.mul_comm]
    exact h2
  | Trich.gt g hg =>
    have hw : mixWit a b d = (b, a.swap) := by
      show (match a.side with
        | Trich.lt _ _ => (BPair.ofPos Pos.one, BPair.unit)
        | Trich.eq _ => ((d + BPair.ofPos Pos.one).swap, b + b)
        | Trich.gt _ _ => (b, a.swap)) = _
      rw [hs]
    rw [hw] at h2
    refine ground.mul_cancel_unit
      (swapOff (ground.offOfUnitLt (unitLtOfSide ⟨g, hg⟩))) ?_
    rw [BPair.mul_comm]
    exact h2

/-! The head block's peel at a combination of the raw list: the
block's own quadratic at the emitted coefficients joined to the
suffix's fold. -/

private theorem peel1p (a : BPair) (bs : List SBlock) (k : Nat)
    (p x : BPair) (cs : List BPair) (M : Mat)
    (hM : rowsLen (widthOf bs k) M) :
    (bQuad (SBlock.one a :: bs) k
        (combo (widthOf (SBlock.one a :: bs) k) (x :: cs)
          ((p :: List.replicate (widthOf bs k) BPair.unit)
            :: M.map (fun v => BPair.unit :: v)))).oneValue
      (blkQ1 a (x * p) + bQuad bs k (combo (widthOf bs k) cs M)) := by
  have hw : widthOf (SBlock.one a :: bs) k = widthOf bs k + 1 :=
    widthOf_shift bs k 1
  rw [hw]
  exact BPair.oneValue_trans
    (bQuad_congr (SBlock.one a :: bs) k
      (shape1 (widthOf bs k) p x cs M hM))
    (peel_one a bs k (x * p) (combo (widthOf bs k) cs M))

private theorem peel1z (a : BPair) (bs : List SBlock) (k : Nat)
    (cs : List BPair) (M : Mat) (hM : rowsLen (widthOf bs k) M) :
    (bQuad (SBlock.one a :: bs) k
        (combo (widthOf (SBlock.one a :: bs) k) cs
          (M.map (fun v => BPair.unit :: v)))).oneValue
      (bQuad bs k (combo (widthOf bs k) cs M)) := by
  have hw : widthOf (SBlock.one a :: bs) k = widthOf bs k + 1 :=
    widthOf_shift bs k 1
  rw [hw]
  refine BPair.oneValue_trans
    (bQuad_congr (SBlock.one a :: bs) k
      (comboConsU (widthOf bs k) cs M hM)) ?_
  refine BPair.oneValue_trans
    (peel_one a bs k BPair.unit (combo (widthOf bs k) cs M)) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (blkQ1_null (BPair.oneValue_refl BPair.unit))
      (BPair.oneValue_refl _))
    (BPair.unit_add _)

private theorem peel2p (a b d : BPair) (bs : List SBlock) (k : Nat)
    (p q x : BPair) (cs : List BPair) (M : Mat)
    (hM : rowsLen (widthOf bs k) M) :
    (bQuad (SBlock.two a b d :: bs) k
        (combo (widthOf (SBlock.two a b d :: bs) k) (x :: cs)
          ((p :: q :: List.replicate (widthOf bs k) BPair.unit)
            :: M.map (fun v => BPair.unit :: BPair.unit :: v)))).oneValue
      (blkQ2 a b d (x * p) (x * q)
        + bQuad bs k (combo (widthOf bs k) cs M)) := by
  have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
    widthOf_shift bs k 2
  rw [hw]
  exact BPair.oneValue_trans
    (bQuad_congr (SBlock.two a b d :: bs) k
      (shape2 (widthOf bs k) p q x cs M hM))
    (peel_two a b d bs k (x * p) (x * q) (combo (widthOf bs k) cs M))

private theorem peel2c (a b d : BPair) (bs : List SBlock) (k : Nat)
    (x y : BPair) (cs : List BPair) (M : Mat)
    (hM : rowsLen (widthOf bs k) M) :
    (bQuad (SBlock.two a b d :: bs) k
        (combo (widthOf (SBlock.two a b d :: bs) k) (x :: y :: cs)
          ((BPair.ofPos Pos.one :: BPair.unit
              :: List.replicate (widthOf bs k) BPair.unit)
            :: (BPair.unit :: BPair.ofPos Pos.one
              :: List.replicate (widthOf bs k) BPair.unit)
            :: M.map (fun v => BPair.unit :: BPair.unit :: v)))).oneValue
      (blkQ2 a b d x y + bQuad bs k (combo (widthOf bs k) cs M)) := by
  have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
    widthOf_shift bs k 2
  rw [hw]
  exact BPair.oneValue_trans
    (bQuad_congr (SBlock.two a b d :: bs) k
      (shape2cols (widthOf bs k) x y cs M hM))
    (peel_two a b d bs k x y (combo (widthOf bs k) cs M))

private theorem peel2z (a b d : BPair) (bs : List SBlock) (k : Nat)
    (cs : List BPair) (M : Mat) (hM : rowsLen (widthOf bs k) M) :
    (bQuad (SBlock.two a b d :: bs) k
        (combo (widthOf (SBlock.two a b d :: bs) k) cs
          (M.map (fun v => BPair.unit :: BPair.unit :: v)))).oneValue
      (bQuad bs k (combo (widthOf bs k) cs M)) := by
  have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
    widthOf_shift bs k 2
  rw [hw]
  refine BPair.oneValue_trans
    (bQuad_congr (SBlock.two a b d :: bs) k
      (comboConsU2 (widthOf bs k) cs M hM)) ?_
  refine BPair.oneValue_trans
    (peel_two a b d bs k BPair.unit BPair.unit
      (combo (widthOf bs k) cs M)) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr
      (blkQ2_null (BPair.oneValue_refl BPair.unit)
        (BPair.oneValue_refl BPair.unit))
      (BPair.oneValue_refl _))
    (BPair.unit_add _)

private theorem kerRows_indep : ∀ (k : Nat) (cs : List BPair),
    cs.length = (kerRows k).length →
    poly.unitTail (combo k cs (kerRows k)) → poly.unitTail cs
  | 0, [], _, _ => trivial
  | 0, _ :: _, hcs, _ => nomatch hcs
  | _ + 1, [], hcs, _ => nomatch hcs
  | k + 1, x :: cs, hcs, hu => by
    have hu' : poly.unitTail
        ((x * BPair.ofPos Pos.one) :: combo k cs (kerRows k)) :=
      poly.unitTail_oneValue_right hu
        (shape1 k (BPair.ofPos Pos.one) x cs (kerRows k) (kerRows_rows k))
    refine ⟨BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.mul_ofNat_one x)) hu'.1, ?_⟩
    refine kerRows_indep k cs ?_ hu'.2
    have h1 : cs.length + 1
        = ((kerRows k).map (fun v => BPair.unit :: v)).length + 1 := hcs
    rw [ground.length_map] at h1
    exact Nat.succ.inj h1

private theorem twoSplit : ∀ (cs : List BPair) (m : Nat),
    cs.length = m + 1 + 1 →
    ∃ x y cs', cs = x :: y :: cs' ∧ cs'.length = m
  | [], _, h => Nat.noConfusion h
  | [_], _, h => Nat.noConfusion (Nat.succ.inj h)
  | x :: y :: cs', _, h =>
    ⟨x, y, cs', rfl, Nat.succ.inj (Nat.succ.inj h)⟩

/-! The lower list's two reads: every combination at or below the
sum's unit, and every off-unit combination strictly below it. -/

private theorem lower_reads : ∀ (bs : List SBlock) (k : Nat),
    (bs.all (fun z => !(decide (z.det.oneValue BPair.unit)))) = true →
    ∀ cs : List BPair, cs.length = (rawLower bs k).length →
      bQuad bs k (combo (widthOf bs k) cs (rawLower bs k)) ≤ BPair.unit
      ∧ (¬ poly.unitTail cs →
          bQuad bs k (combo (widthOf bs k) cs (rawLower bs k))
            < BPair.unit)
  | [], k, _, [], _ =>
    ⟨ground.leB_congr_left (BPair.oneValue_symm (peel_nil k _))
        (ground.leB_refl BPair.unit),
     fun hoff => absurd trivial hoff⟩
  | [], _, _, _ :: _, hcs => nomatch hcs
  | SBlock.one a :: bs, k, hall, cs, hcs => by
    have hrest := lower_reads bs k ((ground.andSplitB hall).2)
    if hlt : a < BPair.unit then
      rw [rawLower_one_lt hlt bs k] at hcs ⊢
      match cs, hcs with
      | x :: cs', hcs =>
        have hcs2 : cs'.length = (rawLower bs k).length := by
          have h1 : cs'.length + 1
              = ((rawLower bs k).map (fun v => BPair.unit :: v)).length
                + 1 := hcs
          rw [ground.length_map] at h1
          exact Nat.succ.inj h1
        obtain ⟨hle, hstr⟩ := hrest cs' hcs2
        have hpk := peel1p a bs k (BPair.ofPos Pos.one) x cs'
          (rawLower bs k) (rawLower_rows bs k)
        refine ⟨ground.leB_congr_left (BPair.oneValue_symm hpk)
          (leUnitAdd (blkQ1_le (ground.leB_of_lt hlt) _) hle), ?_⟩
        intro hoff
        refine BPair.lt_congr (BPair.oneValue_symm hpk)
          (BPair.oneValue_refl BPair.unit) ?_
        if hx : x.oneValue BPair.unit then
          refine leAddLtUnit ?_ (hstr (fun ht => hoff ⟨hx, ht⟩))
          exact ground.leB_congr_left
            (BPair.oneValue_symm (blkQ1_null (elim.oneValue_unit_mul hx)))
            (ground.leB_refl BPair.unit)
        else
          refine ltUnitAddLe ?_ hle
          exact blkQ1_lt hlt (fun he => hx (BPair.oneValue_trans
            (BPair.oneValue_symm (BPair.mul_ofNat_one x)) he))
    else
      have hge : BPair.unit ≤ a := ground.leB_of_not_lt hlt
      rw [rawLower_one_le hge bs k] at hcs ⊢
      have hcs2 : cs.length = (rawLower bs k).length := by
        rw [ground.length_map] at hcs
        exact hcs
      obtain ⟨hle, hstr⟩ := hrest cs hcs2
      have hpk := peel1z a bs k cs (rawLower bs k) (rawLower_rows bs k)
      exact ⟨ground.leB_congr_left (BPair.oneValue_symm hpk) hle,
        fun hoff => BPair.lt_congr (BPair.oneValue_symm hpk)
          (BPair.oneValue_refl BPair.unit) (hstr hoff)⟩
  | SBlock.two a b d :: bs, k, hall, cs, hcs => by
    have hns : ¬ ((SBlock.two a b d).det).oneValue BPair.unit :=
      ground.notOfBang ((ground.andSplitB hall).1)
    have hrest := lower_reads bs k ((ground.andSplitB hall).2)
    if hD : (SBlock.two a b d).det < BPair.unit then
      rw [rawLower_two_mix hD bs k] at hcs ⊢
      match cs, hcs with
      | x :: cs', hcs =>
        have hcs2 : cs'.length = (rawLower bs k).length := by
          have h1 : cs'.length + 1
              = ((rawLower bs k).map
                (fun v => BPair.unit :: BPair.unit :: v)).length + 1 := hcs
          rw [ground.length_map] at h1
          exact Nat.succ.inj h1
        obtain ⟨hle, hstr⟩ := hrest cs' hcs2
        have hpk := peel2p a b d bs k (mixWit a b d).1 (mixWit a b d).2 x
          cs' (rawLower bs k) (rawLower_rows bs k)
        have hval := mixWit_lt hns hD
        refine ⟨ground.leB_congr_left (BPair.oneValue_symm hpk) ?_, ?_⟩
        · refine leUnitAdd ?_ hle
          rw [blkQ2_scale]
          exact mulLeUnit (unitLeSq x) (ground.leB_of_lt hval)
        · intro hoff
          refine BPair.lt_congr (BPair.oneValue_symm hpk)
            (BPair.oneValue_refl BPair.unit) ?_
          if hx : x.oneValue BPair.unit then
            refine leAddLtUnit ?_ (hstr (fun ht => hoff ⟨hx, ht⟩))
            exact ground.leB_congr_left
              (BPair.oneValue_symm
                (blkQ2_null (elim.oneValue_unit_mul hx)
                  (elim.oneValue_unit_mul hx)))
              (ground.leB_refl BPair.unit)
          else
            refine ltUnitAddLe ?_ hle
            rw [blkQ2_scale]
            exact mulNegPos (ground.sq_pos hx) hval
    else
      have hDge : BPair.unit ≤ (SBlock.two a b d).det :=
        ground.leB_of_not_lt hD
      have hDgt : BPair.unit < (SBlock.two a b d).det := ground.ltOfLeOff hDge hns
      if ha : a < BPair.unit then
        rw [rawLower_two_cols hDgt ha bs k] at hcs ⊢
        obtain ⟨x, y, cs', rfl, hcs1⟩ := twoSplit cs _ hcs
        · have hcs2 : cs'.length = (rawLower bs k).length := by
            rw [ground.length_map] at hcs1
            exact hcs1
          obtain ⟨hle, hstr⟩ := hrest cs' hcs2
          have hpk := peel2c a b d bs k x y cs' (rawLower bs k)
            (rawLower_rows bs k)
          refine ⟨ground.leB_congr_left (BPair.oneValue_symm hpk)
            (leUnitAdd (blk2_low_le ha hDgt x y) hle), ?_⟩
          intro hoff
          refine BPair.lt_congr (BPair.oneValue_symm hpk)
            (BPair.oneValue_refl BPair.unit) ?_
          if hxy : x.oneValue BPair.unit ∧ y.oneValue BPair.unit then
            refine leAddLtUnit ?_
              (hstr (fun ht => hoff ⟨hxy.1, hxy.2, ht⟩))
            exact ground.leB_congr_left
              (BPair.oneValue_symm (blkQ2_null hxy.1 hxy.2))
              (ground.leB_refl BPair.unit)
          else
            exact ltUnitAddLe (blk2_low_lt ha hDgt hxy) hle
      else
        have hage : BPair.unit ≤ a := ground.leB_of_not_lt ha
        rw [rawLower_two_nil hDge hage bs k] at hcs ⊢
        have hcs2 : cs.length = (rawLower bs k).length := by
          rw [ground.length_map] at hcs
          exact hcs
        obtain ⟨hle, hstr⟩ := hrest cs hcs2
        have hpk := peel2z a b d bs k cs (rawLower bs k)
          (rawLower_rows bs k)
        exact ⟨ground.leB_congr_left (BPair.oneValue_symm hpk) hle,
          fun hoff => BPair.lt_congr (BPair.oneValue_symm hpk)
            (BPair.oneValue_refl BPair.unit) (hstr hoff)⟩

/-! The head block's peel at the unit tail: the emitted
coefficients' own reads with the suffix's combination. -/

private theorem upeel1p (a : BPair) (bs : List SBlock) (k : Nat)
    (p x : BPair) (cs : List BPair) (M : Mat)
    (hM : rowsLen (widthOf bs k) M)
    (h : poly.unitTail
      (combo (widthOf (SBlock.one a :: bs) k) (x :: cs)
        ((p :: List.replicate (widthOf bs k) BPair.unit)
          :: M.map (fun v => BPair.unit :: v)))) :
    (x * p).oneValue BPair.unit
      ∧ poly.unitTail (combo (widthOf bs k) cs M) := by
  have hw : widthOf (SBlock.one a :: bs) k = widthOf bs k + 1 :=
    widthOf_shift bs k 1
  rw [hw] at h
  exact poly.unitTail_oneValue_right h (shape1 (widthOf bs k) p x cs M hM)

private theorem upeel1z (a : BPair) (bs : List SBlock) (k : Nat)
    (cs : List BPair) (M : Mat) (hM : rowsLen (widthOf bs k) M)
    (h : poly.unitTail
      (combo (widthOf (SBlock.one a :: bs) k) cs
        (M.map (fun v => BPair.unit :: v)))) :
    poly.unitTail (combo (widthOf bs k) cs M) := by
  have hw : widthOf (SBlock.one a :: bs) k = widthOf bs k + 1 :=
    widthOf_shift bs k 1
  rw [hw] at h
  exact (poly.unitTail_oneValue_right h
    (comboConsU (widthOf bs k) cs M hM)).2

private theorem upeel2p (a b d : BPair) (bs : List SBlock) (k : Nat)
    (p q x : BPair) (cs : List BPair) (M : Mat)
    (hM : rowsLen (widthOf bs k) M)
    (h : poly.unitTail
      (combo (widthOf (SBlock.two a b d :: bs) k) (x :: cs)
        ((p :: q :: List.replicate (widthOf bs k) BPair.unit)
          :: M.map (fun v => BPair.unit :: BPair.unit :: v)))) :
    (x * p).oneValue BPair.unit ∧ (x * q).oneValue BPair.unit
      ∧ poly.unitTail (combo (widthOf bs k) cs M) := by
  have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
    widthOf_shift bs k 2
  rw [hw] at h
  exact poly.unitTail_oneValue_right h
    (shape2 (widthOf bs k) p q x cs M hM)

private theorem upeel2c (a b d : BPair) (bs : List SBlock) (k : Nat)
    (x y : BPair) (cs : List BPair) (M : Mat)
    (hM : rowsLen (widthOf bs k) M)
    (h : poly.unitTail
      (combo (widthOf (SBlock.two a b d :: bs) k) (x :: y :: cs)
        ((BPair.ofPos Pos.one :: BPair.unit
            :: List.replicate (widthOf bs k) BPair.unit)
          :: (BPair.unit :: BPair.ofPos Pos.one
            :: List.replicate (widthOf bs k) BPair.unit)
          :: M.map (fun v => BPair.unit :: BPair.unit :: v)))) :
    x.oneValue BPair.unit ∧ y.oneValue BPair.unit
      ∧ poly.unitTail (combo (widthOf bs k) cs M) := by
  have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
    widthOf_shift bs k 2
  rw [hw] at h
  exact poly.unitTail_oneValue_right h
    (shape2cols (widthOf bs k) x y cs M hM)

private theorem upeel2z (a b d : BPair) (bs : List SBlock) (k : Nat)
    (cs : List BPair) (M : Mat) (hM : rowsLen (widthOf bs k) M)
    (h : poly.unitTail
      (combo (widthOf (SBlock.two a b d :: bs) k) cs
        (M.map (fun v => BPair.unit :: BPair.unit :: v)))) :
    poly.unitTail (combo (widthOf bs k) cs M) := by
  have hw : widthOf (SBlock.two a b d :: bs) k = widthOf bs k + 2 :=
    widthOf_shift bs k 2
  rw [hw] at h
  exact (poly.unitTail_oneValue_right h
    (comboConsU2 (widthOf bs k) cs M hM)).2.2

/-! The complement list's two reads: every combination at or above
the sum's unit, and a combination at the unit tail only at unit
coefficients. -/

private theorem compl_reads : ∀ (bs : List SBlock) (k : Nat),
    (bs.all (fun z => !(decide (z.det.oneValue BPair.unit)))) = true →
    ∀ cs : List BPair, cs.length = (rawCompl bs k).length →
      BPair.unit ≤ bQuad bs k (combo (widthOf bs k) cs (rawCompl bs k))
      ∧ (poly.unitTail (combo (widthOf bs k) cs (rawCompl bs k)) →
          poly.unitTail cs)
  | [], k, _, cs, hcs =>
    ⟨ground.leB_congr_right (BPair.oneValue_symm (peel_nil k _))
        (ground.leB_refl BPair.unit),
     fun hu => kerRows_indep k cs hcs hu⟩
  | SBlock.one a :: bs, k, hall, cs, hcs => by
    have hrest := compl_reads bs k ((ground.andSplitB hall).2)
    if hlt : a < BPair.unit then
      rw [rawCompl_one_lt hlt bs k] at hcs ⊢
      have hcs2 : cs.length = (rawCompl bs k).length := by
        rw [ground.length_map] at hcs
        exact hcs
      obtain ⟨hge, hind⟩ := hrest cs hcs2
      have hpk := peel1z a bs k cs (rawCompl bs k) (rawCompl_rows bs k)
      exact ⟨ground.leB_congr_right (BPair.oneValue_symm hpk) hge,
        fun hu => hind (upeel1z a bs k cs (rawCompl bs k)
          (rawCompl_rows bs k) hu)⟩
    else
      have hage : BPair.unit ≤ a := ground.leB_of_not_lt hlt
      rw [rawCompl_one_le hage bs k] at hcs ⊢
      match cs, hcs with
      | x :: cs', hcs =>
        have hcs2 : cs'.length = (rawCompl bs k).length := by
          have h1 : cs'.length + 1
              = ((rawCompl bs k).map (fun v => BPair.unit :: v)).length
                + 1 := hcs
          rw [ground.length_map] at h1
          exact Nat.succ.inj h1
        obtain ⟨hge, hind⟩ := hrest cs' hcs2
        have hpk := peel1p a bs k (BPair.ofPos Pos.one) x cs'
          (rawCompl bs k) (rawCompl_rows bs k)
        refine ⟨ground.leB_congr_right (BPair.oneValue_symm hpk)
          (unitLeAdd (blkQ1_ge hage _) hge), ?_⟩
        intro hu
        have hsp := upeel1p a bs k (BPair.ofPos Pos.one) x cs'
          (rawCompl bs k) (rawCompl_rows bs k) hu
        exact ⟨BPair.oneValue_trans
          (BPair.oneValue_symm (BPair.mul_ofNat_one x)) hsp.1, hind hsp.2⟩
  | SBlock.two a b d :: bs, k, hall, cs, hcs => by
    have hns : ¬ ((SBlock.two a b d).det).oneValue BPair.unit :=
      ground.notOfBang ((ground.andSplitB hall).1)
    have hrest := compl_reads bs k ((ground.andSplitB hall).2)
    if hD : (SBlock.two a b d).det < BPair.unit then
      rw [rawCompl_two_mix hD bs k] at hcs ⊢
      match cs, hcs with
      | x :: cs', hcs =>
        have hcs2 : cs'.length = (rawCompl bs k).length := by
          have h1 : cs'.length + 1
              = ((rawCompl bs k).map
                (fun v => BPair.unit :: BPair.unit :: v)).length + 1 := hcs
          rw [ground.length_map] at h1
          exact Nat.succ.inj h1
        obtain ⟨hge, hind⟩ := hrest cs' hcs2
        have hpk := peel2p a b d bs k (mixWit a.swap b.swap d.swap).1
          (mixWit a.swap b.swap d.swap).2 x cs' (rawCompl bs k)
          (rawCompl_rows bs k)
        have hval := mixWit_gt hns hD
        refine ⟨ground.leB_congr_right (BPair.oneValue_symm hpk) ?_, ?_⟩
        · refine unitLeAdd ?_ hge
          rw [blkQ2_scale]
          exact unitLeMul (unitLeSq x) (ground.leB_of_lt hval)
        · intro hu
          have hsp := upeel2p a b d bs k (mixWit a.swap b.swap d.swap).1
            (mixWit a.swap b.swap d.swap).2 x cs' (rawCompl bs k)
            (rawCompl_rows bs k) hu
          have hns' : ¬ ((SBlock.two a.swap b.swap d.swap).det).oneValue
              BPair.unit := by
            rw [detSwapEq]; exact hns
          exact ⟨mixWit_extract hns' hsp.1 hsp.2.1, hind hsp.2.2⟩
    else
      have hDge : BPair.unit ≤ (SBlock.two a b d).det :=
        ground.leB_of_not_lt hD
      have hDgt : BPair.unit < (SBlock.two a b d).det := ground.ltOfLeOff hDge hns
      if ha : a < BPair.unit then
        rw [rawCompl_two_nil hDgt ha bs k] at hcs ⊢
        have hcs2 : cs.length = (rawCompl bs k).length := by
          rw [ground.length_map] at hcs
          exact hcs
        obtain ⟨hge, hind⟩ := hrest cs hcs2
        have hpk := peel2z a b d bs k cs (rawCompl bs k)
          (rawCompl_rows bs k)
        exact ⟨ground.leB_congr_right (BPair.oneValue_symm hpk) hge,
          fun hu => hind (upeel2z a b d bs k cs (rawCompl bs k)
            (rawCompl_rows bs k) hu)⟩
      else
        have hage : BPair.unit ≤ a := ground.leB_of_not_lt ha
        have hapos : BPair.unit < a := twoLeadPos hDgt hage
        rw [rawCompl_two_cols hDge hage bs k] at hcs ⊢
        obtain ⟨x, y, cs', rfl, hcs1⟩ := twoSplit cs _ hcs
        · have hcs2 : cs'.length = (rawCompl bs k).length := by
            rw [ground.length_map] at hcs1
            exact hcs1
          obtain ⟨hge, hind⟩ := hrest cs' hcs2
          have hpk := peel2c a b d bs k x y cs' (rawCompl bs k)
            (rawCompl_rows bs k)
          refine ⟨ground.leB_congr_right (BPair.oneValue_symm hpk)
            (unitLeAdd (blk2_psd hapos hDgt x y) hge), ?_⟩
          intro hu
          have hsp := upeel2c a b d bs k x y cs' (rawCompl bs k)
            (rawCompl_rows bs k) hu
          exact ⟨hsp.1, hsp.2.1, hind hsp.2.2⟩

/-! The two lists themselves: the congruence's images of the raw
families, with the transport of the datum's quadratic form at a
combination to the block diagonal's own fold. -/

/-- The lower list at a split: the congruence's images of the raw
lower-side vectors, one per lower-side unit — the order-1 columns
at a lower-side entry, both columns of a 2×2 at the shared lower
side, and the mixed block's own witness. -/
def lowerList {n : Nat} (sp : Split n) : Mat :=
  (rawLower sp.blocks sp.kern).map (matVec sp.T.val)

/-- The complement list at a split: the congruence's images of the
raw vectors of the rest of the order — the upper-side order-1
columns, both columns of a 2×2 at the shared upper side, each mixed
block's upper-side vector (the memberwise swap's own witness) and
the kernel block's columns. -/
def complList {n : Nat} (sp : Split n) : Mat :=
  (rawCompl sp.blocks sp.kern).map (matVec sp.T.val)

private theorem listQuad {n : Nat} (S : Mat) (sp : Split n)
    (hsq : sqAt S n)
    (hcong : matOneValue
      (matMul (transposeM sp.T.val) (matMul S sp.T.val))
      (blockMat sp.blocks sp.kern))
    (R : Mat) (hRn : rowsLen n R) (cs : List BPair) :
    (dotN (combo n cs (R.map (matVec sp.T.val)))
        (matVec S (combo n cs (R.map (matVec sp.T.val))))).oneValue
      (bQuad sp.blocks sp.kern (combo n cs R)) := by
  have hTrows : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
  have hc : (combo n cs R).length = n := length_combo n cs R hRn
  have hmv := elim.matVec_combo sp.T.val n cs R hRn
  rw [sp.T.rows] at hmv
  have hlenL : (combo n cs (R.map (matVec sp.T.val))).length = n :=
    length_combo n cs _ (rowsLen_map (matVec sp.T.val) n R (fun x _ => (fun y => (matVec_length sp.T.val y).trans sp.T.rows) x))
  have hlenR : (matVec sp.T.val (combo n cs R)).length = n :=
    (matVec_length sp.T.val _).trans sp.T.rows
  refine BPair.oneValue_trans
    (quad_congr S _ _ (poly.oneValue_symm hmv)) ?_
  refine BPair.oneValue_trans
    (congTransport S sp hsq hcong (combo n cs R) hc) ?_
  exact quadP_read (blockMat sp.blocks sp.kern) (combo n cs R)

/-- The lower list's vectors read the split's own order, the
certificate's own shape and no datum anywhere. -/
theorem lowerList_rowsLen {n : Nat} (sp : Split n) :
    rowsLen n (lowerList sp) :=
  rowsLen_map (matVec sp.T.val) n (rawLower sp.blocks sp.kern) (fun x _ => (fun y => (matVec_length sp.T.val y).trans sp.T.rows) x)

/-- The lower list's count is the split's reversal count. -/
theorem lowerList_length {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) : (lowerList sp).length = revAt sp := by
  obtain ⟨-, ⟨-, -, -⟩, -, hns⟩ := h
  show ((rawLower sp.blocks sp.kern).map (matVec sp.T.val)).length
    = revAt sp
  rw [ground.length_map, rawLower_length sp.blocks sp.kern hns]
  rfl

/-- Every off-unit combination of the lower list prices the datum's
quadratic form strictly below the sum's unit. -/
theorem lowerList_strict {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) :
    ∀ cs : List BPair, cs.length = revAt sp → ¬ poly.unitTail cs →
      dotN (combo n cs (lowerList sp))
        (matVec S (combo n cs (lowerList sp))) < BPair.unit := by
  intro cs hcs hoff
  obtain ⟨hsq, ⟨-, -, -⟩, hcong, hns⟩ := h
  have hN : widthOf sp.blocks sp.kern = n :=
    Nat.eq_of_beq_eq_true sp.width
  have hRn : rowsLen n (rawLower sp.blocks sp.kern) :=
    rowsLen_cast hN (rawLower_rows sp.blocks sp.kern)
  have hcs2 : cs.length = (rawLower sp.blocks sp.kern).length :=
    hcs.trans (rawLower_length sp.blocks sp.kern hns).symm
  have hlow := (lower_reads sp.blocks sp.kern hns cs hcs2).2 hoff
  rw [hN] at hlow
  exact BPair.lt_congr
    (BPair.oneValue_symm
      (listQuad S sp hsq hcong (rawLower sp.blocks sp.kern) hRn cs))
    (BPair.oneValue_refl BPair.unit) hlow

/-- The complement list's vectors read the split's own order, the
certificate's own shape and no datum anywhere. -/
theorem complList_rowsLen {n : Nat} (sp : Split n) :
    rowsLen n (complList sp) :=
  rowsLen_map (matVec sp.T.val) n (rawCompl sp.blocks sp.kern) (fun x _ => (fun y => (matVec_length sp.T.val y).trans sp.T.rows) x)

/-- The two lists' counts join to the split's order. -/
theorem complList_length {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) : revAt sp + (complList sp).length = n := by
  obtain ⟨-, ⟨-, -, -⟩, -, hns⟩ := h
  show revAt sp
      + ((rawCompl sp.blocks sp.kern).map (matVec sp.T.val)).length = n
  rw [ground.length_map,
    show revAt sp = (rawLower sp.blocks sp.kern).length from
      (rawLower_length sp.blocks sp.kern hns).symm,
    raw_length_sum sp.blocks sp.kern hns]
  exact Nat.eq_of_beq_eq_true sp.width

/-- Every combination of the complement list prices the datum's
quadratic form at or above the sum's unit. -/
theorem complList_side {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) :
    ∀ cs : List BPair, cs.length = (complList sp).length →
      ¬ (dotN (combo n cs (complList sp))
          (matVec S (combo n cs (complList sp))) < BPair.unit) := by
  intro cs hcs
  obtain ⟨hsq, ⟨-, -, -⟩, hcong, hns⟩ := h
  have hN : widthOf sp.blocks sp.kern = n :=
    Nat.eq_of_beq_eq_true sp.width
  have hRn : rowsLen n (rawCompl sp.blocks sp.kern) :=
    rowsLen_cast hN (rawCompl_rows sp.blocks sp.kern)
  have hcs2 : cs.length = (rawCompl sp.blocks sp.kern).length := by
    rw [hcs]
    show ((rawCompl sp.blocks sp.kern).map (matVec sp.T.val)).length
      = (rawCompl sp.blocks sp.kern).length
    rw [ground.length_map]
  have hcpl := (compl_reads sp.blocks sp.kern hns cs hcs2).1
  rw [hN] at hcpl
  exact ground.leB_not_lt
    (ground.leB_congr_right
      (BPair.oneValue_symm
        (listQuad S sp hsq hcong (rawCompl sp.blocks sp.kern) hRn cs))
      hcpl)

/-- A combination of the complement list at the unit tail has unit
coefficients: the complement family is independent, the witness's
clearing the transport. -/
theorem complList_indep {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) :
    ∀ cs : List BPair, cs.length = (complList sp).length →
      poly.unitTail (combo n cs (complList sp)) → poly.unitTail cs := by
  intro cs hcs hu
  obtain ⟨-, ⟨hdetT, -, hprod⟩, -, hns⟩ := h
  have hN : widthOf sp.blocks sp.kern = n :=
    Nat.eq_of_beq_eq_true sp.width
  have hRn : rowsLen n (rawCompl sp.blocks sp.kern) :=
    rowsLen_cast hN (rawCompl_rows sp.blocks sp.kern)
  have hTrows : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
  have hTwrows : rowsLen n sp.Tw.val := rowsLen_of_sqAt sp.Tw.shape
  have hc : (combo n cs (rawCompl sp.blocks sp.kern)).length = n :=
    length_combo n cs _ hRn
  have hmv := elim.matVec_combo sp.T.val n cs
    (rawCompl sp.blocks sp.kern) hRn
  rw [sp.T.rows] at hmv
  have hu1 : poly.unitTail
      (matVec sp.T.val (combo n cs (rawCompl sp.blocks sp.kern))) :=
    poly.oneValue_unitTail hmv hu
  have hu2 : poly.unitTail (matVec sp.Tw.val
      (matVec sp.T.val (combo n cs (rawCompl sp.blocks sp.kern)))) :=
    matVec_null sp.Tw.val _ hu1
  have hA : poly.oneValue
      (matVec sp.Tw.val
        (matVec sp.T.val (combo n cs (rawCompl sp.blocks sp.kern))))
      (vecScale (minor sp.T.val)
        (combo n cs (rawCompl sp.blocks sp.kern))) := by
    refine poly.oneValue_trans
      (matVec_comp sp.Tw.val sp.T.val
        (combo n cs (rawCompl sp.blocks sp.kern)) n hTrows hc
        (by rw [sp.T.rows]; exact hTwrows)) ?_
    refine poly.oneValue_trans
      (matVec_matOne _ _ (combo n cs (rawCompl sp.blocks sp.kern))
        hprod) ?_
    exact scaleId_act (minor sp.T.val) n
      (combo n cs (rawCompl sp.blocks sp.kern)) hc
  have hu4 : poly.unitTail (combo n cs (rawCompl sp.blocks sp.kern)) :=
    elim.unitTail_unscale _ hdetT _ (poly.unitTail_oneValue_right hu2 hA)
  have hcs2 : cs.length = (rawCompl sp.blocks sp.kern).length := by
    rw [hcs]
    show ((rawCompl sp.blocks sp.kern).map (matVec sp.T.val)).length
      = (rawCompl sp.blocks sp.kern).length
    rw [ground.length_map]
  refine (compl_reads sp.blocks sp.kern hns cs hcs2).2 ?_
  rw [hN]
  exact hu4

/-! `lem:inertia`'s forcing clause and the count's three general
reads.  The forcing clause is the two lists' join: a family of the
split's own order pricing every off-unit combination strictly below
the sum's unit, joined to the complement list, is independent — a
joint combination at the unit tail forces its complement-side
coefficients through `complList_indep`, and off the unit on the
lower side the joint vanishing exhibits the complement-side vector
as the lower side's memberwise swap, whose form the swap walks
unchanged, so the strict read meets the complement's at-or-above one
and the trichotomy refuses.  The width bound (`elim.indep_bound`)
then prices the joined count at the order, and the two lists' count
identity leaves the family's count at or below the reversal count.
The three reads follow at one engine: the lower list of a second
split is such a family (the exchange, `rev_exchange`, symmetrized at
the antisymmetry), it stays such a family at a datum below a
positive-semidefinite difference (the monotonicity, `rev_mono`, the
site datum's form decomposition its whole content), and its
congruence image is such a family for the compressed datum (the
compression comparison, `rev_compress`, the quadratic form's
transport at a rectangular congruence, witness-free in the one
direction consumed). -/

/-- A datum at or below one strictly below the sum's unit sits
strictly below it. -/
private theorem ltUnitOfLeB {x y : BPair} (h : x ≤ y)
    (hy : y < BPair.unit) : x < BPair.unit := by
  refine ground.ltUnitOfSide ?_
  have hle : x.fst + y.snd ≤ y.fst + x.snd := h
  have key : y.fst + (x.fst + y.snd) < y.snd + (y.fst + x.snd) :=
    posLtAddLe (ground.sideOfLtUnit hy) hle
  have e1 : x.fst + (y.snd + y.fst) = y.fst + (x.fst + y.snd) :=
    (ground.add_assoc x.fst y.snd y.fst).symm.trans
      (ground.add_comm (x.fst + y.snd) y.fst)
  have e2 : x.snd + (y.snd + y.fst) = y.snd + (y.fst + x.snd) :=
    (ground.add_comm x.snd (y.snd + y.fst)).trans
      (ground.add_assoc y.snd y.fst x.snd)
  refine posLtCancelR (c := y.snd + y.fst) ?_
  rw [e1, e2]
  exact key

/-- A vanishing sum at a vanishing first member vanishes at the
second. -/
theorem unitTailAddLeft : ∀ (a b : List BPair),
    a.length = b.length → poly.unitTail a →
    poly.unitTail (vecAdd a b) → poly.unitTail b
  | [], [], _, _, _ => trivial
  | [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, [], hl, _, _ => nomatch hl
  | _ :: a, y :: b, hl, ha, hab =>
    ⟨BPair.oneValue_trans (BPair.oneValue_symm (BPair.unit_add y))
      (BPair.oneValue_trans
        (BPair.oneValue_symm
          (BPair.add_congr ha.1 (BPair.oneValue_refl y)))
        hab.1),
     unitTailAddLeft a b (Nat.succ.inj hl) ha.2 hab.2⟩

/-- The quadratic form's fold at a vector, the pairing's read. -/
def quadForm (A : Mat) (u : List BPair) : BPair :=
  dotN u (matVec A u)

/-! The form fold's decomposition at the site datum: the fold is
additive over the entrywise row sum, walks the memberwise swap, and
carries a positive rescaling out of the matrix — so the datum's
form against the sum's unit is exactly the two forms' own
comparison, `uᵀ(A + Bˇ)u < 0` at `uᵀAu < uᵀBu`.  The scaled
corollaries are the level's own spelling, the clearing weights
riding on the two members. -/

/-- The form fold is additive over the entrywise row sum: at a
shared order the sum matrix's form is the two forms' own. -/
theorem quadForm_add (A B : Mat) (u : List BPair)
    (hAl : A.length = u.length) (hAr : rowsLen u.length A)
    (hBl : B.length = u.length) (hBr : rowsLen u.length B) :
    (quadForm (matAdd A B) u).oneValue (quadForm A u + quadForm B u) := by
  refine BPair.oneValue_trans (quadP_read (matAdd A B) u) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_right u _ _ (matAdd_dotPmap A B u hAr hBr)) ?_
  refine BPair.oneValue_trans
    (dotP_vecAdd u (A.map (fun r => dotP r u))
      (B.map (fun r => dotP r u))
      ((ground.length_map _ A).trans hAl)
      ((ground.length_map _ B).trans hBl)) ?_
  exact BPair.add_congr (BPair.oneValue_symm (quadP_read A u))
    (BPair.oneValue_symm (quadP_read B u))

private theorem swapMapRows : ∀ (M : Mat) (u : List BPair),
    (matSwap M).map (fun r => dotP r u)
      = (M.map (fun r => dotP r u)).map BPair.swap
  | [], _ => rfl
  | r :: t, u => by
    show dotP (r.map BPair.swap) u
        :: (matSwap t).map (fun s => dotP s u)
      = (dotP r u).swap :: (t.map (fun s => dotP s u)).map BPair.swap
    rw [dotP_comm (r.map BPair.swap) u, dotP_swapMap u r,
      dotP_comm u r, swapMapRows t u]

/-- The form fold walks the memberwise swap: the swapped matrix's
form is the form's own swap, at every vector. -/
theorem quadForm_swap (M : Mat) (u : List BPair) :
    (quadForm (matSwap M) u).oneValue (quadForm M u).swap := by
  refine BPair.oneValue_trans (quadP_read (matSwap M) u) ?_
  rw [swapMapRows M u, dotP_swapMap u (M.map (fun r => dotP r u))]
  exact ground.swap_congr (BPair.oneValue_symm (quadP_read M u))

private theorem scaleMulLeft (x y : BPair) (w : Pos) :
    x.scale w * y = (x * y).scale w :=
  (ground.BPair.scale_mul_left x y w).symm

private theorem dotP_scalePos : ∀ (r u : List BPair) (w : Pos),
    (dotP (r.map (fun x => x.scale w)) u).oneValue ((dotP r u).scale w)
  | [], _, w => ground.unitScale w
  | _ :: _, [], w => ground.unitScale w
  | a :: r, b :: u, w => by
    show (a.scale w * b + dotP (r.map (fun x => x.scale w)) u).oneValue
      ((a * b + dotP r u).scale w)
    rw [BPair.scale_add, scaleMulLeft]
    exact BPair.add_congr (BPair.oneValue_refl _) (dotP_scalePos r u w)

private theorem dotP_scaleRight (r v : List BPair) (w : Pos) :
    (dotP r (v.map (fun x => x.scale w))).oneValue
      ((dotP r v).scale w) := by
  rw [dotP_comm r (v.map (fun x => x.scale w)), dotP_comm r v]
  exact dotP_scalePos v r w

private theorem scaleMapRows (w : Pos) : ∀ (M : Mat) (u : List BPair),
    poly.oneValue ((matScale w M).map (fun r => dotP r u))
      ((M.map (fun r => dotP r u)).map (fun x => x.scale w))
  | [], _ => trivial
  | r :: t, u => ⟨dotP_scalePos r u w, scaleMapRows w t u⟩

/-- The form fold carries a positive rescaling out of the matrix:
the scaled matrix's form is the form's own scale. -/
theorem quadForm_scale (w : Pos) (M : Mat) (u : List BPair) :
    (quadForm (matScale w M) u).oneValue ((quadForm M u).scale w) := by
  refine BPair.oneValue_trans (quadP_read (matScale w M) u) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_right u _ _ (scaleMapRows w M u)) ?_
  refine BPair.oneValue_trans
    (dotP_scaleRight u (M.map (fun r => dotP r u)) w) ?_
  exact BPair.scale_congr w (BPair.oneValue_symm (quadP_read M u))

/-- The site datum's form splits into the two members' own, the
second entering swapped — the elimination's `A = B + S` read at a
vector. -/
theorem quadForm_site {X Y : Mat} {u : List BPair}
    (hXl : X.length = u.length) (hXr : rowsLen u.length X)
    (hYl : Y.length = u.length) (hYr : rowsLen u.length Y) :
    (quadForm (siteDatum X Y) u).oneValue
      (quadForm X u + (quadForm Y u).swap) := by
  refine BPair.oneValue_trans
    (quadForm_add X (matSwap Y) u hXl hXr
      ((ground.length_map _ Y).trans hYl)
      (rowsLen_mapRows BPair.swap Y u.length hYr)) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) (quadForm_swap Y u)

/-- The rescaled datum's form at the one-member site: the scaled
matrix's quadratic read is the site's weight against the unscaled
read. -/
theorem quadForm_ofPos (w : Pos) (A : Mat) (u : List BPair) :
    (quadForm (matScale w A) u).oneValue
      (BPair.ofPos w * quadForm A u) :=
  BPair.oneValue_trans (quadForm_scale w A u)
    (BPair.oneValue_symm (BPair.ofPos_scale w (quadForm A u)))

/-- The form's sum split at the stated order, the square shapes'
own frame. -/
theorem quadForm_add_sq {o : Nat} {A B : Mat} {u : List BPair}
    (hA : sqAt A o) (hB : sqAt B o) (hu : u.length = o) :
    (quadForm (matAdd A B) u).oneValue
      (quadForm A u + quadForm B u) :=
  quadForm_add A B u ((sqAt_len hA).trans hu.symm)
    (by rw [hu]; exact rowsLen_of_sqAt hA)
    ((sqAt_len hB).trans hu.symm)
    (by rw [hu]; exact rowsLen_of_sqAt hB)

/-- The site datum's form split at the stated order, the square
shapes' own frame. -/
theorem quadForm_site_sq {o : Nat} {X Y : Mat} {u : List BPair}
    (hX : sqAt X o) (hY : sqAt Y o) (hu : u.length = o) :
    (quadForm (siteDatum X Y) u).oneValue
      (quadForm X u + (quadForm Y u).swap) :=
  quadForm_site ((sqAt_len hX).trans hu.symm)
    (by rw [hu]; exact rowsLen_of_sqAt hX)
    ((sqAt_len hY).trans hu.symm)
    (by rw [hu]; exact rowsLen_of_sqAt hY)

/-- The site datum's form below the sum's unit is the two forms'
own strict order, the gap carried across. -/
theorem site_gap {X Y : Mat} {u : List BPair}
    (hXl : X.length = u.length) (hXr : rowsLen u.length X)
    (hYl : Y.length = u.length) (hYr : rowsLen u.length Y)
    (h : quadForm (siteDatum X Y) u < BPair.unit) :
    quadForm X u < quadForm Y u :=
  ground.ltB_of_add_unit
    (BPair.lt_congr (quadForm_site hXl hXr hYl hYr)
      (BPair.oneValue_refl BPair.unit) h)

/-- The site datum's form at or above the sum's unit refuses the
two forms' strict order, the requirement's own read. -/
theorem site_side {X Y : Mat} {u : List BPair}
    (hXl : X.length = u.length) (hXr : rowsLen u.length X)
    (hYl : Y.length = u.length) (hYr : rowsLen u.length Y)
    (h : ¬ (quadForm (siteDatum X Y) u < BPair.unit)) :
    ¬ (quadForm X u < quadForm Y u) :=
  ground.leB_not_lt
    (ground.leB_of_unit_add
      (ground.leB_congr_right (quadForm_site hXl hXr hYl hYr)
        (ground.leB_of_not_lt h)))

/-- The one-sided comparison's pointwise form comparison: at the
split's own transport the lower datum's form sits at or below the
upper's at every vector of the stated order. -/
theorem le_all {n : Nat} (S C : Mat) (sp : Split n)
    (hS : sqAt S n) (hC : sqAt C n) (h : leAt S C sp) :
    ∀ u : List BPair, u.length = n → quadForm S u ≤ quadForm C u :=
  fun u hu => ground.leB_of_not_lt
    (site_side ((sqAt_len hC).trans hu.symm)
      (by rw [hu]; exact rowsLen_of_sqAt hC)
      ((sqAt_len hS).trans hu.symm)
      (by rw [hu]; exact rowsLen_of_sqAt hS)
      (psd_all _ sp h.1 h.2 u hu))

/-- The cleared site datum's form below the sum's unit is the two
forms' scaled order, the level's weights riding on the members. -/
theorem scaledSite_gap {X Y : Mat} {u : List BPair} {gn gd : Pos}
    (hXl : X.length = u.length) (hXr : rowsLen u.length X)
    (hYl : Y.length = u.length) (hYr : rowsLen u.length Y)
    (h : quadForm (siteDatum (matScale gd X) (matScale gn Y)) u
      < BPair.unit) :
    (quadForm X u).scale gd < (quadForm Y u).scale gn :=
  BPair.lt_congr (quadForm_scale gd X u) (quadForm_scale gn Y u)
    (site_gap ((ground.length_map _ X).trans hXl)
      (rowsLen_mapRows _ X u.length hXr)
      ((ground.length_map _ Y).trans hYl)
      (rowsLen_mapRows _ Y u.length hYr) h)

/-- The cleared site datum's form at or above the sum's unit
refuses the two forms' scaled order, the requirement at a level. -/
theorem scaledSite_side {X Y : Mat} {u : List BPair} {gn gd : Pos}
    (hXl : X.length = u.length) (hXr : rowsLen u.length X)
    (hYl : Y.length = u.length) (hYr : rowsLen u.length Y)
    (h : ¬ (quadForm (siteDatum (matScale gd X) (matScale gn Y)) u
      < BPair.unit)) :
    ¬ ((quadForm X u).scale gd < (quadForm Y u).scale gn) :=
  fun hlt =>
    site_side ((ground.length_map _ X).trans hXl)
      (rowsLen_mapRows _ X u.length hXr)
      ((ground.length_map _ Y).trans hYl)
      (rowsLen_mapRows _ Y u.length hYr) h
      (BPair.lt_congr (BPair.oneValue_symm (quadForm_scale gd X u))
        (BPair.oneValue_symm (quadForm_scale gn Y u)) hlt)

/-- The form carries a one-value read of its vector. -/
theorem quadForm_congr (A : Mat) {u u' : List BPair}
    (h : poly.oneValue u u') :
    (quadForm A u).oneValue (quadForm A u') :=
  BPair.oneValue_trans (dotN_read u _)
    (BPair.oneValue_trans (dotP_oneValue_left _ _ _ h)
      (BPair.oneValue_trans
        (dotP_oneValue_right _ _ _ (matVec_congr A u u' h))
        (BPair.oneValue_symm (dotN_read u' _))))

/-- The form at a cleared vector is the clearing's square against
the form (`lem:inertia`'s congruence read at a scaled column). -/
theorem quadScaleVec (A : Mat) (k : BPair) (u x : List BPair)
    (hx : poly.oneValue x (vecScale k u)) :
    (quadForm A x).oneValue
      (k * k * quadForm A u) := by
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  refine BPair.oneValue_trans (dotP_oneValue_left _ _ _ hx) ?_
  refine BPair.oneValue_trans (dotP_oneValue_right _ _ _
    (matVec_congr A x (vecScale k u) hx)) ?_
  refine BPair.oneValue_trans (dotP_oneValue_right _ _ _
    (matVec_vecScale_free A k u)) ?_
  refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
  have hstep : (dotP (vecScale k u) (matVec A u)).oneValue
      (k * dotP (matVec A u) u) := by
    rw [dotP_comm (vecScale k u) (matVec A u)]
    exact dotP_vecScale_right _ _ _
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl k) hstep) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_assoc k k _).symm) ?_
  refine BPair.mul_congr (BPair.oneValue_refl (k * k)) ?_
  rw [dotP_comm (matVec A u) u]
  exact BPair.oneValue_symm (dotN_read u (matVec A u))

/-- The forcing clause (`lem:inertia`'s general tier): a family at
the split's own order pricing every off-unit combination of its
members strictly below the sum's unit counts at or below the
reversal count. -/
theorem forcing {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) (L : Mat) (hL : rowsLen n L)
    (hstrict : ∀ cs : List BPair, cs.length = L.length →
      ¬ poly.unitTail cs →
      dotN (combo n cs L) (matVec S (combo n cs L)) < BPair.unit) :
    L.length ≤ revAt sp := by
  have hC : rowsLen n (complList sp) := complList_rowsLen sp
  have hLC : rowsLen n (L ++ complList sp) := rowsLen_append n hL hC
  have hall : ∀ cs : List BPair,
      cs.length = (L ++ complList sp).length →
      poly.unitTail (combo n cs (L ++ complList sp)) →
      poly.unitTail cs := by
    intro cs hcs hu
    have hlen : cs.length = L.length + (complList sp).length := by
      rw [hcs, ground.length_append]
    obtain ⟨csL, csC, rfl, hlL⟩ :=
      listSplit cs L.length (by rw [hlen]; exact Nat.le_add_right _ _)
    have h1 : csL.length + csC.length
        = L.length + (complList sp).length := by
      rw [← ground.length_append csL csC]
      exact hlen
    rw [hlL] at h1
    have hlC : csC.length = (complList sp).length :=
      ground.addCancelL L.length h1
    have hvl : (combo n csL L).length = n := length_combo n csL L hL
    have hwl : (combo n csC (complList sp)).length = n :=
      length_combo n csC (complList sp) hC
    have hcomb : poly.oneValue
        (combo n (csL ++ csC) (L ++ complList sp))
        (vecAdd (combo n csL L) (combo n csC (complList sp))) :=
      combo_append n csL L csC (complList sp) hlL hL hC
    have huv : poly.unitTail
        (vecAdd (combo n csL L) (combo n csC (complList sp))) :=
      poly.unitTail_oneValue_right hu hcomb
    cases (inferInstance : Decidable (poly.unitTail csL)) with
    | isTrue hcase =>
      refine unitTail_append hcase (complList_indep S sp h csC hlC ?_)
      exact unitTailAddLeft _ _ (by rw [hvl, hwl])
        (unitTail_combo_of n csL L hcase) huv
    | isFalse hcase =>
      have hsw : poly.oneValue (combo n csC (complList sp))
          ((combo n csL L).map BPair.swap) :=
        swap_of_null_add _ _ (by rw [hvl, hwl]) huv
      have hcg := quad_congr S (combo n csC (complList sp))
        ((combo n csL L).map BPair.swap) hsw
      rw [dotN_matVec_swapMap S (combo n csL L)] at hcg
      exact absurd
        (BPair.lt_congr (BPair.oneValue_symm hcg)
          (BPair.oneValue_refl BPair.unit)
          (hstrict csL hlL hcase))
        (complList_side S sp h csC hlC)
  have hb : (L ++ complList sp).length ≤ n :=
    indep_bound n (L ++ complList sp) hLC
      (indep_intro n (L ++ complList sp) hLC hall)
  rw [ground.length_append] at hb
  have hb2 : L.length + (complList sp).length
      ≤ revAt sp + (complList sp).length := by
    rw [complList_length S sp h]
    exact hb
  exact leCancelR (complList sp).length hb2

/-- The two-splits-one-count exchange: every split of a datum reads
the one reversal count, each split's lower list forcing the other's
count. -/
theorem rev_exchange {n : Nat} (S : Mat) (sp sp' : Split n)
    (h : splitRead S sp) (h' : splitRead S sp') :
    revAt sp = revAt sp' := by
  have key : ∀ a b : Split n, splitRead S a → splitRead S b →
      revAt a ≤ revAt b := by
    intro a b ha hb
    have hlen : (lowerList a).length = revAt a := lowerList_length S a ha
    have hfin := forcing S b hb (lowerList a) (lowerList_rowsLen a)
      (fun cs hcs hoff =>
        lowerList_strict S a ha cs (hcs.trans hlen) hoff)
    rw [hlen] at hfin
    exact hfin
  exact Nat.le_antisymm (key sp sp' h h') (key sp' sp h' h)

/-- The monotonicity: at a positive-semidefinite site datum
`siteDatum S' S` — the difference read `S ⪯ S'` — the upper datum's
reversal count sits at or below the lower's. -/
theorem rev_mono {n : Nat} (S S' : Mat) (spd sp sp' : Split n)
    (hd : splitRead (siteDatum S' S) spd) (hpd : psdAt spd)
    (h : splitRead S sp) (h' : splitRead S' sp') :
    revAt sp' ≤ revAt sp := by
  have hsq : sqAt S n := h.1
  have hsq' : sqAt S' n := h'.1
  have hSlen : S.length = n := SqMat.rows (⟨S, hsq⟩ : SqMat n)
  have hSlen' : S'.length = n := SqMat.rows (⟨S', hsq'⟩ : SqMat n)
  have hSrows : rowsLen n S := rowsLen_of_sqAt hsq
  have hSrows' : rowsLen n S' := rowsLen_of_sqAt hsq'
  have hLr : rowsLen n (lowerList sp') := lowerList_rowsLen sp'
  have hlen : (lowerList sp').length = revAt sp' :=
    lowerList_length S' sp' h'
  have hfin := forcing S sp h (lowerList sp') hLr ?_
  · rw [hlen] at hfin
    exact hfin
  · intro cs hcs hoff
    have hx : (combo n cs (lowerList sp')).length = n :=
      length_combo n cs (lowerList sp') hLr
    have hA := lowerList_strict S' sp' h' cs (hcs.trans hlen) hoff
    have hB := psd_all (siteDatum S' S) spd hd hpd
      (combo n cs (lowerList sp')) hx
    have hsite := quadForm_site
      (hSlen'.trans hx.symm) (rowsLen_cast hx.symm hSrows')
      (hSlen.trans hx.symm) (rowsLen_cast hx.symm hSrows)
    have hle : BPair.unit ≤ dotN (combo n cs (lowerList sp'))
        (matVec S' (combo n cs (lowerList sp')))
        + (dotN (combo n cs (lowerList sp'))
            (matVec S (combo n cs (lowerList sp')))).swap :=
      ground.leB_congr_right hsite (ground.leB_of_not_lt hB)
    have hle2 : dotN (combo n cs (lowerList sp'))
        (matVec S (combo n cs (lowerList sp')))
        ≤ dotN (combo n cs (lowerList sp'))
          (matVec S' (combo n cs (lowerList sp'))) :=
      ground.leB_of_unit_add hle
    exact ltUnitOfLeB hle2 hA

/-- `lem:inertia`'s family transport at the forcing clause: a family
map whose quadratic form crosses the datum to a block's own prices
the block's count at or below the datum's — the block split's lower
list carried through the map is a strict family at the datum
(`rev_compress` and the two corner reads its instances). -/
theorem rev_family {n m : Nat} (S P T : Mat)
    (hTl : T.length = n)
    (hq : ∀ v : List BPair, v.length = m →
      (dotN (matVec T v) (matVec S (matVec T v))).oneValue
        (dotN v (matVec P v)))
    (spP : Split m) (hp : splitRead P spP)
    (spS : Split n) (hS : splitRead S spS) :
    revAt spP ≤ revAt spS := by
  have hLw : rowsLen m (lowerList spP) := lowerList_rowsLen spP
  have hLr : rowsLen n ((lowerList spP).map (matVec T)) :=
    rowsLen_map (matVec T) n (lowerList spP)
      (fun x _ => (matVec_length T x).trans hTl)
  have hlen : ((lowerList spP).map (matVec T)).length = revAt spP := by
    rw [ground.length_map]
    exact lowerList_length P spP hp
  have hfin := forcing S spS hS ((lowerList spP).map (matVec T)) hLr ?_
  · rw [hlen] at hfin
    exact hfin
  · intro cs hcs hoff
    have hx : (combo m cs (lowerList spP)).length = m :=
      length_combo m cs (lowerList spP) hLw
    have hmv : poly.oneValue (matVec T (combo m cs (lowerList spP)))
        (combo n cs ((lowerList spP).map (matVec T))) := by
      have h0 := elim.matVec_combo T m cs (lowerList spP) hLw
      rw [hTl] at h0
      exact h0
    refine BPair.lt_congr
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (quad_congr S _ _ (poly.oneValue_symm hmv))
          (hq (combo m cs (lowerList spP)) hx)))
      (BPair.oneValue_refl BPair.unit)
      (lowerList_strict P spP hp cs (hcs.trans hlen) hoff)

/-- The compression comparison: a congruence image's reversal count
sits at or below the datum's, at every rectangular carrier. -/
theorem rev_compress {n m : Nat} (S P : Mat)
    (hS : sqAt S n) (hP : P.length = n) (hPr : rowsLen m P)
    (spc : Split m)
    (hc : splitRead (matMul (transposeM P) (matMul S P)) spc)
    (sp : Split n) (h : splitRead S sp) :
    revAt spc ≤ revAt sp := by
  exact rev_family S (matMul (transposeM P) (matMul S P)) P hP
    (fun v hv => congQuad S P n m hS hPr hP v hv) spc hc sp h

/-- The withdrawn diagonal's block list: each order-one lower
entry withdrawn to the vacant read, every further block kept —
the positive part at a split whose lower units sit at order-one
blocks, the crossing's stated presentation. -/
def posBlocks : List SBlock → List SBlock
  | [] => []
  | .one a :: bs =>
      (if a < BPair.unit then .one BPair.unit else .one a) :: posBlocks bs
  | .two a b c :: bs => .two a b c :: posBlocks bs

/-- The withdrawal's head read at an order-one lower entry: the
entry moves to the vacant read with the tail's fold its own. -/
theorem posBlocks_cons_lt {a : BPair} (bs : List SBlock)
    (h : a < BPair.unit) :
    posBlocks (SBlock.one a :: bs)
      = SBlock.one BPair.unit :: posBlocks bs := by
  show (if a < BPair.unit then SBlock.one BPair.unit
      else SBlock.one a) :: posBlocks bs = _
  rw [if_pos h]

/-- The withdrawal's head read at an order-one upper entry: the
entry rides kept with the tail's fold its own. -/
theorem posBlocks_cons_ge {a : BPair} (bs : List SBlock)
    (h : ¬ a < BPair.unit) :
    posBlocks (SBlock.one a :: bs)
      = SBlock.one a :: posBlocks bs := by
  show (if a < BPair.unit then SBlock.one BPair.unit
      else SBlock.one a) :: posBlocks bs = _
  rw [if_neg h]

/-- The withdrawn diagonal dominates the block diagonal at the
peeled form: each order-one lower entry's read sits at or below the
vacant read's at every coordinate square, every further block's
read its own. -/
private theorem bQuad_posBlocks : ∀ (bs : List SBlock) (k : Nat)
    (c : List BPair), bQuad bs k c ≤ bQuad (posBlocks bs) k c
  | [], _, _ => ground.leB_refl _
  | SBlock.one _ :: _, _, [] => ground.leB_refl _
  | SBlock.one a :: bs, k, x :: c' => by
    have hrec := bQuad_posBlocks bs k c'
    have hL := peel_one a bs k x c'
    match (inferInstance : Decidable (a < BPair.unit)) with
    | isTrue hg =>
      have hpos := posBlocks_cons_lt bs hg
      rw [hpos]
      have hR := peel_one BPair.unit (posBlocks bs) k x c'
      have hLe : x * (a * x) = x * x * a := by
        rw [BPair.mul_comm a x, ← BPair.mul_assoc]
      have hRu : (x * (BPair.unit * x)).oneValue BPair.unit :=
        BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl x) (BPair.unit_mul x))
          (BPair.mul_unit x)
      have hhead : x * (a * x) ≤ x * (BPair.unit * x) :=
        ground.leB_congr (BPair.oneValue_of_eq hLe.symm)
          (BPair.oneValue_trans (BPair.mul_unit (x * x))
            (BPair.oneValue_symm hRu))
          (ground.leB_mulR (ground.unitLeSq x) (ground.leB_of_lt hg))
      exact ground.leB_congr (BPair.oneValue_symm hL)
        (BPair.oneValue_symm hR) (ground.leB_add hhead hrec)
    | isFalse hg =>
      have hpos := posBlocks_cons_ge bs hg
      rw [hpos]
      have hR := peel_one a (posBlocks bs) k x c'
      exact ground.leB_congr (BPair.oneValue_symm hL)
        (BPair.oneValue_symm hR)
        (ground.leB_add (ground.leB_refl (x * (a * x))) hrec)
  | SBlock.two _ _ _ :: _, _, [] => ground.leB_refl _
  | SBlock.two a b d :: bs, k, [x] =>
    ground.leB_congr (BPair.oneValue_symm (peel_two1 a b d bs k x))
      (BPair.oneValue_symm (peel_two1 a b d (posBlocks bs) k x))
      (ground.leB_refl (x * (a * x)))
  | SBlock.two a b d :: bs, k, x :: y :: c' =>
    ground.leB_congr
      (BPair.oneValue_symm (peel_two a b d bs k x y c'))
      (BPair.oneValue_symm (peel_two a b d (posBlocks bs) k x y c'))
      (ground.leB_add
        (ground.leB_refl (x * (a * x + b * y) + y * (b * x + d * y)))
        (bQuad_posBlocks bs k c'))

/-- The withdrawn diagonal's read: the datum's form at every
vector, cleared at the congruence determinant's square, sits at or
below the withdrawn diagonal's read at the witness's coordinates —
each order-one lower entry's read at or below the vacant read's at
every coordinate square.  At the crossing's stated presentation,
the lower unit at an order-one block, the withdrawn diagonal is
the positive part and the read is the split's rank-one read. -/
theorem split_posPart {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) (v : List BPair) (hv : v.length = n) :
    minor sp.T.val * minor sp.T.val * quadForm S v
      ≤ quadForm (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec sp.Tw.val v) := by
  obtain ⟨hsq, ⟨-, hTTw, -⟩, hcong, -⟩ := h
  have hTrows : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
  have hTwrows : rowsLen n sp.Tw.val := rowsLen_of_sqAt sp.Tw.shape
  have hc : (matVec sp.Tw.val v).length = n :=
    (matVec_length sp.Tw.val v).trans sp.Tw.rows
  have himg : poly.oneValue
      (matVec sp.T.val (matVec sp.Tw.val v))
      (vecScale (minor sp.T.val) v) := by
    refine poly.oneValue_trans
      (matVec_comp sp.T.val sp.Tw.val v n hTwrows hv
        (by rw [sp.Tw.rows]; exact hTrows)) ?_
    refine poly.oneValue_trans (matVec_matOne _ _ v hTTw) ?_
    exact scaleId_act (minor sp.T.val) n v hv
  have hDD := quadScaleVec S (minor sp.T.val) v
    (matVec sp.T.val (matVec sp.Tw.val v)) himg
  have hBQ := congTransport S sp hsq hcong (matVec sp.Tw.val v) hc
  have hstep : quadForm (blockMat sp.blocks sp.kern)
        (matVec sp.Tw.val v)
      ≤ quadForm (blockMat (posBlocks sp.blocks) sp.kern)
        (matVec sp.Tw.val v) :=
    ground.leB_congr
      (BPair.oneValue_symm
        (quadP_read (blockMat sp.blocks sp.kern) (matVec sp.Tw.val v)))
      (BPair.oneValue_symm
        (quadP_read (blockMat (posBlocks sp.blocks) sp.kern)
          (matVec sp.Tw.val v)))
      (bQuad_posBlocks sp.blocks sp.kern (matVec sp.Tw.val v))
  exact ground.leB_congr_left
    (BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.oneValue_symm hDD) hBQ))
    hstep

/-! `lem:inertia`'s consequences paragraph, the general tier's last
two members.  The rescaling invariance is the tex's `rev(qS) =
rev(S)` at a pair `q` strictly above the sum's unit: a split
`(T, D)` of `S` is the split `(T, qD)` of `qS` — the congruence and
its witness untouched, every block scaled entrywise at kept orders,
and every block's own sides and determinant side fixed, the
strictly positive scaling walking each trichotomy branch (the
determinant of a 2×2 block scaling by `q²`, the leading entry by
`q`).  The transport lands as the computed split (`scaleSplit`) with
its read (`scaleSplit_read`, the congruence identity carried by the
scale's passage through the two products and the block diagonal's
own scaling) and its count identity (`scaleSplit_rev`); the
consumable corollary is `rev_scale`, the two-splits exchange at the
scaled datum against the computed split.  The dual forcing clause
(`forcing_upper`) is `forcing`'s joint argument with the roles
exchanged: an independent family reading every combination at or
above the sum's unit joins the split's own lower list, a joint
unit-tail combination forcing the family's coefficients through its
independence and — off the unit on the family's side — exhibiting
the family's combination as the lower list's memberwise swap, whose
form the swap walks unchanged, so the lower list's strict read meets
the family's at-or-above one and the trichotomy refuses; the width
bound then prices `L.length + rev(S) ≤ n`, the upper-bound engine
the addition's second inequality consumes. -/

private theorem colsOne (r : List BPair) : ∀ {M M' : Mat},
    matOneValue M M' →
    poly.oneValue (M.map (fun c => dotN r c)) (M'.map (fun c => dotN r c))
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | c :: _, c' :: _, h =>
    ⟨BPair.oneValue_trans (dotN_read r c)
      (BPair.oneValue_trans (dotP_oneValue_right r c c' h.1)
        (BPair.oneValue_symm (dotN_read r c'))),
     colsOne r h.2⟩

/-! The entrywise scaling's own kit: the shape reads, the scaled
row's pairing, the key-list exchange under the scale, and the
scale's passage through a matrix product on either side. -/

private theorem unitScaleOne (w : BPair) :
    BPair.unit.oneValue ((w * BPair.unit).norm) :=
  BPair.oneValue_symm
    (BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_unit w))

theorem matOne_scaleB (w : BPair) : ∀ {A B : Mat},
    matOneValue A B → matOneValue (matScaleB w A) (matScaleB w B)
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h =>
    ⟨poly.oneValue_scaleP w h.1, matOne_scaleB w h.2⟩

/-- The rescaling keeps the row count. -/
theorem length_scaleB (w : BPair) (M : Mat) :
    (matScaleB w M).length = M.length := ground.length_map _ M

/-- The rescaling keeps the row shape. -/
theorem rowsLen_scaleB (w : BPair) (n : Nat) (M : Mat)
    (h : rowsLen n M) : rowsLen n (matScaleB w M) :=
  elim.rowsLen_mapRows (fun x => (w * x).norm) M n h

/-- The rescaling at a balance weight keeps the square read, the
row count and every row's width the matrix's own. -/
theorem sqAt_scaleB (w : BPair) (o : Nat) (M : Mat)
    (hM : sqAt M o) : sqAt (matScaleB w M) o :=
  elim.sqAt_of ((length_scaleB w M).trans (elim.sqAt_len hM))
    (rowsLen_scaleB w o M (elim.rowsLen_of_sqAt hM))

/-- A weighted row's fold carries the weight out. -/
theorem dotN_scaleRow (w : BPair) (r u : List BPair) :
    (dotN (poly.scaleP w r) u).oneValue (w * dotN r u) :=
  BPair.oneValue_trans (dotN_read _ u)
    (BPair.oneValue_trans (dotP_scaleRow w r u)
      (BPair.mul_congr (BPair.oneValue_refl w)
        (BPair.oneValue_symm (dotN_read r u))))

/-- The contraction at a scaled column list reads the weight's
multiple. -/
theorem dotN_scaleCol (w : BPair) (r u : List BPair) :
    (dotN r (poly.scaleP w u)).oneValue (w * dotN r u) := by
  refine BPair.oneValue_trans (dotN_read r _) ?_
  rw [dotP_comm r (poly.scaleP w u)]
  refine BPair.oneValue_trans (dotP_scaleRow w u r) ?_
  rw [dotP_comm u r]
  exact BPair.mul_congr (BPair.oneValue_refl w)
    (BPair.oneValue_symm (dotN_read r u))

private theorem transposeM_scaleB_pos (w : BPair) (n : Nat) (M : Mat)
    (hM : rowsLen n M) (hpos : 0 < M.length) :
    matOneValue (transposeM (matScaleB w M))
      (matScaleB w (transposeM M)) := by
  have hMs : rowsLen n (matScaleB w M) := rowsLen_scaleB w n M hM
  have hlenS : (matScaleB w M).length = M.length := length_scaleB w M
  have hposS : 0 < (matScaleB w M).length := by rw [hlenS]; exact hpos
  have hTl : (transposeM (matScaleB w M)).length = n :=
    length_transposeM (matScaleB w M) hMs hposS
  have hTl0 : (transposeM M).length = n := length_transposeM M hM hpos
  have hTr : rowsLen (matScaleB w M).length (transposeM (matScaleB w M)) :=
    rowsLen_transposeM (matScaleB w M)
  have hTr0 : rowsLen M.length (transposeM M) := rowsLen_transposeM M
  refine matOne_getAt _ _ (by rw [hTl, length_scaleB, hTl0]) ?_
  intro i hi
  rw [hTl] at hi
  have hrowR : ground.getAt ([] : List BPair)
      (matScaleB w (transposeM M)) i
      = (ground.getAt ([] : List BPair) (transposeM M) i).map
        (fun x => (w * x).norm) :=
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (poly.scaleP w) (transposeM M) i
      (by rw [hTl0]; exact hi)
  have hlenL : (ground.getAt ([] : List BPair)
      (transposeM (matScaleB w M)) i).length = M.length := by
    rw [rowsLen_getAt (transposeM (matScaleB w M)) i hTr
      (by rw [hTl]; exact hi)]
    exact hlenS
  have hlenR0 : (ground.getAt ([] : List BPair) (transposeM M) i).length
      = M.length :=
    rowsLen_getAt (transposeM M) i hTr0 (by rw [hTl0]; exact hi)
  rw [hrowR]
  refine poly.oneValue_of_entries _ _ (by rw [ground.length_map, hlenL, hlenR0]) ?_
  intro q hq
  rw [hlenL] at hq
  rw [getAt_transposeM BPair.unit (matScaleB w M) hMs i q hi
      (by rw [hlenS]; exact hq),
    show matScaleB w M
      = M.map (fun r => r.map (fun x => (w * x).norm)) from rfl,
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (fun r => r.map (fun x => (w * x).norm)) M q hq,
    ground.getAt_map BPair.unit BPair.unit (fun x => (w * x).norm)
      (ground.getAt ([] : List BPair) M q) i
      (by rw [rowsLen_getAt M q hM hq]; exact hi),
    ground.getAt_map BPair.unit BPair.unit (fun x => (w * x).norm)
      (ground.getAt ([] : List BPair) (transposeM M) i) q
      (by rw [hlenR0]; exact hq),
    getAt_transposeM BPair.unit M hM i q hi hq]
  exact BPair.oneValue_refl _

/-- The key-list exchange passes the balance-pair weighting: the
weighted matrix's transpose reads the transpose's weighting, entry
by entry. -/
theorem transposeM_scaleB (w : BPair) (n : Nat) : ∀ M : Mat,
    rowsLen n M →
    matOneValue (transposeM (matScaleB w M)) (matScaleB w (transposeM M))
  | [], _ => trivial
  | r :: t, hM =>
    transposeM_scaleB_pos w n (r :: t) hM (Nat.succ_pos _)

/-- A left factor's rescaling rides out of the product. -/
theorem matMul_scaleL (w : BPair) (A B : Mat) :
    matOneValue (matMul (matScaleB w A) B) (matScaleB w (matMul A B)) := by
  show matOneValue
      ((A.map (poly.scaleP w)).map
        (fun r => (transposeM B).map (fun c => dotN r c)))
      ((A.map (fun r => (transposeM B).map (fun c => dotN r c))).map
        (fun r => r.map (fun x => (w * x).norm)))
  rw [ground.map_map, ground.map_map]
  refine matOne_map _ _ ?_ A
  intro r
  rw [ground.map_map]
  exact poly.oneValue_map _ _ (transposeM B) (fun x _ => (fun c =>
    BPair.oneValue_trans (dotN_scaleRow w r c)
      (BPair.oneValue_symm (BPair.norm_oneValue _))) x)

theorem matMul_scaleR (w : BPair) (n : Nat) (A B : Mat)
    (hB : rowsLen n B) :
    matOneValue (matMul A (matScaleB w B)) (matScaleB w (matMul A B)) := by
  have hT := transposeM_scaleB w n B hB
  show matOneValue
      (A.map (fun r => (transposeM (matScaleB w B)).map
        (fun c => dotN r c)))
      ((A.map (fun r => (transposeM B).map (fun c => dotN r c))).map
        (fun r => r.map (fun x => (w * x).norm)))
  rw [ground.map_map]
  refine matOne_map _ _ ?_ A
  intro r
  rw [ground.map_map]
  refine poly.oneValue_trans (colsOne r hT) ?_
  show poly.oneValue
      (((transposeM B).map (poly.scaleP w)).map
        (fun c => dotN r c))
      ((transposeM B).map (fun c => (w * dotN r c).norm))
  rw [ground.map_map]
  exact poly.oneValue_map _ _ (transposeM B) (fun x _ => (fun c =>
    BPair.oneValue_trans (dotN_scaleCol w r c)
      (BPair.oneValue_symm (BPair.norm_oneValue _))) x)

/-! The scaled blocks: the orders kept (so the split's width read
transports), the block diagonal scaling with the block list, the
determinants scaling by the pair and its square, and every block's
reversal count fixed at a strictly positive scale. -/

/-- A block scaled entrywise, the order kept. -/
private def scaleBlock (w : BPair) : SBlock → SBlock
  | .one a => .one ((w * a).norm)
  | .two a b c => .two ((w * a).norm) ((w * b).norm) ((w * c).norm)

private theorem scaleBlock_order (w : BPair) : ∀ b : SBlock,
    (scaleBlock w b).order = b.order
  | .one _ => rfl
  | .two _ _ _ => rfl

private theorem widthOf_scale (w : BPair) : ∀ (bs : List SBlock) (k : Nat),
    widthOf (bs.map (scaleBlock w)) k = widthOf bs k
  | [], _ => rfl
  | b :: t, k => by
    show widthOf (t.map (scaleBlock w)) (k + (scaleBlock w b).order)
      = widthOf t (k + b.order)
    rw [scaleBlock_order w b, widthOf_scale w t (k + b.order)]

private theorem replScale (w : BPair) : ∀ k : Nat,
    poly.oneValue (List.replicate k BPair.unit)
      (poly.scaleP w (List.replicate k BPair.unit))
  | 0 => trivial
  | k + 1 => ⟨unitScaleOne w, replScale w k⟩

private theorem matOne_consScale (w c : BPair)
    (hc : c.oneValue ((w * c).norm)) : ∀ {A B : Mat},
    matOneValue A (matScaleB w B) →
    matOneValue (A.map (fun r => c :: r))
      (matScaleB w (B.map (fun r => c :: r)))
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h =>
    ⟨⟨hc, h.1⟩, matOne_consScale w c hc h.2⟩

private theorem matOne_cons2Scale (w c c' : BPair)
    (hc : c.oneValue ((w * c).norm))
    (hc' : c'.oneValue ((w * c').norm)) : ∀ {A B : Mat},
    matOneValue A (matScaleB w B) →
    matOneValue (A.map (fun r => c :: c' :: r))
      (matScaleB w (B.map (fun r => c :: c' :: r)))
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h =>
    ⟨⟨hc, hc', h.1⟩, matOne_cons2Scale w c c' hc hc' h.2⟩

private theorem blockMat_scale (w : BPair) : ∀ (bs : List SBlock) (k : Nat),
    matOneValue (blockMat (bs.map (scaleBlock w)) k)
      (matScaleB w (blockMat bs k))
  | [], k => by
    show matOneValue
      ((List.range k).map (fun _ => List.replicate k BPair.unit))
      (((List.range k).map (fun _ => List.replicate k BPair.unit)).map
        (poly.scaleP w))
    rw [ground.map_map]
    exact matOne_map _ _ (fun _ => replScale w k) (List.range k)
  | .one a :: bs, k => by
    refine ⟨?_, matOne_consScale w BPair.unit (unitScaleOne w)
      (blockMat_scale w bs k)⟩
    show poly.oneValue
      ((w * a).norm
        :: List.replicate (widthOf (bs.map (scaleBlock w)) k) BPair.unit)
      ((w * a).norm
        :: (List.replicate (widthOf bs k) BPair.unit).map
            (fun x => (w * x).norm))
    rw [widthOf_scale w bs k]
    exact ⟨BPair.oneValue_refl _, replScale w (widthOf bs k)⟩
  | .two a b c :: bs, k => by
    refine ⟨?_, ?_, matOne_cons2Scale w BPair.unit BPair.unit
      (unitScaleOne w) (unitScaleOne w) (blockMat_scale w bs k)⟩
    · show poly.oneValue
        ((w * a).norm :: (w * b).norm
          :: List.replicate (widthOf (bs.map (scaleBlock w)) k) BPair.unit)
        ((w * a).norm :: (w * b).norm
          :: (List.replicate (widthOf bs k) BPair.unit).map
              (fun x => (w * x).norm))
      rw [widthOf_scale w bs k]
      exact ⟨BPair.oneValue_refl _, BPair.oneValue_refl _,
        replScale w (widthOf bs k)⟩
    · show poly.oneValue
        ((w * b).norm :: (w * c).norm
          :: List.replicate (widthOf (bs.map (scaleBlock w)) k) BPair.unit)
        ((w * b).norm :: (w * c).norm
          :: (List.replicate (widthOf bs k) BPair.unit).map
              (fun x => (w * x).norm))
      rw [widthOf_scale w bs k]
      exact ⟨BPair.oneValue_refl _, BPair.oneValue_refl _,
        replScale w (widthOf bs k)⟩

private theorem det_scale_two (w a b c : BPair) :
    ((SBlock.two ((w * a).norm) ((w * b).norm) ((w * c).norm)).det).oneValue
      (w * w * (SBlock.two a b c).det) := by
  refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.mul_congr (BPair.norm_oneValue _) (BPair.norm_oneValue _))
      (ground.swap_congr
        (BPair.mul_congr (BPair.norm_oneValue _)
          (BPair.norm_oneValue _)))) ?_
  rw [BPair.mul_mul_mul_comm w a w c, BPair.mul_mul_mul_comm w b w b,
    ← ground.BPair.mul_swap (w * w) (b * b),
    ← BPair.left_distrib]
  exact BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (BPair.norm_oneValue _))

private theorem rev_two_detEq {a b d : BPair}
    (hD : ((SBlock.two a b d).det).oneValue BPair.unit) :
    (SBlock.two a b d).rev = 0 := by
  match hs : ((SBlock.two a b d).det).side with
  | Trich.lt g hg =>
    exact absurd hD (ground.offOfLtUnit (ground.ltUnitOfSide ⟨g, hg⟩))
  | Trich.eq _ =>
    show (match ((SBlock.two a b d).det).side with
      | Trich.lt _ _ => 1
      | Trich.eq _ => 0
      | Trich.gt _ _ =>
        match a.side with
        | Trich.lt _ _ => 2
        | Trich.eq _ => 0
        | Trich.gt _ _ => 0) = 0
    rw [hs]
  | Trich.gt g hg =>
    exact absurd hD (ground.offOfUnitLt (unitLtOfSide ⟨g, hg⟩))

private theorem normScaleLtUnit (w : BPair) (hw : BPair.unit < w) (x : BPair)
    (h : x < BPair.unit) : (w * x).norm < BPair.unit :=
  BPair.lt_congr (BPair.oneValue_symm (BPair.norm_oneValue _))
    (BPair.oneValue_refl BPair.unit) (mulNegPos hw h)

private theorem scaleLeUnit (w : BPair) (hw : BPair.unit < w) (x : BPair)
    (h : BPair.unit ≤ x) : BPair.unit ≤ (w * x).norm :=
  ground.leB_congr_right (BPair.oneValue_symm (BPair.norm_oneValue _))
    (unitLeMul (ground.leB_of_lt hw) h)

private theorem rev_scale_one (w : BPair) (hw : BPair.unit < w) (a : BPair) :
    (SBlock.one ((w * a).norm)).rev = (SBlock.one a).rev := by
  cases (inferInstance : Decidable (a < BPair.unit)) with
  | isTrue h =>
    rw [rev_one_lt (normScaleLtUnit w hw a h), rev_one_lt h]
  | isFalse h =>
    have hle : BPair.unit ≤ a := ground.leB_of_not_lt h
    rw [rev_one_le (scaleLeUnit w hw a hle), rev_one_le hle]

private theorem rev_scale_two (w : BPair) (hw : BPair.unit < w)
    (a b c : BPair) :
    (SBlock.two ((w * a).norm) ((w * b).norm) ((w * c).norm)).rev
      = (SBlock.two a b c).rev := by
  have hww : BPair.unit < w * w := unitLtMul hw hw
  have hd := det_scale_two w a b c
  cases (inferInstance :
      Decidable ((SBlock.two a b c).det < BPair.unit)) with
  | isTrue hlt =>
    rw [rev_two_detLt
        (BPair.lt_congr (BPair.oneValue_symm hd)
          (BPair.oneValue_refl BPair.unit) (mulNegPos hww hlt)),
      rev_two_detLt hlt]
  | isFalse hnlt =>
    have hle : BPair.unit ≤ (SBlock.two a b c).det :=
      ground.leB_of_not_lt hnlt
    cases (inferInstance :
        Decidable (((SBlock.two a b c).det).oneValue BPair.unit)) with
    | isTrue heq =>
      have hd' : ((SBlock.two ((w * a).norm) ((w * b).norm)
          ((w * c).norm)).det).oneValue BPair.unit :=
        BPair.oneValue_trans hd
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl (w * w)) heq)
            (BPair.mul_unit (w * w)))
      rw [rev_two_detEq hd', rev_two_detEq heq]
    | isFalse hne =>
      have hlt : BPair.unit < (SBlock.two a b c).det := ground.ltOfLeOff hle hne
      have hlt' : BPair.unit < (SBlock.two ((w * a).norm) ((w * b).norm)
          ((w * c).norm)).det :=
        BPair.lt_congr (BPair.oneValue_refl BPair.unit)
          (BPair.oneValue_symm hd) (unitLtMul hww hlt)
      cases (inferInstance : Decidable (a < BPair.unit)) with
      | isTrue ha =>
        rw [rev_two_cols hlt' (normScaleLtUnit w hw a ha), rev_two_cols hlt ha]
      | isFalse hna =>
        have hale : BPair.unit ≤ a := ground.leB_of_not_lt hna
        rw [rev_two_nil (ground.leB_of_lt hlt') (scaleLeUnit w hw a hale),
          rev_two_nil hle hale]

private theorem rev_scale_block (w : BPair) (hw : BPair.unit < w) :
    ∀ b : SBlock, (scaleBlock w b).rev = b.rev
  | .one a => rev_scale_one w hw a
  | .two a b c => rev_scale_two w hw a b c

private theorem revFold_scale (w : BPair) (hw : BPair.unit < w) :
    ∀ (bs : List SBlock) (m : Nat),
      (bs.map (scaleBlock w)).foldl (fun z b => z + b.rev) m
        = bs.foldl (fun z b => z + b.rev) m
  | [], _ => rfl
  | b :: t, m => by
    show (t.map (scaleBlock w)).foldl (fun z y => z + y.rev)
        (m + (scaleBlock w b).rev)
      = t.foldl (fun z y => z + y.rev) (m + b.rev)
    rw [rev_scale_block w hw b, revFold_scale w hw t (m + b.rev)]

private theorem detOff_scale (w : BPair) (hw : ¬ w.oneValue BPair.unit) :
    ∀ b : SBlock, ¬ (b.det).oneValue BPair.unit →
      ¬ ((scaleBlock w b).det).oneValue BPair.unit
  | .one a, h => fun hs =>
    ground.mulOffUnit hw h
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.norm_oneValue (w * a))) hs)
  | .two a b c, h => fun hs =>
    ground.mulOffUnit (ground.offOfUnitLt (ground.sq_pos hw)) h
      (BPair.oneValue_trans
        (BPair.oneValue_symm (det_scale_two w a b c)) hs)

private theorem allDetScale (w : BPair) (hw : ¬ w.oneValue BPair.unit) :
    ∀ bs : List SBlock,
      (bs.all (fun b => !(decide (b.det.oneValue BPair.unit)))) = true →
      ((bs.map (scaleBlock w)).all
        (fun b => !(decide (b.det.oneValue BPair.unit)))) = true
  | [], _ => rfl
  | b :: t, h =>
    ground.andIntroB
      (congrArg Bool.not (decide_eq_false (detOff_scale w hw b
        (ground.notOfBang ((ground.andSplitB h).1)))))
      (allDetScale w hw t ((ground.andSplitB h).2))

/-- The scaled split: the congruence and its invertibility witness
untouched, the blocks scaled entrywise at kept orders, and the
kernel block as it stands — the tex's `(T, qD)` at the split
`(T, D)`, the split's width read transported by the kept orders. -/
def scaleSplit {n : Nat} (w : BPair) (sp : Split n) : Split n :=
  { T := sp.T, Tw := sp.Tw, blocks := sp.blocks.map (scaleBlock w),
    kern := sp.kern,
    width := by rw [widthOf_scale w sp.blocks sp.kern]; exact sp.width }

/-- The rescaling's transport (`lem:inertia`'s consequences): at a
pair strictly above the sum's unit the scaled split reads the scaled
datum — the datum's square shape and the certificate's own
conjuncts unchanged, the congruence identity carried by the scale's
passage through the two products against the block diagonal's own
scaling, and each scaled block's determinant off equal members at
the product of two off-unit data. -/
theorem scaleSplit_read {n : Nat} (w : BPair)
    (hw : ¬ w.oneValue BPair.unit)
    (S : Mat) (sp : Split n) (h : splitRead S sp) :
    splitRead (matScaleB w S) (scaleSplit w sp) := by
  obtain ⟨hsq, ⟨hdetT, hp1, hp2⟩, hcong, hns⟩ := h
  have hSrows : rowsLen n S := rowsLen_of_sqAt hsq
  have hSlen : S.length = n := sqAt_len hsq
  have hTrows : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
  have hTlen : sp.T.val.length = n := sp.T.rows
  have hTt : (transposeM sp.T.val).length = n :=
    transposeLen sp.T.val hTrows hTlen
  have hXrows : rowsLen n (matMul S sp.T.val) :=
    rowsLen_cast hTt (rowsLen_matMul S sp.T.val)
  have hXlen : (matMul S sp.T.val).length = n := by
    show (S.map (fun r => (transposeM sp.T.val).map
      (fun cc => dotN r cc))).length = n
    rw [ground.length_map]
    exact hSlen
  have hYrows : rowsLen n (matMul (matScaleB w S) sp.T.val) :=
    rowsLen_cast hTt (rowsLen_matMul (matScaleB w S) sp.T.val)
  have hYlen : (matMul (matScaleB w S) sp.T.val).length = n := by
    show ((matScaleB w S).map (fun r => (transposeM sp.T.val).map
      (fun cc => dotN r cc))).length = n
    rw [ground.length_map, length_scaleB]
    exact hSlen
  refine ⟨sqAt_of (by rw [length_scaleB]; exact hSlen)
      (rowsLen_scaleB w n S hSrows), ⟨hdetT, hp1, hp2⟩, ?_, ?_⟩
  · show matOneValue
      (matMul (transposeM sp.T.val) (matMul (matScaleB w S) sp.T.val))
      (blockMat (sp.blocks.map (scaleBlock w)) sp.kern)
    refine matOne_trans (elim.matMul_congrR_of (transposeM sp.T.val) _ _
      (transposeM_congrM n _ _ hYrows
        (rowsLen_scaleB w n (matMul S sp.T.val) hXrows)
        (by rw [hYlen, length_scaleB, hXlen])
        (matMul_scaleL w S sp.T.val))) ?_
    refine matOne_trans
      (matMul_scaleR w n (transposeM sp.T.val) (matMul S sp.T.val)
        hXrows) ?_
    exact matOne_trans (matOne_scaleB w hcong)
      (matOne_symm (blockMat_scale w sp.blocks sp.kern))
  · exact allDetScale w hw sp.blocks hns

/-- The scaled split's reversal count is the split's own: a strictly
positive scaling walks each block's trichotomy branch — the
order-1 entry's side, and the 2×2 block's determinant side at the
squared scale with the leading entry's side beside it — so the
blocks' fold is unchanged summand by summand. -/
theorem scaleSplit_rev {n : Nat} (w : BPair) (hw : BPair.unit < w)
    (sp : Split n) : revAt (scaleSplit w sp) = revAt sp :=
  revFold_scale w hw sp.blocks 0

/-- The rescaling invariance (`lem:inertia`'s consequences): every
split of a positively rescaled datum reads the datum's own reversal
count, the scaled split the exchange's second witness. -/
theorem rev_scale {n : Nat} (w : BPair) (hw : BPair.unit < w)
    (S : Mat) (sp sp' : Split n) (h : splitRead S sp)
    (h' : splitRead (matScaleB w S) sp') : revAt sp' = revAt sp := by
  rw [rev_exchange (matScaleB w S) sp' (scaleSplit w sp) h'
    (scaleSplit_read w (ground.offOfUnitLt hw) S sp h)]
  exact scaleSplit_rev w hw sp

/-- A sum at the unit tail whose second summand reads it there
reads it on the first. -/
theorem unitTailAddRight : ∀ (a b : List BPair),
    a.length = b.length → poly.unitTail b →
    poly.unitTail (vecAdd a b) → poly.unitTail a
  | [], [], _, _, _ => trivial
  | [], _ :: _, hl, _, _ => nomatch hl
  | _ :: _, [], hl, _, _ => nomatch hl
  | x :: a, _ :: b, hl, hb, hab =>
    ⟨BPair.oneValue_trans (BPair.oneValue_symm (BPair.add_unit x))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl x)
          (BPair.oneValue_symm hb.1))
        hab.1),
     unitTailAddRight a b (Nat.succ.inj hl) hb.2 hab.2⟩

/-- The dual forcing clause (`lem:inertia`'s general tier): an
independent family at the split's own order pricing every
combination of its members at or above the sum's unit counts,
joined to the reversal count, at or below the order — the split's
own lower list the joint's second half. -/
theorem forcing_upper {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) (L : Mat) (hL : rowsLen n L)
    (hind : ∀ cs : List BPair, cs.length = L.length →
      poly.unitTail (combo n cs L) → poly.unitTail cs)
    (hside : ∀ cs : List BPair, cs.length = L.length →
      ¬ (dotN (combo n cs L) (matVec S (combo n cs L)) < BPair.unit)) :
    L.length + revAt sp ≤ n := by
  have hW : rowsLen n (lowerList sp) := lowerList_rowsLen sp
  have hlow : (lowerList sp).length = revAt sp := lowerList_length S sp h
  have hLW : rowsLen n (L ++ lowerList sp) := rowsLen_append n hL hW
  have hall : ∀ cs : List BPair,
      cs.length = (L ++ lowerList sp).length →
      poly.unitTail (combo n cs (L ++ lowerList sp)) →
      poly.unitTail cs := by
    intro cs hcs hu
    have hlen : cs.length = L.length + (lowerList sp).length := by
      rw [hcs, ground.length_append]
    obtain ⟨csL, csW, rfl, hlL⟩ :=
      listSplit cs L.length (by rw [hlen]; exact Nat.le_add_right _ _)
    have h1 : csL.length + csW.length
        = L.length + (lowerList sp).length := by
      rw [← ground.length_append csL csW]
      exact hlen
    rw [hlL] at h1
    have hlW : csW.length = (lowerList sp).length :=
      ground.addCancelL L.length h1
    have hvl : (combo n csL L).length = n := length_combo n csL L hL
    have hwl : (combo n csW (lowerList sp)).length = n :=
      length_combo n csW (lowerList sp) hW
    have hcomb : poly.oneValue
        (combo n (csL ++ csW) (L ++ lowerList sp))
        (vecAdd (combo n csL L) (combo n csW (lowerList sp))) :=
      combo_append n csL L csW (lowerList sp) hlL hL hW
    have huv : poly.unitTail
        (vecAdd (combo n csL L) (combo n csW (lowerList sp))) :=
      poly.unitTail_oneValue_right hu hcomb
    cases (inferInstance : Decidable (poly.unitTail csW)) with
    | isTrue hcase =>
      refine unitTail_append (hind csL hlL ?_) hcase
      exact unitTailAddRight _ _ (by rw [hvl, hwl])
        (unitTail_combo_of n csW (lowerList sp) hcase) huv
    | isFalse hcase =>
      have hsw : poly.oneValue (combo n csW (lowerList sp))
          ((combo n csL L).map BPair.swap) :=
        swap_of_null_add _ _ (by rw [hvl, hwl]) huv
      have hcg := quad_congr S (combo n csW (lowerList sp))
        ((combo n csL L).map BPair.swap) hsw
      rw [dotN_matVec_swapMap S (combo n csL L)] at hcg
      exact absurd
        (BPair.lt_congr hcg (BPair.oneValue_refl BPair.unit)
          (lowerList_strict S sp h csW (hlW.trans hlow) hcase))
        (hside csL hlL)
  have hb : (L ++ lowerList sp).length ≤ n :=
    indep_bound n (L ++ lowerList sp) hLW
      (indep_intro n (L ++ lowerList sp) hLW hall)
  rw [ground.length_append, hlow] at hb
  exact hb

/-! `lem:inertia`'s addition at a nonsingular principal pivot, the
count kit's last general member.  The datum is the assembled
`S = [[P, B], [Bᵀ, Q]]` (`blockJoin`) at a nonsingular principal
pivot `P`, and the deflation is `lem:cellcount`'s cleared site datum
`(det P)² Q − (det P) Bᵀ C` (`deflMat`) at the solve witness
`P C ~ (det P) B` — the tex's `S_P` cleared by the pivot's adjugate,
the positive square riding both terms so the count is fixed
regardless of the determinant's side.  The addition
`rev(S) = rev(P) + rev(S_P)` runs on the module's own forcing tier
at two families and one lift: the padded family
`x ↦ (x, 0)` (`padM`) and the deflation's lift
`w ↦ (C w, −(det P) w)` (`liftM`), each the action of a computed
rectangular matrix so the combination read is `elim.matVec_combo`
itself.  The lift's whole content is the solve: the pivot rows of
`S` at a lifted vector read the unit family (`P C w − (det P) B w`),
so the two cross pairings against a padded vector vanish — the
second through the pivot's symmetry and the pairing's transpose
adjoint at `B` — and the lifted quadratic form is the deflation's
own (`quadSplit`, the two forms' join at every pair of arguments).
The `≥` direction joins the two splits' lower lists through the two
maps and prices them at `forcing`; the `≤` direction joins the two
complement lists and prices them at `forcing_upper`, the lift's
bottom half exhibiting the deflation's coefficients through the
determinant's own cancellation (`hPnz`) before the pivot's
independence closes the rest.  The complement lengths arrive as
joins, so the closing arithmetic is `ground.leCancelR` and
nothing subtractive. -/

/-- The row-against-column fold splits over a join at matched first
halves. -/
theorem dotN_app : ∀ (r s a b : List BPair),
    r.length = a.length →
    (dotN (r ++ s) (a ++ b)).oneValue (dotN r a + dotN s b)
  | [], s, [], b, _ => BPair.oneValue_symm (BPair.unit_add (dotN s b))
  | [], _, _ :: _, _, hl => nomatch hl
  | _ :: _, _, [], _, hl => nomatch hl
  | c :: r, s, d :: a, b, hl => by
    show (if c.isUnitRep || d.isUnitRep then dotN (r ++ s) (a ++ b)
        else (c * d + dotN (r ++ s) (a ++ b)).norm).oneValue
      ((if c.isUnitRep || d.isUnitRep then dotN r a
        else (c * d + dotN r a).norm) + dotN s b)
    cases c.isUnitRep || d.isUnitRep with
    | true => exact dotN_app r s a b (Nat.succ.inj hl)
    | false =>
      refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (c * d))
          (dotN_app r s a b (Nat.succ.inj hl))) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.add_assoc (c * d) (dotN r a) (dotN s b)).symm) ?_
      exact BPair.add_congr
        (BPair.oneValue_symm (BPair.norm_oneValue _))
        (BPair.oneValue_refl (dotN s b))

private theorem zipApp_len : ∀ (A C : Mat) (a b : List BPair),
    (List.zipWith (· ++ ·) A C).length
      = (vecAdd (matVec A a) (matVec C b)).length
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: A, _ :: C, a, b => congrArg Nat.succ (zipApp_len A C a b)

/-- The weighted matrix's action is the action's own weighting. -/
theorem matVec_scaleB (c : BPair) (M : Mat) (u : List BPair) :
    poly.oneValue (matVec (matScaleB c M) u)
      (vecScale c (matVec M u)) := by
  show poly.oneValue
      ((M.map (poly.scaleP c)).map
        (fun r => dotN r u))
      ((M.map (fun r => dotN r u)).map (fun x => c * x))
  rw [ground.map_map, ground.map_map]
  exact poly.oneValue_map _ _ M (fun x _ => (fun r => dotN_scaleRow c r u) x)

/-- The rescaled datum's form at a pair weight: the weight
multiplies the unscaled read. -/
theorem quadForm_scaleB (c : BPair) (M : Mat) (u : List BPair) :
    (quadForm (matScaleB c M) u).oneValue (c * quadForm M u) :=
  BPair.oneValue_trans
    (elim.dotN_congrR u _ _ (matVec_scaleB c M u))
    (elim.dotN_scaleV c u (matVec M u))

/-- A unit-tail vector prices the form at the sum's unit. -/
theorem quadNull (S : Mat) (u : List BPair)
    (h : poly.unitTail u) : (dotN u (matVec S u)).oneValue BPair.unit :=
  BPair.oneValue_trans (dotN_read u (matVec S u))
    (dotP_null_tail_left u (matVec S u) h)

/-- The quadratic form at a memberwise sum: the two forms and the
two cross pairings. -/
theorem quadAdd (S : Mat) (n : Nat) (hS : rowsLen n S)
    (hSl : S.length = n) (u v : List BPair)
    (hu : u.length = n) (hv : v.length = n) :
    (dotN (vecAdd u v) (matVec S (vecAdd u v))).oneValue
      ((dotN u (matVec S u) + dotN u (matVec S v))
        + (dotN v (matVec S u) + dotN v (matVec S v))) := by
  have hSu : (matVec S u).length = n := (matVec_length S u).trans hSl
  have hSv : (matVec S v).length = n := (matVec_length S v).trans hSl
  have hlen : (vecAdd (matVec S u) (matVec S v)).length = n :=
    length_vecAdd _ _ n hSu hSv
  refine BPair.oneValue_trans
    (dotN_congrR (vecAdd u v) _ _ (matVec_vecAdd S n hS u v hu hv)) ?_
  refine BPair.oneValue_trans
    (dotN_addRow u v _ (hu.trans hlen.symm) (hv.trans hlen.symm)) ?_
  exact BPair.add_congr
    (elim.dotN_addRow_right u (matVec S u) (matVec S v)
      (hSu.trans hu.symm) (hSv.trans hu.symm))
    (elim.dotN_addRow_right v (matVec S u) (matVec S v)
      (hSu.trans hv.symm) (hSv.trans hv.symm))

/-- The assembled datum at a nonsingular principal pivot: the pivot
block, the coupling slab and its exchange, and the trailing block —
`lem:inertia`'s addition clause reads its count at this join. -/
def blockJoin (P B Q : Mat) : Mat :=
  List.zipWith (· ++ ·) P B
    ++ List.zipWith (· ++ ·) (transposeM B) Q

/-- The join's row count: the two slabs' rows appended. -/
theorem length_blockJoin (P B Q : Mat) (a b : Nat)
    (hP : P.length = a) (hB : B.length = a)
    (hBt : (transposeM B).length = b) (hQ : Q.length = b) :
    (blockJoin P B Q).length = a + b := by
  show (List.zipWith (· ++ ·) P B
    ++ List.zipWith (· ++ ·) (transposeM B) Q).length = a + b
  rw [ground.length_append,
    ground.length_zipWith (· ++ ·) P B a hP hB,
    ground.length_zipWith (· ++ ·) (transposeM B) Q b hBt hQ]

/-- The join's row widths: each slab's rows at the joined width. -/
theorem rowsLen_blockJoin (P B Q : Mat) (a b : Nat)
    (hP : rowsLen a P) (hB : rowsLen b B)
    (hBt : rowsLen a (transposeM B)) (hQ : rowsLen b Q) :
    rowsLen (a + b) (blockJoin P B Q) :=
  rowsLen_append (a + b) (elim.rowsLen_rowJoin a b hP hB)
    (elim.rowsLen_rowJoin a b hBt hQ)

/-- The selected blocks' join at a symmetric square matrix: the
selection at the joined key list reads the join of the pivot block,
the coupling block and the trailing block, the lower coupling the
upper's transpose at the symmetry. -/
theorem selM_blockJoin (M : Mat) (idx cpl : List Nat) (o : Nat)
    (hMsq : sqAt M o) (hMsym : matOneValue (transposeM M) M)
    (hk0 : 0 < idx.length)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (hcpl : (cpl.all (fun j => Nat.blt j o)) = true) :
    matOneValue (selM (idx ++ cpl) (idx ++ cpl) M)
      (blockJoin (selM idx idx M) (selM idx cpl M) (selM cpl cpl M)) := by
  have hBl : (selM idx cpl M).length = idx.length := length_selM _ _ _
  have hCvr : rowsLen idx.length (selM cpl idx M) := rowsLen_selM _ _ _
  have hTBr : rowsLen idx.length (transposeM (selM idx cpl M)) :=
    rowsLen_cast hBl (rowsLen_transposeM _)
  have hCT : matOneValue (selM cpl idx M) (transposeM (selM idx cpl M)) :=
    matOne_symm (transposeM_selM idx cpl M o hMsq hMsym hk0 hidx hcpl)
  rw [selM_append idx cpl]
  show matOneValue
    (List.zipWith (· ++ ·) (selM idx idx M) (selM idx cpl M)
      ++ List.zipWith (· ++ ·) (selM cpl idx M) (selM cpl cpl M))
    (List.zipWith (· ++ ·) (selM idx idx M) (selM idx cpl M)
      ++ List.zipWith (· ++ ·) (transposeM (selM idx cpl M))
        (selM cpl cpl M))
  exact matOne_append _ _ _ _ (matOne_refl _)
    (matOne_rowJoin _ _ _ _ hCvr hTBr hCT (matOne_refl _))

/-- The selected blocks' join is square at the joined count. -/
theorem sqAt_selM_blockJoin (M : Mat) (idx cpl : List Nat)
    (hk0 : 0 < idx.length) :
    sqAt (blockJoin (selM idx idx M) (selM idx cpl M) (selM cpl cpl M))
      (idx.length + cpl.length) := by
  have hBl : (selM idx cpl M).length = idx.length := length_selM _ _ _
  have hBr : rowsLen cpl.length (selM idx cpl M) := rowsLen_selM _ _ _
  have hTBl : (transposeM (selM idx cpl M)).length = cpl.length :=
    length_transposeM _ hBr (by rw [hBl]; exact hk0)
  have hTBr : rowsLen idx.length (transposeM (selM idx cpl M)) :=
    rowsLen_cast hBl (rowsLen_transposeM _)
  exact sqAt_of
    (length_blockJoin _ _ _ idx.length cpl.length (length_selM _ _ _) hBl
      hTBl (length_selM _ _ _))
    (rowsLen_blockJoin _ _ _ idx.length cpl.length (rowsLen_selM _ _ _)
      hBr hTBr (rowsLen_selM _ _ _))

/-- A join at a vacant coupling row count is vacant: the pivot slab's
zip runs out with the coupling and the exchange's slab with the
transpose. -/
theorem blockJoin_nil (P B Q : Mat) (hB : B.length = 0) :
    (blockJoin P B Q).length = 0 := by
  have hBnil : B = [] := by
    cases B with
    | nil => rfl
    | cons r s => exact Nat.noConfusion hB
  rw [hBnil]
  show (List.zipWith (· ++ ·) P ([] : Mat)
    ++ List.zipWith (· ++ ·) (transposeM ([] : Mat)) Q).length = 0
  rw [ground.zipWith_nil_right (· ++ ·) P]
  rfl

/-- The pivot's deflation at the cleared carrier
(`lem:cellcount`'s pricing): the trailing block scaled by the
pivot's squared determinant against the coupling's own solved
correction, the positive square riding both terms. -/
def deflMat (P B Q Cw : Mat) : Mat :=
  siteDatum (matScaleB (minor P * minor P) Q)
    (matScaleB (minor P) (matMul (transposeM B) Cw))

/-- The join's action at a blocked vector: per half the block row's
two products, the read `def:elim`'s fold at the assembled rows. -/
theorem matVec_blockJoin (P B Q : Mat) (a b : List BPair)
    (hPr : rowsLen a.length P)
    (hBtr : rowsLen a.length (transposeM B)) :
    poly.oneValue (matVec (blockJoin P B Q) (a ++ b))
      (vecAdd (matVec P a) (matVec B b)
        ++ vecAdd (matVec (transposeM B) a) (matVec Q b)) := by
  show poly.oneValue
      (matVec (List.zipWith (· ++ ·) P B
        ++ List.zipWith (· ++ ·) (transposeM B) Q) (a ++ b)) _
  rw [elim.matVec_append]
  exact poly.oneValue_append _ _ _ _
    ((matVec_length _ _).trans (zipApp_len P B a b))
    (elim.matVec_rowJoin a.length P B a b hPr rfl)
    (elim.matVec_rowJoin a.length (transposeM B) Q a b hBtr rfl)

/-! The two carriers of the addition's families: the padding at the
pivot's order (`x ↦ (x, 0)`) and the deflation's lift
(`w ↦ (C w, −(det P) w)`), each a computed rectangular matrix so
that a combination of the family reads the action of one matrix at
the combination (`elim.matVec_combo`). -/

/-- The padding matrix at the pivot's order: the identity above the
unit rows. -/
private def padM (k m : Nat) : Mat :=
  matScaleB (BPair.ofPos Pos.one) (idMat k)
    ++ List.replicate m (List.replicate k BPair.unit)

/-- The deflation's lift: the solve witness above the negated
determinant's own identity. -/
private def liftM (P Cw : Mat) (m : Nat) : Mat :=
  Cw ++ matScaleB (minor P).swap (idMat m)

/-- The identity's row count at its order. -/
theorem idMat_len (k : Nat) : (idMat k).length = k :=
  ground.matOf_length k k _

/-- The identity's rows at its order. -/
theorem idMat_rows (k : Nat) : rowsLen k (idMat k) :=
  elim.rowsLen_matOf k k _

/-- The identity is square at its order. -/
theorem sqAt_idMat (k : Nat) : elim.sqAt (idMat k) k :=
  elim.sqAt_of (idMat_len k) (idMat_rows k)


/-- The matrix's iterated product at a stated order, the power's
carrier from the identity. -/
def matPow (M : Mat) (n : Nat) : Nat → Mat
  | 0 => idMat n
  | k + 1 => matMul M (matPow M n k)

/-- The iterated product keeps the row count. -/
theorem length_matPow (M : Mat) (n : Nat) (hM : M.length = n) :
    ∀ k, (matPow M n k).length = n
  | 0 => idMat_len n
  | k + 1 => (length_matMul M (matPow M n k)).trans hM

/-- The iterated product keeps the column counts. -/
theorem rowsLen_matPow (M : Mat) (n : Nat) (hMl : M.length = n) :
    ∀ k, rowsLen n (matPow M n k)
  | 0 => idMat_rows n
  | k + 1 =>
    rowsLen_cast
      (transposeLen (matPow M n k) (rowsLen_matPow M n hMl k)
        (length_matPow M n hMl k))
      (rowsLen_matMul M (matPow M n k))

/-- The identity's action is the vector itself. -/
theorem matVec_idMat (n : Nat) (u : List BPair)
    (hu : u.length = n) : poly.oneValue (matVec (idMat n) u) u := by
  have hid : (idMat n).length = n :=
    ground.length_mapRange _ n
  refine poly.oneValue_of_entries _ _ ?_ ?_
  · rw [matVec_length, hid, hu]
  · intro i hi
    rw [matVec_length, hid] at hi
    rw [show matVec (idMat n) u = (idMat n).map (fun r => dotN r u) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit _ (idMat n) i
        (by rw [hid]; exact hi),
      idMat_row n i hi]
    refine BPair.oneValue_trans (dotN_read _ u) ?_
    rw [dotP_comm (idRow n i) u]
    exact dotP_idRow u n i hu hi

private theorem padM_len (k q : Nat) : (padM k q).length = k + q := by
  show (matScaleB (BPair.ofPos Pos.one) (idMat k)
    ++ List.replicate q (List.replicate k BPair.unit)).length = k + q
  rw [ground.length_append, length_scaleB, idMat_len,
    ground.length_replicate]

private theorem padM_act (k q : Nat) (x : List BPair) (hx : x.length = k) :
    poly.oneValue (matVec (padM k q) x)
      (x ++ List.replicate q BPair.unit) := by
  show poly.oneValue
    (matVec (matScaleB (BPair.ofPos Pos.one) (idMat k)
      ++ List.replicate q (List.replicate k BPair.unit)) x) _
  rw [elim.matVec_append]
  refine poly.oneValue_append _ _ _ _ ?_ ?_ ?_
  · rw [matVec_length, length_scaleB, idMat_len, hx]
  · exact poly.oneValue_trans (scaleId_act (BPair.ofPos Pos.one) k x hx)
      (elim.vecScale_one x)
  · exact poly.unitTail_oneValue (elim.matVec_replicate_null k q x)
      (poly.unitTail_replicate q)

private theorem liftM_len (P Cw : Mat) (k q : Nat) (hCl : Cw.length = k) :
    (liftM P Cw q).length = k + q := by
  show (Cw ++ matScaleB (minor P).swap (idMat q)).length = k + q
  rw [ground.length_append, length_scaleB, idMat_len, hCl]

private theorem liftM_act (P Cw : Mat) (q : Nat) (w : List BPair)
    (hw : w.length = q) :
    poly.oneValue (matVec (liftM P Cw q) w)
      (matVec Cw w ++ vecScale (minor P).swap w) := by
  show poly.oneValue
    (matVec (Cw ++ matScaleB (minor P).swap (idMat q)) w) _
  rw [elim.matVec_append]
  exact poly.oneValue_append _ _ _ _ rfl (poly.oneValue_refl _)
    (scaleId_act (minor P).swap q w hw)

/-! The lift's two reads: the pairing's transpose adjoint at the
coupling slab, and the solve witness's own passage — the pivot at
the lifted vector's top half is the coupling's cleared action. -/


/-- The identity's form is the coordinates' fold of squares. -/
theorem quadForm_idMat (k : Nat) (u : List BPair)
    (hu : u.length = k) :
    (quadForm (idMat k) u).oneValue (elim.dotN u u) :=
  elim.dotN_congrR u (elim.matVec (idMat k) u) u (matVec_idMat k u hu)
/-- The pairing's transpose adjoint at a rectangular block: the
exchange's action against one vector reads the block's action
against the other. -/
theorem adjB (B : Mat) (k m : Nat) (hBl : B.length = k)
    (hBr : rowsLen m B) (w : List BPair) (hw : w.length = m)
    (y : List BPair) (hy : y.length = k) :
    (dotN w (matVec (transposeM B) y)).oneValue (dotN y (matVec B w)) := by
  refine BPair.oneValue_trans (dotN_read w _) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (dotP_matVec_transpose m B w y hBr hw (hy.trans hBl.symm))) ?_
  rw [dotP_comm (matVec B w) y]
  exact BPair.oneValue_symm (dotN_read y (matVec B w))

private theorem pivotSolve (P B Cw : Mat) (k m : Nat)
    (hPr : rowsLen k P) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B))
    (w : List BPair) (hw : w.length = m) :
    poly.oneValue (matVec P (matVec Cw w))
      (vecScale (minor P) (matVec B w)) :=
  poly.oneValue_trans
    (matVec_comp P Cw w m hCr hw (rowsLen_cast hCl.symm hPr))
    (poly.oneValue_trans (matVec_matOne _ _ w hPw)
      (matVec_scaleB (minor P) B w))


/-- The assembled datum's pairing at joined vectors: the four
blockwise pairings, the pivot's and the trailing block's on the
diagonal with the coupling slab's two off it. -/
theorem quadJoin (P B Q : Mat) (k m : Nat)
    (hPr : rowsLen k P) (hPl : P.length = k) (hBl : B.length = k)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQl : Q.length = m) (a b a' b' : List BPair)
    (ha : a.length = k) (hb : b.length = m) (ha' : a'.length = k) :
    (dotN (a ++ b) (matVec (blockJoin P B Q) (a' ++ b'))).oneValue
      ((dotN a (matVec P a') + dotN a (matVec B b'))
        + (dotN b (matVec (transposeM B) a') + dotN b (matVec Q b'))) := by
  have hPa : (matVec P a').length = k := (matVec_length P a').trans hPl
  have hBb : (matVec B b').length = k := (matVec_length B b').trans hBl
  have hTa : (matVec (transposeM B) a').length = m :=
    (matVec_length _ a').trans hBt
  have hQb : (matVec Q b').length = m := (matVec_length Q b').trans hQl
  refine BPair.oneValue_trans
    (dotN_congrR (a ++ b) _ _ (matVec_blockJoin P B Q a' b'
      (rowsLen_cast ha'.symm hPr) (rowsLen_cast ha'.symm hBtr))) ?_
  refine BPair.oneValue_trans
    (dotN_app a b _ _ (ha.trans (length_vecAdd _ _ k hPa hBb).symm)) ?_
  exact BPair.add_congr
    (elim.dotN_addRow_right a (matVec P a') (matVec B b')
      (hPa.trans ha.symm) (hBb.trans ha.symm))
    (elim.dotN_addRow_right b (matVec (transposeM B) a') (matVec Q b')
      (hTa.trans hb.symm) (hQb.trans hb.symm))

/-- The left-padded vector's quadratic form at a join is the pivot
block's own: the coupling slab meets the unit family and the join's
lower half is paired against it. -/
private theorem quad_padJ (P B Q : Mat) (k m : Nat)
    (hPr : rowsLen k P) (hPl : P.length = k) (hBl : B.length = k)
    (x : List BPair) (hx : x.length = k) :
    (dotN (x ++ List.replicate m BPair.unit)
        (matVec (blockJoin P B Q)
          (x ++ List.replicate m BPair.unit))).oneValue
      (dotN x (matVec P x)) := by
  have hU : poly.unitTail (List.replicate m BPair.unit) :=
    poly.unitTail_replicate m
  have hJl : (List.zipWith (· ++ ·) P B).length = k :=
    ground.length_zipWith (· ++ ·) P B k hPl hBl
  have hfst : x.length
      = (matVec (List.zipWith (· ++ ·) P B)
          (x ++ List.replicate m BPair.unit)).length := by
    rw [matVec_length, hJl]
    exact hx
  show (dotN (x ++ List.replicate m BPair.unit)
      (matVec (List.zipWith (· ++ ·) P B
        ++ List.zipWith (· ++ ·) (transposeM B) Q)
        (x ++ List.replicate m BPair.unit))).oneValue
    (dotN x (matVec P x))
  rw [elim.matVec_append]
  refine BPair.oneValue_trans (dotN_app x _ _ _ hfst) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr ?_ (dotN_nullL _ _ hU)) (BPair.add_unit _)
  refine BPair.oneValue_trans
    (dotN_congrR x _ _
      (elim.matVec_rowJoin k P B x (List.replicate m BPair.unit) hPr hx)) ?_
  refine BPair.oneValue_trans
    (elim.dotN_addRow_right x (matVec P x)
      (matVec B (List.replicate m BPair.unit))
      ((matVec_length P x).trans (hPl.trans hx.symm))
      ((matVec_length B _).trans (hBl.trans hx.symm))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (dotN_nullR x _ (matVec_null B _ hU))) ?_
  exact BPair.add_unit _


/-- The deflation's quadratic form at the cleared carrier: the
trailing block at the squared determinant against the solve
witness's own coupling. -/
private theorem quad_defl (P B Q Cw : Mat) (k m : Nat) (w : List BPair)
    (hw : w.length = m) (hBl : B.length = k) (hBr : rowsLen m B)
    (hQr : rowsLen m Q) (hQl : Q.length = m)
    (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hCt : (transposeM Cw).length = m) (hBt : (transposeM B).length = m)
    (hBtr : rowsLen k (transposeM B)) :
    (dotN w (matVec (deflMat P B Q Cw) w)).oneValue
      ((minor P * minor P) * dotN w (matVec Q w)
        + (minor P).swap * dotN (matVec Cw w) (matVec B w)) := by
  have hMr : rowsLen m (matMul (transposeM B) Cw) :=
    rowsLen_cast hCt (rowsLen_matMul (transposeM B) Cw)
  have hMl : (matMul (transposeM B) Cw).length = m :=
    (ground.length_map _ (transposeM B)).trans hBt
  have hXr : rowsLen w.length (matScaleB (minor P * minor P) Q) :=
    rowsLen_cast hw.symm (rowsLen_scaleB _ m Q hQr)
  have hYr : rowsLen w.length
      (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw))) :=
    rowsLen_cast hw.symm
      (rowsLen_mapRows BPair.swap _ m (rowsLen_scaleB _ m _ hMr))
  have hXl : (matVec (matScaleB (minor P * minor P) Q) w).length
      = w.length := by
    rw [matVec_length, length_scaleB, hQl, hw]
  have hYl : (matVec
      (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw)))
      w).length = w.length := by
    rw [matVec_length]
    show ((matScaleB (minor P) (matMul (transposeM B) Cw)).map
      (fun r => r.map BPair.swap)).length = w.length
    rw [ground.length_map, length_scaleB, hMl, hw]
  refine BPair.oneValue_trans
    (dotN_congrR w _ _ (matVec_add _ _ w hXr hYr)) ?_
  refine BPair.oneValue_trans (elim.dotN_addRow_right w _ _ hXl hYl) ?_
  refine BPair.add_congr ?_ ?_
  · exact BPair.oneValue_trans
      (dotN_congrR w _ _ (matVec_scaleB (minor P * minor P) Q w))
      (elim.dotN_scaleV _ w (matVec Q w))
  · rw [matVec_swapM (matScaleB (minor P) (matMul (transposeM B) Cw)) w,
      dotN_swap]
    refine BPair.oneValue_trans
      (ground.swap_congr
        (BPair.oneValue_trans
          (dotN_congrR w _ _             (matVec_scaleB (minor P) (matMul (transposeM B) Cw) w))
          (BPair.oneValue_trans
            (elim.dotN_scaleV (minor P) w (matVec (matMul (transposeM B) Cw) w))
            (BPair.mul_congr (BPair.oneValue_refl (minor P))
              (BPair.oneValue_trans
                (dotN_congrR w _ _                   (poly.oneValue_symm
                    (matVec_comp (transposeM B) Cw w m hCr hw
                      (rowsLen_cast hCl.symm hBtr))))
                (adjB B k m hBl hBr w hw (matVec Cw w)
                  ((matVec_length Cw w).trans hCl))))))) ?_
    exact BPair.oneValue_of_eq
      (BPair.swap_mul (minor P) (dotN (matVec Cw w) (matVec B w))).symm

/-- The lift's own cancellation: the determinant against its negated
self at one pairing reads the sum's unit — the solve's whole
content at the cross terms. -/
private theorem detKill (P : Mat) (t : BPair) :
    (minor P * t + (minor P).swap * t).oneValue BPair.unit := by
  rw [← BPair.right_distrib]
  exact BPair.oneValue_trans
    (BPair.mul_congr (ground.unitOfOne (BPair.oneValue_refl (minor P))) (BPair.oneValue_refl t))
    (BPair.unit_mul t)

/-- The lifted vector's quadratic form is the deflation's own. -/
private theorem quad_lift (P B Q Cw : Mat) (k m : Nat) (w : List BPair)
    (hw : w.length = m) (hPr : rowsLen k P) (hPl : P.length = k)
    (hBl : B.length = k) (hBr : rowsLen m B)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQr : rowsLen m Q) (hQl : Q.length = m)
    (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hCt : (transposeM Cw).length = m)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B)) :
    (dotN (matVec Cw w ++ vecScale (minor P).swap w)
        (matVec (blockJoin P B Q)
          (matVec Cw w ++ vecScale (minor P).swap w))).oneValue
      (dotN w (matVec (deflMat P B Q Cw) w)) := by
  have ha : (matVec Cw w).length = k := (matVec_length Cw w).trans hCl
  have hb : (vecScale (minor P).swap w).length = m :=
    (length_vecScale _ w).trans hw
  have hT1 : (dotN (matVec Cw w) (matVec P (matVec Cw w))).oneValue
      (minor P * dotN (matVec Cw w) (matVec B w)) :=
    BPair.oneValue_trans
      (dotN_congrR _ _ _ (pivotSolve P B Cw k m hPr hCl hCr hPw w hw))
      (elim.dotN_scaleV _ _ (matVec B w))
  have hT2 : (dotN (matVec Cw w)
      (matVec B (vecScale (minor P).swap w))).oneValue
      ((minor P).swap * dotN (matVec Cw w) (matVec B w)) :=
    BPair.oneValue_trans
      (dotN_congrR _ _ _ (matVec_vecScale_free B (minor P).swap w))
      (elim.dotN_scaleV _ _ (matVec B w))
  have hT3 : (dotN (vecScale (minor P).swap w)
      (matVec (transposeM B) (matVec Cw w))).oneValue
      ((minor P).swap * dotN (matVec Cw w) (matVec B w)) :=
    BPair.oneValue_trans (elim.dotN_comm _ _)
      (BPair.oneValue_trans (elim.dotN_scaleV _ _ w)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (elim.dotN_comm _ _)
            (adjB B k m hBl hBr w hw (matVec Cw w) ha))))
  have hT4 : (dotN (vecScale (minor P).swap w)
      (matVec Q (vecScale (minor P).swap w))).oneValue
      ((minor P).swap * ((minor P).swap * dotN w (matVec Q w))) :=
    BPair.oneValue_trans (elim.dotN_comm _ _)
      (BPair.oneValue_trans (elim.dotN_scaleV _ _ w)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (elim.dotN_comm _ _)
            (BPair.oneValue_trans
              (dotN_congrR w _ _ (matVec_vecScale_free Q (minor P).swap w))
              (elim.dotN_scaleV _ w (matVec Q w))))))
  have hsq : ((minor P).swap * ((minor P).swap * dotN w (matVec Q w)))
      = (minor P * minor P) * dotN w (matVec Q w) :=
    (BPair.mul_assoc _ _ _).symm.trans
      (congrArg (fun z => z * dotN w (matVec Q w)) (BPair.swap_sq (minor P)))
  refine BPair.oneValue_trans
    (quadJoin P B Q k m hPr hPl hBl hBt hBtr hQl _ _ _ _ ha hb ha) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.add_congr hT1 hT2)
      (BPair.add_congr hT3 hT4)) ?_
  rw [hsq]
  refine BPair.oneValue_trans
    (BPair.add_congr (detKill P (dotN (matVec Cw w) (matVec B w)))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
  exact BPair.oneValue_symm
    (quad_defl P B Q Cw k m w hw hBl hBr hQr hQl hCl hCr hCt hBt hBtr)

/-- The padded vector against the lifted one: the pivot rows read
the unit family at a lifted vector, so the cross pairing
vanishes. -/
private theorem cross_pad_lift (P B Q Cw : Mat) (k m : Nat)
    (x w : List BPair) (hx : x.length = k) (hw : w.length = m)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBl : B.length = k)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQl : Q.length = m) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B)) :
    (dotN (x ++ List.replicate m BPair.unit)
        (matVec (blockJoin P B Q)
          (matVec Cw w ++ vecScale (minor P).swap w))).oneValue
      BPair.unit := by
  have hU : poly.unitTail (List.replicate m BPair.unit) :=
    poly.unitTail_replicate m
  have ha : (matVec Cw w).length = k := (matVec_length Cw w).trans hCl
  refine BPair.oneValue_trans
    (quadJoin P B Q k m hPr hPl hBl hBt hBtr hQl x _ (matVec Cw w) _ hx
      (ground.length_replicate BPair.unit m) ha) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr
        (BPair.oneValue_trans
          (dotN_congrR x _ _ (pivotSolve P B Cw k m hPr hCl hCr hPw w hw))
          (elim.dotN_scaleV _ x (matVec B w)))
        (BPair.oneValue_trans
          (dotN_congrR x _ _ (matVec_vecScale_free B (minor P).swap w))
          (elim.dotN_scaleV _ x (matVec B w))))
      (BPair.add_congr (dotN_nullL _ _ hU) (dotN_nullL _ _ hU))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (detKill P (dotN x (matVec B w)))
      (BPair.unit_add BPair.unit)) ?_
  exact BPair.add_unit BPair.unit

/-- The lifted vector against the padded one: the pivot's symmetry
and the coupling's transpose adjoint close the second cross
pairing. -/
private theorem cross_lift_pad (P B Q Cw : Mat) (k m : Nat)
    (x w : List BPair) (hx : x.length = k) (hw : w.length = m)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBl : B.length = k) (hBr : rowsLen m B)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQl : Q.length = m) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hPs : matOneValue (transposeM P) P)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B)) :
    (dotN (matVec Cw w ++ vecScale (minor P).swap w)
        (matVec (blockJoin P B Q)
          (x ++ List.replicate m BPair.unit))).oneValue BPair.unit := by
  have hU : poly.unitTail (List.replicate m BPair.unit) :=
    poly.unitTail_replicate m
  have ha : (matVec Cw w).length = k := (matVec_length Cw w).trans hCl
  have hb : (vecScale (minor P).swap w).length = m :=
    (length_vecScale _ w).trans hw
  have hB1 : (dotN (matVec Cw w) (matVec P x)).oneValue
      (minor P * dotN x (matVec B w)) :=
    BPair.oneValue_trans (elim.dotN_comm _ _)
      (BPair.oneValue_trans (dotN_read (matVec P x) (matVec Cw w))
        (BPair.oneValue_trans
          (dotP_matVec_transpose k P x (matVec Cw w) hPr hx
            (ha.trans hPl.symm))
          (BPair.oneValue_trans
            (dotP_oneValue_right x _ _
              (matVec_matOne _ _ (matVec Cw w) hPs))
            (BPair.oneValue_trans
              (dotP_oneValue_right x _ _
                (pivotSolve P B Cw k m hPr hCl hCr hPw w hw))
              (BPair.oneValue_trans
                (dotP_vecScale_right x (matVec B w) (minor P))
                (BPair.mul_congr (BPair.oneValue_refl _)
                  (BPair.oneValue_symm (dotN_read x (matVec B w)))))))))
  have hB3 : (dotN (vecScale (minor P).swap w)
      (matVec (transposeM B) x)).oneValue
      ((minor P).swap * dotN x (matVec B w)) :=
    BPair.oneValue_trans (elim.dotN_comm _ _)
      (BPair.oneValue_trans (elim.dotN_scaleV _ _ w)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (elim.dotN_comm _ _)
            (adjB B k m hBl hBr w hw x hx))))
  refine BPair.oneValue_trans
    (quadJoin P B Q k m hPr hPl hBl hBt hBtr hQl _ _ x _ ha hb hx) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr hB1 (dotN_nullR _ _ (matVec_null B _ hU)))
      (BPair.add_congr hB3 (dotN_nullR _ _ (matVec_null Q _ hU)))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.add_unit _) (BPair.add_unit _)) ?_
  exact detKill P (dotN x (matVec B w))

/-- The addition's whole content at one pair of arguments: the
padded vector's form and the lifted one's join with no cross term
left — the pivot's form and the deflation's, at the coefficients'
own two halves. -/
private theorem quadSplit (P B Q Cw : Mat) (k m : Nat) (x w : List BPair)
    (hx : x.length = k) (hw : w.length = m)
    (hSr : rowsLen (k + m) (blockJoin P B Q))
    (hSl : (blockJoin P B Q).length = k + m)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBl : B.length = k) (hBr : rowsLen m B)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQr : rowsLen m Q) (hQl : Q.length = m)
    (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hCt : (transposeM Cw).length = m)
    (hPs : matOneValue (transposeM P) P)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B)) :
    (dotN (vecAdd (matVec (padM k m) x) (matVec (liftM P Cw m) w))
        (matVec (blockJoin P B Q)
          (vecAdd (matVec (padM k m) x)
            (matVec (liftM P Cw m) w)))).oneValue
      (dotN x (matVec P x) + dotN w (matVec (deflMat P B Q Cw) w)) := by
  have hu : (matVec (padM k m) x).length = k + m :=
    (matVec_length _ x).trans (padM_len k m)
  have hv : (matVec (liftM P Cw m) w).length = k + m :=
    (matVec_length _ w).trans (liftM_len P Cw k m hCl)
  have hpu := padM_act k m x hx
  have hpv := liftM_act P Cw m w hw
  have hulen : (x ++ List.replicate m BPair.unit).length = k + m := by
    rw [ground.length_append, hx, ground.length_replicate]
  have hvlen : (matVec Cw w ++ vecScale (minor P).swap w).length = k + m := by
    rw [ground.length_append, matVec_length, hCl, length_vecScale, hw]
  refine BPair.oneValue_trans
    (quadAdd (blockJoin P B Q) (k + m) hSr hSl _ _ hu hv) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr
        (BPair.oneValue_trans
          (quad_congr (blockJoin P B Q) _ _ hpu)
          (quad_padJ P B Q k m hPr hPl hBl x hx))
        (BPair.oneValue_trans (dotN_congrL _ _ _ hpu)
          (BPair.oneValue_trans
            (dotN_congrR _ _ _ (matVec_congr (blockJoin P B Q) _ _ hpv))
            (cross_pad_lift P B Q Cw k m x w hx hw hPr hPl hBl hBt
              hBtr hQl hCl hCr hPw))))
      (BPair.add_congr
        (BPair.oneValue_trans (dotN_congrL _ _ _ hpv)
          (BPair.oneValue_trans
            (dotN_congrR _ _ _ (matVec_congr (blockJoin P B Q) _ _ hpu))
            (cross_lift_pad P B Q Cw k m x w hx hw hPr hPl hBl hBr hBt
              hBtr hQl hCl hCr hPs hPw)))
        (BPair.oneValue_trans
          (quad_congr (blockJoin P B Q) _ _ hpv)
          (quad_lift P B Q Cw k m w hw hPr hPl hBl hBr hBt hBtr hQr hQl
            hCl hCr hCt hPw)))) ?_
  exact BPair.add_congr (BPair.add_unit _) (BPair.unit_add _)

private theorem padFam_combo (k q : Nat) (cs : List BPair) (L : Mat)
    (hL : rowsLen k L) :
    poly.oneValue (combo (k + q) cs (L.map (matVec (padM k q))))
      (matVec (padM k q) (combo k cs L)) := by
  have h := matVec_combo (padM k q) k cs L hL
  rw [padM_len k q] at h
  exact poly.oneValue_symm h

private theorem liftFam_combo (P Cw : Mat) (k q : Nat) (cs : List BPair)
    (L : Mat) (hCl : Cw.length = k)
    (hL : rowsLen q L) :
    poly.oneValue (combo (k + q) cs (L.map (matVec (liftM P Cw q))))
      (matVec (liftM P Cw q) (combo q cs L)) := by
  have h := matVec_combo (liftM P Cw q) q cs L hL
  rw [liftM_len P Cw k q hCl] at h
  exact poly.oneValue_symm h

private theorem padFam_rows (k q : Nat) (L : Mat) :
    rowsLen (k + q) (L.map (matVec (padM k q))) :=
  rowsLen_map (matVec (padM k q)) (k + q) L (fun x _ => (fun y => (matVec_length _ y).trans (padM_len k q)) x)

private theorem liftFam_rows (P Cw : Mat) (k q : Nat)
    (hCl : Cw.length = k) (L : Mat) :
    rowsLen (k + q) (L.map (matVec (liftM P Cw q))) :=
  rowsLen_map (matVec (liftM P Cw q)) (k + q) L (fun x _ => (fun y => (matVec_length _ y).trans (liftM_len P Cw k q hCl)) x)

/-- The joined family's combination: the two halves' own
combinations, each carried by its carrier's action. -/
private theorem famCombo (P Cw : Mat) (k m : Nat) (LP LD : Mat)
    (hLP : rowsLen k LP) (hLD : rowsLen m LD)
    (hCl : Cw.length = k)
    (cx cw : List BPair)
    (hcx : cx.length = (LP.map (matVec (padM k m))).length) :
    poly.oneValue
      (combo (k + m) (cx ++ cw)
        (LP.map (matVec (padM k m)) ++ LD.map (matVec (liftM P Cw m))))
      (vecAdd (matVec (padM k m) (combo k cx LP))
        (matVec (liftM P Cw m) (combo m cw LD))) := by
  have h1 := padFam_rows k m LP
  have h2 := liftFam_rows P Cw k m hCl LD
  refine poly.oneValue_trans (combo_append (k + m) cx _ cw _ hcx h1 h2) ?_
  exact elim.polyOne_vecAdd _ _ _ _ (padFam_combo k m cx LP hLP)
    (liftFam_combo P Cw k m cw LD hCl hLD)
    ((length_combo (k + m) cx _ h1).trans
      ((matVec_length _ _).trans (padM_len k m)).symm)
    ((length_combo (k + m) cw _ h2).trans
      ((matVec_length _ _).trans (liftM_len P Cw k m hCl)).symm)

/-- The joined family's quadratic form: the pivot's form at the
first half's combination joined to the deflation's at the
second's. -/
private theorem quadFam (P B Q Cw : Mat) (k m : Nat) (LP LD : Mat)
    (hLP : rowsLen k LP) (hLD : rowsLen m LD)
    (cx cw : List BPair)
    (hcx : cx.length = (LP.map (matVec (padM k m))).length)
    (hSr : rowsLen (k + m) (blockJoin P B Q))
    (hSl : (blockJoin P B Q).length = k + m)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBl : B.length = k) (hBr : rowsLen m B)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQr : rowsLen m Q) (hQl : Q.length = m)
    (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hCt : (transposeM Cw).length = m)
    (hPs : matOneValue (transposeM P) P)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B)) :
    (dotN
        (combo (k + m) (cx ++ cw)
          (LP.map (matVec (padM k m)) ++ LD.map (matVec (liftM P Cw m))))
        (matVec (blockJoin P B Q)
          (combo (k + m) (cx ++ cw)
            (LP.map (matVec (padM k m))
              ++ LD.map (matVec (liftM P Cw m)))))).oneValue
      (dotN (combo k cx LP) (matVec P (combo k cx LP))
        + dotN (combo m cw LD)
            (matVec (deflMat P B Q Cw) (combo m cw LD))) := by
  have hX : (combo k cx LP).length = k := length_combo k cx LP hLP
  have hW : (combo m cw LD).length = m := length_combo m cw LD hLD
  have hcl : (combo (k + m) (cx ++ cw)
      (LP.map (matVec (padM k m))
        ++ LD.map (matVec (liftM P Cw m)))).length = k + m :=
    length_combo (k + m) _ _
      (rowsLen_append (k + m) (padFam_rows k m LP)
        (liftFam_rows P Cw k m hCl LD))
  have hvl : (vecAdd (matVec (padM k m) (combo k cx LP))
      (matVec (liftM P Cw m) (combo m cw LD))).length = k + m :=
    length_vecAdd _ _ (k + m)
      ((matVec_length _ _).trans (padM_len k m))
      ((matVec_length _ _).trans (liftM_len P Cw k m hCl))
  refine BPair.oneValue_trans
    (quad_congr (blockJoin P B Q) _ _
      (famCombo P Cw k m LP LD hLP hLD hCl cx cw hcx)) ?_
  exact quadSplit P B Q Cw k m _ _ hX hW hSr hSl hPr hPl hBl hBr hBt
    hBtr hQr hQl hCl hCr hCt hPs hPw

/-- `lem:inertia`'s addition at a nonsingular principal pivot: the
assembled datum's reversal count is the pivot's joined to the
deflation's, at the solve witness `P C ~ (det P) B` and the
determinant off equal members.  The three splits are the theorem's
data — the assembled datum's, the pivot's and the deflation's — and
the count identity is read off them alone: the padded lower list and
the lifted one force the count from below, their complement
counterparts from above. -/
theorem rev_add {k m : Nat} (P B Q Cw : Mat)
    (hP : sqAt P k) (hBl : B.length = k) (hBr : rowsLen m B)
    (hQ : sqAt Q m) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hPs : matOneValue (transposeM P) P)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B))
    (hPnz : ¬ (minor P).oneValue BPair.unit)
    (spS : Split (k + m)) (hS : splitRead (blockJoin P B Q) spS)
    (spP : Split k) (hp : splitRead P spP)
    (spD : Split m) (hd : splitRead (deflMat P B Q Cw) spD) :
    revAt spS = revAt spP + revAt spD := by
  have hPr : rowsLen k P := rowsLen_of_sqAt hP
  have hPl : P.length = k := sqAt_len hP
  have hQr : rowsLen m Q := rowsLen_of_sqAt hQ
  have hQl : Q.length = m := sqAt_len hQ
  have hSr : rowsLen (k + m) (blockJoin P B Q) := rowsLen_of_sqAt hS.1
  have hSl : (blockJoin P B Q).length = k + m := sqAt_len hS.1
  have hBtr : rowsLen k (transposeM B) :=
    rowsLen_cast hBl (rowsLen_transposeM B)
  have hshape : (transposeM B).length = m ∧ (transposeM Cw).length = m := by
    cases Nat.eq_zero_or_pos k with
    | inl hk =>
      have hB0 : B = [] := by
        match B, hBl with
        | [], _ => exact rfl
        | _ :: t, hh => exact Nat.noConfusion (hh.trans hk)
      have hC0 : Cw = [] := by
        match Cw, hCl with
        | [], _ => exact rfl
        | _ :: t, hh => exact Nat.noConfusion (hh.trans hk)
      have h0 : (blockJoin P B Q).length = 0 := by
        rw [hB0]
        show (List.zipWith (· ++ ·) P ([] : Mat)
          ++ List.zipWith (· ++ ·) (transposeM ([] : Mat)) Q).length = 0
        rw [ground.zipWith_nil_right (· ++ ·) P]
        rfl
      have h1 : (0 : Nat) = k + m := h0.symm.trans hSl
      rw [hk, Nat.zero_add] at h1
      rw [hB0, hC0, h1.symm]
      exact ⟨rfl, rfl⟩
    | inr hk =>
      exact ⟨length_transposeM B hBr (by rw [hBl]; exact hk),
        length_transposeM Cw hCr (by rw [hCl]; exact hk)⟩
  have hBt : (transposeM B).length = m := hshape.1
  have hCt : (transposeM Cw).length = m := hshape.2
  have hge : revAt spP + revAt spD ≤ revAt spS := by
    have hstrict : ∀ cs : List BPair,
        cs.length = ((lowerList spP).map (matVec (padM k m))
          ++ (lowerList spD).map (matVec (liftM P Cw m))).length →
        ¬ poly.unitTail cs →
        dotN (combo (k + m) cs ((lowerList spP).map (matVec (padM k m))
            ++ (lowerList spD).map (matVec (liftM P Cw m))))
          (matVec (blockJoin P B Q)
            (combo (k + m) cs
              ((lowerList spP).map (matVec (padM k m))
                ++ (lowerList spD).map (matVec (liftM P Cw m)))))
          < BPair.unit := by
      intro cs hcs hoff
      have hlen : cs.length
          = ((lowerList spP).map (matVec (padM k m))).length
            + ((lowerList spD).map (matVec (liftM P Cw m))).length := by
        rw [hcs, ground.length_append]
      obtain ⟨cx, cw, rfl, hlx⟩ :=
        listSplit cs ((lowerList spP).map (matVec (padM k m))).length
          (by rw [hlen]; exact Nat.le_add_right _ _)
      have h1 : cx.length + cw.length
          = ((lowerList spP).map (matVec (padM k m))).length
            + ((lowerList spD).map (matVec (liftM P Cw m))).length := by
        rw [← ground.length_append cx cw]
        exact hlen
      rw [hlx] at h1
      have hlw : cw.length
          = ((lowerList spD).map (matVec (liftM P Cw m))).length :=
        ground.addCancelL _ h1
      have hXlen : cx.length = revAt spP := by
        rw [hlx, ground.length_map]
        exact lowerList_length P spP hp
      have hWlen : cw.length = revAt spD := by
        rw [hlw, ground.length_map]
        exact lowerList_length (deflMat P B Q Cw) spD hd
      refine BPair.lt_congr
        (BPair.oneValue_symm
          (quadFam P B Q Cw k m (lowerList spP) (lowerList spD)
            (lowerList_rowsLen spP) (lowerList_rowsLen spD) cx cw hlx
            hSr hSl hPr hPl hBl hBr hBt hBtr hQr hQl hCl hCr hCt hPs hPw))
        (BPair.oneValue_refl BPair.unit) ?_
      cases (inferInstance : Decidable (poly.unitTail cx)) with
      | isTrue hux =>
        refine leAddLtUnit ?_
          (lowerList_strict (deflMat P B Q Cw) spD hd cw hWlen
            (fun hcw => hoff (unitTail_append hux hcw)))
        exact ground.leB_congr_left
          (BPair.oneValue_symm
            (quadNull P _ (unitTail_combo_of k cx (lowerList spP) hux)))
          (ground.leB_refl BPair.unit)
      | isFalse hux =>
        refine ltUnitAddLe (lowerList_strict P spP hp cx hXlen hux) ?_
        cases (inferInstance : Decidable (poly.unitTail cw)) with
        | isTrue huw =>
          exact ground.leB_congr_left
            (BPair.oneValue_symm
              (quadNull (deflMat P B Q Cw) _
                (unitTail_combo_of m cw (lowerList spD) huw)))
            (ground.leB_refl BPair.unit)
        | isFalse huw =>
          exact ground.leB_of_lt
            (lowerList_strict (deflMat P B Q Cw) spD hd cw hWlen huw)
    have hfin := forcing (blockJoin P B Q) spS hS
      ((lowerList spP).map (matVec (padM k m))
        ++ (lowerList spD).map (matVec (liftM P Cw m)))
      (rowsLen_append (k + m) (padFam_rows k m (lowerList spP))
        (liftFam_rows P Cw k m hCl (lowerList spD))) hstrict
    rw [ground.length_append, ground.length_map, ground.length_map,
      lowerList_length P spP hp,
      lowerList_length (deflMat P B Q Cw) spD hd] at hfin
    exact hfin
  have hle : revAt spS ≤ revAt spP + revAt spD := by
    have hMr : rowsLen (k + m)
        ((complList spP).map (matVec (padM k m))
          ++ (complList spD).map (matVec (liftM P Cw m))) :=
      rowsLen_append (k + m) (padFam_rows k m (complList spP))
        (liftFam_rows P Cw k m hCl (complList spD))
    have hind : ∀ cs : List BPair,
        cs.length = ((complList spP).map (matVec (padM k m))
          ++ (complList spD).map (matVec (liftM P Cw m))).length →
        poly.unitTail (combo (k + m) cs
          ((complList spP).map (matVec (padM k m))
            ++ (complList spD).map (matVec (liftM P Cw m)))) →
        poly.unitTail cs := by
      intro cs hcs hu
      have hlen : cs.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spD).map (matVec (liftM P Cw m))).length := by
        rw [hcs, ground.length_append]
      obtain ⟨cx, cw, rfl, hlx⟩ :=
        listSplit cs ((complList spP).map (matVec (padM k m))).length
          (by rw [hlen]; exact Nat.le_add_right _ _)
      have h1 : cx.length + cw.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spD).map (matVec (liftM P Cw m))).length := by
        rw [← ground.length_append cx cw]
        exact hlen
      rw [hlx] at h1
      have hlw : cw.length
          = ((complList spD).map (matVec (liftM P Cw m))).length :=
        ground.addCancelL _ h1
      have hXlen : cx.length = (complList spP).length := by
        rw [hlx, ground.length_map]
      have hWlen : cw.length = (complList spD).length := by
        rw [hlw, ground.length_map]
      have hX : (combo k cx (complList spP)).length = k :=
        length_combo k cx _ (complList_rowsLen spP)
      have hW : (combo m cw (complList spD)).length = m :=
        length_combo m cw _ (complList_rowsLen spD)
      have hu2 : poly.unitTail
          (vecAdd (matVec (padM k m) (combo k cx (complList spP)))
            (matVec (liftM P Cw m) (combo m cw (complList spD)))) :=
        poly.unitTail_oneValue_right hu
          (famCombo P Cw k m (complList spP) (complList spD)
            (complList_rowsLen spP) (complList_rowsLen spD) hCl
            cx cw hlx)
      have hpu := padM_act k m (combo k cx (complList spP)) hX
      have hpv := liftM_act P Cw m (combo m cw (complList spD)) hW
      have hulen : ((combo k cx (complList spP))
          ++ List.replicate m BPair.unit).length = k + m := by
        rw [ground.length_append, hX, ground.length_replicate]
      have hvlen : (matVec Cw (combo m cw (complList spD))
          ++ vecScale (minor P).swap
            (combo m cw (complList spD))).length = k + m := by
        rw [ground.length_append, matVec_length, hCl, length_vecScale, hW]
      have hu3 : poly.unitTail
          (vecAdd ((combo k cx (complList spP))
              ++ List.replicate m BPair.unit)
            (matVec Cw (combo m cw (complList spD))
              ++ vecScale (minor P).swap
                (combo m cw (complList spD)))) :=
        poly.unitTail_oneValue_right hu2
          (elim.polyOne_vecAdd _ _ _ _ hpu hpv
            (((matVec_length _ _).trans (padM_len k m)).trans hulen.symm)
            (((matVec_length _ _).trans
              (liftM_len P Cw k m hCl)).trans hvlen.symm))
      rw [vecAdd_app (combo k cx (complList spP)) _
        (matVec Cw (combo m cw (complList spD))) _
        (hX.trans ((matVec_length Cw _).trans hCl).symm)] at hu3
      have hWnull : poly.unitTail (combo m cw (complList spD)) :=
        elim.unitTail_unscale _ (swapOff hPnz) _
          (poly.unitTail_oneValue_right
            (elim.unitTail_append_split _ _ hu3).2
            (vecAddUnitLeft (poly.unitTail_replicate m)
              ((ground.length_replicate BPair.unit m).trans
                ((length_vecScale _ _).trans hW).symm)))
      have hcw : poly.unitTail cw :=
        complList_indep (deflMat P B Q Cw) spD hd cw hWlen hWnull
      have hXnull : poly.unitTail (combo k cx (complList spP)) :=
        (elim.unitTail_append_split _ (List.replicate m BPair.unit)
          (poly.unitTail_oneValue_right
            (unitTailAddRight _ _
              (((matVec_length _ _).trans (padM_len k m)).trans
                ((matVec_length _ _).trans
                  (liftM_len P Cw k m hCl)).symm)
              (matVec_null (liftM P Cw m) _ hWnull) hu2)
            hpu)).1
      exact unitTail_append
        (complList_indep P spP hp cx hXlen hXnull) hcw
    have hside : ∀ cs : List BPair,
        cs.length = ((complList spP).map (matVec (padM k m))
          ++ (complList spD).map (matVec (liftM P Cw m))).length →
        ¬ (dotN (combo (k + m) cs
            ((complList spP).map (matVec (padM k m))
              ++ (complList spD).map (matVec (liftM P Cw m))))
          (matVec (blockJoin P B Q)
            (combo (k + m) cs
              ((complList spP).map (matVec (padM k m))
                ++ (complList spD).map (matVec (liftM P Cw m)))))
          < BPair.unit) := by
      intro cs hcs
      have hlen : cs.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spD).map (matVec (liftM P Cw m))).length := by
        rw [hcs, ground.length_append]
      obtain ⟨cx, cw, rfl, hlx⟩ :=
        listSplit cs ((complList spP).map (matVec (padM k m))).length
          (by rw [hlen]; exact Nat.le_add_right _ _)
      have h1 : cx.length + cw.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spD).map (matVec (liftM P Cw m))).length := by
        rw [← ground.length_append cx cw]
        exact hlen
      rw [hlx] at h1
      have hlw : cw.length
          = ((complList spD).map (matVec (liftM P Cw m))).length :=
        ground.addCancelL _ h1
      have hXlen : cx.length = (complList spP).length := by
        rw [hlx, ground.length_map]
      have hWlen : cw.length = (complList spD).length := by
        rw [hlw, ground.length_map]
      intro hlt
      refine ground.leB_not_lt
        (unitLeAdd
          (ground.leB_of_not_lt (complList_side P spP hp cx hXlen))
          (ground.leB_of_not_lt
            (complList_side (deflMat P B Q Cw) spD hd cw hWlen))) ?_
      exact BPair.lt_congr
        (quadFam P B Q Cw k m (complList spP) (complList spD)
          (complList_rowsLen spP) (complList_rowsLen spD) cx cw hlx
          hSr hSl hPr hPl hBl hBr hBt hBtr hQr hQl hCl hCr hCt hPs hPw)
        (BPair.oneValue_refl BPair.unit) hlt
    have hup := forcing_upper (blockJoin P B Q) spS hS
      ((complList spP).map (matVec (padM k m))
        ++ (complList spD).map (matVec (liftM P Cw m))) hMr hind hside
    rw [ground.length_append, ground.length_map, ground.length_map] at hup
    have hkey : (complList spP).length + (complList spD).length + revAt spS
        ≤ (revAt spP + (complList spP).length)
          + (revAt spD + (complList spD).length) := by
      rw [complList_length P spP hp,
        complList_length (deflMat P B Q Cw) spD hd]
      exact hup
    rw [Nat.add_add_add_comm (revAt spP) (complList spP).length (revAt spD)
        (complList spD).length,
      Nat.add_comm ((complList spP).length + (complList spD).length)
        (revAt spS)] at hkey
    exact ground.leCancelR _ hkey
  exact Nat.le_antisymm hle hge

/-- The rescaled matrix's entry read: the scalar against the entry
at the canonical representative, one read per key pair. -/
theorem entry_scaleB (c : BPair) (A : Mat) (n : Nat)
    (hA : rowsLen n A) (i j : Nat) (hi : i < A.length) (hj : j < n) :
    ground.getAt BPair.unit (ground.getAt [] (matScaleB c A) i) j
      = (c * ground.getAt BPair.unit (ground.getAt [] A i) j).norm := by
  show ground.getAt BPair.unit
    (ground.getAt [] (A.map (poly.scaleP c)) i) j = _
  rw [ground.getAt_map [] [] (poly.scaleP c) A i hi]
  exact ground.getAt_map BPair.unit BPair.unit (fun x => (c * x).norm) _ j
    (by rw [rowsLen_getAt A i hA hi]; exact hj)

/-- `lem:inertia`'s determinant split at the cleared deflation: the
pivot's determinant against the deflation's reads the pivot's
determinant at twice the deflation's order against the assembled
datum's, the unit-triangular congruence keeping the determinant and
the block diagonal's determinant its blocks' product. -/
theorem minor_deflMat {k m : Nat} (P B Q Cw : Mat)
    (hP : sqAt P k) (hBl : B.length = k) (hBr : rowsLen m B)
    (hQ : sqAt Q m) (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hPs : matOneValue (transposeM P) P)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B))
    (hPnz : ¬ (minor P).oneValue BPair.unit) :
    (minor P * minor (deflMat P B Q Cw)).oneValue
      (ground.bpow (minor P) (2 * m) * minor (blockJoin P B Q)) := by
  cases k with
  | zero =>
    have hPn : P = [] := by
      cases P with
      | nil => rfl
      | cons r t => exact Nat.noConfusion (sqAt_len hP)
    have hBn : B = [] := by
      cases B with
      | nil => rfl
      | cons r t => exact Nat.noConfusion hBl
    have hCn : Cw = [] := by
      cases Cw with
      | nil => rfl
      | cons r t => exact Nat.noConfusion hCl
    subst hPn
    subst hBn
    subst hCn
    have hA : matAdd (matScaleB (minor ([] : Mat) * minor ([] : Mat)) Q)
        ([] : Mat) = [] := ground.zipWith_nil_right _ _
    show (BPair.ofPos Pos.one
      * minor (matAdd (matScaleB (minor ([] : Mat) * minor ([] : Mat)) Q)
        ([] : Mat))).oneValue
      (ground.bpow (BPair.ofPos Pos.one) (2 * m) * BPair.ofPos Pos.one)
    rw [hA]
    exact BPair.oneValue_symm (BPair.mul_congr_left (ground.bpow_one (2 * m)))
  | succ k =>
    have hk : 0 < k + 1 := Nat.succ_pos k
    have hPl : P.length = k + 1 := sqAt_len hP
    have hPr : rowsLen (k + 1) P := rowsLen_of_sqAt hP
    have hQl : Q.length = m := sqAt_len hQ
    have hQr : rowsLen m Q := rowsLen_of_sqAt hQ
    have hBpos : 0 < B.length := by rw [hBl]; exact hk
    have hCpos : 0 < Cw.length := by rw [hCl]; exact hk
    have hPpos : 0 < P.length := by rw [hPl]; exact hk
    have hTl : (transposeM B).length = m := length_transposeM B hBr hBpos
    have hTr : rowsLen (k + 1) (transposeM B) :=
      rowsLen_cast hBl (rowsLen_transposeM B)
    have hMsT : rowsLen (k + 1) ((transposeM B).map (vecScale (minor P))) :=
      rowsLen_mapRows (fun x => minor P * x) _ (k + 1) hTr
    have hMsQ : rowsLen m (Q.map (vecScale (minor P))) :=
      rowsLen_mapRows (fun x => minor P * x) _ m hQr
    have hCtl : (transposeM Cw).length = m := length_transposeM Cw hCr hCpos
    have hCtr : rowsLen (k + 1) (transposeM Cw) :=
      rowsLen_cast hCl (rowsLen_transposeM Cw)
    have hPtl : (transposeM P).length = k + 1 :=
      length_transposeM P hPr hPpos
    have hPtr : rowsLen (k + 1) (transposeM P) :=
      rowsLen_cast hPl (rowsLen_transposeM P)
    -- the product's shapes
    have hPCl : (matMul P Cw).length = k + 1 := (length_matMul P Cw).trans hPl
    have hPCr : rowsLen m (matMul P Cw) :=
      rowsLen_cast hCtl (rowsLen_matMul P Cw)
    have hdBl : (matScaleB (minor P) B).length = k + 1 :=
      (length_scaleB _ B).trans hBl
    have hdBr : rowsLen m (matScaleB (minor P) B) := rowsLen_scaleB _ m B hBr
    -- `Cwᵀ P` reads the transposed solve
    have hCP : matOneValue (matMul (transposeM Cw) P)
        (transposeM (matMul P Cw)) :=
      matOne_symm (matOne_trans
        (transposeM_matMul (r := k + 1) (n := k + 1) (k := m) P Cw hPr hCr hPl
          hCl hk hk)
        (matMul_congrR (n := k + 1) (k := k + 1) (transposeM Cw) (transposeM P)
          P hPtr hPr hPtl hPl hk hPs))
    have hCPl : (matMul (transposeM Cw) P).length = m :=
      (length_matMul _ P).trans hCtl
    have hCPr : rowsLen (k + 1) (matMul (transposeM Cw) P) :=
      rowsLen_cast hPtl (rowsLen_matMul _ P)
    have hSwP : rowsLen (k + 1) (matSwap (matMul (transposeM Cw) P)) :=
      rowsLen_mapRows BPair.swap _ (k + 1) hCPr
    -- the entry read of the solve: `(Cwᵀ P)_{i b} ~ d · B_{b i}`
    have hSolve : ∀ i b, i < m → b < k + 1 →
        (ground.getAt BPair.unit
            (ground.getAt [] (matMul (transposeM Cw) P) i) b).oneValue
          (minor P * ground.getAt BPair.unit (ground.getAt [] B b) i) := by
      intro i b hi hb
      have hbP : b < (matMul P Cw).length := by rw [hPCl]; exact hb
      have hbB : b < B.length := by rw [hBl]; exact hb
      refine BPair.oneValue_trans
        (matOne_entry hCP i b (by rw [hCPl]; exact hi)) ?_
      rw [getAt_transposeM BPair.unit (matMul P Cw) hPCr i b hi hbP]
      refine BPair.oneValue_trans (matOne_entry hPw b i hbP) ?_
      rw [entry_scaleB (minor P) B m hBr b i hbB hi]
      exact BPair.norm_oneValue _
    -- the reduced slabs
    have hL'l : (matAdd ((transposeM B).map (vecScale (minor P)))
        (matSwap (matMul (transposeM Cw) P))).length = m := by
      rw [length_matAdd _ _
          (by rw [ground.length_map, hTl, length_matSwap, hCPl]),
        ground.length_map, hTl]
    have hL'r : rowsLen (k + 1)
        (matAdd ((transposeM B).map (vecScale (minor P)))
        (matSwap (matMul (transposeM Cw) P))) :=
      rowsLen_matAdd (k + 1) _ _
        hMsT
        hSwP
    have hCBl : (matMul (transposeM Cw) B).length = m :=
      (length_matMul _ B).trans hCtl
    have hCBr : rowsLen m (matMul (transposeM Cw) B) :=
      rowsLen_cast hTl (rowsLen_matMul _ B)
    have hSwCB : rowsLen m (matSwap (matMul (transposeM Cw) B)) :=
      rowsLen_mapRows BPair.swap _ m hCBr
    have hR'l : (matAdd (Q.map (vecScale (minor P)))
        (matSwap (matMul (transposeM Cw) B))).length = m := by
      rw [length_matAdd _ _
          (by rw [ground.length_map, hQl, length_matSwap, hCBl]),
        ground.length_map, hQl]
    have hR'r : rowsLen m (matAdd (Q.map (vecScale (minor P)))
        (matSwap (matMul (transposeM Cw) B))) :=
      rowsLen_matAdd m _ _ hMsQ
        hSwCB
    have hR' : sqAt (matAdd (Q.map (vecScale (minor P)))
        (matSwap (matMul (transposeM Cw) B))) m := sqAt_of hR'l hR'r
    -- the slab reduction
    have hSlab := detL_slabReduce P B (transposeM B) Q Cw (k + 1) m (minor P)
      hk hP hBl hBr hTl hTr hQ hCl hCr
    -- the reduced lower-left slab reads the unit throughout
    have hNull : ∀ i b, i < m → b < k + 1 →
        (ground.getAt BPair.unit (ground.getAt []
          (matAdd ((transposeM B).map (vecScale (minor P)))
            (matSwap (matMul (transposeM Cw) P))) i) b).oneValue
          BPair.unit := by
      intro i b hi hb
      rw [entry_matAdd _ _ (k + 1)
          hMsT
          hSwP i b
          (by rw [ground.length_map, hTl]; exact hi)
          (by rw [length_matSwap, hCPl]; exact hi) hb,
        entry_mapScale _ _ (k + 1) hTr i b (by rw [hTl]; exact hi) hb,
        entry_matSwap _ (k + 1) hCPr i b (by rw [hCPl]; exact hi) hb,
        getAt_transposeM BPair.unit B hBr i b hi (by rw [hBl]; exact hb),
        BPair.add_comm]
      exact BPair.swap_add_null (hSolve i b hi hb)
    -- the congruence to the block-triangular form
    have hPBl : (rowJoin P B).length = k + 1 :=
      ground.length_zipWith (· ++ ·) P B (k + 1) hPl hBl
    have hLRl : (rowJoin
        (matAdd ((transposeM B).map (vecScale (minor P)))
          (matSwap (matMul (transposeM Cw) P)))
        (matAdd (Q.map (vecScale (minor P)))
          (matSwap (matMul (transposeM Cw) B)))).length = m :=
      ground.length_zipWith (· ++ ·) _ _ m hL'l hR'l
    have hZRl : (rowJoin (List.replicate m (List.replicate (k + 1) BPair.unit))
        (matAdd (Q.map (vecScale (minor P)))
          (matSwap (matMul (transposeM Cw) B)))).length = m :=
      ground.length_zipWith (· ++ ·) _ _ m (ground.length_replicate _ m) hR'l
    have hTri : (detL (rowJoin P B
        ++ rowJoin
          (matAdd ((transposeM B).map (vecScale (minor P)))
            (matSwap (matMul (transposeM Cw) P)))
          (matAdd (Q.map (vecScale (minor P)))
            (matSwap (matMul (transposeM Cw) B))))).oneValue
        (detL (rowJoin P B
          ++ rowJoin (List.replicate m (List.replicate (k + 1) BPair.unit))
            (matAdd (Q.map (vecScale (minor P)))
              (matSwap (matMul (transposeM Cw) B))))) := by
      refine detL_congr_letters _ _
        (by rw [ground.length_append, ground.length_append, hLRl, hZRl]) ?_
      intro a ha b hb
      rw [ground.length_append, hPBl, hLRl] at ha hb
      cases Nat.lt_or_ge a (k + 1) with
      | inl halt =>
        have halt' : a < (rowJoin P B).length := by rw [hPBl]; exact halt
        rw [ground.getAt_append, ground.getAt_append, if_pos halt',
          if_pos halt']
        exact BPair.oneValue_refl _
      | inr hage =>
        obtain ⟨i, hi⟩ := Nat.le.dest hage
        subst hi
        have him : i < m := by
          cases Nat.lt_or_ge i m with
          | inl h => exact h
          | inr h =>
            exact absurd ha (Nat.not_lt_of_le (Nat.add_le_add_left h _))
        have hrow : ∀ X : Mat, ground.getAt ([] : List BPair)
            (rowJoin P B ++ X) (k + 1 + i) = ground.getAt [] X i := by
          intro X
          rw [← hPBl]
          exact ground.getAt_append_add [] _ X i
        rw [hrow, hrow,
          getAt_rowJoin _ _ i (by rw [hL'l]; exact him)
            (by rw [hR'l]; exact him),
          getAt_rowJoin _ _ i (by rw [ground.length_replicate]; exact him)
            (by rw [hR'l]; exact him),
          ground.getAt_replicate [] _ m i him]
        have hL'il : (ground.getAt []
            (matAdd ((transposeM B).map (vecScale (minor P)))
            (matSwap (matMul (transposeM Cw) P))) i).length = k + 1 :=
          rowsLen_getAt _ i hL'r (by rw [hL'l]; exact him)
        cases Nat.lt_or_ge b (k + 1) with
        | inl hblt =>
          rw [ground.getAt_append, ground.getAt_append,
            if_pos (by rw [hL'il]; exact hblt),
            if_pos (by rw [ground.length_replicate]; exact hblt),
            ground.getAt_replicate BPair.unit BPair.unit (k + 1) b hblt]
          exact hNull i b him hblt
        | inr hbge =>
          obtain ⟨j, hj⟩ := Nat.le.dest hbge
          subst hj
          have hcol : ∀ (u v : List BPair), u.length = k + 1 →
              ground.getAt BPair.unit (u ++ v) (k + 1 + j)
                = ground.getAt BPair.unit v j := by
            intro u v hu
            rw [← hu]
            exact ground.getAt_append_add BPair.unit u v j
          rw [hcol _ _ hL'il, hcol _ _ (ground.length_replicate _ _)]
          exact BPair.oneValue_refl _
    have hBT : (detL (rowJoin P B
        ++ rowJoin (List.replicate m (List.replicate (k + 1) BPair.unit))
          (matAdd (Q.map (vecScale (minor P)))
            (matSwap (matMul (transposeM Cw) B))))).oneValue
        (detL P * detL (matAdd (Q.map (vecScale (minor P)))
          (matSwap (matMul (transposeM Cw) B)))) :=
      detL_blockTri P B _ (k + 1) m hP hBl hBr hR'
    -- `Cwᵀ B ~ Bᵀ Cw` through the symmetric pivot
    have hBCl : (matMul (transposeM B) Cw).length = m :=
      (length_matMul _ Cw).trans hTl
    have hBCr : rowsLen m (matMul (transposeM B) Cw) :=
      rowsLen_cast hCtl (rowsLen_matMul _ Cw)
    have hSwBC : rowsLen m (matSwap (matMul (transposeM B) Cw)) :=
      rowsLen_mapRows BPair.swap _ m hBCr
    have hSwD : rowsLen m
        (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw))) :=
      rowsLen_mapRows BPair.swap _ m (rowsLen_scaleB _ m _ hBCr)
    have hX : matOneValue (matScaleB (minor P) (matMul (transposeM Cw) B))
        (matScaleB (minor P) (matMul (transposeM B) Cw)) := by
      have a1 : matOneValue (matMul (transposeM Cw) (matMul P Cw))
          (matMul (transposeM Cw) (matScaleB (minor P) B)) :=
        matMul_congrR (n := k + 1) (k := m) (transposeM Cw) _ _ hPCr hdBr hPCl
          hdBl hk hPw
      have a2 : matOneValue (matMul (transposeM Cw) (matScaleB (minor P) B))
          (matScaleB (minor P) (matMul (transposeM Cw) B)) :=
        matMul_scaleR (minor P) m (transposeM Cw) B hBr
      have b1 : matOneValue (matMul (matMul (transposeM Cw) P) Cw)
          (matMul (transposeM Cw) (matMul P Cw)) :=
        matMul_assoc (n := k + 1) (k := k + 1) (s := m) (transposeM Cw) P Cw
          hCtr hPr hCr hPl hCl hk hk
      have b2 : matOneValue (matMul (matMul (transposeM Cw) P) Cw)
          (matMul (transposeM (matMul P Cw)) Cw) :=
        matMul_congrL _ _ Cw hCP
      have b3 : matOneValue (matMul (transposeM (matMul P Cw)) Cw)
          (matMul (transposeM (matScaleB (minor P) B)) Cw) :=
        matMul_congrL _ _ Cw
          (transposeM_congrM m _ _ hPCr hdBr (by rw [hPCl, hdBl]) hPw)
      have b4 : matOneValue (matMul (transposeM (matScaleB (minor P) B)) Cw)
          (matMul (matScaleB (minor P) (transposeM B)) Cw) :=
        matMul_congrL _ _ Cw (transposeM_scaleB (minor P) m B hBr)
      have b5 : matOneValue (matMul (matScaleB (minor P) (transposeM B)) Cw)
          (matScaleB (minor P) (matMul (transposeM B) Cw)) :=
        matMul_scaleL (minor P) (transposeM B) Cw
      exact matOne_trans (matOne_symm a2) (matOne_trans (matOne_symm a1)
        (matOne_trans (matOne_symm b1) (matOne_trans b2
          (matOne_trans b3 (matOne_trans b4 b5)))))
    have hXent : ∀ i j, i < m → j < m →
        (ground.getAt BPair.unit
            (ground.getAt [] (matMul (transposeM Cw) B) i) j).oneValue
          (ground.getAt BPair.unit
            (ground.getAt [] (matMul (transposeM B) Cw) i) j) := by
      intro i j hi hj
      have h := matOne_entry hX i j (by rw [length_scaleB, hCBl]; exact hi)
      rw [entry_scaleB _ _ m hCBr i j (by rw [hCBl]; exact hi) hj,
        entry_scaleB _ _ m hBCr i j (by rw [hBCl]; exact hi) hj] at h
      exact ground.mulCancel hPnz
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.norm_oneValue _))
          (BPair.oneValue_trans h (BPair.norm_oneValue _)))
    -- the reduced trailing slab against the deflation's unscaled form
    have hR''l : (matAdd (Q.map (vecScale (minor P)))
        (matSwap (matMul (transposeM B) Cw))).length = m := by
      rw [length_matAdd _ _
          (by rw [ground.length_map, hQl, length_matSwap, hBCl]),
        ground.length_map, hQl]
    have hR''r : rowsLen m (matAdd (Q.map (vecScale (minor P)))
        (matSwap (matMul (transposeM B) Cw))) :=
      rowsLen_matAdd m _ _ hMsQ
        hSwBC
    have hRR : (detL (matAdd (Q.map (vecScale (minor P)))
        (matSwap (matMul (transposeM Cw) B)))).oneValue
        (detL (matAdd (Q.map (vecScale (minor P)))
          (matSwap (matMul (transposeM B) Cw)))) := by
      refine detL_congr_letters _ _ (by rw [hR'l, hR''l]) ?_
      intro i hi j hj
      rw [hR'l] at hi hj
      rw [entry_matAdd _ _ m hMsQ
          hSwCB i j
          (by rw [ground.length_map, hQl]; exact hi)
          (by rw [length_matSwap, hCBl]; exact hi) hj,
        entry_matAdd _ _ m hMsQ
          hSwBC i j
          (by rw [ground.length_map, hQl]; exact hi)
          (by rw [length_matSwap, hBCl]; exact hi) hj,
        entry_matSwap _ m hCBr i j (by rw [hCBl]; exact hi) hj,
        entry_matSwap _ m hBCr i j (by rw [hBCl]; exact hi) hj]
      exact BPair.add_congr (BPair.oneValue_refl _)
        (ground.swap_congr (hXent i j hi hj))
    -- the deflation is the unscaled form at the pivot's scale
    have hDfl : deflMat P B Q Cw
        = matAdd (matScaleB (minor P * minor P) Q)
          (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw))) := rfl
    have hDl : (deflMat P B Q Cw).length = m := by
      rw [hDfl, length_matAdd _ _ (by
        rw [length_scaleB, hQl, length_matSwap, length_scaleB, hBCl]),
        length_scaleB, hQl]
    have hDr : rowsLen m (deflMat P B Q Cw) := by
      rw [hDfl]
      exact rowsLen_matAdd m _ _ (rowsLen_scaleB _ m Q hQr)
        hSwD
    have hDS : (detL (deflMat P B Q Cw)).oneValue
        (detL ((matAdd (Q.map (vecScale (minor P)))
          (matSwap (matMul (transposeM B) Cw))).map (vecScale (minor P)))) := by
      refine detL_congr_letters _ _ (by rw [hDl, ground.length_map, hR''l]) ?_
      intro i hi j hj
      rw [hDl] at hi hj
      rw [entry_mapScale _ _ m hR''r i j (by rw [hR''l]; exact hi) hj,
        entry_matAdd _ _ m hMsQ
          hSwBC i j
          (by rw [ground.length_map, hQl]; exact hi)
          (by rw [length_matSwap, hBCl]; exact hi) hj,
        entry_matSwap _ m hBCr i j (by rw [hBCl]; exact hi) hj,
        entry_mapScale _ _ m hQr i j (by rw [hQl]; exact hi) hj,
        hDfl,
        entry_matAdd _ _ m (rowsLen_scaleB _ m Q hQr)
          hSwD i j
          (by rw [length_scaleB, hQl]; exact hi)
          (by rw [length_matSwap, length_scaleB, hBCl]; exact hi) hj,
        entry_scaleB _ Q m hQr i j (by rw [hQl]; exact hi) hj,
        entry_matSwap _ m (rowsLen_scaleB _ m _ hBCr) i j
          (by rw [length_scaleB, hBCl]; exact hi) hj,
        entry_scaleB _ _ m hBCr i j (by rw [hBCl]; exact hi) hj,
        BPair.left_distrib, BPair.mul_swap, BPair.mul_assoc]
      exact BPair.add_congr (BPair.norm_oneValue _)
        (ground.swap_congr (BPair.norm_oneValue _))
    have hSc := detL_scaleAll (minor P) m
      (matAdd (Q.map (vecScale (minor P)))
        (matSwap (matMul (transposeM B) Cw))) hR''l
    -- the assembly
    have hBJ : blockJoin P B Q = rowJoin P B ++ rowJoin (transposeM B) Q := rfl
    have hBJl : (blockJoin P B Q).length = k + 1 + m :=
      length_blockJoin P B Q (k + 1) m hPl hBl hTl hQl
    have hBJr : rowsLen (k + 1 + m) (blockJoin P B Q) :=
      rowsLen_blockJoin P B Q (k + 1) m hPr hBr hTr hQr
    have hMinD : (minor (deflMat P B Q Cw)).oneValue (detL (deflMat P B Q Cw)) :=
      minor_detL _ (by rw [hDl]; exact hDr)
    have hMinJ : (minor (blockJoin P B Q)).oneValue (detL (blockJoin P B Q)) :=
      minor_detL _ (by rw [hBJl]; exact hBJr)
    have hMinP : (minor P).oneValue (detL P) :=
      minor_detL P (by rw [hPl]; exact hPr)
    -- the common value: `d · (d^m · det R')`
    have hLeft : (minor P * minor (deflMat P B Q Cw)).oneValue
        (minor P * (ground.bpow (minor P) m
          * detL (matAdd (Q.map (vecScale (minor P)))
            (matSwap (matMul (transposeM Cw) B))))) :=
      BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans hMinD (BPair.oneValue_trans hDS
          (BPair.oneValue_trans hSc
            (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hRR)))))
    have hRight : (ground.bpow (minor P) (2 * m) * minor (blockJoin P B Q)).oneValue
        (minor P * (ground.bpow (minor P) m
          * detL (matAdd (Q.map (vecScale (minor P)))
            (matSwap (matMul (transposeM Cw) B))))) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr (by rw [Nat.two_mul]; exact ground.bpow_add (minor P) m m) hMinJ) ?_
      rw [BPair.mul_assoc]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (by rw [hBJ]; exact hSlab)
            (BPair.oneValue_trans hTri (BPair.oneValue_trans hBT
              (BPair.mul_congr_left (BPair.oneValue_symm hMinP)))))) ?_
      refine BPair.oneValue_of_eq ?_
      rw [← BPair.mul_assoc, BPair.mul_comm (ground.bpow (minor P) m) (minor P),
        BPair.mul_assoc]
    exact BPair.oneValue_trans hLeft (BPair.oneValue_symm hRight)

/-! `lem:inertia`'s addition at a block diagonal, the pivot clause's
instance at a coupling of equal members.  At that off-block the
lift is a padding besides (`padR`, the trailing block's own half of
the join) and the pricing runs without the solve: the four
blockwise pairings of `quadJoin` read the two forms on the diagonal
with the two crossings at the sum's unit, the off-block's action
and its exchange's reading the unit family at every vector
(`elim.matVec_nullMat` with `slabT_null`, the off-block `elim.nullMat`'s own).  The two lower lists, each padded into
its own half, force one side at `forcing`; the complement lists
force the other at `forcing_upper`, the padded halves' coefficients
read back off the joined vector's own two halves rather than
through a determinant.  The count is the two counts' sum
(`rev_join`). -/

private theorem slabT_null (k m : Nat) (v : List BPair) :
    poly.unitTail (matVec (transposeM (nullMat k m)) v) :=
  elim.matVec_matNull _ v (matNull_transposeM _ (matNull_nullMat m k))

/-- The padding at the trailing block's order: the unit rows above
the identity, the pivot's own padding's partner half. -/
def padR (k m : Nat) : Mat :=
  nullMat k m ++ matScaleB (BPair.ofPos Pos.one) (idMat m)

/-- The trailing padding's row count at the joined order. -/
theorem padR_len (k m : Nat) : (padR k m).length = k + m := by
  show (nullMat k m
    ++ matScaleB (BPair.ofPos Pos.one) (idMat m)).length = k + m
  rw [ground.length_append, length_nullMat, length_scaleB, idMat_len]

/-- The trailing padding's action: the unit family above the
vector's own. -/
theorem padR_act (k m : Nat) (w : List BPair) (hw : w.length = m) :
    poly.oneValue (matVec (padR k m) w)
      (List.replicate k BPair.unit ++ w) := by
  show poly.oneValue
    (matVec (nullMat k m
      ++ matScaleB (BPair.ofPos Pos.one) (idMat m)) w) _
  rw [elim.matVec_append]
  refine poly.oneValue_append _ _ _ _ ?_ ?_ ?_
  · rw [matVec_length, length_nullMat, ground.length_replicate]
  · exact poly.unitTail_oneValue (elim.matVec_nullMat k m w)
      (poly.unitTail_replicate k)
  · exact poly.oneValue_trans (scaleId_act (BPair.ofPos Pos.one) m w hw)
      (elim.vecScale_one w)

/-- The right-padded vector's quadratic form at a join is the
trailing block's own: the coupling's exchange meets the unit family
and the join's upper half is paired against it. -/
private theorem quad_padJR (P B Q : Mat) (k m : Nat)
    (hJl : (List.zipWith (· ++ ·) P B).length = k)
    (hBt : (transposeM B).length = m)
    (hBtr : rowsLen k (transposeM B)) (hQl : Q.length = m)
    (w : List BPair) (hw : w.length = m) :
    (dotN (List.replicate k BPair.unit ++ w)
        (matVec (blockJoin P B Q)
          (List.replicate k BPair.unit ++ w))).oneValue
      (dotN w (matVec Q w)) := by
  have hU : poly.unitTail (List.replicate k BPair.unit) :=
    poly.unitTail_replicate k
  have hfst : (List.replicate k BPair.unit).length
      = (matVec (List.zipWith (· ++ ·) P B)
          (List.replicate k BPair.unit ++ w)).length := by
    rw [matVec_length, hJl]
    exact ground.length_replicate BPair.unit k
  show (dotN (List.replicate k BPair.unit ++ w)
      (matVec (List.zipWith (· ++ ·) P B
        ++ List.zipWith (· ++ ·) (transposeM B) Q)
        (List.replicate k BPair.unit ++ w))).oneValue
    (dotN w (matVec Q w))
  rw [elim.matVec_append]
  refine BPair.oneValue_trans (dotN_app _ w _ _ hfst) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (dotN_nullL _ _ hU) ?_) (BPair.unit_add _)
  refine BPair.oneValue_trans
    (dotN_congrR w _ _
      (elim.matVec_rowJoin k (transposeM B) Q
        (List.replicate k BPair.unit) w hBtr
        (ground.length_replicate BPair.unit k))) ?_
  refine BPair.oneValue_trans
    (elim.dotN_addRow_right w
      (matVec (transposeM B) (List.replicate k BPair.unit))
      (matVec Q w)
      ((matVec_length _ _).trans (hBt.trans hw.symm))
      ((matVec_length Q w).trans (hQl.trans hw.symm))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (dotN_nullR w _ (matVec_null (transposeM B) _ hU))
      (BPair.oneValue_refl _)) ?_
  exact BPair.unit_add _


/-- The pivot's padded vector against the trailing block's: the
off-block's own reading closes the crossing. -/
private theorem cross_padL_padR (P Q : Mat) (k m : Nat)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBt : (transposeM (nullMat k m)).length = m)
    (hBtr : rowsLen k (transposeM (nullMat k m)))
    (hQl : Q.length = m) (x w : List BPair) (hx : x.length = k) :
    (dotN (x ++ List.replicate m BPair.unit)
        (matVec (blockJoin P (nullMat k m) Q)
          (List.replicate k BPair.unit ++ w))).oneValue BPair.unit := by
  have hUm : poly.unitTail (List.replicate m BPair.unit) :=
    poly.unitTail_replicate m
  have hUk : poly.unitTail (List.replicate k BPair.unit) :=
    poly.unitTail_replicate k
  refine BPair.oneValue_trans
    (quadJoin P (nullMat k m) Q k m hPr hPl (length_nullMat k m) hBt hBtr
      hQl x _ _ w hx (ground.length_replicate BPair.unit m)
      (ground.length_replicate BPair.unit k)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (dotN_nullR x _ (matVec_null P _ hUk))
        (dotN_nullR x _ (elim.matVec_nullMat k m w)))
      (BPair.add_congr (dotN_nullL _ _ hUm) (dotN_nullL _ _ hUm))) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.add_unit BPair.unit)
      (BPair.add_unit BPair.unit))
    (BPair.add_unit BPair.unit)

/-- The trailing block's padded vector against the pivot's, the
crossing's partner read. -/
private theorem cross_padR_padL (P Q : Mat) (k m : Nat)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBt : (transposeM (nullMat k m)).length = m)
    (hBtr : rowsLen k (transposeM (nullMat k m)))
    (hQl : Q.length = m) (x w : List BPair) (hx : x.length = k)
    (hw : w.length = m) :
    (dotN (List.replicate k BPair.unit ++ w)
        (matVec (blockJoin P (nullMat k m) Q)
          (x ++ List.replicate m BPair.unit))).oneValue BPair.unit := by
  have hUm : poly.unitTail (List.replicate m BPair.unit) :=
    poly.unitTail_replicate m
  have hUk : poly.unitTail (List.replicate k BPair.unit) :=
    poly.unitTail_replicate k
  refine BPair.oneValue_trans
    (quadJoin P (nullMat k m) Q k m hPr hPl (length_nullMat k m) hBt hBtr
      hQl _ w x _ (ground.length_replicate BPair.unit k) hw hx) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (dotN_nullL _ _ hUk) (dotN_nullL _ _ hUk))
      (BPair.add_congr (dotN_nullR w _ (slabT_null k m x))
        (dotN_nullR w _ (matVec_null Q _ hUm)))) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.add_unit BPair.unit)
      (BPair.add_unit BPair.unit))
    (BPair.add_unit BPair.unit)

/-- The addition's whole content at one pair of arguments: the two
padded vectors' forms with the crossings at the sum's unit. -/
private theorem quadSplitZ (P Q : Mat) (k m : Nat) (x w : List BPair)
    (hx : x.length = k) (hw : w.length = m)
    (hSr : rowsLen (k + m) (blockJoin P (nullMat k m) Q))
    (hSl : (blockJoin P (nullMat k m) Q).length = k + m)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBt : (transposeM (nullMat k m)).length = m)
    (hBtr : rowsLen k (transposeM (nullMat k m)))
    (hQl : Q.length = m) :
    (dotN (vecAdd (matVec (padM k m) x) (matVec (padR k m) w))
        (matVec (blockJoin P (nullMat k m) Q)
          (vecAdd (matVec (padM k m) x)
            (matVec (padR k m) w)))).oneValue
      (dotN x (matVec P x) + dotN w (matVec Q w)) := by
  have hu : (matVec (padM k m) x).length = k + m :=
    (matVec_length _ x).trans (padM_len k m)
  have hv : (matVec (padR k m) w).length = k + m :=
    (matVec_length _ w).trans (padR_len k m)
  have hpu := padM_act k m x hx
  have hpv := padR_act k m w hw
  have hulen : (x ++ List.replicate m BPair.unit).length = k + m := by
    rw [ground.length_append, hx, ground.length_replicate]
  have hvlen : (List.replicate k BPair.unit ++ w).length = k + m := by
    rw [ground.length_append, hw, ground.length_replicate]
  refine BPair.oneValue_trans
    (quadAdd (blockJoin P (nullMat k m) Q) (k + m) hSr hSl _ _ hu hv) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr
        (BPair.oneValue_trans
          (quad_congr (blockJoin P (nullMat k m) Q) _ _ hpu)
          (quad_padJ P (nullMat k m) Q k m hPr hPl
            (length_nullMat k m) x hx))
        (BPair.oneValue_trans (dotN_congrL _ _ _ hpu)
          (BPair.oneValue_trans
            (dotN_congrR _ _ _ (matVec_congr (blockJoin P (nullMat k m) Q)
              _ _ hpv))
            (cross_padL_padR P Q k m hPr hPl hBt hBtr hQl x w hx))))
      (BPair.add_congr
        (BPair.oneValue_trans (dotN_congrL _ _ _ hpv)
          (BPair.oneValue_trans
            (dotN_congrR _ _ _ (matVec_congr (blockJoin P (nullMat k m) Q)
              _ _ hpu))
            (cross_padR_padL P Q k m hPr hPl hBt hBtr hQl x w hx hw)))
        (BPair.oneValue_trans
          (quad_congr (blockJoin P (nullMat k m) Q) _ _ hpv)
          (quad_padJR P (nullMat k m) Q k m
            (ground.length_zipWith (· ++ ·) P (nullMat k m) k hPl
              (length_nullMat k m)) hBt hBtr hQl w hw)))) ?_
  exact BPair.add_congr (BPair.add_unit _) (BPair.unit_add _)

private theorem padRFam_rows (k m : Nat) (L : Mat) :
    rowsLen (k + m) (L.map (matVec (padR k m))) :=
  rowsLen_map (matVec (padR k m)) (k + m) L (fun x _ => (fun y => (matVec_length _ y).trans (padR_len k m)) x)

private theorem padRFam_combo (k m : Nat) (cs : List BPair) (L : Mat)
    (hL : rowsLen m L) :
    poly.oneValue (combo (k + m) cs (L.map (matVec (padR k m))))
      (matVec (padR k m) (combo m cs L)) := by
  have h := matVec_combo (padR k m) m cs L hL
  rw [padR_len k m] at h
  exact poly.oneValue_symm h

/-- The joined family's combination at the two paddings: the two
halves' own combinations. -/
private theorem famComboZ (k m : Nat) (LP LQ : Mat)
    (hLP : rowsLen k LP) (hLQ : rowsLen m LQ) (cx cw : List BPair)
    (hcx : cx.length = (LP.map (matVec (padM k m))).length) :
    poly.oneValue
      (combo (k + m) (cx ++ cw)
        (LP.map (matVec (padM k m)) ++ LQ.map (matVec (padR k m))))
      (vecAdd (matVec (padM k m) (combo k cx LP))
        (matVec (padR k m) (combo m cw LQ))) := by
  have h1 := padFam_rows k m LP
  have h2 := padRFam_rows k m LQ
  refine poly.oneValue_trans (combo_append (k + m) cx _ cw _ hcx h1 h2) ?_
  exact elim.polyOne_vecAdd _ _ _ _ (padFam_combo k m cx LP hLP)
    (padRFam_combo k m cw LQ hLQ)
    ((length_combo (k + m) cx _ h1).trans
      ((matVec_length _ _).trans (padM_len k m)).symm)
    ((length_combo (k + m) cw _ h2).trans
      ((matVec_length _ _).trans (padR_len k m)).symm)

/-- The joined family's quadratic form: the pivot block's form at
the first half's combination joined to the trailing block's at the
second's. -/
private theorem quadFamZ (P Q : Mat) (k m : Nat) (LP LQ : Mat)
    (hLP : rowsLen k LP) (hLQ : rowsLen m LQ) (cx cw : List BPair)
    (hcx : cx.length = (LP.map (matVec (padM k m))).length)
    (hSr : rowsLen (k + m) (blockJoin P (nullMat k m) Q))
    (hSl : (blockJoin P (nullMat k m) Q).length = k + m)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBt : (transposeM (nullMat k m)).length = m)
    (hBtr : rowsLen k (transposeM (nullMat k m)))
    (hQl : Q.length = m) :
    (dotN
        (combo (k + m) (cx ++ cw)
          (LP.map (matVec (padM k m)) ++ LQ.map (matVec (padR k m))))
        (matVec (blockJoin P (nullMat k m) Q)
          (combo (k + m) (cx ++ cw)
            (LP.map (matVec (padM k m))
              ++ LQ.map (matVec (padR k m)))))).oneValue
      (dotN (combo k cx LP) (matVec P (combo k cx LP))
        + dotN (combo m cw LQ) (matVec Q (combo m cw LQ))) := by
  have hX : (combo k cx LP).length = k := length_combo k cx LP hLP
  have hW : (combo m cw LQ).length = m := length_combo m cw LQ hLQ
  have hcl : (combo (k + m) (cx ++ cw)
      (LP.map (matVec (padM k m))
        ++ LQ.map (matVec (padR k m)))).length = k + m :=
    length_combo (k + m) _ _
      (rowsLen_append (k + m) (padFam_rows k m LP) (padRFam_rows k m LQ))
  have hvl : (vecAdd (matVec (padM k m) (combo k cx LP))
      (matVec (padR k m) (combo m cw LQ))).length = k + m :=
    length_vecAdd _ _ (k + m)
      ((matVec_length _ _).trans (padM_len k m))
      ((matVec_length _ _).trans (padR_len k m))
  refine BPair.oneValue_trans
    (quad_congr (blockJoin P (nullMat k m) Q) _ _
      (famComboZ k m LP LQ hLP hLQ cx cw hcx)) ?_
  exact quadSplitZ P Q k m _ _ hX hW hSr hSl hPr hPl hBt hBtr hQl

/-- `lem:inertia`'s addition at a block diagonal: at a join whose
off-block reads equal members throughout, the assembled datum's
reversal count is the two blocks' counts' sum.  The three splits are
the theorem's data, and the count identity is read off them alone:
the two lower lists, each padded into its own half, force the count
from below, their complement counterparts from above. -/
theorem rev_join {k m : Nat} (P Q : Mat)
    (spP : Split k) (hp : splitRead P spP)
    (spQ : Split m) (hq : splitRead Q spQ)
    (spS : Split (k + m))
    (hS : splitRead (blockJoin P (nullMat k m) Q) spS) :
    revAt spS = revAt spP + revAt spQ := by
  have hS' : splitRead (blockJoin P (nullMat k m) Q) spS := hS
  have hPr : rowsLen k P := rowsLen_of_sqAt hp.1
  have hPl : P.length = k := sqAt_len hp.1
  have hQl : Q.length = m := sqAt_len hq.1
  have hSr : rowsLen (k + m) (blockJoin P (nullMat k m) Q) :=
    rowsLen_of_sqAt hS'.1
  have hSl : (blockJoin P (nullMat k m) Q).length = k + m :=
    sqAt_len hS'.1
  have hBtr : rowsLen k (transposeM (nullMat k m)) :=
    rowsLen_cast (length_nullMat k m) (rowsLen_transposeM (nullMat k m))
  have hBt : (transposeM (nullMat k m)).length = m := by
    cases Nat.eq_zero_or_pos k with
    | inl hk =>
      have hZ0 : nullMat k m = [] := by
        show List.replicate k (List.replicate m BPair.unit) = []
        rw [hk]
        rfl
      have h0 : (blockJoin P (nullMat k m) Q).length = 0 := by
        rw [hZ0]
        show (List.zipWith (· ++ ·) P ([] : Mat)
          ++ List.zipWith (· ++ ·) (transposeM ([] : Mat)) Q).length = 0
        rw [ground.zipWith_nil_right (· ++ ·) P]
        rfl
      have h1 : (0 : Nat) = k + m := h0.symm.trans hSl
      rw [hk, Nat.zero_add] at h1
      rw [hZ0]
      exact h1
    | inr hk =>
      exact length_transposeM (nullMat k m) (rowsLen_nullMat k m)
        (by rw [length_nullMat]; exact hk)
  have hge : revAt spP + revAt spQ ≤ revAt spS := by
    have hstrict : ∀ cs : List BPair,
        cs.length = ((lowerList spP).map (matVec (padM k m))
          ++ (lowerList spQ).map (matVec (padR k m))).length →
        ¬ poly.unitTail cs →
        dotN (combo (k + m) cs ((lowerList spP).map (matVec (padM k m))
            ++ (lowerList spQ).map (matVec (padR k m))))
          (matVec (blockJoin P (nullMat k m) Q)
            (combo (k + m) cs
              ((lowerList spP).map (matVec (padM k m))
                ++ (lowerList spQ).map (matVec (padR k m)))))
          < BPair.unit := by
      intro cs hcs hoff
      have hlen : cs.length
          = ((lowerList spP).map (matVec (padM k m))).length
            + ((lowerList spQ).map (matVec (padR k m))).length := by
        rw [hcs, ground.length_append]
      obtain ⟨cx, cw, rfl, hlx⟩ :=
        listSplit cs ((lowerList spP).map (matVec (padM k m))).length
          (by rw [hlen]; exact Nat.le_add_right _ _)
      have h1 : cx.length + cw.length
          = ((lowerList spP).map (matVec (padM k m))).length
            + ((lowerList spQ).map (matVec (padR k m))).length := by
        rw [← ground.length_append cx cw]
        exact hlen
      rw [hlx] at h1
      have hlw : cw.length
          = ((lowerList spQ).map (matVec (padR k m))).length :=
        ground.addCancelL _ h1
      have hXlen : cx.length = revAt spP := by
        rw [hlx, ground.length_map]
        exact lowerList_length P spP hp
      have hWlen : cw.length = revAt spQ := by
        rw [hlw, ground.length_map]
        exact lowerList_length Q spQ hq
      refine BPair.lt_congr
        (BPair.oneValue_symm
          (quadFamZ P Q k m (lowerList spP) (lowerList spQ)
            (lowerList_rowsLen spP) (lowerList_rowsLen spQ) cx cw hlx
            hSr hSl hPr hPl hBt hBtr hQl))
        (BPair.oneValue_refl BPair.unit) ?_
      cases (inferInstance : Decidable (poly.unitTail cx)) with
      | isTrue hux =>
        refine leAddLtUnit ?_
          (lowerList_strict Q spQ hq cw hWlen
            (fun hcw => hoff (unitTail_append hux hcw)))
        exact ground.leB_congr_left
          (BPair.oneValue_symm
            (quadNull P _ (unitTail_combo_of k cx (lowerList spP) hux)))
          (ground.leB_refl BPair.unit)
      | isFalse hux =>
        refine ltUnitAddLe (lowerList_strict P spP hp cx hXlen hux) ?_
        cases (inferInstance : Decidable (poly.unitTail cw)) with
        | isTrue huw =>
          exact ground.leB_congr_left
            (BPair.oneValue_symm
              (quadNull Q _ (unitTail_combo_of m cw (lowerList spQ) huw)))
            (ground.leB_refl BPair.unit)
        | isFalse huw =>
          exact ground.leB_of_lt (lowerList_strict Q spQ hq cw hWlen huw)
    have hfin := forcing (blockJoin P (nullMat k m) Q) spS hS'
      ((lowerList spP).map (matVec (padM k m))
        ++ (lowerList spQ).map (matVec (padR k m)))
      (rowsLen_append (k + m) (padFam_rows k m (lowerList spP))
        (padRFam_rows k m (lowerList spQ))) hstrict
    rw [ground.length_append, ground.length_map, ground.length_map,
      lowerList_length P spP hp, lowerList_length Q spQ hq] at hfin
    exact hfin
  have hle : revAt spS ≤ revAt spP + revAt spQ := by
    have hMr : rowsLen (k + m)
        ((complList spP).map (matVec (padM k m))
          ++ (complList spQ).map (matVec (padR k m))) :=
      rowsLen_append (k + m) (padFam_rows k m (complList spP))
        (padRFam_rows k m (complList spQ))
    have hind : ∀ cs : List BPair,
        cs.length = ((complList spP).map (matVec (padM k m))
          ++ (complList spQ).map (matVec (padR k m))).length →
        poly.unitTail (combo (k + m) cs
          ((complList spP).map (matVec (padM k m))
            ++ (complList spQ).map (matVec (padR k m)))) →
        poly.unitTail cs := by
      intro cs hcs hu
      have hlen : cs.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spQ).map (matVec (padR k m))).length := by
        rw [hcs, ground.length_append]
      obtain ⟨cx, cw, rfl, hlx⟩ :=
        listSplit cs ((complList spP).map (matVec (padM k m))).length
          (by rw [hlen]; exact Nat.le_add_right _ _)
      have h1 : cx.length + cw.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spQ).map (matVec (padR k m))).length := by
        rw [← ground.length_append cx cw]
        exact hlen
      rw [hlx] at h1
      have hlw : cw.length
          = ((complList spQ).map (matVec (padR k m))).length :=
        ground.addCancelL _ h1
      have hXlen : cx.length = (complList spP).length := by
        rw [hlx, ground.length_map]
      have hWlen : cw.length = (complList spQ).length := by
        rw [hlw, ground.length_map]
      have hX : (combo k cx (complList spP)).length = k :=
        length_combo k cx _ (complList_rowsLen spP)
      have hW : (combo m cw (complList spQ)).length = m :=
        length_combo m cw _ (complList_rowsLen spQ)
      have hu2 : poly.unitTail
          (vecAdd (matVec (padM k m) (combo k cx (complList spP)))
            (matVec (padR k m) (combo m cw (complList spQ)))) :=
        poly.unitTail_oneValue_right hu
          (famComboZ k m (complList spP) (complList spQ)
            (complList_rowsLen spP) (complList_rowsLen spQ) cx cw hlx)
      have hpu := padM_act k m (combo k cx (complList spP)) hX
      have hpv := padR_act k m (combo m cw (complList spQ)) hW
      have hulen : ((combo k cx (complList spP))
          ++ List.replicate m BPair.unit).length = k + m := by
        rw [ground.length_append, hX, ground.length_replicate]
      have hvlen : (List.replicate k BPair.unit
          ++ (combo m cw (complList spQ))).length = k + m := by
        rw [ground.length_append, hW, ground.length_replicate]
      have hu3 : poly.unitTail
          (vecAdd ((combo k cx (complList spP))
              ++ List.replicate m BPair.unit)
            (List.replicate k BPair.unit
              ++ (combo m cw (complList spQ)))) :=
        poly.unitTail_oneValue_right hu2
          (elim.polyOne_vecAdd _ _ _ _ hpu hpv
            (((matVec_length _ _).trans (padM_len k m)).trans hulen.symm)
            (((matVec_length _ _).trans (padR_len k m)).trans hvlen.symm))
      rw [vecAdd_app (combo k cx (complList spP)) _
        (List.replicate k BPair.unit) _
        (hX.trans (ground.length_replicate BPair.unit k).symm)] at hu3
      have hXnull : poly.unitTail (combo k cx (complList spP)) :=
        unitTailAddRight _ _
          (hX.trans (ground.length_replicate BPair.unit k).symm)
          (poly.unitTail_replicate k) (elim.unitTail_append_split _ _ hu3).1
      have hWnull : poly.unitTail (combo m cw (complList spQ)) :=
        unitTailAddLeft _ _
          ((ground.length_replicate BPair.unit m).trans hW.symm)
          (poly.unitTail_replicate m) (elim.unitTail_append_split _ _ hu3).2
      exact unitTail_append (complList_indep P spP hp cx hXlen hXnull)
        (complList_indep Q spQ hq cw hWlen hWnull)
    have hside : ∀ cs : List BPair,
        cs.length = ((complList spP).map (matVec (padM k m))
          ++ (complList spQ).map (matVec (padR k m))).length →
        ¬ (dotN (combo (k + m) cs
            ((complList spP).map (matVec (padM k m))
              ++ (complList spQ).map (matVec (padR k m))))
          (matVec (blockJoin P (nullMat k m) Q)
            (combo (k + m) cs
              ((complList spP).map (matVec (padM k m))
                ++ (complList spQ).map (matVec (padR k m)))))
          < BPair.unit) := by
      intro cs hcs
      have hlen : cs.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spQ).map (matVec (padR k m))).length := by
        rw [hcs, ground.length_append]
      obtain ⟨cx, cw, rfl, hlx⟩ :=
        listSplit cs ((complList spP).map (matVec (padM k m))).length
          (by rw [hlen]; exact Nat.le_add_right _ _)
      have h1 : cx.length + cw.length
          = ((complList spP).map (matVec (padM k m))).length
            + ((complList spQ).map (matVec (padR k m))).length := by
        rw [← ground.length_append cx cw]
        exact hlen
      rw [hlx] at h1
      have hlw : cw.length
          = ((complList spQ).map (matVec (padR k m))).length :=
        ground.addCancelL _ h1
      have hXlen : cx.length = (complList spP).length := by
        rw [hlx, ground.length_map]
      have hWlen : cw.length = (complList spQ).length := by
        rw [hlw, ground.length_map]
      intro hlt
      refine ground.leB_not_lt
        (unitLeAdd
          (ground.leB_of_not_lt (complList_side P spP hp cx hXlen))
          (ground.leB_of_not_lt (complList_side Q spQ hq cw hWlen))) ?_
      exact BPair.lt_congr
        (quadFamZ P Q k m (complList spP) (complList spQ)
          (complList_rowsLen spP) (complList_rowsLen spQ) cx cw hlx
          hSr hSl hPr hPl hBt hBtr hQl)
        (BPair.oneValue_refl BPair.unit) hlt
    have hup := forcing_upper (blockJoin P (nullMat k m) Q) spS hS'
      ((complList spP).map (matVec (padM k m))
        ++ (complList spQ).map (matVec (padR k m))) hMr hind hside
    rw [ground.length_append, ground.length_map, ground.length_map] at hup
    have hkey : (complList spP).length + (complList spQ).length + revAt spS
        ≤ (revAt spP + (complList spP).length)
          + (revAt spQ + (complList spQ).length) := by
      rw [complList_length P spP hp, complList_length Q spQ hq]
      exact hup
    rw [Nat.add_add_add_comm (revAt spP) (complList spP).length (revAt spQ)
        (complList spQ).length,
      Nat.add_comm ((complList spP).length + (complList spQ).length)
        (revAt spS)] at hkey
    exact ground.leCancelR _ hkey
  exact Nat.le_antisymm hle hge

/-- The deviation padded at the trailing block: the vacant leading
rows above the deviation's rows at the vacant leading columns, the
padded datum total at every leading order with the vacant order
reading the deviation itself — `lem:inertia`'s addition at a block
diagonal read at a vacant leading summand. -/
def trailPad (k : Nat) (D : Mat) : Mat :=
  nullMat k (k + D.length)
    ++ D.map (fun r => List.replicate k BPair.unit ++ r)

/-- The leading identity padded at the joined order: the identity's
rows at the vacant trailing columns above the vacant trailing rows,
the drift's diagonal at the two heads' tie, total at every leading
order. -/
def headId (k m : Nat) : Mat :=
  (idMat k).map (fun r => r ++ List.replicate m BPair.unit)
    ++ nullMat m (k + m)

/-- A datum supported at the leading block: the block's rows extended
by the sum's unit to the joined order, rows of the sum's unit
beneath — `trailPad`'s mirror, `headId`'s general carrier. -/
def headPad (m : Nat) (D : Mat) : Mat :=
  D.map (fun r => r ++ List.replicate m BPair.unit)
    ++ nullMat m (D.length + m)

/-- The padded datum is square at the joined order. -/
theorem sqAt_headPad {n : Nat} (m : Nat) (A : Mat) (hsq : sqAt A n) :
    sqAt (headPad m A) (n + m) := by
  have hAl : A.length = n := sqAt_len hsq
  have hAr : rowsLen n A := rowsLen_of_sqAt hsq
  refine sqAt_of ?_ ?_
  · show ((A.map (fun r => r ++ List.replicate m BPair.unit))
      ++ nullMat m (A.length + m)).length = n + m
    rw [ground.length_append, ground.length_map, length_nullMat, hAl]
  · show rowsLen (n + m)
      ((A.map (fun r => r ++ List.replicate m BPair.unit))
        ++ nullMat m (A.length + m))
    refine rowsLen_append (n + m) ?_ ?_
    · refine rowsLen_map _ (n + m) A (fun r hr => ?_)
      rw [ground.length_append, ground.length_replicate,
        rowsLen_of_mem hAr hr]
    · rw [hAl]
      exact rowsLen_replicate (n + m) m

/-- The padded datum's head rows read the block's own rows: the
trailing columns of the sum's unit are read off. -/
private theorem getAt_headPad_lo {n : Nat} (m : Nat) (M : Mat)
    (hMl : M.length = n) (i j : Nat) (hi : i < n) :
    ground.getAt BPair.unit (ground.getAt [] (headPad m M) i) j
      = ground.getAt BPair.unit (ground.getAt [] M i) j := by
  have hexp : headPad m M
      = M.map (fun r => r ++ List.replicate m BPair.unit)
        ++ List.replicate m (List.replicate (n + m) BPair.unit) :=
    congrArg (fun t => M.map (fun r => r ++ List.replicate m BPair.unit)
      ++ List.replicate m (List.replicate (t + m) BPair.unit)) hMl
  rw [hexp, ground.getAt_append, ground.length_map, hMl, if_pos hi,
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (fun r => r ++ List.replicate m BPair.unit) M i
      (by rw [hMl]; exact hi),
    ground.getAt_append_replicate]

/-- The padded datum's trailing rows are the sum's unit at every
column key. -/
private theorem getAt_headPad_hi {n : Nat} (m : Nat) (M : Mat)
    (hMl : M.length = n) (i j : Nat) (hi : ¬ i < n) :
    ground.getAt BPair.unit (ground.getAt [] (headPad m M) i) j
      = BPair.unit := by
  have hexp : headPad m M
      = M.map (fun r => r ++ List.replicate m BPair.unit)
        ++ List.replicate m (List.replicate (n + m) BPair.unit) :=
    congrArg (fun t => M.map (fun r => r ++ List.replicate m BPair.unit)
      ++ List.replicate m (List.replicate (t + m) BPair.unit)) hMl
  rw [hexp, ground.getAt_append, ground.length_map, hMl, if_neg hi]
  by_cases hk : i - n < m
  · rw [ground.getAt_replicate ([] : List BPair)
      (List.replicate (n + m) BPair.unit) m (i - n) hk,
      ground.getAt_replicate_self BPair.unit]
  · rw [ground.getAt_over ([] : List BPair)
      (List.replicate m (List.replicate (n + m) BPair.unit)) (i - n)
      (by rw [ground.length_replicate]; exact Nat.le_of_not_lt hk)]
    rfl

/-- The padded datum's transpose is the transpose padded: the pad's
unit columns cross to unit rows. -/
theorem transposeM_headPad {n : Nat} (m : Nat) (A : Mat)
    (hsq : sqAt A n) :
    transposeM (headPad m A) = headPad m (transposeM A) := by
  have hAl : A.length = n := sqAt_len hsq
  have hAr : rowsLen n A := rowsLen_of_sqAt hsq
  have hHsq : sqAt (headPad m A) (n + m) := sqAt_headPad m A hsq
  have hHl : (headPad m A).length = n + m := sqAt_len hHsq
  have hHr : rowsLen (n + m) (headPad m A) := rowsLen_of_sqAt hHsq
  have hTl : (transposeM (headPad m A)).length = n + m :=
    transposeLen (headPad m A) hHr hHl
  have hTr : rowsLen (n + m) (transposeM (headPad m A)) :=
    rowsLen_cast hHl (rowsLen_transposeM (headPad m A))
  have hATl : (transposeM A).length = n := transposeLen A hAr hAl
  have hATr : rowsLen n (transposeM A) :=
    rowsLen_cast hAl (rowsLen_transposeM A)
  have hRsq : sqAt (headPad m (transposeM A)) (n + m) :=
    sqAt_headPad m (transposeM A) (sqAt_of hATl hATr)
  have hRl : (headPad m (transposeM A)).length = n + m := sqAt_len hRsq
  have hRr : rowsLen (n + m) (headPad m (transposeM A)) :=
    rowsLen_of_sqAt hRsq
  refine ground.getAt_ext ([] : List BPair) _ _ (hTl.trans hRl.symm) ?_
  intro p hp
  rw [hTl] at hp
  refine ground.getAt_ext BPair.unit _ _ ?_ ?_
  · rw [rowsLen_getAt _ p hTr (by rw [hTl]; exact hp),
      rowsLen_getAt _ p hRr (by rw [hRl]; exact hp)]
  · intro q hq
    rw [rowsLen_getAt _ p hTr (by rw [hTl]; exact hp)] at hq
    rw [getAt_transposeM BPair.unit (headPad m A) hHr p q hp
      (by rw [hHl]; exact hq)]
    by_cases hpn : p < n
    · by_cases hqn : q < n
      · rw [getAt_headPad_lo m A hAl q p hqn,
          getAt_headPad_lo m (transposeM A) hATl p q hpn,
          getAt_transposeM BPair.unit A hAr p q hpn
            (by rw [hAl]; exact hqn)]
      · rw [getAt_headPad_hi m A hAl q p hqn,
          getAt_headPad_lo m (transposeM A) hATl p q hpn,
          ground.getAt_over BPair.unit _ q
            (by rw [rowsLen_getAt _ p hATr (by rw [hATl]; exact hpn)]
                exact Nat.le_of_not_lt hqn)]
    · by_cases hqn : q < n
      · rw [getAt_headPad_lo m A hAl q p hqn,
          getAt_headPad_hi m (transposeM A) hATl p q hpn,
          ground.getAt_over BPair.unit _ p
            (by rw [rowsLen_getAt _ q hAr (by rw [hAl]; exact hqn)]
                exact Nat.le_of_not_lt hpn)]
      · rw [getAt_headPad_hi m A hAl q p hqn,
          getAt_headPad_hi m (transposeM A) hATl p q hpn]

/-- Two matched row lists pad row by row at one value. -/
private theorem padCongrGo (m : Nat) : ∀ (M N : Mat) (kk : Nat),
    rowsLen kk M → rowsLen kk N → matOneValue M N →
    matOneValue
      (M.map (fun r => r ++ List.replicate m BPair.unit))
      (N.map (fun r => r ++ List.replicate m BPair.unit))
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, _, h => (h : False).elim
  | _ :: _, [], _, _, _, h => (h : False).elim
  | r :: M, r' :: N, kk, hMr, hNr, h =>
    ⟨poly.oneValue_append r r' _ _ (hMr.1.trans hNr.1.symm) h.1
      (poly.oneValue_refl _),
     padCongrGo m M N kk hMr.2 hNr.2 h.2⟩

/-- The padded datum keeps the entrywise read: two matrices at one
value pad to one value, the extension's rows the unit's own. -/
theorem headPad_congr {M N : Mat} {kk : Nat} (m : Nat)
    (hMr : rowsLen kk M) (hNr : rowsLen kk N)
    (h : matOneValue M N) :
    matOneValue (headPad m M) (headPad m N) := by
  show matOneValue
    (M.map (fun r => r ++ List.replicate m BPair.unit)
      ++ nullMat m (M.length + m))
    (N.map (fun r => r ++ List.replicate m BPair.unit)
      ++ nullMat m (N.length + m))
  rw [show N.length = M.length from (matOne_length h).symm]
  exact elim.matOne_append _ _ _ _ (padCongrGo m M N kk hMr hNr h)
    (ground.matched_refl (fun r => poly.oneValue_refl r) _)

/-- The head-supported datum's form at a joined vector reads the
block's own at the leading part: the extension's trailing rows and
columns act at the sum's unit. -/
theorem quadForm_headPad {n : Nat} (m : Nat) (A : Mat)
    (hAr : rowsLen n A) (hAl : A.length = n)
    (x y : List BPair) (hx : x.length = n) :
    (quadForm (headPad m A) (x ++ y)).oneValue (quadForm A x) := by
  have hact : poly.oneValue
      (matVec (headPad m A) (x ++ y))
      (matVec A x
        ++ matVec (nullMat m (A.length + m)) (x ++ y)) := by
    show poly.oneValue
      (matVec (A.map (fun r => r ++ List.replicate m BPair.unit)
        ++ nullMat m (A.length + m)) (x ++ y)) _
    rw [elim.matVec_append]
    refine poly.oneValue_append _ _ _ _ ?_ ?_ (poly.oneValue_refl _)
    · rw [show (matVec (A.map
          (fun r => r ++ List.replicate m BPair.unit)) (x ++ y)).length
        = A.length from
          (ground.length_map _ _).trans (ground.length_map _ _),
        show (matVec A x).length = A.length from ground.length_map _ _]
    · show poly.oneValue
        ((A.map (fun r => r ++ List.replicate m BPair.unit)).map
          (fun r => dotN r (x ++ y)))
        (A.map (fun r => dotN r x))
      rw [ground.map_map]
      refine poly.oneValue_map _ _ A ?_
      intro r hr
      refine BPair.oneValue_trans
        (dotN_app r (List.replicate m BPair.unit) x y
          ((elim.rowsLen_of_mem hAr hr).trans hx.symm)) ?_
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (dotN_nullL _ y (poly.unitTail_replicate m)))
        (BPair.add_unit _)
  refine BPair.oneValue_trans
    (elim.dotN_congrR (x ++ y) _ _ hact) ?_
  refine BPair.oneValue_trans
    (dotN_app x y (matVec A x) _
      (hx.trans ((ground.length_map _ _).trans hAl).symm)) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (elim.dotN_read y _)
        (elim.dotP_null_tail_right y _
          (elim.matVec_nullMat m _ (x ++ y)))))
    (BPair.add_unit _)

/-- The head-supported datum's pairing at joined vectors reads the
block's own at the leading parts: the extension's trailing rows and
columns act at the sum's unit. -/
theorem pair_headPad {n : Nat} (m : Nat) (A : Mat)
    (hAr : rowsLen n A) (hAl : A.length = n)
    (x y x' y' : List BPair) (hx : x.length = n) (hx' : x'.length = n) :
    (dotN (x ++ y) (matVec (headPad m A) (x' ++ y'))).oneValue
      (dotN x (matVec A x')) := by
  have hact : poly.oneValue
      (matVec (headPad m A) (x' ++ y'))
      (matVec A x'
        ++ matVec (nullMat m (A.length + m)) (x' ++ y')) := by
    show poly.oneValue
      (matVec (A.map (fun r => r ++ List.replicate m BPair.unit)
        ++ nullMat m (A.length + m)) (x' ++ y')) _
    rw [elim.matVec_append]
    refine poly.oneValue_append _ _ _ _ ?_ ?_ (poly.oneValue_refl _)
    · rw [show (matVec (A.map
          (fun r => r ++ List.replicate m BPair.unit)) (x' ++ y')).length
        = A.length from
          (ground.length_map _ _).trans (ground.length_map _ _),
        show (matVec A x').length = A.length from ground.length_map _ _]
    · show poly.oneValue
        ((A.map (fun r => r ++ List.replicate m BPair.unit)).map
          (fun r => dotN r (x' ++ y')))
        (A.map (fun r => dotN r x'))
      rw [ground.map_map]
      refine poly.oneValue_map _ _ A ?_
      intro r hr
      refine BPair.oneValue_trans
        (dotN_app r (List.replicate m BPair.unit) x' y'
          ((elim.rowsLen_of_mem hAr hr).trans hx'.symm)) ?_
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (dotN_nullL _ y' (poly.unitTail_replicate m)))
        (BPair.add_unit _)
  refine BPair.oneValue_trans
    (elim.dotN_congrR (x ++ y) _ _ hact) ?_
  refine BPair.oneValue_trans
    (dotN_app x y (matVec A x') _
      (hx.trans ((ground.length_map _ _).trans hAl).symm)) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (elim.dotN_read y _)
        (elim.dotP_null_tail_right y _
          (elim.matVec_nullMat m _ (x' ++ y')))))
    (BPair.add_unit _)

/-! The join's row reads and its algebra: a row of the join is the
two groups' own rows appended, the weightings and the entrywise sum
pass through the join block by block, and the two pads peel one
leading slab — `thm:groundreads`(iii)'s head tie consumes the tier
at the decimated heads' slabs. -/

/-- The join's leading rows: the leading block's row against the
coupling's. -/
theorem blockJoin_rowP {k : Nat} (P B Q : Mat)
    (hPl : P.length = k) (hBl : B.length = k)
    (r : Nat) (hr : r < k) :
    ground.getAt ([] : List BPair) (blockJoin P B Q) r
      = ground.getAt [] P r ++ ground.getAt [] B r := by
  show ground.getAt ([] : List BPair)
    (List.zipWith (· ++ ·) P B
      ++ List.zipWith (· ++ ·) (transposeM B) Q) r = _
  rw [ground.getAt_append ([] : List BPair) _ _ r,
    if_pos (show r < (List.zipWith (· ++ ·) P B).length by
      rw [ground.length_zipWith _ P B k hPl hBl]; exact hr)]
  exact ground.getAt_zipWith [] [] [] (· ++ ·) P B r
    (by rw [hPl]; exact hr) (by rw [hBl]; exact hr)

/-- The join's trailing rows: the coupling's exchanged row against
the trailing block's. -/
theorem blockJoin_rowQ {k m : Nat} (P B Q : Mat)
    (hPl : P.length = k) (hBl : B.length = k)
    (hBtl : (transposeM B).length = m) (hQl : Q.length = m)
    (r : Nat) (hrm : r < m) :
    ground.getAt ([] : List BPair) (blockJoin P B Q) (k + r)
      = ground.getAt [] (transposeM B) r ++ ground.getAt [] Q r := by
  show ground.getAt ([] : List BPair)
    (List.zipWith (· ++ ·) P B
      ++ List.zipWith (· ++ ·) (transposeM B) Q) (k + r) = _
  have hz : (List.zipWith (· ++ ·) P B).length = k :=
    ground.length_zipWith _ P B k hPl hBl
  rw [show k + r = (List.zipWith (· ++ ·) P B).length + r by rw [hz],
    ground.getAt_append_add ([] : List BPair) _ _ r]
  exact ground.getAt_zipWith [] [] [] (· ++ ·) _ Q r
    (by rw [hBtl]; exact hrm) (by rw [hQl]; exact hrm)

/-- The join's row count at the stated frames. -/
theorem blockJoin_len {k m : Nat} (P B Q : Mat)
    (hPl : P.length = k) (hBl : B.length = k)
    (hBtl : (transposeM B).length = m) (hQl : Q.length = m) :
    (blockJoin P B Q).length = k + m := by
  show (List.zipWith (· ++ ·) P B
    ++ List.zipWith (· ++ ·) (transposeM B) Q).length = k + m
  rw [ground.length_append,
    ground.length_zipWith _ P B k hPl hBl,
    ground.length_zipWith _ _ Q m hBtl hQl]

private theorem scaleZip (c : Pos) : ∀ (A B : Mat),
    matScale c (List.zipWith (· ++ ·) A B)
      = List.zipWith (· ++ ·) (matScale c A) (matScale c B)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: A, b :: B => by
    show (a ++ b).map (fun x => x.scale c)
        :: matScale c (List.zipWith (· ++ ·) A B)
      = (a.map (fun x => x.scale c) ++ b.map (fun x => x.scale c))
        :: List.zipWith (· ++ ·) (matScale c A) (matScale c B)
    rw [ground.map_append, scaleZip c A B]

private theorem scaleBZip (w : BPair) : ∀ (A B : Mat),
    matScaleB w (List.zipWith (· ++ ·) A B)
      = List.zipWith (· ++ ·) (matScaleB w A) (matScaleB w B)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: A, b :: B => by
    show poly.scaleP w (a ++ b)
        :: matScaleB w (List.zipWith (· ++ ·) A B)
      = (poly.scaleP w a ++ poly.scaleP w b)
        :: List.zipWith (· ++ ·) (matScaleB w A) (matScaleB w B)
    show (a ++ b).map (fun x => (w * x).norm)
        :: matScaleB w (List.zipWith (· ++ ·) A B) = _
    rw [ground.map_append, scaleBZip w A B]
    rfl

private theorem zipAdd4 {a : Nat} : ∀ (A B C D : Mat),
    rowsLen a A → rowsLen a C →
    List.zipWith (List.zipWith BPair.add)
        (List.zipWith (· ++ ·) A B) (List.zipWith (· ++ ·) C D)
      = List.zipWith (· ++ ·)
        (List.zipWith (List.zipWith BPair.add) A C)
        (List.zipWith (List.zipWith BPair.add) B D)
  | [], _, _, _, _, _ => rfl
  | _ :: _, [], [], _, _, _ => rfl
  | _ :: _, [], _ :: _, [], _, _ => rfl
  | _ :: _, [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _, _ => rfl
  | p1 :: A, b1 :: B, p2 :: C, b2 :: D, hA, hC => by
    show List.zipWith BPair.add (p1 ++ b1) (p2 ++ b2)
        :: List.zipWith (List.zipWith BPair.add)
          (List.zipWith (· ++ ·) A B) (List.zipWith (· ++ ·) C D)
      = (List.zipWith BPair.add p1 p2 ++ List.zipWith BPair.add b1 b2)
        :: _
    rw [ground.zipWith_append BPair.add p1 b1 p2 b2
      (hA.1.trans hC.1.symm), zipAdd4 A B C D hA.2 hC.2]


/-! The weighting's scalar algebra: the weight's congruence, the
two weightings' join at their weights' sum, and the unit weight's
read.  `lem:fiberdec`'s doubling collects its constants through
these. -/


private theorem vecScaleB_add (a b : BPair) : ∀ r : List BPair,
    poly.oneValue
      (vecAdd (poly.scaleP a r) (poly.scaleP b r))
      (poly.scaleP (a + b) r)
  | [] => trivial
  | x :: r =>
    ⟨BPair.oneValue_trans
      (BPair.add_congr (BPair.norm_oneValue _) (BPair.norm_oneValue _))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.right_distrib a b x).symm)
        (BPair.oneValue_symm (BPair.norm_oneValue _))),
     vecScaleB_add a b r⟩

/-- Two weightings of one matrix join at their weights' sum. -/
theorem matScaleB_add (a b : BPair) : ∀ M : Mat,
    matOneValue (matAdd (matScaleB a M) (matScaleB b M))
      (matScaleB (a + b) M)
  | [] => trivial
  | r :: t => ⟨vecScaleB_add a b r, matScaleB_add a b t⟩

/-- The unit weighting is the matrix itself at the one-value
read. -/
theorem matScaleB_one : ∀ M : Mat,
    matOneValue (matScaleB (BPair.ofNat 1) M) M
  | [] => trivial
  | r :: t => ⟨poly.scaleP_one r, matScaleB_one t⟩

/-- The identity's product is read off: at a stated order the
identity against a matrix of that many rows is the matrix itself,
the one-index pairing at the diagonal key (`def:elim`). -/
theorem idMat_matMul {k : Nat} (n : Nat) (X : Mat) (hX : rowsLen k X)
    (hXl : X.length = n) (hn : 0 < n) :
    matOneValue (matMul (idMat n) X) X := by
  have hid : (idMat n).length = n := idMat_len n
  have hMl : (matMul (idMat n) X).length = n :=
    (length_matMul (idMat n) X).trans hid
  have hXt : (transposeM X).length = k :=
    length_transposeM X hX (by rw [hXl]; exact hn)
  have hrl : (List.range n).length = n := ground.length_range n
  refine matOne_getAt _ _ (by rw [hMl, hXl]) ?_
  intro i hi
  rw [hMl] at hi
  rw [getAt_matMul (idMat n) X i (by rw [hid]; exact hi)]
  have hrowLen : ((transposeM X).map
      (fun c => dotN (ground.getAt [] (idMat n) i) c)).length = k := by
    rw [ground.length_map, hXt]
  refine poly.oneValue_of_entries _ _
    (by rw [hrowLen, rowsLen_getAt X i hX (by rw [hXl]; exact hi)]) ?_
  intro j hj
  rw [hrowLen] at hj
  rw [ground.getAt_map ([] : List BPair) BPair.unit
    (fun c => dotN (ground.getAt [] (idMat n) i) c) (transposeM X) j
    (by rw [hXt]; exact hj)]
  have hcolLen : (ground.getAt ([] : List BPair) (transposeM X) j).length
      = n := by
    rw [rowsLen_getAt (transposeM X) j (rowsLen_transposeM X)
      (by rw [hXt]; exact hj), hXl]
  have hoff : ∀ q, q < (elim.idRow n i).length → ¬ q = i →
      (ground.getAt BPair.unit (elim.idRow n i) q).oneValue
        BPair.unit := by
    intro q hq hne
    rw [elim.length_idRow] at hq
    rw [elim.getAt_idRow n i q hq, if_neg hne]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans
    (dotN_read (ground.getAt [] (idMat n) i)
      (ground.getAt [] (transposeM X) j)) ?_
  rw [idMat_row n i hi,
    dotP_comm (elim.idRow n i) (ground.getAt [] (transposeM X) j)]
  refine BPair.oneValue_trans
    (dotP_oneIndex (ground.getAt ([] : List BPair) (transposeM X) j) _ i
      (by rw [hcolLen, elim.length_idRow])
      (by rw [elim.length_idRow]; exact hi) hoff) ?_
  rw [elim.getAt_idRow n i i hi, if_pos rfl,
    getAt_transposeM BPair.unit X hX j i hj (by rw [hXl]; exact hi)]
  exact BPair.mul_ofNat_one _

/-- The identity matrix is its own transpose, the entry test's
symmetry. -/
theorem transposeM_idMat : ∀ n : Nat,
    transposeM (idMat n) = idMat n
  | 0 => rfl
  | k + 1 => by
    have hn : 0 < k + 1 := Nat.succ_pos k
    have hlt : (transposeM (idMat (k + 1))).length = k + 1 :=
      length_transposeM (idMat (k + 1)) (idMat_rows (k + 1))
        (by rw [idMat_len (k + 1)]; exact hn)
    refine ground.getAt_ext ([] : List BPair) _ _
      (by rw [hlt, idMat_len (k + 1)]) ?_
    intro i hi
    rw [hlt] at hi
    refine ground.getAt_ext BPair.unit _ _
      (by rw [rowsLen_getAt (transposeM (idMat (k + 1))) i
          (rowsLen_transposeM (idMat (k + 1))) (by rw [hlt]; exact hi),
        idMat_len (k + 1),
        rowsLen_getAt (idMat (k + 1)) i (idMat_rows (k + 1))
          (by rw [idMat_len (k + 1)]; exact hi)]) ?_
    intro j hj
    rw [rowsLen_getAt (transposeM (idMat (k + 1))) i
        (rowsLen_transposeM (idMat (k + 1))) (by rw [hlt]; exact hi),
      idMat_len (k + 1)] at hj
    rw [getAt_transposeM BPair.unit (idMat (k + 1)) (idMat_rows (k + 1)) i j hi
        (by rw [idMat_len (k + 1)]; exact hj),
      idMat_row (k + 1) j hj, idMat_row (k + 1) i hi,
      elim.getAt_idRow (k + 1) j i hi, elim.getAt_idRow (k + 1) i j hj]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (fun he => hij he.symm)]

/-- The identity is the product's right unit, the left unit's
corollary through the transpose reversal. -/
theorem matMul_idR {k : Nat} (n : Nat) (X : Mat) (hX : rowsLen n X)
    (hXl : X.length = k) (hn : 0 < n) (hk : 0 < k) :
    matOneValue (matMul X (idMat n)) X := by
  have hXt : (transposeM X).length = n :=
    length_transposeM X hX (by rw [hXl]; exact hk)
  have hMw : rowsLen n (matMul X (idMat n)) := by
    refine rowsLen_cast ?_ (rowsLen_matMul X (idMat n))
    rw [transposeM_idMat n, idMat_len n]
  have hMl : (matMul X (idMat n)).length = k :=
    (length_matMul X (idMat n)).trans hXl
  have h1 : matOneValue (transposeM (matMul X (idMat n)))
      (transposeM X) := by
    refine matOne_trans
      (transposeM_matMul (r := k) (n := n) (k := n) X (idMat n)
        hX (idMat_rows n) hXl (idMat_len n) hk hn) ?_
    rw [transposeM_idMat n]
    exact idMat_matMul (k := k) n (transposeM X)
      (rowsLen_cast hXl (rowsLen_transposeM X)) hXt hn
  refine matOne_trans
    (matOne_symm (idMat_matMul (k := n) k (matMul X (idMat n))
      hMw hMl hk)) ?_
  refine matOne_trans
    (matMul_congrR_of (idMat k) (matMul X (idMat n)) X h1) ?_
  exact idMat_matMul (k := n) k X hX hXl hk

/-- Two powers join at the counts' sum. -/
theorem matPow_add (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) : ∀ a b : Nat,
    matOneValue (matMul (matPow M n a) (matPow M n b))
      (matPow M n (a + b))
  | 0, b => by
    rw [Nat.zero_add b]
    exact idMat_matMul n (matPow M n b) (rowsLen_matPow M n hMl b)
      (length_matPow M n hMl b) hn
  | a + 1, b => by
    rw [Nat.add_right_comm a 1 b]
    show matOneValue
      (matMul (matMul M (matPow M n a)) (matPow M n b))
      (matMul M (matPow M n (a + b)))
    refine matOne_trans
      (matMul_assoc M (matPow M n a) (matPow M n b) hMr
        (rowsLen_matPow M n hMl a) (rowsLen_matPow M n hMl b)
        (length_matPow M n hMl a) (length_matPow M n hMl b) hn hn) ?_
    have hml : (matMul (matPow M n a) (matPow M n b)).length = n := by
      rw [length_matMul (matPow M n a) (matPow M n b),
        length_matPow M n hMl a]
    exact matMul_congrR (n := n) (k := n) M
      (matMul (matPow M n a) (matPow M n b)) (matPow M n (a + b))
      (rowsLen_matMul_of (matPow M n a) (matPow M n b)
         (fun _ => (by rw [length_matPow M n hMl b]; exact hn))
         (rowsLen_matPow M n hMl b))
      (rowsLen_matPow M n hMl (a + b)) hml
      (length_matPow M n hMl (a + b)) hn
      (matPow_add n M hMl hMr hn a b)

/-- The power grows at the right factor as well, the counts' sum
at one. -/
theorem matPow_succR (n : Nat) (M : Mat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hn : 0 < n) (m : Nat) :
    matOneValue (matMul (matPow M n m) M) (matPow M n (m + 1)) :=
  matOne_trans
    (matMul_congrR (n := n) (k := n) (matPow M n m) M (matPow M n 1)
      hMr (rowsLen_matPow M n hMl 1) hMl (length_matPow M n hMl 1)
      hn (matOne_symm (matMul_idR n M hMr hMl hn hn)))
    (matPow_add n M hMl hMr hn m 1)

/-- The witness against the fixed read: at the orthogonality
`Tᵀ T = 1` a `T`-fixed matrix is fixed by the witness too
(`lem:fiberdec`'s `Tᵀ X = X`). -/
theorem fixed_transpose (n : Nat) (M X : Mat) (hM : rowsLen n M)
    (hMl : M.length = n) (hn : 0 < n)
    (hXr : rowsLen n X) (hXl : X.length = n)
    (horth : matOneValue (matMul (transposeM M) M) (inertia.idMat n))
    (h : matOneValue (matMul M X) X) :
    matOneValue (matMul (transposeM M) X) X := by
  have hMt : rowsLen n (transposeM M) :=
    rowsLen_cast hMl (rowsLen_transposeM M)
  have hMtl : (transposeM M).length = n := transposeLen M hM hMl
  have hXt : (transposeM X).length = n :=
    length_transposeM X hXr (by rw [hXl]; exact hn)
  refine matOne_trans
    (matMul_congrR (n := n) (k := n) (transposeM M) X (matMul M X)
      hXr (rowsLen_cast hXt (rowsLen_matMul M X)) hXl
      ((length_matMul M X).trans hMl) hn (matOne_symm h)) ?_
  refine matOne_trans
    (matOne_symm (matMul_assoc (n := n) (k := n) (s := n)
      (transposeM M) M X hMt hM hXr hMl hXl hn hn)) ?_
  exact matOne_trans (elim.matMul_congrL _ _ X horth)
    (inertia.idMat_matMul n X hXr hXl hn)

/-- An occupied block list's width sits above the seed. -/
private theorem widthOf_pos (b : SBlock) (bs : List SBlock) (k : Nat) :
    0 < widthOf (b :: bs) k := by
  show 0 < widthOf bs (k + b.order)
  rw [widthOf_shift bs k b.order]
  refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_left b.order (widthOf bs k))
  cases b with
  | one _ => exact Nat.succ_pos 0
  | two _ _ _ => exact Nat.succ_pos 1

/-- Two weightings compose on a row. -/
private theorem vecScaleB_scaleB (a b : BPair) : ∀ r : List BPair,
    poly.oneValue (r.map (fun x => (a * x).norm)
        |>.map (fun x => (b * x).norm))
      (r.map (fun x => ((b * a) * x).norm))
  | [] => trivial
  | x :: r =>
    ⟨BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl b) (BPair.norm_oneValue _))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_assoc b a x).symm)
          (BPair.oneValue_symm (BPair.norm_oneValue _)))),
     vecScaleB_scaleB a b r⟩

/-- A split of the vacant order reads the vacant count: its block
list is the unit family at the width tie. -/
theorem revAt_zero (sp : Split 0) : revAt sp = 0 := by
  have hw : widthOf sp.blocks sp.kern = 0 := Nat.eq_of_beq_eq_true sp.width
  show sp.blocks.foldl (fun m b => m + b.rev) 0 = 0
  cases hb : sp.blocks with
  | nil => rfl
  | cons b bs =>
    rw [hb] at hw
    exact absurd (widthOf_pos b bs sp.kern) (by rw [hw]; exact Nat.lt_irrefl 0)

/-- Two weightings compose to the product's. -/
theorem scaleB_scaleB (a b : BPair) : ∀ M : Mat,
    matOneValue (matScaleB a (matScaleB b M)) (matScaleB (a * b) M)
  | [] => trivial
  | r :: t =>
    ⟨vecScaleB_scaleB b a r, scaleB_scaleB a b t⟩

/-- A split transports across the one-value read at a square
datum: every conjunct of the read is a read of the datum's value. -/
theorem splitRead_congr {n : Nat} (S S' : Mat) (hS' : sqAt S' n)
    (h : matOneValue S S') (sp : Split n) (hs : splitRead S sp) :
    splitRead S' sp := by
  obtain ⟨hsq, hcl, hcong, hns⟩ := hs
  refine ⟨hS', hcl, ?_, hns⟩
  have hSr : rowsLen n S := rowsLen_of_sqAt hsq
  have hS'r : rowsLen n S' := rowsLen_of_sqAt hS'
  have hTl : sp.T.val.length = n := sqAt_len sp.T.shape
  have hTr : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
  have hTt : (transposeM sp.T.val).length = n := transposeLen _ hTr hTl
  have hinner : matOneValue (matMul S sp.T.val) (matMul S' sp.T.val) :=
    matMul_congrL S S' sp.T.val h
  have hrows : rowsLen n (matMul S sp.T.val) :=
    rowsLen_cast hTt (rowsLen_matMul S sp.T.val)
  have hrows' : rowsLen n (matMul S' sp.T.val) :=
    rowsLen_cast hTt (rowsLen_matMul S' sp.T.val)
  have hlen : (matMul S sp.T.val).length = (matMul S' sp.T.val).length := by
    rw [length_matMul, length_matMul]
    exact matOne_length h
  exact matOne_trans
    (matMul_congrR_of (transposeM sp.T.val) _ _
      (transposeM_congrM n _ _ hrows' hrows hlen.symm (matOne_symm hinner)))
    hcong

/-- The congruence invariance (`lem:inertia`'s consequences): at a
congruence with a two-sided witness, `T W ~ c I ~ W T` at `c` off
equal members, the image reads the datum's own reversal count — the
compression comparison each way, the witness's round trip the
datum at the square's positive rescaling. -/
theorem rev_congr {n : Nat} (S T W : Mat) (c : BPair)
    (hc : ¬ c.oneValue BPair.unit)
    (hS : sqAt S n) (hT : sqAt T n) (hW : sqAt W n)
    (hTW : matOneValue (matMul T W) (matScaleB c (idMat n)))
    (hWT : matOneValue (matMul W T) (matScaleB c (idMat n)))
    (sp : Split n) (h : splitRead S sp)
    (spc : Split n) (hc' : splitRead (matMul (transposeM T) (matMul S T)) spc) :
    revAt spc = revAt sp := by
  have hTl : T.length = n := sqAt_len hT
  have hTr : rowsLen n T := rowsLen_of_sqAt hT
  have hWl : W.length = n := sqAt_len hW
  have hWr : rowsLen n W := rowsLen_of_sqAt hW
  have hSl : S.length = n := sqAt_len hS
  have hSr : rowsLen n S := rowsLen_of_sqAt hS
  have hle1 : revAt spc ≤ revAt sp :=
    rev_compress S T hS hTl hTr spc hc' sp h
  refine Nat.le_antisymm hle1 ?_
  cases n with
  | zero =>
    rw [revAt_zero spc, revAt_zero sp]
    exact Nat.le_refl 0
  | succ n0 =>
    have hn : 0 < n0 + 1 := Nat.succ_pos n0
    have hTt : (transposeM T).length = n0 + 1 := transposeLen T hTr hTl
    have hWt : (transposeM W).length = n0 + 1 := transposeLen W hWr hWl
    have hTtr : rowsLen (n0 + 1) (transposeM T) :=
      rowsLen_cast hTl (rowsLen_transposeM T)
    have hWtr : rowsLen (n0 + 1) (transposeM W) :=
      rowsLen_cast hWl (rowsLen_transposeM W)
    have hidl : (idMat (n0 + 1)).length = n0 + 1 := idMat_len (n0 + 1)
    have hidr : rowsLen (n0 + 1) (idMat (n0 + 1)) := idMat_rows (n0 + 1)
    have hcIl : (matScaleB c (idMat (n0 + 1))).length = n0 + 1 :=
      (length_scaleB _ _).trans hidl
    have hcIr : rowsLen (n0 + 1) (matScaleB c (idMat (n0 + 1))) :=
      rowsLen_scaleB c _ _ hidr
    -- the product's shapes
    have hSTl : (matMul S T).length = n0 + 1 := (length_matMul S T).trans hSl
    have hSTr : rowsLen (n0 + 1) (matMul S T) :=
      rowsLen_cast hTt (rowsLen_matMul S T)
    have hTWl : (matMul T W).length = n0 + 1 := (length_matMul T W).trans hTl
    have hTWr : rowsLen (n0 + 1) (matMul T W) :=
      rowsLen_cast hWt (rowsLen_matMul T W)
    have hTSl : (matMul (transposeM T) S).length = n0 + 1 :=
      (length_matMul _ S).trans hTt
    have hTSr : rowsLen (n0 + 1) (matMul (transposeM T) S) :=
      rowsLen_cast (transposeLen S hSr hSl) (rowsLen_matMul _ S)
    have hS'l : (matMul (transposeM T) (matMul S T)).length = n0 + 1 :=
      (length_matMul _ _).trans hTt
    have hS'r : rowsLen (n0 + 1) (matMul (transposeM T) (matMul S T)) :=
      rowsLen_cast (transposeLen _ hSTr hSTl) (rowsLen_matMul _ _)
    -- step A: (Tᵀ (S T)) W ~ Tᵀ (S (T W)) ~ Tᵀ (c S)
    have hA1 : matOneValue (matMul (matMul (transposeM T) (matMul S T)) W)
        (matMul (transposeM T) (matMul (matMul S T) W)) :=
      matMul_assoc (transposeM T) (matMul S T) W hTtr hSTr hWr hSTl hWl hn hn
    have hA2 : matOneValue (matMul (matMul S T) W) (matMul S (matMul T W)) :=
      matMul_assoc S T W hSr hTr hWr hTl hWl hn hn
    have hA3 : matOneValue (matMul S (matMul T W)) (matMul S (matScaleB c (idMat (n0 + 1)))) :=
      matMul_congrR S _ _ hTWr hcIr hTWl hcIl hn hTW
    have hA4 : matOneValue (matMul S (matScaleB c (idMat (n0 + 1))))
        (matScaleB c (matMul S (idMat (n0 + 1)))) :=
      matMul_scaleR c (n0 + 1) S (idMat (n0 + 1)) hidr
    have hA5 : matOneValue (matScaleB c (matMul S (idMat (n0 + 1)))) (matScaleB c S) :=
      matOne_scaleB c (matMul_idR (n0 + 1) S hSr hSl hn hn)
    have hA : matOneValue (matMul (matMul (transposeM T) (matMul S T)) W)
        (matMul (transposeM T) (matScaleB c S)) :=
      matOne_trans hA1 (matMul_congrR (transposeM T) _ _
        (rowsLen_cast hWt (rowsLen_matMul _ W))
        (rowsLen_scaleB c _ _ hSr)
        ((length_matMul _ W).trans hSTl)
        ((length_scaleB _ _).trans hSl) hn
        (matOne_trans hA2 (matOne_trans hA3 (matOne_trans hA4 hA5))))
    have hB : matOneValue (matMul (transposeM T) (matScaleB c S))
        (matScaleB c (matMul (transposeM T) S)) :=
      matMul_scaleR c (n0 + 1) (transposeM T) S hSr
    -- step C: Wᵀ (c (Tᵀ S)) ~ c ((Wᵀ Tᵀ) S) ~ c ((T W)ᵀ S) ~ c ((c I) S) ~ c (c S)
    have hC1 : matOneValue (matMul (transposeM W) (matScaleB c (matMul (transposeM T) S)))
        (matScaleB c (matMul (transposeM W) (matMul (transposeM T) S))) :=
      matMul_scaleR c (n0 + 1) (transposeM W) _ hTSr
    have hC2 : matOneValue (matMul (matMul (transposeM W) (transposeM T)) S)
        (matMul (transposeM W) (matMul (transposeM T) S)) :=
      matMul_assoc (transposeM W) (transposeM T) S hWtr hTtr hSr hTt hSl hn hn
    have hC3 : matOneValue (transposeM (matMul T W))
        (matMul (transposeM W) (transposeM T)) :=
      transposeM_matMul T W hTr hWr hTl hWl hn hn
    have hC4 : matOneValue (transposeM (matMul T W))
        (transposeM (matScaleB c (idMat (n0 + 1)))) :=
      transposeM_congrM (n0 + 1) _ _ hTWr hcIr (hTWl.trans hcIl.symm) hTW
    have hC5 : matOneValue (transposeM (matScaleB c (idMat (n0 + 1))))
        (matScaleB c (idMat (n0 + 1))) := by
      refine matOne_trans (transposeM_scaleB c (n0 + 1) (idMat (n0 + 1)) hidr) ?_
      rw [transposeM_idMat (n0 + 1)]
      exact matOne_refl _
    have hC6 : matOneValue (matMul (matScaleB c (idMat (n0 + 1))) S)
        (matScaleB c S) :=
      matOne_trans (matMul_scaleL c (idMat (n0 + 1)) S)
        (matOne_scaleB c (idMat_matMul (n0 + 1) S hSr hSl hn))
    have hWTt : (matMul (transposeM W) (transposeM T)).length = n0 + 1 :=
      (length_matMul _ _).trans hWt
    have hWTtr : rowsLen (n0 + 1) (matMul (transposeM W) (transposeM T)) :=
      rowsLen_cast (transposeLen _ hTtr hTt) (rowsLen_matMul _ _)
    have hTWtl : (transposeM (matMul T W)).length = n0 + 1 := transposeLen _ hTWr hTWl
    have hTWtr : rowsLen (n0 + 1) (transposeM (matMul T W)) :=
      rowsLen_cast hTWl (rowsLen_transposeM _)
    have hC : matOneValue (matMul (transposeM W) (matMul (transposeM T) S))
        (matScaleB c S) :=
      matOne_trans (matOne_symm hC2)
        (matOne_trans (matMul_congrL _ _ S (matOne_symm hC3))
          (matOne_trans (matMul_congrL _ _ S hC4)
            (matOne_trans (matMul_congrL _ _ S hC5) hC6)))
    -- the round trip whole
    have hround : matOneValue
        (matMul (transposeM W) (matMul (matMul (transposeM T) (matMul S T)) W))
        (matScaleB (c * c) S) := by
      refine matOne_trans (matMul_congrR (transposeM W) _ _
        (rowsLen_cast hWt (rowsLen_matMul _ W))
        (rowsLen_scaleB c _ _ hTSr)
        ((length_matMul _ W).trans hS'l)
        ((length_scaleB _ _).trans hTSl) hn (matOne_trans hA hB)) ?_
      refine matOne_trans hC1 ?_
      refine matOne_trans (matOne_scaleB c hC) ?_
      exact scaleB_scaleB c c S
    have hcc : BPair.unit < c * c := ground.sq_pos hc
    have hsq' : sqAt (matMul (transposeM W)
        (matMul (matMul (transposeM T) (matMul S T)) W)) (n0 + 1) := by
      refine sqAt_of ((length_matMul _ _).trans hWt) ?_
      have hXr : rowsLen (n0 + 1) (matMul (matMul (transposeM T) (matMul S T)) W) :=
        rowsLen_cast hWt (rowsLen_matMul _ W)
      have hXl : (matMul (matMul (transposeM T) (matMul S T)) W).length = n0 + 1 :=
        (length_matMul _ W).trans hS'l
      exact rowsLen_cast (transposeLen _ hXr hXl) (rowsLen_matMul (transposeM W) _)
    have hsp2 : splitRead (matMul (transposeM W)
        (matMul (matMul (transposeM T) (matMul S T)) W)) (scaleSplit (c * c) sp) :=
      splitRead_congr _ _ hsq' (matOne_symm hround) _
        (scaleSplit_read (c * c) (ground.offOfUnitLt hcc) S sp h)
    have hle2 := rev_compress (matMul (transposeM T) (matMul S T)) W
      (sqAt_of hS'l hS'r) hWl hWr _ hsp2 spc hc'
    rw [scaleSplit_rev (c * c) hcc sp] at hle2
    exact hle2

/-- The ground weight against the balance weight on one row: the
sited factor's product is the memberwise rescaling, entry by
entry. -/
private theorem scaleRow_ofPos (w : Pos) : ∀ r : List BPair,
    poly.oneValue (r.map (fun z => z.scale w))
      (r.map (fun z => (BPair.ofPos w * z).norm))
  | [] => trivial
  | z :: r =>
    ⟨BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.ofPos_scale w z)),
     scaleRow_ofPos w r⟩

/-- The ground rescaling is the balance weighting at the sited
member, the two spellings one value entry by entry. -/
theorem matScale_scaleB (w : Pos) : ∀ M : Mat,
    matOneValue (matScale w M) (matScaleB (BPair.ofPos w) M)
  | [] => trivial
  | r :: M => ⟨scaleRow_ofPos w r, matScale_scaleB w M⟩

/-- The positive rescaling keeps the one-value read, the
balance-weight congruence at the clearing's own pair. -/
theorem matScale_matOne (c : Pos) {A B : Mat}
    (h : matOneValue A B) :
    matOneValue (matScale c A) (matScale c B) :=
  elim.matOne_trans (matScale_scaleB c A)
    (elim.matOne_trans (matOne_scaleB (BPair.ofPos c) h)
      (elim.matOne_symm (matScale_scaleB c B)))

/-- The key-list exchange passes the positive rescaling: the rescaled
matrix's transpose reads the transpose's rescaling, the balance-pair
weighting's read at the clearing's own pair. -/
theorem transposeM_matScale (w : Pos) (n : Nat) (M : Mat)
    (hM : rowsLen n M) :
    matOneValue (transposeM (matScale w M)) (matScale w (transposeM M)) :=
  matOne_trans
    (transposeM_congrM n _ _ (rowsLen_mapRows _ M n hM)
      (rowsLen_scaleB _ n M hM)
      ((length_matScale w M).trans (length_scaleB _ M).symm)
      (matScale_scaleB w M))
    (matOne_trans (transposeM_scaleB (BPair.ofPos w) n M hM)
      (matOne_symm (matScale_scaleB w (transposeM M))))

/-! The entrywise positive rescaling at the minor: a weight on
every entry factors out of the first-row fold at the order's own
power.  The column strike commutes with the weighting, so each
splitting's sub-minor collects one weight per row beneath the head
and the head entry supplies the last. -/

/-! The split's own symmetry: the block diagonal's pairing is
symmetric block by block, and the congruence carries that symmetry
back to the datum at the certificate's invertibility witness, the
determinant's square clearing entry by entry. -/

/-- The reversal count is blind to a positive ground factor: two
splits, one of a datum and one of its `c`-multiple, read one count
— `rev_scale` at the factor's own balance weighting. -/
theorem rev_scalePos {n : Nat} (c : Pos) (S : Mat) (sp sp' : Split n)
    (h : splitRead S sp) (h' : splitRead (matScale c S) sp') :
    revAt sp' = revAt sp :=
  rev_scale (BPair.ofPos c) (ground.unitLtOfPos c) S sp sp' h
    (splitRead_congr _ _ (sqAt_scaleB (BPair.ofPos c) n S h.1)
      (matScale_scaleB c S) sp' h')

/-- The positive weighting passes the action: the scaled matrix's
vector read is the read's own weighting. -/
theorem matVec_matScale (w : Pos) (M : Mat) (u : List BPair) :
    poly.oneValue (matVec (matScale w M) u)
      (elim.vecScale (BPair.ofPos w) (matVec M u)) :=
  poly.oneValue_trans (matVec_matOne _ _ u (matScale_scaleB w M))
    (matVec_scaleB _ M u)

theorem dotN_single (c d : BPair) :
    (dotN [c] [d]).oneValue (c * d) :=
  BPair.oneValue_trans (dotN_read [c] [d]) (BPair.add_unit (c * d))

private theorem dotN_cons (c d : BPair) (r u : List BPair) :
    (dotN (c :: r) (d :: u)).oneValue (c * d + dotN r u) :=
  BPair.oneValue_trans (dotN_app [c] r [d] u rfl)
    (BPair.add_congr (dotN_single c d) (BPair.oneValue_refl (dotN r u)))

private theorem matVec_consU (M : Mat) (d : BPair) (u : List BPair) :
    poly.oneValue (matVec (M.map (fun r => BPair.unit :: r)) (d :: u))
      (matVec M u) := by
  show poly.oneValue
    ((M.map (fun r => BPair.unit :: r)).map (fun r => dotN r (d :: u)))
    (M.map (fun r => dotN r u))
  rw [ground.map_map]
  refine poly.oneValue_map _ _ M ?_
  intro r _
  exact BPair.oneValue_trans (dotN_cons BPair.unit d r u)
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.unit_mul d) (BPair.oneValue_refl (dotN r u)))
      (BPair.unit_add (dotN r u)))

private theorem matVec_consU2 (M : Mat) (d e : BPair) (u : List BPair) :
    poly.oneValue
      (matVec (M.map (fun r => BPair.unit :: BPair.unit :: r)) (d :: e :: u))
      (matVec M u) := by
  show poly.oneValue
    ((M.map (fun r => BPair.unit :: BPair.unit :: r)).map
      (fun r => dotN r (d :: e :: u)))
    (M.map (fun r => dotN r u))
  rw [ground.map_map]
  refine poly.oneValue_map _ _ M ?_
  intro r _
  refine BPair.oneValue_trans (dotN_cons BPair.unit d _ (e :: u)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.unit_mul d)
      (dotN_cons BPair.unit e r u)) ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.unit_mul e) (BPair.oneValue_refl (dotN r u)))
    (BPair.unit_add (dotN r u))

private theorem add4swap (P Q R S T : BPair) :
    P + Q + (R + S + T) = P + R + (Q + S + T) := by
  rw [BPair.add_assoc R S T, BPair.add_add_comm P Q R (S + T),
    ← BPair.add_assoc Q S T]

/-- The block diagonal's pairing is symmetric: the order-1 blocks
read one product and the order-2 blocks their two crossings. -/
private theorem blockMat_pair : ∀ (bs : List SBlock) (k : Nat)
    (x y : List BPair), x.length = widthOf bs k →
    y.length = widthOf bs k →
    (dotN x (matVec (blockMat bs k) y)).oneValue
      (dotN y (matVec (blockMat bs k) x))
  | [], k, x, y, _, _ => by
    have hnull : ∀ v : List BPair,
        poly.unitTail (matVec (blockMat [] k) v) := by
      intro v
      show poly.unitTail
        (((List.range k).map (fun _ => List.replicate k BPair.unit)).map
          (fun r => dotN r v))
      rw [ground.map_map]
      exact poly.unitTail_map _ (List.range k)
        (fun _ _ => dotN_nullL _ v (poly.unitTail_replicate k))
    exact BPair.oneValue_trans (dotN_nullR x _ (hnull y))
      (BPair.oneValue_symm (dotN_nullR y _ (hnull x)))
  | .one _ :: bs, k, [], _, hx, _ =>
    Nat.noConfusion (hx.trans (widthOf_shift bs k 1))
  | .one _ :: bs, k, _ :: _, [], _, hy =>
    Nat.noConfusion (hy.trans (widthOf_shift bs k 1))
  | .one a :: bs, k, x0 :: x', y0 :: y', hx, hy => by
    have hx' : x'.length = widthOf bs k :=
      Nat.succ.inj (hx.trans (widthOf_shift bs k 1))
    have hy' : y'.length = widthOf bs k :=
      Nat.succ.inj (hy.trans (widthOf_shift bs k 1))
    have hact : ∀ (z0 : BPair) (z' : List BPair),
        poly.oneValue
          (matVec (blockMat (SBlock.one a :: bs) k) (z0 :: z'))
          (a * z0 :: matVec (blockMat bs k) z') := by
      intro z0 z'
      refine ⟨?_, matVec_consU (blockMat bs k) z0 z'⟩
      exact BPair.oneValue_trans
        (dotN_cons a z0 (List.replicate (widthOf bs k) BPair.unit) z')
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl (a * z0))
            (dotN_nullL _ z' (poly.unitTail_replicate _)))
          (BPair.add_unit (a * z0)))
    refine BPair.oneValue_trans (dotN_congrR _ _ _ (hact y0 y')) ?_
    refine BPair.oneValue_trans (dotN_cons x0 (a * y0) x' _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_of_eq (BPair.mul_rot3r x0 a y0))
        (blockMat_pair bs k x' y' hx' hy')) ?_
    exact BPair.oneValue_symm
      (BPair.oneValue_trans (dotN_congrR _ _ _ (hact x0 x'))
        (dotN_cons y0 (a * x0) y' _))
  | .two _ _ _ :: bs, k, [], _, hx, _ =>
    Nat.noConfusion (hx.trans (widthOf_shift bs k 2))
  | .two _ _ _ :: bs, k, [_], _, hx, _ =>
    Nat.noConfusion (Nat.succ.inj (hx.trans (widthOf_shift bs k 2)))
  | .two _ _ _ :: bs, k, _ :: _ :: _, [], _, hy =>
    Nat.noConfusion (hy.trans (widthOf_shift bs k 2))
  | .two _ _ _ :: bs, k, _ :: _ :: _, [_], _, hy =>
    Nat.noConfusion (Nat.succ.inj (hy.trans (widthOf_shift bs k 2)))
  | .two a b c :: bs, k, x0 :: x1 :: x', y0 :: y1 :: y', hx, hy => by
    have hx' : x'.length = widthOf bs k :=
      Nat.succ.inj (Nat.succ.inj (hx.trans (widthOf_shift bs k 2)))
    have hy' : y'.length = widthOf bs k :=
      Nat.succ.inj (Nat.succ.inj (hy.trans (widthOf_shift bs k 2)))
    have hact : ∀ (z0 z1 : BPair) (z' : List BPair),
        poly.oneValue
          (matVec (blockMat (SBlock.two a b c :: bs) k)
            (z0 :: z1 :: z'))
          ((a * z0 + b * z1) :: (b * z0 + c * z1)
            :: matVec (blockMat bs k) z') := by
      intro z0 z1 z'
      refine ⟨?_, ?_, matVec_consU2 (blockMat bs k) z0 z1 z'⟩
      · refine BPair.oneValue_trans (dotN_cons a z0 _ (z1 :: z')) ?_
        exact BPair.add_congr (BPair.oneValue_refl (a * z0))
          (BPair.oneValue_trans (dotN_cons b z1 _ z')
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.oneValue_refl (b * z1))
                (dotN_nullL _ z' (poly.unitTail_replicate _)))
              (BPair.add_unit (b * z1))))
      · refine BPair.oneValue_trans (dotN_cons b z0 _ (z1 :: z')) ?_
        exact BPair.add_congr (BPair.oneValue_refl (b * z0))
          (BPair.oneValue_trans (dotN_cons c z1 _ z')
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.oneValue_refl (c * z1))
                (dotN_nullL _ z' (poly.unitTail_replicate _)))
              (BPair.add_unit (c * z1))))
    have hL : (dotN (x0 :: x1 :: x')
        (matVec (blockMat (SBlock.two a b c :: bs) k)
          (y0 :: y1 :: y'))).oneValue
        (x0 * (a * y0) + x0 * (b * y1)
          + (x1 * (b * y0) + x1 * (c * y1)
            + dotN x' (matVec (blockMat bs k) y'))) := by
      refine BPair.oneValue_trans (dotN_congrR _ _ _ (hact y0 y1 y')) ?_
      refine BPair.oneValue_trans
        (dotN_cons x0 (a * y0 + b * y1) _ _) ?_
      refine BPair.add_congr
        (BPair.oneValue_of_eq (BPair.left_distrib x0 (a * y0) (b * y1)))
        ?_
      refine BPair.oneValue_trans
        (dotN_cons x1 (b * y0 + c * y1) _ _) ?_
      exact BPair.add_congr
        (BPair.oneValue_of_eq (BPair.left_distrib x1 (b * y0) (c * y1)))
        (BPair.oneValue_refl _)
    have hR : (dotN (y0 :: y1 :: y')
        (matVec (blockMat (SBlock.two a b c :: bs) k)
          (x0 :: x1 :: x'))).oneValue
        (y0 * (a * x0) + y0 * (b * x1)
          + (y1 * (b * x0) + y1 * (c * x1)
            + dotN y' (matVec (blockMat bs k) x'))) := by
      refine BPair.oneValue_trans (dotN_congrR _ _ _ (hact x0 x1 x')) ?_
      refine BPair.oneValue_trans
        (dotN_cons y0 (a * x0 + b * x1) _ _) ?_
      refine BPair.add_congr
        (BPair.oneValue_of_eq (BPair.left_distrib y0 (a * x0) (b * x1)))
        ?_
      refine BPair.oneValue_trans
        (dotN_cons y1 (b * x0 + c * x1) _ _) ?_
      exact BPair.add_congr
        (BPair.oneValue_of_eq (BPair.left_distrib y1 (b * x0) (c * x1)))
        (BPair.oneValue_refl _)
    refine BPair.oneValue_trans hL
      (BPair.oneValue_trans ?_ (BPair.oneValue_symm hR))
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (add4swap (x0 * (a * y0)) (x0 * (b * y1)) (x1 * (b * y0))
          (x1 * (c * y1)) (dotN x' (matVec (blockMat bs k) y')))) ?_
    refine BPair.add_congr
      (BPair.add_congr (BPair.oneValue_of_eq (BPair.mul_rot3r x0 a y0))
        (BPair.oneValue_of_eq (BPair.mul_rot3r x1 b y0))) ?_
    refine BPair.add_congr
      (BPair.add_congr (BPair.oneValue_of_eq (BPair.mul_rot3r x0 b y1))
        (BPair.oneValue_of_eq (BPair.mul_rot3r x1 c y1))) ?_
    exact blockMat_pair bs k x' y' hx' hy'

/-- The identity family's row against a vector reads the vector's
own entry at that key. -/
private theorem dotN_basis (n p : Nat) (u : List BPair) (hp : p < n)
    (hu : u.length = n) :
    (dotN (ground.getAt ([] : List BPair) (elim.idList n) p) u).oneValue
      (ground.getAt BPair.unit u p) := by
  have he : ground.getAt BPair.unit (matVec (elim.idList n) u) p
      = dotN (ground.getAt ([] : List BPair) (elim.idList n) p) u :=
    ground.getAt_map ([] : List BPair) BPair.unit
      (fun r => dotN r u) (elim.idList n) p
      (by rw [elim.length_idList]; exact hp)
  rw [← he]
  exact poly.oneValue_getAt p (elim.matVec_idList n u hu)

/-- The datum's pairing is symmetric at a split: the congruence
carries the block diagonal's own symmetry back through the
certificate's invertibility witness, the determinant's square
cancelling. -/
private theorem splitRead_pair {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) (a b : List BPair)
    (ha : a.length = n) (hb : b.length = n) :
    (dotN a (matVec S b)).oneValue (dotN b (matVec S a)) := by
  obtain ⟨hsq, hcl, hcong, -⟩ := h
  have hTl : sp.T.val.length = n := sqAt_len sp.T.shape
  have hTr : rowsLen n sp.T.val := rowsLen_of_sqAt sp.T.shape
  have hWl : sp.Tw.val.length = n := sqAt_len sp.Tw.shape
  have hWr : rowsLen n sp.Tw.val := rowsLen_of_sqAt sp.Tw.shape
  have hSl : S.length = n := sqAt_len hsq
  have hSr : rowsLen n S := rowsLen_of_sqAt hsq
  have hWid : widthOf sp.blocks sp.kern = n :=
    Nat.eq_of_beq_eq_true sp.width
  have hTt : (transposeM sp.T.val).length = n := transposeLen sp.T.val hTr hTl
  have hTtr : rowsLen n (transposeM sp.T.val) :=
    rowsLen_cast hTl (rowsLen_transposeM sp.T.val)
  have hSTr : rowsLen n (matMul S sp.T.val) :=
    rowsLen_cast hTt (rowsLen_matMul S sp.T.val)
  have hSTl : (matMul S sp.T.val).length = n :=
    (elim.length_matMul S sp.T.val).trans hSl
  have hTW : ∀ v : List BPair, v.length = n →
      poly.oneValue (matVec sp.T.val (matVec sp.Tw.val v))
        (vecScale (minor sp.T.val) v) := by
    intro v hv
    refine poly.oneValue_trans (matVec_comp sp.T.val sp.Tw.val v n hWr hv
      (rowsLen_cast hWl.symm hTr)) ?_
    exact poly.oneValue_trans (matVec_matOne _ _ v hcl.2.1)
      (scaleId_act (minor sp.T.val) n v hv)
  have hcongPair : ∀ u v : List BPair, u.length = n → v.length = n →
      (dotN (matVec sp.T.val u) (matVec S (matVec sp.T.val v))).oneValue
        (dotN u (matVec (blockMat sp.blocks sp.kern) v)) := by
    intro u v hu hv
    refine BPair.oneValue_trans (elim.dotN_comm _ _) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (adjB sp.T.val n n hTl hTr u hu
        (matVec S (matVec sp.T.val v))
        ((matVec_length _ _).trans hSl))) ?_
    refine dotN_congrR u _ _ ?_
    refine poly.oneValue_trans (matVec_congr _ _ _
      (matVec_comp S sp.T.val v n hTr hv (rowsLen_cast hTl.symm hSr))) ?_
    refine poly.oneValue_trans
      (matVec_comp (transposeM sp.T.val) (matMul S sp.T.val) v n
        hSTr hv (rowsLen_cast hSTl.symm hTtr)) ?_
    exact matVec_matOne _ _ v hcong
  have hbig : ∀ u v : List BPair, u.length = n → v.length = n →
      (minor sp.T.val * (minor sp.T.val * dotN u (matVec S v))).oneValue
        (dotN (matVec sp.Tw.val u)
          (matVec (blockMat sp.blocks sp.kern) (matVec sp.Tw.val v))) := by
    intro u v hu hv
    refine BPair.oneValue_trans ?_
      (hcongPair (matVec sp.Tw.val u) (matVec sp.Tw.val v)
        ((matVec_length _ _).trans hWl) ((matVec_length _ _).trans hWl))
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (dotN_congrL _ _ _ (hTW u hu))
          (dotN_congrR _ _ _ (matVec_congr S _ _ (hTW v hv)))))
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (BPair.oneValue_trans
        (dotN_scaleRow_free (minor sp.T.val) u (matVec S (vecScale (minor sp.T.val) v)))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (dotN_congrR u _ _ (elim.matVec_vecScale_free S _ v))
            (elim.dotN_scaleV (minor sp.T.val) u (matVec S v))))))
    exact BPair.oneValue_refl _
  refine ground.mulCancel hcl.1 (ground.mulCancel hcl.1 ?_)
  refine BPair.oneValue_trans (hbig a b ha hb) ?_
  refine BPair.oneValue_trans
    (blockMat_pair sp.blocks sp.kern _ _
      (((matVec_length _ _).trans hWl).trans hWid.symm)
      (((matVec_length _ _).trans hWl).trans hWid.symm)) ?_
  exact BPair.oneValue_symm (hbig b a hb ha)

/-- A datum carrying a split reads its own exchange: the block
diagonal's symmetry transported across the certificate. -/
theorem splitRead_symm {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp) : matOneValue S (transposeM S) := by
  have hSl : S.length = n := sqAt_len h.1
  have hSr : rowsLen n S := rowsLen_of_sqAt h.1
  have hTl : (transposeM S).length = n := transposeLen S hSr hSl
  have hTr : rowsLen n (transposeM S) :=
    rowsLen_cast hSl (rowsLen_transposeM S)
  have hSij : ∀ p q : Nat, p < n → q < n →
      (dotN (ground.getAt ([] : List BPair) (elim.idList n) p)
        (matVec S (ground.getAt [] (elim.idList n) q))).oneValue
        (ground.getAt BPair.unit (ground.getAt ([] : List BPair) S p) q) := by
    intro p q hp hq
    refine BPair.oneValue_trans
      (dotN_basis n p (matVec S _) hp ((matVec_length _ _).trans hSl)) ?_
    have hmp : ground.getAt BPair.unit
        (matVec S (ground.getAt ([] : List BPair) (elim.idList n) q)) p
        = dotN (ground.getAt ([] : List BPair) S p)
          (ground.getAt [] (elim.idList n) q) :=
      ground.getAt_map ([] : List BPair) BPair.unit
        (fun r => dotN r (ground.getAt [] (elim.idList n) q)) S p
        (by rw [hSl]; exact hp)
    rw [hmp]
    refine BPair.oneValue_trans (elim.dotN_comm _ _) ?_
    exact dotN_basis n q (ground.getAt ([] : List BPair) S p) hq
      (rowsLen_getAt S p hSr (by rw [hSl]; exact hp))
  refine elim.matOne_of_entries S (transposeM S) n hSl hSr hTl hTr ?_
  intro i j hi hj
  rw [elim.getAt_transposeM BPair.unit S hSr i j hi (by rw [hSl]; exact hj)]
  refine BPair.oneValue_trans (BPair.oneValue_symm (hSij i j hi hj)) ?_
  refine BPair.oneValue_trans (splitRead_pair S sp h _ _
    (rowsLen_getAt _ i (elim.rowsLen_idList n)
      (by rw [elim.length_idList]; exact hi))
    (rowsLen_getAt _ j (elim.rowsLen_idList n)
      (by rw [elim.length_idList]; exact hj))) ?_
  exact hSij j i hj hi

/-- The two-sided cap's symmetry read: a capped datum is symmetric,
the two certificates' block-diagonal symmetry transported across the
site datum and the sum, the cap's memberwise swap absorbing at the
sum's unit and the doubled datum reading back at the product's
injectivity. -/
theorem sym_of_capAt {n : Nat} (S C : Mat) (spU spL : Split n)
    (h : capAt S C spU spL) : matOneValue (transposeM S) S := by
  obtain ⟨hS, hC, ⟨hU, _⟩, hL, _⟩ := h
  have hSl : S.length = n := sqAt_len hS
  have hSr : rowsLen n S := rowsLen_of_sqAt hS
  have hCl : C.length = n := sqAt_len hC
  have hCr : rowsLen n C := rowsLen_of_sqAt hC
  cases n with
  | zero =>
    cases S with
    | nil => exact trivial
    | cons _ _ => exact Nat.noConfusion hSl
  | succ m =>
  have h0 : 0 < C.length := by rw [hCl]; exact Nat.succ_pos m
  have hSwl : (matSwap S).length = S.length := length_matSwap S
  have hSwr : rowsLen (m + 1) (matSwap S) := rowsLen_mapRows BPair.swap S _ hSr
  have hTl : (transposeM S).length = m + 1 := transposeLen S hSr hSl
  have hTr : rowsLen (m + 1) (transposeM S) :=
    rowsLen_cast hSl (rowsLen_transposeM S)
  have hTwr : rowsLen (m + 1) (matSwap (transposeM S)) :=
    rowsLen_mapRows BPair.swap _ _ hTr
  have hCTl : (transposeM C).length = m + 1 := transposeLen C hCr hCl
  have hCTr : rowsLen (m + 1) (transposeM C) :=
    rowsLen_cast hCl (rowsLen_transposeM C)
  have hU' : matOneValue (matAdd C (matSwap S))
      (matAdd (transposeM C) (matSwap (transposeM S))) := by
    have e := transposeM_matAdd C (matSwap S) hCr hSwr
      (hCl.trans (hSwl.trans hSl).symm) h0
    rw [transposeM_swap] at e
    rw [← e]
    exact splitRead_symm _ spU hU
  have hL' : matOneValue (matAdd C S)
      (matAdd (transposeM C) (transposeM S)) := by
    rw [← transposeM_matAdd C S hCr hSr (hCl.trans hSl.symm) h0]
    exact splitRead_symm _ spL hL
  have hZ : matOneValue
      (matAdd (matAdd C S) (matSwap (matAdd C (matSwap S))))
      (matAdd (matAdd (transposeM C) (transposeM S))
        (matSwap (matAdd (transposeM C) (matSwap (transposeM S))))) :=
    matAdd_cong2 (m + 1) _ _ _ _
      (rowsLen_matAdd _ C S hCr hSr)
      (rowsLen_mapRows BPair.swap _ _ (rowsLen_matAdd _ C (matSwap S) hCr hSwr))
      (rowsLen_matAdd _ _ _ hCTr hTr)
      (rowsLen_mapRows BPair.swap _ _ (rowsLen_matAdd _ _ _ hCTr hTwr))
      hL' (matSwap_congr hU')
  rw [matSwap_matAdd C (matSwap S), matSwap_matSwap S,
    matAdd_shuffle C S (matSwap C) S,
    matSwap_matAdd (transposeM C) (matSwap (transposeM S)),
    matSwap_matSwap (transposeM S),
    matAdd_shuffle (transposeM C) (transposeM S) (matSwap (transposeM C))
      (transposeM S)] at hZ
  have hCwr : rowsLen (m + 1) (matSwap C) := rowsLen_mapRows BPair.swap C _ hCr
  have hCTwr : rowsLen (m + 1) (matSwap (transposeM C)) :=
    rowsLen_mapRows BPair.swap _ _ hCTr
  have hN1 : matOneValue (matAdd (matAdd C (matSwap C)) (matAdd S S))
      (matAdd S S) :=
    matAdd_nullL _ _ (matNull_add_swap C)
      (by rw [length_matAdd C (matSwap C) (length_matSwap C).symm,
        length_matAdd S S rfl, hCl, hSl])
      (rowsLen_matAdd _ C (matSwap C) hCr hCwr)
      (rowsLen_matAdd _ S S hSr hSr)
  have hN2 : matOneValue
      (matAdd (matAdd (transposeM C) (matSwap (transposeM C)))
        (matAdd (transposeM S) (transposeM S)))
      (matAdd (transposeM S) (transposeM S)) :=
    matAdd_nullL _ _ (matNull_add_swap (transposeM C))
      (by rw [length_matAdd (transposeM C) (matSwap (transposeM C))
          (length_matSwap (transposeM C)).symm,
        length_matAdd (transposeM S) (transposeM S) rfl, hCTl, hTl])
      (rowsLen_matAdd _ _ _ hCTr hCTwr)
      (rowsLen_matAdd _ _ _ hTr hTr)
  have hSS : matOneValue (matAdd S S)
      (matAdd (transposeM S) (transposeM S)) :=
    matOne_trans (matOne_symm hN1) (matOne_trans hZ hN2)
  rw [matScale_two S, matScale_two (transposeM S)] at hSS
  exact matOne_symm (matOne_unscale 2 (m + 1) S (transposeM S) hSl hSr hTl hTr hSS)

/-- A capped datum is symmetric, the cap's own two certificates read
back off the rescaling. -/
theorem sym_of_capScale {n : Nat} (A : Mat) (cn cd : Pos)
    (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA') :
    matOneValue (transposeM A) A := by
  have hAl : A.length = n := (length_matScale cd A).symm.trans (sqAt_len hA.1)
  have hAr : rowsLen n A := rowsLen_of_sqAt (sqAt_matScale_reflect cd A hA.1)
  exact matOne_unscale cd n (transposeM A) A (transposeLen A hAr hAl)
    (rowsLen_cast hAl (rowsLen_transposeM A)) hAl hAr
    (matOne_trans (matOne_symm (transposeM_matScale cd n A hAr))
      (sym_of_capAt _ _ spA spA' hA))

/-! `lem:inertia`'s consequences at the two compression corners and
at the cap.  A corner's padded vector — the corner's own vector
above (or below) the unit family at the other block's order — prices
the join's quadratic form at the corner block's own form, the
coupling slab and the far block reading the unit family throughout,
so the corner split's lower list carried through the padding is a
strict family at a datum reading the join and `forcing` prices the
corner's count at or below the datum's (`rev_head_le` at the pivot
corner, `rev_tail_le` at the trailing one; a compression's counts
are at most the full form's, the blocking a one-value read the
quadratic form crosses at its argument).  A compression of a cap is
a cap (`capAt_compress` at the pivot corner, `capAt_compress_tail`
at the trailing one, `thm:truncation`'s read of the magnetic part
inside the removed block): the cap's two positive-semidefinite
reads each compressed at the corner of its own join. -/



/-- `lem:inertia`'s pivot-corner compression at a datum reading a
join: the pivot block's own count sits at or below the datum's — the
head split's lower list padded by the unit family at the trailing
order prices the datum's form at the head block's own, the family
transport at the pivot padding (a compression's counts are at most
the full form's). -/
theorem rev_head_le {k m : Nat} (S P B Q : Mat)
    (hBl : B.length = k) (hSJ : matOneValue S (blockJoin P B Q))
    (spP : Split k) (hp : splitRead P spP)
    (spS : Split (k + m)) (hS : splitRead S spS) :
    revAt spP ≤ revAt spS := by
  have hPr : rowsLen k P := rowsLen_of_sqAt hp.1
  have hPl : P.length = k := sqAt_len hp.1
  refine rev_family S P (padM k m) (padM_len k m) ?_ spP hp spS hS
  intro v hv
  exact BPair.oneValue_trans
    (quad_congr S _ _ (padM_act k m v hv))
    (BPair.oneValue_trans (quadMatOne S (blockJoin P B Q) _ hSJ)
      (quad_padJ P B Q k m hPr hPl hBl v hv))

/-- `lem:inertia`'s trailing-corner compression at a datum reading
a join: the trailing block's own count sits at or below the datum's
— the trailing lower list padded by the unit family at the pivot's
order is the datum's strict family through the family transport, the
coupling's exchange meeting that family at the sum's unit. -/
theorem rev_tail_le {k m : Nat} (S P B Q : Mat)
    (hB : B.length = k) (hBr : rowsLen m B)
    (hSJ : matOneValue S (blockJoin P B Q))
    (spQ : Split m) (hq : splitRead Q spQ)
    (spS : Split (k + m)) (hS : splitRead S spS) :
    revAt spQ ≤ revAt spS := by
  have hJlen : (blockJoin P B Q).length = k + m :=
    (matOne_length hSJ).symm.trans (sqAt_len hS.1)
  cases Nat.eq_zero_or_pos k with
  | inl hk =>
    subst hk
    have h0 : (blockJoin P B Q).length = 0 := blockJoin_nil P B Q hB
    have hm : m = 0 := by
      have h1 : (0 : Nat) = 0 + m := h0.symm.trans hJlen
      rw [Nat.zero_add] at h1
      exact h1.symm
    subst hm
    rw [revAt_zero spQ]
    exact Nat.zero_le _
  | inr hk =>
    have hBt : (transposeM B).length = m :=
      length_transposeM B hBr (by rw [hB]; exact hk)
    have hBtr : rowsLen k (transposeM B) :=
      rowsLen_cast hB (rowsLen_transposeM B)
    have hQl : Q.length = m := sqAt_len hq.1
    have hL2 : (List.zipWith (· ++ ·) (transposeM B) Q).length = m :=
      ground.length_zipWith (· ++ ·) (transposeM B) Q m hBt hQl
    have hJl : (List.zipWith (· ++ ·) P B).length = k := by
      have h1 : (List.zipWith (· ++ ·) P B).length
          + (List.zipWith (· ++ ·) (transposeM B) Q).length = k + m := by
        rw [← ground.length_append]
        exact hJlen
      rw [hL2] at h1
      exact ground.addCancelR m h1
    refine rev_family S Q (padR k m) (padR_len k m) ?_ spQ hq spS hS
    intro v hv
    exact BPair.oneValue_trans
      (quad_congr S _ _ (padR_act k m v hv))
      (BPair.oneValue_trans (quadMatOne S (blockJoin P B Q) _ hSJ)
        (quad_padJR P B Q k m hJl hBt hBtr hQl v hv))

/-- `lem:inertia`'s compression at the cap (`lem:dualtrunc`'s
citation): a compression of a cap is a cap, at the pivot corner.
The cap is two positive-semidefinite reads, and at the pivot corner
of each read's own join the corner block's count sits at or below
the read's vacant count, so both corner reads are vacant in turn. -/
theorem capAt_compress {k m : Nat} (S C S1 C1 BS BC S2 C2 : Mat)
    (spU spL : Split (k + m)) (spU' spL' : Split k)
    (hcap : capAt S C spU spL)
    (hBl : BS.length = k) (hCl : BC.length = k)
    (htU : matOneValue (siteDatum C S)
      (blockJoin (siteDatum C1 S1) BC (siteDatum C2 S2)))
    (htL : matOneValue (matAdd C S)
      (blockJoin (matAdd C1 S1) BS (matAdd C2 S2)))
    (hU' : splitRead (siteDatum C1 S1) spU')
    (hL' : splitRead (matAdd C1 S1) spL')
    (hs1 : sqAt S1 k) (hc1 : sqAt C1 k) :
    capAt S1 C1 spU' spL' := by
  refine ⟨hs1, hc1, ⟨hU', ?_⟩, hL', ?_⟩
  · have hle := rev_head_le (siteDatum C S) (siteDatum C1 S1) BC
      (siteDatum C2 S2) hCl htU spU' hU' spU hcap.2.2.1.1
    have hz : revAt spU = 0 := hcap.2.2.1.2
    rw [hz] at hle
    exact Nat.le_antisymm hle (Nat.zero_le _)
  · have hle := rev_head_le (matAdd C S) (matAdd C1 S1) BS
      (matAdd C2 S2) hBl htL spL' hL' spL hcap.2.2.2.1
    have hz : revAt spL = 0 := hcap.2.2.2.2
    rw [hz] at hle
    exact Nat.le_antisymm hle (Nat.zero_le _)

/-- `lem:inertia`'s compression at the cap, the trailing corner:
the removed block's cap from the assembled one — the trailing
block's count sits at or below each read's vacant count through the
coupling's exchange, so the trailing corner's two reads are vacant
in turn (`thm:truncation`'s compression of the magnetic part inside
the removed block). -/
theorem capAt_compress_tail {k m : Nat} (S C S1 C1 BS BC S2 C2 : Mat)
    (spU spL : Split (k + m)) (spU' spL' : Split m)
    (hcap : capAt S C spU spL)
    (hBl : BS.length = k) (hBr : rowsLen m BS)
    (hCl : BC.length = k) (hCr : rowsLen m BC)
    (htU : matOneValue (siteDatum C S)
      (blockJoin (siteDatum C1 S1) BC (siteDatum C2 S2)))
    (htL : matOneValue (matAdd C S)
      (blockJoin (matAdd C1 S1) BS (matAdd C2 S2)))
    (hU' : splitRead (siteDatum C2 S2) spU')
    (hL' : splitRead (matAdd C2 S2) spL')
    (hs2 : sqAt S2 m) (hc2 : sqAt C2 m) :
    capAt S2 C2 spU' spL' := by
  refine ⟨hs2, hc2, ⟨hU', ?_⟩, hL', ?_⟩
  · have hle := rev_tail_le (siteDatum C S) (siteDatum C1 S1) BC
      (siteDatum C2 S2) hCl hCr htU spU' hU' spU hcap.2.2.1.1
    have hz : revAt spU = 0 := hcap.2.2.1.2
    rw [hz] at hle
    exact Nat.le_antisymm hle (Nat.zero_le _)
  · have hle := rev_tail_le (matAdd C S) (matAdd C1 S1) BS
      (matAdd C2 S2) hBl hBr htL spL' hL' spL hcap.2.2.2.1
    have hz : revAt spL = 0 := hcap.2.2.2.2
    rw [hz] at hle
    exact Nat.le_antisymm hle (Nat.zero_le _)



/-! `lem:inertia`'s existence clause: every symmetric square datum
carries a split, closed by the leftmost admissible pivot's descent
— one pivot block of order at most two per step with the deflation
beneath it, the datum's vacant remainder the kernel block.  The
descent's two devices are the adjacent exchange, which moves a
pivot's places into the leading positions (the congruence's columns
exchanged with them, the determinant's members with the exchange),
and the cleared clearing at the pivot, whose congruence is block
triangular so its determinant is the diagonal blocks' product
outright.  The certificate is carried by the congruence's column
list `V` — the rows of `V` the congruence's columns — so the split
read is the pairing table `dotN Vᵢ (S Vⱼ)` against the block
diagonal, and the congruence is that list's own key exchange. -/

/-- The exchange commutes with a rowwise map. -/
private theorem map_adjSwap {α β : Type} (f : α → β) :
    ∀ (t : Nat) (l : List α),
      (ground.adjSwap t l).map f = ground.adjSwap t (l.map f)
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | t + 1, a :: l => congrArg (fun z => f a :: z) (map_adjSwap f t l)

/-- The rowwise exchange keeps the row widths. -/
private theorem rowsLen_mapAdj {γ : Type} {n : Nat} (t : Nat) :
    ∀ l : List (List γ), rowsLen n l →
      rowsLen n (l.map (ground.adjSwap t))
  | [], _ => trivial
  | r :: l, h =>
    ⟨(ground.length_adjSwap t r).trans h.1, rowsLen_mapAdj t l h.2⟩

/-- A listed row of a stated-width family reads that width. -/
private theorem rowsLen_memLen {γ : Type} {n : Nat} :
    ∀ (l : List (List γ)), rowsLen n l → ∀ r : List γ, r ∈ l →
      r.length = n
  | [], _, _, hm => by cases hm
  | s :: l, h, r, hm => by
    cases hm with
    | head => exact h.1
    | tail _ ht => exact rowsLen_memLen l h.2 r ht

/-- The plain fold moves the exchange across its two arguments. -/
private theorem dotP_adjSwap : ∀ (t : Nat) (u v : List BPair),
    u.length = v.length →
    dotP (ground.adjSwap t u) v = dotP u (ground.adjSwap t v)
  | 0, [], _, _ => rfl
  | _ + 1, [], _, _ => rfl
  | 0, [_], [], h => Nat.noConfusion h
  | 0, [_], [_], _ => rfl
  | 0, [_], _ :: _ :: _, h => Nat.noConfusion (Nat.succ.inj h)
  | 0, _ :: _ :: _, [], h => Nat.noConfusion h
  | 0, _ :: _ :: _, [_], h => Nat.noConfusion (Nat.succ.inj h)
  | 0, a :: b :: u, c :: d :: v, _ => by
    show b * c + (a * d + dotP u v) = a * d + (b * c + dotP u v)
    exact BPair.add_left_comm _ _ _
  | _ + 1, _ :: _, [], h => Nat.noConfusion h
  | t + 1, a :: u, c :: v, h => by
    show a * c + dotP (ground.adjSwap t u) v
      = a * c + dotP u (ground.adjSwap t v)
    rw [dotP_adjSwap t u v (Nat.succ.inj h)]

/-- The skipping fold moves the exchange across its two
arguments. -/
private theorem dotN_adjSwap (t : Nat) (u v : List BPair)
    (h : u.length = v.length) :
    (dotN (ground.adjSwap t u) v).oneValue
      (dotN u (ground.adjSwap t v)) := by
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_adjSwap t u v h]
  exact BPair.oneValue_symm (dotN_read _ _)

/-- The exchanged datum: the rows and the columns exchanged at one
key, the conjugation at the places' adjacent exchange. -/
private def swapRC (t : Nat) (S : Mat) : Mat :=
  (ground.adjSwap t S).map (ground.adjSwap t)

/-- The exchanged datum keeps the order. -/
private theorem sqAt_swapRC (t : Nat) (S : Mat) (n : Nat) (h : sqAt S n) :
    sqAt (swapRC t S) n := by
  refine sqAt_of ?_ (rowsLen_mapAdj t (ground.adjSwap t S)
    (elim.rowsLen_adjSwap t S (rowsLen_of_sqAt h)))
  show ((ground.adjSwap t S).map (ground.adjSwap t)).length = n
  rw [ground.length_map, ground.length_adjSwap]
  exact sqAt_len h

/-- The datum's action at an exchanged vector reads the rowwise
exchanged datum's action. -/
private theorem matVec_adjSwap (t : Nat) (S : Mat) (n : Nat)
    (hS : rowsLen n S) (w : List BPair) (hw : w.length = n) :
    poly.oneValue (matVec S (ground.adjSwap t w))
      (matVec (S.map (ground.adjSwap t)) w) := by
  show poly.oneValue (S.map (fun r => dotN r (ground.adjSwap t w)))
    ((S.map (ground.adjSwap t)).map (fun r => dotN r w))
  rw [ground.map_map]
  refine poly.oneValue_map (fun r => dotN r (ground.adjSwap t w))
    (fun r => dotN (ground.adjSwap t r) w) S ?_
  intro r hr
  exact BPair.oneValue_symm
    (dotN_adjSwap t r w ((rowsLen_memLen S hS r hr).trans hw.symm))

/-- The pairing table moves across the adjacent exchange: the two
exchanged vectors pair at the exchanged datum. -/
private theorem gram_adjSwap (t : Nat) (S : Mat) (n : Nat)
    (hSr : rowsLen n S) (hSl : S.length = n)
    (u w : List BPair) (hu : u.length = n) (hw : w.length = n) :
    (dotN (ground.adjSwap t u) (matVec S (ground.adjSwap t w))).oneValue
      (dotN u (matVec (swapRC t S) w)) := by
  refine BPair.oneValue_trans
    (dotN_adjSwap t u (matVec S (ground.adjSwap t w))
      (by rw [hu, matVec_length, hSl])) ?_
  rw [show ground.adjSwap t (matVec S (ground.adjSwap t w))
      = matVec (ground.adjSwap t S) (ground.adjSwap t w) from
    (map_adjSwap (fun r => dotN r (ground.adjSwap t w)) t S).symm]
  exact dotN_congrR u _ _
    (matVec_adjSwap t (ground.adjSwap t S) n
      (elim.rowsLen_adjSwap t S hSr) w hw)


/-- The key exchange of a rowwise exchange is the row exchange of
the key exchange, entry by entry. -/
private theorem entry_transposeM_mapAdj (M : Mat) (n t : Nat)
    (hMl : M.length = n) (hMr : rowsLen n M) (ht : t + 1 < n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    ground.getAt BPair.unit
        (ground.getAt [] (transposeM (M.map (ground.adjSwap t))) i) j
      = ground.getAt BPair.unit
        (ground.getAt [] (ground.adjSwap t (transposeM M)) i) j := by
  have hXr : rowsLen n (M.map (ground.adjSwap t)) := rowsLen_mapAdj t M hMr
  have hXl : (M.map (ground.adjSwap t)).length = n :=
    (ground.length_map _ M).trans hMl
  have hTl : (transposeM M).length = n :=
    transposeLen M hMr hMl
  have hrowj : (ground.getAt ([] : List BPair) M j).length = n :=
    rowsLen_getAt M j hMr (by rw [hMl]; exact hj)
  rw [getAt_transposeM BPair.unit (M.map (ground.adjSwap t)) hXr i j hi
      (by rw [hXl]; exact hj),
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (ground.adjSwap t) M j (by rw [hMl]; exact hj),
    ground.getAt_adjSwap BPair.unit t (ground.getAt [] M j)
      (by rw [hrowj]; exact ht) i,
    ground.getAt_adjSwap ([] : List BPair) t (transposeM M)
      (by rw [hTl]; exact ht) i,
    getAt_transposeM BPair.unit M hMr (ground.swapIx t (t + 1) i) j
      (ground.swapIx_lt (Nat.lt_of_succ_lt ht) ht i hi)
      (by rw [hMl]; exact hj)]

/-- The rowwise exchange swaps the determinant's members: the key
exchange carries it to the row exchange, `elim.detL_swapAdj`'s
read. -/
private theorem detL_mapAdj (M : Mat) (n t : Nat)
    (hMl : M.length = n) (hMr : rowsLen n M) (ht : t + 1 < n) :
    (detL (M.map (ground.adjSwap t))).oneValue (detL M).swap := by
  have hXr : rowsLen n (M.map (ground.adjSwap t)) := rowsLen_mapAdj t M hMr
  have hXl : (M.map (ground.adjSwap t)).length = n :=
    (ground.length_map _ M).trans hMl
  have hTl : (transposeM M).length = n := transposeLen M hMr hMl
  have hTXl : (transposeM (M.map (ground.adjSwap t))).length = n :=
    transposeLen _ hXr hXl
  have hAl : (ground.adjSwap t (transposeM M)).length = n :=
    (ground.length_adjSwap t (transposeM M)).trans hTl
  have hstep : (detL (transposeM (M.map (ground.adjSwap t)))).oneValue
      (detL (ground.adjSwap t (transposeM M))) := by
    refine detL_congr_letters _ _ (by rw [hTXl, hAl]) ?_
    intro a ha b hb
    rw [hTXl] at ha hb
    exact BPair.oneValue_of_eq
      (entry_transposeM_mapAdj M n t hMl hMr ht a b ha hb)
  rw [← detL_transpose (M.map (ground.adjSwap t)) (by rw [hXl]; exact hXr)]
  refine BPair.oneValue_trans hstep ?_
  rw [detL_swapAdj t (transposeM M) (by rw [hTl]; exact ht),
    detL_transpose M (by rw [hMl]; exact hMr)]
  exact BPair.oneValue_refl _


/-- The pairing table of a column list at a datum: the
congruence's columns paired through the datum, place by place. -/
private def gramAt (S V D : Mat) (n : Nat) : Prop :=
  ∀ i j : Nat, i < n → j < n →
    (dotN (ground.getAt [] V i) (matVec S (ground.getAt [] V j))).oneValue
      (ground.getAt BPair.unit (ground.getAt [] D i) j)

/-- The pairing table is the congruence identity: the column list's
own key exchange is the congruence, and the table's entries are the
image's. -/
private theorem congr_of_gramAt (S V D : Mat) (n : Nat) (hn : 0 < n)
    (hSl : S.length = n)
    (hVl : V.length = n) (hVr : rowsLen n V)
    (hDl : D.length = n) (hDr : rowsLen n D)
    (hg : gramAt S V D n) :
    matOneValue (matMul V (matMul S (transposeM V))) D := by
  have hTVl : (transposeM V).length = n := transposeLen V hVr hVl
  have hVV : transposeM (transposeM V) = V :=
    transposeM_transposeM V hVr hn (by rw [hVl]; exact hn)
  have hXl : (matMul S (transposeM V)).length = n :=
    (elim.length_matMul S _).trans hSl
  have hXr : rowsLen n (matMul S (transposeM V)) :=
    rowsLen_cast (by rw [hVV, hVl]) (rowsLen_matMul S (transposeM V))
  have hTXl : (transposeM (matMul S (transposeM V))).length = n :=
    transposeLen _ hXr hXl
  have hTXr : rowsLen n (transposeM (matMul S (transposeM V))) :=
    rowsLen_cast hXl (rowsLen_transposeM _)
  have hcol : ∀ j, j < n →
      poly.oneValue (ground.getAt [] (transposeM (matMul S (transposeM V))) j)
        (matVec S (ground.getAt [] V j)) := by
    intro j hj
    refine poly.oneValue_of_entries _ _ ?_ ?_
    · rw [rowsLen_getAt _ j hTXr (by rw [hTXl]; exact hj),
        matVec_length, hSl]
    · intro p hp
      rw [rowsLen_getAt _ j hTXr (by rw [hTXl]; exact hj)] at hp
      rw [getAt_transposeM BPair.unit _ hXr j p hj (by rw [hXl]; exact hp),
        getAt_matMul S (transposeM V) p (by rw [hSl]; exact hp), hVV,
        ground.getAt_map ([] : List BPair) BPair.unit
          (fun c => dotN (ground.getAt [] S p) c) V j
          (by rw [hVl]; exact hj)]
      exact BPair.oneValue_of_eq
        (ground.getAt_map ([] : List BPair) BPair.unit
          (fun r => dotN r (ground.getAt [] V j)) S p
          (by rw [hSl]; exact hp)).symm
  refine matOne_of_entries _ D n (by rw [elim.length_matMul, hVl])
    (rowsLen_cast hTXl (rowsLen_matMul V _)) hDl hDr ?_
  intro i j hi hj
  rw [getAt_matMul V _ i (by rw [hVl]; exact hi),
    ground.getAt_map ([] : List BPair) BPair.unit
      (fun c => dotN (ground.getAt [] V i) c) _ j
      (by rw [hTXl]; exact hj)]
  exact BPair.oneValue_trans (dotN_congrR _ _ _ (hcol j hj)) (hg i j hi hj)

/-- The adjugate's shape at a square list. -/
private theorem sqAt_adjM (T : Mat) (n : Nat) (hn : 0 < n) (hT : sqAt T n) :
    sqAt (adjM T) n := by
  have hTl : T.length = n := sqAt_len hT
  have hCl : ((List.range T.length).map (fun k => cofVec T k)).length = n :=
    (cofRows_len T).trans hTl
  have hCr : rowsLen n ((List.range T.length).map (fun k => cofVec T k)) :=
    rowsLen_cast hTl (cofRows_rowsLen T)
  refine sqAt_of ?_ ?_
  · show (transposeM ((List.range T.length).map (fun k => cofVec T k))).length
      = n
    exact length_transposeM _ hCr (by rw [hCl]; exact hn)
  · show rowsLen n
      (transposeM ((List.range T.length).map (fun k => cofVec T k)))
    exact rowsLen_cast hCl (rowsLen_transposeM _)

/-- The adjugate is the cleared congruence's witness: the two
product reads are the adjugate identity's rows and columns, the
determinant off equal members the clearing. -/
private theorem cleared_adjM (T : Mat) (n : Nat) (hn : 0 < n) (hT : sqAt T n)
    (hd : ¬ (detL T).oneValue BPair.unit) :
    clearedCongr (o := n) ⟨T, hT⟩ ⟨adjM T, sqAt_adjM T n hn hT⟩ := by
  have hTl : T.length = n := sqAt_len hT
  have hTr : rowsLen n T := rowsLen_of_sqAt hT
  have hAl : (adjM T).length = n := sqAt_len (sqAt_adjM T n hn hT)
  have hAr : rowsLen n (adjM T) := rowsLen_of_sqAt (sqAt_adjM T n hn hT)
  have hmd : (minor T).oneValue (detL T) :=
    minor_detL T (rowsLen_cast hTl.symm hTr)
  have hoff : ¬ (minor T).oneValue BPair.unit := fun h =>
    hd (BPair.oneValue_trans (BPair.oneValue_symm hmd) h)
  have hIl : (idMat n).length = n := idMat_len n
  have hIr : rowsLen n (idMat n) := idMat_rows n
  have hRl : (matScaleB (minor T) (idMat n)).length = n :=
    (length_scaleB _ _).trans hIl
  have hRr : rowsLen n (matScaleB (minor T) (idMat n)) :=
    rowsLen_scaleB _ n _ hIr
  have hRe : ∀ i j, i < n → j < n →
      ground.getAt BPair.unit
          (ground.getAt [] (matScaleB (minor T) (idMat n)) i) j
        = (minor T * (if j = i then BPair.ofNat 1 else BPair.unit)).norm := by
    intro i j hi hj
    rw [entry_scaleB (minor T) (idMat n) n hIr i j (by rw [hIl]; exact hi) hj,
      getAt_idMat n i j hi hj]
  have hdiag : ∀ i, i < n →
      ((minor T * (if i = i then BPair.ofNat 1 else BPair.unit)).norm).oneValue
        (detL T) := by
    intro i _
    rw [if_pos rfl]
    exact BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans (BPair.mul_one_read (minor T)) hmd)
  have hoffd : ∀ i j : Nat, ¬ j = i →
      ((minor T * (if j = i then BPair.ofNat 1 else BPair.unit)).norm).oneValue
        BPair.unit := by
    intro i j hne
    rw [if_neg hne]
    exact BPair.oneValue_trans (BPair.norm_oneValue _)
      (elim.oneValue_mul_unit (minor T) BPair.unit (BPair.oneValue_refl BPair.unit))
  refine ⟨hoff, ?_, ?_⟩
  · refine matOne_of_entries _ _ n
      (by rw [elim.length_matMul]; exact hTl)
      (rowsLen_cast (transposeLen (adjM T) hAr hAl) (rowsLen_matMul T (adjM T)))
      hRl hRr ?_
    intro i j hi hj
    rw [hRe i j hi hj]
    by_cases he : j = i
    · rw [he]
      exact BPair.oneValue_trans (adjM_row_diag T hT i hi)
        (BPair.oneValue_symm (hdiag i hi))
    · exact BPair.oneValue_trans (adjM_row_off T hT i j hi hj
        (fun h => he h.symm))
        (BPair.oneValue_symm (hoffd i j he))
  · refine matOne_of_entries _ _ n
      (by rw [elim.length_matMul]; exact hAl)
      (rowsLen_cast (transposeLen T hTr hTl) (rowsLen_matMul (adjM T) T))
      hRl hRr ?_
    intro i j hi hj
    rw [hRe i j hi hj]
    by_cases he : j = i
    · rw [he]
      exact BPair.oneValue_trans (adjM_col_diag T hT i hi)
        (BPair.oneValue_symm (hdiag i hi))
    · exact BPair.oneValue_trans (adjM_col_off T hT i j hi hj
        (fun h => he h.symm))
        (BPair.oneValue_symm (hoffd i j he))


/-- A repeated unit family reads the sum's unit at every key. -/
private theorem getAt_repl_unit : ∀ W j : Nat,
    ground.getAt BPair.unit (List.replicate W BPair.unit) j = BPair.unit
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | W + 1, j + 1 => getAt_repl_unit W j

/-- The block diagonal's row count is the assembled width. -/
theorem blockMat_len : ∀ (bs : List SBlock) (k : Nat),
    (blockMat bs k).length = widthOf bs k
  | [], k => by
    show ((List.range k).map
      (fun _ => List.replicate k BPair.unit)).length = k
    rw [ground.length_map, ground.length_range]
  | SBlock.one _ :: bs, k => by
    show ((blockMat bs k).map (fun r => BPair.unit :: r)).length + 1
      = widthOf bs (k + 1)
    rw [ground.length_map, blockMat_len bs k, widthOf_shift bs k 1]
  | SBlock.two _ _ _ :: bs, k => by
    show ((blockMat bs k).map
      (fun r => BPair.unit :: BPair.unit :: r)).length + 1 + 1
      = widthOf bs (k + 2)
    rw [ground.length_map, blockMat_len bs k, widthOf_shift bs k 2]

/-- The block diagonal's rows sit at the assembled width. -/
theorem blockMat_rows : ∀ (bs : List SBlock) (k : Nat),
    rowsLen (widthOf bs k) (blockMat bs k)
  | [], k =>
    rowsLen_map (fun _ => List.replicate k BPair.unit) k (List.range k)
      (fun _ _ => ground.length_replicate BPair.unit k)
  | SBlock.one _ :: bs, k => by
    refine ⟨?_, ?_⟩
    · show (List.replicate (widthOf bs k) BPair.unit).length + 1
        = widthOf bs (k + 1)
      rw [ground.length_replicate, widthOf_shift bs k 1]
    · refine rowsLen_map (fun r => BPair.unit :: r) (widthOf bs (k + 1))
        (blockMat bs k) ?_
      intro r hr
      show r.length + 1 = widthOf bs (k + 1)
      rw [rowsLen_memLen (blockMat bs k) (blockMat_rows bs k) r hr,
        widthOf_shift bs k 1]
  | SBlock.two _ _ _ :: bs, k => by
    refine ⟨?_, ?_, ?_⟩
    · show (List.replicate (widthOf bs k) BPair.unit).length + 1 + 1
        = widthOf bs (k + 2)
      rw [ground.length_replicate, widthOf_shift bs k 2]
    · show (List.replicate (widthOf bs k) BPair.unit).length + 1 + 1
        = widthOf bs (k + 2)
      rw [ground.length_replicate, widthOf_shift bs k 2]
    · refine rowsLen_map (fun r => BPair.unit :: BPair.unit :: r)
        (widthOf bs (k + 2)) (blockMat bs k) ?_
      intro r hr
      show r.length + 1 + 1 = widthOf bs (k + 2)
      rw [rowsLen_memLen (blockMat bs k) (blockMat_rows bs k) r hr,
        widthOf_shift bs k 2]

/-- The one-block diagonal's width is the block's order. -/
private theorem widthOf_single (blk : SBlock) : widthOf [blk] 0 = blk.order :=
  Nat.zero_add _

/-- The block's own square, the one-block diagonal. -/
private theorem sqAt_blockOne (blk : SBlock) :
    sqAt (blockMat [blk] 0) blk.order :=
  sqAt_of ((blockMat_len [blk] 0).trans (widthOf_single blk))
    (rowsLen_cast (widthOf_single blk) (blockMat_rows [blk] 0))

/-- The block diagonal's leading square is the block's own. -/
private theorem blockMat_head (blk : SBlock) (bs : List SBlock) (kn : Nat)
    (i j : Nat) (hi : i < blk.order) (hj : j < blk.order) :
    ground.getAt BPair.unit (ground.getAt [] (blockMat (blk :: bs) kn) i) j
      = ground.getAt BPair.unit
        (ground.getAt [] (blockMat [blk] 0) i) j := by
  cases blk with
  | one _ =>
    cases i with
    | succ i => exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero i)
    | zero =>
      cases j with
      | succ j => exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
      | zero => rfl
  | two _ _ _ =>
    cases i with
    | succ i =>
      cases i with
      | succ i =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))
          (Nat.not_lt_zero i)
      | zero =>
        cases j with
        | succ j =>
          cases j with
          | succ j =>
            exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj))
              (Nat.not_lt_zero j)
          | zero => rfl
        | zero => rfl
    | zero =>
      cases j with
      | succ j =>
        cases j with
        | succ j =>
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj))
            (Nat.not_lt_zero j)
        | zero => rfl
      | zero => rfl

/-- The block diagonal's coupling reads equal members: the leading
block's rows against the descent's remaining places. -/
private theorem blockMat_cross (blk : SBlock) (bs : List SBlock) (kn : Nat)
    (i j : Nat) (hi : i < blk.order) :
    ground.getAt BPair.unit
        (ground.getAt [] (blockMat (blk :: bs) kn) i) (blk.order + j)
      = BPair.unit := by
  cases blk with
  | one _ =>
    cases i with
    | succ i => exact absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero i)
    | zero =>
      show ground.getAt BPair.unit
        (_ :: List.replicate (widthOf bs kn) BPair.unit) (1 + j) = BPair.unit
      rw [Nat.add_comm 1 j]
      exact getAt_repl_unit (widthOf bs kn) j
  | two _ _ _ =>
    have hrep : ∀ x y : BPair,
        ground.getAt BPair.unit
            (x :: y :: List.replicate (widthOf bs kn) BPair.unit) (2 + j)
          = BPair.unit := by
      intro x y
      rw [Nat.add_comm 2 j]
      show ground.getAt BPair.unit
        (List.replicate (widthOf bs kn) BPair.unit) j = BPair.unit
      exact getAt_repl_unit (widthOf bs kn) j
    cases i with
    | succ i =>
      cases i with
      | succ i =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))
          (Nat.not_lt_zero i)
      | zero => exact hrep _ _
    | zero => exact hrep _ _

/-- The block diagonal's exchanged coupling reads equal members. -/
private theorem blockMat_crossT (blk : SBlock) (bs : List SBlock) (kn : Nat)
    (i j : Nat) (hi : i < widthOf bs kn) (hj : j < blk.order) :
    ground.getAt BPair.unit
        (ground.getAt [] (blockMat (blk :: bs) kn) (blk.order + i)) j
      = BPair.unit := by
  have hlen : (blockMat bs kn).length = widthOf bs kn := blockMat_len bs kn
  cases blk with
  | one a =>
    have hrow : ground.getAt ([] : List BPair)
        (blockMat (SBlock.one a :: bs) kn) (1 + i)
        = BPair.unit :: ground.getAt [] (blockMat bs kn) i := by
      rw [Nat.add_comm 1 i]
      show ground.getAt ([] : List BPair)
        ((blockMat bs kn).map (fun r => BPair.unit :: r)) i = _
      exact ground.getAt_map ([] : List BPair) ([] : List BPair)
        (fun r => BPair.unit :: r) (blockMat bs kn) i (by rw [hlen]; exact hi)
    show ground.getAt BPair.unit
      (ground.getAt [] (blockMat (SBlock.one a :: bs) kn) (1 + i)) j
      = BPair.unit
    rw [hrow]
    cases j with
    | zero => rfl
    | succ j => exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
  | two a b c =>
    have hrow : ground.getAt ([] : List BPair)
        (blockMat (SBlock.two a b c :: bs) kn) (2 + i)
        = BPair.unit :: BPair.unit :: ground.getAt [] (blockMat bs kn) i := by
      rw [Nat.add_comm 2 i]
      show ground.getAt ([] : List BPair)
        ((blockMat bs kn).map (fun r => BPair.unit :: BPair.unit :: r)) i = _
      exact ground.getAt_map ([] : List BPair) ([] : List BPair)
        (fun r => BPair.unit :: BPair.unit :: r) (blockMat bs kn) i
        (by rw [hlen]; exact hi)
    show ground.getAt BPair.unit
      (ground.getAt [] (blockMat (SBlock.two a b c :: bs) kn) (2 + i)) j
      = BPair.unit
    rw [hrow]
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj))
          (Nat.not_lt_zero j)

/-- The block diagonal's trailing square is the descent's own. -/
private theorem blockMat_tail (blk : SBlock) (bs : List SBlock) (kn : Nat)
    (i j : Nat) (hi : i < widthOf bs kn) :
    ground.getAt BPair.unit
        (ground.getAt [] (blockMat (blk :: bs) kn) (blk.order + i))
        (blk.order + j)
      = ground.getAt BPair.unit (ground.getAt [] (blockMat bs kn) i) j := by
  have hlen : (blockMat bs kn).length = widthOf bs kn := blockMat_len bs kn
  cases blk with
  | one a =>
    have hrow : ground.getAt ([] : List BPair)
        (blockMat (SBlock.one a :: bs) kn) (1 + i)
        = BPair.unit :: ground.getAt [] (blockMat bs kn) i := by
      rw [Nat.add_comm 1 i]
      show ground.getAt ([] : List BPair)
        ((blockMat bs kn).map (fun r => BPair.unit :: r)) i = _
      exact ground.getAt_map ([] : List BPair) ([] : List BPair)
        (fun r => BPair.unit :: r) (blockMat bs kn) i (by rw [hlen]; exact hi)
    show ground.getAt BPair.unit
      (ground.getAt [] (blockMat (SBlock.one a :: bs) kn) (1 + i)) (1 + j)
      = ground.getAt BPair.unit (ground.getAt [] (blockMat bs kn) i) j
    rw [hrow, Nat.add_comm 1 j]
    rfl
  | two a b c =>
    have hrow : ground.getAt ([] : List BPair)
        (blockMat (SBlock.two a b c :: bs) kn) (2 + i)
        = BPair.unit :: BPair.unit :: ground.getAt [] (blockMat bs kn) i := by
      rw [Nat.add_comm 2 i]
      show ground.getAt ([] : List BPair)
        ((blockMat bs kn).map (fun r => BPair.unit :: BPair.unit :: r)) i = _
      exact ground.getAt_map ([] : List BPair) ([] : List BPair)
        (fun r => BPair.unit :: BPair.unit :: r) (blockMat bs kn) i
        (by rw [hlen]; exact hi)
    show ground.getAt BPair.unit
      (ground.getAt [] (blockMat (SBlock.two a b c :: bs) kn) (2 + i)) (2 + j)
      = ground.getAt BPair.unit (ground.getAt [] (blockMat bs kn) i) j
    rw [hrow, Nat.add_comm 2 j]
    rfl

/-! The pivot step's pairing table: the padded pivot vectors, the
lifted deflation vectors, and the two cross pairings — the
addition's own reads (`quad_padJ`, `quad_lift`) taken at two
arguments, the table's entries rather than its diagonal. -/

/-- The padded vectors' pairing at a join is the pivot block's
own. -/
private theorem quad_padB (P B Q : Mat) (k m : Nat)
    (hPr : rowsLen k P) (hPl : P.length = k) (hBl : B.length = k)
    (hBt : (transposeM B).length = m)
    (hBtr : rowsLen k (transposeM B)) (hQl : Q.length = m)
    (x x' : List BPair) (hx : x.length = k) (hx' : x'.length = k) :
    (dotN (x ++ List.replicate m BPair.unit)
        (matVec (blockJoin P B Q)
          (x' ++ List.replicate m BPair.unit))).oneValue
      (dotN x (matVec P x')) := by
  have hU : poly.unitTail (List.replicate m BPair.unit) :=
    poly.unitTail_replicate m
  refine BPair.oneValue_trans
    (quadJoin P B Q k m hPr hPl hBl hBt hBtr hQl x _ x' _ hx
      (ground.length_replicate BPair.unit m) hx') ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (BPair.oneValue_refl _)
        (dotN_nullR x _ (matVec_null B _ hU)))
      (BPair.add_congr (dotN_nullL _ _ hU) (dotN_nullL _ _ hU))) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.add_unit _) (BPair.unit_add BPair.unit))
    (BPair.add_unit _)

/-- The deflation's pairing at the cleared carrier, at two
arguments. -/
private theorem quad_deflB (P B Q Cw : Mat) (k m : Nat) (w w' : List BPair)
    (hw : w.length = m) (hw' : w'.length = m)
    (hBl : B.length = k) (hBr : rowsLen m B)
    (hQr : rowsLen m Q) (hQl : Q.length = m)
    (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hCt : (transposeM Cw).length = m) (hBt : (transposeM B).length = m)
    (hBtr : rowsLen k (transposeM B)) :
    (dotN w (matVec (deflMat P B Q Cw) w')).oneValue
      ((minor P * minor P) * dotN w (matVec Q w')
        + (minor P).swap * dotN (matVec Cw w') (matVec B w)) := by
  have hMr : rowsLen m (matMul (transposeM B) Cw) :=
    rowsLen_cast hCt (rowsLen_matMul (transposeM B) Cw)
  have hMl : (matMul (transposeM B) Cw).length = m :=
    (ground.length_map _ (transposeM B)).trans hBt
  have hXr : rowsLen w'.length (matScaleB (minor P * minor P) Q) :=
    rowsLen_cast hw'.symm (rowsLen_scaleB _ m Q hQr)
  have hYr : rowsLen w'.length
      (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw))) :=
    rowsLen_cast hw'.symm
      (rowsLen_mapRows BPair.swap _ m (rowsLen_scaleB _ m _ hMr))
  have hXl : (matVec (matScaleB (minor P * minor P) Q) w').length
      = w.length := by
    rw [matVec_length, length_scaleB, hQl, hw]
  have hYl : (matVec
      (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw)))
      w').length = w.length := by
    rw [matVec_length]
    show ((matScaleB (minor P) (matMul (transposeM B) Cw)).map
      (fun r => r.map BPair.swap)).length = w.length
    rw [ground.length_map, length_scaleB, hMl, hw]
  refine BPair.oneValue_trans
    (dotN_congrR w _ _ (matVec_add _ _ w' hXr hYr)) ?_
  refine BPair.oneValue_trans (elim.dotN_addRow_right w _ _ hXl hYl) ?_
  refine BPair.add_congr ?_ ?_
  · exact BPair.oneValue_trans
      (dotN_congrR w _ _ (matVec_scaleB (minor P * minor P) Q w'))
      (elim.dotN_scaleV _ w (matVec Q w'))
  · rw [matVec_swapM (matScaleB (minor P) (matMul (transposeM B) Cw)) w',
      dotN_swap]
    refine BPair.oneValue_trans
      (ground.swap_congr
        (BPair.oneValue_trans
          (dotN_congrR w _ _
            (matVec_scaleB (minor P) (matMul (transposeM B) Cw) w'))
          (BPair.oneValue_trans
            (elim.dotN_scaleV (minor P) w
              (matVec (matMul (transposeM B) Cw) w'))
            (BPair.mul_congr (BPair.oneValue_refl (minor P))
              (BPair.oneValue_trans
                (dotN_congrR w _ _
                  (poly.oneValue_symm
                    (matVec_comp (transposeM B) Cw w' m hCr hw'
                      (rowsLen_cast hCl.symm hBtr))))
                (adjB B k m hBl hBr w hw (matVec Cw w')
                  ((matVec_length Cw w').trans hCl))))))) ?_
    exact BPair.oneValue_of_eq
      (BPair.swap_mul (minor P) (dotN (matVec Cw w') (matVec B w))).symm

/-- The lifted vectors' pairing is the deflation's own, at two
arguments. -/
private theorem quad_liftB (P B Q Cw : Mat) (k m : Nat) (w w' : List BPair)
    (hw : w.length = m) (hw' : w'.length = m)
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBl : B.length = k) (hBr : rowsLen m B)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQr : rowsLen m Q) (hQl : Q.length = m)
    (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hCt : (transposeM Cw).length = m)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B)) :
    (dotN (matVec Cw w ++ vecScale (minor P).swap w)
        (matVec (blockJoin P B Q)
          (matVec Cw w' ++ vecScale (minor P).swap w'))).oneValue
      (dotN w (matVec (deflMat P B Q Cw) w')) := by
  have ha : (matVec Cw w).length = k := (matVec_length Cw w).trans hCl
  have ha' : (matVec Cw w').length = k := (matVec_length Cw w').trans hCl
  have hb : (vecScale (minor P).swap w).length = m :=
    (length_vecScale _ w).trans hw
  have hT1 : (dotN (matVec Cw w) (matVec P (matVec Cw w'))).oneValue
      (minor P * dotN (matVec Cw w) (matVec B w')) :=
    BPair.oneValue_trans
      (dotN_congrR _ _ _ (pivotSolve P B Cw k m hPr hCl hCr hPw w' hw'))
      (elim.dotN_scaleV _ _ (matVec B w'))
  have hT2 : (dotN (matVec Cw w)
      (matVec B (vecScale (minor P).swap w'))).oneValue
      ((minor P).swap * dotN (matVec Cw w) (matVec B w')) :=
    BPair.oneValue_trans
      (dotN_congrR _ _ _ (matVec_vecScale_free B (minor P).swap w'))
      (elim.dotN_scaleV _ _ (matVec B w'))
  have hT3 : (dotN (vecScale (minor P).swap w)
      (matVec (transposeM B) (matVec Cw w'))).oneValue
      ((minor P).swap * dotN (matVec Cw w') (matVec B w)) :=
    BPair.oneValue_trans (elim.dotN_comm _ _)
      (BPair.oneValue_trans (elim.dotN_scaleV _ _ w)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (elim.dotN_comm _ _)
            (adjB B k m hBl hBr w hw (matVec Cw w') ha'))))
  have hT4 : (dotN (vecScale (minor P).swap w)
      (matVec Q (vecScale (minor P).swap w'))).oneValue
      ((minor P).swap * ((minor P).swap * dotN w (matVec Q w'))) :=
    BPair.oneValue_trans (elim.dotN_comm _ _)
      (BPair.oneValue_trans (elim.dotN_scaleV _ _ w)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (elim.dotN_comm _ _)
            (BPair.oneValue_trans
              (dotN_congrR w _ _
                (matVec_vecScale_free Q (minor P).swap w'))
              (elim.dotN_scaleV _ w (matVec Q w'))))))
  have hsq : ((minor P).swap * ((minor P).swap * dotN w (matVec Q w')))
      = (minor P * minor P) * dotN w (matVec Q w') :=
    (BPair.mul_assoc _ _ _).symm.trans
      (congrArg (fun z => z * dotN w (matVec Q w')) (BPair.swap_sq (minor P)))
  refine BPair.oneValue_trans
    (quadJoin P B Q k m hPr hPl hBl hBt hBtr hQl _ _ _ _ ha hb ha') ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.add_congr hT1 hT2)
      (BPair.add_congr hT3 hT4)) ?_
  rw [hsq]
  refine BPair.oneValue_trans
    (BPair.add_congr (detKill P (dotN (matVec Cw w) (matVec B w')))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
  exact BPair.oneValue_symm
    (quad_deflB P B Q Cw k m w w' hw hw' hBl hBr hQr hQl hCl hCr hCt hBt hBtr)

/-- The pivot step's column list: the pivot block's own places
above, the deflation's columns lifted through the solve witness
beneath — the congruence's columns at the step's own order. -/
private def liftV (Cw : Mat) (d : BPair) (k m : Nat) (VD : Mat) : Mat :=
  rowJoin (idMat k) (nullMat k m)
    ++ rowJoin (VD.map (matVec Cw)) (VD.map (vecScale d.swap))

/-- The step's column list has the step's own order. -/
private theorem liftV_len (Cw : Mat) (d : BPair) (k m : Nat) (VD : Mat)
    (hVl : VD.length = m) : (liftV Cw d k m VD).length = k + m := by
  show (rowJoin (idMat k) (nullMat k m)
    ++ rowJoin (VD.map (matVec Cw)) (VD.map (vecScale d.swap))).length = k + m
  have h1 : (rowJoin (idMat k) (nullMat k m)).length = k :=
    ground.length_zipWith (· ++ ·) (idMat k) (nullMat k m) k (idMat_len k)
      (length_nullMat k m)
  have h2 : (rowJoin (VD.map (matVec Cw)) (VD.map (vecScale d.swap))).length
      = m :=
    ground.length_zipWith (· ++ ·) (VD.map (matVec Cw))
      (VD.map (vecScale d.swap)) m
      ((ground.length_map _ VD).trans hVl)
      ((ground.length_map _ VD).trans hVl)
  rw [ground.length_append, h1, h2]

/-- The step's column list has the step's own width. -/
private theorem liftV_rows (Cw : Mat) (d : BPair) (k m : Nat) (VD : Mat)
    (hCl : Cw.length = k) (hVr : rowsLen m VD) :
    rowsLen (k + m) (liftV Cw d k m VD) := by
  refine rowsLen_append (k + m)
    (rowsLen_rowJoin k m (idMat_rows k) (rowsLen_nullMat k m)) ?_
  refine rowsLen_rowJoin k m ?_ ?_
  · exact rowsLen_map (matVec Cw) k VD
      (fun x _ => (matVec_length Cw x).trans hCl)
  · refine rowsLen_map (vecScale d.swap) m VD ?_
    intro x hx
    exact (length_vecScale d.swap x).trans (rowsLen_memLen VD hVr x hx)

/-- The step's leading columns are the pivot block's own places. -/
private theorem liftV_head (Cw : Mat) (d : BPair) (k m : Nat) (VD : Mat)
    (i : Nat) (hi : i < k) :
    ground.getAt [] (liftV Cw d k m VD) i
      = idRow k i ++ List.replicate m BPair.unit := by
  have hJl : (rowJoin (idMat k) (nullMat k m)).length = k :=
    ground.length_zipWith (· ++ ·) _ _ k (idMat_len k) (length_nullMat k m)
  show ground.getAt ([] : List BPair)
    (rowJoin (idMat k) (nullMat k m)
      ++ rowJoin (VD.map (matVec Cw)) (VD.map (vecScale d.swap))) i = _
  rw [ground.getAt_append ([] : List BPair) _ _ i, hJl, if_pos hi,
    getAt_rowJoin (idMat k) (nullMat k m) i (by rw [idMat_len]; exact hi)
      (by rw [length_nullMat]; exact hi),
    idMat_row k i hi]
  show idRow k i ++ ground.getAt ([] : List BPair)
    (List.replicate k (List.replicate m BPair.unit)) i = _
  rw [ground.getAt_replicate ([] : List BPair)
    (List.replicate m BPair.unit) k i hi]

/-- The step's trailing columns are the deflation's own, lifted
through the solve witness. -/
private theorem liftV_tail (Cw : Mat) (d : BPair) (k m : Nat) (VD : Mat)
    (hVl : VD.length = m) (j : Nat) (hj : j < m) :
    ground.getAt [] (liftV Cw d k m VD) (k + j)
      = matVec Cw (ground.getAt [] VD j)
        ++ vecScale d.swap (ground.getAt [] VD j) := by
  have hJl : (rowJoin (idMat k) (nullMat k m)).length = k :=
    ground.length_zipWith (· ++ ·) _ _ k (idMat_len k) (length_nullMat k m)
  have hMl : (VD.map (matVec Cw)).length = m :=
    (ground.length_map _ VD).trans hVl
  have hNl : (VD.map (vecScale d.swap)).length = m :=
    (ground.length_map _ VD).trans hVl
  show ground.getAt ([] : List BPair)
    (rowJoin (idMat k) (nullMat k m)
      ++ rowJoin (VD.map (matVec Cw)) (VD.map (vecScale d.swap)))
    (k + j) = _
  have hstep := ground.getAt_append_add ([] : List BPair)
    (rowJoin (idMat k) (nullMat k m))
    (rowJoin (VD.map (matVec Cw)) (VD.map (vecScale d.swap))) j
  rw [hJl] at hstep
  rw [hstep,
    getAt_rowJoin _ _ j (by rw [hMl]; exact hj) (by rw [hNl]; exact hj),
    ground.getAt_map ([] : List BPair) ([] : List BPair) (matVec Cw) VD j
      (by rw [hVl]; exact hj),
    ground.getAt_map ([] : List BPair) ([] : List BPair)
      (vecScale d.swap) VD j (by rw [hVl]; exact hj)]

/-- A pivot block's order is occupied. -/
theorem order_pos (blk : SBlock) : 0 < blk.order := by
  cases blk with
  | one _ => exact Nat.succ_pos 0
  | two _ _ _ => exact Nat.succ_pos 1

/-- A pivot block's own square is symmetric. -/
private theorem blockOne_symm (blk : SBlock) :
    matOneValue (transposeM (blockMat [blk] 0)) (blockMat [blk] 0) := by
  cases blk with
  | one a => exact matOne_refl [[a]]
  | two a b c => exact matOne_refl [[a, b], [b, c]]

/-- The pivot step's pairing table: the leading places read the
pivot block's own square, the trailing ones the deflation's table,
and the two couplings read equal members — `lem:inertia`'s cleared
clearing at the block diagonal. -/
private theorem gram_step (blk : SBlock) (bs : List SBlock) (kn m : Nat)
    (S B Q Cw VD : Mat)
    (hm : widthOf bs kn = m)
    (hSJ : matOneValue S (blockJoin (blockMat [blk] 0) B Q))
    (hBl : B.length = blk.order) (hBr : rowsLen m B)
    (hQl : Q.length = m) (hQr : rowsLen m Q)
    (hCl : Cw.length = blk.order) (hCr : rowsLen m Cw)
    (hVl : VD.length = m) (hVr : rowsLen m VD)
    (hPw : matOneValue (matMul (blockMat [blk] 0) Cw)
      (matScaleB (minor (blockMat [blk] 0)) B))
    (hg : gramAt (deflMat (blockMat [blk] 0) B Q Cw) VD (blockMat bs kn) m) :
    gramAt S (liftV Cw (minor (blockMat [blk] 0)) blk.order m VD)
      (blockMat (blk :: bs) kn) (blk.order + m) := by
  have hk : 0 < blk.order := order_pos blk
  have hPl : (blockMat [blk] 0).length = blk.order :=
    sqAt_len (sqAt_blockOne blk)
  have hPr : rowsLen blk.order (blockMat [blk] 0) :=
    rowsLen_of_sqAt (sqAt_blockOne blk)
  have hPs : matOneValue (transposeM (blockMat [blk] 0)) (blockMat [blk] 0) :=
    blockOne_symm blk
  have hBt : (transposeM B).length = m :=
    length_transposeM B hBr (by rw [hBl]; exact hk)
  have hBtr : rowsLen blk.order (transposeM B) :=
    rowsLen_cast hBl (rowsLen_transposeM B)
  have hCt : (transposeM Cw).length = m :=
    length_transposeM Cw hCr (by rw [hCl]; exact hk)
  have htr : ∀ u v : List BPair,
      (dotN u (matVec S v)).oneValue
        (dotN u (matVec (blockJoin (blockMat [blk] 0) B Q) v)) :=
    fun u v => dotN_matVec_congrM S _ u v hSJ
  intro i j hi hj
  cases Nat.lt_or_ge i blk.order with
  | inl hik =>
    rw [liftV_head Cw (minor (blockMat [blk] 0)) blk.order m VD i hik]
    cases Nat.lt_or_ge j blk.order with
    | inl hjk =>
      rw [liftV_head Cw (minor (blockMat [blk] 0)) blk.order m VD j hjk,
        blockMat_head blk bs kn i j hik hjk]
      refine BPair.oneValue_trans (htr _ _) ?_
      refine BPair.oneValue_trans
        (quad_padB (blockMat [blk] 0) B Q blk.order m hPr hPl hBl hBt hBtr
          hQl (idRow blk.order i) (idRow blk.order j)
          (length_idRow blk.order i) (length_idRow blk.order j)) ?_
      refine BPair.oneValue_trans (elim.dotN_comm _ _) ?_
      refine BPair.oneValue_trans (dotN_read _ _) ?_
      refine BPair.oneValue_trans
        (dotP_idRow (matVec (blockMat [blk] 0) (idRow blk.order j))
          blk.order i
          ((matVec_length _ _).trans hPl) hik) ?_
      have hmv : ground.getAt BPair.unit
          (matVec (blockMat [blk] 0) (idRow blk.order j)) i
          = dotN (ground.getAt [] (blockMat [blk] 0) i) (idRow blk.order j) :=
        ground.getAt_map ([] : List BPair) BPair.unit
          (fun r => dotN r (idRow blk.order j)) (blockMat [blk] 0) i
          (by rw [hPl]; exact hik)
      rw [hmv]
      refine BPair.oneValue_trans (dotN_read _ _) ?_
      exact dotP_idRow (ground.getAt [] (blockMat [blk] 0) i) blk.order j
        (rowsLen_getAt _ i hPr (by rw [hPl]; exact hik)) hjk
    | inr hjk =>
      match Nat.le.dest hjk with
      | ⟨j', hj'⟩ =>
        subst hj'
        have hj'm : j' < m := Nat.lt_of_add_lt_add_left hj
        rw [liftV_tail Cw (minor (blockMat [blk] 0)) blk.order m VD hVl
            j' hj'm,
          blockMat_cross blk bs kn i j' hik]
        refine BPair.oneValue_trans (htr _ _) ?_
        exact cross_pad_lift (blockMat [blk] 0) B Q Cw blk.order m
          (idRow blk.order i) (ground.getAt [] VD j')
          (length_idRow blk.order i)
          (rowsLen_getAt VD j' hVr (by rw [hVl]; exact hj'm))
          hPr hPl hBl hBt hBtr hQl hCl hCr hPw
  | inr hik =>
    match Nat.le.dest hik with
    | ⟨i', hi'⟩ =>
      subst hi'
      have hi'm : i' < m := Nat.lt_of_add_lt_add_left hi
      have hwi : (ground.getAt ([] : List BPair) VD i').length = m :=
        rowsLen_getAt VD i' hVr (by rw [hVl]; exact hi'm)
      rw [liftV_tail Cw (minor (blockMat [blk] 0)) blk.order m VD hVl i' hi'm]
      cases Nat.lt_or_ge j blk.order with
      | inl hjk =>
        rw [liftV_head Cw (minor (blockMat [blk] 0)) blk.order m VD j hjk,
          blockMat_crossT blk bs kn i' j (by rw [hm]; exact hi'm) hjk]
        refine BPair.oneValue_trans (htr _ _) ?_
        exact cross_lift_pad (blockMat [blk] 0) B Q Cw blk.order m
          (idRow blk.order j) (ground.getAt [] VD i')
          (length_idRow blk.order j) hwi
          hPr hPl hBl hBr hBt hBtr hQl hCl hCr hPs hPw
      | inr hjk =>
        match Nat.le.dest hjk with
        | ⟨j', hj'⟩ =>
          subst hj'
          have hj'm : j' < m := Nat.lt_of_add_lt_add_left hj
          have hwj : (ground.getAt ([] : List BPair) VD j').length = m :=
            rowsLen_getAt VD j' hVr (by rw [hVl]; exact hj'm)
          rw [liftV_tail Cw (minor (blockMat [blk] 0)) blk.order m VD hVl
              j' hj'm,
            blockMat_tail blk bs kn i' j' (by rw [hm]; exact hi'm)]
          refine BPair.oneValue_trans (htr _ _) ?_
          refine BPair.oneValue_trans
            (quad_liftB (blockMat [blk] 0) B Q Cw blk.order m
              (ground.getAt [] VD i') (ground.getAt [] VD j') hwi hwj
              hPr hPl hBl hBr hBt hBtr hQr hQl hCl hCr hCt hPw) ?_
          exact hg i' j' hi'm hj'm

/-- The folds against a vacant family read the sum's unit. -/
private theorem unitTail_mapDot (r : List BPair) : ∀ L : Mat, matNull L →
    poly.unitTail (L.map (fun c => dotN r c))
  | [], _ => trivial
  | c :: L, h => ⟨dotN_nullR r c h.1, unitTail_mapDot r L h.2⟩

/-- A product against a factor of vacant columns is vacant. -/
private theorem matNull_matMul (Z : Mat) (hZ : matNull (transposeM Z)) :
    ∀ A : Mat, matNull (matMul A Z)
  | [] => trivial
  | _ :: A => ⟨unitTail_mapDot _ (transposeM Z) hZ, matNull_matMul Z hZ A⟩

/-- A rescaled vacant family is vacant. -/
private theorem matNull_mapScale (c : BPair) : ∀ Z : Mat, matNull Z →
    matNull (Z.map (vecScale c))
  | [], _ => trivial
  | r :: Z, h => ⟨unitTail_vecScale c r h.1, matNull_mapScale c Z h.2⟩

/-- A memberwise-swapped vacant family is vacant. -/
private theorem matNull_matSwap : ∀ Z : Mat, matNull Z →
    matNull (matSwap Z)
  | [], _ => trivial
  | r :: Z, h => ⟨poly.unitTail_swapMap r h.1, matNull_matSwap Z h.2⟩

/-- A matched pair's determinants read one value. -/
private theorem detL_congr_one (M N : Mat) (h : matOneValue M N) :
    (detL M).oneValue (detL N) :=
  detL_congr_letters M N (matOne_length h)
    (fun a ha b _ => matOne_entry h a b ha)

/-- The step's column list has a determinant off equal members:
the slab reduction against the pivot's own places carries the
scale's power, and the reduced list is block triangular with the
deflation's list beneath the pivot's identity. -/
private theorem detL_liftV (Cw : Mat) (d : BPair) (k m : Nat) (VD : Mat)
    (hk : 0 < k) (hCl : Cw.length = k)
    (hVl : VD.length = m) (hVr : rowsLen m VD)
    (hIk : (detL (idMat k)).oneValue (BPair.ofNat 1))
    (hdoff : ¬ d.oneValue BPair.unit)
    (hVoff : ¬ (detL VD).oneValue BPair.unit) :
    ¬ (detL (liftV Cw d k m VD)).oneValue BPair.unit := by
  have hIoff : ¬ (detL (idMat k)).oneValue BPair.unit := fun h =>
    BPair.ofNat_one_off (BPair.oneValue_trans (BPair.oneValue_symm hIk) h)
  cases Nat.eq_zero_or_pos m with
  | inl hm0 =>
    subst hm0
    have hlen : (liftV Cw d k 0 VD).length = (idMat k).length := by
      rw [liftV_len Cw d k 0 VD hVl, idMat_len k, Nat.add_zero]
    have hcong : (detL (liftV Cw d k 0 VD)).oneValue (detL (idMat k)) := by
      refine detL_congr_letters _ _ hlen ?_
      intro a ha b hb
      rw [liftV_len Cw d k 0 VD hVl, Nat.add_zero] at ha hb
      rw [liftV_head Cw d k 0 VD a ha, idMat_row k a ha,
        ground.getAt_append BPair.unit (idRow k a)
          (List.replicate 0 BPair.unit) b,
        length_idRow k a, if_pos hb]
      exact BPair.oneValue_refl _
    exact fun h => hIoff (BPair.oneValue_trans (BPair.oneValue_symm hcong) h)
  | inr hm =>
    have hWl : (VD.map (matVec Cw)).length = m :=
      (ground.length_map _ VD).trans hVl
    have hWr : rowsLen k (VD.map (matVec Cw)) :=
      rowsLen_map (matVec Cw) k VD (fun x _ => (matVec_length Cw x).trans hCl)
    have hSWl : (matSwap (VD.map (matVec Cw))).length = m :=
      (length_matSwap _).trans hWl
    have hSWr : rowsLen k (matSwap (VD.map (matVec Cw))) :=
      rowsLen_mapRows BPair.swap _ k hWr
    have hCl2 : (transposeM (matSwap (VD.map (matVec Cw)))).length = k :=
      length_transposeM _ hSWr (by rw [hSWl]; exact hm)
    have hCr2 : rowsLen m (transposeM (matSwap (VD.map (matVec Cw)))) :=
      rowsLen_cast hSWl (rowsLen_transposeM _)
    have hCC : transposeM (transposeM (matSwap (VD.map (matVec Cw))))
        = matSwap (VD.map (matVec Cw)) :=
      transposeM_transposeM _ hSWr hk (by rw [hSWl]; exact hm)
    have hIsq : sqAt (idMat k) k := sqAt_idMat k
    have hVsq : sqAt VD m := sqAt_of hVl hVr
    have hred := detL_slabReduce (idMat k) (nullMat k m) (nullMat m k) VD
      (transposeM (matSwap (VD.map (matVec Cw)))) k m d.swap hk hIsq
      (length_nullMat k m) (rowsLen_nullMat k m)
      (length_nullMat m k) (rowsLen_nullMat m k) hVsq hCl2 hCr2
    rw [hCC] at hred
    have hbt := detL_blockTri (idMat k) (nullMat k m) VD k m hIsq
      (length_nullMat k m) (rowsLen_nullMat k m) hVsq
    -- the reduced trailing slab is the step's own lift
    have hTl : (transposeM (idMat k)).length = k := by
      rw [transposeM_idMat k, idMat_len k]
    have hZ1l : ((nullMat m k).map (vecScale d.swap)).length = m :=
      (ground.length_map _ _).trans (length_nullMat m k)
    have hZ1r : rowsLen k ((nullMat m k).map (vecScale d.swap)) :=
      rowsLen_map (vecScale d.swap) k (nullMat m k)
        (fun x hx => (length_vecScale d.swap x).trans
          (rowsLen_memLen (nullMat m k) (rowsLen_nullMat m k) x hx))
    have hZ2l : (matSwap (matMul (matSwap (VD.map (matVec Cw)))
        (idMat k))).length = m := by
      rw [length_matSwap, elim.length_matMul, hSWl]
    have hZ2r : rowsLen k (matSwap (matMul (matSwap (VD.map (matVec Cw)))
        (idMat k))) :=
      rowsLen_mapRows BPair.swap _ k
        (rowsLen_cast hTl (rowsLen_matMul _ (idMat k)))
    have hU1 : matOneValue
        (matAdd ((nullMat m k).map (vecScale d.swap))
          (matSwap (matMul (matSwap (VD.map (matVec Cw))) (idMat k))))
        (VD.map (matVec Cw)) := by
      refine matOne_trans
        (matAdd_nullL (n := k) _ _
          (matNull_mapScale d.swap (nullMat m k) (matNull_nullMat k m))
          (hZ1l.trans hZ2l.symm) hZ1r hZ2r) ?_
      have hswap := matSwap_congr
        (matMul_idR (k := m) k (matSwap (VD.map (matVec Cw))) hSWr hSWl hk hm)
      rw [matSwap_matSwap] at hswap
      exact hswap
    have hN2 : matNull (matSwap (matMul (matSwap (VD.map (matVec Cw)))
        (nullMat k m))) :=
      matNull_matSwap _
        (matNull_matMul (nullMat k m)
          (matNull_transposeM (nullMat k m) (matNull_nullMat m k)) _)
    have hN2l : (matSwap (matMul (matSwap (VD.map (matVec Cw)))
        (nullMat k m))).length = m := by
      rw [length_matSwap, elim.length_matMul, hSWl]
    have hN2r : rowsLen m (matSwap (matMul (matSwap (VD.map (matVec Cw)))
        (nullMat k m))) :=
      rowsLen_mapRows BPair.swap _ m
        (rowsLen_matMul_of _ (nullMat k m)
           (fun _ => (by rw [length_nullMat]; exact hk))
           (rowsLen_nullMat k m))
    have hSVl : (VD.map (vecScale d.swap)).length = m :=
      (ground.length_map _ VD).trans hVl
    have hSVr : rowsLen m (VD.map (vecScale d.swap)) :=
      rowsLen_map (vecScale d.swap) m VD
        (fun x hx => (length_vecScale d.swap x).trans
          (rowsLen_memLen VD hVr x hx))
    have hU2 : matOneValue
        (matAdd (VD.map (vecScale d.swap))
          (matSwap (matMul (matSwap (VD.map (matVec Cw))) (nullMat k m))))
        (VD.map (vecScale d.swap)) := by
      rw [matAdd_comm]
      exact matAdd_nullL (n := m) _ _ hN2 (hN2l.trans hSVl.symm) hN2r hSVr
    have hmatch : matOneValue
        (rowJoin (idMat k) (nullMat k m)
          ++ rowJoin
            (matAdd ((nullMat m k).map (vecScale d.swap))
              (matSwap (matMul (matSwap (VD.map (matVec Cw))) (idMat k))))
            (matAdd (VD.map (vecScale d.swap))
              (matSwap (matMul (matSwap (VD.map (matVec Cw)))
                (nullMat k m)))))
        (liftV Cw d k m VD) :=
      elim.matOne_append _ _ _ _ (matOne_refl _)
        (elim.matOne_rowJoin _ _ _ _
          (rowsLen_matAdd k _ _ hZ1r hZ2r) hWr hU1 hU2)
    have hfin : (detL (liftV Cw d k m VD)).oneValue
        (ground.bpow d.swap m * (detL (idMat k) * detL VD)) := by
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm hbt)) ?_
      exact BPair.oneValue_trans hred (detL_congr_one _ _ hmatch)
    exact fun h => ground.mulOffUnit (ground.bpow_off d.swap (swapOff hdoff) m)
      (ground.mulOffUnit hIoff hVoff) (BPair.oneValue_trans (BPair.oneValue_symm hfin) h)

/-- The pairing at two indicator vectors reads the datum's entry. -/
private theorem entry_pair (M : Mat) (n i j : Nat) (hMl : M.length = n)
    (hMr : rowsLen n M) (hi : i < n) (hj : j < n) :
    (dotN (idRow n i) (matVec M (idRow n j))).oneValue
      (ground.getAt BPair.unit (ground.getAt [] M i) j) := by
  refine BPair.oneValue_trans (elim.dotN_comm _ _) ?_
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (dotP_idRow (matVec M (idRow n j)) n i
      ((matVec_length _ _).trans hMl) hi) ?_
  have hmv : ground.getAt BPair.unit (matVec M (idRow n j)) i
      = dotN (ground.getAt [] M i) (idRow n j) :=
    ground.getAt_map ([] : List BPair) BPair.unit
      (fun r => dotN r (idRow n j)) M i (by rw [hMl]; exact hi)
  rw [hmv]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  exact dotP_idRow (ground.getAt [] M i) n j
    (rowsLen_getAt M i hMr (by rw [hMl]; exact hi)) hj

/-- The datum's pairing read at the stated order: the two arguments
exchange. -/
private def pairSymAt (S : Mat) (n : Nat) : Prop :=
  ∀ u v : List BPair, u.length = n → v.length = n →
    (dotN u (matVec S v)).oneValue (dotN v (matVec S u))

/-- A symmetric datum's pairing exchanges its arguments. -/
private theorem pairSymAt_of (S : Mat) (n : Nat) (hSl : S.length = n)
    (hSr : rowsLen n S) (hsym : matOneValue (transposeM S) S) :
    pairSymAt S n := by
  intro u v hu hv
  refine BPair.oneValue_trans (dotN_read u (matVec S v)) ?_
  rw [dotP_comm u (matVec S v)]
  refine BPair.oneValue_trans
    (dotP_matVec_sym S (elim.sqAt_of hSl hSr) hsym v u hv hu) ?_
  exact BPair.oneValue_symm (dotN_read v (matVec S u))

/-- The exchanged entry read at a datum whose pairing is
symmetric. -/
private theorem entrySym (S : Mat) (n i j : Nat) (hSl : S.length = n)
    (hSr : rowsLen n S) (h : pairSymAt S n) (hi : i < n) (hj : j < n) :
    (ground.getAt BPair.unit (ground.getAt [] S i) j).oneValue
      (ground.getAt BPair.unit (ground.getAt [] S j) i) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (entry_pair S n i j hSl hSr hi hj)) ?_
  refine BPair.oneValue_trans
    (h (idRow n i) (idRow n j) (length_idRow n i) (length_idRow n j)) ?_
  exact entry_pair S n j i hSl hSr hj hi

/-- The identity splits at its leading place, block triangular with
the identity of one order below. -/
private theorem idMat_split (n : Nat) :
    matOneValue (idMat (n + 1))
      (rowJoin (idMat 1) (nullMat 1 n)
        ++ rowJoin (nullMat n 1) (idMat n)) := by
  have hAl : (rowJoin (idMat 1) (nullMat 1 n)).length = 1 :=
    ground.length_zipWith (· ++ ·) _ _ 1 (idMat_len 1) (length_nullMat 1 n)
  have hBl : (rowJoin (nullMat n 1) (idMat n)).length = n :=
    ground.length_zipWith (· ++ ·) _ _ n (length_nullMat n 1) (idMat_len n)
  have hRl : (rowJoin (idMat 1) (nullMat 1 n)
      ++ rowJoin (nullMat n 1) (idMat n)).length = n + 1 := by
    rw [ground.length_append, hAl, hBl, Nat.add_comm n 1]
  have hRr : rowsLen (n + 1) (rowJoin (idMat 1) (nullMat 1 n)
      ++ rowJoin (nullMat n 1) (idMat n)) := by
    refine rowsLen_append (n + 1) ?_ ?_
    · exact rowsLen_cast (Nat.add_comm 1 n)
        (rowsLen_rowJoin 1 n (idMat_rows 1) (rowsLen_nullMat 1 n))
    · exact rowsLen_cast (Nat.add_comm 1 n)
        (rowsLen_rowJoin 1 n (rowsLen_nullMat n 1) (idMat_rows n))
  refine matOne_of_entries _ _ (n + 1) (idMat_len (n + 1))
    (idMat_rows (n + 1)) hRl hRr ?_
  intro i j hi hj
  rw [idMat_row (n + 1) i hi, getAt_idRow (n + 1) i j hj]
  cases i with
  | zero =>
    have hrow : ground.getAt ([] : List BPair)
        (rowJoin (idMat 1) (nullMat 1 n)
          ++ rowJoin (nullMat n 1) (idMat n)) 0
        = idRow 1 0 ++ List.replicate n BPair.unit := by
      rw [ground.getAt_append ([] : List BPair) _ _ 0, hAl,
        if_pos (Nat.succ_pos 0),
        getAt_rowJoin (idMat 1) (nullMat 1 n) 0
          (by rw [idMat_len]; exact Nat.succ_pos 0)
          (by rw [length_nullMat]; exact Nat.succ_pos 0),
        idMat_row 1 0 (Nat.succ_pos 0)]
      show idRow 1 0 ++ ground.getAt ([] : List BPair)
        (List.replicate 1 (List.replicate n BPair.unit)) 0 = _
      rw [ground.getAt_replicate ([] : List BPair)
        (List.replicate n BPair.unit) 1 0 (Nat.succ_pos 0)]
    rw [hrow, ground.getAt_append BPair.unit (idRow 1 0)
      (List.replicate n BPair.unit) j, length_idRow 1 0]
    cases j with
    | zero =>
      rw [if_pos (Nat.succ_pos 0), if_pos rfl]
      exact BPair.oneValue_refl _
    | succ j =>
      rw [if_neg (fun h => Nat.not_succ_le_zero j (Nat.lt_of_succ_lt_succ h)),
        if_neg (fun h : j + 1 = 0 => Nat.noConfusion h),
        getAt_repl_unit n (j + 1 - 1)]
      exact BPair.oneValue_refl _
  | succ i =>
    have hrow : ground.getAt ([] : List BPair)
        (rowJoin (idMat 1) (nullMat 1 n)
          ++ rowJoin (nullMat n 1) (idMat n)) (i + 1)
        = List.replicate 1 BPair.unit ++ idRow n i := by
      have hin : i < n := Nat.lt_of_succ_lt_succ hi
      rw [ground.getAt_append ([] : List BPair) _ _ (i + 1), hAl,
        if_neg (fun h => Nat.not_succ_le_zero i (Nat.lt_of_succ_lt_succ h)),
        show i + 1 - 1 = i from rfl,
        getAt_rowJoin (nullMat n 1) (idMat n) i
          (by rw [length_nullMat]; exact hin)
          (by rw [idMat_len]; exact hin),
        idMat_row n i hin]
      show ground.getAt ([] : List BPair)
        (List.replicate n (List.replicate 1 BPair.unit)) i ++ idRow n i = _
      rw [ground.getAt_replicate ([] : List BPair)
        (List.replicate 1 BPair.unit) n i hin]
    rw [hrow, ground.getAt_append BPair.unit
      (List.replicate 1 BPair.unit) (idRow n i) j,
      ground.length_replicate BPair.unit 1]
    cases j with
    | zero =>
      rw [if_pos (Nat.succ_pos 0),
        if_neg (fun h : (0 : Nat) = i + 1 => Nat.noConfusion h)]
      exact BPair.oneValue_refl _
    | succ j =>
      rw [if_neg (fun h => Nat.not_succ_le_zero j (Nat.lt_of_succ_lt_succ h)),
        show j + 1 - 1 = j from rfl,
        getAt_idRow n i j (Nat.lt_of_succ_lt_succ hj)]
      by_cases he : j = i
      · rw [he, if_pos rfl, if_pos rfl]
        exact BPair.oneValue_refl _
      · rw [if_neg he, if_neg (fun h => he (Nat.succ.inj h))]
        exact BPair.oneValue_refl _

/-- The one-place identity's determinant reads the one. -/
private theorem detL_idMat1 : (detL (idMat 1)).oneValue (BPair.ofNat 1) := by
  rfl

/-- The identity's determinant reads the one. -/
private theorem detL_idMat : ∀ n : Nat,
    (detL (idMat n)).oneValue (BPair.ofNat 1)
  | 0 => by rfl
  | n + 1 => by
    refine BPair.oneValue_trans (detL_congr_one _ _ (idMat_split n)) ?_
    refine BPair.oneValue_trans
      (detL_blockTri (idMat 1) (nullMat 1 n) (idMat n) 1 n
        (sqAt_idMat 1)
        (length_nullMat 1 n) (rowsLen_nullMat 1 n)
        (sqAt_idMat n)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr detL_idMat1 (detL_idMat n)) ?_
    rfl

/-- The solve witness at the adjugate: the pivot against the
adjugate's own coupling reads the coupling at the determinant's
clearing (`lem:inertia`'s solve `P C ≍ (det P) B`). -/
private theorem pivotSolveAdj (P B : Mat) (k m : Nat) (hk : 0 < k)
    (hP : sqAt P k) (hBl : B.length = k) (hBr : rowsLen m B)
    (hdoff : ¬ (detL P).oneValue BPair.unit) :
    matOneValue (matMul P (matMul (adjM P) B)) (matScaleB (minor P) B) := by
  have hPl : P.length = k := sqAt_len hP
  have hPr : rowsLen k P := rowsLen_of_sqAt hP
  have hAsq : sqAt (adjM P) k := sqAt_adjM P k hk hP
  have hAl : (adjM P).length = k := sqAt_len hAsq
  have hAr : rowsLen k (adjM P) := rowsLen_of_sqAt hAsq
  have hprod := (cleared_adjM P k hk hP hdoff).2.1
  refine matOne_trans (matOne_symm (matMul_assoc (n := k) (k := k) (s := m)
    P (adjM P) B hPr hAr hBr hAl hBl hk hk)) ?_
  refine matOne_trans (matMul_congrL _ _ B hprod) ?_
  refine matOne_trans (matMul_scaleL (minor P) (idMat k) B) ?_
  exact matOne_scaleB (minor P) (idMat_matMul (k := m) k B hBr hBl hk)

/-- The coupling slab of a datum at a leading order: the leading
rows against the trailing places. -/
private def coupB (S : Mat) (k m : Nat) : Mat :=
  (List.range k).map (fun i => (List.range m).map (fun j =>
    ground.getAt BPair.unit (ground.getAt [] S i) (k + j)))

/-- The trailing square of a datum at a leading order. -/
private def tailQ (S : Mat) (k m : Nat) : Mat :=
  (List.range m).map (fun i => (List.range m).map (fun j =>
    ground.getAt BPair.unit (ground.getAt [] S (k + i)) (k + j)))

/-- The coupling slab's row count. -/
private theorem coupB_len (S : Mat) (k m : Nat) : (coupB S k m).length = k :=
  (ground.length_map _ _).trans (ground.length_range k)

/-- The coupling slab's row widths. -/
private theorem coupB_rows (S : Mat) (k m : Nat) : rowsLen m (coupB S k m) :=
  rowsLen_map _ m (List.range k)
    (fun _ _ => (ground.length_map _ _).trans (ground.length_range m))

/-- The coupling slab's entry. -/
private theorem coupB_entry (S : Mat) (k m i j : Nat) (hi : i < k)
    (hj : j < m) :
    ground.getAt BPair.unit (ground.getAt [] (coupB S k m) i) j
      = ground.getAt BPair.unit (ground.getAt [] S i) (k + j) := by
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
    ((List.range k).map (fun i => (List.range m).map (fun j =>
      ground.getAt BPair.unit (ground.getAt [] S i) (k + j)))) i) j = _
  rw [ground.getAt_map (0 : Nat) ([] : List BPair) _ (List.range k) i
      (by rw [ground.length_range]; exact hi),
    ground.getAt_range k i hi,
    ground.getAt_map (0 : Nat) BPair.unit _ (List.range m) j
      (by rw [ground.length_range]; exact hj),
    ground.getAt_range m j hj]

/-- The trailing square's row count. -/
private theorem tailQ_len (S : Mat) (k m : Nat) : (tailQ S k m).length = m :=
  (ground.length_map _ _).trans (ground.length_range m)

/-- The trailing square's row widths. -/
private theorem tailQ_rows (S : Mat) (k m : Nat) : rowsLen m (tailQ S k m) :=
  rowsLen_map _ m (List.range m)
    (fun _ _ => (ground.length_map _ _).trans (ground.length_range m))

/-- The trailing square's entry. -/
private theorem tailQ_entry (S : Mat) (k m i j : Nat) (hi : i < m)
    (hj : j < m) :
    ground.getAt BPair.unit (ground.getAt [] (tailQ S k m) i) j
      = ground.getAt BPair.unit (ground.getAt [] S (k + i)) (k + j) := by
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
    ((List.range m).map (fun i => (List.range m).map (fun j =>
      ground.getAt BPair.unit (ground.getAt [] S (k + i)) (k + j)))) i) j = _
  rw [ground.getAt_map (0 : Nat) ([] : List BPair) _ (List.range m) i
      (by rw [ground.length_range]; exact hi),
    ground.getAt_range m i hi,
    ground.getAt_map (0 : Nat) BPair.unit _ (List.range m) j
      (by rw [ground.length_range]; exact hj),
    ground.getAt_range m j hj]

/-- A datum reads its own assembled join at a leading order: the
pivot square's entries the datum's, the coupling and the trailing
square the datum's selections, the exchanged coupling the datum's
pairing symmetry. -/
private theorem join_extract (S P : Mat) (k m : Nat) (hk : 0 < k)
    (hS : sqAt S (k + m)) (hsym : pairSymAt S (k + m))
    (hPl : P.length = k) (hPr : rowsLen k P)
    (hPe : ∀ i j, i < k → j < k →
      (ground.getAt BPair.unit (ground.getAt [] P i) j).oneValue
        (ground.getAt BPair.unit (ground.getAt [] S i) j)) :
    matOneValue S (blockJoin P (coupB S k m) (tailQ S k m)) := by
  have hSl : S.length = k + m := sqAt_len hS
  have hSr : rowsLen (k + m) S := rowsLen_of_sqAt hS
  have hBl : (coupB S k m).length = k := coupB_len S k m
  have hBr : rowsLen m (coupB S k m) := coupB_rows S k m
  have hQl : (tailQ S k m).length = m := tailQ_len S k m
  have hQr : rowsLen m (tailQ S k m) := tailQ_rows S k m
  have hBt : (transposeM (coupB S k m)).length = m :=
    length_transposeM _ hBr (by rw [hBl]; exact hk)
  have hBtr : rowsLen k (transposeM (coupB S k m)) :=
    rowsLen_cast hBl (rowsLen_transposeM _)
  have hJl : (rowJoin P (coupB S k m)).length = k :=
    ground.length_zipWith (· ++ ·) _ _ k hPl hBl
  refine matOne_of_entries S _ (k + m) hSl hSr
    (length_blockJoin P _ _ k m hPl hBl hBt hQl)
    (rowsLen_blockJoin P _ _ k m hPr hBr hBtr hQr) ?_
  intro i j hi hj
  cases Nat.lt_or_ge i k with
  | inl hik =>
    have hrow : ground.getAt ([] : List BPair)
        (blockJoin P (coupB S k m) (tailQ S k m)) i
        = ground.getAt [] P i ++ ground.getAt [] (coupB S k m) i := by
      show ground.getAt ([] : List BPair)
        (rowJoin P (coupB S k m)
          ++ rowJoin (transposeM (coupB S k m)) (tailQ S k m)) i = _
      rw [ground.getAt_append ([] : List BPair) _ _ i, hJl, if_pos hik]
      exact getAt_rowJoin P _ i (by rw [hPl]; exact hik)
        (by rw [hBl]; exact hik)
    have hPi : (ground.getAt ([] : List BPair) P i).length = k :=
      rowsLen_getAt P i hPr (by rw [hPl]; exact hik)
    rw [hrow]
    cases Nat.lt_or_ge j k with
    | inl hjk =>
      rw [ground.getAt_append BPair.unit _ _ j, hPi, if_pos hjk]
      exact BPair.oneValue_symm (hPe i j hik hjk)
    | inr hjk =>
      match Nat.le.dest hjk with
      | ⟨j', hj'⟩ =>
        subst hj'
        have hj'm : j' < m := Nat.lt_of_add_lt_add_left hj
        have hstep := ground.getAt_append_add BPair.unit
          (ground.getAt ([] : List BPair) P i)
          (ground.getAt [] (coupB S k m) i) j'
        rw [hPi] at hstep
        rw [hstep, coupB_entry S k m i j' hik hj'm]
        exact BPair.oneValue_refl _
  | inr hik =>
    match Nat.le.dest hik with
    | ⟨i', hi'⟩ =>
      subst hi'
      have hi'm : i' < m := Nat.lt_of_add_lt_add_left hi
      have hrow : ground.getAt ([] : List BPair)
          (blockJoin P (coupB S k m) (tailQ S k m)) (k + i')
          = ground.getAt [] (transposeM (coupB S k m)) i'
            ++ ground.getAt [] (tailQ S k m) i' := by
        show ground.getAt ([] : List BPair)
          (rowJoin P (coupB S k m)
            ++ rowJoin (transposeM (coupB S k m)) (tailQ S k m)) (k + i') = _
        have hstep := ground.getAt_append_add ([] : List BPair)
          (rowJoin P (coupB S k m))
          (rowJoin (transposeM (coupB S k m)) (tailQ S k m)) i'
        rw [hJl] at hstep
        rw [hstep]
        exact getAt_rowJoin _ _ i' (by rw [hBt]; exact hi'm)
          (by rw [hQl]; exact hi'm)
      have hTi : (ground.getAt ([] : List BPair)
          (transposeM (coupB S k m)) i').length = k :=
        rowsLen_getAt _ i' hBtr (by rw [hBt]; exact hi'm)
      rw [hrow]
      cases Nat.lt_or_ge j k with
      | inl hjk =>
        rw [ground.getAt_append BPair.unit _ _ j, hTi, if_pos hjk,
          getAt_transposeM BPair.unit (coupB S k m) hBr i' j hi'm
            (by rw [hBl]; exact hjk),
          coupB_entry S k m j i' hjk hi'm]
        exact entrySym S (k + m) (k + i') j hSl hSr hsym hi hj
      | inr hjk =>
        match Nat.le.dest hjk with
        | ⟨j', hj'⟩ =>
          subst hj'
          have hj'm : j' < m := Nat.lt_of_add_lt_add_left hj
          have hstep := ground.getAt_append_add BPair.unit
            (ground.getAt ([] : List BPair) (transposeM (coupB S k m)) i')
            (ground.getAt [] (tailQ S k m) i') j'
          rw [hTi] at hstep
          rw [hstep, tailQ_entry S k m i' j' hi'm hj'm]
          exact BPair.oneValue_refl _

/-- The deflation sits square at the trailing order. -/
theorem sqAt_deflMat (P B Q Cw : Mat) (m : Nat)
    (hBt : (transposeM B).length = m) (hCt : (transposeM Cw).length = m)
    (hQl : Q.length = m) (hQr : rowsLen m Q) :
    sqAt (deflMat P B Q Cw) m := by
  have hMl : (matMul (transposeM B) Cw).length = m :=
    (elim.length_matMul _ Cw).trans hBt
  have hMr : rowsLen m (matMul (transposeM B) Cw) :=
    rowsLen_cast hCt (rowsLen_matMul _ Cw)
  have hXl : (matScaleB (minor P * minor P) Q).length = m :=
    (length_scaleB _ Q).trans hQl
  have hXr : rowsLen m (matScaleB (minor P * minor P) Q) :=
    rowsLen_scaleB _ m Q hQr
  have hYl : (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw))).length
      = m := by
    rw [length_matSwap, length_scaleB, hMl]
  have hYr : rowsLen m
      (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw))) :=
    rowsLen_mapRows BPair.swap _ m (rowsLen_scaleB _ m _ hMr)
  refine sqAt_of ?_ (rowsLen_matAdd m _ _ hXr hYr)
  show (List.zipWith (List.zipWith (fun x y => x + y))
    (matScaleB (minor P * minor P) Q)
    (matSwap (matScaleB (minor P) (matMul (transposeM B) Cw)))).length = m
  exact ground.length_zipWith _ _ _ m hXl hYl

/-- The deflation's pairing is symmetric: the lifted arguments pair
at the assembled datum, whose own pairing exchanges. -/
private theorem defl_pairSym (S P B Q Cw : Mat) (k m : Nat)
    (hsym : pairSymAt S (k + m))
    (hSJ : matOneValue S (blockJoin P B Q))
    (hPr : rowsLen k P) (hPl : P.length = k)
    (hBl : B.length = k) (hBr : rowsLen m B)
    (hBt : (transposeM B).length = m) (hBtr : rowsLen k (transposeM B))
    (hQr : rowsLen m Q) (hQl : Q.length = m)
    (hCl : Cw.length = k) (hCr : rowsLen m Cw)
    (hCt : (transposeM Cw).length = m)
    (hPw : matOneValue (matMul P Cw) (matScaleB (minor P) B)) :
    pairSymAt (deflMat P B Q Cw) m := by
  intro w w' hw hw'
  have hlift : ∀ v : List BPair, v.length = m →
      (matVec Cw v ++ vecScale (minor P).swap v).length = k + m := by
    intro v hv
    rw [ground.length_append, matVec_length, hCl, length_vecScale, hv]
  have hback : ∀ u v : List BPair,
      (dotN u (matVec (blockJoin P B Q) v)).oneValue (dotN u (matVec S v)) :=
    fun u v => dotN_matVec_congrM _ _ u v (matOne_symm hSJ)
  have hfwd : ∀ u v : List BPair,
      (dotN u (matVec S v)).oneValue (dotN u (matVec (blockJoin P B Q) v)) :=
    fun u v => dotN_matVec_congrM _ _ u v hSJ
  refine BPair.oneValue_trans
    (BPair.oneValue_symm
      (quad_liftB P B Q Cw k m w w' hw hw' hPr hPl hBl hBr hBt hBtr hQr hQl
        hCl hCr hCt hPw)) ?_
  refine BPair.oneValue_trans (hback _ _) ?_
  refine BPair.oneValue_trans (hsym _ _ (hlift w hw) (hlift w' hw')) ?_
  refine BPair.oneValue_trans (hfwd _ _) ?_
  exact quad_liftB P B Q Cw k m w' w hw' hw hPr hPl hBl hBr hBt hBtr hQr hQl
    hCl hCr hCt hPw

/-- The step's certificate data at a datum: the column list at the
datum's order, its determinant off equal members, and the pairing
table against the block diagonal. -/
private def VGood (S V D : Mat) (n : Nat) : Prop :=
  sqAt V n ∧ ¬ (detL V).oneValue BPair.unit ∧ gramAt S V D n

/-- A pivot block's own square reads the block's determinant. -/
private theorem minor_blockOne : ∀ blk : SBlock,
    (minor (blockMat [blk] 0)).oneValue blk.det
  | SBlock.one a => BPair.oneValue_refl a
  | SBlock.two a b c => by
    show ((((a * c).norm)
      + ((((b * b).norm).swap + BPair.unit).norm)).norm).oneValue
      ((a * c + (b * b).swap).norm)
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.norm_oneValue _) (BPair.norm_oneValue _)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (ground.swap_congr (BPair.norm_oneValue _))
          (BPair.oneValue_refl BPair.unit))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)) ?_
    exact BPair.oneValue_symm (BPair.norm_oneValue _)

/-- The pivot step closes the certificate: the leading block's own
square with the deflation's certificate beneath it. -/
private theorem step_good (blk : SBlock) (bs : List SBlock) (kn m : Nat)
    (S VD : Mat)
    (hm : widthOf bs kn = m)
    (hS : sqAt S (blk.order + m))
    (hsym : pairSymAt S (blk.order + m))
    (hPe : ∀ i j, i < blk.order → j < blk.order →
      (ground.getAt BPair.unit
          (ground.getAt [] (blockMat [blk] 0) i) j).oneValue
        (ground.getAt BPair.unit (ground.getAt [] S i) j))
    (hdet : ¬ blk.det.oneValue BPair.unit)
    (hIk : (detL (idMat blk.order)).oneValue (BPair.ofNat 1))
    (hrec : VGood (deflMat (blockMat [blk] 0) (coupB S blk.order m)
        (tailQ S blk.order m)
        (matMul (adjM (blockMat [blk] 0)) (coupB S blk.order m)))
      VD (blockMat bs kn) m) :
    VGood S (liftV (matMul (adjM (blockMat [blk] 0)) (coupB S blk.order m))
        (minor (blockMat [blk] 0)) blk.order m VD)
      (blockMat (blk :: bs) kn) (blk.order + m) := by
  have hk : 0 < blk.order := order_pos blk
  have hPsq : sqAt (blockMat [blk] 0) blk.order := sqAt_blockOne blk
  have hPl : (blockMat [blk] 0).length = blk.order := sqAt_len hPsq
  have hPr : rowsLen blk.order (blockMat [blk] 0) := rowsLen_of_sqAt hPsq
  have hdoffm : ¬ (minor (blockMat [blk] 0)).oneValue BPair.unit := fun h =>
    hdet (BPair.oneValue_trans
      (BPair.oneValue_symm (minor_blockOne blk)) h)
  have hdoffL : ¬ (detL (blockMat [blk] 0)).oneValue BPair.unit := fun h =>
    hdoffm (BPair.oneValue_trans
      (minor_detL (blockMat [blk] 0) (rowsLen_cast hPl.symm hPr)) h)
  have hBl : (coupB S blk.order m).length = blk.order :=
    coupB_len S blk.order m
  have hBr : rowsLen m (coupB S blk.order m) := coupB_rows S blk.order m
  have hQl : (tailQ S blk.order m).length = m := tailQ_len S blk.order m
  have hQr : rowsLen m (tailQ S blk.order m) := tailQ_rows S blk.order m
  have hAsq : sqAt (adjM (blockMat [blk] 0)) blk.order :=
    sqAt_adjM (blockMat [blk] 0) blk.order hk hPsq
  have hCl : (matMul (adjM (blockMat [blk] 0)) (coupB S blk.order m)).length
      = blk.order :=
    (elim.length_matMul _ _).trans (sqAt_len hAsq)
  have hBt : (transposeM (coupB S blk.order m)).length = m :=
    length_transposeM _ hBr (by rw [hBl]; exact hk)
  have hCr : rowsLen m (matMul (adjM (blockMat [blk] 0)) (coupB S blk.order m)) :=
    rowsLen_cast hBt (rowsLen_matMul _ _)
  have hSJ := join_extract S (blockMat [blk] 0) blk.order m hk hS hsym
    hPl hPr hPe
  have hPw := pivotSolveAdj (blockMat [blk] 0) (coupB S blk.order m)
    blk.order m hk hPsq hBl hBr hdoffL
  have hVl : VD.length = m := sqAt_len hrec.1
  have hVr : rowsLen m VD := rowsLen_of_sqAt hrec.1
  refine ⟨sqAt_of (liftV_len _ _ _ _ VD hVl) (liftV_rows _ _ _ _ VD hCl hVr),
    detL_liftV _ _ blk.order m VD hk hCl hVl hVr hIk hdoffm hrec.2.1, ?_⟩
  exact gram_step blk bs kn m S (coupB S blk.order m) (tailQ S blk.order m)
    (matMul (adjM (blockMat [blk] 0)) (coupB S blk.order m)) VD
    hm hSJ hBl hBr hQl hQr hCl hCr hVl hVr hPw hrec.2.2

/-- The exchanged datum's entry at the index transposition. -/
private theorem entry_swapRC (S : Mat) (n t i j : Nat) (hS : sqAt S n)
    (ht : t + 1 < n) (hi : i < n) :
    ground.getAt BPair.unit (ground.getAt [] (swapRC t S) i) j
      = ground.getAt BPair.unit
        (ground.getAt [] S (ground.swapIx t (t + 1) i))
        (ground.swapIx t (t + 1) j) := by
  have hSl : S.length = n := sqAt_len hS
  have hSr : rowsLen n S := rowsLen_of_sqAt hS
  have hAl : (ground.adjSwap t S).length = n :=
    (ground.length_adjSwap t S).trans hSl
  have hAr : rowsLen n (ground.adjSwap t S) := elim.rowsLen_adjSwap t S hSr
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
    ((ground.adjSwap t S).map (ground.adjSwap t)) i) j = _
  rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
      (ground.adjSwap t) (ground.adjSwap t S) i (by rw [hAl]; exact hi),
    ground.getAt_adjSwap ([] : List BPair) t S (by rw [hSl]; exact ht) i,
    ground.getAt_adjSwap BPair.unit t
      (ground.getAt ([] : List BPair) S (ground.swapIx t (t + 1) i))
      (by
        rw [rowsLen_getAt S (ground.swapIx t (t + 1) i) hSr
          (by
            rw [hSl]
            exact ground.swapIx_lt (Nat.lt_of_succ_lt ht) ht i hi)]
        exact ht) j]

/-- The exchange walk on the datum. -/
private def swapsS : List Nat → Mat → Mat
  | [], S => S
  | t :: ts, S => swapsS ts (swapRC t S)

/-- The exchange walk on the column list. -/
private def swapsV : List Nat → Mat → Mat
  | [], V => V
  | t :: ts, V => (swapsV ts V).map (ground.adjSwap t)

/-- The exchange walk on the places. -/
private def swapsIx : List Nat → Nat → Nat
  | [], i => i
  | t :: ts, i => ground.swapIx t (t + 1) (swapsIx ts i)

/-- The exchange walk keeps the order. -/
private theorem sqAt_swapsS (n : Nat) : ∀ (ts : List Nat) (S : Mat),
    sqAt S n → sqAt (swapsS ts S) n
  | [], _, h => h
  | t :: ts, S, h => sqAt_swapsS n ts (swapRC t S) (sqAt_swapRC t S n h)

/-- The exchange walk's place stays inside the order. -/
private theorem swapsIx_lt (n : Nat) : ∀ ts : List Nat,
    (∀ t, t ∈ ts → t + 1 < n) → ∀ i, i < n → swapsIx ts i < n
  | [], _, _, hi => hi
  | t :: ts, hb, i, hi =>
    ground.swapIx_lt
      (Nat.lt_of_succ_lt (hb t (List.Mem.head ts)))
      (hb t (List.Mem.head ts)) (swapsIx ts i)
      (swapsIx_lt n ts (fun s hs => hb s (List.Mem.tail t hs)) i hi)

/-- The exchange walk's entry read at the walked places. -/
private theorem entry_swapsS (n : Nat) : ∀ (ts : List Nat) (S : Mat),
    sqAt S n → (∀ t, t ∈ ts → t + 1 < n) → ∀ i j : Nat, i < n →
    ground.getAt BPair.unit (ground.getAt [] (swapsS ts S) i) j
      = ground.getAt BPair.unit
        (ground.getAt [] S (swapsIx ts i)) (swapsIx ts j)
  | [], _, _, _, _, _, _ => rfl
  | t :: ts, S, hS, hb, i, j, hi => by
    have ht : t + 1 < n := hb t (List.Mem.head ts)
    have hbt : ∀ s, s ∈ ts → s + 1 < n :=
      fun s hs => hb s (List.Mem.tail t hs)
    show ground.getAt BPair.unit
      (ground.getAt [] (swapsS ts (swapRC t S)) i) j = _
    rw [entry_swapsS n ts (swapRC t S) (sqAt_swapRC t S n hS) hbt i j hi,
      entry_swapRC S n t (swapsIx ts i) (swapsIx ts j) hS ht
        (swapsIx_lt n ts hbt i hi)]
    exact rfl

/-- The certificate transports across one adjacent exchange. -/
private theorem good_swap (n t : Nat) (S V D : Mat) (hS : sqAt S n)
    (ht : t + 1 < n) (h : VGood (swapRC t S) V D n) :
    VGood S (V.map (ground.adjSwap t)) D n := by
  have hVl : V.length = n := sqAt_len h.1
  have hVr : rowsLen n V := rowsLen_of_sqAt h.1
  have hSl : S.length = n := sqAt_len hS
  have hSr : rowsLen n S := rowsLen_of_sqAt hS
  refine ⟨sqAt_of ((ground.length_map _ V).trans hVl)
    (rowsLen_mapAdj t V hVr), ?_, ?_⟩
  · exact fun hz => swapOff h.2.1
      (BPair.oneValue_trans
        (BPair.oneValue_symm (detL_mapAdj V n t hVl hVr ht)) hz)
  · intro i j hi hj
    rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
        (ground.adjSwap t) V i (by rw [hVl]; exact hi),
      ground.getAt_map ([] : List BPair) ([] : List BPair)
        (ground.adjSwap t) V j (by rw [hVl]; exact hj)]
    refine BPair.oneValue_trans
      (gram_adjSwap t S n hSr hSl _ _
        (rowsLen_getAt V i hVr (by rw [hVl]; exact hi))
        (rowsLen_getAt V j hVr (by rw [hVl]; exact hj))) ?_
    exact h.2.2 i j hi hj

/-- The certificate transports across the exchange walk. -/
private theorem good_swaps (n : Nat) : ∀ (ts : List Nat) (S V D : Mat),
    (∀ t, t ∈ ts → t + 1 < n) → sqAt S n →
    VGood (swapsS ts S) V D n → VGood S (swapsV ts V) D n
  | [], _, _, _, _, _, h => h
  | t :: ts, S, V, D, hb, hS, h => by
    refine good_swap n t S _ D hS (hb t (List.Mem.head ts)) ?_
    exact good_swaps n ts (swapRC t S) V D
      (fun s hs => hb s (List.Mem.tail t hs)) (sqAt_swapRC t S n hS) h

/-- The pairing symmetry survives one adjacent exchange. -/
private theorem pairSym_swapRC (t : Nat) (S : Mat) (n : Nat) (hS : sqAt S n)
    (h : pairSymAt S n) : pairSymAt (swapRC t S) n := by
  have hSl : S.length = n := sqAt_len hS
  have hSr : rowsLen n S := rowsLen_of_sqAt hS
  intro u v hu hv
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (gram_adjSwap t S n hSr hSl u v hu hv)) ?_
  refine BPair.oneValue_trans
    (h _ _ ((ground.length_adjSwap t u).trans hu)
      ((ground.length_adjSwap t v).trans hv)) ?_
  exact gram_adjSwap t S n hSr hSl v u hv hu

/-- The pairing symmetry survives the exchange walk. -/
private theorem pairSym_swapsS (n : Nat) : ∀ (ts : List Nat) (S : Mat),
    sqAt S n → pairSymAt S n → pairSymAt (swapsS ts S) n
  | [], _, _, h => h
  | t :: ts, S, hS, h =>
    pairSym_swapsS n ts (swapRC t S) (sqAt_swapRC t S n hS)
      (pairSym_swapRC t S n hS h)

/-- The first place of a list at which a test holds, the stated
default at a walk that never holds. -/
private def firstSat (P : Nat → Bool) (d : Nat) : List Nat → Nat
  | [] => d
  | i :: t =>
    match P i with
    | true => i
    | false => firstSat P d t

/-- The walk's head step at a holding test. -/
private theorem firstSat_cons_true (P : Nat → Bool) (d i : Nat)
    (t : List Nat) (h : P i = true) : firstSat P d (i :: t) = i := by
  show (match P i with | true => i | false => firstSat P d t) = i
  rw [h]

/-- The walk's head step at a failing test. -/
private theorem firstSat_cons_false (P : Nat → Bool) (d i : Nat)
    (t : List Nat) (h : P i = false) :
    firstSat P d (i :: t) = firstSat P d t := by
  show (match P i with | true => i | false => firstSat P d t)
    = firstSat P d t
  rw [h]

/-- The walk lands at its default or at a listed place passing the
test. -/
private theorem firstSat_res (P : Nat → Bool) (d : Nat) : ∀ l : List Nat,
    firstSat P d l = d ∨ (firstSat P d l ∈ l ∧ P (firstSat P d l) = true)
  | [] => Or.inl rfl
  | i :: t => by
    cases hp : P i with
    | true =>
      rw [firstSat_cons_true P d i t hp]
      exact Or.inr ⟨List.Mem.head t, hp⟩
    | false =>
      rw [firstSat_cons_false P d i t hp]
      cases firstSat_res P d t with
      | inl hd => exact Or.inl hd
      | inr hm => exact Or.inr ⟨List.Mem.tail i hm.1, hm.2⟩

/-- A walk landing at its default fails the test at every listed
place, the default off the list. -/
private theorem firstSat_dflt (P : Nat → Bool) (d : Nat) : ∀ l : List Nat,
    (∀ i, i ∈ l → ¬ i = d) → firstSat P d l = d → ∀ q, q ∈ l → P q = false
  | [], _, _, _, hm => by cases hm
  | i :: t, hne, h, q, hm => by
    cases hp : P i with
    | true =>
      rw [firstSat_cons_true P d i t hp] at h
      exact absurd h (hne i (List.Mem.head t))
    | false =>
      rw [firstSat_cons_false P d i t hp] at h
      cases hm with
      | head => exact hp
      | tail _ ht =>
        exact firstSat_dflt P d t
          (fun s hs => hne s (List.Mem.tail i hs)) h q ht

/-- The leading place with a diagonal entry off equal members, the
order itself at a diagonal of equal members throughout. -/
private def diagOf (S : Mat) (n : Nat) : Nat :=
  firstSat (fun p => !(decide ((ground.getAt BPair.unit
    (ground.getAt [] S p) p).oneValue BPair.unit))) n (List.range n)

/-- The leading place above a stated one carrying an entry off
equal members in the stated row. -/
private def aboveOf (S : Mat) (n p : Nat) : Nat :=
  firstSat (fun q => Nat.blt p q
    && !(decide ((ground.getAt BPair.unit
      (ground.getAt [] S p) q).oneValue BPair.unit))) n (List.range n)

/-- The leading row carrying an entry off equal members above its
own place. -/
private def rowOf (S : Mat) (n : Nat) : Nat :=
  firstSat (fun p => Nat.blt (aboveOf S n p) n) n (List.range n)

/-- The range's members sit off the order. -/
private theorem range_ne (n : Nat) : ∀ i, i ∈ List.range n → ¬ i = n := by
  intro i hi he
  have hlt : i < n := ground.ltOfMemRange hi
  rw [he] at hlt
  exact Nat.lt_irrefl n hlt

/-- The diagonal search's find. -/
private theorem diagOf_some (S : Mat) (n : Nat) (h : diagOf S n < n) :
    ¬ (ground.getAt BPair.unit
      (ground.getAt [] S (diagOf S n)) (diagOf S n)).oneValue BPair.unit := by
  intro hz
  have hr := firstSat_res (fun p => !(decide ((ground.getAt BPair.unit
    (ground.getAt [] S p) p).oneValue BPair.unit))) n (List.range n)
  cases hr with
  | inl hd =>
    have hd' : diagOf S n = n := hd
    rw [hd'] at h
    exact Nat.lt_irrefl n h
  | inr hm =>
    have h2 : (!decide ((ground.getAt BPair.unit
        (ground.getAt [] S (diagOf S n)) (diagOf S n)).oneValue
        BPair.unit)) = true := hm.2
    rw [decide_eq_true hz] at h2
    exact Bool.noConfusion h2

/-- The diagonal search's refusal. -/
private theorem diagOf_none (S : Mat) (n : Nat) (h : ¬ diagOf S n < n)
    (p : Nat) (hp : p < n) :
    (ground.getAt BPair.unit (ground.getAt [] S p) p).oneValue BPair.unit := by
  have hd : diagOf S n = n := by
    cases firstSat_res (fun p => !(decide ((ground.getAt BPair.unit
      (ground.getAt [] S p) p).oneValue BPair.unit))) n (List.range n) with
    | inl hz => exact hz
    | inr hm =>
      exact absurd (ground.ltOfMemRange hm.1) h
  have hf := firstSat_dflt _ n (List.range n) (range_ne n) hd p
    (ground.memRange hp)
  cases hz : decide ((ground.getAt BPair.unit
      (ground.getAt [] S p) p).oneValue BPair.unit) with
  | true => exact of_decide_eq_true hz
  | false => rw [hz] at hf; exact Bool.noConfusion hf

/-- The row search's find above the stated place. -/
private theorem aboveOf_some (S : Mat) (n p : Nat) (h : aboveOf S n p < n) :
    p < aboveOf S n p ∧ ¬ (ground.getAt BPair.unit
      (ground.getAt [] S p) (aboveOf S n p)).oneValue BPair.unit := by
  have hr := firstSat_res (fun q => Nat.blt p q
    && !(decide ((ground.getAt BPair.unit
      (ground.getAt [] S p) q).oneValue BPair.unit))) n (List.range n)
  cases hr with
  | inl hd =>
    have hd' : aboveOf S n p = n := hd
    rw [hd'] at h
    exact absurd h (Nat.lt_irrefl n)
  | inr hm =>
    have h2 : (Nat.blt p (aboveOf S n p)
        && !(decide ((ground.getAt BPair.unit
          (ground.getAt [] S p) (aboveOf S n p)).oneValue BPair.unit)))
        = true := hm.2
    have hb := ground.andSplitB h2
    refine ⟨ground.bltLt hb.1, ?_⟩
    intro hz
    have h3 := hb.2
    rw [decide_eq_true hz] at h3
    exact Bool.noConfusion h3

/-- The row search's refusal. -/
private theorem aboveOf_none (S : Mat) (n p : Nat) (h : ¬ aboveOf S n p < n)
    (q : Nat) (hq : q < n) (hpq : p < q) :
    (ground.getAt BPair.unit (ground.getAt [] S p) q).oneValue BPair.unit := by
  have hd : aboveOf S n p = n := by
    cases firstSat_res (fun q => Nat.blt p q
      && !(decide ((ground.getAt BPair.unit
        (ground.getAt [] S p) q).oneValue BPair.unit))) n (List.range n) with
    | inl hz => exact hz
    | inr hm =>
      exact absurd (ground.ltOfMemRange hm.1) h
  have hf := firstSat_dflt _ n (List.range n) (range_ne n) hd q
    (ground.memRange hq)
  rw [ground.ltBlt hpq] at hf
  cases hz : decide ((ground.getAt BPair.unit
      (ground.getAt [] S p) q).oneValue BPair.unit) with
  | true => exact of_decide_eq_true hz
  | false => rw [hz] at hf; exact Bool.noConfusion hf

/-- The occupied-row search's find. -/
private theorem rowOf_lt (S : Mat) (n : Nat) (h : rowOf S n < n) :
    aboveOf S n (rowOf S n) < n := by
  have hr := firstSat_res (fun p => Nat.blt (aboveOf S n p) n) n
    (List.range n)
  cases hr with
  | inl hd =>
    have hd' : rowOf S n = n := hd
    rw [hd'] at h
    exact absurd h (Nat.lt_irrefl n)
  | inr hm =>
    have h2 : Nat.blt (aboveOf S n (rowOf S n)) n = true := hm.2
    exact ground.bltLt h2

/-- The occupied-row search's refusal. -/
private theorem rowOf_none (S : Mat) (n : Nat) (h : ¬ rowOf S n < n)
    (p : Nat) (hp : p < n) : ¬ aboveOf S n p < n := by
  have hd : rowOf S n = n := by
    cases firstSat_res (fun p => Nat.blt (aboveOf S n p) n) n
      (List.range n) with
    | inl hz => exact hz
    | inr hm =>
      exact absurd (ground.ltOfMemRange hm.1) h
  have hf := firstSat_dflt _ n (List.range n) (range_ne n) hd p
    (ground.memRange hp)
  intro hz
  rw [ground.ltBlt hz] at hf
  exact Bool.noConfusion hf

/-- The join's membership splits. -/
private theorem mem_append_or {α : Type} : ∀ (as bs : List α) (t : α),
    t ∈ as ++ bs → t ∈ as ∨ t ∈ bs
  | [], _, _, hm => Or.inr hm
  | a :: as, bs, t, hm => by
    cases hm with
    | head => exact Or.inl (List.Mem.head as)
    | tail _ ht =>
      cases mem_append_or as bs t ht with
      | inl h => exact Or.inl (List.Mem.tail a h)
      | inr h => exact Or.inr h

/-- The exchange walk bringing a place to the leading position: the
adjacent exchanges descending from the place. -/
private def sinkList : Nat → List Nat
  | 0 => []
  | p + 1 => p :: sinkList p

/-- The descent's exchanges sit below the place. -/
private theorem sinkList_mem : ∀ (p t : Nat), t ∈ sinkList p → t < p
  | 0, _, hm => by cases hm
  | p + 1, t, hm => by
    cases hm with
    | head => exact Nat.lt_succ_self p
    | tail _ ht => exact Nat.lt_succ_of_lt (sinkList_mem p t ht)

/-- The place walk of a joined exchange list. -/
private theorem swapsIx_append : ∀ (as bs : List Nat) (i : Nat),
    swapsIx (as ++ bs) i = swapsIx as (swapsIx bs i)
  | [], _, _ => rfl
  | a :: as, bs, i => by
    show ground.swapIx a (a + 1) (swapsIx (as ++ bs) i)
      = ground.swapIx a (a + 1) (swapsIx as (swapsIx bs i))
    rw [swapsIx_append as bs i]

/-- The descent carries the leading place to its own. -/
private theorem sinkIx_zero : ∀ p : Nat, swapsIx (sinkList p) 0 = p
  | 0 => rfl
  | p + 1 => by
    show ground.swapIx p (p + 1) (swapsIx (sinkList p) 0) = p + 1
    rw [sinkIx_zero p]
    exact ground.swapIx_fst p (p + 1)

/-- The descent fixes the places beyond it. -/
private theorem sinkIx_gt : ∀ (p j : Nat), p < j →
    swapsIx (sinkList p) j = j
  | 0, _, _ => rfl
  | p + 1, j, hj => by
    show ground.swapIx p (p + 1) (swapsIx (sinkList p) j) = j
    rw [sinkIx_gt p j (Nat.lt_of_succ_lt hj)]
    exact ground.swapIx_off
      (fun he => by
        rw [he] at hj
        exact Nat.lt_irrefl p (Nat.lt_of_succ_lt hj))
      (fun he => by
        rw [he] at hj
        exact Nat.lt_irrefl (p + 1) hj)

/-- The descent shifts the places below it down by one. -/
private theorem sinkIx_le : ∀ (p j : Nat), j < p →
    swapsIx (sinkList p) (j + 1) = j
  | 0, j, hj => absurd hj (Nat.not_lt_zero j)
  | p + 1, j, hj => by
    show ground.swapIx p (p + 1) (swapsIx (sinkList p) (j + 1)) = j
    cases Nat.lt_or_ge j p with
    | inl hjp =>
      rw [sinkIx_le p j hjp]
      exact ground.swapIx_off
        (fun he => by
          rw [he] at hjp
          exact Nat.lt_irrefl p hjp)
        (fun he => by
          rw [he] at hjp
          exact Nat.lt_irrefl p (Nat.lt_of_succ_lt hjp))
    | inr hjp =>
      have hje : j = p := Nat.le_antisymm (Nat.le_of_lt_succ hj) hjp
      subst hje
      rw [sinkIx_gt j (j + 1) (Nat.lt_succ_self j)]
      exact ground.swapIx_snd (Nat.succ_ne_self j)

/-- The two-way selection at a decided test. -/
private def pick {α : Type} : Bool → α → α → α
  | true, x, _ => x
  | false, _, y => y

/-- The order-one pivot block read off a permuted datum's leading
entry. -/
private def pivBlk1 (S1 : Mat) : SBlock :=
  SBlock.one (ground.getAt BPair.unit (ground.getAt [] S1 0) 0)

/-- The order-two pivot block read off a permuted datum's leading
square. -/
private def pivBlk2 (S1 : Mat) : SBlock :=
  SBlock.two (ground.getAt BPair.unit (ground.getAt [] S1 0) 0)
    (ground.getAt BPair.unit (ground.getAt [] S1 0) 1)
    (ground.getAt BPair.unit (ground.getAt [] S1 1) 1)

/-- The step's deflation at a permuted datum with the pivot block
leading. -/
private def deflOf (blk : SBlock) (m : Nat) (S1 : Mat) : Mat :=
  deflMat (blockMat [blk] 0) (coupB S1 blk.order m) (tailQ S1 blk.order m)
    (matMul (adjM (blockMat [blk] 0)) (coupB S1 blk.order m))

/-- The step's output: the lifted column list carried back across
the exchange walk, the pivot block ahead of the deflation's. -/
private def stepOut (blk : SBlock) (m : Nat) (S1 : Mat) (ts : List Nat)
    (r : Mat × List SBlock × Nat) : Mat × List SBlock × Nat :=
  (swapsV ts (liftV (matMul (adjM (blockMat [blk] 0)) (coupB S1 blk.order m))
      (minor (blockMat [blk] 0)) blk.order m r.1),
    blk :: r.2.1, r.2.2)

/-- The deflation's order and pairing symmetry at a pivot step. -/
private theorem defl_ok (blk : SBlock) (m : Nat) (S1 : Mat)
    (hS1 : sqAt S1 (blk.order + m)) (hsym1 : pairSymAt S1 (blk.order + m))
    (hPe : ∀ i j, i < blk.order → j < blk.order →
      (ground.getAt BPair.unit
          (ground.getAt [] (blockMat [blk] 0) i) j).oneValue
        (ground.getAt BPair.unit (ground.getAt [] S1 i) j))
    (hdet : ¬ blk.det.oneValue BPair.unit) :
    sqAt (deflOf blk m S1) m ∧ pairSymAt (deflOf blk m S1) m := by
  have hk : 0 < blk.order := order_pos blk
  have hPsq : sqAt (blockMat [blk] 0) blk.order := sqAt_blockOne blk
  have hPl : (blockMat [blk] 0).length = blk.order := sqAt_len hPsq
  have hPr : rowsLen blk.order (blockMat [blk] 0) := rowsLen_of_sqAt hPsq
  have hdoffm : ¬ (minor (blockMat [blk] 0)).oneValue BPair.unit := fun h =>
    hdet (BPair.oneValue_trans (BPair.oneValue_symm (minor_blockOne blk)) h)
  have hdoffL : ¬ (detL (blockMat [blk] 0)).oneValue BPair.unit := fun h =>
    hdoffm (BPair.oneValue_trans
      (minor_detL (blockMat [blk] 0) (rowsLen_cast hPl.symm hPr)) h)
  have hBl : (coupB S1 blk.order m).length = blk.order :=
    coupB_len S1 blk.order m
  have hBr : rowsLen m (coupB S1 blk.order m) := coupB_rows S1 blk.order m
  have hQl : (tailQ S1 blk.order m).length = m := tailQ_len S1 blk.order m
  have hQr : rowsLen m (tailQ S1 blk.order m) := tailQ_rows S1 blk.order m
  have hBt : (transposeM (coupB S1 blk.order m)).length = m :=
    length_transposeM _ hBr (by rw [hBl]; exact hk)
  have hBtr : rowsLen blk.order (transposeM (coupB S1 blk.order m)) :=
    rowsLen_cast hBl (rowsLen_transposeM _)
  have hAsq : sqAt (adjM (blockMat [blk] 0)) blk.order :=
    sqAt_adjM (blockMat [blk] 0) blk.order hk hPsq
  have hCl : (matMul (adjM (blockMat [blk] 0))
      (coupB S1 blk.order m)).length = blk.order :=
    (elim.length_matMul _ _).trans (sqAt_len hAsq)
  have hCr : rowsLen m (matMul (adjM (blockMat [blk] 0))
      (coupB S1 blk.order m)) := rowsLen_cast hBt (rowsLen_matMul _ _)
  have hCt : (transposeM (matMul (adjM (blockMat [blk] 0))
      (coupB S1 blk.order m))).length = m :=
    length_transposeM _ hCr (by rw [hCl]; exact hk)
  have hSJ := join_extract S1 (blockMat [blk] 0) blk.order m hk hS1 hsym1
    hPl hPr hPe
  have hPw := pivotSolveAdj (blockMat [blk] 0) (coupB S1 blk.order m)
    blk.order m hk hPsq hBl hBr hdoffL
  exact ⟨sqAt_deflMat _ _ _ _ m hBt hCt hQl hQr,
    defl_pairSym S1 (blockMat [blk] 0) (coupB S1 blk.order m)
      (tailQ S1 blk.order m)
      (matMul (adjM (blockMat [blk] 0)) (coupB S1 blk.order m))
      blk.order m hsym1 hSJ hPr hPl hBl hBr hBt hBtr hQr hQl hCl hCr hCt hPw⟩

/-- The pivot step's whole read: the block widths tie, the blocks'
determinants stay off equal members, and the certificate closes at
the datum before the exchange walk. -/
private theorem branch_read (blk : SBlock) (bs : List SBlock) (kn m n : Nat)
    (S VD : Mat) (ts : List Nat)
    (hn : blk.order + m = n)
    (hts : ∀ t, t ∈ ts → t + 1 < n)
    (hS : sqAt S n) (hsym : pairSymAt S n)
    (hPe : ∀ i j, i < blk.order → j < blk.order →
      (ground.getAt BPair.unit
          (ground.getAt [] (blockMat [blk] 0) i) j).oneValue
        (ground.getAt BPair.unit (ground.getAt [] (swapsS ts S) i) j))
    (hdet : ¬ blk.det.oneValue BPair.unit)
    (hIk : (detL (idMat blk.order)).oneValue (BPair.ofNat 1))
    (hw : widthOf bs kn = m)
    (hall : (bs.all (fun b => !(decide (b.det.oneValue BPair.unit)))) = true)
    (hrec : VGood (deflOf blk m (swapsS ts S)) VD (blockMat bs kn) m) :
    widthOf (blk :: bs) kn = n
      ∧ (((blk :: bs).all
          (fun b => !(decide (b.det.oneValue BPair.unit)))) = true)
      ∧ VGood S (swapsV ts (liftV (matMul (adjM (blockMat [blk] 0))
          (coupB (swapsS ts S) blk.order m))
          (minor (blockMat [blk] 0)) blk.order m VD))
        (blockMat (blk :: bs) kn) n := by
  subst hn
  have hS1 : sqAt (swapsS ts S) (blk.order + m) := sqAt_swapsS _ ts S hS
  have hsym1 : pairSymAt (swapsS ts S) (blk.order + m) :=
    pairSym_swapsS _ ts S hS hsym
  refine ⟨?_, ?_, ?_⟩
  · show widthOf bs (kn + blk.order) = blk.order + m
    rw [widthOf_shift bs kn blk.order, hw, Nat.add_comm m blk.order]
  · show (!(decide (blk.det.oneValue BPair.unit))
      && bs.all (fun b => !(decide (b.det.oneValue BPair.unit)))) = true
    rw [decide_eq_false hdet, hall]
    rfl
  · refine good_swaps (blk.order + m) ts S _ _ hts hS ?_
    exact step_good blk bs kn m (swapsS ts S) VD hw hS1 hsym1 hPe hdet hIk hrec

/-- The kernel block's entries read the sum's unit. -/
private theorem blockMat_nil_entry (k i j : Nat) (hi : i < k) :
    ground.getAt BPair.unit (ground.getAt [] (blockMat [] k) i) j
      = BPair.unit := by
  show ground.getAt BPair.unit (ground.getAt ([] : List BPair)
    ((List.range k).map (fun _ => List.replicate k BPair.unit)) i) j
    = BPair.unit
  rw [ground.getAt_map (0 : Nat) ([] : List BPair)
    (fun _ => List.replicate k BPair.unit) (List.range k) i
    (by rw [ground.length_range]; exact hi)]
  exact getAt_repl_unit k j

/-- The exchange walk bringing the diagonal pivot's place to the
front. -/
private def tsDiag (S : Mat) (n : Nat) : List Nat := sinkList (diagOf S n)

/-- The exchange walk bringing an off-diagonal pivot's two places to
the front, the further place descending first. -/
private def tsPair (S : Mat) (n : Nat) : List Nat :=
  sinkList (aboveOf S n (rowOf S n)) ++ sinkList (rowOf S n + 1)

/-- `lem:inertia`'s descent: the leftmost admissible pivot brought
to the front by the exchange walk, the deflation beneath it, and
the vacant datum's own identity at the kernel block. -/
private def mkVGo : Nat → Nat → Mat → Mat × List SBlock × Nat
  | _, 0, _ => ([], [], 0)
  | 0, n + 1, _ => (idMat (n + 1), [], n + 1)
  | f + 1, n + 1, S =>
    pick (Nat.blt (diagOf S (n + 1)) (n + 1))
      (stepOut (pivBlk1 (swapsS (tsDiag S (n + 1)) S)) n
        (swapsS (tsDiag S (n + 1)) S) (tsDiag S (n + 1))
        (mkVGo f n (deflOf (pivBlk1 (swapsS (tsDiag S (n + 1)) S)) n
          (swapsS (tsDiag S (n + 1)) S))))
      (pick (Nat.blt (rowOf S (n + 1)) (n + 1))
        (stepOut (pivBlk2 (swapsS (tsPair S (n + 1)) S)) (n - 1)
          (swapsS (tsPair S (n + 1)) S) (tsPair S (n + 1))
          (mkVGo f (n - 1)
            (deflOf (pivBlk2 (swapsS (tsPair S (n + 1)) S)) (n - 1)
              (swapsS (tsPair S (n + 1)) S))))
        (idMat (n + 1), [], n + 1))

/-- The descent at the vacant order. -/
private theorem mkVGo_zero (f : Nat) (S : Mat) :
    mkVGo f 0 S = ([], [], 0) := by
  cases f with
  | zero => rfl
  | succ _ => rfl

/-- The descent's step at an occupied order. -/
private theorem mkVGo_succ (f n : Nat) (S : Mat) :
    mkVGo (f + 1) (n + 1) S
      = pick (Nat.blt (diagOf S (n + 1)) (n + 1))
          (stepOut (pivBlk1 (swapsS (tsDiag S (n + 1)) S)) n
            (swapsS (tsDiag S (n + 1)) S) (tsDiag S (n + 1))
            (mkVGo f n (deflOf (pivBlk1 (swapsS (tsDiag S (n + 1)) S)) n
              (swapsS (tsDiag S (n + 1)) S))))
          (pick (Nat.blt (rowOf S (n + 1)) (n + 1))
            (stepOut (pivBlk2 (swapsS (tsPair S (n + 1)) S)) (n - 1)
              (swapsS (tsPair S (n + 1)) S) (tsPair S (n + 1))
              (mkVGo f (n - 1)
                (deflOf (pivBlk2 (swapsS (tsPair S (n + 1)) S)) (n - 1)
                  (swapsS (tsPair S (n + 1)) S))))
            (idMat (n + 1), [], n + 1)) := rfl

/-- The selection's two reads. -/
private theorem pick_true {α : Type} (x y : α) : pick true x y = x := rfl

private theorem pick_false {α : Type} (x y : α) : pick false x y = y := rfl

/-- The vacant datum's certificate: the identity at the whole
order, the kernel block the descent's remainder. -/
private theorem kern_read (S : Mat) (n : Nat) (hS : sqAt S n)
    (hu : ∀ i j, i < n → j < n →
      (ground.getAt BPair.unit (ground.getAt [] S i) j).oneValue
        BPair.unit) :
    VGood S (idMat n) (blockMat [] n) n := by
  have hSl : S.length = n := sqAt_len hS
  have hSr : rowsLen n S := rowsLen_of_sqAt hS
  refine ⟨sqAt_idMat n, ?_, ?_⟩
  · intro hz
    exact BPair.ofNat_one_off
      (BPair.oneValue_trans (BPair.oneValue_symm (detL_idMat n)) hz)
  · intro i j hi hj
    rw [idMat_row n i hi, idMat_row n j hj, blockMat_nil_entry n i j hi]
    exact BPair.oneValue_trans (entry_pair S n i j hSl hSr hi hj) (hu i j hi hj)

/-- An order-two block at an equal-membered leading entry and an
off-unit coupling has a determinant off equal members. -/
private theorem two_det_off {a b c : BPair} (ha : a.oneValue BPair.unit)
    (hb : ¬ b.oneValue BPair.unit) :
    ¬ (SBlock.two a b c).det.oneValue BPair.unit := by
  have hdd : ((a * c + (b * b).swap).norm).oneValue ((b * b).swap) := by
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (elim.oneValue_unit_mul ha)
        (BPair.oneValue_refl _)) ?_
    exact BPair.unit_add _
  intro hz
  exact swapOff (ground.mulOffUnit hb hb)
    (BPair.oneValue_trans (BPair.oneValue_symm hdd) hz)

/-- The order-one pivot block's square is the datum's leading
entry. -/
private theorem one_hPe (S1 : Mat) : ∀ i j,
    i < (pivBlk1 S1).order → j < (pivBlk1 S1).order →
    (ground.getAt BPair.unit
        (ground.getAt [] (blockMat [pivBlk1 S1] 0) i) j).oneValue
      (ground.getAt BPair.unit (ground.getAt [] S1 i) j) := by
  intro i j hi hj
  have hi' : i < 1 := hi
  have hj' : j < 1 := hj
  cases i with
  | succ i => exact absurd (Nat.lt_of_succ_lt_succ hi') (Nat.not_lt_zero i)
  | zero =>
    cases j with
    | succ j => exact absurd (Nat.lt_of_succ_lt_succ hj') (Nat.not_lt_zero j)
    | zero => exact BPair.oneValue_refl _

/-- The order-two pivot block's square is the datum's leading
square, the exchanged entry the datum's own pairing symmetry. -/
private theorem two_hPe (S1 : Mat) (n : Nat) (hS1l : S1.length = n)
    (hS1r : rowsLen n S1) (hsym1 : pairSymAt S1 n) (h1 : 1 < n) : ∀ i j,
    i < (pivBlk2 S1).order → j < (pivBlk2 S1).order →
    (ground.getAt BPair.unit
        (ground.getAt [] (blockMat [pivBlk2 S1] 0) i) j).oneValue
      (ground.getAt BPair.unit (ground.getAt [] S1 i) j) := by
  intro i j hi hj
  have hi' : i < 2 := hi
  have hj' : j < 2 := hj
  cases i with
  | zero =>
    cases j with
    | zero => exact BPair.oneValue_refl _
    | succ j =>
      cases j with
      | zero => exact BPair.oneValue_refl _
      | succ j =>
        exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj'))
          (Nat.not_lt_zero j)
  | succ i =>
    cases i with
    | zero =>
      cases j with
      | zero =>
        exact entrySym S1 n 0 1 hS1l hS1r hsym1
          (Nat.lt_of_succ_lt h1) h1
      | succ j =>
        cases j with
        | zero => exact BPair.oneValue_refl _
        | succ j =>
          exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hj'))
            (Nat.not_lt_zero j)
    | succ i =>
      exact absurd (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi'))
        (Nat.not_lt_zero i)

/-- The descent's read: the block widths tie at the datum's order,
every block's determinant sits off equal members, and the column
list is the datum's certificate. -/
private theorem mkVGo_read : ∀ (f n : Nat) (S : Mat), n ≤ f → sqAt S n →
    pairSymAt S n →
    widthOf (mkVGo f n S).2.1 (mkVGo f n S).2.2 = n
      ∧ (((mkVGo f n S).2.1.all
          (fun b => !(decide (b.det.oneValue BPair.unit)))) = true)
      ∧ VGood S (mkVGo f n S).1
          (blockMat (mkVGo f n S).2.1 (mkVGo f n S).2.2) n
  | f, 0, S, _, _, _ => by
    rw [mkVGo_zero f S]
    exact ⟨rfl, rfl, rfl,
      (fun hz => BPair.ofNat_one_off
        (BPair.oneValue_trans (BPair.oneValue_symm (detL_idMat 0)) hz)),
      (fun i _ hi _ => absurd hi (Nat.not_lt_zero i))⟩
  | 0, n + 1, _, hf, _, _ => absurd hf (Nat.not_succ_le_zero n)
  | f + 1, n + 1, S, hf, hS, hsym => by
    have hfn : n ≤ f := Nat.le_of_succ_le_succ hf
    have hSl : S.length = n + 1 := sqAt_len hS
    have hSr : rowsLen (n + 1) S := rowsLen_of_sqAt hS
    rw [mkVGo_succ f n S]
    cases hb : Nat.blt (diagOf S (n + 1)) (n + 1) with
    | true =>
      rw [pick_true]
      have hp : diagOf S (n + 1) < n + 1 := ground.bltLt hb
      have hts : ∀ t, t ∈ tsDiag S (n + 1) → t + 1 < n + 1 := by
        intro t ht
        exact Nat.lt_of_le_of_lt (sinkList_mem (diagOf S (n + 1)) t ht) hp
      have hS1 : sqAt (swapsS (tsDiag S (n + 1)) S) (n + 1) :=
        sqAt_swapsS (n + 1) _ S hS
      have hsym1 : pairSymAt (swapsS (tsDiag S (n + 1)) S) (n + 1) :=
        pairSym_swapsS (n + 1) _ S hS hsym
      have hentry : ground.getAt BPair.unit
          (ground.getAt [] (swapsS (tsDiag S (n + 1)) S) 0) 0
          = ground.getAt BPair.unit
            (ground.getAt [] S (diagOf S (n + 1))) (diagOf S (n + 1)) := by
        have he := entry_swapsS (n + 1) (tsDiag S (n + 1)) S hS hts 0 0
          (Nat.succ_pos n)
        rw [he]
        have hz : swapsIx (tsDiag S (n + 1)) 0 = diagOf S (n + 1) :=
          sinkIx_zero (diagOf S (n + 1))
        rw [hz]
      have hdet : ¬ (pivBlk1 (swapsS (tsDiag S (n + 1)) S)).det.oneValue
          BPair.unit := by
        have hd0 : (pivBlk1 (swapsS (tsDiag S (n + 1)) S)).det
            = ground.getAt BPair.unit
              (ground.getAt [] (swapsS (tsDiag S (n + 1)) S) 0) 0 := rfl
        rw [hd0, hentry]
        exact diagOf_some S (n + 1) hp
      have hn1 : (pivBlk1 (swapsS (tsDiag S (n + 1)) S)).order + n = n + 1 :=
        Nat.add_comm 1 n
      have hdok := defl_ok (pivBlk1 (swapsS (tsDiag S (n + 1)) S)) n
        (swapsS (tsDiag S (n + 1)) S) (by rw [hn1]; exact hS1)
        (by rw [hn1]; exact hsym1)
        (one_hPe (swapsS (tsDiag S (n + 1)) S)) hdet
      have hIH := mkVGo_read f n
        (deflOf (pivBlk1 (swapsS (tsDiag S (n + 1)) S)) n
          (swapsS (tsDiag S (n + 1)) S)) hfn hdok.1 hdok.2
      exact branch_read (pivBlk1 (swapsS (tsDiag S (n + 1)) S)) _ _ n (n + 1)
        S _ (tsDiag S (n + 1)) hn1 hts hS hsym
        (one_hPe (swapsS (tsDiag S (n + 1)) S)) hdet detL_idMat1
        hIH.1 hIH.2.1 hIH.2.2
    | false =>
      rw [pick_false]
      have hbd : ¬ diagOf S (n + 1) < n + 1 := ground.bltFalse hb
      cases hb2 : Nat.blt (rowOf S (n + 1)) (n + 1) with
      | true =>
        rw [pick_true]
        have hp : rowOf S (n + 1) < n + 1 := ground.bltLt hb2
        have hq : aboveOf S (n + 1) (rowOf S (n + 1)) < n + 1 :=
          rowOf_lt S (n + 1) hp
        have hab := aboveOf_some S (n + 1) (rowOf S (n + 1)) hq
        have hq1 : 0 < aboveOf S (n + 1) (rowOf S (n + 1)) :=
          Nat.lt_of_le_of_lt (Nat.zero_le _) hab.1
        have hnpos : 0 < n :=
          Nat.lt_of_lt_of_le hq1 (Nat.le_of_lt_succ hq)
        have h1n : 1 < n + 1 := Nat.succ_lt_succ hnpos
        have hpred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hnpos
        have hts : ∀ t, t ∈ tsPair S (n + 1) → t + 1 < n + 1 := by
          intro t ht
          cases mem_append_or _ _ t ht with
          | inl h =>
            exact Nat.lt_of_le_of_lt (sinkList_mem _ t h) hq
          | inr h =>
            exact Nat.lt_of_le_of_lt
              (Nat.le_trans (sinkList_mem _ t h) hab.1) hq
        have hS1 : sqAt (swapsS (tsPair S (n + 1)) S) (n + 1) :=
          sqAt_swapsS (n + 1) _ S hS
        have hsym1 : pairSymAt (swapsS (tsPair S (n + 1)) S) (n + 1) :=
          pairSym_swapsS (n + 1) _ S hS hsym
        have hS1l : (swapsS (tsPair S (n + 1)) S).length = n + 1 :=
          sqAt_len hS1
        have hS1r : rowsLen (n + 1) (swapsS (tsPair S (n + 1)) S) :=
          rowsLen_of_sqAt hS1
        have hix0 : swapsIx (tsPair S (n + 1)) 0 = rowOf S (n + 1) := by
          show swapsIx (sinkList (aboveOf S (n + 1) (rowOf S (n + 1)))
            ++ sinkList (rowOf S (n + 1) + 1)) 0 = rowOf S (n + 1)
          rw [swapsIx_append, sinkIx_zero (rowOf S (n + 1) + 1),
            sinkIx_le (aboveOf S (n + 1) (rowOf S (n + 1)))
              (rowOf S (n + 1)) hab.1]
        have h01 : swapsIx (sinkList (rowOf S (n + 1) + 1)) 1 = 0 :=
          sinkIx_le (rowOf S (n + 1) + 1) 0 (Nat.succ_pos _)
        have hix1 : swapsIx (tsPair S (n + 1)) 1
            = aboveOf S (n + 1) (rowOf S (n + 1)) := by
          show swapsIx (sinkList (aboveOf S (n + 1) (rowOf S (n + 1)))
            ++ sinkList (rowOf S (n + 1) + 1)) 1 = _
          rw [swapsIx_append, h01,
            sinkIx_zero (aboveOf S (n + 1) (rowOf S (n + 1)))]
        have hE00 : ground.getAt BPair.unit
            (ground.getAt [] (swapsS (tsPair S (n + 1)) S) 0) 0
            = ground.getAt BPair.unit
              (ground.getAt [] S (rowOf S (n + 1))) (rowOf S (n + 1)) := by
          rw [entry_swapsS (n + 1) (tsPair S (n + 1)) S hS hts 0 0
            (Nat.succ_pos n), hix0]
        have hE01 : ground.getAt BPair.unit
            (ground.getAt [] (swapsS (tsPair S (n + 1)) S) 0) 1
            = ground.getAt BPair.unit
              (ground.getAt [] S (rowOf S (n + 1)))
              (aboveOf S (n + 1) (rowOf S (n + 1))) := by
          rw [entry_swapsS (n + 1) (tsPair S (n + 1)) S hS hts 0 1
            (Nat.succ_pos n), hix0, hix1]
        have ha0 : (ground.getAt BPair.unit
            (ground.getAt [] (swapsS (tsPair S (n + 1)) S) 0) 0).oneValue
            BPair.unit := by
          rw [hE00]
          exact diagOf_none S (n + 1) hbd (rowOf S (n + 1)) hp
        have hb0 : ¬ (ground.getAt BPair.unit
            (ground.getAt [] (swapsS (tsPair S (n + 1)) S) 0) 1).oneValue
            BPair.unit := by
          rw [hE01]
          exact hab.2
        have hdet : ¬ (pivBlk2 (swapsS (tsPair S (n + 1)) S)).det.oneValue
            BPair.unit := two_det_off ha0 hb0
        have hn2 : (pivBlk2 (swapsS (tsPair S (n + 1)) S)).order + (n - 1)
            = n + 1 := by
          show 2 + (n - 1) = n + 1
          rw [Nat.add_comm 2 (n - 1)]
          show n - 1 + 1 + 1 = n + 1
          rw [hpred]
        have hPe := two_hPe (swapsS (tsPair S (n + 1)) S) (n + 1) hS1l hS1r
          hsym1 h1n
        have hdok := defl_ok (pivBlk2 (swapsS (tsPair S (n + 1)) S)) (n - 1)
          (swapsS (tsPair S (n + 1)) S) (by rw [hn2]; exact hS1)
          (by rw [hn2]; exact hsym1) hPe hdet
        have hIH := mkVGo_read f (n - 1)
          (deflOf (pivBlk2 (swapsS (tsPair S (n + 1)) S)) (n - 1)
            (swapsS (tsPair S (n + 1)) S))
          (Nat.le_trans (Nat.sub_le n 1) hfn) hdok.1 hdok.2
        exact branch_read (pivBlk2 (swapsS (tsPair S (n + 1)) S)) _ _ (n - 1)
          (n + 1) S _ (tsPair S (n + 1)) hn2 hts hS hsym hPe hdet
          (by rfl) hIH.1 hIH.2.1 hIH.2.2
      | false =>
        rw [pick_false]
        have hbr : ¬ rowOf S (n + 1) < n + 1 := ground.bltFalse hb2
        have hu : ∀ i j, i < n + 1 → j < n + 1 →
            (ground.getAt BPair.unit (ground.getAt [] S i) j).oneValue
              BPair.unit := by
          intro i j hi hj
          cases Nat.lt_or_ge i j with
          | inl hij =>
            exact aboveOf_none S (n + 1) i
              (rowOf_none S (n + 1) hbr i hi) j hj hij
          | inr hij =>
            cases Nat.lt_or_ge j i with
            | inl hji =>
              refine BPair.oneValue_trans
                (entrySym S (n + 1) i j hSl hSr hsym hi hj) ?_
              exact aboveOf_none S (n + 1) j
                (rowOf_none S (n + 1) hbr j hj) i hi hji
            | inr hji =>
              have he : i = j := Nat.le_antisymm hji hij
              rw [he]
              exact diagOf_none S (n + 1) hbd j hj
        exact ⟨rfl, rfl, kern_read S (n + 1) hS hu⟩


/-! The cap algebra (`thm:groundreads`(iii)'s instantiation): the
two-sided cap respells across an entrywise read of its two data,
rescales at a positive weight with its two splits scaled, adds
summand by summand at the sum's own two splits, and pads to a
joined order at the trailing block, the leading block vacant. -/

/-- The summed cap's upper difference datum: the sum's site datum
against the first summand's own is the second summand's, the first
summand's two balanced copies beside it. -/
private theorem addSiteU (A B C D : Mat) :
    siteDatum (siteDatum (matAdd A C) (matAdd B D)) (siteDatum A B)
      = matAdd (siteDatum C D)
          (matAdd (matAdd A (matSwap A)) (matAdd (matSwap B) B)) := by
  show matAdd (matAdd (matAdd A C) (matSwap (matAdd B D)))
      (matSwap (matAdd A (matSwap B)))
    = matAdd (matAdd C (matSwap D))
        (matAdd (matAdd A (matSwap A)) (matAdd (matSwap B) B))
  rw [elim.matSwap_matAdd B D, elim.matSwap_matAdd A (matSwap B),
    elim.matSwap_matSwap B,
    elim.matAdd_shuffle (matAdd A C) (matAdd (matSwap B) (matSwap D))
      (matSwap A) B,
    elim.matAdd_right_comm A C (matSwap A),
    elim.matAdd_right_comm (matSwap B) (matSwap D) B,
    elim.matAdd_shuffle (matAdd A (matSwap A)) C
      (matAdd (matSwap B) B) (matSwap D),
    elim.matAdd_comm
      (matAdd (matAdd A (matSwap A)) (matAdd (matSwap B) B))
      (matAdd C (matSwap D))]

/-- The summed cap's lower difference datum: the sum's site datum
against the first summand's own sum is the second summand's, the
first summand's two balanced copies beside it. -/
private theorem addSumL (A B C D : Mat) :
    siteDatum (matAdd (matAdd A C) (matAdd B D)) (matAdd A B)
      = matAdd (matAdd C D)
          (matAdd (matAdd A (matSwap A)) (matAdd B (matSwap B))) := by
  show matAdd (matAdd (matAdd A C) (matAdd B D))
      (matSwap (matAdd A B))
    = matAdd (matAdd C D)
        (matAdd (matAdd A (matSwap A)) (matAdd B (matSwap B)))
  rw [elim.matSwap_matAdd A B,
    elim.matAdd_shuffle (matAdd A C) (matAdd B D) (matSwap A) (matSwap B),
    elim.matAdd_right_comm A C (matSwap A),
    elim.matAdd_right_comm B D (matSwap B),
    elim.matAdd_shuffle (matAdd A (matSwap A)) C
      (matAdd B (matSwap B)) D,
    elim.matAdd_comm
      (matAdd (matAdd A (matSwap A)) (matAdd B (matSwap B)))
      (matAdd C D)]

/-- The two-sided cap transports across an entrywise read of its
two data: the site datum and the sum respell entry by entry, so the
two split reads travel by `splitRead_congr` at the two splits
themselves, their reversal counts untouched. -/
theorem capAt_congr {n : Nat} (S C S' C' : Mat) (spU spL : Split n)
    (h : capAt S C spU spL)
    (hS : sqAt S' n) (hC : sqAt C' n)
    (heS : matOneValue S S') (heC : matOneValue C C') :
    capAt S' C' spU spL := by
  obtain ⟨hSq, hCq, ⟨hU, hpU⟩, hL, hpL⟩ := h
  have hrS : rowsLen n S := rowsLen_of_sqAt hSq
  have hrC : rowsLen n C := rowsLen_of_sqAt hCq
  have hrS' : rowsLen n S' := rowsLen_of_sqAt hS
  have hrC' : rowsLen n C' := rowsLen_of_sqAt hC
  refine ⟨hS, hC, ⟨?_, hpU⟩, ?_, hpL⟩
  · refine splitRead_congr (siteDatum C S) (siteDatum C' S')
      (sqAt_siteDatum n C' S' hC hS) ?_ spU hU
    exact elim.matAdd_cong2 n C (matSwap S) C' (matSwap S') hrC
      (rowsLen_mapRows BPair.swap S n hrS) hrC'
      (rowsLen_mapRows BPair.swap S' n hrS') heC (elim.matSwap_congr heS)
  · refine splitRead_congr (matAdd C S) (matAdd C' S')
      (elim.sqAt_matAdd n C' S' hC hS) ?_ spL hL
    exact elim.matAdd_cong2 n C S C' S' hrC hrS hrC' hrS' heC heS

/-- The two-sided cap at a positive rescaling: both data scale and
both splits scale with them — the scaled split reads the scaled
datum and its reversal count is the split's own, so the cap holds
at the weight `q` throughout. -/
theorem capAt_scale {n : Nat} (S C : Mat) (q : Pos) (spU spL : Split n)
    (h : capAt S C spU spL) :
    capAt (matScale q S) (matScale q C)
      (scaleSplit (BPair.ofPos q) spU) (scaleSplit (BPair.ofPos q) spL) := by
  obtain ⟨hSq, hCq, ⟨hU, hpU⟩, hL, hpL⟩ := h
  have hw : BPair.unit < BPair.ofPos q := ground.unitLtOfPos q
  have hoff : ¬ (BPair.ofPos q).oneValue BPair.unit := ground.offOfUnitLt hw
  have hSs : sqAt (matScale q S) n := sqAt_matScale n q S hSq
  have hCs : sqAt (matScale q C) n := sqAt_matScale n q C hCq
  have heU : matScale q (siteDatum C S)
      = siteDatum (matScale q C) (matScale q S) := by
    show matScale q (matAdd C (matSwap S))
      = matAdd (matScale q C) (matSwap (matScale q S))
    rw [matScale_matAdd q C (matSwap S), matScale_matSwap q S]
  have hcU : matOneValue (matScaleB (BPair.ofPos q) (siteDatum C S))
      (siteDatum (matScale q C) (matScale q S)) := by
    have hb := elim.matOne_symm (matScale_scaleB q (siteDatum C S))
    rw [heU] at hb
    exact hb
  have hcL : matOneValue (matScaleB (BPair.ofPos q) (matAdd C S))
      (matAdd (matScale q C) (matScale q S)) := by
    have hb := elim.matOne_symm (matScale_scaleB q (matAdd C S))
    rw [matScale_matAdd q C S] at hb
    exact hb
  refine ⟨hSs, hCs, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact splitRead_congr _ _ (sqAt_siteDatum n _ _ hCs hSs) hcU _
      (scaleSplit_read (BPair.ofPos q) hoff (siteDatum C S) spU hU)
  · show revAt (scaleSplit (BPair.ofPos q) spU) = 0
    rw [scaleSplit_rev (BPair.ofPos q) hw spU]
    exact hpU
  · exact splitRead_congr _ _ (elim.sqAt_matAdd n _ _ hCs hSs) hcL _
      (scaleSplit_read (BPair.ofPos q) hoff (matAdd C S) spL hL)
  · show revAt (scaleSplit (BPair.ofPos q) spL) = 0
    rw [scaleSplit_rev (BPair.ofPos q) hw spL]
    exact hpL

/-- The two summands' caps join at the sum: the sum's site datum
against the first summand's own reads the second summand's, so the
monotone read prices the sum's reversal count at or below the first
summand's, which sits at the sum's unit — the two splits of the sum
the theorem's own data. -/
theorem capAt_add {n : Nat} (S1 C1 S2 C2 : Mat)
    (spU1 spL1 spU2 spL2 spU spL : Split n)
    (h1 : capAt S1 C1 spU1 spL1) (h2 : capAt S2 C2 spU2 spL2)
    (hU : splitRead (siteDatum (matAdd C1 C2) (matAdd S1 S2)) spU)
    (hL : splitRead (matAdd (matAdd C1 C2) (matAdd S1 S2)) spL) :
    capAt (matAdd S1 S2) (matAdd C1 C2) spU spL := by
  obtain ⟨hS1, hC1, ⟨hU1, hpU1⟩, hL1, hpL1⟩ := h1
  obtain ⟨hS2, hC2, ⟨hU2, hpU2⟩, hL2, hpL2⟩ := h2
  have hZC : sqAt (matAdd C1 (matSwap C1)) n :=
    elim.sqAt_matAdd n C1 (matSwap C1) hC1 (elim.sqAt_matSwap n C1 hC1)
  have hZSu : sqAt (matAdd (matSwap S1) S1) n :=
    elim.sqAt_matAdd n (matSwap S1) S1 (elim.sqAt_matSwap n S1 hS1) hS1
  have hZSl : sqAt (matAdd S1 (matSwap S1)) n :=
    elim.sqAt_matAdd n S1 (matSwap S1) hS1 (elim.sqAt_matSwap n S1 hS1)
  have hdU : matOneValue
      (siteDatum (siteDatum (matAdd C1 C2) (matAdd S1 S2))
        (siteDatum C1 S1)) (siteDatum C2 S2) := by
    rw [addSiteU C1 S1 C2 S2]
    exact elim.matAdd_nullR (siteDatum C2 S2) _
      (sqAt_siteDatum n C2 S2 hC2 hS2)
      (elim.sqAt_matAdd n _ _ hZC hZSu)
      (elim.matNull_matAdd (elim.matNull_add_swap C1)
        (elim.matNull_swap_add (elim.matOne_refl S1)))
  have hdL : matOneValue
      (siteDatum (matAdd (matAdd C1 C2) (matAdd S1 S2))
        (matAdd C1 S1)) (matAdd C2 S2) := by
    rw [addSumL C1 S1 C2 S2]
    exact elim.matAdd_nullR (matAdd C2 S2) _
      (elim.sqAt_matAdd n C2 S2 hC2 hS2)
      (elim.sqAt_matAdd n _ _ hZC hZSl)
      (elim.matNull_matAdd (elim.matNull_add_swap C1)
        (elim.matNull_add_swap S1))
  have hddU : splitRead
      (siteDatum (siteDatum (matAdd C1 C2) (matAdd S1 S2))
        (siteDatum C1 S1)) spU2 :=
    splitRead_congr (siteDatum C2 S2) _
      (sqAt_siteDatum n _ _ hU.1 hU1.1) (elim.matOne_symm hdU) spU2 hU2
  have hddL : splitRead
      (siteDatum (matAdd (matAdd C1 C2) (matAdd S1 S2))
        (matAdd C1 S1)) spL2 :=
    splitRead_congr (matAdd C2 S2) _
      (sqAt_siteDatum n _ _ hL.1 hL1.1) (elim.matOne_symm hdL) spL2 hL2
  refine ⟨elim.sqAt_matAdd n S1 S2 hS1 hS2,
    elim.sqAt_matAdd n C1 C2 hC1 hC2, ⟨hU, ?_⟩, hL, ?_⟩
  · show revAt spU = 0
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    rw [← hpU1]
    exact rev_mono (siteDatum C1 S1)
      (siteDatum (matAdd C1 C2) (matAdd S1 S2)) spU2 spU1 spU hddU hpU2
      hU1 hU
  · show revAt spL = 0
    refine Nat.le_antisymm ?_ (Nat.zero_le _)
    rw [← hpL1]
    exact rev_mono (matAdd C1 S1)
      (matAdd (matAdd C1 C2) (matAdd S1 S2)) spL2 spL1 spL hddL hpL2
      hL1 hL

/-- The pointwise converse of the first transport clause: a split
whose datum prices every vector of the stated order at or above the
sum's unit reads the upper side throughout, an occupied reversal
count exhibiting a vector below it (`rev_witness`). -/
theorem psd_of_all {n : Nat} (S : Mat) (sp : Split n)
    (h : splitRead S sp)
    (hall : ∀ u : List BPair, u.length = n →
      ¬ (dotN u (matVec S u) < BPair.unit)) : psdAt sp := by
  have key : ∀ t : Nat, t < 1 → t = 0
    | 0, _ => rfl
    | _ + 1, hh => absurd (Nat.lt_of_succ_lt_succ hh) (Nat.not_lt_zero _)
  show revAt sp = 0
  cases Nat.lt_or_ge (revAt sp) 1 with
  | inl hlt => exact key (revAt sp) hlt
  | inr hge =>
    obtain ⟨u, hu, hltu⟩ := rev_witness S sp h hge
    exact absurd hltu (hall u hu)


/-- The transpose product's stated order at the unit scale. -/
private theorem sqAt_gramT {n : Nat} (M : Mat) (hM : sqAt M n) :
    sqAt (matScale Pos.one (matMul (transposeM M) M)) n :=
  sqAt_matScale n Pos.one _
    (elim.sqAt_of
      ((elim.length_matMul (transposeM M) M).trans
        (elim.transposeLen M (elim.rowsLen_of_sqAt hM) (elim.sqAt_len hM)))
      (elim.rowsLen_cast
        (elim.transposeLen M (elim.rowsLen_of_sqAt hM) (elim.sqAt_len hM))
        (elim.rowsLen_matMul (transposeM M) M)))

/-- The cap's quadratic read at a vector: the site's two members, the
scaled identity against the transpose product, read the priced gap
`W²⟨v,v⟩` against `⟨Mv,Mv⟩`. -/
private theorem capSite_read {n : Nat} (M : Mat) (hM : sqAt M n) (W : Pos)
    (v : List BPair) (hv : v.length = n) :
    (quadForm (siteDatum (matScale (W * W) (idMat n))
        (matScale Pos.one (matMul (transposeM M) M))) v).oneValue
      (BPair.ofPos (W * W) * dotN v v
        + (dotN (matVec M v) (matVec M v)).swap) := by
  have hI : sqAt (idMat n) n := sqAt_idMat n
  have hX : sqAt (matScale (W * W) (idMat n)) n := sqAt_matScale n _ _ hI
  have hY : sqAt (matScale Pos.one (matMul (transposeM M) M)) n :=
    sqAt_gramT M hM
  refine BPair.oneValue_trans
    (quadForm_site ((elim.sqAt_len hX).trans hv.symm)
      (by rw [hv]; exact elim.rowsLen_of_sqAt hX)
      ((elim.sqAt_len hY).trans hv.symm)
      (by rw [hv]; exact elim.rowsLen_of_sqAt hY)) ?_
  refine BPair.add_congr ?_ (ground.swap_congr ?_)
  · refine BPair.oneValue_trans (quadForm_ofPos (W * W) (idMat n) v) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (dotN_congrR v _ _ (matVec_idMat n v hv))
  · refine BPair.oneValue_trans
      (quadForm_ofPos Pos.one (matMul (transposeM M) M) v) ?_
    refine BPair.oneValue_trans
      (BPair.ofPos_one_mul (quadForm (matMul (transposeM M) M) v)) ?_
    refine BPair.oneValue_trans
      (dotN_congrR v _ _
        (elim.matVec_matMul (transposeM M) M n
          (elim.rowsLen_of_sqAt hM) v hv)) ?_
    exact elim.dotN_transpose_flip M n (elim.rowsLen_of_sqAt hM) v
      (matVec M v) hv (elim.matVec_length M v)

/-- The cap's pointwise square read (`lem:fourpoint`'s magnetic square
cap): the capped transpose product prices every vector,
`⟨Mv, Mv⟩ ≤ W²⟨v, v⟩`. -/
theorem cap_vec {n : Nat} (M : Mat) (hM : sqAt M n) (W : Pos)
    (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL)
    (v : List BPair) (hv : v.length = n) :
    dotN (matVec M v) (matVec M v) ≤ BPair.ofPos (W * W) * dotN v v := by
  have hpsd := psd_all _ spU hcapM.2.2.1.1 hcapM.2.2.1.2 v hv
  have hread := capSite_read M hM W v hv
  have hunit : BPair.unit
      ≤ BPair.ofPos (W * W) * dotN v v
        + (dotN (matVec M v) (matVec M v)).swap :=
    ground.leB_congr_right hread (ground.leB_of_not_lt hpsd)
  have h2 := ground.leB_of_unit_add hunit
  refine ground.leB_congr_left ?_ h2
  exact BPair.oneValue_of_eq (BPair.swap_swap _).symm

/-- Every finite family's Gram is positive semidefinite
(`con:coeff`'s Gram read at `lem:inertia`): a coefficient vector's
form at the Gram is the family's combination at that vector paired
against itself, the pairing bilinear — the pairing against a
combination the coefficients' fold over the rows' pairings
(`elim.dotP_combo`), read twice — a self-pairing at or beyond the
sum's unit at the positive pairing, so every split reads the upper
side throughout (`psd_of_all`).  The family enters at one joined
coordinate list, `con:coeff`'s paired slots at one list, the row
width the binder. -/
theorem gram_psd (L : Mat) (m : Nat) (hr : rowsLen m L)
    (sp : Split L.length) (h : splitRead (gramM L) sp) : psdAt sp := by
  refine psd_of_all (gramM L) sp h (fun u hu hlt => ?_)
  have hrow : poly.oneValue (matVec (gramM L) u)
      (L.map (fun r => dotP r (combo m u L))) := by
    show poly.oneValue
      ((L.map (fun r => L.map (fun c => dotP r c))).map (fun row => dotN row u))
      (L.map (fun r => dotP r (combo m u L)))
    rw [ground.map_map]
    refine poly.oneValue_map _ _ L (fun r _ => ?_)
    refine BPair.oneValue_trans (dotN_read _ u) ?_
    rw [dotP_comm]
    exact BPair.oneValue_symm (dotP_combo u L r m hr)
  have hq : (dotN u (matVec (gramM L) u)).oneValue
      (dotN (combo m u L) (combo m u L)) := by
    refine BPair.oneValue_trans (dotN_congrR u _ _ hrow) ?_
    refine BPair.oneValue_trans (dotN_read u _) ?_
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (dotN_read (combo m u L) (combo m u L)))
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (dotP_combo u L (combo m u L) m hr))
    rw [dotP_comm u, dotP_comm u]
    refine dotP_congr_left _ _ u (fun j hj => ?_)
    have hjL : j < L.length := hu ▸ hj
    rw [show ground.getAt BPair.unit (L.map (fun r => dotP r (combo m u L))) j
        = dotP (ground.getAt [] L j) (combo m u L) from ?_,
      show ground.getAt BPair.unit (L.map (fun row => dotP (combo m u L) row)) j
        = dotP (combo m u L) (ground.getAt [] L j) from ?_, dotP_comm]
    · exact BPair.oneValue_refl _
    · exact ground.getAt_map [] BPair.unit (fun row => dotP (combo m u L) row) L j hjL
    · exact ground.getAt_map [] BPair.unit (fun r => dotP r (combo m u L)) L j hjL
  exact dotN_self_side (combo m u L)
    (BPair.lt_congr hq (BPair.oneValue_refl _) hlt)

/-- The pointwise square cap's certificate (`lem:fourpoint`'s magnetic
square cap at the split reads): every vector's price reads the two
splits' conjuncts, the reversal count's own refusal. -/
theorem capAt_of_sq {n : Nat} (M : Mat) (hM : sqAt M n) (W : Pos)
    (hcap : ∀ v : List BPair, v.length = n →
      dotN (matVec M v) (matVec M v) ≤ BPair.ofPos (W * W) * dotN v v)
    (spU spL : Split n)
    (hU : splitRead (siteDatum (matScale (W * W) (idMat n))
      (matScale Pos.one (matMul (transposeM M) M))) spU)
    (hL : splitRead (matAdd (matScale (W * W) (idMat n))
      (matScale Pos.one (matMul (transposeM M) M))) spL) :
    capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL := by
  have hI : sqAt (idMat n) n := sqAt_idMat n
  have hX : sqAt (matScale (W * W) (idMat n)) n := sqAt_matScale n _ _ hI
  have hY : sqAt (matScale Pos.one (matMul (transposeM M) M)) n :=
    sqAt_gramT M hM
  refine ⟨hY, hX, ⟨hU, ?_⟩, hL, ?_⟩
  · refine psd_of_all _ spU hU (fun v hv => ?_)
    refine ground.leB_not_lt ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm (capSite_read M hM W v hv)) ?_
    refine ground.leB_unit_add ?_
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq (BPair.swap_swap _)) ?_
    exact hcap v hv
  · refine psd_of_all _ spL hL (fun v hv => ?_)
    refine ground.leB_not_lt ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm (quadForm_add_sq hX hY hv)) ?_
    refine ground.leB_congr_left (BPair.add_unit BPair.unit) ?_
    refine ground.leB_add ?_ ?_
    · refine ground.leB_congr_right
        (BPair.oneValue_symm
          (BPair.oneValue_trans (quadForm_ofPos (W * W) (idMat n) v)
            (BPair.mul_congr (BPair.oneValue_refl _)
              (dotN_congrR v _ _ (matVec_idMat n v hv))))) ?_
      exact ground.unitLeMul (ground.leB_of_lt (ground.unitLtOfPos (W * W)))
        (ground.leB_of_not_lt (elim.dotN_self_side v))
    · refine ground.leB_congr_right
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (quadForm_ofPos Pos.one (matMul (transposeM M) M) v)
            (BPair.oneValue_trans
              (BPair.ofPos_one_mul _)
              (BPair.oneValue_trans
                (dotN_congrR v _ _
                  (elim.matVec_matMul (transposeM M) M n
                    (elim.rowsLen_of_sqAt hM) v hv))
                (elim.dotN_transpose_flip M n (elim.rowsLen_of_sqAt hM) v
                  (matVec M v) hv (elim.matVec_length M v)))))) ?_
      exact ground.leB_of_not_lt (elim.dotN_self_side (matVec M v))

/-- The weighting passes through the join block by block, the
coupling's exchange riding the weighted key exchange. -/
theorem matScale_blockJoin (c : Pos) {k m : Nat} (P B Q : Mat)
    (hBl : B.length = k) (hBr : rowsLen m B) :
    matOneValue (matScale c (blockJoin P B Q))
      (blockJoin (matScale c P) (matScale c B) (matScale c Q)) := by
  have hTr : rowsLen k (transposeM B) :=
    elim.rowsLen_cast hBl (elim.rowsLen_transposeM B)
  have hTr' : rowsLen k (transposeM (matScale c B)) :=
    elim.rowsLen_cast ((length_matScale c B).trans hBl)
      (elim.rowsLen_transposeM (matScale c B))
  show matOneValue
    (matScale c (List.zipWith (· ++ ·) P B
      ++ List.zipWith (· ++ ·) (transposeM B) Q))
    (List.zipWith (· ++ ·) (matScale c P) (matScale c B)
      ++ List.zipWith (· ++ ·) (transposeM (matScale c B))
        (matScale c Q))
  rw [show matScale c (List.zipWith (· ++ ·) P B
        ++ List.zipWith (· ++ ·) (transposeM B) Q)
      = matScale c (List.zipWith (· ++ ·) P B)
        ++ matScale c (List.zipWith (· ++ ·) (transposeM B) Q) from
      ground.map_append _ _ _,
    scaleZip c P B, scaleZip c (transposeM B) Q]
  refine elim.matOne_append _ _ _ _ (elim.matOne_refl _) ?_
  exact elim.matOne_rowJoin _ _ _ _
    (rowsLen_mapRows _ (transposeM B) k hTr) hTr'
    (elim.matOne_symm (transposeM_matScale c m B hBr))
    (elim.matOne_refl (matScale c Q))

/-- The balance weighting passes through the join block by block. -/
theorem matScaleB_blockJoin (w : BPair) {k m : Nat} (P B Q : Mat)
    (hBl : B.length = k) (hBr : rowsLen m B) :
    matOneValue (matScaleB w (blockJoin P B Q))
      (blockJoin (matScaleB w P) (matScaleB w B) (matScaleB w Q)) := by
  have hTr : rowsLen k (transposeM B) :=
    elim.rowsLen_cast hBl (elim.rowsLen_transposeM B)
  have hTr' : rowsLen k (transposeM (matScaleB w B)) :=
    elim.rowsLen_cast ((length_scaleB w B).trans hBl)
      (elim.rowsLen_transposeM (matScaleB w B))
  show matOneValue
    (matScaleB w (List.zipWith (· ++ ·) P B
      ++ List.zipWith (· ++ ·) (transposeM B) Q))
    (List.zipWith (· ++ ·) (matScaleB w P) (matScaleB w B)
      ++ List.zipWith (· ++ ·) (transposeM (matScaleB w B))
        (matScaleB w Q))
  rw [show matScaleB w (List.zipWith (· ++ ·) P B
        ++ List.zipWith (· ++ ·) (transposeM B) Q)
      = matScaleB w (List.zipWith (· ++ ·) P B)
        ++ matScaleB w (List.zipWith (· ++ ·) (transposeM B) Q) from
      ground.map_append _ _ _,
    scaleBZip w P B, scaleBZip w (transposeM B) Q]
  refine elim.matOne_append _ _ _ _ (elim.matOne_refl _) ?_
  exact elim.matOne_rowJoin _ _ _ _
    (rowsLen_scaleB w k (transposeM B) hTr) hTr'
    (elim.matOne_symm (transposeM_scaleB w m B hBr))
    (elim.matOne_refl (matScaleB w Q))

/-- The entrywise sum passes through the join block by block. -/
theorem matAdd_blockJoin {k m : Nat} (P1 B1 Q1 P2 B2 Q2 : Mat)
    (hP1 : rowsLen k P1) (hP2 : rowsLen k P2)
    (hP1l : P1.length = k) (hP2l : P2.length = k)
    (hB1l : B1.length = k) (hB2l : B2.length = k)
    (hB1r : rowsLen m B1) (hB2r : rowsLen m B2) (hk : 0 < k) :
    matAdd (blockJoin P1 B1 Q1) (blockJoin P2 B2 Q2)
      = blockJoin (matAdd P1 P2) (matAdd B1 B2) (matAdd Q1 Q2) := by
  have hT1 : rowsLen k (transposeM B1) :=
    elim.rowsLen_cast hB1l (elim.rowsLen_transposeM B1)
  show List.zipWith (List.zipWith BPair.add)
      (List.zipWith (· ++ ·) P1 B1
        ++ List.zipWith (· ++ ·) (transposeM B1) Q1)
      (List.zipWith (· ++ ·) P2 B2
        ++ List.zipWith (· ++ ·) (transposeM B2) Q2)
    = List.zipWith (· ++ ·) (matAdd P1 P2) (matAdd B1 B2)
      ++ List.zipWith (· ++ ·) (transposeM (matAdd B1 B2))
        (matAdd Q1 Q2)
  rw [ground.zipWith_append (List.zipWith BPair.add)
      (List.zipWith (· ++ ·) P1 B1)
      (List.zipWith (· ++ ·) (transposeM B1) Q1)
      (List.zipWith (· ++ ·) P2 B2)
      (List.zipWith (· ++ ·) (transposeM B2) Q2)
      ((ground.length_zipWith _ P1 B1 k hP1l hB1l).trans
        (ground.length_zipWith _ P2 B2 k hP2l hB2l).symm),
    zipAdd4 P1 B1 P2 B2 hP1 hP2,
    zipAdd4 (transposeM B1) Q1 (transposeM B2) Q2 hT1
      (elim.rowsLen_cast hB2l (elim.rowsLen_transposeM B2)),
    elim.transposeM_matAdd B1 B2 hB1r hB2r
      (hB1l.trans hB2l.symm) (by rw [hB1l]; exact hk)]
  rfl

/-- The join's congruence at its three blocks. -/
theorem blockJoin_congr {k m : Nat} (P P' B B' Q Q' : Mat)
    (hPr : rowsLen k P) (hPr' : rowsLen k P')
    (hBl : B.length = k) (hBl' : B'.length = k)
    (hBr : rowsLen m B) (hBr' : rowsLen m B')
    (hP : matOneValue P P') (hB : matOneValue B B')
    (hQ : matOneValue Q Q') :
    matOneValue (blockJoin P B Q) (blockJoin P' B' Q') := by
  refine elim.matOne_append _ _ _ _
    (elim.matOne_rowJoin P P' B B' hPr hPr' hP hB) ?_
  exact elim.matOne_rowJoin _ _ _ _
    (elim.rowsLen_cast hBl (elim.rowsLen_transposeM B))
    (elim.rowsLen_cast hBl' (elim.rowsLen_transposeM B'))
    (elim.transposeM_congrM m B B' hBr hBr'
      (hBl.trans hBl'.symm) hB) hQ

private theorem mapShiftUnit (a i : Nat) (hi : i < a) :
    ∀ l : List Nat,
      poly.unitTail (l.map (fun c =>
        if a + c = i then BPair.ofNat 1 else BPair.unit))
  | [] => trivial
  | c :: l => by
    refine ⟨?_, mapShiftUnit a i hi l⟩
    show BPair.oneValue
      (if a + c = i then BPair.ofNat 1 else BPair.unit) BPair.unit
    rw [if_neg (Nat.ne_of_gt
      (Nat.lt_of_lt_of_le hi (Nat.le_add_right a c)))]
    exact BPair.oneValue_refl BPair.unit

private theorem rangeUnit : ∀ (a t : Nat), a ≤ t →
    poly.unitTail ((List.range a).map (fun j =>
      if j = t then BPair.ofNat 1 else BPair.unit))
  | 0, _, _ => trivial
  | a + 1, t, h => by
    rw [ground.range_succ a, ground.map_append]
    refine elim.unitTail_append
      (rangeUnit a t (Nat.le_of_succ_le h)) ⟨?_, trivial⟩
    show BPair.oneValue
      (if a = t then BPair.ofNat 1 else BPair.unit) BPair.unit
    rw [if_neg (Nat.ne_of_lt h)]
    exact BPair.oneValue_refl BPair.unit

private theorem shiftInd (a r : Nat) : ∀ l : List Nat,
    poly.oneValue
      (l.map (fun c =>
        if a + c = a + r then BPair.ofNat 1 else BPair.unit))
      (l.map (fun c => if c = r then BPair.ofNat 1 else BPair.unit))
  | [] => trivial
  | c :: l => by
    refine ⟨?_, shiftInd a r l⟩
    show BPair.oneValue
      (if a + c = a + r then BPair.ofNat 1 else BPair.unit)
      (if c = r then BPair.ofNat 1 else BPair.unit)
    match Nat.decEq c r with
    | isTrue he =>
      rw [he, if_pos rfl, if_pos rfl]
      exact BPair.oneValue_refl _
    | isFalse he =>
      rw [if_neg (fun hx => he (ground.addCancelL a hx)),
        if_neg he]
      exact BPair.oneValue_refl _

/-- The indicator row splits at a join of its width: below the
target the leading width's own indicator against the shifted
piece's read. -/
private theorem idRow_split (a b i : Nat) :
    elim.idRow (a + b) i
      = elim.idRow a i ++ (List.range b).map (fun c =>
          if a + c = i then BPair.ofNat 1 else BPair.unit) := by
  show (List.range (a + b)).map _ = _
  rw [ground.range_split a b, ground.map_append, ground.map_map]
  rfl

/-- The trailing pad peels one leading slab: the padded deviation
at a joined leading order is the join of the vacant slab against
the pad at the residual order. -/
theorem trailPad_join {n0 k m : Nat} (M : Mat) (hM : sqAt M m)
    (hn0 : 0 < n0) :
    matOneValue (trailPad (n0 + k) M)
      (blockJoin (nullMat n0 n0) (nullMat n0 (k + m))
        (trailPad k M)) := by
  have hMl : M.length = m := sqAt_len hM
  have hBtl : (transposeM (nullMat n0 (k + m))).length = k + m :=
    elim.length_transposeM _ (rowsLen_nullMat n0 (k + m))
      (by rw [length_nullMat]; exact hn0)
  have hTr : rowsLen n0 (transposeM (nullMat n0 (k + m))) :=
    elim.rowsLen_cast (length_nullMat n0 (k + m))
      (elim.rowsLen_transposeM _)
  have hQl : (trailPad k M).length = k + m := by
    show (nullMat k (k + M.length)
      ++ M.map (fun r => List.replicate k BPair.unit ++ r)).length
      = k + m
    rw [ground.length_append, length_nullMat, ground.length_map, hMl]
  have hLl : (trailPad (n0 + k) M).length = n0 + (k + m) := by
    show (nullMat (n0 + k) ((n0 + k) + M.length)
      ++ M.map (fun r =>
        List.replicate (n0 + k) BPair.unit ++ r)).length = _
    rw [ground.length_append, length_nullMat, ground.length_map, hMl,
      Nat.add_assoc]
  refine elim.matOne_getAt _ _ ?_ ?_
  · rw [hLl, blockJoin_len _ _ _ (length_nullMat n0 n0)
      (length_nullMat n0 (k + m)) hBtl hQl]
  · intro i hi
    rw [hLl] at hi
    match Nat.lt_or_ge i n0 with
    | Or.inl hin =>
      have hrowL : ground.getAt ([] : List BPair)
          (trailPad (n0 + k) M) i
          = List.replicate ((n0 + k) + M.length) BPair.unit := by
        show ground.getAt ([] : List BPair)
          (nullMat (n0 + k) ((n0 + k) + M.length) ++ _) i = _
        rw [ground.getAt_append ([] : List BPair) _ _ i,
          if_pos (show i < (nullMat (n0 + k)
              ((n0 + k) + M.length)).length by
            rw [length_nullMat]
            exact Nat.lt_of_lt_of_le hin (Nat.le_add_right n0 k))]
        exact ground.getAt_replicate [] _ (n0 + k) i
          (Nat.lt_of_lt_of_le hin (Nat.le_add_right n0 k))
      have hb1 : ground.getAt ([] : List BPair) (nullMat n0 n0) i
          = List.replicate n0 BPair.unit :=
        ground.getAt_replicate [] _ n0 i hin
      have hb2 : ground.getAt ([] : List BPair) (nullMat n0 (k + m)) i
          = List.replicate (k + m) BPair.unit :=
        ground.getAt_replicate [] _ n0 i hin
      rw [hrowL, blockJoin_rowP _ _ _ (length_nullMat n0 n0)
          (length_nullMat n0 (k + m)) i hin, hb1, hb2]
      exact poly.unitTail_oneValue (poly.unitTail_replicate _)
        (elim.unitTail_append (poly.unitTail_replicate n0)
          (poly.unitTail_replicate (k + m)))
    | Or.inr hin =>
      obtain ⟨r, rfl⟩ := Nat.le.dest hin
      have hr : r < k + m := Nat.lt_of_add_lt_add_left hi
      rw [blockJoin_rowQ _ _ _ (length_nullMat n0 n0)
        (length_nullMat n0 (k + m)) hBtl hQl r hr]
      have hrowT : poly.unitTail (ground.getAt ([] : List BPair)
          (transposeM (nullMat n0 (k + m))) r) :=
        elim.matNull_rowAt _ (elim.matNull_transposeM _
          (elim.matNull_nullMat (k + m) n0)) r
      match Nat.lt_or_ge r k with
      | Or.inl hrk =>
        have hrowL : ground.getAt ([] : List BPair)
            (trailPad (n0 + k) M) (n0 + r)
            = List.replicate ((n0 + k) + M.length) BPair.unit := by
          show ground.getAt ([] : List BPair)
            (nullMat (n0 + k) ((n0 + k) + M.length) ++ _) (n0 + r) = _
          rw [ground.getAt_append ([] : List BPair) _ _ (n0 + r),
            if_pos (show n0 + r < (nullMat (n0 + k)
                ((n0 + k) + M.length)).length by
              rw [length_nullMat]
              exact Nat.add_lt_add_left hrk n0)]
          exact ground.getAt_replicate [] _ (n0 + k) (n0 + r)
            (Nat.add_lt_add_left hrk n0)
        have hrowQ : ground.getAt ([] : List BPair)
            (trailPad k M) r
            = List.replicate (k + M.length) BPair.unit := by
          show ground.getAt ([] : List BPair)
            (nullMat k (k + M.length) ++ _) r = _
          rw [ground.getAt_append ([] : List BPair) _ _ r,
            if_pos (show r < (nullMat k (k + M.length)).length by
              rw [length_nullMat]; exact hrk)]
          exact ground.getAt_replicate [] _ k r hrk
        rw [hrowL, hrowQ]
        exact poly.unitTail_oneValue (poly.unitTail_replicate _)
          (elim.unitTail_append hrowT (poly.unitTail_replicate _))
      | Or.inr hrk =>
        obtain ⟨r2, rfl⟩ := Nat.le.dest hrk
        have hr2 : r2 < m := Nat.lt_of_add_lt_add_left hr
        have hr2M : r2 < M.length := by rw [hMl]; exact hr2
        have hrowL : ground.getAt ([] : List BPair)
            (trailPad (n0 + k) M) (n0 + (k + r2))
            = List.replicate (n0 + k) BPair.unit
              ++ ground.getAt [] M r2 := by
          show ground.getAt ([] : List BPair)
            (nullMat (n0 + k) ((n0 + k) + M.length)
              ++ M.map (fun r =>
                List.replicate (n0 + k) BPair.unit ++ r))
            (n0 + (k + r2)) = _
          rw [show n0 + (k + r2)
              = (nullMat (n0 + k) ((n0 + k) + M.length)).length + r2 by
              rw [length_nullMat, Nat.add_assoc],
            ground.getAt_append_add ([] : List BPair) _ _ r2,
            ground.getAt_map [] [] _ M r2 hr2M]
        have hrowQ : ground.getAt ([] : List BPair)
            (trailPad k M) (k + r2)
            = List.replicate k BPair.unit
              ++ ground.getAt [] M r2 := by
          show ground.getAt ([] : List BPair)
            (nullMat k (k + M.length)
              ++ M.map (fun r =>
                List.replicate k BPair.unit ++ r)) (k + r2) = _
          rw [show k + r2 = (nullMat k (k + M.length)).length + r2 by
              rw [length_nullMat],
            ground.getAt_append_add ([] : List BPair) _ _ r2,
            ground.getAt_map [] [] _ M r2 hr2M]
        rw [hrowL, hrowQ, ground.replicate_append BPair.unit n0 k,
          ground.append_assoc]
        refine poly.oneValue_append _ _ _ _ ?_ ?_
          (poly.oneValue_refl _)
        · rw [ground.length_replicate,
            elim.rowsLen_getAt _ (k + r2) hTr
              (by rw [hBtl]; exact hr)]
        · exact poly.unitTail_oneValue (poly.unitTail_replicate n0) hrowT

/-- The leading identity's pad peels one leading slab: the identity
at a joined leading order is the join of the slab's identity against
the pad at the residual order. -/
theorem headId_join {n0 k m : Nat} (hn0 : 0 < n0) :
    matOneValue (headId (n0 + k) m)
      (blockJoin (idMat n0) (nullMat n0 (k + m)) (headId k m)) := by
  have hBtl : (transposeM (nullMat n0 (k + m))).length = k + m :=
    elim.length_transposeM _ (rowsLen_nullMat n0 (k + m))
      (by rw [length_nullMat]; exact hn0)
  have hTr : rowsLen n0 (transposeM (nullMat n0 (k + m))) :=
    elim.rowsLen_cast (length_nullMat n0 (k + m))
      (elim.rowsLen_transposeM _)
  have hQl : (headId k m).length = k + m := by
    show ((idMat k).map (fun r => r ++ List.replicate m BPair.unit)
      ++ nullMat m (k + m)).length = k + m
    rw [ground.length_append, ground.length_map, idMat_len,
      length_nullMat]
  have hLl : (headId (n0 + k) m).length = n0 + (k + m) := by
    show ((idMat (n0 + k)).map
        (fun r => r ++ List.replicate m BPair.unit)
      ++ nullMat m ((n0 + k) + m)).length = _
    rw [ground.length_append, ground.length_map, idMat_len,
      length_nullMat, Nat.add_assoc]
  have hmapl : ((idMat (n0 + k)).map
      (fun r => r ++ List.replicate m BPair.unit)).length = n0 + k := by
    rw [ground.length_map, idMat_len]
  refine elim.matOne_getAt _ _ ?_ ?_
  · rw [hLl, blockJoin_len _ _ _ (idMat_len n0)
      (length_nullMat n0 (k + m)) hBtl hQl]
  · intro i hi
    rw [hLl] at hi
    have hrowMap : ∀ t : Nat, t < n0 + k →
        ground.getAt ([] : List BPair) (headId (n0 + k) m) t
          = elim.idRow (n0 + k) t ++ List.replicate m BPair.unit := by
      intro t ht
      show ground.getAt ([] : List BPair)
        ((idMat (n0 + k)).map
            (fun r => r ++ List.replicate m BPair.unit)
          ++ nullMat m ((n0 + k) + m)) t = _
      rw [ground.getAt_append ([] : List BPair) _ _ t,
        if_pos (by rw [hmapl]; exact ht),
        ground.getAt_map [] [] _ (idMat (n0 + k)) t
          (by rw [idMat_len]; exact ht),
        idMat_row (n0 + k) t ht]
    match Nat.lt_or_ge i n0 with
    | Or.inl hin =>
      have hb1 : ground.getAt ([] : List BPair) (nullMat n0 (k + m)) i
          = List.replicate (k + m) BPair.unit :=
        ground.getAt_replicate [] _ n0 i hin
      rw [hrowMap i (Nat.lt_of_lt_of_le hin (Nat.le_add_right n0 k)),
        blockJoin_rowP _ _ _ (idMat_len n0)
          (length_nullMat n0 (k + m)) i hin,
        idMat_row n0 i hin, idRow_split n0 k i, ground.append_assoc,
        hb1]
      refine poly.oneValue_append _ _ _ _ rfl
        (poly.oneValue_refl _) ?_
      exact poly.unitTail_oneValue
        (elim.unitTail_append (mapShiftUnit n0 i hin (List.range k))
          (poly.unitTail_replicate m))
        (poly.unitTail_replicate (k + m))
    | Or.inr hin =>
      obtain ⟨r, rfl⟩ := Nat.le.dest hin
      have hr : r < k + m := Nat.lt_of_add_lt_add_left hi
      rw [blockJoin_rowQ _ _ _ (idMat_len n0)
        (length_nullMat n0 (k + m)) hBtl hQl r hr]
      have hrowT : poly.unitTail (ground.getAt ([] : List BPair)
          (transposeM (nullMat n0 (k + m))) r) :=
        elim.matNull_rowAt _ (elim.matNull_transposeM _
          (elim.matNull_nullMat (k + m) n0)) r
      have hrowTl : (ground.getAt ([] : List BPair)
          (transposeM (nullMat n0 (k + m))) r).length = n0 :=
        elim.rowsLen_getAt _ r hTr (by rw [hBtl]; exact hr)
      match Nat.lt_or_ge r k with
      | Or.inl hrk =>
        have hrowQ : ground.getAt ([] : List BPair) (headId k m) r
            = elim.idRow k r ++ List.replicate m BPair.unit := by
          show ground.getAt ([] : List BPair)
            ((idMat k).map (fun r => r ++ List.replicate m BPair.unit)
              ++ nullMat m (k + m)) r = _
          rw [ground.getAt_append ([] : List BPair) _ _ r,
            if_pos (by rw [ground.length_map, idMat_len]; exact hrk),
            ground.getAt_map [] [] _ (idMat k) r
              (by rw [idMat_len]; exact hrk),
            idMat_row k r hrk]
        rw [hrowMap (n0 + r) (Nat.add_lt_add_left hrk n0),
          idRow_split n0 k (n0 + r), ground.append_assoc, hrowQ]
        refine poly.oneValue_append _ _ _ _
          ((length_idRow n0 (n0 + r)).trans hrowTl.symm) ?_ ?_
        · exact poly.unitTail_oneValue
            (rangeUnit n0 (n0 + r) (Nat.le_add_right n0 r)) hrowT
        · exact poly.oneValue_append _ _ _ _
            (by rw [ground.length_map, ground.length_range,
              length_idRow])
            (shiftInd n0 r (List.range k)) (poly.oneValue_refl _)
      | Or.inr hrk =>
        obtain ⟨r2, rfl⟩ := Nat.le.dest hrk
        have hr2 : r2 < m := Nat.lt_of_add_lt_add_left hr
        have hrowL : ground.getAt ([] : List BPair)
            (headId (n0 + k) m) (n0 + (k + r2))
            = List.replicate ((n0 + k) + m) BPair.unit := by
          show ground.getAt ([] : List BPair)
            ((idMat (n0 + k)).map
                (fun r => r ++ List.replicate m BPair.unit)
              ++ nullMat m ((n0 + k) + m)) (n0 + (k + r2)) = _
          rw [show n0 + (k + r2)
              = ((idMat (n0 + k)).map
                  (fun r => r ++ List.replicate m BPair.unit)).length
                + r2 by rw [hmapl, Nat.add_assoc],
            ground.getAt_append_add ([] : List BPair) _ _ r2]
          exact ground.getAt_replicate [] _ m r2 hr2
        have hrowQ : ground.getAt ([] : List BPair)
            (headId k m) (k + r2)
            = List.replicate (k + m) BPair.unit := by
          show ground.getAt ([] : List BPair)
            ((idMat k).map (fun r => r ++ List.replicate m BPair.unit)
              ++ nullMat m (k + m)) (k + r2) = _
          rw [show k + r2 = ((idMat k).map
              (fun r => r ++ List.replicate m BPair.unit)).length + r2
              by rw [ground.length_map, idMat_len],
            ground.getAt_append_add ([] : List BPair) _ _ r2]
          exact ground.getAt_replicate [] _ m r2 hr2
        rw [hrowL, hrowQ]
        exact poly.unitTail_oneValue (poly.unitTail_replicate _)
          (elim.unitTail_append hrowT (poly.unitTail_replicate _))

/-- The leading identity's pad is square at the joined order. -/
theorem headId_sq (k m : Nat) : sqAt (headId k m) (k + m) := by
  refine elim.sqAt_of ?_ ?_
  · show ((idMat k).map (fun r => r ++ List.replicate m BPair.unit)
      ++ nullMat m (k + m)).length = k + m
    rw [ground.length_append, ground.length_map, idMat_len,
      length_nullMat]
  · refine elim.rowsLen_append (k + m) ?_ (rowsLen_nullMat m (k + m))
    show rowsLen (k + m) ((idMat k).map
      (fun r => r ++ List.replicate m BPair.unit))
    have hgo : ∀ (L : Mat), rowsLen k L →
        rowsLen (k + m) (L.map
          (fun r => r ++ List.replicate m BPair.unit)) := by
      intro L
      induction L with
      | nil => intro _; trivial
      | cons r t ih =>
        intro hL
        refine ⟨?_, ih hL.2⟩
        rw [ground.length_append, ground.length_replicate, hL.1]
    exact hgo (idMat k) (idMat_rows k)

theorem trailPad_sq {k m : Nat} (D : Mat)
    (hD : sqAt D m) : sqAt (trailPad k D) (k + m) := by
  have hDl : D.length = m := sqAt_len hD
  show sqAt (nullMat k (k + D.length)
    ++ D.map (fun r => List.replicate k BPair.unit ++ r)) (k + m)
  rw [hDl]
  refine sqAt_of ?_ ?_
  · rw [ground.length_append, length_nullMat, ground.length_map, hDl]
  · exact elim.rowsLen_append (k + m) (rowsLen_nullMat k (k + m))
      (elim.rowsLen_padL k m D (rowsLen_of_sqAt hD))

/-- The padded deviation's form at a joined vector is the trailing
block's own at the trailing half: the leading block, the coupling
slab and its exchange all read the sum's unit. -/
private theorem padVec {k : Nat} (x w : List BPair)
    (hx : x.length = k) :
    ∀ D : Mat,
      poly.oneValue
        (matVec (D.map (fun r => List.replicate k BPair.unit ++ r))
          (x ++ w))
        (matVec D w)
  | [] => trivial
  | r :: D => by
    refine ⟨?_, padVec x w hx D⟩
    refine BPair.oneValue_trans
      (dotN_app (List.replicate k BPair.unit) r x w
        (by rw [ground.length_replicate, hx])) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (dotN_nullL (List.replicate k BPair.unit) x
          (poly.unitTail_replicate k)) (BPair.oneValue_refl _)) ?_
    exact BPair.unit_add (dotN r w)

private theorem trailPad_quad {k : Nat} (D : Mat)
    (x w : List BPair) (hx : x.length = k) :
    (dotN (x ++ w) (matVec (trailPad k D) (x ++ w))).oneValue
      (dotN w (matVec D w)) := by
  show (dotN (x ++ w)
      (matVec (nullMat k (k + D.length)
        ++ D.map (fun r => List.replicate k BPair.unit ++ r))
        (x ++ w))).oneValue (dotN w (matVec D w))
  rw [elim.matVec_append]
  refine BPair.oneValue_trans
    (dotN_app x w (matVec (nullMat k (k + D.length)) (x ++ w))
      (matVec (D.map (fun r => List.replicate k BPair.unit ++ r))
        (x ++ w))
      (by rw [hx, matVec_length, length_nullMat])) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (dotN_nullR x _ (elim.matVec_nullMat k (k + D.length) (x ++ w)))
      (dotN_congrR w _ _ (padVec x w hx D))) ?_
  exact BPair.unit_add (dotN w (matVec D w))

/-- The weighted identity's form at a vector is the weight against
the vector's own self pairing. -/
private theorem idQuad (wn : Pos) (n : Nat) (u : List BPair)
    (hu : u.length = n) :
    (dotN u (matVec (matScale wn (idMat n)) u)).oneValue
      (BPair.ofPos wn * dotN u u) := by
  refine BPair.oneValue_trans
    (dotN_congrR u _ _
      (poly.oneValue_trans
        (elim.matVec_matOne _ _ u (matScale_scaleB wn (idMat n)))
        (scaleId_act (BPair.ofPos wn) n u hu))) ?_
  exact elim.dotN_scaleV (BPair.ofPos wn) u u

/-- The weighted identity's form at a joined vector splits into the
two halves' self pairings at the one weight. -/
private theorem padId (wn : Pos) (k m : Nat) (x w : List BPair)
    (hx : x.length = k) (hw : w.length = m) :
    (dotN (x ++ w)
        (matVec (matScale wn (idMat (k + m))) (x ++ w))).oneValue
      (BPair.ofPos wn * dotN x x + BPair.ofPos wn * dotN w w) := by
  have hu : (x ++ w).length = k + m := by
    rw [ground.length_append, hx, hw]
  refine BPair.oneValue_trans (idQuad wn (k + m) (x ++ w) hu) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos wn))
      (dotN_app x w x w rfl)) ?_
  exact BPair.oneValue_of_eq (BPair.left_distrib _ _ _)

/-- The weighted padded deviation's form at a joined vector is the
weight against the trailing block's form at the trailing half. -/
private theorem padDev (wd : Pos) {k : Nat} (D : Mat)
    (x w : List BPair) (hx : x.length = k) :
    (dotN (x ++ w)
        (matVec (matScale wd (trailPad k D)) (x ++ w))).oneValue
      (BPair.ofPos wd * dotN w (matVec D w)) := by
  refine BPair.oneValue_trans
    (quadForm_ofPos wd (trailPad k D) (x ++ w)) ?_
  exact BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos wd))
    (trailPad_quad D x w hx)

/-- The block cap's site datum at a vector: the identity's weight
against the self pairing beside the deviation's weighted form,
swapped. -/
private theorem levelSite (wn wd : Pos) (m : Nat) (D : Mat)
    (hD : sqAt D m) (w : List BPair) (hw : w.length = m) :
    (dotN w (matVec (siteDatum (matScale wn (idMat m))
        (matScale wd D)) w)).oneValue
      (BPair.ofPos wn * dotN w w
        + (BPair.ofPos wd * dotN w (matVec D w)).swap) := by
  refine BPair.oneValue_trans
    (quadForm_site_sq
      (sqAt_matScale m wn (idMat m) (sqAt_idMat m))
      (sqAt_matScale m wd D hD) hw) ?_
  exact BPair.add_congr (idQuad wn m w hw)
    (ground.swap_congr (quadForm_ofPos wd D w))

/-- The block cap's sum at a vector: the identity's weight against
the self pairing beside the deviation's weighted form. -/
private theorem levelSum (wn wd : Pos) (m : Nat) (D : Mat)
    (hD : sqAt D m) (w : List BPair) (hw : w.length = m) :
    (dotN w (matVec (matAdd (matScale wn (idMat m))
        (matScale wd D)) w)).oneValue
      (BPair.ofPos wn * dotN w w
        + BPair.ofPos wd * dotN w (matVec D w)) := by
  refine BPair.oneValue_trans
    (quadForm_add_sq
      (sqAt_matScale m wn (idMat m) (sqAt_idMat m))
      (sqAt_matScale m wd D hD) hw) ?_
  exact BPair.add_congr (idQuad wn m w hw) (quadForm_ofPos wd D w)

/-- The block cap pads to the joined order: at a deviation
supported at the trailing block the joined cap holds at the joined
identity's own weight, the two splits of the padded data the
theorem's own — every joined vector prices the padded site datum at
the leading half's weighted self pairing joined to the block's own
form, both at or above the sum's unit. -/
theorem capAt_trailPad {k m : Nat} (D : Mat) (wn wd : Pos)
    (spU spL : Split m)
    (h : capAt (matScale wd D) (matScale wn (idMat m)) spU spL)
    (spU' spL' : Split (k + m))
    (hU' : splitRead (siteDatum (matScale wn (idMat (k + m)))
      (matScale wd (trailPad k D))) spU')
    (hL' : splitRead (matAdd (matScale wn (idMat (k + m)))
      (matScale wd (trailPad k D))) spL') :
    capAt (matScale wd (trailPad k D)) (matScale wn (idMat (k + m)))
      spU' spL' := by
  have hD : sqAt D m := sqAt_matScale_reflect wd D h.1
  have hIdS : sqAt (matScale wn (idMat (k + m))) (k + m) :=
    sqAt_matScale (k + m) wn (idMat (k + m))
      (sqAt_of (idMat_len (k + m)) (idMat_rows (k + m)))
  · have hPadS : sqAt (matScale wd (trailPad k D)) (k + m) :=
      sqAt_matScale (k + m) wd (trailPad k D) (trailPad_sq D hD)
    have hsplit : ∀ v : List BPair, v.length = k + m →
        ∃ x w : List BPair, v = x ++ w ∧ x.length = k ∧ w.length = m := by
      intro v hv
      obtain ⟨x, w, he, hx⟩ := ground.listSplit v k
        (by rw [hv]; exact Nat.le_add_right k m)
      refine ⟨x, w, he, hx, ?_⟩
      have hlen : x.length + w.length = k + m := by
        rw [← ground.length_append x w, ← he]
        exact hv
      rw [hx] at hlen
      exact ground.addCancelL k hlen
    refine ⟨hPadS, hIdS, ⟨hU', ?_⟩, hL', ?_⟩
    · refine psd_of_all _ spU' hU' (fun v hv => ?_)
      obtain ⟨x, w, he, hx, hw⟩ := hsplit v hv
      rw [he]
      have hu : (x ++ w).length = k + m := by
        rw [ground.length_append, hx, hw]
      have hchain : (dotN (x ++ w)
          (matVec (siteDatum (matScale wn (idMat (k + m)))
            (matScale wd (trailPad k D))) (x ++ w))).oneValue
          (BPair.ofPos wn * dotN x x
            + dotN w (matVec (siteDatum (matScale wn (idMat m))
                (matScale wd D)) w)) := by
        refine BPair.oneValue_trans
          (quadForm_site_sq hIdS hPadS hu) ?_
        refine BPair.oneValue_trans
          (BPair.add_congr (padId wn k m x w hx hw)
            (ground.swap_congr (padDev wd D x w hx))) ?_
        refine BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.add_assoc (BPair.ofPos wn * dotN x x)
              (BPair.ofPos wn * dotN w w)
              (BPair.ofPos wd * dotN w (matVec D w)).swap)) ?_
        exact BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (levelSite wn wd m D hD w hw))
      refine ground.leB_not_lt
        (ground.leB_congr_right (BPair.oneValue_symm hchain) ?_)
      refine ground.leB_congr_left (BPair.add_unit BPair.unit)
        (ground.leB_add
          (ground.unitLeMul (ground.leB_of_lt (ground.unitLtOfPos wn))
            (ground.leB_of_not_lt (elim.dotN_self_side x)))
          (ground.leB_of_not_lt
            (psd_all (siteDatum (matScale wn (idMat m)) (matScale wd D))
              spU h.2.2.1.1 h.2.2.1.2 w hw)))
    · refine psd_of_all _ spL' hL' (fun v hv => ?_)
      obtain ⟨x, w, he, hx, hw⟩ := hsplit v hv
      rw [he]
      have hu : (x ++ w).length = k + m := by
        rw [ground.length_append, hx, hw]
      have hchain : (dotN (x ++ w)
          (matVec (matAdd (matScale wn (idMat (k + m)))
            (matScale wd (trailPad k D))) (x ++ w))).oneValue
          (BPair.ofPos wn * dotN x x
            + dotN w (matVec (matAdd (matScale wn (idMat m))
                (matScale wd D)) w)) := by
        refine BPair.oneValue_trans
          (quadForm_add_sq hIdS hPadS hu) ?_
        refine BPair.oneValue_trans
          (BPair.add_congr (padId wn k m x w hx hw)
            (padDev wd D x w hx)) ?_
        refine BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.add_assoc (BPair.ofPos wn * dotN x x)
              (BPair.ofPos wn * dotN w w)
              (BPair.ofPos wd * dotN w (matVec D w)))) ?_
        exact BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (levelSum wn wd m D hD w hw))
      refine ground.leB_not_lt
        (ground.leB_congr_right (BPair.oneValue_symm hchain) ?_)
      refine ground.leB_congr_left (BPair.add_unit BPair.unit)
        (ground.leB_add
          (ground.unitLeMul (ground.leB_of_lt (ground.unitLtOfPos wn))
            (ground.leB_of_not_lt (elim.dotN_self_side x)))
          (ground.leB_of_not_lt
            (psd_all (matAdd (matScale wn (idMat m)) (matScale wd D))
              spL h.2.2.2.1 h.2.2.2.2 w hw)))


/-- The vacant certificate at a stated order: the identity
congruence with the kernel block at the whole order. -/
def unitSplit (n : Nat) : Split n :=
  ⟨⟨idMat n, sqAt_idMat n⟩,
    ⟨idMat n, sqAt_idMat n⟩, [], n, ground.beqRefl n⟩

/-- The vacant certificate reads the upper side, its block fold
empty. -/
theorem unitSplit_psd (o : Nat) : psdAt (unitSplit o) := rfl

/-- A null matrix splits at the vacant certificate: the identity
congruence returns the matrix itself, every entry at the sum's
unit against the kernel block. -/
theorem unitSplit_read {o : Nat} (S : Mat) (hsq : sqAt S o)
    (h : elim.matNull S) : splitRead S (unitSplit o) := by
  cases o with
  | zero =>
    cases S with
    | nil => exact ⟨hsq, ⟨BPair.ofNat_one_off, trivial, trivial⟩,
        trivial, rfl⟩
    | cons r t =>
      exact absurd (sqAt_len hsq) (fun he => Nat.noConfusion he)
  | succ n =>
    have hn : 0 < n + 1 := Nat.succ_pos n
    have hSl : S.length = n + 1 := sqAt_len hsq
    have hSr : rowsLen (n + 1) S := rowsLen_of_sqAt hsq
    have hidl : (idMat (n + 1)).length = n + 1 := idMat_len (n + 1)
    have hminor : (minor (idMat (n + 1))).oneValue (BPair.ofNat 1) :=
      BPair.oneValue_trans
        (minor_detL (idMat (n + 1))
          (rowsLen_cast hidl.symm (idMat_rows (n + 1))))
        (detL_idMat (n + 1))
    have hid2 : matOneValue (matMul (idMat (n + 1)) (idMat (n + 1)))
        (matScaleB (minor (idMat (n + 1))) (idMat (n + 1))) :=
      matOne_trans
        (idMat_matMul (k := n + 1) (n + 1) (idMat (n + 1))
          (idMat_rows (n + 1)) hidl hn)
        (matOne_symm (matOne_trans
          (matScaleB_congr hminor (idMat (n + 1)))
          (matScaleB_one (idMat (n + 1)))))
    have hnull : matOneValue S (blockMat [] (n + 1)) := by
      refine matOne_of_entries _ _ (n + 1) hSl hSr
        (blockMat_len [] (n + 1)) ?_ ?_
      · exact rowsLen_cast rfl (blockMat_rows [] (n + 1))
      · intro i j hi hj
        rw [blockMat_nil_entry (n + 1) i j hi]
        exact elim.matNull_getAt S h i j
    have h3 : matOneValue
        (matMul (transposeM (idMat (n + 1))) (matMul S (idMat (n + 1))))
        (blockMat ([] : List SBlock) (n + 1)) := by
      rw [transposeM_idMat (n + 1)]
      refine matOne_trans ?_ hnull
      refine matOne_trans ?_ (idMat_matMul (k := n + 1) (n + 1) S hSr hSl hn)
      refine matMul_congrR (n := n + 1) (k := n + 1) (idMat (n + 1))
        (matMul S (idMat (n + 1))) S ?_ hSr ?_ hSl hn
        (matMul_idR (k := n + 1) (n + 1) S hSr hSl hn hn)
      · exact rowsLen_cast (by rw [transposeM_idMat (n + 1), idMat_len])
          (rowsLen_matMul S (idMat (n + 1)))
      · exact (length_matMul S (idMat (n + 1))).trans hSl
    exact ⟨hsq,
      ⟨fun hu => BPair.ofNat_one_off
        (BPair.oneValue_trans (BPair.oneValue_symm hminor) hu),
       hid2, hid2⟩,
      h3, rfl⟩

/-- The block widths at a repeated order-one block: one width per
block, the kernel vacant. -/
private theorem widthOf_replOne (a : BPair) : ∀ o : Nat,
    widthOf (List.replicate o (SBlock.one a)) 0 = o
  | 0 => rfl
  | o + 1 => by
    show widthOf (List.replicate o (SBlock.one a)) (0 + 1) = o + 1
    rw [widthOf_shift (List.replicate o (SBlock.one a)) 0 1,
      widthOf_replOne a o]

/-- The reversal fold over a repeated block at a vacant side is its
own seed. -/
private theorem revFold_replOne (a : BPair) (h : (SBlock.one a).rev = 0) :
    ∀ (o k : Nat),
      (List.replicate o (SBlock.one a)).foldl (fun m b => m + b.rev) k = k
  | 0, _ => rfl
  | o + 1, k => by
    show (List.replicate o (SBlock.one a)).foldl (fun m b => m + b.rev)
        (k + (SBlock.one a).rev) = k
    rw [h]
    exact revFold_replOne a h o k

/-- A repeated block off the sum's unit reads the nonsingularity
fold at the whole list. -/
private theorem allOff_replOne (a : BPair) (h : ¬ a.oneValue BPair.unit) :
    ∀ o : Nat, ((List.replicate o (SBlock.one a)).all
        (fun b => !(decide (b.det.oneValue BPair.unit)))) = true
  | 0 => rfl
  | o + 1 => by
    have hd : decide (a.oneValue BPair.unit) = false := by
      cases hb : decide (a.oneValue BPair.unit) with
      | false => rfl
      | true => exact absurd (of_decide_eq_true hb) h
    show (!(decide (a.oneValue BPair.unit))
      && (List.replicate o (SBlock.one a)).all
        (fun b => !(decide (b.det.oneValue BPair.unit)))) = true
    rw [hd, allOff_replOne a h o]
    rfl

/-- The scalar certificate at a stated order: the identity
congruence with one positive block per key (`lem:inertia`'s
existence clause at the unit gram's scalar copy). -/
def scalarSplit (o : Nat) (c : Pos) : Split o :=
  ⟨⟨idMat o, sqAt_idMat o⟩,
    ⟨idMat o, sqAt_idMat o⟩,
    List.replicate o (SBlock.one (BPair.ofPos c)), 0,
    by rw [widthOf_replOne (BPair.ofPos c) o]; exact ground.beqRefl o⟩

/-- The scalar certificate reads the upper side throughout. -/
theorem scalarSplit_psd (o : Nat) (c : Pos) : psdAt (scalarSplit o c) :=
  revFold_replOne (BPair.ofPos c)
    (rev_one_le (ground.leB_of_lt (ground.unitLtOfPos c))) o 0

/-- The scalar block diagonal's entry: the block's entry at the
diagonal key, the sum's unit off it — the block chart's reads at
the order-one blocks. -/
private theorem blockMat_replOne_entry (a : BPair) : ∀ (o i j : Nat),
    i < o → j < o →
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair)
          (blockMat (List.replicate o (SBlock.one a)) 0) i) j
      = if j = i then a else BPair.unit
  | 0, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | n + 1, 0, 0, _, _ => by
    rw [show List.replicate (n + 1) (SBlock.one a)
        = SBlock.one a :: List.replicate n (SBlock.one a) from rfl,
      blockMat_head (SBlock.one a)
      (List.replicate n (SBlock.one a)) 0 0 0
      Nat.zero_lt_one Nat.zero_lt_one]
    rfl
  | n + 1, 0, j + 1, _, hj => by
    rw [show List.replicate (n + 1) (SBlock.one a)
        = SBlock.one a :: List.replicate n (SBlock.one a) from rfl,
      show j + 1 = (SBlock.one a).order + j from Nat.add_comm j 1,
      blockMat_cross (SBlock.one a)
        (List.replicate n (SBlock.one a)) 0 0 j Nat.zero_lt_one,
      if_neg (fun he : (SBlock.one a).order + j = 0 =>
        Nat.noConfusion ((Nat.add_comm 1 j).symm.trans he))]
  | n + 1, i + 1, 0, hi, _ => by
    rw [show List.replicate (n + 1) (SBlock.one a)
        = SBlock.one a :: List.replicate n (SBlock.one a) from rfl,
      show i + 1 = (SBlock.one a).order + i from Nat.add_comm i 1,
      blockMat_crossT (SBlock.one a)
        (List.replicate n (SBlock.one a)) 0 i 0
        (by rw [widthOf_replOne]; exact Nat.lt_of_succ_lt_succ hi)
        Nat.zero_lt_one,
      if_neg (fun he : (0 : Nat) = (SBlock.one a).order + i =>
        Nat.noConfusion (he.trans (Nat.add_comm 1 i)))]
  | n + 1, i + 1, j + 1, hi, hj => by
    rw [show List.replicate (n + 1) (SBlock.one a)
        = SBlock.one a :: List.replicate n (SBlock.one a) from rfl,
      show i + 1 = (SBlock.one a).order + i from Nat.add_comm i 1,
      show j + 1 = (SBlock.one a).order + j from Nat.add_comm j 1,
      blockMat_tail (SBlock.one a)
        (List.replicate n (SBlock.one a)) 0 i j
        (by rw [widthOf_replOne]; exact Nat.lt_of_succ_lt_succ hi),
      blockMat_replOne_entry a n i j (Nat.lt_of_succ_lt_succ hi)
        (Nat.lt_of_succ_lt_succ hj)]
    by_cases he : j = i
    · rw [if_pos he,
        if_pos (congrArg (fun t => (SBlock.one a).order + t) he)]
    · rw [if_neg he, if_neg (fun hs =>
        he (Nat.succ.inj ((Nat.add_comm 1 j).symm.trans
          (hs.trans (Nat.add_comm 1 i)))))]

/-- The rescaled matrix's entry: the entry's own rescale, at every
key inside the shape. -/
theorem matScale_entry (c : Pos) (M : Mat) (i j : Nat)
    (hi : i < M.length)
    (hj : j < (ground.getAt ([] : List BPair) M i).length) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (matScale c M) i) j
      = (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) M i) j).scale c := by
  show ground.getAt BPair.unit
      (ground.getAt ([] : List BPair)
        (M.map (fun r => r.map (fun x => x.scale c))) i) j = _
  rw [ground.getAt_map ([] : List BPair) ([] : List BPair)
      (fun r => r.map (fun x => x.scale c)) M i hi,
    ground.getAt_map BPair.unit BPair.unit (fun x => x.scale c)
      (ground.getAt ([] : List BPair) M i) j hj]

/-- The scalar copy's entry: the rescaled indicator at the diagonal
key. -/
private theorem matScale_idMat_entry (c : Pos) (o i j : Nat)
    (hi : i < o) (hj : j < o) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (matScale c (idMat o)) i) j
      = (if j = i then BPair.ofNat 1 else BPair.unit).scale c := by
  rw [matScale_entry c (idMat o) i j
      (by rw [idMat_len]; exact hi)
      (by rw [idMat_row o i hi, elim.length_idRow]; exact hj),
    idMat_row o i hi, elim.getAt_idRow o i j hj]

/-- The gram's scalar copy is the scalar certificate's block
diagonal: one positive block per key, the sum's unit off the
diagonal. -/
private theorem blockMat_replicate_one (o : Nat) (c : Pos) :
    matOneValue (matScale c (idMat o))
      (blockMat (List.replicate o (SBlock.one (BPair.ofPos c))) 0) := by
  refine matOne_of_entries _ _ o ?_ ?_ ?_ ?_ ?_
  · rw [length_matScale, idMat_len]
  · exact rowsLen_mapRows (fun x => x.scale c) (idMat o) o (idMat_rows o)
  · rw [blockMat_len, widthOf_replOne]
  · exact rowsLen_cast (widthOf_replOne (BPair.ofPos c) o)
      (blockMat_rows (List.replicate o (SBlock.one (BPair.ofPos c))) 0)
  · intro i j hi hj
    rw [matScale_idMat_entry c o i j hi hj,
      blockMat_replOne_entry (BPair.ofPos c) o i j hi hj]
    by_cases he : j = i
    · rw [if_pos he, if_pos he]
      have hh := BPair.scale_ofPos Pos.one c
      rw [ground.one_mul c] at hh
      exact hh
    · rw [if_neg he, if_neg he]
      show Pos.one * c + Pos.one = Pos.one + Pos.one * c
      exact ground.add_comm (Pos.one * c) Pos.one

/-- A matrix reading the unit gram's scalar copy splits at the scalar
certificate: the identity congruence returns the matrix itself, the
diagonal blocks its entries' read. -/
theorem scalarSplit_read {o : Nat} (c : Pos) (S : Mat)
    (hsq : sqAt S o)
    (h : matOneValue S (matScale c (idMat o))) :
    splitRead S (scalarSplit o c) := by
  cases o with
  | zero =>
    cases S with
    | nil =>
      exact ⟨hsq, ⟨BPair.ofNat_one_off, trivial, trivial⟩, trivial,
        allOff_replOne (BPair.ofPos c) (BPair.ofPos_off c) 0⟩
    | cons r t => exact absurd (sqAt_len hsq) (fun he => Nat.noConfusion he)
  | succ n =>
    have hn : 0 < n + 1 := Nat.succ_pos n
    have hSl : S.length = n + 1 := sqAt_len hsq
    have hSr : rowsLen (n + 1) S := rowsLen_of_sqAt hsq
    have hidl : (idMat (n + 1)).length = n + 1 := idMat_len (n + 1)
    have hminor : (minor (idMat (n + 1))).oneValue (BPair.ofNat 1) :=
      BPair.oneValue_trans
        (minor_detL (idMat (n + 1))
          (rowsLen_cast hidl.symm (idMat_rows (n + 1))))
        (detL_idMat (n + 1))
    have hid2 : matOneValue (matMul (idMat (n + 1)) (idMat (n + 1)))
        (matScaleB (minor (idMat (n + 1))) (idMat (n + 1))) :=
      matOne_trans
        (idMat_matMul (k := n + 1) (n + 1) (idMat (n + 1))
          (idMat_rows (n + 1)) hidl hn)
        (matOne_symm (matOne_trans
          (matScaleB_congr hminor (idMat (n + 1)))
          (matScaleB_one (idMat (n + 1)))))
    have h3 : matOneValue
        (matMul (transposeM (idMat (n + 1))) (matMul S (idMat (n + 1))))
        (blockMat (List.replicate (n + 1) (SBlock.one (BPair.ofPos c))) 0) := by
      rw [transposeM_idMat (n + 1)]
      refine matOne_trans ?_ (blockMat_replicate_one (n + 1) c)
      refine matOne_trans ?_ h
      refine matOne_trans ?_ (idMat_matMul (k := n + 1) (n + 1) S hSr hSl hn)
      refine matMul_congrR (n := n + 1) (k := n + 1) (idMat (n + 1))
        (matMul S (idMat (n + 1))) S ?_ hSr ?_ hSl hn
        (matMul_idR (k := n + 1) (n + 1) S hSr hSl hn hn)
      · exact rowsLen_cast (by rw [transposeM_idMat (n + 1), idMat_len])
          (rowsLen_matMul S (idMat (n + 1)))
      · exact (length_matMul S (idMat (n + 1))).trans hSl
    exact ⟨hsq,
      ⟨fun hu => BPair.ofNat_one_off
        (BPair.oneValue_trans (BPair.oneValue_symm hminor) hu), hid2, hid2⟩,
      h3, allOff_replOne (BPair.ofPos c) (BPair.ofPos_off c) (n + 1)⟩

/-! The diagonal certificate at a stated entry list
(`lem:inertia`'s block-diagonal addition: the splits concatenate to
a split of the block diagonal with the block lists appended and the
kernel orders added, each order-one block reading its entry's side
at the table's own row).  The block table's two small orders keep
their own reads beside it through the exchange. -/

/-- The block widths at an entry list's order-one blocks: one width
per entry, the kernel vacant. -/
private theorem widthOf_mapOne : ∀ ds : List BPair,
    widthOf (ds.map SBlock.one) 0 = ds.length
  | [] => rfl
  | _ :: t => by
    show widthOf (t.map SBlock.one) (0 + 1) = t.length + 1
    rw [widthOf_shift (t.map SBlock.one) 0 1, widthOf_mapOne t]

/-- An entry list off the sum's unit reads the nonsingularity fold
at its order-one blocks, the block's determinant its entry. -/
private theorem allOff_mapOne (ds : List BPair)
    (h : (ds.all (fun d => !(decide (d.oneValue BPair.unit)))) = true) :
    ((ds.map SBlock.one).all
      (fun b => !(decide (b.det.oneValue BPair.unit)))) = true := by
  rw [ground.all_map SBlock.one _ ds]
  exact h

/-- The diagonal identity congruence at a stated entry list: one
order-one block per entry, the kernel vacant. -/
def oneSplit (ds : List BPair) : Split ds.length :=
  ⟨⟨idMat ds.length, sqAt_idMat ds.length⟩,
    ⟨idMat ds.length, sqAt_idMat ds.length⟩,
    ds.map SBlock.one, 0,
    by rw [widthOf_mapOne ds]; exact ground.beqRefl ds.length⟩

/-- A matrix reading an entry list's block diagonal splits at the
diagonal certificate: the identity congruence returns the matrix
itself, the blocks the list's entries at their sides. -/
theorem oneSplit_read (ds : List BPair) (S : Mat)
    (hsq : sqAt S ds.length)
    (h : matOneValue S (blockMat (ds.map SBlock.one) 0))
    (hoff : (ds.all (fun d => !(decide (d.oneValue BPair.unit)))) = true) :
    splitRead S (oneSplit ds) := by
  cases ds with
  | nil =>
    cases S with
    | nil =>
      exact ⟨hsq, ⟨BPair.ofNat_one_off, trivial, trivial⟩, trivial, rfl⟩
    | cons r t => exact absurd (sqAt_len hsq) (fun he => Nat.noConfusion he)
  | cons d t =>
    have hn : 0 < (d :: t).length := Nat.succ_pos t.length
    have hSl : S.length = (d :: t).length := sqAt_len hsq
    have hSr : rowsLen (d :: t).length S := rowsLen_of_sqAt hsq
    have hidl : (idMat (d :: t).length).length = (d :: t).length :=
      idMat_len (d :: t).length
    have hminor : (minor (idMat (d :: t).length)).oneValue (BPair.ofNat 1) :=
      BPair.oneValue_trans
        (minor_detL (idMat (d :: t).length)
          (rowsLen_cast hidl.symm (idMat_rows (d :: t).length)))
        (detL_idMat (d :: t).length)
    have hid2 : matOneValue
        (matMul (idMat (d :: t).length) (idMat (d :: t).length))
        (matScaleB (minor (idMat (d :: t).length))
          (idMat (d :: t).length)) :=
      matOne_trans
        (idMat_matMul (k := (d :: t).length) (d :: t).length
          (idMat (d :: t).length) (idMat_rows (d :: t).length) hidl hn)
        (matOne_symm (matOne_trans
          (matScaleB_congr hminor (idMat (d :: t).length))
          (matScaleB_one (idMat (d :: t).length))))
    have h3 : matOneValue
        (matMul (transposeM (idMat (d :: t).length))
          (matMul S (idMat (d :: t).length)))
        (blockMat ((d :: t).map SBlock.one) 0) := by
      rw [transposeM_idMat (d :: t).length]
      refine matOne_trans ?_ h
      refine matOne_trans ?_
        (idMat_matMul (k := (d :: t).length) (d :: t).length S hSr hSl hn)
      refine matMul_congrR (n := (d :: t).length) (k := (d :: t).length)
        (idMat (d :: t).length) (matMul S (idMat (d :: t).length)) S ?_ hSr ?_
        hSl hn
        (matMul_idR (k := (d :: t).length) (d :: t).length S hSr hSl hn hn)
      · exact rowsLen_cast
          (by rw [transposeM_idMat (d :: t).length, idMat_len])
          (rowsLen_matMul S (idMat (d :: t).length))
      · exact (length_matMul S (idMat (d :: t).length)).trans hSl
    exact ⟨hsq,
      ⟨fun hu => BPair.ofNat_one_off
        (BPair.oneValue_trans (BPair.oneValue_symm hminor) hu), hid2, hid2⟩,
      h3, allOff_mapOne (d :: t) hoff⟩

/-- The diagonal certificate's reversal count is the entry list's
own side fold. -/
theorem revAt_oneSplit (ds : List BPair) :
    revAt (oneSplit ds) = ds.foldl (fun m d => m + (SBlock.one d).rev) 0 :=
  ground.foldl_map SBlock.one (fun m b => m + b.rev) ds 0

/-- The order-two identity congruence at a stated symmetric block,
the datum's own block diagonal. -/
private def twoSplitAt (a b c : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two a b c], 0, rfl⟩

/-- The order-two identity congruence reads the symmetric two-entry
datum. -/
private theorem twoSplitAt_read {a b c : BPair}
    (hdet : ¬ ((SBlock.two a b c).det).oneValue BPair.unit) :
    splitRead [[a, b], [b, c]] (twoSplitAt a b c) := by
  refine ⟨rfl, ⟨BPair.ofNat_one_off, matOne_refl _, matOne_refl _⟩,
    ?_, ?_⟩
  · have hr : rowsLen 2 (matMul [[a, b], [b, c]] (idMat 2)) :=
      rowsLen_cast (transposeLen (idMat 2) (idMat_rows 2) (idMat_len 2))
        (rowsLen_matMul [[a, b], [b, c]] (idMat 2))
    have hl : (matMul [[a, b], [b, c]] (idMat 2)).length = 2 :=
      (length_matMul [[a, b], [b, c]] (idMat 2)).trans rfl
    show matOneValue (matMul (transposeM (idMat 2))
      (matMul [[a, b], [b, c]] (idMat 2)))
      (blockMat [SBlock.two a b c] 0)
    rw [transposeM_idMat 2]
    exact matOne_trans
      (idMat_matMul (k := 2) 2 _ hr hl (Nat.succ_pos 1))
      (show matOneValue (matMul [[a, b], [b, c]] (idMat 2))
          (blockMat [SBlock.two a b c] 0) from
        matMul_idR (k := 2) 2 [[a, b], [b, c]] ⟨rfl, rfl, trivial⟩ rfl
          (Nat.succ_pos 1) (Nat.succ_pos 1))
  · show (!(decide (((SBlock.two a b c).det).oneValue BPair.unit))
      && true) = true
    rw [decide_eq_false hdet]
    rfl

/-- Every split of a one-entry datum off the unit reads the entry's
side, the block table's order-one row. -/
theorem rev_one {d : BPair} (hd : ¬ d.oneValue BPair.unit)
    (sp : Split 1) (h : splitRead [[d]] sp) :
    revAt sp = (SBlock.one d).rev := by
  rw [rev_exchange [[d]] sp (oneSplit [d]) h
    (oneSplit_read [d] [[d]] rfl (matOne_refl _)
      (show (!(decide (d.oneValue BPair.unit)) && true) = true by
        rw [decide_eq_false hd]; rfl)),
    revAt_oneSplit [d]]
  show 0 + (SBlock.one d).rev = (SBlock.one d).rev
  exact Nat.zero_add _

/-- Every split of a symmetric two-entry datum of unequal-membered
determinant reads the block table: one unit per side at the
determinant's lower side, the diagonal's shared side at the
upper. -/
theorem rev_two {a b b' c : BPair} (hb : b'.oneValue b)
    (hdet : ¬ ((SBlock.two a b c).det).oneValue BPair.unit)
    (sp : Split 2) (h : splitRead [[a, b], [b', c]] sp) :
    revAt sp = (SBlock.two a b c).rev := by
  have h' : splitRead [[a, b], [b, c]] sp :=
    splitRead_congr (n := 2) [[a, b], [b', c]] [[a, b], [b, c]] rfl
      ⟨⟨BPair.oneValue_refl a, BPair.oneValue_refl b, trivial⟩,
       ⟨hb, BPair.oneValue_refl c, trivial⟩, trivial⟩ sp h
  rw [rev_exchange [[a, b], [b, c]] sp (twoSplitAt a b c) h'
    (twoSplitAt_read hdet)]
  show 0 + (SBlock.two a b c).rev = (SBlock.two a b c).rev
  exact Nat.zero_add _

/-- lem:inertia's existence clause: the split the leftmost
admissible pivot's descent closes, one pivot of order at most two
per step with the deflation beneath it, the kernel block the
descent's remainder. -/
def mkSplit (n : Nat) (S : Mat) : Split n :=
  if h : sqAt (transposeM (mkVGo n n S).1) n
      ∧ sqAt (adjM (transposeM (mkVGo n n S).1)) n
      ∧ Nat.beq (widthOf (mkVGo n n S).2.1 (mkVGo n n S).2.2) n = true then
    ⟨⟨transposeM (mkVGo n n S).1, h.1⟩,
      ⟨adjM (transposeM (mkVGo n n S).1), h.2.1⟩,
      (mkVGo n n S).2.1, (mkVGo n n S).2.2, h.2.2⟩
  else unitSplit n

/-- The construction's value at a passing shape read. -/
private theorem mkSplit_val (n : Nat) (S : Mat)
    (h : sqAt (transposeM (mkVGo n n S).1) n
      ∧ sqAt (adjM (transposeM (mkVGo n n S).1)) n
      ∧ Nat.beq (widthOf (mkVGo n n S).2.1 (mkVGo n n S).2.2) n = true) :
    mkSplit n S = ⟨⟨transposeM (mkVGo n n S).1, h.1⟩,
      ⟨adjM (transposeM (mkVGo n n S).1), h.2.1⟩,
      (mkVGo n n S).2.1, (mkVGo n n S).2.2, h.2.2⟩ := dif_pos h

/-- A certificate's column list closes the split read at an
occupied order. -/
private theorem splitRead_of_VGood (n : Nat) (hn : 0 < n) (S V : Mat)
    (bs : List SBlock) (kn : Nat) (hS : sqAt S n)
    (hw : widthOf bs kn = n)
    (hall : (bs.all (fun b => !(decide (b.det.oneValue BPair.unit)))) = true)
    (hg : VGood S V (blockMat bs kn) n)
    (hT : sqAt (transposeM V) n) (hA : sqAt (adjM (transposeM V)) n)
    (hbeq : Nat.beq (widthOf bs kn) n = true) :
    splitRead S
      (⟨⟨transposeM V, hT⟩, ⟨adjM (transposeM V), hA⟩, bs, kn, hbeq⟩ :
        Split n) := by
  have hSl : S.length = n := sqAt_len hS
  have hVl : V.length = n := sqAt_len hg.1
  have hVr : rowsLen n V := rowsLen_of_sqAt hg.1
  have hTT : transposeM (transposeM V) = V :=
    transposeM_transposeM V hVr hn (by rw [hVl]; exact hn)
  have hdT : ¬ (detL (transposeM V)).oneValue BPair.unit := by
    rw [detL_transpose V (by rw [hVl]; exact hVr)]
    exact hg.2.1
  refine ⟨hS, cleared_adjM (transposeM V) n hn hT hdT, ?_, hall⟩
  show matOneValue (matMul (transposeM (transposeM V))
    (matMul S (transposeM V))) (blockMat bs kn)
  rw [hTT]
  exact congr_of_gramAt S V (blockMat bs kn) n hn hSl hVl hVr
    ((blockMat_len bs kn).trans hw) (rowsLen_cast hw (blockMat_rows bs kn))
    hg.2.2

/-- The constructed split reads its datum: every symmetric square
datum has a split, the construction's own read. -/
theorem mkSplit_read (n : Nat) (S : Mat) (hS : sqAt S n)
    (hsym : matOneValue (transposeM S) S) :
    splitRead S (mkSplit n S) := by
  have hSl : S.length = n := sqAt_len hS
  have hSr : rowsLen n S := rowsLen_of_sqAt hS
  have hread := mkVGo_read n n S (Nat.le_refl n) hS
    (pairSymAt_of S n hSl hSr hsym)
  have hVsq : sqAt (mkVGo n n S).1 n := hread.2.2.1
  have hVl : (mkVGo n n S).1.length = n := sqAt_len hVsq
  have hVr : rowsLen n (mkVGo n n S).1 := rowsLen_of_sqAt hVsq
  have hTl : (transposeM (mkVGo n n S).1).length = n :=
    transposeLen _ hVr hVl
  have hTsq : sqAt (transposeM (mkVGo n n S).1) n :=
    sqAt_of hTl (rowsLen_cast hVl (rowsLen_transposeM _))
  cases n with
  | zero =>
    have hAsq : sqAt (adjM (transposeM (mkVGo 0 0 S).1)) 0 := rfl
    have hbeq : Nat.beq (widthOf (mkVGo 0 0 S).2.1 (mkVGo 0 0 S).2.2) 0
        = true := rfl
    rw [mkSplit_val 0 S ⟨hTsq, hAsq, hbeq⟩]
    exact ⟨hS, ⟨BPair.ofNat_one_off, trivial, trivial⟩, trivial, rfl⟩
  | succ n0 =>
    have hAsq : sqAt (adjM (transposeM (mkVGo (n0 + 1) (n0 + 1) S).1))
        (n0 + 1) :=
      sqAt_adjM _ (n0 + 1) (Nat.succ_pos n0) hTsq
    have hbeq : Nat.beq (widthOf (mkVGo (n0 + 1) (n0 + 1) S).2.1
        (mkVGo (n0 + 1) (n0 + 1) S).2.2) (n0 + 1) = true := by
      rw [hread.1]
      exact ground.beqRefl (n0 + 1)
    rw [mkSplit_val (n0 + 1) S ⟨hTsq, hAsq, hbeq⟩]
    exact splitRead_of_VGood (n0 + 1) (Nat.succ_pos n0) S
      (mkVGo (n0 + 1) (n0 + 1) S).1 _ _ hS hread.1 hread.2.1 hread.2.2
      hTsq hAsq hbeq

end inertia
