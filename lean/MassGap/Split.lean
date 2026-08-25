import MassGap.Inertia
/-!
`lem:split` — the pencil's split: the level pair's site datum as a
polynomial matrix `Z(x)` at `x G = H + Z(x)` (`zMat`, entries
degree one), its determinant the pencil polynomial `χ` (`charPoly`,
the first-row fold at polynomial entries, `pminor`, whose value a
joint relabeling of the row and the column keys leaves at one
value — `pminor_reindex`, `thm:restoration`'s derivation clause at
this carrier), the
factorization read `χ = det G · Π ⟨x : ε_j⟩` at a stated root list
cleared to pair data (`chiRead`, `linFac` the cleared linear
factor), the count identity `count(a) = #{j : ε_j < a}` at the
split certificate (`countRead` at `rootsBelow`, the display's read
against `lem:inertia`'s count), and the diagonalizing congruence
`S_χᵀ Z(x) S_χ = diag(⟨x : ε_j⟩ g_j)` at `g_j` on their upper
sides (`diagRead`, the congruence cleared to the integer carrier
with the scales absorbing the clearing, the invertibility its own
carried witness — the adjugate at the same carrier with the two
product reads against the determinant), the completed congruence
returning the factorization read (`diag_chiRead`, the identity's
two determinants collecting to the descent's own squared against
the diagonal blocks' product with the shared factor withdrawn off
the unit congruence).  The completed certificate carries the
coefficient tier: the degree-one entries' two scalar
matrices (`pconst`, `plin`), the congruence identity's split into
`Tᵀ G T` and `Tᵀ H T`'s memberwise swap against the diagonals at
the scaled root data (`diagM`), and the eigen-column capstone —
the congruence's own column at a stated root the pencil's
eigendirection there, `d_j (H v_j) = n_j (G v_j)` cleared
(`eigenColumn` at the indicator `elim.idRow`).  The resultant's kernel
read arrives at this
arithmetic (`crossRead`): a kernel vector's cross pair `(A, B)` at
the stated degrees with `A p` the balance partner of `B q`, the
resultant reading equal members exactly at an occupied cross pair,
`elim.bezout_all`'s clause its coprime complement.  The stage-rooted
splits at
stored towers — the deflation's kernel lists over the extensions —
are the emitted certificates' tier at their recorded consumers
(`thm:decimation`'s presentation, `thm:SO`'s multiplicity), the
rational tier's reads the displays below.  The statement's site is
a positive-definite gram, the `pdAt` split of `G`'s own datum the
site's read, the committed batteries at
the unit gram.
-/

namespace split
open ground poly elim inertia

/-- A polynomial matrix, the rows' coefficient-list entries. -/
abbrev PMat := List (List Poly)

/-- The first-row fold at polynomial entries, the representative
map entrywise with the collected sum untouched. -/
def pminor (m : PMat) : Poly := elim.minorO polyOps poly.pnorm id m

/-- The symbol's determinant at a joint relabeling of rows and
columns, the derivation clause at the polynomial carrier
(`thm:restoration`'s congruence at `def:elim`'s exchanged
reads). -/
theorem pminor_reindex (n : Nat) (Z Z' : PMat) (q : List Nat)
    (hq : 0 < ground.countOf q
      (places.monomialsAt (List.replicate n 1)))
    (hZ : Z.length = n) (hZ' : Z'.length = n)
    (hrows : elim.rowsLen n Z) (hrows' : elim.rowsLen n Z')
    (hent : ∀ i j, i < n → j < n →
      poly.oneValue (ground.getAt [] (ground.getAt [] Z' i) j)
        (ground.getAt []
          (ground.getAt [] Z (ground.getAt 0 q i))
          (ground.getAt 0 q j))) :
    poly.oneValue (pminor Z') (pminor Z) :=
  elim.minorP_reindex n Z Z' q hq hZ hZ' hrows hrows' hent

/-- The level pair's site datum as a polynomial matrix:
`Z(x) = x G - H` entrywise, degree one. -/
def zMat (H G : Mat) : PMat :=
  List.zipWith (List.zipWith (fun h g => [BPair.swap h, g])) H G

/-- The site datum's row count is the level pair's own. -/
theorem zMat_len : ∀ (H G : Mat) (n : Nat),
    H.length = n → G.length = n → (zMat H G).length = n
  | [], _, _, h, _ => h
  | _ :: _, [], _, _, hg => hg
  | _ :: H, _ :: G, n, hH, hG => by
    match n, hH, hG with
    | n' + 1, hH, hG =>
      show (zMat H G).length + 1 = n' + 1
      rw [zMat_len H G n' (Nat.succ.inj hH) (Nat.succ.inj hG)]

/-- The pencil polynomial `χ`, the site datum's determinant. -/
def charPoly (H G : Mat) : Poly := pminor (zMat H G)

/-- The cleared linear factor `d x - n` at a root's pair data. -/
def linFac (n : BPair) (d : Pos) : Poly := [BPair.swap n, BPair.ofPos d]

/-- The factorization read at a stated root list:
`χ = det G · Π ⟨x : ε_j⟩` cleared at the roots' second members. -/
def chiRead (H G : Mat) (roots : List (BPair × Pos)) : Prop :=
  poly.oneValue
    (poly.mul [BPair.ofPos (roots.foldl (fun a r => a * r.2) Pos.one)]
      (charPoly H G))
    (poly.mul [minor G]
      (poly.prodFold (roots.map (fun r => linFac r.1 r.2))))

/-- The factorization read transports to the descent's reads at
square frames: both determinants are reads of the value, the
pencil's at `pdetD` and the frame's at `detD`. -/
private theorem chiRead_walk (H G : Mat) (roots : List (BPair × Pos))
    (hZ : elim.rowsLen (zMat H G).length (zMat H G))
    (hG : elim.rowsLen G.length G) :
    chiRead H G roots ↔
    poly.oneValue
      (poly.mul
        [BPair.ofPos (roots.foldl (fun a r => a * r.2) Pos.one)]
        (elim.pdetD (zMat H G)))
      (poly.mul [elim.detD G]
        (poly.prodFold (roots.map (fun r => linFac r.1 r.2)))) := by
  have hL : poly.oneValue (elim.pdetD (zMat H G)) (charPoly H G) :=
    elim.pdetD_eq (zMat H G) hZ
  have hB : (elim.detD G).oneValue (minor G) :=
    BPair.oneValue_trans (elim.detD_eq G hG)
      (BPair.oneValue_symm (elim.minor_detL G hG))
  have h1 : poly.oneValue
      (poly.mul
        [BPair.ofPos (roots.foldl (fun a r => a * r.2) Pos.one)]
        (elim.pdetD (zMat H G)))
      (poly.mul
        [BPair.ofPos (roots.foldl (fun a r => a * r.2) Pos.one)]
        (charPoly H G)) :=
    poly.mul_congr _ hL
  have hS : poly.oneValue [elim.detD G] [minor G] := ⟨hB, trivial⟩
  have h2 : poly.oneValue
      (poly.mul [elim.detD G]
        (poly.prodFold (roots.map (fun r => linFac r.1 r.2))))
      (poly.mul [minor G]
        (poly.prodFold (roots.map (fun r => linFac r.1 r.2)))) :=
    poly.mul_congr_left hS _
  constructor
  · intro h
    exact poly.oneValue_trans h1
      (poly.oneValue_trans h (poly.oneValue_symm h2))
  · intro h
    exact poly.oneValue_trans (poly.oneValue_symm h1)
      (poly.oneValue_trans h h2)

instance (H G : Mat) (roots : List (BPair × Pos)) :
    Decidable (chiRead H G roots) :=
  match elim.decRowsLen (zMat H G).length (zMat H G),
        elim.decRowsLen G.length G with
  | isTrue hZ, isTrue hG =>
    decidable_of_iff _ (chiRead_walk H G roots hZ hG).symm
  | isFalse _, isTrue _ => poly.decOneValue _ _
  | isFalse _, isFalse _ => poly.decOneValue _ _
  | isTrue _, isFalse _ => poly.decOneValue _ _

/-- The roots at levels below a pair, the count's display. -/
def rootsBelow (roots : List (BPair × Pos)) (an ad : Pos) : Nat :=
  roots.countP (fun r =>
    decide (r.1.scale ad < BPair.ofPos (an * r.2)))

/-- The roots at the kernel point, the ground multiplicity's own
display over the located root list. -/
def rootsAtKernel (roots : List (BPair × Pos)) : Nat :=
  roots.countP (fun r => decide (r.1.oneValue BPair.unit))

/-- A first-factor comparison keeps under a common second factor. -/
private theorem posLeMul {a b : Pos} (c : Pos) (h : a ≤ b) :
    a * c ≤ b * c :=
  match h with
  | Or.inl e => Or.inl (congrArg (· * c) e)
  | Or.inr ⟨g, hg⟩ => Or.inr ⟨g * c, by
      rw [← ground.right_distrib a g c, hg]⟩

/-- The one-member site keeps the ground order. -/
private theorem ofPosLe {a b : Pos} (h : a ≤ b) :
    BPair.ofPos a ≤ BPair.ofPos b :=
  match h with
  | Or.inl e => Or.inl (BPair.oneValue_of_eq (congrArg BPair.ofPos e))
  | Or.inr ⟨g, hg⟩ => Or.inr ⟨g, by
      show a + Pos.one + Pos.one + g = b + Pos.one + Pos.one
      rw [ground.add_right_comm (a + Pos.one) Pos.one g,
        ground.add_right_comm a Pos.one g, hg]⟩

/-- The below count is monotone in its level: a level at or below a
second at the cross-multiplied comparison counts at or below it. -/
theorem rootsBelow_mono (roots : List (BPair × Pos))
    (an ad an' ad' : Pos) (h : an * ad' ≤ an' * ad) :
    rootsBelow roots an ad ≤ rootsBelow roots an' ad' := by
  show roots.countP _ ≤ roots.countP _
  rw [ground.countP_read, ground.countP_read]
  refine ground.countBy_mono _ _ (fun r hr => ?_) roots
  refine decide_eq_true ?_
  have hlt : r.1.scale ad < BPair.ofPos (an * r.2) :=
    of_decide_eq_true hr
  have h1 := ground.BPair.scale_lt ad' hlt
  rw [ground.BPair.scale_scale] at h1
  have h2 : r.1.scale (ad * ad') < BPair.ofPos (an * r.2 * ad') :=
    ground.ltB_trans_le h1
      (Or.inl (ground.BPair.scale_ofPos (an * r.2) ad'))
  have h3 : an * r.2 * ad' ≤ an' * r.2 * ad := by
    rw [ground.mul_assoc an r.2 ad', ground.mul_comm r.2 ad',
      ← ground.mul_assoc an ad' r.2,
      ground.mul_assoc an' r.2 ad, ground.mul_comm r.2 ad,
      ← ground.mul_assoc an' ad r.2]
    exact posLeMul r.2 h
  have h4 : r.1.scale (ad * ad') < BPair.ofPos (an' * r.2 * ad) :=
    ground.ltB_trans_le h2 (ofPosLe h3)
  have h5 : (r.1.scale ad').scale ad
      < (BPair.ofPos (an' * r.2)).scale ad := by
    rw [ground.BPair.scale_scale, ground.mul_comm ad' ad]
    exact ground.ltB_trans_le h4
      (Or.inl (ground.BPair.oneValue_symm
        (ground.BPair.scale_ofPos (an' * r.2) ad)))
  exact ground.BPair.lt_of_scale_lt h5

/-- The count identity at the split certificate:
`count(a) = #{j : ε_j < a}` at a level off the roots — the
off-roots clause a conjunct — the reversal count against the
located roots' display. -/
def countRead {o : Nat} (H G : Mat) (roots : List (BPair × Pos))
    (an ad : Pos) (sp : Split o) : Prop :=
  sqAt H o ∧ sqAt G o
  ∧ chiRead H G roots
  ∧ (roots.all (fun r =>
      !(decide ((r.1.scale ad).oneValue (BPair.ofPos (an * r.2)))))) = true
  ∧ splitRead (siteDatum (matScale ad H) (matScale an G)) sp
  ∧ revAt sp = rootsBelow roots an ad

instance {o : Nat} (H G : Mat) (roots : List (BPair × Pos))
    (an ad : Pos) (sp : Split o) :
    Decidable (countRead H G roots an ad sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ = _ ∧ _ ∧ _ = _))

private def pheads (m : PMat) : List Poly :=
  m.map (fun r =>
    match r with
    | [] => []
    | a :: _ => a)

private def ptails (m : PMat) : PMat :=
  m.map (fun r =>
    match r with
    | [] => []
    | _ :: t => t)

private def ptransGo : Nat → PMat → PMat
  | 0, _ => []
  | n + 1, m => pheads m :: ptransGo n (ptails m)

private def ptranspose (m : PMat) : PMat :=
  ptransGo
    (match m with
     | [] => 0
     | r :: _ => r.length) m

/-- The congruence at the site datum's polynomial matrix:
`Tᵀ Z T` at scalar `T`, the entries' folds. -/
def congrZ (T : Mat) (Z : PMat) : PMat :=
  let Tt := transposeM T
  let ZT : PMat := Z.map (fun r => Tt.map (fun c => poly.scaleDot c r))
  let ZTt := ptranspose ZT
  Tt.map (fun ti => ZTt.map (fun colj => poly.scaleDot ti colj))

/-- The diagonal polynomial matrix at stated entries, the off keys
at the sum's unit. -/
def pdiag (ds : List Poly) : PMat := elim.diagO poly.polyOps ds

/-- The polynomial-matrix product, the entries' polynomial folds
(`lem:genericlift`'s adjugate solve and `lem:spectator`'s
factorization the consumers). -/
def pmatMul (a b : PMat) : PMat := elim.matMulO poly.polyOps a b

/-- The polynomial matrices' entrywise sum. -/
def pmatAdd (A B : PMat) : PMat := elim.matAddO poly.polyOps A B

/-- The entrywise memberwise swap. -/
def pswapM (S : PMat) : PMat := elim.matSwapO poly.polyOps S

/-- The entrywise rescaling at a stated polynomial. -/
def pscaleM (f : poly.Poly) (S : PMat) : PMat := S.map (fun r => r.map (poly.mul f))

/-- The selected block at stated row and column key lists. -/
def pselM (I J : List Nat) (S : PMat) : PMat :=
  elim.selMO ([] : poly.Poly) I J S

/-- The selected block's row count is the row key list's. -/
theorem length_pselM (I J : List Nat) (S : PMat) :
    (pselM I J S).length = I.length :=
  elim.length_selMO ([] : poly.Poly) I J S

/-- The selected block's rows read the column key list's count. -/
theorem rowsLen_pselM (J : List Nat) (S : PMat) (I : List Nat) :
    elim.rowsLen J.length (pselM I J S) :=
  elim.rowsLen_selMO ([] : poly.Poly) J S I

/-- The selected block's entry at two keys is the datum's at the
selected keys. -/
theorem getAt_pselM (I J : List Nat) (S : PMat) (p q : Nat)
    (hp : p < I.length) (hq : q < J.length) :
    ground.getAt ([] : poly.Poly)
        (ground.getAt ([] : List poly.Poly) (pselM I J S) p) q
      = ground.getAt ([] : poly.Poly)
          (ground.getAt ([] : List poly.Poly) S (ground.getAt 0 I p))
          (ground.getAt 0 J q) :=
  elim.getAt_selMO ([] : poly.Poly) I J S p q hp hq

/-- The symmetry read at a stated order, entry against exchanged
entry over the key square. -/
def pSymAt (S : PMat) (o : Nat) : Prop :=
  ((List.range o).all (fun i => (List.range o).all (fun j =>
    decide (poly.oneValue
      (ground.getAt ([] : poly.Poly) (ground.getAt [] S i) j)
      (ground.getAt ([] : poly.Poly) (ground.getAt [] S j) i))))) = true

instance (S : PMat) (o : Nat) : Decidable (pSymAt S o) :=
  inferInstanceAs (Decidable (_ = _))

/-- Two polynomial rows read one value entrywise over shared key
lists — the matrix read's own recursion at the coefficient rows
(`elim.matOneValue`, one carrier). -/
def prowOneValue : List Poly → List Poly → Prop := elim.matOneValue

def decProwOneValue : ∀ a b, Decidable (prowOneValue a b) :=
  elim.decMatOneValue

instance (a b : List Poly) : Decidable (prowOneValue a b) :=
  decProwOneValue a b

/-- Two polynomial matrices read one value entrywise. -/
def pmatOneValue : PMat → PMat → Prop :=
  ground.matchedOV (ground.matchedRead poly.polyRead)

def decPmatOneValue : ∀ a b, Decidable (pmatOneValue a b) :=
  ground.decMatchedOV (ground.matchedRead poly.polyRead)

instance (a b : PMat) : Decidable (pmatOneValue a b) :=
  decPmatOneValue a b

/-- A polynomial row reads itself. -/
theorem prowOne_refl : ∀ r : List Poly, prowOneValue r r :=
  ground.matched_refl (fun p => poly.oneValue_refl p)

/-- A polynomial matrix reads itself. -/
theorem pmatOne_refl : ∀ S : PMat, pmatOneValue S S :=
  ground.matched_refl (fun r => prowOne_refl r)

/-- The diagonalizing congruence's read: `S_χᵀ Z(x) S_χ` reads the
diagonal `⟨x : ε_j⟩ g_j` at the scales on their upper sides, the
congruence entering cleared at the integer carrier
(`inertia.clearedCongr`). -/
def diagRead {o : Nat} (H G : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair)) : Prop :=
  sqAt H o ∧ sqAt G o
  ∧ inertia.clearedCongr T Tw
  ∧ pmatOneValue (congrZ T.val (zMat H G))
      (pdiag (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))))
  ∧ (l.all (fun r => decide (BPair.unit < r.2.2))) = true

instance {o : Nat} (H G : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair)) :
    Decidable (diagRead H G T Tw l) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ = _))

/-! The certificate's coefficient tier: the pencil's entries are
degree one, so a polynomial matrix carries two scalar matrices — the
constant and the linear coefficient reads, the entries at the two keys
with the sum's unit beyond a top — and the congruence identity splits
into their two.  The congruence's linear coefficient is the site's
second datum congruated (`Tᵀ G T`) and its constant the first's with
the pencil's own sign (`Tᵀ H T`'s memberwise swap), while the diagonal
side's two are the diagonals at the scaled root data; the capstone
reads the congruence's columns as the pencil's eigendirections at the
cleared roots, the root's two members clearing `H` against `G` at one
column. -/

/-! The one-value kit at the two carriers: the matrix read's
symmetry and transitivity, the row-read introduction, and the
product and diagonal congruences at the entry bundle's
instances. -/

/-- The matrix read is symmetric. -/
theorem pmatOne_symm {A B : PMat} : pmatOneValue A B → pmatOneValue B A :=
  ground.matched_symm (fun h => elim.matOne_symm h)

/-- The matrix read is transitive. -/
theorem pmatOne_trans {A B C : PMat} : pmatOneValue A B →
    pmatOneValue B C → pmatOneValue A C :=
  ground.matched_trans (fun h1 h2 => elim.matOne_trans h1 h2)

/-- The matrix read enters from its row reads at matched counts. -/
theorem pmatOne_ofGetAt {A B : PMat} (hl : A.length = B.length)
    (h : ∀ k, k < A.length →
      prowOneValue (ground.getAt [] A k) (ground.getAt [] B k)) :
    pmatOneValue A B :=
  ground.matched_ofGetAt [] hl h

/-- The product moves across its second factor's read, entry by
entry through the folds. -/
theorem pmatMul_congr_right {X Y : PMat} (hXY : pmatOneValue X Y) :
    ∀ a : PMat, pmatOneValue (pmatMul a X) (pmatMul a Y) :=
  elim.matMulO_congr_right poly.polyOps poly.polyRead
    (poly.oneValue_refl [])
    (fun {_ _ _ _} h1 h2 => poly.add_congr h1 h2)
    (fun x {_ _} h => poly.mul_congr x h) hXY

/-- The replicated diagonal moves across its entry's read. -/
theorem pdiag_repl_congr {p q : Poly} (h : poly.oneValue p q)
    (n : Nat) :
    pmatOneValue (pdiag (List.replicate n p))
      (pdiag (List.replicate n q)) :=
  elim.diagO_repl_congr poly.polyOps poly.polyRead
    (poly.oneValue_refl []) h n

/-! The coefficient readers: the entries at a stated key, the sum's
unit beyond a top. -/

private def cf (k : Nat) (p : Poly) : BPair := ground.getAt BPair.unit p k

private def pcf (k : Nat) (m : PMat) : Mat := m.map (fun r => r.map (cf k))

/-- The constant-coefficient matrix of a polynomial matrix, the
entries at the sum's own key. -/
def pconst (m : PMat) : Mat :=
  m.map (fun r => r.map (fun p => ground.getAt BPair.unit p 0))

/-- The linear-coefficient matrix of a polynomial matrix, the entries
at the first key. -/
def plin (m : PMat) : Mat :=
  m.map (fun r => r.map (fun p => ground.getAt BPair.unit p 1))

private theorem pconst_pcf (m : PMat) : pconst m = pcf 0 m := rfl

private theorem plin_pcf (m : PMat) : plin m = pcf 1 m := rfl

/-- The diagonal at stated entries, the off keys at the sum's unit. -/
def diagM (ds : List BPair) : Mat := elim.diagO ground.bpairOps ds

private theorem rowGetAt : ∀ (r s : List Poly), prowOneValue r s →
    ∀ k : Nat, poly.oneValue (r.map (cf k)) (s.map (cf k))
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | _ :: r, _ :: s, h, k => ⟨poly.oneValue_getAt k h.1, rowGetAt r s h.2 k⟩

private theorem pcfOne : ∀ (a b : PMat), pmatOneValue a b →
    ∀ k : Nat, matOneValue (pcf k a) (pcf k b)
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | _ :: a, _ :: b, h, k => ⟨rowGetAt _ _ h.1 k, pcfOne a b h.2 k⟩

/-! The polynomial operations' coefficient reads: the sum adds, the
scale multiplies, and the row fold is the coefficients' own fold. -/

private theorem cf_add : ∀ (p q : Poly) (k : Nat),
    (cf k (poly.add p q)).oneValue (cf k p + cf k q)
  | [], q, k => BPair.oneValue_symm (BPair.unit_add (cf k q))
  | _ :: _, [], k => BPair.oneValue_symm (BPair.add_unit (cf k _))
  | _ :: _, _ :: _, 0 => BPair.oneValue_refl _
  | _ :: p, _ :: q, k + 1 => cf_add p q k

private theorem cf_scaleP : ∀ (c : BPair) (p : Poly) (k : Nat),
    (cf k (poly.scaleP c p)).oneValue (c * cf k p)
  | c, [], _ => BPair.oneValue_symm (BPair.mul_unit c)
  | _, _ :: _, 0 => BPair.norm_oneValue _
  | c, _ :: t, k + 1 => cf_scaleP c t k

private theorem cf_scaleDot : ∀ (cs : List BPair) (ps : List Poly) (k : Nat),
    (cf k (poly.scaleDot cs ps)).oneValue (dotP (ps.map (cf k)) cs)
  | [], [], _ => BPair.oneValue_refl _
  | [], _ :: _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ => BPair.oneValue_refl _
  | c :: cs, p :: ps, k => by
    refine BPair.oneValue_trans
      (cf_add (poly.scaleP c p) (poly.scaleDot cs ps) k) ?_
    show ((cf k (poly.scaleP c p)) + cf k (poly.scaleDot cs ps)).oneValue
      (cf k p * c + dotP (ps.map (cf k)) cs)
    exact BPair.add_congr
      (BPair.oneValue_trans (cf_scaleP c p k)
        (BPair.oneValue_of_eq (BPair.mul_comm c (cf k p))))
      (cf_scaleDot cs ps k)

/-! The polynomial transpose's entry read and the fold's row read, the
congruence's coefficient split beneath them. -/

private theorem getAt_ptransGo :
    ∀ (n : Nat) (m : PMat) (p q : Nat), p < n → q < m.length →
      ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly) (ptransGo n m) p) q
        = ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly) m q) p
  | 0, _, p, _, hp, _ => absurd hp (Nat.not_lt_zero p)
  | _ + 1, m, 0, q, _, hq => by
    show ground.getAt ([] : Poly) (pheads m) q = _
    rw [show pheads m = m.map (fun r =>
        match r with
        | [] => ([] : Poly)
        | a :: _ => a) from rfl,
      ground.getAt_map ([] : List Poly) ([] : Poly) _ m q hq]
    match ground.getAt ([] : List Poly) m q with
    | [] => rfl
    | _ :: _ => rfl
  | n + 1, m, p + 1, q, hp, hq => by
    show ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (ptransGo n (ptails m)) p) q = _
    have hqt : q < (ptails m).length := by
      rw [show (ptails m).length = m.length from ground.length_map _ m]
      exact hq
    rw [getAt_ptransGo n (ptails m) p q (Nat.lt_of_succ_lt_succ hp) hqt,
      show ground.getAt ([] : List Poly) (ptails m) q
          = (match ground.getAt ([] : List Poly) m q with
             | [] => []
             | _ :: t => t) from
        ground.getAt_map ([] : List Poly) ([] : List Poly) _ m q hq]
    match ground.getAt ([] : List Poly) m q with
    | [] => rfl
    | _ :: _ => rfl

private theorem length_ptransGo : ∀ (n : Nat) (m : PMat),
    (ptransGo n m).length = n
  | 0, _ => rfl
  | n + 1, m => congrArg Nat.succ (length_ptransGo n (ptails m))

private theorem rowsLen_ptransGo : ∀ (n : Nat) (m : PMat) (w : Nat),
    m.length = w → ∀ p, p < n →
      (ground.getAt ([] : List Poly) (ptransGo n m) p).length = w
  | 0, _, _, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | _ + 1, m, w, hw, 0, _ => by
    show (pheads m).length = w
    rw [show (pheads m).length = m.length from ground.length_map _ m]
    exact hw
  | n + 1, m, w, hw, p + 1, hp => by
    show (ground.getAt ([] : List Poly) (ptransGo n (ptails m)) p).length
      = w
    exact rowsLen_ptransGo n (ptails m) w
      ((ground.length_map _ m).trans hw) p (Nat.lt_of_succ_lt_succ hp)

/-! The congruence's shape reads: the descent's exchanged key count
at both sides, and the entries' counts within the site datum's own
— the scalar folds sit at their family's bound and the key-list
exchange keeps it. -/

/-- The congruence's row count is the descent's exchanged one. -/
theorem congrZ_len (T : Mat) (Z : PMat) :
    (congrZ T Z).length = (transposeM T).length :=
  ground.length_map _ _

/-- The key-list exchange runs at the stated order. -/
private theorem ptranspose_fuel : ∀ (M : PMat) (n : Nat),
    M.length = n → rowsLen n M → ptranspose M = ptransGo n M
  | [], n, hl, _ => by
    match n, hl with
    | 0, _ => rfl
  | r :: t, n, _, hr => by
    show ptransGo r.length (r :: t) = ptransGo n (r :: t)
    rw [hr.1]

/-- The congruence's rows read the descent's key count. -/
theorem congrZ_rows (T : Mat) (Z : PMat) (n : Nat)
    (hTl : T.length = n) (hTr : rowsLen n T) (hZl : Z.length = n) :
    rowsLen n (congrZ T Z) := by
  have hTt : (transposeM T).length = n := transposeLen T hTr hTl
  show rowsLen n ((transposeM T).map (fun ti =>
    (ptranspose (Z.map (fun r => (transposeM T).map
      (fun c => poly.scaleDot c r)))).map
      (fun colj => poly.scaleDot ti colj)))
  refine rowsLen_map _ n (transposeM T) (fun ti _ => ?_)
  rw [ground.length_map,
    ptranspose_fuel (Z.map (fun r => (transposeM T).map
      (fun c => poly.scaleDot c r))) n
      (by rw [ground.length_map]; exact hZl)
      (rowsLen_map _ n Z (fun r _ => by
        rw [ground.length_map]; exact hTt)),
    length_ptransGo]

/-- A scalar fold against a family within a count sits there. -/
private theorem scaleDot_ble (K : Nat) (r : List BPair) (u : List Poly)
    (hu : (u.all (fun p => Nat.ble p.length K)) = true) :
    Nat.ble (poly.scaleDot r u).length K = true :=
  ground.leBle (poly.scaleDot_len_le r u
    (fun j hj => ground.bleLe
      (ground.all_getAt ([] : Poly) u hu j hj)))

/-- The folds of one family against a bounded row list sit at the
bound. -/
private theorem scaleDotRow_ble (K : Nat) (ti : List BPair) :
    ∀ M : PMat,
      (M.all (fun r => r.all (fun p => Nat.ble p.length K))) = true →
      ((M.map (fun colj => poly.scaleDot ti colj)).all
        (fun p => Nat.ble p.length K)) = true
  | [], _ => rfl
  | r :: t, h => by
    have hs := ground.andSplitB h
    show (Nat.ble (poly.scaleDot ti r).length K
      && ((t.map (fun colj => poly.scaleDot ti colj)).all
        (fun p => Nat.ble p.length K))) = true
    rw [scaleDot_ble K ti r hs.1, scaleDotRow_ble K ti t hs.2]
    rfl

/-- The exchange's head row sits at the rows' bound. -/
private theorem pheads_ble (K : Nat) : ∀ m : PMat,
    (m.all (fun r => r.all (fun p => Nat.ble p.length K))) = true →
    ((pheads m).all (fun p => Nat.ble p.length K)) = true
  | [], _ => rfl
  | r :: t, h => by
    have hs := ground.andSplitB h
    match r, hs.1 with
    | [], _ =>
      show (Nat.ble ([] : Poly).length K
        && (pheads t).all (fun p => Nat.ble p.length K)) = true
      rw [pheads_ble K t hs.2]
      rfl
    | a :: u, hr =>
      have ha : Nat.ble a.length K = true := (ground.andSplitB hr).1
      show (Nat.ble a.length K
        && (pheads t).all (fun p => Nat.ble p.length K)) = true
      rw [pheads_ble K t hs.2, ha]
      rfl

/-- The exchange's dropped heads keep the rows' bound. -/
private theorem ptails_ble (K : Nat) : ∀ m : PMat,
    (m.all (fun r => r.all (fun p => Nat.ble p.length K))) = true →
    ((ptails m).all
      (fun r => r.all (fun p => Nat.ble p.length K))) = true
  | [], _ => rfl
  | r :: t, h => by
    have hs := ground.andSplitB h
    match r, hs.1 with
    | [], _ =>
      show (([] : List Poly).all (fun p => Nat.ble p.length K)
        && (ptails t).all
          (fun r => r.all (fun p => Nat.ble p.length K))) = true
      rw [ptails_ble K t hs.2]
      rfl
    | a :: u, hr =>
      have hu : (u.all (fun p => Nat.ble p.length K)) = true :=
        (ground.andSplitB hr).2
      show (u.all (fun p => Nat.ble p.length K)
        && (ptails t).all
          (fun r => r.all (fun p => Nat.ble p.length K))) = true
      rw [ptails_ble K t hs.2, hu]
      rfl

/-- The key-list exchange keeps the entries' bound. -/
private theorem ptransGo_ble (K : Nat) : ∀ (n : Nat) (m : PMat),
    (m.all (fun r => r.all (fun p => Nat.ble p.length K))) = true →
    ((ptransGo n m).all
      (fun r => r.all (fun p => Nat.ble p.length K))) = true
  | 0, _, _ => rfl
  | n + 1, m, h => by
    show ((pheads m).all (fun p => Nat.ble p.length K)
      && (ptransGo n (ptails m)).all
        (fun r => r.all (fun p => Nat.ble p.length K))) = true
    rw [pheads_ble K m h, ptransGo_ble K n (ptails m) (ptails_ble K m h)]
    rfl

/-- The congruence keeps the site datum's entry bound: the scalar
folds of families within a count sit within it, the key-list
exchange between them included. -/
theorem congrZ_ble (T : Mat) (Z : PMat) (K : Nat)
    (hZ : (Z.all (fun r => r.all (fun p => Nat.ble p.length K)))
      = true) :
    ((congrZ T Z).all
      (fun r => r.all (fun p => Nat.ble p.length K))) = true := by
  have hZT : ((Z.map (fun r => (transposeM T).map
      (fun c => poly.scaleDot c r))).all
    (fun r => r.all (fun p => Nat.ble p.length K))) = true := by
    rw [ground.all_map]
    refine ground.all_of_getAt ([] : List Poly) _ Z (fun k hk => ?_)
    rw [ground.all_map]
    exact ground.all_of_pointwise _ (transposeM T)
      (fun c => scaleDot_ble K c _
        (ground.all_getAt ([] : List Poly) Z hZ k hk))
  have hZTt : ((ptranspose (Z.map (fun r => (transposeM T).map
      (fun c => poly.scaleDot c r)))).all
    (fun r => r.all (fun p => Nat.ble p.length K))) = true :=
    ptransGo_ble K _ _ hZT
  show (((transposeM T).map (fun ti =>
      (ptranspose (Z.map (fun r => (transposeM T).map
        (fun c => poly.scaleDot c r)))).map
      (fun colj => poly.scaleDot ti colj))).all
    (fun r => r.all (fun p => Nat.ble p.length K))) = true
  rw [ground.all_map]
  exact ground.all_of_pointwise _ (transposeM T)
    (fun ti => scaleDotRow_ble K ti _ hZTt)

/-- A site row's entries read two keys, the pair's two members. -/
private theorem zipRow_ble : ∀ r s : List BPair,
    ((List.zipWith (fun h g => [BPair.swap h, g]) r s).all
      (fun p => Nat.ble p.length 2)) = true
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: r, b :: s => by
    show (Nat.ble [BPair.swap a, b].length 2
      && (List.zipWith (fun h g => [BPair.swap h, g]) r s).all
        (fun p => Nat.ble p.length 2)) = true
    rw [zipRow_ble r s]
    rfl

/-- The site datum's entries read two keys at most: the level
pair's members enter at the two keys alone. -/
theorem zMat_ble : ∀ H G : Mat,
    ((zMat H G).all
      (fun r => r.all (fun p => Nat.ble p.length 2))) = true
  | [], _ => rfl
  | _ :: _, [] => rfl
  | r :: H, s :: G => by
    show ((List.zipWith (fun h g => [BPair.swap h, g]) r s).all
        (fun p => Nat.ble p.length 2)
      && (zMat H G).all
        (fun r => r.all (fun p => Nat.ble p.length 2))) = true
    rw [zMat_ble H G, zipRow_ble r s]
    rfl

private theorem dotRowsOne (ti : List BPair) : ∀ a b : Mat,
    matOneValue a b →
    poly.oneValue (a.map (fun c => dotP c ti)) (b.map (fun c => dotN ti c))
  | [], [], _ => trivial
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | r :: a, s :: b, h =>
    ⟨BPair.oneValue_trans (dotP_oneValue_left r s ti h.1)
       (BPair.oneValue_trans (BPair.oneValue_of_eq (dotP_comm s ti))
         (BPair.oneValue_symm (dotN_read ti s))),
     dotRowsOne ti a b h.2⟩

private theorem pcf_prod (k : Nat) (T : Mat) (Z : PMat) :
    matOneValue
      (pcf k (Z.map (fun r => (transposeM T).map (fun c => poly.scaleDot c r))))
      (matMul (pcf k Z) T) := by
  show matOneValue
      ((Z.map (fun r => (transposeM T).map (fun c => poly.scaleDot c r))).map
        (fun r => r.map (cf k)))
      ((Z.map (fun r => r.map (cf k))).map
        (fun r => (transposeM T).map (fun c => dotN r c)))
  rw [ground.map_map, ground.map_map]
  refine matOne_map _ _ (fun r => ?_) Z
  rw [ground.map_map]
  exact poly.oneValue_map _ _ (transposeM T) (fun x _ => (fun c =>
    BPair.oneValue_trans (cf_scaleDot c r k)
      (BPair.oneValue_symm (dotN_read _ c))) x)

private theorem pcf_trans_key (k w : Nat) (N : PMat) (W : Mat)
    (hN : ∀ p, p < N.length →
      (ground.getAt ([] : List Poly) N p).length = w)
    (hW : rowsLen w W) (hlen : N.length = W.length) (hpos : 0 < N.length)
    (h : matOneValue (pcf k N) W) :
    matOneValue (pcf k (ptranspose N)) (transposeM W) := by
  have hfuel : ptranspose N = ptransGo w N := by
    match N, hpos with
    | r :: t, _ =>
      show ptransGo r.length (r :: t) = ptransGo w (r :: t)
      rw [show r.length = w from hN 0 (Nat.succ_pos _)]
  have hPl : (ptranspose N).length = w := by rw [hfuel, length_ptransGo]
  have hWpos : 0 < W.length := by rw [← hlen]; exact hpos
  have hTWl : (transposeM W).length = w := length_transposeM W hW hWpos
  have hrow : ∀ p, p < w →
      (ground.getAt ([] : List Poly) (ptranspose N) p).length = N.length := by
    intro p hp
    rw [hfuel]
    exact rowsLen_ptransGo w N N.length rfl p hp
  refine matOne_getAt _ _ ?_ ?_
  · rw [show (pcf k (ptranspose N)).length = (ptranspose N).length from
      ground.length_map _ _, hPl, hTWl]
  · intro i hi
    rw [show (pcf k (ptranspose N)).length = (ptranspose N).length from
      ground.length_map _ _, hPl] at hi
    rw [show ground.getAt ([] : List BPair) (pcf k (ptranspose N)) i
        = (ground.getAt ([] : List Poly) (ptranspose N) i).map (cf k) from
      ground.getAt_map ([] : List Poly) ([] : List BPair) _ (ptranspose N) i
        (by rw [hPl]; exact hi)]
    refine getAt_polyOne _ _ ?_ ?_
    · rw [ground.length_map, hrow i hi, hlen,
        rowsLen_getAt (transposeM W) i (rowsLen_transposeM W)
          (by rw [hTWl]; exact hi)]
    · intro q hq
      rw [ground.length_map, hrow i hi] at hq
      rw [ground.getAt_map ([] : Poly) BPair.unit (cf k)
          (ground.getAt ([] : List Poly) (ptranspose N) i) q
          (by rw [hrow i hi]; exact hq),
        hfuel, getAt_ptransGo w N i q hi hq,
        getAt_transposeM BPair.unit W hW i q hi (by rw [← hlen]; exact hq)]
      have hr := matOne_entries _ _ h q
        (by rw [show (pcf k N).length = N.length from
          ground.length_map _ _]; exact hq)
      rw [show ground.getAt ([] : List BPair) (pcf k N) q
          = (ground.getAt ([] : List Poly) N q).map (cf k) from
        ground.getAt_map ([] : List Poly) ([] : List BPair) _ N q hq] at hr
      have hi2 := poly.oneValue_getAt i hr
      rw [ground.getAt_map ([] : Poly) BPair.unit (cf k)
        (ground.getAt ([] : List Poly) N q) i
        (by rw [hN q hq]; exact hi)] at hi2
      exact hi2

private theorem pcf_key (k : Nat) (T : Mat) (Z : PMat) :
    matOneValue
      (pcf k (ptranspose
        (Z.map (fun r => (transposeM T).map (fun c => poly.scaleDot c r)))))
      (transposeM (matMul (pcf k Z) T)) := by
  match Z with
  | [] => exact trivial
  | r0 :: Zt =>
    refine pcf_trans_key k (transposeM T).length _ _ ?_ (rowsLen_matMul _ T)
      ?_ ?_ (pcf_prod k T (r0 :: Zt))
    · intro p hp
      rw [show ((r0 :: Zt).map (fun r =>
            (transposeM T).map (fun c => poly.scaleDot c r))).length
          = (r0 :: Zt).length from ground.length_map _ _] at hp
      rw [ground.getAt_map ([] : List Poly) ([] : List Poly) _ (r0 :: Zt) p hp,
        ground.length_map]
    · rw [show ((r0 :: Zt).map (fun r =>
            (transposeM T).map (fun c => poly.scaleDot c r))).length
          = (r0 :: Zt).length from ground.length_map _ _,
        show (matMul (pcf k (r0 :: Zt)) T).length = (r0 :: Zt).length from by
          rw [show (matMul (pcf k (r0 :: Zt)) T).length
              = (pcf k (r0 :: Zt)).length from ground.length_map _ _,
            show (pcf k (r0 :: Zt)).length = (r0 :: Zt).length from
              ground.length_map _ _]]
    · rw [show ((r0 :: Zt).map (fun r =>
            (transposeM T).map (fun c => poly.scaleDot c r))).length
          = (r0 :: Zt).length from ground.length_map _ _]
      exact Nat.succ_pos _

private theorem pcf_congrZ (k : Nat) (T : Mat) (Z : PMat) :
    matOneValue (pcf k (congrZ T Z))
      (matMul (transposeM T) (matMul (pcf k Z) T)) := by
  show matOneValue
      (((transposeM T).map (fun ti =>
        (ptranspose (Z.map (fun r =>
          (transposeM T).map (fun c => poly.scaleDot c r)))).map
            (fun colj => poly.scaleDot ti colj))).map (fun r => r.map (cf k)))
      ((transposeM T).map (fun ti =>
        (transposeM (matMul (pcf k Z) T)).map (fun c => dotN ti c)))
  rw [ground.map_map]
  refine matOne_map _ _ (fun ti => ?_) (transposeM T)
  rw [ground.map_map]
  refine poly.oneValue_trans
    (poly.oneValue_map (fun colj => cf k (poly.scaleDot ti colj)) (fun colj => dotP (colj.map (cf k)) ti) _ (fun x _ => (fun colj => cf_scaleDot ti colj k) x)) ?_
  rw [show (ptranspose (Z.map (fun r =>
        (transposeM T).map (fun c => poly.scaleDot c r)))).map
        (fun colj => dotP (colj.map (cf k)) ti)
      = (pcf k (ptranspose (Z.map (fun r =>
        (transposeM T).map (fun c => poly.scaleDot c r))))).map (fun c => dotP c ti)
      from (ground.map_map (fun r : List Poly => r.map (cf k))
        (fun c : List BPair => dotP c ti) _).symm]
  exact dotRowsOne ti _ _ (pcf_key k T Z)

/-! The site datum's two coefficients: the linear the second datum
outright, the constant the first's memberwise swap. -/

private theorem zRow_lin : ∀ r s : List BPair, r.length = s.length →
    (List.zipWith (fun h g => [BPair.swap h, g]) r s).map (cf 1) = s
  | [], [], _ => rfl
  | [], _ :: _, hl => Nat.noConfusion hl
  | _ :: _, [], hl => Nat.noConfusion hl
  | _ :: r, b :: s, hl => by
    show b :: (List.zipWith (fun h g => [BPair.swap h, g]) r s).map (cf 1)
      = b :: s
    rw [zRow_lin r s (Nat.succ.inj hl)]

private theorem zRow_const : ∀ r s : List BPair, r.length = s.length →
    (List.zipWith (fun h g => [BPair.swap h, g]) r s).map (cf 0)
      = r.map BPair.swap
  | [], [], _ => rfl
  | [], _ :: _, hl => Nat.noConfusion hl
  | _ :: _, [], hl => Nat.noConfusion hl
  | a :: r, _ :: s, hl => by
    show a.swap :: (List.zipWith (fun h g => [BPair.swap h, g]) r s).map (cf 0)
      = a.swap :: r.map BPair.swap
    rw [zRow_const r s (Nat.succ.inj hl)]

private theorem pcf_zMat_lin : ∀ (H G : Mat) (o : Nat), rowsLen o H →
    rowsLen o G → H.length = G.length → pcf 1 (zMat H G) = G
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hl => Nat.noConfusion hl
  | _ :: _, [], _, _, _, hl => Nat.noConfusion hl
  | r :: H, s :: G, o, hH, hG, hl => by
    show (List.zipWith (fun h g => [BPair.swap h, g]) r s).map (cf 1)
        :: pcf 1 (zMat H G) = s :: G
    rw [zRow_lin r s (hH.1.trans hG.1.symm),
      pcf_zMat_lin H G o hH.2 hG.2 (Nat.succ.inj hl)]

private theorem pcf_zMat_const : ∀ (H G : Mat) (o : Nat), rowsLen o H →
    rowsLen o G → H.length = G.length → pcf 0 (zMat H G) = matSwap H
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hl => Nat.noConfusion hl
  | _ :: _, [], _, _, _, hl => Nat.noConfusion hl
  | r :: H, s :: G, o, hH, hG, hl => by
    show (List.zipWith (fun h g => [BPair.swap h, g]) r s).map (cf 0)
        :: pcf 0 (zMat H G) = r.map BPair.swap :: matSwap H
    rw [zRow_const r s (hH.1.trans hG.1.symm),
      pcf_zMat_const H G o hH.2 hG.2 (Nat.succ.inj hl)]

/-- The congruence's linear coefficient: the site's second datum
carried by the congruence, `Tᵀ G T` at the stated order. -/
theorem plin_congrZ {o : Nat} (H G : Mat) (T : SqMat o)
    (hH : sqAt H o) (hG : sqAt G o) :
    matOneValue (plin (congrZ T.val (zMat H G)))
      (matMul (transposeM T.val) (matMul G T.val)) := by
  have hz : pcf 1 (zMat H G) = G :=
    pcf_zMat_lin H G o (rowsLen_of_sqAt hH) (rowsLen_of_sqAt hG)
      ((sqAt_len hH).trans (sqAt_len hG).symm)
  have h1 := pcf_congrZ 1 T.val (zMat H G)
  rw [hz] at h1
  rw [plin_pcf]
  exact h1

/-- The congruence's constant coefficient: the site's first datum
carried by the congruence at the pencil's own sign, the memberwise
swap of `Tᵀ H T`. -/
theorem pconst_congrZ {o : Nat} (H G : Mat) (T : SqMat o)
    (hH : sqAt H o) (hG : sqAt G o) :
    matOneValue (pconst (congrZ T.val (zMat H G)))
      (matSwap (matMul (transposeM T.val) (matMul H T.val))) := by
  have hz : pcf 0 (zMat H G) = matSwap H :=
    pcf_zMat_const H G o (rowsLen_of_sqAt hH) (rowsLen_of_sqAt hG)
      ((sqAt_len hH).trans (sqAt_len hG).symm)
  have h1 := pcf_congrZ 0 T.val (zMat H G)
  rw [hz, matMul_swapL, matMul_swap] at h1
  rw [pconst_pcf]
  exact h1

/-! The diagonal side's two coefficients: the diagonals at the scaled
root data, the scale against the root's own members. -/

private theorem getAt_cfmap : ∀ (ds : List Poly) (i k : Nat),
    ground.getAt BPair.unit (ds.map (cf k)) i
      = cf k (ground.getAt ([] : Poly) ds i)
  | [], 0, _ => rfl
  | [], _ + 1, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: t, i + 1, k => getAt_cfmap t i k

private theorem pcf_pdiag (k : Nat) (ds : List Poly) :
    pcf k (pdiag ds) = diagM (ds.map (cf k)) := by
  show (ground.matOf ds.length ds.length
      (fun i j => if j = i then ground.getAt ([] : Poly) ds i else [])).map
      (fun r => r.map (cf k))
    = ground.matOf (ds.map (cf k)).length (ds.map (cf k)).length
      (fun i j => if j = i then ground.getAt BPair.unit (ds.map (cf k)) i
        else BPair.unit)
  rw [ground.length_map (cf k) ds]
  refine Eq.trans (ground.map_map _ _ (List.range ds.length)) ?_
  refine ground.map_congr_all _ _ (fun i => ?_) (List.range ds.length)
  refine Eq.trans (ground.map_map _ _ (List.range ds.length)) ?_
  refine ground.map_congr_all _ _ (fun j => ?_) (List.range ds.length)
  show cf k (if j = i then ground.getAt ([] : Poly) ds i else [])
    = if j = i then ground.getAt BPair.unit (ds.map (cf k)) i
      else BPair.unit
  rw [getAt_cfmap ds i k]
  by_cases hij : j = i
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij]
    rfl

private theorem cfmap_lin (l : List (BPair × Pos × BPair)) :
    (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))).map (cf 1)
      = l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm) := by
  rw [ground.map_map]
  exact rfl

private theorem cfmap_const (l : List (BPair × Pos × BPair)) :
    (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))).map (cf 0)
      = l.map (fun r => (r.2.2 * r.1).norm.swap) := by
  rw [ground.map_map]
  refine ground.map_congr_all _ _ (fun r => ?_) l
  show (r.2.2 * r.1.swap).norm = (r.2.2 * r.1).norm.swap
  rw [BPair.mul_swap, BPair.norm_swap]

/-- The diagonal side's linear coefficient: the diagonal at the
scale against the root's second member. -/
theorem plin_pdiag (l : List (BPair × Pos × BPair)) :
    plin (pdiag (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))))
      = diagM (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)) := by
  rw [plin_pcf, pcf_pdiag, cfmap_lin]

/-- The diagonal side's constant coefficient: the diagonal at the
scale against the root's first member, memberwise swapped. -/
theorem pconst_pdiag (l : List (BPair × Pos × BPair)) :
    pconst (pdiag (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))))
      = diagM (l.map (fun r => (r.2.2 * r.1).norm.swap)) := by
  rw [pconst_pcf, pcf_pdiag, cfmap_const]

/-! The capstone's kit: the unit family's pairing, the identity and
diagonal actions, the memberwise swap's transport, and the clearing's
cancellation. -/

theorem matVec_idMat (n : Nat) (u : List BPair)
    (hu : u.length = n) : poly.oneValue (matVec (idMat n) u) u := by
  have hid : (idMat n).length = n :=
    ground.length_mapRange _ n
  refine getAt_polyOne _ _ ?_ ?_
  · rw [matVec_length, hid, hu]
  · intro i hi
    rw [matVec_length, hid] at hi
    rw [show matVec (idMat n) u = (idMat n).map (fun r => dotN r u) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit _ (idMat n) i
        (by rw [hid]; exact hi),
      inertia.idMat_row n i hi]
    refine BPair.oneValue_trans (dotN_read _ u) ?_
    rw [dotP_comm (idRow n i) u]
    exact dotP_idRow u n i hu hi

theorem diagM_len (ds : List BPair) : (diagM ds).length = ds.length :=
  elim.diagO_len ground.bpairOps ds

theorem diagM_rowlen (ds : List BPair) (i : Nat)
    (hi : i < ds.length) :
    (ground.getAt ([] : List BPair) (diagM ds) i).length = ds.length :=
  elim.rowsLen_getAt (diagM ds) i (elim.diagO_rows ground.bpairOps ds)
    (by rw [diagM_len]; exact hi)

theorem diagM_entry (ds : List BPair) (i q : Nat)
    (hi : i < ds.length) (hq : q < ds.length) :
    ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (diagM ds) i) q
      = if q = i then ground.getAt BPair.unit ds i else BPair.unit :=
  elim.diagO_entry ground.bpairOps ds i q hi hq

/-- The diagonal's rows read the entry count. -/
theorem diagM_shape (ds : List BPair) (n : Nat) (hn : ds.length = n) :
    rowsLen n (diagM ds) := by
  rw [← hn]
  exact elim.diagO_rows ground.bpairOps ds

private theorem diagM_act (ds : List BPair) (j : Nat) (hj : j < ds.length) :
    poly.oneValue (matVec (diagM ds) (idRow ds.length j))
      (vecScale (ground.getAt BPair.unit ds j) (idRow ds.length j)) := by
  refine getAt_polyOne _ _ ?_ ?_
  · rw [matVec_length, diagM_len, length_vecScale, length_idRow]
  · intro i hi
    rw [matVec_length, diagM_len] at hi
    rw [show matVec (diagM ds) (idRow ds.length j)
        = (diagM ds).map (fun r => dotN r (idRow ds.length j)) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit _ (diagM ds) i
        (by rw [diagM_len]; exact hi),
      show vecScale (ground.getAt BPair.unit ds j) (idRow ds.length j)
        = (idRow ds.length j).map
          (fun x => ground.getAt BPair.unit ds j * x) from rfl,
      ground.getAt_map BPair.unit BPair.unit _ (idRow ds.length j) i
        (by rw [length_idRow]; exact hi),
      getAt_idRow ds.length j i hi]
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    refine BPair.oneValue_trans
      (dotP_oneIndex _ (idRow ds.length j) j
        (by rw [diagM_rowlen ds i hi, length_idRow])
        (by rw [length_idRow]; exact hj) ?_) ?_
    · intro q hq hne
      rw [length_idRow] at hq
      rw [getAt_idRow ds.length j q hq, if_neg hne]
      exact BPair.oneValue_refl _
    · rw [getAt_idRow ds.length j j hj, if_pos rfl,
        diagM_entry ds i j hi hj]
      by_cases hij : i = j
      · rw [hij, if_pos rfl, if_pos rfl]
        exact BPair.oneValue_refl _
      · rw [if_neg (fun hc : j = i => hij hc.symm),
          if_neg hij]
        exact BPair.oneValue_trans (BPair.unit_mul _)
          (BPair.oneValue_symm (BPair.mul_unit _))

private theorem colRead {o : Nat} (M : Mat) (T Tw : SqMat o) (c : BPair)
    (i j : Nat) (hM : sqAt M o) (hi : i < o)
    (hTTw : matOneValue (matMul T.val Tw.val)
      (matScaleB (minor T.val) (idMat o)))
    (hX : poly.oneValue
      (matVec (matMul (transposeM T.val) (matMul M T.val)) (idRow o j))
      (vecScale c (idRow o j))) :
    (minor T.val * ground.getAt BPair.unit
        (matVec M (matVec T.val (idRow o j))) i).oneValue
      (c * dotP (matVec Tw.val (idRow o i)) (idRow o j)) := by
  have hMl : M.length = o := sqAt_len hM
  have hMr : rowsLen o M := rowsLen_of_sqAt hM
  have hTl : T.val.length = o := SqMat.rows T
  have hTr : rowsLen o T.val := rowsLen_of_sqAt T.shape
  have hTwl : Tw.val.length = o := SqMat.rows Tw
  have hTwr : rowsLen o Tw.val := rowsLen_of_sqAt Tw.shape
  have hTtl : (transposeM T.val).length = o := transposeLen T.val hTr hTl
  have hTtr : rowsLen o (transposeM T.val) :=
    rowsLen_cast hTl (rowsLen_transposeM T.val)
  have hei : (idRow o i).length = o := length_idRow o i
  have hej : (idRow o j).length = o := length_idRow o j
  have hz : (matVec Tw.val (idRow o i)).length = o := by
    rw [matVec_length, hTwl]
  have hu : (matVec M (matVec T.val (idRow o j))).length = o := by
    rw [matVec_length, hMl]
  have hMTl : (matMul M T.val).length = o := by
    rw [show (matMul M T.val).length = M.length from ground.length_map _ M]
    exact hMl
  have hTz : poly.oneValue (matVec T.val (matVec Tw.val (idRow o i)))
      (vecScale (minor T.val) (idRow o i)) :=
    poly.oneValue_trans
      (matVec_comp T.val Tw.val (idRow o i) o hTwr hei
        (rowsLen_cast hTwl.symm hTr))
      (poly.oneValue_trans (matVec_matOne _ _ _ hTTw)
        (scaleId_act (minor T.val) o (idRow o i) hei))
  have hpair : (dotP (matVec T.val (matVec Tw.val (idRow o i)))
        (matVec M (matVec T.val (idRow o j)))).oneValue
      (dotP (matVec Tw.val (idRow o i))
        (matVec (matMul (transposeM T.val) (matMul M T.val))
          (idRow o j))) := by
    refine BPair.oneValue_trans
      (dotP_matVec_transpose o T.val (matVec Tw.val (idRow o i))
        (matVec M (matVec T.val (idRow o j))) hTr hz (by rw [hu, hTl])) ?_
    refine dotP_oneValue_right _ _ _ ?_
    refine poly.oneValue_trans
      (matVec_congr (transposeM T.val) _ _
        (matVec_comp M T.val (idRow o j) o hTr hej
          (rowsLen_cast hTl.symm hMr))) ?_
    exact matVec_comp (transposeM T.val) (matMul M T.val) (idRow o j) o
      (rowsLen_cast hTtl (rowsLen_matMul M T.val)) hej
      (rowsLen_cast hMTl.symm hTtr)
  have hL : (dotP (matVec T.val (matVec Tw.val (idRow o i)))
        (matVec M (matVec T.val (idRow o j)))).oneValue
      (minor T.val * ground.getAt BPair.unit
        (matVec M (matVec T.val (idRow o j))) i) := by
    refine BPair.oneValue_trans (dotP_oneValue_left _ _ _ hTz) ?_
    rw [dotP_comm (vecScale (minor T.val) (idRow o i))
      (matVec M (matVec T.val (idRow o j)))]
    refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _) (dotP_idRow _ o i hu hi)
  exact BPair.oneValue_trans (BPair.oneValue_symm hL)
    (BPair.oneValue_trans hpair
      (BPair.oneValue_trans (dotP_oneValue_right _ _ _ hX)
        (dotP_vecScale_right _ _ _)))

/-- The eigen-column read at the completed certificate: at every key
of the root list the congruence's own column is the pencil's
eigendirection there, the root's two members clearing the two data —
`d_j (H v_j) = n_j (G v_j)` entrywise at the cleared carrier, the
diagonal's key and the witness's product reads the derivation. -/
theorem eigenColumn {o : Nat} (H G : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair)) (j : Nat) (nj gj : BPair) (dj : Pos)
    (hd : diagRead H G T Tw l) (hj : j < l.length)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    poly.oneValue
      (vecScale (BPair.ofPos dj) (matVec H (matVec T.val (idRow o j))))
      (vecScale nj (matVec G (matVec T.val (idRow o j)))) := by
  obtain ⟨hH, hG, ⟨hdet, hTTw, _⟩, hcong, _⟩ := hd
  have hTl : T.val.length = o := SqMat.rows T
  have hTr : rowsLen o T.val := rowsLen_of_sqAt T.shape
  have hHl : H.length = o := sqAt_len hH
  have hGl : G.length = o := sqAt_len hG
  have hTtl : (transposeM T.val).length = o := transposeLen T.val hTr hTl
  have hlo : l.length = o := by
    have h1 := ground.matched_length hcong
    rw [show (congrZ T.val (zMat H G)).length = (transposeM T.val).length from
        ground.length_map _ _, hTtl,
      show (pdiag (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1)))).length
          = (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))).length from
        ground.length_mapRange _ _,
      ground.length_map] at h1
    exact h1.symm
  have hjo : j < o := by rw [← hlo]; exact hj
  have hDG : matOneValue (matMul (transposeM T.val) (matMul G T.val))
      (diagM (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) := by
    have h2 := pcfOne _ _ hcong 1
    rw [pcf_pdiag, cfmap_lin] at h2
    have h3 : matOneValue (pcf 1 (congrZ T.val (zMat H G)))
        (matMul (transposeM T.val) (matMul G T.val)) := by
      rw [← plin_pcf]; exact plin_congrZ H G T hH hG
    exact matOne_trans (matOne_symm h3) h2
  have hDH : matOneValue
      (matSwap (matMul (transposeM T.val) (matMul H T.val)))
      (diagM (l.map (fun r => (r.2.2 * r.1).norm.swap))) := by
    have h2 := pcfOne _ _ hcong 0
    rw [pcf_pdiag, cfmap_const] at h2
    have h3 : matOneValue (pcf 0 (congrZ T.val (zMat H G)))
        (matSwap (matMul (transposeM T.val) (matMul H T.val))) := by
      rw [← pconst_pcf]; exact pconst_congrZ H G T hH hG
    exact matOne_trans (matOne_symm h3) h2
  have hDGl : (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)).length = o := by
    rw [ground.length_map]; exact hlo
  have hDHl : (l.map (fun r => (r.2.2 * r.1).norm.swap)).length = o := by
    rw [ground.length_map]; exact hlo
  have hGval : ground.getAt BPair.unit
      (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)) j
      = (gj * BPair.ofPos dj).norm := by
    rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit) BPair.unit _ l j hj,
      hroot]
  have hHval : ground.getAt BPair.unit
      (l.map (fun r => (r.2.2 * r.1).norm.swap)) j = (gj * nj).norm.swap := by
    rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit) BPair.unit _ l j hj,
      hroot]
  have hXG : poly.oneValue
      (matVec (matMul (transposeM T.val) (matMul G T.val)) (idRow o j))
      (vecScale ((gj * BPair.ofPos dj).norm) (idRow o j)) := by
    refine poly.oneValue_trans (matVec_matOne _ _ _ hDG) ?_
    have hact := diagM_act (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))
      j (by rw [hDGl]; exact hjo)
    rw [hDGl, hGval] at hact
    exact hact
  have hXH : poly.oneValue
      (matVec (matMul (transposeM T.val) (matMul H T.val)) (idRow o j))
      (vecScale ((gj * nj).norm) (idRow o j)) := by
    have hsw : poly.oneValue
        ((matVec (matMul (transposeM T.val) (matMul H T.val))
          (idRow o j)).map BPair.swap)
        (vecScale ((gj * nj).norm.swap) (idRow o j)) := by
      rw [← matVec_swapM (matMul (transposeM T.val) (matMul H T.val))
          (idRow o j)]
      refine poly.oneValue_trans (matVec_matOne _ _ _ hDH) ?_
      have hact := diagM_act (l.map (fun r => (r.2.2 * r.1).norm.swap)) j
        (by rw [hDHl]; exact hjo)
      rw [hDHl, hHval] at hact
      exact hact
    have h4 := poly.swapMap_oneValue hsw
    rw [show ∀ u : List BPair, (u.map BPair.swap).map BPair.swap = u from
      poly.neg_neg, ← elim.vecScale_swap] at h4
    exact h4
  refine getAt_polyOne _ _ ?_ ?_
  · rw [length_vecScale, length_vecScale, matVec_length, matVec_length,
      hHl, hGl]
  · intro i hi
    rw [length_vecScale, matVec_length, hHl] at hi
    rw [show vecScale (BPair.ofPos dj) (matVec H (matVec T.val (idRow o j)))
        = (matVec H (matVec T.val (idRow o j))).map
          (fun x => BPair.ofPos dj * x) from rfl,
      ground.getAt_map BPair.unit BPair.unit _
        (matVec H (matVec T.val (idRow o j))) i
        (by rw [matVec_length, hHl]; exact hi),
      show vecScale nj (matVec G (matVec T.val (idRow o j)))
        = (matVec G (matVec T.val (idRow o j))).map (fun x => nj * x) from rfl,
      ground.getAt_map BPair.unit BPair.unit _
        (matVec G (matVec T.val (idRow o j))) i
        (by rw [matVec_length, hGl]; exact hi)]
    refine mulCancel hdet ?_
    have hHi := colRead H T Tw ((gj * nj).norm) i j hH hi hTTw hXH
    have hGi := colRead G T Tw ((gj * BPair.ofPos dj).norm) i j hG hi hTTw hXG
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hHi) ?_
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _))
        (BPair.mul_congr (BPair.oneValue_refl _) hGi)))
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.norm_oneValue _) (BPair.oneValue_refl _))) ?_
    refine BPair.oneValue_trans ?_
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_symm (BPair.norm_oneValue _))
          (BPair.oneValue_refl _)))
    refine BPair.oneValue_of_eq ?_
    rw [← BPair.mul_assoc (BPair.ofPos dj) (gj * nj)
        (dotP (matVec Tw.val (idRow o i)) (idRow o j)),
      ← BPair.mul_assoc nj (gj * BPair.ofPos dj)
        (dotP (matVec Tw.val (idRow o i)) (idRow o j)),
      BPair.mul_left_comm (BPair.ofPos dj) gj nj,
      BPair.mul_left_comm nj gj (BPair.ofPos dj),
      BPair.mul_comm (BPair.ofPos dj) nj]

/-! `lem:split`'s factorization clause: the completed congruence
returns the pencil's own read.  The congruence identity's
determinant collects the exchanged lists' product to
`det S_χ² χ` against the diagonal blocks' product
`Π_j ⟨x : ε_j⟩ g_j`, the linear coefficient's own determinants
collect to `det S_χ² det G` against `Π_j g_j`, and the shared
factor `det S_χ²`, off equal members at the unit congruence,
withdraws at the products' one value key by key.  The kit beneath
it: the one-member products' collection, the two folds' seed
congruences, the sum fold over a key range against the coefficient
fold, and the product's entry at the polynomial carrier. -/

/-- Two one-member polynomials multiply at their scales' own
product. -/
private theorem mulSingles (a b : BPair) :
    poly.oneValue (poly.mul [a] [b]) [a * b] :=
  poly.oneValue_trans (poly.mul_single [a] b)
    ⟨BPair.oneValue_of_eq (BPair.mul_comm b a), trivial⟩

/-- Two one-member scales collect onto their product. -/
private theorem mulCollect (a b : BPair) (P : Poly) :
    poly.oneValue (poly.mul [a] (poly.mul [b] P)) (poly.mul [a * b] P) :=
  poly.oneValue_trans (poly.oneValue_symm (poly.mul_assoc [a] [b] P))
    (poly.mul_congr_left (mulSingles a b) P)

/-- The one-member product is the entrywise rescaling. -/
private theorem mulVecScale (c : BPair) (P : Poly) :
    poly.oneValue (poly.mul [c] P) (elim.vecScale c P) :=
  poly.oneValue_trans (poly.mul_comm [c] P) (poly.mul_single P c)

/-- The sum fold over a key range moves across one read per key,
the members' congruence at the range's own membership. -/
private theorem famFoldP_congr_range (f g : Nat → Poly) (n : Nat)
    (h : ∀ k, k < n → poly.oneValue (f k) (g k)) :
    poly.oneValue (ground.famFold poly.add [] f (List.range n))
      (ground.famFold poly.add [] g (List.range n)) :=
  ground.famFold_congr_members_ov poly.oneValue poly.add []
    (fun x => poly.oneValue_refl x)
    (fun h1 h2 => poly.add_congr h1 h2) f g (List.range n)
    (fun k hk => h k (by
      rw [ground.countOf_range k n] at hk
      by_cases hkn : k < n
      · exact hkn
      · rw [if_neg hkn] at hk
        exact absurd hk (Nat.lt_irrefl 0)))

/-- The coefficient fold against a polynomial family is the sum
fold of the one-member products over the shared keys
(`poly.scaleDot_getAt` at the one-member factors). -/
private theorem scaleDot_famFold (n : Nat) (cs : List BPair)
    (ps : List Poly) (hc : cs.length = n) (hp : ps.length = n) :
    poly.oneValue (poly.scaleDot cs ps)
      (ground.famFold poly.add []
        (fun k => poly.mul (ground.getAt ([] : Poly) ps k)
          [ground.getAt BPair.unit cs k]) (List.range n)) := by
  rw [poly.scaleDot_getAt cs ps (hc.trans hp.symm), hc]
  exact famFoldP_congr_range _ _ n (fun k _ => poly.scaleP_single _ _)


/-- The embedded scalar list's entry is the one-member polynomial
at the datum's own entry. -/
private theorem getAt_embedP (M : Mat) (i j : Nat) (hi : i < M.length)
    (hj : j < (ground.getAt ([] : List BPair) M i).length) :
    ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (elim.embedP M) i) j
      = [ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) M i) j] := by
  show ground.getAt ([] : Poly)
      (ground.getAt ([] : List Poly)
        (M.map (fun r => r.map (fun b => ([b] : poly.Poly)))) i) j = _
  rw [ground.getAt_map ([] : List BPair) ([] : List Poly) _ M i hi,
    ground.getAt_map BPair.unit ([] : Poly) _ _ j hj]


/-- The site datum's rows read the level pair's own order. -/
private theorem zMat_rows : ∀ (H G : Mat) (o : Nat),
    rowsLen o H → rowsLen o G → rowsLen o (zMat H G)
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, _, _ => trivial
  | r :: H, s :: G, o, hH, hG =>
    ⟨ground.length_zipWith (fun h g => [BPair.swap h, g]) r s o hH.1 hG.1,
     zMat_rows H G o hH.2 hG.2⟩

/-- The congruence's entry is the exchanged lists' product's own:
`Tᵀ Z T` entry by entry at the polynomial carrier, the scalar
factors entering as their one-member polynomials. -/
private theorem congrZ_entry (T : Mat) (Z : PMat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T)
    (hZl : Z.length = o) (hZr : rowsLen o Z)
    (i j : Nat) (hi : i < o) (hj : j < o) :
    poly.oneValue
      (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (congrZ T Z) i) j)
      (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly)
          (elim.matMulO poly.polyOps (elim.embedP (transposeM T))
            (elim.matMulO poly.polyOps Z (elim.embedP T))) i) j) := by
  have hTtl : (transposeM T).length = o := transposeLen T hTr hTl
  have hTtr : rowsLen o (transposeM T) :=
    rowsLen_cast hTl (rowsLen_transposeM T)
  have hEl : (elim.embedP T).length = o := (ground.length_map _ T).trans hTl
  have hEr : rowsLen o (elim.embedP T) := rowsLen_mapRowsO _ T o hTr
  have hEtl : (elim.embedP (transposeM T)).length = o :=
    (ground.length_map _ _).trans hTtl
  have hEtr : rowsLen o (elim.embedP (transposeM T)) :=
    rowsLen_mapRowsO _ (transposeM T) o hTtr
  have hwE : ((elim.embedP T).headD []).length = o := elim.headD_len_of _ o hEl hEr
  have hMl : (elim.matMulO poly.polyOps Z (elim.embedP T)).length = o :=
    (ground.length_map _ Z).trans hZl
  have hMr : rowsLen o (elim.matMulO poly.polyOps Z (elim.embedP T)) :=
    elim.rowsLen_matMulO poly.polyOps Z (elim.embedP T) o hwE
  have hwM : ((elim.matMulO poly.polyOps Z (elim.embedP T)).headD
      []).length = o := elim.headD_len_of _ o hMl hMr
  have hZTl : (Z.map (fun r => (transposeM T).map
      (fun c => poly.scaleDot c r))).length = o :=
    (ground.length_map _ Z).trans hZl
  have hZTr : rowsLen o (Z.map (fun r => (transposeM T).map
      (fun c => poly.scaleDot c r))) :=
    rowsLen_map _ o Z (fun _ _ => (ground.length_map _ _).trans hTtl)
  have hPt : ptranspose (Z.map (fun r => (transposeM T).map
        (fun c => poly.scaleDot c r)))
      = ptransGo o (Z.map (fun r => (transposeM T).map
        (fun c => poly.scaleDot c r))) :=
    ptranspose_fuel _ o hZTl hZTr
  have hPtl : (ptranspose (Z.map (fun r => (transposeM T).map
      (fun c => poly.scaleDot c r)))).length = o := by
    rw [hPt, length_ptransGo]
  have hrowi : (ground.getAt ([] : List BPair) (transposeM T) i).length
      = o := rowsLen_getAt (transposeM T) i hTtr (by rw [hTtl]; exact hi)
  have hrowj : (ground.getAt ([] : List BPair) (transposeM T) j).length
      = o := rowsLen_getAt (transposeM T) j hTtr (by rw [hTtl]; exact hj)
  have hL1 : ground.getAt ([] : List Poly) (congrZ T Z) i
      = (ptranspose (Z.map (fun r => (transposeM T).map
          (fun c => poly.scaleDot c r)))).map
        (fun colj => poly.scaleDot
          (ground.getAt ([] : List BPair) (transposeM T) i) colj) :=
    ground.getAt_map ([] : List BPair) ([] : List Poly) _ (transposeM T) i
      (by rw [hTtl]; exact hi)
  have hL2 : ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly) (congrZ T Z) i) j
      = poly.scaleDot (ground.getAt ([] : List BPair) (transposeM T) i)
        (ground.getAt ([] : List Poly)
          (ptranspose (Z.map (fun r => (transposeM T).map
            (fun c => poly.scaleDot c r)))) j) := by
    rw [hL1]
    exact ground.getAt_map ([] : List Poly) ([] : Poly) _ _ j
      (by rw [hPtl]; exact hj)
  have hcolj : (ground.getAt ([] : List Poly)
      (ptranspose (Z.map (fun r => (transposeM T).map
        (fun c => poly.scaleDot c r)))) j).length = o := by
    rw [hPt]
    exact rowsLen_ptransGo o _ o hZTl j hj
  rw [hL2]
  refine poly.oneValue_trans
    (scaleDot_famFold o _ _ hrowi hcolj) ?_
  refine poly.oneValue_symm (poly.oneValue_trans
    (elim.matMulP_entry (elim.embedP (transposeM T))
      (elim.matMulO poly.polyOps Z (elim.embedP T)) o o hEtr hwM i j
      (by rw [hEtl]; exact hi) hj) ?_)
  refine famFoldP_congr_range _ _ o (fun s hs => ?_)
  have hsZ : s < Z.length := by rw [hZl]; exact hs
  have hrowZ : (ground.getAt ([] : List Poly) Z s).length = o :=
    rowsLen_getAt Z s hZr hsZ
  have he1 : ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly)
          (elim.embedP (transposeM T)) i) s
      = [ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (transposeM T) i) s] :=
    getAt_embedP (transposeM T) i s (by rw [hTtl]; exact hi)
      (by rw [hrowi]; exact hs)
  have he2 : ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly)
          (ptranspose (Z.map (fun r => (transposeM T).map
            (fun c => poly.scaleDot c r)))) j) s
      = poly.scaleDot (ground.getAt ([] : List BPair) (transposeM T) j)
        (ground.getAt ([] : List Poly) Z s) := by
    rw [hPt, getAt_ptransGo o _ j s hj (by rw [hZTl]; exact hs),
      ground.getAt_map ([] : List Poly) ([] : List Poly) _ Z s hsZ]
    exact ground.getAt_map ([] : List BPair) ([] : Poly) _ (transposeM T) j
      (by rw [hTtl]; exact hj)
  have he3 : poly.oneValue
      (poly.scaleDot (ground.getAt ([] : List BPair) (transposeM T) j)
        (ground.getAt ([] : List Poly) Z s))
      (ground.getAt ([] : Poly)
        (ground.getAt ([] : List Poly)
          (elim.matMulO poly.polyOps Z (elim.embedP T)) s) j) := by
    refine poly.oneValue_trans
      (scaleDot_famFold o _ _ hrowj hrowZ) ?_
    refine poly.oneValue_symm (poly.oneValue_trans
      (elim.matMulP_entry Z (elim.embedP T) o o hZr hwE s j hsZ hj) ?_)
    refine famFoldP_congr_range _ _ o (fun t ht => ?_)
    have htT : t < T.length := by rw [hTl]; exact ht
    have hE1 : ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly) (elim.embedP T) t) j
        = [ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) T t) j] :=
      getAt_embedP T t j htT
        (by rw [rowsLen_getAt T t hTr htT]; exact hj)
    have hE2 : ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) (transposeM T) j) t
        = ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) T t) j :=
      getAt_transposeM BPair.unit T hTr j t hj htT
    rw [hE1, hE2]
    exact poly.oneValue_refl _
  rw [he1, he2]
  exact poly.oneValue_trans
    (poly.mul_comm _ _)
    (poly.mul_congr_left (poly.oneValue_symm he3) _)

/-- The congruence identity's determinant: the exchanged lists'
product collects to the descent's determinant squared against the
pencil polynomial (`lem:inertia`; `def:elim`). -/
private theorem pminor_congrZ {o : Nat} (H G : Mat) (T : SqMat o)
    (hH : sqAt H o) (hG : sqAt G o) :
    poly.oneValue (pminor (congrZ T.val (zMat H G)))
      (poly.mul [detL T.val * detL T.val] (charPoly H G)) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hTr : rowsLen o T.val := rowsLen_of_sqAt T.shape
  have hTtl : (transposeM T.val).length = o := transposeLen T.val hTr hTl
  have hTtr : rowsLen o (transposeM T.val) :=
    rowsLen_cast hTl (rowsLen_transposeM T.val)
  have hZl : (zMat H G).length = o :=
    zMat_len H G o (sqAt_len hH) (sqAt_len hG)
  have hZr : rowsLen o (zMat H G) :=
    zMat_rows H G o (rowsLen_of_sqAt hH) (rowsLen_of_sqAt hG)
  have hEl : (elim.embedP T.val).length = o :=
    (ground.length_map _ T.val).trans hTl
  have hEr : rowsLen o (elim.embedP T.val) :=
    rowsLen_mapRowsO _ T.val o hTr
  have hEtl : (elim.embedP (transposeM T.val)).length = o :=
    (ground.length_map _ _).trans hTtl
  have hEtr : rowsLen o (elim.embedP (transposeM T.val)) :=
    rowsLen_mapRowsO _ (transposeM T.val) o hTtr
  have hwE : ((elim.embedP T.val).headD []).length = o :=
    elim.headD_len_of _ o hEl hEr
  have hMl : (elim.matMulO poly.polyOps (zMat H G)
      (elim.embedP T.val)).length = o := (ground.length_map _ _).trans hZl
  have hMr : rowsLen o (elim.matMulO poly.polyOps (zMat H G)
      (elim.embedP T.val)) := elim.rowsLen_matMulO poly.polyOps _ _ o hwE
  have hwM : ((elim.matMulO poly.polyOps (zMat H G)
      (elim.embedP T.val)).headD []).length = o := elim.headD_len_of _ o hMl hMr
  have h1 : poly.oneValue (pminor (congrZ T.val (zMat H G)))
      (pminor (elim.matMulO poly.polyOps
        (elim.embedP (transposeM T.val))
        (elim.matMulO poly.polyOps (zMat H G) (elim.embedP T.val)))) :=
    elim.minorP_congr _ _ o
      ((congrZ_len T.val (zMat H G)).trans hTtl)
      ((ground.length_map _ _).trans hEtl)
      (congrZ_rows T.val (zMat H G) o hTl hTr hZl)
      (elim.rowsLen_matMulO poly.polyOps _ _ o hwM)
      (fun a ha b hb =>
        congrZ_entry T.val (zMat H G) o hTl hTr hZl hZr a b ha hb)
  have h2 : poly.oneValue (pminor (elim.matMulO poly.polyOps
        (elim.embedP (transposeM T.val))
        (elim.matMulO poly.polyOps (zMat H G) (elim.embedP T.val))))
      (poly.mul (pminor (elim.embedP (transposeM T.val)))
        (pminor (elim.matMulO poly.polyOps (zMat H G)
          (elim.embedP T.val)))) :=
    elim.pminor_mul _ _ o hEtl hEtr hMl hMr
  have h3 : poly.oneValue (pminor (elim.matMulO poly.polyOps (zMat H G)
        (elim.embedP T.val)))
      (poly.mul (charPoly H G) (pminor (elim.embedP T.val))) :=
    elim.pminor_mul _ _ o hZl hZr hEl hEr
  have h4 : poly.oneValue (pminor (elim.embedP T.val)) [detL T.val] :=
    elim.pminor_embed T.val o T.shape
  have h5 : poly.oneValue (pminor (elim.embedP (transposeM T.val)))
      [detL T.val] := by
    have h5' := elim.pminor_embed (transposeM T.val) o (sqAt_of hTtl hTtr)
    rw [detL_transpose T.val (rowsLen_cast hTl.symm hTr)] at h5'
    exact h5'
  refine poly.oneValue_trans h1 (poly.oneValue_trans h2 ?_)
  refine poly.oneValue_trans (poly.mul_congr_left h5 _) ?_
  refine poly.oneValue_trans (poly.mul_congr _ h3) ?_
  refine poly.oneValue_trans (poly.mul_congr _ (poly.mul_congr _ h4)) ?_
  refine poly.oneValue_trans (poly.mul_congr _
    (poly.mul_comm (charPoly H G) [detL T.val])) ?_
  exact mulCollect (detL T.val) (detL T.val) (charPoly H G)

/-- The scaled factors' fold: the scales collect onto one
one-member factor with the stated factors left. -/
private theorem prodScale {α : Type} (g : α → BPair) (F : α → Poly) :
    ∀ (l : List α) (acc : Poly) (s : BPair),
    poly.oneValue
      ((l.map (fun r => poly.scaleP (g r) (F r))).foldl poly.mul
        (poly.mul [s] acc))
      (poly.mul [l.foldl (fun a r => a * g r) s]
        ((l.map F).foldl poly.mul acc))
  | [], _, _ => poly.oneValue_refl _
  | r :: t, acc, s => by
    refine poly.oneValue_trans (ground.foldl_congr_seed
      poly.oneValue poly.mul (fun p h => poly.mul_congr_left h p)
      (t.map (fun u => poly.scaleP (g u) (F u))) ?_)
      (prodScale g F t (poly.mul acc (F r)) (s * g r))
    refine poly.oneValue_trans
      (poly.mul_congr _ (poly.scaleP_single (g r) (F r))) ?_
    refine poly.oneValue_trans
      (poly.mul_congr _ (poly.mul_comm (F r) [g r])) ?_
    refine poly.oneValue_trans
      (poly.mul_assoc [s] acc (poly.mul [g r] (F r))) ?_
    refine poly.oneValue_trans
      (poly.mul_congr [s] (poly.mul_left_comm acc [g r] (F r))) ?_
    exact mulCollect s (g r) (poly.mul acc (F r))

/-- The diagonal side's minor: the diagonal blocks' product with
the scales withdrawn to one one-member factor. -/
private theorem pminor_pdiag_read {α : Type} (g : α → BPair)
    (F : α → Poly) (l : List α) :
    poly.oneValue
      (pminor (pdiag (l.map (fun r => poly.scaleP (g r) (F r)))))
      (poly.mul [l.foldl (fun a r => a * g r) (BPair.ofNat 1)]
        (poly.prodFold (l.map F))) := by
  refine poly.oneValue_trans
    (elim.pminor_diag (l.map (fun r => poly.scaleP (g r) (F r)))) ?_
  refine poly.oneValue_trans
    (ground.foldl_congr_seed poly.oneValue poly.mul
      (fun p h => poly.mul_congr_left h p) _ (poly.oneValue_symm
      (poly.oneValue_trans
        (mulSingles (BPair.ofNat 1) (BPair.ofPos Pos.one))
        ⟨BPair.ofNat_one_mul (BPair.ofPos Pos.one), trivial⟩))) ?_
  exact prodScale g F l poly.one (BPair.ofNat 1)

/-- The one-member site's fold rides the ground product's own. -/
private theorem ofPos_fold {α : Type} (d : α → Pos) :
    ∀ (l : List α) (s : Pos),
    (BPair.ofPos (l.foldl (fun a r => a * d r) s)).oneValue
      (l.foldl (fun a r => a * BPair.ofPos (d r)) (BPair.ofPos s))
  | [], _ => BPair.oneValue_refl _
  | r :: t, s =>
    BPair.oneValue_trans (ofPos_fold d t (s * d r))
      (ground.foldl_congr_seed BPair.oneValue
        (fun x u => x * BPair.ofPos (d u))
        (fun _ h => BPair.mul_congr_left h) t
        (BPair.oneValue_symm (BPair.ofPos_mul s (d r))))

/-- The diagonal's own fold splits into the scales' product against
the roots' clearings. -/
private theorem foldSplit {α : Type} (g : α → BPair) (d : α → Pos) :
    ∀ (l : List α) (s1 s2 : BPair),
    ((l.map (fun r => (g r * BPair.ofPos (d r)).norm)).foldl
        (fun a e => a * e) (s1 * s2)).oneValue
      ((l.foldl (fun a r => a * g r) s1)
        * (l.foldl (fun a r => a * BPair.ofPos (d r)) s2))
  | [], _, _ => BPair.oneValue_refl _
  | r :: t, s1, s2 => by
    refine BPair.oneValue_trans ?_
      (foldSplit g d t (s1 * g r) (s2 * BPair.ofPos (d r)))
    refine ground.foldl_congr_seed BPair.oneValue
      (fun x e => x * e) (fun e h => BPair.mul_congr_left h)
      (t.map (fun u => (g u * BPair.ofPos (d u)).norm)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (s1 * s2))
        (BPair.norm_oneValue (g r * BPair.ofPos (d r)))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_assoc s1 s2 (g r * BPair.ofPos (d r)),
      BPair.mul_left_comm s2 (g r) (BPair.ofPos (d r)),
      ← BPair.mul_assoc s1 (g r) (s2 * BPair.ofPos (d r))]

/-- The shared clearing withdraws: at a factor off equal members,
two one-member scales read one value exactly where the cleared
identity and the scalars' own read do. -/
private theorem withdrawScale (c a b g : BPair) (X P : Poly)
    (hc : ¬ c.oneValue BPair.unit)
    (hstar : poly.oneValue (poly.mul [c] X) (poly.mul [g] P))
    (hkey : (a * g).oneValue (c * b)) :
    poly.oneValue (poly.mul [a] X) (poly.mul [b] P) := by
  refine elim.oneValue_unscale c hc _ _ ?_
  refine poly.oneValue_trans
    (poly.oneValue_symm (mulVecScale c (poly.mul [a] X)))
    (poly.oneValue_trans ?_ (mulVecScale c (poly.mul [b] P)))
  refine poly.oneValue_trans (mulCollect c a X) ?_
  refine poly.oneValue_trans
    (poly.mul_congr_left
      (show poly.oneValue [c * a] [a * c] from
        ⟨BPair.oneValue_of_eq (BPair.mul_comm c a), trivial⟩) X) ?_
  refine poly.oneValue_trans (poly.oneValue_symm (mulCollect a c X)) ?_
  refine poly.oneValue_trans (poly.mul_congr _ hstar) ?_
  refine poly.oneValue_trans (mulCollect a g P) ?_
  refine poly.oneValue_trans
    (poly.mul_congr_left
      (show poly.oneValue [a * g] [c * b] from ⟨hkey, trivial⟩) P) ?_
  exact poly.oneValue_symm (mulCollect c b P)

/-- The factorization read at a root list carried from the split
certificate's own: the mapped list's two folds are the statement's
own reads. -/
private theorem chiRead_of_mapped (H G : Mat)
    (l : List (BPair × Pos × BPair))
    (hx : poly.oneValue
      (poly.mul [BPair.ofPos ((l.map (fun r => (r.1, r.2.1))).foldl
        (fun a r => a * r.2) Pos.one)] (charPoly H G))
      (poly.mul [minor G]
        (poly.prodFold ((l.map (fun r => (r.1, r.2.1))).map
          (fun r => linFac r.1 r.2))))) :
    chiRead H G (l.map (fun r => (r.1, r.2.1))) := hx

/-- `lem:split`'s factorization clause: the completed congruence
returns the factorization read.  The congruence identity's
determinant collects the product read at the exchanged lists to
`det S_χ² χ` against the diagonal blocks' product
`Π_j ⟨x : ε_j⟩ g_j`; the identity's linear coefficient,
`S_χᵀ G S_χ` at the diagonal of the scales, collects its own
determinants to `det S_χ² det G` against `Π_j g_j`; and the shared
factor `det S_χ²`, off equal members at the unit congruence,
withdraws at the products' one value key by key — the displayed
factorization is the congruence certificate's own read. -/
theorem diag_chiRead {o : Nat} (H G : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : diagRead H G T Tw l) :
    chiRead H G (l.map (fun r => (r.1, r.2.1))) := by
  obtain ⟨hH, hG, ⟨hdet, _, _⟩, hcong, _⟩ := hd
  have hTl : T.val.length = o := SqMat.rows T
  have hTr : rowsLen o T.val := rowsLen_of_sqAt T.shape
  have hTtl : (transposeM T.val).length = o := transposeLen T.val hTr hTl
  have hTtr : rowsLen o (transposeM T.val) :=
    rowsLen_cast hTl (rowsLen_transposeM T.val)
  have hGl : G.length = o := sqAt_len hG
  have hlo : l.length = o := by
    have h1 := ground.matched_length hcong
    rw [show (congrZ T.val (zMat H G)).length
          = (transposeM T.val).length from ground.length_map _ _, hTtl,
      show (pdiag (l.map
            (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1)))).length
          = (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))).length
        from ground.length_mapRange _ _,
      ground.length_map] at h1
    exact h1.symm
  have hdsl : (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))).length
      = o := (ground.length_map _ l).trans hlo
  have hcl : (congrZ T.val (zMat H G)).length = o :=
    (congrZ_len T.val (zMat H G)).trans hTtl
  have hcr : rowsLen o (congrZ T.val (zMat H G)) :=
    congrZ_rows T.val (zMat H G) o hTl hTr
      (zMat_len H G o (sqAt_len hH) hGl)
  have hdr : rowsLen o (pdiag
      (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1)))) := by
    rw [← hdsl]
    exact elim.diagO_rows poly.polyOps
      (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1)))
  have hminor : poly.oneValue (pminor (congrZ T.val (zMat H G)))
      (pminor (pdiag
        (l.map (fun r => poly.scaleP r.2.2 (linFac r.1 r.2.1))))) :=
    elim.minorP_congr _ _ o hcl
      ((elim.diagO_len poly.polyOps _).trans hdsl) hcr hdr
      (fun a ha b hb =>
        ground.matched_entry ([] : Poly)
          (ground.matched_entry ([] : List Poly) hcong a
            (by rw [hcl]; exact ha))
          b (by
            rw [rowsLen_getAt _ a hcr (by rw [hcl]; exact ha)]
            exact hb))
  have hstar : poly.oneValue
      (poly.mul [detL T.val * detL T.val] (charPoly H G))
      (poly.mul [l.foldl (fun a r => a * r.2.2) (BPair.ofNat 1)]
        (poly.prodFold (l.map (fun r => linFac r.1 r.2.1)))) :=
    poly.oneValue_trans
      (poly.oneValue_symm (pminor_congrZ H G T hH hG))
      (poly.oneValue_trans hminor
        (pminor_pdiag_read (fun r : BPair × Pos × BPair => r.2.2)
          (fun r => linFac r.1 r.2.1) l))
  have hDG : matOneValue (matMul (transposeM T.val) (matMul G T.val))
      (diagM (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))) := by
    have h2 := pcfOne _ _ hcong 1
    rw [pcf_pdiag, cfmap_lin] at h2
    have h3 : matOneValue (pcf 1 (congrZ T.val (zMat H G)))
        (matMul (transposeM T.val) (matMul G T.val)) := by
      rw [← plin_pcf]; exact plin_congrZ H G T hH hG
    exact matOne_trans (matOne_symm h3) h2
  have hGTl : (matMul G T.val).length = o :=
    (length_matMul G T.val).trans hGl
  have hGTr : rowsLen o (matMul G T.val) :=
    rowsLen_cast hTtl (rowsLen_matMul G T.val)
  have hPl : (matMul (transposeM T.val) (matMul G T.val)).length = o :=
    (length_matMul _ _).trans hTtl
  have hdiagl : (diagM
      (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))).length = o := by
    rw [diagM_len, ground.length_map]
    exact hlo
  have hdetprod : (detL (matMul (transposeM T.val)
      (matMul G T.val))).oneValue
      (detL T.val * (detL G * detL T.val)) := by
    refine BPair.oneValue_trans
      (detL_mul (transposeM T.val) (matMul G T.val) o
        (sqAt_of hTtl hTtr) (sqAt_of hGTl hGTr)) ?_
    rw [detL_transpose T.val (rowsLen_cast hTl.symm hTr)]
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (detL_mul G T.val o hG T.shape)
  have hscalar : (detL T.val * (detL G * detL T.val)).oneValue
      ((l.foldl (fun a r => a * r.2.2) (BPair.ofNat 1))
        * (l.foldl (fun a r => a * BPair.ofPos r.2.1) (BPair.ofNat 1))) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm hdetprod) ?_
    refine BPair.oneValue_trans
      (detL_congr_letters _ _ (hPl.trans hdiagl.symm) (fun a ha b _ =>
        poly.oneValue_getAt b
          (ground.matched_entry ([] : List BPair) hDG a ha))) ?_
    refine BPair.oneValue_trans (detL_diag _) ?_
    refine BPair.oneValue_trans
      (ground.foldl_congr_seed BPair.oneValue (fun x e => x * e)
        (fun _ h => BPair.mul_congr_left h) _
        (BPair.oneValue_symm (BPair.mul_ofNat_one (BPair.ofNat 1)))) ?_
    exact foldSplit (fun r : BPair × Pos × BPair => r.2.2)
      (fun r => r.2.1) l (BPair.ofNat 1) (BPair.ofNat 1)
  have hcU : ¬ (detL T.val * detL T.val).oneValue BPair.unit := by
    intro hc
    have hdT : (detL T.val).oneValue BPair.unit :=
      match (ground.BPair.mul_unit_iff (detL T.val) (detL T.val)).1 hc with
      | Or.inl h => h
      | Or.inr h => h
    exact hdet (BPair.oneValue_trans
      (elim.minor_detL T.val (rowsLen_cast hTl.symm hTr)) hdT)
  have hswap : detL T.val * (detL G * detL T.val)
      = detL T.val * detL T.val * detL G := by
    rw [BPair.mul_assoc (detL T.val) (detL T.val) (detL G),
      BPair.mul_comm (detL G) (detL T.val)]
  have hkey : ((BPair.ofPos (l.foldl (fun a r => a * r.2.1) Pos.one))
      * (l.foldl (fun a r => a * r.2.2) (BPair.ofNat 1))).oneValue
      (detL T.val * detL T.val * minor G) :=
    BPair.oneValue_trans
      (BPair.mul_congr_left
        (ofPos_fold (fun r : BPair × Pos × BPair => r.2.1) l Pos.one))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
        (BPair.oneValue_trans (BPair.oneValue_symm hscalar)
          (BPair.oneValue_trans (BPair.oneValue_of_eq hswap)
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_symm (elim.minor_detL G
                (rowsLen_cast hGl.symm (rowsLen_of_sqAt hG))))))))
  have hfoldEq : (l.map (fun r => (r.1, r.2.1))).foldl
        (fun a (r : BPair × Pos) => a * r.2) Pos.one
      = l.foldl (fun a r => a * r.2.1) Pos.one :=
    ground.foldl_map _ _ l Pos.one
  have hmapEq : (l.map (fun r => (r.1, r.2.1))).map
        (fun r : BPair × Pos => linFac r.1 r.2)
      = l.map (fun r => linFac r.1 r.2.1) := ground.map_map _ _ l
  refine chiRead_of_mapped H G l ?_
  rw [hfoldEq, hmapEq]
  exact withdrawScale _ _ _ _ _ _ hcU hstar hkey

/-- The resultant's kernel read, the cross pair: `(A, B)` at the
stated degrees with `A p` the balance partner of `B q`, off the
pair's own unit — the resultant reads equal members exactly at an
occupied cross pair. -/
def crossRead (p q A B : Poly) : Prop :=
  poly.unitTail (poly.add (poly.mul A p) (poly.mul B q))
  ∧ ¬ (poly.unitTail A ∧ poly.unitTail B)
  ∧ A.length + 1 ≤ q.length ∧ B.length + 1 ≤ p.length

instance (p q A B : Poly) : Decidable (crossRead p q A B) :=
  @instDecidableAnd _ _ (poly.decUnitTail _)
    (@instDecidableAnd _ _
      (@instDecidableNot _
        (@instDecidableAnd _ _ (poly.decUnitTail _) (poly.decUnitTail _)))
      (inferInstanceAs (Decidable (_ ∧ _))))

/-! The two-variable pencil tier at the iterated carrier
(`poly.PPoly`): the outer pair's site datum over polynomial
entries and its first-row fold, `thm:trigpencil`'s symbol the
consumer. -/

/-- A matrix over the iterated carrier. -/
abbrev PPMat := List (List poly.PPoly)

/-- The outer pair's site datum at polynomial entries:
`Z(x) = x G - H` entrywise at the coefficient carrier, degree one
in the outer variable. -/
def ppzMat (H G : PMat) : PPMat :=
  List.zipWith (List.zipWith (fun h g => [poly.neg h, g])) H G

/-- The first-row fold at the iterated carrier's entries, the
representative map entrywise with the collected sum untouched. -/
def ppminor (m : PPMat) : poly.PPoly :=
  elim.minorO (poly.polyO polyOps) poly.pnormP id m

end split
