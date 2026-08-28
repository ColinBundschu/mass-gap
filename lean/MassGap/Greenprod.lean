import MassGap.Inertia
/-!
`lem:greenprod` — the slab pivots, the counts, and the Green
products, at the block-tridiagonal slab split.  The slab data
`A_i`, `B_i` enter as the pencil's own integer blocks; the
recursions' outputs are stage elements and enter cleared of their
second members by the homogeneity principle, each a pair of an
integer matrix with its stated clearing — `lem:split`'s
`(BPair × Pos)` root data the precedent — every identity
cross-multiplied through the clearing (`oneValueQ`, `mulQ`, `addQ`
at `inertia.matScale`).  The tail recursion `X_L = A_L`,
`X_{i+1} R_{i+1} = B_iᵀ`, `X_i + B_i R_{i+1} = A_i` is `tailRead`;
the head recursion `Y_1 = A_1`, `Y_i C_i = B_i`,
`Y_{i+1} + B_iᵀ C_i = A_{i+1}` is `headRead`, each solve's witness
a stated datum with the recursion's joins the decidable reads; the
transfer factor is the memberwise swap of the witness (`transfer`),
with `Y_k T_k + B_k` the sum's unit the proven join
(`transfer_null`); and the join's datum `Z_j` at
`Z_j + A_j = X_j + Y_j` is `zJoinQ`.  Clause (iii)'s Green solve is
the blockwise read: the tridiagonal rows (`solveRows`, `solveRead`),
the source's support (`supportAt`), the corner solve at `Z_j`, and
the two transfer telescopes, `u_i = T_i u_{i+1}` below the source
at the head witnesses and `u_{i+1} = Ť_i u_i` beyond it at the tail
witnesses (`teleDown`, `teleUp`), bundled at the slab shape
(`greenRead`, `slabShape` at `elim.rectAt`).  Clause (ii)'s two
splits close at the assembled matrix (`assemble`): the count split
`rev(S) = Σ_i rev(X_i)` is the general theorem `countSplit` — at
the tail recursion's certificate, every split of the assembled
datum reads the pivots' fold, the coherence read `countSplitRead`
its consumable spelling (`countSplit_read`) — and the determinant
split `det S = Π_i det X_i` reads at the cleared minors (`minorQ`,
`detProdRead`), the batteries' instances the pins.  The count
split's engine is the telescoped families: from a seed at one slab
the tail witnesses telescope downward (`liftMat`, each step the
witness's swapped action at the accumulated clearings), the
assembled matrix reads the lifted vector at the slab's own pivot
alone, and the slabs' lower and complement lists lift to the two
families whose combinations price the whole form (`lowFam`,
`complFam`, `famRead`), `lem:inertia`'s forcing clauses closing
the two bounds at one call each; the cross pairings die at the
split's own symmetry (`inertia.splitRead_symm`), so the theorem
binds the certificate reads alone.  A slab split's parts each hold
a key (`slabShape`'s occupancy conjunct): at a vacant slab the
walk's occupancy read refuses at that step, the committed refusal's
read.  Clause (i) — the Schur complement of
the tail maps `A_i` to `X_i` and fixes every other block, so one
recursion datum holds the whole tail — is the recursions'
derivation, the one-slab arithmetic the tier's own reads.
-/

namespace greenprod
open ground poly elim inertia

/-- A cleared matrix datum: the integer matrix at its stated
clearing, a stage element's cross-multiplied entry. -/
abbrev MatQ := Mat × Pos

/-- A cleared vector datum at its stated clearing. -/
abbrev VecQ := List BPair × Pos

/-- An integer matrix's cleared entry at the unit clearing. -/
def ofM (m : Mat) : MatQ := (m, .one)

/-- Two cleared data read one value at the cross-scaled
matrices. -/
def oneValueQ (a b : MatQ) : Prop :=
  matOneValue (matScale b.2 a.1) (matScale a.2 b.1)

instance (a b : MatQ) : Decidable (oneValueQ a b) := decMatOneValue _ _

/-- The cleared product, the clearings multiplying. -/
def mulQ (a b : MatQ) : MatQ := (matMul a.1 b.1, a.2 * b.2)

/-- The cleared sum at the cross-scaled matrices. -/
def addQ (a b : MatQ) : MatQ :=
  (matAdd (matScale b.2 a.1) (matScale a.2 b.1), a.2 * b.2)

/-- The memberwise swap at the matrix datum. -/
def swapQ (a : MatQ) : MatQ := (matSwap a.1, a.2)

/-- The entrywise rescaling of an integer vector. -/
def vecScale (w : Pos) (v : List BPair) : List BPair :=
  v.map (fun x => x.scale w)

/-- The positive rescaling is the balance carrier's scale at the
datum's own entry, entry by entry. -/
theorem vecScale_ofPos (w : Pos) : ∀ v : List BPair,
    poly.oneValue (vecScale w v) (elim.vecScale (BPair.ofPos w) v)
  | [] => trivial
  | x :: v => ⟨BPair.oneValue_symm (BPair.ofPos_scale w x), vecScale_ofPos w v⟩

/-- Two cleared vectors read one value at the cross-scaled
vectors. -/
def vOneValueQ (a b : VecQ) : Prop :=
  poly.oneValue (vecScale b.2 a.1) (vecScale a.2 b.1)

instance (a b : VecQ) : Decidable (vOneValueQ a b) :=
  poly.decOneValue _ _

/-- The cleared vectors' sum at the cross-scaled vectors. -/
def vAddQ (a b : VecQ) : VecQ :=
  (poly.add (vecScale b.2 a.1) (vecScale a.2 b.1), a.2 * b.2)

/-- A cleared matrix against a cleared vector. -/
def appQ (m : MatQ) (v : VecQ) : VecQ :=
  (matVec m.1 v.1, m.2 * v.2)

/-- An integer matrix against a cleared vector, the clearing
kept. -/
def appM (m : Mat) (v : VecQ) : VecQ := (matVec m v.1, v.2)

/-- The vacant cleared matrix datum, `getAt`'s off-range read at a
list of cleared matrices. -/
def dM : MatQ := ([], .one)

/-- The vacant cleared vector datum, `getAt`'s off-range read at a
list of cleared vectors. -/
private def dV : VecQ := ([], .one)

/-! The slab data: the diagonal blocks `A_1, …, A_L` and the
off-diagonal blocks `B_1, …, B_{L-1}`, the pencil's own integer
entries, with the shape read at the stated slab orders. -/

/-- The slab walk: per step the diagonal block square at its
occupied order — a split's parts each hold a key — with the off
block rectangular at the neighbor pair, the last slab's arm the
square block alone. -/
def slabShape : List Mat → List Mat → List Nat → Prop
  | [], _, _ => False
  | _ :: _, _, [] => False
  | [A], [], [k] => 0 < k ∧ sqAt A k
  | [_], [], _ :: _ :: _ => False
  | [_], _ :: _, _ :: _ => False
  | _ :: _ :: _, [], _ :: _ => False
  | _ :: _ :: _, _ :: _, [_] => False
  | A :: A' :: As, B :: Bs, k :: k' :: ns =>
      0 < k ∧ sqAt A k ∧ rectAt B k k'
      ∧ slabShape (A' :: As) Bs (k' :: ns)

def decSlabShape : ∀ (diag off : List Mat) (ns : List Nat),
    Decidable (slabShape diag off ns)
  | [], _, _ => isFalse (fun h => h)
  | _ :: _, _, [] => isFalse (fun h => h)
  | [_], [], [_] => inferInstanceAs (Decidable (_ ∧ _))
  | [_], [], _ :: _ :: _ => isFalse (fun h => h)
  | [_], _ :: _, [_] => isFalse (fun h => h)
  | [_], _ :: _, _ :: _ :: _ => isFalse (fun h => h)
  | _ :: _ :: _, [], [_] => isFalse (fun h => h)
  | _ :: _ :: _, [], _ :: _ :: _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [_] => isFalse (fun h => h)
  | _ :: A' :: As, _ :: Bs, _ :: k' :: ns =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ inferInstance
          (@instDecidableAnd _ _ inferInstance
            (decSlabShape (A' :: As) Bs (k' :: ns))))

instance (diag off : List Mat) (ns : List Nat) :
    Decidable (slabShape diag off ns) := decSlabShape diag off ns

/-- The pivots' shape walk: one square block per slab at its stated
order. -/
def qShape : List MatQ → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | X :: Xs, k :: ns => sqAt X.1 k ∧ qShape Xs ns

def decQShape : ∀ (Xs : List MatQ) (ns : List Nat),
    Decidable (qShape Xs ns)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: Xs, _ :: ns =>
      @instDecidableAnd _ _ inferInstance (decQShape Xs ns)

instance (Xs : List MatQ) (ns : List Nat) : Decidable (qShape Xs ns) :=
  decQShape Xs ns

/-- The tail witnesses' shape walk over the consecutive order
pairs: `R_{i+1}` rectangular at the successor order against the
slab's. -/
def wShapeR : List MatQ → List Nat → Prop
  | [], [] => False
  | [], [_] => True
  | [], _ :: _ :: _ => False
  | _ :: _, [] => False
  | _ :: _, [_] => False
  | R :: Rs, k :: k' :: ns => rectAt R.1 k' k ∧ wShapeR Rs (k' :: ns)

def decWShapeR : ∀ (Rs : List MatQ) (ns : List Nat),
    Decidable (wShapeR Rs ns)
  | [], [] => isFalse (fun h => h)
  | [], [_] => isTrue trivial
  | [], _ :: _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: _, [_] => isFalse (fun h => h)
  | _ :: Rs, _ :: k' :: ns =>
      @instDecidableAnd _ _ inferInstance (decWShapeR Rs (k' :: ns))

instance (Rs : List MatQ) (ns : List Nat) : Decidable (wShapeR Rs ns) :=
  decWShapeR Rs ns

/-- The head witnesses' shape walk, the exchange orientation: `C_i`
rectangular at the slab's order against the successor's. -/
def wShapeC : List MatQ → List Nat → Prop
  | [], [] => False
  | [], [_] => True
  | [], _ :: _ :: _ => False
  | _ :: _, [] => False
  | _ :: _, [_] => False
  | C :: Cs, k :: k' :: ns => rectAt C.1 k k' ∧ wShapeC Cs (k' :: ns)

def decWShapeC : ∀ (Cs : List MatQ) (ns : List Nat),
    Decidable (wShapeC Cs ns)
  | [], [] => isFalse (fun h => h)
  | [], [_] => isTrue trivial
  | [], _ :: _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: _, [_] => isFalse (fun h => h)
  | _ :: Cs, _ :: k' :: ns =>
      @instDecidableAnd _ _ inferInstance (decWShapeC Cs (k' :: ns))

instance (Cs : List MatQ) (ns : List Nat) : Decidable (wShapeC Cs ns) :=
  decWShapeC Cs ns

/-- The gram list at the slab orders: one gram per slab, square at
its own order — the gram's slab blocks at the split
(`lem:spectator`(ii)'s `G_i`, `def:carrier`'s orthogonal sum). -/
def gramShape : List elim.Mat → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | G :: Gs, k :: ns => elim.sqAt G k ∧ gramShape Gs ns

def decGramShape : ∀ (Gs : List elim.Mat) (ns : List Nat),
    Decidable (gramShape Gs ns)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: Gs, _ :: ns =>
    @instDecidableAnd _ _ inferInstance (decGramShape Gs ns)

instance (Gs : List elim.Mat) (ns : List Nat) :
    Decidable (gramShape Gs ns) := decGramShape Gs ns

/-- The vector blocks' length walk, one length per slab. -/
def vShape : List VecQ → List Nat → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | u :: us, k :: ns => u.1.length = k ∧ vShape us ns

def decVShape : ∀ (us : List VecQ) (ns : List Nat),
    Decidable (vShape us ns)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: us, _ :: ns =>
      @instDecidableAnd _ _ inferInstance (decVShape us ns)

instance (us : List VecQ) (ns : List Nat) : Decidable (vShape us ns) :=
  decVShape us ns

/-- The block tridiagonal assembled at the slab data, the off-band
entries the sum's unit. -/
def assemble : List Mat → List Mat → Mat
  | [], _ => []
  | A :: _, [] => A
  | A :: As, B :: Bs =>
    let rest := assemble As Bs
    let restW := (rest.headD []).length
    let bt := transposeM B
    List.zipWith (fun ra rb =>
        ra ++ rb ++ List.replicate (restW - rb.length) BPair.unit) A B
      ++ (List.range rest.length).map (fun r =>
        (if r < bt.length then ground.getAt [] bt r
         else List.replicate A.length BPair.unit)
        ++ ground.getAt [] rest r)

/-- The head decimated onto the depths at or below `j`, cleared by
the pivot's clearing: the shared slab data scaled by that clearing,
with the pivot's cleared numerator the trailing block. -/
def headM (diag off : List Mat) (X : MatQ) (j : Nat) : Mat :=
  assemble
    (List.map (matScale X.2) (List.take j diag) ++ [X.1])
    (List.map (matScale X.2) (List.take j off))

/-! The two pivot recursions at solved-witness data: each witness a
stated cleared datum, the recursion's joins the decidable reads. -/

/-- The tail recursion's steps at the recursion's own walk: the
seed `X_L = A_L` the base arm, each step
`X_{i+1} R_{i+1} = B_iᵀ` naming the witness with
`X_i + B_i R_{i+1} = A_i` the join. -/
def tailSteps : List Mat → List Mat → List MatQ → List MatQ → Prop
  | [], _, _, _ => False
  | [A], [], [X], [] => oneValueQ X (ofM A)
  | [_], [], [_], _ :: _ => False
  | [_], [], [], _ => False
  | [_], [], _ :: _ :: _, _ => False
  | [_], _ :: _, _, _ => False
  | _ :: _ :: _, [], _, _ => False
  | _ :: _ :: _, _ :: _, [], _ => False
  | _ :: _ :: _, _ :: _, [_], _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [] => False
  | A :: A' :: As, B :: Bs, X :: X' :: Xs, R :: Rs =>
      (¬ (minor X'.1).oneValue BPair.unit
       ∧ oneValueQ (mulQ X' R) (ofM (transposeM B))
       ∧ oneValueQ (addQ X (mulQ (ofM B) R)) (ofM A))
      ∧ tailSteps (A' :: As) Bs (X' :: Xs) Rs

def decTailSteps : ∀ (diag off : List Mat) (Xs Rs : List MatQ),
    Decidable (tailSteps diag off Xs Rs)
  | [], _, _, _ => isFalse (fun h => h)
  | [_], [], [_], [] => inferInstanceAs (Decidable (oneValueQ _ _))
  | [_], [], [_], _ :: _ => isFalse (fun h => h)
  | [_], [], [], _ => isFalse (fun h => h)
  | [_], [], _ :: _ :: _, _ => isFalse (fun h => h)
  | [_], _ :: _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, [], _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [], _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [_], _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [] => isFalse (fun h => h)
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xs, _ :: Rs =>
      @instDecidableAnd _ _
        (@instDecidableAnd _ _ inferInstance
          (@instDecidableAnd _ _ inferInstance inferInstance))
        (decTailSteps (A' :: As) Bs (X' :: Xs) Rs)

instance (diag off : List Mat) (Xs Rs : List MatQ) :
    Decidable (tailSteps diag off Xs Rs) := decTailSteps diag off Xs Rs

/-- The tail recursion's read: the slab walk, the two shape walks,
and the recursion's own steps, one recursion datum holding the
whole tail. -/
def tailRead (diag off : List Mat) (Xs Rs : List MatQ)
    (ns : List Nat) : Prop :=
  slabShape diag off ns
  ∧ qShape Xs ns
  ∧ wShapeR Rs ns
  ∧ tailSteps diag off Xs Rs

instance (diag off : List Mat) (Xs Rs : List MatQ) (ns : List Nat) :
    Decidable (tailRead diag off Xs Rs ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The head recursion's steps at the walk forward from the seeded
head: each step `Y_i C_i = B_i` naming the witness with
`Y_{i+1} + B_iᵀ C_i = A_{i+1}` the join, the base arm vacuous at
the last slab. -/
def headSteps : List Mat → List Mat → List MatQ → List MatQ → Prop
  | [], _, _, _ => False
  | [_], [], [_], [] => True
  | [_], [], [_], _ :: _ => False
  | [_], [], [], _ => False
  | [_], [], _ :: _ :: _, _ => False
  | [_], _ :: _, _, _ => False
  | _ :: _ :: _, [], _, _ => False
  | _ :: _ :: _, _ :: _, [], _ => False
  | _ :: _ :: _, _ :: _, [_], _ => False
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [] => False
  | _ :: A' :: As, B :: Bs, Y :: Y' :: Ys, C :: Cs =>
      (¬ (minor Y.1).oneValue BPair.unit
       ∧ oneValueQ (mulQ Y C) (ofM B)
       ∧ oneValueQ (addQ Y' (mulQ (ofM (transposeM B)) C)) (ofM A'))
      ∧ headSteps (A' :: As) Bs (Y' :: Ys) Cs

def decHeadSteps : ∀ (diag off : List Mat) (Ys Cs : List MatQ),
    Decidable (headSteps diag off Ys Cs)
  | [], _, _, _ => isFalse (fun h => h)
  | [_], [], [_], [] => isTrue trivial
  | [_], [], [_], _ :: _ => isFalse (fun h => h)
  | [_], [], [], _ => isFalse (fun h => h)
  | [_], [], _ :: _ :: _, _ => isFalse (fun h => h)
  | [_], _ :: _, _, _ => isFalse (fun h => h)
  | _ :: _ :: _, [], _, _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [], _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, [_], _ => isFalse (fun h => h)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [] => isFalse (fun h => h)
  | _ :: A' :: As, _ :: Bs, _ :: Y' :: Ys, _ :: Cs =>
      @instDecidableAnd _ _
        (@instDecidableAnd _ _ inferInstance
          (@instDecidableAnd _ _ inferInstance inferInstance))
        (decHeadSteps (A' :: As) Bs (Y' :: Ys) Cs)

instance (diag off : List Mat) (Ys Cs : List MatQ) :
    Decidable (headSteps diag off Ys Cs) := decHeadSteps diag off Ys Cs

/-- The head recursion's read: the slab walk, the two shape walks,
the seed `Y_1 = A_1` at the stated head key, and the recursion's
own steps. -/
def headRead (diag off : List Mat) (Ys Cs : List MatQ)
    (ns : List Nat) : Prop :=
  slabShape diag off ns
  ∧ qShape Ys ns
  ∧ wShapeC Cs ns
  ∧ oneValueQ (ground.getAt dM Ys 0) (ofM (ground.getAt [] diag 0))
  ∧ headSteps diag off Ys Cs

instance (diag off : List Mat) (Ys Cs : List MatQ) (ns : List Nat) :
    Decidable (headRead diag off Ys Cs ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The transfer factor, the memberwise swap of the solved
witness. -/
def transfer (C : MatQ) : MatQ := swapQ C

/-- `Y T + B` reads the sum's unit at the witness's own read: the
recursion's join `Y C = B` at the swapped witness, the tex's
display. -/
theorem transfer_null (Y C : MatQ) (B : Mat)
    (h : oneValueQ (mulQ Y C) (ofM B)) :
    matNull (addQ (mulQ Y (transfer C)) (ofM B)).1 := by
  have h' : matOneValue (matMul Y.1 C.1)
      (matScale (Y.2 * C.2) B) := by
    have h2 : matOneValue (matScale Pos.one (matMul Y.1 C.1))
        (matScale (Y.2 * C.2) B) := h
    rw [matScale_one] at h2
    exact h2
  show matNull (matAdd (matScale Pos.one (matMul Y.1 (matSwap C.1)))
      (matScale (Y.2 * C.2) B))
  rw [matScale_one, matMul_swap]
  exact matNull_swap_add h'

/-- The join's datum `Z_j` at `Z_j + A_j = X_j + Y_j`, read off the
two recursions. -/
def zJoinQ (X Y : MatQ) (A : Mat) : MatQ :=
  addQ (addQ X Y) (swapQ (ofM A))

/-! The Green solve, blockwise: the tridiagonal rows, the source's
support, the corner solve, and the two transfer telescopes. -/

/-- The tridiagonal rows' walk of `S u = w`: per block the
neighbor products against the stated side, the accumulator the
prior slab's exchange term, the last row read without a trailing
neighbor. -/
def solveRows : VecQ → List Mat → List Mat → List VecQ → List VecQ →
    Prop
  | _, [], _, _, _ => False
  | p, [A], [], [u], [w] => vOneValueQ (vAddQ p (appM A u)) w
  | _, [_], [], [_], [] => False
  | _, [_], [], [_], _ :: _ :: _ => False
  | _, [_], [], [], _ => False
  | _, [_], [], _ :: _ :: _, _ => False
  | _, [_], _ :: _, _, _ => False
  | _, _ :: _ :: _, [], _, _ => False
  | _, _ :: _ :: _, _ :: _, [], _ => False
  | _, _ :: _ :: _, _ :: _, [_], _ => False
  | _, _ :: _ :: _, _ :: _, _ :: _ :: _, [] => False
  | p, A :: A' :: As, B :: Bs, u :: u' :: us, w :: ws =>
      vOneValueQ (vAddQ p (vAddQ (appM A u) (appM B u'))) w
      ∧ solveRows (appM (transposeM B) u) (A' :: As) Bs (u' :: us)
          ws

def decSolveRows : ∀ (p : VecQ) (diag off : List Mat)
    (us ws : List VecQ), Decidable (solveRows p diag off us ws)
  | _, [], _, _, _ => isFalse (fun h => h)
  | _, [_], [], [_], [_] => inferInstanceAs (Decidable (vOneValueQ _ _))
  | _, [_], [], [_], [] => isFalse (fun h => h)
  | _, [_], [], [_], _ :: _ :: _ => isFalse (fun h => h)
  | _, [_], [], [], _ => isFalse (fun h => h)
  | _, [_], [], _ :: _ :: _, _ => isFalse (fun h => h)
  | _, [_], _ :: _, _, _ => isFalse (fun h => h)
  | _, _ :: _ :: _, [], _, _ => isFalse (fun h => h)
  | _, _ :: _ :: _, _ :: _, [], _ => isFalse (fun h => h)
  | _, _ :: _ :: _, _ :: _, [_], _ => isFalse (fun h => h)
  | _, _ :: _ :: _, _ :: _, _ :: _ :: _, [] => isFalse (fun h => h)
  | _, _ :: A' :: As, _ :: Bs, _ :: u' :: us, _ :: ws =>
      @instDecidableAnd _ _ inferInstance
        (decSolveRows _ (A' :: As) Bs (u' :: us) ws)

instance (p : VecQ) (diag off : List Mat) (us ws : List VecQ) :
    Decidable (solveRows p diag off us ws) := decSolveRows p diag off us ws

/-- The solve's read: the slab walk, the two length walks, and the
rows' own walk from the vacant leading accumulator. -/
def solveRead (diag off : List Mat) (us ws : List VecQ)
    (ns : List Nat) : Prop :=
  slabShape diag off ns
  ∧ vShape us ns
  ∧ vShape ws ns
  ∧ solveRows dV diag off us ws

instance (diag off : List Mat) (us ws : List VecQ) (ns : List Nat) :
    Decidable (solveRead diag off us ws ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Every block's side at the sum's unit, the componentwise
walk. -/
def sidesUnit : List VecQ → Prop
  | [] => True
  | w :: ws => poly.unitTail w.1 ∧ sidesUnit ws

def decSidesUnit : ∀ ws : List VecQ, Decidable (sidesUnit ws)
  | [] => isTrue trivial
  | _ :: ws =>
      @instDecidableAnd _ _ (poly.decUnitTail _) (decSidesUnit ws)

instance (ws : List VecQ) : Decidable (sidesUnit ws) :=
  decSidesUnit ws

/-- The source's support at slab `j`, the keyed walk: the source's
own slab skipped with every further block's side at the sum's
unit. -/
def supportAt : List VecQ → Nat → Prop
  | [], _ => True
  | _ :: ws, 0 => sidesUnit ws
  | w :: ws, i + 1 => poly.unitTail w.1 ∧ supportAt ws i

def decSupportAt : ∀ (ws : List VecQ) (j : Nat),
    Decidable (supportAt ws j)
  | [], _ => isTrue trivial
  | _ :: ws, 0 => decSidesUnit ws
  | _ :: ws, i + 1 =>
      @instDecidableAnd _ _ (poly.decUnitTail _) (decSupportAt ws i)

instance (ws : List VecQ) (j : Nat) : Decidable (supportAt ws j) :=
  decSupportAt ws j

/-- The descending telescope's walk below the source:
`u_i = T_i u_{i+1}` at the head witnesses' transfer factors, the
key counting the steps below the source. -/
def teleDownWalk : Nat → List MatQ → List VecQ → Prop
  | 0, _, _ => True
  | _ + 1, [], _ => False
  | _ + 1, _ :: _, [] => False
  | _ + 1, _ :: _, [_] => False
  | i + 1, C :: Cs, u :: u' :: us =>
      vOneValueQ u (appQ (transfer C) u') ∧ teleDownWalk i Cs (u' :: us)

def decTeleDownWalk : ∀ (j : Nat) (Cs : List MatQ) (us : List VecQ),
    Decidable (teleDownWalk j Cs us)
  | 0, _, _ => isTrue trivial
  | _ + 1, [], _ => isFalse (fun h => h)
  | _ + 1, _ :: _, [] => isFalse (fun h => h)
  | _ + 1, _ :: _, [_] => isFalse (fun h => h)
  | i + 1, _ :: Cs, _ :: u' :: us =>
      @instDecidableAnd _ _ inferInstance
        (decTeleDownWalk i Cs (u' :: us))

instance (j : Nat) (Cs : List MatQ) (us : List VecQ) :
    Decidable (teleDownWalk j Cs us) := decTeleDownWalk j Cs us

/-- The descending telescope below the source at the slab shapes. -/
def teleDown (Cs : List MatQ) (us : List VecQ) (j : Nat)
    (ns : List Nat) : Prop :=
  wShapeC Cs ns ∧ vShape us ns ∧ teleDownWalk j Cs us

instance (Cs : List MatQ) (us : List VecQ) (j : Nat) (ns : List Nat) :
    Decidable (teleDown Cs us j ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The ascending telescope's walk beyond the source:
`u_{i+1} = Ť_i u_i` at the tail witnesses' transfer factors, the
key counting the steps down to the source with each step consuming
one slab. -/
def teleUpWalk : Nat → List MatQ → List VecQ → Prop
  | 0, _, [] => True
  | 0, _, [_] => True
  | 0, [], _ :: _ :: _ => False
  | 0, R :: Rs, u :: u' :: us =>
      vOneValueQ u' (appQ (transfer R) u)
      ∧ teleUpWalk 0 Rs (u' :: us)
  | _ + 1, [], _ => False
  | _ + 1, _ :: _, [] => False
  | i + 1, _ :: Rs, _ :: us => teleUpWalk i Rs us

def decTeleUpWalk : ∀ (j : Nat) (Rs : List MatQ) (us : List VecQ),
    Decidable (teleUpWalk j Rs us)
  | 0, [], [] => isTrue trivial
  | 0, _ :: _, [] => isTrue trivial
  | 0, [], [_] => isTrue trivial
  | 0, _ :: _, [_] => isTrue trivial
  | 0, [], _ :: _ :: _ => isFalse (fun h => h)
  | 0, _ :: Rs, _ :: u' :: us =>
      @instDecidableAnd _ _ inferInstance
        (decTeleUpWalk 0 Rs (u' :: us))
  | _ + 1, [], _ => isFalse (fun h => h)
  | _ + 1, _ :: _, [] => isFalse (fun h => h)
  | i + 1, _ :: Rs, _ :: us => decTeleUpWalk i Rs us

instance (j : Nat) (Rs : List MatQ) (us : List VecQ) :
    Decidable (teleUpWalk j Rs us) := decTeleUpWalk j Rs us

/-- The walk from the source anchors at any depth within the
family: the full ascending walk restricted to the slabs at or
beyond a depth below the witnesses' count and at or below the
factors' count is the walk keyed at that depth. -/
theorem teleUpWalk_anchor : ∀ (j : Nat) (Rs : List MatQ)
    (us : List VecQ), teleUpWalk 0 Rs us →
    j < us.length → j ≤ Rs.length → teleUpWalk j Rs us
  | 0, _, _, h, _, _ => h
  | _ + 1, [], _, _, _, hR => absurd hR (Nat.not_succ_le_zero _)
  | _ + 1, _ :: _, [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | _ + 1, _ :: _, [_], _, hj, _ =>
      absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero _)
  | j + 1, _ :: Rs, _ :: u' :: us, h, hj, hR =>
      teleUpWalk_anchor j Rs (u' :: us) h.2
        (Nat.lt_of_succ_lt_succ hj) (Nat.le_of_succ_le_succ hR)

/-- The ascending telescope beyond the source at the slab shapes,
the walk running over the slabs at or beyond `j`. -/
def teleUp (Rs : List MatQ) (us : List VecQ) (j : Nat)
    (ns : List Nat) : Prop :=
  wShapeR Rs ns ∧ vShape us ns ∧ teleUpWalk j Rs us

instance (Rs : List MatQ) (us : List VecQ) (j : Nat) (ns : List Nat) :
    Decidable (teleUp Rs us j ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The Green solve whole: the slab shape, the two recursions, the
source's support, the row reads, the corner solve at `Z_j`, and the
two transfer telescopes — every Green block a product of transfer
factors and one corner solve. -/
def greenRead (diag off : List Mat) (Xs Rs Ys Cs : List MatQ)
    (us ws : List VecQ) (j : Nat) (ns : List Nat) : Prop :=
  tailRead diag off Xs Rs ns
  ∧ headRead diag off Ys Cs ns
  ∧ supportAt ws j
  ∧ solveRead diag off us ws ns
  ∧ vOneValueQ
      (appQ (zJoinQ (ground.getAt dM Xs j) (ground.getAt dM Ys j)
        (ground.getAt [] diag j)) (ground.getAt dV us j))
      (ground.getAt dV ws j)
  ∧ teleDown Cs us j ns
  ∧ teleUp Rs us j ns

instance (diag off : List Mat) (Xs Rs Ys Cs : List MatQ)
    (us ws : List VecQ) (j : Nat) (ns : List Nat) :
    Decidable (greenRead diag off Xs Rs Ys Cs us ws j ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-! Clause (ii)'s two splits, the coherence reads at the assembled
matrix: the count and the determinant split over the tail pivots. -/

/-- The tail pivots' splits, one certificate per slab, the
clearings blind to the counts. -/
def revListRead : List MatQ → List ((n : Nat) × Split n) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | X :: Xs, s :: sps => splitRead X.1 s.2 ∧ revListRead Xs sps

def decRevListRead : ∀ (Xs : List MatQ)
    (sps : List ((n : Nat) × Split n)),
    Decidable (revListRead Xs sps)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: Xs, _ :: sps =>
    @instDecidableAnd _ _ inferInstance (decRevListRead Xs sps)

instance (Xs : List MatQ) (sps : List ((n : Nat) × Split n)) :
    Decidable (revListRead Xs sps) := decRevListRead Xs sps

/-- The slab fold of the reversal counts, the fast route the
consumers read. -/
def revFold (sps : List ((n : Nat) × Split n)) : Nat :=
  sps.foldl (fun m s => m + revAt s.2) 0

/-- The count split's read: the assembled matrix, the tail
recursion, the pivots' splits, and the whole datum's split at the
fold's value — `rev(S) = Σ_i rev(X_i)`, the coherence the
batteries' pins. -/
def countSplitRead {n : Nat} (S : Mat) (diag off : List Mat)
    (Xs Rs : List MatQ) (sps : List ((k : Nat) × Split k))
    (SP : Split n) (ns : List Nat) : Prop :=
  matOneValue S (assemble diag off)
  ∧ tailRead diag off Xs Rs ns
  ∧ revListRead Xs sps
  ∧ splitRead S SP
  ∧ revAt SP = revFold sps

instance {n : Nat} (S : Mat) (diag off : List Mat)
    (Xs Rs : List MatQ) (sps : List ((k : Nat) × Split k))
    (SP : Split n) (ns : List Nat) :
    Decidable (countSplitRead S diag off Xs Rs sps SP ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ = _))

/-- The cleared minor: the integer minor against the clearing at
the order's power, one composite pair. -/
def minorQ (X : MatQ) : CPair := ⟨minor X.1, Pos.powC X.2 X.1.length⟩

/-- The determinant split's read: `det S = Π_i det X_i` at the
cleared minors, the coherence the batteries' pins. -/
def detProdRead (diag off : List Mat) (Xs : List MatQ)
    (ns : List Nat) : Prop :=
  slabShape diag off ns
  ∧ qShape Xs ns
  ∧ CPair.oneValue ⟨minor (assemble diag off), .one⟩
      (Xs.foldl (fun a X => a * minorQ X) ⟨BPair.ofPos .one, .one⟩)

/-- The split's read transports to the descent's read at a square
assembled list: the determinant is a read of the value, the
first-component congruence carrying it across the composite
pair. -/
private theorem detProdRead_walk (diag off : List Mat)
    (Xs : List MatQ) (ns : List Nat)
    (hsq : elim.rowsLen (assemble diag off).length
      (assemble diag off)) :
    detProdRead diag off Xs ns ↔
    (slabShape diag off ns
     ∧ qShape Xs ns
     ∧ CPair.oneValue ⟨elim.detD (assemble diag off), .one⟩
        (Xs.foldl (fun a X => a * minorQ X)
          ⟨BPair.ofPos .one, .one⟩)) := by
  have hB : (elim.detD (assemble diag off)).oneValue
      (minor (assemble diag off)) :=
    BPair.oneValue_trans (elim.detD_eq _ hsq)
      (BPair.oneValue_symm (elim.minor_detL _ hsq))
  have hc := ground.CPair.num_congr
    (BPair.oneValue_symm hB) Pos.one
    (Xs.foldl (fun a X => a * minorQ X) ⟨BPair.ofPos .one, .one⟩)
  exact ⟨fun h => ⟨h.1, h.2.1, hc.mp h.2.2⟩,
    fun h => ⟨h.1, h.2.1, hc.mpr h.2.2⟩⟩

instance (diag off : List Mat) (Xs : List MatQ) (ns : List Nat) :
    Decidable (detProdRead diag off Xs ns) :=
  match elim.decRowsLen (assemble diag off).length
      (assemble diag off) with
  | isTrue hsq =>
    decidable_of_iff _ (detProdRead_walk diag off Xs ns hsq).symm
  | isFalse _ =>
    inferInstanceAs (Decidable (_ ∧ _ ∧ CPair.oneValue _ _))

/-! The count split's general theorem, at the slab list's own
recursion: the assembled matrix's two-block read, the telescoped
lift at the tail witnesses, and the two families priced at
`lem:inertia`'s forcing clauses. -/

/-- The off-diagonal block's row at the trailing order, the width
filled out by the sum's unit. -/
private def padRow (w : Nat) (rb : List BPair) : List BPair :=
  rb ++ List.replicate (w - rb.length) BPair.unit

/-- The off-diagonal block at the trailing order. -/
def offPad (w : Nat) (B : Mat) : Mat := B.map (padRow w)

/-- The off-diagonal block's exchange at the trailing order: the
exchange's own rows above, rows of the sum's unit beneath. -/
def offT (k : Nat) (bt : Mat) (m : Nat) : Mat :=
  (List.range m).map (fun r =>
    if r < bt.length then ground.getAt [] bt r
    else List.replicate k BPair.unit)

private theorem zipPadRow (w : Nat) : ∀ A B : Mat,
    List.zipWith (fun ra rb =>
        ra ++ rb ++ List.replicate (w - rb.length) BPair.unit) A B
      = List.zipWith (· ++ ·) A (offPad w B)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | ra :: A, rb :: B => by
    show (ra ++ rb ++ List.replicate (w - rb.length) BPair.unit)
        :: List.zipWith (fun ra rb =>
            ra ++ rb ++ List.replicate (w - rb.length) BPair.unit) A B
      = (ra ++ (rb ++ List.replicate (w - rb.length) BPair.unit))
        :: List.zipWith (· ++ ·) A (offPad w B)
    rw [zipPadRow w A B, ground.append_assoc]

private theorem rangeMapApp (Q : Mat) (m : Nat) (g : Nat → List BPair)
    (hQ : Q.length = m) :
    (List.range m).map (fun r => g r ++ ground.getAt [] Q r)
      = List.zipWith (· ++ ·) ((List.range m).map g) Q := by
  have hl : ((List.range m).map g).length = m :=
    ground.length_mapRange _ m
  have hll : ((List.range m).map
      (fun r => g r ++ ground.getAt [] Q r)).length = m :=
    ground.length_mapRange _ m
  refine ground.getAt_ext ([] : List BPair) _ _ ?_ ?_
  · rw [hll, ground.length_zipWith (· ++ ·) _ _ m hl hQ]
  · intro i hi
    rw [hll] at hi
    rw [ground.getAt_map_range ([] : List BPair)
        (fun r => g r ++ ground.getAt [] Q r) m i, if_pos hi,
      ground.getAt_zipWith ([] : List BPair) ([] : List BPair) ([] : List BPair) (· ++ ·) _ Q i (by rw [hl]; exact hi) (by rw [hQ]; exact hi),
      ground.getAt_map_range ([] : List BPair) g m i, if_pos hi]

/-! The shape tier: the slab reads' per-key projections, the
padded block's exchange, and the assembled matrix's square order at
the slab orders' sum. -/

private theorem subLtSubR : ∀ (k m n : Nat), k ≤ m → m < n →
    m - k < n - k
  | 0, _, _, _, h => by rw [Nat.sub_zero, Nat.sub_zero]; exact h
  | k + 1, 0, _, hk, _ => absurd hk (Nat.not_succ_le_zero k)
  | _ + 1, _ + 1, 0, _, hn => absurd hn (Nat.not_lt_zero _)
  | k + 1, m + 1, n + 1, hk, hn => by
    rw [Nat.succ_sub_succ, Nat.succ_sub_succ]
    exact subLtSubR k m n (Nat.le_of_succ_le_succ hk)
      (Nat.lt_of_succ_lt_succ hn)

/-- The rectangular shape's row count. -/
theorem rectAt_len {B : Mat} {r c : Nat} (h : rectAt B r c) :
    B.length = r := ground.beqEq _ _ ((ground.andSplitB h).1)

/-- The rectangular shape's column count, row by row. -/
theorem rectAt_rows {B : Mat} {r c : Nat} (h : rectAt B r c) :
    rowsLen c B :=
  rowsLen_of_allP (fun _ hr => ground.beqEq _ _ hr) B
    ((ground.andSplitB h).2)

theorem sqAt_headD : ∀ (M : Mat) (m : Nat), sqAt M m →
    (M.headD []).length = m
  | [], _, h => sqAt_len h
  | _ :: _, _, h => (rowsLen_of_sqAt h).1

theorem offPad_len (w : Nat) (B : Mat) :
    (offPad w B).length = B.length := ground.length_map _ B

private theorem offPad_rows (w n1 : Nat) (B : Mat) (hB : rowsLen n1 B)
    (hle : n1 ≤ w) : rowsLen w (offPad w B) :=
  rowsLen_map (padRow w) w B (fun r hr => by
    show (r ++ List.replicate (w - r.length) BPair.unit).length = w
    rw [ground.length_append, ground.length_replicate,
      elim.rowsLen_of_mem hB hr, ground.natAddSubCancel hle])

private theorem offPad_getAt (w : Nat) (B : Mat) (q : Nat)
    (hq : q < B.length) :
    ground.getAt [] (offPad w B) q = padRow w (ground.getAt [] B q) :=
  ground.getAt_map ([] : List BPair) ([] : List BPair) (padRow w) B q hq

private theorem offT_len (k : Nat) (bt : Mat) (m : Nat) :
    (offT k bt m).length = m :=
  ground.length_mapRange _ m

private theorem offT_rows (k : Nat) (bt : Mat) (m : Nat)
    (hbt : rowsLen k bt) : rowsLen k (offT k bt m) :=
  rowsLen_map _ k (List.range m) (fun r _ => by
    by_cases hr : r < bt.length
    · show (if r < bt.length then ground.getAt [] bt r
        else List.replicate k BPair.unit).length = k
      rw [if_pos hr]
      exact rowsLen_getAt bt r hbt hr
    · show (if r < bt.length then ground.getAt [] bt r
        else List.replicate k BPair.unit).length = k
      rw [if_neg hr]
      exact ground.length_replicate BPair.unit k)

/-- The padded off-block's exchange is the exchange padded by rows
of the sum's unit, at an occupied slab order. -/
theorem transposeM_offPad (B : Mat) (k n1 m : Nat)
    (hBl : B.length = k) (hBr : rowsLen n1 B) (hk : 0 < k)
    (hle : n1 ≤ m) :
    transposeM (offPad m B) = offT k (transposeM B) m := by
  have hPl : (offPad m B).length = k := (offPad_len m B).trans hBl
  have hPr : rowsLen m (offPad m B) := offPad_rows m n1 B hBr hle
  have hTl : (transposeM (offPad m B)).length = m :=
    length_transposeM (offPad m B) hPr (by rw [hPl]; exact hk)
  have hTr : rowsLen k (transposeM (offPad m B)) :=
    rowsLen_cast hPl (rowsLen_transposeM (offPad m B))
  have hbtl : (transposeM B).length = n1 :=
    length_transposeM B hBr (by rw [hBl]; exact hk)
  have hbtr : rowsLen k (transposeM B) :=
    rowsLen_cast hBl (rowsLen_transposeM B)
  refine ground.getAt_ext ([] : List BPair) _ _ ?_ ?_
  · rw [hTl, offT_len]
  · intro p hp
    rw [hTl] at hp
    have hrl : (ground.getAt ([] : List BPair)
        (transposeM (offPad m B)) p).length = k :=
      rowsLen_getAt _ p hTr (by rw [hTl]; exact hp)
    have hrr : (ground.getAt ([] : List BPair)
        (offT k (transposeM B) m) p).length = k :=
      rowsLen_getAt _ p (offT_rows k (transposeM B) m hbtr)
        (by rw [offT_len]; exact hp)
    refine ground.getAt_ext BPair.unit _ _ (hrl.trans hrr.symm) ?_
    intro q hq
    rw [hrl] at hq
    rw [getAt_transposeM BPair.unit (offPad m B) hPr p q hp
        (by rw [hPl]; exact hq),
      offPad_getAt m B q (by rw [hBl]; exact hq)]
    have hrq : (ground.getAt ([] : List BPair) B q).length = n1 :=
      rowsLen_getAt B q hBr (by rw [hBl]; exact hq)
    show ground.getAt BPair.unit
        (ground.getAt [] B q ++ List.replicate
          (m - (ground.getAt ([] : List BPair) B q).length) BPair.unit) p
      = ground.getAt BPair.unit
          (ground.getAt [] (offT k (transposeM B) m) p) q
    rw [hrq, ground.getAt_append]
    show (if p < (ground.getAt ([] : List BPair) B q).length
        then ground.getAt BPair.unit (ground.getAt [] B q) p
        else ground.getAt BPair.unit
          (List.replicate (m - n1) BPair.unit)
          (p - (ground.getAt ([] : List BPair) B q).length))
      = ground.getAt BPair.unit
          (ground.getAt [] ((List.range m).map (fun r =>
            if r < (transposeM B).length
              then ground.getAt [] (transposeM B) r
              else List.replicate k BPair.unit)) p) q
    rw [hrq, ground.getAt_map_range ([] : List BPair) _ m p, if_pos hp,
      hbtl]
    by_cases hpn : p < n1
    · rw [if_pos hpn, if_pos hpn,
        getAt_transposeM BPair.unit B hBr p q hpn (by rw [hBl]; exact hq)]
    · rw [if_neg hpn, if_neg hpn,
        ground.getAt_replicate BPair.unit BPair.unit (m - n1) (p - n1)
          (subLtSubR n1 p m (Nat.le_of_not_lt hpn) hp),
        ground.getAt_replicate BPair.unit BPair.unit k q hq]

/-- The assembled matrix at a leading slab: the slab's block row
against the padded off-block above, the exchange against the
trailing assembly beneath. -/
theorem assemble_cons (A B : Mat) (As Bs : List Mat)
    (k n1 m : Nat) (hAl : A.length = k) (hk : 0 < k)
    (hBl : B.length = k) (hBr : rowsLen n1 B) (hle : n1 ≤ m)
    (hml : (assemble As Bs).length = m)
    (hhd : ((assemble As Bs).headD []).length = m) :
    assemble (A :: As) (B :: Bs)
      = blockJoin A (offPad m B) (assemble As Bs) := by
  show List.zipWith (fun ra rb =>
        ra ++ rb ++ List.replicate
          (((assemble As Bs).headD []).length - rb.length) BPair.unit) A B
      ++ (List.range (assemble As Bs).length).map (fun r =>
        (if r < (transposeM B).length
          then ground.getAt [] (transposeM B) r
          else List.replicate A.length BPair.unit)
        ++ ground.getAt [] (assemble As Bs) r)
    = List.zipWith (· ++ ·) A (offPad m B)
      ++ List.zipWith (· ++ ·) (transposeM (offPad m B)) (assemble As Bs)
  rw [hhd, zipPadRow m A B,
    rangeMapApp (assemble As Bs) (assemble As Bs).length
      (fun r => if r < (transposeM B).length
        then ground.getAt [] (transposeM B) r
        else List.replicate A.length BPair.unit) rfl,
    hAl, hml]
  exact congrArg
    (fun M => List.zipWith (· ++ ·) A (offPad m B)
      ++ List.zipWith (· ++ ·) M (assemble As Bs))
    (transposeM_offPad B k n1 m hBl hBr hk hle).symm

/-- The slab walk ties the order list to the diagonal blocks. -/
theorem slabShape_len_ns : ∀ {diag off : List Mat}
    {ns : List Nat}, slabShape diag off ns → ns.length = diag.length
  | [], _, _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | [_], [], [_], _ => rfl
  | [_], [], _ :: _ :: _, h => h.elim
  | [_], _ :: _, [_], h => h.elim
  | [_], _ :: _, _ :: _ :: _, h => h.elim
  | _ :: _ :: _, [], [_], h => h.elim
  | _ :: _ :: _, [], _ :: _ :: _, h => h.elim
  | _ :: _ :: _, _ :: _, [_], h => h.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h =>
    congrArg (· + 1) (slabShape_len_ns h.2.2.2)

/-- The slab walk ties the off-diagonal blocks to the diagonal
blocks, one fewer. -/
theorem slabShape_len_off : ∀ {diag off : List Mat}
    {ns : List Nat}, slabShape diag off ns → off.length + 1 = diag.length
  | [], _, _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | [_], [], [_], _ => rfl
  | [_], [], _ :: _ :: _, h => h.elim
  | [_], _ :: _, [_], h => h.elim
  | [_], _ :: _, _ :: _ :: _, h => h.elim
  | _ :: _ :: _, [], [_], h => h.elim
  | _ :: _ :: _, [], _ :: _ :: _, h => h.elim
  | _ :: _ :: _, _ :: _, [_], h => h.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h =>
    congrArg (· + 1) (slabShape_len_off h.2.2.2)

/-- The pivot walk ties the pivots to the orders. -/
theorem qShape_len : ∀ {Xs : List MatQ} {ns : List Nat},
    qShape Xs ns → Xs.length = ns.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: Xs, _ :: ns, h => congrArg (· + 1) (qShape_len (Xs := Xs) (ns := ns) h.2)

/-- The vector walk ties the blocks to the orders. -/
theorem vShape_len : ∀ {us : List VecQ} {ns : List Nat},
    vShape us ns → us.length = ns.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: us, _ :: ns, h =>
    congrArg (· + 1) (vShape_len (us := us) (ns := ns) h.2)

/-- The tail witness walk ties the witnesses to the orders, one
fewer. -/
theorem wShapeR_len : ∀ {Rs : List MatQ} {ns : List Nat},
    wShapeR Rs ns → Rs.length + 1 = ns.length
  | [], [], h => h.elim
  | [], [_], _ => rfl
  | [], _ :: _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, [_], h => h.elim
  | _ :: Rs, _ :: k' :: ns, h =>
    congrArg (· + 1) (wShapeR_len (Rs := Rs) (ns := k' :: ns) h.2)

private theorem slabShape_tail {A B : Mat} {As Bs : List Mat}
    {n0 : Nat} {nt : List Nat}
    (h : slabShape (A :: As) (B :: Bs) (n0 :: nt)) :
    slabShape As Bs nt := by
  cases As with
  | nil =>
    cases nt with
    | nil => exact (h : False).elim
    | cons _ _ => exact (h : False).elim
  | cons A' As' =>
    cases nt with
    | nil => exact (h : False).elim
    | cons k' nt' => exact h.2.2.2

private theorem slab_sq : ∀ {diag off : List Mat} {ns : List Nat},
    slabShape diag off ns → ∀ (i : Nat), i < diag.length →
    sqAt (ground.getAt [] diag i) (ground.getAt 0 ns i)
  | [], _, _, h, _, _ => h.elim
  | _ :: _, _, [], h, _, _ => h.elim
  | [_], [], [_], h, 0, _ => h.2
  | [_], [], [_], _, _ + 1, hi =>
    absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero _)
  | [_], [], _ :: _ :: _, h, _, _ => h.elim
  | [_], _ :: _, [_], h, _, _ => h.elim
  | [_], _ :: _, _ :: _ :: _, h, _, _ => h.elim
  | _ :: _ :: _, [], [_], h, _, _ => h.elim
  | _ :: _ :: _, [], _ :: _ :: _, h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, [_], h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h, 0, _ => h.2.1
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h, i + 1, hi =>
    slab_sq h.2.2.2 i (Nat.lt_of_succ_lt_succ hi)

private theorem slab_rect : ∀ {diag off : List Mat} {ns : List Nat},
    slabShape diag off ns → ∀ (i : Nat), i < off.length →
    rectAt (ground.getAt [] off i) (ground.getAt 0 ns i)
      (ground.getAt 0 ns (i + 1))
  | [], _, _, h, _, _ => h.elim
  | _ :: _, _, [], h, _, _ => h.elim
  | [_], [], [_], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | [_], [], _ :: _ :: _, h, _, _ => h.elim
  | [_], _ :: _, [_], h, _, _ => h.elim
  | [_], _ :: _, _ :: _ :: _, h, _, _ => h.elim
  | _ :: _ :: _, [], [_], h, _, _ => h.elim
  | _ :: _ :: _, [], _ :: _ :: _, h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, [_], h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h, 0, _ => h.2.2.1
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h, i + 1, hi =>
    slab_rect h.2.2.2 i (Nat.lt_of_succ_lt_succ hi)

/-- Every slab holds a key, the walk's occupancy read at a
stated slab. -/
theorem slab_pos : ∀ {diag off : List Mat} {ns : List Nat},
    slabShape diag off ns → ∀ (i : Nat), i < ns.length →
    0 < ground.getAt 0 ns i
  | [], _, _, h, _, _ => h.elim
  | _ :: _, _, [], h, _, _ => h.elim
  | [_], [], [_], h, 0, _ => h.1
  | [_], [], [_], _, _ + 1, hi =>
    absurd (Nat.lt_of_succ_lt_succ hi) (Nat.not_lt_zero _)
  | [_], [], _ :: _ :: _, h, _, _ => h.elim
  | [_], _ :: _, [_], h, _, _ => h.elim
  | [_], _ :: _, _ :: _ :: _, h, _, _ => h.elim
  | _ :: _ :: _, [], [_], h, _, _ => h.elim
  | _ :: _ :: _, [], _ :: _ :: _, h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, [_], h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h, 0, _ => h.1
  | _ :: _ :: _, _ :: _, _ :: _ :: _, h, i + 1, hi =>
    slab_pos h.2.2.2 i (Nat.lt_of_succ_lt_succ hi)

/-- The assembled matrix is square at the slab orders' sum. -/
private theorem assemble_sq : ∀ (diag off : List Mat) (ns : List Nat),
    slabShape diag off ns → sqAt (assemble diag off) (ground.sumNat ns)
  | [], _, _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | A :: [], [], [n0], h => by
    have hA : sqAt A n0 := slab_sq h 0 (Nat.succ_pos 0)
    show sqAt A (n0 + 0)
    rw [Nat.add_zero]
    exact hA
  | _ :: [], [], _ :: _ :: _, h => h.elim
  | _ :: [], _ :: _, [_], h => h.elim
  | _ :: [], _ :: _, _ :: _ :: _, h => h.elim
  | _ :: _ :: _, [], [_], h => h.elim
  | _ :: _ :: _, [], _ :: _ :: _, h => h.elim
  | A :: A' :: As, B :: Bs, n0 :: nt, h => by
    have ht : slabShape (A' :: As) Bs nt := slabShape_tail h
    have hIH : sqAt (assemble (A' :: As) Bs) (ground.sumNat nt) :=
      assemble_sq (A' :: As) Bs nt ht
    have hA : sqAt A n0 := slab_sq h 0 (Nat.succ_pos _)
    have hB : rectAt B n0 (ground.getAt 0 nt 0) :=
      slab_rect h 0 (Nat.succ_pos _)
    have hAl : A.length = n0 := sqAt_len hA
    have hk : 0 < n0 := slab_pos h 0 (Nat.succ_pos _)
    have hrl : (assemble (A' :: As) Bs).length = ground.sumNat nt :=
      sqAt_len hIH
    have hhd : ((assemble (A' :: As) Bs).headD []).length
        = ground.sumNat nt := sqAt_headD _ _ hIH
    have hn1 : ground.getAt 0 nt 0 ≤ ground.sumNat nt :=
      ground.getAt_le_sumNat nt 0
    have hbt : (transposeM (offPad (ground.sumNat nt) B)).length
        = ground.sumNat nt := by
      rw [transposeM_offPad B n0 (ground.getAt 0 nt 0) (ground.sumNat nt)
        (rectAt_len hB) (rectAt_rows hB) hk hn1, offT_len]
    have hbtr : rowsLen n0 (transposeM (offPad (ground.sumNat nt) B)) := by
      rw [transposeM_offPad B n0 (ground.getAt 0 nt 0) (ground.sumNat nt)
        (rectAt_len hB) (rectAt_rows hB) hk hn1]
      exact offT_rows n0 (transposeM B) (ground.sumNat nt)
        (rowsLen_cast (rectAt_len hB) (rowsLen_transposeM B))
    rw [assemble_cons A B (A' :: As) Bs n0 (ground.getAt 0 nt 0)
      (ground.sumNat nt) hAl hk (rectAt_len hB) (rectAt_rows hB)
      hn1 hrl hhd]
    show sqAt (blockJoin A (offPad (ground.sumNat nt) B)
      (assemble (A' :: As) Bs)) (n0 + ground.sumNat nt)
    refine sqAt_of (length_blockJoin _ _ _ n0 (ground.sumNat nt) hAl
      ((offPad_len _ B).trans (rectAt_len hB)) hbt hrl) ?_
    exact rowsLen_blockJoin _ _ _ n0 (ground.sumNat nt)
      (rowsLen_of_sqAt hA)
      (offPad_rows _ _ B (rectAt_rows hB) hn1) hbtr (rowsLen_of_sqAt hIH)

/-- The rescaled rows read the stated width, row by row. -/
private theorem allScale (c : Nat) (w : Pos) : ∀ B : Mat,
    (matScale w B).all (fun row => Nat.beq row.length c)
      = B.all (fun row => Nat.beq row.length c)
  | [] => rfl
  | x :: t => by
    show (Nat.beq (x.map (fun e => e.scale w)).length c
        && (matScale w t).all (fun row => Nat.beq row.length c))
      = (Nat.beq x.length c && t.all (fun row => Nat.beq row.length c))
    rw [ground.length_map (fun e => e.scale w) x, allScale c w t]

/-- The rescaling keeps the rectangular shape. -/
private theorem rectAt_matScale (w : Pos) (B : Mat) (r c : Nat)
    (h : rectAt B r c) : rectAt (matScale w B) r c := by
  show (Nat.beq (matScale w B).length r
    && (matScale w B).all (fun row => Nat.beq row.length c)) = true
  rw [length_matScale w B, allScale c w B]
  exact h

/-- A leading slab joins a slab walk at its own key, its diagonal
block square there and its coupling rectangular against the walk's
leading key. -/
private theorem slabShape_cons (A B : Mat) (D O : List Mat) (k : Nat)
    (N : List Nat) (hk : 0 < k) (hA : sqAt A k)
    (hB : rectAt B k (ground.getAt 0 N 0)) (h : slabShape D O N) :
    slabShape (A :: D) (B :: O) (k :: N) := by
  cases D with
  | nil => exact h.elim
  | cons A' D' =>
    cases N with
    | nil => exact h.elim
    | cons k' N' => exact ⟨hk, hA, hB, h⟩

/-- The decimated order list reads its leading key at the slab
walk's own. -/
private theorem headNs : ∀ (j : Nat) (ns : List Nat), j < ns.length →
    ground.getAt 0 (List.take j ns ++ [ground.getAt 0 ns j]) 0
      = ground.getAt 0 ns 0
  | 0, _, _ => rfl
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _ :: _, _ => rfl

/-- The decimated head's slab walk: the leading slabs at their own
keys rescaled, the pivot's block the trailing slab at the depth's
key. -/
private theorem headShape : ∀ (j : Nat) (diag off : List Mat)
    (ns : List Nat) (w : Pos) (P : Mat), slabShape diag off ns →
    j < ns.length → sqAt P (ground.getAt 0 ns j) →
    slabShape (List.map (matScale w) (List.take j diag) ++ [P])
      (List.map (matScale w) (List.take j off))
      (List.take j ns ++ [ground.getAt 0 ns j])
  | 0, _, _, ns, _, _, hs, hj, hP => ⟨slab_pos hs 0 hj, hP⟩
  | j + 1, diag, off, ns, w, P, hs, hj, hP => by
    cases ns with
    | nil => exact absurd hj (Nat.not_lt_zero _)
    | cons n0 nt =>
      have hjt : j < nt.length := Nat.lt_of_succ_lt_succ hj
      cases diag with
      | nil => exact hs.elim
      | cons A As =>
        cases off with
        | nil =>
          cases nt with
          | nil => exact absurd hjt (Nat.not_lt_zero _)
          | cons k' nt' =>
            cases As with
            | nil => exact hs.elim
            | cons _ _ => exact hs.elim
        | cons B Bs =>
          have hIH : slabShape
              (List.map (matScale w) (List.take j As) ++ [P])
              (List.map (matScale w) (List.take j Bs))
              (List.take j nt ++ [ground.getAt 0 nt j]) :=
            headShape j As Bs nt w P (slabShape_tail hs) hjt hP
          refine slabShape_cons _ _ _ _ n0 _
            (slab_pos hs 0 (Nat.succ_pos _))
            (sqAt_matScale n0 w A (slab_sq hs 0 (Nat.succ_pos _))) ?_ hIH
          show rectAt (matScale w B) n0
            (ground.getAt 0
              (List.take j nt ++ [ground.getAt 0 nt j]) 0)
          rw [headNs j nt hjt]
          exact rectAt_matScale w B n0 (ground.getAt 0 nt 0)
            (slab_rect hs 0 (Nat.succ_pos _))

/-- The decimated head is square at the leading keys' total joined
to the depth's own key. -/
theorem headM_sq (diag off : List Mat) (X : MatQ) (j : Nat)
    (ns : List Nat)
    (hs : slabShape diag off ns) (hj : j < ns.length)
    (hX : sqAt X.1 (ground.getAt 0 ns j)) :
    sqAt (headM diag off X j)
      (ground.sumNat (List.take j ns) + ground.getAt 0 ns j) := by
  have h := assemble_sq
    (List.map (matScale X.2) (List.take j diag) ++ [X.1])
    (List.map (matScale X.2) (List.take j off))
    (List.take j ns ++ [ground.getAt 0 ns j])
    (headShape j diag off ns X.2 X.1 hs hj hX)
  rw [ground.sumNat_append (List.take j ns) [ground.getAt 0 ns j]] at h
  show sqAt (assemble _ _)
    (ground.sumNat (List.take j ns) + ground.getAt 0 ns j)
  rw [show ground.sumNat [ground.getAt 0 ns j] = ground.getAt 0 ns j from
    Nat.add_zero _] at h
  exact h

private theorem unitTail_scaleP (w : BPair) : ∀ {r : List BPair},
    poly.unitTail r → poly.unitTail (poly.scaleP w r)
  | [], _ => trivial
  | _ :: _, h => by
    refine ⟨?_, unitTail_scaleP w h.2⟩
    show BPair.oneValue ((w * _).norm) BPair.unit
    refine BPair.oneValue_trans (BPair.norm_oneValue _) ?_
    exact BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl w) h.1)
        (BPair.mul_unit w)

private theorem nullScaleB (w : BPair) : ∀ (M : Mat),
    elim.matNull M → elim.matNull (matScaleB w M)
  | [], _ => trivial
  | _ :: M, h => ⟨unitTail_scaleP w h.1, nullScaleB w M h.2⟩

private theorem rowScaleP (c : Pos) (w : BPair) : ∀ r : List BPair,
    poly.oneValue ((poly.scaleP w r).map (fun x => x.scale c))
      (poly.scaleP (w.scale c) r)
  | [] => trivial
  | x :: r => by
    refine ⟨?_, rowScaleP c w r⟩
    show (((w * x).norm).scale c).oneValue ((w.scale c * x).norm)
    refine BPair.oneValue_trans
      (BPair.scale_congr c (BPair.norm_oneValue _)) ?_
    rw [← BPair.scale_mul_left w x c]
    exact BPair.oneValue_symm (BPair.norm_oneValue _)

private theorem scaleScaleB (c : Pos) (w : BPair) (M : Mat) :
    matOneValue (matScale c (matScaleB w M))
      (matScaleB (w.scale c) M) := by
  show matOneValue ((M.map (poly.scaleP w)).map
      (fun r => r.map (fun x => x.scale c)))
    (M.map (poly.scaleP (w.scale c)))
  rw [ground.map_map]
  exact elim.matOne_map _ _ (fun r => rowScaleP c w r) M

private theorem matScale_congrM (c : Pos) {A B : Mat}
    (h : matOneValue A B) :
    matOneValue (matScale c A) (matScale c B) :=
  elim.matOne_trans (inertia.matScale_scaleB c A)
    (elim.matOne_trans (inertia.matOne_scaleB (BPair.ofPos c) h)
      (elim.matOne_symm (inertia.matScale_scaleB c B)))

private theorem unitTailRepl {y : BPair} (hy : y.oneValue BPair.unit) :
    ∀ n : Nat, poly.unitTail (List.replicate n y)
  | 0 => trivial
  | n + 1 => ⟨hy, unitTailRepl hy n⟩

private theorem rowPad (c : Pos) (W : Nat) (rb : List BPair) :
    poly.oneValue ((padRow W rb).map (fun x => x.scale c))
      (padRow W (rb.map (fun x => x.scale c))) := by
  show poly.oneValue
    ((rb ++ List.replicate (W - rb.length) BPair.unit).map
      (fun x => x.scale c))
    (rb.map (fun x => x.scale c)
      ++ List.replicate (W - (rb.map (fun x => x.scale c)).length)
        BPair.unit)
  rw [ground.map_append, ground.map_replicate, ground.length_map]
  refine poly.oneValue_append _ _ _ _ rfl
    (poly.oneValue_refl _) ?_
  refine poly.unitTail_oneValue
    (unitTailRepl ?_ (W - rb.length)) (poly.unitTail_replicate _)
  show (BPair.unit.scale c).oneValue BPair.unit
  show Pos.one * c + Pos.one = Pos.one + Pos.one * c
  exact ground.add_comm _ _

private theorem scalePad (c : Pos) (W : Nat) (B : Mat) :
    matOneValue (matScale c (offPad W B))
      (offPad W (matScale c B)) := by
  show matOneValue ((B.map (padRow W)).map
      (fun r => r.map (fun x => x.scale c)))
    ((B.map (fun r => r.map (fun x => x.scale c))).map (padRow W))
  rw [ground.map_map, ground.map_map]
  exact elim.matOne_map _ _ (fun rb => rowPad c W rb) B

private theorem rowPadCongr (W : Nat) {rb rb' : List BPair}
    (hl : rb.length = rb'.length) (h : poly.oneValue rb rb') :
    poly.oneValue (padRow W rb) (padRow W rb') := by
  show poly.oneValue
    (rb ++ List.replicate (W - rb.length) BPair.unit)
    (rb' ++ List.replicate (W - rb'.length) BPair.unit)
  rw [hl]
  exact poly.oneValue_append _ _ _ _ hl h (poly.oneValue_refl _)

private theorem offPadCongr (W : Nat) {n : Nat} :
    ∀ {B B' : Mat}, rowsLen n B → rowsLen n B' →
    matOneValue B B' → matOneValue (offPad W B) (offPad W B')
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, hB, hB', h =>
    ⟨rowPadCongr W (hB.1.trans hB'.1.symm) h.1,
     offPadCongr W hB.2 hB'.2 h.2⟩


private theorem tieBase (dn : BPair) (X X' : MatQ) (o : Nat)
    (hX : sqAt X.1 o) (hX' : sqAt X'.1 o) :
    matOneValue (matScale X.2 X'.1)
      (matAdd (matScale X'.2 X.1)
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2)) (inertia.headId 0 o))
          (inertia.trailPad 0 (addQ X' (swapQ X)).1))) := by
  have hb : sqAt (matScale X.2 X'.1) o :=
    inertia.sqAt_matScale o X.2 X'.1 hX'
  have ha : sqAt (matScale X'.2 X.1) o :=
    inertia.sqAt_matScale o X'.2 X.1 hX
  have hc : sqAt (matScale X'.2 (matSwap X.1)) o :=
    inertia.sqAt_matScale o X'.2 _ (elim.sqAt_matSwap o X.1 hX)
  have hdevS : sqAt (matAdd (matScale X.2 X'.1)
      (matScale X'.2 (matSwap X.1))) o :=
    elim.sqAt_matAdd o _ _ hb hc
  have hnul : elim.matNull (matScaleB (dn.scale (X.2 * X'.2))
      (inertia.headId 0 o)) :=
    nullScaleB _ _ (show elim.matNull (elim.nullMat o (0 + o)) from
      elim.matNull_nullMat _ _)
  have hz : (0 : Nat) + o = o := Nat.zero_add o
  have hnulS : sqAt (matScaleB (dn.scale (X.2 * X'.2))
      (inertia.headId 0 o)) o := by
    refine elim.sqAt_of ?_ ?_
    · show (matScaleB _ (elim.nullMat o (0 + o))).length = o
      rw [inertia.length_scaleB, elim.length_nullMat]
    · exact elim.rowsLen_cast hz
        (inertia.rowsLen_scaleB _ _ _ (elim.rowsLen_nullMat _ _))
  refine elim.matOne_symm ?_
  show matOneValue
    (matAdd (matScale X'.2 X.1)
      (matAdd
        (matScaleB (dn.scale (X.2 * X'.2)) (inertia.headId 0 o))
        (inertia.trailPad 0
          (matAdd (matScale X.2 X'.1)
            (matScale X'.2 (matSwap X.1))))))
    (matScale X.2 X'.1)
  rw [show inertia.trailPad 0
      (matAdd (matScale X.2 X'.1) (matScale X'.2 (matSwap X.1)))
    = (matAdd (matScale X.2 X'.1)
        (matScale X'.2 (matSwap X.1))).map (fun r => r) from rfl,
    ground.map_id]
  refine elim.matOne_trans
    (elim.matAdd_cong2 o (matScale X'.2 X.1) _ (matScale X'.2 X.1) _
      (elim.rowsLen_of_sqAt ha)
      (elim.rowsLen_matAdd o _ _ (elim.rowsLen_of_sqAt hnulS)
        (elim.rowsLen_of_sqAt hdevS))
      (elim.rowsLen_of_sqAt ha) (elim.rowsLen_of_sqAt hdevS)
      (elim.matOne_refl _)
      (elim.matAdd_nullL _ _ hnul
        ((elim.sqAt_len hnulS).trans (elim.sqAt_len hdevS).symm)
        (elim.rowsLen_of_sqAt hnulS)
        (elim.rowsLen_of_sqAt hdevS))) ?_
  rw [← elim.matAdd_assoc,
    elim.matAdd_comm (matScale X'.2 X.1) (matScale X.2 X'.1),
    elim.matAdd_assoc, inertia.matScale_matSwap X'.2 X.1]
  exact elim.matAdd_nullR (matScale X.2 X'.1) _ hb
    (elim.sqAt_matAdd o _ _ ha
      (elim.sqAt_matSwap o _ ha))
    (elim.matNull_add_swap (matScale X'.2 X.1))

private theorem tieStep (dn : BPair) (X X' : MatQ) (j : Nat)
    (A A' B B' : Mat) (dt dt' Bs Bs' : List Mat) (nt : List Nat)
    (n0 : Nat) {n1 : Nat} (hn0 : 0 < n0)
    (hA : sqAt A n0) (hA' : sqAt A' n0)
    (hB : rectAt B n0 n1) (hB' : rectAt B' n0 n1)
    (hle : n1 ≤ ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
    (hX : sqAt X.1 (ground.getAt 0 nt j))
    (hX' : sqAt X'.1 (ground.getAt 0 nt j))
    (hQsq : sqAt (headM dt Bs X j)
      (ground.sumNat (List.take j nt) + ground.getAt 0 nt j))
    (hcons : headM (A :: dt) (B :: Bs) X (j + 1)
      = blockJoin (matScale X.2 A)
        (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X.2 B))
        (headM dt Bs X j))
    (hcons' : headM (A' :: dt') (B' :: Bs') X' (j + 1)
      = blockJoin (matScale X'.2 A')
        (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X'.2 B'))
        (headM dt' Bs' X' j))
    (hIH : matOneValue (matScale X.2 (headM dt' Bs' X' j))
      (matAdd (matScale X'.2 (headM dt Bs X j))
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2))
            (inertia.headId (ground.sumNat (List.take j nt))
              (ground.getAt 0 nt j)))
          (inertia.trailPad (ground.sumNat (List.take j nt))
            (addQ X' (swapQ X)).1))))
    (htie0 : matOneValue A'
      (matAdd A (matScaleB dn (idMat n0))))
    (hoff0 : matOneValue B' B) :
    matOneValue
      (matScale X.2 (headM (A' :: dt') (B' :: Bs') X' (j + 1)))
      (matAdd (matScale X'.2 (headM (A :: dt) (B :: Bs) X (j + 1)))
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2))
            (inertia.headId
              (n0 + ground.sumNat (List.take j nt))
              (ground.getAt 0 nt j)))
          (inertia.trailPad
            (n0 + ground.sumNat (List.take j nt))
            (addQ X' (swapQ X)).1))) := by
  -- shapes
  have hdev : sqAt (addQ X' (swapQ X)).1 (ground.getAt 0 nt j) :=
    elim.sqAt_matAdd _ _ _
      (inertia.sqAt_matScale _ X.2 X'.1 hX')
      (inertia.sqAt_matScale _ X'.2 _ (elim.sqAt_matSwap _ X.1 hX))
  have hOl : (offPad (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j) (matScale X.2 B)).length = n0 := by
    show ((matScale X.2 B).map _).length = n0
    rw [ground.length_map, length_matScale]
    exact rectAt_len hB
  have hOl' : (offPad (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j) (matScale X'.2 B')).length = n0 := by
    show ((matScale X'.2 B').map _).length = n0
    rw [ground.length_map, length_matScale]
    exact rectAt_len hB'
  have hOr : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X.2 B)) :=
    offPad_rows _ n1 _
      (rectAt_rows (rectAt_matScale X.2 B n0 n1 hB)) hle
  have hOr' : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X'.2 B')) :=
    offPad_rows _ n1 _
      (rectAt_rows (rectAt_matScale X'.2 B' n0 n1 hB')) hle
  -- the two scaled peels
  have hL : matOneValue
      (matScale X.2 (headM (A' :: dt') (B' :: Bs') X' (j + 1)))
      (blockJoin (matScale X.2 (matScale X'.2 A'))
        (matScale X.2 (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X'.2 B')))
        (matScale X.2 (headM dt' Bs' X' j))) := by
    rw [hcons']
    exact inertia.matScale_blockJoin X.2 _ _ _ hOl' hOr'
  have hR1 : matOneValue
      (matScale X'.2 (headM (A :: dt) (B :: Bs) X (j + 1)))
      (blockJoin (matScale X'.2 (matScale X.2 A))
        (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X.2 B)))
        (matScale X'.2 (headM dt Bs X j))) := by
    rw [hcons]
    exact inertia.matScale_blockJoin X'.2 _ _ _ hOl hOr
  -- the two pads peel
  have hpeelT : matOneValue
      (inertia.trailPad (n0 + ground.sumNat (List.take j nt))
        (addQ X' (swapQ X)).1)
      (blockJoin (elim.nullMat n0 n0)
        (elim.nullMat n0 (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j))
        (inertia.trailPad (ground.sumNat (List.take j nt))
          (addQ X' (swapQ X)).1)) :=
    inertia.trailPad_join _ hdev hn0
  have hR2 : matOneValue
      (matScaleB (dn.scale (X.2 * X'.2))
        (inertia.headId (n0 + ground.sumNat (List.take j nt))
          (ground.getAt 0 nt j)))
      (blockJoin
        (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
        (matScaleB (dn.scale (X.2 * X'.2))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j)))
        (matScaleB (dn.scale (X.2 * X'.2))
          (inertia.headId (ground.sumNat (List.take j nt))
            (ground.getAt 0 nt j)))) :=
    elim.matOne_trans
      (inertia.matOne_scaleB _ (inertia.headId_join hn0))
      (inertia.matScaleB_blockJoin _ _ _ _
        (elim.length_nullMat n0 _) (elim.rowsLen_nullMat n0 _))
  -- the head-block tie at the shared clearing
  have hidsq : sqAt (idMat n0) n0 :=
    elim.sqAt_of (inertia.idMat_len n0) (inertia.idMat_rows n0)
  have hsProws : rowsLen n0
      (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0)) :=
    inertia.rowsLen_scaleB _ n0 _ (inertia.idMat_rows n0)
  have hsPlen : (matScaleB (dn.scale (X.2 * X'.2))
      (idMat n0)).length = n0 :=
    (inertia.length_scaleB _ _).trans (inertia.idMat_len n0)
  have hPnrows : rowsLen n0
      (matAdd (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
        (elim.nullMat n0 n0)) :=
    elim.rowsLen_matAdd n0 _ _ hsProws (elim.rowsLen_nullMat n0 n0)
  have htieP : matOneValue (matScale X.2 (matScale X'.2 A'))
      (matAdd (matScale X'.2 (matScale X.2 A))
        (matAdd (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
          (elim.nullMat n0 n0))) := by
    rw [inertia.matScale_matScale X'.2 X.2 A',
      inertia.matScale_matScale X.2 X'.2 A,
      ground.mul_comm X'.2 X.2]
    refine elim.matOne_trans
      (matScale_congrM (X.2 * X'.2) htie0) ?_
    rw [inertia.matScale_matAdd (X.2 * X'.2) A
      (matScaleB dn (idMat n0))]
    refine elim.matAdd_cong2 n0 _ _ _ _
      (elim.rowsLen_mapRows _ A n0 (elim.rowsLen_of_sqAt hA))
      (elim.rowsLen_mapRows _ _ n0
        (inertia.rowsLen_scaleB dn n0 _ (inertia.idMat_rows n0)))
      (elim.rowsLen_mapRows _ A n0 (elim.rowsLen_of_sqAt hA))
      hPnrows (elim.matOne_refl _) ?_
    refine elim.matOne_trans
      (scaleScaleB (X.2 * X'.2) dn (idMat n0))
      (elim.matOne_symm ?_)
    exact elim.matAdd_nullR _ _
      (inertia.sqAt_scaleB _ n0 _ hidsq)
      (elim.sqAt_of (elim.length_nullMat n0 n0)
        (elim.rowsLen_nullMat n0 n0))
      (elim.matNull_nullMat n0 n0)
  -- the coupling-block tie at the shared clearing
  have hCl : matOneValue
      (matScale X.2 (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X'.2 B')))
      (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale (X.2 * X'.2) B)) := by
    refine elim.matOne_trans
      (scalePad X.2 _ (matScale X'.2 B')) ?_
    rw [inertia.matScale_matScale X'.2 X.2 B']
    exact offPadCongr _
      (rectAt_rows (rectAt_matScale (X.2 * X'.2) B' n0 n1 hB'))
      (rectAt_rows (rectAt_matScale (X.2 * X'.2) B n0 n1 hB))
      (matScale_congrM (X.2 * X'.2) hoff0)
  have hCr : matOneValue
      (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X.2 B)))
      (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale (X.2 * X'.2) B)) := by
    refine elim.matOne_trans
      (scalePad X'.2 _ (matScale X.2 B)) ?_
    rw [inertia.matScale_matScale X.2 X'.2 B,
      ground.mul_comm X'.2 X.2]
    exact elim.matOne_refl _
  have hOlen : (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j) (matScale X.2 B))).length = n0 :=
    (length_matScale X'.2 _).trans hOl
  have hOrows : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X.2 B))) :=
    elim.rowsLen_mapRows _ _ _ hOr
  have hsOlen : (matScaleB (dn.scale (X.2 * X'.2))
      (elim.nullMat n0 (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j))).length = n0 :=
    (inertia.length_scaleB _ _).trans (elim.length_nullMat n0 _)
  have hsOrows : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (matScaleB (dn.scale (X.2 * X'.2))
        (elim.nullMat n0 (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j))) :=
    inertia.rowsLen_scaleB _ _ _ (elim.rowsLen_nullMat n0 _)
  have hNrows : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (matAdd (matScaleB (dn.scale (X.2 * X'.2))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j)))
        (elim.nullMat n0 (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j))) :=
    elim.rowsLen_matAdd _ _ _ hsOrows (elim.rowsLen_nullMat n0 _)
  have hNlen : (matAdd (matScaleB (dn.scale (X.2 * X'.2))
        (elim.nullMat n0 (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j)))
      (elim.nullMat n0 (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j))).length = n0 :=
    (elim.length_matAdd _ _
      (hsOlen.trans (elim.length_nullMat n0 _).symm)).trans hsOlen
  have habs : matOneValue
      (matAdd (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X.2 B)))
        (matAdd (matScaleB (dn.scale (X.2 * X'.2))
            (elim.nullMat n0 (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j)))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j))))
      (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X.2 B))) := by
    rw [elim.matAdd_comm]
    exact elim.matAdd_nullL _ _
      (elim.matNull_matAdd
        (nullScaleB _ _ (elim.matNull_nullMat _ n0))
        (elim.matNull_nullMat _ n0))
      (hNlen.trans hOlen.symm) hNrows hOrows
  have htieC : matOneValue
      (matScale X.2 (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X'.2 B')))
      (matAdd (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X.2 B)))
        (matAdd (matScaleB (dn.scale (X.2 * X'.2))
            (elim.nullMat n0 (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j)))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j)))) :=
    elim.matOne_trans hCl
      (elim.matOne_trans (elim.matOne_symm hCr)
        (elim.matOne_symm habs))
  -- the sum side at the joined order
  have hProws : rowsLen n0 (matScale X'.2 (matScale X.2 A)) :=
    elim.rowsLen_mapRows _ _ n0
      (elim.rowsLen_mapRows _ A n0 (elim.rowsLen_of_sqAt hA))
  have hPlen : (matScale X'.2 (matScale X.2 A)).length = n0 :=
    (length_matScale _ _).trans
      ((length_matScale _ _).trans (elim.sqAt_len hA))
  have hPNlen : (matAdd (matScaleB (dn.scale (X.2 * X'.2))
      (idMat n0)) (elim.nullMat n0 n0)).length = n0 :=
    (elim.length_matAdd _ _
      (hsPlen.trans (elim.length_nullMat n0 n0).symm)).trans hsPlen
  have hOTrows : rowsLen n0 (transposeM
      (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j) (matScale X.2 B)))) :=
    elim.rowsLen_cast hOlen (elim.rowsLen_transposeM _)
  have hQrows : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (matScale X'.2 (headM dt Bs X j)) :=
    elim.rowsLen_mapRows _ _ _ (elim.rowsLen_of_sqAt hQsq)
  have hRHrows : rowsLen (n0 + (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j))
      (matScale X'.2 (headM (A :: dt) (B :: Bs) X (j + 1))) := by
    rw [hcons]
    exact elim.rowsLen_mapRows _ _ _
      (inertia.rowsLen_blockJoin _ _ _ n0 _
        (elim.rowsLen_mapRows _ A n0 (elim.rowsLen_of_sqAt hA))
        hOr
        (elim.rowsLen_cast hOl (elim.rowsLen_transposeM _))
        (elim.rowsLen_of_sqAt hQsq))
  have hBJ1rows : rowsLen (n0 + (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j))
      (blockJoin (matScale X'.2 (matScale X.2 A))
        (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X.2 B)))
        (matScale X'.2 (headM dt Bs X j))) :=
    inertia.rowsLen_blockJoin _ _ _ n0 _
      hProws hOrows hOTrows hQrows
  have hSBrows : rowsLen (n0 + (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j))
      (matScaleB (dn.scale (X.2 * X'.2))
        (inertia.headId (n0 + ground.sumNat (List.take j nt))
          (ground.getAt 0 nt j))) :=
    elim.rowsLen_cast
      (Nat.add_assoc n0 (ground.sumNat (List.take j nt))
        (ground.getAt 0 nt j))
      (inertia.rowsLen_scaleB _ _ _
        (elim.rowsLen_of_sqAt (inertia.headId_sq
          (n0 + ground.sumNat (List.take j nt))
          (ground.getAt 0 nt j))))
  have hTProws : rowsLen (n0 + (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j))
      (inertia.trailPad (n0 + ground.sumNat (List.take j nt))
        (addQ X' (swapQ X)).1) :=
    elim.rowsLen_cast
      (Nat.add_assoc n0 (ground.sumNat (List.take j nt))
        (ground.getAt 0 nt j))
      (elim.rowsLen_of_sqAt (inertia.trailPad_sq _ hdev))
  have hsQrows : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (matScaleB (dn.scale (X.2 * X'.2))
        (inertia.headId (ground.sumNat (List.take j nt))
          (ground.getAt 0 nt j))) :=
    inertia.rowsLen_scaleB _ _ _
      (elim.rowsLen_of_sqAt (inertia.headId_sq
        (ground.sumNat (List.take j nt)) (ground.getAt 0 nt j)))
  have htQrows : rowsLen (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j)
      (inertia.trailPad (ground.sumNat (List.take j nt))
        (addQ X' (swapQ X)).1) :=
    elim.rowsLen_of_sqAt (inertia.trailPad_sq _ hdev)
  have hsOTrows : rowsLen n0 (transposeM
      (matScaleB (dn.scale (X.2 * X'.2))
        (elim.nullMat n0 (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j)))) :=
    elim.rowsLen_cast hsOlen (elim.rowsLen_transposeM _)
  have hBJ2rows : rowsLen (n0 + (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j))
      (blockJoin
        (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
        (matScaleB (dn.scale (X.2 * X'.2))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j)))
        (matScaleB (dn.scale (X.2 * X'.2))
          (inertia.headId (ground.sumNat (List.take j nt))
            (ground.getAt 0 nt j)))) :=
    inertia.rowsLen_blockJoin _ _ _ n0 _
      hsProws hsOrows hsOTrows hsQrows
  have hnOTrows : rowsLen n0 (transposeM
      (elim.nullMat n0 (ground.sumNat (List.take j nt)
        + ground.getAt 0 nt j))) :=
    elim.rowsLen_cast (elim.length_nullMat n0 _)
      (elim.rowsLen_transposeM _)
  have hBJ3rows : rowsLen (n0 + (ground.sumNat (List.take j nt)
      + ground.getAt 0 nt j))
      (blockJoin (elim.nullMat n0 n0)
        (elim.nullMat n0 (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j))
        (inertia.trailPad (ground.sumNat (List.take j nt))
          (addQ X' (swapQ X)).1)) :=
    inertia.rowsLen_blockJoin _ _ _ n0 _
      (elim.rowsLen_nullMat n0 n0)
      (elim.rowsLen_nullMat n0 _) hnOTrows htQrows
  have hsum2 : matAdd
      (blockJoin
        (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
        (matScaleB (dn.scale (X.2 * X'.2))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j)))
        (matScaleB (dn.scale (X.2 * X'.2))
          (inertia.headId (ground.sumNat (List.take j nt))
            (ground.getAt 0 nt j))))
      (blockJoin (elim.nullMat n0 n0)
        (elim.nullMat n0 (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j))
        (inertia.trailPad (ground.sumNat (List.take j nt))
          (addQ X' (swapQ X)).1))
      = blockJoin
        (matAdd (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
          (elim.nullMat n0 n0))
        (matAdd (matScaleB (dn.scale (X.2 * X'.2))
            (elim.nullMat n0 (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j)))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j)))
        (matAdd (matScaleB (dn.scale (X.2 * X'.2))
            (inertia.headId (ground.sumNat (List.take j nt))
              (ground.getAt 0 nt j)))
          (inertia.trailPad (ground.sumNat (List.take j nt))
            (addQ X' (swapQ X)).1)) :=
    inertia.matAdd_blockJoin _ _ _ _ _ _
      hsProws (elim.rowsLen_nullMat n0 n0)
      hsPlen (elim.length_nullMat n0 n0)
      hsOlen (elim.length_nullMat n0 _)
      hsOrows (elim.rowsLen_nullMat n0 _) hn0
  have hsum1 : matAdd
      (blockJoin (matScale X'.2 (matScale X.2 A))
        (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X.2 B)))
        (matScale X'.2 (headM dt Bs X j)))
      (blockJoin
        (matAdd (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
          (elim.nullMat n0 n0))
        (matAdd (matScaleB (dn.scale (X.2 * X'.2))
            (elim.nullMat n0 (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j)))
          (elim.nullMat n0 (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j)))
        (matAdd (matScaleB (dn.scale (X.2 * X'.2))
            (inertia.headId (ground.sumNat (List.take j nt))
              (ground.getAt 0 nt j)))
          (inertia.trailPad (ground.sumNat (List.take j nt))
            (addQ X' (swapQ X)).1)))
      = blockJoin
        (matAdd (matScale X'.2 (matScale X.2 A))
          (matAdd (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
            (elim.nullMat n0 n0)))
        (matAdd (matScale X'.2 (offPad
            (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j) (matScale X.2 B)))
          (matAdd (matScaleB (dn.scale (X.2 * X'.2))
              (elim.nullMat n0 (ground.sumNat (List.take j nt)
                + ground.getAt 0 nt j)))
            (elim.nullMat n0 (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j))))
        (matAdd (matScale X'.2 (headM dt Bs X j))
          (matAdd (matScaleB (dn.scale (X.2 * X'.2))
              (inertia.headId (ground.sumNat (List.take j nt))
                (ground.getAt 0 nt j)))
            (inertia.trailPad (ground.sumNat (List.take j nt))
              (addQ X' (swapQ X)).1))) :=
    inertia.matAdd_blockJoin _ _ _ _ _ _
      hProws hPnrows hPlen hPNlen hOlen hNlen hOrows hNrows hn0
  have hcong : matOneValue
      (matAdd (matScale X'.2 (headM (A :: dt) (B :: Bs) X (j + 1)))
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2))
            (inertia.headId (n0 + ground.sumNat (List.take j nt))
              (ground.getAt 0 nt j)))
          (inertia.trailPad (n0 + ground.sumNat (List.take j nt))
            (addQ X' (swapQ X)).1)))
      (matAdd
        (blockJoin (matScale X'.2 (matScale X.2 A))
          (matScale X'.2 (offPad (ground.sumNat (List.take j nt)
            + ground.getAt 0 nt j) (matScale X.2 B)))
          (matScale X'.2 (headM dt Bs X j)))
        (matAdd
          (blockJoin
            (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
            (matScaleB (dn.scale (X.2 * X'.2))
              (elim.nullMat n0 (ground.sumNat (List.take j nt)
                + ground.getAt 0 nt j)))
            (matScaleB (dn.scale (X.2 * X'.2))
              (inertia.headId (ground.sumNat (List.take j nt))
                (ground.getAt 0 nt j))))
          (blockJoin (elim.nullMat n0 n0)
            (elim.nullMat n0 (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j))
            (inertia.trailPad (ground.sumNat (List.take j nt))
              (addQ X' (swapQ X)).1)))) :=
    elim.matAdd_cong2 _ _ _ _ _
      hRHrows (elim.rowsLen_matAdd _ _ _ hSBrows hTProws)
      hBJ1rows (elim.rowsLen_matAdd _ _ _ hBJ2rows hBJ3rows)
      hR1
      (elim.matAdd_cong2 _ _ _ _ _ hSBrows hTProws
        hBJ2rows hBJ3rows hR2 hpeelT)
  have hjoin : matOneValue
      (blockJoin (matScale X.2 (matScale X'.2 A'))
        (matScale X.2 (offPad (ground.sumNat (List.take j nt)
          + ground.getAt 0 nt j) (matScale X'.2 B')))
        (matScale X.2 (headM dt' Bs' X' j)))
      (blockJoin
        (matAdd (matScale X'.2 (matScale X.2 A))
          (matAdd (matScaleB (dn.scale (X.2 * X'.2)) (idMat n0))
            (elim.nullMat n0 n0)))
        (matAdd (matScale X'.2 (offPad
            (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j) (matScale X.2 B)))
          (matAdd (matScaleB (dn.scale (X.2 * X'.2))
              (elim.nullMat n0 (ground.sumNat (List.take j nt)
                + ground.getAt 0 nt j)))
            (elim.nullMat n0 (ground.sumNat (List.take j nt)
              + ground.getAt 0 nt j))))
        (matAdd (matScale X'.2 (headM dt Bs X j))
          (matAdd (matScaleB (dn.scale (X.2 * X'.2))
              (inertia.headId (ground.sumNat (List.take j nt))
                (ground.getAt 0 nt j)))
            (inertia.trailPad (ground.sumNat (List.take j nt))
              (addQ X' (swapQ X)).1)))) :=
    inertia.blockJoin_congr _ _ _ _ _ _
      (elim.rowsLen_mapRows _ _ n0
        (elim.rowsLen_mapRows _ A' n0 (elim.rowsLen_of_sqAt hA')))
      (elim.rowsLen_matAdd n0 _ _ hProws hPnrows)
      ((length_matScale _ _).trans hOl')
      ((elim.length_matAdd _ _ (hOlen.trans hNlen.symm)).trans hOlen)
      (elim.rowsLen_mapRows _ _ _ hOr')
      (elim.rowsLen_matAdd _ _ _ hOrows hNrows)
      htieP htieC hIH
  refine elim.matOne_trans hL
    (elim.matOne_trans hjoin (elim.matOne_symm ?_))
  rw [hsum2, hsum1] at hcong
  exact hcong

private theorem tieGo (dn : BPair) (X X' : MatQ) :
    ∀ (j : Nat) (diag off diag' off' : List Mat) (ns : List Nat),
    slabShape diag off ns → slabShape diag' off' ns →
    j < ns.length →
    sqAt X.1 (ground.getAt 0 ns j) →
    sqAt X'.1 (ground.getAt 0 ns j) →
    (∀ i, i < j → matOneValue (ground.getAt [] diag' i)
      (matAdd (ground.getAt [] diag i)
        (matScaleB dn (idMat (ground.getAt 0 ns i))))) →
    (∀ i, i < j → matOneValue (ground.getAt [] off' i)
      (ground.getAt [] off i)) →
    matOneValue (matScale X.2 (headM diag' off' X' j))
      (matAdd (matScale X'.2 (headM diag off X j))
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2))
            (inertia.headId (ground.sumNat (List.take j ns))
              (ground.getAt 0 ns j)))
          (inertia.trailPad (ground.sumNat (List.take j ns))
            (addQ X' (swapQ X)).1)))
  | 0, _, _, _, _, ns, _, _, _, hX, hX', _, _ =>
    tieBase dn X X' (ground.getAt 0 ns 0) hX hX'
  | j + 1, diag, off, diag', off', ns, hs, hs', hj, hX, hX',
      hdag, hoff => by
    cases diag with
    | nil => exact hs.elim
    | cons A dt =>
    cases ns with
    | nil => exact hs.elim
    | cons n0 nt =>
    cases nt with
    | nil =>
      exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero _)
    | cons n1 nrest =>
    cases dt with
    | nil =>
      cases off with
      | nil => exact hs.elim
      | cons _ _ => exact hs.elim
    | cons A2 As =>
    cases off with
    | nil => exact hs.elim
    | cons B Bs =>
    cases diag' with
    | nil => exact hs'.elim
    | cons A' dt' =>
    cases dt' with
    | nil =>
      cases off' with
      | nil => exact hs'.elim
      | cons _ _ => exact hs'.elim
    | cons A2' As' =>
    cases off' with
    | nil => exact hs'.elim
    | cons B' Bs' =>
    -- the slab walks' conjuncts
    have hn0 : 0 < n0 := hs.1
    have hA : sqAt A n0 := hs.2.1
    have hB : rectAt B n0 n1 := hs.2.2.1
    have hst : slabShape (A2 :: As) Bs (n1 :: nrest) := hs.2.2.2
    have hA' : sqAt A' n0 := hs'.2.1
    have hB' : rectAt B' n0 n1 := hs'.2.2.1
    have hst' : slabShape (A2' :: As') Bs' (n1 :: nrest) := hs'.2.2.2
    have hjt : j < (n1 :: nrest).length := Nat.lt_of_succ_lt_succ hj
    have hIH := tieGo dn X X' j (A2 :: As) Bs (A2' :: As') Bs'
      (n1 :: nrest) hst hst' hjt hX hX'
      (fun i hi => hdag (i + 1) (Nat.succ_lt_succ hi))
      (fun i hi => hoff (i + 1) (Nat.succ_lt_succ hi))
    -- the widths
    have hQsq : sqAt (headM (A2 :: As) Bs X j)
        (ground.sumNat (List.take j (n1 :: nrest))
          + ground.getAt 0 (n1 :: nrest) j) :=
      headM_sq _ _ X j _ hst hjt hX
    have hQ'sq : sqAt (headM (A2' :: As') Bs' X' j)
        (ground.sumNat (List.take j (n1 :: nrest))
          + ground.getAt 0 (n1 :: nrest) j) :=
      headM_sq _ _ X' j _ hst' hjt hX'
    have hle : n1 ≤ ground.sumNat (List.take j (n1 :: nrest))
        + ground.getAt 0 (n1 :: nrest) j :=
      ground.headKey_le (n1 :: nrest) j hjt
    -- the two heads peel one slab
    have hcons : headM (A :: A2 :: As) (B :: Bs) X (j + 1)
        = blockJoin (matScale X.2 A)
          (offPad (ground.sumNat (List.take j (n1 :: nrest))
            + ground.getAt 0 (n1 :: nrest) j) (matScale X.2 B))
          (headM (A2 :: As) Bs X j) := by
      show assemble (matScale X.2 A
          :: (List.map (matScale X.2) (List.take j (A2 :: As))
            ++ [X.1]))
        (matScale X.2 B
          :: List.map (matScale X.2) (List.take j Bs)) = _
      exact assemble_cons _ _ _ _ n0 n1 _
        ((length_matScale X.2 A).trans (elim.sqAt_len hA)) hn0
        ((length_matScale X.2 B).trans (rectAt_len hB))
        (rectAt_rows (rectAt_matScale X.2 B n0 n1 hB)) hle
        (elim.sqAt_len hQsq) (sqAt_headD _ _ hQsq)
    have hcons' : headM (A' :: A2' :: As') (B' :: Bs') X' (j + 1)
        = blockJoin (matScale X'.2 A')
          (offPad (ground.sumNat (List.take j (n1 :: nrest))
            + ground.getAt 0 (n1 :: nrest) j) (matScale X'.2 B'))
          (headM (A2' :: As') Bs' X' j) := by
      show assemble (matScale X'.2 A'
          :: (List.map (matScale X'.2) (List.take j (A2' :: As'))
            ++ [X'.1]))
        (matScale X'.2 B'
          :: List.map (matScale X'.2) (List.take j Bs')) = _
      exact assemble_cons _ _ _ _ n0 n1 _
        ((length_matScale X'.2 A').trans (elim.sqAt_len hA')) hn0
        ((length_matScale X'.2 B').trans (rectAt_len hB'))
        (rectAt_rows (rectAt_matScale X'.2 B' n0 n1 hB')) hle
        (elim.sqAt_len hQ'sq) (sqAt_headD _ _ hQ'sq)
    exact tieStep dn X X' j A A' B B' (A2 :: As) (A2' :: As')
      Bs Bs' (n1 :: nrest) n0 hn0 hA hA' hB hB' hle hX hX'
      hQsq hcons hcons' hIH
      (hdag 0 (Nat.succ_pos j)) (hoff 0 (Nat.succ_pos j))

/-- Two decimated heads at one shared clearing, the couplings equal
and each leading diagonal tied at the drift `dn`, differ by the
drift's head identity at the leading keys' total and the pivots'
deviation at the trailing pad, every member cross-multiplied through
the two clearings. -/
theorem headM_tie (diag off diag' off' : List Mat) (X X' : MatQ)
    (j : Nat) (ns : List Nat) (dn : BPair)
    (hs : slabShape diag off ns)
    (hs' : slabShape diag' off' ns)
    (hj : j < ns.length)
    (hX : sqAt X.1 (ground.getAt 0 ns j))
    (hX' : sqAt X'.1 (ground.getAt 0 ns j))
    (hdag : ∀ i, i < j → matOneValue (ground.getAt [] diag' i)
      (matAdd (ground.getAt [] diag i)
        (matScaleB dn (idMat (ground.getAt 0 ns i)))))
    (hoff : ∀ i, i < j → matOneValue (ground.getAt [] off' i)
      (ground.getAt [] off i)) :
    matOneValue (matScale X.2 (headM diag' off' X' j))
      (matAdd (matScale X'.2 (headM diag off X j))
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2))
            (inertia.headId (ground.sumNat (List.take j ns))
              (ground.getAt 0 ns j)))
          (inertia.trailPad (ground.sumNat (List.take j ns))
            (addQ X' (swapQ X)).1))) :=
  tieGo dn X X' j diag off diag' off' ns hs hs' hj hX hX' hdag hoff

private theorem mulLtUnit (c : Pos) {x : BPair} (h : x < BPair.unit) :
    BPair.ofPos c * x < BPair.unit :=
  BPair.lt_congr (BPair.oneValue_symm (BPair.ofPos_scale c x))
    (BPair.oneValue_refl BPair.unit) (scaleLtUnit c h)

private theorem ltUnitOfMul {c : Pos} {x : BPair}
    (h : BPair.ofPos c * x < BPair.unit) : x < BPair.unit :=
  ltUnitOfScale (BPair.lt_congr (BPair.ofPos_scale c x)
    (BPair.oneValue_refl BPair.unit) h)

private theorem unitLeOfMul {c : Pos} {x : BPair}
    (h : BPair.unit ≤ BPair.ofPos c * x) : BPair.unit ≤ x :=
  unitLeOfScale (w := c)
    (ground.leB_congr_right (BPair.ofPos_scale c x) h)

private theorem unitLeMulPos (c : Pos) {x : BPair}
    (h : BPair.unit ≤ x) : BPair.unit ≤ BPair.ofPos c * x :=
  ground.leB_congr_right (BPair.oneValue_symm (BPair.ofPos_scale c x))
    (unitLeScale c h)

/-! The weighted-vector kit: the weight's distribution over the
memberwise sum, the weights' composition, the memberwise swap's
passage, and the summand's withdrawal at a stated join. -/

private theorem vecAdd_moveR : ∀ (Xv Q P : List BPair),
    Xv.length = Q.length → Q.length = P.length →
    poly.oneValue (vecAdd Xv Q) P →
    poly.oneValue (vecAdd P (Q.map BPair.swap)) Xv
  | [], [], [], _, _, _ => trivial
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl
  | _ :: _, _ :: _, [], _, hl, _ => nomatch hl
  | x :: Xv, q :: Q, _ :: P, hl, hl', h =>
    ⟨BPair.oneValue_trans
       (BPair.add_congr (BPair.oneValue_symm h.1)
         (BPair.oneValue_refl q.swap))
       (BPair.oneValue_trans
         (BPair.oneValue_of_eq (BPair.add_assoc x q q.swap))
         (BPair.oneValue_trans
           (BPair.add_congr (BPair.oneValue_refl x)
             (BPair.oneValue_trans
               (BPair.oneValue_of_eq (BPair.add_comm q q.swap))
               (BPair.swap_add_null (BPair.oneValue_refl q))))
           (BPair.add_unit x))),
     vecAdd_moveR Xv Q P (Nat.succ.inj hl) (Nat.succ.inj hl') h.2⟩

/-! The telescoped lift at the tail witnesses: the clearing product
over the witness tail, the telescope matrix, and its action. -/

/-- The clearing product over a witness tail. -/
private def clProd : List MatQ → Pos
  | [] => Pos.one
  | R :: t => R.2 * clProd t

/-- The telescope matrix at a seed slab: the seed's weighted
identity above, the stepped telescope beneath, each step the
witness's memberwise swap. -/
private def liftMat : Nat → List MatQ → Mat
  | k, [] => matScaleB (BPair.ofPos Pos.one) (idMat k)
  | k, R :: Rs => matScaleB (BPair.ofPos (clProd (R :: Rs))) (idMat k)
      ++ matMul (liftMat R.1.length Rs) (matSwap R.1)

/-- The telescope's blocks beyond the seed slab. -/
private def liftTail : List MatQ → List BPair → List BPair
  | [], _ => []
  | R :: Rs, w => matVec (liftMat R.1.length Rs) (matVec (matSwap R.1) w)

private theorem liftMat_nil_act (k : Nat) (w : List BPair)
    (hw : w.length = k) :
    poly.oneValue (matVec (liftMat k []) w) w :=
  poly.oneValue_trans (scaleId_act (BPair.ofPos Pos.one) k w hw)
    (elim.vecScale_one w)

private theorem liftMat_cons_act (k : Nat) (R : MatQ) (Rs : List MatQ)
    (hR : rowsLen k R.1) (w : List BPair) (hw : w.length = k) :
    poly.oneValue (matVec (liftMat k (R :: Rs)) w)
      (elim.vecScale (BPair.ofPos (clProd (R :: Rs))) w
        ++ matVec (liftMat R.1.length Rs) (matVec (matSwap R.1) w)) := by
  show poly.oneValue
    (matVec (matScaleB (BPair.ofPos (clProd (R :: Rs))) (idMat k)
      ++ matMul (liftMat R.1.length Rs) (matSwap R.1)) w) _
  rw [elim.matVec_append]
  refine poly.oneValue_append _ _ _ _ ?_ ?_ ?_
  · rw [matVec_length, length_scaleB, idMat_len, length_vecScale, hw]
  · exact scaleId_act _ k w hw
  · exact matVec_matMul _ _ k
      (rowsLen_mapRows BPair.swap R.1 k hR) w hw

private theorem liftMat_act : ∀ (k : Nat) (Rs : List MatQ)
    (w : List BPair), w.length = k →
    (∀ R Rs', Rs = R :: Rs' → rowsLen k R.1) →
    poly.oneValue (matVec (liftMat k Rs) w)
      (elim.vecScale (BPair.ofPos (clProd Rs)) w ++ liftTail Rs w)
  | k, [], w, hw, _ => by
    show poly.oneValue (matVec (liftMat k []) w)
      (elim.vecScale (BPair.ofPos Pos.one) w ++ [])
    rw [ground.append_nil]
    exact poly.oneValue_trans (liftMat_nil_act k w hw)
      (poly.oneValue_symm (elim.vecScale_one w))
  | k, R :: Rs, w, hw, hR => liftMat_cons_act k R Rs (hR R Rs rfl) w hw

/-- The off-block's exchange at the trailing order splits: the
exchange's own rows above, rows of the sum's unit beneath. -/
theorem offT_split (k : Nat) (bt : Mat) (m : Nat)
    (h : bt.length ≤ m) :
    offT k bt m
      = bt ++ List.replicate (m - bt.length)
          (List.replicate k BPair.unit) := by
  refine ground.getAt_ext ([] : List BPair) _ _ ?_ ?_
  · rw [offT_len, ground.length_append, ground.length_replicate,
      ground.natAddSubCancel h]
  · intro i hi
    rw [offT_len] at hi
    show ground.getAt ([] : List BPair) ((List.range m).map (fun r =>
        if r < bt.length then ground.getAt [] bt r
        else List.replicate k BPair.unit)) i
      = ground.getAt [] (bt ++ List.replicate (m - bt.length)
          (List.replicate k BPair.unit)) i
    rw [ground.getAt_map_range ([] : List BPair) _ m i, if_pos hi,
      ground.getAt_append]
    by_cases hb : i < bt.length
    · rw [if_pos hb, if_pos hb]
    · rw [if_neg hb, if_neg hb,
        ground.getAt_replicate ([] : List BPair)
          (List.replicate k BPair.unit) (m - bt.length)
          (i - bt.length)
          (subLtSubR bt.length i m (Nat.le_of_not_lt hb) hi)]

/-- The padded off-block's action reads the block against the
leading part of its argument. -/
theorem offPad_act (w n1 : Nat) (B : Mat) (hB : rowsLen n1 B)
    (v1 v2 : List BPair) (h1 : v1.length = n1) :
    poly.oneValue (matVec (offPad w B) (v1 ++ v2)) (matVec B v1) := by
  show poly.oneValue
    ((B.map (padRow w)).map (fun r => dotN r (v1 ++ v2)))
    (B.map (fun r => dotN r v1))
  rw [ground.map_map]
  refine poly.oneValue_map _ _ B ?_
  intro rb hrb
  show (dotN (rb ++ List.replicate (w - rb.length) BPair.unit)
    (v1 ++ v2)).oneValue (dotN rb v1)
  refine BPair.oneValue_trans (dotN_app rb _ v1 v2 ?_) ?_
  · rw [elim.rowsLen_of_mem hB hrb, h1]
  · exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (dotN_nullL _ v2 (poly.unitTail_replicate _)))
      (BPair.add_unit _)

/-! The tail recursion's per-key projections and its own tail. -/

private theorem tailSteps_at : ∀ (diag off : List Mat)
    (Xs Rs : List MatQ), tailSteps diag off Xs Rs → ∀ (i : Nat),
    i < Rs.length →
    ¬ (minor (ground.getAt dM Xs (i + 1)).1).oneValue BPair.unit
    ∧ oneValueQ (mulQ (ground.getAt dM Xs (i + 1)) (ground.getAt dM Rs i))
        (ofM (transposeM (ground.getAt [] off i)))
    ∧ oneValueQ (addQ (ground.getAt dM Xs i)
        (mulQ (ofM (ground.getAt [] off i)) (ground.getAt dM Rs i)))
      (ofM (ground.getAt [] diag i))
  | [], _, _, _, h, _, _ => h.elim
  | [_], [], [_], [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | [_], [], [_], _ :: _, h, _, _ => h.elim
  | [_], [], [], _, h, _, _ => h.elim
  | [_], [], _ :: _ :: _, _, h, _, _ => h.elim
  | [_], _ :: _, _, _, h, _, _ => h.elim
  | _ :: _ :: _, [], _, _, h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, [], _, h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, [_], _, h, _, _ => h.elim
  | _ :: _ :: _, _ :: _, _ :: _ :: _, [], _, _, hi =>
    absurd hi (Nat.not_lt_zero _)
  | _ :: _ :: _, _ :: _, _ :: _ :: _, _ :: _, h, 0, _ => h.1
  | _ :: A' :: As, _ :: Bs, _ :: X' :: Xs, _ :: Rs, h, i + 1, hi =>
    tailSteps_at (A' :: As) Bs (X' :: Xs) Rs h.2 i
      (Nat.lt_of_succ_lt_succ hi)

private theorem tail_step {diag off : List Mat} {Xs Rs : List MatQ}
    {ns : List Nat} (h : tailRead diag off Xs Rs ns) (i : Nat)
    (hi : i < Rs.length) :
    ¬ (minor (ground.getAt dM Xs (i + 1)).1).oneValue BPair.unit
    ∧ oneValueQ (mulQ (ground.getAt dM Xs (i + 1)) (ground.getAt dM Rs i))
        (ofM (transposeM (ground.getAt [] off i)))
    ∧ oneValueQ (addQ (ground.getAt dM Xs i)
        (mulQ (ofM (ground.getAt [] off i)) (ground.getAt dM Rs i)))
      (ofM (ground.getAt [] diag i)) :=
  tailSteps_at diag off Xs Rs h.2.2.2 i hi

theorem qShape_at : ∀ {Xs : List MatQ} {ns : List Nat},
    qShape Xs ns → ∀ (i : Nat), i < Xs.length →
    sqAt (ground.getAt dM Xs i).1 (ground.getAt 0 ns i)
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _ => h.1
  | _ :: _, _ :: _, h, i + 1, hi =>
    qShape_at h.2 i (Nat.lt_of_succ_lt_succ hi)

private theorem wShapeR_at : ∀ {Rs : List MatQ} {ns : List Nat},
    wShapeR Rs ns → ∀ (i : Nat), i < Rs.length →
    rectAt (ground.getAt dM Rs i).1 (ground.getAt 0 ns (i + 1))
      (ground.getAt 0 ns i)
  | [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, [_], h, _, _ => h.elim
  | _ :: _, _ :: _ :: _, h, 0, _ => h.1
  | _ :: _, _ :: _ :: _, h, i + 1, hi =>
    wShapeR_at h.2 i (Nat.lt_of_succ_lt_succ hi)

private theorem tailRead_tail {A B : Mat} {As Bs : List Mat}
    {X0 R0 : MatQ} {Xt Rt : List MatQ} {n0 : Nat} {nt : List Nat}
    (h : tailRead (A :: As) (B :: Bs) (X0 :: Xt) (R0 :: Rt) (n0 :: nt)) :
    tailRead As Bs Xt Rt nt := by
  refine ⟨slabShape_tail h.1, h.2.1.2, ?_, ?_⟩
  · cases nt with
    | nil => exact (h.2.2.1 : False).elim
    | cons k' nt' => exact h.2.2.1.2
  · cases As with
    | nil => exact (h.2.2.2 : False).elim
    | cons A' As' =>
      cases Xt with
      | nil => exact (h.2.2.2 : False).elim
      | cons X1 Xt' => exact h.2.2.2.2

private theorem polyOfEq {u v : List BPair} (h : u = v) :
    poly.oneValue u v := h ▸ poly.oneValue_refl u

private theorem posSwap3 (a b c : Pos) : c * (a * b) = a * (b * c) := by
  rw [ground.mul_left_comm c a b, ground.mul_comm c b]

theorem vecScale_two (a b : Pos) (u : List BPair) :
    poly.oneValue
      (elim.vecScale (BPair.ofPos a) (elim.vecScale (BPair.ofPos b) u))
      (elim.vecScale (BPair.ofPos (a * b)) u) :=
  poly.oneValue_trans
    (poly.oneValue_of_eq
      (elim.vecScale_vecScale (BPair.ofPos a) (BPair.ofPos b) u))
    (elim.vecScale_congr (BPair.ofPos_mul a b) u)

theorem vecScale_posEq {a b : Pos} (h : a = b) (u : List BPair) :
    elim.vecScale (BPair.ofPos a) u = elim.vecScale (BPair.ofPos b) u :=
  congrArg (fun z => elim.vecScale (BPair.ofPos z) u) h

/-- The lift's slab row: the diagonal block against the weighted
seed with the off-block against the stepped telescope reads the
slab's own pivot, the recursion's join cross-multiplied. -/
private theorem lift_upper (A B : Mat) (X0 R0 : MatQ) (n0 : Nat)
    (d : Pos) (w : List BPair) (hw : w.length = n0)
    (hAl : A.length = n0) (hX0l : X0.1.length = n0)
    (hBl : B.length = n0) (hX0r : rowsLen n0 X0.1)
    (hMr : rowsLen n0 (matMul B R0.1))
    (hjoin : oneValueQ (addQ X0 (mulQ (ofM B) R0)) (ofM A)) :
    poly.oneValue
      (elim.vecScale (BPair.ofPos X0.2)
        (vecAdd (matVec A (elim.vecScale (BPair.ofPos (R0.2 * d)) w))
          (elim.vecScale (BPair.ofPos d)
            ((matVec (matMul B R0.1) w).map BPair.swap))))
      (elim.vecScale (BPair.ofPos (R0.2 * d)) (matVec X0.1 w)) := by
  have hp : (matVec A w).length = n0 := (matVec_length A w).trans hAl
  have hq : (matVec (matMul B R0.1) w).length = n0 :=
    (matVec_length _ w).trans ((ground.length_map _ B).trans hBl)
  have hx : (matVec X0.1 w).length = n0 :=
    (matVec_length X0.1 w).trans hX0l
  have hj0 : matOneValue (matScale Pos.one
      (matAdd (matScale (Pos.one * R0.2) X0.1)
        (matScale X0.2 (matMul B R0.1))))
      (matScale (X0.2 * (Pos.one * R0.2)) A) := hjoin
  rw [matScale_one, ground.one_mul R0.2] at hj0
  have hMlen : (matScale R0.2 X0.1).length = n0 :=
    (length_matScale R0.2 X0.1).trans hX0l
  have hNlen : (matScale X0.2 (matMul B R0.1)).length = n0 :=
    (length_matScale X0.2 _).trans ((ground.length_map _ B).trans hBl)
  have hadd := matVec_add (matScale R0.2 X0.1)
    (matScale X0.2 (matMul B R0.1)) w
    (rowsLen_cast hw.symm (elim.rowsLen_mapRows _ X0.1 n0 hX0r))
    (rowsLen_cast hw.symm (elim.rowsLen_mapRows _ _ n0 hMr))
  have hJ : poly.oneValue
      (vecAdd (elim.vecScale (BPair.ofPos R0.2) (matVec X0.1 w))
        (elim.vecScale (BPair.ofPos X0.2) (matVec (matMul B R0.1) w)))
      (elim.vecScale (BPair.ofPos (X0.2 * R0.2)) (matVec A w)) := by
    refine poly.oneValue_trans (poly.oneValue_symm (elim.polyOne_vecAdd _ _ _ _
      (matVec_matScale R0.2 X0.1 w) (matVec_matScale X0.2 _ w)
      ((matVec_length _ w).trans (hMlen.trans
        ((length_vecScale _ _).trans hx).symm))
      ((matVec_length _ w).trans (hNlen.trans
        ((length_vecScale _ _).trans hq).symm)))) ?_
    exact poly.oneValue_trans (poly.oneValue_symm hadd)
      (poly.oneValue_trans (matVec_matOne _ _ w hj0)
        (matVec_matScale (X0.2 * R0.2) A w))
  have hJd : poly.oneValue
      (vecAdd (elim.vecScale (BPair.ofPos (R0.2 * d)) (matVec X0.1 w))
        (elim.vecScale (BPair.ofPos (X0.2 * d))
          (matVec (matMul B R0.1) w)))
      (elim.vecScale (BPair.ofPos (X0.2 * (R0.2 * d))) (matVec A w)) := by
    refine poly.oneValue_trans (poly.oneValue_symm (elim.polyOne_vecAdd _ _ _ _
      (poly.oneValue_trans (vecScale_two d R0.2 (matVec X0.1 w))
        (polyOfEq
          (vecScale_posEq (ground.mul_comm d R0.2) (matVec X0.1 w))))
      (poly.oneValue_trans (vecScale_two d X0.2
        (matVec (matMul B R0.1) w))
        (polyOfEq (vecScale_posEq (ground.mul_comm d X0.2)
          (matVec (matMul B R0.1) w))))
      (by rw [length_vecScale, length_vecScale, length_vecScale])
      (by rw [length_vecScale, length_vecScale, length_vecScale]))) ?_
    refine poly.oneValue_trans (poly.oneValue_symm
      (poly.oneValue_of_eq (elim.vecScale_vecAdd (BPair.ofPos d) _ _))) ?_
    refine poly.oneValue_trans
      (elim.vecScale_oneValue (BPair.ofPos d) _ _ hJ) ?_
    exact poly.oneValue_trans (vecScale_two d (X0.2 * R0.2) (matVec A w))
      (polyOfEq
        (vecScale_posEq (posSwap3 X0.2 R0.2 d) (matVec A w)))
  have hmove := vecAdd_moveR
    (elim.vecScale (BPair.ofPos (R0.2 * d)) (matVec X0.1 w))
    (elim.vecScale (BPair.ofPos (X0.2 * d)) (matVec (matMul B R0.1) w))
    (elim.vecScale (BPair.ofPos (X0.2 * (R0.2 * d))) (matVec A w))
    (by rw [length_vecScale, length_vecScale, hx, hq])
    (by rw [length_vecScale, length_vecScale, hq, hp]) hJd
  refine poly.oneValue_trans ?_ hmove
  refine poly.oneValue_trans (elim.vecScale_oneValue (BPair.ofPos X0.2) _ _
    (elim.polyOne_vecAdd _ _ _ _
      (matVec_vecScale_free A (BPair.ofPos (R0.2 * d)) w)
      (poly.oneValue_refl (elim.vecScale (BPair.ofPos d)
        ((matVec (matMul B R0.1) w).map BPair.swap)))
      (by rw [matVec_length, hAl, length_vecScale, hp])
      rfl)) ?_
  refine poly.oneValue_trans
    (poly.oneValue_of_eq (elim.vecScale_vecAdd (BPair.ofPos X0.2) _ _)) ?_
  refine elim.polyOne_vecAdd _ _ _ _ ?_ ?_ ?_ ?_
  · exact poly.oneValue_trans (vecScale_two X0.2 (R0.2 * d) (matVec A w))
      (poly.oneValue_refl _)
  · rw [elim.vecScale_swapMap (BPair.ofPos d) (matVec (matMul B R0.1) w),
      elim.vecScale_swapMap (BPair.ofPos X0.2)
        (elim.vecScale (BPair.ofPos d) (matVec (matMul B R0.1) w))]
    exact poly.swapMap_oneValue
      (vecScale_two X0.2 d (matVec (matMul B R0.1) w))
  · rw [length_vecScale, length_vecScale, length_vecScale]
  · rw [length_vecScale, ground.length_map, length_vecScale,
      length_vecScale, ground.length_map]

/-- The lift's rows beyond the slab: the off-block's exchange
against the weighted seed and the trailing assembly against the
stepped telescope read the sum's unit, the witness's own join
cross-multiplied. -/
private theorem lift_lower (B : Mat) (X1 R0 : MatQ) (rest : Mat)
    (n0 n1 m : Nat) (d : Pos) (w : List BPair) (hw : w.length = n0)
    (hBl : B.length = n0) (hBr : rowsLen n1 B) (hk : 0 < n0)
    (hR0l : R0.1.length = n1) (hR0r : rowsLen n0 R0.1)
    (hX1l : X1.1.length = n1) (hX1r : rowsLen n1 X1.1)
    (hn1m : n1 ≤ m) (hml : rest.length = m)
    (hjoin : oneValueQ (mulQ X1 R0) (ofM (transposeM B)))
    (b : List BPair)
    (hIH : poly.oneValue
      (elim.vecScale (BPair.ofPos X1.2) (matVec rest b))
      (elim.vecScale (BPair.ofPos d)
        (matVec X1.1 (matVec (matSwap R0.1) w))
        ++ List.replicate (m - n1) BPair.unit)) :
    poly.unitTail
      (vecAdd (matVec (offT n0 (transposeM B) m)
          (elim.vecScale (BPair.ofPos (R0.2 * d)) w))
        (matVec rest b)) := by
  have hbtl : (transposeM B).length = n1 :=
    length_transposeM B hBr (by rw [hBl]; exact hk)
  have hbtw : (matVec (transposeM B) w).length = n1 :=
    (matVec_length _ w).trans hbtl
  have hswl : (matSwap R0.1).length = n1 :=
    (ground.length_map _ R0.1).trans hR0l
  have hzl : (elim.vecScale (BPair.ofPos (X1.2 * (R0.2 * d)))
      (matVec (transposeM B) w)).length = n1 :=
    (length_vecScale _ _).trans hbtw
  have hj1 : matOneValue (matScale Pos.one (matMul X1.1 R0.1))
      (matScale (X1.2 * R0.2) (transposeM B)) := hjoin
  rw [matScale_one] at hj1
  have hstep : poly.oneValue (matVec X1.1 (matVec (matSwap R0.1) w))
      ((elim.vecScale (BPair.ofPos (X1.2 * R0.2))
        (matVec (transposeM B) w)).map BPair.swap) := by
    refine poly.oneValue_trans (matVec_comp X1.1 (matSwap R0.1) w n0
      (rowsLen_mapRows BPair.swap R0.1 n0 hR0r) hw
      (rowsLen_cast hswl.symm hX1r)) ?_
    rw [matMul_swap, matVec_swapM]
    exact poly.swapMap_oneValue
      (poly.oneValue_trans (matVec_matOne _ _ w hj1)
        (matVec_matScale (X1.2 * R0.2) (transposeM B) w))
  have hLow : poly.oneValue
      (elim.vecScale (BPair.ofPos d)
        (matVec X1.1 (matVec (matSwap R0.1) w)))
      ((elim.vecScale (BPair.ofPos (X1.2 * (R0.2 * d)))
        (matVec (transposeM B) w)).map BPair.swap) := by
    refine poly.oneValue_trans
      (elim.vecScale_oneValue (BPair.ofPos d) _ _ hstep) ?_
    rw [elim.vecScale_swapMap]
    refine poly.swapMap_oneValue ?_
    exact poly.oneValue_trans
      (vecScale_two d (X1.2 * R0.2) (matVec (transposeM B) w))
      (polyOfEq (vecScale_posEq (posSwap3 X1.2 R0.2 d)
        (matVec (transposeM B) w)))
  have hUp : poly.oneValue
      (elim.vecScale (BPair.ofPos X1.2)
        (matVec (transposeM B)
          (elim.vecScale (BPair.ofPos (R0.2 * d)) w)))
      (elim.vecScale (BPair.ofPos (X1.2 * (R0.2 * d)))
        (matVec (transposeM B) w)) :=
    poly.oneValue_trans (elim.vecScale_oneValue (BPair.ofPos X1.2) _ _
      (matVec_vecScale_free (transposeM B) (BPair.ofPos (R0.2 * d)) w))
      (vecScale_two X1.2 (R0.2 * d) (matVec (transposeM B) w))
  rw [offT_split n0 (transposeM B) m (by rw [hbtl]; exact hn1m),
    elim.matVec_append, hbtl]
  refine elim.unitTail_unscale (BPair.ofPos X1.2) (BPair.ofPos_off X1.2)
    _ ?_
  refine poly.oneValue_unitTail
    (poly.oneValue_of_eq (elim.vecScale_vecAdd (BPair.ofPos X1.2) _ _)) ?_
  rw [elim.vecScale_append]
  have hrhs : (elim.vecScale (BPair.ofPos d)
      (matVec X1.1 (matVec (matSwap R0.1) w))
      ++ List.replicate (m - n1) BPair.unit).length = m := by
    rw [ground.length_append, length_vecScale, matVec_length, hX1l,
      ground.length_replicate, ground.natAddSubCancel hn1m]
  refine poly.oneValue_unitTail (elim.polyOne_vecAdd _ _ _ _
    (poly.oneValue_refl _) hIH rfl
    (((length_vecScale _ _).trans
      ((matVec_length _ _).trans hml)).trans hrhs.symm)) ?_
  have hseam : (elim.vecScale (BPair.ofPos X1.2)
      (matVec (transposeM B)
        (elim.vecScale (BPair.ofPos (R0.2 * d)) w))).length
      = (elim.vecScale (BPair.ofPos d)
        (matVec X1.1 (matVec (matSwap R0.1) w))).length := by
    rw [length_vecScale, matVec_length, hbtl, length_vecScale,
      matVec_length, hX1l]
  rw [vecAdd_app _ _ _ _ hseam]
  refine elim.unitTail_append ?_ ?_
  · refine poly.oneValue_unitTail (elim.polyOne_vecAdd _ _ _ _ hUp hLow ?_ ?_)
      (elim.vecAdd_swap_unitTail _)
    · rw [length_vecScale, matVec_length, hbtl, length_vecScale,
        matVec_length, hbtl]
    · rw [length_vecScale, matVec_length, hX1l, ground.length_map,
        length_vecScale, matVec_length, hbtl]
  · exact elim.unitTail_vecAdd_of
      (elim.unitTail_vecScale _ _ (elim.matVec_replicate_null n0 (m - n1) _))
      (poly.unitTail_replicate _)

/-- The lift's whole row read at a leading slab: the assembled
matrix against the telescope reads the slab's pivot above and the
sum's unit beneath. -/
private theorem lift_cons (A B : Mat) (As Bs : List Mat)
    (X0 R0 : MatQ) (Xt Rt : List MatQ) (n0 : Nat) (nt : List Nat)
    (h : tailRead (A :: As) (B :: Bs) (X0 :: Xt) (R0 :: Rt) (n0 :: nt))
    (ihAct : ∀ v : List BPair, v.length = ground.getAt 0 nt 0 →
      poly.oneValue
        (elim.vecScale (BPair.ofPos (ground.getAt dM Xt 0).2)
          (matVec (assemble As Bs)
            (matVec (liftMat (ground.getAt 0 nt 0) Rt) v)))
        (elim.vecScale (BPair.ofPos (clProd Rt))
          (matVec (ground.getAt dM Xt 0).1 v)
          ++ List.replicate
            ((assemble As Bs).length - ground.getAt 0 nt 0) BPair.unit))
    (w : List BPair) (hw : w.length = n0) :
    poly.oneValue
      (elim.vecScale (BPair.ofPos X0.2)
        (matVec (assemble (A :: As) (B :: Bs))
          (matVec (liftMat n0 (R0 :: Rt)) w)))
      (elim.vecScale (BPair.ofPos (clProd (R0 :: Rt))) (matVec X0.1 w)
        ++ List.replicate
          ((assemble (A :: As) (B :: Bs)).length - n0) BPair.unit) := by
  have hsl : slabShape (A :: As) (B :: Bs) (n0 :: nt) := h.1
  have hAs : Bs.length + 1 = As.length :=
    Nat.succ.inj (slabShape_len_off hsl)
  have hntl : nt.length = As.length := Nat.succ.inj (slabShape_len_ns hsl)
  have hntpos : 0 < nt.length := by
    rw [hntl, ← hAs]; exact Nat.succ_pos _
  have hA : sqAt A n0 := slab_sq hsl 0 (Nat.succ_pos _)
  have hAl : A.length = n0 := sqAt_len hA
  have hAr : rowsLen n0 A := rowsLen_of_sqAt hA
  have hk : 0 < n0 := slab_pos hsl 0 (Nat.succ_pos _)
  have hk1 : 0 < ground.getAt 0 nt 0 :=
    slab_pos hsl 1 (Nat.succ_lt_succ hntpos)
  have hB : rectAt B n0 (ground.getAt 0 nt 0) :=
    slab_rect hsl 0 (Nat.succ_pos _)
  have hBl : B.length = n0 := rectAt_len hB
  have hBr : rowsLen (ground.getAt 0 nt 0) B := rectAt_rows hB
  have ht : slabShape As Bs nt := slabShape_tail hsl
  have hIHsq : sqAt (assemble As Bs) (ground.sumNat nt) :=
    assemble_sq As Bs nt ht
  have hml : (assemble As Bs).length = ground.sumNat nt := sqAt_len hIHsq
  have hn1m : ground.getAt 0 nt 0 ≤ (assemble As Bs).length := by
    rw [hml]; exact ground.getAt_le_sumNat nt 0
  have hhd : ((assemble As Bs).headD []).length = (assemble As Bs).length := by
    rw [hml]; exact sqAt_headD _ _ hIHsq
  have hR0 : rectAt R0.1 (ground.getAt 0 nt 0) n0 :=
    wShapeR_at h.2.2.1 0 (Nat.succ_pos _)
  have hR0l : R0.1.length = ground.getAt 0 nt 0 := rectAt_len hR0
  have hR0r : rowsLen n0 R0.1 := rectAt_rows hR0
  have hX0 : sqAt X0.1 n0 := qShape_at h.2.1 0 (Nat.succ_pos _)
  have hXtl : Xt.length = nt.length := Nat.succ.inj (qShape_len h.2.1)
  have hX1 : sqAt (ground.getAt dM Xt 0).1 (ground.getAt 0 nt 0) :=
    qShape_at h.2.1 1 (Nat.succ_lt_succ (by rw [hXtl]; exact hntpos))
  have hstep := tail_step h 0 (Nat.succ_pos _)
  have hMr : rowsLen n0 (matMul B R0.1) :=
    rowsLen_cast (length_transposeM R0.1 hR0r (by rw [hR0l]; exact hk1))
      (rowsLen_matMul B R0.1)
  have hbtOff : transposeM (offPad (assemble As Bs).length B)
      = offT n0 (transposeM B) (assemble As Bs).length :=
    transposeM_offPad B n0 (ground.getAt 0 nt 0) _ hBl hBr hk hn1m
  have hbtl : (transposeM (offPad (assemble As Bs).length B)).length
      = (assemble As Bs).length := by rw [hbtOff, offT_len]
  have hbtr : rowsLen n0 (transposeM (offPad (assemble As Bs).length B)) := by
    rw [hbtOff]
    exact offT_rows n0 (transposeM B) _
      (rowsLen_cast hBl (rowsLen_transposeM B))
  have hRt : ∀ R Rs', Rt = R :: Rs' →
      rowsLen (ground.getAt 0 nt 0) R.1 := by
    intro R1 Rt' hEq
    have hlt : 1 < (R0 :: Rt).length := by
      rw [hEq]; exact Nat.succ_lt_succ (Nat.succ_pos _)
    have hr := wShapeR_at h.2.2.1 1 hlt
    have h2 : ground.getAt dM (R0 :: Rt) 1 = R1 := by rw [hEq]; rfl
    rw [h2] at hr
    exact rectAt_rows hr
  have hseed : (matVec (matSwap R0.1) w).length = ground.getAt 0 nt 0 :=
    (matVec_length _ w).trans ((ground.length_map _ R0.1).trans hR0l)
  have hact := liftMat_cons_act n0 R0 Rt hR0r w hw
  rw [hR0l] at hact
  have hbsplit := liftMat_act (ground.getAt 0 nt 0) Rt
    (matVec (matSwap R0.1) w) hseed hRt
  have hal : (elim.vecScale (BPair.ofPos (clProd (R0 :: Rt))) w).length
      = n0 := (length_vecScale _ _).trans hw
  have hbl : (matVec (liftMat (ground.getAt 0 nt 0) Rt)
      (matVec (matSwap R0.1) w)).length
      = (liftMat (ground.getAt 0 nt 0) Rt).length := matVec_length _ _
  -- the off-block against the stepped telescope
  have hoff : poly.oneValue
      (matVec (offPad (assemble As Bs).length B)
        (matVec (liftMat (ground.getAt 0 nt 0) Rt)
          (matVec (matSwap R0.1) w)))
      (elim.vecScale (BPair.ofPos (clProd Rt))
        ((matVec (matMul B R0.1) w).map BPair.swap)) := by
    refine poly.oneValue_trans (matVec_congr _ _ _ hbsplit) ?_
    refine poly.oneValue_trans (offPad_act _ (ground.getAt 0 nt 0) B hBr
      _ _ ((length_vecScale _ _).trans hseed)) ?_
    refine poly.oneValue_trans
      (matVec_vecScale_free B (BPair.ofPos (clProd Rt))
        (matVec (matSwap R0.1) w)) ?_
    refine elim.vecScale_oneValue _ _ _ ?_
    refine poly.oneValue_trans (matVec_comp B (matSwap R0.1) w n0
      (rowsLen_mapRows BPair.swap R0.1 n0 hR0r) hw
      (rowsLen_cast ((ground.length_map _ R0.1).trans hR0l).symm hBr)) ?_
    rw [matMul_swap, matVec_swapM]
    exact poly.oneValue_refl _
  rw [assemble_cons A B As Bs n0 (ground.getAt 0 nt 0)
    (assemble As Bs).length hAl hk hBl hBr hn1m rfl hhd,
    length_blockJoin A (offPad (assemble As Bs).length B) (assemble As Bs)
      n0 (assemble As Bs).length hAl ((offPad_len _ B).trans hBl) hbtl rfl,
    ground.addSubSelfL]
  refine poly.oneValue_trans (elim.vecScale_oneValue (BPair.ofPos X0.2) _ _
    (poly.oneValue_trans (matVec_congr _ _ _ hact)
      (matVec_blockJoin A (offPad (assemble As Bs).length B)
        (assemble As Bs) _ _
        (rowsLen_cast hal.symm hAr) (rowsLen_cast hal.symm hbtr)))) ?_
  rw [elim.vecScale_append]
  refine poly.oneValue_append _ _ _ _ ?_ ?_ ?_
  · rw [length_vecScale, length_vecScale, matVec_length,
      sqAt_len hX0,
      elim.length_vecAdd _ _ n0 ((matVec_length _ _).trans hAl)
        ((matVec_length _ _).trans ((offPad_len _ B).trans hBl))]
  · refine poly.oneValue_trans (elim.vecScale_oneValue (BPair.ofPos X0.2)
      _ _ (elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl _) hoff rfl
        (by rw [matVec_length, offPad_len, hBl, length_vecScale,
          ground.length_map, matVec_length, length_matMul, hBl]))) ?_
    exact lift_upper A B X0 R0 n0 (clProd Rt) w hw hAl (sqAt_len hX0) hBl
      (rowsLen_of_sqAt hX0) hMr hstep.2.2
  · refine poly.unitTail_oneValue ?_ (poly.unitTail_replicate _)
    refine elim.unitTail_vecScale _ _ ?_
    rw [hbtOff]
    exact lift_lower B (ground.getAt dM Xt 0) R0 (assemble As Bs) n0
      (ground.getAt 0 nt 0) (assemble As Bs).length (clProd Rt) w hw hBl
      hBr hk hR0l hR0r (sqAt_len hX1) (rowsLen_of_sqAt hX1) hn1m rfl
      hstep.2.1 _ (ihAct (matVec (matSwap R0.1) w) hseed)

/-- The telescope's row count and its whole row read, at the slab
list's own recursion. -/
private theorem lift_read : ∀ (diag off : List Mat) (Xs Rs : List MatQ)
    (ns : List Nat), tailRead diag off Xs Rs ns →
    (liftMat (ground.getAt 0 ns 0) Rs).length = (assemble diag off).length
    ∧ ∀ w : List BPair, w.length = ground.getAt 0 ns 0 →
        poly.oneValue
          (elim.vecScale (BPair.ofPos (ground.getAt dM Xs 0).2)
            (matVec (assemble diag off)
              (matVec (liftMat (ground.getAt 0 ns 0) Rs) w)))
          (elim.vecScale (BPair.ofPos (clProd Rs))
            (matVec (ground.getAt dM Xs 0).1 w)
            ++ List.replicate
              ((assemble diag off).length - ground.getAt 0 ns 0)
              BPair.unit)
  | [], _, _, _, _, h => h.1.elim
  | A :: As, [], Xs, Rs, ns, h => by
    have hAs : As = [] :=
      ground.nil_of_length_zero As
        (Nat.succ.inj (slabShape_len_off h.1)).symm
    subst hAs
    have hnl : ns.length = 1 := slabShape_len_ns h.1
    have hRs : Rs = [] :=
      ground.nil_of_length_zero Rs
        (Nat.succ.inj ((wShapeR_len h.2.2.1).trans hnl))
    subst hRs
    have hX0 : sqAt (ground.getAt dM Xs 0).1 (ground.getAt 0 ns 0) :=
      qShape_at h.2.1 0
        (by rw [qShape_len h.2.1, hnl]; exact Nat.succ_pos 0)
    have hAl : A.length = ground.getAt 0 ns 0 :=
      sqAt_len (slab_sq h.1 0 (Nat.succ_pos _))
    have hanc : oneValueQ (ground.getAt dM Xs 0) (ofM A) := by
      cases Xs with
      | nil => exact (h.2.2.2 : False).elim
      | cons X0 Xt =>
        cases Xt with
        | nil => exact h.2.2.2
        | cons _ _ => exact (h.2.2.2 : False).elim
    have hj : matOneValue (ground.getAt dM Xs 0).1
        (matScale (ground.getAt dM Xs 0).2 A) := by
      have h1 : matOneValue (matScale Pos.one (ground.getAt dM Xs 0).1)
          (matScale (ground.getAt dM Xs 0).2 A) := hanc
      rw [matScale_one] at h1
      exact h1
    refine ⟨?_, ?_⟩
    · show (matScaleB (BPair.ofPos Pos.one)
        (idMat (ground.getAt 0 ns 0))).length = A.length
      rw [length_scaleB, idMat_len, hAl]
    · intro w hw
      have hsub : A.length - ground.getAt 0 ns 0 = 0 := by
        rw [hAl, Nat.sub_self]
      show poly.oneValue
        (elim.vecScale (BPair.ofPos (ground.getAt dM Xs 0).2)
          (matVec A (matVec (liftMat (ground.getAt 0 ns 0) []) w)))
        (elim.vecScale (BPair.ofPos (clProd []))
          (matVec (ground.getAt dM Xs 0).1 w)
          ++ List.replicate (A.length - ground.getAt 0 ns 0) BPair.unit)
      rw [hsub]
      show poly.oneValue
        (elim.vecScale (BPair.ofPos (ground.getAt dM Xs 0).2)
          (matVec A (matVec (liftMat (ground.getAt 0 ns 0) []) w)))
        (elim.vecScale (BPair.ofPos (clProd []))
          (matVec (ground.getAt dM Xs 0).1 w) ++ [])
      rw [ground.append_nil]
      refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
        (matVec_congr A _ _ (liftMat_nil_act _ w hw))) ?_
      refine poly.oneValue_symm (poly.oneValue_trans
        (elim.vecScale_one _) ?_)
      exact poly.oneValue_trans (matVec_matOne _ _ w hj)
        (matVec_matScale (ground.getAt dM Xs 0).2 A w)
  | A :: As, B :: Bs, Xs, Rs, ns, h => by
    have hAs : Bs.length + 1 = As.length :=
      Nat.succ.inj (slabShape_len_off h.1)
    have hnl : ns.length = As.length + 1 := slabShape_len_ns h.1
    have hnpos : 0 < ns.length := by rw [hnl]; exact Nat.succ_pos _
    have hXl : Xs.length = ns.length := qShape_len h.2.1
    have hRl : Rs.length + 1 = ns.length := wShapeR_len h.2.2.1
    match ns, hnl, hXl, hRl with
    | [], hb, _, _ => exact Nat.noConfusion hb
    | n0 :: nt, hnl1, hXl1, hRl1 =>
      match Xs, hXl1 with
      | [], hb => exact Nat.noConfusion hb
      | X0 :: Xt, _ =>
        match Rs, hRl1 with
        | [], hb =>
          exact absurd (Nat.succ.inj (hb.trans hnl1)).symm
            (by rw [← hAs]; exact fun hh => Nat.noConfusion hh)
        | R0 :: Rt, _ =>
          have hIH := lift_read As Bs Xt Rt nt (tailRead_tail h)
          refine ⟨?_, fun w hw => lift_cons A B As Bs X0 R0 Xt Rt n0 nt h
            hIH.2 w hw⟩
          have ht : slabShape As Bs nt := slabShape_tail h.1
          have hA : sqAt A n0 := slab_sq h.1 0 (Nat.succ_pos _)
          have hAl : A.length = n0 := sqAt_len hA
          have hk : 0 < n0 := slab_pos h.1 0 (Nat.succ_pos _)
          have hB : rectAt B n0 (ground.getAt 0 nt 0) :=
            slab_rect h.1 0 (Nat.succ_pos _)
          have hIHsq : sqAt (assemble As Bs) (ground.sumNat nt) :=
            assemble_sq As Bs nt ht
          have hml : (assemble As Bs).length = ground.sumNat nt :=
            sqAt_len hIHsq
          have hn1m : ground.getAt 0 nt 0 ≤ (assemble As Bs).length := by
            rw [hml]; exact ground.getAt_le_sumNat nt 0
          have hhd : ((assemble As Bs).headD []).length
              = (assemble As Bs).length := by
            rw [hml]; exact sqAt_headD _ _ hIHsq
          have hR0 : rectAt R0.1 (ground.getAt 0 nt 0) n0 :=
            wShapeR_at h.2.2.1 0 (Nat.succ_pos _)
          have hbtl : (transposeM (offPad (assemble As Bs).length B)).length
              = (assemble As Bs).length := by
            rw [transposeM_offPad B n0 (ground.getAt 0 nt 0) _
              (rectAt_len hB) (rectAt_rows hB) hk hn1m, offT_len]
          rw [assemble_cons A B As Bs n0 (ground.getAt 0 nt 0)
            (assemble As Bs).length hAl hk (rectAt_len hB) (rectAt_rows hB)
            hn1m rfl hhd,
            length_blockJoin A (offPad (assemble As Bs).length B)
              (assemble As Bs) n0 (assemble As Bs).length hAl
              ((offPad_len _ B).trans (rectAt_len hB)) hbtl rfl]
          show ((matScaleB (BPair.ofPos (clProd (R0 :: Rt))) (idMat n0))
            ++ matMul (liftMat R0.1.length Rt) (matSwap R0.1)).length
            = n0 + (assemble As Bs).length
          rw [ground.length_append, length_scaleB, idMat_len,
            length_matMul, rectAt_len hR0, hIH.1]

/-! Clause (ii)'s pricing tier: the pairing's symmetry as a read at
vectors, the two slab families over the slab list, and the reads
`lem:inertia`'s forcing clauses consume. -/

/-- The pairing's symmetry at a stated order, read at vectors. -/
private def symP (S : Mat) (n : Nat) : Prop :=
  ∀ a b : List BPair, a.length = n → b.length = n →
    (dotN a (matVec S b)).oneValue (dotN b (matVec S a))

private theorem symP_of_sym (S : Mat) (n : Nat) (hSl : S.length = n)
    (hSr : rowsLen n S) (hsym : matOneValue S (transposeM S)) :
    symP S n := fun a b ha hb =>
  BPair.oneValue_trans
    (dotN_congrR a _ _ (matVec_matOne S (transposeM S) b hsym))
    (adjB S n n hSl hSr a ha b hb)

/-- The join's pairing at unit-padded arguments is the trailing
block's own. -/
private theorem padPair (A Bp Q : Mat) (n0 m : Nat)
    (hAr : rowsLen n0 A) (hAl : A.length = n0) (hBpl : Bp.length = n0)
    (hBtl : (transposeM Bp).length = m)
    (hBtr : rowsLen n0 (transposeM Bp)) (hQl : Q.length = m)
    (x y : List BPair) (hx : x.length = m) :
    (dotN (List.replicate n0 BPair.unit ++ x)
      (matVec (blockJoin A Bp Q)
        (List.replicate n0 BPair.unit ++ y))).oneValue
      (dotN x (matVec Q y)) := by
  have hu : (List.replicate n0 BPair.unit).length = n0 :=
    ground.length_replicate BPair.unit n0
  have hut : poly.unitTail (List.replicate n0 BPair.unit) :=
    poly.unitTail_replicate n0
  refine BPair.oneValue_trans (quadJoin A Bp Q n0 m hAr hAl hBpl hBtl
    hBtr hQl _ x _ y hu hx hu) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (dotN_nullL _ _ hut) (dotN_nullL _ _ hut))
      (BPair.add_congr
        (dotN_nullR x _ (matVec_null (transposeM Bp) _ hut))
        (BPair.oneValue_refl _))) ?_
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.add_unit BPair.unit)
      (BPair.unit_add (dotN x (matVec Q y))))
    (BPair.unit_add _)

private theorem symP_tail (A Bp Q : Mat) (n0 m : Nat)
    (hAr : rowsLen n0 A) (hAl : A.length = n0) (hBpl : Bp.length = n0)
    (hBtl : (transposeM Bp).length = m)
    (hBtr : rowsLen n0 (transposeM Bp)) (hQl : Q.length = m)
    (h : symP (blockJoin A Bp Q) (n0 + m)) : symP Q m := by
  intro a b ha hb
  have hu : (List.replicate n0 BPair.unit).length = n0 :=
    ground.length_replicate BPair.unit n0
  have hlen : ∀ x : List BPair, x.length = m →
      (List.replicate n0 BPair.unit ++ x).length = n0 + m := by
    intro x hx
    rw [ground.length_append, hu, hx]
  exact BPair.oneValue_trans
    (BPair.oneValue_symm
      (padPair A Bp Q n0 m hAr hAl hBpl hBtl hBtr hQl a b ha))
    (BPair.oneValue_trans (h _ _ (hlen a ha) (hlen b hb))
      (padPair A Bp Q n0 m hAr hAl hBpl hBtl hBtr hQl b a hb))

private theorem revFoldGo : ∀ (sps : List ((k : Nat) × Split k)) (a : Nat),
    sps.foldl (fun m s => m + revAt s.2) a
      = a + sps.foldl (fun m s => m + revAt s.2) 0
  | [], a => (Nat.add_zero a).symm
  | s :: t, a => by
    show t.foldl (fun m s => m + revAt s.2) (a + revAt s.2)
      = a + t.foldl (fun m s => m + revAt s.2) (0 + revAt s.2)
    rw [Nat.zero_add, revFoldGo t (a + revAt s.2), revFoldGo t (revAt s.2),
      Nat.add_assoc]

private theorem revFold_cons (s : (k : Nat) × Split k)
    (sps : List ((k : Nat) × Split k)) :
    revFold (s :: sps) = revAt s.2 + revFold sps := by
  show sps.foldl (fun m t => m + revAt t.2) (0 + revAt s.2)
    = revAt s.2 + revFold sps
  rw [Nat.zero_add]
  exact revFoldGo sps (revAt s.2)

/-- The slab families' recursion: the slab's own certificate list
carried by the telescope, joined to the trailing family padded
beneath. -/
private def famAt (f : (k : Nat) → Split k → Mat) :
    List Mat → List Mat → List MatQ → List ((k : Nat) × Split k) → Mat
  | [], _, _, _ => []
  | _ :: _, _, _, [] => []
  | A :: As, off, Rs, s :: sps =>
    (f s.1 s.2).map (matVec (liftMat A.length Rs))
    ++ (famAt f As off.tail Rs.tail sps).map
        (matVec (padR A.length (assemble As off.tail).length))

private def lowFam : List Mat → List Mat → List MatQ →
    List ((k : Nat) × Split k) → Mat :=
  famAt (fun _ sp => lowerList sp)

private def complFam : List Mat → List Mat → List MatQ →
    List ((k : Nat) × Split k) → Mat :=
  famAt (fun _ sp => complList sp)

/-- The lifted vector's form is the slab pivot's own at the two
clearings' square. -/
private theorem lift_quad (S : Mat) (X0 : MatQ) (c : Pos) (n0 m : Nat)
    (u tl x : List BPair) (hX0l : (matVec X0.1 x).length = n0)
    (hcx : (elim.vecScale (BPair.ofPos c) x).length = n0)
    (hu : poly.oneValue u (elim.vecScale (BPair.ofPos c) x ++ tl))
    (himg : poly.oneValue (elim.vecScale (BPair.ofPos X0.2) (matVec S u))
      (elim.vecScale (BPair.ofPos c) (matVec X0.1 x)
        ++ List.replicate m BPair.unit)) :
    (BPair.ofPos X0.2 * quadForm S u).oneValue
      (BPair.ofPos c * (BPair.ofPos c * quadForm X0.1 x)) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (elim.dotN_scaleV _ u (matVec S u))) ?_
  refine BPair.oneValue_trans (dotN_congrR u _ _ himg) ?_
  refine BPair.oneValue_trans (dotN_congrL u _ _ hu) ?_
  refine BPair.oneValue_trans (dotN_app _ tl _ _
    (hcx.trans ((length_vecScale _ _).trans hX0l).symm)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (dotN_nullR tl _ (poly.unitTail_replicate m))) ?_
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  exact BPair.oneValue_trans (elim.dotN_scaleRow_free _ x _)
    (BPair.mul_congr (BPair.oneValue_refl _)
      (elim.dotN_scaleV _ x (matVec X0.1 x)))

/-- The padded vector against the lifted one reads the sum's unit:
the lift's rows beyond the slab are the unit family. -/
private theorem cross_pad_lift (S : Mat) (X0 : MatQ) (c : Pos)
    (n0 m : Nat) (u v x y : List BPair)
    (hn0 : (elim.vecScale (BPair.ofPos c) (matVec X0.1 x)).length = n0)
    (hv : poly.oneValue v (List.replicate n0 BPair.unit ++ y))
    (himg : poly.oneValue (elim.vecScale (BPair.ofPos X0.2) (matVec S u))
      (elim.vecScale (BPair.ofPos c) (matVec X0.1 x)
        ++ List.replicate m BPair.unit)) :
    (dotN v (matVec S u)).oneValue BPair.unit := by
  refine ground.mul_cancel_unit (BPair.ofPos_off X0.2) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (elim.dotN_scaleV _ v (matVec S u))) ?_
  refine BPair.oneValue_trans (dotN_congrR v _ _ himg) ?_
  refine BPair.oneValue_trans (dotN_congrL v _ _ hv) ?_
  refine BPair.oneValue_trans (dotN_app _ y _ _ ?_) ?_
  · rw [ground.length_replicate, hn0]
  · exact BPair.oneValue_trans
      (BPair.add_congr (dotN_nullL _ _ (poly.unitTail_replicate n0))
        (dotN_nullR y _ (poly.unitTail_replicate m)))
      (BPair.add_unit BPair.unit)

/-- The joined family's combination: the two halves' own
combinations, each carried by its carrier's action. -/
private theorem fam_combo (LIFT PAD : Mat) (n0 m : Nat) (L1 LT : Mat)
    (hL1 : rowsLen n0 L1) (hLT : rowsLen m LT)
    (hLIFT : LIFT.length = n0 + m) (hPAD : PAD.length = n0 + m)
    (cx cw : List BPair)
    (hcx : cx.length = (L1.map (matVec LIFT)).length) :
    poly.oneValue
      (combo (n0 + m) (cx ++ cw)
        (L1.map (matVec LIFT) ++ LT.map (matVec PAD)))
      (vecAdd (matVec LIFT (combo n0 cx L1))
        (matVec PAD (combo m cw LT))) := by
  have h1 : rowsLen (n0 + m) (L1.map (matVec LIFT)) :=
    rowsLen_map (matVec LIFT) (n0 + m) L1
      (fun x _ => (matVec_length LIFT x).trans hLIFT)
  have h2 : rowsLen (n0 + m) (LT.map (matVec PAD)) :=
    rowsLen_map (matVec PAD) (n0 + m) LT
      (fun x _ => (matVec_length PAD x).trans hPAD)
  have hc1 : poly.oneValue (combo (n0 + m) cx (L1.map (matVec LIFT)))
      (matVec LIFT (combo n0 cx L1)) := by
    have hh := matVec_combo LIFT n0 cx L1 hL1
    rw [hLIFT] at hh
    exact poly.oneValue_symm hh
  have hc2 : poly.oneValue (combo (n0 + m) cw (LT.map (matVec PAD)))
      (matVec PAD (combo m cw LT)) := by
    have hh := matVec_combo PAD m cw LT hLT
    rw [hPAD] at hh
    exact poly.oneValue_symm hh
  refine poly.oneValue_trans (combo_append (n0 + m) cx _ cw _ hcx h1 h2) ?_
  exact elim.polyOne_vecAdd _ _ _ _ hc1 hc2
    ((length_combo (n0 + m) cx _ h1).trans
      ((matVec_length _ _).trans hLIFT).symm)
    ((length_combo (n0 + m) cw _ h2).trans
      ((matVec_length _ _).trans hPAD).symm)

/-- The slab families' seven reads: the two counts, the two row
shapes, the lower family's strict pricing, and the complement
family's independence with its side. -/
private def famRead (diag off : List Mat) (Rs : List MatQ)
    (sps : List ((k : Nat) × Split k)) : Prop :=
  (lowFam diag off Rs sps).length = revFold sps
  ∧ rowsLen (assemble diag off).length (lowFam diag off Rs sps)
  ∧ (∀ cs : List BPair, cs.length = (lowFam diag off Rs sps).length →
      ¬ poly.unitTail cs →
      quadForm (assemble diag off)
        (combo (assemble diag off).length cs (lowFam diag off Rs sps))
        < BPair.unit)
  ∧ (complFam diag off Rs sps).length + revFold sps
      = (assemble diag off).length
  ∧ rowsLen (assemble diag off).length (complFam diag off Rs sps)
  ∧ (∀ cs : List BPair, cs.length = (complFam diag off Rs sps).length →
      poly.unitTail (combo (assemble diag off).length cs
        (complFam diag off Rs sps)) → poly.unitTail cs)
  ∧ (∀ cs : List BPair, cs.length = (complFam diag off Rs sps).length →
      ¬ (quadForm (assemble diag off)
        (combo (assemble diag off).length cs
          (complFam diag off Rs sps)) < BPair.unit))

/-- The families' reads at a leading slab: the slab's certificate
list carried by the telescope prices the slab pivot's own form, the
trailing family padded beneath prices the trailing assembly's, and
the two crossings read the sum's unit. -/
private theorem fam_cons (A B : Mat) (As Bs : List Mat)
    (X0 R0 : MatQ) (Xt Rt : List MatQ) (n0 : Nat) (nt : List Nat)
    (s : (k : Nat) × Split k) (spt : List ((k : Nat) × Split k))
    (h : tailRead (A :: As) (B :: Bs) (X0 :: Xt) (R0 :: Rt) (n0 :: nt))
    (hsp : splitRead X0.1 s.2)
    (hsym : symP (assemble (A :: As) (B :: Bs))
      (assemble (A :: As) (B :: Bs)).length)
    (ih : famRead As Bs Rt spt) :
    famRead (A :: As) (B :: Bs) (R0 :: Rt) (s :: spt) := by
  have hsl : slabShape (A :: As) (B :: Bs) (n0 :: nt) := h.1
  have hA : sqAt A n0 := slab_sq hsl 0 (Nat.succ_pos _)
  have hAl : A.length = n0 := sqAt_len hA
  have hAr : rowsLen n0 A := rowsLen_of_sqAt hA
  have hk : 0 < n0 := slab_pos hsl 0 (Nat.succ_pos _)
  have hAs : Bs.length + 1 = As.length :=
    Nat.succ.inj (slabShape_len_off hsl)
  have hntl : nt.length = As.length := Nat.succ.inj (slabShape_len_ns hsl)
  have hntpos : 0 < nt.length := by
    rw [hntl, ← hAs]; exact Nat.succ_pos _
  have hB : rectAt B n0 (ground.getAt 0 nt 0) :=
    slab_rect hsl 0 (Nat.succ_pos _)
  have ht : slabShape As Bs nt := slabShape_tail hsl
  have hIHsq : sqAt (assemble As Bs) (ground.sumNat nt) :=
    assemble_sq As Bs nt ht
  have hml : (assemble As Bs).length = ground.sumNat nt := sqAt_len hIHsq
  have hn1m : ground.getAt 0 nt 0 ≤ (assemble As Bs).length := by
    rw [hml]; exact ground.getAt_le_sumNat nt 0
  have hhd : ((assemble As Bs).headD []).length
      = (assemble As Bs).length := by
    rw [hml]; exact sqAt_headD _ _ hIHsq
  have hbtOff : transposeM (offPad (assemble As Bs).length B)
      = offT n0 (transposeM B) (assemble As Bs).length :=
    transposeM_offPad B n0 (ground.getAt 0 nt 0) _ (rectAt_len hB)
      (rectAt_rows hB) hk hn1m
  have hbtl : (transposeM (offPad (assemble As Bs).length B)).length
      = (assemble As Bs).length := by rw [hbtOff, offT_len]
  have hbtr : rowsLen n0 (transposeM (offPad (assemble As Bs).length B)) := by
    rw [hbtOff]
    exact offT_rows n0 (transposeM B) _
      (rowsLen_cast (rectAt_len hB) (rowsLen_transposeM B))
  have hAC : assemble (A :: As) (B :: Bs)
      = blockJoin A (offPad (assemble As Bs).length B) (assemble As Bs) :=
    assemble_cons A B As Bs n0 (ground.getAt 0 nt 0)
      (assemble As Bs).length hAl hk (rectAt_len hB) (rectAt_rows hB)
      hn1m rfl hhd
  have hSl : (assemble (A :: As) (B :: Bs)).length
      = n0 + (assemble As Bs).length := by
    rw [hAC]
    exact length_blockJoin A _ (assemble As Bs) n0 _ hAl
      ((offPad_len _ B).trans (rectAt_len hB)) hbtl rfl
  have hSr : rowsLen (n0 + (assemble As Bs).length)
      (assemble (A :: As) (B :: Bs)) := by
    rw [hAC]
    exact rowsLen_blockJoin A _ (assemble As Bs) n0 _ hAr
      (offPad_rows _ _ B (rectAt_rows hB) hn1m) hbtr
      (rowsLen_cast hml.symm (rowsLen_of_sqAt hIHsq))
  have hlift := lift_read (A :: As) (B :: Bs) (X0 :: Xt) (R0 :: Rt)
    (n0 :: nt) h
  have hLIFTl : (liftMat n0 (R0 :: Rt)).length
      = n0 + (assemble As Bs).length := hlift.1.trans hSl
  have hPADl : (padR n0 (assemble As Bs).length).length
      = n0 + (assemble As Bs).length := padR_len n0 _
  have hX0 : sqAt X0.1 n0 := qShape_at h.2.1 0 (Nat.succ_pos _)
  have hs1 : s.1 = n0 := (sqAt_len hsp.1).symm.trans (sqAt_len hX0)
  have hR0 : rectAt R0.1 (ground.getAt 0 nt 0) n0 :=
    wShapeR_at h.2.2.1 0 (Nat.succ_pos _)
  -- the lift's image at a stated seed, the trailing width read off
  have himg : ∀ x : List BPair, x.length = n0 →
      poly.oneValue (elim.vecScale (BPair.ofPos X0.2)
        (matVec (assemble (A :: As) (B :: Bs))
          (matVec (liftMat n0 (R0 :: Rt)) x)))
        (elim.vecScale (BPair.ofPos (clProd (R0 :: Rt)))
          (matVec X0.1 x)
          ++ List.replicate (assemble As Bs).length BPair.unit) := by
    intro x hx
    have hh : poly.oneValue (elim.vecScale (BPair.ofPos X0.2)
        (matVec (assemble (A :: As) (B :: Bs))
          (matVec (liftMat n0 (R0 :: Rt)) x)))
        (elim.vecScale (BPair.ofPos (clProd (R0 :: Rt))) (matVec X0.1 x)
          ++ List.replicate
            ((assemble (A :: As) (B :: Bs)).length - n0) BPair.unit) :=
      hlift.2 x hx
    rw [hSl, ground.addSubSelfL] at hh
    exact hh
  have hcxl : ∀ x : List BPair, x.length = n0 →
      (elim.vecScale (BPair.ofPos (clProd (R0 :: Rt)))
        (matVec X0.1 x)).length = n0 :=
    fun x _ => (length_vecScale _ _).trans
      ((matVec_length _ _).trans (sqAt_len hX0))
  -- the joined family's quadratic form splits over the two halves
  have hsplitQ : ∀ (L1 LT : Mat), rowsLen n0 L1 →
      rowsLen (assemble As Bs).length LT →
      ∀ (cx cw : List BPair),
      cx.length = (L1.map (matVec (liftMat n0 (R0 :: Rt)))).length →
      (quadForm (assemble (A :: As) (B :: Bs))
        (combo (assemble (A :: As) (B :: Bs)).length (cx ++ cw)
          (L1.map (matVec (liftMat n0 (R0 :: Rt)))
            ++ LT.map
              (matVec (padR n0 (assemble As Bs).length))))).oneValue
        (quadForm (assemble (A :: As) (B :: Bs))
            (matVec (liftMat n0 (R0 :: Rt)) (combo n0 cx L1))
          + quadForm (assemble As Bs)
            (combo (assemble As Bs).length cw LT)) := by
    intro L1 LT hL1 hLT cx cw hcx
    have hx : (combo n0 cx L1).length = n0 := length_combo n0 cx L1 hL1
    have hy : (combo (assemble As Bs).length cw LT).length
        = (assemble As Bs).length :=
      length_combo _ cw LT hLT
    have hu : (matVec (liftMat n0 (R0 :: Rt)) (combo n0 cx L1)).length
        = n0 + (assemble As Bs).length :=
      (matVec_length _ _).trans hLIFTl
    have hv : (matVec (padR n0 (assemble As Bs).length)
        (combo (assemble As Bs).length cw LT)).length
        = n0 + (assemble As Bs).length :=
      (matVec_length _ _).trans hPADl
    have hvact := padR_act n0 (assemble As Bs).length _ hy
    have hcross : (dotN (matVec (padR n0 (assemble As Bs).length)
        (combo (assemble As Bs).length cw LT))
        (matVec (assemble (A :: As) (B :: Bs))
          (matVec (liftMat n0 (R0 :: Rt))
            (combo n0 cx L1)))).oneValue BPair.unit :=
      cross_pad_lift (assemble (A :: As) (B :: Bs)) X0
        (clProd (R0 :: Rt)) n0 (assemble As Bs).length _ _
        (combo n0 cx L1) _ (hcxl _ hx) hvact (himg _ hx)
    rw [hSl]
    refine BPair.oneValue_trans (quad_congr _ _ _
      (fam_combo (liftMat n0 (R0 :: Rt))
        (padR n0 (assemble As Bs).length) n0 (assemble As Bs).length
        L1 LT hL1 hLT hLIFTl hPADl cx cw hcx)) ?_
    refine BPair.oneValue_trans
      (quadAdd (assemble (A :: As) (B :: Bs))
        (n0 + (assemble As Bs).length) hSr (hSl.symm ▸ rfl) _ _ hu hv) ?_
    have hpq : (dotN (matVec (padR n0 (assemble As Bs).length)
        (combo (assemble As Bs).length cw LT))
        (matVec (assemble (A :: As) (B :: Bs))
          (matVec (padR n0 (assemble As Bs).length)
            (combo (assemble As Bs).length cw LT)))).oneValue
        (quadForm (assemble As Bs)
          (combo (assemble As Bs).length cw LT)) := by
      refine BPair.oneValue_trans (quad_congr _ _ _ hvact) ?_
      rw [hAC]
      exact padPair A (offPad (assemble As Bs).length B) (assemble As Bs)
        n0 (assemble As Bs).length hAr hAl
        ((offPad_len _ B).trans (rectAt_len hB)) hbtl hbtr rfl _ _ hy
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (hsym _ _ (hu.trans hSl.symm) (hv.trans hSl.symm)) hcross))
        (BPair.add_congr hcross hpq)) ?_
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.add_unit _) (BPair.unit_add _))
      (BPair.oneValue_refl _)
  have hliftQ : ∀ x : List BPair, x.length = n0 →
      (BPair.ofPos X0.2 * quadForm (assemble (A :: As) (B :: Bs))
        (matVec (liftMat n0 (R0 :: Rt)) x)).oneValue
        (BPair.ofPos (clProd (R0 :: Rt))
          * (BPair.ofPos (clProd (R0 :: Rt)) * quadForm X0.1 x)) :=
    fun x hx =>
      lift_quad (assemble (A :: As) (B :: Bs)) X0 (clProd (R0 :: Rt)) n0
        (assemble As Bs).length _ _ x
        ((matVec_length _ _).trans (sqAt_len hX0))
        ((length_vecScale _ _).trans hx)
        (liftMat_cons_act n0 R0 Rt (rectAt_rows hR0) x hx) (himg x hx)
  have hliftLt : ∀ x : List BPair, x.length = n0 →
      quadForm X0.1 x < BPair.unit →
      quadForm (assemble (A :: As) (B :: Bs))
        (matVec (liftMat n0 (R0 :: Rt)) x) < BPair.unit := by
    intro x hx hlt
    exact ltUnitOfMul (BPair.lt_congr (BPair.oneValue_symm (hliftQ x hx))
      (BPair.oneValue_refl BPair.unit)
      (mulLtUnit _ (mulLtUnit _ hlt)))
  have hliftLe : ∀ x : List BPair, x.length = n0 →
      BPair.unit ≤ quadForm X0.1 x →
      BPair.unit ≤ quadForm (assemble (A :: As) (B :: Bs))
        (matVec (liftMat n0 (R0 :: Rt)) x) := by
    intro x hx hle
    exact unitLeOfMul (ground.leB_congr_right
      (BPair.oneValue_symm (hliftQ x hx))
      (unitLeMulPos _ (unitLeMulPos _ hle)))
  have hlowU : lowFam (A :: As) (B :: Bs) (R0 :: Rt) (s :: spt)
      = (lowerList s.2).map (matVec (liftMat n0 (R0 :: Rt)))
        ++ (lowFam As Bs Rt spt).map
            (matVec (padR n0 (assemble As Bs).length)) := by
    show (lowerList s.2).map (matVec (liftMat A.length (R0 :: Rt)))
        ++ (lowFam As Bs Rt spt).map
            (matVec (padR A.length (assemble As Bs).length))
      = (lowerList s.2).map (matVec (liftMat n0 (R0 :: Rt)))
        ++ (lowFam As Bs Rt spt).map
            (matVec (padR n0 (assemble As Bs).length))
    rw [hAl]
  have hcomU : complFam (A :: As) (B :: Bs) (R0 :: Rt) (s :: spt)
      = (complList s.2).map (matVec (liftMat n0 (R0 :: Rt)))
        ++ (complFam As Bs Rt spt).map
            (matVec (padR n0 (assemble As Bs).length)) := by
    show (complList s.2).map (matVec (liftMat A.length (R0 :: Rt)))
        ++ (complFam As Bs Rt spt).map
            (matVec (padR A.length (assemble As Bs).length))
      = (complList s.2).map (matVec (liftMat n0 (R0 :: Rt)))
        ++ (complFam As Bs Rt spt).map
            (matVec (padR n0 (assemble As Bs).length))
    rw [hAl]
  have hLIFTsplit : (liftMat n0 (R0 :: Rt)).length
      = n0 + (liftMat R0.1.length Rt).length := by
    show ((matScaleB (BPair.ofPos (clProd (R0 :: Rt))) (idMat n0))
      ++ matMul (liftMat R0.1.length Rt) (matSwap R0.1)).length
      = n0 + (liftMat R0.1.length Rt).length
    rw [ground.length_append, length_scaleB, idMat_len, length_matMul]
  have hLrows : rowsLen n0 (lowerList s.2) :=
    rowsLen_cast hs1 (lowerList_rowsLen s.2)
  have hCrows : rowsLen n0 (complList s.2) :=
    rowsLen_cast hs1 (complList_rowsLen s.2)
  have hcombL : ∀ cx : List BPair,
      combo s.1 cx (lowerList s.2) = combo n0 cx (lowerList s.2) :=
    fun cx => congrArg (fun k => combo k cx (lowerList s.2)) hs1
  have hcombC : ∀ cx : List BPair,
      combo s.1 cx (complList s.2) = combo n0 cx (complList s.2) :=
    fun cx => congrArg (fun k => combo k cx (complList s.2)) hs1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlowU, ground.length_append, ground.length_map, ground.length_map,
      lowerList_length X0.1 s.2 hsp, ih.1, revFold_cons]
  · rw [hlowU, hSl]
    exact rowsLen_append _
      (rowsLen_map _ _ _ (fun x _ => (matVec_length _ x).trans hLIFTl))
      (rowsLen_map _ _ _ (fun x _ => (matVec_length _ x).trans hPADl))
  · intro cs hcs hoff
    rw [hlowU] at hcs
    have hlen : cs.length = ((lowerList s.2).map
        (matVec (liftMat n0 (R0 :: Rt)))).length
        + ((lowFam As Bs Rt spt).map
          (matVec (padR n0 (assemble As Bs).length))).length := by
      rw [hcs, ground.length_append]
    obtain ⟨cx, cw, rfl, hlx⟩ := ground.listSplit cs
      ((lowerList s.2).map (matVec (liftMat n0 (R0 :: Rt)))).length
      (by rw [hlen]; exact Nat.le_add_right _ _)
    have h1 : cx.length + cw.length
        = ((lowerList s.2).map (matVec (liftMat n0 (R0 :: Rt)))).length
          + ((lowFam As Bs Rt spt).map
            (matVec (padR n0 (assemble As Bs).length))).length := by
      rw [← ground.length_append cx cw]; exact hlen
    rw [hlx] at h1
    have hlw : cw.length = ((lowFam As Bs Rt spt).map
        (matVec (padR n0 (assemble As Bs).length))).length :=
      ground.addCancelL _ h1
    have hcxL : cx.length = (lowerList s.2).length :=
      hlx.trans (ground.length_map _ _)
    have hcwL : cw.length = (lowFam As Bs Rt spt).length :=
      hlw.trans (ground.length_map _ _)
    have hxlen : (combo n0 cx (lowerList s.2)).length = n0 :=
      length_combo n0 cx _ hLrows
    rw [hlowU]
    refine BPair.lt_congr
      (BPair.oneValue_symm (hsplitQ (lowerList s.2) (lowFam As Bs Rt spt)
        hLrows ih.2.1 cx cw hlx))
      (BPair.oneValue_refl BPair.unit) ?_
    cases (inferInstance : Decidable (poly.unitTail cx)) with
    | isTrue hux =>
      refine leAddLtUnit ?_ (ih.2.2.1 cw hcwL
        (fun hh => hoff (elim.unitTail_append hux hh)))
      exact ground.leB_congr_left
        (BPair.oneValue_symm (quadNull _ _
          (matVec_null _ _ (unitTail_combo_of n0 cx (lowerList s.2) hux))))
        (ground.leB_refl BPair.unit)
    | isFalse hux =>
      refine ltUnitAddLe ?_ ?_
      · refine hliftLt _ hxlen ?_
        have hstrict := lowerList_strict X0.1 s.2 hsp cx
          (hcxL.trans (lowerList_length X0.1 s.2 hsp)) hux
        rw [hcombL cx] at hstrict
        exact hstrict
      · cases (inferInstance : Decidable (poly.unitTail cw)) with
        | isTrue huw =>
          exact ground.leB_congr_left
            (BPair.oneValue_symm (quadNull _ _
              (unitTail_combo_of _ cw (lowFam As Bs Rt spt) huw)))
            (ground.leB_refl BPair.unit)
        | isFalse huw => exact ground.leB_of_lt (ih.2.2.1 cw hcwL huw)
  · rw [hcomU, ground.length_append, ground.length_map, ground.length_map,
      revFold_cons, hSl, Nat.add_add_add_comm,
      Nat.add_comm (complList s.2).length (revAt s.2),
      complList_length X0.1 s.2 hsp, hs1, ih.2.2.2.1]
  · rw [hcomU, hSl]
    exact rowsLen_append _
      (rowsLen_map _ _ _ (fun x _ => (matVec_length _ x).trans hLIFTl))
      (rowsLen_map _ _ _ (fun x _ => (matVec_length _ x).trans hPADl))
  · intro cs hcs hu
    rw [hcomU] at hcs hu
    have hlen : cs.length = ((complList s.2).map
        (matVec (liftMat n0 (R0 :: Rt)))).length
        + ((complFam As Bs Rt spt).map
          (matVec (padR n0 (assemble As Bs).length))).length := by
      rw [hcs, ground.length_append]
    obtain ⟨cx, cw, rfl, hlx⟩ := ground.listSplit cs
      ((complList s.2).map (matVec (liftMat n0 (R0 :: Rt)))).length
      (by rw [hlen]; exact Nat.le_add_right _ _)
    have h1 : cx.length + cw.length
        = ((complList s.2).map (matVec (liftMat n0 (R0 :: Rt)))).length
          + ((complFam As Bs Rt spt).map
            (matVec (padR n0 (assemble As Bs).length))).length := by
      rw [← ground.length_append cx cw]; exact hlen
    rw [hlx] at h1
    have hlw : cw.length = ((complFam As Bs Rt spt).map
        (matVec (padR n0 (assemble As Bs).length))).length :=
      ground.addCancelL _ h1
    have hcxL : cx.length = (complList s.2).length :=
      hlx.trans (ground.length_map _ _)
    have hcwL : cw.length = (complFam As Bs Rt spt).length :=
      hlw.trans (ground.length_map _ _)
    have hxlen : (combo n0 cx (complList s.2)).length = n0 :=
      length_combo n0 cx _ hCrows
    have hylen : (combo (assemble As Bs).length cw
        (complFam As Bs Rt spt)).length = (assemble As Bs).length :=
      length_combo _ cw _ ih.2.2.2.2.1
    rw [hSl] at hu
    have hu2 : poly.unitTail
        (vecAdd (matVec (liftMat n0 (R0 :: Rt))
            (combo n0 cx (complList s.2)))
          (matVec (padR n0 (assemble As Bs).length)
            (combo (assemble As Bs).length cw
              (complFam As Bs Rt spt)))) :=
      poly.unitTail_oneValue_right hu
        (fam_combo (liftMat n0 (R0 :: Rt))
          (padR n0 (assemble As Bs).length) n0 (assemble As Bs).length
          (complList s.2) (complFam As Bs Rt spt) hCrows
          ih.2.2.2.2.1 hLIFTl hPADl cx cw hlx)
    have hact := liftMat_cons_act n0 R0 Rt (rectAt_rows hR0) _ hxlen
    have hpact := padR_act n0 (assemble As Bs).length _ hylen
    have hu3 : poly.unitTail
        (vecAdd (elim.vecScale (BPair.ofPos (clProd (R0 :: Rt)))
            (combo n0 cx (complList s.2))
            ++ matVec (liftMat R0.1.length Rt)
              (matVec (matSwap R0.1) (combo n0 cx (complList s.2))))
          (List.replicate n0 BPair.unit
            ++ combo (assemble As Bs).length cw
              (complFam As Bs Rt spt))) :=
      poly.unitTail_oneValue_right hu2 (elim.polyOne_vecAdd _ _ _ _ hact hpact
        (by rw [matVec_length, ground.length_append, length_vecScale,
          hxlen, matVec_length, hLIFTsplit])
        (by rw [matVec_length, padR_len, ground.length_append,
          ground.length_replicate, hylen]))
    rw [vecAdd_app _ _ _ _
      (((length_vecScale _ _).trans hxlen).trans
        (ground.length_replicate BPair.unit n0).symm)] at hu3
    have hxu : poly.unitTail (combo n0 cx (complList s.2)) :=
      elim.unitTail_unscale _ (BPair.ofPos_off _) _
        (unitTailAddRight _ _
          (((length_vecScale _ _).trans hxlen).trans
            (ground.length_replicate BPair.unit n0).symm)
          (poly.unitTail_replicate n0) (elim.unitTail_append_split _ _ hu3).1)
    have hcx : poly.unitTail cx := by
      refine complList_indep X0.1 s.2 hsp cx hcxL ?_
      rw [hcombC cx]
      exact hxu
    have hUL : poly.unitTail (matVec (liftMat n0 (R0 :: Rt))
        (combo n0 cx (complList s.2))) := matVec_null _ _ hxu
    have hVP : poly.unitTail (matVec (padR n0 (assemble As Bs).length)
        (combo (assemble As Bs).length cw (complFam As Bs Rt spt))) :=
      unitTailAddLeft _ _
        (((matVec_length _ _).trans hLIFTl).trans
          ((matVec_length _ _).trans hPADl).symm) hUL hu2
    have hyu : poly.unitTail (combo (assemble As Bs).length cw
        (complFam As Bs Rt spt)) :=
      (elim.unitTail_append_split _ _ (poly.unitTail_oneValue_right hVP hpact)).2
    exact elim.unitTail_append hcx (ih.2.2.2.2.2.1 cw hcwL hyu)
  · intro cs hcs
    rw [hcomU] at hcs
    have hlen : cs.length = ((complList s.2).map
        (matVec (liftMat n0 (R0 :: Rt)))).length
        + ((complFam As Bs Rt spt).map
          (matVec (padR n0 (assemble As Bs).length))).length := by
      rw [hcs, ground.length_append]
    obtain ⟨cx, cw, rfl, hlx⟩ := ground.listSplit cs
      ((complList s.2).map (matVec (liftMat n0 (R0 :: Rt)))).length
      (by rw [hlen]; exact Nat.le_add_right _ _)
    have h1 : cx.length + cw.length
        = ((complList s.2).map (matVec (liftMat n0 (R0 :: Rt)))).length
          + ((complFam As Bs Rt spt).map
            (matVec (padR n0 (assemble As Bs).length))).length := by
      rw [← ground.length_append cx cw]; exact hlen
    rw [hlx] at h1
    have hlw : cw.length = ((complFam As Bs Rt spt).map
        (matVec (padR n0 (assemble As Bs).length))).length :=
      ground.addCancelL _ h1
    have hcxL : cx.length = (complList s.2).length :=
      hlx.trans (ground.length_map _ _)
    have hcwL : cw.length = (complFam As Bs Rt spt).length :=
      hlw.trans (ground.length_map _ _)
    have hxlen : (combo n0 cx (complList s.2)).length = n0 :=
      length_combo n0 cx _ hCrows
    rw [hcomU]
    intro hlt
    refine ground.leB_not_lt
      (ground.unitLeAdd ?_ (ground.leB_of_not_lt (ih.2.2.2.2.2.2 cw hcwL)))
      (BPair.lt_congr (hsplitQ (complList s.2) (complFam As Bs Rt spt)
        hCrows ih.2.2.2.2.1 cx cw hlx)
        (BPair.oneValue_refl BPair.unit) hlt)
    refine hliftLe _ hxlen ?_
    have hside := complList_side X0.1 s.2 hsp cx hcxL
    rw [hcombC cx] at hside
    exact ground.leB_of_not_lt hside

/-- The pairing's symmetry descends to the trailing assembly. -/
private theorem symP_step (A B : Mat) (As Bs : List Mat)
    (n0 : Nat) (nt : List Nat)
    (hsl : slabShape (A :: As) (B :: Bs) (n0 :: nt))
    (hsym : symP (assemble (A :: As) (B :: Bs))
      (assemble (A :: As) (B :: Bs)).length) :
    symP (assemble As Bs) (assemble As Bs).length := by
  have hA : sqAt A n0 := slab_sq hsl 0 (Nat.succ_pos _)
  have hAl : A.length = n0 := sqAt_len hA
  have hAr : rowsLen n0 A := rowsLen_of_sqAt hA
  have hk : 0 < n0 := slab_pos hsl 0 (Nat.succ_pos _)
  have hB : rectAt B n0 (ground.getAt 0 nt 0) :=
    slab_rect hsl 0 (Nat.succ_pos _)
  have ht : slabShape As Bs nt := slabShape_tail hsl
  have hIHsq : sqAt (assemble As Bs) (ground.sumNat nt) :=
    assemble_sq As Bs nt ht
  have hml : (assemble As Bs).length = ground.sumNat nt := sqAt_len hIHsq
  have hn1m : ground.getAt 0 nt 0 ≤ (assemble As Bs).length := by
    rw [hml]; exact ground.getAt_le_sumNat nt 0
  have hhd : ((assemble As Bs).headD []).length
      = (assemble As Bs).length := by
    rw [hml]; exact sqAt_headD _ _ hIHsq
  have hbtOff : transposeM (offPad (assemble As Bs).length B)
      = offT n0 (transposeM B) (assemble As Bs).length :=
    transposeM_offPad B n0 (ground.getAt 0 nt 0) _ (rectAt_len hB)
      (rectAt_rows hB) hk hn1m
  have hbtl : (transposeM (offPad (assemble As Bs).length B)).length
      = (assemble As Bs).length := by rw [hbtOff, offT_len]
  have hbtr : rowsLen n0 (transposeM (offPad (assemble As Bs).length B)) := by
    rw [hbtOff]
    exact offT_rows n0 (transposeM B) _
      (rowsLen_cast (rectAt_len hB) (rowsLen_transposeM B))
  have hAC : assemble (A :: As) (B :: Bs)
      = blockJoin A (offPad (assemble As Bs).length B) (assemble As Bs) :=
    assemble_cons A B As Bs n0 (ground.getAt 0 nt 0)
      (assemble As Bs).length hAl hk (rectAt_len hB) (rectAt_rows hB)
      hn1m rfl hhd
  have hSl : (assemble (A :: As) (B :: Bs)).length
      = n0 + (assemble As Bs).length := by
    rw [hAC]
    exact length_blockJoin A _ (assemble As Bs) n0 _ hAl
      ((offPad_len _ B).trans (rectAt_len hB)) hbtl rfl
  have hsym2 : symP (blockJoin A (offPad (assemble As Bs).length B)
      (assemble As Bs)) (n0 + (assemble As Bs).length) := by
    rw [← hAC, ← hSl]; exact hsym
  exact symP_tail A (offPad (assemble As Bs).length B) (assemble As Bs)
    n0 (assemble As Bs).length hAr hAl
    ((offPad_len _ B).trans (rectAt_len hB)) hbtl hbtr rfl hsym2

/-- The slab families' reads over the whole slab list. -/
private theorem fam_read : ∀ (diag off : List Mat) (Xs Rs : List MatQ)
    (ns : List Nat) (sps : List ((k : Nat) × Split k)),
    tailRead diag off Xs Rs ns → revListRead Xs sps →
    symP (assemble diag off) (assemble diag off).length →
    famRead diag off Rs sps
  | [], _, _, _, _, _, h, _, _ => h.1.elim
  | A :: As, [], Xs, Rs, ns, sps, h, hrl, _ => by
    have hAs : As = [] :=
      ground.nil_of_length_zero As
        (Nat.succ.inj (slabShape_len_off h.1)).symm
    subst hAs
    have hnl : ns.length = 1 := slabShape_len_ns h.1
    have hRs : Rs = [] :=
      ground.nil_of_length_zero Rs
        (Nat.succ.inj ((wShapeR_len h.2.2.1).trans hnl))
    subst hRs
    have hXl : Xs.length = 1 := (qShape_len h.2.1).trans hnl
    match Xs, hXl, hrl, h with
    | [], hb, _, _ => exact Nat.noConfusion hb
    | X0 :: Xt, hb, hrl1, h1 =>
      have hXt : Xt = [] := ground.nil_of_length_zero Xt (Nat.succ.inj hb)
      subst hXt
      match sps, hrl1 with
      | [], hbad => exact hbad.elim
      | s :: spt, hrl2 =>
        have hspt : spt = [] := by
          match spt, hrl2.2 with
          | [], _ => rfl
          | _ :: _, hb2 => exact hb2.elim
        subst hspt
        have hsp : splitRead X0.1 s.2 := hrl2.1
        have hA : sqAt A (ground.getAt 0 ns 0) :=
          slab_sq h1.1 0 (Nat.succ_pos _)
        have hAl : A.length = ground.getAt 0 ns 0 := sqAt_len hA
        have hX0 : sqAt X0.1 (ground.getAt 0 ns 0) :=
          qShape_at h1.2.1 0 (Nat.succ_pos _)
        have hs1 : s.1 = A.length :=
          ((sqAt_len hsp.1).symm.trans (sqAt_len hX0)).trans hAl.symm
        have hanc : oneValueQ X0 (ofM A) := h1.2.2.2
        have hj : matOneValue X0.1 (matScale X0.2 A) := by
          have h2 : matOneValue (matScale Pos.one X0.1)
            (matScale X0.2 A) := hanc
          rw [matScale_one] at h2
          exact h2
        have hL0 : (liftMat A.length ([] : List MatQ)).length = A.length := by
          show (matScaleB (BPair.ofPos Pos.one)
            (idMat A.length)).length = A.length
          rw [length_scaleB, idMat_len]
        have hfam : ∀ (L : Mat) (cs : List BPair), rowsLen A.length L →
            poly.oneValue (combo A.length cs
              (L.map (matVec (liftMat A.length ([] : List MatQ)))))
              (combo A.length cs L) := by
          intro L cs hL
          have hh := matVec_combo (liftMat A.length []) A.length cs L hL
          rw [hL0] at hh
          exact poly.oneValue_trans (poly.oneValue_symm hh)
            (liftMat_nil_act A.length _ (length_combo A.length cs L hL))
        have hbridge : ∀ v : List BPair,
            (quadForm X0.1 v).oneValue ((quadForm A v).scale X0.2) :=
          fun v => BPair.oneValue_trans
            (quadMatOne X0.1 (matScale X0.2 A) v hj)
            (quadForm_scale X0.2 A v)
        have hLrows : rowsLen A.length (lowerList s.2) :=
          rowsLen_cast hs1 (lowerList_rowsLen s.2)
        have hCrows : rowsLen A.length (complList s.2) :=
          rowsLen_cast hs1 (complList_rowsLen s.2)
        have hcombL : combo s.1 = combo A.length := congrArg combo hs1
        have hrf : revFold [s] = revAt s.2 := by
          rw [revFold_cons]; exact Nat.add_zero _
        have hlowU : lowFam (A :: []) ([] : List Mat) ([] : List MatQ) [s]
            = (lowerList s.2).map
              (matVec (liftMat A.length ([] : List MatQ))) := by
          show (lowerList s.2).map (matVec (liftMat A.length []))
            ++ ([] : Mat).map
              (matVec (padR A.length (assemble [] []).length))
            = (lowerList s.2).map (matVec (liftMat A.length []))
          exact ground.append_nil _
        have hcomU : complFam (A :: []) ([] : List Mat) ([] : List MatQ) [s]
            = (complList s.2).map
              (matVec (liftMat A.length ([] : List MatQ))) := by
          show (complList s.2).map (matVec (liftMat A.length []))
            ++ ([] : Mat).map
              (matVec (padR A.length (assemble [] []).length))
            = (complList s.2).map (matVec (liftMat A.length []))
          exact ground.append_nil _
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hlowU, ground.length_map,
            lowerList_length X0.1 s.2 hsp, hrf]
        · rw [hlowU]
          show rowsLen A.length ((lowerList s.2).map
            (matVec (liftMat A.length ([] : List MatQ))))
          exact rowsLen_map _ _ _
            (fun x _ => (matVec_length _ x).trans hL0)
        · intro cs hcs hoff
          rw [hlowU] at hcs
          rw [hlowU]
          show quadForm A (combo A.length cs ((lowerList s.2).map
            (matVec (liftMat A.length ([] : List MatQ))))) < BPair.unit
          refine BPair.lt_congr
            (BPair.oneValue_symm
              (quad_congr A _ _ (hfam (lowerList s.2) cs hLrows)))
            (BPair.oneValue_refl BPair.unit) ?_
          refine ltUnitOfScale (w := X0.2) ?_
          refine BPair.lt_congr (hbridge _)
            (BPair.oneValue_refl BPair.unit) ?_
          have hstrict := lowerList_strict X0.1 s.2 hsp cs
            (hcs.trans ((ground.length_map _ _).trans
              (lowerList_length X0.1 s.2 hsp))) hoff
          rw [hcombL] at hstrict
          exact hstrict
        · rw [hcomU, ground.length_map, hrf]
          show (complList s.2).length + revAt s.2 = A.length
          rw [Nat.add_comm, complList_length X0.1 s.2 hsp, hs1]
        · rw [hcomU]
          show rowsLen A.length ((complList s.2).map
            (matVec (liftMat A.length ([] : List MatQ))))
          exact rowsLen_map _ _ _
            (fun x _ => (matVec_length _ x).trans hL0)
        · intro cs hcs hu
          rw [hcomU] at hcs hu
          refine complList_indep X0.1 s.2 hsp cs
            (hcs.trans (ground.length_map _ _)) ?_
          rw [hcombL]
          exact poly.unitTail_oneValue_right hu
            (hfam (complList s.2) cs hCrows)
        · intro cs hcs hlt
          rw [hcomU] at hcs hlt
          refine complList_side X0.1 s.2 hsp cs
            (hcs.trans (ground.length_map _ _)) ?_
          rw [hcombL]
          refine BPair.lt_congr (BPair.oneValue_symm (hbridge _))
            (BPair.oneValue_refl BPair.unit) ?_
          refine scaleLtUnit X0.2 ?_
          exact BPair.lt_congr
            (quad_congr A _ _ (hfam (complList s.2) cs hCrows))
            (BPair.oneValue_refl BPair.unit) hlt
  | A :: As, B :: Bs, Xs, Rs, ns, sps, h, hrl, hsym => by
    have hAs : Bs.length + 1 = As.length :=
      Nat.succ.inj (slabShape_len_off h.1)
    have hnl : ns.length = As.length + 1 := slabShape_len_ns h.1
    have hXl : Xs.length = ns.length := qShape_len h.2.1
    have hRl : Rs.length + 1 = ns.length := wShapeR_len h.2.2.1
    match ns, hnl, hXl, hRl, h with
    | [], hb, _, _, _ => exact Nat.noConfusion hb
    | n0 :: nt, hnl1, hXl1, hRl1, h1 =>
      match Xs, hXl1, hrl, h1 with
      | [], hb, _, _ => exact Nat.noConfusion hb
      | X0 :: Xt, _, hrl1, h2 =>
        match Rs, hRl1, h2 with
        | [], hb, _ =>
          exact absurd (Nat.succ.inj (hb.trans hnl1)).symm
            (by rw [← hAs]; exact fun hh => Nat.noConfusion hh)
        | R0 :: Rt, _, h3 =>
          match sps, hrl1 with
          | [], hbad => exact hbad.elim
          | s :: spt, hrl2 =>
            exact fam_cons A B As Bs X0 R0 Xt Rt n0 nt s spt h3 hrl2.1
              hsym (fam_read As Bs Xt Rt nt spt (tailRead_tail h3) hrl2.2
                (symP_step A B As Bs n0 nt h3.1 hsym))

/-- Clause (ii)'s count split: the assembled block tridiagonal's
reversal count is the slab fold of the tail pivots' own, at stated
splits of the pivots and the datum.  The lower bound prices the
slabs' lower lists carried by the telescope, the upper bound their
complement lists, each family joined over the slab list and read at
`lem:inertia`'s forcing clauses once. -/
theorem countSplit {n : Nat} (diag off : List Mat) (Xs Rs : List MatQ)
    (ns : List Nat) (sps : List ((k : Nat) × Split k)) (SP : Split n)
    (ht : tailRead diag off Xs Rs ns)
    (hl : revListRead Xs sps)
    (hS : splitRead (assemble diag off) SP) :
    revAt SP = revFold sps := by
  have hSl : (assemble diag off).length = n := sqAt_len hS.1
  have hSr : rowsLen n (assemble diag off) := rowsLen_of_sqAt hS.1
  have hsymP : symP (assemble diag off) (assemble diag off).length := by
    rw [hSl]
    exact symP_of_sym (assemble diag off) n hSl hSr
      (splitRead_symm (assemble diag off) SP hS)
  have hfam := fam_read diag off Xs Rs ns sps ht hl hsymP
  have hge : revFold sps ≤ revAt SP := by
    have hfin := forcing (assemble diag off) SP hS
      (lowFam diag off Rs sps) (rowsLen_cast hSl hfam.2.1)
      (fun cs hcs hoff => by
        have hh := hfam.2.2.1 cs hcs hoff
        rw [hSl] at hh
        exact hh)
    rw [hfam.1] at hfin
    exact hfin
  have hle : revAt SP ≤ revFold sps := by
    have hup := forcing_upper (assemble diag off) SP hS
      (complFam diag off Rs sps) (rowsLen_cast hSl hfam.2.2.2.2.1)
      (fun cs hcs hu => by
        refine hfam.2.2.2.2.2.1 cs hcs ?_
        rw [hSl]
        exact hu)
      (fun cs hcs => by
        have hh := hfam.2.2.2.2.2.2 cs hcs
        rw [hSl] at hh
        exact hh)
    have hlen : (complFam diag off Rs sps).length + revFold sps = n := by
      rw [hfam.2.2.2.1, hSl]
    refine ground.leCancelR (complFam diag off Rs sps).length ?_
    rw [Nat.add_comm (revAt SP) _, Nat.add_comm (revFold sps) _, hlen]
    exact hup
  exact Nat.le_antisymm hle hge

/-- The count split's read at a datum reading the assembled
matrix's value: the coherence bundle whole. -/
theorem countSplit_read {n : Nat} (S : Mat) (diag off : List Mat)
    (Xs Rs : List MatQ) (ns : List Nat)
    (sps : List ((k : Nat) × Split k)) (SP : Split n)
    (hM : matOneValue S (assemble diag off))
    (ht : tailRead diag off Xs Rs ns) (hl : revListRead Xs sps)
    (hS : splitRead S SP) :
    countSplitRead S diag off Xs Rs sps SP ns := by
  refine ⟨hM, ht, hl, hS, ?_⟩
  have hAsq : sqAt (assemble diag off) (ground.sumNat ns) :=
    assemble_sq diag off ns ht.1
  have hn : ground.sumNat ns = n :=
    (sqAt_len hAsq).symm.trans
      ((matOne_length hM).symm.trans (sqAt_len hS.1))
  rw [hn] at hAsq
  exact countSplit diag off Xs Rs ns sps SP ht hl
    (splitRead_congr S (assemble diag off) hAsq hM SP hS)

/-! The chain's suffix reads: the recursion and the pivots' splits
at the dropped leading slabs, with the slab fold split at the
dropped count. -/

/-- The tail recursion drops its leading slabs: the recursion runs
top-down from the last slab, so the dropped chain reads the
recursion's own data (`lem:greenprod`(i), one recursion datum
holding the whole tail). -/
theorem tailRead_drop (diag off : List Mat) (Xs Rs : List MatQ)
    (ns : List Nat) (h : Nat) (hh : h < diag.length)
    (ht : tailRead diag off Xs Rs ns) :
    tailRead (diag.drop h) (off.drop h) (Xs.drop h) (Rs.drop h)
      (ns.drop h) := by
  induction h generalizing diag off Xs Rs ns with
  | zero => exact ht
  | succ h ih =>
    cases diag with
    | nil => exact absurd hh (Nat.not_lt_zero _)
    | cons A As =>
      have hAs : h < As.length := Nat.lt_of_succ_lt_succ hh
      cases off with
      | nil =>
        have hz : (0 : Nat) = As.length :=
          Nat.succ.inj (slabShape_len_off ht.1)
        rw [← hz] at hAs
        exact absurd hAs (Nat.not_lt_zero h)
      | cons B Bs =>
        cases ns with
        | nil => exact Nat.noConfusion (slabShape_len_ns ht.1)
        | cons n0 nt =>
          cases Xs with
          | nil => exact Nat.noConfusion (qShape_len ht.2.1)
          | cons X0 Xt =>
            cases Rs with
            | nil =>
              have hz : (0 : Nat) = nt.length :=
                Nat.succ.inj (wShapeR_len ht.2.2.1)
              have hn : nt.length = As.length :=
                Nat.succ.inj (slabShape_len_ns ht.1)
              rw [← hn, ← hz] at hAs
              exact absurd hAs (Nat.not_lt_zero h)
            | cons R0 Rt =>
              exact ih As Bs Xt Rt nt hAs (tailRead_tail ht)

/-- The pivots' splits drop with the pivots, the componentwise
relation's suffix. -/
theorem revListRead_drop (Xs : List MatQ)
    (sps : List ((k : Nat) × Split k)) (h : Nat)
    (hl : revListRead Xs sps) :
    revListRead (Xs.drop h) (sps.drop h) := by
  induction h generalizing Xs sps with
  | zero => exact hl
  | succ h ih =>
    cases Xs with
    | nil =>
      cases sps with
      | nil => exact trivial
      | cons _ _ => exact (hl : False).elim
    | cons X Xt =>
      cases sps with
      | nil => exact (hl : False).elim
      | cons _ spt => exact ih Xt spt hl.2

/-- The pivots' splits pair the pivots one for one, the
componentwise relation's count tie. -/
theorem revListRead_length : ∀ (Xs : List MatQ)
    (sps : List ((k : Nat) × Split k)),
    revListRead Xs sps → Xs.length = sps.length
  | [], [], _ => rfl
  | [], _ :: _, h => (h : False).elim
  | _ :: _, [], h => (h : False).elim
  | _ :: Xs, _ :: sps, h =>
    congrArg (· + 1) (revListRead_length Xs sps h.2)

/-- The slab fold splits at a leading count, the two parts'
sum. -/
theorem revFold_split (sps : List ((k : Nat) × Split k)) (h : Nat) :
    revFold sps = revFold (sps.take h) + revFold (sps.drop h) := by
  induction h generalizing sps with
  | zero => exact (Nat.zero_add (revFold sps)).symm
  | succ h ih =>
    cases sps with
    | nil => rfl
    | cons s t =>
      show revFold (s :: t) = revFold (s :: t.take h) + revFold (t.drop h)
      rw [revFold_cons s t, revFold_cons s (t.take h), ih t, Nat.add_assoc]

end greenprod
