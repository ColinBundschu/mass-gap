import MassGap.Greenprod
import MassGap.Deckfactor
import MassGap.Split
/-!
`lem:spectator` — the spectator law at two slab families on one
split.  Clause (i): the tail pivots are equal outright beyond the
perturbation (`tailShareRead`, the recursions on equal data from an
equal seed), and the deviation sits in the boundary-direction
pivots alone, the exact sandwich `D_{i+1} = T_iᵀ D_i T'_i` at the
two families' transfer factors (`devQ` the deviation's cleared
datum, `sandwichStep` the one-step read, `sandwichRead` the family
bundle at the shared-data guards) — re-convergence and the Green
products' falloff the one identity, stated twice; the reversed slab
order reads the identity at the tail witnesses, the head pivots equal
below the perturbation slab (`headShareRead`) and the tail deviation
sandwiched down to the head at the tail transfer factors
(`tailSandwichRead`, the one step `sandwichStep` at the witnesses'
places exchanged).  Clause (ii): the
caps propagate geometrically — a transfer factor's certificate
`Tᵀ Gᵢ T ⪯ λ² Gᵢ₊₁` at a cleared pair and the gram's slab blocks
(`contractRead`), a deviation's
two-sided cap at `c G` (`capQ` at `lem:inertia`'s two splits), and
the step's conclusion `2 D_{i+1}` two-sided at
`c (λ² + λ'²) G_{i+1}`, the cap's block the deeper slab's and the
conclusion's its own (`capStepRead`, the two splits at `u + v` and
`u + v̌` the derivation's).  Clause (iii): the bulk pivot is the
deck-interior solvent — the deck polynomial the determinant of the
quadratic site datum (`deckPMat`, `deckPoly`, its deck symmetry
`lem:deckfactor`'s read), the solvent identity `Bᵀ X² + B = A X`
(`solventRead`), the pivot-identity pair `Y X = B`, `Y + Bᵀ X = A`
(`pivotPairRead`) with the pivot map's step `Y♯ = A + Bᵀ T`
(`pivotStepRead`), and the exact factorization `U = U₁ U₂` at the
cleared factors `z Bᵀ + Bᵀ X - A` and `z - X` (`facSplitRead` at
`split.pmatMul`); the scalar instance is
the walk pencil's bulk datum, the error law
`e_{L+1} = z² e_L + z e_L e_{L+1}` the sandwich's own read there.
The ball certificate carries three counts at a located center —
the pivot map's step there, the transfer factor's contraction at
`λ` pricing the solvent's roots inside, the floor
`Ŷ ⪰ (y0 + ρ) G` (`floorRead`) and the center defect capped at
`ρ0` — beside the modulus data, `λ∘` at `y0 λ∘ = λ (y0 + ρ)` and
`ρ0 + μ ρ ≤ ρ` at `μ = λ∘²` (`ballRead` at `contractRead` and
`capQ`); the ball's membership walk reads each pivot square at the
stated order with its deviation from the center capped two-sidedly
at `ρ G` (`ballList`), and a ball member's every split reads the
upper side — the floor with the cap price the member's form at or
above the sum's unit at every vector, the gram's own positive
read the cap's (`ball_psd`); and the cap chain iterates clause
(ii)'s step down the recursion-named brackets at the gram list's
own slab blocks (`capWalk`).  The
companion kernels over stored towers with the graph read's tower
sign are the emitted certificates' tier at their recorded
consumers (`thm:decimation`(iii)'s deck divisors,
`lem:cornerpivot`(vii)'s block chains, `thm:groundreads`'
windows). -/

namespace spectator
open ground poly elim inertia greenprod

/-- The transposed cleared datum. -/
def transposeQ (a : MatQ) : MatQ := (transposeM a.1, a.2)

/-- The deviation's cleared datum, the site structure at two
pivots. -/
def devQ (Y' Y : MatQ) : MatQ := addQ Y' (swapQ Y)

/-- The doubled datum, the cap display's left side. -/
def doubleQ (a : MatQ) : MatQ := (matScale 2 a.1, a.2)

/-- The sandwich's one step: `D_{i+1} = T_iᵀ D_i T'_i` at the two
families' transfer factors, the shapes at the boundary's two
orders. -/
def sandwichStep (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) : Prop :=
  rectAt C.1 n n' ∧ rectAt C'.1 n n'
  ∧ sqAt Y1'.1 n' ∧ sqAt Y1.1 n' ∧ sqAt Y0'.1 n ∧ sqAt Y0.1 n
  ∧ oneValueQ (devQ Y1' Y1)
      (mulQ (transposeQ (transfer C)) (mulQ (devQ Y0' Y0) (transfer C')))

instance (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) :
    Decidable (sandwichStep C C' Y1' Y1 Y0' Y0 n n') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ oneValueQ _ _))

/-- Clause (i)'s tail read: the two tail recursions with the pivots
equal outright beyond the perturbation slab. -/
def tailShareRead (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  tailRead diag off Xs Rs ns
  ∧ tailRead diag' off' Xs' Rs' ns
  ∧ ((List.range Xs.length).all (fun i =>
      Nat.ble i w0 || decide (oneValueQ (ground.getAt dM Xs' i)
        (ground.getAt dM Xs i)))) = true

instance (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 : Nat) (ns : List Nat) :
    Decidable (tailShareRead diag off diag' off' Xs Rs Xs' Rs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _))

/-- The sandwich's family bundle: the two head recursions, the
shared data beyond the perturbation slab, and the telescoping
steps. -/
def sandwichRead (diag off diag' off' : List Mat)
    (Ys Cs Ys' Cs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  headRead diag off Ys Cs ns
  ∧ headRead diag' off' Ys' Cs' ns
  ∧ ((List.range diag.length).all (fun i =>
      Nat.ble i w0 || decide (matOneValue (ground.getAt [] diag' i)
        (ground.getAt [] diag i)))) = true
  ∧ ((List.range off.length).all (fun i =>
      decide (i < w0) || decide (matOneValue (ground.getAt [] off' i)
        (ground.getAt [] off i)))) = true
  ∧ ((List.range (Cs.length - w0)).all (fun k => decide
      (sandwichStep (ground.getAt dM Cs (w0 + k))
        (ground.getAt dM Cs' (w0 + k))
        (ground.getAt dM Ys' (w0 + k + 1))
        (ground.getAt dM Ys (w0 + k + 1))
        (ground.getAt dM Ys' (w0 + k))
        (ground.getAt dM Ys (w0 + k))
        (ground.getAt 0 ns (w0 + k))
        (ground.getAt 0 ns (w0 + k + 1))))) = true

instance (diag off diag' off' : List Mat) (Ys Cs Ys' Cs' : List MatQ)
    (w0 : Nat) (ns : List Nat) :
    Decidable (sandwichRead diag off diag' off' Ys Cs Ys' Cs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _ ∧ _ = _ ∧ _ = _))

/-- The reversed slab order's head read: the two head recursions with
the pivots equal outright below the perturbation slab. -/
def headShareRead (diag off diag' off' : List Mat)
    (Ys Cs Ys' Cs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  headRead diag off Ys Cs ns
  ∧ headRead diag' off' Ys' Cs' ns
  ∧ ((List.range Ys.length).all (fun i =>
      Nat.ble w0 i || decide (oneValueQ (ground.getAt dM Ys' i)
        (ground.getAt dM Ys i)))) = true

instance (diag off diag' off' : List Mat)
    (Ys Cs Ys' Cs' : List MatQ) (w0 : Nat) (ns : List Nat) :
    Decidable (headShareRead diag off diag' off' Ys Cs Ys' Cs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _))

/-- The reversed slab order's sandwich bundle: the two tail recursions,
the shared data below the perturbation slab, and the telescoping
steps `E_i = Ť_{i+1}ᵀ E_{i+1} Ť'_{i+1}` down to the head at the tail
witnesses' transfer factors. -/
def tailSandwichRead (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 : Nat) (ns : List Nat) : Prop :=
  tailRead diag off Xs Rs ns
  ∧ tailRead diag' off' Xs' Rs' ns
  ∧ ((List.range diag.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] diag' i)
        (ground.getAt [] diag i)))) = true
  ∧ ((List.range off.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] off' i)
        (ground.getAt [] off i)))) = true
  ∧ ((List.range w0).all (fun k => decide
      (sandwichStep (ground.getAt dM Rs k)
        (ground.getAt dM Rs' k)
        (ground.getAt dM Xs' k)
        (ground.getAt dM Xs k)
        (ground.getAt dM Xs' (k + 1))
        (ground.getAt dM Xs (k + 1))
        (ground.getAt 0 ns (k + 1))
        (ground.getAt 0 ns k)))) = true

instance (diag off diag' off' : List Mat) (Xs Rs Xs' Rs' : List MatQ)
    (w0 : Nat) (ns : List Nat) :
    Decidable (tailSandwichRead diag off diag' off' Xs Rs Xs' Rs' w0 ns) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _ ∧ _ = _ ∧ _ = _))

/-- The transfer factor's contraction certificate at the slab
split's two grams: `Tᵀ Gi T ⪯ λ² Gs` at a cleared pair
`λ = [ln : ld]`, the image's form against its own slab's gram
priced at the source's, the datum and its split at the source's
order — the factor rectangular at the slabs' own orders, a square
slab's read the one-gram instance. -/
def contractRead {o : Nat} (T : MatQ) (Gi Gsr : Mat) (ln ld : Pos)
    (sp : Split o) : Prop :=
  sqAt Gi T.1.length ∧ rowsLen o T.1 ∧ sqAt Gsr o
  ∧ splitRead (siteDatum (matScale (ln * ln * (T.2 * T.2)) Gsr)
      (matScale (ld * ld) (matMul (transposeM T.1) (matMul Gi T.1)))) sp
  ∧ psdAt sp

instance {o : Nat} (T : MatQ) (Gi Gsr : Mat) (ln ld : Pos) (sp : Split o) :
    Decidable (contractRead T Gi Gsr ln ld sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- A cleared datum's two-sided cap at `[cn : cd] G`, the two
splits `lem:inertia`'s witnesses. -/
def capQ {o : Nat} (D : MatQ) (G : Mat) (cn cd : Pos)
    (spU spL : Split o) : Prop :=
  capAt (matScale cd D.1) (matScale (cn * D.2) G) spU spL

instance {o : Nat} (D : MatQ) (G : Mat) (cn cd : Pos)
    (spU spL : Split o) : Decidable (capQ D G cn cd spU spL) :=
  inferInstanceAs (Decidable (capAt _ _ _ _))

/-- Clause (ii)'s step: the sandwich's step at the two contraction
certificates and the deviation's cap propagates to the doubled next
deviation at `c (λ² + λ'²) G_{i+1}`, the geometric read, each display's
gram its own slab's block — the deviation's cap at the deeper
block, the doubled next at the headward block. -/
def capStepRead {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ)
    (Gd Gh : Mat) (cn cd ln ld ln' ld' : Pos) (sp1 sp2 : Split n')
    (spU spL : Split n) (spU' spL' : Split n') : Prop :=
  sandwichStep C C' Y1' Y1 Y0' Y0 n n'
  ∧ contractRead (transfer C) Gd Gh ln ld sp1
  ∧ contractRead (transfer C') Gd Gh ln' ld' sp2
  ∧ capQ (devQ Y0' Y0) Gd cn cd spU spL
  ∧ capQ (doubleQ (devQ Y1' Y1)) Gh
      (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld)))
      (cd * (ld * ld * (ld' * ld'))) spU' spL'

instance {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ) (Gd Gh : Mat)
    (cn cd ln ld ln' ld' : Pos) (sp1 sp2 : Split n')
    (spU spL : Split n) (spU' spL' : Split n') :
    Decidable (capStepRead C C' Y1' Y1 Y0' Y0 Gd Gh cn cd ln ld
      ln' ld' sp1 sp2 spU spL spU' spL') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-! Clause (iii): the deck polynomial, the solvent, the pivot
identities, and the exact factorization. -/

private def entryAt (m : Mat) (i j : Nat) : BPair :=
  ground.getAt BPair.unit (ground.getAt [] m i) j

/-- The quadratic site datum's polynomial matrix,
`Bᵀ z² - A z + B` entrywise. -/
def deckPMat (A B : Mat) : split.PMat :=
  ground.matOf A.length A.length (fun i j =>
    [entryAt B i j, (entryAt A i j).swap, entryAt B j i])

/-- The deck polynomial, the quadratic site datum's determinant,
its deck symmetry `lem:deckfactor`'s read. -/
def deckPoly (A B : Mat) : Poly := split.pminor (deckPMat A B)

/-- The solvent identity `Bᵀ X² + B = A X` at the cleared
solvent. -/
def solventRead (X : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt X.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ oneValueQ (addQ (mulQ (transposeQ (ofM B)) (mulQ X X)) (ofM B))
      (mulQ (ofM A) X)

instance (X : MatQ) (A B : Mat) (n : Nat) :
    Decidable (solventRead X A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ oneValueQ _ _))

/-- The pivot-identity pair `Y X = B`, `Y + Bᵀ X = A`. -/
def pivotPairRead (Y X : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt Y.1 n ∧ sqAt X.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ oneValueQ (mulQ Y X) (ofM B)
  ∧ oneValueQ (addQ Y (mulQ (transposeQ (ofM B)) X)) (ofM A)

instance (Y X : MatQ) (A B : Mat) (n : Nat) :
    Decidable (pivotPairRead Y X A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The pivot map's step: the witness at `Y C = B` with the image
`Y♯ = A + Bᵀ T` at the transfer factor. -/
def pivotStepRead (Y C Ynext : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt Y.1 n ∧ sqAt C.1 n ∧ sqAt Ynext.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ oneValueQ (mulQ Y C) (ofM B)
  ∧ oneValueQ Ynext
      (addQ (ofM A) (mulQ (ofM (transposeM B)) (transfer C)))

instance (Y C Ynext : MatQ) (A B : Mat) (n : Nat) :
    Decidable (pivotStepRead Y C Ynext A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The exact factorization `U = U₁ U₂` at the cleared factors:
`X₂ U₁ = z X₂ Bᵀ + Bᵀ X₁ - X₂ A` and `X₂ U₂ = z X₂ - X₁`, the
product against the quadratic site datum at the clearing's
square. -/
def facSplitRead (X : MatQ) (A B : Mat) (n : Nat) : Prop :=
  sqAt X.1 n ∧ sqAt A n ∧ sqAt B n
  ∧ split.pmatOneValue
    (split.pmatMul
      (ground.matOf A.length A.length (fun i j =>
        [entryAt (matAdd (matMul (transposeM B) X.1)
           (matSwap (matScale X.2 A))) i j,
         entryAt (matScale X.2 (transposeM B)) i j]))
      (ground.matOf A.length A.length (fun i j =>
        [(entryAt X.1 i j).swap,
         if i == j then BPair.ofPos X.2 else BPair.unit])))
    ((deckPMat A B).map (fun r => r.map (fun p =>
      p.map (fun x => x.scale (X.2 * X.2)))))

instance (X : MatQ) (A B : Mat) (n : Nat) :
    Decidable (facSplitRead X A B n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ split.pmatOneValue _ _))

/-- The ball center's floor `Ŷ ⪰ (y0 + ρ) G` at the cleared
scales, one split. -/
def floorRead {o : Nat} (Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (spF : Split o) : Prop :=
  splitRead (siteDatum (matScale (y0d * rd) Yc.1)
    (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) spF
  ∧ psdAt spF

instance {o : Nat} (Yc : MatQ) (G : Mat) (y0n y0d rn rd : Pos)
    (spF : Split o) :
    Decidable (floorRead Yc G y0n y0d rn rd spF) :=
  inferInstanceAs (Decidable (_ ∧ _ = _))

/-- The ball certificate's three counts at a located center — the
pivot map's step at the center, the transfer factor's contraction
at `λ`, the floor at `y0 + ρ`, the center defect capped at `ρ0` —
with the modulus data: `λ∘` at `y0 λ∘ = λ (y0 + ρ)` and
`ρ0 + μ ρ ≤ ρ` at `μ = λ∘²`, the cross-multiplied reads, the
modulus below one at the occupied `ρ0`'s own margin. -/
def ballRead {o : Nat} (Yc Cc Ysh : MatQ) (A B G : Mat)
    (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (spC spF spU spL : Split o) : Prop :=
  pivotStepRead Yc Cc Ysh A B o
  ∧ contractRead (transfer Cc) G G ln ld spC
  ∧ floorRead Yc G y0n y0d rn rd spF
  ∧ capQ (devQ Ysh Yc) G r0n r0d spU spL
  ∧ y0n * (lcn * (ld * rd)) = ln * ((y0n * rd + rn * y0d) * lcd)
  ∧ r0n * ((lcd * lcd) * rd) + (lcn * lcn) * (rn * r0d)
      ≤ rn * (r0d * (lcd * lcd))

instance {o : Nat} (Yc Cc Ysh : MatQ) (A B G : Mat)
    (ln ld y0n y0d rn rd r0n r0d lcn lcd : Pos)
    (spC spF spU spL : Split o) :
    Decidable (ballRead Yc Cc Ysh A B G ln ld y0n y0d rn rd
      r0n r0d lcn lcd spC spF spU spL) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ = _ ∧ _ ≤ _))

/-- The ball's membership walk: each pivot square at the stated
order with its deviation from the center capped two-sidedly at
`ρ G`, one shape read and one cap pair per pivot. -/
def ballList {o : Nat} (Yc : MatQ) (G : Mat) (rn rd : Pos) :
    List MatQ → List (Split o × Split o) → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | X :: Xs, sp :: sps =>
      sqAt X.1 o
      ∧ capQ (devQ X Yc) G rn rd sp.1 sp.2
      ∧ ballList Yc G rn rd Xs sps

def decBallList {o : Nat} (Yc : MatQ) (G : Mat) (rn rd : Pos) :
    ∀ (Xs : List MatQ) (sps : List (Split o × Split o)),
    Decidable (ballList Yc G rn rd Xs sps)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse (fun h => h)
  | _ :: _, [] => isFalse (fun h => h)
  | _ :: Xs, _ :: sps =>
      @instDecidableAnd _ _ inferInstance
        (@instDecidableAnd _ _ inferInstance
          (decBallList Yc G rn rd Xs sps))

instance {o : Nat} (Yc : MatQ) (G : Mat) (rn rd : Pos)
    (Xs : List MatQ) (sps : List (Split o × Split o)) :
    Decidable (ballList Yc G rn rd Xs sps) :=
  decBallList Yc G rn rd Xs sps

/-- Clause (ii)'s iteration: the cap steps walked down the chain
at the recursion-named brackets, each step's out cap the next
step's stated pair and the gram list walking the slabs' own blocks
beside the reversed factors, the bracket at depth `i` named and
geometric.  Each certificate carries the step's order pair — the
deeper then the headward — the two certified pairs, the two
contraction splits at the headward order, the in cap's pair at the
deeper, and the out cap's at the headward. -/
def capWalk : List Mat → Pos → Pos → MatQ → MatQ →
    List MatQ → List MatQ → List MatQ → List MatQ →
    List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2) →
    Prop
  | _, _, _, _, _, [], [], [], [], [] => True
  | _, _, _, _, _, [], [], [], [], _ :: _ => False
  | _, _, _, _, _, [], [], [], _ :: _, _ => False
  | _, _, _, _, _, [], [], _ :: _, _, _ => False
  | _, _, _, _, _, [], _ :: _, _, _, _ => False
  | _, _, _, _, _, _ :: _, [], _, _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] => False
  | Gs, cn, cd, Y0', Y0, C :: Cs, C' :: Cs', Y1 :: Ys, Y1' :: Ys',
      ⟨_, lam, lam', sp1, sp2, spU, spL, spU', spL'⟩ :: certs =>
      capStepRead C C' Y1' Y1 Y0' Y0 (ground.getAt [] Gs 0)
        (ground.getAt [] Gs 1) cn cd lam.1 lam.2 lam'.1 lam'.2
        sp1 sp2 spU spL spU' spL'
      ∧ capWalk (Gs.drop 1)
          (cn * (lam.1 * lam.1 * (lam'.2 * lam'.2)
            + lam'.1 * lam'.1 * (lam.2 * lam.2)))
          (2 * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2))))
          Y1' Y1 Cs Cs' Ys Ys' certs

def decCapWalk : ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2)),
    Decidable (capWalk Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs)
  | _, _, _, _, _, [], [], [], [], [] => isTrue trivial
  | _, _, _, _, _, [], [], [], [], _ :: _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], [], _ :: _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], _ :: _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], _ :: _, _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, [], _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] =>
      isFalse (fun h => h)
  | _, _, _, _, _, _ :: Cs, _ :: Cs', _ :: Ys, _ :: Ys',
      ⟨_, _, _, _, _, _, _, _, _⟩ :: certs =>
      @instDecidableAnd _ _ inferInstance
        (decCapWalk _ _ _ _ _ Cs Cs' Ys Ys' certs)

instance (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
    (Cs Cs' Ys Ys' : List MatQ)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2)) :
    Decidable (capWalk Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs) :=
  decCapWalk Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs

/-- The tied sandwich's step at the reversed slab order:
`E_i = Ř_{i+1}ᵀ E_{i+1} Ř'_{i+1} + δ·1` at the tail witnesses'
transfer factors, the tie's datum riding each step, the shapes at
the boundary's two orders. -/
def driftStep (dn : BPair) (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) :
    Prop :=
  rectAt C.1 n n' ∧ rectAt C'.1 n n'
  ∧ sqAt Y1'.1 n' ∧ sqAt Y1.1 n' ∧ sqAt Y0'.1 n ∧ sqAt Y0.1 n
  ∧ oneValueQ (devQ Y1' Y1)
      (addQ
        (mulQ (transposeQ (transfer C))
          (mulQ (devQ Y0' Y0) (transfer C')))
        (matScaleB dn (idMat n'), Pos.one))

instance (dn : BPair) (C C' Y1' Y1 Y0' Y0 : MatQ) (n n' : Nat) :
    Decidable (driftStep dn C C' Y1' Y1 Y0' Y0 n n') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ oneValueQ _ _))

/-- Clause (ii)'s step at the tie: the two contraction certificates
and the deviation's cap propagate to the doubled next deviation at
`c (λ² + λ'²) G_{i+1} + 2 s G_{i+1}`, each display's gram its own
slab's block — the deviation's cap at the deeper block, the tie
datum's identity capped two-sidedly at `s G_{i+1}` at the headward
block joining the step's display, the two splits' own polarization
at the identity's datum. -/
def driftCapStep {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ)
    (Gd Gh : Mat) (dn : BPair) (cn cd sn sd ln ld ln' ld' : Pos)
    (sp1 sp2 : Split n') (spU spL : Split n) (spU' spL' : Split n')
    (spS spS' : Split n') : Prop :=
  driftStep dn C C' Y1' Y1 Y0' Y0 n n'
  ∧ contractRead (transfer C) Gd Gh ln ld sp1
  ∧ contractRead (transfer C') Gd Gh ln' ld' sp2
  ∧ capQ ((matScaleB dn (idMat n')), Pos.one) Gh sn sd spS spS'
  ∧ capQ (devQ Y0' Y0) Gd cn cd spU spL
  ∧ capQ (doubleQ (devQ Y1' Y1)) Gh
      (cn * (ln * ln * (ld' * ld') + ln' * ln' * (ld * ld)) * sd
        + 2 * (sn * (cd * (ld * ld * (ld' * ld')))))
      (cd * (ld * ld * (ld' * ld')) * sd) spU' spL'

instance {n n' : Nat} (C C' Y1' Y1 Y0' Y0 : MatQ) (Gd Gh : Mat)
    (dn : BPair) (cn cd sn sd ln ld ln' ld' : Pos)
    (sp1 sp2 : Split n') (spU spL : Split n) (spU' spL' : Split n')
    (spS spS' : Split n') :
    Decidable (driftCapStep C C' Y1' Y1 Y0' Y0 Gd Gh dn cn cd sn sd
      ln ld ln' ld' sp1 sp2 spU spL spU' spL' spS spS') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The step updates folded over the certificates: the seed's
geometric read joined to the tie datum's fold, one summand per
step. -/
def driftFold : Pos → Pos → Pos → Pos →
    List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2) →
    Pos × Pos
  | cn, cd, _, _, [] => (cn, cd)
  | cn, cd, sn, sd, ⟨_, lam, lam', _⟩ :: cs =>
      driftFold
        (cn * (lam.1 * lam.1 * (lam'.2 * lam'.2)
            + lam'.1 * lam'.1 * (lam.2 * lam.2)) * sd
          + 2 * (sn * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)))))
        (2 * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)) * sd)) sn sd cs

/-- Clause (ii)'s iteration at the tie: the tied cap steps walked
down the chain at the recursion-named brackets, each step's out cap
the next step's stated pair and the gram list walking the slabs'
own blocks beside the reversed factors, the bracket at depth `i`
the seed's geometric read joined to the tie datum's fold over the
steps' certificates.  Each certificate carries the step's order
pair — the deeper then the headward — the two certified pairs, the
two contraction splits at the headward order, the in cap's pair at
the deeper, the out cap's at the headward, and the tie datum's two
splits at the headward. -/
def driftWalk (dn : BPair) (sn sd : Pos) :
    List Mat → Pos → Pos → MatQ → MatQ →
    List MatQ → List MatQ → List MatQ → List MatQ →
    List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2) →
    Prop
  | _, _, _, _, _, [], [], [], [], [] => True
  | _, _, _, _, _, [], [], [], [], _ :: _ => False
  | _, _, _, _, _, [], [], [], _ :: _, _ => False
  | _, _, _, _, _, [], [], _ :: _, _, _ => False
  | _, _, _, _, _, [], _ :: _, _, _, _ => False
  | _, _, _, _, _, _ :: _, [], _, _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => False
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] => False
  | Gs, cn, cd, Y0', Y0, C :: Cs, C' :: Cs', Y1 :: Ys, Y1' :: Ys',
      ⟨_, lam, lam', sp1, sp2, spU, spL, spU', spL', spS, spS'⟩
        :: certs =>
      driftCapStep C C' Y1' Y1 Y0' Y0 (ground.getAt [] Gs 0)
        (ground.getAt [] Gs 1) dn cn cd sn sd lam.1 lam.2 lam'.1 lam'.2
        sp1 sp2 spU spL spU' spL' spS spS'
      ∧ driftWalk dn sn sd (Gs.drop 1)
          (cn * (lam.1 * lam.1 * (lam'.2 * lam'.2)
              + lam'.1 * lam'.1 * (lam.2 * lam.2)) * sd
            + 2 * (sn * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)))))
          (2 * (cd * (lam.2 * lam.2 * (lam'.2 * lam'.2)) * sd))
          Y1' Y1 Cs Cs' Ys Ys' certs

def decDriftWalk (dn : BPair) (sn sd : Pos) :
    ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2 × Split p.2 × Split p.2)),
    Decidable (driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs)
  | _, _, _, _, _, [], [], [], [], [] => isTrue trivial
  | _, _, _, _, _, [], [], [], [], _ :: _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], [], _ :: _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], [], _ :: _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, [], _ :: _, _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, [], _, _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _ => isFalse (fun h => h)
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [] =>
      isFalse (fun h => h)
  | _, _, _, _, _, _ :: Cs, _ :: Cs', _ :: Ys, _ :: Ys',
      ⟨_, _, _, _, _, _, _, _, _, _, _⟩ :: certs =>
      @instDecidableAnd _ _ inferInstance
        (decDriftWalk dn sn sd _ _ _ _ _ Cs Cs' Ys Ys' certs)

instance (dn : BPair) (sn sd : Pos) (Gs : List Mat) (cn cd : Pos)
    (Y0' Y0 : MatQ) (Cs Cs' Ys Ys' : List MatQ)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)) :
    Decidable (driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs) :=
  decDriftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs

/-- The two windows at their own roots' site data at one shared
clearing: the couplings equal and the diagonals tied at the roots'
drift below the perturbation slab, the two tail recursions, the
tied steps, and the tied walk from the slab down to the
observable's depth at the gram list's own slab blocks. -/
def driftShareRead (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)) :
    Prop :=
  greenprod.tailRead diag off Xs Rs ns
  ∧ greenprod.tailRead diag' off' Xs' Rs' ns
  ∧ ((List.range off.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] off' i)
        (ground.getAt [] off i)))) = true
  ∧ ((List.range diag.length).all (fun i =>
      Nat.ble w0 i || decide (matOneValue (ground.getAt [] diag' i)
        (matAdd (ground.getAt [] diag i)
          (matScaleB dn (idMat (ground.getAt 0 ns i))))))) = true
  ∧ ((List.range diag.length).all (fun k =>
      Nat.ble w0 k || decide
      (driftStep dn (ground.getAt greenprod.dM Rs k)
        (ground.getAt greenprod.dM Rs' k)
        (ground.getAt greenprod.dM Xs' k)
        (ground.getAt greenprod.dM Xs k)
        (ground.getAt greenprod.dM Xs' (k + 1))
        (ground.getAt greenprod.dM Xs (k + 1))
        (ground.getAt 0 ns (k + 1))
        (ground.getAt 0 ns k)))) = true
  ∧ driftWalk dn sn sd Gs cn cd (ground.getAt greenprod.dM Xs' w0)
      (ground.getAt greenprod.dM Xs w0)
      ((Rs.take w0).drop j).reverse ((Rs'.take w0).drop j).reverse
      ((Xs.take w0).drop j).reverse ((Xs'.take w0).drop j).reverse certs

instance (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)) :
    Decidable (driftShareRead diag off diag' off' Xs Rs Xs' Rs'
      w0 j ns dn cn cd sn sd Gs certs) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ = _ ∧ _ = _ ∧ _ = _ ∧ _))

/-- The doubled datum's cap reads the datum's own at the doubled
clearing. -/
private theorem capQ_double {o : Nat} (D : MatQ) (G : Mat)
    (cn cd : Pos) (spU spL : Split o)
    (h : capQ (doubleQ D) G cn cd spU spL) :
    capQ D G cn (2 * cd) spU spL := by
  have h' : capAt (matScale cd (matScale 2 D.1))
      (matScale (cn * D.2) G) spU spL := h
  rw [matScale_matScale 2 cd D.1, ground.mul_comm cd 2] at h'
  exact h'

/-- The tied walk's lists at the certificate count. -/
theorem driftWalk_len (dn : BPair) (sn sd : Pos) :
    ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2 × Split p.2 × Split p.2)),
    driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs →
    Cs.length = certs.length ∧ Cs'.length = certs.length
      ∧ Ys.length = certs.length ∧ Ys'.length = certs.length
  | _, _, _, _, _, [], [], [], [], [], _ => ⟨rfl, rfl, rfl, rfl⟩
  | _, _, _, _, _, [], [], [], [], _ :: _, h => False.elim h
  | _, _, _, _, _, [], [], [], _ :: _, _, h => False.elim h
  | _, _, _, _, _, [], [], _ :: _, _, _, h => False.elim h
  | _, _, _, _, _, [], _ :: _, _, _, _, h => False.elim h
  | _, _, _, _, _, _ :: _, [], _, _, _, h => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _, h => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _, h => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [], h => False.elim h
  | _, _, _, _, _, _ :: Cs, _ :: Cs', _ :: Ys, _ :: Ys', _ :: certs, h =>
      have ih := driftWalk_len dn sn sd _ _ _ _ _ Cs Cs' Ys Ys' certs h.2
      ⟨congrArg (fun m => m + 1) ih.1, congrArg (fun m => m + 1) ih.2.1,
        congrArg (fun m => m + 1) ih.2.2.1,
        congrArg (fun m => m + 1) ih.2.2.2⟩

/-- The tied walk's fold-out: at an occupied certificate list the
walk caps the last step's deviation two-sidedly at the folded
pair over the walk's last block, the seed's geometric read joined
to the tie datum's fold over the steps' certificates. -/
theorem driftWalk_last (dn : BPair) (sn sd : Pos) :
    ∀ (Gs : List Mat) (cn cd : Pos) (Y0' Y0 : MatQ)
      (Cs Cs' Ys Ys' : List MatQ)
      (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
        × Split p.2 × Split p.2 × Split p.1 × Split p.1
        × Split p.2 × Split p.2 × Split p.2 × Split p.2)),
    driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs →
    0 < certs.length →
    ∃ (k : Nat) (spU spL : Split k),
      capQ (devQ (ground.getAt greenprod.dM Ys' (certs.length - 1))
          (ground.getAt greenprod.dM Ys (certs.length - 1)))
        (ground.getAt [] Gs certs.length)
        (driftFold cn cd sn sd certs).1 (driftFold cn cd sn sd certs).2
        spU spL
  | _, _, _, _, _, [], [], [], [], [], _, hocc =>
      absurd hocc (Nat.not_lt_zero 0)
  | _, _, _, _, _, [], [], [], [], _ :: _, h, _ => False.elim h
  | _, _, _, _, _, [], [], [], _ :: _, _, h, _ => False.elim h
  | _, _, _, _, _, [], [], _ :: _, _, _, h, _ => False.elim h
  | _, _, _, _, _, [], _ :: _, _, _, _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, [], _, _, _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, [], _, _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, [], _, h, _ => False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _, [], h, _ =>
      False.elim h
  | _, _, _, _, _, _ :: _, _ :: _, _ :: _, _ :: _,
      [⟨p, _, _, _, _, _, _, spU', spL', _, _⟩], h, _ =>
      ⟨p.2, spU', spL',
        capQ_double _ _ _ _ spU' spL' h.1.2.2.2.2.2⟩
  | Gs, _, _, _, _, _ :: Cs, _ :: Cs', Y1 :: Ys, Y1' :: Ys',
      cert :: c2 :: rest, h, _ => by
      have hrec := driftWalk_last dn sn sd (Gs.drop 1) _ _ Y1' Y1
        Cs Cs' Ys Ys' (c2 :: rest) h.2 (Nat.succ_pos rest.length)
      have e1 : ground.getAt greenprod.dM Ys' ((c2 :: rest).length - 1)
          = ground.getAt greenprod.dM (Y1' :: Ys')
              ((cert :: c2 :: rest).length - 1) := rfl
      have e2 : ground.getAt greenprod.dM Ys ((c2 :: rest).length - 1)
          = ground.getAt greenprod.dM (Y1 :: Ys)
              ((cert :: c2 :: rest).length - 1) := rfl
      have hadd : 1 + (c2 :: rest).length = (c2 :: rest).length + 1 :=
        (Nat.succ_add 0 (c2 :: rest).length).trans
          (congrArg Nat.succ (Nat.zero_add (c2 :: rest).length))
      have e3 : ground.getAt ([] : Mat) (Gs.drop 1) (c2 :: rest).length
          = ground.getAt ([] : Mat) Gs ((c2 :: rest).length + 1) :=
        (ground.getAt_drop ([] : Mat) 1 Gs (c2 :: rest).length).trans
          (congrArg (ground.getAt ([] : Mat) Gs) hadd)
      rw [e1, e2, e3] at hrec
      exact hrec

/-- The bundle's walk caps the depth-`j` pivot deviation
two-sidedly at the accumulated pair, `thm:groundreads`(iii)'s
bracket read at the observable's depth; the bridge from the
reversed walk's last place down to depth `j` reads the walk's own
list counts. -/
theorem driftShare_cap (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos) (Gs : List Mat)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2))
    (h : driftShareRead diag off diag' off' Xs Rs Xs' Rs'
      w0 j ns dn cn cd sn sd Gs certs)
    (hocc : 0 < certs.length) (hjw : j < w0) :
    ∃ (k : Nat) (spU spL : Split k),
      capQ (devQ (ground.getAt greenprod.dM Xs' j)
          (ground.getAt greenprod.dM Xs j))
        (ground.getAt [] Gs certs.length)
        (driftFold cn cd sn sd certs).1 (driftFold cn cd sn sd certs).2
        spU spL := by
  match certs, h, hocc with
  | c :: cs, h, _ =>
    have hw := h.2.2.2.2.2
    have hlen := driftWalk_len dn sn sd Gs cn cd
      (ground.getAt greenprod.dM Xs' w0) (ground.getAt greenprod.dM Xs w0)
      ((Rs.take w0).drop j).reverse ((Rs'.take w0).drop j).reverse
      ((Xs.take w0).drop j).reverse ((Xs'.take w0).drop j).reverse
      (c :: cs) hw
    have hlast := driftWalk_last dn sn sd Gs cn cd
      (ground.getAt greenprod.dM Xs' w0) (ground.getAt greenprod.dM Xs w0)
      ((Rs.take w0).drop j).reverse ((Rs'.take w0).drop j).reverse
      ((Xs.take w0).drop j).reverse ((Xs'.take w0).drop j).reverse
      (c :: cs) hw (Nat.succ_pos cs.length)
    have hl : ((Xs.take w0).drop j).length = cs.length + 1 :=
      (ground.length_reverse ((Xs.take w0).drop j)).symm.trans hlen.2.2.1
    have hl' : ((Xs'.take w0).drop j).length = cs.length + 1 :=
      (ground.length_reverse ((Xs'.take w0).drop j)).symm.trans
        hlen.2.2.2
    have eX : ground.getAt greenprod.dM ((Xs.take w0).drop j).reverse
        cs.length = ground.getAt greenprod.dM Xs j :=
      (ground.getAt_reverse greenprod.dM ((Xs.take w0).drop j)
        cs.length 0 hl.symm).trans
        ((ground.getAt_drop greenprod.dM j (Xs.take w0) 0).trans
          (ground.getAt_take greenprod.dM w0 Xs j hjw))
    have eX' : ground.getAt greenprod.dM ((Xs'.take w0).drop j).reverse
        cs.length = ground.getAt greenprod.dM Xs' j :=
      (ground.getAt_reverse greenprod.dM ((Xs'.take w0).drop j)
        cs.length 0 hl'.symm).trans
        ((ground.getAt_drop greenprod.dM j (Xs'.take w0) 0).trans
          (ground.getAt_take greenprod.dM w0 Xs' j hjw))
    obtain ⟨k, spU, spL, hc⟩ := hlast
    refine ⟨k, spU, spL, ?_⟩
    rw [← eX, ← eX']
    exact hc

/-! The ball's positivity: the center's floor with the deviation's
two-sided cap price a member's form at or above the sum's unit at
every vector, the three positive reads collected at one scaled
value identity over the form folds. -/

private theorem swap_scale (x : BPair) (w : Pos) :
    (x.scale w).swap = x.swap.scale w := rfl

private theorem pairNull (x : BPair) (w : Pos) :
    (x.swap.scale w + x.scale w).oneValue BPair.unit := by
  rw [← swap_scale]
  exact BPair.swap_add_null (BPair.oneValue_refl (x.scale w))

private theorem pairNull' (x : BPair) (w : Pos) :
    (x.scale w + x.swap.scale w).oneValue BPair.unit := by
  rw [BPair.add_comm]
  exact pairNull x w

private theorem posPb (X2 rd y0d : Pos) :
    X2 * rd * y0d = y0d * rd * X2 := by
  rw [ground.mul_right_comm X2 rd y0d, ground.mul_comm X2 y0d,
    ground.mul_right_comm y0d X2 rd]

private theorem posPc1 (rn X2 Yc2 y0d : Pos) :
    rn * (X2 * Yc2) * y0d = Yc2 * (rn * y0d) * X2 := by
  rw [← ground.mul_assoc rn X2 Yc2, ground.mul_right_comm rn X2 Yc2,
    ground.mul_right_comm (rn * Yc2) X2 y0d,
    ground.mul_right_comm rn Yc2 y0d, ground.mul_comm (rn * y0d) Yc2]

private theorem posPd (Yc2 y0n y0d rn rd X2 : Pos) :
    Yc2 * (y0n * rd + rn * y0d) * X2
      = Yc2 * (y0n * rd) * X2 + Yc2 * (rn * y0d) * X2 := by
  rw [ground.left_distrib Yc2 (y0n * rd) (rn * y0d),
    ground.right_distrib (Yc2 * (y0n * rd)) (Yc2 * (rn * y0d)) X2]

/-- The three scaled positive reads collect to the member's scaled
form: the center terms withdraw pairwise at the memberwise swap. -/
private theorem ballCombine (a b c : BPair)
    (X2 Yc2 y0n y0d rn rd : Pos) :
    ((c.scale (rn * (X2 * Yc2))
        + (a.scale Yc2 + b.swap.scale X2).scale rd).scale y0d
      + ((b.scale (y0d * rd)
          + (c.scale (Yc2 * (y0n * rd + rn * y0d))).swap).scale X2
        + c.scale (Yc2 * (y0n * rd) * X2))).oneValue
    (a.scale (Yc2 * rd * y0d)) := by
  rw [BPair.scale_add (a.scale Yc2) (b.swap.scale X2) rd,
    BPair.scale_scale a Yc2 rd, BPair.scale_scale b.swap X2 rd,
    BPair.scale_add (c.scale (rn * (X2 * Yc2)))
      (a.scale (Yc2 * rd) + b.swap.scale (X2 * rd)) y0d,
    BPair.scale_add (a.scale (Yc2 * rd)) (b.swap.scale (X2 * rd)) y0d,
    BPair.scale_scale c (rn * (X2 * Yc2)) y0d,
    BPair.scale_scale a (Yc2 * rd) y0d,
    BPair.scale_scale b.swap (X2 * rd) y0d,
    swap_scale c (Yc2 * (y0n * rd + rn * y0d)),
    BPair.scale_add (b.scale (y0d * rd))
      (c.swap.scale (Yc2 * (y0n * rd + rn * y0d))) X2,
    BPair.scale_scale b (y0d * rd) X2,
    BPair.scale_scale c.swap (Yc2 * (y0n * rd + rn * y0d)) X2,
    posPd Yc2 y0n y0d rn rd X2,
    ground.BPair.scale_addW c.swap (Yc2 * (y0n * rd) * X2) (Yc2 * (rn * y0d) * X2),
    posPb X2 rd y0d, posPc1 rn X2 Yc2 y0d]
  rw [BPair.add_left_comm (c.scale (Yc2 * (rn * y0d) * X2))
      (a.scale (Yc2 * rd * y0d)) (b.swap.scale (y0d * rd * X2)),
    BPair.add_assoc (a.scale (Yc2 * rd * y0d))
      (c.scale (Yc2 * (rn * y0d) * X2) + b.swap.scale (y0d * rd * X2))
      (b.scale (y0d * rd * X2)
        + (c.swap.scale (Yc2 * (y0n * rd) * X2)
          + c.swap.scale (Yc2 * (rn * y0d) * X2))
        + c.scale (Yc2 * (y0n * rd) * X2)),
    BPair.add_comm (c.swap.scale (Yc2 * (y0n * rd) * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2)),
    ← BPair.add_assoc (b.scale (y0d * rd * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2))
      (c.swap.scale (Yc2 * (y0n * rd) * X2)),
    BPair.add_assoc
      (b.scale (y0d * rd * X2) + c.swap.scale (Yc2 * (rn * y0d) * X2))
      (c.swap.scale (Yc2 * (y0n * rd) * X2))
      (c.scale (Yc2 * (y0n * rd) * X2)),
    ← BPair.add_assoc
      (c.scale (Yc2 * (rn * y0d) * X2) + b.swap.scale (y0d * rd * X2))
      (b.scale (y0d * rd * X2) + c.swap.scale (Yc2 * (rn * y0d) * X2))
      (c.swap.scale (Yc2 * (y0n * rd) * X2)
        + c.scale (Yc2 * (y0n * rd) * X2)),
    BPair.add_comm (b.scale (y0d * rd * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2)),
    BPair.add_add_comm (c.scale (Yc2 * (rn * y0d) * X2))
      (b.swap.scale (y0d * rd * X2))
      (c.swap.scale (Yc2 * (rn * y0d) * X2))
      (b.scale (y0d * rd * X2))]
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_refl (a.scale (Yc2 * rd * y0d)))
    (BPair.oneValue_trans (BPair.add_congr
      (BPair.oneValue_trans (BPair.add_congr
        (pairNull' c (Yc2 * (rn * y0d) * X2))
        (pairNull b (y0d * rd * X2)))
        (BPair.unit_add BPair.unit))
      (pairNull c (Yc2 * (y0n * rd) * X2)))
      (BPair.unit_add BPair.unit))) ?_
  exact BPair.add_unit (a.scale (Yc2 * rd * y0d))

private theorem rowsLen_unmapScale (w : Pos) (n : Nat) : ∀ M : Mat,
    rowsLen n (matScale w M) → rowsLen n M
  | [], _ => trivial
  | r :: t, h =>
    ⟨(ground.length_map _ r).symm.trans h.1,
     rowsLen_unmapScale w n t h.2⟩

/-- The gram's positive read off the cap alone: the two split
reads' forms join, the deviation withdrawing at the memberwise
swap, so the gram's form sits at or above the sum's unit at every
vector. -/
private theorem gramLe {o : Nat} (X Yc : MatQ) (G : Mat)
    (rn rd : Pos) (spU spL : Split o)
    (hcap : capQ (devQ X Yc) G rn rd spU spL)
    (u : List BPair) (hu : u.length = o) :
    BPair.unit ≤ quadForm G u := by
  have hSl : (matScale rd (devQ X Yc).1).length = u.length := by
    rw [hu]; exact sqAt_len hcap.1
  have hSr : rowsLen u.length (matScale rd (devQ X Yc).1) := by
    rw [hu]; exact rowsLen_of_sqAt hcap.1
  have hCl : (matScale (rn * (devQ X Yc).2) G).length = u.length := by
    rw [hu]; exact sqAt_len hcap.2.1
  have hCr : rowsLen u.length (matScale (rn * (devQ X Yc).2) G) := by
    rw [hu]; exact rowsLen_of_sqAt hcap.2.1
  have h1 : BPair.unit ≤ quadForm
      (siteDatum (matScale (rn * (devQ X Yc).2) G)
        (matScale rd (devQ X Yc).1)) u :=
    ground.leB_of_not_lt
      (psd_all _ spU hcap.2.2.1 hcap.2.2.2.1 u hu)
  have h2 : BPair.unit ≤ quadForm
      (matAdd (matScale (rn * (devQ X Yc).2) G)
        (matScale rd (devQ X Yc).1)) u :=
    ground.leB_of_not_lt
      (psd_all _ spL hcap.2.2.2.2.1 hcap.2.2.2.2.2 u hu)
  have e1 : (quadForm (siteDatum (matScale (rn * (devQ X Yc).2) G)
      (matScale rd (devQ X Yc).1)) u).oneValue
      (quadForm (matScale (rn * (devQ X Yc).2) G) u
        + (quadForm (matScale rd (devQ X Yc).1) u).swap) := by
    refine BPair.oneValue_trans
      (quadForm_add (matScale (rn * (devQ X Yc).2) G)
        (matSwap (matScale rd (devQ X Yc).1)) u hCl hCr
        ((length_matSwap _).trans hSl)
        (rowsLen_mapRows BPair.swap _ _ hSr)) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (quadForm_swap (matScale rd (devQ X Yc).1) u)
  have e2 : (quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
      (matScale rd (devQ X Yc).1)) u).oneValue
      (quadForm (matScale (rn * (devQ X Yc).2) G) u
        + quadForm (matScale rd (devQ X Yc).1) u) :=
    quadForm_add _ _ u hCl hCr hSl hSr
  have hsum : BPair.unit ≤
      (quadForm G u).scale (rn * (devQ X Yc).2)
        + (quadForm G u).scale (rn * (devQ X Yc).2) := by
    refine ground.leB_congr_right ?_ (ground.unitLeAdd h1 h2)
    refine BPair.oneValue_trans (BPair.add_congr e1 e2) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq
      (BPair.add_add_comm
        (quadForm (matScale (rn * (devQ X Yc).2) G) u)
        ((quadForm (matScale rd (devQ X Yc).1) u).swap)
        (quadForm (matScale (rn * (devQ X Yc).2) G) u)
        (quadForm (matScale rd (devQ X Yc).1) u))) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.add_congr (quadForm_scale (rn * (devQ X Yc).2) G u)
        (quadForm_scale (rn * (devQ X Yc).2) G u))
      (BPair.swap_add_null (BPair.oneValue_refl
        (quadForm (matScale rd (devQ X Yc).1) u)))) ?_
    exact BPair.add_unit _
  exact ground.unitLeOfScale (ground.leB_congr_right
    (BPair.oneValue_of_eq (ground.BPair.scale_addW (quadForm G u)
      (rn * (devQ X Yc).2) (rn * (devQ X Yc).2)).symm) hsum)

/-- A ball member's every split reads the upper side: the center's
floor with the deviation's two-sided cap price the member's form at
or above the sum's unit at every vector, so an occupied count's
witness is refused; the center's shape is the frame, the consumers'
own pivot read, and the gram's positivity is the cap's own
(`gramLe`). -/
theorem ball_psd {o : Nat} (X Yc : MatQ) (G : Mat)
    (y0n y0d rn rd : Pos) (spF spU spL sp : Split o)
    (hYc : sqAt Yc.1 o)
    (hF : floorRead Yc G y0n y0d rn rd spF)
    (hcap : capQ (devQ X Yc) G rn rd spU spL)
    (hsp : splitRead X.1 sp) : psdAt sp := by
  cases Nat.eq_zero_or_pos (revAt sp) with
  | inl h0 => exact h0
  | inr hpos =>
    obtain ⟨u, hu, hlt⟩ := rev_witness X.1 sp hsp hpos
    have hXl : X.1.length = u.length := by rw [hu]; exact sqAt_len hsp.1
    have hXr : rowsLen u.length X.1 := by
      rw [hu]; exact rowsLen_of_sqAt hsp.1
    have hYl : Yc.1.length = u.length := by rw [hu]; exact sqAt_len hYc
    have hYr : rowsLen u.length Yc.1 := by
      rw [hu]; exact rowsLen_of_sqAt hYc
    have hGsq : sqAt G o :=
      sqAt_of ((length_matScale (rn * (devQ X Yc).2) G).symm.trans
          (sqAt_len hcap.2.1))
        (rowsLen_unmapScale (rn * (devQ X Yc).2) o G
          (rowsLen_of_sqAt hcap.2.1))
    have hGl : G.length = u.length := by rw [hu]; exact sqAt_len hGsq
    have hGr : rowsLen u.length G := by
      rw [hu]; exact rowsLen_of_sqAt hGsq
    have hDl : (devQ X Yc).1.length = u.length := by
      show (matAdd (matScale Yc.2 X.1)
        (matScale X.2 (matSwap Yc.1))).length = u.length
      rw [length_matAdd (matScale Yc.2 X.1)
          (matScale X.2 (matSwap Yc.1))
          ((length_matScale Yc.2 X.1).trans (hXl.trans
            (((length_matScale X.2 (matSwap Yc.1)).trans
              ((length_matSwap Yc.1).trans hYl)).symm))),
        length_matScale]
      exact hXl
    have hDr : rowsLen u.length (devQ X Yc).1 := by
      show rowsLen u.length (matAdd (matScale Yc.2 X.1)
        (matScale X.2 (matSwap Yc.1)))
      exact rowsLen_matAdd u.length _ _
        (rowsLen_mapRows (fun x => x.scale Yc.2) X.1 u.length hXr)
        (rowsLen_mapRows (fun x => x.scale X.2) (matSwap Yc.1)
          u.length (rowsLen_mapRows BPair.swap Yc.1 u.length hYr))
    have hle1 : BPair.unit ≤ quadForm
        (matAdd (matScale (rn * (devQ X Yc).2) G)
          (matScale rd (devQ X Yc).1)) u :=
      ground.leB_of_not_lt
        (psd_all _ spL hcap.2.2.2.2.1 hcap.2.2.2.2.2 u hu)
    have hle2 : BPair.unit ≤ quadForm
        (siteDatum (matScale (y0d * rd) Yc.1)
          (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u :=
      ground.leB_of_not_lt (psd_all _ spF hF.1 hF.2 u hu)
    have hle3 : BPair.unit ≤ quadForm G u :=
      gramLe X Yc G rn rd spU spL hcap u hu
    have eDev : (quadForm (devQ X Yc).1 u).oneValue
        ((quadForm X.1 u).scale Yc.2
          + ((quadForm Yc.1 u).swap).scale X.2) := by
      refine BPair.oneValue_trans
        (quadForm_add (matScale Yc.2 X.1)
          (matScale X.2 (matSwap Yc.1)) u
          ((length_matScale Yc.2 X.1).trans hXl)
          (rowsLen_mapRows (fun x => x.scale Yc.2) X.1 u.length hXr)
          ((length_matScale X.2 (matSwap Yc.1)).trans
            ((length_matSwap Yc.1).trans hYl))
          (rowsLen_mapRows (fun x => x.scale X.2) (matSwap Yc.1)
            u.length (rowsLen_mapRows BPair.swap Yc.1 u.length hYr))) ?_
      exact BPair.add_congr (quadForm_scale Yc.2 X.1 u)
        (BPair.oneValue_trans (quadForm_scale X.2 (matSwap Yc.1) u)
          (BPair.scale_congr X.2 (quadForm_swap Yc.1 u)))
    have eCap : (quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
        (matScale rd (devQ X Yc).1)) u).oneValue
        ((quadForm G u).scale (rn * (X.2 * Yc.2))
          + ((quadForm X.1 u).scale Yc.2
            + ((quadForm Yc.1 u).swap).scale X.2).scale rd) := by
      refine BPair.oneValue_trans
        (quadForm_add (matScale (rn * (devQ X Yc).2) G)
          (matScale rd (devQ X Yc).1) u
          ((length_matScale (rn * (devQ X Yc).2) G).trans hGl)
          (rowsLen_mapRows (fun x => x.scale (rn * (devQ X Yc).2)) G
            u.length hGr)
          ((length_matScale rd (devQ X Yc).1).trans hDl)
          (rowsLen_mapRows (fun x => x.scale rd) (devQ X Yc).1
            u.length hDr)) ?_
      exact BPair.add_congr
        (quadForm_scale (rn * (X.2 * Yc.2)) G u)
        (BPair.oneValue_trans (quadForm_scale rd (devQ X Yc).1 u)
          (BPair.scale_congr rd eDev))
    have eFloor : (quadForm (siteDatum (matScale (y0d * rd) Yc.1)
        (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u).oneValue
        ((quadForm Yc.1 u).scale (y0d * rd)
          + ((quadForm G u).scale
              (Yc.2 * (y0n * rd + rn * y0d))).swap) := by
      refine BPair.oneValue_trans
        (quadForm_add (matScale (y0d * rd) Yc.1)
          (matSwap (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u
          ((length_matScale (y0d * rd) Yc.1).trans hYl)
          (rowsLen_mapRows (fun x => x.scale (y0d * rd)) Yc.1
            u.length hYr)
          ((length_matSwap _).trans
            ((length_matScale (Yc.2 * (y0n * rd + rn * y0d)) G).trans
              hGl))
          (rowsLen_mapRows BPair.swap _ u.length
            (rowsLen_mapRows (fun x => x.scale
              (Yc.2 * (y0n * rd + rn * y0d))) G u.length hGr))) ?_
      exact BPair.add_congr (quadForm_scale (y0d * rd) Yc.1 u)
        (BPair.oneValue_trans
          (quadForm_swap (matScale (Yc.2 * (y0n * rd + rn * y0d)) G) u)
          (ground.swap_congr
            (quadForm_scale (Yc.2 * (y0n * rd + rn * y0d)) G u)))
    have hT : BPair.unit ≤
        (quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
            (matScale rd (devQ X Yc).1)) u).scale y0d
        + ((quadForm (siteDatum (matScale (y0d * rd) Yc.1)
            (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u).scale X.2
          + (quadForm G u).scale (Yc.2 * (y0n * rd) * X.2)) :=
      ground.unitLeAdd (ground.unitLeScale y0d hle1)
        (ground.unitLeAdd (ground.unitLeScale X.2 hle2)
          (ground.unitLeScale (Yc.2 * (y0n * rd) * X.2) hle3))
    have eT : ((quadForm (matAdd (matScale (rn * (devQ X Yc).2) G)
            (matScale rd (devQ X Yc).1)) u).scale y0d
        + ((quadForm (siteDatum (matScale (y0d * rd) Yc.1)
            (matScale (Yc.2 * (y0n * rd + rn * y0d)) G)) u).scale X.2
          + (quadForm G u).scale (Yc.2 * (y0n * rd) * X.2))).oneValue
        ((quadForm X.1 u).scale (Yc.2 * rd * y0d)) := by
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.scale_congr y0d eCap)
        (BPair.add_congr (BPair.scale_congr X.2 eFloor)
          (BPair.oneValue_refl _))) ?_
      exact ballCombine (quadForm X.1 u) (quadForm Yc.1 u)
        (quadForm G u) X.2 Yc.2 y0n y0d rn rd
    exact absurd (ground.scaleLtUnit (Yc.2 * rd * y0d) hlt)
      (ground.leB_not_lt (ground.leB_congr_right eT hT))

end spectator
