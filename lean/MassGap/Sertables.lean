import MassGap.Gentable
import MassGap.Elim
import MassGap.Units
import MassGap.Inertia
/-!
`con:sertables` — the member weight tables, the instantiations
filling `con:gentable`'s fields.  The series' tables are functions
of the rank: the displayed simple data evaluate to the Cartan rows
(`B` with the short last key at the doubled edge toward it, `C` its
mirror, `D` the fork at the last two keys), the length lists read
the displayed form scales, and the positive lists enter at the
displayed family folds — the difference, sum and short or long
families — with the highest root the stated family's first member.
The fixed members enter at their simple keys: the Cartan rows off
the displayed edge lists (`G_2` and `F_4` at their displayed
doubled edges), the length lists the displayed data, `G_2`'s six
folds displayed outright, and `F_4`'s and the `E`-members' positive
lists the displayed coordinate families (the doubled-coordinate
realizations, `E_7` and `E_6` the balance-partner selections of
`E_8`'s list) read to their natural folds by the fold descent, the
walk at a positive-dot simple key with the fold witness collected
along it, `famRead` the naming identity's round trip
(`foldCoords` returning the member) joined to the root fold's
coroot reads at one fold list; the `E`-members' fold lists are the
committed literals (`posE6`, `posE7`, `posE8`), each the descent's
own output at its certifying equation in the check module.  The adjugate rows are the
five displayed matrices at their fold keys, `adjRead` the coroot
witness `Σ_k a_ik α_k(α_j^∨) = e δ_ij` and `thetaRowRead` the
θ-fold row's `e`-multiple.  The derived residues are
`gentable.residue`'s reads, the residue folds pinned per member in
the check module; the reflection permutation, the Weyl list and the
grading land with the alternant layer.  The defining tables enter
at their key encodings — the paired keys with `B`'s further null
key — the simple raisings and lowerings the displayed unit moves at
the form's twist (`B`'s short pair through the null key at the
cleared weights), each triple display one read (`tripleRead`, the
weighted transpose joined to the commutator displays at the coroot
diagonal), and the invariant count the stacked raisings' kernel
over the unit-content monomials (`invCountB` and its partners,
`prop:wg` the pairing's consumer).  The coordinate tier closes the
construction at the coroot presentation: `FundData` carries the
fundamentals' cleared Gram with its scale, the simple members'
positions in the positive list and the reflections' permutations
of it, and the reads pin them — the shape conjuncts, the Gram's
defining read against the Cartan rows with its symmetry, the
simple positions, the involution reads at the reflection matrices
and at the permutation data, the form-keeping read, the
permutation of the positive list, the `ρ`-dot positivity, and the
graded image list's own shape at the keys —
the reflection matrices off the Cartan rows at `con:gentable`'s
reflection join, the split certificates at `inertia`'s own reads
in the check module.
-/

namespace sertables
open ground gentable

/-! The series' fold families, functions of the rank: the occupancy
window `ind l a b`, one on the keys of `[a, b)`, is the families'
one constructor. -/

/-- The occupancy window: one on the keys of `[a, b)`, the fold
families' one constructor. -/
def ind (l a b : Nat) : List Nat :=
  (List.range l).map (fun k => if a ≤ k && k < b then 1 else 0)

private def addN (v w : List Nat) : List Nat :=
  List.zipWith (fun a b => a + b) v w

private def two (v : List Nat) : List Nat := addN v v

/-- The difference family, one at the keys between the pair. -/
def diffFold (l a b : Nat) : List Nat := ind l a b

/-- The `B` sum family: one on `[a, b)`, two on `[b, l)`. -/
def sumFoldB (l a b : Nat) : List Nat := addN (ind l a b) (two (ind l b l))

/-- The `B` short family: one on `[a, l)`. -/
def shortFold (l a : Nat) : List Nat := ind l a l

/-- The `C` sum family: one on `[a, b)`, two on `[b, l-1)`, one at
the last key. -/
def sumFoldC (l a b : Nat) : List Nat :=
  addN (ind l a b) (addN (two (ind l b (l - 1))) (ind l (l - 1) l))

/-- The `C` long family: two on `[a, l-1)`, one at the last key. -/
def longFold (l a : Nat) : List Nat :=
  addN (two (ind l a (l - 1))) (ind l (l - 1) l)

/-- The `D` sum family at a coordinate pair: the generic member one
on `[a, b)`, two on `[b, l-2)`, one on the last two keys, and the
last-coordinate member one on `[a, l-2)` with one on the last
key. -/
def sumFoldD (l a b : Nat) : List Nat :=
  if b + 1 == l then addN (ind l a (l - 2)) (ind l (l - 1) l)
  else
    addN (ind l a b) (addN (two (ind l b (l - 2))) (ind l (l - 2) l))

/-- The `B` positive list at its folds. -/
def foldsB (l : Nat) : List (List Nat) :=
  (places.pairsOf l).map (fun p => diffFold l p.1 p.2)
    ++ (places.pairsOf l).map (fun p => sumFoldB l p.1 p.2)
    ++ (List.range l).map (shortFold l)

/-- The `C` positive list at its folds. -/
def foldsC (l : Nat) : List (List Nat) :=
  (places.pairsOf l).map (fun p => diffFold l p.1 p.2)
    ++ (places.pairsOf l).map (fun p => sumFoldC l p.1 p.2)
    ++ (List.range l).map (longFold l)

/-- The `D` positive list at its folds. -/
def foldsD (l : Nat) : List (List Nat) :=
  (places.pairsOf l).map (fun p => diffFold l p.1 p.2)
    ++ (places.pairsOf l).map (fun p => sumFoldD l p.1 p.2)

/-! The series' Cartan rows, the displayed coroot formulas at the
displayed simples. -/

private def b2 : BPair := BPair.ofNat 2
private def m1 : BPair := (BPair.ofNat 1).swap
private def m2 : BPair := (BPair.ofNat 2).swap
private def m3 : BPair := (BPair.ofNat 3).swap

/-- The `B` Cartan rows: the chain at the doubled edge into the
short last key. -/
def cartanB (l : Nat) : List (List BPair) :=
  ground.matOf l l (fun i j =>
    if j == i then b2
    else if i + 2 == l && j == i + 1 then m2
    else if j + 1 == i || j == i + 1 then m1
    else BPair.unit)

/-- The `C` Cartan rows: the chain at the doubled edge out of the
long last key. -/
def cartanC (l : Nat) : List (List BPair) :=
  ground.matOf l l (fun i j =>
    if j == i then b2
    else if i + 1 == l && j + 2 == l then m2
    else if j + 1 == i || j == i + 1 then m1
    else BPair.unit)

/-- The `D` Cartan rows: the fork, the last two keys joined to the
key before them and off each other. -/
def cartanD (l : Nat) : List (List BPair) :=
  ground.matOf l l (fun i j =>
    if j == i then b2
    else if i + 1 == l then (if j + 3 == l then m1 else BPair.unit)
    else if j + 1 == l then (if i + 3 == l then m1 else BPair.unit)
    else if j + 1 == i || j == i + 1 then m1
    else BPair.unit)

private def lensB (l : Nat) : List Nat :=
  (List.range l).map (fun i => if i + 1 == l then 1 else 2)

private def lensC (l : Nat) : List Nat :=
  (List.range l).map (fun i => if i + 1 == l then 2 else 1)

/-- The `B` member's table at the rank. -/
def tableB (l : Nat) : Table :=
  ⟨l, lensB l, 1, cartanB l, foldsB l, sumFoldB l 0 1⟩

/-- The `C` member's table at the rank. -/
def tableC (l : Nat) : Table :=
  ⟨l, lensC l, 1, cartanC l, foldsC l, longFold l 0⟩

/-- The `D` member's table at the rank. -/
def tableD (l : Nat) : Table :=
  ⟨l, List.replicate l 2, 1, cartanD l, foldsD l, sumFoldD l 0 1⟩

/-! The fixed members' coordinate families and the fold descent. -/

private def isPosB (x : BPair) : Bool :=
  match x.side with
  | .gt _ _ => true
  | .lt _ _ => false
  | .eq _ => false

private def eqB (x y : BPair) : Bool :=
  if x.oneValue y then true else false

private def allUnit : List BPair → Bool
  | [] => true
  | a :: t => a.isUnitRep && allUnit t

private def findPosIdx : List BPair → Nat → Option Nat
  | [], _ => none
  | a :: t, k => if isPosB a then some k else findPosIdx t (k + 1)

private def subRow (v w : List BPair) : List BPair :=
  List.zipWith (fun a b => (a + b.swap).norm) v w

private def descGo (g : List (List BPair)) :
    Nat → List BPair → List Nat → List Nat
  | 0, dv, acc => if allUnit dv then acc else []
  | fuel + 1, dv, acc =>
    if allUnit dv then acc
    else
      match findPosIdx dv 0 with
      | some j => descGo g fuel (subRow dv (getAt [] g j)) (bumpAt j acc)
      | none => []

/-- The fold descent (`con:sertables`' fixed-member walk), run for
the whole family at one Gram read: the walk's state is the member's
dot list against the simples, a step subtracts the positive-dot
key's Gram row and collects the fold witness, and the walk closes
at the unit reads, the last step the ending simple's own key (the
simples' mutual dots off the diagonal sit at or below the unit, so
a simple's one positive read is its own); a starved or stuck walk's
output is caught by `descentRead`'s round trip. -/
def descentAll (simples : List (List BPair)) (fuel : Nat)
    (fam : List (List BPair)) : List (List Nat) :=
  let g := simples.map (fun s => simples.map (fun s' => elim.dotN s s'))
  fam.map (fun v =>
    descGo g fuel (simples.map (fun s => elim.dotN v s))
      (simples.map (fun _ => 0)))

/-- A fold's coordinate content, `Σ_k f_k α_k` at the coordinate
simples. -/
def foldCoords (simples : List (List BPair)) (f : List Nat) :
    List BPair :=
  match simples with
  | [] => []
  | s :: _ =>
    (List.zipWith (fun c => elim.vecScale (BPair.ofNat c)) f simples).foldl
      elim.vecAdd (s.map (fun _ => BPair.unit))

/-- The family read at one traversal, the table's own positive
list against the displayed coordinate family, three reads off one
forcing: the counts agree, every stored fold reads back to its
family member through `foldCoords` (the descent's round trip, the
fold witness's whole verification), and the root fold's coroot
reads `(2ρ)(α_i^∨) = 2` hold at every simple index — the round
trip carries each fold's key count beside it (`foldCoords` reads
the fold against the simples at matched keys alone), and a fold of
the unit family refuses at the round trip against its occupied
member, so the occupancy and shape clauses ride the same read. -/
def famRead (t : Table) (simples fam : List (List BPair)) : Prop :=
  (let folds := t.posFolds
   (folds.length == fam.length)
     && ((List.zipWith (fun f v =>
       decide (ground.matchedOV ground.bpairRead
         (foldCoords simples f) v) && f.length == t.rank)
       folds fam).all (fun b => b))
     && ((List.range t.rank).all (fun j =>
       if (BPair.sum (folds.map (fun f => corootAt t f j))).oneValue
           (BPair.ofNat 2)
       then true else false))) = true

instance (t : Table) (s fam : List (List BPair)) :
    Decidable (famRead t s fam) :=
  inferInstanceAs (Decidable (_ = _))

private def pB (n : Nat) : BPair := BPair.ofNat n
private def mB (n : Nat) : BPair := (BPair.ofNat n).swap

/-- The three `E`-members' shared eight doubled coordinates: the
displayed simple list, `α_1` at the first and eighth keys against
the six between, `α_2` two on the first two keys, and the
letter-pair moves. -/
def e8Simples : List (List BPair) :=
  [pB 1, mB 1, mB 1, mB 1, mB 1, mB 1, mB 1, pB 1]
    :: [pB 2, pB 2, BPair.unit, BPair.unit, BPair.unit, BPair.unit,
        BPair.unit, BPair.unit]
    :: ground.matOf 6 8 (fun k j =>
        if j == k then m2 else if j == k + 1 then b2 else BPair.unit)

/-- The `E_8` coordinate families: the difference, sum and half-sum
families at the displayed counts `28 + 28 + 64`. -/
def e8Family : List (List BPair) :=
  (places.pairsOf 8).map (fun p => (List.range 8).map (fun j =>
      if j == p.1 then m2 else if j == p.2 then b2 else BPair.unit))
    ++ (places.pairsOf 8).map (fun p => (List.range 8).map (fun j =>
        if j == p.1 || j == p.2 then b2 else BPair.unit))
    ++ (List.range 128).filterMap (fun n =>
        let v := (List.range 7).map (fun k =>
          if n / 2 ^ k % 2 == 1 then mB 1 else pB 1)
        if (v.filter (fun x => eqB x (mB 1))).length % 2 == 0 then
          some (v ++ [pB 1])
        else none)

/-- A member's read at the `E_7` selection, the seventh and eighth
entries' sum of equal members. -/
def selE7 (v : List BPair) : Bool :=
  eqB (getAt BPair.unit v 6 + getAt BPair.unit v 7) BPair.unit

/-- A member's read at the further `E_6` selection, the sixth and
eighth entries' sum of equal members as well. -/
def selE6 (v : List BPair) : Bool :=
  selE7 v && eqB (getAt BPair.unit v 5 + getAt BPair.unit v 7) BPair.unit

/-- The `F_4` displayed coordinates: four keys at the doubled
scale, the simple list as displayed. -/
def f4Simples : List (List BPair) :=
  [[BPair.unit, b2, m2, BPair.unit],
   [BPair.unit, BPair.unit, b2, m2],
   [BPair.unit, BPair.unit, BPair.unit, b2],
   [pB 1, mB 1, mB 1, mB 1]]

/-- The `F_4` coordinate families: the singles, the difference and
sum family, and the half-sums, at the displayed counts
`4 + 12 + 8`. -/
def f4Family : List (List BPair) :=
  ground.matOf 4 4 (fun a j => if j == a then b2 else BPair.unit)
    ++ (places.pairsOf 4).flatMap (fun p =>
        [(List.range 4).map (fun j =>
            if j == p.1 then b2 else if j == p.2 then m2 else BPair.unit),
         (List.range 4).map (fun j =>
            if j == p.1 || j == p.2 then b2 else BPair.unit)])
    ++ (List.range 8).map (fun n =>
        pB 1 :: (List.range 3).map (fun k =>
          if n / 2 ^ k % 2 == 1 then mB 1 else pB 1))

/-- The `E`-members' edge lists, the chain `1–3–4–5–6` with the
branch `2–4`, grown by `7` and by `7–8`. -/
def slCartan (n : Nat) (edges : List (Nat × Nat)) :
    List (List BPair) :=
  ground.matOf n n (fun i j =>
    if j == i then b2
    else if edges.any (fun e =>
        (e.1 == i && e.2 == j) || (e.1 == j && e.2 == i)) then m1
    else BPair.unit)

def edgesE6 : List (Nat × Nat) := [(0, 2), (2, 3), (3, 4), (4, 5), (1, 3)]
def edgesE7 : List (Nat × Nat) := edgesE6 ++ [(5, 6)]
def edgesE8 : List (Nat × Nat) := edgesE7 ++ [(6, 7)]

/-- The `G_2` table: the displayed edge reads, lengths `[2:3]` and
`2` at the cleared second member three, and the six displayed
folds. -/
def tableG2 : Table :=
  ⟨2, [2, 6], 3, [[b2, m1], [m3, b2]],
   [[1, 0], [0, 1], [1, 1], [2, 1], [3, 1], [3, 2]], [3, 2]⟩

/-- The `F_4` table: the chain at the middle edge doubled toward
the short pair, the displayed lengths, and the positive list the
coordinate families' descent. -/
def tableF4 : Table :=
  ⟨4, [2, 2, 1, 1], 1,
   [[b2, m1, BPair.unit, BPair.unit],
    [m1, b2, m2, BPair.unit],
    [BPair.unit, m1, b2, m1],
    [BPair.unit, BPair.unit, m1, b2]],
   descentAll f4Simples 32 f4Family, [2, 3, 4, 2]⟩

/-- The `E_6` positive list at its simple folds, the descent's output committed literal. -/
def posE6 : List (List Nat) :=
  [[0,0,1,0,0,0], [0,0,1,1,0,0], [0,0,0,1,0,0], [0,0,1,1,1,0],
   [0,0,0,1,1,0], [0,0,0,0,1,0], [0,0,1,1,1,1], [0,0,0,1,1,1],
   [0,0,0,0,1,1], [0,0,0,0,0,1], [0,1,0,0,0,0], [0,1,0,1,0,0],
   [0,1,1,1,0,0], [0,1,0,1,1,0], [0,1,1,1,1,0], [0,1,1,2,1,0],
   [0,1,0,1,1,1], [0,1,1,1,1,1], [0,1,1,2,1,1], [0,1,1,2,2,1],
   [1,2,2,3,2,1], [1,1,2,3,2,1], [1,1,2,2,2,1], [1,1,1,2,2,1],
   [1,1,2,2,1,1], [1,1,1,2,1,1], [1,1,1,1,1,1], [1,0,1,1,1,1],
   [1,1,2,2,1,0], [1,1,1,2,1,0], [1,1,1,1,1,0], [1,0,1,1,1,0],
   [1,1,1,1,0,0], [1,0,1,1,0,0], [1,0,1,0,0,0], [1,0,0,0,0,0]]

/-- The `E_7` positive list at its simple folds, the descent's output committed literal. -/
def posE7 : List (List Nat) :=
  [[0,0,1,0,0,0,0], [0,0,1,1,0,0,0], [0,0,0,1,0,0,0], [0,0,1,1,1,0,0],
   [0,0,0,1,1,0,0], [0,0,0,0,1,0,0], [0,0,1,1,1,1,0], [0,0,0,1,1,1,0],
   [0,0,0,0,1,1,0], [0,0,0,0,0,1,0], [0,0,1,1,1,1,1], [0,0,0,1,1,1,1],
   [0,0,0,0,1,1,1], [0,0,0,0,0,1,1], [0,0,0,0,0,0,1], [2,2,3,4,3,2,1],
   [0,1,0,0,0,0,0], [0,1,0,1,0,0,0], [0,1,1,1,0,0,0], [0,1,0,1,1,0,0],
   [0,1,1,1,1,0,0], [0,1,1,2,1,0,0], [0,1,0,1,1,1,0], [0,1,1,1,1,1,0],
   [0,1,1,2,1,1,0], [0,1,1,2,2,1,0], [0,1,0,1,1,1,1], [0,1,1,1,1,1,1],
   [0,1,1,2,1,1,1], [0,1,1,2,2,1,1], [0,1,1,2,2,2,1], [1,2,3,4,3,2,1],
   [1,2,2,4,3,2,1], [1,2,2,3,3,2,1], [1,1,2,3,3,2,1], [1,2,2,3,2,2,1],
   [1,1,2,3,2,2,1], [1,1,2,2,2,2,1], [1,1,1,2,2,2,1], [1,2,2,3,2,1,1],
   [1,1,2,3,2,1,1], [1,1,2,2,2,1,1], [1,1,1,2,2,1,1], [1,1,2,2,1,1,1],
   [1,1,1,2,1,1,1], [1,1,1,1,1,1,1], [1,0,1,1,1,1,1], [1,2,2,3,2,1,0],
   [1,1,2,3,2,1,0], [1,1,2,2,2,1,0], [1,1,1,2,2,1,0], [1,1,2,2,1,1,0],
   [1,1,1,2,1,1,0], [1,1,1,1,1,1,0], [1,0,1,1,1,1,0], [1,1,2,2,1,0,0],
   [1,1,1,2,1,0,0], [1,1,1,1,1,0,0], [1,0,1,1,1,0,0], [1,1,1,1,0,0,0],
   [1,0,1,1,0,0,0], [1,0,1,0,0,0,0], [1,0,0,0,0,0,0]]

/-- The `E_8` positive list at its simple folds, the descent's output committed literal. -/
def posE8 : List (List Nat) :=
  [[0,0,1,0,0,0,0,0], [0,0,1,1,0,0,0,0], [0,0,0,1,0,0,0,0],
   [0,0,1,1,1,0,0,0], [0,0,0,1,1,0,0,0], [0,0,0,0,1,0,0,0],
   [0,0,1,1,1,1,0,0], [0,0,0,1,1,1,0,0], [0,0,0,0,1,1,0,0],
   [0,0,0,0,0,1,0,0], [0,0,1,1,1,1,1,0], [0,0,0,1,1,1,1,0],
   [0,0,0,0,1,1,1,0], [0,0,0,0,0,1,1,0], [0,0,0,0,0,0,1,0],
   [0,0,1,1,1,1,1,1], [0,0,0,1,1,1,1,1], [0,0,0,0,1,1,1,1],
   [0,0,0,0,0,1,1,1], [0,0,0,0,0,0,1,1], [0,0,0,0,0,0,0,1],
   [2,2,4,5,4,3,2,1], [2,2,3,5,4,3,2,1], [2,2,3,4,4,3,2,1],
   [2,2,3,4,3,3,2,1], [2,2,3,4,3,2,2,1], [2,2,3,4,3,2,1,1],
   [2,2,3,4,3,2,1,0], [0,1,0,0,0,0,0,0], [0,1,0,1,0,0,0,0],
   [0,1,1,1,0,0,0,0], [0,1,0,1,1,0,0,0], [0,1,1,1,1,0,0,0],
   [0,1,1,2,1,0,0,0], [0,1,0,1,1,1,0,0], [0,1,1,1,1,1,0,0],
   [0,1,1,2,1,1,0,0], [0,1,1,2,2,1,0,0], [0,1,0,1,1,1,1,0],
   [0,1,1,1,1,1,1,0], [0,1,1,2,1,1,1,0], [0,1,1,2,2,1,1,0],
   [0,1,1,2,2,2,1,0], [0,1,0,1,1,1,1,1], [0,1,1,1,1,1,1,1],
   [0,1,1,2,1,1,1,1], [0,1,1,2,2,1,1,1], [0,1,1,2,2,2,1,1],
   [0,1,1,2,2,2,2,1], [2,3,3,5,4,3,2,1], [2,3,4,5,4,3,2,1],
   [2,3,4,6,4,3,2,1], [2,3,4,6,5,3,2,1], [2,3,4,6,5,4,2,1],
   [2,3,4,6,5,4,3,1], [2,3,4,6,5,4,3,2], [1,3,3,5,4,3,2,1],
   [1,2,3,5,4,3,2,1], [1,2,3,4,4,3,2,1], [1,2,2,4,4,3,2,1],
   [1,2,3,4,3,3,2,1], [1,2,2,4,3,3,2,1], [1,2,2,3,3,3,2,1],
   [1,1,2,3,3,3,2,1], [1,2,3,4,3,2,2,1], [1,2,2,4,3,2,2,1],
   [1,2,2,3,3,2,2,1], [1,1,2,3,3,2,2,1], [1,2,2,3,2,2,2,1],
   [1,1,2,3,2,2,2,1], [1,1,2,2,2,2,2,1], [1,1,1,2,2,2,2,1],
   [1,2,3,4,3,2,1,1], [1,2,2,4,3,2,1,1], [1,2,2,3,3,2,1,1],
   [1,1,2,3,3,2,1,1], [1,2,2,3,2,2,1,1], [1,1,2,3,2,2,1,1],
   [1,1,2,2,2,2,1,1], [1,1,1,2,2,2,1,1], [1,2,2,3,2,1,1,1],
   [1,1,2,3,2,1,1,1], [1,1,2,2,2,1,1,1], [1,1,1,2,2,1,1,1],
   [1,1,2,2,1,1,1,1], [1,1,1,2,1,1,1,1], [1,1,1,1,1,1,1,1],
   [1,0,1,1,1,1,1,1], [1,2,3,4,3,2,1,0], [1,2,2,4,3,2,1,0],
   [1,2,2,3,3,2,1,0], [1,1,2,3,3,2,1,0], [1,2,2,3,2,2,1,0],
   [1,1,2,3,2,2,1,0], [1,1,2,2,2,2,1,0], [1,1,1,2,2,2,1,0],
   [1,2,2,3,2,1,1,0], [1,1,2,3,2,1,1,0], [1,1,2,2,2,1,1,0],
   [1,1,1,2,2,1,1,0], [1,1,2,2,1,1,1,0], [1,1,1,2,1,1,1,0],
   [1,1,1,1,1,1,1,0], [1,0,1,1,1,1,1,0], [1,2,2,3,2,1,0,0],
   [1,1,2,3,2,1,0,0], [1,1,2,2,2,1,0,0], [1,1,1,2,2,1,0,0],
   [1,1,2,2,1,1,0,0], [1,1,1,2,1,1,0,0], [1,1,1,1,1,1,0,0],
   [1,0,1,1,1,1,0,0], [1,1,2,2,1,0,0,0], [1,1,1,2,1,0,0,0],
   [1,1,1,1,1,0,0,0], [1,0,1,1,1,0,0,0], [1,1,1,1,0,0,0,0],
   [1,0,1,1,0,0,0,0], [1,0,1,0,0,0,0,0], [1,0,0,0,0,0,0,0]]

/-- The `E_6` table: the first six simples, the positive list the
committed literal `posE6`. -/
def tableE6 : Table :=
  ⟨6, List.replicate 6 2, 1, slCartan 6 edgesE6,
   posE6,
   [1, 2, 2, 3, 2, 1]⟩

/-- The `E_7` table: the first seven simples, the positive list
the committed literal `posE7`. -/
def tableE7 : Table :=
  ⟨7, List.replicate 7 2, 1, slCartan 7 edgesE7,
   posE7,
   [2, 2, 3, 4, 3, 2, 1]⟩

/-- The `E_8` table: the whole simple list, the positive list the
committed literal `posE8`. -/
def tableE8 : Table :=
  ⟨8, List.replicate 8 2, 1, slCartan 8 edgesE8,
   posE8,
   [2, 3, 4, 6, 5, 4, 3, 2]⟩

/-! The adjugate rows: the five displayed matrices at their fold
keys, the coroot witness and the θ-fold row. -/

def adjG2 : List (List Nat) := [[2, 1], [3, 2]]

def adjF4 : List (List Nat) :=
  [[2, 3, 4, 2], [3, 6, 8, 4], [2, 4, 6, 3], [1, 2, 3, 2]]

def adjE6 : List (List Nat) :=
  [[4, 3, 5, 6, 4, 2], [3, 6, 6, 9, 6, 3], [5, 6, 10, 12, 8, 4],
   [6, 9, 12, 18, 12, 6], [4, 6, 8, 12, 10, 5], [2, 3, 4, 6, 5, 4]]

def adjE7 : List (List Nat) :=
  [[4, 4, 6, 8, 6, 4, 2], [4, 7, 8, 12, 9, 6, 3],
   [6, 8, 12, 16, 12, 8, 4], [8, 12, 16, 24, 18, 12, 6],
   [6, 9, 12, 18, 15, 10, 5], [4, 6, 8, 12, 10, 8, 4],
   [2, 3, 4, 6, 5, 4, 3]]

def adjE8 : List (List Nat) :=
  [[4, 5, 7, 10, 8, 6, 4, 2], [5, 8, 10, 15, 12, 9, 6, 3],
   [7, 10, 14, 20, 16, 12, 8, 4], [10, 15, 20, 30, 24, 18, 12, 6],
   [8, 12, 16, 24, 20, 15, 10, 5], [6, 9, 12, 18, 15, 12, 8, 4],
   [4, 6, 8, 12, 10, 8, 6, 3], [2, 3, 4, 6, 5, 4, 3, 2]]

/-- The adjugate rows' coroot witness
`Σ_k a_ik α_k(α_j^∨) = e δ_ij` over the member's Cartan reads, one
fold per key pair. -/
def adjRead (t : Table) (e : Nat) (rows : List (List Nat)) : Prop :=
  ((List.range t.rank).all (fun i => (List.range t.rank).all (fun j =>
    if (corootAt t (getAt [] rows i) j).oneValue
        (if i == j then BPair.ofNat e else BPair.unit)
    then true else false))) = true

instance (t : Table) (e : Nat) (rows : List (List Nat)) :
    Decidable (adjRead t e rows) :=
  inferInstanceAs (Decidable (_ = _))

/-- The θ-fold row: one adjugate row is the highest root's fold at
the fold key's multiple, the highest root the fundamental at that
key. -/
def thetaRowRead (t : Table) (e : Nat) (rows : List (List Nat))
    (k : Nat) : Prop :=
  (getAt [] rows k == t.thetaFold.map (fun c => e * c)) = true

instance (t : Table) (e : Nat) (rows : List (List Nat)) (k : Nat) :
    Decidable (thetaRowRead t e rows k) :=
  inferInstanceAs (Decidable (_ = _))

/-! The defining tables: the paired key encodings, the simple moves
as matrices at the form's twist, the coroot diagonals, and the
invariant count at the unit-content monomials. -/

/-- The `B` defining key count: the paired keys with the further
null key. -/
def vcountB (l : Nat) : Nat := 2 * l + 1

/-- The `C` defining key count: the paired keys. -/
def vcountC (l : Nat) : Nat := 2 * l

/-- The `D` defining key count: the paired keys. -/
def vcountD (l : Nat) : Nat := 2 * l

/-- The `B` pairing weight cleared at two: the null key at one,
every paired key at two. -/
def pw2B (l a : Nat) : Nat := if a == 2 * l then 1 else 2

private def diagOf (n : Nat) (f : Nat → BPair) : elim.Mat :=
  ground.matOf n n (fun a b => if a == b then f a else BPair.unit)

/-- The `B` cleared pairing as a matrix: the diagonal at the
cleared weights. -/
def wB (l : Nat) : elim.Mat :=
  diagOf (vcountB l) (fun a => BPair.ofNat (pw2B l a))

/-- The `B` simple raising: the difference move on a paired key
pair, the last key's short move through the null key at the
doubled return. -/
def raiseB (l i : Nat) : elim.Mat :=
  ground.matOf (vcountB l) (vcountB l) (fun r c =>
    if i + 2 ≤ l then
      if r == i && c == i + 1 then pB 1
      else if r == i + 1 + l && c == i + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i && c == 2 * l then pB 1
      else if r == 2 * l && c == i + l then b2
      else BPair.unit
    else BPair.unit)

/-- The `C` simple raising: the difference move on a paired key
pair, the last key's long move across to its partner. -/
def raiseC (l i : Nat) : elim.Mat :=
  ground.matOf (vcountC l) (vcountC l) (fun r c =>
    if i + 2 ≤ l then
      if r == i && c == i + 1 then pB 1
      else if r == i + 1 + l && c == i + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i && c == i + l then pB 1
      else BPair.unit
    else BPair.unit)

/-- The `D` simple raising: the difference move on a paired key
pair, the last key's sum move at the last coordinate pair. -/
def raiseD (l i : Nat) : elim.Mat :=
  ground.matOf (vcountD l) (vcountD l) (fun r c =>
    if i + 2 ≤ l then
      if r == i && c == i + 1 then pB 1
      else if r == i + 1 + l && c == i + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i - 1 && c == i + l then pB 1
      else if r == i && c == i - 1 + l then mB 1
      else BPair.unit
    else BPair.unit)

/-- The `B` simple lowering, spelled at its own entries: the
difference move's plain transpose, the short move reweighted
through the null key, the doubled entry crossing to the transpose's
partner slot. -/
def lowerB (l i : Nat) : elim.Mat :=
  ground.matOf (vcountB l) (vcountB l) (fun r c =>
    if i + 2 ≤ l then
      if r == i + 1 && c == i then pB 1
      else if r == i + l && c == i + 1 + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == 2 * l && c == i then b2
      else if r == i + l && c == 2 * l then pB 1
      else BPair.unit
    else BPair.unit)

/-- The `C` simple lowering: the difference move's plain transpose,
the long move's return across the last pair. -/
def lowerC (l i : Nat) : elim.Mat :=
  ground.matOf (vcountC l) (vcountC l) (fun r c =>
    if i + 2 ≤ l then
      if r == i + 1 && c == i then pB 1
      else if r == i + l && c == i + 1 + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i + l && c == i then pB 1
      else BPair.unit
    else BPair.unit)

/-- The `D` simple lowering: the difference move's plain transpose,
the sum move's return at the last coordinate pair. -/
def lowerD (l i : Nat) : elim.Mat :=
  ground.matOf (vcountD l) (vcountD l) (fun r c =>
    if i + 2 ≤ l then
      if r == i + 1 && c == i then pB 1
      else if r == i + l && c == i + 1 + l then mB 1
      else BPair.unit
    else if i + 1 == l then
      if r == i + l && c == i - 1 then pB 1
      else if r == i - 1 + l && c == i then mB 1
      else BPair.unit
    else BPair.unit)

private def kcuDiff (j i : Nat) : BPair :=
  if j == i then pB 1 else if j == i + 1 then mB 1 else BPair.unit

private def kcuB (l j i : Nat) : BPair :=
  if i + 2 ≤ l then kcuDiff j i
  else if i + 1 == l then (if j == i then b2 else BPair.unit)
  else BPair.unit

private def kcuC (l j i : Nat) : BPair :=
  if i + 2 ≤ l then kcuDiff j i
  else if i + 1 == l then (if j == i then pB 1 else BPair.unit)
  else BPair.unit

private def kcuD (l j i : Nat) : BPair :=
  if i + 2 ≤ l then kcuDiff j i
  else if i + 1 == l then
    (if j == i - 1 || j == i then pB 1 else BPair.unit)
  else BPair.unit

/-- The `B` key content at a simple coroot: the unprimed keys read
the coroot's differences with the short key doubled, the primed
keys negate their partners, and the null key reads the unit. -/
def kcorootB (l a i : Nat) : BPair :=
  if a == 2 * l then BPair.unit
  else if a < l then kcuB l a i
  else (kcuB l (a - l) i).swap

/-- The `C` key content at a simple coroot: the unprimed keys read
the coroot's differences with the long key single, the primed keys
negate their partners. -/
def kcorootC (l a i : Nat) : BPair :=
  if a < l then kcuC l a i else (kcuC l (a - l) i).swap

/-- The `D` key content at a simple coroot: the unprimed keys read
the coroot's differences with the sum move on the last coordinate
pair, the primed keys negate their partners. -/
def kcorootD (l a i : Nat) : BPair :=
  if a < l then kcuD l a i else (kcuD l (a - l) i).swap

/-- The `B` coroot diagonal at a simple key: the key contents on
the diagonal. -/
def hDiagB (l i : Nat) : elim.Mat :=
  diagOf (vcountB l) (fun a => kcorootB l a i)

/-- The `C` coroot diagonal at a simple key: the key contents on
the diagonal. -/
def hDiagC (l i : Nat) : elim.Mat :=
  diagOf (vcountC l) (fun a => kcorootC l a i)

/-- The `D` coroot diagonal at a simple key: the key contents on
the diagonal. -/
def hDiagD (l i : Nat) : elim.Mat :=
  diagOf (vcountD l) (fun a => kcorootD l a i)

/-- A member triple's display at one read: the pairing carries the
transpose (`Eᵀ W = W F`), the commutator reads the coroot diagonal
(`EF - FE = H`), and the diagonal returns the lowering
(`FH - HF = 2F`), the three entrywise one-value comparisons one
fold. -/
def tripleRead (W E F H : elim.Mat) : Prop :=
  ((if elim.matOneValue (elim.matMul (elim.transposeM E) W)
        (elim.matMul W F) then true else false)
    && (if elim.matOneValue
          (elim.matAdd (elim.matMul E F)
            (elim.matSwap (elim.matMul F E))) H
        then true else false)
    && (if elim.matOneValue
          (elim.matAdd (elim.matMul F H)
            (elim.matSwap (elim.matMul H F))) (elim.matAdd F F)
        then true else false)) = true

instance (W E F H : elim.Mat) : Decidable (tripleRead W E F H) :=
  inferInstanceAs (Decidable (_ = _))

/-- The unit-content read at a rank: each unprimed key's count in
the monomial meets its partner's, the null key unconstrained. -/
def unitContentAt (l : Nat) (m : List Nat) : Bool :=
  (List.range l).all (fun c => countOf c m == countOf (c + l) m)

/-- The Leibniz image of a monomial under a key matrix: per nonunit
matrix entry, the unit move's Leibniz outputs (`units.unitAct`)
scatter at the entry's coefficient, the coordinates over the stated
basis. -/
def actMat (M : elim.Mat) (mons : List (List Nat))
    (m : List Nat) : List BPair :=
  (List.range M.length).foldl (fun acc a =>
    (List.range (getAt [] M a).length).foldl (fun acc2 b =>
      let x := getAt BPair.unit (getAt [] M a) b
      if x.isUnitRep then acc2
      else (units.unitAct a b m).foldl
        (fun acc3 mon => units.scatterAt (places.idxOf mon mons) x acc3)
        acc2)
      acc)
    (mons.map (fun _ => BPair.unit))

private def stackedDef (rs : List elim.Mat)
    (full ucols : List (List Nat)) : elim.Mat :=
  rs.flatMap (fun M =>
    (elim.transposeM (ucols.map (actMat M full))).filter
      (fun r => !allUnit r))

/-- The `B` invariant count at a pair count: the stacked simple
raisings' kernel over the unit-content monomials of the doubled
degree, the raised images' coordinates over the full monomial
list. -/
def invCountB (l k : Nat) : Nat :=
  let full := places.allMon (vcountB l) (2 * k)
  let ucols := full.filter (unitContentAt l)
  elim.kernelDim ucols.length
    (stackedDef ((List.range l).map (raiseB l)) full ucols)

/-- The `C` invariant count at a pair count: the stacked simple
raisings' kernel over the unit-content monomials of the doubled
degree. -/
def invCountC (l k : Nat) : Nat :=
  let full := places.allMon (vcountC l) (2 * k)
  let ucols := full.filter (unitContentAt l)
  elim.kernelDim ucols.length
    (stackedDef ((List.range l).map (raiseC l)) full ucols)

/-- The `D` invariant count at a pair count: the stacked simple
raisings' kernel over the unit-content monomials of the doubled
degree. -/
def invCountD (l k : Nat) : Nat :=
  let full := places.allMon (vcountD l) (2 * k)
  let ucols := full.filter (unitContentAt l)
  elim.kernelDim ucols.length
    (stackedDef ((List.range l).map (raiseD l)) full ucols)

/-! The coordinate tier at the coroot presentation: the keys are
coroot lists, the reflections the integer matrices off the Cartan
rows, `ρ` the all-ones key, and the form the stated cleared Gram
with its defining read. -/

set_option genInjectivity false in
/-- The fundamental data at the coroot presentation
(`con:sertables`' adjugate-row form reads): the cleared Gram of the
fundamentals, its scale, the simple members' positions in the
positive list, and per simple index the reflection's permutation of
the positive list — the keys the contents at the member's coroot
solve. -/
structure FundData where
  gram : elim.Mat
  scale : Nat
  simplePos : List Nat
  perms : List (List Nat)

/-- The reflection's matrix at a simple index, off the Cartan row:
`(s_i μ)_j = μ_j − μ_i · α_i(α_j^∨)` (`con:gentable`'s reflection
join `μ = s_i μ + μ(α_i^∨) α_i`). -/
def reflM (t : gentable.Table) (i : Nat) : elim.Mat :=
  ground.matOf t.rank t.rank (fun j k =>
    BPair.add (if j == k then BPair.ofNat 1 else BPair.unit)
      (if k == i then
        (getAt BPair.unit (getAt [] t.cartan i) j).swap
      else BPair.unit))

/-- A positive member's coroot vector, `corootAt` over the keys
(`con:gentable`'s coroot pairs at `con:sertables`' positive
list). -/
def posCorootV (t : gentable.Table) (j : Nat) : List BPair :=
  (List.range t.rank).map
    (gentable.corootAt t (getAt [] t.posFolds j))

/-- A positive member's coroot vector reads the rank's order. -/
theorem posCorootV_length (t : gentable.Table) (j : Nat) :
    (posCorootV t j).length = t.rank :=
  ground.length_mapRange _ t.rank

/-- `ρ`'s coroot vector, one at every key (`con:sertables`' root
fold at its halved coroot read `(2ρ)(α_i^∨) = 2`). -/
def rhoV (t : gentable.Table) : List BPair :=
  List.replicate t.rank (BPair.ofNat 1)

/-- The form's pairing at a stated cleared Gram (`con:sertables`'
form displays at the adjugate-row solve). -/
def dotG (G : elim.Mat) (x y : List BPair) : BPair :=
  elim.dotP x (elim.matVec G y)

/-- The form's pairing at the fundamental data, `dotG` at the
carried Gram. -/
def dotB (F : FundData) (x y : List BPair) : BPair :=
  dotG F.gram x y

/-- A reflection's image of a key, normed (`con:sertables`: `s_i`
permutes the positive list off `α_i`). -/
def reflAt (t : gentable.Table) (i : Nat) (v : List BPair) :
    List BPair :=
  poly.pnorm (elim.matVec (reflM t i) v)

/-- The shape conjuncts: the stated lists' orders against the rank
and the positive list (`con:sertables`' displayed data). -/
def fundShape (t : gentable.Table) (F : FundData) : Prop :=
  F.gram.length = t.rank
    ∧ (F.gram.all (fun r => r.length == t.rank)) = true
    ∧ 0 < F.scale
    ∧ F.simplePos.length = t.rank
    ∧ F.perms.length = t.rank
    ∧ (F.simplePos.all (fun j => j < t.posFolds.length)) = true
    ∧ (F.perms.all (fun p => p.length == t.posFolds.length
        && p.all (fun j => j < t.posFolds.length))) = true

instance (t : gentable.Table) (F : FundData) :
    Decidable (fundShape t F) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The pairing's congruence at the second slot. -/
theorem dotB_congrR (F : FundData) (x u u' : List BPair)
    (h : poly.oneValue u u') :
    (dotB F x u).oneValue (dotB F x u') := by
  show (elim.dotP x (elim.matVec F.gram u)).oneValue
    (elim.dotP x (elim.matVec F.gram u'))
  rw [elim.dotP_comm x (elim.matVec F.gram u),
    elim.dotP_comm x (elim.matVec F.gram u')]
  exact elim.dotP_oneValue_left _ _ x
    (elim.matVec_congr F.gram u u' h)

/-- The pairing's additivity at the second slot. -/
theorem dotB_addR (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (x u v : List BPair)
    (hx : x.length = t.rank) (hu : u.length = t.rank)
    (hv : v.length = t.rank) :
    (dotB F x (elim.vecAdd u v)).oneValue
      (dotB F x u + dotB F x v) := by
  show (elim.dotP x
    (elim.matVec F.gram (elim.vecAdd u v))).oneValue _
  rw [elim.dotP_comm x (elim.matVec F.gram (elim.vecAdd u v))]
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _
      (elim.vecAdd (elim.matVec F.gram u) (elim.matVec F.gram v)) x
      (elim.matVec_vecAdd F.gram t.rank
        (elim.rowsLen_of_allP (fun _ hr => ground.beqEqOf hr)
          F.gram hshape.2.1) u v hu hv)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_vecAdd_left (elim.matVec F.gram u)
      (elim.matVec F.gram v) x
      (by rw [elim.matVec_length, hshape.1, hx]; exact Nat.le_refl _)
      (by rw [elim.matVec_length, hshape.1, hx]; exact Nat.le_refl _)) ?_
  rw [elim.dotP_comm (elim.matVec F.gram u) x,
    elim.dotP_comm (elim.matVec F.gram v) x]
  exact BPair.oneValue_refl _

/-- The pairing's scale at the second slot. -/
theorem dotB_scaleR (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (c : BPair) (x v : List BPair)
    (hv : v.length = t.rank) :
    (dotB F x (elim.vecScale c v)).oneValue (c * dotB F x v) := by
  show (elim.dotP x (elim.matVec F.gram
    (elim.vecScale c v))).oneValue _
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_right x _ _
      (elim.matVec_vecScale F.gram t.rank
        (elim.rowsLen_of_allP (fun _ hr => ground.beqEqOf hr)
          F.gram hshape.2.1) c v hv)) ?_
  exact elim.dotP_vecScale_right x (elim.matVec F.gram v) c


/-- The pairing's congruence at the first slot. -/
theorem dotB_congrL (F : FundData) (u u' x : List BPair)
    (h : poly.oneValue u u') : (dotB F u x).oneValue (dotB F u' x) :=
  elim.dotP_oneValue_left u u' (elim.matVec F.gram x) h


/-- The pairing's additivity at the first slot. -/
theorem dotB_addL (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (u v x : List BPair)
    (hu : u.length = t.rank) (hv : v.length = t.rank) :
    (dotB F (elim.vecAdd u v) x).oneValue
      (dotB F u x + dotB F v x) := by
  have hG : (elim.matVec F.gram x).length = t.rank :=
    (elim.matVec_length F.gram x).trans hshape.1
  exact elim.dotP_vecAdd_left u v (elim.matVec F.gram x)
    (by rw [hG, hu]; exact Nat.le_refl _)
    (by rw [hG, hv]; exact Nat.le_refl _)

/-- A balance partner's square is the member's own, the two swaps
composing to the identity. -/
theorem dotB_negSq (F : FundData) (u : List BPair) :
    dotB F (poly.neg u) (poly.neg u) = dotB F u u := by
  show elim.dotP (poly.neg u) (elim.matVec F.gram (poly.neg u)) = _
  rw [elim.dotP_swap_left,
    show poly.neg u = u.map BPair.swap from rfl,
    elim.matVec_swapArg u F.gram, elim.dotP_swapMap,
    BPair.swap_swap]
  rfl


/-- The Gram's defining read at a stated cleared Gram and scale:
the Cartan rows against the Gram read the scaled length diagonal,
`⟨α_k, ω_j⟩` cleared (`con:sertables`' adjugate-row form
reads). -/
def gramReadG (t : gentable.Table) (G : elim.Mat) (s : Nat) : Prop :=
  elim.matOneValue (elim.matMul t.cartan G)
    (ground.matOf t.rank t.rank (fun k j =>
      if k == j then BPair.ofNat (s * getAt 0 t.lenNums k)
      else BPair.unit))

instance (t : gentable.Table) (G : elim.Mat) (s : Nat) :
    Decidable (gramReadG t G s) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The Gram's defining read at the fundamental data, `gramReadG`
at the carried Gram and scale. -/
def gramRead (t : gentable.Table) (F : FundData) : Prop :=
  gramReadG t F.gram F.scale

instance (t : gentable.Table) (F : FundData) :
    Decidable (gramRead t F) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- A stated Gram's symmetry (`con:sertables`' form displays, the
symmetric pair read per content pair). -/
def gramSymReadG (G : elim.Mat) : Prop :=
  elim.matOneValue (elim.transposeM G) G

instance (G : elim.Mat) : Decidable (gramSymReadG G) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The symmetry at the fundamental data, `gramSymReadG` at the
carried Gram. -/
def gramSymRead (F : FundData) : Prop :=
  gramSymReadG F.gram

instance (F : FundData) : Decidable (gramSymRead F) :=
  inferInstanceAs (Decidable (elim.matOneValue _ _))

/-- The simple positions' read: the positive list holds each simple
at its stated position, the one-key fold (`con:sertables`' positive
lists at their displayed folds). -/
def simplePosRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank →
    getAt [] t.posFolds (getAt 0 F.simplePos i)
      = (List.range t.rank).map (fun k => if k == i then 1 else 0)

instance (t : gentable.Table) (F : FundData) :
    Decidable (simplePosRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank → _ = _))

/-- The involution read at the matrices: each reflection squares to
the identity, the table's own read (`con:sertables`: each letter an
involution, `s_i s_i μ = μ`). -/
def reflSquareRead (t : gentable.Table) : Prop :=
  ∀ i, i < t.rank →
    elim.matOneValue (elim.matMul (reflM t i) (reflM t i))
      (inertia.idMat t.rank)

instance (t : gentable.Table) : Decidable (reflSquareRead t) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    elim.matOneValue _ _))

/-- The involution read at the permutation data: each permutation of
the positive list is its own involution (`con:sertables`: each
letter an involution, read at the stated positions). -/
def permSquareRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank → ∀ j, j < t.posFolds.length →
    getAt 0 (getAt [] F.perms i)
      (getAt 0 (getAt [] F.perms i) j) = j

instance (t : gentable.Table) (F : FundData) :
    Decidable (permSquareRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    ∀ j, j < t.posFolds.length → _ = _))

/-- The form-keeping read: each reflection is a congruence of the
Gram (`con:sertables`: a reflection keeps the form). -/
def reflFormRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank →
    elim.matOneValue
      (elim.matMul (elim.transposeM (reflM t i))
        (elim.matMul F.gram (reflM t i)))
      F.gram

instance (t : gentable.Table) (F : FundData) :
    Decidable (reflFormRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    elim.matOneValue _ _))

/-- The permutation read: each reflection maps each positive member
off its own simple to the permuted position's member, and its own
simple to the balance partner (`con:sertables`' first shared read,
`s_i` permuting the positive list off `α_i`). -/
def permImageRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ i, i < t.rank →
    (∀ j, j < t.posFolds.length → j ≠ getAt 0 F.simplePos i →
      reflAt t i (posCorootV t j)
        = poly.pnorm (posCorootV t (getAt 0 (getAt [] F.perms i) j)))
    ∧ reflAt t i (posCorootV t (getAt 0 F.simplePos i))
        = poly.pnorm (poly.neg (posCorootV t (getAt 0 F.simplePos i)))

instance (t : gentable.Table) (F : FundData) :
    Decidable (permImageRead t F) :=
  inferInstanceAs (Decidable (∀ i, i < t.rank →
    (∀ j, j < t.posFolds.length → j ≠ _ → _ = _) ∧ _ = _))

/-- The `ρ`-dot read: every positive member's Gram pairing against
`ρ` is positive (`con:sertables`' regular reads, the `ρ`-fold's
members at positive root-fold dots). -/
def rhoDotRead (t : gentable.Table) (F : FundData) : Prop :=
  ∀ j, j < t.posFolds.length →
    BPair.unit < dotB F (posCorootV t j) (rhoV t)

instance (t : gentable.Table) (F : FundData) :
    Decidable (rhoDotRead t F) :=
  inferInstanceAs (Decidable (∀ j, j < t.posFolds.length →
    _ < _))

/-- `B_2`'s fundamental data at the coroot presentation: the
cleared Gram off the adjugate solve at the displayed Cartan rows,
the simple positions, and the reflections' permutations of the
positive list (`con:sertables`' member data). -/
def fundB2 : FundData :=
  ⟨[[(BPair.ofNat 2), (BPair.ofNat 1)], [(BPair.ofNat 1), (BPair.ofNat 1)]],
   1, [0, 3], [[0, 1, 3, 2], [1, 0, 2, 3]]⟩

/-- `G_2`'s fundamental data at the coroot presentation
(`con:sertables`' displayed folds and lengths). -/
def fundG2 : FundData :=
  ⟨[[(BPair.ofNat 4), (BPair.ofNat 6)], [(BPair.ofNat 6), (BPair.ofNat 12)]],
   1, [0, 1], [[0, 4, 3, 2, 1, 5], [2, 1, 0, 3, 5, 4]]⟩

/-! The series' displayed Weyl lists (`con:sertables`: a series
member's list is the signed place permutations of its coordinates,
every sign vector at `B` and `C` and the even flip counts at `D`,
the displayed list, with distinct signed permutations at distinct
coordinate images, one list member each; the grading `sgn σ`
against the flip count's parity at `B` and `C` and `sgn σ` alone
at `D`).  The producers run at the coroot presentation: the
coordinate display enters by the displayed coroot pairs' own
solve, the suffix folds at the doubled coordinates (`B` and `D`)
or the plain ones (`C`), each image reads back through the
displayed pairs, and the halving is the doubled display's read,
the entries one parity across a signed image. -/

/-- The signed half at an even balance pair, the doubled
coordinate display's coroot read. -/
def halfB (x : BPair) : BPair :=
  if x < BPair.unit then (BPair.ofNat (BPair.marginN x / 2)).swap
  else BPair.ofNat (BPair.marginN x / 2)

/-- The `B` coordinate display of a coroot vector: the doubled
suffix fold, the last key the last coroot read itself. -/
def coordsB (m : List BPair) : List BPair :=
  match m.reverse with
  | [] => []
  | a :: rest =>
    rest.foldl (fun acc x =>
      (x + x + ground.getAt BPair.unit acc 0) :: acc) [a]

/-- The `C` coordinate display: the plain suffix fold. -/
def coordsC (m : List BPair) : List BPair :=
  match m.reverse with
  | [] => []
  | a :: rest =>
    rest.foldl (fun acc x =>
      (x + ground.getAt BPair.unit acc 0) :: acc) [a]

/-- The `D` coordinate display: the doubled suffix fold seeded at
the fork keys' sum and gap. -/
def coordsD (m : List BPair) : List BPair :=
  match m.reverse with
  | [] => []
  | [_] => []
  | a :: b :: rest =>
    rest.foldl (fun acc x =>
      (x + x + ground.getAt BPair.unit acc 0) :: acc)
      [b + a, a + b.swap]

/-- The `B` coroot read of a coordinate display: the halved
consecutive gaps with the last key's own read. -/
def corootsB (v : List BPair) : List BPair :=
  (List.zipWith (fun a b => halfB (a + b.swap)) v (v.drop 1))
    ++ [ground.getAt BPair.unit v (v.length - 1)]

/-- The `C` coroot read: the consecutive gaps with the last key's
own read. -/
def corootsC (v : List BPair) : List BPair :=
  (List.zipWith (fun a b => a + b.swap) v (v.drop 1))
    ++ [ground.getAt BPair.unit v (v.length - 1)]

/-- The `D` coroot read: the halved consecutive gaps with the
fork's halved sum. -/
def corootsD (v : List BPair) : List BPair :=
  (List.zipWith (fun a b => halfB (a + b.swap)) v (v.drop 1))
    ++ [halfB (ground.getAt BPair.unit v (v.length - 2)
          + ground.getAt BPair.unit v (v.length - 1))]

/-- A signed permutation's image of a coordinate display: the
permuted display at the flipped places. -/
def signedImage (l : Nat) (D : List BPair) (p : List Nat)
    (n : Nat) : List BPair :=
  (List.range l).map (fun q =>
    let x := ground.getAt BPair.unit D (ground.getAt 0 p q)
    if n / 2 ^ q % 2 == 1 then x.swap else x)

/-- A sign vector's flip parity. -/
def flipParity (l n : Nat) : Bool :=
  ((List.range l).foldl (fun a q => a + n / 2 ^ q % 2) 0) % 2 == 1

private def serWeylGo (coords coroots : List BPair → List BPair)
    (flipsAll : Bool) (l : Nat) (v : List BPair) :
    List (List BPair × Bool) :=
  let D := coords v
  (places.perms l).flatMap (fun p =>
    (List.range (2 ^ l)).filterMap (fun n =>
      if flipsAll || !(flipParity l n) then
        some (poly.pnorm (coroots (signedImage l D p n)),
          if flipsAll then places.parity p != flipParity l n
          else places.parity p)
      else none))

/-- The `B` member's displayed Weyl list at a coroot key: every
sign vector, the grading `sgn σ` against the flip parity. -/
def serWeylB (l : Nat) (v : List BPair) : List (List BPair × Bool) :=
  serWeylGo coordsB corootsB true l v

/-- The `C` member's displayed Weyl list at a coroot key. -/
def serWeylC (l : Nat) (v : List BPair) : List (List BPair × Bool) :=
  serWeylGo coordsC corootsC true l v

/-- The `D` member's displayed Weyl list at a coroot key: the even
flip counts, the grading `sgn σ` alone. -/
def serWeylD (l : Nat) (v : List BPair) : List (List BPair × Bool) :=
  serWeylGo coordsD corootsD false l v

/-- The Weyl list's shape read: every member's key at the rank,
normed (`con:sertables`' graded image list at the coordinate tier's
presentation, the keys the reflections' own carrier). -/
def wShapeRead (t : gentable.Table)
    (W : List (List BPair × Bool)) : Prop :=
  ∀ vp ∈ W, vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1

instance (t : gentable.Table) (W : List (List BPair × Bool)) :
    Decidable (wShapeRead t W) :=
  inferInstanceAs (Decidable (∀ vp ∈ W, _ ∧ _ = _))

end sertables
