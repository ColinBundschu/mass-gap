import MassGap.Sertables
import MassGap.Serpairing
/-!
`con:memtable` — the member generating tables. A member's generating
table is a table space (`con:gentable`) over a stated key list: the
pairing a stated weight (`Table.wt`, sparse, the coordinate fold
at the weights, its entry at a key pair `wtAt`, one value with its
transpose entry by entry at `symmWt`, the read at every key pair
`wtAt_symm`, the letters' at `lettersT_symm`), its cleared partner
at the
clearing (`wtInv`, `wtDet`, the dual pairing's solved witness at
`weightRead`), the simple triples stated sparse matrices over the
keys (`raises`, `lowers`, the coroot diagonals `hdiag`), read at
the transpose identity `Eᵀ W = W F` with the two triple displays
(`tripleRead`, the sparse spelling of `sertables.tripleRead`), the
key weights the diagonals' reads (`keyWeight`, a key's coroot
list), and the table's dual pair (`Table.dual`): a stated matrix
over the keys with its clearing, the invariant of the doubled
table at the standard action twice and an isometry at the
pairing, `wtDet · cᵀ W c = ν² · wtInv` (`dualRead` at its three
reads `dualEntries`, `dualInvAt` and `dualIso`, the read
introduced from the three decided one by one at
`dualRead_intro`), the identification of the dual block on the
coordinate family with the dual label's block; the letters' table
has none, its device the star (`con:slotpower`). The sparse maps
multiply at one sorted walk (`smul` on `ground.mergeCross`, the
first's entries at their source keys against the second's at
their target keys). The tables: the letters' table at the
matrix units (`lettersT`, `con:units`' `E_{i,i+1}` and `E_{i+1,i}`
at the unit weight), the spinor table at the paired keys
(`spinorT`: the keys the bit families over the unprimed keys, the
wedge and the contraction at the sign of the occupied lower keys,
the null key's parity at `B`, the simple raisings the quadratic
reads `wedge ∘ contraction` at a difference move, the short move
`wedge ∘ parity` at `B` and the last move `wedge ∘ wedge` at `D`,
the dual pair each bit family against its complement at the side
of the occupied keys' complement lengths, `spinorC`), the defining
tables at `con:sertables`' dual pairs (`definingB`, `definingC`,
`definingD` at `serpairing.dualB`, `dualC`, `dualD`), the join of
two tables at concatenated keys (`joinT`, the `B` and `D`
generating tables the defining table's join with the spinor's,
the dual pairs scaled at each other's clearings), the adjoint
table of a simply-laced member at the displayed root list with the
cocycle (`adjointT`: the simple raisings and lowerings the signed
roots' moves by a signed simple root resolved at one sorted walk
against the folds at the lexicographic order, `moveBy`,
`keyedFolds`;
the cocycle the parity of the diagonal and edge-pair products,
`cocycle`, `edgePairs`; the dual pair the Cartan's adjugate on the
simple keys and each root key against its partner at the
determinant's balance partner, the clearing the determinant), the
restriction of a table to a key sublist closed under a simple
sublist (`subT`), and the fold at the orbit sums of the simple
raisings (`foldT`). The fixed members: `E_8`'s adjoint table
(`adjointE8`); `E_7`'s the `E_8` table at the root keys pairing
one against the highest root, the `56`, with the dual pair the
cocycle at the pairs joining to the highest root (`genE7`,
`dual56`); `E_6`'s the `E_8` table at the root keys at the
complementary pair's dominant grade together with their partners,
the `27` with its dual (`genE6`); `F_4`'s `E_6`'s adjoint table
folded at the chain's exchange (`genF4`); `G_2`'s `D_4`'s defining
table folded at the three outer simples' orbit against the
center's (`genG2`). The closure read (`closureRead`, every
positive root's raising a commutator word of the simple raisings
along the fold descent at an occupied coefficient, the stated
triples generating the member's every root operator) is a
decidable read at the stated matrices and a stated word store,
one entry per positive fold with a simple key occupied in the fold
and the fold's word: a simple fold's word its raising, a further
fold's the commutator of the key's raising against the withdrawn
fold's stored word (`wordStep`), every word read one value with
its commutator and occupied (`closureAt`) over a store covering
the positive list (`foldsCover`); a store computes height by
height at the least occupied key whose withdrawn fold is stored
(`rootStore`) or enters as a committed record.
-/

namespace memtable
open ground

/-- A sparse map over the keys: entries `(target, source, coefficient)`. -/
abbrev SMap := List (Nat × Nat × BPair)

private def keyEq (a b : Nat × Nat) : Bool := a.1 == b.1 && a.2 == b.2

private def keyLt (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The entries at the keyed form, the key pair against the
coefficient. -/
private def keyed (m : SMap) : List ((Nat × Nat) × BPair) :=
  m.map (fun e => ((e.1, e.2.1), e.2.2))

/-- The entries collected at their keys in the keys' order, the
coefficients joined at their canonical representatives and the
unit entries withdrawn (`ground.collectBy`). -/
def collect (m : SMap) : SMap :=
  (collectBy keyLt keyEq (keyed m)).map (fun p => (p.1.1, p.1.2, p.2))

/-- The product of two sparse maps, the first applied after the
second: the first's entries in their runs at the source keys walked
against the second's in their runs at the target keys, the products
at the shared keys (`ground.sortRuns`, `ground.mergeCross`),
collected. -/
def smul (a b : SMap) : SMap :=
  let aS := sortRuns (fun x y => x < y) (fun x y => x == y) (a.map (fun e => (e.2.1, e)))
  let bS := sortRuns (fun x y => x < y) (fun x y => x == y) (b.map (fun e => (e.1, e)))
  collect (mergeCross (fun x y => x < y) (fun x y => x == y)
    (fun e f => (e.1, f.2.1, e.2.2 * f.2.2)) (aS.length + bS.length) aS bS)

/-- The transpose. -/
def sT (a : SMap) : SMap := a.map (fun e => (e.2.1, e.1, e.2.2))

/-- The balance partner entrywise. -/
def sNeg (a : SMap) : SMap := a.map (fun e => (e.1, e.2.1, e.2.2.swap))

/-- The join of two maps. -/
def sAdd (a b : SMap) : SMap := collect (a ++ b)

/-- A diagonal map at a stated list. -/
def sDiag (l : List BPair) : SMap :=
  (List.range l.length).filterMap (fun k =>
    let c := getAt BPair.unit l k
    if c.isUnitRep then none else some (k, k, c))

/-- Two maps one value at every key pair either occupies
(`ground.oneValueBy`). -/
def sOneValue (a b : SMap) : Bool :=
  oneValueBy keyLt keyEq (keyed a) (keyed b)

/-- A map scaled entrywise at a natural. -/
def sScale (n : Nat) (m : SMap) : SMap :=
  m.map (fun e => (e.1, e.2.1, e.2.2 * BPair.ofNat n))

set_option genInjectivity false in
/-- A generating table: the key count, the pairing's weight (sparse,
the identity's entries where diagonal at one) with its
cleared partner at the clearing (the dual pairing's solved
witness), per simple index the raising, the lowering and the
coroot diagonal, and the dual pair with its clearing where the
table has one. -/
structure Table where
  keys : Nat
  wt : SMap
  wtInv : SMap
  wtDet : Nat
  raises : List SMap
  lowers : List SMap
  hdiag : List (List BPair)
  dual : Option (SMap × Pos)

/-- The rank, the simple count. -/
def Table.rank (T : Table) : Nat := T.raises.length

/-- The keys' weights, the coroot diagonals transposed: one coroot
list per key, built by one walk over the diagonals. -/
def keyWeights (T : Table) : List (List BPair) :=
  T.hdiag.foldr (fun h acc => List.zipWith List.cons h acc)
    (List.replicate T.keys [])

/-- A key's weight, its coroot list off the diagonals. -/
def keyWeight (T : Table) (k : Nat) : List BPair :=
  getAt [] (keyWeights T) k

/-- The triple display at a simple index: `Eᵀ W = W F`,
`E F − F E = H` and `F H − H F = 2 F`, the three one-value reads. -/
def tripleRead (T : Table) (i : Nat) : Prop :=
  (let E := getAt [] T.raises i
   let F := getAt [] T.lowers i
   let H := sDiag (getAt [] T.hdiag i)
   sOneValue (smul (sT E) T.wt) (smul T.wt F)
     && sOneValue (sAdd (smul E F) (sNeg (smul F E))) H
     && sOneValue (sAdd (smul F H) (sNeg (smul H F))) (sAdd F F)) = true

instance (T : Table) (i : Nat) : Decidable (tripleRead T i) :=
  inferInstanceAs (Decidable (_ = _))

/-- The identity weight at a key count. -/
def unitWt (n : Nat) : SMap := (List.range n).map (fun k => (k, k, BPair.ofNat 1))

/-- The weight's witness read: the weight against its stated
cleared partner reads the clearing's diagonal, the solved witness
of the dual pairing (`def:elim`'s adjugate identity). -/
def weightRead (T : Table) : Prop :=
  sOneValue (smul T.wt T.wtInv)
    (sDiag (List.replicate T.keys (BPair.ofNat T.wtDet))) = true

instance (T : Table) : Decidable (weightRead T) :=
  inferInstanceAs (Decidable (_ = _))

/-- The weight's entry at a target and a source key, the entries'
fold. -/
def wtAt (m : SMap) (t s : Nat) : BPair :=
  m.foldl (fun acc e => if e.1 == t && e.2.1 == s then acc + e.2.2 else acc)
    BPair.unit

/-- The weight's symmetry read: the weight one value with its
transpose entry by entry, the pairing symmetric at the exchange
(`lem:lowerspan`'s reads at it). -/
def symmWt (T : Table) : Prop :=
  T.wt.all (fun e =>
    decide ((wtAt T.wt e.2.1 e.1).oneValue (wtAt T.wt e.1 e.2.1))) = true

instance (T : Table) : Decidable (symmWt T) :=
  inferInstanceAs (Decidable (_ = _))

/-- The entry read as the family fold at the key pair's guard. -/
theorem wtAt_read (m : SMap) (t s : Nat) :
    (wtAt m t s).oneValue (famFold BPair.add BPair.unit
      (fun e => if e.1 == t && e.2.1 == s then e.2.2 else BPair.unit) m) :=
  BPair.oneValue_trans
    (foldB_foldl_guard (fun e : Nat × Nat × BPair => e.1 == t && e.2.1 == s)
      (fun e : Nat × Nat × BPair => e.2.2) m BPair.unit)
    (BPair.unit_add _)

/-- A vacant key pair reads the sum's unit. -/
private theorem wtAt_vacant (m : SMap) (t s : Nat)
    (h : ∀ e ∈ m, (e.1 == t && e.2.1 == s) = false) :
    (wtAt m t s).oneValue BPair.unit :=
  BPair.oneValue_trans (wtAt_read m t s) (foldB_null _ m (fun e he => by
    show (if e.1 == t && e.2.1 == s then e.2.2 else BPair.unit).oneValue
      BPair.unit
    rw [h e (mem_of_countOf_pos e m he),
      if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh)]
    exact BPair.oneValue_refl _))

/-- At the symmetry read the entry reads one value at its two
orders at every key pair: an occupied pair reads its own entry, an
occupied partner reads the partner's, and a vacant pair reads the
sum's unit both ways. -/
theorem wtAt_symm (T : Table) (hw : symmWt T) (t s : Nat) :
    (wtAt T.wt t s).oneValue (wtAt T.wt s t) := by
  have hall := all_of_mem _ T.wt hw
  cases h1 : T.wt.any (fun e => e.1 == t && e.2.1 == s) with
  | true =>
    obtain ⟨e, he, hc⟩ := mem_of_any _ T.wt h1
    obtain ⟨h1', h2'⟩ := andSplitB hc
    have ht : e.1 = t := beqEqOf h1'
    have hs : e.2.1 = s := beqEqOf h2'
    have hx := of_decide_eq_true (hall e he)
    rw [ht, hs] at hx
    exact BPair.oneValue_symm hx
  | false =>
    have hv : (wtAt T.wt t s).oneValue BPair.unit :=
      wtAt_vacant T.wt t s (fun e he =>
        boolFalseOfNot (all_of_mem _ T.wt (all_not_of_any_false _ T.wt h1) e he))
    cases h2 : T.wt.any (fun e => e.1 == s && e.2.1 == t) with
    | true =>
      obtain ⟨e, he, hc⟩ := mem_of_any _ T.wt h2
      obtain ⟨h1', h2'⟩ := andSplitB hc
      have ht : e.1 = s := beqEqOf h1'
      have hs : e.2.1 = t := beqEqOf h2'
      have hx := of_decide_eq_true (hall e he)
      rw [ht, hs] at hx
      exact hx
    | false =>
      have hv2 : (wtAt T.wt s t).oneValue BPair.unit :=
        wtAt_vacant T.wt s t (fun e he =>
          boolFalseOfNot (all_of_mem _ T.wt (all_not_of_any_false _ T.wt h2) e he))
      exact BPair.oneValue_trans hv (BPair.oneValue_symm hv2)

/-- The dual pair's content read: every entry at two keys of
partnered weights, the coroot lists joining to the unit fold, the
pair at the unit content (so a vector reading the sum's unit at
every raising is a top of the unit label, its block the line,
`lem:tops`; `lem:lowerspan`). -/
def dualEntries (T : Table) (c : SMap) : Bool :=
  c.all (fun e => (List.zipWith (fun a b => (a + b).norm)
    (keyWeight T e.1) (keyWeight T e.2.1)).all (fun x =>
      decide (x.oneValue BPair.unit)))

/-- The dual pair's invariance at one simple index: `E c + c Eᵀ`
at the sum's unit, the doubled table at the standard action
twice. -/
def dualInvAt (T : Table) (c : SMap) (i : Nat) : Bool :=
  let E := getAt [] T.raises i
  sOneValue (sAdd (smul E c) (smul c (sT E))) []

/-- The dual pair's isometry: `wtDet · cᵀ W c = ν² · wtInv` at the
clearing `ν`, the identification of the dual block with the dual
label's block an isometry of the pairing. -/
def dualIso (T : Table) (c : SMap) (nu : Pos) : Bool :=
  sOneValue (sScale T.wtDet (smul (sT c) (smul T.wt c)))
    (sScale (posVal nu * posVal nu) T.wtInv)

/-- The dual pair's three reads at a stated pair: the content read,
the invariance at every simple index, and the isometry; false at a
table without one. -/
def dualCheck (T : Table) : Bool :=
  match T.dual with
  | none => false
  | some (c, nu) =>
    dualEntries T c && (List.range T.rank).all (dualInvAt T c) && dualIso T c nu

/-- The dual pair's read (`con:memtable`). -/
def dualRead (T : Table) : Prop := dualCheck T = true

instance (T : Table) : Decidable (dualRead T) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dual pair's read at its three reads decided one by one:
the stated pair with the content read, the invariance fold over
the simple indices and the isometry each true reads the pair. -/
theorem dualRead_intro (T : Table) (c : SMap) (nu : Pos)
    (hd : T.dual = some (c, nu)) (h1 : dualEntries T c = true)
    (h2 : (List.range T.rank).all (dualInvAt T c) = true)
    (h3 : dualIso T c nu = true) : dualRead T := by
  show dualCheck T = true
  unfold dualCheck
  rw [hd]
  show (dualEntries T c && (List.range T.rank).all (dualInvAt T c)
    && dualIso T c nu) = true
  rw [h1, h2, h3]
  rfl

/-! The letters' table, the matrix units at the fundamental count. -/

/-- The letters' table: `E_{i,i+1}` reads the letter `i+1` to `i`,
`E_{i+1,i}` the letter `i` to `i+1`, the weight one, and the
diagonal the letter's difference read (`con:units`); the letters
hold no dual pair, the star their device (`con:slotpower`). -/
def lettersT (d : Nat) : Table :=
  ⟨d, unitWt d, unitWt d, 1,
   (List.range (d - 1)).map (fun i => [(i, i + 1, BPair.ofNat 1)]),
   (List.range (d - 1)).map (fun i => [(i + 1, i, BPair.ofNat 1)]),
   (List.range (d - 1)).map (fun i => (List.range d).map (fun k =>
     if k == i then BPair.ofNat 1 else if k == i + 1 then (BPair.ofNat 1).swap
     else BPair.unit)),
   none⟩

/-- The letters' weight is symmetric: every entry diagonal. -/
theorem lettersT_symm (d : Nat) : symmWt (lettersT d) := by
  refine all_of_mem_intro _ _ (fun e he => ?_)
  obtain ⟨k, _, hk⟩ := mem_map_of _ _ e he
  rw [← hk]
  exact decide_eq_true (BPair.oneValue_refl _)

/-! The spinor table at the paired keys. -/

/-- A bit family's read at a key: the occupancy of the unprimed key
`i` in the family `n`. -/
def bitAt (n i : Nat) : Nat := n / 2 ^ i % 2

/-- The sign at a key: the balance partner of one at an odd count
of occupied keys below `i`, one otherwise. -/
def signBelow (n i : Nat) : BPair :=
  if ((List.range i).foldl (fun a j => a + bitAt n j) 0) % 2 == 1
  then (BPair.ofNat 1).swap else BPair.ofNat 1

/-- The wedge at an unprimed key: the bit raised at the sign, the
sum's unit at an occupied bit. -/
def wedgeS (l i : Nat) : SMap :=
  (List.range (2 ^ l)).filterMap (fun n =>
    if bitAt n i == 0 then some (n + 2 ^ i, n, signBelow n i) else none)

/-- The contraction at a primed key: the bit lowered at the sign,
the unit at a vacant bit. -/
def contrS (l i : Nat) : SMap :=
  (List.range (2 ^ l)).filterMap (fun n =>
    if bitAt n i == 1 then some (n - 2 ^ i, n, signBelow (n - 2 ^ i) i) else none)

/-- The parity at the null key: the balance partner of one at an
odd bit count. -/
def parityS (l : Nat) : SMap :=
  (List.range (2 ^ l)).map (fun n =>
    (n, n, if ((List.range l).foldl (fun a j => a + bitAt n j) 0) % 2 == 1
      then (BPair.ofNat 1).swap else BPair.ofNat 1))

/-- The spinor's coroot diagonal at a simple index: the bit
differences at the difference moves, `B`'s short move the last bit
against its partner, `D`'s last move the last two bits' join less
one. -/
def spinorH (l : Nat) (isD : Bool) (i : Nat) : List BPair :=
  (List.range (2 ^ l)).map (fun n =>
    if i + 2 ≤ l then BPair.ofNat (bitAt n i) + (BPair.ofNat (bitAt n (i + 1))).swap
    else if isD then
      BPair.ofNat (bitAt n (l - 2) + bitAt n (l - 1)) + (BPair.ofNat 1).swap
    else BPair.ofNat (2 * bitAt n (l - 1)) + (BPair.ofNat 1).swap)

/-- The spinor's simple raising: the wedge at `i` composed with the
contraction at `i+1` at a difference move, `B`'s short move the
wedge at the last key composed with the parity, `D`'s last move
the two last wedges composed. -/
def spinorE (l : Nat) (isD : Bool) (i : Nat) : SMap :=
  if i + 2 ≤ l then smul (wedgeS l i) (contrS l (i + 1))
  else if isD then smul (wedgeS l (l - 2)) (wedgeS l (l - 1))
  else smul (wedgeS l (l - 1)) (parityS l)

/-- The spinor table's dual pair: each bit family against its
complement at the side of the fold of its occupied keys'
complement lengths, `Σ_{j ∈ n} (l − j)`, a move of one occupied key
down by one and the last key's join each flipping the side. -/
def spinorC (l : Nat) : SMap :=
  (List.range (2 ^ l)).map (fun n =>
    (n, 2 ^ l - 1 - n,
     if ((List.range l).foldl (fun a j => a + bitAt n j * (l - j)) 0) % 2 == 1
     then (BPair.ofNat 1).swap else BPair.ofNat 1))

/-- The spinor table at a rank, `B` at `isD = false` and `D` at
`isD = true`: the bit keys, the unit weight, the raisings the
quadratic reads, the lowerings their transposes, and the dual pair
`spinorC` at the clearing one. -/
def spinorT (l : Nat) (isD : Bool) : Table :=
  ⟨2 ^ l, unitWt (2 ^ l), unitWt (2 ^ l), 1,
   (List.range l).map (spinorE l isD),
   (List.range l).map (fun i => sT (spinorE l isD i)),
   (List.range l).map (spinorH l isD),
   some (spinorC l, Pos.one)⟩

/-! The defining tables as generating tables, the join, the
restriction and the fold. -/

/-- A dense matrix's sparse reading, the off-unit entries. -/
def ofDense (M : elim.Mat) : SMap :=
  (List.range M.length).flatMap (fun r =>
    (List.range (getAt [] M r).length).filterMap (fun c =>
      let x := getAt BPair.unit (getAt [] M r) c
      if x.isUnitRep then none else some (r, c, x)))

/-- A diagonal matrix's diagonal list. -/
private def diagList (M : elim.Mat) : List BPair :=
  (List.range M.length).map (fun r => getAt BPair.unit (getAt [] M r) r)

/-- The `B` defining table (`con:sertables`) as a generating table
at its cleared pairing, the dual pair `serpairing.dualB` at the
clearing two. -/
def definingB (l : Nat) : Table :=
  ⟨sertables.vcountB l, ofDense (sertables.wB l),
   (List.range (sertables.vcountB l)).map (fun k =>
     (k, k, BPair.ofNat (if k == 2 * l then 2 else 1))), 2,
   (List.range l).map (fun i => ofDense (sertables.raiseB l i)),
   (List.range l).map (fun i => ofDense (sertables.lowerB l i)),
   (List.range l).map (fun i => diagList (sertables.hDiagB l i)),
   some (ofDense (serpairing.dualB l), posOfSucc 1)⟩

/-- The `C` defining table at the unit weight, the dual pair
`serpairing.dualC` at the clearing one. -/
def definingC (l : Nat) : Table :=
  ⟨sertables.vcountC l, unitWt (sertables.vcountC l),
   unitWt (sertables.vcountC l), 1,
   (List.range l).map (fun i => ofDense (sertables.raiseC l i)),
   (List.range l).map (fun i => ofDense (sertables.lowerC l i)),
   (List.range l).map (fun i => diagList (sertables.hDiagC l i)),
   some (ofDense (serpairing.dualC l), Pos.one)⟩

/-- The `D` defining table at the unit weight, the dual pair
`serpairing.dualD` at the clearing one. -/
def definingD (l : Nat) : Table :=
  ⟨sertables.vcountD l, unitWt (sertables.vcountD l),
   unitWt (sertables.vcountD l), 1,
   (List.range l).map (fun i => ofDense (sertables.raiseD l i)),
   (List.range l).map (fun i => ofDense (sertables.lowerD l i)),
   (List.range l).map (fun i => diagList (sertables.hDiagD l i)),
   some (ofDense (serpairing.dualD l), Pos.one)⟩

/-- A map's keys shifted. -/
private def shiftS (n : Nat) (m : SMap) : SMap :=
  m.map (fun e => (e.1 + n, e.2.1 + n, e.2.2))

/-- The join of two tables at one simple list: the keys
concatenated, each simple index's maps the two tables' side by
side, the cleared partners each scaled at the other's clearing,
and the dual pairs each scaled at the other's clearing at the
clearings' product, vacant where either is. -/
def joinT (A B : Table) : Table :=
  ⟨A.keys + B.keys, A.wt ++ shiftS A.keys B.wt,
   sScale B.wtDet A.wtInv ++ shiftS A.keys (sScale A.wtDet B.wtInv),
   A.wtDet * B.wtDet,
   List.zipWith (fun a b => a ++ shiftS A.keys b) A.raises B.raises,
   List.zipWith (fun a b => a ++ shiftS A.keys b) A.lowers B.lowers,
   List.zipWith (fun a b => a ++ b) A.hdiag B.hdiag,
   match A.dual, B.dual with
   | some (ca, na), some (cb, nb) =>
     some (sScale (posVal nb) ca ++ shiftS A.keys (sScale (posVal na) cb), na * nb)
   | none, _ => none
   | some _, none => none⟩

/-- The `B` generating table: the defining table joined to the
spinor's. -/
def genB (l : Nat) : Table := joinT (definingB l) (spinorT l false)

/-- The `D` generating table: the defining table joined to the
spinor's, the two parity summands the two spinors. -/
def genD (l : Nat) : Table := joinT (definingD l) (spinorT l true)

/-- A map restricted to a key sublist, the keys renumbered at their
positions in the sublist, an entry off it withdrawn. -/
def subMap (ks : List Nat) (m : SMap) : SMap :=
  m.filterMap (fun e =>
    let i := places.idxOf e.1 ks
    let j := places.idxOf e.2.1 ks
    if i < ks.length && j < ks.length then some (i, j, e.2.2) else none)

/-- A table restricted to a simple sublist and a key sublist closed
under the sublist's raisings and lowerings: the maps at the kept
keys renumbered, the diagonals at the kept keys, the dual pair
restricted with it. -/
def subT (T : Table) (sub : List Nat) (ks : List Nat) : Table :=
  ⟨ks.length, subMap ks T.wt, subMap ks T.wtInv, T.wtDet,
   sub.map (fun i => subMap ks (getAt [] T.raises i)),
   sub.map (fun i => subMap ks (getAt [] T.lowers i)),
   sub.map (fun i => ks.map (fun k => getAt BPair.unit (getAt [] T.hdiag i) k)),
   T.dual.map (fun p => (subMap ks p.1, p.2))⟩

/-- A table folded at stated orbits of its simple list: each
folded index's maps the orbit's sums, the diagonal the orbit's
coroots' sum, the keys and the dual pair kept. -/
def foldT (T : Table) (orbits : List (List Nat)) : Table :=
  ⟨T.keys, T.wt, T.wtInv, T.wtDet,
   orbits.map (fun o => collect (o.flatMap (getAt [] T.raises))),
   orbits.map (fun o => collect (o.flatMap (getAt [] T.lowers))),
   orbits.map (fun o => (List.range T.keys).map (fun k =>
     BPair.sum (o.map (fun i => getAt BPair.unit (getAt [] T.hdiag i) k)))),
   T.dual⟩

/-- The `G_2` generating table: `D_4`'s defining table folded at
the three outer simples' orbit against the center's. -/
def genG2 : Table := foldT (definingD 4) [[0, 2, 3], [1]]

/-! The adjoint table at a simply-laced member's displayed root
list with the cocycle. -/

/-- A signed root: its side and its fold. -/
abbrev SRoot := Bool × List Nat

/-- The signed roots' key: the simple keys first, then the positive
folds in the displayed order, then their partners. -/
def rootKey (t : gentable.Table) (s : SRoot) : Option Nat :=
  let j := places.idxOf s.2 t.posFolds
  if j < t.posFolds.length then
    some (t.rank + (if s.1 then j else t.posFolds.length + j))
  else none

/-- The positive folds with their positions in the lexicographic
order (`ground.lexLt`), the runs one position each at distinct
folds (`ground.sortRuns`). -/
def keyedFolds (t : gentable.Table) : List (List Nat × List Nat) :=
  sortRuns lexLt (fun x y => x == y)
    ((List.range t.posFolds.length).map (fun p => (getAt [] t.posFolds p, p)))

/-- One fold at or below another entrywise. -/
def foldLe (a b : List Nat) : Bool := (List.zipWith Nat.ble a b).all (fun x => x)

/-- The edge pairs of the simple list, `i < j` at the Cartan read
the balance partner of one. -/
def edgePairs (t : gentable.Table) : List (Nat × Nat) :=
  (List.range t.rank).flatMap (fun i => (List.range t.rank).filterMap (fun j =>
    if i < j && decide ((getAt BPair.unit (getAt [] t.cartan i) j).oneValue
        (BPair.ofNat 1).swap)
    then some (i, j) else none))

/-- The cocycle's side at two folds: the balance partner of one at
an odd count of the products `f_i g_i` with the edge products
`f_i g_j` over the edge pairs, one otherwise. -/
def cocycle (t : gentable.Table) (f g : List Nat) : BPair :=
  let e := (List.range t.rank).foldl (fun a i => a + getAt 0 f i * getAt 0 g i) 0
    + (edgePairs t).foldl (fun a p => a + getAt 0 f p.1 * getAt 0 g p.2) 0
  if e % 2 == 1 then (BPair.ofNat 1).swap else BPair.ofNat 1

/-- The signed root list, the positives then their partners. -/
def sroots (t : gentable.Table) : List SRoot :=
  t.posFolds.map (fun f => (true, f)) ++ t.posFolds.map (fun f => (false, f))

/-- The signed roots moved by a signed simple root, the side `eps`
at the index `i`: a root on the simple's side moves to the sum, a
root on the other side to the difference where the simple sits
inside its fold, the simple's own partner to the simple key at the
balance partner of one, and a simple key `j` to the signed simple's
key at the balance partner of the Cartan read; the moved folds
sorted into their runs at the lexicographic order and walked
against the keyed folds (`ground.sortRuns`, `ground.mergeCross`),
each entry `(moved key, root key, coefficient)` at the stated
coefficient read of the root's fold, the entries collected. -/
def moveBy (t : gentable.Table) (eps : Bool) (i : Nat)
    (coef : List Nat → BPair) : SMap :=
  let n := t.posFolds.length
  let ai := unitAt t.rank i
  let offAt (side : Bool) : Nat := t.rank + (if side then 0 else n)
  let cands : List (List Nat × (Nat × Nat × BPair)) :=
    (List.range n).flatMap (fun p =>
      let f := getAt [] t.posFolds p
      let same := (List.zipWith Nat.add f ai, (offAt eps, offAt eps + p, coef f))
      if f == ai then [same]
      else if foldLe ai f then
        [same, (List.zipWith Nat.sub f ai, (offAt (!eps), offAt (!eps) + p, coef f))]
      else [same])
  let sorted := sortRuns lexLt (fun x y => x == y) cands
  collect (mergeCross lexLt (fun x y => x == y)
    (fun c q => (c.1 + q, c.2.1, c.2.2)) (sorted.length + n) sorted (keyedFolds t)
  ++ (match rootKey t (!eps, ai) with
    | some km => [(i, km, (BPair.ofNat 1).swap)]
    | none => [])
  ++ (List.range t.rank).filterMap (fun j =>
    (rootKey t (eps, ai)).map (fun ka =>
      (ka, j, (getAt BPair.unit (getAt [] t.cartan i) j).swap))))

/-- The adjoint table's simple raising: a root key moved to the
sum's key at the cocycle's side, the partner key to the simple key
at the balance partner of one, and a simple key `j` to the root
key at the balance partner of the Cartan read (`moveBy` at the
positive side). -/
def adjRaise (t : gentable.Table) (i : Nat) : SMap :=
  moveBy t true i (cocycle t (unitAt t.rank i))

/-- The adjoint table's simple lowering, the balance partner of the
partner root's action: the own root's key to the simple key at the
balance partner of one, a root key moved to the difference's key
at the cocycle's balance partner, and a simple key to the partner
root's key at the Cartan read's balance partner (`moveBy` at the
negative side). -/
def adjLower (t : gentable.Table) (i : Nat) : SMap :=
  moveBy t false i (fun f => (cocycle t (unitAt t.rank i) f).swap)

/-- The adjoint table's coroot diagonal: the unit at the simple
keys, a root key's coroot read at its side. -/
def adjH (t : gentable.Table) (i : Nat) : List BPair :=
  (List.range t.rank).map (fun _ => BPair.unit)
    ++ (sroots t).map (fun b =>
      if b.1 then gentable.corootAt t b.2 i else (gentable.corootAt t b.2 i).swap)

/-- The adjoint table's dual pair: the Cartan's adjugate on the
simple keys, and each root key against its partner at the
determinant's balance partner, the clearing the determinant. -/
def adjDual (t : gentable.Table) : SMap :=
  let D := BPair.marginN (elim.detD t.cartan)
  ofDense (elim.adjMD t.cartan)
    ++ t.posFolds.flatMap (fun f =>
      match rootKey t (true, f), rootKey t (false, f) with
      | some ka, some km => [(ka, km, (BPair.ofNat D).swap), (km, ka, (BPair.ofNat D).swap)]
      | none, _ => []
      | some _, none => [])

/-- The adjoint table: the simple keys at the Cartan reads' weight
with the weight's partner the Cartan rows' adjugate at their
determinant, the root keys at one, the dual pair `adjDual` at the
determinant's clearing. -/
def adjointT (t : gentable.Table) : Table :=
  ⟨t.rank + 2 * t.posFolds.length,
   ofDense t.cartan ++ shiftS t.rank (unitWt (2 * t.posFolds.length)),
   ofDense (elim.adjMD t.cartan)
     ++ shiftS t.rank ((List.range (2 * t.posFolds.length)).map (fun k =>
       (k, k, BPair.ofNat (BPair.marginN (elim.detD t.cartan))))),
   BPair.marginN (elim.detD t.cartan),
   (List.range t.rank).map (adjRaise t),
   (List.range t.rank).map (adjLower t),
   (List.range t.rank).map (adjH t),
   some (adjDual t, posOfSucc (BPair.marginN (elim.detD t.cartan) - 1))⟩

/-- The `E_8` adjoint table. -/
def adjointE8 : Table := adjointT sertables.tableE8

/-- A signed root's pairing against a stated fold, the fold's coroot
reads folded at the fold's coefficients, at the root's side. -/
def gradeAt (t : gentable.Table) (g : List Nat) (b : SRoot) : BPair :=
  let v := BPair.sum ((List.range t.rank).map (fun j =>
    BPair.ofNat (getAt 0 g j) * gentable.corootAt t b.2 j))
  if b.1 then v else v.swap

/-- The signed roots at a stated grade against the highest root's
fold, their keys in the adjoint table. -/
def keysAtGrade (t : gentable.Table) (g : List Nat) (v : BPair) : List Nat :=
  (sroots t).filterMap (fun b =>
    if decide ((gradeAt t g b).oneValue v) then rootKey t b else none)

/-- The `56`'s dual pair over the `E_7` keys: a positive root
against the highest root's withdrawn fold, the pair joining to the
highest root, at the cocycle's balance partner. -/
def dual56 (t : gentable.Table) (ks : List Nat) : SMap :=
  t.posFolds.filterMap (fun a =>
    if foldLe a t.thetaFold then
      let b := List.zipWith Nat.sub t.thetaFold a
      match rootKey t (true, a), rootKey t (true, b) with
      | some ka, some kb =>
        let i := places.idxOf ka ks
        let j := places.idxOf kb ks
        if i < ks.length && j < ks.length then some (i, j, (cocycle t a b).swap)
        else none
      | none, _ => none
      | some _, none => none
    else none)

/-- The `E_7` generating table: the `E_8` adjoint table at the root
keys pairing one against the highest root, the `56` at the first
seven simples, with its own dual pair at the pairs joining to the
highest root. -/
def genE7 : Table :=
  let ks := keysAtGrade sertables.tableE8 sertables.tableE8.thetaFold (BPair.ofNat 1)
  { subT adjointE8 (List.range 7) ks with dual := some (dual56 sertables.tableE8 ks, Pos.one) }

/-- The `E_6` generating table: the `E_8` adjoint table at the root
keys at the complementary pair's dominant grade, one against the
last simple root and equal members against the highest root less
it, together with their partners, the `27` with its dual at the
first six simples, the dual pair the adjoint's restricted. -/
def genE6 : Table :=
  let t := sertables.tableE8
  let a8 := unitAt 8 7
  let rest := List.zipWith Nat.sub t.thetaFold a8
  let top := (sroots t).filterMap (fun b =>
    if decide ((gradeAt t a8 b).oneValue (BPair.ofNat 1))
        && decide ((gradeAt t rest b).oneValue BPair.unit)
    then rootKey t b else none)
  let ks := top ++ (sroots t).filterMap (fun b =>
    if decide ((gradeAt t a8 b).oneValue (BPair.ofNat 1).swap)
        && decide ((gradeAt t rest b).oneValue BPair.unit)
    then rootKey t b else none)
  subT adjointE8 (List.range 6) ks

/-- The `F_4` generating table: `E_6`'s adjoint table folded at the
chain's exchange, the two fixed simples then the inner pair's
orbit and the ends'. -/
def genF4 : Table := foldT (adjointT sertables.tableE6) [[1], [3], [2, 4], [0, 5]]

/-! The closure read: the commutator words along the fold
descent, stated data with their keys. -/

/-- A word store's entry: a positive fold, a simple key, and the
fold's word. -/
abbrev WordEntry := List Nat × Nat × SMap

/-- The commutator of a simple raising against a stored word. -/
def commWord (T : Table) (j : Nat) (R : SMap) : SMap :=
  let E := getAt [] T.raises j
  sAdd (smul E R) (sNeg (smul R E))

/-- A positive fold's word at a stated key over a store of words: a
simple fold its own raising, and a further fold the commutator of
the key's raising against the withdrawn fold's stored word, vacant
at a key off the fold or at a withdrawn fold off the store. -/
def wordStep (T : Table) (t : gentable.Table) (st : List WordEntry)
    (f : List Nat) (j : Nat) : Option SMap :=
  let i := places.idxOf f ((List.range t.rank).map (unitAt t.rank))
  if i < t.rank then some (getAt [] T.raises i)
  else if 0 < getAt 0 f j then
    (st.find? (fun p => p.1 == editAt (fun x => x - 1) j f)).map
      (fun p => commWord T j p.2.2)
  else none

/-- The positive folds at their heights in order, the coefficient
sums, the withdrawn fold of every key sitting before the fold it
serves (`ground.sortRuns`). -/
def foldsByHeight (t : gentable.Table) : List (List Nat) :=
  (sortRuns (fun x y => x < y) (fun x y => x == y)
    (t.posFolds.map (fun f => (sumNat f, f)))).flatMap (fun p => p.2)

/-- A word store built height by height, each fold at the least
simple key occupied in it whose withdrawn fold is already stored,
the fold's word the step there (`wordStep`); the read at a stated
store (`closureRead`) takes any key so occupied. -/
def rootStore (T : Table) (t : gentable.Table) : List WordEntry :=
  (foldsByHeight t).foldl (fun st f =>
    let j := ((List.range t.rank).find? (fun j =>
      0 < getAt 0 f j && st.any (fun p => p.1 == editAt (fun x => x - 1) j f))).getD 0
    st ++ [(f, j, (wordStep T t st f j).getD [])]) []

/-- A stated store covers the positive folds: one entry per fold
and every positive fold among the entries' folds. -/
def foldsCover (t : gentable.Table) (st : List WordEntry) : Bool :=
  st.length == t.posFolds.length
    && t.posFolds.all (fun f => st.any (fun p => p.1 == f))

/-- The closure read at one entry of a stated store: the entry's
word one value with the step at its key over the store
(`wordStep`) and occupied, some entry off the sum's unit. -/
def closureAt (T : Table) (t : gentable.Table) (st : List WordEntry)
    (k : Nat) : Bool :=
  let p := getAt ([], 0, []) st k
  match wordStep T t st p.1 p.2.1 with
  | some w => sOneValue p.2.2 w && (collect p.2.2).any (fun e => !e.2.2.isUnitRep)
  | none => false

/-- The closure read at a stated word store: the store covers the
positive folds and every entry's word is the step's own at its key
and occupied, so every positive root's raising is a commutator word
of the simple raisings along the fold descent and the stated
triples generate the member's every root operator; the store the
computed one (`rootStore`) or a committed record re-read here. -/
def closureRead (T : Table) (t : gentable.Table) (st : List WordEntry) : Prop :=
  (foldsCover t st && (List.range st.length).all (closureAt T t st)) = true

instance (T : Table) (t : gentable.Table) (st : List WordEntry) :
    Decidable (closureRead T t st) :=
  inferInstanceAs (Decidable (_ = _))

/-- The closure read at its two reads decided one by one: the
cover and the entries' fold read the store. -/
theorem closureRead_intro (T : Table) (t : gentable.Table)
    (st : List WordEntry) (h1 : foldsCover t st = true)
    (h2 : (List.range st.length).all (closureAt T t st) = true) :
    closureRead T t st := by
  show (foldsCover t st && (List.range st.length).all (closureAt T t st)) = true
  rw [h1, h2]
  rfl

end memtable
