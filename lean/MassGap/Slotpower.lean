import MassGap.Blockcount
import MassGap.Labels
import MassGap.Memtable
/-!
`con:slotpower` — the presentation's carrier. A factor list's slot
power is the power at one slot per factor, the units acting on an
undaggered factor's slot by the standard action and on a daggered
factor's slot by the dual action, the exchanged letters' balance
partner (`lem:dualread`(i)), both read on the one coordinate family,
the power's monomials. A label enters at its word
pair (`wordPair`: a column of the reduced shape at a length at or
below its complement's enters the top word at that many undaggered
factors, a further column the bottom word at the complement length's
daggered, the tie a column at its complement's length), its slots the
top columns' undaggered then the bottom columns' daggered (`wordSig`
at a word pair, `labelSig` at the label's, an incoming end at the
exchanged signature `endWordSig`, `endSig`). A monomial's
weight is its undaggered letter counts against its daggered, one
balance pair per letter (`weightAt`, `weightOf`), and the unit weight
is the full columns' class (`unitWeightAt`, `unitWeight` at a
monomial).

The vectors read at their occupied monomials (`SVec`, a monomial
with its coefficient, the family collected at its keys with the
unit coefficients withdrawn, `collect`), the one tier at a
generating table (`con:memtable`), the letters' table its instance
(`memtable.lettersT`): the table's sparse map at one slot (`actT`),
the simple raising and lowering at a slot signature (`raiseT`,
`lowerT`, the dual action at a daggered slot), a monomial's weight
at the keys' coroot lists (`weightT`, `weightV` a vector's at its
first occupied monomial, every block member weight-homogeneous),
the weighted pairing (`monDotT` one monomial against a vector at
the weight's substitutions, `dotT`, `gramT`), the tensor
(`tensorV`), the scale, the sum and the primitive representative
(`scaleV`, `addV`, `prim`), two vectors one value (`oneValueV`), the
lowering closure at a stated top (`blockSpanT` at the membership
read within the weight's group, `tryAddT`, `closeT`, the closure run
at the stored descents, `closeTS`, with `blockSpanT_eq` its read at
the fresh walk at the pairing's exchange, `dotT_comm`), the fused
span at stated end blocks grouped at the ends' weight lists, the
groups pairwise orthogonal at each end's own grading
(`fusedGroupsT`, `fusedSpanT`), the stacked raisings' kernel over a
pool, the invariants' list (`kernelT`, `def:elim`'s back solve;
`comboV` a kernel member as a vector), the Gram-dual solve over a
pool with its clearing (`spanCoeffsT`), the span membership at its
residual (`spanMemberT`), the projection at one pool and group by
group at the clearings' product, the vector at its reduced
representative (`projectT`, `projectGroupsT`, `reduceV`), the paired
tensor of a stated matrix at stated slot pairs (`pairTensor`, the
identity's at the weight's cleared partner the through pairing of
two ends at opposite orientations, `throughT`, and the dual pair's
at two ends of one orientation, `dualThroughT`, each cleared at its
matrix's clearing to the pairs' count), and the place action's
relabeling of the occupied monomials (`relabelV`).

The letters' own devices (`con:slotpower`): a label's block at its
word pair is the lowerings' span at its top, the top-word columns'
wedge exhibits on the undaggered slots tensored with the
bottom-word columns' dual wedges on the daggered, the wedge at the
last letters of the complement's length (`blockTop`, `dualWedge`,
`blockSpanAt` the closure at the letters' table, `blockSpanAt_eq` its
read at the fresh walk); a wiring's tensor
reads one letter per row end, read again at the column end it
pairs (`wiringG`); the through pairing of two ends at dual labels
pairs each column's slots with its complement column's (`colMatch`
at the column layouts, `layoutOf`, at a stated key dual), a wiring
at an undaggered slot against a daggered one and the star at a tie
column, the monomials at complementary letter sets at the swap
grading's side (`starFam`) cleared at the column length's
factorial (`throughPair`, the tensor the column pairs' families'
product); and the terms' transport of `thm:pairpencil` reads a
moved end's slots at the column match (`transportSlots`, the tie
columns' groups at a reversed traversal) with the tie columns at
the star's map (`starAt`).
-/

namespace slotpower
open ground places blockcount

/-- The reduced shape's columns, longest first. -/
def cols (s : Shape) : List Nat := blockcount.columnLengths (labels.reduce s)

/-- A column's side at the count: the top word where its length
sits at or below its complement's. -/
def topCol (d l : Nat) : Bool := l + l ≤ d

/-- The top-word columns, longest first. -/
def topCols (d : Nat) (s : Shape) : List Nat := (cols s).filter (topCol d)

/-- The bottom-word columns, longest first. -/
def botCols (d : Nat) (s : Shape) : List Nat :=
  (cols s).filter (fun l => !topCol d l)

/-- A label's word pair: the top columns' lengths against the
bottom columns' complement lengths. -/
def wordPair (d : Nat) (s : Shape) : Nat × Nat :=
  (sumNat (topCols d s), sumNat ((botCols d s).map (fun l => d - l)))

/-- A word pair's slot signature: the undaggered slots then the
daggered, `false` undaggered. -/
def wordSig (w : Nat × Nat) : List Bool :=
  List.replicate w.1 false ++ List.replicate w.2 true

/-- A label's slot signature, its word pair's. -/
def labelSig (d : Nat) (s : Shape) : List Bool := wordSig (wordPair d s)

/-- An end's slot signature at a word pair: the word's at an
outgoing end, the exchanged at an incoming, the dual block on the
one coordinate family. -/
def endWordSig (w : Nat × Nat) (out : Bool) : List Bool :=
  if out then wordSig w else (wordSig w).map not

/-- An end's slot signature, its label's word pair at the end's
orientation. -/
def endSig (d : Nat) (e : Shape × Bool) : List Bool :=
  endWordSig (wordPair d e.1) e.2

/-- A vertex's slot signature, its ends' in the incident order. -/
def vertexSig (d : Nat) (es : List (Shape × Bool)) : List Bool :=
  es.flatMap (endSig d)

/-- The undaggered slots in order. -/
def upSlots (sig : List Bool) : List Nat :=
  (List.range sig.length).filter (fun s => !getAt false sig s)

/-- The daggered slots in order. -/
def downSlots (sig : List Bool) : List Nat :=
  (List.range sig.length).filter (fun s => getAt false sig s)

/-- A weight at two contents, the undaggered count against the
daggered per letter, one balance pair each at its canonical
representative. -/
def weightAt (up dn : List Nat) : List BPair :=
  List.zipWith (fun a b => (BPair.ofNat a + (BPair.ofNat b).swap).norm) up dn

/-- A monomial's weight at a signature. -/
def weightOf (d : Nat) (sig : List Bool) (m : List Nat) : List BPair :=
  weightAt (content d ((upSlots sig).map (fun s => getAt 0 m s)))
    (content d ((downSlots sig).map (fun s => getAt 0 m s)))

/-- The unit-weight read: every letter's balance one value with the
first's, the full columns' class. -/
def unitWeightAt (w : List BPair) : Bool :=
  w.all (fun x => decide (x.oneValue (getAt BPair.unit w 0)))

/-- A monomial's unit-weight read at a signature. -/
def unitWeight (d : Nat) (sig : List Bool) (m : List Nat) : Bool :=
  unitWeightAt (weightOf d sig m)

/-! The vectors at their occupied monomials, the one tier at a
generating table. -/

/-- A vector at its occupied monomials with their coefficients. -/
abbrev SVec := List (List Nat × BPair)

/-- The monomials collected at their keys, the coefficients joined
at their canonical representatives and the unit coefficients
withdrawn (`ground.collectBy`). -/
def collect (v : SVec) : SVec := collectBy lexLt (fun a b => a == b) v

/-- A monomial's coefficient in a vector, the entries' fold. -/
def coefAt (m : List Nat) (v : SVec) : BPair :=
  v.foldl (fun acc p => if p.1 == m then acc + p.2 else acc) BPair.unit

/-- Two vectors one value at every occupied monomial
(`ground.oneValueBy`). -/
def oneValueV (u v : SVec) : Bool := oneValueBy lexLt (fun a b => a == b) u v

/-- A vector scaled, the coefficients' products collected. -/
def scaleV (c : BPair) (v : SVec) : SVec := collect (v.map (fun p => (p.1, p.2 * c)))

/-- Two vectors' sum. -/
def addV (u v : SVec) : SVec := collect (u ++ v)

/-- The scalar one, the vacant power's own vector. -/
def unitV : SVec := [([], BPair.ofNat 1)]

/-- The tensor of two vectors, the monomials concatenated at the
coefficients' products. -/
def tensorV (u v : SVec) : SVec :=
  u.flatMap (fun p => v.map (fun q => (p.1 ++ q.1, (p.2 * q.2).norm)))

/-- A vector at its primitive representative, the coefficients
stripped at their shared count (`thm:windowsep`'s strip). -/
def prim (v : SVec) : SVec :=
  let k := BPair.listContent (v.map Prod.snd)
  List.zipWith (fun p c => (p.1, c)) v (BPair.listPrim k (v.map Prod.snd))

/-- A dense coordinate family's vector at its occupied monomials
(`blockcount.HVec`, the letters' exhibits). -/
def ofH (v : HVec) : SVec :=
  (List.zipWith (fun m x => (m, x)) (monomialsAt v.content) v.coords).filter
    (fun p => !decide (p.2.oneValue BPair.unit))

/-- The place action on a vector at a slot permutation, the
permuted display of every occupied monomial (`con:places`): the
monomial at a slot reads the source's at the permutation's slot. -/
def relabelV (σ : List Nat) (v : SVec) : SVec :=
  collect (v.map (fun p => (places.expo p.1 σ, p.2)))

/-- A sparse map's action at one slot: each entry reads the source
key at the slot to the target at the coefficient, the balance
partner at a stated side. -/
def actT (m : memtable.SMap) (neg : Bool) (s : Nat) (v : SVec) : SVec :=
  collect (v.flatMap (fun p => m.filterMap (fun e =>
    if getAt 0 p.1 s == e.2.1 then
      some (p.1.set s e.1, if neg then (p.2 * e.2.2).swap else p.2 * e.2.2)
    else none)))

/-- A table's simple raising at a slot signature: the raising at an
undaggered slot, and at a daggered slot the dual action, the
balance partner of the lowering (`lem:dualread`(i)). -/
def raiseT (T : memtable.Table) (sig : List Bool) (i : Nat) (v : SVec) : SVec :=
  collect ((List.range sig.length).flatMap (fun s =>
    if getAt false sig s then actT (getAt [] T.lowers i) true s v
    else actT (getAt [] T.raises i) false s v))

/-- A table's simple lowering at a slot signature, the lowering at
an undaggered slot and the balance partner of the raising at a
daggered one. -/
def lowerT (T : memtable.Table) (sig : List Bool) (i : Nat) (v : SVec) : SVec :=
  collect ((List.range sig.length).flatMap (fun s =>
    if getAt false sig s then actT (getAt [] T.raises i) true s v
    else actT (getAt [] T.lowers i) false s v))

/-- A monomial's weight at a table and a signature: the keys' coroot
lists summed, an undaggered slot's own and a daggered slot's
balance partner, at the canonical representatives. -/
def weightT (T : memtable.Table) (sig : List Bool) (m : List Nat) : List BPair :=
  (List.range sig.length).foldl (fun acc s =>
    let w := memtable.keyWeight T (getAt 0 m s)
    List.zipWith (fun a b => (a + b).norm) acc
      (if getAt false sig s then w.map BPair.swap else w))
    (List.replicate T.rank BPair.unit)

/-- A vector's weight at a table, its first occupied monomial's. -/
def weightV (T : memtable.Table) (sig : List Bool) (v : SVec) : List BPair :=
  match v.head? with
  | none => List.replicate T.rank BPair.unit
  | some p => weightT T sig p.1

/-- The unit-weight read at a table: every coroot read the sum's
unit. -/
def unitWeightT (T : memtable.Table) (sig : List Bool) (m : List Nat) : Bool :=
  (weightT T sig m).all (fun x => decide (x.oneValue BPair.unit))

/-- A table's weight read at the unit: every entry the identity's. -/
def unitWtRead (T : memtable.Table) : Bool :=
  T.wt.all (fun e => e.1 == e.2.1 && decide ((BPair.ofNat 1).oneValue e.2.2))
    && T.wt.length == T.keys

/-- One monomial's weighted pairing against a vector: at the unit
weight the monomial's coefficient, and at a stated weight the
substitutions' fold, the keys' weight entries' product against the
substituted monomial's coefficient. -/
def monDotT (T : memtable.Table) (unitW : Bool) (m : List Nat) (v : SVec) : BPair :=
  if unitW then coefAt m v
  else
    let subs := m.map (fun k => T.wt.filterMap (fun e =>
      if e.1 == k then some (e.2.1, e.2.2) else none))
    (prodLists subs).foldl (fun acc ch =>
      let w := ch.foldl (fun a e => a * e.2) (BPair.ofNat 1)
      acc + w * coefAt (ch.map Prod.fst) v) BPair.unit

/-- The weighted pairing of two vectors at the occupied monomials. -/
def dotT (T : memtable.Table) (unitW : Bool) (u v : SVec) : BPair :=
  u.foldl (fun acc p => acc + p.2 * monDotT T unitW p.1 v) BPair.unit

/-- The Gram of a list at the weighted pairing. -/
def gramT (T : memtable.Table) (l : List SVec) : elim.Mat :=
  let uw := unitWtRead T
  elim.gramBy (fun u v => (dotT T uw u v).norm) l

private def keyFold (m : List Nat) (v : SVec) : BPair :=
  famFold BPair.add BPair.unit (fun q => if q.1 == m then q.2 else BPair.unit) v

/-- A monomial's coefficient as the family fold at the key's
guard. -/
private theorem coefAt_read (m : List Nat) (v : SVec) :
    (coefAt m v).oneValue (keyFold m v) :=
  BPair.oneValue_trans
    (foldB_foldl_guard (fun p : List Nat × BPair => p.1 == m)
      (fun p : List Nat × BPair => p.2) v BPair.unit)
    (BPair.unit_add _)

/-- A chain's weight, the entries' product. -/
private def prodW (ch : List (Nat × BPair)) : BPair :=
  ch.foldl (fun a e => a * e.2) (BPair.ofNat 1)

private theorem prodW_cons (x : Nat × BPair) (ch : List (Nat × BPair)) :
    prodW (x :: ch) = prodW ch * x.2 := by
  show ch.foldl (fun a e => a * e.2) (BPair.ofNat 1 * x.2)
    = ch.foldl (fun a e => a * e.2) (BPair.ofNat 1) * x.2
  exact (foldl_mul_seed BPair.mul BPair.mul_comm BPair.mul_assoc
    (fun e : Nat × BPair => e.2) ch (BPair.ofNat 1) x.2).symm

/-- A key's substitutions at a weight: the entries at the key as
their sources with their weights. -/
private def filt (w : memtable.SMap) (k : Nat) : List (Nat × BPair) :=
  w.filterMap (fun e => if e.1 == k then some (e.2.1, e.2.2) else none)

/-- The substitutions per slot. -/
private def subs (w : memtable.SMap) (m : List Nat) : List (List (Nat × BPair)) :=
  m.map (filt w)

/-- The pairing's kernel at two monomials as the chains' fold: the
chains over the first monomial's substitutions landing on the
second at their weights. -/
private def kerF (w : memtable.SMap) (m m' : List Nat) : BPair :=
  famFold BPair.add BPair.unit
    (fun ch => if ch.map Prod.fst == m' then prodW ch else BPair.unit)
    (prodLists (subs w m))

/-- The pairing's kernel at two monomials as the slots' product of
the weight's entries. -/
private def kerW (w : memtable.SMap) : List Nat → List Nat → BPair
  | [], [] => BPair.ofNat 1
  | [], _ :: _ => BPair.unit
  | _ :: _, [] => BPair.unit
  | k :: t, k' :: t' => memtable.wtAt w k k' * kerW w t t'

/-- The pairing's kernel at a table and the unit-weight read: the
key delta at the unit weight, the slots' product otherwise. -/
private def kerAt (T : memtable.Table) (uw : Bool) (m m' : List Nat) : BPair :=
  if uw then (if m == m' then BPair.ofNat 1 else BPair.unit) else kerW T.wt m m'

private theorem filt_cons (w : memtable.SMap) (e : Nat × Nat × BPair) (k : Nat) :
    filt (e :: w) k
      = if e.1 == k then (e.2.1, e.2.2) :: filt w k else filt w k := by
  show List.filterMap
    (fun e : Nat × Nat × BPair => if e.1 == k then some (e.2.1, e.2.2) else none)
    (e :: w) = _
  rw [List.filterMap_cons]
  cases he : (e.1 == k) with
  | true => exact rfl
  | false => exact rfl

/-- The substitutions at a key folded at a source read the weight's
entries at the key pair. -/
private theorem filt_fold (k k' : Nat) : ∀ w : memtable.SMap,
    (famFold BPair.add BPair.unit
      (fun x : Nat × BPair => if x.1 == k' then x.2 else BPair.unit)
      (filt w k)).oneValue
    (famFold BPair.add BPair.unit
      (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) w)
  | [] => BPair.oneValue_refl _
  | e :: r => by
    rw [filt_cons]
    show (famFold BPair.add BPair.unit
        (fun x : Nat × BPair => if x.1 == k' then x.2 else BPair.unit)
        (if e.1 == k then (e.2.1, e.2.2) :: filt r k else filt r k)).oneValue
      ((if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit)
        + famFold BPair.add BPair.unit
          (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) r)
    cases he : (e.1 == k) with
    | true =>
      rw [if_pos rfl, Bool.true_and]
      show ((if e.2.1 == k' then e.2.2 else BPair.unit)
          + famFold BPair.add BPair.unit
            (fun x : Nat × BPair => if x.1 == k' then x.2 else BPair.unit)
            (filt r k)).oneValue
        ((if e.2.1 == k' then e.2.2 else BPair.unit)
          + famFold BPair.add BPair.unit
            (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) r)
      exact BPair.add_congr (BPair.oneValue_refl _) (filt_fold k k' r)
    | false =>
      rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
        Bool.false_and, if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
      show (famFold BPair.add BPair.unit
          (fun x : Nat × BPair => if x.1 == k' then x.2 else BPair.unit)
          (filt r k)).oneValue
        (BPair.unit + famFold BPair.add BPair.unit
          (fun e => if e.1 == k && e.2.1 == k' then e.2.2 else BPair.unit) r)
      exact BPair.oneValue_trans (filt_fold k k' r)
        (BPair.oneValue_symm (BPair.unit_add _))

/-- The substitutions at a key folded at a source read the weight's
entry at the key pair. -/
private theorem wtAt_filter (w : memtable.SMap) (k k' : Nat) :
    (famFold BPair.add BPair.unit
      (fun x : Nat × BPair => if x.1 == k' then x.2 else BPair.unit)
      (filt w k)).oneValue (memtable.wtAt w k k') :=
  BPair.oneValue_trans (filt_fold k k' w) (BPair.oneValue_symm (memtable.wtAt_read w k k'))

/-- The chains' fold reads the slots' product: at a grown monomial
the chains split at the head's substitutions, each chain's weight
the head's against the tail's, the head's fold the weight's entry
(`wtAt_filter`). -/
private theorem kerF_read (w : memtable.SMap) : ∀ m m' : List Nat,
    (kerF w m m').oneValue (kerW w m m')
  | [], [] => by
    show ((if ([] : List Nat) == [] then prodW [] else BPair.unit)
      + BPair.unit).oneValue (BPair.ofNat 1)
    rw [if_pos (show (([] : List Nat) == []) = true from rfl)]
    exact BPair.add_unit _
  | [], k' :: t' => by
    show ((if ([] : List Nat) == k' :: t' then prodW [] else BPair.unit)
      + BPair.unit).oneValue BPair.unit
    rw [if_neg (c := (([] : List Nat) == k' :: t') = true)
      (fun h => Bool.noConfusion (show (false : Bool) = true from h))]
    exact BPair.add_unit _
  | k :: t, m' => by
    show (famFold BPair.add BPair.unit
      (fun ch => if ch.map Prod.fst == m' then prodW ch else BPair.unit)
      ((filt w k).flatMap (fun x => (prodLists (subs w t)).map
        (fun l => x :: l)))).oneValue (kerW w (k :: t) m')
    refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ (filt w k)) ?_
    refine BPair.oneValue_trans (foldB_congr_members _ _ _ (fun x _ =>
      BPair.oneValue_of_eq (famFold_map BPair.add BPair.unit _
        (fun l => x :: l) (prodLists (subs w t))))) ?_
    cases m' with
    | nil =>
      refine foldB_null _ _ (fun x _ => foldB_null _ _ (fun ch' _ => ?_))
      show (if (x.1 :: ch'.map Prod.fst) == ([] : List Nat) then prodW (x :: ch')
        else BPair.unit).oneValue BPair.unit
      rw [if_neg (c := ((x.1 :: ch'.map Prod.fst) == ([] : List Nat)) = true)
        (fun h => Bool.noConfusion (show (false : Bool) = true from h))]
      exact BPair.oneValue_refl _
    | cons k' t' =>
      show (famFold BPair.add BPair.unit (fun x => famFold BPair.add BPair.unit
        (fun ch' => if (x.1 :: ch'.map Prod.fst) == k' :: t' then prodW (x :: ch')
          else BPair.unit) (prodLists (subs w t))) (filt w k)).oneValue
        (memtable.wtAt w k k' * kerW w t t')
      refine BPair.oneValue_trans (foldB_congr_members _
        (fun x : Nat × BPair => (if x.1 == k' then x.2 else BPair.unit) * kerF w t t')
        _ (fun x _ => ?_)) ?_
      · refine BPair.oneValue_trans (foldB_congr_members _ _ _ (fun ch' _ => ?_))
          (foldB_mul_left (if x.1 == k' then x.2 else BPair.unit)
            (fun ch' : List (Nat × BPair) =>
              if ch'.map Prod.fst == t' then prodW ch' else BPair.unit)
            (prodLists (subs w t)))
        show (if ((x.1 == k') && (ch'.map Prod.fst == t')) = true
            then prodW (x :: ch') else BPair.unit).oneValue
          ((if x.1 == k' then x.2 else BPair.unit)
            * (if ch'.map Prod.fst == t' then prodW ch' else BPair.unit))
        cases h1 : (x.1 == k') with
        | true =>
          cases h2 : (ch'.map Prod.fst == t') with
          | true =>
            rw [if_pos (by decide), if_pos rfl, if_pos rfl, prodW_cons]
            exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
          | false =>
            rw [if_neg (by decide), if_pos rfl,
              if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
            exact BPair.oneValue_symm (BPair.mul_unit _)
        | false =>
          rw [Bool.false_and, if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
            if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
          exact BPair.oneValue_symm (BPair.unit_mul _)
      · refine BPair.oneValue_trans
          (BPair.oneValue_symm (foldB_mul_right (kerF w t t') _ (filt w k))) ?_
        exact BPair.mul_congr (wtAt_filter w k k') (kerF_read w t t')

/-- The slots' product exchanges at a symmetric weight. -/
private theorem kerW_symm (w : memtable.SMap)
    (hs : ∀ t s, (memtable.wtAt w t s).oneValue (memtable.wtAt w s t)) :
    ∀ m m' : List Nat, (kerW w m m').oneValue (kerW w m' m)
  | [], [] => BPair.oneValue_refl _
  | [], _ :: _ => BPair.oneValue_refl _
  | _ :: _, [] => BPair.oneValue_refl _
  | k :: t, k' :: t' => BPair.mul_congr (hs k k') (kerW_symm w hs t t')

/-- The kernel exchanges at the symmetry read. -/
private theorem kerAt_symm (T : memtable.Table) (hw : memtable.symmWt T) (uw : Bool)
    (m m' : List Nat) : (kerAt T uw m m').oneValue (kerAt T uw m' m) := by
  cases uw with
  | true =>
    show (if m == m' then BPair.ofNat 1 else BPair.unit).oneValue
      (if m' == m then BPair.ofNat 1 else BPair.unit)
    rw [listBeqSymm m' m]
    exact BPair.oneValue_refl _
  | false => exact kerW_symm T.wt (memtable.wtAt_symm T hw) m m'

/-- A monomial's pairing against a vector reads the vector's fold
at the kernel: the coefficient's read at the unit weight, and the
chains' fold exchanged with the vector's fold otherwise. -/
private theorem monDotT_read (T : memtable.Table) (uw : Bool) (m : List Nat) (v : SVec) :
    (monDotT T uw m v).oneValue
      (famFold BPair.add BPair.unit (fun q => q.2 * kerAt T uw m q.1) v) := by
  cases uw with
  | true =>
    rw [show monDotT T true m v = coefAt m v from rfl]
    refine BPair.oneValue_trans (coefAt_read m v) ?_
    refine foldB_congr_members _ _ v (fun q _ => ?_)
    show (if q.1 == m then q.2 else BPair.unit).oneValue
      (q.2 * (if m == q.1 then BPair.ofNat 1 else BPair.unit))
    rw [listBeqSymm m q.1]
    cases hc : (q.1 == m) with
    | true =>
      rw [if_pos rfl, if_pos rfl]
      exact BPair.oneValue_symm (BPair.mul_ofNat_one _)
    | false =>
      rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
        if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
      exact BPair.oneValue_symm (BPair.mul_unit _)
  | false =>
    rw [show monDotT T false m v = (prodLists (subs T.wt m)).foldl
      (fun acc ch => acc + prodW ch * coefAt (ch.map Prod.fst) v) BPair.unit
      from rfl]
    have h1 := foldlFamO bpairFoldLaws
      (fun ch : List (Nat × BPair) => prodW ch * coefAt (ch.map Prod.fst) v)
      (prodLists (subs T.wt m)) BPair.unit
    have h2 : (famFold BPair.add BPair.unit
        (fun ch : List (Nat × BPair) => prodW ch * coefAt (ch.map Prod.fst) v)
        (prodLists (subs T.wt m))).oneValue
      (famFold BPair.add BPair.unit
        (fun ch : List (Nat × BPair) => famFold BPair.add BPair.unit
          (fun q : List Nat × BPair =>
            prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit)) v)
        (prodLists (subs T.wt m))) :=
      foldB_congr_members _ _ _ (fun ch _ =>
        BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl (prodW ch)) (coefAt_read _ v))
          (BPair.oneValue_symm (foldB_mul_left (prodW ch)
            (fun q : List Nat × BPair =>
              if q.1 == ch.map Prod.fst then q.2 else BPair.unit) v)))
    have h3 := foldB_swapL (fun (ch : List (Nat × BPair)) (q : List Nat × BPair) =>
      prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit))
      (prodLists (subs T.wt m)) v
    have h4 : (famFold BPair.add BPair.unit
        (fun q : List Nat × BPair => famFold BPair.add BPair.unit
          (fun ch : List (Nat × BPair) =>
            prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit))
          (prodLists (subs T.wt m))) v).oneValue
      (famFold BPair.add BPair.unit
        (fun q : List Nat × BPair => q.2 * kerW T.wt m q.1) v) :=
      foldB_congr_members _ _ v (fun q _ => by
        refine BPair.oneValue_trans ?_
          (BPair.mul_congr (BPair.oneValue_refl q.2) (kerF_read T.wt m q.1))
        refine BPair.oneValue_trans ?_ (foldB_mul_left q.2
          (fun ch : List (Nat × BPair) =>
            if ch.map Prod.fst == q.1 then prodW ch else BPair.unit)
          (prodLists (subs T.wt m)))
        refine foldB_congr_members _ _ _ (fun ch _ => ?_)
        show (prodW ch * (if q.1 == ch.map Prod.fst then q.2 else BPair.unit)).oneValue
          (q.2 * (if ch.map Prod.fst == q.1 then prodW ch else BPair.unit))
        rw [listBeqSymm q.1 (ch.map Prod.fst)]
        cases hc : (ch.map Prod.fst == q.1) with
        | true =>
          rw [if_pos rfl, if_pos rfl]
          exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
        | false =>
          rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
            if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
          exact BPair.oneValue_trans (BPair.mul_unit _)
            (BPair.oneValue_symm (BPair.mul_unit _)))
    exact BPair.oneValue_trans h1 (BPair.oneValue_trans (BPair.unit_add _)
      (BPair.oneValue_trans h2 (BPair.oneValue_trans h3 h4)))

/-- The weighted pairing as the first vector's fold at the
monomials' pairings. -/
private theorem dotT_read (T : memtable.Table) (uw : Bool) (u v : SVec) :
    (dotT T uw u v).oneValue
      (famFold BPair.add BPair.unit (fun p => p.2 * monDotT T uw p.1 v) u) := by
  rw [show dotT T uw u v
    = u.foldl (fun acc p => acc + p.2 * monDotT T uw p.1 v) BPair.unit from rfl]
  have h := foldlFamO bpairFoldLaws
    (fun p : List Nat × BPair => p.2 * monDotT T uw p.1 v) u BPair.unit
  exact BPair.oneValue_trans h (BPair.unit_add _)

/-- The weighted pairing exchanges at a symmetric weight: the two
vectors' double fold at the kernel exchanged, the kernel one value
at its two orders. -/
theorem dotT_comm (T : memtable.Table) (hw : memtable.symmWt T) (uw : Bool) (u v : SVec) :
    (dotT T uw u v).oneValue (dotT T uw v u) := by
  have hu := dotT_read T uw u v
  have hv := dotT_read T uw v u
  have h2 : (famFold BPair.add BPair.unit
      (fun p : List Nat × BPair => p.2 * monDotT T uw p.1 v) u).oneValue
      (famFold BPair.add BPair.unit
        (fun p : List Nat × BPair => famFold BPair.add BPair.unit
          (fun q : List Nat × BPair => p.2 * (q.2 * kerAt T uw p.1 q.1)) v) u) :=
    foldB_congr_members _ _ u (fun p _ =>
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl p.2) (monDotT_read T uw p.1 v))
        (BPair.oneValue_symm (foldB_mul_left p.2
          (fun q : List Nat × BPair => q.2 * kerAt T uw p.1 q.1) v)))
  have h3 := foldB_swapL
    (fun (p q : List Nat × BPair) => p.2 * (q.2 * kerAt T uw p.1 q.1)) u v
  have h4 : (famFold BPair.add BPair.unit
      (fun q : List Nat × BPair => famFold BPair.add BPair.unit
        (fun p : List Nat × BPair => p.2 * (q.2 * kerAt T uw p.1 q.1)) u) v).oneValue
      (famFold BPair.add BPair.unit
        (fun q : List Nat × BPair => q.2 * monDotT T uw q.1 u) v) :=
    foldB_congr_members _ _ v (fun q _ => by
      refine BPair.oneValue_trans ?_ (BPair.mul_congr (BPair.oneValue_refl q.2)
        (BPair.oneValue_symm (monDotT_read T uw q.1 u)))
      refine BPair.oneValue_trans ?_ (foldB_mul_left q.2
        (fun p : List Nat × BPair => p.2 * kerAt T uw q.1 p.1) u)
      refine foldB_congr_members _ _ u (fun p _ => ?_)
      show (p.2 * (q.2 * kerAt T uw p.1 q.1)).oneValue
        (q.2 * (p.2 * kerAt T uw q.1 p.1))
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
      exact BPair.mul_congr (BPair.oneValue_refl q.2)
        (BPair.mul_congr (BPair.oneValue_refl p.2) (kerAt_symm T hw uw p.1 q.1)))
  refine BPair.oneValue_trans hu ?_
  refine BPair.oneValue_trans h2 ?_
  refine BPair.oneValue_trans h3 ?_
  exact BPair.oneValue_trans h4 (BPair.oneValue_symm hv)

/-- A vector joined to a pool at the membership read within its
weight's group: the group's Gram with the vector at the weighted
pairing reads a determinant off the sum's unit (`elim.joinIndep`,
`lem:lowerspan`'s independence read), a member of the group's span
refused. -/
def tryAddT (T : memtable.Table) (sig : List Bool) (pool : List SVec)
    (v : SVec) : List SVec :=
  let w := weightV T sig v
  let group := pool.filter (fun h => weightV T sig h == w)
  let uw := unitWtRead T
  if elim.joinIndep (fun u v => (dotT T uw u v).norm) group v then pool ++ [v]
  else pool

/-- The lowering closure at a table and a signature from stated
seeds, each round joining the frontier's lowerings at the
membership read (`ground.closeBy`), a vacant lowering withdrawn. -/
def closeT (T : memtable.Table) (sig : List Bool) :
    Nat → List SVec → List SVec → List SVec :=
  ground.closeBy
    (fun v => ((List.range T.rank).map (fun i => lowerT T sig i v)).filter
      (fun w => w.length != 0))
    (tryAddT T sig)

/-- The lowering closure at the stored descents: `closeT`'s rounds
at the keyed pool's join, the frontier read off the pool. -/
def closeTS (T : memtable.Table) (sig : List Bool) :
    Nat → elim.PoolS SVec (List BPair) → List SVec →
      elim.PoolS SVec (List BPair) :=
  elim.closeK (fun a b : List BPair => a == b) (weightV T sig)
    (fun u v => (dotT T (unitWtRead T) u v).norm) (fun _ => false)
    (fun v => ((List.range T.rank).map (fun i => lowerT T sig i v)).filter
      (fun w => w.length != 0))

/-- A block at a table: the lowerings' span at a stated top
(`lem:lowerspan`), the collection from the top, the top joined at
the vacant pool's refusal and every lowering at the collection's,
the closure's fuel the top's slot count against the keys, the
closure run at the stored descents (`blockSpanT_eq` its read at
the fresh walk). -/
def blockSpanT (T : memtable.Table) (sig : List Bool) (top : SVec) : List SVec :=
  (closeTS T sig (sig.length * T.keys + 1)
    (elim.tryAddK (fun a b : List BPair => a == b) (weightV T sig)
      (fun u v => (dotT T (unitWtRead T) u v).norm) (fun _ => false)
      ([], []) top)
    [top]).1

/-- The block at the stored descents is the closure at the fresh
walk at a symmetric weight: the top's join at the vacant pool seeds
the trace, every join keeps it (`elim.closeK_eq_vacant` at the
pairing's exchange, `dotT_comm`), and the keyed join is the
membership read's own, the guard vacant. -/
theorem blockSpanT_eq (T : memtable.Table) (sig : List Bool) (top : SVec)
    (hw : memtable.symmWt T) :
    blockSpanT T sig top
      = closeT T sig (sig.length * T.keys + 1) (tryAddT T sig [] top) [top] :=
  (elim.closeK_eq_vacant (fun a b : List BPair => a == b) (weightV T sig)
    (fun u v => (dotT T (unitWtRead T) u v).norm) (fun _ => false)
    (fun _ _ h => ground.listBeqEq h) ground.listEqBeq
    (fun u v => BPair.oneValue_trans (BPair.norm_oneValue _)
      (BPair.oneValue_trans (dotT_comm T hw (unitWtRead T) u v)
        (BPair.oneValue_symm (BPair.norm_oneValue _))))
    (fun v => ((List.range T.rank).map (fun i => lowerT T sig i v)).filter
      (fun w => w.length != 0))
    (sig.length * T.keys + 1) top [top]).trans
  (ground.closeByS_proj
    (fun v => ((List.range T.rank).map (fun i => lowerT T sig i v)).filter
      (fun w => w.length != 0))
    (elim.tryAddL (fun a b : List BPair => a == b) (weightV T sig)
      (fun u v => (dotT T (unitWtRead T) u v).norm) (fun _ => false))
    (tryAddT T sig) (fun l => l) (fun _ => True)
    (fun _ _ _ => trivial) (fun _ _ _ => rfl)
    (sig.length * T.keys + 1) (tryAddT T sig [] top) [top] trivial).2

/-- The fused span at a table over stated end blocks, each with its
signature, grouped at the ends' weight lists: the blocks' tensors
at the unit weight, the families at one weight list one group. -/
def fusedGroupsT (T : memtable.Table) (ends : List (List Bool × List SVec)) :
    List (List SVec) :=
  let combos := ends.foldl
    (fun (P : List (List SVec × List (List BPair) × List BPair)) e =>
      let blk := e.2.map (fun v => (v, weightV T e.1 v))
      P.flatMap (fun t => blk.map (fun b =>
        (t.1 ++ [b.1], t.2.1 ++ [b.2],
         List.zipWith (fun x y => (x + y).norm) t.2.2 b.2))))
    [([], [], List.replicate T.rank BPair.unit)]
  let unit := combos.filter (fun t => t.2.2.all (fun x => decide (x.oneValue BPair.unit)))
  (ground.dedupF (unit.map (fun t => t.2.1))).map (fun key =>
    (unit.filter (fun t => t.2.1 == key)).map (fun t =>
      t.1.foldl tensorV unitV))

/-- The fused span at a table, its groups joined. -/
def fusedSpanT (T : memtable.Table) (ends : List (List Bool × List SVec)) :
    List SVec :=
  (fusedGroupsT T ends).flatMap (fun g => g)

/-- The stacked raisings' rows over a pool at a table: per simple
index and per occupied image monomial, one row at the members'
image coefficients. -/
def raiseRowsT (T : memtable.Table) (sig : List Bool) (pool : List SVec) :
    elim.Mat :=
  (List.range T.rank).flatMap (fun i =>
    let imgs := pool.map (raiseT T sig i)
    (ground.dedupF (imgs.flatMap (fun im => im.map Prod.fst))).map (fun m =>
      imgs.map (coefAt m)))

/-- The invariants over a pool at a table: the stacked raisings'
kernel list at the back solve, one member per pivot-free column. -/
def kernelT (T : memtable.Table) (sig : List Bool) (pool : List SVec) :
    List (List BPair) :=
  elim.kernelList pool.length (raiseRowsT T sig pool)

/-- A combination over a pool, the coefficients' scaled sum
collected. -/
def comboV (pool : List SVec) (k : List BPair) : SVec :=
  collect ((List.zipWith (fun v c => (v, c)) pool k).flatMap (fun p =>
    p.1.map (fun q => (q.1, q.2 * p.2))))

/-- The kernel list over a pool at a table, each member at its
primitive representative. -/
def kernelVecs (T : memtable.Table) (sig : List Bool) (pool : List SVec) :
    List SVec :=
  (kernelT T sig pool).map (fun k => prim (comboV pool k))

/-- The Gram-dual solve of a vector over a pool at the weighted
pairing: the bordered Gram's kernel at the primitive
representative, the coefficients with the last coordinate's margin
the clearing (`elim.solveK`, `def:elim`'s bordered descent at one
stated pairing vector), one member at an independent pool, its
last coordinate the crossed pivots' product on the upper side at
the definite Gram. -/
def spanCoeffsT (T : memtable.Table) (pool : List SVec) (g : SVec) :
    List BPair × Pos :=
  let uw := unitWtRead T
  let G := gramT T pool
  let b := pool.map (fun u => dotT T uw u g)
  let k0 := elim.solveK G b
  let k := BPair.listPrim (BPair.listContent k0) k0
  (k.take pool.length,
   posOfSucc (BPair.marginN (getAt BPair.unit k pool.length) - 1))

/-- The span membership read (`lem:lowerspan`'s residual): the
vector at the solve's clearing one value with its solved
combination over the pool. -/
def spanMemberT (T : memtable.Table) (pool : List SVec) (g : SVec) : Bool :=
  let c := spanCoeffsT T pool g
  oneValueV (scaleV (BPair.ofPos c.2) g) (comboV pool c.1)

/-- The projection onto a pool's span at the weighted pairing, the
solved combination with its clearing. -/
def projectT (T : memtable.Table) (pool : List SVec) (g : SVec) : SVec × Pos :=
  let c := spanCoeffsT T pool g
  (comboV pool c.1, c.2)

/-- A projection at its reduced representative: the coefficients
and the clearing divided at their shared count, one value at the
homogeneity principle. -/
def reduceV (p : SVec × Pos) : SVec × Pos :=
  let k := BPair.sharedCount (p.1.map Prod.snd) p.2
  (List.zipWith (fun q c => (q.1, c)) p.1 (BPair.listPrim k (p.1.map Prod.snd)),
   posOfSucc (posVal p.2 / k - 1))

/-- The projection onto the fused span at its groups, the ends'
weight lists' grading orthogonal (`fusedGroupsT`): each occupied
group's Gram-dual solve at its own clearing, the vector the groups'
solves each scaled by the further groups' clearings at the
clearings' product, reduced. -/
def projectGroupsT (T : memtable.Table) (groups : List (List SVec)) (g : SVec) :
    SVec × Pos :=
  let prs := (groups.map (fun pool => projectT T pool g)).filter (fun p =>
    p.1.length != 0)
  let c := prs.foldl (fun acc p => acc * p.2) Pos.one
  reduceV (collect ((List.range prs.length).flatMap (fun i =>
    let p := getAt ([], Pos.one) prs i
    let others := (List.range prs.length).foldl (fun a j =>
      if j == i then a else a * (getAt ([], Pos.one) prs j).2) Pos.one
    p.1.map (fun q => (q.1, q.2 * BPair.ofPos others)))), c)

/-- The paired tensor of a stated matrix at stated slot pairs over
a power's slots: per pair `(i, j)` the matrix's entries at the two
slots, the product over the pairs, one monomial per entry
assignment. -/
def pairTensor (c : memtable.SMap) (pairs : List (Nat × Nat)) (n : Nat) : SVec :=
  pairs.foldl (fun acc ij =>
    acc.flatMap (fun p => c.map (fun e =>
      ((p.1.set ij.1 e.1).set ij.2 e.2.1, (p.2 * e.2.2).norm))))
    [(List.replicate n 0, BPair.ofNat 1)]

/-- The through pairing at a table of two ends at opposite
orientations over stated slot pairs: the weight's cleared partner
per pair, `Σ wtInv_{kk'} e_k ⊗ e_{k'}`, cleared at the weight's
clearing to the pairs' count (`con:slotpower`'s through pairing at
the table's keys, the coevaluation's tensor before the
projection). -/
def throughT (T : memtable.Table) (pairs : List (Nat × Nat)) (n : Nat) : SVec × Pos :=
  (pairTensor T.wtInv pairs n, posOfSucc (T.wtDet ^ pairs.length - 1))

/-- The through pairing at a table of two ends of one orientation
over stated slot pairs: the dual pair per pair, cleared at its
clearing to the pairs' count (`con:memtable`), vacant at a table
without one. -/
def dualThroughT (T : memtable.Table) (pairs : List (Nat × Nat)) (n : Nat) :
    Option (SVec × Pos) :=
  T.dual.map (fun d => (pairTensor d.1 pairs n, posOfSucc (posVal d.2 ^ pairs.length - 1)))

/-! The letters' own devices. -/

/-- The dual wedge at a complement length: the wedge on the last
letters, each arrangement on its permutation's side. -/
def dualWedge (d m : Nat) : HVec :=
  blockcount.wedgeC ((List.range d).map (fun i => if d - m ≤ i then 1 else 0))

/-- A label's top at its word pair: the top columns' wedges on the
undaggered slots tensored with the bottom columns' dual wedges on
the daggered. -/
def blockTop (d : Nat) (s : Shape) : HVec :=
  (botCols d s).foldl (fun acc l => tensorH acc (dualWedge d (d - l)))
    ((topCols d s).foldl (fun acc l => tensorH acc (wedge d l))
      ⟨List.replicate d 0, [BPair.ofNat 1]⟩)

/-- A label's block at its word pair, the lowerings' span at its
top at the letters' table. -/
def blockSpanAt (d : Nat) (s : Shape) : List SVec :=
  blockSpanT (memtable.lettersT d) (labelSig d s) (ofH (blockTop d s))

/-- A label's block at the letters' table is the closure at the
fresh walk from the top's own join, the letters' weight symmetric
(`memtable.lettersT_symm`). -/
theorem blockSpanAt_eq (d : Nat) (s : Shape) :
    blockSpanT (memtable.lettersT d) (labelSig d s) (ofH (blockTop d s))
      = closeT (memtable.lettersT d) (labelSig d s)
          ((labelSig d s).length * (memtable.lettersT d).keys + 1)
          (tryAddT (memtable.lettersT d) (labelSig d s) [] (ofH (blockTop d s)))
          [ofH (blockTop d s)] :=
  blockSpanT_eq _ _ _ (memtable.lettersT_symm d)

/-- The letters' end blocks at a vertex: per end its signature with
its label's block. -/
def endBlocks (d : Nat) (es : List (Shape × Bool)) : List (List Bool × List SVec) :=
  es.map (fun e => (endSig d e, blockSpanAt d e.1))

/-- A wiring's tensor at a signature: one letter per row end, read
again at the column end it pairs, one monomial per letter
assignment. -/
def wiringG (d : Nat) (sig : List Bool) (σ : List Nat) : SVec :=
  let U := upSlots sig
  let D := downSlots sig
  (allMon d U.length).map (fun ls =>
    ((List.range U.length).foldl (fun m r =>
      (m.set (getAt 0 U r) (getAt 0 ls r)).set (getAt 0 D (getAt 0 σ r))
        (getAt 0 ls r)) (List.replicate sig.length 0), BPair.ofNat 1))

/-- A column layout at stated columns, the top word's against the
bottom's, each column at its key and length: per column its key
with its slots in the vertex, the top columns' slots at their
lengths then the bottom columns' at the complement lengths, from a
stated offset. -/
def layoutOf (d : Nat) (c : List (Nat × Nat) × List (Nat × Nat)) (off : Nat) :
    List (Nat × List Nat) :=
  (c.1.foldl (fun acc l =>
      (acc.1 ++ [(l.1, (List.range l.2).map (fun i => acc.2 + i))], acc.2 + l.2))
    (([] : List (Nat × List Nat)), off)
  |> fun t => c.2.foldl (fun acc l =>
      (acc.1 ++ [(l.1, (List.range (d - l.2)).map (fun i => acc.2 + i))],
       acc.2 + (d - l.2)))
    t).1

/-- A label's columns at the letters, each at its length for its
key: the top columns against the bottom columns. -/
def labelCols (d : Nat) (s : Shape) : List (Nat × Nat) × List (Nat × Nat) :=
  ((topCols d s).map (fun l => (l, l)), (botCols d s).map (fun l => (l, l)))

/-- An end's column layout, its label's columns at the offset. -/
def colLayout (d : Nat) (e : Shape) (off : Nat) : List (Nat × List Nat) :=
  layoutOf d (labelCols d e) off

/-- The column match of two layouts at a stated key dual: per
column of the first the partner in the second, at the dual key
where the two ends' traversals exchange and at the key itself
where they agree, the first unused match consumed, and the tie
flag at an exchanged match of a self-dual key; at the letters the
key a column's length and its dual the complement length. -/
def colMatch (dualKey : Nat → Nat) (rev : Bool) :
    List (Nat × List Nat) → List (Nat × List Nat) →
    List (List Nat × List Nat × Bool)
  | [], _ => []
  | (l, A) :: t, R =>
    let want := if rev then dualKey l else l
    match R.foldl
        (fun (acc : Option (Nat × List Nat) × List (Nat × List Nat)) c =>
          match acc.1 with
          | some _ => (acc.1, acc.2 ++ [c])
          | none =>
            if c.1 == want then (some c, acc.2) else (none, acc.2 ++ [c]))
        (none, []) with
    | (some c, rest) => (A, c.2, rev && (dualKey l == l)) :: colMatch dualKey rev t rest
    | (none, _) => []

/-- The star's family at a stated arrangement of letters
(`con:slotpower`'s star): every arrangement of the letters off it,
the withdrawn content's words (`places.withdrawn`), each at the
swap grading's side of the concatenated arrangement, vacant at a
letter repeated or beyond the count (`starFam_perms` its read at
the permutations opening at the arrangement). -/
def starFam (d : Nat) (I : List Nat) : List (List Nat × BPair) :=
  if wordOccupied I (List.replicate d 1) then
    (monomialsAt (withdrawn I (List.replicate d 1))).map (fun q =>
      (q, if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1))
  else []

/-- The star's family is the permutations opening at the
arrangement, each at its tail and its own side
(`places.monomialsAt_prefix` at the unit content). -/
theorem starFam_perms (d : Nat) (I : List Nat) :
    starFam d I = (perms d).filterMap (fun ls =>
      if ls.take I.length == I then
        some (ls.drop I.length,
          if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1)
      else none) := by
  rw [ground.filterMap_ite (fun ls : List Nat => ls.take I.length == I)
    (fun ls => (ls.drop I.length,
      if parity ls then (BPair.ofNat 1).swap else BPair.ofNat 1))]
  show starFam d I
    = ((monomialsAt (List.replicate d 1)).filter
        (fun ls => ls.take I.length == I)).map _
  rw [monomialsAt_prefix I (List.replicate d 1)]
  show (if wordOccupied I (List.replicate d 1) then
      (monomialsAt (withdrawn I (List.replicate d 1))).map (fun q =>
        (q, if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1))
    else []) = _
  cases hw : wordOccupied I (List.replicate d 1) with
  | true =>
    rw [if_pos rfl, if_pos rfl, ground.map_map]
    refine ground.map_congr_all _ _ (fun q => ?_) _
    show (q, if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1)
      = ((I ++ q).drop I.length,
        if parity (I ++ q) then (BPair.ofNat 1).swap else BPair.ofNat 1)
    rw [ground.drop_append_self]
  | false =>
    rw [if_neg (fun h : (false : Bool) = true => Bool.noConfusion h),
      if_neg (fun h : (false : Bool) = true => Bool.noConfusion h)]
    rfl

/-- The star at a tie column's slots on a vector: every occupied
monomial's letters at the slots read to every arrangement of the
complementary set at the swap grading's side, the coefficient
scaled, the clearing at the column length's factorial the reader's
own (`con:slotpower`'s star as the tie column's map between its
two actions). -/
def starAt (d : Nat) (slots : List Nat) (v : SVec) : SVec :=
  collect (v.flatMap (fun p =>
    (starFam d (slots.map (fun s => getAt 0 p.1 s))).map (fun q =>
      ((List.zipWith (fun s l => (s, l)) slots q.1).foldl
        (fun m sl => m.set sl.1 sl.2) p.1, p.2 * q.2))))

/-- The transport's slot map at a moved end (`thm:pairpencil`'s
terms' transport) at a stated key dual: the moved end's columns
matched to the source end's, a column against the column of its
own key at a traversal kept and against the dual key at a
traversal reversed (`colMatch`), each moved slot at the matched
source slot in order, with the tie columns' slot groups at a
reversed traversal, the star's at the letters. -/
def transportSlots (dualKey : Nat → Nat) (rev : Bool)
    (src tgt : List (Nat × List Nat)) : List Nat × List (List Nat) :=
  let pairs := colMatch dualKey rev tgt src
  (pairs.flatMap (fun p => p.2.1),
   (pairs.filter (fun p => p.2.2)).map (fun p => p.1))

/-- A column pair's family: at a wiring one member per letter list,
the letters at the paired slots agreeing, and at the star one
member per arrangement of the letters over the two columns, the
complementary letter sets at the swap grading's side (`starFam`);
each member its slot assignments with its coefficient. -/
private def pairFam (d : Nat) (p : List Nat × List Nat × Bool) :
    List (List (Nat × Nat) × BPair) :=
  if p.2.2 then
    (allMon d p.1.length).flatMap (fun I =>
      (starFam d I).map (fun q =>
        (List.zipWith (fun s l => (s, l)) p.1 I
          ++ List.zipWith (fun s l => (s, l)) p.2.1 q.1, q.2)))
  else
    (allMon d p.1.length).map (fun ls =>
      (List.zipWith (fun s l => (s, l)) p.1 ls
        ++ List.zipWith (fun s l => (s, l)) p.2.1 ls,
       BPair.ofNat 1))

/-- The through pairing of two ends at dual labels at the letters:
each column's slots against its complement column's, a wiring at
an undaggered slot against a daggered one and the star at a tie
column, the tensor the column pairs' families' product cleared at
the tie columns' factorials; vacant off the dual pair. -/
def throughPair (d : Nat) (e1 e2 : Shape × Bool) : SVec × Pos :=
  let same := e1.2 == e2.2
  let ok := if same then labels.reduce e2.1 == labels.reduce (labels.dualL e1.1)
    else labels.reduce e2.1 == labels.reduce e1.1
  let n1 := (labelSig d e1.1).length
  let n := n1 + (labelSig d e2.1).length
  let pairs := colMatch (fun l => d - l) same (colLayout d e1.1 0) (colLayout d e2.1 n1)
  if !ok || pairs.length != (cols e1.1).length then ([], Pos.one)
  else
    let clear := pairs.foldl (fun acc p =>
      if p.2.2 then acc * factorial p.1.length else acc) 1
    let fam := pairs.foldl (fun acc p =>
      acc.flatMap (fun a =>
        (pairFam d p).map (fun b => (a.1 ++ b.1, a.2 * b.2))))
      [(([] : List (Nat × Nat)), BPair.ofNat 1)]
    (collect (fam.map (fun a =>
      (a.1.foldl (fun m sl => m.set sl.1 sl.2) (List.replicate n 0), a.2))),
     posOfSucc (clear - 1))

end slotpower
