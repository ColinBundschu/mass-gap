import MassGap.Fusion
import MassGap.Lattice
/-!
`def:carrier` — the carrier's index layer, built from the fusion
interface's fields alone over the lattice interface's region: a
configuration assigns a label per link key, the unit label the
unoccupied read and the support the nonunit keys (`support`),
occupied by the shape of its data (`idx` filters at an occupied
support); its content is the support's Casimir fold at the
cleared second member (`contentN`); a touched vertex is a support endpoint, and a
vertex's multiplicity is the invariant count of the incident
support labels' product, the incoming links dualized (`vmult`),
the count the fusion rows' fold (`invCount`, the row expansion one
label at a time); a configuration is occupied where every touched
vertex reads a positive multiplicity; and the window index at the
region and cutoff is the occupied configurations at content at or
below the cutoff (`idx`, the enumeration over the interface's
below-cutoff labels per link), with the content-pruned fast read
beside it (`idxA`, a link label refused at the step where the
running content passes the cutoff, `idxA_eq` the identity).  The
fibers, the pairing and the colimit land with their consumers (`prop:leastwindow`,
`def:algebra`'s product and `def:pencil`'s operators at the
algebra layer).
-/

namespace carrier
open ground lattice fusion

/-- The filter reads through a keyed union, member family by member
family. -/
private theorem filter_flatMap {α β : Type} (f : α → List β) (p : β → Bool) :
    ∀ l : List α, (l.flatMap f).filter p = l.flatMap (fun x => (f x).filter p)
  | [] => rfl
  | x :: t => by
    show (f x ++ t.flatMap f).filter p
      = (f x).filter p ++ t.flatMap (fun y => (f y).filter p)
    rw [filter_append p (f x) (t.flatMap f), filter_flatMap f p t]

/-- Two filters in succession read the conjoined predicate, the
outer one applied at the inner's survivors. -/
private theorem filter_filter {α : Type} (p q : α → Bool) :
    ∀ l : List α, (l.filter q).filter p = l.filter (fun a => q a && p a)
  | [] => rfl
  | a :: t => by
    show (match q a with
          | true => a :: t.filter q
          | false => t.filter q).filter p
       = (match q a && p a with
          | true => a :: t.filter (fun b => q b && p b)
          | false => t.filter (fun b => q b && p b))
    cases hq : q a with
    | false => exact filter_filter p q t
    | true =>
      show (match p a with
            | true => a :: (t.filter q).filter p
            | false => (t.filter q).filter p)
         = (match p a with
            | true => a :: t.filter (fun b => q b && p b)
            | false => t.filter (fun b => q b && p b))
      cases hp : p a with
      | false => exact filter_filter p q t
      | true => exact congrArg (List.cons a) (filter_filter p q t)

/-- Predicates agreeing at every member filter alike. -/
private theorem filter_congr {α : Type} (p q : α → Bool) (h : ∀ a, p a = q a) :
    ∀ l : List α, l.filter p = l.filter q
  | [] => rfl
  | a :: t => by
    show (match p a with
          | true => a :: t.filter p
          | false => t.filter p)
       = (match q a with
          | true => a :: t.filter q
          | false => t.filter q)
    rw [h a, filter_congr p q h t]


/-- The content's one step: an occupied label joins its Casimir
read, the unit passes. -/
private def contentStep {L : Type} (F : Data L) (acc : Nat) (l : L) : Nat :=
  if F.eqL l F.unit then acc else acc + F.c2N l

/-- The content at the cleared second member: the support's
Casimir fold, the unoccupied keys the sum's unit. -/
def contentN {L : Type} (F : Data L) (a : List L) : Nat :=
  a.foldl (contentStep F) 0

/-- The occupied keys below a stated bound: the range's filter at
the occupancy read, the support filter's one body. -/
def occKeys {L : Type} (F : Data L) (n : Nat) (a : List L) :
    List Nat :=
  (List.range n).filter (fun l =>
    !(F.eqL (ground.getAt F.unit a l) F.unit))

/-- The support read: the occupied links, `def:carrier`'s finitely
many at the region's key range. -/
def support {L : Type} (F : Data L) (R : Region) (a : List L) :
    List Nat :=
  occKeys F R.links a

private def invGo {L : Type} (F : Data L) :
    Nat → List L → Nat
  | 0, [] => 1
  | 0, [l] => if F.eqL l F.unit then 1 else 0
  | 0, [l1, l2] => if F.eqL l1 (F.dual l2) then 1 else 0
  | 0, _ :: _ :: _ :: _ => 0
  | _ + 1, [] => 1
  | _ + 1, [l] => if F.eqL l F.unit then 1 else 0
  | _ + 1, [l1, l2] => if F.eqL l1 (F.dual l2) then 1 else 0
  | fuel + 1, l1 :: l2 :: l3 :: rest =>
    (F.row l1 l2).foldl (fun acc c =>
      acc + F.count l1 l2 c * invGo F fuel (c :: l3 :: rest)) 0

/-- The invariant count of a label list's product: the fusion
rows' fold, one label absorbed per step, the pair's read the unit
law `N^𝟏_{ab} = δ_{a b̄}` (`prop:repring`'s first read, the
route `prop:windowfinite` names for the vertex multiplicity), the
list's length the fold's own fuel. -/
def invCount {L : Type} (F : Data L) (ls : List L) : Nat :=
  invGo F ls.length ls

/-- A single label at a positive invariant count is the unit: the
one-label read is the unit's own Kronecker delta. -/
theorem invCount_one_pos {L : Type} (F : Data L) (l : L)
    (h : 0 < invCount F [l]) : F.eqL l F.unit = true := by
  cases hb : F.eqL l F.unit with
  | true => rfl
  | false =>
    have h0 : invCount F [l] = 0 := by
      show (if F.eqL l F.unit then 1 else 0) = 0
      rw [hb]
      exact rfl
    rw [h0] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- A label pair at a positive invariant count is dual: the pair's
read is the unit law `N^𝟏_{ab} = δ_{a b̄}`. -/
theorem invCount_pair_pos {L : Type} (F : Data L) (l1 l2 : L)
    (h : 0 < invCount F [l1, l2]) : F.eqL l1 (F.dual l2) = true := by
  cases hb : F.eqL l1 (F.dual l2) with
  | true => rfl
  | false =>
    have h0 : invCount F [l1, l2] = 0 := by
      show (if F.eqL l1 (F.dual l2) then 1 else 0) = 0
      rw [hb]
      exact rfl
    rw [h0] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- The count's row expansion at three labels or more: the leading
pair absorbs into its row, the fold weighting each row member by
its fusion count against the count of the shortened list. -/
theorem invCount_cons {L : Type} (F : Data L) (l1 l2 l3 : L)
    (rest : List L) :
    invCount F (l1 :: l2 :: l3 :: rest)
      = (F.row l1 l2).foldl (fun acc c =>
          acc + F.count l1 l2 c * invCount F (c :: l3 :: rest)) 0 := rfl

/-- Two configurations' equality at the interface's label equality,
the index's own read. -/
def eqConf {L : Type} (F : Data L) : List L → List L → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | a :: s, b :: t => F.eqL a b && eqConf F s t

/-- A configuration's membership in a stated family at the
interface equality, the fold over the members. -/
def confMem {L : Type} (F : Data L) (a : List L) :
    List (List L) → Bool
  | [] => false
  | b :: t => eqConf F a b || confMem F a t

/-- The incident support labels at a vertex, the incoming links
dualized, the unoccupied keys withdrawn at the support read. -/
def incidentLabels {L : Type} (F : Data L) (R : Region)
    (a : List L) (v : Nat) : List L :=
  (incident R v).filterMap (fun e =>
    let l := getAt F.unit a e.1
    if F.eqL l F.unit then none
    else if e.2 then some l else some (F.dual l))

/-- The vertex multiplicity: the invariant count of the incident
labels' product. -/
def vmult {L : Type} (F : Data L) (R : Region) (a : List L)
    (v : Nat) : Nat :=
  invCount F (incidentLabels F R a v)

/-- At a vertex reading no incident label the multiplicity is the
product's unit. -/
theorem vmult_vacant {L : Type} (F : Data L) (R : Region)
    (c : List L) (v : Nat)
    (h : ((incidentLabels F R c v).length != 0) = false) :
    vmult F R c v = 1 := by
  have hb : ((incidentLabels F R c v).length == 0) = true := by
    cases hc : ((incidentLabels F R c v).length == 0) with
    | true => rfl
    | false =>
      rw [show ((incidentLabels F R c v).length != 0)
          = !((incidentLabels F R c v).length == 0) from rfl,
        hc] at h
      exact Bool.noConfusion h
  have h0 : incidentLabels F R c v = [] :=
    ground.nil_of_length_zero _ (ground.beqEqOf hb)
  show invCount F (incidentLabels F R c v) = 1
  rw [h0]
  rfl

/-- The touched vertices, the support's endpoints. -/
def touched {L : Type} (F : Data L) (R : Region) (a : List L) :
    List Nat :=
  (List.range R.verts).filter (fun v =>
    (incidentLabels F R a v).length != 0)

/-- The occupied read: every touched vertex at a positive
multiplicity. -/
def occupied {L : Type} (F : Data L) (R : Region) (a : List L) :
    Bool :=
  (touched F R a).all (fun v => 0 < vmult F R a v)

/-- A vertex's multiplicity at an occupied configuration is
positive: a touched vertex joins the touched list at its occupied
incident read with the occupied fold reading it there, and an
untouched vertex reads the product's unit. -/
theorem vmult_pos {L : Type} (F : Data L) (R : Region) (a : List L)
    (v : Nat) (hv : v < R.verts)
    (ha : occupied F R a = true) : 0 < vmult F R a v := by
  cases hlen : ((incidentLabels F R a v).length != 0) with
  | false =>
    rw [vmult_vacant F R a v hlen]
    exact Nat.succ_pos 0
  | true =>
    have hmem : v ∈ touched F R a :=
      ground.mem_filter_to _ (ground.memRange hv) hlen
    have hall : (touched F R a).all
        (fun w => decide (0 < vmult F R a w)) = true := ha
    exact of_decide_eq_true (ground.all_of_mem _ _ hall v hmem)

private def assigns {L : Type} (F : Data L) (C : Nat) :
    Nat → List (List L)
  | 0 => [[]]
  | n + 1 => (assigns F C n).flatMap (fun a =>
      (F.unit :: F.below C).map (fun l => l :: a))

/-- The window index at the region and cutoff: the occupied
configurations at an occupied support and content at or below the
cutoff, enumerated over the interface's below-cutoff labels per
link. -/
def idx {L : Type} (F : Data L) (R : Region) (C : Nat) :
    List (List L) :=
  (assigns F C R.links).filter (fun a =>
    (a.any (fun l => !(F.eqL l F.unit)))
      && contentN F a ≤ C
      && occupied F R a)

/-! The window index's fast read beside the enumeration itself: the
content over the naturals is a sum, so a longer configuration prices
at or above its own tail (`contentN_cons`) and a partial assignment
already beyond the cutoff admits no completion within it.  The
pruned enumeration therefore refuses a link label at the step where
the running content passes the cutoff, threading that content
alongside the partial assignment, while the any-nonunit and occupied
reads ride at the leaves as `idx` has them; `idxA_eq` reads the two
at every interface, region and cutoff. -/

/-- The content's step at one link label: the unoccupied key at the
sum's unit, an occupied one at its Casimir. -/
private def stepN {L : Type} (F : Data L) (l : L) : Nat :=
  if F.eqL l F.unit then 0 else F.c2N l

/-- The content step at its additive spelling: an occupied label's
read joins as the sum's own term, the unit at the count's unit. -/
private theorem contentStep_add {L : Type} (F : Data L) :
    ∀ (acc : Nat) (l : L), contentStep F acc l
      = acc + (if F.eqL l F.unit then 0 else F.c2N l) := by
  intro acc l
  show (if F.eqL l F.unit then acc else acc + F.c2N l)
    = acc + (if F.eqL l F.unit then 0 else F.c2N l)
  cases F.eqL l F.unit with
  | true => rfl
  | false => rfl

/-- The seed hoists out of the content fold (`ground.foldlSeed` at
the step's additive spelling). -/
private theorem contentAcc {L : Type} (F : Data L)
    (a : List L) (k : Nat) :
    a.foldl (contentStep F) k = k + a.foldl (contentStep F) 0 := by
  rw [ground.foldl_congr (contentStep F) _ (contentStep_add F) a k,
    ground.foldl_congr (contentStep F) _ (contentStep_add F) a 0,
    ground.foldlSeed (fun l => if F.eqL l F.unit then 0 else F.c2N l) a k,
    ground.foldlSeed (fun l => if F.eqL l F.unit then 0 else F.c2N l) a 0,
    Nat.zero_add]


private theorem stepN_read {L : Type} (F : Data L) (l : L) :
    contentStep F 0 l = stepN F l := by
  show (if F.eqL l F.unit then 0 else 0 + F.c2N l)
    = (if F.eqL l F.unit then 0 else F.c2N l)
  cases hl : F.eqL l F.unit with
  | true => rfl
  | false =>
    show 0 + F.c2N l = F.c2N l
    exact Nat.zero_add (F.c2N l)

private theorem contentN_cons {L : Type} (F : Data L) (l : L) (a : List L) :
    contentN F (l :: a) = contentN F a + stepN F l := by
  show a.foldl (contentStep F) (contentStep F 0 l)
    = a.foldl (contentStep F) 0 + stepN F l
  rw [contentAcc F a (contentStep F 0 l), stepN_read F l,
    Nat.add_comm (stepN F l) (a.foldl (contentStep F) 0)]

private theorem contentN_le {L : Type} (F : Data L) (l : L) (a : List L) :
    contentN F a ≤ contentN F (l :: a) := by
  rw [contentN_cons F l a]
  exact Nat.le_add_right (contentN F a) (stepN F l)

private def assignsA {L : Type} (F : Data L) (C : Nat) :
    Nat → List (Nat × List L)
  | 0 => [(0, [])]
  | n + 1 => (assignsA F C n).flatMap (fun p =>
      ((F.unit :: F.below C).map
          (fun l => (p.1 + stepN F l, l :: p.2))).filter
        (fun r => decide (r.1 ≤ C)))

private theorem extLeaf {L : Type} (F : Data L) (C : Nat) (a : List L)
    (ls : List L) :
    ((ls.map (fun l => (contentN F a + stepN F l, l :: a))).filter
        (fun r => decide (r.1 ≤ C)))
      = ((ls.map (fun l => l :: a)).filter
          (fun b => decide (contentN F b ≤ C))).map
            (fun b => (contentN F b, b)) := by
  rw [map_congr_all (fun l => (contentN F a + stepN F l, l :: a))
      (fun l => (contentN F (l :: a), l :: a))
      (fun l => by rw [contentN_cons F l a]) ls,
    ← map_map (fun l => l :: a) (fun b => (contentN F b, b)) ls]
  exact filter_map (fun b => (contentN F b, b))
    (fun r => decide (r.1 ≤ C)) (ls.map (fun l => l :: a))

private theorem extEmpty {L : Type} (F : Data L) (C : Nat) (a : List L)
    (h : ¬ (contentN F a ≤ C)) : ∀ ls : List L,
      (ls.map (fun l => l :: a)).filter
        (fun b => decide (contentN F b ≤ C)) = []
  | [] => rfl
  | l :: t => by
    have hne : ¬ (contentN F (l :: a) ≤ C) := fun hle =>
      h (Nat.le_trans (contentN_le F l a) hle)
    have hd : decide (contentN F (l :: a) ≤ C) = false := by
      cases hb : decide (contentN F (l :: a) ≤ C) with
      | true => exact absurd (of_decide_eq_true hb) hne
      | false => rfl
    show (match decide (contentN F (l :: a) ≤ C) with
          | true => (l :: a) :: (t.map (fun x => x :: a)).filter
              (fun b => decide (contentN F b ≤ C))
          | false => (t.map (fun x => x :: a)).filter
              (fun b => decide (contentN F b ≤ C))) = []
    rw [hd]
    exact extEmpty F C a h t

private theorem prunePass {L : Type} (F : Data L) (C : Nat)
    (G H : List L → List (Nat × List L))
    (hpos : ∀ a : List L, G a = H a)
    (hneg : ∀ a : List L, decide (contentN F a ≤ C) = false → H a = []) :
    ∀ l : List (List L),
      (l.filter (fun a => decide (contentN F a ≤ C))).flatMap G
        = l.flatMap H
  | [] => rfl
  | a :: t => by
    show (match decide (contentN F a ≤ C) with
          | true => a :: t.filter (fun b => decide (contentN F b ≤ C))
          | false => t.filter (fun b => decide (contentN F b ≤ C))).flatMap G
      = H a ++ t.flatMap H
    cases hd : decide (contentN F a ≤ C) with
    | true =>
      show G a ++ (t.filter (fun b => decide (contentN F b ≤ C))).flatMap G
        = H a ++ t.flatMap H
      rw [hpos a, prunePass F C G H hpos hneg t]
    | false =>
      show (t.filter (fun b => decide (contentN F b ≤ C))).flatMap G
        = H a ++ t.flatMap H
      rw [hneg a hd, prunePass F C G H hpos hneg t]
      rfl

private theorem assignsA_eq {L : Type} (F : Data L) (C : Nat) :
    ∀ n : Nat, assignsA F C n
      = ((assigns F C n).filter
          (fun a => decide (contentN F a ≤ C))).map
            (fun a => (contentN F a, a))
  | 0 => rfl
  | n + 1 => by
    show (assignsA F C n).flatMap (fun p =>
        ((F.unit :: F.below C).map
            (fun l => (p.1 + stepN F l, l :: p.2))).filter
          (fun r => decide (r.1 ≤ C)))
      = (((assigns F C n).flatMap (fun a =>
            (F.unit :: F.below C).map (fun l => l :: a))).filter
          (fun a => decide (contentN F a ≤ C))).map
            (fun a => (contentN F a, a))
    rw [assignsA_eq F C n,
      flatMap_map (fun a => (contentN F a, a))
        (fun p => ((F.unit :: F.below C).map
            (fun l => (p.1 + stepN F l, l :: p.2))).filter
          (fun r => decide (r.1 ≤ C)))
        ((assigns F C n).filter (fun a => decide (contentN F a ≤ C))),
      filter_flatMap (fun a => (F.unit :: F.below C).map (fun l => l :: a))
        (fun a => decide (contentN F a ≤ C)) (assigns F C n),
      map_flatMap (fun a => ((F.unit :: F.below C).map
          (fun l => l :: a)).filter
        (fun b => decide (contentN F b ≤ C)))
        (fun a => (contentN F a, a)) (assigns F C n)]
    exact prunePass F C
      (fun a => ((F.unit :: F.below C).map
          (fun l => (contentN F a + stepN F l, l :: a))).filter
        (fun r => decide (r.1 ≤ C)))
      (fun a => (((F.unit :: F.below C).map (fun l => l :: a)).filter
          (fun b => decide (contentN F b ≤ C))).map
            (fun b => (contentN F b, b)))
      (fun a => extLeaf F C a (F.unit :: F.below C))
      (fun a hda => by
        rw [extEmpty F C a
          (fun hle => Bool.noConfusion
            (hda.symm.trans (decide_eq_true hle)))
          (F.unit :: F.below C)]
        rfl)
      (assigns F C n)

private theorem mapSndPair {L : Type} (F : Data L) :
    ∀ l : List (List L),
      (l.map (fun a => (contentN F a, a))).map Prod.snd = l
  | [] => rfl
  | a :: t => by
    show a :: (t.map (fun b => (contentN F b, b))).map Prod.snd = a :: t
    rw [mapSndPair F t]

/-- The window index's fast read: the content-pruned enumeration,
a link label refused at the step where the running content passes
the cutoff, with the any-nonunit and occupied reads at the leaves.
`prop:windowfinite`'s per-link cutoff read: a partial assignment's
content sits at or below every completion's, so the enumeration
refuses a partial beyond the cutoff with every completion refused
beside it, the pruned walk and the whole product's filter one list
(`idxA_eq`). -/
def idxA {L : Type} (F : Data L) (R : Region) (C : Nat) : List (List L) :=
  ((assignsA F C R.links).map Prod.snd).filter (fun a =>
    (a.any (fun l => !(F.eqL l F.unit)))
      && occupied F R a)

/-- The fast read is the window index: the pruned enumeration's
survivors are exactly the below-cutoff configurations, and the two
leaf reads sit at the identical members. -/
theorem idxA_eq {L : Type} (F : Data L) (R : Region) (C : Nat) :
    idxA F R C = idx F R C := by
  show (((assignsA F C R.links).map Prod.snd).filter
      (fun a => (a.any (fun l => !(F.eqL l F.unit)))
        && occupied F R a))
    = (assigns F C R.links).filter (fun a =>
        (a.any (fun l => !(F.eqL l F.unit)))
          && decide (contentN F a ≤ C)
          && occupied F R a)
  rw [assignsA_eq F C R.links, mapSndPair F
      ((assigns F C R.links).filter
        (fun a => decide (contentN F a ≤ C))),
    filter_filter (fun a => (a.any (fun l => !(F.eqL l F.unit)))
        && occupied F R a)
      (fun a => decide (contentN F a ≤ C)) (assigns F C R.links)]
  exact filter_congr
    (fun a => decide (contentN F a ≤ C)
      && ((a.any (fun l => !(F.eqL l F.unit))) && occupied F R a))
    (fun a => (a.any (fun l => !(F.eqL l F.unit)))
      && decide (contentN F a ≤ C) && occupied F R a)
    (fun a => by
      cases a.any (fun l => !(F.eqL l F.unit)) <;>
        cases decide (contentN F a ≤ C) <;>
          cases occupied F R a <;> rfl)
    (assigns F C R.links)

end carrier
