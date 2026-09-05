import MassGap.Fusion
import MassGap.Lattice
/-!
`def:carrier` — the carrier's index layer, built from the fusion
interface's fields alone over the lattice interface's region: a
configuration assigns a label per link key, the unit label the
unoccupied read and the support the nonunit keys (`support`),
occupied by the shape of its data (`idx` filters at an occupied
support); its content is the support's Casimir fold at the
cleared second member (`contentN`); a touched vertex is a support endpoint, its incident support ends
the occupied incident labels with their orientations
(`incidentEnds`, the presentation field's datum), and a
vertex's multiplicity is the invariant count of the incident
support labels' product, the incoming links dualized (`vmult`),
the count the fusion rows' fold (`invCount`, the row expansion one
label at a time); a configuration is occupied where every touched
vertex reads a positive multiplicity; and the window index at the
region and cutoff is the occupied configurations at content at or
below the cutoff (`idx`, the enumeration over the interface's
below-cutoff labels per link), with the content-pruned fast read
beside it (`idxA`, a link label refused at the step where the
running content passes the cutoff, `idxA_eq` the identity), its
membership read both ways (`idx_sound`, `mem_idx`: the width, the
label carrier, the occupied support, the content and the occupancy
the five data), and its distinctness at a distinct label carrier
(`idx_distinct`).  The index's equality read is the label equality
key by key (`eqConf`, `eqConf_read`, `eqConf_intro`, `eqConf_refl`),
structural on the labels at the label calculus (`eqConf_labelA`),
and a member reads its membership at it (`confMem_of_mem`); the
invariant count is a multiset read at the count laws over a label
domain (`invCount_relist`).  The
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

/-! The invariant count is a read of the labels' multiset: the count
laws of `con:fusion` — the commutativity, the associativity and the
unit read, the row the count's support — carry the row expansion
across every reordering of the label list (`prop:algebra`'s laws at
`def:carrier`'s vertex read), so the vertex multiplicity reads the
incident labels' product free of the incident walk's key order.  The
laws enter relativized to a stated label domain holding the unit and
closed under the rows, the consumer's own scope (the label calculus's
domain the reduced shapes of one width). -/

/-- The count laws over a label domain, the derivation tier's shared
hypothesis shape (definitionally the public statement's binders):
the domain holds the unit and closes under the rows, and the
commutativity, associativity, unit and row laws hold on it. -/
private def domLaws {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) : Prop :=
  P F.unit = true
  ∧ (∀ a b, P a = true → P b = true → ((F.row a b).all P) = true)
  ∧ (∀ a b c, P a = true → P b = true → P c = true →
      F.count a b c = F.count b a c)
  ∧ (∀ a b c d, P a = true → P b = true → P c = true → P d = true →
      assocLaw F a b c d)
  ∧ (∀ a b, P a = true → P b = true → unitLaw F a b)
  ∧ (∀ a b c, P a = true → P b = true → P c = true → rowLaw F a b c)

/-- A label off the domain is vacant in every list inside it. -/
private theorem countOf_off {L : Type} [DecidableEq L] (P : L → Bool)
    (l : List L) (hl : l.all P = true) (x : L) (hx : P x = false) :
    ground.countOf x l = 0 := by
  cases Nat.lt_or_ge 0 (ground.countOf x l) with
  | inl hpos =>
    have := ground.all_of_mem P l hl x (ground.mem_of_countOf_pos x l hpos)
    rw [hx] at this
    exact Bool.noConfusion this
  | inr h0 => exact Nat.le_antisymm h0 (Nat.zero_le _)

/-- A counted member of a domain list reads the domain. -/
private theorem P_of_countOf {L : Type} [DecidableEq L] (P : L → Bool)
    (l : List L) (hl : l.all P = true) (x : L)
    (hx : 0 < ground.countOf x l) : P x = true :=
  ground.all_of_mem P l hl x (ground.mem_of_countOf_pos x l hx)

/-- The row's weighted fold at a stated read, the row expansion's
one summand shape. -/
private def rowSum {L : Type} (F : Data L) (a b : L) (g : L → Nat) :
    Nat :=
  ground.famFold Nat.add 0 (fun c => F.count a b c * g c) (F.row a b)

/-- The row expansion at three labels or more as the row's weighted
fold. -/
private theorem invCount_rowSum {L : Type} (F : Data L) (l1 l2 l3 : L)
    (rest : List L) :
    invCount F (l1 :: l2 :: l3 :: rest)
      = rowSum F l1 l2 (fun c => invCount F (c :: l3 :: rest)) := by
  rw [invCount_cons F l1 l2 l3 rest,
    ground.foldlSum (fun c => F.count l1 l2 c * invCount F (c :: l3 :: rest))
      (F.row l1 l2) 0, Nat.zero_add]
  rfl

/-- The weighted fold moves across a pointwise equality of its reads
on the row's members. -/
private theorem rowSum_congr {L : Type} [DecidableEq L] (F : Data L)
    (a b : L) (g g' : L → Nat)
    (h : ∀ e, 0 < ground.countOf e (F.row a b) → g e = g' e) :
    rowSum F a b g = rowSum F a b g' :=
  ground.famFold_congr_members Nat.add 0 _ _ (F.row a b)
    (fun c hc => by rw [h c hc])

/-- Two counts at most one with equal positivity are equal. -/
private theorem eq_of_le_one_pos {m n : Nat} (hm : m ≤ 1) (hn : n ≤ 1)
    (h : 0 < m ↔ 0 < n) : m = n := by
  cases Nat.lt_or_ge 0 m with
  | inl hmp =>
    cases Nat.lt_or_ge 0 n with
    | inl hnp =>
      exact Nat.le_antisymm (Nat.le_trans hm (Nat.succ_le_of_lt hnp))
        (Nat.le_trans hn (Nat.succ_le_of_lt hmp))
    | inr hn0 =>
      have hz : n = 0 := Nat.le_antisymm hn0 (Nat.zero_le n)
      rw [hz] at h
      exact absurd (h.1 hmp) (Nat.lt_irrefl 0)
  | inr hm0 =>
    have hz : m = 0 := Nat.le_antisymm hm0 (Nat.zero_le m)
    rw [hz] at h
    cases Nat.lt_or_ge 0 n with
    | inl hnp => exact absurd (h.2 hnp) (Nat.lt_irrefl 0)
    | inr hn0 => rw [hz]; exact (Nat.le_antisymm hn0 (Nat.zero_le n)).symm

/-- A row of domain labels is a distinct list at the row law. -/
private theorem row_distinct {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b : L) (ha : P a = true)
    (hb : P b = true) : ground.distinctList (F.row a b) :=
  fun c hc => (hL.2.2.2.2.2 a b c ha hb
    (ground.all_of_mem P _ (hL.2.1 a b ha hb) c hc)).2

/-- The weighted fold exchanges its two labels at the commutativity
law, the row the count's support at either order, the relisting read
at the distinct rows with the off-domain labels vacant in both. -/
private theorem rowSum_comm {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b : L) (ha : P a = true)
    (hb : P b = true) (g : L → Nat) :
    rowSum F a b g = rowSum F b a g := by
  show ground.famFold Nat.add 0 (fun c => F.count a b c * g c) (F.row a b)
    = ground.famFold Nat.add 0 (fun c => F.count b a c * g c) (F.row b a)
  rw [ground.famFold_congr_members Nat.add 0 _
    (fun c => F.count b a c * g c) (F.row a b) (fun c hc => by
      rw [hL.2.2.1 a b c ha hb (P_of_countOf P _ (hL.2.1 a b ha hb) c hc)])]
  refine ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc _
    (F.row a b) (F.row b a) (fun x => ?_)
  cases hx : P x with
  | true =>
    exact eq_of_le_one_pos (hL.2.2.2.2.2 a b x ha hb hx).2
      (hL.2.2.2.2.2 b a x hb ha hx).2
      (Iff.trans (Iff.symm (hL.2.2.2.2.2 a b x ha hb hx).1)
        (Iff.trans (by rw [hL.2.2.1 a b x ha hb hx])
          (hL.2.2.2.2.2 b a x hb ha hx).1))
  | false =>
    rw [countOf_off P _ (hL.2.1 a b ha hb) x hx,
      countOf_off P _ (hL.2.1 b a hb ha) x hx]

/-- The associativity law as the weighted folds: the leading pair's
row against the trailing composition reads the trailing pair's row
against the leading, one value at every domain target. -/
private theorem assoc_rowSum {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b c d : L) (ha : P a = true)
    (hb : P b = true) (hc : P c = true) (hd : P d = true) :
    rowSum F a b (fun e => F.count e c d)
      = rowSum F b c (fun f => F.count a f d) := by
  have h : (F.row a b).foldl (fun acc e =>
        acc + F.count a b e * F.count e c d) 0
      = (F.row b c).foldl (fun acc f =>
        acc + F.count b c f * F.count a f d) 0 :=
    hL.2.2.2.1 a b c d ha hb hc hd
  rw [ground.foldlSum (fun e => F.count a b e * F.count e c d) (F.row a b) 0,
    ground.foldlSum (fun f => F.count b c f * F.count a f d) (F.row b c) 0,
    Nat.zero_add, Nat.zero_add] at h
  exact h

/-- The two-label count is the unit read. -/
private theorem invCount_two {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b : L) (ha : P a = true)
    (hb : P b = true) :
    invCount F [a, b] = F.count a b F.unit := by
  show (if F.eqL a (F.dual b) then 1 else 0) = F.count a b F.unit
  rw [hL.2.2.2.2.1 a b ha hb]

/-- The leading pair exchanges: the two-label read at the unit law's
commutativity, and the row expansion at the exchanged row beyond. -/
private theorem invCount_swap12 {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b : L) (ha : P a = true)
    (hb : P b = true) :
    ∀ r : List L, invCount F (a :: b :: r) = invCount F (b :: a :: r)
  | [] => by
    rw [invCount_two F P hL a b ha hb, invCount_two F P hL b a hb ha,
      hL.2.2.1 a b F.unit ha hb hL.1]
  | c :: r => by
    rw [invCount_rowSum F a b c r, invCount_rowSum F b a c r,
      rowSum_comm F P hL a b ha hb]

/-- A positive product's second factor reads its row membership. -/
private theorem row_of_pos {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (e c g : L) (he : P e = true)
    (hc : P c = true) (hg : P g = true) (k : Nat)
    (h : 0 < F.count e c g * k) : 0 < ground.countOf g (F.row e c) :=
  (hL.2.2.2.2.2 e c g he hc hg).1.1 (ground.mulPosSplit h).1

/-- The weighted fold over a row reads over any distinct domain list
holding the row: the summand is the count's own multiple, vacant off
the row's support. -/
private theorem rowSum_over {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (e c : L) (he : P e = true)
    (hc : P c = true) (g : L → Nat)
    (G : List L) (hG : ground.distinctList G) (hGP : G.all P = true)
    (hsub : ∀ x, 0 < ground.countOf x (F.row e c) →
      0 < ground.countOf x G) :
    rowSum F e c g
      = ground.famFold Nat.add 0 (fun x => F.count e c x * g x) G :=
  ground.famFold_add_occupied (fun x => F.count e c x * g x) (F.row e c) G
    (row_distinct F P hL e c he hc) hG (fun x hx _ => hsub x hx)
    (fun x hxG hp => row_of_pos F P hL e c x he hc
      (P_of_countOf P G hGP x hxG) (g x) hp)

/-- The exchanged double fold: the leading row against the
trailing rows' folds reads, over a distinct domain list holding
every trailing row, the target's fold of the composed counts against
the read — the row folds widened, the product carried in, the two
folds exchanged and the read factored out. -/
private theorem rowSum_double {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b c : L) (ha : P a = true)
    (hb : P b = true) (hc : P c = true) (g : L → Nat)
    (G : List L) (hG : ground.distinctList G) (hGP : G.all P = true)
    (hsub : ∀ e, 0 < ground.countOf e (F.row a b) →
      ∀ x, 0 < ground.countOf x (F.row e c) → 0 < ground.countOf x G) :
    rowSum F a b (fun e => rowSum F e c g)
      = ground.famFold Nat.add 0
          (fun x => rowSum F a b (fun e => F.count e c x) * g x) G := by
  show ground.famFold Nat.add 0
      (fun e => F.count a b e * rowSum F e c g) (F.row a b) = _
  rw [ground.famFold_congr_members Nat.add 0 _
    (fun e => ground.famFold Nat.add 0
      (fun x => F.count a b e * (F.count e c x * g x)) G)
    (F.row a b) (fun e he => by
      rw [rowSum_over F P hL e c (P_of_countOf P _ (hL.2.1 a b ha hb) e he)
          hc g G hG hGP (hsub e he),
        ground.famFold_mul (F.count a b e) _ G]),
    ground.famFold_swap (fun e x => F.count a b e * (F.count e c x * g x))
      (F.row a b) G]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun x => ?_) G
  show ground.famFold Nat.add 0
      (fun e => F.count a b e * (F.count e c x * g x)) (F.row a b)
    = ground.famFold Nat.add 0
      (fun e => F.count a b e * F.count e c x) (F.row a b) * g x
  rw [← ground.famFold_mulR (g x) (fun e => F.count a b e * F.count e c x)
    (F.row a b)]
  exact ground.famFold_congr_all Nat.add 0 _ _
    (fun e => (ground.mulAssoc (F.count a b e) (F.count e c x) (g x)).symm)
    (F.row a b)

/-- The union of the two trailing row families, a distinct list
holding every trailing row of either side. -/
private def rowUnion {L : Type} [DecidableEq L] (F : Data L)
    (a b c : L) : List L :=
  ground.dedupL ((F.row a b).flatMap (fun e => F.row e c)
    ++ (F.row a c).flatMap (fun e => F.row e b))

/-- The union holds the first family's rows. -/
private theorem rowUnion_left {L : Type} [DecidableEq L] (F : Data L)
    (a b c e : L) (he : 0 < ground.countOf e (F.row a b)) (x : L)
    (hx : 0 < ground.countOf x (F.row e c)) :
    0 < ground.countOf x (rowUnion F a b c) :=
  ground.countOf_pos_of_mem (ground.mem_dedupL
    (ground.mem_append_left _ (ground.mem_flatMap_to _
      (ground.mem_of_countOf_pos e _ he)
      (ground.mem_of_countOf_pos x _ hx))))

/-- The union holds the second family's rows. -/
private theorem rowUnion_right {L : Type} [DecidableEq L] (F : Data L)
    (a b c e : L) (he : 0 < ground.countOf e (F.row a c)) (x : L)
    (hx : 0 < ground.countOf x (F.row e b)) :
    0 < ground.countOf x (rowUnion F a b c) :=
  ground.countOf_pos_of_mem (ground.mem_dedupL
    (ground.mem_append_right _ (ground.mem_flatMap_to _
      (ground.mem_of_countOf_pos e _ he)
      (ground.mem_of_countOf_pos x _ hx))))

/-- The union is distinct. -/
private theorem rowUnion_distinct {L : Type} [DecidableEq L] (F : Data L)
    (a b c : L) : ground.distinctList (rowUnion F a b c) :=
  fun x _ => ground.countOf_dedupL_le x _

/-- The union sits in the domain at domain labels, the rows closed. -/
private theorem rowUnion_P {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b c : L) (ha : P a = true)
    (hb : P b = true) (hc : P c = true) :
    (rowUnion F a b c).all P = true := by
  refine ground.all_of_mem_intro P _ (fun x hx => ?_)
  match ground.mem_append_of _ _ (ground.mem_of_dedupL hx) with
  | Or.inl h1 =>
    match ground.mem_flatMap_of _ _ _ h1 with
    | ⟨e, he, hxe⟩ =>
      exact ground.all_of_mem P _ (hL.2.1 e c
        (ground.all_of_mem P _ (hL.2.1 a b ha hb) e he) hc) x hxe
  | Or.inr h2 =>
    match ground.mem_flatMap_of _ _ _ h2 with
    | ⟨e, he, hxe⟩ =>
      exact ground.all_of_mem P _ (hL.2.1 e b
        (ground.all_of_mem P _ (hL.2.1 a c ha hc) e he) hb) x hxe

/-- The second and third labels exchange: at three labels the unit
read joins the associativity law at the unit target, and beyond
three the exchanged double folds meet at the composed counts, the
associativity law at every target with the trailing rows relisted
at the commutativity. -/
private theorem invCount_swap23 {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a b c : L) (ha : P a = true)
    (hb : P b = true) (hc : P c = true) :
    ∀ r : List L, invCount F (a :: b :: c :: r) = invCount F (a :: c :: b :: r)
  | [] => by
    rw [invCount_rowSum F a b c [], invCount_rowSum F a c b [],
      rowSum_congr F a b _ (fun e => F.count e c F.unit)
        (fun e he => invCount_two F P hL e c
          (P_of_countOf P _ (hL.2.1 a b ha hb) e he) hc),
      rowSum_congr F a c _ (fun e => F.count e b F.unit)
        (fun e he => invCount_two F P hL e b
          (P_of_countOf P _ (hL.2.1 a c ha hc) e he) hb),
      assoc_rowSum F P hL a b c F.unit ha hb hc hL.1,
      assoc_rowSum F P hL a c b F.unit ha hc hb hL.1,
      rowSum_comm F P hL c b hc hb]
  | d :: r => by
    rw [invCount_rowSum F a b c (d :: r), invCount_rowSum F a c b (d :: r),
      rowSum_congr F a b _ (fun e => rowSum F e c
        (fun x => invCount F (x :: d :: r)))
        (fun e _ => invCount_rowSum F e c d r),
      rowSum_congr F a c _ (fun e => rowSum F e b
        (fun x => invCount F (x :: d :: r)))
        (fun e _ => invCount_rowSum F e b d r),
      rowSum_double F P hL a b c ha hb hc _ (rowUnion F a b c)
        (rowUnion_distinct F a b c) (rowUnion_P F P hL a b c ha hb hc)
        (rowUnion_left F a b c),
      rowSum_double F P hL a c b ha hc hb _ (rowUnion F a b c)
        (rowUnion_distinct F a b c) (rowUnion_P F P hL a b c ha hb hc)
        (rowUnion_right F a b c)]
    refine ground.famFold_congr_members Nat.add 0 _ _ _ (fun x hx => ?_)
    have hxP : P x = true :=
      P_of_countOf P _ (rowUnion_P F P hL a b c ha hb hc) x hx
    rw [assoc_rowSum F P hL a b c x ha hb hc hxP,
      assoc_rowSum F P hL a c b x ha hc hb hxP,
      rowSum_comm F P hL c b hc hb]

/-- An adjacent pair exchanges at any depth: the two head exchanges
at depths one and two, and beyond them the row expansion carries the
exchange to the shortened lists. -/
private theorem invCount_swapAt {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (x y : L) (hx : P x = true)
    (hy : P y = true) (r : List L) :
    ∀ (n : Nat) (u : List L), u.length ≤ n → u.all P = true →
      invCount F (u ++ x :: y :: r) = invCount F (u ++ y :: x :: r)
  | _, [], _, _ => invCount_swap12 F P hL x y hx hy r
  | _, [p], _, hu =>
    invCount_swap23 F P hL p x y (ground.andSplitB hu).1 hx hy r
  | 0, _ :: _ :: _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | n + 1, p :: q :: u, h, hu => by
    have hp : P p = true := (ground.andSplitB hu).1
    have hq : P q = true := (ground.andSplitB (ground.andSplitB hu).2).1
    have hu' : u.all P = true := (ground.andSplitB (ground.andSplitB hu).2).2
    show invCount F (p :: q :: (u ++ x :: y :: r))
      = invCount F (p :: q :: (u ++ y :: x :: r))
    match hu1 : u ++ x :: y :: r, hu2 : u ++ y :: x :: r with
    | [], _ =>
      exact absurd (congrArg List.length hu1)
        (fun h => by
          rw [ground.length_append] at h
          exact Nat.noConfusion h)
    | _ :: _, [] =>
      exact absurd (congrArg List.length hu2)
        (fun h => by
          rw [ground.length_append] at h
          exact Nat.noConfusion h)
    | c :: r1, c' :: r1' =>
      rw [invCount_rowSum F p q c r1, invCount_rowSum F p q c' r1']
      refine rowSum_congr F p q _ _ (fun e he => ?_)
      rw [← hu1, ← hu2]
      exact invCount_swapAt F P hL x y hx hy r n (e :: u)
        (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
          (by rw [show (p :: q :: u).length = u.length + 2 from rfl] at h
              exact Nat.succ_le_succ h)))
        (by
          show (P e && u.all P) = true
          rw [P_of_countOf P _ (hL.2.1 p q hp hq) e he, hu']
          rfl)

/-- A label moves to the front of its segment past a stated prefix,
one adjacent exchange per crossed member. -/
private theorem invCount_moveFront {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hL : domLaws F P) (a : L) (ha : P a = true)
    (w : List L) :
    ∀ (u pre : List L), u.all P = true → pre.all P = true →
      invCount F (pre ++ u ++ a :: w) = invCount F (pre ++ a :: u ++ w)
  | [], pre, _, _ => by
    rw [ground.append_assoc pre [] (a :: w), ground.append_assoc pre [a] w]
    rfl
  | q :: u, pre, hu, hpre => by
    have hq : P q = true := (ground.andSplitB hu).1
    have hu' : u.all P = true := (ground.andSplitB hu).2
    have e1 : pre ++ q :: u = (pre ++ [q]) ++ u :=
      (ground.append_assoc pre [q] u).symm
    have e2 : ((pre ++ [q]) ++ a :: u) ++ w = pre ++ q :: a :: (u ++ w) := by
      rw [ground.append_assoc (pre ++ [q]) (a :: u) w,
        ground.append_assoc pre [q] (a :: u ++ w)]
      rfl
    have e3 : (pre ++ a :: q :: u) ++ w = pre ++ a :: q :: (u ++ w) :=
      ground.append_assoc pre (a :: q :: u) w
    have hpq : (pre ++ [q]).all P = true := by
      rw [ground.all_append, hpre]
      show (true && (P q && true)) = true
      rw [hq]
      rfl
    rw [show pre ++ (q :: u) ++ a :: w = (pre ++ [q]) ++ u ++ a :: w from by
          rw [e1],
      invCount_moveFront F P hL a ha w u (pre ++ [q]) hu' hpq,
      show (pre ++ [q]) ++ a :: u ++ w = pre ++ q :: a :: (u ++ w) from e2,
      show pre ++ a :: (q :: u) ++ w = pre ++ a :: q :: (u ++ w) from e3]
    exact invCount_swapAt F P hL q a hq ha (u ++ w)
      pre.length pre (Nat.le_refl _) hpre

/-- A counted member splits its list at a first occurrence. -/
private theorem split_of_countOf {L : Type} [DecidableEq L] (a : L) :
    ∀ ls : List L, 0 < ground.countOf a ls →
      ∃ u w : List L, ls = u ++ a :: w
  | [], h => absurd h (Nat.lt_irrefl 0)
  | b :: t, h =>
    if hab : a = b then ⟨[], t, by rw [hab]; rfl⟩
    else
      match split_of_countOf a t (by
          rw [ground.countOf_cons, if_neg hab, Nat.zero_add] at h
          exact h) with
      | ⟨u, w, hw⟩ => ⟨b :: u, w, by rw [hw]; rfl⟩

/-- Two lists of one multiset with a shared member past a split
carry one multiset off it. -/
private theorem counts_past {L : Type} [DecidableEq L] (a : L)
    (u w m : List L)
    (hc : ∀ x, ground.countOf x (u ++ a :: w) = ground.countOf x (a :: m)) :
    ∀ x, ground.countOf x (u ++ w) = ground.countOf x m := by
  intro x
  have hx := hc x
  rw [ground.countOf_append, ground.countOf_cons, ground.countOf_cons,
    Nat.add_left_comm] at hx
  rw [ground.countOf_append]
  exact ground.addCancelL _ hx

/-- A domain list's split parts read the domain. -/
private theorem all_split {L : Type} (P : L → Bool) :
    ∀ (u : List L) (a : L) (w : List L), (u ++ a :: w).all P = true →
      u.all P = true ∧ P a = true ∧ w.all P = true := by
  intro u a w h
  rw [ground.all_append] at h
  have h1 := ground.andSplitB h
  have h2 := ground.andSplitB (show (P a && w.all P) = true from h1.2)
  exact ⟨h1.1, h2.1, h2.2⟩

/-- The count read is one value at two lists of one multiset — the
counts equal at every label — the count laws carrying the row
expansion across the reordering: `def:carrier`'s vertex multiplicity
reads the incident labels' product at any listing of its factors
(`prop:algebra`'s commutativity, associativity and unit laws with the
row as the count's support), the laws over a label domain holding
the unit and closed under the rows with the list inside it. -/
private theorem invCount_relist_fuel {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hunit : P F.unit = true)
    (hrowP : ∀ a b, P a = true → P b = true → ((F.row a b).all P) = true)
    (hcomm : ∀ a b c, P a = true → P b = true → P c = true →
      F.count a b c = F.count b a c)
    (hassoc : ∀ a b c d, P a = true → P b = true → P c = true →
      P d = true → assocLaw F a b c d)
    (hunitL : ∀ a b, P a = true → P b = true → unitLaw F a b)
    (hrow : ∀ a b c, P a = true → P b = true → P c = true →
      rowLaw F a b c) :
    ∀ (n : Nat) (ls ls' : List L), ls.all P = true → ls.length ≤ n →
      (∀ x, ground.countOf x ls = ground.countOf x ls') →
      invCount F ls = invCount F ls'
  | 0, ls, ls', _, hl, hc => by
    have h0 : ls = [] := ground.nil_of_length_zero ls
      (Nat.le_antisymm hl (Nat.zero_le _))
    rw [h0] at hc
    rw [h0, ground.eq_nil_of_countOf ls' (fun x => (hc x).symm)]
  | n + 1, ls, ls', hP, hl, hc =>
    have hL : domLaws F P := ⟨hunit, hrowP, hcomm, hassoc, hunitL, hrow⟩
    match ls', hc with
    | [], hc => by rw [ground.eq_nil_of_countOf ls hc]
    | a :: m', hc =>
      match split_of_countOf a ls (by
          rw [hc a, ground.countOf_head]
          exact Nat.succ_pos _) with
      | ⟨u, w, hw⟩ => by
        have hcw : ∀ x, ground.countOf x (u ++ w) = ground.countOf x m' :=
          counts_past a u w m' (fun x => by rw [← hw]; exact hc x)
        have hlen : (u ++ w).length + 1 ≤ n + 1 := by
          have hl' : ls.length = (u ++ w).length + 1 := by
            rw [hw, ground.length_append, ground.length_append]
            rfl
          rw [hl'] at hl
          exact hl
        have hPs := all_split P u a w (by rw [← hw]; exact hP)
        have hPuw : (u ++ w).all P = true := by
          rw [ground.all_append, hPs.1, hPs.2.2]
          rfl
        rw [hw, show u ++ a :: w = [] ++ u ++ a :: w from rfl,
          invCount_moveFront F P hL a hPs.2.1 w u [] hPs.1 rfl]
        show invCount F (a :: (u ++ w)) = invCount F (a :: m')
        match m', hcw with
        | [], hcw => rw [ground.eq_nil_of_countOf (u ++ w) hcw]
        | [b], hcw =>
          rw [ground.single_of_counts b (u ++ w) (fun y => by
            rw [hcw y, ground.countOf_cons]
            show (if y = b then 1 else 0) + 0 = _
            rw [Nat.add_zero])]
        | b :: c :: r', hcw =>
          match split_of_countOf b (u ++ w) (by
              rw [hcw b, ground.countOf_head]
              exact Nat.succ_pos _) with
          | ⟨u2, w2, hw2⟩ =>
            have hcw2 : ∀ x, ground.countOf x (u2 ++ w2)
                = ground.countOf x (c :: r') :=
              counts_past b u2 w2 (c :: r')
                (fun x => by rw [← hw2]; exact hcw x)
            have hlen2 : (u2 ++ w2).length + 1 ≤ n := by
              have hl' : (u ++ w).length = (u2 ++ w2).length + 1 := by
                rw [hw2, ground.length_append, ground.length_append]
                rfl
              rw [hl'] at hlen
              exact Nat.le_of_succ_le_succ hlen
            have hPs2 := all_split P u2 b w2 (by rw [← hw2]; exact hPuw)
            have hPuw2 : (u2 ++ w2).all P = true := by
              rw [ground.all_append, hPs2.1, hPs2.2.2]
              rfl
            rw [hw2, show a :: (u2 ++ b :: w2) = [a] ++ u2 ++ b :: w2 from rfl,
              invCount_moveFront F P hL b hPs2.2.1 w2 u2 [a] hPs2.1
                (by show (P a && true) = true; rw [hPs.2.1]; rfl)]
            show invCount F (a :: b :: (u2 ++ w2))
              = invCount F (a :: b :: c :: r')
            match hh : u2 ++ w2 with
            | [] =>
              have hz := hcw2 c
              rw [hh, ground.countOf_head] at hz
              have h0 : (0 : Nat) = ground.countOf c r' + 1 := hz
              exact Nat.noConfusion h0
            | c2 :: r2 =>
              rw [invCount_rowSum F a b c2 r2, invCount_rowSum F a b c r']
              refine rowSum_congr F a b _ _ (fun e he => ?_)
              have heP : P e = true :=
                P_of_countOf P _ (hrowP a b hPs.2.1 hPs2.2.1) e he
              refine invCount_relist_fuel F P hunit hrowP hcomm hassoc hunitL hrow
                n (e :: c2 :: r2) (e :: c :: r') ?_ ?_ ?_
              · show (P e && (c2 :: r2).all P) = true
                rw [heP, ← hh, hPuw2]
                rfl
              · rw [← hh]
                exact hlen2
              · intro x
                rw [ground.countOf_cons x e (c2 :: r2),
                  ground.countOf_cons x e (c :: r'), ← hh, hcw2 x]

/-- The invariant count is a multiset read at the count laws over a
label domain holding the unit and closed under the rows: two label
lists of one count family inside the domain read one invariant
count. -/
theorem invCount_relist {L : Type} [DecidableEq L] (F : Data L)
    (P : L → Bool) (hunit : P F.unit = true)
    (hrowP : ∀ a b, P a = true → P b = true → ((F.row a b).all P) = true)
    (hcomm : ∀ a b c, P a = true → P b = true → P c = true →
      F.count a b c = F.count b a c)
    (hassoc : ∀ a b c d, P a = true → P b = true → P c = true →
      P d = true → assocLaw F a b c d)
    (hunitL : ∀ a b, P a = true → P b = true → unitLaw F a b)
    (hrow : ∀ a b c, P a = true → P b = true → P c = true →
      rowLaw F a b c)
    (ls ls' : List L) (hls : ls.all P = true)
    (hc : ∀ x, ground.countOf x ls = ground.countOf x ls') :
    invCount F ls = invCount F ls' :=
  invCount_relist_fuel F P hunit hrowP hcomm hassoc hunitL hrow ls.length
    ls ls' hls (Nat.le_refl _) hc

/-- Two configurations' equality at the interface's label equality,
the index's own read. -/
def eqConf {L : Type} (F : Data L) : List L → List L → Bool :=
  ground.listEqBy F.eqL

/-- A configuration's membership in a stated family at the
interface equality, the fold over the members. -/
def confMem {L : Type} (F : Data L) (a : List L) :
    List (List L) → Bool
  | [] => false
  | b :: t => eqConf F a b || confMem F a t

/-- Two configurations of one length agreeing at every key agree at
the index's own read. -/
theorem eqConf_intro {L : Type} (F : Data L) :
    ∀ a b : List L, a.length = b.length →
      (∀ i, i < b.length →
        F.eqL (getAt F.unit a i) (getAt F.unit b i) = true) →
      eqConf F a b = true
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | x :: s, y :: t, h, hf => by
    have h0 : F.eqL x y = true := hf 0 (Nat.succ_pos t.length)
    show (F.eqL x y && eqConf F s t) = true
    rw [h0]
    show eqConf F s t = true
    exact eqConf_intro F s t (Nat.succ.inj h)
      (fun i hi => hf (i + 1) (Nat.succ_lt_succ hi))

/-- A configuration reads equal to itself, the label equality's own
reflexivity key by key. -/
theorem eqConf_refl {L : Type} (F : Data L) (a : List L) :
    eqConf F a a = true :=
  eqConf_intro F a a rfl (fun _ _ => F.eqLRefl _)

/-- The equality read's members: two equal configurations agree in
length and key by key at the label equality. -/
theorem eqConf_read {L : Type} (F : Data L) :
    ∀ a b : List L, eqConf F a b = true →
      a.length = b.length ∧ ∀ i, i < a.length →
        F.eqL (getAt F.unit a i) (getAt F.unit b i) = true
  | [], [], _ => ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: s, y :: t, h => by
    have h' : (F.eqL x y && eqConf F s t) = true := h
    obtain ⟨hxy, hst⟩ := andSplitB h'
    obtain ⟨hl, hf⟩ := eqConf_read F s t hst
    refine ⟨congrArg Nat.succ hl, fun i hi => ?_⟩
    cases i with
    | zero => exact hxy
    | succ i => exact hf i (Nat.lt_of_succ_lt_succ hi)

/-- At the label calculus the equality read is structural on the
labels: two configurations over the width-`d` labels reading equal
are one list, the reduced representatives their own. -/
theorem eqConf_labelA (d : Nat) (a b : List places.Shape)
    (ha : a.all (labelA d) = true) (hb : b.all (labelA d) = true)
    (h : eqConf (dataA d) a b = true) : a = b := by
  obtain ⟨hl, hf⟩ := eqConf_read (dataA d) a b h
  refine getAt_ext (dataA d).unit a b hl (fun i hi => ?_)
  have hi' : i < b.length := by
    rw [← hl]
    exact hi
  have hx := labelA_red d (getAt (dataA d).unit a i)
    (all_of_mem _ _ ha _ (mem_getAt (dataA d).unit a i hi))
  have hy := labelA_red d (getAt (dataA d).unit b i)
    (all_of_mem _ _ hb _ (mem_getAt (dataA d).unit b i hi'))
  have he : (labels.reduce (getAt (dataA d).unit a i)
      == labels.reduce (getAt (dataA d).unit b i)) = true := hf i hi
  rw [hx, hy] at he
  exact listBeqEq he

/-- A member of a stated family reads its membership at the
interface equality. -/
theorem confMem_of_mem {L : Type} (F : Data L) (a : List L) :
    ∀ ix : List (List L), a ∈ ix → confMem F a ix = true
  | [], h => nomatch h
  | b :: t, h => by
    show (eqConf F a b || confMem F a t) = true
    cases h with
    | head =>
      rw [eqConf_refl]
      rfl
    | tail _ h2 =>
      rw [confMem_of_mem F a t h2]
      cases eqConf F a b <;> rfl

/-- The incident support ends at a vertex: each occupied incident
link's label with its orientation read, `true` at the tail and
`false` at the head, the unoccupied keys withdrawn — the vertex
list's datum at the interface's presentation field. -/
def incidentEnds {L : Type} (F : Data L) (R : Region)
    (a : List L) (v : Nat) : List (L × Bool) :=
  (incident R v).filterMap (fun e =>
    let l := getAt F.unit a e.1
    if F.eqL l F.unit then none else some (l, e.2))

/-- The incident support labels at a vertex, the incoming links
dualized, the unoccupied keys withdrawn at the support read, the
orientation's two branches spelled at the option. -/
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

/-- The unit configuration, the unit label at every link of the
region: the unit line's own index member, the vacant support. -/
def unitConf {L : Type} (F : Data L) (R : Region) : List L :=
  List.replicate R.links F.unit

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

/-- The window index at the region and cutoff: the occupied
configurations at an occupied support and content at or below the
cutoff, enumerated over the interface's below-cutoff labels per
link. -/
def idx {L : Type} (F : Data L) (R : Region) (C : Nat) :
    List (List L) :=
  (prodLists (List.replicate R.links (F.unit :: F.below C))).filter (fun a =>
    (a.any (fun l => !(F.eqL l F.unit)))
      && contentN F a ≤ C
      && occupied F R a)

/-- The window index's soundness: a member is a configuration at the
region's link count over the unit and the below-cutoff labels, with
an occupied support, content at or below the cutoff, and occupied. -/
theorem idx_sound {L : Type} (F : Data L) (R : Region) (C : Nat)
    (a : List L) (h : a ∈ idx F R C) :
    a.length = R.links ∧ (∀ l, l ∈ a → l ∈ F.unit :: F.below C)
      ∧ (a.any (fun l => !(F.eqL l F.unit))) = true
      ∧ contentN F a ≤ C ∧ occupied F R a = true := by
  obtain ⟨hmem, hp⟩ := ground.mem_filter_of _ _ a h
  obtain ⟨hlen, hpos⟩ := mem_prodLists_of F.unit _ a hmem
  rw [length_replicate] at hlen hpos
  have hlab : ∀ l, l ∈ a → l ∈ F.unit :: F.below C := by
    intro l hl
    obtain ⟨i, hi, hil⟩ := getAt_of_mem F.unit hl
    have h3 := hpos i (by rw [← hlen]; exact hi)
    rw [getAt_replicate [] _ _ _ (by rw [← hlen]; exact hi), hil] at h3
    exact h3
  have h1 := ground.andSplitB hp
  have h2 := ground.andSplitB h1.1
  exact ⟨hlen, hlab, h2.1, of_decide_eq_true h2.2, h1.2⟩

/-- The window index's completeness: a configuration at the five
reads is a member (`def:carrier`'s index at its stated data). -/
theorem mem_idx {L : Type} (F : Data L) (R : Region) (C : Nat)
    (a : List L) (hlen : a.length = R.links)
    (hlab : ∀ l, l ∈ a → l ∈ F.unit :: F.below C)
    (hany : (a.any (fun l => !(F.eqL l F.unit))) = true)
    (hcont : contentN F a ≤ C) (hocc : occupied F R a = true) :
    a ∈ idx F R C := by
  refine ground.mem_filter_to _ ?_ ?_
  · refine mem_prodLists_to F.unit _ a (by rw [length_replicate]; exact hlen)
      (fun i hi => ?_)
    rw [length_replicate] at hi
    rw [getAt_replicate [] _ _ _ hi]
    exact hlab _ (mem_getAt F.unit a i (by rw [hlen]; exact hi))
  · show ((a.any (fun l => !(F.eqL l F.unit)))
      && decide (contentN F a ≤ C) && occupied F R a) = true
    rw [hany, decide_eq_true hcont, hocc]
    rfl

/-- The window index is distinct at a distinct label carrier, the
filter keeping the enumeration's counts. -/
theorem idx_distinct {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (C : Nat) (hlab : distinctList (F.unit :: F.below C)) :
    distinctList (idx F R C) := by
  intro x _
  show countOf x ((prodLists (List.replicate R.links (F.unit :: F.below C))).filter _)
    ≤ 1
  rw [countOf_filter]
  by_cases hP : ((fun a : List L => (a.any (fun l => !(F.eqL l F.unit)))
      && decide (contentN F a ≤ C) && occupied F R a) x) = true
  · rw [if_pos hP]
    refine distinctList_all (distinct_prodLists _ (fun D hD => ?_)) x
    obtain ⟨i, hi, hiD⟩ := getAt_of_mem [] hD
    rw [length_replicate] at hi
    rw [← hiD, getAt_replicate [] _ _ _ hi]
    exact hlab
  · rw [if_neg hP]
    exact Nat.zero_le 1

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

/-- The content as the key range's fold: the Casimir step at each
key's label, the unoccupied keys at the sum's unit — `def:carrier`'s
support fold read positionally over the configuration's width. -/
theorem contentN_range {L : Type} (F : Data L) : ∀ a : List L,
    contentN F a
      = ground.famFold Nat.add 0
          (fun l => if F.eqL (getAt F.unit a l) F.unit then 0
            else F.c2N (getAt F.unit a l))
          (List.range a.length)
  | [] => rfl
  | l :: a => by
    rw [contentN_cons F l a, contentN_range F a,
      show (l :: a).length = a.length + 1 from rfl,
      ground.range_cons a.length,
      show ground.famFold Nat.add 0
          (fun k => if F.eqL (getAt F.unit (l :: a) k) F.unit then 0
            else F.c2N (getAt F.unit (l :: a) k))
          (0 :: (List.range a.length).map (fun j => j + 1))
        = Nat.add (stepN F l) (ground.famFold Nat.add 0
            (fun k => if F.eqL (getAt F.unit (l :: a) k) F.unit then 0
              else F.c2N (getAt F.unit (l :: a) k))
            ((List.range a.length).map (fun j => j + 1))) from rfl,
      ground.famFold_map Nat.add 0 _ (fun j => j + 1) (List.range a.length)]
    show ground.famFold Nat.add 0
        (fun k => if F.eqL (getAt F.unit a k) F.unit then 0
          else F.c2N (getAt F.unit a k)) (List.range a.length) + stepN F l
      = stepN F l + ground.famFold Nat.add 0
        (fun k => if F.eqL (getAt F.unit a k) F.unit then 0
          else F.c2N (getAt F.unit a k)) (List.range a.length)
    exact Nat.add_comm _ _

private def assignsA {L : Type} (F : Data L) (C : Nat) :
    Nat → List (Nat × List L)
  | 0 => [(0, [])]
  | n + 1 => (F.unit :: F.below C).flatMap (fun l =>
      ((assignsA F C n).map (fun p => (p.1 + stepN F l, l :: p.2))).filter
        (fun r => decide (r.1 ≤ C)))

/-- A filter before a map is no filter where the mapped filter
implies it: the members the first filter drops fail the second. -/
private theorem pruneMap {α β : Type} (p : α → Bool) (q : β → Bool)
    (g : α → β) (h : ∀ a, q (g a) = true → p a = true) :
    ∀ l : List α, ((l.filter p).map g).filter q = (l.map g).filter q
  | [] => rfl
  | a :: t => by
    cases hp : p a with
    | true =>
      rw [filter_cons_true hp]
      show (g a :: (t.filter p).map g).filter q = (g a :: t.map g).filter q
      cases hq : q (g a) with
      | true =>
        rw [filter_cons_true hq, filter_cons_true hq, pruneMap p q g h t]
      | false =>
        rw [filter_cons_false hq, filter_cons_false hq, pruneMap p q g h t]
    | false =>
      rw [filter_cons_false hp]
      have hq : q (g a) = false := by
        cases hq : q (g a) with
        | true => rw [h a hq] at hp; exact Bool.noConfusion hp
        | false => rfl
      show ((t.filter p).map g).filter q = (g a :: t.map g).filter q
      rw [filter_cons_false hq, pruneMap p q g h t]

private theorem assignsA_eq {L : Type} (F : Data L) (C : Nat) :
    ∀ n : Nat, assignsA F C n
      = ((prodLists (List.replicate n (F.unit :: F.below C))).filter
          (fun a => decide (contentN F a ≤ C))).map
            (fun a => (contentN F a, a))
  | 0 => rfl
  | n + 1 => by
    show (F.unit :: F.below C).flatMap (fun l =>
        ((assignsA F C n).map (fun p => (p.1 + stepN F l, l :: p.2))).filter
          (fun r => decide (r.1 ≤ C)))
      = (((F.unit :: F.below C).flatMap (fun l =>
            (prodLists (List.replicate n (F.unit :: F.below C))).map
              (fun a => l :: a))).filter
          (fun a => decide (contentN F a ≤ C))).map
            (fun a => (contentN F a, a))
    rw [assignsA_eq F C n,
      filter_flatMap (fun l => (prodLists (List.replicate n
          (F.unit :: F.below C))).map (fun a => l :: a))
        (fun a => decide (contentN F a ≤ C)) (F.unit :: F.below C),
      map_flatMap _ (fun a => (contentN F a, a)) (F.unit :: F.below C)]
    refine flatMap_congr_all _ _ (fun l => ?_) (F.unit :: F.below C)
    rw [map_map, map_congr_all
        (fun a => (contentN F a + stepN F l, l :: a))
        (fun a => (contentN F (l :: a), l :: a))
        (fun a => by rw [contentN_cons F l a]) _,
      ← map_map (fun a => l :: a) (fun b => (contentN F b, b)),
      filter_map (fun b => (contentN F b, b)) (fun r => decide (r.1 ≤ C)),
      pruneMap (fun a => decide (contentN F a ≤ C))
        (fun b => decide (contentN F b ≤ C)) (fun a => l :: a)
        (fun a ha => decide_eq_true
          (Nat.le_trans (contentN_le F l a) (of_decide_eq_true ha)))]

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
    = (prodLists (List.replicate R.links (F.unit :: F.below C))).filter
        (fun a =>
        (a.any (fun l => !(F.eqL l F.unit)))
          && decide (contentN F a ≤ C)
          && occupied F R a)
  rw [assignsA_eq F C R.links, mapSndPair F
      ((prodLists (List.replicate R.links (F.unit :: F.below C))).filter
        (fun a => decide (contentN F a ≤ C))),
    filter_filter (fun a => (a.any (fun l => !(F.eqL l F.unit)))
        && occupied F R a)
      (fun a => decide (contentN F a ≤ C))
      (prodLists (List.replicate R.links (F.unit :: F.below C)))]
  exact ground.filter_congr
    (fun a => decide (contentN F a ≤ C)
      && ((a.any (fun l => !(F.eqL l F.unit))) && occupied F R a))
    (fun a => (a.any (fun l => !(F.eqL l F.unit)))
      && decide (contentN F a ≤ C) && occupied F R a)
    (fun a => by
      cases a.any (fun l => !(F.eqL l F.unit)) <;>
        cases decide (contentN F a ≤ C) <;>
          cases occupied F R a <;> rfl)
    (prodLists (List.replicate R.links (F.unit :: F.below C)))

end carrier
