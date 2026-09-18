import MassGap.Grading
import MassGap.Fiberdec
/-!
`lem:grading` — the fiber's index.  Per fiber on the odd tori the
configuration classes are the window index's orbits under the
translations, per fiber the free orbits at the pair base
(`lem:fiberdec`), and the grading reads its two counts off a class,
one value at every member of the orbit.  An action enters as data,
the link map with its witness, the vertex map with its witness and
the plaquette permutation with its witness (`Act`), a region action
at `con:lattice`'s isomorphism read with the plaquette permutation
read (`regionAct`, `regionActs` over a list), and the action list is
a group on the key range at the decidable read `groupRead`: the
identity among the actions, two actions' composite among them, and
each action's witness among them.  A configuration's orbit is its
images under the list (`orbitOf`), a configuration sits in an orbit
at the interface equality (`inOrbit` at `carrier.confMem`,
`def:carrier`'s configurations at their labels), and the class list
is the collection over the index, one member joined per refusal, the
refusal a joined member's orbit holding the member (`classGo`,
`classList`): every class is an index member (`classList_sub`),
every index member sits in a class's orbit at the identity action
(`classList_cover`), and two classes at distinct places hold one
configuration in both orbits at the group read alone
(`classList_disjoint`).  A class is free where its stabilizer is the
identity, every action reading the class back reading the identity
on the key range (`freeB`), one value along the orbit
(`freeB_perm`), the fiber's classes the free ones (`freeClasses`),
and the fiber's graded index at a head bound is `gradedIdx` at them
(`fiberIdx`).  The window's labels enter at a stated domain with one
spelling per label (`con:labels`: each label reads one reduced
shape; `fusion.eqL_labelA` at the label calculus), so two index
configurations equal at the interface are one list.

The reads are the class's own: at a region action the components
transport (`components_perm`, on Grading's `compOf_perm`), a
component's content (`compContent_perm`) and its own configuration
(`compConf_perm`), the vertex neighborhood read (`nearPlaq_perm`),
the band neighborhood (`bandVerts_perm`) and the separation read
(`sepBeyond_perm`), so the tower read, the slab read and the head
read are one value at a configuration and its image (`towerAt_perm`,
`slabAt_perm`, `headAt_perm`), and an index member's head read is
its class's (`classOf_head`).  The torus instance: the plaquette
permutation of a composite shift (`torusPlaqShift`, the plaquette's
site moved with its direction pair kept at `pairCount`), the action
at a key list with its witness at the complementary key
(`torusAct`, the composite shift `fiberdec.compShift` the link map
and the site map at once), the action list over the key box
(`torusActs`, `places.keyBox` the translation group's element
list), and the plaquette chain's actions at the iterated shift
(`chainAct`, `chainActs`).
-/

namespace grading
open ground lattice fusion

/-! ### The action list, the orbit and the class list -/

set_option genInjectivity false in
/-- A region action's data: the link map with its witness, the
vertex map with its witness, and the plaquette permutation with its
witness. -/
structure Act where
  t : Nat → Nat
  s : Nat → Nat
  v : Nat → Nat
  w : Nat → Nat
  pm : Nat → Nat
  pm' : Nat → Nat

/-- An action is a region action: the link and vertex isomorphisms
with the endpoint transport, and the plaquette permutation with its
witness. -/
def regionAct (R : Region) (A : Act) : Prop :=
  isoRead R R A.t A.s A.v A.w (fun _ => false)
    ∧ plaqPermRead R A.t (fun _ => false) A.pm A.pm'

instance instGradingindex1 (R : Region) (A : Act) : Decidable (regionAct R A) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every action of the list is a region action. -/
def regionActs (R : Region) (acts : List Act) : Prop :=
  (acts.all (fun A => decide (regionAct R A))) = true

instance instGradingindex2 (R : Region) (acts : List Act) :
    Decidable (regionActs R acts) :=
  inferInstanceAs (Decidable (_ = _))

/-- The list's read at a member. -/
theorem regionActs_at (R : Region) (acts : List Act) (h : regionActs R acts)
    (A : Act) (hA : A ∈ acts) : regionAct R A :=
  of_decide_eq_true (all_of_mem _ acts h A hA)

/-- Two key maps agree on the key range. -/
def agreeAt (n : Nat) (f g : Nat → Nat) : Bool :=
  (List.range n).all (fun l => f l == g l)

/-- The identity among the actions: one action reading the identity
on the key range with its witness. -/
def idAmong (n : Nat) (acts : List Act) : Bool :=
  acts.any (fun A => agreeAt n A.t (fun l => l) && agreeAt n A.s (fun l => l))

/-- The action list is a group on the key range: the identity among
the actions, two actions' composite among them, and each action's
witness among them. -/
def groupRead (n : Nat) (acts : List Act) : Prop :=
  (idAmong n acts
    && acts.all (fun A => acts.all (fun B => acts.any (fun C =>
        agreeAt n C.t (fun l => A.t (B.t l))
          && agreeAt n C.s (fun l => B.s (A.s l)))))
    && acts.all (fun A => acts.any (fun C =>
        agreeAt n C.t A.s && agreeAt n C.s A.t))) = true

instance instGradingindex3 (n : Nat) (acts : List Act) :
    Decidable (groupRead n acts) :=
  inferInstanceAs (Decidable (_ = _))

/-- A configuration's orbit: its images under the action list. -/
def orbitOf {L : Type} (F : Data L) (n : Nat) (acts : List Act)
    (a : List L) : List (List L) :=
  acts.map (fun A => pairpencil.permConf F A.t A.s n a)

/-- A configuration in a second one's orbit, at the interface
equality. -/
def inOrbit {L : Type} (F : Data L) (n : Nat) (acts : List Act)
    (b a : List L) : Bool :=
  carrier.confMem F b (orbitOf F n acts a)

/-- The class collection: one member joined per refusal, the refusal
a joined member's orbit holding the member. -/
def classGo {L : Type} (F : Data L) (n : Nat) (acts : List Act) :
    List (List L) → List (List L) → List (List L)
  | [], cs => cs
  | a :: rest, cs =>
    if cs.any (fun c => inOrbit F n acts a c) then classGo F n acts rest cs
    else classGo F n acts rest (cs ++ [a])

/-- The class list of a stated index: the collection over it. -/
def classList {L : Type} (F : Data L) (n : Nat) (acts : List Act)
    (ix : List (List L)) : List (List L) :=
  classGo F n acts ix []

/-- A class is free where its stabilizer is the identity: every action
reading the class back at the interface equality reads the identity
on the key range with its witness. -/
def freeB {L : Type} (F : Data L) (n : Nat) (acts : List Act) (a : List L) : Bool :=
  acts.all (fun A =>
    !(carrier.eqConf F (pairpencil.permConf F A.t A.s n a) a)
      || (agreeAt n A.t (fun l => l) && agreeAt n A.s (fun l => l)))

/-- The fiber's classes: the free classes of the index. -/
def freeClasses {L : Type} (F : Data L) (n : Nat) (acts : List Act)
    (ix : List (List L)) : List (List L) :=
  (classList F n acts ix).filter (freeB F n acts)

/-- The fiber's graded index at a head bound: the graded index at the
free classes. -/
def fiberIdx {L : Type} (F : Data L) (R : Region) (lamH : Nat) (acts : List Act)
    (ix : List (List L)) : List (List L) × List (List L) :=
  gradedIdx F R lamH (freeClasses F R.links acts ix)

/-- A collected member is a joined member or an index member. -/
private theorem classGo_mem {L : Type} (F : Data L) (n : Nat) (acts : List Act) :
    ∀ (ix cs : List (List L)) (c : List L),
      c ∈ classGo F n acts ix cs → c ∈ cs ∨ c ∈ ix
  | [], _, _, hc => Or.inl hc
  | a :: rest, cs, c, hc => by
    have hc' : c ∈ (if cs.any (fun c => inOrbit F n acts a c)
        then classGo F n acts rest cs
        else classGo F n acts rest (cs ++ [a])) := hc
    cases hg : cs.any (fun c => inOrbit F n acts a c) with
    | true =>
      rw [if_pos hg] at hc'
      cases classGo_mem F n acts rest cs c hc' with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (List.Mem.tail a h)
    | false =>
      rw [if_neg (fun h => Bool.noConfusion (hg.symm.trans h))] at hc'
      cases classGo_mem F n acts rest (cs ++ [a]) c hc' with
      | inl h =>
        cases mem_append_of _ _ h with
        | inl h1 => exact Or.inl h1
        | inr h2 =>
          rw [eq_of_mem_single h2]
          exact Or.inr (List.Mem.head rest)
      | inr h => exact Or.inr (List.Mem.tail a h)

/-- A joined member stays joined along the collection. -/
private theorem classGo_keep {L : Type} (F : Data L) (n : Nat) (acts : List Act) :
    ∀ (ix cs : List (List L)) (c : List L), c ∈ cs → c ∈ classGo F n acts ix cs
  | [], _, _, hc => hc
  | a :: rest, cs, c, hc => by
    show c ∈ (if cs.any (fun c => inOrbit F n acts a c)
        then classGo F n acts rest cs
        else classGo F n acts rest (cs ++ [a]))
    cases hg : cs.any (fun c => inOrbit F n acts a c) with
    | true =>
      rw [if_pos rfl]
      exact classGo_keep F n acts rest cs c hc
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h)]
      exact classGo_keep F n acts rest (cs ++ [a]) c (mem_append_left _ hc)

/-- Every class is an index member. -/
theorem classList_sub {L : Type} (F : Data L) (n : Nat) (acts : List Act)
    (ix : List (List L)) (c : List L) (hc : c ∈ classList F n acts ix) : c ∈ ix := by
  cases classGo_mem F n acts ix [] c hc with
  | inl h => exact nomatch h
  | inr h => exact h

/-- The agreement read at a key. -/
private theorem agree_read (n : Nat) (f g : Nat → Nat) (h : agreeAt n f g = true)
    (l : Nat) (hl : l < n) : f l = g l :=
  beqEqOf (all_range_read n h l hl)

/-- The agreement read from the keys. -/
private theorem agree_intro (n : Nat) (f g : Nat → Nat) (h : ∀ l, l < n → f l = g l) :
    agreeAt n f g = true :=
  all_range_intro n (fun l hl => eqBeqOf (h l hl))

/-- The relabeling at two maps reading the identity on the key range
is the configuration itself. -/
private theorem permConf_id {L : Type} (F : Data L) (t s : Nat → Nat) (n : Nat)
    (ht : ∀ l, l < n → t l = l) (hs : ∀ l, l < n → s l = l)
    (a : List L) (ha : a.length = n) : pairpencil.permConf F t s n a = a := by
  have hl : (pairpencil.permConf F t s n a).length = n := length_mapRange _ n
  refine getAt_ext F.unit _ a (hl.trans ha.symm) (fun i hi => ?_)
  have hi' : i < n := by
    rw [hl] at hi
    exact hi
  show ground.getAt F.unit ((List.range n).map (fun l => if t (s l) == l then
      (if (fun _ => false) (s l) then F.dual (ground.getAt F.unit a (s l))
        else ground.getAt F.unit a (s l)) else F.unit)) i
    = ground.getAt F.unit a i
  rw [getAt_map_range F.unit _ n i, if_pos hi', hs i hi', ht i hi', eqBeqOf rfl]
  rfl

/-- A member of the orbit read at the interface equality: some image
reads the configuration. -/
private theorem confMem_mem {L : Type} (F : Data L) (a : List L) :
    ∀ l : List (List L), carrier.confMem F a l = true →
      ∃ x, x ∈ l ∧ carrier.eqConf F a x = true
  | [], h => Bool.noConfusion h
  | b :: t, h => by
    have h' : (carrier.eqConf F a b || carrier.confMem F a t) = true := h
    cases orSplitB h' with
    | inl h1 => exact ⟨b, List.Mem.head t, h1⟩
    | inr h2 =>
      obtain ⟨x, hx, he⟩ := confMem_mem F a t h2
      exact ⟨x, List.Mem.tail b hx, he⟩

/-- Every index member at the key count sits in a collected member's
orbit at the identity action. -/
private theorem classGo_cover {L : Type} (F : Data L) (n : Nat) (acts : List Act)
    (hid : idAmong n acts = true) :
    ∀ (ix cs : List (List L)), (∀ a ∈ ix, a.length = n) →
      ∀ b ∈ ix, ∃ c, c ∈ classGo F n acts ix cs ∧ inOrbit F n acts b c = true
  | [], _, _, _, hb => nomatch hb
  | a :: rest, cs, hlen, b, hb => by
    cases hg : cs.any (fun c => inOrbit F n acts a c) with
    | true =>
      have heq : classGo F n acts (a :: rest) cs = classGo F n acts rest cs := by
        show (if cs.any (fun c => inOrbit F n acts a c) then _ else _) = _
        rw [if_pos hg]
      rw [heq]
      cases hb with
      | head =>
        obtain ⟨c, hc, hin⟩ := mem_of_any _ cs hg
        exact ⟨c, classGo_keep F n acts rest cs c hc, hin⟩
      | tail _ hb' =>
        exact classGo_cover F n acts hid rest cs
          (fun x hx => hlen x (List.Mem.tail a hx)) b hb'
    | false =>
      have heq : classGo F n acts (a :: rest) cs
          = classGo F n acts rest (cs ++ [a]) := by
        show (if cs.any (fun c => inOrbit F n acts a c) then _ else _) = _
        rw [if_neg (fun h => Bool.noConfusion (hg.symm.trans h))]
      rw [heq]
      cases hb with
      | head =>
        refine ⟨a, classGo_keep F n acts rest (cs ++ [a]) a
          (mem_append_right cs (List.Mem.head [])), ?_⟩
        obtain ⟨A, hA, hAi⟩ := mem_of_any _ acts hid
        have hs := andSplitB hAi
        have h1 : pairpencil.permConf F A.t A.s n a
            ∈ acts.map (fun A => pairpencil.permConf F A.t A.s n a) :=
          mem_map_to _ hA
        rw [permConf_id F A.t A.s n (agree_read n _ _ hs.1) (agree_read n _ _ hs.2) a
          (hlen a (List.Mem.head rest))] at h1
        exact carrier.confMem_of_mem F a _ h1
      | tail _ hb' =>
        exact classGo_cover F n acts hid rest (cs ++ [a])
          (fun x hx => hlen x (List.Mem.tail a hx)) b hb'

/-- Every index member at the key count sits in a class's orbit, the
identity among the actions. -/
theorem classList_cover {L : Type} (F : Data L) (n : Nat) (acts : List Act)
    (hid : idAmong n acts = true) (ix : List (List L))
    (hlen : ∀ a ∈ ix, a.length = n) (b : List L) (hb : b ∈ ix) :
    ∃ c, c ∈ classList F n acts ix ∧ inOrbit F n acts b c = true :=
  classGo_cover F n acts hid ix [] hlen b hb

/-- Two relabelings compose to the relabeling at the composed maps,
at actions keeping the key range with their witnesses. -/
private theorem permConf_comp {L : Type} (F : Data L) (n : Nat)
    (t s t' s' : Nat → Nat)
    (h : ∀ l, l < n → s (t l) = l ∧ t (s l) = l ∧ t l < n ∧ s l < n)
    (h' : ∀ l, l < n → s' (t' l) = l ∧ t' (s' l) = l ∧ t' l < n ∧ s' l < n)
    (a : List L) :
    pairpencil.permConf F t s n (pairpencil.permConf F t' s' n a)
      = pairpencil.permConf F (fun l => t (t' l)) (fun l => s' (s l)) n a := by
  refine getAt_ext F.unit _ _ ((length_mapRange _ n).trans (length_mapRange _ n).symm)
    (fun i hi => ?_)
  have hi' : i < n := by
    rw [show (pairpencil.permConf F t s n (pairpencil.permConf F t' s' n a)).length = n
      from length_mapRange _ n] at hi
    exact hi
  rw [fiberdec.getAt_permConf F t s n _ i hi' (h i hi').2.1,
    fiberdec.getAt_permConf F t' s' n a (s i) (h i hi').2.2.2
      (h' (s i) (h i hi').2.2.2).2.1]
  show _ = ground.getAt F.unit ((List.range n).map (fun l =>
    if t (t' (s' (s l))) == l then
      (if (fun _ => false) (s' (s l)) then F.dual (ground.getAt F.unit a (s' (s l)))
        else ground.getAt F.unit a (s' (s l))) else F.unit)) i
  rw [getAt_map_range F.unit _ n i, if_pos hi',
    (h' (s i) (h i hi').2.2.2).2.1, (h i hi').2.1, eqBeqOf rfl]
  rfl

/-- Two relabelings at maps agreeing on the key range are one list,
the witness keeping the range. -/
private theorem permConf_agree {L : Type} (F : Data L) (n : Nat)
    (t s t' s' : Nat → Nat) (ht : ∀ l, l < n → t l = t' l)
    (hs : ∀ l, l < n → s l = s' l) (hsr : ∀ l, l < n → s l < n) (a : List L) :
    pairpencil.permConf F t s n a = pairpencil.permConf F t' s' n a := by
  show (List.range n).map _ = (List.range n).map _
  refine map_congr_members _ _ (List.range n) (fun l hl => ?_)
  have hl' : l < n := ltOfMem hl
  have hsl : s l = s' l := hs l hl'
  have htl : t (s l) = t' (s l) := ht (s l) (hsr l hl')
  show (if t (s l) == l then
      (if (fun _ => false) (s l) then F.dual (ground.getAt F.unit a (s l))
        else ground.getAt F.unit a (s l)) else F.unit)
    = (if t' (s' l) == l then
      (if (fun _ => false) (s' l) then F.dual (ground.getAt F.unit a (s' l))
        else ground.getAt F.unit a (s' l)) else F.unit)
  rw [htl, hsl]

/-- Along the collection every joined member sits off every earlier
joined member's orbit. -/
private theorem classGo_guard {L : Type} (F : Data L) (n : Nat) (acts : List Act) :
    ∀ (ix cs : List (List L)),
      (∀ i j, i < j → j < cs.length →
        inOrbit F n acts (ground.getAt [] cs j) (ground.getAt [] cs i) = false) →
      ∀ i j, i < j → j < (classGo F n acts ix cs).length →
        inOrbit F n acts (ground.getAt [] (classGo F n acts ix cs) j)
          (ground.getAt [] (classGo F n acts ix cs) i) = false
  | [], _, hcs, i, j, hij, hj => hcs i j hij hj
  | a :: rest, cs, hcs, i, j, hij, hj => by
    have heq : classGo F n acts (a :: rest) cs
        = (if cs.any (fun c => inOrbit F n acts a c)
          then classGo F n acts rest cs
          else classGo F n acts rest (cs ++ [a])) := rfl
    rw [heq] at hj ⊢
    cases hg : cs.any (fun c => inOrbit F n acts a c) with
    | true =>
      rw [if_pos hg] at hj
      rw [if_pos rfl]
      exact classGo_guard F n acts rest cs hcs i j hij hj
    | false =>
      rw [if_neg (fun h => Bool.noConfusion (hg.symm.trans h))] at hj
      rw [if_neg (fun h => Bool.noConfusion h)]
      refine classGo_guard F n acts rest (cs ++ [a]) (fun i j hij hj => ?_) i j hij hj
      rw [length_append] at hj
      have hi : i < cs.length := Nat.lt_of_lt_of_le hij (Nat.le_of_lt_succ hj)
      rw [getAt_append [] cs [a] i, if_pos hi]
      cases Nat.lt_or_ge j cs.length with
      | inl hjc =>
        rw [getAt_append [] cs [a] j, if_pos hjc]
        exact hcs i j hij hjc
      | inr hjc =>
        have hjeq : j = cs.length := Nat.le_antisymm (Nat.le_of_lt_succ hj) hjc
        rw [getAt_append [] cs [a] j, if_neg (Nat.not_lt_of_ge hjc), hjeq, Nat.sub_self]
        show inOrbit F n acts a (ground.getAt [] cs i) = false
        have hall := all_not_of_any_false _ cs hg
        exact boolFalseOfNot (all_of_mem _ cs hall _ (mem_getAt [] cs i hi))

/-- Two classes at distinct places hold one configuration in both
orbits: the action list a group on the key range, the actions region
actions at their witnesses, and the configurations over a label
domain at one spelling per label. -/
theorem classList_disjoint {L : Type} (F : Data L) (R : Region) (acts : List Act)
    (hacts : regionActs R acts) (hgrp : groupRead R.links acts)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (ix : List (List L)) (hlen : ∀ a ∈ ix, a.length = R.links)
    (hix : ∀ a ∈ ix, a.all P = true) (i j : Nat) (hij : i < j)
    (hj : j < (classList F R.links acts ix).length) (b : List L)
    (hbP : b.all P = true)
    (hbi : inOrbit F R.links acts b (ground.getAt [] (classList F R.links acts ix) i) = true)
    (hbj : inOrbit F R.links acts b (ground.getAt [] (classList F R.links acts ix) j) = true) :
    False := by
  have hguard : inOrbit F R.links acts
      (ground.getAt [] (classList F R.links acts ix) j)
      (ground.getAt [] (classList F R.links acts ix) i) = false :=
    classGo_guard F R.links acts ix [] (fun _ j _ hj => absurd hj (Nat.not_lt_zero _))
      i j hij hj
  have hiso : ∀ A, A ∈ acts → ∀ l, l < R.links →
      A.s (A.t l) = l ∧ A.t (A.s l) = l ∧ A.t l < R.links ∧ A.s l < R.links :=
    fun A hA l hl => linkIso_all R A.t A.s (regionActs_at R acts hacts A hA).1.1 l hl
  have hcomp := (andSplitB (andSplitB hgrp).1).2
  have hinv := (andSplitB hgrp).2
  have hcj : ground.getAt [] (classList F R.links acts ix) j ∈ ix :=
    classList_sub F R.links acts ix _ (mem_getAt [] _ j hj)
  have hci : ground.getAt [] (classList F R.links acts ix) i ∈ ix :=
    classList_sub F R.links acts ix _ (mem_getAt [] _ i (Nat.lt_trans hij hj))
  obtain ⟨x, hx, hbx⟩ := confMem_mem F b _ hbi
  obtain ⟨A, hA, hAb⟩ := mem_map_of _ acts x hx
  obtain ⟨y, hy, hby⟩ := confMem_mem F b _ hbj
  obtain ⟨B, hB, hBb⟩ := mem_map_of _ acts y hy
  have hxeq : b = pairpencil.permConf F A.t A.s R.links
      (ground.getAt [] (classList F R.links acts ix) i) := by
    rw [hAb]
    exact carrier.eqConf_eq F P hred b x hbP (by
      rw [← hAb]
      exact fiberdec.permConf_all F A.t A.s R.links P hunitP _ (hix _ hci)) hbx
  have hyeq : b = pairpencil.permConf F B.t B.s R.links
      (ground.getAt [] (classList F R.links acts ix) j) := by
    rw [hBb]
    exact carrier.eqConf_eq F P hred b y hbP (by
      rw [← hBb]
      exact fiberdec.permConf_all F B.t B.s R.links P hunitP _ (hix _ hcj)) hby
  obtain ⟨C, hC, hCB⟩ := mem_of_any _ acts (all_of_mem _ acts hinv B hB)
  have hCs := andSplitB hCB
  obtain ⟨D, hD, hDC⟩ := mem_of_any _ acts (all_of_mem _ acts
    (all_of_mem _ acts hcomp C hC) A hA)
  have hDs := andSplitB hDC
  have hBiso := hiso B hB
  have hAiso := hiso A hA
  have hCiso := hiso C hC
  have hCB' : pairpencil.permConf F C.t C.s R.links b
      = ground.getAt [] (classList F R.links acts ix) j := by
    rw [hyeq, permConf_comp F R.links C.t C.s B.t B.s hCiso hBiso]
    refine (permConf_agree F R.links (fun l => C.t (B.t l)) (fun l => B.s (C.s l))
      (fun l => l) (fun l => l) ?_ ?_
      (fun l hl => (hBiso _ (hCiso l hl).2.2.2).2.2.2) _).trans
      (permConf_id F _ _ R.links (fun l _ => rfl) (fun l _ => rfl) _ (hlen _ hcj))
    · intro l hl
      show C.t (B.t l) = l
      rw [agree_read _ _ _ hCs.1 (B.t l) (hBiso l hl).2.2.1, (hBiso l hl).1]
    · intro l hl
      show B.s (C.s l) = l
      rw [agree_read _ _ _ hCs.2 l hl, (hBiso l hl).1]
  have hDi : pairpencil.permConf F C.t C.s R.links b
      = pairpencil.permConf F D.t D.s R.links
        (ground.getAt [] (classList F R.links acts ix) i) := by
    rw [hxeq, permConf_comp F R.links C.t C.s A.t A.s hCiso hAiso]
    exact permConf_agree F R.links (fun l => C.t (A.t l)) (fun l => A.s (C.s l))
      D.t D.s (fun l hl => (agree_read _ _ _ hDs.1 l hl).symm)
      (fun l hl => (agree_read _ _ _ hDs.2 l hl).symm)
      (fun l hl => (hAiso _ (hCiso l hl).2.2.2).2.2.2) _
  have hin : inOrbit F R.links acts (ground.getAt [] (classList F R.links acts ix) j)
      (ground.getAt [] (classList F R.links acts ix) i) = true := by
    refine carrier.confMem_of_mem F _ _ ?_
    rw [← hCB', hDi]
    exact mem_map_to _ hD
  rw [hguard] at hin
  exact Bool.noConfusion hin

/-- The free read at an action reading the class back: the action
reads the identity. -/
private theorem free_read {L : Type} (F : Data L) (n : Nat) (acts : List Act) (a : List L)
    (hf : freeB F n acts a = true) (B : Act) (hB : B ∈ acts)
    (he : carrier.eqConf F (pairpencil.permConf F B.t B.s n a) a = true) :
    (∀ l, l < n → B.t l = l) ∧ (∀ l, l < n → B.s l = l) := by
  have h1 : (!(carrier.eqConf F (pairpencil.permConf F B.t B.s n a) a)
      || (agreeAt n B.t (fun l => l) && agreeAt n B.s (fun l => l))) = true :=
    all_of_mem _ acts hf B hB
  rw [he] at h1
  have h2 := andSplitB h1
  exact ⟨agree_read n _ _ h2.1, agree_read n _ _ h2.2⟩

/-- The free read from its actions. -/
private theorem free_intro {L : Type} (F : Data L) (n : Nat) (acts : List Act) (a : List L)
    (hf : ∀ B, B ∈ acts → carrier.eqConf F (pairpencil.permConf F B.t B.s n a) a = true →
      (∀ l, l < n → B.t l = l) ∧ (∀ l, l < n → B.s l = l)) :
    freeB F n acts a = true := by
  refine all_of_mem_intro _ acts (fun B hB => ?_)
  show (!(carrier.eqConf F (pairpencil.permConf F B.t B.s n a) a)
    || (agreeAt n B.t (fun l => l) && agreeAt n B.s (fun l => l))) = true
  cases he : carrier.eqConf F (pairpencil.permConf F B.t B.s n a) a with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := hf B hB he
    rw [agree_intro n _ _ h1, agree_intro n _ _ h2]
    rfl

/-- The free read is one value along the orbit: a class's stabilizer
is the identity exactly where its image's is, the stabilizers
conjugate at the action. -/
theorem freeB_perm {L : Type} (F : Data L) (R : Region) (acts : List Act)
    (hacts : regionActs R acts) (hgrp : groupRead R.links acts)
    (P : L → Bool) (hunitP : P F.unit = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (A : Act) (hA : A ∈ acts) (c : List L) (hc : c.length = R.links)
    (hcP : c.all P = true) :
    freeB F R.links acts (pairpencil.permConf F A.t A.s R.links c)
      = freeB F R.links acts c := by
  have hiso : ∀ B, B ∈ acts → ∀ l, l < R.links →
      B.s (B.t l) = l ∧ B.t (B.s l) = l ∧ B.t l < R.links ∧ B.s l < R.links :=
    fun B hB l hl => linkIso_all R B.t B.s (regionActs_at R acts hacts B hB).1.1 l hl
  have hcomp := (andSplitB (andSplitB hgrp).1).2
  have hinv := (andSplitB hgrp).2
  have hcm : ∀ X Y, X ∈ acts → Y ∈ acts → ∃ Z, Z ∈ acts
      ∧ (∀ l, l < R.links → Z.t l = X.t (Y.t l))
      ∧ (∀ l, l < R.links → Z.s l = Y.s (X.s l)) := by
    intro X Y hX hY
    obtain ⟨Z, hZ, hZE⟩ := mem_of_any _ acts (all_of_mem _ acts
      (all_of_mem _ acts hcomp X hX) Y hY)
    have hs := andSplitB hZE
    exact ⟨Z, hZ, fun l hl => agree_read _ _ _ hs.1 l hl,
      fun l hl => agree_read _ _ _ hs.2 l hl⟩
  obtain ⟨Ai, hAi, hAiE⟩ := mem_of_any _ acts (all_of_mem _ acts hinv A hA)
  have hAis := andSplitB hAiE
  have hAit : ∀ l, l < R.links → Ai.t l = A.s l := fun l hl => agree_read _ _ _ hAis.1 l hl
  have hAis' : ∀ l, l < R.links → Ai.s l = A.t l := fun l hl => agree_read _ _ _ hAis.2 l hl
  have hAiso := hiso A hA
  have hAiiso := hiso Ai hAi
  have hAc : (pairpencil.permConf F A.t A.s R.links c).length = R.links := length_mapRange _ _
  have hAcP : (pairpencil.permConf F A.t A.s R.links c).all P = true :=
    fiberdec.permConf_all F A.t A.s R.links P hunitP c hcP
  have heq : ∀ (a b : List L), a.all P = true → b.all P = true →
      carrier.eqConf F a b = true → a = b :=
    fun a b ha hb he => carrier.eqConf_eq F P hred a b ha hb he
  have hAiA : ∀ a : List L, a.length = R.links →
      pairpencil.permConf F Ai.t Ai.s R.links (pairpencil.permConf F A.t A.s R.links a) = a := by
    intro a ha
    rw [permConf_comp F R.links Ai.t Ai.s A.t A.s hAiiso hAiso]
    exact permConf_id F _ _ R.links
      (fun l hl => by
        show Ai.t (A.t l) = l
        rw [hAit _ (hAiso l hl).2.2.1, (hAiso l hl).1])
      (fun l hl => by
        show A.s (Ai.s l) = l
        rw [hAis' l hl, (hAiso l hl).1]) a ha
  have fwd : freeB F R.links acts (pairpencil.permConf F A.t A.s R.links c) = true →
      freeB F R.links acts c = true := by
    intro hf
    refine free_intro F R.links acts c (fun B hB he => ?_)
    have hBiso := hiso B hB
    have hBc : pairpencil.permConf F B.t B.s R.links c = c :=
      heq _ _ (fiberdec.permConf_all F B.t B.s R.links P hunitP c hcP) hcP he
    obtain ⟨D, hD, hDt, hDs⟩ := hcm A B hA hB
    obtain ⟨E, hE, hEt, hEs⟩ := hcm D Ai hD hAi
    have hDiso := hiso D hD
    have hEiso := hiso E hE
    have hEt' : ∀ l, l < R.links → E.t (A.t l) = A.t (B.t l) := by
      intro l hl
      rw [hEt _ (hAiso l hl).2.2.1, hAit _ (hAiso l hl).2.2.1, (hAiso l hl).1, hDt l hl]
    have hEs' : ∀ l, l < R.links → A.s (E.s l) = B.s (A.s l) := by
      intro l hl
      rw [hEs l hl, hAis' _ (hDiso l hl).2.2.2, (hAiso _ (hDiso l hl).2.2.2).1, hDs l hl]
    have hEA : pairpencil.permConf F E.t E.s R.links (pairpencil.permConf F A.t A.s R.links c)
        = pairpencil.permConf F A.t A.s R.links c := by
      rw [permConf_comp F R.links E.t E.s A.t A.s hEiso hAiso,
        permConf_agree F R.links (fun l => E.t (A.t l)) (fun l => A.s (E.s l))
          (fun l => A.t (B.t l)) (fun l => B.s (A.s l)) hEt' hEs'
          (fun l hl => (hAiso _ (hEiso l hl).2.2.2).2.2.2) c,
        ← permConf_comp F R.links A.t A.s B.t B.s hAiso hBiso, hBc]
    have hEid := free_read F R.links acts _ hf E hE (by
      rw [hEA]
      exact carrier.eqConf_refl F _)
    refine ⟨fun l hl => ?_, fun l hl => ?_⟩
    · have h1 : A.t (B.t l) = A.t l := by
        rw [← hEt' l hl, hEid.1 _ (hAiso l hl).2.2.1]
      have h2 := congrArg A.s h1
      rw [(hAiso _ (hBiso l hl).2.2.1).1, (hAiso l hl).1] at h2
      exact h2
    · have h1 : ∀ m, m < R.links → B.s (A.s m) = A.s m := by
        intro m hm
        rw [← hEs' m hm, hEid.2 m hm]
      have h2 := h1 (A.t l) (hAiso l hl).2.2.1
      rw [(hAiso l hl).1] at h2
      exact h2
  have bwd : freeB F R.links acts c = true →
      freeB F R.links acts (pairpencil.permConf F A.t A.s R.links c) = true := by
    intro hf
    refine free_intro F R.links acts _ (fun B hB he => ?_)
    have hBiso := hiso B hB
    have hBAc : pairpencil.permConf F B.t B.s R.links (pairpencil.permConf F A.t A.s R.links c)
        = pairpencil.permConf F A.t A.s R.links c :=
      heq _ _ (fiberdec.permConf_all F B.t B.s R.links P hunitP _ hAcP) hAcP he
    obtain ⟨D, hD, hDt, hDs⟩ := hcm Ai B hAi hB
    obtain ⟨E, hE, hEt, hEs⟩ := hcm D A hD hA
    have hDiso := hiso D hD
    have hEiso := hiso E hE
    have hEt' : ∀ l, l < R.links → E.t l = A.s (B.t (A.t l)) := by
      intro l hl
      rw [hEt l hl, hDt _ (hAiso l hl).2.2.1, hAit _ (hBiso _ (hAiso l hl).2.2.1).2.2.1]
    have hEs' : ∀ l, l < R.links → E.s l = A.s (B.s (A.t l)) := by
      intro l hl
      rw [hEs l hl, hDs l hl, hAis' l hl]
    have hEc : pairpencil.permConf F E.t E.s R.links c = c := by
      have hDA : pairpencil.permConf F D.t D.s R.links (pairpencil.permConf F A.t A.s R.links c)
          = pairpencil.permConf F E.t E.s R.links c := by
        rw [permConf_comp F R.links D.t D.s A.t A.s hDiso hAiso]
        exact permConf_agree F R.links _ _ E.t E.s (fun l hl => (hEt l hl).symm)
          (fun l hl => (hEs l hl).symm) (fun l hl => (hAiso _ (hDiso l hl).2.2.2).2.2.2) c
      have hAiB : pairpencil.permConf F Ai.t Ai.s R.links
          (pairpencil.permConf F B.t B.s R.links (pairpencil.permConf F A.t A.s R.links c))
          = pairpencil.permConf F D.t D.s R.links (pairpencil.permConf F A.t A.s R.links c) := by
        rw [permConf_comp F R.links Ai.t Ai.s B.t B.s hAiiso hBiso]
        exact permConf_agree F R.links _ _ D.t D.s (fun l hl => (hDt l hl).symm)
          (fun l hl => (hDs l hl).symm) (fun l hl => (hBiso _ (hAiiso l hl).2.2.2).2.2.2) _
      rw [← hDA, ← hAiB, hBAc, hAiA c hc]
    have hEid := free_read F R.links acts c hf E hE (by
      rw [hEc]
      exact carrier.eqConf_refl F c)
    refine ⟨fun l hl => ?_, fun l hl => ?_⟩
    · have h1 : A.s (B.t (A.t (A.s l))) = A.s l := by
        rw [← hEt' _ (hAiso l hl).2.2.2, hEid.1 _ (hAiso l hl).2.2.2]
      rw [(hAiso l hl).2.1] at h1
      have h2 := congrArg A.t h1
      rw [(hAiso _ (hBiso l hl).2.2.1).2.1, (hAiso l hl).2.1] at h2
      exact h2
    · have h1 : A.s (B.s (A.t (A.s l))) = A.s l := by
        rw [← hEs' _ (hAiso l hl).2.2.2, hEid.2 _ (hAiso l hl).2.2.2]
      rw [(hAiso l hl).2.1] at h1
      have h2 := congrArg A.t h1
      rw [(hAiso _ (hBiso l hl).2.2.2).2.1, (hAiso l hl).2.1] at h2
      exact h2
  cases h1 : freeB F R.links acts (pairpencil.permConf F A.t A.s R.links c) with
  | true => exact (fwd h1).symm
  | false =>
    cases h2 : freeB F R.links acts c with
    | true =>
      have h3 := bwd h2
      rw [h1] at h3
      exact Bool.noConfusion h3
    | false => rfl

/-! ### The transport at a region action -/

/-- The support's keys sit below the region's count. -/
private theorem support_lt {L : Type} (F : Data L) (R : Region) (a : List L)
    (x : Nat) (hx : x ∈ carrier.support F R a) : x < R.links :=
  ltOfMemRange (mem_filter_of _ _ x hx).1

/-- The band components transport along a region action: every
component of the relabeled configuration is a component of the
configuration moved, member for member, and every component of the
configuration moves to one. -/
theorem components_perm {L : Type} (F : Data L) (R : Region) (hw : wellRead R)
    (hpr : plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false))
    (hpm : plaqPermRead R t (fun _ => false) pm pm') (a : List L) :
    (∀ c', c' ∈ components F R (pairpencil.permConf F t s R.links a) →
      ∃ c, c ∈ components F R a ∧ ∀ x, x < R.links → (x ∈ c' ↔ s x ∈ c))
    ∧ (∀ c, c ∈ components F R a →
      ∃ c', c' ∈ components F R (pairpencil.permConf F t s R.links a)
        ∧ ∀ x, x < R.links → (x ∈ c' ↔ s x ∈ c)) := by
  have hiso := linkIso_all R t s h.1
  have hS := fiberdec.support_perm F R t s h.1 a
  have hSR := support_lt F R a
  have hS'R := support_lt F R (pairpencil.permConf F t s R.links a)
  constructor
  · intro c' hc'
    obtain ⟨l', hl'c, hc'l⟩ := components_compOf F R _ c' hc'
    have hl'S : l' ∈ carrier.support F R (pairpencil.permConf F t s R.links a) := by
      rw [hc'l] at hl'c
      exact (mem_filter_of _ _ l' hl'c).1
    have hl'R := hS'R l' hl'S
    have hslS : s l' ∈ carrier.support F R a := (hS l' hl'R).1 hl'S
    obtain ⟨c, hc, hcl⟩ := compOf_mem_components F R a (s l') hslS
    refine ⟨c, hc, fun x hx => ?_⟩
    rw [hc'l, hcl]
    have h2 := compOf_perm R hw hpr t s v w pm pm' h hpm _ _ hS hSR hS'R (s l')
      (hiso l' hl'R).2.2.2 x hx
    rw [(hiso l' hl'R).2.1] at h2
    exact h2
  · intro c hc
    obtain ⟨l, hlc, hcl⟩ := components_compOf F R a c hc
    have hlS : l ∈ carrier.support F R a := by
      rw [hcl] at hlc
      exact (mem_filter_of _ _ l hlc).1
    have hlR := hSR l hlS
    have htlS : t l ∈ carrier.support F R (pairpencil.permConf F t s R.links a) := by
      refine (hS (t l) (hiso l hlR).2.2.1).2 ?_
      rw [(hiso l hlR).1]
      exact hlS
    obtain ⟨c', hc', hc'l⟩ := compOf_mem_components F R _ (t l) htlS
    refine ⟨c', hc', fun x hx => ?_⟩
    rw [hc'l, hcl]
    exact compOf_perm R hw hpr t s v w pm pm' h hpm _ _ hS hSR hS'R l hlR x hx

/-- A component's content transports along the action. -/
theorem compContent_perm {L : Type} (F : Data L) (R : Region) (t s : Nat → Nat)
    (h : linkIso R R t s) (a : List L) (c c' : List Nat)
    (hc : distinctList c) (hc' : distinctList c')
    (hcR : ∀ x ∈ c, x < R.links) (hc'R : ∀ x ∈ c', x < R.links)
    (hrel : ∀ x, x < R.links → (x ∈ c' ↔ s x ∈ c)) :
    compContent F (pairpencil.permConf F t s R.links a) c' = compContent F a c := by
  have hiso := linkIso_all R t s h
  show carrier.contentN F (c'.map (ground.getAt F.unit (pairpencil.permConf F t s R.links a)))
    = carrier.contentN F (c.map (ground.getAt F.unit a))
  rw [carrier.contentN_fam, carrier.contentN_fam, famFold_map, famFold_map]
  have step1 : famFold Nat.add 0 (fun x =>
      if F.eqL (ground.getAt F.unit (pairpencil.permConf F t s R.links a) x) F.unit
        then 0 else F.c2N (ground.getAt F.unit (pairpencil.permConf F t s R.links a) x)) c'
      = famFold Nat.add 0 (fun x =>
        if F.eqL (ground.getAt F.unit a (s x)) F.unit then 0
        else F.c2N (ground.getAt F.unit a (s x))) c' := by
    refine famFold_congr_members _ _ _ _ c' (fun x hx => ?_)
    have hxR := hc'R x (mem_of_countOf_pos x c' hx)
    rw [fiberdec.getAt_permConf F t s R.links a x hxR (hiso x hxR).2.1]
  have step2 : famFold Nat.add 0 (fun x =>
        if F.eqL (ground.getAt F.unit a (s x)) F.unit then 0
        else F.c2N (ground.getAt F.unit a (s x))) c'
      = famFold Nat.add 0 (fun x =>
        if F.eqL (ground.getAt F.unit a x) F.unit then 0
        else F.c2N (ground.getAt F.unit a x)) (c'.map s) :=
    (famFold_map Nat.add 0 (fun x =>
        if F.eqL (ground.getAt F.unit a x) F.unit then 0
        else F.c2N (ground.getAt F.unit a x)) s c').symm
  rw [step1, step2,
    famFold_partition _ (c'.map s) c hc (fun y hy => by
      obtain ⟨x, hx, hxy⟩ := mem_map_of _ _ y hy
      rw [← hxy]
      exact (hrel x (hc'R x hx)).1 hx),
    famFold_partition _ c c hc (fun x hx => hx)]
  refine famFold_congr_members _ _ _ _ c (fun k hk => ?_)
  have hkc : k ∈ c := mem_of_countOf_pos k c hk
  have hkR := hcR k hkc
  have h1 : countOf k c = 1 := Nat.le_antisymm (hc k hkc) hk
  have htk : t k ∈ c' := by
    refine (hrel (t k) (hiso k hkR).2.2.1).2 ?_
    rw [(hiso k hkR).1]
    exact hkc
  have h3 : countOf (t k) c' = 1 :=
    Nat.le_antisymm (hc' _ htk) (countOf_pos_of_mem htk)
  have h2 : countOf (s (t k)) (c'.map s) = countOf (t k) c' :=
    countOf_map_inj s (t k) c' (fun x hx he => by
      have hxR := hc'R x (mem_of_countOf_pos x c' hx)
      rw [← (hiso x hxR).2.1, he, (hiso k hkR).1])
  rw [(hiso k hkR).1] at h2
  rw [h2, h3, h1]
  repeat rw [Nat.one_mul]

/-- A component's own configuration transports along the action:
the moved component's configuration is the component's relabeled. -/
theorem compConf_perm {L : Type} (F : Data L) (R : Region) (t s : Nat → Nat)
    (h : linkIso R R t s) (a : List L) (c c' : List Nat)
    (hrel : ∀ x, x < R.links → (x ∈ c' ↔ s x ∈ c)) :
    compConf F R (pairpencil.permConf F t s R.links a) c'
      = pairpencil.permConf F t s R.links (compConf F R a c) := by
  have hiso := linkIso_all R t s h
  refine getAt_ext F.unit _ _ ((length_mapRange _ _).trans (length_mapRange _ _).symm)
    (fun k hk => ?_)
  have hk' : k < R.links := by
    rw [show (compConf F R (pairpencil.permConf F t s R.links a) c').length = R.links
      from length_mapRange _ _] at hk
    exact hk
  rw [fiberdec.getAt_permConf F t s R.links _ k hk' (hiso k hk').2.1]
  show ground.getAt F.unit ((List.range R.links).map (fun l =>
      if containsB c' l then ground.getAt F.unit (pairpencil.permConf F t s R.links a) l
      else F.unit)) k
    = ground.getAt F.unit ((List.range R.links).map (fun l =>
      if containsB c l then ground.getAt F.unit a l else F.unit)) (s k)
  rw [getAt_map_range, getAt_map_range, if_pos hk', if_pos (hiso k hk').2.2.2,
    fiberdec.getAt_permConf F t s R.links a k hk' (hiso k hk').2.1]
  have hcb : containsB c' k = containsB c (s k) := by
    cases hm : containsB c (s k) with
    | true => exact containsB_of_mem ((hrel k hk').2 (mem_of_containsB hm))
    | false =>
      refine containsB_of_not_mem (fun hin => ?_)
      rw [containsB_of_mem ((hrel k hk').1 hin)] at hm
      exact Bool.noConfusion hm
  rw [hcb]

/-- A touched vertex sits below the vertex count. -/
private theorem touched_lt {L : Type} (F : Data L) (R : Region) (a : List L)
    (y : Nat) (hy : y ∈ carrier.touched F R a) : y < R.verts :=
  ltOfMemRange (mem_filter_of _ _ y hy).1

/-- The vertex neighborhood read transports: the relabeled
configuration meets the moved plaquette exactly where the
configuration meets the plaquette. -/
theorem nearPlaq_perm {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false))
    (hpm : plaqPermRead R t (fun _ => false) pm pm') (a : List L) (q : Nat)
    (hq : q < R.plaqs.length) :
    stableentries.nearPlaq F R (pairpencil.permConf F t s R.links a)
        (ground.getAt [] R.plaqs (pm q))
      = stableentries.nearPlaq F R a (ground.getAt [] R.plaqs q) := by
  have hc := (plaqPermRead_at R t _ pm pm' hpm q hq).2.2.2.2
  have hkeys : ((ground.getAt [] R.plaqs q).all (fun e => e.1 < R.links)) = true :=
    (plaqRead_word R hpr _ (mem_getAt [] R.plaqs q hq)).2
  have key : ∀ y, y < R.verts →
      (ground.getAt [] R.plaqs (pm q)).any (fun e => startOf R e == v y || endOf R e == v y)
        = (ground.getAt [] R.plaqs q).any (fun e => startOf R e == y || endOf R e == y) := by
    intro y hy
    rw [← plaqVert_cyc R _ _ hc, plaqVert_move R hw t s v w h _ hkeys y hy]
  cases hb : stableentries.nearPlaq F R a (ground.getAt [] R.plaqs q) with
  | true =>
    obtain ⟨y, hy, hyp⟩ := mem_of_any _ _ hb
    have hyv := touched_lt F R a y hy
    refine any_of_mem _ ((fiberdec.touched_perm F R hw t s v w h a y hyv).2 hy) ?_
    rw [key y hyv]
    exact hyp
  | false =>
    refine any_false_of_all_not _ _ (all_of_mem_intro _ _ (fun y' hy' => ?_))
    have hy'v := touched_lt F R _ y' hy'
    have hwy : w y' < R.verts := (vertIso_all R v w h.2.1 y' hy'v).2.2.2
    have hvw : v (w y') = y' := (vertIso_all R v w h.2.1 y' hy'v).2.1
    have hmem : w y' ∈ carrier.touched F R a := by
      refine (fiberdec.touched_perm F R hw t s v w h a (w y') hwy).1 ?_
      rw [hvw]
      exact hy'
    have h3 := all_of_mem _ _ (all_not_of_any_false _ _ hb) _ hmem
    show (!((ground.getAt [] R.plaqs (pm q)).any
      (fun e => startOf R e == y' || endOf R e == y'))) = true
    rw [← hvw, key (w y') hwy]
    exact h3

/-- The band neighborhood moves along the vertex map. -/
theorem bandVerts_perm {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false))
    (hpm : plaqPermRead R t (fun _ => false) pm pm') (a : List L) (y : Nat)
    (hy : y < R.verts) :
    v y ∈ bandVerts F R (pairpencil.permConf F t s R.links a)
      ↔ y ∈ bandVerts F R a := by
  have hvy : v y < R.verts := (vertIso_all R v w h.2.1 y hy).2.2.1
  have hcb : containsB (carrier.touched F R (pairpencil.permConf F t s R.links a)) (v y)
      = containsB (carrier.touched F R a) y := by
    cases hm : containsB (carrier.touched F R a) y with
    | true =>
      exact containsB_of_mem ((fiberdec.touched_perm F R hw t s v w h a y hy).2
        (mem_of_containsB hm))
    | false =>
      refine containsB_of_not_mem (fun hin => ?_)
      rw [containsB_of_mem ((fiberdec.touched_perm F R hw t s v w h a y hy).1 hin)] at hm
      exact Bool.noConfusion hm
  have hany : R.plaqs.any (fun p =>
        stableentries.nearPlaq F R (pairpencil.permConf F t s R.links a) p
          && p.any (fun e => startOf R e == v y || endOf R e == v y))
      = R.plaqs.any (fun p => stableentries.nearPlaq F R a p
          && p.any (fun e => startOf R e == y || endOf R e == y)) := by
    refine plaqPerm_any R t (fun _ => false) pm pm' hpm _ _ (fun q hq => ?_)
    have hc := (plaqPermRead_at R t _ pm pm' hpm q hq).2.2.2.2
    have hkeys : ((ground.getAt [] R.plaqs q).all (fun e => e.1 < R.links)) = true :=
      (plaqRead_word R hpr _ (mem_getAt [] R.plaqs q hq)).2
    show (stableentries.nearPlaq F R (pairpencil.permConf F t s R.links a)
        (ground.getAt [] R.plaqs (pm q))
      && (ground.getAt [] R.plaqs (pm q)).any
        (fun e => startOf R e == v y || endOf R e == v y))
      = (stableentries.nearPlaq F R a (ground.getAt [] R.plaqs q)
      && (ground.getAt [] R.plaqs q).any (fun e => startOf R e == y || endOf R e == y))
    rw [nearPlaq_perm F R hw hpr t s v w pm pm' h hpm a q hq,
      ← plaqVert_cyc R _ _ hc, plaqVert_move R hw t s v w h _ hkeys y hy]
  constructor
  · intro hm
    have hp : (containsB (carrier.touched F R (pairpencil.permConf F t s R.links a)) (v y)
        || R.plaqs.any (fun p =>
          stableentries.nearPlaq F R (pairpencil.permConf F t s R.links a) p
            && p.any (fun e => startOf R e == v y || endOf R e == v y))) = true :=
      (mem_filter_of _ _ _ hm).2
    rw [hcb, hany] at hp
    exact mem_filter_to _ (memRange hy) hp
  · intro hm
    have hp : (containsB (carrier.touched F R a) y
        || R.plaqs.any (fun p => stableentries.nearPlaq F R a p
          && p.any (fun e => startOf R e == y || endOf R e == y))) = true :=
      (mem_filter_of _ _ _ hm).2
    refine mem_filter_to _ (memRange hvy) ?_
    show (containsB (carrier.touched F R (pairpencil.permConf F t s R.links a)) (v y)
        || R.plaqs.any (fun p =>
          stableentries.nearPlaq F R (pairpencil.permConf F t s R.links a) p
            && p.any (fun e => startOf R e == v y || endOf R e == v y))) = true
    rw [hcb, hany]
    exact hp

/-- The separation read transports along a region action. -/
theorem sepBeyond_perm {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false))
    (hpm : plaqPermRead R t (fun _ => false) pm pm') (a b : List L) :
    sepBeyond F R (pairpencil.permConf F t s R.links a)
        (pairpencil.permConf F t s R.links b)
      ↔ sepBeyond F R a b := by
  have key : R.plaqs.all (fun p =>
        !(meetsB R (bandVerts F R (pairpencil.permConf F t s R.links a)) p)
          || !(meetsB R (bandVerts F R (pairpencil.permConf F t s R.links b)) p))
      = R.plaqs.all (fun p =>
        !(meetsB R (bandVerts F R a) p) || !(meetsB R (bandVerts F R b) p)) := by
    refine plaqPerm_all R t (fun _ => false) pm pm' hpm _ _ (fun q hq => ?_)
    have hc := (plaqPermRead_at R t _ pm pm' hpm q hq).2.2.2.2
    have hkeys : ((ground.getAt [] R.plaqs q).all (fun e => e.1 < R.links)) = true :=
      (plaqRead_word R hpr _ (mem_getAt [] R.plaqs q hq)).2
    show (!(meetsB R (bandVerts F R (pairpencil.permConf F t s R.links a))
          (ground.getAt [] R.plaqs (pm q)))
        || !(meetsB R (bandVerts F R (pairpencil.permConf F t s R.links b))
          (ground.getAt [] R.plaqs (pm q))))
      = (!(meetsB R (bandVerts F R a) (ground.getAt [] R.plaqs q))
        || !(meetsB R (bandVerts F R b) (ground.getAt [] R.plaqs q)))
    rw [← meetsB_cyc R _ _ _ hc, ← meetsB_cyc R _ _ _ hc,
      meetsB_move R hw t s v w h _ _ (bandVerts_perm F R hw hpr t s v w pm pm' h hpm a) _ hkeys,
      meetsB_move R hw t s v w h _ _ (bandVerts_perm F R hw hpr t s v w pm pm' h hpm b) _ hkeys]
  show R.plaqs.all _ = true ↔ R.plaqs.all _ = true
  rw [key]

/-- The tower read transports along a region action. -/
theorem towerAt_perm {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false))
    (hpm : plaqPermRead R t (fun _ => false) pm pm') (lamH : Nat) (a : List L) :
    towerAt F R lamH (pairpencil.permConf F t s R.links a) = towerAt F R lamH a := by
  have hcp := components_perm F R hw hpr t s v w pm pm' h hpm a
  cases hb : towerAt F R lamH a with
  | true =>
    obtain ⟨c, hc, hle⟩ := mem_of_any _ _ hb
    obtain ⟨c', hc', hrel⟩ := hcp.2 c hc
    refine any_of_mem _ hc' ?_
    have hs := components_shape F R a c hc
    have hs' := components_shape F R _ c' hc'
    show decide (lamH ≤ compContent F (pairpencil.permConf F t s R.links a) c') = true
    rw [compContent_perm F R t s h.1 a c c' hs.1 hs'.1 hs.2 hs'.2 hrel]
    exact hle
  | false =>
    refine any_false_of_all_not _ _ (all_of_mem_intro _ _ (fun c' hc' => ?_))
    obtain ⟨c, hc, hrel⟩ := hcp.1 c' hc'
    have hs := components_shape F R a c hc
    have hs' := components_shape F R _ c' hc'
    have h2 := all_of_mem _ _ (all_not_of_any_false _ _ hb) c hc
    show (!(decide (lamH ≤ compContent F (pairpencil.permConf F t s R.links a) c'))) = true
    rw [compContent_perm F R t s h.1 a c c' hs.1 hs'.1 hs.2 hs'.2 hrel]
    exact h2

/-- The slab read transports along a region action. -/
theorem slabAt_perm {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false))
    (hpm : plaqPermRead R t (fun _ => false) pm pm') (a : List L) :
    slabAt F R (pairpencil.permConf F t s R.links a) = slabAt F R a := by
  have hiso := linkIso_all R t s h.1
  have hcp := components_perm F R hw hpr t s v w pm pm' h hpm a
  have hsep : ∀ c c' d d', (∀ x, x < R.links → (x ∈ c' ↔ s x ∈ c)) →
      (∀ x, x < R.links → (x ∈ d' ↔ s x ∈ d)) →
      (sepBeyond F R (compConf F R (pairpencil.permConf F t s R.links a) c')
          (compConf F R (pairpencil.permConf F t s R.links a) d')
        ↔ sepBeyond F R (compConf F R a c) (compConf F R a d)) := by
    intro c c' d d' hrc hrd
    rw [compConf_perm F R t s h.1 a c c' hrc, compConf_perm F R t s h.1 a d d' hrd]
    exact sepBeyond_perm F R hw hpr t s v w pm pm' h hpm _ _
  have hpair : ∀ (b b' : List L) (rel : List Nat → List Nat → Prop),
      (∀ c', c' ∈ components F R b' → ∃ c, c ∈ components F R b ∧ rel c c') →
      (∀ c c' d d', c ∈ components F R b → d ∈ components F R b →
        c' ∈ components F R b' → d' ∈ components F R b' → rel c c' → rel d d' →
        (sepBeyond F R (compConf F R b' c') (compConf F R b' d')
          ↔ sepBeyond F R (compConf F R b c) (compConf F R b d))) →
      (∀ c c' d', c' ∈ components F R b' → rel c c' → rel c d' →
        ∀ y, y ∈ c' → y ∈ d') →
      slabAt F R b' = true → slabAt F R b = true := by
    intro b b' rel hmv hsp hsh hb'
    obtain ⟨p, q, hpq, hq, hsq⟩ := (slabAt_iff F R b').1 hb'
    have hp : p < (components F R b').length := Nat.lt_trans hpq hq
    obtain ⟨c, hc, hrc⟩ := hmv _ (mem_getAt [] _ p hp)
    obtain ⟨d, hd, hrd⟩ := hmv _ (mem_getAt [] _ q hq)
    obtain ⟨i, hi, hci⟩ := getAt_of_mem [] hc
    obtain ⟨j, hj, hdj⟩ := getAt_of_mem [] hd
    have hsep' := (hsp c _ d _ hc hd (mem_getAt [] _ p hp) (mem_getAt [] _ q hq) hrc hrd).1 hsq
    have hij : i ≠ j := fun hij => by
      rw [hij] at hci
      rw [hci] at hdj
      rw [hdj] at hrc
      obtain ⟨y, hy⟩ := components_occupied F R b' _ (mem_getAt [] _ p hp)
      exact components_disjoint F R b' p q hpq hq y hy
        (hsh d _ _ (mem_getAt [] _ p hp) hrc hrd y hy)
    refine (slabAt_iff F R b).2 ?_
    cases Nat.lt_or_ge i j with
    | inl hlt =>
      refine ⟨i, j, hlt, hj, ?_⟩
      rw [hci, hdj]
      exact hsep'
    | inr hge =>
      have hgt : j < i := Nat.lt_of_le_of_ne hge (fun he => hij he.symm)
      refine ⟨j, i, hgt, hi, ?_⟩
      rw [hci, hdj]
      exact (sepBeyond_comm F R _ _).1 hsep'
  cases hb : slabAt F R a with
  | true =>
    exact hpair _ a (fun C D => ∀ x, x < R.links → (x ∈ C ↔ s x ∈ D)) hcp.2
      (fun c c' d d' _ _ _ _ hrc hrd => (hsep c' c d' d hrc hrd).symm)
      (fun c c' d' hc' hrc hrd y hy => by
        have hyR : y < R.links := (components_shape F R a c' hc').2 y hy
        have h1 : t y ∈ c := by
          refine (hrc (t y) (hiso y hyR).2.2.1).2 ?_
          rw [(hiso y hyR).1]
          exact hy
        have h2 := (hrd (t y) (hiso y hyR).2.2.1).1 h1
        rw [(hiso y hyR).1] at h2
        exact h2) hb
  | false =>
    cases hb' : slabAt F R (pairpencil.permConf F t s R.links a) with
    | false => rfl
    | true =>
      have h2 := hpair a _ (fun C D => ∀ x, x < R.links → (x ∈ D ↔ s x ∈ C)) hcp.1
        (fun c c' d d' _ _ _ _ hrc hrd => hsep c c' d d' hrc hrd)
        (fun c c' d' hc' hrc hrd y hy =>
          (hrd y ((components_shape F R _ c' hc').2 y hy)).2
            ((hrc y ((components_shape F R _ c' hc').2 y hy)).1 hy)) hb'
      rw [h2] at hb
      exact Bool.noConfusion hb

/-- The head read is one value at a configuration and its image
under a region action: the class's read is its own. -/
theorem headAt_perm {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R) (t s v w pm pm' : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false))
    (hpm : plaqPermRead R t (fun _ => false) pm pm') (lamH : Nat) (a : List L) :
    headAt F R lamH (pairpencil.permConf F t s R.links a) ↔ headAt F R lamH a := by
  show (towerAt F R lamH (pairpencil.permConf F t s R.links a)
      || slabAt F R (pairpencil.permConf F t s R.links a)) = false
    ↔ (towerAt F R lamH a || slabAt F R a) = false
  rw [towerAt_perm F R hw hpr t s v w pm pm' h hpm lamH a,
    slabAt_perm F R hw hpr t s v w pm pm' h hpm a]

/-- An index member reads the head read of its class: the member a
region action's image of the class at the interface equality, the
configurations over a label domain at one spelling per label. -/
theorem classOf_head {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hpr : plaqRead R) (acts : List Act)
    (hacts : regionActs R acts) (P : L → Bool) (hunitP : P F.unit = true)
    (hred : ∀ x y, P x = true → P y = true → F.eqL x y = true → x = y)
    (lamH : Nat) (a c : List L) (haP : a.all P = true) (hcP : c.all P = true)
    (hin : inOrbit F R.links acts a c = true) :
    headAt F R lamH a ↔ headAt F R lamH c := by
  obtain ⟨x, hx, hax⟩ := confMem_mem F a _ hin
  obtain ⟨A, hA, hAc⟩ := mem_map_of _ acts x hx
  have hA' := regionActs_at R acts hacts A hA
  have hxP : x.all P = true := by
    rw [← hAc]
    exact fiberdec.permConf_all F A.t A.s R.links P hunitP c hcP
  rw [carrier.eqConf_eq F P hred a x haP hxP hax, ← hAc]
  exact headAt_perm F R hw hpr A.t A.s A.v A.w A.pm A.pm' hA'.1 hA'.2 lamH c

/-- A head class of the fiber sits in the fiber's head list. -/
theorem fiberIdx_head_of {L : Type} (F : Data L) (R : Region)
    (lamH : Nat) (acts : List Act) (ix : List (List L)) (c : List L)
    (hc : c ∈ classList F R.links acts ix) (hfree : freeB F R.links acts c = true)
    (hh : headAt F R lamH c) : c ∈ (fiberIdx F R lamH acts ix).1 :=
  mem_filter_to _ (mem_filter_to _ hc hfree) (by
    show (!(towerAt F R lamH c || slabAt F R c)) = true
    rw [show (towerAt F R lamH c || slabAt F R c) = false from hh]
    rfl)

/-- A class of the fiber off the head sits in the fiber's tail
list. -/
theorem fiberIdx_tail_of {L : Type} (F : Data L) (R : Region)
    (lamH : Nat) (acts : List Act) (ix : List (List L)) (c : List L)
    (hc : c ∈ classList F R.links acts ix) (hfree : freeB F R.links acts c = true)
    (hh : ¬ headAt F R lamH c) : c ∈ (fiberIdx F R lamH acts ix).2 :=
  mem_filter_to _ (mem_filter_to _ hc hfree) (by
    cases hb : (towerAt F R lamH c || slabAt F R c) with
    | true => rfl
    | false => exact absurd hb hh)

/-- Every member of the fiber's head list reads the head. -/
theorem fiberIdx_head {L : Type} (F : Data L) (R : Region)
    (lamH : Nat) (acts : List Act) (ix : List (List L)) (c : List L)
    (hc : c ∈ (fiberIdx F R lamH acts ix).1) : headAt F R lamH c :=
  gradedIdx_head F R lamH _ c hc

/-! ### The torus instance and the chain instance -/

/-- The plaquettes per site at a direction count, the direction
pairs. -/
def pairCount (d : Nat) : Nat := d * (d - 1) / 2

/-- The plaquette permutation of a composite shift: the plaquette's
site moved, its direction pair kept. -/
def torusPlaqShift (d L : Nat) (ks : List Nat) : Nat → Nat :=
  fun q => fiberdec.compShift d L ks (q / pairCount d) * pairCount d + q % pairCount d

/-- The torus action at a key list, its witnesses at the
complementary key: the composite shift is the link map and the site
map at once, the site keys the links' own range below the site
count. -/
def torusAct (d L : Nat) (ks : List Nat) : Act :=
  { t := fiberdec.compShift d L ks,
    s := fiberdec.compShift d L (fiberdec.invKey L ks),
    v := fiberdec.compShift d L ks,
    w := fiberdec.compShift d L (fiberdec.invKey L ks),
    pm := torusPlaqShift d L ks,
    pm' := torusPlaqShift d L (fiberdec.invKey L ks) }

/-- The torus translation group's action list over the key box. -/
def torusActs (d L : Nat) : List Act :=
  (places.keyBox d L).map (torusAct d L)

/-- The plaquette chain's action at a stated step count. -/
def chainAct (L k : Nat) : Act :=
  { t := fiberdec.iterAt (fiberdec.chainTransl L) k,
    s := fiberdec.iterAt (fiberdec.chainTranslInv L) k,
    v := fiberdec.iterAt (fiberdec.chainVert L) k,
    w := fiberdec.iterAt (fiberdec.chainVertInv L) k,
    pm := fun q => (q + k) % L,
    pm' := fun q => (q + (L - k)) % L }

/-- The plaquette chain's action list at every step count below the
side. -/
def chainActs (L : Nat) : List Act :=
  (List.range L).map (chainAct L)

end grading
