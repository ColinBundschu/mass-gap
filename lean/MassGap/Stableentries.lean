import MassGap.Algebra
import MassGap.Windowfinite
/-!
`lem:stableentries` — matrix elements are reads at the support's
reach: the pairing and the electric reads are index reads on the
joint support alone (the gram the fibers' orthogonal sum at matched
configurations, the content the support's fold — the index layer's
own shape), and the magnetic row reads only the plaquettes meeting
the support's vertex neighborhood, the read `nearPlaq`.  At a far
plaquette the row factorizes: every boundary link reads the unit
law's row `N^c_{1θ} = δ_{cθ}`, so the row is one concatenation, the
`θ`-loop entering on the boundary with the configuration kept
(`farRead`), and its entry against a summand of the joint support
is the Kronecker delta at distinct configurations with
`Eval(χ_θ) = δ_{θ𝟏}`, the sum's unit — the locality band's read,
every pencil row within one band of its support.  The label-graph
isomorphism's transport across windows lands with the decimation's
consumers (`lem:grading`'s rows, `thm:decimation`), the entries'
residue reads with the rank-stability layer.
-/

namespace stableentries
open ground lattice fusion

/-- The vertex neighborhood read: the plaquette shares a vertex
with the configuration's touched set. -/
def nearPlaq {L : Type} (F : Data L) (R : Region) (a : List L)
    (p : List (Nat × Bool)) : Bool :=
  (carrier.touched F R a).any (fun v =>
    p.any (fun e => startOf R e == v || endOf R e == v))

/-- The far row's factorization: at a plaquette off the vertex
neighborhood the row is one concatenation, the `θ`-loop on the
boundary with the configuration kept, the unit law's row at every
boundary link. -/
def farRead {L : Type} (F : Data L) (R : Region) (a : List L)
    (p : List (Nat × Bool)) : Prop :=
  (match algebra.plaqRow F R p a with
   | [] => false
   | [b] => carrier.eqConf F b ((List.range R.links).map (fun l =>
       if p.any (fun e => e.1 == l) then F.theta
       else getAt F.unit a l))
   | _ :: _ :: _ => false) = true

instance {L : Type} (F : Data L) (R : Region) (a : List L)
    (p : List (Nat × Bool)) : Decidable (farRead F R a p) :=
  inferInstanceAs (Decidable (_ = _))

/-! The border factorization at the index level: two configurations
whose supports read no shared vertex join to one configuration, and
the fiber's dimension multiplies over the two parts — the created
loop's corners at the unit law, the vertex multiplicities' product
at every vertex of the region. -/

/-- The reach at one link: the plaquette's boundary meets the
link's two ends. -/
def nearLink (R : Region) (p : List (Nat × Bool)) (l : Nat) : Bool :=
  p.any (fun e =>
    startOf R e == getAt 0 R.tail l
      || startOf R e == getAt 0 R.head l
      || endOf R e == getAt 0 R.tail l
      || endOf R e == getAt 0 R.head l)

/-- The vertex-disjoint read: no vertex reads occupied incident
labels from both configurations. -/
def disjSupp {L : Type} (F : Data L) (R : Region) (a b : List L) :
    Prop :=
  ((List.range R.verts).all (fun v =>
    ((carrier.incidentLabels F R a v).length == 0)
      || ((carrier.incidentLabels F R b v).length == 0))) = true

instance {L : Type} (F : Data L) (R : Region) (a b : List L) :
    Decidable (disjSupp F R a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The join at the region's key range: the first configuration's
label where occupied, the second's otherwise. -/
def joinConf {L : Type} (F : Data L) (R : Region) (a b : List L) :
    List L :=
  (List.range R.links).map (fun l =>
    let x := getAt F.unit a l
    if F.eqL x F.unit then getAt F.unit b l else x)

/-- The keyed image reads through maps agreeing at every occupied
key. -/
private theorem filterMap_congr {α β : Type} [DecidableEq α]
    (f g : α → Option β) : ∀ l : List α,
    (∀ e, 0 < countOf e l → f e = g e) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | e :: t, h => by
    have he : f e = g e :=
      h e (by rw [countOf_head]; exact Nat.succ_pos _)
    have ht : t.filterMap f = t.filterMap g :=
      filterMap_congr f g t (fun x hx => h x (countOf_cons_pos hx))
    show (match f e with
          | none => t.filterMap f
          | some c => c :: t.filterMap f)
       = (match g e with
          | none => t.filterMap g
          | some c => c :: t.filterMap g)
    rw [he, ht]

/-- Every incident entry keys a link of the region. -/
theorem incident_lt (R : Region) (v : Nat) (e : Nat × Bool)
    (h : 0 < countOf e (incident R v)) : e.1 < R.links := by
  rw [lattice.incident_read R v] at h
  have hm : e ∈ (List.range R.links).flatMap (fun l =>
      (if getAt 0 R.tail l == v then [(l, true)] else [])
        ++ (if getAt 0 R.head l == v then [(l, false)] else [])) :=
    ground.mem_of_countOf_pos e _ h
  match ground.mem_flatMap_of _ (List.range R.links) e hm with
  | ⟨l, hl, he⟩ =>
    have hlt : l < R.links :=
      ground.ltOfMemRange hl
    have harm : e = (l, true) ∨ e = (l, false) := by
      cases ground.mem_append_of _ _ he with
      | inl h1 =>
        cases h1t : (getAt 0 R.tail l == v) with
        | true =>
          rw [h1t] at h1
          cases h1 with
          | head => exact Or.inl rfl
          | tail _ hm2 => exact nomatch hm2
        | false =>
          rw [h1t] at h1
          exact nomatch h1
      | inr h2 =>
        cases h2t : (getAt 0 R.head l == v) with
        | true =>
          rw [h2t] at h2
          cases h2 with
          | head => exact Or.inr rfl
          | tail _ hm2 => exact nomatch hm2
        | false =>
          rw [h2t] at h2
          exact nomatch h2
    cases harm with
    | inl h1 =>
      rw [h1]
      exact hlt
    | inr h2 =>
      rw [h2]
      exact hlt
/-- The join's label at a link of the region: the first
configuration's where occupied, the second's otherwise. -/
theorem join_read {L : Type} (F : Data L) (R : Region)
    (a b : List L) (l : Nat) (hl : l < R.links) :
    getAt F.unit (joinConf F R a b) l
      = if F.eqL (getAt F.unit a l) F.unit then getAt F.unit b l
        else getAt F.unit a l := by
  show getAt F.unit ((List.range R.links).map (fun k =>
      let x := getAt F.unit a k
      if F.eqL x F.unit then getAt F.unit b k else x)) l = _
  rw [ground.getAt_map_range F.unit _ R.links l, if_pos hl]

/-- At a vertex where the second configuration reads no incident
label the join's incident labels are the first's. -/
private theorem incid_join_left {L : Type} (F : Data L) (R : Region)
    (a b : List L) (v : Nat)
    (hb : (carrier.incidentLabels F R b v).length = 0) :
    carrier.incidentLabels F R (joinConf F R a b) v
      = carrier.incidentLabels F R a v := by
  show (incident R v).filterMap (fun e =>
      let l := getAt F.unit (joinConf F R a b) e.1
      if F.eqL l F.unit then none
      else if e.2 then some l else some (F.dual l))
    = (incident R v).filterMap (fun e =>
      let l := getAt F.unit a e.1
      if F.eqL l F.unit then none
      else if e.2 then some l else some (F.dual l))
  have hb' : ((incident R v).filterMap (fun d =>
      let l := getAt F.unit b d.1
      if F.eqL l F.unit then none
      else if d.2 then some l else some (F.dual l))).length = 0 := hb
  refine filterMap_congr _ _ (incident R v) (fun e he => ?_)
  have hlt : e.1 < R.links := incident_lt R v e he
  have hnb := filterMap_none _ (incident R v) hb' e he
  have hbu : F.eqL (getAt F.unit b e.1) F.unit = true := by
    cases hq : F.eqL (getAt F.unit b e.1) F.unit with
    | true => rfl
    | false =>
      show (false : Bool) = true
      rw [if_neg (boolNe hq)] at hnb
      cases h2 : e.2 with
      | true =>
        rw [if_pos h2] at hnb
        exact nomatch hnb
      | false =>
        rw [if_neg (boolNe h2)] at hnb
        exact nomatch hnb
  show (if F.eqL (getAt F.unit (joinConf F R a b) e.1) F.unit then none
        else if e.2 then some (getAt F.unit (joinConf F R a b) e.1)
        else some (F.dual (getAt F.unit (joinConf F R a b) e.1)))
     = (if F.eqL (getAt F.unit a e.1) F.unit then none
        else if e.2 then some (getAt F.unit a e.1)
        else some (F.dual (getAt F.unit a e.1)))
  cases hq : F.eqL (getAt F.unit a e.1) F.unit with
  | true =>
    have hj : getAt F.unit (joinConf F R a b) e.1
        = getAt F.unit b e.1 := by
      rw [join_read F R a b e.1 hlt, if_pos hq]
    show (if F.eqL (getAt F.unit (joinConf F R a b) e.1) F.unit
          then none
          else if e.2 then some (getAt F.unit (joinConf F R a b) e.1)
          else some (F.dual (getAt F.unit (joinConf F R a b) e.1)))
       = (none : Option L)
    rw [hj, if_pos hbu]
  | false =>
    have hj : getAt F.unit (joinConf F R a b) e.1
        = getAt F.unit a e.1 := by
      rw [join_read F R a b e.1 hlt, if_neg (boolNe hq)]
    show (if F.eqL (getAt F.unit (joinConf F R a b) e.1) F.unit
          then none
          else if e.2 then some (getAt F.unit (joinConf F R a b) e.1)
          else some (F.dual (getAt F.unit (joinConf F R a b) e.1)))
       = (if e.2 then some (getAt F.unit a e.1)
          else some (F.dual (getAt F.unit a e.1)))
    rw [hj, if_neg (boolNe hq)]

/-- At a vertex where the first configuration reads no incident
label the join's incident labels are the second's. -/
private theorem incid_join_right {L : Type} (F : Data L) (R : Region)
    (a b : List L) (v : Nat)
    (ha : (carrier.incidentLabels F R a v).length = 0) :
    carrier.incidentLabels F R (joinConf F R a b) v
      = carrier.incidentLabels F R b v := by
  show (incident R v).filterMap (fun e =>
      let l := getAt F.unit (joinConf F R a b) e.1
      if F.eqL l F.unit then none
      else if e.2 then some l else some (F.dual l))
    = (incident R v).filterMap (fun e =>
      let l := getAt F.unit b e.1
      if F.eqL l F.unit then none
      else if e.2 then some l else some (F.dual l))
  have ha' : ((incident R v).filterMap (fun d =>
      let l := getAt F.unit a d.1
      if F.eqL l F.unit then none
      else if d.2 then some l else some (F.dual l))).length = 0 := ha
  refine filterMap_congr _ _ (incident R v) (fun e he => ?_)
  have hlt : e.1 < R.links := incident_lt R v e he
  have hna := filterMap_none _ (incident R v) ha' e he
  have hau : F.eqL (getAt F.unit a e.1) F.unit = true := by
    cases hq : F.eqL (getAt F.unit a e.1) F.unit with
    | true => rfl
    | false =>
      show (false : Bool) = true
      rw [if_neg (boolNe hq)] at hna
      cases h2 : e.2 with
      | true =>
        rw [if_pos h2] at hna
        exact nomatch hna
      | false =>
        rw [if_neg (boolNe h2)] at hna
        exact nomatch hna
  have hj : getAt F.unit (joinConf F R a b) e.1
      = getAt F.unit b e.1 := by
    rw [join_read F R a b e.1 hlt, if_pos hau]
  show (if F.eqL (getAt F.unit (joinConf F R a b) e.1) F.unit then none
        else if e.2 then some (getAt F.unit (joinConf F R a b) e.1)
        else some (F.dual (getAt F.unit (joinConf F R a b) e.1)))
     = (if F.eqL (getAt F.unit b e.1) F.unit then none
        else if e.2 then some (getAt F.unit b e.1)
        else some (F.dual (getAt F.unit b e.1)))
  rw [hj]

/-- The vertex multiplicity factorizes across a vertex-disjoint
pair: at every vertex of the region the join reads the parts'
product, the vacant side at the product's unit. -/
theorem vmult_join {L : Type} (F : Data L) (R : Region)
    (a b : List L) (hd : disjSupp F R a b) (v : Nat)
    (hv : v < R.verts) :
    carrier.vmult F R (joinConf F R a b) v
      = carrier.vmult F R a v * carrier.vmult F R b v := by
  have hall := all_range_read R.verts hd v hv
  cases ha : ((carrier.incidentLabels F R a v).length == 0) with
  | true =>
    have ha0 : (carrier.incidentLabels F R a v).length = 0 :=
      ground.beqEqOf ha
    have hone : carrier.vmult F R a v = 1 := by
      show carrier.invCount F (carrier.incidentLabels F R a v) = 1
      rw [ground.nil_of_length_zero _ ha0]
      rfl
    show carrier.invCount F
        (carrier.incidentLabels F R (joinConf F R a b) v)
      = carrier.vmult F R a v * carrier.vmult F R b v
    rw [incid_join_right F R a b v ha0, hone, Nat.one_mul]
    rfl
  | false =>
    have hb : ((carrier.incidentLabels F R b v).length == 0)
        = true := by
      rw [ha] at hall
      exact hall
    have hb0 : (carrier.incidentLabels F R b v).length = 0 :=
      ground.beqEqOf hb
    have hone : carrier.vmult F R b v = 1 := by
      show carrier.invCount F (carrier.incidentLabels F R b v) = 1
      rw [ground.nil_of_length_zero _ hb0]
      rfl
    show carrier.invCount F
        (carrier.incidentLabels F R (joinConf F R a b) v)
      = carrier.vmult F R a v * carrier.vmult F R b v
    rw [incid_join_left F R a b v hb0, hone, Nat.mul_one]
    rfl

/-- The fiber's dimension over the whole vertex range: the
untouched vertices read the product's unit. -/
private theorem fibProd_read {L : Type} (F : Data L) (R : Region)
    (c : List L) : windowfinite.fibProd F R c
      = ground.prodOver (carrier.vmult F R c) (List.range R.verts) := by
  show ground.prodOver (carrier.vmult F R c)
      ((List.range R.verts).filter (fun v =>
        ((carrier.incidentLabels F R c v).length != 0)))
    = ground.prodOver (carrier.vmult F R c) (List.range R.verts)
  exact ground.prodOver_filter _ _ (carrier.vmult_vacant F R c)
    (List.range R.verts)

/-- The fiber's dimension factorizes across a vertex-disjoint pair:
the join's multiplicity product is the parts'. -/
theorem fibProd_join {L : Type} (F : Data L) (R : Region)
    (a b : List L) (hd : disjSupp F R a b) :
    windowfinite.fibProd F R (joinConf F R a b)
      = windowfinite.fibProd F R a * windowfinite.fibProd F R b := by
  rw [fibProd_read F R (joinConf F R a b), fibProd_read F R a,
    fibProd_read F R b]
  have hcongr : ground.prodOver
        (carrier.vmult F R (joinConf F R a b)) (List.range R.verts)
      = ground.prodOver (fun v => carrier.vmult F R a v
          * carrier.vmult F R b v) (List.range R.verts) :=
    ground.famFold_congr_members Nat.mul 1 _ _ (List.range R.verts)
      (fun v hv => vmult_join F R a b hd v (ground.ltOfMem hv))
  rw [hcongr]
  exact ground.famFold_mul_split (carrier.vmult F R a)
    (carrier.vmult F R b) (List.range R.verts)

end stableentries
