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

/-- The far row's one target: the `θ`-loop on the boundary with
the configuration kept. -/
def farConf {L : Type} (F : Data L) (R : Region) (a : List L)
    (p : List (Nat × Bool)) : List L :=
  (List.range R.links).map (fun l =>
    if p.any (fun e => e.1 == l) then F.theta else getAt F.unit a l)

/-- The far row's factorization: at a plaquette off the vertex
neighborhood the row is one concatenation, the `θ`-loop on the
boundary with the configuration kept, the unit law's row at every
boundary link. -/
def farRead {L : Type} (F : Data L) (R : Region) (a : List L)
    (p : List (Nat × Bool)) : Prop :=
  (match algebra.plaqRow F R p a with
   | [] => false
   | [b] => carrier.eqConf F b (farConf F R a p)
   | _ :: _ :: _ => false) = true

instance instStableentries1 {L : Type} (F : Data L) (R : Region) (a : List L)
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

instance instStableentries2 {L : Type} (F : Data L) (R : Region) (a b : List L) :
    Decidable (disjSupp F R a b) :=
  inferInstanceAs (Decidable (_ = _))

/-- The join at the region's key range: the first configuration's
label where occupied, the second's otherwise. -/
def joinConf {L : Type} (F : Data L) (R : Region) (a b : List L) :
    List L :=
  (List.range R.links).map (fun l =>
    let x := getAt F.unit a l
    if F.eqL x F.unit then getAt F.unit b l else x)

/-- Off the vertex neighborhood the configuration reads the unit's
class on the boundary's keys: an occupied boundary key puts its
tail in the touched set at the plaquette's own boundary. -/
theorem far_unit {L : Type} (F : Data L) (R : Region)
    (p : List (Nat × Bool)) (b : List L) (hw : wellRead R)
    (hfar : nearPlaq F R b p = false) (k : Nat) (hk : k < R.links)
    (hkp : (p.any (fun e => e.1 == k)) = true) :
    F.eqL (getAt F.unit b k) F.unit = true := by
  cases hb : F.eqL (getAt F.unit b k) F.unit with
  | true => rfl
  | false =>
    obtain ⟨e, hep, hek⟩ := ground.mem_of_any _ p hkp
    have hek' : e.1 = k := ground.beqEqOf hek
    have htch := (carrier.end_touched F R hw b k hk hb).1
    have hcov : (p.any (fun e' =>
        startOf R e' == getAt 0 R.tail k
          || endOf R e' == getAt 0 R.tail k)) = true := by
      refine ground.any_of_mem _ hep ?_
      cases edge_ends R e with
      | inl h => rw [h.1, hek', ground.eqBeqOf rfl]; exact Bool.true_or _
      | inr h => rw [h.2, hek', ground.eqBeqOf rfl]; exact Bool.or_true _
    have hnear : nearPlaq F R b p = true :=
      ground.any_of_mem _ htch hcov
    exact Bool.noConfusion (hfar.symm.trans hnear)

/-- The far row's targets: at a plaquette off the vertex
neighborhood every target on the plaquette's row is the far target,
the `θ`-loop on the boundary with the configuration kept, since
every boundary link's label is the unit and the unit's row at `θ` is
the one member `θ` at the interface's unit row law (`lem:grading`'s
border row at `def:algebra`'s changed-edge clause); the far target's
own place on the row is the cutoff's read (`carrier.mem_idx`). -/
theorem farRow {L : Type} [DecidableEq L] (F : Data L) (R : Region)
    (hw : wellRead R) (hrow : unitRowLaw F F.theta)
    (a : List L) (hlen : a.length = R.links) (hun : oneUnit F a)
    (p : List (Nat × Bool)) (hfar : nearPlaq F R a p = false)
    (b : List L) (hb : 0 < countOf b (algebra.plaqRow F R p a)) :
    b = farConf F R a p := by
  have hrow' : F.row F.unit F.theta = [F.theta] := hrow
  have hb' : 0 < countOf b (ground.prodLists ((List.range R.links).map (algebra.linkTargets F p a))) := by
    have h : 0 < countOf b ((ground.prodLists ((List.range R.links).map (algebra.linkTargets F p a))).filter
      (fun t => (t.any (fun m => !(F.eqL m F.unit))) && carrier.occupied F R t)) := hb
    rw [countOf_filter] at h
    cases hf : ((b.any (fun m => !(F.eqL m F.unit))) && carrier.occupied F R b) with
    | false => rw [if_neg (fun h' => Bool.noConfusion (hf.symm.trans h'))] at h; exact absurd h (Nat.lt_irrefl 0)
    | true => rw [if_pos hf] at h; exact h
  obtain ⟨hblen, hall⟩ := mem_prodLists_of F.unit _ b (mem_of_countOf_pos b _ hb')
  have hDs : ((List.range R.links).map (algebra.linkTargets F p a)).length = R.links := by
    rw [length_map, length_range]
  have hflen : (farConf F R a p).length = R.links := by
    show ((List.range R.links).map _).length = R.links
    rw [length_map, length_range]
  refine getAt_ext F.unit b (farConf F R a p) (hblen.trans (hDs.trans hflen.symm)) (fun i hi => ?_)
  have hi' : i < R.links := by rw [← hDs, ← hblen]; exact hi
  have hmem := hall i (by rw [hDs]; exact hi')
  rw [getAt_map 0 [] _ (List.range R.links) i (by rw [length_range]; exact hi'), getAt_range R.links i hi'] at hmem
  have hfar' : getAt F.unit (farConf F R a p) i
      = if p.any (fun e => e.1 == i) then F.theta else getAt F.unit a i := by
    show getAt F.unit ((List.range R.links).map (fun l =>
      if p.any (fun e => e.1 == l) then F.theta else getAt F.unit a l)) i = _
    rw [getAt_map 0 F.unit _ (List.range R.links) i (by rw [length_range]; exact hi'),
      getAt_range R.links i hi']
  rw [hfar']
  cases hkp : (p.any (fun e => e.1 == i)) with
  | true =>
    have hunit : getAt F.unit a i = F.unit :=
      oneUnit_read F a hun _ (countOf_pos_of_mem (mem_getAt F.unit a i (by rw [hlen]; exact hi')))
        (far_unit F R p a hw hfar i hi' hkp)
    have hsing : algebra.linkTargets F p a i = [F.theta] := by
      show (if p.any (fun e => e.1 == i) then F.row (getAt F.unit a i) F.theta
        else [getAt F.unit a i]) = [F.theta]
      rw [hkp, if_pos rfl, hunit, hrow']
    rw [hsing] at hmem
    rw [if_pos rfl]
    exact ground.eq_of_mem_single hmem
  | false =>
    have hsing : algebra.linkTargets F p a i = [getAt F.unit a i] := by
      show (if p.any (fun e => e.1 == i) then F.row (getAt F.unit a i) F.theta
        else [getAt F.unit a i]) = [getAt F.unit a i]
      rw [hkp, if_neg (fun h' => Bool.noConfusion h')]
    rw [hsing] at hmem
    rw [if_neg (fun h' => Bool.noConfusion h')]
    exact ground.eq_of_mem_single hmem

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
  refine filterMap_congr_members _ _ (incident R v) (fun e he => ?_)
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
  refine filterMap_congr_members _ _ (incident R v) (fun e he => ?_)
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


/-! The reach at a link read at the entries' keys: one value across
a plaquette's cyclic readings, and moved along a region action. -/

/-- A plaquette's reach at a link, read at the entries' keys
alone. -/
private def keyNear (R : Region) (k l : Nat) : Bool :=
  (getAt 0 R.tail k == getAt 0 R.tail l)
    || (getAt 0 R.tail k == getAt 0 R.head l)
    || (getAt 0 R.head k == getAt 0 R.tail l)
    || (getAt 0 R.head k == getAt 0 R.head l)

private theorem nearLink_keys (R : Region) (p : List (Nat × Bool)) (l : Nat) :
    nearLink R p l = p.any (fun e => keyNear R e.1 l) := by
  refine any_congr_all _ _ (fun e => ?_) p
  cases e with
  | mk k b =>
    cases b with
    | true => rfl
    | false =>
      show ((getAt 0 R.head k == getAt 0 R.tail l)
          || (getAt 0 R.head k == getAt 0 R.head l)
          || (getAt 0 R.tail k == getAt 0 R.tail l)
          || (getAt 0 R.tail k == getAt 0 R.head l))
        = ((getAt 0 R.tail k == getAt 0 R.tail l)
          || (getAt 0 R.tail k == getAt 0 R.head l)
          || (getAt 0 R.head k == getAt 0 R.tail l)
          || (getAt 0 R.head k == getAt 0 R.head l))
      cases (getAt 0 R.head k == getAt 0 R.tail l) <;>
        cases (getAt 0 R.head k == getAt 0 R.head l) <;>
        cases (getAt 0 R.tail k == getAt 0 R.tail l) <;>
        cases (getAt 0 R.tail k == getAt 0 R.head l) <;> rfl

/-- The reach at a link is one value across a plaquette's cyclic
readings. -/
theorem nearLink_cyc (R : Region) (w w' : List (Nat × Bool))
    (hc : cycEq w w' = true) (l : Nat) : nearLink R w l = nearLink R w' l := by
  rw [nearLink_keys, nearLink_keys]
  exact cycEq_any_keys (fun k => keyNear R k l) w w' hc

private theorem keyNear_move (R : Region) (hw : wellRead R) (t s v w : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false)) (k l : Nat)
    (hk : k < R.links) (hl : l < R.links) :
    keyNear R (t k) (t l) = keyNear R k l := by
  show ((getAt 0 R.tail (t k) == getAt 0 R.tail (t l))
    || (getAt 0 R.tail (t k) == getAt 0 R.head (t l))
    || (getAt 0 R.head (t k) == getAt 0 R.tail (t l))
    || (getAt 0 R.head (t k) == getAt 0 R.head (t l))) = _
  rw [(endsMoved_vac R t v h.2.2 k hk).1, (endsMoved_vac R t v h.2.2 k hk).2,
    (endsMoved_vac R t v h.2.2 l hl).1, (endsMoved_vac R t v h.2.2 l hl).2,
    vertIso_beq R v w h.2.1 _ _ (endLt R hw k hk).1 (endLt R hw l hl).1,
    vertIso_beq R v w h.2.1 _ _ (endLt R hw k hk).1 (endLt R hw l hl).2,
    vertIso_beq R v w h.2.1 _ _ (endLt R hw k hk).2 (endLt R hw l hl).1,
    vertIso_beq R v w h.2.1 _ _ (endLt R hw k hk).2 (endLt R hw l hl).2]
  rfl

/-- The reach at a link transports along a region action: the moved
plaquette's reach at the moved link is the plaquette's at the
link. -/
theorem nearLink_move (R : Region) (hw : wellRead R) (t s v w : Nat → Nat)
    (h : isoRead R R t s v w (fun _ => false)) (p : List (Nat × Bool))
    (hp : (p.all (fun e => e.1 < R.links)) = true) (l : Nat) (hl : l < R.links) :
    nearLink R (moveWord t (fun _ => false) p) (t l) = nearLink R p l := by
  rw [nearLink_keys, nearLink_keys]
  show (p.map (fun e => (t e.1, xor e.2 ((fun _ => false) e.1)))).any
      (fun e => keyNear R e.1 (t l)) = _
  rw [any_map]
  refine any_congr_of_mem _ _ p (fun e he => ?_)
  exact keyNear_move R hw t s v w h e.1 l (of_decide_eq_true (all_of_mem _ p hp e he)) hl

end stableentries
