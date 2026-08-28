import MassGap.Sertables
import MassGap.Split
/-!
`thm:assembly`'s read layer.  The subset fold sits at the content
keys: the product over the positive list expands over the list's
occupancy families, the family `S` taking the second side at its
members and the first at the rest, its side `S`'s count and its
key the join's datum at `e_S + Σ_{α ∈ S} α = ρ`, so the graded
fold `Φ` is the families' count at a key, one side each.  The
Weyl fold enters bound, as the stated graded image list of `ρ`
with the reads that pin it — the closure at the letters, each
member's reflection image sitting at the flipped side; the
support at stated witnesses, `w ρ + Σ_{β ∈ N} β = ρ` at `N` the
element's inversion list (`con:sertables`' grading fold); and the
regular read, `ρ` once at the even side and off the odd
(`con:sertables`' regular reads, `w ρ = ρ` forcing the identity).
The identity's own read is the per-key balance `Φ = a_ρ`
(`thm:assembly` coefficientwise), the two folds' graded counts one
value of the two balance pairs.  The Weyl fold's transport sits
beside them: a reflection carries the graded count at a key to the
count at the reflected key on the flipped side, the closure read's
own consequence through the conditioned involution of the graded
members.  The subset fold's transport is the occupancy families'
own involution — the simple's occupancy toggled and the further
members carried along the permutation — sending a family's key to
the reflected key at the moved side.  The walk closes the identity
at `balanceRead`: a key of the rank's order at its representative
rises at a lower-side simple pair, the raised key's root-fold dot
the key's own joined to the pair's margin at the letter's positive
dot, and the raises close at the gap's count against an occupied
key's dot — its family's or its witness fold's positive dots joined
to `ρ`'s own.  At a dominant image the pins read both folds: a
simple coroot pair the unit fixes the key, each fold reading its own
flipped side, and a key beyond the unit at every pair is `ρ`, where
the subset fold reads the vacant family alone at the even side
against the regular read's own.

`thm:memberchar`'s cross-term tier consumes the identity whole.
The at-k Euler collection (`subsetCountOff_euler`) and its moved
form (`subsetCountOff_euler_moved`) collect the withdrawn folds'
count pairs against the roots' dots, at the key's dot joined to or
against `ρ`'s own; the line telescope (`subsetCountOff_line`)
divides the subset pairs along a root's line at the `(Cof)` gaps
(`subsetCount_off_split`), the end vanishing beyond `ρ`'s height at
the hit keys' own bound (`hitLe`); and the concatenation bridge
(`wFold_subsets`) reads any signed fold over the alternant data as
its fold over the subset families, the two lists' join balanced key
by key at the identity itself.
-/

namespace assembly
open ground sertables

/-- The subset's key: `ρ` less the members' fold, normed
(`thm:assembly`'s subset fold, `e_S + Σ_S α = ρ`). -/
def eKey (t : gentable.Table) (S : List Nat) : List BPair :=
  poly.pnorm (elim.vecAdd (rhoV t)
    (poly.neg (elim.vsum t.rank (posCorootV t) S)))

/-- The subset fold's graded count at a key: the families at the
stated side whose key is the given one (`thm:assembly`'s graded
fold `Φ`). -/
def subsetCount (t : gentable.Table) (y : List BPair)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun S => if places.sideOf S = side then
        (if eKey t S = y then 1 else 0) else 0)
    (ground.sublistsOf (List.range t.posFolds.length))

/-- The withdrawn-index subset fold's graded count at a key: the
families off the given index at the stated side whose key is the
given one (`thm:memberchar`'s cofactor at a positive member). -/
def subsetCountOff (t : gentable.Table) (j : Nat) (y : List BPair)
    (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun S => if places.sideOf S = side then
        (if eKey t S = y then 1 else 0) else 0)
    (ground.sublistsOf (ground.eraseFirst j (List.range t.posFolds.length)))

/-- The Weyl fold's graded count at a key, the stated image list's
own (`thm:assembly`'s `a_ρ`, `con:sertables`' Weyl list at its
grading). -/
def wCount (W : List (List BPair × Bool)) (y : List BPair)
    (side : Bool) : Nat :=
  countOf (y, side) W

/-- The closure read: each member's reflection image sits in the
list at the flipped side at the member's own count
(`con:sertables`: one further letter moves the grading by one). -/
def wCloseRead (t : gentable.Table)
    (W : List (List BPair × Bool)) : Prop :=
  ∀ vp ∈ W, ∀ i, i < t.rank →
    countOf (reflAt t i vp.1, !vp.2) W = countOf vp W

instance (t : gentable.Table) (W : List (List BPair × Bool)) :
    Decidable (wCloseRead t W) :=
  inferInstanceAs (Decidable (∀ vp ∈ W, ∀ i, i < t.rank → _ = _))

/-- A natural fold of the simple roots at stated multiplicities:
the Cartan rows scaled by the counts and joined, the seed the
rank's replicate of the sum's unit. -/
def cartanFold (t : gentable.Table) (w : List Nat) : List BPair :=
  (List.range t.rank).foldl
    (fun acc i => elim.vecAdd acc ((ground.getAt [] t.cartan i).map
      (BPair.mul (BPair.ofNat (ground.getAt 0 w i)))))
    (List.replicate t.rank BPair.unit)

/-- The support read at a stated key: every member's key joins its
witness fold, the simples at natural multiplicities, back to the
stated key — the shifted alternant's second read (`thm:memberchar`:
every key sits at `μ + ρ` against a natural fold of simple
roots). -/
def wDomAt (t : gentable.Table) (W : List (List BPair × Bool))
    (wits : List (List Nat)) (v : List BPair) : Prop :=
  wits.length = W.length ∧ ∀ k, k < W.length →
    poly.pnorm (elim.vecAdd (ground.getAt ([], false) W k).1
      (cartanFold t (ground.getAt [] wits k))) = v

instance (t : gentable.Table) (W : List (List BPair × Bool))
    (wits : List (List Nat)) (v : List BPair) :
    Decidable (wDomAt t W wits v) :=
  inferInstanceAs (Decidable (wits.length = W.length ∧
    ∀ k, k < W.length → poly.pnorm (elim.vecAdd
      (ground.getAt ([], false) W k).1
      (cartanFold t (ground.getAt [] wits k))) = v))

/-- The support read at stated witnesses: each member's key joins
its witness fold, the simples at natural multiplicities, back to
`ρ` — the collected form of `con:sertables`' grading fold
`w ρ + Σ_{β ∈ N} β = ρ`, the inversion list's members regrouped
at their simple folds. -/
def wDomRead (t : gentable.Table) (W : List (List BPair × Bool))
    (wits : List (List Nat)) : Prop :=
  wDomAt t W wits (rhoV t)

instance (t : gentable.Table) (W : List (List BPair × Bool))
    (wits : List (List Nat)) : Decidable (wDomRead t W wits) :=
  inferInstanceAs (Decidable (wDomAt t W wits (rhoV t)))

/-- The regular read: `ρ` sits in the list once even and off it
odd (`con:sertables`' regular reads, `w ρ = ρ` forcing the
identity). -/
def wTopRead (t : gentable.Table)
    (W : List (List BPair × Bool)) : Prop :=
  countOf (poly.pnorm (rhoV t), false) W = 1
    ∧ countOf (poly.pnorm (rhoV t), true) W = 0

instance (t : gentable.Table) (W : List (List BPair × Bool)) :
    Decidable (wTopRead t W) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The top read at a stated key: the key sits in the list once at
the even side and off it at the odd — the shifted alternant's third
read (`thm:memberchar`: the read at `μ + ρ` is one at the even
grading alone). -/
def wTopAt (W : List (List BPair × Bool)) (v : List BPair) : Prop :=
  ground.countOf (v, false) W = 1 ∧ ground.countOf (v, true) W = 0

instance (W : List (List BPair × Bool)) (v : List BPair) :
    Decidable (wTopAt W v) :=
  inferInstanceAs (Decidable (ground.countOf (v, false) W = 1 ∧
    ground.countOf (v, true) W = 0))

/-- The fourth read of the shifted alternant (`thm:memberchar`):
every member at a key beyond the unit on each coordinate, off the
top key, reads its two graded counts at one value. -/
def wRegRead (t : gentable.Table) (W : List (List BPair × Bool))
    (top : List BPair) : Prop :=
  ∀ vp ∈ W, (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit vp.1 k) →
    vp.1 ≠ top →
    ground.countOf (vp.1, true) W = ground.countOf (vp.1, false) W

instance (t : gentable.Table) (W : List (List BPair × Bool))
    (top : List BPair) : Decidable (wRegRead t W top) :=
  inferInstanceAs (Decidable (∀ vp ∈ W,
    (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit vp.1 k) →
    vp.1 ≠ top →
    ground.countOf (vp.1, true) W = ground.countOf (vp.1, false) W))

/-- The per-key balance: the subset fold's graded count against
the Weyl fold's, one value of the two balance pairs
(`thm:assembly` coefficientwise, `Φ = a_ρ` key by key). -/
def balanceAt (t : gentable.Table) (W : List (List BPair × Bool))
    (y : List BPair) : Prop :=
  subsetCount t y false + wCount W y true
    = subsetCount t y true + wCount W y false

instance (t : gentable.Table) (W : List (List BPair × Bool))
    (y : List BPair) : Decidable (balanceAt t W y) :=
  inferInstanceAs (Decidable (_ = _))

/-! The Weyl fold's transport: a reflection carries the graded count
at a key to the count at the reflected key on the other side, the
closure read's own consequence at the list's own members.  The
carrier of the transport is the reflection's conditioned move on the
graded members — the key reflected and the side flipped where the
key sits at the rank normed, the member kept where it does not — an
involution outright, with the closure read its count identity at the
list's members and `ground.countOf_invol` the read at every key. -/

/-- The reflection's matrix reads the rank's order in its rows'
count (`con:sertables`' letter at the rank's keys). -/
theorem reflM_length (t : gentable.Table) (i : Nat) :
    (reflM t i).length = t.rank :=
  ground.length_mapRange _ t.rank

/-- Every row of the reflection's matrix reads the rank's order. -/
theorem reflM_rows (t : gentable.Table) (i : Nat) :
    elim.rowsLen t.rank (reflM t i) :=
  elim.rowsLen_map _ t.rank (List.range t.rank)
    (fun x _ => (fun _ => ground.length_mapRange _ t.rank) x)

/-- A reflection's image reads the rank's order. -/
theorem reflAt_length (t : gentable.Table) (i : Nat)
    (v : List BPair) : (reflAt t i v).length = t.rank := by
  show (poly.pnorm (elim.matVec (reflM t i) v)).length = t.rank
  rw [poly.pnorm_length, elim.matVec_length, reflM_length]

/-- A reflection's image sits at its own representative. -/
theorem reflAt_norm (t : gentable.Table) (i : Nat)
    (v : List BPair) : poly.pnorm (reflAt t i v) = reflAt t i v :=
  poly.pnorm_pnorm _

/-- The reflection's image of its own image is the key back, at a
key of the rank's order sitting at its representative: the squared
matrix reads the identity, the actions compose at the product, and
the representative lists agree at one value (`con:sertables`:
`s_i s_i μ = μ`). -/
private theorem reflAt_invol (t : gentable.Table) (i : Nat)
    (hsq : elim.matOneValue (elim.matMul (reflM t i) (reflM t i))
      (inertia.idMat t.rank))
    (v : List BPair) (hv : v.length = t.rank) (hnv : poly.pnorm v = v) :
    reflAt t i (reflAt t i v) = v := by
  have hrows := reflM_rows t i
  have hrows' : elim.rowsLen (reflM t i).length (reflM t i) := by
    rw [reflM_length]; exact hrows
  have hall := poly.oneValue_trans
    (elim.matVec_congr (reflM t i) (poly.pnorm (elim.matVec (reflM t i) v))
      (elim.matVec (reflM t i) v) (poly.pnorm_oneValue _))
    (poly.oneValue_trans
      (elim.matVec_comp (reflM t i) (reflM t i) v t.rank hrows hv hrows')
      (poly.oneValue_trans
        (elim.matVec_matOne _ _ v hsq)
        (inertia.matVec_idMat t.rank v hv)))
  show poly.pnorm (elim.matVec (reflM t i)
    (poly.pnorm (elim.matVec (reflM t i) v))) = v
  refine Eq.trans (poly.pnorm_congr _ _ ?_ hall) hnv
  rw [elim.matVec_length, reflM_length, hv]

/-- The graded member's conditioned move: the key reflected and the
side flipped where the key sits at the rank's order at its own
representative, the member kept where it does not. -/
def flipAt (t : gentable.Table) (i : Nat)
    (vp : List BPair × Bool) : List BPair × Bool :=
  if vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1 then (reflAt t i vp.1, !vp.2)
  else vp

/-- The conditioned move is an involution outright: a moved member's
image carries the condition itself, so the second move reads the
reflection's square with the side flipped back, and a kept member is
kept again. -/
theorem flipAt_invol (t : gentable.Table) (i : Nat)
    (hsq : elim.matOneValue (elim.matMul (reflM t i) (reflM t i))
      (inertia.idMat t.rank)) (vp : List BPair × Bool) :
    flipAt t i (flipAt t i vp) = vp := by
  by_cases hg : vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1
  · have e1 : flipAt t i vp = (reflAt t i vp.1, !vp.2) := by
      show (if vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1 then
        (reflAt t i vp.1, !vp.2) else vp) = _
      exact if_pos hg
    have e2 : flipAt t i (reflAt t i vp.1, !vp.2)
        = (reflAt t i (reflAt t i vp.1), !(!vp.2)) := by
      show (if (reflAt t i vp.1).length = t.rank
          ∧ poly.pnorm (reflAt t i vp.1) = reflAt t i vp.1 then _ else _) = _
      exact if_pos ⟨reflAt_length t i vp.1, reflAt_norm t i vp.1⟩
    rw [e1, e2, reflAt_invol t i hsq vp.1 hg.1 hg.2, Bool.not_not]
  · have e1 : flipAt t i vp = vp := by
      show (if vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1 then
        (reflAt t i vp.1, !vp.2) else vp) = _
      exact if_neg hg
    rw [e1, e1]

/-- The Weyl fold's transport at a reflection: the graded count at a
reflected key on one side is the count at the key itself on the
other, at every key of the rank's order sitting at its
representative — the conditioned move is the count-preserving
involution, its count identity the closure read at the list's
members with the member's own shape test the move's condition, and
the transported key is the move's own value at the given key. -/
theorem wCount_refl (t : gentable.Table) (W : List (List BPair × Bool))
    (hclose : wCloseRead t W)
    (hsq : reflSquareRead t) (i : Nat) (hi : i < t.rank)
    (y : List BPair) (hy : y.length = t.rank) (hny : poly.pnorm y = y)
    (s : Bool) : wCount W (reflAt t i y) s = wCount W y (!s) := by
  have hmem : ∀ a ∈ W, countOf (flipAt t i a) W = countOf a W := by
    intro a ha
    by_cases hg : a.1.length = t.rank ∧ poly.pnorm a.1 = a.1
    · have e : flipAt t i a = (reflAt t i a.1, !a.2) := by
        show (if a.1.length = t.rank ∧ poly.pnorm a.1 = a.1 then
          (reflAt t i a.1, !a.2) else a) = _
        exact if_pos hg
      rw [e]
      exact hclose a ha i hi
    · have e : flipAt t i a = a := by
        show (if a.1.length = t.rank ∧ poly.pnorm a.1 = a.1 then
          (reflAt t i a.1, !a.2) else a) = _
        exact if_neg hg
      rw [e]
  have key := ground.countOf_invol (flipAt t i) W
    (fun a _ => flipAt_invol t i (hsq i hi) a) hmem (y, !s)
  have e2 : flipAt t i (y, !s) = (reflAt t i y, s) := by
    show (if y.length = t.rank ∧ poly.pnorm y = y then
      (reflAt t i y, !(!s)) else (y, !s)) = _
    rw [if_pos (show y.length = t.rank ∧ poly.pnorm y = y from ⟨hy, hny⟩),
      Bool.not_not]
  rw [e2] at key
  exact key

/-! The subset fold's transport kit: the value-level vector and
fold reads the reindex consumes (`thm:assembly`'s grading tier,
`s_i e_S = e_{T_i S}` at the involution on the occupancy
families). -/

private theorem vecAdd_length {u v : List BPair}
    (h : u.length = v.length) :
    (elim.vecAdd u v).length = u.length :=
  elim.length_vecAdd u v u.length rfl h.symm

/-- The memberwise swap of a sum splits (`poly.neg_sum` at the
matched-key sum). -/
theorem neg_vecAdd : ∀ u v : List BPair,
    poly.neg (elim.vecAdd u v) = elim.vecAdd (poly.neg u) (poly.neg v)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: u, _ :: v => by
    show _ :: poly.neg (elim.vecAdd u v)
      = _ :: elim.vecAdd (poly.neg u) (poly.neg v)
    rw [neg_vecAdd u v]
    rfl

/-- The subset fold's vector at the head-structural spelling: the
famFold recursion's cons read is definitional, a `show` step the
walk's structural inductions consume directly, where
`elim.vsum_cons` prices one one-value transport per step —
`foldl_vsum` the stated bridge between the two spellings, and the
List.filter splits (`fvFilterL`) the head-structural kit's own
reads. -/
private def vsum (t : gentable.Table) (S : List Nat) : List BPair :=
  ground.famFold elim.vecAdd (List.replicate t.rank BPair.unit)
    (posCorootV t) S

private theorem vsum_length (t : gentable.Table) : ∀ S : List Nat,
    (vsum t S).length = t.rank
  | [] => ground.length_replicate BPair.unit t.rank
  | j :: S => by
    show (elim.vecAdd (posCorootV t j) (vsum t S)).length = t.rank
    rw [vecAdd_length ((posCorootV_length t j).trans
      (vsum_length t S).symm)]
    exact posCorootV_length t j

private theorem foldl_length (t : gentable.Table) : ∀ (S : List Nat)
    (acc : List BPair), acc.length = t.rank →
    (S.foldl (fun a j => elim.vecAdd a (posCorootV t j)) acc).length
      = t.rank
  | [], _, h => h
  | j :: S, acc, h => by
    show (S.foldl (fun a j => elim.vecAdd a (posCorootV t j))
      (elim.vecAdd acc (posCorootV t j))).length = t.rank
    refine foldl_length t S _ ?_
    rw [vecAdd_length (h.trans (posCorootV_length t j).symm)]
    exact h

/-- The accumulating fold's join read at the vector sum: the seed
pulls out of the fold at one value. -/
private theorem foldl_vsum (t : gentable.Table) : ∀ (S : List Nat)
    (acc : List BPair), acc.length = t.rank →
    poly.oneValue
      (S.foldl (fun a j => elim.vecAdd a (posCorootV t j)) acc)
      (elim.vecAdd acc (vsum t S))
  | [], acc, h =>
    poly.oneValue_symm (elim.vecAdd_null_right acc (List.replicate t.rank BPair.unit)
      (by rw [ground.length_replicate]; exact h)
      (poly.unitTail_replicate t.rank))
  | j :: S, acc, h => by
    show poly.oneValue
      (S.foldl (fun a j => elim.vecAdd a (posCorootV t j))
        (elim.vecAdd acc (posCorootV t j)))
      (elim.vecAdd acc (vsum t (j :: S)))
    have hl : (elim.vecAdd acc (posCorootV t j)).length = t.rank := by
      rw [vecAdd_length (h.trans (posCorootV_length t j).symm)]
      exact h
    have step := foldl_vsum t S (elim.vecAdd acc (posCorootV t j)) hl
    have e : elim.vecAdd (elim.vecAdd acc (posCorootV t j)) (vsum t S)
        = elim.vecAdd acc (vsum t (j :: S)) := by
      rw [elim.vecAdd_assoc]
      rfl
    rw [e] at step
    exact step

/-- The action reads the unit vector at the unit vector. -/
private theorem matVec_unitV : ∀ (M : elim.Mat) (n k : Nat),
    M.length = k →
    poly.oneValue (elim.matVec M (List.replicate n BPair.unit))
      (List.replicate k BPair.unit)
  | [], _, 0, _ => trivial
  | [], _, _ + 1, h => Nat.noConfusion h
  | _ :: _, _, 0, h => Nat.noConfusion h
  | r :: M, n, k + 1, h => by
    show poly.oneValue
      (elim.dotN r (List.replicate n BPair.unit)
        :: elim.matVec M (List.replicate n BPair.unit))
      (BPair.unit :: List.replicate k BPair.unit)
    exact ⟨BPair.oneValue_trans (elim.dotN_read _ _)
        (elim.dotP_repl_unit r n),
      matVec_unitV M n k (Nat.succ.inj h)⟩

/-! The reflection's `ρ` identity (`con:gentable`'s reflection
join at the coroot presentation, `s_i ρ + α_i = ρ`): the matrix's
row sums against the simple's coroot row, entrywise at the one-hot
folds. -/


private theorem bsum_famFold : ∀ l : List BPair,
    (BPair.sum l).oneValue
      (ground.famFold BPair.add BPair.unit (fun x => x) l)
  | [] => BPair.oneValue_refl _
  | x :: l => BPair.oneValue_trans (BPair.sum_cons x l)
      (BPair.add_congr (BPair.oneValue_refl x) (bsum_famFold l))

private theorem famFold_bsplit (f g : Nat → BPair) : ∀ l : List Nat,
    (ground.famFold BPair.add BPair.unit (fun k => f k + g k) l).oneValue
      (ground.famFold BPair.add BPair.unit f l
        + ground.famFold BPair.add BPair.unit g l)
  | [] => BPair.oneValue_symm (BPair.unit_add _)
  | a :: l => by
    show ((f a + g a)
      + ground.famFold BPair.add BPair.unit (fun k => f k + g k) l).oneValue
      ((f a + ground.famFold BPair.add BPair.unit f l)
        + (g a + ground.famFold BPair.add BPair.unit g l))
    rw [BPair.add_add_comm (f a)
      (ground.famFold BPair.add BPair.unit f l) (g a)
      (ground.famFold BPair.add BPair.unit g l)]
    exact BPair.add_congr (BPair.oneValue_refl _) (famFold_bsplit f g l)

private theorem zipRepl_map {α : Type} (c : BPair) (h : α → BPair) :
    ∀ (l : List α) (n : Nat), l.length = n →
    elim.vecAdd (List.replicate n c) (l.map h)
      = l.map (fun x => c + h x)
  | [], 0, _ => rfl
  | [], _ + 1, hl => Nat.noConfusion hl
  | _ :: _, 0, hl => Nat.noConfusion hl
  | a :: l, n + 1, hl => by
    show (c + h a) :: elim.vecAdd (List.replicate n c) (l.map h)
      = (c + h a) :: l.map (fun x => c + h x)
    rw [zipRepl_map c h l n (Nat.succ.inj hl)]

/-- The reflection's `ρ` identity: the image of `ρ` is `ρ` less the
reflecting simple's coroot vector, entrywise at the row sums
(`con:gentable`'s reflection join, `s_i ρ + α_i = ρ`). -/
private theorem rho_reflM (t : gentable.Table) (F : FundData)
    (i : Nat) (hi : i < t.rank) (hsp : simplePosRead t F) :
    poly.oneValue (elim.matVec (reflM t i) (rhoV t))
      (elim.vecAdd (rhoV t)
        (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i)))) := by
  have eL : elim.matVec (reflM t i) (rhoV t)
      = (List.range t.rank).map (fun j =>
          elim.dotN ((List.range t.rank).map (fun k =>
            BPair.add (if j == k then BPair.ofNat 1 else BPair.unit)
              (if k == i then
                (getAt BPair.unit (getAt [] t.cartan i) j).swap
              else BPair.unit))) (rhoV t)) := by
    show ((List.range t.rank).map _).map _ = _
    rw [ground.map_map]
  have eR : elim.vecAdd (rhoV t)
      (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i)))
      = (List.range t.rank).map (fun j =>
          BPair.ofNat 1
            + (gentable.corootAt t
                (getAt [] t.posFolds (ground.getAt 0 F.simplePos i))
                j).swap) := by
    show elim.vecAdd (List.replicate t.rank (BPair.ofNat 1))
      (((List.range t.rank).map _).map BPair.swap) = _
    rw [ground.map_map, zipRepl_map (BPair.ofNat 1) _ (List.range t.rank)
      t.rank (ground.length_range t.rank)]
  rw [eL, eR]
  refine poly.oneValue_map _ _ (List.range t.rank) (fun j hj => ?_)
  have hjr : j < t.rank :=
    ground.ltOfMemRange hj
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  have eρ : (rhoV t) = List.replicate
      ((List.range t.rank).length) (BPair.ofNat 1) := by
    show List.replicate t.rank (BPair.ofNat 1) = _
    rw [ground.length_range]
  rw [eρ, ← ground.map_const (BPair.ofNat 1) (List.range t.rank),
    elim.dotP_map_pair]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _ _ (List.range t.rank)
      (fun k _ => BPair.mul_ofNat_one _)) ?_
  refine BPair.oneValue_trans
    (famFold_bsplit (fun k => if j == k then BPair.ofNat 1
        else BPair.unit)
      (fun k => if k == i then
        (getAt BPair.unit (getAt [] t.cartan i) j).swap
      else BPair.unit) (List.range t.rank)) ?_
  refine BPair.oneValue_symm ?_
  refine BPair.add_congr ?_ ?_
  · refine BPair.oneValue_symm ?_
    rw [ground.famFold_congr_all BPair.add BPair.unit
      (fun k => if j == k then BPair.ofNat 1 else BPair.unit)
      (fun k => if k == j then BPair.ofNat 1 else BPair.unit)
      (fun k => by rw [ground.beqSymm j k]) (List.range t.rank)]
    exact ground.foldB_pickBeq j (BPair.ofNat 1) (List.range t.rank)
      (ground.countOf_range_one hjr)
  · exact BPair.oneValue_trans
      (ground.swap_congr (by
        rw [hsp i hi]
        exact gentable.corootAt_oneHot t i j hi))
      (BPair.oneValue_symm
        (ground.foldB_pickBeq i _ (List.range t.rank)
          (ground.countOf_range_one hi)))

/-! The occupancy families' enumeration kit: the sublists'
membership, distinctness, and the filter characterization
(`thm:assembly`'s grading tier, the involution's carrier). -/

/-- The withdrawn seed's enumeration is the full enumeration at the
membership guard: a fold over the erased seed's families reads the
guarded fold over the seed's own. -/
private theorem sublists_eraseGuard : ∀ (l : List Nat),
    (∀ x, ground.countOf x l ≤ 1) →
    ∀ (j : Nat), 0 < ground.countOf j l →
    ∀ (f : List Nat → Nat),
    ground.famFold Nat.add 0 f (ground.sublistsOf (ground.eraseFirst j l))
      = ground.famFold Nat.add 0
          (fun S => if ground.containsB S j then 0 else f S) (ground.sublistsOf l)
  | [], _, _, hj, _ => absurd hj (Nat.lt_irrefl 0)
  | a :: t, hd, j, hj, f => by
    exact if hja : j = a then by
      have he : ground.eraseFirst j (a :: t) = t := by
        show (if j = a then t else a :: ground.eraseFirst j t) = t
        rw [if_pos hja]
      rw [he]
      show ground.famFold Nat.add 0 f (ground.sublistsOf t)
        = ground.famFold Nat.add 0
            (fun S => if ground.containsB S j then 0 else f S)
            (ground.sublistsOf t ++ (ground.sublistsOf t).map (fun S => a :: S))
      rw [ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add,
        ground.famFold_map Nat.add 0]
      have hja_t : ground.countOf j t = 0 := by
        have h1 := hd j
        rw [show ground.countOf j (a :: t)
            = 1 + ground.countOf j t from by
          rw [ground.countOf_cons, if_pos hja]] at h1
        cases hc : ground.countOf j t with
        | zero => rfl
        | succ m =>
          rw [hc, Nat.add_comm] at h1
          exact absurd (Nat.le_of_succ_le_succ h1)
            (Nat.not_succ_le_zero m)
      have hguard : ∀ S : List Nat,
          0 < ground.countOf S (ground.sublistsOf t) →
          (if ground.containsB (a :: S) j then 0 else f (a :: S))
            = (fun _ : List Nat => (0 : Nat)) S := by
        intro S _
        show (if ground.containsB (a :: S) j then 0 else f (a :: S)) = 0
        rw [hja, ground.containsB_head a S, if_pos rfl]
      have hopen : ∀ S : List Nat,
          0 < ground.countOf S (ground.sublistsOf t) →
          (if ground.containsB S j then 0 else f S) = f S := by
        intro S hS
        have hoff : ground.countOf j S = 0 := by
          cases hc : ground.countOf j S with
          | zero => rfl
          | succ m =>
            have hin := ground.sublists_entries t S hS j
              (by rw [hc]; exact Nat.succ_pos m)
            rw [hja_t] at hin
            exact absurd hin (Nat.lt_irrefl 0)
        have hcb : ground.containsB S j = false := by
          show decide (0 < ground.countOf j S) = false
          rw [hoff]
          rfl
        rw [hcb]
        show (if false = true then 0 else f S) = f S
        rw [if_neg (ground.boolNe rfl)]
      rw [ground.famFold_congr_members Nat.add 0
          (fun S => if ground.containsB (a :: S) j then 0 else f (a :: S))
          (fun _ => (0 : Nat)) (ground.sublistsOf t) hguard,
        ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (ground.sublistsOf t),
        ground.famFold_congr_members Nat.add 0
          (fun S => if ground.containsB S j then 0 else f S)
          f (ground.sublistsOf t) hopen]
      rfl
    else by
      have he : ground.eraseFirst j (a :: t)
          = a :: ground.eraseFirst j t := by
        show (if j = a then t else a :: ground.eraseFirst j t) = _
        rw [if_neg hja]
      rw [he]
      have hdt : ∀ x, ground.countOf x t ≤ 1 := by
        intro x
        have hle : ground.countOf x t
            ≤ ground.countOf x (a :: t) := by
          rw [ground.countOf_cons]
          exact Nat.le_add_left _ _
        exact Nat.le_trans hle (hd x)
      have hjt : 0 < ground.countOf j t := by
        have hpos := hj
        rw [show ground.countOf j (a :: t) = ground.countOf j t from by
          rw [ground.countOf_cons, if_neg hja, Nat.zero_add]] at hpos
        exact hpos
      show ground.famFold Nat.add 0 f
          (ground.sublistsOf (ground.eraseFirst j t)
            ++ (ground.sublistsOf (ground.eraseFirst j t)).map
                (fun S => a :: S))
        = ground.famFold Nat.add 0
            (fun S => if ground.containsB S j then 0 else f S)
            (ground.sublistsOf t ++ (ground.sublistsOf t).map (fun S => a :: S))
      rw [ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add,
        ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add,
        ground.famFold_map Nat.add 0, ground.famFold_map Nat.add 0,
        sublists_eraseGuard t hdt j hjt f,
        sublists_eraseGuard t hdt j hjt (fun S => f (a :: S))]
      refine congrArg (Nat.add _) ?_
      refine ground.famFold_congr_members Nat.add 0 _ _
        (ground.sublistsOf t) ?_
      intro S _
      show (if ground.containsB S j then 0 else f (a :: S))
        = (if ground.containsB (a :: S) j then 0 else f (a :: S))
      rw [ground.containsB_cons_ne hja S]

/-! The permutation's fixed point (`con:sertables`: `s_i` permutes
the positive list off `α_i`): a member mapped onto the simple's
position would read the simple's balance partner, and the ρ-dots'
positivity refuses the pair. -/

/-- The reflection reads a key's representative and the key alike:
the image is the same at both. -/
theorem reflAt_pnorm (t : gentable.Table) (i : Nat)
    (v : List BPair) : reflAt t i (poly.pnorm v) = reflAt t i v := by
  show poly.pnorm (elim.matVec (reflM t i) (poly.pnorm v))
    = poly.pnorm (elim.matVec (reflM t i) v)
  refine poly.pnorm_congr _ _ ?_
    (elim.matVec_congr (reflM t i) (poly.pnorm v) v
      (poly.pnorm_oneValue v))
  rw [elim.matVec_length, elim.matVec_length]

/-- The double image reads the representative, at every key of the
rank's order. -/
theorem reflAt_invol' (t : gentable.Table) (i : Nat)
    (hsq : elim.matOneValue (elim.matMul (reflM t i) (reflM t i))
      (inertia.idMat t.rank))
    (v : List BPair) (hv : v.length = t.rank) :
    reflAt t i (reflAt t i v) = poly.pnorm v := by
  have hrows := reflM_rows t i
  have hrows' : elim.rowsLen (reflM t i).length (reflM t i) := by
    rw [reflM_length]; exact hrows
  have hall := poly.oneValue_trans
    (elim.matVec_congr (reflM t i) (poly.pnorm (elim.matVec (reflM t i) v))
      (elim.matVec (reflM t i) v) (poly.pnorm_oneValue _))
    (poly.oneValue_trans
      (elim.matVec_comp (reflM t i) (reflM t i) v t.rank hrows hv hrows')
      (poly.oneValue_trans
        (elim.matVec_matOne _ _ v hsq)
        (inertia.matVec_idMat t.rank v hv)))
  show poly.pnorm (elim.matVec (reflM t i)
    (poly.pnorm (elim.matVec (reflM t i) v))) = poly.pnorm v
  refine poly.pnorm_congr _ _ ?_ hall
  rw [elim.matVec_length, reflM_length, hv]

/-- The simple's position sits in the positive list's range. -/
theorem simplePos_lt (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) {i : Nat} (hi : i < t.rank) :
    ground.getAt 0 F.simplePos i < t.posFolds.length := by
  have h := ground.all_getAt 0 F.simplePos hshape.2.2.2.2.2.1 i
    (by rw [hshape.2.2.2.1]; exact hi)
  exact of_decide_eq_true h

/-- The permutation datum's entries sit in the range. -/
private theorem perm_lt (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) {i : Nat} (hi : i < t.rank)
    {j : Nat} (hj : j < t.posFolds.length) :
    ground.getAt 0 (ground.getAt [] F.perms i) j
      < t.posFolds.length := by
  have h := ground.all_getAt ([] : List Nat) F.perms
    hshape.2.2.2.2.2.2 i (by rw [hshape.2.2.2.2.1]; exact hi)
  have hs := ground.andSplitB h
  have hlen : (ground.getAt [] F.perms i).length
      = t.posFolds.length := ground.beqEqOf hs.1
  have h2 := ground.all_getAt 0 (ground.getAt [] F.perms i) hs.2 j
    (by rw [hlen]; exact hj)
  exact of_decide_eq_true h2

/-- The fixed point: the permutation datum keeps the simple's own
position. -/
private theorem perm_fix (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank)
    (hshape : fundShape t F) (hsq : reflSquareRead t)
    (hpsq : permSquareRead t F) (hpi : permImageRead t F)
    (hrd : rhoDotRead t F) :
    ground.getAt 0 (ground.getAt [] F.perms i)
        (ground.getAt 0 F.simplePos i)
      = ground.getAt 0 F.simplePos i := by
  have hsin := simplePos_lt t F hshape hi
  by_cases hfix : ground.getAt 0 (ground.getAt [] F.perms i)
      (ground.getAt 0 F.simplePos i) = ground.getAt 0 F.simplePos i
  · exact hfix
  · exfalso
    have hq := perm_lt t F hshape hi hsin
    have hqfix : ground.getAt 0 (ground.getAt [] F.perms i)
        (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i))
        = ground.getAt 0 F.simplePos i := hpsq i hi _ hsin
    have h1 := (hpi i hi).1 _ hq hfix
    rw [hqfix] at h1
    have h2 : reflAt t i (reflAt t i (posCorootV t
        (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i))))
        = poly.pnorm (poly.neg (posCorootV t
            (ground.getAt 0 F.simplePos i))) := by
      rw [h1, reflAt_pnorm]
      exact (hpi i hi).2
    rw [reflAt_invol' t i (hsq i hi) _ (posCorootV_length t _)] at h2
    have hone : poly.oneValue
        (posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i)))
        (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))) := by
      refine poly.oneValue_trans
        (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
      rw [h2]
      exact poly.pnorm_oneValue _
    have hlq := hrd _ hq
    have hlsi := hrd _ hsin
    have hcong : (elim.dotP
        (posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i)))
        (elim.matVec F.gram (rhoV t))).oneValue
        (elim.dotP (poly.neg (posCorootV t
          (ground.getAt 0 F.simplePos i)))
          (elim.matVec F.gram (rhoV t))) := by
      rw [elim.dotP_comm (posCorootV t _) (elim.matVec F.gram (rhoV t)),
        elim.dotP_comm (poly.neg (posCorootV t _))
          (elim.matVec F.gram (rhoV t))]
      exact elim.dotP_oneValue_right _ _ _ hone
    have hlt2 : BPair.unit < (elim.dotP
        (posCorootV t (ground.getAt 0 F.simplePos i))
        (elim.matVec F.gram (rhoV t))).swap := by
      refine BPair.lt_congr (BPair.oneValue_refl BPair.unit) ?_ hlq
      rw [← elim.dotP_swap_left]
      exact hcong
    have h1' : Pos.one + (elim.dotP
        (posCorootV t (ground.getAt 0 F.simplePos i))
        (elim.matVec F.gram (rhoV t))).snd
        < (elim.dotP (posCorootV t (ground.getAt 0 F.simplePos i))
          (elim.matVec F.gram (rhoV t))).fst + Pos.one := hlsi
    have h2' : Pos.one + (elim.dotP
        (posCorootV t (ground.getAt 0 F.simplePos i))
        (elim.matVec F.gram (rhoV t))).fst
        < (elim.dotP (posCorootV t (ground.getAt 0 F.simplePos i))
          (elim.matVec F.gram (rhoV t))).snd + Pos.one := hlt2
    rw [ground.add_comm] at h1' h2'
    exact ground.lt_asymm (ground.lt_trans h1' h2')
      (ground.lt_trans h1' h2')

/-! The subset involution `T_i` (`thm:assembly`'s grading tier):
the simple's occupancy toggled and the further members carried
along the permutation, spelled as the range's filter. -/

/-- The involution on the occupancy families: the simple's
position toggled, the rest read along the permutation. -/
private def flipT (t : gentable.Table) (F : FundData) (i : Nat)
    (S : List Nat) : List Nat :=
  List.filter (fun j =>
    if j == ground.getAt 0 F.simplePos i then
      !(ground.containsB S (ground.getAt 0 F.simplePos i))
    else ground.containsB S (ground.getAt 0 (ground.getAt [] F.perms i) j))
    (List.range t.posFolds.length)

private theorem perm_ne_si (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank)
    (hshape : fundShape t F) (hsq : reflSquareRead t)
    (hpsq : permSquareRead t F) (hpi : permImageRead t F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (hne : j ≠ ground.getAt 0 F.simplePos i) :
    ground.getAt 0 (ground.getAt [] F.perms i) j
      ≠ ground.getAt 0 F.simplePos i := by
  intro he
  refine hne ?_
  have h2 : ground.getAt 0 (ground.getAt [] F.perms i)
      (ground.getAt 0 (ground.getAt [] F.perms i) j) = j :=
    hpsq i hi j hj
  rw [he, perm_fix t F hi hshape hsq hpsq hpi hrd] at h2
  exact h2.symm

private theorem containsB_filter (P : Nat → Bool) (n y : Nat) :
    ground.containsB (List.filter P (List.range n)) y
      = (P y && decide (y < n)) := by
  show decide (0 < ground.countOf y (List.filter P (List.range n))) = _
  rw [ground.countOf_filter P y (List.range n), ground.countOf_range y n]
  cases hp : P y with
  | true =>
    rw [if_pos rfl]
    by_cases hyn : y < n
    · rw [if_pos hyn, decide_eq_true hyn]
      rfl
    · rw [if_neg hyn]
      cases hd : decide (y < n) with
      | true => exact absurd (of_decide_eq_true hd) hyn
      | false => rfl
  | false =>
    rw [if_neg (ground.boolNe rfl)]
    rfl

/-- The involution reads back: the double flip is the family
itself. -/
private theorem flipT_invol (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank)
    (hshape : fundShape t F) (hsq : reflSquareRead t)
    (hpsq : permSquareRead t F) (hpi : permImageRead t F)
    (hrd : rhoDotRead t F) (S : List Nat)
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length))) :
    flipT t F i (flipT t F i S) = S := by
  have hchar := ground.sublists_char (List.range t.posFolds.length)
    (ground.distinctList_all (ground.distinctList_range t.posFolds.length)) S hS
  have hsin := simplePos_lt t F hshape hi
  refine Eq.trans (ground.filter_congr_mem _ _
    (List.range t.posFolds.length) (fun x hx => ?_)) hchar.symm
  have hxn : x < t.posFolds.length := ground.ltOfMem hx
  by_cases hxsi : x = ground.getAt 0 F.simplePos i
  · rw [if_pos (ground.eqBeqOf hxsi), hxsi]
    show (!(ground.containsB (flipT t F i S)
        (ground.getAt 0 F.simplePos i)))
      = ground.containsB S (ground.getAt 0 F.simplePos i)
    show (!(ground.containsB (List.filter _ (List.range t.posFolds.length))
      (ground.getAt 0 F.simplePos i))) = _
    rw [containsB_filter _ t.posFolds.length _,
      if_pos (ground.eqBeqOf rfl), decide_eq_true hsin]
    cases hc : ground.containsB S (ground.getAt 0 F.simplePos i) with
    | true => rfl
    | false => rfl
  · rw [if_neg (fun ht : (x == ground.getAt 0 F.simplePos i) = true
      => hxsi (ground.beqEqOf ht))]
    have hpx := perm_lt t F hshape hi hxn
    have hpne := perm_ne_si t F hi hshape hsq hpsq hpi hrd hxn hxsi
    show ground.containsB (List.filter _ (List.range t.posFolds.length))
      (ground.getAt 0 (ground.getAt [] F.perms i) x) = _
    rw [containsB_filter _ t.posFolds.length _,
      if_neg (fun ht : (ground.getAt 0 (ground.getAt [] F.perms i) x
          == ground.getAt 0 F.simplePos i) = true
        => hpne (ground.beqEqOf ht)),
      decide_eq_true hpx, hpsq i hi x hxn]
    cases hc : ground.containsB S x with
    | true => rfl
    | false => rfl

private theorem lengthFilterL (P : Nat → Bool) : ∀ l : List Nat,
    (List.filter P l).length
      = ground.famFold Nat.add 0 (fun x => if P x then 1 else 0) l
  | [] => rfl
  | a :: l => by
    cases hpa : P a with
    | true =>
      rw [ground.filter_cons_true hpa]
      show (List.filter P l).length + 1 = _
      rw [lengthFilterL P l]
      show _ = (if P a then 1 else 0)
        + ground.famFold Nat.add 0 (fun x => if P x then 1 else 0) l
      rw [hpa, if_pos rfl, Nat.add_comm]
    | false =>
      rw [ground.filter_cons_false hpa, lengthFilterL P l]
      show _ = (if P a then 1 else 0)
        + ground.famFold Nat.add 0 (fun x => if P x then 1 else 0) l
      rw [hpa, if_neg (ground.boolNe rfl), Nat.zero_add]

private theorem countOf_eraseFirst_le {a x : Nat} : ∀ l : List Nat,
    ground.countOf x (ground.eraseFirst a l) ≤ ground.countOf x l
  | [] => Nat.le.refl
  | b :: l => by
    show ground.countOf x (if a = b then l
      else b :: ground.eraseFirst a l) ≤ _
    by_cases hab : a = b
    · rw [if_pos hab]
      exact ground.countOf_cons_le x b l
    · rw [if_neg hab]
      by_cases hxb : x = b
      · rw [hxb, ground.countOf_head, ground.countOf_head]
        exact Nat.succ_le_succ (countOf_eraseFirst_le l)
      · rw [ground.countOf_head_ne hxb, ground.countOf_head_ne hxb]
        exact countOf_eraseFirst_le l

private theorem eraseFirst_range_distinct (n si : Nat) :
    ground.distinctList (ground.eraseFirst si (List.range n)) :=
  fun x _ => Nat.le_trans (countOf_eraseFirst_le (List.range n))
    (ground.distinctList_all (ground.distinctList_range n) x)

/-- Off the erased key, the erased range's members read the range's
own counts, once each. -/
private theorem eraseFirst_range_count {n si x : Nat}
    (hx : 0 < ground.countOf x
      (ground.eraseFirst si (List.range n))) :
    x < n ∧ x ≠ si := by
  by_cases hxsi : x = si
  · have hself : ground.countOf si (List.range n)
        = ground.countOf si (ground.eraseFirst si (List.range n))
          + 1 ∨ ground.countOf si
            (ground.eraseFirst si (List.range n)) = 0 := by
      by_cases hp : 0 < ground.countOf si (List.range n)
      · exact Or.inl (ground.countOf_eraseFirst_self _ si hp)
      · refine Or.inr ?_
        cases hc : ground.countOf si
            (ground.eraseFirst si (List.range n)) with
        | zero => rfl
        | succ m =>
          have := Nat.le_trans
            (show 0 + 1 ≤ ground.countOf si
                (ground.eraseFirst si (List.range n))
              from by rw [hc]; exact Nat.succ_le_succ (Nat.zero_le m))
            (countOf_eraseFirst_le (List.range n))
          rw [Nat.zero_add] at this
          exact absurd (Nat.lt_of_succ_le this) hp
    cases hself with
    | inl he =>
      have h1 := ground.distinctList_all (ground.distinctList_range n) si
      rw [he] at h1
      have h0 : ground.countOf si
          (ground.eraseFirst si (List.range n)) = 0 := by
        cases hc : ground.countOf si
            (ground.eraseFirst si (List.range n)) with
        | zero => rfl
        | succ m =>
          rw [hc] at h1
          exact absurd (Nat.lt_of_succ_lt_succ
            (Nat.lt_of_succ_le h1)) (Nat.not_lt_zero m)
      rw [hxsi, h0] at hx
      exact absurd hx (Nat.lt_irrefl 0)
    | inr he =>
      rw [hxsi, he] at hx
      exact absurd hx (Nat.lt_irrefl 0)
  · rw [ground.countOf_eraseFirst_ne (List.range n) si x hxsi] at hx
    exact ⟨ground.ltOfMem hx, hxsi⟩

/-- The flip toggles the family's parity. -/
private theorem parity_flip (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank)
    (hshape : fundShape t F) (hsq : reflSquareRead t)
    (hpsq : permSquareRead t F) (hpi : permImageRead t F)
    (hrd : rhoDotRead t F) (S : List Nat)
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length))) :
    places.sideOf (flipT t F i S) = !(places.sideOf S) := by
  have hsin := simplePos_lt t F hshape hi
  have hchar := ground.sublists_char (List.range t.posFolds.length)
    (ground.distinctList_all (ground.distinctList_range t.posFolds.length)) S hS
  have hcnt : 0 < ground.countOf (ground.getAt 0 F.simplePos i)
      (List.range t.posFolds.length) := by
    rw [ground.countOf_range_one hsin]
    exact Nat.succ_pos 0
  have hsplitF := ground.famFold_eraseFirst Nat.add 0 Nat.add_comm
    Nat.add_assoc
    (fun x => if (if x == ground.getAt 0 F.simplePos i then
        !(ground.containsB S (ground.getAt 0 F.simplePos i))
      else ground.containsB S (ground.getAt 0 (ground.getAt [] F.perms i) x))
      then 1 else 0)
    (List.range t.posFolds.length) _ hcnt
  have hsplitS := ground.famFold_eraseFirst Nat.add 0 Nat.add_comm
    Nat.add_assoc
    (fun x => if ground.containsB S x then 1 else 0)
    (List.range t.posFolds.length) _ hcnt
  have hcommon : ground.famFold Nat.add 0
      (fun x => if (if x == ground.getAt 0 F.simplePos i then
          !(ground.containsB S (ground.getAt 0 F.simplePos i))
        else ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) x))
        then 1 else 0)
      (ground.eraseFirst (ground.getAt 0 F.simplePos i)
        (List.range t.posFolds.length))
      = ground.famFold Nat.add 0
        (fun x => if ground.containsB S x then 1 else 0)
        (ground.eraseFirst (ground.getAt 0 F.simplePos i)
          (List.range t.posFolds.length)) := by
    refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
      (fun x => if ground.containsB S
        (ground.getAt 0 (ground.getAt [] F.perms i) x) then 1 else 0)
      _ (fun x hx => ?_)) ?_
    · obtain ⟨hxn, hxsi⟩ := eraseFirst_range_count hx
      rw [if_neg (fun ht : (x == ground.getAt 0 F.simplePos i) = true
        => hxsi (ground.beqEqOf ht))]
    · refine (ground.famFold_reindex Nat.add 0 Nat.add_comm
        Nat.add_assoc (fun x => if ground.containsB S x then 1 else 0)
        (eraseFirst_range_distinct t.posFolds.length _)
        (g := fun x => ground.getAt 0 (ground.getAt [] F.perms i) x)
        (h := fun x => ground.getAt 0 (ground.getAt [] F.perms i) x)
        (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
        (fun x hx => ?_)).symm
      · obtain ⟨hxn, _⟩ := eraseFirst_range_count hx
        exact hpsq i hi x hxn
      · obtain ⟨hxn, _⟩ := eraseFirst_range_count hx
        exact hpsq i hi x hxn
      · obtain ⟨hxn, hxsi⟩ := eraseFirst_range_count hx
        rw [ground.countOf_eraseFirst_ne _ _ _
          (perm_ne_si t F hi hshape hsq hpsq hpi hrd hxn hxsi),
          ground.countOf_range_one (perm_lt t F hshape hi hxn)]
        exact Nat.succ_pos 0
      · obtain ⟨hxn, hxsi⟩ := eraseFirst_range_count hx
        rw [ground.countOf_eraseFirst_ne _ _ _
          (perm_ne_si t F hi hshape hsq hpsq hpi hrd hxn hxsi),
          ground.countOf_range_one (perm_lt t F hshape hi hxn)]
        exact Nat.succ_pos 0
  have hlenF : (flipT t F i S).length
      = (if !(ground.containsB S (ground.getAt 0 F.simplePos i))
          then 1 else 0)
        + ground.famFold Nat.add 0
          (fun x => if ground.containsB S x then 1 else 0)
          (ground.eraseFirst (ground.getAt 0 F.simplePos i)
            (List.range t.posFolds.length)) := by
    show (List.filter _ (List.range t.posFolds.length)).length = _
    rw [lengthFilterL, hsplitF, hcommon,
      if_pos (ground.eqBeqOf rfl)]
    rfl
  have hlenS : S.length
      = (if ground.containsB S (ground.getAt 0 F.simplePos i)
          then 1 else 0)
        + ground.famFold Nat.add 0
          (fun x => if ground.containsB S x then 1 else 0)
          (ground.eraseFirst (ground.getAt 0 F.simplePos i)
            (List.range t.posFolds.length)) := by
    have hlen0 : S.length
        = (List.filter (ground.containsB S)
            (List.range t.posFolds.length)).length :=
      congrArg List.length hchar
    rw [hlen0, lengthFilterL, hsplitS]
    rfl
  show places.parityOf (flipT t F i S).length
    = !(places.parityOf S.length)
  rw [hlenF, hlenS]
  cases hc : ground.containsB S (ground.getAt 0 F.simplePos i) with
  | true =>
    rw [if_neg (ground.boolNe (show (!true) = false from rfl)),
      if_pos rfl, Nat.zero_add, Nat.add_comm]
    show places.parityOf _ = !(!(places.parityOf _))
    rw [Bool.not_not]
  | false =>
    rw [if_pos (show (!false) = true from rfl),
      if_neg (ground.boolNe rfl), Nat.zero_add, Nat.add_comm]
    rfl

/-! The key transport (`thm:assembly`'s grading tier,
`s_i e_S = e_{T_i S}`): the subset key's reflection image is the
flipped family's key, at the range's guarded folds. -/

private theorem fvLen (t : gentable.Table) (f : Nat → List BPair)
    (hf : ∀ j, (f j).length = t.rank) : ∀ l : List Nat,
    (ground.famFold elim.vecAdd
      (List.replicate t.rank BPair.unit) f l).length = t.rank
  | [] => ground.length_replicate BPair.unit t.rank
  | a :: l => by
    show (elim.vecAdd (f a) (ground.famFold elim.vecAdd
      (List.replicate t.rank BPair.unit) f l)).length = t.rank
    rw [vecAdd_length ((hf a).trans (fvLen t f hf l).symm)]
    exact hf a

private theorem fvCongrMem (t : gentable.Table)
    (f g : Nat → List BPair) (hf : ∀ j, (f j).length = t.rank)
    (hg : ∀ j, (g j).length = t.rank) : ∀ l : List Nat,
    (∀ j, 0 < ground.countOf j l →
      poly.oneValue (f j) (g j)) →
    poly.oneValue
      (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit) f l)
      (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit) g l)
  | [], _ => poly.oneValue_refl _
  | a :: l, h =>
    elim.vecAdd_congr2 _ _ _ _ ((hf a).trans (hg a).symm)
      ((fvLen t f hf l).trans (fvLen t g hg l).symm)
      (h a (by rw [ground.countOf_head]; exact Nat.succ_pos _))
      (fvCongrMem t f g hf hg l
        (fun j hj => h j (ground.countOf_cons_pos hj)))

private theorem fvFilterL (t : gentable.Table) (f : Nat → List BPair)
    (hf : ∀ j, (f j).length = t.rank) (P : Nat → Bool) :
    ∀ l : List Nat,
    poly.oneValue
      (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit) f (List.filter P l))
      (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit)
        (fun j => if P j then f j
          else List.replicate t.rank BPair.unit) l)
  | [] => poly.oneValue_refl _
  | a :: l => by
    have hg : ∀ j, ((fun j => if P j then f j
        else List.replicate t.rank BPair.unit) j).length = t.rank :=
      fun j => by
        show (if P j then f j
          else List.replicate t.rank BPair.unit).length = t.rank
        by_cases hp : P j = true
        · rw [if_pos hp]
          exact hf j
        · rw [if_neg hp]
          exact ground.length_replicate BPair.unit t.rank
    cases hpa : P a with
    | true =>
      rw [ground.filter_cons_true hpa]
      show poly.oneValue (elim.vecAdd (f a) _)
        (elim.vecAdd (if P a then f a
          else List.replicate t.rank BPair.unit) _)
      rw [hpa, if_pos rfl]
      exact elim.vecAdd_congr2 _ _ _ _ rfl
        ((fvLen t f hf (List.filter P l)).trans
          (fvLen t _ hg l).symm)
        (poly.oneValue_refl _) (fvFilterL t f hf P l)
    | false =>
      rw [ground.filter_cons_false hpa]
      show poly.oneValue _
        (elim.vecAdd (if P a then f a
          else List.replicate t.rank BPair.unit) _)
      rw [hpa, if_neg (ground.boolNe rfl)]
      refine poly.oneValue_trans (fvFilterL t f hf P l) ?_
      refine poly.oneValue_symm ?_
      rw [elim.vecAdd_comm]
      exact elim.vecAdd_null_right _ (List.replicate t.rank BPair.unit)
        (by rw [ground.length_replicate]; exact fvLen t _ hg l)
        (poly.unitTail_replicate t.rank)

private theorem mvFold (t : gentable.Table) (i : Nat)
    (f : Nat → List BPair) (hf : ∀ j, (f j).length = t.rank) :
    ∀ l : List Nat,
    poly.oneValue
      (elim.matVec (reflM t i) (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit) f l))
      (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit)
        (fun j => elim.matVec (reflM t i) (f j)) l)
  | [] => matVec_unitV (reflM t i) t.rank t.rank (reflM_length t i)
  | a :: l => by
    show poly.oneValue
      (elim.matVec (reflM t i) (elim.vecAdd (f a) _)) _
    refine poly.oneValue_trans
      (elim.matVec_vecAdd (reflM t i) t.rank (reflM_rows t i)
        (f a) _ (hf a) (fvLen t f hf l)) ?_
    have hlam : ∀ j, ((fun j => elim.matVec (reflM t i) (f j))
        j).length = t.rank :=
      fun j => (elim.matVec_length _ _).trans (reflM_length t i)
    have h2 : (elim.matVec (reflM t i)
        (ground.famFold elim.vecAdd
          (List.replicate t.rank BPair.unit) f l)).length
        = (ground.famFold elim.vecAdd
            (List.replicate t.rank BPair.unit)
            (fun j => elim.matVec (reflM t i) (f j)) l).length :=
      ((elim.matVec_length _ _).trans (reflM_length t i)).trans
        (fvLen t _ hlam l).symm
    exact elim.vecAdd_congr2 _ _ _ _ rfl h2 (poly.oneValue_refl _)
      (mvFold t i f hf l)

/-- A key joins its own swap at the unit family. -/
theorem vecAdd_swap_self : ∀ v : List BPair,
    poly.oneValue (elim.vecAdd (poly.neg v) v)
      (List.replicate v.length BPair.unit)
  | [] => trivial
  | a :: v => by
    show poly.oneValue ((a.swap + a) :: elim.vecAdd (poly.neg v) v)
      (BPair.unit :: List.replicate v.length BPair.unit)
    exact ⟨BPair.swap_add_null (BPair.oneValue_refl a), vecAdd_swap_self v⟩

/-- The move as a sum: a family member joins the moved key back to
the stated key exactly where the move lands at it. -/
theorem addKey_iff (n : Nat) (y k v : List BPair)
    (hy : y.length = n) (hyn : poly.pnorm y = y)
    (hk : k.length = n) (hv : v.length = n) (hvn : poly.pnorm v = v) :
    poly.pnorm (elim.vecAdd k v) = y ↔
      poly.pnorm (elim.vecAdd y (poly.neg k)) = v := by
  have hnk : (poly.neg k).length = n :=
    (ground.length_map BPair.swap k).trans hk
  have hZ : poly.unitTail (elim.vecAdd (poly.neg k) k) :=
    poly.oneValue_unitTail (vecAdd_swap_self k)
      (poly.unitTail_replicate _)
  have hZl : (elim.vecAdd (poly.neg k) k).length = n :=
    elim.length_vecAdd _ _ n hnk hk
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [← h, elim.pnorm_vecAdd_left _ _
      ((elim.length_vecAdd k v n hk hv).trans hnk.symm),
      elim.vecAdd_assoc k v (poly.neg k), elim.vecAdd_comm v (poly.neg k),
      ← elim.vecAdd_assoc k (poly.neg k) v,
      elim.vecAdd_comm k (poly.neg k)]
    refine (poly.pnorm_congr _ _ ?_
      (elim.vecAdd_null_left _ _ (hZl.trans hv.symm) hZ)).trans hvn
    rw [elim.length_vecAdd _ _ n hZl hv, hv]
  · rw [← h, elim.vecAdd_comm k _, elim.pnorm_vecAdd_left _ _
      ((elim.length_vecAdd y _ n hy hnk).trans hk.symm),
      elim.vecAdd_assoc y (poly.neg k) k]
    refine (poly.pnorm_congr _ _ ?_
      (elim.vecAdd_null_right _ _ (hy.trans hZl.symm) hZ)).trans hyn
    rw [elim.length_vecAdd _ _ n hy hZl, hy]

/-- The join's solve at the commuted order: a stated join reads its
member back at the key's withdrawal. -/
theorem addKey_solve (n : Nat) (y k v : List BPair)
    (hy : y.length = n) (hyn : poly.pnorm y = y)
    (hk : k.length = n) (hv : v.length = n) (hvn : poly.pnorm v = v)
    (he : poly.pnorm (elim.vecAdd v k) = y) :
    poly.pnorm (elim.vecAdd y (poly.neg k)) = v := by
  refine (addKey_iff n y k v hy hyn hk hv hvn).mp ?_
  rw [elim.vecAdd_comm k v]
  exact he

/-- The solve's converse at the commuted order: the withdrawal's
read joins the member back to the stated key. -/
theorem addKey_join (n : Nat) (y k v : List BPair)
    (hy : y.length = n) (hyn : poly.pnorm y = y)
    (hk : k.length = n) (hv : v.length = n) (hvn : poly.pnorm v = v)
    (he : poly.pnorm (elim.vecAdd y (poly.neg k)) = v) :
    poly.pnorm (elim.vecAdd v k) = y := by
  rw [elim.vecAdd_comm v k]
  exact (addKey_iff n y k v hy hyn hk hv hvn).mpr he


/-- The move is its own inverse: at normed keys of the rank's order
the stated key less a member reads the member back at the stated key
less the move's own image. -/
theorem offKey_swap (n : Nat) (y k mu : List BPair)
    (hy : y.length = n) (hk : k.length = n) (hkn : poly.pnorm k = k)
    (h : poly.pnorm (elim.vecAdd y (poly.neg k)) = mu) :
    poly.pnorm (elim.vecAdd y (poly.neg mu)) = k := by
  have hnk : (poly.neg k).length = n :=
    (ground.length_map BPair.swap k).trans hk
  have hny : (poly.neg y).length = n :=
    (ground.length_map BPair.swap y).trans hy
  have hyk : (elim.vecAdd y (poly.neg k)).length = n :=
    elim.length_vecAdd y _ n hy hnk
  have hnyk : (poly.neg (elim.vecAdd y (poly.neg k))).length = n :=
    (ground.length_map BPair.swap _).trans hyk
  have hnpyk : (poly.neg (poly.pnorm
      (elim.vecAdd y (poly.neg k)))).length = n :=
    (ground.length_map BPair.swap _).trans
      ((poly.pnorm_length _).trans hyk)
  rw [← h]
  have h1 : poly.pnorm (elim.vecAdd y
        (poly.neg (poly.pnorm (elim.vecAdd y (poly.neg k)))))
      = poly.pnorm (elim.vecAdd y
        (poly.neg (elim.vecAdd y (poly.neg k)))) := by
    refine poly.pnorm_congr _ _ ?_ ?_
    · rw [elim.length_vecAdd y _ n hy hnpyk,
        elim.length_vecAdd y _ n hy hnyk]
    · exact elim.polyOne_vecAdd y y _ _ (poly.oneValue_refl y)
        (poly.swapMap_oneValue (poly.pnorm_oneValue _)) rfl
        (hnpyk.trans hnyk.symm)
  rw [h1, neg_vecAdd y (poly.neg k), poly.neg_neg k,
    ← elim.vecAdd_assoc y (poly.neg y) k,
    elim.vecAdd_comm y (poly.neg y)]
  have hz : poly.unitTail (elim.vecAdd (poly.neg y) y) :=
    poly.oneValue_unitTail (vecAdd_swap_self y)
      (poly.unitTail_replicate _)
  have hzl : (elim.vecAdd (poly.neg y) y).length = k.length := by
    rw [elim.length_vecAdd _ _ n hny hy, hk]
  refine (poly.pnorm_congr _ _ ?_
    (elim.vecAdd_null_left _ _ hzl hz)).trans hkn
  rw [elim.length_vecAdd _ _ n (elim.length_vecAdd _ _ n hny hy) hk, hk]


private theorem imgSi (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank) (hpi : permImageRead t F) :
    poly.oneValue
      (elim.matVec (reflM t i)
        (posCorootV t (ground.getAt 0 F.simplePos i)))
      (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))) := by
  refine poly.oneValue_trans
    (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
  rw [show poly.pnorm (elim.matVec (reflM t i)
      (posCorootV t (ground.getAt 0 F.simplePos i)))
    = reflAt t i (posCorootV t (ground.getAt 0 F.simplePos i))
    from rfl, (hpi i hi).2]
  exact poly.pnorm_oneValue _

private theorem imgOff (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank) (hpi : permImageRead t F)
    {j : Nat} (hj : j < t.posFolds.length)
    (hne : j ≠ ground.getAt 0 F.simplePos i) :
    poly.oneValue
      (elim.matVec (reflM t i) (posCorootV t j))
      (posCorootV t
        (ground.getAt 0 (ground.getAt [] F.perms i) j)) := by
  refine poly.oneValue_trans
    (poly.oneValue_symm (poly.pnorm_oneValue _)) ?_
  rw [show poly.pnorm (elim.matVec (reflM t i) (posCorootV t j))
    = reflAt t i (posCorootV t j) from rfl, (hpi i hi).1 j hj hne]
  exact poly.pnorm_oneValue _

/-- The shared guarded read off the simple's position. -/
private def g3 (t : gentable.Table) (F : FundData) (i : Nat)
    (S : List Nat) : Nat → List BPair := fun j =>
  if j == ground.getAt 0 F.simplePos i then
    (if ground.containsB S (ground.getAt 0 F.simplePos i) then
      poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
    else List.replicate t.rank BPair.unit)
  else (if ground.containsB S
      (ground.getAt 0 (ground.getAt [] F.perms i) j) then
    posCorootV t j
  else List.replicate t.rank BPair.unit)

private theorem g3_len (t : gentable.Table) (F : FundData)
    (i : Nat) (S : List Nat) : ∀ j, (g3 t F i S j).length = t.rank :=
  fun j => by
    show (if j == ground.getAt 0 F.simplePos i then
        (if ground.containsB S (ground.getAt 0 F.simplePos i) then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else List.replicate t.rank BPair.unit)
      else (if ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) j) then
        posCorootV t j
      else List.replicate t.rank BPair.unit)).length = t.rank
    by_cases h1 : (j == ground.getAt 0 F.simplePos i) = true
    · rw [if_pos h1]
      by_cases h2 : ground.containsB S (ground.getAt 0 F.simplePos i) = true
      · rw [if_pos h2, poly.length_neg]
        exact posCorootV_length t _
      · rw [if_neg h2]
        exact ground.length_replicate BPair.unit t.rank
    · rw [if_neg h1]
      by_cases h2 : ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) j) = true
      · rw [if_pos h2]
        exact posCorootV_length t j
      · rw [if_neg h2]
        exact ground.length_replicate BPair.unit t.rank

private theorem guardS_len (t : gentable.Table) (S : List Nat) :
    ∀ j, ((fun j => if ground.containsB S j then posCorootV t j
      else List.replicate t.rank BPair.unit) j).length = t.rank :=
  fun j => by
    show (if ground.containsB S j then posCorootV t j
      else List.replicate t.rank BPair.unit).length = t.rank
    by_cases h : ground.containsB S j = true
    · rw [if_pos h]
      exact posCorootV_length t j
    · rw [if_neg h]
      exact ground.length_replicate BPair.unit t.rank

private theorem chainR (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank) (hshape : fundShape t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (S : List Nat)
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length))) :
    poly.oneValue
      (elim.matVec (reflM t i)
        (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
          (List.replicate t.rank BPair.unit)))
      (elim.vecAdd
        (if ground.containsB S (ground.getAt 0 F.simplePos i) then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else List.replicate t.rank BPair.unit)
        (ground.famFold elim.vecAdd
          (List.replicate t.rank BPair.unit) (g3 t F i S)
          (ground.eraseFirst (ground.getAt 0 F.simplePos i)
            (List.range t.posFolds.length)))) := by
  have hsin := simplePos_lt t F hshape hi
  have hchar := ground.sublists_char (List.range t.posFolds.length)
    (ground.distinctList_all (ground.distinctList_range t.posFolds.length)) S hS
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  have hfold : poly.oneValue
      (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
        (List.replicate t.rank BPair.unit)) (vsum t S) := by
    refine poly.oneValue_trans (foldl_vsum t S _ hz) ?_
    rw [elim.vecAdd_comm]
    exact elim.vecAdd_null_right (vsum t S) (List.replicate t.rank BPair.unit)
      (by rw [ground.length_replicate]; exact vsum_length t S)
      (poly.unitTail_replicate t.rank)
  have hvchar : vsum t S = ground.famFold elim.vecAdd
      (List.replicate t.rank BPair.unit) (posCorootV t)
      (List.filter (ground.containsB S) (List.range t.posFolds.length)) := by
    show ground.famFold elim.vecAdd _ (posCorootV t) S = _
    rw [← hchar]
  refine poly.oneValue_trans
    (elim.matVec_congr (reflM t i) _ (vsum t S)
      hfold) ?_
  rw [hvchar]
  refine poly.oneValue_trans
    (elim.matVec_congr (reflM t i) _ _
      (fvFilterL t _
        (fun j => posCorootV_length t j) (ground.containsB S)
        (List.range t.posFolds.length))) ?_
  refine poly.oneValue_trans
    (mvFold t i _ (guardS_len t S) (List.range t.posFolds.length)) ?_
  have hg2len : ∀ j, ((fun j =>
      if ground.containsB S j then
        (if j == ground.getAt 0 F.simplePos i then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else posCorootV t
          (ground.getAt 0 (ground.getAt [] F.perms i) j))
      else List.replicate t.rank BPair.unit) j).length = t.rank :=
    fun j => by
      show (if ground.containsB S j then
        (if j == ground.getAt 0 F.simplePos i then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else posCorootV t
          (ground.getAt 0 (ground.getAt [] F.perms i) j))
      else List.replicate t.rank BPair.unit).length = t.rank
      by_cases h1 : ground.containsB S j = true
      · rw [if_pos h1]
        by_cases h2 : (j == ground.getAt 0 F.simplePos i) = true
        · rw [if_pos h2, poly.length_neg]
          exact posCorootV_length t _
        · rw [if_neg h2]
          exact posCorootV_length t _
      · rw [if_neg h1]
        exact hz
  refine poly.oneValue_trans
    (fvCongrMem t _ _
      (fun j => (elim.matVec_length _ _).trans (reflM_length t i))
      hg2len (List.range t.posFolds.length) (fun j hj => ?_)) ?_
  · have hjn : j < t.posFolds.length := ground.ltOfMem hj
    show poly.oneValue (elim.matVec (reflM t i)
      (if ground.containsB S j then posCorootV t j
        else List.replicate t.rank BPair.unit)) _
    by_cases h1 : ground.containsB S j = true
    · rw [if_pos h1]
      show poly.oneValue _ (if ground.containsB S j then
        (if j == ground.getAt 0 F.simplePos i then _ else _) else _)
      rw [if_pos h1]
      by_cases h2 : (j == ground.getAt 0 F.simplePos i) = true
      · rw [if_pos h2, ground.beqEqOf h2]
        exact imgSi t F hi hpi
      · rw [if_neg h2]
        exact imgOff t F hi hpi hjn
          (fun he => h2 (ground.eqBeqOf he))
    · rw [if_neg h1]
      show poly.oneValue _ (if ground.containsB S j then
        (if j == ground.getAt 0 F.simplePos i then _ else _) else _)
      rw [if_neg h1]
      exact matVec_unitV (reflM t i) t.rank t.rank (reflM_length t i)
  rw [ground.famFold_reindex elim.vecAdd
    (List.replicate t.rank BPair.unit) elim.vecAdd_comm elim.vecAdd_assoc _
    (fun x _ => ground.distinctList_all (ground.distinctList_range t.posFolds.length) x)
    (g := fun x => ground.getAt 0 (ground.getAt [] F.perms i) x)
    (h := fun x => ground.getAt 0 (ground.getAt [] F.perms i) x)
    (fun x hx => hpsq i hi x (ground.ltOfMem hx))
    (fun x hx => hpsq i hi x (ground.ltOfMem hx))
    (fun x hx => by
      rw [ground.countOf_range_one (perm_lt t F hshape hi (ground.ltOfMem hx))]
      exact Nat.succ_pos 0)
    (fun x hx => by
      rw [ground.countOf_range_one (perm_lt t F hshape hi (ground.ltOfMem hx))]
      exact Nat.succ_pos 0)]
  refine poly.oneValue_trans
    (fvCongrMem t _ _ (fun j => by
        show (if ground.containsB S
            (ground.getAt 0 (ground.getAt [] F.perms i) j) then
            (if ground.getAt 0 (ground.getAt [] F.perms i) j
                == ground.getAt 0 F.simplePos i then
              poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
            else posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
              (ground.getAt 0 (ground.getAt [] F.perms i) j)))
          else List.replicate t.rank BPair.unit).length = t.rank
        by_cases h1 : ground.containsB S
            (ground.getAt 0 (ground.getAt [] F.perms i) j) = true
        · rw [if_pos h1]
          by_cases h2 : (ground.getAt 0 (ground.getAt [] F.perms i) j
              == ground.getAt 0 F.simplePos i) = true
          · rw [if_pos h2, poly.length_neg]
            exact posCorootV_length t _
          · rw [if_neg h2]
            exact posCorootV_length t _
        · rw [if_neg h1]
          exact hz)
      (g3_len t F i S) (List.range t.posFolds.length)
      (fun j hj => ?_)) ?_
  · have hjn : j < t.posFolds.length := ground.ltOfMem hj
    show poly.oneValue
      (if ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) j) then
        (if ground.getAt 0 (ground.getAt [] F.perms i) j
            == ground.getAt 0 F.simplePos i then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 (ground.getAt [] F.perms i) j)))
      else List.replicate t.rank BPair.unit)
      (g3 t F i S j)
    by_cases hjsi : j = ground.getAt 0 F.simplePos i
    · rw [hjsi, perm_fix t F hi hshape hsq hpsq hpi hrd]
      show poly.oneValue _ (g3 t F i S
        (ground.getAt 0 F.simplePos i))
      show poly.oneValue _
        (if ground.getAt 0 F.simplePos i
            == ground.getAt 0 F.simplePos i then
          (if ground.containsB S (ground.getAt 0 F.simplePos i) then
            poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
          else List.replicate t.rank BPair.unit)
        else _)
      rw [if_pos (ground.eqBeqOf rfl), if_pos (ground.eqBeqOf rfl)]
      exact poly.oneValue_refl _
    · have hpne := perm_ne_si t F hi hshape hsq hpsq hpi hrd hjn hjsi
      show poly.oneValue _
        (if j == ground.getAt 0 F.simplePos i then _
        else (if ground.containsB S
            (ground.getAt 0 (ground.getAt [] F.perms i) j) then
          posCorootV t j
        else List.replicate t.rank BPair.unit))
      rw [if_neg (fun ht : (ground.getAt 0 (ground.getAt [] F.perms i)
            j == ground.getAt 0 F.simplePos i) = true
          => hpne (ground.beqEqOf ht)),
        if_neg (fun ht : (j == ground.getAt 0 F.simplePos i) = true
          => hjsi (ground.beqEqOf ht)),
        hpsq i hi j hjn]
      exact poly.oneValue_refl _
  rw [ground.famFold_eraseFirst elim.vecAdd
    (List.replicate t.rank BPair.unit) elim.vecAdd_comm elim.vecAdd_assoc
    (g3 t F i S) (List.range t.posFolds.length) _
    (by rw [ground.countOf_range_one hsin]; exact Nat.succ_pos 0)]
  refine elim.vecAdd_congr2 _ _ _ _ ?_ rfl ?_ (poly.oneValue_refl _)
  · show (g3 t F i S (ground.getAt 0 F.simplePos i)).length = _
    rw [g3_len t F i S _]
    by_cases h2 : ground.containsB S (ground.getAt 0 F.simplePos i) = true
    · rw [if_pos h2, poly.length_neg, posCorootV_length]
    · rw [if_neg h2, ground.length_replicate]
  · show poly.oneValue (g3 t F i S (ground.getAt 0 F.simplePos i)) _
    show poly.oneValue
      (if ground.getAt 0 F.simplePos i
          == ground.getAt 0 F.simplePos i then
        (if ground.containsB S (ground.getAt 0 F.simplePos i) then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else List.replicate t.rank BPair.unit)
      else _) _
    rw [if_pos (ground.eqBeqOf rfl)]
    exact poly.oneValue_refl _

private theorem chainL (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank) (hshape : fundShape t F)
    (S : List Nat) :
    poly.oneValue
      ((flipT t F i S).foldl
        (fun acc j => elim.vecAdd acc (posCorootV t j))
        (List.replicate t.rank BPair.unit))
      (elim.vecAdd
        (if ground.containsB S (ground.getAt 0 F.simplePos i) then
          List.replicate t.rank BPair.unit
        else posCorootV t (ground.getAt 0 F.simplePos i))
        (ground.famFold elim.vecAdd
          (List.replicate t.rank BPair.unit) (g3 t F i S)
          (ground.eraseFirst (ground.getAt 0 F.simplePos i)
            (List.range t.posFolds.length)))) := by
  have hsin := simplePos_lt t F hshape hi
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  refine poly.oneValue_trans (poly.oneValue_trans
    (foldl_vsum t (flipT t F i S) _ hz) (by
      rw [elim.vecAdd_comm]
      exact elim.vecAdd_null_right (vsum t (flipT t F i S))
        (List.replicate t.rank BPair.unit)
        (by rw [ground.length_replicate]; exact vsum_length t _)
        (poly.unitTail_replicate t.rank))) ?_
  show poly.oneValue (ground.famFold elim.vecAdd
    (List.replicate t.rank BPair.unit) (posCorootV t)
    (List.filter _ (List.range t.posFolds.length))) _
  refine poly.oneValue_trans (fvFilterL t _
    (fun j => posCorootV_length t j) _
    (List.range t.posFolds.length)) ?_
  have hgTlen : ∀ j, ((fun j =>
      if (if j == ground.getAt 0 F.simplePos i then
        !(ground.containsB S (ground.getAt 0 F.simplePos i))
      else ground.containsB S
        (ground.getAt 0 (ground.getAt [] F.perms i) j)) then
        posCorootV t j
      else List.replicate t.rank BPair.unit) j).length = t.rank :=
    fun j => by
      show (if (if j == ground.getAt 0 F.simplePos i then
          !(ground.containsB S (ground.getAt 0 F.simplePos i))
        else ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) j)) then
          posCorootV t j
        else List.replicate t.rank BPair.unit).length = t.rank
      by_cases h1 : (if j == ground.getAt 0 F.simplePos i then
          !(ground.containsB S (ground.getAt 0 F.simplePos i))
        else ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) j)) = true
      · rw [if_pos h1]
        exact posCorootV_length t j
      · rw [if_neg h1]
        exact hz
  rw [ground.famFold_eraseFirst elim.vecAdd
    (List.replicate t.rank BPair.unit) elim.vecAdd_comm elim.vecAdd_assoc _
    (List.range t.posFolds.length) _
    (by rw [ground.countOf_range_one hsin]; exact Nat.succ_pos 0)]
  refine elim.vecAdd_congr2 _ _ _ _ ?_ ?_ ?_ ?_
  · show (if (if ground.getAt 0 F.simplePos i
        == ground.getAt 0 F.simplePos i then
        !(ground.containsB S (ground.getAt 0 F.simplePos i))
      else _) then posCorootV t (ground.getAt 0 F.simplePos i)
      else List.replicate t.rank BPair.unit).length = _
    rw [if_pos (ground.eqBeqOf rfl)]
    cases hc : ground.containsB S (ground.getAt 0 F.simplePos i) with
    | true =>
      rw [if_neg (ground.boolNe (show (!true) = false from rfl)),
        if_pos rfl]
    | false =>
      rw [if_pos (show (!false) = true from rfl),
        if_neg (ground.boolNe rfl)]
  · exact (fvLen t _ hgTlen _).trans (fvLen t _ (g3_len t F i S) _).symm
  · show poly.oneValue
      (if (if ground.getAt 0 F.simplePos i
          == ground.getAt 0 F.simplePos i then
        !(ground.containsB S (ground.getAt 0 F.simplePos i))
      else _) then posCorootV t (ground.getAt 0 F.simplePos i)
      else List.replicate t.rank BPair.unit) _
    rw [if_pos (ground.eqBeqOf rfl)]
    cases hc : ground.containsB S (ground.getAt 0 F.simplePos i) with
    | true =>
      rw [if_neg (ground.boolNe (show (!true) = false from rfl)),
        if_pos rfl]
      exact poly.oneValue_refl _
    | false =>
      rw [if_pos (show (!false) = true from rfl),
        if_neg (ground.boolNe rfl)]
      exact poly.oneValue_refl _
  · refine fvCongrMem t _ _ hgTlen (g3_len t F i S) _
      (fun j hj => ?_)
    obtain ⟨hjn, hjsi⟩ := eraseFirst_range_count hj
    show poly.oneValue
      (if (if j == ground.getAt 0 F.simplePos i then _
        else ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) j)) then
        posCorootV t j
      else List.replicate t.rank BPair.unit)
      (g3 t F i S j)
    show poly.oneValue _
      (if j == ground.getAt 0 F.simplePos i then _
      else (if ground.containsB S
          (ground.getAt 0 (ground.getAt [] F.perms i) j) then
        posCorootV t j
      else List.replicate t.rank BPair.unit))
    rw [if_neg (fun ht : (j == ground.getAt 0 F.simplePos i) = true
        => hjsi (ground.beqEqOf ht)),
      if_neg (fun ht : (j == ground.getAt 0 F.simplePos i) = true
        => hjsi (ground.beqEqOf ht))]
    exact poly.oneValue_refl _

private theorem shuffle (t : gentable.Table) (P T3 : List BPair)
    (hP : P.length = t.rank) (hT : T3.length = t.rank) (c : Bool) :
    poly.oneValue
      (elim.vecAdd (elim.vecAdd (rhoV t) (poly.neg P))
        (poly.neg (elim.vecAdd
          (if c then poly.neg P else List.replicate t.rank BPair.unit)
          T3)))
      (elim.vecAdd (rhoV t)
        (poly.neg (elim.vecAdd
          (if c then List.replicate t.rank BPair.unit else P)
          T3))) := by
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  have hnP : (poly.neg P).length = t.rank := by
    rw [poly.length_neg]
    exact hP
  have hnT : (poly.neg T3).length = t.rank := by
    rw [poly.length_neg]
    exact hT
  have hPP : (elim.vecAdd (poly.neg P) P).length = t.rank := by
    rw [vecAdd_length (hnP.trans hP.symm)]
    exact hnP
  have hzT : (elim.vecAdd (List.replicate t.rank BPair.unit)
      (poly.neg T3)).length = t.rank := by
    rw [vecAdd_length (hz.trans hnT.symm)]
    exact hz
  cases c with
  | true =>
    rw [if_pos rfl, if_pos rfl, neg_vecAdd, poly.neg_neg,
      neg_vecAdd, poly.neg_repl, elim.vecAdd_assoc,
      ← elim.vecAdd_assoc (poly.neg P) P (poly.neg T3)]
    refine elim.vecAdd_congr2 _ _ _ _ rfl ?_ (poly.oneValue_refl _) ?_
    · refine Eq.trans ?_ hzT.symm
      rw [vecAdd_length (hPP.trans hnT.symm)]
      exact hPP
    · refine elim.vecAdd_congr2 _ _ _ _ (hPP.trans hz.symm) rfl ?_
        (poly.oneValue_refl _)
      rw [show List.replicate t.rank BPair.unit
          = List.replicate P.length BPair.unit from by rw [hP]]
      exact vecAdd_swap_self P
  | false =>
    rw [if_neg (ground.boolNe rfl), if_neg (ground.boolNe rfl),
      neg_vecAdd, poly.neg_repl, neg_vecAdd, elim.vecAdd_assoc]
    refine elim.vecAdd_congr2 _ _ _ _ rfl ?_ (poly.oneValue_refl _) ?_
    · rw [vecAdd_length (hnP.trans hzT.symm),
        vecAdd_length (hnP.trans hnT.symm)]
    · refine elim.vecAdd_congr2 _ _ _ _ rfl (hzT.trans hnT.symm)
        (poly.oneValue_refl _) ?_
      rw [elim.vecAdd_comm]
      exact elim.vecAdd_null_right (poly.neg T3) (List.replicate t.rank BPair.unit)
        (by rw [ground.length_replicate]; exact hnT)
        (poly.unitTail_replicate t.rank)

/-- The subset fold's vector at the rank's order, the landed
`elim.vsum` spelling. -/
private theorem vsumP_length (t : gentable.Table) (S : List Nat) :
    (elim.vsum t.rank (posCorootV t) S).length = t.rank :=
  foldl_length t S _ (ground.length_replicate BPair.unit t.rank)

/-- A subset family's key sits at the rank's order. -/
theorem eKey_length (t : gentable.Table) (S : List Nat) :
    (eKey t S).length = t.rank := by
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hnf : (poly.neg
      (elim.vsum t.rank (posCorootV t) S)).length = t.rank := by
    rw [poly.length_neg]
    exact vsumP_length t S
  show (poly.pnorm (elim.vecAdd (rhoV t) (poly.neg _))).length = t.rank
  rw [poly.pnorm_length, vecAdd_length (hrho.trans hnf.symm)]
  exact hrho

/-- A subset family's key is normed. -/
theorem eKey_norm (t : gentable.Table) (S : List Nat) :
    poly.pnorm (eKey t S) = eKey t S := poly.pnorm_pnorm _

/-- The key transport: the flipped family's key is the key's
reflection image (`thm:assembly`'s grading, `s_i e_S = e_{T_i S}`). -/
private theorem eKey_flip (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank) (hshape : fundShape t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hsp : simplePosRead t F) (S : List Nat)
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length))) :
    eKey t (flipT t F i S) = reflAt t i (eKey t S) := by
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hXlen : (elim.vecAdd (rhoV t)
      (poly.neg (elim.vsum t.rank (posCorootV t) S))).length
      = t.rank := by
    rw [vecAdd_length (by rw [poly.length_neg, hrho, vsumP_length t S])]
    exact hrho
  have hR : reflAt t i (eKey t S)
      = poly.pnorm (elim.matVec (reflM t i)
        (elim.vecAdd (rhoV t)
          (poly.neg (elim.vsum t.rank (posCorootV t) S)))) := by
    show reflAt t i (poly.pnorm _) = _
    rw [reflAt_pnorm]
    rfl
  rw [hR]
  show poly.pnorm (elim.vecAdd (rhoV t) (poly.neg _)) = _
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [vecAdd_length (by rw [poly.length_neg, hrho,
      vsumP_length t (flipT t F i S)]), hrho,
      elim.matVec_length, reflM_length]
  · refine poly.oneValue_symm ?_
    refine poly.oneValue_trans
      (elim.matVec_vecAdd (reflM t i) t.rank (reflM_rows t i) _ _
        hrho
        (by rw [poly.length_neg]; exact foldl_length t S _ hz)) ?_
    rw [elim.matVec_neg]
    have hT3len : (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit) (g3 t F i S)
        (ground.eraseFirst (ground.getAt 0 F.simplePos i)
          (List.range t.posFolds.length))).length = t.rank :=
      fvLen t _ (g3_len t F i S) _
    have hH3len : (if ground.containsB S (ground.getAt 0 F.simplePos i) then
        poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
      else List.replicate t.rank BPair.unit).length = t.rank := by
      by_cases hc : ground.containsB S (ground.getAt 0 F.simplePos i) = true
      · rw [if_pos hc, poly.length_neg]
        exact posCorootV_length t _
      · rw [if_neg hc]
        exact hz
    have hH3T3 : (elim.vecAdd
        (if ground.containsB S (ground.getAt 0 F.simplePos i) then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else List.replicate t.rank BPair.unit)
        (ground.famFold elim.vecAdd
          (List.replicate t.rank BPair.unit) (g3 t F i S)
          (ground.eraseFirst (ground.getAt 0 F.simplePos i)
            (List.range t.posFolds.length)))).length = t.rank := by
      rw [vecAdd_length (hH3len.trans hT3len.symm)]
      exact hH3len
    have hnp : (poly.neg (posCorootV t
        (ground.getAt 0 F.simplePos i))).length = t.rank := by
      rw [poly.length_neg]
      exact posCorootV_length t _
    have hU' : (elim.vecAdd (rhoV t)
        (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i)))).length
        = t.rank := by
      rw [vecAdd_length (hrho.trans hnp.symm)]
      exact hrho
    refine poly.oneValue_trans
      (elim.vecAdd_congr2 _ _ _ _
        (((elim.matVec_length _ _).trans (reflM_length t i)).trans
          hU'.symm)
        ((ground.length_map BPair.swap _).trans
          (((elim.matVec_length _ _).trans (reflM_length t i)).trans
            (hH3T3.symm.trans (ground.length_map BPair.swap _).symm)))
        (rho_reflM t F i hi hsp)
        (poly.swapMap_oneValue
          (chainR t F hi hshape hsq hpsq hpi hrd S hS))) ?_
    refine poly.oneValue_trans
      (shuffle t (posCorootV t (ground.getAt 0 F.simplePos i))
        (ground.famFold elim.vecAdd
          (List.replicate t.rank BPair.unit) (g3 t F i S)
          (ground.eraseFirst (ground.getAt 0 F.simplePos i)
            (List.range t.posFolds.length)))
        (posCorootV_length t _) hT3len
        (ground.containsB S (ground.getAt 0 F.simplePos i))) ?_
    have hHTlen : (if ground.containsB S (ground.getAt 0 F.simplePos i) then
        List.replicate t.rank BPair.unit
      else posCorootV t (ground.getAt 0 F.simplePos i)).length
        = t.rank := by
      by_cases hc : ground.containsB S (ground.getAt 0 F.simplePos i) = true
      · rw [if_pos hc]
        exact hz
      · rw [if_neg hc]
        exact posCorootV_length t _
    have hHT3 : (elim.vecAdd
        (if ground.containsB S (ground.getAt 0 F.simplePos i) then
          List.replicate t.rank BPair.unit
        else posCorootV t (ground.getAt 0 F.simplePos i))
        (ground.famFold elim.vecAdd
          (List.replicate t.rank BPair.unit) (g3 t F i S)
          (ground.eraseFirst (ground.getAt 0 F.simplePos i)
            (List.range t.posFolds.length)))).length = t.rank := by
      rw [vecAdd_length (hHTlen.trans hT3len.symm)]
      exact hHTlen
    refine elim.vecAdd_congr2 _ _ _ _ rfl ?_ (poly.oneValue_refl _)
      (poly.swapMap_oneValue (poly.oneValue_symm
        (chainL t F hi hshape S)))
    exact (poly.length_neg _).trans
      (hHT3.trans ((foldl_length t (flipT t F i S) _ hz).symm.trans
        (poly.length_neg _).symm))

/-- The subset fold's grading: at a normed key of the rank's
length, the reflection image's count at a side is the key's count
at the flipped side (`thm:assembly`'s grading — the pairing `T_i`
an involution moving the count by one, at `s_i e_S = e_{T_i S}`
over the letter's read and the permutation read). -/
theorem subsetCount_refl (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (i : Nat) (hi : i < t.rank)
    (y : List BPair) (hy : y.length = t.rank) (hny : poly.pnorm y = y)
    (s : Bool) :
    subsetCount t (reflAt t i y) s = subsetCount t y (!s) := by
  have hdist : ground.distinctList
      (ground.sublistsOf (List.range t.posFolds.length)) :=
    fun S _ => ground.sublists_count_le (List.range t.posFolds.length)
      (ground.distinctList_all (ground.distinctList_range t.posFolds.length)) S
  have hinv : ∀ S, 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length)) →
      flipT t F i (flipT t F i S) = S :=
    flipT_invol t F hi hshape hsq hpsq hpi hrd
  have hmem : ∀ S, 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length)) →
      0 < ground.countOf (flipT t F i S)
        (ground.sublistsOf (List.range t.posFolds.length)) :=
    fun S _ => ground.filter_member _ (List.range t.posFolds.length)
  show ground.famFold Nat.add 0
      (fun S => if places.sideOf S = s then
        (if eKey t S = reflAt t i y then 1 else 0) else 0)
      (ground.sublistsOf (List.range t.posFolds.length))
    = ground.famFold Nat.add 0
      (fun S => if places.sideOf S = !s then
        (if eKey t S = y then 1 else 0) else 0)
      (ground.sublistsOf (List.range t.posFolds.length))
  rw [ground.famFold_reindex (g := flipT t F i) (h := flipT t F i)
    Nat.add 0 Nat.add_comm Nat.add_assoc
    (fun S => if places.sideOf S = s then
      (if eKey t S = reflAt t i y then 1 else 0) else 0)
    hdist hinv hinv hmem hmem]
  refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
  intro S hS
  show (if places.sideOf (flipT t F i S) = s then
      (if eKey t (flipT t F i S) = reflAt t i y then 1 else 0)
    else 0)
    = (if places.sideOf S = !s then
      (if eKey t S = y then 1 else 0) else 0)
  rw [parity_flip t F hi hshape hsq hpsq hpi hrd S hS,
    eKey_flip t F hi hshape hsq hpsq hpi hrd hsp S hS]
  have hinner : (if reflAt t i (eKey t S) = reflAt t i y
      then (1 : Nat) else 0) = (if eKey t S = y then 1 else 0) := by
    by_cases h : eKey t S = y
    · rw [if_pos h, if_pos (congrArg (reflAt t i) h)]
    · have hne : ¬ (reflAt t i (eKey t S) = reflAt t i y) := by
        intro hr
        have h2 := congrArg (reflAt t i) hr
        rw [reflAt_invol' t i (hsq i hi) _ (eKey_length t S),
          reflAt_invol' t i (hsq i hi) y hy, eKey_norm, hny] at h2
        exact h h2
      rw [if_neg h, if_neg hne]
  rw [hinner]
  cases hp : places.sideOf S <;> cases s <;> rfl

/-! The subset fold's fast read: the positive-list product
evaluated factor by factor at the key chart (`thm:assembly`'s
expansion sentence read at the product side), the running table of
keys at their two graded counts, with the proven equality the
expansion identity itself. -/

/-- One factor's key move: the key less the factor's coroot vector,
normed. -/
private def mkKey (t : gentable.Table) (a : Nat)
    (k : List BPair) : List BPair :=
  poly.pnorm (elim.vecAdd k (poly.neg (posCorootV t a)))

private theorem eKey_cons (t : gentable.Table) (a : Nat)
    (S : List Nat) : eKey t (a :: S) = mkKey t a (eKey t S) := by
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hZA : (elim.vecAdd (List.replicate t.rank BPair.unit)
      (posCorootV t a)).length = t.rank := by
    rw [vecAdd_length (hz.trans (posCorootV_length t a).symm)]
    exact hz
  have hFS : ((S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
      (List.replicate t.rank BPair.unit))).length = t.rank :=
    foldl_length t S _ hz
  have hFA : ((S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
      (elim.vecAdd (List.replicate t.rank BPair.unit)
        (posCorootV t a)))).length = t.rank :=
    foldl_length t S _ hZA
  have hone : poly.oneValue
      (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
        (elim.vecAdd (List.replicate t.rank BPair.unit)
          (posCorootV t a)))
      (elim.vecAdd
        (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
          (List.replicate t.rank BPair.unit))
        (posCorootV t a)) := by
    refine poly.oneValue_trans (foldl_vsum t S _ hZA) ?_
    rw [elim.vecAdd_assoc, elim.vecAdd_comm (posCorootV t a)
      (vsum t S), ← elim.vecAdd_assoc]
    refine elim.vecAdd_congr2 _ _ _ _ ?_ rfl
      (poly.oneValue_symm (foldl_vsum t S _ hz))
      (poly.oneValue_refl _)
    rw [vecAdd_length (hz.trans (vsum_length t S).symm)]
    exact hz.trans hFS.symm
  have hnFS : (poly.neg (S.foldl
      (fun acc j => elim.vecAdd acc (posCorootV t j))
      (List.replicate t.rank BPair.unit))).length = t.rank := by
    rw [poly.length_neg]
    exact hFS
  have hnFA : (poly.neg (S.foldl
      (fun acc j => elim.vecAdd acc (posCorootV t j))
      (elim.vecAdd (List.replicate t.rank BPair.unit)
        (posCorootV t a)))).length = t.rank := by
    rw [poly.length_neg]
    exact hFA
  have hna : (poly.neg (posCorootV t a)).length = t.rank := by
    rw [poly.length_neg]
    exact posCorootV_length t a
  have hX : (elim.vecAdd (rhoV t)
      (poly.neg (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
        (List.replicate t.rank BPair.unit)))).length = t.rank := by
    rw [vecAdd_length (hrho.trans hnFS.symm)]
    exact hrho
  show poly.pnorm (elim.vecAdd (rhoV t)
      (poly.neg (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
        (elim.vecAdd (List.replicate t.rank BPair.unit)
          (posCorootV t a)))))
    = poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd (rhoV t)
          (poly.neg (S.foldl
            (fun acc j => elim.vecAdd acc (posCorootV t j))
            (List.replicate t.rank BPair.unit)))))
        (poly.neg (posCorootV t a)))
  rw [elim.pnorm_vecAdd_left _ _ (hX.trans hna.symm)]
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [vecAdd_length (hrho.trans hnFA.symm),
      vecAdd_length (hX.trans hna.symm)]
    exact hrho.trans hX.symm
  · rw [elim.vecAdd_assoc, ← neg_vecAdd]
    exact elim.vecAdd_congr2 _ _ _ _ rfl (by
        rw [poly.length_neg, poly.length_neg, hFA,
          vecAdd_length (hFS.trans (posCorootV_length t a).symm)]
        exact hFS.symm)
      (poly.oneValue_refl _) (poly.swapMap_oneValue hone)

/-- The key order's member test, the lex read at the pairs'
components. -/
private def bpLt (a b : BPair) : Bool :=
  decide (a.fst < b.fst)
    || (decide (a.fst = b.fst) && decide (a.snd < b.snd))

/-- The key order: the lex read over the coordinate lists. -/
private def keyLt : List BPair → List BPair → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: u, b :: v => bpLt a b || (decide (a = b) && keyLt u v)

/-- One factor's step: each entry kept and re-entered at the moved
key with its sides exchanged. -/
private def stepT (t : gentable.Table) (a : Nat)
    (acc : List (List BPair × Nat × Nat)) :
    List (List BPair × Nat × Nat) :=
  ground.tabMerge keyLt acc
    (acc.map (fun kv => (mkKey t a kv.1, kv.2.2, kv.2.1)))

private theorem stepT_read (t : gentable.Table) (a : Nat)
    (P : List BPair → Bool) (s : Bool)
    (acc : List (List BPair × Nat × Nat)) :
    ground.tabRead P s (stepT t a acc)
      = ground.tabRead P s acc
        + ground.tabRead (fun k => P (mkKey t a k)) (!s) acc := by
  show ground.tabRead P s (ground.tabMerge keyLt acc
    (acc.map (fun kv => (mkKey t a kv.1, kv.2.2, kv.2.1)))) = _
  rw [ground.tabMerge_read]
  refine congrArg (ground.tabRead P s acc + ·) ?_
  show ground.famFold Nat.add 0 _ (acc.map _) = _
  rw [ground.famFold_map]
  refine ground.famFold_congr_all Nat.add 0 _ _ ?_ acc
  intro kv
  show (if P (mkKey t a kv.1) then (if s then kv.2.1 else kv.2.2)
      else 0)
    = (if P (mkKey t a kv.1) then (if !s then kv.2.2 else kv.2.1)
      else 0)
  cases s with
  | true => rfl
  | false => rfl

/-- The running table over a position list. -/
private def accF (t : gentable.Table) : List Nat →
    List (List BPair × Nat × Nat)
  | [] => [(eKey t [], 1, 0)]
  | a :: l => stepT t a (accF t l)

private theorem sideOf_cons (a : Nat) (S : List Nat) :
    places.sideOf (a :: S) = !(places.sideOf S) := rfl

/-- The invariant: the table's read at every key predicate is the
subset fold's over the positions' families. -/
private theorem accF_read (t : gentable.Table) :
    ∀ (l : List Nat) (P : List BPair → Bool) (s : Bool),
      ground.tabRead P s (accF t l)
        = ground.famFold Nat.add 0
            (fun S => if P (eKey t S) then
              (if places.sideOf S = s then 1 else 0) else 0)
            (ground.sublistsOf l)
  | [], P, s => by
    show (if P (eKey t []) then (if s then 0 else 1) else 0) + 0
      = (if P (eKey t []) then
          (if places.sideOf [] = s then 1 else 0) else 0) + 0
    by_cases hp : P (eKey t []) = true
    · rw [if_pos hp, if_pos hp,
        show places.sideOf ([] : List Nat) = false from rfl]
      cases s with
      | true => rw [if_pos rfl, if_neg (ground.boolNe rfl)]
      | false => rw [if_neg (ground.boolNe rfl), if_pos rfl]
    · rw [if_neg hp, if_neg hp]
  | a :: l, P, s => by
    show ground.tabRead P s (stepT t a (accF t l)) = ground.famFold _ _ _
      (ground.sublistsOf l ++ (ground.sublistsOf l).map (fun T => a :: T))
    rw [stepT_read t a P s (accF t l),
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add,
      ground.famFold_map,
      ground.famFold_congr_all Nat.add 0
        (fun S => if P (eKey t (a :: S)) then
          (if places.sideOf (a :: S) = s then 1 else 0) else 0)
        (fun S => if P (mkKey t a (eKey t S)) then
          (if places.sideOf S = !s then 1 else 0) else 0)
        (fun S => by
          rw [eKey_cons, sideOf_cons]
          by_cases hp : P (mkKey t a (eKey t S)) = true
          · rw [if_pos hp, if_pos hp]
            cases hq : places.sideOf S with
            | true => cases s with
              | true => rw [if_neg (fun h => Bool.noConfusion h),
                  if_neg (fun h => Bool.noConfusion h)]
              | false => rw [if_pos (show (!true) = false from rfl),
                  if_pos (show true = !false from rfl)]
            | false => cases s with
              | true => rw [if_pos (show (!false) = true from rfl),
                  if_pos (show false = !true from rfl)]
              | false => rw [if_neg (fun h => Bool.noConfusion h),
                  if_neg (fun h => Bool.noConfusion h)]
          · rw [if_neg hp, if_neg hp])
        (ground.sublistsOf l),
      accF_read t l P s, accF_read t l (fun k => P (mkKey t a k)) (!s)]
    exact rfl

/-- The subset fold's collection: the running table over the
positive list, one fold read per key at the two graded counts
(`thm:assembly`'s subset-fold sentence, the product collecting
factor by factor). -/
def subsetTable (t : gentable.Table) :
    List (List BPair × Nat × Nat) :=
  accF t (List.range t.posFolds.length)

/-- The collection's read at a key is the subset fold's count:
`thm:assembly`'s expansion identity, the read the families'
counts' sum at every key. -/
theorem subsetTable_read (t : gentable.Table) (y : List BPair)
    (side : Bool) :
    ground.tabRead (fun k => decide (k = y)) side (subsetTable t)
      = subsetCount t y side := by
  show ground.tabRead (fun k => decide (k = y)) side
    (accF t (List.range t.posFolds.length)) = _
  rw [accF_read t (List.range t.posFolds.length)
    (fun k => decide (k = y)) side]
  refine ground.famFold_congr_all Nat.add 0 _ _ ?_ _
  intro S
  by_cases he : eKey t S = y
  · rw [decide_eq_true he, if_pos rfl, if_pos he]
  · cases hb : decide (eKey t S = y) with
    | true => exact absurd (of_decide_eq_true hb) he
    | false =>
      rw [if_neg (fun h => Bool.noConfusion h), if_neg he]
      by_cases hp : places.sideOf S = side
      · rw [if_pos hp]
      · rw [if_neg hp]

/-! The cofactor split (`thm:memberchar`'s `Q_j`): the occupancy
families over the positive list split at one index — the families
off it are the withdrawn list's own, and the families holding it
are the withdrawn list's again at the flipped side and the key
moved by the index's own coroot vector.  The move is the key shift
`e_{S+{j}} = e_S − α_j`, so a family holds the index at a key
exactly where the withdrawn family sits at the key joined to that
vector. -/

/-- The two key moves commute at a key of the rank's order. -/
private theorem mkKey_comm (t : gentable.Table) (a b : Nat)
    (k : List BPair) (hk : k.length = t.rank) :
    mkKey t a (mkKey t b k) = mkKey t b (mkKey t a k) := by
  have hna : (poly.neg (posCorootV t a)).length = t.rank := by
    rw [poly.length_neg]
    exact posCorootV_length t a
  have hnb : (poly.neg (posCorootV t b)).length = t.rank := by
    rw [poly.length_neg]
    exact posCorootV_length t b
  have hkb : (elim.vecAdd k (poly.neg (posCorootV t b))).length
      = t.rank := by
    rw [vecAdd_length (hk.trans hnb.symm)]
    exact hk
  have hka : (elim.vecAdd k (poly.neg (posCorootV t a))).length
      = t.rank := by
    rw [vecAdd_length (hk.trans hna.symm)]
    exact hk
  show poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd k
      (poly.neg (posCorootV t b)))) (poly.neg (posCorootV t a)))
    = poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd k
        (poly.neg (posCorootV t a)))) (poly.neg (posCorootV t b)))
  rw [elim.pnorm_vecAdd_left _ _ (hkb.trans hna.symm),
    elim.pnorm_vecAdd_left _ _ (hka.trans hnb.symm),
    elim.vecAdd_assoc k (poly.neg (posCorootV t b))
      (poly.neg (posCorootV t a)),
    elim.vecAdd_assoc k (poly.neg (posCorootV t a))
      (poly.neg (posCorootV t b)),
    elim.vecAdd_comm (poly.neg (posCorootV t b))
      (poly.neg (posCorootV t a))]

/-- The key shift at a normed key of the rank's order: a family's
key moves to the stated key exactly where the family sits at the
key joined to the index's own coroot vector. -/
private theorem mkKey_iff (t : gentable.Table) (j : Nat)
    (k y : List BPair) (hk : k.length = t.rank)
    (hkn : poly.pnorm k = k) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) :
    mkKey t j k = y ↔
      k = poly.pnorm (elim.vecAdd y (posCorootV t j)) := by
  have hA : (posCorootV t j).length = t.rank := posCorootV_length t j
  have hnA : (poly.neg (posCorootV t j)).length = t.rank := by
    rw [poly.length_neg]
    exact hA
  have hZ : (elim.vecAdd (posCorootV t j)
      (poly.neg (posCorootV t j))).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hA hnA
  have hzu : poly.unitTail (elim.vecAdd (posCorootV t j)
      (poly.neg (posCorootV t j))) := by
    rw [elim.vecAdd_comm (posCorootV t j) (poly.neg (posCorootV t j))]
    exact poly.oneValue_unitTail (vecAdd_swap_self (posCorootV t j))
      (poly.unitTail_replicate _)
  have hnull : ∀ v : List BPair, v.length = t.rank →
      poly.pnorm (elim.vecAdd v (elim.vecAdd (posCorootV t j)
        (poly.neg (posCorootV t j)))) = poly.pnorm v := by
    intro v hv
    refine poly.pnorm_congr _ _ ?_ ?_
    · rw [elim.length_vecAdd v _ t.rank hv hZ, hv]
    · exact elim.vecAdd_null_right v _ (hv.trans hZ.symm) hzu
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [← h]
    show k = poly.pnorm (elim.vecAdd (poly.pnorm
      (elim.vecAdd k (poly.neg (posCorootV t j)))) (posCorootV t j))
    rw [elim.pnorm_vecAdd_left _ _ (by
        rw [vecAdd_length (hk.trans hnA.symm), hk]
        exact hA.symm),
      elim.vecAdd_assoc k (poly.neg (posCorootV t j))
        (posCorootV t j),
      elim.vecAdd_comm (poly.neg (posCorootV t j)) (posCorootV t j),
      hnull k hk, hkn]
  · rw [h]
    show poly.pnorm (elim.vecAdd (poly.pnorm
      (elim.vecAdd y (posCorootV t j)))
      (poly.neg (posCorootV t j))) = y
    rw [elim.pnorm_vecAdd_left _ _ (by
        rw [vecAdd_length (hy.trans hA.symm), hy]
        exact hnA.symm),
      elim.vecAdd_assoc y (posCorootV t j)
        (poly.neg (posCorootV t j)),
      hnull y hy, hyn]

/-- The occupancy families' fold splits at one index: the families
off it fold as the withdrawn list's own, and the families holding
it fold as the withdrawn list's at the flipped side and the moved
key. -/
private theorem sublists_split (t : gentable.Table) :
    ∀ (l : List Nat) (j : Nat), 0 < ground.countOf j l →
    ∀ F : Bool → List BPair → Nat,
    ground.famFold Nat.add 0 (fun S => F (places.sideOf S) (eKey t S))
        (ground.sublistsOf l)
      = ground.famFold Nat.add 0 (fun S => F (places.sideOf S) (eKey t S))
          (ground.sublistsOf (ground.eraseFirst j l))
        + ground.famFold Nat.add 0
            (fun S => F (!places.sideOf S) (mkKey t j (eKey t S)))
            (ground.sublistsOf (ground.eraseFirst j l))
  | [], _, h, _ => absurd h (Nat.lt_irrefl 0)
  | a :: l, j, h, F => by
    have happ : ∀ (G : List Nat → Nat) (m : List Nat),
        ground.famFold Nat.add 0 G (ground.sublistsOf (a :: m))
          = ground.famFold Nat.add 0 G (ground.sublistsOf m)
            + ground.famFold Nat.add 0 (fun S => G (a :: S))
                (ground.sublistsOf m) := by
      intro G m
      show ground.famFold Nat.add 0 G
          (ground.sublistsOf m ++ (ground.sublistsOf m).map (fun S => a :: S)) = _
      rw [ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add
          G (ground.sublistsOf m) ((ground.sublistsOf m).map (fun S => a :: S)),
        ground.famFold_map Nat.add 0 G (fun S => a :: S)
          (ground.sublistsOf m)]
      rfl
    by_cases hja : j = a
    · have he : ground.eraseFirst j (a :: l) = l := by
        show (if j = a then l else a :: ground.eraseFirst j l) = l
        rw [if_pos hja]
      rw [he, happ (fun S => F (places.sideOf S) (eKey t S)) l]
      refine congrArg (fun z => _ + z) ?_
      refine ground.famFold_congr_all Nat.add 0 _ _ (fun S => ?_) _
      rw [sideOf_cons, eKey_cons, hja]
    · have he : ground.eraseFirst j (a :: l)
          = a :: ground.eraseFirst j l := by
        show (if j = a then l else a :: ground.eraseFirst j l) = _
        rw [if_neg hja]
      have hl : 0 < ground.countOf j l := by
        rw [ground.countOf_head_ne hja] at h
        exact h
      have hcons : ∀ m : List Nat,
          ground.famFold Nat.add 0
              (fun S => F (places.sideOf (a :: S)) (eKey t (a :: S)))
              (ground.sublistsOf m)
            = ground.famFold Nat.add 0
              (fun S => F (!places.sideOf S) (mkKey t a (eKey t S)))
              (ground.sublistsOf m) := fun m =>
        ground.famFold_congr_all Nat.add 0 _ _ (fun S => by
          rw [sideOf_cons, eKey_cons]) _
      have hcons2 : ∀ m : List Nat,
          ground.famFold Nat.add 0
              (fun S => F (!places.sideOf (a :: S))
                (mkKey t j (eKey t (a :: S))))
              (ground.sublistsOf m)
            = ground.famFold Nat.add 0
              (fun S => F (!(!places.sideOf S))
                (mkKey t a (mkKey t j (eKey t S))))
              (ground.sublistsOf m) := fun m =>
        ground.famFold_congr_all Nat.add 0 _ _ (fun S => by
          rw [sideOf_cons, eKey_cons,
            mkKey_comm t a j (eKey t S) (eKey_length t S)]) _
      rw [he, happ (fun S => F (places.sideOf S) (eKey t S)) l,
        happ (fun S => F (places.sideOf S) (eKey t S))
          (ground.eraseFirst j l),
        happ (fun S => F (!places.sideOf S) (mkKey t j (eKey t S)))
          (ground.eraseFirst j l),
        sublists_split t l j hl F,
        hcons l, hcons (ground.eraseFirst j l),
        hcons2 (ground.eraseFirst j l),
        sublists_split t l j hl (fun b k => F (!b) (mkKey t a k)),
        Nat.add_assoc, Nat.add_assoc,
        Nat.add_left_comm (ground.famFold Nat.add 0
          (fun S => F (!places.sideOf S) (mkKey t j (eKey t S)))
          (ground.sublistsOf (ground.eraseFirst j l)))]

/-- The cofactor split (`thm:memberchar`'s `Q_j`): the subset fold
at a normed key of the rank's order reads the withdrawn-index fold
at that key joined to the withdrawn fold at the moved key on the
flipped side. -/
theorem subsetCount_off_split (t : gentable.Table) (j : Nat)
    (hj : j < t.posFolds.length) (y : List BPair)
    (hy : y.length = t.rank) (hyn : poly.pnorm y = y) (side : Bool) :
    subsetCount t y side = subsetCountOff t j y side
      + subsetCountOff t j
          (poly.pnorm (elim.vecAdd y (posCorootV t j))) (!side) := by
  have hcount : 0 < ground.countOf j (List.range t.posFolds.length) := by
    rw [ground.countOf_range_one hj]
    exact Nat.succ_pos 0
  show ground.famFold Nat.add 0 (fun S =>
      (fun (b : Bool) (k : List BPair) =>
        if b = side then (if k = y then 1 else 0) else 0)
      (places.sideOf S) (eKey t S)) (ground.sublistsOf
        (List.range t.posFolds.length)) = _
  rw [sublists_split t (List.range t.posFolds.length) j hcount
    (fun b k => if b = side then (if k = y then 1 else 0) else 0)]
  refine congrArg (fun z => _ + z) ?_
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun S => ?_) _
  by_cases hb : places.sideOf S = !side
  · have hb' : (!places.sideOf S) = side := by
      rw [hb]
      cases side with
      | false => rfl
      | true => rfl
    rw [if_pos hb, if_pos hb']
    by_cases hk : eKey t S = poly.pnorm (elim.vecAdd y (posCorootV t j))
    · rw [if_pos hk, if_pos ((mkKey_iff t j (eKey t S) y
        (eKey_length t S) (eKey_norm t S) hy hyn).mpr hk)]
    · rw [if_neg hk, if_neg (fun hm => hk
        ((mkKey_iff t j (eKey t S) y
          (eKey_length t S) (eKey_norm t S) hy hyn).mp hm))]
  · have hb' : ¬ ((!places.sideOf S) = side) := fun hc => hb (by
      rw [← hc]
      cases places.sideOf S with
      | false => rfl
      | true => rfl)
    rw [if_neg hb, if_neg hb']

/-! The walk tier's pairing kit: the pairing truncates at its right
argument's order, so the memberwise sum, the scale and the entry
congruence read there — the length obligations are the right
argument's alone. -/

/-- The memberwise sum's order is bounded by its first summand's. -/
theorem vecAdd_lenL : ∀ u v : List BPair,
    (elim.vecAdd u v).length ≤ u.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | _ :: u, _ :: v => Nat.succ_le_succ (vecAdd_lenL u v)

/-- The memberwise sum's order is bounded by its second summand's. -/
theorem vecAdd_lenR : ∀ u v : List BPair,
    (elim.vecAdd u v).length ≤ v.length
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.le_refl _
  | _ :: u, _ :: v => Nat.succ_le_succ (vecAdd_lenR u v)

/-- The accumulating fold never grows its seed's order. -/
theorem foldVA_len (f : Nat → List BPair) : ∀ (l : List Nat)
    (acc : List BPair),
    (l.foldl (fun a i => elim.vecAdd a (f i)) acc).length ≤ acc.length
  | [], _ => Nat.le_refl _
  | i :: l, acc =>
    Nat.le_trans (foldVA_len f l (elim.vecAdd acc (f i)))
      (vecAdd_lenL acc (f i))

/-- The accumulating fold's pairing splits over its members.  The
loose-hypothesis fold reads sit beside Elim's law bundles,
disjoint in statement, the recorded lane. -/
theorem dotP_foldl (f : Nat → List BPair) (x : List BPair) :
    ∀ (l : List Nat) (acc : List BPair),
    x.length ≤ (l.foldl (fun a i => elim.vecAdd a (f i)) acc).length →
    (elim.dotP (l.foldl (fun a i => elim.vecAdd a (f i)) acc) x).oneValue
      (elim.dotP acc x
        + ground.famFold BPair.add BPair.unit
            (fun i => elim.dotP (f i) x) l)
  | [], _, _ => BPair.oneValue_symm (BPair.add_unit _)
  | i :: l, acc, hle => by
    have hstep : x.length ≤ (elim.vecAdd acc (f i)).length :=
      Nat.le_trans hle (foldVA_len f l _)
    refine BPair.oneValue_trans
      (dotP_foldl f x l (elim.vecAdd acc (f i)) hle) ?_
    show (elim.dotP (elim.vecAdd acc (f i)) x
        + ground.famFold BPair.add BPair.unit
          (fun i => elim.dotP (f i) x) l).oneValue
      (elim.dotP acc x + (elim.dotP (f i) x
        + ground.famFold BPair.add BPair.unit
          (fun i => elim.dotP (f i) x) l))
    refine BPair.oneValue_trans
      (BPair.add_congr
        (elim.dotP_vecAdd_left acc (f i) x
          (Nat.le_trans hstep (vecAdd_lenL acc (f i)))
          (Nat.le_trans hstep (vecAdd_lenR acc (f i))))
        (BPair.oneValue_refl _)) ?_
    rw [BPair.add_assoc]
    exact BPair.oneValue_refl _


/-- The memberwise sum's order reads its summands' orders alone. -/
private theorem vecAdd_lenEq : ∀ u v u' v' : List BPair,
    u.length = u'.length → v.length = v'.length →
    (elim.vecAdd u v).length = (elim.vecAdd u' v').length
  | [], _, [], _, _, _ => rfl
  | [], _, _ :: _, _, hu, _ => nomatch hu
  | _ :: _, _, [], _, hu, _ => nomatch hu
  | _ :: _, [], _ :: _, [], _, _ => rfl
  | _ :: _, [], _ :: _, _ :: _, _, hv => nomatch hv
  | _ :: _, _ :: _, _ :: _, [], _, hv => nomatch hv
  | _ :: u, _ :: v, _ :: u', _ :: v', hu, hv => by
    show (elim.vecAdd u v).length + 1 = (elim.vecAdd u' v').length + 1
    rw [vecAdd_lenEq u v u' v' (Nat.succ.inj hu) (Nat.succ.inj hv)]

/-- The simple fold sits at or below the rank's order. -/
theorem cartanFold_le (t : gentable.Table) (c : List Nat) :
    (cartanFold t c).length ≤ t.rank :=
  Nat.le_trans (foldVA_len (fun i => (ground.getAt [] t.cartan i).map (BPair.mul (BPair.ofNat (ground.getAt 0 c i)))) (List.range t.rank)
      (List.replicate t.rank BPair.unit))
    (Nat.le_of_eq (ground.length_replicate BPair.unit t.rank))

/-- The accumulating simple fold's order is the counts' own
invariant: at seeds of one order two count families fold to one
order. -/
private theorem cfEq (t : gentable.Table) (a b : List Nat) :
    ∀ (l : List Nat) (u v : List BPair), u.length = v.length →
    (l.foldl (fun acc i => elim.vecAdd acc
      ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 a i))))) u).length
      = (l.foldl (fun acc i => elim.vecAdd acc
        ((ground.getAt [] t.cartan i).map
          (BPair.mul (BPair.ofNat (ground.getAt 0 b i))))) v).length
  | [], _, _, h => h
  | i :: l, u, v, h =>
    cfEq t a b l
      (elim.vecAdd u ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 a i)))))
      (elim.vecAdd v ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 b i)))))
      (vecAdd_lenEq u _ v _ h
        ((ground.length_map _ (ground.getAt [] t.cartan i)).trans
          (ground.length_map _ (ground.getAt [] t.cartan i)).symm))

/-- Two count families fold to one order. -/
theorem cartanFold_lenEq (t : gentable.Table) (a b : List Nat) :
    (cartanFold t a).length = (cartanFold t b).length :=
  cfEq t a b (List.range t.rank) (List.replicate t.rank BPair.unit)
    (List.replicate t.rank BPair.unit) rfl

/-- A key equation frames the simple fold at the rank's order. -/
theorem cartanFold_frame (t : gentable.Table) (x : List BPair)
    (c : List Nat) (v : List BPair) (hv : v.length = t.rank)
    (hkey : poly.pnorm (elim.vecAdd x (cartanFold t c)) = v) :
    (cartanFold t c).length = t.rank := by
  have hlen : (elim.vecAdd x (cartanFold t c)).length = t.rank := by
    rw [← poly.pnorm_length, hkey]
    exact hv
  refine Nat.le_antisymm (cartanFold_le t c) ?_
  have h := vecAdd_lenR x (cartanFold t c)
  rw [hlen] at h
  exact h

/-- The accumulating simple fold's entry: the seed's own joined to
the counted rows' entries summed. -/
private theorem cfGetAt (t : gentable.Table) (c : List Nat) (j : Nat) :
    ∀ (l : List Nat) (u : List BPair),
    j < (l.foldl (fun acc i => elim.vecAdd acc
      ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 c i))))) u).length →
    (ground.getAt BPair.unit (l.foldl (fun acc i => elim.vecAdd acc
      ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 c i))))) u) j).oneValue
      (ground.getAt BPair.unit u j
        + ground.bsum (fun i => BPair.ofNat (ground.getAt 0 c i)
            * ground.getAt BPair.unit (ground.getAt [] t.cartan i) j) l)
  | [], _, _ => BPair.oneValue_symm (BPair.add_unit _)
  | i :: l, u, hj => by
    have hva : j < (elim.vecAdd u ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 c i))))).length :=
      Nat.lt_of_lt_of_le hj (foldVA_len (fun i => (ground.getAt [] t.cartan i).map (BPair.mul (BPair.ofNat (ground.getAt 0 c i)))) l _)
    have hju : j < u.length :=
      Nat.lt_of_lt_of_le hva (vecAdd_lenL _ _)
    have hjr : j < ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 c i)))).length :=
      Nat.lt_of_lt_of_le hva (vecAdd_lenR _ _)
    have hjc : j < (ground.getAt [] t.cartan i).length := by
      rw [← ground.length_map
        (BPair.mul (BPair.ofNat (ground.getAt 0 c i)))
        (ground.getAt [] t.cartan i)]
      exact hjr
    refine BPair.oneValue_trans (cfGetAt t c j l
      (elim.vecAdd u ((ground.getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (ground.getAt 0 c i))))) hj) ?_
    rw [elim.getAt_vecAdd u _ j hju hjr,
      ground.getAt_map BPair.unit BPair.unit
        (BPair.mul (BPair.ofNat (ground.getAt 0 c i)))
        (ground.getAt [] t.cartan i) j hjc]
    exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _)

/-- The simple fold's entry at a key: the counted rows' entries
summed over the rank. -/
theorem cartanFold_getAt (t : gentable.Table) (c : List Nat)
    {j : Nat} (hj : j < t.rank)
    (hcf : (cartanFold t c).length = t.rank) :
    (ground.getAt BPair.unit (cartanFold t c) j).oneValue
      (ground.bsum (fun i => BPair.ofNat (ground.getAt 0 c i)
        * ground.getAt BPair.unit (ground.getAt [] t.cartan i) j)
        (List.range t.rank)) := by
  have hlt : j < (cartanFold t c).length := by
    rw [hcf]
    exact hj
  refine BPair.oneValue_trans (cfGetAt t c j (List.range t.rank)
    (List.replicate t.rank BPair.unit) hlt) ?_
  rw [ground.getAt_replicate BPair.unit BPair.unit t.rank j hj]
  exact BPair.unit_add _

/-- The simple fold's additivity in its counts. -/
theorem cartanFold_add (t : gentable.Table) (a b : List Nat)
    (ha : (cartanFold t a).length = t.rank) :
    poly.oneValue (elim.vecAdd (cartanFold t a) (cartanFold t b))
      (cartanFold t ((List.range t.rank).map
        (fun i => ground.getAt 0 a i + ground.getAt 0 b i))) := by
  have hb : (cartanFold t b).length = t.rank :=
    (cartanFold_lenEq t b a).trans ha
  have hc : (cartanFold t ((List.range t.rank).map
      (fun i => ground.getAt 0 a i + ground.getAt 0 b i))).length
      = t.rank := (cartanFold_lenEq t _ a).trans ha
  have hab : (elim.vecAdd (cartanFold t a) (cartanFold t b)).length
      = t.rank := elim.length_vecAdd _ _ t.rank ha hb
  refine poly.oneValue_of_entries _ _ (hab.trans hc.symm) (fun j hj => ?_)
  have hjr : j < t.rank := by
    rw [hab] at hj
    exact hj
  rw [elim.getAt_vecAdd _ _ j (by rw [ha]; exact hjr)
    (by rw [hb]; exact hjr)]
  refine BPair.oneValue_trans (BPair.add_congr
    (cartanFold_getAt t a hjr ha) (cartanFold_getAt t b hjr hb)) ?_
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (cartanFold_getAt t _ hjr hc) ?_)
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun i => BPair.ofNat (ground.getAt 0 a i)
        * ground.getAt BPair.unit (ground.getAt [] t.cartan i) j
      + BPair.ofNat (ground.getAt 0 b i)
        * ground.getAt BPair.unit (ground.getAt [] t.cartan i) j)
    (List.range t.rank) (fun i hi => ?_))
    (ground.foldB_add _ _ (List.range t.rank))
  have hir : i < t.rank := ground.ltOfMem hi
  rw [ground.getAt_map 0 0
      (fun i => ground.getAt 0 a i + ground.getAt 0 b i)
      (List.range t.rank) i
      (by rw [ground.length_range]; exact hir),
    ground.getAt_range t.rank i hir]
  exact BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.ofNat_add _ _))
    (BPair.oneValue_of_eq (BPair.right_distrib _ _ _))

/-- The vacant count family's fold reads the width's unit family. -/
theorem cartanFold_null (t : gentable.Table) (c : List Nat)
    (hcf : (cartanFold t c).length = t.rank)
    (hc : ∀ i, i < t.rank → ground.getAt 0 c i = 0) :
    poly.oneValue (cartanFold t c)
      (List.replicate t.rank BPair.unit) := by
  refine poly.oneValue_of_entries _ _
    (hcf.trans (ground.length_replicate BPair.unit t.rank).symm)
    (fun j hj => ?_)
  have hjr : j < t.rank := by
    rw [hcf] at hj
    exact hj
  rw [ground.getAt_replicate BPair.unit BPair.unit t.rank j hjr]
  refine BPair.oneValue_trans (cartanFold_getAt t c hjr hcf) ?_
  refine ground.foldB_nullRange _ t.rank (fun i hi => ?_)
  rw [hc i hi]
  exact BPair.unit_mul _

/-- A vacant count family's fold absorbs: a normed key of the rank's
order joined to it reads the key back. -/
theorem foldNull_key (t : gentable.Table) (c : List Nat)
    (hcf : (cartanFold t c).length = t.rank)
    (hc : ∀ i, i < t.rank → ground.getAt 0 c i = 0)
    (v : List BPair) (hvl : v.length = t.rank)
    (hvn : poly.pnorm v = v) :
    poly.pnorm (elim.vecAdd v (cartanFold t c)) = v := by
  have e1 : poly.pnorm (elim.vecAdd v (cartanFold t c))
      = poly.pnorm (elim.vecAdd v
        (List.replicate t.rank BPair.unit)) := by
    refine poly.pnorm_congr _ _ ?_ ?_
    · rw [elim.length_vecAdd v _ t.rank hvl hcf,
        elim.length_vecAdd v _ t.rank hvl
          (ground.length_replicate BPair.unit t.rank)]
    · exact elim.polyOne_vecAdd v v _ _ (poly.oneValue_refl v)
        (cartanFold_null t c hcf hc) rfl
        (hcf.trans (ground.length_replicate BPair.unit t.rank).symm)
  rw [e1]
  refine Eq.trans (poly.pnorm_congr _ _ ?_
    (elim.vecAdd_null_right v (List.replicate t.rank BPair.unit)
      (hvl.trans (ground.length_replicate BPair.unit t.rank).symm)
      (poly.unitTail_replicate _))) hvn
  rw [elim.length_vecAdd v _ t.rank hvl
    (ground.length_replicate BPair.unit t.rank)]
  exact hvl.symm

/-- The representative list of `ρ` is `ρ`: every key sits at the
natural one, its own representative. -/
theorem pnorm_rhoV (t : gentable.Table) :
    poly.pnorm (rhoV t) = rhoV t := by
  show (List.replicate t.rank (BPair.ofNat 1)).map BPair.norm
    = List.replicate t.rank (BPair.ofNat 1)
  rw [ground.map_replicate,
    show (BPair.ofNat 1).norm = BPair.ofNat 1 from by decide +kernel]

/-- The form's `ρ`-column, the Gram against `ρ`. -/
private def gramRho (t : gentable.Table) (F : FundData) : List BPair :=
  elim.matVec F.gram (rhoV t)

private theorem gramRho_length (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) : (gramRho t F).length = t.rank :=
  (elim.matVec_length F.gram (rhoV t)).trans hshape.1

private theorem dotB_rho (t : gentable.Table) (F : FundData)
    (v : List BPair) :
    dotB F v (rhoV t) = elim.dotP v (gramRho t F) := rfl

/-- The reflecting simple's Cartan row at the rank's keys. -/
def cartRowV (t : gentable.Table) (i : Nat) : List BPair :=
  (List.range t.rank).map (fun j =>
    ground.getAt BPair.unit (ground.getAt [] t.cartan i) j)

theorem cartRowV_length (t : gentable.Table) (i : Nat) :
    (cartRowV t i).length = t.rank :=
  ground.length_mapRange _ t.rank

theorem cartRowV_getAt (t : gentable.Table) (i j : Nat)
    (hj : j < t.rank) :
    ground.getAt BPair.unit (cartRowV t i) j
      = ground.getAt BPair.unit (ground.getAt [] t.cartan i) j := by
  show ground.getAt BPair.unit ((List.range t.rank).map _) j = _
  rw [ground.getAt_map_range BPair.unit _ t.rank j, if_pos hj]

/-- The reflection's kick at a key: the swapped Cartan row scaled by
the key's own reflecting entry (`con:gentable`'s reflection join
`s_i μ = μ − μ(α_i^∨) α_i` at the coroot presentation). -/
private def refKick (t : gentable.Table) (i : Nat) (c : BPair) :
    List BPair := elim.vecScale c (poly.neg (cartRowV t i))

private theorem refKick_length (t : gentable.Table) (i : Nat)
    (c : BPair) : (refKick t i c).length = t.rank :=
  (ground.length_map _ _).trans
    ((ground.length_map _ _).trans (cartRowV_length t i))

private theorem refKick_getAt (t : gentable.Table) (i : Nat)
    (c : BPair) (j : Nat) (hj : j < t.rank) :
    ground.getAt BPair.unit (refKick t i c) j
      = c * (ground.getAt BPair.unit
          (ground.getAt [] t.cartan i) j).swap := by
  show ground.getAt BPair.unit
    (((cartRowV t i).map BPair.swap).map (fun x => c * x)) j = _
  rw [ground.map_map BPair.swap (fun x => c * x) (cartRowV t i),
    ground.getAt_map BPair.unit BPair.unit
      (fun x => c * x.swap) (cartRowV t i) j
      (by rw [cartRowV_length]; exact hj),
    cartRowV_getAt t i j hj]

/-- The accumulating fold's pairing at summands of one order. -/
private theorem dotP_foldlE (f : Nat → List BPair) (x : List BPair)
    (n : Nat) (hf : ∀ i, (f i).length = n) : ∀ (l : List Nat)
    (acc : List BPair), acc.length = n →
    (elim.dotP (l.foldl (fun a i => elim.vecAdd a (f i)) acc) x).oneValue
      (elim.dotP acc x
        + ground.famFold BPair.add BPair.unit
            (fun i => elim.dotP (f i) x) l)
  | [], _, _ => BPair.oneValue_symm (BPair.add_unit _)
  | i :: l, acc, hacc => by
    have hstep : (elim.vecAdd acc (f i)).length = n :=
      elim.length_vecAdd acc (f i) n hacc (hf i)
    refine BPair.oneValue_trans
      (dotP_foldlE f x n hf l (elim.vecAdd acc (f i)) hstep) ?_
    show (elim.dotP (elim.vecAdd acc (f i)) x
        + ground.famFold BPair.add BPair.unit
          (fun i => elim.dotP (f i) x) l).oneValue
      (elim.dotP acc x + (elim.dotP (f i) x
        + ground.famFold BPair.add BPair.unit
          (fun i => elim.dotP (f i) x) l))
    refine BPair.oneValue_trans
      (BPair.add_congr
        (elim.dotP_addE acc (f i) x (hacc.trans (hf i).symm))
        (BPair.oneValue_refl _)) ?_
    rw [BPair.add_assoc]
    exact BPair.oneValue_refl _

/-- The reflection's action at a key of the rank's order: the key
joined to its own kick, one value entry by entry
(`con:gentable`'s reflection join at the coroot presentation). -/
private theorem reflM_expand (t : gentable.Table) {i : Nat}
    (hi : i < t.rank) (y : List BPair) (hy : y.length = t.rank) :
    poly.oneValue (elim.matVec (reflM t i) y)
      (elim.vecAdd y (refKick t i (getAt BPair.unit y i))) := by
  have hK : (refKick t i (getAt BPair.unit y i)).length = t.rank :=
    refKick_length t i _
  have hlen : (elim.matVec (reflM t i) y).length
      = (elim.vecAdd y
        (refKick t i (getAt BPair.unit y i))).length := by
    rw [elim.matVec_length, reflM_length,
      elim.length_vecAdd y _ t.rank hy hK]
  have eL : elim.matVec (reflM t i) y
      = (List.range t.rank).map (fun j =>
          elim.dotN ((List.range t.rank).map (fun k =>
            BPair.add (if j == k then BPair.ofNat 1 else BPair.unit)
              (if k == i then
                (getAt BPair.unit (getAt [] t.cartan i) j).swap
              else BPair.unit))) y) := by
    show ((List.range t.rank).map _).map _ = _
    rw [ground.map_map]
  refine poly.oneValue_of_entries _ _ hlen (fun j hj => ?_)
  have hjr : j < t.rank := by
    rw [elim.matVec_length, reflM_length] at hj
    exact hj
  rw [elim.getAt_vecAdd y _ j (by rw [hy]; exact hjr)
      (by rw [hK]; exact hjr),
    refKick_getAt t i _ j hjr,
    BPair.mul_comm (getAt BPair.unit y i)
      (getAt BPair.unit (getAt [] t.cartan i) j).swap,
    eL,
    ground.getAt_map 0 BPair.unit _ (List.range t.rank) j
      (by rw [ground.length_range]; exact hjr),
    ground.getAt_range t.rank j hjr]
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans (elim.dotP_rowRange _ t.rank y hy) ?_
  rw [ground.famFold_congr_all BPair.add BPair.unit
    (fun k => BPair.add (if j == k then BPair.ofNat 1 else BPair.unit)
        (if k == i then
          (getAt BPair.unit (getAt [] t.cartan i) j).swap
        else BPair.unit)
      * getAt BPair.unit y k)
    (fun k => (if j == k then BPair.ofNat 1 else BPair.unit)
        * getAt BPair.unit y k
      + (if k == i then
          (getAt BPair.unit (getAt [] t.cartan i) j).swap
        else BPair.unit) * getAt BPair.unit y k)
    (fun k => BPair.right_distrib _ _ _) (List.range t.rank)]
  refine BPair.oneValue_trans (famFold_bsplit _ _ (List.range t.rank)) ?_
  refine BPair.add_congr ?_ ?_
  · refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => if k == j then getAt BPair.unit y j
          else BPair.unit) (List.range t.rank) (fun k _ => ?_))
      (ground.foldB_pickBeq j (getAt BPair.unit y j) (List.range t.rank)
        (ground.countOf_range_one hjr))
    by_cases hkj : k = j
    · rw [hkj, if_pos (ground.eqBeqOf rfl), if_pos (ground.eqBeqOf rfl),
        BPair.mul_comm]
      exact BPair.mul_ofNat_one _
    · rw [if_neg (fun ht : (j == k) = true =>
          hkj (ground.beqEqOf ht).symm),
        if_neg (fun ht : (k == j) = true => hkj (ground.beqEqOf ht))]
      exact BPair.unit_mul _
  · refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun k => if k == i then
          (getAt BPair.unit (getAt [] t.cartan i) j).swap
            * getAt BPair.unit y i
          else BPair.unit) (List.range t.rank) (fun k _ => ?_))
      (ground.foldB_pickBeq i ((getAt BPair.unit (getAt [] t.cartan i) j).swap
          * getAt BPair.unit y i) (List.range t.rank)
        (ground.countOf_range_one hi))
    by_cases hki : k = i
    · rw [hki, if_pos (ground.eqBeqOf rfl), if_pos (ground.eqBeqOf rfl)]
      exact BPair.oneValue_refl _
    · rw [if_neg (fun ht : (k == i) = true => hki (ground.beqEqOf ht)),
        if_neg (fun ht : (k == i) = true => hki (ground.beqEqOf ht))]
      exact BPair.unit_mul _

/-- The simple's coroot vector reads the reflecting Cartan row at
every key. -/
private theorem coroot_cartRow (t : gentable.Table) (F : FundData)
    {i : Nat} (hi : i < t.rank) (hsp : simplePosRead t F) :
    poly.oneValue (posCorootV t (getAt 0 F.simplePos i))
      (cartRowV t i) :=
  poly.oneValue_map _ _ (List.range t.rank) (fun j _ => by
    rw [hsp i hi]
    exact gentable.corootAt_oneHot t i j hi)

/-- The reflection's rise (`thm:assembly`'s walk: the raised key's
root-fold dot the key's own joined to the pair's margin at the
letter's positive dot). -/
private theorem dotB_rise (t : gentable.Table) (F : FundData)
    (hsp : simplePosRead t F) (i : Nat) (hi : i < t.rank)
    (y : List BPair) (hy : y.length = t.rank) :
    (dotB F (reflAt t i y) (rhoV t)).oneValue
      (BPair.add (dotB F y (rhoV t))
        (BPair.mul (getAt BPair.unit y i).swap
          (dotB F (posCorootV t (getAt 0 F.simplePos i))
            (rhoV t)))) := by
  show (dotB F (reflAt t i y) (rhoV t)).oneValue
    (dotB F y (rhoV t)
      + (getAt BPair.unit y i).swap
        * dotB F (posCorootV t (getAt 0 F.simplePos i)) (rhoV t))
  rw [dotB_rho, dotB_rho, dotB_rho,
    BPair.swap_mul (getAt BPair.unit y i),
    ← BPair.mul_swap (getAt BPair.unit y i)]
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _ (elim.matVec (reflM t i) y) (gramRho t F)
      (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _ _ (gramRho t F) (reflM_expand t hi y hy)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_addE y (refKick t i (getAt BPair.unit y i)) (gramRho t F)
      (hy.trans (refKick_length t i _).symm)) ?_
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans
    (elim.dotP_scaleL (getAt BPair.unit y i) (poly.neg (cartRowV t i))
      (gramRho t F)) ?_
  rw [elim.dotP_swap_left]
  refine BPair.mul_congr (BPair.oneValue_refl _) ?_
  exact ground.swap_congr
    (BPair.oneValue_symm
      (elim.dotP_oneValue_left _ _ (gramRho t F) (coroot_cartRow t F hi hsp)))


/-! The root fold's coroot read as a derived fact
(`con:sertables`' first shared read, `(2ρ)(α_i^∨) = 2`): the
positive list's coroot vectors sum to `2ρ`'s own coroot list `T`,
and a letter reads `s_i T` two ways — the reflection join's kick at
`T`'s own pair at the letter, and the image clauses memberwise, the
simple's position crossing to its balance partner with every
further key carried along the permutation.  The two readings share
the permuted remainder off the simple's position, which cancels,
and what is left is the vector identity: the member at the
permutation's image `q` of the simple's position is
`(T_i - 1) α_i`.  At `q` the simple's own position the identity
reads `T_i = 2` at the cancelled positive `ρ`-dot; off it the
involution returns at `q` — the permutation datum carries `q` back
to the simple's position, so that member's image clause reads `α_i`
itself — and the returned reading forces the multiple negative,
whose `ρ`-dot joins the simple's to the sum's unit against two
strictly positive dots.  So `gentable.rhoRead` is its co-binders'
own consequence and binds nowhere. -/

/-- The balanced read's own shift: a datum joined to a swapped
product against a swapped datum reads the two data joined against
the product. -/
private theorem dotBalance {a b X : BPair}
    (h : (a + X.swap).oneValue b.swap) : (a + b).oneValue X := by
  refine ground.oneOfUnit ?_
  have h' := ground.unitOfOne h
  rw [BPair.swap_swap, BPair.add_assoc, BPair.add_comm X.swap b,
    ← BPair.add_assoc] at h'
  exact h'

/-- A shared summand cancels from a memberwise one-value read, at
matched orders. -/
private theorem vecCancelR : ∀ x y E : List BPair,
    x.length = E.length → y.length = E.length →
    poly.oneValue (elim.vecAdd x E) (elim.vecAdd y E) →
    poly.oneValue x y
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, [], _, hy, _ => Nat.noConfusion hy
  | _ :: _, [], [], hx, _, _ => Nat.noConfusion hx
  | _ :: _, _ :: _, [], hx, _, _ => Nat.noConfusion hx
  | [], _ :: _, _ :: _, hx, _, _ => Nat.noConfusion hx
  | _ :: _, [], _ :: _, _, hy, _ => Nat.noConfusion hy
  | a :: x, b :: y, c :: E, hx, hy, h => by
    have h' : poly.oneValue ((a + c) :: elim.vecAdd x E)
      ((b + c) :: elim.vecAdd y E) := h
    exact ⟨ground.BPair.add_cancel h'.1,
      vecCancelR x y E (Nat.succ.inj hx) (Nat.succ.inj hy) h'.2⟩

/-- The memberwise sum's fold reads entrywise: the key's entry is
the members' entries' own fold. -/
private theorem fvGetAt (t : gentable.Table) (f : Nat → List BPair)
    (hf : ∀ j, (f j).length = t.rank) {i : Nat} (hi : i < t.rank) :
    ∀ l : List Nat,
    (ground.getAt BPair.unit (ground.famFold elim.vecAdd
      (List.replicate t.rank BPair.unit) f l) i).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun j => ground.getAt BPair.unit (f j) i) l)
  | [] => BPair.oneValue_of_eq
      (ground.getAt_replicate BPair.unit BPair.unit t.rank i hi)
  | a :: l => by
    show (ground.getAt BPair.unit (elim.vecAdd (f a)
      (ground.famFold elim.vecAdd
        (List.replicate t.rank BPair.unit) f l)) i).oneValue _
    rw [elim.getAt_vecAdd (f a) _ i (by rw [hf a]; exact hi)
      (by rw [fvLen t f hf l]; exact hi)]
    exact BPair.add_congr (BPair.oneValue_refl _) (fvGetAt t f hf hi l)

/-- A positive member's coroot vector reads its fold's own coroot
pair at every key. -/
private theorem posCorootV_getAt (t : gentable.Table) (j : Nat)
    {i : Nat} (hi : i < t.rank) :
    ground.getAt BPair.unit (posCorootV t j) i
      = gentable.corootAt t (ground.getAt [] t.posFolds j) i := by
  show ground.getAt BPair.unit ((List.range t.rank).map
    (gentable.corootAt t (ground.getAt [] t.posFolds j))) i = _
  rw [ground.getAt_map_range BPair.unit _ t.rank i, if_pos hi]

/-- The positive list's coroot sum reads the root fold's own coroot
pair at every key (`con:sertables`' fold over the positive
list). -/
private theorem sumT_entry (t : gentable.Table) {i : Nat}
    (hi : i < t.rank) :
    (ground.getAt BPair.unit
        (vsum t (List.range t.posFolds.length)) i).oneValue
      (gentable.rho2Coroot t i) := by
  refine BPair.oneValue_trans
    (fvGetAt t (posCorootV t) (posCorootV_length t) hi
      (List.range t.posFolds.length)) ?_
  rw [ground.famFold_congr_all BPair.add BPair.unit
    (fun j => ground.getAt BPair.unit (posCorootV t j) i)
    (fun j => gentable.corootAt t (ground.getAt [] t.posFolds j) i)
    (fun j => posCorootV_getAt t j hi) (List.range t.posFolds.length)]
  refine BPair.oneValue_symm ?_
  show (BPair.sum (t.posFolds.map
    (fun f => gentable.corootAt t f i))).oneValue _
  refine BPair.oneValue_trans
    (ground.BPair.sum_map (fun f => gentable.corootAt t f i)
      t.posFolds) ?_
  rw [← ground.famFold_getAt BPair.add BPair.unit
    (fun f => gentable.corootAt t f i) ([] : List Nat) t.posFolds
    t.posFolds.length rfl]
  exact BPair.oneValue_refl _

/-- The letter's images at the positive list's keys: the simple's
own position crosses to its balance partner, every further key to
the permutation's image (`con:sertables`' permutation read). -/
private def imgV (t : gentable.Table) (F : FundData) (i j : Nat) :
    List BPair :=
  if j == ground.getAt 0 F.simplePos i then
    poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
  else posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i) j)

private theorem imgV_len (t : gentable.Table) (F : FundData)
    (i j : Nat) : (imgV t F i j).length = t.rank := by
  show (if j == ground.getAt 0 F.simplePos i then
      poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
    else posCorootV t
      (ground.getAt 0 (ground.getAt [] F.perms i) j)).length = t.rank
  by_cases h : (j == ground.getAt 0 F.simplePos i) = true
  · rw [if_pos h, poly.length_neg]
    exact posCorootV_length t _
  · rw [if_neg h]
    exact posCorootV_length t _

/-- The permuted members off the simple's position, the remainder
the two readings of `s_i T` share. -/
private def permRest (t : gentable.Table) (F : FundData) (i : Nat) :
    List BPair :=
  ground.famFold elim.vecAdd (List.replicate t.rank BPair.unit)
    (fun j => posCorootV t
      (ground.getAt 0 (ground.getAt [] F.perms i) j))
    (ground.eraseFirst (ground.getAt 0 F.simplePos i)
      (List.range t.posFolds.length))

private theorem permRest_len (t : gentable.Table) (F : FundData)
    (i : Nat) : (permRest t F i).length = t.rank :=
  fvLen t _ (fun _ => posCorootV_length t _) _

/-- The root fold's coroot reads `(2ρ)(α_i^∨) = 2`, derived: the
shape, the simple positions, the permutation datum's involution,
the reflections' image clauses and the `ρ`-dots' positivity force
the read, so `gentable.rhoRead` binds nowhere
(`con:sertables`' first shared read at its own derivation). -/
theorem rhoRead_derived (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hpsq : permSquareRead t F) (hpi : permImageRead t F)
    (hrd : rhoDotRead t F) : gentable.rhoRead t := by
  show ((List.range t.rank).all (fun j =>
    if (gentable.rho2Coroot t j).oneValue (BPair.ofNat 2)
    then true else false)) = true
  refine ground.all_range_intro t.rank (fun i hi => ?_)
  show (if (gentable.rho2Coroot t i).oneValue (BPair.ofNat 2)
    then true else false) = true
  refine if_pos ?_
  have hsin : ground.getAt 0 F.simplePos i < t.posFolds.length :=
    simplePos_lt t F hshape hi
  have hTlen : (vsum t (List.range t.posFolds.length)).length
      = t.rank := vsum_length t _
  -- the sum read along the permutation, split at the simple's position
  have hreind : vsum t (List.range t.posFolds.length)
      = ground.famFold elim.vecAdd (List.replicate t.rank BPair.unit)
        (fun x => posCorootV t
          (ground.getAt 0 (ground.getAt [] F.perms i) x))
        (List.range t.posFolds.length) := by
    show ground.famFold elim.vecAdd (List.replicate t.rank BPair.unit)
      (posCorootV t) (List.range t.posFolds.length) = _
    exact ground.famFold_reindex elim.vecAdd
      (List.replicate t.rank BPair.unit) elim.vecAdd_comm
      elim.vecAdd_assoc (posCorootV t)
      (g := fun x => ground.getAt 0 (ground.getAt [] F.perms i) x)
      (h := fun x => ground.getAt 0 (ground.getAt [] F.perms i) x)
      (fun x _ => ground.distinctList_all (ground.distinctList_range t.posFolds.length) x)
      (fun x hx => hpsq i hi x (ground.ltOfMem hx))
      (fun x hx => hpsq i hi x (ground.ltOfMem hx))
      (fun x hx => by
        rw [ground.countOf_range_one
          (perm_lt t F hshape hi (ground.ltOfMem hx))]
        exact Nat.succ_pos 0)
      (fun x hx => by
        rw [ground.countOf_range_one
          (perm_lt t F hshape hi (ground.ltOfMem hx))]
        exact Nat.succ_pos 0)
  have hTsplit : vsum t (List.range t.posFolds.length)
      = elim.vecAdd (posCorootV t (ground.getAt 0
          (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i))) (permRest t F i) := by
    rw [hreind]
    exact ground.famFold_eraseFirst elim.vecAdd
      (List.replicate t.rank BPair.unit) elim.vecAdd_comm
      elim.vecAdd_assoc _ (List.range t.posFolds.length)
      (ground.getAt 0 F.simplePos i)
      (by rw [ground.countOf_range_one hsin]; exact Nat.succ_pos 0)
  -- the letter's image read memberwise, split at the same position
  have hR : poly.oneValue
      (elim.matVec (reflM t i)
        (vsum t (List.range t.posFolds.length)))
      (elim.vecAdd
        (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i)))
        (permRest t F i)) := by
    show poly.oneValue (elim.matVec (reflM t i)
      (ground.famFold elim.vecAdd (List.replicate t.rank BPair.unit)
        (posCorootV t) (List.range t.posFolds.length))) _
    refine poly.oneValue_trans
      (mvFold t i (posCorootV t) (posCorootV_length t)
        (List.range t.posFolds.length)) ?_
    refine poly.oneValue_trans
      (fvCongrMem t
        (fun j => elim.matVec (reflM t i) (posCorootV t j))
        (imgV t F i)
        (fun _ => (elim.matVec_length _ _).trans (reflM_length t i))
        (imgV_len t F i) (List.range t.posFolds.length)
        (fun j hj => ?_)) ?_
    · show poly.oneValue (elim.matVec (reflM t i) (posCorootV t j))
        (if j == ground.getAt 0 F.simplePos i then
          poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
        else posCorootV t
          (ground.getAt 0 (ground.getAt [] F.perms i) j))
      by_cases hjp : j = ground.getAt 0 F.simplePos i
      · rw [if_pos (ground.eqBeqOf hjp), hjp]
        exact imgSi t F hi hpi
      · rw [if_neg (fun ht : (j == ground.getAt 0 F.simplePos i) = true
          => hjp (ground.beqEqOf ht))]
        exact imgOff t F hi hpi (ground.ltOfMem hj) hjp
    · rw [ground.famFold_eraseFirst elim.vecAdd
        (List.replicate t.rank BPair.unit) elim.vecAdd_comm
        elim.vecAdd_assoc (imgV t F i) (List.range t.posFolds.length)
        (ground.getAt 0 F.simplePos i)
        (by rw [ground.countOf_range_one hsin]; exact Nat.succ_pos 0)]
      refine elim.vecAdd_congr2 _ _ _ _ ?_ ?_ ?_ ?_
      · rw [imgV_len t F i, poly.length_neg, posCorootV_length]
      · rw [fvLen t (imgV t F i) (imgV_len t F i), permRest_len]
      · show poly.oneValue (if ground.getAt 0 F.simplePos i
            == ground.getAt 0 F.simplePos i then
            poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
          else posCorootV t (ground.getAt 0
            (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i))) _
        rw [if_pos (ground.eqBeqOf rfl)]
        exact poly.oneValue_refl _
      · refine poly.oneValue_trans
          (fvCongrMem t (imgV t F i)
            (fun j => posCorootV t
              (ground.getAt 0 (ground.getAt [] F.perms i) j))
            (imgV_len t F i) (fun _ => posCorootV_length t _)
            (ground.eraseFirst (ground.getAt 0 F.simplePos i)
              (List.range t.posFolds.length)) (fun j hj => ?_)) ?_
        · obtain ⟨_, hjsi⟩ := eraseFirst_range_count hj
          show poly.oneValue (if j == ground.getAt 0 F.simplePos i then
              poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))
            else posCorootV t
              (ground.getAt 0 (ground.getAt [] F.perms i) j)) _
          rw [if_neg (fun ht : (j == ground.getAt 0 F.simplePos i) = true
            => hjsi (ground.beqEqOf ht))]
          exact poly.oneValue_refl _
        · exact poly.oneValue_refl _
  -- the two readings meet, the shared remainder cancels
  have hcomb : poly.oneValue
      (elim.vecAdd (vsum t (List.range t.posFolds.length))
        (refKick t i (ground.getAt BPair.unit
          (vsum t (List.range t.posFolds.length)) i)))
      (elim.vecAdd
        (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i)))
        (permRest t F i)) :=
    poly.oneValue_trans
      (poly.oneValue_symm (reflM_expand t hi
        (vsum t (List.range t.posFolds.length)) hTlen)) hR
  have hEq : elim.vecAdd (elim.vecAdd
        (posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i)))
        (refKick t i (ground.getAt BPair.unit
          (vsum t (List.range t.posFolds.length)) i)))
      (permRest t F i)
      = elim.vecAdd (vsum t (List.range t.posFolds.length))
        (refKick t i (ground.getAt BPair.unit
          (vsum t (List.range t.posFolds.length)) i)) := by
    rw [elim.vecAdd_assoc,
      elim.vecAdd_comm (refKick t i (ground.getAt BPair.unit
        (vsum t (List.range t.posFolds.length)) i)) (permRest t F i),
      ← elim.vecAdd_assoc, ← hTsplit]
  have hV : poly.oneValue
      (elim.vecAdd
        (posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i)))
        (refKick t i (ground.getAt BPair.unit
          (vsum t (List.range t.posFolds.length)) i)))
      (poly.neg (posCorootV t (ground.getAt 0 F.simplePos i))) := by
    refine vecCancelR _ _ (permRest t F i) ?_ ?_ ?_
    · rw [vecAdd_length ((posCorootV_length t _).trans
        (refKick_length t i _).symm), posCorootV_length, permRest_len]
    · rw [poly.length_neg, posCorootV_length, permRest_len]
    · rw [hEq]
      exact hcomb
  -- the vector identity dotted against ρ
  have hdp : BPair.unit < elim.dotP
      (posCorootV t (ground.getAt 0 F.simplePos i)) (gramRho t F) :=
    hrd _ hsin
  have hoff : ¬ (elim.dotP (posCorootV t
      (ground.getAt 0 F.simplePos i)) (gramRho t F)).oneValue
      BPair.unit := fun hc => ground.leB_not_lt (Or.inl hc) hdp
  have hkick : (elim.dotP (refKick t i (ground.getAt BPair.unit
        (vsum t (List.range t.posFolds.length)) i))
      (gramRho t F)).oneValue
      ((ground.getAt BPair.unit
          (vsum t (List.range t.posFolds.length)) i)
        * (elim.dotP (posCorootV t
            (ground.getAt 0 F.simplePos i)) (gramRho t F)).swap) := by
    refine BPair.oneValue_trans
      (elim.dotP_scaleL (ground.getAt BPair.unit
        (vsum t (List.range t.posFolds.length)) i)
        (poly.neg (cartRowV t i)) (gramRho t F)) ?_
    rw [elim.dotP_swap_left]
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    exact ground.swap_congr (BPair.oneValue_symm
      (elim.dotP_oneValue_left _ _ (gramRho t F)
        (coroot_cartRow t F hi hsp)))
  have hS : ((elim.dotP (posCorootV t (ground.getAt 0
        (ground.getAt [] F.perms i) (ground.getAt 0 F.simplePos i)))
        (gramRho t F))
      + ((ground.getAt BPair.unit
            (vsum t (List.range t.posFolds.length)) i)
          * elim.dotP (posCorootV t
            (ground.getAt 0 F.simplePos i)) (gramRho t F)).swap).oneValue
      ((elim.dotP (posCorootV t (ground.getAt 0 F.simplePos i))
        (gramRho t F)).swap) := by
    have h0 : (elim.dotP (elim.vecAdd
          (posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i)))
          (refKick t i (ground.getAt BPair.unit
            (vsum t (List.range t.posFolds.length)) i)))
        (gramRho t F)).oneValue
        ((elim.dotP (posCorootV t (ground.getAt 0 F.simplePos i))
          (gramRho t F)).swap) := by
      refine BPair.oneValue_trans
        (elim.dotP_oneValue_left _ _ (gramRho t F) hV) ?_
      rw [elim.dotP_swap_left]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans ?_ h0
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (elim.dotP_addE _ _ (gramRho t F)
        ((posCorootV_length t _).trans (refKick_length t i _).symm)) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans hkick ?_
    rw [BPair.mul_swap]
    exact BPair.oneValue_refl _
  have hQ : ((elim.dotP (posCorootV t (ground.getAt 0
        (ground.getAt [] F.perms i) (ground.getAt 0 F.simplePos i)))
        (gramRho t F))
      + elim.dotP (posCorootV t
        (ground.getAt 0 F.simplePos i)) (gramRho t F)).oneValue
      ((ground.getAt BPair.unit
          (vsum t (List.range t.posFolds.length)) i)
        * elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F)) :=
    dotBalance hS
  by_cases hqp : ground.getAt 0 (ground.getAt [] F.perms i)
      (ground.getAt 0 F.simplePos i) = ground.getAt 0 F.simplePos i
  · -- the permutation keeps the simple's position: the pair reads two
    rw [hqp] at hQ
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (sumT_entry t hi)) ?_
    refine ground.mulCancel hoff ?_
    rw [BPair.mul_comm (elim.dotP (posCorootV t
        (ground.getAt 0 F.simplePos i)) (gramRho t F))
      (ground.getAt BPair.unit
        (vsum t (List.range t.posFolds.length)) i)]
    refine BPair.oneValue_trans (BPair.oneValue_symm hQ) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (BPair.ofNat_succ 1)) ?_
    rw [BPair.left_distrib]
    exact BPair.add_congr (BPair.mul_ofNat_one _) (BPair.mul_ofNat_one _)
  · -- the involution returns at the image: the two ρ-dots cancel
    exfalso
    have hqlt : ground.getAt 0 (ground.getAt [] F.perms i)
        (ground.getAt 0 F.simplePos i) < t.posFolds.length :=
      perm_lt t F hshape hi hsin
    have hdq : BPair.unit < elim.dotP (posCorootV t
        (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i))) (gramRho t F) :=
      hrd _ hqlt
    have hrefQ : reflAt t i (posCorootV t (ground.getAt 0
        (ground.getAt [] F.perms i) (ground.getAt 0 F.simplePos i)))
        = poly.pnorm (posCorootV t
          (ground.getAt 0 F.simplePos i)) := by
      have h1 := (hpi i hi).1 _ hqlt hqp
      rw [hpsq i hi (ground.getAt 0 F.simplePos i) hsin] at h1
      exact h1
    have hC : ((elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F))
        + elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F)).oneValue
        ((ground.getAt BPair.unit (posCorootV t
            (ground.getAt 0 F.simplePos i)) i)
          * elim.dotP (posCorootV t
            (ground.getAt 0 F.simplePos i)) (gramRho t F)) := by
      refine dotBalance (b := elim.dotP (posCorootV t
        (ground.getAt 0 F.simplePos i)) (gramRho t F)) ?_
      have h0 : (dotB F (reflAt t i (posCorootV t
            (ground.getAt 0 F.simplePos i))) (rhoV t)).oneValue
          ((elim.dotP (posCorootV t (ground.getAt 0 F.simplePos i))
              (gramRho t F))
            + (ground.getAt BPair.unit (posCorootV t
                (ground.getAt 0 F.simplePos i)) i).swap
              * elim.dotP (posCorootV t
                (ground.getAt 0 F.simplePos i)) (gramRho t F)) :=
        dotB_rise t F hsp i hi
          (posCorootV t (ground.getAt 0 F.simplePos i))
          (posCorootV_length t _)
      rw [(hpi i hi).2, BPair.swap_mul] at h0
      have hlhs : (elim.dotP (poly.pnorm (poly.neg (posCorootV t
          (ground.getAt 0 F.simplePos i)))) (gramRho t F)).oneValue
          ((elim.dotP (posCorootV t (ground.getAt 0 F.simplePos i))
            (gramRho t F)).swap) := by
        refine BPair.oneValue_trans
          (elim.dotP_oneValue_left _ _ (gramRho t F)
            (poly.pnorm_oneValue _)) ?_
        rw [elim.dotP_swap_left]
        exact BPair.oneValue_refl _
      exact BPair.oneValue_trans (BPair.oneValue_symm h0) hlhs
    have hR1 : (elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F)).oneValue
        ((elim.dotP (posCorootV t (ground.getAt 0
            (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i))) (gramRho t F))
          + ((ground.getAt BPair.unit (posCorootV t
              (ground.getAt 0 (ground.getAt [] F.perms i)
                (ground.getAt 0 F.simplePos i))) i)
            * elim.dotP (posCorootV t
              (ground.getAt 0 F.simplePos i))
              (gramRho t F)).swap) := by
      have h0 : (dotB F (reflAt t i (posCorootV t (ground.getAt 0
            (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i)))) (rhoV t)).oneValue
          ((elim.dotP (posCorootV t (ground.getAt 0
              (ground.getAt [] F.perms i)
              (ground.getAt 0 F.simplePos i))) (gramRho t F))
            + (ground.getAt BPair.unit (posCorootV t (ground.getAt 0
                (ground.getAt [] F.perms i)
                (ground.getAt 0 F.simplePos i))) i).swap
              * elim.dotP (posCorootV t
                (ground.getAt 0 F.simplePos i)) (gramRho t F)) :=
        dotB_rise t F hsp i hi
          (posCorootV t (ground.getAt 0 (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i)))
          (posCorootV_length t _)
      rw [hrefQ, BPair.swap_mul] at h0
      refine BPair.oneValue_trans ?_ h0
      exact BPair.oneValue_symm
        (elim.dotP_oneValue_left _ _ (gramRho t F) (poly.pnorm_oneValue _))
    have hAqi : ((ground.getAt BPair.unit (posCorootV t
          (ground.getAt 0 (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i))) i)
        + ground.getAt BPair.unit (posCorootV t
          (ground.getAt 0 F.simplePos i)) i).oneValue
        ((ground.getAt BPair.unit
            (vsum t (List.range t.posFolds.length)) i)
          * ground.getAt BPair.unit (posCorootV t
            (ground.getAt 0 F.simplePos i)) i) := by
      refine dotBalance ?_
      have h0 := poly.oneValue_getAt i hV
      rw [elim.getAt_vecAdd _ _ i
          (by rw [posCorootV_length]; exact hi)
          (by rw [refKick_length]; exact hi),
        refKick_getAt t i _ i hi,
        show ground.getAt BPair.unit (poly.neg (posCorootV t
            (ground.getAt 0 F.simplePos i))) i
          = (ground.getAt BPair.unit (posCorootV t
            (ground.getAt 0 F.simplePos i)) i).swap from
          ground.getAt_map BPair.unit BPair.unit BPair.swap
            (posCorootV t (ground.getAt 0 F.simplePos i)) i
            (by rw [posCorootV_length]; exact hi)] at h0
      refine BPair.oneValue_trans ?_ h0
      refine BPair.add_congr (BPair.oneValue_refl _) ?_
      rw [← BPair.mul_swap]
      refine BPair.mul_congr (BPair.oneValue_refl _)
        (ground.swap_congr ?_)
      rw [posCorootV_getAt t (ground.getAt 0 F.simplePos i) hi, hsp i hi]
      exact gentable.corootAt_oneHot t i i hi
    have hAqdp : ((ground.getAt BPair.unit (posCorootV t
          (ground.getAt 0 (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i))) i)
        * elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F)).oneValue
        ((elim.dotP (posCorootV t (ground.getAt 0
            (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i))) (gramRho t F))
          + elim.dotP (posCorootV t (ground.getAt 0
            (ground.getAt [] F.perms i)
            (ground.getAt 0 F.simplePos i))) (gramRho t F)) := by
      refine ground.BPair.add_cancel (c := elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F)
        + elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) hC) ?_
      rw [← BPair.right_distrib]
      refine BPair.oneValue_trans (BPair.mul_congr_left hAqi) ?_
      rw [BPair.mul_assoc]
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm hC)) ?_
      rw [BPair.left_distrib]
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_symm hQ)
          (BPair.oneValue_symm hQ)) ?_
      rw [BPair.add_add_comm]
      exact BPair.oneValue_refl _
    have hStep : ((elim.dotP (posCorootV t (ground.getAt 0
          (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i))) (gramRho t F))
        + (elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i))
          (gramRho t F)).swap).oneValue
        ((ground.getAt BPair.unit (posCorootV t
            (ground.getAt 0 (ground.getAt [] F.perms i)
              (ground.getAt 0 F.simplePos i))) i)
          * elim.dotP (posCorootV t
            (ground.getAt 0 F.simplePos i)) (gramRho t F)) :=
      dotBalance (b := (elim.dotP (posCorootV t
        (ground.getAt 0 F.simplePos i)) (gramRho t F)).swap)
        (BPair.oneValue_symm hR1)
    have hRes : (elim.dotP (posCorootV t
        (ground.getAt 0 F.simplePos i)) (gramRho t F)).swap.oneValue
        (elim.dotP (posCorootV t (ground.getAt 0
          (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i))) (gramRho t F)) := by
      refine ground.BPair.add_cancel (c := elim.dotP (posCorootV t
        (ground.getAt 0 (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i))) (gramRho t F)) ?_
      rw [BPair.add_comm]
      exact BPair.oneValue_trans hStep hAqdp
    have hfin : ((elim.dotP (posCorootV t
          (ground.getAt 0 F.simplePos i)) (gramRho t F))
        + elim.dotP (posCorootV t (ground.getAt 0
          (ground.getAt [] F.perms i)
          (ground.getAt 0 F.simplePos i)))
          (gramRho t F)).oneValue BPair.unit := by
      have h0 := ground.unitOfOne hRes
      rw [BPair.swap_add] at h0
      exact ground.swap_congr h0
    exact ground.leB_not_lt (ground.leB_refl BPair.unit)
      (BPair.lt_congr (BPair.add_unit BPair.unit) hfin
        (ground.ltB_add hdp (Or.inr hdq)))

/-- The fixed key (`thm:assembly`'s walk, pin (a)): a dominant key
at a simple coroot pair the unit is the letter's own fix,
`s_i μ = μ`. -/
theorem reflAt_fix (t : gentable.Table) (i : Nat)
    (hi : i < t.rank) (y : List BPair) (hy : y.length = t.rank)
    (hny : poly.pnorm y = y)
    (hu : (getAt BPair.unit y i).oneValue BPair.unit) :
    reflAt t i y = y := by
  have hK : (refKick t i (getAt BPair.unit y i)).length = t.rank :=
    refKick_length t i _
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  have hunit : poly.oneValue (refKick t i (getAt BPair.unit y i))
      (List.replicate t.rank BPair.unit) := by
    refine poly.oneValue_of_entries _ _ (hK.trans hz.symm) (fun j hj => ?_)
    have hjr : j < t.rank := by
      rw [hK] at hj
      exact hj
    rw [refKick_getAt t i _ j hjr,
      ground.getAt_replicate BPair.unit BPair.unit t.rank j hjr]
    exact BPair.oneValue_trans (BPair.mul_congr_left hu)
      (BPair.unit_mul _)
  show poly.pnorm (elim.matVec (reflM t i) y) = y
  refine Eq.trans (poly.pnorm_congr _ y ?_ ?_) hny
  · rw [elim.matVec_length, reflM_length, hy]
  · refine poly.oneValue_trans (reflM_expand t hi y hy) ?_
    exact poly.oneValue_trans
      (elim.vecAdd_congr2 _ _ _ _ rfl (hK.trans hz.symm)
        (poly.oneValue_refl y) hunit)
      (elim.vecAdd_null_right y (List.replicate t.rank BPair.unit)
        (by rw [ground.length_replicate]; exact hy)
        (poly.unitTail_replicate t.rank))

/-- The shifted key (`thm:assembly`'s walk at `prop:row`'s tie): a
key reading the natural one at a letter's own coordinate moves by
the letter's Cartan row, the reflection join `s_i μ = μ − μ(α_i^∨)
α_i` at the coroot pair one. -/
theorem reflAt_shift (t : gentable.Table) (i : Nat)
    (hi : i < t.rank) (y : List BPair) (hy : y.length = t.rank)
    (hone : (getAt BPair.unit y i).oneValue (BPair.ofNat 1)) :
    reflAt t i y
      = poly.pnorm (elim.vecAdd y (poly.neg (cartRowV t i))) := by
  have hK : (refKick t i (getAt BPair.unit y i)).length = t.rank :=
    refKick_length t i _
  have hN : (poly.neg (cartRowV t i)).length = t.rank :=
    (ground.length_map _ _).trans (cartRowV_length t i)
  have hkick : poly.oneValue (refKick t i (getAt BPair.unit y i))
      (poly.neg (cartRowV t i)) := by
    refine poly.oneValue_of_entries _ _ (hK.trans hN.symm) (fun j hj => ?_)
    have hjr : j < t.rank := by
      rw [hK] at hj
      exact hj
    rw [refKick_getAt t i _ j hjr,
      show poly.neg (cartRowV t i) = (cartRowV t i).map BPair.swap
        from rfl,
      ground.getAt_map BPair.unit BPair.unit BPair.swap _ j
        (by rw [cartRowV_length t i]; exact hjr),
      cartRowV_getAt t i j hjr]
    refine BPair.oneValue_trans (BPair.mul_congr_left hone) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofNat 1) _)) ?_
    exact BPair.mul_ofNat_one _
  show poly.pnorm (elim.matVec (reflM t i) y) = _
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [elim.matVec_length, reflM_length,
      elim.length_vecAdd y _ t.rank hy hN]
  · exact poly.oneValue_trans (reflM_expand t hi y hy)
      (elim.vecAdd_congr2 _ _ _ _ rfl (hK.trans hN.symm) (poly.oneValue_refl y) hkick)

/-! The domination displays (`thm:assembly`'s support tier): an
occupied key's dot joins its family's or its witness fold's positive
dots to `ρ`'s own. -/

/-- The subset key's dot: the family's dots join the key's back to
`ρ`'s (`thm:assembly`'s subset fold, `e_S + Σ_S α = ρ`). -/
private theorem dotB_eKey (t : gentable.Table) (F : FundData)
    (S : List Nat) :
    (BPair.add (dotB F (eKey t S) (rhoV t))
      (ground.famFold BPair.add BPair.unit
        (fun j => dotB F (posCorootV t j) (rhoV t)) S)).oneValue
      (dotB F (rhoV t) (rhoV t)) := by
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hFS : (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
      (List.replicate t.rank BPair.unit)).length = t.rank :=
    foldl_length t S _ hz
  have hnFS : (poly.neg (S.foldl
      (fun acc j => elim.vecAdd acc (posCorootV t j))
      (List.replicate t.rank BPair.unit))).length = t.rank := by
    rw [poly.length_neg]
    exact hFS
  show (elim.dotP (eKey t S) (gramRho t F)
    + ground.famFold BPair.add BPair.unit
        (fun j => elim.dotP (posCorootV t j) (gramRho t F)) S).oneValue
    (elim.dotP (rhoV t) (gramRho t F))
  have hfold : (elim.dotP
      (S.foldl (fun acc j => elim.vecAdd acc (posCorootV t j))
        (List.replicate t.rank BPair.unit)) (gramRho t F)).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun j => elim.dotP (posCorootV t j) (gramRho t F)) S) :=
    BPair.oneValue_trans
      (dotP_foldlE (posCorootV t) (gramRho t F) t.rank
        (posCorootV_length t) S _ hz)
      (BPair.oneValue_trans
        (BPair.add_congr (elim.dotP_replL t.rank (gramRho t F))
          (BPair.oneValue_refl _))
        (BPair.unit_add _))
  have key : (elim.dotP (eKey t S) (gramRho t F)).oneValue
      (elim.dotP (rhoV t) (gramRho t F)
        + (ground.famFold BPair.add BPair.unit
            (fun j => elim.dotP (posCorootV t j) (gramRho t F))
            S).swap) := by
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ (gramRho t F) (poly.pnorm_oneValue _)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_addE (rhoV t) _ (gramRho t F) (hrho.trans hnFS.symm)) ?_
    rw [elim.dotP_swap_left]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (ground.swap_congr hfold)
  refine BPair.oneValue_trans
    (BPair.add_congr key (BPair.oneValue_refl _)) ?_
  rw [BPair.add_assoc]
  exact BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.swap_add_null (BPair.oneValue_refl _)))
    (BPair.add_unit _)

/-- The witness fold's dot at a stated key (`thm:assembly`'s
support tier): where a key joins a natural fold of the simples back
to a target, the fold's counted simple dots join the key's dot back
to the target's. -/
theorem dotB_foldKey (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (x : List BPair) (c : List Nat) (v : List BPair)
    (hv : v.length = t.rank)
    (hkey : poly.pnorm (elim.vecAdd x (cartanFold t c)) = v) :
    (BPair.add (dotB F x (rhoV t))
      (ground.famFold BPair.add BPair.unit
        (fun i => BPair.mul
          (BPair.ofNat (ground.getAt 0 c i))
          (dotB F (posCorootV t (ground.getAt 0 F.simplePos i)) (rhoV t)))
        (List.range t.rank))).oneValue
      (dotB F v (rhoV t)) := by
  have hR : (gramRho t F).length = t.rank := gramRho_length t F hshape
  have hlen : (elim.vecAdd x (cartanFold t c)).length = t.rank := by
    rw [← poly.pnorm_length, hkey]
    exact hv
  have hone : poly.oneValue (elim.vecAdd x (cartanFold t c)) v := by
    have h := poly.oneValue_symm (poly.pnorm_oneValue
      (elim.vecAdd x (cartanFold t c)))
    rw [hkey] at h
    exact h
  have hWge : t.rank ≤ x.length := by
    have h := vecAdd_lenL x (cartanFold t c)
    rw [hlen] at h
    exact h
  have hGge : t.rank ≤ (cartanFold t c).length := by
    have h := vecAdd_lenR x (cartanFold t c)
    rw [hlen] at h
    exact h
  show (elim.dotP x (gramRho t F)
    + ground.famFold BPair.add BPair.unit
        (fun i => BPair.ofNat (getAt 0 c i)
          * elim.dotP (posCorootV t (getAt 0 F.simplePos i))
              (gramRho t F))
        (List.range t.rank)).oneValue
    (elim.dotP v (gramRho t F))
  have hrow : ∀ i, i < t.rank →
      (elim.dotP ((getAt [] t.cartan i).map
        (BPair.mul (BPair.ofNat (getAt 0 c i))))
        (gramRho t F)).oneValue
        (BPair.ofNat (getAt 0 c i)
          * elim.dotP (posCorootV t (getAt 0 F.simplePos i))
              (gramRho t F)) := by
    intro i hi
    refine BPair.oneValue_trans
      (elim.dotP_scaleL (BPair.ofNat (getAt 0 c i))
        (getAt [] t.cartan i) (gramRho t F)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_symm (elim.dotP_congr_left _ _ (gramRho t F)
      (fun j hj => ?_))
    have hjr : j < t.rank := by
      rw [hR] at hj
      exact hj
    show (getAt BPair.unit ((List.range t.rank).map
      (gentable.corootAt t (getAt [] t.posFolds
        (getAt 0 F.simplePos i)))) j).oneValue _
    rw [ground.getAt_map 0 BPair.unit _ (List.range t.rank) j
        (by rw [ground.length_range]; exact hjr),
      ground.getAt_range t.rank j hjr, hsp i hi]
    exact gentable.corootAt_oneHot t i j hi
  have hfold := dotP_foldl
    (fun i => (getAt [] t.cartan i).map
      (BPair.mul (BPair.ofNat (getAt 0 c i))))
    (gramRho t F) (List.range t.rank) (List.replicate t.rank BPair.unit)
    (by rw [hR]; exact hGge)
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (elim.dotP_oneValue_left _ _ (gramRho t F) (poly.oneValue_symm hone)) ?_)
  refine BPair.oneValue_trans
    (elim.dotP_vecAdd_left _ _ (gramRho t F) (by rw [hR]; exact hWge)
      (by rw [hR]; exact hGge)) ?_
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans hfold ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (elim.dotP_replL t.rank (gramRho t F))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  exact ground.foldB_congr_members _ _ (List.range t.rank)
    (fun i hi => hrow i (ground.ltOfMem hi))

/-- The Weyl member's dot: the witness fold's counted simple dots
join the member's key back to `ρ`'s (`con:sertables`' grading fold,
`w ρ + Σ_N β = ρ`). -/
private theorem dotB_wDom (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hdom : wDomRead t W wits) (k : Nat) (hk : k < W.length) :
    (BPair.add (dotB F (getAt ([], false) W k).1 (rhoV t))
      (ground.famFold BPair.add BPair.unit
        (fun i => BPair.mul
          (BPair.ofNat (getAt 0 (getAt [] wits k) i))
          (dotB F (posCorootV t (getAt 0 F.simplePos i)) (rhoV t)))
        (List.range t.rank))).oneValue
      (dotB F (rhoV t) (rhoV t)) :=
  dotB_foldKey t F hshape hsp (getAt ([], false) W k).1
    (getAt [] wits k) (rhoV t)
    (ground.length_replicate (BPair.ofNat 1) t.rank) (hdom.2 k hk)

theorem foldB_mem_le (f : Nat → BPair) : ∀ (l : List Nat),
    (∀ x, 0 < ground.countOf x l → BPair.unit ≤ f x) →
    ∀ x, 0 < ground.countOf x l →
      f x ≤ ground.famFold BPair.add BPair.unit f l
  | [], _, _, hx => absurd hx (Nat.lt_irrefl 0)
  | a :: l, h, x, hx => by
    show f x ≤ f a + ground.famFold BPair.add BPair.unit f l
    have htail : BPair.unit ≤ ground.famFold BPair.add BPair.unit f l :=
      ground.foldB_nonneg f l (fun z hz => h z (ground.countOf_cons_pos hz))
    by_cases hxa : x = a
    · rw [hxa]
      exact ground.leB_congr_left (BPair.add_unit (f a))
        (ground.leB_add (ground.leB_refl (f a)) htail)
    · have hx' : 0 < ground.countOf x l := by
        rw [ground.countOf_head_ne hxa] at hx
        exact hx
      exact ground.leB_trans
        (foldB_mem_le f l
          (fun z hz => h z (ground.countOf_cons_pos hz)) x hx')
        (ground.leB_congr_left (BPair.unit_add _)
          (ground.leB_add
            (h a (by rw [ground.countOf_head]; exact Nat.succ_pos _))
            (ground.leB_refl _)))

/-- `ρ`'s vector reads one at every key. -/
private theorem rhoV_getAt (t : gentable.Table) (j : Nat)
    (hj : j < t.rank) :
    getAt BPair.unit (rhoV t) j = BPair.ofNat 1 :=
  ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank j hj

/-- The Cartan data's row count off the Gram's defining read. -/
theorem cartanLen (t : gentable.Table) (F : FundData)
    (hgram : gramRead t F) : t.cartan.length = t.rank := by
  have h1 : (elim.matMul t.cartan F.gram).length
      = (ground.matOf t.rank t.rank (fun k j =>
          if k == j then
            BPair.ofNat (F.scale * getAt 0 t.lenNums k)
          else BPair.unit)).length := elim.matOne_length hgram
  rw [ground.matOf_length] at h1
  have h2 : (elim.matMul t.cartan F.gram).length
      = t.cartan.length := by
    show (t.cartan.map _).length = _
    exact ground.length_map _ t.cartan
  rw [h2] at h1
  exact h1

/-- The pairing splits over a family sum's keyed reads, one member
at a time (`thm:assembly`'s pin, `2ρ` the root fold). -/
private theorem dotP_foldSum (t : gentable.Table) (n : Nat)
    (x : List BPair) (hx : x.length = n) :
    ∀ folds : List (List Nat),
    (elim.dotP ((List.range n).map (fun j =>
        BPair.sum (folds.map (fun f =>
          gentable.corootAt t f j)))) x).oneValue
      (BPair.sum (folds.map (fun f =>
        elim.dotP ((List.range n).map
          (gentable.corootAt t f)) x)))
  | [] => by
    show (elim.dotP ((List.range n).map
        (fun _ => BPair.unit)) x).oneValue BPair.unit
    rw [ground.map_const BPair.unit (List.range n)]
    exact elim.dotP_replL (List.range n).length x
  | f :: folds => by
    refine BPair.oneValue_trans
      (elim.dotP_congr_left _ ((List.range n).map (fun j =>
          gentable.corootAt t f j
            + BPair.sum (folds.map (fun f' =>
                gentable.corootAt t f' j)))) x
        (fun j hj => ?_)) ?_
    · rw [ground.getAt_map 0 BPair.unit _ (List.range n) j
          (by rw [ground.length_range, ← hx]; exact hj),
        ground.getAt_map 0 BPair.unit _ (List.range n) j
          (by rw [ground.length_range, ← hx]; exact hj)]
      exact BPair.sum_cons _ _
    · rw [← elim.mapAdd]
      refine BPair.oneValue_trans
        (elim.dotP_addE _ _ x (by
          rw [ground.length_map, ground.length_map])) ?_
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (dotP_foldSum t n x hx folds))
        (BPair.oneValue_symm (BPair.sum_cons _ _))

/-- The root fold's coroot read at a key, extracted from the
stated fold (`con:sertables`' first shared read). -/
private theorem rhoTwo (t : gentable.Table)
    (hrho : gentable.rhoRead t) (j : Nat) (hj : j < t.rank) :
    (gentable.rho2Coroot t j).oneValue (BPair.ofNat 2) := by
  have h := ground.all_range_read t.rank hrho j hj
  by_cases hp : (gentable.rho2Coroot t j).oneValue (BPair.ofNat 2)
  · exact hp
  · rw [if_neg hp] at h
    exact Bool.noConfusion h

/-- The Gram slot exchange: the form's pairing reads at either
order, the transpose adjoint at `gramSymRead`'s own read. -/
theorem dotB_swap (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (x y : List BPair) (hx : x.length = t.rank)
    (hy : y.length = t.rank) :
    (dotB F x y).oneValue (dotB F y x) := by
  show (elim.dotP x (elim.matVec F.gram y)).oneValue
    (elim.dotP y (elim.matVec F.gram x))
  rw [elim.dotP_comm x (elim.matVec F.gram y)]
  refine BPair.oneValue_trans
    (elim.dotP_matVec_transpose t.rank F.gram y x
      (elim.rowsLen_of_allP (fun _ hr => ground.beqEqOf hr)
        F.gram hshape.2.1)
      hy (by rw [hx, hshape.1])) ?_
  rw [elim.dotP_comm y (elim.matVec (elim.transposeM F.gram) x),
    elim.dotP_comm y (elim.matVec F.gram x)]
  exact elim.dotP_oneValue_left (elim.matVec (elim.transposeM F.gram) x)
    (elim.matVec F.gram x) y
    (elim.matVec_matOne (elim.transposeM F.gram) F.gram x hgsym)

/-- The positive list's dots at a weight collect to the doubled
`ρ`-dot: the root fold's coroot two read on the weight's first
slot (`con:sertables`' first shared read). -/
private theorem sumRootDotsL (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hrho : gentable.rhoRead t)
    (kap : List BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun j => dotB F (posCorootV t j) kap)
      (List.range t.posFolds.length)).oneValue
      (BPair.add (dotB F (rhoV t) kap) (dotB F (rhoV t) kap)) := by
  have hX : (elim.matVec F.gram kap).length = t.rank :=
    (elim.matVec_length F.gram kap).trans hshape.1
  rw [show ground.famFold BPair.add BPair.unit
      (fun j => dotB F (posCorootV t j) kap)
      (List.range t.posFolds.length)
    = ground.famFold BPair.add BPair.unit
        (fun f => elim.dotP ((List.range t.rank).map
          (gentable.corootAt t f)) (elim.matVec F.gram kap))
        ((List.range t.posFolds.length).map
          (fun p => ground.getAt [] t.posFolds p)) from
    (ground.famFold_map BPair.add BPair.unit
      (fun f => elim.dotP ((List.range t.rank).map
        (gentable.corootAt t f)) (elim.matVec F.gram kap))
      (fun p => ground.getAt [] t.posFolds p)
      (List.range t.posFolds.length)).symm]
  rw [ground.range_map_getAt [] t.posFolds.length t.posFolds rfl]
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (BPair.oneValue_trans (bsum_famFold _)
      (by
        rw [ground.famFold_map BPair.add BPair.unit
          (fun x => x) (fun f => elim.dotP ((List.range t.rank).map
            (gentable.corootAt t f)) (elim.matVec F.gram kap))
          t.posFolds]
        exact BPair.oneValue_refl _))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (dotP_foldSum t t.rank (elim.matVec F.gram kap) hX
      t.posFolds)) ?_
  refine BPair.oneValue_trans
    (elim.dotP_congr_left _
      (elim.vecAdd (rhoV t) (rhoV t)) (elim.matVec F.gram kap) ?_) ?_
  · intro j hj
    rw [hX] at hj
    rw [ground.getAt_map 0 BPair.unit _ (List.range t.rank) j
      (by rw [ground.length_range]; exact hj),
      ground.getAt_range t.rank j hj,
      elim.getAt_vecAdd (rhoV t) (rhoV t) j
        (by rw [rhoV, ground.length_replicate]; exact hj)
        (by rw [rhoV, ground.length_replicate]; exact hj)]
    rw [show ground.getAt BPair.unit (rhoV t) j = BPair.ofNat 1 from by
      rw [rhoV]
      exact ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank j hj]
    exact BPair.oneValue_trans (rhoTwo t hrho j hj) (BPair.ofNat_add 1 1)
  · exact elim.dotP_vecAdd_left (rhoV t) (rhoV t)
      (elim.matVec F.gram kap)
      (by rw [hX, rhoV, ground.length_replicate]; exact Nat.le_refl _)
      (by rw [hX, rhoV, ground.length_replicate]; exact Nat.le_refl _)

/-- At a family key the members' dots at a weight join the key's
own back to `ρ`'s dot, read on the weight's first slot. -/
private theorem hitDotsL (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (kap : List BPair) (S : List Nat) :
    (ground.bsum (fun j => dotB F (posCorootV t j) kap) S
      + dotB F (eKey t S) kap).oneValue
      (dotB F (rhoV t) kap) := by
  have hX : (elim.matVec F.gram kap).length = t.rank :=
    (elim.matVec_length F.gram kap).trans hshape.1
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hV : (elim.vsum t.rank (posCorootV t) S).length = t.rank :=
    foldl_length t S _ (ground.length_replicate BPair.unit t.rank)
  have hnV : (poly.neg (elim.vsum t.rank (posCorootV t) S)).length
      = t.rank := by
    rw [poly.length_neg]
    exact hV
  have hfold : (elim.dotP (elim.vsum t.rank (posCorootV t) S)
      (elim.matVec F.gram kap)).oneValue
      (ground.bsum (fun j => dotB F (posCorootV t j) kap) S) := by
    rw [elim.dotP_comm]
    refine BPair.oneValue_trans
      (elim.dotP_vsum t.rank (posCorootV t) (posCorootV_length t)
        (elim.matVec F.gram kap) hX S) ?_
    refine ground.foldB_congr_members _ _ S (fun j _ => ?_)
    rw [elim.dotP_comm]
    exact BPair.oneValue_of_eq rfl
  have hkey : (dotB F (eKey t S) kap).oneValue
      (dotB F (rhoV t) kap
        + (elim.dotP (elim.vsum t.rank (posCorootV t) S)
            (elim.matVec F.gram kap)).swap) := by
    refine BPair.oneValue_trans
      (elim.dotP_oneValue_left _ _ (elim.matVec F.gram kap)
        (poly.pnorm_oneValue _)) ?_
    refine BPair.oneValue_trans
      (elim.dotP_vecAdd_left (rhoV t) _ (elim.matVec F.gram kap)
        (by rw [hX, hrl]; exact Nat.le_refl _)
        (by rw [hX, hnV]; exact Nat.le_refl _)) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    rw [elim.dotP_swap_left]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) hkey) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_left_comm _ _ _)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.swap_add_null hfold))) ?_
  exact BPair.add_unit _

/-- The positive list's dots against a member collect to the doubled
`ρ`-dot: the weight-slot collection read across the Gram's symmetry,
one swap per member and one at each collected `ρ`-dot. -/
private theorem sumRootDots (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrho : gentable.rhoRead t)
    (nu : List BPair) (hnu : nu.length = t.rank) :
    (ground.famFold BPair.add BPair.unit
      (fun j => dotB F nu (posCorootV t j))
      (List.range t.posFolds.length)).oneValue
      (BPair.add (dotB F nu (rhoV t)) (dotB F nu (rhoV t))) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => dotB F (posCorootV t j) nu)
      (List.range t.posFolds.length) (fun j _ =>
        dotB_swap t F hshape hgsym nu (posCorootV t j) hnu
          (posCorootV_length t j))) ?_
  refine BPair.oneValue_trans (sumRootDotsL t F hshape hrho nu) ?_
  exact BPair.add_congr
    (dotB_swap t F hshape hgsym (rhoV t) nu
      (by rw [rhoV, ground.length_replicate]) hnu)
    (dotB_swap t F hshape hgsym (rhoV t) nu
      (by rw [rhoV, ground.length_replicate]) hnu)
/-- A family fold splits at a stated guard, the two graded parts
joining to the whole. -/
private theorem foldB_guardSplit {α : Type} [DecidableEq α]
    (P : α → Bool) (w : α → BPair) (l : List α) :
    (ground.famFold BPair.add BPair.unit w l).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun j => if P j then w j else BPair.unit) l
       + ground.famFold BPair.add BPair.unit
          (fun j => if P j then BPair.unit else w j) l) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members w
      (fun j => (if P j then w j else BPair.unit)
        + (if P j then BPair.unit else w j)) l (fun x _ => ?_)) ?_
  · cases hp : P x
    · rw [if_neg (ground.boolNe rfl), if_neg (ground.boolNe rfl)]
      exact BPair.oneValue_symm (BPair.unit_add (w x))
    · rw [if_pos rfl, if_pos rfl]
      exact BPair.oneValue_symm (BPair.add_unit (w x))
  · exact ground.foldB_add _ _ l

/-- A membership-masked fold over the positional enumeration reads
the family's own fold, at a distinct family inside the range. -/
private theorem foldB_maskS (w : Nat → BPair) :
    ∀ (S : List Nat), (∀ x, ground.countOf x S ≤ 1) →
    ∀ (N : Nat), (∀ x, 0 < ground.countOf x S → x < N) →
    (ground.famFold BPair.add BPair.unit
      (fun j => if ground.containsB S j then w j else BPair.unit)
      (List.range N)).oneValue
      (ground.famFold BPair.add BPair.unit w S)
  | [], _, N, _ => by
    refine ground.foldB_nullRange _ N (fun x _ => ?_)
    have hc : ground.containsB [] x = false := rfl
    rw [hc, if_neg (ground.boolNe rfl)]
    exact BPair.oneValue_refl _
  | a :: S', hd, N, hb => by
    have haS' : ground.countOf a S' = 0 := by
      have h1 := hd a
      rw [show ground.countOf a (a :: S')
          = 1 + ground.countOf a S' from by
        rw [ground.countOf_cons, if_pos rfl]] at h1
      cases hc : ground.countOf a S' with
      | zero => rfl
      | succ m =>
        rw [hc, Nat.add_comm] at h1
        exact absurd (Nat.le_of_succ_le_succ h1)
          (Nat.not_succ_le_zero m)
    have hdS' : ∀ x, ground.countOf x S' ≤ 1 := fun x =>
      Nat.le_trans (by
        rw [ground.countOf_cons]
        exact Nat.le_add_left _ _) (hd x)
    have hbS' : ∀ x, 0 < ground.countOf x S' → x < N := by
      intro x hx
      refine hb x ?_
      rw [ground.countOf_cons]
      exact if hxa : x = a then by
        rw [if_pos hxa]
        exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _)
      else by
        rw [if_neg hxa, Nat.zero_add]
        exact hx
    have haN : a < N := hb a (by
      rw [ground.countOf_cons, if_pos rfl]
      exact Nat.lt_of_lt_of_le (Nat.succ_pos 0) (Nat.le_add_right 1 _))
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun j => (if j = a then w a else BPair.unit)
          + (if ground.containsB S' j then w j else BPair.unit))
        (List.range N) (fun x _ => ?_)) ?_
    · exact if hxa : x = a then by
        rw [hxa, ground.containsB_head a S', if_pos rfl, if_pos rfl]
        have hcf : ground.containsB S' a = false := by
          show decide (0 < ground.countOf a S') = false
          rw [haS']
          rfl
        rw [hcf, if_neg (ground.boolNe rfl)]
        exact BPair.oneValue_symm (BPair.add_unit (w a))
      else by
        rw [ground.containsB_cons_ne hxa S', if_neg hxa]
        cases ground.containsB S' x
        · exact BPair.oneValue_symm (BPair.unit_add BPair.unit)
        · exact BPair.oneValue_symm (BPair.unit_add (w x))
    · refine BPair.oneValue_trans
        (ground.foldB_add _ _ (List.range N)) ?_
      have hcnt : 0 < ground.countOf a (List.range N) :=
        ground.countOf_range_pos haN
      have hdelta : (ground.famFold BPair.add BPair.unit
          (fun j => if j = a then w a else BPair.unit)
          (List.range N)).oneValue (w a) := by
        have herase : ground.famFold BPair.add BPair.unit
            (fun j => if j = a then w a else BPair.unit)
            (List.range N)
              = (if a = a then w a else BPair.unit)
                + ground.famFold BPair.add BPair.unit
                    (fun j => if j = a then w a else BPair.unit)
                    (ground.eraseFirst a (List.range N)) :=
          ground.famFold_eraseFirst BPair.add BPair.unit
            BPair.add_comm BPair.add_assoc _ (List.range N) a hcnt
        rw [herase, if_pos rfl]
        refine BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl (w a))
            (ground.foldB_null _ _ (fun x hx => ?_)))
          (BPair.add_unit (w a))
        have hxa : x ≠ a := by
          intro hxeq
          rw [hxeq] at hx
          have hself := ground.countOf_eraseFirst_self
            (List.range N) a hcnt
          rw [ground.countOf_range_one haN] at hself
          have h0 : ground.countOf a
              (ground.eraseFirst a (List.range N)) = 0 := by
            cases hc : ground.countOf a
                (ground.eraseFirst a (List.range N)) with
            | zero => rfl
            | succ m =>
              rw [hc] at hself
              exact Nat.noConfusion (Nat.succ.inj hself)
          rw [h0] at hx
          exact absurd hx (Nat.lt_irrefl 0)
        rw [if_neg hxa]
        exact BPair.oneValue_refl _
      exact BPair.add_congr hdelta (foldB_maskS w S' hdS' N hbS')

/-- The complement-guarded dots at a family: the masked fold reads
`ρ`'s dot joined to the key's, on the weight's first slot. -/
private theorem antiDotsL (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hrho : gentable.rhoRead t)
    (kap : List BPair) (S : List Nat)
    (hSd : ∀ x, ground.countOf x S ≤ 1)
    (hSb : ∀ x, 0 < ground.countOf x S → x < t.posFolds.length) :
    (ground.famFold BPair.add BPair.unit
      (fun j => if ground.containsB S j then BPair.unit
        else dotB F (posCorootV t j) kap)
      (List.range t.posFolds.length)).oneValue
      (BPair.add (dotB F (rhoV t) kap) (dotB F (eKey t S) kap)) := by
  have hsplit := foldB_guardSplit (ground.containsB S)
    (fun j => dotB F (posCorootV t j) kap)
    (List.range t.posFolds.length)
  have hall := sumRootDotsL t F hshape hrho kap
  have hmask := foldB_maskS (fun j => dotB F (posCorootV t j) kap)
    S hSd t.posFolds.length hSb
  have hhit := hitDotsL t F hshape kap S
  have hjoin : (ground.famFold BPair.add BPair.unit
      (fun j => if ground.containsB S j then BPair.unit
        else dotB F (posCorootV t j) kap)
      (List.range t.posFolds.length)
      + ground.bsum (fun j => dotB F (posCorootV t j) kap) S).oneValue
      (dotB F (rhoV t) kap + dotB F (rhoV t) kap) :=
    BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm hmask))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.oneValue_trans (BPair.oneValue_symm hsplit) hall))
  refine BPair.add_cancel (c := dotB F (rhoV t) kap) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm hhit)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr hjoin (BPair.oneValue_refl _)) ?_
  show ((dotB F (rhoV t) kap + dotB F (rhoV t) kap)
      + dotB F (eKey t S) kap).oneValue
    ((dotB F (rhoV t) kap + dotB F (eKey t S) kap)
      + dotB F (rhoV t) kap)
  rw [BPair.add_assoc, BPair.add_comm
      (dotB F (rhoV t) kap + dotB F (eKey t S) kap)
      (dotB F (rhoV t) kap)]
  exact BPair.oneValue_refl _

/-- At a family key the members' dots join the key's own back to
the `ρ`-dot: the weight-slot hit read across the Gram's symmetry,
one swap per side. -/
private theorem hitDots (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (nu : List BPair) (hnu : nu.length = t.rank)
    (k : List BPair) (S : List Nat) (hit : eKey t S = k) :
    (ground.bsum (fun j => dotB F nu (posCorootV t j)) S
      + dotB F nu k).oneValue (dotB F nu (rhoV t)) := by
  rw [← hit]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (ground.foldB_congr_members _
        (fun j => dotB F (posCorootV t j) nu) S (fun j _ =>
          dotB_swap t F hshape hgsym nu (posCorootV t j) hnu
            (posCorootV_length t j)))
      (dotB_swap t F hshape hgsym nu (eKey t S) hnu
        (eKey_length t S))) ?_
  refine BPair.oneValue_trans (hitDotsL t F hshape nu S) ?_
  exact dotB_swap t F hshape hgsym (rhoV t) nu
    (by rw [rhoV, ground.length_replicate]) hnu
/-- The count pair at a shared guard: the guard pulls out whole. -/
private theorem hpullCounts (c : Bool) (x y : Nat) :
    BPair.ofCounts (if c then 0 else x) (if c then 0 else y)
      = if c then BPair.ofCounts 0 0 else BPair.ofCounts x y := by
  cases c
  · rfl
  · rfl

/-- An enumerated family is distinct and sits inside the range. -/
private theorem sublists_range_distinct (N : Nat) (S : List Nat)
    (hS : 0 < ground.countOf S (ground.sublistsOf (List.range N))) :
    (∀ x, ground.countOf x S ≤ 1)
      ∧ (∀ x, 0 < ground.countOf x S → x < N) := by
  have hdr : ∀ x, ground.countOf x (List.range N) ≤ 1 :=
    fun x => ground.distinctList_all (ground.distinctList_range N) x
  refine ⟨?_, ?_⟩
  · intro x
    have hchar := ground.sublists_char (List.range N) hdr S hS
    have h2 : ground.countOf x S
        = ground.countOf x (List.filter (ground.containsB S) (List.range N)) := by
      rw [← hchar]
    rw [h2, ground.countOf_filter (ground.containsB S) x (List.range N)]
    exact if hc : ground.containsB S x = true then by
      rw [if_pos hc]; exact hdr x
    else by
      rw [if_neg hc]; exact Nat.zero_le 1
  · intro x hx
    have hin := ground.sublists_entries (List.range N) S hS x hx
    rw [ground.countOf_range x N] at hin
    exact if hxN : x < N then hxN
    else by
      rw [if_neg hxN] at hin
      exact absurd hin (Nat.lt_irrefl 0)

/-- The complement-guarded dots at a family read the key's dot
joined to the `ρ`-dot: the weight-slot masked collection across the
Gram's symmetry, the guard kept memberwise. -/
private theorem antiDots (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrho : gentable.rhoRead t)
    (nu k : List BPair) (hnu : nu.length = t.rank)
    (S : List Nat)
    (hSd : ∀ x, ground.countOf x S ≤ 1)
    (hSb : ∀ x, 0 < ground.countOf x S → x < t.posFolds.length)
    (hit : eKey t S = k) :
    (ground.famFold BPair.add BPair.unit
      (fun j => if ground.containsB S j then BPair.unit
        else dotB F nu (posCorootV t j))
      (List.range t.posFolds.length)).oneValue
      (BPair.add (dotB F nu k) (dotB F nu (rhoV t))) := by
  rw [← hit]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => if ground.containsB S j then BPair.unit
        else dotB F (posCorootV t j) nu)
      (List.range t.posFolds.length) (fun j _ => by
        by_cases hc : ground.containsB S j
        · rw [if_pos hc, if_pos hc]
          exact BPair.oneValue_refl _
        · rw [if_neg hc, if_neg hc]
          exact dotB_swap t F hshape hgsym nu (posCorootV t j) hnu
            (posCorootV_length t j))) ?_
  refine BPair.oneValue_trans
    (antiDotsL t F hshape hrho nu S hSd hSb) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq
    (BPair.add_comm (dotB F (rhoV t) nu) (dotB F (eKey t S) nu))) ?_
  exact BPair.add_congr
    (dotB_swap t F hshape hgsym (eKey t S) nu (eKey_length t S) hnu)
    (dotB_swap t F hshape hgsym (rhoV t) nu
      (by rw [rhoV, ground.length_replicate]) hnu)
/-- One root's cofactor term expands over the guarded enumeration. -/
private theorem eulerPerJ (t : gentable.Table) (F : FundData)
    (nu k : List BPair) (j : Nat)
    (hj : j < t.posFolds.length) :
    (BPair.mul (dotB F nu (posCorootV t j))
      (BPair.ofCounts (subsetCountOff t j k false)
        (subsetCountOff t j k true))).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun S => BPair.mul (dotB F nu (posCorootV t j))
          (if ground.containsB S j then BPair.ofCounts 0 0
            else BPair.ofCounts
              (if places.sideOf S = false then
                (if eKey t S = k then 1 else 0) else 0)
              (if places.sideOf S = true then
                (if eKey t S = k then 1 else 0) else 0)))
        (ground.sublistsOf (List.range t.posFolds.length))) := by
  have hjr : 0 < ground.countOf j (List.range t.posFolds.length) := by
    rw [ground.countOf_range_one hj]
    exact Nat.succ_pos 0
  have hQF : subsetCountOff t j k false
      = ground.famFold Nat.add 0 (fun S => if ground.containsB S j then 0
          else (if places.sideOf S = false then
            (if eKey t S = k then 1 else 0) else 0))
        (ground.sublistsOf (List.range t.posFolds.length)) :=
    sublists_eraseGuard (List.range t.posFolds.length)
      (fun x => ground.distinctList_all (ground.distinctList_range t.posFolds.length) x) j hjr _
  have hQT : subsetCountOff t j k true
      = ground.famFold Nat.add 0 (fun S => if ground.containsB S j then 0
          else (if places.sideOf S = true then
            (if eKey t S = k then 1 else 0) else 0))
        (ground.sublistsOf (List.range t.posFolds.length)) :=
    sublists_eraseGuard (List.range t.posFolds.length)
      (fun x => ground.distinctList_all (ground.distinctList_range t.posFolds.length) x) j hjr _
  rw [hQF, hQT]
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (foldB_ofCounts _ _
        (ground.sublistsOf (List.range t.posFolds.length)))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (ground.foldB_mul_left (dotB F nu (posCorootV t j)) _
      (ground.sublistsOf (List.range t.posFolds.length)))) ?_
  refine ground.foldB_congr_members _ _
    (ground.sublistsOf (List.range t.posFolds.length)) (fun S _ => ?_)
  rw [hpullCounts (ground.containsB S j) _ _]
  exact BPair.oneValue_refl _

/-- The Euler collection at a key: the withdrawn folds' count
pairs collect against the roots' dots to the key's dot joined to
`ρ`'s own, at the subset fold's counts — `thm:memberchar`'s cross
term at the subset reindex.  The key binds free, and `hnu` is
`con:gentable`'s frame, a content a matched list over the
coordinates. -/
theorem subsetCountOff_euler (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrho : gentable.rhoRead t)
    (nu k : List BPair) (hnu : nu.length = t.rank) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      BPair.mul (dotB F nu (posCorootV t j))
        (BPair.ofCounts (subsetCountOff t j k false)
          (subsetCountOff t j k true)))
      (List.range t.posFolds.length)).oneValue
      (BPair.mul (BPair.add (dotB F nu k) (dotB F nu (rhoV t)))
        (BPair.ofCounts (subsetCount t k false)
          (subsetCount t k true))) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _ (fun j =>
      ground.famFold BPair.add BPair.unit
        (fun S => BPair.mul (dotB F nu (posCorootV t j))
          (if ground.containsB S j then BPair.ofCounts 0 0
            else BPair.ofCounts
              (if places.sideOf S = false then
                (if eKey t S = k then 1 else 0) else 0)
              (if places.sideOf S = true then
                (if eKey t S = k then 1 else 0) else 0)))
        (ground.sublistsOf (List.range t.posFolds.length)))
      (List.range t.posFolds.length) (fun j hj => ?_)) ?_
  · refine eulerPerJ t F nu k j ?_
    rw [ground.countOf_range j t.posFolds.length] at hj
    exact if h : j < t.posFolds.length then h
    else by
      rw [if_neg h] at hj
      exact absurd hj (Nat.lt_irrefl 0)
  refine BPair.oneValue_trans
    (ground.foldB_swapL (fun j S => BPair.mul (dotB F nu (posCorootV t j))
      (if ground.containsB S j then BPair.ofCounts 0 0
        else BPair.ofCounts
          (if places.sideOf S = false then
            (if eKey t S = k then 1 else 0) else 0)
          (if places.sideOf S = true then
            (if eKey t S = k then 1 else 0) else 0)))
      (List.range t.posFolds.length)
      (ground.sublistsOf (List.range t.posFolds.length))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun S => BPair.mul
        (BPair.add (dotB F nu k) (dotB F nu (rhoV t)))
        (BPair.ofCounts
          (if places.sideOf S = false then
            (if eKey t S = k then 1 else 0) else 0)
          (if places.sideOf S = true then
            (if eKey t S = k then 1 else 0) else 0)))
      (ground.sublistsOf (List.range t.posFolds.length))
      (fun S hS => ?_)) ?_
  · obtain ⟨hSd, hSb⟩ := sublists_range_distinct
      t.posFolds.length S hS
    exact if hhit : eKey t S = k then by
      rw [if_pos hhit]
      refine BPair.oneValue_trans
        (ground.foldB_congr_members _
          (fun j => BPair.mul
            (BPair.ofCounts
              (if places.sideOf S = false then 1 else 0)
              (if places.sideOf S = true then 1 else 0))
            (if ground.containsB S j then BPair.unit
              else dotB F nu (posCorootV t j)))
          (List.range t.posFolds.length) (fun j _ => ?_)) ?_
      · cases ground.containsB S j
        · exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
        · refine BPair.oneValue_trans
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl _) BPair.ofCounts_zero)
              (BPair.mul_unit _)) ?_
          exact BPair.oneValue_symm (BPair.mul_unit _)
      · refine BPair.oneValue_trans
          (ground.foldB_mul_left _ _
            (List.range t.posFolds.length)) ?_
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (antiDots t F hshape hgsym hrho nu k hnu S
              hSd hSb hhit)) ?_
        exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
    else by
      have hf0 : ∀ b : Bool, (if places.sideOf S = b then
          (if eKey t S = k then 1 else 0) else 0) = 0 := by
        intro b
        exact if hs : places.sideOf S = b then by
          rw [if_pos hs, if_neg hhit]
        else by
          rw [if_neg hs]
      rw [hf0 false, hf0 true]
      refine BPair.oneValue_trans
        (ground.foldB_nullRange _ t.posFolds.length
          (fun j _ => ?_)) ?_
      · cases ground.containsB S j
        · exact BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _) BPair.ofCounts_zero)
            (BPair.mul_unit _)
        · exact BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl _) BPair.ofCounts_zero)
            (BPair.mul_unit _)
      · exact BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) BPair.ofCounts_zero)
          (BPair.mul_unit _))
  refine BPair.oneValue_trans
    (ground.foldB_mul_left
      (BPair.add (dotB F nu k) (dotB F nu (rhoV t))) _
      (ground.sublistsOf (List.range t.posFolds.length))) ?_
  exact BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (foldB_ofCounts _ _
      (ground.sublistsOf (List.range t.posFolds.length))))

/-- The balance fold splits at the join. -/
private theorem foldB_app {α : Type} (f : α → BPair) : ∀ u v : List α,
    (ground.famFold BPair.add BPair.unit f (u ++ v)).oneValue
      (ground.famFold BPair.add BPair.unit f u
        + ground.famFold BPair.add BPair.unit f v)
  | [], _ => BPair.oneValue_symm (BPair.unit_add _)
  | a :: u, v =>
    BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (f a)) (foldB_app f u v))
      (BPair.oneValue_of_eq (BPair.add_assoc (f a) _ _).symm)

/-- At a family key the key's `ρ`-dot sits at or below `ρ`'s own,
the join's read at the withdrawn fold's positive dots
(`thm:assembly`'s conclusion clause: an occupied key's dot
joins its family's positive dots to `ρ`'s own). -/
theorem hitLe (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) (k : List BPair) (S : List Nat)
    (hS : ∀ i, 0 < ground.countOf i S → i < t.posFolds.length)
    (hit : eKey t S = k) :
    dotB F (rhoV t) k ≤ dotB F (rhoV t) (rhoV t) := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hD := hitDots t F hshape hgsym (rhoV t) hrl k S hit
  have hpos : BPair.unit ≤ ground.bsum
      (fun j => dotB F (rhoV t) (posCorootV t j)) S := by
    refine ground.leB_congr_left
      (ground.foldB_null (fun _ => BPair.unit) S
        (fun _ _ => BPair.oneValue_refl _)) ?_
    refine ground.bsum_le _ _ S (fun i hiS => ?_)
    refine Or.inr ?_
    exact BPair.lt_congr (BPair.oneValue_refl _)
      (dotB_swap t F hshape hgsym _ _ (posCorootV_length t i) hrl)
      (hrd i (hS i hiS))
  have hRD : (dotB F (rhoV t) (rhoV t)
      + (dotB F (rhoV t) k).swap).oneValue
      (ground.bsum (fun j => dotB F (rhoV t) (posCorootV t j)) S) := by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_symm hD)
        (BPair.oneValue_refl _)) ?_
    rw [BPair.add_assoc]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.swap_add_null
          (BPair.oneValue_refl (dotB F (rhoV t) k).swap))) ?_
    exact BPair.add_unit _
  exact ground.leB_of_unit_add
    (ground.leB_congr_right (BPair.oneValue_symm hRD) hpos)

/-- The withdrawn fold's count at a key beyond `ρ`'s own height
reads the count's unit. -/
private theorem subsetCountOff_vanish (t : gentable.Table)
    (F : FundData) (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (y : List BPair)
    (hv : dotB F (rhoV t) (rhoV t) < dotB F (rhoV t) y)
    (side : Bool) : subsetCountOff t j y side = 0 := by
  show ground.famFold Nat.add 0 _
    (ground.sublistsOf (ground.eraseFirst j
      (List.range t.posFolds.length))) = 0
  rw [ground.famFold_congr_members Nat.add 0 _ (fun _ => 0)
    (ground.sublistsOf (ground.eraseFirst j
      (List.range t.posFolds.length))) (fun S hS => by
      by_cases hside : places.sideOf S = side
      · by_cases hhit : eKey t S = y
        · refine absurd hv (ground.leB_not_lt ?_)
          rw [← hhit]
          refine hitLe t F hshape hgsym hrd _ S (fun i hiS => ?_) rfl
          have hocc := ground.sublists_entries
            (ground.eraseFirst j (List.range t.posFolds.length))
            S hS i hiS
          by_cases hij : i = j
          · rw [hij]; exact hj
          · refine ground.ltOfMem ?_
            rw [← ground.countOf_eraseFirst_ne
              (List.range t.posFolds.length) j i hij]
            exact hocc
        · rw [if_pos hside, if_neg hhit]
      · rw [if_neg hside])]
  exact ground.famFold_zero (fun _ => 0) (fun _ => rfl) _

/-- The line's first key: the natural one's scale reads the member
itself inside the norm. -/
theorem lineKey_one (t : gentable.Table) {j : Nat}
    (y : List BPair) (hy : y.length = t.rank) :
    poly.pnorm (elim.vecAdd y
        (elim.vecScale (BPair.ofNat 1) (posCorootV t j)))
    = poly.pnorm (elim.vecAdd y (posCorootV t j)) := by
  have hA : (posCorootV t j).length = t.rank := posCorootV_length t j
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [elim.length_vecAdd y _ t.rank hy
        (by rw [elim.length_vecScale]; exact hA),
      elim.length_vecAdd y _ t.rank hy hA]
  · rw [elim.vecAdd_comm y _, elim.vecAdd_comm y (posCorootV t j)]
    refine elim.vecAdd_congr _ _ y ?_ (elim.vecScale_one _)
    rw [elim.length_vecScale]

/-- The line's stepped key: one further member joins the scale's
successor inside the norm. -/
private theorem lineKey_step (t : gentable.Table) {j : Nat}
    (y : List BPair) (hy : y.length = t.rank) (c : Nat) :
    poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd y
        (elim.vecScale (BPair.ofNat (c + 1)) (posCorootV t j))))
      (posCorootV t j))
    = poly.pnorm (elim.vecAdd y
        (elim.vecScale (BPair.ofNat (c + 2)) (posCorootV t j))) := by
  have hA : (posCorootV t j).length = t.rank := posCorootV_length t j
  have hsc : (elim.vecScale (BPair.ofNat (c + 1))
      (posCorootV t j)).length = t.rank := by
    rw [elim.length_vecScale]; exact hA
  have hu : (elim.vecAdd y (elim.vecScale (BPair.ofNat (c + 1))
      (posCorootV t j))).length = t.rank :=
    elim.length_vecAdd y _ t.rank hy hsc
  rw [elim.pnorm_vecAdd_left _ _ (hu.trans hA.symm),
    elim.vecAdd_assoc y _ (posCorootV t j)]
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [elim.length_vecAdd y _ t.rank hy
        (elim.length_vecAdd _ _ t.rank hsc hA),
      elim.length_vecAdd y _ t.rank hy
        (by rw [elim.length_vecScale]; exact hA)]
  · rw [elim.vecAdd_comm y _, elim.vecAdd_comm y
      (elim.vecScale (BPair.ofNat (c + 2)) (posCorootV t j))]
    refine elim.vecAdd_congr _ _ y ?_ ?_
    · rw [elim.length_vecAdd _ _ t.rank hsc hA,
        elim.length_vecScale, hA]
    · refine poly.oneValue_symm ?_
      refine poly.oneValue_trans
        (elim.vecScale_congr (BPair.ofNat_add (c + 1) 1)
          (posCorootV t j)) ?_
      rw [elim.vecScale_add (BPair.ofNat (c + 1)) (BPair.ofNat 1)
        (posCorootV t j)]
      rw [elim.vecAdd_comm _ (elim.vecScale (BPair.ofNat 1)
          (posCorootV t j)),
        elim.vecAdd_comm _ (posCorootV t j)]
      refine elim.vecAdd_congr _ _ _ ?_ (elim.vecScale_one _)
      rw [elim.length_vecScale]

/-- The line's collection: the subset fold's pairs along the line
join the withdrawn pair at the first key to the flipped pair at
the cap's key, one `(Cof)` gap per step — `thm:memberchar`'s cofactor
identity `⟨x^{α+} : x^{α−}⟩ Q_α = a_ρ` read coefficientwise
along the line. -/
private theorem lineCollect (t : gentable.Table) (F : FundData)
    {j : Nat} (hj : j < t.posFolds.length)
    (y : List BPair) (hy : y.length = t.rank) : ∀ cap : Nat,
    (ground.famFold BPair.add BPair.unit (fun l =>
      BPair.ofCounts
        (subsetCount t (poly.pnorm (elim.vecAdd y
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV t j)))) false)
        (subsetCount t (poly.pnorm (elim.vecAdd y
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV t j)))) true))
      (List.range cap)).oneValue
      (BPair.ofCounts
          (subsetCountOff t j
            (poly.pnorm (elim.vecAdd y (posCorootV t j))) false)
          (subsetCountOff t j
            (poly.pnorm (elim.vecAdd y (posCorootV t j))) true)
        + BPair.ofCounts
          (subsetCountOff t j (poly.pnorm (elim.vecAdd y
            (elim.vecScale (BPair.ofNat (cap + 1))
              (posCorootV t j)))) true)
          (subsetCountOff t j (poly.pnorm (elim.vecAdd y
            (elim.vecScale (BPair.ofNat (cap + 1))
              (posCorootV t j)))) false))
  | 0 => by
    rw [show poly.pnorm (elim.vecAdd y
        (elim.vecScale (BPair.ofNat (0 + 1)) (posCorootV t j)))
      = poly.pnorm (elim.vecAdd y (posCorootV t j))
      from lineKey_one t y hy]
    exact BPair.oneValue_symm (BPair.ofCounts_pair _ _)
  | c + 1 => by
    have hkey : (poly.pnorm (elim.vecAdd y
        (elim.vecScale (BPair.ofNat (c + 1))
          (posCorootV t j)))).length = t.rank := by
      rw [poly.pnorm_length]
      exact elim.length_vecAdd y _ t.rank hy
        (by rw [elim.length_vecScale]; exact posCorootV_length t j)
    have hsplitF := subsetCount_off_split t j hj
      (poly.pnorm (elim.vecAdd y (elim.vecScale
        (BPair.ofNat (c + 1)) (posCorootV t j))))
      hkey (poly.pnorm_pnorm _) false
    have hsplitT := subsetCount_off_split t j hj
      (poly.pnorm (elim.vecAdd y (elim.vecScale
        (BPair.ofNat (c + 1)) (posCorootV t j))))
      hkey (poly.pnorm_pnorm _) true
    rw [Bool.not_false] at hsplitF
    rw [Bool.not_true] at hsplitT
    have hstep : (BPair.ofCounts
        (subsetCount t (poly.pnorm (elim.vecAdd y
          (elim.vecScale (BPair.ofNat (c + 1))
            (posCorootV t j)))) false)
        (subsetCount t (poly.pnorm (elim.vecAdd y
          (elim.vecScale (BPair.ofNat (c + 1))
            (posCorootV t j)))) true)).oneValue
        (BPair.ofCounts
            (subsetCountOff t j (poly.pnorm (elim.vecAdd y
              (elim.vecScale (BPair.ofNat (c + 1))
                (posCorootV t j)))) false)
            (subsetCountOff t j (poly.pnorm (elim.vecAdd y
              (elim.vecScale (BPair.ofNat (c + 1))
                (posCorootV t j)))) true)
          + BPair.ofCounts
            (subsetCountOff t j (poly.pnorm (elim.vecAdd y
              (elim.vecScale (BPair.ofNat (c + 2))
                (posCorootV t j)))) true)
            (subsetCountOff t j (poly.pnorm (elim.vecAdd y
              (elim.vecScale (BPair.ofNat (c + 2))
                (posCorootV t j)))) false)) := by
      rw [hsplitF, hsplitT, lineKey_step t y hy c]
      exact BPair.ofCounts_add _ _ _ _
    rw [ground.range_succ c]
    refine BPair.oneValue_trans (foldB_app _ (List.range c) [c]) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (lineCollect t F hj y hy c)
        (BPair.add_unit _)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) hstep) ?_
    rw [BPair.add_assoc]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.ofCounts_pair _ _)
          (BPair.oneValue_refl _))) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.unit_add _)

/-- The line telescope: the withdrawn fold's count pair at the
stepped key collects the subset fold's pairs along the line, the
end vanishing beyond `ρ`'s own height — `thm:memberchar`'s
cofactor identity at the `(Cof)` gaps, the coefficientwise
division descent.  The fold key's bound and the key's order are
the enumeration's frame, and the collection reads no norm of the
base key: `pnorm` absorbs its spelling at every stepped key. -/
theorem subsetCountOff_line (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (y : List BPair) (hy : y.length = t.rank) (cap : Nat)
    (hcap : dotB F (rhoV t) (rhoV t)
      < dotB F (rhoV t) (poly.pnorm (elim.vecAdd y
          (elim.vecScale (BPair.ofNat (cap + 1))
            (posCorootV t j))))) :
    (BPair.ofCounts
        (subsetCountOff t j
          (poly.pnorm (elim.vecAdd y (posCorootV t j))) false)
        (subsetCountOff t j
          (poly.pnorm (elim.vecAdd y (posCorootV t j))) true)).oneValue
      (ground.famFold BPair.add BPair.unit (fun l =>
        BPair.ofCounts
          (subsetCount t (poly.pnorm (elim.vecAdd y
            (elim.vecScale (BPair.ofNat (l + 1))
              (posCorootV t j)))) false)
          (subsetCount t (poly.pnorm (elim.vecAdd y
            (elim.vecScale (BPair.ofNat (l + 1))
              (posCorootV t j)))) true))
        (List.range cap)) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.add_unit _)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) ?_)
    (BPair.oneValue_symm (lineCollect t F hj y hy cap))
  rw [subsetCountOff_vanish t F hshape hgsym hrd hj _ hcap true,
    subsetCountOff_vanish t F hshape hgsym hrd hj _ hcap false]
  exact BPair.oneValue_symm BPair.ofCounts_zero

/-- A pair reading a join at a member's swap moves across: the
member reads the join's swap at the withdrawn slot. -/
private theorem cofMove_alg {p q m : BPair}
    (h : p.oneValue (q + m.swap)) :
    m.oneValue (p.swap + q) := by
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (ground.swap_congr h)
        (BPair.oneValue_of_eq (BPair.swap_add q m.swap).symm))
      (BPair.oneValue_refl q)) ?_
  rw [BPair.add_assoc, BPair.add_comm (m.swap.swap) q,
    ← BPair.add_assoc]
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.swap_add_null (BPair.oneValue_refl q))
      (BPair.oneValue_refl _)) ?_
  exact BPair.unit_add m

/-- The moved collection's closing arithmetic: the doubled swap
factor against the joined dots collects to the gap's read. -/
private theorem eulerMove_alg (x y z : BPair) :
    (z.swap * (y + y) + (x + y) * z).oneValue
      ((x + y.swap) * z) := by
  rw [BPair.swap_mul z (y + y), BPair.mul_comm z (y + y),
    BPair.right_distrib y y z, ← BPair.swap_add,
    BPair.right_distrib x y z,
    BPair.right_distrib x y.swap z, BPair.swap_mul y z,
    BPair.add_add_comm ((y * z).swap) ((y * z).swap)
      (x * z) (y * z),
    BPair.add_comm ((y * z).swap) (x * z)]
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.swap_add_null (BPair.oneValue_refl (y * z)))) ?_
  exact BPair.add_unit _

/-- The Euler collection at the moved keys: the withdrawn folds'
count pairs at the stepped keys collect against the roots' dots to
the key's dot against `ρ`'s own at the subset fold's counts —
`thm:memberchar`'s cross term at the `(Cof)` gaps.  The dot
vector's bound is `con:gentable`'s frame, a content a matched
list over the coordinates; the key's two shape binders are
load-bearing at their committed refusals off the `ρ`-key. -/
theorem subsetCountOff_euler_moved (t : gentable.Table)
    (F : FundData) (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrho : gentable.rhoRead t)
    (nu k : List BPair) (hnu : nu.length = t.rank)
    (hk : k.length = t.rank) (hkn : poly.pnorm k = k) :
    (ground.famFold BPair.add BPair.unit (fun j =>
      BPair.mul (dotB F nu (posCorootV t j))
        (BPair.ofCounts
          (subsetCountOff t j
            (poly.pnorm (elim.vecAdd k (posCorootV t j))) false)
          (subsetCountOff t j
            (poly.pnorm (elim.vecAdd k (posCorootV t j))) true)))
      (List.range t.posFolds.length)).oneValue
      (BPair.mul
        (BPair.add (dotB F nu k) ((dotB F nu (rhoV t)).swap))
        (BPair.ofCounts (subsetCount t k false)
          (subsetCount t k true))) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j =>
        BPair.mul (dotB F nu (posCorootV t j))
          ((BPair.ofCounts (subsetCount t k false)
            (subsetCount t k true)).swap)
        + BPair.mul (dotB F nu (posCorootV t j))
          (BPair.ofCounts (subsetCountOff t j k false)
            (subsetCountOff t j k true)))
      (List.range t.posFolds.length)
      (fun j hj => ?_)) ?_
  · have hjN : j < t.posFolds.length := ground.ltOfMem hj
    have hCF := subsetCount_off_split t j hjN k hk hkn false
    have hCT := subsetCount_off_split t j hjN k hk hkn true
    rw [Bool.not_false] at hCF
    rw [Bool.not_true] at hCT
    have hPhi : (BPair.ofCounts (subsetCount t k false)
        (subsetCount t k true)).oneValue
        (BPair.ofCounts (subsetCountOff t j k false)
            (subsetCountOff t j k true)
          + (BPair.ofCounts
            (subsetCountOff t j
              (poly.pnorm (elim.vecAdd k (posCorootV t j))) false)
            (subsetCountOff t j
              (poly.pnorm (elim.vecAdd k
                (posCorootV t j))) true)).swap) := by
      rw [hCF, hCT, BPair.ofCounts_swap]
      exact BPair.ofCounts_add _ _ _ _
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (cofMove_alg hPhi)) ?_
    exact BPair.oneValue_of_eq
      (BPair.left_distrib (dotB F nu (posCorootV t j)) _ _)
  refine BPair.oneValue_trans (ground.foldB_add _ _
    (List.range t.posFolds.length)) ?_
  rw [ground.famFold_congr_all BPair.add BPair.unit
    (fun j => BPair.mul (dotB F nu (posCorootV t j))
      ((BPair.ofCounts (subsetCount t k false)
        (subsetCount t k true)).swap))
    (fun j => BPair.mul
      ((BPair.ofCounts (subsetCount t k false)
        (subsetCount t k true)).swap)
      (dotB F nu (posCorootV t j)))
    (fun j => BPair.mul_comm _ _) (List.range t.posFolds.length)]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (ground.foldB_mul_left _ _
        (List.range t.posFolds.length))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (sumRootDots t F hshape hgsym hrho nu hnu)))
      (subsetCountOff_euler t F hshape hgsym hrho nu k hnu)) ?_
  exact eulerMove_alg (dotB F nu k) (dotB F nu (rhoV t))
    (BPair.ofCounts (subsetCount t k false) (subsetCount t k true))

/-- A zipped fold at rows pairing above the unit sums above it. -/
private theorem zipDot_nonneg (x : List BPair) :
    ∀ (f : List Nat) (rows : List (List BPair)),
    (∀ l, l < rows.length →
      BPair.unit ≤ elim.dotP (getAt [] rows l) x) →
    BPair.unit ≤ BPair.sum (List.zipWith (fun c row =>
      BPair.ofNat c * elim.dotP row x) f rows)
  | [], _, _ => ground.leB_refl _
  | _ :: _, [], _ => ground.leB_refl _
  | c :: f, row :: rows, h => by
    refine ground.leB_congr_right
      (BPair.oneValue_symm (BPair.sum_cons _ _)) ?_
    refine ground.unitLeAdd
      (ground.leB_unit_mul c (h 0 (Nat.succ_pos _))) ?_
    exact zipDot_nonneg x f rows
      (fun l hl => h (l + 1) (Nat.succ_lt_succ hl))

/-- The diagonal read at a Cartan row: the row's pairing against
the Gram's action reads the scaled length at the key's own entry
(`thm:assembly`'s pin, the halved products at the Gram's defining
read). -/
theorem diagRow (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (v : List BPair) (hv : v.length = t.rank) (l : Nat)
    (hl : l < t.cartan.length) :
    (elim.dotP (getAt [] t.cartan l)
        (elim.matVec F.gram v)).oneValue
      (BPair.ofNat (F.scale * getAt 0 t.lenNums l)
        * getAt BPair.unit v l) := by
  have hln : l < t.rank := by
    rw [← cartanLen t F hgram]
    exact hl
  have hchain : poly.oneValue
      (elim.matVec t.cartan (elim.matVec F.gram v))
      (elim.matVec (ground.matOf t.rank t.rank (fun k j =>
        if k == j then
          BPair.ofNat (F.scale * getAt 0 t.lenNums k)
        else BPair.unit)) v) :=
    poly.oneValue_trans
      (poly.oneValue_symm
        (elim.matVec_matMul t.cartan F.gram t.rank
          (elim.rowsLen_of_allP (fun _ hr => ground.beqEqOf hr) F.gram hshape.2.1) v hv))
      (elim.matVec_matOne _ _ v hgram)
  have hent := poly.oneValue_getAt l hchain
  rw [show elim.matVec t.cartan (elim.matVec F.gram v)
      = t.cartan.map (fun r => elim.dotN r
          (elim.matVec F.gram v)) from rfl,
    ground.getAt_map [] BPair.unit _ t.cartan l hl,
    show elim.matVec (ground.matOf t.rank t.rank (fun k j =>
        if k == j then
          BPair.ofNat (F.scale * getAt 0 t.lenNums k)
        else BPair.unit)) v
      = (ground.matOf t.rank t.rank (fun k j =>
          if k == j then
            BPair.ofNat (F.scale * getAt 0 t.lenNums k)
          else BPair.unit)).map (fun r => elim.dotN r v)
      from rfl,
    ground.getAt_map [] BPair.unit _ _ l
      (by rw [ground.matOf_length]; exact hln),
    ground.matOf_row ([] : List BPair) t.rank t.rank _ l hln] at hent
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (elim.dotN_read _ _)) ?_
  refine BPair.oneValue_trans hent ?_
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (elim.dotP_rowRange _ t.rank v hv) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _ (fun j =>
      if j == l then
        BPair.ofNat (F.scale * getAt 0 t.lenNums l)
          * getAt BPair.unit v l
      else BPair.unit)
      (List.range t.rank) (fun j _ => ?_)) ?_
  · by_cases hjl : j = l
    · rw [if_pos (ground.eqBeqOf (hjl.symm ▸ rfl)),
        if_pos (ground.eqBeqOf hjl), hjl]
      exact BPair.oneValue_refl _
    · rw [if_neg (fun hc => hjl (ground.beqEqOf hc).symm),
        if_neg (fun hc => hjl (ground.beqEqOf hc))]
      exact BPair.unit_mul _
  · exact ground.foldB_pickBeq l _ (List.range t.rank)
      (ground.countOf_range_one hln)


/-- The simple's own pairing: its coroot vector is the reflecting
Cartan row, so the pairing reads the scaled length at the key's own
coordinate (`prop:row`'s tie at `con:sertables`' simple
positions). -/
theorem dotB_simple (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hsp : simplePosRead t F) {i : Nat} (hi : i < t.rank)
    (z : List BPair) (hz : z.length = t.rank) :
    (dotB F (posCorootV t (ground.getAt 0 F.simplePos i)) z).oneValue
      (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
        * ground.getAt BPair.unit z i) := by
  refine BPair.oneValue_trans ?_
    (diagRow t F hshape hgram z hz i
      (by rw [cartanLen t F hgram]; exact hi))
  show (elim.dotP (posCorootV t (ground.getAt 0 F.simplePos i))
    (elim.matVec F.gram z)).oneValue _
  refine elim.dotP_congr_left _ _ (elim.matVec F.gram z) (fun q hq => ?_)
  have hqr : q < t.rank := by
    rw [← ((elim.matVec_length F.gram z).trans hshape.1)]
    exact hq
  show (ground.getAt BPair.unit ((List.range t.rank).map
    (gentable.corootAt t (ground.getAt [] t.posFolds
      (ground.getAt 0 F.simplePos i)))) q).oneValue _
  rw [ground.getAt_map_range BPair.unit _ t.rank q, if_pos hqr,
    hsp i hi]
  exact gentable.corootAt_oneHot t i q hi

/-- The simple's normed coroot vector is its Cartan row's, the
one-hot fold read entrywise (`con:sertables`' simple positions). -/
theorem simpleRow (t : gentable.Table) (F : FundData)
    (hsp : simplePosRead t F) {i : Nat} (hi : i < t.rank) :
    poly.pnorm (posCorootV t (ground.getAt 0 F.simplePos i))
      = poly.pnorm (cartRowV t i) := by
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [posCorootV_length, cartRowV_length]
  · refine poly.oneValue_of_entries _ _
      (by rw [posCorootV_length, cartRowV_length])
      (fun j hj => ?_)
    have hjr : j < t.rank := by
      rw [posCorootV_length] at hj
      exact hj
    show (ground.getAt BPair.unit ((List.range t.rank).map
      (gentable.corootAt t (ground.getAt [] t.posFolds
        (ground.getAt 0 F.simplePos i)))) j).oneValue _
    rw [ground.getAt_map_range BPair.unit _ t.rank j, if_pos hjr,
      hsp i hi, cartRowV_getAt t i j hjr]
    exact gentable.corootAt_oneHot t i j hi

/-- The simple fold's pairing at a key: the counts against the
scaled lengths at the key's own coordinates, the Gram's defining
diagonal read per row. -/
theorem dotB_cartanFold (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F) (c : List Nat)
    (hcf : (cartanFold t c).length = t.rank)
    (z : List BPair) (hz : z.length = t.rank) :
    (dotB F (cartanFold t c) z).oneValue
      (ground.bsum (fun i => BPair.ofNat (ground.getAt 0 c i)
        * (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)
          * ground.getAt BPair.unit z i)) (List.range t.rank)) := by
  have hG : (elim.matVec F.gram z).length = t.rank :=
    (elim.matVec_length F.gram z).trans hshape.1
  have hrepl : (elim.dotP (List.replicate t.rank BPair.unit)
      (elim.matVec F.gram z)).oneValue BPair.unit :=
    elim.dotP_replL t.rank (elim.matVec F.gram z)
  refine BPair.oneValue_trans (dotP_foldl
    (fun i => (ground.getAt [] t.cartan i).map
      (BPair.mul (BPair.ofNat (ground.getAt 0 c i))))
    (elim.matVec F.gram z)
    (List.range t.rank) (List.replicate t.rank BPair.unit)
    (by rw [hG]; exact Nat.le_of_eq hcf.symm)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr hrepl (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (BPair.unit_add _) ?_
  refine ground.foldB_congr_members _ _ (List.range t.rank)
    (fun i hi => ?_)
  have hir : i < t.rank := ground.ltOfMem hi
  have hsc : (elim.dotP ((ground.getAt [] t.cartan i).map
      (BPair.mul (BPair.ofNat (ground.getAt 0 c i))))
      (elim.matVec F.gram z)).oneValue
      (BPair.ofNat (ground.getAt 0 c i)
        * elim.dotP (ground.getAt [] t.cartan i)
            (elim.matVec F.gram z)) :=
    elim.dotP_scaleL (BPair.ofNat (ground.getAt 0 c i))
      (ground.getAt [] t.cartan i) (elim.matVec F.gram z)
  exact BPair.oneValue_trans hsc
    (BPair.mul_congr (BPair.oneValue_refl _)
      (diagRow t F hshape hgram z hz i
        (by rw [cartanLen t F hgram]; exact hir)))

/-- A key at or above the sum's unit at every place pairs against
`ρ` at its upper side or equal members (`thm:assembly`'s pin:
twice the read the fold of the member pairings at `2ρ` the root
fold, each the halved products' fold over its own natural fold,
every summand the length's natural multiple at a coroot pair on
its upper side or equal members). -/
theorem dotB_dom_nonneg (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hrho : gentable.rhoRead t)
    (v : List BPair) (hv : v.length = t.rank)
    (hpos : ∀ k, k < t.rank →
      BPair.unit ≤ getAt BPair.unit v k) :
    BPair.unit ≤ dotB F v (rhoV t) := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hGv : (elim.matVec F.gram v).length = t.rank := by
    show (F.gram.map _).length = _
    rw [ground.length_map]
    exact hshape.1
  have hslot : (dotB F v (rhoV t)).oneValue
      (elim.dotP (rhoV t) (elim.matVec F.gram v)) := by
    show (elim.dotP v (elim.matVec F.gram (rhoV t))).oneValue _
    rw [elim.dotP_comm v (elim.matVec F.gram (rhoV t))]
    refine BPair.oneValue_trans
      (elim.dotP_matVec_transpose t.rank F.gram (rhoV t) v
        (elim.rowsLen_of_allP (fun _ hr => ground.beqEqOf hr) F.gram hshape.2.1) hrl
        (hv.trans hshape.1.symm)) ?_
    rw [elim.dotP_comm (rhoV t)
        (elim.matVec (elim.transposeM F.gram) v),
      elim.dotP_comm (rhoV t) (elim.matVec F.gram v)]
    exact elim.dotP_oneValue_left _ _ (rhoV t)
      (elim.matVec_matOne _ _ v hgsym)
  refine ground.leB_congr_right
    (BPair.oneValue_symm hslot) ?_
  refine ground.unitLeUnscale (k := 2) (by decide +kernel)
    (ground.leB_congr_right (BPair.oneValue_symm
      (BPair.oneValue_trans (ground.ofNat_succ_mul 1 _)
        (BPair.add_congr
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.mul_comm _ _))
            (BPair.mul_ofNat_one _))
          (BPair.oneValue_refl _)))) ?_)
  refine ground.leB_congr_right
    (elim.dotP_vecAdd_left (rhoV t) (rhoV t) (elim.matVec F.gram v)
      (Nat.le_of_eq (hGv.trans hrl.symm))
      (Nat.le_of_eq (hGv.trans hrl.symm))) ?_
  refine ground.leB_congr_right
    (BPair.oneValue_symm
      (elim.dotP_congr_left _ ((List.range t.rank).map
          (gentable.rho2Coroot t))
        (elim.matVec F.gram v) (fun j hj => ?_))) ?_
  · have hjr : j < t.rank := by rw [← hGv]; exact hj
    rw [elim.getAt_vecAdd (rhoV t) (rhoV t) j
        (by rw [hrl]; exact hjr) (by rw [hrl]; exact hjr),
      rhoV_getAt t j hjr,
      ground.getAt_map 0 BPair.unit _ (List.range t.rank) j
        (by rw [ground.length_range]; exact hjr),
      ground.getAt_range t.rank j hjr]
    exact BPair.oneValue_trans
      (show (BPair.ofNat 1 + BPair.ofNat 1).oneValue
        (BPair.ofNat 2) by decide +kernel)
      (BPair.oneValue_symm (rhoTwo t hrho j hjr))
  · refine ground.leB_congr_right
      (BPair.oneValue_symm
        (dotP_foldSum t t.rank (elim.matVec F.gram v) hGv
          t.posFolds)) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm (ground.BPair.sum_map _ t.posFolds)) ?_
    refine ground.foldB_nonneg _ t.posFolds (fun f _ => ?_)
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (elim.dotP_zipSum t.rank (elim.matVec F.gram v) hGv f
          t.cartan)) ?_
    refine zipDot_nonneg (elim.matVec F.gram v) f t.cartan
      (fun l hl => ?_)
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (diagRow t F hshape hgram v hv l hl)) ?_
    exact ground.leB_unit_mul _
      (hpos l (by rw [← cartanLen t F hgram]; exact hl))

/-- A dominant key beyond the unit dominates `ρ`'s own dot: the key
less `ρ` sits at or above the unit at every place, and its dot joins
`ρ`'s. -/
theorem dom_of_beyond (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hrr : gentable.rhoRead t)
    (y : List BPair) (hy : y.length = t.rank)
    (hb : ∀ k, k < t.rank → BPair.unit < getAt BPair.unit y k) :
    dotB F (rhoV t) (rhoV t) ≤ dotB F y (rhoV t) := by
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hneg : poly.neg (rhoV t)
      = List.replicate t.rank ((BPair.ofNat 1).swap) := by
    show (List.replicate t.rank (BPair.ofNat 1)).map BPair.swap = _
    rw [ground.map_replicate]
  have hnl : (poly.neg (rhoV t)).length = t.rank := by
    rw [poly.length_neg]
    exact hrho
  have hnu : (elim.vecAdd y (poly.neg (rhoV t))).length = t.rank :=
    elim.length_vecAdd y _ t.rank hy hnl
  have hent : ∀ j, j < t.rank →
      getAt BPair.unit (elim.vecAdd y (poly.neg (rhoV t))) j
        = getAt BPair.unit y j + (BPair.ofNat 1).swap := by
    intro j hj
    rw [elim.getAt_vecAdd y _ j (by rw [hy]; exact hj)
        (by rw [hnl]; exact hj), hneg,
      ground.getAt_replicate BPair.unit ((BPair.ofNat 1).swap)
        t.rank j hj]
  have hnn : BPair.unit ≤ dotB F (elim.vecAdd y (poly.neg (rhoV t)))
      (rhoV t) := by
    refine dotB_dom_nonneg t F hshape hgram hgsym hrr _ hnu
      (fun k hk => ?_)
    rw [hent k hk]
    refine ground.leB_congr_left ?_
      (ground.leB_add (ground.oneLeOfUnitLt (hb k hk))
        (ground.leB_refl ((BPair.ofNat 1).swap)))
    rw [BPair.add_comm]
    exact BPair.swap_add_null (BPair.oneValue_refl (BPair.ofNat 1))
  have hsplit : (dotB F y (rhoV t)).oneValue
      (dotB F (elim.vecAdd y (poly.neg (rhoV t))) (rhoV t)
        + dotB F (rhoV t) (rhoV t)) := by
    show (elim.dotP y (gramRho t F)).oneValue
      (elim.dotP (elim.vecAdd y (poly.neg (rhoV t))) (gramRho t F)
        + elim.dotP (rhoV t) (gramRho t F))
    refine BPair.oneValue_trans ?_
      (elim.dotP_addE _ (rhoV t) (gramRho t F) (hnu.trans hrho.symm))
    refine elim.dotP_oneValue_left y _ (gramRho t F) ?_
    refine poly.oneValue_symm (poly.oneValue_of_entries _ _
      ((elim.length_vecAdd _ (rhoV t) t.rank hnu hrho).trans hy.symm)
      (fun j hj => ?_))
    have hjr : j < t.rank := by
      rw [elim.length_vecAdd _ (rhoV t) t.rank hnu hrho] at hj
      exact hj
    rw [elim.getAt_vecAdd _ (rhoV t) j (by rw [hnu]; exact hjr)
        (by rw [hrho]; exact hjr), hent j hjr, rhoV_getAt t j hjr,
      BPair.add_assoc]
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.swap_add_null (BPair.oneValue_refl (BPair.ofNat 1))))
      (BPair.add_unit _)
  exact ground.leB_congr_right (BPair.oneValue_symm hsplit)
    (ground.leB_congr_left (BPair.unit_add _)
      (ground.leB_add hnn (ground.leB_refl _)))


/-! The identifications (`thm:assembly`'s pin (b)): a dominant key
beyond the unit is `ρ` on both sides — the subset fold's occupied
family refuses at the support read's positive dots, and the Weyl
member's witness fold clears. -/

/-- The vacant family's key is `ρ` itself. -/
private theorem eKey_nil (t : gentable.Table) : eKey t [] = rhoV t := by
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hz : (List.replicate t.rank BPair.unit).length = t.rank :=
    ground.length_replicate BPair.unit t.rank
  show poly.pnorm (elim.vecAdd (rhoV t)
    (poly.neg (List.replicate t.rank BPair.unit))) = rhoV t
  rw [poly.neg_repl]
  refine Eq.trans (poly.pnorm_congr _ (rhoV t) ?_ ?_) (pnorm_rhoV t)
  · rw [elim.length_vecAdd (rhoV t) _ t.rank hrho hz]
    exact hrho.symm
  · exact elim.vecAdd_null_right (rhoV t) (List.replicate t.rank BPair.unit)
      (by rw [ground.length_replicate]; exact hrho)
      (poly.unitTail_replicate t.rank)

/-- A family whose key dominates `ρ`'s dot is vacant: an occupied
member's positive dot would carry the key's own dot below `ρ`'s. -/
private theorem phi_top (t : gentable.Table) (F : FundData)
    (hrd : rhoDotRead t F) (S : List Nat)
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length)))
    (y : List BPair) (hkey : eKey t S = y)
    (hdomy : dotB F (rhoV t) (rhoV t) ≤ dotB F y (rhoV t)) :
    S = [] := by
  cases S with
  | nil => rfl
  | cons j S' =>
    exfalso
    have hmem : ∀ x, 0 < ground.countOf x (j :: S') →
        BPair.unit < dotB F (posCorootV t x) (rhoV t) := fun x hx =>
      hrd x (ground.ltOfMem (ground.sublists_entries (List.range t.posFolds.length)
        (j :: S') hS x hx))
    have hpos : BPair.unit < ground.famFold BPair.add BPair.unit
        (fun j => dotB F (posCorootV t j) (rhoV t)) (j :: S') := by
      show BPair.unit < dotB F (posCorootV t j) (rhoV t)
        + ground.famFold BPair.add BPair.unit
            (fun j => dotB F (posCorootV t j) (rhoV t)) S'
      exact ground.unitLtAdd
        (hmem j (by rw [ground.countOf_head]; exact Nat.succ_pos _))
        (ground.foldB_nonneg _ S' (fun x hx =>
          Or.inr (hmem x (ground.countOf_cons_pos hx))))
    have hek := dotB_eKey t F (j :: S')
    rw [hkey] at hek
    refine ground.leB_not_lt
      (ground.leB_congr_left (BPair.oneValue_symm hek) hdomy) ?_
    refine BPair.lt_congr (BPair.unit_add _)
      (BPair.oneValue_of_eq (BPair.add_comm _ (dotB F y (rhoV t))))
      (ground.ltB_add hpos (ground.leB_refl (dotB F y (rhoV t))))

/-- The witness fold's own vector at a member's key. -/
private def witFold (t : gentable.Table) (wits : List (List Nat))
    (k : Nat) : List BPair :=
  elim.vsum t.rank
    (fun i => (getAt [] t.cartan i).map
      (BPair.mul (BPair.ofNat (getAt 0 (getAt [] wits k) i))))
    (List.range t.rank)

/-- The accumulating fold at unit-valued members reads its seed. -/
private theorem foldRun (f : Nat → List BPair) : ∀ (l : List Nat)
    (acc : List BPair),
    (∀ i, 0 < ground.countOf i l → ∀ j,
      (getAt BPair.unit (f i) j).oneValue BPair.unit) →
    ∀ j, j < (l.foldl (fun a i => elim.vecAdd a (f i)) acc).length →
    (getAt BPair.unit
        (l.foldl (fun a i => elim.vecAdd a (f i)) acc) j).oneValue
      (getAt BPair.unit acc j)
  | [], _, _, _, _ => BPair.oneValue_refl _
  | i :: l, acc, h, j, hj => by
    have hj' : j < (elim.vecAdd acc (f i)).length :=
      Nat.lt_of_lt_of_le hj (foldVA_len f l _)
    refine BPair.oneValue_trans
      (foldRun f l (elim.vecAdd acc (f i))
        (fun x hx => h x (ground.countOf_cons_pos hx)) j hj) ?_
    rw [elim.getAt_vecAdd acc (f i) j
      (Nat.lt_of_lt_of_le hj' (vecAdd_lenL acc (f i)))
      (Nat.lt_of_lt_of_le hj' (vecAdd_lenR acc (f i)))]
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (h i (by rw [ground.countOf_head]; exact Nat.succ_pos _) j))
      (BPair.add_unit _)

/-- A Weyl member whose key dominates `ρ`'s dot is `ρ`: every
witness count clears, so the member's key joins the unit family
back to `ρ`. -/
private theorem w_beyond (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (hdom : wDomRead t W wits)
    (k : Nat) (hk : k < W.length)
    (y : List BPair) (hy : y.length = t.rank)
    (hny : poly.pnorm y = y)
    (hkey : (getAt ([], false) W k).1 = y)
    (hdomy : dotB F (rhoV t) (rhoV t) ≤ dotB F y (rhoV t)) :
    y = rhoV t := by
  have hrho : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hwd := dotB_wDom t F W wits hshape hsp hdom k hk
  rw [hkey] at hwd
  have hsum : ∀ i, i < t.rank → BPair.unit <
      dotB F (posCorootV t (getAt 0 F.simplePos i)) (rhoV t) :=
    fun i hi => hrd _ (simplePos_lt t F hshape hi)
  have hnn : ∀ i, 0 < ground.countOf i (List.range t.rank) →
      BPair.unit ≤ BPair.ofNat (getAt 0 (getAt [] wits k) i)
        * dotB F (posCorootV t (getAt 0 F.simplePos i)) (rhoV t) :=
    fun i hi => ground.leB_unit_mul _ (Or.inr (hsum i (ground.ltOfMem hi)))
  have hle : ground.famFold BPair.add BPair.unit
      (fun i => BPair.ofNat (getAt 0 (getAt [] wits k) i)
        * dotB F (posCorootV t (getAt 0 F.simplePos i)) (rhoV t))
      (List.range t.rank) ≤ BPair.unit :=
    ground.leB_cancelL (x := dotB F y (rhoV t))
      (ground.leB_congr_right
        (BPair.oneValue_symm (BPair.add_unit (dotB F y (rhoV t))))
        (ground.leB_congr_left (BPair.oneValue_symm hwd) hdomy))
  have hzero : ∀ i, i < t.rank → getAt 0 (getAt [] wits k) i = 0 := by
    intro i hi
    cases hw : getAt 0 (getAt [] wits k) i with
    | zero => rfl
    | succ m =>
      exfalso
      have hmemle := foldB_mem_le _ (List.range t.rank) hnn i
        (by rw [ground.countOf_range_one hi]; exact Nat.succ_pos 0)
      refine ground.leB_not_lt (ground.leB_trans hmemle hle) ?_
      refine ground.ltB_trans_le (hsum i hi) ?_
      refine ground.leB_congr_left ?_
        (ground.leB_scale_mono (a := 1)
          (b := getAt 0 (getAt [] wits k) i)
          (by rw [hw]; exact Nat.succ_le_succ (Nat.zero_le m))
          (Or.inr (hsum i hi)))
      exact BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
        (BPair.mul_ofNat_one _)
  have heq : poly.pnorm (elim.vecAdd y (witFold t wits k)) = rhoV t := by
    have h := hdom.2 k hk
    rw [hkey] at h
    exact h
  have hlen : (elim.vecAdd y (witFold t wits k)).length = t.rank := by
    rw [← poly.pnorm_length, heq]
    exact hrho
  have hGge : t.rank ≤ (witFold t wits k).length :=
    Nat.le_trans (Nat.le_of_eq hlen.symm) (vecAdd_lenR _ _)
  have hGunit : ∀ j, j < t.rank →
      (getAt BPair.unit (witFold t wits k) j).oneValue BPair.unit := by
    intro j hj
    refine BPair.oneValue_trans
      (foldRun _ (List.range t.rank) (List.replicate t.rank BPair.unit)
        (fun i hi j' => ?_) j (Nat.lt_of_lt_of_le hj hGge)) ?_
    · by_cases hj' : j' < (getAt [] t.cartan i).length
      · rw [ground.getAt_map BPair.unit BPair.unit
          (BPair.mul (BPair.ofNat (getAt 0 (getAt [] wits k) i)))
          (getAt [] t.cartan i) j' hj', hzero i (ground.ltOfMem hi)]
        exact BPair.unit_mul _
      · rw [ground.getAt_over BPair.unit _ j'
          (Nat.le_of_not_lt (fun hc => hj' (by
            rw [ground.length_map] at hc
            exact hc)))]
        exact BPair.oneValue_refl _
    · rw [ground.getAt_replicate_self BPair.unit t.rank j]
      exact BPair.oneValue_refl _
  have hone : poly.oneValue (elim.vecAdd y (witFold t wits k)) y := by
    refine poly.oneValue_of_entries _ _ (hlen.trans hy.symm) (fun j hj => ?_)
    have hjr : j < t.rank := by
      rw [hlen] at hj
      exact hj
    rw [elim.getAt_vecAdd y (witFold t wits k) j
      (by rw [hy]; exact hjr) (Nat.lt_of_lt_of_le hjr hGge)]
    exact BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (hGunit j hjr))
      (BPair.add_unit _)
  exact (((poly.pnorm_congr _ y (hlen.trans hy.symm) hone).trans
    hny).symm).trans heq

/-- The vacant family sits once in the enumeration. -/
private theorem countOf_nil_sublists : ∀ l : List Nat,
    ground.countOf ([] : List Nat) (ground.sublistsOf l) = 1
  | [] => rfl
  | a :: l => by
    show ground.countOf ([] : List Nat)
      (ground.sublistsOf l ++ (ground.sublistsOf l).map (fun T => a :: T)) = 1
    rw [ground.countOf_append,
      ground.countOf_nil_consMap a (ground.sublistsOf l),
      countOf_nil_sublists l]

/-- The subset fold's reads at `ρ`: the vacant family alone, at the
even side (`thm:assembly`'s identification at the top key). -/
private theorem subsetCount_rho (t : gentable.Table) (F : FundData)
    (hrd : rhoDotRead t F) :
    subsetCount t (poly.pnorm (rhoV t)) false = 1
      ∧ subsetCount t (poly.pnorm (rhoV t)) true = 0 := by
  have hnil : ∀ S, 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length)) →
      (if eKey t S = poly.pnorm (rhoV t) then (1 : Nat) else 0)
        = (if ([] : List Nat) = S then 1 else 0) := by
    intro S hS
    by_cases hSn : ([] : List Nat) = S
    · rw [if_pos hSn, ← hSn,
        if_pos (show eKey t [] = poly.pnorm (rhoV t) from by
          rw [eKey_nil, pnorm_rhoV])]
    · have hne : ¬ (eKey t S = poly.pnorm (rhoV t)) := fun he =>
        hSn (phi_top t F hrd S hS (poly.pnorm (rhoV t)) he
          (by rw [pnorm_rhoV]; exact ground.leB_refl _)).symm
      rw [if_neg hne, if_neg hSn]
  constructor
  · show ground.famFold Nat.add 0
      (fun S => if places.sideOf S = false then
        (if eKey t S = poly.pnorm (rhoV t) then 1 else 0) else 0)
      (ground.sublistsOf (List.range t.posFolds.length)) = 1
    rw [ground.famFold_congr_members Nat.add 0 _
      (fun S => if ([] : List Nat) = S then (1 : Nat) else 0)
      (ground.sublistsOf (List.range t.posFolds.length)) (fun S hS => ?_),
      ← ground.countOf_fold ([] : List Nat),
      countOf_nil_sublists (List.range t.posFolds.length)]
    by_cases hSn : ([] : List Nat) = S
    · rw [← hSn, show places.sideOf ([] : List Nat) = false from rfl,
        if_pos rfl, hnil [] (by rw [← hSn] at hS; exact hS),
        if_pos rfl]
    · rw [hnil S hS, if_neg hSn]
      by_cases hp : places.sideOf S = false
      · rw [if_pos hp]
      · rw [if_neg hp]
  · show ground.famFold Nat.add 0
      (fun S => if places.sideOf S = true then
        (if eKey t S = poly.pnorm (rhoV t) then 1 else 0) else 0)
      (ground.sublistsOf (List.range t.posFolds.length)) = 0
    rw [ground.famFold_congr_members Nat.add 0 _
      (fun _ => (0 : Nat))
      (ground.sublistsOf (List.range t.posFolds.length)) (fun S hS => ?_)]
    · exact ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) _
    · by_cases hSn : ([] : List Nat) = S
      · rw [← hSn, show places.sideOf ([] : List Nat) = false from rfl,
          if_neg (ground.boolNe rfl)]
      · rw [hnil S hS, if_neg hSn]
        by_cases hp : places.sideOf S = true
        · rw [if_pos hp]
        · rw [if_neg hp]


/-! The walk (`thm:assembly`'s conclusion): `Φ`'s read at a key is
its dominant image's up to the walk's parity, the walk raising at a
lower-side simple pair and closing at the gap's count, with the
dominant images pinned — the fixed key at a simple pair the unit,
and `ρ` itself beyond it. -/

/-- The key's occupancy: the two folds' graded counts joined. -/
private def occAt (t : gentable.Table) (W : List (List BPair × Bool))
    (y : List BPair) : Nat :=
  subsetCount t y false + subsetCount t y true
    + wCount W y false + wCount W y true

/-- An occupied subset count names the family whose key it is. -/
private theorem subsetCount_witness (t : gentable.Table)
    (y : List BPair) (s : Bool) (h : 0 < subsetCount t y s) :
    ∃ S, 0 < ground.countOf S
        (ground.sublistsOf (List.range t.posFolds.length))
      ∧ eKey t S = y := by
  obtain ⟨S, hS, hv⟩ := ground.famFold_pos_witness _
    (ground.sublistsOf (List.range t.posFolds.length)) h
  refine ⟨S, hS, ?_⟩
  have hv' : 0 < (if places.sideOf S = s then
    (if eKey t S = y then 1 else 0) else 0) := hv
  by_cases hk : eKey t S = y
  · exact hk
  · exfalso
    by_cases hp : places.sideOf S = s
    · rw [if_pos hp, if_neg hk] at hv'
      exact Nat.lt_irrefl 0 hv'
    · rw [if_neg hp] at hv'
      exact Nat.lt_irrefl 0 hv'

/-- An occupied Weyl count names the member's position. -/
private theorem wCount_witness (W : List (List BPair × Bool))
    (y : List BPair) (s : Bool) (h : 0 < wCount W y s) :
    ∃ k, k < W.length ∧ (getAt ([], false) W k).1 = y := by
  obtain ⟨k, hk, he⟩ := ground.getAt_of_mem (([], false))
    (ground.mem_of_countOf_pos (y, s) W h)
  exact ⟨k, hk, by rw [he]⟩

/-- An occupied key's dot sits at or below `ρ`'s own
(`thm:assembly`'s support tier). -/
private theorem dom_of_occ (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (hdom : wDomRead t W wits)
    (y : List BPair) (hocc : 0 < occAt t W y) :
    dotB F y (rhoV t) ≤ dotB F (rhoV t) (rhoV t) := by
  have hphi : ∀ s, 0 < subsetCount t y s →
      dotB F y (rhoV t) ≤ dotB F (rhoV t) (rhoV t) := by
    intro s hs
    obtain ⟨S, hS, hkey⟩ := subsetCount_witness t y s hs
    have hek := dotB_eKey t F S
    rw [hkey] at hek
    exact ground.dom_of_split hek (ground.foldB_nonneg _ S (fun x hx =>
      Or.inr (hrd x (ground.ltOfMem (ground.sublists_entries
        (List.range t.posFolds.length) S hS x hx)))))
  have hwey : ∀ s, 0 < wCount W y s →
      dotB F y (rhoV t) ≤ dotB F (rhoV t) (rhoV t) := by
    intro s hs
    obtain ⟨k, hk, hkey⟩ := wCount_witness W y s hs
    have hwd := dotB_wDom t F W wits hshape hsp hdom k hk
    rw [hkey] at hwd
    exact ground.dom_of_split hwd (ground.foldB_nonneg _ (List.range t.rank)
      (fun i hi => ground.leB_unit_mul _
        (Or.inr (hrd _ (simplePos_lt t F hshape (ground.ltOfMem hi))))))
  have h3 : 0 < subsetCount t y false + subsetCount t y true
      + wCount W y false + wCount W y true := hocc
  cases ground.posOr h3 with
  | inr hD => exact hwey true hD
  | inl h2 =>
    cases ground.posOr h2 with
    | inr hC => exact hwey false hC
    | inl h1 =>
      cases ground.posOr h1 with
      | inl hA => exact hphi false hA
      | inr hB => exact hphi true hB

/-- The rise's margin (`thm:assembly`'s walk): at a lower-side entry
the reflection raises the key's dot by at least one. -/
theorem rise_gap (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (i : Nat) (hi : i < t.rank)
    (y : List BPair) (hy : y.length = t.rank)
    (hlt : getAt BPair.unit y i < BPair.unit) :
    dotB F y (rhoV t) + BPair.ofNat 1
      ≤ dotB F (reflAt t i y) (rhoV t) :=
  ground.leB_congr_right
    (BPair.oneValue_symm (dotB_rise t F hsp i hi y hy))
    (ground.leB_add (ground.leB_refl _)
      (ground.oneLeOfUnitLt (ground.unitLtMul (ground.ltB_swap hlt)
        (hrd _ (simplePos_lt t F hshape hi)))))

/-- At a dominant unbalanced key the pins read `ρ`: a key a letter
fixes reads its two counts at one value, so an unbalanced key sits
beyond the unit at every pair, where the support folds' positive
dots identify it with `ρ`. -/
private theorem wOff_dom (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hrr : gentable.rhoRead t)
    (hsp : simplePosRead t F) (hsq : reflSquareRead t)
    (hrd : rhoDotRead t F) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (y : List BPair)
    (hy : y.length = t.rank) (hny : poly.pnorm y = y)
    (hne : wCount W y true ≠ wCount W y false)
    (hlow : ∀ k, k < t.rank → BPair.unit ≤ getAt BPair.unit y k) :
    (dotB F y y).oneValue (dotB F (rhoV t) (rhoV t)) := by
  by_cases hex : ∃ p, p + 1 < t.rank + 1
      ∧ (getAt BPair.unit y p).oneValue BPair.unit
  · obtain ⟨p, hp, hu⟩ := hex
    exfalso
    have hpr : p < t.rank := Nat.lt_of_succ_lt_succ hp
    have hfix : reflAt t p y = y := reflAt_fix t p hpr y hy hny hu
    have hw := wCount_refl t W hclose hsq p hpr y hy hny true
    rw [hfix] at hw
    exact hne hw
  · have hb : ∀ k, k < t.rank → BPair.unit < getAt BPair.unit y k :=
      fun k hk => ground.ltOfLeOff (hlow k hk)
        (fun he => hex ⟨k, Nat.succ_lt_succ hk, he⟩)
    have hdomy := dom_of_beyond t F hshape hgram hgsym hrr y hy hb
    have hwey : ∀ s, 0 < wCount W y s → y = rhoV t := by
      intro s hs
      obtain ⟨k, hk, hkey⟩ := wCount_witness W y s hs
      exact w_beyond t F W wits hshape hsp hrd hdom k hk y hy hny
        hkey hdomy
    have hrhoy : y = rhoV t := by
      by_cases h0 : wCount W y true = 0
      · exact hwey false (Nat.pos_of_ne_zero
          (fun hz => hne (by rw [h0, hz])))
      · exact hwey true (Nat.pos_of_ne_zero h0)
    rw [hrhoy]
    exact BPair.oneValue_refl _

/-! The unbalanced keys' dot square (`thm:memberchar`'s eigen read):
a key of the Weyl fold reading its two graded counts apart rides the
dominance walk to `ρ` — the counts transport at every letter
(`wCount_refl`), a key a letter fixes reads its two counts at one
value, and the kept form carries the key's own dot square along the
chain. -/

/-- The kept form's transport: a reflection keeps a key's own dot
square (`con:sertables`' four-join identity at the matrices). -/
private theorem dotB_reflAt (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hform : reflFormRead t F)
    {i : Nat} (hi : i < t.rank) (y : List BPair)
    (hy : y.length = t.rank) :
    (dotB F (reflAt t i y) (reflAt t i y)).oneValue (dotB F y y) := by
  have hrank : 0 < t.rank := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hSlen : (reflM t i).length = t.rank := reflM_length t i
  have hSrows : elim.rowsLen t.rank (reflM t i) := reflM_rows t i
  have htS : (elim.transposeM (reflM t i)).length = t.rank :=
    elim.length_transposeM (reflM t i) hSrows
      (by rw [hSlen]; exact hrank)
  have hM : (elim.matVec (reflM t i) y).length = t.rank :=
    (elim.matVec_length _ _).trans hSlen
  have hP : (reflAt t i y).length = t.rank :=
    (poly.pnorm_length _).trans hM
  have hMSrows : elim.rowsLen t.rank
      (elim.matMul F.gram (reflM t i)) := by
    have h := elim.rowsLen_matMul F.gram (reflM t i)
    rw [htS] at h
    exact h
  refine BPair.oneValue_trans (elim.dotP_oneValue_left _
    (elim.matVec (reflM t i) y) _ (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans (elim.dotP_oneValue_right _
    (elim.matVec F.gram (reflAt t i y))
    (elim.matVec F.gram (elim.matVec (reflM t i) y))
    (elim.matVec_congr F.gram _ _
      (poly.pnorm_oneValue _))) ?_
  refine BPair.oneValue_trans (elim.dotP_oneValue_right _ _
    (elim.matVec (elim.matMul F.gram (reflM t i)) y)
    (poly.oneValue_symm (elim.matVec_matMul F.gram (reflM t i)
      t.rank hSrows y hy))) ?_
  refine BPair.oneValue_trans (elim.dotP_matVec_transpose t.rank
    (reflM t i) y _ hSrows hy
    (by rw [elim.matVec_length, elim.length_matMul, hSlen]
        exact hshape.1)) ?_
  refine BPair.oneValue_trans (elim.dotP_oneValue_right y _
    (elim.matVec (elim.matMul (elim.transposeM (reflM t i))
      (elim.matMul F.gram (reflM t i))) y)
    (poly.oneValue_symm (elim.matVec_matMul
      (elim.transposeM (reflM t i))
      (elim.matMul F.gram (reflM t i)) t.rank hMSrows y hy))) ?_
  exact elim.dotP_oneValue_right y _ (elim.matVec F.gram y)
    (elim.matVec_matOne _ _ y (hform i hi))

/-- An unbalanced key is occupied. -/
private theorem occ_of_unb (t : gentable.Table)
    (W : List (List BPair × Bool)) (y : List BPair)
    (hne : wCount W y true ≠ wCount W y false) :
    0 < occAt t W y := by
  show 0 < subsetCount t y false + subsetCount t y true
    + wCount W y false + wCount W y true
  by_cases h0 : wCount W y true = 0
  · have hpos : 0 < wCount W y false :=
      Nat.pos_of_ne_zero (fun hz => hne (by rw [h0, hz]))
    exact Nat.lt_of_lt_of_le hpos
      (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  · exact Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero h0)
      (Nat.le_add_left _ _)

/-- The unbalanced walk: a key reading its two graded counts apart
rides the raises to `ρ`, the counts transported at every letter and
the kept form carrying the dot square along. -/
private theorem wOff_go (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hrr : gentable.rhoRead t)
    (hsp : simplePosRead t F) (hsq : reflSquareRead t)
    (hrd : rhoDotRead t F) (hform : reflFormRead t F)
    (hclose : wCloseRead t W) (hdom : wDomRead t W wits) :
    ∀ (n : Nat) (y : List BPair), y.length = t.rank →
      poly.pnorm y = y →
      wCount W y true ≠ wCount W y false →
      dotB F (rhoV t) (rhoV t) ≤ dotB F y (rhoV t) + BPair.ofNat n →
      (dotB F y y).oneValue (dotB F (rhoV t) (rhoV t))
  | 0, y, hy, hny, hne, hfuel => by
    by_cases hex : ∃ p, p + 1 < t.rank + 1
        ∧ getAt BPair.unit y p < BPair.unit
    · obtain ⟨p, hp, hlt⟩ := hex
      exfalso
      have hpr : p < t.rank := Nat.lt_of_succ_lt_succ hp
      have hne' : wCount W (reflAt t p y) true
          ≠ wCount W (reflAt t p y) false := by
        rw [wCount_refl t W hclose hsq p hpr y hy hny true,
          wCount_refl t W hclose hsq p hpr y hy hny false]
        exact fun hc => hne hc.symm
      have hdy : dotB F (rhoV t) (rhoV t) ≤ dotB F y (rhoV t) :=
        ground.leB_congr_right (BPair.add_unit _) hfuel
      refine ground.leB_not_lt
        (ground.leB_trans
          (rise_gap t F hshape hsp hrd p hpr y hy hlt)
          (ground.leB_trans
            (dom_of_occ t F W wits hshape hsp hrd hdom _
              (occ_of_unb t W _ hne')) hdy))
        ?_
      exact ground.ltB_addPos
        (by decide +kernel : BPair.unit < BPair.ofNat 1)
    · exact wOff_dom t F W wits hshape hgram hgsym hrr hsp hsq hrd
        hclose hdom y hy hny hne
        (fun k hk => ground.leB_of_not_lt
          (fun hc => hex ⟨k, Nat.succ_lt_succ hk, hc⟩))
  | m + 1, y, hy, hny, hne, hfuel => by
    by_cases hex : ∃ p, p + 1 < t.rank + 1
        ∧ getAt BPair.unit y p < BPair.unit
    · obtain ⟨p, hp, hlt⟩ := hex
      have hpr : p < t.rank := Nat.lt_of_succ_lt_succ hp
      have hne' : wCount W (reflAt t p y) true
          ≠ wCount W (reflAt t p y) false := by
        rw [wCount_refl t W hclose hsq p hpr y hy hny true,
          wCount_refl t W hclose hsq p hpr y hy hny false]
        exact fun hc => hne hc.symm
      have e : (dotB F y (rhoV t) + BPair.ofNat (m + 1)).oneValue
          (dotB F y (rhoV t) + BPair.ofNat 1 + BPair.ofNat m) := by
        refine BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.ofNat_succ m)) ?_
        rw [BPair.add_comm (BPair.ofNat m) (BPair.ofNat 1),
          ← BPair.add_assoc]
        exact BPair.oneValue_refl _
      refine BPair.oneValue_trans
        (BPair.oneValue_symm
          (dotB_reflAt t F hshape hform hpr y hy)) ?_
      refine wOff_go t F W wits hshape hgram hgsym hrr hsp hsq hrd
        hform hclose hdom m (reflAt t p y) (reflAt_length t p y)
        (reflAt_norm t p y) hne' ?_
      exact ground.leB_trans hfuel
        (ground.leB_congr_left (BPair.oneValue_symm e)
          (ground.leB_add
            (rise_gap t F hshape hsp hrd p hpr y hy hlt)
            (ground.leB_refl (BPair.ofNat m))))
    · exact wOff_dom t F W wits hshape hgram hgsym hrr hsp hsq hrd
        hclose hdom y hy hny hne
        (fun k hk => ground.leB_of_not_lt
          (fun hc => hex ⟨k, Nat.succ_lt_succ hk, hc⟩))


/-- The unbalanced key's dot square (`thm:memberchar`'s eigen read):
a member of the Weyl fold whose two graded counts read apart carries
`ρ`'s own dot square — the dominance walk runs its key to `ρ` with
the counts transported and the kept form carrying the dot. -/
theorem wOff_dotSq (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hrd : rhoDotRead t F)
    (hrr : gentable.rhoRead t)
    (hform : reflFormRead t F) (hwsh : wShapeRead t W)
    (hclose : wCloseRead t W) (hdom : wDomRead t W wits)
    (k : List BPair) (s : Bool) (hmem : (k, s) ∈ W)
    (hunb : ground.countOf (k, true) W
      ≠ ground.countOf (k, false) W) :
    (dotB F k k).oneValue (dotB F (rhoV t) (rhoV t)) := by
  have hsh := hwsh (k, s) hmem
  obtain ⟨n, hn⟩ := ground.leB_ofNat_bound
    (dotB F (rhoV t) (rhoV t) + (dotB F k (rhoV t)).swap)
  refine wOff_go t F W wits hshape hgram hgsym hrr hsp hsq hrd
    hform hclose hdom n k hsh.1 hsh.2 hunb ?_
  refine ground.leB_congr_left ?_
    (ground.leB_add (ground.leB_refl (dotB F k (rhoV t))) hn)
  refine BPair.oneValue_trans ?_ (BPair.add_unit _)
  rw [BPair.add_left_comm]
  exact BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.swap_add_null (BPair.oneValue_refl _)))

/-- The four counts' reorder at a reflection's exchange. -/
private theorem add4_swap (a b c d : Nat) :
    b + a + d + c = a + b + c + d := by
  rw [Nat.add_comm b a, Nat.add_assoc (a + b), Nat.add_comm d c,
    ← Nat.add_assoc]


/-- The witness fold's own read: a natural fold of the simple roots
sits at or above the sum's unit, each member's count scaling a
positive `ρ`-dot. -/
private theorem witFoldUnit (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hrd : rhoDotRead t F) (c : List Nat) :
    BPair.unit ≤ ground.famFold BPair.add BPair.unit
      (fun i => BPair.mul (BPair.ofNat (ground.getAt 0 c i))
        (dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
          (rhoV t)))
      (List.range t.rank) :=
  ground.foldB_nonneg _ (List.range t.rank) (fun _ hi =>
    ground.leB_unit_mul _
      (Or.inr (hrd _ (simplePos_lt t F hshape
        (ground.ltOfMem hi)))))


/-- The family's occupied keys are height-capped: the support read's
witness fold joins an occupied key's `ρ`-dot back to the shifted
key's, at the fold's positive dots. -/
private theorem capGam (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (top : List BPair)
    (htl : top.length = t.rank)
    (gam : List BPair → Bool → Nat)
    (hgfold : ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y → ∀ s, 0 < gam y s → ∃ c : List Nat,
        poly.pnorm (elim.vecAdd y (cartanFold t c)) = top)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) (s : Bool) (hs : 0 < gam y s) :
    dotB F y (rhoV t) ≤ dotB F top (rhoV t) := by
  obtain ⟨c, hkey⟩ := hgfold y hy hyn s hs
  exact ground.dom_of_split
    (dotB_foldKey t F hshape hsp y c top htl hkey)
    (witFoldUnit t F hshape hrd c)


/-- The alternant's occupied keys are height-capped: an occupied
graded member names its position, where the stated witness fold
joins its key's `ρ`-dot back to the shifted key's. -/
private theorem capW (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (top : List BPair)
    (htl : top.length = t.rank)
    (W' : List (List BPair × Bool)) (wits' : List (List Nat))
    (hdom' : wDomAt t W' wits' top)
    (y : List BPair) (s : Bool) (hs : 0 < wCount W' y s) :
    dotB F y (rhoV t) ≤ dotB F top (rhoV t) := by
  obtain ⟨k, hk, he⟩ := ground.getAt_of_mem (([], false))
    (ground.mem_of_countOf_pos (y, s) W' hs)
  have hkey : poly.pnorm (elim.vecAdd y
      (cartanFold t (ground.getAt [] wits' k))) = top := by
    have h := hdom'.2 k hk
    rw [he] at h
    exact h
  exact ground.dom_of_split
    (dotB_foldKey t F hshape hsp y
      (ground.getAt [] wits' k) top htl hkey)
    (witFoldUnit t F hshape hrd (ground.getAt [] wits' k))


/-- An occupied key of either datum sits at or below the shifted
key's own height. -/
private theorem capOcc (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (top : List BPair)
    (htl : top.length = t.rank)
    (gam : List BPair → Bool → Nat)
    (hgfold : ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y → ∀ s, 0 < gam y s → ∃ c : List Nat,
        poly.pnorm (elim.vecAdd y (cartanFold t c)) = top)
    (W' : List (List BPair × Bool)) (wits' : List (List Nat))
    (hdom' : wDomAt t W' wits' top)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y)
    (hocc : 0 < gam y false + gam y true + wCount W' y false
      + wCount W' y true) :
    dotB F y (rhoV t) ≤ dotB F top (rhoV t) := by
  cases ground.posOr hocc with
  | inr hD =>
    exact capW t F hshape hsp hrd top htl W' wits' hdom' y true hD
  | inl h2 =>
    cases ground.posOr h2 with
    | inr hC =>
      exact capW t F hshape hsp hrd top htl W' wits' hdom' y false hC
    | inl h1 =>
      cases ground.posOr h1 with
      | inl hA =>
        exact capGam t F hshape hsp hrd top htl gam hgfold y hy hyn
          false hA
      | inr hB =>
        exact capGam t F hshape hsp hrd top htl gam hgfold y hy hyn
          true hB


/-- The counts' transport at a reflection carries the balance
back. -/
private theorem balRefl (t : gentable.Table)
    (hsq : reflSquareRead t) (gam : List BPair → Bool → Nat)
    (hgrefl : ∀ i, i < t.rank → ∀ y : List BPair,
      y.length = t.rank → poly.pnorm y = y →
      ∀ s, gam (reflAt t i y) s = gam y (!s))
    (W' : List (List BPair × Bool)) (hclose' : wCloseRead t W')
    (p : Nat) (hpr : p < t.rank) (y : List BPair)
    (hy : y.length = t.rank) (hyn : poly.pnorm y = y)
    (h : gam (reflAt t p y) false + wCount W' (reflAt t p y) true
      = gam (reflAt t p y) true
        + wCount W' (reflAt t p y) false) :
    gam y false + wCount W' y true
      = gam y true + wCount W' y false := by
  rw [hgrefl p hpr y hy hyn false, hgrefl p hpr y hy hyn true,
    wCount_refl t W' hclose' hsq p hpr y hy hyn false,
    wCount_refl t W' hclose' hsq p hpr y hy hyn true] at h
  exact h.symm


/-- The dominant images' pins: at a simple pair the unit the key is
its own reflection and both data read their own flipped sides;
beyond the unit the key is either the shifted key, where the pins
read one and none on both, or off it, where the two regular reads
pair the sides. -/
private theorem domClose (t : gentable.Table)
    (hsq : reflSquareRead t) (top : List BPair)
    (gam : List BPair → Bool → Nat)
    (hgrefl : ∀ i, i < t.rank → ∀ y : List BPair,
      y.length = t.rank → poly.pnorm y = y →
      ∀ s, gam (reflAt t i y) s = gam y (!s))
    (hgtop : gam top false = 1 ∧ gam top true = 0)
    (hgreg : ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y →
      (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit y k) →
      y ≠ top → gam y true = gam y false)
    (W' : List (List BPair × Bool)) (hclose' : wCloseRead t W')
    (htop' : wTopAt W' top)
    (hwreg : ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y →
      (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit y k) →
      y ≠ top → wCount W' y true = wCount W' y false)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y)
    (hlow : ∀ k, k < t.rank →
      BPair.unit ≤ ground.getAt BPair.unit y k) :
    gam y false + wCount W' y true
      = gam y true + wCount W' y false := by
  by_cases hex : ∃ p, p + 1 < t.rank + 1
      ∧ (ground.getAt BPair.unit y p).oneValue BPair.unit
  · obtain ⟨p, hp, hu⟩ := hex
    have hpr : p < t.rank := Nat.lt_of_succ_lt_succ hp
    have hfix : reflAt t p y = y :=
      reflAt_fix t p hpr y hy hyn hu
    have hg := hgrefl p hpr y hy hyn false
    have hw := wCount_refl t W' hclose' hsq p hpr y hy hyn
      true
    rw [hfix] at hg hw
    rw [hg, hw]
    rfl
  · have hb : ∀ k, k < t.rank →
        BPair.unit < ground.getAt BPair.unit y k :=
      fun k hk => ground.ltOfLeOff (hlow k hk)
        (fun he => hex ⟨k, Nat.succ_lt_succ hk, he⟩)
    by_cases hyt : y = top
    · rw [hyt, hgtop.1, hgtop.2]
      show 1 + ground.countOf (top, true) W'
        = 0 + ground.countOf (top, false) W'
      rw [htop'.1, htop'.2]
    · rw [hgreg y hy hyn hb hyt, hwreg y hy hyn hb hyt]


/-- The dominance walk at the shifted key: at a lower-side simple
pair the reflection raises the key's `ρ`-dot by at least one and
flips both data's sides, so the fuel counted off the gap runs the
key to a dominant image, where the pins close. -/
private theorem walkGo (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hrd : rhoDotRead t F)
    (top : List BPair) (htl : top.length = t.rank)
    (gam : List BPair → Bool → Nat)
    (hgrefl : ∀ i, i < t.rank → ∀ y : List BPair,
      y.length = t.rank → poly.pnorm y = y →
      ∀ s, gam (reflAt t i y) s = gam y (!s))
    (hgtop : gam top false = 1 ∧ gam top true = 0)
    (hgreg : ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y →
      (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit y k) →
      y ≠ top → gam y true = gam y false)
    (W' : List (List BPair × Bool)) (hclose' : wCloseRead t W')
    (htop' : wTopAt W' top)
    (hwreg : ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y →
      (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit y k) →
      y ≠ top → wCount W' y true = wCount W' y false)
    (hcap : ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y →
      0 < gam y false + gam y true + wCount W' y false
        + wCount W' y true →
      dotB F y (rhoV t) ≤ dotB F top (rhoV t)) :
    ∀ (n : Nat) (y : List BPair), y.length = t.rank →
      poly.pnorm y = y →
      0 < gam y false + gam y true + wCount W' y false
        + wCount W' y true →
      dotB F top (rhoV t) ≤ dotB F y (rhoV t) + BPair.ofNat n →
      gam y false + wCount W' y true
        = gam y true + wCount W' y false
  | 0, y, hy, hyn, hocc, hfuel => by
    by_cases hex : ∃ p, p + 1 < t.rank + 1
        ∧ ground.getAt BPair.unit y p < BPair.unit
    · obtain ⟨p, hp, hlt⟩ := hex
      exfalso
      have hpr : p < t.rank := Nat.lt_of_succ_lt_succ hp
      have hocc' : 0 < gam (reflAt t p y) false
          + gam (reflAt t p y) true
          + wCount W' (reflAt t p y) false
          + wCount W' (reflAt t p y) true := by
        rw [hgrefl p hpr y hy hyn false, hgrefl p hpr y hy hyn true,
          wCount_refl t W' hclose' hsq p hpr y hy hyn false,
          wCount_refl t W' hclose' hsq p hpr y hy hyn true]
        show 0 < gam y true + gam y false + wCount W' y true
          + wCount W' y false
        rw [add4_swap]
        exact hocc
      have hdy : dotB F top (rhoV t) ≤ dotB F y (rhoV t) :=
        ground.leB_congr_right (BPair.add_unit _) hfuel
      refine ground.leB_not_lt
        (ground.leB_trans
          (rise_gap t F hshape hsp hrd p hpr y hy hlt)
          (ground.leB_trans
            (hcap (reflAt t p y) (reflAt_length t p y)
              (reflAt_norm t p y) hocc') hdy))
        ?_
      exact ground.ltB_addPos
        (by decide +kernel : BPair.unit < BPair.ofNat 1)
    · exact domClose t hsq top gam hgrefl hgtop hgreg W' hclose'
        htop' hwreg y hy hyn
        (fun k hk => ground.leB_of_not_lt
          (fun hc => hex ⟨k, Nat.succ_lt_succ hk, hc⟩))
  | m + 1, y, hy, hyn, hocc, hfuel => by
    by_cases hex : ∃ p, p + 1 < t.rank + 1
        ∧ ground.getAt BPair.unit y p < BPair.unit
    · obtain ⟨p, hp, hlt⟩ := hex
      have hpr : p < t.rank := Nat.lt_of_succ_lt_succ hp
      have hocc' : 0 < gam (reflAt t p y) false
          + gam (reflAt t p y) true
          + wCount W' (reflAt t p y) false
          + wCount W' (reflAt t p y) true := by
        rw [hgrefl p hpr y hy hyn false, hgrefl p hpr y hy hyn true,
          wCount_refl t W' hclose' hsq p hpr y hy hyn false,
          wCount_refl t W' hclose' hsq p hpr y hy hyn true]
        show 0 < gam y true + gam y false + wCount W' y true
          + wCount W' y false
        rw [add4_swap]
        exact hocc
      have e : (dotB F y (rhoV t) + BPair.ofNat (m + 1)).oneValue
          (dotB F y (rhoV t) + BPair.ofNat 1 + BPair.ofNat m) := by
        refine BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.ofNat_succ m)) ?_
        rw [BPair.add_comm (BPair.ofNat m) (BPair.ofNat 1),
          ← BPair.add_assoc]
        exact BPair.oneValue_refl _
      refine balRefl t hsq gam hgrefl W' hclose' p hpr y hy hyn ?_
      refine walkGo t F hshape hsp hsq hrd top htl gam hgrefl
        hgtop hgreg W' hclose' htop' hwreg hcap m
        (reflAt t p y) (reflAt_length t p y)
        (reflAt_norm t p y) hocc' ?_
      exact ground.leB_trans hfuel
        (ground.leB_congr_left (BPair.oneValue_symm e)
          (ground.leB_add
            (rise_gap t F hshape hsp hrd p hpr y hy hlt)
            (ground.leB_refl (BPair.ofNat m))))
    · exact domClose t hsq top gam hgrefl hgtop hgreg W' hclose'
        htop' hwreg y hy hyn
        (fun k hk => ground.leB_of_not_lt
          (fun hc => hex ⟨k, Nat.succ_lt_succ hk, hc⟩))


/-- The determination at the four reads: a reflection-graded family
balances the shifted alternant's data key by key — the abstract
family's statement `thm:memberchar`'s determination sentence, the
walk itself `thm:assembly`'s conclusion mechanism, the fuel seeded
off the shifted key's own `ρ`-dot gap and the vacant keys reading
the four counts at the count's unit.  `balanceRead` below is its
`Φ`-instance at `ρ` through the cap engine, and the member identity
consumes it at the convolution's reads.  The walk's frames come
from the reflection's own length and norm reads and the height cap
from the support witness alone, so the shifted key's normed
spelling and the alternant's shape read bind no field of the
derivation and sit off the statement. -/
theorem fourReads_walk (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hrd : rhoDotRead t F)
    (top : List BPair) (htl : top.length = t.rank)
    (gam : List BPair → Bool → Nat)
    (hgrefl : ∀ i, i < t.rank → ∀ y : List BPair, y.length = t.rank →
      poly.pnorm y = y → ∀ s, gam (reflAt t i y) s = gam y (!s))
    (hgfold : ∀ y : List BPair, y.length = t.rank → poly.pnorm y = y →
      ∀ s, 0 < gam y s → ∃ c : List Nat,
        poly.pnorm (elim.vecAdd y (cartanFold t c)) = top)
    (hgtop : gam top false = 1 ∧ gam top true = 0)
    (hgreg : ∀ y : List BPair, y.length = t.rank → poly.pnorm y = y →
      (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit y k) →
      y ≠ top → gam y true = gam y false)
    (W' : List (List BPair × Bool)) (wits' : List (List Nat))
    (hclose' : wCloseRead t W')
    (hdom' : wDomAt t W' wits' top) (htop' : wTopAt W' top)
    (hreg' : wRegRead t W' top)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) :
    gam y false + wCount W' y true = gam y true + wCount W' y false := by
  cases hocc : gam y false + gam y true + wCount W' y false
      + wCount W' y true with
  | succ m =>
    obtain ⟨n, hn⟩ := ground.leB_ofNat_bound
      (dotB F top (rhoV t) + (dotB F y (rhoV t)).swap)
    refine walkGo t F hshape hsp hsq hrd top htl gam hgrefl
      hgtop hgreg W' hclose' htop'
      (fun z hz hzn hb hzt => ?wregD) 
      (fun z hz hzn hzocc =>
        capOcc t F hshape hsp hrd top htl gam hgfold W' wits'
          hdom' z hz hzn hzocc)
      n y hy hyn
      (by rw [hocc]; exact Nat.succ_pos m) ?_
    case wregD =>
      match Nat.eq_zero_or_pos (ground.countOf (z, true) W') with
      | Or.inr h =>
        exact hreg' (z, true)
          (ground.mem_of_countOf_pos (z, true) W' h) hb hzt
      | Or.inl h0 =>
        match Nat.eq_zero_or_pos (ground.countOf (z, false) W') with
        | Or.inr h1 =>
          exact hreg' (z, false)
            (ground.mem_of_countOf_pos (z, false) W' h1) hb hzt
        | Or.inl h2 =>
          show ground.countOf (z, true) W'
            = ground.countOf (z, false) W'
          rw [h0, h2]
    refine ground.leB_congr_left ?_
      (ground.leB_add (ground.leB_refl (dotB F y (rhoV t))) hn)
    refine BPair.oneValue_trans ?_ (BPair.add_unit _)
    rw [BPair.add_left_comm]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.swap_add_null (BPair.oneValue_refl _)))
  | zero =>
    have h1 := Nat.eq_zero_of_add_eq_zero_right hocc
    have h2 := Nat.eq_zero_of_add_eq_zero_right h1
    rw [Nat.eq_zero_of_add_eq_zero_right h2,
      Nat.eq_zero_of_add_eq_zero_left h2,
      Nat.eq_zero_of_add_eq_zero_left h1,
      Nat.eq_zero_of_add_eq_zero_left hocc]


/-- `thm:assembly`'s conclusion: the per-key balance `Φ = a_ρ` at
every normed key of the rank's length — the dominance walk raising
at a lower-side simple pair through the two transports, the raises
closing at the gap's count against the occupied keys' dots, the
fixed keys pairing each fold's sides, and the beyond-unit dominant
keys reading `ρ` at the support folds' positive dots.  The root
fold's coroot read `(2ρ)(α_i^∨) = 2` takes no binder: it is the
shape, the simple positions, the permutation datum's involution,
the image clauses and the `ρ`-dots' own consequence
(`rhoRead_derived`). -/
theorem balanceRead (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hclose : wCloseRead t W) (hdom : wDomRead t W wits)
    (htop : wTopRead t W)
    (y : List BPair) (hy : y.length = t.rank)
    (hny : poly.pnorm y = y) :
    balanceAt t W y := by
  have hrr := rhoRead_derived t F hshape hsp hpsq hpi hrd
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hgtop : subsetCount t (rhoV t) false = 1
      ∧ subsetCount t (rhoV t) true = 0 := by
    have h := subsetCount_rho t F hrd
    rw [pnorm_rhoV] at h
    exact h
  have hwtop : wTopAt W (rhoV t) := by
    constructor
    · rw [← pnorm_rhoV t]
      exact htop.1
    · rw [← pnorm_rhoV t]
      exact htop.2
  have hgreg : ∀ z : List BPair, z.length = t.rank →
      poly.pnorm z = z →
      (∀ k, k < t.rank → BPair.unit < getAt BPair.unit z k) →
      z ≠ rhoV t →
      subsetCount t z true = subsetCount t z false := by
    intro z hz hzn hb hne
    have hzero : ∀ s, subsetCount t z s = 0 := by
      intro s
      match Nat.eq_zero_or_pos (subsetCount t z s) with
      | Or.inl h0 => exact h0
      | Or.inr hp =>
        obtain ⟨S, hS, hkey⟩ := subsetCount_witness t z s hp
        refine absurd ?_ hne
        rw [← hkey, phi_top t F hrd S hS z hkey
          (dom_of_beyond t F hshape hgram hgsym hrr z hz hb)]
        exact eKey_nil t
    rw [hzero true, hzero false]
  have hwreg : ∀ z : List BPair, z.length = t.rank →
      poly.pnorm z = z →
      (∀ k, k < t.rank → BPair.unit < getAt BPair.unit z k) →
      z ≠ rhoV t → wCount W z true = wCount W z false := by
    intro z hz hzn hb hne
    have hzero : ∀ s, wCount W z s = 0 := by
      intro s
      match Nat.eq_zero_or_pos (wCount W z s) with
      | Or.inl h0 => exact h0
      | Or.inr hp =>
        obtain ⟨k, hk, hkey⟩ := wCount_witness W z s hp
        exact absurd (w_beyond t F W wits hshape hsp hrd hdom k hk
          z hz hzn hkey
          (dom_of_beyond t F hshape hgram hgsym hrr z hz hb)) hne
    rw [hzero true, hzero false]
  show subsetCount t y false + wCount W y true
    = subsetCount t y true + wCount W y false
  cases hocc : subsetCount t y false + subsetCount t y true
      + wCount W y false + wCount W y true with
  | succ m =>
    obtain ⟨n, hn⟩ := ground.leB_ofNat_bound
      (dotB F (rhoV t) (rhoV t) + (dotB F y (rhoV t)).swap)
    refine walkGo t F hshape hsp hsq hrd (rhoV t) hrl
      (subsetCount t)
      (fun i hi z hz hzn s =>
        subsetCount_refl t F hshape hsp hsq hpsq hpi hrd
          i hi z hz hzn s)
      hgtop hgreg W hclose hwtop hwreg
      (fun z _ _ hzocc =>
        dom_of_occ t F W wits hshape hsp hrd hdom z hzocc)
      n y hy hny
      (by rw [hocc]; exact Nat.succ_pos m) ?_
    refine ground.leB_congr_left ?_
      (ground.leB_add (ground.leB_refl (dotB F y (rhoV t))) hn)
    refine BPair.oneValue_trans ?_ (BPair.add_unit _)
    rw [BPair.add_left_comm]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.swap_add_null (BPair.oneValue_refl _)))
  | zero =>
    have h1 := Nat.eq_zero_of_add_eq_zero_right hocc
    have h2 := Nat.eq_zero_of_add_eq_zero_right h1
    rw [Nat.eq_zero_of_add_eq_zero_right h2,
      Nat.eq_zero_of_add_eq_zero_left h2,
      Nat.eq_zero_of_add_eq_zero_left h1,
      Nat.eq_zero_of_add_eq_zero_left hocc]
/-- An off-shape key's subset count is the count's unit: every hit
key is normed at the rank's order. -/
private theorem subsetCount_shape (t : gentable.Table)
    (y : List BPair)
    (hsh : ¬ (y.length = t.rank ∧ poly.pnorm y = y))
    (side : Bool) : subsetCount t y side = 0 := by
  show ground.famFold Nat.add 0 _
    (ground.sublistsOf (List.range t.posFolds.length)) = 0
  rw [ground.famFold_congr_members Nat.add 0 _ (fun _ => 0)
    (ground.sublistsOf (List.range t.posFolds.length)) (fun S _ => by
      by_cases hside : places.sideOf S = side
      · by_cases hhit : eKey t S = y
        · refine absurd ?_ hsh
          rw [← hhit]
          exact ⟨eKey_length t S, poly.pnorm_pnorm _⟩
        · rw [if_pos hside, if_neg hhit]
      · rw [if_neg hside])]
  exact ground.famFold_zero (fun _ => 0) (fun _ => rfl) _

/-- The flipped subset map's count at a graded key is the subset
fold's at the flipped side. -/
private theorem countOf_flipMap (t : gentable.Table)
    (k : List BPair) (s : Bool) : ∀ l : List (List Nat),
    ground.countOf (k, s)
      (l.map (fun S => (eKey t S, !places.sideOf S)))
      = ground.famFold Nat.add 0
        (fun S => if places.sideOf S = (!s) then
          (if eKey t S = k then 1 else 0) else 0) l
  | [] => rfl
  | S :: l => by
    show ground.countOf (k, s)
        ((eKey t S, !places.sideOf S)
          :: l.map (fun S => (eKey t S, !places.sideOf S)))
      = (if places.sideOf S = (!s) then
          (if eKey t S = k then 1 else 0) else 0)
        + ground.famFold Nat.add 0
          (fun S => if places.sideOf S = (!s) then
            (if eKey t S = k then 1 else 0) else 0) l
    rw [ground.countOf_cons, countOf_flipMap t k s l]
    by_cases hsd : places.sideOf S = (!s)
    · by_cases hk : eKey t S = k
      · rw [if_pos (by rw [hk, hsd]; cases s <;> rfl),
          if_pos hsd, if_pos hk]
      · rw [if_neg (fun he : (k, s) = (eKey t S, !places.sideOf S) =>
            hk ((congrArg Prod.fst he).symm)),
          if_pos hsd, if_neg hk]
    · rw [if_neg (fun he : (k, s) = (eKey t S, !places.sideOf S) =>
          hsd (by
            have h2 := congrArg Prod.snd he
            rw [show s = !places.sideOf S from h2]
            cases places.sideOf S <;> rfl)),
        if_neg hsd]

/-- The alternant fold reads the subset fold: a read's signed fold
over the alternant data agrees with its signed fold over the
subset families, the concatenation balanced key by key —
`thm:assembly`'s `Φ = a_ρ` consumed whole at every read. -/
theorem wFold_subsets (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (htop : wTopRead t W)
    (X : List BPair → BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2 (X vp.1)) W).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun S => ground.signedAt (places.sideOf S) (X (eKey t S)))
        (ground.sublistsOf (List.range t.posFolds.length))) := by
  have hnull := ground.signedFold_null X
    (W ++ (ground.sublistsOf (List.range t.posFolds.length)).map
      (fun S => (eKey t S, !places.sideOf S))).length
    (W ++ (ground.sublistsOf (List.range t.posFolds.length)).map
      (fun S => (eKey t S, !places.sideOf S)))
    (Nat.le_refl _)
    (fun k _ => by
      refine Or.inl ?_
      rw [ground.countOf_append, ground.countOf_append,
        countOf_flipMap t k true _, countOf_flipMap t k false _]
      show ground.countOf (k, true) W + subsetCount t k false
        = ground.countOf (k, false) W + subsetCount t k true
      by_cases hsh : k.length = t.rank ∧ poly.pnorm k = k
      · have hbal := balanceRead t F W wits hshape hgram hgsym
          hsp hsq hpsq hpi hrd hclose hdom htop k hsh.1 hsh.2
        rw [Nat.add_comm (ground.countOf (k, true) W)
            (subsetCount t k false),
          Nat.add_comm (ground.countOf (k, false) W)
            (subsetCount t k true)]
        exact hbal
      · have hW : ∀ s : Bool, ground.countOf (k, s) W = 0 :=
          fun s => by
            match Nat.eq_zero_or_pos
                (ground.countOf (k, s) W) with
            | .inl h0 => exact h0
            | .inr hpos =>
              exact absurd
                (hwsh (k, s)
                  (ground.mem_of_countOf_pos (k, s) W hpos)) hsh
        rw [hW true, hW false, subsetCount_shape t k hsh false,
          subsetCount_shape t k hsh true])
  have happ := foldB_app (fun vp => ground.signedAt vp.2 (X vp.1))
    W ((ground.sublistsOf (List.range t.posFolds.length)).map
      (fun S => (eKey t S, !places.sideOf S)))
  have hAB := BPair.oneValue_trans (BPair.oneValue_symm happ) hnull
  have hswapEq : ground.famFold BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2 (X vp.1))
      ((ground.sublistsOf (List.range t.posFolds.length)).map
        (fun S => (eKey t S, !places.sideOf S)))
      = (ground.famFold BPair.add BPair.unit
        (fun S => ground.signedAt (places.sideOf S) (X (eKey t S)))
        (ground.sublistsOf (List.range t.posFolds.length))).swap := by
    rw [ground.famFold_map BPair.add BPair.unit
      (fun vp => ground.signedAt vp.2 (X vp.1))
      (fun S => (eKey t S, !places.sideOf S))
      (ground.sublistsOf (List.range t.posFolds.length)),
      ground.famFold_congr_all BPair.add BPair.unit
      (fun S => ground.signedAt
        ((fun S => (eKey t S, !places.sideOf S)) S).2
        (X ((fun S => (eKey t S, !places.sideOf S)) S).1))
      (fun S => (ground.signedAt (places.sideOf S) (X (eKey t S))).swap)
      (fun S => ground.signedAt_not (places.sideOf S) (X (eKey t S)))
      (ground.sublistsOf (List.range t.posFolds.length)),
      ground.fold_swap]
  rw [hswapEq] at hAB
  exact ground.oneOfUnit hAB

/-! `cor:weyldim`'s subset bridges: the pair product over a distinct
index list expands over the occupancy families, one signed monomial
per family at the complement-guarded degree fold, and at a weight
whose positive dots sit at or beyond the unit each family's degree
fold solves to the shifted key margin — `thm:assembly`'s subset fold
consumed at the member dimension's gap product. -/

/-- A positive member's dot against a dominant key sits at or
beyond the sum's unit: the member's coroot vector is its fold's
counted Cartan rows, each row's pairing the scaled length at the
key's own coordinate (`thm:assembly`'s dominance pin at the
positive list). -/
theorem dotB_pos_nonneg (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (z : List BPair) (hz : z.length = t.rank)
    (hpos : ∀ k, k < t.rank → BPair.unit ≤ getAt BPair.unit z k)
    (j : Nat) : BPair.unit ≤ dotB F (posCorootV t j) z := by
  have hG : (elim.matVec F.gram z).length = t.rank :=
    (elim.matVec_length F.gram z).trans hshape.1
  refine ground.leB_congr_right
    (BPair.oneValue_symm
      (elim.dotP_zipSum t.rank (elim.matVec F.gram z) hG
        (getAt [] t.posFolds j) t.cartan)) ?_
  refine zipDot_nonneg (elim.matVec F.gram z) (getAt [] t.posFolds j)
    t.cartan (fun l hl => ?_)
  refine ground.leB_congr_right
    (BPair.oneValue_symm (diagRow t F hshape hgram z hz l hl)) ?_
  exact ground.leB_unit_mul _
    (hpos l (by rw [← cartanLen t F hgram]; exact hl))

/-- The gap at a positive member against a weight: the dot's
margin (`cor:weyldim`'s member gaps at `con:sertables`' positive
list). -/
def gapsAt (t : gentable.Table) (F : FundData)
    (kap : List BPair) (j : Nat) : Nat :=
  BPair.marginN (dotB F (posCorootV t j) kap)

/-- The margin of a fold of reads at or beyond the sum's unit is
the margins' own fold. -/
private theorem marginN_famFold {α : Type} [DecidableEq α]
    (f : α → BPair) : ∀ l : List α,
    (∀ x, 0 < ground.countOf x l → BPair.unit ≤ f x) →
    ground.famFold Nat.add 0 (fun x => BPair.marginN (f x)) l
      = BPair.marginN (ground.famFold BPair.add BPair.unit f l)
  | [], _ => rfl
  | a :: l, h => by
    show BPair.marginN (f a)
        + ground.famFold Nat.add 0 (fun x => BPair.marginN (f x)) l
      = BPair.marginN
          (BPair.add (f a) (ground.famFold BPair.add BPair.unit f l))
    rw [BPair.marginN_add
        (h a (by rw [ground.countOf_head]; exact Nat.succ_pos _))
        (ground.foldB_nonneg f l (fun x hx =>
          h x (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))),
      marginN_famFold f l (fun x hx =>
        h x (Nat.lt_of_lt_of_le hx (Nat.le_add_left _ _)))]

/-- The subset degree solve at a weight whose positive dots sit at
or beyond the unit: the complement-guarded gap fold reads the
shifted key margin (`thm:assembly`'s subset fold at `cor:weyldim`'s
degrees; the root fold's coroot two takes no binder, derived as at
`balanceRead`). -/
theorem gapFold_eKey (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hpsq : permSquareRead t F) (hpi : permImageRead t F)
    (hrd : rhoDotRead t F)
    (kap : List BPair)
    (hnn : ∀ j, j < t.posFolds.length →
      BPair.unit ≤ dotB F (posCorootV t j) kap)
    (S : List Nat)
    (hS : 0 < ground.countOf S
      (ground.sublistsOf (List.range t.posFolds.length))) :
    ground.famFold Nat.add 0
      (fun j => if 0 < ground.countOf j S then 0
        else gapsAt t F kap j)
      (List.range t.posFolds.length)
    = BPair.marginN (BPair.add
        (dotB F (rhoV t) kap) (dotB F (eKey t S) kap)) := by
  obtain ⟨hSd, hSb⟩ := sublists_range_distinct t.posFolds.length S hS
  have hrho := rhoRead_derived t F hshape hsp hpsq hpi hrd
  have hstep : ground.famFold Nat.add 0
      (fun j => if 0 < ground.countOf j S then 0
        else gapsAt t F kap j)
      (List.range t.posFolds.length)
    = ground.famFold Nat.add 0
        (fun j => BPair.marginN (if ground.containsB S j then BPair.unit
          else dotB F (posCorootV t j) kap))
        (List.range t.posFolds.length) := by
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range t.posFolds.length) (fun j _ => ?_)
    by_cases hc : 0 < ground.countOf j S
    · rw [if_pos hc,
        show ground.containsB S j = true from decide_eq_true hc, if_pos rfl]
      rfl
    · rw [if_neg hc,
        show ground.containsB S j = false from decide_eq_false hc,
        if_neg (ground.boolNe rfl)]
      rfl
  rw [hstep, marginN_famFold _ (List.range t.posFolds.length)
    (fun j hj => ?_)]
  · exact BPair.marginN_congr (antiDotsL t F hshape hrho kap S hSd hSb)
  · by_cases hc : ground.containsB S j = true
    · rw [if_pos hc]
      exact ground.leB_refl _
    · rw [if_neg hc]
      rw [ground.countOf_range j t.posFolds.length] at hj
      by_cases hlt : j < t.posFolds.length
      · exact hnn j hlt
      · rw [if_neg hlt] at hj
        exact absurd hj (Nat.lt_irrefl 0)


end assembly
