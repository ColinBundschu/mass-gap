import MassGap.Cellcount
import MassGap.Stagebox
/-!
`lem:cellcount` — the box cover.  A pencil in two variables enters as
a symmetric site datum over the iterated carrier (`split.PPMat`, the
inner variable's polynomials the outer variable's coefficients), its
shape read the stated order with every entry's outer degree within
the outer clearing power and every coefficient within the inner one
(`ppShapeAt`); the inner evaluation at a composite inner point
(`ppevalPC`, `poly.pevalCP` entrywise) leaves the outer variable's
pencil, shaped and symmetric where the two-variable datum is
(`pShapeAt_ppevalPC`, `pSymAt_ppevalPC`), and the point count is the
one-variable count of that pencil at the outer point.  The deflation
cleared once at the pivot's determinant's magnitude at the iterated
carrier, `det P · S_P` at a pivot whose determinant keeps its upper
side (`pdeflP2` at the polynomial adjugate `split.ppadj`, the entry
bundle's `deflPO` and `elim.adjO` at the polynomial entries,
`def:poly`'s reads over the polynomials as the entry carrier in turn)
and its memberwise swap at a pivot keeping its lower side or at the
mixed block (`pdeflM2`), each shaped at the pivot order's successor
multiple of the two clearing powers (`ppShape_pdeflP2`,
`ppShape_pdeflM2`), reads under the inner evaluation as the
evaluated pencil's own once-cleared deflation (`ppevalPC_pdeflP2`,
`ppevalPC_pdeflM2`, the bundle's graded map at the inner evaluation
reading sums to sums and products to products at the split clearing
powers).  The cover of a box is the box cut at stated points, one
variable per cut, into pieces (`Cover2`, `coverRead2`), each piece
with its designated minor keeping its side over the piece at the
box's priced side read (`stage.keepUpperBox`, `stage.keepLowerBox`),
at order two its leading entry so as well where the determinant sits
on its upper side, and beneath it the once-cleared deflation's own
box cover over the piece, the deflation or its swap at the
determinant's side.  The constancy theorem `cover2_const` reads one
integer at every point of the box at the pencil's shape and symmetry
reads: at every point of a piece the count is the pivot's block read
(`inertia.revSel_one`, `revSel_mixed`, `revSel_twoUp` at the box
read's side) joined to the once-cleared deflation's count
(`piece_addP`, `piece_addM` at the double evaluation), one integer
on the piece at its own cover, and a cut's two boxes read one count
through a point of the cut; `cellCount2` transports a sampled count
across the box. -/

namespace cellcount
open ground poly elim inertia

/-! The two-variable pencil's shape and symmetry through the inner
evaluation. -/

/-- The two-variable pencil's shape read: square at the stated order,
every entry's outer degree within the outer clearing power and every
coefficient's inner degree within the inner one. -/
def ppShapeAt (S : split.PPMat) (o Ks Kt : Nat) : Prop :=
  elim.shapeAtO (fun P => Nat.ble P.length (Ks + 1)
    && P.all (fun c => Nat.ble c.length (Kt + 1))) S o

instance instCellbox1 (S : split.PPMat) (o Ks Kt : Nat) :
    Decidable (ppShapeAt S o Ks Kt) :=
  inferInstanceAs (Decidable (elim.shapeAtO _ _ _))

/-- The two-variable shape read's row count. -/
theorem ppShape_len {S : split.PPMat} {o Ks Kt : Nat}
    (h : ppShapeAt S o Ks Kt) : S.length = o :=
  elim.shapeAt_len h

/-- The two-variable shape read's row widths. -/
theorem ppShape_rows {S : split.PPMat} {o Ks Kt : Nat}
    (h : ppShapeAt S o Ks Kt) : elim.rowsLen o S :=
  elim.shapeAt_rows h

/-- Every entry's outer degree sits within the outer clearing power
and its coefficients within the inner one, a key beyond the datum
reading the vacant list. -/
theorem ppShape_entry {S : split.PPMat} {o Ks Kt : Nat}
    (hsh : ppShapeAt S o Ks Kt) : ∀ i j,
    (ground.getAt ([] : PPoly)
      (ground.getAt ([] : List PPoly) S i) j).length ≤ Ks + 1
    ∧ innerLe (ground.getAt ([] : PPoly)
      (ground.getAt ([] : List PPoly) S i) j) Kt := by
  intro i j
  have he := ground.andSplitB (elim.shapeAt_entry hsh ([] : PPoly) rfl i j)
  exact ⟨ground.bleLe he.1, he.2⟩

/-- The inner evaluation keeps the row count. -/
theorem length_ppevalPC (S : split.PPMat) (tn : BPair) (tc : Pos) (Kt : Nat) :
    (ppevalPC S tn tc Kt).length = S.length :=
  ground.length_map _ S

/-- The inner evaluation keeps every row's width. -/
theorem rowsLen_ppevalPC (n : Nat) (S : split.PPMat) (tn : BPair) (tc : Pos)
    (Kt : Nat) (h : elim.rowsLen n S) :
    elim.rowsLen n (ppevalPC S tn tc Kt) :=
  elim.rowsLen_mapRowsO (fun P => pevalCP P tn tc Kt) S n h

/-- The inner-evaluated pencil's entry at two keys: the datum's entry
there, evaluated. -/
theorem getAt_ppevalPC (tn : BPair) (tc : Pos) (Kt : Nat) :
    ∀ (S : split.PPMat) (i j : Nat),
      ground.getAt ([] : Poly)
          (ground.getAt ([] : List Poly) (ppevalPC S tn tc Kt) i) j
        = pevalCP (ground.getAt ([] : PPoly)
            (ground.getAt ([] : List PPoly) S i) j) tn tc Kt :=
  elim.getAt_mapRowsO ([] : PPoly) ([] : Poly)
    (fun P => pevalCP P tn tc Kt) rfl

/-- One row's inner evaluations keep the outer degree read. -/
private theorem rowBle_ppeval (tn : BPair) (tc : Pos) (Ks Kt : Nat) :
    ∀ r : List PPoly,
      (r.all (fun P => Nat.ble P.length (Ks + 1)
        && P.all (fun c => Nat.ble c.length (Kt + 1)))) = true →
      ((evalPC r tn tc Kt).all (fun p => Nat.ble p.length (Ks + 1))) = true
  | [], _ => rfl
  | P :: r, h => by
    have h' : ((Nat.ble P.length (Ks + 1)
        && P.all (fun c => Nat.ble c.length (Kt + 1)))
      && r.all (fun P => Nat.ble P.length (Ks + 1)
        && P.all (fun c => Nat.ble c.length (Kt + 1)))) = true := h
    have hs := ground.andSplitB h'
    have hs2 := ground.andSplitB hs.1
    show (Nat.ble (pevalCP P tn tc Kt).length (Ks + 1)
      && (evalPC r tn tc Kt).all (fun p => Nat.ble p.length (Ks + 1))) = true
    rw [length_pevalCP]
    exact ground.andIntroB hs2.1 (rowBle_ppeval tn tc Ks Kt r hs.2)

/-- The inner evaluation keeps the outer degree read row by row. -/
private theorem matBle_ppeval (tn : BPair) (tc : Pos) (o Ks Kt : Nat) :
    ∀ S : split.PPMat,
      (S.all (fun r => Nat.beq r.length o
        && r.all (fun P => Nat.ble P.length (Ks + 1)
          && P.all (fun c => Nat.ble c.length (Kt + 1))))) = true →
      ((ppevalPC S tn tc Kt).all
        (fun r => r.all (fun p => Nat.ble p.length (Ks + 1)))) = true
  | [], _ => rfl
  | r :: S, h => by
    have h' : ((Nat.beq r.length o
        && r.all (fun P => Nat.ble P.length (Ks + 1)
          && P.all (fun c => Nat.ble c.length (Kt + 1))))
      && S.all (fun r => Nat.beq r.length o
        && r.all (fun P => Nat.ble P.length (Ks + 1)
          && P.all (fun c => Nat.ble c.length (Kt + 1))))) = true := h
    have hs := ground.andSplitB h'
    have hs2 := ground.andSplitB hs.1
    show ((evalPC r tn tc Kt).all (fun p => Nat.ble p.length (Ks + 1))
      && (ppevalPC S tn tc Kt).all
        (fun r => r.all (fun p => Nat.ble p.length (Ks + 1)))) = true
    exact ground.andIntroB (rowBle_ppeval tn tc Ks Kt r hs2.2)
      (matBle_ppeval tn tc o Ks Kt S hs.2)

/-- The inner evaluation of a two-variable shaped pencil is shaped
at the outer clearing power. -/
theorem pShapeAt_ppevalPC {S : split.PPMat} {o Ks Kt : Nat}
    (hsh : ppShapeAt S o Ks Kt) (tn : BPair) (tc : Pos) :
    pShapeAt (ppevalPC S tn tc Kt) o Ks :=
  pShapeAt_of ((length_ppevalPC S tn tc Kt).trans (ppShape_len hsh))
    (rowsLen_ppevalPC o S tn tc Kt (ppShape_rows hsh))
    (matBle_ppeval tn tc o Ks Kt S
      (ground.andSplitB
        (show (Nat.beq S.length o && S.all (fun r => Nat.beq r.length o
          && r.all (fun P => Nat.ble P.length (Ks + 1)
            && P.all (fun c => Nat.ble c.length (Kt + 1))))) = true
          from hsh)).2)

/-- The inner evaluation of a two-variable symmetric pencil is
symmetric at the stated order. -/
theorem pSymAt_ppevalPC {S : split.PPMat} {o : Nat} (hsym : split.ppSymAt S o)
    (tn : BPair) (tc : Pos) (Kt : Nat) :
    split.pSymAt (ppevalPC S tn tc Kt) o :=
  elim.symAtO_of _ _ _ o (fun i j hi hj => by
    rw [getAt_ppevalPC tn tc Kt S i j, getAt_ppevalPC tn tc Kt S j i]
    exact pevalCP_congr tn tc Kt (elim.symAtO_at hsym i j hi hj))

/-! The deflation cleared once at the pivot's determinant's magnitude
at the iterated carrier: the bundle's once-cleared family at the
polynomial entries with the polynomial adjugate of every order, its
memberwise swap, their shapes at the pivot order's successor
multiple of the two clearing powers, and their inner evaluations as
the evaluated pencil's own once-cleared deflations. -/

/-- The deflation cleared once at the iterated carrier: the trailing
block at the pivot minor against the coupling's solved correction at
the polynomial adjugate, the bundle's `deflPO` at the polynomial
entries (`lem:cellcount`'s deflation cleared once at the pivot's
determinant's magnitude, the read at a pivot whose determinant keeps
its upper side). -/
def pdeflP2 (idx rest : List Nat) (S : split.PPMat) : split.PPMat :=
  deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj false idx rest S

/-- The deflation cleared once at the iterated carrier at a pivot
whose determinant keeps its lower side or at the mixed block: the
trailing block at the minor's swap joined to the correction, the
bundle's `deflPO` at the lower side (`lem:cellcount`'s collected
display of the once-cleared deflation's memberwise swap). -/
def pdeflM2 (idx rest : List Nat) (S : split.PPMat) : split.PPMat :=
  deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj true idx rest S

/-- The two-variable shape read assembled from its conjunct reads. -/
theorem ppShapeAt_of {S : split.PPMat} {o Ks Kt : Nat}
    (hlen : S.length = o) (hrows : elim.rowsLen o S)
    (hout : ∀ i j, (ground.getAt ([] : PPoly)
      (ground.getAt ([] : List PPoly) S i) j).length ≤ Ks + 1)
    (hin : ∀ i j, innerLe (ground.getAt ([] : PPoly)
      (ground.getAt ([] : List PPoly) S i) j) Kt) :
    ppShapeAt S o Ks Kt :=
  elim.shapeAtO_of _ hlen hrows
    (ground.all_of_getAt ([] : List PPoly) _ _ (fun k _ =>
      ground.all_of_getAt ([] : PPoly) _ _ (fun j _ =>
        ground.andIntroB (ground.leBle (hout k j)) (hin k j))))

/-- The once-cleared deflation's entries at either side and a pivot of
every order at the pivot order's successor multiple of both clearing
powers, `(k + 1) Ks` and `(k + 1) Kt` at the pivot order `k`: the
pivot minor's caps at the order's multiples (`elim.deg_minorO`), the
adjugate's one order below (`elim.deg_adjO`), and the bundle's cap
read joining them (`inertia.deg_deflPO`) in each variable. -/
private theorem ppShape_deflS2 (lower : Bool) (S : split.PPMat) (o Ks Kt : Nat)
    (idx rest : List Nat) (hS : ppShapeAt S o Ks Kt) :
    ppShapeAt (deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj lower idx rest S)
      rest.length ((idx.length + 1) * Ks) ((idx.length + 1) * Kt) := by
  match idx with
  | [] =>
    have hPo : ∀ a b, (ground.getAt ([] : PPoly) (ground.getAt ([] : List PPoly)
        (split.ppselM [] [] S) a) b).length ≤ Ks + 1 :=
      elim.deg_selMO ([] : PPoly) (fun P K => P.length ≤ K + 1)
        (fun a b => (ppShape_entry hS a b).1) [] []
    have hPi : ∀ a b, innerLe (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly) (split.ppselM [] [] S) a) b) Kt :=
      elim.deg_selMO ([] : PPoly) (fun P K => innerLe P K)
        (fun a b => (ppShape_entry hS a b).2) [] []
    have hPl0 : (split.ppselM [] [] S).length = ([] : List Nat).length :=
      elim.length_selMO _ _ _ _
    have hmO : (split.ppminor (split.ppselM [] [] S)).length ≤ 0 * Ks + 1 := by
      have h := elim.deg_minorO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => P.length ≤ K + 1)
        (fun _ _ _ hK hx => Nat.le_trans hx (Nat.succ_le_succ hK))
        (fun K x y hx hy => poly.addLenLeO poly.polyOps x y (K + 1) hx hy)
        (fun K1 K2 x y hx hy => poly.mulLenLeO poly.polyOps x y K1 K2 hx hy)
        (fun _ x h => by
          show (x.map poly.polyOps.swap).length ≤ _
          rw [ground.length_map]; exact h)
        (fun _ x h => by
          show (x.map poly.pnorm).length ≤ _
          rw [ground.length_map]; exact h)
        (fun _ _ h => h) (fun _ => Nat.zero_le _) (Nat.le_refl 1)
        Ks (split.ppselM [] [] S) hPo
      rw [hPl0] at h
      exact h
    have hmI : innerLe (split.ppminor (split.ppselM [] [] S)) (0 * Kt) := by
      have h := elim.deg_minorO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => innerLe P K)
        (fun _ _ _ hK hx => innerLe_of_le hx hK)
        (fun _ _ _ hx hy => innerLe_padd hx hy)
        (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
        (fun _ _ h => innerLe_pnegP h)
        (fun _ _ h => innerLe_pnormP h)
        (fun _ _ h => h) (fun _ => rfl) rfl
        Kt (split.ppselM [] [] S) hPi
      rw [hPl0] at h
      exact h
    have hmOc : (cond lower (poly.pnegP (split.ppminor (split.ppselM [] [] S)))
        (split.ppminor (split.ppselM [] [] S))).length ≤ 0 * Ks + 1 := by
      cases lower with
      | false => exact hmO
      | true =>
        show (poly.pnegP (split.ppminor (split.ppselM [] [] S))).length ≤ 0 * Ks + 1
        rw [show (poly.pnegP (split.ppminor (split.ppselM [] [] S))).length
          = (split.ppminor (split.ppselM [] [] S)).length from ground.length_map _ _]
        exact hmO
    have hmIc : innerLe (cond lower (poly.pnegP (split.ppminor (split.ppselM [] [] S)))
        (split.ppminor (split.ppselM [] [] S))) (0 * Kt) := by
      cases lower with
      | false => exact hmI
      | true => exact innerLe_pnegP hmI
    have hout : ∀ i j, (ground.getAt ([] : PPoly) (ground.getAt ([] : List PPoly)
        (deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj lower [] rest S)
          i) j).length ≤ 0 * Ks + Ks + 1 :=
      elim.deg_scaleO (poly.polyO poly.polyOps) (fun P K => P.length ≤ K + 1)
        (fun x y hx hy => poly.mulLenLeO poly.polyOps x y (0 * Ks) Ks hx hy)
        (Nat.zero_le _) _ hmOc _
        (elim.deg_selMO ([] : PPoly) (fun P K => P.length ≤ K + 1)
          (fun a b => (ppShape_entry hS a b).1) rest rest)
    have hin : ∀ i j, innerLe (ground.getAt ([] : PPoly) (ground.getAt ([] : List PPoly)
        (deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj lower [] rest S)
          i) j) (0 * Kt + Kt) :=
      elim.deg_scaleO (poly.polyO poly.polyOps) (fun P K => innerLe P K)
        (fun x y hx hy => innerLe_pmul hx hy) rfl _ hmIc _
        (elim.deg_selMO ([] : PPoly) (fun P K => innerLe P K)
          (fun a b => (ppShape_entry hS a b).2) rest rest)
    have hKs : (([] : List Nat).length + 1) * Ks = 0 * Ks + Ks := Nat.succ_mul 0 Ks
    have hKt : (([] : List Nat).length + 1) * Kt = 0 * Kt + Kt := Nat.succ_mul 0 Kt
    rw [hKs, hKt]
    exact ppShapeAt_of (length_deflPO _ _ _ _ _ _ _ _)
      (rowsLen_deflPO _ _ _ _ _ _ _ _
        ((elim.length_adjO _ _ _).trans (elim.length_selMO _ _ _ _))) hout hin
  | i :: t =>
    have hPl : (split.ppselM (i :: t) (i :: t) S).length = t.length + 1 :=
      elim.length_selMO _ _ _ _
    have hPo : ∀ a b, (ground.getAt ([] : PPoly) (ground.getAt ([] : List PPoly)
        (split.ppselM (i :: t) (i :: t) S) a) b).length ≤ Ks + 1 :=
      elim.deg_selMO ([] : PPoly) (fun P K => P.length ≤ K + 1)
        (fun a b => (ppShape_entry hS a b).1) (i :: t) (i :: t)
    have hPi : ∀ a b, innerLe (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly) (split.ppselM (i :: t) (i :: t) S) a) b)
        Kt :=
      elim.deg_selMO ([] : PPoly) (fun P K => innerLe P K)
        (fun a b => (ppShape_entry hS a b).2) (i :: t) (i :: t)
    have hmO : (split.ppminor (split.ppselM (i :: t) (i :: t) S)).length
        ≤ (t.length + 1) * Ks + 1 := by
      have h := elim.deg_minorO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => P.length ≤ K + 1)
        (fun _ _ _ hK hx => Nat.le_trans hx (Nat.succ_le_succ hK))
        (fun K x y hx hy => poly.addLenLeO poly.polyOps x y (K + 1) hx hy)
        (fun K1 K2 x y hx hy => poly.mulLenLeO poly.polyOps x y K1 K2 hx hy)
        (fun _ x h => by
          show (x.map poly.polyOps.swap).length ≤ _
          rw [ground.length_map]; exact h)
        (fun _ x h => by
          show (x.map poly.pnorm).length ≤ _
          rw [ground.length_map]; exact h)
        (fun _ _ h => h) (fun _ => Nat.zero_le _) (Nat.le_refl 1)
        Ks (split.ppselM (i :: t) (i :: t) S) hPo
      rw [hPl] at h
      exact h
    have hmI : innerLe (split.ppminor (split.ppselM (i :: t) (i :: t) S))
        ((t.length + 1) * Kt) := by
      have h := elim.deg_minorO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => innerLe P K)
        (fun _ _ _ hK hx => innerLe_of_le hx hK)
        (fun _ _ _ hx hy => innerLe_padd hx hy)
        (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
        (fun _ _ h => innerLe_pnegP h)
        (fun _ _ h => innerLe_pnormP h)
        (fun _ _ h => h) (fun _ => rfl) rfl
        Kt (split.ppselM (i :: t) (i :: t) S) hPi
      rw [hPl] at h
      exact h
    have hAo : ∀ a b, (ground.getAt ([] : PPoly) (ground.getAt ([] : List PPoly)
        (split.ppadj (split.ppselM (i :: t) (i :: t) S)) a) b).length
        ≤ t.length * Ks + 1 :=
      elim.deg_adjO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => P.length ≤ K + 1)
        (fun _ _ _ hK hx => Nat.le_trans hx (Nat.succ_le_succ hK))
        (fun K x y hx hy => poly.addLenLeO poly.polyOps x y (K + 1) hx hy)
        (fun K1 K2 x y hx hy => poly.mulLenLeO poly.polyOps x y K1 K2 hx hy)
        (fun _ x h => by
          show (x.map poly.polyOps.swap).length ≤ _
          rw [ground.length_map]; exact h)
        (fun _ x h => by
          show (x.map poly.pnorm).length ≤ _
          rw [ground.length_map]; exact h)
        (fun _ _ h => h) (fun _ => Nat.zero_le _) (Nat.le_refl 1)
        Ks t.length (split.ppselM (i :: t) (i :: t) S) hPl hPo
    have hAi : ∀ a b, innerLe (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly)
          (split.ppadj (split.ppselM (i :: t) (i :: t) S)) a) b) (t.length * Kt) :=
      elim.deg_adjO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => innerLe P K)
        (fun _ _ _ hK hx => innerLe_of_le hx hK)
        (fun _ _ _ hx hy => innerLe_padd hx hy)
        (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
        (fun _ _ h => innerLe_pnegP h)
        (fun _ _ h => innerLe_pnormP h)
        (fun _ _ h => h) (fun _ => rfl) rfl
        Kt t.length (split.ppselM (i :: t) (i :: t) S) hPl hPi
    have hout := deg_deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj
      (fun P K => P.length ≤ K + 1)
      (fun K x y hx hy => poly.addLenLeO poly.polyOps x y (K + 1) hx hy)
      (fun K1 K2 x y hx hy => poly.mulLenLeO poly.polyOps x y K1 K2 hx hy)
      (fun _ x h => by
        show (x.map poly.polyOps.swap).length ≤ _
        rw [ground.length_map]; exact h)
      (fun _ => Nat.zero_le _) lower
      S Ks ((t.length + 1) * Ks) (t.length * Ks) (i :: t) rest
      (fun a b => (ppShape_entry hS a b).1) (Nat.succ_mul t.length Ks).symm hmO hAo
    have hin := deg_deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj
      (fun P K => innerLe P K)
      (fun _ _ _ hx hy => innerLe_padd hx hy)
      (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
      (fun _ _ h => innerLe_pnegP h)
      (fun _ => rfl) lower
      S Kt ((t.length + 1) * Kt) (t.length * Kt) (i :: t) rest
      (fun a b => (ppShape_entry hS a b).2) (Nat.succ_mul t.length Kt).symm hmI hAi
    have hout' : ∀ a b, (ground.getAt ([] : PPoly) (ground.getAt ([] : List PPoly)
        (deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj lower (i :: t) rest S)
          a) b).length ≤ (t.length + 1 + 1) * Ks + 1 := by
      intro a b
      rw [Nat.succ_mul (t.length + 1) Ks]
      exact hout a b
    have hin' : ∀ a b, innerLe (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly)
          (deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj lower (i :: t) rest S)
          a) b) ((t.length + 1 + 1) * Kt) := by
      intro a b
      rw [Nat.succ_mul (t.length + 1) Kt]
      exact hin a b
    show ppShapeAt
      (deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj lower (i :: t) rest S)
      rest.length ((t.length + 1 + 1) * Ks) ((t.length + 1 + 1) * Kt)
    exact ppShapeAt_of (length_deflPO _ _ _ _ _ _ _ _)
      (rowsLen_deflPO _ _ _ _ _ _ _ _ ((elim.length_adjO _ _ _).trans hPl)) hout' hin'

/-- The once-cleared deflation's entries at the pivot order's
successor multiple of both clearing powers, `(k + 1) Ks` and
`(k + 1) Kt` at the pivot order `k`: the pivot minor's caps at the
order's multiples (`elim.deg_minorO`), the adjugate's one order
below (`elim.deg_adjO`), and the bundle's cap read joining them
(`inertia.deg_deflPO`) in each variable. -/
theorem ppShape_pdeflP2 (S : split.PPMat) (o Ks Kt : Nat) (idx rest : List Nat)
    (hS : ppShapeAt S o Ks Kt) :
    ppShapeAt (pdeflP2 idx rest S) rest.length
      ((idx.length + 1) * Ks) ((idx.length + 1) * Kt) :=
  ppShape_deflS2 false S o Ks Kt idx rest hS

/-- The swapped deflation's entries at the pivot order's successor
multiple of both clearing powers, the swapped minor's caps the
minor's own. -/
theorem ppShape_pdeflM2 (S : split.PPMat) (o Ks Kt : Nat) (idx rest : List Nat)
    (hS : ppShapeAt S o Ks Kt) :
    ppShapeAt (pdeflM2 idx rest S) rest.length
      ((idx.length + 1) * Ks) ((idx.length + 1) * Kt) :=
  ppShape_deflS2 true S o Ks Kt idx rest hS

/-- The once-cleared deflation's inner evaluation at either side is the
evaluated pencil's own once-cleared deflation at that side, at an
occupied pivot list of every order (`lem:cellcount`'s designated
minor), the inner clearing power `(k + 1) Kt` at the pivot order `k`:
the bundle's graded map at the inner evaluation reading sums to sums
and products to products (`inertia.deflPO_map`), the pivot minor and
the polynomial adjugate each carried across the map
(`elim.minorO_gmap`, `elim.adjO_gmap`). -/
private theorem ppevalPC_deflS2 (lower : Bool) {o Ks Kt : Nat} (S : split.PPMat)
    (idx rest : List Nat) (tn : BPair) (tc : Pos) (hsh : ppShapeAt S o Ks Kt)
    (hk0 : 0 < idx.length) :
    split.pmatOneValue
      (ppevalPC (deflPO (poly.polyO poly.polyOps) poly.pnormP id split.ppadj lower
        idx rest S) tn tc ((idx.length + 1) * Kt))
      (deflPO poly.polyOps poly.pnorm id split.padj lower idx rest
        (ppevalPC S tn tc Kt)) := by
  match idx, hk0 with
  | [], h => exact absurd h (Nat.lt_irrefl 0)
  | i :: t, _ =>
    have hPl : (elim.selMO ([] : PPoly) (i :: t) (i :: t) S).length = t.length + 1 :=
      elim.length_selMO _ _ _ _
    have hPr : elim.rowsLen (t.length + 1) (elim.selMO ([] : PPoly) (i :: t) (i :: t) S) :=
      elim.rowsLen_selMO ([] : PPoly) (i :: t) S (i :: t)
    have hPsq : elim.rowsLen (elim.selMO ([] : PPoly) (i :: t) (i :: t) S).length
        (elim.selMO ([] : PPoly) (i :: t) (i :: t) S) := by
      rw [hPl]; exact hPr
    have hPi : ∀ a b, innerLe (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly)
          (elim.selMO ([] : PPoly) (i :: t) (i :: t) S) a) b) Kt :=
      elim.deg_selMO ([] : PPoly) (fun P K => innerLe P K)
        (fun a b => (ppShape_entry hsh a b).2) (i :: t) (i :: t)
    have hmI : innerLe (split.ppminor (split.ppselM (i :: t) (i :: t) S))
        ((t.length + 1) * Kt) := by
      have h := elim.deg_minorO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => innerLe P K)
        (fun _ _ _ hK hx => innerLe_of_le hx hK)
        (fun _ _ _ hx hy => innerLe_padd hx hy)
        (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
        (fun _ _ h => innerLe_pnegP h)
        (fun _ _ h => innerLe_pnormP h)
        (fun _ _ h => h) (fun _ => rfl) rfl
        Kt (elim.selMO ([] : PPoly) (i :: t) (i :: t) S) hPi
      rw [hPl] at h
      exact h
    have hAi : ∀ a b, innerLe (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly)
          (split.ppadj (elim.selMO ([] : PPoly) (i :: t) (i :: t) S)) a) b)
        (t.length * Kt) :=
      elim.deg_adjO (poly.polyO poly.polyOps) poly.pnormP id
        (fun P K => innerLe P K)
        (fun _ _ _ hK hx => innerLe_of_le hx hK)
        (fun _ _ _ hx hy => innerLe_padd hx hy)
        (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
        (fun _ _ h => innerLe_pnegP h)
        (fun _ _ h => innerLe_pnormP h)
        (fun _ _ h => h) (fun _ => rfl) rfl
        Kt t.length (elim.selMO ([] : PPoly) (i :: t) (i :: t) S) hPl hPi
    have hmin : poly.oneValue
        (pevalCP (split.ppminor (split.ppselM (i :: t) (i :: t) S)) tn tc
          ((t.length + 1) * Kt))
        (split.pminor (split.pselM (i :: t) (i :: t) (ppevalPC S tn tc Kt))) := by
      have h := elim.minorO_gmap (poly.polyO poly.polyOps) poly.polyOps
        poly.polyRead poly.pnormP id poly.pnorm id
        (fun K P => pevalCP P tn tc K) (fun P K => innerLe P K)
        poly.oneValue_refl (fun h => poly.oneValue_symm h)
        (fun h1 h2 => poly.oneValue_trans h1 h2)
        (fun h1 h2 => poly.add_congr h1 h2)
        (fun h1 h2 => poly.oneValue_trans (poly.mul_congr_left h1 _)
          (poly.mul_congr _ h2))
        (fun h => poly.neg_congr h)
        (fun _ => rfl) ⟨evalClear_one tn tc, trivial⟩
        (fun K x y => pevalCP_padd x y tn tc K)
        (fun K1 K2 x y hx hy => pevalCP_pmul x y K1 K2 hx hy tn tc)
        (fun K x => pevalCP_pnegP x tn tc K)
        (fun K x => pevalCP_congr tn tc K (pnormP_ppOneValue x))
        (fun _ _ => poly.oneValue_refl _)
        (fun y => pnorm_oneValue y) (fun _ => poly.oneValue_refl _)
        (fun _ _ _ hK hx => innerLe_of_le hx hK)
        (fun _ _ _ hx hy => innerLe_padd hx hy)
        (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
        (fun _ _ h => innerLe_pnegP h)
        (fun _ _ h => innerLe_pnormP h)
        (fun _ _ h => h) (fun _ => rfl) rfl
        Kt (elim.selMO ([] : PPoly) (i :: t) (i :: t) S) hPsq hPi
      rw [hPl, ← elim.selMO_mapRowsO ([] : PPoly) ([] : Poly)
        (fun P => pevalCP P tn tc Kt) rfl S (i :: t) (i :: t)] at h
      exact h
    have hadj : ground.matchedOV (ground.matchedRead poly.polyRead)
        ((split.ppadj (elim.selMO ([] : PPoly) (i :: t) (i :: t) S)).map
          (fun r => r.map (fun P => pevalCP P tn tc (t.length * Kt))))
        (split.padj (elim.selMO ([] : Poly) (i :: t) (i :: t)
          (S.map (fun r => r.map (fun P => pevalCP P tn tc Kt))))) := by
      have h := elim.adjO_gmap (poly.polyO poly.polyOps) poly.polyOps
        poly.polyRead poly.pnormP id poly.pnorm id
        (fun K P => pevalCP P tn tc K) (fun P K => innerLe P K)
        poly.oneValue_refl (fun h => poly.oneValue_symm h)
        (fun h1 h2 => poly.oneValue_trans h1 h2)
        (fun h1 h2 => poly.add_congr h1 h2)
        (fun h1 h2 => poly.oneValue_trans (poly.mul_congr_left h1 _)
          (poly.mul_congr _ h2))
        (fun h => poly.neg_congr h)
        (fun _ => rfl) ⟨evalClear_one tn tc, trivial⟩
        (fun K x y => pevalCP_padd x y tn tc K)
        (fun K1 K2 x y hx hy => pevalCP_pmul x y K1 K2 hx hy tn tc)
        (fun K x => pevalCP_pnegP x tn tc K)
        (fun K x => pevalCP_congr tn tc K (pnormP_ppOneValue x))
        (fun _ _ => poly.oneValue_refl _)
        (fun y => pnorm_oneValue y) (fun _ => poly.oneValue_refl _)
        (fun _ _ _ hK hx => innerLe_of_le hx hK)
        (fun _ _ _ hx hy => innerLe_padd hx hy)
        (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
        (fun _ _ h => innerLe_pnegP h)
        (fun _ _ h => innerLe_pnormP h)
        (fun _ _ h => h) (fun _ => rfl) rfl
        Kt t.length (elim.selMO ([] : PPoly) (i :: t) (i :: t) S) hPl hPr hPi
      rw [← elim.selMO_mapRowsO ([] : PPoly) ([] : Poly)
        (fun P => pevalCP P tn tc Kt) rfl S (i :: t) (i :: t)] at h
      exact h
    have h := deflPO_map (poly.polyO poly.polyOps) poly.polyOps poly.polyRead
      poly.pnormP id poly.pnorm id split.ppadj split.padj
      (fun K P => pevalCP P tn tc K) (fun P K => innerLe P K)
      poly.oneValue_refl (fun h1 h2 => poly.oneValue_trans h1 h2)
      (fun h1 h2 => poly.add_congr h1 h2)
      (fun y h => poly.mul_congr_left h y)
      (fun x {_ _} h => poly.mul_congr x h)
      (fun h => poly.neg_congr h)
      (fun _ => rfl)
      (fun K x y => pevalCP_padd x y tn tc K)
      (fun K1 K2 x y hx hy => pevalCP_pmul x y K1 K2 hx hy tn tc)
      (fun K x => pevalCP_pnegP x tn tc K)
      (fun _ _ _ hx hy => innerLe_padd hx hy)
      (fun _ _ _ _ hx hy => innerLe_pmul hx hy)
      (fun _ _ h => innerLe_pnegP h)
      (fun _ => rfl) lower
      S Kt ((t.length + 1) * Kt) (t.length * Kt) (i :: t) rest
      (fun a b => (ppShape_entry hsh a b).2) (Nat.succ_mul t.length Kt).symm
      hmI hmin ((elim.length_adjO _ _ _).trans hPl) hAi hadj
    rw [show (t.length + 1) * Kt + Kt = (t.length + 1 + 1) * Kt from
      (Nat.succ_mul (t.length + 1) Kt).symm] at h
    exact h

/-- The once-cleared deflation's inner evaluation is the evaluated
pencil's own once-cleared deflation at an occupied pivot list of
every order (`lem:cellcount`'s designated minor), the inner clearing
power `(k + 1) Kt` at the pivot order `k` (`ppevalPC_deflS2` at the
upper side). -/
theorem ppevalPC_pdeflP2 {o Ks Kt : Nat} (S : split.PPMat) (idx rest : List Nat)
    (tn : BPair) (tc : Pos) (hsh : ppShapeAt S o Ks Kt)
    (hk0 : 0 < idx.length) :
    split.pmatOneValue
      (ppevalPC (pdeflP2 idx rest S) tn tc ((idx.length + 1) * Kt))
      (pdeflP idx rest (ppevalPC S tn tc Kt)) :=
  ppevalPC_deflS2 false S idx rest tn tc hsh hk0

/-- The swapped deflation's inner evaluation is the evaluated pencil's
own swapped deflation (`ppevalPC_deflS2` at the lower side). -/
theorem ppevalPC_pdeflM2 {o Ks Kt : Nat} (S : split.PPMat) (idx rest : List Nat)
    (tn : BPair) (tc : Pos) (hsh : ppShapeAt S o Ks Kt)
    (hk0 : 0 < idx.length) :
    split.pmatOneValue
      (ppevalPC (pdeflM2 idx rest S) tn tc ((idx.length + 1) * Kt))
      (pdeflM idx rest (ppevalPC S tn tc Kt)) :=
  ppevalPC_deflS2 true S idx rest tn tc hsh hk0

/-- The order-two designated minor keeps the doubled inner-degree
read, the bundle's cap read. -/
private theorem ppminor2_innerLe {S : split.PPMat} {o Ks Kt : Nat}
    (hsh : ppShapeAt S o Ks Kt) (i j : Nat) :
    innerLe (split.ppminor (split.ppselM [i, j] [i, j] S)) (Kt + Kt) :=
  deg_minorO_two (poly.polyO poly.polyOps) poly.pnormP id
    (fun P K => innerLe P K)
    (fun _ _ hx hy => innerLe_padd hx hy) (fun _ _ hx hy => innerLe_pmul hx hy)
    (fun _ h => innerLe_pnegP h) (fun _ h => innerLe_pnormP h) (fun _ h => h) rfl
    (fun i j => (ppShape_entry hsh i j).2) i j

/-- The order-two designated minor's outer degree sits within the
doubled outer clearing power, the bundle's cap read. -/
private theorem ppminor2_len {S : split.PPMat} {o Ks Kt : Nat}
    (hsh : ppShapeAt S o Ks Kt) (i j : Nat) :
    (split.ppminor (split.ppselM [i, j] [i, j] S)).length ≤ Ks + Ks + 1 :=
  deg_minorO_two (poly.polyO poly.polyOps) poly.pnormP id
    (fun P K => P.length ≤ K + 1)
    (fun x y hx hy => addLenLeO polyOps x y (Ks + Ks + 1) hx hy)
    (fun x y hx hy => mulLenLeO polyOps x y Ks Ks hx hy)
    (fun x h => by
      show (x.map poly.polyOps.swap).length ≤ _
      rw [ground.length_map]; exact h)
    (fun x h => by
      show (x.map poly.pnorm).length ≤ _
      rw [ground.length_map]; exact h)
    (fun _ h => h) (Nat.zero_le _)
    (fun i j => (ppShape_entry hsh i j).1) i j

/-! The box read's side at a stated inner and outer power, and the
designated minors' bridges to the evaluated pencil's selections. -/

/-- The box read's upper side at a stated inner and outer power: the
inner evaluation at a power the coefficients sit within and the
outer at one the key count sits within, the value at the
polynomial's own tops rescaled at the gaps. -/
private theorem sideBox_up (m : PPoly) (KT KS : Nat) (hin : innerLe m KT)
    (hout : m.length ≤ KS + 1) (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (h : stage.unitC < stage.evalC (stage.innerC m ⟨tn, tc⟩) ⟨sn, sc⟩) :
    BPair.unit < poly.evalClear (pevalCP m tn tc KT) sn sc KS := by
  rw [stage.innerC_mk] at h
  have h1 : BPair.unit
      < poly.evalClear (pevalCP m tn tc (innerTop m)) sn sc KS :=
    stage.evalFloor
      (fun d hd => BPair.oneValue_of_eq
        (ground.getAt_over BPair.unit _ d
          (Nat.le_trans (by rw [length_pevalCP]; exact hout) hd)))
      sn sc h
  have h2 : (poly.evalClear (pevalCP m tn tc KT) sn sc KS).oneValue
      (ground.bpow (BPair.ofPos tc) (KT - innerTop m)
        * poly.evalClear (pevalCP m tn tc (innerTop m)) sn sc KS) :=
    BPair.oneValue_trans
      (poly.evalClear_congr
        (pevalCP_pow tn tc (innerTop_le hin) (innerLe_innerTop m)) sn sc KS)
      (poly.evalClear_scaleP _ _ sn sc KS)
  exact BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_symm h2)
    (ground.unitLtMul (ground.unitLtBpow (ground.unitLtOfPos tc) _) h1)

/-- The box read's lower side at a stated inner and outer power, the
memberwise swap's. -/
private theorem sideBox_down (m : PPoly) (KT KS : Nat) (hin : innerLe m KT)
    (hout : m.length ≤ KS + 1) (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (h : stage.evalC (stage.innerC m ⟨tn, tc⟩) ⟨sn, sc⟩ < stage.unitC) :
    poly.evalClear (pevalCP m tn tc KT) sn sc KS < BPair.unit := by
  rw [stage.innerC_mk] at h
  have h1 : poly.evalClear (pevalCP m tn tc (innerTop m)) sn sc KS
      < BPair.unit :=
    sideDown_shift _ sn sc KS (by rw [length_pevalCP]; exact hout)
      (sideDown_rep _ sn sc h)
  have h2 : (poly.evalClear (pevalCP m tn tc KT) sn sc KS).oneValue
      (ground.bpow (BPair.ofPos tc) (KT - innerTop m)
        * poly.evalClear (pevalCP m tn tc (innerTop m)) sn sc KS) :=
    BPair.oneValue_trans
      (poly.evalClear_congr
        (pevalCP_pow tn tc (innerTop_le hin) (innerLe_innerTop m)) sn sc KS)
      (poly.evalClear_scaleP _ _ sn sc KS)
  have h2' : (poly.evalClear (pevalCP m tn tc KT) sn sc KS).oneValue
      ((poly.evalClear (pevalCP m tn tc (innerTop m)) sn sc KS).scale
        (ground.Pos.pow tc (KT - innerTop m))) :=
    BPair.oneValue_trans h2
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_symm (ground.ofPos_pow tc _))
          (BPair.oneValue_refl _))
        (BPair.ofPos_scale _ _))
  exact BPair.lt_congr (BPair.oneValue_symm h2') (BPair.oneValue_refl _)
    (ground.scaleLtUnit _ h1)

/-- The order-one designated minor's double evaluation is the
evaluated pencil's selected minor. -/
private theorem box1_bridge (S : split.PPMat) (i : Nat) (tn : BPair)
    (tc : Pos) (Kt : Nat) (sn : BPair) (sc : Pos) (Ks : Nat) :
    (poly.evalClear (pevalCP (split.ppminor (split.ppselM [i] [i] S)) tn tc Kt)
        sn sc Ks).oneValue
      (elim.minor (elim.selM [i] [i]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks))) :=
  BPair.oneValue_trans
    (poly.evalClear_congr
      (minorO_map_one (poly.polyO poly.polyOps) poly.polyOps poly.polyRead
        poly.pnormP id poly.pnorm id (fun K P => pevalCP P tn tc K)
        poly.oneValue_refl (fun _ => rfl) Kt S i)
      sn sc Ks)
    (minor1_bridge (ppevalPC S tn tc Kt) Ks i sn sc)

/-- The order-two designated minor's double evaluation at the doubled
powers is the evaluated pencil's selected minor. -/
private theorem box2_bridge {S : split.PPMat} {o Ks Kt : Nat}
    (hsh : ppShapeAt S o Ks Kt) (i j : Nat) (tn : BPair) (tc : Pos)
    (sn : BPair) (sc : Pos) :
    (poly.evalClear
        (pevalCP (split.ppminor (split.ppselM [i, j] [i, j] S)) tn tc (Kt + Kt))
        sn sc (Ks + Ks)).oneValue
      (elim.minor (elim.selM [i, j] [i, j]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks))) :=
  BPair.oneValue_trans
    (poly.evalClear_congr
      (minorO_map_two (poly.polyO poly.polyOps) poly.polyOps poly.polyRead
        poly.pnormP id poly.pnorm id (fun K P => pevalCP P tn tc K)
        (fun P K => innerLe P K)
        poly.oneValue_refl (fun h => poly.oneValue_symm h)
        (fun h1 h2 => poly.oneValue_trans h1 h2)
        (fun h1 h2 => poly.add_congr h1 h2)
        (fun h => poly.neg_congr h)
        (fun _ => rfl)
        (fun K x y => pevalCP_padd x y tn tc K)
        (fun K1 K2 x y hx hy => pevalCP_pmul x y K1 K2 hx hy tn tc)
        (fun K x => pevalCP_pnegP x tn tc K)
        (fun K x => pevalCP_congr tn tc K (pnormP_ppOneValue x))
        (fun _ _ => poly.oneValue_refl _)
        (fun y => pnorm_oneValue y) (fun _ => poly.oneValue_refl _)
        Kt S (fun i j => (ppShape_entry hsh i j).2) i j)
      sn sc (Ks + Ks))
    (minor2_bridge (pShapeAt_ppevalPC hsh tn tc) i j sn sc)

/-- The order-one designated block's frame at a point of the box: the
minor's side is the block table's entry side, and the pivot's split
reads the table. -/
private theorem side_one2 {o : Nat} (S : split.PPMat) (Ks Kt : Nat)
    (t0 t1 s0 s1 : CPair) (i : Nat) (up : Bool) (Nt Dt Ns Ds : BPair)
    (hsh : ppShapeAt S o Ks Kt)
    (hidx : (([i] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : if up then
        stage.keepUpperBox (split.ppminor (split.ppselM [i] [i] S))
          t0 t1 s0 s1 Nt Dt Ns Ds
      else
        stage.keepLowerBox (split.ppminor (split.ppselM [i] [i] S))
          t0 t1 s0 s1 Nt Dt Ns Ds)
    (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (ht0 : t0 ≤ ⟨tn, tc⟩) (ht1 : (⟨tn, tc⟩ : CPair) ≤ t1)
    (hs0 : s0 ≤ ⟨sn, sc⟩) (hs1 : (⟨sn, sc⟩ : CPair) ≤ s1)
    (hMsym : elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) :
    (¬ (elim.minor (elim.selM [i] [i]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i] : List Nat).length
        (elim.selM [i] [i] (evalPC (ppevalPC S tn tc Kt) sn sc Ks)))
      = (if up = true then 0 else 1)
    ∧ (up = true → BPair.unit < elim.minor (elim.selM [i] [i]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks)))
    ∧ (up = false → elim.minor (elim.selM [i] [i]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) < BPair.unit) := by
  have hsh' := pShapeAt_ppevalPC hsh tn tc
  have hMsq : elim.sqAt (evalPC (ppevalPC S tn tc Kt) sn sc Ks) o :=
    evalPC_sqAt hsh' sn sc
  have hi : i < o := ground.bltLt (ground.andSplitB hidx).1
  have hent := ppShape_entry hsh i i
  match up, hside with
  | true, hs =>
    have h2 := sideBox_up (split.ppminor (split.ppselM [i] [i] S)) Kt Ks
      hent.2 hent.1 tn tc sn sc
      (stage.keepUpperBox_all _ t0 t1 s0 s1 Nt Dt Ns Ds hs ⟨tn, tc⟩ ⟨sn, sc⟩
        ht0 ht1 hs0 hs1)
    have h3 : BPair.unit
        < ground.getAt BPair.unit (ground.getAt ([] : List BPair)
            (evalPC (ppevalPC S tn tc Kt) sn sc Ks) i) i :=
      BPair.lt_congr (BPair.oneValue_refl _)
        (box1_bridge S i tn tc Kt sn sc Ks) h2
    have hr := inertia.revSel_one _ hMsq hMsym i hi true h3
    exact ⟨hr.1, hr.2, fun _ => h3, fun h => Bool.noConfusion h⟩
  | false, hs =>
    have h2 := sideBox_down (split.ppminor (split.ppselM [i] [i] S)) Kt Ks
      hent.2 hent.1 tn tc sn sc
      (stage.keepLowerBox_all _ t0 t1 s0 s1 Nt Dt Ns Ds hs ⟨tn, tc⟩ ⟨sn, sc⟩
        ht0 ht1 hs0 hs1)
    have h3 : ground.getAt BPair.unit (ground.getAt ([] : List BPair)
          (evalPC (ppevalPC S tn tc Kt) sn sc Ks) i) i
        < BPair.unit :=
      BPair.lt_congr (box1_bridge S i tn tc Kt sn sc Ks)
        (BPair.oneValue_refl _) h2
    have hr := inertia.revSel_one _ hMsq hMsym i hi false h3
    exact ⟨hr.1, hr.2, fun h => Bool.noConfusion h, fun _ => h3⟩

/-- The mixed order-two block's frame at a point of the box: the
determinant on its lower side reads one unit per side. -/
private theorem side_mixed2 {o : Nat} (S : split.PPMat) (Ks Kt : Nat)
    (t0 t1 s0 s1 : CPair) (i j : Nat) (Nt Dt Ns Ds : BPair)
    (hsh : ppShapeAt S o Ks Kt)
    (hidx : (([i, j] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : stage.keepLowerBox (split.ppminor (split.ppselM [i, j] [i, j] S))
      t0 t1 s0 s1 Nt Dt Ns Ds)
    (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (ht0 : t0 ≤ ⟨tn, tc⟩) (ht1 : (⟨tn, tc⟩ : CPair) ≤ t1)
    (hs0 : s0 ≤ ⟨sn, sc⟩) (hs1 : (⟨sn, sc⟩ : CPair) ≤ s1)
    (hMsym : elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) :
    (¬ (elim.minor (elim.selM [i, j] [i, j]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i, j] : List Nat).length
        (elim.selM [i, j] [i, j] (evalPC (ppevalPC S tn tc Kt) sn sc Ks)))
      = 1
    ∧ elim.minor (elim.selM [i, j] [i, j]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) < BPair.unit := by
  have hs1' := ground.andSplitB hidx
  have hs2' := ground.andSplitB hs1'.2
  have hi : i < o := ground.bltLt hs1'.1
  have hj : j < o := ground.bltLt hs2'.1
  have hsh' := pShapeAt_ppevalPC hsh tn tc
  have hMsq : elim.sqAt (evalPC (ppevalPC S tn tc Kt) sn sc Ks) o :=
    evalPC_sqAt hsh' sn sc
  have h2 := sideBox_down (split.ppminor (split.ppselM [i, j] [i, j] S))
    (Kt + Kt) (Ks + Ks) (ppminor2_innerLe hsh i j) (ppminor2_len hsh i j)
    tn tc sn sc
    (stage.keepLowerBox_all _ t0 t1 s0 s1 Nt Dt Ns Ds hside ⟨tn, tc⟩ ⟨sn, sc⟩
      ht0 ht1 hs0 hs1)
  have h3 : elim.minor (elim.selM [i, j] [i, j]
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) < BPair.unit :=
    BPair.lt_congr (box2_bridge hsh i j tn tc sn sc)
      (BPair.oneValue_refl _) h2
  have hr := inertia.revSel_mixed _ hMsq hMsym i j hi hj h3
  exact ⟨hr.1, hr.2, h3⟩

/-- The upper order-two block's frame at a point of the box: the
determinant on its upper side with the leading entry's own side
reading the table. -/
private theorem side_twoUp2 {o : Nat} (S : split.PPMat) (Ks Kt : Nat)
    (t0 t1 s0 s1 : CPair) (i j : Nat) (Nt Dt Ns Ds : BPair) (eUp : Bool)
    (eNt eDt eNs eDs : BPair)
    (hsh : ppShapeAt S o Ks Kt)
    (hidx : (([i, j] : List Nat).all (fun t => Nat.blt t o)) = true)
    (hside : stage.keepUpperBox (split.ppminor (split.ppselM [i, j] [i, j] S))
      t0 t1 s0 s1 Nt Dt Ns Ds)
    (hent : if eUp then
        stage.keepUpperBox (ground.getAt ([] : PPoly)
          (ground.getAt ([] : List PPoly) S i) i) t0 t1 s0 s1 eNt eDt eNs eDs
      else
        stage.keepLowerBox (ground.getAt ([] : PPoly)
          (ground.getAt ([] : List PPoly) S i) i) t0 t1 s0 s1 eNt eDt eNs eDs)
    (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (ht0 : t0 ≤ ⟨tn, tc⟩) (ht1 : (⟨tn, tc⟩ : CPair) ≤ t1)
    (hs0 : s0 ≤ ⟨sn, sc⟩) (hs1 : (⟨sn, sc⟩ : CPair) ≤ s1)
    (hMsym : elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) :
    (¬ (elim.minor (elim.selM [i, j] [i, j]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks))).oneValue BPair.unit)
    ∧ inertia.revAt (inertia.mkSplit ([i, j] : List Nat).length
        (elim.selM [i, j] [i, j] (evalPC (ppevalPC S tn tc Kt) sn sc Ks)))
      = (if eUp = true then 0 else 2)
    ∧ BPair.unit < elim.minor (elim.selM [i, j] [i, j]
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) := by
  have hs1' := ground.andSplitB hidx
  have hs2' := ground.andSplitB hs1'.2
  have hi : i < o := ground.bltLt hs1'.1
  have hj : j < o := ground.bltLt hs2'.1
  have hsh' := pShapeAt_ppevalPC hsh tn tc
  have hMsq : elim.sqAt (evalPC (ppevalPC S tn tc Kt) sn sc Ks) o :=
    evalPC_sqAt hsh' sn sc
  have h2 := sideBox_up (split.ppminor (split.ppselM [i, j] [i, j] S))
    (Kt + Kt) (Ks + Ks) (ppminor2_innerLe hsh i j) (ppminor2_len hsh i j)
    tn tc sn sc
    (stage.keepUpperBox_all _ t0 t1 s0 s1 Nt Dt Ns Ds hside ⟨tn, tc⟩ ⟨sn, sc⟩
      ht0 ht1 hs0 hs1)
  have h3 : BPair.unit < elim.minor (elim.selM [i, j] [i, j]
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (box2_bridge hsh i j tn tc sn sc) h2
  have hent' := ppShape_entry hsh i i
  match eUp, hent with
  | true, he =>
    have e2 := sideBox_up (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly) S i) i) Kt Ks hent'.2 hent'.1
      tn tc sn sc
      (stage.keepUpperBox_all _ t0 t1 s0 s1 eNt eDt eNs eDs he ⟨tn, tc⟩ ⟨sn, sc⟩
        ht0 ht1 hs0 hs1)
    have e3 : BPair.unit < ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks) i) i := by
      rw [getAt_evalPC sn sc Ks _ i i, getAt_ppevalPC tn tc Kt S i i]
      exact e2
    have hr := inertia.revSel_twoUp _ hMsq hMsym i j hi hj h3 true e3
    exact ⟨hr.1, hr.2, h3⟩
  | false, he =>
    have e2 := sideBox_down (ground.getAt ([] : PPoly)
        (ground.getAt ([] : List PPoly) S i) i) Kt Ks hent'.2 hent'.1
      tn tc sn sc
      (stage.keepLowerBox_all _ t0 t1 s0 s1 eNt eDt eNs eDs he ⟨tn, tc⟩ ⟨sn, sc⟩
        ht0 ht1 hs0 hs1)
    have e3 : ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks) i) i < BPair.unit := by
      rw [getAt_evalPC sn sc Ks _ i i, getAt_ppevalPC tn tc Kt S i i]
      exact e2
    have hr := inertia.revSel_twoUp _ hMsq hMsym i j hi hj h3 false e3
    exact ⟨hr.1, hr.2, h3⟩

/-! `lem:cellcount`'s box cover: the box cut at stated points, one
variable per cut, each point strictly inside its variable's bracket,
into pieces, each with a designated principal minor of order at most
two keeping its side over the piece at the box's
priced side read, at order two its leading entry so as well where
the determinant sits on its upper side, and beneath it the
once-cleared deflation's own box cover over the piece, the deflation
at a pivot whose determinant keeps its upper side and its memberwise
swap at a pivot keeping its lower side or at the mixed block. -/

set_option genInjectivity false in
/-- The box cover: the order-nought deflation, one piece per
designation over the box (the designated places, the determinant's
priced box read at stated bounds, the lower side the mixed order-two
row, at order two with the determinant upper the leading entry's own
read, and beneath it the once-cleared deflation's cover over the same
box, the deflation or its swap at the determinant's side), and the
box cut at a stated point of either variable into two covered
boxes. -/
inductive Cover2 where
  | nought : Cover2
  | one (i : Nat) (up : Bool) (Nt Dt Ns Ds : BPair) (sub : Cover2) : Cover2
  | mixed (i j : Nat) (Nt Dt Ns Ds : BPair) (sub : Cover2) : Cover2
  | twoUp (i j : Nat) (Nt Dt Ns Ds : BPair) (eUp : Bool)
      (eNt eDt eNs eDs : BPair) (sub : Cover2) : Cover2
  | cutT (c : CPair) (left right : Cover2) : Cover2
  | cutS (c : CPair) (left right : Cover2) : Cover2

/-- The cover's read at a pencil, an order, the two clearings and a
box: the order-nought deflation reads its order, a piece reads its
places' frame, the designated minor's priced box read and the cover
beneath it over the box at the once-cleared deflation or its swap at
the determinant's side, the clearings at the pivot order's successor
multiple, and a cut reads its point strictly inside the variable's
bracket with the two covers at the two boxes, the cut's two boxes
meeting along it. -/
def coverRead2 (S : split.PPMat) (o Ks Kt : Nat) (t0 t1 s0 s1 : CPair) :
    Cover2 → Prop
  | .nought => Nat.beq o 0 = true
  | .one i up Nt Dt Ns Ds sub =>
      pieceRead o [i]
      ∧ (if up then
          stage.keepUpperBox (split.ppminor (split.ppselM [i] [i] S))
            t0 t1 s0 s1 Nt Dt Ns Ds
        else
          stage.keepLowerBox (split.ppminor (split.ppselM [i] [i] S))
            t0 t1 s0 s1 Nt Dt Ns Ds)
      ∧ (if up then
          coverRead2 (pdeflP2 [i] (compl [i] o) S) (o - 1) (2 * Ks) (2 * Kt)
            t0 t1 s0 s1 sub
        else
          coverRead2 (pdeflM2 [i] (compl [i] o) S) (o - 1) (2 * Ks) (2 * Kt)
            t0 t1 s0 s1 sub)
  | .mixed i j Nt Dt Ns Ds sub =>
      pieceRead o [i, j]
      ∧ stage.keepLowerBox (split.ppminor (split.ppselM [i, j] [i, j] S))
          t0 t1 s0 s1 Nt Dt Ns Ds
      ∧ coverRead2 (pdeflM2 [i, j] (compl [i, j] o) S) (o - 2) (3 * Ks) (3 * Kt)
          t0 t1 s0 s1 sub
  | .twoUp i j Nt Dt Ns Ds eUp eNt eDt eNs eDs sub =>
      pieceRead o [i, j]
      ∧ stage.keepUpperBox (split.ppminor (split.ppselM [i, j] [i, j] S))
          t0 t1 s0 s1 Nt Dt Ns Ds
      ∧ (if eUp then
          stage.keepUpperBox (ground.getAt [] (ground.getAt [] S i) i)
            t0 t1 s0 s1 eNt eDt eNs eDs
        else
          stage.keepLowerBox (ground.getAt [] (ground.getAt [] S i) i)
            t0 t1 s0 s1 eNt eDt eNs eDs)
      ∧ coverRead2 (pdeflP2 [i, j] (compl [i, j] o) S) (o - 2) (3 * Ks) (3 * Kt)
          t0 t1 s0 s1 sub
  | .cutT c left right =>
      t0 < c ∧ c < t1
      ∧ coverRead2 S o Ks Kt t0 c s0 s1 left
      ∧ coverRead2 S o Ks Kt c t1 s0 s1 right
  | .cutS c left right =>
      s0 < c ∧ c < s1
      ∧ coverRead2 S o Ks Kt t0 t1 s0 c left
      ∧ coverRead2 S o Ks Kt t0 t1 c s1 right

/-- The cover read's decision, one arm per constructor with the
covers beneath and beside decided in turn, a side read and the
deflation beneath it decided at their own guard. -/
instance decCoverRead2 (S : split.PPMat) (o Ks Kt : Nat) (t0 t1 s0 s1 : CPair) :
    ∀ cov : Cover2, Decidable (coverRead2 S o Ks Kt t0 t1 s0 s1 cov)
  | .nought => inferInstanceAs (Decidable (Nat.beq o 0 = true))
  | .one i up Nt Dt Ns Ds sub =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead o [i])))
      (@instDecidableAnd _ _
        (match up with
          | true => inferInstanceAs (Decidable (stage.keepUpperBox
              (split.ppminor (split.ppselM [i] [i] S)) t0 t1 s0 s1 Nt Dt Ns Ds))
          | false => inferInstanceAs (Decidable (stage.keepLowerBox
              (split.ppminor (split.ppselM [i] [i] S)) t0 t1 s0 s1 Nt Dt Ns Ds)))
        (match up with
          | true => decCoverRead2 (pdeflP2 [i] (compl [i] o) S) (o - 1) (2 * Ks)
              (2 * Kt) t0 t1 s0 s1 sub
          | false => decCoverRead2 (pdeflM2 [i] (compl [i] o) S) (o - 1) (2 * Ks)
              (2 * Kt) t0 t1 s0 s1 sub))
  | .mixed i j Nt Dt Ns Ds sub =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead o [i, j])))
      (@instDecidableAnd _ _
        (inferInstanceAs (Decidable (stage.keepLowerBox
          (split.ppminor (split.ppselM [i, j] [i, j] S)) t0 t1 s0 s1 Nt Dt Ns Ds)))
        (decCoverRead2 (pdeflM2 [i, j] (compl [i, j] o) S) (o - 2) (3 * Ks)
          (3 * Kt) t0 t1 s0 s1 sub))
  | .twoUp i j Nt Dt Ns Ds eUp eNt eDt eNs eDs sub =>
    @instDecidableAnd _ _
      (inferInstanceAs (Decidable (pieceRead o [i, j])))
      (@instDecidableAnd _ _
        (inferInstanceAs (Decidable (stage.keepUpperBox
          (split.ppminor (split.ppselM [i, j] [i, j] S)) t0 t1 s0 s1
          Nt Dt Ns Ds)))
        (@instDecidableAnd _ _
          (match eUp with
            | true => inferInstanceAs (Decidable (stage.keepUpperBox
                (ground.getAt [] (ground.getAt [] S i) i) t0 t1 s0 s1
                eNt eDt eNs eDs))
            | false => inferInstanceAs (Decidable (stage.keepLowerBox
                (ground.getAt [] (ground.getAt [] S i) i) t0 t1 s0 s1
                eNt eDt eNs eDs)))
          (decCoverRead2 (pdeflP2 [i, j] (compl [i, j] o) S) (o - 2) (3 * Ks)
            (3 * Kt) t0 t1 s0 s1 sub)))
  | .cutT c left right =>
    @instDecidableAnd _ _ (inferInstanceAs (Decidable (t0 < c)))
      (@instDecidableAnd _ _ (inferInstanceAs (Decidable (c < t1)))
        (@instDecidableAnd _ _
          (decCoverRead2 S o Ks Kt t0 c s0 s1 left)
          (decCoverRead2 S o Ks Kt c t1 s0 s1 right)))
  | .cutS c left right =>
    @instDecidableAnd _ _ (inferInstanceAs (Decidable (s0 < c)))
      (@instDecidableAnd _ _ (inferInstanceAs (Decidable (c < s1)))
        (@instDecidableAnd _ _
          (decCoverRead2 S o Ks Kt t0 t1 s0 c left)
          (decCoverRead2 S o Ks Kt t0 t1 c s1 right)))

/-! The cover's proof tier: the deflations' symmetry at a point of
the box where the pivot sits off the unit, one piece's count at a
point as the pivot's block read joined to the deflation's, and the
constancy walk. -/

/-- The double-evaluated once-cleared deflation at a point where the
double-evaluated pencil is symmetric and the pivot's minor sits off
the unit is symmetric: the inner evaluation reads the deflation as
the inner-evaluated pencil's own, whose evaluated deflation is
symmetric (`evalPC_pdeflP_symm`), the symmetry carried across the
read. -/
private theorem defl2P_symF {o : Nat} (S : split.PPMat) (Ks Kt : Nat)
    (idx : List Nat) (hsh : ppShapeAt S o Ks Kt)
    (hk0 : 0 < idx.length)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (hMsym : elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
    (hPnz : ¬ (elim.minor (elim.selM idx idx
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks))).oneValue BPair.unit) :
    elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC (pdeflP2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks)))
      (evalPC (ppevalPC (pdeflP2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks)) := by
  have hE : elim.matOneValue
      (evalPC (ppevalPC (pdeflP2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks))
      (evalPC (pdeflP idx (compl idx o) (ppevalPC S tn tc Kt)) sn sc
        ((idx.length + 1) * Ks)) :=
    evalPC_pcongr sn sc _ (ppevalPC_pdeflP2 S idx (compl idx o) tn tc hsh hk0)
  have hL : elim.sqAt (evalPC (ppevalPC (pdeflP2 idx (compl idx o) S) tn tc
      ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks))
      (compl idx o).length :=
    evalPC_sqAt (pShapeAt_ppevalPC
      (ppShape_pdeflP2 S o Ks Kt idx (compl idx o) hsh) tn tc) sn sc
  have hR : elim.sqAt (evalPC (pdeflP idx (compl idx o) (ppevalPC S tn tc Kt))
      sn sc ((idx.length + 1) * Ks)) (compl idx o).length :=
    evalPC_sqAt (pShape_pdeflP (ppevalPC S tn tc Kt) o Ks idx (compl idx o)
      (pShapeAt_ppevalPC hsh tn tc)) sn sc
  have hDs := evalPC_pdeflP_symm (ppevalPC S tn tc Kt) Ks idx (compl idx o) sn sc
    (pShapeAt_ppevalPC hsh tn tc) hMsym hk0 hidx (all_compl idx o) hPnz
  have hT := elim.transposeM_congrM (compl idx o).length _ _
    (elim.rowsLen_of_sqAt hL) (elim.rowsLen_of_sqAt hR)
    ((elim.sqAt_len hL).trans (elim.sqAt_len hR).symm) hE
  exact elim.matOne_trans hT (elim.matOne_trans hDs (elim.matOne_symm hE))

/-- The double-evaluated swapped deflation at a point where the
double-evaluated pencil is symmetric and the pivot's minor sits off
the unit is symmetric (`evalPC_pdeflM_symm` across the inner
evaluation's read). -/
private theorem defl2M_symF {o : Nat} (S : split.PPMat) (Ks Kt : Nat)
    (idx : List Nat) (hsh : ppShapeAt S o Ks Kt)
    (hk0 : 0 < idx.length)
    (hidx : (idx.all (fun i => Nat.blt i o)) = true)
    (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (hMsym : elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
    (hPnz : ¬ (elim.minor (elim.selM idx idx
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks))).oneValue BPair.unit) :
    elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC (pdeflM2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks)))
      (evalPC (ppevalPC (pdeflM2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks)) := by
  have hE : elim.matOneValue
      (evalPC (ppevalPC (pdeflM2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks))
      (evalPC (pdeflM idx (compl idx o) (ppevalPC S tn tc Kt)) sn sc
        ((idx.length + 1) * Ks)) :=
    evalPC_pcongr sn sc _ (ppevalPC_pdeflM2 S idx (compl idx o) tn tc hsh hk0)
  have hL : elim.sqAt (evalPC (ppevalPC (pdeflM2 idx (compl idx o) S) tn tc
      ((idx.length + 1) * Kt)) sn sc ((idx.length + 1) * Ks))
      (compl idx o).length :=
    evalPC_sqAt (pShapeAt_ppevalPC
      (ppShape_pdeflM2 S o Ks Kt idx (compl idx o) hsh) tn tc) sn sc
  have hR : elim.sqAt (evalPC (pdeflM idx (compl idx o) (ppevalPC S tn tc Kt))
      sn sc ((idx.length + 1) * Ks)) (compl idx o).length :=
    evalPC_sqAt (pShape_pdeflM (ppevalPC S tn tc Kt) o Ks idx (compl idx o)
      (pShapeAt_ppevalPC hsh tn tc)) sn sc
  have hDs := evalPC_pdeflM_symm (ppevalPC S tn tc Kt) Ks idx (compl idx o) sn sc
    (pShapeAt_ppevalPC hsh tn tc) hMsym hk0 hidx (all_compl idx o) hPnz
  have hT := elim.transposeM_congrM (compl idx o).length _ _
    (elim.rowsLen_of_sqAt hL) (elim.rowsLen_of_sqAt hR)
    ((elim.sqAt_len hL).trans (elim.sqAt_len hR).symm) hE
  exact elim.matOne_trans hT (elim.matOne_trans hDs (elim.matOne_symm hE))

/-- One piece's count at a point of the box at a pivot whose
determinant keeps its upper side: the count is the pivot's block read
joined to the once-cleared deflation's (`piece_addP`), the
deflation's double evaluation carried to the evaluated pencil's own
deflation. -/
private theorem piece_keyP2 {o m : Nat} (S : split.PPMat) (Ks Kt KKs KKt : Nat)
    (idx : List Nat) (hpc : pieceRead o idx) (hsh : ppShapeAt S o Ks Kt)
    (hk0 : 0 < idx.length)
    (hm : (compl idx o).length = m)
    (hKKs : KKs = (idx.length + 1) * Ks)
    (hKKt : KKt = (idx.length + 1) * Kt)
    (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (hMsym : elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
    (hPpos : BPair.unit < elim.minor (elim.selM idx idx
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks)))
    (spz : inertia.Split o)
    (hz : inertia.splitRead (evalPC (ppevalPC S tn tc Kt) sn sc Ks) spz)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (evalPC (ppevalPC (pdeflP2 idx (compl idx o) S) tn tc KKt) sn sc KKs)
      spD) :
    inertia.revAt spz
      = inertia.revAt (inertia.mkSplit idx.length
          (elim.selM idx idx (evalPC (ppevalPC S tn tc Kt) sn sc Ks)))
        + inertia.revAt spD := by
  subst hKKt
  have hDefl : elim.matOneValue
      (evalPC (ppevalPC (pdeflP2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc KKs)
      (evalPC (pdeflP idx (compl idx o) (ppevalPC S tn tc Kt)) sn sc KKs) :=
    evalPC_pcongr sn sc KKs
      (ppevalPC_pdeflP2 S idx (compl idx o) tn tc hsh hk0)
  have hDsq : elim.sqAt
      (evalPC (pdeflP idx (compl idx o) (ppevalPC S tn tc Kt)) sn sc KKs) m := by
    subst hKKs
    have h1 := evalPC_sqAt
      (pShape_pdeflP (ppevalPC S tn tc Kt) o Ks idx (compl idx o)
        (pShapeAt_ppevalPC hsh tn tc)) sn sc
    rw [hm] at h1
    exact h1
  exact piece_addP (ppevalPC S tn tc Kt) Ks KKs idx hpc
    (pShapeAt_ppevalPC hsh tn tc) hk0 hm hKKs sn sc hMsym hPpos spz hz spD
    (inertia.splitRead_congr _ _ hDsq hDefl spD hD)

/-- One piece's count at a point of the box at a pivot whose
determinant keeps its lower side or at the mixed block: the count is
the pivot's block read joined to the swapped once-cleared
deflation's (`piece_addM`), the deflation's double evaluation carried
to the evaluated pencil's own swapped deflation. -/
private theorem piece_keyM2 {o m : Nat} (S : split.PPMat) (Ks Kt KKs KKt : Nat)
    (idx : List Nat) (hpc : pieceRead o idx) (hsh : ppShapeAt S o Ks Kt)
    (hk0 : 0 < idx.length)
    (hm : (compl idx o).length = m)
    (hKKs : KKs = (idx.length + 1) * Ks)
    (hKKt : KKt = (idx.length + 1) * Kt)
    (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos)
    (hMsym : elim.matOneValue
      (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
    (hPneg : elim.minor (elim.selM idx idx
      (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) < BPair.unit)
    (spz : inertia.Split o)
    (hz : inertia.splitRead (evalPC (ppevalPC S tn tc Kt) sn sc Ks) spz)
    (spD : inertia.Split m)
    (hD : inertia.splitRead
      (evalPC (ppevalPC (pdeflM2 idx (compl idx o) S) tn tc KKt) sn sc KKs)
      spD) :
    inertia.revAt spz
      = inertia.revAt (inertia.mkSplit idx.length
          (elim.selM idx idx (evalPC (ppevalPC S tn tc Kt) sn sc Ks)))
        + inertia.revAt spD := by
  subst hKKt
  have hDefl : elim.matOneValue
      (evalPC (ppevalPC (pdeflM2 idx (compl idx o) S) tn tc
        ((idx.length + 1) * Kt)) sn sc KKs)
      (evalPC (pdeflM idx (compl idx o) (ppevalPC S tn tc Kt)) sn sc KKs) :=
    evalPC_pcongr sn sc KKs
      (ppevalPC_pdeflM2 S idx (compl idx o) tn tc hsh hk0)
  have hDsq : elim.sqAt
      (evalPC (pdeflM idx (compl idx o) (ppevalPC S tn tc Kt)) sn sc KKs) m := by
    subst hKKs
    have h1 := evalPC_sqAt
      (pShape_pdeflM (ppevalPC S tn tc Kt) o Ks idx (compl idx o)
        (pShapeAt_ppevalPC hsh tn tc)) sn sc
    rw [hm] at h1
    exact h1
  exact piece_addM (ppevalPC S tn tc Kt) Ks KKs idx hpc
    (pShapeAt_ppevalPC hsh tn tc) hk0 hm hKKs sn sc hMsym hPneg spz hz spD
    (inertia.splitRead_congr _ _ hDsq hDefl spD hD)

/-- One piece's constancy at a stated deflation beneath it: at every
point of the box the count is the piece's fixed value joined to the
deflation's, the deflation's count one integer over the box at its
own cover, the deflation shaped and symmetric over the box. -/
private theorem piece_go {o m : Nat} (S D : split.PPMat) (Ks Kt KKs KKt : Nat)
    (t0 t1 s0 s1 : CPair) (r : Nat)
    (hshD : ppShapeAt D m KKs KKt)
    (hDsymF : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
      t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
      elim.matOneValue
        (elim.transposeM (evalPC (ppevalPC D tn tc KKt) sn sc KKs))
        (evalPC (ppevalPC D tn tc KKt) sn sc KKs))
    (key : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
      t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
      ∀ (spz : inertia.Split o),
        inertia.splitRead (evalPC (ppevalPC S tn tc Kt) sn sc Ks) spz →
        ∀ (spD : inertia.Split m),
          inertia.splitRead (evalPC (ppevalPC D tn tc KKt) sn sc KKs) spD →
          inertia.revAt spz = r + inertia.revAt spD)
    (ihSub : ∀ (utn : BPair) (utc : Pos) (usn : BPair) (usc : Pos)
      (vtn : BPair) (vtc : Pos) (vsn : BPair) (vsc : Pos),
      t0 ≤ ⟨utn, utc⟩ → (⟨utn, utc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨usn, usc⟩ → (⟨usn, usc⟩ : CPair) ≤ s1 →
      t0 ≤ ⟨vtn, vtc⟩ → (⟨vtn, vtc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨vsn, vsc⟩ → (⟨vsn, vsc⟩ : CPair) ≤ s1 →
      ∀ (spu spv : inertia.Split m),
        inertia.splitRead (evalPC (ppevalPC D utn utc KKt) usn usc KKs) spu →
        inertia.splitRead (evalPC (ppevalPC D vtn vtc KKt) vsn vsc KKs) spv →
        inertia.revAt spu = inertia.revAt spv)
    (xtn : BPair) (xtc : Pos) (xsn : BPair) (xsc : Pos)
    (ytn : BPair) (ytc : Pos) (ysn : BPair) (ysc : Pos)
    (hx0 : t0 ≤ ⟨xtn, xtc⟩) (hx1 : (⟨xtn, xtc⟩ : CPair) ≤ t1)
    (hxs0 : s0 ≤ ⟨xsn, xsc⟩) (hxs1 : (⟨xsn, xsc⟩ : CPair) ≤ s1)
    (hy0 : t0 ≤ ⟨ytn, ytc⟩) (hy1 : (⟨ytn, ytc⟩ : CPair) ≤ t1)
    (hys0 : s0 ≤ ⟨ysn, ysc⟩) (hys1 : (⟨ysn, ysc⟩ : CPair) ≤ s1)
    (spx spy : inertia.Split o)
    (hx : inertia.splitRead (evalPC (ppevalPC S xtn xtc Kt) xsn xsc Ks) spx)
    (hy : inertia.splitRead (evalPC (ppevalPC S ytn ytc Kt) ysn ysc Ks) spy) :
    inertia.revAt spx = inertia.revAt spy := by
  have mkD : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
      t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
      inertia.splitRead (evalPC (ppevalPC D tn tc KKt) sn sc KKs)
        (inertia.mkSplit m (evalPC (ppevalPC D tn tc KKt) sn sc KKs)) :=
    fun tn tc sn sc ht0 ht1 hs0 hs1 =>
      inertia.mkSplit_read m _ (evalPC_sqAt (pShapeAt_ppevalPC hshD tn tc) sn sc)
        (hDsymF tn tc sn sc ht0 ht1 hs0 hs1)
  rw [key xtn xtc xsn xsc hx0 hx1 hxs0 hxs1 spx hx _
      (mkD xtn xtc xsn xsc hx0 hx1 hxs0 hxs1),
    key ytn ytc ysn ysc hy0 hy1 hys0 hys1 spy hy _
      (mkD ytn ytc ysn ysc hy0 hy1 hys0 hys1)]
  exact congrArg (fun t => r + t)
    (ihSub xtn xtc xsn xsc ytn ytc ysn ysc hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1
      _ _ (mkD xtn xtc xsn xsc hx0 hx1 hxs0 hxs1)
      (mkD ytn ytc ysn ysc hy0 hy1 hys0 hys1))

/-- The cover's constancy walk at a shaped pencil symmetric at every
point of the box: the order-nought deflation at the vacant count,
each piece at its own block value with the once-cleared deflation's
cover beneath it, the deflation or its swap at the determinant's
side, and a cut's two boxes read through a point of the cut. -/
private theorem cover2_go : ∀ (cov : Cover2) (o : Nat) (S : split.PPMat)
    (Ks Kt : Nat) (t0 t1 s0 s1 : CPair),
    coverRead2 S o Ks Kt t0 t1 s0 s1 cov →
    ppShapeAt S o Ks Kt →
    (∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
      t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
      elim.matOneValue
        (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
        (evalPC (ppevalPC S tn tc Kt) sn sc Ks)) →
    ∀ (xtn : BPair) (xtc : Pos) (xsn : BPair) (xsc : Pos)
      (ytn : BPair) (ytc : Pos) (ysn : BPair) (ysc : Pos),
      t0 ≤ ⟨xtn, xtc⟩ → (⟨xtn, xtc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨xsn, xsc⟩ → (⟨xsn, xsc⟩ : CPair) ≤ s1 →
      t0 ≤ ⟨ytn, ytc⟩ → (⟨ytn, ytc⟩ : CPair) ≤ t1 →
      s0 ≤ ⟨ysn, ysc⟩ → (⟨ysn, ysc⟩ : CPair) ≤ s1 →
    ∀ (spx spy : inertia.Split o),
      inertia.splitRead (evalPC (ppevalPC S xtn xtc Kt) xsn xsc Ks) spx →
      inertia.splitRead (evalPC (ppevalPC S ytn ytc Kt) ysn ysc Ks) spy →
      inertia.revAt spx = inertia.revAt spy
  | .nought => by
    intro o S Ks Kt t0 t1 s0 s1 h _ _ xtn xtc xsn xsc ytn ytc ysn ysc
      _ _ _ _ _ _ _ _ spx spy _ _
    have h0 : o = 0 := ground.beqEq _ _ h
    subst h0
    rw [inertia.revAt_zero spx, inertia.revAt_zero spy]
  | .one i true Nt Dt Ns Ds sub => by
    intro o S Ks Kt t0 t1 s0 s1 h hsh hsymF xtn xtc xsn xsc ytn ytc ysn ysc
      hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1 spx spy hx hy
    have hs : stage.keepUpperBox (split.ppminor (split.ppselM [i] [i] S))
        t0 t1 s0 s1 Nt Dt Ns Ds := h.2.1
    have hsub : coverRead2 (pdeflP2 [i] (compl [i] o) S) (o - 1) (2 * Ks) (2 * Kt)
        t0 t1 s0 s1 sub := h.2.2
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans
        (congrArg (fun t => t - 1) (compl_length h.1.2 h.1.1))
    have hshS : ppShapeAt (pdeflP2 [i] (compl [i] o) S) (o - 1) (2 * Ks) (2 * Kt) := by
      have h1 := ppShape_pdeflP2 S o Ks Kt [i] (compl [i] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsym : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
        s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC (pdeflP2 [i] (compl [i] o) S) tn tc
            (2 * Kt)) sn sc (2 * Ks)))
          (evalPC (ppevalPC (pdeflP2 [i] (compl [i] o) S) tn tc (2 * Kt))
            sn sc (2 * Ks)) :=
      fun tn tc sn sc ht0 ht1 hs0 hs1 =>
        defl2P_symF S Ks Kt [i] hsh (Nat.succ_pos 0) h.1.1 tn tc sn sc
          (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
          (side_one2 S Ks Kt t0 t1 s0 s1 i true Nt Dt Ns Ds hsh h.1.1 hs
            tn tc sn sc ht0 ht1 hs0 hs1 (hsymF tn tc sn sc ht0 ht1 hs0 hs1)).1
    exact piece_go S (pdeflP2 [i] (compl [i] o) S) Ks Kt (2 * Ks) (2 * Kt)
      t0 t1 s0 s1 (if true = true then 0 else 1) hshS hDsym
      (fun tn tc sn sc ht0 ht1 hs0 hs1 spz hz spD hD => by
        have hsd := side_one2 S Ks Kt t0 t1 s0 s1 i true Nt Dt Ns Ds hsh h.1.1 hs
          tn tc sn sc ht0 ht1 hs0 hs1 (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
        rw [← hsd.2.1]
        exact piece_keyP2 S Ks Kt (2 * Ks) (2 * Kt) [i] h.1 hsh (Nat.succ_pos 0) hcl
          rfl rfl tn tc sn sc (hsymF tn tc sn sc ht0 ht1 hs0 hs1) (hsd.2.2.1 rfl)
          spz hz spD hD)
      (fun utn utc usn usc vtn vtc vsn vsc h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv =>
        cover2_go sub (o - 1) (pdeflP2 [i] (compl [i] o) S) (2 * Ks) (2 * Kt)
          t0 t1 s0 s1 hsub hshS hDsym
          utn utc usn usc vtn vtc vsn vsc
          h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv)
      xtn xtc xsn xsc ytn ytc ysn ysc hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1
      spx spy hx hy
  | .one i false Nt Dt Ns Ds sub => by
    intro o S Ks Kt t0 t1 s0 s1 h hsh hsymF xtn xtc xsn xsc ytn ytc ysn ysc
      hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1 spx spy hx hy
    have hs : stage.keepLowerBox (split.ppminor (split.ppselM [i] [i] S))
        t0 t1 s0 s1 Nt Dt Ns Ds := h.2.1
    have hsub : coverRead2 (pdeflM2 [i] (compl [i] o) S) (o - 1) (2 * Ks) (2 * Kt)
        t0 t1 s0 s1 sub := h.2.2
    have hcl : (compl [i] o).length = o - 1 :=
      ((ground.addSubSelfL 1 _).symm).trans
        (congrArg (fun t => t - 1) (compl_length h.1.2 h.1.1))
    have hshS : ppShapeAt (pdeflM2 [i] (compl [i] o) S) (o - 1) (2 * Ks) (2 * Kt) := by
      have h1 := ppShape_pdeflM2 S o Ks Kt [i] (compl [i] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsym : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
        s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC (pdeflM2 [i] (compl [i] o) S) tn tc
            (2 * Kt)) sn sc (2 * Ks)))
          (evalPC (ppevalPC (pdeflM2 [i] (compl [i] o) S) tn tc (2 * Kt))
            sn sc (2 * Ks)) :=
      fun tn tc sn sc ht0 ht1 hs0 hs1 =>
        defl2M_symF S Ks Kt [i] hsh (Nat.succ_pos 0) h.1.1 tn tc sn sc
          (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
          (side_one2 S Ks Kt t0 t1 s0 s1 i false Nt Dt Ns Ds hsh h.1.1 hs
            tn tc sn sc ht0 ht1 hs0 hs1 (hsymF tn tc sn sc ht0 ht1 hs0 hs1)).1
    exact piece_go S (pdeflM2 [i] (compl [i] o) S) Ks Kt (2 * Ks) (2 * Kt)
      t0 t1 s0 s1 (if false = true then 0 else 1) hshS hDsym
      (fun tn tc sn sc ht0 ht1 hs0 hs1 spz hz spD hD => by
        have hsd := side_one2 S Ks Kt t0 t1 s0 s1 i false Nt Dt Ns Ds hsh h.1.1 hs
          tn tc sn sc ht0 ht1 hs0 hs1 (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
        rw [← hsd.2.1]
        exact piece_keyM2 S Ks Kt (2 * Ks) (2 * Kt) [i] h.1 hsh (Nat.succ_pos 0) hcl
          rfl rfl tn tc sn sc (hsymF tn tc sn sc ht0 ht1 hs0 hs1) (hsd.2.2.2 rfl)
          spz hz spD hD)
      (fun utn utc usn usc vtn vtc vsn vsc h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv =>
        cover2_go sub (o - 1) (pdeflM2 [i] (compl [i] o) S) (2 * Ks) (2 * Kt)
          t0 t1 s0 s1 hsub hshS hDsym
          utn utc usn usc vtn vtc vsn vsc
          h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv)
      xtn xtc xsn xsc ytn ytc ysn ysc hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1
      spx spy hx hy
  | .mixed i j Nt Dt Ns Ds sub => by
    intro o S Ks Kt t0 t1 s0 s1 h hsh hsymF xtn xtc xsn xsc ytn ytc ysn ysc
      hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1 spx spy hx hy
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans
        (congrArg (fun t => t - 2) (compl_length h.1.2 h.1.1))
    have hshS : ppShapeAt (pdeflM2 [i, j] (compl [i, j] o) S) (o - 2)
        (3 * Ks) (3 * Kt) := by
      have h1 := ppShape_pdeflM2 S o Ks Kt [i, j] (compl [i, j] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsym : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
        s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC (pdeflM2 [i, j] (compl [i, j] o) S)
            tn tc (3 * Kt)) sn sc (3 * Ks)))
          (evalPC (ppevalPC (pdeflM2 [i, j] (compl [i, j] o) S) tn tc (3 * Kt))
            sn sc (3 * Ks)) :=
      fun tn tc sn sc ht0 ht1 hs0 hs1 =>
        defl2M_symF S Ks Kt [i, j] hsh (Nat.succ_pos 1) h.1.1 tn tc sn sc
          (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
          (side_mixed2 S Ks Kt t0 t1 s0 s1 i j Nt Dt Ns Ds hsh h.1.1 h.2.1
            tn tc sn sc ht0 ht1 hs0 hs1 (hsymF tn tc sn sc ht0 ht1 hs0 hs1)).1
    exact piece_go S (pdeflM2 [i, j] (compl [i, j] o) S) Ks Kt (3 * Ks) (3 * Kt)
      t0 t1 s0 s1 1 hshS hDsym
      (fun tn tc sn sc ht0 ht1 hs0 hs1 spz hz spD hD => by
        have hsd := side_mixed2 S Ks Kt t0 t1 s0 s1 i j Nt Dt Ns Ds hsh h.1.1 h.2.1
          tn tc sn sc ht0 ht1 hs0 hs1 (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
        rw [← hsd.2.1]
        exact piece_keyM2 S Ks Kt (3 * Ks) (3 * Kt) [i, j] h.1 hsh (Nat.succ_pos 1) hcl
          rfl rfl tn tc sn sc (hsymF tn tc sn sc ht0 ht1 hs0 hs1) hsd.2.2
          spz hz spD hD)
      (fun utn utc usn usc vtn vtc vsn vsc h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv =>
        cover2_go sub (o - 2) (pdeflM2 [i, j] (compl [i, j] o) S) (3 * Ks) (3 * Kt)
          t0 t1 s0 s1 h.2.2 hshS hDsym
          utn utc usn usc vtn vtc vsn vsc
          h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv)
      xtn xtc xsn xsc ytn ytc ysn ysc hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1
      spx spy hx hy
  | .twoUp i j Nt Dt Ns Ds eUp eNt eDt eNs eDs sub => by
    intro o S Ks Kt t0 t1 s0 s1 h hsh hsymF xtn xtc xsn xsc ytn ytc ysn ysc
      hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1 spx spy hx hy
    have hcl : (compl [i, j] o).length = o - 2 :=
      ((ground.addSubSelfL 2 _).symm).trans
        (congrArg (fun t => t - 2) (compl_length h.1.2 h.1.1))
    have hshS : ppShapeAt (pdeflP2 [i, j] (compl [i, j] o) S) (o - 2)
        (3 * Ks) (3 * Kt) := by
      have h1 := ppShape_pdeflP2 S o Ks Kt [i, j] (compl [i, j] o) hsh
      rw [hcl] at h1
      exact h1
    have hDsym : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
        s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC (pdeflP2 [i, j] (compl [i, j] o) S)
            tn tc (3 * Kt)) sn sc (3 * Ks)))
          (evalPC (ppevalPC (pdeflP2 [i, j] (compl [i, j] o) S) tn tc (3 * Kt))
            sn sc (3 * Ks)) :=
      fun tn tc sn sc ht0 ht1 hs0 hs1 =>
        defl2P_symF S Ks Kt [i, j] hsh (Nat.succ_pos 1) h.1.1 tn tc sn sc
          (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
          (side_twoUp2 S Ks Kt t0 t1 s0 s1 i j Nt Dt Ns Ds eUp eNt eDt eNs eDs
            hsh h.1.1 h.2.1 h.2.2.1 tn tc sn sc ht0 ht1 hs0 hs1
            (hsymF tn tc sn sc ht0 ht1 hs0 hs1)).1
    exact piece_go S (pdeflP2 [i, j] (compl [i, j] o) S) Ks Kt (3 * Ks) (3 * Kt)
      t0 t1 s0 s1 (if eUp = true then 0 else 2) hshS hDsym
      (fun tn tc sn sc ht0 ht1 hs0 hs1 spz hz spD hD => by
        have hsd := side_twoUp2 S Ks Kt t0 t1 s0 s1 i j Nt Dt Ns Ds eUp
          eNt eDt eNs eDs hsh h.1.1 h.2.1 h.2.2.1 tn tc sn sc ht0 ht1 hs0 hs1
          (hsymF tn tc sn sc ht0 ht1 hs0 hs1)
        rw [← hsd.2.1]
        exact piece_keyP2 S Ks Kt (3 * Ks) (3 * Kt) [i, j] h.1 hsh (Nat.succ_pos 1) hcl
          rfl rfl tn tc sn sc (hsymF tn tc sn sc ht0 ht1 hs0 hs1) hsd.2.2
          spz hz spD hD)
      (fun utn utc usn usc vtn vtc vsn vsc h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv =>
        cover2_go sub (o - 2) (pdeflP2 [i, j] (compl [i, j] o) S) (3 * Ks) (3 * Kt)
          t0 t1 s0 s1 h.2.2.2 hshS hDsym
          utn utc usn usc vtn vtc vsn vsc
          h1 h2 h3 h4 h5 h6 h7 h8 spu spv hu hv)
      xtn xtc xsn xsc ytn ytc ysn ysc hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1
      spx spy hx hy
  | .cutT c left right => by
    intro o S Ks Kt t0 t1 s0 s1 h hsh hsymF xtn xtc xsn xsc ytn ytc ysn ysc
      hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1 spx spy hx hy
    obtain ⟨cn, cc⟩ := c
    obtain ⟨s0n, s0c⟩ := s0
    have hs01 : (⟨s0n, s0c⟩ : CPair) ≤ s1 := CPair.le_trans hxs0 hxs1
    have hp : inertia.splitRead (evalPC (ppevalPC S cn cc Kt) s0n s0c Ks)
        (inertia.mkSplit o (evalPC (ppevalPC S cn cc Kt) s0n s0c Ks)) :=
      inertia.mkSplit_read o _ (evalPC_sqAt (pShapeAt_ppevalPC hsh cn cc) s0n s0c)
        (hsymF cn cc s0n s0c (Or.inr h.1) (Or.inr h.2.1) (CPair.le_refl _) hs01)
    have hsymL : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        t0 ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ ⟨cn, cc⟩ →
        (⟨s0n, s0c⟩ : CPair) ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
          (evalPC (ppevalPC S tn tc Kt) sn sc Ks) :=
      fun tn tc sn sc a b d e =>
        hsymF tn tc sn sc a (CPair.le_trans b (Or.inr h.2.1)) d e
    have hsymR : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        (⟨cn, cc⟩ : CPair) ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
        (⟨s0n, s0c⟩ : CPair) ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
          (evalPC (ppevalPC S tn tc Kt) sn sc Ks) :=
      fun tn tc sn sc a b d e =>
        hsymF tn tc sn sc (CPair.le_trans (Or.inr h.1) a) b d e
    have hx' : inertia.revAt spx
        = inertia.revAt (inertia.mkSplit o
          (evalPC (ppevalPC S cn cc Kt) s0n s0c Ks)) := by
      match CPair.le_total ⟨xtn, xtc⟩ ⟨cn, cc⟩ with
      | Or.inl hxc =>
        exact cover2_go left o S Ks Kt t0 ⟨cn, cc⟩ ⟨s0n, s0c⟩ s1 h.2.2.1 hsh hsymL
          xtn xtc xsn xsc cn cc s0n s0c hx0 hxc hxs0 hxs1 (Or.inr h.1)
          (CPair.le_refl _) (CPair.le_refl _) hs01 spx _ hx hp
      | Or.inr hcx =>
        exact cover2_go right o S Ks Kt ⟨cn, cc⟩ t1 ⟨s0n, s0c⟩ s1 h.2.2.2 hsh hsymR
          xtn xtc xsn xsc cn cc s0n s0c hcx hx1 hxs0 hxs1 (CPair.le_refl _)
          (Or.inr h.2.1) (CPair.le_refl _) hs01 spx _ hx hp
    have hy' : inertia.revAt spy
        = inertia.revAt (inertia.mkSplit o
          (evalPC (ppevalPC S cn cc Kt) s0n s0c Ks)) := by
      match CPair.le_total ⟨ytn, ytc⟩ ⟨cn, cc⟩ with
      | Or.inl hyc =>
        exact cover2_go left o S Ks Kt t0 ⟨cn, cc⟩ ⟨s0n, s0c⟩ s1 h.2.2.1 hsh hsymL
          ytn ytc ysn ysc cn cc s0n s0c hy0 hyc hys0 hys1 (Or.inr h.1)
          (CPair.le_refl _) (CPair.le_refl _) hs01 spy _ hy hp
      | Or.inr hcy =>
        exact cover2_go right o S Ks Kt ⟨cn, cc⟩ t1 ⟨s0n, s0c⟩ s1 h.2.2.2 hsh hsymR
          ytn ytc ysn ysc cn cc s0n s0c hcy hy1 hys0 hys1 (CPair.le_refl _)
          (Or.inr h.2.1) (CPair.le_refl _) hs01 spy _ hy hp
    exact hx'.trans hy'.symm
  | .cutS c left right => by
    intro o S Ks Kt t0 t1 s0 s1 h hsh hsymF xtn xtc xsn xsc ytn ytc ysn ysc
      hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1 spx spy hx hy
    obtain ⟨cn, cc⟩ := c
    obtain ⟨t0n, t0c⟩ := t0
    have ht01 : (⟨t0n, t0c⟩ : CPair) ≤ t1 := CPair.le_trans hx0 hx1
    have hp : inertia.splitRead (evalPC (ppevalPC S t0n t0c Kt) cn cc Ks)
        (inertia.mkSplit o (evalPC (ppevalPC S t0n t0c Kt) cn cc Ks)) :=
      inertia.mkSplit_read o _ (evalPC_sqAt (pShapeAt_ppevalPC hsh t0n t0c) cn cc)
        (hsymF t0n t0c cn cc (CPair.le_refl _) ht01 (Or.inr h.1) (Or.inr h.2.1))
    have hsymL : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        (⟨t0n, t0c⟩ : CPair) ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
        s0 ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ ⟨cn, cc⟩ →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
          (evalPC (ppevalPC S tn tc Kt) sn sc Ks) :=
      fun tn tc sn sc a b d e =>
        hsymF tn tc sn sc a b d (CPair.le_trans e (Or.inr h.2.1))
    have hsymR : ∀ (tn : BPair) (tc : Pos) (sn : BPair) (sc : Pos),
        (⟨t0n, t0c⟩ : CPair) ≤ ⟨tn, tc⟩ → (⟨tn, tc⟩ : CPair) ≤ t1 →
        (⟨cn, cc⟩ : CPair) ≤ ⟨sn, sc⟩ → (⟨sn, sc⟩ : CPair) ≤ s1 →
        elim.matOneValue
          (elim.transposeM (evalPC (ppevalPC S tn tc Kt) sn sc Ks))
          (evalPC (ppevalPC S tn tc Kt) sn sc Ks) :=
      fun tn tc sn sc a b d e =>
        hsymF tn tc sn sc a b (CPair.le_trans (Or.inr h.1) d) e
    have hx' : inertia.revAt spx
        = inertia.revAt (inertia.mkSplit o
          (evalPC (ppevalPC S t0n t0c Kt) cn cc Ks)) := by
      match CPair.le_total ⟨xsn, xsc⟩ ⟨cn, cc⟩ with
      | Or.inl hxc =>
        exact cover2_go left o S Ks Kt ⟨t0n, t0c⟩ t1 s0 ⟨cn, cc⟩ h.2.2.1 hsh hsymL
          xtn xtc xsn xsc t0n t0c cn cc hx0 hx1 hxs0 hxc (CPair.le_refl _)
          ht01 (Or.inr h.1) (CPair.le_refl _) spx _ hx hp
      | Or.inr hcx =>
        exact cover2_go right o S Ks Kt ⟨t0n, t0c⟩ t1 ⟨cn, cc⟩ s1 h.2.2.2 hsh hsymR
          xtn xtc xsn xsc t0n t0c cn cc hx0 hx1 hcx hxs1 (CPair.le_refl _)
          ht01 (CPair.le_refl _) (Or.inr h.2.1) spx _ hx hp
    have hy' : inertia.revAt spy
        = inertia.revAt (inertia.mkSplit o
          (evalPC (ppevalPC S t0n t0c Kt) cn cc Ks)) := by
      match CPair.le_total ⟨ysn, ysc⟩ ⟨cn, cc⟩ with
      | Or.inl hyc =>
        exact cover2_go left o S Ks Kt ⟨t0n, t0c⟩ t1 s0 ⟨cn, cc⟩ h.2.2.1 hsh hsymL
          ytn ytc ysn ysc t0n t0c cn cc hy0 hy1 hys0 hyc (CPair.le_refl _)
          ht01 (Or.inr h.1) (CPair.le_refl _) spy _ hy hp
      | Or.inr hcy =>
        exact cover2_go right o S Ks Kt ⟨t0n, t0c⟩ t1 ⟨cn, cc⟩ s1 h.2.2.2 hsh hsymR
          ytn ytc ysn ysc t0n t0c cn cc hy0 hy1 hcy hys1 (CPair.le_refl _)
          ht01 (CPair.le_refl _) (Or.inr h.2.1) spy _ hy hp
    exact hx'.trans hy'.symm

/-- `lem:cellcount`'s constancy on a box: at a valid box cover of a
shaped symmetric pencil (the symmetry binder the lemma's hypothesis,
a symmetric pencil whose entries are polynomial in the coordinates)
the reversal count reads one integer at every point of the box, any
two stated points' splits at the double evaluations reading one
count, the representatives entering as data. -/
theorem cover2_const {o : Nat} (S : split.PPMat) (Ks Kt : Nat)
    (t0 t1 s0 s1 : CPair) (cov : Cover2)
    (h : coverRead2 S o Ks Kt t0 t1 s0 s1 cov)
    (hsh : ppShapeAt S o Ks Kt) (hsym : split.ppSymAt S o)
    (xtn : BPair) (xtc : Pos) (xsn : BPair) (xsc : Pos)
    (ytn : BPair) (ytc : Pos) (ysn : BPair) (ysc : Pos)
    (hx0 : t0 ≤ ⟨xtn, xtc⟩) (hx1 : (⟨xtn, xtc⟩ : CPair) ≤ t1)
    (hxs0 : s0 ≤ ⟨xsn, xsc⟩) (hxs1 : (⟨xsn, xsc⟩ : CPair) ≤ s1)
    (hy0 : t0 ≤ ⟨ytn, ytc⟩) (hy1 : (⟨ytn, ytc⟩ : CPair) ≤ t1)
    (hys0 : s0 ≤ ⟨ysn, ysc⟩) (hys1 : (⟨ysn, ysc⟩ : CPair) ≤ s1)
    (spx spy : Split o)
    (hx : splitRead (evalPC (ppevalPC S xtn xtc Kt) xsn xsc Ks) spx)
    (hy : splitRead (evalPC (ppevalPC S ytn ytc Kt) ysn ysc Ks) spy) :
    revAt spx = revAt spy :=
  cover2_go cov o S Ks Kt t0 t1 s0 s1 h hsh
    (fun tn tc sn sc _ _ _ _ => elim.matOne_symm
      (evalPC_symAt _ o Ks sn sc (pShape_len (pShapeAt_ppevalPC hsh tn tc))
        (pShape_rows (pShapeAt_ppevalPC hsh tn tc))
        (pSymAt_ppevalPC hsym tn tc Kt)))
    xtn xtc xsn xsc ytn ytc ysn ysc
    hx0 hx1 hxs0 hxs1 hy0 hy1 hys0 hys1 spx spy hx hy

/-- The count is a cell function on a box, read once
(`lem:cellcount`'s constancy at the box cover): on a covered box of a
shaped symmetric pencil (the symmetry binder the lemma's hypothesis)
a sampled count at the inner-evaluated pencil holds at every point,
the target's stated split reading the sample's value. -/
theorem cellCount2 {o : Nat} (S : split.PPMat) (Ks Kt n : Nat)
    (t0 t1 s0 s1 : CPair) (cov : Cover2)
    (hc : coverRead2 S o Ks Kt t0 t1 s0 s1 cov)
    (hsh : ppShapeAt S o Ks Kt) (hsym : split.ppSymAt S o)
    (stn : BPair) (stc : Pos) (ssn : BPair) (ssc : Pos)
    (hst0 : t0 ≤ (⟨stn, stc⟩ : CPair)) (hst1 : (⟨stn, stc⟩ : CPair) ≤ t1)
    (hss0 : s0 ≤ (⟨ssn, ssc⟩ : CPair)) (hss1 : (⟨ssn, ssc⟩ : CPair) ≤ s1)
    (sps : inertia.Split o)
    (hs : countAt (ppevalPC S stn stc Kt) Ks ssn ssc n sps)
    (ttn : BPair) (ttc : Pos) (tsn : BPair) (tsc : Pos)
    (htt0 : t0 ≤ (⟨ttn, ttc⟩ : CPair)) (htt1 : (⟨ttn, ttc⟩ : CPair) ≤ t1)
    (hts0 : s0 ≤ (⟨tsn, tsc⟩ : CPair)) (hts1 : (⟨tsn, tsc⟩ : CPair) ≤ s1)
    (spt : inertia.Split o)
    (ht : inertia.splitRead (evalPC (ppevalPC S ttn ttc Kt) tsn tsc Ks) spt) :
    inertia.revAt spt = n :=
  (cover2_const S Ks Kt t0 t1 s0 s1 cov hc hsh hsym ttn ttc tsn tsc stn stc ssn ssc
    htt0 htt1 hts0 hts1 hst0 hst1 hss0 hss1 spt sps ht hs.2.1).trans hs.2.2

end cellcount
