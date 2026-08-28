import MassGap.Certconstruct
/-!
`thm:momentform` — the two-moment form: a probe's moments depend on
it through `y = A ψ` alone (`probeVec`, the matrix against the
ground), the moments the quadratic reads `μ₁ = ⟨y, Ẽ y⟩` and
`μ₂ = ⟨y, Ẽ² y⟩` (`mu1`, `mu2` at `thm:certconstruct`'s form
fold), and the requirement per probe is one cleared inequality
(`reqRead`, the coupling entering through the state alone).  For a
multiplication probe the commutator is the electric member's,
`[H, f] = [E, f]` (`commE` at the diagonal's gaps, the magnetic
member commuting by `prop:algebra`), and the second moment's
operator is `Q₂(f) = [E, f]† [E, f]` (`q2`).  The commutator's action
on a vector reads the diagonal's action of the multiplication's read
joined to the multiplication's action of the diagonal's at the
memberwise swap, the swap the subtraction (`commE_read`, the
diagonal's row against a vector its stated gap at the row's key).
The evaluation displays `μ₂(f) = ω(Q₂(f))` and `μ₁(f) = ω(f†[E, f])`
(`thm:coeffone`'s exact line read at the state) are the check
module's coherence pins at the free end's ground; the multiplication
family's sufficiency — `A ↦ A ψ` linear with the word sector its
image — is `lem:statespace`'s layer with `def:pencil`'s sector.
The pairings below read at the unit gram, the committed loop
windows' own; the fibered gram rides `prop:wg`'s site.  The
commutator's fold truncates at the shorter operand, the
certificate Props' standing shape convention; the probe's order
is the carrier's own.
-/

namespace momentform
open ground elim

/-- The probe's vector: `y = A ψ` at the carrier, the moments' one
datum. -/
def probeVec {n : Nat} (A : SqMat n) (psi : Vec n) : Vec n :=
  appSq A psi

/-- The first moment `μ₁ = ⟨y, Ẽ y⟩`, the level gap's quadratic
read at the probe's vector. -/
def mu1 {n : Nat} (Et : SqMat n) (y : Vec n) : BPair :=
  inertia.quadForm Et.val y.val

/-- The second moment `μ₂ = ⟨y, Ẽ² y⟩` at the square. -/
def mu2 {n : Nat} (Et : SqMat n) (y : Vec n) : BPair :=
  inertia.quadForm (matMul Et.val Et.val) y.val

/-- The requirement's read at a probe: `μ₂ ≥ γ μ₁` at the level
`[gn : gd]`, cleared at the carrier's one order — the coupling
entering through the state alone. -/
def reqRead {n : Nat} (Et : SqMat n) (y : Vec n) (gn gd : Pos) :
    Prop :=
  ¬ (mu2 Et y).scale gd < (mu1 Et y).scale gn

instance {n : Nat} (Et : SqMat n) (y : Vec n) (gn gd : Pos) :
    Decidable (reqRead Et y gn gd) :=
  inferInstanceAs (Decidable (¬ _ < _))

/-- The electric commutator `[E, f]` at the diagonal member: entry
`(dᵢ + dⱼˇ) Fᵢⱼ`, the diagonal's gaps against the multiplication
matrix. -/
def commE (dg : List Nat) (F : Mat) : Mat :=
  List.zipWith (fun di row =>
    List.zipWith (fun dj e =>
      ((BPair.ofNat di + (BPair.ofNat dj).swap) * e).norm) dg row)
    dg F

/-- The second moment's operator `Q₂(f) = [E, f]† [E, f]`, positive
by its shape. -/
def q2 (dg : List Nat) (F : Mat) : Mat :=
  let c := commE dg F
  matMul (transposeM c) c

/-! `thm:coeffone`'s electric commutator at the diagonal: the
commutator's action reads the diagonal's action of the composite
against the composite of the diagonal's, the swap the
subtraction. -/



/-- The diagonal's action is the entrywise product against the
stated gaps. -/
private theorem diagAct (dg : List Nat) (v : List BPair) (n : Nat)
    (hdg : dg.length = n) (hv : v.length = n) :
    poly.oneValue
      (matVec (diagO ground.bpairOps (dg.map BPair.ofNat)) v)
      (List.zipWith (fun dj x => BPair.ofNat dj * x) dg v) := by
  have hml : (dg.map BPair.ofNat).length = n :=
    (ground.length_map _ dg).trans hdg
  have hDl : (diagO ground.bpairOps (dg.map BPair.ofNat)).length = n :=
    (diagO_len ground.bpairOps _).trans hml
  refine poly.oneValue_of_entries _ _ ?_ ?_
  · rw [matVec_length, hDl,
      ground.length_zipWith _ dg v n hdg hv]
  · intro t ht
    rw [matVec_length, hDl] at ht
    rw [show matVec (diagO ground.bpairOps (dg.map BPair.ofNat)) v
        = (diagO ground.bpairOps (dg.map BPair.ofNat)).map
            (fun r => dotN r v) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit _ _ t
        (by rw [hDl]; exact ht),
      ground.getAt_zipWith 0 BPair.unit BPair.unit
        (fun dj x => BPair.ofNat dj * x) dg v t
        (by rw [hdg]; exact ht) (by rw [hv]; exact ht)]
    refine BPair.oneValue_trans
      (elim.diagO_row (dg.map BPair.ofNat) v t (by rw [hml]; exact ht)
        (by rw [hv, hml])) ?_
    rw [ground.getAt_map 0 BPair.unit BPair.ofNat dg t
      (by rw [hdg]; exact ht)]
    exact BPair.oneValue_refl _

/-- One commutator row against a vector: the row's own gap times the
row's fold, joined to the fold against the gap-weighted vector at the
memberwise swap. -/
private theorem rowCommE (c : BPair) : ∀ (dg : List Nat) (r v : List BPair),
    dg.length = r.length → r.length = v.length →
    (dotP (List.zipWith (fun dj e =>
        ((c + (BPair.ofNat dj).swap) * e).norm) dg r) v).oneValue
      (c * dotP r v
        + (dotP r (List.zipWith (fun dj x => BPair.ofNat dj * x) dg v)).swap)
  | [], [], [], _, _ =>
    BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_unit c) (BPair.oneValue_refl BPair.unit))
        (BPair.add_unit BPair.unit))
  | [], [], _ :: _, _, hr => Nat.noConfusion hr
  | [], _ :: _, _, hdg, _ => Nat.noConfusion hdg
  | _ :: _, [], _, hdg, _ => Nat.noConfusion hdg
  | _ :: _, _ :: _, [], _, hr => Nat.noConfusion hr
  | d :: dg, e :: r, x :: v, hdg, hr => by
    show (((c + (BPair.ofNat d).swap) * e).norm * x
        + dotP (List.zipWith (fun dj e' =>
            ((c + (BPair.ofNat dj).swap) * e').norm) dg r) v).oneValue
      (c * (e * x + dotP r v)
        + (e * (BPair.ofNat d * x)
            + dotP r (List.zipWith
                (fun dj y => BPair.ofNat dj * y) dg v)).swap)
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr_left (BPair.norm_oneValue _))
        (rowCommE c dg r v (Nat.succ.inj hdg) (Nat.succ.inj hr))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.right_distrib c ((BPair.ofNat d).swap) e,
      BPair.right_distrib (c * e) ((BPair.ofNat d).swap * e) x,
      BPair.mul_assoc c e x,
      BPair.swap_mul (BPair.ofNat d) e,
      BPair.swap_mul (BPair.ofNat d * e) x,
      BPair.mul_assoc (BPair.ofNat d) e x,
      BPair.left_distrib c (e * x) (dotP r v),
      BPair.mul_left_comm e (BPair.ofNat d) x,
      ← BPair.swap_add (BPair.ofNat d * (e * x))
        (dotP r (List.zipWith (fun dj y => BPair.ofNat dj * y) dg v)),
      BPair.add_add_comm (c * (e * x))
        ((BPair.ofNat d * (e * x)).swap) (c * dotP r v)
        ((dotP r (List.zipWith
          (fun dj y => BPair.ofNat dj * y) dg v)).swap)]

/-- `thm:coeffone`'s electric commutator at the diagonal: the
commutator's action on a vector is the diagonal's action of the
multiplication's read against the multiplication's action of the
diagonal's, the swap the subtraction. -/
theorem commE_read (dg : List Nat) (C : Mat) (v : List BPair)
    (n : Nat) (hdg : dg.length = n) (hCr : rowsLen n C)
    (hCl : C.length = n) (hv : v.length = n) :
    poly.oneValue (matVec (commE dg C) v)
      (poly.add
        (matVec (diagO ground.bpairOps (dg.map BPair.ofNat))
          (matVec C v))
        ((matVec C (matVec (diagO ground.bpairOps
            (dg.map BPair.ofNat)) v)).map BPair.swap)) := by
  have hml : (dg.map BPair.ofNat).length = n :=
    (ground.length_map _ dg).trans hdg
  have hDl : (diagO ground.bpairOps (dg.map BPair.ofNat)).length = n :=
    (diagO_len ground.bpairOps _).trans hml
  have hEl : (commE dg C).length = n :=
    ground.length_zipWith _ dg C n hdg hCl
  have hAl : (matVec (diagO ground.bpairOps (dg.map BPair.ofNat))
      (matVec C v)).length = n := (matVec_length _ _).trans hDl
  have hBl : ((matVec C (matVec (diagO ground.bpairOps
      (dg.map BPair.ofNat)) v)).map BPair.swap).length = n :=
    (ground.length_map _ _).trans ((matVec_length _ _).trans hCl)
  refine poly.oneValue_of_entries _ _ ?_ ?_
  · rw [matVec_length, hEl, ← vecAdd_eq_polyAdd _ _ (hAl.trans hBl.symm),
      length_vecAdd _ _ n hAl hBl]
  · intro t ht
    rw [matVec_length, hEl] at ht
    have hCt : (ground.getAt ([] : List BPair) C t).length = n :=
      rowsLen_getAt C t hCr (by rw [hCl]; exact ht)
    have hrow := rowCommE (BPair.ofNat (ground.getAt 0 dg t)) dg
      (ground.getAt ([] : List BPair) C t) v (by rw [hdg, hCt])
      (by rw [hCt, hv])
    have hDv := diagAct dg v n hdg hv
    rw [show matVec (commE dg C) v
        = (commE dg C).map (fun r => dotN r v) from rfl,
      ground.getAt_map ([] : List BPair) BPair.unit _ (commE dg C) t
        (by rw [hEl]; exact ht),
      show commE dg C = List.zipWith (fun di row =>
          List.zipWith (fun dj e =>
            ((BPair.ofNat di + (BPair.ofNat dj).swap) * e).norm) dg row)
          dg C from rfl,
      ground.getAt_zipWith 0 ([] : List BPair) ([] : List BPair) _ dg C t
        (by rw [hdg]; exact ht) (by rw [hCl]; exact ht)]
    refine BPair.oneValue_trans (dotN_read _ v)
      (BPair.oneValue_trans hrow ?_)
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (poly.getAt_add _ _ t) ?_)
    refine BPair.add_congr ?_ ?_
    · rw [show matVec (diagO ground.bpairOps (dg.map BPair.ofNat))
          (matVec C v)
          = (diagO ground.bpairOps (dg.map BPair.ofNat)).map
              (fun r => dotN r (matVec C v)) from rfl,
        ground.getAt_map ([] : List BPair) BPair.unit _ _ t
          (by rw [hDl]; exact ht)]
      refine BPair.oneValue_trans
        (elim.diagO_row (dg.map BPair.ofNat) (matVec C v) t
          (by rw [hml]; exact ht)
          (by rw [matVec_length, hCl, hml])) ?_
      rw [ground.getAt_map 0 BPair.unit BPair.ofNat dg t
          (by rw [hdg]; exact ht),
        show matVec C v = C.map (fun r => dotN r v) from rfl,
        ground.getAt_map ([] : List BPair) BPair.unit _ C t
          (by rw [hCl]; exact ht)]
      exact BPair.mul_congr (BPair.oneValue_refl _) (dotN_read _ v)
    · rw [ground.getAt_map BPair.unit BPair.unit BPair.swap _ t
          (by rw [matVec_length, hCl]; exact ht),
        show matVec C (matVec (diagO ground.bpairOps
              (dg.map BPair.ofNat)) v)
            = C.map (fun r => dotN r (matVec
                (diagO ground.bpairOps (dg.map BPair.ofNat)) v)) from rfl,
        ground.getAt_map ([] : List BPair) BPair.unit _ C t
          (by rw [hCl]; exact ht)]
      exact ground.swap_congr
        (BPair.oneValue_trans (dotN_congrR _ _ _ hDv) (dotN_read _ _))

end momentform
