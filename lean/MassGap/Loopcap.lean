import MassGap.Coeff
import MassGap.Fpcap
import MassGap.Pairpencil
/-!
`lem:loopcap` — the loop window's form cap at the label index.  At a
loop window the magnetic matrix is the fusion form's own at the
self-dual `θ` over the unit-headed label list (`pairpencil.loopMag`,
the two spellings one datum), so the shifted term reads the
character's two-sided cap: unit width below and `r (r + 2)` above.
The upper side is `lem:fpcap`'s cap at `θ`'s instance
(`shiftUpper`), the interface's window reads its hypotheses — the
tex's own bare derivation is the cut tier below, the coefficient
carrier's; the lower side is the Gram
route (`shiftLower`) —
the squared fundamental's composition read `Σ_c N^c_{f x} N^c_{f y}
= N^x_{θ y} + δ_{xy}` at the window (`fpcap.compRead`) turns the
shifted form's double fold into the fundamental's window block
against the vector, the block's own squares summed over the
intermediate labels, at or above the sum's unit by the pairing's
one-sided read (`elim.dotN_self_side`).  The window's labels enter
pairwise distinct at the index's equality (`hdist`, `fpcap`'s
`distinctAt` — the decided fold whose pointwise decode converts the
label equality to the positional one), which is where the
composition read's `δ` becomes the identity the shifted term's
first summand carries.

The loop-cut tier reads the coefficient carrier's pairing
(`con:coeff`).  `cutSq` is the display: at joined slot coordinates
whose two self-pairings read the count against the two grams — the
evaluation identity's contractions — the squared Cauchy–Schwarz
over the joined list (`coeff.dotP_sq_le`) prices the pairing's
square at or below the count's square against the grams' product.
`cutCap` reads the order back at the image: the cut datum's own
pairing reads the image's gram, and the count cancels off the
comparison (`ground.leB_unscale`) to leave the image's gram at or
below the squared count against the vector's, the vacant arm
closing at the pairing's definiteness (`elim.dotP_self_null`,
where the absent count forces the pairing to the sum's unit).
`cutForm` reads the term two-sided: one further squared
Cauchy–Schwarz at a window vector against its image, the squared
comparison reading back at the trichotomy (`ground.leB_of_sq_le`),
so the form and its memberwise swap each sit at or below the count
against the gram.  `prop:wg`'s presentation Gram is the recorded
site; `thm:truncation`'s member cap is the consumer.

The member reads: the block's index `κ_λ`
(`indexAt`) with the closure's joined index (`joinedIndex`), the
adjoint tie's pair `t_λ` (`tieAt`) with `t_L` the least over the
closure (`tieLeast`), the second member's pair `c^z_λ` at the block's
dimension (`secondMember`), the residual cap `c^⊥_λ` (`residualCap`)
and the adjoint's `c^⊥_θ` (`adjResidualCap`), the coordinates' tie
`c_{β,λ}` (`coordTie`), the off-class index `κ'_λ`
(`offClassIndex`), the dispersion's pair `c_ϱ` (`dispersion`, its
term per label `dispersionAt`), the closure's least dimension `d₋`
(`leastDim`) and the second-order pair `s_L` (`secondOrder`), every
read a pair at the member's tables and the residue with the
Casimirs' cleared second member withdrawn.
-/

namespace loopcap
open ground fusion elim

/-- The shifted term's upper side at a loop window: the `θ`-cap's
own instance, `r (r+2)` above at the interface's dimension
(`lem:loopcap`; `lem:fpcap`'s cap at the self-dual `θ`). -/
theorem shiftUpper {L : Type} (F : fusion.Data L) (ls : List L)
    (hsym : fpcap.symAt F F.theta (F.unit :: ls))
    (hrow : fpcap.rowCap F F.theta (F.unit :: ls))
    (hdim : fpcap.dimPos F (F.unit :: ls))
    (u : List ground.BPair) (hu : u.length = ls.length + 1) :
    ¬ (ground.BPair.ofNat (F.dim F.theta) * elim.dotN u u
        < inertia.quadForm (pairpencil.loopMag F ls) u) :=
  fpcap.capUpper F F.theta (F.unit :: ls) hsym hrow hdim u hu

/-- The composition's Gram collection: a double index fold whose
count is the further fold of a family's products collects to the
squares of that family's weighted folds — the tex's
`Σ_c (Σ_i N^c_{f x_i} u_i)²` at the cleared exchange. -/
private theorem gramFold (n m : Nat) (A : Nat → Nat → Nat)
    (uu : Nat → BPair) :
    (bsum (fun i => bsum (fun j =>
        BPair.ofNat (ground.famFold Nat.add 0
            (fun c => A c i * A c j) (List.range m))
          * (uu i * uu j)) (List.range n)) (List.range n)).oneValue
      (bsum (fun c =>
        bsum (fun i => BPair.ofNat (A c i) * uu i) (List.range n)
          * bsum (fun i => BPair.ofNat (A c i) * uu i)
            (List.range n)) (List.range m)) := by
  have hsplit : (bsum (fun i => bsum (fun j =>
        BPair.ofNat (ground.famFold Nat.add 0
            (fun c => A c i * A c j) (List.range m))
          * (uu i * uu j)) (List.range n)) (List.range n)).oneValue
      (bsum (fun i => bsum (fun j => bsum (fun c =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range m)) (List.range n)) (List.range n)) :=
    foldB_congr_members _ _ (List.range n) (fun i _ =>
      foldB_congr_members _ _ (List.range n) (fun j _ =>
        BPair.oneValue_symm (bsum_scalar (fun c => A c i * A c j)
          (uu i * uu j) (List.range m))))
  have hswapIn : (bsum (fun i => bsum (fun j => bsum (fun c =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range m)) (List.range n)) (List.range n)).oneValue
      (bsum (fun i => bsum (fun c => bsum (fun j =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range n)) (List.range m)) (List.range n)) :=
    foldB_congr_members _ _ (List.range n) (fun i _ =>
      bsum_swap (fun j c => BPair.ofNat (A c i * A c j)
        * (uu i * uu j)) (List.range n) (List.range m))
  have hswapOut := bsum_swap (fun i c => bsum (fun j =>
      BPair.ofNat (A c i * A c j) * (uu i * uu j)) (List.range n))
    (List.range n) (List.range m)
  have hcollect : (bsum (fun c => bsum (fun i => bsum (fun j =>
        BPair.ofNat (A c i * A c j) * (uu i * uu j))
        (List.range n)) (List.range n)) (List.range m)).oneValue
      (bsum (fun c =>
        bsum (fun i => BPair.ofNat (A c i) * uu i) (List.range n)
          * bsum (fun i => BPair.ofNat (A c i) * uu i)
            (List.range n)) (List.range m)) := by
    refine foldB_congr_members _ _ (List.range m) (fun c _ => ?_)
    refine BPair.oneValue_trans
      (foldB_congr_members _ (fun i => (BPair.ofNat (A c i) * uu i)
        * bsum (fun j => BPair.ofNat (A c j) * uu j)
          (List.range n)) (List.range n) (fun i _ => ?_)) ?_
    · refine BPair.oneValue_trans
        (foldB_congr_members _ (fun j => (BPair.ofNat (A c i) * uu i)
          * (BPair.ofNat (A c j) * uu j)) (List.range n)
          (fun j _ => BPair.oneValue_symm
            (mulPairNat (A c i) (A c j) (uu i) (uu j)))) ?_
      exact foldB_mul_left
        (BPair.ofNat (A c i) * uu i)
        (fun j => BPair.ofNat (A c j) * uu j) (List.range n)
    · refine BPair.oneValue_trans
        (foldB_congr_members _ (fun i =>
          bsum (fun j => BPair.ofNat (A c j) * uu j) (List.range n)
            * (BPair.ofNat (A c i) * uu i)) (List.range n)
          (fun i _ => BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
      exact foldB_mul_left
        (bsum (fun j => BPair.ofNat (A c j) * uu j) (List.range n))
        (fun i => BPair.ofNat (A c i) * uu i) (List.range n)
  exact BPair.oneValue_trans hsplit (BPair.oneValue_trans hswapIn
    (BPair.oneValue_trans hswapOut hcollect))

/-- The lower side at the abstract families: a form reading the
window's squares against a double fold whose count is the
composition's own sits at or above the sum's unit, the block's
squares the carrier. -/
private theorem lowerAt (n m : Nat) (NN dl A : Nat → Nat → Nat)
    (uu : Nat → BPair) (V : List BPair) (hV : V.length = m)
    (hdl : ∀ i j, i < n → j < n →
      dl i j = if i = j then 1 else 0)
    (hC : ∀ i j, i < n → j < n →
      ground.famFold Nat.add 0 (fun c => A c i * A c j)
          (List.range m)
        = NN i j + dl i j)
    (hVc : ∀ c, c < m → (ground.getAt BPair.unit V c).oneValue
      (bsum (fun i => BPair.ofNat (A c i) * uu i) (List.range n)))
    (X : BPair)
    (hX : X.oneValue (bsum (fun i => uu i * uu i) (List.range n)
      + bsum (fun i => bsum (fun j => BPair.ofNat (NN i j)
        * (uu i * uu j)) (List.range n)) (List.range n))) :
    ¬ (X < BPair.unit) := by
  intro hlt
  refine elim.dotN_self_side V
    (BPair.lt_congr ?_ (BPair.oneValue_refl BPair.unit) hlt)
  refine BPair.oneValue_trans hX (BPair.oneValue_trans
    (sumFold n dl NN (fun i j => ground.famFold Nat.add 0
      (fun c => A c i * A c j) (List.range m)) uu hdl hC) ?_)
  refine BPair.oneValue_trans (gramFold n m A uu) ?_
  exact BPair.oneValue_trans
    (foldB_congr_members _ _ (List.range m) (fun c hc =>
      BPair.mul_congr (BPair.oneValue_symm (hVc c (ground.ltOfMem hc)))
        (BPair.oneValue_symm (hVc c (ground.ltOfMem hc)))))
    (BPair.oneValue_symm (selfFold V m hV))

/-! The fundamental's window block: the composition read's
intermediate labels the rows, the window the columns, entry
`(c, x) = N^c_{f x}`. -/

/-- The fundamental's window block at a composition's intermediate
list. -/
private def crossMat {L : Type} (F : fusion.Data L) (fl : L)
    (ls cs : List L) : Mat :=
  cs.map (fun c => (F.unit :: ls).map (fun x =>
    BPair.ofNat (F.count fl x c)))

/-- The block against the window's vector: at a stated intermediate
key the entry is the fundamental's weighted fold over the
window. -/
private theorem crossVec {L : Type} (F : fusion.Data L) (fl : L)
    (ls cs : List L) (u : List BPair)
    (hu : u.length = ls.length + 1) (c : Nat) (hc : c < cs.length) :
    (ground.getAt BPair.unit
        (elim.matVec (crossMat F fl ls cs) u) c).oneValue
      (bsum (fun i => BPair.ofNat (F.count fl
          (ground.getAt F.unit (F.unit :: ls) i)
          (ground.getAt F.unit cs c)) * ground.getAt BPair.unit u i)
        (List.range (ls.length + 1))) := by
  have hrow : ∀ y : L, ((F.unit :: ls).map (fun x =>
      BPair.ofNat (F.count fl x y))).length = ls.length + 1 :=
    fun y => ground.length_map _ (F.unit :: ls)
  have hmap : elim.matVec (crossMat F fl ls cs) u
      = cs.map (fun y => elim.dotN ((F.unit :: ls).map
        (fun x => BPair.ofNat (F.count fl x y))) u) :=
    ground.map_map _ _ cs
  rw [hmap, ground.getAt_map F.unit BPair.unit _ cs c hc]
  refine BPair.oneValue_trans (elim.dotN_read _ u) ?_
  rw [dotP_fold (ls.length + 1) _ u (hrow _) hu]
  refine foldB_congr_members _ _ (List.range (ls.length + 1))
    (fun i hi => ?_)
  rw [ground.getAt_map F.unit BPair.unit
    (fun x => BPair.ofNat
      (F.count fl x (ground.getAt F.unit cs c)))
    (F.unit :: ls) i (ground.ltOfMem hi)]
  exact BPair.oneValue_refl _

/-- The shifted term's lower side at a loop window: the form with
the gram at or above the sum's unit — `χ_θ + 1` the squared
fundamental's Gram at the composition read, the window's labels
pairwise distinct at the index's equality (`lem:loopcap`). -/
theorem shiftLower {L : Type} (F : fusion.Data L) (fl : L)
    (ls cs : List L)
    (hcomp : fpcap.compRead F fl (F.unit :: ls) cs)
    (hdist : fpcap.distinctAt F (F.unit :: ls))
    (u : List ground.BPair) (hu : u.length = ls.length + 1) :
    ¬ (elim.dotN u u
          + inertia.quadForm (pairpencil.loopMag F ls) u
        < ground.BPair.unit) := by
  have hV : (elim.matVec (crossMat F fl ls cs) u).length
      = cs.length :=
    (ground.length_map _ (crossMat F fl ls cs)).trans
      (ground.length_map _ cs)
  have hq : (inertia.quadForm (pairpencil.loopMag F ls)
        u).oneValue
      (bsum (fun i => bsum (fun j =>
        BPair.ofNat (F.count F.theta
            (ground.getAt F.unit (F.unit :: ls) j)
            (ground.getAt F.unit (F.unit :: ls) i))
          * (ground.getAt BPair.unit u i
            * ground.getAt BPair.unit u j))
        (List.range (ls.length + 1)))
        (List.range (ls.length + 1))) := by
    exact fpcap.quadFold F F.theta (F.unit :: ls) u hu
  refine lowerAt (ls.length + 1) cs.length
    (fun i j => F.count F.theta
      (ground.getAt F.unit (F.unit :: ls) j)
      (ground.getAt F.unit (F.unit :: ls) i))
    (fun i j => if F.eqL (ground.getAt F.unit (F.unit :: ls) i)
      (ground.getAt F.unit (F.unit :: ls) j) then 1 else 0)
    (fun c i => F.count fl (ground.getAt F.unit (F.unit :: ls) i)
      (ground.getAt F.unit cs c))
    (fun i => ground.getAt BPair.unit u i)
    (elim.matVec (crossMat F fl ls cs) u) hV ?_ ?_
    (fun c hc => crossVec F fl ls cs u hu c hc) _
    (BPair.add_congr (selfFold u (ls.length + 1) hu) hq)
  · intro i j hi hj
    by_cases hij : i = j
    · rw [if_pos ((fpcap.distinctAt_read hdist i j hi hj).mpr hij), if_pos hij]
    · rw [if_neg (fun he => hij ((fpcap.distinctAt_read hdist i j hi hj).mp he)),
        if_neg hij]
  · intro i j hi hj
    have h0 := fpcap.compRead_read hcomp i j hi hj
    rw [← ground.famFold_getAt Nat.add 0 _ F.unit cs cs.length rfl] at h0
    exact h0

/-! The loop-cut tier: the joined slot coordinates' pairing at the
squared Cauchy--Schwarz (`con:coeff`), the count cancelled off the
comparison, and the window vector's form read two-sided at the
count against the gram. -/

/-- The loop-cut display (`lem:loopcap`): at joined slot coordinates
whose two self-pairings read the count against the two grams, the
evaluation identity's contractions, the pairing's square sits at or
below the count's square against the grams' product, the squared
Cauchy--Schwarz at the joined list (`con:coeff`). -/
theorem cutSq (ya xb : List BPair) (hlen : ya.length = xb.length)
    (D : Nat) (Gy Gx : BPair)
    (hy : (elim.dotP ya ya).oneValue (BPair.ofNat D * Gy))
    (hx : (elim.dotP xb xb).oneValue (BPair.ofNat D * Gx)) :
    ¬ (BPair.ofNat D * Gy * (BPair.ofNat D * Gx)
        < elim.dotP ya xb * elim.dotP ya xb) :=
  fun hlt => coeff.dotP_sq_le ya xb hlen
    (BPair.lt_congr
      (BPair.mul_congr (BPair.oneValue_symm hy)
        (BPair.oneValue_symm hx))
      (BPair.oneValue_refl _) hlt)

/-- The order's read back at the image (`lem:loopcap`): at the cut
datum whose pairing reads the image's own gram, the image's gram
sits at or below the squared count against the vector's, the
comparison at the occupied factor with the vacant arm at the
pairing's definiteness. -/
theorem cutCap (ya xb : List BPair) (hlen : ya.length = xb.length)
    (D : Nat) (N Gx : BPair)
    (hP : (elim.dotP ya xb).oneValue N)
    (hy : (elim.dotP ya ya).oneValue (BPair.ofNat D * N))
    (hx : (elim.dotP xb xb).oneValue (BPair.ofNat D * Gx)) :
    ¬ (BPair.ofNat (D * D) * Gx < N) := by
  match D with
  | 0 =>
    have hself : (elim.dotP ya ya).oneValue BPair.unit :=
      BPair.oneValue_trans hy (BPair.unit_mul N)
    have hcross : (elim.dotP ya xb).oneValue BPair.unit :=
      elim.dotP_null_or ya xb hlen (fun i _ => Or.inl
        (poly.getAt_unitTail (elim.dotP_self_null ya hself) i))
    have hNu : N.oneValue BPair.unit :=
      BPair.oneValue_trans (BPair.oneValue_symm hP) hcross
    intro hlt
    exact leB_not_lt (leB_refl BPair.unit)
      (BPair.lt_congr (BPair.unit_mul Gx) hNu hlt)
  | D' + 1 =>
    have hD1 : BPair.unit < BPair.ofNat (D' + 1) := unitLtOfNat D'
    have hsq := cutSq ya xb hlen (D' + 1) N Gx hy hx
    have hNN : N * N
        ≤ BPair.ofNat ((D' + 1) * (D' + 1)) * Gx * N := by
      refine leB_congr (BPair.mul_congr hP hP) ?_
        (leB_of_not_lt hsq)
      rw [BPair.mul_mul_mul_comm (BPair.ofNat (D' + 1)) N
          (BPair.ofNat (D' + 1)) Gx,
        BPair.mul_comm N Gx, ← BPair.mul_assoc]
      exact BPair.mul_congr_left (BPair.mul_congr_left
        (BPair.oneValue_symm (BPair.ofNat_mul (D' + 1) (D' + 1))))
    have hN1 : BPair.unit ≤ N :=
      unitLeUnscale hD1 (leB_congr_right hy
        (unitLeOfSide (elim.dotP_self_side ya)))
    if hc : BPair.unit < N then
      exact leB_not_lt (leB_unscale hc hNN)
    else
      have hNu : BPair.unit.oneValue N :=
        leB_antisymm hN1 (leB_of_not_lt hc)
      have hGx1 : BPair.unit ≤ Gx :=
        unitLeUnscale hD1 (leB_congr_right hx
          (unitLeOfSide (elim.dotP_self_side xb)))
      exact leB_not_lt (leB_congr_left hNu
        (leB_unit_mul ((D' + 1) * (D' + 1)) hGx1))

/-- The two-sided form read (`lem:loopcap`): one further squared
Cauchy--Schwarz at a window vector against its image, the squared
comparison reading back at the trichotomy, the form and its
memberwise swap each at or below the count against the gram. -/
theorem cutForm (xc mxc : List BPair) (hlen : xc.length = mxc.length)
    (D : Nat) (Gx Q : BPair)
    (hGc : (elim.dotP xc xc).oneValue Gx)
    (hQ : Q.oneValue (elim.dotP xc mxc))
    (hcap : ¬ (BPair.ofNat (D * D) * Gx < elim.dotP mxc mxc)) :
    Q ≤ BPair.ofNat D * Gx ∧ Q.swap ≤ BPair.ofNat D * Gx := by
  have hside : BPair.unit ≤ Gx :=
    leB_congr_right hGc (unitLeOfSide (elim.dotP_self_side xc))
  have hb : BPair.unit ≤ BPair.ofNat D * Gx := leB_unit_mul D hside
  have h1 : ¬ (elim.dotP xc xc * elim.dotP mxc mxc < Q * Q) :=
    fun hlt => coeff.dotP_sq_le xc mxc hlen
      (BPair.lt_congr (BPair.oneValue_refl _)
        (BPair.mul_congr hQ hQ) hlt)
  have h3 : Gx * elim.dotP mxc mxc
      ≤ Gx * (BPair.ofNat (D * D) * Gx) :=
    leB_mulR hside (leB_of_not_lt hcap)
  have h4 : (Gx * (BPair.ofNat (D * D) * Gx)).oneValue
      (BPair.ofNat D * Gx * (BPair.ofNat D * Gx)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl Gx)
        (BPair.mul_congr_left (BPair.ofNat_mul D D))) ?_
    rw [BPair.mul_left_comm Gx (BPair.ofNat D * BPair.ofNat D) Gx,
      BPair.mul_mul_mul_comm (BPair.ofNat D) Gx (BPair.ofNat D) Gx]
    exact BPair.oneValue_refl _
  have hsq : ¬ (BPair.ofNat D * Gx * (BPair.ofNat D * Gx) < Q * Q) :=
    leB_not_lt (leB_congr_right h4
      (leB_trans (leB_congr_right (BPair.mul_congr_left hGc)
        (leB_of_not_lt h1)) h3))
  refine ⟨leB_of_sq_le hb hsq, leB_of_sq_le hb ?_⟩
  rw [BPair.swap_sq]
  exact hsq


/-- The coefficient list of a family against a vector, each row's
pairing. -/
private def coefs (T : Mat) (w : List BPair) : List BPair :=
  T.map (fun r => dotP r w)

/-- The scaled coefficient list: the moved vector's coefficients at
a list perpendicular to the mover read the pair's multiples. -/
private theorem coefs_scaled (n : Nat) (L : Mat) (x w : List BPair)
    (κ a : BPair) (hL : rowsLen n L) (hw : w.length = n) (hx : x.length = n)
    (hxL : ∀ i, i < L.length →
      (dotP (getAt [] L i) x).oneValue BPair.unit) :
    BPair.oneValue
      (dotP (coefs L (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap)))
        (coefs L (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap))))
      (κ * (κ * dotP (coefs L w) (coefs L w))) := by
  have hrow : ∀ j, j < L.length →
      BPair.oneValue (getAt BPair.unit
        (coefs L (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap))) j)
        (getAt BPair.unit (vecScale κ (coefs L w)) j) := by
    intro j hj
    have hr : (getAt [] L j).length = n := rowsLen_getAt L j hL hj
    show BPair.oneValue (getAt BPair.unit
      (L.map (fun r => dotP r
        (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap)))) j)
      (getAt BPair.unit (vecScale κ (coefs L w)) j)
    rw [ground.getAt_map ([] : List BPair) BPair.unit _ L j hj]
    show (dotP (getAt [] L j)
      (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap))).oneValue
      (getAt BPair.unit (vecScale κ (coefs L w)) j)
    have hv : getAt BPair.unit (vecScale κ (coefs L w)) j
        = κ * dotP (getAt [] L j) w := by
      rw [getAt_vecScale κ (coefs L w) j
          (by show j < (L.map _).length; rw [ground.length_map]; exact hj)]
      show κ * getAt BPair.unit (L.map (fun r => dotP r w)) j
        = κ * dotP (getAt [] L j) w
      rw [ground.getAt_map ([] : List BPair) BPair.unit _ L j hj]
    rw [hv]
    refine BPair.oneValue_trans (dotP_vecAdd (getAt [] L j) _ _
      (by rw [length_vecScale, hw, hr])
      (by rw [ground.length_map, length_vecScale, hx, hr])) ?_
    rw [dotP_swapMap]
    refine BPair.oneValue_trans (BPair.add_congr
      (dotP_vecScale_right (getAt [] L j) w κ)
      (swap_congr (BPair.oneValue_trans
        (dotP_vecScale_right (getAt [] L j) x a)
        (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl a) (hxL j hj))
          (BPair.mul_unit a))))) ?_
    exact BPair.add_unit _
  have hlen : (coefs L (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap))).length
      = (vecScale κ (coefs L w)).length := by
    show (L.map _).length = (vecScale κ (L.map _)).length
    rw [length_vecScale, ground.length_map, ground.length_map]
  have hlenL : (vecScale κ (coefs L w)).length = L.length := by
    show (vecScale κ (L.map _)).length = L.length
    rw [length_vecScale, ground.length_map]
  have h1 : BPair.oneValue
      (dotP (coefs L (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap)))
        (coefs L (vecAdd (vecScale κ w) ((vecScale a x).map BPair.swap))))
      (dotP (vecScale κ (coefs L w)) (vecScale κ (coefs L w))) := by
    refine BPair.oneValue_trans (dotP_congr_left _ _ _ (fun j hj => hrow j (by
      rw [hlen, hlenL] at hj; exact hj))) ?_
    rw [dotP_comm (vecScale κ (coefs L w)) _]
    refine BPair.oneValue_trans (dotP_congr_left _ _ _ (fun j hj => hrow j (by
      rw [hlenL] at hj; exact hj))) ?_
    rw [dotP_comm]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans h1 ?_
  refine BPair.oneValue_trans (dotP_scaleL κ (coefs L w) (vecScale κ (coefs L w))) ?_
  exact BPair.mul_congr (BPair.oneValue_refl κ)
    (dotP_vecScale_right (coefs L w) (coefs L w) κ)

/-- `lem:loopcap`'s gradient deficit as Bessel's read at an
orthogonal list: at a list `T` of vectors pairwise perpendicular
with every self-pairing the index `κ`, and a vector `e` perpendicular
to the list at self-pairing `d`, every vector `w` reads its
coefficients' square fold against the count and its `e`-pairing's
square against the index at or below its self-pairing against the
index and the count — the projection fold's positive gap; at the
adjoint block `T` is the generators' transposes flattened, `e` the
identity, `w` the coefficient less the identity, and the reads are
the gradient square, the deficit's square and twice the deficit. -/
theorem gradient_deficit (n : Nat) :
    ∀ (T : Mat) (w e : List BPair) (κ d : BPair),
    rowsLen n T → w.length = n → e.length = n → perpAll T →
    (∀ i, i < T.length →
      (dotP (getAt [] T i) (getAt [] T i)).oneValue κ) →
    BPair.unit < κ →
    (∀ i, i < T.length → (dotP (getAt [] T i) e).oneValue BPair.unit) →
    (dotP e e).oneValue d → BPair.unit < d →
    dotP (coefs T w) (coefs T w) * d + dotP e w * dotP e w * κ
      ≤ dotP w w * κ * d
  | [], w, e, κ, d, _, hw, he, _, _, hκ, _, hd, hdp => by
    have hcs : ¬ (dotP e e * dotP w w < dotP e w * dotP e w) :=
      coeff.dotP_sq_le e w (he.trans hw.symm)
    have h1 : dotP e w * dotP e w ≤ d * dotP w w :=
      leB_congr_right (BPair.mul_congr_left hd) (leB_of_not_lt hcs)
    have hb : BPair.unit ≤ d * dotP w w :=
      leB_congr_left (BPair.mul_unit d)
        (leB_mulR (Or.inr hdp) (unitLeOfSide (dotP_self_side w)))
    have h2 : dotP e w * dotP e w * κ ≤ d * dotP w w * κ :=
      leB_mul_mono (Or.inr hκ) hb h1 (leB_refl κ)
    have h3 : d * dotP w w * κ = dotP w w * κ * d := by
      rw [BPair.mul_comm d, BPair.mul_assoc, BPair.mul_comm d κ,
        ← BPair.mul_assoc]
    rw [h3] at h2
    have hL : BPair.oneValue
        (dotP (coefs [] w) (coefs [] w) * d + dotP e w * dotP e w * κ)
        (dotP e w * dotP e w * κ) := by
      show (BPair.unit * d + dotP e w * dotP e w * κ).oneValue _
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.unit_mul d) (BPair.oneValue_refl _))
        (BPair.unit_add _)
    exact leB_congr_left (BPair.oneValue_symm hL) h2
  | x :: L, w, e, κ, d, hT, hw, he, hperp, hself, hκ, heT, hd, hdp => by
    have hx : x.length = n := hT.1
    have hL : rowsLen n L := hT.2
    have hxx : (dotP x x).oneValue κ := hself 0 (Nat.succ_pos _)
    have hxe : (dotP x e).oneValue BPair.unit := heT 0 (Nat.succ_pos _)
    have hperpL : perpAll L := perpAll_tail x L hperp
    have hselfL : ∀ i, i < L.length →
        (dotP (getAt [] L i) (getAt [] L i)).oneValue κ :=
      fun i hi => hself (i + 1) (Nat.succ_lt_succ hi)
    have heTL : ∀ i, i < L.length →
        (dotP (getAt [] L i) e).oneValue BPair.unit :=
      fun i hi => heT (i + 1) (Nat.succ_lt_succ hi)
    have hxL : ∀ i, i < L.length →
        (dotP (getAt [] L i) x).oneValue BPair.unit :=
      fun i hi => hperp (i + 1) (Nat.succ_lt_succ hi) 0 (Nat.succ_pos _)
        (fun h => Nat.noConfusion h)
    have hw'l : (vecAdd (vecScale κ w)
        ((vecScale (dotP x w) x).map BPair.swap)).length = n :=
      length_vecAdd _ _ n (by rw [length_vecScale, hw])
        (by rw [ground.length_map, length_vecScale, hx])
    have pairW' : ∀ r : List BPair, r.length = n →
        BPair.oneValue (dotP r (vecAdd (vecScale κ w)
            ((vecScale (dotP x w) x).map BPair.swap)))
          (κ * dotP r w + (dotP x w * dotP r x).swap) := by
      intro r hr
      refine BPair.oneValue_trans (dotP_vecAdd r _ _
        (by rw [length_vecScale, hw, hr])
        (by rw [ground.length_map, length_vecScale, hx, hr])) ?_
      rw [dotP_swapMap]
      exact BPair.add_congr (dotP_vecScale_right r w κ)
        (swap_congr (dotP_vecScale_right r x (dotP x w)))
    have hxw' : BPair.oneValue (dotP x (vecAdd (vecScale κ w)
        ((vecScale (dotP x w) x).map BPair.swap))) BPair.unit := by
      refine BPair.oneValue_trans (pairW' x hx) ?_
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
        (swap_congr (BPair.mul_congr (BPair.oneValue_refl (dotP x w)) hxx))) ?_
      rw [BPair.mul_comm (dotP x w) κ]
      exact BPair.add_swap_null (κ * dotP x w)
    have hew' : BPair.oneValue (dotP e (vecAdd (vecScale κ w)
        ((vecScale (dotP x w) x).map BPair.swap))) (κ * dotP e w) := by
      refine BPair.oneValue_trans (pairW' e he) ?_
      rw [dotP_comm e x]
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
        (swap_congr (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hxe)
          (BPair.mul_unit _)))) ?_
      exact BPair.add_unit _
    have hww' : BPair.oneValue
        (dotP (vecAdd (vecScale κ w) ((vecScale (dotP x w) x).map BPair.swap))
          (vecAdd (vecScale κ w) ((vecScale (dotP x w) x).map BPair.swap)))
        (κ * (κ * dotP w w + (dotP x w * dotP x w).swap)) := by
      refine BPair.oneValue_trans (pairW' _ hw'l) ?_
      rw [dotP_comm (vecAdd (vecScale κ w) ((vecScale (dotP x w) x).map BPair.swap)) x,
        dotP_comm (vecAdd (vecScale κ w) ((vecScale (dotP x w) x).map BPair.swap)) w]
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl κ) (pairW' w hw))
        (swap_congr (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hxw') (BPair.mul_unit _)))) ?_
      rw [dotP_comm w x]
      exact BPair.add_unit _
    have hC' := coefs_scaled n L x w κ (dotP x w) hL hw hx hxL
    have ih := gradient_deficit n L
      (vecAdd (vecScale κ w) ((vecScale (dotP x w) x).map BPair.swap)) e κ d
      hL hw'l he hperpL hselfL hκ heTL hd hdp
    have ih' : κ * (κ * dotP (coefs L w) (coefs L w)) * d
          + κ * dotP e w * (κ * dotP e w) * κ
        ≤ κ * (κ * dotP w w + (dotP x w * dotP x w).swap) * κ * d :=
      leB_congr (BPair.add_congr (BPair.mul_congr_left hC')
          (BPair.mul_congr_left (BPair.mul_congr hew' hew')))
        (BPair.mul_congr_left (BPair.mul_congr_left hww')) ih
    have hm : BPair.unit < κ * κ :=
      leB_ltB_trans (leB_congr_right (BPair.oneValue_symm (BPair.unit_mul κ))
        (leB_refl BPair.unit)) (ltB_mulPos hκ hκ)
    have hadd := leB_add (leB_refl (κ * κ * (dotP x w * dotP x w) * d)) ih'
    have hlhs : ((κ * κ) * ((dotP x w * dotP x w + dotP (coefs L w) (coefs L w)) * d
          + dotP e w * dotP e w * κ)).oneValue
        (κ * κ * (dotP x w * dotP x w) * d
          + (κ * (κ * dotP (coefs L w) (coefs L w)) * d
            + κ * dotP e w * (κ * dotP e w) * κ)) :=
      polEqB [κ, d, dotP x w, dotP (coefs L w) (coefs L w), dotP e w]
        (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.add (Pol.mul (Pol.add (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 4))) (Pol.mon (Mon.var 0)))))
        (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2)))) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 4))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 4)))) (Pol.mon (Mon.var 0)))))
        (by decide +kernel)
    have hrhs : BPair.oneValue
        (κ * κ * (dotP x w * dotP x w) * d
          + κ * (κ * dotP w w + (dotP x w * dotP x w).swap) * κ * d)
        ((κ * κ) * (dotP w w * κ * d)) := by
      refine BPair.oneValue_trans
        (polEqB [κ, d, dotP x w, dotP w w, (dotP x w * dotP x w).swap]
          (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2)))) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 4)))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))))
          (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1)))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 4)))))
          (by decide +kernel)) ?_
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.add_swap_null (dotP x w * dotP x w)))) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _) (BPair.mul_unit _)) ?_
      exact BPair.add_unit _
    have hfin : (κ * κ) * ((dotP x w * dotP x w + dotP (coefs L w) (coefs L w)) * d
          + dotP e w * dotP e w * κ)
        ≤ (κ * κ) * (dotP w w * κ * d) :=
      leB_congr (BPair.oneValue_symm hlhs) hrhs hadd
    rw [BPair.mul_comm (κ * κ) ((dotP x w * dotP x w + dotP (coefs L w) (coefs L w)) * d
          + dotP e w * dotP e w * κ),
      BPair.mul_comm (κ * κ) (dotP w w * κ * d)] at hfin
    exact leB_unscale hm hfin

/-! `lem:loopcap`'s member reads: the index, the adjoint tie's pair,
the residual cap, the coordinates' tie, the dispersion's pair and the
second-order pair, each a read of the member's tables (`con:fusion`'s
fields at the member's instantiation) at the member's derived residue
`r` (the interface's field), the form's point `C₂(θ) = 2 (r + 1)`
(`prop:anchor`), and its floor label `f₀`, the cleared Casimir's second member withdrawn from
every quotient of two Casimirs.  A pair positive by its shape is a
scalar pair (`ground.Pair`) and a pair whose first datum reads the
sum's unit a composite (`ground.CPair`); a least or largest member
over a list is the trichotomy fold from a seed (`ground.leastBy`);
and the closure enters occupied, its first member beside the rest. -/

/-- The block's index `κ_λ = [C₂(λ) d_λ : dim G]`, the Casimir the
cleared read's multiple of `C₂(θ)`. -/
def indexAt {L : Type} (F : fusion.Data L) (l : L) : Pair :=
  ⟨posOfNat (F.c2N l * (2 * (F.residue + 1)) * F.dim l), posOfNat (F.c2D * F.dim F.theta)⟩

/-- The joined index `κ_Σ`, the closure's indices' fold from its
first member. -/
def joinedIndex {L : Type} (F : fusion.Data L) (l : L) (t : List L) : Pair :=
  t.foldl (fun acc m => acc + indexAt F m) (indexAt F l)

/-- The adjoint tie's pair `t_λ = [C₂(λ + λ̄) : κ_λ]`, the Casimirs'
cleared second member and the form's point withdrawn:
`[ĉ₂(λ + λ̄) dim G : ĉ₂(λ) d_λ]` at the cleared reads. -/
def tieAt {L : Type} (F : fusion.Data L) (l : L) : Pair :=
  ⟨posOfNat (F.c2N (F.add l (F.dual l)) * F.dim F.theta), posOfNat (F.c2N l * F.dim l)⟩

/-- `t_L`, the least tie over the closure, one trichotomy fold. -/
def tieLeast {L : Type} (F : fusion.Data L) (l : L) (t : List L) : Pair :=
  leastBy (fun x y => decide (x ≤ y)) (tieAt F l) (t.map (tieAt F))

/-- The second member's pair `c^z_λ` at the block's dimension `d`:
`[4 Σ_{j ≤ d-2} j² Σ_{2 ≤ k < d} C(d, k) (4d)^{k-2} : d²]`, the
first datum the sum's unit at a dimension below three. -/
def secondMember (d : Nat) : CPair :=
  ⟨BPair.ofNat (4 * sumNat ((List.range (d - 1)).map (fun j => j * j))
    * sumNat ((List.range (d - 2)).map (fun i => pasc d (i + 2) * (4 * d) ^ i))),
   posOfNat (d * d)⟩

/-- The residual cap
`c^⊥_λ = [4 C₂(λ) C₂(λ + λ̄) : κ_λ C₂(f₀)] + [c^z_λ : d_λ]` at the
member floor `f₀`, the first summand at the cleared reads
`[4 ĉ₂(λ + λ̄) dim G : d_λ ĉ₂(f₀)]` and the second summand at a
label distinct from its dual, vacant at a self-dual label. -/
def residualCap {L : Type} (F : fusion.Data L) (f0 l : L) : CPair :=
  let first : CPair := CPair.ofPair
    ⟨posOfNat (4 * F.c2N (F.add l (F.dual l)) * F.dim F.theta),
     posOfNat (F.dim l * F.c2N f0)⟩ .one
  if F.eqL l (F.dual l) then first
  else first + secondMember (F.dim l) * CPair.ofPair ⟨1, posOfNat (F.dim l)⟩ .one

/-- The adjoint's residual cap `c^⊥_θ = [4 C₂(2θ) : C₂(f₀)]`. -/
def adjResidualCap {L : Type} (F : fusion.Data L) (f0 : L) : Pair :=
  ⟨posOfNat (4 * F.c2N (F.add F.theta F.theta)), posOfNat (F.c2N f0)⟩

/-- The coordinates' tie
`c_{β,λ} = [3 (t_λ² ([1 : d_θ] + c^⊥_θ) + 4 t_λ) : κ_θ]` at
`κ_θ = 2 (r + 1)`. -/
def coordTie {L : Type} (F : fusion.Data L) (f0 l : L) : Pair :=
  Pair.ofPos 3
    * (tieAt F l * tieAt F l * (⟨1, posOfNat (F.dim F.theta)⟩ + adjResidualCap F f0)
      + Pair.ofPos 4 * tieAt F l)
    * ⟨1, posOfSucc (2 * F.residue + 1)⟩

/-- The closure's members off `λ`'s dual class. -/
def offClass {L : Type} (F : fusion.Data L) (ls : List L) (l : L) : List L :=
  ls.filter (fun m => !(F.eqL m l || F.eqL m (F.dual l)))

/-- `κ'_λ`, the indices' fold over the closure's members off `λ`'s
dual class, the sum's unit at a closure of one dual class. -/
def offClassIndex {L : Type} (F : fusion.Data L) (ls : List L) (l : L) : CPair :=
  CPair.sum ((offClass F ls l).map (fun m => CPair.ofPair (indexAt F m) .one))

/-- The dispersion's term at a label,
`c^⊥_λ + [2 κ_λ κ'_λ : κ_Σ] c_{β,λ}`, the second summand the doubled
index against the off-class index at the coordinates' tie's cofactor
at the joined index. -/
def dispersionAt {L : Type} (F : fusion.Data L) (f0 l : L) (t : List L) (m : L) : CPair :=
  residualCap F f0 m
    + CPair.ofPair (Pair.ofPos 2 * indexAt F m) .one * offClassIndex F (l :: t) m
      * CPair.ofPair ((coordTie F f0 m).cofactor (joinedIndex F l t)) .one

/-- The dispersion's pair `c_ϱ`, the largest term over the closure,
one trichotomy fold. -/
def dispersion {L : Type} (F : fusion.Data L) (f0 l : L) (t : List L) : CPair :=
  leastBy (fun x y => decide (y ≤ x)) (dispersionAt F f0 l t l)
    (t.map (dispersionAt F f0 l t))

/-- The closure's least dimension `d₋`, one trichotomy fold. -/
def leastDim {L : Type} (F : fusion.Data L) (l : L) (t : List L) : Nat :=
  t.foldl (fun acc m => natMin acc (F.dim m)) (F.dim l)

/-- The second-order pair `s_L = [1 : d₋] + c_ϱ`. -/
def secondOrder {L : Type} (F : fusion.Data L) (f0 l : L) (t : List L) : CPair :=
  CPair.ofPair ⟨1, posOfNat (leastDim F l t)⟩ .one + dispersion F f0 l t

end loopcap
