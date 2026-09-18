import MassGap.Loopcap
import MassGap.Lap

/-!
`lem:cornercert`'s squares' certificate, its matrix reads: the rows'
square fold `rowSq` (each row's self-pairing over the row keys),
its transpose read `rowSq_transpose` (the entries' squares fold in
either order, `dotP_fold` at the double fold's exchange), the
product read `rowSq_matMul` (each column of `A g` the first factor
against the column, its self-pairing the column's form at the
transpose product `A^T A`), the projector read `proj_split` (a
symmetric idempotent's form joined to the residual's self-pairing
reads the vector's own), and the local square `local_square`: at
moved fluxes `G` whose rows' squares read the product's, the
transports orthogonal, and the kernel identity `A^T A ≡ c Π`, the
squares' fold joined to the pair's multiple of the residuals'
squares off the range reads the pair's multiple of the fluxes'
squares, the projector's symmetry the tex's own datum of the range
projector, the modes' kernel's display at `S Δ S = [1 : 2κ] Π` with
`A = K^T S`, the residual the fluxes moved to one vertex projected
off the incidence's range; the local square against the gradient
deficit (`sq_deficit`, cleared at the count: the count's multiple of
the squares' fold at or below the pair's multiple of the deficits'
cleared fold, each row's square at `lem:loopcap`'s cleared deficit
read), closing at the assembly's scale through `deficit_seam` (the
count and the index withdrawn at the pair `c ≡ κ + κ`, the scale
pair's square joined); and the assembly (`floor_assembly`, cleared at the scale
pair `[n : s]` and the doubled count): the three comparisons, the
local square against the deficit, the plaquette terms at the
deficits `δ_p + χ_p ≡ d`, and the cross read at the scale's first
member with the deviation priced at the covering count, collect
per plaquette at the completed square (`complete_sq` at the shift
`n d (a + b)`), the floor line the fold over the plaquettes of the
doubled count's multiple of the flat read's multiple of the
kernel's read against the scale's square, less the shift's square.
The cross read's deviation (`crossDev`): at a plaquette's character
and a boundary link, the joint insertion across the tree path joined
to the traversal sign's multiple of the base link's Laplacian's
balance partner at the tree's site at the word's unit, the loop's
coefficient against the second gradient at the tree path against
the arc, the arc's read the base's Laplacian at the traversal sign
(`prop:lap`'s arc read at `lap.jointComb`, `states.padState`).
-/
namespace cornercert
open ground elim inertia


/-- The rows' square fold of a matrix, each row's self-pairing over
the row keys. -/
def rowSq (M : Mat) : BPair :=
  bsum (fun i => dotP (getAt [] M i) (getAt [] M i)) (List.range M.length)

/-- The entries' squares fold in either order: a matrix's rows'
square fold reads its transpose's. -/
theorem rowSq_transpose (n : Nat) (M : Mat) (hM : rowsLen n M)
    (h0 : 0 < M.length) :
    (rowSq M).oneValue (rowSq (transposeM M)) := by
  have hTl : (transposeM M).length = n := length_transposeM M hM h0
  have hTr : rowsLen M.length (transposeM M) := rowsLen_transposeM M
  show (bsum (fun i => dotP (getAt [] M i) (getAt [] M i))
      (List.range M.length)).oneValue
    (bsum (fun c => dotP (getAt [] (transposeM M) c)
      (getAt [] (transposeM M) c)) (List.range (transposeM M).length))
  rw [hTl]
  rw [bsum_congr_range _ (fun i => bsum (fun c =>
      getAt BPair.unit (getAt [] M i) c * getAt BPair.unit (getAt [] M i) c)
      (List.range n)) M.length
      (fun i hi => dotP_fold n _ _ (rowsLen_getAt M i hM hi)
        (rowsLen_getAt M i hM hi))]
  rw [bsum_congr_range
      (fun c => dotP (getAt [] (transposeM M) c) (getAt [] (transposeM M) c))
      (fun c => bsum (fun i =>
        getAt BPair.unit (getAt [] M i) c * getAt BPair.unit (getAt [] M i) c)
        (List.range M.length)) n
      (fun c hc => by
        rw [dotP_fold M.length _ _
            (rowsLen_getAt (transposeM M) c hTr (by rw [hTl]; exact hc))
            (rowsLen_getAt (transposeM M) c hTr (by rw [hTl]; exact hc))]
        exact bsum_congr_range _ _ M.length (fun i hi => by
          rw [getAt_transposeM BPair.unit M hM c i hc hi]))]
  exact bsum_swap (fun i c =>
    getAt BPair.unit (getAt [] M i) c * getAt BPair.unit (getAt [] M i) c)
    (List.range M.length) (List.range n)

/-- The rows' square fold of a product reads the Gram's quadratic
form at the second factor's columns: each column of the product is
the first factor against the column, and its self-pairing is the
column's form at the first factor's transpose product. -/
theorem rowSq_matMul (P n : Nat) (A g : Mat) (hA : rowsLen P A)
    (hA0 : 0 < A.length) (hg : rowsLen n g) (hgl : g.length = P)
    (hP : 0 < P) :
    (rowSq (matMul A g)).oneValue
      (bsum (fun c => quadForm (matMul (transposeM A) A)
        (getAt [] (transposeM g) c)) (List.range n)) := by
  have hMr : rowsLen n (matMul A g) :=
    rowsLen_matMul_of A g (fun _ => hgl ▸ hP) hg
  have hMl : (matMul A g).length = A.length := length_matMul A g
  have hM0 : 0 < (matMul A g).length := by rw [hMl]; exact hA0
  have hTl : (transposeM (matMul A g)).length = n :=
    length_transposeM (matMul A g) hMr hM0
  have hTgl : (transposeM g).length = n := length_transposeM g hg (hgl ▸ hP)
  have hTgr : rowsLen g.length (transposeM g) := rowsLen_transposeM g
  refine BPair.oneValue_trans (rowSq_transpose n (matMul A g) hMr hM0) ?_
  show (bsum (fun c => dotP (getAt [] (transposeM (matMul A g)) c)
      (getAt [] (transposeM (matMul A g)) c))
      (List.range (transposeM (matMul A g)).length)).oneValue _
  rw [hTl]
  refine bsum_congr_range_ov _ _ n (fun c hc => ?_)
  have hcl : (getAt [] (transposeM (matMul A g)) c).length = A.length := by
    rw [rowsLen_getAt (transposeM (matMul A g)) c
      (rowsLen_transposeM (matMul A g)) (by rw [hTl]; exact hc), hMl]
  have hv : (getAt [] (transposeM g) c).length = P := by
    rw [rowsLen_getAt (transposeM g) c hTgr (by rw [hTgl]; exact hc), hgl]
  have hcol : poly.oneValue (getAt [] (transposeM (matMul A g)) c)
      (matVec A (getAt [] (transposeM g) c)) := by
    refine poly.oneValue_of_entries _ _ ?_ ?_
    · rw [hcl, matVec_length]
    · intro t ht
      rw [hcl] at ht
      rw [getAt_transposeM BPair.unit (matMul A g) hMr c t hc
          (by rw [hMl]; exact ht),
        getAt_matMul A g t ht,
        ground.getAt_map ([] : List BPair) BPair.unit _ (transposeM g) c
          (by rw [hTgl]; exact hc)]
      show (dotN (getAt [] A t) (getAt [] (transposeM g) c)).oneValue
        (getAt BPair.unit (A.map (fun r => dotN r (getAt [] (transposeM g) c))) t)
      rw [ground.getAt_map ([] : List BPair) BPair.unit _ A t ht]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (dotP_congr_left _ _ _
    (fun j _ => poly.oneValue_getAt j hcol)) ?_
  rw [dotP_comm]
  refine BPair.oneValue_trans (dotP_congr_left _ _ _
    (fun j _ => poly.oneValue_getAt j hcol)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) ?_
  refine BPair.oneValue_symm ?_
  show (dotN (getAt [] (transposeM g) c)
    (matVec (matMul (transposeM A) A) (getAt [] (transposeM g) c))).oneValue _
  refine BPair.oneValue_trans (dotN_congrR _ _ _
    (matVec_matMul (transposeM A) A P hA _ hv)) ?_
  exact dotN_transpose_flip A P hA _ (matVec A _) hv (matVec_length A _)

/-- A projector's form against a vector joined to the residual's
self-pairing reads the vector's own: the residual is the vector
less its image, its self-pairing the vector's less the form, the
image's self-pairing the form at the symmetric idempotent. -/
theorem proj_split (n : Nat) (Pi : Mat) (hPi : sqAt Pi n)
    (hsym : matOneValue (transposeM Pi) Pi)
    (hidem : matOneValue (matMul Pi Pi) Pi)
    (v : List BPair) (hv : v.length = n) :
    (quadForm Pi v + dotN (vecAdd v ((matVec Pi v).map BPair.swap))
      (vecAdd v ((matVec Pi v).map BPair.swap))).oneValue (dotN v v) := by
  have hr : rowsLen n Pi := rowsLen_of_sqAt hPi
  have hl : Pi.length = n := sqAt_len hPi
  have hwl : (matVec Pi v).length = n := by rw [matVec_length, hl]
  have hsl : ((matVec Pi v).map BPair.swap).length = n := by
    rw [ground.length_map, hwl]
  have hal : (vecAdd v ((matVec Pi v).map BPair.swap)).length = n :=
    length_vecAdd _ _ n hv hsl
  have hww : (dotN (matVec Pi v) (matVec Pi v)).oneValue
      (dotN v (matVec Pi v)) := by
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (dotN_matVec_congrM Pi (matMul Pi Pi) v v (matOne_symm hidem)) ?_
    refine BPair.oneValue_trans
      (dotN_congrR v _ _ (matVec_matMul Pi Pi n hr v hv)) ?_
    refine BPair.oneValue_trans
      (dotN_matVec_congrM Pi (transposeM Pi) v (matVec Pi v)
        (matOne_symm hsym)) ?_
    exact dotN_transpose_flip Pi n hr v (matVec Pi v) hv
      (by rw [matVec_length, hl])
  have hexp : (dotN (vecAdd v ((matVec Pi v).map BPair.swap))
      (vecAdd v ((matVec Pi v).map BPair.swap))).oneValue
      ((dotN v v + (dotN v (matVec Pi v)).swap)
        + ((dotN v (matVec Pi v)).swap + dotN v (matVec Pi v))) := by
    refine BPair.oneValue_trans (dotN_addRow v _ _ (by rw [hv, hal])
      (by rw [hsl, hal])) ?_
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_trans (dotN_comm v _) ?_
      refine BPair.oneValue_trans
        (dotN_addRow v _ v (by rw [hv]) (by rw [hsl, hv])) ?_
      rw [dotN_swapLeft]
      exact BPair.add_congr (BPair.oneValue_refl _)
        (swap_congr (dotN_comm (matVec Pi v) v))
    · refine BPair.oneValue_trans (dotN_comm _ _) ?_
      refine BPair.oneValue_trans (dotN_addRow v _ ((matVec Pi v).map BPair.swap)
        (by rw [hv, hsl]) (by rw [hsl])) ?_
      rw [dotN_swap, dotN_swapLeft, dotN_swap, BPair.swap_swap]
      exact BPair.add_congr (BPair.oneValue_refl _) hww
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) hexp) ?_
  show (dotN v (matVec Pi v) + ((dotN v v + (dotN v (matVec Pi v)).swap)
    + ((dotN v (matVec Pi v)).swap + dotN v (matVec Pi v)))).oneValue (dotN v v)
  rw [BPair.add_left_comm (dotN v (matVec Pi v)),
    BPair.add_assoc (dotN v v),
    ← BPair.add_assoc ((dotN v (matVec Pi v)).swap) (dotN v (matVec Pi v))]
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr (BPair.swap_add_null (BPair.oneValue_refl _))
      (BPair.swap_add_null (BPair.oneValue_refl _)))) ?_
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_unit _)) ?_
  exact BPair.add_unit _

/-- `lem:cornercert`'s local square: at the moved fluxes `G` whose rows'
squares read the product's (the transports orthogonal), the kernel
identity `A^T A ≡ c Π` at a symmetric idempotent `Π`, the squares'
fold joined to the pair's multiple of the residuals' squares off
the range reads the pair's multiple of the fluxes' squares. -/
theorem local_square (P n L : Nat) (G A g Pi : Mat) (c : BPair)
    (hA : rowsLen P A) (hAl : A.length = L) (hL : 0 < L)
    (hg : rowsLen n g) (hgl : g.length = P) (hP : 0 < P)
    (hPi : sqAt Pi P) (hsym : matOneValue (transposeM Pi) Pi)
    (hidem : matOneValue (matMul Pi Pi) Pi)
    (hker : matOneValue (matMul (transposeM A) A) (matScaleB c Pi))
    (horth : (rowSq G).oneValue (rowSq (matMul A g))) :
    (rowSq G + c * bsum (fun a =>
        dotN (vecAdd (getAt [] (transposeM g) a)
            ((matVec Pi (getAt [] (transposeM g) a)).map BPair.swap))
          (vecAdd (getAt [] (transposeM g) a)
            ((matVec Pi (getAt [] (transposeM g) a)).map BPair.swap)))
        (List.range n)).oneValue (c * rowSq g) := by
  have hA0 : 0 < A.length := by rw [hAl]; exact hL
  have hTgl : (transposeM g).length = n := length_transposeM g hg (hgl ▸ hP)
  have hTgr : rowsLen g.length (transposeM g) := rowsLen_transposeM g
  have hcol : ∀ a, a < n → (getAt [] (transposeM g) a).length = P := fun a ha => by
    rw [rowsLen_getAt (transposeM g) a hTgr (by rw [hTgl]; exact ha), hgl]
  -- the squares' fold at the scaled projector's forms
  have h1 : (rowSq G).oneValue
      (bsum (fun a => c * quadForm Pi (getAt [] (transposeM g) a)) (List.range n)) := by
    refine BPair.oneValue_trans horth ?_
    refine BPair.oneValue_trans (rowSq_matMul P n A g hA hA0 hg hgl hP) ?_
    refine bsum_congr_range_ov _ _ n (fun a _ => ?_)
    refine BPair.oneValue_trans
      (dotN_matVec_congrM _ _ _ _ hker) ?_
    exact quadForm_scaleB c Pi _
  refine BPair.oneValue_trans (BPair.add_congr h1 (BPair.oneValue_symm (foldB_mul_left c _ (List.range n)))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (famFold_add_ov bpairFoldLaws _ _ (List.range n))) ?_
  refine BPair.oneValue_trans (bsum_congr_range_ov _
    (fun a => c * dotN (getAt [] (transposeM g) a) (getAt [] (transposeM g) a)) n
    (fun a ha => by
      show (c * quadForm Pi _ + c * dotN _ _).oneValue _
      rw [← BPair.left_distrib]
      exact BPair.mul_congr (BPair.oneValue_refl c)
        (proj_split P Pi hPi hsym hidem _ (hcol a ha)))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.oneValue_symm (foldB_mul_left c _ (List.range n)))) ?_
  refine BPair.mul_congr (BPair.oneValue_refl c) ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (rowSq_transpose n g hg (hgl ▸ hP)) ?_
  show (bsum (fun a => dotP (getAt [] (transposeM g) a) (getAt [] (transposeM g) a))
    (List.range (transposeM g).length)).oneValue _
  rw [hTgl]
  exact bsum_congr_range_ov _ _ n (fun a _ => BPair.oneValue_symm (dotN_read _ _))

/-- `lem:cornercert`'s local square against the gradient deficit, cleared
at the count: at the squares' fold joined to the pair's multiple of
the residuals' read, at or beyond the sum's unit, reading the pair's
multiple of the fluxes' squares, and every flux's square at the
gradient deficit's cleared read, the count's multiple of the squares'
fold sits at or below the pair's multiple of the deficits' cleared
fold, each deficit's doubled read at the index and the count less
its square at the index. -/
theorem sq_deficit (P : Nat) (g : Mat) (δ : Nat → BPair)
    (G2 R c κ d : BPair) (hgl : g.length = P)
    (hloc : (G2 + c * R).oneValue (c * rowSq g))
    (hR : BPair.unit ≤ R) (hc : BPair.unit ≤ c) (hd0 : BPair.unit ≤ d)
    (hdef : ∀ p, p < P →
      dotP (getAt [] g p) (getAt [] g p) * d + δ p * δ p * κ
        ≤ (δ p + δ p) * κ * d) :
    d * G2 ≤ c * bsum (fun p => (δ p + δ p) * κ * d + (δ p * δ p * κ).swap)
      (List.range P) := by
  have h1 : G2 ≤ c * rowSq g := dom_of_split hloc (unitLeMul hc hR)
  have h1' : d * G2 ≤ d * (c * rowSq g) := leB_mulR hd0 h1
  have h2 : (d * (c * rowSq g)).oneValue
      (c * bsum (fun p => d * dotP (getAt [] g p) (getAt [] g p)) (List.range P)) := by
    rw [BPair.mul_left_comm d c (rowSq g)]
    refine BPair.mul_congr (BPair.oneValue_refl c) ?_
    show (d * bsum (fun i => dotP (getAt [] g i) (getAt [] g i))
      (List.range g.length)).oneValue _
    rw [hgl]
    exact BPair.oneValue_symm (foldB_mul_left d _ (List.range P))
  refine leB_trans (leB_congr_right h2 h1') ?_
  refine leB_mulR hc ?_
  refine bsum_le _ _ (List.range P) (fun p hp => ?_)
  have h3 := hdef p (ltOfCountRange hp)
  rw [BPair.mul_comm d]
  exact leB_swapL (leB_congr_left
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_of_eq (BPair.swap_swap _))) h3)

/-- The local square's deficit read at the assembly's scale: the
count-cleared read `sq_deficit` closes, at the pair `c ≡ κ + κ` and
the squares' fold `G2 ≡ c c S`, to the uncleared fold `S` at the
scale pair's square, the assembly's deficit binder. -/
theorem deficit_seam (P : Nat) (δ : Nat → BPair) (S G2 c κ d s : BPair)
    (hG : G2.oneValue (c * c * S)) (hc : c.oneValue (κ + κ))
    (hκ : BPair.unit < κ) (hs0 : BPair.unit ≤ s)
    (h : d * G2 ≤ c * bsum (fun p => (δ p + δ p) * κ * d + (δ p * δ p * κ).swap)
      (List.range P)) :
    bsum (fun p => s * δ p * (s * δ p) + ((d + d) * (s * s) * δ p).swap)
      (List.range P) ≤ ((d + d) * (s * s) * S).swap := by
  have hc0 : BPair.unit < c :=
    ltB_trans_le (unitLtAdd hκ (leB_of_lt hκ)) (Or.inl (BPair.oneValue_symm hc))
  -- the right side at the index withdrawn
  have hR : (c * bsum (fun p => (δ p + δ p) * κ * d + (δ p * δ p * κ).swap)
      (List.range P)).oneValue
      (c * (κ * bsum (fun p => (δ p + δ p) * d + (δ p * δ p).swap) (List.range P))) := by
    refine BPair.mul_congr (BPair.oneValue_refl c) ?_
    refine BPair.oneValue_trans (bsum_congr_range_ov _
      (fun p => κ * ((δ p + δ p) * d + (δ p * δ p).swap)) P (fun p _ => ?_)) ?_
    · rw [BPair.left_distrib, BPair.mul_swap κ (δ p * δ p), BPair.mul_comm κ (δ p * δ p),
        BPair.mul_comm (δ p + δ p) κ, BPair.mul_assoc κ (δ p + δ p) d]
      exact BPair.oneValue_refl _
    · exact foldB_mul_left κ _ (List.range P)
  -- the left side at the pair withdrawn
  have hL : (d * G2).oneValue (c * (κ * ((d + d) * S))) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl d) hG) ?_
    rw [BPair.mul_comm d, BPair.mul_assoc (c * c) S d, BPair.mul_assoc c c (S * d)]
    refine BPair.mul_congr (BPair.oneValue_refl c) ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left hc) ?_
    exact polEqB [κ, S, d]
        (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.mul (Mon.var 1) (Mon.var 2))))
        (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 1)))) (by decide +kernel)
  have h1 : (d + d) * S ≤ bsum (fun p => (δ p + δ p) * d + (δ p * δ p).swap)
      (List.range P) :=
    leB_unscale_left hκ (leB_unscale_left hc0 (leB_congr hL hR h))
  -- the scale's square
  have h2 : (s * s) * ((d + d) * S) ≤ (s * s) * bsum
      (fun p => (δ p + δ p) * d + (δ p * δ p).swap) (List.range P) :=
    leB_mulR (unitLeMul hs0 hs0) h1
  have hA : ((s * s) * bsum (fun p => (δ p + δ p) * d + (δ p * δ p).swap)
      (List.range P)).oneValue
      (bsum (fun p => (d + d) * (s * s) * δ p) (List.range P)
        + (bsum (fun p => s * δ p * (s * δ p)) (List.range P)).swap) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (foldB_mul_left (s * s) _ (List.range P))) ?_
    refine BPair.oneValue_trans (bsum_congr_range_ov _
      (fun p => (d + d) * (s * s) * δ p + (s * δ p * (s * δ p)).swap) P
      (fun p _ => ?_)) ?_
    · rw [BPair.left_distrib, BPair.mul_swap (s * s) (δ p * δ p)]
      refine BPair.add_congr ?_ (swap_congr (BPair.oneValue_of_eq ?_))
      · exact polEqB [s, (δ p), d]
            (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0))) (Pol.mul (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))))
            (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.mon (Mon.var 1))) (by decide +kernel)
      · rw [BPair.mul_assoc s (δ p) (s * δ p), ← BPair.mul_assoc (δ p) s (δ p),
          BPair.mul_comm (δ p) s, BPair.mul_assoc s (δ p) (δ p),
          ← BPair.mul_assoc s s (δ p * δ p)]
    · refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws _ _ (List.range P)) ?_
      refine BPair.add_congr (BPair.oneValue_refl _) ?_
      show (ground.famFold BPair.add BPair.unit (fun p => (s * δ p * (s * δ p)).swap)
        (List.range P)).oneValue _
      rw [fold_swap]
      exact BPair.oneValue_refl _
  have h3 := leB_swapR (leB_congr_right hA h2)
  -- the target's fold splits as the two folds
  have hT : (bsum (fun p => s * δ p * (s * δ p) + ((d + d) * (s * s) * δ p).swap)
      (List.range P)).oneValue
      (bsum (fun p => s * δ p * (s * δ p)) (List.range P)
        + (bsum (fun p => (d + d) * (s * s) * δ p) (List.range P)).swap) := by
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws _ _ (List.range P)) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    show (ground.famFold BPair.add BPair.unit (fun p => ((d + d) * (s * s) * δ p).swap)
      (List.range P)).oneValue _
    rw [fold_swap]
    exact BPair.oneValue_refl _
  refine leB_congr_left (BPair.oneValue_symm hT) ?_
  -- from X + B ≤ A to B + A.swap ≤ X.swap
  have h4 := leB_swap h3
  have h5 : (bsum (fun p => (d + d) * (s * s) * δ p) (List.range P)).swap
      + bsum (fun p => s * δ p * (s * δ p)) (List.range P)
      ≤ ((s * s) * ((d + d) * S)).swap := by
    have h6 := leB_add h4 (leB_refl (bsum (fun p => s * δ p * (s * δ p)) (List.range P)))
    refine leB_congr_right ?_ h6
    show (((s * s) * ((d + d) * S)).swap
      + (bsum (fun p => s * δ p * (s * δ p)) (List.range P)).swap
      + bsum (fun p => s * δ p * (s * δ p)) (List.range P)).oneValue _
    rw [BPair.add_assoc]
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.swap_add_null (BPair.oneValue_refl _))) ?_
    exact BPair.add_unit _
  have h5' : bsum (fun p => s * δ p * (s * δ p)) (List.range P)
      + (bsum (fun p => (d + d) * (s * s) * δ p) (List.range P)).swap
      ≤ ((s * s) * ((d + d) * S)).swap := by
    rw [BPair.add_comm]
    exact h5
  refine leB_congr_right (BPair.oneValue_of_eq ?_) h5'
  rw [BPair.mul_comm (s * s) ((d + d) * S), BPair.mul_assoc (d + d) S (s * s),
    BPair.mul_comm S (s * s), ← BPair.mul_assoc]

/-- One plaquette's completed square, `complete_sq` at the vacant
third datum: the shifted square joined to the shift's square's
balance partner reads the square joined to the doubled product's. -/
private theorem plaq_complete (x M : BPair) :
    ((x + M.swap) * (x + M.swap) + (M * M).swap).oneValue
      (x * x + (M * x + M * x).swap) :=
  BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_symm (BPair.add_unit (x * x)))
      (BPair.oneValue_refl _))
    (BPair.oneValue_trans (complete_sq x M BPair.unit)
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_add _))))

/-- `lem:cornercert`'s assembly, cleared at the scale pair `[n : s]` and
the doubled count: the fold of squares joined to the electric
member's balance partner reads the pencil at the dual representative
less the multiplication `ζ`, and `ζ` reads at or beyond the floor
line by the three comparisons: the local square against the
gradient deficit (the doubled count's multiple of the scale's square
against the squares' fold at or below the scaled deficits' squares'
fold less their doubled-count reads), the plaquette terms at the
deficits (`δ_p + χ_p ≡ d`), and the cross read at the scale's
first member with the deviation priced at the covering count (the
kernel's read at the flat read against the pair's multiple of the
deficits' fold); each plaquette completes its square at the shift
`M = n d (a + b)`, the floor line the fold over the plaquettes of the
doubled count's multiple of the flat read's multiple of the kernel's
read against the scale's square, less the shift's square. -/
theorem floor_assembly (P : Nat) (δ χ : Nat → BPair)
    (G2 X d n s a b L0 : BPair) (hd0 : BPair.unit ≤ d) (hs0 : BPair.unit ≤ s)
    (h1 : bsum (fun p => s * δ p * (s * δ p) + ((d + d) * (s * s) * δ p).swap)
        (List.range P) ≤ ((d + d) * (s * s) * G2).swap)
    (h2 : ∀ p, p < P → (δ p + χ p).oneValue d)
    (h3 : bsum (fun _ => n * a * d) (List.range P)
        + (n * (a + b) * bsum δ (List.range P)).swap ≤ (n * X).swap)
    (hL : L0.oneValue (bsum (fun _ => (d + d) * d * (n * s * a + (s * s).swap)
        + (n * d * (a + b) * (n * d * (a + b))).swap) (List.range P))) :
    bsum (fun p => (s * δ p + (n * d * (a + b)).swap)
        * (s * δ p + (n * d * (a + b)).swap)) (List.range P) + L0
      ≤ (d + d) * (s * s) * (G2.swap + (bsum χ (List.range P)).swap)
        + (d + d) * s * (n * X).swap := by
  -- the per-plaquette collected read
  let Cp : Nat → BPair := fun p =>
    s * δ p * (s * δ p) + ((d + d) * s * (n * (a + b) * δ p)).swap
      + (d + d) * d * (n * s * a + (s * s).swap)
  -- the left side collects at Cp
  have hLft : (bsum (fun p => (s * δ p + (n * d * (a + b)).swap)
      * (s * δ p + (n * d * (a + b)).swap)) (List.range P) + L0).oneValue
      (bsum Cp (List.range P)) := by
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) hL) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (famFold_add_ov bpairFoldLaws _ _ (List.range P))) ?_
    refine bsum_congr_range_ov _ _ P (fun p _ => ?_)
    show ((s * δ p + (n * d * (a + b)).swap) * (s * δ p + (n * d * (a + b)).swap)
      + ((d + d) * d * (n * s * a + (s * s).swap)
        + (n * d * (a + b) * (n * d * (a + b))).swap)).oneValue (Cp p)
    rw [BPair.add_comm ((d + d) * d * (n * s * a + (s * s).swap)), ← BPair.add_assoc]
    refine BPair.add_congr ?_ (BPair.oneValue_refl _)
    refine BPair.oneValue_trans (plaq_complete (s * δ p) (n * d * (a + b))) ?_
    exact (BPair.add_congr (BPair.oneValue_refl _) (swap_congr (polEqB [n, d, a, b, s, (δ p)]
        (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 5)))) (Pol.mul (Pol.mul (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 1))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.mul (Mon.var 4) (Mon.var 5)))))
        (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 4))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3)))) (Pol.mon (Mon.var 5)))) (by decide +kernel))))
  -- the right side's floor collects at Cp as well
  have hχ : ((bsum χ (List.range P)).swap).oneValue
      (bsum (fun p => d.swap + δ p) (List.range P)) := by
    show ((ground.famFold BPair.add BPair.unit χ (List.range P)).swap).oneValue _
    rw [← fold_swap χ (List.range P)]
    refine bsum_congr_range_ov _ _ P (fun p hp => ?_)
    have h := h2 p hp
    have hc : (χ p).oneValue (d + (δ p).swap) :=
      BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_symm h) (BPair.oneValue_refl _))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.add_assoc (δ p) (χ p) (δ p).swap))
          (BPair.add_swap_cancel (δ p) (χ p))))
    exact swap_congr hc
  -- the cross read scaled by the doubled count against the scale
  have h3' : (d + d) * s * (bsum (fun _ => n * a * d) (List.range P)
      + (n * (a + b) * bsum δ (List.range P)).swap)
      ≤ (d + d) * s * (n * X).swap :=
    leB_mulR (unitLeMul (unitLeAdd hd0 hd0) hs0) h3
  -- the local square's read at the swap moved inside
  have h1' : bsum (fun p => s * δ p * (s * δ p) + ((d + d) * (s * s) * δ p).swap)
      (List.range P) ≤ (d + d) * (s * s) * G2.swap :=
    leB_congr_right (BPair.oneValue_of_eq (BPair.mul_swap _ _).symm) h1
  -- the plaquette terms' read scaled
  have h2' : ((d + d) * (s * s) * (bsum χ (List.range P)).swap).oneValue
      ((d + d) * (s * s) * bsum (fun p => d.swap + δ p) (List.range P)) :=
    BPair.mul_congr (BPair.oneValue_refl _) hχ
  -- the three reads' join collects at Cp
  have hT : (bsum (fun p => s * δ p * (s * δ p) + ((d + d) * (s * s) * δ p).swap)
      (List.range P)
      + (d + d) * (s * s) * bsum (fun p => d.swap + δ p) (List.range P)
      + (d + d) * s * (bsum (fun _ => n * a * d) (List.range P)
        + (n * (a + b) * bsum δ (List.range P)).swap)).oneValue
      (bsum Cp (List.range P)) := by
    have hB : ((d + d) * (s * s) * bsum (fun p => d.swap + δ p) (List.range P)).oneValue
        (bsum (fun p => (d + d) * (s * s) * (d.swap + δ p)) (List.range P)) :=
      BPair.oneValue_symm (foldB_mul_left _ _ _)
    have hC : ((d + d) * s * (bsum (fun _ => n * a * d) (List.range P)
        + (n * (a + b) * bsum δ (List.range P)).swap)).oneValue
        (bsum (fun _ => (d + d) * s * (n * a * d)) (List.range P)
          + bsum (fun p => ((d + d) * s * (n * (a + b) * δ p)).swap) (List.range P)) := by
      rw [BPair.left_distrib, BPair.mul_swap]
      refine BPair.add_congr (BPair.oneValue_symm (foldB_mul_left _ _ _)) ?_
      refine BPair.oneValue_trans (swap_congr (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (foldB_mul_left _ _ _)))) ?_
      refine BPair.oneValue_trans (swap_congr (BPair.oneValue_symm (foldB_mul_left _ _ _))) ?_
      show ((ground.famFold BPair.add BPair.unit
        (fun i => (d + d) * s * (n * (a + b) * δ i)) (List.range P)).swap).oneValue _
      rw [← fold_swap]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (BPair.add_congr (BPair.add_congr
      (BPair.oneValue_refl _) hB) hC) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (famFold_add_ov bpairFoldLaws _ _ (List.range P)))) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_symm
      (famFold_add_ov bpairFoldLaws _ _ (List.range P))) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (famFold_add_ov bpairFoldLaws _ _ (List.range P))) ?_
    refine bsum_congr_range_ov _ _ P (fun p _ => ?_)
    show (s * δ p * (s * δ p) + ((d + d) * (s * s) * δ p).swap
      + (d + d) * (s * s) * (d.swap + δ p)
      + ((d + d) * s * (n * a * d) + ((d + d) * s * (n * (a + b) * δ p)).swap)).oneValue
      (Cp p)
    refine BPair.oneValue_trans (polEqB [s, (δ p), (((d + d) * (s * s) * δ p).swap), d, d.swap, n, a,
        (((d + d) * s * (n * (a + b) * δ p)).swap)]
        (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.mul (Mon.var 0) (Mon.var 1)))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.add (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 1))))) (Pol.add (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 6)) (Mon.var 3)))) (Pol.mon (Mon.var 7))))
        (Pol.add (Pol.add (Pol.add (Pol.mon (Mon.mul (Mon.mul (Mon.var 0) (Mon.var 1)) (Mon.mul (Mon.var 0) (Mon.var 1)))) (Pol.mon (Mon.var 7))) (Pol.add (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 5) (Mon.var 6)) (Mon.var 3)))) (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.mon (Mon.var 4))))) (Pol.add (Pol.mon (Mon.var 2)) (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 3))) (Pol.mon (Mon.mul (Mon.var 0) (Mon.var 0)))) (Pol.mon (Mon.var 1))))) (by decide +kernel)) (?_ : (s * δ p * (s * δ p) + ((d + d) * s * (n * (a + b) * δ p)).swap + ((d + d) * s * (n * a * d) + (d + d) * (s * s) * d.swap) + (((d + d) * (s * s) * δ p).swap + (d + d) * (s * s) * δ p)).oneValue (Cp p))
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.swap_add_null (BPair.oneValue_refl ((d + d) * (s * s) * δ p)))) ?_
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    show ((d + d) * s * (n * a * d) + (d + d) * (s * s) * d.swap).oneValue
      ((d + d) * d * (n * s * a + (s * s).swap))
    rw [BPair.left_distrib ((d + d) * d), BPair.mul_swap, BPair.mul_swap]
    exact BPair.add_congr
      (polEqB [d, s, n, a]
        (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 3)) (Mon.var 0))))
        (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.mul (Mon.mul (Mon.var 2) (Mon.var 1)) (Mon.var 3)))) (by decide +kernel))
      (swap_congr (BPair.oneValue_of_eq (BPair.mul_right_comm (d + d) (s * s) d)))
  refine leB_congr_left (BPair.oneValue_symm hLft) ?_
  refine leB_congr_left hT ?_
  rw [BPair.left_distrib ((d + d) * (s * s)) G2.swap]
  exact leB_add (leB_add h1' (Or.inl (BPair.oneValue_symm h2'))) h3'

/-- `lem:cornercert`'s cross read at one plaquette and one boundary link:
the deviation, the loop's coefficient against the second gradient at
the entrywise balance pair against the identity, the joint insertion
of the link's factors against the base link's across the tree path
joined to the traversal sign `k`'s multiple of the base link's
Laplacian's balance partner, the arc read at the sign (`prop:lap`),
the Laplacian read at the tree's site at the word's unit. -/
def crossDev (F Pt : states.FList) (l p : Nat) (k : poly.PPair)
    (c : states.Comb) : states.Comb :=
  lap.jointComb F Pt l p c
    ++ lap.scaleComb (poly.pMul lap.negP k)
      (states.padState F Pt (lap.lapComb F p c))

end cornercert
