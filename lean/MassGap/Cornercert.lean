import MassGap.Loopcap
import MassGap.Lap

/-!
`lem:corner`'s squares' certificate, its matrix reads: the rows'
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
projector — the tail read's display at `S Δ S = [1 : 2κ] Π` with
`A = K^T S`, the residual the fluxes moved to one vertex projected
off the incidence's range; the local square against the gradient
deficit (`sq_deficit`, cleared at the count: the count's multiple of
the squares' fold at or below the pair's multiple of the deficits'
cleared fold, each row's square at `lem:loopcap`'s cleared deficit
read), closing at the assembly's scale through `deficit_seam` (the
count and the index withdrawn at the pair `c ≡ κ + κ`, the scale
pair's square joined); and the assembly (`floor_assembly`, cleared at the scale
pair `[n : s]` and the doubled count): the three comparisons — the
local square against the deficit, the plaquette terms at the
deficits `δ_p + χ_p ≡ d`, and the cross read at the scale's first
member with the deviation priced at the covering count — collect
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
The cap block: the mode's variance read `mode_variance` (the
chi-square read at `dim G` degrees, cleared at the scale pair and the
profile's solve), the coordinate identity `coord_identity` (the parts
identity folded over the links and the generator index at the dual
weights), the excess read `excess_read` (the trial's form against
the floor line at the moments, the flux moments' fold read at the
gradient deficit against the deficits' fold) and the mode read
`mode_read` (the mode member's form at the moments, its scale reads'
coefficients collected at one group), each cleared at the scale
pair, the mass, the solve and the mode read, and the key's quarters
`key_quarters` (the excess and the mode read joined at the cap, the
three key comparisons putting the reads' sum under the floor's
multiple of the scale; the count read at the line beyond the reads'
sum is `momentfold.cap_line`'s).
-/
namespace corner
open ground elim inertia

/-- The rows' square fold of a matrix, each row's self-pairing over
the row keys. -/
def rowSq (M : Mat) : BPair :=
  bsum (fun i => dotP (getAt [] M i) (getAt [] M i)) (List.range M.length)

private theorem bsum_congr_range (F G : Nat → BPair) (n : Nat)
    (h : ∀ i, i < n → F i = G i) :
    bsum F (List.range n) = bsum G (List.range n) :=
  famFold_congr_members BPair.add BPair.unit F G (List.range n)
    (fun i hc => h i (ltOfCountRange hc))

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

private theorem bsum_congr_range_ov (F G : Nat → BPair) (n : Nat)
    (h : ∀ i, i < n → (F i).oneValue (G i)) :
    (bsum F (List.range n)).oneValue (bsum G (List.range n)) :=
  famFold_congr_members_ov BPair.oneValue BPair.add BPair.unit
    BPair.oneValue_refl (fun h1 h2 => BPair.add_congr h1 h2) F G
    (List.range n) (fun i hc => h i (ltOfCountRange hc))

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

/-- `lem:corner`'s local square: at the moved fluxes `G` whose rows'
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

/-- `lem:corner`'s local square against the gradient deficit, cleared
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
    rw [BPair.right_distrib, BPair.right_distrib d d S, BPair.left_distrib,
      BPair.mul_comm S d]
    exact BPair.oneValue_refl _
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
      refine BPair.add_congr (BPair.oneValue_of_eq ?_) (swap_congr (BPair.oneValue_of_eq ?_))
      · rw [BPair.right_distrib (δ p) (δ p) d, BPair.mul_comm (δ p) d,
          ← BPair.right_distrib d d (δ p), BPair.mul_comm (s * s) ((d + d) * δ p),
          BPair.mul_assoc (d + d) (δ p) (s * s), BPair.mul_comm (δ p) (s * s),
          ← BPair.mul_assoc]
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

/-- The doubled shift against the scaled deficit reads the doubled
count's multiple of the scale against the kernel's linear read. -/
private theorem twoM (n d a b s x : BPair) :
    n * d * (a + b) * (s * x) + n * d * (a + b) * (s * x)
      = (d + d) * s * (n * (a + b) * x) := by
  rw [← BPair.right_distrib, BPair.mul_comm n d, BPair.mul_assoc d n (a + b),
    ← BPair.right_distrib d d (n * (a + b)), BPair.mul_assoc (d + d),
    BPair.mul_assoc (d + d), BPair.mul_left_comm (n * (a + b)) s x]

/-- The six-member reshuffle the assembly's right side collects at:
the deficit's two members pair off and the kernel's read joins the
flat read. -/
private theorem shuffle6 (A B C D E F : BPair) :
    A + B + (C + D) + (E + F) = A + D + (C + E) + (B + F) := by
  rw [← BPair.add_assoc (A + B) C D, ← BPair.add_assoc (A + B + C + D) E F,
    ← BPair.add_assoc (A + D) C E, ← BPair.add_assoc (A + D + C + E) B F,
    BPair.add_right_comm A B C, BPair.add_right_comm (A + C) B D,
    BPair.add_right_comm (A + C + D) B E, BPair.add_right_comm A D C]

/-- `lem:corner`'s assembly, cleared at the scale pair `[n : s]` and
the doubled count: the fold of squares joined to the electric
member's balance partner reads the pencil at the dual representative
less the multiplication `g`, and `g` reads at or beyond the floor
line by the three comparisons — the local square against the
gradient deficit (the doubled count's multiple of the scale's square
against the squares' fold at or below the scaled deficits' squares'
fold less their doubled-count reads), the plaquette terms at the
deficits (`δ_p + χ_p ≡ d`), and the cross read at the scale's
first member with the deviation priced at the covering count (the
kernel's read at the flat read against the pair's multiple of the
deficits' fold) — each plaquette completing its square at the shift
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
    rw [twoM n d a b s (δ p)]
    exact BPair.oneValue_refl _
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
    rw [BPair.left_distrib ((d + d) * (s * s)) d.swap (δ p),
      BPair.add_right_comm (s * δ p * (s * δ p) + ((d + d) * (s * s) * δ p).swap),
      shuffle6]
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.swap_add_null (BPair.oneValue_refl ((d + d) * (s * s) * δ p)))) ?_
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    show ((d + d) * s * (n * a * d) + (d + d) * (s * s) * d.swap).oneValue
      ((d + d) * d * (n * s * a + (s * s).swap))
    rw [BPair.left_distrib ((d + d) * d), BPair.mul_swap, BPair.mul_swap,
      BPair.mul_assoc (d + d) s (n * a * d), BPair.mul_assoc (d + d) d (n * s * a),
      BPair.mul_assoc (d + d) (s * s) d, BPair.mul_assoc (d + d) d (s * s),
      BPair.mul_comm (s * s) d, BPair.mul_comm s (n * a * d),
      BPair.mul_assoc (n * a) d s, BPair.mul_comm (n * a) (d * s),
      BPair.mul_assoc d s (n * a), ← BPair.mul_assoc s n a, BPair.mul_comm s n]
    exact BPair.oneValue_refl _
  refine leB_congr_left (BPair.oneValue_symm hLft) ?_
  refine leB_congr_left hT ?_
  rw [BPair.left_distrib ((d + d) * (s * s)) G2.swap]
  exact leB_add (leB_add h1' (Or.inl (BPair.oneValue_symm h2'))) h3'

/-- `lem:corner`'s cross read at one plaquette and one boundary link:
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

/-- `lem:corner`'s moment identities at the tail read: the parts
identity `m^X_{la} + s_n ν^G_{la} ≡ 1` folded over the generator
index and over the links reads the sum's unit, so each link's
moment fold joined to its leading member `c_l k_d K^T_l μ_Z` — the
link weight's multiple of the remainder and the generator's read of
`Z` — against the gradient fold's link read `c_l (ν^{ZG}_l +
ν^{ZR}_l)` collects, at the weighted folds `ν_Zyy` and `σ`, to the
four collected members against the leading members' own fold
`k_d σ μ_Z`. -/
theorem coord_identity (Lk A : Nat) (c KTu mZr mXZ nuZG nuZR : Nat → BPair)
    (mX nuG : Nat → Nat → BPair) (nuZyy sigma muZ sn kd : BPair)
    (h1 : ∀ l, l < Lk → (bsum (fun a => mX l a) (List.range A) + c l * kd * KTu l * muZ).oneValue
        (c l * (mZr l + mXZ l)))
    (h2 : ∀ l, l < Lk → (bsum (fun a => nuG l a) (List.range A)).oneValue
        (c l * (nuZG l + nuZR l)))
    (h3 : (bsum (fun l => c l * nuZG l) (List.range Lk)).oneValue nuZyy)
    (h4 : (bsum (fun l => c l * KTu l) (List.range Lk)).oneValue sigma)
    (h5 : ∀ l a, l < Lk → a < A → (mX l a + sn * nuG l a).oneValue BPair.unit) :
    (sn * nuZyy + bsum (fun l => c l * mZr l) (List.range Lk)
      + bsum (fun l => c l * mXZ l) (List.range Lk)
      + sn * bsum (fun l => c l * nuZR l) (List.range Lk)).oneValue (kd * sigma * muZ) := by
  -- the parts identity folded over the generator index, one link at a time
  have hInner : ∀ l, l < Lk →
      (bsum (fun a => mX l a) (List.range A)
        + sn * bsum (fun a => nuG l a) (List.range A)).oneValue BPair.unit := by
    intro l hl
    have hnull : (bsum (fun a => mX l a + sn * nuG l a) (List.range A)).oneValue BPair.unit :=
      foldB_nullRange (fun a => mX l a + sn * nuG l a) A (fun a ha => h5 l a hl ha)
    refine BPair.oneValue_trans (BPair.oneValue_symm ?_) hnull
    show (ground.famFold BPair.add BPair.unit (fun a => mX l a + sn * nuG l a)
      (List.range A)).oneValue _
    exact BPair.oneValue_trans
      (famFold_add_ov bpairFoldLaws (fun a => mX l a) (fun a => sn * nuG l a) (List.range A))
      (BPair.add_congr (BPair.oneValue_refl _)
        (foldB_mul_left sn (fun a => nuG l a) (List.range A)))
  -- the leading members' fold at the collected weights
  have hK : (bsum (fun l => c l * kd * KTu l * muZ) (List.range Lk)).oneValue
      (kd * sigma * muZ) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm
      (foldB_mul_right muZ (fun l => c l * kd * KTu l) (List.range Lk))) ?_
    refine BPair.mul_congr_left ?_
    refine BPair.oneValue_trans (bsum_congr_range_ov _
      (fun l => kd * (c l * KTu l)) Lk (fun l _ => ?_)) ?_
    · rw [BPair.mul_comm (c l) kd, BPair.mul_assoc kd (c l) (KTu l)]
      exact BPair.oneValue_refl _
    · exact BPair.oneValue_trans (foldB_mul_left kd (fun l => c l * KTu l) (List.range Lk))
        (BPair.mul_congr (BPair.oneValue_refl kd) h4)
  -- each link's read at the moment and the gradient identities
  have hER : ∀ l, l < Lk →
      (bsum (fun a => mX l a) (List.range A)
        + sn * bsum (fun a => nuG l a) (List.range A)
        + c l * kd * KTu l * muZ).oneValue
      (sn * (c l * nuZG l) + c l * mZr l + c l * mXZ l + sn * (c l * nuZR l)) := by
    intro l hl
    rw [BPair.add_right_comm (bsum (fun a => mX l a) (List.range A))
      (sn * bsum (fun a => nuG l a) (List.range A)) (c l * kd * KTu l * muZ)]
    refine BPair.oneValue_trans
      (BPair.add_congr (h1 l hl) (BPair.mul_congr (BPair.oneValue_refl sn) (h2 l hl))) ?_
    rw [BPair.left_distrib (c l) (mZr l) (mXZ l),
      BPair.left_distrib (c l) (nuZG l) (nuZR l),
      BPair.left_distrib sn (c l * nuZG l) (c l * nuZR l),
      ← BPair.add_assoc (c l * mZr l + c l * mXZ l) (sn * (c l * nuZG l))
        (sn * (c l * nuZR l)),
      BPair.add_right_comm (c l * mZr l) (c l * mXZ l) (sn * (c l * nuZG l)),
      BPair.add_comm (c l * mZr l) (sn * (c l * nuZG l))]
    exact BPair.oneValue_refl _
  -- the links' fold at the leading members withdrawn
  have hE : (bsum (fun l => bsum (fun a => mX l a) (List.range A)
      + sn * bsum (fun a => nuG l a) (List.range A)
      + c l * kd * KTu l * muZ) (List.range Lk)).oneValue (kd * sigma * muZ) := by
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => bsum (fun a => mX l a) (List.range A)
        + sn * bsum (fun a => nuG l a) (List.range A))
      (fun l => c l * kd * KTu l * muZ) (List.range Lk)) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (foldB_nullRange _ Lk hInner) hK) ?_
    exact BPair.unit_add _
  -- the read side's fold splits at the four members
  have hRfold : (bsum (fun l => sn * (c l * nuZG l) + c l * mZr l + c l * mXZ l
      + sn * (c l * nuZR l)) (List.range Lk)).oneValue
      (sn * nuZyy + bsum (fun l => c l * mZr l) (List.range Lk)
        + bsum (fun l => c l * mXZ l) (List.range Lk)
        + sn * bsum (fun l => c l * nuZR l) (List.range Lk)) := by
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => sn * (c l * nuZG l) + c l * mZr l + c l * mXZ l)
      (fun l => sn * (c l * nuZR l)) (List.range Lk)) ?_
    refine BPair.add_congr ?_
      (foldB_mul_left sn (fun l => c l * nuZR l) (List.range Lk))
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => sn * (c l * nuZG l) + c l * mZr l)
      (fun l => c l * mXZ l) (List.range Lk)) ?_
    refine BPair.add_congr ?_ (BPair.oneValue_refl _)
    refine BPair.oneValue_trans (famFold_add_ov bpairFoldLaws
      (fun l => sn * (c l * nuZG l)) (fun l => c l * mZr l) (List.range Lk)) ?_
    refine BPair.add_congr ?_ (BPair.oneValue_refl _)
    exact BPair.oneValue_trans (foldB_mul_left sn (fun l => c l * nuZG l) (List.range Lk))
      (BPair.mul_congr (BPair.oneValue_refl sn) h3)
  refine BPair.oneValue_trans (BPair.oneValue_symm hRfold) ?_
  exact BPair.oneValue_trans (BPair.oneValue_symm (bsum_congr_range_ov _ _ Lk hER)) hE

/-- `lem:corner`'s excess: at the moment's read `r_u μ_1 ≡ T^T +
m_q` with the two members priced at the deficit caps, the flux
moments' fold read at the gradient deficit against the deficits' fold
(`lem:loopcap`'s `|f_p|² ≤ 2 κ δ_p` at every plaquette, folded at the
moments), the caps for `m_D` and `m_D2` entering their coefficient
data, every read cleared at the scale pair `[n : s]` (the scale's cube
at the squares' cap and the slack, its square at the deficit's square
moment and the scale itself at the first-order caps) and the mass
`[e : m]` (the mass's square at the leading summand), the moment `μ_1`
withdrawn at its strict read above the sum's unit and the scale's
first member at or below its second: the excess at the clearing
`s³ m²` sits at or below the leading summand `192 g κ C_D n_p e² n s²`
joined to the coefficient fold `(24 Θ_R K² + 2 c_q K² + 3 C_D n_p +
Ω C_D n_p + W_q) m² n² s`, the substituted members' coefficients `g`,
`κ`, `Θ_R`, `c_q`, `Ω`, `C_D` and `n_p` at or above the sum's unit as
the substitutions' own binders. -/
theorem excess_read (ru TT mq mu1 sf mD mD2 K ThR cq Om Wq CD np g kappa n s e m : BPair)
    (hru : (ru * mu1).oneValue (TT + mq))
    (hTT : TT * (m * m) * (s * s * s) ≤ BPair.ofNat 96 * (g * ((e * e) * sf)) * (s * s * s)
      + BPair.ofNat 12 * (ThR * mD2) * (m * m) * (s * s * s)
      + BPair.ofNat 3 * ((n * n) * mD) * (m * m) * s)
    (hmq : mq * (s * s * s) ≤ cq * mD2 * (s * s * s) + n * Om * mD * (s * s)
      + Wq * (n * n) * mu1 * s)
    (hfp : sf ≤ BPair.ofNat 2 * kappa * mD)
    (hmD : mD * s ≤ CD * np * n * mu1)
    (hmD2 : mD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (n * n) * mu1)
    (hmu : BPair.unit < mu1) (hns : n ≤ s)
    (hn : BPair.unit ≤ n) (hs : BPair.unit ≤ s) (he : BPair.unit ≤ e) (hm : BPair.unit ≤ m)
    (hg : BPair.unit ≤ g) (hkappa : BPair.unit ≤ kappa) (hThR : BPair.unit ≤ ThR)
    (hcq : BPair.unit ≤ cq) (hOm : BPair.unit ≤ Om) (hCD : BPair.unit ≤ CD)
    (hnp : BPair.unit ≤ np) :
    ru * (s * s * s) * (m * m)
      ≤ BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s)
        + (BPair.ofNat 24 * (ThR * (K * K)) + BPair.ofNat 2 * (cq * (K * K))
          + BPair.ofNat 3 * (CD * np) + Om * (CD * np) + Wq) * (m * m) * (n * n) * s := by
  have hmu1 : BPair.unit ≤ mu1 := leB_of_lt hmu
  have hpos2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  -- the flux moments' fold at the gradient deficit against the deficits' fold
  have hsf : sf * s ≤ BPair.ofNat 2 * kappa * (CD * np * n * mu1) :=
    leB_trans (leB_mulL hs hfp)
      (leB_congr_left (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm)
        (leB_mulR (unitLeMul hpos2 hkappa) hmD))
  -- the three cap members at the moments
  have b1 : BPair.ofNat 96 * (g * ((e * e) * sf)) * (s * s * s)
      ≤ BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s) * mu1 := by
    have t := leB_mulL (unitLeMul hs hs)
      (leB_mulR (unitLeMul (unitLeMul (unitLeOfNat 96) hg) (unitLeMul he he)) hsf)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_refl _) ?_ t
    have h1 : BPair.ofNat 96 * g * e * e * BPair.ofNat 2 * kappa * CD * np * n * mu1 * s * s = BPair.ofNat 96 * BPair.ofNat 2 * g * kappa * CD * np * e * e * n * s * s * mu1 := by
      rw [BPair.mul_right_comm (BPair.ofNat 96 * g * e) e (BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 96 * g) e (BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 96) g (BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g * e) e kappa,
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g) e kappa,
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g * kappa * e) e CD,
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g * kappa) e CD,
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g * kappa * CD * e) e np,
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g * kappa * CD) e np,
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g * kappa * CD * np * e * e * n) mu1 s,
        BPair.mul_right_comm (BPair.ofNat 96 * BPair.ofNat 2 * g * kappa * CD * np * e * e * n * s) mu1 s]
    have h4 : BPair.ofNat 192 * g * kappa * CD * np * e * e * n * s * s * mu1 = BPair.ofNat 192 * g * kappa * CD * np * e * e * n * s * s * mu1 := by
      rfl
    exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
      (BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 96 2))))))))))))
      (BPair.oneValue_trans (BPair.oneValue_refl _) (BPair.oneValue_of_eq h4)))
  have b2 : BPair.ofNat 12 * (ThR * mD2) * (m * m) * (s * s * s)
      ≤ BPair.ofNat 24 * (ThR * (K * K)) * (m * m) * (n * n) * s * mu1 := by
    have t := leB_mulL (unitLeMul (unitLeMul hm hm) hs)
      (leB_mulR (unitLeMul (unitLeOfNat 12) hThR) hmD2)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_of_eq ?_) ?_ t
    · rw [BPair.mul_right_comm (BPair.ofNat 12 * ThR * mD2 * s) s m,
        BPair.mul_right_comm (BPair.ofNat 12 * ThR * mD2) s m,
        BPair.mul_right_comm (BPair.ofNat 12 * ThR * mD2 * m * s) s m,
        BPair.mul_right_comm (BPair.ofNat 12 * ThR * mD2 * m) s m]
    · have h1 : BPair.ofNat 12 * ThR * BPair.ofNat 2 * K * K * n * n * mu1 * m * m * s = BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K * m * m * n * n * s * mu1 := by
        rw [BPair.mul_right_comm (BPair.ofNat 12) ThR (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K * n * n) mu1 m,
          BPair.mul_right_comm (BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K * n) n m,
          BPair.mul_right_comm (BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K) n m,
          BPair.mul_right_comm (BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K * m * n * n) mu1 m,
          BPair.mul_right_comm (BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K * m * n) n m,
          BPair.mul_right_comm (BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K * m) n m,
          BPair.mul_right_comm (BPair.ofNat 12 * BPair.ofNat 2 * ThR * K * K * m * m * n * n) mu1 s]
      have h4 : BPair.ofNat 24 * ThR * K * K * m * m * n * n * s * mu1 = BPair.ofNat 24 * ThR * K * K * m * m * n * n * s * mu1 := by
        rfl
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 12 2)))))))))))
        (BPair.oneValue_trans (BPair.oneValue_refl _) (BPair.oneValue_of_eq h4)))
  have b3 : BPair.ofNat 3 * ((n * n) * mD) * (m * m) * s
      ≤ BPair.ofNat 3 * (CD * np) * (m * m) * (n * n) * s * mu1 := by
    have t := leB_mulL (unitLeMul hm hm)
      (leB_mulR (unitLeMul (unitLeOfNat 3) (unitLeMul hn hn)) hmD)
    have t3 := leB_mulL (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
      (unitLeMul (unitLeOfNat 3) hCD) hnp) hm) hm) hn) hn) hmu1) hns
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc] at t3
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left (BPair.oneValue_of_eq ?_) t)
      (leB_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_) t3)
    · rw [BPair.mul_right_comm (BPair.ofNat 3 * n * n * mD) s m,
        BPair.mul_right_comm (BPair.ofNat 3 * n * n * mD * m) s m]
    · rw [BPair.mul_comm n (BPair.ofNat 3),
        BPair.mul_right_comm (BPair.ofNat 3 * n * CD * np * m) m n,
        BPair.mul_right_comm (BPair.ofNat 3 * n * CD * np) m n,
        BPair.mul_right_comm (BPair.ofNat 3 * n * CD) np n,
        BPair.mul_right_comm (BPair.ofNat 3 * n) CD n,
        BPair.mul_right_comm (BPair.ofNat 3 * n * n * CD * np * m) m n,
        BPair.mul_right_comm (BPair.ofNat 3 * n * n * CD * np) m n,
        BPair.mul_right_comm (BPair.ofNat 3 * n * n * CD * np * n * m) m mu1,
        BPair.mul_right_comm (BPair.ofNat 3 * n * n * CD * np * n) m mu1]
    · rw [BPair.mul_comm s (BPair.ofNat 3),
        BPair.mul_right_comm (BPair.ofNat 3) s CD,
        BPair.mul_right_comm (BPair.ofNat 3 * CD) s np,
        BPair.mul_right_comm (BPair.ofNat 3 * CD * np) s m,
        BPair.mul_right_comm (BPair.ofNat 3 * CD * np * m) s m,
        BPair.mul_right_comm (BPair.ofNat 3 * CD * np * m * m) s n,
        BPair.mul_right_comm (BPair.ofNat 3 * CD * np * m * m * n) s n]
  -- the slack's three members at the moments
  have c1 : cq * mD2 * (s * s * s) * (m * m)
      ≤ BPair.ofNat 2 * (cq * (K * K)) * (m * m) * (n * n) * s * mu1 := by
    have t := leB_mulL (unitLeMul hs (unitLeMul hm hm)) (leB_mulR hcq hmD2)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq ?_) t
    rw [BPair.mul_comm cq (BPair.ofNat 2),
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * n * n * mu1) s m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * n * n) mu1 m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * n) n m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K) n m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * m * n * n * mu1) s m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * m * n * n) mu1 m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * m * n) n m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * m) n m,
      BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * m * m * n * n) mu1 s]
  have c2 : n * Om * mD * (s * s) * (m * m) ≤ Om * (CD * np) * (m * m) * (n * n) * s * mu1 := by
    have t := leB_mulL (unitLeMul hs (unitLeMul hm hm)) (leB_mulR (unitLeMul hn hOm) hmD)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq ?_) t
    rw [BPair.mul_comm n Om,
      BPair.mul_right_comm (Om) n CD,
      BPair.mul_right_comm (Om * CD) n np,
      BPair.mul_right_comm (Om * CD * np * n * n * mu1) s m,
      BPair.mul_right_comm (Om * CD * np * n * n) mu1 m,
      BPair.mul_right_comm (Om * CD * np * n) n m,
      BPair.mul_right_comm (Om * CD * np) n m,
      BPair.mul_right_comm (Om * CD * np * m * n * n * mu1) s m,
      BPair.mul_right_comm (Om * CD * np * m * n * n) mu1 m,
      BPair.mul_right_comm (Om * CD * np * m * n) n m,
      BPair.mul_right_comm (Om * CD * np * m) n m,
      BPair.mul_right_comm (Om * CD * np * m * m * n * n) mu1 s]
  have c3 : Wq * (n * n) * mu1 * s * (m * m) = Wq * (m * m) * (n * n) * s * mu1 := by
    repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_right_comm (Wq * n * n * mu1) s m,
      BPair.mul_right_comm (Wq * n * n) mu1 m,
      BPair.mul_right_comm (Wq * n) n m,
      BPair.mul_right_comm (Wq) n m,
      BPair.mul_right_comm (Wq * m * n * n * mu1) s m,
      BPair.mul_right_comm (Wq * m * n * n) mu1 m,
      BPair.mul_right_comm (Wq * m * n) n m,
      BPair.mul_right_comm (Wq * m) n m,
      BPair.mul_right_comm (Wq * m * m * n * n) mu1 s]
  have hmq2 : mq * (s * s * s) * (m * m) ≤ cq * mD2 * (s * s * s) * (m * m)
      + n * Om * mD * (s * s) * (m * m) + Wq * (n * n) * mu1 * s * (m * m) := by
    have t := leB_mulL (unitLeMul hm hm) hmq
    rw [BPair.right_distrib, BPair.right_distrib] at t
    exact t
  -- the six summands' reshuffle, the two square members pairing off
  have hac : ∀ t1 t2 t3 t4 t5 t6 : BPair,
      t1 + t2 + t3 + (t4 + t5 + t6) = t1 + (t2 + t4 + t3 + t5 + t6) := by
    intro t1 t2 t3 t4 t5 t6
    rw [← BPair.add_assoc (t1 + t2 + t3) (t4 + t5) t6,
      ← BPair.add_assoc (t1 + t2 + t3) t4 t5,
      BPair.add_right_comm (t1 + t2) t3 t4,
      ← BPair.add_assoc t1 (t2 + t4 + t3 + t5) t6,
      ← BPair.add_assoc t1 (t2 + t4 + t3) t5,
      ← BPair.add_assoc t1 (t2 + t4) t3,
      ← BPair.add_assoc t1 t2 t4]
  -- the moment's clearing on both sides
  have hL : (mu1 * (ru * (s * s * s) * (m * m))).oneValue
      (TT * (m * m) * (s * s * s) + mq * (s * s * s) * (m * m)) := by
    have e : mu1 * (ru * (s * s * s) * (m * m)) = ru * mu1 * (s * s * s * (m * m)) := by
      rw [BPair.mul_comm mu1, BPair.mul_assoc ru (s * s * s) (m * m),
        BPair.mul_right_comm ru (s * s * s * (m * m)) mu1]
    refine BPair.oneValue_trans (BPair.oneValue_of_eq e) ?_
    refine BPair.oneValue_trans (BPair.mul_congr_left hru) ?_
    rw [BPair.right_distrib]
    refine BPair.add_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_)
    · rw [← BPair.mul_assoc, BPair.mul_right_comm TT (s * s * s) (m * m)]
    · rw [← BPair.mul_assoc]
  have hR : (mu1 * (BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s)
        + (BPair.ofNat 24 * (ThR * (K * K)) + BPair.ofNat 2 * (cq * (K * K))
          + BPair.ofNat 3 * (CD * np) + Om * (CD * np) + Wq) * (m * m) * (n * n) * s)).oneValue
      (BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s) * mu1
        + BPair.ofNat 24 * (ThR * (K * K)) * (m * m) * (n * n) * s * mu1
        + BPair.ofNat 3 * (CD * np) * (m * m) * (n * n) * s * mu1
        + (BPair.ofNat 2 * (cq * (K * K)) * (m * m) * (n * n) * s * mu1
          + Om * (CD * np) * (m * m) * (n * n) * s * mu1
          + Wq * (m * m) * (n * n) * s * mu1)) := by
    rw [BPair.left_distrib,
      BPair.mul_comm mu1 (BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s)),
      BPair.mul_comm mu1 ((BPair.ofNat 24 * (ThR * (K * K)) + BPair.ofNat 2 * (cq * (K * K))
          + BPair.ofNat 3 * (CD * np) + Om * (CD * np) + Wq) * (m * m) * (n * n) * s)]
    repeat rw [BPair.right_distrib]
    rw [hac]
    exact BPair.oneValue_refl _
  refine leB_unscale_left hmu ?_
  refine leB_congr (BPair.oneValue_symm hL) (BPair.oneValue_symm hR) ?_
  exact leB_add (leB_trans hTT (leB_add (leB_add b1 b2) b3))
    (leB_trans hmq2 (leB_add (leB_add c1 c2)
      (leB_congr_right (BPair.oneValue_of_eq c3) (leB_refl _))))

/-- The mode's variance read (`lem:corner`'s mode member, the
chi-square read at `dim G` degrees), cleared at the scale `[n : s]`
and the profile's solve `[sn : sd]`: at the coordinate identity's
two reads, the mode square's moment at the solve against the unit's
and the square's square's against the mode square's, the mode mean
below its moment read and the profile's two reads a scale apart,
the member's self-pairing, the mode's variance cleared at the unit's
moment, sits at or beyond the scale's multiple of the solve against
the two moments at the gap `1 - η (dim G + 2) / 4`, less the
remainders' caps at the scale, every read cleared at four, the
scale's square and the solve's clearing. -/
theorem mode_variance (muQ muQ2 nuQ nuQ2 mu1 K dG n s sn sd r1 r2 R1 R2 : BPair)
    (h1 : (BPair.ofNat 2 * nuQ * s * sd).oneValue (n * (K * dG * sn * mu1 + r1 * sd)))
    (h2 : (BPair.ofNat 2 * nuQ2 * s * sd).oneValue
      (n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd)))
    (h3 : muQ ≤ nuQ)
    (h4 : BPair.ofNat 2 * nuQ2 * s ≤ BPair.ofNat 2 * muQ2 * s + n * nuQ2)
    (hr1 : r1 ≤ R1) (hr2 : r2.swap ≤ R2)
    (hns : n ≤ s) (hn : BPair.unit ≤ n) (hs : BPair.unit ≤ s) (hsd : BPair.unit ≤ sd)
    (hmu1 : BPair.unit ≤ mu1) (hmuQ : BPair.unit ≤ muQ)
    (hR1 : BPair.unit ≤ R1) (hR2 : BPair.unit ≤ R2) :
    BPair.ofNat 4 * n * K * sn * muQ * mu1 * s + BPair.ofNat 4 * muQ * muQ * s * s * sd
      ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd
        + n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1
        + BPair.ofNat 4 * n * s * R2 * sd * mu1 + BPair.ofNat 4 * n * muQ * R1 * sd * s := by
  have h22 : (BPair.ofNat 4).oneValue (BPair.ofNat 2 * BPair.ofNat 2) := BPair.ofNat_mul 2 2
  have hpos2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  -- S1: 4 μQ μQ s s sd ≤ 2 n K dG sn μQ μ1 s + 2 n μQ R1 sd s
  have s1 : BPair.ofNat 4 * muQ * muQ * s * s * sd
      ≤ BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 * s + BPair.ofNat 2 * n * muQ * R1 * sd * s := by
    have a1 : BPair.ofNat 4 * muQ * muQ * s * sd ≤ BPair.ofNat 2 * muQ * (BPair.ofNat 2 * nuQ * s * sd) := by
      have hm : BPair.ofNat 2 * muQ * (BPair.ofNat 2 * muQ * s * sd)
          = BPair.ofNat 2 * BPair.ofNat 2 * muQ * muQ * s * sd := by
        repeat rw [← BPair.mul_assoc]
        rw [BPair.mul_right_comm (BPair.ofNat 2) muQ (BPair.ofNat 2)]
      refine leB_congr_left (BPair.oneValue_trans (BPair.oneValue_of_eq hm)
        (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left
          (BPair.mul_congr_left (BPair.oneValue_symm h22)))))) ?_
      exact leB_mulR (unitLeMul hpos2 hmuQ) (leB_mulL hsd (leB_mulL hs (leB_mulR hpos2 h3)))
    have hm2 : BPair.ofNat 2 * muQ * (n * (K * dG * sn * mu1 + r1 * sd))
        = BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 + BPair.ofNat 2 * n * muQ * r1 * sd := by
      rw [BPair.left_distrib, BPair.left_distrib]
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (BPair.ofNat 2) muQ n,
        BPair.mul_right_comm (BPair.ofNat 2 * n) muQ K,
        BPair.mul_right_comm (BPair.ofNat 2 * n * K) muQ dG,
        BPair.mul_right_comm (BPair.ofNat 2 * n * K * dG) muQ sn]
    have a2 : BPair.ofNat 2 * muQ * (BPair.ofNat 2 * nuQ * s * sd)
        ≤ BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 + BPair.ofNat 2 * n * muQ * R1 * sd :=
      leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) h1) (BPair.oneValue_of_eq hm2)))
        (leB_add (leB_refl _) (leB_mulL hsd (leB_mulR (unitLeMul (unitLeMul hpos2 hn) hmuQ) hr1)))
    have a3 := leB_mulL hs (leB_trans a1 a2)
    rw [BPair.right_distrib] at a3
    exact leB_congr_left (BPair.oneValue_of_eq (BPair.mul_right_comm (BPair.ofNat 4 * muQ * muQ * s) sd s)) a3
  -- S2: 2 n B' μ1 s ≤ 4 μQ2 μ1 s s sd + n n B' μ1 at B' := K (dG+2) sn μQ + r2 sd
  have s2 : BPair.ofNat 2 * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1 * s
      ≤ BPair.ofNat 4 * muQ2 * mu1 * s * s * sd
        + n * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1 := by
    have b1 := leB_mulL (unitLeMul (unitLeMul (unitLeMul hpos2 hmu1) hsd) hs) h4
    rw [BPair.right_distrib] at b1
    have e2l : BPair.ofNat 2 * nuQ2 * s * (BPair.ofNat 2 * mu1 * sd * s)
        = BPair.ofNat 2 * nuQ2 * s * sd * (BPair.ofNat 2 * mu1 * s) := by
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (BPair.ofNat 2 * nuQ2 * s * BPair.ofNat 2) mu1 sd,
        BPair.mul_right_comm (BPair.ofNat 2 * nuQ2 * s) (BPair.ofNat 2) sd]
    have e2r : n * nuQ2 * (BPair.ofNat 2 * mu1 * sd * s)
        = n * (BPair.ofNat 2 * nuQ2 * s * sd) * mu1 := by
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (n * nuQ2 * BPair.ofNat 2 * mu1) sd s,
        BPair.mul_right_comm (n * nuQ2 * BPair.ofNat 2) mu1 s,
        BPair.mul_right_comm (n * nuQ2 * BPair.ofNat 2 * s) mu1 sd,
        BPair.mul_right_comm n nuQ2 (BPair.ofNat 2)]
    have e2m : BPair.ofNat 2 * muQ2 * s * (BPair.ofNat 2 * mu1 * sd * s)
        = BPair.ofNat 2 * BPair.ofNat 2 * muQ2 * mu1 * s * s * sd := by
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (BPair.ofNat 2 * muQ2 * s * BPair.ofNat 2 * mu1) sd s,
        BPair.mul_right_comm (BPair.ofNat 2 * muQ2 * s * BPair.ofNat 2) mu1 s,
        BPair.mul_right_comm (BPair.ofNat 2 * muQ2 * s * BPair.ofNat 2) s mu1,
        BPair.mul_right_comm (BPair.ofNat 2 * muQ2 * s) (BPair.ofNat 2) mu1,
        BPair.mul_right_comm (BPair.ofNat 2 * muQ2) s mu1,
        BPair.mul_right_comm (BPair.ofNat 2 * muQ2 * mu1) s (BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 2 * muQ2) mu1 (BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 2) muQ2 (BPair.ofNat 2)]
    rw [e2l, e2r, e2m] at b1
    refine leB_congr_right (BPair.add_congr (BPair.mul_congr_left (BPair.mul_congr_left
      (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left
        (BPair.oneValue_symm h22)))))) ?_) (leB_congr_left ?_ b1)
    · exact BPair.oneValue_trans (BPair.mul_congr (BPair.mul_congr (BPair.oneValue_refl n) h2)
        (BPair.oneValue_refl mu1)) (BPair.oneValue_of_eq (by rw [← BPair.mul_assoc n n]))
    · refine BPair.oneValue_trans (BPair.mul_congr h2 (BPair.oneValue_refl _))
        (BPair.oneValue_of_eq ?_)
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm n _ (BPair.ofNat 2), BPair.mul_comm n (BPair.ofNat 2)]
  -- the B' terms opened
  have e3a : BPair.ofNat 2 * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1 * s
      = BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
        + BPair.ofNat 2 * n * r2 * sd * mu1 * s := by
    rw [BPair.left_distrib, BPair.right_distrib, BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
  have e3b : n * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1
      = n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 + n * n * r2 * sd * mu1 := by
    rw [BPair.left_distrib, BPair.right_distrib]
    repeat rw [← BPair.mul_assoc]
  have e4 : BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
      = BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 * s
        + BPair.ofNat 2 * n * K * BPair.ofNat 2 * sn * muQ * mu1 * s := by
    rw [BPair.left_distrib, BPair.right_distrib, BPair.right_distrib, BPair.right_distrib,
      BPair.right_distrib]
  have e4' : (BPair.ofNat 2 * n * K * BPair.ofNat 2 * sn * muQ * mu1 * s).oneValue
      (BPair.ofNat 4 * n * K * sn * muQ * mu1 * s) := by
    rw [BPair.mul_right_comm (BPair.ofNat 2 * n) K (BPair.ofNat 2),
      BPair.mul_right_comm (BPair.ofNat 2) n (BPair.ofNat 2)]
    exact BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left
      (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left
        (BPair.oneValue_symm h22))))))
  have hL : BPair.ofNat 4 * n * K * sn * muQ * mu1 * s + BPair.ofNat 4 * muQ * muQ * s * s * sd
      ≤ BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
        + BPair.ofNat 2 * n * muQ * R1 * sd * s := by
    refine leB_trans (leB_add (leB_refl _) s1) ?_
    rw [e4]
    refine leB_congr_right ?_ (leB_refl _)
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.add_congr (BPair.oneValue_refl _) e4') (BPair.oneValue_refl _))
      (BPair.oneValue_of_eq ?_))
    rw [BPair.add_comm (BPair.ofNat 2 * n * K * dG * sn * muQ * mu1 * s), BPair.add_assoc]
  have hee : n * n ≤ BPair.ofNat 2 * n * s :=
    leB_trans (leB_mulR hn hns) (leB_congr_right (BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofNat_two_mul (n * s)))
      (BPair.oneValue_of_eq (BPair.mul_assoc (BPair.ofNat 2) n s).symm))
      (leB_congr_left (BPair.unit_add _) (leB_add (unitLeMul hn hs) (leB_refl _))))
  have hrr : BPair.unit ≤ (r2 + R2) * sd * mu1 := by
    refine unitLeMul (unitLeMul ?_ hsd) hmu1
    have := leB_swapL (X := BPair.unit) (Y := r2) (W := R2)
      (leB_congr_left (BPair.oneValue_symm (BPair.unit_add _)) hr2)
    exact leB_congr_right (BPair.oneValue_of_eq (BPair.add_comm R2 r2)) this
  have f1 : n * n * r2 * sd * mu1
      ≤ BPair.ofNat 2 * n * r2 * sd * mu1 * s + BPair.ofNat 2 * n * s * R2 * sd * mu1 := by
    have hh : n * n * ((r2 + R2) * sd * mu1) ≤ BPair.ofNat 2 * n * s * ((r2 + R2) * sd * mu1) :=
      leB_mulL hrr hee
    have ex : ∀ z : BPair, z * ((r2 + R2) * sd * mu1) = z * r2 * sd * mu1 + z * R2 * sd * mu1 := by
      intro z
      rw [← BPair.mul_assoc, ← BPair.mul_assoc, BPair.left_distrib, BPair.right_distrib,
        BPair.right_distrib]
    rw [ex, ex] at hh
    have perm' : BPair.ofNat 2 * n * s * r2 * sd * mu1 = BPair.ofNat 2 * n * r2 * sd * mu1 * s := by
      rw [BPair.mul_right_comm (BPair.ofNat 2 * n) s r2, BPair.mul_right_comm (BPair.ofNat 2 * n * r2) s sd,
        BPair.mul_right_comm (BPair.ofNat 2 * n * r2 * sd) s mu1]
    rw [perm'] at hh
    refine leB_trans ?_ hh
    exact leB_congr_left (BPair.add_unit _) (leB_add (leB_refl _)
      (unitLeMul (unitLeMul (unitLeMul (unitLeMul hn hn) hR2) hsd) hmu1))
  have f2 : BPair.ofNat 2 * n * muQ * R1 * sd * s ≤ BPair.ofNat 4 * n * muQ * R1 * sd * s :=
    leB_mulL hs (leB_mulL hsd (leB_mulL hR1 (leB_mulL hmuQ (leB_mulL hn (leB_of_lt (ltB_ofNat (by decide)))))))
  have f3 : BPair.unit ≤ BPair.ofNat 2 * n * s * R2 * sd * mu1 :=
    unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul hpos2 hn) hs) hR2) hsd) hmu1
  have hC : (BPair.ofNat 4 * n * s * R2 * sd * mu1).oneValue
      (BPair.ofNat 2 * n * s * R2 * sd * mu1 + BPair.ofNat 2 * n * s * R2 * sd * mu1) := by
    refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left
      (BPair.mul_congr_left (BPair.mul_congr_left (BPair.ofNat_add 2 2)))))) (BPair.oneValue_of_eq ?_)
    rw [BPair.right_distrib, BPair.right_distrib, BPair.right_distrib, BPair.right_distrib,
      BPair.right_distrib]
  have p1 : ∀ W A B C D : BPair, W + (A + B + C + D) = A + W + (B + (C + D)) := by
    intro W A B C D
    rw [← BPair.add_assoc W (A + B + C) D, ← BPair.add_assoc W (A + B) C,
      ← BPair.add_assoc W A B, BPair.add_comm W A, BPair.add_assoc (A + W + B) C D,
      BPair.add_assoc (A + W) B (C + D)]
  have p2 : ∀ X r B c D : BPair, X + r + (B + (c + c + D)) = B + (r + c + (X + D + c)) := by
    intro X r B c D
    rw [BPair.add_comm (X + r), BPair.add_assoc B, BPair.add_assoc c c D,
      BPair.add_comm (c + (c + D)), BPair.add_comm X r, BPair.add_assoc r X,
      ← BPair.add_assoc X c (c + D), BPair.add_comm X c, BPair.add_assoc c X (c + D),
      ← BPair.add_assoc r c, BPair.add_comm c D, ← BPair.add_assoc X D c]
  have hR' : n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 + n * n * r2 * sd * mu1
        + (BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
          + BPair.ofNat 2 * n * muQ * R1 * sd * s)
      ≤ n * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1
        + (BPair.ofNat 4 * muQ2 * mu1 * s * s * sd
          + n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1
          + BPair.ofNat 4 * n * s * R2 * sd * mu1 + BPair.ofNat 4 * n * muQ * R1 * sd * s) := by
    refine leB_congr_right (BPair.oneValue_of_eq (p1 _ _ _ _ _).symm) ?_
    refine leB_trans ?_ (leB_add s2 (leB_refl _))
    rw [e3a]
    refine leB_congr_right (BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr hC (BPair.oneValue_refl _))))
      (BPair.oneValue_of_eq (p2 _ _ _ _ _)))) ?_
    refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_assoc _ _ _))
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (BPair.add_unit _)))))) ?_
    exact leB_add (leB_refl _) (leB_add f1 (leB_add (leB_add (leB_refl _) f2) f3))
  have hWT : n * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 + n * n * r2 * sd * mu1
        + (BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
          + BPair.ofNat 2 * n * muQ * R1 * sd * s)
      = n * n * (K * (dG + BPair.ofNat 2) * sn * muQ + r2 * sd) * mu1
        + (BPair.ofNat 2 * n * K * (dG + BPair.ofNat 2) * sn * muQ * mu1 * s
          + BPair.ofNat 2 * n * muQ * R1 * sd * s) := by
    rw [e3b]
  exact leB_trans hL (leB_cancelL (leB_congr_left (BPair.oneValue_of_eq hWT) hR'))

/-- The mode read (`lem:corner`'s mode member): the member's form
against the floor line reads the squares' cap at the mode weight,
the slack at the mode weight and the mode read at the closed sums,
each at the two deficit moments at the mode weight and the mode
square's deficit moment at the near scale, against the variance read
on the cell, the variance at or beyond half its leading member, and
at the profile's solve floored at the roots' floor; every read
cleared at the scale pair `[n : s]`, the mass `[e : m]`, the
profile's solve `[sn : sd]` and the mode read `[eWn : eWd]`, the
scale's first member at or below its second: the excess per gram at
the clearing `s² m² eWd` sits at or below the mode's frequency read
at the side, `16 κ (L m + 2 e) eWn n s m`, the mass gradient's read
at the mode weight's deficit moment, `384 g κ C_D n_p e² n s eWd`,
and the scale reads' one group at `n² eWd`, `P_v`'s display: the mode
square's deficit term, the mass gradient's near-scale member and the
further caps at the mass's square, every cap displayed. -/
theorem mode_read (rv D N mXQ mZt mZq mZD mZD2 mQD muQ K n s e m g kappa CD np ThR cq Om Wq
    Pp dG eWn eWd W2 Winf2 sn sd L nl rho2 : BPair)
    (hrv : (rv * D).oneValue N)
    (hN : N * (s * s) ≤ BPair.ofNat 2 * (n * n) * mXQ + BPair.ofNat 2 * mZt * (s * s)
      + mZq * (s * s))
    (hXQ : mXQ * eWd ≤ BPair.ofNat 8 * (kappa * kappa) * eWn * W2 * muQ
      + BPair.ofNat 8 * rho2 * nl * Winf2 * mQD * eWd)
    (hQD : mQD * s ≤ BPair.ofNat 2 * K * n * muQ)
    (hZt : mZt * (m * m) * (s * s) ≤ BPair.ofNat 192 * (g * kappa * (e * e) * mZD) * (s * s)
      + BPair.ofNat 12 * (ThR * mZD2) * (m * m) * (s * s)
      + BPair.ofNat 3 * (n * n * mZD) * (m * m))
    (hZq : mZq * (s * s) ≤ cq * mZD2 * (s * s) + n * Om * mZD * s + Wq * (n * n) * D)
    (hZD : mZD * (s * s) ≤ (CD * np * n * s + Pp * (n * n)) * D)
    (hZD2 : mZD2 * (s * s) ≤ BPair.ofNat 2 * (K * K) * (dG + BPair.ofNat 1) * (n * n) * D)
    (hD : n * kappa * sn * muQ ≤ D * s * (BPair.ofNat 2 * sd))
    (hsig : W2 * m * (BPair.ofNat 2 * sd) ≤ sn * (L * m + BPair.ofNat 2 * e))
    (hWinf : Winf2 ≤ W2)
    (hD0 : BPair.unit < D) (hs0 : BPair.unit < s) (hns : n ≤ s)
    (hn : BPair.unit ≤ n) (he : BPair.unit ≤ e) (hm : BPair.unit ≤ m)
    (hkappa : BPair.ofNat 1 ≤ kappa)
    (hg : BPair.unit ≤ g) (hThR : BPair.unit ≤ ThR) (hcq : BPair.unit ≤ cq)
    (hOm : BPair.unit ≤ Om) (hPp : BPair.unit ≤ Pp)
    (heWn : BPair.unit ≤ eWn) (heWd : BPair.unit ≤ eWd) (hW2 : BPair.unit ≤ W2)
    (hsd0 : BPair.unit < sd) (hL : BPair.unit ≤ L) (hnl : BPair.unit ≤ nl)
    (hrho2 : BPair.unit ≤ rho2) (hCD : BPair.unit ≤ CD) (hnp : BPair.unit ≤ np)
    (hK : BPair.unit ≤ K) (hmuQ : BPair.unit ≤ muQ) (hmQD : BPair.unit ≤ mQD) :
    rv * (s * s) * (m * m) * eWd
      ≤ BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m
        + BPair.ofNat 384 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd
        + (BPair.ofNat 32 * (K * rho2 * nl * (L * m + BPair.ofNat 2 * e)) * m
          + BPair.ofNat 384 * (g * kappa * (e * e)) * Pp
          + (BPair.ofNat 48 * (ThR * (K * K) * (dG + BPair.ofNat 1)) + BPair.ofNat 6 * (CD * np + Pp)
            + BPair.ofNat 2 * (cq * (K * K) * (dG + BPair.ofNat 1)) + Om * (CD * np + Pp) + Wq)
            * (m * m)) * (n * n) * eWd := by
  have hpos2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  have hkap : BPair.unit ≤ kappa := leB_trans (unitLeOfNat 1) hkappa
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hL2 : BPair.unit ≤ L * m + BPair.ofNat 2 * e := unitLeAdd (unitLeMul hL hm) (unitLeMul hpos2 he)
  have hD1 : BPair.unit ≤ D := leB_of_lt hD0
  have hc0 : BPair.unit < D * (s * s) := unitLtMul hD0 (unitLtMul hs0 hs0)
  -- the flux read at the scale and the solve: W2 m n κ μQ ≤ (L m + 2 e) D s
  have hcoreK : W2 * m * n * kappa * muQ ≤ (L * m + BPair.ofNat 2 * e) * D * s := by
    have c1 : W2 * m * (BPair.ofNat 2 * sd) * (n * kappa * muQ)
        ≤ sn * (L * m + BPair.ofNat 2 * e) * (n * kappa * muQ) :=
      leB_mulL (unitLeMul (unitLeMul hn hkap) hmuQ) hsig
    have c2 : (L * m + BPair.ofNat 2 * e) * (n * kappa * sn * muQ)
        ≤ (L * m + BPair.ofNat 2 * e) * (D * s * (BPair.ofNat 2 * sd)) := leB_mulR hL2 hD
    have e1 : sn * (L * m + BPair.ofNat 2 * e) * (n * kappa * muQ)
        = (L * m + BPair.ofNat 2 * e) * (n * kappa * sn * muQ) := by
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_comm sn (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (L * m + BPair.ofNat 2 * e) sn n,
        BPair.mul_right_comm ((L * m + BPair.ofNat 2 * e) * n) sn kappa]
    have e2 : W2 * m * (BPair.ofNat 2 * sd) * (n * kappa * muQ)
        = W2 * m * n * kappa * muQ * (BPair.ofNat 2 * sd) := by
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (W2 * m * BPair.ofNat 2) sd n,
        BPair.mul_right_comm (W2 * m) (BPair.ofNat 2) n,
        BPair.mul_right_comm (W2 * m * n * BPair.ofNat 2) sd kappa,
        BPair.mul_right_comm (W2 * m * n) (BPair.ofNat 2) kappa,
        BPair.mul_right_comm (W2 * m * n * kappa * BPair.ofNat 2) sd muQ,
        BPair.mul_right_comm (W2 * m * n * kappa) (BPair.ofNat 2) muQ]
    have e3 : (L * m + BPair.ofNat 2 * e) * (D * s * (BPair.ofNat 2 * sd))
        = (L * m + BPair.ofNat 2 * e) * D * s * (BPair.ofNat 2 * sd) := by
      repeat rw [← BPair.mul_assoc]
    rw [e1] at c1
    have c3 := leB_trans c1 c2
    rw [e2, e3] at c3
    exact leB_unscale (unitLtMul (unitLtNat (by decide)) hsd0) c3
  have hcore : W2 * m * n * muQ ≤ (L * m + BPair.ofNat 2 * e) * D * s :=
    leB_trans (leB_congr_left (BPair.mul_ofNat_one (W2 * m * n * muQ))
      (leB_congr_right (BPair.oneValue_of_eq (BPair.mul_right_comm (W2 * m * n) muQ kappa))
        (leB_mulR (unitLeMul (unitLeMul (unitLeMul hW2 hm) hn) hmuQ) hkappa))) hcoreK
  -- the leading term
  have hA1 : BPair.ofNat 2 * (n * n) * (s * s * (m * m))
        * (BPair.ofNat 8 * (kappa * kappa) * eWn * W2 * muQ)
      ≤ BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m * (D * (s * s)) := by
    have hM : BPair.unit ≤ BPair.ofNat 16 * kappa * eWn * n * s * m * s :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 16) hkap) heWn)
        hn) hs) hm) hs
    have t := leB_mulR hM hcoreK
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · have h1 : BPair.ofNat 16 * kappa * eWn * n * s * m * s * W2 * m * n * kappa * muQ = BPair.ofNat 16 * n * n * s * s * m * m * kappa * kappa * eWn * W2 * muQ := by
        rw [BPair.mul_right_comm (BPair.ofNat 16 * kappa) eWn n,
          BPair.mul_right_comm (BPair.ofNat 16) kappa n,
          BPair.mul_right_comm (BPair.ofNat 16 * n * kappa * eWn * s * m * s * W2) m n,
          BPair.mul_right_comm (BPair.ofNat 16 * n * kappa * eWn * s * m * s) W2 n,
          BPair.mul_right_comm (BPair.ofNat 16 * n * kappa * eWn * s * m) s n,
          BPair.mul_right_comm (BPair.ofNat 16 * n * kappa * eWn * s) m n,
          BPair.mul_right_comm (BPair.ofNat 16 * n * kappa * eWn) s n,
          BPair.mul_right_comm (BPair.ofNat 16 * n * kappa) eWn n,
          BPair.mul_right_comm (BPair.ofNat 16 * n) kappa n,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * kappa) eWn s,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n) kappa s,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * kappa * eWn) m s,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * kappa) eWn s,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s) kappa s,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * s * kappa) eWn m,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * s) kappa m,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * s * m * kappa * eWn) W2 m,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * s * m * kappa) eWn m,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * s * m) kappa m,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * s * m * m * kappa * eWn) W2 kappa,
          BPair.mul_right_comm (BPair.ofNat 16 * n * n * s * s * m * m * kappa) eWn kappa]
      have h4 : BPair.ofNat 2 * BPair.ofNat 8 * n * n * s * s * m * m * kappa * kappa * eWn * W2 * muQ = BPair.ofNat 2 * n * n * s * s * m * m * BPair.ofNat 8 * kappa * kappa * eWn * W2 * muQ := by
        rw [BPair.mul_right_comm (BPair.ofNat 2) (BPair.ofNat 8) n,
          BPair.mul_right_comm (BPair.ofNat 2 * n) (BPair.ofNat 8) n,
          BPair.mul_right_comm (BPair.ofNat 2 * n * n) (BPair.ofNat 8) s,
          BPair.mul_right_comm (BPair.ofNat 2 * n * n * s) (BPair.ofNat 8) s,
          BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * s) (BPair.ofNat 8) m,
          BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * s * m) (BPair.ofNat 8) m]
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 2 8)))))))))))))) (BPair.oneValue_of_eq h4)))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (BPair.ofNat 16 * kappa * eWn * n * s * m) s (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 16 * kappa * eWn * n * s) m (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 16 * kappa * eWn * n) s (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 16 * kappa * eWn) n (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 16 * kappa) eWn (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m) s D]
  -- the mode square's deficit term
  have hA2 : BPair.ofNat 2 * (n * n) * (s * s * (m * m))
        * (BPair.ofNat 8 * rho2 * nl * Winf2 * mQD * eWd)
      ≤ BPair.ofNat 32 * (K * rho2 * nl * (L * m + BPair.ofNat 2 * e)) * m * (n * n) * eWd
          * (D * (s * s)) := by
    have hY : BPair.unit ≤ BPair.ofNat 2 * (n * n) * (s * s * (m * m)) :=
      unitLeMul (unitLeMul hpos2 (unitLeMul hn hn)) (unitLeMul (unitLeMul hs hs) (unitLeMul hm hm))
    have u1 := leB_mulR hY
      (leB_mulL heWd (leB_mulL hmQD (leB_mulR (unitLeMul (unitLeMul (unitLeOfNat 8) hrho2) hnl) hWinf)))
    have hX : BPair.unit ≤ BPair.ofNat 2 * (n * n) * (s * (m * m))
        * (BPair.ofNat 8 * rho2 * nl * W2 * eWd) :=
      unitLeMul (unitLeMul (unitLeMul hpos2 (unitLeMul hn hn)) (unitLeMul hs (unitLeMul hm hm)))
        (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 8) hrho2) hnl) hW2) heWd)
    have u2 := leB_mulR hX hQD
    have hM : BPair.unit ≤ BPair.ofNat 32 * K * rho2 * nl * m * n * n * eWd * s :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul
        (unitLeOfNat 32) hK) hrho2) hnl) hm) hn) hn) heWd) hs
    have t := leB_mulR hM hcore
    repeat rw [← BPair.mul_assoc] at u1
    repeat rw [← BPair.mul_assoc] at u2
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_trans u1 (leB_trans (leB_congr ?_ ?_ u2) (leB_congr_right ?_ t))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m * m * BPair.ofNat 8 * rho2 * nl * W2 * eWd) mQD s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m * m * BPair.ofNat 8 * rho2 * nl * W2) eWd s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m * m * BPair.ofNat 8 * rho2 * nl) W2 s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m * m * BPair.ofNat 8 * rho2) nl s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m * m * BPair.ofNat 8) rho2 s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m * m) (BPair.ofNat 8) s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m) m s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s) m s,
        BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * s * m * m * BPair.ofNat 8 * rho2 * nl * W2) eWd mQD]
    · have h1 : BPair.ofNat 2 * n * n * s * m * m * BPair.ofNat 8 * rho2 * nl * W2 * eWd * BPair.ofNat 2 * K * n * muQ = BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl * m * n * n * eWd * s * W2 * m * n * muQ := by
        rw [BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * m) m (BPair.ofNat 8),
          BPair.mul_right_comm (BPair.ofNat 2 * n * n * s) m (BPair.ofNat 8),
          BPair.mul_right_comm (BPair.ofNat 2 * n * n) s (BPair.ofNat 8),
          BPair.mul_right_comm (BPair.ofNat 2 * n) n (BPair.ofNat 8),
          BPair.mul_right_comm (BPair.ofNat 2) n (BPair.ofNat 8),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n * n * s * m * m * rho2 * nl * W2) eWd (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n * n * s * m * m * rho2 * nl) W2 (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n * n * s * m * m * rho2) nl (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n * n * s * m * m) rho2 (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n * n * s * m) m (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n * n * s) m (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n * n) s (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * n) n (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8) n (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n * n * s * m * m * rho2 * nl * W2) eWd K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n * n * s * m * m * rho2 * nl) W2 K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n * n * s * m * m * rho2) nl K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n * n * s * m * m) rho2 K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n * n * s * m) m K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n * n * s) m K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n * n) s K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * n) n K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2) n K,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * n * n * s * m) m rho2,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * n * n * s) m rho2,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * n * n) s rho2,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * n) n rho2,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K) n rho2,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * n * n * s * m) m nl,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * n * n * s) m nl,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * n * n) s nl,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * n) n nl,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2) n nl,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl * n * n) s m,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl * n) n m,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl) n m,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl * m * n * n * s * m) W2 eWd,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl * m * n * n * s) m eWd,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl * m * n * n) s eWd,
          BPair.mul_right_comm (BPair.ofNat 2 * BPair.ofNat 8 * BPair.ofNat 2 * K * rho2 * nl * m * n * n * eWd * s) m W2]
      have h4 : BPair.ofNat 32 * K * rho2 * nl * m * n * n * eWd * s * W2 * m * n * muQ = BPair.ofNat 32 * K * rho2 * nl * m * n * n * eWd * s * W2 * m * n * muQ := by
        rfl
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 2 8))))))))))))))) (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 16 2)))))))))))))))
        (BPair.oneValue_trans (BPair.oneValue_refl _) (BPair.oneValue_of_eq h4)))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (BPair.ofNat 32 * K * rho2 * nl * m * n * n * eWd) s (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 32 * K * rho2 * nl * m * n * n) eWd (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 32 * K * rho2 * nl * m * n) n (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 32 * K * rho2 * nl * m) n (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 32 * K * rho2 * nl) m (L * m + BPair.ofNat 2 * e),
        BPair.mul_right_comm (BPair.ofNat 32 * K * rho2 * nl * (L * m + BPair.ofNat 2 * e) * m * n * n * eWd) s D]
  -- the squares' cap at the mode weight: the three members
  have hZ : BPair.unit ≤ BPair.ofNat 2 * eWd * (s * s) :=
    unitLeMul (unitLeMul hpos2 heWd) (unitLeMul hs hs)
  have tB := leB_mulR hZ hZt
  rw [BPair.left_distrib, BPair.left_distrib] at tB
  have hB1 : BPair.ofNat 2 * eWd * (s * s) * (BPair.ofNat 192 * (g * kappa * (e * e) * mZD) * (s * s))
      ≤ BPair.ofNat 384 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd * (D * (s * s))
        + BPair.ofNat 384 * (g * kappa * (e * e)) * Pp * (n * n) * eWd * (D * (s * s)) := by
    have hW : BPair.unit ≤ BPair.ofNat 384 * (g * kappa * (e * e)) * eWd * (s * s) :=
      unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 384) (unitLeMul (unitLeMul hg hkap)
        (unitLeMul he he))) heWd) (unitLeMul hs hs)
    have t := leB_mulR hW hZD
    rw [BPair.right_distrib, BPair.left_distrib] at t
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ (BPair.add_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_)) t
    · have h1 : BPair.ofNat 384 * g * kappa * e * e * eWd * s * s * mZD * s * s = BPair.ofNat 384 * eWd * s * s * g * kappa * e * e * mZD * s * s := by
        rw [BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e) e eWd,
          BPair.mul_right_comm (BPair.ofNat 384 * g * kappa) e eWd,
          BPair.mul_right_comm (BPair.ofNat 384 * g) kappa eWd,
          BPair.mul_right_comm (BPair.ofNat 384) g eWd,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd * g * kappa * e) e s,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd * g * kappa) e s,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd * g) kappa s,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd) g s,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd * s * g * kappa * e) e s,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd * s * g * kappa) e s,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd * s * g) kappa s,
          BPair.mul_right_comm (BPair.ofNat 384 * eWd * s) g s]
      have h4 : BPair.ofNat 2 * BPair.ofNat 192 * eWd * s * s * g * kappa * e * e * mZD * s * s = BPair.ofNat 2 * eWd * s * s * BPair.ofNat 192 * g * kappa * e * e * mZD * s * s := by
        rw [BPair.mul_right_comm (BPair.ofNat 2) (BPair.ofNat 192) eWd,
          BPair.mul_right_comm (BPair.ofNat 2 * eWd) (BPair.ofNat 192) s,
          BPair.mul_right_comm (BPair.ofNat 2 * eWd * s) (BPair.ofNat 192) s]
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 2 192))))))))))))) (BPair.oneValue_of_eq h4)))
    · rw [BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * eWd * s) s CD,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * eWd) s CD,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e) eWd CD,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e) e CD,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa) e CD,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * e * e * eWd * s) s np,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * e * e * eWd) s np,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * e * e) eWd np,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * e) e np,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD) e np,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * np * e * e * eWd * s) s n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * np * e * e * eWd) s n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * np * e * e) eWd n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * np * e * e * n) eWd s,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * np * e * e * n * s * eWd * s) s D,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * CD * np * e * e * n * s * eWd) s D]
    · rw [BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * eWd * s) s Pp,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * eWd) s Pp,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e) eWd Pp,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp * eWd * s) s n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp * eWd) s n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp) eWd n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp * n * eWd * s) s n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp * n * eWd) s n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp * n) eWd n,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp * n * n * eWd * s) s D,
        BPair.mul_right_comm (BPair.ofNat 384 * g * kappa * e * e * Pp * n * n * eWd) s D]
  have hB2 : BPair.ofNat 2 * eWd * (s * s) * (BPair.ofNat 12 * (ThR * mZD2) * (m * m) * (s * s))
      ≤ BPair.ofNat 48 * (ThR * (K * K) * (dG + BPair.ofNat 1)) * (m * m) * (n * n) * eWd
        * (D * (s * s)) := by
    have hV : BPair.unit ≤ BPair.ofNat 24 * (ThR * eWd) * (s * s) * (m * m) :=
      unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 24) (unitLeMul hThR heWd)) (unitLeMul hs hs))
        (unitLeMul hm hm)
    have t := leB_mulR hV hZD2
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · have h1 : BPair.ofNat 24 * ThR * eWd * s * s * m * m * mZD2 * s * s = BPair.ofNat 24 * eWd * s * s * ThR * mZD2 * m * m * s * s := by
        rw [BPair.mul_right_comm (BPair.ofNat 24) ThR eWd,
          BPair.mul_right_comm (BPair.ofNat 24 * eWd) ThR s,
          BPair.mul_right_comm (BPair.ofNat 24 * eWd * s) ThR s,
          BPair.mul_right_comm (BPair.ofNat 24 * eWd * s * s * ThR * m) m mZD2,
          BPair.mul_right_comm (BPair.ofNat 24 * eWd * s * s * ThR) m mZD2]
      have h4 : BPair.ofNat 2 * BPair.ofNat 12 * eWd * s * s * ThR * mZD2 * m * m * s * s = BPair.ofNat 2 * eWd * s * s * BPair.ofNat 12 * ThR * mZD2 * m * m * s * s := by
        rw [BPair.mul_right_comm (BPair.ofNat 2) (BPair.ofNat 12) eWd,
          BPair.mul_right_comm (BPair.ofNat 2 * eWd) (BPair.ofNat 12) s,
          BPair.mul_right_comm (BPair.ofNat 2 * eWd * s) (BPair.ofNat 12) s]
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 2 12)))))))))))) (BPair.oneValue_of_eq h4)))
    · have h1 : BPair.ofNat 24 * ThR * eWd * s * s * m * m * BPair.ofNat 2 * K * K * (dG + BPair.ofNat 1) * n * n * D = BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n * n * eWd * D * s * s := by
        rw [BPair.mul_right_comm (BPair.ofNat 24 * ThR * eWd * s * s * m) m (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 24 * ThR * eWd * s * s) m (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 24 * ThR * eWd * s) s (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 24 * ThR * eWd) s (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 24 * ThR) eWd (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 24) ThR (BPair.ofNat 2),
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * eWd * s * s * m) m K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * eWd * s * s) m K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * eWd * s) s K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * eWd) s K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR) eWd K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * eWd * s * s * m) m K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * eWd * s * s) m K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * eWd * s) s K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * eWd) s K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K) eWd K,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * eWd * s * s * m) m (dG + BPair.ofNat 1),
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * eWd * s * s) m (dG + BPair.ofNat 1),
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * eWd * s) s (dG + BPair.ofNat 1),
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * eWd) s (dG + BPair.ofNat 1),
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K) eWd (dG + BPair.ofNat 1),
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * eWd * s) s m,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * eWd) s m,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1)) eWd m,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * eWd * s) s m,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * eWd) s m,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m) eWd m,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * eWd * s) s n,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * eWd) s n,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m) eWd n,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n * eWd * s) s n,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n * eWd) s n,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n) eWd n,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n * n * eWd * s) s D,
          BPair.mul_right_comm (BPair.ofNat 24 * BPair.ofNat 2 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n * n * eWd) s D]
      have h4 : BPair.ofNat 48 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n * n * eWd * D * s * s = BPair.ofNat 48 * ThR * K * K * (dG + BPair.ofNat 1) * m * m * n * n * eWd * D * s * s := by
        rfl
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 24 2))))))))))))))
        (BPair.oneValue_trans (BPair.oneValue_refl _) (BPair.oneValue_of_eq h4)))
  have hB3 : BPair.ofNat 2 * eWd * (s * s) * (BPair.ofNat 3 * (n * n * mZD) * (m * m))
      ≤ BPair.ofNat 6 * (CD * np) * (m * m) * (n * n) * eWd * (D * (s * s))
        + BPair.ofNat 6 * Pp * (m * m) * (n * n) * eWd * (D * (s * s)) := by
    have hU : BPair.unit ≤ BPair.ofNat 6 * (n * n) * (m * m) * eWd :=
      unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 6) (unitLeMul hn hn)) (unitLeMul hm hm)) heWd
    have t := leB_mulR hU hZD
    rw [BPair.right_distrib, BPair.left_distrib] at t
    have hQ1 : BPair.unit ≤ BPair.ofNat 6 * (CD * np) * (n * n) * (m * m) * eWd * D * s :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 6)
        (unitLeMul hCD hnp)) (unitLeMul hn hn)) (unitLeMul hm hm)) heWd) hD1) hs
    have t1 := leB_mulL hQ1 hns
    have hQ2 : BPair.unit ≤ BPair.ofNat 6 * Pp * (n * n) * (m * m) * eWd * D :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 6) hPp)
        (unitLeMul hn hn)) (unitLeMul hm hm)) heWd) hD1
    have t2 := leB_mulR hQ2 (leB_mul_mono hn hs hns hns)
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc] at t1
    repeat rw [← BPair.mul_assoc] at t2
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left ?_ t) (leB_add (leB_congr ?_ ?_ t1) (leB_congr ?_ ?_ t2))
    · have h1 : BPair.ofNat 6 * n * n * m * m * eWd * mZD * s * s = BPair.ofNat 6 * eWd * s * s * n * n * mZD * m * m := by
        rw [BPair.mul_right_comm (BPair.ofNat 6 * n * n * m) m eWd,
          BPair.mul_right_comm (BPair.ofNat 6 * n * n) m eWd,
          BPair.mul_right_comm (BPair.ofNat 6 * n) n eWd,
          BPair.mul_right_comm (BPair.ofNat 6) n eWd,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * n * n * m * m) mZD s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * n * n * m) m s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * n * n) m s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * n) n s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd) n s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * s * n * n * m * m) mZD s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * s * n * n * m) m s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * s * n * n) m s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * s * n) n s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * s) n s,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * s * s * n * n * m) m mZD,
          BPair.mul_right_comm (BPair.ofNat 6 * eWd * s * s * n * n) m mZD]
      have h4 : BPair.ofNat 2 * BPair.ofNat 3 * eWd * s * s * n * n * mZD * m * m = BPair.ofNat 2 * eWd * s * s * BPair.ofNat 3 * n * n * mZD * m * m := by
        rw [BPair.mul_right_comm (BPair.ofNat 2) (BPair.ofNat 3) eWd,
          BPair.mul_right_comm (BPair.ofNat 2 * eWd) (BPair.ofNat 3) s,
          BPair.mul_right_comm (BPair.ofNat 2 * eWd * s) (BPair.ofNat 3) s]
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 2 3))))))))))) (BPair.oneValue_of_eq h4)))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_comm n (BPair.ofNat 6),
        BPair.mul_right_comm (BPair.ofNat 6 * n * CD) np n,
        BPair.mul_right_comm (BPair.ofNat 6 * n) CD n,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * CD * np) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * CD) np m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n) CD m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * CD * np) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * CD) np m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m) CD m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * m * CD * np) n eWd,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * m * CD) np eWd,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * m) CD eWd,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * m * eWd * CD * np * n) D s]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_comm s (BPair.ofNat 6),
        BPair.mul_right_comm (BPair.ofNat 6) s CD,
        BPair.mul_right_comm (BPair.ofNat 6 * CD) s np,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * s * n) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * s) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np) s m,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * m * s * n) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * m * s) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * m) s m,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * m * m) s n,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * m * m * n) s n,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * m * m * n * n) s eWd,
        BPair.mul_right_comm (BPair.ofNat 6 * CD * np * m * m * n * n * eWd) s D]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (BPair.ofNat 6) Pp n,
        BPair.mul_right_comm (BPair.ofNat 6 * n) Pp n,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n) Pp m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m) Pp m,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * m) Pp eWd,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * m * eWd * Pp) D n,
        BPair.mul_right_comm (BPair.ofNat 6 * n * n * m * m * eWd * Pp * n) D n]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (BPair.ofNat 6 * Pp * n) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * Pp) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * Pp * m * n) n m,
        BPair.mul_right_comm (BPair.ofNat 6 * Pp * m) n m]
  -- the slack at the mode weight: the three members
  have hX : BPair.unit ≤ s * s * (m * m) * eWd :=
    unitLeMul (unitLeMul (unitLeMul hs hs) (unitLeMul hm hm)) heWd
  have tC := leB_mulR hX hZq
  rw [BPair.left_distrib, BPair.left_distrib] at tC
  have hC1 : s * s * (m * m) * eWd * (cq * mZD2 * (s * s))
      ≤ BPair.ofNat 2 * (cq * (K * K) * (dG + BPair.ofNat 1)) * (m * m) * (n * n) * eWd
        * (D * (s * s)) := by
    have hQ : BPair.unit ≤ cq * (s * s) * (m * m) * eWd :=
      unitLeMul (unitLeMul (unitLeMul hcq (unitLeMul hs hs)) (unitLeMul hm hm)) heWd
    have t := leB_mulR hQ hZD2
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr ?_ ?_ t
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_comm cq s,
        BPair.mul_right_comm (s) cq s,
        BPair.mul_right_comm (s * s) cq m,
        BPair.mul_right_comm (s * s * m) cq m,
        BPair.mul_right_comm (s * s * m * m) cq eWd]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (cq * s * s * m * m) eWd (BPair.ofNat 2),
        BPair.mul_right_comm (cq * s * s * m) m (BPair.ofNat 2),
        BPair.mul_right_comm (cq * s * s) m (BPair.ofNat 2),
        BPair.mul_right_comm (cq * s) s (BPair.ofNat 2),
        BPair.mul_right_comm (cq) s (BPair.ofNat 2),
        BPair.mul_comm cq (BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 2 * cq * s * s * m * m) eWd K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * s * s * m) m K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * s * s) m K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * s) s K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq) s K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * s * s * m * m) eWd K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * s * s * m) m K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * s * s) m K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * s) s K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K) s K,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * s * s * m * m) eWd (dG + BPair.ofNat 1),
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * s * s * m) m (dG + BPair.ofNat 1),
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * s * s) m (dG + BPair.ofNat 1),
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * s) s (dG + BPair.ofNat 1),
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K) s (dG + BPair.ofNat 1),
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * s) s m,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1)) s m,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * s) s m,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m) s m,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * s * s) eWd n,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * s) s n,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m) s n,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * n * s * s) eWd n,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * n * s) s n,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * n) s n,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * n * n * s) s eWd,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * n * n) s eWd,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * n * n * eWd * s) s D,
        BPair.mul_right_comm (BPair.ofNat 2 * cq * K * K * (dG + BPair.ofNat 1) * m * m * n * n * eWd) s D]
  have hC2 : s * s * (m * m) * eWd * (n * Om * mZD * s)
      ≤ Om * (CD * np) * (m * m) * (n * n) * eWd * (D * (s * s))
        + Om * Pp * (m * m) * (n * n) * eWd * (D * (s * s)) := by
    have hR : BPair.unit ≤ n * Om * s * (m * m) * eWd :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul hn hOm) hs) (unitLeMul hm hm)) heWd
    have t := leB_mulR hR hZD
    rw [BPair.right_distrib, BPair.left_distrib] at t
    have hQ3 : BPair.unit ≤ Om * Pp * (n * n) * (m * m) * eWd * D * s :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul hOm hPp)
        (unitLeMul hn hn)) (unitLeMul hm hm)) heWd) hD1) hs
    have t2 := leB_mulL hQ3 hns
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc] at t2
    repeat rw [← BPair.mul_assoc]
    refine leB_trans (leB_congr_left ?_ t)
      (leB_add (leB_congr_right ?_ (leB_refl _)) (leB_congr ?_ ?_ t2))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (n) Om s,
        BPair.mul_comm n s,
        BPair.mul_right_comm (s * n * Om * m * m * eWd) mZD s,
        BPair.mul_right_comm (s * n * Om * m * m) eWd s,
        BPair.mul_right_comm (s * n * Om * m) m s,
        BPair.mul_right_comm (s * n * Om) m s,
        BPair.mul_right_comm (s * n) Om s,
        BPair.mul_right_comm (s) n s,
        BPair.mul_right_comm (s * s * n) Om m,
        BPair.mul_right_comm (s * s) n m,
        BPair.mul_right_comm (s * s * m * n) Om m,
        BPair.mul_right_comm (s * s * m) n m,
        BPair.mul_right_comm (s * s * m * m * n) Om eWd,
        BPair.mul_right_comm (s * s * m * m) n eWd]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_comm n Om,
        BPair.mul_right_comm (Om * n * s * m * m) eWd CD,
        BPair.mul_right_comm (Om * n * s * m) m CD,
        BPair.mul_right_comm (Om * n * s) m CD,
        BPair.mul_right_comm (Om * n) s CD,
        BPair.mul_right_comm (Om) n CD,
        BPair.mul_right_comm (Om * CD * n * s * m * m) eWd np,
        BPair.mul_right_comm (Om * CD * n * s * m) m np,
        BPair.mul_right_comm (Om * CD * n * s) m np,
        BPair.mul_right_comm (Om * CD * n) s np,
        BPair.mul_right_comm (Om * CD) n np,
        BPair.mul_right_comm (Om * CD * np * n) s m,
        BPair.mul_right_comm (Om * CD * np) n m,
        BPair.mul_right_comm (Om * CD * np * m * n) s m,
        BPair.mul_right_comm (Om * CD * np * m) n m,
        BPair.mul_right_comm (Om * CD * np * m * m * n * s) eWd n,
        BPair.mul_right_comm (Om * CD * np * m * m * n) s n,
        BPair.mul_right_comm (Om * CD * np * m * m * n * n) s eWd,
        BPair.mul_right_comm (Om * CD * np * m * m * n * n * eWd * s) s D,
        BPair.mul_right_comm (Om * CD * np * m * m * n * n * eWd) s D]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (n * Om * Pp * n * n * m * m * eWd) D s,
        BPair.mul_right_comm (n * Om * Pp * n * n * m * m) eWd s,
        BPair.mul_right_comm (n * Om * Pp * n * n * m) m s,
        BPair.mul_right_comm (n * Om * Pp * n * n) m s,
        BPair.mul_right_comm (n * Om * Pp * n) n s,
        BPair.mul_right_comm (n * Om * Pp) n s,
        BPair.mul_right_comm (n * Om) Pp s,
        BPair.mul_right_comm (n * Om * s * Pp * n) n m,
        BPair.mul_right_comm (n * Om * s * Pp) n m,
        BPair.mul_right_comm (n * Om * s) Pp m,
        BPair.mul_right_comm (n * Om * s * m * Pp * n) n m,
        BPair.mul_right_comm (n * Om * s * m * Pp) n m,
        BPair.mul_right_comm (n * Om * s * m) Pp m,
        BPair.mul_right_comm (n * Om * s * m * m * Pp * n) n eWd,
        BPair.mul_right_comm (n * Om * s * m * m * Pp) n eWd,
        BPair.mul_right_comm (n * Om * s * m * m) Pp eWd]
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_comm s Om,
        BPair.mul_right_comm (Om) s Pp,
        BPair.mul_right_comm (Om * Pp * s * n) n m,
        BPair.mul_right_comm (Om * Pp * s) n m,
        BPair.mul_right_comm (Om * Pp) s m,
        BPair.mul_right_comm (Om * Pp * m * s * n) n m,
        BPair.mul_right_comm (Om * Pp * m * s) n m,
        BPair.mul_right_comm (Om * Pp * m) s m,
        BPair.mul_right_comm (Om * Pp * m * m) s n,
        BPair.mul_right_comm (Om * Pp * m * m * n) s n,
        BPair.mul_right_comm (Om * Pp * m * m * n * n) s eWd,
        BPair.mul_right_comm (Om * Pp * m * m * n * n * eWd) s D]
  have hC3 : s * s * (m * m) * eWd * (Wq * (n * n) * D)
      = Wq * (m * m) * (n * n) * eWd * (D * (s * s)) := by
    repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_right_comm (s * s * m * m) eWd Wq,
      BPair.mul_right_comm (s * s * m) m Wq,
      BPair.mul_right_comm (s * s) m Wq,
      BPair.mul_right_comm (s) s Wq,
      BPair.mul_comm s Wq,
      BPair.mul_right_comm (Wq * s) s m,
      BPair.mul_right_comm (Wq) s m,
      BPair.mul_right_comm (Wq * m * s) s m,
      BPair.mul_right_comm (Wq * m) s m,
      BPair.mul_right_comm (Wq * m * m * s * s) eWd n,
      BPair.mul_right_comm (Wq * m * m * s) s n,
      BPair.mul_right_comm (Wq * m * m) s n,
      BPair.mul_right_comm (Wq * m * m * n * s * s) eWd n,
      BPair.mul_right_comm (Wq * m * m * n * s) s n,
      BPair.mul_right_comm (Wq * m * m * n) s n,
      BPair.mul_right_comm (Wq * m * m * n * n * s) s eWd,
      BPair.mul_right_comm (Wq * m * m * n * n) s eWd,
      BPair.mul_right_comm (Wq * m * m * n * n * eWd * s) s D,
      BPair.mul_right_comm (Wq * m * m * n * n * eWd) s D]
  -- the three groups
  have hA : BPair.ofNat 2 * (n * n) * mXQ * (s * s * (m * m) * eWd)
      ≤ BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m * (D * (s * s))
        + BPair.ofNat 32 * (K * rho2 * nl * (L * m + BPair.ofNat 2 * e)) * m * (n * n) * eWd
          * (D * (s * s)) := by
    have hY : BPair.unit ≤ BPair.ofNat 2 * (n * n) * (s * s * (m * m)) :=
      unitLeMul (unitLeMul hpos2 (unitLeMul hn hn)) (unitLeMul (unitLeMul hs hs) (unitLeMul hm hm))
    have t := leB_mulR hY hXQ
    rw [BPair.left_distrib] at t
    refine leB_trans (leB_congr_left (BPair.oneValue_of_eq ?_) t) (leB_add hA1 hA2)
    repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * s * m) m mXQ,
      BPair.mul_right_comm (BPair.ofNat 2 * n * n * s * s) m mXQ,
      BPair.mul_right_comm (BPair.ofNat 2 * n * n * s) s mXQ,
      BPair.mul_right_comm (BPair.ofNat 2 * n * n) s mXQ]
  have hB : BPair.ofNat 2 * mZt * (s * s) * (s * s * (m * m) * eWd)
      ≤ (BPair.ofNat 384 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd * (D * (s * s))
          + BPair.ofNat 384 * (g * kappa * (e * e)) * Pp * (n * n) * eWd * (D * (s * s)))
        + BPair.ofNat 48 * (ThR * (K * K) * (dG + BPair.ofNat 1)) * (m * m) * (n * n) * eWd
          * (D * (s * s))
        + (BPair.ofNat 6 * (CD * np) * (m * m) * (n * n) * eWd * (D * (s * s))
          + BPair.ofNat 6 * Pp * (m * m) * (n * n) * eWd * (D * (s * s))) := by
    refine leB_trans (leB_congr_left (BPair.oneValue_of_eq ?_) tB) (leB_add (leB_add hB1 hB2) hB3)
    repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_right_comm (BPair.ofNat 2 * eWd * s) s mZt,
      BPair.mul_right_comm (BPair.ofNat 2 * eWd) s mZt,
      BPair.mul_right_comm (BPair.ofNat 2) eWd mZt,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt) eWd s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s) eWd s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s * eWd * m) m s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s * eWd) m s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s) eWd s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s * s * eWd * m) m s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s * s * eWd) m s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s * s) eWd s,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s * s * s) eWd m,
      BPair.mul_right_comm (BPair.ofNat 2 * mZt * s * s * s * s * m) eWd m]
  have hC : mZq * (s * s) * (s * s * (m * m) * eWd)
      ≤ BPair.ofNat 2 * (cq * (K * K) * (dG + BPair.ofNat 1)) * (m * m) * (n * n) * eWd
          * (D * (s * s))
        + (Om * (CD * np) * (m * m) * (n * n) * eWd * (D * (s * s))
          + Om * Pp * (m * m) * (n * n) * eWd * (D * (s * s)))
        + Wq * (m * m) * (n * n) * eWd * (D * (s * s)) := by
    refine leB_trans (leB_congr_left (BPair.oneValue_of_eq ?_) tC)
      (leB_add (leB_add hC1 hC2) (leB_congr_right (BPair.oneValue_of_eq hC3) (leB_refl _)))
    repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_right_comm (s * s * m * m) eWd mZq,
      BPair.mul_right_comm (s * s * m) m mZq,
      BPair.mul_right_comm (s * s) m mZq,
      BPair.mul_right_comm (s) s mZq,
      BPair.mul_comm s mZq,
      BPair.mul_right_comm (mZq * s * s * m * m) eWd s,
      BPair.mul_right_comm (mZq * s * s * m) m s,
      BPair.mul_right_comm (mZq * s * s) m s,
      BPair.mul_right_comm (mZq * s * s * s * m * m) eWd s,
      BPair.mul_right_comm (mZq * s * s * s * m) m s,
      BPair.mul_right_comm (mZq * s * s * s) m s]
  -- the assembly at the clearing D s², the excess against the members joined
  have hN2 := leB_mulL hX hN
  rw [BPair.right_distrib, BPair.right_distrib] at hN2
  have hsum := leB_trans hN2 (leB_add (leB_add hA hB) hC)
  have hL' : (rv * (s * s) * (m * m) * eWd * (D * (s * s))).oneValue
      (N * (s * s) * (s * s * (m * m) * eWd)) := by
    have e : rv * (s * s) * (m * m) * eWd * (D * (s * s)) = rv * D * (s * s) * (s * s * (m * m) * eWd) := by
      repeat rw [← BPair.mul_assoc]
      rw [BPair.mul_right_comm (rv * s * s * m * m) eWd D,
        BPair.mul_right_comm (rv * s * s * m) m D,
        BPair.mul_right_comm (rv * s * s) m D,
        BPair.mul_right_comm (rv * s) s D,
        BPair.mul_right_comm (rv) s D,
        BPair.mul_right_comm (rv * D * s * s * m * m) eWd s,
        BPair.mul_right_comm (rv * D * s * s * m) m s,
        BPair.mul_right_comm (rv * D * s * s) m s,
        BPair.mul_right_comm (rv * D * s * s * s * m * m) eWd s,
        BPair.mul_right_comm (rv * D * s * s * s * m) m s,
        BPair.mul_right_comm (rv * D * s * s * s) m s]
    exact BPair.oneValue_trans (BPair.oneValue_of_eq e)
      (BPair.mul_congr_left (BPair.mul_congr_left hrv))
  refine leB_unscale hc0 (leB_congr (BPair.oneValue_symm hL') ?_ hsum)
  repeat rw [BPair.right_distrib]
  rw [BPair.left_distrib (BPair.ofNat 6), BPair.left_distrib Om]
  repeat rw [BPair.right_distrib]
  repeat rw [← BPair.mul_assoc]
  repeat rw [← BPair.add_assoc]
  rw [BPair.add_right_comm
    (BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m * D * s * s)
    (BPair.ofNat 32 * K * rho2 * nl * (L * m + BPair.ofNat 2 * e) * m * n * n * eWd * D * s * s)
    (BPair.ofNat 384 * g * kappa * CD * np * e * e * n * s * eWd * D * s * s)]
  exact BPair.oneValue_refl _

/-- `lem:corner`'s cap and key at one scale: the excess and the mode
read joined, the reads' sum at or below `η (16 κ (L + 2ε) e_W + 576
g κ C_D n_p ε² + (P_u + P_v) η)` (the excess at the mode read's
clearing, the two mass reads' coefficients joined at `192 + 384`),
and at the three key comparisons, the side's `64 κ (L + 2) e_W < φ`,
the mass's `2304 g κ C_D n_p ε² < φ` and the scale's
`4 (P_u + P_v) η < φ`, each at its pair cross-multiplied, with the
mass at or below one: the reads' sum sits under three quarters of the
floor's multiple of the scale, `r_u + r_v < η φ`, read at the
clearing `s fd` against `n fn`; every datum cleared at the scale pair
`[n : s]`, the mass `[e : m]`, the mode read `[eWn : eWd]` and the
floor pair `[fn : fd]`, with `P_u` and `P_v` the two scale reads'
coefficients at the mass's clearing. -/
theorem key_quarters (ru rv Pu Pv g kappa CD np e m n s eWn eWd L fn fd : BPair)
    (hru : ru * (s * s * s) * (m * m)
      ≤ BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * (s * s) + Pu * (n * n) * s)
    (hrv : rv * (s * s) * (m * m) * eWd
      ≤ BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m
        + BPair.ofNat 384 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd
        + Pv * (n * n) * eWd)
    (hside : BPair.ofNat 64 * kappa * (L + BPair.ofNat 2) * eWn * fd < fn * eWd)
    (hmass : BPair.ofNat 2304 * (g * kappa * (CD * np)) * (e * e) * fd < fn * (m * m))
    (hscale : BPair.ofNat 4 * (Pu + Pv) * n * fd < fn * s * (m * m))
    (hem : e ≤ m) (hn0 : BPair.unit < n) (hs0 : BPair.unit < s) (hm0 : BPair.unit < m)
    (heWd0 : BPair.unit < eWd) (hfd : BPair.unit ≤ fd) (hfn : BPair.unit ≤ fn)
    (hkappa : BPair.unit ≤ kappa) (heWn : BPair.unit ≤ eWn) :
    (ru + rv) * s * fd < n * fn := by
  have hpos2 : BPair.unit ≤ BPair.ofNat 2 := unitLeOfNat 2
  have hn : BPair.unit ≤ n := leB_of_lt hn0
  have hs : BPair.unit ≤ s := leB_of_lt hs0
  have hm : BPair.unit ≤ m := leB_of_lt hm0
  have heWd : BPair.unit ≤ eWd := leB_of_lt heWd0
  have hC0 : BPair.unit < s * s * (m * m) * eWd :=
    unitLtMul (unitLtMul (unitLtMul hs0 hs0) (unitLtMul hm0 hm0)) heWd0
  have hC : BPair.unit ≤ s * s * (m * m) * eWd := leB_of_lt hC0
  have hFc : BPair.unit ≤ fn * (n * (s * s) * (m * m) * eWd) :=
    unitLeMul hfn (unitLeMul (unitLeMul (unitLeMul hn (unitLeMul hs hs)) (unitLeMul hm hm)) heWd)
  -- the excess at the mode read's clearing
  have hru' : ru * (s * s) * (m * m) * eWd
      ≤ BPair.ofNat 192 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd + Pu * (n * n) * eWd := by
    have t := leB_mulL heWd hru
    rw [BPair.right_distrib] at t
    refine leB_unscale hs0 ?_
    rw [BPair.right_distrib]
    repeat rw [← BPair.mul_assoc] at t
    repeat rw [← BPair.mul_assoc]
    refine leB_congr (BPair.oneValue_of_eq ?_)
      (BPair.add_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_)) t
    · rw [BPair.mul_right_comm (ru * s * s) s m,
        BPair.mul_right_comm (ru * s * s * m) s m,
        BPair.mul_right_comm (ru * s * s * m * m) s eWd]
    · rw [BPair.mul_right_comm (BPair.ofNat 192 * g * kappa * CD * np * e * e * n * s) s eWd]
    · rw [BPair.mul_right_comm (Pu * n * n) s eWd]
  -- the reads' sum at the cap: the excess and the mode read joined
  have hsum : (ru + rv) * (s * s) * (m * m) * eWd
      ≤ BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m
        + BPair.ofNat 576 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd
        + (Pu + Pv) * (n * n) * eWd := by
    have t := leB_add hru' hrv
    have hac5 : ∀ a b c d f : BPair, a + b + (c + d + f) = c + (a + d) + (b + f) := by
      intro a b c d f
      repeat rw [← BPair.add_assoc]
      rw [BPair.add_right_comm (a) (b) (c),
        BPair.add_comm (a) (c),
        BPair.add_right_comm (c + a) (b) (d)]
    have reg : ∀ k : BPair, k * (g * kappa * (CD * np)) * (e * e) * n * s * eWd
        = k * (g * kappa * (CD * np) * (e * e) * n * s * eWd) := by
      intro k
      repeat rw [← BPair.mul_assoc]
    rw [hac5] at t
    refine leB_congr (BPair.oneValue_of_eq ?_) (BPair.add_congr (BPair.add_congr
      (BPair.oneValue_refl _) ?_) (BPair.oneValue_of_eq ?_)) t
    · rw [BPair.right_distrib, BPair.right_distrib, BPair.right_distrib]
    · rw [reg (BPair.ofNat 192), reg (BPair.ofNat 384), reg (BPair.ofNat 576),
        ← BPair.right_distrib]
      exact BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_add 192 384))
    · rw [BPair.right_distrib, BPair.right_distrib]
  -- the three quarters, each strictly under the floor's multiple of the clearing
  have t1 : BPair.ofNat 4 * (BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m)
        * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd) := by
    have hL2m : L * m + BPair.ofNat 2 * e ≤ (L + BPair.ofNat 2) * m := by
      rw [BPair.right_distrib]
      exact leB_add (leB_refl _) (leB_mulR hpos2 hem)
    have hb := ltB_mulPos hside (unitLtMul hn0 (unitLtMul (unitLtMul hs0 hs0) (unitLtMul hm0 hm0)))
    have hq : BPair.unit ≤ BPair.ofNat 64 * kappa * eWn * fd * n * s * s * m :=
      unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeMul (unitLeOfNat 64)
        hkappa) heWn) hfd) hn) hs) hs) hm
    have u := leB_mulR hq hL2m
    repeat rw [← BPair.mul_assoc] at u
    repeat rw [← BPair.mul_assoc] at hb
    repeat rw [← BPair.mul_assoc]
    refine leB_ltB_trans (leB_congr ?_ ?_ u) (BPair.lt_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq ?_) hb)
    · have h1 : BPair.ofNat 64 * kappa * eWn * fd * n * s * s * m * (L * m + BPair.ofNat 2 * e) = BPair.ofNat 64 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m * s * fd := by
        rw [BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd * n * s * s) m (L * m + BPair.ofNat 2 * e),
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd * n * s) s (L * m + BPair.ofNat 2 * e),
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd * n) s (L * m + BPair.ofNat 2 * e),
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd) n (L * m + BPair.ofNat 2 * e),
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn) fd (L * m + BPair.ofNat 2 * e),
          BPair.mul_right_comm (BPair.ofNat 64 * kappa) eWn (L * m + BPair.ofNat 2 * e),
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * (L * m + BPair.ofNat 2 * e) * eWn) fd n,
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n) fd s,
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * fd) s m,
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s) fd m,
          BPair.mul_right_comm (BPair.ofNat 64 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m) fd s]
      have h4 : BPair.ofNat 4 * BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m * s * fd = BPair.ofNat 4 * BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m * s * fd := by
        rfl
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 4 16))))))))))) (BPair.oneValue_of_eq h4)))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd * n * s * s) m (L + BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd * n * s) s (L + BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd * n) s (L + BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn * fd) n (L + BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 64 * kappa * eWn) fd (L + BPair.ofNat 2),
        BPair.mul_right_comm (BPair.ofNat 64 * kappa) eWn (L + BPair.ofNat 2)]
    · rw [BPair.mul_right_comm (fn) eWd n,
        BPair.mul_right_comm (fn * n) eWd s,
        BPair.mul_right_comm (fn * n * s) eWd s,
        BPair.mul_right_comm (fn * n * s * s) eWd m,
        BPair.mul_right_comm (fn * n * s * s * m) eWd m]
  have t2 : BPair.ofNat 4 * (BPair.ofNat 576 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd)
        * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd) := by
    have hb := ltB_mulPos hmass (unitLtMul hn0 (unitLtMul (unitLtMul hs0 hs0) heWd0))
    repeat rw [← BPair.mul_assoc] at hb
    repeat rw [← BPair.mul_assoc]
    refine BPair.lt_congr ?_ (BPair.oneValue_of_eq ?_) hb
    · have h1 : BPair.ofNat 2304 * g * kappa * CD * np * e * e * fd * n * s * s * eWd = BPair.ofNat 2304 * g * kappa * CD * np * e * e * n * s * eWd * s * fd := by
        rw [BPair.mul_right_comm (BPair.ofNat 2304 * g * kappa * CD * np * e * e) fd n,
          BPair.mul_right_comm (BPair.ofNat 2304 * g * kappa * CD * np * e * e * n) fd s,
          BPair.mul_right_comm (BPair.ofNat 2304 * g * kappa * CD * np * e * e * n * s * fd) s eWd,
          BPair.mul_right_comm (BPair.ofNat 2304 * g * kappa * CD * np * e * e * n * s) fd eWd,
          BPair.mul_right_comm (BPair.ofNat 2304 * g * kappa * CD * np * e * e * n * s * eWd) fd s]
      have h4 : BPair.ofNat 4 * BPair.ofNat 576 * g * kappa * CD * np * e * e * n * s * eWd * s * fd = BPair.ofNat 4 * BPair.ofNat 576 * g * kappa * CD * np * e * e * n * s * eWd * s * fd := by
        rfl
      exact BPair.oneValue_trans (BPair.oneValue_of_eq h1)
        (BPair.oneValue_trans (BPair.oneValue_refl _)
        (BPair.oneValue_trans (BPair.oneValue_symm (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.mul_congr_left (BPair.oneValue_symm (BPair.ofNat_mul 4 576)))))))))))))) (BPair.oneValue_of_eq h4)))
    · rw [BPair.mul_right_comm (fn * m) m n,
        BPair.mul_right_comm (fn) m n,
        BPair.mul_right_comm (fn * n * m) m s,
        BPair.mul_right_comm (fn * n) m s,
        BPair.mul_right_comm (fn * n * s * m) m s,
        BPair.mul_right_comm (fn * n * s) m s]
  have t3 : BPair.ofNat 4 * ((Pu + Pv) * (n * n) * eWd) * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd) := by
    have hb := ltB_mulPos hscale (unitLtMul hn0 (unitLtMul hs0 heWd0))
    repeat rw [← BPair.mul_assoc] at hb
    repeat rw [← BPair.mul_assoc]
    refine BPair.lt_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_) hb
    · rw [BPair.mul_right_comm (BPair.ofNat 4 * (Pu + Pv) * n) fd n,
        BPair.mul_right_comm (BPair.ofNat 4 * (Pu + Pv) * n * n * fd) s eWd,
        BPair.mul_right_comm (BPair.ofNat 4 * (Pu + Pv) * n * n) fd eWd,
        BPair.mul_right_comm (BPair.ofNat 4 * (Pu + Pv) * n * n * eWd) fd s]
    · rw [BPair.mul_right_comm (fn * s * m) m n,
        BPair.mul_right_comm (fn * s) m n,
        BPair.mul_right_comm (fn) s n,
        BPair.mul_right_comm (fn * n * s * m) m s,
        BPair.mul_right_comm (fn * n * s) m s]
  -- the sum under three quarters, under the whole
  have hR : BPair.ofNat 4 * (BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m
        + BPair.ofNat 576 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd
        + (Pu + Pv) * (n * n) * eWd) * (s * fd)
      < BPair.ofNat 4 * (fn * (n * (s * s) * (m * m) * eWd)) := by
    rw [BPair.left_distrib, BPair.left_distrib, BPair.right_distrib, BPair.right_distrib]
    have h3 := ltB_add (ltB_add t1 (leB_of_lt t2)) (leB_of_lt t3)
    refine ltB_trans_le h3 ?_
    have e4 : (BPair.ofNat 4 * (fn * (n * (s * s) * (m * m) * eWd))).oneValue
        (fn * (n * (s * s) * (m * m) * eWd) + fn * (n * (s * s) * (m * m) * eWd)
          + (fn * (n * (s * s) * (m * m) * eWd) + fn * (n * (s * s) * (m * m) * eWd))) := by
      refine BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofNat_add 2 2)) ?_
      rw [BPair.right_distrib]
      exact BPair.add_congr (BPair.ofNat_two_mul _) (BPair.ofNat_two_mul _)
    refine leB_congr_right (BPair.oneValue_symm e4) ?_
    exact leB_add (leB_refl _) (leB_congr_left (BPair.add_unit _) (leB_add (leB_refl _) hFc))
  have h4 : (BPair.ofNat 16 * kappa * (L * m + BPair.ofNat 2 * e) * eWn * n * s * m
        + BPair.ofNat 576 * (g * kappa * (CD * np)) * (e * e) * n * s * eWd
        + (Pu + Pv) * (n * n) * eWd) * (s * fd)
      < fn * (n * (s * s) * (m * m) * eWd) := by
    have c4 : ∀ X Y : BPair, BPair.ofNat 4 * X * Y = X * Y * BPair.ofNat 4 := fun X Y => by
      rw [BPair.mul_comm (BPair.ofNat 4) X, BPair.mul_right_comm X (BPair.ofNat 4) Y]
    refine ltB_unscale (unitLeOfNat 4) ?_
    exact BPair.lt_congr (BPair.oneValue_of_eq (c4 _ _))
      (BPair.oneValue_of_eq (BPair.mul_comm _ _)) hR
  -- the clearing withdrawn
  have h5 := leB_ltB_trans (leB_mulL (unitLeMul hs hfd) hsum) h4
  refine ltB_unscale hC ?_
  refine BPair.lt_congr (BPair.oneValue_of_eq ?_) (BPair.oneValue_of_eq ?_) h5
  · repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_right_comm ((ru + rv) * s * s * m * m * eWd) s fd,
      BPair.mul_right_comm ((ru + rv) * s * s * m * m) eWd fd,
      BPair.mul_right_comm ((ru + rv) * s * s * m) m fd,
      BPair.mul_right_comm ((ru + rv) * s * s) m fd,
      BPair.mul_right_comm ((ru + rv) * s) s fd,
      BPair.mul_right_comm ((ru + rv) * s * fd * s * m * m) eWd s,
      BPair.mul_right_comm ((ru + rv) * s * fd * s * m) m s,
      BPair.mul_right_comm ((ru + rv) * s * fd * s) m s]
  · repeat rw [← BPair.mul_assoc]
    rw [BPair.mul_comm fn n]

end corner
