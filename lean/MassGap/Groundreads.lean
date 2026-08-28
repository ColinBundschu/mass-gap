import MassGap.Greenprod
import MassGap.Spectator
import MassGap.Truncation
import MassGap.Coeff
import MassGap.Momentform
/-!
`thm:groundreads` — the ground reads are bracketed.

Clause (i): a ground read is a stage read.  The ground `ψ` is the
diagonalizing congruence's column at the kernel root (`lem:split`'s
eigen column at the root at the sum's unit), and at an observable `A`
the read enters as the pair of the two pairings `⟨ψ, A ψ⟩` against the
gram's `⟨ψ, G ψ⟩` (`read`), its value the cofactor (`def:ground`),
`def:pencil`'s `ω` at the unit gram; the column is a kernel vector off
the unit family with its self-pairing above the sum's unit
(`ground_column`), and two reads' gap is the cross-multiplied
difference (`readGap`).

Clause (iii): the ground transport.  At two pencils on one head at the
unit gram, the earlier gap `Et` diagonalized with the ground simple at
the flat window's clearance `γ'` — every further root at or beyond it —
and the later gap `Es = Et + D` at a datum `D` capped two-sidedly at
`w` (`thm:truncation`'s cap at the unit gram), the later ground's part
off the earlier line, `lem:lowerspan`'s product-scaled residual at the
one-member list `[ψ]`, obeys `γ'² ⟨φ, φ⟩ ≤ w² ⟨ψ̃, ψ̃⟩` at the residual's
clearing `⟨ψ, ψ⟩` (`transport_offLine`): the earlier gap prices the
off-line part at the clearance on the kernel column's complement
(`gap_perp` at the clearance read `clearRead`, every root off the
kernel root at or beyond the level, the diagonalizing congruence's fold
at those roots), the pencil identity reads `Et φ` as `−⟨ψ,ψ⟩ D ψ̃`, and the
cap's polarization at the cofactor pair `[w : γ']` closes.  The width
of the bracket holding the two grounds' reads of an observable at the
head cap `c_A` then reads `γ' w_ω ≤ 4 c_A w`
(`transport_read`): the reads' pairing members collect to three
off-line terms, each polarized at the cofactor pair.

Clause (ii): the tail rides the transfer factors.  At the ground root
the kernel rows of the slab split close from the far end,
`X_{i+1} ψ_{i+1} + B_iᵀ ψ_i` the sum's unit per row (`lem:greenprod`(iii)'s
row read), the tail pivots of unequal-membered determinant, so a
depth-`j` component is a `j`-fold transfer image (`kernel_tele`, the
ascending telescope at the tail witnesses from the kernel rows at unit
sides: the far row closes at the last pivot, each earlier row withdraws
the next slab's transfer image, and the next pivot's nonsingularity
reads the slab's own image off it); its weight is capped geometrically
at the transfer factor's certificate (`weight_step`, `lem:spectator`(ii)'s
`Tᵀ Gᵢ T ⪯ λ² Gₛ` read at the image against the two slabs' own grams, the
factor rectangular and the certificate's split at the source slab's order,
priced at every vector), and the certificates' product prices every deeper
component against the head's (`weight_chain` along the ascending telescope
at the certificate list `capList` over the gram list
`greenprod.gramShape` — one gram per slab, the gram's slab blocks at
the split, the cross blocks vacant at `def:carrier`'s orthogonal sum
— the products `prodN` and `prodD` the chain's two clearings).  The
ground's head components concatenate cross-cleared
(`headVec` at the joined clearing `denProd`) and solve the head
decimated onto the depths at or below any stated depth, every row the
sum's unit (`head_kernel`, the leading rows at their own kernel row
reads and the pivot's row at the walk's own); the full read extends the
head pair by the tail weight at the clearing scales, the extended gap's
magnitude split by subadditivity (`readGap_extend`), and the tail
weights beyond a depth sum cross-cleared at the slabs' own grams
(`tailSum`) and are priced geometrically by the certificates' Horner fold
(`tailFold`,
`tail_price`).

Clause (iv): the separated reads cluster.  The connected datum is
the probe's image off the ground line (`elim.residD` at the
one-member family), two residuals pair at the cross Gram
determinant (`offLine_cross`), and the rearrangement at the
gram-symmetric multiplications reads the joint cofactor against
the squared self-pairing as the reads' product joined to the
connected pairing (`connected_split`).  At the level gap's tie
`Ẽ ~ ε δₙ E − ε δ_d M − ε₀ G` on `lem:dualtrunc`'s site datum, with
the ground in the gap's kernel and the word's products with the
magnetic member at one value in either order (`prop:algebra`'s
commuting), the word's off-line residual solves the pencil sourced
at the electric commutator, `Ẽ φ ~ ⟨ψ,ψ⟩ ε δₙ [E, f] ψ`
(`sourced_pencil` at `def:pencil`'s level gap, the source's reach
`lem:stableentries`').  The source's slab support hands the walk the
descending telescope (`source_tele`: the head recursion's rows at the
source's own support walk the solved witnesses down to the sourced
slab, the slab a slab of the split, `jb < |us|` the frame); the
descending certificate list pairs each transfer factor against the
image and source grams (`capListDown`, `lem:spectator`(ii)'s read at
the descending pairing), and the weight at the head's side rides the
products through the `j` separating slabs at the certificates against
the crossing clearings, anchored at the sourced slab's block weight
(`ride_price`); the clearance prices the off-line vector at the
sourced identity through the dot polarization (`source_weight` at
`elim.dotN_polar`); and the connected pairing is that weight at the
head observable's cap, the observable padded onto the head width
(`inertia.headPad`) with the cap's polarization closing it
(`cluster_read` at `truncation.cap_polar`): the two reads read one
value within the bracket the crossing certificates and the clearance
price, geometric in the separation.

Clause (v): the Euclidean brackets.  At a pair `u` and the level
gap's diagonalizing certificate, the certificate fold (`eucRead`)
reads every root at the kernel arm's full gap or at the positive
arm's representative, gap witness and cap against the largest gap
(`eucRead_at`, `eucRead_arm`).  The two solved witnesses enter
cleared, the lower at `(N ud)L + (un lc)Ẽ ~ (N ud lc)I` and the
upper at `(N ud)V + un ẼV ~ (N ud vc)I`, and their columns read the
located pairs `[g lc : N ud d]` and `[N ud d vc : N ud d + un p]`
(`euc_lo_col`, `euc_lo_col_ker`, `euc_hi_col` at the applied solve
identity); the iterated products carry the reads to
every count (`inertia.matPow`, `matPow_col`), the congruated
diagonals pin per root (`split.colDiagPin`), and the bracket closes
cross-cleared inside `euc_pair_price`, the sum's unit at or below
`lc^N dsV + (vc^N dsL).swap` at width
`[u²ϰ²(lc·vc)^N : N(ud·kd)²]` (the
two-sided Bernoulli display, `Pos.bernoulli_le`/`Pos.bernoulli_ge`,
the refinement comparisons at every larger count
`euc_hi_mono_le`/`euc_lo_mono_le`).  A read at the pair of families
is priced by the weighted polarization at the two probes' gram
reads, the spectral width the factor (`euc_pair_price` at
`split.pairScale` and `split.diagFold`); and the m-point iteration
is capped: the chain of head-capped probes over certified
separations (`growthTail`) collapses its gram along the
certificates (`tailCap` at `truncation.cap_sq` and `weight_step`),
and the chain read's magnitude sits at or below the end pairings at
the caps' fold against the certificate factors (`growth_cap`).

Clause (v$'$): the decomposition display.  At a convex splitting of
the state into translation-invariant components — the weights' fold
to one (`ground.bsum` at the entries `BPair.ofPos`), the splitting's read identities at the probe and
at the translate fold's square, each component's fold read at the
probe's (the invariance) and its fold square at or beyond its mean
square (the pairing's positivity) — the translate fold's
self-pairing collects the pair reads at their own counts
(`transSum` at the translates `transVec`, `trans_collect` at
`collectFold`: `n` diagonal reads and `2 (n - s)` per separation
`s`), the translated probes' fold on the ground collapsing to the
probe vector's translates at the ground's fixed read (`conjSum`),
and the weighted square fold of the component means about the
state's sits below the widths' read — the diagonal's own gap at the
mean's weight joined to the off-diagonal clustering widths, clause
(iv)'s displays, at the collection's counts (`decomp_display`), one
located bracket per probe at every translate count.

Clause (vi): the propagation bracket.  At the unit gram the level
gap is banded at the boundary list filling the order (`bandedAt`
at the two-sided keep `reachKeep` over `ground.prefixAt`
boundaries), and the witness inherits the gap's reads through the
join identity: the join's entry read forces the witness's
off-band entries vacant where the gap's are (`banded_of_join`)
and its symmetry from the gap's own (`sym_of_join`, the gap's
symmetry `split.sym_of_diagRead`'s read).  A banded matrix's
powers keep the widened boundaries (`pow_reach`): the lower
family's reach is exact, its blocks beyond `N` bands vacant.  A
leading-supported observable (`leadAt`, the padded carrier)
sandwiched by the powers keeps the widened support
(`lead_sandwich`), and against a tail-supported observable beyond
the reach (`tailAt`) the two products are vacant both ways
(`lead_tail_null`): the within-reach part of the evolved probe
commutes outright, and every ordering difference is the
remainder's own read.  The remainder is priced at clause (v)'s
width: the evolved probe's ordering gap sits at or below the
width against the caps and the two grams (`prop_bracket`) — the
two orderings' telescopes exact at the swap absorption, each of
the four branches one `euc_pair_price` instance at its branch
weights, the weights chosen so the cap chains (the
`inertia.capAt` binders at the observables, `cap_pow` at the
powers) land both grams at the one uniform weight per branch
pair, and the four priced branches assembled at the display —
with the symmetric factors walked across the pairing
(`elim.dotP_matVec_sym`).  The Green solve's beyond-band
components are the standing transfer telescopes at the
certificates (`lem:greenprod`(iii)'s reads at
`lem:spectator`(ii)'s caps), and the index-side commuting clause
is `relfiber.comm_shift`, standing: clause (vi)'s tier reads it
at the matrix carrier, where disjoint supports annihilate
outright.
-/

namespace groundreads
open ground elim inertia

/-- A positive rescaling keeps the unit tail. -/
private theorem gvsUnit (w : Pos) {v : List BPair}
    (h : poly.unitTail v) : poly.unitTail (greenprod.vecScale w v) :=
  poly.oneValue_unitTail (greenprod.vecScale_ofPos w v)
    (unitTail_vecScale _ v h)

/-- The rescaling distributes over the componentwise sum, the
longer list's tail riding. -/
private theorem scaleAdd (c : BPair) : ∀ p q : List BPair,
    vecScale c (poly.add p q) = poly.add (vecScale c p) (vecScale c q)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: p, b :: q => by
    show (c * (a + b)) :: vecScale c (poly.add p q)
      = (c * a + c * b) :: poly.add (vecScale c p) (vecScale c q)
    rw [BPair.left_distrib, scaleAdd c p q]

/-- Two composed clearings read the product's, the members
regrouped. -/
private theorem scaleJoin {a b c d : Pos} (h : a * b = c * d)
    (v : List BPair) :
    poly.oneValue (vecScale (BPair.ofPos a) (vecScale (BPair.ofPos b) v))
      (vecScale (BPair.ofPos c) (vecScale (BPair.ofPos d) v)) :=
  poly.oneValue_trans (greenprod.vecScale_two a b v)
    (poly.oneValue_trans
      (poly.oneValue_of_eq (greenprod.vecScale_posEq h v))
      (poly.oneValue_symm (greenprod.vecScale_two c d v)))

/-- Two composed clearings read the product's. -/
private theorem scaleFlat {a b c : Pos} (h : a * b = c)
    (v : List BPair) :
    poly.oneValue (vecScale (BPair.ofPos a) (vecScale (BPair.ofPos b) v))
      (vecScale (BPair.ofPos c) v) :=
  poly.oneValue_trans (greenprod.vecScale_two a b v)
    (poly.oneValue_of_eq (greenprod.vecScale_posEq h v))

/-- The pivot's action reads the slab block's at the pivot's own
clearing. -/
private theorem clearAct (X : greenprod.MatQ) (A : Mat)
    (h : greenprod.oneValueQ X (greenprod.ofM A)) (v : List BPair) :
    poly.oneValue (matVec X.1 v)
      (vecScale (BPair.ofPos X.2) (matVec A v)) := by
  have h0 : matOneValue (matScale Pos.one X.1) (matScale X.2 A) := h
  rw [matScale_one] at h0
  exact poly.oneValue_trans (matVec_matOne _ _ v h0)
    (matVec_matScale X.2 A v)

/-- The slab's kernel row at its accumulator: the pivot against the
slab's component joins the accumulator at the sum's unit, the two
clearings cross-multiplied. -/
private def rowRead (X : greenprod.MatQ) (u p : greenprod.VecQ) : Prop :=
  poly.unitTail
    (poly.add (vecScale (BPair.ofPos p.2) (matVec X.1 u.1))
      (vecScale (BPair.ofPos (X.2 * u.2)) p.1))

/-- The kernel rows' walk from the far end: at the tail recursion's
certificate, the rows at unit sides and an accumulator, every slab
carries its own row read and the ascending telescope over the
witnesses beyond it. -/
private theorem walk : ∀ (diag : List Mat) (A : Mat) (off : List Mat)
    (X : greenprod.MatQ) (Xs Rs : List greenprod.MatQ) (k : Nat)
    (ns : List Nat) (u : greenprod.VecQ) (us ws : List greenprod.VecQ)
    (p : greenprod.VecQ),
    greenprod.slabShape (A :: diag) off (k :: ns) →
    greenprod.qShape (X :: Xs) (k :: ns) →
    greenprod.wShapeR Rs (k :: ns) →
    greenprod.vShape (u :: us) (k :: ns) →
    greenprod.tailSteps (A :: diag) off (X :: Xs) Rs →
    greenprod.solveRows p (A :: diag) off (u :: us) ws →
    greenprod.sidesUnit ws →
    rowRead X u p ∧ greenprod.teleUpWalk 0 Rs (u :: us) := by
  intro diag
  induction diag with
  | nil =>
    intro A off X Xs Rs k ns u us ws p hslab hq hwr hv hts hsr hsu
    cases ns with
    | cons k1 ns1 =>
      cases off with
      | nil => exact (hslab : False).elim
      | cons B Bs => exact (hslab : False).elim
    | nil =>
    cases off with
    | cons B Bs => exact (hslab : False).elim
    | nil =>
    cases Xs with
    | cons X1 Xs1 => exact (hq.2 : False).elim
    | nil =>
    cases us with
    | cons u1 us1 => exact (hv.2 : False).elim
    | nil =>
    cases Rs with
    | cons R Rs1 => exact (hts : False).elim
    | nil =>
    cases ws with
    | nil => exact (hsr : False).elim
    | cons w ws1 =>
    cases ws1 with
    | cons w1 ws2 => exact (hsr : False).elim
    | nil =>
    refine ⟨?_, trivial⟩
    have hrow : poly.oneValue
        (greenprod.vecScale w.2
          (poly.add (greenprod.vecScale u.2 p.1)
            (greenprod.vecScale p.2 (matVec A u.1))))
        (greenprod.vecScale (p.2 * u.2) w.1) := hsr
    have m1 : poly.unitTail
        (greenprod.vecScale w.2
          (poly.add (greenprod.vecScale u.2 p.1)
            (greenprod.vecScale p.2 (matVec A u.1)))) :=
      poly.oneValue_unitTail hrow (gvsUnit _ hsu.1)
    have m2 : poly.unitTail
        (poly.add (greenprod.vecScale u.2 p.1)
          (greenprod.vecScale p.2 (matVec A u.1))) :=
      unitTail_unscale _ (BPair.ofPos_off w.2) _
        (poly.unitTail_oneValue_right m1 (greenprod.vecScale_ofPos w.2 _))
    have m3 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos X.2) (greenprod.vecScale u.2 p.1))
          (vecScale (BPair.ofPos X.2)
            (greenprod.vecScale p.2 (matVec A u.1)))) := by
      have h := unitTail_vecScale (BPair.ofPos X.2) _ m2
      rw [scaleAdd] at h
      exact h
    have m4 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos (X.2 * u.2)) p.1)
          (vecScale (BPair.ofPos p.2) (matVec X.1 u.1))) := by
      refine poly.unitTail_oneValue_right m3 (poly.add_congr ?_ ?_)
      · exact poly.oneValue_trans
          (vecScale_oneValue _ _ _ (greenprod.vecScale_ofPos u.2 p.1))
          (scaleFlat rfl p.1)
      · refine poly.oneValue_trans
          (vecScale_oneValue _ _ _
            (greenprod.vecScale_ofPos p.2 (matVec A u.1))) ?_
        refine poly.oneValue_trans
          (scaleJoin (ground.mul_comm X.2 p.2) (matVec A u.1)) ?_
        exact vecScale_oneValue _ _ _
          (poly.oneValue_symm (clearAct X A hts u.1))
    exact poly.oneValue_unitTail (poly.add_comm _ _) m4
  | cons A1 As ih =>
    intro A off X Xs Rs k ns u us ws p hslab hq hwr hv hts hsr hsu
    cases ns with
    | nil =>
      cases off with
      | nil => exact (hslab : False).elim
      | cons B Bs => exact (hslab : False).elim
    | cons k1 ns1 =>
    cases off with
    | nil => exact (hslab : False).elim
    | cons B Bs =>
    cases Xs with
    | nil => exact (hq.2 : False).elim
    | cons X1 Xs1 =>
    cases us with
    | nil => exact (hv.2 : False).elim
    | cons u1 us1 =>
    cases Rs with
    | nil => exact (hts : False).elim
    | cons R Rs1 =>
    cases ws with
    | nil => exact (hsr : False).elim
    | cons w ws1 =>
    -- the slab shapes
    have hk : 0 < k := hslab.1
    have hAsq : sqAt A k := hslab.2.1
    have hAl : A.length = k := sqAt_len hAsq
    have hAr : rowsLen k A := rowsLen_of_sqAt hAsq
    have hBl : B.length = k := greenprod.rectAt_len hslab.2.2.1
    have hBr : rowsLen k1 B := greenprod.rectAt_rows hslab.2.2.1
    have hBt : (transposeM B).length = k1 :=
      length_transposeM B hBr (by rw [hBl]; exact hk)
    have hXl : X.1.length = k := sqAt_len hq.1
    have hX1sq : sqAt X1.1 k1 := hq.2.1
    have hX1l : X1.1.length = k1 := sqAt_len hX1sq
    have hRl : R.1.length = k1 := greenprod.rectAt_len hwr.1
    have hRr : rowsLen k R.1 := greenprod.rectAt_rows hwr.1
    have hRt : (transposeM R.1).length = k :=
      length_transposeM R.1 hRr (by rw [hRl]; exact greenprod.slab_pos hslab.2.2.2 0 (Nat.succ_pos _))
    have hul : u.1.length = k := hv.1
    have hu1l : u1.1.length = k1 := hv.2.1
    -- the induction hypothesis at the exchange accumulator
    have hih := ih A1 Bs X1 Xs1 Rs1 k1 ns1 u1 us1 ws1
      (greenprod.appM (transposeM B) u)
      hslab.2.2.2 hq.2 hwr.2 hv.2 hts.2 hsr.2 hsu.2
    have hrow1 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos u.2) (matVec X1.1 u1.1))
          (vecScale (BPair.ofPos (X1.2 * u1.2))
            (matVec (transposeM B) u.1))) := hih.1
    -- the two carried vectors of the slab's telescope step
    have hA0l : (vecScale (BPair.ofPos (R.2 * u.2)) u1.1).length = k1 := by
      rw [length_vecScale]; exact hu1l
    have hB0l : (vecScale (BPair.ofPos u1.2)
        (matVec R.1 u.1)).length = k1 := by
      rw [length_vecScale, matVec_length]; exact hRl
    have hXR0 : matOneValue (matMul X1.1 R.1)
        (matScale (X1.2 * R.2) (transposeM B)) := by
      have h0 : matOneValue (matScale Pos.one (matMul X1.1 R.1))
          (matScale (X1.2 * R.2) (transposeM B)) := hts.1.2.1
      rw [matScale_one] at h0
      exact h0
    have hcomp : poly.oneValue (matVec X1.1 (matVec R.1 u.1))
        (vecScale (BPair.ofPos (X1.2 * R.2))
          (matVec (transposeM B) u.1)) :=
      poly.oneValue_trans
        (matVec_comp X1.1 R.1 u.1 k hRr hul
          (rowsLen_cast hRl.symm (rowsLen_of_sqAt hX1sq)))
        (poly.oneValue_trans (matVec_matOne _ _ u.1 hXR0)
          (matVec_matScale _ _ u.1))
    have t1 : poly.unitTail
        (poly.add
          (matVec X1.1 (vecScale (BPair.ofPos (R.2 * u.2)) u1.1))
          (matVec X1.1
            (vecScale (BPair.ofPos u1.2) (matVec R.1 u.1)))) := by
      have h := unitTail_vecScale (BPair.ofPos R.2) _ hrow1
      rw [scaleAdd] at h
      refine poly.unitTail_oneValue_right h (poly.add_congr ?_ ?_)
      · exact poly.oneValue_trans
          (scaleFlat rfl (matVec X1.1 u1.1))
          (poly.oneValue_symm
            (matVec_vecScale_free X1.1 (BPair.ofPos (R.2 * u.2)) u1.1))
      · refine poly.oneValue_trans
          (scaleJoin
            (show R.2 * (X1.2 * u1.2) = u1.2 * (X1.2 * R.2) by
              rw [ground.mul_left_comm R.2 X1.2 u1.2,
                ground.mul_left_comm u1.2 X1.2 R.2,
                ground.mul_comm R.2 u1.2])
            (matVec (transposeM B) u.1)) ?_
        exact poly.oneValue_trans
          (vecScale_oneValue _ _ _ (poly.oneValue_symm hcomp))
          (poly.oneValue_symm
            (matVec_vecScale_free X1.1 (BPair.ofPos u1.2)
              (matVec R.1 u.1)))
    have t2 : poly.unitTail
        (matVec X1.1
          (vecAdd (vecScale (BPair.ofPos (R.2 * u.2)) u1.1)
            (vecScale (BPair.ofPos u1.2) (matVec R.1 u.1)))) := by
      refine poly.oneValue_unitTail
        (matVec_vecAdd_free X1.1 _ _ (hA0l.trans hB0l.symm)) ?_
      rw [vecAdd_eq_polyAdd _ _
        ((matVec_length X1.1 _).trans
          ((matVec_length X1.1 _).symm))]
      exact t1
    have t4 : poly.unitTail
        (vecAdd (vecScale (BPair.ofPos (R.2 * u.2)) u1.1)
          (vecScale (BPair.ofPos u1.2) (matVec R.1 u.1))) :=
      matVec_null_of_det X1.1 hX1sq hts.1.1 _
        (length_vecAdd _ _ k1 hA0l hB0l) t2
    have t5 : poly.oneValue (vecScale (BPair.ofPos (R.2 * u.2)) u1.1)
        (List.map BPair.swap
          (vecScale (BPair.ofPos u1.2) (matVec R.1 u.1))) := by
      refine swap_of_null_add _ _ (hB0l.trans hA0l.symm) ?_
      rw [vecAdd_comm]
      exact t4
    have htele : greenprod.vOneValueQ u1
        (greenprod.appQ (greenprod.transfer R) u) := by
      show poly.oneValue (greenprod.vecScale (R.2 * u.2) u1.1)
        (greenprod.vecScale u1.2 (matVec (matSwap R.1) u.1))
      refine poly.oneValue_trans
        (greenprod.vecScale_ofPos (R.2 * u.2) u1.1)
        (poly.oneValue_trans t5 (poly.oneValue_symm ?_))
      rw [matVec_swapM]
      refine poly.oneValue_trans
        (greenprod.vecScale_ofPos u1.2 _) ?_
      rw [vecScale_swapMap]
      exact poly.oneValue_refl _
    refine ⟨?_, htele, hih.2⟩
    -- the exchange block's read off the telescope step
    have n1 : poly.unitTail
        (poly.add
          (vecScale (BPair.ofPos (R.2 * u.2)) (matVec B u1.1))
          (vecScale (BPair.ofPos u1.2)
            (matVec (matMul B R.1) u.1))) := by
      have h0 : poly.unitTail
          (matVec B
            (vecAdd (vecScale (BPair.ofPos (R.2 * u.2)) u1.1)
              (vecScale (BPair.ofPos u1.2) (matVec R.1 u.1)))) :=
        matVec_null B _ t4
      have h1 : poly.unitTail
          (vecAdd (matVec B (vecScale (BPair.ofPos (R.2 * u.2)) u1.1))
            (matVec B
              (vecScale (BPair.ofPos u1.2) (matVec R.1 u.1)))) :=
        poly.unitTail_oneValue_right h0
          (matVec_vecAdd_free B _ _ (hA0l.trans hB0l.symm))
      rw [vecAdd_eq_polyAdd _ _
        ((matVec_length B _).trans (matVec_length B _).symm)] at h1
      refine poly.unitTail_oneValue_right h1 (poly.add_congr ?_ ?_)
      · exact matVec_vecScale_free B (BPair.ofPos (R.2 * u.2)) u1.1
      · exact poly.oneValue_trans
          (matVec_vecScale_free B (BPair.ofPos u1.2) (matVec R.1 u.1))
          (vecScale_oneValue _ _ _
            (matVec_comp B R.1 u.1 k hRr hul
              (rowsLen_cast hRl.symm hBr)))
    have hG3l : (vecScale (BPair.ofPos (R.2 * (p.2 * u.2)))
        (matVec B u1.1)).length = k := by
      rw [length_vecScale, matVec_length]; exact hBl
    have hWl : (vecScale (BPair.ofPos (p.2 * u1.2))
        (matVec (matMul B R.1) u.1)).length = k := by
      rw [length_vecScale, matVec_length, length_matMul]; exact hBl
    have n4 : poly.unitTail
        (vecAdd
          (vecScale (BPair.ofPos (R.2 * (p.2 * u.2))) (matVec B u1.1))
          (vecScale (BPair.ofPos (p.2 * u1.2))
            (matVec (matMul B R.1) u.1))) := by
      rw [vecAdd_eq_polyAdd _ _ (hG3l.trans hWl.symm)]
      have h := unitTail_vecScale (BPair.ofPos p.2) _ n1
      rw [scaleAdd] at h
      refine poly.unitTail_oneValue_right h (poly.add_congr ?_ ?_)
      · exact scaleFlat
          (show p.2 * (R.2 * u.2) = R.2 * (p.2 * u.2) from
            ground.mul_left_comm p.2 R.2 u.2)
          (matVec B u1.1)
      · exact scaleFlat rfl (matVec (matMul B R.1) u.1)
    have t6 : poly.oneValue
        (vecScale (BPair.ofPos (R.2 * (p.2 * u.2))) (matVec B u1.1))
        (List.map BPair.swap
          (vecScale (BPair.ofPos (p.2 * u1.2))
            (matVec (matMul B R.1) u.1))) := by
      refine swap_of_null_add _ _ (hWl.trans hG3l.symm) ?_
      rw [vecAdd_comm]
      exact n4
    -- the slab's own row, collected
    have hrow : poly.oneValue
        (greenprod.vecScale w.2
          (poly.add (greenprod.vecScale (u.2 * u1.2) p.1)
            (greenprod.vecScale p.2
              (poly.add (greenprod.vecScale u1.2 (matVec A u.1))
                (greenprod.vecScale u.2 (matVec B u1.1))))))
        (greenprod.vecScale (p.2 * (u.2 * u1.2)) w.1) := hsr.1
    have m2 : poly.unitTail
        (poly.add (greenprod.vecScale (u.2 * u1.2) p.1)
          (greenprod.vecScale p.2
            (poly.add (greenprod.vecScale u1.2 (matVec A u.1))
              (greenprod.vecScale u.2 (matVec B u1.1))))) :=
      unitTail_unscale _ (BPair.ofPos_off w.2) _
        (poly.unitTail_oneValue_right
          (poly.oneValue_unitTail hrow (gvsUnit _ hsu.1))
          (greenprod.vecScale_ofPos w.2 _))
    have m3 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos (u.2 * u1.2)) p.1)
          (poly.add (vecScale (BPair.ofPos (p.2 * u1.2)) (matVec A u.1))
            (vecScale (BPair.ofPos (p.2 * u.2)) (matVec B u1.1)))) := by
      refine poly.unitTail_oneValue_right m2
        (poly.add_congr (greenprod.vecScale_ofPos _ _) ?_)
      refine poly.oneValue_trans (greenprod.vecScale_ofPos p.2 _) ?_
      rw [scaleAdd]
      exact poly.add_congr
        (poly.oneValue_trans
          (vecScale_oneValue _ _ _
            (greenprod.vecScale_ofPos u1.2 (matVec A u.1)))
          (scaleFlat rfl (matVec A u.1)))
        (poly.oneValue_trans
          (vecScale_oneValue _ _ _
            (greenprod.vecScale_ofPos u.2 (matVec B u1.1)))
          (scaleFlat rfl (matVec B u1.1)))
    have m6 : poly.unitTail
        (poly.add
          (vecScale (BPair.ofPos u1.2)
            (vecScale (BPair.ofPos (R.2 * u.2)) p.1))
          (poly.add
            (vecScale (BPair.ofPos u1.2)
              (vecScale (BPair.ofPos (R.2 * p.2)) (matVec A u.1)))
            (vecScale (BPair.ofPos u1.2)
              (List.map BPair.swap
                (vecScale (BPair.ofPos p.2)
                  (matVec (matMul B R.1) u.1)))))) := by
      have h := unitTail_vecScale (BPair.ofPos R.2) _ m3
      rw [scaleAdd, scaleAdd] at h
      refine poly.unitTail_oneValue_right h
        (poly.add_congr ?_ (poly.add_congr ?_ ?_))
      · exact scaleJoin
          (show R.2 * (u.2 * u1.2) = u1.2 * (R.2 * u.2) by
            rw [← ground.mul_assoc R.2 u.2 u1.2,
              ground.mul_comm (R.2 * u.2) u1.2]) p.1
      · exact scaleJoin
          (show R.2 * (p.2 * u1.2) = u1.2 * (R.2 * p.2) by
            rw [← ground.mul_assoc R.2 p.2 u1.2,
              ground.mul_comm (R.2 * p.2) u1.2]) (matVec A u.1)
      · refine poly.oneValue_trans
          (scaleFlat
            (show R.2 * (p.2 * u.2) = R.2 * (p.2 * u.2) from rfl)
            (matVec B u1.1)) ?_
        refine poly.oneValue_trans t6 ?_
        rw [vecScale_swapMap]
        exact poly.swapMap_oneValue
          (poly.oneValue_symm
            (scaleFlat (ground.mul_comm u1.2 p.2)
              (matVec (matMul B R.1) u.1)))
    have m7 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos (R.2 * u.2)) p.1)
          (poly.add
            (vecScale (BPair.ofPos (R.2 * p.2)) (matVec A u.1))
            (List.map BPair.swap
              (vecScale (BPair.ofPos p.2)
                (matVec (matMul B R.1) u.1))))) := by
      refine unitTail_unscale _ (BPair.ofPos_off u1.2) _ ?_
      rw [scaleAdd, scaleAdd]
      exact m6
    have hj0 : matOneValue
        (matAdd (matScale R.2 X.1) (matScale X.2 (matMul B R.1)))
        (matScale (X.2 * R.2) A) := by
      have h0 : matOneValue (matScale Pos.one
          (matAdd (matScale (Pos.one * R.2) X.1)
            (matScale X.2 (matMul B R.1))))
          (matScale (X.2 * (Pos.one * R.2)) A) := hts.1.2.2
      rw [matScale_one, ground.one_mul R.2] at h0
      exact h0
    have hsplit : poly.oneValue
        (vecScale (BPair.ofPos (X.2 * R.2)) (matVec A u.1))
        (poly.add (vecScale (BPair.ofPos R.2) (matVec X.1 u.1))
          (vecScale (BPair.ofPos X.2) (matVec (matMul B R.1) u.1))) := by
      have hadd := matVec_add (matScale R.2 X.1)
        (matScale X.2 (matMul B R.1)) u.1
        (rowsLen_cast hul.symm (rowsLen_mapRows _ X.1 k
          (rowsLen_of_sqAt hq.1)))
        (rowsLen_cast hul.symm (rowsLen_mapRows _ (matMul B R.1) k
          (rowsLen_cast hRt (rowsLen_matMul B R.1))))
      have hx : (matVec (matScale R.2 X.1) u.1).length = k := by
        rw [matVec_length, length_matScale]; exact hXl
      have hy : (matVec (matScale X.2 (matMul B R.1)) u.1).length = k := by
        rw [matVec_length, length_matScale, length_matMul]; exact hBl
      rw [vecAdd_eq_polyAdd _ _ (hx.trans hy.symm)] at hadd
      refine poly.oneValue_trans
        (poly.oneValue_symm (matVec_matScale (X.2 * R.2) A u.1)) ?_
      refine poly.oneValue_trans
        (poly.oneValue_symm (matVec_matOne _ _ u.1 hj0)) ?_
      refine poly.oneValue_trans hadd ?_
      exact poly.add_congr (matVec_matScale R.2 X.1 u.1)
        (matVec_matScale X.2 (matMul B R.1) u.1)
    have hZl : (vecScale (BPair.ofPos p.2)
        (vecScale (BPair.ofPos X.2)
          (matVec (matMul B R.1) u.1))).length = k := by
      rw [length_vecScale, length_vecScale, matVec_length,
        length_matMul]
      exact hBl
    have m9 : poly.unitTail
        (poly.add
          (vecScale (BPair.ofPos R.2)
            (vecScale (BPair.ofPos (X.2 * u.2)) p.1))
          (vecScale (BPair.ofPos R.2)
            (vecScale (BPair.ofPos p.2) (matVec X.1 u.1)))) := by
      have h := unitTail_vecScale (BPair.ofPos X.2) _ m7
      rw [scaleAdd, scaleAdd] at h
      refine poly.unitTail_oneValue_right h (poly.add_congr ?_ ?_)
      · exact scaleJoin
          (show X.2 * (R.2 * u.2) = R.2 * (X.2 * u.2) from
            ground.mul_left_comm X.2 R.2 u.2) p.1
      · refine poly.oneValue_trans
          (poly.add_congr
            (poly.oneValue_trans
              (scaleFlat (ground.mul_comm X.2 (R.2 * p.2))
                (matVec A u.1))
              (poly.oneValue_trans
                (poly.oneValue_symm
                  (scaleFlat
                    (show p.2 * (X.2 * R.2) = R.2 * p.2 * X.2 by
                      rw [ground.mul_comm X.2 R.2,
                        ground.mul_left_comm p.2 R.2 X.2,
                        ground.mul_assoc R.2 p.2 X.2])
                    (matVec A u.1)))
                (vecScale_oneValue _ _ _ hsplit)))
            (poly.oneValue_of_eq
              (vecScale_swapMap (BPair.ofPos X.2) _))) ?_
        rw [scaleAdd]
        refine poly.oneValue_trans
          (poly.oneValue_symm (poly.add_join _ _ _)) ?_
        refine poly.oneValue_trans
          (poly.add_unitTail _ ?_) ?_
        · have h0 : poly.unitTail
              (vecAdd
                (vecScale (BPair.ofPos p.2)
                  (vecScale (BPair.ofPos X.2)
                    (matVec (matMul B R.1) u.1)))
                (List.map BPair.swap
                  (vecScale (BPair.ofPos p.2)
                    (vecScale (BPair.ofPos X.2)
                      (matVec (matMul B R.1) u.1))))) :=
            vecAdd_swap_unitTail _
          rw [vecAdd_eq_polyAdd _ _
            (by rw [ground.length_map])] at h0
          refine poly.unitTail_oneValue_right h0
            (poly.add_congr (poly.oneValue_refl _) ?_)
          exact poly.swapMap_oneValue
            (poly.oneValue_symm
              (scaleJoin (ground.mul_comm X.2 p.2)
                (matVec (matMul B R.1) u.1)))
        · exact poly.oneValue_symm
            (scaleJoin (ground.mul_comm R.2 p.2) (matVec X.1 u.1))
    have m11 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos (X.2 * u.2)) p.1)
          (vecScale (BPair.ofPos p.2) (matVec X.1 u.1))) := by
      refine unitTail_unscale _ (BPair.ofPos_off R.2) _ ?_
      rw [scaleAdd]
      exact m9
    exact poly.oneValue_unitTail (poly.add_comm _ _) m11

/-- The kernel rows close from the far end: at the tail recursion's
certificate and the rows at unit sides every slab is the next transfer
factor's image of the slab before it, the ascending telescope from the
head. -/
theorem kernel_tele (diag off : List Mat) (Xs Rs : List greenprod.MatQ)
    (ns : List Nat) (us ws : List greenprod.VecQ)
    (ht : greenprod.tailRead diag off Xs Rs ns)
    (hs : greenprod.solveRead diag off us ws ns)
    (hw : greenprod.sidesUnit ws) : greenprod.teleUp Rs us 0 ns := by
  obtain ⟨hslab, hqs, hwr, hsteps⟩ := ht
  obtain ⟨_, hvs, _, hrows⟩ := hs
  cases diag with
  | nil => exact (hslab : False).elim
  | cons A diag1 =>
  cases ns with
  | nil => exact (hslab : False).elim
  | cons k ns1 =>
  cases Xs with
  | nil => exact (hqs : False).elim
  | cons X Xs1 =>
  cases us with
  | nil => exact (hvs : False).elim
  | cons u us1 =>
  exact ⟨hwr, hvs,
    (walk diag1 A off X Xs1 Rs k ns1 u us1 ws ([], Pos.one)
      hslab hqs hwr hvs hsteps hrows hw).2⟩

/-- The rows strictly below a depth at unit sides, the source
support's leading read. -/
private def belowUnit : Nat → List greenprod.VecQ → Prop
  | 0, _ => True
  | _ + 1, [] => True
  | i + 1, w :: ws => poly.unitTail w.1 ∧ belowUnit i ws

/-- The source's support hands the leading rows their unit
sides. -/
private theorem belowOfSupport : ∀ (jb : Nat) (ws : List greenprod.VecQ),
    greenprod.supportAt ws jb → belowUnit jb ws
  | 0, _, _ => trivial
  | _ + 1, [], _ => trivial
  | i + 1, _ :: ws, h => ⟨h.1, belowOfSupport i ws h.2⟩

/-- The forward rows' invariant: the accumulator joins the
diagonal's action to the head pivot's at the slabs' clearings. -/
private def downRead (Y : greenprod.MatQ) (A : Mat)
    (u p : greenprod.VecQ) : Prop :=
  poly.unitTail
    (poly.add (vecScale (BPair.ofPos (Y.2 * u.2)) p.1)
      (poly.add (vecScale (BPair.ofPos (Y.2 * p.2)) (matVec A u.1))
        ((vecScale (BPair.ofPos p.2) (matVec Y.1 u.1)).map BPair.swap)))

/-- The forward walk below the source: at the head recursion's
certificate, the rows at unit sides and the invariant at the head
slab, the slabs below the source each hand their component to the
next transfer factor's image, the descending telescope. -/
private theorem walkDown : ∀ (jb : Nat) (A : Mat) (diag off : List Mat)
    (Y : greenprod.MatQ) (Ys Cs : List greenprod.MatQ) (k : Nat)
    (ns : List Nat) (u : greenprod.VecQ) (us ws : List greenprod.VecQ)
    (p : greenprod.VecQ),
    greenprod.slabShape (A :: diag) off (k :: ns) →
    greenprod.qShape (Y :: Ys) (k :: ns) →
    greenprod.wShapeC Cs (k :: ns) →
    greenprod.vShape (u :: us) (k :: ns) →
    greenprod.headSteps (A :: diag) off (Y :: Ys) Cs →
    greenprod.solveRows p (A :: diag) off (u :: us) ws →
    belowUnit jb ws →
    jb < (u :: us).length →
    downRead Y A u p →
    greenprod.teleDownWalk jb Cs (u :: us) := by
  intro jb
  induction jb with
  | zero =>
    exact fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  | succ i ih =>
    intro A diag off Y Ys Cs k ns u us ws p
      hslab hq hwc hv hhs hsr hbu hjb hinv
    cases us with
    | nil => exact absurd (Nat.lt_of_succ_lt_succ hjb) (Nat.not_lt_zero _)
    | cons u1 us1 =>
    cases ns with
    | nil => exact (hv.2 : False).elim
    | cons k1 ns1 =>
    cases diag with
    | nil =>
      cases off with
      | nil => exact (hslab : False).elim
      | cons B Bs => exact (hslab : False).elim
    | cons A1 diag1 =>
    cases off with
    | nil => exact (hslab : False).elim
    | cons B Bs =>
    cases Cs with
    | nil => exact (hwc : False).elim
    | cons C Cs1 =>
    cases Ys with
    | nil => exact (hhs : False).elim
    | cons Y1 Ys1 =>
    cases ws with
    | nil => exact (hsr : False).elim
    | cons w ws1 =>
    -- the peeled data
    obtain ⟨⟨hdet, hYC, hjoin⟩, hhs1⟩ := hhs
    obtain ⟨hrow, hsr1⟩ := hsr
    obtain ⟨hwu, hbu1⟩ := hbu
    -- the row at the unit side, cleared of the side's clearing
    have hm2 : poly.unitTail
        (poly.add (greenprod.vecScale (u.2 * u1.2) p.1)
          (greenprod.vecScale p.2
            (poly.add (greenprod.vecScale u1.2 (matVec A u.1))
              (greenprod.vecScale u.2 (matVec B u1.1))))) :=
      unitTail_unscale _ (BPair.ofPos_off w.2) _
        (poly.unitTail_oneValue_right
          (poly.oneValue_unitTail hrow (gvsUnit _ hwu))
          (greenprod.vecScale_ofPos w.2 _))
    have hm3 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos (u.2 * u1.2)) p.1)
          (poly.add (vecScale (BPair.ofPos (p.2 * u1.2)) (matVec A u.1))
            (vecScale (BPair.ofPos (p.2 * u.2)) (matVec B u1.1)))) := by
      refine poly.unitTail_oneValue_right hm2
        (poly.add_congr (greenprod.vecScale_ofPos _ _) ?_)
      refine poly.oneValue_trans (greenprod.vecScale_ofPos p.2 _) ?_
      rw [scaleAdd]
      exact poly.add_congr
        (poly.oneValue_trans
          (vecScale_oneValue _ _ _
            (greenprod.vecScale_ofPos u1.2 (matVec A u.1)))
          (scaleFlat rfl (matVec A u.1)))
        (poly.oneValue_trans
          (vecScale_oneValue _ _ _
            (greenprod.vecScale_ofPos u.2 (matVec B u1.1)))
          (scaleFlat rfl (matVec B u1.1)))
    -- the head pivot's row: the invariant against the row at the
    -- unit side, the shared terms withdrawing at the swap
    have hA : poly.unitTail
        (poly.add
          (poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
            (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2))) (matVec A u.1)))
          (vecScale (BPair.ofPos (Y.2 * (p.2 * u.2))) (matVec B u1.1))) := by
      have h0 := unitTail_vecScale (BPair.ofPos Y.2) _ hm3
      rw [scaleAdd, scaleAdd] at h0
      refine poly.unitTail_oneValue_right h0
        (poly.oneValue_trans
          (poly.add_congr
            (scaleFlat rfl p.1)
            (poly.add_congr (scaleFlat rfl (matVec A u.1))
              (scaleFlat rfl (matVec B u1.1))))
          (poly.add_join _ _ _))
    have hB : poly.unitTail
        (poly.add
          (poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
            (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2))) (matVec A u.1)))
          ((vecScale (BPair.ofPos (p.2 * u1.2)) (matVec Y.1 u.1)).map
            BPair.swap)) := by
      have h0 := unitTail_vecScale (BPair.ofPos u1.2) _ hinv
      rw [scaleAdd, scaleAdd] at h0
      refine poly.unitTail_oneValue_right h0
        (poly.oneValue_trans
          (poly.add_congr
            (scaleFlat (show u1.2 * (Y.2 * u.2) = Y.2 * (u.2 * u1.2) by
              rw [ground.mul_comm u1.2 (Y.2 * u.2),
                ground.mul_assoc Y.2 u.2 u1.2]) p.1)
            (poly.add_congr
              (scaleFlat (show u1.2 * (Y.2 * p.2) = Y.2 * (p.2 * u1.2) by
                rw [ground.mul_comm u1.2 (Y.2 * p.2),
                  ground.mul_assoc Y.2 p.2 u1.2]) (matVec A u.1))
              (poly.oneValue_trans
                (poly.oneValue_of_eq
                  (vecScale_swapMap (BPair.ofPos u1.2) _))
                (poly.swapMap_oneValue
                  (scaleFlat (ground.mul_comm u1.2 p.2)
                    (matVec Y.1 u.1))))))
          (poly.add_join _ _ _))
    -- the shared terms withdraw at the swap: the head pivot's row
    have hG1 : poly.unitTail
        (poly.add (vecScale (BPair.ofPos (p.2 * u1.2)) (matVec Y.1 u.1))
          (vecScale (BPair.ofPos (Y.2 * (p.2 * u.2))) (matVec B u1.1))) := by
      have hns := poly.neg_sum
        (poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
          (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2))) (matVec A u.1)))
        ((vecScale (BPair.ofPos (p.2 * u1.2)) (matVec Y.1 u.1)).map
          BPair.swap)
      have hdd := poly.neg_neg
        (vecScale (BPair.ofPos (p.2 * u1.2)) (matVec Y.1 u.1))
      have hBsw : poly.unitTail
          (poly.add
            ((poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
              (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2)))
                (matVec A u.1))).map BPair.swap)
            (vecScale (BPair.ofPos (p.2 * u1.2)) (matVec Y.1 u.1))) := by
        have h0 := poly.unitTail_swapMap _ hB
        rw [show ((poly.add
            (poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
              (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2))) (matVec A u.1)))
            ((vecScale (BPair.ofPos (p.2 * u1.2)) (matVec Y.1 u.1)).map
              BPair.swap)).map BPair.swap)
          = poly.add
            ((poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
              (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2)))
                (matVec A u.1))).map BPair.swap)
            (vecScale (BPair.ofPos (p.2 * u1.2)) (matVec Y.1 u.1))
          from hns.trans (congrArg _ hdd)] at h0
        exact h0
      have hsum := poly.unitTail_sum hA hBsw
      have hbal : poly.unitTail
          (poly.add
            (poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
              (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2))) (matVec A u.1)))
            ((poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
              (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2)))
                (matVec A u.1))).map BPair.swap)) := by
        have h0 := vecAdd_swap_unitTail
          (poly.add (vecScale (BPair.ofPos (Y.2 * (u.2 * u1.2))) p.1)
            (vecScale (BPair.ofPos (Y.2 * (p.2 * u1.2))) (matVec A u.1)))
        rw [vecAdd_eq_polyAdd _ _ (by rw [ground.length_map])] at h0
        exact h0
      refine poly.unitTail_oneValue_right hsum ?_
      refine poly.oneValue_trans
        (poly.oneValue_symm (poly.add_join _ _ _)) ?_
      refine poly.oneValue_trans
        (poly.add_congr (poly.oneValue_refl _)
          (poly.add_comm _ _)) ?_
      refine poly.oneValue_trans
        (poly.add_congr (poly.oneValue_refl _)
          (poly.oneValue_symm (poly.add_join _ _ _))) ?_
      refine poly.oneValue_trans (poly.add_join _ _ _) ?_
      exact poly.unitTail_add hbal _
    -- the shape frames
    have hk0 : 0 < k := hslab.1
    have hYsq : sqAt Y.1 k := hq.1
    have hul : u.1.length = k := hv.1
    have hu1l : u1.1.length = k1 := hv.2.1
    have hCsw_rows : rowsLen k1 (matSwap C.1) :=
      rowsLen_mapRows BPair.swap C.1 k1 (greenprod.rectAt_rows hwc.1)
    have hCsw_len : (matSwap C.1).length = k :=
      (length_matSwap C.1).trans (greenprod.rectAt_len hwc.1)
    have hTt : (transposeM (matSwap C.1)).length = k1 :=
      length_transposeM (matSwap C.1) hCsw_rows
        (by rw [hCsw_len]; exact hk0)
    have hMulRows : rowsLen u1.1.length (matMul Y.1 (matSwap C.1)) := by
      rw [hu1l, ← hTt]; exact rowsLen_matMul Y.1 (matSwap C.1)
    have hBrows : rowsLen u1.1.length B := by
      rw [hu1l]; exact greenprod.rectAt_rows hslab.2.2.1
    -- the transfer witness's action at the far component
    have htn : poly.unitTail
        (matVec (matAdd (matScale Pos.one (matMul Y.1 (matSwap C.1)))
          (matScale (Y.2 * C.2) B)) u1.1) :=
      matVec_matNull _ u1.1 (greenprod.transfer_null Y C B hYC)
    have hact : poly.unitTail
        (poly.add (matVec Y.1 (matVec (matSwap C.1) u1.1))
          (vecScale (BPair.ofPos (Y.2 * C.2)) (matVec B u1.1))) := by
      rw [matScale_one] at htn
      have h1 := poly.unitTail_oneValue_right htn
        (matVec_add _ _ u1.1 hMulRows
          (rowsLen_mapRows _ _ _ hBrows))
      rw [vecAdd_eq_polyAdd _ _ (by
        rw [matVec_length, matVec_length, length_matScale,
          length_matMul, sqAt_len hYsq,
          greenprod.rectAt_len hslab.2.2.1])] at h1
      refine poly.unitTail_oneValue_right h1 (poly.add_congr ?_ ?_)
      · exact poly.oneValue_symm
          (matVec_comp Y.1 (matSwap C.1) u1.1 k1 hCsw_rows hu1l
            (by rw [hCsw_len]; exact rowsLen_of_sqAt hYsq))
      · exact inertia.matVec_matScale _ B u1.1
    -- the far coupling withdraws between the pivot's row and the
    -- transfer witness's action
    have hmid : poly.unitTail
        (poly.add
          (vecScale (BPair.ofPos (p.2 * (C.2 * u1.2))) (matVec Y.1 u.1))
          ((vecScale (BPair.ofPos (p.2 * u.2))
            (matVec Y.1 (matVec (matSwap C.1) u1.1))).map BPair.swap)) := by
      have h2 := unitTail_vecScale (BPair.ofPos C.2) _ hG1
      rw [scaleAdd] at h2
      have h2' : poly.unitTail (poly.add
          (vecScale (BPair.ofPos (p.2 * (C.2 * u1.2))) (matVec Y.1 u.1))
          (vecScale (BPair.ofPos ((p.2 * u.2) * (Y.2 * C.2)))
            (matVec B u1.1))) :=
        poly.unitTail_oneValue_right h2 (poly.add_congr
          (scaleFlat (show C.2 * (p.2 * u1.2) = p.2 * (C.2 * u1.2) from
            ground.mul_left_comm C.2 p.2 u1.2) (matVec Y.1 u.1))
          (scaleFlat (show C.2 * (Y.2 * (p.2 * u.2))
              = (p.2 * u.2) * (Y.2 * C.2) by
            rw [ground.mul_comm C.2 (Y.2 * (p.2 * u.2)),
              ground.mul_assoc Y.2 (p.2 * u.2) C.2,
              ground.mul_comm Y.2 ((p.2 * u.2) * C.2),
              ground.mul_assoc (p.2 * u.2) C.2 Y.2,
              ground.mul_comm C.2 Y.2,
              ← ground.mul_assoc (p.2 * u.2) Y.2 C.2,
              ground.mul_assoc (p.2 * u.2) Y.2 C.2])
            (matVec B u1.1)))
      have h3 := poly.unitTail_swapMap _ hact
      have hns3 : (poly.add (matVec Y.1 (matVec (matSwap C.1) u1.1))
            (vecScale (BPair.ofPos (Y.2 * C.2)) (matVec B u1.1))).map
            BPair.swap
          = poly.add
            ((matVec Y.1 (matVec (matSwap C.1) u1.1)).map BPair.swap)
            ((vecScale (BPair.ofPos (Y.2 * C.2))
              (matVec B u1.1)).map BPair.swap) :=
        poly.neg_sum _ _
      rw [hns3] at h3
      have h4 := unitTail_vecScale (BPair.ofPos (p.2 * u.2)) _ h3
      rw [scaleAdd] at h4
      have h4' : poly.unitTail (poly.add
          ((vecScale (BPair.ofPos (p.2 * u.2))
            (matVec Y.1 (matVec (matSwap C.1) u1.1))).map BPair.swap)
          ((vecScale (BPair.ofPos ((p.2 * u.2) * (Y.2 * C.2)))
            (matVec B u1.1)).map BPair.swap)) :=
        poly.unitTail_oneValue_right h4 (poly.add_congr
          (poly.oneValue_of_eq (vecScale_swapMap _ _))
          (poly.oneValue_trans
            (poly.oneValue_of_eq (vecScale_swapMap _ _))
            (poly.swapMap_oneValue (scaleFlat rfl (matVec B u1.1)))))
      have hsum := poly.unitTail_sum h2' h4'
      have hbal2 : poly.unitTail (poly.add
          (vecScale (BPair.ofPos ((p.2 * u.2) * (Y.2 * C.2)))
            (matVec B u1.1))
          ((vecScale (BPair.ofPos ((p.2 * u.2) * (Y.2 * C.2)))
            (matVec B u1.1)).map BPair.swap)) := by
        have h0 := vecAdd_swap_unitTail
          (vecScale (BPair.ofPos ((p.2 * u.2) * (Y.2 * C.2)))
            (matVec B u1.1))
        rw [vecAdd_eq_polyAdd _ _ (by rw [ground.length_map])] at h0
        exact h0
      refine poly.unitTail_oneValue_right hsum ?_
      refine poly.oneValue_trans (poly.add_add_comm _ _ _ _) ?_
      refine poly.oneValue_trans (poly.add_comm _ _) ?_
      exact poly.unitTail_add hbal2 _
    -- the pivot cancels: the slab's component is the transfer image
    have hstep : greenprod.vOneValueQ u
        (greenprod.appQ (greenprod.transfer C) u1) := by
      have hin : poly.unitTail
          (poly.add
            (vecScale (BPair.ofPos (C.2 * u1.2)) (matVec Y.1 u.1))
            ((vecScale (BPair.ofPos u.2)
              (matVec Y.1 (matVec (matSwap C.1) u1.1))).map
                BPair.swap)) := by
        refine unitTail_unscale (BPair.ofPos p.2) (BPair.ofPos_off p.2) _ ?_
        rw [scaleAdd]
        refine poly.unitTail_oneValue_right hmid (poly.add_congr ?_ ?_)
        · exact poly.oneValue_symm
            (scaleFlat (rfl : p.2 * (C.2 * u1.2) = p.2 * (C.2 * u1.2))
              (matVec Y.1 u.1))
        · refine poly.oneValue_trans
            (poly.swapMap_oneValue
              (poly.oneValue_symm
                (scaleFlat (rfl : p.2 * u.2 = p.2 * u.2)
                  (matVec Y.1 (matVec (matSwap C.1) u1.1))))) ?_
          exact poly.oneValue_of_eq
            (vecScale_swapMap (BPair.ofPos p.2)
              (vecScale (BPair.ofPos u.2)
                (matVec Y.1 (matVec (matSwap C.1) u1.1)))).symm
      have hYV : poly.unitTail
          (matVec Y.1 (vecAdd
            (vecScale (BPair.ofPos (C.2 * u1.2)) u.1)
            ((vecScale (BPair.ofPos u.2)
              (matVec (matSwap C.1) u1.1)).map BPair.swap))) := by
        have hlen1 : (vecScale (BPair.ofPos (C.2 * u1.2)) u.1).length
            = k := by rw [length_vecScale]; exact hul
        have hlen2 : ((vecScale (BPair.ofPos u.2)
            (matVec (matSwap C.1) u1.1)).map BPair.swap).length = k := by
          rw [ground.length_map, length_vecScale, matVec_length]
          exact hCsw_len
        refine poly.unitTail_oneValue_right hin ?_
        refine poly.oneValue_trans (poly.add_congr
          (poly.oneValue_symm
            (matVec_vecScale_free Y.1 (BPair.ofPos (C.2 * u1.2)) u.1))
          (poly.oneValue_trans
            (poly.swapMap_oneValue
              (poly.oneValue_symm
                (matVec_vecScale_free Y.1 (BPair.ofPos u.2)
                  (matVec (matSwap C.1) u1.1))))
            (poly.oneValue_of_eq
              (matVec_swapArg _ Y.1).symm))) ?_
        rw [← vecAdd_eq_polyAdd _ _ (by
          rw [matVec_length, matVec_length])]
        exact poly.oneValue_symm
          (matVec_vecAdd Y.1 k (rowsLen_of_sqAt hYsq) _ _ hlen1 hlen2)
      have hVsum : poly.unitTail (vecAdd
          (vecScale (BPair.ofPos (C.2 * u1.2)) u.1)
          ((vecScale (BPair.ofPos u.2)
            (matVec (matSwap C.1) u1.1)).map BPair.swap)) :=
        matVec_null_of_det Y.1 hYsq hdet _
          (length_vecAdd _ _ k
            (by rw [length_vecScale]; exact hul)
            (by rw [ground.length_map, length_vecScale, matVec_length]
                exact hCsw_len))
          hYV
      rw [vecAdd_comm] at hVsum
      have hone := swap_of_null_add _ _
        (by rw [ground.length_map, length_vecScale, matVec_length,
            length_vecScale, hCsw_len]
            exact hul.symm)
        hVsum
      have hdd2 : ((vecScale (BPair.ofPos u.2)
            (matVec (matSwap C.1) u1.1)).map BPair.swap).map BPair.swap
          = vecScale (BPair.ofPos u.2) (matVec (matSwap C.1) u1.1) :=
        poly.neg_neg _
      rw [hdd2] at hone
      show poly.oneValue (greenprod.vecScale (C.2 * u1.2) u.1)
        (greenprod.vecScale u.2 (matVec (matSwap C.1) u1.1))
      refine poly.oneValue_trans (greenprod.vecScale_ofPos _ u.1) ?_
      refine poly.oneValue_trans hone ?_
      exact poly.oneValue_symm (greenprod.vecScale_ofPos u.2 _)
    -- the invariant steps to the next slab: the join reads the
    -- exchange block through the telescope's image
    have hBt_rows : rowsLen k (transposeM B) :=
      rowsLen_cast (greenprod.rectAt_len hslab.2.2.1)
        (rowsLen_transposeM B)
    -- the telescope's image under the exchange block
    have ha : poly.oneValue
        (vecScale (BPair.ofPos (C.2 * u1.2))
          (matVec (transposeM B) u.1))
        ((vecScale (BPair.ofPos u.2)
          (matVec (matMul (transposeM B) C.1) u1.1)).map BPair.swap) := by
      refine poly.oneValue_trans
        (poly.oneValue_symm
          (matVec_vecScale_free (transposeM B)
            (BPair.ofPos (C.2 * u1.2)) u.1)) ?_
      refine poly.oneValue_trans
        (matVec_congr (transposeM B) _ _
          (poly.oneValue_trans
            (poly.oneValue_symm
              (greenprod.vecScale_ofPos (C.2 * u1.2) u.1))
            (poly.oneValue_trans hstep
              (greenprod.vecScale_ofPos u.2 _)))) ?_
      refine poly.oneValue_trans
        (matVec_vecScale_free (transposeM B) (BPair.ofPos u.2) _) ?_
      refine poly.oneValue_trans
        (elim.vecScale_oneValue _ _ _
          (matVec_comp (transposeM B) (matSwap C.1) u1.1 k1
            hCsw_rows hu1l
            (rowsLen_cast hCsw_len.symm hBt_rows))) ?_
      rw [matMul_swap, matVec_swapM, vecScale_swapMap]
      exact poly.oneValue_refl _
    -- the join's action at the far component
    have hY1sq : sqAt Y1.1 k1 := hq.2.1
    have hjact : poly.oneValue
        (matVec (matAdd (matScale (Pos.one * C.2) Y1.1)
          (matScale Y1.2 (matMul (transposeM B) C.1))) u1.1)
        (matVec (matScale (Y1.2 * (Pos.one * C.2)) A1) u1.1) := by
      have h0 : matOneValue
          (matScale Pos.one (matAdd (matScale (Pos.one * C.2) Y1.1)
            (matScale Y1.2 (matMul (transposeM B) C.1))))
          (matScale (Y1.2 * (Pos.one * C.2)) A1) := hjoin
      rw [matScale_one] at h0
      exact matVec_matOne _ _ u1.1 h0
    have hCt : (transposeM C.1).length = k1 :=
      length_transposeM C.1 (greenprod.rectAt_rows hwc.1)
        (by rw [greenprod.rectAt_len hwc.1]; exact hk0)
    have hBt_len : (transposeM B).length = k1 :=
      length_transposeM B (greenprod.rectAt_rows hslab.2.2.1)
        (by rw [greenprod.rectAt_len hslab.2.2.1]; exact hk0)
    have hd : poly.oneValue
        (poly.add
          (vecScale (BPair.ofPos (Pos.one * C.2)) (matVec Y1.1 u1.1))
          (vecScale (BPair.ofPos Y1.2)
            (matVec (matMul (transposeM B) C.1) u1.1)))
        (vecScale (BPair.ofPos (Y1.2 * (Pos.one * C.2)))
          (matVec A1 u1.1)) := by
      refine poly.oneValue_trans
        (poly.add_congr
          (poly.oneValue_symm (inertia.matVec_matScale _ Y1.1 u1.1))
          (poly.oneValue_symm
            (inertia.matVec_matScale _ (matMul (transposeM B) C.1)
              u1.1))) ?_
      refine poly.oneValue_trans ?_
        (poly.oneValue_trans hjact
          (inertia.matVec_matScale _ A1 u1.1))
      rw [← vecAdd_eq_polyAdd _ _ (by
        rw [matVec_length, matVec_length, length_matScale,
          length_matScale, length_matMul, sqAt_len hY1sq, hBt_len])]
      exact poly.oneValue_symm
        (matVec_add _ _ u1.1
          (rowsLen_mapRows _ _ _
            (by rw [hu1l]; exact rowsLen_of_sqAt hY1sq))
          (rowsLen_mapRows _ _ _
            (by rw [hu1l, ← hCt]
                exact rowsLen_matMul (transposeM B) C.1)))
    -- the next invariant, cleared of the witness's clearing
    have hnext : downRead Y1 A1 u1 (greenprod.appM (transposeM B) u) := by
      show poly.unitTail
        (poly.add (vecScale (BPair.ofPos (Y1.2 * u1.2))
            (matVec (transposeM B) u.1))
          (poly.add (vecScale (BPair.ofPos (Y1.2 * u.2))
              (matVec A1 u1.1))
            ((vecScale (BPair.ofPos u.2)
              (matVec Y1.1 u1.1)).map BPair.swap)))
      have hW1bal := vecAdd_swap_unitTail
        (vecScale (BPair.ofPos (u.2 * Y1.2))
          (matVec (matMul (transposeM B) C.1) u1.1))
      have hW2bal := vecAdd_swap_unitTail
        (vecScale (BPair.ofPos (u.2 * (Pos.one * C.2)))
          (matVec Y1.1 u1.1))
      rw [vecAdd_eq_polyAdd _ _ (by rw [ground.length_map])] at hW1bal
      rw [vecAdd_eq_polyAdd _ _ (by rw [ground.length_map])] at hW2bal
      have hbal := poly.unitTail_sum hW1bal hW2bal
      refine unitTail_unscale (BPair.ofPos C.2) (BPair.ofPos_off C.2) _ ?_
      rw [scaleAdd, scaleAdd]
      have c1 : poly.oneValue
          (vecScale (BPair.ofPos C.2)
            (vecScale (BPair.ofPos (Y1.2 * u1.2))
              (matVec (transposeM B) u.1)))
          ((vecScale (BPair.ofPos (u.2 * Y1.2))
            (matVec (matMul (transposeM B) C.1) u1.1)).map
              BPair.swap) := by
        refine poly.oneValue_trans
          (scaleFlat (rfl : C.2 * (Y1.2 * u1.2) = C.2 * (Y1.2 * u1.2))
            (matVec (transposeM B) u.1)) ?_
        refine poly.oneValue_trans
          (poly.oneValue_symm
            (scaleFlat (show Y1.2 * (C.2 * u1.2) = C.2 * (Y1.2 * u1.2)
                from ground.mul_left_comm Y1.2 C.2 u1.2)
              (matVec (transposeM B) u.1))) ?_
        refine poly.oneValue_trans
          (elim.vecScale_oneValue _ _ _ ha) ?_
        rw [vecScale_swapMap]
        refine poly.swapMap_oneValue ?_
        exact scaleFlat (ground.mul_comm Y1.2 u.2) _
      have c2 : poly.oneValue
          (vecScale (BPair.ofPos C.2)
            (vecScale (BPair.ofPos (Y1.2 * u.2)) (matVec A1 u1.1)))
          (poly.add
            (vecScale (BPair.ofPos (u.2 * (Pos.one * C.2)))
              (matVec Y1.1 u1.1))
            (vecScale (BPair.ofPos (u.2 * Y1.2))
              (matVec (matMul (transposeM B) C.1) u1.1))) := by
        refine poly.oneValue_trans
          (scaleFlat (rfl : C.2 * (Y1.2 * u.2) = C.2 * (Y1.2 * u.2))
            (matVec A1 u1.1)) ?_
        refine poly.oneValue_trans
          (poly.oneValue_symm
            (scaleFlat (show u.2 * (Y1.2 * (Pos.one * C.2))
                = C.2 * (Y1.2 * u.2) by
              rw [ground.one_mul,
                ground.mul_left_comm u.2 Y1.2 C.2,
                ground.mul_comm u.2 C.2,
                ground.mul_left_comm Y1.2 C.2 u.2])
              (matVec A1 u1.1))) ?_
        refine poly.oneValue_trans
          (elim.vecScale_oneValue _ _ _ (poly.oneValue_symm hd)) ?_
        rw [scaleAdd]
        exact poly.add_congr
          (scaleFlat rfl (matVec Y1.1 u1.1))
          (scaleFlat rfl (matVec (matMul (transposeM B) C.1) u1.1))
      have c3 : poly.oneValue
          (vecScale (BPair.ofPos C.2)
            ((vecScale (BPair.ofPos u.2)
              (matVec Y1.1 u1.1)).map BPair.swap))
          ((vecScale (BPair.ofPos (u.2 * (Pos.one * C.2)))
            (matVec Y1.1 u1.1)).map BPair.swap) := by
        rw [vecScale_swapMap]
        refine poly.swapMap_oneValue ?_
        exact scaleFlat (show C.2 * u.2 = u.2 * (Pos.one * C.2) by
          rw [ground.one_mul, ground.mul_comm C.2 u.2]) _
      refine poly.oneValue_unitTail
        (poly.oneValue_trans
          (poly.add_congr c1 (poly.add_congr c2 c3)) ?_) hbal
      refine poly.oneValue_trans
        (poly.add_congr (poly.oneValue_refl _)
          (poly.oneValue_symm (poly.add_join _ _ _))) ?_
      refine poly.oneValue_trans (poly.add_join _ _ _) ?_
      refine poly.oneValue_trans (poly.add_add_comm _ _ _ _) ?_
      exact poly.add_congr (poly.add_comm _ _) (poly.oneValue_refl _)
    show greenprod.vOneValueQ u (greenprod.appQ (greenprod.transfer C) u1)
      ∧ greenprod.teleDownWalk i Cs1 (u1 :: us1)
    exact ⟨hstep, ih A1 diag1 Bs Y1 Ys1 Cs1 k1 ns1 u1 us1 ws1
      (greenprod.appM (transposeM B) u)
      hslab.2.2.2 hq.2 hwc.2 hv.2 hhs1 hsr1 hbu1
      (Nat.lt_of_succ_lt_succ hjb) hnext⟩

/-- Below a far source the solve rides the head witnesses: at the
head recursion's certificate, the rows at unit sides below the
source hand each slab to the next transfer factor's image, the
descending telescope from the head, the source's slab within the
family. -/
theorem source_tele (diag off : List Mat) (Ys Cs : List greenprod.MatQ)
    (us ws : List greenprod.VecQ) (ns : List Nat) (jb : Nat)
    (hh : greenprod.headRead diag off Ys Cs ns)
    (hs : greenprod.solveRead diag off us ws ns)
    (hw : greenprod.supportAt ws jb)
    (hjb : jb < us.length) :
    greenprod.teleDown Cs us jb ns := by
  obtain ⟨hslab, hq, hwc, hseed, hsteps⟩ := hh
  obtain ⟨_, hvs, _, hrows⟩ := hs
  refine ⟨hwc, hvs, ?_⟩
  cases diag with
  | nil => exact (hslab : False).elim
  | cons A diag1 =>
  cases ns with
  | nil => exact (hslab : False).elim
  | cons k ns1 =>
  cases Ys with
  | nil => exact (hq : False).elim
  | cons Y Ys1 =>
  cases us with
  | nil => exact (hvs : False).elim
  | cons u us1 =>
  -- the seed's invariant at the vacant accumulator
  have hseed' : matOneValue (matScale Pos.one Y.1) (matScale Y.2 A) :=
    hseed
  have hY1 : poly.oneValue (matVec Y.1 u.1)
      (vecScale (BPair.ofPos Y.2) (matVec A u.1)) := by
    have h0 : matOneValue Y.1 (matScale Y.2 A) := by
      rw [matScale_one] at hseed'
      exact hseed'
    exact poly.oneValue_trans (matVec_matOne _ _ u.1 h0)
      (inertia.matVec_matScale Y.2 A u.1)
  have hinv0 : downRead Y A u ([], Pos.one) := by
    show poly.unitTail
      (poly.add (vecScale (BPair.ofPos (Y.2 * u.2)) [])
        (poly.add (vecScale (BPair.ofPos (Y.2 * Pos.one)) (matVec A u.1))
          ((vecScale (BPair.ofPos Pos.one)
            (matVec Y.1 u.1)).map BPair.swap)))
    have hb := vecAdd_swap_unitTail
      (vecScale (BPair.ofPos (Y.2 * Pos.one)) (matVec A u.1))
    rw [vecAdd_eq_polyAdd _ _ (by rw [ground.length_map])] at hb
    refine poly.oneValue_unitTail ?_ hb
    show poly.oneValue
      (poly.add (vecScale (BPair.ofPos (Y.2 * Pos.one)) (matVec A u.1))
        ((vecScale (BPair.ofPos Pos.one)
          (matVec Y.1 u.1)).map BPair.swap))
      _
    refine poly.add_congr (poly.oneValue_refl _) ?_
    refine poly.swapMap_oneValue ?_
    refine poly.oneValue_trans
      (elim.vecScale_oneValue _ _ _ hY1) ?_
    exact scaleFlat (show Pos.one * Y.2 = Y.2 * Pos.one by
      rw [ground.one_mul, ground.mul_one]) (matVec A u.1)
  exact walkDown jb A diag1 off Y Ys1 Cs k ns1 u us1 ws _
    hslab hq hwc hvs hsteps hrows
    (belowOfSupport jb ws hw) hjb hinv0

/-- The transfer factor's certificate prices its image's weight: at
`Tᵀ Gi T ⪯ λ² Gs` the image's form at its own slab's gram sits at
or below the certificate's square against the source's at the
source's, the clearing's square riding the factor — the factor
rectangular at the two slabs' orders. -/
theorem weight_step {o : Nat} (T : greenprod.MatQ) (Gi Gsr : Mat)
    (ln ld : Pos) (sp : Split o)
    (h : spectator.contractRead T Gi Gsr ln ld sp)
    (u : List BPair) (hu : u.length = o) :
    (inertia.quadForm Gi (matVec T.1 u)).scale (ld * ld)
      ≤ (inertia.quadForm Gsr u).scale (ln * ln * (T.2 * T.2)) := by
  obtain ⟨hGi, hTr, hGs, hsp, hpsd⟩ := h
  cases hT1 : T.1 with
  | nil =>
    rw [hT1] at hsp
    have hzn : ∀ X : elim.Mat,
        inertia.siteDatum X ([] : elim.Mat) = [] := fun X =>
      match X with | [] => rfl | _ :: _ => rfl
    have hy : inertia.matScale (ld * ld)
        (elim.matMul (transposeM ([] : elim.Mat))
          (elim.matMul Gi ([] : elim.Mat))) = ([] : elim.Mat) := rfl
    have hd := hsp.1
    rw [hy, hzn] at hd
    have ho : (0 : Nat) = o := sqAt_len hd
    have h0 : u.length = 0 := hu.trans ho.symm
    match u, h0 with
    | [], _ =>
      show BPair.scale (dotN [] _) (ld * ld)
        ≤ BPair.scale (dotN [] _) (ln * ln * (T.2 * T.2))
      exact ground.leB_congr (ground.unitScale (ld * ld))
        (ground.unitScale (ln * ln * (T.2 * T.2)))
        (ground.leB_refl BPair.unit)
  | cons r tl =>
    rw [hT1] at hTr hGi hsp
    have hTt : (transposeM (r :: tl)).length = o :=
      length_transposeM (r :: tl) hTr (Nat.succ_pos _)
    have hGT : (matMul Gi (r :: tl)).length = (r :: tl).length :=
      (length_matMul Gi (r :: tl)).trans (sqAt_len hGi)
    have hGTr : rowsLen o (matMul Gi (r :: tl)) :=
      rowsLen_cast hTt (rowsLen_matMul Gi (r :: tl))
    have hGTpos : 0 < (matMul Gi (r :: tl)).length := by
      rw [hGT]; exact Nat.succ_pos tl.length
    have hMl : (matMul (transposeM (r :: tl))
        (matMul Gi (r :: tl))).length = u.length := by
      rw [length_matMul, hTt, hu]
    have hMr : rowsLen u.length (matMul (transposeM (r :: tl))
        (matMul Gi (r :: tl))) := by
      rw [hu]
      exact rowsLen_cast
        (length_transposeM (matMul Gi (r :: tl)) hGTr hGTpos)
        (rowsLen_matMul (transposeM (r :: tl)) (matMul Gi (r :: tl)))
    have hGl : Gsr.length = u.length := (sqAt_len hGs).trans hu.symm
    have hGr : rowsLen u.length Gsr := by rw [hu]; exact rowsLen_of_sqAt hGs
    have hbase : ¬ (inertia.quadForm
        (siteDatum (matScale (ln * ln * (T.2 * T.2)) Gsr)
          (matScale (ld * ld) (matMul (transposeM (r :: tl))
            (matMul Gi (r :: tl))))) u
        < BPair.unit) := inertia.psd_all _ sp hsp hpsd u hu
    have hside := inertia.scaledSite_side hGl hGr hMl hMr hbase
    have hle := ground.leB_of_not_lt hside
    refine ground.leB_congr_left ?_ hle
    exact BPair.scale_congr (ld * ld)
      (BPair.oneValue_symm
        (inertia.congQuad Gi (r :: tl) (r :: tl).length o hGi hTr rfl
          u hu))

/-- The certificate list along the tail witnesses at the slab
grams: per transfer factor its contraction certificate at its own
two slabs' grams, each certificate's split at its source slab's
order — `lem:spectator`(ii)'s read at `lem:greenprod`'s split, the
gram list one gram per slab. -/
def capList : List Mat → List greenprod.MatQ →
    List ((k : Nat) × Pos × Pos × Split k) → Prop
  | _, [], [] => True
  | _, [], _ :: _ => False
  | _, _ :: _, [] => False
  | Gs, R :: Rs, c :: cs =>
    spectator.contractRead (greenprod.transfer R)
      (ground.getAt [] Gs 1) (ground.getAt [] Gs 0)
      c.2.1 c.2.2.1 c.2.2.2
      ∧ capList (Gs.drop 1) Rs cs

def decCapList :
    ∀ (Gs : List Mat) (Rs : List greenprod.MatQ)
      (cs : List ((k : Nat) × Pos × Pos × Split k)),
    Decidable (capList Gs Rs cs)
  | _, [], [] => isTrue trivial
  | _, [], _ :: _ => isFalse (fun h => h)
  | _, _ :: _, [] => isFalse (fun h => h)
  | Gs, _ :: Rs, _ :: cs =>
    @instDecidableAnd _ _ inferInstance (decCapList (Gs.drop 1) Rs cs)

instance (Gs : List Mat) (Rs : List greenprod.MatQ)
    (cs : List ((k : Nat) × Pos × Pos × Split k)) :
    Decidable (capList Gs Rs cs) :=
  decCapList Gs Rs cs

/-- The descending certificate list: per head witness the
contraction certificate reads the shallower slab's gram at the
image against the deeper slab's at the source. -/
def capListDown : List Mat → List greenprod.MatQ →
    List ((k : Nat) × Pos × Pos × Split k) → Prop
  | _, [], [] => True
  | _, [], _ :: _ => False
  | _, _ :: _, [] => False
  | Gs, C :: Cs, c :: cs =>
    spectator.contractRead (greenprod.transfer C)
      (ground.getAt [] Gs 0) (ground.getAt [] Gs 1)
      c.2.1 c.2.2.1 c.2.2.2
      ∧ capListDown (Gs.drop 1) Cs cs

def decCapListDown :
    ∀ (Gs : List Mat) (Cs : List greenprod.MatQ)
      (cs : List ((k : Nat) × Pos × Pos × Split k)),
    Decidable (capListDown Gs Cs cs)
  | _, [], [] => isTrue trivial
  | _, [], _ :: _ => isFalse (fun h => h)
  | _, _ :: _, [] => isFalse (fun h => h)
  | Gs, _ :: Cs, _ :: cs =>
    @instDecidableAnd _ _ inferInstance (decCapListDown (Gs.drop 1) Cs cs)

instance (Gs : List Mat) (Cs : List greenprod.MatQ)
    (cs : List ((k : Nat) × Pos × Pos × Split k)) :
    Decidable (capListDown Gs Cs cs) :=
  decCapListDown Gs Cs cs

/-- The certificates' first members' squared product, the chain's
upper clearing. -/
def prodN (cs : List ((k : Nat) × Pos × Pos × Split k)) : Pos :=
  ground.famFold (· * ·) Pos.one (fun c => c.2.1 * c.2.1) cs

/-- The certificates' second members' squared product, the chain's
lower clearing. -/
def prodD (cs : List ((k : Nat) × Pos × Pos × Split k)) : Pos :=
  ground.famFold (· * ·) Pos.one (fun c => c.2.2.1 * c.2.2.1) cs

/-- The certificate list's first members' product, the cap
polarization's crossing weight; the upper clearing `prodN` is its
square. -/
def certN (cs : List ((k : Nat) × Pos × Pos × Split k)) : Pos :=
  ground.famFold (· * ·) Pos.one (fun c => c.2.1) cs

/-- The certificate list's second members' product, the cap
polarization's clearing weight; the lower clearing `prodD` is its
square. -/
def certD (cs : List ((k : Nat) × Pos × Pos × Split k)) : Pos :=
  ground.famFold (· * ·) Pos.one (fun c => c.2.2.1) cs

/-- The upper clearing is the first members' fold squared. -/
theorem prodN_read : ∀ cs : List ((k : Nat) × Pos × Pos × Split k),
    prodN cs = certN cs * certN cs
  | [] => (ground.mul_one Pos.one).symm
  | c :: cs => by
    show c.2.1 * c.2.1 * prodN cs
      = c.2.1 * certN cs * (c.2.1 * certN cs)
    rw [prodN_read cs,
      ground.mul_mul_mul_comm c.2.1 (certN cs) c.2.1 (certN cs)]

/-- The lower clearing is the second members' fold squared. -/
theorem prodD_read : ∀ cs : List ((k : Nat) × Pos × Pos × Split k),
    prodD cs = certD cs * certD cs
  | [] => (ground.mul_one Pos.one).symm
  | c :: cs => by
    show c.2.2.1 * c.2.2.1 * prodD cs
      = c.2.2.1 * certD cs * (c.2.2.1 * certD cs)
    rw [prodD_read cs,
      ground.mul_mul_mul_comm c.2.2.1 (certD cs) c.2.2.1 (certD cs)]

/-- The second members' fold reads one value at either list
order. -/
theorem certD_rev (cs : List ((k : Nat) × Pos × Pos × Split k)) :
    certD cs.reverse = certD cs :=
  ground.famFold_rev (· * ·) Pos.one ground.mul_assoc ground.one_mul
    ground.mul_comm _ cs

/-- The step's clearings regroup at the squared members. -/
private theorem posE1 (a b L : Pos) :
    a * b * (a * b) * L = L * (b * b) * (a * a) := by
  rw [ground.mul_mul_mul_comm a b a b, ground.mul_comm (a * a * (b * b)) L,
    ground.mul_left_comm L (a * a) (b * b),
    ground.mul_comm (a * a) (L * (b * b))]

/-- The chain's lower clearings regroup at the shared square. -/
private theorem posE3 (PD U L V : Pos) :
    PD * U * (L * V) = L * PD * V * U := by
  rw [ground.mul_mul_mul_comm PD U L V, ground.mul_comm PD L,
    ground.mul_comm U V,
    ← ground.mul_assoc (L * PD) V U]

/-- The chain's upper clearings regroup at the shared square. -/
private theorem posE4 (N U PN W : Pos) :
    N * U * (PN * W) = N * PN * W * U := by
  rw [ground.mul_mul_mul_comm N U PN W, ground.mul_comm U W,
    ← ground.mul_assoc (N * PN) W U]

/-- The squared clearing against a datum is the datum's own
rescaling. -/
private theorem sqScale (a : Pos) (x : BPair) :
    (BPair.ofPos a * BPair.ofPos a * x).oneValue (x.scale (a * a)) :=
  BPair.oneValue_trans
    (BPair.mul_congr (BPair.ofPos_mul a a) (BPair.oneValue_refl x))
    (BPair.ofPos_scale (a * a) x)

/-- The chain's walk: along the telescope at the certificate list,
every depth's weight at its own slab's gram sits at or below the
head's against the certificates' product to that depth. -/
private theorem chainGo :
    ∀ (j : Nat) (Gs : List Mat) (Rs : List greenprod.MatQ)
      (cs : List ((k : Nat) × Pos × Pos × Split k))
      (us : List greenprod.VecQ) (ns : List Nat),
    greenprod.gramShape Gs ns → capList Gs Rs cs →
    greenprod.teleUp Rs us 0 ns → j < us.length →
    (inertia.quadForm (ground.getAt [] Gs j)
        (ground.getAt ([], Pos.one) us j).1).scale
        (prodD (cs.take j)
          * ((ground.getAt ([], Pos.one) us 0).2
            * (ground.getAt ([], Pos.one) us 0).2))
      ≤ (inertia.quadForm (ground.getAt [] Gs 0)
          (ground.getAt ([], Pos.one) us 0).1).scale
        (prodN (cs.take j)
          * ((ground.getAt ([], Pos.one) us j).2
            * (ground.getAt ([], Pos.one) us j).2)) := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _ _ _ _ _; exact ground.leB_refl _
  | succ i ih =>
    intro Gs Rs cs us ns hg hc hw hj
    cases us with
    | nil => exact absurd hj (Nat.not_lt_zero _)
    | cons u0 rest =>
    cases rest with
    | nil => exact absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero _)
    | cons u1 rest1 =>
    cases Rs with
    | nil => exact (hw.2.2 : False).elim
    | cons R Rs1 =>
    cases cs with
    | nil => exact (hc : False).elim
    | cons c cs1 =>
    cases ns with
    | nil => exact (hw.1 : False).elim
    | cons k ns' =>
    cases ns' with
    | nil => exact (hw.1 : False).elim
    | cons k' ns'' =>
    cases Gs with
    | nil => exact (hg : False).elim
    | cons G0 Gs1 =>
    cases Gs1 with
    | nil => exact (hg.2 : False).elim
    | cons G1 Gs2 =>
    obtain ⟨hwR, hwv, hwalk⟩ := hw
    have hih' : (inertia.quadForm
          (ground.getAt [] (G1 :: Gs2) i)
          (ground.getAt ([], Pos.one) (u1 :: rest1) i).1).scale
          (prodD (cs1.take i) * (u1.2 * u1.2))
        ≤ (inertia.quadForm G1 u1.1).scale
          (prodN (cs1.take i)
            * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
              * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2)) :=
      ih (G1 :: Gs2) Rs1 cs1 (u1 :: rest1) (k' :: ns'') hg.2 hc.2
        ⟨hwR.2, hwv.2, hwalk.2⟩ (Nat.lt_of_succ_lt_succ hj)
    have hck : c.1 = k :=
      (sqAt_len hc.1.2.2.1).symm.trans (sqAt_len hg.1)
    have hu0 : u0.1.length = c.1 := hwv.1.trans hck.symm
    have hstep : (inertia.quadForm G1
          (matVec (matSwap R.1) u0.1)).scale (c.2.2.1 * c.2.2.1)
        ≤ (inertia.quadForm G0 u0.1).scale
          (c.2.1 * c.2.1 * (R.2 * R.2)) :=
      weight_step (greenprod.transfer R) G1 G0 c.2.1 c.2.2.1 c.2.2.2
        hc.1 u0.1 hu0
    have hx1 : poly.oneValue (greenprod.vecScale (R.2 * u0.2) u1.1)
        (vecScale (BPair.ofPos (R.2 * u0.2)) u1.1) :=
      greenprod.vecScale_ofPos _ _
    have hx2 : poly.oneValue (greenprod.vecScale (R.2 * u0.2) u1.1)
        (vecScale (BPair.ofPos u1.2) (matVec (matSwap R.1) u0.1)) :=
      poly.oneValue_trans hwalk.1 (greenprod.vecScale_ofPos _ _)
    have hrel : ((inertia.quadForm G1 u1.1).scale
          (R.2 * u0.2 * (R.2 * u0.2))).oneValue
        ((inertia.quadForm G1 (matVec (matSwap R.1) u0.1)).scale
          (u1.2 * u1.2)) :=
      BPair.oneValue_trans
        (BPair.oneValue_symm
          (sqScale (R.2 * u0.2) (inertia.quadForm G1 u1.1)))
        (BPair.oneValue_trans
          (BPair.oneValue_symm
            (inertia.quadScaleVec G1 (BPair.ofPos (R.2 * u0.2)) u1.1 _ hx1))
          (BPair.oneValue_trans
            (inertia.quadScaleVec G1 (BPair.ofPos u1.2) _ _ hx2)
            (sqScale u1.2 _)))
    have e1 : ((inertia.quadForm G1 (matVec (matSwap R.1) u0.1)).scale
          (c.2.2.1 * c.2.2.1)).scale (u1.2 * u1.2)
        = ((inertia.quadForm G1 (matVec (matSwap R.1) u0.1)).scale
          (u1.2 * u1.2)).scale (c.2.2.1 * c.2.2.1) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_comm (c.2.2.1 * c.2.2.1) (u1.2 * u1.2)]
    have e2 : ((inertia.quadForm G1 u1.1).scale
          (R.2 * u0.2 * (R.2 * u0.2))).scale (c.2.2.1 * c.2.2.1)
        = ((inertia.quadForm G1 u1.1).scale
          (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2))).scale (R.2 * R.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        posE1 R.2 u0.2 (c.2.2.1 * c.2.2.1)]
    have e3 : ((inertia.quadForm G0 u0.1).scale
          (c.2.1 * c.2.1 * (R.2 * R.2))).scale (u1.2 * u1.2)
        = ((inertia.quadForm G0 u0.1).scale
          (c.2.1 * c.2.1 * (u1.2 * u1.2))).scale (R.2 * R.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_right_comm (c.2.1 * c.2.1) (R.2 * R.2) (u1.2 * u1.2)]
    have hone : (inertia.quadForm G1 u1.1).scale
          (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2))
        ≤ (inertia.quadForm G0 u0.1).scale
          (c.2.1 * c.2.1 * (u1.2 * u1.2)) :=
      ground.leB_of_scale (w := R.2 * R.2)
        (ground.leB_congr
          (BPair.oneValue_trans (BPair.oneValue_of_eq e1)
            (BPair.oneValue_trans
              (BPair.scale_congr (c.2.2.1 * c.2.2.1)
                (BPair.oneValue_symm hrel))
              (BPair.oneValue_of_eq e2)))
          (BPair.oneValue_of_eq e3)
          (ground.leB_scale hstep (u1.2 * u1.2)))
    show (inertia.quadForm
        (ground.getAt [] (G1 :: Gs2) i)
        (ground.getAt ([], Pos.one) (u1 :: rest1) i).1).scale
        (c.2.2.1 * c.2.2.1 * prodD (cs1.take i) * (u0.2 * u0.2))
      ≤ (inertia.quadForm G0 u0.1).scale
        (c.2.1 * c.2.1 * prodN (cs1.take i)
          * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
            * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))
    refine ground.leB_of_scale (w := u1.2 * u1.2) ?_
    refine ground.leB_congr (BPair.oneValue_of_eq ?_)
      (BPair.oneValue_of_eq ?_)
      (ground.leB_trans
        (ground.leB_congr_right (BPair.oneValue_of_eq ?_)
          (ground.leB_scale hih' (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2))))
        (ground.leB_scale hone
          (prodN (cs1.take i)
            * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
              * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))))
    · rw [BPair.scale_scale, BPair.scale_scale,
        posE3 (prodD (cs1.take i)) (u1.2 * u1.2) (c.2.2.1 * c.2.2.1)
          (u0.2 * u0.2)]
    · rw [BPair.scale_scale, BPair.scale_scale,
        posE4 (c.2.1 * c.2.1) (u1.2 * u1.2) (prodN (cs1.take i))
          ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
            * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2)]
    · rw [BPair.scale_scale, BPair.scale_scale, ground.mul_comm]

/-- The certificates' product prices the tail: along the telescope at
the certificate list, every depth's weight sits at or below the
head's against the certificates' product to that depth, the two
clearings' squares riding the comparison. -/
theorem weight_chain (Gs : List Mat) (Rs : List greenprod.MatQ)
    (cs : List ((k : Nat) × Pos × Pos × Split k))
    (us : List greenprod.VecQ) (ns : List Nat)
    (hg : greenprod.gramShape Gs ns) (hc : capList Gs Rs cs)
    (hw : greenprod.teleUp Rs us 0 ns)
    (j : Nat) (hj : j < us.length) :
    (inertia.quadForm (ground.getAt [] Gs j)
        (ground.getAt ([], Pos.one) us j).1).scale
        (prodD (cs.take j)
          * ((ground.getAt ([], Pos.one) us 0).2
            * (ground.getAt ([], Pos.one) us 0).2))
      ≤ (inertia.quadForm (ground.getAt [] Gs 0)
          (ground.getAt ([], Pos.one) us 0).1).scale
        (prodN (cs.take j)
          * ((ground.getAt ([], Pos.one) us j).2
            * (ground.getAt ([], Pos.one) us j).2)) :=
  chainGo j Gs Rs cs us ns hg hc hw hj

/-! Clause (i): the ground column and the read. -/

/-- The read of an observable at a ground, the pair of the two pairings:
the observable's against the gram's at the unit gram, the value the
cofactor. -/
def read (A : Mat) (psi : List BPair) : BPair × BPair :=
  (inertia.quadForm A psi, dotN psi psi)

/-- Two reads' gap, cross-multiplied: the later read's first member
against the earlier's second, less the earlier's first against the
later's second. -/
def readGap (r r' : BPair × BPair) : BPair := r'.1 * r.2 + (r.1 * r'.2).swap

/-- The ground column: at the kernel root the congruence's column is a
kernel vector of the gap, off the unit family, its self-pairing above
the sum's unit. -/
theorem ground_column {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l) (j : Nat) (hj : j < n)
    (dj : Pos) (gj : BPair)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (BPair.unit, dj, gj)) :
    poly.unitTail (matVec Et (matVec T.val (elim.idRow n j)))
      ∧ ¬ poly.unitTail (matVec T.val (elim.idRow n j))
      ∧ BPair.unit < dotN (matVec T.val (elim.idRow n j))
          (matVec T.val (elim.idRow n j)) := by
  have hTl : T.val.length = n := SqMat.rows T
  have hTr : rowsLen n T.val := rowsLen_of_sqAt T.shape
  have hTwr : rowsLen n Tw.val := rowsLen_of_sqAt Tw.shape
  have hjl : j < l.length := by rw [split.rootLen Et T Tw l hd]; exact hj
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  have hkern : poly.unitTail (matVec Et (matVec T.val (elim.idRow n j))) := by
    have he := split.eigenColumn Et (idMat n) T Tw l j BPair.unit gj dj hd
      hjl hroot
    exact unitTail_unscale (BPair.ofPos dj) (BPair.ofPos_off dj) _
      (poly.oneValue_unitTail he
        (elim.unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit) _))
  have hoff : ¬ poly.unitTail (matVec T.val (elim.idRow n j)) := by
    intro hu
    have h1 : poly.unitTail (matVec Tw.val (matVec T.val (elim.idRow n j))) :=
      matVec_null Tw.val _ hu
    have h2 : poly.oneValue (matVec Tw.val (matVec T.val (elim.idRow n j)))
        (vecScale (minor T.val) (elim.idRow n j)) :=
      poly.oneValue_trans
        (matVec_comp Tw.val T.val (elim.idRow n j) n hTr (length_idRow n j)
          (rowsLen_cast hTl.symm hTwr))
        (poly.oneValue_trans (matVec_matOne _ _ _ hd.2.2.1.2.2)
          (scaleId_act (minor T.val) n (elim.idRow n j) (length_idRow n j)))
    have h4 := poly.getAt_unitTail
      (unitTail_unscale (minor T.val) hdet _
        (poly.unitTail_oneValue_right h1 h2)) j
    rw [getAt_idRow n j j hj, if_pos rfl] at h4
    exact BPair.ofNat_one_off h4
  refine ⟨hkern, hoff, ?_⟩
  refine ground.ltOfLeOff (ground.leB_of_not_lt (dotN_self_side _)) ?_
  intro hz
  exact hoff (dotP_self_null _
    (BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) hz))

/-- The residual at a one-member list, read at the pairings: the
self-pairing's multiple of the vector against the pairing's multiple
of the member. -/
private theorem residOne (psi v : List BPair) (n : Nat)
    (hp : psi.length = n) (hv : v.length = n) :
    poly.oneValue (residD [psi] v)
      (vecAdd (vecScale (dotP psi psi) v)
        ((vecScale (dotP psi v) psi).map BPair.swap)) := by
  have hS : ((dotP psi psi * BPair.ofPos Pos.one).norm).oneValue
      (dotP psi psi) :=
    BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_one_read _)
  have hA : ((dotP psi v * BPair.ofPos Pos.one).norm).oneValue
      (dotP psi v) :=
    BPair.oneValue_trans (BPair.norm_oneValue _) (BPair.mul_one_read _)
  have hinner : poly.oneValue
      (vecAdd (vecScale ((dotP psi v * BPair.ofPos Pos.one).norm) psi)
        (vecScale (dotP psi psi) (vecScale BPair.unit v)))
      (vecScale (dotP psi v) psi) :=
    poly.oneValue_trans
      (vecAdd_null_right _ _
        (by rw [length_vecScale, length_vecScale, length_vecScale, hp, hv])
        (unitTail_vecScale _ _
          (elim.unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit) v)))
      (vecScale_congr hA psi)
  show poly.oneValue
      (vecAdd (vecScale ((dotP psi psi * BPair.ofPos Pos.one).norm) v)
        ((vecAdd (vecScale ((dotP psi v * BPair.ofPos Pos.one).norm) psi)
            (vecScale (dotP psi psi) (vecScale BPair.unit v))).map
          BPair.swap))
      (vecAdd (vecScale (dotP psi psi) v)
        ((vecScale (dotP psi v) psi).map BPair.swap))
  refine elim.vecAdd_congr2 _ _ _ _
    (by rw [length_vecScale, length_vecScale]) ?_
    (vecScale_congr hS v) (poly.swapMap_oneValue hinner)
  rw [ground.length_map, ground.length_map, length_vecScale, hp]
  exact length_vecAdd _ _ n (by rw [length_vecScale]; exact hp)
    (by rw [length_vecScale, length_vecScale]; exact hv)

/-- The cross-pairing of two one-member residual shapes, the four
blockwise pairings displayed at the two clearings. -/
private theorem crossPair (S A0 B0 : BPair) (psi v w : List BPair)
    (n : Nat) (hp : psi.length = n) (hv : v.length = n)
    (hw : w.length = n) :
    (dotP (vecAdd (vecScale S v) ((vecScale A0 psi).map BPair.swap))
        (vecAdd (vecScale S w)
          ((vecScale B0 psi).map BPair.swap))).oneValue
      ((S * (S * dotP v w) + (B0 * (S * dotP psi v)).swap)
        + ((A0 * (S * dotP psi w)).swap + A0 * (B0 * dotP psi psi))) := by
  have hAl : (vecScale S v).length = n := by rw [length_vecScale]; exact hv
  have hCl : (vecScale S w).length = n := by rw [length_vecScale]; exact hw
  have hBl : ((vecScale A0 psi).map BPair.swap).length = n := by
    rw [ground.length_map, length_vecScale]; exact hp
  have hDl : ((vecScale B0 psi).map BPair.swap).length = n := by
    rw [ground.length_map, length_vecScale]; exact hp
  have hYl : (vecAdd (vecScale S w)
      ((vecScale B0 psi).map BPair.swap)).length = n :=
    length_vecAdd _ _ n hCl hDl
  have eApsiV : (dotP (vecScale S v) psi).oneValue (S * dotP psi v) := by
    rw [dotP_comm (vecScale S v) psi]
    exact dotP_vecScale_right psi v S
  have eApsiW : (dotP (vecScale S w) psi).oneValue (S * dotP psi w) := by
    rw [dotP_comm (vecScale S w) psi]
    exact dotP_vecScale_right psi w S
  have eAA : (dotP (vecScale S v) (vecScale S w)).oneValue
      (S * (S * dotP v w)) := by
    refine BPair.oneValue_trans
      (dotP_vecScale_right (vecScale S v) w S) ?_
    refine BPair.mul_congr (BPair.oneValue_refl S) ?_
    rw [dotP_comm (vecScale S v) w, dotP_comm v w]
    exact dotP_vecScale_right w v S
  have eAB : (dotP (vecScale S v)
      ((vecScale B0 psi).map BPair.swap)).oneValue
      ((B0 * (S * dotP psi v)).swap) := by
    rw [dotP_swapMap (vecScale S v) (vecScale B0 psi)]
    exact ground.swap_congr
      (BPair.oneValue_trans
        (dotP_vecScale_right (vecScale S v) psi B0)
        (BPair.mul_congr (BPair.oneValue_refl B0) eApsiV))
  have eBA : (dotP (vecScale S w)
      ((vecScale A0 psi).map BPair.swap)).oneValue
      ((A0 * (S * dotP psi w)).swap) := by
    rw [dotP_swapMap (vecScale S w) (vecScale A0 psi)]
    exact ground.swap_congr
      (BPair.oneValue_trans
        (dotP_vecScale_right (vecScale S w) psi A0)
        (BPair.mul_congr (BPair.oneValue_refl A0) eApsiW))
  have eBB : (dotP ((vecScale A0 psi).map BPair.swap)
      ((vecScale B0 psi).map BPair.swap)).oneValue
      (A0 * (B0 * dotP psi psi)) := by
    rw [dotP_swapMap ((vecScale A0 psi).map BPair.swap)
        (vecScale B0 psi),
      dotP_comm ((vecScale A0 psi).map BPair.swap) (vecScale B0 psi),
      dotP_swapMap (vecScale B0 psi) (vecScale A0 psi),
      BPair.swap_swap]
    refine BPair.oneValue_trans
      (dotP_vecScale_right (vecScale B0 psi) psi A0) ?_
    refine BPair.mul_congr (BPair.oneValue_refl A0) ?_
    rw [dotP_comm (vecScale B0 psi) psi]
    exact dotP_vecScale_right psi psi B0
  refine BPair.oneValue_trans
    (dotP_vecAdd_left _ _ _ (Nat.le_of_eq (hYl.trans hAl.symm))
      (Nat.le_of_eq (hYl.trans hBl.symm))) ?_
  refine BPair.add_congr ?_ ?_
  · refine BPair.oneValue_trans
      (dotP_vecAdd_right _ _ _ (hCl.trans hDl.symm)) ?_
    exact BPair.add_congr eAA eAB
  · refine BPair.oneValue_trans
      (dotP_vecAdd_right _ _ _ (hCl.trans hDl.symm)) ?_
    refine BPair.add_congr ?_ eBB
    rw [dotP_comm ((vecScale A0 psi).map BPair.swap) (vecScale S w)]
    exact eBA

/-- The cross-pairing of two one-member residuals: the self-pairing
against the pairings' cross Gram determinant, `lem:groundreads`'s
connected pairing at its two probes. -/
theorem offLine_cross (psi v w : List BPair) (n : Nat)
    (hp : psi.length = n) (hv : v.length = n) (hw : w.length = n) :
    (dotN (residD [psi] v) (residD [psi] w)).oneValue
      (dotN psi psi
        * (dotN psi psi * dotN v w
          + (dotN psi v * dotN psi w).swap)) := by
  have hresv := residOne psi v n hp hv
  have hresw := residOne psi w n hp hw
  have hstep := crossPair (dotP psi psi) (dotP psi v) (dotP psi w)
    psi v w n hp hv hw
  have hcollect : ((dotP psi psi * (dotP psi psi * dotP v w)
        + (dotP psi w * (dotP psi psi * dotP psi v)).swap)
      + ((dotP psi v * (dotP psi psi * dotP psi w)).swap
        + dotP psi v * (dotP psi w * dotP psi psi))).oneValue
      (dotP psi psi
        * (dotP psi psi * dotP v w
          + (dotP psi v * dotP psi w).swap)) := by
    rw [BPair.mul_left_comm (dotP psi w) (dotP psi psi) (dotP psi v),
      BPair.mul_comm (dotP psi w) (dotP psi v),
      BPair.mul_left_comm (dotP psi v) (dotP psi psi) (dotP psi w),
      show dotP psi v * (dotP psi w * dotP psi psi)
          = dotP psi psi * (dotP psi v * dotP psi w) from by
        rw [← BPair.mul_assoc (dotP psi v) (dotP psi w) (dotP psi psi),
          BPair.mul_comm (dotP psi v * dotP psi w) (dotP psi psi)],
      BPair.left_distrib (dotP psi psi) (dotP psi psi * dotP v w)
        ((dotP psi v * dotP psi w).swap),
      ← BPair.mul_swap (dotP psi psi) (dotP psi v * dotP psi w)]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.swap_add_null
          (BPair.oneValue_refl
            (dotP psi psi * (dotP psi v * dotP psi w))))) ?_
    exact BPair.add_unit _
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_left _ _ _
      (poly.oneValue_trans hresv (poly.oneValue_refl _))) ?_
  refine BPair.oneValue_trans (dotP_oneValue_right _ _ _ hresw) ?_
  refine BPair.oneValue_trans hstep ?_
  refine BPair.oneValue_trans hcollect ?_
  exact BPair.mul_congr (BPair.oneValue_symm (dotN_read psi psi))
    (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_symm (dotN_read psi psi))
        (BPair.oneValue_symm (dotN_read v w)))
      (ground.swap_congr
        (BPair.mul_congr (BPair.oneValue_symm (dotN_read psi v))
          (BPair.oneValue_symm (dotN_read psi w)))))

/-- The off-line part's two reads at the one-member list: the residual
is the self-pairing's multiple of the vector against the pairing's
multiple of the member, and its self-pairing is the self-pairing
against the pairings' Gram determinant. -/
theorem offLine_reads (psi v : List BPair) (n : Nat)
    (hp : psi.length = n) (hv : v.length = n) :
    poly.oneValue (residD [psi] v)
      (vecAdd (vecScale (dotN psi psi) v)
        ((vecScale (dotN psi v) psi).map BPair.swap))
    ∧ (dotN (residD [psi] v) (residD [psi] v)).oneValue
      (dotN psi psi
        * (dotN psi psi * dotN v v + (dotN psi v * dotN psi v).swap)) := by
  have hres := residOne psi v n hp hv
  refine ⟨poly.oneValue_trans hres
      (elim.vecAdd_congr2 _ _ _ _
        (by rw [length_vecScale, length_vecScale])
        (by rw [ground.length_map, ground.length_map,
          length_vecScale, length_vecScale])
        (vecScale_congr (BPair.oneValue_symm (dotN_read psi psi)) v)
        (poly.swapMap_oneValue
          (vecScale_congr (BPair.oneValue_symm (dotN_read psi v)) psi))),
    offLine_cross psi v v n hp hv hv⟩

/-! Clause (iii): the gap on the kernel column's complement. -/

/-- The per-root comparison weighted by a square: the two clearings'
order passes a square weight. -/
private theorem sqTerm {V K cj : BPair} {p q : Pos}
    (h : V.scale p ≤ K.scale q) :
    ((V * (cj * cj)).scale p) ≤ ((K * (cj * cj)).scale q) := by
  rw [BPair.scale_mul_left V (cj * cj) p,
    BPair.scale_mul_left K (cj * cj) q,
    BPair.mul_comm (V.scale p) (cj * cj),
    BPair.mul_comm (K.scale q) (cj * cj)]
  exact ground.leB_mulR (ground.unitLeSq cj) h

/-- The kernel column's coordinate at a perpendicular vector: the
congruence's own coordinate at the kernel root reads the sum's
unit. -/
private theorem perpCoord {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (x : List BPair) (hx : x.length = n)
    (hperp : (dotN (matVec T.val (elim.idRow n j0)) x).oneValue BPair.unit) :
    (ground.getAt BPair.unit (matVec Tw.val x) j0).oneValue BPair.unit := by
  have hTl : T.val.length = n := SqMat.rows T
  have hTr : rowsLen n T.val := rowsLen_of_sqAt T.shape
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hIl : (idMat n).length = n := idMat_len n
  have hIr : rowsLen n (idMat n) := idMat_rows n
  have hlen : l.length = n := split.rootLen Et T Tw l hd
  have hc : (matVec Tw.val x).length = n := by rw [matVec_length, hTwl]
  have hdsl : (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)).length = n := by
    rw [ground.length_map]; exact hlen
  have hds0 : ground.getAt BPair.unit
      (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)) j0
      = (g0 * BPair.ofPos d0).norm := by
    rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit) BPair.unit _ l j0
      (by rw [hlen]; exact hj0), hroot0]
  have hg0 : BPair.unit < g0 :=
    split.scalePos Et T Tw l hd j0 (by rw [hlen]; exact hj0)
      BPair.unit g0 d0 hroot0
  have hds0off : ¬ ((g0 * BPair.ofPos d0).norm).oneValue BPair.unit :=
    ground.offOfUnitLt
      (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
        (BPair.oneValue_symm (BPair.norm_oneValue _))
        (ground.unitLtMul hg0 (ground.unitLtOfPos d0)))
  have hadj := split.adjAct Et T Tw l hd x hx
  have hleft : (dotP (matVec T.val (elim.idRow n j0))
      (matVec T.val (matVec Tw.val x))).oneValue BPair.unit := by
    refine BPair.oneValue_trans
      (dotP_oneValue_right _ _ _ hadj) ?_
    refine BPair.oneValue_trans (dotP_vecScale_right _ x (minor T.val)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans
          (BPair.oneValue_symm (dotN_read _ x)) hperp)) ?_
    exact BPair.mul_unit _
  have hwl : (matVec (split.diagM
      (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)))
      (matVec Tw.val x)).length = n := by
    rw [matVec_length, split.diagM_len]; exact hdsl
  have hrowl : (ground.getAt ([] : List BPair)
      (split.diagM (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)))
      j0).length = n := by
    rw [split.diagM_rowlen _ j0 (by rw [hdsl]; exact hj0)]; exact hdsl
  have hright : (dotP (matVec T.val (elim.idRow n j0))
      (matVec T.val (matVec Tw.val x))).oneValue
      (ground.getAt BPair.unit (matVec Tw.val x) j0
        * (g0 * BPair.ofPos d0).norm) := by
    refine BPair.oneValue_trans
      (dotP_oneValue_right _ _ _
        (poly.oneValue_symm
          (inertia.matVec_idMat n (matVec T.val (matVec Tw.val x))
            (by rw [matVec_length]; exact hTl)))) ?_
    refine BPair.oneValue_trans
      (inertia.congrPair (idMat n) T.val n n hIl hIr hTl hTr
        (elim.idRow n j0) (matVec Tw.val x) (length_idRow n j0) hc) ?_
    refine BPair.oneValue_trans
      (dotP_oneValue_right _ _ _
        (matVec_matOne _ _ (matVec Tw.val x) (split.gramMat Et T Tw l hd))) ?_
    rw [dotP_comm (elim.idRow n j0) _]
    refine BPair.oneValue_trans (dotP_idRow _ n j0 hwl hj0) ?_
    rw [getAt_matVec _ _ j0 (by rw [split.diagM_len, hdsl]; exact hj0)]
    refine BPair.oneValue_trans
      (elim.diagO_row _ (matVec Tw.val x) j0
        (by rw [hdsl]; exact hj0) (by rw [hc, hdsl])) ?_
    rw [hds0]
    exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
  refine ground.mulCancel hds0off ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.mul_comm (g0 * BPair.ofPos d0).norm
        (ground.getAt BPair.unit (matVec Tw.val x) j0))) ?_
  exact BPair.oneValue_trans
    (BPair.oneValue_trans (BPair.oneValue_symm hright) hleft)
    (BPair.oneValue_symm (BPair.mul_unit _))

/-- The clearance read off the kernel column: every root off the
kernel root sits at or beyond the level `[gn : gd]`, the root list's
fold at the cross-multiplied comparison. -/
def clearGo (j0 : Nat) (gn gd : Pos) :
    Nat → List (BPair × Pos × BPair) → Bool
  | _, [] => true
  | j, r :: t =>
    (Nat.beq j j0 || !(decide (r.1.scale gd < BPair.ofPos (gn * r.2.1))))
      && clearGo j0 gn gd (j + 1) t

def clearRead (l : List (BPair × Pos × BPair)) (j0 : Nat) (gn gd : Pos) :
    Prop :=
  clearGo j0 gn gd 0 l = true

instance (l : List (BPair × Pos × BPair)) (j0 : Nat) (gn gd : Pos) :
    Decidable (clearRead l j0 gn gd) :=
  inferInstanceAs (Decidable (_ = _))

/-- The clearance read's per-root clause: at every key off the kernel
root the root's cross-multiplied comparison against the level refuses
the lower side. -/
private theorem clearGo_at (j0 : Nat) (gn gd : Pos) :
    ∀ (t : List (BPair × Pos × BPair)) (k : Nat),
    clearGo j0 gn gd k t = true →
    ∀ i, i < t.length → k + i ≠ j0 → ∀ (nj gj : BPair) (dj : Pos),
      ground.getAt (BPair.unit, Pos.one, BPair.unit) t i = (nj, dj, gj) →
      ¬ (nj.scale gd < BPair.ofPos (gn * dj))
  | [], _, _, _, hi, _, _, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | r :: _, k, h, 0, _, hne, nj, gj, dj, hget => by
    have h1 := (ground.andSplitB h).1
    refine (ground.orSplitB h1).elim
      (fun hb => absurd (ground.beqEq k j0 hb) hne) (fun hb => ?_)
    have h2 := ground.notOfBang hb
    have e : r = (nj, dj, gj) := hget
    rw [e] at h2
    exact h2
  | _ :: t, k, h, i + 1, hi, hne, nj, gj, dj, hget =>
    clearGo_at j0 gn gd t (k + 1) (ground.andSplitB h).2 i
      (Nat.lt_of_succ_lt_succ hi)
      (fun h' => hne (by rw [Nat.add_succ, ← Nat.succ_add]; exact h'))
      nj gj dj hget

theorem clearRead_at {l : List (BPair × Pos × BPair)} {j0 : Nat}
    {gn gd : Pos} (h : clearRead l j0 gn gd) :
    ∀ j, j < l.length → j ≠ j0 → ∀ (nj gj : BPair) (dj : Pos),
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj) →
      ¬ (nj.scale gd < BPair.ofPos (gn * dj)) :=
  fun j hj hne => clearGo_at j0 gn gd l 0 h j hj
    (by rw [Nat.zero_add]; exact hne)

/-- The gap on the kernel column's complement: at every further root at
or beyond the clearance, a vector perpendicular to the kernel column
reads the gap's form at or beyond the clearance's multiple of its
self-pairing, the diagonalizing congruence's two folds term by
term. -/
theorem gap_perp {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (gn gd : Pos)
    (hcl : clearRead l j0 gn gd)
    (x : List BPair) (hx : x.length = n)
    (hperp : (dotN (matVec T.val (elim.idRow n j0)) x).oneValue BPair.unit) :
    (dotN x x).scale gn ≤ (inertia.quadForm Et x).scale gd := by
  have hgap : ∀ j, j < n → j ≠ j0 → ∀ (nj gj : BPair) (dj : Pos),
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj) →
      ¬ (nj.scale gd < BPair.ofPos (gn * dj)) :=
    fun j hj hne => clearRead_at hcl j
      (by rw [split.rootLen Et T Tw l hd]; exact hj) hne
  have hTl : T.val.length = n := SqMat.rows T
  have hTwl : Tw.val.length = n := SqMat.rows Tw
  have hEt : sqAt Et n := hd.1
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEt
  have hIr : rowsLen n (idMat n) := idMat_rows n
  have hlen : l.length = n := split.rootLen Et T Tw l hd
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  have hc : (matVec Tw.val x).length = n := by rw [matVec_length, hTwl]
  have hdsl : (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)).length = n := by
    rw [ground.length_map]; exact hlen
  have hcoord := perpCoord Et T Tw l hd j0 hj0 d0 g0 hroot0 x hx hperp
  have hterm : ∀ j, j < (l.map (fun r =>
        (r.2.2 * BPair.ofPos r.2.1).norm)).length →
      ((ground.getAt BPair.unit
            (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm)) j
          * ground.getAt BPair.unit
            (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val x))
            j).scale gn)
        ≤ ((ground.getAt BPair.unit (split.vDiagL Et T) j
            * ground.getAt BPair.unit
              (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val x))
              j).scale gd) := by
    intro j hj
    rw [hdsl] at hj
    have hjl : j < l.length := by rw [hlen]; exact hj
    have hcj : j < (matVec Tw.val x).length := by rw [hc]; exact hj
    rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit) BPair.unit _ l j hjl,
      split.vDiagL_get Et T j hj,
      ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
        (matVec Tw.val x) (matVec Tw.val x) j hcj hcj]
    refine ground.leB_congr_right
      (BPair.scale_congr gd
        (BPair.mul_congr
          (BPair.oneValue_symm
            (split.diagEntryV Et T Tw l hd j hj _ _ _ rfl))
          (BPair.oneValue_refl _))) ?_
    by_cases hjj : j = j0
    · have hnj : (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1
          = BPair.unit := by rw [hjj, hroot0]
      have hsq : (ground.getAt BPair.unit (matVec Tw.val x) j
          * ground.getAt BPair.unit (matVec Tw.val x) j).oneValue
          BPair.unit := by
        rw [hjj]
        exact BPair.oneValue_trans
          (BPair.mul_congr hcoord (BPair.oneValue_refl _))
          (BPair.oneValue_trans (BPair.unit_mul _) (BPair.oneValue_refl _))
      refine ground.leB_congr
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.scale_congr gn
              (BPair.oneValue_trans
                (BPair.mul_congr (BPair.oneValue_refl _) hsq)
                (BPair.mul_unit _)))
            (BPair.oneValue_symm (ground.unitScale gn))))
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.scale_congr gd
              (BPair.oneValue_trans
                (BPair.mul_congr (BPair.oneValue_refl _) hsq)
                (BPair.mul_unit _)))
            (BPair.oneValue_symm (ground.unitScale gd))))
        (ground.leB_refl BPair.unit)
    · refine sqTerm ?_
      have hle : BPair.ofPos (gn
          * (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1)
          ≤ ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1).scale gd :=
        ground.leB_of_not_lt (hgap j hj hjj _ _ _ rfl)
      have hgj : BPair.unit ≤ (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2 :=
        ground.leB_of_lt (split.scalePos Et T Tw l hd j hjl _ _ _ rfl)
      refine ground.leB_congr
        (BPair.oneValue_symm
          (BPair.oneValue_trans
            (BPair.scale_congr gn (BPair.norm_oneValue _))
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq
                (BPair.mul_scale _ _ gn).symm)
              (BPair.mul_congr (BPair.oneValue_refl _)
                (BPair.oneValue_trans
                  (BPair.scale_ofPos _ gn)
                  (BPair.oneValue_of_eq
                    (congrArg BPair.ofPos (ground.mul_comm _ gn))))))))
        (BPair.oneValue_symm
          (BPair.oneValue_of_eq
            (by rw [BPair.scale_mul_left, BPair.mul_comm])))
        (ground.leB_mulR hgj hle)
  have hfold : (dotP (l.map (fun r => (r.2.2 * BPair.ofPos r.2.1).norm))
        (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val x))).scale gn
      ≤ (dotP (split.vDiagL Et T)
        (List.zipWith (· * ·) (matVec Tw.val x)
          (matVec Tw.val x))).scale gd :=
    elim.dotP_le_of_leTerm gn gd _ _ _ _
      (by rw [hdsl, split.vDiagL_len]) hterm
  have hTc : (dotN (matVec T.val (matVec Tw.val x))
        (matVec T.val (matVec Tw.val x))).scale gn
      ≤ (inertia.quadForm Et (matVec T.val (matVec Tw.val x))).scale gd :=
    ground.leB_congr
      (BPair.scale_congr gn
        (BPair.oneValue_symm (split.quadFoldG Et T Tw l hd _ hc)))
      (BPair.scale_congr gd
        (BPair.oneValue_symm (split.quadFoldV Et T Tw l hd _ hc)))
      hfold
  have hadj := split.adjAct Et T Tw l hd x hx
  have hq1 : (inertia.quadForm Et (matVec T.val (matVec Tw.val x))).oneValue
      (minor T.val * minor T.val * inertia.quadForm Et x) :=
    inertia.quadScaleVec Et (minor T.val) x _ hadj
  have hidq : ∀ y : List BPair, y.length = n →
      (inertia.quadForm (idMat n) y).oneValue (dotN y y) := by
    intro y hy
    exact dotN_congrR y _ _ (inertia.matVec_idMat n y hy)
  have hq2 : (dotN (matVec T.val (matVec Tw.val x))
      (matVec T.val (matVec Tw.val x))).oneValue
      (minor T.val * minor T.val * dotN x x) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (hidq (matVec T.val (matVec Tw.val x))
          (by rw [matVec_length]; exact hTl))) ?_
    refine BPair.oneValue_trans
      (inertia.quadScaleVec (idMat n) (minor T.val) x _ hadj) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _) (hidq x hx)
  have hfin : (minor T.val * minor T.val * dotN x x).scale gn
      ≤ (minor T.val * minor T.val * inertia.quadForm Et x).scale gd :=
    ground.leB_congr (BPair.scale_congr gn hq2) (BPair.scale_congr gd hq1) hTc
  rw [← BPair.mul_scale (minor T.val * minor T.val) (dotN x x) gn,
    ← BPair.mul_scale (minor T.val * minor T.val)
      (inertia.quadForm Et x) gd,
    BPair.mul_comm (minor T.val * minor T.val) ((dotN x x).scale gn),
    BPair.mul_comm (minor T.val * minor T.val)
      ((inertia.quadForm Et x).scale gd)] at hfin
  exact ground.leB_unscale (ground.sq_pos hdet) hfin

/-! Clause (iii): the transport display at the off-line part. -/

/-- The cap's lower weight regroups at the clearance. -/
private theorem posLow (gn gd wn wd : Pos) :
    gn * wd * (wn * gd) * (2 * wd)
      = gd * (2 * (gn * (wd * wn) * wd)) := by
  rw [ground.mul_comm wn gd, ground.mul_mul_mul_comm gn wd gd wn,
    ground.mul_comm gn gd,
    ground.mul_assoc gd gn (wd * wn),
    ground.mul_assoc gd (gn * (wd * wn)) (2 * wd),
    ground.mul_left_comm (gn * (wd * wn)) 2 wd]

/-- The cap's upper weight regroups at the clearance. -/
private theorem posC (gn wn wd : Pos) :
    gn * (gn * (wd * wn) * wd) = gn * gn * (wd * wd) * wn := by
  rw [← ground.mul_assoc gn (gn * (wd * wn)) wd,
    ← ground.mul_assoc gn gn (wd * wn),
    ground.mul_assoc (gn * gn) (wd * wn) wd,
    ground.mul_right_comm wd wn wd,
    ← ground.mul_assoc (gn * gn) (wd * wd) wn]

/-- The doubled comparison closes: a datum at or below a second whose
doubled rescaling sits at or below the datum's own rescaling joined to
a remainder sits at or below that remainder. -/
private theorem closeStep {Z W B : BPair} {c : Pos}
    (h1 : Z ≤ W) (h2 : W.scale (2 * c) ≤ Z.scale c + B) :
    Z.scale c ≤ B := by
  refine ground.leB_cancelL (x := Z.scale c) ?_
  refine ground.leB_trans
    (ground.leB_congr_left
      (BPair.oneValue_of_eq (by rw [ground.two_mul c, BPair.scale_addW]))
      (ground.leB_scale h1 (2 * c))) h2

/-- The transport display at the off-line part: at the earlier gap's
clearance and the datum's cap the later ground's part off the earlier
line is priced by the later ground's weight, `γ'² ⟨φ, φ⟩ ≤ w² ⟨ψ̃, ψ̃⟩`
at the residual's clearing, the pencil identity read at the part with
the cap's polarization at the cofactor pair. -/
theorem transport_offLine {n : Nat} (Et Es D : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (gn gd : Pos)
    (hcl : clearRead l j0 gn gd)
    (htie : matOneValue Es (matAdd Et D))
    (wn wd : Pos) (spU spL : Split n)
    (hcap : capAt (matScale wd D) (matScale wn (idMat n)) spU spL)
    (psit : List BPair) (hpt : psit.length = n)
    (hker : poly.unitTail (matVec Es psit)) :
    (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
        (residD [matVec T.val (elim.idRow n j0)] psit)).scale
        (gn * gn * (wd * wd))
      ≤ ((dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0)))
          * dotN psit psit).scale (wn * wn * (gd * gd)) := by
  have hgap : ∀ j, j < n → j ≠ j0 → ∀ (nj gj : BPair) (dj : Pos),
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj) →
      ¬ (nj.scale gd < BPair.ofPos (gn * dj)) :=
    fun j hj hne => clearRead_at hcl j
      (by rw [split.rootLen Et T Tw l hd]; exact hj) hne
  have hTl : T.val.length = n := SqMat.rows T
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hd.1
  have hEtl : Et.length = n := sqAt_len hd.1
  have hDl : D.length = n :=
    (length_matScale wd D).symm.trans (sqAt_len hcap.1)
  have hDr : rowsLen n D :=
    rowsLen_of_sqAt (sqAt_matScale_reflect wd D hcap.1)
  have hpl : (matVec T.val (elim.idRow n j0)).length = n := by
    rw [matVec_length]; exact hTl
  have hRl : (residD [matVec T.val (elim.idRow n j0)] psit).length = n :=
    elim.length_residD n [matVec T.val (elim.idRow n j0)] psit
      ⟨hpl, trivial⟩ hpt
  have hgc := ground_column Et T Tw l hd j0 hj0 d0 g0 hroot0
  have hor := offLine_reads (matVec T.val (elim.idRow n j0)) psit n hpl hpt
  -- the residual is perpendicular to the kernel column
  have hperpR : (dotN (matVec T.val (elim.idRow n j0))
      (residD [matVec T.val (elim.idRow n j0)] psit)).oneValue BPair.unit :=
    BPair.oneValue_trans
      (dotN_read _ _)
      (elim.residD_perp n [matVec T.val (elim.idRow n j0)] psit
        ⟨hpl, trivial⟩ hpt
        (elim.perpAll_le1 [matVec T.val (elim.idRow n j0)] (Nat.le_refl 1))
        0 (Nat.succ_pos 0))
  -- the pencil identity at the later kernel vector
  have hsum : poly.unitTail
      (vecAdd (matVec Et psit) (matVec D psit)) :=
    poly.unitTail_oneValue_right hker
      (poly.oneValue_trans (matVec_matOne Es (matAdd Et D) psit htie)
        (matVec_add Et D psit (rowsLen_cast hpt.symm hEtr)
          (rowsLen_cast hpt.symm hDr)))
  have hEtD : (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
      (matVec Et psit)).oneValue
      ((dotN (residD [matVec T.val (elim.idRow n j0)] psit)
        (matVec D psit)).swap) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    refine BPair.oneValue_trans
      (BPair.swap_of_add_unit
        (v := dotP (residD [matVec T.val (elim.idRow n j0)] psit)
          (matVec D psit))
        (BPair.oneValue_trans
          (BPair.oneValue_symm
            (dotP_vecAdd_right _ (matVec Et psit) (matVec D psit)
              (by rw [matVec_length, matVec_length, hDl]; exact hEtl)))
          (dotP_null_tail_right _ _ hsum))) ?_
    exact ground.swap_congr (BPair.oneValue_symm (dotN_read _ _))
  -- the gap's form at the off-line part
  have hEtR : (inertia.quadForm Et
      (residD [matVec T.val (elim.idRow n j0)] psit)).oneValue
      (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
        * (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
            (matVec D psit)).swap) := by
    have hvec : poly.oneValue
        (matVec Et (residD [matVec T.val (elim.idRow n j0)] psit))
        (vecScale (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))) (matVec Et psit)) := by
      refine poly.oneValue_trans
        (matVec_congr Et _ _ hor.1) ?_
      rw [← vecScale_swap (dotN (matVec T.val (elim.idRow n j0)) psit)
        (matVec T.val (elim.idRow n j0))]
      refine poly.oneValue_trans
        (matVec_vecAdd Et n hEtr _ _
          (by rw [length_vecScale]; exact hpt)
          (by rw [length_vecScale]; exact hpl)) ?_
      refine poly.oneValue_trans
        (elim.vecAdd_congr2 _ _ _ _
          (by rw [matVec_length, length_vecScale, matVec_length])
          (by rw [matVec_length, length_vecScale, matVec_length])
          (matVec_vecScale_free Et _ psit)
          (matVec_vecScale_free Et _ _)) ?_
      exact vecAdd_null_right _ _
        (by rw [length_vecScale, length_vecScale, matVec_length,
          matVec_length])
        (unitTail_vecScale _ _ hgc.1)
    refine BPair.oneValue_trans (dotN_congrR _ _ _ hvec) ?_
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) hEtD)
  have hstep1 : (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
        (residD [matVec T.val (elim.idRow n j0)] psit)).scale gn
      ≤ (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
              (matVec D psit)).swap).scale gd :=
    ground.leB_congr_right (BPair.scale_congr gd hEtR)
      (gap_perp Et T Tw l hd j0 hj0 d0 g0 hroot0 gn gd hcl _ hRl hperpR)
  have hcp := truncation.cap_polar D wn wd spU spL hcap
    (residD [matVec T.val (elim.idRow n j0)] psit) psit hRl hpt
    (BPair.ofPos (gn * wd)) ((BPair.ofPos (wn * gd)
      * dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))).swap)
  have hstep2 : ((dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
              (matVec D psit)).swap).scale gd).scale
        (2 * (gn * (wd * wn) * wd))
      ≤ ((dotN (residD [matVec T.val (elim.idRow n j0)] psit)
            (residD [matVec T.val (elim.idRow n j0)] psit)).scale gn).scale
          (gn * (wd * wn) * wd)
        + (((dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))
            * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0)))
            * dotN psit psit).scale ((wn * gd) * (wn * gd))).scale wn := by
    refine ground.leB_congr ?_ ?_ hcp
    · rw [BPair.scale_scale, ← posLow gn gd wn wd,
        ← BPair.scale_scale
          (dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))
            * (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
                (matVec D psit)).swap)
          (gn * wd * (wn * gd)) (2 * wd)]
      refine BPair.scale_congr (2 * wd) ?_
      rw [show (BPair.ofPos (gn * wd)
            * (BPair.ofPos (wn * gd)
              * dotN (matVec T.val (elim.idRow n j0))
                (matVec T.val (elim.idRow n j0))).swap)
            * dotN (residD [matVec T.val (elim.idRow n j0)] psit)
                (matVec D psit)
          = (BPair.ofPos (gn * wd) * BPair.ofPos (wn * gd))
            * (dotN (matVec T.val (elim.idRow n j0))
                (matVec T.val (elim.idRow n j0))
              * (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
                  (matVec D psit)).swap) from by
        rw [BPair.mul_swap (BPair.ofPos (gn * wd)) _,
          BPair.swap_mul (BPair.ofPos (gn * wd)
            * (BPair.ofPos (wn * gd)
              * dotN (matVec T.val (elim.idRow n j0))
                (matVec T.val (elim.idRow n j0)))) _,
          ← BPair.mul_assoc (BPair.ofPos (gn * wd)) (BPair.ofPos (wn * gd)) _,
          BPair.mul_assoc (BPair.ofPos (gn * wd) * BPair.ofPos (wn * gd)) _ _,
          ← BPair.mul_swap (BPair.ofPos (gn * wd) * BPair.ofPos (wn * gd)) _,
          ← BPair.mul_swap
            (dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))) _]]
      exact BPair.oneValue_trans
        (BPair.mul_congr (BPair.ofPos_mul (gn * wd) (wn * gd))
          (BPair.oneValue_refl _))
        (BPair.ofPos_scale _ _)
    · rw [BPair.scale_scale
          (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
            (residD [matVec T.val (elim.idRow n j0)] psit))
          gn (gn * (wd * wn) * wd),
        posC gn wn wd,
        ← BPair.scale_scale
          (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
            (residD [matVec T.val (elim.idRow n j0)] psit))
          (gn * gn * (wd * wd)) wn,
        ← BPair.scale_add, ← ground.mul_mul_mul_comm gn wd gn wd]
      refine BPair.scale_congr wn (BPair.add_congr ?_ ?_)
      · exact BPair.oneValue_trans
          (BPair.mul_congr (BPair.ofPos_mul (gn * wd) (gn * wd))
            (BPair.oneValue_refl _))
          (BPair.ofPos_scale _ _)
      · rw [BPair.swap_mul_swap,
          BPair.mul_mul_mul_comm (BPair.ofPos (wn * gd)) _
          (BPair.ofPos (wn * gd)) _,
          BPair.mul_assoc (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)) _ _]
        exact BPair.oneValue_trans
          (BPair.mul_congr (BPair.ofPos_mul (wn * gd) (wn * gd))
            (BPair.oneValue_refl _))
          (BPair.ofPos_scale _ _)
  have hfin := closeStep hstep1 hstep2
  rw [BPair.scale_scale
      (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
        (residD [matVec T.val (elim.idRow n j0)] psit))
      gn (gn * (wd * wn) * wd),
    posC gn wn wd,
    ← BPair.scale_scale
      (dotN (residD [matVec T.val (elim.idRow n j0)] psit)
        (residD [matVec T.val (elim.idRow n j0)] psit))
      (gn * gn * (wd * wd)) wn,
    ground.mul_mul_mul_comm wn gd wn gd] at hfin
  exact ground.leB_of_scale hfin

/-! Clause (iii): the width between the two grounds' reads. -/

/-- The three off-line terms collect: the display's members, each
priced at the cofactor pair, sum to four copies of the head cap's
own bound. -/
private theorem masterAlg {s t a N Qx Qp Cc al be bc bn : BPair}
    (hdisp : N.oneValue ((Qx + (Cc + Cc)) + Qp * (a * a + (s * t).swap)))
    (hDpos : BPair.unit ≤ s * t + (a * a).swap)
    (hcore : al * be * (s * (s * t + (a * a).swap)) ≤ al * al * (s * s * t))
    (hbn : BPair.unit ≤ bn) (halbe : BPair.unit ≤ al * be)
    (hQx : bc * Qx ≤ bn * (s * (s * t + (a * a).swap)))
    (hQp : bc * Qp.swap ≤ bn * s)
    (hCc : bc * (al * be * (Cc + Cc))
      ≤ bn * (al * al * (s * s * t)) + bn * (al * al * (s * s * t))) :
    bc * (al * be) * N
      ≤ bn * (al * al * (s * s * t)) + bn * (al * al * (s * s * t))
        + bn * (al * al * (s * s * t)) + bn * (al * al * (s * s * t)) := by
  have hpull : ∀ z : BPair, bc * (al * be) * z = al * be * (bc * z) := by
    intro z
    rw [BPair.mul_comm bc (al * be), BPair.mul_assoc (al * be) bc z]
  have h1 : bc * (al * be) * Qx
      ≤ bn * (al * al * (s * s * t)) := by
    rw [hpull Qx]
    refine ground.leB_trans (ground.leB_mulR halbe hQx) ?_
    rw [BPair.mul_left_comm (al * be) bn (s * (s * t + (a * a).swap))]
    exact ground.leB_mulR hbn hcore
  have h3 : bc * (al * be) * (Qp * (a * a + (s * t).swap))
      ≤ bn * (al * al * (s * s * t)) := by
    rw [hpull (Qp * (a * a + (s * t).swap)),
      ← BPair.mul_assoc bc Qp (a * a + (s * t).swap),
      BPair.add_comm (a * a) ((s * t).swap),
      show ((s * t).swap + a * a) = (s * t + (a * a).swap).swap from by
        rw [← BPair.swap_add, BPair.swap_swap],
      BPair.mul_swap (bc * Qp) (s * t + (a * a).swap),
      ← BPair.swap_mul (bc * Qp) (s * t + (a * a).swap),
      ← BPair.mul_swap bc Qp,
      BPair.mul_comm (bc * Qp.swap) (s * t + (a * a).swap)]
    refine ground.leB_trans
      (ground.leB_mulR halbe
        (ground.leB_mulR hDpos hQp)) ?_
    rw [BPair.mul_left_comm (s * t + (a * a).swap) bn s,
      BPair.mul_left_comm (al * be) bn
        ((s * t + (a * a).swap) * s),
      BPair.mul_comm (s * t + (a * a).swap) s]
    exact ground.leB_mulR hbn hcore
  refine ground.leB_congr_left
    (BPair.oneValue_symm
      (BPair.mul_congr (BPair.oneValue_refl (bc * (al * be))) hdisp)) ?_
  rw [BPair.left_distrib (bc * (al * be)) (Qx + (Cc + Cc))
      (Qp * (a * a + (s * t).swap)),
    BPair.left_distrib (bc * (al * be)) Qx (Cc + Cc),
    BPair.add_assoc (bn * (al * al * (s * s * t)))
      (bn * (al * al * (s * s * t))) (bn * (al * al * (s * s * t)))]
  refine ground.leB_add (ground.leB_add h1 ?_) h3
  rw [BPair.mul_assoc bc (al * be) (Cc + Cc)]
  exact hCc

/-- Four copies of a datum read its rescaling by four. -/
private theorem fourB (K : BPair) :
    (K + K + K + K).oneValue (BPair.ofPos 4 * K) :=
  BPair.oneValue_symm
    (BPair.oneValue_trans (BPair.ofPos_scale 4 K)
      (BPair.oneValue_of_eq
        (by rw [show (4 : Pos) = Pos.one + Pos.one + Pos.one + Pos.one from rfl,
          BPair.scale_addW, BPair.scale_addW, BPair.scale_addW,
          BPair.scale_one])))

/-- The cap's polarization read at the doubled cross term. -/
private theorem polarTerm {n : Nat} (A : Mat) (cn cd : Pos)
    (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA')
    (u w : List BPair) (hu : u.length = n) (hw : w.length = n)
    (p q : BPair) :
    BPair.ofPos cd * (p * q * (dotN u (matVec A w) + dotN u (matVec A w)))
      ≤ BPair.ofPos cn * (p * p * dotN u u + q * q * dotN w w) := by
  refine ground.leB_congr ?_ ?_
    (truncation.cap_polar A cn cd spA spA' hA u w hu hw p q)
  · rw [← BPair.scale_scale (p * q * dotN u (matVec A w)) 2 cd,
      BPair.scale_two (p * q * dotN u (matVec A w)),
      ← BPair.left_distrib (p * q) (dotN u (matVec A w))
        (dotN u (matVec A w))]
    exact BPair.oneValue_symm
      (BPair.ofPos_scale cd (p * q * (dotN u (matVec A w)
        + dotN u (matVec A w))))
  · exact BPair.oneValue_symm
      (BPair.ofPos_scale cn (p * p * dotN u u + q * q * dotN w w))

/-- The width between the two grounds' reads at the head cap, read at
the ground data alone: the three off-line terms, each polarized at the
cofactor pair, close the bracket. -/
theorem readClose {n : Nat} (A : Mat) (cn cd : Pos)
    (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA')
    (psi psit : List BPair) (hpl : psi.length = n) (hpt : psit.length = n)
    (gn gd wn wd : Pos)
    (hw : BPair.ofPos (wn * gd) ≤ BPair.ofPos (gn * wd))
    (hs : BPair.unit < dotN psi psi)
    (htrans : (dotN (residD [psi] psit) (residD [psi] psit)).scale
          (gn * gn * (wd * wd))
        ≤ ((dotN psi psi * dotN psi psi) * dotN psit psit).scale
          (wn * wn * (gd * gd))) :
    (windowsep.mag (readGap (read A psi) (read A psit))).scale (gn * wd * cd)
      ≤ (dotN psi psi * dotN psit psit).scale (4 * (cn * wn * gd)) := by
  have hAl : A.length = n := (length_matScale cd A).symm.trans (sqAt_len hA.1)
  have hAr : rowsLen n A := rowsLen_of_sqAt (sqAt_matScale_reflect cd A hA.1)
  have hsymA := inertia.sym_of_capScale A cn cd spA spA' hA
  have hRl : (residD [psi] psit).length = n :=
    elim.length_residD n [psi] psit ⟨hpl, trivial⟩ hpt
  have hul : (vecScale (dotN psi psit) psi).length = n := by
    rw [length_vecScale]; exact hpl
  have hor := offLine_reads psi psit n hpl hpt
  have hbe : BPair.unit ≤ BPair.ofPos (gn * wd) :=
    ground.leB_of_lt (ground.unitLtOfPos (gn * wd))
  have hbn : BPair.unit ≤ BPair.ofPos cn :=
    ground.leB_of_lt (ground.unitLtOfPos cn)
  have halbe : BPair.unit ≤ BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd) :=
    ground.leB_of_lt
      (ground.unitLtMul (ground.unitLtOfPos (wn * gd))
        (ground.unitLtOfPos (gn * wd)))
  have halal : BPair.unit ≤ BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd) :=
    ground.leB_of_lt
      (ground.unitLtMul (ground.unitLtOfPos (wn * gd))
        (ground.unitLtOfPos (wn * gd)))
  have hYpos : BPair.unit ≤ dotN (residD [psi] psit) (residD [psi] psit) :=
    ground.leB_of_not_lt (dotN_self_side _)
  have hsq : dotN psi psit * dotN psi psit ≤ dotN psi psi * dotN psit psit :=
    coeff.dotN_sq_le psi psit (hpl.trans hpt.symm)
  have hDpos : BPair.unit ≤ dotN psi psi * dotN psit psit
      + (dotN psi psit * dotN psi psit).swap :=
    ground.leB_unit_add hsq
  have hbebe : (BPair.ofPos (gn * wd) * BPair.ofPos (gn * wd)).oneValue
      (BPair.ofPos (gn * gn * (wd * wd))) :=
    BPair.oneValue_trans (BPair.ofPos_mul (gn * wd) (gn * wd))
      (BPair.oneValue_of_eq
        (congrArg BPair.ofPos (ground.mul_mul_mul_comm gn wd gn wd)))
  have halal2 : (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)).oneValue
      (BPair.ofPos (wn * wn * (gd * gd))) :=
    BPair.oneValue_trans (BPair.ofPos_mul (wn * gd) (wn * gd))
      (BPair.oneValue_of_eq
        (congrArg BPair.ofPos (ground.mul_mul_mul_comm wn gd wn gd)))
  have hLc : (BPair.ofPos (gn * wd) * BPair.ofPos (gn * wd)
        * dotN (residD [psi] psit) (residD [psi] psit)).oneValue
      ((dotN (residD [psi] psit) (residD [psi] psit)).scale
        (gn * gn * (wd * wd))) :=
    BPair.oneValue_trans
      (BPair.mul_congr hbebe (BPair.oneValue_refl _))
      (BPair.ofPos_scale (gn * gn * (wd * wd)) _)
  have hRc : (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
        * (dotN psi psi * dotN psi psi * dotN psit psit)).oneValue
      ((dotN psi psi * dotN psi psi * dotN psit psit).scale
        (wn * wn * (gd * gd))) :=
    BPair.oneValue_trans
      (BPair.mul_congr halal2 (BPair.oneValue_refl _))
      (BPair.ofPos_scale (wn * wn * (gd * gd)) _)
  have hT1 : BPair.ofPos (gn * wd) * BPair.ofPos (gn * wd)
        * dotN (residD [psi] psit) (residD [psi] psit)
      ≤ BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
        * (dotN psi psi * dotN psi psi * dotN psit psit) :=
    ground.leB_congr (BPair.oneValue_symm hLc) (BPair.oneValue_symm hRc)
      htrans
  have hstepbe : BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd)
        * dotN (residD [psi] psit) (residD [psi] psit)
      ≤ BPair.ofPos (gn * wd) * BPair.ofPos (gn * wd)
        * dotN (residD [psi] psit) (residD [psi] psit) := by
    rw [BPair.mul_comm (BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd))
        (dotN (residD [psi] psit) (residD [psi] psit)),
      BPair.mul_comm (BPair.ofPos (gn * wd) * BPair.ofPos (gn * wd))
        (dotN (residD [psi] psit) (residD [psi] psit)),
      BPair.mul_comm (BPair.ofPos (wn * gd)) (BPair.ofPos (gn * wd))]
    exact ground.leB_mulR hYpos
      (ground.leB_mulR hbe hw)
  have hcore : BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd)
        * (dotN psi psi * (dotN psi psi * dotN psit psit
          + (dotN psi psit * dotN psi psit).swap))
      ≤ BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
        * (dotN psi psi * dotN psi psi * dotN psit psit) :=
    ground.leB_congr_left
      (BPair.mul_congr (BPair.oneValue_refl _) hor.2)
      (ground.leB_trans hstepbe hT1)
  have hsp : poly.oneValue
      (vecAdd (residD [psi] psit) (vecScale (dotN psi psit) psi))
      (vecScale (dotN psi psi) psit) := by
    refine poly.oneValue_trans
      (elim.vecAdd_congr2 _ _ _ _
        (by rw [hRl, length_vecAdd _ _ n
            (by rw [length_vecScale]; exact hpt)
            (by rw [ground.length_map, length_vecScale]; exact hpl)])
        rfl hor.1 (poly.oneValue_refl _)) ?_
    rw [vecAdd_assoc, vecAdd_comm
      ((vecScale (dotN psi psit) psi).map BPair.swap)
      (vecScale (dotN psi psit) psi)]
    exact vecAdd_null_right _ _
      (by rw [length_vecScale, length_vecAdd _ _ n
          (by rw [length_vecScale]; exact hpl)
          (by rw [ground.length_map, length_vecScale]; exact hpl), hpt])
      (vecAdd_swap_unitTail (vecScale (dotN psi psit) psi))
  have h4 : (dotN psi psi * dotN psi psi * inertia.quadForm A psit).oneValue
      ((inertia.quadForm A (residD [psi] psit)
          + dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit)))
        + (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
          + dotN psi psit * dotN psi psit * inertia.quadForm A psi)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (inertia.quadScaleVec A (dotN psi psi) psit _
          (poly.oneValue_refl _))) ?_
    refine BPair.oneValue_trans
      (inertia.quadForm_congr A (poly.oneValue_symm hsp)) ?_
    refine BPair.oneValue_trans
      (inertia.quadAdd A n hAr hAl (residD [psi] psit)
        (vecScale (dotN psi psit) psi) hRl hul) ?_
    exact BPair.add_congr
      (BPair.add_congr (BPair.oneValue_refl _)
        (elim.dotN_sym_flip A n hAr hAl hsymA (vecScale (dotN psi psit) psi)
          (residD [psi] psit) hul hRl))
      (BPair.add_congr (BPair.oneValue_refl _)
        (inertia.quadScaleVec A (dotN psi psit) psi _
          (poly.oneValue_refl _)))
  have hexp : dotN psi psi * readGap (read A psi) (read A psit)
      = dotN psi psi * dotN psi psi * inertia.quadForm A psit
        + (inertia.quadForm A psi
            * (dotN psi psi * dotN psit psit)).swap := by
    show dotN psi psi * (inertia.quadForm A psit * dotN psi psi
        + (inertia.quadForm A psi * dotN psit psit).swap) = _
    rw [BPair.left_distrib,
      BPair.mul_left_comm (dotN psi psi) (inertia.quadForm A psit)
        (dotN psi psi),
      BPair.mul_comm (inertia.quadForm A psit)
        (dotN psi psi * dotN psi psi),
      BPair.mul_swap (dotN psi psi)
        (inertia.quadForm A psi * dotN psit psit),
      BPair.mul_left_comm (dotN psi psi) (inertia.quadForm A psi)
        (dotN psit psit)]
  have hregroup :
      ((inertia.quadForm A (residD [psi] psit)
            + dotN (vecScale (dotN psi psit) psi)
                (matVec A (residD [psi] psit)))
          + (dotN (vecScale (dotN psi psit) psi)
                (matVec A (residD [psi] psit))
            + dotN psi psit * dotN psi psit * inertia.quadForm A psi))
        + (inertia.quadForm A psi
            * (dotN psi psi * dotN psit psit)).swap
      = (inertia.quadForm A (residD [psi] psit)
          + (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
            + dotN (vecScale (dotN psi psit) psi)
                (matVec A (residD [psi] psit))))
        + inertia.quadForm A psi
          * (dotN psi psit * dotN psi psit
            + (dotN psi psi * dotN psit psit).swap) := by
    rw [BPair.left_distrib (inertia.quadForm A psi)
        (dotN psi psit * dotN psi psit)
        ((dotN psi psi * dotN psit psit).swap),
      BPair.mul_comm (inertia.quadForm A psi)
        (dotN psi psit * dotN psi psit),
      BPair.mul_swap (inertia.quadForm A psi)
        (dotN psi psi * dotN psit psit),
      BPair.add_assoc (inertia.quadForm A (residD [psi] psit))
        (dotN (vecScale (dotN psi psit) psi)
          (matVec A (residD [psi] psit)))
        (dotN (vecScale (dotN psi psit) psi)
            (matVec A (residD [psi] psit))
          + dotN psi psit * dotN psi psit * inertia.quadForm A psi),
      ← BPair.add_assoc
        (dotN (vecScale (dotN psi psit) psi)
          (matVec A (residD [psi] psit)))
        (dotN (vecScale (dotN psi psit) psi)
          (matVec A (residD [psi] psit)))
        (dotN psi psit * dotN psi psit * inertia.quadForm A psi),
      ← BPair.add_assoc (inertia.quadForm A (residD [psi] psit))
        (dotN (vecScale (dotN psi psit) psi)
            (matVec A (residD [psi] psit))
          + dotN (vecScale (dotN psi psit) psi)
            (matVec A (residD [psi] psit)))
        (dotN psi psit * dotN psi psit * inertia.quadForm A psi),
      BPair.add_assoc
        (inertia.quadForm A (residD [psi] psit)
          + (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
            + dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))))
        (dotN psi psit * dotN psi psit * inertia.quadForm A psi)
        ((inertia.quadForm A psi
          * (dotN psi psi * dotN psit psit)).swap)]
  have hdisp : (dotN psi psi
        * readGap (read A psi) (read A psit)).oneValue
      ((inertia.quadForm A (residD [psi] psit)
          + (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
            + dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))))
        + inertia.quadForm A psi
          * (dotN psi psit * dotN psi psit
            + (dotN psi psi * dotN psit psit).swap)) := by
    rw [hexp, ← hregroup]
    exact BPair.add_congr h4 (BPair.oneValue_refl _)
  have hdispS : (dotN psi psi
        * readGap (read A psi) (read A psit)).swap.oneValue
      (((inertia.quadForm A (residD [psi] psit)).swap
          + ((dotN (vecScale (dotN psi psit) psi)
                (matVec A (residD [psi] psit))).swap
            + (dotN (vecScale (dotN psi psit) psi)
                (matVec A (residD [psi] psit))).swap))
        + (inertia.quadForm A psi).swap
          * (dotN psi psit * dotN psi psit
            + (dotN psi psi * dotN psit psit).swap)) := by
    refine BPair.oneValue_trans (ground.swap_congr hdisp)
      (BPair.oneValue_of_eq ?_)
    rw [← BPair.swap_add
        (inertia.quadForm A (residD [psi] psit)
          + (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
            + dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))))
        (inertia.quadForm A psi
          * (dotN psi psit * dotN psi psit
            + (dotN psi psi * dotN psit psit).swap)),
      ← BPair.swap_add (inertia.quadForm A (residD [psi] psit))
        (dotN (vecScale (dotN psi psit) psi)
            (matVec A (residD [psi] psit))
          + dotN (vecScale (dotN psi psit) psi)
            (matVec A (residD [psi] psit))),
      ← BPair.swap_add
        (dotN (vecScale (dotN psi psit) psi)
          (matVec A (residD [psi] psit)))
        (dotN (vecScale (dotN psi psit) psi)
          (matVec A (residD [psi] psit))),
      ← BPair.swap_mul (inertia.quadForm A psi)
        (dotN psi psit * dotN psi psit
          + (dotN psi psi * dotN psit psit).swap)]
  have hcapR := truncation.cap_read A cn cd spA spA' hA (residD [psi] psit) hRl
  have hcapP := truncation.cap_read A cn cd spA spA' hA psi hpl
  have hQx1 : BPair.ofPos cd * inertia.quadForm A (residD [psi] psit)
      ≤ BPair.ofPos cn * (dotN psi psi * (dotN psi psi * dotN psit psit
        + (dotN psi psit * dotN psi psit).swap)) :=
    ground.leB_congr_right
      (BPair.mul_congr (BPair.oneValue_refl _) hor.2) hcapR.1
  have hQx2 : BPair.ofPos cd
        * (inertia.quadForm A (residD [psi] psit)).swap
      ≤ BPair.ofPos cn * (dotN psi psi * (dotN psi psi * dotN psit psit
        + (dotN psi psit * dotN psi psit).swap)) :=
    ground.leB_congr_right
      (BPair.mul_congr (BPair.oneValue_refl _) hor.2) hcapR.2
  have ha1 : dotN psi psit * dotN psi psit * dotN psi psi
      ≤ dotN psi psi * dotN psi psi * dotN psit psit := by
    rw [BPair.mul_comm (dotN psi psit * dotN psi psit) (dotN psi psi),
      BPair.mul_assoc (dotN psi psi) (dotN psi psi) (dotN psit psit)]
    exact ground.leB_mulR (ground.leB_of_lt hs) hsq
  have hAA : BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
        * dotN (vecScale (dotN psi psit) psi)
          (vecScale (dotN psi psit) psi)
      ≤ BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
        * (dotN psi psi * dotN psi psi * dotN psit psit) :=
    ground.leB_congr_left
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (elim.dotN_vecScale_self (dotN psi psit) psi)))
      (ground.leB_mulR halal ha1)
  have hRHSc : BPair.ofPos cn
        * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
            * dotN (vecScale (dotN psi psit) psi)
              (vecScale (dotN psi psit) psi)
          + BPair.ofPos (gn * wd) * BPair.ofPos (gn * wd)
            * dotN (residD [psi] psit) (residD [psi] psit))
      ≤ BPair.ofPos cn * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
          * (dotN psi psi * dotN psi psi * dotN psit psit))
        + BPair.ofPos cn * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
          * (dotN psi psi * dotN psi psi * dotN psit psit)) :=
    ground.leB_congr_right
      (BPair.oneValue_of_eq (BPair.left_distrib (BPair.ofPos cn) _ _))
      (ground.leB_mulR hbn (ground.leB_add hAA hT1))
  have hCc1 : BPair.ofPos cd
        * (BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd)
          * (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
            + dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))))
      ≤ BPair.ofPos cn * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
          * (dotN psi psi * dotN psi psi * dotN psit psit))
        + BPair.ofPos cn * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
          * (dotN psi psi * dotN psi psi * dotN psit psit)) :=
    ground.leB_trans
      (polarTerm A cn cd spA spA' hA (vecScale (dotN psi psit) psi)
        (residD [psi] psit) hul hRl (BPair.ofPos (wn * gd))
        (BPair.ofPos (gn * wd)))
      hRHSc
  have hCc2 : BPair.ofPos cd
        * (BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd)
          * ((dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))).swap
            + (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))).swap))
      ≤ BPair.ofPos cn * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
          * (dotN psi psi * dotN psi psi * dotN psit psit))
        + BPair.ofPos cn * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
          * (dotN psi psi * dotN psi psi * dotN psit psit)) := by
    refine ground.leB_trans
      (ground.leB_congr (BPair.oneValue_of_eq ?_)
        (BPair.oneValue_of_eq ?_)
        (polarTerm A cn cd spA spA' hA (vecScale (dotN psi psit) psi)
          (residD [psi] psit) hul hRl (BPair.ofPos (wn * gd))
          (BPair.ofPos (gn * wd)).swap))
      hRHSc
    · rw [BPair.mul_swap (BPair.ofPos (wn * gd)) (BPair.ofPos (gn * wd)),
        BPair.swap_mul (BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd))
          (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
            + dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))),
        ← BPair.mul_swap
          (BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd))
          (dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))
            + dotN (vecScale (dotN psi psit) psi)
              (matVec A (residD [psi] psit))),
        ← BPair.swap_add
          (dotN (vecScale (dotN psi psit) psi)
            (matVec A (residD [psi] psit)))
          (dotN (vecScale (dotN psi psit) psi)
            (matVec A (residD [psi] psit)))]
    · rw [BPair.swap_mul_swap (BPair.ofPos (gn * wd))
        (BPair.ofPos (gn * wd))]
  have hM1 := masterAlg hdisp hDpos hcore hbn halbe hQx1 hcapP.2 hCc1
  have hM2 := masterAlg hdispS hDpos hcore hbn halbe hQx2 hcapP.1 hCc2
  have hmag := windowsep.mag_mul_le hM1 hM2
  have hmagmul : (windowsep.mag (dotN psi psi
        * readGap (read A psi) (read A psit))).oneValue
      (dotN psi psi
        * windowsep.mag (readGap (read A psi) (read A psit))) :=
    BPair.oneValue_trans (windowsep.mag_mul _ _)
      (BPair.oneValue_of_eq
        (by rw [windowsep.mag_unitLe (ground.leB_of_lt hs)]))
  have hmag2 := ground.leB_congr_left
    (BPair.mul_congr (BPair.oneValue_refl _) hmagmul) hmag
  have hmag3 := ground.leB_congr_right
    (fourB (BPair.ofPos cn * (BPair.ofPos (wn * gd) * BPair.ofPos (wn * gd)
      * (dotN psi psi * dotN psi psi * dotN psit psit)))) hmag2
  rw [BPair.mul_assoc (BPair.ofPos cd)
      (BPair.ofPos (wn * gd) * BPair.ofPos (gn * wd))
      (dotN psi psi
        * windowsep.mag (readGap (read A psi) (read A psit))),
    BPair.mul_assoc (BPair.ofPos (wn * gd)) (BPair.ofPos (gn * wd))
      (dotN psi psi
        * windowsep.mag (readGap (read A psi) (read A psit))),
    BPair.mul_left_comm (BPair.ofPos (gn * wd)) (dotN psi psi)
      (windowsep.mag (readGap (read A psi) (read A psit))),
    BPair.mul_left_comm (BPair.ofPos (wn * gd)) (dotN psi psi)
      (BPair.ofPos (gn * wd)
        * windowsep.mag (readGap (read A psi) (read A psit))),
    BPair.mul_left_comm (BPair.ofPos cd) (dotN psi psi)
      (BPair.ofPos (wn * gd) * (BPair.ofPos (gn * wd)
        * windowsep.mag (readGap (read A psi) (read A psit)))),
    BPair.mul_left_comm (BPair.ofPos cd) (BPair.ofPos (wn * gd))
      (BPair.ofPos (gn * wd)
        * windowsep.mag (readGap (read A psi) (read A psit))),
    BPair.mul_assoc (BPair.ofPos (wn * gd)) (BPair.ofPos (wn * gd))
      (dotN psi psi * dotN psi psi * dotN psit psit),
    BPair.mul_assoc (dotN psi psi) (dotN psi psi) (dotN psit psit),
    BPair.mul_left_comm (BPair.ofPos (wn * gd)) (dotN psi psi)
      (dotN psi psi * dotN psit psit),
    BPair.mul_left_comm (BPair.ofPos (wn * gd)) (dotN psi psi)
      (BPair.ofPos (wn * gd) * (dotN psi psi * dotN psit psit)),
    BPair.mul_left_comm (BPair.ofPos cn) (dotN psi psi)
      (BPair.ofPos (wn * gd) * (BPair.ofPos (wn * gd)
        * (dotN psi psi * dotN psit psit))),
    BPair.mul_left_comm (BPair.ofPos cn) (BPair.ofPos (wn * gd))
      (BPair.ofPos (wn * gd) * (dotN psi psi * dotN psit psit)),
    BPair.mul_left_comm (BPair.ofPos 4) (dotN psi psi)
      (BPair.ofPos (wn * gd) * (BPair.ofPos cn
        * (BPair.ofPos (wn * gd) * (dotN psi psi * dotN psit psit)))),
    BPair.mul_left_comm (BPair.ofPos 4) (BPair.ofPos (wn * gd))
      (BPair.ofPos cn
        * (BPair.ofPos (wn * gd) * (dotN psi psi * dotN psit psit)))]
    at hmag3
  have hcut := ground.leB_unscale_left (ground.unitLtOfPos (wn * gd))
    (ground.leB_unscale_left hs hmag3)
  refine ground.leB_congr ?_ ?_ hcut
  · refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.ofPos_scale (gn * wd * cd)
          (windowsep.mag (readGap (read A psi) (read A psit))))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_symm
          (BPair.ofPos_mul (gn * wd) cd)) (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_of_eq
      (by rw [BPair.mul_comm (BPair.ofPos (gn * wd)) (BPair.ofPos cd),
        BPair.mul_assoc (BPair.ofPos cd) (BPair.ofPos (gn * wd))
          (windowsep.mag (readGap (read A psi) (read A psit)))])
  · refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.ofPos_scale (4 * (cn * wn * gd))
          (dotN psi psi * dotN psit psit))) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_symm (BPair.ofPos_mul 4 (cn * wn * gd)))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq
              (congrArg BPair.ofPos (ground.mul_assoc cn wn gd)))
            (BPair.oneValue_symm (BPair.ofPos_mul cn (wn * gd)))))
        (BPair.oneValue_refl _)) ?_
    exact BPair.oneValue_of_eq
      (by rw [BPair.mul_assoc (BPair.ofPos 4)
          (BPair.ofPos cn * BPair.ofPos (wn * gd))
          (dotN psi psi * dotN psit psit),
        BPair.mul_assoc (BPair.ofPos cn) (BPair.ofPos (wn * gd))
          (dotN psi psi * dotN psit psit)])

/-- The order read back: a datum off the lower side of a comparison
sits at or beyond the other member. -/
private theorem ltB_of_not_le {a b : BPair} (h : ¬ (a ≤ b)) : b < a :=
  Decidable.of_not_not (fun hn => h (ground.leB_of_not_lt hn))

/-- The width at the head cap alone: each read sits at or below the
cap against its self-pairing, so the reads' gap sits at or below
twice the cap against the two self-pairings, and at a cap beyond the
clearance that is below the display's right side. -/
theorem readCrude {n : Nat} (A : Mat) (cn cd : Pos)
    (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA')
    (psi psit : List BPair) (hpl : psi.length = n) (hpt : psit.length = n)
    (gn gd wn wd : Pos)
    (hw : BPair.ofPos (gn * wd) ≤ BPair.ofPos (wn * gd)) :
    (windowsep.mag (readGap (read A psi) (read A psit))).scale (gn * wd * cd)
      ≤ (dotN psi psi * dotN psit psit).scale (4 * (cn * wn * gd)) := by
  have hs : BPair.unit ≤ dotN psi psi := ground.leB_of_not_lt (dotN_self_side psi)
  have ht : BPair.unit ≤ dotN psit psit :=
    ground.leB_of_not_lt (dotN_self_side psit)
  have hcn : BPair.unit ≤ BPair.ofPos cn := ground.leB_of_lt (ground.unitLtOfPos cn)
  have hK : BPair.unit ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit) :=
    ground.unitLeMul hcn (ground.unitLeMul hs ht)
  have eN : readGap (read A psi) (read A psit)
      = inertia.quadForm A psit * dotN psi psi
        + (inertia.quadForm A psi * dotN psit psit).swap := rfl
  obtain ⟨hp1, hp2⟩ := truncation.cap_read A cn cd spA spA' hA psi hpl
  obtain ⟨ht1, ht2⟩ := truncation.cap_read A cn cd spA spA' hA psit hpt
  have hcnt : BPair.unit ≤ BPair.ofPos cn * dotN psit psit := ground.unitLeMul hcn ht
  have hcns : BPair.unit ≤ BPair.ofPos cn * dotN psi psi := ground.unitLeMul hcn hs
  have eK1 : (BPair.ofPos cn * dotN psit psit * dotN psi psi).oneValue
      (BPair.ofPos cn * (dotN psi psi * dotN psit psit)) := by
    rw [BPair.mul_assoc, BPair.mul_comm (dotN psit psit) (dotN psi psi)]
    exact BPair.oneValue_refl _
  have eK2 : (BPair.ofPos cn * dotN psi psi * dotN psit psit).oneValue
      (BPair.ofPos cn * (dotN psi psi * dotN psit psit)) := by
    rw [BPair.mul_assoc]; exact BPair.oneValue_refl _
  have hA1 : BPair.ofPos cd * (inertia.quadForm A psit * dotN psi psi)
      ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit) := by
    rw [← BPair.mul_assoc]
    exact ground.leB_congr_right eK1
      (ground.leB_mul_mono hs hcnt ht1 (ground.leB_refl _))
  have hA2 : BPair.ofPos cd * (inertia.quadForm A psit * dotN psi psi).swap
      ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit) := by
    rw [← BPair.swap_mul, ← BPair.mul_assoc]
    exact ground.leB_congr_right eK1
      (ground.leB_mul_mono hs hcnt ht2 (ground.leB_refl _))
  have hB1 : BPair.ofPos cd * (inertia.quadForm A psi * dotN psit psit)
      ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit) := by
    rw [← BPair.mul_assoc]
    exact ground.leB_congr_right eK2
      (ground.leB_mul_mono ht hcns hp1 (ground.leB_refl _))
  have hB2 : BPair.ofPos cd * (inertia.quadForm A psi * dotN psit psit).swap
      ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit) := by
    rw [← BPair.swap_mul, ← BPair.mul_assoc]
    exact ground.leB_congr_right eK2
      (ground.leB_mul_mono ht hcns hp2 (ground.leB_refl _))
  have hN1 : BPair.ofPos cd * readGap (read A psi) (read A psit)
      ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit)
        + BPair.ofPos cn * (dotN psi psi * dotN psit psit) := by
    rw [eN, BPair.left_distrib]
    exact ground.leB_add hA1 hB2
  have hN2 : BPair.ofPos cd * (readGap (read A psi) (read A psit)).swap
      ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit)
        + BPair.ofPos cn * (dotN psi psi * dotN psit psit) := by
    rw [eN, ← BPair.swap_add, BPair.swap_swap, BPair.left_distrib]
    exact ground.leB_add hA2 hB1
  have hM := windowsep.mag_mul_le hN1 hN2
  have hKK : BPair.unit ≤ BPair.ofPos cn * (dotN psi psi * dotN psit psit)
      + BPair.ofPos cn * (dotN psi psi * dotN psit psit) :=
    ground.leB_trans hK (ground.leB_congr_left
      (BPair.add_unit (BPair.ofPos cn * (dotN psi psi * dotN psit psit)))
      (ground.leB_add (ground.leB_refl _) hK))
  have hgw : BPair.unit ≤ BPair.ofPos (gn * wd) :=
    ground.leB_of_lt (ground.unitLtOfPos (gn * wd))
  have hwg : BPair.unit ≤ BPair.ofPos (wn * gd) :=
    ground.leB_of_lt (ground.unitLtOfPos (wn * gd))
  have hstep1 : (windowsep.mag (readGap (read A psi) (read A psit))).scale
        (gn * wd * cd)
      ≤ BPair.ofPos (wn * gd)
        * (BPair.ofPos cn * (dotN psi psi * dotN psit psit)
          + BPair.ofPos cn * (dotN psi psi * dotN psit psit)) := by
    refine ground.leB_congr_left
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.ofPos_mul (gn * wd) cd) (BPair.oneValue_refl _))
        (BPair.ofPos_scale (gn * wd * cd) _)) ?_
    rw [BPair.mul_assoc]
    exact ground.leB_trans (ground.leB_mulR hgw hM)
      (ground.leB_mul_mono hKK hwg hw (ground.leB_refl _))
  refine ground.leB_trans hstep1 ?_
  have hfour : BPair.ofPos cn * (dotN psi psi * dotN psit psit)
        + BPair.ofPos cn * (dotN psi psi * dotN psit psit)
      ≤ BPair.ofPos 4 * (BPair.ofPos cn * (dotN psi psi * dotN psit psit)) :=
    ground.leB_congr (BPair.oneValue_trans
        (BPair.add_congr (BPair.add_unit _) (BPair.oneValue_refl _))
        (BPair.add_unit _))
      (fourB (BPair.ofPos cn * (dotN psi psi * dotN psit psit)))
      (ground.leB_add (ground.leB_add (ground.leB_refl _) hK) hK)
  refine ground.leB_trans (ground.leB_mulR hwg hfour) ?_
  refine ground.leB_congr_right ?_ (ground.leB_refl _)
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.ofPos_scale cn _))) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl _) (BPair.ofPos_scale 4 _)) ?_
  refine BPair.oneValue_trans (BPair.ofPos_scale (wn * gd) _) ?_
  rw [BPair.scale_scale, BPair.scale_scale,
    show cn * (4 * (wn * gd)) = 4 * (cn * wn * gd) by
      rw [ground.mul_left_comm cn 4 (wn * gd), ground.mul_assoc cn wn gd]]
  exact BPair.oneValue_refl _

/-- The width between the two grounds' reads of an observable at the
head cap: at the datum's cap at or below the clearance the two reads'
gap is priced at `γ' w_ω ≤ 4 c_A w`, the reads' pairing members three
off-line terms each polarized at the cofactor pair `[w : γ']`. -/
theorem transport_read {n : Nat} (Et Es D A : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (gn gd : Pos)
    (hcl : clearRead l j0 gn gd)
    (htie : matOneValue Es (matAdd Et D))
    (wn wd : Pos) (spU spL : Split n)
    (hcap : capAt (matScale wd D) (matScale wn (idMat n)) spU spL)
    (cn cd : Pos) (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA')
    (psit : List BPair) (hpt : psit.length = n)
    (hker : poly.unitTail (matVec Es psit)) :
    (windowsep.mag (readGap (read A (matVec T.val (elim.idRow n j0)))
        (read A psit))).scale (gn * wd * cd)
      ≤ (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN psit psit).scale (4 * (cn * wn * gd)) :=
  Decidable.byCases
    (p := BPair.ofPos (wn * gd) ≤ BPair.ofPos (gn * wd))
    (fun hw => readClose A cn cd spA spA' hA (matVec T.val (elim.idRow n j0)) psit
      (by rw [matVec_length]; exact SqMat.rows T) hpt gn gd wn wd hw
      (ground_column Et T Tw l hd j0 hj0 d0 g0 hroot0).2.2
      (transport_offLine Et Es D T Tw l hd j0 hj0 d0 g0 hroot0 gn gd hcl
        htie wn wd spU spL hcap psit hpt hker))
    (fun hw => readCrude A cn cd spA spA' hA (matVec T.val (elim.idRow n j0)) psit
      (by rw [matVec_length]; exact SqMat.rows T) hpt gn gd wn wd
      (ground.leB_of_lt (ltB_of_not_le hw)))

/-- The couplings at the depths below the last: at a slab walk every
depth with a successor key names its own coupling. -/
private theorem offAt {diag off : List Mat} {ns : List Nat}
    (h : greenprod.slabShape diag off ns) (i : Nat)
    (hi : i + 1 < ns.length) : i < off.length := by
  have hlen : ns.length = off.length + 1 :=
    (greenprod.slabShape_len_ns h).trans
      (greenprod.slabShape_len_off h).symm
  rw [hlen] at hi
  exact Nat.lt_of_succ_lt_succ hi

/-- The leading segment's trailing part occupied names a key within
the family's own count. -/
private theorem takeDropOcc {a : Type} : ∀ (m i : Nat) (l : List a),
    0 < ((l.take m).drop i).length → i < l.length
  | 0, 0, _, h => absurd h (Nat.lt_irrefl 0)
  | 0, _ + 1, _, h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, 0, [], h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, 0, _ :: _, _ => Nat.succ_pos _
  | _ + 1, _ + 1, [], h => absurd h (Nat.lt_irrefl 0)
  | m + 1, i + 1, _ :: t, h =>
    Nat.succ_lt_succ (takeDropOcc m i t h)

/-- A key within the family's count leaves the trailing part
occupied. -/
private theorem dropPos {a : Type} : ∀ (i : Nat) (l : List a),
    i < l.length → 0 < (l.drop i).length
  | 0, [], h => absurd h (Nat.not_lt_zero 0)
  | 0, _ :: _, _ => Nat.succ_pos _
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | i + 1, _ :: t, h => dropPos i t (Nat.lt_of_succ_lt_succ h)

/-- The tied walk at an occupied certificate list runs on occupied
witness families. -/
private theorem walkOcc {dn : BPair} {sn sd cn cd : Pos}
    {Gs : List Mat} {Y0' Y0 : greenprod.MatQ}
    {Cs Cs' Ys Ys' : List greenprod.MatQ}
    {certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)}
    (h : spectator.driftWalk dn sn sd Gs cn cd Y0' Y0 Cs Cs' Ys Ys' certs)
    (hc : 0 < certs.length) : 0 < Cs.length ∧ 0 < Cs'.length :=
  have hl := spectator.driftWalk_len dn sn sd Gs cn cd Y0' Y0
    Cs Cs' Ys Ys' certs h
  ⟨hl.1 ▸ hc, hl.2.1 ▸ hc⟩

/-- At the unit-gram list of the gap slabs' own orders the tied
walk's last block reads the head slab's identity: the walk's list
counts place the perturbation slab at or below the factor count,
and the reversed segment's last entry is the head slab's own
order. -/
private theorem unitGram_last {dn : BPair} {sn sd cn cd : Pos}
    {Y0' Y0 : greenprod.MatQ} {Xs Rs Xs' Rs' : List greenprod.MatQ}
    {w0 j : Nat} {ns : List Nat}
    {certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2)}
    (hw : spectator.driftWalk dn sn sd
      ((((ns.take (w0 + 1)).drop j).reverse).map inertia.idMat) cn cd
      Y0' Y0 ((Rs.take w0).drop j).reverse
      ((Rs'.take w0).drop j).reverse ((Xs.take w0).drop j).reverse
      ((Xs'.take w0).drop j).reverse certs)
    (hjw : j < w0) (hjR : j < Rs.length)
    (hXn : Xs.length = ns.length) (hRn : Rs.length + 1 = ns.length) :
    ground.getAt ([] : Mat)
      ((((ns.take (w0 + 1)).drop j).reverse).map inertia.idMat)
      certs.length = inertia.idMat (ground.getAt 0 ns j) := by
  have hlen := spectator.driftWalk_len dn sn sd
    ((((ns.take (w0 + 1)).drop j).reverse).map inertia.idMat) cn cd
    Y0' Y0 _ _ _ _ certs hw
  have hCs : ((Rs.take w0).drop j).length = certs.length :=
    (ground.length_reverse ((Rs.take w0).drop j)).symm.trans hlen.1
  have hYs : ((Xs.take w0).drop j).length = certs.length :=
    (ground.length_reverse ((Xs.take w0).drop j)).symm.trans hlen.2.2.1
  have hw0 : w0 ≤ Rs.length := by
    refine (Nat.lt_or_ge Rs.length w0).elim (fun hlt => ?_) (fun h => h)
    have hXw : Xs.length ≤ w0 := by
      rw [hXn, ← hRn]
      exact hlt
    rw [ground.take_of_le Rs w0 (Nat.le_of_lt hlt)] at hCs
    rw [ground.take_of_le Xs w0 hXw] at hYs
    have hdR := ground.length_drop j Rs (Nat.le_of_lt hjR)
    have hjX : j ≤ Xs.length := by
      rw [hXn, ← hRn]
      exact Nat.le_of_lt (Nat.lt_succ_of_lt hjR)
    have hdX := ground.length_drop j Xs hjX
    rw [hCs] at hdR
    rw [hYs, hXn, ← hRn] at hdX
    exact absurd (hdR.symm.trans hdX) (Nat.succ_ne_self Rs.length).symm
  have htR : (Rs.take w0).length = w0 := ground.length_take w0 Rs hw0
  have hjt : j ≤ (Rs.take w0).length := by
    rw [htR]
    exact Nat.le_of_lt hjw
  have hdT := ground.length_drop j (Rs.take w0) hjt
  rw [hCs, htR] at hdT
  have hw1 : w0 + 1 ≤ ns.length := by
    rw [← hRn]
    exact Nat.succ_le_succ hw0
  have htN : (ns.take (w0 + 1)).length = w0 + 1 :=
    ground.length_take (w0 + 1) ns hw1
  have hjN : j ≤ (ns.take (w0 + 1)).length := by
    rw [htN]
    exact Nat.le_of_lt (Nat.lt_succ_of_lt hjw)
  have hdN := ground.length_drop j (ns.take (w0 + 1)) hjN
  rw [htN] at hdN
  have hLlen : ((ns.take (w0 + 1)).drop j).length
      = certs.length + 1 := by
    refine ground.addCancelR j ?_
    rw [hdN, ← hdT, Nat.add_right_comm]
  have hbound : certs.length
      < (((ns.take (w0 + 1)).drop j).reverse).length := by
    rw [ground.length_reverse, hLlen]
    exact Nat.lt_succ_self certs.length
  have h1 := ground.getAt_map (0 : Nat) ([] : Mat) inertia.idMat
    (((ns.take (w0 + 1)).drop j).reverse) certs.length hbound
  have h2 : ground.getAt 0 (((ns.take (w0 + 1)).drop j).reverse)
      certs.length = ground.getAt 0 ((ns.take (w0 + 1)).drop j) 0 :=
    ground.getAt_reverse 0 ((ns.take (w0 + 1)).drop j)
      certs.length 0 hLlen.symm
  have h3 : ground.getAt 0 ((ns.take (w0 + 1)).drop j) 0
      = ground.getAt 0 (ns.take (w0 + 1)) j :=
    ground.getAt_drop 0 j (ns.take (w0 + 1)) 0
  have h4 : ground.getAt 0 (ns.take (w0 + 1)) j
      = ground.getAt 0 ns j :=
    ground.getAt_take 0 (w0 + 1) ns j (Nat.lt_succ_of_lt hjw)
  exact h1.trans (congrArg inertia.idMat (h2.trans (h3.trans h4)))

/-- Two windows entering at their own roots' site data at one shared
clearing instantiate the transport display at the two heads decimated
onto the depths at or below the observable's depth `j`: the heads
differ at the drift along the leading diagonal and at the depth-`j`
pivot, the pivot's deviation capped by the tied walk's accumulated
pair with the drift's own cap the transported bracket's datum, and
the composed cap prices the width of the one bracket holding the two
heads' reads of an observable at the head cap. -/
theorem window_transport {o : Nat} (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List greenprod.MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2))
    (hshare : spectator.driftShareRead diag off diag' off' Xs Rs Xs' Rs'
      w0 j ns dn cn cd sn sd
      ((((ns.take (w0 + 1)).drop j).reverse).map inertia.idMat) certs)
    (hocc : 0 < certs.length) (hjw : j < w0)
    (X X' : greenprod.MatQ)
    (hX : X = ground.getAt greenprod.dM Xs j)
    (hX' : X' = ground.getAt greenprod.dM Xs' j)
    (ho : ground.getAt 0 ns j = o)
    (k n : Nat)
    (hk : k = ground.sumNat (List.take j ns))
    (hn : n = k + o)
    (T Tw : SqMat n) (l : List (BPair × Pos × BPair))
    (hd : split.diagRead (matScale X'.2 (greenprod.headM diag off X j))
      (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : clearRead l j0 gn gd)
    (wrn wrd : Pos) (spD spD' : Split n)
    (hdrift : capAt
      (matScale wrd (matScaleB (dn.scale (X.2 * X'.2))
        (inertia.headId k o)))
      (matScale wrn (idMat n)) spD spD')
    (spP spP' : Split n)
    (hUP : splitRead (siteDatum
      (matScale ((spectator.driftFold cn cd sn sd certs).1
        * (X'.2 * X.2)) (idMat n))
      (matScale (spectator.driftFold cn cd sn sd certs).2
        (inertia.trailPad k
          (greenprod.addQ X' (greenprod.swapQ X)).1))) spP)
    (hLP : splitRead (matAdd
      (matScale ((spectator.driftFold cn cd sn sd certs).1
        * (X'.2 * X.2)) (idMat n))
      (matScale (spectator.driftFold cn cd sn sd certs).2
        (inertia.trailPad k
          (greenprod.addQ X' (greenprod.swapQ X)).1))) spP')
    (spF spF' : Split n)
    (hUF : splitRead (siteDatum
      (matScale (wrd * ((spectator.driftFold cn cd sn sd certs).1
          * (X'.2 * X.2))
        + (spectator.driftFold cn cd sn sd certs).2 * wrn) (idMat n))
      (matScale (wrd * (spectator.driftFold cn cd sn sd certs).2)
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2)) (inertia.headId k o))
          (inertia.trailPad k
            (greenprod.addQ X' (greenprod.swapQ X)).1)))) spF)
    (hLF : splitRead (matAdd
      (matScale (wrd * ((spectator.driftFold cn cd sn sd certs).1
          * (X'.2 * X.2))
        + (spectator.driftFold cn cd sn sd certs).2 * wrn) (idMat n))
      (matScale (wrd * (spectator.driftFold cn cd sn sd certs).2)
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2)) (inertia.headId k o))
          (inertia.trailPad k
            (greenprod.addQ X' (greenprod.swapQ X)).1)))) spF')
    (A : Mat) (cA cdA : Pos) (spA spA' : Split n)
    (hA : capAt (matScale cdA A) (matScale cA (idMat n)) spA spA')
    (psit : List BPair) (hpt : psit.length = n)
    (hker : poly.unitTail (matVec
      (matScale X.2 (greenprod.headM diag' off' X' j)) psit)) :
    (windowsep.mag (readGap
        (read A (matVec T.val (elim.idRow n j0)))
        (read A psit))).scale
      (gn * (wrd * (spectator.driftFold cn cd sn sd certs).2) * cdA)
      ≤ (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN psit psit).scale
        (4 * (cA * (wrd * ((spectator.driftFold cn cd sn sd certs).1
            * (X'.2 * X.2))
          + (spectator.driftFold cn cd sn sd certs).2 * wrn) * gd)) := by
  subst hk
  subst ho
  subst hn
  subst hX
  subst hX'
  have hjRs : j < Rs.length := by
    have ho2 := (walkOcc hshare.2.2.2.2.2 hocc).1
    rw [ground.length_reverse] at ho2
    exact takeDropOcc w0 j Rs ho2
  have hjn : j < ns.length := by
    rw [← greenprod.wShapeR_len hshare.1.2.2.1]
    exact Nat.lt_succ_of_lt hjRs
  have hGl := unitGram_last hshare.2.2.2.2.2 hjw hjRs
    (greenprod.qShape_len hshare.1.2.1)
    (greenprod.wShapeR_len hshare.1.2.2.1)
  obtain ⟨kk, spW, spW', hQ⟩ := spectator.driftShare_cap diag off diag'
    off' Xs Rs Xs' Rs' w0 j ns dn cn cd sn sd
    ((((ns.take (w0 + 1)).drop j).reverse).map inertia.idMat)
    certs hshare hocc hjw
  rw [hGl] at hQ
  have h1 : capAt
      (matScale (spectator.driftFold cn cd sn sd certs).2
        (greenprod.addQ (ground.getAt greenprod.dM Xs' j)
          (greenprod.swapQ (ground.getAt greenprod.dM Xs j))).1)
      (matScale ((spectator.driftFold cn cd sn sd certs).1
          * ((ground.getAt greenprod.dM Xs' j).2
            * (ground.getAt greenprod.dM Xs j).2))
        (idMat (ground.getAt 0 ns j))) spW spW' := hQ
  have hgk : ground.getAt 0 ns j = kk :=
    (inertia.idMat_len (ground.getAt 0 ns j)).symm.trans
      ((inertia.length_matScale _ _).symm.trans (elim.sqAt_len h1.2.1))
  subst hgk
  have h2 := inertia.capAt_trailPad
    (k := ground.sumNat (List.take j ns))
    (m := ground.getAt 0 ns j)
    (greenprod.addQ (ground.getAt greenprod.dM Xs' j)
      (greenprod.swapQ (ground.getAt greenprod.dM Xs j))).1
    ((spectator.driftFold cn cd sn sd certs).1
      * ((ground.getAt greenprod.dM Xs' j).2
        * (ground.getAt greenprod.dM Xs j).2))
    (spectator.driftFold cn cd sn sd certs).2 spW spW' h1 spP spP' hUP hLP
  have h3 := inertia.capAt_scale _ _ wrd _ _ h2
  rw [inertia.matScale_matScale _ wrd _,
    inertia.matScale_matScale _ wrd _] at h3
  have h4 := inertia.capAt_scale _ _
    (spectator.driftFold cn cd sn sd certs).2 _ _ hdrift
  rw [inertia.matScale_matScale _
      (spectator.driftFold cn cd sn sd certs).2 _,
    inertia.matScale_matScale _
      (spectator.driftFold cn cd sn sd certs).2 _,
    ground.mul_comm (spectator.driftFold cn cd sn sd certs).2 wrd] at h4
  have eS : matAdd
      (matScale (wrd * (spectator.driftFold cn cd sn sd certs).2)
        (matScaleB
          (dn.scale ((ground.getAt greenprod.dM Xs j).2
            * (ground.getAt greenprod.dM Xs' j).2))
          (inertia.headId (ground.sumNat (List.take j ns))
            (ground.getAt 0 ns j))))
      (matScale (wrd * (spectator.driftFold cn cd sn sd certs).2)
        (inertia.trailPad (ground.sumNat (List.take j ns))
          (greenprod.addQ (ground.getAt greenprod.dM Xs' j)
            (greenprod.swapQ (ground.getAt greenprod.dM Xs j))).1))
      = matScale (wrd * (spectator.driftFold cn cd sn sd certs).2)
        (matAdd
          (matScaleB
            (dn.scale ((ground.getAt greenprod.dM Xs j).2
              * (ground.getAt greenprod.dM Xs' j).2))
            (inertia.headId (ground.sumNat (List.take j ns))
              (ground.getAt 0 ns j)))
          (inertia.trailPad (ground.sumNat (List.take j ns))
            (greenprod.addQ (ground.getAt greenprod.dM Xs' j)
              (greenprod.swapQ (ground.getAt greenprod.dM Xs j))).1)) :=
    (inertia.matScale_matAdd _ _ _).symm
  have eC : matAdd
      (matScale ((spectator.driftFold cn cd sn sd certs).2 * wrn)
        (idMat (ground.sumNat (List.take j ns)
          + ground.getAt 0 ns j)))
      (matScale (wrd * ((spectator.driftFold cn cd sn sd certs).1
          * ((ground.getAt greenprod.dM Xs' j).2
            * (ground.getAt greenprod.dM Xs j).2)))
        (idMat (ground.sumNat (List.take j ns)
          + ground.getAt 0 ns j)))
      = matScale (wrd * ((spectator.driftFold cn cd sn sd certs).1
          * ((ground.getAt greenprod.dM Xs' j).2
            * (ground.getAt greenprod.dM Xs j).2))
        + (spectator.driftFold cn cd sn sd certs).2 * wrn)
        (idMat (ground.sumNat (List.take j ns)
          + ground.getAt 0 ns j)) := by
    rw [inertia.matScale_addW _ _ (idMat _)]
    exact elim.matAdd_comm _ _
  have hUF2 := hUF
  have hLF2 := hLF
  rw [← eS, ← eC] at hUF2 hLF2
  have h5 := inertia.capAt_add _ _ _ _ _ _ _ _ spF spF' h4 h3 hUF2 hLF2
  rw [eS, eC] at h5
  have hstep := (ground.orSplitB
    (ground.all_range_read diag.length hshare.2.2.2.2.1 j (by
      rw [← greenprod.slabShape_len_ns hshare.1.1]
      exact hjn))).elim
    (fun hle => absurd (Nat.lt_of_lt_of_le hjw (ground.bleLe hle))
      (Nat.lt_irrefl j))
    (fun hdec => of_decide_eq_true hdec)
  have hdag : ∀ i, i < j → matOneValue (ground.getAt [] diag' i)
      (matAdd (ground.getAt [] diag i)
        (matScaleB dn (idMat (ground.getAt 0 ns i)))) := by
    intro i hi
    have hid : i < diag.length := by
      rw [← greenprod.slabShape_len_ns hshare.1.1]
      exact Nat.lt_trans hi hjn
    refine (ground.orSplitB
      (ground.all_range_read diag.length hshare.2.2.2.1 i hid)).elim
      (fun hle => ?_) (fun hdec => of_decide_eq_true hdec)
    exact absurd (Nat.lt_of_lt_of_le (Nat.lt_trans hi hjw)
      (ground.bleLe hle)) (Nat.lt_irrefl i)
  have hoff : ∀ i, i < j → matOneValue (ground.getAt [] off' i)
      (ground.getAt [] off i) := by
    intro i hi
    have hio : i < off.length :=
      offAt hshare.1.1 i (Nat.lt_of_le_of_lt hi hjn)
    refine (ground.orSplitB
      (ground.all_range_read off.length hshare.2.2.1 i hio)).elim
      (fun hle => ?_) (fun hdec => of_decide_eq_true hdec)
    exact absurd (Nat.lt_of_lt_of_le (Nat.lt_trans hi hjw)
      (ground.bleLe hle)) (Nat.lt_irrefl i)
  exact transport_read _ _ _ A T Tw l hd j0 hj0 d0 g0 hroot0 gn gd hcl
    (greenprod.headM_tie diag off diag' off'
      (ground.getAt greenprod.dM Xs j) (ground.getAt greenprod.dM Xs' j)
      j ns dn hshare.1.1 hshare.2.1.1 hjn hstep.2.2.2.1 hstep.2.2.1
      hdag hoff)
    _ (wrd * (spectator.driftFold cn cd sn sd certs).2) spF spF' h5
    cA cdA spA spA' hA psit hpt hker

/-! The full read: the extension of the head pair by the tail weight,
the cross-cleared head components, and the tail weights' price. -/

/-- The extended reads' gap at the clearing scales: the pair of each
window's full read extends its head pair by the tail weight, and the
gap's magnitude splits into the head gap's own rescaling by the two
clearings and the two cross terms, each rescaled by the other
window's clearing. -/
theorem readGap_extend (a g a' g' Th Th' : BPair) (Dt Dt' : Pos) :
    windowsep.mag (readGap
        (a.scale Dt, g.scale Dt + Th) (a'.scale Dt', g'.scale Dt' + Th'))
      ≤ (windowsep.mag (readGap (a, g) (a', g'))).scale (Dt * Dt')
        + ((windowsep.mag (a' * Th)).scale Dt'
          + (windowsep.mag (a * Th')).scale Dt) := by
  have key : readGap (a.scale Dt, g.scale Dt + Th)
        (a'.scale Dt', g'.scale Dt' + Th')
      = (readGap (a, g) (a', g')).scale (Dt * Dt')
        + ((a' * Th).scale Dt' + ((a * Th').scale Dt).swap) := by
    show a'.scale Dt' * (g.scale Dt + Th)
        + (a.scale Dt * (g'.scale Dt' + Th')).swap
      = (a' * g + (a * g').swap).scale (Dt * Dt')
        + ((a' * Th).scale Dt' + ((a * Th').scale Dt).swap)
    rw [BPair.left_distrib (a'.scale Dt') (g.scale Dt) Th,
      BPair.left_distrib (a.scale Dt) (g'.scale Dt') Th',
      ← BPair.swap_add (a.scale Dt * g'.scale Dt') (a.scale Dt * Th'),
      ← BPair.scale_mul a' g Dt' Dt, ← BPair.scale_mul a g' Dt Dt',
      ← BPair.scale_mul_left a' Th Dt',
      ← BPair.scale_mul_left a Th' Dt,
      ground.mul_comm Dt' Dt, BPair.scale_add,
      BPair.add_add_comm ((a' * g).scale (Dt * Dt'))
        ((a' * Th).scale Dt') (((a * g').scale (Dt * Dt')).swap)
        (((a * Th').scale Dt).swap)]
    rfl
  rw [key]
  refine ground.leB_trans (windowsep.mag_add_le _ _) (ground.leB_add ?_ ?_)
  · rw [windowsep.mag_scale]
    exact ground.leB_refl _
  · refine ground.leB_trans (windowsep.mag_add_le _ _) (ground.leB_add ?_ ?_)
    · rw [windowsep.mag_scale]
      exact ground.leB_refl _
    · rw [windowsep.mag_swap, windowsep.mag_scale]
      exact ground.leB_refl _

/-- The clearings' product along a list of cleared vectors. -/
def denProd : List greenprod.VecQ → Pos
  | [] => Pos.one
  | u :: t => u.2 * denProd t

/-- The head's components cross-cleared and joined: the leading
block rescaled by the clearings of every block beyond it, the blocks
beyond it rescaled by its own, so the joined list reads one vector
at the product clearing. -/
def headVec : List greenprod.VecQ → List BPair
  | [] => []
  | u :: t =>
    greenprod.vecScale (denProd t) u.1 ++ greenprod.vecScale u.2 (headVec t)


/-! `thm:groundreads`(ii)'s far-end closure at the decimated head:
the cross-cleared head concatenation solves the decimated head's
rows, each leading row at its own kernel row read and the pivot's
row at the kernel walk's own. -/

/-- The componentwise sum splits at a stated seam when the first
family ends within the seam's leading part. -/
private theorem addSplit : ∀ (p X Y : List BPair),
    p.length ≤ X.length →
    poly.add p (X ++ Y) = poly.add p X ++ Y
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => absurd h (Nat.not_succ_le_zero _)
  | a :: p, x :: X, Y, h => by
    show (a + x) :: poly.add p (X ++ Y)
      = (a + x) :: (poly.add p X ++ Y)
    rw [addSplit p X Y (Nat.le_of_succ_le_succ h)]

/-- A family extended by a unit tail reads the family itself. -/
private theorem appUnitR : ∀ (a U : List BPair), poly.unitTail U →
    poly.oneValue (a ++ U) a
  | [], [], _ => trivial
  | [], _ :: _, hU => hU
  | _ :: a, U, hU => ⟨BPair.oneValue_refl _, appUnitR a U hU⟩

/-- A unit-tailed family absorbs into the componentwise sum on the
left. -/
private theorem addUnitL : ∀ (U b : List BPair), poly.unitTail U →
    poly.oneValue (poly.add U b) b
  | [], b, _ => poly.oneValue_refl b
  | _ :: _, [], hU => hU
  | u :: U, x :: b, hU =>
    ⟨BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm u x))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl x) hU.1)
        (BPair.add_unit x)),
     addUnitL U b hU.2⟩

/-- A unit-tailed middle absorbs into the componentwise sum at the
seam. -/
private theorem addUnitsMid : ∀ (a U b : List BPair),
    poly.unitTail U →
    poly.oneValue (poly.add (a ++ U) b) (poly.add a b)
  | [], U, b, hU => addUnitL U b hU
  | _ :: a, U, [], hU => ⟨BPair.oneValue_refl _, appUnitR a U hU⟩
  | _ :: a, U, _ :: b, hU =>
    ⟨BPair.oneValue_refl _, addUnitsMid a U b hU⟩

/-- The rescaling at the unit clearing reads the family itself. -/
private theorem scaleOne : ∀ v : List BPair,
    poly.oneValue (greenprod.vecScale Pos.one v) v
  | [] => trivial
  | x :: v => by
    refine ⟨?_, scaleOne v⟩
    show x.fst * Pos.one + x.snd = x.fst + x.snd * Pos.one
    rw [ground.mul_one, ground.mul_one]

/-- The clearings' product splits at any cut: the joined clearing
is the leading part's product against the product of the part
beyond the cut. -/
theorem denProd_split : ∀ (m : Nat) (vs : List greenprod.VecQ),
    denProd vs = denProd (List.take m vs) * denProd (List.drop m vs)
  | 0, vs => (ground.one_mul _).symm
  | _ + 1, [] => (ground.one_mul _).symm
  | m + 1, u :: t => by
    show u.2 * denProd t = u.2 * denProd (List.take m t)
      * denProd (List.drop m t)
    rw [denProd_split m t, ground.mul_assoc]

/-- The positive rescaling splits over a join. -/
private theorem gvsApp (w : Pos) (x y : List BPair) :
    greenprod.vecScale w (x ++ y)
      = greenprod.vecScale w x ++ greenprod.vecScale w y := by
  show (x ++ y).map (fun z => z.scale w)
    = x.map (fun z => z.scale w) ++ y.map (fun z => z.scale w)
  rw [ground.map_append (fun z : BPair => z.scale w) x y]

/-- Two positive rescalings compose at the clearings' product. -/
private theorem gvsTwo (a b : Pos) : ∀ v : List BPair,
    greenprod.vecScale a (greenprod.vecScale b v)
      = greenprod.vecScale (a * b) v
  | [] => rfl
  | x :: v => by
    show (x.scale b).scale a
        :: greenprod.vecScale a (greenprod.vecScale b v)
      = x.scale (a * b) :: greenprod.vecScale (a * b) v
    rw [BPair.scale_scale x b a, ground.mul_comm b a, gvsTwo a b v]

/-- The positive rescaling passes the one-value read. -/
private theorem gvsCongr (w : Pos) : ∀ {p q : List BPair},
    poly.oneValue p q →
    poly.oneValue (greenprod.vecScale w p) (greenprod.vecScale w q)
  | [], _, h => gvsUnit w h
  | c :: p, [], h => gvsUnit w (show poly.unitTail (c :: p) from h)
  | _ :: _, _ :: _, h => ⟨BPair.scale_congr w h.1, gvsCongr w h.2⟩

/-- The cross-cleared head splits at any cut: the head reads the
leading part's own head rescaled by the clearing beyond the cut,
joined to the head beyond the cut rescaled by the leading part's
own clearing. -/
theorem headVec_split : ∀ (m : Nat) (vs : List greenprod.VecQ),
    poly.oneValue (headVec vs)
      (greenprod.vecScale (denProd (List.drop m vs))
          (headVec (List.take m vs))
        ++ greenprod.vecScale (denProd (List.take m vs))
          (headVec (List.drop m vs)))
  | 0, vs => poly.oneValue_symm (scaleOne (headVec vs))
  | _ + 1, [] => trivial
  | m + 1, u :: t => by
    show poly.oneValue
      (greenprod.vecScale (denProd t) u.1
        ++ greenprod.vecScale u.2 (headVec t))
      (greenprod.vecScale (denProd (List.drop m t))
          (greenprod.vecScale (denProd (List.take m t)) u.1
            ++ greenprod.vecScale u.2 (headVec (List.take m t)))
        ++ greenprod.vecScale (u.2 * denProd (List.take m t))
          (headVec (List.drop m t)))
    rw [gvsApp (denProd (List.drop m t)), ground.append_assoc,
      gvsTwo (denProd (List.drop m t)) (denProd (List.take m t)) u.1,
      ground.mul_comm (denProd (List.drop m t)) (denProd (List.take m t)),
      ← denProd_split m t,
      gvsTwo (denProd (List.drop m t)) u.2 (headVec (List.take m t)),
      ground.mul_comm (denProd (List.drop m t)) u.2]
    refine poly.oneValue_append _ _ _ _ rfl
      (poly.oneValue_refl _) ?_
    rw [← gvsTwo u.2 (denProd (List.drop m t)) (headVec (List.take m t)),
      ← gvsTwo u.2 (denProd (List.take m t)) (headVec (List.drop m t)),
      ← gvsApp u.2]
    exact gvsCongr u.2 (headVec_split m t)

/-- The four clearings regroup at the walked step. -/
private theorem posK1 (a b c d : Pos) :
    a * d * (b * c) = a * (b * (c * d)) := by
  rw [ground.mul_assoc a d (b * c), ground.mul_comm d (b * c),
    ground.mul_assoc b c d]

/-- The three clearings regroup at the walked step. -/
private theorem posK2 (a b d : Pos) : a * d * b = a * (b * d) := by
  rw [ground.mul_assoc a d b, ground.mul_comm d b]

/-- The head kernel's walk: at the slab, pivot, witness and vector
walks with the rows at unit sides and an accumulator entering the
leading slab, the decimated head at any depth reads the accumulator
against the cross-cleared head concatenation at the sum's unit, the
clearings collected at the pivot's and the depths' own. -/
private theorem kernelGo : ∀ (j : Nat) (A : Mat) (diag off : List Mat)
    (X : greenprod.MatQ) (Xs Rs : List greenprod.MatQ) (k : Nat)
    (ns : List Nat) (u : greenprod.VecQ) (us ws : List greenprod.VecQ)
    (p : greenprod.VecQ),
    greenprod.slabShape (A :: diag) off (k :: ns) →
    greenprod.qShape (X :: Xs) (k :: ns) →
    greenprod.wShapeR Rs (k :: ns) →
    greenprod.vShape (u :: us) (k :: ns) →
    greenprod.tailSteps (A :: diag) off (X :: Xs) Rs →
    greenprod.solveRows p (A :: diag) off (u :: us) ws →
    greenprod.sidesUnit ws →
    j + 1 ≤ (u :: us).length →
    p.1.length ≤ k →
    poly.unitTail (poly.add
      (vecScale (BPair.ofPos
        ((ground.getAt greenprod.dM (X :: Xs) j).2
          * denProd (List.take (j + 1) (u :: us)))) p.1)
      (vecScale (BPair.ofPos p.2)
        (matVec (greenprod.headM (A :: diag) off
            (ground.getAt greenprod.dM (X :: Xs) j) j)
          (headVec (List.take (j + 1) (u :: us))))))
  | 0, A, diag, off, X, Xs, Rs, k, ns, u, us, ws, p,
      hslab, hq, hwr, hv, hts, hsr, hsu, _, _ => by
    have hrr := (walk diag A off X Xs Rs k ns u us ws p
      hslab hq hwr hv hts hsr hsu).1
    refine poly.oneValue_unitTail (poly.add_congr ?_ ?_)
      (poly.oneValue_unitTail (poly.add_comm _ _) hrr)
    · exact poly.oneValue_of_eq (congrArg
        (fun c => vecScale (BPair.ofPos c) p.1)
        (show X.2 * (u.2 * Pos.one) = X.2 * u.2 by
          rw [ground.mul_one]))
    · refine elim.vecScale_oneValue _ _ _ ?_
      refine elim.matVec_congr X.1 _ _ ?_
      exact poly.oneValue_trans
        (appUnitR (greenprod.vecScale Pos.one u.1) [] trivial)
        (scaleOne u.1)
  | j + 1, A, diag, off, X, Xs, Rs, k, ns, u, us, ws, p,
      hslab, hq, hwr, hv, hts, hsr, hsu, hj, hpl => by
    cases diag with
    | nil =>
      cases off with
      | cons _ _ => exact (hsr : False).elim
      | nil =>
        cases us with
        | nil =>
          exact absurd (Nat.le_of_succ_le_succ hj)
            (Nat.not_succ_le_zero j)
        | cons _ _ => exact (hsr : False).elim
    | cons A1 As =>
    cases off with
    | nil => exact (hsr : False).elim
    | cons B Bs =>
    cases us with
    | nil => exact (hsr : False).elim
    | cons u1 us1 =>
    cases ns with
    | nil => exact (hv.2 : False).elim
    | cons k1 ns1 =>
    cases Xs with
    | nil => exact (hq.2 : False).elim
    | cons X1 Xs1 =>
    cases Rs with
    | nil => exact (hts : False).elim
    | cons R Rs1 =>
    cases ws with
    | nil => exact (hsr : False).elim
    | cons w ws1 =>
    -- the slab frames
    have hk : 0 < k := hslab.1
    have hAl : (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2 A).length
        = k :=
      (length_matScale _ A).trans (sqAt_len hslab.2.1)
    have hBr0 : rowsLen k1 B := greenprod.rectAt_rows hslab.2.2.1
    have hBl0 : B.length = k := greenprod.rectAt_len hslab.2.2.1
    have hul : u.1.length = k := hv.1
    have hu1l : u1.1.length = k1 := hv.2.1
    have hjt : j < (k1 :: ns1).length := by
      rw [← greenprod.vShape_len hv.2]
      exact Nat.le_of_succ_le_succ hj
    have hXpsq : sqAt (ground.getAt greenprod.dM (X1 :: Xs1) j).1
        (ground.getAt 0 (k1 :: ns1) j) :=
      greenprod.qShape_at hq.2 j
        (by rw [greenprod.qShape_len hq.2]; exact hjt)
    have hQsq : sqAt (greenprod.headM (A1 :: As) Bs (ground.getAt greenprod.dM
        (X1 :: Xs1) j) j) (ground.sumNat (List.take j (k1 :: ns1)) +
        ground.getAt 0 (k1 :: ns1) j) :=
      greenprod.headM_sq (A1 :: As) Bs _ j (k1 :: ns1)
        hslab.2.2.2 hjt hXpsq
    have hle : k1 ≤ ground.sumNat (List.take j (k1 :: ns1)) + ground.getAt 0
        (k1 :: ns1) j :=
      ground.headKey_le (k1 :: ns1) j hjt
    have hB'l : (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2
        B).length = k := (length_matScale _ B).trans hBl0
    have hB'r : rowsLen k1 (matScale (ground.getAt greenprod.dM (X1 :: Xs1)
        j).2 B) := elim.rowsLen_mapRows _ B k1 hBr0
    have hbtl : (transposeM (matScale (ground.getAt greenprod.dM (X1 :: Xs1)
        j).2 B)).length = k1 :=
      length_transposeM _ hB'r (by rw [hB'l]; exact hk)
    -- the head's one-slab peel
    have hpeel : greenprod.headM (A :: A1 :: As) (B :: Bs)
        (ground.getAt greenprod.dM (X1 :: Xs1) j) (j + 1)
        = blockJoin (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2 A)
            (greenprod.offPad (ground.sumNat (List.take j (k1 :: ns1)) +
            ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt greenprod.dM
            (X1 :: Xs1) j).2 B)) (greenprod.headM (A1 :: As) Bs (ground.getAt
            greenprod.dM (X1 :: Xs1) j) j) := by
      show greenprod.assemble
        (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2 A
          :: (List.map (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2)
              (List.take j (A1 :: As))
            ++ [(ground.getAt greenprod.dM (X1 :: Xs1) j).1]))
        (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2 B
          :: List.map (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2)
              (List.take j Bs)) = _
      exact greenprod.assemble_cons _ _ _ _ k k1 _
        hAl hk hB'l hB'r hle (sqAt_len hQsq)
        (greenprod.sqAt_headD _ _ hQsq)
    -- the kernel row read at the leading slab
    have m2 : poly.unitTail (poly.add
        (greenprod.vecScale (u.2 * u1.2) p.1)
        (greenprod.vecScale p.2 (poly.add (greenprod.vecScale u1.2 (matVec A
            u.1)) (greenprod.vecScale u.2 (matVec B u1.1))))) := by
      have m1 : poly.unitTail (greenprod.vecScale w.2 (poly.add
          (greenprod.vecScale (u.2 * u1.2) p.1)
          (greenprod.vecScale p.2 (poly.add (greenprod.vecScale u1.2 (matVec A
              u.1)) (greenprod.vecScale u.2 (matVec B u1.1)))))) :=
        poly.oneValue_unitTail hsr.1 (gvsUnit _ hsu.1)
      exact unitTail_unscale _ (BPair.ofPos_off w.2) _
        (poly.unitTail_oneValue_right m1
          (greenprod.vecScale_ofPos w.2 _))
    have m3 : poly.unitTail (poly.add
        (vecScale (BPair.ofPos ((ground.getAt greenprod.dM (X1 :: Xs1) j).2 *
            denProd (List.take j us1)))
          (greenprod.vecScale (u.2 * u1.2) p.1))
        (vecScale (BPair.ofPos ((ground.getAt greenprod.dM (X1 :: Xs1) j).2 *
            denProd (List.take j us1)))
          (greenprod.vecScale p.2 (poly.add (greenprod.vecScale u1.2 (matVec A
              u.1)) (greenprod.vecScale u.2 (matVec B u1.1)))))) := by
      have h := unitTail_vecScale (BPair.ofPos ((ground.getAt greenprod.dM (X1
          :: Xs1) j).2 * denProd (List.take j us1))) _ m2
      rw [scaleAdd] at h
      exact h
    -- the induction hypothesis at the exchange accumulator
    have hIH := kernelGo j A1 As Bs X1 Xs1 Rs1 k1 ns1 u1 us1 ws1
      (greenprod.appM (transposeM B) u)
      hslab.2.2.2 hq.2 hwr.2 hv.2 hts.2 hsr.2 hsu.2
      (Nat.le_of_succ_le_succ hj)
      (Nat.le_of_eq ((ground.length_map _ _).trans
        (length_transposeM B hBr0 (by rw [hBl0]; exact hk))))
    -- the leading block against the row read
    have hW1 : poly.oneValue (matVec (matScale (ground.getAt greenprod.dM (X1
        :: Xs1) j).2 A) (greenprod.vecScale (denProd (List.take (j + 1) (u1 ::
        us1))) u.1))
        (vecScale (BPair.ofPos ((ground.getAt greenprod.dM (X1 :: Xs1) j).2 *
            denProd (List.take j us1))) (greenprod.vecScale u1.2 (matVec A
            u.1))) := by
      refine poly.oneValue_trans (inertia.matVec_matScale _ A _) ?_
      refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
        (poly.oneValue_trans
          (elim.matVec_congr A _ _ (greenprod.vecScale_ofPos _ u.1))
          (elim.matVec_vecScale_free A _ u.1))) ?_
      refine poly.oneValue_trans (scaleFlat rfl (matVec A u.1)) ?_
      refine poly.oneValue_symm ?_
      refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
        (greenprod.vecScale_ofPos u1.2 (matVec A u.1))) ?_
      exact scaleFlat (posK2 _ u1.2 _) (matVec A u.1)
    have hW2 : poly.oneValue (matVec (greenprod.offPad (ground.sumNat
        (List.take j (k1 :: ns1)) + ground.getAt 0 (k1 :: ns1) j) (matScale
        (ground.getAt greenprod.dM (X1 :: Xs1) j).2 B)) (greenprod.vecScale
        u.2 (headVec (List.take (j + 1) (u1 :: us1)))))
        (vecScale (BPair.ofPos ((ground.getAt greenprod.dM (X1 :: Xs1) j).2 *
            denProd (List.take j us1))) (greenprod.vecScale u.2 (matVec B
            u1.1))) := by
      rw [show (greenprod.vecScale u.2 (headVec (List.take (j + 1) (u1 ::
          us1))))
        = greenprod.vecScale u.2
            (greenprod.vecScale (denProd (List.take j us1)) u1.1)
          ++ greenprod.vecScale u.2
            (greenprod.vecScale u1.2 (headVec (List.take j us1)))
        from ground.map_append _ _ _]
      refine poly.oneValue_trans
        (greenprod.offPad_act _ k1 _ hB'r _ _
          ((ground.length_map _ _).trans
            ((ground.length_map _ _).trans hu1l))) ?_
      refine poly.oneValue_trans (inertia.matVec_matScale _ B _) ?_
      refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
        (poly.oneValue_trans
          (elim.matVec_congr B _ _ (poly.oneValue_trans
            (greenprod.vecScale_ofPos u.2 _)
            (elim.vecScale_oneValue _ _ _
              (greenprod.vecScale_ofPos _ u1.1))))
          (poly.oneValue_trans
            (elim.matVec_vecScale_free B _ _)
            (elim.vecScale_oneValue _ _ _
              (elim.matVec_vecScale_free B _ u1.1))))) ?_
      refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
        (scaleFlat rfl (matVec B u1.1))) ?_
      refine poly.oneValue_trans (scaleFlat rfl (matVec B u1.1)) ?_
      refine poly.oneValue_symm ?_
      refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
        (greenprod.vecScale_ofPos u.2 (matVec B u1.1))) ?_
      exact scaleFlat (posK2 _ u.2 _) (matVec B u1.1)
    -- the trailing block against the induction hypothesis
    have hT1 : poly.oneValue (matVec (transposeM (matScale (ground.getAt
        greenprod.dM (X1 :: Xs1) j).2 B)) (greenprod.vecScale (denProd
        (List.take (j + 1) (u1 :: us1))) u.1))
        (vecScale (BPair.ofPos
            ((ground.getAt greenprod.dM (X1 :: Xs1) j).2 * denProd (List.take
                (j + 1) (u1 :: us1))))
          (matVec (transposeM B) u.1)) := by
      refine poly.oneValue_trans
        (elim.matVec_matOne _ _ _
          (inertia.transposeM_matScale _ k1 B hBr0)) ?_
      refine poly.oneValue_trans
        (inertia.matVec_matScale _ (transposeM B) _) ?_
      refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
        (poly.oneValue_trans
          (elim.matVec_congr (transposeM B) _ _
            (greenprod.vecScale_ofPos _ u.1))
          (elim.matVec_vecScale_free (transposeM B) _ u.1))) ?_
      exact scaleFlat rfl (matVec (transposeM B) u.1)
    have hT2 : poly.oneValue (matVec (greenprod.headM (A1 :: As) Bs
        (ground.getAt greenprod.dM (X1 :: Xs1) j) j) (greenprod.vecScale u.2
        (headVec (List.take (j + 1) (u1 :: us1)))))
        (vecScale (BPair.ofPos u.2)
          (matVec (greenprod.headM (A1 :: As) Bs (ground.getAt greenprod.dM
              (X1 :: Xs1) j) j) (headVec (List.take (j + 1) (u1 :: us1))))) :=
      poly.oneValue_trans
        (elim.matVec_congr _ _ _ (greenprod.vecScale_ofPos u.2 _))
        (elim.matVec_vecScale_free _ _ _)
    have hTrU : poly.unitTail (elim.vecAdd (matVec (transposeM
        (greenprod.offPad (ground.sumNat (List.take j (k1 :: ns1)) +
        ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt greenprod.dM (X1
        :: Xs1) j).2 B))) (greenprod.vecScale (denProd (List.take (j + 1) (u1
        :: us1))) u.1)) (matVec (greenprod.headM (A1 :: As) Bs (ground.getAt
        greenprod.dM (X1 :: Xs1) j) j) (greenprod.vecScale u.2 (headVec
        (List.take (j + 1) (u1 :: us1)))))) := by
      rw [greenprod.transposeM_offPad _ k k1 _ hB'l hB'r hk hle,
        greenprod.offT_split k _ _ (by rw [hbtl]; exact hle),
        hbtl, elim.matVec_append]
      refine poly.oneValue_unitTail ?_ hIH
      refine poly.oneValue_trans (poly.oneValue_of_eq
        (elim.vecAdd_eq_polyAdd _ _ ?_)) ?_
      · rw [ground.length_append,
          show (matVec (transposeM (matScale (ground.getAt greenprod.dM (X1 ::
              Xs1) j).2 B)) (greenprod.vecScale (denProd (List.take (j + 1)
              (u1 :: us1))) u.1)).length = k1 from
            (ground.length_map _ _).trans hbtl,
          show (matVec (List.replicate
              (ground.sumNat (List.take j (k1 :: ns1)) + ground.getAt 0 (k1 ::
                  ns1) j - k1) (List.replicate k BPair.unit))
              (greenprod.vecScale (denProd (List.take (j + 1) (u1 :: us1)))
                  u.1)).length
            = ground.sumNat (List.take j (k1 :: ns1)) + ground.getAt 0 (k1 ::
                ns1) j - k1 from
            (ground.length_map _ _).trans (ground.length_replicate _ _),
          show (matVec (greenprod.headM (A1 :: As) Bs (ground.getAt
              greenprod.dM (X1 :: Xs1) j) j) (greenprod.vecScale u.2 (headVec
              (List.take (j + 1) (u1 :: us1))))).length
            = ground.sumNat (List.take j (k1 :: ns1)) + ground.getAt 0 (k1 ::
                ns1) j from
            (ground.length_map _ _).trans (sqAt_len hQsq)]
        exact ground.natAddSubCancel hle
      · refine poly.oneValue_trans
          (addUnitsMid _ _ _ (elim.matVec_nullMat _ k _)) ?_
        exact poly.add_congr hT1 hT2
    -- the action's block split
    have hM : poly.oneValue
        (matVec (greenprod.headM (A :: A1 :: As) (B :: Bs)
            (ground.getAt greenprod.dM (X1 :: Xs1) j) (j + 1))
          (headVec (List.take (j + 1 + 1) (u :: u1 :: us1))))
        ((elim.vecAdd (matVec (matScale (ground.getAt greenprod.dM (X1 :: Xs1)
            j).2 A) (greenprod.vecScale (denProd (List.take (j + 1) (u1 ::
            us1))) u.1)) (matVec (greenprod.offPad (ground.sumNat (List.take j
            (k1 :: ns1)) + ground.getAt 0 (k1 :: ns1) j) (matScale
            (ground.getAt greenprod.dM (X1 :: Xs1) j).2 B))
            (greenprod.vecScale u.2 (headVec (List.take (j + 1) (u1 ::
            us1)))))) ++ (elim.vecAdd (matVec (transposeM (greenprod.offPad
            (ground.sumNat (List.take j (k1 :: ns1)) + ground.getAt 0 (k1 ::
            ns1) j) (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2 B)))
            (greenprod.vecScale (denProd (List.take (j + 1) (u1 :: us1)))
            u.1)) (matVec (greenprod.headM (A1 :: As) Bs (ground.getAt
            greenprod.dM (X1 :: Xs1) j) j) (greenprod.vecScale u.2 (headVec
            (List.take (j + 1) (u1 :: us1))))))) := by
      rw [hpeel]
      show poly.oneValue
        (matVec (rowJoin (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2
            A) (greenprod.offPad (ground.sumNat (List.take j (k1 :: ns1)) +
            ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt greenprod.dM
            (X1 :: Xs1) j).2 B))
            ++ rowJoin (transposeM (greenprod.offPad (ground.sumNat (List.take
                j (k1 :: ns1)) + ground.getAt 0 (k1 :: ns1) j) (matScale
                (ground.getAt greenprod.dM (X1 :: Xs1) j).2 B)))
                (greenprod.headM (A1 :: As) Bs (ground.getAt greenprod.dM (X1
                :: Xs1) j) j))
          ((greenprod.vecScale (denProd (List.take (j + 1) (u1 :: us1))) u.1)
              ++ (greenprod.vecScale u.2 (headVec (List.take (j + 1) (u1 ::
              us1)))))) _
      rw [elim.matVec_append]
      refine poly.oneValue_append _ _ _ _ ?_
        (elim.matVec_rowJoin k _ _ _ _
          (elim.rowsLen_mapRows _ A k (rowsLen_of_sqAt hslab.2.1))
          ((ground.length_map _ u.1).trans hul))
        (elim.matVec_rowJoin k _ _ _ _
          (elim.rowsLen_cast
            ((greenprod.offPad_len _ _).trans hB'l)
            (elim.rowsLen_transposeM _))
          ((ground.length_map _ u.1).trans hul))
      rw [show (matVec (rowJoin (matScale (ground.getAt greenprod.dM (X1 ::
          Xs1) j).2 A) (greenprod.offPad (ground.sumNat (List.take j (k1 ::
          ns1)) + ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt
          greenprod.dM (X1 :: Xs1) j).2 B))) ((greenprod.vecScale (denProd
          (List.take (j + 1) (u1 :: us1))) u.1) ++ (greenprod.vecScale u.2
          (headVec (List.take (j + 1) (u1 :: us1)))))).length = k
          from (ground.length_map _ _).trans
            (ground.length_zipWith _ _ _ k hAl
              ((greenprod.offPad_len _ _).trans hB'l)),
        show ((elim.vecAdd (matVec (matScale (ground.getAt greenprod.dM (X1 ::
            Xs1) j).2 A) (greenprod.vecScale (denProd (List.take (j + 1) (u1
            :: us1))) u.1)) (matVec (greenprod.offPad (ground.sumNat
            (List.take j (k1 :: ns1)) + ground.getAt 0 (k1 :: ns1) j)
            (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2 B))
            (greenprod.vecScale u.2 (headVec (List.take (j + 1) (u1 ::
            us1)))))) : List BPair).length = k from
          elim.length_vecAdd _ _ k
            ((ground.length_map _ _).trans hAl)
            ((ground.length_map _ _).trans
              ((greenprod.offPad_len _ _).trans hB'l))]
    -- the assembly
    refine poly.oneValue_unitTail (poly.add_congr
      (poly.oneValue_refl _)
      (elim.vecScale_oneValue _ _ _ hM)) ?_
    rw [show vecScale (BPair.ofPos p.2) ((elim.vecAdd (matVec (matScale
        (ground.getAt greenprod.dM (X1 :: Xs1) j).2 A) (greenprod.vecScale
        (denProd (List.take (j + 1) (u1 :: us1))) u.1)) (matVec
        (greenprod.offPad (ground.sumNat (List.take j (k1 :: ns1)) +
        ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt greenprod.dM (X1
        :: Xs1) j).2 B)) (greenprod.vecScale u.2 (headVec (List.take (j + 1)
        (u1 :: us1)))))) ++ (elim.vecAdd (matVec (transposeM (greenprod.offPad
        (ground.sumNat (List.take j (k1 :: ns1)) + ground.getAt 0 (k1 :: ns1)
        j) (matScale (ground.getAt greenprod.dM (X1 :: Xs1) j).2 B)))
        (greenprod.vecScale (denProd (List.take (j + 1) (u1 :: us1))) u.1))
        (matVec (greenprod.headM (A1 :: As) Bs (ground.getAt greenprod.dM (X1
        :: Xs1) j) j) (greenprod.vecScale u.2 (headVec (List.take (j + 1) (u1
        :: us1)))))))
        = vecScale (BPair.ofPos p.2) (elim.vecAdd (matVec (matScale
            (ground.getAt greenprod.dM (X1 :: Xs1) j).2 A) (greenprod.vecScale
            (denProd (List.take (j + 1) (u1 :: us1))) u.1)) (matVec
            (greenprod.offPad (ground.sumNat (List.take j (k1 :: ns1)) +
            ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt greenprod.dM
            (X1 :: Xs1) j).2 B)) (greenprod.vecScale u.2 (headVec (List.take
            (j + 1) (u1 :: us1))))))
          ++ vecScale (BPair.ofPos p.2) (elim.vecAdd (matVec (transposeM
              (greenprod.offPad (ground.sumNat (List.take j (k1 :: ns1)) +
              ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt
              greenprod.dM (X1 :: Xs1) j).2 B))) (greenprod.vecScale (denProd
              (List.take (j + 1) (u1 :: us1))) u.1)) (matVec (greenprod.headM
              (A1 :: As) Bs (ground.getAt greenprod.dM (X1 :: Xs1) j) j)
              (greenprod.vecScale u.2 (headVec (List.take (j + 1) (u1 ::
              us1))))))
      from ground.map_append _ _ _]
    rw [addSplit _ _ _ (by
      rw [show (vecScale (BPair.ofPos
            ((ground.getAt greenprod.dM (X :: X1 :: Xs1) (j + 1)).2
              * denProd (List.take (j + 1 + 1) (u :: u1 :: us1))))
            p.1).length = p.1.length from ground.length_map _ _,
        show (vecScale (BPair.ofPos p.2) (elim.vecAdd (matVec (matScale
            (ground.getAt greenprod.dM (X1 :: Xs1) j).2 A) (greenprod.vecScale
            (denProd (List.take (j + 1) (u1 :: us1))) u.1)) (matVec
            (greenprod.offPad (ground.sumNat (List.take j (k1 :: ns1)) +
            ground.getAt 0 (k1 :: ns1) j) (matScale (ground.getAt greenprod.dM
            (X1 :: Xs1) j).2 B)) (greenprod.vecScale u.2 (headVec (List.take
            (j + 1) (u1 :: us1))))))).length = k from
          (ground.length_map _ _).trans
            (elim.length_vecAdd _ _ k
              ((ground.length_map _ _).trans hAl)
              ((ground.length_map _ _).trans
                ((greenprod.offPad_len _ _).trans hB'l)))]
      exact hpl)]
    refine elim.unitTail_append ?_
      (unitTail_vecScale (BPair.ofPos p.2) _ hTrU)
    refine poly.oneValue_unitTail (poly.add_congr
      (poly.oneValue_symm (poly.oneValue_trans
        (elim.vecScale_oneValue _ _ _
          (greenprod.vecScale_ofPos _ p.1))
        (scaleFlat (posK1 _ u.2 u1.2 _) p.1)))
      ?_) m3
    refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
      (poly.oneValue_trans (poly.oneValue_of_eq
        (elim.vecAdd_eq_polyAdd _ _
          (((ground.length_map _ _).trans hAl).trans
            (((ground.length_map _ _).trans
              ((greenprod.offPad_len _ _).trans hB'l)).symm))))
        (poly.add_congr hW1 hW2))) ?_
    refine poly.oneValue_trans (elim.vecScale_oneValue _ _ _
      (poly.oneValue_of_eq (scaleAdd (BPair.ofPos ((ground.getAt greenprod.dM
          (X1 :: Xs1) j).2 * denProd (List.take j us1)))
        (greenprod.vecScale u1.2 (matVec A u.1)) (greenprod.vecScale u.2
            (matVec B u1.1))).symm)) ?_
    refine poly.oneValue_trans
      (scaleJoin (ground.mul_comm p.2 ((ground.getAt greenprod.dM (X1 :: Xs1)
          j).2 * denProd (List.take j us1))) _) ?_
    exact elim.vecScale_oneValue _ _ _
      (poly.oneValue_symm (greenprod.vecScale_ofPos p.2 _))

/-- At the ground root the kernel rows of the slab split close from
the far end: at the tail recursion's certificate and the rows at
unit sides, the cross-cleared head concatenation solves the head
decimated onto the depths at or below any stated depth, every row at
the sum's unit. -/
theorem head_kernel (diag off : List Mat) (Xs Rs : List greenprod.MatQ)
    (us ws : List greenprod.VecQ) (ns : List Nat) (j : Nat)
    (ht : greenprod.tailRead diag off Xs Rs ns)
    (hs : greenprod.solveRead diag off us ws ns)
    (hw : greenprod.sidesUnit ws)
    (hj : j + 1 ≤ us.length) :
    poly.unitTail (matVec
      (greenprod.headM diag off (ground.getAt greenprod.dM Xs j) j)
      (headVec (List.take (j + 1) us))) := by
  obtain ⟨hslab, hqs, hwr, hsteps⟩ := ht
  obtain ⟨_, hvs, _, hrows⟩ := hs
  cases diag with
  | nil => exact (hslab : False).elim
  | cons A diag1 =>
  cases ns with
  | nil => exact (hslab : False).elim
  | cons k ns1 =>
  cases Xs with
  | nil => exact (hqs : False).elim
  | cons X Xs1 =>
  cases us with
  | nil => exact (hvs : False).elim
  | cons u us1 =>
  exact unitTail_unscale _ (BPair.ofPos_off Pos.one) _
    (kernelGo j A diag1 off X Xs1 Rs k ns1 u us1 ws
      ([], Pos.one) hslab hqs hwr hvs hsteps hrows hw hj
      (Nat.zero_le k))

/-- The gap's covariance in the earlier read's joint rescaling:
rescaling both members of the earlier read rescales the gap. -/
theorem readGap_scaleL (c : Pos) (a g : BPair) (r : BPair × BPair) :
    (readGap (a.scale c, g.scale c) r).oneValue
      ((readGap (a, g) r).scale c) := by
  refine BPair.oneValue_of_eq ?_
  show r.1 * g.scale c + (a.scale c * r.2).swap
    = (r.1 * g + (a * r.2).swap).scale c
  rw [BPair.mul_scale r.1 g c, ← BPair.scale_mul_left a r.2 c,
    BPair.scale_add]
  rfl

/-- The gap's covariance in the later read's joint rescaling. -/
theorem readGap_scaleR (c : Pos) (a g : BPair) (r : BPair × BPair) :
    (readGap r (a.scale c, g.scale c)).oneValue
      ((readGap r (a, g)).scale c) := by
  refine BPair.oneValue_of_eq ?_
  show a.scale c * r.2 + (r.1 * g.scale c).swap
    = (a * r.2 + (r.1 * g).swap).scale c
  rw [← BPair.scale_mul_left a r.2 c, BPair.mul_scale r.1 g c,
    BPair.scale_add]
  rfl

/-- The gap's congruence in its four members. -/
theorem readGap_congr {a g b h a' g' b' h' : BPair}
    (h1 : a.oneValue a') (h2 : g.oneValue g')
    (h3 : b.oneValue b') (h4 : h.oneValue h') :
    (readGap (a, g) (b, h)).oneValue (readGap (a', g') (b', h')) :=
  BPair.add_congr (BPair.mul_congr h3 h2)
    (ground.swap_congr (BPair.mul_congr h1 h4))

/-- A positively rescaled family's self-pairing is the clearing's
square against the family's own. -/
private theorem gvsSelf (w : Pos) (v : List BPair) :
    (dotN (greenprod.vecScale w v) (greenprod.vecScale w v)).oneValue
      ((dotN v v).scale (w * w)) :=
  BPair.oneValue_trans
    (BPair.oneValue_trans
      (dotN_congrL _ _ _ (greenprod.vecScale_ofPos w v))
      (dotN_congrR _ _ _ (greenprod.vecScale_ofPos w v)))
    (BPair.oneValue_trans (dotN_vecScale_self (BPair.ofPos w) v)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.ofPos_mul w w)
          (BPair.oneValue_refl (dotN v v)))
        (BPair.ofPos_scale (w * w) (dotN v v))))

/-- A block's self-pairing at its own withdrawn clearing sits at or
below the joined head's over the blocks at or below that block's
depth: the leading blocks' pairing sits at or above the sum's unit
and the block's own rescales into the part beyond them. -/
theorem blockWeight_le : ∀ (j : Nat) (vs : List greenprod.VecQ),
    j < vs.length →
    (dotN (ground.getAt ([], Pos.one) vs j).1
        (ground.getAt ([], Pos.one) vs j).1).scale
      (denProd (List.take j vs) * denProd (List.take j vs))
      ≤ dotN (headVec (List.take (j + 1) vs))
        (headVec (List.take (j + 1) vs))
  | _, [], hj => absurd hj (Nat.not_lt_zero _)
  | 0, u :: t, _ => by
    have hc : poly.oneValue
        (greenprod.vecScale Pos.one u.1
          ++ greenprod.vecScale u.2 (headVec [])) u.1 :=
      poly.oneValue_trans
        (appUnitR (greenprod.vecScale Pos.one u.1) _ trivial)
        (scaleOne u.1)
    have hd : (dotN (greenprod.vecScale Pos.one u.1
          ++ greenprod.vecScale u.2 (headVec []))
        (greenprod.vecScale Pos.one u.1
          ++ greenprod.vecScale u.2 (headVec []))).oneValue
        (dotN u.1 u.1) :=
      BPair.oneValue_trans (dotN_congrL _ _ _ hc) (dotN_congrR _ _ _ hc)
    show (dotN u.1 u.1).scale (Pos.one * Pos.one)
      ≤ dotN (greenprod.vecScale Pos.one u.1
          ++ greenprod.vecScale u.2 (headVec []))
        (greenprod.vecScale Pos.one u.1
          ++ greenprod.vecScale u.2 (headVec []))
    rw [ground.mul_one, BPair.scale_one]
    exact ground.leB_congr_right (BPair.oneValue_symm hd)
      (ground.leB_refl _)
  | j + 1, u :: t, hj => by
    show (dotN (ground.getAt ([], Pos.one) t j).1
          (ground.getAt ([], Pos.one) t j).1).scale
        (u.2 * denProd (List.take j t) * (u.2 * denProd (List.take j t)))
      ≤ dotN (greenprod.vecScale (denProd (List.take (j + 1) t)) u.1
          ++ greenprod.vecScale u.2 (headVec (List.take (j + 1) t)))
        (greenprod.vecScale (denProd (List.take (j + 1) t)) u.1
          ++ greenprod.vecScale u.2 (headVec (List.take (j + 1) t)))
    rw [ground.mul_comm u.2 (denProd (List.take j t)),
      ← ground.mul_mul_mul_comm (denProd (List.take j t))
        (denProd (List.take j t)) u.2 u.2,
      ← BPair.scale_scale]
    refine ground.leB_trans
      (ground.leB_congr_right
        (BPair.oneValue_symm (gvsSelf u.2 (headVec (List.take (j + 1) t))))
        (ground.leB_scale
          (blockWeight_le j t (Nat.lt_of_succ_lt_succ hj)) (u.2 * u.2)))
      ?_
    refine ground.leB_trans
      (ground.leB_congr_left (BPair.unit_add _)
        (ground.leB_add
          (ground.leB_of_not_lt (dotN_self_side
            (greenprod.vecScale (denProd (List.take (j + 1) t)) u.1)))
          (ground.leB_refl _)))
      (ground.leB_congr_right
        (BPair.oneValue_symm (dotN_app _ _ _ _ rfl))
        (ground.leB_refl _))

/-- The tail weights' joined sum along a list of cleared vectors: per
block the gap's form at that block's own slab gram against that
block's component, priced by the squared clearings of the blocks
past it, the squared clearings' product the joined clearing — the
gram list one gram per slab, the gram's slab blocks at
`lem:greenprod`'s split. -/
def tailSum : List Mat → List greenprod.VecQ → BPair × Pos
  | _, [] => (BPair.unit, Pos.one)
  | Gs, u :: t =>
      BPair.addQ (inertia.quadForm (ground.getAt [] Gs 0) u.1, u.2 * u.2)
        (tailSum (Gs.drop 1) t)

/-- The tail weights' joined clearing is the clearings' product
against itself. -/
theorem tailSum_den (Gs : List Mat) : ∀ vs : List greenprod.VecQ,
    (tailSum Gs vs).2 = denProd vs * denProd vs
  | [] => (ground.mul_one _).symm
  | u :: t => by
    show u.2 * u.2 * (tailSum (Gs.drop 1) t).2
      = u.2 * denProd t * (u.2 * denProd t)
    rw [tailSum_den (Gs.drop 1) t, ground.mul_mul_mul_comm]

/-- The cross-cleared head's self-pairing reads the tail weights'
sum at the unit grams of the slabs' own orders, every block's
component at its slab's order. -/
theorem headVec_weight : ∀ (vs : List greenprod.VecQ)
    (ns : List Nat), greenprod.vShape vs ns →
    (dotN (headVec vs) (headVec vs)).oneValue
      (tailSum (ns.map inertia.idMat) vs).1
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], h => h.elim
  | u :: t, k :: ns, h => by
    have hu : (dotN u.1 u.1).oneValue (inertia.quadForm (idMat k) u.1) :=
      BPair.oneValue_symm
        (dotN_congrR u.1 _ _
          (inertia.matVec_idMat k u.1 h.1))
    show (dotN (greenprod.vecScale (denProd t) u.1
          ++ greenprod.vecScale u.2 (headVec t))
        (greenprod.vecScale (denProd t) u.1
          ++ greenprod.vecScale u.2 (headVec t))).oneValue
      ((inertia.quadForm (idMat k) u.1).scale
          (tailSum (ns.map inertia.idMat) t).2
        + (tailSum (ns.map inertia.idMat) t).1.scale (u.2 * u.2))
    rw [tailSum_den (ns.map inertia.idMat) t]
    refine BPair.oneValue_trans (dotN_app _ _ _ _ rfl) ?_
    refine BPair.add_congr ?_ ?_
    · exact BPair.oneValue_trans (gvsSelf (denProd t) u.1)
        (BPair.scale_congr (denProd t * denProd t) hu)
    · exact BPair.oneValue_trans (gvsSelf u.2 (headVec t))
        (BPair.scale_congr (u.2 * u.2)
          (headVec_weight t ns h.2))

/-- The certificates' fold along the tail witnesses: at each step the
certificate's two squared members against the fold beyond it joined to
its own clearing, the sum's unit at the vacant list. -/
def tailFold : List ((k : Nat) × Pos × Pos × Split k) → BPair × Pos
  | [] => (BPair.unit, Pos.one)
  | c :: cs =>
      (((tailFold cs).1 + BPair.ofPos (tailFold cs).2).scale
          (c.2.1 * c.2.1),
       c.2.2.1 * c.2.2.1 * (tailFold cs).2)

/-- The Horner fold's clearing is the second members' fold
squared. -/
theorem tailFold_certD : ∀ cs : List ((k : Nat) × Pos × Pos × Split k),
    (tailFold cs).2 = certD cs * certD cs
  | [] => (ground.mul_one Pos.one).symm
  | c :: cs => by
    show c.2.2.1 * c.2.2.1 * (tailFold cs).2
      = c.2.2.1 * certD cs * (c.2.2.1 * certD cs)
    rw [tailFold_certD cs,
      ground.mul_mul_mul_comm c.2.2.1 (certD cs) c.2.2.1 (certD cs)]

/-- The certificates' fold sits at or above the sum's unit at its
first member. -/
private theorem tailFold_unitLe :
    ∀ cs : List ((k : Nat) × Pos × Pos × Split k),
    BPair.unit ≤ (tailFold cs).1
  | [] => ground.leB_refl _
  | c :: cs => by
    show BPair.unit
      ≤ (((tailFold cs).1 + BPair.ofPos (tailFold cs).2).scale
        (c.2.1 * c.2.1))
    refine ground.leB_congr_left
      (BPair.oneValue_symm (ground.unitScale (c.2.1 * c.2.1))) ?_
    refine ground.leB_scale ?_ (c.2.1 * c.2.1)
    exact ground.leB_congr_left (BPair.add_unit BPair.unit)
      (ground.leB_add (tailFold_unitLe cs)
        (ground.leB_of_lt (ground.unitLtOfPos (tailFold cs).2)))

/-- The step's clearings regroup at the anchor's square. -/
private theorem posQ1 (D a Dt F2 : Pos) :
    D * a * (Dt * F2) = Dt * (D * F2 * a) := by
  rw [ground.mul_right_comm D F2 a, ← ground.mul_assoc Dt (D * a) F2,
    ground.mul_comm Dt (D * a), ← ground.mul_assoc (D * a) Dt F2]

/-- The step's clearings regroup at the leading block's square. -/
private theorem posQ2 (D a d F2 : Pos) :
    F2 * d * (D * a) = d * (D * F2 * a) := by
  rw [ground.mul_right_comm D F2 a, ← ground.mul_assoc d (D * a) F2,
    ground.mul_comm d (D * a), ground.mul_comm F2 d,
    ground.mul_comm (d * F2) (D * a), ← ground.mul_assoc (D * a) d F2]

/-- The fold's clearing regroups against the joined clearing. -/
private theorem posQ3 (N d Dt F2 : Pos) :
    F2 * N * (d * Dt) = N * d * (Dt * F2) := by
  rw [ground.mul_comm F2 N, ground.mul_assoc N F2 (d * Dt),
    ground.mul_assoc N d (Dt * F2), ground.mul_left_comm F2 d Dt,
    ground.mul_comm F2 Dt]

/-- The tail weights' walk: at the certificates and the ascending
telescope anchored at a depth, the weights beyond that depth sum at
or below the depth's own weight against the certificates' fold, each
block's form read at its own slab's gram. -/
private theorem priceGo :
    ∀ (us : List greenprod.VecQ) (j : Nat) (Gs : List Mat)
      (Rs : List greenprod.MatQ)
      (cs : List ((k : Nat) × Pos × Pos × Split k)) (ns : List Nat),
    greenprod.gramShape Gs ns → capList Gs Rs cs →
    greenprod.teleUp Rs us j ns →
    (tailSum (Gs.drop (j + 1)) (us.drop (j + 1))).1.scale
        ((tailFold (cs.drop j)).2
          * ((ground.getAt ([], Pos.one) us j).2
            * (ground.getAt ([], Pos.one) us j).2))
      ≤ (inertia.quadForm (ground.getAt [] Gs j)
            (ground.getAt ([], Pos.one) us j).1
          * (tailFold (cs.drop j)).1).scale
        (tailSum (Gs.drop (j + 1)) (us.drop (j + 1))).2 := by
  intro us
  induction us with
  | nil =>
    intro j Gs Rs cs ns _ _ hw
    cases ns with
    | cons k ns1 => exact (hw.2.1 : False).elim
    | nil =>
      cases Rs with
      | nil => exact (hw.1 : False).elim
      | cons R Rs1 => exact (hw.1 : False).elim
  | cons u0 rest ih =>
    intro j Gs Rs cs ns hg hc hw
    cases j with
    | succ i =>
      cases Rs with
      | nil => exact (hw.2.2 : False).elim
      | cons R Rs1 =>
      cases ns with
      | nil => exact (hw.1 : False).elim
      | cons k ns1 =>
      cases ns1 with
      | nil => exact (hw.1 : False).elim
      | cons k' ns2 =>
      cases cs with
      | nil => exact (hc : False).elim
      | cons c cs1 =>
      cases Gs with
      | nil => exact (hg : False).elim
      | cons G0 Gs1 =>
      exact ih i Gs1 Rs1 cs1 (k' :: ns2) hg.2 hc.2
        ⟨hw.1.2, hw.2.1.2, hw.2.2⟩
    | zero =>
      cases rest with
      | nil =>
        cases Rs with
        | cons R Rs1 =>
          cases ns with
          | nil => exact (hw.1 : False).elim
          | cons k ns1 =>
            cases ns1 with
            | nil => exact (hw.1 : False).elim
            | cons k' ns2 => exact (hw.2.1.2 : False).elim
        | nil =>
        cases ns with
        | nil => exact (hw.1 : False).elim
        | cons k ns1 =>
        cases ns1 with
        | cons k' ns2 => exact (hw.2.1.2 : False).elim
        | nil =>
        cases cs with
        | cons c cs1 => exact (hc : False).elim
        | nil =>
        show BPair.unit.scale (Pos.one * (u0.2 * u0.2))
          ≤ (inertia.quadForm (ground.getAt [] Gs 0) u0.1
            * BPair.unit).scale Pos.one
        exact ground.leB_congr (ground.unitScale _)
          (BPair.oneValue_symm
            (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.scale_one _))
              (BPair.mul_unit _)))
          (ground.leB_refl BPair.unit)
      | cons u1 rest1 =>
        cases Rs with
        | nil => exact (hw.2.2 : False).elim
        | cons R Rs1 =>
        cases cs with
        | nil => exact (hc : False).elim
        | cons c cs1 =>
        cases ns with
        | nil => exact (hw.1 : False).elim
        | cons k ns1 =>
        cases ns1 with
        | nil => exact (hw.1 : False).elim
        | cons k' ns2 =>
        cases Gs with
        | nil => exact (hg : False).elim
        | cons G0 Gs1 =>
        have hIH : (tailSum (Gs1.drop 1) rest1).1.scale
              ((tailFold cs1).2 * (u1.2 * u1.2))
            ≤ (inertia.quadForm (ground.getAt [] Gs1 0) u1.1
                * (tailFold cs1).1).scale
              (tailSum (Gs1.drop 1) rest1).2 :=
          ih 0 Gs1 Rs1 cs1 (k' :: ns2) hg.2 hc.2
            ⟨hw.1.2, hw.2.1.2, hw.2.2.2⟩
        have hone : (inertia.quadForm (ground.getAt [] Gs1 0) u1.1).scale
              (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2))
            ≤ (inertia.quadForm G0 u0.1).scale
              (c.2.1 * c.2.1 * (u1.2 * u1.2)) := by
          have h : (inertia.quadForm (ground.getAt [] Gs1 0) u1.1).scale
                (c.2.2.1 * c.2.2.1 * Pos.one * (u0.2 * u0.2))
              ≤ (inertia.quadForm G0 u0.1).scale
                (c.2.1 * c.2.1 * Pos.one * (u1.2 * u1.2)) :=
            weight_chain (G0 :: Gs1) (R :: Rs1) (c :: cs1)
              (u0 :: u1 :: rest1) (k :: k' :: ns2) hg hc hw 1
              (Nat.succ_lt_succ (Nat.succ_pos rest1.length))
          rw [ground.mul_one, ground.mul_one] at h
          exact h
        have hT1 : ((inertia.quadForm (ground.getAt [] Gs1 0) u1.1).scale
                (tailSum (Gs1.drop 1) rest1).2).scale
              (c.2.2.1 * c.2.2.1 * (tailFold cs1).2 * (u0.2 * u0.2))
            ≤ ((inertia.quadForm G0 u0.1).scale
                (c.2.1 * c.2.1 * (u1.2 * u1.2))).scale
              ((tailSum (Gs1.drop 1) rest1).2 * (tailFold cs1).2) := by
          refine ground.leB_congr_left (BPair.oneValue_of_eq ?_)
            (ground.leB_scale hone
              ((tailSum (Gs1.drop 1) rest1).2 * (tailFold cs1).2))
          rw [BPair.scale_scale, BPair.scale_scale,
            posQ1 (c.2.2.1 * c.2.2.1) (u0.2 * u0.2)
              (tailSum (Gs1.drop 1) rest1).2 (tailFold cs1).2]
        have hmul : (inertia.quadForm (ground.getAt [] Gs1 0) u1.1).scale
              (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2)) * (tailFold cs1).1
            ≤ (inertia.quadForm G0 u0.1).scale
              (c.2.1 * c.2.1 * (u1.2 * u1.2)) * (tailFold cs1).1 := by
          rw [BPair.mul_comm
              ((inertia.quadForm (ground.getAt [] Gs1 0) u1.1).scale
                (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2))) (tailFold cs1).1,
            BPair.mul_comm ((inertia.quadForm G0 u0.1).scale
              (c.2.1 * c.2.1 * (u1.2 * u1.2))) (tailFold cs1).1]
          exact ground.leB_mulR (tailFold_unitLe cs1) hone
        have hT2 : ((tailSum (Gs1.drop 1) rest1).1.scale (u1.2 * u1.2)).scale
              (c.2.2.1 * c.2.2.1 * (tailFold cs1).2 * (u0.2 * u0.2))
            ≤ ((inertia.quadForm G0 u0.1).scale
                  (c.2.1 * c.2.1 * (u1.2 * u1.2))
                * (tailFold cs1).1).scale
              (tailSum (Gs1.drop 1) rest1).2 := by
          refine ground.leB_trans
            (ground.leB_congr_left (BPair.oneValue_of_eq ?_)
              (ground.leB_scale hIH (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2)))) ?_
          · rw [BPair.scale_scale, BPair.scale_scale,
              posQ2 (c.2.2.1 * c.2.2.1) (u0.2 * u0.2) (u1.2 * u1.2)
                (tailFold cs1).2]
          · refine ground.leB_congr_left (BPair.oneValue_of_eq ?_)
              (ground.leB_scale hmul (tailSum (Gs1.drop 1) rest1).2)
            rw [BPair.scale_mul_left, BPair.scale_scale, BPair.scale_scale,
              ground.mul_comm (tailSum (Gs1.drop 1) rest1).2
                (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2)),
              ← BPair.scale_mul_left
                (inertia.quadForm (ground.getAt [] Gs1 0) u1.1)
                (tailFold cs1).1
                (c.2.2.1 * c.2.2.1 * (u0.2 * u0.2)
                  * (tailSum (Gs1.drop 1) rest1).2)]
        have hB : ((inertia.quadForm G0 u0.1
              * (tailFold cs1).1.scale (c.2.1 * c.2.1)).scale
                ((u1.2 * u1.2) * (tailSum (Gs1.drop 1) rest1).2)).oneValue
            (((inertia.quadForm G0 u0.1).scale (c.2.1 * c.2.1 * (u1.2 * u1.2))
                * (tailFold cs1).1).scale (tailSum (Gs1.drop 1) rest1).2) := by
          refine BPair.oneValue_of_eq ?_
          rw [BPair.mul_scale, BPair.scale_scale,
            ← BPair.scale_mul_left (inertia.quadForm G0 u0.1)
              (tailFold cs1).1 (c.2.1 * c.2.1 * (u1.2 * u1.2)),
            BPair.scale_scale,
            ground.mul_assoc (c.2.1 * c.2.1) (u1.2 * u1.2)
              (tailSum (Gs1.drop 1) rest1).2]
        have hA : ((inertia.quadForm G0 u0.1
              * (BPair.ofPos (tailFold cs1).2).scale (c.2.1 * c.2.1)).scale
                ((u1.2 * u1.2) * (tailSum (Gs1.drop 1) rest1).2)).oneValue
            (((inertia.quadForm G0 u0.1).scale
                (c.2.1 * c.2.1 * (u1.2 * u1.2))).scale
              ((tailSum (Gs1.drop 1) rest1).2 * (tailFold cs1).2)) := by
          refine BPair.oneValue_trans
            (BPair.scale_congr ((u1.2 * u1.2) * (tailSum (Gs1.drop 1) rest1).2)
              (BPair.mul_congr (BPair.oneValue_refl _)
                (BPair.scale_ofPos (tailFold cs1).2 (c.2.1 * c.2.1)))) ?_
          rw [BPair.mul_comm (inertia.quadForm G0 u0.1)
            (BPair.ofPos ((tailFold cs1).2 * (c.2.1 * c.2.1)))]
          refine BPair.oneValue_trans
            (BPair.scale_congr ((u1.2 * u1.2) * (tailSum (Gs1.drop 1) rest1).2)
              (BPair.ofPos_scale ((tailFold cs1).2 * (c.2.1 * c.2.1))
                (inertia.quadForm G0 u0.1))) ?_
          rw [BPair.scale_scale, BPair.scale_scale,
            posQ3 (c.2.1 * c.2.1) (u1.2 * u1.2)
              (tailSum (Gs1.drop 1) rest1).2 (tailFold cs1).2]
          exact BPair.oneValue_refl _
        show ((inertia.quadForm (ground.getAt [] Gs1 0) u1.1).scale
                (tailSum (Gs1.drop 1) rest1).2
              + (tailSum (Gs1.drop 1) rest1).1.scale (u1.2 * u1.2)).scale
            (c.2.2.1 * c.2.2.1 * (tailFold cs1).2 * (u0.2 * u0.2))
          ≤ (inertia.quadForm G0 u0.1
              * (((tailFold cs1).1 + BPair.ofPos (tailFold cs1).2).scale
                  (c.2.1 * c.2.1))).scale
            ((u1.2 * u1.2) * (tailSum (Gs1.drop 1) rest1).2)
        refine ground.leB_congr
          (BPair.oneValue_of_eq
            (BPair.scale_add
              ((inertia.quadForm (ground.getAt [] Gs1 0) u1.1).scale
                (tailSum (Gs1.drop 1) rest1).2)
              ((tailSum (Gs1.drop 1) rest1).1.scale (u1.2 * u1.2))
              (c.2.2.1 * c.2.2.1 * (tailFold cs1).2 * (u0.2 * u0.2))).symm)
          ?_ (ground.leB_add hT1 hT2)
        refine BPair.oneValue_symm ?_
        rw [BPair.scale_add (tailFold cs1).1
            (BPair.ofPos (tailFold cs1).2) (c.2.1 * c.2.1),
          BPair.left_distrib, BPair.scale_add,
          BPair.add_comm ((inertia.quadForm G0 u0.1
              * (tailFold cs1).1.scale (c.2.1 * c.2.1)).scale
            ((u1.2 * u1.2) * (tailSum (Gs1.drop 1) rest1).2))
            ((inertia.quadForm G0 u0.1
              * (BPair.ofPos (tailFold cs1).2).scale (c.2.1 * c.2.1)).scale
            ((u1.2 * u1.2) * (tailSum (Gs1.drop 1) rest1).2))]
        exact BPair.add_congr hA hB

/-- The tail weights' price: at the certificates and the ascending
telescope anchored at the depth `j`, the weights of every depth beyond
`j` sum at or below the depth-`j` weight against the certificates'
fold from that depth, each block's form at its own slab's gram and
the two joined clearings riding the comparison. -/
theorem tail_price (Gs : List Mat) (Rs : List greenprod.MatQ)
    (cs : List ((k : Nat) × Pos × Pos × Split k))
    (us : List greenprod.VecQ) (ns : List Nat) (j : Nat)
    (hg : greenprod.gramShape Gs ns) (hc : capList Gs Rs cs)
    (hw : greenprod.teleUp Rs us j ns) :
    (tailSum (Gs.drop (j + 1)) (us.drop (j + 1))).1.scale
        ((tailFold (cs.drop j)).2
          * ((ground.getAt ([], Pos.one) us j).2
            * (ground.getAt ([], Pos.one) us j).2))
      ≤ (inertia.quadForm (ground.getAt [] Gs j)
            (ground.getAt ([], Pos.one) us j).1
          * (tailFold (cs.drop j)).1).scale
        (tailSum (Gs.drop (j + 1)) (us.drop (j + 1))).2 :=
  priceGo us j Gs Rs cs ns hg hc hw

/-! The ride's price: the head-side blocks priced at the source
slab along the descending telescope. -/

/-- The chain's upper clearing reads the reversed list's own. -/
private theorem prodN_rev (l : List ((k : Nat) × Pos × Pos × Split k)) :
    prodN l.reverse = prodN l :=
  ground.famFold_rev (· * ·) Pos.one ground.mul_assoc ground.one_mul
    ground.mul_comm
    (fun c : ((k : Nat) × Pos × Pos × Split k) => c.2.1 * c.2.1) l

/-- The chain's lower clearing reads the reversed list's own. -/
private theorem prodD_rev (l : List ((k : Nat) × Pos × Pos × Split k)) :
    prodD l.reverse = prodD l :=
  ground.famFold_rev (· * ·) Pos.one ground.mul_assoc ground.one_mul
    ground.mul_comm
    (fun c : ((k : Nat) × Pos × Pos × Split k) => c.2.2.1 * c.2.2.1) l

/-- The certificates' fold carries the chain's lower clearing. -/
private theorem foldDen :
    ∀ l : List ((k : Nat) × Pos × Pos × Split k),
    (tailFold l).2 = prodD l
  | [] => rfl
  | c :: l => by
    show c.2.2.1 * c.2.2.1 * (tailFold l).2
      = c.2.2.1 * c.2.2.1 * prodD l
    rw [foldDen l]

/-- A leading segment's product splits at any cut within it. -/
private theorem posTakeSplit {a : Type} (f : a → Pos) :
    ∀ (m j : Nat) (l : List a),
    ground.famFold (· * ·) Pos.one f (List.take (j + m) l)
      = ground.famFold (· * ·) Pos.one f (List.take m l)
        * ground.famFold (· * ·) Pos.one f
            (List.take j (List.drop m l))
  | 0, j, l => (ground.one_mul _).symm
  | m + 1, j, [] => by
    show ground.famFold (· * ·) Pos.one f ([] : List a)
      = ground.famFold (· * ·) Pos.one f ([] : List a)
        * ground.famFold (· * ·) Pos.one f (List.take j ([] : List a))
    rw [List.take_nil]
    show Pos.one = Pos.one * Pos.one
    rw [ground.mul_one]
  | m + 1, j, x :: l => by
    show f x * ground.famFold (· * ·) Pos.one f (List.take (j + m) l)
      = f x * ground.famFold (· * ·) Pos.one f (List.take m l)
        * ground.famFold (· * ·) Pos.one f
            (List.take j (List.drop m l))
    rw [posTakeSplit f m j l, ground.mul_assoc]

/-- The chain's upper clearing splits at any cut within the leading
segment. -/
private theorem prodN_takeSplit (m j : Nat)
    (l : List ((k : Nat) × Pos × Pos × Split k)) :
    prodN (List.take (j + m) l)
      = prodN (List.take m l) * prodN (List.take j (List.drop m l)) :=
  posTakeSplit _ m j l

/-- The chain's lower clearing splits at any cut within the leading
segment. -/
private theorem prodD_takeSplit (m j : Nat)
    (l : List ((k : Nat) × Pos × Pos × Split k)) :
    prodD (List.take (j + m) l)
      = prodD (List.take m l) * prodD (List.take j (List.drop m l)) :=
  posTakeSplit _ m j l

/-- The certificates' fold at a certificate joined past the list:
the list's own fold at the joined certificate's lower square, joined
to the list's upper product at its upper square, the two clearings
composing. -/
private theorem foldApp :
    ∀ (l : List ((k : Nat) × Pos × Pos × Split k))
      (c : (k : Nat) × Pos × Pos × Split k),
    ((tailFold (l ++ [c])).1).oneValue
        ((tailFold l).1.scale (c.2.2.1 * c.2.2.1)
          + (BPair.ofPos (prodN l)).scale (c.2.1 * c.2.1))
      ∧ (tailFold (l ++ [c])).2 = (tailFold l).2 * (c.2.2.1 * c.2.2.1)
  | [], c => by
    refine ⟨?_, ?_⟩
    · show ((BPair.unit + BPair.ofPos Pos.one).scale
          (c.2.1 * c.2.1)).oneValue
        (BPair.unit.scale (c.2.2.1 * c.2.2.1)
          + (BPair.ofPos Pos.one).scale (c.2.1 * c.2.1))
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.scale_add _ _ _)) ?_
      exact BPair.add_congr
        (BPair.oneValue_trans
          (BPair.oneValue_symm (ground.unitScale (c.2.1 * c.2.1)))
          (ground.unitScale (c.2.2.1 * c.2.2.1)))
        (BPair.oneValue_refl _)
    · show c.2.2.1 * c.2.2.1 * Pos.one = Pos.one * (c.2.2.1 * c.2.2.1)
      rw [ground.mul_one, ground.one_mul]
  | a :: l, c => by
    have ih := foldApp l c
    refine ⟨?_, ?_⟩
    · have s2 : ((tailFold ((a :: l) ++ [c])).1).oneValue
          (((tailFold l).1.scale (c.2.2.1 * c.2.2.1)
              + (BPair.ofPos (prodN l)).scale (c.2.1 * c.2.1)
              + BPair.ofPos ((tailFold l).2 * (c.2.2.1 * c.2.2.1))).scale
            (a.2.1 * a.2.1)) :=
        BPair.scale_congr (a.2.1 * a.2.1)
          (BPair.add_congr ih.1
            (BPair.oneValue_of_eq (congrArg BPair.ofPos ih.2)))
      have s3 : (((tailFold l).1.scale (c.2.2.1 * c.2.2.1)
              + (BPair.ofPos (prodN l)).scale (c.2.1 * c.2.1)
              + BPair.ofPos ((tailFold l).2 * (c.2.2.1 * c.2.2.1))).scale
            (a.2.1 * a.2.1))
          = ((tailFold l).1.scale (c.2.2.1 * c.2.2.1)).scale
              (a.2.1 * a.2.1)
            + (BPair.ofPos ((tailFold l).2 * (c.2.2.1 * c.2.2.1))).scale
                (a.2.1 * a.2.1)
            + ((BPair.ofPos (prodN l)).scale (c.2.1 * c.2.1)).scale
                (a.2.1 * a.2.1) := by
        rw [BPair.scale_add, BPair.scale_add, BPair.add_assoc,
          BPair.add_comm
            (((BPair.ofPos (prodN l)).scale (c.2.1 * c.2.1)).scale
              (a.2.1 * a.2.1))
            ((BPair.ofPos ((tailFold l).2 * (c.2.2.1 * c.2.2.1))).scale
              (a.2.1 * a.2.1)),
          ← BPair.add_assoc]
      have h1 : (((tailFold l).1.scale (c.2.2.1 * c.2.2.1)).scale
            (a.2.1 * a.2.1)).oneValue
          (((tailFold l).1.scale (a.2.1 * a.2.1)).scale
            (c.2.2.1 * c.2.2.1)) :=
        BPair.oneValue_of_eq (by
          rw [BPair.scale_scale, BPair.scale_scale,
            ground.mul_comm (c.2.2.1 * c.2.2.1) (a.2.1 * a.2.1)])
      have h3 : ((BPair.ofPos ((tailFold l).2 * (c.2.2.1 * c.2.2.1))).scale
            (a.2.1 * a.2.1)).oneValue
          (((BPair.ofPos (tailFold l).2).scale (a.2.1 * a.2.1)).scale
            (c.2.2.1 * c.2.2.1)) := by
        refine BPair.oneValue_trans
          (BPair.scale_congr (a.2.1 * a.2.1)
            (BPair.oneValue_symm
              (BPair.scale_ofPos (tailFold l).2 (c.2.2.1 * c.2.2.1)))) ?_
        exact BPair.oneValue_of_eq (by
          rw [BPair.scale_scale, BPair.scale_scale,
            ground.mul_comm (c.2.2.1 * c.2.2.1) (a.2.1 * a.2.1)])
      have h2 : (((BPair.ofPos (prodN l)).scale (c.2.1 * c.2.1)).scale
            (a.2.1 * a.2.1)).oneValue
          ((BPair.ofPos (a.2.1 * a.2.1 * prodN l)).scale
            (c.2.1 * c.2.1)) := by
        have e : (((BPair.ofPos (prodN l)).scale (c.2.1 * c.2.1)).scale
              (a.2.1 * a.2.1))
            = ((BPair.ofPos (prodN l)).scale (a.2.1 * a.2.1)).scale
              (c.2.1 * c.2.1) := by
          rw [BPair.scale_scale, BPair.scale_scale,
            ground.mul_comm (c.2.1 * c.2.1) (a.2.1 * a.2.1)]
        refine BPair.oneValue_trans (BPair.oneValue_of_eq e) ?_
        refine BPair.scale_congr (c.2.1 * c.2.1) ?_
        refine BPair.oneValue_trans
          (BPair.scale_ofPos (prodN l) (a.2.1 * a.2.1)) ?_
        exact BPair.oneValue_of_eq
          (congrArg BPair.ofPos
            (ground.mul_comm (prodN l) (a.2.1 * a.2.1)))
      have s5 : ((((tailFold l).1 + BPair.ofPos (tailFold l).2).scale
              (a.2.1 * a.2.1)).scale (c.2.2.1 * c.2.2.1)
            + (BPair.ofPos (a.2.1 * a.2.1 * prodN l)).scale
                (c.2.1 * c.2.1))
          = (((tailFold l).1.scale (a.2.1 * a.2.1)).scale
                (c.2.2.1 * c.2.2.1)
              + ((BPair.ofPos (tailFold l).2).scale
                  (a.2.1 * a.2.1)).scale (c.2.2.1 * c.2.2.1))
            + (BPair.ofPos (a.2.1 * a.2.1 * prodN l)).scale
                (c.2.1 * c.2.1) := by
        rw [BPair.scale_add, BPair.scale_add]
      show ((tailFold ((a :: l) ++ [c])).1).oneValue
        ((((tailFold l).1 + BPair.ofPos (tailFold l).2).scale
              (a.2.1 * a.2.1)).scale (c.2.2.1 * c.2.2.1)
          + (BPair.ofPos (a.2.1 * a.2.1 * prodN l)).scale (c.2.1 * c.2.1))
      refine BPair.oneValue_trans s2
        (BPair.oneValue_trans (BPair.oneValue_of_eq s3)
          (BPair.oneValue_trans
            (BPair.add_congr (BPair.add_congr h1 h3) h2)
            (BPair.oneValue_of_eq s5.symm)))
    · show a.2.2.1 * a.2.2.1 * (tailFold (l ++ [c])).2
        = a.2.2.1 * a.2.2.1 * (tailFold l).2 * (c.2.2.1 * c.2.2.1)
      rw [ih.2, ← ground.mul_assoc (a.2.2.1 * a.2.2.1) (tailFold l).2
        (c.2.2.1 * c.2.2.1)]

/-- The descending chain's walk: along the telescope below the
source at the descending certificate list, the head block's weight
at its own slab's gram sits at or below the source slab's against
the certificates' product down to it. -/
private theorem chainDownGo :
    ∀ (jb : Nat) (Gs : List Mat) (Cs : List greenprod.MatQ)
      (cs : List ((k : Nat) × Pos × Pos × Split k))
      (us : List greenprod.VecQ) (ns : List Nat),
    greenprod.gramShape Gs ns → capListDown Gs Cs cs →
    greenprod.teleDown Cs us jb ns → jb < us.length →
    (inertia.quadForm (ground.getAt [] Gs 0)
        (ground.getAt ([], Pos.one) us 0).1).scale
        (prodD (cs.take jb)
          * ((ground.getAt ([], Pos.one) us jb).2
            * (ground.getAt ([], Pos.one) us jb).2))
      ≤ (inertia.quadForm (ground.getAt [] Gs jb)
          (ground.getAt ([], Pos.one) us jb).1).scale
        (prodN (cs.take jb)
          * ((ground.getAt ([], Pos.one) us 0).2
            * (ground.getAt ([], Pos.one) us 0).2)) := by
  intro jb
  induction jb with
  | zero => intro _ _ _ _ _ _ _ _ _; exact ground.leB_refl _
  | succ i ih =>
    intro Gs Cs cs us ns hg hc hw hjb
    cases us with
    | nil => exact absurd hjb (Nat.not_lt_zero _)
    | cons u0 rest =>
    cases rest with
    | nil => exact absurd (Nat.lt_of_succ_lt_succ hjb) (Nat.not_lt_zero _)
    | cons u1 rest1 =>
    cases Cs with
    | nil => exact (hw.2.2 : False).elim
    | cons C Cs1 =>
    cases cs with
    | nil => exact (hc : False).elim
    | cons c cs1 =>
    cases ns with
    | nil => exact (hw.1 : False).elim
    | cons k ns' =>
    cases ns' with
    | nil => exact (hw.1 : False).elim
    | cons k' ns'' =>
    cases Gs with
    | nil => exact (hg : False).elim
    | cons G0 Gs1 =>
    cases Gs1 with
    | nil => exact (hg.2 : False).elim
    | cons G1 Gs2 =>
    obtain ⟨hwC, hwv, hwalk⟩ := hw
    have hih : (inertia.quadForm G1 u1.1).scale
          (prodD (cs1.take i)
            * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
              * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))
        ≤ (inertia.quadForm (ground.getAt [] (G1 :: Gs2) i)
            (ground.getAt ([], Pos.one) (u1 :: rest1) i).1).scale
          (prodN (cs1.take i) * (u1.2 * u1.2)) :=
      ih (G1 :: Gs2) Cs1 cs1 (u1 :: rest1) (k' :: ns'') hg.2 hc.2
        ⟨hwC.2, hwv.2, hwalk.2⟩ (Nat.lt_of_succ_lt_succ hjb)
    have hck : c.1 = k' :=
      (sqAt_len hc.1.2.2.1).symm.trans (sqAt_len hg.2.1)
    have hu1 : u1.1.length = c.1 := hwv.2.1.trans hck.symm
    have hstep : (inertia.quadForm G0
          (matVec (matSwap C.1) u1.1)).scale (c.2.2.1 * c.2.2.1)
        ≤ (inertia.quadForm G1 u1.1).scale
          (c.2.1 * c.2.1 * (C.2 * C.2)) :=
      weight_step (greenprod.transfer C) G0 G1 c.2.1 c.2.2.1 c.2.2.2
        hc.1 u1.1 hu1
    have hx1 : poly.oneValue (greenprod.vecScale (C.2 * u1.2) u0.1)
        (vecScale (BPair.ofPos (C.2 * u1.2)) u0.1) :=
      greenprod.vecScale_ofPos _ _
    have hx2 : poly.oneValue (greenprod.vecScale (C.2 * u1.2) u0.1)
        (vecScale (BPair.ofPos u0.2) (matVec (matSwap C.1) u1.1)) :=
      poly.oneValue_trans hwalk.1 (greenprod.vecScale_ofPos _ _)
    have hrel : ((inertia.quadForm G0 u0.1).scale
          (C.2 * u1.2 * (C.2 * u1.2))).oneValue
        ((inertia.quadForm G0 (matVec (matSwap C.1) u1.1)).scale
          (u0.2 * u0.2)) :=
      BPair.oneValue_trans
        (BPair.oneValue_symm
          (sqScale (C.2 * u1.2) (inertia.quadForm G0 u0.1)))
        (BPair.oneValue_trans
          (BPair.oneValue_symm
            (inertia.quadScaleVec G0 (BPair.ofPos (C.2 * u1.2)) u0.1 _ hx1))
          (BPair.oneValue_trans
            (inertia.quadScaleVec G0 (BPair.ofPos u0.2) _ _ hx2)
            (sqScale u0.2 _)))
    have e1 : ((inertia.quadForm G0 (matVec (matSwap C.1) u1.1)).scale
          (c.2.2.1 * c.2.2.1)).scale (u0.2 * u0.2)
        = ((inertia.quadForm G0 (matVec (matSwap C.1) u1.1)).scale
          (u0.2 * u0.2)).scale (c.2.2.1 * c.2.2.1) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_comm (c.2.2.1 * c.2.2.1) (u0.2 * u0.2)]
    have e2 : ((inertia.quadForm G0 u0.1).scale
          (C.2 * u1.2 * (C.2 * u1.2))).scale (c.2.2.1 * c.2.2.1)
        = ((inertia.quadForm G0 u0.1).scale
          (c.2.2.1 * c.2.2.1 * (u1.2 * u1.2))).scale (C.2 * C.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        posE1 C.2 u1.2 (c.2.2.1 * c.2.2.1)]
    have e3 : ((inertia.quadForm G1 u1.1).scale
          (c.2.1 * c.2.1 * (C.2 * C.2))).scale (u0.2 * u0.2)
        = ((inertia.quadForm G1 u1.1).scale
          (c.2.1 * c.2.1 * (u0.2 * u0.2))).scale (C.2 * C.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_right_comm (c.2.1 * c.2.1) (C.2 * C.2) (u0.2 * u0.2)]
    have hone : (inertia.quadForm G0 u0.1).scale
          (c.2.2.1 * c.2.2.1 * (u1.2 * u1.2))
        ≤ (inertia.quadForm G1 u1.1).scale
          (c.2.1 * c.2.1 * (u0.2 * u0.2)) :=
      ground.leB_of_scale (w := C.2 * C.2)
        (ground.leB_congr
          (BPair.oneValue_trans (BPair.oneValue_of_eq e1)
            (BPair.oneValue_trans
              (BPair.scale_congr (c.2.2.1 * c.2.2.1)
                (BPair.oneValue_symm hrel))
              (BPair.oneValue_of_eq e2)))
          (BPair.oneValue_of_eq e3)
          (ground.leB_scale hstep (u0.2 * u0.2)))
    show (inertia.quadForm G0 u0.1).scale
        (c.2.2.1 * c.2.2.1 * prodD (cs1.take i)
          * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
            * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))
      ≤ (inertia.quadForm (ground.getAt [] (G1 :: Gs2) i)
          (ground.getAt ([], Pos.one) (u1 :: rest1) i).1).scale
        (c.2.1 * c.2.1 * prodN (cs1.take i) * (u0.2 * u0.2))
    refine ground.leB_of_scale (w := u1.2 * u1.2) ?_
    have mid : ((inertia.quadForm G1 u1.1).scale
          (c.2.1 * c.2.1 * (u0.2 * u0.2))).scale
          (prodD (cs1.take i)
            * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
              * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))
        = ((inertia.quadForm G1 u1.1).scale
            (prodD (cs1.take i)
              * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
                * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))).scale
          (c.2.1 * c.2.1 * (u0.2 * u0.2)) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_comm (c.2.1 * c.2.1 * (u0.2 * u0.2))
          (prodD (cs1.take i)
            * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
              * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))]
    have eL : ((inertia.quadForm G0 u0.1).scale
          (c.2.2.1 * c.2.2.1 * (u1.2 * u1.2))).scale
          (prodD (cs1.take i)
            * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
              * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))
        = ((inertia.quadForm G0 u0.1).scale
            (c.2.2.1 * c.2.2.1 * prodD (cs1.take i)
              * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
                * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))).scale
          (u1.2 * u1.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        posE4 (c.2.2.1 * c.2.2.1) (u1.2 * u1.2) (prodD (cs1.take i))
          ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
            * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2)]
    have eR : ((inertia.quadForm (ground.getAt [] (G1 :: Gs2) i)
            (ground.getAt ([], Pos.one) (u1 :: rest1) i).1).scale
          (prodN (cs1.take i) * (u1.2 * u1.2))).scale
          (c.2.1 * c.2.1 * (u0.2 * u0.2))
        = ((inertia.quadForm (ground.getAt [] (G1 :: Gs2) i)
              (ground.getAt ([], Pos.one) (u1 :: rest1) i).1).scale
            (c.2.1 * c.2.1 * prodN (cs1.take i) * (u0.2 * u0.2))).scale
          (u1.2 * u1.2) := by
      rw [BPair.scale_scale, BPair.scale_scale,
        posE3 (prodN (cs1.take i)) (u1.2 * u1.2) (c.2.1 * c.2.1)
          (u0.2 * u0.2)]
    exact ground.leB_congr (BPair.oneValue_of_eq eL)
      (BPair.oneValue_of_eq eR)
      (ground.leB_trans
        (ground.leB_congr_right (BPair.oneValue_of_eq mid)
          (ground.leB_scale hone
            (prodD (cs1.take i)
              * ((ground.getAt ([], Pos.one) (u1 :: rest1) i).2
                * (ground.getAt ([], Pos.one) (u1 :: rest1) i).2))))
        (ground.leB_scale hih (c.2.1 * c.2.1 * (u0.2 * u0.2))))

/-- The head block's clearings regroup at the joined blocks. -/
private theorem posRide1 (dc Dh PD b e : Pos) :
    dc * (Dh * PD) * b * e = e * (Dh * dc * (PD * b)) := by
  rw [ground.mul_comm e (Dh * dc * (PD * b)),
    ground.mul_assoc dc (Dh * PD) b,
    ground.mul_assoc Dh PD b, ground.mul_assoc Dh dc (PD * b),
    ground.mul_left_comm dc Dh (PD * b)]

/-- The trailing blocks' clearings regroup at the joined blocks. -/
private theorem posRide2 (Dh PD b a dc : Pos) :
    Dh * (PD * b) * (a * dc) = a * (Dh * dc * (PD * b)) := by
  rw [ground.mul_assoc Dh dc (PD * b), ground.mul_left_comm Dh dc (PD * b),
    ground.mul_comm a (dc * (Dh * (PD * b))),
    ground.mul_assoc dc (Dh * (PD * b)) a,
    ground.mul_comm dc (Dh * (PD * b) * a),
    ground.mul_assoc (Dh * (PD * b)) a dc]

/-- The trailing blocks' upper clearings regroup at the fold's
own. -/
private theorem posRide3 (dc PN a e : Pos) :
    PN * e * (a * dc) = dc * (PN * (a * e)) := by
  rw [ground.mul_assoc PN e (a * dc), ground.mul_left_comm e a dc,
    ground.mul_left_comm dc PN (a * e), ground.mul_left_comm dc a e,
    ground.mul_comm e dc]

/-- The head block's upper clearings regroup at the fold's own. -/
private theorem posRide4 (Nh nc PN a e : Pos) :
    nc * (Nh * PN) * a * e = Nh * (nc * (PN * (a * e))) := by
  rw [ground.mul_assoc (nc * (Nh * PN)) a e,
    ground.mul_assoc nc (Nh * PN) (a * e), ground.mul_assoc Nh PN (a * e),
    ground.mul_left_comm nc Nh (PN * (a * e))]

/-- The ride's step: the head block priced at the anchor and the
trailing blocks priced at the fold beyond it collect at the joined
fold, the head certificate's two squares the fold's own step. -/
private theorem rideStep {W0 s A F F1 : BPair}
    {e a dc nc Dh Nh PD PN b : Pos}
    (hhead : W0.scale (dc * (Dh * PD) * b) ≤ A.scale (nc * (Nh * PN) * a))
    (htail : s.scale (Dh * (PD * b)) ≤ (A * F1).scale (PN * e))
    (hF : F.oneValue (F1.scale dc + (BPair.ofPos Nh).scale nc)) :
    (W0.scale e + s.scale a).scale (Dh * dc * (PD * b))
      ≤ (A * F).scale (PN * (a * e)) := by
  have h1 : (W0.scale e).scale (Dh * dc * (PD * b))
      ≤ (A.scale (nc * (Nh * PN) * a)).scale e := by
    refine ground.leB_congr_left (BPair.oneValue_of_eq ?_)
      (ground.leB_scale hhead e)
    rw [BPair.scale_scale, BPair.scale_scale, posRide1 dc Dh PD b e]
  have h2 : (s.scale a).scale (Dh * dc * (PD * b))
      ≤ ((A * F1).scale (PN * e)).scale (a * dc) := by
    refine ground.leB_congr_left (BPair.oneValue_of_eq ?_)
      (ground.leB_scale htail (a * dc))
    rw [BPair.scale_scale, BPair.scale_scale, posRide2 Dh PD b a dc]
  have hRH : ((A.scale (nc * (Nh * PN) * a)).scale e).oneValue
      ((A * ((BPair.ofPos Nh).scale nc)).scale (PN * (a * e))) := by
    have e1 : (A * ((BPair.ofPos Nh).scale nc)).scale (PN * (a * e))
        = ((A * BPair.ofPos Nh).scale nc).scale (PN * (a * e)) := by
      rw [BPair.mul_scale]
    refine BPair.oneValue_trans ?_ (BPair.oneValue_of_eq e1.symm)
    have e2 : (A.scale (nc * (Nh * PN) * a)).scale e
        = ((A.scale Nh).scale nc).scale (PN * (a * e)) := by
      rw [BPair.scale_scale, BPair.scale_scale, BPair.scale_scale,
        posRide4 Nh nc PN a e]
    refine BPair.oneValue_trans (BPair.oneValue_of_eq e2) ?_
    refine BPair.scale_congr (PN * (a * e)) (BPair.scale_congr nc ?_)
    refine BPair.oneValue_symm ?_
    rw [BPair.mul_comm A (BPair.ofPos Nh)]
    exact BPair.ofPos_scale Nh A
  have hRT : (((A * F1).scale (PN * e)).scale (a * dc)).oneValue
      ((A * (F1.scale dc)).scale (PN * (a * e))) := by
    refine BPair.oneValue_of_eq ?_
    rw [BPair.mul_scale, BPair.scale_scale, BPair.scale_scale,
      posRide3 dc PN a e]
  have hy : ((A.scale (nc * (Nh * PN) * a)).scale e
        + ((A * F1).scale (PN * e)).scale (a * dc)).oneValue
      ((A * F).scale (PN * (a * e))) := by
    refine BPair.oneValue_trans (BPair.add_congr hRH hRT) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_comm
          ((A * ((BPair.ofPos Nh).scale nc)).scale (PN * (a * e)))
          ((A * (F1.scale dc)).scale (PN * (a * e))))) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (PN * (a * e)) (BPair.mul_congr
        (BPair.oneValue_refl A) hF)) ?_
    exact BPair.oneValue_of_eq (by
      rw [BPair.left_distrib, BPair.scale_add])
  exact ground.leB_congr
    (BPair.oneValue_of_eq (BPair.scale_add (W0.scale e) (s.scale a)
      (Dh * dc * (PD * b))).symm)
    hy (ground.leB_add h1 h2)

/-- The ride's walk: the head-side blocks' weights sum at or below
the source slab's own weight against the leading certificates'
reversed fold and the crossing certificates' product. -/
private theorem rideGo :
    ∀ (m : Nat) (Gs : List Mat) (Cs : List greenprod.MatQ)
      (cs : List ((k : Nat) × Pos × Pos × Split k))
      (us : List greenprod.VecQ) (ns : List Nat) (j : Nat),
    greenprod.gramShape Gs ns → capListDown Gs Cs cs →
    greenprod.teleDown Cs us (j + m) ns → j + m < us.length →
    (tailSum (Gs.take m) (us.take m)).1.scale
        ((tailFold (cs.take m).reverse).2
          * (prodD ((cs.drop m).take j)
            * ((ground.getAt ([], Pos.one) us (j + m)).2
              * (ground.getAt ([], Pos.one) us (j + m)).2)))
      ≤ ((inertia.quadForm (ground.getAt [] Gs (j + m))
            (ground.getAt ([], Pos.one) us (j + m)).1
          * (tailFold (cs.take m).reverse).1).scale
        (prodN ((cs.drop m).take j)
          * (tailSum (Gs.take m) (us.take m)).2)) := by
  intro m
  induction m with
  | zero =>
    intro Gs Cs cs us ns j _ _ _ _
    show BPair.unit.scale (Pos.one * (prodD (cs.take j)
        * ((ground.getAt ([], Pos.one) us j).2
          * (ground.getAt ([], Pos.one) us j).2)))
      ≤ ((inertia.quadForm (ground.getAt [] Gs j)
            (ground.getAt ([], Pos.one) us j).1
          * BPair.unit).scale (prodN (cs.take j) * Pos.one))
    exact ground.leB_congr (ground.unitScale _)
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.scale_congr (prodN (cs.take j) * Pos.one)
            (BPair.mul_unit _))
          (BPair.oneValue_symm
            (ground.unitScale (prodN (cs.take j) * Pos.one)))))
      (ground.leB_refl BPair.unit)
  | succ m' ih =>
    intro Gs Cs cs us ns j hg hc hw hjb
    cases us with
    | nil => exact absurd hjb (Nat.not_lt_zero _)
    | cons u0 rest =>
    cases Cs with
    | nil => exact (hw.2.2 : False).elim
    | cons C Cs1 =>
    cases rest with
    | nil => exact (hw.2.2 : False).elim
    | cons u1 rest1 =>
    cases cs with
    | nil => exact (hc : False).elim
    | cons c cs1 =>
    cases ns with
    | nil => exact (hw.1 : False).elim
    | cons k ns1 =>
    cases ns1 with
    | nil => exact (hw.1 : False).elim
    | cons k' ns2 =>
    cases Gs with
    | nil => exact (hg : False).elim
    | cons G0 Gs1 =>
    have hDeq : prodD (List.take (j + (m' + 1)) (c :: cs1))
        = c.2.2.1 * c.2.2.1
          * ((tailFold ((cs1.take m').reverse)).2
            * prodD ((cs1.drop m').take j)) := by
      show c.2.2.1 * c.2.2.1 * prodD (cs1.take (j + m'))
        = c.2.2.1 * c.2.2.1
          * ((tailFold ((cs1.take m').reverse)).2
            * prodD ((cs1.drop m').take j))
      rw [foldDen, prodD_rev, prodD_takeSplit m' j cs1]
    have hNeq : prodN (List.take (j + (m' + 1)) (c :: cs1))
        = c.2.1 * c.2.1
          * (prodN ((cs1.take m').reverse)
            * prodN ((cs1.drop m').take j)) := by
      show c.2.1 * c.2.1 * prodN (cs1.take (j + m'))
        = c.2.1 * c.2.1
          * (prodN ((cs1.take m').reverse)
            * prodN ((cs1.drop m').take j))
      rw [prodN_rev, prodN_takeSplit m' j cs1]
    have hchain := chainDownGo (j + (m' + 1)) (G0 :: Gs1) (C :: Cs1)
      (c :: cs1) (u0 :: u1 :: rest1) (k :: k' :: ns2) hg hc hw hjb
    rw [hDeq, hNeq] at hchain
    have htail := ih Gs1 Cs1 cs1 (u1 :: rest1) (k' :: ns2) j hg.2 hc.2
      ⟨hw.1.2, hw.2.1.2, hw.2.2.2⟩ (Nat.lt_of_succ_lt_succ hjb)
    show ((inertia.quadForm G0 u0.1).scale
          (tailSum (Gs1.take m') ((u1 :: rest1).take m')).2
        + (tailSum (Gs1.take m') ((u1 :: rest1).take m')).1.scale
            (u0.2 * u0.2)).scale
        ((tailFold ((c :: cs1.take m').reverse)).2
          * (prodD ((cs1.drop m').take j)
            * ((ground.getAt ([], Pos.one) (u1 :: rest1) (j + m')).2
              * (ground.getAt ([], Pos.one) (u1 :: rest1) (j + m')).2)))
      ≤ ((inertia.quadForm (ground.getAt [] Gs1 (j + m'))
            (ground.getAt ([], Pos.one) (u1 :: rest1) (j + m')).1
          * (tailFold ((c :: cs1.take m').reverse)).1).scale
        (prodN ((cs1.drop m').take j)
          * (u0.2 * u0.2
            * (tailSum (Gs1.take m') ((u1 :: rest1).take m')).2)))
    rw [ground.reverse_cons, (foldApp ((cs1.take m').reverse) c).2]
    exact rideStep hchain htail (foldApp ((cs1.take m').reverse) c).1

/-- The descending walk bounds its depth by the vector count, the
vacant depth split off. -/
private theorem walkBound : ∀ (i : Nat) (Cs : List greenprod.MatQ)
    (us : List greenprod.VecQ), greenprod.teleDownWalk i Cs us →
    i < us.length ∨ i = 0
  | 0, _, _, _ => Or.inr rfl
  | _ + 1, [], _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim
  | _ + 1, _ :: _, [_], h => h.elim
  | i + 1, _ :: Cs, _ :: u' :: us, h =>
    match walkBound i Cs (u' :: us) h.2 with
    | Or.inl hl => Or.inl (Nat.succ_lt_succ hl)
    | Or.inr hz => Or.inl (by
        subst hz
        exact Nat.succ_lt_succ (Nat.succ_pos _))

/-- The ride's price: at the descending certificates and the
descending telescope anchored at the source slab, the head-side
blocks' weights sum at or below the anchor's weight against the
leading certificates' fold and the crossing certificates' product,
each block's form at its own slab's gram and the joined clearings
riding the comparison. -/
theorem ride_price (Gs : List Mat) (Cs : List greenprod.MatQ)
    (cs : List ((k : Nat) × Pos × Pos × Split k))
    (us : List greenprod.VecQ) (ns : List Nat) (m j jb : Nat)
    (hg : greenprod.gramShape Gs ns)
    (hmj : m + j = jb)
    (hc : capListDown Gs Cs cs)
    (hw : greenprod.teleDown Cs us jb ns) :
    (tailSum (List.take m Gs) (List.take m us)).1.scale
        ((tailFold (List.take m cs).reverse).2
          * (prodD (List.take j (List.drop m cs))
            * ((ground.getAt ([], Pos.one) us jb).2
              * (ground.getAt ([], Pos.one) us jb).2)))
      ≤ ((inertia.quadForm (ground.getAt [] Gs jb)
            (ground.getAt ([], Pos.one) us jb).1
          * (tailFold (List.take m cs).reverse).1).scale
        ((prodN (List.take j (List.drop m cs)))
          * (tailSum (List.take m Gs) (List.take m us)).2)) := by
  have hj : j + m = jb := (Nat.add_comm j m).trans hmj
  rw [← hj] at hw ⊢
  match walkBound (j + m) Cs us hw.2.2 with
  | Or.inl hjb => exact rideGo m Gs Cs cs us ns j hg hc hw hjb
  | Or.inr hz =>
    match m, j, hz with
    | _ + 1, _, hz => nomatch hz
    | 0, _ + 1, hz => nomatch hz
    | 0, 0, _ =>
      have hq : (inertia.quadForm (ground.getAt [] Gs (0 + 0))
            (ground.getAt ([], Pos.one) us (0 + 0)).1
          * (tailFold (List.take 0 cs).reverse).1).oneValue
          BPair.unit := BPair.mul_unit _
      exact Or.inl (BPair.oneValue_trans
        (BPair.oneValue_symm (ground.unitScale _))
        (BPair.oneValue_trans (ground.unitScale _)
          (BPair.scale_congr _ (BPair.oneValue_symm hq))))

/-! The composing bracket: the two windows' full reads of a
head-supported observable within one display, `thm:groundreads`(iii)'s
conclusion sentence. -/

/-- The rescaled datum's rows read back the datum's own. -/
private theorem rowsUnscale (c : Pos) : ∀ {M : Mat} {n : Nat},
    rowsLen n (matScale c M) → rowsLen n M
  | [], _, _ => trivial
  | r :: _, _, h =>
    ⟨(ground.length_map (fun x => x.scale c) r).symm.trans h.1,
     rowsUnscale c h.2⟩

/-- The vector walk's per-index length read. -/
private theorem vShape_at : ∀ {vs : List greenprod.VecQ}
    {ns : List Nat}, greenprod.vShape vs ns → ∀ i, i < vs.length →
    (ground.getAt ([], Pos.one) vs i).1.length = ground.getAt 0 ns i
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, 0, _ => h.1
  | _ :: _, _ :: _, h, i + 1, hi =>
    vShape_at h.2 i (Nat.lt_of_succ_lt_succ hi)

/-- The vector walk restricts to any leading segment. -/
private theorem vShape_take : ∀ (m : Nat) {vs : List greenprod.VecQ}
    {ns : List Nat}, greenprod.vShape vs ns →
    greenprod.vShape (List.take m vs) (List.take m ns)
  | 0, _, _, _ => trivial
  | _ + 1, [], [], _ => trivial
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim
  | m + 1, _ :: vs, _ :: ns, h =>
    ⟨h.1, vShape_take m (vs := vs) (ns := ns) h.2⟩

/-- The vector walk restricts to any dropped tail. -/
private theorem vShape_drop : ∀ (m : Nat) {vs : List greenprod.VecQ}
    {ns : List Nat}, greenprod.vShape vs ns →
    greenprod.vShape (List.drop m vs) (List.drop m ns)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim
  | m + 1, _ :: vs, _ :: ns, h =>
    vShape_drop m (vs := vs) (ns := ns) h.2

/-- The joined family's count is the orders' total. -/
private theorem headVec_len : ∀ {vs : List greenprod.VecQ}
    {ns : List Nat}, greenprod.vShape vs ns →
    (headVec vs).length = ground.sumNat ns
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | u :: vs, k :: ns, h => by
    show (greenprod.vecScale (denProd vs) u.1
        ++ greenprod.vecScale u.2 (headVec vs)).length
      = k + ground.sumNat ns
    rw [ground.length_append,
      show (greenprod.vecScale (denProd vs) u.1).length = u.1.length
        from ground.length_map _ _,
      show (greenprod.vecScale u.2 (headVec vs)).length
        = (headVec vs).length from ground.length_map _ _,
      h.1, headVec_len h.2]

/-- The leading totals step by one key. -/
private theorem sumTake : ∀ (j : Nat) (ns : List Nat),
    j < ns.length →
    ground.sumNat (List.take (j + 1) ns)
      = ground.sumNat (List.take j ns) + ground.getAt 0 ns j
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, k :: _, _ => by
    show k + 0 = 0 + k
    rw [Nat.add_zero, Nat.zero_add]
  | j + 1, k :: ns, h => by
    show k + ground.sumNat (List.take (j + 1) ns)
      = k + ground.sumNat (List.take j ns) + ground.getAt 0 ns j
    rw [sumTake j ns (Nat.lt_of_succ_lt_succ h), Nat.add_assoc]



/-- The certificate list runs one certificate per transfer
factor. -/
private theorem capList_len (Gs : List Mat) :
    ∀ (Rs : List greenprod.MatQ)
      (cs : List ((k : Nat) × Pos × Pos × Split k)),
    capList Gs Rs cs → Rs.length = cs.length
  | [], [], _ => rfl
  | [], _ :: _, h => (h : False).elim
  | _ :: _, [], h => (h : False).elim
  | _ :: Rs, _ :: cs, h =>
    congrArg (· + 1) (capList_len (Gs.drop 1) Rs cs h.2)

/-- The unit grams at a walk of orders make a gram list at that
walk: each slab's unit gram square at its own order. -/
private theorem unitGramShape : ∀ ns : List Nat,
    greenprod.gramShape (ns.map inertia.idMat) ns
  | [] => trivial
  | k :: ns =>
    ⟨elim.sqAt_of (inertia.idMat_len k) (inertia.idMat_rows k),
     unitGramShape ns⟩


/-- The certificates' fold at an occupied list sits at or above the
product's own unit. -/
private theorem tailFold_oneLe :
    ∀ cs : List ((k : Nat) × Pos × Pos × Split k), 0 < cs.length →
    BPair.ofPos Pos.one ≤ (tailFold cs).1
  | [], h => absurd h (Nat.lt_irrefl 0)
  | c :: cs, _ => by
    show BPair.ofPos Pos.one
      ≤ ((tailFold cs).1 + BPair.ofPos (tailFold cs).2).scale
        (c.2.1 * c.2.1)
    refine ground.leB_trans
      (ground.leB_ofPos (a := Pos.one)
        (ground.posOneLe ((tailFold cs).2 * (c.2.1 * c.2.1)))) ?_
    refine ground.leB_congr_left
      (BPair.scale_ofPos (tailFold cs).2 (c.2.1 * c.2.1)) ?_
    refine ground.leB_scale ?_ (c.2.1 * c.2.1)
    exact ground.leB_congr_left (BPair.unit_add _)
      (ground.leB_add (tailFold_unitLe cs)
        (ground.leB_refl (BPair.ofPos (tailFold cs).2)))

/-- A datum at or above the sum's unit sits at or below its product
with a factor at or above the product's unit. -/
private theorem mulPadR {x y : BPair} (hx : BPair.unit ≤ x)
    (hy : BPair.ofPos Pos.one ≤ y) : x ≤ x * y :=
  ground.leB_congr_left (BPair.mul_one_read x)
    (ground.leB_mulR hx hy)

/-- Two composed rescalings read the product taken the other way. -/
private theorem scaleSwap (x : BPair) (a b : Pos) :
    (x.scale a).scale b = x.scale (b * a) := by
  rw [BPair.scale_scale, ground.mul_comm a b]

/-- The cap's two members price the magnitude at the clearing. -/
private theorem capMag {q g : BPair} {ca cda : Pos}
    (h1 : BPair.ofPos cda * q ≤ BPair.ofPos ca * g)
    (h2 : BPair.ofPos cda * q.swap ≤ BPair.ofPos ca * g) :
    (windowsep.mag q).scale cda ≤ g.scale ca :=
  ground.leB_congr (BPair.ofPos_scale cda (windowsep.mag q))
    (BPair.ofPos_scale ca g) (windowsep.mag_mul_le h1 h2)

/-- Two priced factors at or above the sum's unit price their
product, the clearings joining. -/
private theorem crossProd {q t gu gv : BPair} {ca cda ff dd : Pos}
    (hq : (windowsep.mag q).scale cda ≤ gu.scale ca)
    (ht : t.scale ff ≤ gv.scale dd)
    (hu : BPair.unit ≤ t) (hg : BPair.unit ≤ gu) :
    (windowsep.mag q * t).scale (cda * ff) ≤ (gu * gv).scale (ca * dd) := by
  have h := ground.leB_mul_mono (ground.unitLeScale ff hu)
    (ground.unitLeScale ca hg) hq ht
  rw [← BPair.scale_mul, ← BPair.scale_mul] at h
  exact h

/-- The anchored price lifts to the joined head at the leading
blocks' clearing. -/
private theorem tailBound {t uj gh f1 : BPair} {ff ee dd : Pos}
    (hp : t.scale ff ≤ (uj * f1).scale dd)
    (hb : uj.scale ee ≤ gh)
    (hf : BPair.unit ≤ f1) (hg : BPair.unit ≤ gh) :
    t.scale (ff * ee) ≤ (gh * f1).scale dd := by
  have h1 := ground.leB_scale hp ee
  rw [BPair.scale_scale, BPair.scale_scale] at h1
  refine ground.leB_trans h1 ?_
  rw [ground.mul_comm dd ee, ← BPair.scale_scale, BPair.scale_mul_left]
  exact ground.leB_scale
    (ground.leB_mul_mono hf hg hb (ground.leB_refl f1)) dd

/-- The collinearity tie passes a joined factor. -/
private theorem tieScale (x : BPair) {g gc : BPair} {s s2 : Pos}
    (h : (g.scale s).oneValue (gc.scale s2)) :
    ((x * g).scale s).oneValue ((x * gc).scale s2) :=
  BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_scale x g s).symm)
    (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl x) h)
      (BPair.oneValue_of_eq (BPair.mul_scale x gc s2)))

/-- The head term's clearings regroup at the joined blocks. -/
private theorem posL1 (a b c d : Pos) :
    a * b * (c * d) = c * (a * (b * d)) := by
  rw [ground.mul_assoc a b (c * d), ground.mul_left_comm b c d,
    ground.mul_left_comm a c (b * d)]

/-- The head term's upper clearings regroup at the joined blocks. -/
private theorem posL5 (a b c d : Pos) :
    a * b * (c * d) = b * (a * (c * d)) := by
  rw [ground.mul_assoc a b (c * d), ground.mul_left_comm a b (c * d)]

/-- The first cross term's clearings regroup at the two blocks. -/
private theorem posL2 (a x s p b : Pos) :
    a * (x * (s * (p * b))) = x * (s * (p * (a * b))) := by
  rw [ground.mul_left_comm a x (s * (p * b)),
    ground.mul_left_comm a s (p * b), ground.mul_left_comm a p b]

/-- The second cross term's clearings regroup at the two blocks. -/
private theorem posL2' (a x s p b : Pos) :
    a * (x * (s * (p * b))) = x * (s * (p * (b * a))) := by
  rw [ground.mul_left_comm a x (s * (p * b)),
    ground.mul_left_comm a s (p * b), ground.mul_left_comm a p b,
    ground.mul_comm a b]

/-- The first cross term's upper clearings regroup at the collinear
factor. -/
private theorem posL3 (ca dt dh dt' s p b : Pos) :
    ca * dt * (dh * dt' * (s * (p * b)))
      = s * (ca * (dh * (dt * dt') * (p * b))) := by
  rw [ground.mul_left_comm (dh * dt') s (p * b),
    ground.mul_left_comm (ca * dt) s (dh * dt' * (p * b)),
    ground.mul_assoc ca dt (dh * dt' * (p * b)),
    ← ground.mul_assoc dt (dh * dt') (p * b),
    ground.mul_left_comm dt dh dt']

/-- The second cross term's upper clearings regroup at the collinear
factor. -/
private theorem posL3' (ca dt' dh' dt s p b : Pos) :
    ca * dt' * (dh' * dt * (s * (p * b)))
      = s * (ca * (dh' * (dt * dt') * (p * b))) := by
  rw [ground.mul_left_comm (dh' * dt) s (p * b),
    ground.mul_left_comm (ca * dt') s (dh' * dt * (p * b)),
    ground.mul_assoc ca dt' (dh' * dt * (p * b)),
    ← ground.mul_assoc dt' (dh' * dt) (p * b),
    ground.mul_left_comm dt' dh' dt, ground.mul_comm dt' dt]

/-- The cross terms' clearings regroup at the collinear square. -/
private theorem posL4 (s2 ca u p b : Pos) :
    s2 * (ca * (u * (p * b))) = ca * (u * (s2 * (p * b))) := by
  rw [ground.mul_left_comm s2 ca (u * (p * b)),
    ground.mul_left_comm s2 u (p * b)]

/-- The three bracketed terms collect at the joined datum: the head
gap's transported price and the two cross terms, each padded to the
common datum and rescaled to the shared clearing. -/
private theorem bracketJoin {M MH Y Y' Gc Gu Gv F1 F1' : BPair}
    {S S2 P Q4 ca Dt Dt' DH DH' B1 B2 : Pos}
    (hred : M ≤ MH.scale (Dt * Dt')
      + ((Y.scale DH).scale Dt' + (Y'.scale DH').scale Dt))
    (hMH : MH.scale (S * P) ≤ (Gc * Gu).scale (S2 * Q4))
    (hY : Y.scale B1 ≤ (Gu * (Gv * F1)).scale (ca * Dt))
    (hY' : Y'.scale B2 ≤ (Gv * (Gu * F1')).scale (ca * Dt'))
    (htie : (Gv.scale S).oneValue (Gc.scale S2))
    (hGc : BPair.unit ≤ Gc) (hGu : BPair.unit ≤ Gu)
    (hF1 : BPair.ofPos Pos.one ≤ F1)
    (hF1' : BPair.ofPos Pos.one ≤ F1') :
    M.scale (S * (P * (B1 * B2)))
      ≤ (Gc * (Gu * (F1 * F1'))).scale
        (Q4 * (S2 * (Dt * Dt' * (B1 * B2)))
          + (ca * (DH * (Dt * Dt') * (S2 * (P * B2)))
            + ca * (DH' * (Dt * Dt') * (S2 * (P * B1))))) := by
  have hu1 : BPair.unit ≤ BPair.ofPos Pos.one :=
    ground.leB_of_lt (ground.unitLtOfPos Pos.one)
  have hF1u : BPair.unit ≤ F1 := ground.leB_trans hu1 hF1
  have hF1u' : BPair.unit ≤ F1' := ground.leB_trans hu1 hF1'
  have hone : BPair.ofPos Pos.one ≤ F1 * F1' :=
    ground.leB_congr_left
      (BPair.oneValue_trans (BPair.ofPos_mul Pos.one Pos.one)
        (BPair.oneValue_of_eq
          (congrArg BPair.ofPos (ground.mul_one Pos.one))))
      (ground.leB_mul_mono hu1 hF1u hF1 hF1')
  have hZH : Gc * Gu ≤ Gc * (Gu * (F1 * F1')) :=
    ground.leB_mulR hGc (mulPadR hGu hone)
  have hZB : Gu * F1 * Gc ≤ Gc * (Gu * (F1 * F1')) := by
    rw [BPair.mul_comm (Gu * F1) Gc]
    exact ground.leB_mulR hGc (ground.leB_mulR hGu (mulPadR hF1u hF1'))
  have hZC : Gu * F1' * Gc ≤ Gc * (Gu * (F1 * F1')) := by
    rw [BPair.mul_comm (Gu * F1') Gc]
    refine ground.leB_mulR hGc (ground.leB_mulR hGu ?_)
    exact ground.leB_congr_right
      (BPair.oneValue_of_eq (BPair.mul_comm F1' F1))
      (mulPadR hF1u' hF1)
  refine ground.leB_trans
    (ground.leB_scale hred (S * (P * (B1 * B2)))) ?_
  rw [BPair.scale_add, BPair.scale_add, BPair.scale_addW,
    BPair.scale_addW]
  refine ground.leB_add ?_ (ground.leB_add ?_ ?_)
  · rw [BPair.scale_scale]
    have h := ground.leB_scale hMH (Dt * Dt' * (B1 * B2))
    rw [BPair.scale_scale, BPair.scale_scale,
      posL1 S P (Dt * Dt') (B1 * B2),
      posL5 S2 Q4 (Dt * Dt') (B1 * B2)] at h
    exact ground.leB_trans h
      (ground.leB_scale hZH (Q4 * (S2 * (Dt * Dt' * (B1 * B2)))))
  · rw [BPair.scale_scale, BPair.scale_scale,
      ← ground.mul_assoc DH Dt' (S * (P * (B1 * B2)))]
    have h := ground.leB_scale hY (DH * Dt' * (S * (P * B2)))
    rw [BPair.scale_scale, BPair.scale_scale,
      posL2 B1 (DH * Dt') S P B2,
      posL3 ca Dt DH Dt' S P B2,
      ← BPair.scale_scale (Gu * (Gv * F1)) S
        (ca * (DH * (Dt * Dt') * (P * B2))),
      BPair.mul_left_comm Gu Gv F1, BPair.mul_comm Gv (Gu * F1)] at h
    refine ground.leB_trans (ground.leB_congr_right
      (BPair.scale_congr (ca * (DH * (Dt * Dt') * (P * B2)))
        (tieScale (Gu * F1) htie)) h) ?_
    rw [BPair.scale_scale, posL4 S2 ca (DH * (Dt * Dt')) P B2]
    exact ground.leB_scale hZB
      (ca * (DH * (Dt * Dt') * (S2 * (P * B2))))
  · rw [BPair.scale_scale, BPair.scale_scale,
      ← ground.mul_assoc DH' Dt (S * (P * (B1 * B2)))]
    have h := ground.leB_scale hY' (DH' * Dt * (S * (P * B1)))
    rw [BPair.scale_scale, BPair.scale_scale,
      posL2' B2 (DH' * Dt) S P B1,
      posL3' ca Dt' DH' Dt S P B1,
      ← BPair.scale_scale (Gv * (Gu * F1')) S
        (ca * (DH' * (Dt * Dt') * (P * B1))),
      BPair.mul_comm Gv (Gu * F1')] at h
    refine ground.leB_trans (ground.leB_congr_right
      (BPair.scale_congr (ca * (DH' * (Dt * Dt') * (P * B1)))
        (tieScale (Gu * F1') htie)) h) ?_
    rw [BPair.scale_scale, posL4 S2 ca (DH' * (Dt * Dt')) P B1]
    exact ground.leB_scale hZC
      (ca * (DH' * (Dt * Dt') * (S2 * (P * B1))))

/-- A ground read of a supported observable is window-free within
one named bracket, geometric in the certificates' fold: the two
grounds' full reads of a head-supported observable sit within one
display whose head term is priced by the transport display and whose
two cross terms are priced by the head cap and the tail prices. -/
theorem window_free {o : Nat} (diag off diag' off' : List Mat)
    (Xs Rs Xs' Rs' : List greenprod.MatQ) (w0 j : Nat) (ns : List Nat)
    (dn : BPair) (cn cd sn sd : Pos)
    (certs : List ((p : Nat × Nat) × (Pos × Pos) × (Pos × Pos)
      × Split p.2 × Split p.2 × Split p.1 × Split p.1
      × Split p.2 × Split p.2 × Split p.2 × Split p.2))
    (hshare : spectator.driftShareRead diag off diag' off' Xs Rs Xs' Rs'
      w0 j ns dn cn cd sn sd
      ((((ns.take (w0 + 1)).drop j).reverse).map inertia.idMat) certs)
    (hocc : 0 < certs.length) (hjw : j < w0)
    (X X' : greenprod.MatQ)
    (hX : X = ground.getAt greenprod.dM Xs j)
    (hX' : X' = ground.getAt greenprod.dM Xs' j)
    (ho : ground.getAt 0 ns j = o)
    (k n : Nat)
    (hk : k = ground.sumNat (List.take j ns))
    (hn : n = k + o)
    (T Tw : SqMat n) (l : List (BPair × Pos × BPair))
    (hd : split.diagRead (matScale X'.2 (greenprod.headM diag off X j))
      (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : clearRead l j0 gn gd)
    (wrn wrd : Pos) (spD spD' : Split n)
    (hdrift : capAt
      (matScale wrd (matScaleB (dn.scale (X.2 * X'.2))
        (inertia.headId k o)))
      (matScale wrn (idMat n)) spD spD')
    (spP spP' : Split n)
    (hUP : splitRead (siteDatum
      (matScale ((spectator.driftFold cn cd sn sd certs).1
        * (X'.2 * X.2)) (idMat n))
      (matScale (spectator.driftFold cn cd sn sd certs).2
        (inertia.trailPad k
          (greenprod.addQ X' (greenprod.swapQ X)).1))) spP)
    (hLP : splitRead (matAdd
      (matScale ((spectator.driftFold cn cd sn sd certs).1
        * (X'.2 * X.2)) (idMat n))
      (matScale (spectator.driftFold cn cd sn sd certs).2
        (inertia.trailPad k
          (greenprod.addQ X' (greenprod.swapQ X)).1))) spP')
    (spF spF' : Split n)
    (hUF : splitRead (siteDatum
      (matScale (wrd * ((spectator.driftFold cn cd sn sd certs).1
          * (X'.2 * X.2))
        + (spectator.driftFold cn cd sn sd certs).2 * wrn) (idMat n))
      (matScale (wrd * (spectator.driftFold cn cd sn sd certs).2)
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2)) (inertia.headId k o))
          (inertia.trailPad k
            (greenprod.addQ X' (greenprod.swapQ X)).1)))) spF)
    (hLF : splitRead (matAdd
      (matScale (wrd * ((spectator.driftFold cn cd sn sd certs).1
          * (X'.2 * X.2))
        + (spectator.driftFold cn cd sn sd certs).2 * wrn) (idMat n))
      (matScale (wrd * (spectator.driftFold cn cd sn sd certs).2)
        (matAdd
          (matScaleB (dn.scale (X.2 * X'.2)) (inertia.headId k o))
          (inertia.trailPad k
            (greenprod.addQ X' (greenprod.swapQ X)).1)))) spF')
    (A : Mat) (cA cdA : Pos) (spA spA' : Split n)
    (hA : capAt (matScale cdA A) (matScale cA (idMat n)) spA spA')
    (us ws us' ws' : List greenprod.VecQ)
    (hs1 : greenprod.solveRead diag off us ws ns)
    (hw1 : greenprod.sidesUnit ws)
    (hs2 : greenprod.solveRead diag' off' us' ws' ns)
    (hw2 : greenprod.sidesUnit ws')
    (s1 s2 : Pos)
    (hcol : poly.oneValue
      (greenprod.vecScale s1 (headVec (List.take (j + 1) us)))
      (greenprod.vecScale s2 (matVec T.val (elim.idRow n j0))))
    (cs cs' : List ((k : Nat) × Pos × Pos × Split k))
    (hcap1 : capList (ns.map inertia.idMat) Rs cs)
    (hcap2 : capList (ns.map inertia.idMat) Rs' cs')
 :
    (windowsep.mag (readGap
        (inertia.quadForm
          (inertia.headPad (ground.sumNat (List.drop (j + 1) ns)) A)
          (headVec us),
         dotN (headVec us) (headVec us))
        (inertia.quadForm
          (inertia.headPad (ground.sumNat (List.drop (j + 1) ns)) A)
          (headVec us'),
         dotN (headVec us') (headVec us')))).scale
      ((s1 * s1)
        * ((gn * (wrd * (spectator.driftFold cn cd sn sd certs).2)
            * cdA)
          * (((cdA * ((tailFold (List.drop j cs)).2
                * ((ground.getAt ([], Pos.one) us j).2
                  * (ground.getAt ([], Pos.one) us j).2)))
              * (denProd (List.take j us) * denProd (List.take j us)))
            * ((cdA * ((tailFold (List.drop j cs')).2
                * ((ground.getAt ([], Pos.one) us' j).2
                  * (ground.getAt ([], Pos.one) us' j).2)))
              * (denProd (List.take j us')
                * denProd (List.take j us'))))))
      ≤ (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * (dotN (headVec (List.take (j + 1) us'))
              (headVec (List.take (j + 1) us'))
            * ((tailFold (List.drop j cs)).1
              * (tailFold (List.drop j cs')).1))).scale
        ((4 * (cA * (wrd * ((spectator.driftFold cn cd sn sd certs).1
              * (X'.2 * X.2))
            + (spectator.driftFold cn cd sn sd certs).2 * wrn) * gd))
          * ((s2 * s2)
            * (((denProd (List.drop (j + 1) us)
                  * denProd (List.drop (j + 1) us))
                * (denProd (List.drop (j + 1) us')
                  * denProd (List.drop (j + 1) us')))
              * (((cdA * ((tailFold (List.drop j cs)).2
                    * ((ground.getAt ([], Pos.one) us j).2
                      * (ground.getAt ([], Pos.one) us j).2)))
                  * (denProd (List.take j us)
                    * denProd (List.take j us)))
                * ((cdA * ((tailFold (List.drop j cs')).2
                    * ((ground.getAt ([], Pos.one) us' j).2
                      * (ground.getAt ([], Pos.one) us' j).2)))
                  * (denProd (List.take j us')
                    * denProd (List.take j us'))))))
          + (cA * (((denProd (List.take (j + 1) us)
                  * denProd (List.take (j + 1) us))
                * ((denProd (List.drop (j + 1) us)
                    * denProd (List.drop (j + 1) us))
                  * (denProd (List.drop (j + 1) us')
                    * denProd (List.drop (j + 1) us'))))
              * ((s2 * s2)
                * ((gn * (wrd
                      * (spectator.driftFold cn cd sn sd certs).2)
                    * cdA)
                  * ((cdA * ((tailFold (List.drop j cs')).2
                      * ((ground.getAt ([], Pos.one) us' j).2
                        * (ground.getAt ([], Pos.one) us' j).2)))
                    * (denProd (List.take j us')
                      * denProd (List.take j us'))))))
            + cA * (((denProd (List.take (j + 1) us')
                  * denProd (List.take (j + 1) us'))
                * ((denProd (List.drop (j + 1) us)
                    * denProd (List.drop (j + 1) us))
                  * (denProd (List.drop (j + 1) us')
                    * denProd (List.drop (j + 1) us'))))
              * ((s2 * s2)
                * ((gn * (wrd
                      * (spectator.driftFold cn cd sn sd certs).2)
                    * cdA)
                  * ((cdA * ((tailFold (List.drop j cs)).2
                      * ((ground.getAt ([], Pos.one) us j).2
                        * (ground.getAt ([], Pos.one) us j).2)))
                    * (denProd (List.take j us)
                      * denProd (List.take j us)))))))) := by
  have hjRs : j < Rs.length := by
    have ho2 := (walkOcc hshare.2.2.2.2.2 hocc).1
    rw [ground.length_reverse] at ho2
    exact takeDropOcc w0 j Rs ho2
  have hjn : j < ns.length := by
    rw [← greenprod.wShapeR_len hshare.1.2.2.1]
    exact Nat.lt_succ_of_lt hjRs

  have ht1 := hshare.1
  have ht2 := hshare.2.1
  have hvs1 := hs1.2.1
  have hvs2 := hs2.2.1
  have hv1 : greenprod.vShape (List.drop (j + 1) us)
      (List.drop (j + 1) ns) := vShape_drop (j + 1) hvs1
  have hv2 : greenprod.vShape (List.drop (j + 1) us')
      (List.drop (j + 1) ns) := vShape_drop (j + 1) hvs2
  have hjus : j < us.length := by
    rw [greenprod.vShape_len hvs1]
    exact hjn
  have hjus2 : j < us'.length := by
    rw [greenprod.vShape_len hvs2]
    exact hjn
  obtain ⟨hw1r, hv1r, hwk1⟩ :=
    kernel_tele diag off Xs Rs ns us ws ht1 hs1 hw1
  obtain ⟨hw2r, hv2r, hwk2⟩ :=
    kernel_tele diag' off' Xs' Rs' ns us' ws' ht2 hs2 hw2
  have hjR : j ≤ Rs.length := by
    have hlt : j < Rs.length + 1 := by
      rw [greenprod.wShapeR_len hw1r]
      exact hjn
    exact Nat.le_of_succ_le_succ hlt
  have hjR' : j ≤ Rs'.length := by
    have hlt : j < Rs'.length + 1 := by
      rw [greenprod.wShapeR_len hw2r]
      exact hjn
    exact Nat.le_of_succ_le_succ hlt
  have htel1 : greenprod.teleUp Rs us j ns :=
    ⟨hw1r, hv1r, greenprod.teleUpWalk_anchor j Rs us hwk1 hjus hjR⟩
  have htel2 : greenprod.teleUp Rs' us' j ns :=
    ⟨hw2r, hv2r, greenprod.teleUpWalk_anchor j Rs' us' hwk2 hjus2 hjR'⟩
  have hwo := walkOcc hshare.2.2.2.2.2 hocc
  have hoc1 : 0 < (List.drop j cs).length := by
    refine dropPos j cs ?_
    rw [← capList_len (ns.map inertia.idMat) Rs cs hcap1]
    refine takeDropOcc w0 j Rs ?_
    rw [← ground.length_reverse]
    exact hwo.1
  have hoc2 : 0 < (List.drop j cs').length := by
    refine dropPos j cs' ?_
    rw [← capList_len (ns.map inertia.idMat) Rs' cs' hcap2]
    refine takeDropOcc w0 j Rs' ?_
    rw [← ground.length_reverse]
    exact hwo.2
  have hpt : (headVec (List.take (j + 1) us)).length = n := by
    rw [hn, hk, ← ho]
    exact (headVec_len (vShape_take (j + 1) hvs1)).trans (sumTake j ns hjn)
  have hpt' : (headVec (List.take (j + 1) us')).length = n := by
    rw [hn, hk, ← ho]
    exact (headVec_len (vShape_take (j + 1) hvs2)).trans (sumTake j ns hjn)
  have hcpA := truncation.cap_read A cA cdA spA spA' hA
    (headVec (List.take (j + 1) us)) hpt
  have hcpA' := truncation.cap_read A cA cdA spA spA' hA
    (headVec (List.take (j + 1) us')) hpt'
  have hmagQ := capMag hcpA.1 hcpA.2
  have hmagQ' := capMag hcpA'.1 hcpA'.2
  have hgram1 : (dotN (headVec us) (headVec us)).oneValue
      ((dotN (headVec (List.take (j + 1) us))
          (headVec (List.take (j + 1) us))).scale
          (denProd (List.drop (j + 1) us)
            * denProd (List.drop (j + 1) us))
        + (dotN (headVec (List.drop (j + 1) us))
            (headVec (List.drop (j + 1) us))).scale
          (denProd (List.take (j + 1) us)
            * denProd (List.take (j + 1) us))) :=
    BPair.oneValue_trans
      (BPair.oneValue_trans
        (dotN_congrL _ _ _ (headVec_split (j + 1) us))
        (dotN_congrR _ _ _ (headVec_split (j + 1) us)))
      (BPair.oneValue_trans (dotN_app _ _ _ _ rfl)
        (BPair.add_congr (gvsSelf _ _) (gvsSelf _ _)))
  have hgram2 : (dotN (headVec us') (headVec us')).oneValue
      ((dotN (headVec (List.take (j + 1) us'))
          (headVec (List.take (j + 1) us'))).scale
          (denProd (List.drop (j + 1) us')
            * denProd (List.drop (j + 1) us'))
        + (dotN (headVec (List.drop (j + 1) us'))
            (headVec (List.drop (j + 1) us'))).scale
          (denProd (List.take (j + 1) us')
            * denProd (List.take (j + 1) us'))) :=
    BPair.oneValue_trans
      (BPair.oneValue_trans
        (dotN_congrL _ _ _ (headVec_split (j + 1) us'))
        (dotN_congrR _ _ _ (headVec_split (j + 1) us')))
      (BPair.oneValue_trans (dotN_app _ _ _ _ rfl)
        (BPair.add_congr (gvsSelf _ _) (gvsSelf _ _)))
  have hsqA : sqAt A n :=
    elim.sqAt_of
      ((length_matScale cdA A).symm.trans (elim.sqAt_len hA.1))
      (rowsUnscale cdA (rowsLen_of_sqAt hA.1))
  have hobs1 : (inertia.quadForm
      (inertia.headPad (ground.sumNat (List.drop (j + 1) ns)) A)
      (headVec us)).oneValue
      ((inertia.quadForm A (headVec (List.take (j + 1) us))).scale
        (denProd (List.drop (j + 1) us)
          * denProd (List.drop (j + 1) us))) := by
    refine BPair.oneValue_trans
      (inertia.quadForm_congr _ (headVec_split (j + 1) us)) ?_
    refine BPair.oneValue_trans
      (inertia.quadForm_headPad _ A (rowsLen_of_sqAt hsqA)
        (elim.sqAt_len hsqA) _ _
        ((ground.length_map _ _).trans hpt)) ?_
    refine BPair.oneValue_trans
      (inertia.quadScaleVec A
        (BPair.ofPos (denProd (List.drop (j + 1) us))) _ _
        (greenprod.vecScale_ofPos _ _)) ?_
    exact sqScale _ _
  have hobs2 : (inertia.quadForm
      (inertia.headPad (ground.sumNat (List.drop (j + 1) ns)) A)
      (headVec us')).oneValue
      ((inertia.quadForm A (headVec (List.take (j + 1) us'))).scale
        (denProd (List.drop (j + 1) us')
          * denProd (List.drop (j + 1) us'))) := by
    refine BPair.oneValue_trans
      (inertia.quadForm_congr _ (headVec_split (j + 1) us')) ?_
    refine BPair.oneValue_trans
      (inertia.quadForm_headPad _ A (rowsLen_of_sqAt hsqA)
        (elim.sqAt_len hsqA) _ _
        ((ground.length_map _ _).trans hpt')) ?_
    refine BPair.oneValue_trans
      (inertia.quadScaleVec A
        (BPair.ofPos (denProd (List.drop (j + 1) us'))) _ _
        (greenprod.vecScale_ofPos _ _)) ?_
    exact sqScale _ _
  have hpr1 := tail_price (ns.map inertia.idMat) Rs cs us ns j
    (unitGramShape ns) hcap1 htel1
  rw [ground.map_drop inertia.idMat ns (j + 1),
    tailSum_den ((List.drop (j + 1) ns).map inertia.idMat)
      (us.drop (j + 1))] at hpr1
  have hpr2 := tail_price (ns.map inertia.idMat) Rs' cs' us' ns j
    (unitGramShape ns) hcap2 htel2
  rw [ground.map_drop inertia.idMat ns (j + 1),
    tailSum_den ((List.drop (j + 1) ns).map inertia.idMat)
      (us'.drop (j + 1))] at hpr2
  have hgj : ground.getAt ([] : Mat) (ns.map inertia.idMat) j
      = inertia.idMat o := by
    rw [ground.getAt_map 0 ([] : Mat) inertia.idMat ns j hjn, ho]
  have hq1 : (inertia.quadForm
        (ground.getAt ([] : Mat) (ns.map inertia.idMat) j)
        (ground.getAt ([], Pos.one) us j).1).oneValue
      (dotN (ground.getAt ([], Pos.one) us j).1
        (ground.getAt ([], Pos.one) us j).1) := by
    rw [hgj]
    exact dotN_congrR _ _ _
      (inertia.matVec_idMat o _ ((vShape_at hvs1 j hjus).trans ho))
  have hq2 : (inertia.quadForm
        (ground.getAt ([] : Mat) (ns.map inertia.idMat) j)
        (ground.getAt ([], Pos.one) us' j).1).oneValue
      (dotN (ground.getAt ([], Pos.one) us' j).1
        (ground.getAt ([], Pos.one) us' j).1) := by
    rw [hgj]
    exact dotN_congrR _ _ _
      (inertia.matVec_idMat o _ ((vShape_at hvs2 j hjus2).trans ho))
  have hpx1 := ground.leB_congr_left
    (BPair.scale_congr _ (BPair.oneValue_symm
      (headVec_weight (List.drop (j + 1) us) (List.drop (j + 1) ns)
        hv1)))
    (ground.leB_congr_right
      (BPair.scale_congr _
        (BPair.mul_congr hq1 (BPair.oneValue_refl _))) hpr1)
  have hpx2 := ground.leB_congr_left
    (BPair.scale_congr _ (BPair.oneValue_symm
      (headVec_weight (List.drop (j + 1) us') (List.drop (j + 1) ns)
        hv2)))
    (ground.leB_congr_right
      (BPair.scale_congr _
        (BPair.mul_congr hq2 (BPair.oneValue_refl _))) hpr2)
  have htl1 := tailBound hpx1 (blockWeight_le j us hjus)
    (tailFold_unitLe _) (ground.leB_of_not_lt (dotN_self_side _))
  have htl2 := tailBound hpx2 (blockWeight_le j us' hjus2)
    (tailFold_unitLe _) (ground.leB_of_not_lt (dotN_self_side _))
  have hY1 := crossProd hmagQ' htl1
    (ground.leB_of_not_lt (dotN_self_side _))
    (ground.leB_of_not_lt (dotN_self_side _))
  have hY2 := crossProd hmagQ htl2
    (ground.leB_of_not_lt (dotN_self_side _))
    (ground.leB_of_not_lt (dotN_self_side _))
  rw [← ground.mul_assoc cdA] at hY1
  rw [← ground.mul_assoc cdA] at hY2
  have hY0 : (windowsep.mag (inertia.quadForm A
        (headVec (List.take (j + 1) us'))
      * (dotN (headVec (List.drop (j + 1) us))
          (headVec (List.drop (j + 1) us))).scale
        (denProd (List.take (j + 1) us)
          * denProd (List.take (j + 1) us)))).oneValue
      ((windowsep.mag (inertia.quadForm A
          (headVec (List.take (j + 1) us')))
        * dotN (headVec (List.drop (j + 1) us))
            (headVec (List.drop (j + 1) us))).scale
        (denProd (List.take (j + 1) us)
          * denProd (List.take (j + 1) us))) := by
    refine BPair.oneValue_trans (windowsep.mag_mul _ _) ?_
    rw [windowsep.mag_scale,
      windowsep.mag_unitLe (ground.leB_of_not_lt (dotN_self_side _)),
      BPair.mul_scale]
    exact BPair.oneValue_refl _
  have hY0' : (windowsep.mag (inertia.quadForm A
        (headVec (List.take (j + 1) us))
      * (dotN (headVec (List.drop (j + 1) us'))
          (headVec (List.drop (j + 1) us'))).scale
        (denProd (List.take (j + 1) us')
          * denProd (List.take (j + 1) us')))).oneValue
      ((windowsep.mag (inertia.quadForm A
          (headVec (List.take (j + 1) us)))
        * dotN (headVec (List.drop (j + 1) us'))
            (headVec (List.drop (j + 1) us'))).scale
        (denProd (List.take (j + 1) us')
          * denProd (List.take (j + 1) us'))) := by
    refine BPair.oneValue_trans (windowsep.mag_mul _ _) ?_
    rw [windowsep.mag_scale,
      windowsep.mag_unitLe (ground.leB_of_not_lt (dotN_self_side _)),
      BPair.mul_scale]
    exact BPair.oneValue_refl _
  have hext := readGap_extend
    (inertia.quadForm A (headVec (List.take (j + 1) us)))
    (dotN (headVec (List.take (j + 1) us))
      (headVec (List.take (j + 1) us)))
    (inertia.quadForm A (headVec (List.take (j + 1) us')))
    (dotN (headVec (List.take (j + 1) us'))
      (headVec (List.take (j + 1) us')))
    ((dotN (headVec (List.drop (j + 1) us))
        (headVec (List.drop (j + 1) us))).scale
      (denProd (List.take (j + 1) us)
        * denProd (List.take (j + 1) us)))
    ((dotN (headVec (List.drop (j + 1) us'))
        (headVec (List.drop (j + 1) us'))).scale
      (denProd (List.take (j + 1) us')
        * denProd (List.take (j + 1) us')))
    (denProd (List.drop (j + 1) us) * denProd (List.drop (j + 1) us))
    (denProd (List.drop (j + 1) us') * denProd (List.drop (j + 1) us'))
  have hred := ground.leB_congr_right
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.scale_congr _ hY0)
        (BPair.scale_congr _ hY0')))
    (ground.leB_congr_left
      (BPair.oneValue_symm (windowsep.mag_congr
        (readGap_congr hobs1 hgram1 hobs2 hgram2)))
      hext)
  have hQtie : ((inertia.quadForm A
        (headVec (List.take (j + 1) us))).scale (s1 * s1)).oneValue
      ((inertia.quadForm A (matVec T.val (elim.idRow n j0))).scale
        (s2 * s2)) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (inertia.quadScaleVec A (BPair.ofPos s1) _ _
            (greenprod.vecScale_ofPos s1 _))
          (sqScale s1 _)))
      (BPair.oneValue_trans (inertia.quadForm_congr A hcol)
        (BPair.oneValue_trans
          (inertia.quadScaleVec A (BPair.ofPos s2) _ _
            (greenprod.vecScale_ofPos s2 _))
          (sqScale s2 _)))
  have hGtie : ((dotN (headVec (List.take (j + 1) us))
        (headVec (List.take (j + 1) us))).scale (s1 * s1)).oneValue
      ((dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0))).scale (s2 * s2)) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (gvsSelf s1 _))
      (BPair.oneValue_trans
        (BPair.oneValue_trans (dotN_congrL _ _ _ hcol)
          (dotN_congrR _ _ _ hcol))
        (gvsSelf s2 _))
  have hker0 := head_kernel diag' off' Xs' Rs' us' ws' ns j ht2 hs2 hw2
    hjus2
  have hker : poly.unitTail (matVec
      (matScale X.2 (greenprod.headM diag' off' X' j))
      (headVec (List.take (j + 1) us'))) := by
    rw [hX, hX']
    exact poly.oneValue_unitTail (inertia.matVec_matScale _ _ _)
      (elim.unitTail_vecScale _ _ hker0)
  have hWT := window_transport diag off diag' off' Xs Rs Xs' Rs' w0 j ns
    dn cn cd sn sd certs hshare hocc hjw X X' hX hX' ho
    k n hk hn T Tw l hd j0 hj0 d0 g0 hroot0 gn gd hcl wrn wrd spD spD'
    hdrift spP spP' hUP hLP spF spF' hUF hLF A cA cdA spA spA' hA
    (headVec (List.take (j + 1) us')) hpt' hker
  have hWT' : (windowsep.mag (readGap
        (inertia.quadForm A (matVec T.val (elim.idRow n j0)),
         dotN (matVec T.val (elim.idRow n j0))
           (matVec T.val (elim.idRow n j0)))
        (inertia.quadForm A (headVec (List.take (j + 1) us')),
         dotN (headVec (List.take (j + 1) us'))
           (headVec (List.take (j + 1) us'))))).scale
      (gn * (wrd * (spectator.driftFold cn cd sn sd certs).2) * cdA)
      ≤ (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (headVec (List.take (j + 1) us'))
            (headVec (List.take (j + 1) us'))).scale
        (4 * (cA * (wrd * ((spectator.driftFold cn cd sn sd certs).1
            * (X'.2 * X.2))
          + (spectator.driftFold cn cd sn sd certs).2 * wrn) * gd)) :=
    hWT
  have hmagTie : ((windowsep.mag (readGap
        (inertia.quadForm A (headVec (List.take (j + 1) us)),
         dotN (headVec (List.take (j + 1) us))
           (headVec (List.take (j + 1) us)))
        (inertia.quadForm A (headVec (List.take (j + 1) us')),
         dotN (headVec (List.take (j + 1) us'))
           (headVec (List.take (j + 1) us'))))).scale
        (s1 * s1)).oneValue
      ((windowsep.mag (readGap
        (inertia.quadForm A (matVec T.val (elim.idRow n j0)),
         dotN (matVec T.val (elim.idRow n j0))
           (matVec T.val (elim.idRow n j0)))
        (inertia.quadForm A (headVec (List.take (j + 1) us')),
         dotN (headVec (List.take (j + 1) us'))
           (headVec (List.take (j + 1) us'))))).scale (s2 * s2)) := by
    rw [← windowsep.mag_scale, ← windowsep.mag_scale]
    refine windowsep.mag_congr ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (readGap_scaleL (s1 * s1) _ _ _))
      (BPair.oneValue_trans
        (readGap_congr hQtie hGtie (BPair.oneValue_refl _)
          (BPair.oneValue_refl _))
        (readGap_scaleL (s2 * s2) _ _ _))
  have hMH : (windowsep.mag (readGap
        (inertia.quadForm A (headVec (List.take (j + 1) us)),
         dotN (headVec (List.take (j + 1) us))
           (headVec (List.take (j + 1) us)))
        (inertia.quadForm A (headVec (List.take (j + 1) us')),
         dotN (headVec (List.take (j + 1) us'))
           (headVec (List.take (j + 1) us'))))).scale
      ((s1 * s1)
        * (gn * (wrd * (spectator.driftFold cn cd sn sd certs).2) * cdA))
      ≤ (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (headVec (List.take (j + 1) us'))
            (headVec (List.take (j + 1) us'))).scale
        ((s2 * s2)
          * (4 * (cA * (wrd * ((spectator.driftFold cn cd sn sd certs).1
              * (X'.2 * X.2))
            + (spectator.driftFold cn cd sn sd certs).2 * wrn) * gd))) := by
    have h := ground.leB_scale hWT' (s2 * s2)
    rw [scaleSwap, scaleSwap] at h
    refine ground.leB_congr_left ?_ h
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.scale_scale _ (s2 * s2)
          (gn * (wrd * (spectator.driftFold cn cd sn sd certs).2)
            * cdA)).symm)
      (BPair.oneValue_trans
        (BPair.scale_congr _ (BPair.oneValue_symm hmagTie))
        (BPair.oneValue_of_eq
          (BPair.scale_scale _ (s1 * s1)
            (gn * (wrd * (spectator.driftFold cn cd sn sd certs).2)
              * cdA))))
  exact bracketJoin hred hMH hY1 hY2 hGtie
    (ground.leB_of_not_lt (dotN_self_side _))
    (ground.leB_of_not_lt (dotN_self_side _))
    (tailFold_oneLe (List.drop j cs) hoc1)
    (tailFold_oneLe (List.drop j cs') hoc2)

/-! Clause (iv): the separated reads cluster — the connected read
is one pairing of two off-line vectors. -/

/-- The rearrangement at the gram-symmetric multiplications: the
joint read's cofactor against the squared self-pairing is the two
reads' product at the self-pairing joined to the connected pairing,
the two probes' residuals off the ground line. -/
theorem connected_split (A B : Mat) (psi : List BPair) (n : Nat)
    (hAr : rowsLen n A) (hAl : A.length = n)
    (hsym : matOneValue (transposeM A) A)
    (hBl : B.length = n) (hp : psi.length = n) :
    (dotN psi (matVec A (matVec B psi))
        * (dotN psi psi * dotN psi psi)).oneValue
      (inertia.quadForm A psi * inertia.quadForm B psi * dotN psi psi
        + dotN (residD [psi] (matVec A psi))
            (residD [psi] (matVec B psi))) := by
  have hAv : (matVec A psi).length = n :=
    (ground.length_map _ _).trans hAl
  have hBv : (matVec B psi).length = n :=
    (ground.length_map _ _).trans hBl
  have hflip : (dotN (matVec A psi) (matVec B psi)).oneValue
      (dotN psi (matVec A (matVec B psi))) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    rw [dotP_comm (matVec A psi) (matVec B psi)]
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (dotN_read (matVec B psi) (matVec A psi)))
      ?_
    exact dotN_sym_flip A n hAr hAl hsym psi (matVec B psi) hp hBv
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (offLine_cross psi (matVec A psi) (matVec B psi) n hp hAv hBv))
    ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.add_congr
          (BPair.mul_congr (BPair.oneValue_refl _) hflip)
          (BPair.oneValue_refl _)))) ?_
  rw [BPair.left_distrib (dotN psi psi)
      (dotN psi psi * dotN psi (matVec A (matVec B psi)))
      ((dotN psi (matVec A psi) * dotN psi (matVec B psi)).swap),
    BPair.mul_swap (dotN psi psi)
      (dotN psi (matVec A psi) * dotN psi (matVec B psi)),
    BPair.add_comm
      (dotN psi psi
        * (dotN psi psi * dotN psi (matVec A (matVec B psi))))
      ((dotN psi psi
        * (dotN psi (matVec A psi) * dotN psi (matVec B psi))).swap),
    ← BPair.add_assoc,
    show inertia.quadForm A psi * inertia.quadForm B psi * dotN psi psi
        = dotN psi psi
          * (dotN psi (matVec A psi) * dotN psi (matVec B psi)) from
      BPair.mul_comm _ _]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.swap_add_null (BPair.oneValue_refl _)))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.add_unit _)) ?_
  rw [← BPair.mul_assoc (dotN psi psi) (dotN psi psi)
      (dotN psi (matVec A (matVec B psi)))]
  exact BPair.oneValue_of_eq (BPair.mul_comm _ _)

/-! Clause (iv): the sourced pencil at the level gap's tie. -/

/-- The level gap's action at the tie: the electric diagonal's read
at the gap's weight, the magnetic member's and the cleared floor's
at the memberwise swap. -/
private theorem tieRead (dg : List Nat) (M Et : Mat) (x : List BPair)
    (n : Nat) (sn sd ed : Pos) (en : BPair)
    (hdg : dg.length = n) (hMr : rowsLen n M) (hMl : M.length = n)
    (hx : x.length = n)
    (hEt : matOneValue Et (matAdd (matAdd
        (inertia.matScale (ed * sn)
          (diagO ground.bpairOps (dg.map BPair.ofNat)))
        (matSwap (inertia.matScale (ed * sd) M)))
        (matSwap (inertia.matScaleB en (inertia.idMat n))))) :
    poly.oneValue (matVec Et x)
      (vecAdd (vecAdd
          (vecScale (BPair.ofPos (ed * sn))
            (matVec (diagO ground.bpairOps (dg.map BPair.ofNat)) x))
          ((vecScale (BPair.ofPos (ed * sd)) (matVec M x)).map BPair.swap))
        ((vecScale en x).map BPair.swap)) := by
  have hml : (dg.map BPair.ofNat).length = n :=
    (ground.length_map _ dg).trans hdg
  have hDl : (diagO ground.bpairOps (dg.map BPair.ofNat)).length = n :=
    (diagO_len ground.bpairOps _).trans hml
  have hDr : rowsLen n (diagO ground.bpairOps (dg.map BPair.ofNat)) :=
    rowsLen_cast hml (diagO_rows ground.bpairOps _)
  have lS1 : (inertia.matScale (ed * sn)
      (diagO ground.bpairOps (dg.map BPair.ofNat))).length = n :=
    (inertia.length_matScale _ _).trans hDl
  have lS2 : (matSwap (inertia.matScale (ed * sd) M)).length = n :=
    (length_matSwap _).trans ((inertia.length_matScale _ _).trans hMl)
  have lP : (matAdd
      (inertia.matScale (ed * sn)
        (diagO ground.bpairOps (dg.map BPair.ofNat)))
      (matSwap (inertia.matScale (ed * sd) M))).length = n :=
    (length_matAdd _ _ (lS1.trans lS2.symm)).trans lS1
  have hS1 : rowsLen n (inertia.matScale (ed * sn)
      (diagO ground.bpairOps (dg.map BPair.ofNat))) :=
    rowsLen_mapRows (fun z => z.scale (ed * sn)) _ n hDr
  have hS2 : rowsLen n (matSwap (inertia.matScale (ed * sd) M)) :=
    rowsLen_mapRows BPair.swap _ n
      (rowsLen_mapRows (fun z => z.scale (ed * sd)) M n hMr)
  have hS3 : rowsLen n (matSwap (inertia.matScaleB en (inertia.idMat n))) :=
    rowsLen_mapRows BPair.swap _ n
      (inertia.rowsLen_scaleB en n (inertia.idMat n) (inertia.idMat_rows n))
  have q1 : poly.oneValue
      (matVec (inertia.matScale (ed * sn)
        (diagO ground.bpairOps (dg.map BPair.ofNat))) x)
      (vecScale (BPair.ofPos (ed * sn))
        (matVec (diagO ground.bpairOps (dg.map BPair.ofNat)) x)) :=
    inertia.matVec_matScale _ _ x
  have q2 : poly.oneValue (matVec (matSwap (inertia.matScale (ed * sd) M)) x)
      ((vecScale (BPair.ofPos (ed * sd)) (matVec M x)).map BPair.swap) := by
    rw [matVec_swapM]
    exact poly.swapMap_oneValue (inertia.matVec_matScale _ M x)
  have q3 : poly.oneValue
      (matVec (matSwap (inertia.matScaleB en (inertia.idMat n))) x)
      ((vecScale en x).map BPair.swap) := by
    rw [matVec_swapM]
    exact poly.swapMap_oneValue (inertia.scaleId_act en n x hx)
  refine poly.oneValue_trans (matVec_matOne _ _ x hEt) ?_
  refine poly.oneValue_trans
    (matVec_add_free n _ _ x (rowsLen_matAdd n _ _ hS1 hS2) hS3) ?_
  refine elim.vecAdd_congr2 _ _ _ _
    (by rw [matVec_length, lP,
      length_vecAdd _ _ n
        (by rw [length_vecScale, matVec_length, hDl])
        (by rw [ground.length_map, length_vecScale, matVec_length, hMl])])
    (by rw [matVec_length, length_matSwap, inertia.length_scaleB,
      inertia.idMat_len, ground.length_map, length_vecScale, hx]) ?_ q3
  refine poly.oneValue_trans
    (matVec_add_free n _ _ x hS1 hS2) ?_
  exact elim.vecAdd_congr2 _ _ _ _
    (by rw [matVec_length, lS1, length_vecScale, matVec_length, hDl])
    (by rw [matVec_length, lS2, ground.length_map, length_vecScale,
      matVec_length, hMl]) q1 q2

/-- `thm:groundreads`(iv)'s sourced pencil: at the level gap's tie
the off-line residual of the word's image solves the pencil sourced
at the electric commutator, the source cleared by the ground's
self-pairing against the gap's own weight. -/
theorem sourced_pencil (dg : List Nat) (C M Et : Mat)
    (psi : List BPair) (n : Nat) (sn sd ed : Pos) (en : BPair)
    (hdg : dg.length = n)
    (hCr : rowsLen n C) (hCl : C.length = n)
    (hMr : rowsLen n M) (hMl : M.length = n)
    (hEr : rowsLen n Et)
    (hp : psi.length = n)
    (hEt : matOneValue Et (matAdd (matAdd
        (inertia.matScale (ed * sn)
          (diagO ground.bpairOps (dg.map BPair.ofNat)))
        (matSwap (inertia.matScale (ed * sd) M)))
        (matSwap (inertia.matScaleB en (inertia.idMat n)))))
    (hker : poly.unitTail (matVec Et psi))
    (hcomm : poly.oneValue (matVec M (matVec C psi))
      (matVec C (matVec M psi))) :
    poly.oneValue (matVec Et (residD [psi] (matVec C psi)))
      (vecScale (dotN psi psi * BPair.ofPos (ed * sn))
        (matVec (momentform.commE dg C) psi)) := by
  have hml : (dg.map BPair.ofNat).length = n :=
    (ground.length_map _ dg).trans hdg
  have hDl : (diagO ground.bpairOps (dg.map BPair.ofNat)).length = n :=
    (diagO_len ground.bpairOps _).trans hml
  have hCpl : (matVec C psi).length = n := (matVec_length C psi).trans hCl
  -- the residual's one-member expansion, the source term dead at the kernel
  have step1 : poly.oneValue (matVec Et (residD [psi] (matVec C psi)))
      (vecScale (dotP psi psi) (matVec Et (matVec C psi))) := by
    refine poly.oneValue_trans
      (matVec_congr Et _ _ (residOne psi (matVec C psi) n hp hCpl)) ?_
    rw [← vecScale_swap (dotP psi (matVec C psi)) psi]
    refine poly.oneValue_trans
      (matVec_vecAdd Et n hEr _ _
        (by rw [length_vecScale]; exact hCpl)
        (by rw [length_vecScale]; exact hp)) ?_
    refine poly.oneValue_trans
      (elim.vecAdd_congr2 _ _ _ _
        (by rw [matVec_length, length_vecScale, matVec_length])
        (by rw [matVec_length, length_vecScale, matVec_length])
        (matVec_vecScale_free Et _ _)
        (matVec_vecScale_free Et _ psi)) ?_
    exact vecAdd_null_right _ _
      (by rw [length_vecScale, length_vecScale, matVec_length,
        matVec_length])
      (unitTail_vecScale _ _ hker)
  -- the kernel row solves the magnetic member against the electric
  have hsolve : poly.oneValue
      (vecScale (BPair.ofPos (ed * sn))
        (matVec (diagO ground.bpairOps (dg.map BPair.ofNat)) psi))
      (vecAdd (vecScale (BPair.ofPos (ed * sd)) (matVec M psi))
        (vecScale en psi)) := by
    refine elim.oneValue_of_null_swap _ _
      (by rw [length_vecScale, matVec_length, hDl,
        length_vecAdd _ _ n
          (by rw [length_vecScale, matVec_length]; exact hMl)
          (by rw [length_vecScale]; exact hp)]) ?_
    rw [elim.vecAdd_swapMap, ← elim.vecAdd_assoc]
    exact poly.unitTail_oneValue_right hker
      (tieRead dg M Et psi n sn sd ed en hdg hMr hMl hp hEt)
  -- the solve's word image, the two orders exchanged at the ground
  have himg : poly.oneValue
      (vecScale (BPair.ofPos (ed * sn))
        (matVec C (matVec (diagO ground.bpairOps (dg.map BPair.ofNat)) psi)))
      (vecAdd (vecScale (BPair.ofPos (ed * sd)) (matVec M (matVec C psi)))
        (vecScale en (matVec C psi))) := by
    refine poly.oneValue_trans
      (poly.oneValue_symm
        (matVec_vecScale_free C (BPair.ofPos (ed * sn)) _)) ?_
    refine poly.oneValue_trans (matVec_congr C _ _ hsolve) ?_
    refine poly.oneValue_trans
      (matVec_vecAdd_free C _ _
        (by rw [length_vecScale, length_vecScale, matVec_length, hMl, hp])) ?_
    refine elim.vecAdd_congr2 _ _ _ _
      (by rw [matVec_length, hCl, length_vecScale, matVec_length, hMl])
      (by rw [matVec_length, hCl, length_vecScale, matVec_length, hCl]) ?_ ?_
    · exact poly.oneValue_trans (matVec_vecScale_free C _ _)
        (vecScale_oneValue _ _ _ (poly.oneValue_symm hcomm))
    · exact matVec_vecScale_free C en psi
  -- the level gap at the word's image collects to the commutator
  have hEtCv : poly.oneValue (matVec Et (matVec C psi))
      (vecScale (BPair.ofPos (ed * sn))
        (matVec (momentform.commE dg C) psi)) := by
    refine poly.oneValue_trans
      (tieRead dg M Et (matVec C psi) n sn sd ed en hdg hMr hMl hCpl hEt) ?_
    rw [elim.vecAdd_assoc, ← elim.vecAdd_swapMap]
    refine poly.oneValue_trans
      (elim.vecAdd_congr2 _ _ _ _
        (by rw [length_vecScale, matVec_length, diagO_len, hml])
        (by rw [ground.length_map, ground.length_map,
          length_vecAdd _ _ n
            (by rw [length_vecScale, matVec_length, hMl])
            (by rw [length_vecScale]; exact hCpl),
          length_vecScale, matVec_length, hCl])
        (poly.oneValue_refl _)
        (poly.swapMap_oneValue (poly.oneValue_symm himg))) ?_
    refine poly.oneValue_symm ?_
    refine poly.oneValue_trans
      (vecScale_oneValue _ _ _
        (momentform.commE_read dg C psi n hdg hCr hCl hp)) ?_
    rw [← vecAdd_eq_polyAdd _ _
        (by rw [matVec_length, diagO_len, hml, ground.length_map,
          matVec_length, hCl]),
      elim.vecScale_vecAdd, elim.vecScale_swapMap]
    exact poly.oneValue_refl _
  refine poly.oneValue_trans step1 ?_
  refine poly.oneValue_trans (vecScale_oneValue _ _ _ hEtCv) ?_
  rw [elim.vecScale_vecScale]
  exact vecScale_congr
    (BPair.mul_congr (BPair.oneValue_symm (dotN_read psi psi))
      (BPair.oneValue_refl (BPair.ofPos (ed * sn)))) _

/-- The clearance comparison closes at the doubled polarization: a
datum priced by a read whose polarization returns the datum's own
scale beside a second weight withdraws at the cancellation. -/
private theorem sourceClose {X Q K p Y : BPair} {gn gd : Pos}
    (h1 : X.scale gn ≤ Q.scale gd)
    (h2 : Q.oneValue (K * p))
    (hpol : ((BPair.ofPos gn * (K * BPair.ofPos gd)) * p).scale 2
      ≤ (BPair.ofPos gn * BPair.ofPos gn) * X
        + ((K * BPair.ofPos gd) * (K * BPair.ofPos gd)) * Y) :
    X.scale (gn * gn) ≤ ((K * K) * Y).scale (gd * gd) := by
  have h1' : X.scale gn ≤ (K * p).scale gd :=
    ground.leB_congr_right (BPair.scale_congr gd h2) h1
  have e0 : ((BPair.ofPos gn * (K * BPair.ofPos gd)) * p).oneValue
      ((K * p).scale (gn * gd)) := by
    rw [BPair.mul_comm K (BPair.ofPos gd),
      ← BPair.mul_assoc (BPair.ofPos gn) (BPair.ofPos gd) K,
      BPair.mul_assoc (BPair.ofPos gn * BPair.ofPos gd) K p]
    exact BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofPos_mul gn gd))
      (BPair.ofPos_scale (gn * gd) (K * p))
  have e2 : ((BPair.ofPos gn * BPair.ofPos gn) * X).oneValue
      (X.scale (gn * gn)) :=
    BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofPos_mul gn gn))
      (BPair.ofPos_scale (gn * gn) X)
  have e3 : (((K * BPair.ofPos gd) * (K * BPair.ofPos gd)) * Y).oneValue
      (((K * K) * Y).scale (gd * gd)) := by
    rw [BPair.mul_assoc K (BPair.ofPos gd) (K * BPair.ofPos gd),
      ← BPair.mul_assoc (BPair.ofPos gd) K (BPair.ofPos gd),
      BPair.mul_comm (BPair.ofPos gd) K,
      BPair.mul_assoc K (BPair.ofPos gd) (BPair.ofPos gd),
      ← BPair.mul_assoc K K (BPair.ofPos gd * BPair.ofPos gd)]
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.mul_congr (BPair.oneValue_refl (K * K))
          (BPair.ofPos_mul gd gd))
        (BPair.oneValue_refl Y)) ?_
    rw [BPair.mul_assoc (K * K) (BPair.ofPos (gd * gd)) Y]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (K * K))
        (BPair.ofPos_scale (gd * gd) Y)) ?_
    exact BPair.oneValue_of_eq (BPair.mul_scale (K * K) Y (gd * gd))
  have hlhs : (((BPair.ofPos gn * (K * BPair.ofPos gd)) * p).scale
        2).oneValue
      (((K * p).scale gd).scale (2 * gn)) := by
    refine BPair.oneValue_trans (BPair.scale_congr 2 e0) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.scale_scale, BPair.scale_scale,
      show gn * gd * 2 = gd * (2 * gn) by
        rw [ground.mul_assoc gn gd 2, ground.mul_comm gd 2,
          ← ground.mul_assoc gn 2 gd, ground.mul_comm gn 2,
          ground.mul_assoc 2 gn gd, ground.mul_comm gn gd,
          ← ground.mul_assoc 2 gd gn, ground.mul_comm 2 gd,
          ground.mul_assoc gd 2 gn]]
  have hW : ((K * p).scale gd).scale (2 * gn)
      ≤ (X.scale gn).scale gn + ((K * K) * Y).scale (gd * gd) := by
    refine ground.leB_congr_right
      (BPair.add_congr
        (BPair.oneValue_trans e2 (BPair.oneValue_of_eq
          (BPair.scale_scale X gn gn).symm)) e3) ?_
    exact ground.leB_congr_left hlhs hpol
  exact ground.leB_congr_left
    (BPair.oneValue_of_eq (BPair.scale_scale X gn gn))
    (closeStep h1' hW)

/-- The clearance prices the connected datum by its source: at the
level gap's tie, the diagonalizing congruence with the kernel root
and the clearance at every further root, and the word's commutation
at the source, the off-line residual's weight sits at or below the
source's own against the clearance, the pencil identity read at the
residual with the polarization at the cofactor pair. -/
theorem source_weight {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : clearRead l j0 gn gd)
    (dg : List Nat) (C M : Mat) (sn sd ed : Pos) (en : BPair)
    (hdg : dg.length = n)
    (hCr : rowsLen n C) (hCl : C.length = n)
    (hMr : rowsLen n M) (hMl : M.length = n)
    (hEt : matOneValue Et (matAdd (matAdd
        (inertia.matScale (ed * sn)
          (diagO ground.bpairOps (dg.map BPair.ofNat)))
        (matSwap (inertia.matScale (ed * sd) M)))
        (matSwap (inertia.matScaleB en (inertia.idMat n)))))
    (hcomm : poly.oneValue
      (matVec M (matVec C (matVec T.val (elim.idRow n j0))))
      (matVec C (matVec M (matVec T.val (elim.idRow n j0))))) :
    BPair.scale
        (dotN (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0))))
          (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0)))))
        (gn * gn)
      ≤ BPair.scale
        ((dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)))
          * dotN
            (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0)))
            (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0))))
        ((ed * sn) * ((ed * sn) * (gd * gd))) := by
  have hTl : T.val.length = n := SqMat.rows T
  have hpl : (matVec T.val (elim.idRow n j0)).length = n := by
    rw [matVec_length]; exact hTl
  have hEr : rowsLen n Et := rowsLen_of_sqAt hd.1
  have hgc := ground_column Et T Tw l hd j0 hj0 d0 g0 hroot0
  have hCpl : (matVec C (matVec T.val (elim.idRow n j0))).length = n :=
    (matVec_length _ _).trans hCl
  have hRl : (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0)))).length = n :=
    elim.length_residD n _ _ ⟨hpl, trivial⟩ hCpl
  have hperp : (dotN (matVec T.val (elim.idRow n j0))
      (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0))))).oneValue
      BPair.unit :=
    BPair.oneValue_trans (dotN_read _ _)
      (elim.residD_perp n [matVec T.val (elim.idRow n j0)] _
        ⟨hpl, trivial⟩ hCpl
        (elim.perpAll_le1 [matVec T.val (elim.idRow n j0)]
          (Nat.le_refl 1)) 0 (Nat.succ_pos 0))
  have h1 : (dotN (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0))))
        (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0))))).scale gn
      ≤ (inertia.quadForm Et
          (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0))))).scale gd :=
    gap_perp Et T Tw l hd j0 hj0 d0 g0 hroot0 gn gd hcl _ hRl hperp
  have hsp := sourced_pencil dg C M Et
    (matVec T.val (elim.idRow n j0)) n sn sd ed en hdg hCr hCl hMr hMl
    hEr hpl hEt hgc.1 hcomm
  have h2 : (inertia.quadForm Et
      (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0))))).oneValue
      ((dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))
        * BPair.ofPos (ed * sn))
        * dotN (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0))))
          (matVec (momentform.commE dg C)
            (matVec T.val (elim.idRow n j0)))) := by
    refine BPair.oneValue_trans (dotN_congrR _ _ _ hsp) ?_
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (dotN_read _ _))
  have hpol := elim.dotN_polar
    (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0))))
    (matVec (momentform.commE dg C) (matVec T.val (elim.idRow n j0)))
    (hRl.trans ((matVec_length _ _).trans
      (ground.length_zipWith _ dg C n hdg hCl)).symm)
    (BPair.ofPos gn)
    ((dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0))
      * BPair.ofPos (ed * sn)) * BPair.ofPos gd)
  have hcls := sourceClose h1 h2 hpol
  refine ground.leB_congr_right ?_ hcls
  rw [show (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)) * BPair.ofPos (ed * sn))
      * (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)) * BPair.ofPos (ed * sn))
    = (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0))
      * dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)))
      * (BPair.ofPos (ed * sn) * BPair.ofPos (ed * sn)) by
    rw [BPair.mul_assoc
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)))
        (BPair.ofPos (ed * sn))
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)) * BPair.ofPos (ed * sn)),
      ← BPair.mul_assoc (BPair.ofPos (ed * sn))
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)))
        (BPair.ofPos (ed * sn)),
      BPair.mul_comm (BPair.ofPos (ed * sn))
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))),
      BPair.mul_assoc
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)))
        (BPair.ofPos (ed * sn)) (BPair.ofPos (ed * sn)),
      BPair.mul_assoc
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)))
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)))
        (BPair.ofPos (ed * sn) * BPair.ofPos (ed * sn))]]
  refine BPair.oneValue_trans
    (BPair.scale_congr (gd * gd)
      (BPair.oneValue_trans
        (BPair.mul_congr_left
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.ofPos_mul (ed * sn) (ed * sn))))
        (BPair.oneValue_trans
          (BPair.mul_congr_left
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq (BPair.mul_comm _ _))
              (BPair.ofPos_scale ((ed * sn) * (ed * sn)) _)))
          (BPair.oneValue_of_eq
            (BPair.scale_mul_left _ _ _).symm)))) ?_
  refine BPair.oneValue_of_eq ?_
  rw [BPair.scale_scale,
    ground.mul_assoc (ed * sn) (ed * sn) (gd * gd)]

/-- A comparison of scaled data keeps a joined factor from the
sum's unit. -/
private theorem scaleMulLe {X Y F : BPair} {a b : Pos}
    (hF : BPair.unit ≤ F) (h : X.scale a ≤ Y.scale b) :
    (X * F).scale a ≤ (Y * F).scale b := by
  rw [BPair.scale_mul_left, BPair.scale_mul_left]
  exact ground.leB_congr_right
    (BPair.oneValue_of_eq (BPair.mul_comm F (Y.scale b)))
    (ground.leB_congr_left
      (BPair.oneValue_of_eq (BPair.mul_comm F (X.scale a)))
      (ground.leB_mulR hF h))

/-- The comparison steps under a joined factor and a passive
clearing. -/
private theorem stepLe {X Y F : BPair} {a b c : Pos}
    (hF : BPair.unit ≤ F) (h : X.scale a ≤ Y.scale b) :
    (X * F).scale (a * c) ≤ (Y * F).scale (b * c) := by
  rw [← BPair.scale_scale, ← BPair.scale_scale]
  exact ground.leB_scale (scaleMulLe hF h) c

/-- The one-value read steps under a joined factor and a passive
clearing. -/
private theorem stepCongr {X Y F : BPair} {a b c : Pos}
    (h : (X.scale a).oneValue (Y.scale b)) :
    ((X * F).scale (a * c)).oneValue ((Y * F).scale (b * c)) := by
  rw [← BPair.scale_scale (X * F) a c, ← BPair.scale_scale (Y * F) b c,
    BPair.scale_mul_left X F a, BPair.scale_mul_left Y F b]
  exact BPair.scale_congr c
    (BPair.mul_congr h (BPair.oneValue_refl F))

/-- The seven clearings regroup at the peel's head. -/
private theorem posC1 (A B C D E F G : Pos) :
    ((A * B) * (C * D)) * (E * (F * G))
      = E * (F * (D * (G * (A * (B * C))))) := by
  rw [ground.mul_comm ((A * B) * (C * D)) (E * (F * G)),
    ground.mul_assoc E (F * G) ((A * B) * (C * D)),
    ground.mul_assoc F G ((A * B) * (C * D)),
    ← ground.mul_assoc (A * B) C D,
    ground.mul_assoc A B C,
    ground.mul_comm (A * (B * C)) D,
    ground.mul_left_comm G D (A * (B * C))]

/-- The head-side clearing regroups at the pinned nesting. -/
private theorem posC2 (S F P U D E G : Pos) :
    (S * (F * (P * U))) * (D * (E * G))
      = S * (G * (F * (P * (U * (D * E))))) := by
  rw [ground.mul_assoc S (F * (P * U)) (D * (E * G))]
  refine congrArg (S * ·) ?_
  rw [← ground.mul_assoc D E G,
    ground.mul_comm (D * E) G,
    ← ground.mul_assoc (F * (P * U)) G (D * E),
    ground.mul_comm (F * (P * U)) G,
    ground.mul_assoc G (F * (P * U)) (D * E),
    ground.mul_assoc F (P * U) (D * E),
    ground.mul_assoc P U (D * E)]

/-- The source-side clearing regroups at the pinned nesting. -/
private theorem posC3 (e g S N M H : Pos) :
    (e * (e * g)) * (S * (N * (M * H)))
      = S * ((e * e) * (g * (H * (N * M)))) := by
  rw [← ground.mul_assoc e e g,
    ground.mul_comm ((e * e) * g) (S * (N * (M * H))),
    ground.mul_assoc S (N * (M * H)) ((e * e) * g)]
  refine congrArg (S * ·) ?_
  rw [ground.mul_comm (N * (M * H)) ((e * e) * g),
    ground.mul_assoc (e * e) g (N * (M * H)),
    ground.mul_comm M H, ← ground.mul_assoc N H M,
    ground.mul_comm N H, ground.mul_assoc H N M]

/-- `thm:groundreads`(iv)'s close: the two reads at a head observable
against a far one read one value within the bracket the crossing
certificates and the clearance price, the crossing product the
geometric factor. -/
theorem cluster_read {n : Nat} (Et : Mat) (T Tw : SqMat n)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0
      = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : clearRead l j0 gn gd)
    (dg : List Nat) (C M : Mat) (sn sd ed : Pos) (en : BPair)
    (hdg : dg.length = n)
    (hCr : rowsLen n C) (hCl : C.length = n)
    (hMr : rowsLen n M) (hMl : M.length = n)
    (hEt : matOneValue Et (matAdd (matAdd
        (inertia.matScale (ed * sn)
          (diagO ground.bpairOps (dg.map BPair.ofNat)))
        (matSwap (inertia.matScale (ed * sd) M)))
        (matSwap (inertia.matScaleB en (inertia.idMat n)))))
    (hcomm : poly.oneValue
      (matVec M (matVec C (matVec T.val (elim.idRow n j0))))
      (matVec C (matVec M (matVec T.val (elim.idRow n j0)))))
    (diag off : List Mat) (Ys Cs : List greenprod.MatQ)
    (us ws : List greenprod.VecQ) (ns : List Nat) (jb : Nat)
    (hh : greenprod.headRead diag off Ys Cs ns)
    (hs : greenprod.solveRead diag off us ws ns)
    (hsupp : greenprod.supportAt ws jb)
    (hjb : jb < us.length)
    (s1 s2 : Pos)
    (hjoin : poly.oneValue
      (greenprod.vecScale s1 (headVec us))
      (greenprod.vecScale s2
        (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0))))))
    (cs : List ((k : Nat) × Pos × Pos × Split k))
    (hcap : capListDown (ns.map inertia.idMat) Cs cs)
    (m j : Nat) (hmj : m + j = jb)
    (k m' : Nat) (hk : k = ground.sumNat (List.take m ns))
    (hkm : k + m' = n)
    (A : Mat) (hAsq : sqAt A k)
    (hAsym : matOneValue (transposeM A) A)
    (cn cd : Pos) (spA spA' : Split k)
    (hA : capAt (inertia.matScale cd A)
      (inertia.matScale cn (inertia.idMat k)) spA spA') :
    BPair.scale
      (windowsep.mag (readGap
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec (inertia.headPad m' A)
            (matVec C (matVec T.val (elim.idRow n j0)))),
         dotN (matVec T.val (elim.idRow n j0))
           (matVec T.val (elim.idRow n j0)))
        (inertia.quadForm (inertia.headPad m' A)
            (matVec T.val (elim.idRow n j0))
          * inertia.quadForm C (matVec T.val (elim.idRow n j0)),
         dotN (matVec T.val (elim.idRow n j0))
             (matVec T.val (elim.idRow n j0))
           * dotN (matVec T.val (elim.idRow n j0))
             (matVec T.val (elim.idRow n j0)))))
      (2 * (cd * ((gn * (certD (List.take m cs)
          * (certD (List.take j (List.drop m cs))
            * ((ground.getAt ([], Pos.one) us jb).2
              * (denProd (List.take jb us)
                * denProd (List.drop (jb + 1) us))))))
        * (certD (List.take m cs)
          * certN (List.take j (List.drop m cs))))))
      ≤ BPair.scale
        (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * (BPair.scale
              ((tailFold (List.take m cs).reverse).1
                * ((dotN (matVec T.val (elim.idRow n j0))
                      (matVec T.val (elim.idRow n j0))
                    * dotN (matVec T.val (elim.idRow n j0))
                      (matVec T.val (elim.idRow n j0)))
                  * dotN
                    (matVec (momentform.commE dg C)
                      (matVec T.val (elim.idRow n j0)))
                    (matVec (momentform.commE dg C)
                      (matVec T.val (elim.idRow n j0)))))
              (((ed * sn) * (ed * sn)) * ((gd * gd)
                * ((denProd (List.drop m us)
                    * denProd (List.drop m us))
                  * ((certN (List.take j (List.drop m cs))
                      * certN (List.take j (List.drop m cs)))
                    * (denProd (List.take m us)
                      * denProd (List.take m us))))))
            + BPair.scale
              (dotN (matVec T.val (elim.idRow n j0))
                (matVec T.val (elim.idRow n j0)))
              ((certD (List.take m cs)
                  * certN (List.take j (List.drop m cs)))
                * (certD (List.take m cs)
                  * certN (List.take j (List.drop m cs))))))
        cn := by
  have hTl : T.val.length = n := SqMat.rows T
  have hpl : (matVec T.val (elim.idRow n j0)).length = n := by
    rw [matVec_length]; exact hTl
  have hAr : rowsLen k A := rowsLen_of_sqAt hAsq
  have hAl : A.length = k := sqAt_len hAsq
  have hPsq : sqAt (inertia.headPad m' A) n := by
    have h0 := inertia.sqAt_headPad m' A hAsq
    rw [hkm] at h0
    exact h0
  have hPr : rowsLen n (inertia.headPad m' A) := rowsLen_of_sqAt hPsq
  have hPlen : (inertia.headPad m' A).length = n := sqAt_len hPsq
  have hTAr : rowsLen k (transposeM A) :=
    rowsLen_cast hAl (rowsLen_transposeM A)
  have hPsym : matOneValue (transposeM (inertia.headPad m' A))
      (inertia.headPad m' A) := by
    rw [inertia.transposeM_headPad m' A hAsq]
    exact inertia.headPad_congr m' hTAr hAr hAsym
  have hcs := connected_split (inertia.headPad m' A) C
    (matVec T.val (elim.idRow n j0)) n hPr hPlen hPsym hCl hpl
  -- the reads' gap is the connected pairing, the shared summand
  -- withdrawing at the swap
  have hL1 : (windowsep.mag (readGap
      (dotN (matVec T.val (elim.idRow n j0))
        (matVec (inertia.headPad m' A)
          (matVec C (matVec T.val (elim.idRow n j0)))),
       dotN (matVec T.val (elim.idRow n j0))
         (matVec T.val (elim.idRow n j0)))
      (inertia.quadForm (inertia.headPad m' A)
          (matVec T.val (elim.idRow n j0))
        * inertia.quadForm C (matVec T.val (elim.idRow n j0)),
       dotN (matVec T.val (elim.idRow n j0))
           (matVec T.val (elim.idRow n j0))
         * dotN (matVec T.val (elim.idRow n j0))
           (matVec T.val (elim.idRow n j0))))).oneValue
      (windowsep.mag
        (dotN (residD [matVec T.val (elim.idRow n j0)]
            (matVec (inertia.headPad m' A)
              (matVec T.val (elim.idRow n j0))))
          (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0)))))) := by
    refine BPair.oneValue_trans (windowsep.mag_congr ?_)
      (BPair.oneValue_of_eq (windowsep.mag_swap _))
    show (inertia.quadForm (inertia.headPad m' A)
          (matVec T.val (elim.idRow n j0))
        * inertia.quadForm C (matVec T.val (elim.idRow n j0))
        * dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))
      + (dotN (matVec T.val (elim.idRow n j0))
          (matVec (inertia.headPad m' A)
            (matVec C (matVec T.val (elim.idRow n j0))))
        * (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)))).swap).oneValue _
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (ground.swap_congr hcs)) ?_
    rw [← BPair.swap_add, ← BPair.add_assoc]
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.add_comm _ _))
          (BPair.swap_add_null (BPair.oneValue_refl _)))
        (BPair.oneValue_refl _)) ?_
    exact BPair.unit_add _
  -- the residual expands: the pairing collapses to the head
  -- observable's image against the connected datum
  have hAv : (matVec (inertia.headPad m' A)
      (matVec T.val (elim.idRow n j0))).length = n :=
    (matVec_length _ _).trans hPlen
  have hCpl : (matVec C (matVec T.val (elim.idRow n j0))).length = n :=
    (matVec_length _ _).trans hCl
  have hRl : (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0)))).length = n :=
    elim.length_residD n _ _ ⟨hpl, trivial⟩ hCpl
  have hperpC : (dotN (matVec T.val (elim.idRow n j0))
      (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0))))).oneValue
      BPair.unit :=
    BPair.oneValue_trans (dotN_read _ _)
      (elim.residD_perp n [matVec T.val (elim.idRow n j0)] _
        ⟨hpl, trivial⟩ hCpl
        (elim.perpAll_le1 [matVec T.val (elim.idRow n j0)]
          (Nat.le_refl 1)) 0 (Nat.succ_pos 0))
  have hor := offLine_reads (matVec T.val (elim.idRow n j0))
    (matVec (inertia.headPad m' A) (matVec T.val (elim.idRow n j0)))
    n hpl hAv
  have hPexp : (dotN (residD [matVec T.val (elim.idRow n j0)]
        (matVec (inertia.headPad m' A)
          (matVec T.val (elim.idRow n j0))))
      (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0))))).oneValue
      (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))
        * dotN (matVec (inertia.headPad m' A)
            (matVec T.val (elim.idRow n j0)))
          (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0))))) := by
    refine BPair.oneValue_trans (dotN_congrL _ _ _ hor.1) ?_
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    refine BPair.oneValue_trans
      (dotP_vecAdd_left _ _ _
        (by rw [length_vecScale, matVec_length, hPlen, hRl]
            exact Nat.le_refl n)
        (by rw [ground.length_map, length_vecScale, hpl, hRl]
            exact Nat.le_refl n)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (dotP_comm _ _))
          (BPair.oneValue_trans (dotP_vecScale_right _ _ _)
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_trans
                (BPair.oneValue_of_eq (dotP_comm _ _))
                (BPair.oneValue_symm (dotN_read _ _))))))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (dotP_comm _ _))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (dotP_swapMap _ _))
            (ground.swap_congr
              (BPair.oneValue_trans (dotP_vecScale_right _ _ _)
                (BPair.oneValue_trans
                  (BPair.mul_congr (BPair.oneValue_refl _)
                    (BPair.oneValue_trans
                      (BPair.oneValue_of_eq (dotP_comm _ _))
                      (BPair.oneValue_trans
                        (BPair.oneValue_symm (dotN_read _ _)) hperpC)))
                  (BPair.mul_unit _))))))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (ground.swap_congr (BPair.oneValue_refl BPair.unit))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq (rfl : BPair.unit.swap = BPair.unit))) ?_
    exact BPair.add_unit _
  have hS : BPair.unit ≤ dotN (matVec T.val (elim.idRow n j0))
      (matVec T.val (elim.idRow n j0)) :=
    ground.leB_of_not_lt (dotN_self_side _)
  have hL2 : (windowsep.mag
      (dotN (residD [matVec T.val (elim.idRow n j0)]
          (matVec (inertia.headPad m' A)
            (matVec T.val (elim.idRow n j0))))
        (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0)))))).oneValue
      (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))
        * windowsep.mag
          (dotN (matVec (inertia.headPad m' A)
              (matVec T.val (elim.idRow n j0)))
            (residD [matVec T.val (elim.idRow n j0)]
              (matVec C (matVec T.val (elim.idRow n j0)))))) := by
    refine BPair.oneValue_trans (windowsep.mag_congr hPexp) ?_
    refine BPair.oneValue_trans (windowsep.mag_mul _ _) ?_
    exact BPair.mul_congr_left
      (BPair.oneValue_of_eq (windowsep.mag_unitLe hS))
  -- the localization at the head width
  have hkn : k ≤ n := Nat.le.intro hkm
  have htkphi : (List.take k (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0))))).length = k :=
    ground.length_take k _ (by rw [hRl]; exact hkn)
  have htkcol : (List.take k (matVec T.val (elim.idRow n j0))).length = k :=
    ground.length_take k _ (by rw [hpl]; exact hkn)
  have hph := inertia.pair_headPad (n := k) m' A hAr hAl
    (List.take k (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0)))))
    (List.drop k (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0)))))
    (List.take k (matVec T.val (elim.idRow n j0)))
    (List.drop k (matVec T.val (elim.idRow n j0)))
    htkphi htkcol
  rw [List.take_append_drop, List.take_append_drop] at hph
  have hL3 : (dotN (matVec (inertia.headPad m' A)
        (matVec T.val (elim.idRow n j0)))
      (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0))))).oneValue
      (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0)))))
        (matVec A (List.take k (matVec T.val (elim.idRow n j0))))) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (dotP_comm _ _)) ?_
    exact BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) hph
  -- the head part's weight ties to the join's leading blocks
  have hvs : greenprod.vShape us ns := hs.2.1
  have hlyh : (headVec (List.take m us)).length
      = ground.sumNat (List.take m ns) :=
    headVec_len (vShape_take m hvs)
  have hlgvs : (greenprod.vecScale (denProd (List.drop m us))
      (headVec (List.take m us))).length = k := by
    rw [show (greenprod.vecScale (denProd (List.drop m us))
        (headVec (List.take m us))).length
      = (headVec (List.take m us)).length from ground.length_map _ _,
      hlyh, hk]
  have htie : poly.oneValue
      (greenprod.vecScale s1
        (greenprod.vecScale (denProd (List.drop m us))
          (headVec (List.take m us))))
      (greenprod.vecScale s2
        (List.take k (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0)))))) := by
    have h1 := poly.take_congr k hjoin
    rw [show List.take k (greenprod.vecScale s1 (headVec us))
        = greenprod.vecScale s1 (List.take k (headVec us)) from
        ground.take_map (fun x : BPair => x.scale s1) k (headVec us),
      show List.take k (greenprod.vecScale s2
          (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0)))))
        = greenprod.vecScale s2
          (List.take k (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0))))) from
        ground.take_map (fun x : BPair => x.scale s2) k _] at h1
    refine poly.oneValue_trans ?_ h1
    refine gvsCongr s1 ?_
    refine poly.oneValue_symm ?_
    refine poly.oneValue_trans (poly.take_congr k (headVec_split m us)) ?_
    rw [show k = (greenprod.vecScale (denProd (List.drop m us))
        (headVec (List.take m us))).length from hlgvs.symm,
      ground.take_append_self]
    exact poly.oneValue_refl _
  -- the two weights at the tie's clearings
  have hwtie : ((dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))).scale
        (s2 * s2)).oneValue
      (((dotN (headVec (List.take m us)) (headVec (List.take m us))).scale
        (denProd (List.drop m us) * denProd (List.drop m us))).scale
        (s1 * s1)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (gvsSelf s2 _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (dotN_congrL _ _ _ htie)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (dotN_congrR _ _ _ htie)) ?_
    refine BPair.oneValue_trans (gvsSelf s1 _) ?_
    exact BPair.scale_congr (s1 * s1) (gvsSelf _ _)
  -- the join's leading blocks read the summed weights, and the ride
  -- prices them at the anchor
  have hWh : (dotN (headVec (List.take m us))
      (headVec (List.take m us))).oneValue
      (tailSum (List.take m (ns.map inertia.idMat))
        (List.take m us)).1 := by
    rw [ground.take_map inertia.idMat m ns]
    exact headVec_weight (List.take m us) (List.take m ns)
      (vShape_take m hvs)
  have hride := ride_price (ns.map inertia.idMat) Cs cs us ns m j jb
    (unitGramShape ns) hmj hcap
    (source_tele diag off Ys Cs us ws ns jb hh hs hsupp hjb)
  have hjbn : jb < ns.length := by
    rw [← greenprod.vShape_len hvs]; exact hjb
  have hujbl : (ground.getAt ([], Pos.one) us jb).1.length
      = ground.getAt 0 ns jb := vShape_at hvs jb hjb
  have hanchor : (inertia.quadForm
      (ground.getAt [] (ns.map inertia.idMat) jb)
      (ground.getAt ([], Pos.one) us jb).1).oneValue
      (dotN (ground.getAt ([], Pos.one) us jb).1
        (ground.getAt ([], Pos.one) us jb).1) := by
    rw [ground.getAt_map 0 [] inertia.idMat ns jb hjbn]
    exact BPair.oneValue_symm
      (dotN_congrR _ _ _
        (poly.oneValue_symm
          (inertia.matVec_idMat (ground.getAt 0 ns jb) _ hujbl)))
  have hblock := blockWeight_le jb us hjb
  -- the leading segment's weight sits inside the join's
  have hpre : ((dotN (headVec (List.take (jb + 1) us))
        (headVec (List.take (jb + 1) us))).scale
        (denProd (List.drop (jb + 1) us)
          * denProd (List.drop (jb + 1) us)))
      ≤ dotN (headVec us) (headVec us) := by
    have hsp := headVec_split (jb + 1) us
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (BPair.oneValue_trans (dotN_congrL _ _ _ hsp)
          (dotN_congrR _ _ _ hsp))) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm (dotN_app _ _ _ _ rfl)) ?_
    refine ground.leB_congr_left
      (BPair.add_unit _) ?_
    refine ground.leB_add ?_ ?_
    · exact ground.leB_congr_right
        (BPair.oneValue_symm (gvsSelf _ _)) (ground.leB_refl _)
    · exact ground.leB_of_not_lt (dotN_self_side _)
  -- the join reads the connected datum whole
  have hFtie : ((dotN (headVec us) (headVec us)).scale (s1 * s1)).oneValue
      ((dotN (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0))))
        (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0))))).scale
        (s2 * s2)) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (gvsSelf s1 _)) ?_
    refine BPair.oneValue_trans (dotN_congrL _ _ _ hjoin) ?_
    refine BPair.oneValue_trans (dotN_congrR _ _ _ hjoin) ?_
    exact gvsSelf s2 _
  have hsw := source_weight Et T Tw l hd j0 hj0 d0 g0 hroot0 gn gd hcl
    dg C M sn sd ed en hdg hCr hCl hMr hMl hEt hcomm
  -- the ride's chain, composed at the accumulated clearings
  have hy3a : ((dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))).scale
        (s2 * s2)).oneValue
      ((tailSum (List.take m (ns.map inertia.idMat))
        (List.take m us)).1.scale
        ((denProd (List.drop m us) * denProd (List.drop m us))
          * (s1 * s1))) := by
    refine BPair.oneValue_trans hwtie ?_
    rw [BPair.scale_scale]
    exact BPair.scale_congr _ hWh
  have hy3 : ((dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))).scale
        ((s2 * s2)
          * ((tailFold (List.take m cs).reverse).2
            * (prodD (List.take j (List.drop m cs))
              * ((ground.getAt ([], Pos.one) us jb).2
                * (ground.getAt ([], Pos.one) us jb).2)))))
      ≤ ((inertia.quadForm
            (ground.getAt [] (ns.map inertia.idMat) jb)
            (ground.getAt ([], Pos.one) us jb).1
          * (tailFold (List.take m cs).reverse).1).scale
        (((prodN (List.take j (List.drop m cs))
            * (tailSum (List.take m (ns.map inertia.idMat))
              (List.take m us)).2))
          * ((denProd (List.drop m us) * denProd (List.drop m us))
            * (s1 * s1)))) := by
    have h1 : ((dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0)))))
        (List.take k (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0)))))).scale
          ((s2 * s2)
            * ((tailFold (List.take m cs).reverse).2
              * (prodD (List.take j (List.drop m cs))
                * ((ground.getAt ([], Pos.one) us jb).2
                  * (ground.getAt ([], Pos.one) us jb).2))))).oneValue
        (((tailSum (List.take m (ns.map inertia.idMat))
            (List.take m us)).1.scale
          ((tailFold (List.take m cs).reverse).2
            * (prodD (List.take j (List.drop m cs))
              * ((ground.getAt ([], Pos.one) us jb).2
                * (ground.getAt ([], Pos.one) us jb).2)))).scale
          ((denProd (List.drop m us) * denProd (List.drop m us))
            * (s1 * s1))) := by
      rw [← BPair.scale_scale
        (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0)))))
          (List.take k (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0))))))
        (s2 * s2)
        ((tailFold (List.take m cs).reverse).2
          * (prodD (List.take j (List.drop m cs))
            * ((ground.getAt ([], Pos.one) us jb).2
              * (ground.getAt ([], Pos.one) us jb).2)))]
      refine BPair.oneValue_trans
        (BPair.scale_congr _ hy3a) ?_
      rw [BPair.scale_scale, BPair.scale_scale,
        ground.mul_comm
          ((denProd (List.drop m us) * denProd (List.drop m us))
            * (s1 * s1))
          ((tailFold (List.take m cs).reverse).2
            * (prodD (List.take j (List.drop m cs))
              * ((ground.getAt ([], Pos.one) us jb).2
                * (ground.getAt ([], Pos.one) us jb).2))),
        ← BPair.scale_scale]
      exact BPair.oneValue_refl _
    refine ground.leB_congr_left (BPair.oneValue_symm h1) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_of_eq (BPair.scale_scale _ _ _)) ?_
    exact ground.leB_scale hride _
  -- the anchor's substitution and the accumulated peel
  have hy4 : ((dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))).scale
        (((s2 * s2)
          * ((tailFold (List.take m cs).reverse).2
            * (prodD (List.take j (List.drop m cs))
              * ((ground.getAt ([], Pos.one) us jb).2
                * (ground.getAt ([], Pos.one) us jb).2))))
          * ((denProd (List.take jb us) * denProd (List.take jb us))
            * ((denProd (List.drop (jb + 1) us)
                * denProd (List.drop (jb + 1) us))
              * (gn * gn)))))
      ≤ ((dotN (ground.getAt ([], Pos.one) us jb).1
            (ground.getAt ([], Pos.one) us jb).1
          * (tailFold (List.take m cs).reverse).1).scale
        ((((prodN (List.take j (List.drop m cs))
            * (tailSum (List.take m (ns.map inertia.idMat))
              (List.take m us)).2))
          * ((denProd (List.drop m us) * denProd (List.drop m us))
            * (s1 * s1)))
          * ((denProd (List.take jb us) * denProd (List.take jb us))
            * ((denProd (List.drop (jb + 1) us)
                * denProd (List.drop (jb + 1) us))
              * (gn * gn))))) := by
    have hy3' := ground.leB_congr_right
      (BPair.scale_congr _
        (BPair.mul_congr hanchor
          (BPair.oneValue_refl (tailFold (List.take m cs).reverse).1)))
      hy3
    rw [← BPair.scale_scale
        (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0)))))
          (List.take k (residD [matVec T.val (elim.idRow n j0)]
            (matVec C (matVec T.val (elim.idRow n j0)))))) _ _,
      ← BPair.scale_scale
        (dotN (ground.getAt ([], Pos.one) us jb).1
            (ground.getAt ([], Pos.one) us jb).1
          * (tailFold (List.take m cs).reverse).1) _ _]
    exact ground.leB_scale hy3' _
  -- the peel: the anchor's weight rides block, prefix, join and
  -- clearance to the source
  have hF1 : BPair.unit ≤ (tailFold (List.take m cs).reverse).1 :=
    tailFold_unitLe _
  have hblock1 : (dotN (ground.getAt ([], Pos.one) us jb).1
        (ground.getAt ([], Pos.one) us jb).1).scale
        (denProd (List.take jb us) * denProd (List.take jb us))
      ≤ (dotN (headVec (List.take (jb + 1) us))
          (headVec (List.take (jb + 1) us))).scale Pos.one := by
    rw [BPair.scale_one]; exact hblock
  have hpre1 : (dotN (headVec (List.take (jb + 1) us))
        (headVec (List.take (jb + 1) us))).scale
        (denProd (List.drop (jb + 1) us)
          * denProd (List.drop (jb + 1) us))
      ≤ (dotN (headVec us) (headVec us)).scale Pos.one := by
    rw [BPair.scale_one]; exact hpre
  have hy5 := hy4
  rw [posC1 (prodN (List.take j (List.drop m cs)))
      (tailSum (List.take m (ns.map inertia.idMat)) (List.take m us)).2
      (denProd (List.drop m us) * denProd (List.drop m us)) (s1 * s1)
      (denProd (List.take jb us) * denProd (List.take jb us))
      (denProd (List.drop (jb + 1) us)
        * denProd (List.drop (jb + 1) us)) (gn * gn)] at hy5
  have hy6 := ground.leB_trans hy5 (stepLe hF1 hblock1)
  rw [ground.one_mul] at hy6
  have hy7 := ground.leB_trans hy6 (stepLe hF1 hpre1)
  rw [ground.one_mul] at hy7
  have hy8 := ground.leB_congr_right (stepCongr hFtie) hy7
  rw [ground.mul_left_comm (s2 * s2) (gn * gn)
      (prodN (List.take j (List.drop m cs))
        * ((tailSum (List.take m (ns.map inertia.idMat))
            (List.take m us)).2
          * (denProd (List.drop m us) * denProd (List.drop m us))))] at hy8
  have hy9 := ground.leB_trans hy8 (stepLe hF1 hsw)
  rw [posC3 (ed * sn) (gd * gd) (s2 * s2)
      (prodN (List.take j (List.drop m cs)))
      (tailSum (List.take m (ns.map inertia.idMat)) (List.take m us)).2
      (denProd (List.drop m us) * denProd (List.drop m us)),
    posC2 (s2 * s2) (tailFold (List.take m cs).reverse).2
      (prodD (List.take j (List.drop m cs)))
      ((ground.getAt ([], Pos.one) us jb).2
        * (ground.getAt ([], Pos.one) us jb).2)
      (denProd (List.take jb us) * denProd (List.take jb us))
      (denProd (List.drop (jb + 1) us)
        * denProd (List.drop (jb + 1) us)) (gn * gn),
    tailSum_den] at hy9
  -- cancel the join tie's clearing
  have hycore : (dotN (List.take k
        (residD [matVec T.val (elim.idRow n j0)]
          (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))).scale
        ((gn * gn)
          * ((tailFold (List.take m cs).reverse).2
            * (prodD (List.take j (List.drop m cs))
              * (((ground.getAt ([], Pos.one) us jb).2
                  * (ground.getAt ([], Pos.one) us jb).2)
                * ((denProd (List.take jb us)
                    * denProd (List.take jb us))
                  * (denProd (List.drop (jb + 1) us)
                    * denProd (List.drop (jb + 1) us)))))))
      ≤ ((dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)))
          * dotN
            (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0)))
            (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0)))
          * (tailFold (List.take m cs).reverse).1).scale
        (((ed * sn) * (ed * sn)) * ((gd * gd)
          * ((denProd (List.drop m us) * denProd (List.drop m us))
            * (prodN (List.take j (List.drop m cs))
              * (denProd (List.take m us)
                * denProd (List.take m us)))))) := by
    refine ground.leB_of_scale (w := s2 * s2) ?_
    refine ground.leB_congr_left
      (BPair.oneValue_of_eq (by
        rw [BPair.scale_scale, ground.mul_comm _ (s2 * s2)])) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_of_eq (by
        rw [BPair.scale_scale, ground.mul_comm _ (s2 * s2)])) ?_
    exact hy9
  -- the x-slot: the head observable's own weight is a prefix read
  have hcolsplit : (dotN (List.take k (matVec T.val (elim.idRow n j0)))
        (List.take k (matVec T.val (elim.idRow n j0)))
      + dotN (List.drop k (matVec T.val (elim.idRow n j0)))
        (List.drop k (matVec T.val (elim.idRow n j0)))).oneValue
      (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (dotN_app _ _ _ _ rfl)) ?_
    rw [List.take_append_drop]
    exact BPair.oneValue_refl _
  have hxslot : (dotN (List.take k (matVec T.val (elim.idRow n j0))) (List.take k (matVec T.val (elim.idRow n j0))))
      ≤ dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)) := by
    refine ground.leB_congr_right hcolsplit ?_
    refine ground.leB_congr_left (BPair.add_unit _) ?_
    exact ground.leB_add (ground.leB_refl _)
      (ground.leB_of_not_lt (dotN_self_side _))
  -- the y-slot at the ride's own crossing clearing
  have hyc2 : (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))).scale
        ((gn * gn)
        * ((tailFold (List.take m cs).reverse).2
          * (prodD (List.take j (List.drop m cs))
            * (((ground.getAt ([], Pos.one) us jb).2
                * (ground.getAt ([], Pos.one) us jb).2)
              * ((denProd (List.take jb us)
                  * denProd (List.take jb us))
                * (denProd (List.drop (jb + 1) us)
                  * denProd (List.drop (jb + 1) us)))))))
      ≤ ((tailFold (List.take m cs).reverse).1
          * (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0)))
            (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0))))).scale
        (((ed * sn) * (ed * sn)) * ((gd * gd)
          * ((denProd (List.drop m us) * denProd (List.drop m us))
            * ((certN (List.take j (List.drop m cs))
                * certN (List.take j (List.drop m cs)))
              * (denProd (List.take m us)
                * denProd (List.take m us)))))) := by
    have h := hycore
    rw [BPair.mul_comm
        (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0)))
            (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0))))
        (tailFold (List.take m cs).reverse).1,
      prodN_read (List.take j (List.drop m cs))] at h
    exact h
  -- the polarization's two weights, the certificate folds
  have hA0sq : (gn * (certD (List.take m cs)
        * (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))))))
      * (gn * (certD (List.take m cs)
        * (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))))))
      = (gn * gn)
        * ((tailFold (List.take m cs).reverse).2
          * (prodD (List.take j (List.drop m cs))
            * (((ground.getAt ([], Pos.one) us jb).2
                * (ground.getAt ([], Pos.one) us jb).2)
              * ((denProd (List.take jb us)
                  * denProd (List.take jb us))
                * (denProd (List.drop (jb + 1) us)
                  * denProd (List.drop (jb + 1) us)))))) := by
    rw [ground.mul_mul_mul_comm gn
        (certD (List.take m cs)
        * (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))))) gn
        (certD (List.take m cs)
        * (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))))),
      ground.mul_mul_mul_comm (certD (List.take m cs))
        (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))))
        (certD (List.take m cs))
        (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us)))),
      ground.mul_mul_mul_comm (certD (List.take j (List.drop m cs)))
        ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us)))
        (certD (List.take j (List.drop m cs)))
        ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))),
      ground.mul_mul_mul_comm ((ground.getAt ([], Pos.one) us jb).2)
        (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))
        ((ground.getAt ([], Pos.one) us jb).2)
        (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us)),
      ground.mul_mul_mul_comm (denProd (List.take jb us))
        (denProd (List.drop (jb + 1) us))
        (denProd (List.take jb us))
        (denProd (List.drop (jb + 1) us)),
      ← certD_rev (List.take m cs),
      ← tailFold_certD (List.take m cs).reverse,
      ← prodD_read (List.take j (List.drop m cs))]
  have ha : ((BPair.ofPos (gn * (certD (List.take m cs)
        * (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us))))))
      * BPair.ofPos (gn * (certD (List.take m cs)
        * (certD (List.take j (List.drop m cs))
          * ((ground.getAt ([], Pos.one) us jb).2
            * (denProd (List.take jb us)
              * denProd (List.drop (jb + 1) us)))))))
      * (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0))))))).oneValue
      ((dotN (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))
      (List.take k (residD [matVec T.val (elim.idRow n j0)]
        (matVec C (matVec T.val (elim.idRow n j0)))))).scale
        ((gn * gn)
        * ((tailFold (List.take m cs).reverse).2
          * (prodD (List.take j (List.drop m cs))
            * (((ground.getAt ([], Pos.one) us jb).2
                * (ground.getAt ([], Pos.one) us jb).2)
              * ((denProd (List.take jb us)
                  * denProd (List.take jb us))
                * (denProd (List.drop (jb + 1) us)
                  * denProd (List.drop (jb + 1) us)))))))) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofPos_mul _ _)) ?_
    rw [hA0sq]
    exact BPair.ofPos_scale _ _
  have hb : ((BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))) * BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
      * (dotN (List.take k (matVec T.val (elim.idRow n j0)))
      (List.take k (matVec T.val (elim.idRow n j0))))).oneValue
      ((dotN (List.take k (matVec T.val (elim.idRow n j0)))
      (List.take k (matVec T.val (elim.idRow n j0)))).scale ((certD (List.take m cs) * certN (List.take j (List.drop m cs))) * (certD (List.take m cs) * certN (List.take j (List.drop m cs))))) :=
    BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofPos_mul _ _))
      (BPair.ofPos_scale _ _)
  have hxsq := ground.leB_scale hxslot ((certD (List.take m cs) * certN (List.take j (List.drop m cs))) * (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
  -- the two-sided cap read at the head width
  have h1 := truncation.cap_polar A cn cd spA spA' hA
    (List.take k (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0)))))
    (List.take k (matVec T.val (elim.idRow n j0)))
    htkphi htkcol (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us))))))) (BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
  have h2 := truncation.cap_polar A cn cd spA spA' hA
    (List.take k (residD [matVec T.val (elim.idRow n j0)]
      (matVec C (matVec T.val (elim.idRow n j0)))))
    (List.take k (matVec T.val (elim.idRow n j0)))
    htkphi htkcol (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))))
    (BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs)))).swap
  rw [BPair.swap_mul_swap (BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
      (BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs)))),
    BPair.mul_swap (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))))
      (BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs)))),
    BPair.swap_mul (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
      (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0))))),
    ← BPair.mul_swap (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
      (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0)))))] at h2
  -- the polarized sum's bound at the two slots
  have hsum := ground.leB_scale (ground.leB_congr_left
    (BPair.oneValue_symm (BPair.add_congr ha hb))
    (ground.leB_add hyc2 hxsq)) cn
  have h1' := ground.leB_trans h1 hsum
  have h2' := ground.leB_trans h2 hsum
  rw [BPair.scale_mul_left
    (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
    (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0)))))
    (2 * cd)] at h1'
  rw [BPair.scale_mul_left
    (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
    (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0))))).swap (2 * cd)] at h2'
  -- the magnitude closes at the common factor
  have hmag := windowsep.mag_mul_le h1' h2'
  have hKmag : ((BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
        * windowsep.mag (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0)))))).oneValue
      ((windowsep.mag (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0)))))).scale
        ((gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * (certD (List.take m cs) * certN (List.take j (List.drop m cs))))) :=
    BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.ofPos_mul _ _))
      (BPair.ofPos_scale _ _)
  rw [← BPair.scale_mul_left
    (BPair.ofPos (gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * BPair.ofPos (certD (List.take m cs) * certN (List.take j (List.drop m cs))))
    (windowsep.mag (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0)))))) (2 * cd)] at hmag
  have hmag2 := ground.leB_congr_left
    (BPair.scale_congr (2 * cd) hKmag) hmag
  rw [BPair.scale_scale,
    ground.mul_comm ((gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * (certD (List.take m cs) * certN (List.take j (List.drop m cs)))) (2 * cd),
    ground.mul_assoc 2 cd ((gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * (certD (List.take m cs) * certN (List.take j (List.drop m cs))))] at hmag2
  -- the outer pairing multiplies through
  have hSm := ground.leB_mulR hS hmag2
  rw [BPair.mul_scale
      (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)))
      (windowsep.mag (dotN (List.take k (residD [matVec T.val (elim.idRow n j0)] (matVec C (matVec T.val (elim.idRow n j0))))) (matVec A (List.take k (matVec T.val (elim.idRow n j0))))))
      (2 * (cd * ((gn * (certD (List.take m cs) * (certD (List.take j (List.drop m cs)) * ((ground.getAt ([], Pos.one) us jb).2 * (denProd (List.take jb us) * denProd (List.drop (jb + 1) us)))))) * (certD (List.take m cs) * certN (List.take j (List.drop m cs)))))),
    BPair.mul_scale
      (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)))
      (BPair.scale ((tailFold (List.take m cs).reverse).1
          * (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * dotN (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0)))
            (matVec (momentform.commE dg C)
              (matVec T.val (elim.idRow n j0)))))
          (((ed * sn) * (ed * sn)) * ((gd * gd)
          * ((denProd (List.drop m us) * denProd (List.drop m us))
            * ((certN (List.take j (List.drop m cs))
                * certN (List.take j (List.drop m cs)))
              * (denProd (List.take m us)
                * denProd (List.take m us))))))
        + BPair.scale (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)))
          ((certD (List.take m cs) * certN (List.take j (List.drop m cs))) * (certD (List.take m cs) * certN (List.take j (List.drop m cs))))) cn] at hSm
  -- the display closes at the collapse chain
  have hfin := BPair.oneValue_trans hL1 (BPair.oneValue_trans hL2
    (BPair.mul_congr (BPair.oneValue_refl _)
      (windowsep.mag_congr hL3)))
  exact ground.leB_congr_left
    (BPair.scale_congr _ (BPair.oneValue_symm hfin)) hSm

/-- Clause (v)'s member comparison at one count: at the witnessed
gap the lower member's power sits at or below the upper's, the
split's square identity read at the power, the pair comparison
cross-multiplied. -/
theorem euc_le (A D g : Pos) (n : Nat)
    (hg : A + g = posOfSucc n * D) :
    Pos.pow g (n + 1) * Pos.pow (posOfSucc n * D + A) (n + 1)
      ≤ Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc n * D) (n + 1) := by
  have h1 : g * (posOfSucc n * D + A)
      ≤ posOfSucc n * D * (posOfSucc n * D) :=
    Or.inr ⟨A * A, Pos.sq_split A g (posOfSucc n * D) hg⟩
  have h2 := Pos.pow_le h1 (n + 1)
  rw [Pos.pow_mul g (posOfSucc n * D + A) (n + 1),
    Pos.pow_mul (posOfSucc n * D) (posOfSucc n * D) (n + 1)] at h2
  exact h2

/-- Clause (v)'s width: the upper member's power sits at or below
the lower's joined to the width `[A * A : N * D * D]`, the Bernoulli
display's upper side at the split square — the members' gap at most
the width at every spectral point, the pair comparison
cross-multiplied. -/
theorem euc_width (A D g : Pos) (n : Nat)
    (hg : A + g = posOfSucc n * D) :
    Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc n * D) (n + 1)
        * (posOfSucc n * (D * D))
      ≤ (Pos.pow g (n + 1) * (posOfSucc n * (D * D))
          + A * A * Pos.pow (posOfSucc n * D) (n + 1))
        * Pos.pow (posOfSucc n * D + A) (n + 1) := by
  have h0 : A * A + g * (posOfSucc n * D + A)
      = posOfSucc n * D * (posOfSucc n * D) := by
    rw [add_comm]
    exact Pos.sq_split A g (posOfSucc n * D) hg
  have hber := Pos.bernoulli_le (A * A) (g * (posOfSucc n * D + A))
    (posOfSucc n * D * (posOfSucc n * D)) h0 n
  have hs := mul_le_mul_right (posOfSucc n * (D * D)) hber
  have eq1 : Pos.pow (posOfSucc n * D * (posOfSucc n * D)) (n + 1)
      = Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc n * D) (n + 1) :=
    Pos.pow_mul (posOfSucc n * D) (posOfSucc n * D) (n + 1)
  have eq2 : Pos.pow (g * (posOfSucc n * D + A)) (n + 1)
        * (posOfSucc n * (D * D))
      = Pos.pow g (n + 1) * (posOfSucc n * (D * D))
        * Pos.pow (posOfSucc n * D + A) (n + 1) := by
    rw [Pos.pow_mul g (posOfSucc n * D + A) (n + 1),
      mul_right_comm (Pos.pow g (n + 1))
        (Pos.pow (posOfSucc n * D + A) (n + 1))
        (posOfSucc n * (D * D))]
  have hp : posOfSucc n * D * (posOfSucc n * D)
        * Pos.pow (posOfSucc n * D * (posOfSucc n * D)) n
      = Pos.pow (posOfSucc n * D * (posOfSucc n * D)) (n + 1) := rfl
  have eq3 : posOfSucc n * (A * A)
        * Pos.pow (posOfSucc n * D * (posOfSucc n * D)) n
        * (posOfSucc n * (D * D))
      = A * A * Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc n * D) (n + 1) := by
    rw [mul_right_comm (posOfSucc n * (A * A))
        (Pos.pow (posOfSucc n * D * (posOfSucc n * D)) n)
        (posOfSucc n * (D * D)),
      mul_mul_mul_comm (posOfSucc n) (A * A) (posOfSucc n) (D * D),
      ← mul_assoc (posOfSucc n * posOfSucc n) (A * A) (D * D),
      mul_comm (posOfSucc n * posOfSucc n) (A * A),
      mul_assoc (A * A) (posOfSucc n * posOfSucc n) (D * D),
      ← mul_mul_mul_comm (posOfSucc n) D (posOfSucc n) D,
      mul_assoc (A * A) (posOfSucc n * D * (posOfSucc n * D))
        (Pos.pow (posOfSucc n * D * (posOfSucc n * D)) n),
      hp, eq1, ← mul_assoc (A * A) (Pos.pow (posOfSucc n * D) (n + 1))
        (Pos.pow (posOfSucc n * D) (n + 1))]
  have hT2 : posOfSucc n * (A * A)
        * Pos.pow (posOfSucc n * D * (posOfSucc n * D)) n
        * (posOfSucc n * (D * D))
      ≤ A * A * Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc n * D + A) (n + 1) := by
    rw [eq3,
      mul_comm (A * A * Pos.pow (posOfSucc n * D) (n + 1))
        (Pos.pow (posOfSucc n * D) (n + 1)),
      mul_comm (A * A * Pos.pow (posOfSucc n * D) (n + 1))
        (Pos.pow (posOfSucc n * D + A) (n + 1))]
    exact mul_le_mul_right (A * A * Pos.pow (posOfSucc n * D) (n + 1))
      (Pos.pow_le (posLeSelfAdd (posOfSucc n * D) A) (n + 1))
  rw [right_distrib (Pos.pow g (n + 1) * (posOfSucc n * (D * D)))
      (A * A * Pos.pow (posOfSucc n * D) (n + 1))
      (Pos.pow (posOfSucc n * D + A) (n + 1)), ← eq1]
  refine le_trans hs ?_
  rw [right_distrib (Pos.pow (g * (posOfSucc n * D + A)) (n + 1))
      (posOfSucc n * (A * A)
        * Pos.pow (posOfSucc n * D * (posOfSucc n * D)) n)
      (posOfSucc n * (D * D))]
  exact posLeAdd (Or.inl eq2) hT2

/-- The refinement comparison's upper arm: one more count moves the
upper member down, the Bernoulli display's upper side read at the
crossed pair, the comparison cross-multiplied. -/
theorem euc_hi_mono (A D : Pos) (n : Nat) :
    Pos.pow (posOfSucc (n + 1) * D) (n + 2)
        * Pos.pow (posOfSucc n * D + A) (n + 1)
      ≤ Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc (n + 1) * D + A) (n + 2) := by
  have hone : Pos.one + posOfSucc n = posOfSucc (n + 1) :=
    one_add (posOfSucc n)
  have hAN : A + posOfSucc n * A = posOfSucc (n + 1) * A := by
    rw [← hone, right_distrib Pos.one (posOfSucc n) A, one_mul]
  have hNN : posOfSucc n * (posOfSucc (n + 1) * D)
      = posOfSucc (n + 1) * (posOfSucc n * D) := by
    rw [← mul_assoc (posOfSucc n) (posOfSucc (n + 1)) D,
      mul_comm (posOfSucc n) (posOfSucc (n + 1)),
      mul_assoc (posOfSucc (n + 1)) (posOfSucc n) D]
  have hb0 : A + posOfSucc n * (posOfSucc (n + 1) * D + A)
      = posOfSucc (n + 1) * (posOfSucc n * D + A) := by
    rw [left_distrib (posOfSucc n) (posOfSucc (n + 1) * D) A,
      left_distrib (posOfSucc (n + 1)) (posOfSucc n * D) A,
      add_left_comm A (posOfSucc n * (posOfSucc (n + 1) * D))
        (posOfSucc n * A),
      hAN, hNN]
  have hber := Pos.bernoulli_le A
    (posOfSucc n * (posOfSucc (n + 1) * D + A))
    (posOfSucc (n + 1) * (posOfSucc n * D + A)) hb0 n
  have hcap := mul_le_mul_right (posOfSucc (n + 1) * D + A) hber
  rw [right_distrib
      (Pos.pow (posOfSucc n * (posOfSucc (n + 1) * D + A)) (n + 1))
      (posOfSucc n * A
        * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n)
      (posOfSucc (n + 1) * D + A)] at hcap
  have hpb : posOfSucc (n + 1) * (posOfSucc n * D + A)
      * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n
      = Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1) := rfl
  have hAb : A * (posOfSucc (n + 1) * (posOfSucc n * D + A))
      = A * A + posOfSucc n * A * (posOfSucc (n + 1) * D + A) := by
    rw [← hb0,
      left_distrib A A (posOfSucc n * (posOfSucc (n + 1) * D + A)),
      ← mul_assoc A (posOfSucc n) (posOfSucc (n + 1) * D + A),
      mul_comm A (posOfSucc n)]
  have hA1 : A * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1)
      = A * A * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n
        + posOfSucc n * A
            * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n
            * (posOfSucc (n + 1) * D + A) := by
    rw [← hpb,
      ← mul_assoc A (posOfSucc (n + 1) * (posOfSucc n * D + A))
        (Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n),
      hAb,
      right_distrib (A * A)
        (posOfSucc n * A * (posOfSucc (n + 1) * D + A))
        (Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n),
      mul_right_comm (posOfSucc n * A) (posOfSucc (n + 1) * D + A)
        (Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n)]
  have hexp : Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1)
        * (posOfSucc (n + 1) * D + A)
      = (posOfSucc (n + 1) * D
            * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1)
          + A * A
            * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n)
        + posOfSucc n * A
            * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n
            * (posOfSucc (n + 1) * D + A) := by
    rw [mul_comm
        (Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1))
        (posOfSucc (n + 1) * D + A),
      right_distrib (posOfSucc (n + 1) * D) A
        (Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1)),
      hA1,
      ← add_assoc (posOfSucc (n + 1) * D
          * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1))
        (A * A * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n)
        (posOfSucc n * A
          * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n
          * (posOfSucc (n + 1) * D + A))]
  rw [hexp] at hcap
  have hcut := ground.posLeCancelR hcap
  have hstep := le_trans (posLeSelfAdd
    (posOfSucc (n + 1) * D
      * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1))
    (A * A * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) n)) hcut
  have hL : posOfSucc (n + 1) * D
        * Pos.pow (posOfSucc (n + 1) * (posOfSucc n * D + A)) (n + 1)
      = D * Pos.pow (posOfSucc (n + 1)) (n + 2)
        * Pos.pow (posOfSucc n * D + A) (n + 1) := by
    rw [Pos.pow_mul (posOfSucc (n + 1)) (posOfSucc n * D + A) (n + 1),
      ← mul_assoc (posOfSucc (n + 1) * D)
        (Pos.pow (posOfSucc (n + 1)) (n + 1))
        (Pos.pow (posOfSucc n * D + A) (n + 1)),
      mul_comm (posOfSucc (n + 1)) D,
      mul_assoc D (posOfSucc (n + 1)) (Pos.pow (posOfSucc (n + 1)) (n + 1))]
    rfl
  have hR : Pos.pow (posOfSucc n * (posOfSucc (n + 1) * D + A)) (n + 1)
        * (posOfSucc (n + 1) * D + A)
      = Pos.pow (posOfSucc n) (n + 1)
        * Pos.pow (posOfSucc (n + 1) * D + A) (n + 2) := by
    rw [Pos.pow_mul (posOfSucc n) (posOfSucc (n + 1) * D + A) (n + 1),
      mul_assoc (Pos.pow (posOfSucc n) (n + 1))
        (Pos.pow (posOfSucc (n + 1) * D + A) (n + 1))
        (posOfSucc (n + 1) * D + A),
      mul_comm (Pos.pow (posOfSucc (n + 1) * D + A) (n + 1))
        (posOfSucc (n + 1) * D + A)]
    rfl
  rw [hL, hR] at hstep
  have hmul := mul_le_mul_right (Pos.pow D (n + 1)) hstep
  have hLf : D * Pos.pow (posOfSucc (n + 1)) (n + 2)
        * Pos.pow (posOfSucc n * D + A) (n + 1) * Pos.pow D (n + 1)
      = Pos.pow (posOfSucc (n + 1) * D) (n + 2)
        * Pos.pow (posOfSucc n * D + A) (n + 1) := by
    rw [mul_right_comm (D * Pos.pow (posOfSucc (n + 1)) (n + 2))
        (Pos.pow (posOfSucc n * D + A) (n + 1)) (Pos.pow D (n + 1)),
      mul_comm D (Pos.pow (posOfSucc (n + 1)) (n + 2)),
      mul_assoc (Pos.pow (posOfSucc (n + 1)) (n + 2)) D (Pos.pow D (n + 1)),
      show D * Pos.pow D (n + 1) = Pos.pow D (n + 2) from rfl,
      ← Pos.pow_mul (posOfSucc (n + 1)) D (n + 2)]
  have hRf : Pos.pow (posOfSucc n) (n + 1)
        * Pos.pow (posOfSucc (n + 1) * D + A) (n + 2) * Pos.pow D (n + 1)
      = Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc (n + 1) * D + A) (n + 2) := by
    rw [mul_right_comm (Pos.pow (posOfSucc n) (n + 1))
        (Pos.pow (posOfSucc (n + 1) * D + A) (n + 2)) (Pos.pow D (n + 1)),
      ← Pos.pow_mul (posOfSucc n) D (n + 1)]
  rw [hLf, hRf] at hmul
  exact hmul

/-- The refinement comparison's lower arm: one more count moves the
lower member up, the Bernoulli display's lower side read at the
crossed pair, the comparison cross-multiplied. -/
theorem euc_lo_mono (A D g : Pos) (n : Nat)
    (hg : A + g = posOfSucc n * D) :
    Pos.pow g (n + 1) * Pos.pow (posOfSucc (n + 1) * D) (n + 2)
      ≤ Pos.pow (g + D) (n + 2)
        * Pos.pow (posOfSucc n * D) (n + 1) := by
  have hone2 : posOfSucc n + Pos.one = posOfSucc (n + 1) :=
    add_one (posOfSucc n)
  have hgN : posOfSucc n * g + g = posOfSucc (n + 1) * g := by
    rw [← hone2, right_distrib (posOfSucc n) Pos.one g, one_mul]
  have hND : posOfSucc n * D + D = posOfSucc (n + 1) * D := by
    rw [← hone2, right_distrib (posOfSucc n) Pos.one D, one_mul]
  have hb1 : A + posOfSucc (n + 1) * g = posOfSucc n * (g + D) := by
    rw [left_distrib (posOfSucc n) g D, ← hg,
      add_left_comm (posOfSucc n * g) A g, hgN]
  have hlow : Pos.pow (posOfSucc (n + 1) * g) (n + 2)
      + posOfSucc (n + 1) * A * Pos.pow (posOfSucc (n + 1) * g) (n + 1)
      ≤ Pos.pow (posOfSucc n * (g + D)) (n + 2) :=
    Pos.bernoulli_ge A (posOfSucc (n + 1) * g)
      (posOfSucc n * (g + D)) hb1 (n + 1)
  have hcollect : Pos.pow (posOfSucc (n + 1) * g) (n + 2)
      + posOfSucc (n + 1) * A * Pos.pow (posOfSucc (n + 1) * g) (n + 1)
      = (posOfSucc (n + 1) * g + posOfSucc (n + 1) * A)
        * Pos.pow (posOfSucc (n + 1) * g) (n + 1) := by
    rw [right_distrib (posOfSucc (n + 1) * g) (posOfSucc (n + 1) * A)
      (Pos.pow (posOfSucc (n + 1) * g) (n + 1))]
    rfl
  have hkey : posOfSucc (n + 1) * g + posOfSucc (n + 1) * A
      = posOfSucc n * (posOfSucc (n + 1) * D) := by
    rw [← hND, left_distrib (posOfSucc n) (posOfSucc n * D) D, ← hg,
      ← left_distrib (posOfSucc (n + 1)) g A, ← hone2,
      right_distrib (posOfSucc n) Pos.one (g + A), one_mul,
      add_comm g A]
  have hcol : posOfSucc n * (posOfSucc (n + 1) * D)
        * Pos.pow (posOfSucc (n + 1) * g) (n + 1)
      ≤ Pos.pow (posOfSucc n * (g + D)) (n + 2) := by
    rw [← hkey, ← hcollect]
    exact hlow
  have hLu : posOfSucc n * (posOfSucc (n + 1) * D)
        * Pos.pow (posOfSucc (n + 1) * g) (n + 1)
      = D * Pos.pow (posOfSucc (n + 1)) (n + 2) * Pos.pow g (n + 1)
        * posOfSucc n := by
    rw [Pos.pow_mul (posOfSucc (n + 1)) g (n + 1),
      ← mul_assoc (posOfSucc n * (posOfSucc (n + 1) * D))
        (Pos.pow (posOfSucc (n + 1)) (n + 1)) (Pos.pow g (n + 1)),
      mul_comm (posOfSucc n) (posOfSucc (n + 1) * D),
      mul_right_comm (posOfSucc (n + 1) * D) (posOfSucc n)
        (Pos.pow (posOfSucc (n + 1)) (n + 1)),
      mul_comm (posOfSucc (n + 1)) D,
      mul_assoc D (posOfSucc (n + 1)) (Pos.pow (posOfSucc (n + 1)) (n + 1)),
      mul_right_comm (D * (posOfSucc (n + 1)
        * Pos.pow (posOfSucc (n + 1)) (n + 1))) (posOfSucc n)
        (Pos.pow g (n + 1))]
    rfl
  have hPN : Pos.pow (posOfSucc n) (n + 2)
      = posOfSucc n * Pos.pow (posOfSucc n) (n + 1) := rfl
  have hRu : Pos.pow (posOfSucc n * (g + D)) (n + 2)
      = Pos.pow (posOfSucc n) (n + 1) * Pos.pow (g + D) (n + 2)
        * posOfSucc n := by
    rw [Pos.pow_mul (posOfSucc n) (g + D) (n + 2), hPN,
      mul_comm (posOfSucc n) (Pos.pow (posOfSucc n) (n + 1)),
      mul_right_comm (Pos.pow (posOfSucc n) (n + 1)) (posOfSucc n)
        (Pos.pow (g + D) (n + 2))]
  rw [hLu, hRu] at hcol
  have hcan := ground.le_of_mul_le hcol
  have hmul := mul_le_mul_right (Pos.pow D (n + 1)) hcan
  have hLf : D * Pos.pow (posOfSucc (n + 1)) (n + 2) * Pos.pow g (n + 1)
        * Pos.pow D (n + 1)
      = Pos.pow g (n + 1) * Pos.pow (posOfSucc (n + 1) * D) (n + 2) := by
    rw [mul_right_comm (D * Pos.pow (posOfSucc (n + 1)) (n + 2))
        (Pos.pow g (n + 1)) (Pos.pow D (n + 1)),
      mul_comm D (Pos.pow (posOfSucc (n + 1)) (n + 2)),
      mul_assoc (Pos.pow (posOfSucc (n + 1)) (n + 2)) D (Pos.pow D (n + 1)),
      show D * Pos.pow D (n + 1) = Pos.pow D (n + 2) from rfl,
      ← Pos.pow_mul (posOfSucc (n + 1)) D (n + 2),
      mul_comm (Pos.pow (posOfSucc (n + 1) * D) (n + 2))
        (Pos.pow g (n + 1))]
  have hRf : Pos.pow (posOfSucc n) (n + 1) * Pos.pow (g + D) (n + 2)
        * Pos.pow D (n + 1)
      = Pos.pow (g + D) (n + 2) * Pos.pow (posOfSucc n * D) (n + 1) := by
    rw [mul_right_comm (Pos.pow (posOfSucc n) (n + 1))
        (Pos.pow (g + D) (n + 2)) (Pos.pow D (n + 1)),
      ← Pos.pow_mul (posOfSucc n) D (n + 1),
      mul_comm (Pos.pow (posOfSucc n * D) (n + 1))
        (Pos.pow (g + D) (n + 2))]
  rw [hLf, hRf] at hmul
  exact hmul

/-- The cross-multiplied comparisons compose: two located-pair
reads at a shared middle chain to the outer pair's read. -/
private theorem crossTrans {a b c d e f : Pos}
    (h1 : a * b ≤ c * d) (h2 : c * e ≤ f * b) :
    a * e ≤ f * d := by
  refine ground.le_of_mul_le (c := c * b) ?_
  have e1 : a * e * (c * b) = a * b * (c * e) := by
    rw [mul_mul_mul_comm a e c b, mul_mul_mul_comm a b c e,
      mul_comm e b]
  have e2 : f * d * (c * b) = c * d * (f * b) := by
    rw [mul_mul_mul_comm f d c b, mul_mul_mul_comm c d f b,
      mul_comm f c]
  rw [e1, e2]
  refine le_trans (mul_le_mul_right (c * e) h1) ?_
  rw [mul_comm (c * d) (c * e), mul_comm (c * d) (f * b)]
  exact mul_le_mul_right (c * d) h2

/-- The refinement comparison's upper arm at every larger count:
the one-count arm chained along the added counts, each step the
Bernoulli display's read. -/
theorem euc_hi_mono_le (A D : Pos) (n : Nat) : ∀ k : Nat,
    Pos.pow (posOfSucc (n + k) * D) (n + k + 1)
        * Pos.pow (posOfSucc n * D + A) (n + 1)
      ≤ Pos.pow (posOfSucc n * D) (n + 1)
        * Pos.pow (posOfSucc (n + k) * D + A) (n + k + 1)
  | 0 => Or.inl rfl
  | k + 1 =>
    crossTrans (euc_hi_mono A D (n + k)) (euc_hi_mono_le A D n k)

/-- The lower gap at a later count: one denominator per added
count. -/
def gapUp (g D : Pos) : Nat → Pos
  | 0 => g
  | k + 1 => gapUp g D k + D

/-- The later count's gap solves its own level's split. -/
theorem gapUp_eq (A D g : Pos) (n : Nat)
    (hg : A + g = posOfSucc n * D) :
    ∀ k, A + gapUp g D k = posOfSucc (n + k) * D
  | 0 => hg
  | k + 1 => by
    show A + (gapUp g D k + D) = posOfSucc (n + k + 1) * D
    have hone : posOfSucc (n + k) + Pos.one = posOfSucc (n + k + 1) :=
      add_one (posOfSucc (n + k))
    rw [← add_assoc, gapUp_eq A D g n hg k, ← hone, right_distrib,
      one_mul]

/-- The refinement comparison's lower arm at every larger count:
the one-count arm chained along the added counts at the stepped
gaps, each step the Bernoulli display's read. -/
theorem euc_lo_mono_le (A D g : Pos) (n : Nat)
    (hg : A + g = posOfSucc n * D) : ∀ k : Nat,
    Pos.pow g (n + 1) * Pos.pow (posOfSucc (n + k) * D) (n + k + 1)
      ≤ Pos.pow (gapUp g D k) (n + k + 1)
        * Pos.pow (posOfSucc n * D) (n + 1)
  | 0 => Or.inl rfl
  | k + 1 => by
    have hstep := euc_lo_mono A D (gapUp g D k) (n + k)
      (gapUp_eq A D g n hg k)
    exact crossTrans (euc_lo_mono_le A D g n hg k) hstep

/-! Clause (v): the Euclidean brackets' witness tier. -/

/-- Clause (v)'s certificate fold: per root the kernel arm at the
stated full gap, or the positive arm at the stated representative,
gap witness and cap, the two lists read together. -/
def eucGo (un ud kn kd N : Pos) :
    List (BPair × Pos × BPair) → List (Pos × Pos) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | r :: t, w :: ws =>
    ((decide (r.1.oneValue BPair.unit)
        && decide (w.2 = N * (ud * r.2.1)))
      || (decide (r.1.oneValue (BPair.ofPos w.1))
          && decide (un * w.1 + w.2 = N * (ud * r.2.1))
          && decide (w.1 * kd ≤ kn * r.2.1)))
      && eucGo un ud kn kd N t ws

def eucRead (un ud kn kd N : Pos)
    (l : List (BPair × Pos × BPair)) (ws : List (Pos × Pos)) : Prop :=
  eucGo un ud kn kd N l ws = true

instance (un ud kn kd N : Pos) (l : List (BPair × Pos × BPair))
    (ws : List (Pos × Pos)) :
    Decidable (eucRead un ud kn kd N l ws) :=
  inferInstanceAs (Decidable (_ = _))

/-- The fold ties the two lists' lengths. -/
theorem eucRead_len (un ud kn kd N : Pos) :
    ∀ (l : List (BPair × Pos × BPair)) (ws : List (Pos × Pos)),
      eucRead un ud kn kd N l ws → l.length = ws.length
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | _ :: t, _ :: ws, h => by
    show t.length + 1 = ws.length + 1
    rw [eucRead_len un ud kn kd N t ws (ground.andSplitB h).2]

/-- The fold's per-root arm: at every key the root reads the kernel
arm at the stated gap, or the positive arm at the stated
representative, gap witness, and cap. -/
theorem eucRead_at (un ud kn kd N : Pos) :
    ∀ (l : List (BPair × Pos × BPair)) (ws : List (Pos × Pos)),
      eucRead un ud kn kd N l ws →
      ∀ j, j < l.length →
      ∀ (nj gj : BPair) (dj : Pos),
        ground.getAt (BPair.unit, Pos.one, BPair.unit) l j = (nj, dj, gj) →
      ∀ (p g : Pos),
        ground.getAt (Pos.one, Pos.one) ws j = (p, g) →
      (nj.oneValue BPair.unit ∧ g = N * (ud * dj))
        ∨ (nj.oneValue (BPair.ofPos p)
            ∧ un * p + g = N * (ud * dj)
            ∧ p * kd ≤ kn * dj)
  | [], _, _, j, hj, _, _, _, _, _, _, _ => absurd hj (Nat.not_lt_zero j)
  | _ :: _, [], h, _, _, _, _, _, _, _, _, _ => Bool.noConfusion h
  | r :: _, w :: _, h, 0, _, nj, gj, dj, hroot, p, g, hw => by
    have h1 := (ground.andSplitB h).1
    have er : r = (nj, dj, gj) := hroot
    have ew : w = (p, g) := hw
    rw [er, ew] at h1
    refine (ground.orSplitB h1).elim (fun hk => ?_) (fun hp => ?_)
    · exact Or.inl ⟨of_decide_eq_true (ground.andSplitB hk).1,
        of_decide_eq_true (ground.andSplitB hk).2⟩
    · exact Or.inr ⟨of_decide_eq_true
          (ground.andSplitB (ground.andSplitB hp).1).1,
        of_decide_eq_true (ground.andSplitB (ground.andSplitB hp).1).2,
        of_decide_eq_true (ground.andSplitB hp).2⟩
  | _ :: t, _ :: ws, h, j + 1, hj, nj, gj, dj, hroot, p, g, hw =>
    eucRead_at un ud kn kd N t ws (ground.andSplitB h).2 j
      (Nat.lt_of_succ_lt_succ hj) nj gj dj hroot p g hw

/-- The certificate's arm at a key: each root's numerator reads the
sum's unit or the stated positive representative. -/
theorem eucRead_arm (un ud kn kd N : Pos)
    (l : List (BPair × Pos × BPair)) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd N l ws) :
    ∀ k, k < l.length →
    ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1).oneValue
        BPair.unit
      ∨ ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1).oneValue
          (BPair.ofPos (ground.getAt (Pos.one, Pos.one) ws k).1) :=
  fun k hk =>
    (eucRead_at un ud kn kd N l ws hw k hk _ _ _ rfl _ _ rfl).imp
      And.left And.left


/-- The two-summand solve identity applied at a vector: the summed
scaled actions read the stated scale of the vector itself. -/
private theorem solveCols {o : Nat} (M1 M2 : Mat) (s1 s2 s3 : Pos)
    (hM1 : sqAt M1 o) (hM2r : rowsLen o M2)
    (hI : elim.matOneValue
      (matAdd (inertia.matScale s1 M1) (inertia.matScale s2 M2))
      (inertia.matScale s3 (idMat o)))
    (v : List BPair) (hv : v.length = o) :
    poly.oneValue
      (vecAdd (vecScale (BPair.ofPos s1) (matVec M1 v))
        (vecScale (BPair.ofPos s2) (matVec M2 v)))
      (vecScale (BPair.ofPos s3) v) := by
  have h0 : poly.oneValue
      (matVec (matAdd (inertia.matScale s1 M1)
        (inertia.matScale s2 M2)) v)
      (matVec (inertia.matScale s3 (idMat o)) v) :=
    matVec_matOne _ _ _ hI
  have h1 : poly.oneValue
      (matVec (matAdd (inertia.matScale s1 M1)
        (inertia.matScale s2 M2)) v)
      (vecAdd (matVec (inertia.matScale s1 M1) v)
        (matVec (inertia.matScale s2 M2) v)) :=
    matVec_add_free o _ _ v
      (rowsLen_of_sqAt (inertia.sqAt_matScale o s1 M1 hM1))
      (elim.rowsLen_mapRows _ M2 o hM2r)
  have h2 : poly.oneValue
      (vecAdd (matVec (inertia.matScale s1 M1) v)
        (matVec (inertia.matScale s2 M2) v))
      (vecAdd (vecScale (BPair.ofPos s1) (matVec M1 v))
        (vecScale (BPair.ofPos s2) (matVec M2 v))) :=
    vecAdd_congr2 _ _ _ _
      (by rw [matVec_length, inertia.length_matScale s1 M1,
        length_vecScale, matVec_length])
      (by rw [matVec_length, inertia.length_matScale s2 M2,
        length_vecScale, matVec_length])
      (inertia.matVec_matScale s1 M1 _)
      (inertia.matVec_matScale s2 M2 _)
  have h3 : poly.oneValue
      (matVec (inertia.matScale s3 (idMat o)) v)
      (vecScale (BPair.ofPos s3) v) :=
    poly.oneValue_trans
      (inertia.matVec_matScale s3 (idMat o) _)
      (vecScale_oneValue _ _ _ (inertia.matVec_idMat o _ hv))
  exact poly.oneValue_trans (poly.oneValue_symm h2)
    (poly.oneValue_trans (poly.oneValue_symm h1)
      (poly.oneValue_trans h0 h3))

/-- The lower solve identity at a column, scaled to the root's
clearing: the two summands collapse to the located scales. -/
private theorem loColDj {o : Nat} (Lw Et : Mat) (un ud lc dj : Pos)
    (n : Nat) (hLs : sqAt Lw o) (hEt : sqAt Et o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (v : List BPair) (hv : v.length = o) :
    poly.oneValue
      (vecAdd
        (vecScale (BPair.ofPos (posOfSucc n * (ud * dj)))
          (matVec Lw v))
        (vecScale (BPair.ofPos dj * BPair.ofPos (un * lc))
          (matVec Et v)))
      (vecScale (BPair.ofPos ((posOfSucc n * (ud * dj)) * lc)) v) := by
  have hI := solveCols Lw Et (posOfSucc n * ud) (un * lc)
    ((posOfSucc n * ud) * lc) hLs (rowsLen_of_sqAt hEt) hL v hv
  have hscaled := vecScale_oneValue (BPair.ofPos dj) _ _ hI
  rw [vecScale_vecAdd (BPair.ofPos dj) _ _,
    vecScale_vecScale (BPair.ofPos dj) (BPair.ofPos (posOfSucc n * ud)) _,
    vecScale_vecScale (BPair.ofPos dj) (BPair.ofPos (un * lc)) _,
    vecScale_vecScale (BPair.ofPos dj)
      (BPair.ofPos ((posOfSucc n * ud) * lc)) _]
    at hscaled
  have hsc1 : (BPair.ofPos dj * BPair.ofPos (posOfSucc n * ud)).oneValue
      (BPair.ofPos (posOfSucc n * (ud * dj))) := by
    refine BPair.oneValue_trans (BPair.ofPos_mul dj (posOfSucc n * ud)) ?_
    refine BPair.oneValue_of_eq (congrArg BPair.ofPos ?_)
    rw [mul_left_comm dj (posOfSucc n) ud, mul_comm dj ud]
  have hsc3 : (BPair.ofPos dj
      * BPair.ofPos ((posOfSucc n * ud) * lc)).oneValue
      (BPair.ofPos ((posOfSucc n * (ud * dj)) * lc)) := by
    refine BPair.oneValue_trans
      (BPair.ofPos_mul dj ((posOfSucc n * ud) * lc)) ?_
    refine BPair.oneValue_of_eq (congrArg BPair.ofPos ?_)
    rw [← mul_assoc dj (posOfSucc n * ud) lc,
      mul_left_comm dj (posOfSucc n) ud, mul_comm dj ud]
  refine poly.oneValue_trans
    (poly.oneValue_symm
      (vecAdd_congr2 _ _ _ _
        (by rw [length_vecScale, length_vecScale])
        rfl
        (vecScale_congr hsc1 _) (poly.oneValue_refl _))) ?_
  refine poly.oneValue_trans hscaled ?_
  exact vecScale_congr hsc3 _

/-- Clause (v)'s lower witness at a congruence column off the
kernel: the solve identity's read at the column is the witnessed
gap against the count, the split's diagonal read at the root. -/
theorem euc_lo_col {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud lc : Pos) (n : Nat) (Lw : Mat) (hLs : sqAt Lw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (j : Nat) (hj : j < o) (nj gj : BPair) (dj p g : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj))
    (hp : nj.oneValue (BPair.ofPos p))
    (hgap : un * p + g = posOfSucc n * (ud * dj)) :
    poly.oneValue
      (elim.vecScale (BPair.ofPos (posOfSucc n * (ud * dj)))
        (elim.matVec Lw (elim.matVec T.val (elim.idRow o j))))
      (elim.vecScale (BPair.ofPos (g * lc))
        (elim.matVec T.val (elim.idRow o j))) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hEt : sqAt Et o := hd.1
  have hvl : (matVec T.val (elim.idRow o j)).length = o := by
    rw [matVec_length, hTl]
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hloc := loColDj Lw Et un ud lc dj n hLs hEt hL _ hvl
  -- the middle summand reads through the eigencolumn
  have hmid : poly.oneValue
      (vecScale (BPair.ofPos dj * BPair.ofPos (un * lc))
        (matVec Et (matVec T.val (elim.idRow o j))))
      (vecScale (BPair.ofPos ((un * lc) * p))
        (matVec T.val (elim.idRow o j))) := by
    rw [show BPair.ofPos dj * BPair.ofPos (un * lc)
        = BPair.ofPos (un * lc) * BPair.ofPos dj from BPair.mul_comm _ _,
      ← vecScale_vecScale (BPair.ofPos (un * lc)) (BPair.ofPos dj) _]
    refine poly.oneValue_trans
      (vecScale_oneValue (BPair.ofPos (un * lc)) _ _
        (split.eigenColumn Et (idMat o) T Tw l j nj gj dj hd hjl hroot)) ?_
    refine poly.oneValue_trans
      (vecScale_oneValue (BPair.ofPos (un * lc)) _ _
        (vecScale_congr hp _)) ?_
    refine poly.oneValue_trans
      (vecScale_oneValue (BPair.ofPos (un * lc)) _ _
        (vecScale_oneValue (BPair.ofPos p) _ _
          (inertia.matVec_idMat o _ hvl))) ?_
    rw [vecScale_vecScale (BPair.ofPos (un * lc)) (BPair.ofPos p) _]
    exact vecScale_congr (BPair.ofPos_mul (un * lc) p) _
  have hIdj : poly.oneValue
      (vecAdd
        (vecScale (BPair.ofPos (posOfSucc n * (ud * dj)))
          (matVec Lw (matVec T.val (elim.idRow o j))))
        (vecScale (BPair.ofPos ((un * lc) * p))
          (matVec T.val (elim.idRow o j))))
      (vecScale (BPair.ofPos ((posOfSucc n * (ud * dj)) * lc))
        (matVec T.val (elim.idRow o j))) :=
    poly.oneValue_trans
      (poly.oneValue_symm
        (vecAdd_congr2 _ _ _ _ rfl
          (by rw [length_vecScale, length_vecScale, matVec_length,
            sqAt_len hEt, matVec_length, hTl])
          (poly.oneValue_refl _) hmid)) hloc
  -- close: split the right side at the gap and cancel
  have hofp : (BPair.ofPos ((posOfSucc n * (ud * dj)) * lc)).oneValue
      (BPair.ofPos ((un * lc) * p) + BPair.ofPos (g * lc)) := by
    rw [show (posOfSucc n * (ud * dj)) * lc = (un * lc) * p + g * lc from by
      rw [mul_assoc un lc p, mul_comm lc p, ← mul_assoc un p lc,
        ← right_distrib, hgap]]
    exact BPair.ofPos_add ((un * lc) * p) (g * lc)
  have hsplit : poly.oneValue
      (vecScale (BPair.ofPos ((posOfSucc n * (ud * dj)) * lc))
        (matVec T.val (elim.idRow o j)))
      (vecAdd
        (vecScale (BPair.ofPos (g * lc)) (matVec T.val (elim.idRow o j)))
        (vecScale (BPair.ofPos ((un * lc) * p))
          (matVec T.val (elim.idRow o j)))) := by
    refine poly.oneValue_trans (vecScale_congr hofp _) ?_
    rw [vecScale_add (BPair.ofPos ((un * lc) * p)) (BPair.ofPos (g * lc)) _]
    exact poly.oneValue_of_eq (elim.vecAdd_comm _ _)
  refine vecAdd_cancel_right _ _
    (vecScale (BPair.ofPos ((un * lc) * p)) (matVec T.val (elim.idRow o j)))
    (by rw [length_vecScale, length_vecScale, matVec_length,
      sqAt_len hLs, matVec_length, hTl])
    (by rw [length_vecScale, length_vecScale, matVec_length,
      sqAt_len hLs, matVec_length, hTl])
    (poly.oneValue_trans hIdj hsplit)

/-- Clause (v)'s lower witness at a kernel column: the electric
summand reads the unit tail and the solve identity's read is the
column kept whole, the full gap's instance. -/
theorem euc_lo_col_ker {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud lc : Pos) (n : Nat) (Lw : Mat) (hLs : sqAt Lw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (j : Nat) (hj : j < o) (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj))
    (hker : nj.oneValue BPair.unit) :
    poly.oneValue
      (elim.vecScale (BPair.ofPos (posOfSucc n * (ud * dj)))
        (elim.matVec Lw (elim.matVec T.val (elim.idRow o j))))
      (elim.vecScale (BPair.ofPos ((posOfSucc n * (ud * dj)) * lc))
        (elim.matVec T.val (elim.idRow o j))) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hEt : sqAt Et o := hd.1
  have hvl : (matVec T.val (elim.idRow o j)).length = o := by
    rw [matVec_length, hTl]
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hloc := loColDj Lw Et un ud lc dj n hLs hEt hL _ hvl
  have hmidU : poly.unitTail
      (vecScale (BPair.ofPos dj * BPair.ofPos (un * lc))
        (matVec Et (matVec T.val (elim.idRow o j)))) := by
    rw [show BPair.ofPos dj * BPair.ofPos (un * lc)
        = BPair.ofPos (un * lc) * BPair.ofPos dj from BPair.mul_comm _ _,
      ← vecScale_vecScale (BPair.ofPos (un * lc)) (BPair.ofPos dj) _]
    refine unitTail_vecScale (BPair.ofPos (un * lc)) _ ?_
    refine poly.unitTail_oneValue_right ?_
      (poly.oneValue_symm
        (split.eigenColumn Et (idMat o) T Tw l j nj gj dj hd hjl hroot))
    refine poly.unitTail_oneValue_right ?_
      (poly.oneValue_symm (vecScale_congr hker _))
    exact unitTail_vecScale_unit (BPair.oneValue_refl BPair.unit) _
  have habs : poly.oneValue
      (vecScale (BPair.ofPos (posOfSucc n * (ud * dj)))
        (matVec Lw (matVec T.val (elim.idRow o j))))
      (vecAdd
        (vecScale (BPair.ofPos (posOfSucc n * (ud * dj)))
          (matVec Lw (matVec T.val (elim.idRow o j))))
        (vecScale (BPair.ofPos dj * BPair.ofPos (un * lc))
          (matVec Et (matVec T.val (elim.idRow o j))))) := by
    rw [vecAdd_eq_polyAdd _ _
      (by rw [length_vecScale, length_vecScale, matVec_length,
        sqAt_len hLs, matVec_length, sqAt_len hEt])]
    exact poly.oneValue_symm (poly.add_unitTail _ hmidU)
  exact poly.oneValue_trans habs hloc


/-- The coordinate read at a congruence column: the determinant's
multiple of a vector's pairing against the column is the column's
gram scale against the vector's own coordinate, the adjugate action
read at the congruated gram's diagonal. -/
private theorem colCoord {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (k : Nat) (hk : k < o) (nk gk : BPair) (dk : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l k
      = (nk, dk, gk))
    (x : List BPair) (hx : x.length = o) :
    (minor T.val * dotP (matVec T.val (elim.idRow o k)) x).oneValue
      ((gk * BPair.ofPos dk).norm
        * ground.getAt BPair.unit (matVec Tw.val x) k) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hTwl : Tw.val.length = o := SqMat.rows Tw
  have hlen : l.length = o := split.rootLen Et T Tw l hd
  have hcl : (matVec Tw.val x).length = o := by
    rw [matVec_length, hTwl]
  have hdf := split.diagFold (idMat o) T _
    (idMat_len o) (idMat_rows o)
    (by rw [ground.length_map]; exact hlen)
    (split.gramMat Et T Tw l hd)
    (elim.idRow o k) (matVec Tw.val x) (length_idRow o k) hcl
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (dotP_vecScale_right _ x (minor T.val))) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_right _ _ _
      (poly.oneValue_symm (split.adjAct Et T Tw l hd x hx))) ?_
  refine BPair.oneValue_trans
    (dotP_oneValue_right _ _ _
      (poly.oneValue_symm
        (inertia.matVec_idMat o _ (by rw [matVec_length, hTl])))) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (dotN_read (matVec T.val (elim.idRow o k))
      (matVec (idMat o) (matVec T.val (matVec Tw.val x))))) ?_
  refine BPair.oneValue_trans hdf ?_
  refine BPair.oneValue_trans
    (dotP_oneIndex _ _ k
      (by rw [ground.length_map, hlen,
        ground.length_zipWith (· * ·) _ _ o (length_idRow o k) hcl])
      (by rw [ground.length_zipWith (· * ·) _ _ o
          (length_idRow o k) hcl]
          exact hk)
      (fun q hq hne => by
        rw [ground.length_zipWith (· * ·) _ _ o
          (length_idRow o k) hcl] at hq
        rw [ground.getAt_zipWith BPair.unit BPair.unit BPair.unit
            (· * ·) _ _ q (by rw [length_idRow]; exact hq)
            (by rw [hcl]; exact hq),
          getAt_idRow o k q hq, if_neg hne]
        exact BPair.unit_mul _)) ?_
  rw [ground.getAt_map (BPair.unit, Pos.one, BPair.unit) BPair.unit
      (fun r => (r.2.2 * BPair.ofPos r.2.1).norm) l k
      (by rw [hlen]; exact hk),
    hroot,
    ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
      _ _ k (by rw [length_idRow]; exact hk) (by rw [hcl]; exact hk),
    getAt_idRow o k k hk, if_pos rfl]
  refine BPair.mul_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
  exact BPair.mul_ofNat_one _

/-- The upper witness's pairing at a congruence column: the solve
identity paired against the column collects the column root's own
scale, the transpose walk at the split's symmetry. -/
private theorem hiPair {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud vc : Pos) (n : Nat) (Vw : Mat) (hVs : sqAt Vw o)
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (j k : Nat) (hkl : k < l.length)
    (nk gk : BPair) (dk : Pos)
    (hrootk : ground.getAt (BPair.unit, Pos.one, BPair.unit) l k
      = (nk, dk, gk)) :
    ((BPair.ofPos (dk * (posOfSucc n * ud)) + nk.scale un)
        * dotP (matVec T.val (elim.idRow o k))
            (matVec Vw (matVec T.val (elim.idRow o j)))).oneValue
      (BPair.ofPos (dk * ((posOfSucc n * ud) * vc))
        * dotP (matVec T.val (elim.idRow o k))
            (matVec T.val (elim.idRow o j))) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hEt : sqAt Et o := hd.1
  have hEtl : Et.length = o := sqAt_len hEt
  have hEtr : rowsLen o Et := rowsLen_of_sqAt hEt
  have hVl : Vw.length = o := sqAt_len hVs
  have hVr : rowsLen o Vw := rowsLen_of_sqAt hVs
  have hvl : (matVec T.val (elim.idRow o j)).length = o := by
    rw [matVec_length, hTl]
  have hkvl : (matVec T.val (elim.idRow o k)).length = o := by
    rw [matVec_length, hTl]
  have hzl : (matVec Vw (matVec T.val (elim.idRow o j))).length = o := by
    rw [matVec_length, hVl]
  have hEzl : (matVec Et
      (matVec Vw (matVec T.val (elim.idRow o j)))).length = o := by
    rw [matVec_length, hEtl]
  have hEV : rowsLen o (matMul Et Vw) :=
    rowsLen_cast (transposeLen Vw hVr hVl) (rowsLen_matMul Et Vw)
  have hI0 := solveCols Vw (matMul Et Vw) (posOfSucc n * ud) un
    ((posOfSucc n * ud) * vc) hVs hEV hV _ hvl
  -- the applied solve identity at the j-th column, the composed
  -- summand read through the product's action
  have hI : poly.oneValue
      (vecAdd
        (vecScale (BPair.ofPos (posOfSucc n * ud))
          (matVec Vw (matVec T.val (elim.idRow o j))))
        (vecScale (BPair.ofPos un)
          (matVec Et (matVec Vw (matVec T.val (elim.idRow o j))))))
      (vecScale (BPair.ofPos ((posOfSucc n * ud) * vc))
        (matVec T.val (elim.idRow o j))) :=
    poly.oneValue_trans
      (poly.oneValue_symm
        (vecAdd_congr2 _ _ _ _ rfl
          (by rw [length_vecScale, length_vecScale, matVec_length,
            matVec_length, length_matMul])
          (poly.oneValue_refl _)
          (vecScale_oneValue _ _ _
            (matVec_matMul Et Vw o hVr _ hvl)))) hI0
  -- the k-th pairing of the identity
  have hpair : (BPair.ofPos (posOfSucc n * ud)
        * dotP (matVec T.val (elim.idRow o k))
            (matVec Vw (matVec T.val (elim.idRow o j)))
      + BPair.ofPos un
        * dotP (matVec T.val (elim.idRow o k))
            (matVec Et (matVec Vw (matVec T.val (elim.idRow o j))))).oneValue
      (BPair.ofPos ((posOfSucc n * ud) * vc)
        * dotP (matVec T.val (elim.idRow o k))
            (matVec T.val (elim.idRow o j))) := by
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_symm (dotP_vecScale_right _ _ _))
        (BPair.oneValue_symm (dotP_vecScale_right _ _ _))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (dotP_vecAdd_right _ _ _
          (by rw [length_vecScale, length_vecScale, hzl, hEzl]))) ?_
    refine BPair.oneValue_trans
      (dotP_oneValue_right _ _ _ hI) ?_
    exact dotP_vecScale_right _ _ _
  -- the electric pairing walks across the symmetry to the root
  have hwalk : (BPair.ofPos dk
        * dotP (matVec T.val (elim.idRow o k))
            (matVec Et (matVec Vw (matVec T.val (elim.idRow o j))))).oneValue
      (nk * dotP (matVec T.val (elim.idRow o k))
        (matVec Vw (matVec T.val (elim.idRow o j)))) := by
    have hd1 : (dotP (matVec T.val (elim.idRow o k))
        (matVec Et (matVec Vw (matVec T.val (elim.idRow o j))))).oneValue
        (dotP (matVec Vw (matVec T.val (elim.idRow o j)))
          (matVec Et (matVec T.val (elim.idRow o k)))) := by
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (dotP_comm _ _)) ?_
      refine BPair.oneValue_trans
        (dotP_matVec_transpose o Et _ _ hEtr hzl
          (by rw [hkvl, hEtl])) ?_
      exact dotP_oneValue_right _ _ _
        (matVec_matOne _ _ _ (split.sym_of_diagRead Et T Tw l hd))
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos dk)) hd1) ?_
    refine BPair.oneValue_trans
      (split.pairEigen Et T Tw l hd k hkl nk gk dk hrootk _) ?_
    exact BPair.mul_congr (BPair.oneValue_refl nk)
      (BPair.oneValue_of_eq (dotP_comm _ _))
  -- scale the pairing by the clearing and collect
  have hscaled := BPair.mul_congr
    (BPair.oneValue_refl (BPair.ofPos dk)) hpair
  rw [BPair.left_distrib (BPair.ofPos dk) _ _] at hscaled
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_symm (BPair.ofPos_mul dk (posOfSucc n * ud)))
          (BPair.oneValue_refl _))
        (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)))
      (BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_symm (BPair.ofPos_scale un nk))
          (BPair.oneValue_refl _))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos un))
              (BPair.oneValue_symm hwalk))
            (BPair.oneValue_trans
              (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm)
              (BPair.oneValue_trans
                (BPair.mul_congr
                  (BPair.oneValue_of_eq (BPair.mul_comm _ _))
                  (BPair.oneValue_refl _))
                (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)))))))) ?_
  refine BPair.oneValue_trans hscaled ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
  exact BPair.mul_congr (BPair.ofPos_mul dk ((posOfSucc n * ud) * vc))
    (BPair.oneValue_refl _)

/-- The certificate arm's collected scale sits off the unit class
at either arm. -/
private theorem armScaleOff {un ud N : Pos} {nk : BPair}
    {dk pk : Pos}
    (harm : nk.oneValue BPair.unit
      ∨ nk.oneValue (BPair.ofPos pk)) :
    ¬ (BPair.ofPos (dk * (N * ud)) + nk.scale un).oneValue
      BPair.unit := by
  refine harm.elim (fun hker => ?_) (fun hpos => ?_)
  · intro hu
    have h1 : (BPair.ofPos (dk * (N * ud))).oneValue BPair.unit := by
      refine BPair.oneValue_trans ?_ hu
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.scale_congr un hker)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (ground.unitScale un))) ?_
      exact BPair.add_unit _
    exact BPair.ofPos_off _ h1
  · intro hu
    have h1 : (BPair.ofPos (dk * (N * ud) + un * pk)).oneValue
        BPair.unit := by
      refine BPair.oneValue_trans ?_ hu
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.scale_congr un hpos)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.scale_ofPos _ un)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_of_eq
            (congrArg BPair.ofPos (mul_comm _ un)))) ?_
      exact BPair.oneValue_symm (BPair.ofPos_add _ _)
    exact BPair.ofPos_off _ h1

/-- Clause (v)'s upper witness at a congruence column off the
kernel: the solve identity's read at the column is the count
against the count joined to the root's crossing, the split's
diagonal read at the root, the certificate fold clearing every
further coordinate. -/
theorem euc_hi_col {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud vc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (harm : ∀ k, k < l.length →
      ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1).oneValue
          BPair.unit
        ∨ ((ground.getAt (BPair.unit, Pos.one,
            BPair.unit) l k).1).oneValue
            (BPair.ofPos (ground.getAt (Pos.one, Pos.one) ws k).1))
    (Vw : Mat) (hVs : sqAt Vw o)
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (j : Nat) (hj : j < o) (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    poly.oneValue
      (elim.vecScale
        (BPair.ofPos (posOfSucc n * (ud * dj)) + nj.scale un)
        (elim.matVec Vw (elim.matVec T.val (elim.idRow o j))))
      (elim.vecScale (BPair.ofPos ((posOfSucc n * (ud * dj)) * vc))
        (elim.matVec T.val (elim.idRow o j))) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hTwl : Tw.val.length = o := SqMat.rows Tw
  have hVl : Vw.length = o := sqAt_len hVs
  have hlen : l.length = o := split.rootLen Et T Tw l hd
  have hjl : j < l.length := by rw [hlen]; exact hj
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  have hvl : (matVec T.val (elim.idRow o j)).length = o := by
    rw [matVec_length, hTl]
  have hzl : (matVec Vw (matVec T.val (elim.idRow o j))).length = o := by
    rw [matVec_length, hVl]
  have hcl : (matVec Tw.val
      (matVec Vw (matVec T.val (elim.idRow o j)))).length = o := by
    rw [matVec_length, hTwl]
  -- the coordinates off the pivot key read the unit
  have hoff : ∀ k, k < o → ¬ k = j →
      (ground.getAt BPair.unit
        (matVec Tw.val
          (matVec Vw (matVec T.val (elim.idRow o j)))) k).oneValue
        BPair.unit := by
    intro k hk hne
    have hkl : k < l.length := by rw [hlen]; exact hk
    have hrk : ground.getAt (BPair.unit, Pos.one, BPair.unit) l k
        = ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).2.1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).2.2) :=
      rfl
    have hak := harm k hkl
    have hgk : BPair.unit
        < (ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).2.2 :=
      split.scalePos Et T Tw l hd k hkl _ _ _ hrk
    -- the scale is off the unit class at either arm
    have hSoff : ¬ (BPair.ofPos
          ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).2.1
            * (posOfSucc n * ud))
        + ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1).scale
            un).oneValue BPair.unit := armScaleOff hak
    -- the pairing vanishes: the paired identity at the unit gram entry
    have hq := hiPair Et T Tw l hd un ud vc n Vw hVs hV j k hkl _ _ _ hrk
    have hGoff := split.gramOff Et T Tw l hd k j hk hj hne
    have hqu : ((BPair.ofPos
          ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).2.1
            * (posOfSucc n * ud))
        + ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).1).scale
            un)
        * dotP (matVec T.val (elim.idRow o k))
            (matVec Vw (matVec T.val (elim.idRow o j)))).oneValue
        BPair.unit := by
      refine BPair.oneValue_trans hq ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) hGoff) ?_
      exact BPair.mul_unit _
    have hqk : (dotP (matVec T.val (elim.idRow o k))
        (matVec Vw (matVec T.val (elim.idRow o j)))).oneValue
        BPair.unit :=
      ((BPair.mul_unit_iff _ _).mp hqu).elim
        (fun h1 => absurd h1 hSoff) id
    -- the coordinate read kills the entry
    have hcc := colCoord Et T Tw l hd k hk _ _ _ hrk
      (matVec Vw (matVec T.val (elim.idRow o j))) hzl
    have hwoff : ¬ (((ground.getAt (BPair.unit, Pos.one, BPair.unit)
          l k).2.2
        * BPair.ofPos
          (ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).2.1).norm
          ).oneValue BPair.unit :=
      ground.offOfUnitLt
        (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
          (BPair.oneValue_symm (BPair.norm_oneValue _))
          (ground.unitLtMul hgk (ground.unitLtOfPos _)))
    have hwu : (((ground.getAt (BPair.unit, Pos.one, BPair.unit)
          l k).2.2
        * BPair.ofPos
          (ground.getAt (BPair.unit, Pos.one, BPair.unit) l k).2.1).norm
        * ground.getAt BPair.unit
            (matVec Tw.val
              (matVec Vw (matVec T.val (elim.idRow o j)))) k).oneValue
        BPair.unit := by
      refine BPair.oneValue_trans (BPair.oneValue_symm hcc) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) hqk) ?_
      exact BPair.mul_unit _
    exact ((BPair.mul_unit_iff _ _).mp hwu).elim
      (fun h1 => absurd h1 hwoff) id
  -- the pivot coordinate carries the solve's value
  have hq_j := hiPair Et T Tw l hd un ud vc n Vw hVs hV j j hjl nj gj dj
    hroot
  have hGdiag := split.gramDiag Et T Tw l hd j hj nj gj dj hroot
  have hcc_j := colCoord Et T Tw l hd j hj nj gj dj hroot
    (matVec Vw (matVec T.val (elim.idRow o j))) hzl
  have hgj : BPair.unit < gj := by
    have h := split.scalePos Et T Tw l hd j hjl nj gj dj hroot
    exact h
  have hwoffj : ¬ ((gj * BPair.ofPos dj).norm).oneValue BPair.unit :=
    ground.offOfUnitLt
      (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
        (BPair.oneValue_symm (BPair.norm_oneValue _))
        (ground.unitLtMul hgj (ground.unitLtOfPos dj)))
  have hSc : ((BPair.ofPos (dj * (posOfSucc n * ud)) + nj.scale un)
      * ground.getAt BPair.unit
          (matVec Tw.val
            (matVec Vw (matVec T.val (elim.idRow o j)))) j).oneValue
      (minor T.val * BPair.ofPos (dj * ((posOfSucc n * ud) * vc))) := by
    refine ground.mulCancel hwoffj ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm hcc_j)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (minor T.val)) hq_j) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (minor T.val))
        (BPair.mul_congr (BPair.oneValue_refl _) hGdiag)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    exact BPair.mul_congr
      (BPair.oneValue_symm (BPair.norm_oneValue _))
      (BPair.oneValue_of_eq (BPair.mul_comm _ _))
  -- the coordinate vector is the pivot coordinate's own column
  have hcvec : poly.oneValue
      (matVec Tw.val (matVec Vw (matVec T.val (elim.idRow o j))))
      (vecScale
        (ground.getAt BPair.unit
          (matVec Tw.val
            (matVec Vw (matVec T.val (elim.idRow o j)))) j)
        (elim.idRow o j)) := by
    refine poly.oneValue_of_entries _ _
      (by rw [hcl, length_vecScale, length_idRow]) ?_
    intro i hi
    rw [hcl] at hi
    rw [getAt_vecScale _ _ i (by rw [length_idRow]; exact hi),
      getAt_idRow o j i hi]
    by_cases hij : i = j
    · rw [if_pos hij, hij]
      exact BPair.oneValue_symm (BPair.mul_ofNat_one _)
    · rw [if_neg hij]
      refine BPair.oneValue_trans (hoff i hi hij) ?_
      exact BPair.oneValue_symm (BPair.mul_unit _)
  have hTc : poly.oneValue
      (vecScale (minor T.val)
        (matVec Vw (matVec T.val (elim.idRow o j))))
      (vecScale
        (ground.getAt BPair.unit
          (matVec Tw.val
            (matVec Vw (matVec T.val (elim.idRow o j)))) j)
        (matVec T.val (elim.idRow o j))) := by
    refine poly.oneValue_trans
      (poly.oneValue_symm (split.adjAct Et T Tw l hd _ hzl)) ?_
    refine poly.oneValue_trans
      (matVec_congr T.val _ _ hcvec) ?_
    exact matVec_vecScale_free T.val _ _
  -- close at the determinant's clearing
  refine oneValue_unscale (minor T.val) hdet _ _ ?_
  rw [vecScale_vecScale, vecScale_vecScale,
    BPair.mul_comm (minor T.val)
      (BPair.ofPos (posOfSucc n * (ud * dj)) + nj.scale un),
    ← vecScale_vecScale]
  refine poly.oneValue_trans
    (vecScale_oneValue _ _ _ hTc) ?_
  rw [vecScale_vecScale]
  have hSS : (BPair.ofPos (posOfSucc n * (ud * dj))
      + nj.scale un).oneValue
      (BPair.ofPos (dj * (posOfSucc n * ud)) + nj.scale un) := by
    refine BPair.add_congr
      (BPair.oneValue_of_eq (congrArg BPair.ofPos ?_))
      (BPair.oneValue_refl _)
    rw [mul_left_comm dj (posOfSucc n) ud, mul_comm dj ud]
  refine poly.oneValue_trans
    (vecScale_congr
      (BPair.oneValue_trans
        (BPair.mul_congr hSS (BPair.oneValue_refl _))
        (BPair.oneValue_trans hSc
          (BPair.mul_congr (BPair.oneValue_refl (minor T.val))
            (BPair.oneValue_of_eq (congrArg BPair.ofPos
              (by rw [← mul_assoc dj (posOfSucc n * ud) vc,
                mul_left_comm dj (posOfSucc n) ud,
                mul_comm dj ud])))))) _) ?_
  exact poly.oneValue_refl _

/-- The iterated product's read at a cleared eigencolumn: the
column read's power at every count, the clearing and the value each
at their own power. -/
theorem matPow_col {o : Nat} (M : Mat) (hMs : sqAt M o)
    (v : List BPair) (hv : v.length = o) (cn cd : BPair)
    (hcol : poly.oneValue (elim.vecScale cd (elim.matVec M v))
      (elim.vecScale cn v)) :
    ∀ k : Nat,
    poly.oneValue
      (elim.vecScale (ground.bpow cd k)
        (elim.matVec (matPow M o k) v))
      (elim.vecScale (ground.bpow cn k) v)
  | 0 => by
    show poly.oneValue
      (elim.vecScale (BPair.ofPos .one) (elim.matVec (idMat o) v))
      (elim.vecScale (BPair.ofPos .one) v)
    exact vecScale_oneValue _ _ _ (inertia.matVec_idMat o v hv)
  | k + 1 => by
    have hPr : rowsLen o (matPow M o k) :=
      rowsLen_matPow M o (sqAt_len hMs) k
    refine poly.oneValue_trans
      (vecScale_congr (BPair.norm_oneValue _) _) ?_
    refine poly.oneValue_trans
      (vecScale_oneValue _ _ _
        (matVec_matMul M (matPow M o k) o hPr v hv)) ?_
    rw [← vecScale_vecScale cd (ground.bpow cd k) _]
    refine poly.oneValue_trans
      (vecScale_oneValue cd _ _
        (poly.oneValue_symm
          (matVec_vecScale_free M (ground.bpow cd k) _))) ?_
    refine poly.oneValue_trans
      (vecScale_oneValue cd _ _
        (matVec_congr M _ _ (matPow_col M hMs v hv cn cd hcol k))) ?_
    refine poly.oneValue_trans
      (vecScale_oneValue cd _ _
        (matVec_vecScale_free M (ground.bpow cn k) v)) ?_
    rw [vecScale_vecScale cd (ground.bpow cn k) _,
      BPair.mul_comm cd (ground.bpow cn k),
      ← vecScale_vecScale (ground.bpow cn k) cd _]
    refine poly.oneValue_trans
      (vecScale_oneValue (ground.bpow cn k) _ _ hcol) ?_
    rw [vecScale_vecScale (ground.bpow cn k) cn v,
      BPair.mul_comm (ground.bpow cn k) cn]
    exact poly.oneValue_symm
      (vecScale_congr (BPair.norm_oneValue _) v)

/-- The lower witness's column read at either certificate arm: the
count's clearing against the stated gap value, the two arms one
display at the fold's own gap. -/
private theorem loColArm {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud kn kd lc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd (posOfSucc n) l ws)
    (Lw : Mat) (hLs : sqAt Lw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (j : Nat) (hj : j < o) :
    poly.oneValue
      (elim.vecScale
        (BPair.ofPos (posOfSucc n
          * (ud * (ground.getAt (BPair.unit, Pos.one, BPair.unit)
              l j).2.1)))
        (elim.matVec Lw (elim.matVec T.val (elim.idRow o j))))
      (elim.vecScale
        (BPair.ofPos ((ground.getAt (Pos.one, Pos.one) ws j).2 * lc))
        (elim.matVec T.val (elim.idRow o j))) := by
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hrj : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1,
         (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1,
         (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2) := rfl
  have hwj : ground.getAt (Pos.one, Pos.one) ws j
      = ((ground.getAt (Pos.one, Pos.one) ws j).1,
         (ground.getAt (Pos.one, Pos.one) ws j).2) := rfl
  have harm := eucRead_at un ud kn kd (posOfSucc n) l ws hw j hjl
    _ _ _ hrj _ _ hwj
  refine harm.elim (fun hker => ?_) (fun hpos => ?_)
  · rw [hker.2]
    exact euc_lo_col_ker Et T Tw l hd un ud lc n Lw hLs hL j hj _ _ _
      hrj hker.1
  · exact euc_lo_col Et T Tw l hd un ud lc n Lw hLs hL j hj _ _ _ _ _
      hrj hpos.1 hpos.2.1

/-- The scalar polarization: the weighted cross product's double at
or below the weighted squares' join, the cross-square comparison at
the product's unit. -/
private theorem scalarPolar (a b X Y : BPair) :
    ((a * b) * (X * Y)).scale 2
      ≤ (a * a) * (X * X) + (b * b) * (Y * Y) := by
  refine ground.leB_congr ?_ ?_
    (ground.leB_crossSq
      (ground.leB_of_lt (ground.unitLtOfPos Pos.one)) (a * X) (b * Y))
  · refine BPair.oneValue_trans (BPair.ofPos_one_mul _)
      (BPair.oneValue_of_eq ?_)
    rw [BPair.mul_mul_mul_comm a X b Y, ← BPair.scale_two]
  · refine BPair.oneValue_trans (BPair.ofPos_one_mul _)
      (BPair.oneValue_of_eq ?_)
    rw [BPair.mul_mul_mul_comm a X a X, BPair.mul_mul_mul_comm b Y b Y]

/-- One term's price at the bracket: the weighted difference term
sits below the polarization against the gram scale at the width. -/
private theorem termChain (ab R dD wl z : BPair) (Wn Wd : Pos)
    (hpos : BPair.unit ≤ dD) (hcap : dD.scale Wd ≤ wl.scale Wn)
    (hRpos : BPair.unit ≤ R)
    (hpol : (ab * z).scale 2 ≤ R) :
    ((ab * (dD * z)).scale (2 * Wd)) ≤ ((R * wl).scale Wn) := by
  have h1 : (dD * ((ab * z).scale 2)).scale Wd
      ≤ (dD * R).scale Wd :=
    ground.leB_scale (ground.leB_mulR hpos hpol) Wd
  have h2 : (dD * R).scale Wd = (dD.scale Wd) * R := by
    rw [BPair.mul_comm dD R, ← BPair.mul_scale R dD Wd,
      BPair.mul_comm R (dD.scale Wd)]
  have h3 : (dD.scale Wd) * R ≤ (wl.scale Wn) * R := by
    rw [BPair.mul_comm (dD.scale Wd) R, BPair.mul_comm (wl.scale Wn) R]
    exact ground.leB_mulR hRpos hcap
  have h4 : (wl.scale Wn) * R = (R * wl).scale Wn := by
    rw [BPair.mul_comm (wl.scale Wn) R, ← BPair.mul_scale R wl Wn]
  have hL : (ab * (dD * z)).scale (2 * Wd)
      = (dD * ((ab * z).scale 2)).scale Wd := by
    rw [show ab * (dD * z) = dD * (ab * z) from by
        rw [← BPair.mul_assoc, BPair.mul_comm ab dD, BPair.mul_assoc],
      ← BPair.scale_scale (dD * (ab * z)) 2 Wd,
      BPair.mul_scale dD (ab * z) 2]
  rw [hL, ← h4]
  refine ground.leB_trans h1 ?_
  rw [h2]
  exact h3

/-- The width's pair read at the cleared displays: the two-member
site's scaled comparison from the cross-multiplied ground read. -/
private theorem pairWidthLe (a b Jp : Pos) (Wn Wd : Pos)
    (h : a * Wd ≤ Jp * Wn + b * Wd) :
    (BPair.ofPos a + (BPair.ofPos b).swap).scale Wd
      ≤ (BPair.ofPos Jp).scale Wn := by
  show (a + Pos.one + Pos.one) * Wd + Pos.one * Wn
    ≤ (Jp + Pos.one) * Wn + (Pos.one + (b + Pos.one)) * Wd
  rw [ground.right_distrib (a + Pos.one) Pos.one Wd,
    ground.right_distrib a Pos.one Wd,
    ground.right_distrib Jp Pos.one Wn,
    ground.right_distrib Pos.one (b + Pos.one) Wd,
    ground.right_distrib b Pos.one Wd,
    ground.one_mul Wd, ground.one_mul Wn]
  have hR : Wn + (Wd + (b * Wd + Wd)) = b * Wd + (Wd + (Wd + Wn)) := by
    rw [ground.add_left_comm Wn Wd (b * Wd + Wd),
      ground.add_left_comm Wn (b * Wd) Wd,
      ground.add_comm Wn Wd,
      ground.add_left_comm Wd (b * Wd) (Wd + Wn)]
  rw [ground.add_assoc (a * Wd) Wd Wd,
    ground.add_assoc (a * Wd) (Wd + Wd) Wn,
    ground.add_assoc Wd Wd Wn,
    ground.add_assoc (Jp * Wn) Wn (Wd + (b * Wd + Wd)),
    hR,
    ← ground.add_assoc (Jp * Wn) (b * Wd) (Wd + (Wd + Wn))]
  exact ground.posLeAdd h (Or.inl rfl)

/-- The bracket's close at one root: from the two pinned diagonal
entries and the arm's ground comparisons, the difference sits on
the positive side and within the width against the gram scale. -/
private theorem bracketClose (dsV dsL Wj : BPair)
    (C Dg E lc vc : Pos) (n : Nat) (Wn Wd : Pos)
    (hWpos : BPair.unit < Wj)
    (hVpin : (BPair.ofPos (Pos.pow E (n + 1)) * dsV).oneValue
      (BPair.ofPos (Pos.pow (C * vc) (n + 1)) * Wj))
    (hLpin : (BPair.ofPos (Pos.pow C (n + 1)) * dsL).oneValue
      (BPair.ofPos (Pos.pow (Dg * lc) (n + 1)) * Wj))
    (hloPos : Pos.pow Dg (n + 1) * Pos.pow E (n + 1)
      ≤ Pos.pow C (n + 1) * Pos.pow C (n + 1))
    (hwidPos : Pos.pow C (n + 1) * Pos.pow C (n + 1) * Wd
      ≤ Pos.pow E (n + 1) * Pos.pow C (n + 1) * Wn
        + Pos.pow E (n + 1) * Pos.pow Dg (n + 1) * Wd) :
    (BPair.unit ≤ BPair.ofPos (Pos.pow lc (n + 1)) * dsV
        + (BPair.ofPos (Pos.pow vc (n + 1)) * dsL).swap)
    ∧ ((BPair.ofPos (Pos.pow lc (n + 1)) * dsV
        + (BPair.ofPos (Pos.pow vc (n + 1)) * dsL).swap).scale Wd
      ≤ (Wj.norm).scale (Wn * Pos.pow (lc * vc) (n + 1))) := by
  have hJlt : BPair.unit
      < BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1)) :=
    ground.unitLtOfPos _
  have hWle : BPair.unit ≤ Wj := ground.leB_of_lt hWpos
  -- the two entries at the joint clearing, the solves' own clearings
  -- riding outside
  have a0 : (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
      * dsL).oneValue
      (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow (Dg * lc) (n + 1))
        * Wj) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_symm (BPair.ofPos_mul _ _))
        (BPair.oneValue_refl dsL)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hLpin) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
    exact BPair.mul_congr (BPair.ofPos_mul _ _) (BPair.oneValue_refl Wj)
  have b0 : (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
      * dsV).oneValue
      (BPair.ofPos (Pos.pow C (n + 1) * Pos.pow (C * vc) (n + 1))
        * Wj) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_of_eq
          (congrArg BPair.ofPos (mul_comm _ _)))
        (BPair.oneValue_refl dsV)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_symm (BPair.ofPos_mul _ _))
        (BPair.oneValue_refl dsV)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) hVpin) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
    exact BPair.mul_congr (BPair.ofPos_mul _ _) (BPair.oneValue_refl Wj)
  have a1 : (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
      * (BPair.ofPos (Pos.pow vc (n + 1)) * dsL)).oneValue
      (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
        * (Pos.pow E (n + 1) * Pos.pow Dg (n + 1))) * Wj) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) a0) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.ofPos_mul _ _)
        (BPair.oneValue_refl Wj)) ?_
    refine BPair.mul_congr
      (BPair.oneValue_of_eq (congrArg BPair.ofPos ?_))
      (BPair.oneValue_refl Wj)
    rw [Pos.pow_mul Dg lc (n + 1), Pos.pow_mul lc vc (n + 1),
      mul_comm (Pos.pow Dg (n + 1)) (Pos.pow lc (n + 1)),
      mul_left_comm (Pos.pow E (n + 1)) (Pos.pow lc (n + 1))
        (Pos.pow Dg (n + 1)),
      ← mul_assoc (Pos.pow vc (n + 1)) (Pos.pow lc (n + 1))
        (Pos.pow E (n + 1) * Pos.pow Dg (n + 1)),
      mul_comm (Pos.pow vc (n + 1)) (Pos.pow lc (n + 1))]
  have b1 : (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
      * (BPair.ofPos (Pos.pow lc (n + 1)) * dsV)).oneValue
      (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
        * (Pos.pow C (n + 1) * Pos.pow C (n + 1))) * Wj) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) b0) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.ofPos_mul _ _)
        (BPair.oneValue_refl Wj)) ?_
    refine BPair.mul_congr
      (BPair.oneValue_of_eq (congrArg BPair.ofPos ?_))
      (BPair.oneValue_refl Wj)
    rw [Pos.pow_mul C vc (n + 1), Pos.pow_mul lc vc (n + 1),
      mul_comm (Pos.pow C (n + 1)) (Pos.pow vc (n + 1)),
      mul_left_comm (Pos.pow C (n + 1)) (Pos.pow vc (n + 1))
        (Pos.pow C (n + 1)),
      ← mul_assoc (Pos.pow lc (n + 1)) (Pos.pow vc (n + 1))
        (Pos.pow C (n + 1) * Pos.pow C (n + 1))]
  -- the lower side at the joint clearing
  have hcmp : BPair.ofPos (Pos.pow (lc * vc) (n + 1)
        * (Pos.pow E (n + 1) * Pos.pow Dg (n + 1))) * Wj
      ≤ BPair.ofPos (Pos.pow (lc * vc) (n + 1)
        * (Pos.pow C (n + 1) * Pos.pow C (n + 1))) * Wj := by
    rw [BPair.mul_comm _ Wj, BPair.mul_comm _ Wj]
    refine ground.leB_mulR hWle ?_
    refine ground.leB_ofPos ?_
    rw [mul_comm (Pos.pow (lc * vc) (n + 1))
        (Pos.pow E (n + 1) * Pos.pow Dg (n + 1)),
      mul_comm (Pos.pow (lc * vc) (n + 1))
        (Pos.pow C (n + 1) * Pos.pow C (n + 1)),
      mul_comm (Pos.pow E (n + 1)) (Pos.pow Dg (n + 1))]
    exact mul_le_mul_right _ hloPos
  have hLV : BPair.ofPos (Pos.pow vc (n + 1)) * dsL
      ≤ BPair.ofPos (Pos.pow lc (n + 1)) * dsV := by
    have h1 : BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
        * (BPair.ofPos (Pos.pow vc (n + 1)) * dsL)
        ≤ BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
          * (BPair.ofPos (Pos.pow lc (n + 1)) * dsV) :=
      ground.leB_congr (BPair.oneValue_symm a1)
        (BPair.oneValue_symm b1) hcmp
    rw [BPair.mul_comm _ (BPair.ofPos (Pos.pow vc (n + 1)) * dsL),
      BPair.mul_comm _ (BPair.ofPos (Pos.pow lc (n + 1)) * dsV)] at h1
    exact ground.leB_unscale hJlt h1
  refine ⟨ground.leB_unit_add hLV, ?_⟩
  -- the width at the clearing-multiplied Pos display
  have hwid' : Pos.pow (lc * vc) (n + 1)
        * (Pos.pow C (n + 1) * Pos.pow C (n + 1)) * Wd
      ≤ Pos.pow E (n + 1) * Pos.pow C (n + 1)
          * (Wn * Pos.pow (lc * vc) (n + 1))
        + Pos.pow (lc * vc) (n + 1)
          * (Pos.pow E (n + 1) * Pos.pow Dg (n + 1)) * Wd := by
    have h0 := mul_le_mul_right (Pos.pow (lc * vc) (n + 1)) hwidPos
    rw [right_distrib] at h0
    rw [mul_comm (Pos.pow C (n + 1) * Pos.pow C (n + 1) * Wd)
        (Pos.pow (lc * vc) (n + 1)),
      ← mul_assoc (Pos.pow (lc * vc) (n + 1))
        (Pos.pow C (n + 1) * Pos.pow C (n + 1)) Wd,
      mul_assoc (Pos.pow E (n + 1) * Pos.pow C (n + 1)) Wn
        (Pos.pow (lc * vc) (n + 1)),
      mul_comm (Pos.pow E (n + 1) * Pos.pow Dg (n + 1) * Wd)
        (Pos.pow (lc * vc) (n + 1)),
      ← mul_assoc (Pos.pow (lc * vc) (n + 1))
        (Pos.pow E (n + 1) * Pos.pow Dg (n + 1)) Wd] at h0
    exact h0
  have pw := pairWidthLe
    (Pos.pow (lc * vc) (n + 1)
      * (Pos.pow C (n + 1) * Pos.pow C (n + 1)))
    (Pos.pow (lc * vc) (n + 1)
      * (Pos.pow E (n + 1) * Pos.pow Dg (n + 1)))
    (Pos.pow E (n + 1) * Pos.pow C (n + 1))
    (Wn * Pos.pow (lc * vc) (n + 1)) Wd hwid'
  have c1 : (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
      * (BPair.ofPos (Pos.pow lc (n + 1)) * dsV
        + (BPair.ofPos (Pos.pow vc (n + 1)) * dsL).swap)).oneValue
      ((BPair.ofPos (Pos.pow (lc * vc) (n + 1)
          * (Pos.pow C (n + 1) * Pos.pow C (n + 1)))
        + (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
            * (Pos.pow E (n + 1) * Pos.pow Dg (n + 1)))).swap)
        * Wj) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.left_distrib _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr b1
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_swap _ _))
          (ground.swap_congr a1))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.right_distrib, BPair.swap_mul]
  have hle0 : ((BPair.ofPos (Pos.pow (lc * vc) (n + 1)
          * (Pos.pow C (n + 1) * Pos.pow C (n + 1)))
        + (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
            * (Pos.pow E (n + 1)
              * Pos.pow Dg (n + 1)))).swap).scale Wd) * Wj
      ≤ ((BPair.ofPos
          (Pos.pow E (n + 1) * Pos.pow C (n + 1))).scale
            (Wn * Pos.pow (lc * vc) (n + 1))) * Wj := by
    rw [BPair.mul_comm _ Wj, BPair.mul_comm _ Wj]
    exact ground.leB_mulR hWle pw
  have he1 : ((BPair.ofPos (Pos.pow (lc * vc) (n + 1)
          * (Pos.pow C (n + 1) * Pos.pow C (n + 1)))
        + (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
            * (Pos.pow E (n + 1)
              * Pos.pow Dg (n + 1)))).swap) * Wj).scale Wd
      = (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
          * (Pos.pow C (n + 1) * Pos.pow C (n + 1)))
        + (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
            * (Pos.pow E (n + 1)
              * Pos.pow Dg (n + 1)))).swap).scale Wd * Wj := by
    rw [BPair.mul_comm _ Wj, ← BPair.mul_scale Wj _ Wd,
      BPair.mul_comm Wj _]
  have he2 : (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
        * Wj).scale (Wn * Pos.pow (lc * vc) (n + 1))
      = ((BPair.ofPos
          (Pos.pow E (n + 1) * Pos.pow C (n + 1))).scale
            (Wn * Pos.pow (lc * vc) (n + 1))) * Wj := by
    rw [BPair.mul_comm _ Wj,
      ← BPair.mul_scale Wj _ (Wn * Pos.pow (lc * vc) (n + 1)),
      BPair.mul_comm Wj _]
  have hle1 : ((BPair.ofPos (Pos.pow (lc * vc) (n + 1)
          * (Pos.pow C (n + 1) * Pos.pow C (n + 1)))
        + (BPair.ofPos (Pos.pow (lc * vc) (n + 1)
            * (Pos.pow E (n + 1)
              * Pos.pow Dg (n + 1)))).swap) * Wj).scale Wd
      ≤ (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
          * Wj).scale (Wn * Pos.pow (lc * vc) (n + 1)) := by
    rw [he1, he2]
    exact hle0
  have h2 : (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
      * (BPair.ofPos (Pos.pow lc (n + 1)) * dsV
        + (BPair.ofPos (Pos.pow vc (n + 1)) * dsL).swap)).scale Wd
      ≤ (BPair.ofPos (Pos.pow E (n + 1) * Pos.pow C (n + 1))
        * (Wj.norm)).scale (Wn * Pos.pow (lc * vc) (n + 1)) :=
    ground.leB_congr
      (BPair.scale_congr Wd (BPair.oneValue_symm c1))
      (BPair.scale_congr (Wn * Pos.pow (lc * vc) (n + 1))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (BPair.norm_oneValue Wj))))
      hle1
  have h3 := ground.leB_congr
    (BPair.oneValue_of_eq
      (BPair.mul_scale _ (BPair.ofPos (Pos.pow lc (n + 1)) * dsV
        + (BPair.ofPos (Pos.pow vc (n + 1)) * dsL).swap) Wd).symm)
    (BPair.oneValue_of_eq
      (BPair.mul_scale _ (Wj.norm)
        (Wn * Pos.pow (lc * vc) (n + 1))).symm) h2
  rw [BPair.mul_comm _ ((BPair.ofPos (Pos.pow lc (n + 1)) * dsV
      + (BPair.ofPos (Pos.pow vc (n + 1)) * dsL).swap).scale Wd),
    BPair.mul_comm _
      ((Wj.norm).scale (Wn * Pos.pow (lc * vc) (n + 1)))] at h3
  exact ground.leB_unscale hJlt h3

/-- The width's ground comparison at the positive arm: the counts'
square against the crossed products at the uniform width, the
Bernoulli display's upper side crossed by the cap. -/
private theorem widthPos (p dj Dg un ud kn kd : Pos) (n : Nat)
    (hg : un * p + Dg = posOfSucc n * (ud * dj))
    (hcap : p * kd ≤ kn * dj) :
    Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * (posOfSucc n * ((ud * ud) * (kd * kd)))
      ≤ Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * (un * un * (kn * kn))
        + Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * Pos.pow Dg (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd))) := by
  have hw0 := euc_width (un * p) (ud * dj) Dg n hg
  -- the cap crossed to the uniform width
  have hAW : un * p * (un * p)
        * (posOfSucc n * ((ud * ud) * (kd * kd)))
      ≤ un * un * (kn * kn)
        * (posOfSucc n * ((ud * dj) * (ud * dj))) := by
    have hsq : p * kd * (p * kd) ≤ kn * dj * (kn * dj) :=
      le_trans (mul_le_mul_right (p * kd) hcap)
        (by rw [mul_comm (kn * dj) (p * kd),
          mul_comm (kn * dj) (kn * dj)]
            exact mul_le_mul_right (kn * dj) hcap)
    have e1 : un * p * (un * p)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))
        = un * un * (posOfSucc n * (ud * ud))
          * (p * kd * (p * kd)) := by
      rw [mul_mul_mul_comm un p un p,
        mul_mul_mul_comm p kd p kd]
      rw [show posOfSucc n * ((ud * ud) * (kd * kd))
          = posOfSucc n * (ud * ud) * (kd * kd) from
          (mul_assoc _ _ _).symm]
      rw [mul_mul_mul_comm (un * un) (p * p)
        (posOfSucc n * (ud * ud)) (kd * kd)]
    have e2 : un * un * (kn * kn)
          * (posOfSucc n * ((ud * dj) * (ud * dj)))
        = un * un * (posOfSucc n * (ud * ud))
          * (kn * dj * (kn * dj)) := by
      rw [mul_mul_mul_comm ud dj ud dj,
        mul_mul_mul_comm kn dj kn dj]
      rw [show posOfSucc n * (ud * ud * (dj * dj))
          = posOfSucc n * (ud * ud) * (dj * dj) from
          (mul_assoc _ _ _).symm]
      rw [mul_mul_mul_comm (un * un) (kn * kn)
        (posOfSucc n * (ud * ud)) (dj * dj)]
    rw [e1, e2,
      mul_comm (un * un * (posOfSucc n * (ud * ud)))
        (p * kd * (p * kd)),
      mul_comm (un * un * (posOfSucc n * (ud * ud)))
        (kn * dj * (kn * dj))]
    exact mul_le_mul_right _ hsq
  have h1 := mul_le_mul_right
    (posOfSucc n * ((ud * ud) * (kd * kd))) hw0
  have e2a : (Pos.pow Dg (n + 1)
        * (posOfSucc n * (ud * dj * (ud * dj)))
      + un * p * (un * p)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
      * Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
      * (posOfSucc n * ((ud * ud) * (kd * kd)))
      = Pos.pow Dg (n + 1) * (posOfSucc n * (ud * dj * (ud * dj)))
          * Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))
        + un * p * (un * p)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd))) := by
    rw [right_distrib
        (Pos.pow Dg (n + 1)
          * (posOfSucc n * (ud * dj * (ud * dj))))
        (un * p * (un * p)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)),
      right_distrib _ _ (posOfSucc n * ((ud * ud) * (kd * kd)))]
  have e3a : un * p * (un * p)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
        * (posOfSucc n * ((ud * ud) * (kd * kd)))
      = Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * (un * p * (un * p)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))) := by
    rw [mul_assoc
        (un * p * (un * p)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd))),
      mul_comm
        (un * p * (un * p)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))),
      mul_mul_mul_comm
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd)))
        (un * p * (un * p))
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1)),
      mul_comm (posOfSucc n * ((ud * ud) * (kd * kd)))
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1)),
      mul_mul_mul_comm
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1))
        (un * p * (un * p))
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd)))]
  have e3b : Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * (un * p * (un * p)
          * (posOfSucc n * ((ud * ud) * (kd * kd))))
      ≤ Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * (un * un * (kn * kn)
          * (posOfSucc n * (ud * dj * (ud * dj)))) := by
    rw [mul_comm
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (un * p * (un * p)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))),
      mul_comm
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (un * un * (kn * kn)
          * (posOfSucc n * (ud * dj * (ud * dj))))]
    exact mul_le_mul_right _
      (by
        rw [show posOfSucc n * (ud * dj * (ud * dj))
            = posOfSucc n * ((ud * dj) * (ud * dj)) from rfl]
        exact hAW)
  have e4 : Pos.pow Dg (n + 1)
        * (posOfSucc n * (ud * dj * (ud * dj)))
        * Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
        * (posOfSucc n * ((ud * ud) * (kd * kd)))
      = Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * Pos.pow Dg (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))
          * (posOfSucc n * (ud * dj * (ud * dj))) := by
    rw [mul_assoc
        (Pos.pow Dg (n + 1)
          * (posOfSucc n * (ud * dj * (ud * dj))))
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd))),
      mul_comm
        (Pos.pow Dg (n + 1)
          * (posOfSucc n * (ud * dj * (ud * dj))))
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))),
      mul_mul_mul_comm
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd)))
        (Pos.pow Dg (n + 1))
        (posOfSucc n * (ud * dj * (ud * dj))),
      ← mul_assoc
        (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * Pos.pow Dg (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd)))
        (posOfSucc n * (ud * dj * (ud * dj)))]
  have e3c : Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * (un * un * (kn * kn)
          * (posOfSucc n * (ud * dj * (ud * dj))))
      = Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * (un * un * (kn * kn))
          * (posOfSucc n * (ud * dj * (ud * dj))) := by
    rw [← mul_assoc
      (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
      (un * un * (kn * kn))
      (posOfSucc n * (ud * dj * (ud * dj)))]
  have e6 : Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
        * (posOfSucc n * (ud * dj * (ud * dj)))
        * (posOfSucc n * ((ud * ud) * (kd * kd)))
      = Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd)))
          * (posOfSucc n * (ud * dj * (ud * dj))) := by
    rw [mul_assoc
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (posOfSucc n * (ud * dj * (ud * dj)))
        (posOfSucc n * ((ud * ud) * (kd * kd))),
      mul_comm (posOfSucc n * (ud * dj * (ud * dj)))
        (posOfSucc n * ((ud * ud) * (kd * kd))),
      ← mul_assoc
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd)))
        (posOfSucc n * (ud * dj * (ud * dj)))]
  rw [e2a, e3a] at h1
  have h2 := ground.le_trans h1
    (posLeAdd (Or.inl rfl) e3b)
  rw [e4, e3c, e6] at h2
  rw [← right_distrib
    (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
      * Pos.pow Dg (n + 1)
      * (posOfSucc n * ((ud * ud) * (kd * kd))))
    (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
      * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
      * (un * un * (kn * kn)))
    (posOfSucc n * (ud * dj * (ud * dj)))] at h2
  rw [ground.add_comm
    (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
      * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
      * (un * un * (kn * kn)))
    (Pos.pow (posOfSucc n * (ud * dj) + un * p) (n + 1)
      * Pos.pow Dg (n + 1)
      * (posOfSucc n * ((ud * ud) * (kd * kd))))]
  exact ground.le_of_mul_le h2

/-- One root's bracket at the two families' congruated diagonal
entries: the difference on the positive side and within the uniform
width against the gram scale, the certificate arm's own reads. -/
private theorem rootBracket {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud kn kd lc vc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd (posOfSucc n) l ws)
    (Lw Vw : Mat) (hLs : sqAt Lw o) (hVs : sqAt Vw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (j : Nat) (hj : j < o) (nj gj : BPair) (dj : Pos)
    (hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
      = (nj, dj, gj)) :
    (BPair.unit
      ≤ BPair.ofPos (Pos.pow lc (n + 1))
          * ground.getAt BPair.unit
              (split.vDiagL (matPow Vw o (n + 1)) T) j
        + (BPair.ofPos (Pos.pow vc (n + 1))
            * ground.getAt BPair.unit
                (split.vDiagL (matPow Lw o (n + 1)) T) j).swap)
    ∧ ((BPair.ofPos (Pos.pow lc (n + 1))
          * ground.getAt BPair.unit
              (split.vDiagL (matPow Vw o (n + 1)) T) j
        + (BPair.ofPos (Pos.pow vc (n + 1))
            * ground.getAt BPair.unit
                (split.vDiagL (matPow Lw o (n + 1)) T) j).swap).scale
          (posOfSucc n * ((ud * ud) * (kd * kd)))
        ≤ ((gj * BPair.ofPos dj).norm).scale
            ((un * un * (kn * kn)) * Pos.pow (lc * vc) (n + 1))) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hjl : j < l.length := by
    rw [split.rootLen Et T Tw l hd]; exact hj
  have hvl : (matVec T.val (elim.idRow o j)).length = o := by
    rw [matVec_length, hTl]
  have hwj : ground.getAt (Pos.one, Pos.one) ws j
      = ((ground.getAt (Pos.one, Pos.one) ws j).1,
         (ground.getAt (Pos.one, Pos.one) ws j).2) := rfl
  have harm := eucRead_at un ud kn kd (posOfSucc n) l ws hw j hjl
    nj gj dj hroot _ _ hwj
  have hHcol := euc_hi_col Et T Tw l hd un ud vc n ws
      (eucRead_arm un ud kn kd (posOfSucc n) l ws hw) Vw hVs hV
    j hj nj gj dj hroot
  have hLcol := loColArm Et T Tw l hd un ud kn kd lc n ws hw Lw hLs hL
    j hj
  rw [hroot] at hLcol
  have hHpow := matPow_col Vw hVs _ hvl
    (BPair.ofPos ((posOfSucc n * (ud * dj)) * vc))
    (BPair.ofPos (posOfSucc n * (ud * dj)) + nj.scale un)
    hHcol (n + 1)
  have hLpow := matPow_col Lw hLs _ hvl
    (BPair.ofPos ((ground.getAt (Pos.one, Pos.one) ws j).2 * lc))
    (BPair.ofPos (posOfSucc n * (ud * dj)))
    hLcol (n + 1)
  have hVpin0 := split.colDiagPin Et T Tw l hd (matPow Vw o (n + 1))
    (length_matPow Vw o (sqAt_len hVs) (n + 1))
    (rowsLen_matPow Vw o (sqAt_len hVs) (n + 1))
    j hj nj gj dj hroot _ _ hHpow
  have hLpin0 := split.colDiagPin Et T Tw l hd (matPow Lw o (n + 1))
    (length_matPow Lw o (sqAt_len hLs) (n + 1))
    (rowsLen_matPow Lw o (sqAt_len hLs) (n + 1))
    j hj nj gj dj hroot _ _ hLpow
  have hWpos : BPair.unit < gj * BPair.ofPos dj :=
    ground.unitLtMul (split.scalePos Et T Tw l hd j hjl nj gj dj hroot)
      (ground.unitLtOfPos dj)
  have hLpin : (BPair.ofPos
      (Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
      * ground.getAt BPair.unit
          (split.vDiagL (matPow Lw o (n + 1)) T) j).oneValue
      (BPair.ofPos
        (Pos.pow ((ground.getAt (Pos.one, Pos.one) ws j).2 * lc)
          (n + 1))
        * (gj * BPair.ofPos dj)) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (ground.ofPos_pow _ (n + 1))
        (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans hLpin0 ?_
    exact BPair.mul_congr
      (BPair.oneValue_symm (ground.ofPos_pow _ (n + 1)))
      (BPair.oneValue_refl _)
  refine harm.elim (fun hker => ?_) (fun hpos => ?_)
  · -- the kernel arm: the crossing is vacant, the value the clearing
    have hE : (BPair.ofPos (posOfSucc n * (ud * dj))
        + nj.scale un).oneValue
        (BPair.ofPos (posOfSucc n * (ud * dj))) := by
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.scale_congr un hker.1)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_symm (ground.unitScale un))) ?_
      exact BPair.add_unit _
    have hVpin : (BPair.ofPos
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1))
        * ground.getAt BPair.unit
            (split.vDiagL (matPow Vw o (n + 1)) T) j).oneValue
        (BPair.ofPos
            (Pos.pow ((posOfSucc n * (ud * dj)) * vc) (n + 1))
          * (gj * BPair.ofPos dj)) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans (ground.ofPos_pow _ (n + 1))
            (BPair.oneValue_symm (ground.bpow_congr hE (n + 1))))
          (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans hVpin0 ?_
      exact BPair.mul_congr
        (BPair.oneValue_symm (ground.ofPos_pow _ (n + 1)))
        (BPair.oneValue_refl _)
    refine bracketClose _ _ _
      (posOfSucc n * (ud * dj))
      (ground.getAt (Pos.one, Pos.one) ws j).2
      (posOfSucc n * (ud * dj)) lc vc n
      (un * un * (kn * kn))
      (posOfSucc n * ((ud * ud) * (kd * kd)))
      hWpos hVpin hLpin ?_ ?_
    · rw [hker.2]
      exact Or.inl rfl
    · rw [hker.2, ground.add_comm
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * (un * un * (kn * kn)))
        (Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * Pos.pow (posOfSucc n * (ud * dj)) (n + 1)
          * (posOfSucc n * ((ud * ud) * (kd * kd))))]
      exact posLeSelfAdd _ _
  · -- the positive arm: the crossing at the stated representative
    have hE : (BPair.ofPos (posOfSucc n * (ud * dj))
        + nj.scale un).oneValue
        (BPair.ofPos (posOfSucc n * (ud * dj)
          + un * (ground.getAt (Pos.one, Pos.one) ws j).1)) := by
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.scale_congr un hpos.1)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.scale_ofPos _ un)) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.oneValue_of_eq
            (congrArg BPair.ofPos (mul_comm _ un)))) ?_
      exact BPair.oneValue_symm (BPair.ofPos_add _ _)
    have hVpin : (BPair.ofPos
        (Pos.pow (posOfSucc n * (ud * dj)
          + un * (ground.getAt (Pos.one, Pos.one) ws j).1) (n + 1))
        * ground.getAt BPair.unit
            (split.vDiagL (matPow Vw o (n + 1)) T) j).oneValue
        (BPair.ofPos
            (Pos.pow ((posOfSucc n * (ud * dj)) * vc) (n + 1))
          * (gj * BPair.ofPos dj)) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.oneValue_trans (ground.ofPos_pow _ (n + 1))
            (BPair.oneValue_symm (ground.bpow_congr hE (n + 1))))
          (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans hVpin0 ?_
      exact BPair.mul_congr
        (BPair.oneValue_symm (ground.ofPos_pow _ (n + 1)))
        (BPair.oneValue_refl _)
    refine bracketClose _ _ _
      (posOfSucc n * (ud * dj))
      (ground.getAt (Pos.one, Pos.one) ws j).2
      (posOfSucc n * (ud * dj)
        + un * (ground.getAt (Pos.one, Pos.one) ws j).1) lc vc n
      (un * un * (kn * kn))
      (posOfSucc n * ((ud * ud) * (kd * kd)))
      hWpos hVpin hLpin ?_ ?_
    · exact euc_le (un * (ground.getAt (Pos.one, Pos.one) ws j).1)
        (ud * dj) (ground.getAt (Pos.one, Pos.one) ws j).2 n
        hpos.2.1
    · exact widthPos (ground.getAt (Pos.one, Pos.one) ws j).1 dj
        (ground.getAt (Pos.one, Pos.one) ws j).2 un ud kn kd n
        hpos.2.1 hpos.2.2

/-- The magnitude display's close at the two directions: the two
det-cleared fold comparisons and the three fold reads land the
polarized bound, the balance partner's direction the read at the
swapped difference. -/
private theorem pairPriceCore {dd A0 B0 Gx Gy a b : BPair}
    {P1 P2 W Q V : List BPair} {WD WN : Pos}
    (hdd : BPair.unit < dd)
    (hcmp1 : (dotP P1 W).scale WD ≤ (dotP Q V).scale WN)
    (hcmp2 : (dotP P2 W).scale WD ≤ (dotP Q V).scale WN)
    (he1 : (dotP P1 W).oneValue ((a * b) * (A0 + B0.swap) * dd))
    (he1b : (dotP P2 W).oneValue ((a * b) * (A0.swap + B0) * dd))
    (he2 : (dotP Q V).oneValue
      (((a * a) * Gx + (b * b) * Gy) * dd)) :
    (windowsep.mag ((a * b) * (A0 + B0.swap))).scale WD
      ≤ ((a * a) * Gx + (b * b) * Gy).scale WN := by
  have hdir1 : (((a * b) * (A0 + B0.swap)).scale WD) * dd
      ≤ (((a * a) * Gx + (b * b) * Gy).scale WN) * dd := by
    rw [← BPair.scale_mul_left ((a * b) * (A0 + B0.swap)) dd WD,
      ← BPair.scale_mul_left ((a * a) * Gx + (b * b) * Gy) dd WN]
    exact ground.leB_congr (BPair.scale_congr WD he1)
      (BPair.scale_congr WN he2) hcmp1
  have hdir2 : (((a * b) * (A0.swap + B0)).scale WD) * dd
      ≤ (((a * a) * Gx + (b * b) * Gy).scale WN) * dd := by
    rw [← BPair.scale_mul_left ((a * b) * (A0.swap + B0)) dd WD,
      ← BPair.scale_mul_left ((a * a) * Gx + (b * b) * Gy) dd WN]
    exact ground.leB_congr (BPair.scale_congr WD he1b)
      (BPair.scale_congr WN he2) hcmp2
  have h1 := ground.leB_unscale hdd hdir1
  have h2 := ground.leB_unscale hdd hdir2
  refine ground.leB_congr_left (BPair.ofPos_scale WD _) ?_
  refine windowsep.mag_mul_le ?_ ?_
  · exact ground.leB_congr_left
      (BPair.oneValue_symm (BPair.ofPos_scale WD _)) h1
  · refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.ofPos_scale WD _)) ?_
    show ((a * b) * (A0.swap + B0)).scale WD
      ≤ ((a * a) * Gx + (b * b) * Gy).scale WN
    exact h2

/-- Clause (v)'s pair-of-families pricing: a read at the two
families' difference is priced by the weighted polarization at the
two probes' gram reads, the spectral width the factor — the
magnitude display at free weights, the certificate fold's uniform
width. -/
theorem euc_pair_price {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud kn kd lc vc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd (posOfSucc n) l ws)
    (Lw Vw : Mat) (hLs : sqAt Lw o) (hVs : sqAt Vw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (x y : List BPair) (hx : x.length = o) (hy : y.length = o)
    (a b : BPair) :
    (windowsep.mag ((a * b)
        * ((elim.dotP x (elim.matVec (matPow Vw o (n + 1)) y)).scale
            (Pos.pow lc (n + 1))
           + ((elim.dotP x
               (elim.matVec (matPow Lw o (n + 1)) y)).scale
             (Pos.pow vc (n + 1))).swap))).scale
      (2 * (posOfSucc n * ((ud * ud) * (kd * kd))))
    ≤ ((a * a) * elim.dotP x x + (b * b) * elim.dotP y y).scale
        ((un * un * (kn * kn)) * Pos.pow (lc * vc) (n + 1)) := by
  have hTl : T.val.length = o := SqMat.rows T
  have hTwl : Tw.val.length = o := SqMat.rows Tw
  have hdet : ¬ (minor T.val).oneValue BPair.unit := hd.2.2.1.1
  have hlen : l.length = o := split.rootLen Et T Tw l hd
  have hXl : (matVec Tw.val x).length = o := by
    rw [matVec_length, hTwl]
  have hYl : (matVec Tw.val y).length = o := by
    rw [matVec_length, hTwl]
  -- the two families' diagonal identities from the column reads
  have hcdVoff : ∀ j, j < o →
      ∀ (nj gj : BPair) (dj : Pos),
      ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
        = (nj, dj, gj) →
      ¬ (ground.bpow
          (BPair.ofPos (posOfSucc n * (ud * dj)) + nj.scale un)
          (n + 1)).oneValue BPair.unit := by
    intro j hj nj gj dj hroot
    have hjl : j < l.length := by rw [hlen]; exact hj
    have hwj : ground.getAt (Pos.one, Pos.one) ws j
        = ((ground.getAt (Pos.one, Pos.one) ws j).1,
           (ground.getAt (Pos.one, Pos.one) ws j).2) := rfl
    have harm := eucRead_at un ud kn kd (posOfSucc n) l ws hw j hjl
      nj gj dj hroot _ _ hwj
    have h0 : ¬ (BPair.ofPos (dj * (posOfSucc n * ud))
        + nj.scale un).oneValue BPair.unit :=
      armScaleOff (harm.imp And.left And.left)
    rw [show dj * (posOfSucc n * ud) = posOfSucc n * (ud * dj) from by
      rw [mul_left_comm dj (posOfSucc n) ud, mul_comm dj ud]] at h0
    exact ground.bpow_off _ h0 (n + 1)
  have hDiagV : elim.matOneValue
      (matMul (transposeM T.val)
        (matMul (matPow Vw o (n + 1)) T.val))
      (split.diagM (split.vDiagL (matPow Vw o (n + 1)) T)) := by
    refine split.diagOfPairs (matPow Vw o (n + 1)) T
      (length_matPow Vw o (sqAt_len hVs) (n + 1))
      (rowsLen_matPow Vw o (sqAt_len hVs) (n + 1)) ?_
    intro i j hi hj hne
    have hjl : j < l.length := by rw [hlen]; exact hj
    have hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
        = ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2) :=
      rfl
    have hvl : (matVec T.val (elim.idRow o j)).length = o := by
      rw [matVec_length, hTl]
    have hHcol := euc_hi_col Et T Tw l hd un ud vc n ws
      (eucRead_arm un ud kn kd (posOfSucc n) l ws hw) Vw hVs
      hV j hj _ _ _ hroot
    exact split.colOffPair Et T Tw l hd (matPow Vw o (n + 1)) i j hi hj hne
      _ _ (hcdVoff j hj _ _ _ hroot)
      (matPow_col Vw hVs _ hvl _ _ hHcol (n + 1))
  have hDiagL : elim.matOneValue
      (matMul (transposeM T.val)
        (matMul (matPow Lw o (n + 1)) T.val))
      (split.diagM (split.vDiagL (matPow Lw o (n + 1)) T)) := by
    refine split.diagOfPairs (matPow Lw o (n + 1)) T
      (length_matPow Lw o (sqAt_len hLs) (n + 1))
      (rowsLen_matPow Lw o (sqAt_len hLs) (n + 1)) ?_
    intro i j hi hj hne
    have hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
        = ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2) :=
      rfl
    have hvl : (matVec T.val (elim.idRow o j)).length = o := by
      rw [matVec_length, hTl]
    have hLcol := loColArm Et T Tw l hd un ud kn kd lc n ws hw Lw hLs hL
      j hj
    have hoff : ¬ (ground.bpow (BPair.ofPos (posOfSucc n
        * (ud * (ground.getAt (BPair.unit, Pos.one, BPair.unit)
            l j).2.1))) (n + 1)).oneValue BPair.unit := by
      intro hu
      exact BPair.ofPos_off _
        (BPair.oneValue_trans (ground.ofPos_pow _ (n + 1)) hu)
    exact split.colOffPair Et T Tw l hd (matPow Lw o (n + 1)) i j hi hj hne
      _ _ hoff (matPow_col Lw hLs _ hvl _ _ hLcol (n + 1))
  -- the identity family's congruated diagonal: the gram reads
  have hDiagG : elim.matOneValue
      (matMul (transposeM T.val) (matMul (idMat o) T.val))
      (split.diagM (split.vDiagL (idMat o) T)) := by
    refine split.diagOfPairs (idMat o) T (idMat_len o) (idMat_rows o) ?_
    intro i j hi hj hne
    have hvl : (matVec T.val (elim.idRow o j)).length = o := by
      rw [matVec_length, hTl]
    exact BPair.oneValue_trans
      (dotP_oneValue_right _ _ _ (inertia.matVec_idMat o _ hvl))
      (split.gramOff Et T Tw l hd i j hi hj hne)
  have hadjx := split.adjAct Et T Tw l hd x hx
  have hadjy := split.adjAct Et T Tw l hd y hy
  -- the three families' det-cleared fold reads
  have hFV : (minor T.val * minor T.val
        * dotP x (matVec (matPow Vw o (n + 1)) y)).oneValue
      (dotP (split.vDiagL (matPow Vw o (n + 1)) T)
        (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (split.pairScale (matPow Vw o (n + 1)) (minor T.val) x y
          (matVec T.val (matVec Tw.val x)) (matVec T.val (matVec Tw.val y))
          hadjx hadjy)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) ?_
    exact split.diagFold (matPow Vw o (n + 1)) T _
      (length_matPow Vw o (sqAt_len hVs) (n + 1))
      (rowsLen_matPow Vw o (sqAt_len hVs) (n + 1))
      (split.vDiagL_len (matPow Vw o (n + 1)) T) hDiagV
      (matVec Tw.val x) (matVec Tw.val y) hXl hYl
  have hFL : (minor T.val * minor T.val
        * dotP x (matVec (matPow Lw o (n + 1)) y)).oneValue
      (dotP (split.vDiagL (matPow Lw o (n + 1)) T)
        (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (split.pairScale (matPow Lw o (n + 1)) (minor T.val) x y
          (matVec T.val (matVec Tw.val x)) (matVec T.val (matVec Tw.val y))
          hadjx hadjy)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) ?_
    exact split.diagFold (matPow Lw o (n + 1)) T _
      (length_matPow Lw o (sqAt_len hLs) (n + 1))
      (rowsLen_matPow Lw o (sqAt_len hLs) (n + 1))
      (split.vDiagL_len (matPow Lw o (n + 1)) T) hDiagL
      (matVec Tw.val x) (matVec Tw.val y) hXl hYl
  have hGX : (minor T.val * minor T.val * dotP x x).oneValue
      (dotP (split.vDiagL (idMat o) T)
        (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val x))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.mul_congr
          (BPair.oneValue_refl (minor T.val * minor T.val))
          (dotP_oneValue_right x _ _ (inertia.matVec_idMat o x hx)))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (split.pairScale (idMat o) (minor T.val) x x
          (matVec T.val (matVec Tw.val x)) (matVec T.val (matVec Tw.val x))
          hadjx hadjx)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) ?_
    exact split.diagFold (idMat o) T _ (idMat_len o) (idMat_rows o)
      (split.vDiagL_len (idMat o) T) hDiagG
      (matVec Tw.val x) (matVec Tw.val x) hXl hXl
  have hGY : (minor T.val * minor T.val * dotP y y).oneValue
      (dotP (split.vDiagL (idMat o) T)
        (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.mul_congr
          (BPair.oneValue_refl (minor T.val * minor T.val))
          (dotP_oneValue_right y _ _ (inertia.matVec_idMat o y hy)))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (split.pairScale (idMat o) (minor T.val) y y
          (matVec T.val (matVec Tw.val y)) (matVec T.val (matVec Tw.val y))
          hadjy hadjy)) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) ?_
    exact split.diagFold (idMat o) T _ (idMat_len o) (idMat_rows o)
      (split.vDiagL_len (idMat o) T) hDiagG
      (matVec Tw.val y) (matVec Tw.val y) hYl hYl
  -- the carried lists' orders
  have hdsVl : (split.vDiagL (matPow Vw o (n + 1)) T).length = o :=
    split.vDiagL_len (matPow Vw o (n + 1)) T
  have hdsLl : (split.vDiagL (matPow Lw o (n + 1)) T).length = o :=
    split.vDiagL_len (matPow Lw o (n + 1)) T
  have hdsGl : (split.vDiagL (idMat o) T).length = o :=
    split.vDiagL_len (idMat o) T
  have hVsl : (vecScale (BPair.ofPos (Pos.pow lc (n + 1))) (split.vDiagL
      (matPow Vw o (n + 1)) T)).length = o := by
    rw [length_vecScale]; exact hdsVl
  have hLsl : (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
      (matPow Lw o (n + 1)) T)).length = o := by
    rw [length_vecScale]; exact hdsLl
  have hnegVl : (poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
      (split.vDiagL (matPow Vw o (n + 1)) T))).length = o := by
    rw [poly.length_neg]; exact hVsl
  have hnegLl : (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1)))
      (split.vDiagL (matPow Lw o (n + 1)) T))).length = o := by
    rw [poly.length_neg]; exact hLsl
  have hZXYl : (List.zipWith (· * ·) (matVec Tw.val x)
      (matVec Tw.val y)).length = o :=
    ground.length_zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y) o
      hXl hYl
  have hZXXl : (List.zipWith (· * ·) (matVec Tw.val x)
      (matVec Tw.val x)).length = o :=
    ground.length_zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val x) o
      hXl hXl
  have hZYYl : (List.zipWith (· * ·) (matVec Tw.val y)
      (matVec Tw.val y)).length = o :=
    ground.length_zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y) o
      hYl hYl
  have hD1l : (vecAdd (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
      (split.vDiagL (matPow Vw o (n + 1)) T))
      (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
          (matPow Lw o (n + 1)) T)))).length = o :=
    length_vecAdd _ _ o hVsl hnegLl
  have hD2l : (vecAdd (poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
      (split.vDiagL (matPow Vw o (n + 1)) T)))
      (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow Lw o
          (n + 1)) T))).length = o :=
    length_vecAdd _ _ o hnegVl hLsl
  have hVXl : (vecScale (a * a) (List.zipWith (· * ·) (matVec Tw.val x)
      (matVec Tw.val x))).length = o := by
    rw [length_vecScale]; exact hZXXl
  have hVYl : (vecScale (b * b) (List.zipWith (· * ·) (matVec Tw.val y)
      (matVec Tw.val y))).length = o := by
    rw [length_vecScale]; exact hZYYl
  have hVall : (vecAdd
      (vecScale (a * a) (List.zipWith (· * ·) (matVec Tw.val x)
        (matVec Tw.val x)))
      (vecScale (b * b) (List.zipWith (· * ·) (matVec Tw.val y)
        (matVec Tw.val y)))).length = o :=
    length_vecAdd _ _ o hVXl hVYl
  -- the per-root term price at a free polarization partner
  have hkey : ∀ j, j < o → ∀ z : BPair,
      (((a * b) * z).scale 2
        ≤ (a * a) * (ground.getAt BPair.unit (matVec Tw.val x) j
              * ground.getAt BPair.unit (matVec Tw.val x) j)
          + (b * b) * (ground.getAt BPair.unit (matVec Tw.val y) j
              * ground.getAt BPair.unit (matVec Tw.val y) j)) →
      ((a * b) * ((BPair.ofPos (Pos.pow lc (n + 1)) * ground.getAt BPair.unit
          (split.vDiagL (matPow Vw o (n + 1)) T) j
          + (BPair.ofPos (Pos.pow vc (n + 1)) * ground.getAt BPair.unit
              (split.vDiagL (matPow Lw o (n + 1)) T) j).swap) * z)).scale
          (2 * (posOfSucc n * ((ud * ud) * (kd * kd))))
        ≤ (ground.getAt BPair.unit (split.vDiagL (idMat o) T) j
            * ((a * a) * (ground.getAt BPair.unit (matVec Tw.val x) j
              * ground.getAt BPair.unit (matVec Tw.val x) j)
          + (b * b) * (ground.getAt BPair.unit (matVec Tw.val y) j
              * ground.getAt BPair.unit (matVec Tw.val y) j))).scale
          ((un * un * (kn * kn)) * Pos.pow (lc * vc) (n + 1)) := by
    intro j hj z hpol
    have hroot : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j
        = ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1,
           (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2) :=
      rfl
    have hvl : (matVec T.val (elim.idRow o j)).length = o := by
      rw [matVec_length, hTl]
    have hbr := rootBracket Et T Tw l hd un ud kn kd lc vc n ws hw
      Lw Vw hLs hVs hL hV j hj _ _ _ hroot
    have hQread : (ground.getAt BPair.unit
          (split.vDiagL (idMat o) T) j).oneValue
        ((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2
          * BPair.ofPos
            (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1) := by
      refine BPair.oneValue_trans
        (split.vDiagL_read (idMat o) T (idMat_len o) (idMat_rows o)
          j hj) ?_
      refine BPair.oneValue_trans
        (dotP_oneValue_right _ _ _ (inertia.matVec_idMat o _ hvl)) ?_
      exact split.gramDiag Et T Tw l hd j hj _ _ _ hroot
    have hRpos : BPair.unit
        ≤ (a * a) * (ground.getAt BPair.unit (matVec Tw.val x) j
              * ground.getAt BPair.unit (matVec Tw.val x) j)
          + (b * b) * (ground.getAt BPair.unit (matVec Tw.val y) j
              * ground.getAt BPair.unit (matVec Tw.val y) j) := by
      refine ground.leB_congr (BPair.add_unit BPair.unit)
        (BPair.oneValue_refl _) (ground.leB_add ?_ ?_)
      · rw [BPair.mul_mul_mul_comm]
        exact ground.unitLeSq _
      · rw [BPair.mul_mul_mul_comm]
        exact ground.unitLeSq _
    refine ground.leB_congr_right ?_
      (termChain (a * b)
        ((a * a) * (ground.getAt BPair.unit (matVec Tw.val x) j
              * ground.getAt BPair.unit (matVec Tw.val x) j)
          + (b * b) * (ground.getAt BPair.unit (matVec Tw.val y) j
              * ground.getAt BPair.unit (matVec Tw.val y) j))
        (BPair.ofPos (Pos.pow lc (n + 1)) * ground.getAt BPair.unit
            (split.vDiagL (matPow Vw o (n + 1)) T) j
          + (BPair.ofPos (Pos.pow vc (n + 1)) * ground.getAt BPair.unit
              (split.vDiagL (matPow Lw o (n + 1)) T) j).swap)
        (((ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.2
          * BPair.ofPos
            (ground.getAt (BPair.unit, Pos.one, BPair.unit) l j).2.1).norm)
        z ((un * un * (kn * kn)) * Pos.pow (lc * vc) (n + 1))
        (posOfSucc n * ((ud * ud) * (kd * kd)))
        hbr.1 hbr.2 hRpos hpol)
    exact BPair.scale_congr _
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.oneValue_trans (BPair.norm_oneValue _)
            (BPair.oneValue_symm hQread)))
        (BPair.oneValue_of_eq (BPair.mul_comm _ _)))
  have hcmp1 := elim.dotP_le_of_leTerm
    (2 * (posOfSucc n * ((ud * ud) * (kd * kd)))) ((un * un * (kn * kn)) *
        Pos.pow (lc * vc) (n + 1))
    (vecScale (a * b) (vecAdd (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
        (split.vDiagL (matPow Vw o (n + 1)) T))
      (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
          (matPow Lw o (n + 1)) T)))))
    (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
    (split.vDiagL (idMat o) T)
    (vecAdd (vecScale (a * a) (List.zipWith (· * ·) (matVec Tw.val x) (matVec
        Tw.val x))) (vecScale (b * b) (List.zipWith (· * ·) (matVec Tw.val y)
        (matVec Tw.val y))))
    (by rw [length_vecScale, hD1l, hdsGl])
    (by
      intro j hj0
      rw [length_vecScale, hD1l] at hj0
      rw [getAt_vecScale (a * b)
          (vecAdd (vecScale (BPair.ofPos (Pos.pow lc (n + 1))) (split.vDiagL
              (matPow Vw o (n + 1)) T))
      (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
          (matPow Lw o (n + 1)) T)))) j
          (by rw [hD1l]; exact hj0),
        getAt_vecAdd (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
            (split.vDiagL (matPow Vw o (n + 1)) T))
          (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1)))
              (split.vDiagL (matPow Lw o (n + 1)) T))) j
          (by rw [hVsl]; exact hj0) (by rw [hnegLl]; exact hj0),
        show poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1)))
            (split.vDiagL (matPow Lw o (n + 1)) T))
            = (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
                (matPow Lw o (n + 1)) T)).map BPair.swap
          from rfl,
        ground.getAt_map BPair.unit BPair.unit BPair.swap
          (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow
              Lw o (n + 1)) T)) j
          (by rw [hLsl]; exact hj0),
        getAt_vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
          (split.vDiagL (matPow Vw o (n + 1)) T) j
          (by rw [hdsVl]; exact hj0),
        getAt_vecScale (BPair.ofPos (Pos.pow vc (n + 1)))
          (split.vDiagL (matPow Lw o (n + 1)) T) j
          (by rw [hdsLl]; exact hj0),
        ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
          (matVec Tw.val x) (matVec Tw.val y) j
          (by rw [hXl]; exact hj0) (by rw [hYl]; exact hj0),
        getAt_vecAdd (vecScale (a * a) (List.zipWith (· * ·) (matVec Tw.val
            x) (matVec Tw.val x)))
          (vecScale (b * b) (List.zipWith (· * ·) (matVec Tw.val y) (matVec
              Tw.val y))) j
          (by rw [hVXl]; exact hj0) (by rw [hVYl]; exact hj0),
        getAt_vecScale (a * a)
          (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val x)) j
          (by rw [hZXXl]; exact hj0),
        getAt_vecScale (b * b)
          (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y)) j
          (by rw [hZYYl]; exact hj0),
        ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
          (matVec Tw.val x) (matVec Tw.val x) j
          (by rw [hXl]; exact hj0) (by rw [hXl]; exact hj0),
        ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
          (matVec Tw.val y) (matVec Tw.val y) j
          (by rw [hYl]; exact hj0) (by rw [hYl]; exact hj0),
        BPair.mul_assoc]
      exact hkey j hj0
        (ground.getAt BPair.unit (matVec Tw.val x) j
          * ground.getAt BPair.unit (matVec Tw.val y) j)
        (scalarPolar a b (ground.getAt BPair.unit (matVec Tw.val x) j)
          (ground.getAt BPair.unit (matVec Tw.val y) j)))
  have hcmp2 := elim.dotP_le_of_leTerm
    (2 * (posOfSucc n * ((ud * ud) * (kd * kd)))) ((un * un * (kn * kn)) *
        Pos.pow (lc * vc) (n + 1))
    (vecScale (a * b) (vecAdd (poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n
        + 1))) (split.vDiagL (matPow Vw o (n + 1)) T)))
      (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow Lw o
          (n + 1)) T))))
    (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
    (split.vDiagL (idMat o) T)
    (vecAdd (vecScale (a * a) (List.zipWith (· * ·) (matVec Tw.val x) (matVec
        Tw.val x))) (vecScale (b * b) (List.zipWith (· * ·) (matVec Tw.val y)
        (matVec Tw.val y))))
    (by rw [length_vecScale, hD2l, hdsGl])
    (by
      intro j hj0
      rw [length_vecScale, hD2l] at hj0
      rw [getAt_vecScale (a * b)
          (vecAdd (poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
              (split.vDiagL (matPow Vw o (n + 1)) T)))
      (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow Lw o
          (n + 1)) T))) j
          (by rw [hD2l]; exact hj0),
        getAt_vecAdd (poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
            (split.vDiagL (matPow Vw o (n + 1)) T)))
          (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow
              Lw o (n + 1)) T)) j
          (by rw [hnegVl]; exact hj0) (by rw [hLsl]; exact hj0),
        show poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
            (split.vDiagL (matPow Vw o (n + 1)) T))
            = (vecScale (BPair.ofPos (Pos.pow lc (n + 1))) (split.vDiagL
                (matPow Vw o (n + 1)) T)).map BPair.swap
          from rfl,
        ground.getAt_map BPair.unit BPair.unit BPair.swap
          (vecScale (BPair.ofPos (Pos.pow lc (n + 1))) (split.vDiagL (matPow
              Vw o (n + 1)) T)) j
          (by rw [hVsl]; exact hj0),
        getAt_vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
          (split.vDiagL (matPow Vw o (n + 1)) T) j
          (by rw [hdsVl]; exact hj0),
        getAt_vecScale (BPair.ofPos (Pos.pow vc (n + 1)))
          (split.vDiagL (matPow Lw o (n + 1)) T) j
          (by rw [hdsLl]; exact hj0),
        ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
          (matVec Tw.val x) (matVec Tw.val y) j
          (by rw [hXl]; exact hj0) (by rw [hYl]; exact hj0),
        getAt_vecAdd (vecScale (a * a) (List.zipWith (· * ·) (matVec Tw.val
            x) (matVec Tw.val x)))
          (vecScale (b * b) (List.zipWith (· * ·) (matVec Tw.val y) (matVec
              Tw.val y))) j
          (by rw [hVXl]; exact hj0) (by rw [hVYl]; exact hj0),
        getAt_vecScale (a * a)
          (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val x)) j
          (by rw [hZXXl]; exact hj0),
        getAt_vecScale (b * b)
          (List.zipWith (· * ·) (matVec Tw.val y) (matVec Tw.val y)) j
          (by rw [hZYYl]; exact hj0),
        ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
          (matVec Tw.val x) (matVec Tw.val x) j
          (by rw [hXl]; exact hj0) (by rw [hXl]; exact hj0),
        ground.getAt_zipWith BPair.unit BPair.unit BPair.unit (· * ·)
          (matVec Tw.val y) (matVec Tw.val y) j
          (by rw [hYl]; exact hj0) (by rw [hYl]; exact hj0),
        BPair.mul_assoc,
        show BPair.swap (BPair.ofPos (Pos.pow lc (n + 1)) * ground.getAt
            BPair.unit (split.vDiagL (matPow Vw o (n + 1)) T) j)
            + BPair.ofPos (Pos.pow vc (n + 1)) * ground.getAt BPair.unit
                (split.vDiagL (matPow Lw o (n + 1)) T) j
          = (BPair.ofPos (Pos.pow lc (n + 1)) * ground.getAt BPair.unit
              (split.vDiagL (matPow Vw o (n + 1)) T) j
            + (BPair.ofPos (Pos.pow vc (n + 1)) * ground.getAt BPair.unit
                (split.vDiagL (matPow Lw o (n + 1)) T) j).swap).swap
          from rfl,
        BPair.swap_mul, ← BPair.mul_swap, ← BPair.mul_swap]
      have hpol2 := scalarPolar a b
        (ground.getAt BPair.unit (matVec Tw.val x) j)
        ((ground.getAt BPair.unit (matVec Tw.val y) j).swap)
      rw [BPair.swap_sq
        (ground.getAt BPair.unit (matVec Tw.val y) j)] at hpol2
      exact hkey j hj0
        (ground.getAt BPair.unit (matVec Tw.val x) j
          * (ground.getAt BPair.unit (matVec Tw.val y) j).swap) hpol2)
  have eV : (dotP (vecScale (BPair.ofPos (Pos.pow lc (n + 1))) (split.vDiagL
      (matPow Vw o (n + 1)) T))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))).oneValue
      ((minor T.val * minor T.val)
        * ((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow lc (n +
            1)))) := by
    rw [dotP_comm (vecScale (BPair.ofPos (Pos.pow lc (n + 1))) (split.vDiagL
        (matPow Vw o (n + 1)) T))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))]
    refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
    rw [dotP_comm (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
      (split.vDiagL (matPow Vw o (n + 1)) T)]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm hFV)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.ofPos_scale _ _)
  have eL : (dotP (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
      (matPow Lw o (n + 1)) T))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))).oneValue
      ((minor T.val * minor T.val)
        * ((dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n +
            1)))) := by
    rw [dotP_comm (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
        (matPow Lw o (n + 1)) T))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))]
    refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
    rw [dotP_comm (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
      (split.vDiagL (matPow Lw o (n + 1)) T)]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm hFL)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.ofPos_scale _ _)
  have e1 : (dotP (vecScale (a * b) (vecAdd (vecScale (BPair.ofPos (Pos.pow
      lc (n + 1))) (split.vDiagL (matPow Vw o (n + 1)) T))
      (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
          (matPow Lw o (n + 1)) T)))))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))).oneValue
      ((a * b) * ((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow lc
          (n + 1))
          + ((dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n +
              1))).swap)
        * (minor T.val * minor T.val)) := by
    rw [dotP_comm (vecScale (a * b) (vecAdd (vecScale (BPair.ofPos (Pos.pow
        lc (n + 1))) (split.vDiagL (matPow Vw o (n + 1)) T))
      (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
          (matPow Lw o (n + 1)) T)))))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))]
    refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
    rw [dotP_comm (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
      (vecAdd (vecScale (BPair.ofPos (Pos.pow lc (n + 1))) (split.vDiagL
          (matPow Vw o (n + 1)) T))
      (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL
          (matPow Lw o (n + 1)) T))))]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (a * b))
        (dotP_vecAdd_left (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
            (split.vDiagL (matPow Vw o (n + 1)) T))
          (poly.neg (vecScale (BPair.ofPos (Pos.pow vc (n + 1)))
              (split.vDiagL (matPow Lw o (n + 1)) T)))
          (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
          (Nat.le_of_eq (hZXYl.trans hVsl.symm))
          (Nat.le_of_eq (hZXYl.trans hnegLl.symm)))) ?_
    rw [dotP_swap_left (vecScale (BPair.ofPos (Pos.pow vc (n + 1)))
        (split.vDiagL (matPow Lw o (n + 1)) T))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (a * b))
        (BPair.add_congr eV (ground.swap_congr eL))) ?_
    exact BPair.oneValue_of_eq (by
      rw [← BPair.mul_swap (minor T.val * minor T.val)
          ((dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n +
              1))),
        ← BPair.left_distrib (minor T.val * minor T.val)
          ((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow lc (n + 1)))
          (((dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n +
              1))).swap),
        BPair.mul_left_comm (a * b) (minor T.val * minor T.val)
          ((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow lc (n + 1))
            + ((dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n
                + 1))).swap),
        BPair.mul_comm (minor T.val * minor T.val)
          ((a * b) * ((dotP x (matVec (matPow Vw o (n + 1)) y)).scale
              (Pos.pow lc (n + 1))
            + ((dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n
                + 1))).swap))])
  have e1b : (dotP (vecScale (a * b) (vecAdd (poly.neg (vecScale (BPair.ofPos
      (Pos.pow lc (n + 1))) (split.vDiagL (matPow Vw o (n + 1)) T)))
      (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow Lw o
          (n + 1)) T))))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))).oneValue
      ((a * b) * (((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow
          lc (n + 1))).swap
          + (dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n +
              1)))
        * (minor T.val * minor T.val)) := by
    rw [dotP_comm (vecScale (a * b) (vecAdd (poly.neg (vecScale (BPair.ofPos
        (Pos.pow lc (n + 1))) (split.vDiagL (matPow Vw o (n + 1)) T)))
      (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow Lw o
          (n + 1)) T))))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))]
    refine BPair.oneValue_trans (dotP_vecScale_right _ _ _) ?_
    rw [dotP_comm (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
      (vecAdd (poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
          (split.vDiagL (matPow Vw o (n + 1)) T)))
      (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow Lw o
          (n + 1)) T)))]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (a * b))
        (dotP_vecAdd_left (poly.neg (vecScale (BPair.ofPos (Pos.pow lc (n +
            1))) (split.vDiagL (matPow Vw o (n + 1)) T)))
          (vecScale (BPair.ofPos (Pos.pow vc (n + 1))) (split.vDiagL (matPow
              Lw o (n + 1)) T))
          (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))
          (Nat.le_of_eq (hZXYl.trans hnegVl.symm))
          (Nat.le_of_eq (hZXYl.trans hLsl.symm)))) ?_
    rw [dotP_swap_left (vecScale (BPair.ofPos (Pos.pow lc (n + 1)))
        (split.vDiagL (matPow Vw o (n + 1)) T))
      (List.zipWith (· * ·) (matVec Tw.val x) (matVec Tw.val y))]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (a * b))
        (BPair.add_congr (ground.swap_congr eV) eL)) ?_
    exact BPair.oneValue_of_eq (by
      rw [← BPair.mul_swap (minor T.val * minor T.val)
          ((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow lc (n +
              1))),
        ← BPair.left_distrib (minor T.val * minor T.val)
          (((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow lc (n +
              1))).swap)
          ((dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n +
              1))),
        BPair.mul_left_comm (a * b) (minor T.val * minor T.val)
          (((dotP x (matVec (matPow Vw o (n + 1)) y)).scale (Pos.pow lc (n +
              1))).swap
            + (dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n
                + 1))),
        BPair.mul_comm (minor T.val * minor T.val)
          ((a * b) * (((dotP x (matVec (matPow Vw o (n + 1)) y)).scale
              (Pos.pow lc (n + 1))).swap
            + (dotP x (matVec (matPow Lw o (n + 1)) y)).scale (Pos.pow vc (n
                + 1))))])
  have e2 : (dotP (split.vDiagL (idMat o) T)
      (vecAdd (vecScale (a * a) (List.zipWith (· * ·) (matVec Tw.val x)
          (matVec Tw.val x)))
        (vecScale (b * b) (List.zipWith (· * ·) (matVec Tw.val y)
          (matVec Tw.val y))))).oneValue
      (((a * a) * dotP x x + (b * b) * dotP y y)
        * (minor T.val * minor T.val)) := by
    refine BPair.oneValue_trans
      (dotP_vecAdd_right (split.vDiagL (idMat o) T) _ _
        (hVXl.trans hVYl.symm)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (dotP_vecScale_right _ _ _)
        (dotP_vecScale_right _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl (a * a))
          (BPair.oneValue_symm hGX))
        (BPair.mul_congr (BPair.oneValue_refl (b * b))
          (BPair.oneValue_symm hGY))) ?_
    exact BPair.oneValue_of_eq (by
      rw [BPair.mul_left_comm (a * a) (minor T.val * minor T.val)
          (dotP x x),
        BPair.mul_left_comm (b * b) (minor T.val * minor T.val)
          (dotP y y),
        ← BPair.left_distrib (minor T.val * minor T.val)
          ((a * a) * dotP x x) ((b * b) * dotP y y),
        BPair.mul_comm (minor T.val * minor T.val)
          ((a * a) * dotP x x + (b * b) * dotP y y)])
  exact pairPriceCore (ground.sq_pos hdet) hcmp1 hcmp2 e1 e1b e2

set_option genInjectivity false in
/-- One growth step's data: the separation transfer with its
contraction certificate members, the following probe with its head
cap members, and the certificates' split witnesses at the step's
exit order. -/
structure GStep where
  ko : Nat
  T : greenprod.MatQ
  A : Mat
  ln : Pos
  ld : Pos
  cn : Pos
  cd : Pos
  spT : inertia.Split ko
  spU : inertia.Split ko
  spL : inertia.Split ko

/-- The chain's applied vector: each step's transfer against its
probe's action on the deeper fold, the final entry the vector
itself. -/
def tailVec : List GStep → List BPair → List BPair
  | [], y => y
  | s :: ss, y => matVec s.T.1 (matVec s.A (tailVec ss y))

/-- The growth chain at stated orders: per step the transfer's
contraction certificate at the two unit grams and the probe's head
cap at the exit order, the orders threaded head to tail. -/
def growthTail : Nat → List GStep → Nat → Prop
  | kim, [], kfin => kim = kfin
  | kim, s :: ss, kfin =>
    spectator.contractRead s.T (idMat kim) (idMat s.ko)
        s.ln s.ld s.spT
      ∧ inertia.capAt (inertia.matScale s.cd s.A)
          (inertia.matScale s.cn (idMat s.ko))
          s.spU s.spL
      ∧ growthTail s.ko ss kfin

def decGrowthTail :
    ∀ (kim : Nat) (ss : List GStep) (kfin : Nat),
    Decidable (growthTail kim ss kfin)
  | kim, [], kfin => inferInstanceAs (Decidable (kim = kfin))
  | _, s :: ss, kfin =>
    @instDecidableAnd _ _ inferInstance
      (@instDecidableAnd _ _ inferInstance (decGrowthTail s.ko ss kfin))

instance (kim : Nat) (ss : List GStep) (kfin : Nat) :
    Decidable (growthTail kim ss kfin) := decGrowthTail kim ss kfin

/-- The chain's lower clearing: the certificate and cap second
members' squared fold. -/
def growthD (ss : List GStep) : Pos :=
  ground.famFold (· * ·) Pos.one
    (fun s => (s.ld * s.ld)
      * (s.cd * s.cd)) ss

/-- The chain's upper clearing: the certificate factors' cleared
squares against the cap first members' squared fold. -/
def growthN (ss : List GStep) : Pos :=
  ground.famFold (· * ·) Pos.one
    (fun s => (s.ln * s.ln * (s.T.2 * s.T.2))
      * (s.cn * s.cn)) ss

/-- The chain vector carries the entering order. -/
theorem tailVec_len : ∀ (kim : Nat) (ss : List GStep) (kfin : Nat)
    (y : List BPair), growthTail kim ss kfin → y.length = kfin →
    (tailVec ss y).length = kim
  | kim, [], kfin, y, h, hy => by
    have h' : kim = kfin := h
    show y.length = kim
    exact hy.trans h'.symm
  | kim, s :: ss, kfin, y, h, hy => by
    have hc : spectator.contractRead s.T (idMat kim) (idMat s.ko)
        s.ln s.ld s.spT := h.1
    show (matVec s.T.1 (matVec s.A (tailVec ss y))).length = kim
    rw [matVec_length]
    exact (sqAt_len hc.1).symm.trans (idMat_len kim)

/-- The chain's gram collapse: the applied vector's self-pairing at
the lower clearing sits at or below the vector's own at the upper,
each step one certificate ride and one cap square. -/
theorem tailCap : ∀ (kim : Nat) (ss : List GStep) (kfin : Nat)
    (y : List BPair), growthTail kim ss kfin → y.length = kfin →
    (dotN (tailVec ss y) (tailVec ss y)).scale (growthD ss)
      ≤ (dotN y y).scale (growthN ss)
  | _, [], _, y, _, _ => by
    show (dotN y y).scale Pos.one ≤ (dotN y y).scale Pos.one
    exact ground.leB_refl _
  | kim, ⟨ko, T, P, ln, ld, cn, cd, spc, spU, spL⟩ :: ss, kfin, y, h,
      hy => by
    have hc : spectator.contractRead T (idMat kim) (idMat ko) ln ld spc :=
      h.1
    have hcap : inertia.capAt (inertia.matScale cd P)
        (inertia.matScale cn (idMat ko)) spU spL := h.2.1
    have htail : growthTail ko ss kfin := h.2.2
    have hw0 : (tailVec ss y).length = ko :=
      tailVec_len ko ss kfin y htail hy
    have hPl : P.length = ko :=
      (length_matScale cd P).symm.trans (sqAt_len hcap.1)
    have hAlen : (matVec P (tailVec ss y)).length = ko :=
      (matVec_length P (tailVec ss y)).trans hPl
    have hTl : T.1.length = kim := (sqAt_len hc.1).symm.trans (idMat_len kim)
    have hzl : (matVec T.1 (matVec P (tailVec ss y))).length = kim :=
      (matVec_length T.1 (matVec P (tailVec ss y))).trans hTl
    have hw := weight_step T (idMat kim) (idMat ko) ln ld spc hc
      (matVec P (tailVec ss y)) hAlen
    have e1 : (inertia.quadForm (idMat kim)
          (matVec T.1 (matVec P (tailVec ss y)))).oneValue
        (dotN (matVec T.1 (matVec P (tailVec ss y)))
          (matVec T.1 (matVec P (tailVec ss y)))) :=
      dotN_congrR (matVec T.1 (matVec P (tailVec ss y))) _ _
        (inertia.matVec_idMat kim (matVec T.1 (matVec P (tailVec ss y))) hzl)
    have e2 : (inertia.quadForm (idMat ko)
          (matVec P (tailVec ss y))).oneValue
        (dotN (matVec P (tailVec ss y)) (matVec P (tailVec ss y))) :=
      dotN_congrR (matVec P (tailVec ss y)) _ _
        (inertia.matVec_idMat ko (matVec P (tailVec ss y)) hAlen)
    have hw' : (dotN (matVec T.1 (matVec P (tailVec ss y)))
          (matVec T.1 (matVec P (tailVec ss y)))).scale (ld * ld)
        ≤ (dotN (matVec P (tailVec ss y))
            (matVec P (tailVec ss y))).scale (ln * ln * (T.2 * T.2)) :=
      ground.leB_congr (BPair.scale_congr (ld * ld) e1)
        (BPair.scale_congr (ln * ln * (T.2 * T.2)) e2) hw
    have hsq := truncation.cap_sq P cn cd spU spL hcap (tailVec ss y) hw0
    have ih := tailCap ko ss kfin y htail hy
    show (dotN (matVec T.1 (matVec P (tailVec ss y)))
          (matVec T.1 (matVec P (tailVec ss y)))).scale
        (ld * ld * (cd * cd) * growthD ss)
      ≤ (dotN y y).scale
        (ln * ln * (T.2 * T.2) * (cn * cn) * growthN ss)
    have k1 : (dotN (matVec T.1 (matVec P (tailVec ss y)))
            (matVec T.1 (matVec P (tailVec ss y)))).scale
          (ld * ld * (cd * cd) * growthD ss)
        ≤ ((dotN (matVec P (tailVec ss y))
              (matVec P (tailVec ss y))).scale
            (ln * ln * (T.2 * T.2))).scale (cd * cd * growthD ss) := by
      refine ground.leB_congr_left ?_
        (ground.leB_scale hw' (cd * cd * growthD ss))
      refine BPair.oneValue_of_eq ?_
      rw [BPair.scale_scale (dotN (matVec T.1 (matVec P (tailVec ss y)))
            (matVec T.1 (matVec P (tailVec ss y)))) (ld * ld)
          (cd * cd * growthD ss),
        ground.mul_assoc (ld * ld) (cd * cd) (growthD ss)]
    have k2 : ((dotN (matVec P (tailVec ss y))
              (matVec P (tailVec ss y))).scale
            (ln * ln * (T.2 * T.2))).scale (cd * cd * growthD ss)
        ≤ ((dotN (tailVec ss y) (tailVec ss y)).scale (cn * cn)).scale
            (ln * ln * (T.2 * T.2) * growthD ss) := by
      refine ground.leB_congr_left ?_
        (ground.leB_scale hsq (ln * ln * (T.2 * T.2) * growthD ss))
      refine BPair.oneValue_of_eq ?_
      rw [BPair.scale_scale (dotN (matVec P (tailVec ss y))
            (matVec P (tailVec ss y))) (cd * cd)
          (ln * ln * (T.2 * T.2) * growthD ss),
        BPair.scale_scale (dotN (matVec P (tailVec ss y))
            (matVec P (tailVec ss y))) (ln * ln * (T.2 * T.2))
          (cd * cd * growthD ss),
        ground.mul_left_comm (ln * ln * (T.2 * T.2)) (cd * cd)
          (growthD ss)]
    have k3 : ((dotN (tailVec ss y) (tailVec ss y)).scale (cn * cn)).scale
            (ln * ln * (T.2 * T.2) * growthD ss)
        ≤ ((dotN y y).scale (growthN ss)).scale
            (ln * ln * (T.2 * T.2) * (cn * cn)) := by
      refine ground.leB_congr_left ?_
        (ground.leB_scale ih (ln * ln * (T.2 * T.2) * (cn * cn)))
      refine BPair.oneValue_of_eq ?_
      rw [BPair.scale_scale (dotN (tailVec ss y) (tailVec ss y))
          (growthD ss) (ln * ln * (T.2 * T.2) * (cn * cn)),
        BPair.scale_scale (dotN (tailVec ss y) (tailVec ss y)) (cn * cn)
          (ln * ln * (T.2 * T.2) * growthD ss),
        ground.mul_left_comm (growthD ss) (ln * ln * (T.2 * T.2))
          (cn * cn),
        ground.mul_left_comm (cn * cn) (ln * ln * (T.2 * T.2))
          (growthD ss),
        ground.mul_comm (growthD ss) (cn * cn)]
    refine ground.leB_congr_right ?_
      (ground.leB_trans k1 (ground.leB_trans k2 k3))
    refine BPair.oneValue_of_eq ?_
    rw [BPair.scale_scale (dotN y y) (growthN ss)
        (ln * ln * (T.2 * T.2) * (cn * cn)),
      ground.mul_comm (growthN ss) (ln * ln * (T.2 * T.2) * (cn * cn))]

/-- Clause (v)'s growth cap: the chain read's magnitude at the head
cap's polarization sits at or below the two end self-pairings at the
chain's clearings, one cap per probe and one certificate factor per
separation, the head cap free-weighted and every deeper step the
polarization at its own cap's members. -/
theorem growth_cap {k1 : Nat} (A1 : Mat) (cn1 cd1 : Pos)
    (spU1 spL1 : inertia.Split k1)
    (hA1 : inertia.capAt (inertia.matScale cd1 A1)
      (inertia.matScale cn1 (idMat k1)) spU1 spL1)
    (ss : List GStep) (kfin : Nat) (hch : growthTail k1 ss kfin)
    (x y : List BPair) (hx : x.length = k1) (hy : y.length = kfin)
    (a b : BPair) :
    (windowsep.mag ((a * b)
        * dotN x (matVec A1 (tailVec ss y)))).scale
      ((2 * cd1) * growthD ss)
    ≤ ((a * a) * dotN x x).scale (cn1 * growthD ss)
      + ((b * b) * dotN y y).scale (cn1 * growthN ss) := by
  have hzlen : (tailVec ss y).length = k1 :=
    tailVec_len k1 ss kfin y hch hy
  have htail := tailCap k1 ss kfin y hch hy
  -- the folded bound at either direction's polarization
  have hfold : ∀ W : BPair,
      W.scale (2 * cd1)
        ≤ ((a * a) * dotN x x
            + (b * b) * dotN (tailVec ss y) (tailVec ss y)).scale cn1 →
      W.scale ((2 * cd1) * growthD ss)
        ≤ ((a * a) * dotN x x).scale (cn1 * growthD ss)
          + ((b * b) * dotN y y).scale (cn1 * growthN ss) := by
    intro W hW
    have h1 := ground.leB_scale hW (growthD ss)
    rw [BPair.scale_scale, BPair.scale_scale, BPair.scale_add] at h1
    refine ground.leB_trans h1 (ground.leB_add (ground.leB_refl _) ?_)
    have h2 := ground.leB_mulR (ground.unitLeSq b) htail
    rw [BPair.mul_scale, BPair.mul_scale] at h2
    have h3 := ground.leB_scale h2 cn1
    rw [BPair.scale_scale, BPair.scale_scale,
      mul_comm (growthD ss) cn1, mul_comm (growthN ss) cn1] at h3
    exact h3
  have hp1 := truncation.cap_polar A1 cn1 cd1 spU1 spL1 hA1
    x (tailVec ss y) hx hzlen a b
  have hp2 := truncation.cap_polar A1 cn1 cd1 spU1 spL1 hA1
    x (tailVec ss y) hx hzlen a b.swap
  rw [BPair.swap_sq b, BPair.mul_swap a b,
    BPair.swap_mul (a * b)
      (dotN x (matVec A1 (tailVec ss y)))] at hp2
  refine ground.leB_congr_left
    (BPair.ofPos_scale ((2 * cd1) * growthD ss) _) ?_
  refine windowsep.mag_mul_le ?_ ?_
  · exact ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.ofPos_scale ((2 * cd1) * growthD ss) _))
      (hfold _ hp1)
  · exact ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.ofPos_scale ((2 * cd1) * growthD ss) _))
      (hfold _ hp2)


/-- The `k`-th translate of a window vector, the translation's
iterated action. -/
def transVec (T : Mat) (o : Nat) (y : List BPair) (k : Nat) :
    List BPair :=
  matVec (inertia.matPow T o k) y

/-- The translate fold: the sum of the first `n` translates of a
window vector. -/
def transSum (T : Mat) (o : Nat) (y : List BPair) : Nat → List BPair
  | 0 => List.replicate o BPair.unit
  | n + 1 => vecAdd (transSum T o y n) (transVec T o y n)

/-- The descending segment fold: the reads `c (n - j)` at `j`
below `m`, the translate fold's cross terms' own enumeration. -/
private def segFold (c : Nat → BPair) (n : Nat) : Nat → BPair
  | 0 => BPair.unit
  | m + 1 => segFold c n m + c (n - m)

/-- The collection fold at a diagonal read `d` and separation
reads `c`: `n` diagonal terms and `2 (n - s)` terms per
separation `s`, the translate fold's pair reads at their own
counts. -/
def collectFold (d : BPair) (c : Nat → BPair) : Nat → BPair
  | 0 => BPair.unit
  | n + 1 => collectFold d c n + (d + BPair.ofNat 2 * segFold c n n)

/-- The `k`-th translated probe's vector at the state: the
conjugated probe's action on the ground. -/
private def conjVec (T A : Mat) (o : Nat) (psi : List BPair)
    (k : Nat) : List BPair :=
  matVec (inertia.matPow T o k)
    (matVec A (matVec (inertia.matPow (transposeM T) o k) psi))

/-- The translate fold's vector at the state: the sum of the
first `n` translated probes' actions on the ground. -/
def conjSum (T A : Mat) (o : Nat) (psi : List BPair) :
    Nat → List BPair
  | 0 => List.replicate o BPair.unit
  | n + 1 => vecAdd (conjSum T A o psi n) (conjVec T A o psi n)

/-- The stated shape's length read. -/
private theorem transVec_len (T : Mat) (o : Nat)
    (hTl : T.length = o) (y : List BPair) :
    ∀ k, (transVec T o y k).length = o :=
  fun k => (matVec_length (inertia.matPow T o k) y).trans
    (inertia.length_matPow T o hTl k)

/-- The stated shape's length read. -/
private theorem transSum_len (T : Mat) (o : Nat)
    (hTl : T.length = o) (y : List BPair) :
    ∀ n, (transSum T o y n).length = o
  | 0 => length_replicate BPair.unit o
  | n + 1 => length_vecAdd (transSum T o y n) (transVec T o y n) o
      (transSum_len T o hTl y n)
      (transVec_len T o hTl y n)

/-- The stated shape's length read. -/
private theorem conjVec_len (T A : Mat) (o : Nat)
    (hTl : T.length = o) (psi : List BPair) :
    ∀ k, (conjVec T A o psi k).length = o :=
  fun k => (matVec_length (inertia.matPow T o k) _).trans
    (inertia.length_matPow T o hTl k)

/-- The stated shape's length read. -/
private theorem conjSum_len (T A : Mat) (o : Nat)
    (hTl : T.length = o) (psi : List BPair) :
    ∀ n, (conjSum T A o psi n).length = o
  | 0 => length_replicate BPair.unit o
  | n + 1 => length_vecAdd (conjSum T A o psi n) (conjVec T A o psi n) o
      (conjSum_len T A o hTl psi n)
      (conjVec_len T A o hTl psi n)

/-- An orthogonal action keeps the pairing: the transpose walk at
the product's identity read. -/
private theorem dotIso (P : Mat) (o : Nat) (hPr : rowsLen o P)
    (horth : matOneValue (matMul (transposeM P) P)
      (inertia.idMat o))
    (u v : List BPair) (hu : u.length = o) (hv : v.length = o) :
    (dotN (matVec P u) (matVec P v)).oneValue (dotN u v) := by
  have hflip := dotN_transpose_flip P o hPr v (matVec P u) hv
    (matVec_length P u)
  have hinner : poly.oneValue (matVec (transposeM P) (matVec P u)) u :=
    poly.oneValue_trans
      (matVec_comp (transposeM P) P u o hPr hu (rowsLen_transposeM P))
      (poly.oneValue_trans
        (matVec_matOne (matMul (transposeM P) P) (inertia.idMat o)
          u horth)
        (inertia.matVec_idMat o u hu))
  exact BPair.oneValue_trans (BPair.oneValue_symm hflip)
    (BPair.oneValue_trans
      (dotN_congrR v (matVec (transposeM P) (matVec P u)) u hinner)
      (dotN_comm v u))

/-- Two translates' pairing reads the separation's own: the
orthogonality strips the shared prefix. -/
private theorem transStrip (T : Mat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T)
    (horth : matOneValue (matMul (transposeM T) T)
      (inertia.idMat o))
    (y : List BPair) (hy : y.length = o) :
    ∀ j g k, j + g = k →
    (dotN (transVec T o y j) (transVec T o y k)).oneValue
      (dotN y (transVec T o y g))
  | 0, g, k, hk => by
    have hg : g = k := (Nat.zero_add g).symm.trans hk
    rw [← hg]
    exact dotN_congrL (transVec T o y 0) y (transVec T o y g)
      (inertia.matVec_idMat o y hy)
  | j + 1, g, k, hk => by
    have hk' : j + g + 1 = k := (Nat.succ_add j g).symm.trans hk
    rw [← hk']
    have hSj : rowsLen (inertia.matPow T o j).length T := by
      rw [inertia.length_matPow T o hTl j]
      exact hTr
    have hSjg : rowsLen (inertia.matPow T o (j + g)).length T := by
      rw [inertia.length_matPow T o hTl (j + g)]
      exact hTr
    have hc1 := matVec_comp T (inertia.matPow T o j) y o
      (inertia.rowsLen_matPow T o hTl j) hy hSj
    have hc2 := matVec_comp T (inertia.matPow T o (j + g)) y o
      (inertia.rowsLen_matPow T o hTl (j + g)) hy hSjg
    refine BPair.oneValue_trans
      (dotN_congrL (transVec T o y (j + 1))
        (matVec T (transVec T o y j))
        (transVec T o y (j + g + 1))
        (poly.oneValue_symm hc1)) ?_
    refine BPair.oneValue_trans
      (dotN_congrR (matVec T (transVec T o y j))
        (transVec T o y (j + g + 1))
        (matVec T (transVec T o y (j + g)))
        (poly.oneValue_symm hc2)) ?_
    refine BPair.oneValue_trans
      (dotIso T o hTr horth (transVec T o y j)
        (transVec T o y (j + g))
        (transVec_len T o hTl y j)
        (transVec_len T o hTl y (j + g))) ?_
    exact transStrip T o hTl hTr horth y hy j g (j + g) rfl

/-- The cross term's segment read: the partial fold against one
translate enumerates the separations descending. -/
private theorem crossSeg (T : Mat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T)
    (horth : matOneValue (matMul (transposeM T) T)
      (inertia.idMat o))
    (y : List BPair) (hy : y.length = o) (n : Nat) :
    ∀ m, m ≤ n →
    (dotN (transSum T o y m) (transVec T o y n)).oneValue
      (segFold (fun s => dotN y (transVec T o y s)) n m)
  | 0, _ => dotN_nullL _ _ (poly.unitTail_replicate o)
  | m + 1, hm => by
    refine BPair.oneValue_trans
      (dotN_addRow_free (transSum T o y m) (transVec T o y m)
        (transVec T o y n)
        ((transSum_len T o hTl y m).trans
          (transVec_len T o hTl y m).symm)) ?_
    refine BPair.add_congr
      (crossSeg T o hTl hTr horth y hy n m (Nat.le_of_succ_le hm)) ?_
    exact transStrip T o hTl hTr horth y hy m (n - m) n
      (ground.natAddSubCancel (Nat.le_of_succ_le hm))

/-- The translate fold's self-pairing collects the pair reads at
their own counts: `n` diagonal reads and `2 (n - s)` reads per
separation `s`, the orthogonality keying every pair by its
separation. -/
theorem trans_collect (T : Mat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T)
    (horth : matOneValue (matMul (transposeM T) T)
      (inertia.idMat o))
    (y : List BPair) (hy : y.length = o) :
    ∀ n : Nat,
    (dotN (transSum T o y n) (transSum T o y n)).oneValue
      (collectFold (dotN y y)
        (fun s => dotN y (transVec T o y s)) n)
  | 0 => dotN_nullL _ _ (poly.unitTail_replicate o)
  | n + 1 => by
    refine BPair.oneValue_trans
      (dotN_add_expand (transSum T o y n) (transVec T o y n)
        ((transSum_len T o hTl y n).trans
          (transVec_len T o hTl y n).symm)) ?_
    have hab : (dotN (transSum T o y n) (transVec T o y n)).oneValue
        (segFold (fun s => dotN y (transVec T o y s)) n n) :=
      crossSeg T o hTl hTr horth y hy n n (Nat.le_refl n)
    have hdiag : (dotN (transVec T o y n) (transVec T o y n)).oneValue
        (dotN y y) :=
      BPair.oneValue_trans
        (transStrip T o hTl hTr horth y hy n 0 n rfl)
        (dotN_congrR y (transVec T o y 0) y
          (inertia.matVec_idMat o y hy))
    have hcross : (dotN (transSum T o y n) (transVec T o y n)
        + dotN (transVec T o y n) (transSum T o y n)).oneValue
        (BPair.ofNat 2
          * segFold (fun s => dotN y (transVec T o y s)) n n) :=
      BPair.oneValue_trans
        (BPair.add_congr hab
          (BPair.oneValue_trans
            (dotN_comm (transVec T o y n) (transSum T o y n)) hab))
        (BPair.oneValue_symm (BPair.ofNat_two_mul _))
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.add_congr (trans_collect T o hTl hTr horth y hy n) hdiag)
        hcross) ?_
    exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _)

/-- The occupied gap at an at-or-below successor pair. -/
private theorem natSubPos : ∀ m n : Nat, m + 1 ≤ n → 1 ≤ n - m
  | 0, n, h => h
  | m + 1, 0, h => absurd h (Nat.not_succ_le_zero (m + 1))
  | m + 1, n + 1, h => by
    rw [Nat.succ_sub_succ n m]
    exact natSubPos m n (Nat.le_of_succ_le_succ h)

/-- Termwise brackets fold over the segment: each read within its
width of the one term, the fold within the widths' fold of the
count's multiple. -/
private theorem segBracket (B : BPair) (c w : Nat → BPair)
    (n : Nat)
    (hw : ∀ s, 1 ≤ s → s < n + 1 →
      windowsep.mag (c s + B.swap) ≤ w s) :
    ∀ m, m ≤ n →
    windowsep.mag (segFold c n m + (BPair.ofNat m * B).swap)
      ≤ segFold w n m
  | 0, _ => by
    have h1 : (segFold c n 0 + (BPair.ofNat 0 * B).swap).oneValue
        BPair.unit :=
      BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl BPair.unit)
          (ground.swap_congr (BPair.unit_mul B)))
        (BPair.unit_add BPair.unit)
    exact ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.oneValue_trans (windowsep.mag_congr h1)
          (BPair.oneValue_of_eq
            (windowsep.mag_unitLe (ground.leB_refl BPair.unit)))))
      (ground.leB_refl BPair.unit)
  | m + 1, hm => by
    have h2 : (segFold c n (m + 1)
        + (BPair.ofNat (m + 1) * B).swap).oneValue
        (segFold c n m + (BPair.ofNat m * B).swap
          + (c (n - m) + B.swap)) := by
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl (segFold c n (m + 1)))
          (ground.swap_congr (ofNat_succ_mul m B))) ?_
      refine BPair.oneValue_of_eq ?_
      rw [← BPair.swap_add]
      exact BPair.add_add_comm (segFold c n m) (c (n - m))
        ((BPair.ofNat m * B).swap) B.swap
    refine ground.leB_congr_left
      (BPair.oneValue_symm (windowsep.mag_congr h2)) ?_
    refine ground.leB_trans
      (windowsep.mag_add_le
        (segFold c n m + (BPair.ofNat m * B).swap)
        (c (n - m) + B.swap)) ?_
    exact ground.leB_add
      (segBracket B c w n hw m (Nat.le_of_succ_le hm))
      (hw (n - m) (natSubPos m n hm)
        (Nat.lt_succ_of_le (Nat.sub_le n m)))

/-- The collection fold sits within the widths' fold of the
count's multiple: the diagonal within its width at the diagonal
count and each separation within its own at the pair count. -/
private theorem foldBracket (d B wd : BPair) (c w : Nat → BPair)
    (n : Nat)
    (hd : windowsep.mag (d + B.swap) ≤ wd)
    (hw : ∀ s, 1 ≤ s → s < n →
      windowsep.mag (c s + B.swap) ≤ w s) :
    windowsep.mag
        (collectFold d c n + (BPair.ofNat (n * n) * B).swap)
      ≤ collectFold wd w n :=
  match n, hw with
  | 0, _ => by
    have h1 : (collectFold d c 0
        + (BPair.ofNat (0 * 0) * B).swap).oneValue BPair.unit :=
      BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl BPair.unit)
          (ground.swap_congr (BPair.unit_mul B)))
        (BPair.unit_add BPair.unit)
    exact ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.oneValue_trans (windowsep.mag_congr h1)
          (BPair.oneValue_of_eq
            (windowsep.mag_unitLe (ground.leB_refl BPair.unit)))))
      (ground.leB_refl BPair.unit)
  | n + 1, hw => by
    have hseg := segBracket B c w n hw n (Nat.le_refl n)
    have hdb : (BPair.ofNat 2 * segFold c n n
        + (BPair.ofNat 2 * (BPair.ofNat n * B)).swap).oneValue
        ((segFold c n n + (BPair.ofNat n * B).swap)
          + (segFold c n n + (BPair.ofNat n * B).swap)) := by
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.ofNat_two_mul (segFold c n n))
          (ground.swap_congr
            (BPair.ofNat_two_mul (BPair.ofNat n * B)))) ?_
      refine BPair.oneValue_of_eq ?_
      rw [← BPair.swap_add]
      exact BPair.add_add_comm (segFold c n n) (segFold c n n)
        ((BPair.ofNat n * B).swap) ((BPair.ofNat n * B).swap)
    have h3 : windowsep.mag (BPair.ofNat 2 * segFold c n n
          + (BPair.ofNat 2 * (BPair.ofNat n * B)).swap)
        ≤ BPair.ofNat 2 * segFold w n n :=
      ground.leB_congr_left
        (BPair.oneValue_symm (windowsep.mag_congr hdb))
        (ground.leB_congr_right
          (BPair.oneValue_symm (BPair.ofNat_two_mul (segFold w n n)))
          (ground.leB_trans (windowsep.mag_add_le _ _)
            (ground.leB_add hseg hseg)))
    have hnn : (BPair.ofNat (n + n) * B).oneValue
        (BPair.ofNat 2 * (BPair.ofNat n * B)) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.ofNat_add n n)) ?_
      rw [BPair.right_distrib]
      exact BPair.oneValue_symm
        (BPair.ofNat_two_mul (BPair.ofNat n * B))
    have hmulsplit : (BPair.ofNat (n * n + (n + n + 1)) * B).oneValue
        (BPair.ofNat (n * n) * B
          + (B + BPair.ofNat 2 * (BPair.ofNat n * B))) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.ofNat_add (n * n) (n + n + 1))) ?_
      rw [BPair.right_distrib]
      refine BPair.add_congr
        (BPair.oneValue_refl (BPair.ofNat (n * n) * B)) ?_
      refine BPair.oneValue_trans (ofNat_succ_mul (n + n) B) ?_
      refine BPair.oneValue_trans
        (BPair.add_congr hnn (BPair.oneValue_refl B)) ?_
      exact BPair.oneValue_of_eq
        (BPair.add_comm (BPair.ofNat 2 * (BPair.ofNat n * B)) B)
    have hsplit : (collectFold d c (n + 1)
        + (BPair.ofNat ((n + 1) * (n + 1)) * B).swap).oneValue
        ((collectFold d c n + (BPair.ofNat (n * n) * B).swap)
          + ((d + B.swap)
            + (BPair.ofNat 2 * segFold c n n
                + (BPair.ofNat 2 * (BPair.ofNat n * B)).swap))) := by
      rw [ground.sqSucc n]
      refine BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_refl (collectFold d c (n + 1)))
          (ground.swap_congr hmulsplit)) ?_
      refine BPair.oneValue_of_eq ?_
      rw [← BPair.swap_add, ← BPair.swap_add]
      exact (BPair.add_add_comm (collectFold d c n)
          (d + BPair.ofNat 2 * segFold c n n)
          ((BPair.ofNat (n * n) * B).swap)
          (B.swap + (BPair.ofNat 2 * (BPair.ofNat n * B)).swap)).trans
        (congrArg
          (fun t => collectFold d c n
            + (BPair.ofNat (n * n) * B).swap + t)
          (BPair.add_add_comm d (BPair.ofNat 2 * segFold c n n)
            B.swap ((BPair.ofNat 2 * (BPair.ofNat n * B)).swap)))
    refine ground.leB_congr_left
      (BPair.oneValue_symm (windowsep.mag_congr hsplit)) ?_
    refine ground.leB_trans (windowsep.mag_add_le _ _) ?_
    refine ground.leB_trans
      (ground.leB_add (ground.leB_refl _) (windowsep.mag_add_le _ _)) ?_
    show _ ≤ collectFold wd w n + (wd + BPair.ofNat 2 * segFold w n n)
    exact ground.leB_add
      (foldBracket d B wd c w n hd
        (fun s h1 h2 => hw s h1 (Nat.lt_succ_of_lt h2)))
      (ground.leB_add hd h3)

/-- The squared-gap fold's expansion: per term the square splits
at the swap (`BPair.sq_expand_swap`), and the fold collects the
three families. -/
private theorem bvarGo (b : BPair) : ∀ (ps : List Pos)
    (xs : List BPair), xs.length = ps.length →
    (dotP (ps.map BPair.ofPos)
        (xs.map (fun x => (x + b.swap) * (x + b.swap)))).oneValue
      (dotP (ps.map BPair.ofPos) (xs.map (fun x => x * x))
        + (b * b) * ground.bsum BPair.ofPos ps
        + (BPair.ofNat 2
            * (b * dotP (ps.map BPair.ofPos) xs)).swap)
  | [], [], _ =>
    BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.add_congr (BPair.oneValue_refl BPair.unit)
            (BPair.mul_unit (b * b)))
          (ground.swap_congr
            (BPair.oneValue_trans
              (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2))
                (BPair.mul_unit b))
              (BPair.mul_unit (BPair.ofNat 2)))))
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.unit_add BPair.unit)
            (BPair.oneValue_refl BPair.unit))
          (BPair.unit_add BPair.unit)))
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | p :: pt, x :: xt, h => by
    have htail : xt.length = pt.length := Nat.succ.inj h
    show (BPair.ofPos p * ((x + b.swap) * (x + b.swap))
        + dotP (pt.map BPair.ofPos)
            (xt.map fun x => (x + b.swap) * (x + b.swap))).oneValue
      (BPair.ofPos p * (x * x)
          + dotP (pt.map BPair.ofPos) (xt.map fun x => x * x)
        + (b * b) * (BPair.ofPos p + ground.bsum BPair.ofPos pt)
        + (BPair.ofNat 2
            * (b * (BPair.ofPos p * x
                + dotP (pt.map BPair.ofPos) xt))).swap)
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_refl
          (BPair.ofPos p * ((x + b.swap) * (x + b.swap))))
        (bvarGo b pt xt htail)) ?_
    rw [BPair.sq_expand_swap x b,
      BPair.left_distrib (BPair.ofPos p) (x * x + b * b),
      BPair.left_distrib (BPair.ofPos p) (x * x) (b * b),
      BPair.left_distrib (BPair.ofPos p) ((x * b).swap) ((x * b).swap),
      BPair.mul_swap (BPair.ofPos p) (x * b),
      BPair.left_distrib (b * b) (BPair.ofPos p) (ground.bsum BPair.ofPos pt),
      BPair.left_distrib b (BPair.ofPos p * x)
        (dotP (pt.map BPair.ofPos) xt),
      BPair.left_distrib (BPair.ofNat 2) (b * (BPair.ofPos p * x)),
      ← BPair.swap_add,
      BPair.mul_comm (b * b) (BPair.ofPos p),
      BPair.mul_left_comm b (BPair.ofPos p) x,
      BPair.mul_comm b x]
    have hK : ((BPair.ofNat 2 * (BPair.ofPos p * (x * b))).swap).oneValue
        ((BPair.ofPos p * (x * b)).swap
          + (BPair.ofPos p * (x * b)).swap) :=
      BPair.oneValue_trans
        (ground.swap_congr
          (BPair.ofNat_two_mul (BPair.ofPos p * (x * b))))
        (BPair.oneValue_of_eq
          (BPair.swap_add (BPair.ofPos p * (x * b))
            (BPair.ofPos p * (x * b))).symm)
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        ((BPair.add_add_comm
            (BPair.ofPos p * (x * x) + BPair.ofPos p * (b * b))
            ((BPair.ofPos p * (x * b)).swap
              + (BPair.ofPos p * (x * b)).swap)
            (dotP (pt.map BPair.ofPos) (xt.map fun x => x * x)
              + (b * b) * ground.bsum BPair.ofPos pt)
            ((BPair.ofNat 2
                * (b * dotP (pt.map BPair.ofPos) xt)).swap)).trans
          (congrArg
            (fun t => t + ((BPair.ofPos p * (x * b)).swap
              + (BPair.ofPos p * (x * b)).swap
              + (BPair.ofNat 2
                  * (b * dotP (pt.map BPair.ofPos) xt)).swap))
            (BPair.add_add_comm (BPair.ofPos p * (x * x))
              (BPair.ofPos p * (b * b))
              (dotP (pt.map BPair.ofPos) (xt.map fun x => x * x))
              ((b * b) * ground.bsum BPair.ofPos pt))))) ?_
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.oneValue_symm hK)
        (BPair.oneValue_refl _))

/-- The weighted square fold about the mean: the fold of squared
gaps joined to the mean's square at the weight fold reads the
second moments' fold, the cross terms withdrawing at the swap. -/
private theorem bvarFold :
    ∀ (ps : List Pos) (xs : List BPair) (D : Pos) (b : BPair),
    xs.length = ps.length →
    (ground.bsum BPair.ofPos ps).oneValue (BPair.ofPos D) →
    (dotP (ps.map BPair.ofPos) xs).oneValue (BPair.scale b D) →
    ((dotP (ps.map BPair.ofPos)
        (xs.map (fun x => (x + b.swap) * (x + b.swap))))
      + BPair.scale (b * b) D).oneValue
      (dotP (ps.map BPair.ofPos) (xs.map (fun x => x * x))) :=
  fun ps xs D b hlen hW hD => by
    have hE : ((b * b) * ground.bsum BPair.ofPos ps).oneValue (BPair.scale (b * b) D) :=
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (b * b)) hW)
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_comm (b * b) (BPair.ofPos D)))
          (BPair.ofPos_scale D (b * b)))
    have hbD : (b * dotP (ps.map BPair.ofPos) xs).oneValue
        (BPair.scale (b * b) D) :=
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl b) hD)
        (BPair.oneValue_of_eq (BPair.mul_scale b b D))
    have hF : ((BPair.ofNat 2
        * (b * dotP (ps.map BPair.ofPos) xs)).swap).oneValue
        ((BPair.scale (b * b) D).swap + (BPair.scale (b * b) D).swap) :=
      BPair.oneValue_trans
        (ground.swap_congr
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2)) hbD)
            (BPair.ofNat_two_mul (BPair.scale (b * b) D))))
        (BPair.oneValue_of_eq
          (BPair.swap_add (BPair.scale (b * b) D)
            (BPair.scale (b * b) D)).symm)
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans (bvarGo b ps xs hlen)
          (BPair.add_congr
            (BPair.add_congr (BPair.oneValue_refl _) hE) hF))
        (BPair.oneValue_refl (BPair.scale (b * b) D))) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (congrArg (fun t => t + BPair.scale (b * b) D)
          (BPair.add_assoc
            (dotP (ps.map BPair.ofPos) (xs.map fun x => x * x)
              + BPair.scale (b * b) D)
            ((BPair.scale (b * b) D).swap)
            ((BPair.scale (b * b) D).swap)).symm)) ?_
    refine BPair.oneValue_trans
      (BPair.add_swap_self
        ((dotP (ps.map BPair.ofPos) (xs.map fun x => x * x)
            + BPair.scale (b * b) D) + (BPair.scale (b * b) D).swap)
        (BPair.scale (b * b) D)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_assoc
          (dotP (ps.map BPair.ofPos) (xs.map fun x => x * x))
          (BPair.scale (b * b) D)
          ((BPair.scale (b * b) D).swap))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.add_comm (BPair.scale (b * b) D)
              ((BPair.scale (b * b) D).swap)))
          (BPair.swap_add_null
            (BPair.oneValue_refl (BPair.scale (b * b) D))))) ?_
    exact BPair.add_unit _

/-- The transposed action fixes the ground: the fixed read walks
across the product's identity. -/
private theorem fixT' (T : Mat) (o : Nat)
    (hTr : rowsLen o T)
    (horth : matOneValue (matMul (transposeM T) T)
      (inertia.idMat o))
    (psi : List BPair) (hpsi : psi.length = o)
    (hfix : poly.oneValue (matVec T psi) psi) :
    poly.oneValue (matVec (transposeM T) psi) psi :=
  poly.oneValue_trans
    (matVec_congr (transposeM T) psi (matVec T psi)
      (poly.oneValue_symm hfix))
    (poly.oneValue_trans
      (matVec_comp (transposeM T) T psi o hTr hpsi
        (rowsLen_transposeM T))
      (poly.oneValue_trans
        (matVec_matOne (matMul (transposeM T) T) (inertia.idMat o)
          psi horth)
        (inertia.matVec_idMat o psi hpsi)))

/-- The transposed power fixes the ground: the fixed read iterates
across the peeled factors. -/
private theorem fixTPow (T : Mat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T)
    (horth : matOneValue (matMul (transposeM T) T)
      (inertia.idMat o))
    (psi : List BPair) (hpsi : psi.length = o)
    (hfix : poly.oneValue (matVec T psi) psi) :
    ∀ k, poly.oneValue
      (matVec (inertia.matPow (transposeM T) o k) psi) psi
  | 0 => inertia.matVec_idMat o psi hpsi
  | k + 1 =>
    poly.oneValue_trans
      (poly.oneValue_symm
        (matVec_comp (transposeM T)
          (inertia.matPow (transposeM T) o k) psi o
          (inertia.rowsLen_matPow (transposeM T) o
            (transposeLen T hTr hTl) k)
          hpsi
          (rowsLen_cast
            (hTl.trans
              (inertia.length_matPow (transposeM T) o
                (transposeLen T hTr hTl) k).symm)
            (rowsLen_transposeM T))))
      (poly.oneValue_trans
        (matVec_congr (transposeM T)
          (matVec (inertia.matPow (transposeM T) o k) psi) psi
          (fixTPow T o hTl hTr horth psi hpsi hfix k))
        (fixT' T o hTr horth psi hpsi hfix))

/-- The conjugated translate reads the probe vector's translate
at the ground's fixed read: the transposed powers withdraw on the
ground. -/
private theorem conjCollapse (T A : Mat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T)
    (horth : matOneValue (matMul (transposeM T) T)
      (inertia.idMat o))
    (psi : List BPair) (hpsi : psi.length = o)
    (hfix : poly.oneValue (matVec T psi) psi) :
    ∀ k : Nat,
    poly.oneValue (conjVec T A o psi k)
      (transVec T o (matVec A psi) k) :=
  fun k =>
    matVec_congr (inertia.matPow T o k)
      (matVec A (matVec (inertia.matPow (transposeM T) o k) psi))
      (matVec A psi)
      (matVec_congr A
        (matVec (inertia.matPow (transposeM T) o k) psi) psi
        (fixTPow T o hTl hTr horth psi hpsi hfix k))

/-- The segment fold's read at entrywise one-value data. -/
private theorem segFold_congr (c c' : Nat → BPair) (n : Nat)
    (h : ∀ s, (c s).oneValue (c' s)) :
    ∀ m, (segFold c n m).oneValue (segFold c' n m)
  | 0 => BPair.oneValue_refl BPair.unit
  | m + 1 =>
    BPair.add_congr (segFold_congr c c' n h m) (h (n - m))

/-- The segment fold's clearing commutes with the fold. -/
private theorem segFold_scale (c : Nat → BPair) (k : Pos) (n : Nat) :
    ∀ m, (segFold (fun s => (c s).scale k) n m).oneValue
      ((segFold c n m).scale k)
  | 0 => ground.unitScale k
  | m + 1 => by
    show (segFold (fun s => (c s).scale k) n m
        + (c (n - m)).scale k).oneValue
      ((segFold c n m + c (n - m)).scale k)
    rw [BPair.scale_add]
    exact BPair.add_congr (segFold_scale c k n m)
      (BPair.oneValue_refl _)

/-- The collection fold's read at entrywise one-value data. -/
private theorem collectFold_congr (d d' : BPair) (c c' : Nat → BPair)
    (hd : d.oneValue d') (hc : ∀ s, (c s).oneValue (c' s)) :
    ∀ n, (collectFold d c n).oneValue (collectFold d' c' n)
  | 0 => BPair.oneValue_refl BPair.unit
  | n + 1 =>
    BPair.add_congr (collectFold_congr d d' c c' hd hc n)
      (BPair.add_congr hd
        (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2))
          (segFold_congr c c' n hc n)))

/-- The collection fold's clearing commutes with the fold. -/
private theorem collectFold_scale (d : BPair) (c : Nat → BPair)
    (k : Pos) :
    ∀ n, (collectFold (d.scale k) (fun s => (c s).scale k) n).oneValue
      ((collectFold d c n).scale k)
  | 0 => ground.unitScale k
  | n + 1 => by
    show (collectFold (d.scale k) (fun s => (c s).scale k) n
        + (d.scale k
          + BPair.ofNat 2
            * segFold (fun s => (c s).scale k) n n)).oneValue
      ((collectFold d c n + (d + BPair.ofNat 2 * segFold c n n)).scale k)
    rw [BPair.scale_add, BPair.scale_add]
    refine BPair.add_congr (collectFold_scale d c k n)
      (BPair.add_congr (BPair.oneValue_refl _) ?_)
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat 2))
        (segFold_scale c k n n)) ?_
    exact BPair.oneValue_of_eq (BPair.mul_scale (BPair.ofNat 2) (segFold c n n) k)

/-- The translate fold's vector at the state reads the probe
vector's translate fold, the collapse folded. -/
private theorem conjSum_collapse (T A : Mat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T)
    (horth : matOneValue (matMul (transposeM T) T)
      (inertia.idMat o))
    (psi : List BPair) (hpsi : psi.length = o)
    (hfix : poly.oneValue (matVec T psi) psi) :
    ∀ n, poly.oneValue (conjSum T A o psi n)
      (transSum T o (matVec A psi) n)
  | 0 => poly.oneValue_refl _
  | n + 1 =>
    vecAdd_congr2 _ _ _ _
      ((conjSum_len T A o hTl psi n).trans
        (transSum_len T o hTl (matVec A psi) n).symm)
      ((conjVec_len T A o hTl psi n).trans
        (transVec_len T o hTl (matVec A psi) n).symm)
      (conjSum_collapse T A o hTl hTr horth psi hpsi hfix n)
      (conjCollapse T A o hTl hTr horth psi hpsi hfix n)

/-- `thm:groundreads` (v$'$), the decomposition display: at a
convex splitting of the state into translation-invariant
components — the weights folding to one, each component's fold
read at the probe's by the invariance and its fold square at or
beyond its mean square by the pairing's positivity — the weighted
square fold of the component means about the state's sits below
the widths' read: the diagonal's own gap at the mean's weight
joined to the off-diagonal clustering widths at the collection's
own counts, one located bracket per probe at every translate
count. -/
theorem decomp_display (T A : Mat) (o : Nat)
    (hTl : T.length = o) (hTr : rowsLen o T) (hA : sqAt A o)
    (horth : matOneValue (matMul (transposeM T) T) (inertia.idMat o))
    (psi : List BPair) (hpsi : psi.length = o)
    (hfix : poly.oneValue (matVec T psi) psi)
    (dp c D : Pos) (ps : List Pos) (as ss qs : List BPair)
    (hasl : as.length = ps.length)
    (hD : (ground.bsum BPair.ofPos ps).oneValue (BPair.ofPos D))
    (hinv : ∀ i, i < ps.length →
      (ground.getAt BPair.unit ss i).oneValue
        (ground.getAt BPair.unit as i))
    (hpos : ∀ i, i < ps.length →
      ground.getAt BPair.unit ss i * ground.getAt BPair.unit ss i
        ≤ BPair.scale (ground.getAt BPair.unit qs i) c)
    (n : Nat)
    (hsplitA : (BPair.scale (dotN psi (matVec A psi)) (D * c)).oneValue
      (BPair.scale (dotP (ps.map BPair.ofPos) as) dp))
    (hsplitQ : (BPair.scale
        (dotN (conjSum T A o psi n) (conjSum T A o psi n))
        (D * c)).oneValue
      (BPair.ofNat (n * n)
        * BPair.scale (dotP (ps.map BPair.ofPos) qs) dp))
    (ws : Nat → BPair)
    (hw : ∀ s, 1 ≤ s → s < n →
      windowsep.mag (readGap
          (dotN (matVec A psi) (transVec T o (matVec A psi) s),
            BPair.ofPos dp)
          (dotN psi (matVec A psi) * dotN psi (matVec A psi),
            BPair.ofPos (dp * dp)))
        ≤ ws s) :
    BPair.ofNat (n * n)
      * BPair.scale
          (dotP (ps.map BPair.ofPos)
            (as.map (fun a =>
              (BPair.scale a dp
                  + (BPair.scale (dotN psi (matVec A psi)) c).swap)
                * (BPair.scale a dp
                  + (BPair.scale (dotN psi (matVec A psi)) c).swap))))
          dp
      ≤ BPair.scale
          (collectFold
            (windowsep.mag (readGap
              (dotN (matVec A psi) (matVec A psi), BPair.ofPos dp)
              (dotN psi (matVec A psi) * dotN psi (matVec A psi),
                BPair.ofPos (dp * dp))))
            ws n)
          (D * (c * c)) := by
  have hy : (matVec A psi).length = o :=
    (matVec_length A psi).trans (sqAt_len hA)
  have hXs : (dotP (ps.map BPair.ofPos)
        (as.map (fun a => a.scale dp))).oneValue
      ((dotP (ps.map BPair.ofPos) as).scale dp) := by
    refine BPair.oneValue_trans
      (dotP_oneValue_right (ps.map BPair.ofPos) _ _
        (greenprod.vecScale_ofPos dp as)) ?_
    refine BPair.oneValue_trans
      (dotP_vecScale_right (ps.map BPair.ofPos) as (BPair.ofPos dp)) ?_
    exact BPair.ofPos_scale dp (dotP (ps.map BPair.ofPos) as)
  have hb' : (dotP (ps.map BPair.ofPos)
        (as.map (fun a => a.scale dp))).oneValue
      (BPair.scale (BPair.scale (dotN psi (matVec A psi)) c) D) := by
    refine BPair.oneValue_trans hXs ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm hsplitA) ?_
    rw [BPair.scale_scale, ground.mul_comm c D]
    exact BPair.oneValue_refl _
  have hbv0 := bvarFold ps (as.map (fun a => a.scale dp)) D
    (BPair.scale (dotN psi (matVec A psi)) c)
    ((ground.length_map _ as).trans hasl) hD hb'
  rw [ground.map_map (fun a => a.scale dp)
      (fun x => (x + (BPair.scale (dotN psi (matVec A psi)) c).swap)
        * (x + (BPair.scale (dotN psi (matVec A psi)) c).swap)) as,
    ground.map_map (fun a => a.scale dp) (fun x => x * x) as] at hbv0
  have hbv : (dotP (ps.map BPair.ofPos)
        (as.map (fun a =>
          (BPair.scale a dp
              + (BPair.scale (dotN psi (matVec A psi)) c).swap)
            * (BPair.scale a dp
              + (BPair.scale (dotN psi (matVec A psi)) c).swap)))
      + BPair.scale
          (BPair.scale (dotN psi (matVec A psi)) c
            * BPair.scale (dotN psi (matVec A psi)) c) D).oneValue
      (dotP (ps.map BPair.ofPos)
        (as.map (fun a => BPair.scale a dp * BPair.scale a dp))) := hbv0
  have hmono0 := dotP_le_of_leTerm Pos.one (c * (dp * dp))
    (ps.map BPair.ofPos)
    (as.map (fun a => BPair.scale a dp * BPair.scale a dp))
    (ps.map BPair.ofPos) qs rfl
    (fun j hj => by
      have hj' : j < ps.length := by
        rw [ground.length_map BPair.ofPos ps] at hj
        exact hj
      have e1 : ground.getAt BPair.unit (ps.map BPair.ofPos) j
          = BPair.ofPos (ground.getAt Pos.one ps j) :=
        ground.getAt_map Pos.one BPair.unit BPair.ofPos ps j hj'
      have e2 : ground.getAt BPair.unit
            (as.map (fun a => BPair.scale a dp * BPair.scale a dp)) j
          = BPair.scale (ground.getAt BPair.unit as j) dp
            * BPair.scale (ground.getAt BPair.unit as j) dp :=
        ground.getAt_map BPair.unit BPair.unit _ as j
          (by rw [hasl]; exact hj')
      have h1 : (ground.getAt BPair.unit as j
            * ground.getAt BPair.unit as j).oneValue
          (ground.getAt BPair.unit ss j
            * ground.getAt BPair.unit ss j) :=
        BPair.mul_congr (BPair.oneValue_symm (hinv j hj'))
          (BPair.oneValue_symm (hinv j hj'))
      have h2 : ground.getAt BPair.unit as j
            * ground.getAt BPair.unit as j
          ≤ BPair.scale (ground.getAt BPair.unit qs j) c :=
        ground.leB_congr_left (BPair.oneValue_symm h1) (hpos j hj')
      have h3 := ground.leB_scale h2 (dp * dp)
      rw [BPair.scale_scale] at h3
      have hsq : BPair.scale (ground.getAt BPair.unit as j) dp
            * BPair.scale (ground.getAt BPair.unit as j) dp
          ≤ BPair.scale (ground.getAt BPair.unit qs j)
              (c * (dp * dp)) :=
        ground.leB_congr_left
          (BPair.oneValue_of_eq
            (BPair.scale_mul (ground.getAt BPair.unit as j)
              (ground.getAt BPair.unit as j) dp dp)) h3
      rw [e1, e2, BPair.scale_one]
      refine ground.leB_congr_right
        (BPair.oneValue_of_eq
          (BPair.mul_scale (BPair.ofPos (ground.getAt Pos.one ps j))
            (ground.getAt BPair.unit qs j) (c * (dp * dp)))) ?_
      exact ground.leB_mulR
        (ground.leB_of_lt
          (ground.unitLtOfPos (ground.getAt Pos.one ps j))) hsq)
  have hmono : dotP (ps.map BPair.ofPos)
        (as.map (fun a => BPair.scale a dp * BPair.scale a dp))
      ≤ BPair.scale (dotP (ps.map BPair.ofPos) qs) (c * (dp * dp)) :=
    ground.leB_congr_left
      (BPair.oneValue_of_eq (BPair.scale_one _)) hmono0
  have hchain1 : dotP (ps.map BPair.ofPos)
        (as.map (fun a =>
          (BPair.scale a dp
              + (BPair.scale (dotN psi (matVec A psi)) c).swap)
            * (BPair.scale a dp
              + (BPair.scale (dotN psi (matVec A psi)) c).swap)))
      + BPair.scale
          (BPair.scale (dotN psi (matVec A psi)) c
            * BPair.scale (dotN psi (matVec A psi)) c) D
      ≤ BPair.scale (dotP (ps.map BPair.ofPos) qs) (c * (dp * dp)) :=
    ground.leB_congr_left (BPair.oneValue_symm hbv) hmono
  have hc2 := ground.leB_mulR (ground.unitLeOfNat (n * n))
    (ground.leB_scale hchain1 dp)
  have hr1 : (BPair.ofNat (n * n)
        * ((BPair.scale (dotP (ps.map BPair.ofPos) qs)
            (c * (dp * dp))).scale dp)).oneValue
      ((dotN (conjSum T A o psi n) (conjSum T A o psi n)).scale
        ((D * c) * (c * (dp * dp)))) := by
    rw [BPair.scale_scale, ground.mul_comm (c * (dp * dp)) dp,
      ← BPair.scale_scale]
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_scale (BPair.ofNat (n * n)) _ (c * (dp * dp)))) ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (c * (dp * dp))
        (BPair.oneValue_symm hsplitQ)) ?_
    rw [BPair.scale_scale]
    exact BPair.oneValue_refl _
  have hcol := conjSum_collapse T A o hTl hTr horth psi hpsi hfix n
  have hcv : (dotN (conjSum T A o psi n)
        (conjSum T A o psi n)).oneValue
      (collectFold (dotN (matVec A psi) (matVec A psi))
        (fun s => dotN (matVec A psi) (transVec T o (matVec A psi) s))
        n) :=
    BPair.oneValue_trans (dotN_congrL _ _ _ hcol)
      (BPair.oneValue_trans (dotN_congrR _ _ _ hcol)
        (trans_collect T o hTl hTr horth (matVec A psi) hy n))
  have hswapEq : ∀ x : BPair,
      (x * BPair.ofPos (dp * dp)
        + ((dotN psi (matVec A psi) * dotN psi (matVec A psi))
            * BPair.ofPos dp).swap)
      = (readGap (x, BPair.ofPos dp)
          (dotN psi (matVec A psi) * dotN psi (matVec A psi),
            BPair.ofPos (dp * dp))).swap := by
    intro x
    show x * BPair.ofPos (dp * dp)
        + ((dotN psi (matVec A psi) * dotN psi (matVec A psi))
            * BPair.ofPos dp).swap
      = ((dotN psi (matVec A psi) * dotN psi (matVec A psi))
          * BPair.ofPos dp
        + (x * BPair.ofPos (dp * dp)).swap).swap
    rw [← BPair.swap_add, BPair.swap_swap, BPair.add_comm]
  have hd' : windowsep.mag
      (dotN (matVec A psi) (matVec A psi) * BPair.ofPos (dp * dp)
        + ((dotN psi (matVec A psi) * dotN psi (matVec A psi))
            * BPair.ofPos dp).swap)
      ≤ windowsep.mag (readGap
          (dotN (matVec A psi) (matVec A psi), BPair.ofPos dp)
          (dotN psi (matVec A psi) * dotN psi (matVec A psi),
            BPair.ofPos (dp * dp))) := by
    rw [hswapEq (dotN (matVec A psi) (matVec A psi)),
      windowsep.mag_swap]
    exact ground.leB_refl _
  have hw' : ∀ s, 1 ≤ s → s < n →
      windowsep.mag
        (dotN (matVec A psi) (transVec T o (matVec A psi) s)
            * BPair.ofPos (dp * dp)
          + ((dotN psi (matVec A psi) * dotN psi (matVec A psi))
              * BPair.ofPos dp).swap)
        ≤ ws s := by
    intro s hs1 hsn
    rw [hswapEq (dotN (matVec A psi) (transVec T o (matVec A psi) s)),
      windowsep.mag_swap]
    exact hw s hs1 hsn
  have hfb := foldBracket
    (dotN (matVec A psi) (matVec A psi) * BPair.ofPos (dp * dp))
    ((dotN psi (matVec A psi) * dotN psi (matVec A psi))
      * BPair.ofPos dp)
    (windowsep.mag (readGap
      (dotN (matVec A psi) (matVec A psi), BPair.ofPos dp)
      (dotN psi (matVec A psi) * dotN psi (matVec A psi),
        BPair.ofPos (dp * dp))))
    (fun s => dotN (matVec A psi) (transVec T o (matVec A psi) s)
      * BPair.ofPos (dp * dp))
    ws n hd' hw'
  have hup := ground.leB_swapL (ground.leB_trans (windowsep.le_mag _) hfb)
  have hclr : (collectFold
        (dotN (matVec A psi) (matVec A psi) * BPair.ofPos (dp * dp))
        (fun s => dotN (matVec A psi) (transVec T o (matVec A psi) s)
          * BPair.ofPos (dp * dp)) n).oneValue
      ((collectFold (dotN (matVec A psi) (matVec A psi))
        (fun s => dotN (matVec A psi) (transVec T o (matVec A psi) s))
        n).scale (dp * dp)) :=
    BPair.oneValue_trans
      (collectFold_congr _ _ _ _
        (BPair.mul_ofPos (dotN (matVec A psi) (matVec A psi)) (dp * dp))
        (fun s => BPair.mul_ofPos
          (dotN (matVec A psi) (transVec T o (matVec A psi) s))
          (dp * dp)) n)
      (collectFold_scale (dotN (matVec A psi) (matVec A psi))
        (fun s => dotN (matVec A psi) (transVec T o (matVec A psi) s))
        (dp * dp) n)
  have hqbound := ground.leB_congr_left hclr hup
  have hqb2 := ground.leB_scale hqbound (D * (c * c))
  rw [BPair.scale_scale] at hqb2
  have hposEq : (dp * dp) * (D * (c * c)) = (D * c) * (c * (dp * dp)) := by
    rw [ground.mul_comm (dp * dp) (D * (c * c)),
      ground.mul_assoc D (c * c) (dp * dp),
      ground.mul_assoc D c (c * (dp * dp)),
      ground.mul_assoc c c (dp * dp)]
  rw [hposEq] at hqb2
  have hlink : BPair.ofNat (n * n)
      * ((dotP (ps.map BPair.ofPos)
          (as.map (fun a =>
            (BPair.scale a dp
                + (BPair.scale (dotN psi (matVec A psi)) c).swap)
              * (BPair.scale a dp
                + (BPair.scale (dotN psi (matVec A psi)) c).swap)))
        + BPair.scale
            (BPair.scale (dotN psi (matVec A psi)) c
              * BPair.scale (dotN psi (matVec A psi)) c) D).scale dp)
      ≤ (collectFold
            (windowsep.mag (readGap
              (dotN (matVec A psi) (matVec A psi), BPair.ofPos dp)
              (dotN psi (matVec A psi) * dotN psi (matVec A psi),
                BPair.ofPos (dp * dp)))) ws n
          + BPair.ofNat (n * n)
            * ((dotN psi (matVec A psi)
                * dotN psi (matVec A psi)) * BPair.ofPos dp)).scale
          (D * (c * c)) := by
    refine ground.leB_trans (ground.leB_congr_right hr1 hc2) ?_
    refine ground.leB_congr_left
      (BPair.oneValue_symm
        (BPair.scale_congr ((D * c) * (c * (dp * dp))) hcv)) ?_
    exact hqb2
  rw [BPair.scale_add, BPair.left_distrib, BPair.scale_add] at hlink
  have hZ : (BPair.ofNat (n * n)
        * ((BPair.scale
            (BPair.scale (dotN psi (matVec A psi)) c
              * BPair.scale (dotN psi (matVec A psi)) c) D).scale
          dp)).oneValue
      ((BPair.ofNat (n * n)
        * ((dotN psi (matVec A psi)
            * dotN psi (matVec A psi)) * BPair.ofPos dp)).scale
        (D * (c * c))) := by
    rw [← BPair.scale_mul (dotN psi (matVec A psi))
        (dotN psi (matVec A psi)) c c,
      BPair.scale_scale, BPair.scale_scale]
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_scale (BPair.ofNat (n * n))
          (dotN psi (matVec A psi) * dotN psi (matVec A psi))
          ((c * c) * (D * dp)))) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (D * (c * c))
        (BPair.mul_congr
          (BPair.oneValue_refl (BPair.ofNat (n * n)))
          (BPair.mul_ofPos (dotN psi (matVec A psi)
            * dotN psi (matVec A psi)) dp))) ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (D * (c * c))
        (BPair.oneValue_of_eq
          (BPair.mul_scale (BPair.ofNat (n * n))
            (dotN psi (matVec A psi) * dotN psi (matVec A psi)) dp))) ?_
    rw [BPair.scale_scale]
    have e : dp * (D * (c * c)) = (c * c) * (D * dp) := by
      rw [ground.mul_comm dp (D * (c * c)),
        ground.mul_comm D (c * c), ground.mul_assoc (c * c) D dp]
    rw [e]
    exact BPair.oneValue_refl _
  refine ground.leB_cancelL
    (x := BPair.ofNat (n * n)
      * ((BPair.scale
          (BPair.scale (dotN psi (matVec A psi)) c
            * BPair.scale (dotN psi (matVec A psi)) c) D).scale dp))
    ?_
  refine ground.leB_congr
    (BPair.oneValue_of_eq (BPair.add_comm _ _))
    (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
  refine ground.leB_congr_right
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm hZ)) ?_
  exact hlink


/-! Clause (vi): the reach tier, the sandwich, the disjoint-support
annihilation, and the cap's power read. -/

/-- The two-sided keep at a boundary pair: every entry with its row
before the first boundary and its column at or beyond the second,
or the mirrored pair, reads the sum's unit. -/
def reachKeep (M : Mat) (p q : Nat) : Prop :=
  ∀ r, r < M.length → ∀ c, c < (ground.getAt [] M r).length →
    ((r < p ∧ q ≤ c) ∨ (c < p ∧ q ≤ r)) →
    (ground.getAt BPair.unit (ground.getAt [] M r) c).oneValue
      BPair.unit

instance (M : Mat) (p q : Nat) : Decidable (reachKeep M p q) :=
  Nat.decidableBallLT _ _

/-- The banded read: the keep at every consecutive boundary pair of
the list. -/
def bandedAt (M : Mat) (ns : List Nat) : Prop :=
  ∀ j, j < ns.length →
    reachKeep M (ground.prefixAt j ns) (ground.prefixAt (j + 1) ns)

instance (M : Mat) (ns : List Nat) : Decidable (bandedAt M ns) :=
  Nat.decidableBallLT _ _

/-- The leading support: every entry at a row or column key at or
beyond the boundary reads the sum's unit. -/
def leadAt (M : Mat) (p : Nat) : Prop :=
  ∀ r, r < M.length → ∀ c, c < (ground.getAt [] M r).length →
    (p ≤ r ∨ p ≤ c) →
    (ground.getAt BPair.unit (ground.getAt [] M r) c).oneValue
      BPair.unit

instance (M : Mat) (p : Nat) : Decidable (leadAt M p) :=
  Nat.decidableBallLT _ _

/-- The trailing support: every entry at a row or column key before
the boundary reads the sum's unit. -/
def tailAt (M : Mat) (q : Nat) : Prop :=
  ∀ r, r < M.length → ∀ c, c < (ground.getAt [] M r).length →
    (r < q ∨ c < q) →
    (ground.getAt BPair.unit (ground.getAt [] M r) c).oneValue
      BPair.unit

instance (M : Mat) (q : Nat) : Decidable (tailAt M q) :=
  Nat.decidableBallLT _ _

/-- The skipping fold sits at the sum's unit where at every key one of
the two members does. -/
private theorem dotN_unitOr : ∀ (u v : List BPair),
    (∀ i, i < u.length → i < v.length →
      (ground.getAt BPair.unit u i).oneValue BPair.unit
      ∨ (ground.getAt BPair.unit v i).oneValue BPair.unit) →
    (elim.dotN u v).oneValue BPair.unit
  | [], _, _ => BPair.oneValue_refl _
  | _ :: _, [], _ => BPair.oneValue_refl _
  | a :: s, b :: t, h => by
    have hrest : (elim.dotN s t).oneValue BPair.unit :=
      dotN_unitOr s t (fun i hi hj =>
        h (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj))
    show (if a.isUnitRep || b.isUnitRep then elim.dotN s t
        else (a * b + elim.dotN s t).norm).oneValue BPair.unit
    cases hab : a.isUnitRep || b.isUnitRep with
    | true =>
      rw [if_pos rfl]
      exact hrest
    | false =>
      rw [if_neg (fun hc : (false : Bool) = true => Bool.noConfusion hc)]
      have habU : (a * b).oneValue BPair.unit :=
        match h 0 (Nat.succ_pos _) (Nat.succ_pos _) with
        | Or.inl ha =>
          BPair.oneValue_trans
            (BPair.mul_congr ha (BPair.oneValue_refl b))
            (BPair.unit_mul b)
        | Or.inr hb =>
          BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl a) hb)
            (BPair.mul_unit a)
      exact BPair.oneValue_trans (BPair.norm_oneValue _)
        (BPair.oneValue_trans
          (BPair.add_congr habU hrest)
          (BPair.unit_add BPair.unit))

/-- A null matrix's action pairs every vector at the sum's unit. -/
private theorem matNull_dotP (Z : Mat) (h : elim.matNull Z) :
    ∀ (x y : List BPair),
    (elim.dotP x (elim.matVec Z y)).oneValue BPair.unit :=
  fun x y =>
    elim.dotP_null_tail_right x (elim.matVec Z y)
      (elim.matVec_matNull Z y h)

/-- Two matrices of vacant row count read one value. -/
private theorem matOne_of_len_zero : ∀ (A B : Mat),
    A.length = 0 → B.length = 0 → elim.matOneValue A B
  | [], [], _, _ => trivial
  | [], _ :: _, _, hB => Nat.noConfusion hB
  | _ :: _, _, hA, _ => Nat.noConfusion hA

/-- A symmetric datum's powers are symmetric. -/
private theorem transposeM_matPow {o : Nat} (M : Mat)
    (hM : sqAt M o) (hsym : elim.matOneValue (elim.transposeM M) M) :
    ∀ k, elim.matOneValue (elim.transposeM (matPow M o k))
      (matPow M o k) := by
  have hMl : M.length = o := sqAt_len hM
  have hMr : rowsLen o M := rowsLen_of_sqAt hM
  cases o with
  | zero =>
    intro k
    exact matOne_of_len_zero _ _
      (transposeLen (matPow M 0 k) (rowsLen_matPow M 0 hMl k)
        (length_matPow M 0 hMl k))
      (length_matPow M 0 hMl k)
  | succ o0 =>
    have ho : 0 < o0 + 1 := Nat.succ_pos o0
    intro k
    induction k with
    | zero =>
      show elim.matOneValue (elim.transposeM (idMat (o0 + 1))) (idMat (o0 + 1))
      rw [transposeM_idMat (o0 + 1)]
      exact matOne_refl _
    | succ k ih =>
      have hPr : rowsLen (o0 + 1) (matPow M (o0 + 1) k) :=
        rowsLen_matPow M (o0 + 1) hMl k
      have hPl : (matPow M (o0 + 1) k).length = o0 + 1 :=
        length_matPow M (o0 + 1) hMl k
      have hTMl : (elim.transposeM M).length = o0 + 1 :=
        length_transposeM M hMr (by rw [hMl]; exact ho)
      have hTMr : rowsLen (o0 + 1) (elim.transposeM M) :=
        rowsLen_cast hMl (rowsLen_transposeM M)
      show elim.matOneValue
        (elim.transposeM (matMul M (matPow M (o0 + 1) k)))
        (matMul M (matPow M (o0 + 1) k))
      refine matOne_trans
        (transposeM_matMul (r := o0 + 1) (n := o0 + 1) (k := o0 + 1)
          M (matPow M (o0 + 1) k) hMr hPr hMl hPl ho ho) ?_
      refine matOne_trans
        (matMul_congrL _ _ (elim.transposeM M) ih) ?_
      refine matOne_trans
        (matMul_congrR (n := o0 + 1) (k := o0 + 1)
          (matPow M (o0 + 1) k) (elim.transposeM M) M
          hTMr hMr hTMl hMl ho hsym) ?_
      exact matPow_succR (o0 + 1) M hMl hMr ho k

/-- The product's entry sits at the sum's unit where at every key one
of the two factors' entries does. -/
private theorem matMul_entry_unit {n : Nat} (X Y : Mat)
    (hXr : rowsLen n X) (hYl : Y.length = n) (hYr : rowsLen n Y)
    (r c : Nat) (hr : r < X.length) (hc : c < n)
    (h : ∀ i, i < n →
      (ground.getAt BPair.unit (ground.getAt ([] : List BPair) X r) i).oneValue
        BPair.unit
      ∨ (ground.getAt BPair.unit (ground.getAt ([] : List BPair) Y i) c).oneValue
        BPair.unit) :
    (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (matMul X Y) r) c).oneValue
      BPair.unit := by
  have hYt : (transposeM Y).length = n := transposeLen Y hYr hYl
  have hct : c < (transposeM Y).length := by rw [hYt]; exact hc
  have hcol : (ground.getAt ([] : List BPair) (transposeM Y) c).length
      = n := by
    rw [rowsLen_getAt (transposeM Y) c (rowsLen_transposeM Y) hct]
    exact hYl
  rw [getAt_matMul X Y r hr,
    ground.getAt_map ([] : List BPair) BPair.unit
      (fun cc => dotN (ground.getAt [] X r) cc) (transposeM Y) c hct]
  refine dotN_unitOr _ _ (fun i hi _ => ?_)
  rw [rowsLen_getAt X r hXr hr] at hi
  rw [getAt_transposeM BPair.unit Y hYr c i hc (by rw [hYl]; exact hi)]
  exact h i hi

/-- The row read's converse: every row a unit tail is the null read. -/
private theorem matNull_of_rows : ∀ (M : Mat),
    (∀ i, i < M.length →
      poly.unitTail (ground.getAt ([] : List BPair) M i)) →
    elim.matNull M
  | [], _ => trivial
  | _ :: t, h =>
    ⟨h 0 (Nat.succ_pos _),
     matNull_of_rows t (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))⟩

/-- The entry read's converse at a stated width. -/
private theorem matNull_of_entries {n : Nat} (M : Mat)
    (hMr : rowsLen n M)
    (h : ∀ r, r < M.length → ∀ c, c < n →
      (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) M r) c).oneValue BPair.unit) :
    elim.matNull M := by
  refine matNull_of_rows M (fun i hi => ?_)
  refine elim.unitTail_of_getAt _ (fun p hp => ?_)
  rw [rowsLen_getAt M i hMr hi] at hp
  exact h i hi p hp

/-- A banded datum's powers keep the widened boundaries. -/
theorem pow_reach {o : Nat} (M : Mat) (hM : sqAt M o) (ns : List Nat)
    (hns : ground.prefixAt ns.length ns = o) (hband : bandedAt M ns)
    (j k : Nat) :
    reachKeep (matPow M o k) (ground.prefixAt j ns)
      (ground.prefixAt (j + k) ns) := by
  have hMl : M.length = o := sqAt_len hM
  have hMr : rowsLen o M := rowsLen_of_sqAt hM
  have hclamp : ∀ m : Nat, ns.length ≤ m → ground.prefixAt m ns = o := by
    intro m hm
    rw [ground.prefixAt_full ns m hm,
      ← ground.prefixAt_full ns ns.length (Nat.le_refl _)]
    exact hns
  induction k generalizing j with
  | zero =>
    intro r hr c hc harm
    have hr' : r < o := by
      have h0 : r < (idMat o).length := hr
      rw [idMat_len o] at h0
      exact h0
    have hri : r < (idMat o).length := by rw [idMat_len o]; exact hr'
    have hc' : c < o := by
      have h0 : c < (ground.getAt ([] : List BPair) (idMat o) r).length := hc
      rw [rowsLen_getAt (idMat o) r (idMat_rows o) hri] at h0
      exact h0
    have hne : ¬ (c = r) := by
      intro he
      match harm with
      | Or.inl ⟨h1, h2⟩ =>
        rw [he] at h2
        exact Nat.lt_irrefl r (Nat.lt_of_lt_of_le h1 h2)
      | Or.inr ⟨h1, h2⟩ =>
        rw [← he] at h2
        exact Nat.lt_irrefl c (Nat.lt_of_lt_of_le h1 h2)
    show (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (idMat o) r) c).oneValue BPair.unit
    rw [getAt_idMat o r c hr' hc', if_neg hne]
    exact BPair.oneValue_refl _
  | succ k ih =>
    have hPl : (matPow M o k).length = o := length_matPow M o hMl k
    have hPr : rowsLen o (matPow M o k) := rowsLen_matPow M o hMl k
    intro r hr c hc harm
    have hr' : r < o := by
      have h0 : r < (matMul M (matPow M o k)).length := hr
      rw [length_matMul M (matPow M o k), hMl] at h0
      exact h0
    have hrM : r < M.length := by rw [hMl]; exact hr'
    have hMMr : rowsLen o (matMul M (matPow M o k)) :=
      rowsLen_cast (transposeLen (matPow M o k) hPr hPl)
        (rowsLen_matMul M (matPow M o k))
    have hrMM : r < (matMul M (matPow M o k)).length := by
      rw [length_matMul M (matPow M o k), hMl]; exact hr'
    have hc' : c < o := by
      have h0 : c < (ground.getAt ([] : List BPair)
          (matMul M (matPow M o k)) r).length := hc
      rw [rowsLen_getAt (matMul M (matPow M o k)) r hMMr hrMM] at h0
      exact h0
    have hrowM : (ground.getAt ([] : List BPair) M r).length = o :=
      rowsLen_getAt M r hMr hrM
    show (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (matMul M (matPow M o k)) r) c).oneValue
      BPair.unit
    refine matMul_entry_unit (n := o) M (matPow M o k) hMr hPl hPr r c
      hrM hc' ?_
    match harm with
    | Or.inl ⟨hrp, hqc⟩ =>
      match Nat.lt_or_ge j ns.length with
      | Or.inr hge =>
        have hfull : ground.prefixAt (j + (k + 1)) ns = o :=
          hclamp (j + (k + 1)) (Nat.le_trans hge (Nat.le_add_right j (k + 1)))
        rw [hfull] at hqc
        exact (Nat.lt_irrefl c (Nat.lt_of_lt_of_le hc' hqc)).elim
      | Or.inl hj =>
        have heq : j + 1 + k = j + (k + 1) := Nat.succ_add j k
        have hshift : ground.prefixAt (j + 1 + k) ns ≤ c := by
          rw [heq]; exact hqc
        intro i hi
        have hiP : i < (matPow M o k).length := by rw [hPl]; exact hi
        have hrowP : (ground.getAt ([] : List BPair) (matPow M o k) i).length
            = o := rowsLen_getAt (matPow M o k) i hPr hiP
        match Nat.lt_or_ge i (ground.prefixAt (j + 1) ns) with
        | Or.inl hlt =>
          exact Or.inr (ih (j + 1) i hiP c (by rw [hrowP]; exact hc')
            (Or.inl ⟨hlt, hshift⟩))
        | Or.inr hge2 =>
          exact Or.inl (hband j hj r hrM i (by rw [hrowM]; exact hi)
            (Or.inl ⟨hrp, hge2⟩))
    | Or.inr ⟨hcp, hqr⟩ =>
      match Nat.lt_or_ge (j + k) ns.length with
      | Or.inr hge =>
        have hfull : ground.prefixAt (j + (k + 1)) ns = o :=
          hclamp (j + (k + 1)) (Nat.le_trans hge (Nat.le_succ (j + k)))
        rw [hfull] at hqr
        exact (Nat.lt_irrefl r (Nat.lt_of_lt_of_le hr' hqr)).elim
      | Or.inl hjk =>
        have hqr' : ground.prefixAt (j + k + 1) ns ≤ r := hqr
        intro i hi
        have hiP : i < (matPow M o k).length := by rw [hPl]; exact hi
        have hrowP : (ground.getAt ([] : List BPair) (matPow M o k) i).length
            = o := rowsLen_getAt (matPow M o k) i hPr hiP
        match Nat.lt_or_ge i (ground.prefixAt (j + k) ns) with
        | Or.inl hlt =>
          exact Or.inl (hband (j + k) hjk r hrM i (by rw [hrowM]; exact hi)
            (Or.inr ⟨hlt, hqr'⟩))
        | Or.inr hge2 =>
          exact Or.inr (ih j i hiP c (by rw [hrowP]; exact hc')
            (Or.inr ⟨hcp, hge2⟩))

/-- The banded powers' sandwich keeps the widened leading support. -/
theorem lead_sandwich {o : Nat} (Lw A : Mat) (hLw : sqAt Lw o)
    (hA : sqAt A o) (ns : List Nat)
    (hns : ground.prefixAt ns.length ns = o) (hband : bandedAt Lw ns)
    (j k : Nat) (hlead : leadAt A (ground.prefixAt j ns)) :
    leadAt (matMul (matPow Lw o k) (matMul A (matPow Lw o k)))
      (ground.prefixAt (j + k) ns) := by
  have hLwl : Lw.length = o := sqAt_len hLw
  have hAl : A.length = o := sqAt_len hA
  have hAr : rowsLen o A := rowsLen_of_sqAt hA
  have hLl : (matPow Lw o k).length = o := length_matPow Lw o hLwl k
  have hLr : rowsLen o (matPow Lw o k) := rowsLen_matPow Lw o hLwl k
  have hreach := pow_reach Lw hLw ns hns hband j k
  have hPl : (matMul A (matPow Lw o k)).length = o := by
    rw [length_matMul A (matPow Lw o k), hAl]
  have hPr : rowsLen o (matMul A (matPow Lw o k)) :=
    rowsLen_cast (transposeLen (matPow Lw o k) hLr hLl)
      (rowsLen_matMul A (matPow Lw o k))
  -- the middle factor's entry at a column past the widened boundary
  have hmidC : ∀ i, i < o → ∀ c, c < o →
      ground.prefixAt (j + k) ns ≤ c →
      (ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (matMul A (matPow Lw o k)) i) c).oneValue BPair.unit := by
    intro i hi c hc hqc
    refine matMul_entry_unit (n := o) A (matPow Lw o k) hAr hLl hLr i c
      (by rw [hAl]; exact hi) hc ?_
    intro m hm
    match Nat.lt_or_ge m (ground.prefixAt j ns) with
    | Or.inl hlt =>
      exact Or.inr (hreach m (by rw [hLl]; exact hm) c
        (by rw [rowsLen_getAt (matPow Lw o k) m hLr (by rw [hLl]; exact hm)]
            exact hc)
        (Or.inl ⟨hlt, hqc⟩))
    | Or.inr hge =>
      exact Or.inl (hlead i (by rw [hAl]; exact hi) m
        (by rw [rowsLen_getAt A i hAr (by rw [hAl]; exact hi)]; exact hm)
        (Or.inr hge))
  -- the middle factor's entry at a row past the leading boundary
  have hmidR : ∀ i, i < o → ground.prefixAt j ns ≤ i → ∀ c, c < o →
      (ground.getAt BPair.unit (ground.getAt ([] : List BPair)
        (matMul A (matPow Lw o k)) i) c).oneValue BPair.unit := by
    intro i hi hpi c hc
    refine matMul_entry_unit (n := o) A (matPow Lw o k) hAr hLl hLr i c
      (by rw [hAl]; exact hi) hc ?_
    intro m hm
    exact Or.inl (hlead i (by rw [hAl]; exact hi) m
      (by rw [rowsLen_getAt A i hAr (by rw [hAl]; exact hi)]; exact hm)
      (Or.inl hpi))
  intro r hr c hc harm
  have hr' : r < o := by
    have h0 : r < (matMul (matPow Lw o k) (matMul A (matPow Lw o k))).length :=
      hr
    rw [length_matMul (matPow Lw o k) (matMul A (matPow Lw o k)), hLl] at h0
    exact h0
  have hrL : r < (matPow Lw o k).length := by rw [hLl]; exact hr'
  have hMMr : rowsLen o (matMul (matPow Lw o k) (matMul A (matPow Lw o k))) :=
    rowsLen_cast (transposeLen (matMul A (matPow Lw o k)) hPr hPl)
      (rowsLen_matMul (matPow Lw o k) (matMul A (matPow Lw o k)))
  have hrMM : r < (matMul (matPow Lw o k) (matMul A (matPow Lw o k))).length := by
    rw [length_matMul (matPow Lw o k) (matMul A (matPow Lw o k)), hLl]
    exact hr'
  have hc' : c < o := by
    have h0 : c < (ground.getAt ([] : List BPair)
        (matMul (matPow Lw o k) (matMul A (matPow Lw o k))) r).length := hc
    rw [rowsLen_getAt (matMul (matPow Lw o k) (matMul A (matPow Lw o k))) r
      hMMr hrMM] at h0
    exact h0
  have hrowL : (ground.getAt ([] : List BPair) (matPow Lw o k) r).length = o :=
    rowsLen_getAt (matPow Lw o k) r hLr hrL
  refine matMul_entry_unit (n := o) (matPow Lw o k)
    (matMul A (matPow Lw o k)) hLr hPl hPr r c hrL hc' ?_
  intro i hi
  match harm with
  | Or.inr hqc => exact Or.inr (hmidC i hi c hc' hqc)
  | Or.inl hqr =>
    match Nat.lt_or_ge i (ground.prefixAt j ns) with
    | Or.inl hlt =>
      exact Or.inl (hreach r hrL i (by rw [hrowL]; exact hi)
        (Or.inr ⟨hlt, hqr⟩))
    | Or.inr hge =>
      exact Or.inr (hmidR i hi hge c hc')

/-- Disjoint supports annihilate both ways. -/
theorem lead_tail_null {o : Nat} (X Y : Mat) (hX : sqAt X o) (hY : sqAt Y o)
    (q : Nat) (hlead : leadAt X q) (htail : tailAt Y q) :
    elim.matNull (matMul X Y) ∧ elim.matNull (matMul Y X) := by
  have hXl : X.length = o := sqAt_len hX
  have hXr : rowsLen o X := rowsLen_of_sqAt hX
  have hYl : Y.length = o := sqAt_len hY
  have hYr : rowsLen o Y := rowsLen_of_sqAt hY
  have hXYr : rowsLen o (matMul X Y) :=
    rowsLen_cast (transposeLen Y hYr hYl) (rowsLen_matMul X Y)
  have hYXr : rowsLen o (matMul Y X) :=
    rowsLen_cast (transposeLen X hXr hXl) (rowsLen_matMul Y X)
  refine ⟨matNull_of_entries (n := o) (matMul X Y) hXYr (fun r hr c hc => ?_),
    matNull_of_entries (n := o) (matMul Y X) hYXr (fun r hr c hc => ?_)⟩
  · have hrX : r < X.length := by
      rw [length_matMul X Y] at hr; exact hr
    have hrowX : (ground.getAt ([] : List BPair) X r).length = o :=
      rowsLen_getAt X r hXr hrX
    refine matMul_entry_unit (n := o) X Y hXr hYl hYr r c hrX hc ?_
    intro i hi
    match Nat.lt_or_ge i q with
    | Or.inl hlt =>
      exact Or.inr (htail i (by rw [hYl]; exact hi) c
        (by rw [rowsLen_getAt Y i hYr (by rw [hYl]; exact hi)]; exact hc)
        (Or.inl hlt))
    | Or.inr hge =>
      exact Or.inl (hlead r hrX i (by rw [hrowX]; exact hi) (Or.inr hge))
  · have hrY : r < Y.length := by
      rw [length_matMul Y X] at hr; exact hr
    have hrowY : (ground.getAt ([] : List BPair) Y r).length = o :=
      rowsLen_getAt Y r hYr hrY
    refine matMul_entry_unit (n := o) Y X hYr hXl hXr r c hrY hc ?_
    intro i hi
    match Nat.lt_or_ge i q with
    | Or.inl hlt =>
      exact Or.inl (htail r hrY i (by rw [hrowY]; exact hi) (Or.inr hlt))
    | Or.inr hge =>
      exact Or.inr (hlead i (by rw [hXl]; exact hi) c
        (by rw [rowsLen_getAt X i hXr (by rw [hXl]; exact hi)]; exact hc)
        (Or.inl hge))

/-- The cap's read at the plain pairing, the skipping fold bridged. -/
private theorem capP {o : Nat} (A : Mat) (an ad : Pos)
    (spU spL : inertia.Split o)
    (hc : inertia.capAt (inertia.matScale ad A)
      (inertia.matScale an (idMat o)) spU spL)
    (v : List BPair) (hv : v.length = o) :
    (elim.dotP (elim.matVec A v) (elim.matVec A v)).scale (ad * ad)
      ≤ (elim.dotP v v).scale (an * an) :=
  ground.leB_congr
    (BPair.scale_congr (ad * ad) (elim.dotN_read _ _))
    (BPair.scale_congr (an * an) (elim.dotN_read v v))
    (truncation.cap_sq A an ad spU spL hc v hv)

/-- The cap's power read at the plain pairing. -/
theorem cap_pow {o : Nat} (V : Mat) (cn cd : Pos)
    (spU spL : inertia.Split o)
    (hc : inertia.capAt (inertia.matScale cd V)
      (inertia.matScale cn (idMat o)) spU spL)
    (z : List BPair) (hz : z.length = o) (k : Nat) :
    (elim.dotP (elim.matVec (matPow V o k) z)
        (elim.matVec (matPow V o k) z)).scale (Pos.pow (cd * cd) k)
      ≤ (elim.dotP z z).scale (Pos.pow (cn * cn) k) := by
  have hVl : V.length = o :=
    (length_matScale cd V).symm.trans (sqAt_len hc.1)
  have hself : ∀ u u' : List BPair, poly.oneValue u u' →
      (elim.dotP u u).oneValue (elim.dotP u' u') := by
    intro u u' h
    exact BPair.oneValue_trans (elim.dotP_oneValue_left u u' u h)
      (elim.dotP_oneValue_right u' u u' h)
  induction k with
  | zero =>
    have h0 : poly.oneValue (elim.matVec (matPow V o 0) z) z :=
      matVec_idMat o z hz
    show (elim.dotP (elim.matVec (matPow V o 0) z)
        (elim.matVec (matPow V o 0) z)).scale Pos.one
      ≤ (elim.dotP z z).scale Pos.one
    rw [BPair.scale_one, BPair.scale_one]
    exact ground.leB_congr_left
      (BPair.oneValue_symm (hself _ _ h0)) (ground.leB_refl _)
  | succ k ih =>
    have hPl : (matPow V o k).length = o := length_matPow V o hVl k
    have hPr : rowsLen o (matPow V o k) := rowsLen_matPow V o hVl k
    have hwl : (elim.matVec (matPow V o k) z).length = o :=
      (elim.matVec_length (matPow V o k) z).trans hPl
    have hW : poly.oneValue (elim.matVec (matPow V o (k + 1)) z)
        (elim.matVec V (elim.matVec (matPow V o k) z)) :=
      elim.matVec_matMul V (matPow V o k) o hPr z hz
    have hbase : (elim.dotP (elim.matVec (matPow V o (k + 1)) z)
        (elim.matVec (matPow V o (k + 1)) z)).scale (cd * cd)
      ≤ (elim.dotP (elim.matVec (matPow V o k) z)
        (elim.matVec (matPow V o k) z)).scale (cn * cn) :=
      ground.leB_congr_left
        (BPair.scale_congr (cd * cd)
          (BPair.oneValue_symm (hself _ _ hW)))
        (capP V cn cd spU spL hc (elim.matVec (matPow V o k) z) hwl)
    have h1 := ground.leB_scale hbase (Pos.pow (cd * cd) k)
    rw [BPair.scale_scale, BPair.scale_scale] at h1
    have h2 := ground.leB_scale ih (cn * cn)
    rw [BPair.scale_scale, BPair.scale_scale] at h2
    rw [ground.mul_comm (Pos.pow (cd * cd) k) (cn * cn)] at h2
    rw [ground.mul_comm (Pos.pow (cn * cn) k) (cn * cn)] at h2
    show (elim.dotP (elim.matVec (matPow V o (k + 1)) z)
        (elim.matVec (matPow V o (k + 1)) z)).scale
        ((cd * cd) * Pos.pow (cd * cd) k)
      ≤ (elim.dotP z z).scale ((cn * cn) * Pos.pow (cn * cn) k)
    exact ground.leB_trans h1 h2


/-- The two-step telescope's magnitude read: at a vacant far term
the squared-clearing read sits below the two cross-cleared gaps at
their own weights. -/
private theorem magTele (X1 X2 X3 : BPair) (l v : Pos)
    (h3 : X3.oneValue BPair.unit) :
    windowsep.mag (X1.scale (l * l))
      ≤ (windowsep.mag (X1.scale l + (X2.scale v).swap)).scale l
        + (windowsep.mag (X2.scale l + (X3.scale v).swap)).scale v := by
  have hX3v : ((X3.scale v).swap).oneValue BPair.unit := by
    have h1 : (X3.scale v).oneValue BPair.unit :=
      BPair.oneValue_trans (BPair.scale_congr v h3)
        (BPair.oneValue_symm (ground.unitScale v))
    exact ground.swap_congr h1
  have hswap3 : (((X3.scale v).swap).scale v).oneValue BPair.unit :=
    BPair.oneValue_trans (BPair.scale_congr v hX3v)
      (BPair.oneValue_symm (ground.unitScale v))
  have hD : ((X1.scale l + (X2.scale v).swap).scale l
      + (X2.scale l + (X3.scale v).swap).scale v).oneValue
      (X1.scale (l * l)) := by
    rw [BPair.scale_add (X1.scale l) ((X2.scale v).swap) l,
      BPair.scale_add (X2.scale l) ((X3.scale v).swap) v,
      BPair.scale_swap (X2.scale v) l,
      BPair.scale_scale X1 l l, BPair.scale_scale X2 v l,
      BPair.scale_scale X2 l v]
    have hmid : (X1.scale (l * l) + (X2.scale (v * l)).swap
        + (X2.scale (l * v)) + ((X3.scale v).swap.scale v)).oneValue
        (X1.scale (l * l)) := by
      have habs : (X1.scale (l * l) + (X2.scale (v * l)).swap
          + (X2.scale (l * v))).oneValue (X1.scale (l * l)) := by
        rw [show l * v = v * l from ground.mul_comm l v]
        exact BPair.add_swap_self (X1.scale (l * l)) (X2.scale (v * l))
      refine BPair.oneValue_trans
        (BPair.add_congr habs hswap3) ?_
      exact BPair.add_unit (X1.scale (l * l))
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq ?_) hmid
    rw [BPair.add_assoc (X1.scale (l * l)) ((X2.scale (v * l)).swap)
        (X2.scale (l * v) + (X3.scale v).swap.scale v),
      ← BPair.add_assoc ((X2.scale (v * l)).swap) (X2.scale (l * v))
        ((X3.scale v).swap.scale v),
      ← BPair.add_assoc (X1.scale (l * l))
        ((X2.scale (v * l)).swap + X2.scale (l * v))
        ((X3.scale v).swap.scale v),
      ← BPair.add_assoc (X1.scale (l * l)) ((X2.scale (v * l)).swap)
        (X2.scale (l * v))]
  have hle : windowsep.mag
      ((X1.scale l + (X2.scale v).swap).scale l
        + (X2.scale l + (X3.scale v).swap).scale v)
      ≤ (windowsep.mag (X1.scale l + (X2.scale v).swap)).scale l
        + (windowsep.mag (X2.scale l + (X3.scale v).swap)).scale v := by
    refine ground.leB_trans (windowsep.mag_add_le _ _) ?_
    rw [windowsep.mag_scale _ l, windowsep.mag_scale _ v]
    exact ground.leB_refl _
  exact ground.leB_congr_left (windowsep.mag_congr hD) hle


/-- The pair price at stated weights: `euc_pair_price`'s display
with the weight pair read onto the two grams. -/
private theorem dPrice {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud kn kd lc vc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd (posOfSucc n) l ws)
    (Lw Vw : Mat) (hLs : sqAt Lw o) (hVs : sqAt Vw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (aw bw : Pos) (p q : List BPair)
    (hp : p.length = o) (hq : q.length = o) :
    ((windowsep.mag
      ((elim.dotP p (elim.matVec (matPow Vw o (n + 1)) q)).scale
          (Pos.pow lc (n + 1))
        + ((elim.dotP p (elim.matVec (matPow Lw o (n + 1)) q)).scale
            (Pos.pow vc (n + 1))).swap)).scale (aw * bw)).scale
      (2 * (posOfSucc n * ((ud * ud) * (kd * kd))))
    ≤ ((elim.dotP p p).scale (aw * aw)
        + (elim.dotP q q).scale (bw * bw)).scale
        ((un * un * (kn * kn)) * Pos.pow (lc * vc) (n + 1)) := by
  have hE := euc_pair_price Et T Tw l hd un ud kn kd lc vc n ws hw
    Lw Vw hLs hVs hL hV p q hp hq (BPair.ofPos aw) (BPair.ofPos bw)
  have hmul : ∀ (u v : Pos) (z : BPair),
      ((BPair.ofPos u * BPair.ofPos v) * z).oneValue
        (z.scale (u * v)) :=
    fun u v z => BPair.oneValue_trans
      (BPair.mul_congr (BPair.ofPos_mul u v) (BPair.oneValue_refl z))
      (BPair.ofPos_scale (u * v) z)
  refine ground.leB_congr
    (BPair.scale_congr _
      (BPair.oneValue_trans
        (windowsep.mag_congr (hmul aw bw _))
        (BPair.oneValue_of_eq (windowsep.mag_scale _ (aw * bw)))))
    (BPair.scale_congr _
      (BPair.add_congr (hmul aw aw (elim.dotP p p))
        (hmul bw bw (elim.dotP q q))))
    hE

/-- Two priced hops compose at the multiplied clearings. -/
private theorem chain2 (q u y : BPair) (a1n a1d a2n a2d : Pos)
    (h1 : q.scale a1d ≤ u.scale a1n)
    (h2 : u.scale a2d ≤ y.scale a2n) :
    q.scale (a1d * a2d) ≤ y.scale (a1n * a2n) := by
  have k1 := ground.leB_scale h1 a2d
  have k2 := ground.leB_scale h2 a1n
  rw [BPair.scale_scale q a1d a2d, BPair.scale_scale u a1n a2d] at k1
  rw [BPair.scale_scale u a2d a1n, BPair.scale_scale y a2n a1n,
    ground.mul_comm a2d a1n, ground.mul_comm a2n a1n] at k2
  exact ground.leB_trans k1 k2

/-- Three priced hops compose, the middle hop's clearings carried
past the outer two. -/
private theorem chain3 (q u v y : BPair)
    (a1n a1d a2n a2d a3n a3d : Pos)
    (h1 : q.scale a1d ≤ u.scale a1n)
    (h2 : u.scale a2d ≤ v.scale a2n)
    (h3 : v.scale a3d ≤ y.scale a3n) :
    q.scale (a1d * (a3d * a2d)) ≤ y.scale (a1n * (a3n * a2n)) := by
  have h := chain2 q v y (a1n * a2n) (a1d * a2d) a3n a3d
    (chain2 q u v a1n a1d a2n a2d h1 h2) h3
  rw [ground.mul_assoc a1d a2d a3d, ground.mul_comm a2d a3d,
    ground.mul_assoc a1n a2n a3n, ground.mul_comm a2n a3n] at h
  exact h

/-- The join's entry read: the two scaled entries against the
identity's. -/
private theorem joinEntry {o : Nat} (Et Lw : Mat) (hEts : sqAt Et o)
    (hLs : sqAt Lw o) (a b c : Pos)
    (hJ : elim.matOneValue
      (matAdd (inertia.matScale a Lw) (inertia.matScale b Et))
      (inertia.matScale c (idMat o)))
    (r c' : Nat) (hr' : r < o) (hcc : c' < o) :
    ((ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) Lw r) c').scale a
      + (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) Et r) c').scale b).oneValue
      ((ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (idMat o) r) c').scale c) := by
  have hEl : Et.length = o := sqAt_len hEts
  have hEr : rowsLen o Et := rowsLen_of_sqAt hEts
  have hLl : Lw.length = o := sqAt_len hLs
  have hLr : rowsLen o Lw := rowsLen_of_sqAt hLs
  have hlenA : (inertia.matScale a Lw).length
      = (inertia.matScale b Et).length := by
    rw [inertia.length_matScale, inertia.length_matScale, hLl, hEl]
  have hrA : r < (matAdd (inertia.matScale a Lw)
      (inertia.matScale b Et)).length := by
    rw [elim.length_matAdd _ _ hlenA, inertia.length_matScale, hLl]
    exact hr'
  have hrsA : elim.rowsLen o (inertia.matScale a Lw) :=
    elim.rowsLen_mapRows _ Lw o hLr
  have hrsB : elim.rowsLen o (inertia.matScale b Et) :=
    elim.rowsLen_mapRows _ Et o hEr
  have hrow := poly.oneValue_getAt c'
    (ground.matched_entry ([] : List BPair) hJ r hrA)
  rw [elim.getAt_matAdd (inertia.matScale a Lw)
      (inertia.matScale b Et) r
      (by rw [inertia.length_matScale, hLl]; exact hr')
      (by rw [inertia.length_matScale, hEl]; exact hr')] at hrow
  rw [elim.getAt_vecAdd _ _ c'
      (by rw [rowsLen_getAt (inertia.matScale a Lw) r hrsA
            (by rw [inertia.length_matScale, hLl]; exact hr')]
          exact hcc)
      (by rw [rowsLen_getAt (inertia.matScale b Et) r hrsB
            (by rw [inertia.length_matScale, hEl]; exact hr')]
          exact hcc)] at hrow
  rw [inertia.matScale_entry a Lw r c' (by rw [hLl]; exact hr')
      (by rw [rowsLen_getAt Lw r hLr (by rw [hLl]; exact hr')]
          exact hcc),
    inertia.matScale_entry b Et r c' (by rw [hEl]; exact hr')
      (by rw [rowsLen_getAt Et r hEr (by rw [hEl]; exact hr')]
          exact hcc),
    inertia.matScale_entry c (idMat o) r c'
      (by rw [idMat_len]; exact hr')
      (by rw [rowsLen_getAt (idMat o) r (idMat_rows o)
            (by rw [idMat_len]; exact hr')]
          exact hcc)] at hrow
  exact hrow

/-- The banded read passes through the witness join: at the join's
identity the gap's vacant off-band entries force the witness's. -/
theorem banded_of_join {o : Nat} (Et Lw : Mat) (hEts : sqAt Et o)
    (hLs : sqAt Lw o) (a b c : Pos)
    (hJ : elim.matOneValue
      (matAdd (inertia.matScale a Lw) (inertia.matScale b Et))
      (inertia.matScale c (idMat o)))
    (ns : List Nat) (hband : bandedAt Et ns) :
    bandedAt Lw ns := by
  have hEl : Et.length = o := sqAt_len hEts
  have hEr : rowsLen o Et := rowsLen_of_sqAt hEts
  have hLl : Lw.length = o := sqAt_len hLs
  have hLr : rowsLen o Lw := rowsLen_of_sqAt hLs
  intro j hj r hr c' hc harm
  have hr' : r < o := by rw [hLl] at hr; exact hr
  have hcc : c' < o := by
    rw [rowsLen_getAt Lw r hLr (by rw [hLl]; exact hr')] at hc
    exact hc
  have hmono : ground.prefixAt j ns ≤ ground.prefixAt (j + 1) ns := by
    rw [ground.prefixAt_succ ns j hj]
    exact Nat.le_add_right _ _
  have hne : ¬ c' = r := by
    intro he
    match harm with
    | Or.inl ⟨h1, h2⟩ =>
      rw [← he] at h1
      exact Nat.lt_irrefl c'
        (Nat.lt_of_lt_of_le h1 (Nat.le_trans hmono (he ▸ h2)))
    | Or.inr ⟨h1, h2⟩ =>
      rw [he] at h1
      exact Nat.lt_irrefl r
        (Nat.lt_of_lt_of_le h1 (Nat.le_trans hmono h2))
  have hrow := joinEntry Et Lw hEts hLs a b c hJ r c' hr' hcc
  rw [getAt_idMat o r c' hr' hcc, if_neg hne] at hrow
  have hEt0 : (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) Et r) c').oneValue BPair.unit :=
    hband j hj r (by rw [hEl]; exact hr') c'
      (by rw [rowsLen_getAt Et r hEr (by rw [hEl]; exact hr')]
          exact hcc) harm
  have hLsc : ((ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) Lw r) c').scale a).oneValue
      BPair.unit := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.add_unit _)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm
          (BPair.oneValue_trans (BPair.scale_congr b hEt0)
            (BPair.oneValue_symm (ground.unitScale b))))) ?_
    refine BPair.oneValue_trans hrow ?_
    exact BPair.oneValue_symm
      (BPair.oneValue_trans (ground.unitScale c)
        (BPair.scale_congr c (BPair.oneValue_refl BPair.unit)))
  refine BPair.scale_cancel (w := a) ?_
  refine BPair.oneValue_trans hLsc ?_
  exact ground.unitScale a

/-- The witness inherits the gap's symmetry through the join. -/
theorem sym_of_join {o : Nat} (Et Lw : Mat) (hEts : sqAt Et o)
    (hLs : sqAt Lw o)
    (hsymE : elim.matOneValue (elim.transposeM Et) Et)
    (a b c : Pos)
    (hJ : elim.matOneValue
      (matAdd (inertia.matScale a Lw) (inertia.matScale b Et))
      (inertia.matScale c (idMat o))) :
    elim.matOneValue (elim.transposeM Lw) Lw := by
  have hEl : Et.length = o := sqAt_len hEts
  have hEr : rowsLen o Et := rowsLen_of_sqAt hEts
  have hLl : Lw.length = o := sqAt_len hLs
  have hLr : rowsLen o Lw := rowsLen_of_sqAt hLs
  cases o with
  | zero =>
    exact matOne_of_len_zero _ _
      (elim.transposeLen Lw hLr hLl) hLl
  | succ o0 =>
  have ho : 0 < o0 + 1 := Nat.succ_pos o0
  have htl : (elim.transposeM Lw).length = o0 + 1 :=
    elim.length_transposeM Lw hLr (by rw [hLl]; exact ho)
  refine elim.matOne_getAt _ _ (htl.trans hLl.symm) ?_
  intro r hrT
  have hr' : r < o0 + 1 := by rw [htl] at hrT; exact hrT
  refine poly.oneValue_of_entries _ _
    (by rw [rowsLen_getAt (elim.transposeM Lw) r
          (elim.rowsLen_cast hLl (elim.rowsLen_transposeM Lw)) hrT,
        rowsLen_getAt Lw r hLr (by rw [hLl]; exact hr')]) ?_
  intro c' hcT
  have hcc : c' < o0 + 1 := by
    rw [rowsLen_getAt (elim.transposeM Lw) r
      (elim.rowsLen_cast hLl (elim.rowsLen_transposeM Lw)) hrT] at hcT
    exact hcT
  rw [elim.getAt_transposeM BPair.unit Lw hLr r c' hr'
    (by rw [hLl]; exact hcc)]
  -- Et's entries exchange across its own transpose read
  have hEsym : (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) Et c') r).oneValue
      (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) Et r) c') := by
    have h0 := poly.oneValue_getAt c'
      (ground.matched_entry ([] : List BPair) hsymE r
        (by rw [elim.length_transposeM Et hEr
              (by rw [hEl]; exact ho)]
            exact hr'))
    rw [elim.getAt_transposeM BPair.unit Et hEr r c' hr'
      (by rw [hEl]; exact hcc)] at h0
    exact h0
  -- the two join entries at the exchanged keys
  have h1 := joinEntry Et Lw hEts hLs a b c hJ r c' hr' hcc
  have h2 := joinEntry Et Lw hEts hLs a b c hJ c' r hcc hr'
  -- the identity's two entries are one value
  have hid : (ground.getAt BPair.unit
      (ground.getAt ([] : List BPair) (idMat (o0 + 1)) c') r).scale c
      = (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) (idMat (o0 + 1)) r) c').scale
        c := by
    rw [getAt_idMat (o0 + 1) c' r hcc hr',
      getAt_idMat (o0 + 1) r c' hr' hcc]
    cases Nat.decEq r c' with
    | isTrue h => rw [if_pos h, if_pos h.symm]
    | isFalse h => rw [if_neg h, if_neg (fun he => h he.symm)]
  rw [hid] at h2
  have h3 := BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.scale_congr b (BPair.oneValue_symm hEsym)))
    (BPair.oneValue_trans h2 (BPair.oneValue_symm h1))
  exact BPair.scale_cancel (w := a) (BPair.add_cancel h3)

/-- A two-factor weight's square regroups to the squared factors at
the squared power. -/
private theorem posSq (a b c : Pos) (k : Nat) :
    ((a * b) * Pos.pow c k) * ((a * b) * Pos.pow c k)
      = (a * a) * ((b * b) * Pos.pow (c * c) k) := by
  rw [ground.mul_mul_mul_comm (a * b) (Pos.pow c k) (a * b)
      (Pos.pow c k),
    ground.mul_mul_mul_comm a b a b, ← ground.Pos.pow_mul c c k,
    ground.mul_assoc (a * a) (b * b) (Pos.pow (c * c) k)]

/-- The two weights' second slots exchange across the product. -/
private theorem posXch (p q u r v w : Pos) :
    ((p * q) * u) * ((r * v) * w)
      = ((p * v) * u) * ((r * q) * w) := by
  rw [ground.mul_assoc (p * q) u ((r * v) * w),
    ground.mul_assoc (p * v) u ((r * q) * w),
    ground.mul_left_comm u (r * v) w, ground.mul_left_comm u (r * q) w,
    ← ground.mul_assoc (p * q) (r * v) (u * w),
    ← ground.mul_assoc (p * v) (r * q) (u * w),
    ground.mul_mul_mul_comm p q r v, ground.mul_mul_mul_comm p v r q,
    ground.mul_comm q v]

/-- The four priced branches assemble: the two orderings' telescopes
at the branch weights close on the one display. -/
private theorem magAssemble (G M1 M4 D1 D2 D3 D4 R : BPair)
    (lam nu N2 PU PL CU CL W0 : Pos)
    (hGap : G ≤ M1 + M4)
    (hT1 : M1.scale (lam * lam) ≤ D1.scale lam + D2.scale nu)
    (hT2 : M4.scale (lam * lam) ≤ D3.scale lam + D4.scale nu)
    (hQ1 : (D1.scale PU).scale N2 ≤ R.scale (CU * W0))
    (hQ2 : (D2.scale PL).scale N2 ≤ R.scale (CL * W0))
    (hQ3 : (D3.scale PU).scale N2 ≤ R.scale (CU * W0))
    (hQ4 : (D4.scale PL).scale N2 ≤ R.scale (CL * W0)) :
    G.scale ((lam * lam) * (N2 * (PU * PL)))
      ≤ R.scale (W0 * (2 * (lam * (CU * PL) + nu * (CL * PU)))) := by
  have q1 : D1.scale (lam * (N2 * (PU * PL)))
      ≤ R.scale ((CU * W0) * (lam * PL)) := by
    have k := ground.leB_scale hQ1 (lam * PL)
    rw [BPair.scale_scale (D1.scale PU) N2 (lam * PL),
      BPair.scale_scale D1 PU (N2 * (lam * PL)),
      BPair.scale_scale R (CU * W0) (lam * PL),
      ground.mul_left_comm PU N2 (lam * PL),
      ground.mul_left_comm PU lam PL,
      ground.mul_left_comm N2 lam (PU * PL)] at k
    exact k
  have q3 : D3.scale (lam * (N2 * (PU * PL)))
      ≤ R.scale ((CU * W0) * (lam * PL)) := by
    have k := ground.leB_scale hQ3 (lam * PL)
    rw [BPair.scale_scale (D3.scale PU) N2 (lam * PL),
      BPair.scale_scale D3 PU (N2 * (lam * PL)),
      BPair.scale_scale R (CU * W0) (lam * PL),
      ground.mul_left_comm PU N2 (lam * PL),
      ground.mul_left_comm PU lam PL,
      ground.mul_left_comm N2 lam (PU * PL)] at k
    exact k
  have q2 : D2.scale (nu * (N2 * (PU * PL)))
      ≤ R.scale ((CL * W0) * (nu * PU)) := by
    have k := ground.leB_scale hQ2 (nu * PU)
    rw [BPair.scale_scale (D2.scale PL) N2 (nu * PU),
      BPair.scale_scale D2 PL (N2 * (nu * PU)),
      BPair.scale_scale R (CL * W0) (nu * PU),
      ground.mul_left_comm PL N2 (nu * PU),
      ground.mul_left_comm PL nu PU, ground.mul_comm PL PU,
      ground.mul_left_comm N2 nu (PU * PL)] at k
    exact k
  have q4 : D4.scale (nu * (N2 * (PU * PL)))
      ≤ R.scale ((CL * W0) * (nu * PU)) := by
    have k := ground.leB_scale hQ4 (nu * PU)
    rw [BPair.scale_scale (D4.scale PL) N2 (nu * PU),
      BPair.scale_scale D4 PL (N2 * (nu * PU)),
      BPair.scale_scale R (CL * W0) (nu * PU),
      ground.mul_left_comm PL N2 (nu * PU),
      ground.mul_left_comm PL nu PU, ground.mul_comm PL PU,
      ground.mul_left_comm N2 nu (PU * PL)] at k
    exact k
  have s1 : G.scale (lam * lam)
      ≤ M1.scale (lam * lam) + M4.scale (lam * lam) := by
    have h := ground.leB_scale hGap (lam * lam)
    rw [BPair.scale_add M1 M4 (lam * lam)] at h
    exact h
  have s3 := ground.leB_scale
    (ground.leB_trans s1 (ground.leB_add hT1 hT2)) (N2 * (PU * PL))
  rw [BPair.scale_scale G (lam * lam) (N2 * (PU * PL)),
    BPair.scale_add (D1.scale lam + D2.scale nu)
      (D3.scale lam + D4.scale nu) (N2 * (PU * PL)),
    BPair.scale_add (D1.scale lam) (D2.scale nu) (N2 * (PU * PL)),
    BPair.scale_add (D3.scale lam) (D4.scale nu) (N2 * (PU * PL)),
    BPair.scale_scale D1 lam (N2 * (PU * PL)),
    BPair.scale_scale D2 nu (N2 * (PU * PL)),
    BPair.scale_scale D3 lam (N2 * (PU * PL)),
    BPair.scale_scale D4 nu (N2 * (PU * PL))] at s3
  refine ground.leB_trans s3 ?_
  refine ground.leB_trans
    (ground.leB_add (ground.leB_add q1 q2) (ground.leB_add q3 q4)) ?_
  refine ground.leB_congr_right (BPair.oneValue_of_eq ?_)
    (ground.leB_refl _)
  have e1 : W0 * (lam * (CU * PL)) = (CU * W0) * (lam * PL) := by
    rw [ground.mul_left_comm W0 lam (CU * PL),
      ground.mul_left_comm W0 CU PL,
      ground.mul_left_comm lam CU (W0 * PL),
      ground.mul_assoc CU W0 (lam * PL),
      ground.mul_left_comm W0 lam PL]
  have e2 : W0 * (nu * (CL * PU)) = (CL * W0) * (nu * PU) := by
    rw [ground.mul_left_comm W0 nu (CL * PU),
      ground.mul_left_comm W0 CL PU,
      ground.mul_left_comm nu CL (W0 * PU),
      ground.mul_assoc CL W0 (nu * PU),
      ground.mul_left_comm W0 nu PU]
  rw [show W0 * (2 * (lam * (CU * PL) + nu * (CL * PU)))
      = (CU * W0) * (lam * PL) + (CL * W0) * (nu * PU)
        + ((CU * W0) * (lam * PL) + (CL * W0) * (nu * PU)) from by
    rw [ground.two_mul (lam * (CU * PL) + nu * (CL * PU)),
      ground.left_distrib W0 (lam * (CU * PL) + nu * (CL * PU))
        (lam * (CU * PL) + nu * (CL * PU)),
      ground.left_distrib W0 (lam * (CU * PL)) (nu * (CL * PU)),
      e1, e2]]
  rw [BPair.scale_addW R
      ((CU * W0) * (lam * PL) + (CL * W0) * (nu * PU))
      ((CU * W0) * (lam * PL) + (CL * W0) * (nu * PU)),
    BPair.scale_addW R ((CU * W0) * (lam * PL))
      ((CL * W0) * (nu * PU))]

/-- A priced branch joins the two grams at the uniform weight, the
chained caps' shared read. -/
private theorem qJoin (Dv S1 S2 xx yy : BPair) (P N2 C W0 : Pos)
    (hP : (Dv.scale P).scale N2 ≤ (S1 + S2).scale W0)
    (h1 : S1 ≤ xx.scale C) (h2 : S2 ≤ yy.scale C) :
    (Dv.scale P).scale N2 ≤ (xx + yy).scale (C * W0) := by
  refine ground.leB_trans hP ?_
  have k := ground.leB_scale
    (ground.leB_congr_right
      (BPair.oneValue_of_eq (BPair.scale_add xx yy C).symm)
      (ground.leB_add h1 h2)) W0
  rw [BPair.scale_scale (xx + yy) C W0] at k
  exact k

/-- The propagation bracket: the evolved probe's ordering gap
against a beyond-reach observable sits at or below the width
against the caps and the two grams. -/
theorem prop_bracket {o : Nat} (Et : Mat) (T Tw : SqMat o)
    (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat o) T Tw l)
    (un ud kn kd lc vc : Pos) (n : Nat) (ws : List (Pos × Pos))
    (hw : eucRead un ud kn kd (posOfSucc n) l ws)
    (Lw Vw : Mat) (hLs : sqAt Lw o) (hVs : sqAt Vw o)
    (hL : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Lw)
        (inertia.matScale (un * lc) Et))
      (inertia.matScale ((posOfSucc n * ud) * lc) (idMat o)))
    (hV : elim.matOneValue
      (matAdd (inertia.matScale (posOfSucc n * ud) Vw)
        (inertia.matScale un (matMul Et Vw)))
      (inertia.matScale ((posOfSucc n * ud) * vc) (idMat o)))
    (ns : List Nat) (hns : ground.prefixAt ns.length ns = o)
    (hband : bandedAt Et ns)
    (A : Mat) (hAs : sqAt A o)
    (hsymA : elim.matOneValue (elim.transposeM A) A)
    (j : Nat) (hlead : leadAt A (ground.prefixAt j ns))
    (an ad : Pos) (spA spA' : inertia.Split o)
    (hcapA : inertia.capAt (inertia.matScale ad A)
      (inertia.matScale an (idMat o)) spA spA')
    (A' : Mat) (hA's : sqAt A' o)
    (hsymA' : elim.matOneValue (elim.transposeM A') A')
    (htail : tailAt A' (ground.prefixAt (j + (n + 1)) ns))
    (bn bd : Pos) (spB spB' : inertia.Split o)
    (hcapB : inertia.capAt (inertia.matScale bd A')
      (inertia.matScale bn (idMat o)) spB spB')
    (cn cd : Pos) (spU spU' : inertia.Split o)
    (hcapU : inertia.capAt (inertia.matScale cd Vw)
      (inertia.matScale cn (idMat o)) spU spU')
    (en ed : Pos) (spL spL' : inertia.Split o)
    (hcapL : inertia.capAt (inertia.matScale ed Lw)
      (inertia.matScale en (idMat o)) spL spL')
    (x y : List BPair) (hx : x.length = o) (hy : y.length = o) :
    (windowsep.mag
      (elim.dotP x (elim.matVec (matPow Vw o (n + 1))
          (elim.matVec A (elim.matVec (matPow Vw o (n + 1))
            (elim.matVec A' y))))
        + (elim.dotP x (elim.matVec A'
            (elim.matVec (matPow Vw o (n + 1))
              (elim.matVec A (elim.matVec (matPow Vw o (n + 1))
                y))))).swap)).scale
      ((Pos.pow lc (n + 1) * Pos.pow lc (n + 1))
        * ((2 * (posOfSucc n * ((ud * ud) * (kd * kd))))
          * ((((an * bn) * Pos.pow cn (n + 1))
              * ((ad * bd) * Pos.pow cd (n + 1)))
            * (((ad * bd) * Pos.pow ed (n + 1))
              * ((an * bn) * Pos.pow en (n + 1))))))
      ≤ (elim.dotP x x + elim.dotP y y).scale
        (((un * un * (kn * kn)) * Pos.pow (lc * vc) (n + 1))
          * (2 * (Pos.pow lc (n + 1)
              * ((((an * bn) * Pos.pow cn (n + 1))
                  * ((an * bn) * Pos.pow cn (n + 1)))
                * (((ad * bd) * Pos.pow ed (n + 1))
                  * ((an * bn) * Pos.pow en (n + 1))))
            + Pos.pow vc (n + 1)
              * ((((an * bn) * Pos.pow en (n + 1))
                  * ((an * bn) * Pos.pow en (n + 1)))
                * (((an * bn) * Pos.pow cn (n + 1))
                  * ((ad * bd) * Pos.pow cd (n + 1))))))) := by
  -- Step 0: the derived reads, and the frames
  have hEts : sqAt Et o := hd.1
  have hsymE : elim.matOneValue (elim.transposeM Et) Et :=
    split.sym_of_diagRead Et T Tw l hd
  have hsymL : elim.matOneValue (elim.transposeM Lw) Lw :=
    sym_of_join Et Lw hEts hLs hsymE (posOfSucc n * ud) (un * lc)
      ((posOfSucc n * ud) * lc) hL
  have hbandL : bandedAt Lw ns :=
    banded_of_join Et Lw hEts hLs (posOfSucc n * ud) (un * lc)
      ((posOfSucc n * ud) * lc) hL ns hband
  have hAl : A.length = o := sqAt_len hAs
  have hA'l : A'.length = o := sqAt_len hA's
  have hVl : Vw.length = o := sqAt_len hVs
  have hLwl : Lw.length = o := sqAt_len hLs
  have hA'r : rowsLen o A' := rowsLen_of_sqAt hA's
  have hUl : (matPow Vw o (n + 1)).length = o := length_matPow Vw o hVl
      (n + 1)
  have hLl : (matPow Lw o (n + 1)).length = o := length_matPow Lw o hLwl
      (n + 1)
  have hLr : rowsLen o (matPow Lw o (n + 1)) := rowsLen_matPow Lw o hLwl
      (n + 1)
  have hLsq : sqAt (matPow Lw o (n + 1)) o := sqAt_of hLl hLr
  have hsymLP : elim.matOneValue (elim.transposeM (matPow Lw o (n + 1)))
      (matPow Lw o (n + 1)) :=
    transposeM_matPow Lw hLs hsymL (n + 1)
  have hALl : (matMul A (matPow Lw o (n + 1))).length = o :=
    (length_matMul A (matPow Lw o (n + 1))).trans hAl
  have hALr : rowsLen o (matMul A (matPow Lw o (n + 1))) :=
    rowsLen_cast (transposeLen (matPow Lw o (n + 1)) hLr hLl)
        (rowsLen_matMul A (matPow Lw o (n + 1)))
  have hTl :
      (matMul (matPow Lw o (n + 1))
      (matMul A (matPow Lw o (n + 1)))).length = o :=
    (length_matMul (matPow Lw o (n + 1))
        (matMul A (matPow Lw o (n + 1)))).trans hLl
  have hTr : rowsLen o
      (matMul (matPow Lw o (n + 1)) (matMul A (matPow Lw o (n + 1)))) :=
    rowsLen_cast (transposeLen (matMul A (matPow Lw o (n + 1))) hALr hALl)
      (rowsLen_matMul (matPow Lw o (n + 1))
          (matMul A (matPow Lw o (n + 1))))
  have hTs : sqAt
      (matMul (matPow Lw o (n + 1)) (matMul A (matPow Lw o (n + 1)))) o :=
      sqAt_of hTl hTr
  have hwl : (elim.matVec A' y).length = o :=
      (elim.matVec_length A' y).trans hA'l
  have hu1l :
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)).length = o :=
    (elim.matVec_length (matPow Vw o (n + 1)) (elim.matVec A' y)).trans
        hUl
  have ha1l :
      (elim.matVec A
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y))).length = o
      :=
      (elim.matVec_length A
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y))).trans hAl
  have haxl : (elim.matVec A' x).length = o :=
      (elim.matVec_length A' x).trans hA'l
  have hu4l : (elim.matVec (matPow Vw o (n + 1)) y).length = o :=
      (elim.matVec_length (matPow Vw o (n + 1)) y).trans hUl
  have ha4l : (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)).length
      = o :=
      (elim.matVec_length A (elim.matVec (matPow Vw o (n + 1)) y)).trans
      hAl
  have hUa4l :
      (elim.matVec (matPow Vw o (n + 1))
      (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))).length = o :=
    (elim.matVec_length (matPow Vw o (n + 1))
        (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))).trans hUl
  have hlxl : (elim.matVec (matPow Lw o (n + 1)) x).length = o :=
      (elim.matVec_length (matPow Lw o (n + 1)) x).trans hLl
  have hp2l : (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x)).length
      = o :=
      (elim.matVec_length A (elim.matVec (matPow Lw o (n + 1)) x)).trans
      hAl
  have hlaxl :
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)).length = o :=
    (elim.matVec_length (matPow Lw o (n + 1)) (elim.matVec A' x)).trans
        hLl
  have hp4l :
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x))).length = o
      :=
      (elim.matVec_length A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x))).trans hAl
  have hLwv :
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y)).length = o :=
    (elim.matVec_length (matPow Lw o (n + 1)) (elim.matVec A' y)).trans
        hLl
  have hALw :
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y))).length = o
      :=
    (elim.matVec_length A
        (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y))).trans hAl
  have hLy : (elim.matVec (matPow Lw o (n + 1)) y).length = o :=
      (elim.matVec_length (matPow Lw o (n + 1)) y).trans hLl
  have hALy : (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) y)).length
      = o :=
    (elim.matVec_length A (elim.matVec (matPow Lw o (n + 1)) y)).trans hAl
  have hLALy :
      (elim.matVec (matPow Lw o (n + 1))
      (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) y))).length = o :=
    (elim.matVec_length (matPow Lw o (n + 1))
        (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) y))).trans hLl
  -- Step 1: the two null reads
  have hnull := lead_tail_null
      (matMul (matPow Lw o (n + 1)) (matMul A (matPow Lw o (n + 1)))) A'
      hTs hA's
    (ground.prefixAt (j + (n + 1)) ns)
    (lead_sandwich Lw A hLs hAs ns hns hbandL j (n + 1) hlead) htail
  have hchain3 : poly.oneValue
      (elim.matVec
          (matMul
          (matMul (matPow Lw o (n + 1)) (matMul A (matPow Lw o (n + 1))))
          A') y)
      (elim.matVec (matPow Lw o (n + 1))
          (elim.matVec A
          (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y)))) :=
    poly.oneValue_trans
      (elim.matVec_matMul
          (matMul (matPow Lw o (n + 1)) (matMul A (matPow Lw o (n + 1))))
          A' o hA'r y hy)
      (poly.oneValue_trans
        (elim.matVec_matMul (matPow Lw o (n + 1))
            (matMul A (matPow Lw o (n + 1))) o hALr (elim.matVec A' y)
            hwl)
        (elim.matVec_congr (matPow Lw o (n + 1)) _ _
          (elim.matVec_matMul A (matPow Lw o (n + 1)) o hLr
              (elim.matVec A' y) hwl)))
  have hX3null :
      (elim.dotP x
      (elim.matVec (matPow Lw o (n + 1))
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y))))).oneValue
      BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (elim.dotP_oneValue_right x _ _ hchain3))
      (matNull_dotP _ hnull.1 x y)
  have hchain6 : poly.oneValue
      (elim.matVec
          (matMul A'
          (matMul (matPow Lw o (n + 1)) (matMul A (matPow Lw o (n + 1)))))
          y)
      (elim.matVec A'
          (elim.matVec (matPow Lw o (n + 1))
          (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) y)))) :=
    poly.oneValue_trans
      (elim.matVec_matMul A'
          (matMul (matPow Lw o (n + 1)) (matMul A (matPow Lw o (n + 1))))
          o hTr y hy)
      (elim.matVec_congr A' _ _
        (poly.oneValue_trans
          (elim.matVec_matMul (matPow Lw o (n + 1))
              (matMul A (matPow Lw o (n + 1))) o hALr y hy)
          (elim.matVec_congr (matPow Lw o (n + 1)) _ _
            (elim.matVec_matMul A (matPow Lw o (n + 1)) o hLr y hy))))
  have hX6null :
      (elim.dotP
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)))
      (elim.matVec (matPow Lw o (n + 1)) y)).oneValue BPair.unit :=
    BPair.oneValue_trans
      (elim.dotP_matVec_sym A hAs hsymA
          (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x))
          (elim.matVec (matPow Lw o (n + 1)) y) hlaxl hLy)
      (BPair.oneValue_trans
        (elim.dotP_matVec_sym (matPow Lw o (n + 1)) hLsq hsymLP
            (elim.matVec A' x)
            (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) y)) haxl
            hALy)
        (BPair.oneValue_trans
          (elim.dotP_matVec_sym A' hA's hsymA' x
              (elim.matVec (matPow Lw o (n + 1))
              (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) y))) hx
              hLALy)
          (BPair.oneValue_trans
            (BPair.oneValue_symm
              (elim.dotP_oneValue_right x _ _ hchain6))
            (matNull_dotP _ hnull.2 x y))))
  -- Step 2: the walks
  have hw12 :
      (elim.dotP x
      (elim.matVec (matPow Lw o (n + 1))
      (elim.matVec A
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y))))).oneValue
      (elim.dotP (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x))
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y))) :=
    BPair.oneValue_trans
        (BPair.oneValue_symm
          (elim.dotP_matVec_sym (matPow Lw o (n + 1)) hLsq hsymLP x
            (elim.matVec A
              (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))
            hx ha1l))
      (BPair.oneValue_symm
        (elim.dotP_matVec_sym A hAs hsymA
          (elim.matVec (matPow Lw o (n + 1)) x)
          (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)) hlxl
          hu1l))
  have hw13 :
      (elim.dotP x
      (elim.matVec (matPow Lw o (n + 1))
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y))))).oneValue
      (elim.dotP (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x))
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y))) :=
    BPair.oneValue_trans
        (BPair.oneValue_symm
          (elim.dotP_matVec_sym (matPow Lw o (n + 1)) hLsq hsymLP x
            (elim.matVec A
              (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y)))
            hx hALw))
      (BPair.oneValue_symm
        (elim.dotP_matVec_sym A hAs hsymA
          (elim.matVec (matPow Lw o (n + 1)) x)
          (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y)) hlxl
          hLwv))
  have hw4 :
      (elim.dotP x
      (elim.matVec A'
      (elim.matVec (matPow Vw o (n + 1))
      (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))))).oneValue
      (elim.dotP (elim.matVec A' x)
      (elim.matVec (matPow Vw o (n + 1))
      (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)))) :=
    BPair.oneValue_symm
      (elim.dotP_matVec_sym A' hA's hsymA' x
        (elim.matVec (matPow Vw o (n + 1))
          (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))) hx
        hUa4l)
  have hw5 :
      (elim.dotP (elim.matVec A' x)
      (elim.matVec (matPow Lw o (n + 1))
      (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)))).oneValue
      (elim.dotP
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)))
      (elim.matVec (matPow Vw o (n + 1)) y)) :=
    BPair.oneValue_trans
        (BPair.oneValue_symm
          (elim.dotP_matVec_sym (matPow Lw o (n + 1)) hLsq hsymLP
            (elim.matVec A' x)
            (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)) haxl
            ha4l))
      (BPair.oneValue_symm
        (elim.dotP_matVec_sym A hAs hsymA
          (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x))
          (elim.matVec (matPow Vw o (n + 1)) y) hlaxl hu4l))
  -- Step 3: the telescopes and the four pair prices
  have hT1 := ground.leB_congr_left
    (BPair.oneValue_of_eq
        (windowsep.mag_scale
        (elim.dotP x
        (elim.matVec (matPow Vw o (n + 1))
        (elim.matVec A
        (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))))
        ((Pos.pow lc (n + 1)) * (Pos.pow lc (n + 1)))))
    (magTele
        (elim.dotP x
        (elim.matVec (matPow Vw o (n + 1))
        (elim.matVec A
        (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))))
        (elim.dotP x
        (elim.matVec (matPow Lw o (n + 1))
        (elim.matVec A
        (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))))
        (elim.dotP x
        (elim.matVec (matPow Lw o (n + 1))
        (elim.matVec A
        (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' y)))))
        (Pos.pow lc (n + 1)) (Pos.pow vc (n + 1)) hX3null)
  have hT2 := ground.leB_congr_left
    (BPair.oneValue_of_eq
        (windowsep.mag_scale
        (elim.dotP (elim.matVec A' x)
        (elim.matVec (matPow Vw o (n + 1))
        (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))))
        ((Pos.pow lc (n + 1)) * (Pos.pow lc (n + 1)))))
    (magTele
        (elim.dotP (elim.matVec A' x)
        (elim.matVec (matPow Vw o (n + 1))
        (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))))
        (elim.dotP (elim.matVec A' x)
        (elim.matVec (matPow Lw o (n + 1))
        (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))))
        (elim.dotP
        (elim.matVec A
        (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)))
        (elim.matVec (matPow Lw o (n + 1)) y)) (Pos.pow lc (n + 1))
        (Pos.pow vc (n + 1)) hX6null)
  have hP1 := dPrice Et T Tw l hd un ud kn kd lc vc n ws hw Lw Vw hLs hVs
      hL hV ((an * bn) * Pos.pow cn (n + 1))
      ((ad * bd) * Pos.pow cd (n + 1)) x
      (elim.matVec A
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y))) hx ha1l
  have hP3 := dPrice Et T Tw l hd un ud kn kd lc vc n ws hw Lw Vw hLs hVs
      hL hV ((an * bd) * Pos.pow cn (n + 1))
      ((ad * bn) * Pos.pow cd (n + 1)) (elim.matVec A' x)
      (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)) haxl ha4l
  rw [posXch an bd (Pos.pow cn (n + 1)) ad bn (Pos.pow cd (n + 1))]
    at hP3
  have hP2 := ground.leB_congr_left
    (BPair.scale_congr (2 * (posOfSucc n * ((ud * ud) * (kd * kd))))
      (BPair.scale_congr
        (((ad * bn) * Pos.pow ed (n + 1))
          * ((an * bd) * Pos.pow en (n + 1)))
        (BPair.oneValue_symm (windowsep.mag_congr
          (BPair.add_congr
            (BPair.scale_congr (Pos.pow lc (n + 1)) hw12)
            (ground.swap_congr
              (BPair.scale_congr (Pos.pow vc (n + 1)) hw13)))))))
    (dPrice Et T Tw l hd un ud kn kd lc vc n ws hw Lw Vw hLs hVs hL hV
        ((ad * bn) * Pos.pow ed (n + 1))
        ((an * bd) * Pos.pow en (n + 1))
        (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x))
        (elim.matVec A' y) hp2l hwl)
  rw [posXch ad bn (Pos.pow ed (n + 1)) an bd (Pos.pow en (n + 1))]
    at hP2
  have hP4 := ground.leB_congr_left
    (BPair.scale_congr (2 * (posOfSucc n * ((ud * ud) * (kd * kd))))
      (BPair.scale_congr
        (((ad * bd) * Pos.pow ed (n + 1))
          * ((an * bn) * Pos.pow en (n + 1)))
        (BPair.oneValue_symm (windowsep.mag_congr
          (BPair.add_congr
            (BPair.scale_congr (Pos.pow lc (n + 1)) hw5)
            (BPair.oneValue_refl
              (((elim.dotP
                (elim.matVec A
                (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)))
                (elim.matVec (matPow Lw o (n + 1)) y)).scale
                (Pos.pow vc (n + 1))).swap)))))))
    (dPrice Et T Tw l hd un ud kn kd lc vc n ws hw Lw Vw hLs hVs hL hV
        ((ad * bd) * Pos.pow ed (n + 1))
        ((an * bn) * Pos.pow en (n + 1))
        (elim.matVec A
        (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x))) y hp4l hy)
  -- Step 4: the gram caps
  have hc1 :
      (elim.dotP
      (elim.matVec A
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))
      (elim.matVec A
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))).scale
      ((ad * ad) * ((bd * bd) * Pos.pow (cd * cd) (n + 1))) ≤
      (elim.dotP y y).scale
      ((an * an) * ((bn * bn) * Pos.pow (cn * cn) (n + 1))) :=
    chain3 _ _ _ _ (an * an) (ad * ad) (Pos.pow (cn * cn) (n + 1))
        (Pos.pow (cd * cd) (n + 1)) (bn * bn) (bd * bd)
      (capP A an ad spA spA' hcapA
          (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)) hu1l)
      (cap_pow Vw cn cd spU spU' hcapU (elim.matVec A' y) hwl (n + 1))
      (capP A' bn bd spB spB' hcapB y hy)
  rw [← posSq ad bd cd (n + 1), ← posSq an bn cn (n + 1)] at hc1
  have hc2p :
      (elim.dotP (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x))
      (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x))).scale
      ((ad * ad) * (Pos.pow (ed * ed) (n + 1)))
      ≤ (elim.dotP x x).scale ((an * an) * (Pos.pow (en * en) (n + 1))) :=
    chain2 _ _ _ (an * an) (ad * ad) (Pos.pow (en * en) (n + 1))
        (Pos.pow (ed * ed) (n + 1))
      (capP A an ad spA spA' hcapA (elim.matVec (matPow Lw o (n + 1)) x)
          hlxl)
      (cap_pow Lw en ed spL spL' hcapL x hx (n + 1))
  have hc2w : (elim.dotP (elim.matVec A' y) (elim.matVec A' y)).scale
      (bd * bd)
      ≤ (elim.dotP y y).scale (bn * bn) := capP A' bn bd spB spB' hcapB y
          hy
  have hc3p : (elim.dotP (elim.matVec A' x) (elim.matVec A' x)).scale
      (bd * bd)
      ≤ (elim.dotP x x).scale (bn * bn) := capP A' bn bd spB spB' hcapB x
          hx
  have hc3q :
      (elim.dotP (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))
      (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))).scale
      ((ad * ad) * (Pos.pow (cd * cd) (n + 1)))
      ≤ (elim.dotP y y).scale ((an * an) * (Pos.pow (cn * cn) (n + 1))) :=
    chain2 _ _ _ (an * an) (ad * ad) (Pos.pow (cn * cn) (n + 1))
        (Pos.pow (cd * cd) (n + 1))
      (capP A an ad spA spA' hcapA (elim.matVec (matPow Vw o (n + 1)) y)
          hu4l)
      (cap_pow Vw cn cd spU spU' hcapU y hy (n + 1))
  have hc4p :
      (elim.dotP
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)))
      (elim.matVec A
      (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)))).scale
      ((ad * ad) * ((bd * bd) * Pos.pow (ed * ed) (n + 1))) ≤
      (elim.dotP x x).scale
      ((an * an) * ((bn * bn) * Pos.pow (en * en) (n + 1))) :=
    chain3 _ _ _ _ (an * an) (ad * ad) (Pos.pow (en * en) (n + 1))
        (Pos.pow (ed * ed) (n + 1)) (bn * bn) (bd * bd)
      (capP A an ad spA spA' hcapA
          (elim.matVec (matPow Lw o (n + 1)) (elim.matVec A' x)) hlaxl)
      (cap_pow Lw en ed spL spL' hcapL (elim.matVec A' x) haxl (n + 1))
      (capP A' bn bd spB spB' hcapB x hx)
  rw [← posSq ad bd ed (n + 1), ← posSq an bn en (n + 1)] at hc4p
  -- Step 5: the assembly
  have hGap : windowsep.mag
      ((elim.dotP x
      (elim.matVec (matPow Vw o (n + 1))
      (elim.matVec A
      (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y))))) +
      (elim.dotP x
      (elim.matVec A'
      (elim.matVec (matPow Vw o (n + 1))
      (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))))).swap)
      ≤ windowsep.mag
          (elim.dotP x
          (elim.matVec (matPow Vw o (n + 1))
          (elim.matVec A
          (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y))))) +
          windowsep.mag
          (elim.dotP (elim.matVec A' x)
          (elim.matVec (matPow Vw o (n + 1))
          (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)))) :=
    ground.leB_congr_right
      (BPair.add_congr
          (BPair.oneValue_refl
          (windowsep.mag
          (elim.dotP x
          (elim.matVec (matPow Vw o (n + 1))
          (elim.matVec A
          (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))))))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
              (windowsep.mag_swap
              (elim.dotP x
              (elim.matVec A'
              (elim.matVec (matPow Vw o (n + 1))
              (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)))))))
          (windowsep.mag_congr hw4)))
      (windowsep.mag_add_le
          (elim.dotP x
          (elim.matVec (matPow Vw o (n + 1))
          (elim.matVec A
          (elim.matVec (matPow Vw o (n + 1)) (elim.matVec A' y)))))
          (elim.dotP x
          (elim.matVec A'
          (elim.matVec (matPow Vw o (n + 1))
          (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))))).swap)
  -- Step 5b: the branch joins at the uniform weights
  have h2p := ground.leB_scale hc2p (bn * bn)
  rw [BPair.scale_scale
      (elim.dotP (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x))
        (elim.matVec A (elim.matVec (matPow Lw o (n + 1)) x)))
      ((ad * ad) * (Pos.pow (ed * ed) (n + 1))) (bn * bn),
    BPair.scale_scale (elim.dotP x x)
      ((an * an) * (Pos.pow (en * en) (n + 1))) (bn * bn),
    ground.mul_assoc (ad * ad) (Pos.pow (ed * ed) (n + 1)) (bn * bn),
    ground.mul_comm (Pos.pow (ed * ed) (n + 1)) (bn * bn),
    ground.mul_assoc (an * an) (Pos.pow (en * en) (n + 1)) (bn * bn),
    ground.mul_comm (Pos.pow (en * en) (n + 1)) (bn * bn),
    ← posSq ad bn ed (n + 1), ← posSq an bn en (n + 1)] at h2p
  have h2w := ground.leB_scale hc2w
    ((an * an) * Pos.pow (en * en) (n + 1))
  rw [BPair.scale_scale
      (elim.dotP (elim.matVec A' y) (elim.matVec A' y)) (bd * bd)
      ((an * an) * Pos.pow (en * en) (n + 1)),
    BPair.scale_scale (elim.dotP y y) (bn * bn)
      ((an * an) * Pos.pow (en * en) (n + 1)),
    ground.mul_left_comm (bd * bd) (an * an)
      (Pos.pow (en * en) (n + 1)),
    ground.mul_left_comm (bn * bn) (an * an)
      (Pos.pow (en * en) (n + 1)),
    ← posSq an bd en (n + 1), ← posSq an bn en (n + 1)] at h2w
  have h3p := ground.leB_scale hc3p
    ((an * an) * Pos.pow (cn * cn) (n + 1))
  rw [BPair.scale_scale
      (elim.dotP (elim.matVec A' x) (elim.matVec A' x)) (bd * bd)
      ((an * an) * Pos.pow (cn * cn) (n + 1)),
    BPair.scale_scale (elim.dotP x x) (bn * bn)
      ((an * an) * Pos.pow (cn * cn) (n + 1)),
    ground.mul_left_comm (bd * bd) (an * an)
      (Pos.pow (cn * cn) (n + 1)),
    ground.mul_left_comm (bn * bn) (an * an)
      (Pos.pow (cn * cn) (n + 1)),
    ← posSq an bd cn (n + 1), ← posSq an bn cn (n + 1)] at h3p
  have h3q := ground.leB_scale hc3q (bn * bn)
  rw [BPair.scale_scale
      (elim.dotP (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y))
        (elim.matVec A (elim.matVec (matPow Vw o (n + 1)) y)))
      ((ad * ad) * (Pos.pow (cd * cd) (n + 1))) (bn * bn),
    BPair.scale_scale (elim.dotP y y)
      ((an * an) * (Pos.pow (cn * cn) (n + 1))) (bn * bn),
    ground.mul_assoc (ad * ad) (Pos.pow (cd * cd) (n + 1)) (bn * bn),
    ground.mul_comm (Pos.pow (cd * cd) (n + 1)) (bn * bn),
    ground.mul_assoc (an * an) (Pos.pow (cn * cn) (n + 1)) (bn * bn),
    ground.mul_comm (Pos.pow (cn * cn) (n + 1)) (bn * bn),
    ← posSq ad bn cd (n + 1), ← posSq an bn cn (n + 1)] at h3q
  have hQ1 := qJoin _ _ _ _ _ _ _ _ _ hP1 (ground.leB_refl _) hc1
  have hQ2 := qJoin _ _ _ _ _ _ _ _ _ hP2 h2p h2w
  have hQ3 := qJoin _ _ _ _ _ _ _ _ _ hP3 h3p h3q
  have hQ4 := qJoin _ _ _ _ _ _ _ _ _ hP4 hc4p (ground.leB_refl _)
  exact magAssemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hGap hT1 hT2 hQ1 hQ2 hQ3 hQ4

end groundreads
