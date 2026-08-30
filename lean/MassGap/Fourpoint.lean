import MassGap.Groundreads
import MassGap.Carrier
/-!
`lem:fourpoint` — the four-point floor.  The side: at the pair fold
`S := Σ_k w_k [1 : 6 + ĉ₂(k)]` over the adjoint square's channel
list at the module–pair weights `w_k = [m_k d_k : d_θ²]`, the
channel list's two closure identities — the completeness
`Σ_k m_k d_k = d_θ²` (`fusion.dimLaw`) and the uniform drift
`Σ_k m_k d_k ĉ₂(k) = 2 d_θ²` (`fusion.driftLaw` at the adjoint) —
read `Σ_k w_k (6 + ĉ₂(k)) = 8`, and the product of `S` with that
fold against the weights' squared fold collects per channel pair,
each pair's cleared read the square identity, one display per
pair: `8 S = 1 + Σ_{k<l} w_k w_l ⟨ĉ₂(k) : ĉ₂(l)⟩² [1 : (6 + ĉ₂(k))
(6 + ĉ₂(l))]`, every summand a square at pair weights, so `8 S`
exceeds one at the unit channel's term against the `θ` channel's,
`[c₁ : 42 d_θ³]`, or beyond.
The derivation tier reads a channel as its cleared datum `(u, a)`,
the weight's numerator `m d` and the content `6 + ĉ₂` at the
Casimir's second member, over the balance carrier with a clearing
denominator: the fold of the reads `[u : a]` (`sumQ`), the weight
and content folds (`tSum`, `aSum`), a pair's term `u u' ⟨a : a'⟩²`
over `a a'` (`term`) and the pair sum over the list's pairs
(`crossAt` at one channel against the rest, `pairSum` the whole).
The jet: the connected four-point partition fold `ϰ₄` at a moment
family, each field twice, is the displayed balance pair of the
odd-count partitions' moment products against the even, at the
block-count weights, over any carrier with the displayed sum,
product and partner (`kappa4` at `ground.DOps`); the graph's free
moments `m_a := Eval(χ_θ^a)` are the invariant counts of the
adjoint lists (`moment` at `carrier.invCount`) and the `k`-counts
`T_a(k)` of the powers the families' folds at the labels
(`powCount` over `powFam`, the row expansion from the adjoint's
own); the jet moments at the displayed orders are the polynomials
in `τ²` over the composite pairs
`μ̂_ab = m_a m_b + τ² [1 : 2] (m_{a+1} m_b + m_a m_{b+1}) + τ⁴ D_ab`
(`jetMoment` at `poly.polyO ground.bpairQOps`), `D_ab` the join's
datum at its three folds — the pair insertions' square reads, the
single-plaquette channels' solves over the square's nonunit
channels at the Casimir's cleared read, and the pair networks'
`T_a(θ) T_b(θ) S` — against the partner of `[1 : 8] m_a m_b`
(`jetD`).  The collection (`collection`): the fold at the jet
moments reads the unit at `τ⁰` and `τ²` and `c₁² ⟨S : [1 : 8]⟩` at
`τ⁴`, at the reads `m₁` of equal members, `m₂ = 1`, `m₃ = c₁`
and `T₂(θ) = c₁`, the square reads' collection through the three
fourth-order data.
The jet at the theta graph: the free end's ground jet
`ψ̂ = 1 + τ² ψ₁ + τ⁴ ψ₂` at `ψ₁ = [1 : 4](q₁ + q₂)` and `ψ₂` the
second-order solve at `M ψ₁`'s components off the unit line, read at
the graph's evaluation split (`thm:network`(i)) against the
`q`-monomials — the modules' reads at the powers (`oneRead`), the
channels' at the `k`-counts and the pair sectors' at the weights
(`twoRead`) — so the jet's pairing polynomial `⟨ψ̂, q₁^a q₂^b ψ̂⟩`
through `τ⁴` (`jetPair`, the gram its `(0, 0)` instance) is the jet
moments' product with the gram (`jetRead`): the displayed orders are
the normalized pairing, `D_ab + [1 : 8] m_a m_b` the `τ⁴` read at the
gram's eighth.  A window beyond the graph's band reads the pair's at
every far datum (`farPair`, `jetWindow`).
The tail (`lem:fourpoint`'s last paragraph), at `thm:groundreads`(iii)'s
own level — matrices and vectors over the balance pairs at the unit
gram, the ray `[1 : τ²]` at `τ = [p : q]` cleared: the pencil's site
datum `q²E − p²M` (`rayH`), the jet `q⁴ψ̂` (`jetVec`) and the residual
`4q⁸ρ` (`residVec`).  `jetResidual` is the identity `Hψ̂ = ε̂ψ̂ + ρ` at
the reads `E𝟏 = 0`, `Eψ₁ = M𝟏`, `4Eψ₂ + #p𝟏 = 4Mψ₁`; `solveFloor` the
second-order weight's cap `ℓ²⟨ψ₂,ψ₂⟩ ≤ W²⟨ψ₁,ψ₁⟩` at the solve floor
and the magnetic square cap; `residWeight` the residual's weight at the
squares' fold twice, `⟨ρ,ρ⟩ ≤ τ¹²Q(τ)`; and `offLine_drift` the ground's
gap from the jet — the transport display's pairing step at the level
gap's clearance less the drift, the drift floored at the magnetic cap
through the ground's own Rayleigh read,
`⟨γ' : τ²W⟩²⟨φ,φ⟩ ≤ ⟨ρ,ρ⟩`.  The count's fold of squares at a matrix
sum and the squares' fold at a vector sum are `def:elim`'s
(`elim.matSumL_sq_cap`, `elim.dotN_vecAdd_sq_le`).
The tail's brackets.  `truncBracket` is the truncation beyond `τ⁴`: the
jet state's moment is the pairing at the full jet against its gram,
degree eight in the two clearings (`jetQuad`, `jetGram`), the displayed
read through `τ⁴` its keys nought to two (`jetDisplay`), and the datum
`N_A = P_A − μ̂_A G` at the keys three to six is capped key by key at the
observable's cap, the display's three coefficients' magnitudes, the
gram's key-two read and the second-order weight's cap (`truncCap`),
`|N_A(τ)| ≤ τ⁶ T_A(τ)`.  `momentBracket` is the moments' brackets at
the jet: the transport display's width read at the jet as the later
ground, the off-line weight priced by the residual at the drift's
clearing and the residual's weight by the root caps `K₀`, `K₁`
(`offLine_drift`, `residWeight`), one polarization at the observable's
cap through `thm:groundreads`(iii)'s two width reads
(`groundreads.readClose`, `groundreads.readCrude`),
`γ' |ω(A) − ω̂(A)| ≤ 4 c_A w` at `w ⟨γ' : τ²W⟩ = γ' τ⁶ K(τ)`.
`foldBracket` is the partition fold's bracket at two moment families:
the fold's gap telescopes factor by factor, every term at field count
four and one move per moment factor at the block-count weights, `75`
in all, each order the composite pair's cross-multiplied read.
`gapBracket` chains the two brackets through the reads' gap at one
factor's move — the moments' at the jet and the truncation's at the
display, the jet state's clearing stripped at the gram's floor `q⁸` —
`δ ≤ [4c w : γ'] + τ⁶T` at the two brackets' own clearings, and
`kappaBracket` is the fold's bracket at the window carrier: the moment
families the ground state's reads and the jet's displays, each
factor's move priced by the gap bracket and folded under the one
datum, `|κ₄(ω) − κ₄(μ̂(τ))| ≤ 75 D`.
The cell (`lem:fourpoint`'s last display): `tailPoly` and `compPoly` are
the tail's fold and the comparison in the squared ray coordinate, cleared
at the drift clearance's second datum; `compCross` reads the comparison on
its lower side at the crossing `u W = γ'`, the leading read's members
equal there with the occupied root-cap term standing alone; and
`cellFloor` is the floor on the cell — at the priced side certificate
from the free end (`stage.keepUpper`), a ray whose squared point sits in
the segment, and the tail's bracket cleared at the drift's clearing, the
four-point read sits at its upper side at the margin `[1 : 2] τ⁴ c` or
beyond, the crossing's lower side putting the segment inside the drift's
clearance and the clearing's occupied gap withdrawing the bracket.
-/

namespace fourpoint
open ground

/-- The fold of the reads `[u : a]` over the channels. -/
private def sumQ : List (Pos × Pos) → BPair × Pos
  | [] => (BPair.unit, Pos.one)
  | x :: xs => BPair.addQ (BPair.ofPos x.1, x.2) (sumQ xs)

/-- The weights' fold `Σ u`. -/
private def tSum : List (Pos × Pos) → BPair
  | [] => BPair.unit
  | x :: xs => BPair.ofPos x.1 + tSum xs

/-- The contents' weighted fold `Σ u a`. -/
private def aSum : List (Pos × Pos) → BPair
  | [] => BPair.unit
  | x :: xs => BPair.ofPos (x.1 * x.2) + aSum xs

/-- A pair's term, `u u' ⟨a : a'⟩²` over `a a'`. -/
private def term (x y : Pos × Pos) : BPair × Pos :=
  (BPair.ofPos (x.1 * y.1) * (BPair.mk x.2 y.2 * BPair.mk x.2 y.2),
    x.2 * y.2)

/-- One channel's terms against a list. -/
private def crossAt (x : Pos × Pos) : List (Pos × Pos) → BPair × Pos
  | [] => (BPair.unit, Pos.one)
  | y :: ys => BPair.addQ (term x y) (crossAt x ys)

/-- The pair sum over the list's pairs, each pair once. -/
private def pairSum : List (Pos × Pos) → BPair × Pos
  | [] => (BPair.unit, Pos.one)
  | x :: xs => BPair.addQ (crossAt x xs) (pairSum xs)

/-! The cleared read's kit at `def:ground`: a balance factor
distributes over the join. -/

/-- A balance factor at a carried read. -/
private def qscale (c : BPair) (p : BPair × Pos) : BPair × Pos :=
  (c * p.1, p.2)

private theorem qscale_add (c : BPair) (p q : BPair × Pos) :
    qscale c (BPair.addQ p q) = BPair.addQ (qscale c p) (qscale c q) := by
  show (c * (p.1.scale q.2 + q.1.scale p.2), p.2 * q.2)
    = ((c * p.1).scale q.2 + (c * q.1).scale p.2, p.2 * q.2)
  rw [BPair.left_distrib, BPair.mul_scale, BPair.mul_scale]

private theorem qscale_congr {c c' : BPair} {p p' : BPair × Pos}
    (hc : c.oneValue c') (hp : bpairQRead.rel p p') : bpairQRead.rel (qscale c p) (qscale c' p') := by
  show ((c * p.1).scale p'.2).oneValue ((c' * p'.1).scale p.2)
  rw [← BPair.mul_scale, ← BPair.mul_scale]
  exact BPair.mul_congr hc hp

/-! The per-pair read: a pair's term is its two cross reads against
twice the pair's weight, the square identity at the gap. -/

/-- The three cross reads collect to a pair's term. -/
private theorem pair_read (x y : Pos × Pos) :
    bpairQRead.rel (term x y)
      (BPair.addQ (BPair.ofPos (x.1 * x.2) * BPair.ofPos y.1, y.2)
        (BPair.addQ (BPair.ofPos x.1 * BPair.ofPos (y.1 * y.2), x.2)
          ((BPair.ofPos (2 * x.1) * BPair.ofPos y.1).swap, Pos.one))) := by
  obtain ⟨u, a⟩ := x
  obtain ⟨u', b⟩ := y
  show ((BPair.ofPos (u * u') * (BPair.mk a b * BPair.mk a b)).scale
      (b * (a * Pos.one))).oneValue
    (BPair.scale ((BPair.ofPos (u * a) * BPair.ofPos u').scale (a * Pos.one)
      + BPair.scale ((BPair.ofPos u * BPair.ofPos (u' * b)).scale Pos.one
        + (BPair.ofPos (2 * u) * BPair.ofPos u').swap.scale a) b) (a * b))
  rw [ground.mul_one, BPair.scale_one, ground.mul_comm b a]
  refine BPair.scale_congr (a * b) ?_
  rw [BPair.scale_add, ← BPair.add_assoc]
  -- the left side at the square identity
  have hL : (BPair.ofPos (u * u') * (BPair.mk a b * BPair.mk a b)).oneValue
      (BPair.ofPos (u * u') * (BPair.ofPos a * BPair.ofPos a)
        + BPair.ofPos (u * u') * (BPair.ofPos b * BPair.ofPos b)
        + ((BPair.ofPos (u * u') * (BPair.ofPos a * BPair.ofPos b)).swap
          + (BPair.ofPos (u * u') * (BPair.ofPos a * BPair.ofPos b)).swap)) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.mul_congr (BPair.mk_read a b) (BPair.mk_read a b))) ?_
    rw [BPair.sq_expand_swap, BPair.left_distrib, BPair.left_distrib,
      BPair.left_distrib, BPair.mul_swap]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans hL ?_
  -- each cross read at its one-member site
  have h1 : (BPair.ofPos (u * u') * (BPair.ofPos a * BPair.ofPos a)).oneValue
      ((BPair.ofPos (u * a) * BPair.ofPos u').scale a) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.ofPos_mul a a)) ?_
    refine BPair.oneValue_trans (BPair.ofPos_mul (u * u') (a * a)) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.scale_congr a (BPair.ofPos_mul (u * a) u')) ?_
    refine BPair.oneValue_trans (BPair.scale_ofPos (u * a * u') a) ?_
    refine BPair.oneValue_of_eq (congrArg BPair.ofPos ?_)
    rw [ground.mul_right_comm u a u', ground.mul_assoc (u * u') a a]
  have h2 : (BPair.ofPos (u * u') * (BPair.ofPos b * BPair.ofPos b)).oneValue
      ((BPair.ofPos u * BPair.ofPos (u' * b)).scale b) := by
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.ofPos_mul b b)) ?_
    refine BPair.oneValue_trans (BPair.ofPos_mul (u * u') (b * b)) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.scale_congr b (BPair.ofPos_mul u (u' * b))) ?_
    refine BPair.oneValue_trans (BPair.scale_ofPos (u * (u' * b)) b) ?_
    refine BPair.oneValue_of_eq (congrArg BPair.ofPos ?_)
    rw [← ground.mul_assoc u u' b, ground.mul_assoc (u * u') b b]
  have h3 : ((BPair.ofPos (u * u') * (BPair.ofPos a * BPair.ofPos b)).swap
      + (BPair.ofPos (u * u') * (BPair.ofPos a * BPair.ofPos b)).swap).oneValue
      (((BPair.ofPos (2 * u) * BPair.ofPos u').swap.scale a).scale b) := by
    rw [BPair.swap_add, BPair.scale_swap, BPair.scale_swap, BPair.scale_scale]
    refine ground.swap_congr ?_
    rw [← BPair.scale_two]
    refine BPair.oneValue_trans (BPair.scale_congr 2
      (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.ofPos_mul a b)) (BPair.ofPos_mul (u * u') (a * b)))) ?_
    refine BPair.oneValue_trans (BPair.scale_ofPos (u * u' * (a * b)) 2) ?_
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans (BPair.scale_congr (a * b) (BPair.ofPos_mul (2 * u) u')) ?_
    refine BPair.oneValue_trans (BPair.scale_ofPos (2 * u * u') (a * b)) ?_
    refine BPair.oneValue_of_eq (congrArg BPair.ofPos ?_)
    rw [ground.mul_comm (u * u' * (a * b)) 2, ← ground.mul_assoc,
      ← ground.mul_assoc, ← ground.mul_assoc 2 u u',
      ← ground.mul_assoc (2 * u * u') a b]
  exact BPair.add_congr (BPair.add_congr h1 h2) h3

/-! The collection at one channel: its terms against a list collect
to its three cross reads — its weight and content against the
fold, its weight against the content fold, and twice its weight
against the weight fold withdrawn. -/

private theorem qadd_zero :
    bpairQRead.rel (BPair.addQ (BPair.unit, Pos.one) (BPair.unit, Pos.one))
      (BPair.unit, Pos.one) :=
  qOneValue_unit (BPair.add_unit _)

/-- A balance factor at a sum reads the two scaled reads joined. -/
private theorem qsplit (c X Y : BPair) (a : Pos) :
    bpairQRead.rel (c * (X + Y), a) (BPair.addQ (c * X, a) (c * Y, a)) := by
  show ((c * (X + Y)).scale (a * a)).oneValue
    (((c * X).scale a + (c * Y).scale a).scale a)
  rw [BPair.left_distrib, ← BPair.scale_add, BPair.scale_scale]
  exact BPair.oneValue_refl _

private theorem qsplit_swap (c X Y : BPair) :
    bpairQRead.rel ((c * (X + Y)).swap, Pos.one)
      (BPair.addQ ((c * X).swap, Pos.one) ((c * Y).swap, Pos.one)) := by
  show ((c * (X + Y)).swap.scale (Pos.one * Pos.one)).oneValue
    (((c * X).swap.scale Pos.one + (c * Y).swap.scale Pos.one).scale Pos.one)
  rw [BPair.left_distrib, ← BPair.swap_add, ground.mul_one, BPair.scale_one,
    BPair.scale_one, BPair.scale_one, BPair.scale_one]
  exact BPair.oneValue_refl _

/-- One channel's cross reads against a list. -/
private def crossRead (x : Pos × Pos) (xs : List (Pos × Pos)) : BPair × Pos :=
  BPair.addQ (qscale (BPair.ofPos (x.1 * x.2)) (sumQ xs))
    (BPair.addQ (BPair.ofPos x.1 * aSum xs, x.2)
      ((BPair.ofPos (2 * x.1) * tSum xs).swap, Pos.one))

private theorem crossAt_read (x : Pos × Pos) :
    ∀ xs : List (Pos × Pos), bpairQRead.rel (crossAt x xs) (crossRead x xs)
  | [] => by
    refine qOneValue_symm ?_
    show bpairQRead.rel (BPair.addQ (BPair.ofPos (x.1 * x.2) * BPair.unit, Pos.one)
      (BPair.addQ (BPair.ofPos x.1 * BPair.unit, x.2)
        ((BPair.ofPos (2 * x.1) * BPair.unit).swap, Pos.one)))
      (BPair.unit, Pos.one)
    refine qOneValue_trans (BPair.addQ_congr (qOneValue_unit (BPair.mul_unit _))
      (BPair.addQ_congr (qOneValue_unit (BPair.mul_unit _))
        (qOneValue_unit (ground.swap_congr (BPair.mul_unit _))))) ?_
    exact qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) qadd_zero) qadd_zero
  | y :: ys => by
    refine qOneValue_trans (BPair.addQ_congr (pair_read x y) (crossAt_read x ys)) ?_
    refine qOneValue_trans (BPair.addQ_add_comm _ _ _ _) ?_
    refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (BPair.addQ_add_comm _ _ _ _)) ?_
    refine qOneValue_symm ?_
    show bpairQRead.rel (BPair.addQ (qscale (BPair.ofPos (x.1 * x.2))
        (BPair.addQ (BPair.ofPos y.1, y.2) (sumQ ys)))
      (BPair.addQ (BPair.ofPos x.1 * (BPair.ofPos (y.1 * y.2) + aSum ys), x.2)
        ((BPair.ofPos (2 * x.1) * (BPair.ofPos y.1 + tSum ys)).swap,
          Pos.one))) _
    rw [qscale_add]
    exact BPair.addQ_congr (qOneValue_refl _)
      (BPair.addQ_congr (qsplit _ _ _ _) (qsplit_swap _ _ _))

/-! The collection over the list: the contents' weighted fold
against the fold reads the weight fold's square joined to the pair
sum, one channel at a time — the new channel's square, its cross
reads collected to its terms with twice its weight against the
weight fold restored, and the rest the list's own. -/

private theorem qscale_addL (c c' : BPair) (p : BPair × Pos) :
    bpairQRead.rel (qscale (c + c') p) (BPair.addQ (qscale c p) (qscale c' p)) := by
  show (((c + c') * p.1).scale (p.2 * p.2)).oneValue
    (((c * p.1).scale p.2 + (c' * p.1).scale p.2).scale p.2)
  rw [BPair.right_distrib, ← BPair.scale_add, BPair.scale_scale]
  exact BPair.oneValue_refl _

private theorem qadd_rot (a b c : BPair × Pos) :
    bpairQRead.rel (BPair.addQ a (BPair.addQ b c)) (BPair.addQ b (BPair.addQ a c)) := by
  refine qOneValue_trans (qOneValue_symm (BPair.addQ_assoc a b c)) ?_
  refine qOneValue_trans (BPair.addQ_congr (BPair.addQ_comm a b) (qOneValue_refl c)) ?_
  exact BPair.addQ_assoc b a c

/-- A read against its partner reads the sum's unit. -/
private theorem qadd_neg (p : BPair × Pos) : bpairQRead.rel (BPair.addQ p (bpairQOps.swap p)) bpairQOps.unit := by
  refine qOneValue_unit ?_
  show (p.1.scale p.2 + p.1.swap.scale p.2).oneValue BPair.unit
  rw [← BPair.scale_add]
  refine BPair.oneValue_trans (BPair.scale_congr p.2
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.swap_add_null (BPair.oneValue_refl p.1)))) ?_
  show Pos.one * p.2 + Pos.one = Pos.one + Pos.one * p.2
  exact ground.add_comm _ _

private theorem qneg_read (Z : BPair) :
    bpairQRead.rel (BPair.addQ (Z.swap, Pos.one) (Z, Pos.one)) (BPair.unit, Pos.one) :=
  qOneValue_trans (BPair.addQ_comm _ _) (qadd_neg (Z, Pos.one))

/-- The new channel's square: its weight and content against its
weight over its content is its weight's square. -/
private theorem sq_head (u a : Pos) :
    bpairQRead.rel (BPair.ofPos (u * a) * BPair.ofPos u, a)
      (BPair.ofPos u * BPair.ofPos u, Pos.one) := by
  show ((BPair.ofPos (u * a) * BPair.ofPos u).scale Pos.one).oneValue
    ((BPair.ofPos u * BPair.ofPos u).scale a)
  rw [BPair.scale_one]
  refine BPair.oneValue_trans (BPair.ofPos_mul (u * a) u) ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.scale_congr a (BPair.ofPos_mul u u)) ?_
  refine BPair.oneValue_trans (BPair.scale_ofPos (u * u) a) ?_
  refine BPair.oneValue_of_eq (congrArg BPair.ofPos ?_)
  rw [ground.mul_right_comm u a u]

/-- Twice a weight against a read is the read's doubled product. -/
private theorem two_read (u : Pos) (T : BPair) :
    (BPair.ofPos (2 * u) * T).oneValue (BPair.ofPos u * T + BPair.ofPos u * T) := by
  rw [← BPair.scale_two, BPair.scale_mul_left]
  refine BPair.mul_congr ?_ (BPair.oneValue_refl T)
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.scale_ofPos u 2) ?_
  exact BPair.oneValue_of_eq (congrArg BPair.ofPos (ground.mul_comm u 2))

/-- Two reads at one clearing join at their numerators' sum. -/
private theorem qsplit_one (X Y : BPair) :
    bpairQRead.rel (X + Y, Pos.one) (BPair.addQ (X, Pos.one) (Y, Pos.one)) := by
  show ((X + Y).scale (Pos.one * Pos.one)).oneValue
    ((X.scale Pos.one + Y.scale Pos.one).scale Pos.one)
  rw [ground.mul_one, BPair.scale_one, BPair.scale_one, BPair.scale_one,
    BPair.scale_one]
  exact BPair.oneValue_refl _

private theorem qeq_num {X Y : BPair} (d : Pos) (h : X.oneValue Y) :
    bpairQRead.rel (X, d) (Y, d) :=
  BPair.scale_congr d h

private theorem collect :
    ∀ xs : List (Pos × Pos), bpairQRead.rel (qscale (aSum xs) (sumQ xs))
      (BPair.addQ (tSum xs * tSum xs, Pos.one) (pairSum xs))
  | [] => by
    refine qOneValue_trans (qOneValue_unit (BPair.mul_unit _)) (qOneValue_symm ?_)
    exact qOneValue_trans (BPair.addQ_congr (qOneValue_unit (BPair.mul_unit _)) (qOneValue_refl _))
      qadd_zero
  | x :: xs => by
    have ih := collect xs
    show bpairQRead.rel (qscale (BPair.ofPos (x.1 * x.2) + aSum xs)
        (BPair.addQ (BPair.ofPos x.1, x.2) (sumQ xs)))
      (BPair.addQ ((BPair.ofPos x.1 + tSum xs) * (BPair.ofPos x.1 + tSum xs),
        Pos.one) (BPair.addQ (crossAt x xs) (pairSum xs)))
    refine qOneValue_trans (qscale_addL _ _ _) ?_
    rw [qscale_add, qscale_add]
    refine qOneValue_trans (BPair.addQ_add_comm _ _ _ _) ?_
    refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (BPair.addQ_congr (qOneValue_refl _)
      (qOneValue_symm (qOneValue_trans (BPair.addQ_congr
        (qneg_read (BPair.ofPos (2 * x.1) * tSum xs)) (qOneValue_refl _))
        (BPair.addQ_unitL _))))) ?_
    refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (qOneValue_trans
      (qOneValue_symm (BPair.addQ_assoc _ _ _)) (qOneValue_trans
        (BPair.addQ_congr (qOneValue_symm (BPair.addQ_assoc _ _ _)) (qOneValue_refl _))
        (BPair.addQ_assoc _ _ _)))) ?_
    refine qOneValue_trans (BPair.addQ_assoc _ _ _) ?_
    refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (qOneValue_trans
      (qOneValue_symm (BPair.addQ_assoc _ _ _))
      (BPair.addQ_congr (qadd_rot _ _ _) (qOneValue_refl _)))) ?_
    have hm : qscale (aSum xs) (BPair.ofPos x.1, x.2)
        = (BPair.ofPos x.1 * aSum xs, x.2) := by
      show (aSum xs * BPair.ofPos x.1, x.2) = _
      rw [BPair.mul_comm]
    rw [hm]
    refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (BPair.addQ_congr
      (qOneValue_symm (crossAt_read x xs)) (BPair.addQ_congr (qOneValue_refl _) ih))) ?_
    refine qOneValue_symm ?_
    rw [BPair.sq_expand]
    refine qOneValue_trans (BPair.addQ_congr (qOneValue_trans (qsplit_one _ _)
      (qOneValue_trans (BPair.addQ_congr (qsplit_one _ _) (qOneValue_refl _))
        (BPair.addQ_assoc _ _ _))) (qOneValue_refl _)) ?_
    refine qOneValue_trans (BPair.addQ_congr (BPair.addQ_congr (qOneValue_symm (sq_head x.1 x.2))
      (BPair.addQ_congr (qOneValue_refl _) (qeq_num Pos.one
        (BPair.oneValue_symm (two_read x.1 (tSum xs)))))) (qOneValue_refl _)) ?_
    refine qOneValue_trans (BPair.addQ_assoc _ _ _) ?_
    refine BPair.addQ_congr (qOneValue_refl _) ?_
    refine qOneValue_trans (BPair.addQ_add_comm _ _ _ _) ?_
    refine qOneValue_trans (BPair.addQ_congr (BPair.addQ_comm _ _) (qOneValue_refl _)) ?_
    refine qOneValue_trans (BPair.addQ_assoc _ _ _) ?_
    exact BPair.addQ_congr (qOneValue_refl _) (qadd_rot _ _ _)

/-! The pair sum's side: every term is a square at pair weights, so
the sum sits at or above the unit and at or above any one of its
terms. -/

private theorem unit_le_ofPos (p : Pos) : BPair.unit ≤ BPair.ofPos p :=
  leB_of_lt (unitLtOfPos p)

private theorem term_nn (x y : Pos × Pos) : BPair.unit ≤ (term x y).1 :=
  unitLeMul (unit_le_ofPos _) (unitLeSq _)

private theorem scale_nn {x : BPair} (h : BPair.unit ≤ x) (w : Pos) :
    BPair.unit ≤ x.scale w := by
  refine leB_congr_left ?_ (leB_scale h w)
  show Pos.one * w + Pos.one = Pos.one + Pos.one * w
  exact ground.add_comm _ _

private theorem qadd_nn {p q : BPair × Pos} (hp : BPair.unit ≤ p.1)
    (hq : BPair.unit ≤ q.1) : BPair.unit ≤ (BPair.addQ p q).1 :=
  unitLeAdd (scale_nn hp q.2) (scale_nn hq p.2)

private theorem crossAt_nn (x : Pos × Pos) :
    ∀ ys : List (Pos × Pos), BPair.unit ≤ (crossAt x ys).1
  | [] => leB_refl _
  | _ :: ys => qadd_nn (term_nn _ _) (crossAt_nn x ys)

private theorem pairSum_nn : ∀ xs : List (Pos × Pos), BPair.unit ≤ (pairSum xs).1
  | [] => leB_refl _
  | x :: xs => qadd_nn (crossAt_nn x xs) (pairSum_nn xs)

/-- The order of two carried reads, cross-multiplied. -/
private def qle (p q : BPair × Pos) : Prop := p.1.scale q.2 ≤ q.1.scale p.2

private theorem qle_add_right (p r : BPair × Pos) (hr : BPair.unit ≤ r.1) :
    qle p (BPair.addQ p r) := by
  show p.1.scale (p.2 * r.2) ≤ (p.1.scale r.2 + r.1.scale p.2).scale p.2
  rw [BPair.scale_add, BPair.scale_scale, ground.mul_comm r.2 p.2]
  exact leB_congr_left (BPair.add_unit _)
    (leB_add (leB_refl _) (scale_nn (scale_nn hr p.2) p.2))

private theorem qle_congr_right {p q q' : BPair × Pos} (hq : bpairQRead.rel q q')
    (h : qle p q) : qle p q' := by
  show p.1.scale q'.2 ≤ q'.1.scale p.2
  refine leB_of_scale (w := q.2) ?_
  rw [BPair.scale_comm p.1 q'.2 q.2]
  refine leB_congr_right ?_ (leB_scale h q'.2)
  rw [BPair.scale_comm q.1 p.2 q'.2, BPair.scale_comm q'.1 p.2 q.2]
  exact BPair.scale_congr p.2 hq

private theorem qle_add_left (p r : BPair × Pos) (hr : BPair.unit ≤ r.1) :
    qle p (BPair.addQ r p) :=
  qle_congr_right (BPair.addQ_comm p r) (qle_add_right p r hr)

private theorem qle_trans {p q r : BPair × Pos} (h1 : qle p q) (h2 : qle q r) :
    qle p r := by
  show p.1.scale r.2 ≤ r.1.scale p.2
  refine leB_of_scale (w := q.2) ?_
  rw [BPair.scale_comm p.1 r.2 q.2, BPair.scale_comm r.1 p.2 q.2]
  refine leB_trans (leB_scale h1 r.2) ?_
  rw [BPair.scale_comm q.1 p.2 r.2]
  exact leB_scale h2 p.2

private theorem crossAt_ge (x : Pos × Pos) :
    ∀ (ys : List (Pos × Pos)) (k : Nat), k < ys.length →
      qle (term x (ground.getAt (Pos.one, Pos.one) ys k)) (crossAt x ys)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: ys, 0, _ => qle_add_right _ _ (crossAt_nn x ys)
  | _ :: ys, k + 1, h =>
    qle_trans (crossAt_ge x ys k (Nat.lt_of_succ_lt_succ h))
      (qle_add_left _ _ (term_nn _ _))

private theorem pairSum_ge :
    ∀ (xs : List (Pos × Pos)) (i j : Nat), i < j → j < xs.length →
      qle (term (ground.getAt (Pos.one, Pos.one) xs i) (ground.getAt (Pos.one, Pos.one) xs j))
        (pairSum xs)
  | [], _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, 0, hij, _ => absurd hij (Nat.lt_irrefl 0)
  | x :: xs, 0, k + 1, _, hj =>
    qle_trans (crossAt_ge x xs k (Nat.lt_of_succ_lt_succ hj))
      (qle_add_right _ _ (pairSum_nn xs))
  | _ :: _, _ + 1, 0, hij, _ => absurd hij (Nat.not_lt_zero _)
  | x :: xs, i + 1, j + 1, hij, hj =>
    qle_trans (pairSum_ge xs i j (Nat.lt_of_succ_lt_succ hij)
      (Nat.lt_of_succ_lt_succ hj))
      (qle_add_left _ _ (crossAt_nn x xs))

/-! The interface tier: the channel list's cleared data over the
adjoint square's row at an occupied Casimir scale, the pair fold
`S`, and the bridges from the interface's count folds — the
completeness and the drift — to the derivation's weight and
content folds. -/

/-- The channels' cleared data at the Casimir scale `q + 1`: each
occupied channel's weight numerator at its one-member site and the
content `6 (q + 1) + p` at the Casimir's second member. -/
private def chans (q : Nat) : List (Nat × Nat) → List (Pos × Pos)
  | [] => []
  | (0, _) :: cs => chans q cs
  | (m + 1, p) :: cs =>
    (ground.posOfSucc m, ground.posOfSucc (6 * q + 5 + p)) :: chans q cs

/-- The adjoint square's channel list at its cleared data, vacant
at a vacant Casimir scale. -/
def chanList {L : Type} (F : fusion.Data L) : List (Pos × Pos) :=
  match F.c2D with
  | 0 => []
  | q + 1 => chans q (fusion.adjChannels F)

/-- A read at the interface's occupied data, the Casimir scale
`q + 1` and the adjoint dimension `t + 1`, the stated datum at a
vacant one. -/
private def atScale {L : Type} {α : Type} (F : fusion.Data L) (d : α)
    (k : Nat → Nat → α) : α :=
  match F.c2D, F.dim F.theta with
  | 0, _ => d
  | _ + 1, 0 => d
  | q + 1, t + 1 => k q t

/-- The pair fold `S = Σ_k w_k [1 : 6 + ĉ₂(k)]` over the adjoint
square's channels at the module–pair weights `[m_k d_k : d_θ²]`:
the channel reads' fold at the Casimir scale over the adjoint
dimension's square, the unit at vacant interface data. -/
def pairFold {L : Type} (F : fusion.Data L) : BPair × Pos :=
  atScale F (BPair.unit, Pos.one) (fun q t =>
    ((sumQ (chans q (fusion.adjChannels F))).1.scale
        (ground.posOfSucc q),
      (sumQ (chans q (fusion.adjChannels F))).2
        * (ground.posOfSucc t * ground.posOfSucc t)))

/-- The pair sum's public face: the channel list's pair terms
`w_k w_l ⟨ĉ₂(k) : ĉ₂(l)⟩² [1 : (6 + ĉ₂(k)) (6 + ĉ₂(l))]` at the cleared
data, each pair once, over the weights' clearing `d_θ⁴`. -/
def pairRead {L : Type} (F : fusion.Data L) : BPair × Pos :=
  pairSum (chanList F)

/-- The weight fold over the channels reads the interface's
completeness fold. -/
private theorem tSum_read {L : Type} (F : fusion.Data L) (q : Nat) :
    ∀ (ks : List L) (acc : Nat),
      (BPair.ofNat (ks.foldl (fun acc c =>
          acc + F.count F.theta F.theta c * F.dim c) acc)).oneValue
        (BPair.ofNat acc + tSum (chans q (fusion.adjRow F ks)))
  | [], acc => BPair.oneValue_symm (BPair.add_unit _)
  | k :: ks, acc => by
    show (BPair.ofNat (ks.foldl (fun acc c =>
        acc + F.count F.theta F.theta c * F.dim c)
        (acc + F.count F.theta F.theta k * F.dim k))).oneValue
      (BPair.ofNat acc + tSum (chans q (fusion.adjRow F (k :: ks))))
    refine BPair.oneValue_trans (tSum_read F q ks _) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.ofNat_add acc _)
      (BPair.oneValue_refl _)) ?_
    rw [BPair.add_assoc]
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    show (BPair.ofNat (F.count F.theta F.theta k * F.dim k)
        + tSum (chans q (fusion.adjRow F ks))).oneValue
      (tSum (chans q (match F.count F.theta F.theta k * F.dim k with
        | 0 => fusion.adjRow F ks
        | m + 1 => (m + 1, F.c2N k) :: fusion.adjRow F ks)))
    match F.count F.theta F.theta k * F.dim k with
    | 0 => exact BPair.unit_add _
    | m + 1 => exact BPair.oneValue_refl _

/-- The drift fold over a label list at the balance carrier: each
channel's weight numerator against its Casimir numerator. -/
private def dSum {L : Type} (F : fusion.Data L) : List L → BPair
  | [] => BPair.unit
  | k :: ks =>
    BPair.ofNat (F.count F.theta F.theta k * F.dim k)
      * BPair.ofNat (F.c2N k) + dSum F ks

/-- The drift fold reads the interface's drift fold. -/
private theorem dSum_read {L : Type} (F : fusion.Data L) :
    ∀ (ks : List L) (acc : Nat),
      (BPair.ofNat (ks.foldl (fun acc c =>
          acc + F.count F.theta F.theta c * F.dim c * F.c2N c) acc)).oneValue
        (BPair.ofNat acc + dSum F ks)
  | [], acc => BPair.oneValue_symm (BPair.add_unit _)
  | k :: ks, acc => by
    show (BPair.ofNat (ks.foldl (fun acc c =>
        acc + F.count F.theta F.theta c * F.dim c * F.c2N c)
        (acc + F.count F.theta F.theta k * F.dim k * F.c2N k))).oneValue
      (BPair.ofNat acc + (BPair.ofNat (F.count F.theta F.theta k * F.dim k)
        * BPair.ofNat (F.c2N k) + dSum F ks))
    refine BPair.oneValue_trans (dSum_read F ks _) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.ofNat_add acc _)
      (BPair.oneValue_refl _)) ?_
    rw [BPair.add_assoc]
    exact BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.ofNat_mul _ _) (BPair.oneValue_refl _))

/-- The content fold over the channels is six Casimir scales of the
weight fold joined to the drift fold. -/
private theorem aSum_read {L : Type} (F : fusion.Data L) (q : Nat) :
    ∀ ks : List L, (aSum (chans q (fusion.adjRow F ks))).oneValue
      (BPair.ofNat (6 * (q + 1)) * tSum (chans q (fusion.adjRow F ks)) + dSum F ks)
  | [] => by
    show BPair.unit.oneValue (BPair.ofNat (6 * (q + 1)) * BPair.unit + BPair.unit)
    exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.add_unit _)
      (BPair.mul_unit _))
  | k :: ks => by
    show (aSum (chans q (match F.count F.theta F.theta k * F.dim k with
        | 0 => fusion.adjRow F ks
        | m + 1 => (m + 1, F.c2N k) :: fusion.adjRow F ks))).oneValue
      (BPair.ofNat (6 * (q + 1)) * tSum (chans q
        (match F.count F.theta F.theta k * F.dim k with
        | 0 => fusion.adjRow F ks
        | m + 1 => (m + 1, F.c2N k) :: fusion.adjRow F ks))
        + (BPair.ofNat (F.count F.theta F.theta k * F.dim k)
          * BPair.ofNat (F.c2N k) + dSum F ks))
    match F.count F.theta F.theta k * F.dim k with
    | 0 =>
      refine BPair.oneValue_trans (aSum_read F q ks) ?_
      refine BPair.oneValue_symm ?_
      rw [BPair.add_comm (BPair.ofNat 0 * BPair.ofNat (F.c2N k)) (dSum F ks),
        ← BPair.add_assoc]
      refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.unit_mul _)) (BPair.add_unit _)
    | m + 1 =>
      show (BPair.ofPos (ground.posOfSucc m
          * ground.posOfSucc (6 * q + 5 + F.c2N k)) + aSum (chans q (fusion.adjRow F ks))).oneValue
        (BPair.ofNat (6 * (q + 1))
          * (BPair.ofPos (ground.posOfSucc m) + tSum (chans q (fusion.adjRow F ks)))
          + (BPair.ofNat (m + 1) * BPair.ofNat (F.c2N k) + dSum F ks))
      have hterm : (BPair.ofPos (ground.posOfSucc m
          * ground.posOfSucc (6 * q + 5 + F.c2N k))).oneValue
          (BPair.ofNat (6 * (q + 1)) * BPair.ofPos (ground.posOfSucc m)
            + BPair.ofNat (m + 1) * BPair.ofNat (F.c2N k)) := by
        have hnat : 6 * q + 5 + F.c2N k + 1 = 6 * (q + 1) + F.c2N k :=
          Nat.add_right_comm (6 * q + 5) (F.c2N k) 1
        refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofPos_mul _ _)) ?_
        show (BPair.ofPos (ground.posOfSucc m)
          * BPair.ofNat (6 * q + 5 + F.c2N k + 1)).oneValue _
        rw [hnat]
        refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.ofNat_add (6 * (q + 1)) (F.c2N k))) ?_
        rw [BPair.left_distrib, BPair.mul_comm (BPair.ofPos (ground.posOfSucc m))
          (BPair.ofNat (6 * (q + 1)))]
        exact BPair.oneValue_refl _
      refine BPair.oneValue_trans (BPair.add_congr hterm (aSum_read F q ks)) ?_
      rw [BPair.left_distrib, BPair.add_assoc, BPair.add_assoc]
      refine BPair.add_congr (BPair.oneValue_refl _) ?_
      rw [← BPair.add_assoc, BPair.add_comm (BPair.ofNat (m + 1) * BPair.ofNat (F.c2N k))
        (BPair.ofNat (6 * (q + 1)) * tSum (chans q (fusion.adjRow F ks))), BPair.add_assoc]
      exact BPair.oneValue_refl _

/-- A pair's term reads at either order. -/
private theorem term_comm (x y : Pos × Pos) : bpairQRead.rel (term x y) (term y x) := by
  refine qOneValue_of_eq ?_
  show (BPair.ofPos (x.1 * y.1) * (BPair.mk x.2 y.2 * BPair.mk x.2 y.2), x.2 * y.2)
    = (BPair.ofPos (y.1 * x.1) * (BPair.mk y.2 x.2 * BPair.mk y.2 x.2), y.2 * x.2)
  rw [ground.mul_comm x.1 y.1, ground.mul_comm x.2 y.2,
    show BPair.mk y.2 x.2 = (BPair.mk x.2 y.2).swap from rfl, BPair.swap_sq]

/-! The side at the interface: eight times the pair fold reads the
unit joined to the pair sum over the adjoint dimension's fourth
power, the collection at the two closure identities. -/

/-- A carried read at a further clearing. -/
private def qdiv (p : BPair × Pos) (w : Pos) : BPair × Pos := (p.1, p.2 * w)

/-- A carried read at a common scaling of its members. -/
private theorem qscaleD (p : BPair × Pos) (s : Pos) :
    bpairQRead.rel p (p.1.scale s, p.2 * s) := by
  show (p.1.scale (p.2 * s)).oneValue ((p.1.scale s).scale p.2)
  rw [BPair.scale_scale, ground.mul_comm s p.2]
  exact BPair.oneValue_refl _

private theorem qdiv_add (p q : BPair × Pos) (w : Pos) :
    bpairQRead.rel (qdiv (BPair.addQ p q) w) (BPair.addQ (qdiv p w) (qdiv q w)) := by
  refine qOneValue_trans (qscaleD _ w) (qOneValue_of_eq ?_)
  show ((p.1.scale q.2 + q.1.scale p.2).scale w, p.2 * q.2 * w * w)
    = (p.1.scale (q.2 * w) + q.1.scale (p.2 * w), p.2 * w * (q.2 * w))
  rw [BPair.scale_add, BPair.scale_scale, BPair.scale_scale, ground.mul_mul_mul_comm p.2 w q.2 w,
    ground.mul_assoc (p.2 * q.2) w w]

private theorem qdiv_congr {p p' : BPair × Pos} (w : Pos) (h : bpairQRead.rel p p') :
    bpairQRead.rel (qdiv p w) (qdiv p' w) := by
  show (p.1.scale (p'.2 * w)).oneValue (p'.1.scale (p.2 * w))
  rw [← BPair.scale_scale, ← BPair.scale_scale]
  exact BPair.scale_congr w h

/-- The weight fold over the adjoint square's channels is the
adjoint dimension's square, the completeness. -/
private theorem tSum_law {L : Type} (F : fusion.Data L) (q t : Nat)
    (ht : F.dim F.theta = t + 1) (hdim : fusion.dimLaw F F.theta F.theta) :
    (tSum (chans q (fusion.adjChannels F))).oneValue
      (BPair.ofPos (ground.posOfSucc t * ground.posOfSucc t)) := by
  have h := tSum_read F q (F.row F.theta F.theta) 0
  unfold fusion.dimLaw at hdim
  rw [hdim, ht] at h
  refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.unit_add _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm h) ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm
    (BPair.ofPos_mul (ground.posOfSucc t) (ground.posOfSucc t))) ?_
  exact BPair.oneValue_symm (BPair.ofNat_mul (t + 1) (t + 1))

/-- The drift fold over the adjoint square's row is the adjoint
dimension's square at twice the Casimir scale, the uniform drift at
the adjoint. -/
private theorem dSum_law {L : Type} (F : fusion.Data L) (q t : Nat)
    (hq : F.c2D = q + 1) (ht : F.dim F.theta = t + 1)
    (hθ : F.c2N F.theta = q + 1) (hdrift : fusion.driftLaw F F.theta) :
    (dSum F (F.row F.theta F.theta)).oneValue
      (BPair.ofNat ((t + 1) * (t + 1) * ((q + 1) + (q + 1)))) := by
  have h := dSum_read F (F.row F.theta F.theta) 0
  unfold fusion.driftLaw at hdrift
  rw [hdrift, ht, hθ, hq] at h
  refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.unit_add _)) ?_
  exact BPair.oneValue_symm h

/-- The content fold over the adjoint square's channels is eight
Casimir scales of the adjoint dimension's square. -/
private theorem aSum_law {L : Type} (F : fusion.Data L) (q t : Nat)
    (hq : F.c2D = q + 1) (ht : F.dim F.theta = t + 1)
    (hθ : F.c2N F.theta = q + 1) (hdim : fusion.dimLaw F F.theta F.theta)
    (hdrift : fusion.driftLaw F F.theta) :
    (aSum (chans q (fusion.adjChannels F))).oneValue
      (BPair.ofPos (8 * ground.posOfSucc q)
        * BPair.ofPos (ground.posOfSucc t * ground.posOfSucc t)) := by
  refine BPair.oneValue_trans (aSum_read F q _) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.mul_congr (BPair.ofNat_mul 6 (q + 1)) (tSum_law F q t ht hdim))
    (dSum_law F q t hq ht hθ hdrift)) ?_
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans (BPair.ofNat_mul _ _)
      (BPair.mul_congr (BPair.oneValue_trans
        (BPair.ofNat_mul (t + 1) (t + 1))
        (BPair.ofPos_mul (ground.posOfSucc t) (ground.posOfSucc t)))
        (BPair.ofNat_add (q + 1) (q + 1))))) ?_
  rw [BPair.mul_comm (BPair.ofPos (ground.posOfSucc t * ground.posOfSucc t))
    (BPair.ofNat (q + 1) + BPair.ofNat (q + 1)), ← BPair.right_distrib]
  refine BPair.mul_congr ?_ (BPair.oneValue_refl _)
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans (BPair.oneValue_of_eq
      (BPair.scale_two (BPair.ofNat (q + 1))).symm)
      (BPair.oneValue_symm (BPair.ofPos_scale 2 _)))) ?_
  rw [← BPair.right_distrib]
  refine BPair.oneValue_trans (BPair.mul_congr ?_ (BPair.oneValue_refl _))
    (BPair.ofPos_mul 8 (ground.posOfSucc q))
  show (BPair.ofPos 6 + BPair.ofPos 2).oneValue (BPair.ofPos 8)
  decide +kernel

/-- The pair fold at an occupied Casimir scale and adjoint
dimension, the channels' fold scaled at the Casimir scale over the
adjoint dimension's square. -/
private theorem pairFold_at {L : Type} (F : fusion.Data L) (q t : Nat)
    (hq : F.c2D = q + 1) (ht : F.dim F.theta = t + 1) :
    pairFold F = ((sumQ (chans q (fusion.adjChannels F))).1.scale
        (ground.posOfSucc q),
      (sumQ (chans q (fusion.adjChannels F))).2
        * (ground.posOfSucc t * ground.posOfSucc t)) := by
  unfold pairFold atScale
  rw [hq, ht]

private theorem chanList_at {L : Type} (F : fusion.Data L) (q : Nat)
    (hq : F.c2D = q + 1) :
    chanList F = chans q (fusion.adjChannels F) := by
  unfold chanList
  rw [hq]

/-- Eight times the scaled fold is the content fold's read against
the fold over the adjoint dimension's fourth power. -/
private theorem eight_read (S1 : BPair) (S2 Q D2 : Pos) :
    bpairQRead.rel (qscale (BPair.ofPos 8) (S1.scale Q, S2 * D2))
      (qdiv (qscale (BPair.ofPos (8 * Q) * BPair.ofPos D2) (S1, S2))
        (D2 * D2)) := by
  show ((BPair.ofPos 8 * S1.scale Q).scale (S2 * (D2 * D2))).oneValue
    ((BPair.ofPos (8 * Q) * BPair.ofPos D2 * S1).scale (S2 * D2))
  rw [BPair.mul_scale, BPair.scale_scale, BPair.mul_right_comm]
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.scale_congr _ (BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.mul_comm _ _))
    (BPair.ofPos_scale D2 (BPair.ofPos (8 * Q) * S1)))) ?_
  rw [BPair.scale_scale]
  refine BPair.oneValue_trans (BPair.scale_congr _ (BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_symm (BPair.ofPos_mul 8 Q))
      (BPair.oneValue_refl S1))
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))
      (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.ofPos_scale Q S1))
        (BPair.oneValue_of_eq (BPair.mul_scale _ _ _)))))) ?_
  rw [BPair.scale_scale, ground.mul_left_comm D2 S2 D2]
  exact BPair.oneValue_refl _

/-- The weight fold's square over the fourth power is the unit. -/
private theorem unit_read (T : BPair) (D2 : Pos) (hT : T.oneValue (BPair.ofPos D2)) :
    bpairQRead.rel (qdiv (T * T, Pos.one) (D2 * D2)) (BPair.ofPos Pos.one, Pos.one) := by
  show ((T * T).scale Pos.one).oneValue
    ((BPair.ofPos Pos.one).scale (Pos.one * (D2 * D2)))
  rw [BPair.scale_one, ground.one_mul]
  refine BPair.oneValue_trans (BPair.mul_congr hT hT) ?_
  refine BPair.oneValue_trans (BPair.ofPos_mul D2 D2) ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.scale_ofPos Pos.one (D2 * D2)) ?_
  rw [ground.one_mul]
  exact BPair.oneValue_refl _

/-- The side, the carried read: eight times the pair fold is the
unit joined to the pair sum over the adjoint dimension's fourth
power. -/
private theorem side_core {L : Type} (F : fusion.Data L) (q t : Nat)
    (hq : F.c2D = q + 1) (ht : F.dim F.theta = t + 1)
    (hθ : F.c2N F.theta = q + 1) (hdim : fusion.dimLaw F F.theta F.theta)
    (hdrift : fusion.driftLaw F F.theta) :
    bpairQRead.rel (qscale (BPair.ofPos 8) (pairFold F))
      (BPair.addQ (BPair.ofPos Pos.one, Pos.one)
        (qdiv (pairRead F) (ground.posOfSucc t * ground.posOfSucc t
          * (ground.posOfSucc t * ground.posOfSucc t)))) := by
  rw [pairFold_at F q t hq ht]
  unfold pairRead
  rw [chanList_at F q hq]
  refine qOneValue_trans (eight_read _ _ _ _) ?_
  refine qOneValue_trans (qdiv_congr _ (qOneValue_trans (qscale_congr
    (BPair.oneValue_symm (aSum_law F q t hq ht hθ hdim hdrift)) (qOneValue_refl _))
    (collect _))) ?_
  refine qOneValue_trans (qdiv_add _ _ _) ?_
  exact BPair.addQ_congr (unit_read _ _ (tSum_law F q t ht hdim)) (qOneValue_refl _)

/-- The side: eight times the pair fold is the unit joined to the
pair sum over the adjoint dimension's fourth power, the collection
at the completeness and the drift. -/
theorem side {L : Type} (F : fusion.Data L) (q t : Nat)
    (hq : F.c2D = q + 1) (ht : F.dim F.theta = t + 1)
    (hθ : F.c2N F.theta = q + 1) (hdim : fusion.dimLaw F F.theta F.theta)
    (hdrift : fusion.driftLaw F F.theta) :
    ((BPair.ofPos 8 * (pairFold F).1).scale
        ((pairRead F).2 * (ground.posOfSucc t * ground.posOfSucc t
          * (ground.posOfSucc t * ground.posOfSucc t)))).oneValue
      (((BPair.ofPos Pos.one).scale
          ((pairRead F).2 * (ground.posOfSucc t * ground.posOfSucc t
            * (ground.posOfSucc t * ground.posOfSucc t)))
        + (pairRead F).1).scale (pairFold F).2) := by
  have h : ((BPair.ofPos 8 * (pairFold F).1).scale
      (Pos.one * ((pairRead F).2 * (ground.posOfSucc t * ground.posOfSucc t
        * (ground.posOfSucc t * ground.posOfSucc t))))).oneValue
    (((BPair.ofPos Pos.one).scale
        ((pairRead F).2 * (ground.posOfSucc t * ground.posOfSucc t
          * (ground.posOfSucc t * ground.posOfSucc t)))
      + (pairRead F).1.scale Pos.one).scale (pairFold F).2) :=
    side_core F q t hq ht hθ hdim hdrift
  rw [ground.one_mul, BPair.scale_one] at h
  exact h

/-! The margin: the unit channel's term against the `θ` channel's is
`[c₁ : 42 d_θ³]` over the fourth power's clearing, every other
term a square, so eight times the pair fold exceeds the unit by
that margin or beyond. -/

private theorem qle_add_mono (p : BPair × Pos) {a b : BPair × Pos}
    (h : qle a b) : qle (BPair.addQ p a) (BPair.addQ p b) := by
  show ((p.1.scale a.2 + a.1.scale p.2).scale (p.2 * b.2))
    ≤ ((p.1.scale b.2 + b.1.scale p.2).scale (p.2 * a.2))
  rw [BPair.scale_add, BPair.scale_add, BPair.scale_scale, BPair.scale_scale,
    BPair.scale_scale, BPair.scale_scale]
  refine leB_add (leB_congr_right (BPair.oneValue_of_eq
    (congrArg p.1.scale ?_)) (leB_refl _)) ?_
  · rw [ground.mul_left_comm a.2 p.2 b.2, ground.mul_left_comm b.2 p.2 a.2,
      ground.mul_comm a.2 b.2]
  · have e1 : a.1.scale (p.2 * (p.2 * b.2)) = (a.1.scale b.2).scale (p.2 * p.2) := by
      rw [BPair.scale_scale, ground.mul_comm p.2 b.2,
        ground.mul_left_comm p.2 b.2 p.2]
    have e2 : b.1.scale (p.2 * (p.2 * a.2)) = (b.1.scale a.2).scale (p.2 * p.2) := by
      rw [BPair.scale_scale, ground.mul_comm p.2 a.2,
        ground.mul_left_comm p.2 a.2 p.2]
    rw [e1, e2]
    exact leB_scale h (p.2 * p.2)

private theorem qdiv_mono {a b : BPair × Pos} (w : Pos) (h : qle a b) :
    qle (qdiv a w) (qdiv b w) := by
  show a.1.scale (b.2 * w) ≤ b.1.scale (a.2 * w)
  rw [← BPair.scale_scale, ← BPair.scale_scale]
  exact leB_scale h w

private theorem qle_congr_left {p p' q : BPair × Pos} (hp : bpairQRead.rel p p')
    (h : qle p q) : qle p' q := by
  show p'.1.scale q.2 ≤ q.1.scale p'.2
  refine leB_of_scale (w := p.2) ?_
  rw [BPair.scale_comm p'.1 q.2 p.2, BPair.scale_comm q.1 p'.2 p.2]
  refine leB_congr_left (BPair.scale_congr q.2 hp) ?_
  rw [BPair.scale_comm p.1 p'.2 q.2]
  exact leB_scale h p'.2

/-- The unit channel's content at the Casimir scale, six scales. -/
private theorem sixQ_read (q : Nat) :
    ground.posOfSucc (6 * q + 5) = 6 * ground.posOfSucc q := by
  show ground.posOfSucc (6 * q + 5) = ground.posOfSucc (5 * q + 5 + q)
  refine congrArg ground.posOfSucc ?_
  show Nat.succ 5 * q + 5 = 5 * q + 5 + q
  rw [Nat.succ_mul 5 q, Nat.add_right_comm]

/-- The `θ` channel's content at the Casimir scale, seven scales. -/
private theorem sevenQ_read (q : Nat) :
    ground.posOfSucc (6 * q + 5 + (q + 1)) = 7 * ground.posOfSucc q := by
  show ground.posOfSucc (6 * q + 5 + q + 1) = ground.posOfSucc (6 * q + 6 + q)
  refine congrArg ground.posOfSucc ?_
  rw [Nat.add_right_comm (6 * q + 5) q 1]

/-- The unit channel's term against the `θ` channel's, over the
fourth power: `[c₁ : 42 d_θ³]` at the `θ` channel's weight numerator
`c₁ d_θ`. -/
private theorem term_val (q t c c1 : Nat)
    (hE : (BPair.ofNat c1 * BPair.ofPos (ground.posOfSucc t)).oneValue
      (BPair.ofPos (ground.posOfSucc c))) :
    bpairQRead.rel (qdiv (term (Pos.one, ground.posOfSucc (6 * q + 5))
        (ground.posOfSucc c, ground.posOfSucc (6 * q + 5 + (q + 1))))
        (ground.posOfSucc t * ground.posOfSucc t
          * (ground.posOfSucc t * ground.posOfSucc t)))
      (BPair.ofNat c1, 42 * (ground.posOfSucc t * ground.posOfSucc t
        * ground.posOfSucc t)) := by
  have hG : (BPair.mk (ground.posOfSucc (6 * q + 5))
      (ground.posOfSucc (6 * q + 5 + (q + 1)))
      * BPair.mk (ground.posOfSucc (6 * q + 5))
        (ground.posOfSucc (6 * q + 5 + (q + 1)))).oneValue
      (BPair.ofPos (ground.posOfSucc q * ground.posOfSucc q)) := by
    have hg : (BPair.mk (ground.posOfSucc (6 * q + 5))
        (ground.posOfSucc (6 * q + 5 + (q + 1)))).oneValue
        (BPair.ofPos (ground.posOfSucc q)).swap := by
      show ground.posOfSucc (6 * q + 5) + (ground.posOfSucc q + Pos.one)
        = Pos.one + (ground.posOfSucc (6 * q + 5) + ground.posOfSucc q)
      rw [← ground.add_assoc]
      exact ground.add_comm _ _
    refine BPair.oneValue_trans (BPair.mul_congr hg hg) ?_
    rw [BPair.swap_sq]
    exact BPair.ofPos_mul _ _
  rw [sixQ_read, sevenQ_read] at hG
  show ((BPair.ofPos (Pos.one * ground.posOfSucc c)
      * (BPair.mk (ground.posOfSucc (6 * q + 5))
          (ground.posOfSucc (6 * q + 5 + (q + 1)))
        * BPair.mk (ground.posOfSucc (6 * q + 5))
          (ground.posOfSucc (6 * q + 5 + (q + 1))))).scale
      (42 * (ground.posOfSucc t * ground.posOfSucc t
        * ground.posOfSucc t))).oneValue
    ((BPair.ofNat c1).scale
      (ground.posOfSucc (6 * q + 5) * ground.posOfSucc (6 * q + 5 + (q + 1))
        * (ground.posOfSucc t * ground.posOfSucc t
          * (ground.posOfSucc t * ground.posOfSucc t))))
  rw [ground.one_mul, sixQ_read, sevenQ_read,
    ground.mul_mul_mul_comm 6 (ground.posOfSucc q) 7 (ground.posOfSucc q),
    show (6 : Pos) * 7 = 42 from by decide +kernel]
  refine BPair.oneValue_trans (BPair.scale_congr _
    (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) hG)
      (BPair.ofPos_mul _ _))) ?_
  refine BPair.oneValue_trans (BPair.scale_ofPos _ _) ?_
  refine BPair.oneValue_symm ?_
  have hD4 : ground.posOfSucc t * ground.posOfSucc t
      * (ground.posOfSucc t * ground.posOfSucc t)
      = ground.posOfSucc t * ground.posOfSucc t * ground.posOfSucc t
        * ground.posOfSucc t := by
    rw [ground.mul_assoc (ground.posOfSucc t * ground.posOfSucc t)]
  rw [hD4, ← ground.mul_assoc (42 * (ground.posOfSucc q * ground.posOfSucc q))
    (ground.posOfSucc t * ground.posOfSucc t * ground.posOfSucc t)
    (ground.posOfSucc t),
    ground.mul_comm (42 * (ground.posOfSucc q * ground.posOfSucc q)
      * (ground.posOfSucc t * ground.posOfSucc t * ground.posOfSucc t))
      (ground.posOfSucc t),
    ← BPair.scale_scale]
  refine BPair.oneValue_trans (BPair.scale_congr _ (BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofPos_scale (ground.posOfSucc t) (BPair.ofNat c1)))
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _)) hE))) ?_
  refine BPair.oneValue_trans (BPair.scale_ofPos _ _) ?_
  refine BPair.oneValue_of_eq (congrArg BPair.ofPos ?_)
  rw [ground.mul_assoc (ground.posOfSucc c) (ground.posOfSucc q * ground.posOfSucc q),
    ground.mul_left_comm (ground.posOfSucc q * ground.posOfSucc q) 42,
    ← ground.mul_assoc 42,
    ground.mul_assoc (42 * ground.posOfSucc q) (ground.posOfSucc q),
    ground.mul_assoc 42 (ground.posOfSucc q),
    ground.mul_assoc (ground.posOfSucc q) (ground.posOfSucc q)]

/-- The margin: eight times the pair fold exceeds the unit by
`[c₁ : 42 d_θ³]` or beyond, at the unit channel's term against the
`θ` channel's — the unit channel at the kernel point and weight one,
the `θ` channel at the Casimir scale and weight `c₁ d_θ` — every
other term a square. -/
theorem margin {L : Type} (F : fusion.Data L) (q t c : Nat)
    (hq : F.c2D = q + 1) (ht : F.dim F.theta = t + 1)
    (hθ : F.c2N F.theta = q + 1) (hdim : fusion.dimLaw F F.theta F.theta)
    (hdrift : fusion.driftLaw F F.theta)
    (i j : Nat)
    (hui : ground.getAt (Pos.one, Pos.one) (chanList F) i
      = (Pos.one, ground.posOfSucc (6 * q + 5)))
    (huj : ground.getAt (Pos.one, Pos.one) (chanList F) j
      = (ground.posOfSucc c, ground.posOfSucc (6 * q + 5 + (q + 1))))
    (hc : F.c1 * F.dim F.theta = c + 1) :
    ((BPair.ofPos Pos.one).scale
        (42 * (ground.posOfSucc t * ground.posOfSucc t * ground.posOfSucc t))
      + BPair.ofNat F.c1).scale (pairFold F).2
      ≤ (BPair.ofPos 8 * (pairFold F).1).scale
        (42 * (ground.posOfSucc t * ground.posOfSucc t
          * ground.posOfSucc t)) := by
  have hE : (BPair.ofNat F.c1 * BPair.ofPos (ground.posOfSucc t)).oneValue
      (BPair.ofPos (ground.posOfSucc c)) := by
    have h := BPair.ofNat_mul F.c1 (F.dim F.theta)
    rw [hc, ht] at h
    exact BPair.oneValue_symm h
  have hi : i < (chanList F).length := by
    refine (Nat.lt_or_ge i (chanList F).length).elim id (fun hge => ?_)
    rw [ground.getAt_over _ _ _ hge] at hui
    exact absurd (congrArg Prod.snd hui).symm
      (ground.succ_ne_one (ground.posOfSucc (6 * q + 4)))
  have hj : j < (chanList F).length := by
    refine (Nat.lt_or_ge j (chanList F).length).elim id (fun hge => ?_)
    rw [ground.getAt_over _ _ _ hge] at huj
    exact absurd (congrArg Prod.snd huj).symm
      (ground.succ_ne_one (ground.posOfSucc (6 * q + 5 + q)))
  have hij : i ≠ j := fun heq => by
    subst heq
    rw [hui] at huj
    have h1 : ground.posOfSucc (6 * q + 5)
        = ground.posOfSucc (6 * q + 5 + (q + 1)) := congrArg Prod.snd huj
    have h2 : 6 * q + 5 + 1 = 6 * q + 5 + (q + 1 + 1) := congrArg ground.posVal h1
    exact Nat.noConfusion (Nat.succ.inj (ground.addCancelL (6 * q + 5) h2))
  have hP : qle (term (Pos.one, ground.posOfSucc (6 * q + 5))
      (ground.posOfSucc c, ground.posOfSucc (6 * q + 5 + (q + 1))))
      (pairSum (chanList F)) := by
    refine (Nat.lt_or_ge i j).elim (fun hlt => ?_) (fun hge => ?_)
    · have h := pairSum_ge (chanList F) i j hlt hj
      rw [hui, huj] at h
      exact h
    · have h := pairSum_ge (chanList F) j i
        (Nat.lt_of_le_of_ne hge (Ne.symm hij)) hi
      rw [hui, huj] at h
      exact qle_congr_left (term_comm _ _) h
  have h2 : qle (BPair.addQ (BPair.ofPos Pos.one, Pos.one)
      (qdiv (term (Pos.one, ground.posOfSucc (6 * q + 5))
        (ground.posOfSucc c, ground.posOfSucc (6 * q + 5 + (q + 1))))
        (ground.posOfSucc t * ground.posOfSucc t
          * (ground.posOfSucc t * ground.posOfSucc t))))
      (qscale (BPair.ofPos 8) (pairFold F)) :=
    qle_congr_right (qOneValue_symm (side_core F q t hq ht hθ hdim hdrift))
      (qle_add_mono _ (qdiv_mono _ hP))
  have h3 := qle_congr_left (BPair.addQ_congr (qOneValue_refl _) (term_val q t c F.c1 hE)) h2
  have h4 : ((BPair.ofPos Pos.one).scale
      (42 * (ground.posOfSucc t * ground.posOfSucc t * ground.posOfSucc t))
    + (BPair.ofNat F.c1).scale Pos.one).scale (pairFold F).2
    ≤ (BPair.ofPos 8 * (pairFold F).1).scale
      (Pos.one * (42 * (ground.posOfSucc t * ground.posOfSucc t
        * ground.posOfSucc t))) := h3
  rw [BPair.scale_one, ground.one_mul] at h4
  exact h4

/-! The jet tier: the connected four-point partition fold at a
moment family over any carrier with the displayed sum, product and
partner, the graph's free moments and the powers' `k`-counts at the
interface, and the jet moments at the displayed orders — a
polynomial in `τ²` (the key `k` the power `τ^{2k}`) over the
composite pairs `[⟨u:v⟩:c]` at `def:poly`'s carrier
(`poly.polyO ground.bpairQOps`). -/

/-- The connected four-point partition fold `ϰ₄` at a moment family
`μ_ab`, each field twice: the displayed balance pair of the odd
partition counts against the even, the block-count weights the
displayed naturals. -/
def kappa4 {γ : Type} (ops : ground.DOps γ) (μ : Nat → Nat → γ) : γ :=
  ops.add
    (ops.add (ops.add (ops.add (μ 2 2)
        (poly.nsmulO ops (ops.mul (ops.mul (μ 1 0) (μ 1 0)) (μ 0 2)) 2))
        (poly.nsmulO ops (ops.mul (ops.mul (μ 0 1) (μ 0 1)) (μ 2 0)) 2))
      (poly.nsmulO ops (ops.mul (ops.mul (μ 1 0) (μ 0 1)) (μ 1 1)) 8))
    (ops.swap
      (ops.add (ops.add (ops.add (ops.add
          (poly.nsmulO ops (ops.mul (μ 1 0) (μ 1 2)) 2)
          (poly.nsmulO ops (ops.mul (μ 0 1) (μ 2 1)) 2))
          (ops.mul (μ 2 0) (μ 0 2)))
        (poly.nsmulO ops (ops.mul (μ 1 1) (μ 1 1)) 2))
        (poly.nsmulO ops (ops.mul (ops.mul (μ 1 0) (μ 1 0))
          (ops.mul (μ 0 1) (μ 0 1))) 6)))

/-- The graph's free moments, the per-plaquette reads
`m_a := Eval(χ_θ^a)`: the invariant count of the `a`-fold adjoint
list, the fusion rows' fold. -/
def moment {L : Type} (F : fusion.Data L) (a : Nat) : Nat :=
  carrier.invCount F (List.replicate a F.theta)

/-- The positive powers' coefficient families over the labels, the
adjoint's own at the first and each further power the row
expansion of the one before, every entry at its label and its
count. -/
private def powFam {L : Type} (F : fusion.Data L) : Nat → List (L × Nat)
  | 0 => [(F.theta, 1)]
  | a + 1 => (powFam F a).flatMap (fun e =>
      (F.row F.theta e.1).map (fun c => (c, e.2 * F.count F.theta e.1 c)))

/-- The `k`-count of the `a`-th power, `T_a(k)`: the unit read at
the vacant power, and at a positive power the family's fold at the
label. -/
def powCount {L : Type} (F : fusion.Data L) : Nat → L → Nat
  | 0, k => if F.eqL k F.unit then 1 else 0
  | a + 1, k => (powFam F a).foldl
      (fun s e => if F.eqL e.1 k then s + e.2 else s) 0

/-- The vacant power's `θ`-count is the first moment: `T₀(θ)` the
unit read and `m₁ = Eval(χ_θ)` are one Kronecker read at the
label pair `(θ, 𝟏)`. -/
private theorem powCount_zero_theta {L : Type} (F : fusion.Data L) :
    powCount F 0 F.theta = moment F 1 := rfl

/-- One nonunit channel's solve at the moments' indices:
`N^k_θθ [T_a(k) m_b + m_a T_b(k) : ĉ₂(k)]` at the Casimir's cleared
read `[x c2D : c2N(k)]`, the vacant Casimir's arm at the sum's
unit (`con:fusion`'s positivity at every nonunit label). -/
private def chanTerm {L : Type} (F : fusion.Data L) (a b : Nat) (k : L) :
    BPair × Pos :=
  match F.c2N k with
  | 0 => (BPair.unit, Pos.one)
  | p + 1 =>
    (BPair.ofNat (F.count F.theta F.theta k
      * ((powCount F a k * moment F b + moment F a * powCount F b k) * F.c2D)),
     ground.posOfSucc p)

/-- The single-plaquette channels' fold over a label list, the unit
label passing. -/
private def chanFold {L : Type} (F : fusion.Data L) (a b : Nat) :
    List L → BPair × Pos
  | [] => (BPair.unit, Pos.one)
  | k :: ks =>
    if F.eqL k F.unit then chanFold F a b ks
    else BPair.addQ (chanTerm F a b k) (chanFold F a b ks)

/-- The jet moments' fourth-order datum `D_ab`, the join's datum
over the balance pairs: the pair insertions' square reads at
`[1 : 16]`, the single-plaquette channels' solves at `[1 : 8]` over
the adjoint square's nonunit channels, and the pair networks'
`T_a(θ) T_b(θ) S`, against the partner of `[1 : 8] m_a m_b`. -/
def jetD {L : Type} (F : fusion.Data L) (a b : Nat) : BPair × Pos :=
  BPair.addQ
    (BPair.addQ
      (BPair.ofNat (moment F (a + 2) * moment F b
        + 2 * (moment F (a + 1) * moment F (b + 1))
        + moment F a * moment F (b + 2)), 16)
      (BPair.addQ (qdiv (chanFold F a b (F.row F.theta F.theta)) 8)
        (qscale (BPair.ofNat (powCount F a F.theta * powCount F b F.theta))
          (pairFold F))))
    ((BPair.ofNat (moment F a * moment F b)).swap, 8)

/-- The jet moments at the displayed orders,
`μ̂_ab = m_a m_b + τ² [1 : 2] (m_{a+1} m_b + m_a m_{b+1}) + τ⁴ D_ab`,
the polynomial in `τ²` over the composite pairs. -/
def jetMoment {L : Type} (F : fusion.Data L) (a b : Nat) :
    List (BPair × Pos) :=
  [(BPair.ofNat (moment F a * moment F b), Pos.one),
   (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2),
   jetD F a b]

/-! The jet at the theta graph: the ground's jet at the free end is
the second-order solve `ψ̂ = 1 + τ² ψ₁ + τ⁴ ψ₂` at
`ψ₁ = [1 : 4](q₁ + q₂)`, each module an eigenvector at the plaquette
content four (`prop:E0`), and `ψ₂` the solve at `M ψ₁`'s components
off the unit line — a single-plaquette channel `χ_k(p)` at the
content `4 ĉ₂(k)` and the pair's product at its channel split
`q₁ q₂ = Σ_k F_k` over the shared link's channels at the contents
`6 + ĉ₂(k)` and the weights `⟨F_k, F_k⟩ = w_k` (`thm:network`(i),(ii);
the contents the spread's reads at `thm:network`(i)), each
component's solve the content's cofactor.  The jet moments are the
normalized pairing `[⟨ψ̂, q₁^a q₂^b ψ̂⟩ : ⟨ψ̂, ψ̂⟩]` through `τ⁴`,
read component by component at the theta graph's evaluation: the
split at the shared link and the outer word reads
`Eval(f(U) g(V))` as the two unit coefficients' product
(`thm:network`(i); `prop:wg`), so a module's
pairing against a monomial is the powers' read `m_{c+1} m_d`, a
channel's the `k`-count `T_c(k) m_d`, and a pair sector's reads at
the `θ`-labeled free links alone, `T_c(θ) T_d(θ) w_k`, the gram's
configuration split (`def:carrier`).  The far insertions of a
window beyond the graph's band factorize (`lem:stableentries`) and
enter the pairing and the gram equally, a summand on both members
fixing the value (`def:ground`): the window's read is the pair's
at every far datum. -/

/-- `⟨ψ₁, q₁^c q₂^d⟩` at `ψ₁ = [1 : 4](q₁ + q₂)`: the split's read at
the powers, `[1 : 4](m_{c+1} m_d + m_c m_{d+1})`. -/
def oneRead {L : Type} (F : fusion.Data L) (c d : Nat) : BPair × Pos :=
  (BPair.ofNat (moment F (c + 1) * moment F d + moment F c * moment F (d + 1)), 4)

/-- The pair sectors' solves against `q₁^c q₂^d`: at each channel
`[1 : 2 (6 + ĉ₂(k))] T_c(θ) T_d(θ) w_k` over the channel list's cleared
data `(m_k d_k, 6 c2D + c2N(k))` at the Casimir scale `q + 1` and the
adjoint square `(t + 1)²`, the fold seeded at the sum's unit. -/
private def secFold (T q t : Nat) : List (Pos × Pos) → BPair × Pos
  | [] => (BPair.unit, Pos.one)
  | (u, a) :: cs =>
    BPair.addQ (BPair.ofNat T * BPair.ofPos (ground.posOfSucc q * u),
        (2 : Pos) * (a * (ground.posOfSucc t * ground.posOfSucc t)))
      (secFold T q t cs)

/-- The pair sectors' read against `q₁^c q₂^d` at the interface's
data, the unit at a vacant Casimir scale or adjoint dimension. -/
private def secRead {L : Type} (F : fusion.Data L) (c d : Nat) : BPair × Pos :=
  atScale F (BPair.unit, Pos.one) (fun q t =>
    secFold (powCount F c F.theta * powCount F d F.theta) q t (chanList F))

/-- `⟨ψ₂, q₁^c q₂^d⟩`: the single-plaquette channels' solves at
`[1 : 16]` over the adjoint square's nonunit channels and the pair
sectors' at their contents. -/
def twoRead {L : Type} (F : fusion.Data L) (c d : Nat) : BPair × Pos :=
  BPair.addQ (qdiv (chanFold F c d (F.row F.theta F.theta)) 16) (secRead F c d)

/-- The jet's pairing polynomial at the moment `(a, b)`,
`⟨ψ̂, q₁^a q₂^b ψ̂⟩` through `τ⁴`: the unit's read `m_a m_b`, the two
first-order reads, and at `τ⁴` the modules' reads against the moved
monomials with the second-order solve's twice; the gram is its
`(0, 0)` instance. -/
def jetPair {L : Type} (F : fusion.Data L) (a b : Nat) : List (BPair × Pos) :=
  [(BPair.ofNat (moment F a * moment F b), Pos.one),
   BPair.addQ (oneRead F a b) (oneRead F a b),
   BPair.addQ (qdiv (BPair.addQ (oneRead F (a + 1) b) (oneRead F a (b + 1))) 4)
     (BPair.addQ (twoRead F a b) (twoRead F a b))]

/-- A window's far datum at the pairing's three keys: the unit at
`τ⁰` and `τ²`, its multiple of the unit's read at `τ⁴`. -/
private def farTail {L : Type} (F : fusion.Data L) (a b : Nat) (f : BPair × Pos) :
    List (BPair × Pos) :=
  [bpairQOps.unit, bpairQOps.unit,
   bpairQOps.mul f (BPair.ofNat (moment F a * moment F b), Pos.one)]

/-- A window's pairing polynomial beyond the graph's band: the far
insertions' datum enters at `τ⁴` as its multiple of the unit's read,
the gram's at the `(0, 0)` instance. -/
def farPair {L : Type} (F : fusion.Data L) (a b : Nat) (f : BPair × Pos) :
    List (BPair × Pos) :=
  (poly.polyO ground.bpairQOps).add (jetPair F a b) (farTail F a b f)

/-! The composite carrier's polynomial reads at the low keys, each
a carried read at the entries' own: the key reads of the sum, the
product at the keys through two, the partner and the natural
weights. -/

private theorem qmul_congr {p p' q q' : BPair × Pos} (hp : bpairQRead.rel p p')
    (hq : bpairQRead.rel q q') : bpairQRead.rel (bpairQOps.mul p q) (bpairQOps.mul p' q') := by
  show ((p.1 * q.1).scale (p'.2 * q'.2)).oneValue ((p'.1 * q'.1).scale (p.2 * q.2))
  rw [BPair.scale_mul, BPair.scale_mul]
  exact BPair.mul_congr hp hq

private theorem qswap_congr {p q : BPair × Pos} (h : bpairQRead.rel p q) :
    bpairQRead.rel (bpairQOps.swap p) (bpairQOps.swap q) := by
  show (p.1.swap.scale q.2).oneValue (q.1.swap.scale p.2)
  rw [BPair.scale_swap, BPair.scale_swap]
  exact ground.swap_congr h

private theorem qmul_zero_left {p : BPair × Pos} (h : p.1.oneValue BPair.unit)
    (q : BPair × Pos) : bpairQRead.rel (bpairQOps.mul p q) bpairQOps.unit :=
  qOneValue_unit (BPair.oneValue_trans (BPair.mul_congr_left h) (BPair.unit_mul _))

private theorem qmul_zero_right (p : BPair × Pos) {q : BPair × Pos}
    (h : q.1.oneValue BPair.unit) : bpairQRead.rel (bpairQOps.mul p q) bpairQOps.unit :=
  qOneValue_unit (BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) h)
    (BPair.mul_unit _))

private theorem qmul_one_left (q : BPair × Pos) :
    bpairQRead.rel (bpairQOps.mul (BPair.ofNat 1, Pos.one) q) q := by
  show ((BPair.ofNat 1 * q.1).scale q.2).oneValue (q.1.scale (Pos.one * q.2))
  rw [ground.one_mul]
  exact BPair.scale_congr q.2 (BPair.ofNat_one_mul q.1)

private theorem qmul_one_right (p : BPair × Pos) :
    bpairQRead.rel (bpairQOps.mul p (BPair.ofNat 1, Pos.one)) p := by
  show ((p.1 * BPair.ofNat 1).scale p.2).oneValue (p.1.scale (p.2 * Pos.one))
  rw [ground.mul_one]
  exact BPair.scale_congr p.2 (BPair.mul_ofNat_one p.1)

private theorem qswap_add (p q : BPair × Pos) :
    bpairQOps.swap (BPair.addQ p q) = BPair.addQ (bpairQOps.swap p) (bpairQOps.swap q) := by
  show ((p.1.scale q.2 + q.1.scale p.2).swap, p.2 * q.2)
    = (p.1.swap.scale q.2 + q.1.swap.scale p.2, p.2 * q.2)
  rw [BPair.scale_swap, BPair.scale_swap, BPair.swap_add]

private theorem getAt_addQ (p q : List (BPair × Pos)) (k : Nat) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (poly.addLO ground.bpairQOps p q) k)
      (BPair.addQ (ground.getAt bpairQOps.unit p k) (ground.getAt bpairQOps.unit q k)) :=
  poly.getAt_addLO ground.bpairQOps ground.bpairQRead qOneValue_refl qOneValue_symm
    BPair.addQ_unitL BPair.addQ_unitR p q k

private theorem getAt_mapMul (c : BPair × Pos) (q : List (BPair × Pos)) (k : Nat) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (q.map (ground.bpairQOps.mul c)) k)
      (bpairQOps.mul c (ground.getAt bpairQOps.unit q k)) :=
  poly.getAt_mapMul ground.bpairQOps ground.bpairQRead qOneValue_refl qOneValue_symm
    (fun x => qmul_zero_right x (BPair.oneValue_refl _)) c q k

private theorem getAt0_mul : ∀ (p q : List (BPair × Pos)),
    bpairQRead.rel (ground.getAt bpairQOps.unit (poly.mulLO ground.bpairQOps p q) 0)
      (bpairQOps.mul (ground.getAt bpairQOps.unit p 0) (ground.getAt bpairQOps.unit q 0))
  | [], _ => qOneValue_symm (qmul_zero_left (BPair.oneValue_refl _) _)
  | c :: p, q => by
    show bpairQRead.rel (ground.getAt bpairQOps.unit (poly.addLO ground.bpairQOps
      (q.map (ground.bpairQOps.mul c))
      (bpairQOps.unit :: poly.mulLO ground.bpairQOps p q)) 0) _
    refine qOneValue_trans (getAt_addQ _ _ 0) ?_
    refine qOneValue_trans (BPair.addQ_congr (getAt_mapMul c q 0) (qOneValue_refl _)) ?_
    exact BPair.addQ_unitR _

private theorem getAt1_mul : ∀ (p q : List (BPair × Pos)),
    bpairQRead.rel (ground.getAt bpairQOps.unit (poly.mulLO ground.bpairQOps p q) 1)
      (BPair.addQ (bpairQOps.mul (ground.getAt bpairQOps.unit p 0) (ground.getAt bpairQOps.unit q 1))
        (bpairQOps.mul (ground.getAt bpairQOps.unit p 1) (ground.getAt bpairQOps.unit q 0)))
  | [], _ => qOneValue_symm (qOneValue_trans (BPair.addQ_congr
      (qmul_zero_left (BPair.oneValue_refl _) _)
      (qmul_zero_left (BPair.oneValue_refl _) _)) qadd_zero)
  | c :: p, q => by
    show bpairQRead.rel (ground.getAt bpairQOps.unit (poly.addLO ground.bpairQOps
      (q.map (ground.bpairQOps.mul c))
      (bpairQOps.unit :: poly.mulLO ground.bpairQOps p q)) 1) _
    refine qOneValue_trans (getAt_addQ _ _ 1) ?_
    exact BPair.addQ_congr (getAt_mapMul c q 1) (getAt0_mul p q)

private theorem getAt2_mul : ∀ (p q : List (BPair × Pos)),
    bpairQRead.rel (ground.getAt bpairQOps.unit (poly.mulLO ground.bpairQOps p q) 2)
      (BPair.addQ (bpairQOps.mul (ground.getAt bpairQOps.unit p 0) (ground.getAt bpairQOps.unit q 2))
        (BPair.addQ (bpairQOps.mul (ground.getAt bpairQOps.unit p 1) (ground.getAt bpairQOps.unit q 1))
          (bpairQOps.mul (ground.getAt bpairQOps.unit p 2) (ground.getAt bpairQOps.unit q 0))))
  | [], _ => qOneValue_symm (qOneValue_trans (BPair.addQ_congr
      (qmul_zero_left (BPair.oneValue_refl _) _)
      (qOneValue_trans (BPair.addQ_congr (qmul_zero_left (BPair.oneValue_refl _) _)
        (qmul_zero_left (BPair.oneValue_refl _) _)) qadd_zero)) qadd_zero)
  | c :: p, q => by
    show bpairQRead.rel (ground.getAt bpairQOps.unit (poly.addLO ground.bpairQOps
      (q.map (ground.bpairQOps.mul c))
      (bpairQOps.unit :: poly.mulLO ground.bpairQOps p q)) 2) _
    refine qOneValue_trans (getAt_addQ _ _ 2) ?_
    exact BPair.addQ_congr (getAt_mapMul c q 2) (getAt1_mul p q)

private theorem getAt_swapP : ∀ (p : List (BPair × Pos)) (k : Nat),
    ground.getAt bpairQOps.unit (p.map ground.bpairQOps.swap) k
      = bpairQOps.swap (ground.getAt bpairQOps.unit p k)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: p, k + 1 => getAt_swapP p k

private theorem getAt_nsmul : ∀ (n : Nat) (p : List (BPair × Pos)) (k : Nat),
    bpairQRead.rel (ground.getAt bpairQOps.unit (poly.nsmulO (poly.polyO ground.bpairQOps) p n) k)
      (poly.nsmulO ground.bpairQOps (ground.getAt bpairQOps.unit p k) n)
  | 0, _, _ => qOneValue_refl _
  | n + 1, p, k => by
    show bpairQRead.rel (ground.getAt bpairQOps.unit (poly.addLO ground.bpairQOps p
      (poly.nsmulO (poly.polyO ground.bpairQOps) p n)) k) _
    refine qOneValue_trans (getAt_addQ _ _ k) ?_
    exact BPair.addQ_congr (qOneValue_refl _) (getAt_nsmul n p k)

/-- Two carried reads at one clearing join at their first data. -/
private theorem qadd_same (u v : BPair) (d : Pos) :
    bpairQRead.rel (BPair.addQ (u, d) (v, d)) (u + v, d) := by
  show ((u.scale d + v.scale d).scale d).oneValue ((u + v).scale (d * d))
  rw [← BPair.scale_add, BPair.scale_scale]
  exact BPair.oneValue_refl _

/-- The channel term at a vacant Casimir reads the unit. -/
private theorem chanTerm_zero {L : Type} (F : fusion.Data L) (a b : Nat) {k : L}
    (h : F.c2N k = 0) : chanTerm F a b k = bpairQOps.unit := by
  unfold chanTerm
  rw [h]
  exact rfl

/-- The channel term at an occupied Casimir, its displayed read. -/
private theorem chanTerm_succ {L : Type} (F : fusion.Data L) (a b : Nat) {k : L}
    {p : Nat} (h : F.c2N k = p + 1) :
    chanTerm F a b k = (BPair.ofNat (F.count F.theta F.theta k
      * ((powCount F a k * moment F b + moment F a * powCount F b k) * F.c2D)),
     ground.posOfSucc p) := by
  unfold chanTerm
  rw [h]

/-- The channel fold at the pair indices splits termwise into the
two mixed folds: at every occupied channel the `(2,2)` term reads
the `(2,0)` and `(0,2)` terms' join, the vacant power's count at
the unit read off the unit label. -/
private theorem chanFold_split {L : Type} (F : fusion.Data L)
    (hm2 : moment F 2 = 1) :
    ∀ ks : List L, bpairQRead.rel (chanFold F 2 2 ks)
      (BPair.addQ (chanFold F 2 0 ks) (chanFold F 0 2 ks))
  | [] => qOneValue_symm qadd_zero
  | k :: ks => by
    have ih := chanFold_split F hm2 ks
    cases hk : F.eqL k F.unit with
    | true =>
      show bpairQRead.rel (if F.eqL k F.unit then chanFold F 2 2 ks
          else BPair.addQ (chanTerm F 2 2 k) (chanFold F 2 2 ks))
        (BPair.addQ
          (if F.eqL k F.unit then chanFold F 2 0 ks
            else BPair.addQ (chanTerm F 2 0 k) (chanFold F 2 0 ks))
          (if F.eqL k F.unit then chanFold F 0 2 ks
            else BPair.addQ (chanTerm F 0 2 k) (chanFold F 0 2 ks)))
      rw [hk]
      exact ih
    | false =>
      show bpairQRead.rel (if F.eqL k F.unit then chanFold F 2 2 ks
          else BPair.addQ (chanTerm F 2 2 k) (chanFold F 2 2 ks))
        (BPair.addQ
          (if F.eqL k F.unit then chanFold F 2 0 ks
            else BPair.addQ (chanTerm F 2 0 k) (chanFold F 2 0 ks))
          (if F.eqL k F.unit then chanFold F 0 2 ks
            else BPair.addQ (chanTerm F 0 2 k) (chanFold F 0 2 ks)))
      rw [hk]
      show bpairQRead.rel (BPair.addQ (chanTerm F 2 2 k) (chanFold F 2 2 ks))
        (BPair.addQ (BPair.addQ (chanTerm F 2 0 k) (chanFold F 2 0 ks))
          (BPair.addQ (chanTerm F 0 2 k) (chanFold F 0 2 ks)))
      refine qOneValue_trans (BPair.addQ_congr ?_ ih) (BPair.addQ_add_comm _ _ _ _)
      have hT0 : powCount F 0 k = 0 := by
        show (if F.eqL k F.unit then 1 else 0) = 0
        rw [hk]
        exact rfl
      have hm0 : moment F 0 = 1 := rfl
      cases hc : F.c2N k with
      | zero =>
        rw [chanTerm_zero F 2 2 hc, chanTerm_zero F 2 0 hc, chanTerm_zero F 0 2 hc]
        exact qOneValue_symm qadd_zero
      | succ p =>
        rw [chanTerm_succ F 2 2 hc, chanTerm_succ F 2 0 hc, chanTerm_succ F 0 2 hc,
          hT0, hm0, hm2, Nat.mul_one, Nat.one_mul, Nat.mul_zero, Nat.add_zero,
          Nat.zero_add]
        refine qOneValue_trans ?_ (qOneValue_symm (qadd_same _ _ _))
        refine qeq_num _ ?_
        refine BPair.oneValue_trans (BPair.oneValue_of_eq
          (congrArg BPair.ofNat ?_)) (BPair.ofNat_add _ _)
        rw [Nat.mul_comm (powCount F 2 k + powCount F 2 k) F.c2D,
          Nat.left_distrib, Nat.left_distrib, Nat.mul_comm F.c2D]

/-- The fourth-order datum at the pair, read at the stated
moments. -/
private theorem jetD22_read {L : Type} (F : fusion.Data L)
    (hm2 : moment F 2 = 1) (hm3 : moment F 3 = F.c1)
    (hT2 : powCount F 2 F.theta = F.c1) :
    jetD F 2 2 = BPair.addQ
      (BPair.addQ (BPair.ofNat (moment F 4 + 2 * (F.c1 * F.c1) + moment F 4), 16)
        (BPair.addQ (qdiv (chanFold F 2 2 (F.row F.theta F.theta)) 8)
          (qscale (BPair.ofNat (F.c1 * F.c1)) (pairFold F))))
      ((BPair.ofNat 1).swap, 8) := by
  unfold jetD
  rw [hm2, hm3, hT2, Nat.mul_one, Nat.one_mul]

/-- The fourth-order datum at the pair against the unit power. -/
private theorem jetD20_read {L : Type} (F : fusion.Data L)
    (hm1 : moment F 1 = 0) (hm2 : moment F 2 = 1) (hm3 : moment F 3 = F.c1)
    (hT2 : powCount F 2 F.theta = F.c1) :
    jetD F 2 0 = BPair.addQ
      (BPair.addQ (BPair.ofNat (moment F 4 + 1), 16)
        (BPair.addQ (qdiv (chanFold F 2 0 (F.row F.theta F.theta)) 8)
          (qscale (BPair.ofNat 0) (pairFold F))))
      ((BPair.ofNat 1).swap, 8) := by
  have hT0 : powCount F 0 F.theta = 0 := by
    rw [powCount_zero_theta]
    exact hm1
  have hm0 : moment F 0 = 1 := rfl
  unfold jetD
  rw [hm0, hm1, hm2, hm3, hT2, hT0, Nat.mul_one, Nat.one_mul, Nat.mul_zero,
    Nat.add_zero]

/-- The fourth-order datum at the unit power against the pair. -/
private theorem jetD02_read {L : Type} (F : fusion.Data L)
    (hm1 : moment F 1 = 0) (hm2 : moment F 2 = 1) (hm3 : moment F 3 = F.c1)
    (hT2 : powCount F 2 F.theta = F.c1) :
    jetD F 0 2 = BPair.addQ
      (BPair.addQ (BPair.ofNat (1 + moment F 4), 16)
        (BPair.addQ (qdiv (chanFold F 0 2 (F.row F.theta F.theta)) 8)
          (qscale (BPair.ofNat 0) (pairFold F))))
      ((BPair.ofNat 1).swap, 8) := by
  have hT0 : powCount F 0 F.theta = 0 := by
    rw [powCount_zero_theta]
    exact hm1
  have hm0 : moment F 0 = 1 := rfl
  unfold jetD
  rw [hm0, hm1, hm2, hm3, hT2, hT0, Nat.mul_one, Nat.one_mul, Nat.zero_mul,
    Nat.mul_zero, Nat.add_zero]

/-- A four-term join flattens to the right. -/
private theorem flat4 (X Y Z W : BPair × Pos) :
    bpairQRead.rel (BPair.addQ (BPair.addQ X (BPair.addQ Y Z)) W)
      (BPair.addQ X (BPair.addQ Y (BPair.addQ Z W))) :=
  qOneValue_trans (BPair.addQ_assoc X (BPair.addQ Y Z) W)
    (BPair.addQ_congr (qOneValue_refl X) (BPair.addQ_assoc Y Z W))

/-- Two right-nested four-term joins merge term by term. -/
private theorem merge4 (X1 Y1 Z1 W1 X2 Y2 Z2 W2 : BPair × Pos) :
    bpairQRead.rel (BPair.addQ (BPair.addQ X1 (BPair.addQ Y1 (BPair.addQ Z1 W1)))
        (BPair.addQ X2 (BPair.addQ Y2 (BPair.addQ Z2 W2))))
      (BPair.addQ (BPair.addQ X1 X2) (BPair.addQ (BPair.addQ Y1 Y2)
        (BPair.addQ (BPair.addQ Z1 Z2) (BPair.addQ W1 W2)))) :=
  qOneValue_trans (BPair.addQ_add_comm _ _ _ _)
    (BPair.addQ_congr (qOneValue_refl _) (qOneValue_trans (BPair.addQ_add_comm _ _ _ _)
      (BPair.addQ_congr (qOneValue_refl _) (BPair.addQ_add_comm _ _ _ _))))

/-- Three four-term joins regroup by position. -/
private theorem regroup (X1 Y1 Z1 W1 X2 Y2 Z2 W2 X3 Y3 Z3 W3 : BPair × Pos) :
    bpairQRead.rel (BPair.addQ (BPair.addQ (BPair.addQ X1 (BPair.addQ Y1 Z1)) W1)
        (BPair.addQ (BPair.addQ (BPair.addQ X2 (BPair.addQ Y2 Z2)) W2)
          (BPair.addQ (BPair.addQ X3 (BPair.addQ Y3 Z3)) W3)))
      (BPair.addQ (BPair.addQ X1 (BPair.addQ X2 X3))
        (BPair.addQ (BPair.addQ Y1 (BPair.addQ Y2 Y3))
          (BPair.addQ (BPair.addQ Z1 (BPair.addQ Z2 Z3))
            (BPair.addQ W1 (BPair.addQ W2 W3))))) :=
  qOneValue_trans (BPair.addQ_congr (flat4 _ _ _ _)
    (qOneValue_trans (BPair.addQ_congr (flat4 _ _ _ _) (flat4 _ _ _ _))
      (merge4 _ _ _ _ _ _ _ _)))
    (merge4 _ _ _ _ _ _ _ _)

/-- A read at the clearing one is the read at the clearing's own
multiple by one. -/
private theorem qone_mul_den (x : BPair) (d : Pos) :
    bpairQRead.rel (x, d) (x, Pos.one * d) := by
  show (x.scale (Pos.one * d)).oneValue (x.scale d)
  rw [ground.one_mul]
  exact BPair.oneValue_refl _

/-- The count identity behind the square reads' collection. -/
private theorem natX (m c : Nat) : m + c + m + 2 = c + (m + 1 + (1 + m)) := by
  rw [Nat.add_comm 1 m, ← Nat.add_assoc (m + 1) m 1, Nat.add_right_comm m 1 m,
    Nat.add_assoc (m + m) 1 1, Nat.add_right_comm m c m,
    Nat.add_right_comm (m + m) c 2, Nat.add_comm (m + m + 2) c]

/-- The square reads' part collects to `c₁² : 8` less one eighth. -/
private theorem xpart (m4 c1 : Nat) :
    bpairQRead.rel (BPair.addQ (BPair.ofNat (m4 + 2 * (c1 * c1) + m4), 16)
        (BPair.addQ ((BPair.ofNat (m4 + 1)).swap, 16)
          ((BPair.ofNat (1 + m4)).swap, 16)))
      (BPair.ofCounts (c1 * c1) 1, 8) := by
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (qadd_same _ _ _)) ?_
  refine qOneValue_trans (qadd_same _ _ _) ?_
  have hu : (BPair.ofNat (m4 + 2 * (c1 * c1) + m4)
      + ((BPair.ofNat (m4 + 1)).swap + (BPair.ofNat (1 + m4)).swap)).oneValue
      (BPair.ofCounts (m4 + 2 * (c1 * c1) + m4) (m4 + 1 + (1 + m4))) := by
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    rw [BPair.swap_add]
    exact ground.swap_congr (BPair.oneValue_symm (BPair.ofNat_add _ _))
  refine qOneValue_trans (qeq_num 16 hu) ?_
  refine qOneValue_trans (qeq_num 16
    (BPair.ofCounts_crossed (natX m4 (2 * (c1 * c1))))) ?_
  have h2 : 2 * (c1 * c1) = c1 * c1 + c1 * c1 := by
    rw [Nat.succ_mul, Nat.one_mul]
  rw [h2]
  refine qOneValue_trans (qeq_num 16 (BPair.ofCounts_add (c1 * c1) 1 (c1 * c1) 1)) ?_
  show ((BPair.ofCounts (c1 * c1) 1 + BPair.ofCounts (c1 * c1) 1).scale 8).oneValue
    ((BPair.ofCounts (c1 * c1) 1).scale 16)
  have h16 : (16 : Pos) = 8 + 8 := rfl
  rw [h16, BPair.scale_addW, BPair.scale_add]
  exact BPair.oneValue_refl _

/-- The channel folds' part reads the unit: the pair fold is the
two mixed folds' join, and each against its partner. -/
private theorem ypart {L : Type} (F : fusion.Data L) (hm2 : moment F 2 = 1) :
    bpairQRead.rel (BPair.addQ (qdiv (chanFold F 2 2 (F.row F.theta F.theta)) 8)
        (BPair.addQ (bpairQOps.swap (qdiv (chanFold F 2 0 (F.row F.theta F.theta)) 8))
          (bpairQOps.swap (qdiv (chanFold F 0 2 (F.row F.theta F.theta)) 8)))) bpairQOps.unit := by
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_trans (qdiv_congr 8
    (chanFold_split F hm2 _)) (qdiv_add _ _ _)) (qOneValue_refl _)) ?_
  refine qOneValue_trans (BPair.addQ_add_comm _ _ _ _) ?_
  exact qOneValue_trans (BPair.addQ_congr (qadd_neg _) (qadd_neg _)) qadd_zero

/-- The pair networks' part reads the `(2,2)` term alone, the mixed
terms at the vacant power reading the unit. -/
private theorem zpart (c : BPair) (S : BPair × Pos) :
    bpairQRead.rel (BPair.addQ (qscale c S)
        (BPair.addQ (bpairQOps.swap (qscale (BPair.ofNat 0) S)) (bpairQOps.swap (qscale (BPair.ofNat 0) S))))
      (bpairQOps.mul (c, Pos.one) S) := by
  have hz : bpairQRead.rel (bpairQOps.swap (qscale (BPair.ofNat 0) S)) bpairQOps.unit :=
    qswap_congr (qOneValue_unit (BPair.unit_mul S.1))
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (qOneValue_trans (BPair.addQ_congr hz hz) qadd_zero)) ?_
  refine qOneValue_trans (BPair.addQ_unitR _) ?_
  exact qone_mul_den _ _

/-- The distant products' part reads one eighth. -/
private theorem wpart :
    bpairQRead.rel (BPair.addQ ((BPair.ofNat 1).swap, 8)
        (BPair.addQ (bpairQOps.swap ((BPair.ofNat 1).swap, 8)) (bpairQOps.swap ((BPair.ofNat 1).swap, 8))))
      (BPair.ofNat 1, 8) := by
  show bpairQRead.rel (BPair.addQ ((BPair.ofNat 1).swap, 8)
    (BPair.addQ (BPair.ofNat 1, 8) (BPair.ofNat 1, 8))) (BPair.ofNat 1, 8)
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (qadd_same _ _ _)) ?_
  refine qOneValue_trans (qadd_same _ _ _) ?_
  refine qeq_num 8 ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.swap_add_null (BPair.oneValue_refl _)) (BPair.oneValue_refl _)) ?_
  exact BPair.unit_add _

/-- The fourth-order data collect: `D₂₂ − D₂₀ − D₀₂` reads
`c₁²/8 + c₁² S`. -/
private theorem jetD_read {L : Type} (F : fusion.Data L)
    (hm1 : moment F 1 = 0) (hm2 : moment F 2 = 1) (hm3 : moment F 3 = F.c1)
    (hT2 : powCount F 2 F.theta = F.c1) :
    bpairQRead.rel (BPair.addQ (jetD F 2 2) (BPair.addQ (bpairQOps.swap (jetD F 2 0)) (bpairQOps.swap (jetD F 0 2))))
      (BPair.addQ (BPair.ofNat (F.c1 * F.c1), 8)
        (bpairQOps.mul (BPair.ofNat (F.c1 * F.c1), Pos.one) (pairFold F))) := by
  rw [jetD22_read F hm2 hm3 hT2, jetD20_read F hm1 hm2 hm3 hT2,
    jetD02_read F hm1 hm2 hm3 hT2, qswap_add, qswap_add, qswap_add, qswap_add,
    qswap_add, qswap_add]
  refine qOneValue_trans (regroup _ _ _ _ _ _ _ _ _ _ _ _) ?_
  refine qOneValue_trans (BPair.addQ_congr (xpart _ _) (BPair.addQ_congr (ypart F hm2)
    (BPair.addQ_congr (zpart _ _) wpart))) ?_
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (BPair.addQ_unitL _)) ?_
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (BPair.addQ_comm _ _)) ?_
  refine qOneValue_trans (qOneValue_symm (BPair.addQ_assoc _ _ _)) ?_
  refine BPair.addQ_congr ?_ (qOneValue_refl _)
  refine qOneValue_trans (qadd_same _ _ _) ?_
  exact qeq_num 8 (BPair.add_swap_self (BPair.ofNat (F.c1 * F.c1)) (BPair.ofNat 1))

/-- One eighth against a quarter's partner collects to the eighth's
partner. -/
private theorem eighth_quarter (x : BPair) :
    bpairQRead.rel (BPair.addQ (x, 8) (x.swap, 4)) (x.swap, 8) := by
  show ((x.scale 4 + x.swap.scale 8).scale 8).oneValue (x.swap.scale (8 * 4))
  have h32 : (8 : Pos) * 4 = 4 * 8 := rfl
  rw [h32, ← BPair.scale_scale]
  refine BPair.scale_congr 8 ?_
  have h8 : (8 : Pos) = 4 + 4 := rfl
  rw [h8, BPair.scale_addW, BPair.scale_swap, ← BPair.add_assoc]
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.swap_add_null (BPair.oneValue_refl _))) (BPair.oneValue_refl _)) ?_
  exact BPair.unit_add _

/-- The closing read: the `τ⁴` coefficient at a fourth-order datum
reading `c₁²/8 + c₁² S` less a quarter of `c₁²` reads
`c₁² ⟨S : [1 : 8]⟩` cross-multiplied. -/
private theorem closing (c1 : Nat) (S K X : BPair × Pos)
    (hK : bpairQRead.rel K (BPair.addQ X ((BPair.ofNat (c1 * c1)).swap, 4)))
    (hX : bpairQRead.rel X (BPair.addQ (BPair.ofNat (c1 * c1), 8)
      (bpairQOps.mul (BPair.ofNat (c1 * c1), Pos.one) S))) :
    (K.1.scale (8 * S.2)).oneValue
      (((BPair.ofNat c1 * BPair.ofNat c1)
          * (S.1.scale 8 + (BPair.ofPos S.2).swap)).scale K.2) := by
  have s1 : bpairQRead.rel K (BPair.addQ (BPair.addQ (BPair.ofNat (c1 * c1), 8)
      (bpairQOps.mul (BPair.ofNat (c1 * c1), Pos.one) S)) ((BPair.ofNat (c1 * c1)).swap, 4)) :=
    qOneValue_trans hK (BPair.addQ_congr hX (qOneValue_refl ((BPair.ofNat (c1 * c1)).swap, 4)))
  have s2 : bpairQRead.rel (BPair.addQ (BPair.addQ (BPair.ofNat (c1 * c1), 8)
      (bpairQOps.mul (BPair.ofNat (c1 * c1), Pos.one) S)) ((BPair.ofNat (c1 * c1)).swap, 4))
      (BPair.addQ (BPair.ofNat (c1 * c1), 8)
        (BPair.addQ (bpairQOps.mul (BPair.ofNat (c1 * c1), Pos.one) S) ((BPair.ofNat (c1 * c1)).swap, 4))) :=
    BPair.addQ_assoc _ _ _
  have s3 : bpairQRead.rel (BPair.addQ (BPair.ofNat (c1 * c1), 8)
      (BPair.addQ (bpairQOps.mul (BPair.ofNat (c1 * c1), Pos.one) S) ((BPair.ofNat (c1 * c1)).swap, 4)))
      (BPair.addQ (bpairQOps.mul (BPair.ofNat (c1 * c1), Pos.one) S)
        (BPair.addQ (BPair.ofNat (c1 * c1), 8) ((BPair.ofNat (c1 * c1)).swap, 4))) :=
    qadd_rot _ _ _
  have s4 : bpairQRead.rel (BPair.addQ (BPair.ofNat (c1 * c1), 8) ((BPair.ofNat (c1 * c1)).swap, 4))
      ((BPair.ofNat (c1 * c1)).swap, 8) := eighth_quarter _
  have s5 : bpairQRead.rel (bpairQOps.mul (BPair.ofNat (c1 * c1), Pos.one) S)
      (BPair.ofNat (c1 * c1) * S.1, S.2) := qOneValue_symm (qone_mul_den _ _)
  have h1 : bpairQRead.rel K (BPair.addQ (BPair.ofNat (c1 * c1) * S.1, S.2)
      ((BPair.ofNat (c1 * c1)).swap, 8)) :=
    qOneValue_trans s1 (qOneValue_trans s2 (qOneValue_trans s3 (BPair.addQ_congr s5 s4)))
  have h2 : (K.1.scale (S.2 * 8)).oneValue
      (((BPair.ofNat (c1 * c1) * S.1).scale 8
        + (BPair.ofNat (c1 * c1)).swap.scale S.2).scale K.2) := h1
  rw [ground.mul_comm S.2 8] at h2
  refine BPair.oneValue_trans h2 (BPair.scale_congr K.2 ?_)
  rw [BPair.left_distrib, BPair.mul_scale, BPair.mul_swap, BPair.scale_swap]
  refine BPair.add_congr ?_ ?_
  · exact BPair.scale_congr 8 (BPair.mul_congr_left (BPair.ofNat_mul _ _))
  · refine ground.swap_congr ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofPos_scale _ _)) ?_
    exact BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.mul_congr_left (BPair.ofNat_mul _ _))

/-! The partition fold's three low keys at the jet's shape: the
eight moments' 3-list reads carried through the fold's sum,
convolution, partner and natural weights, key by key. -/

/-- A read at the sum's unit reads its numerator at the unit. -/
private theorem oneValue_of_qeq_z {p : BPair × Pos} (h : bpairQRead.rel p bpairQOps.unit) :
    p.1.oneValue BPair.unit := by
  have h' : (p.1.scale Pos.one).oneValue (BPair.unit.scale p.2) := h
  rw [BPair.scale_one] at h'
  refine BPair.oneValue_trans h' ?_
  show Pos.one * p.2 + Pos.one = Pos.one + Pos.one * p.2
  exact ground.add_comm _ _

private theorem qaddL {p q r : BPair × Pos} (hp : bpairQRead.rel p bpairQOps.unit) (hq : bpairQRead.rel q r) :
    bpairQRead.rel (BPair.addQ p q) r :=
  qOneValue_trans (BPair.addQ_congr hp hq) (BPair.addQ_unitL r)

private theorem qaddR {p q r : BPair × Pos} (hp : bpairQRead.rel p r) (hq : bpairQRead.rel q bpairQOps.unit) :
    bpairQRead.rel (BPair.addQ p q) r :=
  qOneValue_trans (BPair.addQ_congr hp hq) (BPair.addQ_unitR r)

private theorem qmul_zL {p : BPair × Pos} (h : bpairQRead.rel p bpairQOps.unit) (r : BPair × Pos) :
    bpairQRead.rel (bpairQOps.mul p r) bpairQOps.unit :=
  qOneValue_trans (qmul_congr h (qOneValue_refl r)) (qmul_zero_left (BPair.oneValue_refl _) r)

private theorem qmul_zR (r : BPair × Pos) {p : BPair × Pos} (h : bpairQRead.rel p bpairQOps.unit) :
    bpairQRead.rel (bpairQOps.mul r p) bpairQOps.unit :=
  qOneValue_trans (qmul_congr (qOneValue_refl r) h) (qmul_zero_right r (BPair.oneValue_refl _))

private theorem qhalf :
    bpairQRead.rel (BPair.addQ (BPair.ofNat 1, (4 : Pos)) (BPair.ofNat 1, (4 : Pos)))
      (BPair.ofNat 1, (2 : Pos)) := rfl

private theorem qone :
    bpairQRead.rel (BPair.addQ (BPair.ofNat 1, (2 : Pos)) (BPair.ofNat 1, (2 : Pos)))
      (BPair.ofNat 1, Pos.one) := rfl

private theorem qmulHH :
    bpairQRead.rel (bpairQOps.mul (BPair.ofNat 1, (2 : Pos)) (BPair.ofNat 1, (2 : Pos)))
      (BPair.ofNat 1, (4 : Pos)) := rfl

private theorem nsmul_z : ∀ (n : Nat) (x : BPair × Pos), bpairQRead.rel x bpairQOps.unit →
    bpairQRead.rel (poly.nsmulO ground.bpairQOps x n) bpairQOps.unit
  | 0, _, _ => qOneValue_refl bpairQOps.unit
  | _ + 1, _, h => qaddL h (nsmul_z _ _ h)

private theorem nsmul2 {x r : BPair × Pos} (h : bpairQRead.rel x r) :
    bpairQRead.rel (poly.nsmulO ground.bpairQOps x 2) (BPair.addQ r r) := by
  show bpairQRead.rel (BPair.addQ x (BPair.addQ x bpairQOps.unit)) (BPair.addQ r r)
  exact BPair.addQ_congr h (qaddR h (qOneValue_refl bpairQOps.unit))

/-! The polynomial carrier's key reads at the fold's own spellings. -/

/-! The per-node combinators: a key of a node from its children's. -/

private theorem addKey {p q : List (BPair × Pos)} {k : Nat} {r s : BPair × Pos}
    (hp : bpairQRead.rel (ground.getAt bpairQOps.unit p k) r) (hq : bpairQRead.rel (ground.getAt bpairQOps.unit q k) s) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).add p q) k)
      (BPair.addQ r s) :=
  qOneValue_trans (getAt_addQ p q k) (BPair.addQ_congr hp hq)

private theorem addKeyR {p q : List (BPair × Pos)} {k : Nat} {r : BPair × Pos}
    (hp : bpairQRead.rel (ground.getAt bpairQOps.unit p k) r) (hq : bpairQRead.rel (ground.getAt bpairQOps.unit q k) bpairQOps.unit) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).add p q) k) r :=
  qOneValue_trans (getAt_addQ p q k) (qaddR hp hq)

private theorem addKeyL {p q : List (BPair × Pos)} {k : Nat} {r : BPair × Pos}
    (hp : bpairQRead.rel (ground.getAt bpairQOps.unit p k) bpairQOps.unit) (hq : bpairQRead.rel (ground.getAt bpairQOps.unit q k) r) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).add p q) k) r :=
  qOneValue_trans (getAt_addQ p q k) (qaddL hp hq)

private theorem mulKey0 {p q : List (BPair × Pos)} {a b : BPair × Pos}
    (ha : bpairQRead.rel (ground.getAt bpairQOps.unit p 0) a) (hb : bpairQRead.rel (ground.getAt bpairQOps.unit q 0) b) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).mul p q) 0) (bpairQOps.mul a b) :=
  qOneValue_trans (getAt0_mul p q) (qmul_congr ha hb)

private theorem mulKey1 {p q : List (BPair × Pos)} {a0 a1 b0 b1 : BPair × Pos}
    (ha0 : bpairQRead.rel (ground.getAt bpairQOps.unit p 0) a0) (ha1 : bpairQRead.rel (ground.getAt bpairQOps.unit p 1) a1)
    (hb0 : bpairQRead.rel (ground.getAt bpairQOps.unit q 0) b0) (hb1 : bpairQRead.rel (ground.getAt bpairQOps.unit q 1) b1) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).mul p q) 1)
      (BPair.addQ (bpairQOps.mul a0 b1) (bpairQOps.mul a1 b0)) :=
  qOneValue_trans (getAt1_mul p q) (BPair.addQ_congr (qmul_congr ha0 hb1) (qmul_congr ha1 hb0))

private theorem mulKey2 {p q : List (BPair × Pos)} {a0 a1 a2 b0 b1 b2 : BPair × Pos}
    (ha0 : bpairQRead.rel (ground.getAt bpairQOps.unit p 0) a0) (ha1 : bpairQRead.rel (ground.getAt bpairQOps.unit p 1) a1)
    (ha2 : bpairQRead.rel (ground.getAt bpairQOps.unit p 2) a2) (hb0 : bpairQRead.rel (ground.getAt bpairQOps.unit q 0) b0)
    (hb1 : bpairQRead.rel (ground.getAt bpairQOps.unit q 1) b1) (hb2 : bpairQRead.rel (ground.getAt bpairQOps.unit q 2) b2) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).mul p q) 2)
      (BPair.addQ (bpairQOps.mul a0 b2)
        (BPair.addQ (bpairQOps.mul a1 b1) (bpairQOps.mul a2 b0))) :=
  qOneValue_trans (getAt2_mul p q)
    (BPair.addQ_congr (qmul_congr ha0 hb2)
      (BPair.addQ_congr (qmul_congr ha1 hb1) (qmul_congr ha2 hb0)))

private theorem mulKey0_unitL {p : List (BPair × Pos)} (q : List (BPair × Pos))
    (h : bpairQRead.rel (ground.getAt bpairQOps.unit p 0) bpairQOps.unit) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).mul p q) 0) bpairQOps.unit :=
  qOneValue_trans (getAt0_mul p q) (qmul_zL h _)

private theorem mulKey1_units {p q : List (BPair × Pos)}
    (hp : bpairQRead.rel (ground.getAt bpairQOps.unit p 0) bpairQOps.unit) (hq : bpairQRead.rel (ground.getAt bpairQOps.unit q 0) bpairQOps.unit) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).mul p q) 1) bpairQOps.unit :=
  qOneValue_trans (getAt1_mul p q) (qaddL (qmul_zL hp _) (qmul_zR _ hq))

private theorem mulKey1_unitL {p : List (BPair × Pos)} (q : List (BPair × Pos))
    (hp0 : bpairQRead.rel (ground.getAt bpairQOps.unit p 0) bpairQOps.unit) (hp1 : bpairQRead.rel (ground.getAt bpairQOps.unit p 1) bpairQOps.unit) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).mul p q) 1) bpairQOps.unit :=
  qOneValue_trans (getAt1_mul p q) (qaddL (qmul_zL hp0 _) (qmul_zL hp1 _))

private theorem mulKey2_units {p q : List (BPair × Pos)}
    (hp0 : bpairQRead.rel (ground.getAt bpairQOps.unit p 0) bpairQOps.unit) (hp1 : bpairQRead.rel (ground.getAt bpairQOps.unit p 1) bpairQOps.unit)
    (hq0 : bpairQRead.rel (ground.getAt bpairQOps.unit q 0) bpairQOps.unit) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).mul p q) 2) bpairQOps.unit :=
  qOneValue_trans (getAt2_mul p q)
    (qaddL (qmul_zL hp0 _) (qaddL (qmul_zL hp1 _) (qmul_zR _ hq0)))

private theorem nsmulKey_unit (n : Nat) {p : List (BPair × Pos)} {k : Nat}
    (h : bpairQRead.rel (ground.getAt bpairQOps.unit p k) bpairQOps.unit) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (poly.nsmulO (poly.polyO ground.bpairQOps) p n) k) bpairQOps.unit :=
  qOneValue_trans (getAt_nsmul n p k) (nsmul_z n _ h)

private theorem nsmulKey2 {p : List (BPair × Pos)} {k : Nat} {r : BPair × Pos}
    (h : bpairQRead.rel (ground.getAt bpairQOps.unit p k) r) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (poly.nsmulO (poly.polyO ground.bpairQOps) p 2) k)
      (BPair.addQ r r) :=
  qOneValue_trans (getAt_nsmul 2 p k) (nsmul2 h)

private theorem swapKey {p : List (BPair × Pos)} {k : Nat} {r : BPair × Pos}
    (h : bpairQRead.rel (ground.getAt bpairQOps.unit p k) r) :
    bpairQRead.rel (ground.getAt bpairQOps.unit ((poly.polyO ground.bpairQOps).swap p) k) (bpairQOps.swap r) := by
  show bpairQRead.rel (ground.getAt bpairQOps.unit (p.map ground.bpairQOps.swap) k) _
  rw [getAt_swapP]
  exact qswap_congr h

/-- The partition fold's three low keys at the jet's shape: at the
eight moments' displayed 3-lists the keys zero and one read the
sum's unit and the key two reads
`D₂₂ − D₂₀ − D₀₂ − c₁²/4`. -/
private theorem kappa4_low {μ : Nat → Nat → List (BPair × Pos)} (c1 : Nat)
    {D10 D01 D11 D20 D02 D12 D21 D22 : BPair × Pos}
    (h10 : μ 1 0 = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), D10])
    (h01 : μ 0 1 = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), D01])
    (h11 : μ 1 1 = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 0, 2), D11])
    (h20 : μ 2 0 = [(BPair.ofNat 1, Pos.one), (BPair.ofNat c1, 2), D20])
    (h02 : μ 0 2 = [(BPair.ofNat 1, Pos.one), (BPair.ofNat c1, 2), D02])
    (h12 : μ 1 2 = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), D12])
    (h21 : μ 2 1 = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), D21])
    (h22 : μ 2 2 = [(BPair.ofNat 1, Pos.one), (BPair.ofNat (c1 + c1), 2), D22]) :
    (ground.getAt bpairQOps.unit (kappa4 (poly.polyO ground.bpairQOps) μ) 0).1.oneValue BPair.unit
    ∧ (ground.getAt bpairQOps.unit (kappa4 (poly.polyO ground.bpairQOps) μ) 1).1.oneValue BPair.unit
    ∧ bpairQRead.rel (ground.getAt bpairQOps.unit (kappa4 (poly.polyO ground.bpairQOps) μ) 2)
        (BPair.addQ D22 (BPair.addQ (bpairQOps.swap D20)
          (BPair.addQ (bpairQOps.swap D02) ((BPair.ofNat (c1 * c1)).swap, 4)))) := by
  -- the eight moments' three low reads
  have r10_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 0) 0) bpairQOps.unit := by
    rw [h10]; exact qOneValue_refl _
  have r10_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 0) 1) (BPair.ofNat 1, (2 : Pos)) := by
    rw [h10]; exact qOneValue_refl _
  have r10_2 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 0) 2) D10 := by
    rw [h10]; exact qOneValue_refl _
  have r01_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 0 1) 0) bpairQOps.unit := by
    rw [h01]; exact qOneValue_refl _
  have r01_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 0 1) 1) (BPair.ofNat 1, (2 : Pos)) := by
    rw [h01]; exact qOneValue_refl _
  have r01_2 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 0 1) 2) D01 := by
    rw [h01]; exact qOneValue_refl _
  have r11_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 1) 0) bpairQOps.unit := by
    rw [h11]; exact qOneValue_refl _
  have r11_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 1) 1) bpairQOps.unit := by
    rw [h11]; exact qOneValue_unit (BPair.oneValue_refl _)
  have r20_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 0) 0) (BPair.ofNat 1, Pos.one) := by
    rw [h20]; exact qOneValue_refl _
  have r20_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 0) 1) (BPair.ofNat c1, (2 : Pos)) := by
    rw [h20]; exact qOneValue_refl _
  have r20_2 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 0) 2) D20 := by
    rw [h20]; exact qOneValue_refl _
  have r02_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 0 2) 0) (BPair.ofNat 1, Pos.one) := by
    rw [h02]; exact qOneValue_refl _
  have r02_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 0 2) 1) (BPair.ofNat c1, (2 : Pos)) := by
    rw [h02]; exact qOneValue_refl _
  have r02_2 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 0 2) 2) D02 := by
    rw [h02]; exact qOneValue_refl _
  have r12_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 2) 0) bpairQOps.unit := by
    rw [h12]; exact qOneValue_refl _
  have r12_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 2) 1) (BPair.ofNat 1, (2 : Pos)) := by
    rw [h12]; exact qOneValue_refl _
  have r12_2 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 1 2) 2) D12 := by
    rw [h12]; exact qOneValue_refl _
  have r21_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 1) 0) bpairQOps.unit := by
    rw [h21]; exact qOneValue_refl _
  have r21_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 1) 1) (BPair.ofNat 1, (2 : Pos)) := by
    rw [h21]; exact qOneValue_refl _
  have r21_2 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 1) 2) D21 := by
    rw [h21]; exact qOneValue_refl _
  have r22_0 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 2) 0) (BPair.ofNat 1, Pos.one) := by
    rw [h22]; exact qOneValue_refl _
  have r22_1 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 2) 1)
      (BPair.ofNat (c1 + c1), (2 : Pos)) := by
    rw [h22]; exact qOneValue_refl _
  have r22_2 : bpairQRead.rel (ground.getAt bpairQOps.unit (μ 2 2) 2) D22 := by
    rw [h22]; exact qOneValue_refl _
  -- the squares of the two odd moments and their cross
  have w0 := mulKey0_unitL (μ 1 0) r10_0
  have w1 := mulKey1_units r10_0 r10_0
  have w2 := qOneValue_trans (mulKey2 r10_0 r10_1 r10_2 r10_0 r10_1 r10_2)
    (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) D10)
      (qaddR qmulHH (qmul_zR D10 (qOneValue_refl bpairQOps.unit))))
  have v0 := mulKey0_unitL (μ 0 1) r01_0
  have v1 := mulKey1_units r01_0 r01_0
  have v2 := qOneValue_trans (mulKey2 r01_0 r01_1 r01_2 r01_0 r01_1 r01_2)
    (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) D01)
      (qaddR qmulHH (qmul_zR D01 (qOneValue_refl bpairQOps.unit))))
  have y0 := mulKey0_unitL (μ 0 1) r10_0
  have y1 := mulKey1_units r10_0 r01_0
  -- the first member's three insertions
  have xa0 := mulKey0_unitL (μ 0 2) w0
  have xa1 := mulKey1_unitL (μ 0 2) w0 w1
  have xa2 := qOneValue_trans (mulKey2 w0 w1 w2 r02_0 r02_1 r02_2)
    (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) D02)
      (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) (BPair.ofNat c1, (2 : Pos)))
        (qmul_one_right (BPair.ofNat 1, (4 : Pos)))))
  have xb0 := mulKey0_unitL (μ 2 0) v0
  have xb1 := mulKey1_unitL (μ 2 0) v0 v1
  have xb2 := qOneValue_trans (mulKey2 v0 v1 v2 r20_0 r20_1 r20_2)
    (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) D20)
      (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) (BPair.ofNat c1, (2 : Pos)))
        (qmul_one_right (BPair.ofNat 1, (4 : Pos)))))
  have xc0 := mulKey0_unitL (μ 1 1) y0
  have xc1 := mulKey1_unitL (μ 1 1) y0 y1
  have xc2 := mulKey2_units y0 y1 r11_0
  have t1_0 := nsmulKey_unit 2 xa0
  have t1_1 := nsmulKey_unit 2 xa1
  have t1_2 := qOneValue_trans (nsmulKey2 xa2) qhalf
  have t2_0 := nsmulKey_unit 2 xb0
  have t2_1 := nsmulKey_unit 2 xb1
  have t2_2 := qOneValue_trans (nsmulKey2 xb2) qhalf
  have t3_0 := nsmulKey_unit 8 xc0
  have t3_1 := nsmulKey_unit 8 xc1
  have t3_2 := nsmulKey_unit 8 xc2
  -- the second member's five terms
  have p1_0 := mulKey0_unitL (μ 1 2) r10_0
  have p1_1 := mulKey1_units r10_0 r12_0
  have p1_2 := qOneValue_trans (mulKey2 r10_0 r10_1 r10_2 r12_0 r12_1 r12_2)
    (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) D12)
      (qaddR qmulHH (qmul_zR D10 (qOneValue_refl bpairQOps.unit))))
  have p2_0 := mulKey0_unitL (μ 2 1) r01_0
  have p2_1 := mulKey1_units r01_0 r21_0
  have p2_2 := qOneValue_trans (mulKey2 r01_0 r01_1 r01_2 r21_0 r21_1 r21_2)
    (qaddL (qmul_zL (qOneValue_refl bpairQOps.unit) D21)
      (qaddR qmulHH (qmul_zR D01 (qOneValue_refl bpairQOps.unit))))
  have s1_0 := nsmulKey_unit 2 p1_0
  have s1_1 := nsmulKey_unit 2 p1_1
  have s1_2 := qOneValue_trans (nsmulKey2 p1_2) qhalf
  have s2_0 := nsmulKey_unit 2 p2_0
  have s2_1 := nsmulKey_unit 2 p2_1
  have s2_2 := qOneValue_trans (nsmulKey2 p2_2) qhalf
  have s3_0 := qOneValue_trans (mulKey0 r20_0 r02_0)
    (qmul_one_right (BPair.ofNat 1, Pos.one))
  have s3_1 := qOneValue_trans (mulKey1 r20_0 r20_1 r02_0 r02_1)
    (qOneValue_trans (BPair.addQ_congr (qmul_one_left (BPair.ofNat c1, (2 : Pos)))
        (qmul_one_right (BPair.ofNat c1, (2 : Pos))))
      (qOneValue_trans (qadd_same (BPair.ofNat c1) (BPair.ofNat c1) 2)
        (qeq_num 2 (BPair.oneValue_symm (BPair.ofNat_add c1 c1)))))
  have s3_2 := qOneValue_trans (mulKey2 r20_0 r20_1 r20_2 r02_0 r02_1 r02_2)
    (BPair.addQ_congr (qmul_one_left D02)
      (BPair.addQ_congr (qeq_num 4 (BPair.oneValue_symm (BPair.ofNat_mul c1 c1)))
        (qmul_one_right D20)))
  have s4_0 := nsmulKey_unit 2 (mulKey0_unitL (μ 1 1) r11_0)
  have s4_1 := nsmulKey_unit 2 (mulKey1_units r11_0 r11_0)
  have s4_2 := nsmulKey_unit 2 (mulKey2_units r11_0 r11_1 r11_0)
  have s5_0 := nsmulKey_unit 6
    (mulKey0_unitL ((poly.polyO ground.bpairQOps).mul (μ 0 1) (μ 0 1)) w0)
  have s5_1 := nsmulKey_unit 6
    (mulKey1_unitL ((poly.polyO ground.bpairQOps).mul (μ 0 1) (μ 0 1)) w0 w1)
  have s5_2 := nsmulKey_unit 6 (mulKey2_units w0 w1 v0)
  -- the two members' keys
  have m1k0 := addKeyR (addKeyR (addKeyR r22_0 t1_0) t2_0) t3_0
  have m1k1 := addKeyR (addKeyR (addKeyR r22_1 t1_1) t2_1) t3_1
  have m1k2 := qOneValue_trans (addKeyR (addKey (addKey r22_2 t1_2) t2_2) t3_2)
    (qOneValue_trans (BPair.addQ_assoc D22 (BPair.ofNat 1, (2 : Pos))
        (BPair.ofNat 1, (2 : Pos)))
      (BPair.addQ_congr (qOneValue_refl D22) qone))
  have m2k0 := addKeyR (addKeyR (addKeyL (addKeyR s1_0 s2_0) s3_0) s4_0) s5_0
  have m2k1 := addKeyR (addKeyR (addKeyL (addKeyR s1_1 s2_1) s3_1) s4_1) s5_1
  have m2k2 := qOneValue_trans (addKeyR (addKeyR (addKey (addKey s1_2 s2_2) s3_2) s4_2) s5_2)
    (BPair.addQ_congr qone (qOneValue_refl
      (BPair.addQ D02 (BPair.addQ (BPair.ofNat (c1 * c1), (4 : Pos)) D20))))
  -- the fold's keys
  have k0 := addKey m1k0 (swapKey m2k0)
  have k1 := addKey m1k1 (swapKey m2k1)
  have k2 := addKey m1k2 (swapKey m2k2)
  have hR : bpairQRead.rel (BPair.addQ (bpairQOps.swap D02)
        (BPair.addQ (bpairQOps.swap (BPair.ofNat (c1 * c1), (4 : Pos))) (bpairQOps.swap D20)))
      (BPair.addQ (bpairQOps.swap D20) (BPair.addQ (bpairQOps.swap D02)
        (bpairQOps.swap (BPair.ofNat (c1 * c1), (4 : Pos))))) :=
    qOneValue_trans (BPair.addQ_congr (qOneValue_refl (bpairQOps.swap D02))
        (BPair.addQ_comm (bpairQOps.swap (BPair.ofNat (c1 * c1), (4 : Pos))) (bpairQOps.swap D20)))
      (qadd_rot (bpairQOps.swap D02) (bpairQOps.swap D20)
        (bpairQOps.swap (BPair.ofNat (c1 * c1), (4 : Pos))))
  have hfin : bpairQRead.rel (BPair.addQ (BPair.addQ D22 (BPair.ofNat 1, Pos.one))
        (bpairQOps.swap (BPair.addQ (BPair.ofNat 1, Pos.one)
          (BPair.addQ D02
            (BPair.addQ (BPair.ofNat (c1 * c1), (4 : Pos)) D20)))))
      (BPair.addQ D22 (BPair.addQ (bpairQOps.swap D20)
        (BPair.addQ (bpairQOps.swap D02)
          ((BPair.ofNat (c1 * c1)).swap, (4 : Pos))))) := by
    rw [qswap_add, qswap_add, qswap_add]
    refine qOneValue_trans (BPair.addQ_assoc D22 (BPair.ofNat 1, Pos.one) _) ?_
    refine BPair.addQ_congr (qOneValue_refl D22) ?_
    refine qOneValue_trans (qOneValue_symm (BPair.addQ_assoc (BPair.ofNat 1, Pos.one)
      (bpairQOps.swap (BPair.ofNat 1, Pos.one)) _)) ?_
    exact qaddL (qadd_neg (BPair.ofNat 1, Pos.one)) hR
  exact ⟨oneValue_of_qeq_z
      (qOneValue_trans k0 (qadd_neg (BPair.ofNat 1, Pos.one))),
    oneValue_of_qeq_z
      (qOneValue_trans k1 (qadd_neg (BPair.ofNat (c1 + c1), 2))),
    qOneValue_trans k2 hfin⟩

/-! The jet's pairing reads collected: the second-order solve's two
folds against the moved monomials, the sector fold against the pair
fold, and the gram's three keys at the stated reads `m₁` of equal
members and `m₂ = 1`. -/

private theorem qmul_comm (p q : BPair × Pos) : bpairQOps.mul p q = bpairQOps.mul q p := by
  show (p.1 * q.1, p.2 * q.2) = (q.1 * p.1, q.2 * p.2)
  rw [BPair.mul_comm p.1 q.1, ground.mul_comm p.2 q.2]

/-- A read at the second member one is the first member's scale. -/
private theorem qmul_one_scale (X : BPair) (p : BPair × Pos) :
    bpairQRead.rel (bpairQOps.mul (X, Pos.one) p) (qscale X p) := by
  show ((X * p.1).scale p.2).oneValue ((X * p.1).scale (Pos.one * p.2))
  rw [ground.one_mul]
  exact BPair.oneValue_refl _

/-- The product at a second member one distributes over the join. -/
private theorem qmul_add (X : BPair) (p q : BPair × Pos) :
    bpairQRead.rel (bpairQOps.mul (X, Pos.one) (BPair.addQ p q))
      (BPair.addQ (bpairQOps.mul (X, Pos.one) p) (bpairQOps.mul (X, Pos.one) q)) := by
  refine qOneValue_trans (qmul_one_scale X (BPair.addQ p q)) ?_
  rw [qscale_add]
  exact BPair.addQ_congr (qOneValue_symm (qmul_one_scale X p)) (qOneValue_symm (qmul_one_scale X q))

/-- Two halves of a read join to the read. -/
private theorem qdiv_two_add (y : BPair × Pos) :
    bpairQRead.rel (BPair.addQ (qdiv y 2) (qdiv y 2)) y := by
  refine qOneValue_trans (qadd_same y.1 y.1 (y.2 * 2)) ?_
  show ((y.1 + y.1).scale y.2).oneValue (y.1.scale (y.2 * 2))
  rw [BPair.scale_add, show (2 : Pos) = Pos.one + Pos.one from rfl,
    ground.left_distrib, ground.mul_one, BPair.scale_addW]
  exact BPair.oneValue_refl _

/-- Two sixteenths of a read join to its eighth, the halves' read at
the eighth. -/
private theorem qdiv_double (x : BPair × Pos) :
    bpairQRead.rel (BPair.addQ (qdiv x 16) (qdiv x 16)) (qdiv x 8) := by
  have h16 : (16 : Pos) = 8 * 2 := rfl
  have h : qdiv x 16 = qdiv (qdiv x 8) 2 := by
    show (x.1, x.2 * 16) = (x.1, x.2 * 8 * 2)
    rw [h16, ground.mul_assoc]
  rw [h]
  exact qdiv_two_add (qdiv x 8)

/-- A read against the eighth at the second member one. -/
private theorem qmul_eighth (X : BPair) :
    bpairQRead.rel (bpairQOps.mul (X, Pos.one) (BPair.ofNat 1, 8)) (X, 8) := by
  show ((X * BPair.ofNat 1).scale 8).oneValue (X.scale (Pos.one * 8))
  rw [ground.one_mul]
  exact BPair.scale_congr 8 (BPair.mul_ofNat_one X)

/-- The module's two reads against the moved monomials collect to the
pair insertions' square reads. -/
private theorem oneRead_fold {L : Type} (F : fusion.Data L) (a b : Nat) :
    bpairQRead.rel (qdiv (BPair.addQ (oneRead F (a + 1) b) (oneRead F a (b + 1))) 4)
      (BPair.ofNat (moment F (a + 2) * moment F b
        + 2 * (moment F (a + 1) * moment F (b + 1)) + moment F a * moment F (b + 2)), 16) := by
  refine qOneValue_trans (qdiv_congr 4 (qadd_same _ _ 4)) ?_
  show bpairQRead.rel
    (BPair.ofNat (moment F (a + 1 + 1) * moment F b + moment F (a + 1) * moment F (b + 1))
      + BPair.ofNat (moment F (a + 1) * moment F (b + 1) + moment F a * moment F (b + 1 + 1)),
      4 * 4)
    (BPair.ofNat (moment F (a + 1 + 1) * moment F b
      + 2 * (moment F (a + 1) * moment F (b + 1)) + moment F a * moment F (b + 1 + 1)), 16)
  have hn : moment F (a + 1 + 1) * moment F b + 2 * (moment F (a + 1) * moment F (b + 1))
      + moment F a * moment F (b + 1 + 1)
      = moment F (a + 1 + 1) * moment F b + moment F (a + 1) * moment F (b + 1)
        + (moment F (a + 1) * moment F (b + 1) + moment F a * moment F (b + 1 + 1)) := by
    rw [Nat.two_mul,
      Nat.add_assoc (moment F (a + 1 + 1) * moment F b)
        (moment F (a + 1) * moment F (b + 1) + moment F (a + 1) * moment F (b + 1))
        (moment F a * moment F (b + 1 + 1)),
      Nat.add_assoc (moment F (a + 1) * moment F (b + 1))
        (moment F (a + 1) * moment F (b + 1)) (moment F a * moment F (b + 1 + 1)),
      Nat.add_assoc (moment F (a + 1 + 1) * moment F b)
        (moment F (a + 1) * moment F (b + 1))
        (moment F (a + 1) * moment F (b + 1) + moment F a * moment F (b + 1 + 1))]
  rw [hn]
  exact qOneValue_symm (qeq_num (4 * 4) (BPair.ofNat_add _ _))

/-- The sector fold reads half the scaled pair sum at the count. -/
private theorem secFold_read (T q t : Nat) : ∀ cs : List (Pos × Pos),
    bpairQRead.rel (secFold T q t cs)
      (qdiv (qscale (BPair.ofNat T) (qscale (BPair.ofPos (ground.posOfSucc q))
        (qdiv (sumQ cs) (ground.posOfSucc t * ground.posOfSucc t)))) 2)
  | [] => qOneValue_symm (qOneValue_unit (BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (BPair.mul_unit _)) (BPair.mul_unit _)))
  | (u, a) :: cs => by
    have ih := secFold_read T q t cs
    show bpairQRead.rel
      (BPair.addQ (BPair.ofNat T * BPair.ofPos (ground.posOfSucc q * u),
          (2 : Pos) * (a * (ground.posOfSucc t * ground.posOfSucc t)))
        (secFold T q t cs))
      (qdiv (qscale (BPair.ofNat T) (qscale (BPair.ofPos (ground.posOfSucc q))
        (qdiv (BPair.addQ (BPair.ofPos u, a) (sumQ cs))
          (ground.posOfSucc t * ground.posOfSucc t)))) 2)
    have hH : bpairQRead.rel
        (BPair.ofNat T * BPair.ofPos (ground.posOfSucc q * u),
          (2 : Pos) * (a * (ground.posOfSucc t * ground.posOfSucc t)))
        (qdiv (qscale (BPair.ofNat T) (qscale (BPair.ofPos (ground.posOfSucc q))
          (qdiv (BPair.ofPos u, a) (ground.posOfSucc t * ground.posOfSucc t)))) 2) := by
      show ((BPair.ofNat T * BPair.ofPos (ground.posOfSucc q * u)).scale
          (a * (ground.posOfSucc t * ground.posOfSucc t) * 2)).oneValue
        ((BPair.ofNat T * (BPair.ofPos (ground.posOfSucc q) * BPair.ofPos u)).scale
          ((2 : Pos) * (a * (ground.posOfSucc t * ground.posOfSucc t))))
      rw [ground.mul_comm (a * (ground.posOfSucc t * ground.posOfSucc t)) 2]
      exact BPair.scale_congr _ (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.oneValue_symm (BPair.ofPos_mul _ _)))
    refine qOneValue_trans (BPair.addQ_congr hH ih) ?_
    refine qOneValue_symm ?_
    refine qOneValue_trans (qdiv_congr 2 (qscale_congr (BPair.oneValue_refl _)
      (qscale_congr (BPair.oneValue_refl _) (qdiv_add _ _ _)))) ?_
    rw [qscale_add, qscale_add]
    exact qdiv_add _ _ 2

/-- The doubled sector read at the occupied data is the count's
scale of the pair fold; at vacant data both read the unit. -/
private theorem secRead_double {L : Type} (F : fusion.Data L) (c d : Nat) :
    bpairQRead.rel (BPair.addQ (secRead F c d) (secRead F c d))
      (qscale (BPair.ofNat (powCount F c F.theta * powCount F d F.theta)) (pairFold F)) := by
  cases hq : F.c2D with
  | zero =>
    have h1 : secRead F c d = (BPair.unit, Pos.one) := by
      unfold secRead atScale
      rw [hq]
    have h2 : pairFold F = (BPair.unit, Pos.one) := by
      unfold pairFold atScale
      rw [hq]
    rw [h1, h2]
    exact qOneValue_trans qadd_zero (qOneValue_symm (qOneValue_unit (BPair.mul_unit _)))
  | succ q =>
    cases ht : F.dim F.theta with
    | zero =>
      have h1 : secRead F c d = (BPair.unit, Pos.one) := by
        unfold secRead atScale
        rw [hq, ht]
      have h2 : pairFold F = (BPair.unit, Pos.one) := by
        unfold pairFold atScale
        rw [hq, ht]
      rw [h1, h2]
      exact qOneValue_trans qadd_zero (qOneValue_symm (qOneValue_unit (BPair.mul_unit _)))
    | succ t =>
      have h1 : secRead F c d
          = secFold (powCount F c F.theta * powCount F d F.theta) q t
              (chans q (fusion.adjChannels F)) := by
        unfold secRead atScale
        rw [hq, ht, chanList_at F q hq]
      rw [h1, pairFold_at F q t hq ht]
      refine qOneValue_trans (BPair.addQ_congr (secFold_read _ q t _) (secFold_read _ q t _)) ?_
      refine qOneValue_trans (qdiv_two_add _) ?_
      refine qscale_congr (BPair.oneValue_refl _) ?_
      exact qeq_num _ (BPair.ofPos_scale _ _)

/-- The doubled second-order read is the two folds of `D_ab`: the
channel fold at the eighth and the count's scale of the pair fold. -/
private theorem twoRead_double {L : Type} (F : fusion.Data L) (c d : Nat) :
    bpairQRead.rel (BPair.addQ (twoRead F c d) (twoRead F c d))
      (BPair.addQ (qdiv (chanFold F c d (F.row F.theta F.theta)) 8)
        (qscale (BPair.ofNat (powCount F c F.theta * powCount F d F.theta)) (pairFold F))) :=
  qOneValue_trans (BPair.addQ_add_comm _ _ _ _) (BPair.addQ_congr (qdiv_double _) (secRead_double F c d))

/-- The vacant power's channel fold reads the unit: every channel's
count at the unit power is the unit off the unit label. -/
private theorem chanFold_zero {L : Type} (F : fusion.Data L) :
    ∀ ks : List L, bpairQRead.rel (chanFold F 0 0 ks) bpairQOps.unit
  | [] => qOneValue_refl _
  | k :: ks => by
    have ih := chanFold_zero F ks
    cases hk : F.eqL k F.unit with
    | true =>
      show bpairQRead.rel (if F.eqL k F.unit then chanFold F 0 0 ks
        else BPair.addQ (chanTerm F 0 0 k) (chanFold F 0 0 ks)) _
      rw [hk]
      exact ih
    | false =>
      show bpairQRead.rel (if F.eqL k F.unit then chanFold F 0 0 ks
        else BPair.addQ (chanTerm F 0 0 k) (chanFold F 0 0 ks)) _
      rw [hk]
      refine qaddL ?_ ih
      cases hc : F.c2N k with
      | zero =>
        show bpairQRead.rel (match F.c2N k with
          | 0 => (BPair.unit, Pos.one)
          | p + 1 => (BPair.ofNat (F.count F.theta F.theta k
              * ((powCount F 0 k * moment F 0 + moment F 0 * powCount F 0 k) * F.c2D)),
             ground.posOfSucc p)) _
        rw [hc]
        exact qOneValue_refl _
      | succ p =>
        show bpairQRead.rel (match F.c2N k with
          | 0 => (BPair.unit, Pos.one)
          | p + 1 => (BPair.ofNat (F.count F.theta F.theta k
              * ((powCount F 0 k * moment F 0 + moment F 0 * powCount F 0 k) * F.c2D)),
             ground.posOfSucc p)) _
        rw [hc]
        have hp : powCount F 0 k = 0 := by
          show (if F.eqL k F.unit then 1 else 0) = 0
          rw [hk]
          exact rfl
        show bpairQRead.rel (BPair.ofNat (F.count F.theta F.theta k
            * ((powCount F 0 k * moment F 0 + moment F 0 * powCount F 0 k) * F.c2D)),
          ground.posOfSucc p) _
        rw [hp, Nat.zero_mul (moment F 0), Nat.mul_zero (moment F 0), Nat.add_zero,
          Nat.zero_mul F.c2D, Nat.mul_zero (F.count F.theta F.theta k)]
        exact qOneValue_unit (BPair.oneValue_refl _)

/-- The sector fold at the vacant count reads the unit. -/
private theorem secFold_zero (q t : Nat) : ∀ cs : List (Pos × Pos),
    bpairQRead.rel (secFold 0 q t cs) bpairQOps.unit
  | [] => qOneValue_refl _
  | (u, a) :: cs => by
    have ih := secFold_zero q t cs
    show bpairQRead.rel (BPair.addQ (BPair.ofNat 0 * BPair.ofPos (ground.posOfSucc q * u),
        (2 : Pos) * (a * (ground.posOfSucc t * ground.posOfSucc t))) (secFold 0 q t cs)) _
    exact qaddL (qOneValue_unit (BPair.unit_mul _)) ih

/-- The second-order read at the vacant powers is the unit. -/
private theorem twoRead_zero {L : Type} (F : fusion.Data L) (hm1 : moment F 1 = 0) :
    bpairQRead.rel (twoRead F 0 0) bpairQOps.unit := by
  have hT : powCount F 0 F.theta = 0 := (powCount_zero_theta F).trans hm1
  refine qaddL (qOneValue_unit (oneValue_of_qeq_z
    (p := chanFold F 0 0 (F.row F.theta F.theta)) (chanFold_zero F _))) ?_
  cases hq : F.c2D with
  | zero =>
    have h1 : secRead F 0 0 = (BPair.unit, Pos.one) := by
      unfold secRead atScale
      rw [hq]
    rw [h1]
    exact qOneValue_refl _
  | succ q =>
    cases ht : F.dim F.theta with
    | zero =>
      have h1 : secRead F 0 0 = (BPair.unit, Pos.one) := by
        unfold secRead atScale
        rw [hq, ht]
      rw [h1]
      exact qOneValue_refl _
    | succ t =>
      have h1 : secRead F 0 0 = secFold 0 q t (chanList F) := by
        unfold secRead atScale
        rw [hq, ht, hT, Nat.mul_zero]
      rw [h1]
      exact secFold_zero q t _

/-- The gram's unit read is one. -/
private theorem gram0 {L : Type} (F : fusion.Data L) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F 0 0) 0) (BPair.ofNat 1, Pos.one) := by
  have hm0 : moment F 0 = 1 := rfl
  show bpairQRead.rel (BPair.ofNat (moment F 0 * moment F 0), Pos.one) _
  rw [hm0, Nat.mul_one]
  exact qOneValue_refl _

/-- The gram's `τ²` read is the unit at `m₁` of equal members. -/
private theorem gram1 {L : Type} (F : fusion.Data L) (hm1 : moment F 1 = 0) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F 0 0) 1) bpairQOps.unit := by
  have hm0 : moment F 0 = 1 := rfl
  have h : oneRead F 0 0 = (BPair.ofNat 0, 4) := by
    show (BPair.ofNat (moment F 1 * moment F 0 + moment F 0 * moment F 1), 4) = _
    rw [hm1, hm0, Nat.zero_mul 1, Nat.add_zero]
  show bpairQRead.rel (BPair.addQ (oneRead F 0 0) (oneRead F 0 0)) _
  rw [h]
  exact qaddL (qOneValue_unit (BPair.oneValue_refl _)) (qOneValue_unit (BPair.oneValue_refl _))

/-- The gram's `τ⁴` read is the eighth at `m₁` of equal members and
`m₂ = 1`. -/
private theorem gram2 {L : Type} (F : fusion.Data L) (hm1 : moment F 1 = 0)
    (hm2 : moment F 2 = 1) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F 0 0) 2) (BPair.ofNat 1, 8) := by
  have hm0 : moment F 0 = 1 := rfl
  show bpairQRead.rel (BPair.addQ (qdiv (BPair.addQ (oneRead F (0 + 1) 0) (oneRead F 0 (0 + 1))) 4)
    (BPair.addQ (twoRead F 0 0) (twoRead F 0 0))) _
  refine qaddR ?_ (qaddL (twoRead_zero F hm1) (twoRead_zero F hm1))
  refine qOneValue_trans (oneRead_fold F 0 0) ?_
  show bpairQRead.rel (BPair.ofNat (moment F 2 * moment F 0
    + 2 * (moment F 1 * moment F 1) + moment F 0 * moment F 2), 16) _
  rw [hm0, hm1, hm2, Nat.mul_one 1, Nat.mul_zero 0, Nat.add_zero 1]
  exact rfl

/-- The `τ²` pairing read is the displayed first-order coefficient. -/
private theorem pair1_read {L : Type} (F : fusion.Data L) (a b : Nat) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F a b) 1)
      (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) := by
  show bpairQRead.rel (BPair.addQ (oneRead F a b) (oneRead F a b)) _
  refine qOneValue_trans (qadd_same _ _ 4) ?_
  show ((BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1))
    + BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1))).scale 2).oneValue
    ((BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1))).scale 4)
  rw [BPair.scale_add, show (4 : Pos) = 2 + 2 from rfl, BPair.scale_addW]
  exact BPair.oneValue_refl _

/-- The `τ⁴` pairing read is `D_ab` joined to the eighth of the unit's
read: the module's square reads, the channel fold at the eighth and
the count's scale of the pair fold. -/
private theorem pair2_read {L : Type} (F : fusion.Data L) (a b : Nat) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F a b) 2)
      (BPair.addQ (BPair.ofNat (moment F (a + 2) * moment F b
          + 2 * (moment F (a + 1) * moment F (b + 1)) + moment F a * moment F (b + 2)), 16)
        (BPair.addQ (qdiv (chanFold F a b (F.row F.theta F.theta)) 8)
          (qscale (BPair.ofNat (powCount F a F.theta * powCount F b F.theta)) (pairFold F)))) := by
  show bpairQRead.rel (BPair.addQ (qdiv (BPair.addQ (oneRead F (a + 1) b) (oneRead F a (b + 1))) 4)
    (BPair.addQ (twoRead F a b) (twoRead F a b))) _
  exact BPair.addQ_congr (oneRead_fold F a b) (twoRead_double F a b)

/-- The jet moments read the displayed orders: the jet's pairing
polynomial at `(a, b)` is the jet moments' product with the gram, the
`(0, 0)` pairing, at the keys through `τ⁴` — the unit at the reads
`m₁` of equal members and `m₂ = 1`, `lem:fourpoint`'s stated reads. -/
theorem jetRead {L : Type} (F : fusion.Data L) (a b : Nat)
    (hm1 : moment F 1 = 0) (hm2 : moment F 2 = 1) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F a b) 0)
        (ground.getAt bpairQOps.unit
          ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (jetPair F 0 0)) 0)
      ∧ bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F a b) 1)
        (ground.getAt bpairQOps.unit
          ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (jetPair F 0 0)) 1)
      ∧ bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F a b) 2)
        (ground.getAt bpairQOps.unit
          ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (jetPair F 0 0)) 2) := by
  have hG0 := gram0 F
  have hG1 := gram1 F hm1
  have hG2 := gram2 F hm1 hm2
  have hJ0 : bpairQRead.rel (ground.getAt bpairQOps.unit (jetMoment F a b) 0)
      (BPair.ofNat (moment F a * moment F b), Pos.one) := qOneValue_refl _
  have hJ1 : bpairQRead.rel (ground.getAt bpairQOps.unit (jetMoment F a b) 1)
      (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) :=
    qOneValue_refl _
  have hJ2 : bpairQRead.rel (ground.getAt bpairQOps.unit (jetMoment F a b) 2) (jetD F a b) :=
    qOneValue_refl _
  refine ⟨?_, ?_, ?_⟩
  · have hP : bpairQRead.rel (ground.getAt bpairQOps.unit (jetPair F a b) 0)
        (BPair.ofNat (moment F a * moment F b), Pos.one) := qOneValue_refl _
    refine qOneValue_trans hP (qOneValue_symm ?_)
    exact qOneValue_trans (mulKey0 hJ0 hG0) (qmul_one_right _)
  · refine qOneValue_trans (pair1_read F a b) (qOneValue_symm ?_)
    refine qOneValue_trans (mulKey1 hJ0 hJ1 hG0 hG1) ?_
    exact qaddL (qmul_zR _ (qOneValue_refl _)) (qmul_one_right _)
  · refine qOneValue_trans (pair2_read F a b) (qOneValue_symm ?_)
    refine qOneValue_trans (mulKey2 hJ0 hJ1 hJ2 hG0 hG1 hG2) ?_
    refine qOneValue_trans (BPair.addQ_congr (qmul_eighth _)
      (qaddL (qmul_zR _ (qOneValue_refl _)) (qmul_one_right _))) ?_
    show bpairQRead.rel (BPair.addQ (BPair.ofNat (moment F a * moment F b), 8)
      (BPair.addQ
        (BPair.addQ (BPair.ofNat (moment F (a + 2) * moment F b
            + 2 * (moment F (a + 1) * moment F (b + 1)) + moment F a * moment F (b + 2)), 16)
          (BPair.addQ (qdiv (chanFold F a b (F.row F.theta F.theta)) 8)
            (qscale (BPair.ofNat (powCount F a F.theta * powCount F b F.theta)) (pairFold F))))
        ((BPair.ofNat (moment F a * moment F b)).swap, 8))) _
    refine qOneValue_trans (qadd_rot _ _ _) ?_
    exact qaddR (qOneValue_refl _) (qadd_neg (BPair.ofNat (moment F a * moment F b), 8))

/-- A window's read beyond the graph's band is the pair's at every far
datum: the far insertions enter the pairing and the gram equally, a
summand on both members fixing the value, and the window's pairing
polynomial reads the jet moments' product with its gram at the keys
through `τ⁴`. -/
theorem jetWindow {L : Type} (F : fusion.Data L) (a b : Nat) (f : BPair × Pos)
    (hm1 : moment F 1 = 0) (hm2 : moment F 2 = 1) :
    bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F a b f) 0)
        (ground.getAt bpairQOps.unit
          ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (farPair F 0 0 f)) 0)
      ∧ bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F a b f) 1)
        (ground.getAt bpairQOps.unit
          ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (farPair F 0 0 f)) 1)
      ∧ bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F a b f) 2)
        (ground.getAt bpairQOps.unit
          ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (farPair F 0 0 f)) 2) := by
  have hG0 := gram0 F
  have hG1 := gram1 F hm1
  have hG2 := gram2 F hm1 hm2
  have hJ0 : bpairQRead.rel (ground.getAt bpairQOps.unit (jetMoment F a b) 0)
      (BPair.ofNat (moment F a * moment F b), Pos.one) := qOneValue_refl _
  have hJ1 : bpairQRead.rel (ground.getAt bpairQOps.unit (jetMoment F a b) 1)
      (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) := qOneValue_refl _
  have hJ2 : bpairQRead.rel (ground.getAt bpairQOps.unit (jetMoment F a b) 2) (jetD F a b) :=
    qOneValue_refl _
  have hR := (jetRead F a b hm1 hm2).2.2
  have hL : bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F a b f) 2)
      (BPair.addQ (ground.getAt bpairQOps.unit (jetPair F a b) 2) (bpairQOps.mul f (BPair.ofNat (moment F a * moment F b), Pos.one))) :=
    addKey (p := jetPair F a b) (q := farTail F a b f) (qOneValue_refl _) (qOneValue_refl _)
  have hW0 : bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F 0 0 f) 0)
      (BPair.ofNat 1, Pos.one) :=
    addKeyR (q := farTail F 0 0 f) hG0 (qOneValue_refl _)
  have hW1 : bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F 0 0 f) 1)
      bpairQOps.unit :=
    addKeyR (q := farTail F 0 0 f) hG1 (qOneValue_refl _)
  have hW2 : bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F 0 0 f) 2)
      (BPair.addQ (BPair.ofNat 1, 8) (bpairQOps.mul f (BPair.ofNat 1, Pos.one))) :=
    addKey (q := farTail F 0 0 f) hG2 (qmul_congr (qOneValue_refl f) hG0)
  refine ⟨?_, ?_, ?_⟩
  · have hL0 : bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F a b f) 0)
        (BPair.ofNat (moment F a * moment F b), Pos.one) :=
      addKeyR (p := jetPair F a b) (q := farTail F a b f) (qOneValue_refl _) (qOneValue_refl _)
    refine qOneValue_trans hL0 (qOneValue_symm ?_)
    exact qOneValue_trans (mulKey0 hJ0 hW0) (qmul_one_right _)
  · have hL1 : bpairQRead.rel (ground.getAt bpairQOps.unit (farPair F a b f) 1)
        (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) :=
      addKeyR (p := jetPair F a b) (q := farTail F a b f) (pair1_read F a b) (qOneValue_refl _)
    refine qOneValue_trans hL1 (qOneValue_symm ?_)
    refine qOneValue_trans (mulKey1 hJ0 hJ1 hW0 hW1) ?_
    exact qaddL (qmul_zR _ (qOneValue_refl _)) (qmul_one_right _)
  · have h1 : bpairQRead.rel (ground.getAt bpairQOps.unit
        ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (farPair F 0 0 f)) 2)
        (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.addQ (BPair.ofNat 1, 8) (bpairQOps.mul f (BPair.ofNat 1, Pos.one)))) (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) bpairQOps.unit) (bpairQOps.mul (jetD F a b) (BPair.ofNat 1, Pos.one)))) :=
      mulKey2 hJ0 hJ1 hJ2 hW0 hW1 hW2
    have h2 : bpairQRead.rel (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.addQ (BPair.ofNat 1, 8) (bpairQOps.mul f (BPair.ofNat 1, Pos.one)))) (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) bpairQOps.unit) (bpairQOps.mul (jetD F a b) (BPair.ofNat 1, Pos.one))))
        (BPair.addQ (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one)))) (jetD F a b)) :=
      BPair.addQ_congr (qmul_add _ _ _) (qaddL (qmul_zR _ (qOneValue_refl _)) (qmul_one_right _))
    have h3 : bpairQRead.rel (BPair.addQ (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one)))) (jetD F a b))
        (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one))) (jetD F a b))) := BPair.addQ_assoc _ _ _
    have h4 : bpairQRead.rel (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one))) (jetD F a b)))
        (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (BPair.addQ (jetD F a b) (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one))))) := BPair.addQ_congr (qOneValue_refl _) (BPair.addQ_comm _ _)
    have h5 : bpairQRead.rel (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (BPair.addQ (jetD F a b) (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one)))))
        (BPair.addQ (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (jetD F a b)) (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one)))) := qOneValue_symm (BPair.addQ_assoc _ _ _)
    have h6a : bpairQRead.rel (ground.getAt bpairQOps.unit
        ((poly.polyO ground.bpairQOps).mul (jetMoment F a b) (jetPair F 0 0)) 2)
        (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) bpairQOps.unit) (bpairQOps.mul (jetD F a b) (BPair.ofNat 1, Pos.one)))) :=
      mulKey2 hJ0 hJ1 hJ2 hG0 hG1 hG2
    have h6b : bpairQRead.rel (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F (a + 1) * moment F b + moment F a * moment F (b + 1)), 2) bpairQOps.unit) (bpairQOps.mul (jetD F a b) (BPair.ofNat 1, Pos.one)))) (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (jetD F a b)) :=
      BPair.addQ_congr (qOneValue_refl _) (qaddL (qmul_zR _ (qOneValue_refl _)) (qmul_one_right _))
    have h6 : bpairQRead.rel (BPair.addQ (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (BPair.ofNat 1, 8)) (jetD F a b)) (ground.getAt bpairQOps.unit (jetPair F a b) 2) :=
      qOneValue_symm (qOneValue_trans hR (qOneValue_trans h6a h6b))
    have h7 : bpairQRead.rel (bpairQOps.mul (BPair.ofNat (moment F a * moment F b), Pos.one) (bpairQOps.mul f (BPair.ofNat 1, Pos.one))) (bpairQOps.mul f (BPair.ofNat (moment F a * moment F b), Pos.one)) :=
      qOneValue_trans (qmul_congr (qOneValue_refl _) (qmul_one_right f)) (qOneValue_of_eq (qmul_comm _ _))
    exact qOneValue_trans hL (qOneValue_symm (qOneValue_trans h1 (qOneValue_trans h2 (qOneValue_trans h3
      (qOneValue_trans h4 (qOneValue_trans h5 (BPair.addQ_congr h6 h7)))))))

/-- The collection: the jet moments' partition fold reads the unit
at `τ⁰` and at `τ²`, and at `τ⁴` the pair-network read against the
distant product's, `c₁² ⟨S : [1 : 8]⟩` — the `τ²` reads enter the
fold's two members equally, the single-channel folds and the
fourth-moment reads enter `D₂₂` and twice `D₂₀` equally, and the
`τ²` cross products collect against the square terms. -/
theorem collection {L : Type} (F : fusion.Data L)
    (hm1 : moment F 1 = 0) (hm2 : moment F 2 = 1) (hm3 : moment F 3 = F.c1)
    (hT2 : powCount F 2 F.theta = F.c1) :
    (ground.getAt bpairQOps.unit
        (kappa4 (poly.polyO ground.bpairQOps) (jetMoment F)) 0).1.oneValue BPair.unit
    ∧ (ground.getAt bpairQOps.unit
        (kappa4 (poly.polyO ground.bpairQOps) (jetMoment F)) 1).1.oneValue BPair.unit
    ∧ ((ground.getAt bpairQOps.unit
          (kappa4 (poly.polyO ground.bpairQOps) (jetMoment F)) 2).1.scale
          (8 * (pairFold F).2)).oneValue
        (((BPair.ofNat F.c1 * BPair.ofNat F.c1)
            * ((pairFold F).1.scale 8 + (BPair.ofPos (pairFold F).2).swap)).scale
          (ground.getAt bpairQOps.unit
            (kappa4 (poly.polyO ground.bpairQOps) (jetMoment F)) 2).2) := by
  have hm0 : moment F 0 = 1 := rfl
  have h10 : jetMoment F 1 0
      = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), jetD F 1 0] := by
    show [(BPair.ofNat (moment F 1 * moment F 0), Pos.one),
      (BPair.ofNat (moment F 2 * moment F 0 + moment F 1 * moment F 1), 2), jetD F 1 0] = _
    rw [hm1, hm0, hm2]
  have h01 : jetMoment F 0 1
      = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), jetD F 0 1] := by
    show [(BPair.ofNat (moment F 0 * moment F 1), Pos.one),
      (BPair.ofNat (moment F 1 * moment F 1 + moment F 0 * moment F 2), 2), jetD F 0 1] = _
    rw [hm1, hm0, hm2]
  have h11 : jetMoment F 1 1
      = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 0, 2), jetD F 1 1] := by
    show [(BPair.ofNat (moment F 1 * moment F 1), Pos.one),
      (BPair.ofNat (moment F 2 * moment F 1 + moment F 1 * moment F 2), 2), jetD F 1 1] = _
    rw [hm1, hm2]
  have h20 : jetMoment F 2 0
      = [(BPair.ofNat 1, Pos.one), (BPair.ofNat F.c1, 2), jetD F 2 0] := by
    show [(BPair.ofNat (moment F 2 * moment F 0), Pos.one),
      (BPair.ofNat (moment F 3 * moment F 0 + moment F 2 * moment F 1), 2), jetD F 2 0] = _
    rw [hm1, hm0, hm2, hm3, Nat.mul_one F.c1, Nat.add_zero F.c1]
  have h02 : jetMoment F 0 2
      = [(BPair.ofNat 1, Pos.one), (BPair.ofNat F.c1, 2), jetD F 0 2] := by
    show [(BPair.ofNat (moment F 0 * moment F 2), Pos.one),
      (BPair.ofNat (moment F 1 * moment F 2 + moment F 0 * moment F 3), 2), jetD F 0 2] = _
    rw [hm1, hm0, hm2, hm3, Nat.one_mul F.c1, Nat.zero_add F.c1]
  have h12 : jetMoment F 1 2
      = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), jetD F 1 2] := by
    show [(BPair.ofNat (moment F 1 * moment F 2), Pos.one),
      (BPair.ofNat (moment F 2 * moment F 2 + moment F 1 * moment F 3), 2), jetD F 1 2] = _
    rw [hm1, hm2, hm3, Nat.zero_mul F.c1]
  have h21 : jetMoment F 2 1
      = [(BPair.ofNat 0, Pos.one), (BPair.ofNat 1, 2), jetD F 2 1] := by
    show [(BPair.ofNat (moment F 2 * moment F 1), Pos.one),
      (BPair.ofNat (moment F 3 * moment F 1 + moment F 2 * moment F 2), 2), jetD F 2 1] = _
    rw [hm1, hm2, hm3, Nat.mul_zero F.c1]
  have h22 : jetMoment F 2 2
      = [(BPair.ofNat 1, Pos.one), (BPair.ofNat (F.c1 + F.c1), 2), jetD F 2 2] := by
    show [(BPair.ofNat (moment F 2 * moment F 2), Pos.one),
      (BPair.ofNat (moment F 3 * moment F 2 + moment F 2 * moment F 3), 2), jetD F 2 2] = _
    rw [hm2, hm3, Nat.mul_one F.c1, Nat.one_mul F.c1]
  obtain ⟨k0, k1, k2⟩ := kappa4_low (μ := jetMoment F) F.c1
    h10 h01 h11 h20 h02 h12 h21 h22
  refine ⟨k0, k1, closing F.c1 (pairFold F) _ _ ?_ (jetD_read F hm1 hm2 hm3 hT2)⟩
  refine qOneValue_trans k2 ?_
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _) (qOneValue_symm (BPair.addQ_assoc _ _ _))) ?_
  exact qOneValue_symm (BPair.addQ_assoc _ _ _)


/-! `lem:fourpoint`'s tail: the pencil at the ray, the jet
and its residual with the jet identity, the residual's weight and the
second-order solve floor. -/

open elim inertia


/-- The pencil at the ray `[1 : τ²]` at the clearing `q²`, `q² E − p² M`,
the site datum's read (`lem:fourpoint`'s tail). -/
def rayH (p q : Pos) (E M : Mat) : Mat :=
  siteDatum (matScale (q * q) E) (matScale (p * p) M)

/-- The jet at the clearing `q⁴`: `q⁴ 𝟏 + p² q² ψ₁ + p⁴ ψ₂`. -/
def jetVec (p q : Pos) (one psi1 psi2 : List BPair) : List BPair :=
  vecAdd (vecScale (BPair.ofPos (Pos.pow q 4)) one)
    (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
      (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))

/-- The residual at the clearing `4 q⁸`: `q² p⁶ (#p ψ₁ − 4 M ψ₂) + p⁸ #p ψ₂`,
`lem:fourpoint`'s `ρ` cleared. -/
def residVec (p q : Pos) (np : Nat) (M : Mat) (psi1 psi2 : List BPair) : List BPair :=
  vecAdd (vecScale (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np) psi1)
    (vecAdd ((vecScale (BPair.ofPos (4 * (q * q) * Pos.pow p 6)) (matVec M psi2)).map BPair.swap)
      (vecScale (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np) psi2))

/-- A ground datum's square is its second power. -/
private theorem posSq (a : Pos) : a * a = Pos.pow a 2 :=
  (Pos.pow_two a).symm

/-- The eighth power splits at the fourth. -/
private theorem posP8 (p : Pos) : Pos.pow p 8 = Pos.pow p 4 * Pos.pow p 4 :=
  Pos.pow_add p 4 4

/-- The eighth power's square is the sixteenth. -/
private theorem posP16 (p : Pos) : Pos.pow p 8 * Pos.pow p 8 = Pos.pow p 16 :=
  (Pos.pow_add p 8 8).symm

/-- The residual's first clearing squared, `(q²p⁶)² = q⁴p¹²`. -/
private theorem posU2 (p q : Pos) :
    (q * q * Pos.pow p 6) * (q * q * Pos.pow p 6)
      = Pos.pow q 4 * Pos.pow p 12 := by
  rw [ground.mul_mul_mul_comm (q * q) (Pos.pow p 6) (q * q) (Pos.pow p 6),
    posSq q, ← Pos.pow_add q 2 2, ← Pos.pow_add p 6 6]

/-- The residual's magnetic clearing squared, `(4q²p⁶)² = 16 q⁴p¹²`. -/
private theorem posV2 (p q : Pos) :
    (4 * (q * q) * Pos.pow p 6) * (4 * (q * q) * Pos.pow p 6)
      = 16 * (Pos.pow q 4 * Pos.pow p 12) := by
  rw [ground.mul_mul_mul_comm (4 * (q * q)) (Pos.pow p 6)
      (4 * (q * q)) (Pos.pow p 6),
    ground.mul_mul_mul_comm (4 : Pos) (q * q) (4 : Pos) (q * q),
    posSq q, ← Pos.pow_add q 2 2, ← Pos.pow_add p 6 6,
    ground.mul_assoc ((4 : Pos) * 4) (Pos.pow q 4) (Pos.pow p 12),
    show (4 : Pos) * 4 = 16 from rfl]

/-- The magnetic term's clearing collected, `4·(16 u)(W²) = u(64 W²)`. -/
private theorem posMix (u2 W : Pos) :
    (4 : Pos) * (16 * u2 * (W * W)) = u2 * (64 * (W * W)) := by
  rw [ground.mul_assoc (16 : Pos) u2 (W * W),
    ← ground.mul_assoc (4 : Pos) 16 (u2 * (W * W)),
    ← ground.mul_assoc u2 64 (W * W),
    ground.mul_comm u2 (64 : Pos),
    ground.mul_assoc (64 : Pos) u2 (W * W),
    show (4 : Pos) * 16 = 64 from rfl]

/-- The electric second-order clearing at its monomial form. -/
private theorem posA3read (p q : Pos) :
    4 * (q * q) * (q * q) * Pos.pow p 4 = 4 * (Pos.pow p 4 * Pos.pow q 4) := by
  rw [posSq q, ground.mul_assoc (4 : Pos) (Pos.pow q 2) (Pos.pow q 2),
    ← Pos.pow_add q 2 2, ground.mul_assoc (4 : Pos) (Pos.pow q 4) (Pos.pow p 4),
    ground.mul_comm (Pos.pow q 4) (Pos.pow p 4)]

/-- The jet level's clearing at its monomial form. -/
private theorem posT4read (p q : Pos) :
    Pos.pow p 4 * Pos.pow q 4 * 4 = 4 * (Pos.pow p 4 * Pos.pow q 4) :=
  ground.mul_comm _ _

/-- The magnetic first-order clearing at its monomial form. -/
private theorem posB2read (p q : Pos) :
    4 * (q * q) * (p * p) * (p * p * (q * q))
      = 4 * (Pos.pow p 4 * Pos.pow q 4) := by
  rw [posSq p, posSq q,
    ground.mul_assoc (4 * Pos.pow q 2) (Pos.pow p 2)
      (Pos.pow p 2 * Pos.pow q 2),
    ← ground.mul_assoc (Pos.pow p 2) (Pos.pow p 2) (Pos.pow q 2),
    ← Pos.pow_add p 2 2,
    ground.mul_assoc (4 : Pos) (Pos.pow q 2) (Pos.pow p 4 * Pos.pow q 2),
    ground.mul_left_comm (Pos.pow q 2) (Pos.pow p 4) (Pos.pow q 2),
    ← Pos.pow_add q 2 2]

/-- The magnetic level clearing at its monomial form. -/
private theorem posB1read (p q : Pos) :
    4 * (q * q) * (p * p) * Pos.pow q 4
      = 4 * (Pos.pow p 2 * Pos.pow q 6) := by
  rw [posSq p, posSq q,
    ground.mul_right_comm (4 * Pos.pow q 2) (Pos.pow p 2) (Pos.pow q 4),
    ground.mul_assoc (4 : Pos) (Pos.pow q 2) (Pos.pow q 4),
    ← Pos.pow_add q 2 4,
    ground.mul_assoc (4 : Pos) (Pos.pow q 6) (Pos.pow p 2),
    ground.mul_comm (Pos.pow q 6) (Pos.pow p 2)]

/-- The electric first-order clearing at its monomial form. -/
private theorem posA2read (p q : Pos) :
    4 * (q * q) * (q * q) * (p * p * (q * q))
      = 4 * (Pos.pow p 2 * Pos.pow q 6) := by
  rw [posSq p, posSq q,
    ground.mul_assoc (4 * Pos.pow q 2) (Pos.pow q 2)
      (Pos.pow p 2 * Pos.pow q 2),
    ground.mul_left_comm (Pos.pow q 2) (Pos.pow p 2) (Pos.pow q 2),
    ← Pos.pow_add q 2 2,
    ground.mul_assoc (4 : Pos) (Pos.pow q 2) (Pos.pow p 2 * Pos.pow q 4),
    ground.mul_left_comm (Pos.pow q 2) (Pos.pow p 2) (Pos.pow q 4),
    ← Pos.pow_add q 2 4]

/-- The magnetic second-order clearing at its monomial form. -/
private theorem posB3read (p q : Pos) :
    4 * (q * q) * (p * p) * Pos.pow p 4
      = 4 * (Pos.pow p 6 * Pos.pow q 2) := by
  rw [posSq p, posSq q,
    ground.mul_assoc (4 * Pos.pow q 2) (Pos.pow p 2) (Pos.pow p 4),
    ← Pos.pow_add p 2 4,
    ground.mul_assoc (4 : Pos) (Pos.pow q 2) (Pos.pow p 6),
    ground.mul_comm (Pos.pow q 2) (Pos.pow p 6)]

/-- The residual's magnetic clearing at its monomial form. -/
private theorem posLLread (p q : Pos) :
    4 * (q * q) * Pos.pow p 6 = 4 * (Pos.pow p 6 * Pos.pow q 2) := by
  rw [posSq q, ground.mul_assoc (4 : Pos) (Pos.pow q 2) (Pos.pow p 6),
    ground.mul_comm (Pos.pow q 2) (Pos.pow p 6)]

/-- The residual's first clearing at its monomial form. -/
private theorem posD1read (p q : Pos) :
    q * q * Pos.pow p 6 = Pos.pow p 6 * Pos.pow q 2 := by
  rw [posSq q, ground.mul_comm (Pos.pow q 2) (Pos.pow p 6)]

/-- The jet's first-order clearing at its monomial form. -/
private theorem posJ1read (p q : Pos) :
    Pos.pow p 4 * (p * p * (q * q)) = Pos.pow p 6 * Pos.pow q 2 := by
  rw [posSq p, posSq q,
    ← ground.mul_assoc (Pos.pow p 4) (Pos.pow p 2) (Pos.pow q 2),
    ← Pos.pow_add p 4 2]


/-- Three sited data multiply at the ground product. -/
private theorem ofPos3 (x y z : Pos) :
    (BPair.ofPos x * BPair.ofPos y * BPair.ofPos z).oneValue
      (BPair.ofPos (x * y * z)) :=
  BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofPos_mul x y))
    (BPair.ofPos_mul (x * y) z)

/-- A sited pair's composed weight is the ground product's site. -/
private theorem posPair (a b : Pos) (Z : BPair) :
    (BPair.ofPos a * (BPair.ofPos b * Z)).oneValue
      (BPair.ofPos (a * b) * Z) := by
  rw [← BPair.mul_assoc]
  exact BPair.mul_congr_left (BPair.ofPos_mul a b)

/-- A sited triple's composed weight is the ground product's site. -/
private theorem posTriple (a b c : Pos) (Z : BPair) :
    (BPair.ofPos a * (BPair.ofPos b * (BPair.ofPos c * Z))).oneValue
      (BPair.ofPos (a * (b * c)) * Z) :=
  BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos a)) (posPair b c Z))
    (posPair a (b * c) Z)


/-- A count against a sited clearing's square collects at the clearing's
square and the count's own. -/
private theorem quadTerm (m : Nat) (w : Pos) (k : Nat) (Z : BPair) :
    (BPair.ofNat m * ((BPair.ofPos w * BPair.ofNat k)
        * (BPair.ofPos w * BPair.ofNat k) * Z)).oneValue
      ((BPair.ofNat (m * (k * k)) * Z).scale (w * w)) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat m))
      (BPair.mul_congr_left
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.mul_mul_mul_comm (BPair.ofPos w) (BPair.ofNat k)
              (BPair.ofPos w) (BPair.ofNat k)))
          (BPair.mul_congr (BPair.ofPos_mul w w)
            (BPair.oneValue_symm (BPair.ofNat_mul k k)))))) ?_
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofPos_scale (w * w)
      (BPair.ofNat (m * (k * k)) * Z))) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos (w * w)))
      (BPair.mul_congr_left (BPair.ofNat_mul m (k * k)))) ?_
  rw [BPair.mul_assoc (BPair.ofNat m) (BPair.ofNat (k * k)) Z,
    BPair.mul_left_comm (BPair.ofPos (w * w)) (BPair.ofNat m)
      (BPair.ofNat (k * k) * Z),
    BPair.mul_assoc (BPair.ofPos (w * w)) (BPair.ofNat (k * k)) Z]
  exact BPair.oneValue_refl _

/-- The electric second-order clearing reads the jet level's at four. -/
private theorem sA3 (p q : Pos) :
    (BPair.ofPos (4 * (q * q)) * BPair.ofPos (q * q)
      * BPair.ofPos (Pos.pow p 4)).oneValue
      (BPair.ofPos (Pos.pow p 4 * Pos.pow q 4) * BPair.ofNat 4) := by
  refine BPair.oneValue_trans (ofPos3 (4 * (q * q)) (q * q) (Pos.pow p 4)) ?_
  rw [posA3read p q, ← posT4read p q]
  exact BPair.oneValue_symm (BPair.ofPos_mul (Pos.pow p 4 * Pos.pow q 4) 4)

/-- The magnetic first-order clearing reads the jet level's partner at four. -/
private theorem sB2 (p q : Pos) :
    (BPair.ofPos (4 * (q * q)) * (BPair.ofPos (p * p)).swap
      * BPair.ofPos (p * p * (q * q))).oneValue
      (BPair.ofPos (Pos.pow p 4 * Pos.pow q 4) * BPair.ofNat 4).swap := by
  rw [BPair.mul_swap, BPair.swap_mul]
  refine ground.swap_congr ?_
  refine BPair.oneValue_trans
    (ofPos3 (4 * (q * q)) (p * p) (p * p * (q * q))) ?_
  rw [posB2read p q, ← posT4read p q]
  exact BPair.oneValue_symm (BPair.ofPos_mul (Pos.pow p 4 * Pos.pow q 4) 4)

/-- The magnetic level clearing is the electric first-order's partner. -/
private theorem sB1 (p q : Pos) :
    (BPair.ofPos (4 * (q * q)) * (BPair.ofPos (p * p)).swap
      * BPair.ofPos (Pos.pow q 4)).oneValue
      (BPair.ofPos (4 * (q * q)) * BPair.ofPos (q * q)
        * BPair.ofPos (p * p * (q * q))).swap := by
  rw [BPair.mul_swap, BPair.swap_mul]
  refine ground.swap_congr ?_
  refine BPair.oneValue_trans (ofPos3 (4 * (q * q)) (p * p) (Pos.pow q 4)) ?_
  rw [posB1read p q, ← posA2read p q]
  exact BPair.oneValue_symm (ofPos3 (4 * (q * q)) (q * q) (p * p * (q * q)))

/-- The magnetic second-order clearing is the residual's own. -/
private theorem sB3 (p q : Pos) :
    (BPair.ofPos (4 * (q * q)) * (BPair.ofPos (p * p)).swap
      * BPair.ofPos (Pos.pow p 4)).oneValue
      (BPair.ofPos (4 * (q * q) * Pos.pow p 6)).swap := by
  rw [BPair.mul_swap, BPair.swap_mul]
  refine ground.swap_congr ?_
  refine BPair.oneValue_trans (ofPos3 (4 * (q * q)) (p * p) (Pos.pow p 4)) ?_
  rw [posB3read p q, ← posLLread p q]
  exact BPair.oneValue_refl _

/-- The jet level's partner at the count reads the display's unit weight. -/
private theorem sKK (p q : Pos) (np : Nat) :
    ((BPair.ofPos (Pos.pow p 4 * Pos.pow q 4) * BPair.ofNat np).swap).oneValue
      ((BPair.ofPos (Pos.pow p 4) * BPair.ofNat np).swap
        * BPair.ofPos (Pos.pow q 4)) := by
  rw [BPair.swap_mul]
  refine ground.swap_congr ?_
  rw [BPair.mul_right_comm (BPair.ofPos (Pos.pow p 4)) (BPair.ofNat np)
    (BPair.ofPos (Pos.pow q 4))]
  exact BPair.oneValue_symm
    (BPair.mul_congr_left (BPair.ofPos_mul (Pos.pow p 4) (Pos.pow q 4)))

/-- The residual's first clearing is the jet's first-order partner. -/
private theorem sd1 (p q : Pos) (np : Nat) :
    (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np).oneValue
      (BPair.swap ((BPair.ofPos (Pos.pow p 4) * BPair.ofNat np).swap
        * BPair.ofPos (p * p * (q * q)))) := by
  rw [BPair.swap_mul (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np)
    (BPair.ofPos (p * p * (q * q)))]
  show (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np).oneValue
    (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np
      * BPair.ofPos (p * p * (q * q)))
  rw [BPair.mul_right_comm (BPair.ofPos (Pos.pow p 4)) (BPair.ofNat np)
    (BPair.ofPos (p * p * (q * q))), posD1read p q, ← posJ1read p q]
  exact BPair.oneValue_symm
    (BPair.mul_congr_left (BPair.ofPos_mul (Pos.pow p 4) (p * p * (q * q))))

/-- The residual's second clearing is the jet's second-order partner. -/
private theorem sd3 (p : Pos) (np : Nat) :
    (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np).oneValue
      (BPair.swap ((BPair.ofPos (Pos.pow p 4) * BPair.ofNat np).swap
        * BPair.ofPos (Pos.pow p 4))) := by
  rw [BPair.swap_mul (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np)
    (BPair.ofPos (Pos.pow p 4))]
  show (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np).oneValue
    (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np * BPair.ofPos (Pos.pow p 4))
  rw [BPair.mul_right_comm (BPair.ofPos (Pos.pow p 4)) (BPair.ofNat np)
    (BPair.ofPos (Pos.pow p 4)), posP8 p]
  exact BPair.oneValue_symm
    (BPair.mul_congr_left (BPair.ofPos_mul (Pos.pow p 4) (Pos.pow p 4)))

/-- A clearing passes a three-term combination, weight by weight. -/
private theorem scale_lin3 (c d1 d2 d3 : BPair) (a b e : List BPair) :
    vecScale c (vecAdd (vecScale d1 a) (vecAdd (vecScale d2 b) (vecScale d3 e)))
      = vecAdd (vecScale (c * d1) a)
        (vecAdd (vecScale (c * d2) b) (vecScale (c * d3) e)) := by
  rw [vecScale_vecAdd, vecScale_vecAdd, vecScale_vecScale,
    vecScale_vecScale, vecScale_vecScale]

/-- Six summands regrouped at the second triple's middle member left
standing. -/
private theorem vecRegroupA (x1 x2 x3 y1 y2 y3 : List BPair) :
    vecAdd (vecAdd x1 (vecAdd x2 x3)) (vecAdd y1 (vecAdd y2 y3))
      = vecAdd (vecAdd x1 y2) (vecAdd (vecAdd x2 y1) (vecAdd x3 y3)) := by
  rw [← vecAdd_assoc y1 y2 y3, vecAdd_comm y1 y2, vecAdd_assoc y2 y1 y3,
    vecAdd_add_comm x1 (vecAdd x2 x3) y2 (vecAdd y1 y3),
    vecAdd_add_comm x2 x3 y1 y3]

/-- Six summands regrouped at the second triple's last member left
standing. -/
private theorem vecRegroupB (x1 x2 x3 y1 y2 y3 : List BPair) :
    vecAdd (vecAdd x1 (vecAdd x2 x3)) (vecAdd y1 (vecAdd y2 y3))
      = vecAdd (vecAdd x1 y3) (vecAdd (vecAdd x2 y1) (vecAdd x3 y2)) := by
  rw [← vecAdd_assoc y1 y2 y3, vecAdd_comm (vecAdd y1 y2) y3,
    vecAdd_add_comm x1 (vecAdd x2 x3) y3 (vecAdd y1 y2),
    vecAdd_add_comm x2 x3 y1 y2]

/-- Two clearings at partner weights cancel on one vector. -/
private theorem vecScale_pair_null (c d : BPair) (hcd : d.oneValue c.swap) :
    ∀ v : List BPair, poly.unitTail (vecAdd (vecScale c v) (vecScale d v))
  | [] => trivial
  | x :: t => by
    refine ⟨?_, vecScale_pair_null c d hcd t⟩
    show (c * x + d * x).oneValue BPair.unit
    rw [← BPair.right_distrib]
    refine BPair.oneValue_trans
      (BPair.mul_congr_left
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl c) hcd)
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (BPair.add_comm c c.swap))
            (BPair.swap_add_null (BPair.oneValue_refl c))))) ?_
    exact BPair.unit_mul x

/-- The action passes a three-term combination. -/
private theorem matVec_lin3 (T : Mat) (n : Nat) (hT : rowsLen n T)
    (c1 c2 c3 : BPair) (a b e : List BPair)
    (ha : a.length = n) (hb : b.length = n) (hc : e.length = n) :
    poly.oneValue
      (matVec T (vecAdd (vecScale c1 a) (vecAdd (vecScale c2 b) (vecScale c3 e))))
      (vecAdd (vecScale c1 (matVec T a))
        (vecAdd (vecScale c2 (matVec T b)) (vecScale c3 (matVec T e)))) := by
  have hs : ∀ (c : BPair) (u : List BPair),
      (vecScale c (matVec T u)).length = T.length :=
    fun c u => (length_vecScale c (matVec T u)).trans (matVec_length T u)
  have hla : (vecScale c1 a).length = n := (length_vecScale c1 a).trans ha
  have hlb : (vecScale c2 b).length = n := (length_vecScale c2 b).trans hb
  have hlc : (vecScale c3 e).length = n := (length_vecScale c3 e).trans hc
  have hlbc : (vecAdd (vecScale c2 b) (vecScale c3 e)).length = n :=
    length_vecAdd _ _ n hlb hlc
  refine poly.oneValue_trans (matVec_vecAdd T n hT _ _ hla hlbc) ?_
  refine vecAdd_congr2 _ _ _ _
    ((matVec_length T (vecScale c1 a)).trans (hs c1 a).symm)
    ((matVec_length T (vecAdd (vecScale c2 b) (vecScale c3 e))).trans
      (length_vecAdd (vecScale c2 (matVec T b)) (vecScale c3 (matVec T e))
        T.length (hs c2 b) (hs c3 e)).symm)
    (matVec_vecScale_free T c1 a) ?_
  refine poly.oneValue_trans (matVec_vecAdd T n hT _ _ hlb hlc) ?_
  exact vecAdd_congr2 _ _ _ _
    ((matVec_length T (vecScale c2 b)).trans (hs c2 b).symm)
    ((matVec_length T (vecScale c3 e)).trans (hs c3 e).symm)
    (matVec_vecScale_free T c2 b) (matVec_vecScale_free T c3 e)

/-- The site datum's action splits into the two members' cleared
actions, the second entering as its partner. -/
private theorem site_split {n : Nat} (E M : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (a b : Pos) (v : List BPair) (hv : v.length = n) :
    poly.oneValue (matVec (siteDatum (matScale a E) (matScale b M)) v)
      (vecAdd (vecScale (BPair.ofPos a) (matVec E v))
        (vecScale (BPair.ofPos b).swap (matVec M v))) := by
  have hX : sqAt (matScale a E) n := sqAt_matScale n a E hE
  have hY : sqAt (matSwap (matScale b M)) n :=
    sqAt_matSwap n _ (sqAt_matScale n b M hM)
  have hA : (matVec (matScale a E) v).length
      = (vecScale (BPair.ofPos a) (matVec E v)).length := by
    rw [matVec_length, length_matScale, length_vecScale, matVec_length]
  have hB : (matVec (matSwap (matScale b M)) v).length
      = (vecScale (BPair.ofPos b).swap (matVec M v)).length := by
    rw [matVec_length, length_matSwap, length_matScale, length_vecScale,
      matVec_length]
  refine poly.oneValue_trans
    (matVec_add (matScale a E) (matSwap (matScale b M)) v
      (rowsLen_cast hv.symm (rowsLen_of_sqAt hX))
      (rowsLen_cast hv.symm (rowsLen_of_sqAt hY))) ?_
  refine vecAdd_congr2 _ _ _ _ hA hB (matVec_matScale a E v) ?_
  rw [matVec_swapM, vecScale_swap]
  exact poly.swapMap_oneValue (matVec_matScale b M v)

/-- The cleared site datum against a three-term jet: six cleared
actions, the electric triple joined to the magnetic. -/
private theorem rayLin {n : Nat} (E M : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (a b : Pos) (c d1 d2 d3 : BPair)
    (u v w : List BPair) (hu : u.length = n) (hv : v.length = n)
    (hw : w.length = n) :
    poly.oneValue
      (vecScale c (matVec (siteDatum (matScale a E) (matScale b M))
        (vecAdd (vecScale d1 u) (vecAdd (vecScale d2 v) (vecScale d3 w)))))
      (vecAdd
        (vecAdd (vecScale (c * BPair.ofPos a * d1) (matVec E u))
          (vecAdd (vecScale (c * BPair.ofPos a * d2) (matVec E v))
            (vecScale (c * BPair.ofPos a * d3) (matVec E w))))
        (vecAdd (vecScale (c * (BPair.ofPos b).swap * d1) (matVec M u))
          (vecAdd (vecScale (c * (BPair.ofPos b).swap * d2) (matVec M v))
            (vecScale (c * (BPair.ofPos b).swap * d3) (matVec M w))))) := by
  have lE : ∀ x : List BPair, (matVec E x).length = n :=
    fun x => (matVec_length E x).trans (sqAt_len hE)
  have lM : ∀ x : List BPair, (matVec M x).length = n :=
    fun x => (matVec_length M x).trans (sqAt_len hM)
  have hjl : (vecAdd (vecScale d1 u) (vecAdd (vecScale d2 v)
      (vecScale d3 w))).length = n :=
    length_vecAdd _ _ n ((length_vecScale d1 u).trans hu)
      (length_vecAdd _ _ n ((length_vecScale d2 v).trans hv)
        ((length_vecScale d3 w).trans hw))
  have lenA : (vecScale (BPair.ofPos a)
        (matVec E (vecAdd (vecScale d1 u) (vecAdd (vecScale d2 v)
          (vecScale d3 w))))).length
      = (vecScale (BPair.ofPos a) (vecAdd (vecScale d1 (matVec E u))
          (vecAdd (vecScale d2 (matVec E v))
            (vecScale d3 (matVec E w))))).length :=
    ((length_vecScale _ _).trans (lE _)).trans
      ((length_vecScale _ _).trans
        (length_vecAdd _ _ n ((length_vecScale d1 (matVec E u)).trans (lE u))
          (length_vecAdd _ _ n ((length_vecScale d2 (matVec E v)).trans (lE v))
            ((length_vecScale d3 (matVec E w)).trans (lE w))))).symm
  have lenB : (vecScale (BPair.ofPos b).swap
        (matVec M (vecAdd (vecScale d1 u) (vecAdd (vecScale d2 v)
          (vecScale d3 w))))).length
      = (vecScale (BPair.ofPos b).swap (vecAdd (vecScale d1 (matVec M u))
          (vecAdd (vecScale d2 (matVec M v))
            (vecScale d3 (matVec M w))))).length :=
    ((length_vecScale _ _).trans (lM _)).trans
      ((length_vecScale _ _).trans
        (length_vecAdd _ _ n ((length_vecScale d1 (matVec M u)).trans (lM u))
          (length_vecAdd _ _ n ((length_vecScale d2 (matVec M v)).trans (lM v))
            ((length_vecScale d3 (matVec M w)).trans (lM w))))).symm
  refine poly.oneValue_trans
    (vecScale_oneValue c _ _
      (poly.oneValue_trans (site_split E M hE hM a b _ hjl)
        (vecAdd_congr2 _ _ _ _ lenA lenB
          (vecScale_oneValue (BPair.ofPos a) _ _
            (matVec_lin3 E n (rowsLen_of_sqAt hE) d1 d2 d3 u v w hu hv hw))
          (vecScale_oneValue (BPair.ofPos b).swap _ _
            (matVec_lin3 M n (rowsLen_of_sqAt hM) d1 d2 d3 u v w hu hv hw))))) ?_
  rw [vecScale_vecAdd c, vecScale_vecScale c (BPair.ofPos a),
    vecScale_vecScale c (BPair.ofPos b).swap,
    scale_lin3 (c * BPair.ofPos a) d1 d2 d3 (matVec E u) (matVec E v) (matVec E w),
    scale_lin3 (c * (BPair.ofPos b).swap) d1 d2 d3
      (matVec M u) (matVec M v) (matVec M w)]
  exact poly.oneValue_refl _

/-- The second-order read moved across: at the read `4Eψ₂ + #p𝟏 = 4Mψ₁`
cleared by a weight, the electric term joined to the magnetic
term's partner reads the unit term's own partner. -/
private theorem hE2_move (T : BPair) (E2 M1 onev : List BPair) (np n : Nat)
    (hE2l : E2.length = n) (hM1l : M1.length = n) (honel : onev.length = n)
    (h : poly.oneValue
      (vecAdd (vecScale (BPair.ofNat 4) E2) (vecScale (BPair.ofNat np) onev))
      (vecScale (BPair.ofNat 4) M1)) :
    poly.oneValue
      (vecAdd (vecScale (T * BPair.ofNat 4) E2)
        (vecScale (T * BPair.ofNat 4).swap M1))
      (vecScale (T * BPair.ofNat np).swap onev) := by
  have hsc := vecScale_oneValue T _ _ h
  rw [vecScale_vecAdd, vecScale_vecScale, vecScale_vecScale,
    vecScale_vecScale] at hsc
  have hlU : (vecScale (T * BPair.ofNat 4) E2).length = n :=
    (length_vecScale _ E2).trans hE2l
  have hlV : (vecScale (T * BPair.ofNat np) onev).length = n :=
    (length_vecScale _ onev).trans honel
  have hlR : (vecScale (T * BPair.ofNat 4) M1).length = n :=
    (length_vecScale _ M1).trans hM1l
  have hlUs : ((vecScale (T * BPair.ofNat 4) E2).map BPair.swap).length = n :=
    (ground.length_map BPair.swap _).trans hlU
  have hlmap : ((vecScale (T * BPair.ofNat 4) M1).map BPair.swap).length
      = ((vecAdd (vecScale (T * BPair.ofNat 4) E2)
          (vecScale (T * BPair.ofNat np) onev)).map BPair.swap).length := by
    rw [ground.length_map, ground.length_map, hlR,
      length_vecAdd _ _ n hlU hlV]
  have hlfin : (vecAdd (vecScale (T * BPair.ofNat 4) E2)
        ((vecScale (T * BPair.ofNat 4) E2).map BPair.swap)).length
      = ((vecScale (T * BPair.ofNat np) onev).map BPair.swap).length := by
    rw [ground.length_map, hlV, length_vecAdd _ _ n hlU hlUs]
  rw [vecScale_swap (T * BPair.ofNat 4) M1,
    vecScale_swap (T * BPair.ofNat np) onev]
  refine poly.oneValue_trans
    (vecAdd_congr2 _ _ _ _ rfl hlmap (poly.oneValue_refl _)
      (poly.swapMap_oneValue (poly.oneValue_symm hsc))) ?_
  rw [vecAdd_swapMap, ← vecAdd_assoc]
  exact vecAdd_null_left _ _ hlfin (vecAdd_swap_unitTail _)

/-- The display's six summands collapse: two matched pairs cancel and
the unit and magnetic terms stand. -/
private theorem sixPairs {n : Nat} (onev x y z : List BPair)
    (honev : onev.length = n) (hx : x.length = n) (hy : y.length = n)
    (hz : z.length = n) (a b e f1 f2 f3 : BPair)
    (hb : f1.oneValue b.swap) (he : f3.oneValue e.swap) :
    poly.oneValue
      (vecAdd (vecAdd (vecScale a onev) (vecAdd (vecScale b x) (vecScale e y)))
        (vecAdd (vecScale f1 x) (vecAdd (vecScale f2 z) (vecScale f3 y))))
      (vecAdd (vecScale a onev) (vecScale f2 z)) := by
  have ls : ∀ (c : BPair) (t : List BPair), t.length = n →
      (vecScale c t).length = n := fun c t h => (length_vecScale c t).trans h
  rw [vecRegroupA (vecScale a onev) (vecScale b x) (vecScale e y)
    (vecScale f1 x) (vecScale f2 z) (vecScale f3 y)]
  exact vecAdd_null_right _ _
    ((length_vecAdd _ _ n (ls a onev honev) (ls f2 z hz)).trans
      (length_vecAdd _ _ n
        (length_vecAdd _ _ n (ls b x hx) (ls f1 x hx))
        (length_vecAdd _ _ n (ls e y hy) (ls f3 y hy))).symm)
    (unitTail_vecAdd_of (vecScale_pair_null b f1 hb x)
      (vecScale_pair_null e f3 he y))

/-- The pencil's six cleared actions collapse: the electric unit term
vanishes, the level terms cancel, the second-order pair reads the
unit term and the magnetic second-order term stands. -/
private theorem sixCollapse {n : Nat} (Eo E1 E2 Mo M1 M2 onev : List BPair)
    (hEol : Eo.length = n) (hE1l : E1.length = n) (hE2l : E2.length = n)
    (hMol : Mo.length = n) (hM1l : M1.length = n) (hM2l : M2.length = n)
    (honel : onev.length = n)
    (A1 A2 A3 B1 B2 B3 K L : BPair)
    (hnull : poly.unitTail Eo)
    (hE1M : poly.oneValue E1 Mo)
    (hpair : B1.oneValue A2.swap)
    (hmove : poly.oneValue (vecAdd (vecScale A3 E2) (vecScale B2 M1))
      (vecScale K onev))
    (hB3 : B3.oneValue L) :
    poly.oneValue
      (vecAdd (vecAdd (vecScale A1 Eo) (vecAdd (vecScale A2 E1) (vecScale A3 E2)))
        (vecAdd (vecScale B1 Mo) (vecAdd (vecScale B2 M1) (vecScale B3 M2))))
      (vecAdd (vecScale K onev) (vecScale L M2)) := by
  have ls : ∀ (c : BPair) (t : List BPair), t.length = n →
      (vecScale c t).length = n := fun c t h => (length_vecScale c t).trans h
  have hstep1 : poly.oneValue
      (vecAdd (vecAdd (vecScale A1 Eo) (vecAdd (vecScale A2 E1) (vecScale A3 E2)))
        (vecAdd (vecScale B1 Mo) (vecAdd (vecScale B2 M1) (vecScale B3 M2))))
      (vecAdd (vecAdd (vecScale A1 Eo) (vecAdd (vecScale A2 Mo) (vecScale A3 E2)))
        (vecAdd (vecScale B1 Mo) (vecAdd (vecScale B2 M1) (vecScale B3 M2)))) := by
    refine vecAdd_congr2 _ _ _ _
      ((length_vecAdd _ _ n (ls A1 Eo hEol)
        (length_vecAdd _ _ n (ls A2 E1 hE1l) (ls A3 E2 hE2l))).trans
        (length_vecAdd _ _ n (ls A1 Eo hEol)
          (length_vecAdd _ _ n (ls A2 Mo hMol) (ls A3 E2 hE2l))).symm)
      rfl ?_ (poly.oneValue_refl _)
    exact vecAdd_congr2 _ _ _ _ rfl
      ((length_vecAdd _ _ n (ls A2 E1 hE1l) (ls A3 E2 hE2l)).trans
        (length_vecAdd _ _ n (ls A2 Mo hMol) (ls A3 E2 hE2l)).symm)
      (poly.oneValue_refl _)
      (vecAdd_congr2 _ _ _ _ ((ls A2 E1 hE1l).trans (ls A2 Mo hMol).symm) rfl
        (vecScale_oneValue A2 E1 Mo hE1M) (poly.oneValue_refl _))
  refine poly.oneValue_trans hstep1 ?_
  rw [vecRegroupB (vecScale A1 Eo) (vecScale A2 Mo) (vecScale A3 E2)
    (vecScale B1 Mo) (vecScale B2 M1) (vecScale B3 M2)]
  have hfirst : poly.oneValue (vecAdd (vecScale A1 Eo) (vecScale B3 M2))
      (vecScale L M2) :=
    poly.oneValue_trans
      (vecAdd_null_left _ _ ((ls A1 Eo hEol).trans (ls B3 M2 hM2l).symm)
        (unitTail_vecScale A1 Eo hnull))
      (vecScale_congr hB3 M2)
  have hsecond : poly.oneValue
      (vecAdd (vecAdd (vecScale A2 Mo) (vecScale B1 Mo))
        (vecAdd (vecScale A3 E2) (vecScale B2 M1)))
      (vecScale K onev) :=
    poly.oneValue_trans
      (vecAdd_null_left _ _
        ((length_vecAdd _ _ n (ls A2 Mo hMol) (ls B1 Mo hMol)).trans
          (length_vecAdd _ _ n (ls A3 E2 hE2l) (ls B2 M1 hM1l)).symm)
        (vecScale_pair_null A2 B1 hpair Mo))
      hmove
  refine poly.oneValue_trans
    (vecAdd_congr2 _ _ _ _
      ((length_vecAdd _ _ n (ls A1 Eo hEol) (ls B3 M2 hM2l)).trans
        (ls L M2 hM2l).symm)
      ((length_vecAdd _ _ n
        (length_vecAdd _ _ n (ls A2 Mo hMol) (ls B1 Mo hMol))
        (length_vecAdd _ _ n (ls A3 E2 hE2l) (ls B2 M1 hM1l))).trans
        (ls K onev honel).symm)
      hfirst hsecond) ?_
  exact poly.oneValue_of_eq (vecAdd_comm (vecScale L M2) (vecScale K onev))

/-- The squares' fold twice at a three-term join. -/
private theorem triWeight (a b c : List BPair) (n : Nat)
    (ha : a.length = n) (hb : b.length = n) (hc : c.length = n)
    (X Y Z : BPair)
    (hA : dotN a a ≤ X) (hB : dotN b b ≤ Y) (hC : dotN c c ≤ Z) :
    dotN (vecAdd a (vecAdd b c)) (vecAdd a (vecAdd b c))
      ≤ BPair.ofNat 2 * (BPair.ofNat 2 * (X + Y) + Z) := by
  have hlab : (vecAdd a b).length = n := length_vecAdd a b n ha hb
  rw [← vecAdd_assoc a b c]
  refine ground.leB_trans
    (dotN_vecAdd_sq_le (vecAdd a b) c (hlab.trans hc.symm)) ?_
  refine ground.leB_mulR (ground.unitLeOfNat 2) (ground.leB_add ?_ hC)
  exact ground.leB_trans (dotN_vecAdd_sq_le a b (ha.trans hb.symm))
    (ground.leB_mulR (ground.unitLeOfNat 2) (ground.leB_add hA hB))

/-- The jet's identity at the ray (`lem:fourpoint`'s tail): at the reads
`E𝟏` the null vector, `Eψ₁ = M𝟏` and `4Eψ₂ + #p𝟏 = 4Mψ₁`, the pencil's
site datum reads the jet at its level's multiple joined to the residual,
`H ψ̂ = ε̂ ψ̂ + ρ` at `ε̂` the balance partner of `τ⁴[#p : 4]`, the display
cleared at `4 q⁸`. -/
theorem jetResidual {n : Nat} (E M : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (one psi1 psi2 : List BPair) (h1 : one.length = n) (h2 : psi1.length = n)
    (h3 : psi2.length = n) (np : Nat) (p q : Pos)
    (hE0 : poly.unitTail (matVec E one))
    (hE1 : poly.oneValue (matVec E psi1) (matVec M one))
    (hE2 : poly.oneValue
      (vecAdd (vecScale (BPair.ofNat 4) (matVec E psi2)) (vecScale (BPair.ofNat np) one))
      (vecScale (BPair.ofNat 4) (matVec M psi1))) :
    poly.oneValue
      (vecScale (BPair.ofPos (4 * (q * q))) (matVec (rayH p q E M) (jetVec p q one psi1 psi2)))
      (vecAdd ((vecScale (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np)
          (jetVec p q one psi1 psi2)).map BPair.swap)
        (residVec p q np M psi1 psi2)) := by
  have lE : ∀ x : List BPair, (matVec E x).length = n :=
    fun x => (matVec_length E x).trans (sqAt_len hE)
  have lM : ∀ x : List BPair, (matVec M x).length = n :=
    fun x => (matVec_length M x).trans (sqAt_len hM)
  have hmove : poly.oneValue
      (vecAdd (vecScale (BPair.ofPos (4 * (q * q)) * BPair.ofPos (q * q)
          * BPair.ofPos (Pos.pow p 4)) (matVec E psi2))
        (vecScale (BPair.ofPos (4 * (q * q)) * (BPair.ofPos (p * p)).swap
          * BPair.ofPos (p * p * (q * q))) (matVec M psi1)))
      (vecScale ((BPair.ofPos (Pos.pow p 4) * BPair.ofNat np).swap
        * BPair.ofPos (Pos.pow q 4)) one) := by
    refine poly.oneValue_trans
      (vecAdd_congr2 _ _ _ _
        (((length_vecScale _ (matVec E psi2)).trans (lE psi2)).trans
          ((length_vecScale _ (matVec E psi2)).trans (lE psi2)).symm)
        (((length_vecScale _ (matVec M psi1)).trans (lM psi1)).trans
          ((length_vecScale _ (matVec M psi1)).trans (lM psi1)).symm)
        (vecScale_congr (sA3 p q) (matVec E psi2))
        (vecScale_congr (sB2 p q) (matVec M psi1))) ?_
    refine poly.oneValue_trans
      (hE2_move (BPair.ofPos (Pos.pow p 4 * Pos.pow q 4)) (matVec E psi2)
        (matVec M psi1) one np n (lE psi2) (lM psi1) h1 hE2) ?_
    exact vecScale_congr (sKK p q np) one
  have hcol := sixCollapse (n := n) (matVec E one) (matVec E psi1) (matVec E psi2)
    (matVec M one) (matVec M psi1) (matVec M psi2) one
    (lE one) (lE psi1) (lE psi2) (lM one) (lM psi1) (lM psi2) h1
    (BPair.ofPos (4 * (q * q)) * BPair.ofPos (q * q) * BPair.ofPos (Pos.pow q 4))
    (BPair.ofPos (4 * (q * q)) * BPair.ofPos (q * q) * BPair.ofPos (p * p * (q * q)))
    (BPair.ofPos (4 * (q * q)) * BPair.ofPos (q * q) * BPair.ofPos (Pos.pow p 4))
    (BPair.ofPos (4 * (q * q)) * (BPair.ofPos (p * p)).swap * BPair.ofPos (Pos.pow q 4))
    (BPair.ofPos (4 * (q * q)) * (BPair.ofPos (p * p)).swap
      * BPair.ofPos (p * p * (q * q)))
    (BPair.ofPos (4 * (q * q)) * (BPair.ofPos (p * p)).swap * BPair.ofPos (Pos.pow p 4))
    ((BPair.ofPos (Pos.pow p 4) * BPair.ofNat np).swap * BPair.ofPos (Pos.pow q 4))
    (BPair.ofPos (4 * (q * q) * Pos.pow p 6)).swap
    hE0 hE1 (sB1 p q) hmove (sB3 p q)
  have hL := poly.oneValue_trans
    (rayLin E M hE hM (q * q) (p * p) (BPair.ofPos (4 * (q * q)))
      (BPair.ofPos (Pos.pow q 4)) (BPair.ofPos (p * p * (q * q)))
      (BPair.ofPos (Pos.pow p 4)) one psi1 psi2 h1 h2 h3) hcol
  have hrhs : poly.oneValue
      (vecAdd ((vecScale (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np)
          (vecAdd (vecScale (BPair.ofPos (Pos.pow q 4)) one)
            (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
              (vecScale (BPair.ofPos (Pos.pow p 4)) psi2)))).map BPair.swap)
        (vecAdd (vecScale (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np) psi1)
          (vecAdd ((vecScale (BPair.ofPos (4 * (q * q) * Pos.pow p 6))
              (matVec M psi2)).map BPair.swap)
            (vecScale (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np) psi2))))
      (vecAdd (vecScale ((BPair.ofPos (Pos.pow p 4) * BPair.ofNat np).swap
          * BPair.ofPos (Pos.pow q 4)) one)
        (vecScale (BPair.ofPos (4 * (q * q) * Pos.pow p 6)).swap
          (matVec M psi2))) := by
    rw [← vecScale_swap (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np)
        (vecAdd (vecScale (BPair.ofPos (Pos.pow q 4)) one)
          (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
            (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))),
      ← vecScale_swap (BPair.ofPos (4 * (q * q) * Pos.pow p 6)) (matVec M psi2),
      scale_lin3 (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np).swap
        (BPair.ofPos (Pos.pow q 4)) (BPair.ofPos (p * p * (q * q)))
        (BPair.ofPos (Pos.pow p 4)) one psi1 psi2]
    exact sixPairs (n := n) one psi1 psi2 (matVec M psi2) h1 h2 h3 (lM psi2)
      _ _ _ _ _ _ (sd1 p q np) (sd3 p np)
  exact poly.oneValue_trans hL (poly.oneValue_symm hrhs)

/-- The solve floor (`lem:fourpoint`'s tail): at the second-order solve's
floor `ℓ⟨ψ₂,ψ₂⟩ ≤ ⟨ψ₂,Eψ₂⟩`, the read `4Eψ₂ + #p𝟏 = 4Mψ₁` with `ψ₂` off
the unit line, and the magnetic member's square cap `W`, the squared
Cauchy–Schwarz reads `ℓ²⟨ψ₂,ψ₂⟩ ≤ W²⟨ψ₁,ψ₁⟩`. -/
theorem solveFloor {n : Nat} (E M : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (one psi1 psi2 : List BPair) (h1 : one.length = n) (h2 : psi1.length = n)
    (h3 : psi2.length = n) (np : Nat)
    (hE2 : poly.oneValue
      (vecAdd (vecScale (BPair.ofNat 4) (matVec E psi2)) (vecScale (BPair.ofNat np) one))
      (vecScale (BPair.ofNat 4) (matVec M psi1)))
    (hperp : (dotN psi2 one).oneValue BPair.unit)
    (ln ld : Pos) (hfloor : (dotN psi2 psi2).scale ln ≤ (quadForm E psi2).scale ld)
    (W : Pos) (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL) :
    (dotN psi2 psi2).scale (ln * ln)
      ≤ (BPair.ofPos (W * W) * dotN psi1 psi1).scale (ld * ld) := by
  have hlE : (vecScale (BPair.ofNat 4) (matVec E psi2)).length = psi2.length := by
    rw [length_vecScale, matVec_length, sqAt_len hE, h3]
  have hlo : (vecScale (BPair.ofNat np) one).length = psi2.length := by
    rw [length_vecScale, h1, h3]
  have hEM : (quadForm E psi2).oneValue (dotN psi2 (matVec M psi1)) := by
    refine ground.mulCancel (c := BPair.ofNat 4)
      (BPair.ofNat_off_unit 4 (Nat.succ_pos 3)) ?_
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_trans (dotN_congrR psi2 _ _ hE2)
        (dotN_scaleV (BPair.ofNat 4) psi2 (matVec M psi1)))
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (dotN_addRow_right psi2 (vecScale (BPair.ofNat 4) (matVec E psi2))
        (vecScale (BPair.ofNat np) one) hlE hlo) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (dotN_scaleV (BPair.ofNat 4) psi2 (matVec E psi2))
        (BPair.oneValue_trans
          (dotN_scaleV (BPair.ofNat np) psi2 one)
          (BPair.oneValue_trans
            (BPair.mul_congr (BPair.oneValue_refl (BPair.ofNat np)) hperp)
            (BPair.mul_unit (BPair.ofNat np))))) ?_
    exact BPair.add_unit _
  have hQ2 : BPair.unit ≤ dotN psi2 psi2 :=
    ground.leB_of_not_lt (dotN_self_side psi2)
  have hQ1 : BPair.unit ≤ dotN psi1 psi1 :=
    ground.leB_of_not_lt (dotN_self_side psi1)
  have hcap' : dotN (matVec M psi1) (matVec M psi1)
      ≤ BPair.ofPos (W * W) * dotN psi1 psi1 :=
    inertia.cap_vec M hM W spU spL hcapM psi1 h2
  have hcs : dotN psi2 (matVec M psi1) * dotN psi2 (matVec M psi1)
      ≤ dotN psi2 psi2 * (BPair.ofPos (W * W) * dotN psi1 psi1) :=
    ground.leB_trans
      (coeff.dotN_sq_le psi2 (matVec M psi1)
        (h3.trans ((matVec_length M psi1).trans (sqAt_len hM)).symm))
      (ground.leB_mulR hQ2 hcap')
  have hX : (dotN psi2 psi2).scale ln
      ≤ (dotN psi2 (matVec M psi1)).scale ld :=
    ground.leB_congr_right (BPair.scale_congr ld hEM) hfloor
  have hunitX : BPair.unit ≤ (dotN psi2 psi2).scale ln :=
    ground.leB_congr_left (BPair.oneValue_symm (ground.unitScale ln))
      (ground.leB_scale hQ2 ln)
  have hsq : (dotN psi2 psi2).scale ln * (dotN psi2 psi2).scale ln
      ≤ (dotN psi2 (matVec M psi1)).scale ld
        * (dotN psi2 (matVec M psi1)).scale ld :=
    ground.leB_mul_mono hunitX (ground.leB_trans hunitX hX) hX hX
  have hchain : (dotN psi2 psi2 * dotN psi2 psi2).scale (ln * ln)
      ≤ (dotN psi2 psi2 * (BPair.ofPos (W * W) * dotN psi1 psi1)).scale (ld * ld) := by
    rw [BPair.scale_mul (dotN psi2 psi2) (dotN psi2 psi2) ln ln]
    refine ground.leB_trans hsq ?_
    rw [← BPair.scale_mul (dotN psi2 (matVec M psi1))
      (dotN psi2 (matVec M psi1)) ld ld]
    exact ground.leB_scale hcs (ld * ld)
  rw [← BPair.mul_scale (dotN psi2 psi2) (dotN psi2 psi2) (ln * ln),
    ← BPair.mul_scale (dotN psi2 psi2)
      (BPair.ofPos (W * W) * dotN psi1 psi1) (ld * ld)] at hchain
  match hQ2 with
  | Or.inr hlt => exact ground.leB_unscale_left hlt hchain
  | Or.inl he =>
    refine ground.leB_congr_left (BPair.scale_congr (ln * ln) he) ?_
    refine ground.leB_congr_left (ground.unitScale (ln * ln)) ?_
    exact ground.leB_congr_left
      (BPair.oneValue_symm (ground.unitScale (ld * ld)))
      (ground.leB_scale
        (ground.unitLeMul (ground.leB_of_lt (ground.unitLtOfPos (W * W))) hQ1)
        (ld * ld))

/-- The residual's weight (`lem:fourpoint`'s tail): the squares' fold twice
at the residual's three terms with the magnetic member's square cap,
`⟨ρ,ρ⟩ ≤ τ¹²(4[#p:4]²⟨ψ₁,ψ₁⟩ + 4W²⟨ψ₂,ψ₂⟩ + 2τ⁴[#p:4]²⟨ψ₂,ψ₂⟩)` cleared at
`16 q¹⁶`. -/
theorem residWeight {n : Nat} (M : Mat) (hM : sqAt M n) (psi1 psi2 : List BPair)
    (h2 : psi1.length = n) (h3 : psi2.length = n) (np : Nat) (p q : Pos)
    (W : Pos) (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL) :
    dotN (residVec p q np M psi1 psi2) (residVec p q np M psi1 psi2)
      ≤ (BPair.ofNat (4 * (np * np)) * dotN psi1 psi1).scale (Pos.pow q 4 * Pos.pow p 12)
        + (BPair.ofPos (64 * (W * W)) * dotN psi2 psi2).scale (Pos.pow q 4 * Pos.pow p 12)
        + (BPair.ofNat (2 * (np * np)) * dotN psi2 psi2).scale (Pos.pow p 16) := by
  have hlM2 : (matVec M psi2).length = n :=
    (matVec_length M psi2).trans (sqAt_len hM)
  have hlA : (vecScale (BPair.ofPos (q * q * Pos.pow p 6)
      * BPair.ofNat np) psi1).length = n := by
    rw [length_vecScale]; exact h2
  have hlB : ((vecScale (BPair.ofPos (4 * (q * q) * Pos.pow p 6))
      (matVec M psi2)).map BPair.swap).length = n := by
    rw [ground.length_map, length_vecScale]; exact hlM2
  have hlC : (vecScale (BPair.ofPos (Pos.pow p 8)
      * BPair.ofNat np) psi2).length = n := by
    rw [length_vecScale]; exact h3
  have hAle : dotN (vecScale (BPair.ofPos (q * q * Pos.pow p 6)
        * BPair.ofNat np) psi1)
      (vecScale (BPair.ofPos (q * q * Pos.pow p 6)
        * BPair.ofNat np) psi1)
      ≤ (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * dotN psi1 psi1 :=
    ground.leB_congr_right (dotN_vecScale_self _ psi1) (ground.leB_refl _)
  have hCle : dotN (vecScale (BPair.ofPos (Pos.pow p 8)
        * BPair.ofNat np) psi2)
      (vecScale (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np) psi2)
      ≤ (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np)
        * (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np)
        * dotN psi2 psi2 :=
    ground.leB_congr_right (dotN_vecScale_self _ psi2) (ground.leB_refl _)
  have hBle : dotN ((vecScale (BPair.ofPos (4 * (q * q) * Pos.pow p 6))
        (matVec M psi2)).map BPair.swap)
      ((vecScale (BPair.ofPos (4 * (q * q) * Pos.pow p 6))
        (matVec M psi2)).map BPair.swap)
      ≤ BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * (BPair.ofPos (W * W) * dotN psi2 psi2) := by
    rw [dotN_swapPair]
    exact ground.leB_congr_left
      (BPair.oneValue_symm (dotN_vecScale_self _ (matVec M psi2)))
      (ground.leB_mulR
        (ground.unitLeSq (BPair.ofPos (4 * (q * q) * Pos.pow p 6)))
        (inertia.cap_vec M hM W spU spL hcapM psi2 h3))
  refine ground.leB_trans
    (triWeight _ _ _ n hlA hlB hlC _ _ _ hAle hBle hCle) ?_
  have hT1 : (BPair.ofNat 2 * (BPair.ofNat 2
        * ((BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
          * (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
          * dotN psi1 psi1))).oneValue
      ((BPair.ofNat (4 * (np * np)) * dotN psi1 psi1).scale
        (Pos.pow q 4 * Pos.pow p 12)) := by
    rw [← posU2 p q]
    exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofNat_mul_mul 2 2 _))
      (quadTerm 4 (q * q * Pos.pow p 6) np (dotN psi1 psi1))
  have hT3 : (BPair.ofNat 2
        * ((BPair.ofPos (Pos.pow p 8) * BPair.ofNat np)
          * (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np)
          * dotN psi2 psi2)).oneValue
      ((BPair.ofNat (2 * (np * np)) * dotN psi2 psi2).scale
        (Pos.pow p 16)) := by
    rw [← posP16 p]
    exact quadTerm 2 (Pos.pow p 8) np (dotN psi2 psi2)
  have hT2 : (BPair.ofNat 2 * (BPair.ofNat 2
        * (BPair.ofPos (4 * (q * q) * Pos.pow p 6)
          * BPair.ofPos (4 * (q * q) * Pos.pow p 6)
          * (BPair.ofPos (W * W) * dotN psi2 psi2)))).oneValue
      ((BPair.ofPos (64 * (W * W)) * dotN psi2 psi2).scale
        (Pos.pow q 4 * Pos.pow p 12)) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofNat_mul_mul 2 2 _)) ?_
    show (BPair.ofPos 4 * (BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * (BPair.ofPos (W * W) * dotN psi2 psi2))).oneValue _
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl (BPair.ofPos 4))
        (BPair.mul_congr_left
          (BPair.ofPos_mul (4 * (q * q) * Pos.pow p 6)
            (4 * (q * q) * Pos.pow p 6)))) ?_
    rw [posV2 p q]
    refine BPair.oneValue_trans
      (posTriple 4 (16 * (Pos.pow q 4 * Pos.pow p 12)) (W * W)
        (dotN psi2 psi2)) ?_
    rw [posMix (Pos.pow q 4 * Pos.pow p 12) W]
    exact BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.ofPos_scale
          (Pos.pow q 4 * Pos.pow p 12)
          (BPair.ofPos (64 * (W * W)) * dotN psi2 psi2)))
        (posPair (Pos.pow q 4 * Pos.pow p 12) (64 * (W * W))
          (dotN psi2 psi2)))
  refine ground.leB_congr_right ?_ (ground.leB_refl _)
  rw [BPair.left_distrib (BPair.ofNat 2)
      (BPair.ofNat 2 * ((BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * dotN psi1 psi1
        + BPair.ofPos (4 * (q * q) * Pos.pow p 6)
          * BPair.ofPos (4 * (q * q) * Pos.pow p 6)
          * (BPair.ofPos (W * W) * dotN psi2 psi2)))
      ((BPair.ofPos (Pos.pow p 8) * BPair.ofNat np)
        * (BPair.ofPos (Pos.pow p 8) * BPair.ofNat np)
        * dotN psi2 psi2),
    BPair.left_distrib (BPair.ofNat 2)
      ((BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * dotN psi1 psi1)
      (BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * (BPair.ofPos (W * W) * dotN psi2 psi2)),
    BPair.left_distrib (BPair.ofNat 2)
      (BPair.ofNat 2 * ((BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * (BPair.ofPos (q * q * Pos.pow p 6) * BPair.ofNat np)
        * dotN psi1 psi1))
      (BPair.ofNat 2 * (BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * BPair.ofPos (4 * (q * q) * Pos.pow p 6)
        * (BPair.ofPos (W * W) * dotN psi2 psi2)))]
  exact BPair.add_congr (BPair.add_congr hT1 hT2) hT3


/-! The ground's gap from the jet: the transport display's pairing
step at the level gap's clearance less the drift, the drift floored
at the magnetic cap through the ground's own Rayleigh read. -/

/-- Four factors, the outer one moved past the middle pair. -/
private theorem m4 (x y z w : BPair) :
    x * (y * (z * w)) = y * z * (x * w) := by
  rw [BPair.mul_left_comm x y (z * w), BPair.mul_left_comm x z w,
    ← BPair.mul_assoc y z (x * w)]

/-- Four factors, the two middle ones exchanged. -/
private theorem m4' (x y z w : BPair) :
    x * (y * (z * w)) = x * z * (y * w) := by
  rw [BPair.mul_left_comm y z w, ← BPair.mul_assoc x z (y * w)]

/-- The squared comparison at the perpendicular part: a comparison
between two members at or above the sum's unit squares, the pairing's
square passes the Cauchy read, and one self-pairing cancels. -/
private theorem sqStep {X Y f pr r : BPair}
    (hf : BPair.unit ≤ f) (hX : BPair.unit ≤ X) (hr : BPair.unit ≤ r)
    (hcs : ¬ (f * r < pr * pr))
    (h : X * f ≤ Y * pr) :
    X * X * f ≤ Y * Y * r := by
  have hXf : BPair.unit ≤ X * f := ground.unitLeMul hX hf
  have hYpr : BPair.unit ≤ Y * pr := ground.leB_trans hXf h
  have hsq : (X * f) * (X * f) ≤ (Y * pr) * (Y * pr) :=
    ground.leB_mul_mono hXf hYpr h h
  have hstep : (Y * pr) * (Y * pr) ≤ (Y * Y) * (f * r) := by
    rw [BPair.mul_mul_mul_comm Y pr Y pr]
    exact ground.leB_mulR (ground.unitLeSq Y) (ground.leB_of_not_lt hcs)
  have e1 : (X * f) * (X * f) = (X * X * f) * f := by
    rw [BPair.mul_mul_mul_comm X f X f, ← BPair.mul_assoc (X * X) f f]
  have e2 : (Y * Y) * (f * r) = (Y * Y * r) * f := by
    rw [BPair.mul_comm f r, ← BPair.mul_assoc (Y * Y) r f]
  have hall : (X * X * f) * f ≤ (Y * Y * r) * f :=
    ground.leB_congr (BPair.oneValue_of_eq e1) (BPair.oneValue_of_eq e2)
      (ground.leB_trans hsq hstep)
  have hf' : BPair.unit.oneValue f ∨ BPair.unit < f := hf
  match hf' with
  | Or.inl he =>
    refine ground.leB_congr_left ?_
      (ground.unitLeMul (ground.unitLeSq Y) hr)
    exact BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl (X * X)) (BPair.oneValue_symm he))
        (BPair.mul_unit (X * X)))
  | Or.inr hlt => exact ground.leB_unscale hlt hall

/-- The tie's algebra: the cleared pencil's form against the jet, the
residual read substituted and the self-pairing's solve folded in. -/
private theorem tieAlg {Q cB e0 a s pv pj pr f QF : BPair}
    (hQF : QF.oneValue (s * (cB * pv + (e0 * pj).swap)))
    (hrs : (Q * pv).oneValue ((a * pj).swap + pr))
    (hsf : (s * pj).oneValue f) :
    (Q * QF).oneValue (cB * s * pr + ((cB * a + Q * e0) * f).swap) := by
  have e1 : Q * (s * (cB * pv + (e0 * pj).swap))
      = s * (cB * (Q * pv)) + (Q * e0 * (s * pj)).swap := by
    rw [BPair.left_distrib s (cB * pv) ((e0 * pj).swap),
      BPair.left_distrib Q (s * (cB * pv)) (s * (e0 * pj).swap),
      BPair.mul_swap s (e0 * pj), BPair.mul_swap Q (s * (e0 * pj)),
      BPair.mul_left_comm Q s (cB * pv), BPair.mul_left_comm Q cB pv,
      m4' Q s e0 pj]
  have e2 : s * (cB * ((a * pj).swap + pr))
      = (cB * a * (s * pj)).swap + cB * s * pr := by
    rw [BPair.left_distrib cB ((a * pj).swap) pr,
      BPair.mul_swap cB (a * pj),
      BPair.left_distrib s ((cB * (a * pj)).swap) (cB * pr),
      BPair.mul_swap s (cB * (a * pj)), m4 s cB a pj,
      BPair.mul_left_comm s cB pr, ← BPair.mul_assoc cB s pr]
  have h1 : (Q * QF).oneValue (s * (cB * (Q * pv)) + (Q * e0 * (s * pj)).swap) :=
    BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl Q) hQF)
      (BPair.oneValue_of_eq e1)
  have h2 : (s * (cB * (Q * pv))).oneValue
      ((cB * a * (s * pj)).swap + cB * s * pr) :=
    BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl s)
        (BPair.mul_congr (BPair.oneValue_refl cB) hrs))
      (BPair.oneValue_of_eq e2)
  refine BPair.oneValue_trans
    (BPair.oneValue_trans h1 (BPair.add_congr h2 (BPair.oneValue_refl _))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr
        (ground.swap_congr
          (BPair.mul_congr (BPair.oneValue_refl (cB * a)) hsf))
        (BPair.oneValue_refl (cB * s * pr)))
      (ground.swap_congr
        (BPair.mul_congr (BPair.oneValue_refl (Q * e0)) hsf))) ?_
  refine BPair.oneValue_of_eq ?_
  rw [BPair.add_right_comm ((cB * a * f).swap) (cB * s * pr) ((Q * e0 * f).swap),
    BPair.swap_add (cB * a * f) (Q * e0 * f),
    ← BPair.right_distrib (cB * a) (Q * e0) f,
    BPair.add_comm (((cB * a + Q * e0) * f).swap) (cB * s * pr)]

/-- The drift's close at the balance carrier: the cleared pencil's
comparison with the residual read folded in, the drift floor beneath
the clearance and the Cauchy read at the residual, the whole
squared. -/
private theorem driftClose {Q gnB gdB cB Vb a e0 s pv pj pr f r QF : BPair}
    (hQpos : BPair.unit ≤ Q) (hfpos : BPair.unit ≤ f)
    (hrpos : BPair.unit ≤ r) (hDpos : BPair.unit ≤ gnB + Vb.swap)
    (hQFr : QF.oneValue (s * (cB * pv + (e0 * pj).swap)))
    (hrs : (Q * pv).oneValue ((a * pj).swap + pr))
    (hsf : (s * pj).oneValue f)
    (hgap2 : gnB * f ≤ gdB * QF)
    (hfl : (Q * Vb).swap ≤ gdB * (cB * a + Q * e0))
    (hcs : ¬ (f * r < pr * pr)) :
    Q * (gnB + Vb.swap) * (Q * (gnB + Vb.swap)) * f
      ≤ gdB * cB * s * (gdB * cB * s) * r := by
  have htie2 := tieAlg hQFr hrs hsf
  have h1 : Q * gnB * f
      ≤ gdB * (cB * s * pr) + (gdB * ((cB * a + Q * e0) * f)).swap := by
    refine ground.leB_congr
      (BPair.oneValue_of_eq (BPair.mul_assoc Q gnB f).symm) ?_
      (ground.leB_mulR hQpos hgap2)
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm Q gdB QF)) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl gdB) htie2) ?_
    exact BPair.oneValue_of_eq (by rw [BPair.left_distrib, BPair.mul_swap])
  have h2 := ground.leB_swapR h1
  have hstar : (Q * gnB + gdB * (cB * a + Q * e0)) * f
      ≤ gdB * cB * s * pr := by
    refine ground.leB_congr (BPair.oneValue_of_eq ?_)
      (BPair.oneValue_of_eq ?_) h2
    · rw [BPair.right_distrib (Q * gnB) (gdB * (cB * a + Q * e0)) f,
        BPair.mul_assoc gdB (cB * a + Q * e0) f]
    · rw [← BPair.mul_assoc gdB (cB * s) pr, ← BPair.mul_assoc gdB cB s]
  have hfloor : Q * (gnB + Vb.swap) ≤ Q * gnB + gdB * (cB * a + Q * e0) := by
    refine ground.leB_congr_left (BPair.oneValue_of_eq ?_)
      (ground.leB_add (ground.leB_refl (Q * gnB)) hfl)
    rw [← BPair.mul_swap Q Vb, ← BPair.left_distrib Q gnB Vb.swap]
  have hXpos : BPair.unit ≤ Q * (gnB + Vb.swap) := ground.unitLeMul hQpos hDpos
  have hXf : Q * (gnB + Vb.swap) * f ≤ gdB * cB * s * pr :=
    ground.leB_trans
      (ground.leB_mul_mono hfpos (ground.leB_trans hXpos hfloor) hfloor
        (ground.leB_refl f)) hstar
  exact sqStep hfpos hXpos hrpos hcs hXf


/-- The ground's gap from the jet at the drift (`lem:fourpoint`'s tail): at
the level gap diagonalized with the kernel root at the ground column and the
clearance `[gn : gd]` beyond every further root, the gap the cleared pencil's
own at the level `e₀` (`Et = c·rayH − e₀·I`), the electric member positive
semidefinite, the magnetic member at the square cap `W`, and a vector `J`
solving the ray's pencil to a residual `R` at the jet level's read
(`4q²·rayH·J = −#p p⁴ J + R`), the jet's part off the ground's line is priced
by the residual at the clearance less the drift, `τ²W` below `γ'`:
`⟨γ' : τ²W⟩² ⟨φ,φ⟩ ≤ ⟨ρ,ρ⟩`, the display cleared. -/
theorem offLine_drift {n : Nat} (E M Et : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (T Tw : SqMat n) (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0 = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : groundreads.clearRead l j0 gn gd)
    (p q c : Pos) (e0 : BPair)
    (htie : matOneValue Et
      (siteDatum (matScale c (rayH p q E M)) (matScaleB e0 (idMat n))))
    (spE : Split n) (hEs : splitRead E spE) (hEp : psdAt spE)
    (W : Pos) (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL)
    (np : Nat) (J R : List BPair) (hJ : J.length = n) (hR : R.length = n)
    (hres : poly.oneValue (vecScale (BPair.ofPos (4 * (q * q))) (matVec (rayH p q E M) J))
      (vecAdd ((vecScale (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np) J).map BPair.swap) R))
    (hside : BPair.ofPos (gd * c * (p * p) * W) < BPair.ofPos gn) :
    ((BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap)
        * (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap)
        * dotN (residD [matVec T.val (elim.idRow n j0)] J)
            (residD [matVec T.val (elim.idRow n j0)] J)).scale (16 * Pos.pow q 4)
      ≤ (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN R R).scale (gd * gd * (c * c)) := by
  have hTl : T.val.length = n := SqMat.rows T
  have hpsi : (matVec T.val (elim.idRow n j0)).length = n := by
    rw [matVec_length]; exact hTl
  have hEtsq : sqAt Et n := hd.1
  have hEtl : Et.length = n := sqAt_len hEtsq
  have hEtr : rowsLen n Et := rowsLen_of_sqAt hEtsq
  have hMr : rowsLen n M := rowsLen_of_sqAt hM
  have hMl : M.length = n := sqAt_len hM
  have hray : sqAt (rayH p q E M) n :=
    sqAt_siteDatum n _ _ (sqAt_matScale n (q * q) E hE)
      (sqAt_matScale n (p * p) M hM)
  have hphi : (residD [matVec T.val (elim.idRow n j0)] J).length = n :=
    length_residD n [matVec T.val (elim.idRow n j0)] J ⟨hpsi, trivial⟩ hJ
  obtain ⟨hker, _, hs⟩ :=
    groundreads.ground_column Et T Tw l hd j0 hj0 d0 g0 hroot0
  obtain ⟨hr1, _⟩ :=
    groundreads.offLine_reads (matVec T.val (elim.idRow n j0)) J n hpsi hJ

  have hvJ : ∀ x : BPair, (vecScale x J).length = n := fun x => by
    rw [length_vecScale, hJ]
  have hvP : ∀ x : BPair,
      ((vecScale x (matVec T.val (elim.idRow n j0))).map BPair.swap).length = n :=
    fun x => by rw [ground.length_map, length_vecScale, hpsi]
  have hperp : (dotN (matVec T.val (elim.idRow n j0))
      (residD [matVec T.val (elim.idRow n j0)] J)).oneValue BPair.unit := by
    refine BPair.oneValue_trans
      (dotN_congrR (matVec T.val (elim.idRow n j0)) _ _ hr1) ?_
    refine BPair.oneValue_trans
      (dotN_addRow_right (matVec T.val (elim.idRow n j0)) _ _
        ((hvJ _).trans hpsi.symm) ((hvP _).trans hpsi.symm)) ?_
    rw [dotN_swap (matVec T.val (elim.idRow n j0))
      (vecScale (dotN (matVec T.val (elim.idRow n j0)) J)
        (matVec T.val (elim.idRow n j0)))]
    refine BPair.oneValue_trans
      (BPair.add_congr (dotN_scaleV _ _ _)
        (ground.swap_congr (dotN_scaleV _ _ _))) ?_
    rw [BPair.mul_comm (dotN (matVec T.val (elim.idRow n j0)) J)
      (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))),
      BPair.add_comm]
    exact BPair.swap_add_null (BPair.oneValue_refl _)
  have hperp' : (dotN (residD [matVec T.val (elim.idRow n j0)] J)
      (matVec T.val (elim.idRow n j0))).oneValue BPair.unit :=
    BPair.oneValue_trans
      (dotN_comm (residD [matVec T.val (elim.idRow n j0)] J)
        (matVec T.val (elim.idRow n j0))) hperp
  have hsf : (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0))
      * dotN (residD [matVec T.val (elim.idRow n j0)] J) J).oneValue
      (dotN (residD [matVec T.val (elim.idRow n j0)] J)
        (residD [matVec T.val (elim.idRow n j0)] J)) := by
    refine BPair.oneValue_symm ?_
    refine BPair.oneValue_trans
      (dotN_congrR (residD [matVec T.val (elim.idRow n j0)] J) _ _ hr1) ?_
    refine BPair.oneValue_trans
      (dotN_addRow_right (residD [matVec T.val (elim.idRow n j0)] J) _ _
        ((hvJ _).trans hphi.symm) ((hvP _).trans hphi.symm)) ?_
    rw [dotN_swap (residD [matVec T.val (elim.idRow n j0)] J)
      (vecScale (dotN (matVec T.val (elim.idRow n j0)) J)
        (matVec T.val (elim.idRow n j0)))]
    refine BPair.oneValue_trans
      (BPair.add_congr (dotN_scaleV _ _ _)
        (ground.swap_congr (dotN_scaleV _ _ _))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (ground.swap_congr (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hperp')
          (BPair.mul_unit _)))) ?_
    exact BPair.add_unit _
  have hgap := groundreads.gap_perp Et T Tw l hd j0 hj0 d0 g0 hroot0 gn gd hcl
    (residD [matVec T.val (elim.idRow n j0)] J) hphi hperp

  have hIsq : sqAt (idMat n) n := inertia.sqAt_idMat n
  have hnull : (dotN (residD [matVec T.val (elim.idRow n j0)] J)
      (matVec Et (matVec T.val (elim.idRow n j0)))).oneValue BPair.unit :=
    BPair.oneValue_trans (dotN_read _ _) (dotP_null_tail_right _ _ hker)
  have hEphi : poly.oneValue
      (matVec Et (residD [matVec T.val (elim.idRow n j0)] J))
      (vecAdd
        (vecScale (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))) (matVec Et J))
        ((vecScale (dotN (matVec T.val (elim.idRow n j0)) J)
          (matVec Et (matVec T.val (elim.idRow n j0)))).map BPair.swap)) := by
    refine poly.oneValue_trans (matVec_congr Et _ _ hr1) ?_
    refine poly.oneValue_trans
      (matVec_vecAdd Et n hEtr _ _ (hvJ _) (hvP _)) ?_
    refine elim.vecAdd_congr2 _ _ _ _
      (by rw [matVec_length, length_vecScale, matVec_length])
      (by rw [matVec_length, ground.length_map, length_vecScale,
        matVec_length])
      (matVec_vecScale_free Et _ J) ?_
    rw [matVec_swapArg
      (vecScale (dotN (matVec T.val (elim.idRow n j0)) J)
        (matVec T.val (elim.idRow n j0))) Et]
    exact poly.swapMap_oneValue (matVec_vecScale_free Et _ _)
  have hQF : (inertia.quadForm Et (residD [matVec T.val (elim.idRow n j0)] J)).oneValue
      (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
        * dotN (residD [matVec T.val (elim.idRow n j0)] J) (matVec Et J)) := by
    refine BPair.oneValue_trans (dotN_congrR _ _ _ hEphi) ?_
    refine BPair.oneValue_trans
      (dotN_addRow_right _ _ _
        (by rw [length_vecScale, matVec_length, hEtl, hphi])
        (by rw [ground.length_map, length_vecScale, matVec_length, hEtl,
          hphi])) ?_
    rw [dotN_swap (residD [matVec T.val (elim.idRow n j0)] J)
      (vecScale (dotN (matVec T.val (elim.idRow n j0)) J)
        (matVec Et (matVec T.val (elim.idRow n j0))))]
    refine BPair.oneValue_trans
      (BPair.add_congr (dotN_scaleV _ _ _)
        (ground.swap_congr (dotN_scaleV _ _ _))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (ground.swap_congr (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _) hnull)
          (BPair.mul_unit _)))) ?_
    exact BPair.add_unit _
  have hEtJ : poly.oneValue (matVec Et J)
      (vecAdd (vecScale (BPair.ofPos c) (matVec (rayH p q E M) J))
        ((vecScale e0 J).map BPair.swap)) := by
    refine poly.oneValue_trans (matVec_matOne Et _ J htie) ?_
    refine poly.oneValue_trans
      (matVec_add (matScale c (rayH p q E M))
        (matSwap (matScaleB e0 (idMat n))) J
        (by rw [hJ]; exact rowsLen_of_sqAt (sqAt_matScale n c _ hray))
        (by rw [hJ]
            exact rowsLen_of_sqAt (elim.sqAt_matSwap n _
              (sqAt_scaleB e0 n (idMat n) hIsq)))) ?_
    rw [matVec_swapM (matScaleB e0 (idMat n)) J]
    refine elim.vecAdd_congr2 _ _ _ _
      (by rw [matVec_length, length_vecScale, matVec_length, length_matScale])
      (by rw [ground.length_map, ground.length_map, matVec_length,
        length_vecScale, length_scaleB, idMat_len, hJ])
      (matVec_matScale c (rayH p q E M) J) ?_
    exact poly.swapMap_oneValue (poly.oneValue_trans
      (matVec_scaleB e0 (idMat n) J)
      (vecScale_oneValue e0 _ _ (inertia.matVec_idMat n J hJ)))
  have hEJdot : (dotN (residD [matVec T.val (elim.idRow n j0)] J)
      (matVec Et J)).oneValue
      (BPair.ofPos c * dotN (residD [matVec T.val (elim.idRow n j0)] J)
          (matVec (rayH p q E M) J)
        + (e0 * dotN (residD [matVec T.val (elim.idRow n j0)] J) J).swap) := by
    refine BPair.oneValue_trans (dotN_congrR _ _ _ hEtJ) ?_
    refine BPair.oneValue_trans
      (dotN_addRow_right _ _ _
        (by rw [length_vecScale, matVec_length, sqAt_len hray, hphi])
        (by rw [ground.length_map, length_vecScale, hJ, hphi])) ?_
    rw [dotN_swap (residD [matVec T.val (elim.idRow n j0)] J)
      (vecScale e0 J)]
    exact BPair.add_congr (dotN_scaleV _ _ _)
      (ground.swap_congr (dotN_scaleV _ _ _))
  have hF7 : (BPair.ofPos (4 * (q * q))
      * dotN (residD [matVec T.val (elim.idRow n j0)] J)
          (matVec (rayH p q E M) J)).oneValue
      ((BPair.ofPos (Pos.pow p 4) * BPair.ofNat np
          * dotN (residD [matVec T.val (elim.idRow n j0)] J) J).swap
        + dotN (residD [matVec T.val (elim.idRow n j0)] J) R) := by
    refine BPair.oneValue_trans (BPair.oneValue_symm (dotN_scaleV _ _ _)) ?_
    refine BPair.oneValue_trans (dotN_congrR _ _ _ hres) ?_
    refine BPair.oneValue_trans
      (dotN_addRow_right _ _ _
        (by rw [ground.length_map, length_vecScale, hJ, hphi])
        (hR.trans hphi.symm)) ?_
    rw [dotN_swap (residD [matVec T.val (elim.idRow n j0)] J)
      (vecScale (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np) J)]
    exact BPair.add_congr (ground.swap_congr (dotN_scaleV _ _ _))
      (BPair.oneValue_refl _)

  have hspos : BPair.unit ≤ dotN (matVec T.val (elim.idRow n j0))
      (matVec T.val (elim.idRow n j0)) := ground.leB_of_lt hs
  have hcpos : BPair.unit ≤ BPair.ofPos c := ground.leB_of_lt (ground.unitLtOfPos c)
  have hppos : BPair.unit ≤ BPair.ofPos (p * p) :=
    ground.leB_of_lt (ground.unitLtOfPos (p * p))
  have hqpos : BPair.unit ≤ BPair.ofPos (q * q) :=
    ground.leB_of_lt (ground.unitLtOfPos (q * q))
  have hWpos : BPair.unit ≤ BPair.ofPos W := ground.leB_of_lt (ground.unitLtOfPos W)
  have honeMul : ∀ x : BPair, (BPair.ofPos Pos.one * x).oneValue x := fun x =>
    BPair.oneValue_trans (BPair.ofPos_scale Pos.one x)
      (BPair.oneValue_of_eq (BPair.scale_one x))
  have hQE : BPair.unit ≤ inertia.quadForm E (matVec T.val (elim.idRow n j0)) :=
    ground.leB_of_not_lt (inertia.psd_all E spE hEs hEp _ hpsi)
  have hMMle : dotN (matVec M (matVec T.val (elim.idRow n j0)))
        (matVec M (matVec T.val (elim.idRow n j0)))
      ≤ BPair.ofPos (W * W) * dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)) :=
    inertia.cap_vec M hM W spU spL hcapM _ hpsi
  have hcsM : inertia.quadForm M (matVec T.val (elim.idRow n j0))
        * inertia.quadForm M (matVec T.val (elim.idRow n j0))
      ≤ dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
        * dotN (matVec M (matVec T.val (elim.idRow n j0)))
          (matVec M (matVec T.val (elim.idRow n j0))) :=
    coeff.dotN_sq_le _ _ (by rw [matVec_length, matVec_length, hMl]; exact hTl)
  have hQMle : inertia.quadForm M (matVec T.val (elim.idRow n j0))
      ≤ BPair.ofPos W * dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0)) := by
    refine ground.leB_of_sq_le (ground.unitLeMul hWpos hspos)
      (ground.leB_not_lt ?_)
    refine ground.leB_congr_right ?_
      (ground.leB_trans hcsM (ground.leB_mulR hspos hMMle))
    rw [BPair.mul_left_comm (dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0))) (BPair.ofPos (W * W))
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))),
      BPair.mul_mul_mul_comm (BPair.ofPos W)
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0))) (BPair.ofPos W)
        (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)))]
    exact BPair.mul_congr (BPair.oneValue_symm (BPair.ofPos_mul W W))
      (BPair.oneValue_refl _)
  have hray' : (inertia.quadForm (rayH p q E M)
      (matVec T.val (elim.idRow n j0))).oneValue
      (BPair.ofPos (q * q) * inertia.quadForm E (matVec T.val (elim.idRow n j0))
        + (BPair.ofPos (p * p)
            * inertia.quadForm M (matVec T.val (elim.idRow n j0))).swap) :=
    BPair.oneValue_trans
      (quadForm_site_sq (sqAt_matScale n (q * q) E hE)
        (sqAt_matScale n (p * p) M hM) hpsi)
      (BPair.add_congr (quadForm_ofPos (q * q) E _)
        (ground.swap_congr (quadForm_ofPos (p * p) M _)))
  have hone : BPair.unit.oneValue
      (BPair.ofPos c * inertia.quadForm (rayH p q E M)
          (matVec T.val (elim.idRow n j0))
        + (e0 * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))).swap) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (dotN_read (matVec T.val (elim.idRow n j0)) _)
          (dotP_null_tail_right (matVec T.val (elim.idRow n j0)) _ hker))) ?_
    refine BPair.oneValue_trans
      (dotN_matVec_congrM Et _ _ _ htie) ?_
    refine BPair.oneValue_trans
      (quadForm_site_sq (sqAt_matScale n c _ hray)
        (sqAt_scaleB e0 n (idMat n) hIsq) hpsi) ?_
    refine BPair.add_congr (quadForm_ofPos c _ _) (ground.swap_congr ?_)
    exact BPair.oneValue_trans (quadForm_scaleB e0 (idMat n) _)
      (BPair.mul_congr (BPair.oneValue_refl _)
        (dotN_congrR _ _ _ (inertia.matVec_idMat n _ hpsi)))
  have he0s : (BPair.ofPos c * inertia.quadForm (rayH p q E M)
      (matVec T.val (elim.idRow n j0))).oneValue
      (e0 * dotN (matVec T.val (elim.idRow n j0))
        (matVec T.val (elim.idRow n j0))) :=
    BPair.swap_of_add_unit (BPair.oneValue_symm hone)
  have hfloor0 : (BPair.ofPos (c * (p * p) * W)).swap ≤ e0 := by
    have e5 : BPair.ofPos c * (BPair.ofPos (p * p)
          * (BPair.ofPos W * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))))
        = BPair.ofPos c * BPair.ofPos (p * p) * BPair.ofPos W
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)) := by
      rw [← BPair.mul_assoc (BPair.ofPos c) (BPair.ofPos (p * p))
          (BPair.ofPos W * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))),
        ← BPair.mul_assoc (BPair.ofPos c * BPair.ofPos (p * p)) (BPair.ofPos W)
          (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)))]
    have e6 : (BPair.ofPos c * BPair.ofPos (p * p) * BPair.ofPos W).oneValue
        (BPair.ofPos (c * (p * p) * W)) :=
      BPair.oneValue_trans
        (BPair.mul_congr (BPair.ofPos_mul c (p * p)) (BPair.oneValue_refl _))
        (BPair.ofPos_mul (c * (p * p)) W)
    have e4 : BPair.ofPos c * (BPair.ofPos (q * q)
            * inertia.quadForm E (matVec T.val (elim.idRow n j0))
          + (BPair.ofPos (p * p)
              * inertia.quadForm M (matVec T.val (elim.idRow n j0))).swap)
        = BPair.ofPos c * (BPair.ofPos (q * q)
            * inertia.quadForm E (matVec T.val (elim.idRow n j0)))
          + (BPair.ofPos c * (BPair.ofPos (p * p)
              * inertia.quadForm M (matVec T.val (elim.idRow n j0)))).swap := by
      rw [BPair.left_distrib, BPair.mul_swap]
    have hstep : BPair.unit
          + (BPair.ofPos c * (BPair.ofPos (p * p)
              * (BPair.ofPos W * dotN (matVec T.val (elim.idRow n j0))
                (matVec T.val (elim.idRow n j0))))).swap
        ≤ BPair.ofPos c * (BPair.ofPos (q * q)
            * inertia.quadForm E (matVec T.val (elim.idRow n j0)))
          + (BPair.ofPos c * (BPair.ofPos (p * p)
              * inertia.quadForm M (matVec T.val (elim.idRow n j0)))).swap :=
      ground.leB_add (ground.unitLeMul hcpos (ground.unitLeMul hqpos hQE))
        (ground.leB_swap (ground.leB_mulR hcpos (ground.leB_mulR hppos hQMle)))
    have hlow : (BPair.ofPos (c * (p * p) * W)).swap
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
        ≤ e0 * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)) := by
      refine ground.leB_congr ?_ ?_ hstep
      · refine BPair.oneValue_trans (BPair.unit_add _) ?_
        refine BPair.oneValue_trans (ground.swap_congr
          (BPair.oneValue_trans (BPair.oneValue_of_eq e5)
            (BPair.mul_congr e6 (BPair.oneValue_refl _)))) ?_
        exact BPair.oneValue_of_eq
          (BPair.swap_mul (BPair.ofPos (c * (p * p) * W)) _).symm
      · refine BPair.oneValue_trans (BPair.oneValue_of_eq e4.symm) ?_
        exact BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_symm hray')) he0s
    exact ground.leB_unscale hs hlow

  have hQpos : BPair.unit ≤ BPair.ofPos (4 * (q * q)) :=
    ground.leB_of_lt (ground.unitLtOfPos (4 * (q * q)))
  have hgdpos : BPair.unit ≤ BPair.ofPos gd :=
    ground.leB_of_lt (ground.unitLtOfPos gd)
  have hapos : BPair.unit ≤ BPair.ofPos (Pos.pow p 4) * BPair.ofNat np :=
    ground.unitLeMul (ground.leB_of_lt (ground.unitLtOfPos (Pos.pow p 4)))
      (ground.unitLeOfNat np)
  have hfpos : BPair.unit ≤ dotN (residD [matVec T.val (elim.idRow n j0)] J)
      (residD [matVec T.val (elim.idRow n j0)] J) :=
    ground.leB_of_not_lt (dotN_self_side _)
  have hrpos : BPair.unit ≤ dotN R R := ground.leB_of_not_lt (dotN_self_side R)
  have hDpos : BPair.unit ≤ BPair.ofPos gn
      + (BPair.ofPos (gd * c * (p * p) * W)).swap :=
    ground.leB_of_lt (ground.unitLt_of_swap_lt hside)
  have hQFtie : (inertia.quadForm Et
      (residD [matVec T.val (elim.idRow n j0)] J)).oneValue
      (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
        * (BPair.ofPos c * dotN (residD [matVec T.val (elim.idRow n j0)] J)
              (matVec (rayH p q E M) J)
          + (e0 * dotN (residD [matVec T.val (elim.idRow n j0)] J) J).swap)) :=
    BPair.oneValue_trans hQF (BPair.mul_congr (BPair.oneValue_refl _) hEJdot)
  have hgap2 : BPair.ofPos gn * dotN (residD [matVec T.val (elim.idRow n j0)] J)
        (residD [matVec T.val (elim.idRow n j0)] J)
      ≤ BPair.ofPos gd * inertia.quadForm Et
        (residD [matVec T.val (elim.idRow n j0)] J) :=
    ground.leB_congr (BPair.oneValue_symm (BPair.ofPos_scale gn _))
      (BPair.oneValue_symm (BPair.ofPos_scale gd _)) hgap
  have hposid : gd * (c * (p * p) * W) = gd * c * (p * p) * W := by
    rw [← ground.mul_assoc gd (c * (p * p)) W, ← ground.mul_assoc gd c (p * p)]
  have hVb : (BPair.ofPos gd * BPair.ofPos (c * (p * p) * W)).oneValue
      (BPair.ofPos (gd * c * (p * p) * W)) :=
    BPair.oneValue_trans (BPair.ofPos_mul gd (c * (p * p) * W))
      (BPair.oneValue_of_eq (congrArg BPair.ofPos hposid))
  have hfl : (BPair.ofPos (4 * (q * q))
        * BPair.ofPos (gd * c * (p * p) * W)).swap
      ≤ BPair.ofPos gd * (BPair.ofPos c
          * (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np)
        + BPair.ofPos (4 * (q * q)) * e0) := by
    have hb : BPair.unit
          + BPair.ofPos gd * (BPair.ofPos (4 * (q * q))
              * (BPair.ofPos (c * (p * p) * W)).swap)
        ≤ BPair.ofPos gd * (BPair.ofPos c
            * (BPair.ofPos (Pos.pow p 4) * BPair.ofNat np))
          + BPair.ofPos gd * (BPair.ofPos (4 * (q * q)) * e0) :=
      ground.leB_add (ground.unitLeMul hgdpos (ground.unitLeMul hcpos hapos))
        (ground.leB_mulR hgdpos (ground.leB_mulR hQpos hfloor0))
    refine ground.leB_congr ?_
      (BPair.oneValue_of_eq (BPair.left_distrib _ _ _).symm) hb
    refine BPair.oneValue_trans (BPair.unit_add _) ?_
    rw [BPair.mul_swap, BPair.mul_swap]
    refine ground.swap_congr ?_
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm (BPair.ofPos gd)
        (BPair.ofPos (4 * (q * q))) (BPair.ofPos (c * (p * p) * W))))
      (BPair.mul_congr (BPair.oneValue_refl _) hVb)
  have hcs : ¬ (dotN (residD [matVec T.val (elim.idRow n j0)] J)
        (residD [matVec T.val (elim.idRow n j0)] J) * dotN R R
      < dotN (residD [matVec T.val (elim.idRow n j0)] J) R
        * dotN (residD [matVec T.val (elim.idRow n j0)] J) R) :=
    ground.leB_not_lt (coeff.dotN_sq_le _ R (hphi.trans hR.symm))
  have epow : 4 * (q * q) * (4 * (q * q)) = 16 * Pos.pow q 4 := by
    show 4 * (q * q) * (4 * (q * q)) = 16 * (q * (q * (q * (q * Pos.one))))
    rw [ground.mul_one q, ground.mul_mul_mul_comm 4 (q * q) 4 (q * q),
      ground.mul_assoc q q (q * q),
      show (4 : Pos) * 4 = 16 from by decide +kernel]
  have hmain := driftClose hQpos hfpos hrpos hDpos hQFtie hF7 hsf hgap2 hfl hcs
  refine ground.leB_congr ?_ ?_ hmain
  · have e7 : BPair.ofPos (4 * (q * q))
          * (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap)
          * (BPair.ofPos (4 * (q * q))
            * (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap))
          * dotN (residD [matVec T.val (elim.idRow n j0)] J)
            (residD [matVec T.val (elim.idRow n j0)] J)
        = BPair.ofPos (4 * (q * q)) * BPair.ofPos (4 * (q * q))
          * ((BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap)
            * (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap)
            * dotN (residD [matVec T.val (elim.idRow n j0)] J)
              (residD [matVec T.val (elim.idRow n j0)] J)) := by
      rw [BPair.mul_mul_mul_comm (BPair.ofPos (4 * (q * q)))
          (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap)
          (BPair.ofPos (4 * (q * q)))
          (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap),
        BPair.mul_assoc
          (BPair.ofPos (4 * (q * q)) * BPair.ofPos (4 * (q * q)))
          ((BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap)
            * (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap))
          (dotN (residD [matVec T.val (elim.idRow n j0)] J)
            (residD [matVec T.val (elim.idRow n j0)] J))]
    refine BPair.oneValue_trans (BPair.oneValue_of_eq e7) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_trans (BPair.ofPos_mul (4 * (q * q)) (4 * (q * q)))
          (BPair.oneValue_of_eq (congrArg BPair.ofPos epow)))
        (BPair.oneValue_refl _)) ?_
    exact BPair.ofPos_scale (16 * Pos.pow q 4) _
  · have e8 : BPair.ofPos gd * BPair.ofPos c
          * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))
          * (BPair.ofPos gd * BPair.ofPos c
            * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0)))
          * dotN R R
        = BPair.ofPos gd * BPair.ofPos gd * (BPair.ofPos c * BPair.ofPos c)
          * (dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))
            * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))
            * dotN R R) := by
      rw [BPair.mul_mul_mul_comm (BPair.ofPos gd * BPair.ofPos c)
          (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)))
          (BPair.ofPos gd * BPair.ofPos c)
          (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))),
        BPair.mul_mul_mul_comm (BPair.ofPos gd) (BPair.ofPos c)
          (BPair.ofPos gd) (BPair.ofPos c),
        BPair.mul_assoc
          (BPair.ofPos gd * BPair.ofPos gd * (BPair.ofPos c * BPair.ofPos c))
          (dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))
            * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0)))
          (dotN R R)]
    refine BPair.oneValue_trans (BPair.oneValue_of_eq e8) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.ofPos_mul gd gd) (BPair.ofPos_mul c c))
          (BPair.ofPos_mul (gd * gd) (c * c)))
        (BPair.oneValue_refl _)) ?_
    exact BPair.ofPos_scale (gd * gd * (c * c)) _

/-! The truncation tier of `lem:fourpoint`'s tail: the displayed jet moment
through `τ⁴`, the key caps' fold, and the bracket `|N_A(τ)| ≤ τ⁶ T_A(τ)`. -/

/-- The jet state's moment through `τ⁴` (`lem:fourpoint`'s tail): the
pairing at the full jet against its gram read through `τ⁴`, the keys
nought to two, the gram's key-two read entering the top coefficient as
the datum's balance partner, cleared at `q⁴`: the window carrier's
spelling of the displayed moment, the interface's `jetMoment` at the
anchor's own reads. -/
def jetDisplay (A : Mat) (psi0 psi1 psi2 : List BPair) (p q : Pos) : BPair :=
  (dotN psi0 (matVec A psi0)).scale (Pos.pow q 4)
  + (BPair.ofNat 2 * dotN psi0 (matVec A psi1)).scale (p * p * (q * q))
  + (BPair.ofNat 2 * dotN psi0 (matVec A psi2) + dotN psi1 (matVec A psi1)
      + (dotN psi0 (matVec A psi0) * dotN psi1 psi1).swap).scale (Pos.pow p 4)

/-- The key caps' fold `T_A` (`lem:fourpoint`'s tail): the magnitude fold of
`N_A`'s keys three to six at the caps `n₃, …, n₆`, read at the observable's
cap `[cn : cd]`, the display's three coefficients' magnitudes, the gram's
key-two read `g11` and the second-order weight's cap `[zn : zd]`, cleared
at `cd zd` and at the two clearings `p`, `q`. -/
def truncCap (cn cd zd : Pos) (m0 m1 m2 g11 zn : BPair) (p q : Pos) : BPair :=
  ((BPair.ofPos cn + BPair.ofPos cd * windowsep.mag m0) * (zn + g11.scale zd)
      + BPair.ofPos cd * windowsep.mag m1 * g11.scale zd).scale (Pos.pow q 6 * Pos.pow p 6)
  + ((BPair.ofPos cn + BPair.ofPos cd * windowsep.mag m0) * zn
      + BPair.ofPos cd * windowsep.mag m1 * (zn + g11.scale zd)
      + BPair.ofPos cd * windowsep.mag m2 * g11.scale zd).scale (Pos.pow q 4 * Pos.pow p 8)
  + (BPair.ofPos cd * windowsep.mag m1 * zn
      + BPair.ofPos cd * windowsep.mag m2 * (zn + g11.scale zd)).scale (q * q * Pos.pow p 10)
  + (BPair.ofPos cd * windowsep.mag m2 * zn).scale (Pos.pow p 12)

/-! The ground monomial kit: a two-base power product multiplies at the
added keys, and the jet's three clearings read at the two-base normal
form. -/

/-- Two-base monomials multiply at the added keys. -/
private theorem powMul (x y : Pos) (a b c d e f : Nat) (he : a + c = e)
    (hf : b + d = f) :
    (Pos.pow x a * Pos.pow y b) * (Pos.pow x c * Pos.pow y d)
      = Pos.pow x e * Pos.pow y f := by
  rw [← he, ← hf, ground.mul_mul_mul_comm, ← Pos.pow_add, ← Pos.pow_add]

private theorem s0read (p q : Pos) : Pos.pow q 4 = Pos.pow q 4 * Pos.pow p 0 :=
  (ground.mul_one (Pos.pow q 4)).symm

private theorem s1read (p q : Pos) :
    p * p * (q * q) = Pos.pow q 2 * Pos.pow p 2 := by
  rw [Pos.pow_two q, Pos.pow_two p]
  exact ground.mul_comm (p * p) (q * q)

private theorem s2read (p q : Pos) :
    Pos.pow p 4 = Pos.pow q 0 * Pos.pow p 4 :=
  (ground.one_mul (Pos.pow p 4)).symm

private theorem w5read (p q : Pos) :
    Pos.pow q 2 * Pos.pow p 10 = q * q * Pos.pow p 10 := by
  rw [Pos.pow_two q]

private theorem w6read (p q : Pos) :
    Pos.pow q 0 * Pos.pow p 12 = Pos.pow p 12 :=
  ground.one_mul (Pos.pow p 12)

private theorem mono00 (p q : Pos) :
    Pos.pow q 4 * Pos.pow q 4 = Pos.pow q 8 * Pos.pow p 0 := by
  rw [s0read p q]; exact powMul q p 4 0 4 0 8 0 rfl rfl

private theorem mono01 (p q : Pos) :
    Pos.pow q 4 * (p * p * (q * q)) = Pos.pow q 6 * Pos.pow p 2 := by
  rw [s1read p q, s0read p q]; exact powMul q p 4 0 2 2 6 2 rfl rfl

private theorem mono10 (p q : Pos) :
    p * p * (q * q) * Pos.pow q 4 = Pos.pow q 6 * Pos.pow p 2 := by
  rw [s1read p q, s0read p q]; exact powMul q p 2 2 4 0 6 2 rfl rfl

private theorem mono11 (p q : Pos) :
    p * p * (q * q) * (p * p * (q * q)) = Pos.pow q 4 * Pos.pow p 4 := by
  rw [s1read p q]; exact powMul q p 2 2 2 2 4 4 rfl rfl

private theorem mono12 (p q : Pos) :
    p * p * (q * q) * Pos.pow p 4 = Pos.pow q 2 * Pos.pow p 6 := by
  rw [s1read p q, s2read p q]; exact powMul q p 2 2 0 4 2 6 rfl rfl

private theorem mono20 (p q : Pos) :
    Pos.pow p 4 * Pos.pow q 4 = Pos.pow q 4 * Pos.pow p 4 :=
  ground.mul_comm _ _

private theorem mono21 (p q : Pos) :
    Pos.pow p 4 * (p * p * (q * q)) = Pos.pow q 2 * Pos.pow p 6 := by
  rw [s2read p q, s1read p q]; exact powMul q p 0 4 2 2 2 6 rfl rfl

private theorem mono22 (p q : Pos) :
    Pos.pow p 4 * Pos.pow p 4 = Pos.pow q 0 * Pos.pow p 8 := by
  rw [s2read p q]; exact powMul q p 0 4 0 4 0 8 rfl rfl

/-! The balance carrier's small reads consumed below. -/

private theorem scale3 (x1 x2 x3 : BPair) (w : Pos) :
    (x1 + (x2 + x3)).scale w = x1.scale w + (x2.scale w + x3.scale w) := by
  rw [BPair.scale_add, BPair.scale_add]

private theorem scale4 (x1 x2 x3 x4 : BPair) (w : Pos) :
    (x1 + (x2 + (x3 + x4))).scale w
      = x1.scale w + (x2.scale w + (x3.scale w + x4.scale w)) := by
  rw [BPair.scale_add, BPair.scale_add, BPair.scale_add]

/-- Four summands exchange their inner pair. -/
private theorem regroup4 (a b c d : BPair) :
    (a + b) + (c + d) = (a + d) + (b + c) := by
  rw [BPair.add_assoc, ← BPair.add_assoc b c d, BPair.add_comm (b + c) d,
    ← BPair.add_assoc]

private theorem le3 {x1 x2 x3 y1 y2 y3 : BPair} (h1 : x1 ≤ y1) (h2 : x2 ≤ y2)
    (h3 : x3 ≤ y3) : x1 + (x2 + x3) ≤ y1 + y2 + y3 :=
  ground.leB_congr_right (BPair.oneValue_of_eq (BPair.add_assoc y1 y2 y3).symm)
    (ground.leB_add h1 (ground.leB_add h2 h3))

private theorem le4 {x1 x2 x3 x4 y1 y2 y3 y4 : BPair} (h1 : x1 ≤ y1)
    (h2 : x2 ≤ y2) (h3 : x3 ≤ y3) (h4 : x4 ≤ y4) :
    x1 + (x2 + (x3 + x4)) ≤ y1 + y2 + y3 + y4 := by
  refine ground.leB_congr_right (BPair.oneValue_of_eq ?_)
    (ground.leB_add h1 (ground.leB_add h2 (ground.leB_add h3 h4)))
  rw [BPair.add_assoc, BPair.add_assoc]

/-! The pairing's linearity at a three-term jet and the symmetric
collection of the nine cross terms. -/

/-- The fold against a fixed right argument is linear in a three-term
combination. -/
private theorem bilin3 (y : List BPair) (c0 c1 c2 : BPair)
    (x0 x1 x2 : List BPair) (k0 : x0.length = y.length)
    (k1 : x1.length = y.length) (k2 : x2.length = y.length) :
    (dotN (vecAdd (vecScale c0 x0) (vecAdd (vecScale c1 x1) (vecScale c2 x2)))
        y).oneValue
      (c0 * dotN x0 y + (c1 * dotN x1 y + c2 * dotN x2 y)) := by
  have l0 : (vecScale c0 x0).length = y.length := (length_vecScale c0 x0).trans k0
  have l1 : (vecScale c1 x1).length = y.length := (length_vecScale c1 x1).trans k1
  have l2 : (vecScale c2 x2).length = y.length := (length_vecScale c2 x2).trans k2
  have l12 : (vecAdd (vecScale c1 x1) (vecScale c2 x2)).length = y.length :=
    length_vecAdd _ _ y.length l1 l2
  refine BPair.oneValue_trans (dotN_addRow _ _ y l0 l12) ?_
  refine BPair.add_congr (dotN_scaleRow_free c0 x0 y) ?_
  refine BPair.oneValue_trans (dotN_addRow _ _ y l1 l2) ?_
  exact BPair.add_congr (dotN_scaleRow_free c1 x1 y) (dotN_scaleRow_free c2 x2 y)

/-- The fold against a fixed left argument is linear in a three-term
combination. -/
private theorem bilin3R (y : List BPair) (c0 c1 c2 : BPair)
    (x0 x1 x2 : List BPair) (k0 : x0.length = y.length)
    (k1 : x1.length = y.length) (k2 : x2.length = y.length) :
    (dotN y (vecAdd (vecScale c0 x0)
        (vecAdd (vecScale c1 x1) (vecScale c2 x2)))).oneValue
      (c0 * dotN y x0 + (c1 * dotN y x1 + c2 * dotN y x2)) := by
  have l0 : (vecScale c0 x0).length = y.length := (length_vecScale c0 x0).trans k0
  have l1 : (vecScale c1 x1).length = y.length := (length_vecScale c1 x1).trans k1
  have l2 : (vecScale c2 x2).length = y.length := (length_vecScale c2 x2).trans k2
  have l12 : (vecAdd (vecScale c1 x1) (vecScale c2 x2)).length = y.length :=
    length_vecAdd _ _ y.length l1 l2
  refine BPair.oneValue_trans (dotN_addRow_right y _ _ l0 l12) ?_
  refine BPair.add_congr (dotN_scaleV c0 y x0) ?_
  refine BPair.oneValue_trans (dotN_addRow_right y _ _ l1 l2) ?_
  exact BPair.add_congr (dotN_scaleV c1 y x1) (dotN_scaleV c2 y x2)

/-- The action against a three-term jet is linear at every left
argument. -/
private theorem mv3 {n : Nat} (A : Mat) (hAr : rowsLen n A) (hAl : A.length = n)
    (y : List BPair) (hy : y.length = n)
    (c0 c1 c2 : BPair) (x0 x1 x2 : List BPair)
    (k0 : x0.length = n) (k1 : x1.length = n) (k2 : x2.length = n) :
    (dotN y (matVec A (vecAdd (vecScale c0 x0)
        (vecAdd (vecScale c1 x1) (vecScale c2 x2))))).oneValue
      (c0 * dotN y (matVec A x0)
        + (c1 * dotN y (matVec A x1) + c2 * dotN y (matVec A x2))) :=
  have lm : ∀ u : List BPair, (matVec A u).length = y.length :=
    fun u => (matVec_length A u).trans (hAl.trans hy.symm)
  BPair.oneValue_trans
    (dotN_congrR y _ _ (matVec_lin3 A n hAr c0 c1 c2 x0 x1 x2 k0 k1 k2))
    (bilin3R y c0 c1 c2 (matVec A x0) (matVec A x1) (matVec A x2)
      (lm x0) (lm x1) (lm x2))

/-- A sited pair's composed weight is the datum's rescaling. -/
private theorem leafScale (u v w : Pos) (a : BPair) (hw : u * v = w) :
    (BPair.ofPos u * (BPair.ofPos v * a)).oneValue (a.scale w) := by
  rw [← hw, ← BPair.mul_assoc]
  exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofPos_mul u v))
    (BPair.ofPos_scale (u * v) a)

/-- Nine summands collect at the five weights of the symmetric square. -/
private theorem col9 (t1 t2 t3 t4 t5 t6 t7 t8 t9 : BPair) :
    (t1 + (t2 + t3)) + ((t4 + (t5 + t6)) + (t7 + (t8 + t9)))
      = t1 + ((t2 + t4) + (((t3 + t7) + t5) + ((t6 + t8) + t9))) := by
  repeat rw [BPair.add_assoc]
  rw [BPair.add_left_comm t3 t4 (t5 + (t6 + (t7 + (t8 + t9)))),
    BPair.add_left_comm t6 t7 (t8 + t9),
    BPair.add_left_comm t5 t7 (t6 + (t8 + t9))]

/-- The symmetric square's nine cross terms read at the five weights. -/
private theorem sym3 (s0 s1 s2 : Pos) (a00 a01 a02 a11 a12 a22 : BPair)
    (w0 w1 w2 w3 w4 : Pos)
    (e0 : s0 * s0 = w0) (e1 : s0 * s1 = w1) (e2 : s0 * s2 = w2)
    (f1 : s1 * s0 = w1) (f2 : s1 * s1 = w2) (f3 : s1 * s2 = w3)
    (g2 : s2 * s0 = w2) (g3 : s2 * s1 = w3) (g4 : s2 * s2 = w4) :
    (BPair.ofPos s0 * (BPair.ofPos s0 * a00
        + (BPair.ofPos s1 * a01 + BPair.ofPos s2 * a02))
      + (BPair.ofPos s1 * (BPair.ofPos s0 * a01
          + (BPair.ofPos s1 * a11 + BPair.ofPos s2 * a12))
        + BPair.ofPos s2 * (BPair.ofPos s0 * a02
          + (BPair.ofPos s1 * a12 + BPair.ofPos s2 * a22)))).oneValue
      (a00.scale w0 + ((a01 + a01).scale w1
        + (((a02 + a02) + a11).scale w2
          + ((a12 + a12).scale w3 + a22.scale w4)))) := by
  rw [BPair.left_distrib, BPair.left_distrib, BPair.left_distrib,
    BPair.left_distrib, BPair.left_distrib, BPair.left_distrib]
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (leafScale s0 s0 w0 a00 e0)
        (BPair.add_congr (leafScale s0 s1 w1 a01 e1) (leafScale s0 s2 w2 a02 e2)))
      (BPair.add_congr
        (BPair.add_congr (leafScale s1 s0 w1 a01 f1)
          (BPair.add_congr (leafScale s1 s1 w2 a11 f2) (leafScale s1 s2 w3 a12 f3)))
        (BPair.add_congr (leafScale s2 s0 w2 a02 g2)
          (BPair.add_congr (leafScale s2 s1 w3 a12 g3)
            (leafScale s2 s2 w4 a22 g4))))) ?_
  rw [col9, ← BPair.scale_add, ← BPair.scale_add, ← BPair.scale_add,
    ← BPair.scale_add]
  exact BPair.oneValue_refl _

/-! The cancelling reads of the display's construction. -/

private theorem scaleNull {x y : BPair} (w : Pos) (h : x.oneValue y) :
    (x.scale w + (y.scale w).swap).oneValue BPair.unit := by
  rw [← BPair.scale_swap, ← BPair.scale_add]
  exact BPair.oneValue_trans (BPair.scale_congr w (ground.unitOfOne h))
    (BPair.oneValue_of_eqMem rfl)

private theorem scaleNull3 {x y z : BPair} (w : Pos)
    (h : x.oneValue (y + z)) :
    (x.scale w + ((y.scale w).swap + (z.scale w).swap)).oneValue BPair.unit := by
  rw [BPair.swap_add, ← BPair.scale_add]
  exact scaleNull w h

/-- The jet's five weights zip against the display's seven. -/
private theorem col5 (a1 a2 a3 a4 a5 c0 c1 c2 c3 c4 c5 c6 : BPair) :
    (a1 + (a2 + (a3 + (a4 + a5)))) + (c0 + (c1 + (c2 + (c3 + (c4 + (c5 + c6))))))
      = (a1 + c0) + ((a2 + c1) + ((a3 + c2)
          + ((a4 + c3) + ((a5 + c4) + (c5 + c6))))) := by
  rw [BPair.add_add_comm a1 (a2 + (a3 + (a4 + a5))) c0
        (c1 + (c2 + (c3 + (c4 + (c5 + c6))))),
    BPair.add_add_comm a2 (a3 + (a4 + a5)) c1 (c2 + (c3 + (c4 + (c5 + c6)))),
    BPair.add_add_comm a3 (a4 + a5) c2 (c3 + (c4 + (c5 + c6))),
    BPair.add_add_comm a4 a5 c3 (c4 + (c5 + c6)),
    ← BPair.add_assoc a5 c4 (c5 + c6)]

/-- The twelve products of the display against the gram collect at the
seven weights. -/
private theorem col12 (b00 b10 b20 b01 b11 b21 b02 b12 b22 b03 b13 b23 : BPair) :
    b00 + b10 + b20 + (b01 + b11 + b21 + (b02 + b12 + b22 + (b03 + b13 + b23)))
      = b00 + (b10 + ((b20 + b01) + ((b02 + b11)
          + ((b03 + (b12 + b21)) + ((b13 + b22) + b23))))) := by
  repeat rw [BPair.add_assoc]
  rw [BPair.add_left_comm b21 b02 (b12 + (b22 + (b03 + (b13 + b23)))),
    BPair.add_left_comm b11 b02 (b21 + (b12 + (b22 + (b03 + (b13 + b23))))),
    BPair.add_left_comm b22 b03 (b13 + b23),
    BPair.add_left_comm b12 b03 (b22 + (b13 + b23)),
    BPair.add_left_comm b21 b03 (b12 + (b22 + (b13 + b23))),
    BPair.add_left_comm b21 b12 (b22 + (b13 + b23)),
    BPair.add_left_comm b22 b13 b23]

/-- The truncation identity at the abstract carrier: the jet's moment
cleared at `q⁴` against the display's pairing with the gram leaves the
four keys three to six, the keys nought to two withdrawing at the
display's own construction. -/
private theorem tailId (m0 m1 m2 T A3 A4 e g11 G g22 : BPair) (p q : Pos)
    (hT : T.oneValue (m2 * e + m0 * g11))
    (hm0 : m0.oneValue (m0 * e)) (hm1 : m1.oneValue (m1 * e)) :
    ((m0.scale (Pos.pow q 8 * Pos.pow p 0)
        + (m1.scale (Pos.pow q 6 * Pos.pow p 2)
          + (T.scale (Pos.pow q 4 * Pos.pow p 4)
            + (A3.scale (Pos.pow q 2 * Pos.pow p 6)
              + A4.scale (Pos.pow q 0 * Pos.pow p 8))))).scale
          (Pos.pow q 4 * Pos.pow p 0)
      + ((m0.scale (Pos.pow q 4 * Pos.pow p 0)
            + m1.scale (Pos.pow q 2 * Pos.pow p 2)
            + m2.scale (Pos.pow q 0 * Pos.pow p 4))
          * (e.scale (Pos.pow q 8 * Pos.pow p 0)
            + (g11.scale (Pos.pow q 4 * Pos.pow p 4)
              + (G.scale (Pos.pow q 2 * Pos.pow p 6)
                + g22.scale (Pos.pow q 0 * Pos.pow p 8))))).swap).oneValue
      ((A3.scale (Pos.pow q 6 * Pos.pow p 6)
          + (((m0 * G).scale (Pos.pow q 6 * Pos.pow p 6)).swap
            + ((m1 * g11).scale (Pos.pow q 6 * Pos.pow p 6)).swap))
        + ((A4.scale (Pos.pow q 4 * Pos.pow p 8)
            + (((m0 * g22).scale (Pos.pow q 4 * Pos.pow p 8)).swap
              + (((m1 * G).scale (Pos.pow q 4 * Pos.pow p 8)).swap
                  + ((m2 * g11).scale (Pos.pow q 4 * Pos.pow p 8)).swap)))
          + ((((m1 * g22).scale (q * q * Pos.pow p 10)).swap
              + ((m2 * G).scale (q * q * Pos.pow p 10)).swap)
            + ((m2 * g22).scale (Pos.pow p 12)).swap))) := by
  rw [BPair.scale_add, BPair.scale_add, BPair.scale_add, BPair.scale_add,
    BPair.scale_scale, BPair.scale_scale, BPair.scale_scale, BPair.scale_scale,
    BPair.scale_scale,
    powMul q p 8 0 4 0 12 0 rfl rfl,
    powMul q p 6 2 4 0 10 2 rfl rfl,
    powMul q p 4 4 4 0 8 4 rfl rfl,
    powMul q p 2 6 4 0 6 6 rfl rfl,
    powMul q p 0 8 4 0 4 8 rfl rfl,
    BPair.left_distrib, BPair.left_distrib, BPair.left_distrib,
    BPair.right_distrib, BPair.right_distrib, BPair.right_distrib,
    BPair.right_distrib, BPair.right_distrib, BPair.right_distrib,
    BPair.right_distrib, BPair.right_distrib,
    ← BPair.scale_mul, ← BPair.scale_mul, ← BPair.scale_mul,
    ← BPair.scale_mul, ← BPair.scale_mul, ← BPair.scale_mul,
    ← BPair.scale_mul, ← BPair.scale_mul, ← BPair.scale_mul,
    ← BPair.scale_mul, ← BPair.scale_mul, ← BPair.scale_mul,
    powMul q p 4 0 8 0 12 0 rfl rfl,
    powMul q p 2 2 8 0 10 2 rfl rfl,
    powMul q p 0 4 8 0 8 4 rfl rfl,
    powMul q p 4 0 4 4 8 4 rfl rfl,
    powMul q p 2 2 4 4 6 6 rfl rfl,
    powMul q p 0 4 4 4 4 8 rfl rfl,
    powMul q p 4 0 2 6 6 6 rfl rfl,
    powMul q p 2 2 2 6 4 8 rfl rfl,
    powMul q p 0 4 2 6 2 10 rfl rfl,
    powMul q p 4 0 0 8 4 8 rfl rfl,
    powMul q p 2 2 0 8 2 10 rfl rfl,
    powMul q p 0 4 0 8 0 12 rfl rfl,
    w5read p q, w6read p q,
    col12,
    ← BPair.swap_add, ← BPair.swap_add, ← BPair.swap_add, ← BPair.swap_add,
    ← BPair.swap_add, ← BPair.swap_add, ← BPair.swap_add, ← BPair.swap_add,
    ← BPair.swap_add, ← BPair.swap_add, ← BPair.swap_add,
    col5]
  refine BPair.oneValue_trans
    (BPair.add_congr (scaleNull _ hm0)
      (BPair.add_congr (scaleNull _ hm1)
        (BPair.add_congr (scaleNull3 _ hT) (BPair.oneValue_refl _)))) ?_
  exact BPair.oneValue_trans (BPair.unit_add _)
    (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))

/-- The jet's moment against a symmetric datum, degree eight in the two
clearings. -/
private theorem jetQuad {n : Nat} (A : Mat) (hAr : rowsLen n A)
    (hAl : A.length = n) (hsym : matOneValue (transposeM A) A)
    (psi0 psi1 psi2 : List BPair) (h0 : psi0.length = n) (h1 : psi1.length = n)
    (h2 : psi2.length = n) (p q : Pos) :
    (dotN (jetVec p q psi0 psi1 psi2)
        (matVec A (jetVec p q psi0 psi1 psi2))).oneValue
      ((dotN psi0 (matVec A psi0)).scale (Pos.pow q 8 * Pos.pow p 0)
        + ((BPair.ofNat 2 * dotN psi0 (matVec A psi1)).scale
              (Pos.pow q 6 * Pos.pow p 2)
          + ((BPair.ofNat 2 * dotN psi0 (matVec A psi2)
                + dotN psi1 (matVec A psi1)).scale (Pos.pow q 4 * Pos.pow p 4)
            + ((dotN psi1 (matVec A psi2) + dotN psi1 (matVec A psi2)).scale
                  (Pos.pow q 2 * Pos.pow p 6)
              + (dotN psi2 (matVec A psi2)).scale
                  (Pos.pow q 0 * Pos.pow p 8))))) := by
  have lmv : ∀ u : List BPair, (matVec A u).length = n :=
    fun u => (matVec_length A u).trans hAl
  refine BPair.oneValue_trans
    (bilin3 (matVec A (jetVec p q psi0 psi1 psi2))
      (BPair.ofPos (Pos.pow q 4)) (BPair.ofPos (p * p * (q * q)))
      (BPair.ofPos (Pos.pow p 4)) psi0 psi1 psi2
      (h0.trans (lmv (jetVec p q psi0 psi1 psi2)).symm)
      (h1.trans (lmv (jetVec p q psi0 psi1 psi2)).symm)
      (h2.trans (lmv (jetVec p q psi0 psi1 psi2)).symm)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl _)
        (mv3 A hAr hAl psi0 h0 (BPair.ofPos (Pos.pow q 4))
          (BPair.ofPos (p * p * (q * q))) (BPair.ofPos (Pos.pow p 4))
          psi0 psi1 psi2 h0 h1 h2))
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (mv3 A hAr hAl psi1 h1 (BPair.ofPos (Pos.pow q 4))
            (BPair.ofPos (p * p * (q * q))) (BPair.ofPos (Pos.pow p 4))
            psi0 psi1 psi2 h0 h1 h2))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (mv3 A hAr hAl psi2 h2 (BPair.ofPos (Pos.pow q 4))
            (BPair.ofPos (p * p * (q * q))) (BPair.ofPos (Pos.pow p 4))
            psi0 psi1 psi2 h0 h1 h2)))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.add_congr
            (BPair.mul_congr (BPair.oneValue_refl _)
              (dotN_sym_flip A n hAr hAl hsym psi0 psi1 h0 h1))
            (BPair.oneValue_refl _)))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.add_congr
            (BPair.mul_congr (BPair.oneValue_refl _)
              (dotN_sym_flip A n hAr hAl hsym psi0 psi2 h0 h2))
            (BPair.add_congr
              (BPair.mul_congr (BPair.oneValue_refl _)
                (dotN_sym_flip A n hAr hAl hsym psi1 psi2 h1 h2))
              (BPair.oneValue_refl _)))))) ?_
  refine BPair.oneValue_trans
    (sym3 (Pos.pow q 4) (p * p * (q * q)) (Pos.pow p 4)
      (dotN psi0 (matVec A psi0)) (dotN psi0 (matVec A psi1))
      (dotN psi0 (matVec A psi2)) (dotN psi1 (matVec A psi1))
      (dotN psi1 (matVec A psi2)) (dotN psi2 (matVec A psi2))
      (Pos.pow q 8 * Pos.pow p 0) (Pos.pow q 6 * Pos.pow p 2)
      (Pos.pow q 4 * Pos.pow p 4) (Pos.pow q 2 * Pos.pow p 6)
      (Pos.pow q 0 * Pos.pow p 8)
      (mono00 p q) (mono01 p q) rfl (mono10 p q) (mono11 p q) (mono12 p q)
      (mono20 p q) (mono21 p q) (mono22 p q)) ?_
  exact BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr
      (BPair.scale_congr _ (BPair.oneValue_symm (BPair.ofNat_two_mul _)))
      (BPair.add_congr
        (BPair.scale_congr _
          (BPair.add_congr (BPair.oneValue_symm (BPair.ofNat_two_mul _))
            (BPair.oneValue_refl _)))
        (BPair.oneValue_refl _)))

/-- The jet's gram at the unit `ψ₀` with `ψ₁`, `ψ₂` off its line. -/
private theorem jetGram {n : Nat} (psi0 psi1 psi2 : List BPair)
    (h0 : psi0.length = n) (h1 : psi1.length = n) (h2 : psi2.length = n)
    (h00 : (dotN psi0 psi0).oneValue (BPair.ofNat 1))
    (h01 : (dotN psi0 psi1).oneValue BPair.unit)
    (h02 : (dotN psi0 psi2).oneValue BPair.unit) (p q : Pos) :
    (dotN (jetVec p q psi0 psi1 psi2) (jetVec p q psi0 psi1 psi2)).oneValue
      ((BPair.ofNat 1).scale (Pos.pow q 8 * Pos.pow p 0)
        + ((dotN psi1 psi1).scale (Pos.pow q 4 * Pos.pow p 4)
          + ((dotN psi1 psi2 + dotN psi1 psi2).scale
                (Pos.pow q 2 * Pos.pow p 6)
            + (dotN psi2 psi2).scale (Pos.pow q 0 * Pos.pow p 8)))) := by
  have lJ : (jetVec p q psi0 psi1 psi2).length = n :=
    length_vecAdd _ _ n ((length_vecScale _ psi0).trans h0)
      (length_vecAdd _ _ n ((length_vecScale _ psi1).trans h1)
        ((length_vecScale _ psi2).trans h2))
  refine BPair.oneValue_trans
    (bilin3 (jetVec p q psi0 psi1 psi2)
      (BPair.ofPos (Pos.pow q 4)) (BPair.ofPos (p * p * (q * q)))
      (BPair.ofPos (Pos.pow p 4)) psi0 psi1 psi2
      (h0.trans lJ.symm) (h1.trans lJ.symm) (h2.trans lJ.symm)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl _)
        (bilin3R psi0 (BPair.ofPos (Pos.pow q 4))
          (BPair.ofPos (p * p * (q * q))) (BPair.ofPos (Pos.pow p 4))
          psi0 psi1 psi2 (h0.trans h0.symm) (h1.trans h0.symm)
          (h2.trans h0.symm)))
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (bilin3R psi1 (BPair.ofPos (Pos.pow q 4))
            (BPair.ofPos (p * p * (q * q))) (BPair.ofPos (Pos.pow p 4))
            psi0 psi1 psi2 (h0.trans h1.symm) (h1.trans h1.symm)
            (h2.trans h1.symm)))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (bilin3R psi2 (BPair.ofPos (Pos.pow q 4))
            (BPair.ofPos (p * p * (q * q))) (BPair.ofPos (Pos.pow p 4))
            psi0 psi1 psi2 (h0.trans h2.symm) (h1.trans h2.symm)
            (h2.trans h2.symm))))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.mul_congr (BPair.oneValue_refl _)
        (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl _) h00)
          (BPair.add_congr (BPair.mul_congr (BPair.oneValue_refl _) h01)
            (BPair.mul_congr (BPair.oneValue_refl _) h02))))
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.add_congr
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_trans (dotN_comm psi1 psi0) h01))
            (BPair.oneValue_refl _)))
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.add_congr
            (BPair.mul_congr (BPair.oneValue_refl _)
              (BPair.oneValue_trans (dotN_comm psi2 psi0) h02))
            (BPair.add_congr
              (BPair.mul_congr (BPair.oneValue_refl _)
                (dotN_comm psi2 psi1))
              (BPair.oneValue_refl _)))))) ?_
  refine BPair.oneValue_trans
    (sym3 (Pos.pow q 4) (p * p * (q * q)) (Pos.pow p 4)
      (BPair.ofNat 1) BPair.unit BPair.unit (dotN psi1 psi1)
      (dotN psi1 psi2) (dotN psi2 psi2)
      (Pos.pow q 8 * Pos.pow p 0) (Pos.pow q 6 * Pos.pow p 2)
      (Pos.pow q 4 * Pos.pow p 4) (Pos.pow q 2 * Pos.pow p 6)
      (Pos.pow q 0 * Pos.pow p 8)
      (mono00 p q) (mono01 p q) rfl (mono10 p q) (mono11 p q) (mono12 p q)
      (mono20 p q) (mono21 p q) (mono22 p q)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.scale_congr _ (BPair.unit_add BPair.unit))
          (BPair.unit_scale _))
        (BPair.add_congr
          (BPair.scale_congr _
            (BPair.oneValue_trans
              (BPair.add_congr (BPair.unit_add BPair.unit)
                (BPair.oneValue_refl _))
              (BPair.unit_add _)))
          (BPair.oneValue_refl _)))) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_add _)

/-! The magnitude's cap tier: the two-sided read, the second-order
weight's clearing and the products' caps. -/

private theorem magLe {z M : BPair} (h1 : z ≤ M) (h2 : z.swap ≤ M) :
    windowsep.mag z ≤ M :=
  ground.leB_congr_left (BPair.ofNat_one_mul (windowsep.mag z))
    (windowsep.mag_mul_le
      (ground.leB_congr_left (BPair.oneValue_symm (BPair.ofNat_one_mul z)) h1)
      (ground.leB_congr_left (BPair.oneValue_symm (BPair.ofNat_one_mul z.swap))
        h2))

private theorem scaleRead (x : BPair) (w zd : Pos) :
    (x.scale (w * zd)).oneValue (BPair.ofPos w * x.scale zd) :=
  BPair.oneValue_symm
    (BPair.oneValue_trans (BPair.ofPos_scale w (x.scale zd))
      (BPair.oneValue_of_eq (by rw [BPair.scale_scale, ground.mul_comm zd w])))

private theorem gramCapZ (g22 zn : BPair) (w zd : Pos)
    (hZ : g22.scale zd ≤ zn) : g22.scale (w * zd) ≤ BPair.ofPos w * zn := by
  rw [ground.mul_comm w zd, ← BPair.scale_scale]
  exact ground.leB_congr_right (BPair.oneValue_symm (BPair.ofPos_scale w zn))
    (ground.leB_scale hZ w)

private theorem gramCap (g11 g22 zn : BPair) (w zd : Pos)
    (hZ : g22.scale zd ≤ zn) :
    (g11 + g22).scale (w * zd) ≤ BPair.ofPos w * (zn + g11.scale zd) := by
  rw [BPair.scale_add]
  refine ground.leB_congr_right (BPair.oneValue_of_eq ?_)
    (ground.leB_add
      (ground.leB_congr_right (scaleRead g11 w zd) (ground.leB_refl _))
      (gramCapZ g22 zn w zd hZ))
  rw [← BPair.left_distrib, BPair.add_comm (g11.scale zd) zn]

private theorem prodBound (mi gj B : BPair) (cd zd : Pos)
    (hg : (windowsep.mag gj).scale (cd * zd) ≤ BPair.ofPos cd * B) :
    (windowsep.mag (mi * gj)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag mi * B := by
  refine ground.leB_congr_left
    (BPair.scale_congr (cd * zd)
      (BPair.oneValue_symm (windowsep.mag_mul mi gj))) ?_
  rw [← BPair.mul_scale]
  refine ground.leB_congr_right (BPair.oneValue_of_eq ?_)
    (ground.leB_mulR (windowsep.unitLe_mag mi) hg)
  rw [← BPair.mul_assoc, BPair.mul_comm (windowsep.mag mi) (BPair.ofPos cd)]

private theorem magStep (X Y MX MY : BPair) (hX : windowsep.mag X ≤ MX)
    (hY : windowsep.mag Y ≤ MY) : windowsep.mag (X + Y) ≤ MX + MY :=
  ground.leB_trans (windowsep.mag_add_le X Y) (ground.leB_add hX hY)

private theorem magLeaf (x : BPair) (w : Pos) :
    windowsep.mag (x.scale w) ≤ (windowsep.mag x).scale w :=
  ground.leB_congr_right (BPair.oneValue_of_eq (windowsep.mag_scale x w))
    (ground.leB_refl _)

private theorem magLeafS (x : BPair) (w : Pos) :
    windowsep.mag ((x.scale w).swap) ≤ (windowsep.mag x).scale w := by
  rw [windowsep.mag_swap, windowsep.mag_scale]
  exact ground.leB_refl _

/-- The self pairing of a two-term sum. -/
private theorem sumSelf {n : Nat} (u v : List BPair) (hu : u.length = n)
    (hv : v.length = n) :
    (dotN (vecAdd u v) (vecAdd u v)).oneValue
      ((dotN u u + dotN u v) + (dotN v u + dotN v v)) := by
  refine BPair.oneValue_trans
    (dotN_add_expand u v (hu.trans hv.symm)) ?_
  rw [BPair.add_add_comm (dotN u u) (dotN v v) (dotN u v) (dotN v u),
    BPair.add_comm (dotN v v) (dotN v u)]
  exact BPair.oneValue_refl _

/-- The four keys' magnitude fold sits under the cap, key by key. -/
private theorem magClose (cn cd zd : Pos) (A3 A4 m0 m1 m2 g11 G g22 zn : BPair)
    (w3 w4 w5 w6 : Pos)
    (b3a : (windowsep.mag A3).scale (cd * zd)
      ≤ BPair.ofPos cn * (zn + g11.scale zd))
    (b3b : (windowsep.mag (m0 * G)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m0 * (zn + g11.scale zd))
    (b3c : (windowsep.mag (m1 * g11)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m1 * g11.scale zd)
    (b4a : (windowsep.mag A4).scale (cd * zd) ≤ BPair.ofPos cn * zn)
    (b4b : (windowsep.mag (m0 * g22)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m0 * zn)
    (b4c : (windowsep.mag (m1 * G)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m1 * (zn + g11.scale zd))
    (b4d : (windowsep.mag (m2 * g11)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m2 * g11.scale zd)
    (b5a : (windowsep.mag (m1 * g22)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m1 * zn)
    (b5b : (windowsep.mag (m2 * G)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m2 * (zn + g11.scale zd))
    (b6a : (windowsep.mag (m2 * g22)).scale (cd * zd)
      ≤ BPair.ofPos cd * windowsep.mag m2 * zn) :
    (windowsep.mag
        ((A3.scale w3 + (((m0 * G).scale w3).swap + ((m1 * g11).scale w3).swap))
          + ((A4.scale w4 + (((m0 * g22).scale w4).swap
                + (((m1 * G).scale w4).swap + ((m2 * g11).scale w4).swap)))
            + ((((m1 * g22).scale w5).swap + ((m2 * G).scale w5).swap)
              + ((m2 * g22).scale w6).swap)))).scale (cd * zd)
      ≤ ((BPair.ofPos cn + BPair.ofPos cd * windowsep.mag m0)
              * (zn + g11.scale zd)
            + BPair.ofPos cd * windowsep.mag m1 * g11.scale zd).scale w3
        + ((BPair.ofPos cn + BPair.ofPos cd * windowsep.mag m0) * zn
            + BPair.ofPos cd * windowsep.mag m1 * (zn + g11.scale zd)
            + BPair.ofPos cd * windowsep.mag m2 * g11.scale zd).scale w4
        + (BPair.ofPos cd * windowsep.mag m1 * zn
            + BPair.ofPos cd * windowsep.mag m2 * (zn + g11.scale zd)).scale w5
        + (BPair.ofPos cd * windowsep.mag m2 * zn).scale w6 := by
  refine ground.leB_trans (ground.leB_scale
    (magStep _ _ _ _
      (magStep _ _ _ _ (magLeaf A3 w3)
        (magStep _ _ _ _ (magLeafS (m0 * G) w3) (magLeafS (m1 * g11) w3)))
      (magStep _ _ _ _
        (magStep _ _ _ _ (magLeaf A4 w4)
          (magStep _ _ _ _ (magLeafS (m0 * g22) w4)
            (magStep _ _ _ _ (magLeafS (m1 * G) w4) (magLeafS (m2 * g11) w4))))
        (magStep _ _ _ _
          (magStep _ _ _ _ (magLeafS (m1 * g22) w5) (magLeafS (m2 * G) w5))
          (magLeafS (m2 * g22) w6)))) (cd * zd)) ?_
  rw [scale4]
  refine le4 ?_ ?_ ?_ ?_
  · rw [← scale3 (windowsep.mag A3) (windowsep.mag (m0 * G))
        (windowsep.mag (m1 * g11)) w3,
      BPair.scale_comm (windowsep.mag A3 + (windowsep.mag (m0 * G)
        + windowsep.mag (m1 * g11))) w3 (cd * zd)]
    refine ground.leB_scale ?_ w3
    rw [scale3 (windowsep.mag A3) (windowsep.mag (m0 * G))
        (windowsep.mag (m1 * g11)) (cd * zd),
      BPair.right_distrib]
    exact le3 b3a b3b b3c
  · rw [← scale4 (windowsep.mag A4) (windowsep.mag (m0 * g22))
        (windowsep.mag (m1 * G)) (windowsep.mag (m2 * g11)) w4,
      BPair.scale_comm (windowsep.mag A4 + (windowsep.mag (m0 * g22)
        + (windowsep.mag (m1 * G) + windowsep.mag (m2 * g11)))) w4 (cd * zd)]
    refine ground.leB_scale ?_ w4
    rw [scale4 (windowsep.mag A4) (windowsep.mag (m0 * g22))
        (windowsep.mag (m1 * G)) (windowsep.mag (m2 * g11)) (cd * zd),
      BPair.right_distrib]
    exact le4 b4a b4b b4c b4d
  · rw [← BPair.scale_add (windowsep.mag (m1 * g22)) (windowsep.mag (m2 * G)) w5,
      BPair.scale_comm (windowsep.mag (m1 * g22) + windowsep.mag (m2 * G)) w5
        (cd * zd)]
    refine ground.leB_scale ?_ w5
    rw [BPair.scale_add (windowsep.mag (m1 * g22)) (windowsep.mag (m2 * G)) (cd * zd)]
    exact ground.leB_add b5a b5b
  · rw [BPair.scale_comm (windowsep.mag (m2 * g22)) w6 (cd * zd)]
    exact ground.leB_scale b6a w6

/-- The truncation beyond `τ⁴` (`lem:fourpoint`'s tail): the jet state's
moment is the pairing at the full jet against its gram, degree eight, while
the display reads the pairing against the gram through `τ⁴`; at the unit
`ψ₀` of self-pairing one with `ψ₁`, `ψ₂` off its line, the observable's
cap `[cn : cd]` and a cap `[zn : zd]` on the second-order weight, the
datum `N_A = P_A − μ̂_A G` sits at the keys three to six and its magnitude
fold is capped key by key, `|N_A(τ)| ≤ τ⁶ T_A(τ)` at the key caps
`n₃, …, n₆`, the display cleared at `q¹² cd zd`. -/
theorem truncBracket {n : Nat} (A : Mat) (cn cd : Pos) (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA')
    (psi0 psi1 psi2 : List BPair) (h0 : psi0.length = n) (h1 : psi1.length = n)
    (h2 : psi2.length = n)
    (h00 : (dotN psi0 psi0).oneValue (BPair.ofNat 1))
    (h01 : (dotN psi0 psi1).oneValue BPair.unit)
    (h02 : (dotN psi0 psi2).oneValue BPair.unit)
    (zn : BPair) (zd : Pos) (hZ : (dotN psi2 psi2).scale zd ≤ zn) (p q : Pos) :
    windowsep.mag
        ((dotN (jetVec p q psi0 psi1 psi2) (matVec A (jetVec p q psi0 psi1 psi2))).scale
            (Pos.pow q 4 * (cd * zd))
          + ((jetDisplay A psi0 psi1 psi2 p q
              * dotN (jetVec p q psi0 psi1 psi2) (jetVec p q psi0 psi1 psi2)).scale
              (cd * zd)).swap)
      ≤ truncCap cn cd zd (dotN psi0 (matVec A psi0))
          (BPair.ofNat 2 * dotN psi0 (matVec A psi1))
          (BPair.ofNat 2 * dotN psi0 (matVec A psi2) + dotN psi1 (matVec A psi1)
            + (dotN psi0 (matVec A psi0) * dotN psi1 psi1).swap)
          (dotN psi1 psi1) zn p q := by
  have hSq : sqAt (matScale cd A) n := hA.1
  have hAl : A.length = n := (length_matScale cd A).symm.trans (sqAt_len hSq)
  have hAr : rowsLen n A := rowsLen_of_sqAt (sqAt_matScale_reflect cd A hSq)
  have hsymA : matOneValue (transposeM A) A :=
    sym_of_capScale A cn cd spA spA' hA
  have hg11 : BPair.unit ≤ dotN psi1 psi1 :=
    ground.leB_of_not_lt (dotN_self_side psi1)
  have hg22 : BPair.unit ≤ dotN psi2 psi2 :=
    ground.leB_of_not_lt (dotN_self_side psi2)
  have lsw : (psi2.map BPair.swap).length = n :=
    (ground.length_map BPair.swap psi2).trans h2
  have hswapG : (dotN psi1 psi2 + dotN psi1 psi2).swap
      ≤ dotN psi1 psi1 + dotN psi2 psi2 := by
    refine ground.leB_of_unit_add (ground.leB_congr_right ?_
      (ground.leB_of_not_lt (dotN_self_side (vecAdd psi1 psi2))))
    refine BPair.oneValue_trans (sumSelf psi1 psi2 h1 h2) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (dotN_comm psi2 psi1) (BPair.oneValue_refl _))) ?_
    exact BPair.oneValue_of_eq
      (regroup4 (dotN psi1 psi1) (dotN psi1 psi2) (dotN psi1 psi2)
        (dotN psi2 psi2))
  have hGplain : (dotN psi1 psi2 + dotN psi1 psi2)
      ≤ dotN psi1 psi1 + dotN psi2 psi2 := by
    refine ground.leB_of_unit_add
      (V := (dotN psi1 psi2 + dotN psi1 psi2).swap)
      (ground.leB_congr_right ?_
        (ground.leB_of_not_lt
          (dotN_self_side (vecAdd psi1 (psi2.map BPair.swap)))))
    refine BPair.oneValue_trans (sumSelf psi1 (psi2.map BPair.swap) h1 lsw) ?_
    rw [dotN_swap psi1 psi2, dotN_swapLeft psi2 psi1,
      dotN_swapLeft psi2 (psi2.map BPair.swap), dotN_swap psi2 psi2,
      BPair.swap_swap]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.add_congr (ground.swap_congr (dotN_comm psi2 psi1))
          (BPair.oneValue_refl _))) ?_
    exact BPair.oneValue_of_eq
      (regroup4 (dotN psi1 psi1) (dotN psi1 psi2).swap (dotN psi1 psi2).swap
        (dotN psi2 psi2))
  have hGle : windowsep.mag (dotN psi1 psi2 + dotN psi1 psi2)
      ≤ dotN psi1 psi1 + dotN psi2 psi2 := magLe hGplain hswapG
  have hone : ∀ x : BPair, ((BPair.ofNat 1 * BPair.ofNat 1) * x).oneValue x :=
    fun x => BPair.oneValue_trans
      (BPair.mul_congr_left (BPair.mul_ofNat_one (BPair.ofNat 1)))
      (BPair.ofNat_one_mul x)
  have hdbl : ∀ x : BPair, x.scale (2 * cd) = (x + x).scale cd := by
    intro x
    rw [← BPair.scale_scale, BPair.scale_two]
  have hcp1 : (dotN psi1 (matVec A psi2) + dotN psi1 (matVec A psi2)).scale cd
      ≤ (dotN psi1 psi1 + dotN psi2 psi2).scale cn := by
    refine ground.leB_congr ?_
      (BPair.scale_congr cn (BPair.add_congr (hone _) (hone _)))
      (truncation.cap_polar A cn cd spA spA' hA psi1 psi2 h1 h2
        (BPair.ofNat 1) (BPair.ofNat 1))
    rw [hdbl]
    exact BPair.scale_congr cd (BPair.add_congr (hone _) (hone _))
  have hcp2 : ((dotN psi1 (matVec A psi2)
        + dotN psi1 (matVec A psi2)).scale cd).swap
      ≤ (dotN psi1 psi1 + dotN psi2 psi2).scale cn := by
    refine ground.leB_congr ?_ ?_
      (truncation.cap_polar A cn cd spA spA' hA psi1 psi2 h1 h2
        (BPair.ofNat 1) (BPair.ofNat 1).swap)
    · rw [BPair.mul_swap, BPair.swap_mul, BPair.scale_swap, hdbl]
      exact ground.swap_congr
        (BPair.scale_congr cd (BPair.add_congr (hone _) (hone _)))
    · rw [BPair.swap_sq]
      exact BPair.scale_congr cn (BPair.add_congr (hone _) (hone _))
  have hA3mag : (windowsep.mag (dotN psi1 (matVec A psi2)
        + dotN psi1 (matVec A psi2))).scale cd
      ≤ (dotN psi1 psi1 + dotN psi2 psi2).scale cn := by
    rw [← windowsep.mag_scale]
    exact magLe hcp1 hcp2
  have b3a : (windowsep.mag (dotN psi1 (matVec A psi2)
        + dotN psi1 (matVec A psi2))).scale (cd * zd)
      ≤ BPair.ofPos cn * (zn + (dotN psi1 psi1).scale zd) := by
    rw [← BPair.scale_scale]
    exact ground.leB_trans
      (ground.leB_congr_right
        (BPair.oneValue_of_eq (BPair.scale_scale _ cn zd))
        (ground.leB_scale hA3mag zd))
      (gramCap (dotN psi1 psi1) (dotN psi2 psi2) zn cn zd hZ)
  have hcr := truncation.cap_read A cn cd spA spA' hA psi2 h2
  have hA4cd : (dotN psi2 (matVec A psi2)).scale cd
      ≤ (dotN psi2 psi2).scale cn :=
    ground.leB_congr (BPair.ofPos_scale cd _) (BPair.ofPos_scale cn _) hcr.1
  have hA4sw : ((dotN psi2 (matVec A psi2)).scale cd).swap
      ≤ (dotN psi2 psi2).scale cn :=
    ground.leB_congr (BPair.ofPos_scale cd _) (BPair.ofPos_scale cn _) hcr.2
  have hA4mag : (windowsep.mag (dotN psi2 (matVec A psi2))).scale cd
      ≤ (dotN psi2 psi2).scale cn := by
    rw [← windowsep.mag_scale]
    exact magLe hA4cd hA4sw
  have b4a : (windowsep.mag (dotN psi2 (matVec A psi2))).scale (cd * zd)
      ≤ BPair.ofPos cn * zn := by
    rw [← BPair.scale_scale]
    exact ground.leB_trans
      (ground.leB_congr_right
        (BPair.oneValue_of_eq (BPair.scale_scale _ cn zd))
        (ground.leB_scale hA4mag zd))
      (gramCapZ (dotN psi2 psi2) zn cn zd hZ)
  have hbg11 : (windowsep.mag (dotN psi1 psi1)).scale (cd * zd)
      ≤ BPair.ofPos cd * (dotN psi1 psi1).scale zd := by
    rw [windowsep.mag_unitLe hg11]
    exact ground.leB_congr_right (scaleRead (dotN psi1 psi1) cd zd)
      (ground.leB_refl _)
  have hbg22 : (windowsep.mag (dotN psi2 psi2)).scale (cd * zd)
      ≤ BPair.ofPos cd * zn := by
    rw [windowsep.mag_unitLe hg22]
    exact gramCapZ (dotN psi2 psi2) zn cd zd hZ
  have hbG : (windowsep.mag (dotN psi1 psi2 + dotN psi1 psi2)).scale (cd * zd)
      ≤ BPair.ofPos cd * (zn + (dotN psi1 psi1).scale zd) :=
    ground.leB_trans (ground.leB_scale hGle (cd * zd))
      (gramCap (dotN psi1 psi1) (dotN psi2 psi2) zn cd zd hZ)
  have hD : jetDisplay A psi0 psi1 psi2 p q
      = (dotN psi0 (matVec A psi0)).scale (Pos.pow q 4 * Pos.pow p 0)
        + (BPair.ofNat 2 * dotN psi0 (matVec A psi1)).scale
            (Pos.pow q 2 * Pos.pow p 2)
        + (BPair.ofNat 2 * dotN psi0 (matVec A psi2)
            + dotN psi1 (matVec A psi1)
            + (dotN psi0 (matVec A psi0) * dotN psi1 psi1).swap).scale
            (Pos.pow q 0 * Pos.pow p 4) := by
    rw [← s0read p q, ← s1read p q, ← s2read p q]
    exact rfl
  have hT : (BPair.ofNat 2 * dotN psi0 (matVec A psi2)
        + dotN psi1 (matVec A psi1)).oneValue
      ((BPair.ofNat 2 * dotN psi0 (matVec A psi2)
          + dotN psi1 (matVec A psi1)
          + (dotN psi0 (matVec A psi0) * dotN psi1 psi1).swap)
          * BPair.ofNat 1
        + dotN psi0 (matVec A psi0) * dotN psi1 psi1) :=
    BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_ofNat_one _) (BPair.oneValue_refl _))
        (BPair.add_swap_self _ _))
  have hV := BPair.oneValue_trans
    (BPair.add_congr
      (BPair.scale_congr (Pos.pow q 4 * Pos.pow p 0)
        (jetQuad A hAr hAl hsymA psi0 psi1 psi2 h0 h1 h2 p q))
      (ground.swap_congr
        (BPair.mul_congr (BPair.oneValue_of_eq hD)
          (jetGram psi0 psi1 psi2 h0 h1 h2 h00 h01 h02 p q))))
    (tailId (dotN psi0 (matVec A psi0))
      (BPair.ofNat 2 * dotN psi0 (matVec A psi1))
      (BPair.ofNat 2 * dotN psi0 (matVec A psi2) + dotN psi1 (matVec A psi1)
        + (dotN psi0 (matVec A psi0) * dotN psi1 psi1).swap)
      (BPair.ofNat 2 * dotN psi0 (matVec A psi2) + dotN psi1 (matVec A psi1))
      (dotN psi1 (matVec A psi2) + dotN psi1 (matVec A psi2))
      (dotN psi2 (matVec A psi2)) (BPair.ofNat 1) (dotN psi1 psi1)
      (dotN psi1 psi2 + dotN psi1 psi2) (dotN psi2 psi2) p q hT
      (BPair.oneValue_symm (BPair.mul_ofNat_one _))
      (BPair.oneValue_symm (BPair.mul_ofNat_one _)))
  have hBig : (dotN (jetVec p q psi0 psi1 psi2)
          (matVec A (jetVec p q psi0 psi1 psi2))).scale
          (Pos.pow q 4 * (cd * zd))
        + ((jetDisplay A psi0 psi1 psi2 p q
            * dotN (jetVec p q psi0 psi1 psi2)
                (jetVec p q psi0 psi1 psi2)).scale (cd * zd)).swap
      = ((dotN (jetVec p q psi0 psi1 psi2)
              (matVec A (jetVec p q psi0 psi1 psi2))).scale
              (Pos.pow q 4 * Pos.pow p 0)
            + (jetDisplay A psi0 psi1 psi2 p q
                * dotN (jetVec p q psi0 psi1 psi2)
                    (jetVec p q psi0 psi1 psi2)).swap).scale (cd * zd) := by
    rw [← s0read p q, BPair.scale_add, BPair.scale_scale, BPair.scale_swap]
  rw [hBig, windowsep.mag_scale]
  refine ground.leB_congr_left
    (BPair.scale_congr (cd * zd)
      (BPair.oneValue_symm (windowsep.mag_congr hV))) ?_
  exact magClose cn cd zd
    (dotN psi1 (matVec A psi2) + dotN psi1 (matVec A psi2))
    (dotN psi2 (matVec A psi2)) (dotN psi0 (matVec A psi0))
    (BPair.ofNat 2 * dotN psi0 (matVec A psi1))
    (BPair.ofNat 2 * dotN psi0 (matVec A psi2) + dotN psi1 (matVec A psi1)
      + (dotN psi0 (matVec A psi0) * dotN psi1 psi1).swap)
    (dotN psi1 psi1) (dotN psi1 psi2 + dotN psi1 psi2) (dotN psi2 psi2) zn
    (Pos.pow q 6 * Pos.pow p 6) (Pos.pow q 4 * Pos.pow p 8)
    (q * q * Pos.pow p 10) (Pos.pow p 12)
    b3a
    (prodBound _ _ _ cd zd hbG)
    (prodBound _ _ _ cd zd hbg11)
    b4a
    (prodBound _ _ _ cd zd hbg22)
    (prodBound _ _ _ cd zd hbG)
    (prodBound _ _ _ cd zd hbg11)
    (prodBound _ _ _ cd zd hbg22)
    (prodBound _ _ _ cd zd hbG)
    (prodBound _ _ _ cd zd hbg22)


/-! `lem:fourpoint`'s tail closed: the drift, the residual's cap and the
jet's floor joined at the transport display's width read. -/

/-- A clearing's two trailing factors exchange. -/
private theorem posMove (x a b : Pos) : x * (a * b) = x * b * a := by
  rw [ground.mul_comm a b, ← ground.mul_assoc]

/-- The leading factor moves to the tail. -/
private theorem posLead (a b c : Pos) : a * b * c = b * c * a := by
  rw [ground.mul_assoc, ground.mul_comm]

/-- The outer factors exchange across a middle one. -/
private theorem posEnds (x g y : Pos) : x * (g * y) = y * (g * x) := by
  rw [ground.mul_comm g y, ← ground.mul_assoc, ground.mul_comm x y,
    ground.mul_assoc, ground.mul_comm x g]

/-- The residual cap's weight sorted: the root cap's square against the
level's clearing, the drift's clearing and the tie's clearing. -/
private theorem posCapread (Kn p gd cc : Pos) :
    Kn * Kn * (Pos.pow p 12 * (gd * gd * (cc * cc)))
      = cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd) := by
  rw [ground.mul_assoc (cc * cc) (Pos.pow p 12) (Kn * Kn),
    ground.mul_assoc (cc * cc) (Pos.pow p 12 * (Kn * Kn)) (gd * gd),
    ground.mul_assoc (Pos.pow p 12) (Kn * Kn) (gd * gd),
    ground.mul_left_comm (Kn * Kn) (Pos.pow p 12) (gd * gd * (cc * cc)),
    ground.mul_left_comm (cc * cc) (Pos.pow p 12) (Kn * Kn * (gd * gd)),
    ground.mul_left_comm (cc * cc) (Kn * Kn) (gd * gd),
    ground.mul_comm (gd * gd) (cc * cc)]

/-- The width's square at the sorted weight: the display's numerator
`γ' τ⁶ K(τ)` squared against the clearance's clearing. -/
private theorem posWidthread (gn cc p Kn gd : Pos) :
    gn * cc * Pos.pow p 6 * Kn * (gn * cc * Pos.pow p 6 * Kn) * (gd * gd)
      = gn * gn * (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd)) := by
  rw [ground.mul_mul_mul_comm (gn * cc * Pos.pow p 6) Kn
      (gn * cc * Pos.pow p 6) Kn,
    ground.mul_mul_mul_comm (gn * cc) (Pos.pow p 6) (gn * cc) (Pos.pow p 6),
    ground.mul_mul_mul_comm gn cc gn cc, ← Pos.pow_add p 6 6,
    ground.mul_assoc (gn * gn) (cc * cc) (Pos.pow p 12),
    ground.mul_assoc (gn * gn) (cc * cc * Pos.pow p 12) (Kn * Kn),
    ground.mul_assoc (gn * gn) (cc * cc * Pos.pow p 12 * (Kn * Kn)) (gd * gd)]

/-- The drift's clearing carried to the display's denominator,
`(dp)²τ⁴ · γ'²τ⁸ = γ'²(dp τ⁶)²`. -/
private theorem posDriftread (dpv q gn : Pos) :
    dpv * dpv * Pos.pow q 4 * (gn * gn * Pos.pow q 8)
      = gn * gn * (dpv * Pos.pow q 6 * (dpv * Pos.pow q 6)) := by
  rw [ground.mul_mul_mul_comm (dpv * dpv) (Pos.pow q 4) (gn * gn)
      (Pos.pow q 8),
    ground.mul_mul_mul_comm dpv (Pos.pow q 6) dpv (Pos.pow q 6),
    ← Pos.pow_add q 4 8, ← Pos.pow_add q 6 6,
    ground.mul_comm (dpv * dpv) (gn * gn), ground.mul_assoc]

/-- The one-member sites join at the summed site. -/
private theorem ofPosAdd (a b : Pos) :
    (BPair.ofPos a + BPair.ofPos b).oneValue (BPair.ofPos (a + b)) := by
  show a + Pos.one + (b + Pos.one) + Pos.one
    = a + b + Pos.one + (Pos.one + Pos.one)
  rw [ground.add_add_comm a Pos.one b Pos.one,
    ground.add_assoc (a + b) (Pos.one + Pos.one) Pos.one,
    ground.add_assoc (a + b) Pos.one (Pos.one + Pos.one),
    ground.add_assoc Pos.one Pos.one Pos.one]

/-- The jet's floor: with `ψ₁`, `ψ₂` off the head's line and the head at
the unit gram, the jet's self-pairing sits at or above the head's own
clearing `τ⁸`, the two cross terms reading the sum's unit and the
off-line part's self-pairing at or above it. -/
private theorem jetFloor {n : Nat} (one psi1 psi2 : List BPair)
    (h1 : one.length = n) (h2 : psi1.length = n) (h3 : psi2.length = n)
    (hperp1 : (dotN psi1 one).oneValue BPair.unit)
    (hperp2 : (dotN psi2 one).oneValue BPair.unit)
    (h11 : (dotN one one).oneValue (BPair.ofNat 1)) (p q : Pos) :
    BPair.ofPos (Pos.pow q 8)
      ≤ dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2) := by
  have hu : (vecScale (BPair.ofPos (Pos.pow q 4)) one).length = n := by
    rw [length_vecScale]; exact h1
  have hv : (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
      (vecScale (BPair.ofPos (Pos.pow p 4)) psi2)).length = n :=
    length_vecAdd _ _ n ((length_vecScale _ psi1).trans h2)
      ((length_vecScale _ psi2).trans h3)
  have hone : (dotN one (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
      (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))).oneValue BPair.unit := by
    refine BPair.oneValue_trans
      (dotN_addRow_right one _ _
        ((length_vecScale _ psi1).trans (h2.trans h1.symm))
        ((length_vecScale _ psi2).trans (h3.trans h1.symm))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (dotN_scaleV _ one psi1) (dotN_scaleV _ one psi2)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans (dotN_comm one psi1) hperp1))
          (BPair.mul_unit _))
        (BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl _)
            (BPair.oneValue_trans (dotN_comm one psi2) hperp2))
          (BPair.mul_unit _))) ?_
    exact BPair.unit_add BPair.unit
  have euu : (dotN (vecScale (BPair.ofPos (Pos.pow q 4)) one)
      (vecScale (BPair.ofPos (Pos.pow q 4)) one)).oneValue
      (BPair.ofPos (Pos.pow q 8)) := by
    refine BPair.oneValue_trans (dotN_vecScale_self _ one) ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.ofPos_mul (Pos.pow q 4) (Pos.pow q 4)) h11) ?_
    rw [← Pos.pow_add q 4 4]
    exact BPair.mul_ofNat_one _
  have euV : (dotN (vecScale (BPair.ofPos (Pos.pow q 4)) one)
      (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
        (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))).oneValue BPair.unit :=
    BPair.oneValue_trans (dotN_scaleRow_free _ one _)
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) hone) (BPair.mul_unit _))
  have eVu : (dotN (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
        (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))
      (vecScale (BPair.ofPos (Pos.pow q 4)) one)).oneValue BPair.unit :=
    BPair.oneValue_trans (dotN_comm _ _) euV
  have hVV : BPair.unit ≤ dotN
      (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
        (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))
      (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
        (vecScale (BPair.ofPos (Pos.pow p 4)) psi2)) :=
    ground.leB_of_not_lt (dotN_self_side _)
  have hJJ : (dotN (jetVec p q one psi1 psi2)
      (jetVec p q one psi1 psi2)).oneValue
      (BPair.ofPos (Pos.pow q 8)
        + dotN (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
            (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))
          (vecAdd (vecScale (BPair.ofPos (p * p * (q * q))) psi1)
            (vecScale (BPair.ofPos (Pos.pow p 4)) psi2))) := by
    refine BPair.oneValue_trans (sumSelf _ _ hu hv) ?_
    exact BPair.add_congr
      (BPair.oneValue_trans (BPair.add_congr euu euV) (BPair.add_unit _))
      (BPair.oneValue_trans (BPair.add_congr eVu (BPair.oneValue_refl _))
        (BPair.unit_add _))
  refine ground.leB_congr_right (BPair.oneValue_symm hJJ) ?_
  exact ground.leB_congr_left (BPair.add_unit (BPair.ofPos (Pos.pow q 8)))
    (ground.leB_add (ground.leB_refl _) hVV)

/-- The first root cap's monomial at the joined cap's leading square. -/
private theorem posK0read (K0 p q : Pos) :
    16 * (K0 * K0) * (Pos.pow q 4 * Pos.pow p 12)
      = 16 * (K0 * (q * q) * (K0 * (q * q))) * Pos.pow p 12 := by
  rw [ground.mul_mul_mul_comm K0 (q * q) K0 (q * q), posSq q,
    ← Pos.pow_add q 2 2, ← ground.mul_assoc (16 : Pos) (K0 * K0) (Pos.pow q 4),
    ground.mul_assoc (16 * (K0 * K0)) (Pos.pow q 4) (Pos.pow p 12)]

/-- The second root cap's monomial at the joined cap's trailing square. -/
private theorem posK1read (K1 p : Pos) :
    16 * (K1 * K1) * Pos.pow p 16
      = 16 * (K1 * (p * p) * (K1 * (p * p))) * Pos.pow p 12 := by
  rw [ground.mul_mul_mul_comm K1 (p * p) K1 (p * p), posSq p,
    ← Pos.pow_add p 2 2, ← ground.mul_assoc (16 : Pos) (K1 * K1) (Pos.pow p 4),
    ground.mul_assoc (16 * (K1 * K1)) (Pos.pow p 4) (Pos.pow p 12),
    ← Pos.pow_add p 4 12]

/-- The joined cap's square splits at the two squares and the cross
term. -/
private theorem posSqSum (a b P : Pos) :
    16 * (a * a) * P + 16 * (b * b) * P + 16 * (a * b + b * a) * P
      = 16 * ((a + b) * (a + b)) * P := by
  rw [ground.left_distrib (a + b) a b, ground.right_distrib a b a,
    ground.right_distrib a b b,
    ground.left_distrib (16 : Pos) (a * a + b * a) (a * b + b * b),
    ground.right_distrib (16 * (a * a + b * a)) (16 * (a * b + b * b)) P,
    ground.left_distrib (16 : Pos) (a * a) (b * a),
    ground.left_distrib (16 : Pos) (a * b) (b * b),
    ground.right_distrib (16 * (a * a)) (16 * (b * a)) P,
    ground.right_distrib (16 * (a * b)) (16 * (b * b)) P,
    ground.left_distrib (16 : Pos) (a * b) (b * a),
    ground.right_distrib (16 * (a * b)) (16 * (b * a)) P,
    ground.add_assoc (16 * (a * a) * P) (16 * (b * b) * P)
      (16 * (a * b) * P + 16 * (b * a) * P),
    ground.add_assoc (16 * (a * a) * P) (16 * (b * a) * P)
      (16 * (a * b) * P + 16 * (b * b) * P),
    ground.add_left_comm (16 * (b * a) * P) (16 * (a * b) * P)
      (16 * (b * b) * P),
    ground.add_left_comm (16 * (b * b) * P) (16 * (a * b) * P)
      (16 * (b * a) * P),
    ground.add_comm (16 * (b * b) * P) (16 * (b * a) * P)]

/-- The two root caps' folds sit under the joined cap `K(τ) = K₀ + τ²K₁`
squared, the cross term the margin. -/
private theorem posCapSum (K0 K1 p q : Pos) :
    16 * (K0 * K0) * (Pos.pow q 4 * Pos.pow p 12)
        + 16 * (K1 * K1) * Pos.pow p 16
      ≤ 16 * ((K0 * (q * q) + K1 * (p * p)) * (K0 * (q * q) + K1 * (p * p)))
          * Pos.pow p 12 := by
  rw [posK0read K0 p q, posK1read K1 p,
    ← posSqSum (K0 * (q * q)) (K1 * (p * p)) (Pos.pow p 12)]
  exact ground.posLeSelfAdd _ _

/-- The residual's weight at the two root caps: with `K₀`, `K₁` clearing
the residual weight's two folds, the residual's self-pairing sits under
the joined cap's square, `⟨ρ,ρ⟩ ≤ 16 K(τ)² τ¹²` at the display's
clearing. -/
private theorem residCap {n : Nat} (M : Mat) (hM : sqAt M n)
    (psi1 psi2 : List BPair) (h2 : psi1.length = n) (h3 : psi2.length = n)
    (np : Nat) (p q : Pos) (W : Pos) (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL)
    (K0 K1 : Pos)
    (hK0 : BPair.ofNat (4 * (np * np)) * dotN psi1 psi1
        + BPair.ofPos (64 * (W * W)) * dotN psi2 psi2
        ≤ BPair.ofPos (16 * (K0 * K0)))
    (hK1 : BPair.ofNat (2 * (np * np)) * dotN psi2 psi2
        ≤ BPair.ofPos (16 * (K1 * K1))) :
    dotN (residVec p q np M psi1 psi2) (residVec p q np M psi1 psi2)
      ≤ (BPair.ofPos (16 * ((K0 * (q * q) + K1 * (p * p))
          * (K0 * (q * q) + K1 * (p * p))))).scale (Pos.pow p 12) := by
  have hstep : (BPair.ofNat (4 * (np * np)) * dotN psi1 psi1).scale
        (Pos.pow q 4 * Pos.pow p 12)
      + (BPair.ofPos (64 * (W * W)) * dotN psi2 psi2).scale
        (Pos.pow q 4 * Pos.pow p 12)
      + (BPair.ofNat (2 * (np * np)) * dotN psi2 psi2).scale (Pos.pow p 16)
      ≤ (BPair.ofPos (16 * (K0 * K0))).scale (Pos.pow q 4 * Pos.pow p 12)
        + (BPair.ofPos (16 * (K1 * K1))).scale (Pos.pow p 16) :=
    ground.leB_add
      (ground.leB_congr_left
        (BPair.oneValue_of_eq
          (BPair.scale_add _ _ (Pos.pow q 4 * Pos.pow p 12)))
        (ground.leB_scale hK0 (Pos.pow q 4 * Pos.pow p 12)))
      (ground.leB_scale hK1 (Pos.pow p 16))
  refine ground.leB_trans
    (residWeight M hM psi1 psi2 h2 h3 np p q W spU spL hcapM)
    (ground.leB_trans hstep ?_)
  refine ground.leB_congr
    (BPair.oneValue_symm
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.scale_ofPos (16 * (K0 * K0)) (Pos.pow q 4 * Pos.pow p 12))
          (BPair.scale_ofPos (16 * (K1 * K1)) (Pos.pow p 16)))
        (ofPosAdd _ _)))
    (BPair.oneValue_symm (BPair.scale_ofPos _ (Pos.pow p 12)))
    (ground.leB_ofPos (posCapSum K0 K1 p q))

/-- The transport display's own comparison: the drift's read at the
cleared level, the residual's cap and the jet's floor compose to the
width's squared display, `γ'²(dp τ⁶)²⟨φ,φ⟩ ≤ (γ' τ⁶ K(τ))² γ_d² s²⟨J,J⟩`
at the ground column's self-pairing `s`. -/
private theorem driftTrans {Phi s RR JJ : BPair} {dpv gd cc Kn gn p q : Pos}
    (hdrift : (BPair.ofPos dpv * BPair.ofPos dpv * Phi).scale (16 * Pos.pow q 4)
        ≤ (s * s * RR).scale (gd * gd * (cc * cc)))
    (hRR : RR ≤ (BPair.ofPos (16 * (Kn * Kn))).scale (Pos.pow p 12))
    (hss : BPair.unit ≤ s * s)
    (hJJ : BPair.ofPos (Pos.pow q 8) ≤ JJ) :
    Phi.scale (gn * gn * (dpv * Pos.pow q 6 * (dpv * Pos.pow q 6)))
      ≤ (s * s * JJ).scale
          (gn * cc * Pos.pow p 6 * Kn * (gn * cc * Pos.pow p 6 * Kn)
            * (gd * gd)) := by
  have eL : ((BPair.ofPos dpv * BPair.ofPos dpv * Phi).scale
      (16 * Pos.pow q 4)).oneValue
      (Phi.scale (dpv * dpv * Pos.pow q 4 * 16)) := by
    refine BPair.oneValue_trans
      (BPair.scale_congr (16 * Pos.pow q 4)
        (BPair.oneValue_trans (BPair.mul_congr_left (BPair.ofPos_mul dpv dpv))
          (BPair.ofPos_scale (dpv * dpv) Phi))) ?_
    rw [BPair.scale_scale, posMove]
    exact BPair.oneValue_refl _
  have h1 : Phi.scale (dpv * dpv * Pos.pow q 4 * 16)
      ≤ (s * s * RR).scale (gd * gd * (cc * cc)) :=
    ground.leB_congr_left eL hdrift
  have h2 : (s * s * RR).scale (gd * gd * (cc * cc))
      ≤ (s * s).scale (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd) * 16) := by
    refine ground.leB_congr_right ?_
      (ground.leB_scale (ground.leB_mulR hss hRR) (gd * gd * (cc * cc)))
    rw [BPair.mul_scale, BPair.scale_scale,
      BPair.mul_comm (s * s) (BPair.ofPos (16 * (Kn * Kn)))]
    refine BPair.oneValue_trans
      (BPair.scale_congr _ (BPair.ofPos_scale (16 * (Kn * Kn)) (s * s))) ?_
    rw [BPair.scale_scale, posLead, posCapread]
    exact BPair.oneValue_refl _
  have h4 : Phi.scale (dpv * dpv * Pos.pow q 4)
      ≤ (s * s).scale (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd)) := by
    refine ground.leB_of_scale (w := 16) ?_
    rw [BPair.scale_scale, BPair.scale_scale]
    exact ground.leB_trans h1 h2
  have h5 := ground.leB_scale h4 (gn * gn * Pos.pow q 8)
  rw [BPair.scale_scale, BPair.scale_scale,
    posEnds (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd)) (gn * gn)
      (Pos.pow q 8), posDriftread] at h5
  have eA : (((s * s) * BPair.ofPos (Pos.pow q 8)).scale
        (gn * gn * (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd)))).oneValue
      ((s * s).scale (Pos.pow q 8
        * (gn * gn * (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd))))) := by
    rw [BPair.mul_comm (s * s) (BPair.ofPos (Pos.pow q 8))]
    exact BPair.oneValue_trans
      (BPair.scale_congr _ (BPair.ofPos_scale (Pos.pow q 8) (s * s)))
      (BPair.oneValue_of_eq (BPair.scale_scale (s * s) (Pos.pow q 8) _))
  have eB : (((s * s) * JJ).scale
        (gn * gn * (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd)))).oneValue
      ((s * s * JJ).scale
        (gn * cc * Pos.pow p 6 * Kn * (gn * cc * Pos.pow p 6 * Kn)
          * (gd * gd))) :=
    BPair.oneValue_of_eq
      (congrArg (BPair.scale (s * s * JJ)) (posWidthread gn cc p Kn gd).symm)
  exact ground.leB_trans h5
    (ground.leB_congr eA eB
      (ground.leB_scale (ground.leB_mulR hss hJJ)
        (gn * gn * (cc * cc * Pos.pow p 12 * (Kn * Kn) * (gd * gd)))))

/-- The moments' brackets at the jet (`lem:fourpoint`'s tail): at the jet's
data — the reads `E𝟏 = 0`, `Eψ₁ = M𝟏`, `4Eψ₂ + #p𝟏 = 4Mψ₁`, `ψ₁` and `ψ₂` off
the unit line with `⟨𝟏,𝟏⟩ = 1` — the level gap's data with the clearance
`[gn : gd]`, the drift's clearing as the positive datum `dp` at
`⟨γ' : τ²W⟩ = dp`, and the root caps `K₀`, `K₁` whose squares clear the
residual weight's two folds, each observable's bracket is the transport
display's width read at the jet as the later ground, one polarization at the
observable's cap `[cn : cd]`: `γ'|ω(A) − ω̂(A)| ≤ 4c_A w` at
`w = γ' τ⁶ K(τ) / ⟨γ' : τ²W⟩`, `K(τ) = K₀ + τ²K₁`, the display cleared. -/
theorem momentBracket {n : Nat} (E M Et : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (T Tw : SqMat n) (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0 = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : groundreads.clearRead l j0 gn gd)
    (p q c : Pos) (e0 : BPair)
    (htie : matOneValue Et
      (siteDatum (matScale c (rayH p q E M)) (matScaleB e0 (idMat n))))
    (spE : Split n) (hEs : splitRead E spE) (hEp : psdAt spE)
    (W : Pos) (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL)
    (one psi1 psi2 : List BPair) (h1 : one.length = n) (h2 : psi1.length = n)
    (h3 : psi2.length = n) (np : Nat)
    (hE0 : poly.unitTail (matVec E one))
    (hE1 : poly.oneValue (matVec E psi1) (matVec M one))
    (hE2 : poly.oneValue
      (vecAdd (vecScale (BPair.ofNat 4) (matVec E psi2)) (vecScale (BPair.ofNat np) one))
      (vecScale (BPair.ofNat 4) (matVec M psi1)))
    (hperp1 : (dotN psi1 one).oneValue BPair.unit)
    (hperp2 : (dotN psi2 one).oneValue BPair.unit)
    (h11 : (dotN one one).oneValue (BPair.ofNat 1))
    (dp : Pos)
    (hdp : (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap).oneValue (BPair.ofPos dp))
    (K0 K1 : Pos)
    (hK0 : BPair.ofNat (4 * (np * np)) * dotN psi1 psi1
        + BPair.ofPos (64 * (W * W)) * dotN psi2 psi2 ≤ BPair.ofPos (16 * (K0 * K0)))
    (hK1 : BPair.ofNat (2 * (np * np)) * dotN psi2 psi2 ≤ BPair.ofPos (16 * (K1 * K1)))
    (A : Mat) (cn cd : Pos) (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA') :
    (windowsep.mag (groundreads.readGap
        (groundreads.read A (matVec T.val (elim.idRow n j0)))
        (groundreads.read A (jetVec p q one psi1 psi2)))).scale
        (gn * (dp * Pos.pow q 6) * cd)
      ≤ (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)).scale
        (4 * (cn * (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p))) * gd)) := by
  have hpsi : (matVec T.val (elim.idRow n j0)).length = n := by
    rw [matVec_length]; exact SqMat.rows T
  have hJl : (jetVec p q one psi1 psi2).length = n :=
    length_vecAdd _ _ n ((length_vecScale _ one).trans h1)
      (length_vecAdd _ _ n ((length_vecScale _ psi1).trans h2)
        ((length_vecScale _ psi2).trans h3))
  have hRl : (residVec p q np M psi1 psi2).length = n :=
    length_vecAdd _ _ n ((length_vecScale _ psi1).trans h2)
      (length_vecAdd _ _ n
        (by
          rw [ground.length_map, length_vecScale, matVec_length]
          exact sqAt_len hM)
        ((length_vecScale _ psi2).trans h3))
  have hside : BPair.ofPos (gd * c * (p * p) * W) < BPair.ofPos gn := by
    have hlt : BPair.unit < BPair.ofPos gn
        + (BPair.ofPos (gd * c * (p * p) * W)).swap :=
      BPair.lt_congr (BPair.oneValue_refl BPair.unit) (BPair.oneValue_symm hdp)
        (ground.unitLtOfPos dp)
    have h := ground.swapLt_of_unitLt hlt
    rw [BPair.swap_swap] at h
    exact h
  have hdrift0 := offLine_drift E M Et hE hM T Tw l hd j0 hj0 d0 g0 hroot0
    gn gd hcl p q c e0 htie spE hEs hEp W spU spL hcapM np
    (jetVec p q one psi1 psi2) (residVec p q np M psi1 psi2) hJl hRl
    (jetResidual E M hE hM one psi1 psi2 h1 h2 h3 np p q hE0 hE1 hE2) hside
  have hdrift : (BPair.ofPos dp * BPair.ofPos dp
        * dotN (residD [matVec T.val (elim.idRow n j0)] (jetVec p q one psi1 psi2))
          (residD [matVec T.val (elim.idRow n j0)]
            (jetVec p q one psi1 psi2))).scale (16 * Pos.pow q 4)
      ≤ (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN (residVec p q np M psi1 psi2)
            (residVec p q np M psi1 psi2)).scale (gd * gd * (c * c)) :=
    ground.leB_congr_left
      (BPair.scale_congr (16 * Pos.pow q 4)
        (BPair.mul_congr_left (BPair.mul_congr hdp hdp))) hdrift0
  have htrans := driftTrans (gn := gn) hdrift
    (residCap M hM psi1 psi2 h2 h3 np p q W spU spL hcapM K0 K1 hK0 hK1)
    (ground.unitLeSq (dotN (matVec T.val (elim.idRow n j0))
      (matVec T.val (elim.idRow n j0))))
    (jetFloor one psi1 psi2 h1 h2 h3 hperp1 hperp2 h11 p q)
  have hs : BPair.unit < dotN (matVec T.val (elim.idRow n j0))
      (matVec T.val (elim.idRow n j0)) :=
    (groundreads.ground_column Et T Tw l hd j0 hj0 d0 g0 hroot0).2.2
  refine Decidable.byCases
    (p := BPair.ofPos (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p)) * gd)
      ≤ BPair.ofPos (gn * (dp * Pos.pow q 6)))
    (fun hw => groundreads.readClose A cn cd spA spA' hA
      (matVec T.val (elim.idRow n j0)) (jetVec p q one psi1 psi2) hpsi hJl
      gn gd (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p)))
      (dp * Pos.pow q 6) hw hs htrans)
    (fun hw => groundreads.readCrude A cn cd spA spA' hA
      (matVec T.val (elim.idRow n j0)) (jetVec p q one psi1 psi2) hpsi hJl
      gn gd (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p)))
      (dp * Pos.pow q 6)
      (ground.leB_of_lt (Decidable.of_not_not (fun hnn =>
        hw (ground.leB_of_not_lt hnn)))))

/-! The fold's bracket tier: the magnitude at the composite pair
carrier, the telescoping identity of a two-factor product's gap, and
the per-factor step at the caps — a moment product's gap collects one
move per factor at the datum, each move the factor's own gap against
the other factors' caps. -/

/-- The magnitude at the composite pair: the balance member's own at
the clearing kept. -/
private def magQ (x : BPair × Pos) : BPair × Pos := (windowsep.mag x.1, x.2)

private theorem magQ_nn (x : BPair × Pos) : BPair.unit ≤ (magQ x).1 :=
  windowsep.unitLe_mag x.1

private theorem magQ_unit : magQ bpairQOps.unit = bpairQOps.unit := by
  show (windowsep.mag BPair.unit, Pos.one) = (BPair.unit, Pos.one)
  rw [windowsep.mag_unitLe (leB_refl BPair.unit)]

private theorem magQ_congr {x y : BPair × Pos} (h : bpairQRead.rel x y) :
    bpairQRead.rel (magQ x) (magQ y) := by
  have h' := windowsep.mag_congr h
  rw [windowsep.mag_scale, windowsep.mag_scale] at h'
  exact h'

private theorem magQ_swap (x : BPair × Pos) :
    magQ (bpairQOps.swap x) = magQ x := by
  show (windowsep.mag x.1.swap, x.2) = (windowsep.mag x.1, x.2)
  rw [windowsep.mag_swap]

/-- The magnitude is multiplicative at the composite pair. -/
private theorem magQ_mul (x y : BPair × Pos) :
    bpairQRead.rel (magQ (bpairQOps.mul x y)) (bpairQOps.mul (magQ x) (magQ y)) :=
  BPair.scale_congr (x.2 * y.2) (windowsep.mag_mul x.1 y.1)

/-- The magnitude is subadditive at the composite pair. -/
private theorem magQ_add (x y : BPair × Pos) :
    qle (magQ (BPair.addQ x y)) (BPair.addQ (magQ x) (magQ y)) := by
  have h := windowsep.mag_add_le (x.1.scale y.2) (y.1.scale x.2)
  rw [windowsep.mag_scale, windowsep.mag_scale] at h
  exact leB_scale h (x.2 * y.2)

private theorem qle_refl (p : BPair × Pos) : qle p p := leB_refl _

/-- The product's two-sided comparison at a first upper datum and a
second lower datum from the sum's unit. -/
private theorem qle_mul_mono {p q p' q' : BPair × Pos}
    (hq : BPair.unit ≤ q.1) (hp' : BPair.unit ≤ p'.1)
    (h : qle p q) (h' : qle p' q') :
    qle (bpairQOps.mul p p') (bpairQOps.mul q q') := by
  show (p.1 * p'.1).scale (q.2 * q'.2) ≤ (q.1 * q'.1).scale (p.2 * p'.2)
  rw [BPair.scale_mul, BPair.scale_mul]
  exact leB_mul_mono (scale_nn hp' q'.2) (scale_nn hq p.2) h h'

private theorem qle_add_mono2 {a b a' b' : BPair × Pos}
    (h : qle a b) (h' : qle a' b') : qle (BPair.addQ a a') (BPair.addQ b b') :=
  qle_trans (qle_add_mono a h')
    (qle_congr_left (BPair.addQ_comm b' a)
      (qle_congr_right (BPair.addQ_comm b' b) (qle_add_mono b' h)))

/-- The natural weights at two counts join at the summed count. -/
private theorem nsmul_add (x : BPair × Pos) (j : Nat) : ∀ k : Nat,
    bpairQRead.rel
      (BPair.addQ (poly.nsmulO bpairQOps x j) (poly.nsmulO bpairQOps x k))
      (poly.nsmulO bpairQOps x (j + k))
  | 0 => BPair.addQ_unitR _
  | k + 1 =>
    qOneValue_trans (qadd_rot _ x _) (BPair.addQ_congr (qOneValue_refl x) (nsmul_add x j k))

/-- The weight of a weight is the weight at the counts' product. -/
private theorem nsmul_flat (x : BPair × Pos) (k : Nat) : ∀ w : Nat,
    bpairQRead.rel (poly.nsmulO bpairQOps (poly.nsmulO bpairQOps x k) w)
      (poly.nsmulO bpairQOps x (k * w))
  | 0 => qOneValue_refl _
  | w + 1 =>
    qOneValue_trans (BPair.addQ_comm _ _)
      (qOneValue_trans (BPair.addQ_congr (nsmul_flat x k w) (qOneValue_refl _))
        (nsmul_add x (k * w) k))

private theorem qswap_mul (p q : BPair × Pos) :
    bpairQOps.mul (bpairQOps.swap p) q = bpairQOps.swap (bpairQOps.mul p q) := by
  show (p.1.swap * q.1, p.2 * q.2) = ((p.1 * q.1).swap, p.2 * q.2)
  rw [BPair.swap_mul]

/-- A product reads its first member's factor at the clearing moved. -/
private theorem qmul_qdiv (p s : BPair × Pos) :
    bpairQOps.mul p s = qdiv (bpairQOps.mul (p.1, Pos.one) s) p.2 := by
  show (p.1 * s.1, p.2 * s.2) = (p.1 * s.1, Pos.one * s.2 * p.2)
  rw [ground.one_mul, ground.mul_comm s.2 p.2]

/-- The product distributes over the join at the composite pair. -/
private theorem qmul_addQ (p q r : BPair × Pos) :
    bpairQRead.rel (bpairQOps.mul p (BPair.addQ q r))
      (BPair.addQ (bpairQOps.mul p q) (bpairQOps.mul p r)) := by
  rw [qmul_qdiv p (BPair.addQ q r), qmul_qdiv p q, qmul_qdiv p r]
  exact qOneValue_trans (qdiv_congr p.2 (qmul_add p.1 q r)) (qdiv_add _ _ p.2)

/-- The telescoping identity at two factors: the product's gap is the
first factor's gap against the second joined to the first's partner
against the second's gap, `xX − yY = (x − y)X + y(X − Y)`. -/
private theorem teleQ (x y X Y : BPair × Pos) :
    bpairQRead.rel
      (BPair.addQ (bpairQOps.mul X (BPair.addQ x (bpairQOps.swap y)))
        (bpairQOps.mul y (BPair.addQ X (bpairQOps.swap Y))))
      (BPair.addQ (bpairQOps.mul x X) (bpairQOps.swap (bpairQOps.mul y Y))) := by
  have e1 : bpairQOps.mul X x = bpairQOps.mul x X := qmul_comm X x
  have e2 : bpairQOps.mul X (bpairQOps.swap y)
      = bpairQOps.swap (bpairQOps.mul y X) := by
    rw [qmul_comm X (bpairQOps.swap y), qswap_mul y X]
  have e3 : bpairQOps.mul y (bpairQOps.swap Y)
      = bpairQOps.swap (bpairQOps.mul y Y) := by
    rw [qmul_comm y (bpairQOps.swap Y), qswap_mul Y y, qmul_comm Y y]
  refine qOneValue_trans (BPair.addQ_congr (qmul_addQ X x (bpairQOps.swap y))
    (qmul_addQ y X (bpairQOps.swap Y))) ?_
  rw [e1, e2, e3]
  refine qOneValue_trans (BPair.addQ_congr (qOneValue_refl _)
    (BPair.addQ_comm (bpairQOps.mul y X) (bpairQOps.swap (bpairQOps.mul y Y)))) ?_
  refine qOneValue_trans (BPair.addQ_add_comm _ _ _ _) ?_
  exact qaddR (qOneValue_refl _)
    (qOneValue_trans (BPair.addQ_comm _ _) (qadd_neg (bpairQOps.mul y X)))

/-- A cap at one key against a datum cleared at the summed key reads
the datum at the remaining key. -/
private theorem capDiv (d : Pos) (Z : BPair × Pos) (m e : Nat) :
    bpairQRead.rel
      (bpairQOps.mul (BPair.ofPos (Pos.pow d m), Pos.one)
        (qdiv Z (Pos.pow d (m + e))))
      (qdiv Z (Pos.pow d e)) := by
  show ((BPair.ofPos (Pos.pow d m) * Z.1).scale (Z.2 * Pos.pow d e)).oneValue
    (Z.1.scale (Pos.one * (Z.2 * Pos.pow d (m + e))))
  rw [Pos.pow_add, ground.one_mul,
    ground.mul_left_comm Z.2 (Pos.pow d m) (Pos.pow d e)]
  refine BPair.oneValue_trans
    (BPair.scale_congr _ (BPair.ofPos_scale (Pos.pow d m) Z.1)) ?_
  rw [BPair.scale_scale]
  exact BPair.oneValue_refl _

/-- Two capped reads multiply at the caps' summed key. -/
private theorem capMul (d : Pos) {x X : BPair × Pos} (m1 m2 : Nat)
    (h1 : qle (magQ x) (BPair.ofPos (Pos.pow d m1), Pos.one))
    (h2 : qle (magQ X) (BPair.ofPos (Pos.pow d m2), Pos.one)) :
    qle (magQ (bpairQOps.mul x X)) (BPair.ofPos (Pos.pow d (m1 + m2)), Pos.one) := by
  refine qle_congr_left (qOneValue_symm (magQ_mul x X)) (qle_congr_right ?_
    (qle_mul_mono (unit_le_ofPos _) (magQ_nn X) h1 h2))
  show ((BPair.ofPos (Pos.pow d m1) * BPair.ofPos (Pos.pow d m2)).scale Pos.one).oneValue
    ((BPair.ofPos (Pos.pow d (m1 + m2))).scale (Pos.one * Pos.one))
  rw [BPair.scale_one, Pos.pow_add, ground.one_mul, BPair.scale_one]
  exact BPair.ofPos_mul _ _

/-- One move of the fold: at a factor's gap over the other factors'
key, the remaining product's gap over the factor's key, and the caps
of the second family's factor and the first's remaining product, the
product's gap is the counts' sum over the joined key. -/
private theorem prodStep (d : Pos) {D x y X Y : BPair × Pos} (m1 m2 e : Nat)
    {j k : Nat}
    (hgx : qle (magQ (BPair.addQ x (bpairQOps.swap y)))
      (qdiv (poly.nsmulO bpairQOps D j) (Pos.pow d (m2 + e))))
    (hcX : qle (magQ X) (BPair.ofPos (Pos.pow d m2), Pos.one))
    (hcy : qle (magQ y) (BPair.ofPos (Pos.pow d m1), Pos.one))
    (hgr : qle (magQ (BPair.addQ X (bpairQOps.swap Y)))
      (qdiv (poly.nsmulO bpairQOps D k) (Pos.pow d (m1 + e)))) :
    qle (magQ (BPair.addQ (bpairQOps.mul x X)
        (bpairQOps.swap (bpairQOps.mul y Y))))
      (qdiv (poly.nsmulO bpairQOps D (j + k)) (Pos.pow d e)) := by
  have h1 : qle (magQ (bpairQOps.mul X (BPair.addQ x (bpairQOps.swap y))))
      (qdiv (poly.nsmulO bpairQOps D j) (Pos.pow d e)) :=
    qle_congr_left (qOneValue_symm (magQ_mul X (BPair.addQ x (bpairQOps.swap y))))
      (qle_congr_right (capDiv d _ m2 e)
        (qle_mul_mono (unit_le_ofPos _) (magQ_nn _) hcX hgx))
  have h2 : qle (magQ (bpairQOps.mul y (BPair.addQ X (bpairQOps.swap Y))))
      (qdiv (poly.nsmulO bpairQOps D k) (Pos.pow d e)) :=
    qle_congr_left (qOneValue_symm (magQ_mul y (BPair.addQ X (bpairQOps.swap Y))))
      (qle_congr_right (capDiv d _ m1 e)
        (qle_mul_mono (unit_le_ofPos _) (magQ_nn _) hcy hgr))
  refine qle_congr_left (magQ_congr (teleQ x y X Y)) ?_
  refine qle_trans (magQ_add _ _) ?_
  exact qle_congr_right
    (qOneValue_trans (qOneValue_symm (qdiv_add _ _ (Pos.pow d e)))
      (qdiv_congr (Pos.pow d e) (nsmul_add D j k)))
    (qle_add_mono2 h1 h2)

/-- Two joined reads' gap is the gaps' join. -/
private theorem addGap {x1 x2 y1 y2 b1 b2 : BPair × Pos}
    (h1 : qle (magQ (BPair.addQ x1 (bpairQOps.swap y1))) b1)
    (h2 : qle (magQ (BPair.addQ x2 (bpairQOps.swap y2))) b2) :
    qle (magQ (BPair.addQ (BPair.addQ x1 x2)
        (bpairQOps.swap (BPair.addQ y1 y2))))
      (BPair.addQ b1 b2) := by
  have htel : bpairQRead.rel
      (BPair.addQ (BPair.addQ x1 x2) (bpairQOps.swap (BPair.addQ y1 y2)))
      (BPair.addQ (BPair.addQ x1 (bpairQOps.swap y1))
        (BPair.addQ x2 (bpairQOps.swap y2))) := by
    rw [qswap_add y1 y2]
    exact BPair.addQ_add_comm x1 x2 (bpairQOps.swap y1) (bpairQOps.swap y2)
  exact qle_congr_left (qOneValue_symm (magQ_congr htel))
    (qle_trans (magQ_add _ _) (qle_add_mono2 h1 h2))

/-- A weighted read's gap is the gap at the same weight. -/
private theorem weightGap {x y b : BPair × Pos}
    (h : qle (magQ (BPair.addQ x (bpairQOps.swap y))) b) : ∀ w : Nat,
    qle (magQ (BPair.addQ (poly.nsmulO bpairQOps x w)
        (bpairQOps.swap (poly.nsmulO bpairQOps y w))))
      (poly.nsmulO bpairQOps b w)
  | 0 =>
    qle_congr_left
      (qOneValue_symm (qOneValue_trans (magQ_congr (qadd_neg bpairQOps.unit))
        (qOneValue_of_eq magQ_unit)))
      (qle_refl bpairQOps.unit)
  | w + 1 => addGap h (weightGap h w)

/-- A gap read against the datum alone reads it at the count one. -/
private theorem baseGap {D g : BPair × Pos} (w : Pos)
    (h : qle (magQ g) (qdiv D w)) :
    qle (magQ g) (qdiv (poly.nsmulO bpairQOps D 1) w) :=
  qle_congr_right (qdiv_congr w (qOneValue_symm (BPair.addQ_unitR D))) h

/-- A gap read at the vacant key is the read at the weighted datum. -/
private theorem gapDone {D g : BPair × Pos} {k : Nat} {d : Pos}
    (h : qle (magQ g) (qdiv (poly.nsmulO bpairQOps D k) (Pos.pow d 0))) :
    qle (magQ g) (poly.nsmulO bpairQOps D k) := by
  refine qle_congr_right (qOneValue_of_eq ?_) h
  show ((poly.nsmulO bpairQOps D k).1, (poly.nsmulO bpairQOps D k).2 * Pos.one)
    = poly.nsmulO bpairQOps D k
  rw [ground.mul_one]

private theorem addGapN {D x1 x2 y1 y2 : BPair × Pos} {j k : Nat}
    (h1 : qle (magQ (BPair.addQ x1 (bpairQOps.swap y1)))
      (poly.nsmulO bpairQOps D j))
    (h2 : qle (magQ (BPair.addQ x2 (bpairQOps.swap y2)))
      (poly.nsmulO bpairQOps D k)) :
    qle (magQ (BPair.addQ (BPair.addQ x1 x2)
        (bpairQOps.swap (BPair.addQ y1 y2))))
      (poly.nsmulO bpairQOps D (j + k)) :=
  qle_congr_right (nsmul_add D j k) (addGap h1 h2)

private theorem wGapN {D x y : BPair × Pos} {k : Nat}
    (h : qle (magQ (BPair.addQ x (bpairQOps.swap y))) (poly.nsmulO bpairQOps D k))
    (w : Nat) :
    qle (magQ (BPair.addQ (poly.nsmulO bpairQOps x w)
        (bpairQOps.swap (poly.nsmulO bpairQOps y w))))
      (poly.nsmulO bpairQOps D (k * w)) :=
  qle_congr_right (nsmul_flat D k w) (weightGap h w)

/-- Both members' partners read the same gap. -/
private theorem swapGap {x y b : BPair × Pos}
    (h : qle (magQ (BPair.addQ x (bpairQOps.swap y))) b) :
    qle (magQ (BPair.addQ (bpairQOps.swap x)
      (bpairQOps.swap (bpairQOps.swap y)))) b := by
  rw [← qswap_add x (bpairQOps.swap y), magQ_swap]
  exact h

/-- A capped read at the clearing one. -/
private theorem capOf {p : BPair × Pos} {c : BPair}
    (h : windowsep.mag p.1 ≤ c.scale p.2) : qle (magQ p) (c, Pos.one) := by
  show (windowsep.mag p.1).scale Pos.one ≤ c.scale p.2
  rw [BPair.scale_one]
  exact h

/-- The order at a magnitude, the composite pair's displayed
cross-multiplied read. -/
private theorem qleOut {X Y : BPair × Pos} (h : qle (magQ X) Y) :
    (windowsep.mag X.1).scale Y.2 ≤ Y.1.scale X.2 := h

/-- The partition fold's bracket (`lem:fourpoint`'s tail): at two moment
families whose reads' magnitudes sit under the caps `d^{a+b}` at every index
pair and whose gaps at `(a, b)`, scaled at `d^{4−a−b}`, sit under one datum,
the fold's gap telescopes factor by factor — every term at field count four,
one move per moment factor at the block-count weights, `75` in all — to
`75` times the datum, every order the composite pair's cross-multiplied
read. -/
theorem foldBracket (mu nu : Nat → Nat → BPair × Pos) (d : Pos) (D : BPair × Pos)
    (hcap : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      windowsep.mag (mu a b).1 ≤ (BPair.ofPos (Pos.pow d (a + b))).scale (mu a b).2
      ∧ windowsep.mag (nu a b).1 ≤ (BPair.ofPos (Pos.pow d (a + b))).scale (nu a b).2)
    (hgap : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      ∀ e : Nat, e ≤ 4 → a + b + e = 4 →
      (windowsep.mag (BPair.addQ (mu a b) (bpairQOps.swap (nu a b))).1).scale
          (D.2 * Pos.pow d e)
        ≤ D.1.scale (BPair.addQ (mu a b) (bpairQOps.swap (nu a b))).2) :
    (windowsep.mag (BPair.addQ (kappa4 bpairQOps mu)
        (bpairQOps.swap (kappa4 bpairQOps nu))).1).scale (poly.nsmulO bpairQOps D 75).2
      ≤ (poly.nsmulO bpairQOps D 75).1.scale
          (BPair.addQ (kappa4 bpairQOps mu) (bpairQOps.swap (kappa4 bpairQOps nu))).2
    := by
  have c10 : qle (magQ (mu 1 0)) (BPair.ofPos (Pos.pow d 1), Pos.one) :=
    capOf (hcap 1 (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)).1
  have c01 : qle (magQ (mu 0 1)) (BPair.ofPos (Pos.pow d 1), Pos.one) :=
    capOf (hcap 0 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)).1
  have c11 : qle (magQ (mu 1 1)) (BPair.ofPos (Pos.pow d 2), Pos.one) :=
    capOf (hcap 1 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)).1
  have c20 : qle (magQ (mu 2 0)) (BPair.ofPos (Pos.pow d 2), Pos.one) :=
    capOf (hcap 2 (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)).1
  have c02 : qle (magQ (mu 0 2)) (BPair.ofPos (Pos.pow d 2), Pos.one) :=
    capOf (hcap 0 (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)).1
  have c12 : qle (magQ (mu 1 2)) (BPair.ofPos (Pos.pow d 3), Pos.one) :=
    capOf (hcap 1 (by decide +kernel) 2 (by decide +kernel) (by decide +kernel)).1
  have c21 : qle (magQ (mu 2 1)) (BPair.ofPos (Pos.pow d 3), Pos.one) :=
    capOf (hcap 2 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)).1
  have k10 : qle (magQ (nu 1 0)) (BPair.ofPos (Pos.pow d 1), Pos.one) :=
    capOf (hcap 1 (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)).2
  have k01 : qle (magQ (nu 0 1)) (BPair.ofPos (Pos.pow d 1), Pos.one) :=
    capOf (hcap 0 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)).2
  have k11 : qle (magQ (nu 1 1)) (BPair.ofPos (Pos.pow d 2), Pos.one) :=
    capOf (hcap 1 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel)).2
  have k20 : qle (magQ (nu 2 0)) (BPair.ofPos (Pos.pow d 2), Pos.one) :=
    capOf (hcap 2 (by decide +kernel) 0 (by decide +kernel) (by decide +kernel)).2
  have b10 : qle (magQ (BPair.addQ (mu 1 0) (bpairQOps.swap (nu 1 0))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 3)) :=
    baseGap _ (hgap 1 (by decide +kernel) 0 (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) rfl)
  have b01 : qle (magQ (BPair.addQ (mu 0 1) (bpairQOps.swap (nu 0 1))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 3)) :=
    baseGap _ (hgap 0 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel) 3 (by decide +kernel) rfl)
  have b11 : qle (magQ (BPair.addQ (mu 1 1) (bpairQOps.swap (nu 1 1))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 2)) :=
    baseGap _ (hgap 1 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) rfl)
  have b20 : qle (magQ (BPair.addQ (mu 2 0) (bpairQOps.swap (nu 2 0))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 2)) :=
    baseGap _ (hgap 2 (by decide +kernel) 0 (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) rfl)
  have b02 : qle (magQ (BPair.addQ (mu 0 2) (bpairQOps.swap (nu 0 2))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 2)) :=
    baseGap _ (hgap 0 (by decide +kernel) 2 (by decide +kernel) (by decide +kernel) 2 (by decide +kernel) rfl)
  have b12 : qle (magQ (BPair.addQ (mu 1 2) (bpairQOps.swap (nu 1 2))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 1)) :=
    baseGap _ (hgap 1 (by decide +kernel) 2 (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) rfl)
  have b21 : qle (magQ (BPair.addQ (mu 2 1) (bpairQOps.swap (nu 2 1))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 1)) :=
    baseGap _ (hgap 2 (by decide +kernel) 1 (by decide +kernel) (by decide +kernel) 1 (by decide +kernel) rfl)
  have b22 : qle (magQ (BPair.addQ (mu 2 2) (bpairQOps.swap (nu 2 2))))
      (qdiv (poly.nsmulO bpairQOps D 1) (Pos.pow d 0)) :=
    baseGap _ (hgap 2 (by decide +kernel) 2 (by decide +kernel) (by decide +kernel) 0 (by decide +kernel) rfl)
  have p1010 := prodStep d 1 1 2 b10 c10 k10 b10
  have p0101 := prodStep d 1 1 2 b01 c01 k01 b01
  have p1001 := prodStep d 1 1 2 b10 c01 k10 b01
  have t22 := gapDone b22
  have wA := wGapN (gapDone (prodStep d 2 2 0 p1010 c02 (capMul d 1 1 k10 k10) b02)) 2
  have wB := wGapN (gapDone (prodStep d 2 2 0 p0101 c20 (capMul d 1 1 k01 k01) b20)) 2
  have wC := wGapN (gapDone (prodStep d 2 2 0 p1001 c11 (capMul d 1 1 k10 k01) b11)) 8
  have wP := wGapN (gapDone (prodStep d 1 3 0 b10 c12 k10 b12)) 2
  have wQ := wGapN (gapDone (prodStep d 1 3 0 b01 c21 k01 b21)) 2
  have tR := gapDone (prodStep d 2 2 0 b20 c02 k20 b02)
  have wS := wGapN (gapDone (prodStep d 2 2 0 b11 c11 k11 b11)) 2
  have wT := wGapN (gapDone (prodStep d 2 2 0 p1010
    (capMul d 1 1 c01 c01) (capMul d 1 1 k10 k10) p0101)) 6
  have hOdd := addGapN (addGapN (addGapN t22 wA) wB) wC
  have hEven := addGapN (addGapN (addGapN (addGapN wP wQ) tR) wS) wT
  have hsum := addGapN hOdd (swapGap hEven)
  have hfold : qle (magQ (BPair.addQ (kappa4 bpairQOps mu)
      (bpairQOps.swap (kappa4 bpairQOps nu)))) (poly.nsmulO bpairQOps D 75) := hsum
  exact qleOut hfold

/-- Two reads' gap against a third chains at the middle read's
clearing: the outer gap scaled by the middle second datum is the two
inner gaps at the outer second data, the middle read's own terms
withdrawing at the exchange. -/
private theorem readGap_chain (r r' r'' : BPair × BPair) :
    (groundreads.readGap r r' * r''.2
        + groundreads.readGap r' r'' * r.2).oneValue
      (groundreads.readGap r r'' * r'.2) := by
  show ((r'.1 * r.2 + (r.1 * r'.2).swap) * r''.2
      + (r''.1 * r'.2 + (r'.1 * r''.2).swap) * r.2).oneValue
    ((r''.1 * r.2 + (r.1 * r''.2).swap) * r'.2)
  rw [BPair.right_distrib, BPair.right_distrib, BPair.right_distrib,
    BPair.swap_mul, BPair.swap_mul, BPair.swap_mul]
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.add_add_comm (r'.1 * r.2 * r''.2)
        ((r.1 * r'.2 * r''.2).swap) (r''.1 * r'.2 * r.2)
        ((r'.1 * r''.2 * r.2).swap))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.add_comm (r'.1 * r.2 * r''.2) (r''.1 * r'.2 * r.2)))
        (BPair.oneValue_refl _))
      (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.add_add_comm (r''.1 * r'.2 * r.2) (r'.1 * r.2 * r''.2)
        ((r.1 * r'.2 * r''.2).swap) ((r'.1 * r''.2 * r.2).swap))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr
        (BPair.oneValue_of_eq (BPair.mul_right_comm r''.1 r'.2 r.2))
        (ground.swap_congr
          (BPair.oneValue_of_eq (BPair.mul_right_comm r.1 r'.2 r''.2))))
      (BPair.oneValue_trans
        (BPair.add_congr
          (BPair.oneValue_of_eq (BPair.mul_right_comm r'.1 r.2 r''.2))
          (BPair.oneValue_refl _))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.add_comm (r'.1 * r''.2 * r.2)
              ((r'.1 * r''.2 * r.2).swap)))
          (BPair.swap_add_null
            (BPair.oneValue_refl (r'.1 * r''.2 * r.2)))))) ?_
  exact BPair.add_unit _

/-- The factor's move cost (`lem:fourpoint`'s tail): the moments'
bracket at the jet chained to the truncation's through the reads' gap,
the jet state's clearing stripped at the gram's floor `q⁸` — the
displayed `δ ≤ [4c w : γ'] + τ⁶T` at the two brackets' own clearings,
`|ω̂(A) − μ̂(τ)| ≤ |N_A(τ)|` at `G ≥ 1` the middle step. -/
theorem gapBracket {n : Nat} (E M Et : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (T Tw : SqMat n) (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0 = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : groundreads.clearRead l j0 gn gd)
    (p q c : Pos) (e0 : BPair)
    (htie : matOneValue Et
      (siteDatum (matScale c (rayH p q E M)) (matScaleB e0 (idMat n))))
    (spE : Split n) (hEs : splitRead E spE) (hEp : psdAt spE)
    (W : Pos) (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL)
    (one psi1 psi2 : List BPair) (h1 : one.length = n) (h2 : psi1.length = n)
    (h3 : psi2.length = n) (np : Nat)
    (hE0 : poly.unitTail (matVec E one))
    (hE1 : poly.oneValue (matVec E psi1) (matVec M one))
    (hE2 : poly.oneValue
      (vecAdd (vecScale (BPair.ofNat 4) (matVec E psi2)) (vecScale (BPair.ofNat np) one))
      (vecScale (BPair.ofNat 4) (matVec M psi1)))
    (hperp1 : (dotN psi1 one).oneValue BPair.unit)
    (hperp2 : (dotN psi2 one).oneValue BPair.unit)
    (h11 : (dotN one one).oneValue (BPair.ofNat 1))
    (dp : Pos)
    (hdp : (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap).oneValue (BPair.ofPos dp))
    (K0 K1 : Pos)
    (hK0 : BPair.ofNat (4 * (np * np)) * dotN psi1 psi1
        + BPair.ofPos (64 * (W * W)) * dotN psi2 psi2 ≤ BPair.ofPos (16 * (K0 * K0)))
    (hK1 : BPair.ofNat (2 * (np * np)) * dotN psi2 psi2 ≤ BPair.ofPos (16 * (K1 * K1)))
    (A : Mat) (cn cd : Pos) (spA spA' : Split n)
    (hA : capAt (matScale cd A) (matScale cn (idMat n)) spA spA')
    (zn : BPair) (zd : Pos) (hZ : (dotN psi2 psi2).scale zd ≤ zn) :
    (windowsep.mag (groundreads.readGap
        (groundreads.read A (matVec T.val (elim.idRow n j0)))
        (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))).scale
        (gn * (dp * Pos.pow q 6) * cd * (cd * zd * Pos.pow q 8))
      ≤ (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
            * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)).scale
          (4 * (cn * (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p))) * gd)
            * (Pos.pow q 4 * (cd * zd)))
        + (truncCap cn cd zd (dotN one (matVec A one))
              (BPair.ofNat 2 * dotN one (matVec A psi1))
              (BPair.ofNat 2 * dotN one (matVec A psi2) + dotN psi1 (matVec A psi1)
                + (dotN one (matVec A one) * dotN psi1 psi1).swap)
              (dotN psi1 psi1) zn p q
            * dotN (matVec T.val (elim.idRow n j0))
                (matVec T.val (elim.idRow n j0))).scale
          (gn * (dp * Pos.pow q 6) * cd) := by
  have hS0nn : BPair.unit
      ≤ dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0)) :=
    ground.leB_of_not_lt (dotN_self_side _)
  have hS1nn : BPair.unit
      ≤ dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2) :=
    ground.leB_of_not_lt (dotN_self_side _)
  have hmb := momentBracket E M Et hE hM T Tw l hd j0 hj0 d0 g0 hroot0 gn gd
    hcl p q c e0 htie spE hEs hEp W spU spL hcapM one psi1 psi2 h1 h2 h3 np
    hE0 hE1 hE2 hperp1 hperp2 h11 dp hdp K0 K1 hK0 hK1 A cn cd spA spA' hA
  have htb := truncBracket A cn cd spA spA' hA one psi1 psi2 h1 h2 h3 h11
    (BPair.oneValue_trans (dotN_comm one psi1) hperp1)
    (BPair.oneValue_trans (dotN_comm one psi2) hperp2) zn zd hZ p q
  -- the truncation bracket's argument is the middle gap, memberwise swapped
  have hswap : (((dotN (jetVec p q one psi1 psi2)
          (matVec A (jetVec p q one psi1 psi2))).scale (Pos.pow q 4 * (cd * zd))
        + ((jetDisplay A one psi1 psi2 p q
            * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)).scale
            (cd * zd)).swap).swap).oneValue
      ((groundreads.readGap (groundreads.read A (jetVec p q one psi1 psi2))
        (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4))).scale (cd * zd)) := by
    show (((dotN (jetVec p q one psi1 psi2)
          (matVec A (jetVec p q one psi1 psi2))).scale (Pos.pow q 4 * (cd * zd))
        + ((jetDisplay A one psi1 psi2 p q
            * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)).scale
            (cd * zd)).swap).swap).oneValue
      ((jetDisplay A one psi1 psi2 p q
          * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)
        + (dotN (jetVec p q one psi1 psi2) (matVec A (jetVec p q one psi1 psi2))
            * BPair.ofPos (Pos.pow q 4)).swap).scale (cd * zd))
    rw [← BPair.swap_add, BPair.swap_swap, BPair.scale_add, BPair.scale_swap,
      BPair.add_comm ((jetDisplay A one psi1 psi2 p q
          * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)).scale (cd * zd))
        (((dotN (jetVec p q one psi1 psi2) (matVec A (jetVec p q one psi1 psi2))
          * BPair.ofPos (Pos.pow q 4)).scale (cd * zd)).swap)]
    refine BPair.add_congr (ground.swap_congr ?_) (BPair.oneValue_refl _)
    refine BPair.oneValue_symm ?_
    rw [BPair.mul_comm (dotN (jetVec p q one psi1 psi2)
        (matVec A (jetVec p q one psi1 psi2))) (BPair.ofPos (Pos.pow q 4)),
      ← BPair.scale_scale (dotN (jetVec p q one psi1 psi2)
        (matVec A (jetVec p q one psi1 psi2))) (Pos.pow q 4) (cd * zd)]
    exact BPair.scale_congr (cd * zd) (BPair.ofPos_scale (Pos.pow q 4) _)
  have hg12 : (windowsep.mag (groundreads.readGap
        (groundreads.read A (jetVec p q one psi1 psi2))
        (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))).scale (cd * zd)
      ≤ truncCap cn cd zd (dotN one (matVec A one))
          (BPair.ofNat 2 * dotN one (matVec A psi1))
          (BPair.ofNat 2 * dotN one (matVec A psi2) + dotN psi1 (matVec A psi1)
            + (dotN one (matVec A one) * dotN psi1 psi1).swap)
          (dotN psi1 psi1) zn p q := by
    refine ground.leB_congr_left ?_ htb
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (windowsep.mag_swap _).symm) ?_
    rw [← windowsep.mag_scale]
    exact windowsep.mag_congr hswap
  -- the reads' gap chain at the three reads
  have hch : (groundreads.readGap
        (groundreads.read A (matVec T.val (elim.idRow n j0)))
        (groundreads.read A (jetVec p q one psi1 psi2))
          * BPair.ofPos (Pos.pow q 4)
      + groundreads.readGap (groundreads.read A (jetVec p q one psi1 psi2))
          (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4))
          * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))).oneValue
      (groundreads.readGap (groundreads.read A (matVec T.val (elim.idRow n j0)))
          (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4))
        * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)) :=
    readGap_chain (groundreads.read A (matVec T.val (elim.idRow n j0)))
      (groundreads.read A (jetVec p q one psi1 psi2))
      (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4))
  have hkey : windowsep.mag (groundreads.readGap
        (groundreads.read A (matVec T.val (elim.idRow n j0)))
        (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))
        * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)
      ≤ windowsep.mag (groundreads.readGap
          (groundreads.read A (matVec T.val (elim.idRow n j0)))
          (groundreads.read A (jetVec p q one psi1 psi2)))
          * BPair.ofPos (Pos.pow q 4)
        + windowsep.mag (groundreads.readGap
            (groundreads.read A (jetVec p q one psi1 psi2))
            (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))
          * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0)) := by
    refine ground.leB_congr ?_ ?_
      (windowsep.mag_add_le
        (groundreads.readGap
            (groundreads.read A (matVec T.val (elim.idRow n j0)))
            (groundreads.read A (jetVec p q one psi1 psi2))
          * BPair.ofPos (Pos.pow q 4))
        (groundreads.readGap (groundreads.read A (jetVec p q one psi1 psi2))
            (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4))
          * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))))
    · refine BPair.oneValue_trans (windowsep.mag_congr hch) ?_
      refine BPair.oneValue_trans (windowsep.mag_mul _ _) ?_
      exact BPair.oneValue_of_eq (by rw [windowsep.mag_unitLe hS1nn])
    · refine BPair.add_congr ?_ ?_
      · refine BPair.oneValue_trans (windowsep.mag_mul _ _) ?_
        exact BPair.oneValue_of_eq (by rw [windowsep.mag_unitLe
          (ground.leB_of_lt (ground.unitLtOfPos (Pos.pow q 4)))])
      · refine BPair.oneValue_trans (windowsep.mag_mul _ _) ?_
        exact BPair.oneValue_of_eq (by rw [windowsep.mag_unitLe hS0nn])
  -- the gram's floor strips the jet's clearing
  have hfloor : BPair.ofPos (Pos.pow q 8)
      ≤ dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2) :=
    jetFloor one psi1 psi2 h1 h2 h3 hperp1 hperp2 h11 p q
  have hq8 : (windowsep.mag (groundreads.readGap
        (groundreads.read A (matVec T.val (elim.idRow n j0)))
        (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))).scale
        (Pos.pow q 8)
      ≤ windowsep.mag (groundreads.readGap
          (groundreads.read A (matVec T.val (elim.idRow n j0)))
          (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))
        * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2) := by
    refine ground.leB_congr_left ?_
      (ground.leB_mulR (windowsep.unitLe_mag _) hfloor)
    rw [BPair.mul_comm (windowsep.mag (groundreads.readGap
        (groundreads.read A (matVec T.val (elim.idRow n j0)))
        (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4))))
      (BPair.ofPos (Pos.pow q 8))]
    exact BPair.ofPos_scale (Pos.pow q 8) _
  have hsc := ground.leB_scale (ground.leB_trans hq8 hkey)
    (gn * (dp * Pos.pow q 6) * cd * (cd * zd))
  rw [BPair.scale_add] at hsc
  -- the moments' bracket at the further clearing
  have t1 : (windowsep.mag (groundreads.readGap
          (groundreads.read A (matVec T.val (elim.idRow n j0)))
          (groundreads.read A (jetVec p q one psi1 psi2)))
        * BPair.ofPos (Pos.pow q 4)).scale
        (gn * (dp * Pos.pow q 6) * cd * (cd * zd))
      ≤ (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
            * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)).scale
          (4 * (cn * (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p))) * gd)
            * (Pos.pow q 4 * (cd * zd))) := by
    refine ground.leB_congr ?_ ?_
      (ground.leB_scale hmb (Pos.pow q 4 * (cd * zd)))
    · refine BPair.oneValue_symm ?_
      rw [BPair.mul_comm (windowsep.mag (groundreads.readGap
            (groundreads.read A (matVec T.val (elim.idRow n j0)))
            (groundreads.read A (jetVec p q one psi1 psi2))))
          (BPair.ofPos (Pos.pow q 4)),
        BPair.scale_scale (windowsep.mag (groundreads.readGap
            (groundreads.read A (matVec T.val (elim.idRow n j0)))
            (groundreads.read A (jetVec p q one psi1 psi2))))
          (gn * (dp * Pos.pow q 6) * cd) (Pos.pow q 4 * (cd * zd)),
        ← ground.mul_assoc (gn * (dp * Pos.pow q 6) * cd) (Pos.pow q 4) (cd * zd),
        ground.mul_comm (gn * (dp * Pos.pow q 6) * cd) (Pos.pow q 4),
        ground.mul_assoc (Pos.pow q 4) (gn * (dp * Pos.pow q 6) * cd) (cd * zd),
        ← BPair.scale_scale (windowsep.mag (groundreads.readGap
            (groundreads.read A (matVec T.val (elim.idRow n j0)))
            (groundreads.read A (jetVec p q one psi1 psi2))))
          (Pos.pow q 4) (gn * (dp * Pos.pow q 6) * cd * (cd * zd))]
      exact BPair.scale_congr (gn * (dp * Pos.pow q 6) * cd * (cd * zd))
        (BPair.ofPos_scale (Pos.pow q 4) _)
    · exact BPair.oneValue_of_eq (BPair.scale_scale
        (dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
          * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2))
        (4 * (cn * (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p))) * gd))
        (Pos.pow q 4 * (cd * zd)))
  -- the truncation's bracket at the ground state's clearing
  have t2 : (windowsep.mag (groundreads.readGap
          (groundreads.read A (jetVec p q one psi1 psi2))
          (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))
        * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))).scale
        (gn * (dp * Pos.pow q 6) * cd * (cd * zd))
      ≤ (truncCap cn cd zd (dotN one (matVec A one))
            (BPair.ofNat 2 * dotN one (matVec A psi1))
            (BPair.ofNat 2 * dotN one (matVec A psi2) + dotN psi1 (matVec A psi1)
              + (dotN one (matVec A one) * dotN psi1 psi1).swap)
            (dotN psi1 psi1) zn p q
          * dotN (matVec T.val (elim.idRow n j0))
              (matVec T.val (elim.idRow n j0))).scale
        (gn * (dp * Pos.pow q 6) * cd) := by
    refine ground.leB_congr ?_ ?_
      (ground.leB_scale (ground.leB_mulR hS0nn hg12) (gn * (dp * Pos.pow q 6) * cd))
    · refine BPair.oneValue_of_eq ?_
      rw [BPair.mul_scale (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)))
          (windowsep.mag (groundreads.readGap
            (groundreads.read A (jetVec p q one psi1 psi2))
            (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))) (cd * zd),
        BPair.scale_scale, BPair.mul_comm (dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0)))
          (windowsep.mag (groundreads.readGap
            (groundreads.read A (jetVec p q one psi1 psi2))
            (jetDisplay A one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))),
        ground.mul_comm (cd * zd) (gn * (dp * Pos.pow q 6) * cd)]
    · exact BPair.oneValue_of_eq (by
        rw [BPair.mul_comm (dotN (matVec T.val (elim.idRow n j0))
          (matVec T.val (elim.idRow n j0)))])
  refine ground.leB_congr_left (BPair.oneValue_of_eq ?_)
    (ground.leB_trans hsc (ground.leB_add t1 t2))
  rw [BPair.scale_scale,
    ground.mul_comm (Pos.pow q 8) (gn * (dp * Pos.pow q 6) * cd * (cd * zd)),
    ground.mul_assoc (gn * (dp * Pos.pow q 6) * cd) (cd * zd) (Pos.pow q 8)]

/-- The four-point fold's bracket at the window carrier
(`lem:fourpoint`'s tail): the moment families the ground state's reads
and the jet's displays, each factor's move priced by the gap bracket
at its clearing and folded under the one datum at the block-count
weights, `|κ₄(ω) − κ₄(μ̂(τ))| ≤ 75·D` at the composite pairs'
cross-multiplied read. -/
theorem kappaBracket {n : Nat} (E M Et : Mat) (hE : sqAt E n) (hM : sqAt M n)
    (T Tw : SqMat n) (l : List (BPair × Pos × BPair))
    (hd : split.diagRead Et (idMat n) T Tw l)
    (j0 : Nat) (hj0 : j0 < n) (d0 : Pos) (g0 : BPair)
    (hroot0 : ground.getAt (BPair.unit, Pos.one, BPair.unit) l j0 = (BPair.unit, d0, g0))
    (gn gd : Pos) (hcl : groundreads.clearRead l j0 gn gd)
    (p q c : Pos) (e0 : BPair)
    (htie : matOneValue Et
      (siteDatum (matScale c (rayH p q E M)) (matScaleB e0 (idMat n))))
    (spE : Split n) (hEs : splitRead E spE) (hEp : psdAt spE)
    (W : Pos) (spU spL : Split n)
    (hcapM : capAt (matScale Pos.one (matMul (transposeM M) M))
      (matScale (W * W) (idMat n)) spU spL)
    (one psi1 psi2 : List BPair) (h1 : one.length = n) (h2 : psi1.length = n)
    (h3 : psi2.length = n) (np : Nat)
    (hE0 : poly.unitTail (matVec E one))
    (hE1 : poly.oneValue (matVec E psi1) (matVec M one))
    (hE2 : poly.oneValue
      (vecAdd (vecScale (BPair.ofNat 4) (matVec E psi2)) (vecScale (BPair.ofNat np) one))
      (vecScale (BPair.ofNat 4) (matVec M psi1)))
    (hperp1 : (dotN psi1 one).oneValue BPair.unit)
    (hperp2 : (dotN psi2 one).oneValue BPair.unit)
    (h11 : (dotN one one).oneValue (BPair.ofNat 1))
    (dp : Pos)
    (hdp : (BPair.ofPos gn + (BPair.ofPos (gd * c * (p * p) * W)).swap).oneValue (BPair.ofPos dp))
    (K0 K1 : Pos)
    (hK0 : BPair.ofNat (4 * (np * np)) * dotN psi1 psi1
        + BPair.ofPos (64 * (W * W)) * dotN psi2 psi2 ≤ BPair.ofPos (16 * (K0 * K0)))
    (hK1 : BPair.ofNat (2 * (np * np)) * dotN psi2 psi2 ≤ BPair.ofPos (16 * (K1 * K1)))
    (s0 : Pos)
    (hs0 : (dotN (matVec T.val (elim.idRow n j0))
      (matVec T.val (elim.idRow n j0))).oneValue (BPair.ofPos s0))
    (dth : Pos)
    (A : Nat → Nat → Mat) (cn cd : Nat → Nat → Pos)
    (spA spA' : Nat → Nat → Split n)
    (hA : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      capAt (matScale (cd a b) (A a b)) (matScale (cn a b) (idMat n))
        (spA a b) (spA' a b))
    (zn : Nat → Nat → BPair) (zd : Nat → Nat → Pos)
    (hZ : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      (dotN psi2 psi2).scale (zd a b) ≤ zn a b)
    (D : BPair × Pos)
    (hcap : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      windowsep.mag (quadForm (A a b) (matVec T.val (elim.idRow n j0)))
          ≤ (BPair.ofPos (Pos.pow dth (a + b))).scale s0
        ∧ windowsep.mag (jetDisplay (A a b) one psi1 psi2 p q)
          ≤ (BPair.ofPos (Pos.pow dth (a + b))).scale (Pos.pow q 4))
    (hD : ∀ a : Nat, a ≤ 2 → ∀ b : Nat, b ≤ 2 → 0 < a + b →
      ∀ e : Nat, e ≤ 4 → a + b + e = 4 →
      ((dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
            * dotN (jetVec p q one psi1 psi2) (jetVec p q one psi1 psi2)).scale
            (4 * (cn a b * (gn * c * Pos.pow p 6 * (K0 * (q * q) + K1 * (p * p))) * gd)
              * (Pos.pow q 4 * (cd a b * zd a b)))
          + (truncCap (cn a b) (cd a b) (zd a b) (dotN one (matVec (A a b) one))
                (BPair.ofNat 2 * dotN one (matVec (A a b) psi1))
                (BPair.ofNat 2 * dotN one (matVec (A a b) psi2)
                  + dotN psi1 (matVec (A a b) psi1)
                  + (dotN one (matVec (A a b) one) * dotN psi1 psi1).swap)
                (dotN psi1 psi1) (zn a b) p q
              * dotN (matVec T.val (elim.idRow n j0))
                  (matVec T.val (elim.idRow n j0))).scale
            (gn * (dp * Pos.pow q 6) * cd a b)).scale (D.2 * Pos.pow dth e)
        ≤ (D.1.scale (s0 * Pos.pow q 4)).scale
            (gn * (dp * Pos.pow q 6) * cd a b
              * (cd a b * zd a b * Pos.pow q 8))) :
    (windowsep.mag (BPair.addQ
        (kappa4 bpairQOps (fun a b =>
          (quadForm (A a b) (matVec T.val (elim.idRow n j0)), s0)))
        (bpairQOps.swap (kappa4 bpairQOps (fun a b =>
          (jetDisplay (A a b) one psi1 psi2 p q, Pos.pow q 4))))).1).scale
        (poly.nsmulO bpairQOps D 75).2
      ≤ (poly.nsmulO bpairQOps D 75).1.scale
          (BPair.addQ
            (kappa4 bpairQOps (fun a b =>
              (quadForm (A a b) (matVec T.val (elim.idRow n j0)), s0)))
            (bpairQOps.swap (kappa4 bpairQOps (fun a b =>
              (jetDisplay (A a b) one psi1 psi2 p q, Pos.pow q 4))))).2 := by
  refine foldBracket
    (fun a b => (quadForm (A a b) (matVec T.val (elim.idRow n j0)), s0))
    (fun a b => (jetDisplay (A a b) one psi1 psi2 p q, Pos.pow q 4))
    dth D hcap ?_
  intro a ha b hb hab e he hsum
  show (windowsep.mag ((quadForm (A a b) (matVec T.val (elim.idRow n j0))).scale
        (Pos.pow q 4)
      + ((jetDisplay (A a b) one psi1 psi2 p q).swap).scale s0)).scale
      (D.2 * Pos.pow dth e)
    ≤ D.1.scale (s0 * Pos.pow q 4)
  have hgb := gapBracket E M Et hE hM T Tw l hd j0 hj0 d0 g0 hroot0 gn gd
    hcl p q c e0 htie spE hEs hEp W spU spL hcapM one psi1 psi2 h1 h2 h3 np
    hE0 hE1 hE2 hperp1 hperp2 h11 dp hdp K0 K1 hK0 hK1 (A a b) (cn a b) (cd a b)
    (spA a b) (spA' a b) (hA a ha b hb hab) (zn a b) (zd a b) (hZ a ha b hb hab)
  have hDi := hD a ha b hb hab e he hsum
  -- the composite gap's magnitude is the reads' gap's, memberwise swapped
  have hor : (windowsep.mag ((quadForm (A a b) (matVec T.val (elim.idRow n j0))).scale
        (Pos.pow q 4)
      + ((jetDisplay (A a b) one psi1 psi2 p q).swap).scale s0)).oneValue
      (windowsep.mag (groundreads.readGap
        (groundreads.read (A a b) (matVec T.val (elim.idRow n j0)))
        (jetDisplay (A a b) one psi1 psi2 p q, BPair.ofPos (Pos.pow q 4)))) := by
    refine BPair.oneValue_trans (windowsep.mag_congr ?_)
      (BPair.oneValue_of_eq (windowsep.mag_swap _))
    show ((quadForm (A a b) (matVec T.val (elim.idRow n j0))).scale (Pos.pow q 4)
        + ((jetDisplay (A a b) one psi1 psi2 p q).swap).scale s0).oneValue
      ((jetDisplay (A a b) one psi1 psi2 p q
          * dotN (matVec T.val (elim.idRow n j0)) (matVec T.val (elim.idRow n j0))
        + (quadForm (A a b) (matVec T.val (elim.idRow n j0))
            * BPair.ofPos (Pos.pow q 4)).swap).swap)
    rw [← BPair.swap_add, BPair.swap_swap, BPair.add_comm
      ((jetDisplay (A a b) one psi1 psi2 p q
        * dotN (matVec T.val (elim.idRow n j0))
            (matVec T.val (elim.idRow n j0))).swap)
      (quadForm (A a b) (matVec T.val (elim.idRow n j0))
        * BPair.ofPos (Pos.pow q 4))]
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_symm ?_
      rw [BPair.mul_comm (quadForm (A a b) (matVec T.val (elim.idRow n j0)))
        (BPair.ofPos (Pos.pow q 4))]
      exact BPair.ofPos_scale (Pos.pow q 4) _
    · rw [BPair.scale_swap]
      refine ground.swap_congr ?_
      refine BPair.oneValue_symm ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) hs0) ?_
      rw [BPair.mul_comm (jetDisplay (A a b) one psi1 psi2 p q)
        (BPair.ofPos s0)]
      exact BPair.ofPos_scale s0 _
  refine ground.leB_of_scale
    (w := gn * (dp * Pos.pow q 6) * cd a b * (cd a b * zd a b * Pos.pow q 8)) ?_
  refine ground.leB_trans ?_ hDi
  refine ground.leB_congr_left ?_
    (ground.leB_scale hgb (D.2 * Pos.pow dth e))
  rw [BPair.scale_scale, BPair.scale_scale,
    ground.mul_comm (gn * (dp * Pos.pow q 6) * cd a b
      * (cd a b * zd a b * Pos.pow q 8)) (D.2 * Pos.pow dth e)]
  exact BPair.scale_congr _ (BPair.oneValue_symm hor)


/-! `lem:fourpoint`'s tail at the cell: the comparison polynomial and the
cell's floor.  The tail's fold at the drift's clearing (`tailPoly`) and the
leading read against twice that fold (`compPoly`) are polynomials in the
squared ray coordinate over the balance pairs, both cleared at the
clearance's second datum.  The comparison sits on its lower side at the
crossing `[gn : gd W]` (`compCross`), where the leading read's factor reads
equal members and only the root caps' line stands; so a priced side
certificate for the comparison (`stage.keepUpper`) cannot reach the
crossing, and every ray whose squared point sits inside the certificate's
segment carries the clearance's occupied gap.  At such a ray the
comparison's positive read is the cleared statement that twice the tail's
fold sits below the leading read (`clearGap`), and against the tail's own
bracket at the ray it collects to the four-point read's upper side at the
margin `[1 : 2] τ⁴ c` (`cellFloor`), the magnitude's two-sided read
withdrawing the half at the doubled spelling. -/

/-- The tail's fold at the drift's clearing (`lem:fourpoint`'s tail),
cleared at the clearance's second datum, in the squared ray coordinate
`u = τ²`: `75 d_θ⁴ (4 gd K(u) + (gn − gd W u) ΣT(u)) + (gn − gd W u) |R|(u)`,
`K` the root caps' line, `ΣT` the key caps' fold and `|R|` the remainder's
magnitude fold. -/
def tailPoly (gn gd W dth K0 K1 : Pos) (ST Rm : poly.Poly) : poly.Poly :=
  poly.add
    (poly.mul [BPair.ofPos (75 * Pos.pow dth 4)]
      (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
        (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST)))
    (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] Rm)

/-- The comparison polynomial (`lem:fourpoint`'s tail): the leading read
against twice the tail's fold at the drift's clearing, cleared at the
clearance's second datum in the squared ray coordinate,
`(gn − gd W u) c − 2u · tail(u)`. -/
def compPoly (gn gd W dth K0 K1 : Pos) (c : BPair) (ST Rm : poly.Poly) : poly.Poly :=
  poly.add (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] [c])
    (poly.neg (poly.mul [BPair.unit, BPair.ofNat 2]
      (tailPoly gn gd W dth K0 K1 ST Rm)))

/-- A two-key list's cleared read at the key one: the constant against the
clearing and the linear coefficient against the point. -/
private theorem ecPair (a0 a1 ln : BPair) (cc : Pos) :
    (poly.evalClear [a0, a1] ln cc 1).oneValue
      (a0 * BPair.ofPos cc + a1 * ln) := by
  refine BPair.oneValue_trans (poly.evalClear_read [a0, a1] ln cc 1) ?_
  show (a0 * ground.bpow ln 0 * ground.bpow (BPair.ofPos cc) 1
      + (a1 * ground.bpow ln 1 * ground.bpow (BPair.ofPos cc) 0
        + BPair.unit)).oneValue (a0 * BPair.ofPos cc + a1 * ln)
  refine BPair.add_congr ?_ (BPair.oneValue_trans (BPair.add_unit _) ?_)
  · exact BPair.mul_congr (BPair.mul_one_read a0) (ground.bpow_one_read _)
  · exact BPair.oneValue_trans (BPair.mul_one_read _)
      (BPair.mul_congr (BPair.oneValue_refl a1) (ground.bpow_one_read ln))

/-- The leading read's factor reads equal members at the crossing: at the
point `[gn : gd W]` the two members are `gn (gd W)` both ways. -/
private theorem crossFactor (gn gd W : Pos) :
    (poly.evalClear [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap]
        (BPair.ofPos gn) (gd * W) 1).oneValue BPair.unit := by
  refine BPair.oneValue_trans (ecPair _ _ _ _) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_of_eq (BPair.swap_mul _ _))
      (BPair.oneValue_refl _)) ?_
  exact BPair.swap_add_null (BPair.oneValue_of_eq (BPair.mul_comm _ _))

/-- Every multiple of the leading read's factor reads the sum's unit at the
crossing, the product's own read at the split powers. -/
private theorem crossMul (gn gd W : Pos) (X : poly.Poly) (J : Nat)
    (hX : X.length ≤ J + 1) :
    (poly.evalClear (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] X)
        (BPair.ofPos gn) (gd * W) (1 + J)).oneValue BPair.unit :=
  BPair.oneValue_trans
    (poly.evalClear_mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] X
      (BPair.ofPos gn) (gd * W) 1 J (Nat.le_refl 2) hX)
    (BPair.oneValue_trans
      (BPair.mul_congr (crossFactor gn gd W) (BPair.oneValue_refl _))
      (BPair.unit_mul _))

/-- The tail's cleared read at the crossing sits strictly above the sum's
unit: the key caps' and the remainder's folds enter through the leading
read's factor and read the sum's unit there, so what stands is the root
caps' line at the drift's clearing, occupied at every datum. -/
private theorem crossTail (gn gd W dth K0 K1 : Pos) (ST Rm : poly.Poly) (K3 : Nat)
    (hST : ST.length ≤ K3 + 1) (hRm : Rm.length ≤ K3 + 1)
    (hZ : (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
            (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST)).length
        ≤ 1 + K3 + 1) :
    BPair.unit < poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
        (BPair.ofPos gn) (gd * W) (1 + K3) := by
  have hA01 : BPair.unit
      < BPair.ofPos (4 * (gd * K0)) * BPair.ofPos (gd * W)
        + BPair.ofPos (4 * (gd * K1)) * BPair.ofPos gn :=
    unitLtAdd (unitLtMul (unitLtOfPos _) (unitLtOfPos _))
      (leB_of_lt (unitLtMul (unitLtOfPos _) (unitLtOfPos _)))
  have hpair : (poly.evalClear
        [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
        (BPair.ofPos gn) (gd * W) (1 + K3)).oneValue
      (ground.bpow (BPair.ofPos (gd * W)) K3
        * (BPair.ofPos (4 * (gd * K0)) * BPair.ofPos (gd * W)
          + BPair.ofPos (4 * (gd * K1)) * BPair.ofPos gn)) := by
    have h := poly.evalClear_pow
      [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
      (BPair.ofPos gn) (gd * W) (1 + K3) 1 (Nat.le_refl 2)
      (Nat.le_add_right 1 K3)
    rw [ground.addSubSelfL 1 K3] at h
    exact BPair.oneValue_trans h
      (BPair.mul_congr (BPair.oneValue_refl _) (ecPair _ _ _ _))
  have hZread : (poly.evalClear
        (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
          (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST))
        (BPair.ofPos gn) (gd * W) (1 + K3)).oneValue
      (ground.bpow (BPair.ofPos (gd * W)) K3
        * (BPair.ofPos (4 * (gd * K0)) * BPair.ofPos (gd * W)
          + BPair.ofPos (4 * (gd * K1)) * BPair.ofPos gn) + BPair.unit) :=
    BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
      (BPair.add_congr hpair (crossMul gn gd W ST K3 hST))
  have hPread : (poly.evalClear
        (poly.mul [BPair.ofPos (75 * Pos.pow dth 4)]
          (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
            (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST)))
        (BPair.ofPos gn) (gd * W) (1 + K3)).oneValue
      (BPair.ofPos (75 * Pos.pow dth 4)
        * (ground.bpow (BPair.ofPos (gd * W)) K3
            * (BPair.ofPos (4 * (gd * K0)) * BPair.ofPos (gd * W)
              + BPair.ofPos (4 * (gd * K1)) * BPair.ofPos gn) + BPair.unit)) := by
    have h := poly.evalClear_mul [BPair.ofPos (75 * Pos.pow dth 4)]
      (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
        (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST))
      (BPair.ofPos gn) (gd * W) 0 (1 + K3) (Nat.le_refl 1) hZ
    rw [Nat.zero_add] at h
    refine BPair.oneValue_trans h ?_
    refine BPair.mul_congr ?_ hZread
    exact BPair.oneValue_trans (poly.evalClear_single _ _ _ _)
      (BPair.mul_one_read _)
  have hread : (poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
        (BPair.ofPos gn) (gd * W) (1 + K3)).oneValue
      (BPair.ofPos (75 * Pos.pow dth 4)
        * (ground.bpow (BPair.ofPos (gd * W)) K3
            * (BPair.ofPos (4 * (gd * K0)) * BPair.ofPos (gd * W)
              + BPair.ofPos (4 * (gd * K1)) * BPair.ofPos gn) + BPair.unit)
        + BPair.unit) :=
    BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
      (BPair.add_congr hPread (crossMul gn gd W Rm K3 hRm))
  refine BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm hread) ?_
  exact unitLtAdd
    (unitLtMul (unitLtOfPos _)
      (unitLtAdd (unitLtMul (ground.unitLtBpow (unitLtOfPos (gd * W)) K3) hA01) (leB_refl BPair.unit)))
    (leB_refl BPair.unit)

/-- The composite point's evaluation reads the cleared evaluation at the
clearing's stated power, at every power bounding the list's keys. -/
private theorem clearedRead (p : poly.Poly) (l : BPair) (cc : Pos) (K : Nat)
    (hK : p.length ≤ K + 1) :
    (stage.evalC p ⟨l, cc⟩).oneValue
      ⟨poly.evalClear p l cc K, Pos.pow cc K⟩ :=
  CPair.oneValue_trans (stage.evalC_read p K hK l cc)
    (CPair.num_oneValue (poly.eval_clearVar p cc K l) (Pos.pow cc K))

/-- The composite evaluation sits on its lower side where the cleared
evaluation does, at every power bounding the list's keys. -/
private theorem evalC_lt_unit (p : poly.Poly) (l : BPair) (cc : Pos) (K : Nat)
    (hK : p.length ≤ K + 1) (h : poly.evalClear p l cc K < BPair.unit) :
    stage.evalC p ⟨l, cc⟩ < stage.unitC := by
  refine CPair.lt_congr (CPair.oneValue_symm (clearedRead p l cc K hK))
    (CPair.oneValue_refl stage.unitC) ?_
  show (poly.evalClear p l cc K).scale Pos.one
    < BPair.unit.scale (Pos.pow cc K)
  exact BPair.lt_congr
    (BPair.oneValue_symm (BPair.oneValue_of_eq (BPair.scale_one _)))
    (BPair.oneValue_symm (BPair.unit_scale (Pos.pow cc K))) h

/-- The comparison sits on its lower side at the crossing, read at a power
bounding the factors' keys: the leading read's members are equal there and
the tail's occupied root-cap term stands alone on the balance partner. -/
private theorem crossCore (gn gd W dth K0 K1 : Pos) (c : BPair) (ST Rm : poly.Poly)
    (K3 : Nat)
    (hST : ST.length ≤ K3 + 1) (hRm : Rm.length ≤ K3 + 1)
    (hZ : (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
            (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST)).length
        ≤ 1 + K3 + 1)
    (hT : (tailPoly gn gd W dth K0 K1 ST Rm).length ≤ 1 + K3 + 1)
    (hC : (compPoly gn gd W dth K0 K1 c ST Rm).length ≤ 1 + (1 + K3) + 1) :
    stage.evalC (compPoly gn gd W dth K0 K1 c ST Rm)
      ⟨BPair.ofPos gn, gd * W⟩ < stage.unitC := by
  have hTB := crossTail gn gd W dth K0 K1 ST Rm K3 hST hRm hZ
  have hE2 : (poly.evalClear [BPair.unit, BPair.ofNat 2]
      (BPair.ofPos gn) (gd * W) 1).oneValue
      (BPair.ofNat 2 * BPair.ofPos gn) :=
    BPair.oneValue_trans (ecPair _ _ _ _)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.unit_mul _) (BPair.oneValue_refl _))
        (BPair.unit_add _))
  have hB : (poly.evalClear (poly.mul [BPair.unit, BPair.ofNat 2]
        (tailPoly gn gd W dth K0 K1 ST Rm))
        (BPair.ofPos gn) (gd * W) (1 + (1 + K3))).oneValue
      (BPair.ofNat 2 * BPair.ofPos gn
        * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
            (BPair.ofPos gn) (gd * W) (1 + K3)) :=
    BPair.oneValue_trans
      (poly.evalClear_mul [BPair.unit, BPair.ofNat 2]
        (tailPoly gn gd W dth K0 K1 ST Rm) (BPair.ofPos gn) (gd * W)
        1 (1 + K3) (Nat.le_refl 2) hT)
      (BPair.mul_congr hE2 (BPair.oneValue_refl _))
  have hBpos : BPair.unit < BPair.ofNat 2 * BPair.ofPos gn
      * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
          (BPair.ofPos gn) (gd * W) (1 + K3) :=
    unitLtMul (unitLtMul (unitLtOfPos (posOfSucc 1)) (unitLtOfPos gn)) hTB
  have hcompRead : (poly.evalClear (compPoly gn gd W dth K0 K1 c ST Rm)
        (BPair.ofPos gn) (gd * W) (1 + (1 + K3))).oneValue
      (BPair.unit + (BPair.ofNat 2 * BPair.ofPos gn
        * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
            (BPair.ofPos gn) (gd * W) (1 + K3)).swap) :=
    BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
      (BPair.add_congr (crossMul gn gd W [c] (1 + K3) (Nat.le_add_left 1 (1 + K3)))
        (BPair.oneValue_trans (poly.evalClear_neg _ _ _ _)
          (ground.swap_congr hB)))
  refine evalC_lt_unit _ _ _ (1 + (1 + K3)) hC ?_
  refine BPair.lt_congr (BPair.oneValue_symm hcompRead)
    (BPair.oneValue_refl BPair.unit) ?_
  refine BPair.lt_congr (BPair.oneValue_symm (BPair.unit_add _))
    (BPair.oneValue_refl BPair.unit) ?_
  exact ground.swapLt_of_unitLt (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm (BPair.unit_add _)) hBpos)

/-- Each of five summands sits within their sum. -/
private theorem sumBound (a b z t e : Nat) :
    a ≤ a + b + z + t + e ∧ (b ≤ a + b + z + t + e
      ∧ (z ≤ a + b + z + t + e
        ∧ (t ≤ a + b + z + t + e ∧ e ≤ a + b + z + t + e))) := by
  have h1 : a + b + z + t ≤ a + b + z + t + e := Nat.le_add_right _ e
  have h2 : a + b + z ≤ a + b + z + t + e :=
    Nat.le_trans (Nat.le_add_right _ t) h1
  have h3 : a + b ≤ a + b + z + t + e :=
    Nat.le_trans (Nat.le_add_right _ z) h2
  exact ⟨Nat.le_trans (Nat.le_add_right a b) h3,
    Nat.le_trans (Nat.le_add_left b a) h3,
    Nat.le_trans (Nat.le_add_left z (a + b)) h2,
    Nat.le_trans (Nat.le_add_left t (a + b + z)) h1,
    Nat.le_add_left e (a + b + z + t)⟩

/-- A product's rescaling rides its second factor. -/
private theorem scaleMulR (x y : BPair) (w : Pos) :
    ((x * y).scale w).oneValue (x * y.scale w) :=
  BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofPos_scale w (x * y)))
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm (BPair.ofPos w) x y))
      (BPair.mul_congr (BPair.oneValue_refl x) (BPair.ofPos_scale w y)))

/-- A shared summand cancels off the order's strict read. -/
private theorem ltAddCancel {a b z : BPair} (h : z + a < z + b) : a < b := by
  show a.fst + b.snd < b.fst + a.snd
  refine ground.posLtCancelR (c := z.fst + z.snd) ?_
  have h' : z.fst + a.fst + (z.snd + b.snd) < z.fst + b.fst + (z.snd + a.snd) := h
  rw [ground.add_add_comm a.fst b.snd z.fst z.snd,
    ground.add_add_comm b.fst a.snd z.fst z.snd,
    ground.add_comm a.fst z.fst, ground.add_comm b.snd z.snd,
    ground.add_comm b.fst z.fst, ground.add_comm a.snd z.snd]
  exact h'

/-- The ray's squared point against the tie's fourth-power weight is the
sixth-power weight. -/
private theorem posP6 (k4c p : Pos) :
    p * p * (k4c * Pos.pow p 4) = k4c * Pos.pow p 6 := by
  rw [posSq p, ground.mul_left_comm (Pos.pow p 2) k4c (Pos.pow p 4),
    ← Pos.pow_add p 2 4]

/-- The ray's power at a doubled key is the squared ray's own power. -/
private theorem posQ2 (q : Pos) (TK : Nat) :
    Pos.pow q (2 * TK) = Pos.pow (q * q) TK := by
  rw [Pos.pow_mul q q TK, Nat.two_mul TK, Pos.pow_add q TK TK]

/-- The clearing's spare power factors out of the comparison's two terms,
the leading term's at its trailing factor and the tail's past the balance
partner. -/
private theorem facEq (U cB s m A2 T : BPair) :
    U * (cB * (s * m)) + (A2 * (m * T)).swap
      = (U * (cB * s) + (A2 * T).swap) * m := by
  rw [BPair.right_distrib, BPair.swap_mul, ← BPair.mul_assoc cB s m,
    ← BPair.mul_assoc U (cB * s) m, BPair.mul_comm m T,
    ← BPair.mul_assoc A2 T m]

/-- The leading read's factor at the ray: the crossing read
`gn q² − gd W p²` at the displayed spelling. -/
private theorem ggRead (gn gd W p q : Pos) :
    (poly.evalClear [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap]
        (BPair.ofPos (p * p)) (q * q) 1).oneValue
      ((BPair.ofPos gn).scale (q * q)
        + ((BPair.ofPos (gd * W)).scale (p * p)).swap) := by
  refine BPair.oneValue_trans (ecPair _ _ _ _) (BPair.add_congr ?_ ?_)
  · exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm (BPair.ofPos gn) (BPair.ofPos (q * q))))
      (BPair.ofPos_scale (q * q) (BPair.ofPos gn))
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.swap_mul (BPair.ofPos (gd * W)) (BPair.ofPos (p * p))))
      (ground.swap_congr ?_)
    exact BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.mul_comm (BPair.ofPos (gd * W)) (BPair.ofPos (p * p))))
      (BPair.ofPos_scale (p * p) (BPair.ofPos (gd * W)))

/-- The comparison's cleared read at the ray, split at the two summands and
withdrawn to the tail's own key: twice the tail's fold against the ray's
squared point sits strictly below the leading read at the tail's key. -/
private theorem clearGap (gn gd W dth K0 K1 : Pos) (c : BPair) (ST Rm : poly.Poly)
    (p q : Pos) (TK M : Nat)
    (hTK : (tailPoly gn gd W dth K0 K1 ST Rm).length ≤ TK + 1)
    (h : BPair.unit < poly.evalClear (compPoly gn gd W dth K0 K1 c ST Rm)
        (BPair.ofPos (p * p)) (q * q) (1 + (TK + M))) :
    BPair.ofNat 2 * BPair.ofPos (p * p)
        * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
            (BPair.ofPos (p * p)) (q * q) TK
      < ((BPair.ofPos gn).scale (q * q)
          + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
        * (c * ground.bpow (BPair.ofPos (q * q)) TK) := by
  have hE2 : (poly.evalClear [BPair.unit, BPair.ofNat 2]
      (BPair.ofPos (p * p)) (q * q) 1).oneValue
      (BPair.ofNat 2 * BPair.ofPos (p * p)) :=
    BPair.oneValue_trans (ecPair _ _ _ _)
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.unit_mul _) (BPair.oneValue_refl _))
        (BPair.unit_add _))
  have hTKM : (tailPoly gn gd W dth K0 K1 ST Rm).length ≤ TK + M + 1 :=
    Nat.le_trans hTK (Nat.add_le_add_right (Nat.le_add_right TK M) 1)
  have hTBp : (poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
        (BPair.ofPos (p * p)) (q * q) (TK + M)).oneValue
      (ground.bpow (BPair.ofPos (q * q)) M
        * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
            (BPair.ofPos (p * p)) (q * q) TK) := by
    have hh := poly.evalClear_pow (tailPoly gn gd W dth K0 K1 ST Rm)
      (BPair.ofPos (p * p)) (q * q) (TK + M) TK hTK (Nat.le_add_right TK M)
    rw [ground.addSubSelfL TK M] at hh
    exact hh
  have hA : (poly.evalClear
        (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] [c])
        (BPair.ofPos (p * p)) (q * q) (1 + (TK + M))).oneValue
      (((BPair.ofPos gn).scale (q * q)
          + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
        * (c * ground.bpow (BPair.ofPos (q * q)) (TK + M))) :=
    BPair.oneValue_trans
      (poly.evalClear_mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] [c]
        (BPair.ofPos (p * p)) (q * q) 1 (TK + M) (Nat.le_refl 2)
        (Nat.le_add_left 1 (TK + M)))
      (BPair.mul_congr (ggRead gn gd W p q) (poly.evalClear_single c _ _ _))
  have hB : (poly.evalClear (poly.mul [BPair.unit, BPair.ofNat 2]
        (tailPoly gn gd W dth K0 K1 ST Rm))
        (BPair.ofPos (p * p)) (q * q) (1 + (TK + M))).oneValue
      (BPair.ofNat 2 * BPair.ofPos (p * p)
        * (ground.bpow (BPair.ofPos (q * q)) M
          * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
              (BPair.ofPos (p * p)) (q * q) TK)) :=
    BPair.oneValue_trans
      (poly.evalClear_mul [BPair.unit, BPair.ofNat 2]
        (tailPoly gn gd W dth K0 K1 ST Rm) (BPair.ofPos (p * p)) (q * q)
        1 (TK + M) (Nat.le_refl 2) hTKM)
      (BPair.mul_congr hE2 hTBp)
  have hcomp : (poly.evalClear (compPoly gn gd W dth K0 K1 c ST Rm)
        (BPair.ofPos (p * p)) (q * q) (1 + (TK + M))).oneValue
      (((BPair.ofPos gn).scale (q * q)
          + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
        * (c * ground.bpow (BPair.ofPos (q * q)) (TK + M))
        + (BPair.ofNat 2 * BPair.ofPos (p * p)
          * (ground.bpow (BPair.ofPos (q * q)) M
            * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
                (BPair.ofPos (p * p)) (q * q) TK)).swap) :=
    BPair.oneValue_trans (poly.evalClear_add _ _ _ _ _)
      (BPair.add_congr hA
        (BPair.oneValue_trans (poly.evalClear_neg _ _ _ _)
          (ground.swap_congr hB)))
  have hfac : (((BPair.ofPos gn).scale (q * q)
          + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
        * (c * ground.bpow (BPair.ofPos (q * q)) (TK + M))
        + (BPair.ofNat 2 * BPair.ofPos (p * p)
          * (ground.bpow (BPair.ofPos (q * q)) M
            * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
                (BPair.ofPos (p * p)) (q * q) TK)).swap).oneValue
      ((((BPair.ofPos gn).scale (q * q)
            + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
          * (c * ground.bpow (BPair.ofPos (q * q)) TK)
        + (BPair.ofNat 2 * BPair.ofPos (p * p)
            * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
                (BPair.ofPos (p * p)) (q * q) TK).swap)
        * ground.bpow (BPair.ofPos (q * q)) M) := by
    exact BPair.oneValue_trans
      (BPair.add_congr
        (BPair.mul_congr (BPair.oneValue_refl _)
          (BPair.mul_congr (BPair.oneValue_refl c)
            (ground.bpow_add (BPair.ofPos (q * q)) TK M)))
        (BPair.oneValue_refl _))
      (BPair.oneValue_of_eq (facEq _ _ _ _ _ _))
  have hX : BPair.unit
      < ((BPair.ofPos gn).scale (q * q)
            + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
          * (c * ground.bpow (BPair.ofPos (q * q)) TK)
        + (BPair.ofNat 2 * BPair.ofPos (p * p)
            * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
                (BPair.ofPos (p * p)) (q * q) TK).swap :=
    ground.ltB_unscale (ground.leB_of_lt (ground.unitLtBpow (unitLtOfPos (q * q)) M))
      (BPair.lt_congr (BPair.oneValue_symm (BPair.unit_mul _))
        (BPair.oneValue_refl _)
        (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
          (BPair.oneValue_trans hcomp hfac) h))
  exact ground.swapLt_of_unitLt hX

/-- The comparison sits on its lower side at the crossing
(`lem:fourpoint`'s tail): at the point `[gn : gd W]`, `u W = γ'`, the
leading read's members are equal and the tail's occupied root-cap term
stands alone, so the evaluation reads below the unit at every tail
datum. -/
theorem compCross (gn gd W dth K0 K1 : Pos) (c : BPair) (ST Rm : poly.Poly) :
    stage.evalC (compPoly gn gd W dth K0 K1 c ST Rm)
      ⟨BPair.ofPos gn, gd * W⟩ < stage.unitC := by
  have hb := sumBound ST.length Rm.length
    (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
      (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST)).length
    (tailPoly gn gd W dth K0 K1 ST Rm).length
    (compPoly gn gd W dth K0 K1 c ST Rm).length
  exact crossCore gn gd W dth K0 K1 c ST Rm
    (ST.length + Rm.length
      + (poly.add [BPair.ofPos (4 * (gd * K0)), BPair.ofPos (4 * (gd * K1))]
          (poly.mul [BPair.ofPos gn, (BPair.ofPos (gd * W)).swap] ST)).length
      + (tailPoly gn gd W dth K0 K1 ST Rm).length
      + (compPoly gn gd W dth K0 K1 c ST Rm).length)
    (Nat.le_succ_of_le hb.1) (Nat.le_succ_of_le hb.2.1)
    (Nat.le_succ_of_le (Nat.le_trans hb.2.2.1 (Nat.le_add_left _ 1)))
    (Nat.le_succ_of_le (Nat.le_trans hb.2.2.2.1 (Nat.le_add_left _ 1)))
    (Nat.le_succ_of_le (Nat.le_trans
      (Nat.le_trans hb.2.2.2.2 (Nat.le_add_left _ 1)) (Nat.le_add_left _ 1)))

/-- The cell's floor (`lem:fourpoint`'s tail): at the priced side
certificate from the free end, a ray whose squared point sits in the
segment, and the tail's bracket at the ray cleared at the drift's
clearing, the four-point read sits at its upper side at the margin
`[1 : 2] τ⁴ c` or beyond: the crossing's lower side puts the segment
inside the drift's clearance, the comparison's positive read puts twice
the tail's fold below the leading read, and the bracket withdraws at the
clearing's occupied gap. -/
theorem cellFloor (gn gd W dth K0 K1 : Pos) (c : BPair) (ST Rm : poly.Poly)
    (hi : CPair) (N D : BPair)
    (hkeep : stage.keepUpper (compPoly gn gd W dth K0 K1 c ST Rm)
      stage.unitC hi N D)
    (p q : Pos)
    (hx : (⟨BPair.ofPos (p * p), q * q⟩ : CPair) ≤ hi)
    (K4n : BPair) (k4c : Pos) (TK M : Nat)
    (hTK : (tailPoly gn gd W dth K0 K1 ST Rm).length ≤ TK + 1)
    (hL : (compPoly gn gd W dth K0 K1 c ST Rm).length ≤ TK + 1 + M + 1)
    (hbr : (((BPair.ofPos gn).scale (q * q)
          + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
        * windowsep.mag (K4n.scale (Pos.pow q 4)
            + (c.scale (k4c * Pos.pow p 4)).swap)).scale (Pos.pow q (2 * TK))
      ≤ (poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
            (BPair.ofPos (p * p)) (q * q) TK).scale (k4c * Pos.pow p 6)) :
    c.scale (k4c * Pos.pow p 4) ≤ (BPair.ofNat 2 * K4n).scale (Pos.pow q 4) := by
  have hunit : stage.unitC ≤ (⟨BPair.ofPos (p * p), q * q⟩ : CPair) :=
    Or.inr (BPair.lt_congr (BPair.oneValue_symm (BPair.unit_scale (q * q)))
      (BPair.oneValue_symm (BPair.oneValue_of_eq (BPair.scale_one _)))
      (unitLtOfPos (p * p)))
  have hunitc : stage.unitC ≤ (⟨BPair.ofPos gn, gd * W⟩ : CPair) :=
    Or.inr (BPair.lt_congr (BPair.oneValue_symm (BPair.unit_scale (gd * W)))
      (BPair.oneValue_symm (BPair.oneValue_of_eq (BPair.scale_one _)))
      (unitLtOfPos gn))
  have hxc : (⟨BPair.ofPos (p * p), q * q⟩ : CPair)
      ≤ ⟨BPair.ofPos gn, gd * W⟩ := by
    match CPair.le_total hi ⟨BPair.ofPos gn, gd * W⟩ with
    | Or.inl hle => exact CPair.le_trans hx hle
    | Or.inr hle =>
      exact absurd
        (stage.keepUpper_all (compPoly gn gd W dth K0 K1 c ST Rm) stage.unitC
          hi N D hkeep ⟨BPair.ofPos gn, gd * W⟩ hunitc hle)
        (CPair.le_not_lt (Or.inr (compCross gn gd W dth K0 K1 c ST Rm)))
  have hnum : (BPair.ofPos (p * p)).scale (gd * W)
      ≤ (BPair.ofPos gn).scale (q * q) := hxc
  have hswapeq : ((BPair.ofPos (p * p)).scale (gd * W)).oneValue
      ((BPair.ofPos (gd * W)).scale (p * p)) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.ofPos_scale (gd * W) (BPair.ofPos (p * p))))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq
          (BPair.mul_comm (BPair.ofPos (gd * W)) (BPair.ofPos (p * p))))
        (BPair.ofPos_scale (p * p) (BPair.ofPos (gd * W))))
  have hGG : BPair.unit ≤ (BPair.ofPos gn).scale (q * q)
      + ((BPair.ofPos (gd * W)).scale (p * p)).swap :=
    ground.leB_unit_add (ground.leB_congr_left hswapeq hnum)
  have hKeq : TK + 1 + M + 1 = 1 + (TK + M) + 1 := by
    rw [Nat.add_right_comm TK 1 M, Nat.add_comm (TK + M) 1]
  have hK : (compPoly gn gd W dth K0 K1 c ST Rm).length ≤ 1 + (TK + M) + 1 := by
    rw [← hKeq]
    exact hL
  have hstrict := clearGap gn gd W dth K0 K1 c ST Rm p q TK M hTK
    (stage.evalFloor
      (fun j hj => BPair.oneValue_of_eq
        (ground.getAt_over BPair.unit
          (compPoly gn gd W dth K0 K1 c ST Rm) j (Nat.le_trans hK hj)))
      (BPair.ofPos (p * p)) (q * q)
      (stage.keepUpper_all (compPoly gn gd W dth K0 K1 c ST Rm) stage.unitC
        hi N D hkeep ⟨BPair.ofPos (p * p), q * q⟩ hunit hx))
  have hs := BPair.scale_lt (k4c * Pos.pow p 4) hstrict
  have hLread : ((BPair.ofNat 2 * BPair.ofPos (p * p)
        * poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
            (BPair.ofPos (p * p)) (q * q) TK).scale
        (k4c * Pos.pow p 4)).oneValue
      (BPair.ofNat 2
        * (poly.evalClear (tailPoly gn gd W dth K0 K1 ST Rm)
            (BPair.ofPos (p * p)) (q * q) TK).scale
          (k4c * Pos.pow p 6)) := by
    refine BPair.oneValue_trans
      (BPair.scale_congr (k4c * Pos.pow p 4)
        (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _))) ?_
    refine BPair.oneValue_trans (scaleMulR (BPair.ofNat 2) _ _) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (k4c * Pos.pow p 4)
        (BPair.ofPos_scale (p * p) _)) ?_
    refine BPair.oneValue_of_eq ?_
    rw [BPair.scale_scale, posP6 k4c p]
  have hRread : ((((BPair.ofPos gn).scale (q * q)
            + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
          * (c * ground.bpow (BPair.ofPos (q * q)) TK)).scale
        (k4c * Pos.pow p 4)).oneValue
      (((BPair.ofPos gn).scale (q * q)
          + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
        * (c.scale (k4c * Pos.pow p 4)).scale (Pos.pow q (2 * TK))) := by
    refine BPair.oneValue_trans (scaleMulR _ _ _) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (k4c * Pos.pow p 4)
        (BPair.mul_congr (BPair.oneValue_refl c)
          (BPair.oneValue_symm (ground.ofPos_pow (q * q) TK)))) ?_
    refine BPair.oneValue_trans
      (BPair.scale_congr (k4c * Pos.pow p 4)
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.mul_comm c (BPair.ofPos (Pos.pow (q * q) TK))))
          (BPair.ofPos_scale (Pos.pow (q * q) TK) c))) ?_
    refine BPair.oneValue_of_eq ?_
    rw [posQ2 q TK, BPair.scale_scale, BPair.scale_scale,
      ground.mul_comm (k4c * Pos.pow p 4) (Pos.pow (q * q) TK)]
  have hmid := BPair.lt_congr hLread hRread hs
  have hbr2 := ground.leB_mulR (ground.unitLeOfNat 2) hbr
  have hchain := ground.leB_ltB_trans hbr2 hmid
  have hLL : (BPair.ofNat 2
        * ((((BPair.ofPos gn).scale (q * q)
              + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
            * windowsep.mag (K4n.scale (Pos.pow q 4)
                + (c.scale (k4c * Pos.pow p 4)).swap)).scale
          (Pos.pow q (2 * TK)))).oneValue
      (((BPair.ofPos gn).scale (q * q)
          + ((BPair.ofPos (gd * W)).scale (p * p)).swap)
        * ((BPair.ofNat 2 * windowsep.mag (K4n.scale (Pos.pow q 4)
              + (c.scale (k4c * Pos.pow p 4)).swap)).scale
          (Pos.pow q (2 * TK)))) := by
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) (scaleMulR _ _ _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_left_comm _ _ _)) ?_
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (scaleMulR _ _ _))
  have hcancel := ground.ltB_unscale hGG
    (BPair.lt_congr
      (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.lt_congr hLL (BPair.oneValue_refl _) hchain))
  have hA : BPair.ofNat 2 * windowsep.mag (K4n.scale (Pos.pow q 4)
        + (c.scale (k4c * Pos.pow p 4)).swap)
      < c.scale (k4c * Pos.pow p 4) :=
    BPair.lt_of_scale_lt hcancel
  have hB1 : (K4n.scale (Pos.pow q 4)).swap + c.scale (k4c * Pos.pow p 4)
      ≤ windowsep.mag (K4n.scale (Pos.pow q 4)
          + (c.scale (k4c * Pos.pow p 4)).swap) :=
    windowsep.swap_le_mag (K4n.scale (Pos.pow q 4)
      + (c.scale (k4c * Pos.pow p 4)).swap)
  have hB3 : c.scale (k4c * Pos.pow p 4)
      ≤ windowsep.mag (K4n.scale (Pos.pow q 4)
          + (c.scale (k4c * Pos.pow p 4)).swap) + K4n.scale (Pos.pow q 4) :=
    ground.leB_congr_left (BPair.add_swap_self _ _)
      (ground.leB_add
        (ground.leB_congr_left (BPair.oneValue_of_eq (BPair.add_comm _ _)) hB1)
        (ground.leB_refl _))
  have hAA := BPair.lt_congr
    (BPair.ofNat_two_mul (windowsep.mag (K4n.scale (Pos.pow q 4)
      + (c.scale (k4c * Pos.pow p 4)).swap)))
    (BPair.oneValue_refl _) hA
  have hMK := ltAddCancel (ground.ltB_trans_le hAA hB3)
  refine ground.leB_congr_right ?_
    (ground.leB_of_lt (ground.leB_ltB_trans hB3
      (ground.ltB_add hMK (ground.leB_refl _))))
  exact BPair.oneValue_symm
    (BPair.oneValue_trans (scaleMulR (BPair.ofNat 2) K4n (Pos.pow q 4))
      (BPair.ofNat_two_mul (K4n.scale (Pos.pow q 4))))

end fourpoint
