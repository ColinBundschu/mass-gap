import MassGap.Assembly
/-!
`thm:memberchar`'s read layer.  The member character identity
`a_ρ ch_λ = a_{λ+ρ}` is read at the graded folds: the convolution
count is the product's own side count at a key, the Weyl fold's
members joined to the multiplicity family's, and the shifted
alternant enters at the four reads that determine it — the closure
at the letters (`assembly.wCloseRead`), the support at stated
witnesses against the shifted key (`assembly.wDomAt`), the top read
at that key (`assembly.wTopAt`), and the regular read off it
(`assembly.wRegRead`).  The multiplicity family carries its own
three: the reflection invariance of its counts, the support at
stated witnesses joining every member to the top content at a
natural simple fold, and the top count one.  The recursion's reads
sit beside them: the line test at a positive member, a bounded
search over the natural multiples capped at the ρ-height gap; the
line's weighted fold, the collapsed `G`-summand at `2 dot(μ, α_j)`
per hit; the dominant window, the keys at `λ+ρ` against a natural
simple fold kept beyond the unit at every coordinate; and the
recursion read, the trace display at every window key against every
fold key.  Two reads of the line close beneath them — its key read,
the test's truth the natural multiple within the cap, and its cap
read, a hit at any natural multiple sitting inside the search — over
the Γ-tier's own: the Cartan row's ρ-pairing at the scaled length,
off the Gram's defining diagonal.

The theorem tier stands at two publics over the family shape read
`mShapeRead` (every member normed at the rank's order).  `convDots`
is `thm:memberchar`'s cross-term identity `(XX)`: the recursion's
whole correction summed over the Weyl fold collects at the moved
keys' dot reads against the family's counts — the alternant fold
bridged to the subset families on both sides (`wFold_subsets`), the
grading pushed through the folds, the `(S, j)` and `(S, μ)`
exchanges, the line's capped hit count telescoped to the withdrawn
pair (`subsetCountOff_line`), the moved Euler collection
(`subsetCountOff_euler_moved`) closing per member, and the family
indicator collapsed at the key-move correspondence.  `eigenAt` is
the eigen identity `(E)` at every dominant-window key: the gap
`q₀(λ+ρ)` against the key's own square multiplies the convolution's
count pair to the sum's unit — the count pair read as the Weyl
fold's signed fold of family counts, the per-member square split at
the pairing's bilinearity, the recursion read consumed at the
window against every fold key, the cross term dying against
`(XX)`, and the residual squares dying at the unbalanced keys' one
dot square (`wOff_dotSq`) through the signed fold's pairing-off.

The conclusion tier closes the identity.  `identityAt` is the
per-key balance of the product's data with the shifted alternant's,
and `identityRead` is `thm:memberchar` itself: a reflection-graded
family at the four reads is the shifted alternant's graded fold key
by key (the determination, the walk at the abstract family against
the concrete data), and the convolution carries the four — the
letter transport from the Weyl data's closure with the family's
invariance, the support from the two witness folds' join, the
shifted key's one-and-none from the two tops at the witness folds'
`ρ`-dots joined to the sum's unit, and the regular read from the
eigen identity against the separation's strict gap at the
product's injectivity — with every key off the rank's normed frame
reading all four counts at the count's unit.  The dominant window's
completeness (an occupied strictly dominant key joins the window at
the capped coefficient sum) and the separation (the fall identity's
strict read at a window key off the shifted one) sit beneath the
regular read.
-/

namespace memberchar
open ground places sertables assembly

/-- The convolution count: the product `a_ρ ch`'s side count at a
key, the Weyl fold's members joined to the multiplicity family's,
one side each (`thm:memberchar`'s graded product). -/
def convCount (W : List (List BPair × Bool)) (L : List (List BPair))
    (y : List BPair) (side : Bool) : Nat :=
  ground.famFold Nat.add 0
    (fun vp => if vp.2 = side then
      ground.famFold Nat.add 0
        (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0) L
      else 0) W

/-- The multiplicity family's reflection invariance: each member's
reflected key carries the member's own count (`thm:memberchar`'s
`ch` invariant, `lem:strings`). -/
def symRead (t : gentable.Table) (L : List (List BPair)) : Prop :=
  ∀ nu ∈ L, ∀ i, i < t.rank →
    ground.countOf (reflAt t i nu) L = ground.countOf nu L

/-- The support read: every member joins the top content at a
natural simple fold (`thm:memberchar`'s support, `ν ⪯ λ` at the
block, `lem:lowerspan`). -/
def supportRead (t : gentable.Table) (L : List (List BPair))
    (wits : List (List Nat)) (lamV : List BPair) : Prop :=
  wits.length = L.length ∧ ∀ k, k < L.length →
    poly.pnorm (elim.vecAdd (ground.getAt [] L k)
      (cartanFold t (ground.getAt [] wits k))) = lamV

/-- The top read: the top content sits in the multiplicity family
once — the block's top-content summand on one line
(`lem:lowerspan`), the `ch`-side factor of `thm:memberchar`'s
`c_λ = 1` clause. -/
def topRead (L : List (List BPair)) (lamV : List BPair) : Prop :=
  ground.countOf lamV L = 1

/-- The top content's shape read: the rank's order, normed, every
entry at or beyond the unit — the dominance of `λ`
(`thm:memberchar`'s dominant top content). -/
def lamRead (t : gentable.Table) (lamV : List BPair) : Prop :=
  lamV.length = t.rank ∧ poly.pnorm lamV = lamV ∧
    ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit lamV k

instance (t : gentable.Table) (L : List (List BPair)) :
    Decidable (symRead t L) :=
  inferInstanceAs (Decidable (∀ nu ∈ L, ∀ i, i < t.rank →
    ground.countOf (reflAt t i nu) L = ground.countOf nu L))

instance (t : gentable.Table) (L : List (List BPair))
    (wits : List (List Nat)) (lamV : List BPair) :
    Decidable (supportRead t L wits lamV) :=
  inferInstanceAs (Decidable (wits.length = L.length ∧
    ∀ k, k < L.length → poly.pnorm (elim.vecAdd
      (ground.getAt [] L k)
      (cartanFold t (ground.getAt [] wits k))) = lamV))

instance (L : List (List BPair)) (lamV : List BPair) :
    Decidable (topRead L lamV) :=
  inferInstanceAs (Decidable (ground.countOf lamV L = 1))

instance (t : gentable.Table) (lamV : List BPair) :
    Decidable (lamRead t lamV) :=
  inferInstanceAs (Decidable (lamV.length = t.rank ∧
    poly.pnorm lamV = lamV ∧
    ∀ k, k < t.rank → BPair.unit ≤ ground.getAt BPair.unit lamV k))

/-- The shifted key reads beyond the unit at every coordinate: the
dominant top's entries joined to `ρ`'s unit entries —
`thm:memberchar`'s strictly dominant-shifted representative. -/
theorem shifted_reg (t : gentable.Table) (cV : List BPair)
    (hcV : lamRead t cV) :
    ∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd cV (rhoV t))) k := by
  intro k hk
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hvl : (elim.vecAdd cV (rhoV t)).length = t.rank :=
    elim.length_vecAdd cV _ t.rank hcV.1 hrl
  have hrho : ground.getAt BPair.unit (rhoV t) k = BPair.ofNat 1 :=
    ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank k hk
  have hentry : ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd cV (rhoV t))) k
      = BPair.norm (ground.getAt BPair.unit cV k + BPair.ofNat 1) := by
    show ground.getAt BPair.unit
      ((elim.vecAdd cV (rhoV t)).map BPair.norm) k = _
    rw [ground.getAt_map BPair.unit BPair.unit BPair.norm
        (elim.vecAdd cV (rhoV t)) k (by rw [hvl]; exact hk),
      elim.getAt_vecAdd cV (rhoV t) k (by rw [hcV.1]; exact hk)
        (by rw [hrl]; exact hk), hrho]
  rw [hentry]
  exact BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.add_comm (BPair.ofNat 1) (ground.getAt BPair.unit cV k)))
      (BPair.oneValue_symm (BPair.norm_oneValue _)))
    (ground.unitLtAdd (by decide +kernel : BPair.unit < BPair.ofNat 1)
      (hcV.2.2 k hk))

/-- The line test: the key `μ` sits on the `j`-line beyond `ν`, the
bounded search over the natural multiples within the two dots' gap
at the root's positive dot (`thm:memberchar`'s recursion at a
positive member, a line member within the gap at the root's own
dot). -/
def lineAt (t : gentable.Table) (F : FundData) (nu mu : List BPair)
    (j : Nat) : Bool :=
  ground.famFold Bool.or false
    (fun l => decide (poly.pnorm (elim.vecAdd nu
      (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))) = mu))
    (List.range (BPair.capN (BPair.add (dotB F mu (rhoV t))
        ((dotB F nu (rhoV t)).swap))
      / BPair.marginN (dotB F (posCorootV t j) (rhoV t))))

/-- The `j`-line's weighted fold over the family: the recursion's
collapsed `G`-summand, `2 dot(μ, α_j)` at each line hit
(`thm:memberchar`'s `G_α` at the telescope). -/
def gAt (t : gentable.Table) (F : FundData) (L : List (List BPair))
    (nu : List BPair) (j : Nat) : BPair :=
  ground.famFold BPair.add BPair.unit
    (fun mu => if lineAt t F nu mu j then
      BPair.add (dotB F mu (posCorootV t j)) (dotB F mu (posCorootV t j))
      else BPair.unit) L

/-- The `G`-summands' fold over the positive list, the recursion's
whole correction at a key (`thm:memberchar`'s `Σ_α 2 G_α`). -/
def gSum (t : gentable.Table) (F : FundData) (L : List (List BPair))
    (nu : List BPair) : BPair :=
  ground.famFold BPair.add BPair.unit (fun j => gAt t F L nu j)
    (List.range t.posFolds.length)

/-- The order against a cofactor: a count whose product with an
occupied divisor sits at or below the datum sits at or below the
division's read (`ground.natDivRead`, the naming identity at core
`Nat.div`). -/
private theorem le_div_of_mul_le {n m a : Nat} (hm : 0 < m)
    (hmul : a * m ≤ n) : a ≤ n / m := by
  have hread := ground.natDivRead n m hm
  match Nat.lt_or_ge (n / m) a with
  | Or.inr h => exact h
  | Or.inl h =>
    have he : (n / m + 1) * m = m * (n / m) + m := by
      rw [Nat.succ_mul, Nat.mul_comm (n / m) m]
    have h3 : m * (n / m) + m ≤ n :=
      he ▸ Nat.le_trans (Nat.mul_le_mul_right m h) hmul
    have h5 : n < m * (n / m) + m :=
      Nat.lt_of_le_of_lt (Nat.le_of_eq hread.1.symm)
        (Nat.add_lt_add_left hread.2 (m * (n / m)))
    exact absurd h3 (Nat.not_le_of_gt h5)

/-- A simple member's cleared `ρ`-dot at its margin. -/
private def simDotAt (t : gentable.Table) (F : FundData)
    (i : Nat) : Nat :=
  BPair.marginN (dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
    (rhoV t))

/-- The weighted box: the coefficient vectors whose fold against
the stated weights sits at or below the budget, one coordinate
per weight (`thm:memberchar`'s capped fold at the simple dots). -/
private def wBox : List Nat → Nat → List (List Nat)
  | [], _ => [[]]
  | d :: ds, D =>
    (List.range (D / d + 1)).flatMap (fun v =>
      (wBox ds (D - v * d)).map (fun m => v :: m))

/-- The weighted box's membership: a coefficient vector at the
weights' order whose fold against occupied weights sits at or
below the budget is a member. -/
private theorem wBox_mem : ∀ (ds : List Nat) (D : Nat) (c : List Nat),
    c.length = ds.length →
    (∀ k, k < ds.length → 0 < ground.getAt 0 ds k) →
    ground.sumNat (List.zipWith Nat.mul c ds) ≤ D →
    c ∈ wBox ds D
  | [], _, [], _, _, _ => List.Mem.head _
  | [], _, x :: t, hlen, _, _ =>
    nomatch (show Nat.succ t.length = 0 from hlen)
  | _ :: ds, _, [], hlen, _, _ =>
    nomatch (show Nat.succ ds.length = 0 from hlen.symm)
  | d :: ds, D, v :: c, hlen, hpos, hsum => by
    have hlen' : c.length = ds.length := Nat.succ.inj hlen
    have hd : 0 < d := hpos 0 (Nat.succ_pos ds.length)
    have hsum' : v * d + ground.sumNat (List.zipWith Nat.mul c ds)
        ≤ D := hsum
    have hvd : v * d ≤ D :=
      Nat.le_trans (Nat.le_add_right _ _) hsum'
    have hres : ground.sumNat (List.zipWith Nat.mul c ds)
        ≤ D - v * d := by
      refine ground.leCancelR (v * d) ?_
      rw [ground.subAdd hvd]
      rw [Nat.add_comm (v * d)
        (ground.sumNat (List.zipWith Nat.mul c ds))] at hsum'
      exact hsum'
    show (v :: c) ∈ (List.range (D / d + 1)).flatMap (fun w =>
      (wBox ds (D - w * d)).map (fun m => w :: m))
    refine ground.mem_flatMap_to _
      (ground.memRange (Nat.lt_succ_of_le
        (le_div_of_mul_le hd hvd))) ?_
    exact ground.mem_map_to (fun m => v :: m)
      (wBox_mem ds (D - v * d) c hlen'
        (fun k hk => hpos (k + 1) (Nat.succ_lt_succ hk)) hres)

/-- The dominant window at the fundamental data: the keys at
`λ+ρ` against a natural simple fold over the weighted box, the
coefficients' fold against the simples' `ρ`-dots capped at the
height read, kept at every entry beyond the unit
(`thm:memberchar`'s dominant support at the capped fold). -/
def domWindow (t : gentable.Table) (F : FundData)
    (lamV : List BPair) : List (List BPair) :=
  ((wBox ((List.range t.rank).map (simDotAt t F))
      (BPair.capN (dotB F lamV (rhoV t)))).map (fun c =>
    poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (poly.neg (cartanFold t c))))).filter
    (fun y => decide (∀ k, k < t.rank →
      BPair.unit < ground.getAt BPair.unit y k))

/-- The recursion read at the consumed keys: the display at every
dominant-window key against every fold key (`lem:casimir`'s trace
recursion at `thm:memberchar`'s eigen-read). -/
def recRead (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (lamV : List BPair) : Prop :=
  ∀ y ∈ domWindow t F lamV, ∀ vp ∈ W,
    BPair.oneValue
      (BPair.mul (dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
          (poly.pnorm (elim.vecAdd lamV (rhoV t))))
        (BPair.ofNat (ground.countOf
          (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L)))
      (BPair.add
        (BPair.mul (dotB F
            (poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd y
              (poly.neg vp.1))) (rhoV t)))
            (poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd y
              (poly.neg vp.1))) (rhoV t))))
          (BPair.ofNat (ground.countOf
            (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L)))
        (gSum t F L (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))))

instance (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (lamV : List BPair) : Decidable (recRead t F W L lamV) :=
  inferInstanceAs (Decidable (∀ y ∈ domWindow t F lamV, ∀ vp ∈ W,
    BPair.oneValue _ _))

/-- The Cartan row's `ρ`-pairing: the row against `ρ` reads the
scaled length at its own key (`thm:memberchar`'s eigen-read at the
Gram's defining diagonal). -/
theorem dotB_cartan_rho (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F) {i : Nat}
    (hi : i < t.rank) :
    (dotB F (ground.getAt [] t.cartan i) (rhoV t)).oneValue
      (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)) := by
  refine BPair.oneValue_trans
    (assembly.diagRow t F hshape hgram (rhoV t)
      (ground.length_replicate (BPair.ofNat 1) t.rank)
      i (by rw [assembly.cartanLen t F hgram]; exact hi)) ?_
  have hrho : ground.getAt BPair.unit (rhoV t) i = BPair.ofNat 1 :=
    ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi
  rw [hrho]
  exact BPair.mul_ofNat_one _

/-- The line test's key read: the test is true exactly at a natural
multiple within the cap whose join carries `ν` to `μ`
(`thm:memberchar`'s recursion at a positive member). -/
theorem lineAt_iff (t : gentable.Table) (F : FundData)
    (nu mu : List BPair) (j : Nat) :
    lineAt t F nu mu j = true ↔
      ∃ l, l < BPair.capN (BPair.add (dotB F mu (rhoV t))
            ((dotB F nu (rhoV t)).swap))
          / BPair.marginN (dotB F (posCorootV t j) (rhoV t))
        ∧ poly.pnorm (elim.vecAdd nu
            (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))) = mu :=
  Iff.intro
    (fun h => by
      obtain ⟨i, hi, hfi⟩ := ground.orRange_read _ _ h
      exact ⟨i, hi, of_decide_eq_true hfi⟩)
    (fun h => by
      obtain ⟨l, hl, hhit⟩ := h
      exact ground.orRange_intro _ _ l hl (decide_eq_true hhit))

/-! The line's own cap: a hit at any natural multiple sits inside
the ρ-height gap's cap, so the bounded search finds it.  The
carrier's product order enters here at its second member. -/

/-- The line step's height read: a key one natural multiple of the
`j`-th positive member beyond `ν` pairs against `ρ` at `ν`'s own
pairing joined to the scaled member's. -/
private theorem dotB_step (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) {j : Nat} (nu mu : List BPair)
    (hnu : t.rank ≤ nu.length) (l : Nat)
    (hhit : poly.pnorm (elim.vecAdd nu
      (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))) = mu) :
    (dotB F mu (rhoV t)).oneValue
      (dotB F nu (rhoV t)
        + BPair.ofNat (l + 1) * dotB F (posCorootV t j) (rhoV t)) := by
  have hG : (elim.matVec F.gram (rhoV t)).length = t.rank :=
    (elim.matVec_length F.gram (rhoV t)).trans hshape.1
  have hA : (posCorootV t j).length = t.rank :=
    ground.length_mapRange _ t.rank
  have hS : (elim.vecScale (BPair.ofNat (l + 1))
      (posCorootV t j)).length = t.rank :=
    (elim.length_vecScale _ _).trans hA
  have h1 : (dotB F mu (rhoV t)).oneValue
      (elim.dotP (elim.vecAdd nu (elim.vecScale
        (BPair.ofNat (l + 1)) (posCorootV t j)))
        (elim.matVec F.gram (rhoV t))) := by
    rw [← hhit]
    exact elim.dotP_oneValue_left _ _ _ (poly.pnorm_oneValue _)
  refine BPair.oneValue_trans h1 ?_
  refine BPair.oneValue_trans
    (elim.dotP_vecAdd_left nu _ _ (by rw [hG]; exact hnu)
      (by rw [hG, hS]; exact Nat.le_refl _)) ?_
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  rw [elim.dotP_comm (elim.vecScale (BPair.ofNat (l + 1))
    (posCorootV t j)) (elim.matVec F.gram (rhoV t))]
  refine BPair.oneValue_trans
    (elim.dotP_vecScale_right _ _ _) ?_
  refine BPair.mul_congr (BPair.oneValue_refl _) ?_
  rw [elim.dotP_comm (elim.matVec F.gram (rhoV t)) (posCorootV t j)]
  exact BPair.oneValue_refl _

/-- The line's cap read: a key one natural multiple of the `j`-th
positive member beyond `ν` sits inside the search's cap, the gap
of the two `ρ`-heights the member's own positive dot scaled
(`thm:memberchar`'s recursion at a positive member); the fold key's bound `hj` is `con:sertables`' frame, the positive list's own enumeration. -/
theorem lineAt_of_hit (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hrd : rhoDotRead t F) {j : Nat}
    (hj : j < t.posFolds.length) (nu mu : List BPair)
    (hnu : t.rank ≤ nu.length) (l : Nat)
    (hhit : poly.pnorm (elim.vecAdd nu
      (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))) = mu) :
    lineAt t F nu mu j = true := by
  have hsplit := dotB_step t F hshape nu mu hnu l hhit
  -- the cap's own datum is the scaled dot
  have hgap : (BPair.ofNat (l + 1)
      * dotB F (posCorootV t j) (rhoV t)).oneValue
      (BPair.add (dotB F mu (rhoV t)) ((dotB F nu (rhoV t)).swap)) := by
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr hsplit (BPair.oneValue_refl _)) ?_)
    have hre : dotB F nu (rhoV t)
          + BPair.ofNat (l + 1) * dotB F (posCorootV t j) (rhoV t)
          + (dotB F nu (rhoV t)).swap
        = BPair.ofNat (l + 1) * dotB F (posCorootV t j) (rhoV t)
          + (dotB F nu (rhoV t) + (dotB F nu (rhoV t)).swap) := by
      rw [BPair.add_assoc, BPair.add_left_comm]
    rw [hre]
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.oneValue_refl _) (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm (dotB F nu (rhoV t))
          (dotB F nu (rhoV t)).swap))
        (BPair.swap_add_null
          (BPair.oneValue_refl (dotB F nu (rhoV t)))))) ?_
    exact BPair.add_unit _
  -- the count's product with the root's dot sits at the cap's datum
  have hbound : BPair.ofNat
      ((l + 1) * BPair.marginN (dotB F (posCorootV t j) (rhoV t)))
      ≤ BPair.add (dotB F mu (rhoV t)) ((dotB F nu (rhoV t)).swap) := by
    refine ground.leB_congr_right hgap ?_
    refine ground.leB_congr_left (BPair.oneValue_symm
      (BPair.ofNat_mul (l + 1)
        (BPair.marginN (dotB F (posCorootV t j) (rhoV t))))) ?_
    refine ground.leB_mulR (ground.unitLeOfNat (l + 1)) ?_
    exact ground.leB_congr_right
      (BPair.oneValue_symm (BPair.ofNat_marginN
        (ground.leB_of_lt (hrd j hj))))
      (ground.leB_refl _)
  exact (lineAt_iff t F nu mu j).mpr
    ⟨l, le_div_of_mul_le (BPair.marginN_pos (hrd j hj))
      (ground.BPair.ofNat_le_capN hbound), hhit⟩

/-! The telescope: the `j`-line's fold at a key reads the fold at the
key one step along the line, joined to that step's own weighted
count.  Every hit two steps or beyond is a hit of the stepped key's
own line, the stepped key is the one member the two lines read
apart, and the stepped key sits off its own line at the positive
member's strictly rising `ρ`-dot. -/

/-- The further line steps: a multiple two or beyond of the `j`-th
positive member beyond `ν` sits one multiple lower beyond the
stepped key. -/
private theorem stepKey (t : gentable.Table) (j : Nat)
    (nu : List BPair) (hnu : nu.length = t.rank) (l : Nat) :
    poly.pnorm (elim.vecAdd nu
        (elim.vecScale (BPair.ofNat (l + 1 + 1)) (posCorootV t j)))
      = poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd nu (posCorootV t j)))
          (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))) := by
  have hA : (posCorootV t j).length = t.rank := posCorootV_length t j
  have hS : (elim.vecScale (BPair.ofNat (l + 1))
      (posCorootV t j)).length = t.rank :=
    (elim.length_vecScale _ _).trans hA
  have hNA : (elim.vecAdd nu (posCorootV t j)).length = t.rank :=
    elim.length_vecAdd nu _ t.rank hnu hA
  rw [elim.pnorm_vecAdd_left _ _ (hNA.trans hS.symm),
    elim.vecAdd_assoc nu (posCorootV t j)
      (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))]
  refine poly.pnorm_congr _ _ ?_ ?_
  · rw [elim.length_vecAdd nu _ t.rank hnu
      ((elim.length_vecScale _ _).trans hA),
      elim.length_vecAdd nu _ t.rank hnu
        (elim.length_vecAdd _ _ t.rank hA hS)]
  · refine elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl nu) ?_ rfl ?_
    · refine poly.oneValue_trans
        (elim.vecScale_congr (BPair.ofNat_succ (l + 1))
          (posCorootV t j)) ?_
      rw [elim.vecScale_add (BPair.ofNat (l + 1)) (BPair.ofNat 1)
          (posCorootV t j),
        elim.vecAdd_comm
          (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))
          (elim.vecScale (BPair.ofNat 1) (posCorootV t j))]
      exact elim.polyOne_vecAdd _ _ _ _ (elim.vecScale_one _)
        (poly.oneValue_refl _) (elim.length_vecScale _ _) rfl
    · rw [elim.length_vecScale, elim.length_vecAdd _ _ t.rank hA hS, hA]

/-- The stepped key sits off its own `j`-line: a hit would read the
key's `ρ`-height at its own joined to the member's scaled dot, where
that dot sits strictly above the sum's unit. -/
private theorem lineAt_self_off (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hrd : rhoDotRead t F) {j : Nat}
    (hj : j < t.posFolds.length) (v : List BPair)
    (hv : t.rank ≤ v.length) : ¬ lineAt t F v v j = true := fun hb => by
  obtain ⟨l, _, hhit⟩ := (lineAt_iff t F v v j).mp hb
  have hs := dotB_step t F hshape v v hv l hhit
  have hc : BPair.unit.oneValue
      (BPair.ofNat (l + 1) * dotB F (posCorootV t j) (rhoV t)) := by
    refine ground.BPair.add_cancel (c := dotB F v (rhoV t)) ?_
    exact BPair.oneValue_trans (BPair.unit_add _)
      (BPair.oneValue_trans hs
        (BPair.oneValue_of_eq (BPair.add_comm _ _)))
  exact absurd (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm hc)
    (ground.unitLtMul (ground.unitLtOfNat l) (hrd j hj))) (by decide +kernel)

/-- The `j`-line's telescope: the line's fold at a key reads the
fold at the key one step along, joined to the step's own weighted
count — the stepped key's doubled dot at its count in the family
(`thm:memberchar`'s telescope). -/
theorem gAt_tel (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hrd : rhoDotRead t F)
    (L : List (List BPair)) (nu : List BPair)
    (hnu : nu.length = t.rank) {j : Nat}
    (hj : j < t.posFolds.length) :
    (gAt t F L nu j).oneValue
      (BPair.add
        (gAt t F L (poly.pnorm (elim.vecAdd nu (posCorootV t j))) j)
        (BPair.mul
          (BPair.add
            (dotB F (poly.pnorm (elim.vecAdd nu (posCorootV t j)))
              (posCorootV t j))
            (dotB F (poly.pnorm (elim.vecAdd nu (posCorootV t j)))
              (posCorootV t j)))
          (BPair.ofNat (ground.countOf
            (poly.pnorm (elim.vecAdd nu (posCorootV t j))) L)))) := by
  have hA : (posCorootV t j).length = t.rank := posCorootV_length t j
  have hnuLe : t.rank ≤ nu.length := Nat.le_of_eq hnu.symm
  have hnu' : t.rank ≤ (poly.pnorm
      (elim.vecAdd nu (posCorootV t j))).length :=
    Nat.le_of_eq ((poly.pnorm_length _).trans
      (elim.length_vecAdd nu _ t.rank hnu hA)).symm
  -- the stepped key is on the key's own line
  have hhead : lineAt t F nu
      (poly.pnorm (elim.vecAdd nu (posCorootV t j))) j = true :=
    lineAt_of_hit t F hshape hrd hj nu _ hnuLe 0 (assembly.lineKey_one t (j := j) nu hnu)
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _ (fun mu =>
      (if lineAt t F (poly.pnorm (elim.vecAdd nu (posCorootV t j)))
            mu j then
          BPair.add (dotB F mu (posCorootV t j))
            (dotB F mu (posCorootV t j))
        else BPair.unit)
      + (if mu = poly.pnorm (elim.vecAdd nu (posCorootV t j)) then
          BPair.add
            (dotB F (poly.pnorm (elim.vecAdd nu (posCorootV t j)))
              (posCorootV t j))
            (dotB F (poly.pnorm (elim.vecAdd nu (posCorootV t j)))
              (posCorootV t j))
        else BPair.unit)) L (fun mu _ => ?_)) ?_
  · by_cases hmu : mu = poly.pnorm (elim.vecAdd nu (posCorootV t j))
    · rw [hmu, if_pos hhead, if_pos (rfl : poly.pnorm
        (elim.vecAdd nu (posCorootV t j))
          = poly.pnorm (elim.vecAdd nu (posCorootV t j))),
        if_neg (lineAt_self_off t F hshape hrd hj _ hnu')]
      exact BPair.oneValue_symm (BPair.unit_add _)
    · rw [if_neg hmu]
      by_cases h1 : lineAt t F nu mu j = true
      · obtain ⟨l, _, hhit⟩ := (lineAt_iff t F nu mu j).mp h1
        have h2 : lineAt t F
            (poly.pnorm (elim.vecAdd nu (posCorootV t j))) mu j = true := by
          match l with
          | 0 => exact absurd ((assembly.lineKey_one t (j := j) nu hnu).symm.trans hhit).symm hmu
          | l' + 1 =>
            refine lineAt_of_hit t F hshape hrd hj _ mu hnu' l' ?_
            rw [← stepKey t j nu hnu l']
            exact hhit
        rw [if_pos h1, if_pos h2]
        exact BPair.oneValue_symm (BPair.add_unit _)
      · have h2 : ¬ lineAt t F
            (poly.pnorm (elim.vecAdd nu (posCorootV t j))) mu j = true :=
          fun hb => by
            obtain ⟨l, _, hhit⟩ := (lineAt_iff t F _ mu j).mp hb
            refine h1 (lineAt_of_hit t F hshape hrd hj nu mu hnuLe
              (l + 1) ?_)
            rw [stepKey t j nu hnu l]
            exact hhit
        rw [if_neg h1, if_neg h2]
        exact BPair.oneValue_symm (BPair.add_unit _)
  · refine BPair.oneValue_trans (ground.foldB_add _ _ L) ?_
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans (ground.foldB_indicator _ _ L) ?_
    exact BPair.oneValue_of_eq (BPair.mul_comm _ _)

/-! The height calculus's ground: the table's lengths are occupied,
and the Gram's action on `ρ` reads at or beyond the sum's unit at
every key.  Both sit at the Cartan row's `ρ`-pairing, the simple's
own positive member read through the one-hot coroot fold. -/

/-- The table's lengths are occupied: the length at a key enters
beyond zero, the simple's own `ρ`-dot read at the Gram's defining
diagonal (`con:sertables`' displayed positive lengths). -/
theorem lenNums_pos (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (hgram : gramRead t F) {i : Nat}
    (hi : i < t.rank) : 0 < ground.getAt 0 t.lenNums i := by
  have hj : ground.getAt 0 F.simplePos i < t.posFolds.length :=
    of_decide_eq_true (ground.all_getAt 0 F.simplePos
      hshape.2.2.2.2.2.1 i (by rw [hshape.2.2.2.1]; exact hi))
  -- the simple's positive member reads the scaled length at ρ's key
  have htr : (dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
      (rhoV t)).oneValue
      (BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i)) := by
    refine BPair.oneValue_trans
      (assembly.dotB_simple t F hshape hgram hsp hi (rhoV t)
        (ground.length_replicate (BPair.ofNat 1) t.rank)) ?_
    rw [show rhoV t = List.replicate t.rank (BPair.ofNat 1) from rfl,
      ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank i hi]
    exact BPair.mul_ofNat_one _
  have hlt : BPair.unit
      < BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i) :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit) htr
      (hrd (ground.getAt 0 F.simplePos i) hj)
  have hm : 0 < F.scale * ground.getAt 0 t.lenNums i := by
    match Nat.eq_zero_or_pos (F.scale * ground.getAt 0 t.lenNums i) with
    | Or.inr h => exact h
    | Or.inl h0 =>
      rw [h0] at hlt
      exact absurd hlt (by decide +kernel)
  match Nat.eq_zero_or_pos (ground.getAt 0 t.lenNums i) with
  | Or.inr h => exact h
  | Or.inl h0 =>
    rw [h0, Nat.mul_zero] at hm
    exact absurd hm (Nat.lt_irrefl 0)

/-- The Gram's action on `ρ` at a key sits at or beyond the sum's
unit: the key's own one-hot content is dominant, so its `ρ`-pairing
collects the positive list's halved products (`thm:memberchar`'s
height calculus, `thm:assembly`'s dominance pin). -/
theorem gramRho_nonneg (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hrho : gentable.rhoRead t) {i : Nat}
    (hi : i < t.rank) :
    BPair.unit ≤ ground.getAt BPair.unit
      (elim.matVec F.gram (rhoV t)) i := by
  have hG : (elim.matVec F.gram (rhoV t)).length = t.rank :=
    (elim.matVec_length F.gram (rhoV t)).trans hshape.1
  have hlen : ((List.range t.rank).map (fun k =>
      if k == i then BPair.ofNat 1 else BPair.unit)).length
      = t.rank :=
    ground.length_mapRange _ t.rank
  have hread : ∀ q, q < t.rank → ground.getAt BPair.unit
      ((List.range t.rank).map (fun k =>
        if k == i then BPair.ofNat 1 else BPair.unit)) q
      = if q == i then BPair.ofNat 1 else BPair.unit := fun q hq => by
    rw [ground.getAt_map 0 BPair.unit _ (List.range t.rank) q
      (by rw [ground.length_range]; exact hq),
      ground.getAt_range t.rank q hq]
  have hdom := assembly.dotB_dom_nonneg t F hshape hgram hgsym hrho
    ((List.range t.rank).map (fun k =>
      if k == i then BPair.ofNat 1 else BPair.unit)) hlen
    (fun q hq => by
      rw [hread q hq]
      by_cases hqi : q = i
      · rw [if_pos (ground.eqBeqOf hqi)]
        exact ground.unitLeOfNat 1
      · rw [if_neg (fun hb => hqi (ground.beqEqOf hb))]
        exact ground.leB_refl _)
  refine ground.leB_congr_right ?_ hdom
  show (elim.dotP ((List.range t.rank).map (fun k =>
      if k == i then BPair.ofNat 1 else BPair.unit))
    (elim.matVec F.gram (rhoV t))).oneValue _
  rw [elim.dotP_comm]
  refine BPair.oneValue_trans (elim.dotP_oneIndex
    (elim.matVec F.gram (rhoV t)) _ i (by rw [hlen, hG])
    (by rw [hlen]; exact hi)
    (fun q hq hne => by
      rw [hlen] at hq
      rw [hread q hq, if_neg (fun hb => hne (ground.beqEqOf hb))]
      exact BPair.oneValue_refl _)) ?_
  rw [hread i hi, if_pos (ground.eqBeqOf rfl)]
  exact BPair.mul_ofNat_one _

/-- The multiplicity family's shape read: every member sits at the
rank's order, normed — the matched-list carrier (`con:places`) at
`thm:memberchar`'s multiplicity family. -/
def mShapeRead (t : gentable.Table) (L : List (List BPair)) : Prop :=
  ∀ mu ∈ L, mu.length = t.rank ∧ poly.pnorm mu = mu

instance (t : gentable.Table) (L : List (List BPair)) :
    Decidable (mShapeRead t L) :=
  inferInstanceAs (Decidable (∀ mu ∈ L,
    mu.length = t.rank ∧ poly.pnorm mu = mu))

/-! The key moves: the shift past a stated key's move commutes with
the move itself, and the move is its own inverse at normed keys of
the rank's order.  The pair literalizes the line's hits — a family
key sits on the line beyond the moved key exactly where the member's
own move lands at the family key. -/

/-- The shift past a move: norming the moved key first changes
nothing the shift reads. -/
private theorem shiftMove (n : Nat) (y v d : List BPair)
    (hy : y.length = n) (hv : v.length = n) (hd : d.length = n) :
    poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd y v)) d)
      = poly.pnorm (elim.vecAdd (elim.vecAdd y d) v) := by
  rw [elim.pnorm_vecAdd_left _ _
      ((elim.length_vecAdd y v n hy hv).trans hd.symm),
    elim.vecAdd_assoc y v d, elim.vecAdd_comm v d,
    ← elim.vecAdd_assoc y d v]

/-- The move's own correspondence, both ways. -/
private theorem offKey_iff (n : Nat) (y k mu : List BPair)
    (hy : y.length = n) (hk : k.length = n) (hkn : poly.pnorm k = k)
    (hm : mu.length = n) (hmn : poly.pnorm mu = mu) :
    poly.pnorm (elim.vecAdd y (poly.neg k)) = mu ↔
      poly.pnorm (elim.vecAdd y (poly.neg mu)) = k :=
  Iff.intro (offKey_swap n y k mu hy hk hkn)
    (offKey_swap n y mu k hy hm hmn)

/-- The line's hit correspondence: the shifted move of a family key
lands at a member exactly where the member's own shifted move lands
at the family key. -/
private theorem lineKey_iff (n : Nat) (y k mu d : List BPair)
    (hy : y.length = n) (hd : d.length = n)
    (hk : k.length = n) (hkn : poly.pnorm k = k)
    (hm : mu.length = n) (hmn : poly.pnorm mu = mu) :
    poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd y (poly.neg k))) d) = mu ↔
      poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd y (poly.neg mu))) d) = k := by
  rw [shiftMove n y (poly.neg k) d hy
      ((ground.length_map BPair.swap k).trans hk) hd,
    shiftMove n y (poly.neg mu) d hy
      ((ground.length_map BPair.swap mu).trans hm) hd]
  exact offKey_iff n (elim.vecAdd y d) k mu
    (elim.length_vecAdd y d n hy hd) hk hkn hm hmn

/-! The line's height calculus at `ρ`'s own slot: a key one natural
multiple of the `j`-th positive member beyond a base pairs against
`ρ` at the base's own pairing joined to the member's scaled dot, and
that dot sits strictly above the sum's unit.  The keys along the
line are therefore distinct, their heights rise with the multiple,
and a multiple exists whose key sits strictly beyond `ρ`'s own
height — the telescope's cap. -/

/-- The line key's height: the base's own pairing joined to the
member's scaled dot. -/
private theorem lineHt (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (j : Nat) (z : List BPair)
    (hz : z.length = t.rank) (l : Nat) :
    (dotB F (rhoV t) (poly.pnorm (elim.vecAdd z
        (elim.vecScale (BPair.ofNat (l + 1))
          (posCorootV t j))))).oneValue
      (dotB F (rhoV t) z
        + BPair.ofNat (l + 1) * dotB F (rhoV t) (posCorootV t j)) := by
  have hA : (posCorootV t j).length = t.rank := posCorootV_length t j
  have hS : (elim.vecScale (BPair.ofNat (l + 1))
      (posCorootV t j)).length = t.rank :=
    (elim.length_vecScale _ _).trans hA
  refine BPair.oneValue_trans
    (dotB_congrR F (rhoV t) _ _ (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans
    (dotB_addR t F hshape (rhoV t) z _
      (ground.length_replicate (BPair.ofNat 1) t.rank) hz hS) ?_
  exact BPair.add_congr (BPair.oneValue_refl _)
    (dotB_scaleR F _ (rhoV t) (posCorootV t j))

/-- The positive member's own height sits strictly above the sum's
unit, `ρ` read at the pairing's first slot. -/
private theorem rootHt (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length) :
    BPair.unit < dotB F (rhoV t) (posCorootV t j) :=
  BPair.lt_congr (BPair.oneValue_refl _)
    (assembly.dotB_swap t F hshape hgsym (posCorootV t j) (rhoV t)
      (posCorootV_length t j)
      (ground.length_replicate (BPair.ofNat 1) t.rank))
    (hrd j hj)

/-- A datum strictly above the sum's unit is off the vacant count's
scale. -/
private theorem scaleUnit {A : BPair} (hA : BPair.unit < A)
    (e : Nat) :
    ¬ (BPair.ofNat 0 * A).oneValue (BPair.ofNat (e + 1) * A) :=
  fun h => absurd (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
    (BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.oneValue_symm (BPair.unit_mul A)) h))
    (ground.unitLtMul (ground.unitLtOfNat e) hA)) (by decide +kernel)

/-- The counts' scales part at a datum strictly above the sum's
unit. -/
private theorem scaleInj {A : BPair} (hA : BPair.unit < A) :
    ∀ (a b : Nat),
    (BPair.ofNat a * A).oneValue (BPair.ofNat b * A) → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (scaleUnit hA _)
  | _ + 1, 0, h => absurd (BPair.oneValue_symm h) (scaleUnit hA _)
  | a + 1, b + 1, h => congrArg (fun z => z + 1) (scaleInj hA a b (by
      refine BPair.add_cancel (c := BPair.ofNat 1 * A) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.mul_congr_left (BPair.ofNat_succ a))
          (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)))) ?_
      refine BPair.oneValue_trans h ?_
      exact BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.ofNat_succ b))
        (BPair.oneValue_of_eq (BPair.right_distrib _ _ _))))

/-- The line's keys part: two natural multiples reading one key are
the same multiple. -/
private theorem lineKey_inj (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (z : List BPair) (hz : z.length = t.rank) {a b : Nat}
    (h : poly.pnorm (elim.vecAdd z (elim.vecScale
          (BPair.ofNat (a + 1)) (posCorootV t j)))
        = poly.pnorm (elim.vecAdd z (elim.vecScale
          (BPair.ofNat (b + 1)) (posCorootV t j)))) :
    a = b := by
  have hEq : (dotB F (rhoV t) z
        + BPair.ofNat (a + 1) * dotB F (rhoV t) (posCorootV t j)).oneValue
      (dotB F (rhoV t) z
        + BPair.ofNat (b + 1) * dotB F (rhoV t) (posCorootV t j)) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (lineHt t F hshape j z hz a))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (congrArg (dotB F (rhoV t)) h))
        (lineHt t F hshape j z hz b))
  have hc : (BPair.ofNat (a + 1)
        * dotB F (rhoV t) (posCorootV t j)).oneValue
      (BPair.ofNat (b + 1) * dotB F (rhoV t) (posCorootV t j)) := by
    refine BPair.add_cancel (c := dotB F (rhoV t) z) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    exact BPair.oneValue_trans hEq
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
  exact Nat.succ.inj (scaleInj (rootHt t F hshape hgsym hrd hj)
    (a + 1) (b + 1) hc)

/-- The line's heights rise with the multiple. -/
private theorem lineHt_mono (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (z : List BPair) (hz : z.length = t.rank) {a b : Nat}
    (hab : a ≤ b) :
    dotB F (rhoV t) (poly.pnorm (elim.vecAdd z (elim.vecScale
        (BPair.ofNat (a + 1)) (posCorootV t j))))
      ≤ dotB F (rhoV t) (poly.pnorm (elim.vecAdd z (elim.vecScale
        (BPair.ofNat (b + 1)) (posCorootV t j)))) :=
  ground.leB_congr
    (BPair.oneValue_symm (lineHt t F hshape j z hz a))
    (BPair.oneValue_symm (lineHt t F hshape j z hz b))
    (ground.leB_add (ground.leB_refl _)
      (ground.leB_scale_mono (Nat.succ_le_succ hab)
        (ground.leB_congr_left
          (BPair.oneValue_refl BPair.unit)
          (Or.inr (rootHt t F hshape hgsym hrd hj)))))

/-- The line's cap: a natural multiple whose key sits strictly
beyond `ρ`'s own height. -/
private theorem lineCap (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (z : List BPair) (hz : z.length = t.rank) :
    ∃ cap : Nat, dotB F (rhoV t) (rhoV t)
      < dotB F (rhoV t) (poly.pnorm (elim.vecAdd z
          (elim.vecScale (BPair.ofNat (cap + 1))
            (posCorootV t j)))) := by
  obtain ⟨n, hn⟩ := ground.leB_ofNat_bound
    (dotB F (rhoV t) (rhoV t) + (dotB F (rhoV t) z).swap)
  refine ⟨n, ?_⟩
  have hA := rootHt t F hshape hgsym hrd hj
  have hstep : BPair.ofNat n < BPair.ofNat (n + 1) :=
    BPair.lt_congr (BPair.unit_add (BPair.ofNat n))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.oneValue_symm (BPair.ofNat_succ n)))
      (ground.ltB_add (show BPair.unit < BPair.ofNat 1 from
        ground.unitLtOfNat 0) (ground.leB_refl (BPair.ofNat n)))
  have hmul : BPair.ofNat (n + 1)
      ≤ BPair.ofNat (n + 1) * dotB F (rhoV t) (posCorootV t j) :=
    ground.leB_congr_left (BPair.mul_ofNat_one (BPair.ofNat (n + 1)))
      (ground.leB_mulR (ground.unitLeOfNat (n + 1))
        (ground.oneLeOfUnitLt hA))
  have hlt : dotB F (rhoV t) (rhoV t) + (dotB F (rhoV t) z).swap
      < BPair.ofNat (n + 1) * dotB F (rhoV t) (posCorootV t j) :=
    ground.leB_ltB_trans hn (ground.ltB_trans_le hstep hmul)
  refine BPair.lt_congr ?_
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (BPair.oneValue_symm (lineHt t F hshape j z hz n)))
    (ground.ltB_add hlt (ground.leB_refl (dotB F (rhoV t) z)))
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.swap_add_null
        (BPair.oneValue_refl (dotB F (rhoV t) z)))) ?_
  exact BPair.add_unit _

/-! The signed folds' arithmetic: the grading passes through a fold,
through a guarded entry and through a scalar; a guarded constant's
fold collects at the guard's count; and the subset families' signed
fold at a stated key reads that key's own count pair against the
datum. -/

/-- The subset families' signed fold at a stated key: the key's own
count pair against the datum. -/
private theorem subsetSigned (t : gentable.Table) (k : List BPair)
    (X : BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (if eKey t S = k then X else BPair.unit))
      (sublistsOf (List.range t.posFolds.length))).oneValue
      (BPair.ofCounts (subsetCount t k false) (subsetCount t k true)
        * X) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun S =>
        (if (sideOf S = false ∧ eKey t S = k) then X else BPair.unit)
        + (if (sideOf S = true ∧ eKey t S = k) then X.swap
            else BPair.unit))
      (sublistsOf (List.range t.posFolds.length)) (fun S _ => ?_)) ?_
  · rw [ground.signedAt_if]
    by_cases hk : eKey t S = k
    · rw [if_pos hk]
      cases hs : sideOf S
      · rw [if_pos (And.intro rfl hk),
          if_neg (fun hc : (false = true ∧ eKey t S = k) =>
            Bool.noConfusion hc.1)]
        exact BPair.oneValue_symm (BPair.add_unit X)
      · rw [if_neg (fun hc : (true = false ∧ eKey t S = k) =>
            Bool.noConfusion hc.1),
          if_pos (And.intro rfl hk)]
        exact BPair.oneValue_symm (BPair.unit_add X.swap)
    · rw [if_neg hk,
        if_neg (fun hc : sideOf S = false ∧ eKey t S = k => hk hc.2),
        if_neg (fun hc : sideOf S = true ∧ eKey t S = k => hk hc.2)]
      exact BPair.oneValue_symm (BPair.add_unit _)
  refine BPair.oneValue_trans
    (ground.foldB_add _ _ (sublistsOf (List.range t.posFolds.length))) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (ground.foldB_guard (fun S => sideOf S = false ∧ eKey t S = k) X _)
      (ground.foldB_guard (fun S => sideOf S = true ∧ eKey t S = k) X.swap _)) ?_
  have hcf : ground.famFold Nat.add 0
      (fun S => if (sideOf S = false ∧ eKey t S = k) then 1 else 0)
      (sublistsOf (List.range t.posFolds.length))
      = subsetCount t k false := by
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun S => ?_) _
    by_cases hs : sideOf S = false
    · rw [if_pos hs]
      by_cases hk : eKey t S = k
      · rw [if_pos hk, if_pos (⟨hs, hk⟩ : sideOf S = false ∧ eKey t S = k)]
      · rw [if_neg hk, if_neg (fun hc : sideOf S = false ∧ eKey t S = k =>
          hk hc.2)]
    · rw [if_neg hs, if_neg (fun hc : sideOf S = false ∧ eKey t S = k =>
        hs hc.1)]
  have hct : ground.famFold Nat.add 0
      (fun S => if (sideOf S = true ∧ eKey t S = k) then 1 else 0)
      (sublistsOf (List.range t.posFolds.length))
      = subsetCount t k true := by
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun S => ?_) _
    by_cases hs : sideOf S = true
    · rw [if_pos hs]
      by_cases hk : eKey t S = k
      · rw [if_pos hk, if_pos (⟨hs, hk⟩ : sideOf S = true ∧ eKey t S = k)]
      · rw [if_neg hk, if_neg (fun hc : sideOf S = true ∧ eKey t S = k =>
          hk hc.2)]
    · rw [if_neg hs, if_neg (fun hc : sideOf S = true ∧ eKey t S = k =>
        hs hc.1)]
  rw [hcf, hct]
  refine BPair.oneValue_of_eq ?_
  show _ = (BPair.ofNat (subsetCount t k false)
    + (BPair.ofNat (subsetCount t k true)).swap) * X
  rw [BPair.right_distrib, BPair.swap_mul, BPair.mul_swap]

/-! The line's collection at the subset families: the signed fold of
the line test at a member collects the family folds' count pairs
along the line, the member's own dot the constant weight.  The count
of hits along a capped run is the line test itself — one multiple
where the test reads true, none where it reads false — the keys
parting at their rising heights and the hits bounded by `ρ`'s own. -/

/-- The line's hit count along a capped run reads the line test. -/
private theorem lineCount (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (y mu e : List BPair) (hy : y.length = t.rank)
    (hmu : mu.length = t.rank) (hmun : poly.pnorm mu = mu)
    (he : e.length = t.rank) (hen : poly.pnorm e = e)
    (hle : dotB F (rhoV t) e ≤ dotB F (rhoV t) (rhoV t)) (cap : Nat)
    (hcap : dotB F (rhoV t) (rhoV t)
      < dotB F (rhoV t) (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg mu)))
          (elim.vecScale (BPair.ofNat (cap + 1)) (posCorootV t j))))) :
    ground.famFold Nat.add 0
        (fun l => if e = poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd y (poly.neg mu)))
            (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j)))
          then 1 else 0) (List.range cap)
      = if lineAt t F (poly.pnorm (elim.vecAdd y (poly.neg e))) mu j
        then 1 else 0 := by
  have hnmu : (poly.neg mu).length = t.rank :=
    (ground.length_map BPair.swap mu).trans hmu
  have hne : (poly.neg e).length = t.rank :=
    (ground.length_map BPair.swap e).trans he
  have hz : (poly.pnorm (elim.vecAdd y (poly.neg mu))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd y _ t.rank hy hnmu)
  have hzE : (poly.pnorm (elim.vecAdd y (poly.neg e))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd y _ t.rank hy hne)
  have hd : ∀ l : Nat, (elim.vecScale (BPair.ofNat (l + 1))
      (posCorootV t j)).length = t.rank := fun _ =>
    (elim.length_vecScale _ _).trans (posCorootV_length t j)
  by_cases hline : lineAt t F
      (poly.pnorm (elim.vecAdd y (poly.neg e))) mu j = true
  · rw [if_pos hline]
    obtain ⟨l0, _, hhit⟩ := (lineAt_iff t F _ mu j).mp hline
    have hkey : e = poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd y (poly.neg mu)))
        (elim.vecScale (BPair.ofNat (l0 + 1)) (posCorootV t j))) :=
      ((lineKey_iff t.rank y e mu _ hy (hd l0) he hen hmu hmun).mp
        hhit).symm
    have hlt : l0 < cap := by
      match Nat.lt_or_ge l0 cap with
      | Or.inl h => exact h
      | Or.inr h =>
        refine absurd hcap (ground.leB_not_lt ?_)
        refine ground.leB_trans
          (lineHt_mono t F hshape hgsym hrd hj _ hz h) ?_
        exact ground.leB_congr_left
          (BPair.oneValue_of_eq (congrArg (dotB F (rhoV t)) hkey)) hle
    have hpt : ∀ l : Nat, (if e = poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd y (poly.neg mu)))
        (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j)))
          then 1 else 0) = (if l0 = l then 1 else 0) := by
      intro l
      by_cases hl : l0 = l
      · rw [if_pos hl, if_pos (show e = poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg mu)))
          (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))) by
            rw [← hl]; exact hkey)]
      · refine (if_neg ?_).trans (if_neg hl).symm
        intro he2
        exact hl (lineKey_inj t F hshape hgsym hrd hj _ hz
          (hkey.symm.trans he2))
    rw [ground.famFold_congr_all Nat.add 0 _ _ hpt (List.range cap),
      ← ground.countOf_fold, ground.countOf_range_one hlt]
  · rw [if_neg hline]
    refine Eq.trans (ground.famFold_congr_all Nat.add 0 _
      (fun _ => 0) (fun l => ?_) (List.range cap))
      (ground.famFold_zero (fun _ => 0) (fun _ => rfl) _)
    refine if_neg (fun he2 => hline ?_)
    refine lineAt_of_hit t F hshape hrd hj _ mu
      (Nat.le_of_eq hzE.symm) l ?_
    exact (lineKey_iff t.rank y e mu _ hy (hd l) he hen hmu hmun).mpr
      he2.symm

/-- The line's inner collection at the subset families. -/
private theorem innerFold (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (y mu : List BPair) (hy : y.length = t.rank)
    (hmu : mu.length = t.rank) (hmun : poly.pnorm mu = mu)
    (c : BPair) (cap : Nat)
    (hcap : dotB F (rhoV t) (rhoV t)
      < dotB F (rhoV t) (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg mu)))
          (elim.vecScale (BPair.ofNat (cap + 1)) (posCorootV t j))))) :
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (if lineAt t F (poly.pnorm (elim.vecAdd y
            (poly.neg (eKey t S)))) mu j then c else BPair.unit))
      (sublistsOf (List.range t.posFolds.length))).oneValue
      (c * ground.famFold BPair.add BPair.unit
        (fun l => BPair.ofCounts
          (subsetCount t (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd y (poly.neg mu)))
            (elim.vecScale (BPair.ofNat (l + 1))
              (posCorootV t j)))) false)
          (subsetCount t (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd y (poly.neg mu)))
            (elim.vecScale (BPair.ofNat (l + 1))
              (posCorootV t j)))) true))
        (List.range cap)) := by
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun S => ground.famFold BPair.add BPair.unit
        (fun l => ground.signedAt (sideOf S)
          (if eKey t S = poly.pnorm (elim.vecAdd
              (poly.pnorm (elim.vecAdd y (poly.neg mu)))
              (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j)))
            then c else BPair.unit)) (List.range cap))
      (sublistsOf (List.range t.posFolds.length)) (fun S hS => ?_)) ?_
  · have hSent : ∀ i, 0 < ground.countOf i S → i < t.posFolds.length :=
      fun i hi => ground.ltOfMem
        (ground.sublists_entries (List.range t.posFolds.length) S hS i hi)
    have hleS := assembly.hitLe t F hshape hgsym hrd (eKey t S) S hSent rfl
    refine BPair.oneValue_trans (ground.signedAt_congr (sideOf S)
      (BPair.oneValue_symm ?_))
      (BPair.oneValue_of_eq (ground.signedAt_fold (sideOf S) _ (List.range cap)))
    refine BPair.oneValue_trans
      (ground.foldB_guard (fun l => eKey t S = poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd y (poly.neg mu)))
        (elim.vecScale (BPair.ofNat (l + 1)) (posCorootV t j))))
        c (List.range cap)) ?_
    rw [lineCount t F hshape hgsym hrd hj y mu (eKey t S) hy hmu hmun
      (assembly.eKey_length t S) (assembly.eKey_norm t S) hleS cap hcap]
    by_cases hb : lineAt t F (poly.pnorm (elim.vecAdd y
        (poly.neg (eKey t S)))) mu j = true
    · rw [if_pos hb, if_pos hb]
      exact BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm _ _))
        (BPair.mul_ofNat_one c)
    · rw [if_neg hb, if_neg hb]
      exact BPair.unit_mul c
  · refine BPair.oneValue_trans
      (ground.foldB_swapL _ (sublistsOf (List.range t.posFolds.length))
        (List.range cap)) ?_
    refine BPair.oneValue_trans
      (ground.foldB_congr_members _
        (fun l => BPair.ofCounts
            (subsetCount t (poly.pnorm (elim.vecAdd
              (poly.pnorm (elim.vecAdd y (poly.neg mu)))
              (elim.vecScale (BPair.ofNat (l + 1))
                (posCorootV t j)))) false)
            (subsetCount t (poly.pnorm (elim.vecAdd
              (poly.pnorm (elim.vecAdd y (poly.neg mu)))
              (elim.vecScale (BPair.ofNat (l + 1))
                (posCorootV t j)))) true) * c)
        (List.range cap) (fun l _ => subsetSigned t _ c)) ?_
    rw [ground.famFold_congr_all BPair.add BPair.unit _
      (fun l => c * (BPair.ofCounts
        (subsetCount t (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg mu)))
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV t j)))) false)
        (subsetCount t (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg mu)))
          (elim.vecScale (BPair.ofNat (l + 1))
            (posCorootV t j)))) true)))
      (fun l => BPair.mul_comm _ _) (List.range cap)]
    exact ground.foldB_mul_left c _ (List.range cap)

/-- The line's collection at its moved key: the subset families'
signed fold of the line test at a member reads the withdrawn fold's
count pair at the stepped key, the member's own dot the weight. -/
private theorem innerMoved (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrd : rhoDotRead t F) {j : Nat} (hj : j < t.posFolds.length)
    (y mu : List BPair) (hy : y.length = t.rank)
    (hmu : mu.length = t.rank) (hmun : poly.pnorm mu = mu)
    (c : BPair) :
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (if lineAt t F (poly.pnorm (elim.vecAdd y
            (poly.neg (eKey t S)))) mu j then c else BPair.unit))
      (sublistsOf (List.range t.posFolds.length))).oneValue
      (c * BPair.ofCounts
        (subsetCountOff t j (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg mu)))
          (posCorootV t j))) false)
        (subsetCountOff t j (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg mu)))
          (posCorootV t j))) true)) := by
  have hz : (poly.pnorm (elim.vecAdd y (poly.neg mu))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd y _ t.rank hy
      ((ground.length_map BPair.swap mu).trans hmu))
  obtain ⟨cap, hcap⟩ := lineCap t F hshape hgsym hrd hj _ hz
  refine BPair.oneValue_trans
    (innerFold t F hshape hgsym hrd hj y mu hy hmu hmun c cap hcap) ?_
  exact BPair.mul_congr (BPair.oneValue_refl c)
    (BPair.oneValue_symm
      (subsetCountOff_line t F hshape hgsym hrd hj _ hz cap hcap))

/-- The alternant-weighted line folds at the subset families, the
single-weight form: the line's own folds collect against the key's
dot reads at the family's counts (`thm:memberchar`'s `(XX)` at the
subset side). -/
private theorem convDots_core (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (hrho : gentable.rhoRead t) (hrd : rhoDotRead t F)
    (L : List (List BPair)) (hmsh : mShapeRead t L)
    (y : List BPair) (hy : y.length = t.rank) :
    (ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (ground.famFold BPair.add BPair.unit (fun j =>
          ground.famFold BPair.add BPair.unit (fun mu =>
            if lineAt t F (poly.pnorm (elim.vecAdd y
                (poly.neg (eKey t S)))) mu j
              then dotB F mu (posCorootV t j) else BPair.unit) L)
          (List.range t.posFolds.length)))
      (sublistsOf (List.range t.posFolds.length))).oneValue
      (ground.famFold BPair.add BPair.unit
        (fun S => ground.signedAt (sideOf S)
          ((dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
              (eKey t S)
            + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
              (rhoV t)).swap)
            * BPair.ofNat (ground.countOf
                (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S)))) L)))
        (sublistsOf (List.range t.posFolds.length))) := by
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun S => ground.famFold BPair.add BPair.unit (fun j =>
      ground.famFold BPair.add BPair.unit (fun mu =>
        ground.signedAt (sideOf S)
          (if lineAt t F (poly.pnorm (elim.vecAdd y
              (poly.neg (eKey t S)))) mu j
            then dotB F mu (posCorootV t j) else BPair.unit)) L)
      (List.range t.posFolds.length))
    (sublistsOf (List.range t.posFolds.length)) (fun S _ => ?_)) ?_
  · rw [ground.signedAt_fold, ground.famFold_congr_all BPair.add BPair.unit _ _
      (fun j => ground.signedAt_fold (sideOf S) _ L)
      (List.range t.posFolds.length)]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (ground.foldB_swapL _
    (sublistsOf (List.range t.posFolds.length))
    (List.range t.posFolds.length)) ?_
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun j => ground.famFold BPair.add BPair.unit (fun mu =>
        dotB F mu (posCorootV t j) * BPair.ofCounts
          (subsetCountOff t j (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd y (poly.neg mu)))
            (posCorootV t j))) false)
          (subsetCountOff t j (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd y (poly.neg mu)))
            (posCorootV t j))) true)) L)
    (List.range t.posFolds.length) (fun j hj => ?_)) ?_
  · refine BPair.oneValue_trans (ground.foldB_swapL _
      (sublistsOf (List.range t.posFolds.length)) L) ?_
    refine ground.foldB_congr_members _ _ L (fun mu hmuL => ?_)
    obtain ⟨hmu, hmun⟩ := hmsh mu (ground.mem_of_countOf_pos mu L hmuL)
    exact innerMoved t F hshape hgsym hrd (ground.ltOfMem hj) y mu hy
      hmu hmun _
  refine BPair.oneValue_trans (ground.foldB_swapL _
    (List.range t.posFolds.length) L) ?_
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun mu => (dotB F mu (poly.pnorm (elim.vecAdd y (poly.neg mu)))
        + (dotB F mu (rhoV t)).swap)
      * BPair.ofCounts
          (subsetCount t (poly.pnorm (elim.vecAdd y (poly.neg mu))) false)
          (subsetCount t (poly.pnorm (elim.vecAdd y (poly.neg mu))) true))
    L (fun mu hmuL => ?_)) ?_
  · obtain ⟨hmu, hmun⟩ := hmsh mu (ground.mem_of_countOf_pos mu L hmuL)
    exact subsetCountOff_euler_moved t F hshape hgsym hrho mu _ hmu
      ((poly.pnorm_length _).trans (elim.length_vecAdd y _ t.rank hy
        ((ground.length_map BPair.swap mu).trans hmu)))
      (poly.pnorm_pnorm _)
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun mu => ground.famFold BPair.add BPair.unit
      (fun S => ground.signedAt (sideOf S)
        (if eKey t S = poly.pnorm (elim.vecAdd y (poly.neg mu))
          then (dotB F mu (poly.pnorm (elim.vecAdd y (poly.neg mu)))
            + (dotB F mu (rhoV t)).swap) else BPair.unit))
      (sublistsOf (List.range t.posFolds.length)))
    L (fun mu _ => ?_)) ?_
  · exact BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.oneValue_symm (subsetSigned t _ _))
  refine BPair.oneValue_trans (ground.foldB_swapL _ L
    (sublistsOf (List.range t.posFolds.length))) ?_
  refine ground.foldB_congr_members _ _
    (sublistsOf (List.range t.posFolds.length)) (fun S _ => ?_)
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (ground.signedAt_fold (sideOf S) _ L).symm) ?_
  refine ground.signedAt_congr (sideOf S) ?_
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun mu => if mu = poly.pnorm (elim.vecAdd y
        (poly.neg (eKey t S)))
      then (dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
          (eKey t S)
        + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
          (rhoV t)).swap) else BPair.unit) L (fun mu hmuL => ?_)) ?_
  · obtain ⟨hmu, hmun⟩ := hmsh mu (ground.mem_of_countOf_pos mu L hmuL)
    have hcorr := offKey_iff t.rank y mu (eKey t S) hy hmu hmun
      (assembly.eKey_length t S) (assembly.eKey_norm t S)
    by_cases hg : eKey t S = poly.pnorm (elim.vecAdd y (poly.neg mu))
    · have hmS : mu = poly.pnorm (elim.vecAdd y
          (poly.neg (eKey t S))) := (hcorr.mp hg.symm).symm
      rw [if_pos hg, if_pos hmS, ← hg, hmS]
      exact BPair.oneValue_refl _
    · rw [if_neg hg, if_neg (fun hc : mu = poly.pnorm (elim.vecAdd y
        (poly.neg (eKey t S))) => hg (hcorr.mpr hc.symm).symm)]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (ground.foldB_indicator _ _ L) ?_
  exact BPair.oneValue_of_eq (BPair.mul_comm _ _)

/-- The recursion's whole correction at a key doubles its
single-weight fold: each line hit enters at the member's dot twice. -/
private theorem gSum_double (t : gentable.Table) (F : FundData)
    (L : List (List BPair)) (nu : List BPair) :
    (gSum t F L nu).oneValue
      (ground.famFold BPair.add BPair.unit (fun j =>
          ground.famFold BPair.add BPair.unit (fun mu =>
            if lineAt t F nu mu j then dotB F mu (posCorootV t j)
            else BPair.unit) L) (List.range t.posFolds.length)
        + ground.famFold BPair.add BPair.unit (fun j =>
          ground.famFold BPair.add BPair.unit (fun mu =>
            if lineAt t F nu mu j then dotB F mu (posCorootV t j)
            else BPair.unit) L) (List.range t.posFolds.length)) := by
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun j => ground.famFold BPair.add BPair.unit (fun mu =>
        if lineAt t F nu mu j then dotB F mu (posCorootV t j)
        else BPair.unit) L
      + ground.famFold BPair.add BPair.unit (fun mu =>
        if lineAt t F nu mu j then dotB F mu (posCorootV t j)
        else BPair.unit) L)
    (List.range t.posFolds.length) (fun j _ => ?_))
    (ground.foldB_add _ _ (List.range t.posFolds.length))
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun mu => (if lineAt t F nu mu j then dotB F mu (posCorootV t j)
        else BPair.unit)
      + (if lineAt t F nu mu j then dotB F mu (posCorootV t j)
        else BPair.unit)) L (fun mu _ => ?_))
    (ground.foldB_add _ _ L)
  by_cases hb : lineAt t F nu mu j = true
  · rw [if_pos hb, if_pos hb]
    exact BPair.oneValue_refl _
  · rw [if_neg hb, if_neg hb]
    exact BPair.oneValue_symm (BPair.add_unit _)

/-- `thm:memberchar`'s `(XX)`: the alternant-weighted line folds
collect at the key's own dot reads — the recursion's whole correction
summed over the Weyl fold reads the moved key's dot against the fold
key joined to `ρ`'s own, at the multiplicity family's count.  The
root fold's coroot read takes no binder: it is `rhoRead_derived`'s
own consequence of the shape, the simple positions, the permutation
datum and the `ρ`-dots; the family's shape read and the key's
order are the correspondence's frame — an off-shape member or an
off-rank key enters neither side, the line hits and the count hits
each demanding the normed rank-length spelling. -/
theorem convDots (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (htop : wTopRead t W)
    (hmsh : mShapeRead t L)
    (y : List BPair) (hy : y.length = t.rank) :
    (ground.famFold BPair.add BPair.unit (fun vp =>
      ground.signedAt vp.2
        (gSum t F L (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))))
      W).oneValue
      (ground.famFold BPair.add BPair.unit (fun vp =>
        ground.signedAt vp.2
          (((dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1
                + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                  (rhoV t)).swap)
              + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1
                + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                  (rhoV t)).swap))
            * BPair.ofNat (ground.countOf
                (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L))) W) := by
  have hrho := assembly.rhoRead_derived t F hshape hsp hpsq hpi hrd
  refine BPair.oneValue_trans
    (wFold_subsets t F W wits hshape hgram hgsym hsp hsq hpsq hpi hrd
      hwsh hclose hdom htop
      (fun k => gSum t F L (poly.pnorm (elim.vecAdd y (poly.neg k)))))
    (BPair.oneValue_trans ?_
      (BPair.oneValue_symm (wFold_subsets t F W wits hshape hgram hgsym
        hsp hsq hpsq hpi hrd hwsh hclose hdom htop
        (fun k => ((dotB F (poly.pnorm (elim.vecAdd y (poly.neg k))) k
              + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg k)))
                (rhoV t)).swap)
            + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg k))) k
              + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg k)))
                (rhoV t)).swap))
          * BPair.ofNat (ground.countOf
              (poly.pnorm (elim.vecAdd y (poly.neg k))) L)))))
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun S => ground.signedAt (sideOf S)
        (ground.famFold BPair.add BPair.unit (fun j =>
          ground.famFold BPair.add BPair.unit (fun mu =>
            if lineAt t F (poly.pnorm (elim.vecAdd y
                (poly.neg (eKey t S)))) mu j
              then dotB F mu (posCorootV t j) else BPair.unit) L)
          (List.range t.posFolds.length))
      + ground.signedAt (sideOf S)
        (ground.famFold BPair.add BPair.unit (fun j =>
          ground.famFold BPair.add BPair.unit (fun mu =>
            if lineAt t F (poly.pnorm (elim.vecAdd y
                (poly.neg (eKey t S)))) mu j
              then dotB F mu (posCorootV t j) else BPair.unit) L)
          (List.range t.posFolds.length)))
    (sublistsOf (List.range t.posFolds.length)) (fun S _ => ?_)) ?_
  · exact BPair.oneValue_trans
      (ground.signedAt_congr (sideOf S) (gSum_double t F L _))
      (BPair.oneValue_of_eq (ground.signedAt_add (sideOf S) _ _))
  refine BPair.oneValue_trans (ground.foldB_add _ _
    (sublistsOf (List.range t.posFolds.length))) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (convDots_core t F hshape hgsym hrho hrd L hmsh y hy)
    (convDots_core t F hshape hgsym hrho hrd L hmsh y hy)) ?_
  refine BPair.oneValue_symm (BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun S => ground.signedAt (sideOf S)
          ((dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
              (eKey t S)
            + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
              (rhoV t)).swap)
            * BPair.ofNat (ground.countOf
                (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S)))) L))
        + ground.signedAt (sideOf S)
          ((dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
              (eKey t S)
            + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S))))
              (rhoV t)).swap)
            * BPair.ofNat (ground.countOf
                (poly.pnorm (elim.vecAdd y (poly.neg (eKey t S)))) L)))
      (sublistsOf (List.range t.posFolds.length)) (fun S _ => ?_))
    (ground.foldB_add _ _ (sublistsOf (List.range t.posFolds.length))))
  exact BPair.oneValue_trans
    (ground.signedAt_congr (sideOf S)
      (BPair.oneValue_of_eq (BPair.right_distrib _ _ _)))
    (BPair.oneValue_of_eq (ground.signedAt_add (sideOf S) _ _))

/-! The window's own shape: every window key is normed and sits at
the rank's order — bounded above by the shifted key's own order and
below by the window's coordinate test, a key short of the rank
reading the sum's unit at its own order. -/

/-- The dominant window's keys are normed and sit at the rank's
order. -/
private theorem domWindow_shape (t : gentable.Table) (F : FundData)
    (lamV : List BPair) (y : List BPair)
    (hwin : y ∈ domWindow t F lamV) :
    y.length = t.rank ∧ poly.pnorm y = y := by
  have hBIG : ∀ x ∈ (wBox ((List.range t.rank).map (simDotAt t F))
        (BPair.capN (dotB F lamV (rhoV t)))).map (fun c =>
      poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        (poly.neg (cartanFold t c)))),
      x.length ≤ t.rank ∧ poly.pnorm x = x :=
    ground.all_of_map _ _ (fun c => by
      refine ⟨?_, poly.pnorm_pnorm _⟩
      rw [poly.pnorm_length]
      refine Nat.le_trans (assembly.vecAdd_lenL _
        (poly.neg (cartanFold t c))) ?_
      rw [poly.pnorm_length]
      refine Nat.le_trans (assembly.vecAdd_lenR lamV (rhoV t)) ?_
      exact Nat.le_of_eq
        (ground.length_replicate (BPair.ofNat 1) t.rank)) _
  obtain ⟨⟨hle, hn⟩, hq⟩ := ground.all_of_filter _ _ _ hBIG y hwin
  refine ⟨Nat.le_antisymm hle ?_, hn⟩
  have hq' : ∀ k, k < t.rank →
      BPair.unit < ground.getAt BPair.unit y k := of_decide_eq_true hq
  match Nat.lt_or_ge y.length t.rank with
  | Or.inr h => exact h
  | Or.inl h =>
    refine absurd (hq' y.length h) ?_
    rw [ground.getAt_over BPair.unit y y.length (Nat.le_refl _)]
    exact (by decide +kernel)

/-! The eigen tier's arithmetic: the move's own sum read, the
pairing's bilinear square split, the recursion's collapse against a
gap factor, and the eigen split's two algebraic steps. -/

/-- The square of a joined key: the summands' squares against their
doubled cross pairing (`thm:memberchar`'s bilinear split, the form
kit's read). -/
theorem dotB_sq_split (t : gentable.Table) (F : FundData)
    (hshape : fundShape t F) (hgsym : gramSymRead F)
    (u v : List BPair) (hu : u.length = t.rank)
    (hv : v.length = t.rank) :
    (dotB F (poly.pnorm (elim.vecAdd u v))
        (poly.pnorm (elim.vecAdd u v))).oneValue
      (dotB F u u + (dotB F u v + dotB F u v) + dotB F v v) := by
  have huv : (elim.vecAdd u v).length = t.rank :=
    elim.length_vecAdd u v t.rank hu hv
  refine BPair.oneValue_trans
    (dotB_congrL F _ _ _ (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans
    (dotB_congrR F _ _ _ (poly.pnorm_oneValue _)) ?_
  refine BPair.oneValue_trans (dotB_addR t F hshape _ u v huv hu hv) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (dotB_addL t F hshape u v u hu hv)
    (dotB_addL t F hshape u v v hu hv)) ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr (BPair.oneValue_refl _)
      (assembly.dotB_swap t F hshape hgsym v u hv hu))
    (BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_of_eq ?_
  rw [BPair.add_assoc,
    ← BPair.add_assoc (dotB F u v) (dotB F u v) (dotB F v v),
    ← BPair.add_assoc]

/-- The recursion's collapse: a gap factor against the display's two
sides leaves the correction alone. -/
private theorem recCollapse {Q P G n : BPair}
    (h : (Q * n).oneValue (P * n + G)) :
    ((Q + P.swap) * n).oneValue G := by
  rw [BPair.right_distrib, BPair.swap_mul]
  refine BPair.oneValue_trans
    (BPair.add_congr h (BPair.oneValue_refl _)) ?_
  rw [BPair.add_assoc, BPair.add_comm G ((P * n).swap),
    ← BPair.add_assoc]
  refine BPair.oneValue_trans (BPair.add_congr
    (ground.unitOfOne (BPair.oneValue_refl (P * n)))
    (BPair.oneValue_refl G)) ?_
  exact BPair.unit_add G

/-- The eigen split's move: a gap against one square reads the gap
against another joined to the two squares' own gap. -/
private theorem eigenSplit_alg {Q p q D : BPair}
    (h : (p + D).oneValue q) :
    (Q + p.swap).oneValue ((Q + q.swap) + D) := by
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr (BPair.oneValue_refl Q)
      (ground.swap_congr (BPair.oneValue_symm h)))
    (BPair.oneValue_refl D)) ?_
  rw [← BPair.swap_add p D, BPair.add_assoc, BPair.add_assoc]
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl Q)
    (BPair.add_congr (BPair.oneValue_refl p.swap)
      (BPair.swap_add_null (BPair.oneValue_refl D)))) ?_
  exact BPair.add_congr (BPair.oneValue_refl Q) (BPair.add_unit p.swap)

/-- The eigen split's arithmetic: the joined key's square less the
cross gap and the two end squares reads the shifted key's own. -/
private theorem eigenBil_alg (A B C Rm R : BPair) :
    ((A + (B + B) + C)
      + ((((B + Rm.swap) + (B + Rm.swap)).swap)
        + (R + C.swap))).oneValue (A + (Rm + Rm) + R) := by
  rw [BPair.add_add_comm B Rm.swap B Rm.swap, BPair.swap_add Rm Rm,
    ← BPair.swap_add (B + B) ((Rm + Rm).swap),
    BPair.swap_swap (Rm + Rm),
    BPair.add_comm ((B + B).swap) (Rm + Rm),
    BPair.add_add_comm (A + (B + B)) C
      ((Rm + Rm) + (B + B).swap) (R + C.swap),
    BPair.add_add_comm A (B + B) (Rm + Rm) ((B + B).swap),
    BPair.add_comm R C.swap, ← BPair.add_assoc C C.swap R]
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.add_congr (BPair.oneValue_refl (A + (Rm + Rm)))
      (ground.unitOfOne (BPair.oneValue_refl (B + B))))
    (BPair.add_congr (ground.unitOfOne (BPair.oneValue_refl C))
      (BPair.oneValue_refl R))) ?_
  exact BPair.add_congr (BPair.add_unit (A + (Rm + Rm)))
    (BPair.unit_add R)

/-- The convolution's count pair as the Weyl fold's signed fold of
the family's counts at the moved keys. -/
private theorem convCount_fold (t : gentable.Table)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hwsh : wShapeRead t W) (hmsh : mShapeRead t L)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) :
    (BPair.ofCounts (convCount W L y false)
        (convCount W L y true)).oneValue
      (ground.famFold BPair.add BPair.unit (fun vp =>
        ground.signedAt vp.2 (BPair.ofNat (ground.countOf
          (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L))) W) := by
  refine BPair.oneValue_trans (ground.foldB_ofCounts _ _ W) ?_
  refine ground.foldB_congr_members _ _ W (fun vp hvp => ?_)
  obtain ⟨hk, hkn⟩ := hwsh vp (ground.mem_of_countOf_pos vp W hvp)
  have hinner : ground.famFold Nat.add 0
      (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0) L
      = ground.countOf (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L := by
    rw [ground.countOf_fold]
    refine ground.famFold_congr_members Nat.add 0 _ _ L (fun nu hnu => ?_)
    obtain ⟨hv, hvn⟩ := hmsh nu (ground.mem_of_countOf_pos nu L hnu)
    have hiff := addKey_iff t.rank y vp.1 nu hy hyn hk hv hvn
    by_cases hc : poly.pnorm (elim.vecAdd vp.1 nu) = y
    · rw [if_pos hc, if_pos (hiff.mp hc)]
    · rw [if_neg hc, if_neg (fun he => hc (hiff.mpr he))]
  rw [hinner]
  cases hb : vp.2
  · exact BPair.add_unit _
  · exact BPair.unit_add _

/-- `thm:memberchar`'s `(E)`: at a dominant-window key the eigen gap
against the convolution's count pair reads the sum's unit — the
recursion's display per member, the line folds' collection `(XX)`,
and the unbalanced keys' dot square closing the residual. -/
theorem eigenAt (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (lamV : List BPair)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hform : reflFormRead t F) (hwsh : wShapeRead t W)
    (hclose : wCloseRead t W) (hdom : wDomRead t W wits)
    (htop : wTopRead t W) (hmsh : mShapeRead t L)
    (hrec : recRead t F W L lamV)
    (y : List BPair) (hwin : y ∈ domWindow t F lamV) :
    ((dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
          (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        + (dotB F y y).swap)
      * BPair.ofCounts (convCount W L y false)
          (convCount W L y true)).oneValue BPair.unit := by
  obtain ⟨hy, hyn⟩ := domWindow_shape t F lamV y hwin
  have hrr := assembly.rhoRead_derived t F hshape hsp hpsq hpi hrd
  have hrhoLen : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
    (convCount_fold t W L hwsh hmsh y hy hyn)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (ground.foldB_mul_left _ _ W)) ?_
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun vp => ground.signedAt vp.2
      (gSum t F L (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
        + ((((dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1
                  + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                    (rhoV t)).swap)
                + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                    vp.1
                  + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                    (rhoV t)).swap))
              * BPair.ofNat (ground.countOf
                  (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L)).swap
          + (dotB F (rhoV t) (rhoV t) + (dotB F vp.1 vp.1).swap)
              * BPair.ofNat (ground.countOf
                  (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L))))
    W (fun vp hvp => ?_)) ?_
  · have hvpW := ground.mem_of_countOf_pos vp W hvp
    obtain ⟨hk, hkn⟩ := hwsh vp hvpW
    have hm : (poly.pnorm (elim.vecAdd y (poly.neg vp.1))).length
        = t.rank :=
      (poly.pnorm_length _).trans (elim.length_vecAdd y _ t.rank hy
        ((ground.length_map BPair.swap vp.1).trans hk))
    have hyk : poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1) = y :=
      (addKey_iff t.rank y (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
        vp.1 hy hyn hm hk hkn).mpr
        (offKey_swap t.rank y vp.1 _ hy hk hkn rfl)
    have hsq1 := dotB_sq_split t F hshape hgsym
      (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1 hm hk
    rw [hyk] at hsq1
    have hsq2 := dotB_sq_split t F hshape hgsym
      (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) (rhoV t) hm hrhoLen
    have hbil := BPair.oneValue_trans
      (BPair.add_congr hsq1 (BPair.oneValue_refl _))
      (BPair.oneValue_trans
        (eigenBil_alg (dotB F (poly.pnorm (elim.vecAdd y
            (poly.neg vp.1))) (poly.pnorm (elim.vecAdd y
            (poly.neg vp.1))))
          (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1)
          (dotB F vp.1 vp.1)
          (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) (rhoV t))
          (dotB F (rhoV t) (rhoV t)))
        (BPair.oneValue_symm hsq2))
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (ground.signedAt_mul vp.2 _ _).symm) ?_
    refine ground.signedAt_congr vp.2 ?_
    refine BPair.oneValue_trans
      (BPair.mul_congr_left (eigenSplit_alg hbil)) ?_
    rw [BPair.right_distrib]
    refine BPair.add_congr (recCollapse (hrec y hwin vp hvpW)) ?_
    rw [BPair.right_distrib, BPair.swap_mul]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (ground.foldB_congr_members _
    (fun vp => ground.signedAt vp.2
        (gSum t F L (poly.pnorm (elim.vecAdd y (poly.neg vp.1))))
      + ((ground.signedAt vp.2
          (((dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1
                + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                  (rhoV t)).swap)
              + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) vp.1
                + (dotB F (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                  (rhoV t)).swap))
            * BPair.ofNat (ground.countOf
                (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L))).swap
        + ground.signedAt vp.2
          ((dotB F (rhoV t) (rhoV t) + (dotB F vp.1 vp.1).swap)
            * BPair.ofNat (ground.countOf
                (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L))))
    W (fun vp _ => BPair.oneValue_of_eq (by
      rw [ground.signedAt_add, ground.signedAt_add, ground.signedAt_swap]))) ?_
  refine BPair.oneValue_trans (ground.foldB_add _ _ W) ?_
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (ground.foldB_add _ _ W)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  refine BPair.oneValue_trans (BPair.add_congr ?_ ?_)
    (BPair.add_unit BPair.unit)
  · rw [ground.fold_swap]
    exact ground.unitOfOne (convDots t F W wits L hshape hgram hgsym
      hsp hsq hpsq hpi hrd hwsh hclose hdom htop hmsh y hy)
  · refine ground.signedFold_null (fun k =>
      (dotB F (rhoV t) (rhoV t) + (dotB F k k).swap)
        * BPair.ofNat (ground.countOf
            (poly.pnorm (elim.vecAdd y (poly.neg k))) L))
      W.length W (Nat.le_refl _) (fun k hkocc => ?_)
    by_cases hb : ground.countOf (k, true) W = ground.countOf (k, false) W
    · exact Or.inl hb
    · refine Or.inr ?_
      have hmem : ∃ s : Bool, (k, s) ∈ W := by
        match Nat.eq_zero_or_pos (ground.countOf (k, true) W) with
        | Or.inr h => exact ⟨true, ground.mem_of_countOf_pos _ W h⟩
        | Or.inl h0 =>
          refine ⟨false, ground.mem_of_countOf_pos _ W ?_⟩
          rw [h0, Nat.zero_add] at hkocc
          exact hkocc
      obtain ⟨s, hs⟩ := hmem
      have hdot := assembly.wOff_dotSq t F W wits hshape hgram hgsym
        hsp hsq hrd hrr hform hwsh hclose hdom k s hs hb
      refine BPair.oneValue_trans (BPair.mul_congr_left ?_)
        (BPair.unit_mul _)
      exact BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (ground.swap_congr hdot))
        (ground.unitOfOne (BPair.oneValue_refl _))

/-! `thm:memberchar`'s determination sentence: a reflection-graded
family at the four reads balances the shifted alternant's data key
by key.  The family is abstract — its reads are the reflection
transport of its counts, the support at a natural simple fold back
to the shifted key, the one-and-none pins at that key, and the
regular read off it — and the alternant's data are the concrete
graded list at its own four.  The proof is `thm:assembly`'s
dominance walk read at the shifted key: at a lower-side simple pair
the reflection raises the key's `ρ`-dot by at least one and flips
both sides, so the fuel counted off the gap runs the key to a
dominant image, where the fixed keys pair each side against its
flip, the shifted key reads one and none on both data, and the
regular read closes the rest. -/


/-! The convolution's own reads: the inner fold at a graded member
is the family's count at the member's moved key, an occupied count
names both positions, and the reflection carries the whole count to
the flipped side — the letter's conditioned moves on the graded
list and on the family the count-preserving involutions, and the
key identity the reflection's own additivity across the join. -/

/-- The convolution's inner fold at a graded member: the family's
count at the member's own moved key. -/
private theorem convInner (t : gentable.Table) (L : List (List BPair))
    (hmsh : mShapeRead t L) (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) (k : List BPair)
    (hk : k.length = t.rank) :
    ground.famFold Nat.add 0
        (fun nu => if poly.pnorm (elim.vecAdd k nu) = y then 1 else 0) L
      = ground.countOf (poly.pnorm (elim.vecAdd y (poly.neg k))) L := by
  rw [ground.countOf_fold]
  refine ground.famFold_congr_members Nat.add 0 _ _ L (fun nu hnu => ?_)
  obtain ⟨hv, hvn⟩ := hmsh nu (ground.mem_of_countOf_pos nu L hnu)
  have hiff := addKey_iff t.rank y k nu hy hyn hk hv hvn
  by_cases hc : poly.pnorm (elim.vecAdd k nu) = y
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg (fun he => hc (hiff.mpr he))]

/-- The convolution's count at a normed key of the rank's order:
the graded fold of the family's counts at the moved keys. -/
theorem convCount_countOf (t : gentable.Table)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hwsh : wShapeRead t W) (hmsh : mShapeRead t L)
    (z : List BPair) (hz : z.length = t.rank) (hzn : poly.pnorm z = z)
    (s : Bool) :
    convCount W L z s = ground.famFold Nat.add 0
      (fun vp => if vp.2 = s then ground.countOf
        (poly.pnorm (elim.vecAdd z (poly.neg vp.1))) L else 0) W := by
  show ground.famFold Nat.add 0
    (fun vp => if vp.2 = s then
      ground.famFold Nat.add 0
        (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu) = z then 1 else 0) L
      else 0) W = _
  refine ground.famFold_congr_members Nat.add 0 _ _ W (fun vp hvp => ?_)
  obtain ⟨hk, hkn⟩ := hwsh vp (ground.mem_of_countOf_pos vp W hvp)
  by_cases hb : vp.2 = s
  · rw [if_pos hb, if_pos hb, convInner t L hmsh z hz hzn vp.1 hk]
  · rw [if_neg hb, if_neg hb]


/-- The convolution folded over the multiplicity family: the graded
count collects per family member at the withdrawn key's own count in
the image list, the two folds exchanged and the withdrawal its own
inverse (`thm:memberchar`'s graded product read family-first). -/
theorem convCount_wFold (t : gentable.Table)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hwsh : wShapeRead t W) (hmsh : mShapeRead t L)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) (s : Bool) :
    convCount W L y s
      = ground.famFold Nat.add 0
          (fun nu => ground.countOf
            (poly.pnorm (elim.vecAdd y (poly.neg nu)), s) W) L := by
  rw [convCount_countOf t W L hwsh hmsh y hy hyn s,
    ground.famFold_congr_all Nat.add 0
      (fun vp : List BPair × Bool => if vp.2 = s then ground.countOf
        (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L else 0)
      (fun vp : List BPair × Bool => if vp.2 = s then
        ground.famFold Nat.add 0 (fun nu =>
          if poly.pnorm (elim.vecAdd y (poly.neg vp.1)) = nu then 1
          else 0) L
        else 0)
      (fun vp => by rw [ground.countOf_fold]) W,
    ground.famFold_guard_swap
      (fun vp : List BPair × Bool => vp.2 = s)
      (fun vp nu => if poly.pnorm (elim.vecAdd y (poly.neg vp.1)) = nu
        then 1 else 0) W L]
  refine ground.famFold_congr_members Nat.add 0 _ _ L (fun nu hnu => ?_)
  obtain ⟨hnul, hnun⟩ := hmsh nu (ground.mem_of_countOf_pos nu L hnu)
  rw [ground.countOf_fold]
  refine ground.famFold_congr_members Nat.add 0 _ _ W (fun vp hvp => ?_)
  obtain ⟨hk, hkn⟩ := hwsh vp (ground.mem_of_countOf_pos vp W hvp)
  by_cases hb : vp.2 = s
  · rw [if_pos hb]
    by_cases hc : poly.pnorm (elim.vecAdd y (poly.neg vp.1)) = nu
    · have hswap := assembly.offKey_swap t.rank y vp.1 nu hy hk hkn hc
      rw [if_pos hc, if_pos (show
        (poly.pnorm (elim.vecAdd y (poly.neg nu)), s) = vp by
        rw [hswap, ← hb])]
    · refine Eq.trans (if_neg hc) (Eq.symm (if_neg (fun he => hc ?_)))
      have h1 : poly.pnorm (elim.vecAdd y (poly.neg nu)) = vp.1 :=
        congrArg Prod.fst he
      exact assembly.offKey_swap t.rank y nu vp.1 hy hnul hnun h1
  · refine Eq.trans (if_neg hb) (Eq.symm (if_neg (fun he => hb ?_)))
    exact (congrArg Prod.snd he).symm

/-- The convolution's occupied count names both positions: a graded
member at the read's side and a family member whose join reads the
key, each at a position of its own list. -/
private theorem conv_witness (W : List (List BPair × Bool))
    (L : List (List BPair)) (y : List BPair) (s : Bool)
    (h : 0 < convCount W L y s) :
    ∃ (vp : List BPair × Bool) (k : Nat), vp ∈ W ∧ k < W.length
      ∧ ground.getAt ([], false) W k = vp ∧ vp.2 = s
      ∧ ∃ (nu : List BPair) (m : Nat), nu ∈ L ∧ m < L.length
        ∧ ground.getAt [] L m = nu
        ∧ poly.pnorm (elim.vecAdd vp.1 nu) = y := by
  obtain ⟨vp, hvp, hgv⟩ := ground.famFold_pos_witness
    (fun vp : List BPair × Bool => if vp.2 = s then
      ground.famFold Nat.add 0
        (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0) L
      else 0) W h
  have hvpW : vp ∈ W := ground.mem_of_countOf_pos vp W hvp
  obtain ⟨k, hk, hke⟩ := ground.getAt_of_mem (([], false)) hvpW
  have hg' : 0 < (if vp.2 = s then ground.famFold Nat.add 0
      (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0) L
    else 0) := hgv
  by_cases hs : vp.2 = s
  · rw [if_pos hs] at hg'
    obtain ⟨nu, hnu, hgn⟩ := ground.famFold_pos_witness
      (fun nu => if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0)
      L hg'
    have hnuL : nu ∈ L := ground.mem_of_countOf_pos nu L hnu
    obtain ⟨m, hm, hme⟩ := ground.getAt_of_mem ([] : List BPair) hnuL
    have hgn' : 0 < (if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0) :=
      hgn
    refine ⟨vp, k, hvpW, hk, hke, hs, nu, m, hnuL, hm, hme, ?_⟩
    by_cases hc : poly.pnorm (elim.vecAdd vp.1 nu) = y
    · exact hc
    · rw [if_neg hc] at hgn'
      exact absurd hgn' (Nat.lt_irrefl 0)
  · rw [if_neg hs] at hg'
    exact absurd hg' (Nat.lt_irrefl 0)

/-- The reflection's additivity across a join: the letter's image of
a joined key is its images joined. -/
private theorem reflAt_vecAdd (t : gentable.Table) (i : Nat)
    (u v : List BPair) (hu : u.length = t.rank)
    (hv : v.length = t.rank) :
    reflAt t i (poly.pnorm (elim.vecAdd u v))
      = poly.pnorm (elim.vecAdd (reflAt t i u) (reflAt t i v)) := by
  have hMu : (elim.matVec (reflM t i) u).length = t.rank :=
    (elim.matVec_length (reflM t i) u).trans (assembly.reflM_length t i)
  have hMv : (elim.matVec (reflM t i) v).length = t.rank :=
    (elim.matVec_length (reflM t i) v).trans (assembly.reflM_length t i)
  rw [assembly.reflAt_pnorm t i (elim.vecAdd u v)]
  show poly.pnorm (elim.matVec (reflM t i) (elim.vecAdd u v))
    = poly.pnorm (elim.vecAdd (poly.pnorm (elim.matVec (reflM t i) u))
      (poly.pnorm (elim.matVec (reflM t i) v)))
  rw [elim.pnorm_vecAdd_left (elim.matVec (reflM t i) u)
      (poly.pnorm (elim.matVec (reflM t i) v))
      (hMu.trans ((poly.pnorm_length _).trans hMv).symm),
    elim.vecAdd_comm (elim.matVec (reflM t i) u)
      (poly.pnorm (elim.matVec (reflM t i) v)),
    elim.pnorm_vecAdd_left (elim.matVec (reflM t i) v)
      (elim.matVec (reflM t i) u) (hMv.trans hMu.symm),
    elim.vecAdd_comm (elim.matVec (reflM t i) v)
      (elim.matVec (reflM t i) u)]
  refine poly.pnorm_congr _ _ ?_
    (elim.matVec_vecAdd (reflM t i) t.rank (assembly.reflM_rows t i)
      u v hu hv)
  rw [elim.matVec_length, assembly.reflM_length,
    elim.length_vecAdd _ _ t.rank hMu hMv]

/-- The family key's conditioned move at a reflection: the key
reflected where it sits at the rank's order at its own
representative, the key kept where it does not. -/
private def reflCond (t : gentable.Table) (i : Nat) (v : List BPair) :
    List BPair :=
  if v.length = t.rank ∧ poly.pnorm v = v then reflAt t i v else v

private theorem reflCond_pos (t : gentable.Table) (i : Nat)
    (v : List BPair) (hg : v.length = t.rank ∧ poly.pnorm v = v) :
    reflCond t i v = reflAt t i v := by
  show (if v.length = t.rank ∧ poly.pnorm v = v then reflAt t i v
    else v) = _
  exact if_pos hg

private theorem reflCond_invol (t : gentable.Table) (i : Nat)
    (hsq : elim.matOneValue (elim.matMul (reflM t i) (reflM t i))
      (inertia.idMat t.rank)) (v : List BPair) :
    reflCond t i (reflCond t i v) = v := by
  by_cases hg : v.length = t.rank ∧ poly.pnorm v = v
  · rw [reflCond_pos t i v hg, reflCond_pos t i (reflAt t i v)
      ⟨assembly.reflAt_length t i v, assembly.reflAt_norm t i v⟩,
      assembly.reflAt_invol' t i hsq v hg.1, hg.2]
  · have e : reflCond t i v = v := by
      show (if v.length = t.rank ∧ poly.pnorm v = v then reflAt t i v
        else v) = _
      exact if_neg hg
    rw [e, e]

/-- The family's counts transport at a reflection: the invariance
read at the members is the conditioned move's count identity, so the
count reads across at every key of the rank's order sitting at its
representative. -/
private theorem reflCond_count (t : gentable.Table)
    (L : List (List BPair)) (hsq : reflSquareRead t)
    (hmsh : mShapeRead t L) (hsym : symRead t L)
    (i : Nat) (hi : i < t.rank) (x : List BPair)
    (hx : x.length = t.rank) (hxn : poly.pnorm x = x) :
    ground.countOf (reflAt t i x) L = ground.countOf x L := by
  have key := ground.countOf_invol (reflCond t i) L
    (fun a _ => reflCond_invol t i (hsq i hi) a)
    (fun a ha => by
      obtain ⟨hal, han⟩ := hmsh a ha
      rw [reflCond_pos t i a ⟨hal, han⟩]
      exact hsym a ha i hi) x
  rw [reflCond_pos t i x ⟨hx, hxn⟩] at key
  exact key

/-- The conditioned move's positive read: a framed member moves to
its reflected key at the flipped side. -/
private theorem flipAt_pos (t : gentable.Table) (i : Nat)
    (vp : List BPair × Bool)
    (hg : vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1) :
    assembly.flipAt t i vp = (reflAt t i vp.1, !vp.2) := by
  show (if vp.1.length = t.rank ∧ poly.pnorm vp.1 = vp.1 then
    (reflAt t i vp.1, !vp.2) else vp) = _
  exact if_pos hg

/-- The flipped guard reads the guard itself. -/
private theorem flipGuard (A : Nat) : ∀ a b : Bool,
    (if (!a) = (!b) then A else 0) = (if a = b then A else 0)
  | true, true => rfl
  | true, false => rfl
  | false, true => rfl
  | false, false => rfl

/-- The convolution's key move at a graded member: the reflected key
against a member reads the key against the member's own reflection,
the two counts one at the family's reflection invariance. -/
private theorem convRefl_step (t : gentable.Table)
    (L : List (List BPair)) (hsq : reflSquareRead t)
    (hmsh : mShapeRead t L) (hsym : symRead t L)
    (i : Nat) (hi : i < t.rank)
    (y : List BPair) (hy : y.length = t.rank) (hyn : poly.pnorm y = y)
    (k : List BPair) (hk : k.length = t.rank) (hkn : poly.pnorm k = k) :
    ground.countOf
        (poly.pnorm (elim.vecAdd (reflAt t i y) (poly.neg k))) L
      = ground.countOf
        (poly.pnorm (elim.vecAdd y (poly.neg (reflAt t i k)))) L := by
  have hrk : (reflAt t i k).length = t.rank := assembly.reflAt_length t i k
  have hrkn : poly.pnorm (reflAt t i k) = reflAt t i k :=
    assembly.reflAt_norm t i k
  have hry : (reflAt t i y).length = t.rank := assembly.reflAt_length t i y
  have hryn : poly.pnorm (reflAt t i y) = reflAt t i y :=
    assembly.reflAt_norm t i y
  have hXl : (poly.pnorm (elim.vecAdd y
      (poly.neg (reflAt t i k)))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd y _ t.rank hy
      ((ground.length_map BPair.swap _).trans hrk))
  have hXn : poly.pnorm (poly.pnorm (elim.vecAdd y
      (poly.neg (reflAt t i k))))
      = poly.pnorm (elim.vecAdd y (poly.neg (reflAt t i k))) :=
    poly.pnorm_pnorm _
  have hA : poly.pnorm (elim.vecAdd (reflAt t i k)
      (poly.pnorm (elim.vecAdd y (poly.neg (reflAt t i k))))) = y :=
    (addKey_iff t.rank y (reflAt t i k) _ hy hyn hrk hXl hXn).mpr rfl
  have hB : poly.pnorm (elim.vecAdd k (reflAt t i
      (poly.pnorm (elim.vecAdd y (poly.neg (reflAt t i k))))))
      = reflAt t i y := by
    refine Eq.trans ?_ (congrArg (reflAt t i) hA)
    rw [reflAt_vecAdd t i (reflAt t i k)
        (poly.pnorm (elim.vecAdd y (poly.neg (reflAt t i k)))) hrk hXl,
      assembly.reflAt_invol' t i (hsq i hi) k hk, hkn]
  have hC : poly.pnorm (elim.vecAdd (reflAt t i y) (poly.neg k))
      = reflAt t i (poly.pnorm (elim.vecAdd y
        (poly.neg (reflAt t i k)))) :=
    (addKey_iff t.rank (reflAt t i y) k _ hry hryn hk
      (assembly.reflAt_length t i _) (assembly.reflAt_norm t i _)).mp hB
  rw [hC]
  exact reflCond_count t L hsq hmsh hsym i hi _ hXl hXn

/-- `thm:memberchar`'s first read of the convolution: the reflected
key's count is the key's own on the flipped side — the family's
invariance moving the inner count and the graded list's closure
reindexing the outer fold along the conditioned move. -/
private theorem convRefl (t : gentable.Table)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hsq : reflSquareRead t) (hwsh : wShapeRead t W)
    (hclose : wCloseRead t W) (hmsh : mShapeRead t L)
    (hsym : symRead t L)
    (i : Nat) (hi : i < t.rank)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) (s : Bool) :
    convCount W L (reflAt t i y) s = convCount W L y (!s) := by
  have hcount : ∀ x, ground.countOf x (W.map (assembly.flipAt t i))
      = ground.countOf x W := by
    intro x
    rw [ground.countOf_map_iff (assembly.flipAt t i) W x
      (assembly.flipAt t i x)
      (fun v _ => Iff.intro
        (fun hv => by
          rw [hv, assembly.flipAt_invol t i (hsq i hi) v])
        (fun hv => by
          rw [← hv, assembly.flipAt_invol t i (hsq i hi) x]))]
    exact ground.countOf_invol (assembly.flipAt t i) W
      (fun a _ => assembly.flipAt_invol t i (hsq i hi) a)
      (fun a ha => by
        rw [flipAt_pos t i a (hwsh a ha)]
        exact hclose a ha i hi) x
  have hmap : ground.famFold Nat.add 0
      (fun vp => if (assembly.flipAt t i vp).2 = !s then ground.countOf
        (poly.pnorm (elim.vecAdd y (poly.neg (assembly.flipAt t i vp).1))) L
        else 0) W
      = ground.famFold Nat.add 0
        (fun vp => if vp.2 = !s then ground.countOf
          (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L else 0)
        (W.map (assembly.flipAt t i)) :=
    (ground.famFold_map Nat.add 0
      (fun vp => if vp.2 = !s then ground.countOf
        (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L else 0)
      (assembly.flipAt t i) W).symm
  rw [convCount_countOf t W L hwsh hmsh (reflAt t i y)
      (assembly.reflAt_length t i y) (assembly.reflAt_norm t i y) s,
    convCount_countOf t W L hwsh hmsh y hy hyn (!s)]
  refine Eq.trans ?_ (Eq.trans hmap (ground.famFold_relist Nat.add 0
    Nat.add_comm Nat.add_assoc _ (W.map (assembly.flipAt t i)) W hcount))
  refine ground.famFold_congr_members Nat.add 0 _ _ W (fun vp hvp => ?_)
  have hg := hwsh vp (ground.mem_of_countOf_pos vp W hvp)
  rw [flipAt_pos t i vp hg]
  show (if vp.2 = s then ground.countOf
      (poly.pnorm (elim.vecAdd (reflAt t i y) (poly.neg vp.1))) L
      else 0)
    = (if (!vp.2) = (!s) then ground.countOf
      (poly.pnorm (elim.vecAdd y (poly.neg (reflAt t i vp.1)))) L
      else 0)
  rw [convRefl_step t L hsq hmsh hsym i hi y hy hyn vp.1 hg.1 hg.2]
  exact (flipGuard _ vp.2 s).symm

/-- `thm:memberchar`'s second read of the convolution: an occupied
key joins the shifted key at a natural simple fold — the graded
member's own witness fold carrying its key to `ρ` and the family
member's carrying its key to `λ`, the two folds joined at the
counts' memberwise sum, one count per simple.  The key's normed
spelling binds no field of the derivation (the witness's own join
states it), and the witness family sits at the rank's order, the
join's own read. -/
private theorem convFold (t : gentable.Table)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (witsL : List (List Nat))
    (lamV : List BPair)
    (hwsh : wShapeRead t W) (hdom : wDomRead t W wits)
    (hmsh : mShapeRead t L) (hsupp : supportRead t L witsL lamV)
    (y : List BPair) (hy : y.length = t.rank)
    (s : Bool) (hocc : 0 < convCount W L y s) :
    ∃ c : List Nat, c.length = t.rank
      ∧ poly.pnorm (elim.vecAdd y (cartanFold t c))
        = poly.pnorm (elim.vecAdd lamV (rhoV t)) := by
  obtain ⟨vp, k, hvpW, hk, hke, _, nu, m, hnuL, hm, hme, hjoin⟩ :=
    conv_witness W L y s hocc
  obtain ⟨hvl, _⟩ := hwsh vp hvpW
  obtain ⟨hnu, _⟩ := hmsh nu hnuL
  have hW : poly.pnorm (elim.vecAdd vp.1
      (cartanFold t (ground.getAt [] wits k))) = rhoV t := by
    have h := hdom.2 k hk
    rw [hke] at h
    exact h
  have hL : poly.pnorm (elim.vecAdd nu
      (cartanFold t (ground.getAt [] witsL m))) = lamV := by
    have h := hsupp.2 m hm
    rw [hme] at h
    exact h
  have hAlen : (cartanFold t (ground.getAt [] wits k)).length = t.rank :=
    cartanFold_frame t vp.1 (ground.getAt [] wits k) (rhoV t)
      (ground.length_replicate (BPair.ofNat 1) t.rank) hW
  have hBlen : (cartanFold t (ground.getAt [] witsL m)).length = t.rank :=
    (cartanFold_lenEq t (ground.getAt [] witsL m)
      (ground.getAt [] wits k)).trans hAlen
  have hlam : lamV.length = t.rank := by
    rw [← hL, poly.pnorm_length,
      elim.length_vecAdd nu _ t.rank hnu hBlen]
  have hclen : (cartanFold t ((List.range t.rank).map
      (fun i => ground.getAt 0 (ground.getAt [] wits k) i
        + ground.getAt 0 (ground.getAt [] witsL m) i))).length
      = t.rank :=
    (cartanFold_lenEq t _ (ground.getAt [] wits k)).trans hAlen
  have hAB : (elim.vecAdd (cartanFold t (ground.getAt [] wits k))
      (cartanFold t (ground.getAt [] witsL m))).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hAlen hBlen
  have hWA : (elim.vecAdd vp.1
      (cartanFold t (ground.getAt [] wits k))).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hvl hAlen
  have hNB : (elim.vecAdd nu
      (cartanFold t (ground.getAt [] witsL m))).length = t.rank :=
    elim.length_vecAdd _ _ t.rank hnu hBlen
  refine ⟨(List.range t.rank).map
    (fun i => ground.getAt 0 (ground.getAt [] wits k) i
      + ground.getAt 0 (ground.getAt [] witsL m) i),
    ground.length_mapRange _ t.rank, ?_⟩
  have e1 : poly.pnorm (elim.vecAdd y (cartanFold t
        ((List.range t.rank).map
          (fun i => ground.getAt 0 (ground.getAt [] wits k) i
            + ground.getAt 0 (ground.getAt [] witsL m) i))))
      = poly.pnorm (elim.vecAdd y
        (elim.vecAdd (cartanFold t (ground.getAt [] wits k))
          (cartanFold t (ground.getAt [] witsL m)))) := by
    refine poly.pnorm_congr _ _ ?_ ?_
    · rw [elim.length_vecAdd y _ t.rank hy hclen,
        elim.length_vecAdd y _ t.rank hy hAB]
    · exact elim.polyOne_vecAdd y y _ _ (poly.oneValue_refl y)
        (poly.oneValue_symm (cartanFold_add t (ground.getAt [] wits k)
          (ground.getAt [] witsL m) hAlen)) rfl
        (hclen.trans hAB.symm)
  have e2 : elim.vecAdd (elim.vecAdd vp.1 nu)
        (elim.vecAdd (cartanFold t (ground.getAt [] wits k))
          (cartanFold t (ground.getAt [] witsL m)))
      = elim.vecAdd
        (elim.vecAdd vp.1 (cartanFold t (ground.getAt [] wits k)))
        (elim.vecAdd nu (cartanFold t (ground.getAt [] witsL m))) := by
    rw [elim.vecAdd_assoc vp.1 nu
        (elim.vecAdd (cartanFold t (ground.getAt [] wits k))
          (cartanFold t (ground.getAt [] witsL m))),
      ← elim.vecAdd_assoc nu (cartanFold t (ground.getAt [] wits k))
        (cartanFold t (ground.getAt [] witsL m)),
      elim.vecAdd_comm nu (cartanFold t (ground.getAt [] wits k)),
      elim.vecAdd_assoc (cartanFold t (ground.getAt [] wits k)) nu
        (cartanFold t (ground.getAt [] witsL m)),
      ← elim.vecAdd_assoc vp.1 (cartanFold t (ground.getAt [] wits k))
        (elim.vecAdd nu (cartanFold t (ground.getAt [] witsL m)))]
  rw [e1, ← hjoin, elim.pnorm_vecAdd_left (elim.vecAdd vp.1 nu)
      (elim.vecAdd (cartanFold t (ground.getAt [] wits k))
        (cartanFold t (ground.getAt [] witsL m)))
      ((elim.length_vecAdd vp.1 nu t.rank hvl hnu).trans hAB.symm),
    e2,
    ← elim.pnorm_vecAdd_left
      (elim.vecAdd vp.1 (cartanFold t (ground.getAt [] wits k)))
      (elim.vecAdd nu (cartanFold t (ground.getAt [] witsL m)))
      (hWA.trans hNB.symm),
    hW,
    elim.vecAdd_comm (rhoV t)
      (elim.vecAdd nu (cartanFold t (ground.getAt [] witsL m))),
    ← elim.pnorm_vecAdd_left
      (elim.vecAdd nu (cartanFold t (ground.getAt [] witsL m)))
      (rhoV t)
      (hNB.trans (ground.length_replicate (BPair.ofNat 1) t.rank).symm),
    hL]

/-! The shifted key's own reads: at the shifted key the convolution
reads one on the even side and none on the odd.  A graded member
off `ρ` contributes nothing — its own witness fold and the family
member's join to the sum's unit at every simple, where each
summand's positive `ρ`-dot forces the count to nought, so the
member's fold is vacant and its key is `ρ` itself. -/

/-- A graded member whose moved key is occupied in the family reads
`ρ` at its own key: the two witness folds' dots join to the sum's
unit, every summand at or beyond it, so every count is nought and
the member's fold absorbs. -/
private theorem convTop_off (t : gentable.Table) (F : FundData)
    (L : List (List BPair)) (witsL : List (List Nat))
    (lamV : List BPair)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F)
    (hsupp : supportRead t L witsL lamV)
    (hlam : lamRead t lamV)
    (v : List BPair) (hvl : v.length = t.rank)
    (hvn : poly.pnorm v = v)
    (cW : List Nat)
    (hW : poly.pnorm (elim.vecAdd v (cartanFold t cW)) = rhoV t)
    (mu : List BPair)
    (hmu : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd lamV (rhoV t))) (poly.neg v)) = mu)
    (hpos : 0 < ground.countOf mu L) :
    v = rhoV t := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have htl : (poly.pnorm (elim.vecAdd lamV (rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd lamV _ t.rank hlam.1 hrl)
  have htn : poly.pnorm (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      = poly.pnorm (elim.vecAdd lamV (rhoV t)) := poly.pnorm_pnorm _
  have hnv : (poly.neg v).length = t.rank :=
    (ground.length_map BPair.swap v).trans hvl
  have hmul : mu.length = t.rank := by
    rw [← hmu, poly.pnorm_length,
      elim.length_vecAdd (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        (poly.neg v) t.rank htl hnv]
  have hmun : poly.pnorm mu = mu := by
    rw [← hmu]
    exact poly.pnorm_pnorm _
  have hjoin : poly.pnorm (elim.vecAdd v mu)
      = poly.pnorm (elim.vecAdd lamV (rhoV t)) :=
    (addKey_iff t.rank (poly.pnorm (elim.vecAdd lamV (rhoV t))) v mu
      htl htn hvl hmul hmun).mpr hmu
  obtain ⟨m, hm, hme⟩ := ground.getAt_of_mem ([] : List BPair)
    (ground.mem_of_countOf_pos mu L hpos)
  have hL : poly.pnorm (elim.vecAdd mu
      (cartanFold t (ground.getAt [] witsL m))) = lamV := by
    have h := hsupp.2 m hm
    rw [hme] at h
    exact h
  have hcWlen : (cartanFold t cW).length = t.rank :=
    cartanFold_frame t v cW (rhoV t) hrl hW
  have h1 := assembly.dotB_foldKey t F hshape hsp v cW (rhoV t) hrl hW
  have h2 := assembly.dotB_foldKey t F hshape hsp mu
    (ground.getAt [] witsL m) lamV hlam.1 hL
  have h3 : (dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (rhoV t)).oneValue
      (dotB F v (rhoV t) + dotB F mu (rhoV t)) := by
    refine BPair.oneValue_trans (dotB_congrL F _ (elim.vecAdd v mu)
      (rhoV t) ?_) (dotB_addL t F hshape v mu (rhoV t) hvl hmul)
    have h := poly.pnorm_oneValue (elim.vecAdd v mu)
    rw [hjoin] at h
    exact h
  have h4 : (dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (rhoV t)).oneValue
      (dotB F lamV (rhoV t) + dotB F (rhoV t) (rhoV t)) :=
    BPair.oneValue_trans
      (dotB_congrL F _ (elim.vecAdd lamV (rhoV t)) (rhoV t)
        (poly.pnorm_oneValue _))
      (dotB_addL t F hshape lamV (rhoV t) (rhoV t) hlam.1 hrl)
  have hsum : (ground.famFold BPair.add BPair.unit
        (fun i => BPair.mul (BPair.ofNat (ground.getAt 0 cW i))
          (dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
            (rhoV t))) (List.range t.rank)
      + ground.famFold BPair.add BPair.unit
        (fun i => BPair.mul
          (BPair.ofNat (ground.getAt 0 (ground.getAt [] witsL m) i))
          (dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
            (rhoV t))) (List.range t.rank)).oneValue BPair.unit := by
    refine BPair.add_cancel
      (c := dotB F lamV (rhoV t) + dotB F (rhoV t) (rhoV t)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.oneValue_symm
        (BPair.oneValue_trans (BPair.oneValue_symm h3) h4))
      (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_add_comm _ _ _ _)) ?_
    refine BPair.oneValue_trans (BPair.add_congr h1 h2) ?_
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_comm _ _)) ?_
    exact BPair.oneValue_symm (BPair.unit_add _)
  have hcomb : (ground.bsum (fun i =>
      BPair.mul (BPair.ofNat (ground.getAt 0 cW i))
        (dotB F (posCorootV t (ground.getAt 0 F.simplePos i)) (rhoV t))
      + BPair.mul
        (BPair.ofNat (ground.getAt 0 (ground.getAt [] witsL m) i))
        (dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
          (rhoV t))) (List.range t.rank)).oneValue BPair.unit :=
    BPair.oneValue_trans (ground.foldB_add _ _ (List.range t.rank)) hsum
  have hmem := ground.bsum_unit_members _ (List.range t.rank)
    (fun x hx => ground.unitLeAdd
      (ground.leB_unit_mul _ (Or.inr (hrd _
        (assembly.simplePos_lt t F hshape (ground.ltOfMemRange hx)))))
      (ground.leB_unit_mul _ (Or.inr (hrd _
        (assembly.simplePos_lt t F hshape (ground.ltOfMemRange hx))))))
    hcomb
  have hzero : ∀ i, i < t.rank → ground.getAt 0 cW i = 0 := by
    intro i hi
    have hd : BPair.unit
        < dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
          (rhoV t) :=
      hrd _ (assembly.simplePos_lt t F hshape hi)
    have hone : (BPair.mul (BPair.ofNat (ground.getAt 0 cW i))
        (dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
          (rhoV t))).oneValue BPair.unit := by
      refine ground.leB_antisymm ?_
        (ground.leB_unit_mul _ (Or.inr hd))
      refine ground.dom_of_split (hmem i (ground.memRange hi)) ?_
      exact ground.leB_unit_mul _ (Or.inr hd)
    cases hci : ground.getAt 0 cW i with
    | zero => rfl
    | succ n =>
      rw [hci] at hone
      exact absurd (BPair.lt_congr (BPair.oneValue_refl BPair.unit)
        hone (ground.unitLtMul (ground.unitLtOfNat n) hd)) (by decide +kernel)
  rw [foldNull_key t cW hcWlen hzero v hvl hvn] at hW
  exact hW

/-- `thm:memberchar`'s third read of the convolution: the shifted
key reads one at the even grading and none at the odd — the inner
count at each graded member the indicator of `ρ`, the two guards
collapsing to the member's own pair, and the alternant's top read
closing.  The height ledger runs at the support folds' positive
`ρ`-dots alone, so the Gram's symmetry and defining reads bind no
field and sit off the statement. -/
private theorem convTop (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (witsL : List (List Nat))
    (lamV : List BPair)
    (hshape : fundShape t F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F)
    (hwsh : wShapeRead t W) (hdom : wDomRead t W wits)
    (htop : wTopRead t W)
    (hmsh : mShapeRead t L) (hsupp : supportRead t L witsL lamV)
    (htopL : topRead L lamV) (hlam : lamRead t lamV) :
    convCount W L (poly.pnorm (elim.vecAdd lamV (rhoV t))) false = 1
      ∧ convCount W L (poly.pnorm (elim.vecAdd lamV (rhoV t))) true
        = 0 := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have htl : (poly.pnorm (elim.vecAdd lamV (rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd lamV _ t.rank hlam.1 hrl)
  have htn : poly.pnorm (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      = poly.pnorm (elim.vecAdd lamV (rhoV t)) := poly.pnorm_pnorm _
  have hfold : ∀ s : Bool,
      convCount W L (poly.pnorm (elim.vecAdd lamV (rhoV t))) s
        = ground.countOf (rhoV t, s) W := by
    intro s
    rw [convCount_countOf t W L hwsh hmsh _ htl htn s,
      ground.countOf_fold]
    refine ground.famFold_congr_members Nat.add 0 _ _ W (fun vp hvp => ?_)
    have hvpW := ground.mem_of_countOf_pos vp W hvp
    obtain ⟨k, hk, hke⟩ := ground.getAt_of_mem
      (([], false) : List BPair × Bool) hvpW
    have hW : poly.pnorm (elim.vecAdd vp.1
        (cartanFold t (ground.getAt [] wits k))) = rhoV t := by
      have h := hdom.2 k hk
      rw [hke] at h
      exact h
    obtain ⟨hkl, hkn⟩ := hwsh vp hvpW
    have hinner : ground.countOf (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd lamV (rhoV t))) (poly.neg vp.1))) L
        = if vp.1 = rhoV t then 1 else 0 := by
      by_cases hvr : vp.1 = rhoV t
      · rw [if_pos hvr]
        have hkey := addKey_solve t.rank
          (poly.pnorm (elim.vecAdd lamV (rhoV t))) (rhoV t) lamV
          htl htn hrl hlam.1 hlam.2.1 rfl
        rw [hvr, hkey]
        exact htopL
      · rw [if_neg hvr]
        match Nat.eq_zero_or_pos (ground.countOf (poly.pnorm
          (elim.vecAdd (poly.pnorm (elim.vecAdd lamV (rhoV t)))
            (poly.neg vp.1))) L) with
        | Or.inl h0 => exact h0
        | Or.inr hp =>
          exact absurd (convTop_off t F L witsL lamV hshape hsp hrd
            hsupp hlam vp.1 hkl hkn (ground.getAt [] wits k) hW
            _ rfl hp) hvr
    rw [hinner]
    by_cases h1 : vp.1 = rhoV t
    · by_cases h2 : vp.2 = s
      · rw [if_pos h2, if_pos h1,
          if_pos (show (rhoV t, s) = vp by rw [← h1, ← h2])]
      · rw [if_neg h2,
          if_neg (fun he : (rhoV t, s) = vp =>
            h2 (congrArg Prod.snd he).symm)]
    · rw [if_neg h1,
        if_neg (fun he : (rhoV t, s) = vp =>
          h1 (congrArg Prod.fst he).symm)]
      by_cases h2 : vp.2 = s
      · rw [if_pos h2]
      · rw [if_neg h2]
  refine ⟨?_, ?_⟩
  · have h := htop.1
    rw [assembly.pnorm_rhoV t] at h
    rw [hfold false]
    exact h
  · have h := htop.2
    rw [assembly.pnorm_rhoV t] at h
    rw [hfold true]
    exact h

/-! The window's separation: off the shifted key every window key
pairs strictly below it.  The window's own enumeration names the
natural simple fold that carries the key to the shifted one, the
fold is occupied — a vacant one would return the shifted key
itself — and the square split's cross term rides the fold's two
pairings, each read at the counted rows' scaled lengths against a
coordinate at or beyond the unit, strict at the occupied count
against the key's own strict dominance. -/

/-- A fold of reads at or above the sum's unit with one member
strictly above it sits strictly above it. -/
private theorem foldUnitLt (f : Nat → BPair) (l : List Nat) (a : Nat)
    (ha : 0 < ground.countOf a l)
    (hle : ∀ x, 0 < ground.countOf x l → BPair.unit ≤ f x)
    (hlt : BPair.unit < f a) :
    BPair.unit < ground.famFold BPair.add BPair.unit f l :=
  ground.ltB_trans_le hlt (assembly.foldB_mem_le f l hle a ha)

/-- The window's enumeration read off a member: the key's own strict
dominance and the natural simple fold the shifted key carries it
by. -/
private theorem domWindow_elim (t : gentable.Table) (F : FundData)
    (lamV : List BPair) (y : List BPair)
    (hwin : y ∈ domWindow t F lamV) :
    (∀ k, k < t.rank → BPair.unit < ground.getAt BPair.unit y k)
      ∧ ∃ c : List Nat, poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        (poly.neg (cartanFold t c))) = y := by
  obtain ⟨hmem, hp⟩ := ground.mem_filter_of _ _ y hwin
  refine ⟨of_decide_eq_true hp, ?_⟩
  obtain ⟨c, _, hc⟩ := ground.mem_map_of _ _ y hmem
  exact ⟨c, hc⟩

/-- `thm:memberchar`'s separation read: off the shifted key every
dominant-window key's own square sits strictly below the shifted
key's — the joining simple fold occupied, its two pairings at the
key and at the shifted key carrying the square split's whole
correction. -/
private theorem sep_lt (t : gentable.Table) (F : FundData)
    (lamV : List BPair)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hrd : rhoDotRead t F) (hlam : lamRead t lamV)
    (y : List BPair) (hwin : y ∈ domWindow t F lamV)
    (hne : y ≠ poly.pnorm (elim.vecAdd lamV (rhoV t))) :
    dotB F y y
      < dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        (poly.pnorm (elim.vecAdd lamV (rhoV t))) := by
  obtain ⟨hy, hyn⟩ := domWindow_shape t F lamV y hwin
  obtain ⟨hdy, c, hc⟩ := domWindow_elim t F lamV y hwin
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have htl : (poly.pnorm (elim.vecAdd lamV (rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans
      (elim.length_vecAdd lamV _ t.rank hlam.1 hrl)
  have htn : poly.pnorm (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      = poly.pnorm (elim.vecAdd lamV (rhoV t)) := poly.pnorm_pnorm _
  have hnf : (poly.neg (cartanFold t c)).length
      = (cartanFold t c).length :=
    ground.length_map BPair.swap (cartanFold t c)
  have hfl : (cartanFold t c).length = t.rank := by
    refine Nat.le_antisymm (cartanFold_le t c) ?_
    have hh : (elim.vecAdd (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        (poly.neg (cartanFold t c))).length = t.rank := by
      rw [← poly.pnorm_length, hc]
      exact hy
    have h := assembly.vecAdd_lenR
      (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (poly.neg (cartanFold t c))
    rw [hh, hnf] at h
    exact h
  have hkey2 : poly.pnorm (elim.vecAdd y (cartanFold t c))
      = poly.pnorm (elim.vecAdd lamV (rhoV t)) :=
    addKey_join t.rank _ (cartanFold t c) y htl htn hfl hy hyn hc
  have hsq := dotB_sq_split t F hshape hgsym y (cartanFold t c) hy hfl
  rw [hkey2] at hsq
  have hone : poly.oneValue (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (elim.vecAdd y (cartanFold t c)) := by
    have h := poly.pnorm_oneValue (elim.vecAdd y (cartanFold t c))
    rw [hkey2] at h
    exact h
  have hsw : (dotB F y (cartanFold t c)).oneValue
      (dotB F (cartanFold t c) y) :=
    assembly.dotB_swap t F hshape hgsym y (cartanFold t c) hy hfl
  have htf : (dotB F (cartanFold t c) y
      + dotB F (cartanFold t c) (cartanFold t c)).oneValue
      (dotB F (cartanFold t c)
        (poly.pnorm (elim.vecAdd lamV (rhoV t)))) :=
    BPair.oneValue_symm (BPair.oneValue_trans
      (dotB_congrR F (cartanFold t c) _
        (elim.vecAdd y (cartanFold t c)) hone)
      (dotB_addR t F hshape (cartanFold t c) y (cartanFold t c)
        hfl hy hfl))
  have hcross : (dotB F y (cartanFold t c) + dotB F y (cartanFold t c)
      + dotB F (cartanFold t c) (cartanFold t c)).oneValue
      (dotB F (cartanFold t c) y
        + dotB F (cartanFold t c)
          (poly.pnorm (elim.vecAdd lamV (rhoV t)))) := by
    refine BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
    exact BPair.add_congr hsw
      (BPair.oneValue_trans
        (BPair.add_congr hsw (BPair.oneValue_refl _)) htf)
  have htopi : ∀ i, i < t.rank → BPair.unit ≤ ground.getAt BPair.unit
      (poly.pnorm (elim.vecAdd lamV (rhoV t))) i :=
    fun i hi => ground.leB_of_lt (shifted_reg t lamV hlam i hi)
  have hexists : ∃ i, i < t.rank ∧ ¬ ground.getAt 0 c i = 0 := by
    match ground.getAt_vac_or_occ c t.rank with
    | Or.inr h => exact h
    | Or.inl hall =>
      exfalso
      refine hne ?_
      rw [← hkey2]
      exact (foldNull_key t c hfl hall y hy hyn).symm
  obtain ⟨i0, hi0, hnz⟩ := hexists
  have hs1 : BPair.unit < BPair.ofNat (ground.getAt 0 c i0) := by
    cases hcv : ground.getAt 0 c i0 with
    | zero => exact absurd hcv hnz
    | succ n => exact ground.unitLtOfNat n
  have hmpos : 0 < F.scale * ground.getAt 0 t.lenNums i0 :=
    Nat.mul_pos hshape.2.2.1 (lenNums_pos t F hshape hsp hrd hgram hi0)
  have hs2 : BPair.unit
      < BPair.ofNat (F.scale * ground.getAt 0 t.lenNums i0) := by
    cases hm : F.scale * ground.getAt 0 t.lenNums i0 with
    | zero =>
      rw [hm] at hmpos
      exact absurd hmpos (Nat.lt_irrefl 0)
    | succ n => exact ground.unitLtOfNat n
  have hlt : BPair.unit < dotB F (cartanFold t c) y := by
    refine BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (BPair.oneValue_symm
        (assembly.dotB_cartanFold t F hshape hgram c hfl y hy)) ?_
    refine foldUnitLt _ (List.range t.rank) i0
      (ground.countOf_range_pos hi0)
      (fun x hx => ground.leB_unit_mul _ (ground.leB_unit_mul _
        (Or.inr (hdy x (ground.ltOfMem hx))))) ?_
    exact ground.unitLtMul hs1 (ground.unitLtMul hs2 (hdy i0 hi0))
  have hle : BPair.unit ≤ dotB F (cartanFold t c)
      (poly.pnorm (elim.vecAdd lamV (rhoV t))) := by
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (assembly.dotB_cartanFold t F hshape hgram c hfl _ htl)) ?_
    exact ground.foldB_nonneg _ (List.range t.rank) (fun x hx =>
      ground.leB_unit_mul _ (ground.leB_unit_mul _
        (htopi x (ground.ltOfMem hx))))
  have hposP : BPair.unit < dotB F (cartanFold t c) y
      + dotB F (cartanFold t c)
        (poly.pnorm (elim.vecAdd lamV (rhoV t))) :=
    BPair.lt_congr (BPair.add_unit BPair.unit) (BPair.oneValue_refl _)
      (ground.ltB_add hlt hle)
  have hPu : BPair.unit < dotB F y (cartanFold t c)
      + dotB F y (cartanFold t c)
      + dotB F (cartanFold t c) (cartanFold t c) :=
    BPair.lt_congr (BPair.oneValue_refl BPair.unit)
      (BPair.oneValue_symm hcross) hposP
  have hstep : dotB F y y < dotB F y y
      + (dotB F y (cartanFold t c) + dotB F y (cartanFold t c)
        + dotB F (cartanFold t c) (cartanFold t c)) :=
    BPair.lt_congr (BPair.unit_add _)
      (BPair.oneValue_of_eq (BPair.add_comm _ _))
      (ground.ltB_add hPu (ground.leB_refl (dotB F y y)))
  refine BPair.lt_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm ?_) hstep
  exact BPair.oneValue_trans hsq
    (BPair.oneValue_of_eq (BPair.add_assoc _ _ _))


/-! The window's completeness, and the regular read: an occupied
strictly dominant key joins the window at the capped coefficient
sum, and the separation prices the eigen identity's factor so the
counts balance off the shifted key. -/

/-- The window's completeness: a strictly dominant normed key of
the rank's order joining the shifted key at a natural simple fold
sits in the window — the fold's coefficient sum capped at the
height read, every simple's `ρ`-dot at or beyond one and the key's
own `ρ`-dot clearing `ρ`'s. -/
private theorem domWindow_mem (t : gentable.Table) (F : FundData)
    (lamV : List BPair)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hpsq : permSquareRead t F) (hpi : permImageRead t F)
    (hrd : rhoDotRead t F) (hlam : lamRead t lamV)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y)
    (hdy : ∀ k, k < t.rank →
      BPair.unit < ground.getAt BPair.unit y k)
    (c : List Nat) (hc : c.length = t.rank)
    (hkey : poly.pnorm (elim.vecAdd y (cartanFold t c))
      = poly.pnorm (elim.vecAdd lamV (rhoV t))) :
    y ∈ domWindow t F lamV := by
  have hrho := assembly.rhoRead_derived t F hshape hsp hpsq hpi hrd
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have htl : (poly.pnorm (elim.vecAdd lamV (rhoV t))).length
      = t.rank := by
    rw [poly.pnorm_length]
    exact elim.length_vecAdd lamV (rhoV t) t.rank hlam.1 hrl
  have hcf : (cartanFold t c).length = t.rank :=
    cartanFold_frame t y c _ htl hkey
  have hel : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (poly.neg (cartanFold t c))) = y :=
    addKey_solve t.rank (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (cartanFold t c) y htl (poly.pnorm_pnorm _) hcf hy hyn hkey
  have hfk := assembly.dotB_foldKey t F hshape hsp y c
    (poly.pnorm (elim.vecAdd lamV (rhoV t))) htl hkey
  have htopdot : (dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
      (rhoV t)).oneValue
      (dotB F lamV (rhoV t) + dotB F (rhoV t) (rhoV t)) :=
    BPair.oneValue_trans
      (dotB_congrL F _ _ _ (poly.pnorm_oneValue _))
      (dotB_addL t F hshape lamV (rhoV t) (rhoV t) hlam.1 hrl)
  have hyd := assembly.dom_of_beyond t F hshape hgram hgsym hrho y hy hdy
  have hfle : ground.famFold BPair.add BPair.unit
      (fun i => BPair.ofNat (ground.getAt 0 c i)
        * dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
          (rhoV t))
      (List.range t.rank) ≤ dotB F lamV (rhoV t) := by
    have hgap : BPair.unit
        ≤ dotB F y (rhoV t) + (dotB F (rhoV t) (rhoV t)).swap := by
      refine ground.leB_congr_left
        (ground.unitOfOne
          (BPair.oneValue_refl (dotB F (rhoV t) (rhoV t)))) ?_
      exact ground.leB_add hyd (ground.leB_refl _)
    have hchain : (ground.famFold BPair.add BPair.unit
        (fun i => BPair.ofNat (ground.getAt 0 c i)
          * dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
            (rhoV t))
        (List.range t.rank)
        + (dotB F y (rhoV t)
          + (dotB F (rhoV t) (rhoV t)).swap)).oneValue
        (dotB F lamV (rhoV t)) := by
      refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.add_assoc _ _ _).symm) ?_
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_of_eq (BPair.add_comm _ _))
        (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans (BPair.add_congr hfk
        (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans (BPair.add_congr htopdot
        (BPair.oneValue_refl _)) ?_
      refine BPair.oneValue_trans (BPair.oneValue_of_eq
        (BPair.add_assoc _ _ _)) ?_
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_refl _)
        (ground.unitOfOne (BPair.oneValue_refl _))) ?_
      exact BPair.add_unit _
    refine ground.leB_congr_right hchain ?_
    exact ground.leB_congr_left (BPair.add_unit _)
      (ground.leB_add (ground.leB_refl _) hgap)
  have hdsl : ((List.range t.rank).map (simDotAt t F)).length
      = t.rank :=
    ground.length_mapRange _ t.rank
  have hws : ground.sumNat (List.zipWith Nat.mul c
      ((List.range t.rank).map (simDotAt t F)))
      ≤ BPair.capN (dotB F lamV (rhoV t)) := by
    refine ground.BPair.ofNat_le_capN (ground.leB_trans ?_ hfle)
    show BPair.ofNat (ground.famFold Nat.add 0 (fun x => x)
        (List.zipWith Nat.mul c
          ((List.range t.rank).map (simDotAt t F))))
      ≤ ground.famFold BPair.add BPair.unit
        (fun i => BPair.ofNat (ground.getAt 0 c i)
          * dotB F (posCorootV t (ground.getAt 0 F.simplePos i))
            (rhoV t))
        (List.range t.rank)
    rw [← ground.famFold_getAt Nat.add 0 (fun x => x) 0
      (List.zipWith Nat.mul c
        ((List.range t.rank).map (simDotAt t F)))
      t.rank (ground.length_zipWith Nat.mul c
        ((List.range t.rank).map (simDotAt t F)) t.rank hc hdsl)]
    refine ground.leB_congr_left
      (BPair.oneValue_symm (ground.ofNat_famFold
        (fun k => ground.getAt 0 (List.zipWith Nat.mul c
          ((List.range t.rank).map (simDotAt t F))) k)
        (List.range t.rank))) ?_
    refine ground.bsum_le _ _ (List.range t.rank)
      (fun i hipos => ?_)
    have hir : i < t.rank := ground.ltOfMem hipos
    rw [ground.getAt_zipWith 0 0 0 Nat.mul c
      ((List.range t.rank).map (simDotAt t F)) i
      (by rw [hc]; exact hir) (by rw [hdsl]; exact hir)]
    rw [ground.getAt_map_range 0 (simDotAt t F) t.rank i, if_pos hir]
    refine ground.leB_congr_left
      (BPair.oneValue_symm (BPair.ofNat_mul (ground.getAt 0 c i)
        (simDotAt t F i))) ?_
    refine ground.leB_mulR
      (ground.unitLeOfNat (ground.getAt 0 c i)) ?_
    exact ground.leB_congr_right
      (BPair.oneValue_symm (BPair.ofNat_marginN (ground.leB_of_lt
        (hrd _ (assembly.simplePos_lt t F hshape hir)))))
      (ground.leB_refl _)
  have hdsp : ∀ k,
      k < ((List.range t.rank).map (simDotAt t F)).length →
      0 < ground.getAt 0 ((List.range t.rank).map (simDotAt t F)) k := by
    intro k hk
    rw [hdsl] at hk
    rw [ground.getAt_map_range 0 (simDotAt t F) t.rank k, if_pos hk]
    exact BPair.marginN_pos
      (hrd _ (assembly.simplePos_lt t F hshape hk))
  have hcm : c ∈ wBox ((List.range t.rank).map (simDotAt t F))
      (BPair.capN (dotB F lamV (rhoV t))) :=
    wBox_mem _ _ c (hc.trans hdsl.symm) hdsp hws
  have hdyE : decide (∀ k, k < t.rank → BPair.unit
      < ground.getAt BPair.unit (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        (poly.neg (cartanFold t c)))) k) = true := by
    rw [hel]
    exact decide_eq_true hdy
  have hfin := ground.mem_filter_to
    (fun z => decide (∀ k, k < t.rank → BPair.unit
      < ground.getAt BPair.unit z k))
    (ground.mem_map_to
      (fun cc => poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        (poly.neg (cartanFold t cc)))) hcm)
    hdyE
  rw [hel] at hfin
  exact hfin


/-- `thm:memberchar`'s fourth read of the convolution: at a strictly
dominant key off the shifted key the two graded counts read one
value — the eigen identity's factor priced strictly positive by the
separation, the count pair cancelled at the product's injectivity. -/
private theorem convReg (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (witsL : List (List Nat))
    (lamV : List BPair)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hform : reflFormRead t F)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (htop : wTopRead t W)
    (hmsh : mShapeRead t L) (hsupp : supportRead t L witsL lamV)
    (hlam : lamRead t lamV) (hrec : recRead t F W L lamV)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y)
    (hdy : ∀ k, k < t.rank →
      BPair.unit < ground.getAt BPair.unit y k)
    (hne : y ≠ poly.pnorm (elim.vecAdd lamV (rhoV t))) :
    convCount W L y true = convCount W L y false := by
  match Nat.eq_zero_or_pos
      (convCount W L y false + convCount W L y true) with
  | .inl h0 =>
    obtain ⟨hf, ht⟩ := Nat.eq_zero_of_add_eq_zero h0
    rw [hf, ht]
  | .inr hpos =>
    have hwin : y ∈ domWindow t F lamV := by
      match ground.posOr hpos with
      | .inl hoccf =>
        obtain ⟨c, hc, hkey⟩ := convFold t W wits L witsL lamV
          hwsh hdom hmsh hsupp y hy false hoccf
        exact domWindow_mem t F lamV hshape hgram hgsym hsp hpsq
          hpi hrd hlam y hy hyn hdy c hc hkey
      | .inr hocct =>
        obtain ⟨c, hc, hkey⟩ := convFold t W wits L witsL lamV
          hwsh hdom hmsh hsupp y hy true hocct
        exact domWindow_mem t F lamV hshape hgram hgsym hsp hpsq
          hpi hrd hlam y hy hyn hdy c hc hkey
    have hE := eigenAt t F W wits L lamV hshape hgram hgsym hsp hsq
      hpsq hpi hrd hform hwsh hclose hdom htop hmsh hrec y hwin
    have hlt := sep_lt t F lamV hshape hgram hgsym hsp hrd hlam
      y hwin hne
    have hXpos : BPair.unit
        < dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
            (poly.pnorm (elim.vecAdd lamV (rhoV t)))
          + (dotB F y y).swap :=
      BPair.lt_congr
        (ground.unitOfOne (BPair.oneValue_refl (dotB F y y)))
        (BPair.oneValue_refl _)
        (ground.ltB_add hlt (ground.leB_refl (dotB F y y).swap))
    have hXne : ¬ (dotB F (poly.pnorm (elim.vecAdd lamV (rhoV t)))
          (poly.pnorm (elim.vecAdd lamV (rhoV t)))
        + (dotB F y y).swap).oneValue BPair.unit :=
      fun hu => absurd
        (BPair.lt_congr (BPair.oneValue_refl _) hu hXpos)
        (by decide +kernel)
    have hcnt := ground.mulCancel hXne
      (BPair.oneValue_trans hE
        (BPair.oneValue_symm (BPair.mul_unit _)))
    exact (ground.BPair.ofCounts_unit.mp hcnt).symm


/-! The identity's per-key read, and its theorem: the product's
graded count balances the shifted alternant's at every key — the
framed keys by the walk at the convolution's four reads, and the
keys off the frame at every count's own vacancy. -/

/-- A key off the rank's normed frame reads the convolution's count
at the count's unit: every product key is a normed image at the
rank's order. -/
private theorem convCount_offFrame (t : gentable.Table)
    (W : List (List BPair × Bool)) (L : List (List BPair))
    (hwsh : wShapeRead t W) (hmsh : mShapeRead t L)
    (y : List BPair)
    (hoff : ¬ (y.length = t.rank ∧ poly.pnorm y = y)) (s : Bool) :
    convCount W L y s = 0 := by
  show ground.famFold Nat.add 0 (fun vp => if vp.2 = s then
      ground.famFold Nat.add 0 (fun nu =>
        if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0) L
      else 0) W = 0
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun _ => 0) W (fun vp hvp => ?_))
    (ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) W)
  obtain ⟨hk, _⟩ := hwsh vp (ground.mem_of_countOf_pos vp W hvp)
  have hin : ground.famFold Nat.add 0 (fun nu =>
      if poly.pnorm (elim.vecAdd vp.1 nu) = y then 1 else 0) L = 0 := by
    refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
      (fun _ => 0) L (fun nu hnu => ?_))
      (ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) L)
    obtain ⟨hnl, _⟩ := hmsh nu (ground.mem_of_countOf_pos nu L hnu)
    refine if_neg (fun hc => hoff ⟨?_, ?_⟩)
    · rw [← hc, poly.pnorm_length]
      exact elim.length_vecAdd vp.1 nu t.rank hk hnl
    · rw [← hc]
      exact poly.pnorm_pnorm _
  by_cases hb : vp.2 = s
  · rw [if_pos hb]
    exact hin
  · rw [if_neg hb]

/-- A key off the rank's normed frame reads the alternant data's
count at the count's unit: every member sits framed. -/
private theorem wCount_offFrame (t : gentable.Table)
    (W' : List (List BPair × Bool)) (hwsh' : wShapeRead t W')
    (y : List BPair)
    (hoff : ¬ (y.length = t.rank ∧ poly.pnorm y = y)) (s : Bool) :
    wCount W' y s = 0 := by
  match h0 : ground.countOf (y, s) W' with
  | 0 => exact h0
  | n + 1 =>
    refine absurd (hwsh' (y, s) (ground.mem_of_countOf_pos (y, s) W'
      (by rw [h0]; exact Nat.succ_pos n))) (fun hfr => hoff ?_)
    exact hfr

/-- The per-key balance of the product's data with the shifted
alternant's: `a_ρ ch_λ`'s graded count against `a_{λ+ρ}`'s, the
identity `a_ρ ch_λ = a_{λ+ρ}` coefficientwise
(`thm:memberchar`'s conclusion at a key). -/
def identityAt (W : List (List BPair × Bool))
    (L : List (List BPair)) (W' : List (List BPair × Bool))
    (y : List BPair) : Prop :=
  convCount W L y false + wCount W' y true
    = convCount W L y true + wCount W' y false

instance (W : List (List BPair × Bool)) (L : List (List BPair))
    (W' : List (List BPair × Bool)) (y : List BPair) :
    Decidable (identityAt W L W' y) :=
  inferInstanceAs (Decidable (_ = _))

/-- `thm:memberchar`: the member character identity
`a_ρ ch_λ = a_{λ+ρ}`, read key by key — the convolution of the
`ρ`-alternant's data with the multiplicity family balances the
shifted alternant's data at every key.  A framed key rides the
dominance walk at the convolution's four reads: the reflection
transport (`ch` invariant and `a_ρ` graded), the support at the
two witness folds' join, the shifted key's one-and-none read at
the two tops, and the regular read at the eigen identity against
the separation; a key off the frame reads all four counts at the
count's unit. -/
theorem identityRead (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (L : List (List BPair)) (witsL : List (List Nat))
    (lamV : List BPair)
    (W' : List (List BPair × Bool)) (wits' : List (List Nat))
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hform : reflFormRead t F)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (htop : wTopRead t W)
    (hmsh : mShapeRead t L) (hsym : symRead t L)
    (hsupp : supportRead t L witsL lamV)
    (htopL : topRead L lamV) (hlam : lamRead t lamV)
    (hwsh' : wShapeRead t W') (hclose' : wCloseRead t W')
    (hdom' : wDomAt t W' wits'
      (poly.pnorm (elim.vecAdd lamV (rhoV t))))
    (htop' : wTopAt W' (poly.pnorm (elim.vecAdd lamV (rhoV t))))
    (hreg' : wRegRead t W' (poly.pnorm (elim.vecAdd lamV (rhoV t))))
    (hrec : recRead t F W L lamV)
    (y : List BPair) :
    identityAt W L W' y := by
  by_cases hfr : y.length = t.rank ∧ poly.pnorm y = y
  · obtain ⟨hy, hyn⟩ := hfr
    have htl : (poly.pnorm (elim.vecAdd lamV (rhoV t))).length
        = t.rank :=
      (poly.pnorm_length _).trans (elim.length_vecAdd lamV _ t.rank
        hlam.1 (ground.length_replicate (BPair.ofNat 1) t.rank))
    exact fourReads_walk t F hshape hsp hsq hrd
      (poly.pnorm (elim.vecAdd lamV (rhoV t))) htl
      (convCount W L)
      (fun i hi z hz hzn s =>
        convRefl t W L hsq hwsh hclose hmsh hsym i hi z hz hzn s)
      (fun z hz _ s hocc =>
        match convFold t W wits L witsL lamV hwsh hdom hmsh hsupp
            z hz s hocc with
        | ⟨c, _, hkey⟩ => ⟨c, hkey⟩)
      (convTop t F W wits L witsL lamV hshape hsp hrd hwsh hdom
        htop hmsh hsupp htopL hlam)
      (fun z hz hzn hdz hne =>
        convReg t F W wits L witsL lamV hshape hgram hgsym hsp hsq
          hpsq hpi hrd hform hwsh hclose hdom htop hmsh hsupp hlam
          hrec z hz hzn hdz hne)
      W' wits' hclose' hdom' htop' hreg' y hy hyn
  · show convCount W L y false + wCount W' y true
      = convCount W L y true + wCount W' y false
    rw [convCount_offFrame t W L hwsh hmsh y hfr false,
      convCount_offFrame t W L hwsh hmsh y hfr true,
      wCount_offFrame t W' hwsh' y hfr false,
      wCount_offFrame t W' hwsh' y hfr true]

end memberchar
