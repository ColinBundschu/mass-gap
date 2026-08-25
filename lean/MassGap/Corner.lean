import MassGap.Certconstruct
import MassGap.Rankstable
import MassGap.Serstable
import MassGap.Memberdata
/-!
`lem:corner`'s corner count tier: toward the contact end the chain
reads in the corner coordinate, the ray `[η² : 1]` at the scale
pair `η = [en : ed]`.  At the cleared integer carrier
(`lem:dualtrunc`'s seam clause) the ray names the integer pencil
pair `(en²E : ed²M)` (`cornerPencil`), and the corner count is the
reversal count of the displayed form pair
`rev(η²E + ηη′₋G : M + ηη′₊G)` at the height `η′ = ⟨η′₊ : η′₋⟩` —
the height's two members cross-added onto the pair's two sides, the
display cleared by the scale's square (`cornerSite`, `cornerCount`;
`lem:inertia`, `thm:certconstruct`).  The corner data are the dual
pencil's at the substitution `σ = η²`, `λ = ηη′`: the corner count
is the seam pencil's own count at the level members
`(en·ed·hp, en·ed·hm)` (`corner_dual` at
`certconstruct.countAtPair`), the two site matrices one matrix at
the summands' exchange.  The display clears by the scale's square
at the seam identity's integer pencil, every entry's weight a
natural product of the scale's members and the height's.

The shifted-scaling tier carries the pencil `Q(σ) = σE + S_θ` at
the cap's site datum with its equal-scale read, its
positive-semidefinite split at the two summands' own, the cleared
`ρ, w` identity (`shiftQ_split`) and the three root reads as count
comparisons (`shift_count_le`, `shift_count_scale`,
`dual_count_mono` at the corner ray's own points); the drift tier
prices the ground's electric weight at the drift, the join of the
ground level with the top root (`drift_cap`).

The grade-key tier: the key `G(λ) := λ(θ^∨)` enters at the dual
fold's read `G = Σ_i m_i c^∨_i` over the halved summands
`2 c^∨_i · lenDen = c_i · lenNums_i` of the residue fold (`cvee`
with its naming read `cveeRead`; `con:gentable`'s root coroot pair
at `θ`, `con:sertables`' residue fold), `grade` the natural read at
a coroot list and `gradeV` the balance-pair fold at a content; the
summands join to the residue (`cvee_sum`), the vacuum reads the key
at the sum's unit (`grade_vac`), `ρ` reads it at the residue — the
root fold's coroot reads one at every simple key (`grade_rho`) —
and the coefficient sum
sits at or below the key (`coeffSum_le`).  The series' halved
summands are the displayed closed forms (`cvee_A`, `cvee_B`,
`cvee_C`, `cvee_D`) and the key telescopes at the sorted word —
the top pair's sum with the last coordinate withdrawn at `B`, the
top coordinate at `C`, and the top pair's sum with the
next-to-last coordinate withdrawn at `D`
(`grade_member_B`, `grade_member_C`, `grade_member_D`); at the
`A`-series' shape carrier the key reads the reduced shape's top
row, the pair `⟨λ_1 : λ_{d_f}⟩` at the one-member site, one value
per label (`gradeA` with `gradeA_fulls`, `gradeA_reduce`).

The move-cap tier: a `θ` content is the unit content or a root with
its balance partner (`prop:row`'s list), and the join
`ν + Σ d_i α_i = θ` at natural `d_i` prices the key read `ν(θ^∨)`
at magnitude at most two.  The table's two reads are the highest
root's dominant coroot pairs (`thetaDomRead`) and the dominance
join's componentwise witness, every positive fold at or below the
top's (`thetaTopRead`); at those with the shape, symmetry, norm and
naming reads a positive member's key read sits in `[0, 2]`
(`posGrade_cap` — the row keys cleared by the halved second member
read the top's coroot pairs at the form's symmetry, the lower wall
the dominant reads and the upper the norm `⟨θ,θ⟩ = 2` at the
dominance join), every `θ` content's key read and its balance
partner's sit at or below two (`content_cap`), the key fold is
additive over a content join at matched orders (`gradeV_add`), and
the key moves by at most two under adjoint fusion (`grade_move`).

The Casimir-cap tier: the fundamental display
`C₂(λ) = Σ m_i m_j ⟨ω_i,ω_j⟩ + Σ m_i ⟨ω_i,2ρ⟩` is priced at the
member's fundamental reads — the base at one or beyond, every Gram
entry within `[0, FN]` and every row's `ρ`-dot at or below `RN`
(`gramCapRead`) — and there `ĉ₂(λ)` sits below `(FN + RN)(G² + 1)`,
the cleared member pair's numerator side (`c2M_cap`: the
coefficient sum at or below the key by `coeffSum_le`, the doubled
cross term priced by the key's own square `2G ≤ G² + 1`).  The
coordinate route reads the series' displayed numerators against the
sorted word's key — the top pair's sum at `B` and `D`, the top
coordinate at `C` — each below `l(l+1)(K² + 1)` at the cleared
member pair `[l(l+1) : casDenX l]` (`casCap_B`, `casCap_C`,
`casCap_D` at one shared core over the entry and root-fold caps);
at the `A` series the reduced representative's cleared traceless
read sits below `d²(d+1)(K² + 1)` at the shape key (`dfQ_cap`, the
rows the shape's tail totals at or below the top row;
`def:c2hat`).

The per-key counts tier: the labels at one key value are the dual
fold's solutions, the coroot box under the key's own entry bound
filtered at the key (`keyAll` over `ground.boxAll`), where a coroot
list at the rank sits once exactly at its key value and off it at
the vacant count (`keyAll_countOf`, the entry bound the halved
summands' own at the naming read) with at most `(G+1)` per simple
key (`keyAll_length`).  The `θ` factor at a coroot list is the
highest root's fold against the length-weighted entries
(`thetaGap`), and at the raised member it reads
`2 lenDen (G + r)` — `(λ+ρ)(θ^∨) = G + r` cleared
(`thetaGap_read`) — so the member dimension sits at or below that
factor's power, every gap-product factor capped at the dominance
join's componentwise witness (`dimM_cap`).  At the member reads
`A` and `p` (`capA` the halved summands' scaled residue product,
`capP` the rank joined to the positive count) the per-key label and
dimension counts sit below `A (G+1)^p` (`keyCount_cap`,
`keyDim_cap`, the strictness the raised residue's own gap at the
occupied positive list).

The graded sums' arithmetic tier: the rising product from a floor
(`ground.rise`) carries its shift absorption, its Pascal identity
and its floor monotonicity, the constant power sits at or below it
— the display's `j! C(L+j, j)` the rising product's own value —
and the cleared graded sum of rising-product weights against split
powers descends by the exact Pascal identity from the geometric
seed, closing at the gap's power against the factorial and the
whole power (the `gradSum` reads, `lem:corner`'s two displayed
graded-sum reads).

The dimension-weighted family's fold tier: at the head order `o`
the labels enter positionally at the reads `dR`, `gR`, `eR` and the
fusion rows `NR`, the scale cleared at the triple `a + b = c`
(`ξ = [a:c]`, `w = [b:c]`), and the trial coefficient is the
dimension against the scale's split powers at the key, a row beyond
the key window at the count's unit (`trialAt`); the family's
pairing, its electric and magnetic reads and the top two key
values' boundary part are that coefficient's own folds
(`pairFold`, `elecFold`, `magFold`, `topFold`).  The four member
reads: the move cap prices the magnetic read termwise at the
dimension eigen-identity, every fusion target below the top two key
values staying in the family (`mag_low`); the boundary part sits at
or below the gap's multiple of the whole power at the counts'
squares and the certificate's power comparison (`top_cap`, the
boundary split termwise at the top two keys with each key's
squared fold at or below its count read's square); the electric
read closes at the Casimir cap against
the squared counts, the power cap and the Pascal descent closing
the weighted geometric sum at the cleared gap `b(a+c)`
(`elec_cap`); and the vacuum's unit term floors the pairing
(`vac_floor`).

The Rayleigh close: the trial family enters the head pencil as the
coefficient vector, one count per row (`trialVec`), and its three
quadratic reads at the ordered head are the folds themselves — the
diagonal head's at the electric fold (`quad_diag`), the identity
gram's at the pairing (`quad_gram`), the fusion rows' at the
magnetic fold (`quad_rows`) — each the count matrix's row-against-row
double fold read at the counts' own.  A witness vector pricing the
counted pair's site below the sum's unit occupies the count
(`rayleigh_count`, `lem:inertia`'s forcing clause at the one-row
list, an off-unit coefficient's square carrying the site's strict
read), and at the family's fold data the four member reads join to
the displayed comparison — the electric term at the Casimir cap
through the vacuum floor, the pairing at the move cap with the
boundary term at the certificate's comparison — so every occupied
margin above the assembled level reads the count occupied
(`family_ground`).  The drift closes at its two arithmetic reads:
the assembled level joined to the top root's cap sits at or below
`C_g`'s multiple of the gap at the bracket's upper side, the three
pieces the bracket comparison, the boundary identity and the cube
comparison `c³ ≤ 2bc² + a²c` off `c² + b² = 2bc + a²`
(`level_drift`); and the rate's power close raises the drift
comparison to the `q+1`-st power at the positive carrier's own fold
(`ground.Pos.pow`) and cancels the scale's power (`rate_close`).
-/

namespace corner
open ground elim inertia

/-- The corner ray's integer pencil: the ray `[η²:1]` at the scale
pair `η = [en:ed]` names the pencil pair `(en²E : ed²M)`, the seam
clause's own integer representative (`lem:dualtrunc`). -/
def cornerPencil (E M : Mat) (en ed : Pos) : Mat :=
  inertia.siteDatum (inertia.matScale (en * en) E)
    (inertia.matScale (ed * ed) M)

/-- The corner count's site matrix: the displayed pair
`(η²E + ηη′₋G : M + ηη′₊G)` at the height `⟨hp:hm⟩`, cleared by the
scale's square — every entry's weight a natural product of the
scale and the height's members. -/
def cornerSite (E M G : Mat) (en ed hp hm : Pos) : Mat :=
  inertia.siteDatum
    (elim.matAdd (inertia.matScale (en * en) E)
      (inertia.matScale (en * ed * hm) G))
    (elim.matAdd (inertia.matScale (ed * ed) M)
      (inertia.matScale (en * ed * hp) G))

/-- The corner count: the reversal count of the displayed form pair,
the height's members cross-added onto the pair's two sides, at the
split certificate (`lem:inertia`; `thm:certconstruct`). -/
def cornerCount {o : Nat} (E M G : Mat) (en ed hp hm : Pos)
    (n : Nat) (sp : inertia.Split o) : Prop :=
  elim.sqAt E o ∧ elim.sqAt M o ∧ elim.sqAt G o
  ∧ inertia.splitRead (cornerSite E M G en ed hp hm) sp
  ∧ inertia.revAt sp = n

instance {o : Nat} (E M G : Mat) (en ed hp hm : Pos) (n : Nat)
    (sp : inertia.Split o) :
    Decidable (cornerCount E M G en ed hp hm n sp) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The corner site and the seam pencil's site at the level members
`(en·ed·hp, en·ed·hm)` are one matrix: the four summands
`en²E`, `en·ed·hm·G`, `swap(ed²M)`, `swap(en·ed·hp·G)` exchange
across the sum. -/
private theorem cornerSite_dual (E M G : Mat) (en ed hp hm : Pos) :
    cornerSite E M G en ed hp hm
      = inertia.siteDatum
          (elim.matAdd (cornerPencil E M en ed)
            (inertia.matScale (en * ed * hm) G))
          (inertia.matScale (en * ed * hp) G) := by
  show elim.matAdd
      (elim.matAdd (inertia.matScale (en * en) E)
        (inertia.matScale (en * ed * hm) G))
      (elim.matSwap
        (elim.matAdd (inertia.matScale (ed * ed) M)
          (inertia.matScale (en * ed * hp) G)))
    = elim.matAdd
        (elim.matAdd
          (elim.matAdd (inertia.matScale (en * en) E)
            (elim.matSwap (inertia.matScale (ed * ed) M)))
          (inertia.matScale (en * ed * hm) G))
        (elim.matSwap (inertia.matScale (en * ed * hp) G))
  rw [elim.matSwap_matAdd (inertia.matScale (ed * ed) M)
      (inertia.matScale (en * ed * hp) G),
    elim.matAdd_shuffle (inertia.matScale (en * en) E)
      (inertia.matScale (en * ed * hm) G)
      (elim.matSwap (inertia.matScale (ed * ed) M))
      (elim.matSwap (inertia.matScale (en * ed * hp) G)),
    ← elim.matAdd_assoc
      (elim.matAdd (inertia.matScale (en * en) E)
        (elim.matSwap (inertia.matScale (ed * ed) M)))
      (inertia.matScale (en * ed * hm) G)
      (elim.matSwap (inertia.matScale (en * ed * hp) G))]

/-- The corner data are the dual pencil's at the substitution: the
corner count is the seam pencil's count at the level members
`(en·ed·hp, en·ed·hm)`, the site matrices one matrix at the
summands' exchange (`lem:dualtrunc`). -/
theorem corner_dual {o : Nat} (E M G : Mat) (en ed hp hm : Pos)
    (n : Nat) (sp : inertia.Split o)
    (hE : elim.sqAt E o) (hM : elim.sqAt M o) :
    cornerCount E M G en ed hp hm n sp
      ↔ certconstruct.countAtPair (cornerPencil E M en ed) G
          (en * ed * hp) (en * ed * hm) n sp := by
  constructor
  · intro h
    match h with
    | ⟨_, _, hG, hsplit, hrev⟩ =>
      refine ⟨inertia.sqAt_siteDatum o (inertia.matScale (en * en) E)
        (inertia.matScale (ed * ed) M)
        (inertia.sqAt_matScale o (en * en) E hE)
        (inertia.sqAt_matScale o (ed * ed) M hM), hG, ?_, hrev⟩
      rw [← cornerSite_dual E M G en ed hp hm]
      exact hsplit
  · intro h
    match h with
    | ⟨_, hG, hsplit, hrev⟩ =>
      refine ⟨hE, hM, hG, ?_, hrev⟩
      rw [cornerSite_dual E M G en ed hp hm]
      exact hsplit

/-! `lem:corner`'s shifted scaling: at the magnetic form cap `d_θ`
(`lem:fpcap`) the shifted pencil `Q(σ) := σE + S_θ`, at `S_θ` the
pair `(d_θ G : M)`'s site datum, is a sum of two
positive-semidefinite forms — the electric diagonal's and the cap's
— and at scales `σ′ < σ` with the cofactor `ρ` at `ρσ = σ′` the
comparison `ρQ(σ) ⪯ Q(σ′) ⪯ Q(σ)` reads `ρμ_j(σ) ≤ μ_j(σ′) ≤ μ_j(σ)`
at the shifted roots, `Q(σ′)` the sum `ρQ(σ) + wS_θ` at the gap `w`
with `ρ + w = 1`, the second summand positive semidefinite; the root
reads are the comparison's counts (`lem:inertia`), cutoff-free and
window-free, a form comparison compressing.  At the cleared carrier
the scales enter as the pairs `[sn : sd]`, `[tn : td]` with the
cross gap `g` at `tn·sd + g = sn·td` — the order's own witness —
`shiftQ` is the `sd`-cleared `Q`, the `ρ, w` display clears to the
natural-weight identity `shiftQ_split`, and the root reads are the
count comparisons at `lem:split`'s committed carrier — the two
sides `shift_count_le` and `shift_count_scale` with the ray's own
monotone read `dual_count_mono`, each at the stated
positive-semidefinite split data, and the pencil's own
positive-semidefinite read `shiftQ_psd` with the equal-scale
matrix identity `shiftQ_eq`. -/

/-- The cap's summand: at the magnetic form cap `d_θ`
(`lem:fpcap`) the pair `(d_θ G : M)`'s site datum `S_θ`, the second
of the shifted pencil's two positive-semidefinite forms. -/
def stheta (G M : Mat) (dth : Pos) : Mat :=
  inertia.siteDatum (inertia.matScale dth G) M

/-- The shifted pencil at a scale, cleared: `Q(σ) = σE + S_θ` at
the scale pair `σ = [sn : sd]` reads `sd·Q(σ) = sn·E + sd·S_θ`, the
sum of the electric diagonal's positive-semidefinite form and the
cap's (`lem:fpcap`). -/
def shiftQ (E G M : Mat) (dth sn sd : Pos) : Mat :=
  elim.matAdd (inertia.matScale sn E)
    (inertia.matScale sd (stheta G M dth))

/-- The scales' comparison display: at the lower scale
`[tn : td] < [sn : sd]`, the cross gap `g` at `tn·sd + g = sn·td`
the order's witness, the lower scale's pencil is `ρQ(σ) + wS_θ` —
the cofactor `ρ` at `ρσ = σ′` and the gap `w` at `ρ + w = 1` — read
at the cleared carrier as the natural-weight identity, the second
summand the cap's form. -/
theorem shiftQ_split (E G M : Mat) (dth sn sd tn td g : Pos)
    (hg : tn * sd + g = sn * td) :
    inertia.matScale (sn * sd * td) (shiftQ E G M dth tn td)
      = elim.matAdd
          (inertia.matScale (tn * sd * td) (shiftQ E G M dth sn sd))
          (inertia.matScale (sd * td * g) (stheta G M dth)) := by
  have eA : sn * sd * td * tn = tn * sd * td * sn := by
    rw [ground.mul_assoc (sn * sd) td tn, ground.mul_mul_comm' sn sd td tn,
      ground.mul_assoc (tn * sd) td sn, ground.mul_mul_comm' tn sd td sn,
      ground.mul_comm sn tn]
  have eB : sn * sd * td * td = tn * sd * td * sd + sd * td * g := by
    rw [ground.mul_assoc (sn * sd) td td,
      ground.mul_mul_mul_comm sn sd td td, ← hg,
      ground.right_distrib (tn * sd) g (sd * td),
      ground.mul_assoc (tn * sd) td sd, ground.mul_comm td sd,
      ground.mul_comm g (sd * td)]
  show inertia.matScale (sn * sd * td)
      (elim.matAdd (inertia.matScale tn E)
        (inertia.matScale td (stheta G M dth)))
    = elim.matAdd
        (inertia.matScale (tn * sd * td)
          (elim.matAdd (inertia.matScale sn E)
            (inertia.matScale sd (stheta G M dth))))
        (inertia.matScale (sd * td * g) (stheta G M dth))
  rw [inertia.matScale_matAdd (sn * sd * td) (inertia.matScale tn E)
      (inertia.matScale td (stheta G M dth)),
    inertia.matScale_matScale tn (sn * sd * td) E,
    inertia.matScale_matScale td (sn * sd * td) (stheta G M dth),
    inertia.matScale_matAdd (tn * sd * td) (inertia.matScale sn E)
      (inertia.matScale sd (stheta G M dth)),
    inertia.matScale_matScale sn (tn * sd * td) E,
    inertia.matScale_matScale sd (tn * sd * td) (stheta G M dth),
    elim.matAdd_assoc (inertia.matScale (tn * sd * td * sn) E)
      (inertia.matScale (tn * sd * td * sd) (stheta G M dth))
      (inertia.matScale (sd * td * g) (stheta G M dth)),
    ← inertia.matScale_addW (tn * sd * td * sd) (sd * td * g)
      (stheta G M dth), eA, eB]

/-- Two equal scales read one pencil outright: at the crossed tie
the two cleared pencils are one matrix. -/
theorem shiftQ_eq (E G M : Mat) (dth sn sd tn td : Pos)
    (h : tn * sd = sn * td) :
    inertia.matScale td (shiftQ E G M dth sn sd)
      = inertia.matScale sd (shiftQ E G M dth tn td) := by
  show inertia.matScale td
      (elim.matAdd (inertia.matScale sn E)
        (inertia.matScale sd (stheta G M dth)))
    = inertia.matScale sd
      (elim.matAdd (inertia.matScale tn E)
        (inertia.matScale td (stheta G M dth)))
  rw [inertia.matScale_matAdd td (inertia.matScale sn E)
      (inertia.matScale sd (stheta G M dth)),
    inertia.matScale_matAdd sd (inertia.matScale tn E)
      (inertia.matScale td (stheta G M dth)),
    inertia.matScale_matScale sn td E,
    inertia.matScale_matScale tn sd E,
    inertia.matScale_matScale sd td (stheta G M dth),
    inertia.matScale_matScale td sd (stheta G M dth),
    show td * sn = sd * tn by
      rw [ground.mul_comm td sn, ground.mul_comm sd tn, h],
    ground.mul_comm td sd]

/-- A summand's split reads the difference site of the sum against
the summed datum: the datum and its swap withdraw, so the site is
the summand's own value at the stated order. -/
private theorem addSite_congr {o : Nat} (Z T : Mat)
    (hZ : elim.sqAt Z o) (hT : elim.sqAt T o) (sp : inertia.Split o)
    (hs : inertia.splitRead Z sp) :
    inertia.splitRead (inertia.siteDatum (elim.matAdd Z T) T) sp := by
  refine inertia.splitRead_congr Z
    (inertia.siteDatum (elim.matAdd Z T) T)
    (inertia.sqAt_siteDatum o (elim.matAdd Z T) T
      (elim.sqAt_matAdd o Z T hZ hT) hT) ?_ sp hs
  show elim.matOneValue Z
    (elim.matAdd (elim.matAdd Z T) (elim.matSwap T))
  rw [elim.matAdd_assoc Z T (elim.matSwap T)]
  exact elim.matOne_symm (elim.matAdd_nullR Z
    (elim.matAdd T (elim.matSwap T)) hZ
    (elim.sqAt_matAdd o T (elim.matSwap T) hT
      (elim.sqAt_matSwap o T hT))
    (elim.matNull_add_swap T))

/-- The count comparison at a positive-semidefinite summand: at one
gram and one level the pencil raised by a positive-semidefinite
summand counts at or below the unraised pencil's
(`certconstruct.countAtPair_mono` at the summand's own split). -/
private theorem count_le_of_add {o : Nat} (Z H G : Mat) (x y : Pos)
    (n n' : Nat) (sp sp' spg : inertia.Split o)
    (hZ : inertia.splitRead Z spg) (hpsd : inertia.psdAt spg)
    (h : certconstruct.countAtPair (elim.matAdd Z H) G x y n sp)
    (h' : certconstruct.countAtPair H G x y n' sp') :
    n ≤ n' := by
  have hsite : inertia.siteDatum
      (elim.matAdd (elim.matAdd Z H) (inertia.matScale y G))
      (inertia.matScale x G)
      = elim.matAdd Z (inertia.siteDatum
          (elim.matAdd H (inertia.matScale y G))
          (inertia.matScale x G)) := by
    show elim.matAdd
        (elim.matAdd (elim.matAdd Z H) (inertia.matScale y G))
        (elim.matSwap (inertia.matScale x G))
      = elim.matAdd Z
          (elim.matAdd (elim.matAdd H (inertia.matScale y G))
            (elim.matSwap (inertia.matScale x G)))
    rw [elim.matAdd_assoc Z H (inertia.matScale y G),
      elim.matAdd_assoc Z (elim.matAdd H (inertia.matScale y G))
        (elim.matSwap (inertia.matScale x G))]
  refine certconstruct.countAtPair_mono (elim.matAdd Z H) H G x y x y
    n n' sp sp' spg ?_ hpsd h h'
  rw [hsite]
  exact addSite_congr _ _ hZ.1 h'.2.2.1.1 spg hZ

/-- The gap split at a scaled two-summand pencil: the outer scale's
read is the gap's first-summand diagonal raised onto the inner
scale's read, at the two weight joins. -/
private theorem scaleGap (c p g d q w v : Pos) (E X : Mat)
    (h1 : c * p = g + d * q) (h2 : c * w = d * v) :
    inertia.matScale c
        (elim.matAdd (inertia.matScale p E) (inertia.matScale w X))
      = elim.matAdd (inertia.matScale g E)
          (inertia.matScale d
            (elim.matAdd (inertia.matScale q E)
              (inertia.matScale v X))) := by
  rw [inertia.matScale_matAdd c (inertia.matScale p E)
      (inertia.matScale w X),
    inertia.matScale_matScale p c E,
    inertia.matScale_matScale w c X,
    inertia.matScale_matAdd d (inertia.matScale q E)
      (inertia.matScale v X),
    inertia.matScale_matScale q d E,
    inertia.matScale_matScale v d X,
    ← elim.matAdd_assoc (inertia.matScale g E)
      (inertia.matScale (d * q) E)
      (inertia.matScale (d * v) X),
    ← inertia.matScale_addW g (d * q) E, ← h1, ← h2]

/-- The shifted pencil is a sum of two positive-semidefinite
forms, the electric diagonal's and the cap's (`lem:fpcap`): a
split of the pencil reads positive semidefinite at the two
summands' own positive-semidefinite splits. -/
theorem shiftQ_psd {o : Nat} (E G M : Mat) (dth sn sd : Pos)
    (spE spS spQ : inertia.Split o)
    (hE : inertia.splitRead (inertia.matScale sn E) spE)
    (hEpsd : inertia.psdAt spE)
    (hS : inertia.splitRead
      (inertia.matScale sd (stheta G M dth)) spS)
    (hSpsd : inertia.psdAt spS)
    (hQ : inertia.splitRead (shiftQ E G M dth sn sd) spQ) :
    inertia.psdAt spQ := by
  show inertia.revAt spQ = 0
  have hle := inertia.rev_mono
    (inertia.matScale sd (stheta G M dth))
    (shiftQ E G M dth sn sd) spE spS spQ
    (addSite_congr (inertia.matScale sn E)
      (inertia.matScale sd (stheta G M dth)) hE.1 hS.1 spE hE)
    hEpsd hS hQ
  rw [show inertia.revAt spS = 0 from hSpsd] at hle
  exact Nat.le_antisymm hle (Nat.zero_le _)

/-- The count comparison at a scaled positive-semidefinite summand:
the summand's positivity read at the base's stated split, the
scaled split's own count the base's (`lem:inertia`). -/
private theorem count_le_of_gap {o : Nat} (B HL G : Mat)
    (c x y : Pos) (n n' : Nat) (sp sp' spB spg : inertia.Split o)
    (hB : inertia.splitRead B spB) (hBpsd : inertia.psdAt spB)
    (hsg : inertia.splitRead (inertia.matScale c B) spg)
    (h : certconstruct.countAtPair
      (elim.matAdd (inertia.matScale c B) HL) G x y n sp)
    (h' : certconstruct.countAtPair HL G x y n' sp') :
    n ≤ n' := by
  have hpsd : inertia.psdAt spg := by
    show inertia.revAt spg = 0
    rw [inertia.rev_scalePos c B spB spg hB hsg]
    exact hBpsd
  exact count_le_of_add (inertia.matScale c B) HL G x y n n'
    sp sp' spg hsg hpsd h h'

/-- The two scales' cleared pencils at the cross gap: the upper
scale's pencil is the lower's raised by the gap's electric
diagonal, `td·Q(σ) = gE + sd·Q(σ′)` at `tn·sd + g = sn·td`. -/
private theorem shiftQ_gap (E G M : Mat) (dth sn sd tn td g : Pos)
    (hg : tn * sd + g = sn * td) :
    inertia.matScale td (shiftQ E G M dth sn sd)
      = elim.matAdd (inertia.matScale g E)
          (inertia.matScale sd (shiftQ E G M dth tn td)) :=
  scaleGap td sn g sd tn sd td E (stheta G M dth)
    (by rw [ground.mul_comm td sn, ← hg,
      ground.add_comm (tn * sd) g, ground.mul_comm tn sd])
    (ground.mul_comm td sd)

/-- The shifted comparison's upper side `Q(σ′) ⪯ Q(σ)`: at one gram
and one level the upper scale's count sits at or below the lower
scale's, the difference the gap's electric diagonal — the electric
form positive semidefinite the comparison's one datum. -/
theorem shift_count_le {o : Nat} (E G M : Mat)
    (dth sn sd tn td g x y : Pos) (n n' : Nat)
    (sp sp' spE spg : inertia.Split o)
    (hg : tn * sd + g = sn * td)
    (hE : inertia.splitRead E spE) (hEpsd : inertia.psdAt spE)
    (hsg : inertia.splitRead (inertia.matScale g E) spg)
    (h : certconstruct.countAtPair
      (inertia.matScale td (shiftQ E G M dth sn sd)) G x y n sp)
    (h' : certconstruct.countAtPair
      (inertia.matScale sd (shiftQ E G M dth tn td)) G x y n' sp') :
    n ≤ n' := by
  rw [shiftQ_gap E G M dth sn sd tn td g hg] at h
  exact count_le_of_gap E
    (inertia.matScale sd (shiftQ E G M dth tn td)) G g x y n n'
    sp sp' spE spg hE hEpsd hsg h h'

/-- The shifted comparison's lower side `ρQ(σ) ⪯ Q(σ′)`: at one
gram and one level the cofactor's scaling of the upper scale's
pencil counts at or above the lower scale's, the difference the
gap's copy of the cap's form (`shiftQ_split`'s second summand). -/
theorem shift_count_scale {o : Nat} (E G M : Mat)
    (dth sn sd tn td g x y : Pos) (n n' : Nat)
    (sp sp' spS spg : inertia.Split o)
    (hg : tn * sd + g = sn * td)
    (hS : inertia.splitRead (stheta G M dth) spS)
    (hSpsd : inertia.psdAt spS)
    (hsg : inertia.splitRead
      (inertia.matScale (sd * td * g) (stheta G M dth)) spg)
    (h : certconstruct.countAtPair
      (inertia.matScale (tn * sd * td) (shiftQ E G M dth sn sd))
      G x y n sp)
    (h' : certconstruct.countAtPair
      (inertia.matScale (sn * sd * td) (shiftQ E G M dth tn td))
      G x y n' sp') :
    n' ≤ n := by
  rw [shiftQ_split E G M dth sn sd tn td g hg,
    elim.matAdd_comm
      (inertia.matScale (tn * sd * td) (shiftQ E G M dth sn sd))
      (inertia.matScale (sd * td * g) (stheta G M dth))] at h'
  exact count_le_of_gap (stheta G M dth)
    (inertia.matScale (tn * sd * td) (shiftQ E G M dth sn sd))
    G (sd * td * g) x y n' n sp' sp spS spg hS hSpsd hsg h' h

/-- The corner ray's two scales at the cross gap: the upper ray
point's cleared pencil is the lower's raised by the gap's electric
diagonal, `ed′²(en²E : ed²M) = gE + ed²(en′²E : ed′²M)` at
`en′²ed² + g = en²ed′²`. -/
private theorem cornerPencil_gap (E M : Mat) (en ed en' ed' g : Pos)
    (hg : en' * en' * (ed * ed) + g = en * en * (ed' * ed')) :
    inertia.matScale (ed' * ed') (cornerPencil E M en ed)
      = elim.matAdd (inertia.matScale g E)
          (inertia.matScale (ed * ed) (cornerPencil E M en' ed')) := by
  show inertia.matScale (ed' * ed')
      (elim.matAdd (inertia.matScale (en * en) E)
        (elim.matSwap (inertia.matScale (ed * ed) M)))
    = elim.matAdd (inertia.matScale g E)
        (inertia.matScale (ed * ed)
          (elim.matAdd (inertia.matScale (en' * en') E)
            (elim.matSwap (inertia.matScale (ed' * ed') M))))
  rw [← inertia.matScale_matSwap (ed * ed) M,
    ← inertia.matScale_matSwap (ed' * ed') M]
  exact scaleGap (ed' * ed') (en * en) g (ed * ed) (en' * en')
    (ed * ed) (ed' * ed') E (elim.matSwap M)
    (by rw [ground.mul_comm (ed' * ed') (en * en), ← hg,
      ground.add_comm (en' * en' * (ed * ed)) g,
      ground.mul_comm (en' * en') (ed * ed)])
    (ground.mul_comm (ed' * ed') (ed * ed))

/-- The corner ray's counts are monotone in the scale: at one gram
and one level the ray's upper point counts at or below the lower
point's, the two cleared pencils differing by the gap's electric
diagonal — the order witnessed by the counts monotone in the scale,
stated at the corner coordinate's own ray points. -/
theorem dual_count_mono {o : Nat} (E M G : Mat)
    (en ed en' ed' g x y : Pos) (n n' : Nat)
    (sp sp' spE spg : inertia.Split o)
    (hg : en' * en' * (ed * ed) + g = en * en * (ed' * ed'))
    (hE : inertia.splitRead E spE) (hEpsd : inertia.psdAt spE)
    (hsg : inertia.splitRead (inertia.matScale g E) spg)
    (h : certconstruct.countAtPair
      (inertia.matScale (ed' * ed') (cornerPencil E M en ed))
      G x y n sp)
    (h' : certconstruct.countAtPair
      (inertia.matScale (ed * ed) (cornerPencil E M en' ed'))
      G x y n' sp') :
    n ≤ n' := by
  rw [cornerPencil_gap E M en ed en' ed' g hg] at h
  exact count_le_of_gap E
    (inertia.matScale (ed * ed) (cornerPencil E M en' ed'))
    G g x y n n' sp sp' spE spg hE hEpsd hsg h h'


/-! `lem:corner`'s contact drift: the ground's electric weight rides
the contact drift.  At the dual representative the ground identity
reads `σ⟨ψ,Eψ⟩ = ε₀(σ)⟨ψ,Gψ⟩ + ⟨ψ,Mψ⟩`, and the electric weight is
priced `σ⟨ψ,Eψ⟩ ≤ g⟨ψ,Gψ⟩` at the drift `g` with `ε₀(σ) + m₊ = g` —
the magnetic read at or below the top root `m₊` of `(M:G)` on the
head, the order witnessed by the counts monotone in the scale
(`lem:inertia`), so the electric weight is priced by two located
roots and the drift is its own cap.  At the cleared representative
`[sn : sd]` the identity cross-adds at the level `⟨x : y⟩` and the
top-root cap at `⟨mx : my⟩`; the drift's join is the members' own,
`g = ⟨x + sd·mx : y + sd·my⟩` against the `sd`-cleared magnetic
read. -/

/-- The one-member site is additive in the ground datum: the summed
datum's site is the two sites' own sum. -/
private theorem ofPos_add (a b : Pos) :
    (BPair.ofPos (a + b)).oneValue (BPair.ofPos a + BPair.ofPos b) := by
  show a + b + Pos.one + (Pos.one + Pos.one)
    = a + Pos.one + (b + Pos.one) + Pos.one
  rw [ground.add_add_comm a Pos.one b Pos.one,
    ground.add_assoc (a + b) Pos.one (Pos.one + Pos.one),
    ground.add_assoc (a + b) (Pos.one + Pos.one) Pos.one,
    ground.add_assoc Pos.one Pos.one Pos.one]

/-- The contact drift: at the dual representative's ground identity
— the cleared pencil's quadratic read at the level `⟨x:y⟩` — with
the magnetic form at or below the top root `⟨mx:my⟩` of `(M:G)` on
the head, the electric weight is priced at the drift, the join of
the ground level with the top root (`lem:split`;
`lem:contactcell`'s reads at the contact end; `lem:inertia`). -/
theorem drift_cap {o : Nat} (E M G : Mat) (psi : List BPair)
    (sn sd x y mx my : Pos) (spM : inertia.Split o)
    (hlen : psi.length = o)
    (hMsq : elim.sqAt M o) (hGsq : elim.sqAt G o)
    (hid : (BPair.ofPos sn * inertia.quadForm E psi
        + BPair.ofPos y * inertia.quadForm G psi).oneValue
      (BPair.ofPos x * inertia.quadForm G psi
        + BPair.ofPos sd * inertia.quadForm M psi))
    (hcap : inertia.splitRead
      (inertia.siteDatum (inertia.matScale mx G)
        (elim.matAdd M (inertia.matScale my G))) spM)
    (hpsd : inertia.psdAt spM) :
    BPair.ofPos sn * inertia.quadForm E psi
        + BPair.ofPos (y + sd * my) * inertia.quadForm G psi
      ≤ BPair.ofPos (x + sd * mx) * inertia.quadForm G psi := by
  have hsG : elim.sqAt (inertia.matScale my G) o :=
    inertia.sqAt_matScale o my G hGsq
  have hxG : elim.sqAt (inertia.matScale mx G) o :=
    inertia.sqAt_matScale o mx G hGsq
  have hY : elim.sqAt (elim.matAdd M (inertia.matScale my G)) o :=
    elim.sqAt_matAdd o M (inertia.matScale my G) hMsq hsG
  have h1 := inertia.psd_all
    (inertia.siteDatum (inertia.matScale mx G)
      (elim.matAdd M (inertia.matScale my G))) spM hcap hpsd psi hlen
  have h2 : BPair.unit ≤ inertia.quadForm
      (inertia.siteDatum (inertia.matScale mx G)
        (elim.matAdd M (inertia.matScale my G))) psi :=
    ground.leB_of_not_lt h1
  have h4 : BPair.unit ≤ inertia.quadForm (inertia.matScale mx G) psi
      + (inertia.quadForm (elim.matAdd M (inertia.matScale my G)) psi).swap :=
    ground.leB_congr_right (inertia.quadForm_site_sq hxG hY hlen) h2
  have h5 : inertia.quadForm (elim.matAdd M (inertia.matScale my G)) psi
      ≤ inertia.quadForm (inertia.matScale mx G) psi :=
    ground.leB_of_unit_add h4
  have hqY :
      (inertia.quadForm (elim.matAdd M (inertia.matScale my G)) psi).oneValue
        (inertia.quadForm M psi + BPair.ofPos my * inertia.quadForm G psi) :=
    BPair.oneValue_trans
      (inertia.quadForm_add_sq hMsq hsG hlen)
      (BPair.add_congr (BPair.oneValue_refl _)
        (inertia.quadForm_ofPos my G psi))
  have hA : inertia.quadForm M psi + BPair.ofPos my * inertia.quadForm G psi
      ≤ BPair.ofPos mx * inertia.quadForm G psi :=
    ground.leB_congr hqY (inertia.quadForm_ofPos mx G psi) h5
  have hB := ground.leB_mulR
    (ground.leB_of_lt (ground.unitLtOfPos sd)) hA
  have hL : (BPair.ofPos sd * (inertia.quadForm M psi
        + BPair.ofPos my * inertia.quadForm G psi)).oneValue
      (BPair.ofPos sd * inertia.quadForm M psi
        + BPair.ofPos (sd * my) * inertia.quadForm G psi) := by
    rw [BPair.left_distrib]
    refine BPair.add_congr (BPair.oneValue_refl _) ?_
    rw [← BPair.mul_assoc]
    exact BPair.mul_congr_left (BPair.ofPos_mul sd my)
  have hR : (BPair.ofPos sd
        * (BPair.ofPos mx * inertia.quadForm G psi)).oneValue
      (BPair.ofPos (sd * mx) * inertia.quadForm G psi) := by
    rw [← BPair.mul_assoc]
    exact BPair.mul_congr_left (BPair.ofPos_mul sd mx)
  have hC : BPair.ofPos sd * inertia.quadForm M psi
      + BPair.ofPos (sd * my) * inertia.quadForm G psi
      ≤ BPair.ofPos (sd * mx) * inertia.quadForm G psi :=
    ground.leB_congr hL hR hB
  have hgoalL : (BPair.ofPos sn * inertia.quadForm E psi
        + BPair.ofPos (y + sd * my) * inertia.quadForm G psi).oneValue
      (BPair.ofPos x * inertia.quadForm G psi
        + (BPair.ofPos sd * inertia.quadForm M psi
          + BPair.ofPos (sd * my) * inertia.quadForm G psi)) := by
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (BPair.mul_congr_left (ofPos_add y (sd * my)))) ?_
    rw [BPair.right_distrib, ← BPair.add_assoc, ← BPair.add_assoc]
    exact BPair.add_congr hid (BPair.oneValue_refl _)
  have hgoalR : (BPair.ofPos x * inertia.quadForm G psi
        + BPair.ofPos (sd * mx) * inertia.quadForm G psi).oneValue
      (BPair.ofPos (x + sd * mx) * inertia.quadForm G psi) := by
    rw [← BPair.right_distrib]
    exact BPair.mul_congr_left (BPair.oneValue_symm (ofPos_add x (sd * mx)))
  exact ground.leB_congr (BPair.oneValue_symm hgoalL) hgoalR
    (ground.leB_add (ground.leB_refl _) hC)

/-! `lem:corner`'s grade key: the highest root's coroot pair
`G(λ) := λ(θ^∨)`, one natural per label, the dual fold's read at
the halved summands of the residue fold. -/

/-- The halved summands of the residue fold:
`2 c^∨_i · lenDen = c_i · lenNums_i` over the highest root's fold,
the fundamental keys' `θ`-coroot reads (`lem:corner`'s grade key;
`con:sertables`' residue fold). -/
def cvee (t : gentable.Table) : List Nat :=
  (List.range t.rank).map (fun i =>
    ground.getAt 0 t.thetaFold i * ground.getAt 0 t.lenNums i
      / (2 * t.lenDen))

/-- The halved summands' naming read: per key the cleared cofactor
identity with the summand at one or beyond. -/
def cveeRead (t : gentable.Table) : Prop :=
  ((List.range t.rank).all (fun i =>
    (ground.getAt 0 (cvee t) i * (2 * t.lenDen)
        == ground.getAt 0 t.thetaFold i * ground.getAt 0 t.lenNums i)
      && (1 ≤ ground.getAt 0 (cvee t) i))) = true

instance (t : gentable.Table) : Decidable (cveeRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The grade key at a coroot list: the dual fold's read
`G = Σ_i m_i c^∨_i`, one natural per label (`lem:corner`). -/
def grade (t : gentable.Table) (m : List Nat) : Nat :=
  ground.dotNat m (cvee t)

/-- The grade fold at a balance-pair content, the key's read at a
`θ`-content's coroot vector (`lem:corner`'s move cap). -/
def gradeV (t : gentable.Table) (x : List BPair) : BPair :=
  elim.dotP x (memberdata.natV (cvee t))

/-- The `A`-series' key at a shape: the pair `⟨λ_1 : λ_{d_f}⟩`'s
natural read, the coordinates below the full-column key
(`lem:corner`: the reduced shape's top row at the one-member
site). -/
def gradeA (s : places.Shape) : Nat :=
  ground.sumNat (List.take (s.length - 1) s)

/-- The halved summands are one per key. -/
private theorem cvee_len (t : gentable.Table) : (cvee t).length = t.rank :=
  ground.length_mapRange _ t.rank

/-- A key range's mapped family reads the map's value at every key
below the count. -/
private theorem mapRange_read {α : Type} (d0 : α) (f : Nat → α)
    (l i : Nat) (h : i < l) :
    ground.getAt d0 ((List.range l).map f) i = f i := by
  rw [ground.getAt_map_range d0 f l i, if_pos h]

/-- The halved summand at a key: the fold's entry against the
length's, halved at the cleared second member. -/
private theorem cvee_entry (t : gentable.Table) (i : Nat) (h : i < t.rank) :
    ground.getAt 0 (cvee t) i
      = ground.getAt 0 t.thetaFold i * ground.getAt 0 t.lenNums i
        / (2 * t.lenDen) :=
  mapRange_read 0 _ t.rank i h

/-- The naming read's cleared identity at a key. -/
private theorem cveeRead_mul (t : gentable.Table) (h : cveeRead t)
    (i : Nat) (hi : i < t.rank) :
    ground.getAt 0 (cvee t) i * (2 * t.lenDen)
      = ground.getAt 0 t.thetaFold i * ground.getAt 0 t.lenNums i :=
  ground.beqEqOf
    (ground.andSplitB (ground.all_range_read t.rank h i hi)).1

/-- The naming read's occupancy at a key. -/
private theorem cveeRead_pos (t : gentable.Table) (h : cveeRead t)
    (i : Nat) (hi : i < t.rank) : 1 ≤ ground.getAt 0 (cvee t) i :=
  of_decide_eq_true
    (ground.andSplitB (ground.all_range_read t.rank h i hi)).2

/-- The division at the vacant divisor reads the count's unit. -/
private theorem divZeroN (x : Nat) : x / 0 = 0 := by
  show Nat.div x 0 = 0
  delta Nat.div
  rw [dif_neg (fun h : 0 < 0 => Nat.lt_irrefl 0 h)]

/-- The vacant coefficient list pairs off at the sum's unit. -/
private theorem dotZeroL : ∀ (n : Nat) (Y : List Nat),
    ground.dotNat (List.replicate n 0) Y = 0
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, b :: Y => by
    show 0 * b + ground.dotNat (List.replicate n 0) Y = 0
    rw [Nat.zero_mul, Nat.zero_add]
    exact dotZeroL n Y

/-- The unit coefficient list pairs off at the second family's
total, at the matched count. -/
private theorem dotOnesL : ∀ (n : Nat) (Y : List Nat), Y.length = n →
    ground.dotNat (List.replicate n 1) Y = ground.sumNat Y
  | 0, [], _ => rfl
  | 0, _ :: _, h => Nat.noConfusion h
  | _ + 1, [], h => Nat.noConfusion h
  | n + 1, b :: Y, h => by
    show 1 * b + ground.dotNat (List.replicate n 1) Y
      = b + ground.sumNat Y
    rw [Nat.one_mul, dotOnesL n Y (Nat.succ.inj h)]

/-- The coefficient total sits at or below the pairing against a
family occupied at every paired key. -/
private theorem dotGeSum : ∀ (m Y : List Nat), m.length ≤ Y.length →
    (∀ i, i < m.length → 1 ≤ ground.getAt 0 Y i) →
    ground.sumNat m ≤ ground.dotNat m Y
  | [], _, _, _ => Nat.le_refl 0
  | _ :: _, [], h, _ => absurd h (Nat.not_succ_le_zero _)
  | a :: m, b :: Y, h, hb => by
    show a + ground.sumNat m ≤ a * b + ground.dotNat m Y
    have h1 : a ≤ a * b := by
      have h2 := Nat.mul_le_mul_left a (hb 0 (Nat.succ_pos _))
      rw [Nat.mul_one] at h2
      exact h2
    exact Nat.add_le_add h1
      (dotGeSum m Y (Nat.le_of_succ_le_succ h)
        (fun i hi => hb (i + 1) (Nat.succ_lt_succ hi)))

/-- The halved summands join to the residue:
`Σ_i c^∨_i = r` at the shape and naming reads, the residue fold's
own division read back (`lem:corner`; `con:sertables`). -/
theorem cvee_sum : ∀ t : gentable.Table, gentable.shapeRead t →
    cveeRead t → ground.sumNat (cvee t) = gentable.residue t := by
  intro t hs hc
  have s1 := ground.andSplitB hs
  have s2 := ground.andSplitB s1.1
  have s3 := ground.andSplitB s2.1
  have s4 := ground.andSplitB s3.1
  have hln : t.lenNums.length = t.rank := ground.beqEqOf s4.1
  have hth : t.thetaFold.length = t.rank := ground.beqEqOf s2.2
  have hres : gentable.residue t
      = ground.famFold Nat.add 0
          (fun i => ground.getAt 0 t.thetaFold i
            * ground.getAt 0 t.lenNums i)
          (List.range t.rank) / (2 * t.lenDen) := by
    show ground.dotNat t.thetaFold t.lenNums / (2 * t.lenDen) = _
    rw [ground.dotNat_index t.thetaFold t.lenNums (hln.trans hth.symm), hth]
  have hsum : ground.sumNat (cvee t)
      = ground.famFold Nat.add 0
          (fun i => ground.getAt 0 t.thetaFold i
              * ground.getAt 0 t.lenNums i / (2 * t.lenDen))
          (List.range t.rank) :=
    ground.sumMap _ (List.range t.rank)
  match Nat.eq_zero_or_pos (2 * t.lenDen) with
  | Or.inl hD0 =>
    rw [hD0] at hres hsum
    rw [hsum, hres, divZeroN, ground.famFold_zero _
      (fun i => divZeroN _) (List.range t.rank)]
  | Or.inr hDpos =>
    have hmul : ground.sumNat (cvee t) * (2 * t.lenDen)
        = ground.famFold Nat.add 0
            (fun i => ground.getAt 0 t.thetaFold i
              * ground.getAt 0 t.lenNums i)
            (List.range t.rank) := by
      rw [hsum, ← ground.famFold_mulR (2 * t.lenDen) _ (List.range t.rank)]
      refine ground.famFold_congr_range _ _ t.rank (fun i hi => ?_)
      rw [← cvee_entry t i hi]
      exact cveeRead_mul t hc i hi
    rw [hres, ← hmul, ground.divMulSelf _ _ hDpos]

/-- The vacuum reads the key at the sum's unit. -/
theorem grade_vac : ∀ t : gentable.Table,
    grade t (List.replicate t.rank 0) = 0 := by
  intro t
  exact dotZeroL t.rank (cvee t)

/-- `ρ` reads the key at the residue: the root fold's coroot reads
one at every simple key (`sertables.rhoV`; `con:sertables`), so
the key folds the halved summands whole (`lem:corner`). -/
theorem grade_rho : ∀ t : gentable.Table, gentable.shapeRead t →
    cveeRead t →
    grade t (List.replicate t.rank 1) = gentable.residue t := by
  intro t hs hc
  show ground.dotNat (List.replicate t.rank 1) (cvee t) = gentable.residue t
  rw [dotOnesL t.rank (cvee t) (cvee_len t)]
  exact cvee_sum t hs hc

/-- The coefficient sum sits at or below the key, each halved
summand at one or beyond. -/
theorem coeffSum_le : ∀ (t : gentable.Table) (m : List Nat),
    cveeRead t → m.length ≤ t.rank →
    ground.sumNat m ≤ grade t m := by
  intro t m hc hlen
  refine dotGeSum m (cvee t) ?_ ?_
  · rw [cvee_len t]; exact hlen
  · intro i hi
    exact cveeRead_pos t hc i (Nat.lt_of_lt_of_le hi hlen)

/-- The occupancy window is one entry per key. -/
private theorem ind_len (l a b : Nat) : (sertables.ind l a b).length = l :=
  ground.length_mapRange _ l

/-- The occupancy window's entry: one on the keys of the stated
interval, the count's unit off it. -/
private theorem ind_read (l a b i : Nat) (h : i < l) :
    ground.getAt 0 (sertables.ind l a b) i
      = if a ≤ i && i < b then 1 else 0 :=
  mapRange_read 0 (fun k => if a ≤ k && k < b then 1 else 0) l i h

/-- The `B` table's highest-root fold at a key: the head window
joined to the doubled tail window. -/
private theorem thetaB_read (l i : Nat) (h : i < l) :
    ground.getAt 0 (sertables.tableB l).thetaFold i
      = (if 0 ≤ i && i < 1 then 1 else 0)
        + ((if 1 ≤ i && i < l then 1 else 0)
          + (if 1 ≤ i && i < l then 1 else 0)) := by
  have e1 : (sertables.ind l 0 1).length = l := ind_len l 0 1
  have e2 : (sertables.ind l 1 l).length = l := ind_len l 1 l
  have e3 : (List.zipWith (fun a b => a + b) (sertables.ind l 1 l)
      (sertables.ind l 1 l)).length = l :=
    ground.length_zipWith _ _ _ l e2 e2
  show ground.getAt 0 (List.zipWith (fun a b => a + b)
      (sertables.ind l 0 1)
      (List.zipWith (fun a b => a + b) (sertables.ind l 1 l)
        (sertables.ind l 1 l))) i = _
  rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e1]; exact h) (by rw [e3]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e2]; exact h) (by rw [e2]; exact h),
    ind_read l 0 1 i h, ind_read l 1 l i h]

/-- The `C` table's highest-root fold at a key: the doubled
leading window joined to the last key's own. -/
private theorem thetaC_read (l i : Nat) (h : i < l) :
    ground.getAt 0 (sertables.tableC l).thetaFold i
      = ((if 0 ≤ i && i < l - 1 then 1 else 0)
          + (if 0 ≤ i && i < l - 1 then 1 else 0))
        + (if l - 1 ≤ i && i < l then 1 else 0) := by
  have e1 : (sertables.ind l 0 (l - 1)).length = l := ind_len l 0 (l - 1)
  have e2 : (sertables.ind l (l - 1) l).length = l := ind_len l (l - 1) l
  have e3 : (List.zipWith (fun a b => a + b) (sertables.ind l 0 (l - 1))
      (sertables.ind l 0 (l - 1))).length = l :=
    ground.length_zipWith _ _ _ l e1 e1
  show ground.getAt 0 (List.zipWith (fun a b => a + b)
      (List.zipWith (fun a b => a + b) (sertables.ind l 0 (l - 1))
        (sertables.ind l 0 (l - 1)))
      (sertables.ind l (l - 1) l)) i = _
  rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e3]; exact h) (by rw [e2]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e1]; exact h) (by rw [e1]; exact h),
    ind_read l 0 (l - 1) i h, ind_read l (l - 1) l i h]

/-- The `D` table's highest-root fold at a key, past the fork
rank: the head window, the doubled interior window and the last
two keys' own. -/
private theorem thetaD_read (l i : Nat) (h3 : 3 ≤ l) (h : i < l) :
    ground.getAt 0 (sertables.tableD l).thetaFold i
      = (if 0 ≤ i && i < 1 then 1 else 0)
        + (((if 1 ≤ i && i < l - 2 then 1 else 0)
            + (if 1 ≤ i && i < l - 2 then 1 else 0))
          + (if l - 2 ≤ i && i < l then 1 else 0)) := by
  have hne : ¬ ((1 + 1 == l) = true) := by
    intro hb
    have he : 1 + 1 = l := ground.beqEqOf hb
    rw [← he] at h3
    exact absurd h3 (Nat.lt_irrefl 2)
  have e1 : (sertables.ind l 0 1).length = l := ind_len l 0 1
  have e2 : (sertables.ind l 1 (l - 2)).length = l := ind_len l 1 (l - 2)
  have e4 : (sertables.ind l (l - 2) l).length = l := ind_len l (l - 2) l
  have e3 : (List.zipWith (fun a b => a + b) (sertables.ind l 1 (l - 2))
      (sertables.ind l 1 (l - 2))).length = l :=
    ground.length_zipWith _ _ _ l e2 e2
  have e5 : (List.zipWith (fun a b => a + b)
      (List.zipWith (fun a b => a + b) (sertables.ind l 1 (l - 2))
        (sertables.ind l 1 (l - 2)))
      (sertables.ind l (l - 2) l)).length = l :=
    ground.length_zipWith _ _ _ l e3 e4
  have hth : (sertables.tableD l).thetaFold
      = List.zipWith (fun a b => a + b) (sertables.ind l 0 1)
          (List.zipWith (fun a b => a + b)
            (List.zipWith (fun a b => a + b) (sertables.ind l 1 (l - 2))
              (sertables.ind l 1 (l - 2)))
            (sertables.ind l (l - 2) l)) := by
    show (if (1 + 1 == l) = true then
        List.zipWith (fun a b => a + b) (sertables.ind l 0 (l - 2))
          (sertables.ind l (l - 1) l)
      else List.zipWith (fun a b => a + b) (sertables.ind l 0 1)
          (List.zipWith (fun a b => a + b)
            (List.zipWith (fun a b => a + b) (sertables.ind l 1 (l - 2))
              (sertables.ind l 1 (l - 2)))
            (sertables.ind l (l - 2) l))) = _
    exact if_neg hne
  rw [hth,
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e1]; exact h) (by rw [e5]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e3]; exact h) (by rw [e4]; exact h),
    ground.getAt_zipWith 0 0 0 (fun a b => a + b) _ _ i
        (by rw [e2]; exact h) (by rw [e2]; exact h),
    ind_read l 0 1 i h, ind_read l 1 (l - 2) i h,
    ind_read l (l - 2) l i h]

/-- The `B` table's length list at a key: one at the last key,
two below it. -/
private theorem lenB_read (l i : Nat) (h : i < l) :
    ground.getAt 0 (sertables.tableB l).lenNums i
      = if i + 1 == l then 1 else 2 :=
  mapRange_read 0 (fun k => if k + 1 == l then 1 else 2) l i h

/-- The `C` table's length list at a key: two at the last key,
one below it. -/
private theorem lenC_read (l i : Nat) (h : i < l) :
    ground.getAt 0 (sertables.tableC l).lenNums i
      = if i + 1 == l then 2 else 1 :=
  mapRange_read 0 (fun k => if k + 1 == l then 2 else 1) l i h

/-- The `A` table's halved summands, the displayed closed form in
the rank: one at every key. -/
theorem cvee_A : ∀ r : Nat,
    cvee (gentable.tableA r) = List.replicate r 1 := by
  intro r
  have hrk : (gentable.tableA r).rank = r := rfl
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [cvee_len (gentable.tableA r), hrk, ground.length_replicate 1 r]
  · intro i hi
    rw [cvee_len (gentable.tableA r), hrk] at hi
    rw [cvee_entry (gentable.tableA r) i hi,
      show (gentable.tableA r).thetaFold = List.replicate r 1 from rfl,
      show (gentable.tableA r).lenNums = List.replicate r 2 from rfl,
      show (gentable.tableA r).lenDen = 1 from rfl,
      ground.getAt_replicate 0 1 r i hi,
      ground.getAt_replicate 0 2 r i hi]

/-- The `B` table's halved summands, the displayed closed form in
the rank: one at the first and last keys, two between. -/
theorem cvee_B : ∀ l : Nat, 2 ≤ l → cvee (sertables.tableB l)
    = (List.range l).map (fun i =>
        if i == 0 then 1 else if i + 1 == l then 1 else 2) := by
  intro l h2
  have hrk : (sertables.tableB l).rank = l := rfl
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [cvee_len (sertables.tableB l), hrk, ground.length_mapRange]
  · intro i hi
    rw [cvee_len (sertables.tableB l), hrk] at hi
    rw [mapRange_read 0 _ l i hi, cvee_entry (sertables.tableB l) i hi,
      thetaB_read l i hi, lenB_read l i hi,
      show (sertables.tableB l).lenDen = 1 from rfl]
    match i, hi with
    | 0, _ =>
      have hne : ¬ (0 + 1 = l) := by
        intro he
        rw [← he] at h2
        exact absurd h2 (Nat.lt_irrefl 1)
      rw [ground.neBeqOf hne]
      show (1 + (0 + 0)) * 2 / (2 * 1) = 1
      exact rfl
    | j + 1, hj =>
      rw [decide_eq_true hj]
      by_cases hA : j + 1 + 1 = l
      · rw [ground.eqBeqOf hA]
        show (0 + (1 + 1)) * 1 / (2 * 1) = 1
        exact rfl
      · rw [ground.neBeqOf hA]
        show (0 + (1 + 1)) * 2 / (2 * 1) = 2
        exact rfl

/-- The `C` table's halved summands, the displayed closed form in
the rank: one at every key. -/
theorem cvee_C : ∀ l : Nat,
    cvee (sertables.tableC l) = List.replicate l 1 := by
  intro l
  have hrk : (sertables.tableC l).rank = l := rfl
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [cvee_len (sertables.tableC l), hrk, ground.length_replicate 1 l]
  · intro i hi
    rw [cvee_len (sertables.tableC l), hrk] at hi
    rw [cvee_entry (sertables.tableC l) i hi, thetaC_read l i hi,
      lenC_read l i hi, ground.getAt_replicate 0 1 l i hi,
      show (sertables.tableC l).lenDen = 1 from rfl]
    by_cases he : i + 1 = l
    · have hl1 : l - 1 = i := by
        rw [← he]
        exact rfl
      rw [hl1, decide_eq_true (Nat.zero_le i),
        decide_eq_false (Nat.lt_irrefl i),
        decide_eq_true (Nat.le_refl i), decide_eq_true hi,
        ground.eqBeqOf he]
      show ((0 + 0) + 1) * 2 / (2 * 1) = 1
      exact rfl
    · have hlt : i + 1 < l := Nat.lt_of_le_of_ne hi he
      have h1l : 1 ≤ l := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le i)) hi
      have hll : l - 1 + 1 = l := ground.subAdd h1l
      have hsub : i < l - 1 := by
        rw [← hll] at hlt
        exact Nat.lt_of_succ_lt_succ hlt
      have hnle : ¬ (l - 1 ≤ i) := fun hle =>
        Nat.lt_irrefl i (Nat.lt_of_lt_of_le hsub hle)
      rw [decide_eq_true (Nat.zero_le i), decide_eq_true hsub,
        decide_eq_false hnle, ground.neBeqOf he]
      show ((1 + 1) + 0) * 1 / (2 * 1) = 1
      exact rfl

/-- The `D` table's halved summands, the displayed closed form in
the rank: one at the first and last two keys, two between. -/
theorem cvee_D : ∀ l : Nat, 3 ≤ l → cvee (sertables.tableD l)
    = (List.range l).map (fun i =>
        if i == 0 then 1 else if l ≤ i + 2 then 1 else 2) := by
  intro l h3
  have hrk : (sertables.tableD l).rank = l := rfl
  have h2l : 2 ≤ l := Nat.le_of_succ_le h3
  have hll : l - 2 + 2 = l := ground.subAdd h2l
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [cvee_len (sertables.tableD l), hrk, ground.length_mapRange]
  · intro i hi
    rw [cvee_len (sertables.tableD l), hrk] at hi
    rw [mapRange_read 0 _ l i hi, cvee_entry (sertables.tableD l) i hi,
      thetaD_read l i h3 hi,
      show (sertables.tableD l).lenNums = List.replicate l 2 from rfl,
      ground.getAt_replicate 0 2 l i hi,
      show (sertables.tableD l).lenDen = 1 from rfl]
    match i, hi with
    | 0, _ =>
      have hnz : ¬ (l - 2 ≤ 0) := by
        intro hle
        rw [← hll] at h3
        exact absurd (Nat.le_trans h3
          (Nat.succ_le_succ (Nat.succ_le_succ hle))) (Nat.lt_irrefl 2)
      rw [decide_eq_false hnz]
      show (1 + ((0 + 0) + 0)) * 2 / (2 * 1) = 1
      exact rfl
    | j + 1, hj =>
      by_cases hA : l ≤ j + 1 + 2
      · have hle2 : l - 2 ≤ j + 1 := by
          rw [← hll] at hA
          exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ hA)
        have hnb : ¬ (j + 1 < l - 2) := fun hlt =>
          Nat.lt_irrefl (j + 1) (Nat.lt_of_lt_of_le hlt hle2)
        rw [decide_eq_false hnb, decide_eq_true hle2,
          decide_eq_true hj, if_pos hA]
        show (0 + ((0 + 0) + 1)) * 2 / (2 * 1) = 1
        exact rfl
      · have hgt : j + 1 + 2 < l := Nat.lt_of_not_le hA
        have hsub : j + 1 < l - 2 := by
          rw [← hll] at hgt
          exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hgt)
        have hnle : ¬ (l - 2 ≤ j + 1) := fun hle =>
          Nat.lt_irrefl (j + 1) (Nat.lt_of_lt_of_le hsub hle)
        rw [decide_eq_true hsub, decide_eq_false hnle, if_neg hA]
        show (0 + ((1 + 1) + 0)) * 2 / (2 * 1) = 2
        exact rfl

/-- A sorted word reads at or below its entry at any earlier
key. -/
private theorem descMono (W : List Nat)
    (hs : ∀ i, ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) (s : Nat) :
    ∀ k, ground.getAt 0 W (s + k) ≤ ground.getAt 0 W s
  | 0 => Nat.le_refl _
  | k + 1 => Nat.le_trans (hs (s + k)) (descMono W hs s k)

/-- The sorted word's consecutive gaps telescope from a stated
key: the collected gaps are the outer gap. -/
private theorem tele (W : List Nat)
    (hs : ∀ i, ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) (s : Nat) :
    ∀ k, ground.famFold Nat.add 0
      (fun j => ground.getAt 0 W (s + j) - ground.getAt 0 W (s + j + 1))
      (List.range k) = ground.getAt 0 W s - ground.getAt 0 W (s + k)
  | 0 => (Nat.sub_self _).symm
  | k + 1 => by
    rw [ground.range_succ k,
      ground.famFold_append Nat.add 0 Nat.add_assoc Nat.zero_add _
        (List.range k) [k]]
    show ground.famFold Nat.add 0
        (fun j => ground.getAt 0 W (s + j) - ground.getAt 0 W (s + j + 1))
        (List.range k)
        + ((ground.getAt 0 W (s + k) - ground.getAt 0 W (s + k + 1)) + 0)
      = ground.getAt 0 W s - ground.getAt 0 W (s + (k + 1))
    rw [Nat.add_zero, tele W hs s k]
    exact ground.subJoin (hs (s + k)) (descMono W hs s k)

/-- The gap telescope from the head key. -/
private theorem tele0 (W : List Nat)
    (hs : ∀ i, ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) (k : Nat) :
    ground.famFold Nat.add 0
      (fun j => ground.getAt 0 W j - ground.getAt 0 W (j + 1))
      (List.range k) = ground.getAt 0 W 0 - ground.getAt 0 W k := by
  rw [ground.famFold_congr_all Nat.add 0
      (fun j => ground.getAt 0 W j - ground.getAt 0 W (j + 1))
      (fun j => ground.getAt 0 W (0 + j) - ground.getAt 0 W (0 + j + 1))
      (fun j => by rw [Nat.zero_add]) (List.range k),
    tele W hs 0 k, Nat.zero_add]

/-- A range fold splits off its head key. -/
private theorem rangePeel (F : Nat → Nat) (n : Nat) :
    ground.famFold Nat.add 0 F (List.range (n + 1))
      = F 0 + ground.famFold Nat.add 0 (fun j => F (j + 1))
          (List.range n) := by
  rw [ground.range_cons n]
  show F 0 + ground.famFold Nat.add 0 F
      ((List.range n).map (fun j => j + 1))
    = F 0 + ground.famFold Nat.add 0 (fun j => F (j + 1)) (List.range n)
  rw [ground.famFold_map Nat.add 0 F (fun j => j + 1)]

/-- The key at a member, read as a range fold of the word's gaps
against the halved summands. -/
private theorem grade_index (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) :
    grade t (serstable.member W l)
      = ground.famFold Nat.add 0
          (fun i => (ground.getAt 0 W i - ground.getAt 0 W (i + 1))
            * ground.getAt 0 (cvee t) i) (List.range l) := by
  show ground.dotNat (serstable.member W l) (cvee t) = _
  rw [ground.dotNat_index (serstable.member W l) (cvee t)
      (by rw [cvee_len t, hrk, serstable.memberLen]),
    serstable.memberLen W l]
  exact ground.famFold_congr_range _ _ l
    (fun i hi => by rw [serstable.memberEntry W l i hi])

/-- The vacant word's member reads the key at the sum's unit. -/
private theorem grade_vanish (t : gentable.Table) (W : List Nat) (l : Nat)
    (hrk : t.rank = l) (hz : ∀ k, ground.getAt 0 W k = 0) :
    grade t (serstable.member W l) = 0 := by
  rw [grade_index t W l hrk]
  exact ground.famFold_zero _
    (fun i => by rw [hz i, hz (i + 1)]; exact Nat.zero_mul _)
    (List.range l)

/-- The `B` key at a member, the closed form's weights in the
fold. -/
private theorem grade_indexB (W : List Nat) (m : Nat) :
    grade (sertables.tableB (m + 2)) (serstable.member W (m + 2))
      = ground.famFold Nat.add 0
          (fun i => (ground.getAt 0 W i - ground.getAt 0 W (i + 1))
            * (if i == 0 then 1 else if i + 1 == m + 2 then 1 else 2))
          (List.range (m + 2)) := by
  rw [grade_index (sertables.tableB (m + 2)) W (m + 2) rfl,
    cvee_B (m + 2) (Nat.le_add_left 2 m)]
  exact ground.famFold_congr_range _ _ (m + 2)
    (fun i hi => by rw [mapRange_read 0 _ (m + 2) i hi])

/-- The `D` key at a member, the closed form's weights in the
fold. -/
private theorem grade_indexD (W : List Nat) (m : Nat) :
    grade (sertables.tableD (m + 3)) (serstable.member W (m + 3))
      = ground.famFold Nat.add 0
          (fun i => (ground.getAt 0 W i - ground.getAt 0 W (i + 1))
            * (if i == 0 then 1 else if m + 3 ≤ i + 2 then 1 else 2))
          (List.range (m + 3)) := by
  rw [grade_index (sertables.tableD (m + 3)) W (m + 3) rfl,
    cvee_D (m + 3) (Nat.le_add_left 3 m)]
  exact ground.famFold_congr_range _ _ (m + 3)
    (fun i hi => by rw [mapRange_read 0 _ (m + 3) i hi])

/-- The two consecutive-gap keys' arithmetic close: the peeled
head against the doubled telescope and the kept tail. -/
private theorem keyJoin {a b c : Nat} (hcb : c ≤ b) (hba : b ≤ a) :
    (a - b) * 1 + ((b - c) * 2 + (c - 0) * 1) = a + b - c := by
  refine ground.addCancelR c ?_
  rw [Nat.mul_one, Nat.mul_one, Nat.sub_zero, Nat.mul_two,
    Nat.add_assoc (b - c) (b - c) c, ground.subAdd hcb,
    ground.subAdd (Nat.le_trans hcb (Nat.le_add_left b a)),
    ← Nat.add_assoc (a - b) (b - c) b, ground.subJoin hcb hba,
    Nat.add_assoc (a - c) b c, Nat.add_comm b c,
    ← Nat.add_assoc (a - c) c b, ground.subAdd (Nat.le_trans hcb hba)]

/-- The close at two kept tail gaps, the `D` shape. -/
private theorem keyJoinD {a b c d : Nat} (hdc : d ≤ c) (hcb : c ≤ b)
    (hba : b ≤ a) :
    (a - b) * 1 + (((b - c) * 2 + (c - d) * 1) + (d - 0) * 1)
      = a + b - c := by
  rw [Nat.add_assoc ((b - c) * 2) ((c - d) * 1) ((d - 0) * 1)]
  have hcd : (c - d) * 1 + (d - 0) * 1 = (c - 0) * 1 := by
    rw [Nat.mul_one, Nat.mul_one, Nat.mul_one, Nat.sub_zero,
      Nat.sub_zero, ground.subAdd hdc]
  rw [hcd]
  exact keyJoin hcb hba

/-- The key at a leading word's member: the top pair's sum with
the last coordinate withdrawn, the coroot presentation's telescope
at the sorted word (`lem:corner`'s sorted-coordinate key reads). -/
theorem grade_member_B : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length ≤ l →
    grade (sertables.tableB l) (serstable.member W l)
      = ground.getAt 0 W 0 + ground.getAt 0 W 1
        - ground.getAt 0 W (l - 1) := by
  intro W l hW hcl
  have hs := ground.sortedAll W hW
  match l, hcl with
  | 0, hcl =>
    have hz : ∀ k, ground.getAt 0 W k = 0 := fun k =>
      ground.getAt_over 0 W k (Nat.le_trans hcl (Nat.zero_le k))
    rw [grade_vanish (sertables.tableB 0) W 0 rfl hz, hz 0, hz 1]
  | 1, hcl =>
    have hz1 : ∀ k, 1 ≤ k → ground.getAt 0 W k = 0 := fun k hk =>
      ground.getAt_over 0 W k (Nat.le_trans hcl hk)
    have hc1 : cvee (sertables.tableB 1) = [0] := by decide
    show ground.dotNat (serstable.member W 1)
      (cvee (sertables.tableB 1)) = _
    rw [hc1, hz1 1 (Nat.le_refl 1)]
    show (ground.getAt 0 W 0 - ground.getAt 0 W 1) * 0 + 0
      = ground.getAt 0 W 0 + 0 - ground.getAt 0 W (1 - 1)
    rw [Nat.mul_zero (ground.getAt 0 W 0 - ground.getAt 0 W 1)]
    show (0 : Nat) = ground.getAt 0 W 0 - ground.getAt 0 W 0
    exact (Nat.sub_self _).symm
  | m + 2, hcl =>
    have hzk : ∀ k, m + 2 ≤ k → ground.getAt 0 W k = 0 := fun k hk =>
      ground.getAt_over 0 W k (Nat.le_trans hcl hk)
    have hmid : ground.famFold Nat.add 0
        (fun j => (ground.getAt 0 W (j + 1)
              - ground.getAt 0 W (j + 1 + 1))
            * (if j + 1 == 0 then 1
              else if j + 1 + 1 == m + 2 then 1 else 2))
        (List.range m)
      = ground.famFold Nat.add 0
        (fun j => (ground.getAt 0 W (1 + j)
          - ground.getAt 0 W (1 + j + 1)) * 2) (List.range m) :=
      ground.famFold_congr_range _ _ m (fun j hjm => by
        have hne : ¬ (j + 1 + 1 = m + 2) := by
          intro he
          have hj2 : j = m := Nat.succ.inj (Nat.succ.inj he)
          rw [hj2] at hjm
          exact Nat.lt_irrefl m hjm
        rw [ground.neBeqOf hne, Nat.add_comm 1 j]
        exact rfl)
    have hgm : (ground.getAt 0 W (m + 1)
          - ground.getAt 0 W (m + 1 + 1))
        * (if m + 1 == 0 then 1
          else if m + 1 + 1 == m + 2 then 1 else 2)
      = (ground.getAt 0 W (m + 1) - 0) * 1 := by
      rw [ground.neBeqOf (fun h : m + 1 = 0 => Nat.noConfusion h),
        ground.eqBeqOf (rfl : m + 1 + 1 = m + 2),
        hzk (m + 1 + 1) (Nat.le_refl (m + 2))]
      exact rfl
    have hcb : ground.getAt 0 W (m + 1) ≤ ground.getAt 0 W 1 := by
      rw [Nat.add_comm m 1]
      exact descMono W hs 1 m
    rw [grade_indexB W m, rangePeel _ (m + 1), ground.range_succ m,
      ground.famFold_snoc _ (List.range m) m, hmid,
      ground.famFold_mulR 2 _ (List.range m), tele W hs 1 m, hgm,
      Nat.add_comm 1 m]
    show (ground.getAt 0 W 0 - ground.getAt 0 W 1) * 1
        + ((ground.getAt 0 W 1 - ground.getAt 0 W (m + 1)) * 2
          + (ground.getAt 0 W (m + 1) - 0) * 1)
      = ground.getAt 0 W 0 + ground.getAt 0 W 1
        - ground.getAt 0 W (m + 1)
    exact keyJoin hcb (hs 0)

/-- The key at a leading word's member: the top coordinate, the
coroot presentation's telescope at the sorted word (`lem:corner`'s
sorted-coordinate key reads). -/
theorem grade_member_C : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length ≤ l →
    grade (sertables.tableC l) (serstable.member W l)
      = ground.getAt 0 W 0 := by
  intro W l hW hcl
  have hs := ground.sortedAll W hW
  have hzl : ground.getAt 0 W l = 0 := ground.getAt_over 0 W l hcl
  have hcong : ground.famFold Nat.add 0
      (fun i => (ground.getAt 0 W i - ground.getAt 0 W (i + 1))
        * ground.getAt 0 (List.replicate l 1) i) (List.range l)
    = ground.famFold Nat.add 0
      (fun i => ground.getAt 0 W i - ground.getAt 0 W (i + 1))
      (List.range l) :=
    ground.famFold_congr_range _ _ l (fun i hi => by
      rw [ground.getAt_replicate 0 1 l i hi, Nat.mul_one])
  rw [grade_index (sertables.tableC l) W l rfl, cvee_C l, hcong,
    tele0 W hs l, hzl, Nat.sub_zero]

/-- The key at a leading word's member: the top pair's sum with
the next-to-last coordinate withdrawn, the coroot presentation's
telescope at the sorted word (`lem:corner`'s sorted-coordinate key
reads). -/
theorem grade_member_D : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length ≤ l → 2 ≤ l →
    grade (sertables.tableD l) (serstable.member W l)
      = ground.getAt 0 W 0 + ground.getAt 0 W 1
        - ground.getAt 0 W (l - 2) := by
  intro W l hW hcl hrk
  have hs := ground.sortedAll W hW
  match l, hcl, hrk with
  | 0, _, hrk => exact absurd hrk (Nat.not_succ_le_zero 1)
  | 1, _, hrk =>
    exact absurd (Nat.le_of_succ_le_succ hrk) (Nat.not_succ_le_zero 0)
  | 2, hcl, _ =>
    have hz2 : ∀ k, 2 ≤ k → ground.getAt 0 W k = 0 := fun k hk =>
      ground.getAt_over 0 W k (Nat.le_trans hcl hk)
    have hc2 : cvee (sertables.tableD 2) = [0, 1] := by decide
    show ground.dotNat (serstable.member W 2)
      (cvee (sertables.tableD 2)) = _
    rw [hc2]
    show (ground.getAt 0 W 0 - ground.getAt 0 W 1) * 0
        + ((ground.getAt 0 W 1 - ground.getAt 0 W 2) * 1 + 0)
      = ground.getAt 0 W 0 + ground.getAt 0 W 1
        - ground.getAt 0 W 0
    rw [hz2 2 (Nat.le_refl 2),
      Nat.mul_zero (ground.getAt 0 W 0 - ground.getAt 0 W 1),
      Nat.mul_one, Nat.sub_zero, Nat.add_zero, Nat.zero_add]
    exact (ground.addSubSelfL _ _).symm
  | m + 3, hcl, _ =>
    have hzk : ∀ k, m + 3 ≤ k → ground.getAt 0 W k = 0 := fun k hk =>
      ground.getAt_over 0 W k (Nat.le_trans hcl hk)
    have hmid : ground.famFold Nat.add 0
        (fun j => (ground.getAt 0 W (j + 1)
              - ground.getAt 0 W (j + 1 + 1))
            * (if j + 1 == 0 then 1
              else if m + 3 ≤ j + 1 + 2 then 1 else 2))
        (List.range m)
      = ground.famFold Nat.add 0
        (fun j => (ground.getAt 0 W (1 + j)
          - ground.getAt 0 W (1 + j + 1)) * 2) (List.range m) :=
      ground.famFold_congr_range _ _ m (fun j hjm => by
        have hne : ¬ (m + 3 ≤ j + 1 + 2) := by
          intro hle
          have hmj : m ≤ j :=
            Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
              (Nat.le_of_succ_le_succ hle))
          exact Nat.lt_irrefl j (Nat.lt_of_lt_of_le hjm hmj)
        rw [if_neg hne, Nat.add_comm 1 j]
        exact rfl)
    have hgm : (ground.getAt 0 W (m + 1)
          - ground.getAt 0 W (m + 1 + 1))
        * (if m + 1 == 0 then 1
          else if m + 3 ≤ m + 1 + 2 then 1 else 2)
      = (ground.getAt 0 W (m + 1)
          - ground.getAt 0 W (m + 1 + 1)) * 1 := by
      rw [ground.neBeqOf (fun h : m + 1 = 0 => Nat.noConfusion h),
        if_pos (Nat.le_refl (m + 3))]
      exact rfl
    have hgm1 : (ground.getAt 0 W (m + 1 + 1)
          - ground.getAt 0 W (m + 1 + 1 + 1))
        * (if m + 1 + 1 == 0 then 1
          else if m + 3 ≤ m + 1 + 1 + 2 then 1 else 2)
      = (ground.getAt 0 W (m + 1 + 1) - 0) * 1 := by
      rw [ground.neBeqOf (fun h : m + 1 + 1 = 0 => Nat.noConfusion h),
        if_pos (Nat.le_succ (m + 3)),
        hzk (m + 1 + 1 + 1) (Nat.le_refl (m + 3))]
      exact rfl
    have hcb : ground.getAt 0 W (m + 1) ≤ ground.getAt 0 W 1 := by
      rw [Nat.add_comm m 1]
      exact descMono W hs 1 m
    rw [grade_indexD W m, rangePeel _ (m + 2), ground.range_succ (m + 1),
      ground.famFold_snoc _ (List.range (m + 1)) (m + 1),
      ground.range_succ m, ground.famFold_snoc _ (List.range m) m,
      hmid, ground.famFold_mulR 2 _ (List.range m), tele W hs 1 m,
      hgm, hgm1, Nat.add_comm 1 m]
    show (ground.getAt 0 W 0 - ground.getAt 0 W 1) * 1
        + (((ground.getAt 0 W 1 - ground.getAt 0 W (m + 1)) * 2
            + (ground.getAt 0 W (m + 1)
              - ground.getAt 0 W (m + 1 + 1)) * 1)
          + (ground.getAt 0 W (m + 1 + 1) - 0) * 1)
      = ground.getAt 0 W 0 + ground.getAt 0 W 1
        - ground.getAt 0 W (m + 1)
    exact keyJoinD (hs (m + 1)) hcb (hs 0)

/-- A join's leading part at the first side's count is that
side. -/
private theorem takeLen : ∀ (u v : List Nat),
    List.take u.length (u ++ v) = u
  | [], _ => rfl
  | a :: u, v => congrArg (List.cons a) (takeLen u v)

/-- The `A` key at a shape split off its last member: the
prefix's total. -/
private theorem gradeA_snoc (s : places.Shape) (x : Nat) :
    gradeA (s ++ [x]) = ground.sumNat s := by
  show ground.sumNat (List.take ((s ++ [x]).length - 1) (s ++ [x]))
    = ground.sumNat s
  rw [ground.length_append s [x]]
  show ground.sumNat (List.take s.length (s ++ [x])) = ground.sumNat s
  rw [takeLen s [x]]

/-- The full columns join at the split-off last member. -/
private theorem addFullsSnoc (m : Nat) (s : places.Shape) (x : Nat) :
    labels.addFulls m (s ++ [x]) = s ++ [x + m] := by
  show (match (s ++ [x]).reverse with
    | [] => []
    | a :: t => ((a + m) :: t).reverse) = s ++ [x + m]
  rw [ground.reverse_snoc s x]
  show ((x + m) :: s.reverse).reverse = s ++ [x + m]
  rw [ground.reverse_cons (x + m) s.reverse, ground.reverse_reverse s]

/-- The full-column key's occupancy moves off the read: one value
per label. -/
theorem gradeA_fulls : ∀ (m : Nat) (s : places.Shape),
    gradeA (labels.addFulls m s) = gradeA s
  | _, [] => rfl
  | m, x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hsq, _⟩ =>
      rw [hsq, addFullsSnoc m s' a, gradeA_snoc s' (a + m),
        gradeA_snoc s' a]

/-- The reduction keeps the key, the same read. -/
theorem gradeA_reduce : ∀ s : places.Shape,
    gradeA (labels.reduce s) = gradeA s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hsq, _⟩ =>
      rw [hsq, labels.reduce_snoc s' a, gradeA_snoc s' 0,
        gradeA_snoc s' a]

/-! `lem:corner`'s move cap: a `θ` content is the unit content or a
root with its balance partner (`prop:row`'s list), and the join
`ν + Σ d_i α_i = θ` prices the key read `ν(θ^∨)` against `θ`'s
dominant reads at the halved products and the norm `⟨θ,θ⟩ = 2`, so
the key moves by at most two under adjoint fusion. -/

/-- `θ`'s dominant reads: every simple coroot pair of the highest
root's fold at or beyond the unit (`lem:corner`'s move cap at
`lem:tops`(ii)'s reads, data at the table). -/
def thetaDomRead (t : gentable.Table) : Prop :=
  ((List.range t.rank).all (fun j =>
    if BPair.unit ≤ gentable.corootAt t t.thetaFold j then true
    else false)) = true

instance (t : gentable.Table) : Decidable (thetaDomRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The dominance join at the top: every positive fold at or below
the highest root's, componentwise — the join `ν + Σ d_i α_i = θ`'s
witness data (`lem:corner`'s move cap). -/
def thetaTopRead (t : gentable.Table) : Prop :=
  (t.posFolds.all (fun f =>
    (List.range t.rank).all (fun i =>
      ground.getAt 0 f i ≤ ground.getAt 0 t.thetaFold i))) = true

instance (t : gentable.Table) : Decidable (thetaTopRead t) :=
  inferInstanceAs (Decidable (_ = _))

/-- A zipped family at matched counts is the keyed family's map:
the two families' entries read at every key below the count. -/
private theorem zipRange {α β γ : Type} (da : α) (db : β)
    (F : α → β → γ) :
    ∀ (n : Nat) (u : List α) (v : List β),
      u.length = n → v.length = n →
      List.zipWith F u v
        = (List.range n).map (fun i =>
            F (ground.getAt da u i) (ground.getAt db v i))
  | 0, [], [], _, _ => rfl
  | 0, _ :: _, _, hu, _ => Nat.noConfusion hu
  | 0, [], _ :: _, _, hv => Nat.noConfusion hv
  | _ + 1, [], _, hu, _ => Nat.noConfusion hu
  | _ + 1, _ :: _, [], _, hv => Nat.noConfusion hv
  | n + 1, a :: u, b :: v, hu, hv => by
    rw [ground.range_cons n]
    show F a b :: List.zipWith F u v
      = F a b :: ((List.range n).map (fun j => j + 1)).map
          (fun i => F (ground.getAt da (a :: u) i)
            (ground.getAt db (b :: v) i))
    rw [ground.map_map]
    show F a b :: List.zipWith F u v
      = F a b :: (List.range n).map
          (fun j => F (ground.getAt da u j) (ground.getAt db v j))
    rw [zipRange da db F n u v (Nat.succ.inj hu) (Nat.succ.inj hv)]

/-- The balance fold scales through its members. -/
private theorem bsumMulR (F : Nat → BPair) (c : BPair) :
    ∀ l : List Nat,
      (ground.bsum F l * c).oneValue (ground.bsum (fun i => F i * c) l)
  | [] => BPair.unit_mul c
  | a :: l => by
    show ((F a + ground.bsum F l) * c).oneValue
      (F a * c + ground.bsum (fun i => F i * c) l)
    rw [BPair.right_distrib]
    exact BPair.add_congr (BPair.oneValue_refl _) (bsumMulR F c l)

/-- The matched-list clause's four reads at the key count. -/
private theorem shapeAt (t : gentable.Table) (hs : gentable.shapeRead t) :
    t.cartan.length = t.rank ∧ t.thetaFold.length = t.rank
      ∧ (t.cartan.all (fun row => row.length == t.rank)) = true
      ∧ (t.posFolds.all (fun f => f.length == t.rank)) = true := by
  have s1 := ground.andSplitB hs
  have s2 := ground.andSplitB s1.1
  have s3 := ground.andSplitB s2.1
  have s4 := ground.andSplitB s3.1
  exact ⟨ground.beqEqOf s4.2, ground.beqEqOf s2.2, s3.2, s1.2⟩

/-- A Cartan row is one entry per key. -/
private theorem cartanRow_len (t : gentable.Table)
    (hs : gentable.shapeRead t) (i : Nat) (hi : i < t.rank) :
    (ground.getAt ([] : List BPair) t.cartan i).length = t.rank :=
  ground.beqEqOf (ground.all_getAt ([] : List BPair) t.cartan
    (shapeAt t hs).2.2.1 i (by rw [(shapeAt t hs).1]; exact hi))

/-- A positive member's fold is one entry per key. -/
private theorem posRow_len (t : gentable.Table)
    (hs : gentable.shapeRead t) (j : Nat) (hj : j < t.posFolds.length) :
    (ground.getAt ([] : List Nat) t.posFolds j).length = t.rank :=
  ground.beqEqOf (ground.all_getAt ([] : List Nat) t.posFolds
    (shapeAt t hs).2.2.2 j hj)

/-- The halved summands' coroot list is one entry per key. -/
private theorem natVcvee_len (t : gentable.Table) :
    (memberdata.natV (cvee t)).length = t.rank :=
  (ground.length_map BPair.ofNat (cvee t)).trans (cvee_len t)

/-- The form's symmetry at a key pair, extracted from the stated
fold: the halved products' two reads. -/
private theorem symRead_at (t : gentable.Table)
    (h : gentable.symRead t) (i j : Nat) (hi : i < t.rank)
    (hj : j < t.rank) :
    (ground.getAt BPair.unit (ground.getAt ([] : List BPair) t.cartan i) j
        * BPair.ofNat (ground.getAt 0 t.lenNums j)).oneValue
      (ground.getAt BPair.unit (ground.getAt ([] : List BPair) t.cartan j) i
        * BPair.ofNat (ground.getAt 0 t.lenNums i)) := by
  have h1 := ground.all_range_read t.rank h i hi
  have h2 := ground.all_range_read t.rank h1 j hj
  by_cases hp : (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) t.cartan i) j
      * BPair.ofNat (ground.getAt 0 t.lenNums j)).oneValue
    (ground.getAt BPair.unit
        (ground.getAt ([] : List BPair) t.cartan j) i
      * BPair.ofNat (ground.getAt 0 t.lenNums i))
  · exact hp
  · rw [if_neg hp] at h2
    exact Bool.noConfusion h2

/-- The highest root's dominant read at a key, extracted from the
stated fold. -/
private theorem thetaDom_at (t : gentable.Table) (h : thetaDomRead t)
    (j : Nat) (hj : j < t.rank) :
    BPair.unit ≤ gentable.corootAt t t.thetaFold j := by
  have h1 := ground.all_range_read t.rank h j hj
  by_cases hp : BPair.unit ≤ gentable.corootAt t t.thetaFold j
  · exact hp
  · rw [if_neg hp] at h1
    exact Bool.noConfusion h1

/-- The dominance join's componentwise read at a positive member's
key, extracted from the stated fold. -/
private theorem thetaTop_at (t : gentable.Table) (h : thetaTopRead t)
    (j : Nat) (hj : j < t.posFolds.length) (i : Nat) (hi : i < t.rank) :
    ground.getAt 0 (ground.getAt ([] : List Nat) t.posFolds j) i
      ≤ ground.getAt 0 t.thetaFold i :=
  of_decide_eq_true (ground.all_range_read t.rank
    (ground.all_getAt ([] : List Nat) t.posFolds h j hj) i hi)

/-- The key's row read: a Cartan row against the halved summands. -/
private def rowKey (t : gentable.Table) (i : Nat) : BPair :=
  gradeV t (ground.getAt ([] : List BPair) t.cartan i)

/-- The key's fold at a natural fold: the fold's coefficients
against the rows' key reads, one member per simple key. -/
private def foldKey (t : gentable.Table) (g : List Nat) : BPair :=
  ground.bsum (fun i => BPair.ofNat (ground.getAt 0 g i) * rowKey t i)
    (List.range t.rank)

/-- A fold's coroot read at a key as the key fold of the Cartan
column's weighted entries. -/
private theorem corootBsum (t : gentable.Table)
    (hcl : t.cartan.length = t.rank) (g : List Nat)
    (hg : g.length = t.rank) (i : Nat) :
    (gentable.corootAt t g i).oneValue
      (ground.bsum (fun k => BPair.ofNat (ground.getAt 0 g k)
        * ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) t.cartan k) i)
        (List.range t.rank)) := by
  show (BPair.sum (List.zipWith (fun c row =>
      BPair.ofNat c * ground.getAt BPair.unit row i) g t.cartan)).oneValue _
  rw [zipRange (0 : Nat) ([] : List BPair) _ t.rank g t.cartan hg hcl]
  exact BPair.sum_map _ (List.range t.rank)

/-- The row key's cleared read: scaled by the halved second member
the row key is the highest root's coroot pair at the row's key,
weighted by that key's length — the form's symmetry at the halved
products (`lem:corner`; `con:gentable`). -/
private theorem rowKey_scale (t : gentable.Table)
    (hs : gentable.shapeRead t) (hsym : gentable.symRead t)
    (hc : cveeRead t) (i : Nat) (hi : i < t.rank) :
    (rowKey t i * BPair.ofNat (2 * t.lenDen)).oneValue
      (gentable.corootAt t t.thetaFold i
        * BPair.ofNat (ground.getAt 0 t.lenNums i)) := by
  have hrow : rowKey t i
      = ground.bsum (fun k =>
          ground.getAt BPair.unit
              (ground.getAt ([] : List BPair) t.cartan i) k
            * ground.getAt BPair.unit (memberdata.natV (cvee t)) k)
          (List.range t.rank) :=
    elim.dotP_fold t.rank (ground.getAt ([] : List BPair) t.cartan i)
      (memberdata.natV (cvee t)) (cartanRow_len t hs i hi) (natVcvee_len t)
  have hstep : ∀ k, 0 < ground.countOf k (List.range t.rank) →
      ((ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) t.cartan i) k
          * ground.getAt BPair.unit (memberdata.natV (cvee t)) k)
        * BPair.ofNat (2 * t.lenDen)).oneValue
      (BPair.ofNat (ground.getAt 0 t.thetaFold k)
          * ground.getAt BPair.unit
              (ground.getAt ([] : List BPair) t.cartan k) i
        * BPair.ofNat (ground.getAt 0 t.lenNums i)) := by
    intro k hk
    have hkr : k < t.rank := ground.ltOfMem hk
    have hxk : ground.getAt BPair.unit (memberdata.natV (cvee t)) k
        = BPair.ofNat (ground.getAt 0 (cvee t) k) :=
      ground.getAt_map 0 BPair.unit BPair.ofNat (cvee t) k
        (by rw [cvee_len t]; exact hkr)
    have e1 : (BPair.ofNat (ground.getAt 0 (cvee t) k)
        * BPair.ofNat (2 * t.lenDen)).oneValue
        (BPair.ofNat (ground.getAt 0 t.thetaFold k)
          * BPair.ofNat (ground.getAt 0 t.lenNums k)) := by
      refine BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.ofNat_mul _ _)) ?_
      rw [cveeRead_mul t hc k hkr]
      exact BPair.ofNat_mul _ _
    rw [hxk, BPair.mul_assoc]
    refine BPair.oneValue_trans
      (BPair.mul_congr (BPair.oneValue_refl _) e1) ?_
    rw [BPair.mul_left_comm
        (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) t.cartan i) k)
        (BPair.ofNat (ground.getAt 0 t.thetaFold k))
        (BPair.ofNat (ground.getAt 0 t.lenNums k)),
      BPair.mul_assoc (BPair.ofNat (ground.getAt 0 t.thetaFold k))
        (ground.getAt BPair.unit
          (ground.getAt ([] : List BPair) t.cartan k) i)
        (BPair.ofNat (ground.getAt 0 t.lenNums i))]
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (symRead_at t hsym i k hi hkr)
  rw [hrow]
  refine BPair.oneValue_trans
    (bsumMulR _ (BPair.ofNat (2 * t.lenDen)) (List.range t.rank)) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _ _ (List.range t.rank) hstep) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (bsumMulR
      (fun k => BPair.ofNat (ground.getAt 0 t.thetaFold k)
        * ground.getAt BPair.unit
            (ground.getAt ([] : List BPair) t.cartan k) i)
      (BPair.ofNat (ground.getAt 0 t.lenNums i)) (List.range t.rank))) ?_
  exact BPair.mul_congr
    (BPair.oneValue_symm (corootBsum t (shapeAt t hs).1 t.thetaFold
      (shapeAt t hs).2.1 i))
    (BPair.oneValue_refl _)

/-- An occupied count sits strictly above the sum's unit. -/
private theorem unitLtNat : ∀ n : Nat, 0 < n →
    BPair.unit < BPair.ofNat n
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, _ => ground.unitLtOfPos (ground.posOfSucc n)

/-- The halved second member is occupied at an occupied key count:
a vacant divisor truncates the first halved summand off its stated
occupancy. -/
private theorem denPos (t : gentable.Table) (hc : cveeRead t)
    (hr : 0 < t.rank) : 0 < 2 * t.lenDen := by
  match Nat.eq_zero_or_pos (2 * t.lenDen) with
  | Or.inr h => exact h
  | Or.inl h0 =>
    have h1 : 1 ≤ ground.getAt 0 (cvee t) 0 := cveeRead_pos t hc 0 hr
    have h2 : ground.getAt 0 (cvee t) 0 = 0 := by
      rw [cvee_entry t 0 hr, h0]
      exact divZeroN _
    rw [h2] at h1
    exact absurd h1 (Nat.not_succ_le_zero 0)

/-- Every row key sits at or beyond the sum's unit: the cleared
read is a product of `θ`'s dominant pair with a count. -/
private theorem rowKey_unit (t : gentable.Table)
    (hs : gentable.shapeRead t) (hsym : gentable.symRead t)
    (hc : cveeRead t) (hdom : thetaDomRead t) (i : Nat)
    (hi : i < t.rank) : BPair.unit ≤ rowKey t i := by
  have h1 : BPair.unit ≤ rowKey t i * BPair.ofNat (2 * t.lenDen) :=
    ground.leB_congr_right
      (BPair.oneValue_symm (rowKey_scale t hs hsym hc i hi))
      (ground.unitLeMul (thetaDom_at t hdom i hi) (ground.unitLeOfNat _))
  refine ground.leB_unscale
    (unitLtNat _ (denPos t hc (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) ?_
  exact ground.leB_congr_left (BPair.oneValue_symm (BPair.unit_mul _)) h1

/-- The key fold at any natural fold sits at or beyond the sum's
unit. -/
private theorem foldKey_unit (t : gentable.Table)
    (hs : gentable.shapeRead t) (hsym : gentable.symRead t)
    (hc : cveeRead t) (hdom : thetaDomRead t) (g : List Nat) :
    BPair.unit ≤ foldKey t g :=
  ground.foldB_nonneg _ (List.range t.rank) (fun k hk =>
    ground.unitLeMul (ground.unitLeOfNat _)
      (rowKey_unit t hs hsym hc hdom k (ground.ltOfMem hk)))

/-- A fold at or below the highest root's reads its key fold at or
below the top's, key by key. -/
private theorem foldKey_mono (t : gentable.Table)
    (hs : gentable.shapeRead t) (hsym : gentable.symRead t)
    (hc : cveeRead t) (hdom : thetaDomRead t) (g : List Nat)
    (hle : ∀ i, i < t.rank →
      ground.getAt 0 g i ≤ ground.getAt 0 t.thetaFold i) :
    foldKey t g ≤ foldKey t t.thetaFold :=
  ground.bsum_le _ _ (List.range t.rank) (fun k hk => by
    have hkr : k < t.rank := ground.ltOfMem hk
    rw [BPair.mul_comm (BPair.ofNat (ground.getAt 0 g k)) (rowKey t k),
      BPair.mul_comm (BPair.ofNat (ground.getAt 0 t.thetaFold k))
        (rowKey t k)]
    exact ground.leB_mulR (rowKey_unit t hs hsym hc hdom k hkr)
      (ground.leB_ofNat (hle k hkr)))

/-- The top's key fold at the cleared scale is the highest root's
norm: the form fold's own read at `⟨θ,θ⟩ = 2`. -/
private theorem foldKey_top (t : gentable.Table)
    (hs : gentable.shapeRead t) (hsym : gentable.symRead t)
    (hc : cveeRead t) (hnorm : gentable.thetaNormRead t) :
    (foldKey t t.thetaFold * BPair.ofNat (2 * t.lenDen)).oneValue
      (BPair.ofNat (4 * t.lenDen)) := by
  refine BPair.oneValue_trans
    (bsumMulR _ (BPair.ofNat (2 * t.lenDen)) (List.range t.rank)) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun j => BPair.ofNat (ground.getAt 0 t.thetaFold j)
        * gentable.corootAt t t.thetaFold j
        * BPair.ofNat (ground.getAt 0 t.lenNums j))
      (List.range t.rank) ?_) ?_
  · intro k hk
    have hkr : k < t.rank := ground.ltOfMem hk
    rw [BPair.mul_assoc (BPair.ofNat (ground.getAt 0 t.thetaFold k))
        (rowKey t k) (BPair.ofNat (2 * t.lenDen)),
      BPair.mul_assoc (BPair.ofNat (ground.getAt 0 t.thetaFold k))
        (gentable.corootAt t t.thetaFold k)
        (BPair.ofNat (ground.getAt 0 t.lenNums k))]
    exact BPair.mul_congr (BPair.oneValue_refl _)
      (rowKey_scale t hs hsym hc k hkr)
  · exact BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.sum_map _ (List.range t.rank))) hnorm

/-- A positive root's key read sits in `[0, 2]`: the fold's
`θ`-pairing at the join against `θ`'s dominant reads, the norm the
upper wall (`lem:corner`'s move cap). -/
theorem posGrade_cap : ∀ (t : gentable.Table) (j : Nat),
    gentable.shapeRead t → gentable.symRead t →
    gentable.thetaNormRead t → cveeRead t →
    thetaDomRead t → thetaTopRead t → j < t.posFolds.length →
    BPair.unit ≤ gradeV t (poly.pnorm (sertables.posCorootV t j))
    ∧ gradeV t (poly.pnorm (sertables.posCorootV t j))
        ≤ BPair.ofNat 2 := by
  intro t j hs hsym hnorm hc hdom htop hj
  match Nat.eq_zero_or_pos t.rank with
  | Or.inl hr0 =>
    have hval : gradeV t (poly.pnorm (sertables.posCorootV t j))
        = BPair.unit := by
      show elim.dotP (poly.pnorm ((List.range t.rank).map
          (gentable.corootAt t
            (ground.getAt ([] : List Nat) t.posFolds j))))
          (memberdata.natV (cvee t)) = BPair.unit
      rw [hr0]
      rfl
    rw [hval]
    exact ⟨ground.leB_refl _, ground.unitLeOfNat 2⟩
  | Or.inr hrp =>
    have hpn : (gradeV t (poly.pnorm (sertables.posCorootV t j))).oneValue
        (gradeV t (sertables.posCorootV t j)) :=
      elim.dotP_oneValue_left _ _ _ (poly.pnorm_oneValue _)
    have hzip := elim.dotP_zipSum t.rank (memberdata.natV (cvee t))
      (natVcvee_len t) (ground.getAt ([] : List Nat) t.posFolds j) t.cartan
    have hzip' : (gradeV t (sertables.posCorootV t j)).oneValue
        (BPair.sum (List.zipWith (fun c row =>
          BPair.ofNat c * elim.dotP row (memberdata.natV (cvee t)))
          (ground.getAt ([] : List Nat) t.posFolds j) t.cartan)) := hzip
    have hfold : (gradeV t (poly.pnorm (sertables.posCorootV t j))).oneValue
        (foldKey t (ground.getAt ([] : List Nat) t.posFolds j)) := by
      refine BPair.oneValue_trans hpn (BPair.oneValue_trans hzip' ?_)
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (congrArg BPair.sum
          (zipRange (0 : Nat) ([] : List BPair) _ t.rank
            (ground.getAt ([] : List Nat) t.posFolds j) t.cartan
            (posRow_len t hs j hj) (shapeAt t hs).1))) ?_
      exact BPair.sum_map _ (List.range t.rank)
    have hD : BPair.unit < BPair.ofNat (2 * t.lenDen) :=
      unitLtNat _ (denPos t hc hrp)
    have hmono : foldKey t (ground.getAt ([] : List Nat) t.posFolds j)
        ≤ foldKey t t.thetaFold :=
      foldKey_mono t hs hsym hc hdom _
        (fun i hi => thetaTop_at t htop j hj i hi)
    have hscale : foldKey t (ground.getAt ([] : List Nat) t.posFolds j)
          * BPair.ofNat (2 * t.lenDen)
        ≤ foldKey t t.thetaFold * BPair.ofNat (2 * t.lenDen) := by
      rw [BPair.mul_comm (foldKey t (ground.getAt ([] : List Nat)
          t.posFolds j)) (BPair.ofNat (2 * t.lenDen)),
        BPair.mul_comm (foldKey t t.thetaFold)
          (BPair.ofNat (2 * t.lenDen))]
      exact ground.leB_mulR (ground.unitLeOfNat _) hmono
    have h4 : (4 : Nat) * t.lenDen = 2 * (2 * t.lenDen) :=
      ground.mulAssoc 2 2 t.lenDen
    have htop2 : (foldKey t t.thetaFold * BPair.ofNat (2 * t.lenDen)).oneValue
        (BPair.ofNat 2 * BPair.ofNat (2 * t.lenDen)) := by
      refine BPair.oneValue_trans (foldKey_top t hs hsym hc hnorm) ?_
      rw [h4]
      exact BPair.ofNat_mul 2 (2 * t.lenDen)
    exact ⟨ground.leB_congr_right (BPair.oneValue_symm hfold)
        (foldKey_unit t hs hsym hc hdom _),
      ground.leB_congr_left (BPair.oneValue_symm hfold)
        (ground.leB_unscale hD (ground.leB_congr_right htop2 hscale))⟩

/-- A `θ` content is one entry per key: the unit content at the
coordinate count, a coroot vector and its balance partner at the
key range's own. -/
private theorem famLen (t : gentable.Table) (L : List (List BPair))
    (nu : List BPair) (hfam : row.thetaFamRead t L) (nu_mem : nu ∈ L) :
    nu.length = t.rank := by
  match hfam.2.2 nu nu_mem with
  | Or.inl hu => rw [hu]; exact ground.length_replicate BPair.unit t.rank
  | Or.inr hex =>
    match hex with
    | ⟨j, _, hcase⟩ =>
      match hcase with
      | Or.inl he =>
        rw [he, poly.pnorm_length]
        exact sertables.posCorootV_length t j
      | Or.inr he =>
        rw [he, poly.pnorm_length, poly.length_neg]
        exact sertables.posCorootV_length t j

/-- Every `θ` content's key read at magnitude at most two: the unit
content at the sum's unit, a coroot vector at the positive cap, its
balance partner at the swap (`lem:corner`). -/
theorem content_cap : ∀ (t : gentable.Table)
    (L : List (List BPair)) (nu : List BPair),
    gentable.shapeRead t → gentable.symRead t →
    gentable.thetaNormRead t → cveeRead t →
    thetaDomRead t → thetaTopRead t →
    row.thetaFamRead t L → nu ∈ L →
    gradeV t nu ≤ BPair.ofNat 2
    ∧ (gradeV t nu).swap ≤ BPair.ofNat 2 := by
  intro t L nu hs hsym hnorm hc hdom htop hfam nu_mem
  match hfam.2.2 nu nu_mem with
  | Or.inl hu =>
    have h1 : (gradeV t nu).oneValue BPair.unit := by
      rw [hu]
      exact elim.dotP_replL t.rank (memberdata.natV (cvee t))
    exact ⟨ground.leB_congr_left (BPair.oneValue_symm h1)
        (ground.unitLeOfNat 2),
      ground.leB_congr_left
        (ground.swap_congr (BPair.oneValue_symm h1))
        (ground.unitLeOfNat 2)⟩
  | Or.inr hex =>
    match hex with
    | ⟨j, hjl, hcase⟩ =>
      have hj : j < t.posFolds.length := Nat.lt_of_succ_lt_succ hjl
      have hcap := posGrade_cap t j hs hsym hnorm hc hdom htop hj
      have hpnj : (gradeV t (poly.pnorm (sertables.posCorootV t j))).oneValue
          (gradeV t (sertables.posCorootV t j)) :=
        elim.dotP_oneValue_left _ _ _ (poly.pnorm_oneValue _)
      have hv1 : BPair.unit ≤ gradeV t (sertables.posCorootV t j) :=
        ground.leB_congr_right hpnj hcap.1
      have hv2 : gradeV t (sertables.posCorootV t j) ≤ BPair.ofNat 2 :=
        ground.leB_congr_left hpnj hcap.2
      match hcase with
      | Or.inl he =>
        rw [he]
        exact ⟨hcap.2,
          ground.leB_trans (ground.leB_swap hcap.1) (ground.unitLeOfNat 2)⟩
      | Or.inr he =>
        have hg : (gradeV t nu).oneValue
            (gradeV t (sertables.posCorootV t j)).swap := by
          rw [he]
          refine BPair.oneValue_trans
            (elim.dotP_oneValue_left _ _ _ (poly.pnorm_oneValue _)) ?_
          exact BPair.oneValue_of_eq
            (elim.dotP_swap_left (sertables.posCorootV t j)
              (memberdata.natV (cvee t)))
        exact ⟨ground.leB_congr_left (BPair.oneValue_symm hg)
            (ground.leB_trans (ground.leB_swap hv1)
              (ground.unitLeOfNat 2)),
          ground.leB_congr_left
            (ground.swap_congr (BPair.oneValue_symm hg)) hv2⟩

/-- The key fold is additive over a content join at matched
orders. -/
theorem gradeV_add : ∀ (t : gentable.Table) (x y : List BPair),
    x.length = y.length →
    (gradeV t (poly.pnorm (elim.vecAdd x y))).oneValue
      (gradeV t x + gradeV t y) := by
  intro t x y h
  refine BPair.oneValue_trans
    (elim.dotP_oneValue_left _ _ _ (poly.pnorm_oneValue _)) ?_
  exact elim.dotP_addE x y (memberdata.natV (cvee t)) h

/-- The coroot lists' pairing reads the counts' own, the fold's
count read entrywise. -/
private theorem dotP_natV : ∀ m Y : List Nat,
    (elim.dotP (memberdata.natV m) (memberdata.natV Y)).oneValue
      (BPair.ofNat (ground.dotNat m Y))
  | [], _ => BPair.oneValue_refl _
  | _ :: _, [] => BPair.oneValue_refl _
  | a :: m, b :: Y => by
    show (BPair.ofNat a * BPair.ofNat b
        + elim.dotP (memberdata.natV m) (memberdata.natV Y)).oneValue
      (BPair.ofNat (a * b + ground.dotNat m Y))
    exact BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.ofNat_add (a * b) (ground.dotNat m Y))
      (BPair.add_congr (BPair.ofNat_mul a b)
        (BPair.oneValue_symm (dotP_natV m Y))))

/-- The key moves by at most two under adjoint fusion: a fused
target's coroot list at the moved content reads its key within two
of the source's (`lem:corner`). -/
theorem grade_move : ∀ (t : gentable.Table)
    (L : List (List BPair)) (m c : List Nat) (nu : List BPair),
    gentable.shapeRead t → gentable.symRead t →
    gentable.thetaNormRead t → cveeRead t →
    thetaDomRead t → thetaTopRead t →
    row.thetaFamRead t L → nu ∈ L →
    m.length = t.rank → c.length = t.rank →
    (∀ i, i < t.rank → (BPair.ofNat (ground.getAt 0 c i)).oneValue
      (ground.getAt BPair.unit
        (elim.vecAdd (memberdata.natV m) nu) i)) →
    grade t c ≤ grade t m + 2 ∧ grade t m ≤ grade t c + 2 := by
  intro t L m c nu hs hsym hnorm hcv hdom htop hfam nu_mem hm hcl htie
  have hcap := content_cap t L nu hs hsym hnorm hcv hdom htop hfam nu_mem
  have hnl : nu.length = t.rank := famLen t L nu hfam nu_mem
  have hmv : (memberdata.natV m).length = t.rank :=
    (ground.length_map BPair.ofNat m).trans hm
  have h1 : (gradeV t (memberdata.natV c)).oneValue
      (elim.dotP (elim.vecAdd (memberdata.natV m) nu)
        (memberdata.natV (cvee t))) := by
    refine elim.dotP_congr_left _ _ _ (fun k hk => ?_)
    have hkr : k < t.rank := by
      rw [natVcvee_len t] at hk
      exact hk
    have hcm : ground.getAt BPair.unit (memberdata.natV c) k
        = BPair.ofNat (ground.getAt 0 c k) :=
      ground.getAt_map 0 BPair.unit BPair.ofNat c k
        (by rw [hcl]; exact hkr)
    rw [hcm]
    exact htie k hkr
  have h2 : (elim.dotP (elim.vecAdd (memberdata.natV m) nu)
        (memberdata.natV (cvee t))).oneValue
      (gradeV t (memberdata.natV m) + gradeV t nu) :=
    elim.dotP_addE (memberdata.natV m) nu (memberdata.natV (cvee t))
      (hmv.trans hnl.symm)
  have h3 : (BPair.ofNat (grade t c)).oneValue
      (BPair.ofNat (grade t m) + gradeV t nu) :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (dotP_natV c (cvee t)))
      (BPair.oneValue_trans h1
        (BPair.oneValue_trans h2
          (BPair.add_congr (dotP_natV m (cvee t))
            (BPair.oneValue_refl _))))
  have hle1 : BPair.ofNat (grade t c) ≤ BPair.ofNat (grade t m + 2) := by
    refine ground.leB_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.ofNat_add (grade t m) 2)) ?_
    exact ground.leB_congr_left (BPair.oneValue_symm h3)
      (ground.leB_add (ground.leB_refl _) hcap.1)
  have h4 : (BPair.ofNat (grade t m)).oneValue
      (BPair.ofNat (grade t c) + (gradeV t nu).swap) := by
    refine BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr h3 (BPair.oneValue_refl _)) ?_)
    rw [BPair.add_assoc]
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (ground.unitOfOne (BPair.oneValue_refl (gradeV t nu)))) ?_
    exact BPair.add_unit (BPair.ofNat (grade t m))
  have hle2 : BPair.ofNat (grade t m) ≤ BPair.ofNat (grade t c + 2) := by
    refine ground.leB_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (BPair.ofNat_add (grade t c) 2)) ?_
    exact ground.leB_congr_left (BPair.oneValue_symm h4)
      (ground.leB_add (ground.leB_refl _) hcap.2)
  exact ⟨ground.leB_ofNat_cancel hle1, ground.leB_ofNat_cancel hle2⟩

/-! `lem:corner`'s Casimir cap: the fundamental display
`C₂(λ) = Σ m_i m_j ⟨ω_i,ω_j⟩ + Σ m_i ⟨ω_i,2ρ⟩` capped at the
member's fundamental reads, every summand priced by the
coefficient sum at or below the key. -/

/-- The fundamental Gram's cap read: the base at one or beyond,
every entry within `[0, FN]`, every row's `ρ`-dot at or below `RN`
(`lem:corner`'s Casimir cap at the member's fundamental reads). -/
def gramCapRead (t : gentable.Table) (G : elim.Mat) (FN RN : Nat) :
    Prop :=
  ((1 ≤ FN : Bool)
    && (List.range t.rank).all (fun i =>
      (List.range t.rank).all (fun j =>
        (BPair.unit ≤ ground.getAt BPair.unit (ground.getAt [] G i) j)
          && (ground.getAt BPair.unit (ground.getAt [] G i) j
                ≤ BPair.ofNat FN))
      && (elim.dotP (ground.getAt [] G i) (sertables.rhoV t)
            ≤ BPair.ofNat RN))) = true

instance (t : gentable.Table) (G : elim.Mat) (FN RN : Nat) :
    Decidable (gramCapRead t G FN RN) :=
  inferInstanceAs (Decidable (_ = _))

/-- A strict comparison at an occupied slack: a stated at-or-below
read sits strictly below the joined occupied member. -/
private theorem ltAddPos {a b c : Nat} (h : a ≤ b) (hc : 1 ≤ c) :
    a < b + c :=
  Nat.le_trans (Nat.succ_le_succ h) (Nat.add_le_add_left hc b)

/-- The doubled count sits at or below its square joined to the
count's unit: the gap's own square. -/
private theorem sqCap : ∀ K : Nat, 2 * K ≤ K * K + 1
  | 0 => by decide
  | s + 1 => by
    show 2 * (s + 1) ≤ (s + 1) * (s + 1) + 1
    rw [ground.sqJoin s, Nat.left_distrib s s 2, Nat.mul_comm s 2,
      Nat.left_distrib 2 s 1, Nat.mul_one]
    exact Nat.add_le_add_right (Nat.le_add_left (2 * s) (s * s)) 2

/-- A sorted word reads at or below its head at every key. -/
private theorem headBound (W : List Nat)
    (hs : ∀ i, ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i)
    (i : Nat) : ground.getAt 0 W i ≤ ground.getAt 0 W 0 := by
  have h := descMono W hs 0 i
  rw [Nat.zero_add] at h
  exact h

/-- The word's square fold at a cap on its entries: the cap scales
the word's total. -/
private theorem sumSq_cap : ∀ (W : List Nat) (K : Nat),
    (∀ i, i < W.length → ground.getAt 0 W i ≤ K) →
    c2hat.sumSq W ≤ K * ground.sumNat W
  | [], _, _ => Nat.zero_le _
  | x :: t, K, h => by
    show x * x + c2hat.sumSq t ≤ K * (x + ground.sumNat t)
    rw [Nat.left_distrib K x (ground.sumNat t)]
    exact Nat.add_le_add
      (Nat.mul_le_mul_right x (h 0 (Nat.succ_pos _)))
      (sumSq_cap t K (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

/-- The pairing at a cap on the second family's entries: the cap
scales the first family's total, the fold truncating at it. -/
private theorem dotNat_cap : ∀ (X Y : List Nat) (c : Nat),
    (∀ i, i < X.length → ground.getAt 0 Y i ≤ c) →
    ground.dotNat X Y ≤ c * ground.sumNat X
  | [], _, _, _ => Nat.zero_le _
  | _ :: _, [], _, _ => Nat.zero_le _
  | a :: X, b :: Y, c, h => by
    show a * b + ground.dotNat X Y ≤ c * (a + ground.sumNat X)
    rw [Nat.left_distrib c a (ground.sumNat X)]
    refine Nat.add_le_add ?_
      (dotNat_cap X Y c (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))
    rw [Nat.mul_comm c a]
    exact Nat.mul_le_mul_left a (h 0 (Nat.succ_pos _))

/-- The word's total at a cap on its entries: one cap per key. -/
private theorem sumNat_cap : ∀ (W : List Nat) (K : Nat),
    (∀ i, i < W.length → ground.getAt 0 W i ≤ K) →
    ground.sumNat W ≤ W.length * K
  | [], _, _ => Nat.zero_le _
  | x :: t, K, h => by
    show x + ground.sumNat t ≤ (t.length + 1) * K
    rw [ground.mulAddR t.length 1 K, Nat.one_mul,
      Nat.add_comm (t.length * K) K]
    exact Nat.add_le_add (h 0 (Nat.succ_pos _))
      (sumNat_cap t K (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

/-- The series' shared coordinate core: at entries capped by the
key and root-fold reads capped by the doubled rank, the square
fold with the word against those reads sits below
`l(l+1)(K² + 1)` (`lem:corner`; `lem:serstable`(i)). -/
private theorem casCore (W Y : List Nat) (K l : Nat)
    (hK : ∀ i, i < W.length → ground.getAt 0 W i ≤ K)
    (hY : ∀ i, i < W.length → ground.getAt 0 Y i ≤ 2 * l)
    (hWl : W.length ≤ l) (hl : 1 ≤ l) :
    c2hat.sumSq W + ground.dotNat W Y < (l * l + l) * (K * K + 1) := by
  have hS : ground.sumNat W ≤ l * K :=
    Nat.le_trans (sumNat_cap W K hK) (Nat.mul_le_mul_right K hWl)
  have e1 : K * (l * K) = l * (K * K) := by
    rw [← ground.mulAssoc K l K, Nat.mul_comm K l, ground.mulAssoc l K K]
  have e2 : 2 * l * (l * K) = l * l * (2 * K) := by
    rw [ground.mulAssoc 2 l (l * K), ← ground.mulAssoc l l K,
      ← ground.mulAssoc (l * l) 2 K, Nat.mul_comm (l * l) 2,
      ground.mulAssoc 2 (l * l) K]
  have h1 : c2hat.sumSq W ≤ l * (K * K) := by
    rw [← e1]
    exact Nat.le_trans (sumSq_cap W K hK) (Nat.mul_le_mul_left K hS)
  have h2 : ground.dotNat W Y ≤ l * l * (2 * K) := by
    rw [← e2]
    exact Nat.le_trans (dotNat_cap W Y (2 * l) hY)
      (Nat.mul_le_mul_left (2 * l) hS)
  have h3 : l * l * (2 * K) ≤ l * l * (K * K + 1) :=
    Nat.mul_le_mul_left (l * l) (sqCap K)
  have h4 : (l * l + l) * (K * K + 1)
      = l * (K * K) + l * l * (K * K + 1) + l := by
    rw [ground.mulAddR (l * l) l (K * K + 1),
      Nat.left_distrib l (K * K) 1, Nat.mul_one,
      Nat.add_comm (l * l * (K * K + 1)) (l * (K * K) + l),
      Nat.add_assoc (l * (K * K)) l (l * l * (K * K + 1)),
      Nat.add_comm l (l * l * (K * K + 1)),
      ← Nat.add_assoc (l * (K * K)) (l * l * (K * K + 1)) l]
  rw [h4]
  exact ltAddPos
    (Nat.add_le_add h1 (Nat.le_trans h2 h3)) hl

/-- The `B` series' coordinate route: the rows' magnitudes at or
below the key fold the displayed numerator below `l(l+1)(K² + 1)`,
the cleared member pair `[l(l+1) : casDenB l]` (`lem:corner`;
`lem:serstable`(i)'s displayed value). -/
theorem casCap_B : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length ≤ l → 1 ≤ l →
    serstable.casNumB W l < (l * l + l)
      * ((ground.getAt 0 W 0 + ground.getAt 0 W 1)
          * (ground.getAt 0 W 0 + ground.getAt 0 W 1) + 1) := by
  intro W l hW hWl hl
  have hs := ground.sortedAll W hW
  show c2hat.sumSq W + ground.dotNat W
      ((List.range W.length).map (fun i => 2 * (l - (i + 1)) + 1)) < _
  refine casCore W _ _ l
    (fun i _ => Nat.le_trans (headBound W hs i) (Nat.le_add_right _ _))
    ?_ hWl hl
  intro i hi
  rw [mapRange_read 0 _ W.length i hi]
  have hil : i + 1 ≤ l := Nat.le_trans hi hWl
  have hq : l - (i + 1) + 1 ≤ l := by
    have h1 : l - (i + 1) + (i + 1) = l := ground.subAdd hil
    have h0 : l - (i + 1) + 1 ≤ l - (i + 1) + (i + 1) :=
      Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le i))
        (l - (i + 1))
    rw [h1] at h0
    exact h0
  have h2 : 2 * (l - (i + 1)) + 1 ≤ 2 * (l - (i + 1) + 1) := by
    rw [Nat.left_distrib 2 (l - (i + 1)) 1, Nat.mul_one]
    exact Nat.add_le_add_left (by decide) (2 * (l - (i + 1)))
  exact Nat.le_trans h2 (Nat.mul_le_mul_left 2 hq)

/-- The `C` series' coordinate route: the rows' magnitudes at or
below the key fold the displayed numerator below `l(l+1)(K² + 1)`,
the cleared member pair `[l(l+1) : casDenC l]` (`lem:corner`;
`lem:serstable`(i)'s displayed value). -/
theorem casCap_C : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length ≤ l → 1 ≤ l →
    serstable.casNumC W l < (l * l + l)
      * (ground.getAt 0 W 0 * ground.getAt 0 W 0 + 1) := by
  intro W l hW hWl hl
  have hs := ground.sortedAll W hW
  show c2hat.sumSq W + ground.dotNat W
      ((List.range W.length).map (fun i => 2 * (l - i))) < _
  refine casCore W _ _ l (fun i _ => headBound W hs i) ?_ hWl hl
  intro i hi
  rw [mapRange_read 0 _ W.length i hi]
  exact Nat.mul_le_mul_left 2 (Nat.sub_le l i)

/-- The `D` series' coordinate route: the rows' magnitudes at or
below the key fold the displayed numerator below `l(l+1)(K² + 1)`,
the cleared member pair `[l(l+1) : casDenD l]` (`lem:corner`;
`lem:serstable`(i)'s displayed value). -/
theorem casCap_D : ∀ (W : List Nat) (l : Nat),
    (∀ i, i + 1 < W.length →
      ground.getAt 0 W (i + 1) ≤ ground.getAt 0 W i) →
    W.length ≤ l → 1 ≤ l →
    serstable.casNumD W l < (l * l + l)
      * ((ground.getAt 0 W 0 + ground.getAt 0 W 1)
          * (ground.getAt 0 W 0 + ground.getAt 0 W 1) + 1) := by
  intro W l hW hWl hl
  have hs := ground.sortedAll W hW
  show c2hat.sumSq W + ground.dotNat W
      ((List.range W.length).map (fun i => 2 * (l - (i + 1)))) < _
  refine casCore W _ _ l
    (fun i _ => Nat.le_trans (headBound W hs i) (Nat.le_add_right _ _))
    ?_ hWl hl
  intro i hi
  rw [mapRange_read 0 _ W.length i hi]
  exact Nat.mul_le_mul_left 2 (Nat.sub_le l (i + 1))

/-- A count sits at or below its square joined to the count's
unit. -/
private theorem linCap (K : Nat) : K ≤ K * K + 1 := by
  refine Nat.le_trans ?_ (sqCap K)
  rw [Nat.two_mul]
  exact Nat.le_add_left K K

/-- The count joined to its square sits at or below the
successor's square. -/
private theorem lenSq (n : Nat) : n + n * n ≤ (n + 1) * (n + 1) := by
  have hn : n ≤ 2 * n := by
    rw [Nat.two_mul]
    exact Nat.le_add_left n n
  rw [ground.sqJoin n, Nat.left_distrib n n 2, Nat.mul_comm n 2,
    Nat.add_comm n (n * n)]
  exact Nat.le_trans (Nat.add_le_add_left hn (n * n))
    (Nat.le_add_right (n * n + 2 * n) 1)

/-- The row list reads at or below the shape's total at every
key: the rows are the shape's tail totals. -/
private theorem rowList_cap : ∀ (s : places.Shape) (i : Nat),
    ground.getAt 0 (places.rowList s) i ≤ ground.sumNat s
  | [], _ => Nat.zero_le _
  | n :: t, 0 => Nat.le_refl (n + ground.sumNat t)
  | n :: t, k + 1 => by
    show ground.getAt 0 (places.rowList t) k ≤ n + ground.sumNat t
    exact Nat.le_trans (rowList_cap t k) (Nat.le_add_left _ n)

/-- The reduced representative's total is the `A`-series key: the
full-column key is read to the unit occupancy. -/
private theorem sumNat_reduce : ∀ s : places.Shape,
    ground.sumNat (labels.reduce s) = gradeA s
  | [] => rfl
  | x :: t => by
    match ground.snoc_split t.length (x :: t) rfl with
    | ⟨s', a, hsq, _⟩ =>
      rw [hsq, labels.reduce_snoc s' a, gradeA_snoc s' a,
        ground.sumNat_append s' [0]]
      show ground.sumNat s' + (0 + 0) = ground.sumNat s'
      rw [Nat.add_zero]

/-- An accumulating fold at a capped summand: one cap per member
over the seed. -/
private theorem foldlCap (g : Nat → Nat) (c : Nat) (hg : ∀ y, g y ≤ c) :
    ∀ (t : List Nat) (a : Nat),
      t.foldl (fun acc y => acc + g y) a ≤ a + t.length * c
  | [], a => by
    show a ≤ a + 0 * c
    rw [Nat.zero_mul, Nat.add_zero]
    exact Nat.le_refl a
  | y :: t, a => by
    show List.foldl (fun acc z => acc + g z) (a + g y) t
      ≤ a + (t.length + 1) * c
    refine Nat.le_trans (foldlCap g c hg t (a + g y)) ?_
    rw [ground.mulAddR t.length 1 c, Nat.one_mul,
      Nat.add_comm (t.length * c) c, ← Nat.add_assoc a c (t.length * c)]
    exact Nat.add_le_add_right (Nat.add_le_add_left (hg y) a)
      (t.length * c)

/-- The squared-gap fold at a cap on the rows: every gap's square
within the cap's own, one pair per row pair. -/
private theorem sqGaps_cap : ∀ (R : List Nat) (K : Nat),
    (∀ i, i < R.length → ground.getAt 0 R i ≤ K) →
    c2hat.sqGaps R ≤ R.length * R.length * (K * K)
  | [], _, _ => Nat.zero_le _
  | x :: t, K, h => by
    have hx : x ≤ K := h 0 (Nat.succ_pos _)
    have hg : ∀ y, (x - y) * (x - y) ≤ K * K := fun y =>
      Nat.mul_le_mul (Nat.le_trans (Nat.sub_le x y) hx)
        (Nat.le_trans (Nat.sub_le x y) hx)
    show List.foldl (fun acc y => acc + (x - y) * (x - y)) 0 t
        + c2hat.sqGaps t
      ≤ (t.length + 1) * (t.length + 1) * (K * K)
    refine Nat.le_trans (Nat.add_le_add
      (Nat.le_trans (foldlCap _ (K * K) hg t 0)
        (Nat.le_of_eq (Nat.zero_add _)))
      (sqGaps_cap t K (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))) ?_
    rw [← ground.mulAddR t.length (t.length * t.length) (K * K)]
    exact Nat.mul_le_mul_right (K * K) (lenSq t.length)

/-- The gap fold at a cap on the rows: every gap within the cap,
one pair per row pair. -/
private theorem rho2_cap : ∀ (R : List Nat) (K : Nat),
    (∀ i, i < R.length → ground.getAt 0 R i ≤ K) →
    c2hat.rho2 R ≤ R.length * R.length * K
  | [], _, _ => Nat.zero_le _
  | x :: t, K, h => by
    have hx : x ≤ K := h 0 (Nat.succ_pos _)
    have hg : ∀ y, x - y ≤ K := fun y => Nat.le_trans (Nat.sub_le x y) hx
    show List.foldl (fun acc y => acc + (x - y)) 0 t + c2hat.rho2 t
      ≤ (t.length + 1) * (t.length + 1) * K
    refine Nat.le_trans (Nat.add_le_add
      (Nat.le_trans (foldlCap _ K hg t 0)
        (Nat.le_of_eq (Nat.zero_add _)))
      (rho2_cap t K (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))) ?_
    rw [← ground.mulAddR t.length (t.length * t.length) K]
    exact Nat.mul_le_mul_right K (lenSq t.length)

/-- The `A`-series' coordinate route at the reduced representative:
the sorted rows at or below the key fold the cleared traceless read
below `d²(d+1)(K² + 1)` (`lem:corner`; `def:c2hat`). -/
theorem dfQ_cap : ∀ s : places.Shape, 1 ≤ s.length →
    c2hat.dfQ (labels.reduce s)
      < s.length * s.length * (s.length + 1)
        * (gradeA s * gradeA s + 1) := by
  intro s hd
  have hlen : (labels.reduce s).length = s.length := labels.length_reduce s
  have hR : (places.rowList (labels.reduce s)).length = s.length :=
    (places.length_rowList _).trans hlen
  have hcap : ∀ i, i < (places.rowList (labels.reduce s)).length →
      ground.getAt 0 (places.rowList (labels.reduce s)) i ≤ gradeA s := by
    intro i _
    have hz := rowList_cap (labels.reduce s) i
    rw [sumNat_reduce s] at hz
    exact hz
  have h1 := sqGaps_cap (places.rowList (labels.reduce s)) (gradeA s) hcap
  have h2 := rho2_cap (places.rowList (labels.reduce s)) (gradeA s) hcap
  rw [hR] at h1 h2
  have hcube : s.length * (s.length * s.length * gradeA s)
      = s.length * s.length * s.length * gradeA s := by
    rw [← ground.mulAssoc s.length (s.length * s.length) (gradeA s),
      Nat.mul_comm s.length (s.length * s.length)]
  have h3 : s.length * (s.length * s.length * gradeA s)
      ≤ s.length * s.length * s.length * (gradeA s * gradeA s)
        + s.length * s.length * s.length := by
    have he : s.length * s.length * s.length * (gradeA s * gradeA s)
        + s.length * s.length * s.length
        = s.length * s.length * s.length * (gradeA s * gradeA s + 1) := by
      rw [Nat.left_distrib (s.length * s.length * s.length)
        (gradeA s * gradeA s) 1, Nat.mul_one]
    rw [hcube, he]
    exact Nat.mul_le_mul_left _ (linCap (gradeA s))
  have hone : 1 ≤ s.length * s.length := by
    have hz := Nat.mul_le_mul hd hd
    rw [Nat.one_mul] at hz
    exact hz
  have hrhs : s.length * s.length * (s.length + 1)
        * (gradeA s * gradeA s + 1)
      = s.length * s.length * (gradeA s * gradeA s)
        + (s.length * s.length * s.length * (gradeA s * gradeA s)
          + s.length * s.length * s.length)
        + s.length * s.length := by
    rw [Nat.left_distrib (s.length * s.length) s.length 1, Nat.mul_one,
      ground.mulAddR (s.length * s.length * s.length) (s.length * s.length)
        (gradeA s * gradeA s + 1),
      Nat.left_distrib (s.length * s.length * s.length)
        (gradeA s * gradeA s) 1, Nat.mul_one,
      Nat.left_distrib (s.length * s.length) (gradeA s * gradeA s) 1,
      Nat.mul_one,
      Nat.add_comm (s.length * s.length * (gradeA s * gradeA s))
        (s.length * s.length),
      ← Nat.add_assoc
        (s.length * s.length * s.length * (gradeA s * gradeA s)
          + s.length * s.length * s.length)
        (s.length * s.length)
        (s.length * s.length * (gradeA s * gradeA s)),
      Nat.add_comm
        (s.length * s.length * s.length * (gradeA s * gradeA s)
          + s.length * s.length * s.length + s.length * s.length)
        (s.length * s.length * (gradeA s * gradeA s)),
      ← Nat.add_assoc (s.length * s.length * (gradeA s * gradeA s))
        (s.length * s.length * s.length * (gradeA s * gradeA s)
          + s.length * s.length * s.length)
        (s.length * s.length)]
  show c2hat.sqGaps (places.rowList (labels.reduce s))
      + (labels.reduce s).length
        * c2hat.rho2 (places.rowList (labels.reduce s)) < _
  rw [hlen, hrhs]
  exact ltAddPos
    (Nat.add_le_add h1
      (Nat.le_trans (Nat.mul_le_mul_left s.length h2) h3)) hone

/-- The cap read's base occupancy. -/
private theorem gramCap_base (t : gentable.Table) (G : elim.Mat)
    (FN RN : Nat) (h : gramCapRead t G FN RN) : 1 ≤ FN :=
  of_decide_eq_true (ground.andSplitB h).1

/-- The cap read's entry walls at a key pair. -/
private theorem gramCap_entry (t : gentable.Table) (G : elim.Mat)
    (FN RN : Nat) (h : gramCapRead t G FN RN) (i : Nat) (hi : i < t.rank)
    (j : Nat) (hj : j < t.rank) :
    BPair.unit
        ≤ ground.getAt BPair.unit (ground.getAt [] G i) j
      ∧ ground.getAt BPair.unit (ground.getAt [] G i) j
          ≤ BPair.ofNat FN := by
  have h1 := ground.all_range_read t.rank (ground.andSplitB h).2 i hi
  have h2 := ground.all_range_read t.rank (ground.andSplitB h1).1 j hj
  exact ⟨of_decide_eq_true (ground.andSplitB h2).1,
    of_decide_eq_true (ground.andSplitB h2).2⟩

/-- The cap read's `ρ`-dot wall at a row. -/
private theorem gramCap_rho (t : gentable.Table) (G : elim.Mat)
    (FN RN : Nat) (h : gramCapRead t G FN RN) (i : Nat) (hi : i < t.rank) :
    elim.dotP (ground.getAt [] G i) (sertables.rhoV t) ≤ BPair.ofNat RN :=
  of_decide_eq_true (ground.andSplitB
    (ground.all_range_read t.rank (ground.andSplitB h).2 i hi)).2

/-- A content occupied within its order is occupied at every key:
the keys beyond the order read the family's own unit. -/
private theorem allUnitB (w : List BPair)
    (h : ∀ k, k < w.length → BPair.unit ≤ ground.getAt BPair.unit w k) :
    ∀ k, BPair.unit ≤ ground.getAt BPair.unit w k := by
  intro k
  by_cases hk : k < w.length
  · exact h k hk
  · rw [ground.getAt_over BPair.unit w k (Nat.le_of_not_lt hk)]
    exact ground.leB_refl _

/-- A coroot list's order is the count list's own. -/
private theorem natV_len (m : List Nat) :
    (memberdata.natV m).length = m.length :=
  ground.length_map BPair.ofNat m

/-- A coroot list's entry within its order is the count's pair. -/
private theorem natV_read (m : List Nat) (k : Nat) (hk : k < m.length) :
    ground.getAt BPair.unit (memberdata.natV m) k
      = BPair.ofNat (ground.getAt 0 m k) :=
  ground.getAt_map 0 BPair.unit BPair.ofNat m k hk

/-- A coroot list is occupied at every key. -/
private theorem natV_unit (m : List Nat) :
    ∀ k, BPair.unit ≤ ground.getAt BPair.unit (memberdata.natV m) k := by
  refine allUnitB _ (fun k hk => ?_)
  rw [natV_len m] at hk
  rw [natV_read m k hk]
  exact ground.unitLeOfNat _

/-- `ρ`'s coroot vector is occupied at every key. -/
private theorem rhoV_unit (t : gentable.Table) :
    ∀ k, BPair.unit ≤ ground.getAt BPair.unit (sertables.rhoV t) k := by
  refine allUnitB _ (fun k hk => ?_)
  have hk' : k < t.rank := by
    rw [show (sertables.rhoV t).length = t.rank from
      ground.length_replicate (BPair.ofNat 1) t.rank] at hk
    exact hk
  show BPair.unit ≤ ground.getAt BPair.unit
    (List.replicate t.rank (BPair.ofNat 1)) k
  rw [ground.getAt_replicate BPair.unit (BPair.ofNat 1) t.rank k hk']
  exact ground.unitLeOfNat 1

/-- A memberwise sum of two occupied contents is occupied at every
key. -/
private theorem vecAdd_unit : ∀ (u w : List BPair),
    (∀ k, BPair.unit ≤ ground.getAt BPair.unit u k) →
    (∀ k, BPair.unit ≤ ground.getAt BPair.unit w k) →
    ∀ k, BPair.unit ≤ ground.getAt BPair.unit (elim.vecAdd u w) k
  | [], _, _, _, _ => ground.leB_refl _
  | _ :: _, [], _, _, _ => ground.leB_refl _
  | _ :: _, _ :: _, hu, hw, 0 =>
    ground.leB_congr_left (BPair.add_unit BPair.unit)
      (ground.leB_add (hu 0) (hw 0))
  | _ :: u, _ :: w, hu, hw, k + 1 =>
    vecAdd_unit u w (fun j => hu (j + 1)) (fun j => hw (j + 1)) k

/-- The pairing of two occupied contents is occupied: every
summand within the fold's own truncation sits at or beyond the
sum's unit. -/
private theorem dotP_unit : ∀ (u w : List BPair),
    (∀ j, j < w.length → BPair.unit ≤ ground.getAt BPair.unit u j) →
    (∀ j, BPair.unit ≤ ground.getAt BPair.unit w j) →
    BPair.unit ≤ elim.dotP u w
  | [], _, _, _ => ground.leB_refl _
  | _ :: _, [], _, _ => ground.leB_refl _
  | a :: u, b :: w, hu, hw => by
    show BPair.unit ≤ a * b + elim.dotP u w
    exact ground.leB_congr_left (BPair.add_unit BPair.unit)
      (ground.leB_add (ground.unitLeMul (hu 0 (Nat.succ_pos _)) (hw 0))
        (dotP_unit u w (fun j hj => hu (j + 1) (Nat.succ_lt_succ hj))
          (fun j => hw (j + 1))))

/-- The pairing against a coroot list at a cap on the first
content's entries: the cap scales the count list's total, the fold
truncating at that count. -/
private theorem dotP_scaleN : ∀ (u : List BPair) (a : List Nat) (F : Nat),
    (∀ j, j < a.length →
      ground.getAt BPair.unit u j ≤ BPair.ofNat F) →
    elim.dotP u (memberdata.natV a)
      ≤ BPair.ofNat (F * ground.sumNat a)
  | [], _, _, _ => ground.unitLeOfNat _
  | _ :: _, [], _, _ => ground.unitLeOfNat _
  | x :: u, b :: a, F, h => by
    show x * BPair.ofNat b + elim.dotP u (memberdata.natV a)
      ≤ BPair.ofNat (F * (b + ground.sumNat a))
    rw [Nat.left_distrib F b (ground.sumNat a)]
    refine ground.leB_congr_right
      (BPair.oneValue_symm
        (BPair.ofNat_add (F * b) (F * ground.sumNat a)))
      (ground.leB_add ?_ (dotP_scaleN u a F
        (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))))
    exact ground.leB_congr_right
      (BPair.oneValue_symm (BPair.ofNat_mul F b))
      (ground.leB_mul_mono (ground.unitLeOfNat b) (ground.unitLeOfNat F)
        (h 0 (Nat.succ_pos _)) (ground.leB_refl _))

/-- The matrix-against-content read at a row key: the row's
skipping fold against the content. -/
private theorem matVec_read (G : elim.Mat) (y : List BPair) (j : Nat)
    (hj : j < G.length) :
    ground.getAt BPair.unit (elim.matVec G y) j
      = elim.dotN (ground.getAt [] G j) y :=
  ground.getAt_map ([] : List BPair) BPair.unit _ G j hj

/-- The cap's strict count step: a value at or below the cleared
product sits below `(FN + RN)(g² + 1)` at an occupied base, the
doubled cross term priced by the key's square. -/
private theorem capNat (FN RN S g N : Nat) (hS : S ≤ g) (hF : 1 ≤ FN)
    (hN : N ≤ (FN * S + (RN + RN)) * S) :
    N < (FN + RN) * (g * g + 1) := by
  have hstep : (FN * g + (RN + RN)) * g = FN * (g * g) + (RN + RN) * g := by
    rw [ground.mulAddR (FN * g) (RN + RN) g, ground.mulAssoc FN g g]
  have hrn : (RN + RN) * g ≤ RN * (g * g) + RN := by
    have h1 : (RN + RN) * g = RN * (2 * g) := by
      rw [← Nat.mul_two RN, ground.mulAssoc RN 2 g]
    have h2 : RN * (g * g + 1) = RN * (g * g) + RN := by
      rw [Nat.left_distrib RN (g * g) 1, Nat.mul_one]
    rw [h1, ← h2]
    exact Nat.mul_le_mul_left RN (sqCap g)
  have e4 : (FN + RN) * (g * g + 1)
      = FN * (g * g) + (RN * (g * g) + RN) + FN := by
    rw [ground.mulAddR FN RN (g * g + 1),
      Nat.left_distrib FN (g * g) 1, Nat.mul_one,
      Nat.left_distrib RN (g * g) 1, Nat.mul_one,
      Nat.add_right_comm (FN * (g * g)) FN (RN * (g * g) + RN)]
  rw [e4]
  refine ltAddPos (Nat.le_trans hN ?_) hF
  refine Nat.le_trans (Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul_left FN hS) (RN + RN)) hS) ?_
  rw [hstep]
  exact Nat.add_le_add_left hrn (FN * (g * g))

/-- The fundamental display's cap: the Gram summands against the
coefficient sum at or below the key fold the cleared Casimir below
`(FN + RN)(G² + 1)` — the cleared member pair's numerator side,
the adjoint's clearing the consumer's own read (`lem:corner`'s
Casimir cap at the adjugate rows' displayed folds). -/
theorem c2M_cap : ∀ (t : gentable.Table) (G : elim.Mat)
    (FN RN : Nat) (m : List Nat),
    gramCapRead t G FN RN → cveeRead t →
    m.length = t.rank → G.length = t.rank →
    memberdata.c2M t G m
      < (FN + RN) * (grade t m * grade t m + 1) := by
  intro t G FN RN m hgc hcv hm hG
  have hmv : (memberdata.natV m).length = t.rank := (natV_len m).trans hm
  have hrv : (sertables.rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hrr : (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t)).length
      = t.rank := elim.length_vecAdd _ _ t.rank hrv hrv
  have hyl : (elim.vecAdd (memberdata.natV m)
      (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))).length
      = t.rank := elim.length_vecAdd _ _ t.rank hmv hrr
  have hyu : ∀ k, BPair.unit ≤ ground.getAt BPair.unit
      (elim.vecAdd (memberdata.natV m)
        (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))) k :=
    vecAdd_unit _ _ (natV_unit m)
      (vecAdd_unit _ _ (rhoV_unit t) (rhoV_unit t))
  have hrowU : ∀ j, j < t.rank → BPair.unit ≤ elim.dotP
      (ground.getAt [] G j) (elim.vecAdd (memberdata.natV m)
        (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))) := by
    intro j hj
    refine dotP_unit _ _ (fun i hi => ?_) hyu
    rw [hyl] at hi
    exact (gramCap_entry t G FN RN hgc j hj i hi).1
  have hrowC : ∀ j, j < t.rank → elim.dotP
      (ground.getAt [] G j) (elim.vecAdd (memberdata.natV m)
        (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t)))
      ≤ BPair.ofNat (FN * ground.sumNat m + (RN + RN)) := by
    intro j hj
    have e1 := elim.dotP_vecAdd_right (ground.getAt [] G j)
      (memberdata.natV m)
      (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))
      (hmv.trans hrr.symm)
    have e2 := elim.dotP_vecAdd_right (ground.getAt [] G j)
      (sertables.rhoV t) (sertables.rhoV t) rfl
    have echain := BPair.oneValue_trans e1
      (BPair.add_congr (BPair.oneValue_refl _) e2)
    have b1 : elim.dotP (ground.getAt [] G j) (memberdata.natV m)
        ≤ BPair.ofNat (FN * ground.sumNat m) :=
      dotP_scaleN (ground.getAt [] G j) m FN (fun i hi => by
        rw [hm] at hi
        exact (gramCap_entry t G FN RN hgc j hj i hi).2)
    have b2 := gramCap_rho t G FN RN hgc j hj
    refine ground.leB_congr_left (BPair.oneValue_symm echain) ?_
    refine ground.leB_congr_right
      (BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.ofNat_add (FN * ground.sumNat m) (RN + RN))
        (BPair.add_congr (BPair.oneValue_refl _)
          (BPair.ofNat_add RN RN)))) ?_
    exact ground.leB_add b1 (ground.leB_add b2 b2)
  have hmvU : ∀ j, j < (memberdata.natV m).length → BPair.unit
      ≤ ground.getAt BPair.unit (elim.matVec G
          (elim.vecAdd (memberdata.natV m)
            (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t)))) j := by
    intro j hj
    rw [hmv] at hj
    rw [matVec_read G _ j (by rw [hG]; exact hj)]
    exact ground.leB_congr_right
      (BPair.oneValue_symm (elim.dotN_dotP _ _)) (hrowU j hj)
  have hmvC : ∀ j, j < m.length → ground.getAt BPair.unit
      (elim.matVec G (elim.vecAdd (memberdata.natV m)
        (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t)))) j
      ≤ BPair.ofNat (FN * ground.sumNat m + (RN + RN)) := by
    intro j hj
    rw [hm] at hj
    rw [matVec_read G _ j (by rw [hG]; exact hj)]
    exact ground.leB_congr_left
      (BPair.oneValue_symm (elim.dotN_dotP _ _)) (hrowC j hj)
  have hvU : BPair.unit ≤ elim.dotP (elim.matVec G
      (elim.vecAdd (memberdata.natV m)
        (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))))
      (memberdata.natV m) :=
    dotP_unit _ _ hmvU (natV_unit m)
  have hvC : elim.dotP (elim.matVec G
      (elim.vecAdd (memberdata.natV m)
        (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))))
      (memberdata.natV m)
      ≤ BPair.ofNat ((FN * ground.sumNat m + (RN + RN))
          * ground.sumNat m) :=
    dotP_scaleN _ m (FN * ground.sumNat m + (RN + RN)) hmvC
  have hc2 : memberdata.c2M t G m = BPair.marginN (elim.dotP
      (elim.matVec G (elim.vecAdd (memberdata.natV m)
        (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t))))
      (memberdata.natV m)) := by
    show BPair.marginN (BPair.norm (elim.dotP (memberdata.natV m)
        (elim.matVec G (elim.vecAdd (memberdata.natV m)
          (elim.vecAdd (sertables.rhoV t) (sertables.rhoV t)))))) = _
    rw [elim.dotP_comm (memberdata.natV m) (elim.matVec G _)]
    exact BPair.marginN_congr (BPair.norm_oneValue _)
  rw [hc2]
  refine capNat FN RN (ground.sumNat m) (grade t m) _
    (coeffSum_le t m hcv (Nat.le_of_eq hm)) (gramCap_base t G FN RN hgc) ?_
  exact ground.leB_ofNat_cancel
    (ground.leB_congr_left (BPair.ofNat_marginN hvU) hvC)

/-! `lem:corner`'s per-key counts: the labels at one key value are
the dual fold's solutions, at most `(G+1)` per simple key; the
member gap product's factors read at or below the `θ` factor at the
join's read against `λ+ρ`'s coroot pairs with
`(λ+ρ)(θ^∨) = G + r`; so the per-key label and dimension counts sit
below `A (G+1)^p` at the member reads `A`, `p`. -/

/-- The labels at one key value: the dual fold's solutions, the
box under the key's own entry bound filtered at the key
(`lem:corner`'s counts). -/
def keyAll (t : gentable.Table) (g : Nat) : List (List Nat) :=
  (ground.boxAll (List.replicate t.rank g)).filter
    (fun m => grade t m == g)

/-- The `θ` factor at a coroot list: the highest root's fold
against the length-weighted entries, the member gap product's
capping factor (`lem:corner`'s counts). -/
def thetaGap (t : gentable.Table) (v : List Nat) : Nat :=
  ground.dotNat t.thetaFold (List.zipWith Nat.mul t.lenNums v)

/-- The count caps' base `A`, a member read (`lem:corner`). -/
def capA (t : gentable.Table) : Nat :=
  ground.prodOver (fun _ => 2 * t.lenDen * (gentable.residue t + 1))
    (List.range t.posFolds.length)

/-- The count caps' exponent `p`, a member read (`lem:corner`). -/
def capP (t : gentable.Table) : Nat :=
  t.rank + t.posFolds.length

/-- The length family is one entry per key. -/
private theorem lenNums_len (t : gentable.Table)
    (hs : gentable.shapeRead t) : t.lenNums.length = t.rank :=
  ground.beqEqOf (ground.andSplitB (ground.andSplitB
    (ground.andSplitB (ground.andSplitB hs).1).1).1).1

/-- A filtered family is no longer than its source. -/
private theorem lenFilterLe {α : Type} (P : α → Bool) :
    ∀ l : List α, (l.filter P).length ≤ l.length
  | [] => Nat.le_refl 0
  | a :: t => by
    cases hp : P a with
    | true =>
      rw [ground.filter_cons_true hp]
      exact Nat.succ_le_succ (lenFilterLe P t)
    | false =>
      rw [ground.filter_cons_false hp]
      exact Nat.le_trans (lenFilterLe P t) (Nat.le_succ t.length)

/-- A cofactor sits at or below its numerator. -/
private theorem divLeSelf (a b : Nat) : a / b ≤ a := by
  match Nat.eq_zero_or_pos b with
  | Or.inl hb =>
    rw [hb, divZeroN]
    exact Nat.zero_le a
  | Or.inr hb =>
    have h1 := (ground.natDivRead a b hb).1
    have h2 : b * (a / b) ≤ a := by
      have h2' : b * (a / b) ≤ b * (a / b) + a % b :=
        Nat.le_add_right _ _
      rw [h1] at h2'
      exact h2'
    have h3 : 1 * (a / b) ≤ b * (a / b) :=
      Nat.mul_le_mul_right (a / b) hb
    rw [Nat.one_mul] at h3
    exact Nat.le_trans h3 h2

/-- Each coefficient sits at or below the pairing against a family
occupied at every paired key. -/
private theorem dotGeAt : ∀ (m Y : List Nat), m.length ≤ Y.length →
    (∀ k, k < m.length → 1 ≤ ground.getAt 0 Y k) →
    ∀ i, i < m.length → ground.getAt 0 m i ≤ ground.dotNat m Y
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | _ :: _, [], h, _, _, _ => absurd h (Nat.not_succ_le_zero _)
  | a :: m, b :: Y, _, hb, 0, _ => by
    show a ≤ a * b + ground.dotNat m Y
    have h1 : a * 1 ≤ a * b :=
      Nat.mul_le_mul_left a (hb 0 (Nat.succ_pos m.length))
    rw [Nat.mul_one] at h1
    exact Nat.le_trans h1 (Nat.le_add_right _ _)
  | a :: m, b :: Y, h, hb, i + 1, hi => by
    show ground.getAt 0 m i ≤ a * b + ground.dotNat m Y
    exact Nat.le_trans
      (dotGeAt m Y (Nat.le_of_succ_le_succ h)
        (fun k hk => hb (k + 1) (Nat.succ_lt_succ hk)) i
        (Nat.lt_of_succ_lt_succ hi))
      (Nat.le_add_left _ _)

/-- The componentwise walk stops at its shorter side. -/
private theorem lenZipLe {α β γ : Type} (f : α → β → γ) :
    ∀ (u : List α) (v : List β),
      (List.zipWith f u v).length ≤ u.length
  | [], _ => Nat.le_refl 0
  | _ :: _, [] => Nat.zero_le _
  | _ :: u, _ :: v => Nat.succ_le_succ (lenZipLe f u v)

/-- The pairing is monotone in its first family at the entries the
second family reads. -/
private theorem dotNatMonoL : ∀ (X X' Y : List Nat),
    (∀ i, i < Y.length →
      ground.getAt 0 X i ≤ ground.getAt 0 X' i) →
    ground.dotNat X Y ≤ ground.dotNat X' Y
  | [], _, _, _ => Nat.zero_le _
  | _ :: _, [], [], _ => Nat.le_refl 0
  | _ :: _, _ :: _, [], _ => Nat.le_refl 0
  | a :: X, [], c :: Y, h => by
    show a * c + ground.dotNat X Y ≤ 0
    have h0 : a = 0 :=
      Nat.eq_zero_of_le_zero (h 0 (Nat.succ_pos Y.length))
    rw [h0, Nat.zero_mul, Nat.zero_add]
    exact dotNatMonoL X [] Y
      (fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
  | a :: X, b :: X', c :: Y, h => by
    show a * c + ground.dotNat X Y ≤ b * c + ground.dotNat X' Y
    exact Nat.add_le_add
      (Nat.mul_le_mul (h 0 (Nat.succ_pos Y.length)) (Nat.le_refl c))
      (dotNatMonoL X X' Y
        (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)))

/-- The member gap product's factors read at or below the `θ`
factor: the join's pointwise witness against the natural entries,
the fold windows the shaped table's own. -/
theorem gapAt_le : ∀ (t : gentable.Table) (v : List Nat) (j : Nat),
    gentable.shapeRead t → thetaTopRead t → j < t.posFolds.length →
    serstable.gapAt t v j ≤ thetaGap t v := by
  intro t v j hs h hj
  show ground.dotNat (ground.getAt ([] : List Nat) t.posFolds j)
      (List.zipWith Nat.mul t.lenNums v)
    ≤ ground.dotNat t.thetaFold (List.zipWith Nat.mul t.lenNums v)
  refine dotNatMonoL _ _ _ (fun i hi => ?_)
  exact thetaTop_at t h j hj i
    (Nat.lt_of_lt_of_le hi
      (Nat.le_trans (lenZipLe Nat.mul t.lenNums v)
        (Nat.le_of_eq (lenNums_len t hs))))

/-- A mapped family's total sits at or below the count scaled by a
shared member cap. -/
private theorem sumMapCap {α : Type} (f : α → Nat) (c : Nat) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ c) →
      ground.sumNat (l.map f) ≤ l.length * c
  | [], _ => Nat.zero_le _
  | a :: t, h => by
    show f a + ground.sumNat (t.map f) ≤ (t.length + 1) * c
    rw [ground.mulAddR t.length 1 c, Nat.one_mul,
      Nat.add_comm (t.length * c) c]
    exact Nat.add_le_add (h a (List.Mem.head t))
      (sumMapCap f c t (fun x hx => h x (List.Mem.tail a hx)))

/-- The identification: a coroot list at the rank sits in the key
list once exactly at its key value, off it at the vacant count —
the labels at one key value are the dual fold's solutions, the
entry bound the halved summands' own (`lem:corner`). -/
theorem keyAll_countOf : ∀ (t : gentable.Table) (g : Nat)
    (m : List Nat), cveeRead t →
    ground.countOf m (keyAll t g)
      = if m.length = t.rank ∧ grade t m = g then 1 else 0 := by
  intro t g m hc
  show ground.countOf m
      ((ground.boxAll (List.replicate t.rank g)).filter
        (fun w => grade t w == g)) = _
  rw [ground.countOf_filter (fun w => grade t w == g) m
      (ground.boxAll (List.replicate t.rank g)),
    ground.boxAll_countOf (List.replicate t.rank g) m]
  by_cases hg : grade t m = g
  · rw [if_pos (ground.eqBeqOf hg)]
    by_cases hl : m.length = t.rank
    · have hb1 : m.length = (List.replicate t.rank g).length := by
        rw [ground.length_replicate]
        exact hl
      have hb2 : ∀ i, i < (List.replicate t.rank g).length →
          ground.getAt 0 m i
            ≤ ground.getAt 0 (List.replicate t.rank g) i := by
        intro i hi
        rw [ground.length_replicate] at hi
        rw [ground.getAt_replicate 0 g t.rank i hi]
        have hle := dotGeAt m (cvee t)
          (Nat.le_of_eq (hl.trans (cvee_len t).symm))
          (fun k hk => cveeRead_pos t hc k
            (Nat.lt_of_lt_of_le hk (Nat.le_of_eq hl)))
          i (Nat.lt_of_lt_of_le hi (Nat.le_of_eq hl.symm))
        rw [← hg]
        exact hle
      rw [if_pos ⟨hb1, hb2⟩, if_pos ⟨hl, hg⟩]
    · rw [if_neg (fun hbc => hl (hbc.1.trans
        (ground.length_replicate g t.rank))),
        if_neg (fun hcc => hl hcc.1)]
  · rw [if_neg (fun hb => hg (ground.beqEqOf hb)),
      if_neg (fun hcc => hg hcc.2)]

/-- A key list's member reads its length at the rank and its key
at the value. -/
private theorem keyAll_mem_reads (t : gentable.Table) (g : Nat)
    (hc : cveeRead t) (m : List Nat) (hm : m ∈ keyAll t g) :
    m.length = t.rank ∧ grade t m = g := by
  have h := ground.countOf_pos_of_mem hm
  rw [keyAll_countOf t g m hc] at h
  by_cases hcond : m.length = t.rank ∧ grade t m = g
  · exact hcond
  · rw [if_neg hcond] at h
    exact absurd h (Nat.lt_irrefl 0)

/-- At most `(G+1)` per simple key. -/
theorem keyAll_length : ∀ (t : gentable.Table) (g : Nat),
    (keyAll t g).length
      ≤ ground.prodOver (fun _ => g + 1) (List.range t.rank) := by
  intro t g
  show ((ground.boxAll (List.replicate t.rank g)).filter
      (fun w => grade t w == g)).length ≤ _
  refine Nat.le_trans (lenFilterLe _ _) ?_
  rw [ground.boxAll_length (List.replicate t.rank g)]
  have hcongr : ground.prodOver (fun x => x + 1)
        (List.replicate t.rank g)
      = ground.prodOver (fun _ => g + 1)
          (List.replicate t.rank g) :=
    ground.famFold_congr_members Nat.mul 1 _ _
      (List.replicate t.rank g)
      (fun x hx => by
        by_cases hxg : x = g
        · rw [hxg]
        · rw [ground.countOf_replicate_ne x g hxg t.rank] at hx
          exact absurd hx (Nat.lt_irrefl 0))
  have hconst : ground.prodOver (fun _ => g + 1)
        (List.replicate t.rank g)
      = ground.prodOver (fun _ => g + 1) (List.range t.rank) :=
    ground.prodOver_const (g + 1) (List.replicate t.rank g)
      (List.range t.rank)
      (by rw [ground.length_replicate, ground.length_range])
  exact Nat.le_of_eq (hcongr.trans hconst)

/-- The `θ` factor at the raised member reads `2 lenDen (G + r)`:
`(λ+ρ)(θ^∨) = G + r` cleared. -/
theorem thetaGap_read : ∀ (t : gentable.Table) (m : List Nat),
    gentable.shapeRead t → cveeRead t → m.length = t.rank →
    thetaGap t (m.map (· + 1))
      = 2 * t.lenDen * (grade t m + gentable.residue t) := by
  intro t m hs hc hm
  have hln : t.lenNums.length = t.rank := lenNums_len t hs
  have hth : t.thetaFold.length = t.rank := (shapeAt t hs).2.1
  have hmap : (m.map (· + 1)).length = t.rank :=
    (ground.length_map (· + 1) m).trans hm
  have hzip : (List.zipWith Nat.mul t.lenNums (m.map (· + 1))).length
      = t.rank :=
    ground.length_zipWith Nat.mul t.lenNums (m.map (· + 1)) t.rank
      hln hmap
  have hL : thetaGap t (m.map (· + 1))
      = ground.famFold Nat.add 0
          (fun i => ground.getAt 0 t.thetaFold i
            * ground.getAt 0
                (List.zipWith Nat.mul t.lenNums (m.map (· + 1))) i)
          (List.range t.rank) := by
    show ground.dotNat t.thetaFold
        (List.zipWith Nat.mul t.lenNums (m.map (· + 1))) = _
    rw [ground.dotNat_index t.thetaFold
        (List.zipWith Nat.mul t.lenNums (m.map (· + 1)))
        (hzip.trans hth.symm), hth]
  have hgrade : grade t m = ground.famFold Nat.add 0
      (fun i => ground.getAt 0 m i * ground.getAt 0 (cvee t) i)
      (List.range t.rank) := by
    show ground.dotNat m (cvee t) = _
    rw [ground.dotNat_index m (cvee t) ((cvee_len t).trans hm.symm), hm]
  have hres : gentable.residue t = ground.famFold Nat.add 0
      (fun i => ground.getAt 0 (cvee t) i) (List.range t.rank) := by
    rw [← cvee_sum t hs hc]
    show ground.sumNat ((List.range t.rank).map
        (fun i => ground.getAt 0 t.thetaFold i
          * ground.getAt 0 t.lenNums i / (2 * t.lenDen))) = _
    rw [ground.sumMap _ (List.range t.rank)]
    exact ground.famFold_congr_range _ _ t.rank
      (fun i hi => (cvee_entry t i hi).symm)
  have hterm : ∀ i, i < t.rank →
      ground.getAt 0 t.thetaFold i
          * ground.getAt 0
              (List.zipWith Nat.mul t.lenNums (m.map (· + 1))) i
        = 2 * t.lenDen
            * (ground.getAt 0 m i * ground.getAt 0 (cvee t) i)
          + 2 * t.lenDen * ground.getAt 0 (cvee t) i := by
    intro i hi
    rw [ground.getAt_zipWith 0 0 0 Nat.mul t.lenNums (m.map (· + 1)) i
        (by rw [hln]; exact hi) (by rw [hmap]; exact hi),
      ground.getAt_map 0 0 (· + 1) m i (by rw [hm]; exact hi)]
    show ground.getAt 0 t.thetaFold i
        * (ground.getAt 0 t.lenNums i * (ground.getAt 0 m i + 1))
      = 2 * t.lenDen
          * (ground.getAt 0 m i * ground.getAt 0 (cvee t) i)
        + 2 * t.lenDen * ground.getAt 0 (cvee t) i
    rw [← ground.mulAssoc (ground.getAt 0 t.thetaFold i)
        (ground.getAt 0 t.lenNums i) (ground.getAt 0 m i + 1),
      ← cveeRead_mul t hc i hi,
      Nat.left_distrib (ground.getAt 0 (cvee t) i * (2 * t.lenDen))
        (ground.getAt 0 m i) 1,
      Nat.mul_one (ground.getAt 0 (cvee t) i * (2 * t.lenDen)),
      Nat.mul_comm (ground.getAt 0 (cvee t) i) (2 * t.lenDen),
      ground.mulAssoc (2 * t.lenDen) (ground.getAt 0 (cvee t) i)
        (ground.getAt 0 m i),
      Nat.mul_comm (ground.getAt 0 (cvee t) i) (ground.getAt 0 m i)]
  rw [hL, ground.famFold_congr_range _ _ t.rank hterm,
    ground.famFold_add_split
      (fun i => 2 * t.lenDen
        * (ground.getAt 0 m i * ground.getAt 0 (cvee t) i))
      (fun i => 2 * t.lenDen * ground.getAt 0 (cvee t) i)
      (List.range t.rank),
    Nat.left_distrib (2 * t.lenDen) (grade t m) (gentable.residue t),
    hgrade, hres,
    ground.famFold_mul (2 * t.lenDen)
      (fun i => ground.getAt 0 m i * ground.getAt 0 (cvee t) i)
      (List.range t.rank),
    ground.famFold_mul (2 * t.lenDen)
      (fun i => ground.getAt 0 (cvee t) i) (List.range t.rank)]

/-- The member dimension at or below the `θ` factor's power, the
gap product's factors each capped. -/
theorem dimM_cap : ∀ (t : gentable.Table) (m : List Nat),
    gentable.shapeRead t → cveeRead t → thetaTopRead t →
    m.length = t.rank →
    memberdata.dimM t m
      ≤ ground.prodOver
          (fun _ => 2 * t.lenDen * (grade t m + gentable.residue t))
          (List.range t.posFolds.length) := by
  intro t m hs hc ht hm
  refine Nat.le_trans (divLeSelf _ _) ?_
  refine Nat.le_trans
    (ground.prodOver_le (serstable.gapAt t (m.map (· + 1)))
      (fun _ => thetaGap t (m.map (· + 1)))
      (List.range t.posFolds.length)
      (fun j hj => gapAt_le t (m.map (· + 1)) j hs ht
        (ground.ltOfMemRange hj))) ?_
  rw [thetaGap_read t m hs hc hm]
  exact Nat.le_refl _

/-- The per-key label count sits below `A (G+1)^p` at the member
reads `A`, `p` (`lem:corner`). -/
theorem keyCount_cap : ∀ (t : gentable.Table) (g : Nat),
    1 ≤ t.lenDen → 1 ≤ t.posFolds.length →
    (keyAll t g).length
      < capA t * ground.prodOver (fun _ => g + 1)
          (List.range (capP t)) := by
  intro t g hd hp
  have hg1 : 1 ≤ g + 1 := Nat.succ_le_succ (Nat.zero_le g)
  have hP : 1 ≤ ground.prodOver (fun _ => g + 1) (List.range t.rank) :=
    ground.prodOver_pos (fun _ => g + 1) (List.range t.rank)
      (fun _ _ => hg1)
  have hQ : 1 ≤ ground.prodOver (fun _ => g + 1)
      (List.range t.posFolds.length) :=
    ground.prodOver_pos (fun _ => g + 1)
      (List.range t.posFolds.length) (fun _ _ => hg1)
  have hc2 : 2 ≤ 2 * t.lenDen * (gentable.residue t + 1) := by
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 2) hd)
      (Nat.succ_le_succ (Nat.zero_le (gentable.residue t)))
    rw [Nat.mul_one, Nat.mul_one] at h1
    exact h1
  have hA : 2 ≤ capA t :=
    Nat.le_trans hc2 (ground.prodConst_ge _
      (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 1)) hc2)
      t.posFolds.length hp)
  have hsplit : ground.prodOver (fun _ => g + 1) (List.range (capP t))
      = ground.prodOver (fun _ => g + 1) (List.range t.rank)
        * ground.prodOver (fun _ => g + 1)
            (List.range t.posFolds.length) :=
    ground.prodConst_split (g + 1) t.rank t.posFolds.length
  refine Nat.lt_of_le_of_lt (keyAll_length t g) ?_
  rw [hsplit]
  have h1 : ground.prodOver (fun _ => g + 1) (List.range t.rank)
      ≤ ground.prodOver (fun _ => g + 1) (List.range t.rank)
        * ground.prodOver (fun _ => g + 1)
            (List.range t.posFolds.length) := by
    have h := Nat.mul_le_mul
      (Nat.le_refl (ground.prodOver (fun _ => g + 1)
        (List.range t.rank))) hQ
    rw [Nat.mul_one] at h
    exact h
  refine Nat.lt_of_lt_of_le ?_ (Nat.mul_le_mul hA h1)
  rw [Nat.two_mul]
  have h3 := Nat.add_lt_add_left hP
    (ground.prodOver (fun _ => g + 1) (List.range t.rank))
  rw [Nat.add_zero] at h3
  exact h3

/-- The two factors' strict exchange: the key's join against the
residue sits strictly below the raised residue's scale at the
raised key. -/
private theorem gapStrict (g r : Nat) : g + r < (r + 1) * (g + 1) := by
  rw [Nat.left_distrib (r + 1) g 1, Nat.mul_one,
    ground.mulAddR r 1 g, Nat.one_mul]
  exact Nat.lt_of_le_of_lt
    (Nat.add_le_add_right (Nat.le_add_left g (r * g)) r)
    (Nat.add_lt_add_left (Nat.lt_succ_self r) (r * g + g))

/-- The strict product at an occupied left scale. -/
private theorem mulLtL {a b : Nat} (h : a < b) {c : Nat}
    (hc : 1 ≤ c) : c * a < c * b := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  have hb : b = a + (d + 1) := by
    rw [← hd]
    show a + 1 + d = a + (d + 1)
    rw [Nat.add_assoc, Nat.add_comm 1 d]
  have hk : 1 ≤ c * (d + 1) := by
    have h1 := Nat.mul_le_mul hc
      (Nat.succ_le_succ (Nat.zero_le d))
    rw [Nat.mul_one] at h1
    exact h1
  rw [hb, Nat.left_distrib]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (c * a))
    (Nat.add_le_add_left hk (c * a))

/-- A constant's power at reach one is the constant. -/
private theorem powOne (C : Nat) :
    ground.prodOver (fun _ => C) (List.range 1) = C := by
  show C * 1 = C
  rw [Nat.mul_one]

/-- A constant factor's strict product over an occupied range. -/
private theorem prodConst_lt {a b : Nat} (h : a < b) :
    ∀ n : Nat, 1 ≤ n →
      ground.prodOver (fun _ => a) (List.range n)
        < ground.prodOver (fun _ => b) (List.range n)
  | n + 1, _ => by
    rw [ground.prodConst_split a n 1, ground.prodConst_split b n 1,
      powOne a, powOne b]
    refine Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (ground.prodOver_le _ _ (List.range n)
        (fun _ _ => Nat.le_of_lt h)) (Nat.le_refl a)) ?_
    exact mulLtL h (ground.prodOver_pos (fun _ => b) (List.range n)
      (fun _ _ => Nat.le_trans (Nat.succ_le_succ (Nat.zero_le a))
        (Nat.succ_le_of_lt h)))

/-- The per-key dimension count sits below `A (G+1)^p` at the
member reads `A`, `p` (`lem:corner`). -/
theorem keyDim_cap : ∀ (t : gentable.Table) (g : Nat),
    gentable.shapeRead t → cveeRead t → thetaTopRead t →
    1 ≤ t.lenDen → 1 ≤ t.posFolds.length →
    ground.sumNat ((keyAll t g).map (memberdata.dimM t))
      < capA t * ground.prodOver (fun _ => g + 1)
          (List.range (capP t)) := by
  intro t g hs hc ht hd hp
  have hg1 : 1 ≤ g + 1 := Nat.succ_le_succ (Nat.zero_le g)
  have hP : 1 ≤ ground.prodOver (fun _ => g + 1) (List.range t.rank) :=
    ground.prodOver_pos (fun _ => g + 1) (List.range t.rank)
      (fun _ _ => hg1)
  have hmem : ∀ x ∈ keyAll t g, memberdata.dimM t x
      ≤ ground.prodOver
          (fun _ => 2 * t.lenDen * (g + gentable.residue t))
          (List.range t.posFolds.length) := by
    intro x hx
    have hr := keyAll_mem_reads t g hc x hx
    have h := dimM_cap t x hs hc ht hr.1
    rw [hr.2] at h
    exact h
  have hsplit : ground.prodOver (fun _ => g + 1) (List.range (capP t))
      = ground.prodOver (fun _ => g + 1) (List.range t.rank)
        * ground.prodOver (fun _ => g + 1)
            (List.range t.posFolds.length) :=
    ground.prodConst_split (g + 1) t.rank t.posFolds.length
  have hfac : 2 * t.lenDen * (g + gentable.residue t)
      < 2 * t.lenDen * (gentable.residue t + 1) * (g + 1) := by
    have hK : 1 ≤ 2 * t.lenDen := by
      have h := Nat.mul_le_mul (Nat.le_refl 2) hd
      rw [Nat.mul_one] at h
      exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 1)) h
    have h := mulLtL (gapStrict g (gentable.residue t)) hK
    rw [← ground.mulAssoc (2 * t.lenDen) (gentable.residue t + 1)
      (g + 1)] at h
    exact h
  have hCQ : ground.prodOver
        (fun _ => 2 * t.lenDen * (g + gentable.residue t))
        (List.range t.posFolds.length)
      < capA t * ground.prodOver (fun _ => g + 1)
          (List.range t.posFolds.length) := by
    have hms : ground.prodOver
          (fun _ => 2 * t.lenDen * (gentable.residue t + 1) * (g + 1))
          (List.range t.posFolds.length)
        = capA t * ground.prodOver (fun _ => g + 1)
            (List.range t.posFolds.length) :=
      ground.famFold_mul_split
        (fun _ => 2 * t.lenDen * (gentable.residue t + 1))
        (fun _ => g + 1) (List.range t.posFolds.length)
    rw [← hms]
    exact prodConst_lt hfac t.posFolds.length hp
  refine Nat.lt_of_le_of_lt
    (Nat.le_trans (sumMapCap (memberdata.dimM t) _ (keyAll t g) hmem)
      (Nat.mul_le_mul (keyAll_length t g) (Nat.le_refl _))) ?_
  rw [hsplit, ← ground.mulLeftComm
    (ground.prodOver (fun _ => g + 1) (List.range t.rank)) (capA t)
    (ground.prodOver (fun _ => g + 1)
      (List.range t.posFolds.length))]
  exact mulLtL hCQ hP

/-- The rising product absorbs its own reach: the floor's step
against the length's. -/
private theorem riseShift : ∀ (j c : Nat),
    (c + j) * ground.rise c j = c * ground.rise (c + 1) j
  | 0, _ => rfl
  | j + 1, c => by
    show (c + j + 1) * (c * ground.rise (c + 1) j)
      = c * ((c + 1) * ground.rise (c + 1 + 1) j)
    rw [← riseShift j (c + 1),
      ground.mulLeftComm (c + j + 1) c (ground.rise (c + 1) j),
      Nat.add_right_comm c j 1]

/-- The rising product's Pascal identity, one display per key. -/
private theorem risePascal (k j : Nat) :
    ground.rise (k + 1) (j + 1)
      = ground.rise k (j + 1) + (j + 1) * ground.rise (k + 1) j := by
  show (k + 1) * ground.rise (k + 1 + 1) j
    = k * ground.rise (k + 1) j + (j + 1) * ground.rise (k + 1) j
  rw [← riseShift j (k + 1), ← ground.mulAddR k (j + 1)
      (ground.rise (k + 1) j), Nat.add_right_comm k 1 j,
    Nat.add_assoc k j 1]

/-- The rising product is monotone in its floor. -/
private theorem riseMono : ∀ (j c c' : Nat), c ≤ c' →
    ground.rise c j ≤ ground.rise c' j
  | 0, _, _, _ => Nat.le_refl 1
  | j + 1, c, c', h =>
    Nat.mul_le_mul h (riseMono j (c + 1) (c' + 1) (Nat.succ_le_succ h))

/-- The rising product at the unit floor peels its own length. -/
private theorem riseOne (j : Nat) :
    ground.rise 1 (j + 1) = (j + 1) * ground.rise 1 j := by
  show 1 * ground.rise (1 + 1) j = (j + 1) * ground.rise 1 j
  rw [← riseShift j 1, Nat.add_comm 1 j]

/-- A constant's power at a grown reach peels its top factor. -/
private theorem powStep (C n : Nat) :
    ground.prodOver (fun _ => C) (List.range (n + 1))
      = ground.prodOver (fun _ => C) (List.range n) * C := by
  rw [ground.prodConst_split C n 1]
  show ground.prodOver (fun _ => C) (List.range n) * (C * 1) = _
  rw [Nat.mul_one]

/-- A gap below the whole shifts with the whole's step. -/
private theorem subShift (k M : Nat) (h : k ≤ M) : M + 1 - k = M - k + 1 := by
  have h1 : M + 1 - (k + 1) + 1 = M + 1 - k :=
    ground.subSuccAdd (Nat.succ_le_succ h)
  rw [Nat.succ_sub_succ M k] at h1
  exact h1.symm

/-- The cleared graded sum: the rising-product weights against the
split powers. -/
private def gradSum (j M X C : Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun k => ground.rise (k + 1) j
      * ground.prodOver (fun _ => X) (List.range k)
      * ground.prodOver (fun _ => C) (List.range (M - k)))
    (List.range (M + 1))

/-- The graded sum at the vacant reach is the rising product at the
unit floor. -/
private theorem gradSum_zero (j X C : Nat) : gradSum j 0 X C = ground.rise 1 j := by
  show ground.rise 1 j * 1 * 1 = ground.rise 1 j
  rw [Nat.mul_one, Nat.mul_one]

/-- The graded sum at a grown reach: the whole's multiple of the
sum joins the new top term. -/
private theorem gradSum_top (j M X C : Nat) :
    gradSum j (M + 1) X C
      = C * gradSum j M X C
        + ground.rise (M + 1 + 1) j
          * ground.prodOver (fun _ => X) (List.range (M + 1)) := by
  have hcong : ground.famFold Nat.add 0
      (fun k => ground.rise (k + 1) j
        * ground.prodOver (fun _ => X) (List.range k)
        * ground.prodOver (fun _ => C) (List.range (M + 1 - k)))
      (List.range (M + 1))
      = ground.famFold Nat.add 0
      (fun k => (ground.rise (k + 1) j
        * ground.prodOver (fun _ => X) (List.range k)
        * ground.prodOver (fun _ => C) (List.range (M - k))) * C)
      (List.range (M + 1)) :=
    ground.famFold_congr_range _ _ (M + 1) (fun i hi => by
      rw [subShift i M (Nat.le_of_lt_succ hi), powStep C (M - i)]
      exact (ground.mulAssoc _ _ _).symm)
  show ground.famFold Nat.add 0
      (fun k => ground.rise (k + 1) j
        * ground.prodOver (fun _ => X) (List.range k)
        * ground.prodOver (fun _ => C) (List.range (M + 1 - k)))
      (List.range (M + 1 + 1)) = _
  rw [ground.range_succ (M + 1), ground.famFold_snoc, hcong,
    ground.famFold_mulR C
      (fun k => ground.rise (k + 1) j
        * ground.prodOver (fun _ => X) (List.range k)
        * ground.prodOver (fun _ => C) (List.range (M - k)))
      (List.range (M + 1)),
    ground.subLe (M + 1) (M + 1) (Nat.le_refl (M + 1))]
  show gradSum j M X C * C
      + ground.rise (M + 1 + 1) j
        * ground.prodOver (fun _ => X) (List.range (M + 1)) * 1
    = C * gradSum j M X C
      + ground.rise (M + 1 + 1) j
        * ground.prodOver (fun _ => X) (List.range (M + 1))
  rw [Nat.mul_one, Nat.mul_comm (gradSum j M X C) C]

/-- The geometric seed: the gap's multiple of the plain sum joins
the top power to the whole power. -/
private theorem gradSum_geo (M X Y C : Nat) (h : X + Y = C) :
    Y * gradSum 0 M X C
        + ground.prodOver (fun _ => X) (List.range (M + 1))
      = ground.prodOver (fun _ => C) (List.range (M + 1)) := by
  induction M with
  | zero =>
    show Y * gradSum 0 0 X C
        + ground.prodOver (fun _ => X) (List.range 1)
      = ground.prodOver (fun _ => C) (List.range 1)
    rw [gradSum_zero 0 X C, powOne X, powOne C]
    show Y * 1 + X = C
    rw [Nat.mul_one, Nat.add_comm Y X]
    exact h
  | succ M ih =>
    rw [gradSum_top 0 M X C, powStep X (M + 1), powStep C (M + 1)]
    show Y * (C * gradSum 0 M X C
          + 1 * ground.prodOver (fun _ => X) (List.range (M + 1)))
        + ground.prodOver (fun _ => X) (List.range (M + 1)) * X
      = ground.prodOver (fun _ => C) (List.range (M + 1)) * C
    rw [Nat.one_mul (ground.prodOver (fun _ => X) (List.range (M + 1))),
      Nat.left_distrib Y (C * gradSum 0 M X C)
        (ground.prodOver (fun _ => X) (List.range (M + 1))),
      Nat.add_assoc,
      Nat.mul_comm Y (ground.prodOver (fun _ => X) (List.range (M + 1))),
      ← Nat.left_distrib
        (ground.prodOver (fun _ => X) (List.range (M + 1))) Y X,
      Nat.add_comm Y X, h,
      ground.mulLeftComm Y C (gradSum 0 M X C),
      Nat.mul_comm C (Y * gradSum 0 M X C), ← ih,
      ground.mulAddR (Y * gradSum 0 M X C)
        (ground.prodOver (fun _ => X) (List.range (M + 1))) C]

/-- The exact Pascal descent: the gap's multiple of the raised sum
joins the boundary term to the stepped multiple of the sum. -/
private theorem gradSum_step (j M X Y C : Nat) (h : X + Y = C) :
    Y * gradSum (j + 1) M X C
        + ground.rise (M + 1) (j + 1)
          * ground.prodOver (fun _ => X) (List.range (M + 1))
      = (j + 1) * C * gradSum j M X C := by
  induction M with
  | zero =>
    show Y * gradSum (j + 1) 0 X C
        + ground.rise 1 (j + 1) * ground.prodOver (fun _ => X) (List.range 1)
      = (j + 1) * C * gradSum j 0 X C
    rw [gradSum_zero (j + 1) X C, gradSum_zero j X C, powOne X,
      Nat.mul_comm Y (ground.rise 1 (j + 1)),
      ← Nat.left_distrib (ground.rise 1 (j + 1)) Y X,
      Nat.add_comm Y X, h, riseOne j,
      ground.mulRightComm (j + 1) (ground.rise 1 j) C]
  | succ M ih =>
    have hA : Y * gradSum (j + 1) (M + 1) X C
          + ground.rise (M + 1 + 1) (j + 1)
            * ground.prodOver (fun _ => X) (List.range (M + 1 + 1))
        = C * (Y * gradSum (j + 1) M X C
          + ground.rise (M + 1 + 1) (j + 1)
            * ground.prodOver (fun _ => X) (List.range (M + 1))) := by
      rw [gradSum_top (j + 1) M X C, powStep X (M + 1),
        Nat.left_distrib Y (C * gradSum (j + 1) M X C)
          (ground.rise (M + 1 + 1) (j + 1)
            * ground.prodOver (fun _ => X) (List.range (M + 1))),
        Nat.left_distrib C (Y * gradSum (j + 1) M X C)
          (ground.rise (M + 1 + 1) (j + 1)
            * ground.prodOver (fun _ => X) (List.range (M + 1))),
        ground.mulLeftComm Y C (gradSum (j + 1) M X C),
        Nat.add_assoc,
        ← ground.mulAssoc (ground.rise (M + 1 + 1) (j + 1))
          (ground.prodOver (fun _ => X) (List.range (M + 1))) X,
        Nat.mul_comm Y (ground.rise (M + 1 + 1) (j + 1)
          * ground.prodOver (fun _ => X) (List.range (M + 1))),
        ← Nat.left_distrib (ground.rise (M + 1 + 1) (j + 1)
          * ground.prodOver (fun _ => X) (List.range (M + 1))) Y X,
        Nat.add_comm Y X, h,
        Nat.mul_comm (ground.rise (M + 1 + 1) (j + 1)
          * ground.prodOver (fun _ => X) (List.range (M + 1))) C]
    have hB : Y * gradSum (j + 1) M X C
          + ground.rise (M + 1 + 1) (j + 1)
            * ground.prodOver (fun _ => X) (List.range (M + 1))
        = (j + 1) * gradSum j (M + 1) X C := by
      rw [risePascal (M + 1) j, gradSum_top j M X C,
        ground.mulAddR (ground.rise (M + 1) (j + 1))
          ((j + 1) * ground.rise (M + 1 + 1) j)
          (ground.prodOver (fun _ => X) (List.range (M + 1))),
        ← Nat.add_assoc, ih,
        Nat.left_distrib (j + 1) (C * gradSum j M X C)
          (ground.rise (M + 1 + 1) j
            * ground.prodOver (fun _ => X) (List.range (M + 1))),
        ground.mulAssoc (j + 1) C (gradSum j M X C),
        ground.mulAssoc (j + 1) (ground.rise (M + 1 + 1) j)
          (ground.prodOver (fun _ => X) (List.range (M + 1)))]
    rw [hA, hB, ground.mulLeftComm C (j + 1) (gradSum j (M + 1) X C),
      ← ground.mulAssoc (j + 1) C (gradSum j (M + 1) X C)]

/-- The descent's close: the gap's power caps the graded sum at the
factorial against the whole power. -/
private theorem gradSum_close (j M X Y C : Nat) (h : X + Y = C) :
    ground.prodOver (fun _ => Y) (List.range (j + 1))
        * gradSum j M X C
      ≤ ground.rise 1 j
        * ground.prodOver (fun _ => C) (List.range (M + j + 1)) := by
  induction j with
  | zero =>
    show ground.prodOver (fun _ => Y) (List.range 1) * gradSum 0 M X C
      ≤ 1 * ground.prodOver (fun _ => C) (List.range (M + 1))
    rw [powOne Y, Nat.one_mul]
    exact Nat.le.intro (gradSum_geo M X Y C h)
  | succ j ih =>
    have hstep : Y * gradSum (j + 1) M X C
        ≤ (j + 1) * C * gradSum j M X C :=
      Nat.le.intro (gradSum_step j M X Y C h)
    show ground.prodOver (fun _ => Y) (List.range (j + 1 + 1))
        * gradSum (j + 1) M X C
      ≤ ground.rise 1 (j + 1)
        * ground.prodOver (fun _ => C) (List.range (M + j + 1 + 1))
    rw [powStep Y (j + 1), powStep C (M + j + 1), riseOne j,
      ground.mulAssoc (ground.prodOver (fun _ => Y) (List.range (j + 1))) Y
        (gradSum (j + 1) M X C)]
    refine Nat.le_trans (Nat.mul_le_mul (Nat.le_refl _) hstep) ?_
    rw [ground.mulLeftComm (ground.prodOver (fun _ => Y) (List.range (j + 1)))
      ((j + 1) * C) (gradSum j M X C)]
    refine Nat.le_trans (Nat.mul_le_mul (Nat.le_refl ((j + 1) * C)) ih) ?_
    rw [ground.mulMulMulComm (j + 1) C (ground.rise 1 j)
        (ground.prodOver (fun _ => C) (List.range (M + j + 1))),
      Nat.mul_comm C
        (ground.prodOver (fun _ => C) (List.range (M + j + 1)))]
    exact Nat.le_refl _

/-- The power cap: the constant power at or below the rising
product, every factor at or beyond the floor. -/
private theorem powLeRise (k j : Nat) :
    ground.prodOver (fun _ => k + 1) (List.range j)
      ≤ ground.rise (k + 1) j := by
  induction j with
  | zero => exact Nat.le_refl 1
  | succ j ih =>
    rw [powStep (k + 1) j]
    refine Nat.le_trans (Nat.mul_le_mul ih (Nat.le_refl (k + 1))) ?_
    rw [Nat.mul_comm (ground.rise (k + 1) j) (k + 1)]
    show (k + 1) * ground.rise (k + 1) j
      ≤ (k + 1) * ground.rise (k + 1 + 1) j
    exact Nat.mul_le_mul (Nat.le_refl (k + 1))
      (riseMono j (k + 1) (k + 1 + 1) (Nat.le_add_right (k + 1) 1))


/-- The trial family's coefficient at a row: the dimension against
the scale's split powers at the key, the off-family rows at the
count's unit (`lem:corner`'s dimension-weighted family, cleared at
the scale triple). -/
def trialAt (twoN a c : Nat) (dR gR : Nat → Nat) (i : Nat) : Nat :=
  if gR i ≤ twoN
  then dR i * ground.prodOver (fun _ => a) (List.range (gR i))
    * ground.prodOver (fun _ => c) (List.range (twoN - gR i))
  else 0

/-- The family's pairing: the squared coefficients' fold. -/
def pairFold (o twoN a c : Nat) (dR gR : Nat → Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun i => trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
    (List.range o)

/-- The electric read: the diagonal against the squared
coefficients. -/
def elecFold (o twoN a c : Nat) (dR gR eR : Nat → Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun i => eR i
      * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
    (List.range o)

/-- The magnetic read: the fusion rows' quadratic fold. -/
def magFold (o twoN a c : Nat) (dR gR : Nat → Nat)
    (NR : Nat → Nat → Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun i => trialAt twoN a c dR gR i
      * ground.famFold Nat.add 0
          (fun j => NR i j * trialAt twoN a c dR gR j) (List.range o))
    (List.range o)

/-- The top two key values' part of the pairing, the boundary
term's carrier. -/
def topFold (o twoN a c : Nat) (dR gR : Nat → Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun i => if twoN ≤ gR i + 1
      then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
      else 0)
    (List.range o)

/-- A row inside the key window reads the displayed product. -/
private theorem trial_of (twoN a c : Nat) (dR gR : Nat → Nat) (i : Nat)
    (h : gR i ≤ twoN) :
    trialAt twoN a c dR gR i
      = dR i * ground.prodOver (fun _ => a) (List.range (gR i))
        * ground.prodOver (fun _ => c) (List.range (twoN - gR i)) :=
  if_pos h

/-- A row beyond the key window reads the sum's unit. -/
private theorem trial_off (twoN a c : Nat) (dR gR : Nat → Nat) (i : Nat)
    (h : ¬ gR i ≤ twoN) : trialAt twoN a c dR gR i = 0 :=
  if_neg h

/-- The split powers at a raised key sit at or below those at a
lowered one, the scale at or below the whole. -/
private theorem powMono (a c K : Nat) (hac : a ≤ c) (g g' : Nat)
    (hg : g ≤ g') (hK : g' ≤ K) :
    ground.prodOver (fun _ => a) (List.range g')
        * ground.prodOver (fun _ => c) (List.range (K - g'))
      ≤ ground.prodOver (fun _ => a) (List.range g)
        * ground.prodOver (fun _ => c) (List.range (K - g)) := by
  have hd := Nat.le.dest hg
  refine Exists.elim hd (fun d hdd => ?_)
  have hgap : g' - g = d := by
    rw [← hdd, ground.addSubSelfL g d]
  have hsub : K - g = (K - g') + d := by
    rw [← hgap, ground.subJoin hg hK]
  have e1 : ground.prodOver (fun _ => a) (List.range g')
      = ground.prodOver (fun _ => a) (List.range g)
        * ground.prodOver (fun _ => a) (List.range d) := by
    rw [← hdd, ground.prodConst_split a g d]
  have e2 : ground.prodOver (fun _ => c) (List.range (K - g))
      = ground.prodOver (fun _ => c) (List.range (K - g'))
        * ground.prodOver (fun _ => c) (List.range d) := by
    rw [hsub, ground.prodConst_split c (K - g') d]
  have hle : ground.prodOver (fun _ => a) (List.range d)
      ≤ ground.prodOver (fun _ => c) (List.range d) :=
    ground.prodOver_le (fun _ => a) (fun _ => c) (List.range d)
      (fun _ _ => hac)
  rw [e1, e2, ground.mulAssoc
      (ground.prodOver (fun _ => a) (List.range g))
      (ground.prodOver (fun _ => a) (List.range d))
      (ground.prodOver (fun _ => c) (List.range (K - g'))),
    Nat.mul_comm (ground.prodOver (fun _ => c) (List.range (K - g')))
      (ground.prodOver (fun _ => c) (List.range d))]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hle (Nat.le_refl _))

/-- The squares' fold sits at or below the fold's own square. -/
private theorem sqFoldLe (f : Nat → Nat) (l : List Nat) :
    ground.famFold Nat.add 0 (fun i => f i * f i) l
      ≤ ground.famFold Nat.add 0 f l * ground.famFold Nat.add 0 f l := by
  rw [← ground.famFold_mulR (ground.famFold Nat.add 0 f l) f l]
  exact ground.famFold_le _ _ l
    (fun x hx => Nat.mul_le_mul_left (f x)
      (ground.famFold_mem_le f l x hx))

/-- The key regroup: a family vacant beyond the key window folds as
the keys' own row folds over the window. -/
private theorem keyGroup (o twoN : Nat) (gR h : Nat → Nat)
    (hz : ∀ i, twoN < gR i → h i = 0) :
    ground.famFold Nat.add 0 h (List.range o)
      = ground.famFold Nat.add 0
          (fun k => ground.famFold Nat.add 0
            (fun i => if gR i == k then h i else 0) (List.range o))
          (List.range (twoN + 1)) := by
  rw [← ground.famFold_swap (fun i k => if gR i == k then h i else 0)
      (List.range o) (List.range (twoN + 1))]
  refine ground.famFold_congr_all Nat.add 0 h _ (fun i => ?_) (List.range o)
  by_cases hi : gR i ≤ twoN
  · exact (ground.famFold_pickBeqRange (gR i) (h i) (twoN + 1)
      (Nat.lt_succ_of_le hi)).symm
  · have h0 : h i = 0 := hz i (Nat.lt_of_not_le hi)
    refine h0.trans (ground.famFold_zero
      (fun k => if gR i == k then h i else 0) (fun x => ?_)
      (List.range (twoN + 1))).symm
    cases hb : (gR i == x) with
    | true => exact h0
    | false => rfl

/-- The key's own row fold: the family's rows at one key read the
key's dimension count against the split powers. -/
private theorem keySum (o twoN a c k : Nat) (dR gR : Nat → Nat)
    (hk : k ≤ twoN) :
    ground.famFold Nat.add 0
        (fun i => if gR i == k then trialAt twoN a c dR gR i else 0)
        (List.range o)
      = ground.famFold Nat.add 0
          (fun i => if gR i == k then dR i else 0) (List.range o)
        * ground.prodOver (fun _ => a) (List.range k)
        * ground.prodOver (fun _ => c) (List.range (twoN - k)) := by
  rw [← ground.famFold_mulR (ground.prodOver (fun _ => a) (List.range k))
      (fun i => if gR i == k then dR i else 0) (List.range o),
    ← ground.famFold_mulR (ground.prodOver (fun _ => c) (List.range (twoN - k)))
      (fun i => (if gR i == k then dR i else 0)
        * ground.prodOver (fun _ => a) (List.range k)) (List.range o)]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun i => ?_) (List.range o)
  cases hb : (gR i == k) with
  | true =>
    have he : gR i = k := ground.beqEqOf hb
    have hik : gR i ≤ twoN := by
      rw [he]
      exact hk
    show trialAt twoN a c dR gR i
      = dR i * ground.prodOver (fun _ => a) (List.range k)
        * ground.prodOver (fun _ => c) (List.range (twoN - k))
    rw [trial_of twoN a c dR gR i hik, he]
  | false =>
    show (0 : Nat)
      = 0 * ground.prodOver (fun _ => a) (List.range k)
        * ground.prodOver (fun _ => c) (List.range (twoN - k))
    rw [Nat.zero_mul, Nat.zero_mul]

/-- A constant's power at a twice-grown reach peels its two top
factors. -/
private theorem powAdd2 (C n : Nat) :
    ground.prodOver (fun _ => C) (List.range (n + 2))
      = ground.prodOver (fun _ => C) (List.range n) * (C * C) := by
  rw [ground.prodConst_split C n 2]
  show ground.prodOver (fun _ => C) (List.range n) * (C * (C * 1))
    = ground.prodOver (fun _ => C) (List.range n) * (C * C)
  rw [Nat.mul_one]

/-- A five-factor product's exchange, `A D (E F G) = D E (F A G)`. -/
private theorem mulRearr5 (A D E F G : Nat) :
    A * D * (E * F * G) = D * E * (F * A * G) := by
  rw [ground.mulAssoc A D (E * F * G), ground.mulAssoc E F G,
    ground.mulAssoc D E (F * A * G), ground.mulAssoc F A G,
    ground.mulLeftComm F A G, ground.mulLeftComm E A (F * G),
    ground.mulLeftComm D A (E * (F * G))]

/-- A five-factor product's exchange, the head factor withdrawing
to the tail. -/
private theorem mulRearrR (u z e f g : Nat) :
    u * (z * (e * f * g)) = z * e * (f * g * u) := by
  rw [ground.mulAssoc e f g, ground.mulAssoc z e (f * g * u),
    Nat.mul_comm (f * g) u, ground.mulLeftComm e u (f * g),
    ground.mulLeftComm z u (e * (f * g))]

/-- The vacuum's unit term floors the pairing. -/
theorem vac_floor (o twoN a c i0 : Nat) (dR gR : Nat → Nat)
    (hi0 : i0 < o) (hg : gR i0 = 0) (hd : dR i0 = 1) :
    ground.prodOver (fun _ => c) (List.range (2 * twoN))
      ≤ pairFold o twoN a c dR gR := by
  have hle : gR i0 ≤ twoN := by
    rw [hg]
    exact Nat.zero_le twoN
  have ht : trialAt twoN a c dR gR i0
      = ground.prodOver (fun _ => c) (List.range twoN) := by
    rw [trial_of twoN a c dR gR i0 hle, hg, hd, Nat.sub_zero twoN]
    show 1 * 1 * ground.prodOver (fun _ => c) (List.range twoN)
      = ground.prodOver (fun _ => c) (List.range twoN)
    rw [Nat.mul_one, Nat.one_mul]
  rw [Nat.two_mul twoN, ground.prodConst_split c twoN twoN, ← ht]
  exact ground.famFold_mem_le
    (fun i => trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
    (List.range o) i0 (ground.memRange hi0)

/-- The move cap prices the magnetic read termwise at the dimension
eigen-identity: below the top two key values every fusion target
stays in the family, and the row collects at the identity
(`lem:corner`'s magnetic display, cleared). -/
theorem mag_low (o twoN a c dth : Nat) (dR gR : Nat → Nat)
    (NR : Nat → Nat → Nat) (hac : a ≤ c)
    (hmove : ∀ i j, i < o → j < o → 0 < NR i j → gR j ≤ gR i + 2)
    (hdim : ∀ i, i < o → gR i + 2 ≤ twoN →
      ground.famFold Nat.add 0 (fun j => NR i j * dR j) (List.range o)
        = dth * dR i) :
    a * a * dth * pairFold o twoN a c dR gR
      ≤ c * c * magFold o twoN a c dR gR NR
        + a * a * dth * topFold o twoN a c dR gR := by
  have key : ∀ i ∈ List.range o,
      a * a * dth
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
        ≤ c * c
            * (trialAt twoN a c dR gR i
              * ground.famFold Nat.add 0
                  (fun j => NR i j * trialAt twoN a c dR gR j)
                  (List.range o))
          + a * a * dth
            * (if twoN ≤ gR i + 1
              then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
              else 0) := by
    refine fun i hi => ?_
    have hio : i < o := ground.ltOfMemRange hi
    by_cases htop : twoN ≤ gR i + 1
    · rw [if_pos htop]
      exact Nat.le_add_left _ _
    · have hlt : gR i + 2 ≤ twoN := Nat.lt_of_not_le htop
      have hgi : gR i ≤ twoN :=
        Nat.le_trans (Nat.le_add_right (gR i) 2) hlt
      have hs2 : twoN - gR i = twoN - (gR i + 2) + 2 := by
        rw [← ground.subJoin (Nat.le_add_right (gR i) 2) hlt,
          ground.addSubSelfL (gR i) 2]
      have hP2 : ground.prodOver (fun _ => c) (List.range (twoN - gR i))
          = ground.prodOver (fun _ => c)
              (List.range (twoN - (gR i + 2))) * (c * c) := by
        rw [hs2, powAdd2 c (twoN - (gR i + 2))]
      have hW : a * a * dth * trialAt twoN a c dR gR i
          = dth * dR i
            * (ground.prodOver (fun _ => a) (List.range (gR i + 2))
              * ground.prodOver (fun _ => c)
                  (List.range (twoN - (gR i + 2))) * (c * c)) := by
        rw [trial_of twoN a c dR gR i hgi, powAdd2 a (gR i),
          ground.mulAssoc
            (ground.prodOver (fun _ => a) (List.range (gR i)) * (a * a))
            (ground.prodOver (fun _ => c)
              (List.range (twoN - (gR i + 2)))) (c * c),
          ← hP2]
        exact mulRearr5 (a * a) dth (dR i)
          (ground.prodOver (fun _ => a) (List.range (gR i)))
          (ground.prodOver (fun _ => c) (List.range (twoN - gR i)))
      have hmain : a * a * dth * trialAt twoN a c dR gR i
          ≤ c * c
            * ground.famFold Nat.add 0
                (fun j => NR i j * trialAt twoN a c dR gR j)
                (List.range o) := by
        rw [hW, ← hdim i hio hlt,
          ← ground.famFold_mulR
            (ground.prodOver (fun _ => a) (List.range (gR i + 2))
              * ground.prodOver (fun _ => c)
                  (List.range (twoN - (gR i + 2))) * (c * c))
            (fun j => NR i j * dR j) (List.range o),
          ground.famFold_mul (c * c)
            (fun j => NR i j * trialAt twoN a c dR gR j) (List.range o)]
        refine ground.famFold_le _ _ (List.range o) (fun j hj => ?_)
        have hjo : j < o := ground.ltOfMemRange hj
        by_cases hn : 0 < NR i j
        · have hgj : gR j ≤ gR i + 2 := hmove i j hio hjo hn
          have hgjN : gR j ≤ twoN := Nat.le_trans hgj hlt
          rw [trial_of twoN a c dR gR j hgjN,
            mulRearrR (c * c) (NR i j) (dR j)
              (ground.prodOver (fun _ => a) (List.range (gR j)))
              (ground.prodOver (fun _ => c) (List.range (twoN - gR j)))]
          exact Nat.mul_le_mul_left (NR i j * dR j)
            (Nat.mul_le_mul
              (powMono a c twoN hac (gR j) (gR i + 2) hgj hlt)
              (Nat.le_refl (c * c)))
        · have hz : NR i j = 0 :=
            Nat.eq_zero_of_not_pos hn
          rw [hz, Nat.zero_mul, Nat.zero_mul]
          exact Nat.zero_le _
      rw [if_neg htop, Nat.mul_zero, Nat.add_zero,
        ← ground.mulAssoc (a * a * dth) (trialAt twoN a c dR gR i)
          (trialAt twoN a c dR gR i),
        Nat.mul_comm (trialAt twoN a c dR gR i)
          (ground.famFold Nat.add 0
            (fun j => NR i j * trialAt twoN a c dR gR j)
            (List.range o)),
        ← ground.mulAssoc (c * c)
          (ground.famFold Nat.add 0
            (fun j => NR i j * trialAt twoN a c dR gR j)
            (List.range o)) (trialAt twoN a c dR gR i)]
      exact Nat.mul_le_mul hmain (Nat.le_refl _)
  show a * a * dth * ground.famFold Nat.add 0
      (fun i => trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
      (List.range o)
    ≤ c * c * ground.famFold Nat.add 0
        (fun i => trialAt twoN a c dR gR i
          * ground.famFold Nat.add 0
              (fun j => NR i j * trialAt twoN a c dR gR j)
              (List.range o))
        (List.range o)
      + a * a * dth * ground.famFold Nat.add 0
        (fun i => if twoN ≤ gR i + 1
          then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
          else 0)
        (List.range o)
  rw [ground.famFold_mul (a * a * dth)
      (fun i => trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
      (List.range o),
    ground.famFold_mul (c * c)
      (fun i => trialAt twoN a c dR gR i
        * ground.famFold Nat.add 0
            (fun j => NR i j * trialAt twoN a c dR gR j)
            (List.range o))
      (List.range o),
    ground.famFold_mul (a * a * dth)
      (fun i => if twoN ≤ gR i + 1
        then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
        else 0)
      (List.range o),
    ← ground.famFold_add_split
      (fun i => c * c
        * (trialAt twoN a c dR gR i
          * ground.famFold Nat.add 0
              (fun j => NR i j * trialAt twoN a c dR gR j)
              (List.range o)))
      (fun i => a * a * dth
        * (if twoN ≤ gR i + 1
          then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
          else 0))
      (List.range o)]
  exact ground.famFold_le _ _ (List.range o) key

/-- A constant's power at a doubled reach is its own square. -/
private theorem powSq (C n : Nat) :
    ground.prodOver (fun _ => C) (List.range (2 * n))
      = ground.prodOver (fun _ => C) (List.range n)
        * ground.prodOver (fun _ => C) (List.range n) := by
  rw [Nat.two_mul n, ground.prodConst_split C n n]

/-- A four-factor product's square splits at its factors' own. -/
private theorem sqRearr4 (u v w x : Nat) :
    u * v * w * x * (u * v * w * x)
      = u * u * (v * v) * (w * x * (w * x)) := by
  rw [ground.mulAssoc (u * v) w x,
    ground.mulMulMulComm (u * v) (w * x) (u * v) (w * x),
    ground.mulMulMulComm u v u v]

/-- The squared rows at one key sit at or below the key's own row
fold squared. -/
private theorem sqKeyFold (o k : Nat) (gR f : Nat → Nat) :
    ground.famFold Nat.add 0
        (fun i => if gR i == k then f i * f i else 0) (List.range o)
      ≤ ground.famFold Nat.add 0
          (fun i => if gR i == k then f i else 0) (List.range o)
        * ground.famFold Nat.add 0
          (fun i => if gR i == k then f i else 0) (List.range o) := by
  refine Nat.le_trans (Nat.le_of_eq
    (ground.famFold_congr_all Nat.add 0 _
      (fun i => (if gR i == k then f i else 0)
        * (if gR i == k then f i else 0)) (fun i => ?_) (List.range o)))
    (sqFoldLe (fun i => if gR i == k then f i else 0) (List.range o))
  cases hb : (gR i == k) with
  | true => rfl
  | false => exact (Nat.zero_mul 0).symm

/-- The rows at one key: the squared coefficients' fold sits at or
below the key count's cap against the split powers. -/
private theorem topKey (o twoN a c A p k : Nat) (dR gR : Nat → Nat)
    (hk : k ≤ twoN)
    (hcnt : ground.famFold Nat.add 0
        (fun i => if gR i == k then dR i else 0) (List.range o)
      ≤ A * ground.prodOver (fun _ => k + 1) (List.range p)) :
    ground.famFold Nat.add 0
        (fun i => if gR i == k
          then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
          else 0) (List.range o)
      ≤ A * A * ground.prodOver (fun _ => k + 1) (List.range (2 * p))
        * (ground.prodOver (fun _ => a) (List.range k)
            * ground.prodOver (fun _ => c) (List.range (twoN - k))
          * (ground.prodOver (fun _ => a) (List.range k)
            * ground.prodOver (fun _ => c)
                (List.range (twoN - k)))) := by
  have hS : ground.famFold Nat.add 0
        (fun i => if gR i == k then trialAt twoN a c dR gR i else 0)
        (List.range o)
      ≤ A * ground.prodOver (fun _ => k + 1) (List.range p)
        * ground.prodOver (fun _ => a) (List.range k)
        * ground.prodOver (fun _ => c) (List.range (twoN - k)) := by
    rw [keySum o twoN a c k dR gR hk]
    exact Nat.mul_le_mul (Nat.mul_le_mul hcnt (Nat.le_refl _))
      (Nat.le_refl _)
  refine Nat.le_trans (sqKeyFold o k gR (trialAt twoN a c dR gR)) ?_
  refine Nat.le_trans (Nat.mul_le_mul hS hS) ?_
  rw [sqRearr4 A (ground.prodOver (fun _ => k + 1) (List.range p))
      (ground.prodOver (fun _ => a) (List.range k))
      (ground.prodOver (fun _ => c) (List.range (twoN - k))),
    ← powSq (k + 1) p]
  exact Nat.le_refl _

/-- A four-factor product's outer exchange, `u v (w z) = v w (u z)`. -/
private theorem mulSwapOuter (u v w z : Nat) :
    u * v * (w * z) = v * w * (u * z) := by
  repeat rw [ground.mulAssoc]
  rw [ground.mulLeftComm w u z, ground.mulLeftComm v u (w * z)]

/-- The boundary part splits at the top two key values: a row of
the boundary carries the top key or the one below it. -/
private theorem topSplit (o twoN a c : Nat) (dR gR : Nat → Nat) :
    topFold o twoN a c dR gR
      ≤ ground.famFold Nat.add 0
          (fun i => if gR i == twoN
            then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
            else 0) (List.range o)
        + ground.famFold Nat.add 0
          (fun i => if gR i == twoN - 1
            then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
            else 0) (List.range o) := by
  rw [← ground.famFold_add_split
    (fun i => if gR i == twoN
      then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i else 0)
    (fun i => if gR i == twoN - 1
      then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i else 0)
    (List.range o)]
  refine ground.famFold_le _ _ (List.range o) (fun i _ => ?_)
  by_cases htop : twoN ≤ gR i + 1
  · by_cases hw : gR i ≤ twoN
    · by_cases he : gR i = twoN
      · rw [if_pos htop, if_pos (ground.eqBeqOf he)]
        exact Nat.le_add_right _ _
      · have h2 : twoN = gR i + 1 :=
          Nat.le_antisymm htop
            (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hw he))
        have he2 : gR i = twoN - 1 := by
          rw [h2, ground.addSubSelfR (gR i) 1]
        rw [if_pos htop, if_pos (ground.eqBeqOf he2)]
        exact Nat.le_add_left _ _
    · rw [trial_off twoN a c dR gR i hw, if_pos htop, Nat.zero_mul]
      exact Nat.zero_le _
  · rw [if_neg htop]
    exact Nat.zero_le _

/-- The boundary term's price: at the counts' squares and the
weighted power comparison the top two key values' part sits at or
below the gap's multiple of the whole power (`lem:corner`'s
boundary clause at the certificate's first comparison). -/
theorem top_cap (o twoN a b c dth A p : Nat) (dR gR : Nat → Nat)
    (hac : a ≤ c)
    (hcntT : ground.famFold Nat.add 0
        (fun i => if gR i == twoN then dR i else 0) (List.range o)
      ≤ A * ground.prodOver (fun _ => twoN + 1) (List.range p))
    (hcntU : ground.famFold Nat.add 0
        (fun i => if gR i == twoN - 1 then dR i else 0) (List.range o)
      ≤ A * ground.prodOver (fun _ => twoN - 1 + 1) (List.range p))
    (hcert : 2 * dth * (A * A)
        * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p))
        * ground.prodOver (fun _ => a) (List.range (2 * twoN)) * c
      ≤ b * ground.prodOver (fun _ => c) (List.range (2 * twoN))) :
    a * a * dth * topFold o twoN a c dR gR
      ≤ b * ground.prodOver (fun _ => c)
          (List.range (2 * twoN + 1)) := by
  have hX1 : a * a
      * (ground.prodOver (fun _ => a) (List.range twoN)
          * ground.prodOver (fun _ => c) (List.range (twoN - twoN))
        * (ground.prodOver (fun _ => a) (List.range twoN)
          * ground.prodOver (fun _ => c) (List.range (twoN - twoN))))
      ≤ ground.prodOver (fun _ => a) (List.range (2 * twoN))
        * (c * c) := by
    rw [Nat.sub_self twoN]
    show a * a
        * (ground.prodOver (fun _ => a) (List.range twoN) * 1
          * (ground.prodOver (fun _ => a) (List.range twoN) * 1))
      ≤ ground.prodOver (fun _ => a) (List.range (2 * twoN)) * (c * c)
    rw [Nat.mul_one, ← powSq a twoN,
      Nat.mul_comm (ground.prodOver (fun _ => a) (List.range (2 * twoN)))
        (c * c)]
    exact Nat.mul_le_mul (Nat.mul_le_mul hac hac) (Nat.le_refl _)
  have hX2 : a * a
      * (ground.prodOver (fun _ => a) (List.range (twoN - 1))
          * ground.prodOver (fun _ => c)
              (List.range (twoN - (twoN - 1)))
        * (ground.prodOver (fun _ => a) (List.range (twoN - 1))
          * ground.prodOver (fun _ => c)
              (List.range (twoN - (twoN - 1)))))
      ≤ ground.prodOver (fun _ => a) (List.range (2 * twoN))
        * (c * c) := by
    cases twoN with
    | zero =>
      show a * a * (1 * 1 * (1 * 1)) ≤ 1 * (c * c)
      rw [Nat.mul_one, Nat.one_mul]
      exact Nat.mul_le_mul hac hac
    | succ m =>
      rw [ground.addSubSelfR m 1, ground.addSubSelfL m 1, powOne c,
        Nat.mul_succ 2 m, powAdd2 a (2 * m),
        ground.mulMulMulComm
          (ground.prodOver (fun _ => a) (List.range m)) c
          (ground.prodOver (fun _ => a) (List.range m)) c,
        ← powSq a m]
      refine Nat.le_of_eq ?_
      repeat rw [ground.mulAssoc]
      rw [ground.mulLeftComm a
          (ground.prodOver (fun _ => a) (List.range (2 * m))) (c * c),
        ground.mulLeftComm a
          (ground.prodOver (fun _ => a) (List.range (2 * m)))
          (a * (c * c))]
  refine Nat.le_trans (Nat.mul_le_mul_left (a * a * dth)
    (topSplit o twoN a c dR gR)) ?_
  have hUp : ∀ k : Nat, k ≤ twoN → ∀ X : Nat,
      A * A * ground.prodOver (fun _ => k + 1) (List.range (2 * p)) * X
        ≤ A * A
            * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p))
          * X :=
    fun k hk X => Nat.mul_le_mul
      (Nat.mul_le_mul_left (A * A)
        (ground.prodOver_le _ _ (List.range (2 * p))
          (fun _ _ => Nat.succ_le_succ hk)))
      (Nat.le_refl X)
  refine Nat.le_trans (Nat.mul_le_mul_left (a * a * dth)
    (Nat.add_le_add
      (Nat.le_trans
        (topKey o twoN a c A p twoN dR gR (Nat.le_refl twoN) hcntT)
        (hUp twoN (Nat.le_refl twoN) _))
      (Nat.le_trans
        (topKey o twoN a c A p (twoN - 1) dR gR (Nat.sub_le twoN 1)
          hcntU)
        (hUp (twoN - 1) (Nat.sub_le twoN 1) _)))) ?_
  rw [Nat.left_distrib (a * a * dth)
      (A * A * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p))
        * (ground.prodOver (fun _ => a) (List.range twoN)
            * ground.prodOver (fun _ => c) (List.range (twoN - twoN))
          * (ground.prodOver (fun _ => a) (List.range twoN)
            * ground.prodOver (fun _ => c)
                (List.range (twoN - twoN)))))
      (A * A * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p))
        * (ground.prodOver (fun _ => a) (List.range (twoN - 1))
            * ground.prodOver (fun _ => c)
                (List.range (twoN - (twoN - 1)))
          * (ground.prodOver (fun _ => a) (List.range (twoN - 1))
            * ground.prodOver (fun _ => c)
                (List.range (twoN - (twoN - 1)))))),
    mulSwapOuter (a * a) dth
      (A * A * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p)))
      (ground.prodOver (fun _ => a) (List.range twoN)
          * ground.prodOver (fun _ => c) (List.range (twoN - twoN))
        * (ground.prodOver (fun _ => a) (List.range twoN)
          * ground.prodOver (fun _ => c) (List.range (twoN - twoN)))),
    mulSwapOuter (a * a) dth
      (A * A * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p)))
      (ground.prodOver (fun _ => a) (List.range (twoN - 1))
          * ground.prodOver (fun _ => c)
              (List.range (twoN - (twoN - 1)))
        * (ground.prodOver (fun _ => a) (List.range (twoN - 1))
          * ground.prodOver (fun _ => c)
              (List.range (twoN - (twoN - 1)))))]
  refine Nat.le_trans (Nat.add_le_add
    (Nat.mul_le_mul_left (dth
      * (A * A
        * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p))))
      hX1)
    (Nat.mul_le_mul_left (dth
      * (A * A
        * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p))))
      hX2)) ?_
  rw [← Nat.two_mul (dth
      * (A * A
        * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p)))
      * (ground.prodOver (fun _ => a) (List.range (2 * twoN))
        * (c * c))),
    powStep c (2 * twoN),
    ← ground.mulAssoc b
      (ground.prodOver (fun _ => c) (List.range (2 * twoN))) c]
  refine Nat.le_trans (Nat.le_of_eq ?_)
    (Nat.mul_le_mul hcert (Nat.le_refl c))
  repeat rw [ground.mulAssoc]

/-- Two constants' powers at one reach join at the constants'
product. -/
private theorem powMulPair (x y : Nat) : ∀ n : Nat,
    ground.prodOver (fun _ => x) (List.range n)
        * ground.prodOver (fun _ => y) (List.range n)
      = ground.prodOver (fun _ => x * y) (List.range n)
  | 0 => Nat.mul_one 1
  | n + 1 => by
    rw [powStep x n, powStep y n, powStep (x * y) n,
      ground.mulMulMulComm
        (ground.prodOver (fun _ => x) (List.range n)) x
        (ground.prodOver (fun _ => y) (List.range n)) y,
      powMulPair x y n]

/-- A key's square against the count's unit sits at or below the
raised key's square. -/
private theorem sqStep (g : Nat) : g * g + 1 ≤ (g + 1) * (g + 1) := by
  rw [ground.sqAdd g 1, Nat.mul_one, Nat.mul_one]
  exact Nat.add_le_add_right (Nat.le_add_right (g * g) (2 * g)) 1

/-- A four-factor product's key exchange,
`s (R Q X) = R (Q s) X`. -/
private theorem mulRearrKey (s R Q X : Nat) :
    s * (R * Q * X) = R * (Q * s) * X := by
  repeat rw [ground.mulAssoc]
  rw [ground.mulLeftComm Q s X, ground.mulLeftComm R s (Q * X)]

/-- A four-factor product's tail exchange, `u v w z = u z (v w)`. -/
private theorem mulRearrL (u v w z : Nat) :
    u * v * w * z = u * z * (v * w) := by
  repeat rw [ground.mulAssoc]
  rw [ground.mulLeftComm z v w, Nat.mul_comm z w]

/-- The doubled reach at a stepped length splits into two equal
segments. -/
private theorem reachSplit (n t : Nat) :
    2 * (n + t + 1) = 2 * n + (t + 1) + (t + 1) := by
  rw [Nat.two_mul (n + t + 1), Nat.two_mul n, Nat.add_assoc n t 1,
    ground.addJoinHeadFront n (t + 1) n (t + 1),
    Nat.add_assoc (n + n) (t + 1) (t + 1)]

/-- The electric rows collect at the graded sum: the diagonal cap
prices each row at its key's raised square, and the key counts
price the squared coefficients at the rising-product weights. -/
private theorem elecKey (o twoN a c A p KN KD : Nat)
    (dR gR eR : Nat → Nat)
    (he : ∀ i, i < o → eR i * KD ≤ KN * (gR i * gR i + 1))
    (hcnt : ∀ k, k ≤ twoN →
      ground.famFold Nat.add 0
          (fun i => if gR i == k then dR i else 0) (List.range o)
        ≤ A * ground.prodOver (fun _ => k + 1) (List.range p)) :
    KD * elecFold o twoN a c dR gR eR
      ≤ KN * (A * A)
        * gradSum (2 * p + 2) twoN (a * a) (c * c) := by
  have hstep : KD * elecFold o twoN a c dR gR eR
      ≤ KN * ground.famFold Nat.add 0
          (fun i => (gR i + 1) * (gR i + 1)
            * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
          (List.range o) := by
    show KD * ground.famFold Nat.add 0
        (fun i => eR i
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
        (List.range o)
      ≤ KN * ground.famFold Nat.add 0
          (fun i => (gR i + 1) * (gR i + 1)
            * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
          (List.range o)
    rw [ground.famFold_mul KD
        (fun i => eR i
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
        (List.range o),
      ground.famFold_mul KN
        (fun i => (gR i + 1) * (gR i + 1)
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
        (List.range o)]
    refine ground.famFold_le _ _ (List.range o) (fun i hi => ?_)
    rw [ground.mulHeadComm KD (eR i)
        (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i),
      ← ground.mulAssoc KN ((gR i + 1) * (gR i + 1))
        (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)]
    exact Nat.mul_le_mul (Nat.le_trans (he i (ground.ltOfMemRange hi))
      (Nat.mul_le_mul_left KN (sqStep (gR i)))) (Nat.le_refl _)
  refine Nat.le_trans hstep ?_
  rw [ground.mulAssoc KN (A * A)
      (gradSum (2 * p + 2) twoN (a * a) (c * c))]
  refine Nat.mul_le_mul_left KN ?_
  rw [keyGroup o twoN gR
    (fun i => (gR i + 1) * (gR i + 1)
      * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
    (fun i hi => by
      rw [trial_off twoN a c dR gR i (fun hle =>
          absurd (Nat.lt_of_lt_of_le hi hle) (Nat.lt_irrefl twoN)),
        Nat.mul_zero])]
  show ground.famFold Nat.add 0
      (fun k => ground.famFold Nat.add 0
        (fun i => if gR i == k
          then (gR i + 1) * (gR i + 1)
            * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
          else 0) (List.range o))
      (List.range (twoN + 1))
    ≤ A * A * ground.famFold Nat.add 0
        (fun k => ground.rise (k + 1) (2 * p + 2)
          * ground.prodOver (fun _ => a * a) (List.range k)
          * ground.prodOver (fun _ => c * c) (List.range (twoN - k)))
        (List.range (twoN + 1))
  rw [ground.famFold_mul (A * A)
    (fun k => ground.rise (k + 1) (2 * p + 2)
      * ground.prodOver (fun _ => a * a) (List.range k)
      * ground.prodOver (fun _ => c * c) (List.range (twoN - k)))
    (List.range (twoN + 1))]
  refine ground.famFold_le _ _ (List.range (twoN + 1)) (fun k hk => ?_)
  have hkN : k ≤ twoN := Nat.le_of_lt_succ (ground.ltOfMemRange hk)
  have hrow : ground.famFold Nat.add 0
      (fun i => if gR i == k
        then (gR i + 1) * (gR i + 1)
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
        else 0) (List.range o)
      = (k + 1) * (k + 1) * ground.famFold Nat.add 0
          (fun i => if gR i == k
            then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
            else 0) (List.range o) := by
    rw [ground.famFold_mul ((k + 1) * (k + 1))
      (fun i => if gR i == k
        then trialAt twoN a c dR gR i * trialAt twoN a c dR gR i
        else 0) (List.range o)]
    refine ground.famFold_congr_all Nat.add 0 _ _
      (fun i => ?_) (List.range o)
    cases hb : (gR i == k) with
    | true =>
      show (gR i + 1) * (gR i + 1)
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
        = (k + 1) * (k + 1)
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i)
      rw [ground.beqEqOf hb]
    | false =>
      show (0 : Nat) = (k + 1) * (k + 1) * 0
      rw [Nat.mul_zero]
  rw [hrow]
  refine Nat.le_trans (Nat.mul_le_mul_left ((k + 1) * (k + 1))
    (topKey o twoN a c A p k dR gR hkN (hcnt k hkN))) ?_
  rw [mulRearrKey ((k + 1) * (k + 1)) (A * A)
      (ground.prodOver (fun _ => k + 1) (List.range (2 * p)))
      (ground.prodOver (fun _ => a) (List.range k)
          * ground.prodOver (fun _ => c) (List.range (twoN - k))
        * (ground.prodOver (fun _ => a) (List.range k)
          * ground.prodOver (fun _ => c) (List.range (twoN - k)))),
    ← powAdd2 (k + 1) (2 * p),
    ground.mulMulMulComm
      (ground.prodOver (fun _ => a) (List.range k))
      (ground.prodOver (fun _ => c) (List.range (twoN - k)))
      (ground.prodOver (fun _ => a) (List.range k))
      (ground.prodOver (fun _ => c) (List.range (twoN - k))),
    powMulPair a a k, powMulPair c c (twoN - k),
    ground.mulAssoc (ground.rise (k + 1) (2 * p + 2))
      (ground.prodOver (fun _ => a * a) (List.range k))
      (ground.prodOver (fun _ => c * c) (List.range (twoN - k))),
    ← ground.mulAssoc (A * A) (ground.rise (k + 1) (2 * p + 2))
      (ground.prodOver (fun _ => a * a) (List.range k)
        * ground.prodOver (fun _ => c * c) (List.range (twoN - k)))]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left (A * A)
    (powLeRise k (2 * p + 2))) (Nat.le_refl _)

/-- The electric read's close at the two displayed reads: the
Casimir cap against the squared counts, the power cap and the
Pascal descent closing the weighted geometric sum (`lem:corner`'s
electric display, cleared). -/
theorem elec_cap (o twoN a b c A p KN KD : Nat)
    (dR gR eR : Nat → Nat) (hc : a + b = c)
    (he : ∀ i, i < o → eR i * KD ≤ KN * (gR i * gR i + 1))
    (hcnt : ∀ k, k ≤ twoN →
      ground.famFold Nat.add 0
          (fun i => if gR i == k then dR i else 0) (List.range o)
        ≤ A * ground.prodOver (fun _ => k + 1) (List.range p)) :
    ground.prodOver (fun _ => b) (List.range (2 * p + 3)) * KD
        * elecFold o twoN a c dR gR eR
      ≤ KN * (A * A) * ground.rise 1 (2 * p + 2)
        * ground.prodOver (fun _ => c)
            (List.range (2 * twoN + (2 * p + 3))) := by
  by_cases hc0 : 0 < c
  · have hpos : 0 < ground.prodOver (fun _ => c)
        (List.range (2 * p + 3)) :=
      ground.prodOver_pos (fun _ => c) (List.range (2 * p + 3))
        (fun _ _ => hc0)
    have hid : a * a + b * (a + c) = c * c := by
      rw [Nat.left_distrib b a c,
        ← Nat.add_assoc (a * a) (b * a) (b * c),
        ← ground.mulAddR a b a, hc, Nat.mul_comm c a,
        ← ground.mulAddR a b c, hc]
    have hcc : ground.prodOver (fun _ => c * c)
          (List.range (twoN + (2 * p + 2) + 1))
        = ground.prodOver (fun _ => c)
            (List.range (2 * twoN + (2 * p + 3)))
          * ground.prodOver (fun _ => c) (List.range (2 * p + 3)) := by
      show ground.prodOver (fun _ => c * c)
            (List.range (twoN + (2 * p + 2) + 1))
          = ground.prodOver (fun _ => c)
              (List.range (2 * twoN + (2 * p + 2 + 1)))
            * ground.prodOver (fun _ => c)
                (List.range (2 * p + 2 + 1))
      rw [← powMulPair c c (twoN + (2 * p + 2) + 1),
        ← powSq c (twoN + (2 * p + 2) + 1), reachSplit twoN (2 * p + 2),
        ground.prodConst_split c (2 * twoN + (2 * p + 2 + 1))
          (2 * p + 2 + 1)]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    rw [mulRearrL (ground.prodOver (fun _ => b) (List.range (2 * p + 3)))
        KD (elecFold o twoN a c dR gR eR)
        (ground.prodOver (fun _ => c) (List.range (2 * p + 3))),
      powMulPair b c (2 * p + 3)]
    refine Nat.le_trans (Nat.mul_le_mul
      (ground.prodOver_le _ _ (List.range (2 * p + 3))
        (fun _ _ => Nat.mul_le_mul_left b (Nat.le_add_left c a)))
      (elecKey o twoN a c A p KN KD dR gR eR he hcnt)) ?_
    rw [ground.mulLeftComm
      (ground.prodOver (fun _ => b * (a + c)) (List.range (2 * p + 3)))
      (KN * (A * A)) (gradSum (2 * p + 2) twoN (a * a) (c * c))]
    refine Nat.le_trans (Nat.mul_le_mul_left (KN * (A * A))
      (gradSum_close (2 * p + 2) twoN (a * a) (b * (a + c)) (c * c)
        hid)) ?_
    refine Nat.le_of_eq ?_
    rw [hcc]
    repeat rw [ground.mulAssoc]
  · have hab : a + b = 0 := by
      rw [hc]
      exact Nat.eq_zero_of_not_pos hc0
    have hb0 : b = 0 := by
      have h1 : b ≤ a + b := Nat.le_add_left b a
      rw [hab] at h1
      exact Nat.le_antisymm h1 (Nat.zero_le b)
    rw [hb0]
    show ground.prodOver (fun _ => 0) (List.range (2 * p + 2 + 1)) * KD
        * elecFold o twoN a c dR gR eR
      ≤ KN * (A * A) * ground.rise 1 (2 * p + 2)
        * ground.prodOver (fun _ => c)
            (List.range (2 * twoN + (2 * p + 3)))
    rw [powStep 0 (2 * p + 2), Nat.mul_zero, Nat.zero_mul, Nat.zero_mul]
    exact Nat.zero_le _

/-! `lem:corner`'s Rayleigh close: the dimension-weighted family
enters the head pencil as a witness vector, its three quadratic
reads are the fold data, and a lower-side witness occupies the
count.  The drift's rate closes at the power comparison, the
positive carrier's own fold. -/

/-- The trial family as the head's coefficient vector, one entry
per row. -/
def trialVec (o twoN a c : Nat) (dR gR : Nat → Nat) :
    List ground.BPair :=
  (List.range o).map
    (fun i => ground.BPair.ofNat (trialAt twoN a c dR gR i))


/-- The plain pairing at a count row and a count vector: the
entries' fold read at the counts' own. -/
private theorem rowNat (o : Nat) (G : Nat → Nat) (v : Nat → Nat) :
    (elim.dotN ((List.range o).map (fun j => ground.BPair.ofNat (G j)))
        ((List.range o).map
          (fun j => ground.BPair.ofNat (v j)))).oneValue
      (ground.BPair.ofNat
        (ground.famFold Nat.add 0 (fun j => G j * v j)
          (List.range o))) := by
  refine BPair.oneValue_trans (elim.dotN_dotP _ _) ?_
  rw [elim.dotP_map_pair (fun j => ground.BPair.ofNat (G j))
    (fun j => ground.BPair.ofNat (v j)) (List.range o)]
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (ground.ofNat_famFold (fun j => G j * v j) (List.range o)) ?_
  exact ground.foldB_congr_members _ _ (List.range o)
    (fun j _ => BPair.ofNat_mul (G j) (v j))

/-- The quadratic form at a count matrix and a count vector: the
row-against-row double fold read at the counts' own. -/
private theorem quadNat (o : Nat) (F : Nat → Nat → Nat)
    (v : Nat → Nat) :
    (inertia.quadForm
        (ground.matOf o o (fun i j => ground.BPair.ofNat (F i j)))
        ((List.range o).map
          (fun i => ground.BPair.ofNat (v i)))).oneValue
      (ground.BPair.ofNat
        (ground.famFold Nat.add 0
          (fun i => v i
            * ground.famFold Nat.add 0 (fun j => F i j * v j)
                (List.range o))
          (List.range o))) := by
  show (elim.dotN
      ((List.range o).map (fun i => ground.BPair.ofNat (v i)))
      (elim.matVec
        (ground.matOf o o (fun i j => ground.BPair.ofNat (F i j)))
        ((List.range o).map
          (fun i => ground.BPair.ofNat (v i))))).oneValue _
  rw [show elim.matVec
        (ground.matOf o o (fun i j => ground.BPair.ofNat (F i j)))
        ((List.range o).map (fun i => ground.BPair.ofNat (v i)))
      = (List.range o).map (fun i =>
          elim.dotN ((List.range o).map
              (fun j => ground.BPair.ofNat (F i j)))
            ((List.range o).map
              (fun i => ground.BPair.ofNat (v i)))) from
    ground.map_map _ _ (List.range o)]
  refine BPair.oneValue_trans (elim.dotN_dotP _ _) ?_
  rw [elim.dotP_map_pair (fun i => ground.BPair.ofNat (v i))
    (fun i => elim.dotN ((List.range o).map
        (fun j => ground.BPair.ofNat (F i j)))
      ((List.range o).map (fun i => ground.BPair.ofNat (v i))))
    (List.range o)]
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans
    (ground.ofNat_famFold _ (List.range o)) ?_
  refine ground.foldB_congr_members _ _ (List.range o)
    (fun i _ => ?_)
  refine BPair.oneValue_trans
    (BPair.ofNat_mul (v i)
      (ground.famFold Nat.add 0 (fun j => F i j * v j)
        (List.range o))) ?_
  exact BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (rowNat o (fun j => F i j) v))

/-- The diagonal head's quadratic read at the trial vector is the
electric fold. -/
theorem quad_diag (o twoN a c : Nat) (dR gR eR : Nat → Nat) :
    (inertia.quadForm
        (ground.matOf o o (fun i j =>
          if i == j then ground.BPair.ofNat (eR i)
          else ground.BPair.unit))
        (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat (elecFold o twoN a c dR gR eR)) := by
  have hM : ground.matOf o o (fun i j =>
        if i == j then ground.BPair.ofNat (eR i)
        else ground.BPair.unit)
      = ground.matOf o o (fun i j =>
        ground.BPair.ofNat (if i == j then eR i else 0)) := by
    refine ground.matOf_congr o o _ _ (fun i j _ _ => ?_)
    by_cases hbq : (i == j) = true
    · rw [if_pos hbq, if_pos hbq]
    · rw [if_neg hbq, if_neg hbq]
      rfl
  rw [hM]
  refine BPair.oneValue_trans
    (quadNat o (fun i j => if i == j then eR i else 0)
      (trialAt twoN a c dR gR)) ?_
  refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
  refine ground.famFold_congr_range _ _ o (fun i hi => ?_)
  rw [ground.famFold_pick_of
      (fun j => (if i == j then eR i else 0)
        * trialAt twoN a c dR gR j) i (List.range o)
      (ground.countOf_range_one hi)
      (fun w _ hwi => by
        rw [if_neg (fun hbq => hwi (ground.beqEqOf hbq).symm),
          Nat.zero_mul]),
    if_pos (ground.eqBeqOf (rfl : i = i)),
    ground.mulLeftComm (trialAt twoN a c dR gR i) (eR i)
      (trialAt twoN a c dR gR i)]

/-- The identity gram's quadratic read at the trial vector is the
pairing fold. -/
theorem quad_gram (o twoN a c : Nat) (dR gR : Nat → Nat) :
    (inertia.quadForm (inertia.idMat o)
        (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat (pairFold o twoN a c dR gR)) := by
  have hM : inertia.idMat o
      = ground.matOf o o (fun i j =>
        ground.BPair.ofNat (if j = i then 1 else 0)) := by
    show ground.matOf o o (fun i j =>
        if j = i then ground.BPair.ofNat 1 else ground.BPair.unit)
      = ground.matOf o o (fun i j =>
        ground.BPair.ofNat (if j = i then 1 else 0))
    refine ground.matOf_congr o o _ _ (fun i j _ _ => ?_)
    by_cases hbq : j = i
    · rw [if_pos hbq, if_pos hbq]
    · rw [if_neg hbq, if_neg hbq]
      rfl
  rw [hM]
  refine BPair.oneValue_trans
    (quadNat o (fun i j => if j = i then 1 else 0)
      (trialAt twoN a c dR gR)) ?_
  refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
  refine ground.famFold_congr_range _ _ o (fun i hi => ?_)
  rw [ground.famFold_pick_of
      (fun j => (if j = i then 1 else 0) * trialAt twoN a c dR gR j)
      i (List.range o) (ground.countOf_range_one hi)
      (fun w _ hwi => by rw [if_neg hwi, Nat.zero_mul]),
    if_pos (rfl : i = i), Nat.one_mul]

/-- The row head's quadratic read at the trial vector is the
magnetic fold. -/
theorem quad_rows (o twoN a c : Nat) (dR gR : Nat → Nat)
    (NR : Nat → Nat → Nat) :
    (inertia.quadForm
        (ground.matOf o o (fun i j => ground.BPair.ofNat (NR i j)))
        (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat (magFold o twoN a c dR gR NR)) :=
  quadNat o NR (trialAt twoN a c dR gR)

/-- A datum below another joins the second's swap below the sum's
unit, the gap carried across unchanged. -/
private theorem ltUnit_of_lt {L R : ground.BPair} (h : L < R) :
    L + R.swap < ground.BPair.unit :=
  BPair.lt_congr (BPair.oneValue_refl _)
    (ground.unitOfOne (BPair.oneValue_refl R))
    (ground.ltB_add h (ground.leB_refl R.swap))

/-- A lower-side quadratic witness occupies the count: at the
counted pair a trial vector reading the site below the unit forces
the reversal (`lem:inertia`'s forcing clause at the one-row
list). -/
theorem rayleigh_count {o : Nat} (H G : elim.Mat) (x y : ground.Pos)
    (n : Nat) (sp : inertia.Split o) (phi : List ground.BPair)
    (hlen : phi.length = o)
    (hcount : certconstruct.countAtPair H G x y n sp)
    (hq : inertia.quadForm H phi
        + ground.BPair.ofPos y * inertia.quadForm G phi
      < ground.BPair.ofPos x * inertia.quadForm G phi) :
    1 ≤ n := by
  obtain ⟨hHsq, hGsq, hsplit, hrev⟩ := hcount
  have hyG : elim.sqAt (inertia.matScale y G) o :=
    inertia.sqAt_matScale o y G hGsq
  have hxG : elim.sqAt (inertia.matScale x G) o :=
    inertia.sqAt_matScale o x G hGsq
  have hXsq : elim.sqAt (elim.matAdd H (inertia.matScale y G)) o :=
    elim.sqAt_matAdd o H (inertia.matScale y G) hHsq hyG
  have hsite : inertia.quadForm
      (inertia.siteDatum (elim.matAdd H (inertia.matScale y G))
        (inertia.matScale x G)) phi < ground.BPair.unit := by
    refine BPair.lt_congr
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (inertia.quadForm_site_sq hXsq hxG hlen)
          (BPair.add_congr
            (BPair.oneValue_trans
              (inertia.quadForm_add_sq hHsq hyG hlen)
              (BPair.add_congr (BPair.oneValue_refl _)
                (inertia.quadForm_ofPos y G phi)))
            (ground.swap_congr (inertia.quadForm_ofPos x G phi)))))
      (BPair.oneValue_refl ground.BPair.unit) (ltUnit_of_lt hq)
  have hstrict : ∀ cs : List ground.BPair, cs.length = [phi].length →
      ¬ poly.unitTail cs →
      elim.dotN
          (elim.combo o cs [phi])
          (elim.matVec
            (inertia.siteDatum (elim.matAdd H (inertia.matScale y G))
              (inertia.matScale x G))
            (elim.combo o cs [phi]))
        < ground.BPair.unit := by
    intro cs hcs hoff
    cases cs with
    | nil => exact absurd hcs (fun hh => Nat.noConfusion hh)
    | cons cc rest =>
    cases rest with
    | cons d t =>
      exact absurd hcs (fun hh => Nat.noConfusion (Nat.succ.inj hh))
    | nil =>
      have hcc : ¬ cc.oneValue ground.BPair.unit :=
        fun hh => hoff ⟨hh, trivial⟩
      have hOV : poly.oneValue (elim.combo o [cc] [phi])
          (elim.vecScale cc phi) := by
        show poly.oneValue
          (elim.vecAdd (elim.vecScale cc phi)
            (List.replicate o ground.BPair.unit)) (elim.vecScale cc phi)
        refine elim.vecAdd_null_right_le _ _ ?_
          (poly.unitTail_replicate o)
        rw [show (elim.vecScale cc phi).length = phi.length from
            ground.length_map _ phi,
          ground.length_replicate ground.BPair.unit o]
        exact Nat.le_of_eq hlen
      refine BPair.lt_congr
        (BPair.oneValue_symm (inertia.quad_congr _ _ _ hOV))
        (BPair.oneValue_refl ground.BPair.unit) ?_
      have hinner : (elim.dotN phi
            (elim.matVec
              (inertia.siteDatum
                (elim.matAdd H (inertia.matScale y G))
                (inertia.matScale x G))
              (elim.vecScale cc phi))).oneValue
          (cc * inertia.quadForm
            (inertia.siteDatum
              (elim.matAdd H (inertia.matScale y G))
              (inertia.matScale x G)) phi) := by
        refine BPair.oneValue_trans (elim.dotN_read phi _) ?_
        refine BPair.oneValue_trans
          (elim.dotP_oneValue_right phi _
            (elim.vecScale cc
              (elim.matVec
                (inertia.siteDatum
                  (elim.matAdd H (inertia.matScale y G))
                  (inertia.matScale x G)) phi))
            (elim.matVec_vecScale_free _ cc phi)) ?_
        refine BPair.oneValue_trans
          (elim.dotP_vecScale_right phi _ cc) ?_
        exact BPair.mul_congr (BPair.oneValue_refl cc)
          (BPair.oneValue_symm (elim.dotN_read phi _))
      have hstep : (elim.dotN (elim.vecScale cc phi)
            (elim.matVec
              (inertia.siteDatum
                (elim.matAdd H (inertia.matScale y G))
                (inertia.matScale x G))
              (elim.vecScale cc phi))).oneValue
          (inertia.quadForm
              (inertia.siteDatum
                (elim.matAdd H (inertia.matScale y G))
                (inertia.matScale x G)) phi * (cc * cc)) := by
        refine BPair.oneValue_trans
          (elim.dotN_scaleRow_free cc phi _) ?_
        refine BPair.oneValue_trans
          (BPair.mul_congr (BPair.oneValue_refl cc) hinner) ?_
        rw [← BPair.mul_assoc,
          BPair.mul_comm (cc * cc)
            (inertia.quadForm
              (inertia.siteDatum
                (elim.matAdd H (inertia.matScale y G))
                (inertia.matScale x G)) phi)]
        exact BPair.oneValue_refl _
      refine BPair.lt_congr (BPair.oneValue_symm hstep)
        (BPair.unit_mul (cc * cc)) ?_
      exact ground.ltB_mulPos hsite (ground.sq_pos hcc)
  have hfin := inertia.forcing
    (inertia.siteDatum (elim.matAdd H (inertia.matScale y G))
      (inertia.matScale x G)) sp hsplit [phi] ⟨hlen, trivial⟩ hstrict
  rw [hrev] at hfin
  exact hfin

/-- A swapped summand crosses the order: the datum below the join
sits, with the summand's swap, below the join's first member. -/
private theorem leSwapAdd {A T Z : ground.BPair} (h : A ≤ Z + T) :
    A + T.swap ≤ Z :=
  ground.leB_congr_right
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.add_assoc Z T T.swap))
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl Z)
          (ground.unitOfOne (BPair.oneValue_refl T)))
        (BPair.add_unit Z)))
    (ground.leB_add h (ground.leB_refl T.swap))

/-- The ground display's arithmetic: the electric fold rides the
Casimir cap through the vacuum floor, the pairing rides the move
cap with the boundary term at the certificate's comparison, and the
two join at the assembled level. -/
private theorem groundArith (KD B3 B4 C5 CV CE CT KN2 Ef Mf P TF
    a b c dth sn sM : Nat)
    (hB4 : b * B3 = B4)
    (hCE : CE * (c * c) = C5 * CV)
    (hCT : CT = CV * c)
    (hE : B3 * KD * Ef ≤ KN2 * CE)
    (hM : a * a * dth * P ≤ c * c * Mf + a * a * dth * TF)
    (hT : a * a * dth * TF ≤ b * CT)
    (hV : CV ≤ P) :
    KD * B3 * (c * c) * sn * Ef + sM * KD * B3 * (a * a) * dth * P
      ≤ (sn * KN2 * C5 + sM * KD * B4 * c) * P
        + KD * B3 * (c * c) * sM * Mf := by
  have q1 : KD * B3 * (c * c) * sn * Ef
      = sn * (c * c) * (B3 * KD * Ef) := by
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm c sn Ef,
      ground.mulLeftComm c sn (c * Ef),
      ground.mulLeftComm B3 sn (c * (c * Ef)),
      ground.mulLeftComm KD sn (B3 * (c * (c * Ef))),
      ground.mulLeftComm B3 c (c * Ef),
      ground.mulLeftComm KD c (B3 * (c * Ef)),
      ground.mulLeftComm B3 c Ef,
      ground.mulLeftComm KD c (B3 * Ef),
      ground.mulLeftComm KD B3 Ef]
  have q2 : sn * (c * c) * (KN2 * CE) = sn * KN2 * (CE * (c * c)) := by
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm c KN2 CE,
      ground.mulLeftComm c KN2 (c * CE),
      Nat.mul_comm c CE,
      ground.mulLeftComm c CE c]
  have hI : KD * B3 * (c * c) * sn * Ef ≤ sn * KN2 * C5 * P := by
    rw [q1]
    refine Nat.le_trans (Nat.mul_le_mul_left (sn * (c * c)) hE) ?_
    rw [q2, hCE, ground.mulAssoc (sn * KN2) C5 P]
    exact Nat.mul_le_mul_left (sn * KN2) (Nat.mul_le_mul_left C5 hV)
  have q4 : sM * KD * B3 * (a * a) * dth * P
      = sM * KD * B3 * (a * a * dth * P) := by
    repeat rw [ground.mulAssoc]
  have q5 : sM * KD * B3 * (c * c * Mf)
      = KD * B3 * (c * c) * sM * Mf := by
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm sM KD (B3 * (c * (c * Mf))),
      ground.mulLeftComm sM B3 (c * (c * Mf)),
      ground.mulLeftComm sM c (c * Mf),
      ground.mulLeftComm sM c Mf]
  have q6 : sM * KD * B3 * (b * (CV * c)) = sM * KD * B4 * c * CV := by
    repeat rw [ground.mulAssoc]
    rw [Nat.mul_comm CV c,
      ground.mulLeftComm b c CV,
      ground.mulLeftComm B3 c (b * CV),
      Nat.mul_comm b CV,
      ground.mulLeftComm B3 CV b,
      Nat.mul_comm B3 b, hB4]
    repeat rw [ground.mulAssoc]
    rw [Nat.mul_comm CV B4,
      ground.mulLeftComm c B4 CV]
  have hII : sM * KD * B3 * (a * a) * dth * P
      ≤ sM * KD * B4 * c * P + KD * B3 * (c * c) * sM * Mf := by
    rw [q4]
    refine Nat.le_trans (Nat.mul_le_mul_left (sM * KD * B3) hM) ?_
    rw [Nat.left_distrib (sM * KD * B3) (c * c * Mf) (a * a * dth * TF),
      q5, Nat.add_comm (KD * B3 * (c * c) * sM * Mf)
        (sM * KD * B3 * (a * a * dth * TF))]
    refine Nat.add_le_add ?_ (Nat.le_refl _)
    refine Nat.le_trans (Nat.mul_le_mul_left (sM * KD * B3) hT) ?_
    rw [hCT, q6]
    exact Nat.mul_le_mul_left (sM * KD * B4 * c) hV
  rw [ground.mulAddR (sn * KN2 * C5) (sM * KD * B4 * c) P,
    Nat.add_assoc (sn * KN2 * C5 * P) (sM * KD * B4 * c * P)
      (KD * B3 * (c * c) * sM * Mf)]
  exact Nat.add_le_add hI hII

/-- `lem:corner`'s Rayleigh read: at the family's fold data every
occupied margin above the assembled level reads the count occupied
at the cleared head. -/
theorem family_ground {o : Nat}
    (twoN a b c dth A p KN KD sn sM i0 : Nat)
    (dR gR eR : Nat → Nat) (NR : Nat → Nat → Nat)
    (H : elim.Mat) (x y e : ground.Pos) (n : Nat)
    (sp : inertia.Split o)
    (hc : a + b = c)
    (hmove : ∀ i j, i < o → j < o → 0 < NR i j → gR j ≤ gR i + 2)
    (hdim : ∀ i, i < o → gR i + 2 ≤ twoN →
      ground.famFold Nat.add 0 (fun j => NR i j * dR j) (List.range o)
        = dth * dR i)
    (he : ∀ i, i < o → eR i * KD ≤ KN * (gR i * gR i + 1))
    (hcnt : ∀ k, k ≤ twoN →
      ground.famFold Nat.add 0
          (fun i => if gR i == k then dR i else 0) (List.range o)
        ≤ A * ground.prodOver (fun _ => k + 1) (List.range p))
    (hcert : 2 * dth * (A * A)
        * ground.prodOver (fun _ => twoN + 1) (List.range (2 * p))
        * ground.prodOver (fun _ => a) (List.range (2 * twoN)) * c
      ≤ b * ground.prodOver (fun _ => c) (List.range (2 * twoN)))
    (hi0 : i0 < o) (hg0 : gR i0 = 0) (hd0 : dR i0 = 1)
    (hH : elim.matOneValue H (inertia.siteDatum
      (ground.matOf o o (fun i j =>
        ground.BPair.ofNat
          (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sn * (if i == j then eR i else 0))))
      (ground.matOf o o (fun i j =>
        ground.BPair.ofNat
          (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sM * NR i j)))))
    (hx : (ground.BPair.ofPos x).oneValue (ground.BPair.ofNat
      (sn * KN * (A * A) * ground.rise 1 (2 * p + 2)
          * ground.prodOver (fun _ => c) (List.range (2 * p + 5))
        + sM * KD
          * ground.prodOver (fun _ => b) (List.range (2 * p + 4))
          * c)))
    (hy : (ground.BPair.ofPos y).oneValue (ground.BPair.ofNat
      (sM * KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (a * a) * dth)))
    (hcount : certconstruct.countAtPair H (inertia.idMat o)
      (x + e) y n sp) :
    1 ≤ n := by
  have hb : 0 < b := by
    have hV : 0 < sM * KD
        * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (a * a) * dth := by
      cases hV0 : sM * KD
          * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (a * a) * dth with
      | succ n => exact Nat.succ_pos n
      | zero =>
        rw [hV0] at hy
        exact absurd
          (BPair.lt_congr (BPair.oneValue_refl ground.BPair.unit) hy
            (ground.unitLtOfPos y)) (by decide +kernel)
    cases hbz : b with
    | succ n => exact Nat.succ_pos n
    | zero =>
      rw [hbz] at hV
      have hz : ground.prodOver (fun _ => (0:Nat))
          (List.range (2 * p + 3)) = 0 := by
        show ground.prodOver (fun _ => (0:Nat))
          (List.range (2 * p + 2 + 1)) = 0
        rw [ground.prodConst_split 0 (2 * p + 2) 1]
        rfl
      rw [hz, Nat.mul_zero, Nat.zero_mul, Nat.zero_mul] at hV
      exact absurd hV (Nat.lt_irrefl 0)
  have hc0 : 0 < c := by
    rw [← hc]
    exact Nat.lt_of_lt_of_le hb (Nat.le_add_left b a)
  have hvac := vac_floor o twoN a c i0 dR gR hi0 hg0 hd0
  have hPpos : 0 < pairFold o twoN a c dR gR :=
    Nat.lt_of_lt_of_le
      (ground.prodOver_pos (fun _ => c) (List.range (2 * twoN))
        (fun _ _ => hc0)) hvac
  have hB4 : b * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
      = ground.prodOver (fun _ => b) (List.range (2 * p + 4)) := by
    show b * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
      = ground.prodOver (fun _ => b) (List.range (2 * p + 3 + 1))
    rw [powStep b (2 * p + 3),
      Nat.mul_comm
        (ground.prodOver (fun _ => b) (List.range (2 * p + 3))) b]
  have hCE : ground.prodOver (fun _ => c)
        (List.range (2 * twoN + (2 * p + 3))) * (c * c)
      = ground.prodOver (fun _ => c) (List.range (2 * p + 5))
        * ground.prodOver (fun _ => c) (List.range (2 * twoN)) := by
    rw [← powAdd2 c (2 * twoN + (2 * p + 3)),
      show 2 * twoN + (2 * p + 3) + 2 = 2 * p + 5 + 2 * twoN from by
        rw [Nat.add_assoc (2 * twoN) (2 * p + 3) 2,
          Nat.add_assoc (2 * p) 3 2,
          Nat.add_comm (2 * twoN) (2 * p + 5)],
      ground.prodConst_split c (2 * p + 5) (2 * twoN)]
  have hnat0 := groundArith KD
    (ground.prodOver (fun _ => b) (List.range (2 * p + 3)))
    (ground.prodOver (fun _ => b) (List.range (2 * p + 4)))
    (ground.prodOver (fun _ => c) (List.range (2 * p + 5)))
    (ground.prodOver (fun _ => c) (List.range (2 * twoN)))
    (ground.prodOver (fun _ => c)
      (List.range (2 * twoN + (2 * p + 3))))
    (ground.prodOver (fun _ => c) (List.range (2 * twoN + 1)))
    (KN * (A * A) * ground.rise 1 (2 * p + 2))
    (elecFold o twoN a c dR gR eR) (magFold o twoN a c dR gR NR)
    (pairFold o twoN a c dR gR) (topFold o twoN a c dR gR)
    a b c dth sn sM hB4 hCE (powStep c (2 * twoN))
    (elec_cap o twoN a b c A p KN KD dR gR eR hc he hcnt)
    (mag_low o twoN a c dth dR gR NR (Nat.le.intro hc) hmove hdim)
    (top_cap o twoN a b c dth A p dR gR (Nat.le.intro hc)
      (hcnt twoN (Nat.le_refl twoN))
      (hcnt (twoN - 1) (Nat.sub_le twoN 1)) hcert) hvac
  have hxE : sn * KN * (A * A) * ground.rise 1 (2 * p + 2)
      = sn * (KN * (A * A) * ground.rise 1 (2 * p + 2)) := by
    rw [ground.mulAssoc (sn * KN) (A * A) (ground.rise 1 (2 * p + 2)),
      ground.mulAssoc sn KN ((A * A) * ground.rise 1 (2 * p + 2)),
      ← ground.mulAssoc KN (A * A) (ground.rise 1 (2 * p + 2))]
  have hnat : KD
        * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (c * c) * sn * elecFold o twoN a c dR gR eR
      + sM * KD
        * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (a * a) * dth * pairFold o twoN a c dR gR
      ≤ (sn * KN * (A * A) * ground.rise 1 (2 * p + 2)
            * ground.prodOver (fun _ => c) (List.range (2 * p + 5))
          + sM * KD
            * ground.prodOver (fun _ => b) (List.range (2 * p + 4))
            * c) * pairFold o twoN a c dR gR
        + KD
          * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sM * magFold o twoN a c dR gR NR := by
    rw [hxE]
    exact hnat0
  have hEeq : ground.matOf o o (fun i j =>
        ground.BPair.ofNat
          (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sn * (if i == j then eR i else 0)))
      = ground.matOf o o (fun i j =>
        if i == j
        then ground.BPair.ofNat
          (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sn * eR i)
        else ground.BPair.unit) := by
    refine ground.matOf_congr o o _ _ (fun i j _ _ => ?_)
    by_cases hbq : (i == j) = true
    · rw [if_pos hbq, if_pos hbq]
    · rw [if_neg hbq, if_neg hbq, Nat.mul_zero]
      rfl
  have hEf : elecFold o twoN a c dR gR
        (fun i => KD
          * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sn * eR i)
      = KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (c * c) * sn * elecFold o twoN a c dR gR eR := by
    show ground.famFold Nat.add 0
        (fun i => KD
            * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sn * eR i
          * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
        (List.range o)
      = KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sn
        * ground.famFold Nat.add 0
          (fun i => eR i
            * (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
          (List.range o)
    rw [ground.famFold_mul
      (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (c * c) * sn) _ (List.range o)]
    exact ground.famFold_congr_range _ _ o (fun i _ =>
      ground.mulAssoc
        (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sn) (eR i)
        (trialAt twoN a c dR gR i * trialAt twoN a c dR gR i))
  have hMf : magFold o twoN a c dR gR
        (fun i j => KD
          * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sM * NR i j)
      = KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (c * c) * sM * magFold o twoN a c dR gR NR := by
    show ground.famFold Nat.add 0
        (fun i => trialAt twoN a c dR gR i
          * ground.famFold Nat.add 0
            (fun j => KD
                * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
                * (c * c) * sM * NR i j
              * trialAt twoN a c dR gR j) (List.range o))
        (List.range o)
      = KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sM
        * ground.famFold Nat.add 0
          (fun i => trialAt twoN a c dR gR i
            * ground.famFold Nat.add 0
              (fun j => NR i j * trialAt twoN a c dR gR j)
              (List.range o))
          (List.range o)
    rw [ground.famFold_mul
      (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
        * (c * c) * sM) _ (List.range o)]
    refine ground.famFold_congr_range _ _ o (fun i _ => ?_)
    rw [ground.famFold_congr_range
        (fun j => KD
            * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sM * NR i j
          * trialAt twoN a c dR gR j)
        (fun j => KD
            * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sM
          * (NR i j * trialAt twoN a c dR gR j)) o
        (fun j _ => ground.mulAssoc
          (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sM) (NR i j) (trialAt twoN a c dR gR j)),
      ← ground.famFold_mul
        (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sM)
        (fun j => NR i j * trialAt twoN a c dR gR j) (List.range o),
      ground.mulLeftComm (trialAt twoN a c dR gR i)
        (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sM)
        (ground.famFold Nat.add 0
          (fun j => NR i j * trialAt twoN a c dR gR j)
          (List.range o))]
  have hlen : (trialVec o twoN a c dR gR).length = o :=
    ground.length_mapRange _ o
  have hE1 : (inertia.quadForm
        (ground.matOf o o (fun i j =>
          ground.BPair.ofNat
            (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
              * (c * c) * sn * (if i == j then eR i else 0))))
        (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat
        (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sn * elecFold o twoN a c dR gR eR)) := by
    rw [hEeq]
    refine BPair.oneValue_trans
      (quad_diag o twoN a c dR gR
        (fun i => KD
          * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sn * eR i)) ?_
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat hEf)
  have hM1 : (inertia.quadForm
        (ground.matOf o o (fun i j =>
          ground.BPair.ofNat
            (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
              * (c * c) * sM * NR i j)))
        (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat
        (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sM * magFold o twoN a c dR gR NR)) := by
    refine BPair.oneValue_trans
      (quad_rows o twoN a c dR gR
        (fun i j => KD
          * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sM * NR i j)) ?_
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat hMf)
  have hG1 := quad_gram o twoN a c dR gR
  have hHval : (inertia.quadForm H
        (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat
        (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c) * sn * elecFold o twoN a c dR gR eR)
        + (ground.BPair.ofNat
          (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c) * sM * magFold o twoN a c dR gR NR)).swap) :=
    BPair.oneValue_trans
      (inertia.quadMatOne H _ (trialVec o twoN a c dR gR) hH)
      (BPair.oneValue_trans
        (inertia.quadForm_site_sq
          (elim.sqAt_of (ground.matOf_length o o _)
            (elim.rowsLen_matOf o o _))
          (elim.sqAt_of (ground.matOf_length o o _)
            (elim.rowsLen_matOf o o _)) hlen)
        (BPair.add_congr hE1 (ground.swap_congr hM1)))
  refine rayleigh_count H (inertia.idMat o) (x + e) y n sp
    (trialVec o twoN a c dR gR) hlen hcount ?_
  have hyq : (ground.BPair.ofPos y
        * inertia.quadForm (inertia.idMat o)
          (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat
        ((sM * KD
            * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (a * a) * dth) * pairFold o twoN a c dR gR)) :=
    BPair.oneValue_trans (BPair.mul_congr hy hG1)
      (BPair.oneValue_symm (BPair.ofNat_mul _ _))
  have hxq : (ground.BPair.ofPos x
        * inertia.quadForm (inertia.idMat o)
          (trialVec o twoN a c dR gR)).oneValue
      (ground.BPair.ofNat
        ((sn * KN * (A * A) * ground.rise 1 (2 * p + 2)
              * ground.prodOver (fun _ => c) (List.range (2 * p + 5))
            + sM * KD
              * ground.prodOver (fun _ => b) (List.range (2 * p + 4))
              * c) * pairFold o twoN a c dR gR)) :=
    BPair.oneValue_trans (BPair.mul_congr hx hG1)
      (BPair.oneValue_symm (BPair.ofNat_mul _ _))
  have hle : inertia.quadForm H (trialVec o twoN a c dR gR)
        + ground.BPair.ofPos y
          * inertia.quadForm (inertia.idMat o)
            (trialVec o twoN a c dR gR)
      ≤ ground.BPair.ofPos x
        * inertia.quadForm (inertia.idMat o)
          (trialVec o twoN a c dR gR) := by
    refine ground.leB_congr
      (BPair.oneValue_symm (BPair.add_congr hHval hyq))
      (BPair.oneValue_symm hxq) ?_
    rw [BPair.add_right_comm]
    refine leSwapAdd ?_
    exact ground.leB_congr (BPair.ofNat_add _ _)
      (BPair.ofNat_add _ _) (ground.leB_ofNat hnat)
  refine ground.leB_ltB_trans hle ?_
  have hQpos : ground.BPair.unit
      < inertia.quadForm (inertia.idMat o)
        (trialVec o twoN a c dR gR) :=
    BPair.lt_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm hG1)
      (unitLtNat (pairFold o twoN a c dR gR) hPpos)
  refine BPair.lt_congr (BPair.oneValue_refl _) ?_
    (ground.ltB_addPos
      (ground.unitLtMul (ground.unitLtOfPos e) hQpos))
  rw [← BPair.right_distrib]
  exact BPair.mul_congr_left (BPair.oneValue_symm (ofPos_add x e))

/-- The gap's square identity at an ordered split: the whole's
square joined to the gap's square reads the doubled cross term
against the complement's square. -/
private theorem sqJoinAB (a b c : Nat) (h : a + b = c) :
    c * c + b * b = 2 * b * c + a * a := by
  have h1 : c * c = c * a + c * b := by rw [← Nat.left_distrib c a b, h]
  have h2 : c * a = a * a + b * a := by rw [← ground.mulAddR a b a, h]
  have h3 : b * c = b * a + b * b := by rw [← Nat.left_distrib b a b, h]
  rw [Nat.two_mul b, ground.mulAddR b b c, h1, h2, Nat.mul_comm c b,
    Nat.add_right_comm (a * a + b * a) (b * c) (b * b),
    Nat.add_assoc (a * a) (b * a) (b * b), ← h3,
    Nat.add_comm (a * a) (b * c),
    Nat.add_right_comm (b * c) (a * a) (b * c)]

/-- The drift's regrouping at abstract atoms: the electric term
rides the bracket comparison, the boundary term is the gap's own
multiple, and the magnetic term pays the cube comparison
`c^3 ≤ 2bc^2 + a^2 c`. -/
private theorem driftNat (KD dth sn sM a b c W B3 B4 C4 C5 T : Nat)
    (hB4 : b * B3 = B4)
    (hC5 : c * C5 = c * c * C4)
    (hsq : c * c + b * b = 2 * b * c + a * a)
    (hbr : sn * C4 ≤ T * B4 * sM) :
    c * KD * (sn * W * C5 + sM * KD * B4 * c)
        + c * KD * (KD * B3 * (c * c)) * sM * dth
      ≤ (T * W + KD * (2 * dth + 1)) * b * (KD * B3 * (c * c)) * sM
        + c * KD * (sM * KD * B3 * (a * a) * dth) := by
  have e1 : c * KD * (sn * W * C5) = KD * W * (c * c) * (sn * C4) := by
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm c KD (sn * (W * C5)),
      ground.mulLeftComm sn W C5,
      ground.mulLeftComm c W (sn * C5),
      ground.mulLeftComm c sn C5, hC5]
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm sn c (c * C4),
      ground.mulLeftComm sn c C4]
  have e2 : T * W * b * (KD * B3 * (c * c)) * sM
      = KD * W * (c * c) * (T * B4 * sM) := by
    rw [← hB4]
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm b KD (B3 * (c * (c * sM))),
      ground.mulLeftComm W KD (b * (B3 * (c * (c * sM)))),
      ground.mulLeftComm T KD (W * (b * (B3 * (c * (c * sM))))),
      ground.mulLeftComm T W (b * (B3 * (c * (c * sM)))),
      ground.mulLeftComm B3 c (c * sM),
      ground.mulLeftComm b c (B3 * (c * sM)),
      ground.mulLeftComm T c (b * (B3 * (c * sM))),
      ground.mulLeftComm B3 c sM,
      ground.mulLeftComm b c (B3 * sM),
      ground.mulLeftComm T c (b * (B3 * sM))]
  have h1 : c * KD * (sn * W * C5)
      ≤ T * W * b * (KD * B3 * (c * c)) * sM := by
    rw [e1, e2]
    exact Nat.mul_le_mul_left (KD * W * (c * c)) hbr
  have h2 : c * KD * (sM * KD * B4 * c)
      = KD * b * (KD * B3 * (c * c)) * sM := by
    rw [← hB4]
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm c KD (sM * (KD * (b * (B3 * c)))),
      ground.mulLeftComm KD b (B3 * c),
      ground.mulLeftComm sM b (KD * (B3 * c)),
      ground.mulLeftComm c b (sM * (KD * (B3 * c))),
      ground.mulLeftComm sM KD (B3 * c),
      ground.mulLeftComm c KD (sM * (B3 * c)),
      ground.mulLeftComm sM B3 c,
      ground.mulLeftComm c B3 (sM * c),
      Nat.mul_comm sM c]
  have hcube : c * (c * c) ≤ 2 * b * (c * c) + c * (a * a) := by
    have hm : (c * c + b * b) * c = (2 * b * c + a * a) * c := by
      rw [hsq]
    rw [ground.mulAddR (c * c) (b * b) c,
      ground.mulAddR (2 * b * c) (a * a) c] at hm
    rw [← ground.mulAssoc c c c, ← ground.mulAssoc (2 * b) c c,
      Nat.mul_comm c (a * a), ← hm]
    exact Nat.le_add_right _ _
  have e3 : c * KD * (KD * B3 * (c * c)) * sM * dth
      = KD * KD * B3 * sM * dth * (c * (c * c)) := by
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm c KD (KD * (B3 * (c * (c * (sM * dth))))),
      ground.mulLeftComm c KD (B3 * (c * (c * (sM * dth)))),
      ground.mulLeftComm c B3 (c * (c * (sM * dth))),
      ground.mulLeftComm c sM dth,
      ground.mulLeftComm c sM (c * dth),
      ground.mulLeftComm c sM (c * (c * dth)),
      Nat.mul_comm c dth,
      ground.mulLeftComm c dth c,
      ground.mulLeftComm c dth (c * c)]
  have e4 : KD * (2 * dth) * b * (KD * B3 * (c * c)) * sM
      = KD * KD * B3 * sM * dth * (2 * b * (c * c)) := by
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm b KD (B3 * (c * (c * sM))),
      ground.mulLeftComm dth KD (b * (B3 * (c * (c * sM)))),
      ground.mulLeftComm 2 KD (dth * (b * (B3 * (c * (c * sM))))),
      ground.mulLeftComm b B3 (c * (c * sM)),
      ground.mulLeftComm dth B3 (b * (c * (c * sM))),
      ground.mulLeftComm 2 B3 (dth * (b * (c * (c * sM)))),
      Nat.mul_comm c sM,
      ground.mulLeftComm c sM c,
      ground.mulLeftComm b sM (c * c),
      ground.mulLeftComm dth sM (b * (c * c)),
      ground.mulLeftComm 2 sM (dth * (b * (c * c))),
      ground.mulLeftComm 2 dth (b * (c * c))]
  have e5 : c * KD * (sM * KD * B3 * (a * a) * dth)
      = KD * KD * B3 * sM * dth * (c * (a * a)) := by
    repeat rw [ground.mulAssoc]
    rw [ground.mulLeftComm c KD (sM * (KD * (B3 * (a * (a * dth))))),
      ground.mulLeftComm sM KD (B3 * (a * (a * dth))),
      ground.mulLeftComm c KD (sM * (B3 * (a * (a * dth)))),
      ground.mulLeftComm sM B3 (a * (a * dth)),
      ground.mulLeftComm c B3 (sM * (a * (a * dth))),
      ground.mulLeftComm c sM (a * (a * dth)),
      Nat.mul_comm a dth,
      ground.mulLeftComm a dth a,
      ground.mulLeftComm c dth (a * a)]
  have h3 : c * KD * (KD * B3 * (c * c)) * sM * dth
      ≤ KD * (2 * dth) * b * (KD * B3 * (c * c)) * sM
        + c * KD * (sM * KD * B3 * (a * a) * dth) := by
    rw [e3, e4, e5, ← Nat.left_distrib]
    exact Nat.mul_le_mul_left (KD * KD * B3 * sM * dth) hcube
  rw [Nat.left_distrib (c * KD) (sn * W * C5) (sM * KD * B4 * c),
    Nat.add_assoc (c * KD * (sn * W * C5)) (c * KD * (sM * KD * B4 * c))
      (c * KD * (KD * B3 * (c * c)) * sM * dth),
    Nat.left_distrib KD (2 * dth) 1, Nat.mul_one KD,
    ← Nat.add_assoc (T * W) (KD * (2 * dth)) KD,
    ground.mulAddR (T * W + KD * (2 * dth)) KD b,
    ground.mulAddR ((T * W + KD * (2 * dth)) * b) (KD * b)
      (KD * B3 * (c * c)),
    ground.mulAddR ((T * W + KD * (2 * dth)) * b * (KD * B3 * (c * c)))
      (KD * b * (KD * B3 * (c * c))) sM,
    ground.mulAddR (T * W) (KD * (2 * dth)) b,
    ground.mulAddR (T * W * b) (KD * (2 * dth) * b) (KD * B3 * (c * c)),
    ground.mulAddR (T * W * b * (KD * B3 * (c * c)))
      (KD * (2 * dth) * b * (KD * B3 * (c * c))) sM,
    Nat.add_assoc (T * W * b * (KD * B3 * (c * c)) * sM)
      (KD * (2 * dth) * b * (KD * B3 * (c * c)) * sM)
      (KD * b * (KD * B3 * (c * c)) * sM),
    Nat.add_assoc (T * W * b * (KD * B3 * (c * c)) * sM)
      (KD * (2 * dth) * b * (KD * B3 * (c * c)) * sM
        + KD * b * (KD * B3 * (c * c)) * sM)
      (c * KD * (sM * KD * B3 * (a * a) * dth)),
    Nat.add_comm (KD * (2 * dth) * b * (KD * B3 * (c * c)) * sM)
      (KD * b * (KD * B3 * (c * c)) * sM),
    Nat.add_assoc (KD * b * (KD * B3 * (c * c)) * sM)
      (KD * (2 * dth) * b * (KD * B3 * (c * c)) * sM)
      (c * KD * (sM * KD * B3 * (a * a) * dth))]
  exact Nat.add_le_add h1 (Nat.add_le_add (Nat.le_of_eq h2) h3)

/-- The assembled level joined to the top root's cap sits at or
below `C_g`'s multiple of the gap, at the bracket's upper side:
`C_g` the collected read `2^{q+1}C_E + 2d_θ + 1` at the cleared
pair `[2^{q+1}·KN·A²·(2p+2)! + KD·(2d_θ+1) : KD]`. -/
theorem level_drift (p A KN KD dth sn sM a b c : Nat)
    (hc : a + b = c)
    (hbr : sn * ground.prodOver (fun _ => c) (List.range (2 * p + 4))
      ≤ ground.prodOver (fun _ => 2) (List.range (2 * p + 4))
        * ground.prodOver (fun _ => b) (List.range (2 * p + 4)) * sM) :
    c * KD
        * (sn * KN * (A * A) * ground.rise 1 (2 * p + 2)
            * ground.prodOver (fun _ => c) (List.range (2 * p + 5))
          + sM * KD
            * ground.prodOver (fun _ => b) (List.range (2 * p + 4))
            * c)
      + c * KD
        * (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
          * (c * c)) * sM * dth
      ≤ (ground.prodOver (fun _ => 2) (List.range (2 * p + 4))
            * (KN * (A * A) * ground.rise 1 (2 * p + 2))
          + KD * (2 * dth + 1)) * b
          * (KD * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (c * c)) * sM
        + c * KD
          * (sM * KD
            * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
            * (a * a) * dth) := by
  have hB4 : b * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
      = ground.prodOver (fun _ => b) (List.range (2 * p + 4)) := by
    show b * ground.prodOver (fun _ => b) (List.range (2 * p + 3))
      = ground.prodOver (fun _ => b) (List.range (2 * p + 3 + 1))
    rw [powStep b (2 * p + 3),
      Nat.mul_comm
        (ground.prodOver (fun _ => b) (List.range (2 * p + 3))) b]
  have hC5 : c * ground.prodOver (fun _ => c) (List.range (2 * p + 5))
      = c * c * ground.prodOver (fun _ => c) (List.range (2 * p + 4)) := by
    show c * ground.prodOver (fun _ => c) (List.range (2 * p + 4 + 1))
      = c * c * ground.prodOver (fun _ => c) (List.range (2 * p + 4))
    rw [powStep c (2 * p + 4),
      ← ground.mulAssoc c
        (ground.prodOver (fun _ => c) (List.range (2 * p + 4))) c,
      ground.mulRightComm c
        (ground.prodOver (fun _ => c) (List.range (2 * p + 4))) c]
  have hW : sn * KN * (A * A) * ground.rise 1 (2 * p + 2)
      = sn * (KN * (A * A) * ground.rise 1 (2 * p + 2)) := by
    rw [ground.mulAssoc (sn * KN) (A * A) (ground.rise 1 (2 * p + 2)),
      ground.mulAssoc sn KN ((A * A) * ground.rise 1 (2 * p + 2)),
      ← ground.mulAssoc KN (A * A) (ground.rise 1 (2 * p + 2))]
  rw [hW]
  exact driftNat KD dth sn sM a b c
    (KN * (A * A) * ground.rise 1 (2 * p + 2))
    (ground.prodOver (fun _ => b) (List.range (2 * p + 3)))
    (ground.prodOver (fun _ => b) (List.range (2 * p + 4)))
    (ground.prodOver (fun _ => c) (List.range (2 * p + 4)))
    (ground.prodOver (fun _ => c) (List.range (2 * p + 5)))
    (ground.prodOver (fun _ => 2) (List.range (2 * p + 4)))
    hB4 hC5 (sqJoinAB a b c hc) hbr

/-- A shared right factor cancels off the ground order. -/
private theorem posMulCancelR {a b c : ground.Pos}
    (h : a * c ≤ b * c) : a ≤ b :=
  match ground.trich a b with
  | ground.Trich.eq e => Or.inl e
  | ground.Trich.lt g hg => Or.inr ⟨g, hg⟩
  | ground.Trich.gt g hg =>
    absurd (ground.mul_lt_mul_right c
      (show b < a from ⟨g, hg⟩)) (ground.posLtLe h)

/-- The rate's power close: the drift below `C_g`'s multiple of the
gap and the gap's power below the scale close the displayed
comparison, one cross-multiplication (`lem:corner`'s
`g(σ)^{q+1} ≤ C_g^{q+1} σ`). -/
theorem rate_close (q1 : Nat) (gn gd Cg wn wd sn sd : ground.Pos)
    (hg : gn * wd ≤ Cg * wn * gd)
    (hbr : ground.Pos.pow wn q1 * sd ≤ sn * ground.Pos.pow wd q1) :
    ground.Pos.pow gn q1 * sd ≤ ground.Pos.pow Cg q1 * sn * ground.Pos.pow gd q1 := by
  have hpow : ground.Pos.pow gn q1 * ground.Pos.pow wd q1
      ≤ ground.Pos.pow Cg q1 * ground.Pos.pow wn q1 * ground.Pos.pow gd q1 := by
    rw [← ground.Pos.pow_mul gn wd q1, ← ground.Pos.pow_mul Cg wn q1,
      ← ground.Pos.pow_mul (Cg * wn) gd q1]
    exact ground.Pos.pow_le hg q1
  refine posMulCancelR (c := ground.Pos.pow wd q1) ?_
  refine ground.le_trans
    (show ground.Pos.pow gn q1 * sd * ground.Pos.pow wd q1
        ≤ ground.Pos.pow Cg q1 * ground.Pos.pow gd q1 * (ground.Pos.pow wn q1 * sd) from ?_) ?_
  · rw [ground.mul_right_comm (ground.Pos.pow gn q1) sd (ground.Pos.pow wd q1),
      ground.mul_assoc (ground.Pos.pow Cg q1) (ground.Pos.pow gd q1)
        (ground.Pos.pow wn q1 * sd),
      ground.mul_left_comm (ground.Pos.pow gd q1) (ground.Pos.pow wn q1) sd,
      ← ground.mul_assoc (ground.Pos.pow Cg q1) (ground.Pos.pow wn q1)
        (ground.Pos.pow gd q1 * sd),
      ← ground.mul_assoc (ground.Pos.pow Cg q1 * ground.Pos.pow wn q1)
        (ground.Pos.pow gd q1) sd]
    exact ground.mul_le_mul_right sd hpow
  · rw [ground.mul_comm (ground.Pos.pow Cg q1 * ground.Pos.pow gd q1)
      (ground.Pos.pow wn q1 * sd)]
    refine ground.le_trans
      (ground.mul_le_mul_right (a := ground.Pos.pow wn q1 * sd) (b := sn * ground.Pos.pow wd q1)
        (ground.Pos.pow Cg q1 * ground.Pos.pow gd q1) hbr) ?_
    refine Or.inl ?_
    rw [ground.mul_mul_mul_comm sn (ground.Pos.pow wd q1) (ground.Pos.pow Cg q1)
        (ground.Pos.pow gd q1),
      ground.mul_assoc (ground.Pos.pow Cg q1 * sn) (ground.Pos.pow gd q1)
        (ground.Pos.pow wd q1),
      ground.mul_comm (ground.Pos.pow Cg q1) sn,
      ground.mul_comm (ground.Pos.pow gd q1) (ground.Pos.pow wd q1)]

end corner
