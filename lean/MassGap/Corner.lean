import MassGap.Certconstruct
import MassGap.Contactcell
import MassGap.Flatstep
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
`dual_count_mono` at the corner ray's own points, under one further
clearing).

The corner presentation tier carries the count's base as a
two-variable pencil at `lem:cellcount`'s carrier: the height
variable over the scale base, the base entry's scale polynomial
`ed² M + en² (swap E)` at the keys nought and two against the
seam's weight `en ed (swap G)` at key one (`cornerPP` at
`split.ppzMat`).  Its double evaluation — the base at the scale
point `[en : ed]` cleared at the square, the height at the
balance-pair point — is the corner site (`cornerPP_eval`), so at
the three data's stated orders the height-direction count of the
evaluated presentation is the corner count itself
(`cornerPP_count` at `cellcount.countAt`).  The cell's two located
outputs read back at squares in the ray coordinate: the ray
`[a : b]` sits in the extent `η₁ = [n₁ : d₁]` at the
cross-multiplied comparison `a d₁² ≤ n₁² b` (`rayInExtent`), one
value across the ray's representatives and across the extent's
(`rayInExtent_ray`, `rayInExtent_ext`), and a level clears the
floor at the level's square against the weight product at the
floor's square (`levelClears`), which at the ray's scale tie and
the cofactor `λ = β (η η′)` is the height against the floor
(`level_height`).

The cutoff at the scale: the scale key is the least natural whose
`4η²` multiple clears the dimension fold against the window's top
level and the clearance (`scaleKey`, with `scaleKey_ge` its own
witness and `scaleKey_least` the minimality), and at that comparison
the seed floor clears every window level at once — a cutoff at or
beyond the key and a level at or below the top clear by the
clearance (`seedClears`, `keyClears` at the key itself).

The presentation's height section substitutes the height variable
first, leaving the pencil's polynomial matrix in the scale variable
alone (`cornerAtHeight` at `poly.pevalC`); the scale's own cleared
evaluation of that section is the corner site again
(`cornerAtHeight_eval`), so the two substitution orders read one
matrix and the section is `thm:decimation`'s emitted record's own
carrier.

The extent and the floor: the corner divisor is `thm:divisorid`'s
crossing read at the presentation's committed split, and an
occupied corner divisor holds the origin at its least occupied
degree (the height's weight carries one scale power), so the
extent brackets the first positive root at the withdrawal, the
vacant leading keys at the stated degree, the cofactor's constant
occupied, and `lem:contactcell`'s bracket shape at the withdrawn
cofactor (`contactcell.extentRead`).  The floor is the flat step's height extent: the
seam levels' window is the corner counts' at the heights, the
scale factor withdrawing from the order (`corner_flat` at
`corner_dual` twice with the strict cancellation).

The record ties the families at committed data: the cells at their
counted samples with the cutoff's comparison bound and the
pencil determinant's jump, the decimation's own jump divisors at
the substitution (`decimation.DivRecord` at the height section),
the deck family at the walk's base reads with its vacant-direction
segment count, the tension family's unit-class drop at the matched
stencil, the t-section at the band's own segment count
(`deckfactor.bandClear`), and the rank direction at the member-key
count's stability (`xfusion.c1_eq`), the batteries the reads'
whole verification.
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

instance instCorner1 {o : Nat} (E M G : Mat) (en ed hp hm : Pos) (n : Nat)
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
      show inertia.splitRead (inertia.siteDatum
        (elim.matAdd (cornerPencil E M en ed) (inertia.matScale (en * ed * hm) G))
        (inertia.matScale (en * ed * hp) G)) sp
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
stated at the corner coordinate's own ray points, the two cleared
pencils read under one further clearing `c`, the common clearing
an extent interval's three scales share (`lem:cornerfloor`'s
mixed window). -/
theorem dual_count_mono {o : Nat} (E M G : Mat)
    (c en ed en' ed' g x y : Pos) (n n' : Nat)
    (sp sp' spE spg : inertia.Split o)
    (hg : en' * en' * (ed * ed) + g = en * en * (ed' * ed'))
    (hE : inertia.splitRead E spE) (hEpsd : inertia.psdAt spE)
    (hsg : inertia.splitRead (inertia.matScale (c * g) E) spg)
    (h : certconstruct.countAtPair
      (inertia.matScale (c * (ed' * ed')) (cornerPencil E M en ed))
      G x y n sp)
    (h' : certconstruct.countAtPair
      (inertia.matScale (c * (ed * ed)) (cornerPencil E M en' ed'))
      G x y n' sp') :
    n ≤ n' := by
  rw [← inertia.matScale_matScale (ed' * ed') c (cornerPencil E M en ed),
    cornerPencil_gap E M en ed en' ed' g hg, inertia.matScale_matAdd,
    inertia.matScale_matScale, inertia.matScale_matScale] at h
  rw [← inertia.matScale_matScale (ed * ed) c (cornerPencil E M en' ed'),
    inertia.matScale_matScale] at h'
  exact count_le_of_gap E
    (inertia.matScale (c * (ed * ed)) (cornerPencil E M en' ed'))
    G (c * g) x y n n' sp sp' spE spg hE hEpsd hsg h h'


/-! `lem:corner`'s corner presentation at the two-variable pencil:
the height variable over the scale base, the base entry the scale
polynomial `ed² M + en² (swap E)` at the keys nought and two, the
seam's weight `en ed (swap G)` at key one, and the pencil
`Z(x) = x (en ed G) - (ed² M + en² swap E)` the outer pair's site
datum over those coefficients (`baseSite`, `heightWeight`,
`cornerPP` at `split.ppzMat`).  The double evaluation reads the
corner site — the base at the scale point `[en : ed]` cleared at
the square, the height at the balance-pair point `⟨η′₊ : η′₋⟩`,
one matrix identity (`cornerPP_eval`) — so at the three data'
stated orders the height-direction count of the evaluated
presentation is the corner count itself (`cornerPP_count` at
`lem:cellcount`'s `countAt`). -/

/-- The corner pencil's base matrix: per entry the scale
polynomial `ed^2 M + en^2 (swap E)` at keys 0 and 2, the pencil's
own base presentation. -/
private def baseSite (E M : Mat) : split.PMat :=
  List.zipWith (List.zipWith (fun e m =>
    [m, ground.BPair.unit, ground.BPair.swap e])) E M

/-- The height's weight matrix: per entry the scale polynomial
`en ed (swap G)` at key 1, the gram's seam weight. -/
private def heightWeight (G : Mat) : split.PMat :=
  G.map (fun r => r.map (fun g =>
    [ground.BPair.unit, ground.BPair.swap g]))

/-- The corner presentation: the two-variable pencil at the height
variable over the scale base, `Z(x) = x (en ed G) - (ed^2 M
+ en^2 swap E)` at the cleared base display (`lem:corner`'s
polynomial-pair head entries at the substitution). -/
def cornerPP (E M G : Mat) : split.PPMat :=
  split.ppzMat (baseSite E M) (heightWeight G)

/-- A one-member site's square is the ground square's own site. -/
private theorem bpowSq (a : Pos) :
    (ground.bpow (BPair.ofPos a) 2).oneValue (BPair.ofPos (a * a)) := by
  have hp : Pos.pow a 2 = a * a := Pos.pow_two a
  have h := ground.ofPos_pow a 2
  rw [hp] at h
  exact BPair.oneValue_symm h

/-- The height pair against the seam weight's swapped scaling: the
pair's two members distribute onto the weight's two sides, the
lower member on the datum and the upper on its swap. -/
private theorem seamHeight (g : BPair) (en ed hp hm : Pos) :
    ((⟨hp, hm⟩ : BPair) * (g.scale (en * ed)).swap).oneValue
      (g.scale (en * ed * hm) + (g.scale (en * ed * hp)).swap) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.mk_read hp hm)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq (BPair.right_distrib (BPair.ofPos hp)
      (BPair.ofPos hm).swap (g.scale (en * ed)).swap)) ?_
  refine BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.add_comm (BPair.ofPos hp * (g.scale (en * ed)).swap)
        ((BPair.ofPos hm).swap * (g.scale (en * ed)).swap))) ?_
  refine BPair.add_congr ?_ ?_
  · refine BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (BPair.swap_mul (BPair.ofPos hm) (g.scale (en * ed)).swap)) ?_
    refine BPair.oneValue_trans
      (ground.swap_congr
        (BPair.ofPos_scale hm (g.scale (en * ed)).swap)) ?_
    exact BPair.oneValue_of_eq
      (congrArg BPair.swap
        (congrArg BPair.swap (BPair.scale_scale g (en * ed) hm)))
  · refine BPair.oneValue_trans
      (BPair.ofPos_scale hp (g.scale (en * ed)).swap) ?_
    exact BPair.oneValue_of_eq
      (congrArg BPair.swap (BPair.scale_scale g (en * ed) hp))

/-- The presentation's entry at the double evaluation: the base
entry's two surviving keys read `en^2 e` against `ed^2 m` at the
scale point and the seam weight reads `en ed (swap g)`, the height
pair distributing its two members onto the two sides — the corner
site's entry. -/
private theorem cornerEntry (e m g : BPair) (en ed hp hm : Pos) :
    (poly.evalClear
        [poly.evalClear (poly.neg [m, BPair.unit, BPair.swap e])
            (BPair.ofPos en) ed 2,
          poly.evalClear [BPair.unit, BPair.swap g]
            (BPair.ofPos en) ed 2]
        ⟨hp, hm⟩ Pos.one 1).oneValue
      (e.scale (en * en) + g.scale (en * ed * hm)
        + (m.scale (ed * ed) + g.scale (en * ed * hp)).swap) := by
  have hb : (poly.evalClear (poly.neg [m, BPair.unit, BPair.swap e])
      (BPair.ofPos en) ed 2).oneValue
      ((m.scale (ed * ed)).swap + e.scale (en * en)) := by
    refine BPair.oneValue_trans
      (poly.evalClear_ends m.swap e [BPair.unit]
        ⟨BPair.oneValue_refl BPair.unit, trivial⟩
        (BPair.ofPos en) ed) ?_
    exact BPair.add_congr
      (BPair.oneValue_trans (BPair.mul_congr_left (bpowSq ed))
        (BPair.ofPos_scale (ed * ed) m.swap))
      (BPair.oneValue_trans (BPair.mul_congr_left (bpowSq en))
        (BPair.ofPos_scale (en * en) e))
  have hh : (poly.evalClear [BPair.unit, BPair.swap g]
      (BPair.ofPos en) ed 2).oneValue ((g.scale (en * ed)).swap) := by
    have h0 : (BPair.unit * ground.bpow (BPair.ofPos en) 0
        * ground.bpow (BPair.ofPos ed) 2).oneValue BPair.unit :=
      BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.unit_mul _)) (BPair.unit_mul _)
    have h1 : (BPair.swap g * ground.bpow (BPair.ofPos en) 1
        * ground.bpow (BPair.ofPos ed) 1).oneValue
        ((g.scale (en * ed)).swap) := by
      refine BPair.oneValue_trans
        (BPair.mul_congr
          (BPair.mul_congr (BPair.oneValue_refl g.swap) (bpow_one_read _))
          (bpow_one_read _)) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.oneValue_of_eq
          (BPair.mul_comm g.swap (BPair.ofPos en)))) ?_
      refine BPair.oneValue_trans
        (BPair.mul_congr_left (BPair.ofPos_scale en g.swap)) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (BPair.mul_comm (g.swap.scale en)
          (BPair.ofPos ed))) ?_
      refine BPair.oneValue_trans
        (BPair.ofPos_scale ed (g.swap.scale en)) ?_
      exact BPair.oneValue_of_eq (BPair.scale_scale g.swap en ed)
    refine BPair.oneValue_trans
      (poly.evalClear_read [BPair.unit, BPair.swap g]
        (BPair.ofPos en) ed 2) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr h0
        (BPair.oneValue_trans
          (BPair.add_congr h1 (BPair.oneValue_refl BPair.unit))
          (BPair.add_unit _))) ?_
    exact BPair.unit_add _
  have hmul := seamHeight g en ed hp hm
  refine BPair.oneValue_trans
    (poly.evalClear_ends
      (poly.evalClear (poly.neg [m, BPair.unit, BPair.swap e])
        (BPair.ofPos en) ed 2)
      (poly.evalClear [BPair.unit, BPair.swap g] (BPair.ofPos en) ed 2)
      [] trivial ⟨hp, hm⟩ Pos.one) ?_
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.oneValue_trans (BPair.mul_congr (bpow_one_read _) hb)
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (BPair.mul_comm _ _))
          (BPair.mul_one_read _)))
      (BPair.oneValue_trans (BPair.mul_congr (bpow_one_read _) hh) hmul)) ?_
  refine BPair.oneValue_of_eq ?_
  rw [← BPair.swap_add (m.scale (ed * ed)) (g.scale (en * ed * hp)),
    BPair.add_comm (m.scale (ed * ed)).swap (e.scale (en * en)),
    BPair.add_add_comm (e.scale (en * en)) (m.scale (ed * ed)).swap
      (g.scale (en * ed * hm)) (g.scale (en * ed * hp)).swap]

/-- One row of the double evaluation reads the corner site's row,
the three rows' componentwise walk entry by entry. -/
private theorem cornerRow (en ed hp hm : Pos) : ∀ rE rM rG : List BPair,
    poly.oneValue
      (((List.zipWith (fun h g => [poly.neg h, g])
          (List.zipWith (fun e m =>
              [m, ground.BPair.unit, ground.BPair.swap e]) rE rM)
          (rG.map (fun g =>
              [ground.BPair.unit, ground.BPair.swap g]))).map
          (fun P => P.map (fun p =>
            poly.evalClear p (BPair.ofPos en) ed 2))).map
        (fun p => poly.evalClear p ⟨hp, hm⟩ Pos.one 1))
      (List.zipWith BPair.add
        (List.zipWith BPair.add (rE.map (fun x => x.scale (en * en)))
          (rG.map (fun x => x.scale (en * ed * hm))))
        ((List.zipWith BPair.add (rM.map (fun x => x.scale (ed * ed)))
          (rG.map (fun x => x.scale (en * ed * hp)))).map BPair.swap))
  | [], _, _ => trivial
  | _ :: _, [], [] => trivial
  | _ :: _, [], _ :: _ => trivial
  | _ :: _, _ :: _, [] => trivial
  | e :: rE, m :: rM, g :: rG =>
    ⟨cornerEntry e m g en ed hp hm, cornerRow en ed hp hm rE rM rG⟩

/-- The double evaluation reads the corner site row by row, the
three data's componentwise walk. -/
private theorem cornerMat (en ed hp hm : Pos) : ∀ E M G : Mat,
    elim.matOneValue
      (cellcount.evalPC
        (cellcount.ppevalPC (cornerPP E M G) (BPair.ofPos en) ed 2)
        ⟨hp, hm⟩ Pos.one 1)
      (cornerSite E M G en ed hp hm)
  | [], _, _ => trivial
  | _ :: _, [], [] => trivial
  | _ :: _, [], _ :: _ => trivial
  | _ :: _, _ :: _, [] => trivial
  | rE :: E, rM :: M, rG :: G =>
    ⟨cornerRow en ed hp hm rE rM rG, cornerMat en ed hp hm E M G⟩

/-- The double evaluation reads the corner site: the base at the
scale point `[en:ed]` cleared at the square, the height at the
balance-pair point, one matrix identity. -/
theorem cornerPP_eval (E M G : Mat) (en ed hp hm : Pos) :
    elim.matOneValue
      (cellcount.evalPC
        (cellcount.ppevalPC (cornerPP E M G)
          (ground.BPair.ofPos en) ed 2)
        ⟨hp, hm⟩ ground.Pos.one 1)
      (cornerSite E M G en ed hp hm) :=
  cornerMat en ed hp hm E M G

/-- The presentation's row count at the three data's own: the
componentwise walk's own truncation at matched counts. -/
private theorem cornerPP_len (E M G : Mat) (o : Nat)
    (hE : E.length = o) (hM : M.length = o) (hG : G.length = o) :
    (cornerPP E M G).length = o :=
  ground.length_zipWith _ _ _ o
    (ground.length_zipWith _ E M o hE hM)
    ((ground.length_map _ G).trans hG)

/-- The presentation's rows at the three data's own width. -/
private theorem cornerPP_rows (o : Nat) : ∀ E M G : Mat,
    elim.rowsLen o E → elim.rowsLen o M → elim.rowsLen o G →
    elim.rowsLen o (cornerPP E M G)
  | [], _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _ => trivial
  | _ :: _, _ :: _, [], _, _, _ => trivial
  | rE :: E, rM :: M, rG :: G, hE, hM, hG =>
    ⟨ground.length_zipWith _ _ _ o
      (ground.length_zipWith _ rE rM o hE.1 hM.1)
      ((ground.length_map _ rG).trans hG.1),
     cornerPP_rows o E M G hE.2 hM.2 hG.2⟩

/-- One evaluated row's entries are linear in the height variable:
every entry is the outer pair's two coefficients. -/
private theorem cornerRow_ble (ln : BPair) (c : Pos) :
    ∀ rE rM rG : List BPair,
    (((List.zipWith (fun h g => [poly.neg h, g])
        (List.zipWith (fun e m =>
            [m, ground.BPair.unit, ground.BPair.swap e]) rE rM)
        (rG.map (fun g =>
            [ground.BPair.unit, ground.BPair.swap g]))).map
        (fun P => P.map (fun p => poly.evalClear p ln c 2))).all
      (fun p => Nat.ble p.length 2)) = true
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | _ :: rE, _ :: rM, _ :: rG => cornerRow_ble ln c rE rM rG

/-- The base's evaluated presentation is linear in the height
variable at every entry. -/
private theorem cornerPP_ble (ln : BPair) (c : Pos) : ∀ E M G : Mat,
    ((cellcount.ppevalPC (cornerPP E M G) ln c 2).all
      (fun r => r.all (fun p => Nat.ble p.length 2))) = true
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | rE :: E, rM :: M, rG :: G =>
    ground.andIntroB (cornerRow_ble ln c rE rM rG)
      (cornerPP_ble ln c E M G)

/-- The height-direction count of the evaluated presentation is
the corner count: the two site matrices one value at the double
evaluation, the shape reads exchanged at the stated orders. -/
theorem cornerPP_count {o : Nat} (E M G : Mat)
    (en ed hp hm : Pos) (n : Nat) (sp : inertia.Split o)
    (hE : elim.sqAt E o) (hM : elim.sqAt M o)
    (hG : elim.sqAt G o) :
    cellcount.countAt
        (cellcount.ppevalPC (cornerPP E M G)
          (ground.BPair.ofPos en) ed 2)
        1 ⟨hp, hm⟩ ground.Pos.one n sp
      ↔ cornerCount E M G en ed hp hm n sp := by
  have hrows : elim.rowsLen o (cornerPP E M G) :=
    cornerPP_rows o E M G (elim.rowsLen_of_sqAt hE)
      (elim.rowsLen_of_sqAt hM) (elim.rowsLen_of_sqAt hG)
  have hplen : (cellcount.ppevalPC (cornerPP E M G)
      (BPair.ofPos en) ed 2).length = o :=
    (ground.length_map _ _).trans
      (cornerPP_len E M G o (elim.sqAt_len hE) (elim.sqAt_len hM)
        (elim.sqAt_len hG))
  have hprows : elim.rowsLen o (cellcount.ppevalPC (cornerPP E M G)
      (BPair.ofPos en) ed 2) :=
    elim.rowsLen_mapRowsO _ (cornerPP E M G) o hrows
  have hshape : cellcount.pShapeAt (cellcount.ppevalPC (cornerPP E M G)
      (BPair.ofPos en) ed 2) o 1 :=
    cellcount.pShapeAt_of hplen hprows (cornerPP_ble _ _ E M G)
  have hevsq : elim.sqAt (cellcount.evalPC
      (cellcount.ppevalPC (cornerPP E M G) (BPair.ofPos en) ed 2)
      ⟨hp, hm⟩ Pos.one 1) o :=
    elim.sqAt_of ((ground.length_map _ _).trans hplen)
      (elim.rowsLen_mapRowsO _ _ o hprows)
  have hsitesq : elim.sqAt (cornerSite E M G en ed hp hm) o :=
    inertia.sqAt_siteDatum o _ _
      (elim.sqAt_matAdd o _ _ (inertia.sqAt_matScale o (en * en) E hE)
        (inertia.sqAt_matScale o (en * ed * hm) G hG))
      (elim.sqAt_matAdd o _ _ (inertia.sqAt_matScale o (ed * ed) M hM)
        (inertia.sqAt_matScale o (en * ed * hp) G hG))
  constructor
  · intro h
    exact ⟨hE, hM, hG,
      inertia.splitRead_congr _ _ hsitesq
        (cornerPP_eval E M G en ed hp hm) sp h.2.1,
      h.2.2⟩
  · intro h
    exact ⟨hshape,
      inertia.splitRead_congr _ _ hevsq
        (elim.matOne_symm (cornerPP_eval E M G en ed hp hm)) sp
        h.2.2.2.1,
      h.2.2.2.2⟩

/-! `lem:corner`'s ray coordinate read-backs: the cell's two
located outputs read back at squares.  The ray `[a : b]` sits in
the extent `η₁ = [n₁ : d₁]` exactly at the cross-multiplied
comparison `a d₁² ≤ n₁² b` (`rayInExtent`), one value across the
ray's representatives and across the extent's
(`rayInExtent_ray`, `rayInExtent_ext`); and a level reads through
its height at the floor `κ = [kn : kd]`, the level's square
against the weight product at the floor's square
(`levelClears`), which at the ray's scale tie `α ed² = en² β` and
the cofactor `λ = β (η η′)` is the height against the floor
(`level_height`), the two end weights' own scale withdrawing from
the comparison. -/

/-- The ray sits in the extent: the ray `[a:b]` against the
extent `eta_1 = [n1:d1]` at the squares' cross-multiplied read
(`lem:corner`'s ray read-back). -/
def rayInExtent (a b n1 d1 : Pos) : Prop :=
  a * (d1 * d1) ≤ n1 * n1 * b

instance instCorner6 (a b n1 d1 : Pos) :
    Decidable (rayInExtent a b n1 d1) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The membership is one value across the ray's
representatives. -/
theorem rayInExtent_ray (a b a' b' n1 d1 : Pos)
    (h : a * b' = a' * b) :
    rayInExtent a b n1 d1 ↔ rayInExtent a' b' n1 d1 := by
  constructor
  · intro hle
    refine ground.le_of_mul_le (c := b) ?_
    have h1 : a * (d1 * d1) * b' ≤ n1 * n1 * b * b' :=
      ground.mul_le_mul_right b' hle
    rw [ground.mul_right_comm a (d1 * d1) b', h,
      ground.mul_right_comm a' b (d1 * d1),
      ground.mul_right_comm (n1 * n1) b b'] at h1
    exact h1
  · intro hle
    refine ground.le_of_mul_le (c := b') ?_
    have h1 : a' * (d1 * d1) * b ≤ n1 * n1 * b' * b :=
      ground.mul_le_mul_right b hle
    rw [ground.mul_right_comm a' (d1 * d1) b, ← h,
      ground.mul_right_comm a b' (d1 * d1),
      ground.mul_right_comm (n1 * n1) b' b] at h1
    exact h1

/-- The membership is one value across the extent's
representatives. -/
theorem rayInExtent_ext (a b n1 d1 n1' d1' : Pos)
    (h : n1 * d1' = n1' * d1) :
    rayInExtent a b n1 d1 ↔ rayInExtent a b n1' d1' := by
  constructor
  · intro hle
    refine ground.le_of_mul_le (c := d1 * d1) ?_
    have h1 : a * (d1 * d1) * (d1' * d1')
        ≤ n1 * n1 * b * (d1' * d1') :=
      ground.mul_le_mul_right (d1' * d1') hle
    rw [ground.mul_right_comm a (d1 * d1) (d1' * d1'),
      ground.mul_right_comm (n1 * n1) b (d1' * d1'),
      ground.mul_mul_mul_comm n1 n1 d1' d1', h,
      ← ground.mul_mul_mul_comm n1' n1' d1 d1,
      ground.mul_right_comm (n1' * n1') (d1 * d1) b] at h1
    exact h1
  · intro hle
    refine ground.le_of_mul_le (c := d1' * d1') ?_
    have h1 : a * (d1' * d1') * (d1 * d1)
        ≤ n1' * n1' * b * (d1 * d1) :=
      ground.mul_le_mul_right (d1 * d1) hle
    rw [ground.mul_right_comm a (d1' * d1') (d1 * d1),
      ground.mul_right_comm (n1' * n1') b (d1 * d1),
      ground.mul_mul_mul_comm n1' n1' d1 d1, ← h,
      ← ground.mul_mul_mul_comm n1 n1 d1' d1',
      ground.mul_right_comm (n1 * n1) (d1' * d1') b] at h1
    exact h1

/-- The level clears the floor: the level's square against the
weight product at the floor's square, one pair comparison
(`lem:corner`'s height read at the two end weights' own scale). -/
def levelClears (ln ld kn kd al be : Pos) : Prop :=
  kn * kn * (al * be) * (ld * ld) ≤ ln * ln * (kd * kd)

instance instCorner7 (ln ld kn kd al be : Pos) :
    Decidable (levelClears ln ld kn kd al be) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A level reads through its height: at the ray's scale tie and
the cofactor `lambda = be (eta eta')` the comparison is the
height against the floor. -/
theorem level_height (en ed hn hd ln ld kn kd al be : Pos)
    (hray : al * (ed * ed) = en * en * be)
    (hcof : ln * (ed * hd) = ld * (be * (en * hn))) :
    levelClears ln ld kn kd al be ↔ kn * hd ≤ hn * kd := by
  have q1 : kn * kn * (al * be) * (ld * ld) * (ed * ed * (hd * hd))
      = kn * hd * (kn * hd) * (ld * ld * (be * be * (en * en))) := by
    rw [ground.mul_mul_mul_comm (kn * kn * (al * be)) (ld * ld)
        (ed * ed) (hd * hd),
      ground.mul_assoc (kn * kn) (al * be) (ed * ed),
      ground.mul_right_comm al be (ed * ed), hray,
      ground.mul_assoc (en * en) be be,
      ground.mul_comm (en * en) (be * be),
      ground.mul_mul_mul_comm kn hd kn hd,
      ground.mul_mul_mul_comm (kn * kn) (be * be * (en * en))
        (ld * ld) (hd * hd),
      ground.mul_mul_mul_comm (kn * kn) (hd * hd) (ld * ld)
        (be * be * (en * en)),
      ground.mul_comm (be * be * (en * en)) (hd * hd)]
  have q2 : ln * ln * (kd * kd) * (ed * ed * (hd * hd))
      = hn * kd * (hn * kd) * (ld * ld * (be * be * (en * en))) := by
    rw [← ground.mul_mul_mul_comm ed hd ed hd,
      ground.mul_right_comm (ln * ln) (kd * kd) (ed * hd * (ed * hd)),
      ← ground.mul_mul_mul_comm ln (ed * hd) ln (ed * hd), hcof,
      ground.mul_mul_mul_comm ld (be * (en * hn)) ld (be * (en * hn)),
      ground.mul_mul_mul_comm be (en * hn) be (en * hn),
      ground.mul_mul_mul_comm en hn en hn,
      ground.mul_mul_mul_comm hn kd hn kd,
      ground.mul_assoc (ld * ld) (be * be * (en * en * (hn * hn)))
        (kd * kd),
      ground.mul_assoc (be * be) (en * en * (hn * hn)) (kd * kd),
      ground.mul_assoc (en * en) (hn * hn) (kd * kd),
      ground.mul_comm (hn * hn * (kd * kd))
        (ld * ld * (be * be * (en * en))),
      ground.mul_assoc (ld * ld) (be * be * (en * en))
        (hn * hn * (kd * kd)),
      ground.mul_assoc (be * be) (en * en) (hn * hn * (kd * kd))]
  constructor
  · intro h
    refine ground.posSqLe (ground.le_of_mul_le
      (c := ld * ld * (be * be * (en * en))) ?_)
    rw [← q1, ← q2]
    exact ground.mul_le_mul_right (ed * ed * (hd * hd)) h
  · intro h
    refine ground.le_of_mul_le (c := ed * ed * (hd * hd)) ?_
    rw [q1, q2]
    exact ground.mul_le_mul_right (ld * ld * (be * be * (en * en)))
      (ground.posSqMono h)

/-- The flat window at the corner carrier: the seam levels' window
is the corner counts' at the heights, the scale factor withdrawing
from the order (`thm:flatstep` at `lem:dualtrunc`'s seam
identity). -/
theorem corner_flat {o : Nat} (E M G : Mat)
    (en ed h1p h1m h2p h2m : Pos) (g : Nat)
    (spa spt : inertia.Split o)
    (hE : elim.sqAt E o) (hM : elim.sqAt M o) :
    flatstep.vacFlat (cornerPencil E M en ed) G
        (en * ed * h1p) (en * ed * h1m)
        (en * ed * h2p) (en * ed * h2m) g spa spt
      ↔ (cornerCount E M G en ed h1p h1m g spa
        ∧ cornerCount E M G en ed h2p h2m g spt
        ∧ 1 ≤ g ∧ h1p + h2m < h2p + h1m) := by
  constructor
  · intro h
    match h with
    | ⟨h1, h2, hg, hord⟩ =>
      refine ⟨(corner_dual E M G en ed h1p h1m g spa hE hM).mpr h1,
        (corner_dual E M G en ed h2p h2m g spt hE hM).mpr h2,
        hg, ?_⟩
      rw [← ground.left_distrib (en * ed) h1p h2m,
        ← ground.left_distrib (en * ed) h2p h1m] at hord
      rw [ground.mul_comm (en * ed) (h1p + h2m),
        ground.mul_comm (en * ed) (h2p + h1m)] at hord
      exact ground.lt_of_mul_lt hord
  · intro h
    match h with
    | ⟨h1, h2, hg, hord⟩ =>
      refine ⟨(corner_dual E M G en ed h1p h1m g spa hE hM).mp h1,
        (corner_dual E M G en ed h2p h2m g spt hE hM).mp h2,
        hg, ?_⟩
      rw [← ground.left_distrib (en * ed) h1p h2m,
        ← ground.left_distrib (en * ed) h2p h1m]
      rw [ground.mul_comm (en * ed) (h1p + h2m),
        ground.mul_comm (en * ed) (h2p + h1m)]
      exact ground.mul_lt_mul_right (en * ed) hord

/-! `lem:corner`'s cutoff at the scale: the scale key is the least
natural whose `4η²` multiple clears the dimension fold against the
window's top level and the clearance (`scaleKey`, `scaleKey_ge` its
own witness, `scaleKey_least` the minimality), and at the key's
comparison the seed floor `⟨4σΛ : d_L⟩` clears every window level at
once — a cutoff at or beyond the key and a level at or below the
window's top (`seedClears`, `keyClears`). -/

/-- The clearing quotient's comparison at its own division
witness: the step's multiple joined to the clearance sits at or
beyond the fold. -/
private theorem ceilCore {K S A q r : Nat} (hA : 0 < A)
    (hsum : A * q + r = K - S + (A - 1)) (hlt : r < A) :
    K ≤ A * q + S := by
  match Nat.le_total K S with
  | Or.inl h => exact Nat.le_trans h (Nat.le_add_left S _)
  | Or.inr h =>
    have hr : r ≤ A - 1 := by
      refine Nat.le_of_lt_succ ?_
      show r < A - 1 + 1
      rw [ground.subAdd hA]
      exact hlt
    have h0 : A * q + r ≤ A * q + (A - 1) :=
      Nat.add_le_add (Nat.le_refl (A * q)) hr
    rw [hsum] at h0
    have h3 : K - S + S ≤ A * q + S :=
      Nat.add_le_add (ground.leCancelR (A - 1) h0) (Nat.le_refl S)
    rw [ground.subAdd h] at h3
    exact h3

/-- The clearing quotient is least at its own division witness:
any step multiple clearing the fold sits at or beyond it. -/
private theorem ceilLeastCore {K S A L q r : Nat} (hA : 0 < A)
    (hL : K ≤ A * L + S)
    (hsum : A * q + r = K - S + (A - 1)) : q ≤ L := by
  have hKS : K - S ≤ A * L := by
    match Nat.le_total K S with
    | Or.inl h => rw [ground.subLe K S h]; exact Nat.zero_le _
    | Or.inr h =>
      exact ground.leCancelR S (by rw [ground.subAdd h]; exact hL)
  match Nat.lt_or_ge L q with
  | Or.inr h => exact h
  | Or.inl h =>
    have h0 : A * q ≤ A * q + r := Nat.le_add_right _ _
    rw [hsum] at h0
    have hfin : A * (L + 1) < A * L + A :=
      Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.mul_le_mul_left A h) h0)
        (Nat.lt_of_le_of_lt
          (Nat.add_le_add hKS (Nat.le_refl (A - 1)))
          (Nat.add_lt_add_left (ground.subOneLt hA) (A * L)))
    rw [Nat.mul_succ A L] at hfin
    exact absurd hfin (Nat.lt_irrefl _)

/-- The scale's step is occupied at an occupied scale numerator
and an occupied level denominator. -/
private theorem scalePos (en vd : Nat) (hen : 0 < en) (hvd : 0 < vd) :
    0 < 4 * en * en * vd :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide +kernel) hen) hen)
    hvd

/-- The scale key: the least natural whose `4 eta^2` multiple
clears the dimension fold, the window's top level and the
clearance, the cleared members' division witness (`lem:corner`'s
boundary families, the cutoff at the scale). -/
def scaleKey (en ed vn vd dth xp yp : Nat) : Nat :=
  (ed * ed * (dth * vd + xp * vd + vn) - yp * (ed * ed) * vd
    + (4 * en * en * vd - 1)) / (4 * en * en * vd)

/-- The key's comparison holds at the key, its own witness. -/
theorem scaleKey_ge (en ed vn vd dth xp yp : Nat)
    (hen : 0 < en) (hvd : 0 < vd) :
    ed * ed * (dth * vd + xp * vd + vn)
      ≤ 4 * en * en * vd * scaleKey en ed vn vd dth xp yp
        + yp * (ed * ed) * vd :=
  ceilCore (scalePos en vd hen hvd)
    (ground.natDivRead _ _ (scalePos en vd hen hvd)).1
    (ground.natDivRead _ _ (scalePos en vd hen hvd)).2

/-- The key is the least natural at the comparison. -/
theorem scaleKey_least (en ed vn vd dth xp yp L : Nat)
    (hen : 0 < en) (hvd : 0 < vd)
    (hL : ed * ed * (dth * vd + xp * vd + vn)
      ≤ 4 * en * en * vd * L + yp * (ed * ed) * vd) :
    scaleKey en ed vn vd dth xp yp ≤ L :=
  ceilLeastCore (scalePos en vd hen hvd) hL
    (ground.natDivRead _ _ (scalePos en vd hen hvd)).1

/-- The dimension fold at a window level, the level's own weight
withdrawn from the fold's head. -/
private theorem seedExp (E dth vd vn t : Nat) :
    E * (dth * vd + t * vd + vn)
      = E * (dth * vd) + E * vn + t * E * vd := by
  rw [Nat.left_distrib E (dth * vd + t * vd) vn,
    Nat.left_distrib E (dth * vd) (t * vd),
    ground.mulHeadComm E t vd,
    Nat.add_assoc (E * (dth * vd)) (t * E * vd) (E * vn),
    Nat.add_comm (t * E * vd) (E * vn),
    ← Nat.add_assoc (E * (dth * vd)) (E * vn) (t * E * vd)]

/-- The seed floor's window clearing at the abstract weights: the
level pair's cross-added order carries the top level's clearance
to every level of the window. -/
private theorem seedCore {E vd A L cp dth xp yp x y vn : Nat}
    (hL : E * (dth * vd + xp * vd + vn) ≤ A * L + yp * E * vd)
    (hcp : L ≤ cp) (hlev : x + yp ≤ xp + y) :
    E * (dth * vd + x * vd + vn) ≤ A * cp + y * E * vd := by
  have hstep : x * E * vd + yp * E * vd
      ≤ xp * E * vd + y * E * vd := by
    rw [ground.mulAssoc x E vd, ground.mulAssoc yp E vd,
      ground.mulAssoc xp E vd, ground.mulAssoc y E vd,
      ← ground.mulAddR x yp (E * vd), ← ground.mulAddR xp y (E * vd)]
    exact Nat.mul_le_mul_right (E * vd) hlev
  have h1 : E * (dth * vd + x * vd + vn) + yp * E * vd
      ≤ E * (dth * vd + xp * vd + vn) + y * E * vd := by
    rw [seedExp E dth vd vn x, seedExp E dth vd vn xp,
      Nat.add_assoc (E * (dth * vd) + E * vn) (x * E * vd)
        (yp * E * vd),
      Nat.add_assoc (E * (dth * vd) + E * vn) (xp * E * vd)
        (y * E * vd)]
    exact Nat.add_le_add (Nat.le_refl _) hstep
  have h2 : E * (dth * vd + xp * vd + vn) + y * E * vd
      ≤ A * cp + yp * E * vd + y * E * vd :=
    Nat.add_le_add
      (Nat.le_trans hL
        (Nat.add_le_add (Nat.mul_le_mul_left A hcp) (Nat.le_refl _)))
      (Nat.le_refl _)
  have h4 := Nat.le_trans h1 h2
  rw [Nat.add_assoc (A * cp) (yp * E * vd) (y * E * vd),
    Nat.add_comm (yp * E * vd) (y * E * vd),
    ← Nat.add_assoc (A * cp) (y * E * vd) (yp * E * vd)] at h4
  exact ground.leCancelR (yp * E * vd) h4

/-- The seed floor clears every window level at once: at the
key's comparison, a cutoff at or beyond the key, and a level at or
below the window's top, the floor `⟨4σΛ : d_L⟩` clears the level
by the clearance (`lem:corner`'s cutoff family). -/
theorem seedClears (en ed vn vd dth xp yp x y cp L : Nat)
    (hL : ed * ed * (dth * vd + xp * vd + vn)
      ≤ 4 * en * en * vd * L + yp * (ed * ed) * vd)
    (hcp : L ≤ cp) (hlev : x + yp ≤ xp + y) :
    ed * ed * (dth * vd + x * vd + vn)
      ≤ 4 * en * en * vd * cp + y * (ed * ed) * vd :=
  seedCore hL hcp hlev

/-- The key clears every window level: the seed floor at the scale
key's cutoff, `F = ⟨4σΛ : d_L⟩` at `Λ` the key, clears every level at
or below the window's top by the clearance (`lem:corner`'s cutoff
family, the key's comparison its own witness). -/
theorem keyClears (en ed vn vd dth xp yp x y : Nat)
    (hen : 0 < en) (hvd : 0 < vd) (hlev : x + yp ≤ xp + y) :
    ed * ed * (dth * vd + x * vd + vn)
      ≤ 4 * en * en * vd * scaleKey en ed vn vd dth xp yp
        + y * (ed * ed) * vd :=
  seedClears en ed vn vd dth xp yp x y _ (scaleKey en ed vn vd dth xp yp)
    (scaleKey_ge en ed vn vd dth xp yp hen hvd) (Nat.le_refl _) hlev

/-! `lem:corner`'s height section: the presentation's height
variable substituted first, leaving the pencil's polynomial matrix
in the scale variable alone (`cornerAtHeight` at `poly.pevalC`).
The scale's own cleared evaluation of that section is the corner
site again, so the two substitution orders read one matrix
(`cornerAtHeight_eval` beside `cornerPP_eval`), and the section is
the emitted record's carrier (`thm:decimation`'s `DivRecord`). -/

/-- The presentation's height section: the corner pencil read
along the scale at a stated height, the record's own carrier
(`lem:corner`'s boundary families at `thm:decimation`'s emitted
record). -/
def cornerAtHeight (E M G : Mat) (hp hm : Pos) : split.PMat :=
  (cornerPP E M G).map (fun r => r.map
    (fun P => poly.pevalC P [⟨hp, hm⟩] ground.Pos.one 1))

/-- The outer pair's height substitution at one entry: the base's
memberwise swap on its two surviving keys against the seam weight
scaled by the height, the section's entry in the scale variable. -/
private theorem heightEntry (e m g x : BPair) :
    poly.oneValue
      (poly.pevalC [poly.neg [m, BPair.unit, BPair.swap e],
        [BPair.unit, BPair.swap g]] [x] Pos.one 1)
      [m.swap, g.swap * x, e] := by
  have h0 : poly.oneValue
      (poly.pnorm (poly.scaleP (BPair.ofPos Pos.one)
        (poly.mul (poly.neg [m, BPair.unit, BPair.swap e])
          (poly.powOf [x] 0))))
      [m.swap, BPair.unit, e] :=
    poly.oneValue_trans (poly.pnorm_oneValue _)
      (poly.oneValue_trans (poly.scaleP_one _)
        (poly.oneValue_trans
          (poly.mul_comm (poly.neg [m, BPair.unit, BPair.swap e])
            poly.one)
          (poly.one_mul (poly.neg [m, BPair.unit, BPair.swap e]))))
  have hx : poly.oneValue (poly.powOf [x] 1) [x] :=
    poly.oneValue_trans (poly.mul_comm [x] poly.one) (poly.one_mul [x])
  have h1 : poly.oneValue
      (poly.pnorm (poly.scaleP (BPair.ofPos Pos.one)
        (poly.mul [BPair.unit, BPair.swap g] (poly.powOf [x] 1))))
      [BPair.unit, g.swap * x] :=
    poly.oneValue_trans (poly.pnorm_oneValue _)
      (poly.oneValue_trans (poly.scaleP_one _)
        (poly.oneValue_trans
          (poly.mul_congr [BPair.unit, BPair.swap g] hx)
          ⟨BPair.oneValue_trans
              (BPair.add_congr (BPair.unit_mul x)
                (BPair.oneValue_refl BPair.unit))
              (BPair.unit_add BPair.unit),
            BPair.add_unit (g.swap * x), trivial⟩))
  show poly.oneValue
    (poly.add
      (poly.pnorm (poly.scaleP (BPair.ofPos Pos.one)
        (poly.mul (poly.neg [m, BPair.unit, BPair.swap e])
          (poly.powOf [x] 0))))
      (poly.pnorm (poly.scaleP (BPair.ofPos Pos.one)
        (poly.mul [BPair.unit, BPair.swap g] (poly.powOf [x] 1)))))
    [m.swap, g.swap * x, e]
  exact poly.oneValue_trans (poly.add_congr h0 h1)
    ⟨BPair.add_unit m.swap, BPair.unit_add (g.swap * x),
      BPair.oneValue_refl e, trivial⟩

/-- The three-key list's cleared evaluation at the square: the
three monomials at the point's powers against the clearing's
complementary ones, the cleared variable's fold read at each
key. -/
private theorem evalThree (a0 a1 a2 ln : BPair) (c : Pos) :
    (poly.evalClear [a0, a1, a2] ln c 2).oneValue
      (a0 * ground.bpow ln 0 * ground.bpow (BPair.ofPos c) 2
        + a1 * ground.bpow ln 1 * ground.bpow (BPair.ofPos c) 1
        + a2 * ground.bpow ln 2 * ground.bpow (BPair.ofPos c) 0) := by
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (poly.eval_clearVar [a0, a1, a2] c 2 ln)) ?_
  refine BPair.oneValue_trans
    (poly.eval_famFold (poly.clearVar [a0, a1, a2] c 2) ln) ?_
  rw [poly.length_clearVar]
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => ground.getAt BPair.unit [a0, a1, a2] k
        * ground.bpow (BPair.ofPos c) (2 - k) * ground.bpow ln k)
      (List.range 3) (fun i _ =>
        BPair.mul_congr_left (BPair.oneValue_trans
          (poly.getAt_clearVar [a0, a1, a2] c 2 i)
          (BPair.norm_oneValue _)))) ?_
  refine BPair.oneValue_trans
    (ground.foldB_congr_members _
      (fun k => ground.getAt BPair.unit [a0, a1, a2] k
        * ground.bpow ln k * ground.bpow (BPair.ofPos c) (2 - k))
      (List.range 3) (fun i _ => BPair.oneValue_of_eq
        (BPair.mul_right_comm
          (ground.getAt BPair.unit [a0, a1, a2] i)
          (ground.bpow (BPair.ofPos c) (2 - i))
          (ground.bpow ln i)))) ?_
  show (a0 * ground.bpow ln 0 * ground.bpow (BPair.ofPos c) 2
      + (a1 * ground.bpow ln 1 * ground.bpow (BPair.ofPos c) 1
        + (a2 * ground.bpow ln 2 * ground.bpow (BPair.ofPos c) 0
          + BPair.unit))).oneValue _
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _))) ?_
  exact BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm

/-- The three monomials' regrouping at the entry's join: the
constant key's swapped datum joins the top key's on the far side
of the seam's two members. -/
private theorem addShuffle (a b c d : BPair) :
    c + (b + d) + a = a + b + (c + d) := by
  rw [BPair.add_comm (c + (b + d)) a, ← BPair.add_assoc c b d,
    BPair.add_comm c b, BPair.add_assoc b c d,
    ← BPair.add_assoc a b (c + d)]

/-- The constant key's monomial: the base's swapped magnetic entry
at the clearing's square, the scale's own power absorbing. -/
private theorem constKeyRead (m : BPair) (en ed : Pos) :
    (m.swap * ground.bpow (BPair.ofPos en) 0
      * ground.bpow (BPair.ofPos ed) 2).oneValue
      ((m.scale (ed * ed)).swap) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr_left (BPair.mul_one_read m.swap)) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl m.swap) (bpowSq ed)) ?_
  exact BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.mul_comm m.swap (BPair.ofPos (ed * ed))))
    (BPair.ofPos_scale (ed * ed) m.swap)

/-- The top key's monomial: the base's electric entry at the
scale's square, the clearing's own power absorbing. -/
private theorem topKeyRead (e : BPair) (en ed : Pos) :
    (e * ground.bpow (BPair.ofPos en) 2
      * ground.bpow (BPair.ofPos ed) 0).oneValue
      (e.scale (en * en)) := by
  refine BPair.oneValue_trans (BPair.mul_one_read _) ?_
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl e) (bpowSq en)) ?_
  exact BPair.oneValue_trans
    (BPair.oneValue_of_eq
      (BPair.mul_comm e (BPair.ofPos (en * en))))
    (BPair.ofPos_scale (en * en) e)

/-- The middle key's monomial: the seam weight at the scale's two
members with the height's own members already on the weight's two
sides. -/
private theorem midKeyRead (g : BPair) (en ed hp hm : Pos) :
    (g.swap * (⟨hp, hm⟩ : BPair)
      * ground.bpow (BPair.ofPos en) 1
      * ground.bpow (BPair.ofPos ed) 1).oneValue
      (g.scale (en * ed * hm) + (g.scale (en * ed * hp)).swap) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.mul_congr (BPair.oneValue_refl _)
      (bpow_one_read (BPair.ofPos en))) (bpow_one_read (BPair.ofPos ed))) ?_
  have hrw : g.swap * (⟨hp, hm⟩ : BPair) * BPair.ofPos en
        * BPair.ofPos ed
      = (⟨hp, hm⟩ : BPair)
        * (g.swap * (BPair.ofPos en * BPair.ofPos ed)) := by
    rw [BPair.mul_assoc (g.swap * (⟨hp, hm⟩ : BPair))
        (BPair.ofPos en) (BPair.ofPos ed),
      BPair.mul_comm g.swap (⟨hp, hm⟩ : BPair),
      BPair.mul_assoc (⟨hp, hm⟩ : BPair) g.swap
        (BPair.ofPos en * BPair.ofPos ed)]
  rw [hrw]
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl (⟨hp, hm⟩ : BPair))
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl g.swap)
          (BPair.ofPos_mul en ed))
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq
            (BPair.mul_comm g.swap (BPair.ofPos (en * ed))))
          (BPair.ofPos_scale (en * ed) g.swap)))) ?_
  exact seamHeight g en ed hp hm

/-- The three monomials join to the corner site's entry: the
electric and the seam's lower member on the datum, the magnetic and
the seam's upper member on the swap. -/
private theorem entryJoin (e m g : BPair) (en ed hp hm : Pos) :
    (m.swap * ground.bpow (BPair.ofPos en) 0
        * ground.bpow (BPair.ofPos ed) 2
      + g.swap * (⟨hp, hm⟩ : BPair) * ground.bpow (BPair.ofPos en) 1
        * ground.bpow (BPair.ofPos ed) 1
      + e * ground.bpow (BPair.ofPos en) 2
        * ground.bpow (BPair.ofPos ed) 0).oneValue
      (e.scale (en * en) + g.scale (en * ed * hm)
        + (m.scale (ed * ed) + g.scale (en * ed * hp)).swap) := by
  refine BPair.oneValue_trans
    (BPair.add_congr
      (BPair.add_congr (constKeyRead m en ed) (midKeyRead g en ed hp hm))
      (topKeyRead e en ed)) ?_
  refine BPair.oneValue_of_eq ?_
  rw [← BPair.swap_add (m.scale (ed * ed)) (g.scale (en * ed * hp))]
  exact addShuffle _ _ _ _

/-- The section's entry at the scale point: the base's two
surviving keys read `en² e` against `ed² m`, the seam weight reads
`en ed (swap g)` with the height's two members already distributed
onto its two sides — the corner site's entry. -/
private theorem cornerEntryH (e m g : BPair) (en ed hp hm : Pos) :
    (poly.evalClear
        (poly.pevalC [poly.neg [m, BPair.unit, BPair.swap e],
          [BPair.unit, BPair.swap g]] [⟨hp, hm⟩] Pos.one 1)
        (BPair.ofPos en) ed 2).oneValue
      (e.scale (en * en) + g.scale (en * ed * hm)
        + (m.scale (ed * ed) + g.scale (en * ed * hp)).swap) :=
  BPair.oneValue_trans
    (poly.evalClear_congr (heightEntry e m g (⟨hp, hm⟩ : BPair))
      (BPair.ofPos en) ed 2)
    (BPair.oneValue_trans
      (evalThree m.swap (g.swap * (⟨hp, hm⟩ : BPair)) e
        (BPair.ofPos en) ed)
      (entryJoin e m g en ed hp hm))

/-- One row of the section's evaluation reads the corner site's
row, the three rows' componentwise walk entry by entry. -/
private theorem cornerRowH (en ed hp hm : Pos) : ∀ rE rM rG : List BPair,
    poly.oneValue
      (((List.zipWith (fun h g => [poly.neg h, g])
          (List.zipWith (fun e m =>
              [m, ground.BPair.unit, ground.BPair.swap e]) rE rM)
          (rG.map (fun g =>
              [ground.BPair.unit, ground.BPair.swap g]))).map
          (fun P => poly.pevalC P [⟨hp, hm⟩] Pos.one 1)).map
        (fun p => poly.evalClear p (BPair.ofPos en) ed 2))
      (List.zipWith BPair.add
        (List.zipWith BPair.add (rE.map (fun x => x.scale (en * en)))
          (rG.map (fun x => x.scale (en * ed * hm))))
        ((List.zipWith BPair.add (rM.map (fun x => x.scale (ed * ed)))
          (rG.map (fun x => x.scale (en * ed * hp)))).map BPair.swap))
  | [], _, _ => trivial
  | _ :: _, [], [] => trivial
  | _ :: _, [], _ :: _ => trivial
  | _ :: _, _ :: _, [] => trivial
  | e :: rE, m :: rM, g :: rG =>
    ⟨cornerEntryH e m g en ed hp hm, cornerRowH en ed hp hm rE rM rG⟩

/-- The section's evaluation reads the corner site row by row, the
three data's componentwise walk. -/
private theorem cornerMatH (en ed hp hm : Pos) : ∀ E M G : Mat,
    elim.matOneValue
      (cellcount.evalPC (cornerAtHeight E M G hp hm)
        (BPair.ofPos en) ed 2)
      (cornerSite E M G en ed hp hm)
  | [], _, _ => trivial
  | _ :: _, [], [] => trivial
  | _ :: _, [], _ :: _ => trivial
  | _ :: _, _ :: _, [] => trivial
  | rE :: E, rM :: M, rG :: G =>
    ⟨cornerRowH en ed hp hm rE rM rG, cornerMatH en ed hp hm E M G⟩

/-- The height section's evaluation at the scale reads the corner
site, the two substitution orders one matrix. -/
theorem cornerAtHeight_eval (E M G : Mat) (en ed hp hm : Pos) :
    elim.matOneValue
      (cellcount.evalPC (cornerAtHeight E M G hp hm)
        (ground.BPair.ofPos en) ed 2)
      (cornerSite E M G en ed hp hm) :=
  cornerMatH en ed hp hm E M G

/-- The section's determinant is the presentation's own at the
height substitution: the height section's minor reads the
two-variable minor at the height point, tying the emitted record's
carrier to the corner presentation (`thm:decimation`'s record at
the corner pencil). -/
theorem cornerAtHeight_minor {o : Nat} (E M G : Mat) (hp hm : Pos)
    (hE : elim.sqAt E o) (hM : elim.sqAt M o)
    (hG : elim.sqAt G o) :
    poly.oneValue
      (split.pminor (cornerAtHeight E M G hp hm))
      (poly.pevalC (split.ppminor (cornerPP E M G))
        [⟨hp, hm⟩] Pos.one 1) := by
  have hlen : (cornerPP E M G).length = o :=
    cornerPP_len E M G o (elim.sqAt_len hE) (elim.sqAt_len hM)
      (elim.sqAt_len hG)
  have hrows : elim.rowsLen o (cornerPP E M G) :=
    cornerPP_rows o E M G (elim.rowsLen_of_sqAt hE)
      (elim.rowsLen_of_sqAt hM) (elim.rowsLen_of_sqAt hG)
  have hsq : elim.rowsLen (cornerPP E M G).length (cornerPP E M G) := by
    rw [hlen]
    exact hrows
  exact poly.oneValue_symm
    (elim.evalC_minorPP (cornerPP E M G) [⟨hp, hm⟩] hsq)


end corner
