import MassGap.Ground
/-!
`thm:chordmap` — the chord map and the channel's base, read at the
walk's level, the balance pair `y = ⟨y₊ : y₋⟩` cross-added onto the
two sides.  The deck relation `z² + y₊ z + 1 = (c₁ + y₋) z`
(`def:deck`) reads its level through the chord `w` joining the
level's members, `w + y₊ = c₁ + y₋` (`chordJoin`).  The relation's
two roots are equal exactly at the crossings, the deck involution's
fixed points, a double root squaring to the constant coefficient
one: the double-root read `crossAt` — the balance square's
cross-added identity `(c₁ + y₋)² + y₊² = 2 y₊ (c₁ + y₋) + 4` —
holds exactly at the two crossing joins `y₊ + 2 = c₁ + y₋`
(`crossLo`) and `y₊ = c₁ + y₋ + 2` (`crossHi`), which is
`cross_split`.  The band is the segment between the two crossing
levels (`bandAt`, the closed segment with both crossings members by
`cross_band_lo` and `cross_band_hi`), its width the coordination
count's `4` (`band_width`, the two roots the half-line walk's
neighbors).  The defect's root is `z*` at `c₁ z* = 1`
(`defectRoot`, `defect_read`), where the relation reads the
bound-state level: the cleared evaluation at `z*`
(`defectLevel`) holds exactly at the join `c₁ y₊ + 1 = c₁ y₋`
(`boundJoin`), which is `defect_level`.  The base of the channel's
value is `c₁` at the mass point's own witness, and the chord and
the defect read two integers agreeing exactly at base two — the
member-key count's two-key read (`prop:row`) — and separating at
base one, where the chord has two terms and the bound level is
itself the lower crossing; both reads are the check module's
instances.
-/

namespace chordmap
open ground

/-- The chord's naming at a stated level, `def:deck`'s relation at
the chord `w` joining the level's members: `w + y₊ = c₁ + y₋`. -/
def chordJoin (c1 : Pos) (yp ym w : Pair) : Prop :=
  (w + yp).oneValue (Pair.ofPos c1 + ym)

instance (c1 : Pos) (yp ym w : Pair) : Decidable (chordJoin c1 yp ym w) :=
  inferInstanceAs (Decidable (_ = _))

/-- The lower crossing join, `y₊ + 2 = c₁ + y₋`. -/
def crossLo (c1 : Pos) (yp ym : Pair) : Prop :=
  (yp + Pair.ofPos 2).oneValue (Pair.ofPos c1 + ym)

instance (c1 : Pos) (yp ym : Pair) : Decidable (crossLo c1 yp ym) :=
  inferInstanceAs (Decidable (_ = _))

/-- The upper crossing join, `y₊ = c₁ + y₋ + 2`. -/
def crossHi (c1 : Pos) (yp ym : Pair) : Prop :=
  yp.oneValue (Pair.ofPos c1 + ym + Pair.ofPos 2)

instance (c1 : Pos) (yp ym : Pair) : Decidable (crossHi c1 yp ym) :=
  inferInstanceAs (Decidable (_ = _))

/-- The double-root read: the relation's two roots are equal, the
chord's square at four spelled through the balance square's
cross-added identity `(c₁ + y₋)² + y₊² = 2 y₊ (c₁ + y₋) + 4`. -/
def crossAt (c1 : Pos) (yp ym : Pair) : Prop :=
  ((Pair.ofPos c1 + ym) * (Pair.ofPos c1 + ym) + yp * yp).oneValue
    (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym) + Pair.ofPos 4)

instance (c1 : Pos) (yp ym : Pair) : Decidable (crossAt c1 yp ym) :=
  inferInstanceAs (Decidable (_ = _))

/-- The band, the segment between the two crossing levels: the
level at or above the lower crossing and at or below the upper
one, both crossings its members. -/
def bandAt (c1 : Pos) (yp ym : Pair) : Prop :=
  ¬ (yp + Pair.ofPos 2 < Pair.ofPos c1 + ym)
  ∧ ¬ (Pair.ofPos c1 + ym + Pair.ofPos 2 < yp)

instance (c1 : Pos) (yp ym : Pair) : Decidable (bandAt c1 yp ym) :=
  inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

/-- The defect's root `z*` at `c₁ z* = 1`. -/
def defectRoot (c1 : Pos) : Pair := ⟨Pos.one, c1⟩

/-- The bound-state join, `c₁ y₊ + 1 = c₁ y₋`. -/
def boundJoin (c1 : Pos) (yp ym : Pair) : Prop :=
  (Pair.ofPos c1 * yp + Pair.ofPos Pos.one).oneValue
    (Pair.ofPos c1 * ym)

instance (c1 : Pos) (yp ym : Pair) : Decidable (boundJoin c1 yp ym) :=
  inferInstanceAs (Decidable (_ = _))

/-- The relation at the defect's root, `def:deck`'s display
evaluated at `z*`: `z*² + y₊ z* + 1 = (c₁ + y₋) z*`. -/
def defectLevel (c1 : Pos) (yp ym : Pair) : Prop :=
  (defectRoot c1 * defectRoot c1 + yp * defectRoot c1
    + Pair.ofPos Pos.one).oneValue
    ((Pair.ofPos c1 + ym) * defectRoot c1)

instance (c1 : Pos) (yp ym : Pair) : Decidable (defectLevel c1 yp ym) :=
  inferInstanceAs (Decidable (_ = _))

/-- The evaluation cleared at `c₁²`, the proof-side spelling. -/
private def defectClear (c1 : Pos) (yp ym : Pair) : Prop :=
  (Pair.ofPos Pos.one + Pair.ofPos c1 * yp + Pair.ofPos (c1 * c1)).oneValue
    (Pair.ofPos (c1 * c1) + Pair.ofPos c1 * ym)

private theorem two_two : Pair.ofPos 2 * Pair.ofPos 2 = Pair.ofPos 4 := rfl

private theorem two_add_two :
    Pair.ofPos 2 + Pair.ofPos 2 = Pair.ofPos 4 := rfl

/-- The double root holds exactly at the two crossing joins: the
gap between the level's two sides is a pair, the balance square's
identity reads that gap's square at four by `Pair.sq_gap` with the
joined term dropping off (`Pair.add_cancel`), and a square at four
has its root at two (`Pair.mul_self_cancel`); at equal sides the
identity would read a pair strictly above itself. -/
theorem cross_split (c1 : Pos) (yp ym : Pair) :
    crossAt c1 yp ym ↔ (crossLo c1 yp ym ∨ crossHi c1 yp ym) := by
  constructor
  · intro h
    rcases Pair.gap_trich yp (Pair.ofPos c1 + ym) with he | ⟨g, hg⟩ | ⟨g, hg⟩
    · exfalso
      have hA : ((Pair.ofPos c1 + ym) * (Pair.ofPos c1 + ym)).oneValue
          (yp * yp) :=
        Pair.mul_congr (Pair.oneValue_symm he) (Pair.oneValue_symm he)
      have hR : (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym)).oneValue
          (yp * yp + yp * yp) := by
        refine Pair.oneValue_trans
          (Pair.mul_congr (Pair.oneValue_refl (Pair.ofPos 2 * yp))
            (Pair.oneValue_symm he)) ?_
        rw [Pair.mul_assoc]
        exact Pair.two_mul (yp * yp)
      have hx : (yp * yp + yp * yp).oneValue
          ((yp * yp + yp * yp) + Pair.ofPos 4) :=
        Pair.oneValue_trans
          (Pair.oneValue_symm
            (Pair.add_congr hA (Pair.oneValue_refl (yp * yp))))
          (Pair.oneValue_trans h
            (Pair.add_congr hR (Pair.oneValue_refl (Pair.ofPos 4))))
      exact ground.lt_ne
        (Pair.lt_congr hx (Pair.oneValue_refl _)
          (Pair.lt_add_right (yp * yp + yp * yp) (Pair.ofPos 4))) rfl
    · left
      have key := Pair.sq_gap yp g
      have hc : (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym) + g * g).oneValue
          (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym) + Pair.ofPos 4) := by
        refine Pair.oneValue_trans (Pair.add_congr
          (Pair.oneValue_symm (Pair.mul_congr
            (Pair.oneValue_refl (Pair.ofPos 2 * yp)) hg))
          (Pair.oneValue_refl (g * g))) ?_
        refine Pair.oneValue_trans (Pair.oneValue_symm key) ?_
        exact Pair.oneValue_trans
          (Pair.add_congr (Pair.mul_congr hg hg) (Pair.oneValue_refl (yp * yp)))
          h
      rw [Pair.add_comm (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym)) (g * g),
        Pair.add_comm (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym))
          (Pair.ofPos 4)] at hc
      have hg2 : g.oneValue (Pair.ofPos 2) :=
        Pair.mul_self_cancel (by rw [two_two]; exact Pair.add_cancel hc)
      exact Pair.oneValue_trans
        (Pair.add_congr (Pair.oneValue_refl yp) (Pair.oneValue_symm hg2)) hg
    · right
      have key := Pair.sq_gap (Pair.ofPos c1 + ym) g
      have hA : (Pair.ofPos 2 * (Pair.ofPos c1 + ym)
            * (Pair.ofPos c1 + ym + g)).oneValue
          (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym)) := by
        rw [Pair.mul_right_comm (Pair.ofPos 2) yp (Pair.ofPos c1 + ym)]
        exact Pair.mul_congr
          (Pair.oneValue_refl (Pair.ofPos 2 * (Pair.ofPos c1 + ym))) hg
      have hc : (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym) + g * g).oneValue
          (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym) + Pair.ofPos 4) := by
        refine Pair.oneValue_trans (Pair.add_congr (Pair.oneValue_symm hA)
          (Pair.oneValue_refl (g * g))) ?_
        · refine Pair.oneValue_trans (Pair.oneValue_symm key) ?_
          refine Pair.oneValue_trans (Pair.add_congr (Pair.mul_congr hg hg)
            (Pair.oneValue_refl ((Pair.ofPos c1 + ym) * (Pair.ofPos c1 + ym))))
            ?_
          rw [Pair.add_comm (yp * yp)
            ((Pair.ofPos c1 + ym) * (Pair.ofPos c1 + ym))]
          exact h
      rw [Pair.add_comm (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym)) (g * g),
        Pair.add_comm (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym))
          (Pair.ofPos 4)] at hc
      have hg2 : g.oneValue (Pair.ofPos 2) :=
        Pair.mul_self_cancel (by rw [two_two]; exact Pair.add_cancel hc)
      exact Pair.oneValue_trans (Pair.oneValue_symm hg)
        (Pair.add_congr (Pair.oneValue_refl (Pair.ofPos c1 + ym)) hg2)
  · intro hor
    rcases hor with hu | hd
    · refine Pair.oneValue_trans (Pair.add_congr
        (Pair.mul_congr (Pair.oneValue_symm hu) (Pair.oneValue_symm hu))
        (Pair.oneValue_refl (yp * yp))) ?_
      refine Pair.oneValue_trans (Pair.sq_gap yp (Pair.ofPos 2)) ?_
      rw [two_two]
      exact Pair.add_congr (Pair.mul_congr
        (Pair.oneValue_refl (Pair.ofPos 2 * yp)) hu)
        (Pair.oneValue_refl (Pair.ofPos 4))
    · show ((Pair.ofPos c1 + ym) * (Pair.ofPos c1 + ym) + yp * yp).oneValue
        (Pair.ofPos 2 * yp * (Pair.ofPos c1 + ym) + Pair.ofPos 4)
      rw [Pair.add_comm ((Pair.ofPos c1 + ym) * (Pair.ofPos c1 + ym))
        (yp * yp)]
      refine Pair.oneValue_trans (Pair.add_congr
        (Pair.mul_congr hd hd)
        (Pair.oneValue_refl
          ((Pair.ofPos c1 + ym) * (Pair.ofPos c1 + ym)))) ?_
      refine Pair.oneValue_trans (Pair.sq_gap (Pair.ofPos c1 + ym)
        (Pair.ofPos 2)) ?_
      rw [two_two, Pair.mul_right_comm (Pair.ofPos 2) yp
        (Pair.ofPos c1 + ym)]
      exact Pair.add_congr (Pair.mul_congr
        (Pair.oneValue_refl (Pair.ofPos 2 * (Pair.ofPos c1 + ym)))
        (Pair.oneValue_symm hd))
        (Pair.oneValue_refl (Pair.ofPos 4))

/-- The band's width is the coordination count `4`: the upper
crossing's level joins four to the lower crossing's, the two
crossing joins the theorem's binders. -/
theorem band_width (c1 : Pos) (yp yp' ym : Pair)
    (hu : crossLo c1 yp ym) (hd : crossHi c1 yp' ym) :
    yp'.oneValue (yp + Pair.ofPos 4) := by
  refine Pair.oneValue_trans hd ?_
  refine Pair.oneValue_trans (Pair.add_congr (Pair.oneValue_symm hu)
    (Pair.oneValue_refl (Pair.ofPos 2))) ?_
  rw [Pair.add_assoc yp (Pair.ofPos 2) (Pair.ofPos 2), two_add_two]
  exact Pair.oneValue_refl _

/-- The lower crossing is a member of the band
(`Pair.band_of_join` at the gap two). -/
theorem cross_band_lo (c1 : Pos) (yp ym : Pair) (hu : crossLo c1 yp ym) :
    bandAt c1 yp ym :=
  Pair.band_of_join hu

/-- The upper crossing is a member of the band, the two flanks
exchanged. -/
theorem cross_band_hi (c1 : Pos) (yp ym : Pair) (hd : crossHi c1 yp ym) :
    bandAt c1 yp ym :=
  let t := Pair.band_of_join (Pair.oneValue_symm hd)
  ⟨t.2, t.1⟩
/-- The defect root's own witness, `c₁ z* = 1` at every base. -/
theorem defect_read (c1 : Pos) :
    (Pair.ofPos c1 * defectRoot c1).oneValue (Pair.ofPos Pos.one) := by
  show c1 * Pos.one * Pos.one = Pos.one * (Pos.one * c1)
  rw [mul_one, mul_one, one_mul, one_mul]

private theorem clear_bound (c1 : Pos) (yp ym : Pair) :
    defectClear c1 yp ym ↔ boundJoin c1 yp ym := by
  constructor
  · intro h
    have h1 : (Pair.ofPos Pos.one + Pair.ofPos c1 * yp
          + Pair.ofPos (c1 * c1)).oneValue
        (Pair.ofPos (c1 * c1) + Pair.ofPos c1 * ym) := h
    rw [Pair.add_comm (Pair.ofPos (c1 * c1)) (Pair.ofPos c1 * ym)] at h1
    show (Pair.ofPos c1 * yp + Pair.ofPos Pos.one).oneValue
      (Pair.ofPos c1 * ym)
    rw [Pair.add_comm (Pair.ofPos c1 * yp) (Pair.ofPos Pos.one)]
    exact Pair.add_cancel h1
  · intro h
    have h1 : (Pair.ofPos c1 * yp + Pair.ofPos Pos.one).oneValue
        (Pair.ofPos c1 * ym) := h
    have h2 := Pair.add_congr h1 (Pair.oneValue_refl (Pair.ofPos (c1 * c1)))
    rw [Pair.add_comm (Pair.ofPos c1 * yp) (Pair.ofPos Pos.one),
      Pair.add_comm (Pair.ofPos c1 * ym) (Pair.ofPos (c1 * c1))] at h2
    show (Pair.ofPos Pos.one + Pair.ofPos c1 * yp
        + Pair.ofPos (c1 * c1)).oneValue
      (Pair.ofPos (c1 * c1) + Pair.ofPos c1 * ym)
    exact h2

/-- The evaluation's left side scaled at the clearing: the three
summands collect entrywise (`Pair.root_sq_scale`,
`Pair.root_scale`, `Pair.one_mul`). -/
private theorem clearL (c1 : Pos) (yp : Pair) :
    ((defectRoot c1 * defectRoot c1 + yp * defectRoot c1
        + Pair.ofPos Pos.one) * Pair.ofPos (c1 * c1)).oneValue
      (Pair.ofPos Pos.one + Pair.ofPos c1 * yp
        + Pair.ofPos (c1 * c1)) := by
  refine Pair.oneValue_trans
    (Pair.right_distrib
      (defectRoot c1 * defectRoot c1 + yp * defectRoot c1)
      (Pair.ofPos Pos.one) (Pair.ofPos (c1 * c1))) ?_
  refine Pair.add_congr
    (Pair.oneValue_trans
      (Pair.right_distrib (defectRoot c1 * defectRoot c1)
        (yp * defectRoot c1) (Pair.ofPos (c1 * c1))) ?_)
    (Pair.one_mul (Pair.ofPos (c1 * c1)))
  refine Pair.add_congr (Pair.root_sq_scale c1) ?_
  rw [Pair.mul_assoc yp (defectRoot c1) (Pair.ofPos (c1 * c1))]
  refine Pair.oneValue_trans
    (Pair.mul_congr (Pair.oneValue_refl yp) (Pair.root_scale c1)) ?_
  rw [Pair.mul_comm yp (Pair.ofPos c1)]
  exact Pair.oneValue_refl _

/-- The evaluation's right side scaled at the clearing. -/
private theorem clearR (c1 : Pos) (ym : Pair) :
    (((Pair.ofPos c1 + ym) * defectRoot c1)
        * Pair.ofPos (c1 * c1)).oneValue
      (Pair.ofPos (c1 * c1) + Pair.ofPos c1 * ym) := by
  rw [Pair.mul_assoc (Pair.ofPos c1 + ym) (defectRoot c1)
    (Pair.ofPos (c1 * c1))]
  refine Pair.oneValue_trans
    (Pair.mul_congr (Pair.oneValue_refl (Pair.ofPos c1 + ym))
      (Pair.root_scale c1)) ?_
  refine Pair.oneValue_trans
    (Pair.right_distrib (Pair.ofPos c1) ym (Pair.ofPos c1)) ?_
  refine Pair.add_congr ?_ ?_
  · show (c1 * c1) * Pos.one = (c1 * c1) * (Pos.one * Pos.one)
    rw [ground.mul_one (c1 * c1), ground.one_mul Pos.one,
      ground.mul_one (c1 * c1)]
  · rw [Pair.mul_comm ym (Pair.ofPos c1)]
    exact Pair.oneValue_refl _

/-- The evaluation and its clearing read one value, both sides
scaled at `c₁²` (`def:ground`'s homogeneity). -/
private theorem level_clear (c1 : Pos) (yp ym : Pair) :
    defectLevel c1 yp ym ↔ defectClear c1 yp ym := by
  constructor
  · intro h
    exact Pair.oneValue_trans
      (Pair.oneValue_trans (Pair.oneValue_symm (clearL c1 yp))
        (Pair.mul_congr h (Pair.oneValue_refl (Pair.ofPos (c1 * c1)))))
      (clearR c1 ym)
  · intro h
    have hs : ((defectRoot c1 * defectRoot c1 + yp * defectRoot c1
          + Pair.ofPos Pos.one) * Pair.ofPos (c1 * c1)).oneValue
        (((Pair.ofPos c1 + ym) * defectRoot c1)
          * Pair.ofPos (c1 * c1)) :=
      Pair.oneValue_trans (clearL c1 yp)
        (Pair.oneValue_trans h (Pair.oneValue_symm (clearR c1 ym)))
    rw [Pair.mul_comm (defectRoot c1 * defectRoot c1
        + yp * defectRoot c1 + Pair.ofPos Pos.one)
        (Pair.ofPos (c1 * c1)),
      Pair.mul_comm ((Pair.ofPos c1 + ym) * defectRoot c1)
        (Pair.ofPos (c1 * c1))] at hs
    exact Pair.mul_cancel hs

/-- The relation at the defect root reads the level exactly at the
bound-state join: the evaluation clears at `c₁²`
(`Definition~def:ground`'s homogeneity) and the join's shared
summand drops off the cleared read. -/
theorem defect_level (c1 : Pos) (yp ym : Pair) :
    defectLevel c1 yp ym ↔ boundJoin c1 yp ym :=
  Iff.trans (level_clear c1 yp ym) (clear_bound c1 yp ym)

end chordmap
