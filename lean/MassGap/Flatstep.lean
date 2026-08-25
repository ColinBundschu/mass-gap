import MassGap.Speccut
/-!
`thm:flatstep` — the window cut is a flat step of the decimated
counting function, reached by located jump comparisons on the
decimated symbols.

Per fiber and per charge — the `d_f`-ality class of
`lem:chargedcell`(i), `M` of the unit charge class — the counting
function's first jump sits at or above `ε₀ + E₀κ`, and on the
vacuum's own sector its second jump does, the first the window's
`ε₀`, the boundary pivot's own root (`thm:decimation`(i)).  The
vacuum sector's window is `vacFlat`: two counts at
`certconstruct.countAtPair`, the ground's own at the anchor and at
the top, the count occupied and the ordered level pair cross-added
onto the sides; a sector off the vacuum carries its two counts at
the sum's unit at the same pair.

Each comparison is two counts at located pairs, and the counts split
over the sector blocking: `flat_window` carries the vacuum sector's
window onto the whole fiber across `lem:inertia`'s join
(`inertia.rev_join` at the vacant coupling `elim.nullMat`), the
site tie at
each level a stated conjunct — the fiber's own site datum reading
the two sectors' block join — so the joined level's count is the
vacuum block's alone, the clear block's own at the sum's unit.  Each
stored level names its representative across `lem:dualtrunc`'s seam
identity (`certconstruct.countAtPair_scale`), the count blind to the
ray's positive factor.

The comparisons read
`spec(H) ⊂ {ε₀} ∪ [ε₀ + E₀κ, ∞)` on the window, the cut at that
window at every ground (`lem:speccut`): `flat_spec` reads the located
root list against `lem:split`'s count identity — `split.rootsBelow`
at the edge `[E₀ p : q]` against the kernel point's own count — and
lands `speccut.specRead`.  A root at the kernel point sits below the
edge, so the kernel count never exceeds the below count; at the two
counts equal the two memberships coincide root by root, and a root
off the kernel point then sits at or beyond the edge.  The two
carriers tie at `countAtPair_roots`: a balance-pair level's count is
the root list's below count at the count identity's certificate
(`split.countRead` at the site pencil's level-one spelling,
`lem:inertia`'s exchange).  The cut
identification itself is `lem:speccut`'s `spec_to_cut`, read there.
-/

namespace flatstep
open ground elim inertia certconstruct

/-- The vacuum sector's flat window: the counting function at the
anchor and at the top at one count, the ground's own, occupied at
the anchor and unmoved at the top over the ordered cross-added
level pair — the sector's second jump at or beyond the top
(`thm:flatstep`; the counts `certconstruct.countAtPair`'s, the
anchor's own site the window datum's read). -/
def vacFlat {o : Nat} (H G : Mat) (hx hy tx ty : Pos) (g : Nat)
    (spa spt : Split o) : Prop :=
  countAtPair H G hx hy g spa ∧ countAtPair H G tx ty g spt
  ∧ 1 ≤ g ∧ hx + ty < tx + hy

instance {o : Nat} (H G : Mat) (hx hy tx ty : Pos) (g : Nat)
    (spa spt : Split o) : Decidable (vacFlat H G hx hy tx ty g spa spt) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The sector join's order read: the coupling slab is the unit
family at the two sector orders, so the join's rows sit at the summed
order, and its row count is the fiber datum's own carried across the
site tie. -/
private theorem sqJoin {k m : Nat} (P Q S : Mat)
    (hP : sqAt P k) (hQ : sqAt Q m) (hS : sqAt S (k + m))
    (htie : matOneValue S (blockJoin P (elim.nullMat k m) Q)) :
    sqAt (blockJoin P (elim.nullMat k m) Q) (k + m) :=
  elim.sqAt_of ((elim.matOne_length htie).symm.trans
      (elim.sqAt_len hS))
    (inertia.rowsLen_blockJoin P (elim.nullMat k m) Q k m
      (elim.rowsLen_of_sqAt hP) (elim.rowsLen_nullMat k m)
      (elim.rowsLen_cast (elim.length_nullMat k m)
        (elim.rowsLen_transposeM _))
      (elim.rowsLen_of_sqAt hQ))

/-- The joined level's count at one level: the fiber's site datum
reads the two sectors' block join, so its split counts the two
sectors' counts summed (`lem:inertia`'s addition clause). -/
private theorem joinCount {k m : Nat} (Hp Gp Hq Gq H G : Mat)
    (x y : Pos) (a b : Nat) (spP : Split k) (spQ : Split m)
    (spS : Split (k + m))
    (hp : splitRead
      (siteDatum (matAdd Hp (matScale y Gp)) (matScale x Gp)) spP)
    (hpn : revAt spP = a)
    (hq : splitRead
      (siteDatum (matAdd Hq (matScale y Gq)) (matScale x Gq)) spQ)
    (hqn : revAt spQ = b)
    (htie : matOneValue
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd Hp (matScale y Gp)) (matScale x Gp))
        (elim.nullMat k m)
        (siteDatum (matAdd Hq (matScale y Gq)) (matScale x Gq))))
    (hS : splitRead
      (siteDatum (matAdd H (matScale y G)) (matScale x G)) spS) :
    revAt spS = a + b := by
  have hjoin := inertia.splitRead_congr _ _
    (sqJoin _ _ _ hp.1 hq.1 hS.1 htie) htie spS hS
  rw [inertia.rev_join _ _ spP hp spQ hq spS hjoin, hpn, hqn]

/-- The window's transport across the sector blocking: the vacuum
sector's flat window and a sector at the sum's unit at both levels
join to the fiber's own flat window, the site tie at each level the
join's read and the count the vacuum block's alone
(`thm:flatstep`'s second sentence, `lem:inertia`'s join). -/
theorem flat_window {k m : Nat} (Hp Gp Hq Gq H G : Mat)
    (hx hy tx ty : Pos) (g : Nat)
    (spa spt : Split k) (sqa sqt : Split m)
    (spSa spSt : Split (k + m))
    (hvac : vacFlat Hp Gp hx hy tx ty g spa spt)
    (hqa : countAtPair Hq Gq hx hy 0 sqa)
    (hqt : countAtPair Hq Gq tx ty 0 sqt)
    (hH : sqAt H (k + m)) (hG : sqAt G (k + m))
    (htiea : matOneValue
      (siteDatum (matAdd H (matScale hy G)) (matScale hx G))
      (blockJoin
        (siteDatum (matAdd Hp (matScale hy Gp)) (matScale hx Gp))
        (elim.nullMat k m)
        (siteDatum (matAdd Hq (matScale hy Gq)) (matScale hx Gq))))
    (htiet : matOneValue
      (siteDatum (matAdd H (matScale ty G)) (matScale tx G))
      (blockJoin
        (siteDatum (matAdd Hp (matScale ty Gp)) (matScale tx Gp))
        (elim.nullMat k m)
        (siteDatum (matAdd Hq (matScale ty Gq)) (matScale tx Gq))))
    (hSa : splitRead
      (siteDatum (matAdd H (matScale hy G)) (matScale hx G)) spSa)
    (hSt : splitRead
      (siteDatum (matAdd H (matScale ty G)) (matScale tx G)) spSt) :
    vacFlat H G hx hy tx ty g spSa spSt :=
  ⟨⟨hH, hG, hSa,
     joinCount Hp Gp Hq Gq H G hx hy g 0 spa sqa spSa
       hvac.1.2.2.1 hvac.1.2.2.2 hqa.2.2.1 hqa.2.2.2 htiea hSa⟩,
   ⟨hH, hG, hSt,
     joinCount Hp Gp Hq Gq H G tx ty g 0 spt sqt spSt
       hvac.2.1.2.2.1 hvac.2.1.2.2.2 hqt.2.2.1 hqt.2.2.2 htiet hSt⟩,
   hvac.2.2.1, hvac.2.2.2⟩

/-- The comparison's two carriers are one count: a count at a
balance-pair level ties to the count identity's root-list read at
the site pencil's own level-one spelling, the reversal against the
roots below (`thm:flatstep`'s two counts at located pairs reading
the spectrum, `lem:split`'s count identity at `lem:inertia`'s
exchange). -/
theorem countAtPair_roots {o : Nat} (H G : Mat)
    (roots : List (BPair × Pos)) (x y : Pos) (g : Nat)
    (sp sp' : Split o)
    (h : countAtPair H G x y g sp)
    (hcr : split.countRead (matAdd H (matScale y G)) G roots x Pos.one
      sp') :
    split.rootsBelow roots x Pos.one = g := by
  have hsp' : splitRead
      (siteDatum (matAdd H (matScale y G)) (matScale x G)) sp' := by
    have hs := hcr.2.2.2.2.1
    rw [inertia.matScale_one (matAdd H (matScale y G))] at hs
    exact hs
  rw [← hcr.2.2.2.2.2, inertia.rev_exchange
    (siteDatum (matAdd H (matScale y G)) (matScale x G)) sp' sp
    hsp' h.2.2.1]
  exact h.2.2.2

/-- A root at the kernel point sits below the edge: its rescaling
reads the sum's unit and the edge's own site sits strictly above
it. -/
private theorem kernelBelow (E0 p q : Pos) (r : BPair × Pos)
    (h : r.1.oneValue BPair.unit) :
    r.1.scale q < BPair.ofPos (E0 * p * r.2) :=
  BPair.lt_congr
    (BPair.oneValue_trans (ground.unitScale q)
      (BPair.oneValue_symm (BPair.scale_congr q h)))
    (BPair.oneValue_refl _) (ground.unitLtOfPos (E0 * p * r.2))

/-- The comparisons reach the cut: at the located root list's below
count and its kernel count reading one value, the located spectrum
sits at the kernel point or at or beyond the edge — `lem:split`'s
count identity at `split.rootsBelow` landing `lem:speccut`'s own
spectral read (`thm:flatstep`'s third sentence).  Every kernel root
sits below every edge, the sited edge strictly above the sum's unit
at every positive datum, so the two counts equal pins the two
memberships member by member. -/
theorem flat_spec (roots : List (BPair × Pos)) (E0 p q : Pos)
    (g : Nat)
    (htop : split.rootsBelow roots (E0 * p) q = g)
    (hker : split.rootsAtKernel roots = g) :
    speccut.specRead roots E0 p q := by
  have hbelow : roots.countP (fun r =>
      decide (r.1.scale q < BPair.ofPos (E0 * p * r.2))) = g := htop
  have hker' : roots.countP (fun r =>
      decide (r.1.oneValue BPair.unit)) = g := hker
  have heq : ground.countBy (fun r : BPair × Pos =>
        decide (r.1.oneValue BPair.unit)) roots
      = ground.countBy (fun r : BPair × Pos =>
        decide (r.1.scale q < BPair.ofPos (E0 * p * r.2))) roots := by
    rw [← ground.countP_read, ← ground.countP_read, hker', hbelow]
  show (roots.all (fun r =>
    decide (r.1.oneValue BPair.unit)
      || !(decide (r.1.scale q < BPair.ofPos (E0 * p * r.2))))) = true
  exact ground.countBy_eq_all _ _
    (fun r hr => decide_eq_true
      (kernelBelow E0 p q r (of_decide_eq_true hr))) roots heq

end flatstep
