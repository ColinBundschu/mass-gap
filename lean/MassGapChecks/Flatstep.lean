import MassGap.Flatstep
/-!
The check module for `thm:flatstep`: the batteries re-read the flat
window and the spectral tie by kernel `decide` at an order-one
sector pair joined to an order-two fiber.

The window: the vacuum sector's pencil `H_p = [2]` against the unit
gram carries one count at both levels of the ordered pair
`⟨4 : 1⟩ < ⟨6 : 1⟩` (the levels three and five), the clear sector's
`H_q = [6]` carries the sum's unit at both, and the fiber's
`H = diag(2, 6)` reads the two sectors' block join at the
kernel-literal coupling `List.replicate 1 (List.replicate 1
BPair.unit)` — the joined window by the theorem route beside its own
`decide`.

The window's committed refusals, each named to its binder: the
occupancy at the vacant ground (`vacFlat` refusing the count
naught with both counts and the order holding); the vacuum sector
forged to the level four (`hVf`), every other hypothesis holding
while the forged window and the joined window refuse; the site
ties at a fiber whose second level is four (`hJf`), the join's own
second block reading six while the fiber reads four, both ties
refusing together — the recorded joint tie, an isolating tie forge
being unconstructible at clear-sector counts naught — and the
joined top count moving to two; the clear sector occupied at the
top (`hCf = [4]`, the sum's unit at the anchor and one count at
the top), the two ties holding there while the joined top count
moves; and the ordered pair exchanged, both counts standing at one
while the cross-added order refuses.  The two window splits are
stated certificate data, their reads inside the refused
conclusions.

The spectral tie: at the located roots `0` and `4` with the edge
`[E₀ p : q] = [4 : 2]` the below count and the kernel count both
read one, and `flat_spec` lands `speccut.specRead` — beside the same
read decided raw.  Its committed refusals: an interior root at one
moves the below count to two against the kernel count's one, the
below count's binder refusing at the stated jump and the spectral
read failing there; the same forge at the jump two refuses the
kernel count's binder instead; the least edge `E₀ = p = q = 1`
reads through the theorem's own route, a root at the kernel point
below every edge; the roots' weights discriminate the below read
at a nonunit denominator with its interior forge refused; and
`countAtPair_roots` ties the fiber's top count to the root list's
below count at the count identity's certificate.
-/
set_option maxHeartbeats 4000000

open ground elim inertia certconstruct flatstep

private def u : BPair := BPair.unit

/-- The vacuum sector's pencil, the level two. -/
private def hV : Mat := [[⟨3, 1⟩]]

/-- The clear sector's pencil, the level six. -/
private def hC : Mat := [[⟨7, 1⟩]]

/-- The fiber's pencil, the two sectors' diagonal. -/
private def hJ : Mat := [[⟨3, 1⟩, u], [u, ⟨7, 1⟩]]

private def sp1 (a : BPair) : Split 1 :=
  ⟨⟨idMat 1, rfl⟩, ⟨idMat 1, rfl⟩, [.one a], 0, rfl⟩

private def sp2 (a b : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.one a, .one b], 0, rfl⟩

/-! The vacuum sector's flat window at the ordered pair
`⟨4 : 1⟩ < ⟨6 : 1⟩`: the site data are the levels `-1` and `-3`,
one count each. -/

example : vacFlat hV (idMat 1) 4 1 6 1 1 (sp1 ⟨1, 2⟩) (sp1 ⟨1, 4⟩) := by
  decide +kernel

/-! The clear sector at the same pair: the site data are `3` and
`1`, the sum's unit at both counts. -/

example : countAtPair hC (idMat 1) 4 1 0 (sp1 ⟨4, 1⟩) := by decide +kernel
example : countAtPair hC (idMat 1) 6 1 0 (sp1 ⟨2, 1⟩) := by decide +kernel

/-! The occupancy binder's own record: at the clear sector both
counts hold at the sum's unit and the pair is ordered, while the
window's count conjunct refuses the vacant ground. -/

example : ¬ vacFlat hC (idMat 1) 4 1 6 1 0
    (sp1 ⟨4, 1⟩) (sp1 ⟨2, 1⟩) := by decide +kernel

/-! The fiber's own window: the joined count is the vacuum block's
alone, by the theorem route at the two site ties and then by the
kernel's own `decide`. -/

example : vacFlat hJ (idMat 2) 4 1 6 1 1
    (sp2 ⟨1, 2⟩ ⟨4, 1⟩) (sp2 ⟨1, 4⟩ ⟨2, 1⟩) :=
  flat_window hV (idMat 1) hC (idMat 1) hJ (idMat 2) 4 1 6 1 1
    (sp1 ⟨1, 2⟩) (sp1 ⟨1, 4⟩) (sp1 ⟨4, 1⟩) (sp1 ⟨2, 1⟩)
    (sp2 ⟨1, 2⟩ ⟨4, 1⟩) (sp2 ⟨1, 4⟩ ⟨2, 1⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : vacFlat hJ (idMat 2) 4 1 6 1 1
    (sp2 ⟨1, 2⟩ ⟨4, 1⟩) (sp2 ⟨1, 4⟩ ⟨2, 1⟩) := by decide +kernel

/-! The vacuum sector's own binder: the vacuum forged to the level
four (`hVf`) against the same clear sector at the fiber
`diag(4, 6)` — every other hypothesis holds, the two ties and the
two window splits among them, while the forged sector's window and
the joined window both refuse. -/

private def hVf : Mat := [[⟨5, 1⟩]]
private def hJv : Mat := [[⟨5, 1⟩, u], [u, ⟨7, 1⟩]]

example : ¬ vacFlat hVf (idMat 1) 4 1 6 1 1
    (sp1 ⟨2, 1⟩) (sp1 ⟨1, 2⟩) := by decide +kernel
example : countAtPair hC (idMat 1) 4 1 0 (sp1 ⟨4, 1⟩) := by decide +kernel
example : countAtPair hC (idMat 1) 6 1 0 (sp1 ⟨2, 1⟩) := by decide +kernel
example : matOneValue
    (siteDatum (matAdd hJv (matScale 1 (idMat 2))) (matScale 4 (idMat 2)))
    (blockJoin
      (siteDatum (matAdd hVf (matScale 1 (idMat 1))) (matScale 4 (idMat 1)))
      (elim.nullMat 1 1)
      (siteDatum (matAdd hC (matScale 1 (idMat 1))) (matScale 4 (idMat 1))))
  := by decide +kernel
example : matOneValue
    (siteDatum (matAdd hJv (matScale 1 (idMat 2))) (matScale 6 (idMat 2)))
    (blockJoin
      (siteDatum (matAdd hVf (matScale 1 (idMat 1))) (matScale 6 (idMat 1)))
      (elim.nullMat 1 1)
      (siteDatum (matAdd hC (matScale 1 (idMat 1))) (matScale 6 (idMat 1))))
  := by decide +kernel
example : splitRead
    (siteDatum (matAdd hJv (matScale 1 (idMat 2))) (matScale 4 (idMat 2)))
    (sp2 ⟨2, 1⟩ ⟨4, 1⟩) := by decide +kernel
example : splitRead
    (siteDatum (matAdd hJv (matScale 1 (idMat 2))) (matScale 6 (idMat 2)))
    (sp2 ⟨1, 2⟩ ⟨2, 1⟩) := by decide +kernel
example : ¬ vacFlat hJv (idMat 2) 4 1 6 1 1
    (sp2 ⟨2, 1⟩ ⟨4, 1⟩) (sp2 ⟨1, 2⟩ ⟨2, 1⟩) := by decide +kernel

/-! The site tie's refusal: the fiber `diag(2, 4)` against the same
two sectors.  Every other binder holds — the vacuum sector's window,
the clear sector's two units, the fiber's order and its two splits —
while both ties refuse (the join's second block reads six, the
fiber's four) and the joined top count moves to two. -/

private def hJf : Mat := [[⟨3, 1⟩, u], [u, ⟨5, 1⟩]]

example : splitRead
    (siteDatum (matAdd hJf (matScale 1 (idMat 2))) (matScale 4 (idMat 2)))
    (sp2 ⟨1, 2⟩ ⟨2, 1⟩) := by decide +kernel

example : splitRead
    (siteDatum (matAdd hJf (matScale 1 (idMat 2))) (matScale 6 (idMat 2)))
    (sp2 ⟨1, 4⟩ ⟨1, 2⟩) := by decide +kernel

example : ¬ matOneValue
    (siteDatum (matAdd hJf (matScale 1 (idMat 2))) (matScale 4 (idMat 2)))
    (blockJoin
      (siteDatum (matAdd hV (matScale 1 (idMat 1))) (matScale 4 (idMat 1)))
      (elim.nullMat 1 1)
      (siteDatum (matAdd hC (matScale 1 (idMat 1))) (matScale 4 (idMat 1))))
  := by decide +kernel

example : ¬ matOneValue
    (siteDatum (matAdd hJf (matScale 1 (idMat 2))) (matScale 6 (idMat 2)))
    (blockJoin
      (siteDatum (matAdd hV (matScale 1 (idMat 1))) (matScale 6 (idMat 1)))
      (elim.nullMat 1 1)
      (siteDatum (matAdd hC (matScale 1 (idMat 1))) (matScale 6 (idMat 1))))
  := by decide +kernel

example : ¬ vacFlat hJf (idMat 2) 4 1 6 1 1
    (sp2 ⟨1, 2⟩ ⟨2, 1⟩) (sp2 ⟨1, 4⟩ ⟨1, 2⟩) := by decide +kernel

/-! The clear sector's own binder at the top: at `H_q = [4]` the
sector reads the sum's unit at the anchor and one count at the top,
the two site ties holding at the fiber `diag(2, 4)` while the joined
top count moves to two. -/

private def hCf : Mat := [[⟨5, 1⟩]]

example : countAtPair hCf (idMat 1) 4 1 0 (sp1 ⟨2, 1⟩) := by decide +kernel
example : ¬ countAtPair hCf (idMat 1) 6 1 0 (sp1 ⟨1, 2⟩) := by decide +kernel
example : countAtPair hCf (idMat 1) 6 1 1 (sp1 ⟨1, 2⟩) := by decide +kernel

example : matOneValue
    (siteDatum (matAdd hJf (matScale 1 (idMat 2))) (matScale 4 (idMat 2)))
    (blockJoin
      (siteDatum (matAdd hV (matScale 1 (idMat 1))) (matScale 4 (idMat 1)))
      (elim.nullMat 1 1)
      (siteDatum (matAdd hCf (matScale 1 (idMat 1))) (matScale 4 (idMat 1))))
  := by decide +kernel

example : matOneValue
    (siteDatum (matAdd hJf (matScale 1 (idMat 2))) (matScale 6 (idMat 2)))
    (blockJoin
      (siteDatum (matAdd hV (matScale 1 (idMat 1))) (matScale 6 (idMat 1)))
      (elim.nullMat 1 1)
      (siteDatum (matAdd hCf (matScale 1 (idMat 1))) (matScale 6 (idMat 1))))
  := by decide +kernel

/-! The ordered pair's own binder: the anchor and the top exchanged.
Both counts stand at one and every other conjunct holds, while the
cross-added order `hx + ty < tx + hy` refuses. -/

example : countAtPair hJ (idMat 2) 6 1 1 (sp2 ⟨1, 4⟩ ⟨2, 1⟩) := by decide +kernel
example : countAtPair hJ (idMat 2) 4 1 1 (sp2 ⟨1, 2⟩ ⟨4, 1⟩) := by decide +kernel
example : ¬ vacFlat hJ (idMat 2) 6 1 4 1 1
    (sp2 ⟨1, 4⟩ ⟨2, 1⟩) (sp2 ⟨1, 2⟩ ⟨4, 1⟩) := by decide +kernel

/-! The spectral tie at the located roots `0` and `4`, the edge
`[4 : 2]` — the level two.  The below count and the kernel count
both read one, and the spectral read lands by the theorem route
beside its own `decide`. -/

private def rts : List (BPair × Pos) := [(u, 1), (⟨5, 1⟩, 1)]

example : split.rootsBelow rts (4 * 1) 2 = 1 := by decide +kernel
example : split.rootsAtKernel rts = 1 := by decide +kernel

example : speccut.specRead rts 4 1 2 :=
  flat_spec rts 4 1 2 1 (by decide +kernel) (by decide +kernel)

example : speccut.specRead rts 4 1 2 := by decide +kernel

/-! The below count's own binder: an interior root at the level one
sits off the kernel point and below the edge, so the below count
moves to two against the kernel count's one — the spectral read
failing there. -/

private def rtsF : List (BPair × Pos) := [(u, 1), (⟨2, 1⟩, 1), (⟨5, 1⟩, 1)]

example : ¬ split.rootsBelow rtsF (4 * 1) 2 = 1 := by decide +kernel
example : split.rootsAtKernel rtsF = 1 := by decide +kernel
example : ¬ speccut.specRead rtsF 4 1 2 := by decide +kernel

/-! The kernel count's own binder at the same forge: at the jump two
the below count reads the jump exactly while the kernel count refuses
it. -/

example : split.rootsBelow rtsF (4 * 1) 2 = 2 := by decide +kernel
example : ¬ split.rootsAtKernel rtsF = 2 := by decide +kernel

/-! The least edge: at `E₀ = p = q = 1` a root at the kernel point
still sits below the edge — the sited edge strictly above the sum's
unit at every positive datum — and the tie reads there through the
theorem's own route. -/

example : split.rootsBelow rts (1 * 1) 1 = 1 := by decide +kernel
example : speccut.specRead rts 1 1 1 :=
  flat_spec rts 1 1 1 1 (by decide +kernel) (by decide +kernel)

/-! The roots' weights: a root enters at its cleared pair, the
second datum its weight, and the below read discriminates at it —
the kernel root at weight three with the value-one root at weight
two sitting at or beyond the edge two, and the forged interior
three-halves refusing. -/

private def rtsD : List (BPair × Pos) := [(u, 3), (⟨5, 1⟩, 2)]

example : split.rootsBelow rtsD (4 * 1) 2 = 1 := by decide +kernel
example : split.rootsAtKernel rtsD = 1 := by decide +kernel
example : speccut.specRead rtsD 4 1 2 :=
  flat_spec rtsD 4 1 2 1 (by decide +kernel) (by decide +kernel)

private def rtsDF : List (BPair × Pos) :=
  [(u, 3), (⟨4, 1⟩, 2), (⟨5, 1⟩, 2)]

example : split.rootsBelow rtsDF (4 * 1) 2 = 2 := by decide +kernel
example : split.rootsAtKernel rtsDF = 1 := by decide +kernel
example : ¬ speccut.specRead rtsDF 4 1 2 := by decide +kernel

/-! The two carriers tied: the fiber's top count at the level six
is the root list's below count at the site pencil's own level-one
spelling, `countAtPair_roots` at the count identity's certificate —
the pencil `hJ + G` at the roots three and seven, one root below
the level. -/

private def rtsJ : List (BPair × Pos) := [(⟨4, 1⟩, 1), (⟨8, 1⟩, 1)]

example : split.countRead (matAdd hJ (matScale 1 (idMat 2))) (idMat 2)
    rtsJ 6 Pos.one (sp2 ⟨1, 4⟩ ⟨2, 1⟩) := by decide +kernel
example : split.rootsBelow rtsJ 6 Pos.one = 1 :=
  countAtPair_roots hJ (idMat 2) rtsJ 6 1 1
    (sp2 ⟨1, 4⟩ ⟨2, 1⟩) (sp2 ⟨1, 4⟩ ⟨2, 1⟩) (by decide +kernel) (by decide +kernel)
example : split.rootsBelow rtsJ 6 Pos.one = 1 := by decide +kernel
