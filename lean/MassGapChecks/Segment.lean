import MassGap.Segment
/-!
The check module for `prop:segment`: the batteries re-read the
base's three matrix forms and the pencil's degree-one homogeneity by
kernel `decide` at the window `diag = [4, 8]` with the magnetic
matrix at unit diagonal and count-one couplings — the three arms of
the site map against their named targets and their displayed values
(the free end's electric diagonal, the interior pair `[3 : 5]`'s
site datum, the contact end's balance partner), the homogeneity at
the factor two decided at the fixture and consumed through
`pencil_scale`, the literal-equality refusal at the norm-gauge
boundary (the canonical representative does not commute with the
rescaling literally, the one-value read the forced spelling), and
the ray's spectral descent (`ray_count` at `u = 2` over the level
`⟨20 : 1⟩`, the base count one at its split certificate, the scaled
certificate decided, the theorem route, and the two refusals — the
false count at the base fixture and the forged split failing the
scaled site's read — isolating the two load-bearing binders), and
the base's ray reading, two interior pairs one ray exactly at the
cross-multiplied identity with the ends their own classes and the
cross-class reads refused. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground elim inertia pairpencil certconstruct segment

private def u : BPair := BPair.unit

/-- The magnetic fixture: unit diagonal with count-one couplings,
the off-diagonal weights live in every arm. -/
private def mF : Mat := [[u, BPair.ofNat 1], [BPair.ofNat 1, u]]

/-- A one-block split at the identity congruence, the 2×2 block's
own datum. -/
private def spB (a b c : BPair) : Split 2 :=
  ⟨⟨idMat 2, rfl⟩, ⟨idMat 2, rfl⟩, [.two a b c], 0, rfl⟩

/-! The site map's three arms against their named targets: the free
end the electric diagonal alone, the interior pair the pencil's site
datum, the contact end the magnetic member's balance partner. -/

example : matOneValue (siteAt [4, 8] mF .free) (pencilE [4, 8]) := by
  decide +kernel
example : matOneValue (siteAt [4, 8] mF (.mid 3 5))
    (pencilH 3 5 [4, 8] mF) := by decide +kernel
example : matOneValue (siteAt [4, 8] mF .contact) (matSwap mF) := by
  decide +kernel

/-! The three arms' displayed values: the window contents on the
free diagonal, the interior entries `3·diag` against the swapped
`5`-weighted couplings, and the contact end's negated couplings. -/

example : matOneValue (siteAt [4, 8] mF .free)
    [[⟨5, 1⟩, u], [u, ⟨9, 1⟩]] := by decide +kernel
example : matOneValue (siteAt [4, 8] mF (.mid 3 5))
    [[⟨13, 1⟩, ⟨1, 6⟩], [⟨1, 6⟩, ⟨25, 1⟩]] := by decide +kernel
example : matOneValue (siteAt [4, 8] mF .contact)
    [[u, ⟨1, 2⟩], [⟨1, 2⟩, u]] := by decide +kernel

/-! The homogeneity at the factor two: the pencil at the weights
`[6 : 10]` reads one value with the `[3 : 5]` pencil rescaled —
decided at the fixture, then consumed through the theorem. -/

example : matOneValue (pencilH (2 * 3) (2 * 5) [4, 8] mF)
    (matScale 2 (pencilH 3 5 [4, 8] mF)) := by decide +kernel
example : matOneValue (pencilH (2 * 3) (2 * 5) [4, 8] mF)
    (matScale 2 (pencilH 3 5 [4, 8] mF)) :=
  pencil_scale 2 3 5 [4, 8] mF

/-! The norm-gauge boundary: the literal equality refuses at the
fixture — the entry's canonical representative does not commute with
the rescaling literally — so the one-value read is the homogeneity
clause's forced spelling. -/

example : ¬ (pencilH (2 * 3) (2 * 5) [4, 8] mF
    = matScale 2 (pencilH 3 5 [4, 8] mF)) := by decide +kernel

/-! The ray's spectral descent at `u = 2` over the level `⟨20 : 1⟩`:
the base pencil `H ~ diag(12, 24)` with couplings `-5` reads count
one at the site `[[-7, -5], [-5, 5]]`, the scaled coupling at
`[[-14, -10], [-10, 10]]` — the base and scaled certificates
decided, then the theorem route through `ray_count`. -/

example : countAtPair (pencilH 3 5 [4, 8] mF) (idMat 2) 20 1 1
    (spB ⟨1, 8⟩ ⟨1, 6⟩ ⟨6, 1⟩) := by decide +kernel

example : countAtPair (pencilH (2 * 3) (2 * 5) [4, 8] mF) (idMat 2)
    (2 * 20) (2 * 1) 1 (spB ⟨1, 15⟩ ⟨1, 11⟩ ⟨11, 1⟩) := by
  decide +kernel

example : countAtPair (pencilH (2 * 3) (2 * 5) [4, 8] mF) (idMat 2)
    (2 * 20) (2 * 1) 1 (spB ⟨1, 15⟩ ⟨1, 11⟩ ⟨11, 1⟩) :=
  ray_count 2 3 5 [4, 8] mF (idMat 2) 20 1 1
    (spB ⟨1, 8⟩ ⟨1, 6⟩ ⟨6, 1⟩) (spB ⟨1, 15⟩ ⟨1, 11⟩ ⟨11, 1⟩)
    (by decide +kernel) (by decide +kernel)

/-! The two refusals, each isolating one load-bearing binder of the
descent.  (a) The count certificate `h`: the false count two refuses
at the base fixture, the datum's one lower-side block.  (b) The
scaled split `h'`: a forged block datum fails the scaled site's
read, and the transported count refuses with it. -/

example : ¬ countAtPair (pencilH 3 5 [4, 8] mF) (idMat 2) 20 1 2
    (spB ⟨1, 8⟩ ⟨1, 6⟩ ⟨6, 1⟩) := by decide +kernel
example : ¬ countAtPair (pencilH (2 * 3) (2 * 5) [4, 8] mF) (idMat 2)
    (2 * 20) (2 * 1) 2 (spB ⟨1, 15⟩ ⟨1, 11⟩ ⟨11, 1⟩) := by
  decide +kernel

example : ¬ splitRead (siteDatum
    (matAdd (pencilH (2 * 3) (2 * 5) [4, 8] mF)
      (matScale (2 * 1) (idMat 2)))
    (matScale (2 * 20) (idMat 2)))
    (spB ⟨1, 15⟩ ⟨1, 11⟩ ⟨12, 1⟩) := by decide +kernel

example : ¬ countAtPair (pencilH (2 * 3) (2 * 5) [4, 8] mF) (idMat 2)
    (2 * 20) (2 * 1) 1 (spB ⟨1, 15⟩ ⟨1, 11⟩ ⟨12, 1⟩) := by
  decide +kernel

/-! The base's ray reading (`prop:segment`'s weight data up to
rescaling): two interior pairs one ray exactly at the
cross-multiplied identity, the ends their own classes, the
cross-class and off-ray reads refused. -/

example : rayEq (.mid 2 5) (.mid 4 10) := by decide +kernel
example : ¬ rayEq (.mid 2 5) (.mid 4 11) := by decide +kernel
example : rayEq .free .free := by decide +kernel
example : rayEq .contact .contact := by decide +kernel
example : ¬ rayEq .free .contact := by decide +kernel
example : ¬ rayEq .free (.mid 2 5) := by decide +kernel
example : ¬ rayEq (.mid 2 5) .free := by decide +kernel
example : ¬ rayEq (.mid 2 5) .contact := by decide +kernel
example : ¬ rayEq .contact .free := by decide +kernel
example : ¬ rayEq .contact (.mid 2 5) := by decide +kernel
