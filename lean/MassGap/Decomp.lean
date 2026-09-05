import MassGap.Corner
/-!
`thm:decomp`'s corner clause: the corner outputs move with the
family's scale as the level does, the extent's ray the one pencil
at every scale.  `pencil_scale` reads the corner pencil at the
family scaled by `u` as the scaled pencil, the ray's cleared point
one matrix up to the scale (`lem:dualtrunc`'s seam pencil at the
family's multiple), and `count_scale` with `count_unscale` read the
count at the scaled family and the scaled level as the family's own
count at the level (`certconstruct.countAtPair_scale`,
`certconstruct.countAtPair_unscale`; `thm:unitschain`'s degree-one
homogeneity at the corner coordinate): the extent's ray sits at
every scale, and the floor's move with the scale is the count read
at the member line's level (`corner.line_count`).
-/

namespace decomp
open ground elim inertia certconstruct corner

/-- The corner pencil at the family scaled by `u` is the scaled
corner pencil: the scale passes through the two members' clearings
and the site datum's swap. -/
theorem pencil_scale (E M : Mat) (u en ed : Pos) :
    cornerPencil (matScale u E) (matScale u M) en ed
      = matScale u (cornerPencil E M en ed) := by
  show matAdd (matScale (en * en) (matScale u E))
      (matSwap (matScale (ed * ed) (matScale u M)))
    = matScale u (matAdd (matScale (en * en) E)
      (matSwap (matScale (ed * ed) M)))
  rw [matScale_matAdd, matScale_matSwap, matScale_matScale,
    matScale_matScale, matScale_matScale, matScale_matScale,
    ground.mul_comm u (en * en), ground.mul_comm u (ed * ed)]

/-- The count at the scaled family and the scaled level is the
family's count at the level. -/
theorem count_scale {o : Nat} (E M G : Mat) (u en ed x y : Pos)
    (n : Nat) (sp sp' : Split o)
    (h : countAtPair (cornerPencil E M en ed) G x y n sp)
    (h' : splitRead (siteDatum
      (matAdd (cornerPencil (matScale u E) (matScale u M) en ed)
        (matScale (u * y) G))
      (matScale (u * x) G)) sp') :
    countAtPair (cornerPencil (matScale u E) (matScale u M) en ed) G
      (u * x) (u * y) n sp' := by
  rw [pencil_scale] at h' ⊢
  exact countAtPair_scale u _ G x y n sp sp' h h'

/-- The family's count at the level is the scaled family's count at
the scaled level, the seam transport back. -/
theorem count_unscale {o : Nat} (E M G : Mat) (u en ed x y : Pos)
    (n : Nat) (sp sp' : Split o)
    (h : countAtPair (cornerPencil (matScale u E) (matScale u M) en ed) G
      (u * x) (u * y) n sp')
    (hs : splitRead (siteDatum
      (matAdd (cornerPencil E M en ed) (matScale y G)) (matScale x G)) sp) :
    countAtPair (cornerPencil E M en ed) G x y n sp := by
  rw [pencil_scale] at h
  exact countAtPair_unscale u _ G x y n sp sp' h hs

end decomp
