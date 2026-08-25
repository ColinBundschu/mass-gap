import MassGap.Truncation
/-!
`lem:dualtrunc` — the dual coupling's reads at the roles exchanged,
and the count pinned on the finite head.

At the coupling `[σ : 1]` at a pair `σ` the cap, the floor and the
compression of `thm:truncation` read with one substitution, the two
terms' roles exchanged in the bound's inputs: the off-block coupling
and the removed block's magnetic part capped as forms by the fusion
data's `W` (`truncation.polar_psd` at the shift site's display, the
cofactor `ς c_W = W²`), the removed block's electric diagonal at or
above `σΛ_C` (`truncation.removed_psd` at the cross-added level tie),
and the compression's two count reads (`truncation.count_head_le`,
`truncation.count_full_le`).  The generals are role-neutral in their
two terms; the substitution is the reading.

`pin_count` is the pinned count at a bracket clear of the head's
divisor: the head's two counts at the bracket's ends are one integer
(`lem:cellcount`'s divisor-clearance read at the level as the
parameter), so the two transports squeeze the dual pencil's own count
between them — the compression side at the fiber datum's site tie
from below, the monotone side at the vacant coupling's block diagonal
from above — and the fiber count is that integer.  The two ends enter
as `certconstruct.countAtPair` at the head's own pencil, the removed
block's count vacant at its own level pair.

`admRead` is the displayed admissibility comparison
`σΛ_C > λ + W + c_ϑ` at a clearance pair `ϑ = [vn : vd]` with
`ϑ c_ϑ = W²`, the level's two members cross-added onto the
comparison's sides and the whole cleared to the naturals.  The
admissible set is an output whose floor rises toward the contact
end.

The transfer is one-sided: the compression lowers counts and raises
levels, each level's downward shift capped at `c_W`
(`thm:truncation`; `lem:inertia`), so between two head jumps the
lower comparison reads at its equality and the clearance rides the
upper jump alone — the admissible levels are those beyond the ground
bracket's top whose sum with `c_W` sits below the second jump's
bottom.  The count beyond every cutoff is `pin_count` at any two
admissible cutoffs: the smaller head is the larger head's own
truncation, the display running on the larger head at the one cap `W`
(a compression of a cap is a cap, `inertia.capAt_compress`) with the
removed block's floor at least `ς`, and the clear bracket pins the
count both times, the two pinned counts one integer.

The seam identity rides `certconstruct.countAtPair_scale` and
`certconstruct.countAtPair_unscale`: at the ray's positive factor the
pencil and both of the level's members rescale together and the count
is unchanged, the reversal blind to the factor (`lem:inertia`), so a
stored level names its representative and a seam comparison is two
reads of the one integer pencil at matched levels.
-/

namespace dualtrunc
open ground elim inertia certconstruct truncation

/-- The displayed admissibility comparison `σΛ_C > λ + W + c_ϑ` at
the clearance pair `ϑ = [vn : vd]` with `ϑ c_ϑ = W²`, the level
`λ = ⟨x : y⟩`'s two members cross-added onto the comparison's sides
and the whole cleared to the naturals — the admissible set's
membership read, its floor rising toward the contact end at the
consumers' own data. -/
def admRead (s LamC x y W vn vd : Pos) : Prop :=
  vn * (x + W) + W * W * vd < vn * (s * LamC) + vn * y

instance (s LamC x y W vn vd : Pos) :
    Decidable (admRead s LamC x y W vn vd) :=
  inferInstanceAs (Decidable (_ < _))

/-- The clear bracket pins the count on the head: the head's counts
at the bracket's two ends are one integer (`lem:cellcount`'s
divisor-clearance read at the level as the parameter), the
compression side transporting that integer up to the dual pencil's
own count and the monotone side transporting it back down, so the
squeeze reads the fiber count as the head's.  This is the count
beyond every cutoff — at two admissible cutoffs the smaller head is
the larger head's own truncation at the compressed cap
(`inertia.capAt_compress`), and the two pinned counts are one
integer. -/
theorem pin_count {k m : Nat} (H G P G1 B Q G2 : Mat)
    (x y hx hy rx ry : Pos) (n nf : Nat)
    (spH1 spH2 : Split k) (spR : Split m)
    (spF spD spd : Split (k + m))
    (hB : B.length = k)
    (hlow : countAtPair P G1 x y n spH1)
    (hhigh : countAtPair P G1 hx hy n spH2)
    (htie : matOneValue
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd P (matScale y G1)) (matScale x G1)) B
        (siteDatum (matAdd Q (matScale y G2)) (matScale x G2))))
    (hr : countAtPair Q G2 rx ry 0 spR)
    (hD : splitRead (blockJoin
      (siteDatum (matAdd P (matScale hy G1)) (matScale hx G1))
      (elim.nullMat k m)
      (siteDatum (matAdd Q (matScale ry G2)) (matScale rx G2))) spD)
    (hd : splitRead (siteDatum
      (siteDatum (matAdd H (matScale y G)) (matScale x G))
      (blockJoin
        (siteDatum (matAdd P (matScale hy G1)) (matScale hx G1))
        (elim.nullMat k m)
        (siteDatum (matAdd Q (matScale ry G2)) (matScale rx G2)))) spd)
    (hpsd : psdAt spd)
    (hf : countAtPair H G x y nf spF) :
    nf = n :=
  Nat.le_antisymm
    (truncation.count_full_le H G P G1 Q G2 x y hx hy rx ry nf n
      spF spH2 spR spD spd hf hhigh hr hD hd hpsd)
    (truncation.count_head_le H G P G1 B Q G2 x y n nf spH1 spF
      hB htie hlow hf)

end dualtrunc
