import MassGap.Pairpencil
import MassGap.Certconstruct
/-!
`prop:segment` — the base as the closed segment of end-weight pairs
`[α : β]`, with the pencil's degree-one homogeneity.  The base's
three classes are the three matrix forms (`Coupling` with `siteAt`):
the free end the electric member's one-member weighting
(`pairpencil.pencilE`, the window diagonal alone), an interior
coupling the pair `(α E : β M)`'s site datum at both weights present
by the type's shape (`pairpencil.pencilH`), and the contact end the
magnetic member's balance partner (`elim.matSwap`).  The homogeneity
clause is `pencil_scale`: rescaling both weights by a ground datum
`u` rescales the pencil by `u`, entry by entry — the join's shape is
degree one in each weight (`pencil.rayH_scale` at the window's
form).  The spectral descent along a ray is `ray_count`, riding
`certconstruct.countAtPair_scale`: a count certificate at a balance
level `⟨x : y⟩` carries onto the `u`-rescaled coupling at the
level's `u`-rescaled members, the reversal count blind to the
positive factor (`lem:inertia`).  Interiority is the carrier's shape:
a `mid` coupling holds both weights as positive carrier data, an end
weight at the sum's unit unrepresentable, the frame by construction.
-/

namespace segment
open ground elim inertia pairpencil certconstruct

set_option genInjectivity false in
/-- A coupling of `prop:segment`'s base: the free end, an interior
end-weight pair `[α : β]` with both weights present by the shape of
its data, and the contact end — the closed segment's three
classes. -/
inductive Coupling where
  | free
  | mid (al be : Pos)
  | contact

/-- The coupling's site matrix over a window diagonal, gram and
magnetic matrix: the free end the electric member's one-member
weighting (`H = E`, the form against the gram), an interior pair the pencil's site datum at its two
weights, and the contact end the magnetic member's balance
partner. -/
def siteAt (diag : List Nat) (G M : elim.Mat) : Coupling → elim.Mat
  | .free => pairpencil.formE diag G
  | .mid al be => pairpencil.pencilH al be diag G M
  | .contact => elim.matSwap M

/-- Two couplings at one base point: the ends their own classes and
two interior pairs one ray exactly at the cross-multiplied identity
(`prop:segment`'s weight data up to rescaling, the identity
`def:ground`'s one-value read of two pairs). -/
def rayEq : Coupling → Coupling → Prop
  | .free, .free => True
  | .contact, .contact => True
  | .mid al be, .mid al' be' =>
    (Pair.mk al be).oneValue (Pair.mk al' be')
  | .free, .mid _ _ => False
  | .free, .contact => False
  | .mid _ _, .free => False
  | .mid _ _, .contact => False
  | .contact, .free => False
  | .contact, .mid _ _ => False

instance instSegment1 : (c c' : Coupling) → Decidable (rayEq c c')
  | .free, .free => inferInstanceAs (Decidable True)
  | .contact, .contact => inferInstanceAs (Decidable True)
  | .mid _ _, .mid _ _ =>
    inferInstanceAs (Decidable (Pair.oneValue _ _))
  | .free, .mid _ _ => inferInstanceAs (Decidable False)
  | .free, .contact => inferInstanceAs (Decidable False)
  | .mid _ _, .free => inferInstanceAs (Decidable False)
  | .mid _ _, .contact => inferInstanceAs (Decidable False)
  | .contact, .free => inferInstanceAs (Decidable False)
  | .contact, .mid _ _ => inferInstanceAs (Decidable False)

/-- The pencil's degree-one homogeneity (`prop:segment`): the site
datum at both weights' `u`-multiples is the unscaled site datum
rescaled by `u`, entry by entry — the join's shape is degree one in
each weight.  No hypotheses: the weights' positivity is the carrier's
type, the frame by construction. -/
theorem pencil_scale (u al be : Pos) (diag : List Nat) (G M : elim.Mat) :
    pairpencil.pencilH (u * al) (u * be) diag G M
      = inertia.matScale u (pairpencil.pencilH al be diag G M) :=
  pencil.rayH_scale (pairpencil.formE diag G) M u al be

/-- The spectral descent along a ray (`prop:segment`): a count
certificate at a balance level `⟨x : y⟩` over the pencil carries
onto the coupling at both weights' `u`-multiples at the level's
`u`-rescaled members — the rescaled pencil is the pencil's rescaling
(`pencil_scale`) and the reversal count is blind to the positive
factor (`certconstruct.countAtPair_scale`, `lem:inertia`).  Both
binders are load-bearing, the same classes as
`certconstruct.countAtPair_scale`'s own: `h` refuses at a false
count `n` at the fixture, and `h'` refuses at a forged split failing
`splitRead` — the committed refusals in the check module. -/
theorem ray_count {o : Nat} (u al be : Pos) (diag : List Nat)
    (M G : elim.Mat) (x y : Pos) (n : Nat)
    (sp sp' : inertia.Split o)
    (h : certconstruct.countAtPair
      (pairpencil.pencilH al be diag G M) G x y n sp)
    (h' : inertia.splitRead (inertia.siteDatum
        (elim.matAdd (pairpencil.pencilH (u * al) (u * be) diag G M)
          (inertia.matScale (u * y) G))
        (inertia.matScale (u * x) G)) sp') :
    certconstruct.countAtPair
      (pairpencil.pencilH (u * al) (u * be) diag G M)
      G (u * x) (u * y) n sp' := by
  rw [pencil_scale] at h' ⊢
  exact certconstruct.countAtPair_scale u _ G x y n sp sp' h h'

end segment
