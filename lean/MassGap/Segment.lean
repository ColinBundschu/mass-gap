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
`u` rescales the pencil by `u` at the one-value read, entry by entry
— the join's shape is degree one in each weight, so the site datum
acquires the one factor, the canonical representative moving only by
the homogeneity principle's gauge motion (`def:ground`).  The
spectral descent along a ray is `ray_count`, riding
`certconstruct.countAtPair_scale`: a count certificate at a balance
level `⟨x : y⟩` carries onto the `u`-rescaled coupling at the
level's `u`-rescaled members, the reversal count blind to the
positive factor (`lem:inertia`).  Interiority is the carrier's shape
— a `mid` coupling holds both weights as positive carrier data, an
end weight at the sum's unit unrepresentable — so no refusal exists
for it, the frame by construction.
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

instance : (c c' : Coupling) → Decidable (rayEq c c')
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

/-- A weight's ground factor splits off the sited product: the
one-member site at the `u`-multiple against a datum is the unscaled
sited product rescaled by `u`, the sited weighting's own composition
(`BPair.ofPos_scale` at the two weights). -/
private theorem scaleFactor (u w : Pos) (m : BPair) :
    (BPair.ofPos (u * w) * m).oneValue ((BPair.ofPos w * m).scale u) :=
  BPair.oneValue_trans (BPair.ofPos_scale (u * w) m)
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq
        (show m.scale (u * w) = (m.scale w).scale u by
          rw [BPair.scale_scale, ground.mul_comm w u]))
      (BPair.scale_congr u (BPair.oneValue_symm (BPair.ofPos_scale w m))))

/-- The pencil entry's homogeneity: the entry at both weights'
`u`-multiples reads one value with the unscaled entry rescaled by
`u` — the electric arm at the diagonal's factor, the off-diagonal's
unit fixed under the rescaling at the cross-added read, the magnetic
arm through the memberwise swap, and the canonical representative
crossed on both sides. -/
private theorem entryScale (u al be : Pos) (dv m : BPair) :
    ((BPair.ofPos (u * al) * dv
        + (BPair.ofPos (u * be) * m).swap).norm).oneValue
      (((BPair.ofPos al * dv
          + (BPair.ofPos be * m).swap).norm).scale u) := by
  refine BPair.oneValue_trans (BPair.norm_oneValue _)
    (BPair.oneValue_trans ?_
      (BPair.scale_congr u (BPair.oneValue_symm (BPair.norm_oneValue _))))
  rw [BPair.scale_add]
  refine BPair.add_congr ?_ ?_
  · exact scaleFactor u al dv
  · exact ground.swap_congr (scaleFactor u be m)

/-- The pencil row's homogeneity, `entryScale` folded along the
column range. -/
private theorem rowScale (u al be : Pos) (diag : List Nat)
    (G M : elim.Mat) (i : Nat) :
    poly.oneValue
      ((List.range diag.length).map (fun j =>
        (BPair.ofPos (u * al) * (BPair.ofNat (ground.getAt 0 diag i)
            * ground.getAt BPair.unit (ground.getAt [] G i) j)
          + (BPair.ofPos (u * be)
              * ground.getAt BPair.unit (ground.getAt [] M i) j).swap
         ).norm))
      (((List.range diag.length).map (fun j =>
        (BPair.ofPos al * (BPair.ofNat (ground.getAt 0 diag i)
            * ground.getAt BPair.unit (ground.getAt [] G i) j)
          + (BPair.ofPos be
              * ground.getAt BPair.unit (ground.getAt [] M i) j).swap
         ).norm)).map (fun x => x.scale u)) := by
  rw [ground.map_map]
  exact poly.oneValue_map _ _ (List.range diag.length)
    (fun j _ => entryScale u al be _ _)

/-- The pencil's degree-one homogeneity (`prop:segment`): the site
datum at both weights' `u`-multiples reads one value with the
unscaled site datum rescaled by `u`, entry by entry — the join's
shape is degree one in each weight, so the rescaling passes the
electric arm, the magnetic arm's memberwise swap, and the entry's
canonical representative.  No hypotheses: the weights' positivity is
the carrier's type, the frame by construction. -/
theorem pencil_scale (u al be : Pos) (diag : List Nat) (G M : elim.Mat) :
    elim.matOneValue (pairpencil.pencilH (u * al) (u * be) diag G M)
      (inertia.matScale u (pairpencil.pencilH al be diag G M)) := by
  unfold inertia.matScale pairpencil.pencilH ground.matOf
  rw [ground.map_map]
  exact elim.matOne_map _ _ (rowScale u al be diag G M)
    (List.range diag.length)

/-- The pencil's row count is the window diagonal's, the weights and
the magnetic matrix feeding the entries alone. -/
private theorem pencilH_len (al be : Pos) (diag : List Nat)
    (G M : elim.Mat) :
    (pairpencil.pencilH al be diag G M).length = diag.length :=
  ground.length_mapRange _ diag.length

/-- The pencil is square at the window diagonal's length: the row
and column ranges are the diagonal's own, independent of the
weights. -/
private theorem pencilH_sqAt (al be : Pos) (diag : List Nat)
    (G M : elim.Mat) :
    elim.sqAt (pairpencil.pencilH al be diag G M) diag.length :=
  elim.sqAt_of (pencilH_len al be diag G M)
    (elim.rowsLen_map _ diag.length (List.range diag.length)
      (fun _ _ => ground.length_mapRange _ diag.length))

/-- The spectral descent along a ray (`prop:segment`): a count
certificate at a balance level `⟨x : y⟩` over the pencil carries
onto the coupling at both weights' `u`-multiples at the level's
`u`-rescaled members — the rescaled pencil reads one value with the
pencil's rescaling (`pencil_scale`), the split transports across the
one-value read, and the reversal count is blind to the positive
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
  have ho : diag.length = o :=
    (pencilH_len al be diag G M).symm.trans (elim.sqAt_len h.1)
  have hsqPu : elim.sqAt
      (pairpencil.pencilH (u * al) (u * be) diag G M) o := by
    rw [← ho]
    exact pencilH_sqAt (u * al) (u * be) diag G M
  have hsqUH : elim.sqAt
      (inertia.matScale u (pairpencil.pencilH al be diag G M)) o :=
    inertia.sqAt_matScale o u _ h.1
  have hsqSy : elim.sqAt (inertia.matScale (u * y) G) o :=
    inertia.sqAt_matScale o (u * y) G h.2.1
  have hsqSx : elim.sqAt (inertia.matScale (u * x) G) o :=
    inertia.sqAt_matScale o (u * x) G h.2.1
  have htie : elim.matOneValue
      (inertia.siteDatum
        (elim.matAdd (pairpencil.pencilH (u * al) (u * be) diag G M)
          (inertia.matScale (u * y) G))
        (inertia.matScale (u * x) G))
      (inertia.siteDatum
        (elim.matAdd
          (inertia.matScale u (pairpencil.pencilH al be diag G M))
          (inertia.matScale (u * y) G))
        (inertia.matScale (u * x) G)) :=
    elim.matAdd_cong2 o _ _ _ _
      (elim.rowsLen_of_sqAt (elim.sqAt_matAdd o _ _ hsqPu hsqSy))
      (elim.rowsLen_of_sqAt (elim.sqAt_matSwap o _ hsqSx))
      (elim.rowsLen_of_sqAt (elim.sqAt_matAdd o _ _ hsqUH hsqSy))
      (elim.rowsLen_of_sqAt (elim.sqAt_matSwap o _ hsqSx))
      (elim.matAdd_cong2 o _ _ _ _
        (elim.rowsLen_of_sqAt hsqPu) (elim.rowsLen_of_sqAt hsqSy)
        (elim.rowsLen_of_sqAt hsqUH) (elim.rowsLen_of_sqAt hsqSy)
        (pencil_scale u al be diag G M)
        (elim.matOne_refl (inertia.matScale (u * y) G)))
      (elim.matOne_refl (elim.matSwap (inertia.matScale (u * x) G)))
  have h'2 : inertia.splitRead
      (inertia.siteDatum
        (elim.matAdd
          (inertia.matScale u (pairpencil.pencilH al be diag G M))
          (inertia.matScale (u * y) G))
        (inertia.matScale (u * x) G)) sp' :=
    inertia.splitRead_congr _ _
      (inertia.sqAt_siteDatum o _ _
        (elim.sqAt_matAdd o _ _ hsqUH hsqSy) hsqSx)
      htie sp' h'
  have hc := certconstruct.countAtPair_scale u
    (pairpencil.pencilH al be diag G M) G x y n sp sp' h h'2
  exact ⟨hsqPu, h.2.1, h', hc.2.2.2⟩

end segment
