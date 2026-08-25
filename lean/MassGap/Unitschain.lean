import MassGap.Segment
/-!
`thm:unitschain` — the scaling form: the pencil is degree-one
homogeneous in the end weights (`segment.pencil_scale`), and a
rescaling multiplies every spectral read of the family by the one
factor — the count at the pencil (`segment.ray_count`;
`certconstruct.countAtPair_scale`) and the cut at 𝒦's own carrier
(`K.cutRead_scale` with `K.cutRead_unscale`, the descent both
ways) — so the two ends' reads descend jointly to the ray and the
invariant is their pair (`def:K`), a count against a count with
each read one value at every form point (`prop:form`).  The first
consequence is the coordinates' stated data: the contact pair's
reads take the base and the residue alone (`contactpair.pair`;
`def:channelreads`; `def:excess`), the direction count entering
nowhere.  The module's own tier is the second consequence: the
scheme bridge acts on the base by `[α : β] ↦ [α : λβ]`
(`bridgeMap`, descending to the rays at `bridgeMap_congr`), and
its fixed points at the ray reading are exactly the two ends
(`bridge_fixed`) — an end reads its own class, and an interior
pair's image ray is refused at the product's injectivity at every
factor beyond one, the bridge's own coefficient `2 d_f` among them
(`bridge.count`; `thm:twoaction`'s instance).
-/

namespace unitschain
open ground segment

/-- The scheme bridge's action on the base: the coupling
coordinate rescaled at the factor, the ends their own classes
(`thm:bridge`'s `b_f^equiv = 2 d_f b_X` the coefficient's
instance). -/
def bridgeMap (la : Pos) : Coupling → Coupling
  | .free => .free
  | .mid al be => .mid al (la * be)
  | .contact => .contact

/-- The action descends to the base's rays: two couplings at one
ray map to one ray, the interior read the rescaled
cross-multiplication. -/
theorem bridgeMap_congr (la : Pos) : ∀ c c' : Coupling,
    rayEq c c' → rayEq (bridgeMap la c) (bridgeMap la c')
  | .free, .free, h => h
  | .contact, .contact, h => h
  | .mid al be, .mid al' be', h => by
    show al * (la * be') = al' * (la * be)
    rw [ground.mul_left_comm al la be',
      ground.mul_left_comm al' la be,
      show al * be' = al' * be from h]

/-- The fixed points are exactly the two ends: at a factor beyond
one, an end reads its own ray and an interior pair moves, the
cross-multiplied identity refused at the product's injectivity. -/
theorem bridge_fixed (la : Pos) (hla : 1 < la) :
    ∀ c : Coupling,
      rayEq c (bridgeMap la c) ↔ (c = .free ∨ c = .contact)
  | .free => ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | .contact => ⟨fun _ => Or.inr rfl, fun _ => trivial⟩
  | .mid _ be =>
    ⟨fun h =>
      have h1 : la * be = Pos.one * be :=
        (ground.mul_left_cancel h).trans (ground.one_mul be).symm
      absurd (ground.mul_right_cancel h1).symm (ground.lt_ne hla),
     fun h => h.elim (fun h1 => Coupling.noConfusion h1)
       (fun h2 => Coupling.noConfusion h2)⟩

end unitschain
