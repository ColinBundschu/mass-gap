import MassGap.Qla
/-!
The check module for `def:qla`: the filtration membership at the
window pair — the reads decided at a small index with the self-window
and directedness theorem routes, the width tie's refusal and the two
order binders' refusals — and the winding exclusion at the support
count: the torus chain's winding configuration crossing every cut
with the exclusion's theorem route at a small support, the support
binder's refusal at the winding string itself, and the occupancy
conjunct's isolation at the vacant configuration.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open ground fusion adjchar qla

/-! The membership fixtures: two configurations over a three-column
chain region's width, one occupied pair. -/

private def chain3 : lattice.Region := fiberdec.chainRegion 3
private def gChain : Nat → Nat := fun v => v / 2

private def cfgA : List places.Shape :=
  [theta 2, [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 0],
   [0, 0]]
private def cfgB : List places.Shape :=
  [[0, 0], [0, 0], [0, 0], theta 2, [0, 0], [0, 0], [0, 0], [0, 0],
   [0, 0]]

example : memberAt (dataA 2) 9 8 [cfgA, cfgB] := by decide +kernel
example : memberAt (dataA 2) 9 8 [cfgA, cfgB] :=
  member_self (dataA 2) chain3 [cfgA, cfgB] (by decide +kernel)
example : memberAt (dataA 2) 12 11 [cfgA, cfgB] :=
  member_of_le (dataA 2) (by decide +kernel) (by decide +kernel)
    [cfgA, cfgB] (member_self (dataA 2) chain3 [cfgA, cfgB]
      (by decide +kernel))

/-! The membership refusals: the width tie at a too-long
configuration, the bound below a support key, and the cutoff below
the content. -/

example : ¬ ((([cfgA ++ [theta 2]] : List (List places.Shape)).all
    (fun a => a.length == chain3.links)) = true) := by decide +kernel
example : ¬ memberAt (dataA 2) 3 8 [cfgB] := by decide +kernel
example : ¬ memberAt (dataA 2) 9 7 [cfgA] := by decide +kernel

/-! The winding side: the torus chain's rail string crosses every
cut, the support count seven at the count three. -/

private def wcfg : List places.Shape :=
  [[0, 0], [0, 0], [0, 0], theta 2, theta 2, theta 2, [0, 0],
   [0, 0], [0, 0]]
private def lcfg : List places.Shape :=
  List.replicate 7 (theta 2)

example : windSupp (dataA 2) chain3 gChain 3 wcfg := by decide +kernel
example : (carrier.support (dataA 2) chain3 wcfg).length = 3 := by
  decide +kernel
example : (carrier.support (dataA 2) chain3 lcfg).length = 7 := by
  decide +kernel

/-! The exclusion: a two-link support cannot cross three cuts —
decided, and through `noWind` at the stated count. -/

private def small : List places.Shape :=
  [theta 2, [0, 0], [0, 0], theta 2, [0, 0], [0, 0], [0, 0],
   [0, 0], [0, 0]]

example : (carrier.support (dataA 2) chain3 small).length = 2 := by
  decide +kernel
example : ¬ windSupp (dataA 2) chain3 gChain 3 small := by
  decide +kernel
example : ¬ windSupp (dataA 2) chain3 gChain 3 small :=
  noWind (dataA 2) chain3 gChain 3 small (by decide +kernel)

/-! The support binder's refusal: the winding string satisfies every
further read with the conclusion false — the support seven at the
count three, the finite-support premise the exclusion's one
carrier. -/

example : ¬ ((carrier.support (dataA 2) chain3 lcfg).length < 3) := by
  decide +kernel
example : windSupp (dataA 2) chain3 gChain 3 lcfg := by decide +kernel

/-! The occupancy conjunct's isolation: the vacant configuration
crosses nothing, so the winding read refuses at every cut. -/

example : ¬ windSupp (dataA 2) chain3 gChain 3
    (List.replicate 9 ([0, 0] : places.Shape)) := by decide +kernel
