import MassGap.Unitschain
/-!
The check module for `thm:unitschain`: the bridge map's displays at
the three classes, the fixed-point characterization decided and
routed at the ends and at a moved interior pair, the descent to
the rays at the congruence, and the refusal
isolating the factor's bound — at the unit factor an interior pair
is fixed and the characterization refuses, the bound's own
instance. -/

open ground segment unitschain

/-! The bridge map's displays. -/

example : bridgeMap 3 (.mid 2 5) = .mid 2 15 := rfl
example : bridgeMap 3 .free = .free := rfl
example : bridgeMap 3 .contact = .contact := rfl

/-! The action descends to the rays: one ray's two representatives
map to one ray, decided and through the congruence. -/

example : rayEq (bridgeMap 3 (.mid 2 5)) (bridgeMap 3 (.mid 4 10)) := by
  decide +kernel
example : rayEq (bridgeMap 3 (.mid 2 5)) (bridgeMap 3 (.mid 4 10)) :=
  bridgeMap_congr 3 (.mid 2 5) (.mid 4 10) (by decide +kernel)

/-! The ends fixed, decided and through the characterization. -/

example : rayEq .free (bridgeMap 3 .free) := by decide +kernel
example : rayEq .contact (bridgeMap 3 .contact) := by decide +kernel
example : rayEq .free (bridgeMap 3 .free) :=
  (bridge_fixed 3 (by decide +kernel) .free).mpr (Or.inl rfl)
example : rayEq .contact (bridgeMap 3 .contact) :=
  (bridge_fixed 3 (by decide +kernel) .contact).mpr (Or.inr rfl)

/-! An interior pair moves, decided and through the
characterization. -/

example : ¬ rayEq (.mid 2 5) (bridgeMap 3 (.mid 2 5)) := by
  decide +kernel
example : ¬ rayEq (.mid 2 5) (bridgeMap 3 (.mid 2 5)) :=
  fun h => ((bridge_fixed 3 (by decide +kernel) (.mid 2 5)).mp h).elim
    (fun h1 => Coupling.noConfusion h1)
    (fun h2 => Coupling.noConfusion h2)

/-! The factor bound's refusal: at the unit factor the interior
pair is fixed and the characterization fails at it. -/

example : rayEq (.mid 2 5) (bridgeMap 1 (.mid 2 5)) := by
  decide +kernel
example : ¬ (rayEq (.mid 2 5) (bridgeMap 1 (.mid 2 5))
    ↔ ((Coupling.mid 2 5) = .free ∨ (Coupling.mid 2 5) = .contact)) :=
  fun hiff => ((hiff.mp (by decide +kernel)).elim
    (fun h1 => Coupling.noConfusion h1)
    (fun h2 => Coupling.noConfusion h2))
