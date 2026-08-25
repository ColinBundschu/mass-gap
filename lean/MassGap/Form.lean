import MassGap.Repring
import MassGap.Adjchar
/-!
`prop:form` — theta's self-duality and the form line.  The
form-line sentence's reads land here: the adjoint label is
self-dual at the complement arithmetic — the reduction and the
occupancy reversal both fix the adjoint shape (`reduce_theta`,
`dualL_theta`) — and the form line's dimension is the unit-label
count through `repring.unitRead_all`, `N^𝟏_{θθ} = 1` (`lineRead`).
The proposition's further sentences — the form point's rescaling,
the one-value pair read, and the against-`C2(adj)` denotation —
execute at `def:ground`'s homogeneity clause and the tree's
form-free representation: every energy read is already the
weight-free pair (`def:c2hat`'s pair display the named site), so
no form parameter exists to rescale.
-/

namespace form

/-- The adjoint shape at the fundamental pair, split at the trailing
vacancy: the doubled column over the vacant key. -/
private theorem theta_two : adjchar.theta 2 = [2] ++ [0] := rfl

/-- The adjoint shape past the pair, split at the trailing vacancy:
the raised head over the vacant middle with the deep column's unit,
the last key vacant. -/
private theorem theta_snoc (g : Nat) :
    adjchar.theta (g + 3)
      = (1 :: (List.replicate g 0 ++ [1])) ++ [0] := by
  have hlt : g + 1 < g + 3 := Nat.le_succ (g + 2)
  show ground.bumpAt 0
      (ground.bumpAt (g + 1) (List.replicate (g + 3) 0))
    = (1 :: (List.replicate g 0 ++ [1])) ++ [0]
  rw [← ground.unitAt_bumpRep (g + 3) (g + 1) hlt,
    ground.unitAt_replicate (g + 3) (g + 1) hlt,
    show g + 3 - (g + 1) - 1 = 1 from
      congrArg (fun n => n - 1) (ground.addSubSelfL (g + 1) 2)]
  show 1 :: (List.replicate g 0 ++ [1, 0])
    = 1 :: ((List.replicate g 0 ++ [1]) ++ [0])
  rw [ground.append_assoc (List.replicate g 0) [1] [0]]
  rfl

/-- The adjoint label is self-dual, the reduction's half: the
reduced shape's last key is already vacant, so the reduction fixes
it, the complement arithmetic's read.  The width bound `hd` is
LOAD-BEARING at the one refusing width: at `d = 1` the adjoint
shape is the doubled single column `[2]` and the reduction reads
`[0]` — the committed refusal — while the vacant width's shape is
vacuous and reads true. -/
theorem reduce_theta (d : Nat) (hd : 2 ≤ d) :
    labels.reduce (adjchar.theta d) = adjchar.theta d := by
  match Nat.le.dest hd with
  | ⟨e, he⟩ =>
    have hde : d = e + 2 := by rw [← he, Nat.add_comm]
    subst hde
    match e with
    | 0 =>
      show labels.reduce (adjchar.theta 2) = adjchar.theta 2
      rw [theta_two, labels.reduce_snoc [2] 0]
    | g + 1 =>
      show labels.reduce (adjchar.theta (g + 3)) = adjchar.theta (g + 3)
      rw [theta_snoc g,
        labels.reduce_snoc (1 :: (List.replicate g 0 ++ [1])) 0]

/-- The adjoint label is self-dual, the reversal's half: the front
`(1, 0^g, 1)` is its own reversal off the vacant last key, the
complement arithmetic's read.  The width bound `hd` is
LOAD-BEARING at the one refusing width: at `d = 1` the adjoint
shape is the doubled single column `[2]` and the occupancy
reversal reads `[0]` — the committed refusal — while the vacant
width's shape is vacuous and reads true. -/
theorem dualL_theta (d : Nat) (hd : 2 ≤ d) :
    labels.dualL (adjchar.theta d) = adjchar.theta d := by
  match Nat.le.dest hd with
  | ⟨e, he⟩ =>
    have hde : d = e + 2 := by rw [← he, Nat.add_comm]
    subst hde
    match e with
    | 0 =>
      show labels.dualL (adjchar.theta 2) = adjchar.theta 2
      rw [theta_two, labels.dualL_snoc [2] 0]
      rfl
    | g + 1 =>
      show labels.dualL (adjchar.theta (g + 3)) = adjchar.theta (g + 3)
      rw [theta_snoc g,
        labels.dualL_snoc (1 :: (List.replicate g 0 ++ [1])) 0,
        ground.reverse_cons 1 (List.replicate g 0 ++ [1]),
        ground.reverse_append (List.replicate g 0) [1],
        ground.reverse_replicate g 0]
      rfl

/-- The form line's dimension is the unit-label count in the
adjoint square, `N^𝟏_{θθ} = 1`: `repring.unitRead_all` at the
self-dual adjoint, the delta occupied at the fixed label — the
form-line sentence's own read.  The bound `hd` is FRAME — the
tex's object space, `con:places`' fundamental count at the
A-series domain (`d_f ≥ 2`), the proof's own consumption; the
statement decides true at every width (the below-domain shapes'
own reads), so no refusal exists. -/
theorem lineRead (d : Nat) (hd : 2 ≤ d) :
    labels.countL (adjchar.theta d) (adjchar.theta d) (labels.unitL d) = 1 := by
  have h : labels.countL (adjchar.theta d) (adjchar.theta d)
      (labels.unitL (adjchar.theta d).length)
      = (if labels.reduce (adjchar.theta d) = labels.dualL (adjchar.theta d)
          then 1 else 0) :=
    repring.unitRead_all (adjchar.theta d) (adjchar.theta d) rfl
  rw [adjchar.length_theta d] at h
  rw [h, if_pos ((reduce_theta d hd).trans (dualL_theta d hd).symm)]

end form
