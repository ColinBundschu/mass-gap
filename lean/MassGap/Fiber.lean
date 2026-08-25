import MassGap.Wg
/-!
`con:fiber` — the two-plaquette fiber.  The theta-graph's invariant
fiber is the span of the permutation-presentation states in the two
plaquette variables (`con:states`' `Comb` at the two-letter factor
lists), and its pairing is `prop:algebra`'s identity through the
presentation Gram, the fiber's own read (`pairP` at `prop:wg`'s
`pairFull`); the graph's operator data are `con:twoplaq`'s displays,
the recorded consumer.
-/

namespace fiber

/-- The fiber's pairing, `prop:algebra`'s identity through the
presentation Gram. -/
def pairP (Fa Fb : states.FList) (a b : states.Comb) :
    poly.PPair :=
  wg.pairFull Fa Fb a b

end fiber
