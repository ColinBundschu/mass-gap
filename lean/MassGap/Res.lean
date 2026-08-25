import MassGap.Lap
/-!
`con:res` — the Feshbach resolvent at polynomial pairs, the four
steps as reads.  The deflated side is the join at one module
presentation, the withdrawn term the pairing's cofactor at the
negation's pair (`deflate1`, `deflate` the fold over the stated
presentations in list order), with `deflateRead` the m-pairing
certificate — every presentation's self-pairing occupied, its
pairing against the deflated side at equal members.  The support is
the state's key list closed under the insertions (`suppOf`,
`stepE` the round, `closeE` the rounds' fold at stated fuel) with
`closedE` the fixpoint read, and the read is order-free: the
closure's ordering is never load-bearing, the fixpoint holding at
any listing of the same keys.  The solve is the componentwise
identity at the closed support (`solveRead`, the coverage conjuncts
reading the whole mass — a key off the support would carry mass the
identity never reads), the site datum's matrix at the stated key
basis beside it (`siteMat`, the level withdrawn on the diagonal)
and `kernel.nullRead` the member's read.  The fourth step is the
solution's own deflation, `deflate` reused: module components in
solutions are the recorded historical bug class, and `resRead`'s
fourth conjunct is its structural closure.  The action and the
level enter as stated arguments — `con:twoplaq`'s display
`(E : 4d_f)` is the recorded instantiation.  The batteries read
at hand-derived instances with `lem:genericlift`(ii)'s pair-entried
adjugate the battery route, closed at the site datum itself
(`ppadjRead` of `siteMat`'s matrix, the check module's read), and
`ppSquare` the stated-order read at the matrix batteries — an
unshaped `ppadjRead`
reads vacuously at ragged input, the vacuity its own committed
battery beside the row-length refusal.
-/

namespace res
open ground poly places states genericlift

/-- Step 1's join at one module presentation: the deflation at the
pairing's cofactor, the withdrawn term at the negation's pair, the
coefficient at the certified reduction — `lem:genericlift`'s
`pReduce` at the seam, the moved representative scaling the
presentation, `pReduce_read` the value's bridge. -/
def deflate1 (F : states.FList) (m y : states.Comb) : states.Comb :=
  y ++ lap.scaleComb (genericlift.pReduce (poly.pMul lap.negP
    (genericlift.pCofactor (wg.pairFull F F m y)
      (wg.pairFull F F m m)))) m

/-- The deflated side: the fold over the module presentations in
list order, each join at the prior deflation. -/
def deflate (F : states.FList) (mods : List states.Comb)
    (y : states.Comb) : states.Comb :=
  mods.foldl (fun acc m => deflate1 F m acc) y

/-- Step 1's certificate: every presentation's self-pairing
occupied, and its pairing against the deflated side at equal
members. -/
def deflateRead (F : states.FList) (mods : List states.Comb)
    (y : states.Comb) : Prop :=
  (mods.all (fun m => !(decide (genericlift.crossNull
      (wg.pairFull F F m m) poly.pZero)))) = true
  ∧ (mods.all (fun m => decide (genericlift.crossNull
      (wg.pairFull F F m (deflate F mods y))
      poly.pZero))) = true

instance (F : states.FList) (mods : List states.Comb)
    (y : states.Comb) : Decidable (deflateRead F mods y) :=
  inferInstanceAs (Decidable (_ = _ ∧ _ = _))

/-- One closure round: the stated keys joined by the action
images' own, a member joined once. -/
def stepE (act : List Nat → states.Comb)
    (ws : List (List Nat)) : List (List Nat) :=
  ws.foldl (fun acc w => (act w).foldl (fun acc2 e =>
    if acc2.any (fun v => v == e.1) then acc2
    else acc2 ++ [e.1]) acc) ws

/-- The closure at stated fuel, the rounds' fold. -/
def closeE (act : List Nat → states.Comb) :
    Nat → List (List Nat) → List (List Nat)
  | 0, ws => ws
  | fuel + 1, ws => closeE act fuel (stepE act ws)

/-- Step 2's read: the insertions map the stated support into
itself. -/
def closedE (act : List Nat → states.Comb)
    (ws : List (List Nat)) : Prop :=
  (ws.all (fun w => (act w).all (fun e =>
    ws.any (fun v => v == e.1)))) = true

instance (act : List Nat → states.Comb) (ws : List (List Nat)) :
    Decidable (closedE act ws) :=
  inferInstanceAs (Decidable (_ = _))

/-- A state's keys inside a stated list, the coverage read. -/
def covers (ws : List (List Nat)) (c : states.Comb) : Prop :=
  (c.all (fun e => ws.any (fun v => v == e.1))) = true

instance (ws : List (List Nat)) (c : states.Comb) :
    Decidable (covers ws c) :=
  inferInstanceAs (Decidable (_ = _))

/-- The site datum's matrix at a level over a stated key basis:
the action's coefficient at the basis pair, the level withdrawn on
the diagonal. -/
def siteMat (act : List Nat → states.Comb)
    (lvl : poly.PPair) (ws : List (List Nat)) :
    genericlift.PPMat :=
  ground.matOf ws.length ws.length (fun i j =>
    let c := states.coeffAtW (act (ground.getAt [] ws j))
      (ground.getAt [] ws i)
    if i == j then poly.pAdd c
      (poly.pMul lap.negP lvl) else c)

/-- Step 3's identity at stated data: the action's read of the
solution against the level, joined by the kernel member, reads the
deflated side at every support key — the support closed with every
stated state covered, so the identity reads the whole mass. -/
def solveRead (act : List Nat → states.Comb)
    (lvl : poly.PPair) (ws : List (List Nat))
    (x k y' : states.Comb) : Prop :=
  closedE act ws
  ∧ covers ws x ∧ covers ws k ∧ covers ws y'
  ∧ (ws.all (fun w => decide (genericlift.crossNull
      (poly.pAdd
        (states.coeffAtW (states.extComb act x) w)
        (poly.pAdd
          (poly.pMul lap.negP
            (poly.pMul lvl (states.coeffAtW x w)))
          (states.coeffAtW k w)))
      (states.coeffAtW y' w)))) = true

instance (act : List Nat → states.Comb) (lvl : poly.PPair)
    (ws : List (List Nat)) (x k y' : states.Comb) :
    Decidable (solveRead act lvl ws x k y') :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ = _))

/-- The resolvent's certificate, whole: the deflation's reads, the
kernel member's, the solve identity at the closed support, and
step 4's join — the solution's own deflation reads. -/
def resRead (F : states.FList) (act : List Nat → states.Comb)
    (lvl : poly.PPair) (mods : List states.Comb)
    (ws : List (List Nat)) (y x k : states.Comb) : Prop :=
  deflateRead F mods y
  ∧ kernel.nullRead F k
  ∧ solveRead act lvl ws x k (deflate F mods y)
  ∧ deflateRead F mods x

instance (F : states.FList) (act : List Nat → states.Comb)
    (lvl : poly.PPair) (mods : List states.Comb)
    (ws : List (List Nat)) (y x k : states.Comb) :
    Decidable (resRead F act lvl mods ws y x k) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end res
