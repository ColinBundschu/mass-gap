import MassGap.Mixedinv
/-!
The check module for `lem:mixedinv`: the batteries re-read the
block count's identity with the path count at the tableau
instances — the read decided against `def:blockcount`'s
kernel-dimension count and run through the general theorem.
-/
set_option maxHeartbeats 4000000

open ground places mixedinv

/-! The read against the definitional count. -/

example : mixedinv.read [2, 0] := by decide +kernel
example : mixedinv.read [1, 1] := by decide +kernel
example : mixedinv.read [1, 1, 0] := by decide +kernel
example : mixedinv.read [0, 0, 1] := by decide +kernel

/-! The general theorem's own route at the standing instances. -/

example : mixedinv.read [1, 1] := mixedinv.readAll [1, 1]
example : mixedinv.read [1, 1, 0] := mixedinv.readAll [1, 1, 0]
example : mixedinv.read [0, 0, 1] := mixedinv.readAll [0, 0, 1]

/-! The theorem carries no binder: the vacant shape and the vacant
content both stand, each decided at the kernel, and the vacant
shape runs through the theorem beside its decide. -/

example : mixedinv.read [] := by decide +kernel
example : mixedinv.read [0, 0, 0] := by decide +kernel
example : mixedinv.read [] := mixedinv.readAll []

/-! Both removal arms at one shape: `[1, 0, 1]`'s paths join at
three, the count decided against the definitional one and read
through the theorem. -/

example : mixedinv.read [1, 0, 1] := by decide +kernel
example : mixedinv.read [1, 0, 1] := mixedinv.readAll [1, 0, 1]

/-! The carrier tier's batteries: the permutation matrices at the
two-letter content, the moved read decided at the kernel and run
through the equivariance theorem at one instance, the independence
decided at two sizes and run through the theorem, and the width
binder's refusal — at `k > d` the flats are dependent. -/

/-! The permutation matrices at the two-letter content: the
identity assignment reads the diagonal, the swap the
antidiagonal. -/

example : mixedinv.permMat [0, 1] [1, 1]
    = [[ground.BPair.ofNat 1, ground.BPair.unit],
       [ground.BPair.unit, ground.BPair.ofNat 1]] := by decide +kernel

example : mixedinv.permMat [1, 0] [1, 1]
    = [[ground.BPair.unit, ground.BPair.ofNat 1],
       [ground.BPair.ofNat 1, ground.BPair.unit]] := by decide +kernel

/-! The moved read at one instance — the swap permutation on the
two-letter content against the `E_{01}` move at a concrete vector —
decided at the kernel and read through the theorem. -/

example : poly.oneValue
    (elim.matVec
      (units.matUnitAt (blockcount.moveAt 0 1 [1, 1]) [1, 1] 0 1)
      (elim.matVec (mixedinv.permMat [1, 0] [1, 1])
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]))
    (elim.matVec (mixedinv.permMat [1, 0] (blockcount.moveAt 0 1 [1, 1]))
      (elim.matVec
        (units.matUnitAt (blockcount.moveAt 0 1 [1, 1]) [1, 1] 0 1)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2])) := by decide +kernel

example : poly.oneValue
    (elim.matVec
      (units.matUnitAt (blockcount.moveAt 0 1 [1, 1]) [1, 1] 0 1)
      (elim.matVec (mixedinv.permMat [1, 0] [1, 1])
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]))
    (elim.matVec (mixedinv.permMat [1, 0] (blockcount.moveAt 0 1 [1, 1]))
      (elim.matVec
        (units.matUnitAt (blockcount.moveAt 0 1 [1, 1]) [1, 1] 0 1)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2])) :=
  mixedinv.permMat_moved 2 [1, 0] (by decide +kernel) 2 [1, 1] (by decide +kernel)
    0 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    [ground.BPair.ofNat 1, ground.BPair.ofNat 2] (by decide +kernel)

/-! The independence decided at two sizes and read through the
theorem. -/

example : elim.indepRows (mixedinv.mixWidth 2 2)
    (mixedinv.permFlats 2 2) := by decide +kernel

example : elim.indepRows (mixedinv.mixWidth 3 2)
    (mixedinv.permFlats 3 2) := by decide +kernel

example : elim.indepRows (mixedinv.mixWidth 2 2)
    (mixedinv.permFlats 2 2) := mixedinv.perm_indep 2 2 (by decide +kernel)

example : elim.indepRows (mixedinv.mixWidth 3 2)
    (mixedinv.permFlats 3 2) := mixedinv.perm_indep 3 2 (by decide +kernel)

/-! The width binder's refusal: beyond the letter count the six
degree-three flats over two letters are dependent — `k ≤ d` is
load-bearing. -/

example : ¬ elim.indepRows (mixedinv.mixWidth 2 3)
    (mixedinv.permFlats 2 3) := by decide +kernel

/-! The Gram tier's batteries: the four cycle-count pins decided
at the kernel and read through the theorem — the identity pair at
the letter-squared, the transposed pair at one cycle over two and
three letters, and the mixed three-letter pair at one cycle — with
the cycle fold's length pinned at a two-cycle instance and the
membership binder's refusal at a non-permutation. -/

example : (elim.dotP (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))
    (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))).oneValue
    (ground.BPair.ofNat
      (2 ^ (places.cyclesOf
        (places.expo [0, 1] (places.invPerm 2 [0, 1]))).length))
    := by decide +kernel

example : (elim.dotP (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))
    (mixedinv.flatF 2 2 (mixedinv.permMat [1, 0]))).oneValue
    (ground.BPair.ofNat
      (2 ^ (places.cyclesOf
        (places.expo [0, 1] (places.invPerm 2 [1, 0]))).length))
    := by decide +kernel

example : (elim.dotP (mixedinv.flatF 3 2 (mixedinv.permMat [0, 1]))
    (mixedinv.flatF 3 2 (mixedinv.permMat [1, 0]))).oneValue
    (ground.BPair.ofNat
      (3 ^ (places.cyclesOf
        (places.expo [0, 1] (places.invPerm 2 [1, 0]))).length))
    := by decide +kernel

example : (elim.dotP (mixedinv.flatF 3 3 (mixedinv.permMat [0, 2, 1]))
    (mixedinv.flatF 3 3 (mixedinv.permMat [1, 0, 2]))).oneValue
    (ground.BPair.ofNat
      (3 ^ (places.cyclesOf
        (places.expo [0, 2, 1] (places.invPerm 3 [1, 0, 2]))).length))
    := by decide +kernel

/-! The same four pins through the theorem. -/

example : (elim.dotP (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))
    (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))).oneValue
    (ground.BPair.ofNat
      (2 ^ (places.cyclesOf
        (places.expo [0, 1] (places.invPerm 2 [0, 1]))).length))
    := mixedinv.perm_gram 2 2 [0, 1] [0, 1] (by decide +kernel) (by decide +kernel)

example : (elim.dotP (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))
    (mixedinv.flatF 2 2 (mixedinv.permMat [1, 0]))).oneValue
    (ground.BPair.ofNat
      (2 ^ (places.cyclesOf
        (places.expo [0, 1] (places.invPerm 2 [1, 0]))).length))
    := mixedinv.perm_gram 2 2 [0, 1] [1, 0] (by decide +kernel) (by decide +kernel)

example : (elim.dotP (mixedinv.flatF 3 2 (mixedinv.permMat [0, 1]))
    (mixedinv.flatF 3 2 (mixedinv.permMat [1, 0]))).oneValue
    (ground.BPair.ofNat
      (3 ^ (places.cyclesOf
        (places.expo [0, 1] (places.invPerm 2 [1, 0]))).length))
    := mixedinv.perm_gram 3 2 [0, 1] [1, 0] (by decide +kernel) (by decide +kernel)

example : (elim.dotP (mixedinv.flatF 3 3 (mixedinv.permMat [0, 2, 1]))
    (mixedinv.flatF 3 3 (mixedinv.permMat [1, 0, 2]))).oneValue
    (ground.BPair.ofNat
      (3 ^ (places.cyclesOf
        (places.expo [0, 2, 1] (places.invPerm 3 [1, 0, 2]))).length))
    := mixedinv.perm_gram 3 3 [0, 2, 1] [1, 0, 2] (by decide +kernel) (by decide +kernel)

/-! The membership binder's refusal: at the repeated-letter
assignment beside a held member the Gram read fails — the pairing
is the permutations' own. -/

example : ¬ (elim.dotP (mixedinv.flatF 2 2 (mixedinv.permMat [0, 0]))
    (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))).oneValue
    (ground.BPair.ofNat
      (2 ^ (places.cyclesOf
        (places.expo [0, 0] (places.invPerm 2 [0, 1]))).length))
    := by decide +kernel

/-! The Gram's second membership binder: the mirrored refusal at
the repeated-letter assignment on the second slot. -/

example : ¬ (elim.dotP (mixedinv.flatF 2 2 (mixedinv.permMat [0, 1]))
    (mixedinv.flatF 2 2 (mixedinv.permMat [0, 0]))).oneValue
    (ground.BPair.ofNat
      (2 ^ (places.cyclesOf
        (places.expo [0, 1] (places.invPerm 2 [0, 0]))).length))
    := by decide +kernel

/-! The moved read's binder records: the membership's refusal at
the repeated-letter assignment, and the held binders — the letter
bounds and the distinctness `con:units`' index frame with the
content membership the enumeration's, each surviving its drop at
the kernel. -/

example : ¬ poly.oneValue
    (elim.matVec (units.matUnitAt (blockcount.moveAt 0 1 [1, 1]) [1, 1] 0 1)
      (elim.matVec (mixedinv.permMat [0, 0] [1, 1])
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]))
    (elim.matVec (mixedinv.permMat [0, 0] (blockcount.moveAt 0 1 [1, 1]))
      (elim.matVec (units.matUnitAt (blockcount.moveAt 0 1 [1, 1]) [1, 1] 0 1)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2])) := by decide +kernel

example : poly.oneValue
    (elim.matVec (units.matUnitAt (blockcount.moveAt 0 2 [1, 1]) [1, 1] 0 2)
      (elim.matVec (mixedinv.permMat [1, 0] [1, 1])
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]))
    (elim.matVec (mixedinv.permMat [1, 0] (blockcount.moveAt 0 2 [1, 1]))
      (elim.matVec (units.matUnitAt (blockcount.moveAt 0 2 [1, 1]) [1, 1] 0 2)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2])) := by decide +kernel

example : poly.oneValue
    (elim.matVec (units.matUnitAt (blockcount.moveAt 3 1 [1, 1]) [1, 1] 3 1)
      (elim.matVec (mixedinv.permMat [1, 0] [1, 1])
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]))
    (elim.matVec (mixedinv.permMat [1, 0] (blockcount.moveAt 3 1 [1, 1]))
      (elim.matVec (units.matUnitAt (blockcount.moveAt 3 1 [1, 1]) [1, 1] 3 1)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2])) := by decide +kernel

example : poly.oneValue
    (elim.matVec (units.matUnitAt (blockcount.moveAt 0 0 [1, 1]) [1, 1] 0 0)
      (elim.matVec (mixedinv.permMat [1, 0] [1, 1])
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2]))
    (elim.matVec (mixedinv.permMat [1, 0] (blockcount.moveAt 0 0 [1, 1]))
      (elim.matVec (units.matUnitAt (blockcount.moveAt 0 0 [1, 1]) [1, 1] 0 0)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2])) := by decide +kernel

example : poly.oneValue
    (elim.matVec (units.matUnitAt (blockcount.moveAt 0 1 [2, 1]) [2, 1] 0 1)
      (elim.matVec (mixedinv.permMat [1, 0] [2, 1])
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2, ground.BPair.ofNat 3]))
    (elim.matVec (mixedinv.permMat [1, 0] (blockcount.moveAt 0 1 [2, 1]))
      (elim.matVec (units.matUnitAt (blockcount.moveAt 0 1 [2, 1]) [2, 1] 0 1)
        [ground.BPair.ofNat 1, ground.BPair.ofNat 2, ground.BPair.ofNat 3]))
    := by decide +kernel

/-! The independence at three letters and three boxes, the six
flats at the `3! = 6` count, decided and through the theorem; the
kernel's reach here is the assignment fold over the flats' Gram, a
determinant at the flat count's order, so the decides sit at the
counts below four. -/

example : elim.indepRows (mixedinv.mixWidth 3 3)
    (mixedinv.permFlats 3 3) := by decide +kernel
example : elim.indepRows (mixedinv.mixWidth 3 3)
    (mixedinv.permFlats 3 3) := mixedinv.perm_indep 3 3 (by decide +kernel)

/-! The span theorem's batteries.  The identity family — one
identity matrix per content, `lem:dualread`(i)'s coevaluation
shape — is an invariant at hand-built frames and moved reads over
the public identity kit, and its span read runs decided and
through the theorem at two sizes.  The frames and moved reads
quantify over an infinite type, so the theorem routes carry them
as terms; the refusals isolate each load-bearing binder at a
decided conclusion. -/

example : elim.spanRel (mixedinv.mixWidth 2 2)
    (mixedinv.permFlats 2 2)
    (mixedinv.flatF 2 2
      (fun mu => elim.idList (places.monomialsAt mu).length)) := by
  decide +kernel

example : elim.spanRel (mixedinv.mixWidth 2 2)
    (mixedinv.permFlats 2 2)
    (mixedinv.flatF 2 2
      (fun mu => elim.idList (places.monomialsAt mu).length)) :=
  mixedinv.perm_span 2 2 (by decide +kernel) _
    (fun mu _ =>
      ⟨elim.rowsLen_idList (places.monomialsAt mu).length,
        elim.length_idList (places.monomialsAt mu).length⟩)
    (fun mu _ i j _ _ _ x hx =>
      poly.oneValue_trans
        (elim.matVec_congr
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j) _ _
          (elim.matVec_idList (places.monomialsAt mu).length x hx))
        (poly.oneValue_symm
          (elim.matVec_idList
            (places.monomialsAt (blockcount.moveAt i j mu)).length
            _
            (by rw [elim.matVec_length, units.length_matUnitAt]))))

example : elim.spanRel (mixedinv.mixWidth 3 2)
    (mixedinv.permFlats 3 2)
    (mixedinv.flatF 3 2
      (fun mu => elim.idList (places.monomialsAt mu).length)) :=
  mixedinv.perm_span 3 2 (by decide +kernel) _
    (fun mu _ =>
      ⟨elim.rowsLen_idList (places.monomialsAt mu).length,
        elim.length_idList (places.monomialsAt mu).length⟩)
    (fun mu _ i j _ _ _ x hx =>
      poly.oneValue_trans
        (elim.matVec_congr
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j) _ _
          (elim.matVec_idList (places.monomialsAt mu).length x hx))
        (poly.oneValue_symm
          (elim.matVec_idList
            (places.monomialsAt (blockcount.moveAt i j mu)).length
            _
            (by rw [elim.matVec_length, units.length_matUnitAt]))))

/-! A combination invariant's span read decided at the kernel: the
identity and swap families' entrywise sum sits in the permutation
span at the two-letter power. -/

example : elim.spanRel (mixedinv.mixWidth 2 2)
    (mixedinv.permFlats 2 2)
    (mixedinv.flatF 2 2
      (fun mu => elim.matAdd (mixedinv.permMat [0, 1] mu)
        (mixedinv.permMat [1, 0] mu))) := by decide +kernel

/-! The frames' two conjuncts, each at its own refusal at the one
content of `(1, 1)`, where the moved reads are vacant at the one
letter: a wide row breaks the row-width read with the matrix's
length held, and a second row breaks the length read with the row
widths held — either way the flat form sits off the width and the
conclusion refuses. -/

example : ¬ elim.spanRel (mixedinv.mixWidth 1 1)
    (mixedinv.permFlats 1 1)
    (mixedinv.flatF 1 1
      (fun _ => [[ground.BPair.ofNat 1, ground.BPair.ofNat 1]]))
    := by decide +kernel

example : ¬ elim.spanRel (mixedinv.mixWidth 1 1)
    (mixedinv.permFlats 1 1)
    (mixedinv.flatF 1 1
      (fun _ => [[ground.BPair.ofNat 1], [ground.BPair.ofNat 1]]))
    := by decide +kernel

/-! The moved reads' refusal: a framed family reading two scalars
at the two contents of `(2, 1)` is off the equivariance — the one
permutation flat cannot reach it, the conclusion refused with the
frames held. -/

example : ¬ elim.spanRel (mixedinv.mixWidth 2 1)
    (mixedinv.permFlats 2 1)
    (mixedinv.flatF 2 1
      (fun mu => if mu = [1, 0] then [[ground.BPair.ofNat 2]]
        else [[ground.BPair.ofNat 1]])) := by decide +kernel

/-! The width binder `k ≤ d` is the tex's own frame
(`lem:mixedinv` states the lemma at `k ≤ d_f`): at `(1, 2)` the
identity family's span read still holds — the permutations span
beyond the letter count while their independence fails — so the
binder holds no refusal at this instance, the theorem's route the
frame's own. -/

example : elim.spanRel (mixedinv.mixWidth 1 2)
    (mixedinv.permFlats 1 2)
    (mixedinv.flatF 1 2
      (fun mu => elim.idList (places.monomialsAt mu).length)) := by
  decide +kernel
