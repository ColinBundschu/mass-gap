import MassGap.Carrier
import MassGap.Channels
import MassGap.Twoplaq
/-!
`thm:network` — the network reduction and the two-vertex coupling
law.  (i) The theta graph enters as the committed region `thetaR`,
two square plaquettes sharing one link, and the reduction is the
convolution identity at the carrier's own reads: an occupied
configuration reads its two three-link paths at one label each,
the two-valent vertices' invariant counts the unit law's own
Kronecker reads (`carrier.invCount_pair_pos`), so the occupied
index is the `Θ(R₁, k, R₂)`-network data — the spread `netConf`
with the two three-valent vertices' multiplicities the incident
triples' invariant counts — and `E` is diagonal there at the
eigenvalue `3 C₂(R₁) + C₂(k) + 3 C₂(R₂)`, the content fold's
collected read.  (ii) The module–pair weights are
`w_k = [m_k d_k : d_θ²]` over the adjoint square's row, the
completeness `Σ_k m_k d_k = d_θ²` the interface's dimension
identity (`fusion.dimLaw`; `channels.dimClosureAll` the
`A`-calculus's general read), the displayed six-weight list the
channel table's reads at the committed polynomial pairs `wList`
with their evaluation ties at every width from each row's own
floor (`wUnit_read` through `wOmega_read`), and the leading-term
reads the committed data's own degree and top comparisons.  (iii) The
slot-two self-energy is the fold `selfEnergy` of the weights
against the resolvent factors `[q_k : 2q_k + p_k]` at
`ĉ₂(k) = [p_k : q_k]` (`resFactor`), the factor's gap the module
pair's network eigenvalue against the module count,
`3 + ĉ₂(k) + 3` against `E₀ = 4` at `ĉ₂(adj) = 1`, each factor a
constructed pair at an occupied second member with the vacant
data's arms at `none` (`prop:E0`; the eigenvalue clause (i)'s).
The recoupling constituent's content is the finite tetrahedral
list at the middle index the channel table's occupied Casimir
values — `nodes`, the trace form's reads tied to the table's
Casimir column at every width from each row's own floor
(`nodeUnit_read` through `nodeOmega_read`) with the dual pair's
shared value one joint block: the within-pair middle matrix
`kMid`, the bra and ket the interpolant-projected two-plaquette
states `chanState` — `E_link`'s Lagrange read, the cleared
interpolant `lagNum` at the clearing scale `lagScale` applied
along the shared-link Casimir's Horner fold `lagApply`
(`con:units`' Lagrange read at `prop:link`'s insertion, each
level collected at `states.collect`) — against the magnetic
multiplication at the first plaquette, the pairing `prop:wg`'s.
-/

namespace network
open ground fusion

/-! The module–pair weights (`thm:network`(ii)). -/

/-- The module–pair weight's numerator at a channel, `m_k d_k`:
the count against the dimension, the shared second member the
adjoint square's dimension `d_θ²`. -/
def weightN {L : Type} (F : Data L) (k : L) : Nat :=
  F.count F.theta F.theta k * F.dim k

/-- The unit channel's weight, `[1 : r²(r+2)²]`. -/
def wUnit : poly.Poly × poly.Poly :=
  ([BPair.ofPos .one],
   [BPair.unit, BPair.unit, ⟨5, 1⟩, ⟨5, 1⟩, ⟨2, 1⟩])

/-- The `θ` channel's weight at the generic base `c₁ = 2`,
`[c₁ : r(r+2)]`. -/
def wTheta : poly.Poly × poly.Poly :=
  ([⟨3, 1⟩], [BPair.unit, ⟨3, 1⟩, ⟨2, 1⟩])

/-- The `2θ` channel's weight, `[(r+1)²r(r+4) : 4r²(r+2)²]`. -/
def wTwoTheta : poly.Poly × poly.Poly :=
  ([BPair.unit, ⟨5, 1⟩, ⟨10, 1⟩, ⟨7, 1⟩, ⟨2, 1⟩],
   [BPair.unit, BPair.unit, ⟨17, 1⟩, ⟨17, 1⟩, ⟨5, 1⟩])

/-- The dual pair's weight, each member's,
`[(r-1)(r+3) : 4r(r+2)]` at the gap witness `g + 1 = r`. -/
def wDual : poly.Poly × poly.Poly :=
  ([⟨1, 4⟩, ⟨3, 1⟩, ⟨2, 1⟩], [BPair.unit, ⟨9, 1⟩, ⟨5, 1⟩])

/-- The `ω₂ + ω₂*` channel's weight,
`[(r+1)²(r+2)(r-2) : 4r²(r+2)²]` at the gap witness
`w' + 2 = r`. -/
def wOmega : poly.Poly × poly.Poly :=
  ([⟨1, 5⟩, ⟨1, 9⟩, ⟨1, 4⟩, ⟨3, 1⟩, ⟨2, 1⟩],
   [BPair.unit, BPair.unit, ⟨17, 1⟩, ⟨17, 1⟩, ⟨5, 1⟩])

/-- The displayed weight list, the channel table's reads as
committed polynomial pairs in the residue, one `(numerator,
denominator)` pair per channel in the table's row order with the
dual pair's member entered twice. -/
def wList : List (poly.Poly × poly.Poly) :=
  [wUnit, wTheta, wTwoTheta, wDual, wDual, wOmega]

/-! The displayed weights' ties at the channel table's dimension
column (`thm:network`(ii)): each weight's two members multiplied
across against `[m_k d_k : d_θ²]` at every width from its row's
own floor, with the leading-term reads at the committed data. -/

/-- The residue's own monic factor. -/
private def facArg : poly.Poly := [BPair.unit, BPair.ofNat 1]

/-- The raised monic factor at a count, `r + a`. -/
private def facUp (a : Nat) : poly.Poly := [BPair.ofNat a, BPair.ofNat 1]

/-- The lowered monic factor at a count, `r - a`, its constant the
count's swap. -/
private def facDn (a : Nat) : poly.Poly :=
  [(BPair.ofNat a).swap, BPair.ofNat 1]

/-- A two-coefficient list's Horner read at an argument. -/
private theorem eval_two (c0 c1 r : BPair) :
    (poly.eval [c0, c1] r).oneValue (c0 + r * c1) :=
  BPair.add_congr (BPair.oneValue_refl c0)
    (BPair.mul_congr (BPair.oneValue_refl r) (poly.eval_one c1 r))

/-- A monic linear factor's read is its constant shifted by the
argument. -/
private theorem eval_lin (c r : BPair) :
    (poly.eval [c, BPair.ofNat 1] r).oneValue (c + r) :=
  BPair.oneValue_trans (eval_two c (BPair.ofNat 1) r)
    (BPair.add_congr (BPair.oneValue_refl c) (BPair.mul_ofNat_one r))

/-- A constant list's count read. -/
private theorem eval_const (a : Nat) (r : BPair) :
    (poly.eval [BPair.ofNat a] r).oneValue (BPair.ofNat a) :=
  poly.eval_one (BPair.ofNat a) r

/-- A two-coefficient list's count read at a count argument, the
constant joined to the argument's scale. -/
private theorem eval_twoVal (a b n m : Nat) (hm : a + n * b = m) :
    (poly.eval [BPair.ofNat a, BPair.ofNat b] (BPair.ofNat n)).oneValue
      (BPair.ofNat m) := by
  rw [← hm]
  exact BPair.oneValue_trans (eval_two _ _ _)
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl (BPair.ofNat a))
        (BPair.oneValue_symm (BPair.ofNat_mul n b)))
      (BPair.oneValue_symm (BPair.ofNat_add a (n * b))))

/-- The residue's factor reads the argument's own count. -/
private theorem eval_arg (n : Nat) :
    (poly.eval facArg (BPair.ofNat n)).oneValue (BPair.ofNat n) :=
  BPair.oneValue_trans (eval_lin _ _) (BPair.unit_add (BPair.ofNat n))

/-- The raised factor's count read at its sum. -/
private theorem eval_up (a n m : Nat) (hm : a + n = m) :
    (poly.eval (facUp a) (BPair.ofNat n)).oneValue (BPair.ofNat m) :=
  hm ▸ BPair.oneValue_trans (eval_lin _ _)
    (BPair.oneValue_symm (BPair.ofNat_add a n))

/-- The lowered factor's count read at the gap witness `a + m = n`. -/
private theorem eval_dn (a n m : Nat) (hm : a + m = n) :
    (poly.eval (facDn a) (BPair.ofNat n)).oneValue (BPair.ofNat m) := by
  refine BPair.oneValue_trans (eval_lin _ _) ?_
  have e1 : (BPair.ofNat n).oneValue (BPair.ofNat a + BPair.ofNat m) :=
    hm ▸ BPair.ofNat_add a m
  refine BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl ((BPair.ofNat a).swap)) e1) ?_
  rw [← BPair.add_assoc]
  exact BPair.oneValue_trans
    (BPair.add_congr
      (BPair.swap_add_null (BPair.oneValue_refl (BPair.ofNat a)))
      (BPair.oneValue_refl (BPair.ofNat m)))
    (BPair.unit_add (BPair.ofNat m))

/-- The convolution's count read is the two counts' product. -/
private theorem eval_prod {p q : poly.Poly} {r : BPair} {u v : Nat}
    (hp : (poly.eval p r).oneValue (BPair.ofNat u))
    (hq : (poly.eval q r).oneValue (BPair.ofNat v)) :
    (poly.eval (poly.mul p q) r).oneValue (BPair.ofNat (u * v)) :=
  BPair.oneValue_trans (poly.eval_mul p q r)
    (BPair.oneValue_trans (BPair.mul_congr hp hq)
      (BPair.oneValue_symm (BPair.ofNat_mul u v)))

/-- The cross-multiplied tie at two count reads against their
scales, the scales' own product identity the tie's content. -/
private theorem tie_read {p q : poly.Poly} {r : BPair} {u v A B : Nat}
    (hp : (poly.eval p r).oneValue (BPair.ofNat u))
    (hq : (poly.eval q r).oneValue (BPair.ofNat v))
    (hn : u * A = v * B) :
    ((poly.eval p r).mul (BPair.ofNat A)).oneValue
      ((poly.eval q r).mul (BPair.ofNat B)) :=
  BPair.oneValue_trans
    (BPair.mul_congr hp (BPair.oneValue_refl (BPair.ofNat A)))
    (BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofNat_mul u A))
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (congrArg BPair.ofNat hn))
        (BPair.oneValue_trans (BPair.ofNat_mul v B)
          (BPair.mul_congr (BPair.oneValue_symm hq)
            (BPair.oneValue_refl (BPair.ofNat B))))))

/-- The adjoint's dimension at a width, `d² - 1` read as the
residue against its own raise by two. -/
private theorem sq_pred (a : Nat) :
    (a + 1) * (a + 1) - 1 = a * (a + 2) := by
  rw [show (a + 1) * (a + 1) = a * (a + 2) + 1 from ground.sqJoin a]
  exact ground.addSubSelfR (a * (a + 2)) 1

/-- The unit row's cleared dimension, at every width. -/
private theorem dim_unit (h : Nat) :
    4 * weyldim.dimOf (channels.rowUnit (h + 2)) = 4 :=
  congrArg (fun l => ground.getAt 0 l 0)
    (channels.rows_dim (h + 2) (Nat.le_add_left 2 h))

/-- The `θ` row's cleared dimension, from the width three. -/
private theorem dim_theta (h : Nat) :
    4 * weyldim.dimOf (channels.rowTheta (h + 3))
      = 4 * ((h + 3) * (h + 3) - 1) :=
  congrArg (fun l => ground.getAt 0 l 1)
    (channels.rows_dim (h + 3) (Nat.le_add_left 2 (h + 1)))

/-- The `2θ` row's cleared dimension, at every width. -/
private theorem dim_twoTheta (h : Nat) :
    4 * weyldim.dimOf (channels.rowTwoTheta (h + 2))
      = (h + 2) * (h + 2) * ((h + 1) * (h + 5)) :=
  congrArg (fun l => ground.getAt 0 l 2)
    (channels.rows_dim (h + 2) (Nat.le_add_left 2 h))

/-- The dual pair's first row's cleared dimension, from the width
three. -/
private theorem dim_dual (h : Nat) :
    4 * weyldim.dimOf (channels.rowDualA (h + 3))
      = (h + 1) * ((h + 2) * ((h + 4) * (h + 5))) :=
  congrArg (fun l => ground.getAt 0 l 3)
    (channels.rows_dim (h + 3) (Nat.le_add_left 2 (h + 1)))

/-- The dual pair's second row's cleared dimension, from the width
three. -/
private theorem dim_dualB (h : Nat) :
    4 * weyldim.dimOf (channels.rowDualB (h + 3))
      = (h + 1) * ((h + 2) * ((h + 4) * (h + 5))) :=
  congrArg (fun l => ground.getAt 0 l 4)
    (channels.rows_dim (h + 3) (Nat.le_add_left 2 (h + 1)))

/-- The `ω₂ + ω₂*` row's cleared dimension, from the width
four. -/
private theorem dim_omega (h : Nat) :
    4 * weyldim.dimOf (channels.rowOmega (h + 4))
      = (h + 4) * (h + 4) * ((h + 5) * (h + 1)) :=
  congrArg (fun l => ground.getAt 0 l 5)
    (channels.rows_dim (h + 4) (Nat.le_add_left 2 (h + 2)))

/-- The unit channel's display ties at the channel table's read:
the weight's members against `[m_k d_k : d_θ²]` multiplied across,
at the residue `r = h + 1` of every width `d = h + 2`. -/
theorem wUnit_read (h : Nat) :
    ((poly.eval wUnit.1 (BPair.ofNat (h + 1))).mul
        (BPair.ofNat
          (4 * (((h + 2) * (h + 2) - 1) * ((h + 2) * (h + 2) - 1))))).oneValue
      ((poly.eval wUnit.2 (BPair.ofNat (h + 1))).mul
        (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowUnit (h + 2)))))) := by
  rw [dim_unit h, sq_pred (h + 1)]
  refine tie_read (u := 1)
    (v := ((h + 1) * (h + 3)) * ((h + 1) * (h + 3)))
    (eval_const 1 (BPair.ofNat (h + 1))) ?_ ?_
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wUnit.2
        (poly.mul (poly.mul facArg (facUp 2)) (poly.mul facArg (facUp 2)))
        by decide +kernel) (BPair.ofNat (h + 1)))
      (eval_prod
        (eval_prod (eval_arg _)
          (eval_up 2 (h + 1) (h + 3) (Nat.add_comm 2 (h + 1))))
        (eval_prod (eval_arg _)
          (eval_up 2 (h + 1) (h + 3) (Nat.add_comm 2 (h + 1)))))
  · rw [Nat.one_mul, Nat.one_mul]
    exact Nat.mul_comm 4 (((h + 1) * (h + 3)) * ((h + 1) * (h + 3)))

/-- The `θ` channel's display ties at the channel table's read:
the weight's members against `[m_k d_k : d_θ²]` multiplied across,
at the residue `r = h + 2` of every width `d = h + 3`, the base's
own floor. -/
theorem wTheta_read (h : Nat) :
    ((poly.eval wTheta.1 (BPair.ofNat (h + 2))).mul
        (BPair.ofNat
          (4 * (((h + 3) * (h + 3) - 1) * ((h + 3) * (h + 3) - 1))))).oneValue
      ((poly.eval wTheta.2 (BPair.ofNat (h + 2))).mul
        (BPair.ofNat (2 * (4 * weyldim.dimOf (channels.rowTheta (h + 3)))))) := by
  rw [dim_theta h, sq_pred (h + 2)]
  refine tie_read (u := 2) (v := (h + 2) * (h + 4))
    (eval_const 2 (BPair.ofNat (h + 2))) ?_ ?_
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wTheta.2
        (poly.mul facArg (facUp 2)) by decide +kernel) (BPair.ofNat (h + 2)))
      (eval_prod (eval_arg _)
        (eval_up 2 (h + 2) (h + 4) (Nat.add_comm 2 (h + 2))))
  · rw [← ground.mulAssoc 2 4 (((h + 2) * (h + 4)) * ((h + 2) * (h + 4))),
      ← ground.mulAssoc 2 4 ((h + 2) * (h + 4)),
      ground.mulLeftComm ((h + 2) * (h + 4)) (2 * 4) ((h + 2) * (h + 4))]

/-- The `2θ` channel's display ties at the channel table's read:
the weight's members against `[m_k d_k : d_θ²]` multiplied across,
at the residue `r = h + 1` of every width `d = h + 2`. -/
theorem wTwoTheta_read (h : Nat) :
    ((poly.eval wTwoTheta.1 (BPair.ofNat (h + 1))).mul
        (BPair.ofNat
          (4 * (((h + 2) * (h + 2) - 1) * ((h + 2) * (h + 2) - 1))))).oneValue
      ((poly.eval wTwoTheta.2 (BPair.ofNat (h + 1))).mul
        (BPair.ofNat
          (1 * (4 * weyldim.dimOf (channels.rowTwoTheta (h + 2)))))) := by
  rw [dim_twoTheta h, sq_pred (h + 1)]
  refine tie_read (u := ((h + 2) * (h + 2)) * ((h + 1) * (h + 5)))
    (v := 4 * (((h + 1) * (h + 3)) * ((h + 1) * (h + 3)))) ?_ ?_ ?_
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wTwoTheta.1
        (poly.mul (poly.mul (facUp 1) (facUp 1)) (poly.mul facArg (facUp 4)))
        by decide +kernel) (BPair.ofNat (h + 1)))
      (eval_prod
        (eval_prod (eval_up 1 (h + 1) (h + 2) (Nat.add_comm 1 (h + 1)))
          (eval_up 1 (h + 1) (h + 2) (Nat.add_comm 1 (h + 1))))
        (eval_prod (eval_arg _)
          (eval_up 4 (h + 1) (h + 5) (Nat.add_comm 4 (h + 1)))))
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wTwoTheta.2
        (poly.mul [BPair.ofNat 4]
          (poly.mul (poly.mul facArg (facUp 2)) (poly.mul facArg (facUp 2))))
        by decide +kernel) (BPair.ofNat (h + 1)))
      (eval_prod (eval_const 4 _)
        (eval_prod
          (eval_prod (eval_arg _)
            (eval_up 2 (h + 1) (h + 3) (Nat.add_comm 2 (h + 1))))
          (eval_prod (eval_arg _)
            (eval_up 2 (h + 1) (h + 3) (Nat.add_comm 2 (h + 1))))))
  · rw [Nat.one_mul]
    exact Nat.mul_comm (((h + 2) * (h + 2)) * ((h + 1) * (h + 5)))
      (4 * (((h + 1) * (h + 3)) * ((h + 1) * (h + 3))))

/-- The dual pair's first display tie at the channel table's read:
the weight's members against `[m_k d_k : d_θ²]` multiplied across,
at the residue `r = h + 2` of every width `d = h + 3`, the pair's
own floor. -/
theorem wDual_read (h : Nat) :
    ((poly.eval wDual.1 (BPair.ofNat (h + 2))).mul
        (BPair.ofNat
          (4 * (((h + 3) * (h + 3) - 1) * ((h + 3) * (h + 3) - 1))))).oneValue
      ((poly.eval wDual.2 (BPair.ofNat (h + 2))).mul
        (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowDualA (h + 3)))))) := by
  rw [dim_dual h, sq_pred (h + 2)]
  refine tie_read (u := (h + 1) * (h + 5))
    (v := 4 * ((h + 2) * (h + 4))) ?_ ?_ ?_
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wDual.1
        (poly.mul (facDn 1) (facUp 3)) by decide +kernel) (BPair.ofNat (h + 2)))
      (eval_prod (eval_dn 1 (h + 2) (h + 1) (Nat.add_comm 1 (h + 1)))
        (eval_up 3 (h + 2) (h + 5) (Nat.add_comm 3 (h + 2))))
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wDual.2
        (poly.mul [BPair.ofNat 4] (poly.mul facArg (facUp 2)))
        by decide +kernel) (BPair.ofNat (h + 2)))
      (eval_prod (eval_const 4 _)
        (eval_prod (eval_arg _)
          (eval_up 2 (h + 2) (h + 4) (Nat.add_comm 2 (h + 2)))))
  · rw [Nat.one_mul,
      ground.mulLeftComm ((h + 1) * (h + 5)) 4
        (((h + 2) * (h + 4)) * ((h + 2) * (h + 4))),
      ground.mulAssoc 4 ((h + 2) * (h + 4))
        ((h + 1) * ((h + 2) * ((h + 4) * (h + 5)))),
      ground.mulLeftComm ((h + 2) * (h + 4)) (h + 1)
        ((h + 2) * ((h + 4) * (h + 5))),
      ground.mulAssoc (h + 1) (h + 5)
        (((h + 2) * (h + 4)) * ((h + 2) * (h + 4))),
      ← ground.mulAssoc (h + 2) (h + 4) (h + 5),
      ← ground.mulAssoc ((h + 2) * (h + 4)) ((h + 2) * (h + 4)) (h + 5),
      Nat.mul_comm (h + 5) (((h + 2) * (h + 4)) * ((h + 2) * (h + 4)))]

/-- The dual pair's second display tie: the one closed form at the
pair's two rows, the first tie read across `rows_dim`'s shared
entry. -/
theorem wDualB_read (h : Nat) :
    ((poly.eval wDual.1 (BPair.ofNat (h + 2))).mul
        (BPair.ofNat
          (4 * (((h + 3) * (h + 3) - 1) * ((h + 3) * (h + 3) - 1))))).oneValue
      ((poly.eval wDual.2 (BPair.ofNat (h + 2))).mul
        (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowDualB (h + 3)))))) := by
  rw [dim_dualB h, ← dim_dual h]
  exact wDual_read h

/-- The `ω₂ + ω₂*` channel's display ties at the channel table's
read: the weight's members against `[m_k d_k : d_θ²]` multiplied
across, at the residue `r = h + 3` of every width `d = h + 4`, the
row's own floor. -/
theorem wOmega_read (h : Nat) :
    ((poly.eval wOmega.1 (BPair.ofNat (h + 3))).mul
        (BPair.ofNat
          (4 * (((h + 4) * (h + 4) - 1) * ((h + 4) * (h + 4) - 1))))).oneValue
      ((poly.eval wOmega.2 (BPair.ofNat (h + 3))).mul
        (BPair.ofNat (1 * (4 * weyldim.dimOf (channels.rowOmega (h + 4)))))) := by
  rw [dim_omega h, sq_pred (h + 3)]
  refine tie_read (u := ((h + 4) * (h + 4)) * ((h + 5) * (h + 1)))
    (v := 4 * (((h + 3) * (h + 5)) * ((h + 3) * (h + 5)))) ?_ ?_ ?_
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wOmega.1
        (poly.mul (poly.mul (facUp 1) (facUp 1)) (poly.mul (facUp 2) (facDn 2)))
        by decide +kernel) (BPair.ofNat (h + 3)))
      (eval_prod
        (eval_prod (eval_up 1 (h + 3) (h + 4) (Nat.add_comm 1 (h + 3)))
          (eval_up 1 (h + 3) (h + 4) (Nat.add_comm 1 (h + 3))))
        (eval_prod (eval_up 2 (h + 3) (h + 5) (Nat.add_comm 2 (h + 3)))
          (eval_dn 2 (h + 3) (h + 1) (Nat.add_comm 2 (h + 1)))))
  · exact BPair.oneValue_trans
      (poly.eval_congr (show poly.oneValue wOmega.2
        (poly.mul [BPair.ofNat 4]
          (poly.mul (poly.mul facArg (facUp 2)) (poly.mul facArg (facUp 2))))
        by decide +kernel) (BPair.ofNat (h + 3)))
      (eval_prod (eval_const 4 _)
        (eval_prod
          (eval_prod (eval_arg _)
            (eval_up 2 (h + 3) (h + 5) (Nat.add_comm 2 (h + 3))))
          (eval_prod (eval_arg _)
            (eval_up 2 (h + 3) (h + 5) (Nat.add_comm 2 (h + 3))))))
  · rw [Nat.one_mul]
    exact Nat.mul_comm (((h + 4) * (h + 4)) * ((h + 5) * (h + 1)))
      (4 * (((h + 3) * (h + 5)) * ((h + 3) * (h + 5))))

/-- The unit weight's second member exceeds in degree
(`thm:windowsep`'s leading terms). -/
theorem wUnit_deg : (wUnit.1).length < (wUnit.2).length := by decide +kernel

/-- The `θ` weight's second member exceeds in degree
(`thm:windowsep`'s leading terms). -/
theorem wTheta_deg : (wTheta.1).length < (wTheta.2).length := by decide +kernel

/-- The `2θ` channel weight reads `[1 : 4]` at the top. -/
theorem wTwoTheta_top :
    ((BPair.ofNat 4).mul (poly.top wTwoTheta.1)).oneValue
      (poly.top wTwoTheta.2) := by decide +kernel

/-- The dual pair's weight reads `[1 : 4]` at the top. -/
theorem wDual_top :
    ((BPair.ofNat 4).mul (poly.top wDual.1)).oneValue
      (poly.top wDual.2) := by decide +kernel

/-- The `ω₂ + ω₂*` channel weight reads `[1 : 4]` at the top. -/
theorem wOmega_top :
    ((BPair.ofNat 4).mul (poly.top wOmega.1)).oneValue
      (poly.top wOmega.2) := by decide +kernel

/-! The slot-two self-energy (`thm:network`(iii)). -/

/-- The resolvent factor at a channel, `[q_k : 2q_k + p_k]` at
`ĉ₂(k) = [p_k : q_k]`: the factor's gap the module pair's network
eigenvalue against the module count, `3 + ĉ₂(k) + 3` against
`E₀ = 4` at `ĉ₂(adj) = 1`, a constructed pair at an occupied
second member and `none` at the vacant one. -/
def resFactor {L : Type} (F : Data L) (k : L) :
    Option ground.Pair :=
  match F.c2D with
  | 0 => none
  | q + 1 =>
    some ⟨ground.posOfSucc q,
      ground.posOfSucc (2 * q + 1 + F.c2N k)⟩

/-- The slot-two self-energy, `Σ_k w_k [q_k : 2q_k + p_k]` over
the adjoint square's channel list (`fusion.adjChannels`): at an
occupied Casimir scale and adjoint dimension each occupied channel
joins the fold at the products' display, the fold seeded at its first member, with the vacant
interface data — the Casimir scale, the adjoint dimension, or
every count — at `none`. -/
def selfEnergy {L : Type} (F : Data L) : Option ground.Pair :=
  match F.c2D, F.dim F.theta with
  | 0, _ => none
  | _ + 1, 0 => none
  | q + 1, t + 1 =>
    (adjChannels F).foldl (fun acc c =>
      match c.1 with
      | 0 => acc
      | m + 1 =>
        match acc with
        | none => some ⟨ground.posOfSucc m * ground.posOfSucc q,
            ground.posOfSucc t * ground.posOfSucc t
              * ground.posOfSucc (2 * q + 1 + c.2)⟩
        | some a =>
          some (a + ⟨ground.posOfSucc m * ground.posOfSucc q,
            ground.posOfSucc t * ground.posOfSucc t
              * ground.posOfSucc (2 * q + 1 + c.2)⟩)) none

/-! The theta graph, and the reduction (`thm:network`(i)). -/

/-- The theta graph's committed region: two square plaquettes
sharing one link.  The shared link `0` runs between the two
three-valent vertices `0` and `1`; links `1, 2, 3` are the first
plaquette's unshared path through vertices `2, 3` and links
`4, 5, 6` the second's through `4, 5`, each path oriented from
vertex `0` to vertex `1`; the two boundary words close each
square, and the coloring witnesses the even cycles. -/
def thetaR : lattice.Region :=
  ⟨7, 6, [0, 0, 2, 3, 0, 4, 5], [1, 2, 3, 1, 4, 5, 1],
   [[(0, true), (3, false), (2, false), (1, false)],
    [(0, true), (6, false), (5, false), (4, false)]],
   [false, true, true, false, true, false], rfl, rfl⟩

/-- The `Θ(R₁, k, R₂)`-network's spread over the theta region's
links: the shared link at the middle label with each path's three
links at its own label. -/
def netConf {L : Type} (R1 k R2 : L) : List L :=
  [k, R1, R1, R1, R2, R2, R2]

/-- The spread's unit read (`thm:network`(i)): the
`Θ(R₁, k, R₂)`-network's spread is the unit assignment exactly at its
three unit labels. -/
theorem spreadUnit {L : Type} (F : Data L) (R1 k R2 : L) :
    (netConf R1 k R2).all (fun x => F.eqL x F.unit)
      = (F.eqL k F.unit && F.eqL R1 F.unit && F.eqL R2 F.unit) := by
  show (F.eqL k F.unit && (F.eqL R1 F.unit && (F.eqL R1 F.unit
      && (F.eqL R1 F.unit && (F.eqL R2 F.unit && (F.eqL R2 F.unit
      && (F.eqL R2 F.unit && true))))))) = _
  cases F.eqL k F.unit <;> cases F.eqL R1 F.unit <;> cases F.eqL R2 F.unit <;> rfl

/-! The reduction (`thm:network`(i)): the two-valent vertices' reads
at the incident pairs, the content fold at the spread, the
three-valent vertices' multiplicities, and an occupied
configuration read as the `Θ(R₁, k, R₂)`-network data. -/

/-- The label at one incident entry: an occupied key reads its own
label at an outgoing end and the dual at an incoming one, a key at
the unit reading `none`. -/
private def labelOf {L : Type} (F : Data L) (a : List L)
    (e : Nat × Bool) : Option L :=
  let l := ground.getAt F.unit a e.1
  if F.eqL l F.unit then none else if e.2 then some l else some (F.dual l)

/-- The labels along a list of incident entries. -/
private def labelsOf {L : Type} (F : Data L) (a : List L)
    (es : List (Nat × Bool)) : List L :=
  es.filterMap (labelOf F a)

/-- The vertex's incident labels are the entry read along its
incident list. -/
private theorem labels_read {L : Type} (F : Data L)
    (R : lattice.Region) (a : List L) (v : Nat) :
    carrier.incidentLabels F R a v = labelsOf F a (lattice.incident R v) :=
  rfl

/-- An occupied key at an outgoing end reads its own label. -/
private theorem labelOf_out {L : Type} (F : Data L) (a : List L) (i : Nat)
    (h : F.eqL (ground.getAt F.unit a i) F.unit = false) :
    labelOf F a (i, true) = some (ground.getAt F.unit a i) := by
  show (if F.eqL (ground.getAt F.unit a i) F.unit then none
    else some (ground.getAt F.unit a i)) = some (ground.getAt F.unit a i)
  rw [h]
  exact rfl

/-- An occupied key at an incoming end reads its label's dual. -/
private theorem labelOf_in {L : Type} (F : Data L) (a : List L) (i : Nat)
    (h : F.eqL (ground.getAt F.unit a i) F.unit = false) :
    labelOf F a (i, false) = some (F.dual (ground.getAt F.unit a i)) := by
  show (if F.eqL (ground.getAt F.unit a i) F.unit then none
      else some (F.dual (ground.getAt F.unit a i)))
    = some (F.dual (ground.getAt F.unit a i))
  rw [h]
  exact rfl

/-- A key at the unit reads `none` at either end. -/
private theorem labelOf_unit {L : Type} (F : Data L) (a : List L)
    (e : Nat × Bool) (h : F.eqL (ground.getAt F.unit a e.1) F.unit = true) :
    labelOf F a e = none := by
  show (if F.eqL (ground.getAt F.unit a e.1) F.unit then none
      else if e.2 then some (ground.getAt F.unit a e.1)
        else some (F.dual (ground.getAt F.unit a e.1))) = none
  rw [h]
  exact rfl

/-- An entry reading a label joins it to the labels of the entries
past it. -/
private theorem labelsOf_cons_some {L : Type} (F : Data L) (a : List L)
    (e : Nat × Bool) (b : L) (t : List (Nat × Bool))
    (h : labelOf F a e = some b) :
    labelsOf F a (e :: t) = b :: labelsOf F a t := by
  show (match labelOf F a e with
        | none => labelsOf F a t
        | some c => c :: labelsOf F a t) = b :: labelsOf F a t
  rw [h]

/-- An entry at the unit passes to the entries past it. -/
private theorem labelsOf_cons_none {L : Type} (F : Data L) (a : List L)
    (e : Nat × Bool) (t : List (Nat × Bool)) (h : labelOf F a e = none) :
    labelsOf F a (e :: t) = labelsOf F a t := by
  show (match labelOf F a e with
        | none => labelsOf F a t
        | some c => c :: labelsOf F a t) = labelsOf F a t
  rw [h]

/-- The two-valent vertex's read at its link pair: both keys at the
unit, or both occupied with the two duals at one label. -/
private def pairRead {L : Type} (F : Data L) (x y : L) : Prop :=
  (F.eqL x F.unit = true ∧ F.eqL y F.unit = true)
    ∨ (F.eqL x F.unit = false ∧ F.eqL y F.unit = false
        ∧ F.eqL (F.dual x) (F.dual y) = true)

/-- The convolution identity at a two-valent vertex: at an incoming
key `i` and an outgoing key `j` an occupied configuration reads the
pair, the unit law's own Kronecker read
(`carrier.invCount_pair_pos`) at the occupied arm and the one-label
read (`carrier.invCount_one_pos`) refusing the arms where one key is
occupied beside a key at the unit. -/
private theorem pairAt {L : Type} (F : Data L)
    (hdu : ∀ x, F.eqL (F.dual x) F.unit = true → F.eqL x F.unit = true)
    (R : lattice.Region) (a : List L) (v i j : Nat) (hv : v < R.verts)
    (hinc : lattice.incident R v = [(i, false), (j, true)])
    (ha : carrier.occupied F R a = true) :
    pairRead F (ground.getAt F.unit a i) (ground.getAt F.unit a j) := by
  cases hi : F.eqL (ground.getAt F.unit a i) F.unit with
  | true =>
    cases hj : F.eqL (ground.getAt F.unit a j) F.unit with
    | true => exact Or.inl (And.intro hi hj)
    | false =>
      have hl : carrier.incidentLabels F R a v
          = [ground.getAt F.unit a j] := by
        rw [labels_read F R a v, hinc,
          labelsOf_cons_none F a (i, false) _ (labelOf_unit F a (i, false) hi),
          labelsOf_cons_some F a (j, true) (ground.getAt F.unit a j) _
            (labelOf_out F a j hj)]
        exact rfl
      have hp : 0 < carrier.invCount F [ground.getAt F.unit a j] := by
        have h0 : 0 < carrier.vmult F R a v :=
          carrier.vmult_pos F R a v hv ha
        show 0 < carrier.invCount F [ground.getAt F.unit a j]
        rw [← hl]
        exact h0
      exact absurd (carrier.invCount_one_pos F _ hp)
        (fun hc => Bool.noConfusion (hj.symm.trans hc))
  | false =>
    cases hj : F.eqL (ground.getAt F.unit a j) F.unit with
    | true =>
      have hl : carrier.incidentLabels F R a v
          = [F.dual (ground.getAt F.unit a i)] := by
        rw [labels_read F R a v, hinc,
          labelsOf_cons_some F a (i, false)
            (F.dual (ground.getAt F.unit a i)) _ (labelOf_in F a i hi),
          labelsOf_cons_none F a (j, true) _ (labelOf_unit F a (j, true) hj)]
        exact rfl
      have hp : 0 < carrier.invCount F
          [F.dual (ground.getAt F.unit a i)] := by
        have h0 : 0 < carrier.vmult F R a v :=
          carrier.vmult_pos F R a v hv ha
        show 0 < carrier.invCount F [F.dual (ground.getAt F.unit a i)]
        rw [← hl]
        exact h0
      exact absurd (hdu _ (carrier.invCount_one_pos F _ hp))
        (fun hc => Bool.noConfusion (hi.symm.trans hc))
    | false =>
      have hl : carrier.incidentLabels F R a v
          = [F.dual (ground.getAt F.unit a i), ground.getAt F.unit a j] := by
        rw [labels_read F R a v, hinc,
          labelsOf_cons_some F a (i, false)
            (F.dual (ground.getAt F.unit a i)) _ (labelOf_in F a i hi),
          labelsOf_cons_some F a (j, true) (ground.getAt F.unit a j) _
            (labelOf_out F a j hj)]
        exact rfl
      have hp : 0 < carrier.invCount F
          [F.dual (ground.getAt F.unit a i), ground.getAt F.unit a j] := by
        have h0 : 0 < carrier.vmult F R a v :=
          carrier.vmult_pos F R a v hv ha
        show 0 < carrier.invCount F
          [F.dual (ground.getAt F.unit a i), ground.getAt F.unit a j]
        rw [← hl]
        exact h0
      exact Or.inr (And.intro hi (And.intro hj
        (carrier.invCount_pair_pos F _ _ hp)))

/-- The two paths' reads (`thm:network`(i)): at each of the theta
region's four two-valent vertices an occupied configuration reads
its two links at one pair — both at the unit, or both occupied with
the two duals at one label — so each three-link path reads at one
label.  The involution's unit read `hdu` enters at the arms where
one link is occupied beside a link at the unit. -/
theorem pathReads {L : Type} (F : Data L)
    (hdu : ∀ x, F.eqL (F.dual x) F.unit = true → F.eqL x F.unit = true)
    (a : List L) (ha : carrier.occupied F thetaR a = true) :
    ((F.eqL (ground.getAt F.unit a 1) F.unit = true
          ∧ F.eqL (ground.getAt F.unit a 2) F.unit = true)
        ∨ (F.eqL (ground.getAt F.unit a 1) F.unit = false
          ∧ F.eqL (ground.getAt F.unit a 2) F.unit = false
          ∧ F.eqL (F.dual (ground.getAt F.unit a 1))
              (F.dual (ground.getAt F.unit a 2)) = true))
      ∧ ((F.eqL (ground.getAt F.unit a 2) F.unit = true
          ∧ F.eqL (ground.getAt F.unit a 3) F.unit = true)
        ∨ (F.eqL (ground.getAt F.unit a 2) F.unit = false
          ∧ F.eqL (ground.getAt F.unit a 3) F.unit = false
          ∧ F.eqL (F.dual (ground.getAt F.unit a 2))
              (F.dual (ground.getAt F.unit a 3)) = true))
      ∧ ((F.eqL (ground.getAt F.unit a 4) F.unit = true
          ∧ F.eqL (ground.getAt F.unit a 5) F.unit = true)
        ∨ (F.eqL (ground.getAt F.unit a 4) F.unit = false
          ∧ F.eqL (ground.getAt F.unit a 5) F.unit = false
          ∧ F.eqL (F.dual (ground.getAt F.unit a 4))
              (F.dual (ground.getAt F.unit a 5)) = true))
      ∧ ((F.eqL (ground.getAt F.unit a 5) F.unit = true
          ∧ F.eqL (ground.getAt F.unit a 6) F.unit = true)
        ∨ (F.eqL (ground.getAt F.unit a 5) F.unit = false
          ∧ F.eqL (ground.getAt F.unit a 6) F.unit = false
          ∧ F.eqL (F.dual (ground.getAt F.unit a 5))
              (F.dual (ground.getAt F.unit a 6)) = true)) :=
  And.intro (pairAt F hdu thetaR a 2 1 2 (by decide +kernel) (by decide +kernel) ha)
    (And.intro (pairAt F hdu thetaR a 3 2 3 (by decide +kernel) (by decide +kernel) ha)
      (And.intro (pairAt F hdu thetaR a 4 4 5 (by decide +kernel) (by decide +kernel) ha)
        (pairAt F hdu thetaR a 5 5 6 (by decide +kernel) (by decide +kernel) ha)))

/-- The content's step at a running value: an occupied label joins
its Casimir read, a label at the unit passing. -/
private def cstep {L : Type} (F : Data L) (acc : Nat) (l : L) : Nat :=
  if F.eqL l F.unit then acc else acc + F.c2N l

/-- The content's step at one label, the running value withdrawn. -/
private def gstep {L : Type} (F : Data L) (l : L) : Nat :=
  if F.eqL l F.unit then 0 else F.c2N l

/-- The step at its additive spelling. -/
private theorem cstep_add {L : Type} (F : Data L) (acc : Nat) (l : L) :
    cstep F acc l = acc + gstep F l := by
  show (if F.eqL l F.unit then acc else acc + F.c2N l)
    = acc + (if F.eqL l F.unit then 0 else F.c2N l)
  cases hl : F.eqL l F.unit with
  | true => exact (Nat.add_zero acc).symm
  | false => exact rfl

/-- `E` at the network spread (`thm:network`(i)): the content fold
reads the eigenvalue `3 C₂(R₁) + C₂(k) + 3 C₂(R₂)`, each path's
three links at its own label's Casimir and the shared link at the
middle label's, a label at the unit reading the sum's unit. -/
theorem netConf_energy {L : Type} (F : Data L) (R1 k R2 : L) :
    carrier.contentN F (netConf R1 k R2)
      = 3 * (if F.eqL R1 F.unit then 0 else F.c2N R1)
        + (if F.eqL k F.unit then 0 else F.c2N k)
        + 3 * (if F.eqL R2 F.unit then 0 else F.c2N R2) := by
  show cstep F (cstep F (cstep F (cstep F (cstep F (cstep F
      (cstep F 0 k) R1) R1) R1) R2) R2) R2
    = 3 * gstep F R1 + gstep F k + 3 * gstep F R2
  rw [Nat.add_comm (3 * gstep F R1) (gstep F k)]
  rw [cstep_add, cstep_add, cstep_add, cstep_add, cstep_add, cstep_add,
    cstep_add, ground.threeMul (gstep F R1), ground.threeMul (gstep F R2),
    Nat.zero_add,
    ← Nat.add_assoc (gstep F k) (gstep F R1 + gstep F R1) (gstep F R1),
    ← Nat.add_assoc (gstep F k) (gstep F R1) (gstep F R1),
    ← Nat.add_assoc (gstep F k + gstep F R1 + gstep F R1 + gstep F R1)
      (gstep F R2 + gstep F R2) (gstep F R2),
    ← Nat.add_assoc (gstep F k + gstep F R1 + gstep F R1 + gstep F R1)
      (gstep F R2) (gstep F R2)]

/-- The three-valent vertices' multiplicities at the network spread
(`thm:network`(i)): at three occupied labels vertex `0` reads the
invariant count of `(k, R₁, R₂)` along its three outgoing ends and
vertex `1` the count of the three duals along its three incoming
ends. -/
theorem netConf_vmult {L : Type} (F : Data L) (R1 k R2 : L)
    (h1 : F.eqL R1 F.unit = false) (hk : F.eqL k F.unit = false)
    (h2 : F.eqL R2 F.unit = false) :
    carrier.vmult F thetaR (netConf R1 k R2) 0
        = carrier.invCount F [k, R1, R2]
      ∧ carrier.vmult F thetaR (netConf R1 k R2) 1
        = carrier.invCount F [F.dual k, F.dual R1, F.dual R2] := by
  have hz : carrier.incidentLabels F thetaR (netConf R1 k R2) 0
      = [k, R1, R2] := by
    rw [labels_read F thetaR (netConf R1 k R2) 0,
      show lattice.incident thetaR 0 = [(0, true), (1, true), (4, true)]
        from by decide +kernel,
      labelsOf_cons_some F (netConf R1 k R2) (0, true) k _
        (labelOf_out F _ 0 hk),
      labelsOf_cons_some F (netConf R1 k R2) (1, true) R1 _
        (labelOf_out F _ 1 h1),
      labelsOf_cons_some F (netConf R1 k R2) (4, true) R2 _
        (labelOf_out F _ 4 h2)]
    exact rfl
  have ho : carrier.incidentLabels F thetaR (netConf R1 k R2) 1
      = [F.dual k, F.dual R1, F.dual R2] := by
    rw [labels_read F thetaR (netConf R1 k R2) 1,
      show lattice.incident thetaR 1 = [(0, false), (3, false), (6, false)]
        from by decide +kernel,
      labelsOf_cons_some F (netConf R1 k R2) (0, false) (F.dual k) _
        (labelOf_in F _ 0 hk),
      labelsOf_cons_some F (netConf R1 k R2) (3, false) (F.dual R1) _
        (labelOf_in F _ 3 h1),
      labelsOf_cons_some F (netConf R1 k R2) (6, false) (F.dual R2) _
        (labelOf_in F _ 6 h2)]
    exact rfl
  refine And.intro ?_ ?_
  · show carrier.invCount F
      (carrier.incidentLabels F thetaR (netConf R1 k R2) 0) = _
    rw [hz]
  · show carrier.invCount F
      (carrier.incidentLabels F thetaR (netConf R1 k R2) 1) = _
    rw [ho]

/-- The two-valent vertex's read at either arm gives the pair one
label: the unit arm at the unit labels' own read `huu`, the occupied
arm at the involution's `hdc`. -/
private theorem pairEq {L : Type} (F : Data L)
    (hdc : ∀ x y, F.eqL (F.dual x) (F.dual y) = true → F.eqL y x = true)
    (huu : ∀ x y, F.eqL x F.unit = true → F.eqL y F.unit = true →
      F.eqL y x = true) {x y : L} (h : pairRead F x y) :
    F.eqL y x = true := by
  cases h with
  | inl hu => exact huu x y hu.1 hu.2
  | inr hn => exact hdc x y hn.2.2

/-- The reduction (`thm:network`(i)): an occupied configuration on
the theta region's seven links is the `Θ(R₁, k, R₂)`-network spread
at its own labels, the shared link `0` at the middle label and each
path at its first link's label.  The two-valent reads (`pathReads`)
give each path's three links one label through the involution's
`hdc`, the unit labels' `huu` and the transitive read `htr`. -/
theorem netConf_det {L : Type} (F : Data L)
    (hdu : ∀ x, F.eqL (F.dual x) F.unit = true → F.eqL x F.unit = true)
    (hdc : ∀ x y, F.eqL (F.dual x) (F.dual y) = true → F.eqL y x = true)
    (huu : ∀ x y, F.eqL x F.unit = true → F.eqL y F.unit = true →
      F.eqL y x = true)
    (htr : ∀ x y z, F.eqL x y = true → F.eqL y z = true → F.eqL x z = true)
    (a : List L) (hlen : a.length = 7)
    (ha : carrier.occupied F thetaR a = true) :
    carrier.eqConf F a
      (netConf (ground.getAt F.unit a 1) (ground.getAt F.unit a 0)
        (ground.getAt F.unit a 4)) = true := by
  have hr := pathReads F hdu a ha
  have e21 : F.eqL (ground.getAt F.unit a 2) (ground.getAt F.unit a 1) = true :=
    pairEq F hdc huu hr.1
  have e32 : F.eqL (ground.getAt F.unit a 3) (ground.getAt F.unit a 2) = true :=
    pairEq F hdc huu hr.2.1
  have e54 : F.eqL (ground.getAt F.unit a 5) (ground.getAt F.unit a 4) = true :=
    pairEq F hdc huu hr.2.2.1
  have e65 : F.eqL (ground.getAt F.unit a 6) (ground.getAt F.unit a 5) = true :=
    pairEq F hdc huu hr.2.2.2
  have e31 : F.eqL (ground.getAt F.unit a 3) (ground.getAt F.unit a 1) = true :=
    htr _ _ _ e32 e21
  have e64 : F.eqL (ground.getAt F.unit a 6) (ground.getAt F.unit a 4) = true :=
    htr _ _ _ e65 e54
  refine carrier.eqConf_intro F a _ hlen (fun i hi => ?_)
  match i, hi with
  | 0, _ => exact F.eqLRefl (ground.getAt F.unit a 0)
  | 1, _ => exact F.eqLRefl (ground.getAt F.unit a 1)
  | 2, _ => exact e21
  | 3, _ => exact e31
  | 4, _ => exact F.eqLRefl (ground.getAt F.unit a 4)
  | 5, _ => exact e54
  | 6, _ => exact e64
  | n + 7, hn => exact absurd hn (Nat.not_lt_of_ge (Nat.le_add_left 7 n))

/-! The recoupling constituent (`thm:network`(iii)): the middle
Casimir values, the Lagrange interpolant along the shared-link
Casimir, the projected two-plaquette states, and the within-pair
middle matrix. -/

/-- The occupied middle Casimir values at the trace form, the
channel table's reads in its row order with the dual pair's
shared value one joint entry: `0`, `d_f`, `2d_f + 2`, `2d_f`, and
`2d_f - 2`, each one polynomial pair in the residue. -/
def nodes : List poly.PPair :=
  [poly.pZero,
   lap.dfP,
   ([⟨5, 1⟩, ⟨3, 1⟩], [⟨2, 1⟩]),
   ([⟨3, 1⟩, ⟨3, 1⟩], [⟨2, 1⟩]),
   ([BPair.unit, ⟨3, 1⟩], [⟨2, 1⟩])]


/-- Two pairs at second members the product's unit and first
members reading apart in count refuse the one-value read at the
argument. -/
private theorem gap_of {x y : poly.PPair} {r : BPair} {u v : Nat}
    (hx : (poly.eval x.1 r).oneValue (BPair.ofNat u))
    (hy : (poly.eval y.1 r).oneValue (BPair.ofNat v))
    (hx2 : x.2 = poly.one) (hy2 : y.2 = poly.one)
    (huv : ¬ u = v) : ¬ genericlift.agreeAt x y r := by
  intro hag
  refine huv (BPair.ofNat_inj ?_)
  have hd1 : (poly.eval x.2 r).oneValue (BPair.ofNat 1) := by
    rw [hx2]; exact poly.eval_one (BPair.ofNat 1) r
  have hd2 : (poly.eval y.2 r).oneValue (BPair.ofNat 1) := by
    rw [hy2]; exact poly.eval_one (BPair.ofNat 1) r
  exact BPair.oneValue_trans
    (BPair.oneValue_symm
      (BPair.oneValue_trans (BPair.mul_congr hx hd2)
        (BPair.mul_ofNat_one (BPair.ofNat u))))
    (BPair.oneValue_trans hag
      (BPair.oneValue_trans (BPair.mul_congr hy hd1)
        (BPair.mul_ofNat_one (BPair.ofNat v))))

/-- The residue's double at the middle values' argument. -/
private theorem two_step (h : Nat) : (h + 2) * 2 = h + (h + 4) := by
  rw [Nat.mul_succ (h + 2) 1, Nat.mul_one, Nat.add_assoc h 2 (h + 2),
    Nat.add_comm 2 (h + 2)]

/-- The first middle value's count read. -/
private theorem node_val0 (h : Nat) :
    (poly.eval (ground.getAt poly.pZero nodes 0).1
      (BPair.ofNat (h + 2))).oneValue (BPair.ofNat 0) :=
  BPair.oneValue_refl BPair.unit

/-- The second middle value's count read, `d_f`. -/
private theorem node_val1 (h : Nat) :
    (poly.eval (ground.getAt poly.pZero nodes 1).1
      (BPair.ofNat (h + 2))).oneValue (BPair.ofNat (h + 3)) :=
  eval_twoVal 1 1 (h + 2) (h + 3)
    (by rw [Nat.mul_one, Nat.add_comm 1 (h + 2)])

/-- The third middle value's count read, `2 d_f + 2`. -/
private theorem node_val2 (h : Nat) :
    (poly.eval (ground.getAt poly.pZero nodes 2).1
      (BPair.ofNat (h + 2))).oneValue (BPair.ofNat (h + (h + 8))) :=
  eval_twoVal 4 2 (h + 2) (h + (h + 8))
    (by rw [two_step h, Nat.add_comm 4 (h + (h + 4)),
      Nat.add_assoc h (h + 4) 4])

/-- The fourth middle value's count read, `2 d_f`. -/
private theorem node_val3 (h : Nat) :
    (poly.eval (ground.getAt poly.pZero nodes 3).1
      (BPair.ofNat (h + 2))).oneValue (BPair.ofNat (h + (h + 6))) :=
  eval_twoVal 2 2 (h + 2) (h + (h + 6))
    (by rw [two_step h, Nat.add_comm 2 (h + (h + 4)),
      Nat.add_assoc h (h + 4) 2])

/-- The fifth middle value's count read, `2 d_f - 2`. -/
private theorem node_val4 (h : Nat) :
    (poly.eval (ground.getAt poly.pZero nodes 4).1
      (BPair.ofNat (h + 2))).oneValue (BPair.ofNat (h + (h + 4))) :=
  eval_twoVal 0 2 (h + 2) (h + (h + 4)) (by rw [two_step h, Nat.zero_add])

/-- Counts reading apart keep their gap under a shared summand. -/
private theorem gap_hd {a b : Nat} (h : Nat) (hne : ¬ a = b) :
    ¬ (h + a : Nat) = h + b :=
  fun hc => hne (ground.addCancelL h hc)

/-- A count of three reads apart from every raise of the residue by
four and beyond. -/
private theorem gap_lit (h k : Nat) : ¬ (3 : Nat) = h + (k + 4) := by
  intro hc
  exact Nat.noConfusion (ground.addCancelL 3
    (show (3 : Nat) + 0 = 3 + (h + (k + 1)) by
      rw [Nat.add_comm 3 (h + (k + 1))]; exact hc))

/-- The channel distances' occupied gaps at the middle values, one
refusal per pair, at every residue `r = h + 2` and beyond. -/
theorem nodes_gap (h : Nat) :
    (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 0)
        (ground.getAt poly.pZero nodes 1) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 0)
        (ground.getAt poly.pZero nodes 2) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 0)
        (ground.getAt poly.pZero nodes 3) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 0)
        (ground.getAt poly.pZero nodes 4) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 1)
        (ground.getAt poly.pZero nodes 2) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 1)
        (ground.getAt poly.pZero nodes 3) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 1)
        (ground.getAt poly.pZero nodes 4) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 2)
        (ground.getAt poly.pZero nodes 3) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 2)
        (ground.getAt poly.pZero nodes 4) (BPair.ofNat (h + 2)))
    ∧ (¬ genericlift.agreeAt (ground.getAt poly.pZero nodes 3)
        (ground.getAt poly.pZero nodes 4) (BPair.ofNat (h + 2))) :=
  ⟨gap_of (node_val0 h) (node_val1 h) rfl rfl
      (fun hc => Nat.noConfusion hc),
   gap_of (node_val0 h) (node_val2 h) rfl rfl
      (fun hc => Nat.noConfusion hc),
   gap_of (node_val0 h) (node_val3 h) rfl rfl
      (fun hc => Nat.noConfusion hc),
   gap_of (node_val0 h) (node_val4 h) rfl rfl
      (fun hc => Nat.noConfusion hc),
   gap_of (node_val1 h) (node_val2 h) rfl rfl (gap_hd h (gap_lit h 4)),
   gap_of (node_val1 h) (node_val3 h) rfl rfl (gap_hd h (gap_lit h 2)),
   gap_of (node_val1 h) (node_val4 h) rfl rfl (gap_hd h (gap_lit h 0)),
   gap_of (node_val2 h) (node_val3 h) rfl rfl
      (gap_hd h (gap_hd h (by decide +kernel))),
   gap_of (node_val2 h) (node_val4 h) rfl rfl
      (gap_hd h (gap_hd h (by decide +kernel))),
   gap_of (node_val3 h) (node_val4 h) rfl rfl
      (gap_hd h (gap_hd h (by decide +kernel)))⟩

/-- The unit row's cleared Casimir, at every width. -/
private theorem dfq_unit (h : Nat) :
    c2hat.dfQ (channels.rowUnit (h + 2)) = 0 :=
  congrArg (fun l => ground.getAt 0 l 0)
    (channels.rows_dfQ (h + 2) (Nat.le_add_left 2 h))

/-- The `θ` row's cleared Casimir, at every width. -/
private theorem dfq_theta (h : Nat) :
    c2hat.dfQ (channels.rowTheta (h + 2)) = 2 * ((h + 2) * (h + 2)) :=
  congrArg (fun l => ground.getAt 0 l 1)
    (channels.rows_dfQ (h + 2) (Nat.le_add_left 2 h))

/-- The `2θ` row's cleared Casimir, at every width. -/
private theorem dfq_twoTheta (h : Nat) :
    c2hat.dfQ (channels.rowTwoTheta (h + 2))
      = 2 * ((h + 2) * (h + 2)) + 2 * ((h + 2) * (h + 4)) :=
  congrArg (fun l => ground.getAt 0 l 2)
    (channels.rows_dfQ (h + 2) (Nat.le_add_left 2 h))

/-- The dual pair's first row's cleared Casimir, from the width
three. -/
private theorem dfq_dual (h : Nat) :
    c2hat.dfQ (channels.rowDualA (h + 3)) = 4 * ((h + 3) * (h + 3)) :=
  congrArg (fun l => ground.getAt 0 l 3)
    (channels.rows_dfQ (h + 3) (Nat.le_add_left 2 (h + 1)))

/-- The dual pair's second row's cleared Casimir, from the width
three. -/
private theorem dfq_dualB (h : Nat) :
    c2hat.dfQ (channels.rowDualB (h + 3)) = 4 * ((h + 3) * (h + 3)) :=
  congrArg (fun l => ground.getAt 0 l 4)
    (channels.rows_dfQ (h + 3) (Nat.le_add_left 2 (h + 1)))

/-- The `ω₂ + ω₂*` row's cleared Casimir, from the width four. -/
private theorem dfq_omega (h : Nat) :
    c2hat.dfQ (channels.rowOmega (h + 4))
      = 2 * ((h + 4) * (h + 4)) + 2 * ((h + 4) * (h + 2)) :=
  congrArg (fun l => ground.getAt 0 l 5)
    (channels.rows_dfQ (h + 4) (Nat.le_add_left 2 (h + 2)))

/-- The unit middle value ties at the channel table's Casimir
column: the node against `[dfQ : 2 d_f]` multiplied across, at
every width `d = h + 2`. -/
theorem nodeUnit_read (h : Nat) :
    ((poly.eval (ground.getAt poly.pZero nodes 0).1
        (BPair.ofNat (h + 1))).mul (BPair.ofNat (2 * (h + 2)))).oneValue
      ((poly.eval (ground.getAt poly.pZero nodes 0).2
        (BPair.ofNat (h + 1))).mul
        (BPair.ofNat (c2hat.dfQ (channels.rowUnit (h + 2))))) := by
  rw [dfq_unit h]
  refine tie_read (u := 0) (v := 1)
    (BPair.oneValue_refl BPair.unit) (eval_const 1 _) ?_
  rw [Nat.zero_mul, Nat.one_mul]

/-- The `θ` middle value ties at the channel table's Casimir
column, at every width `d = h + 2`: the trace form's `d_f`. -/
theorem nodeTheta_read (h : Nat) :
    ((poly.eval (ground.getAt poly.pZero nodes 1).1
        (BPair.ofNat (h + 1))).mul (BPair.ofNat (2 * (h + 2)))).oneValue
      ((poly.eval (ground.getAt poly.pZero nodes 1).2
        (BPair.ofNat (h + 1))).mul
        (BPair.ofNat (c2hat.dfQ (channels.rowTheta (h + 2))))) := by
  rw [dfq_theta h]
  refine tie_read (u := h + 2) (v := 1)
    (eval_twoVal 1 1 (h + 1) (h + 2)
      (by rw [Nat.mul_one]; exact Nat.add_comm 1 (h + 1)))
    (eval_const 1 _) ?_
  rw [Nat.one_mul]
  exact ground.mulLeftComm (h + 2) 2 (h + 2)

/-- The `2θ` middle value ties at the channel table's Casimir
column, at every width `d = h + 2`: `2 d_f + 2`. -/
theorem nodeTwoTheta_read (h : Nat) :
    ((poly.eval (ground.getAt poly.pZero nodes 2).1
        (BPair.ofNat (h + 1))).mul (BPair.ofNat (2 * (h + 2)))).oneValue
      ((poly.eval (ground.getAt poly.pZero nodes 2).2
        (BPair.ofNat (h + 1))).mul
        (BPair.ofNat (c2hat.dfQ (channels.rowTwoTheta (h + 2))))) := by
  rw [dfq_twoTheta h]
  refine tie_read (u := (h + 2) + (h + 4)) (v := 1)
    (eval_twoVal 4 2 (h + 1) ((h + 2) + (h + 4))
      (by
        rw [Nat.mul_succ (h + 1) 1, Nat.mul_one,
          Nat.add_comm 4 ((h + 1) + (h + 1)),
          Nat.add_assoc (h + 1) (h + 1) 4]
        show h + 1 + (h + 1 + 4) = Nat.succ (h + 1) + (h + 4)
        rw [Nat.succ_add (h + 1) (h + 4)]
        exact rfl))
    (eval_const 1 _) ?_
  rw [Nat.one_mul, Nat.mul_comm ((h + 2) + (h + 4)) (2 * (h + 2)),
    ground.mulAssoc 2 (h + 2) ((h + 2) + (h + 4)),
    Nat.left_distrib (h + 2) (h + 2) (h + 4),
    Nat.left_distrib 2 ((h + 2) * (h + 2)) ((h + 2) * (h + 4))]

/-- The dual pair's middle value ties at the channel table's
Casimir column, from the width `d = h + 3`: the shared value
`2 d_f` at the pair's first row. -/
theorem nodeDual_read (h : Nat) :
    ((poly.eval (ground.getAt poly.pZero nodes 3).1
        (BPair.ofNat (h + 2))).mul (BPair.ofNat (2 * (h + 3)))).oneValue
      ((poly.eval (ground.getAt poly.pZero nodes 3).2
        (BPair.ofNat (h + 2))).mul
        (BPair.ofNat (c2hat.dfQ (channels.rowDualA (h + 3))))) := by
  rw [dfq_dual h]
  refine tie_read (u := (h + 3) + (h + 3)) (v := 1)
    (eval_twoVal 2 2 (h + 2) ((h + 3) + (h + 3))
      (by
        rw [Nat.mul_succ (h + 2) 1, Nat.mul_one,
          Nat.add_comm 2 ((h + 2) + (h + 2)),
          Nat.add_assoc (h + 2) (h + 2) 2]
        show h + 2 + (h + 2 + 2) = Nat.succ (h + 2) + (h + 3)
        rw [Nat.succ_add (h + 2) (h + 3)]
        exact rfl))
    (eval_const 1 _) ?_
  rw [Nat.one_mul, Nat.mul_comm ((h + 3) + (h + 3)) (2 * (h + 3)),
    ground.mulAssoc 2 (h + 3) ((h + 3) + (h + 3)),
    Nat.left_distrib (h + 3) (h + 3) (h + 3),
    Nat.left_distrib 2 ((h + 3) * (h + 3)) ((h + 3) * (h + 3)),
    ground.fourMul ((h + 3) * (h + 3))]

/-- The dual pair's second row ties at the one shared value, the
first tie read across the table's shared entry. -/
theorem nodeDualB_read (h : Nat) :
    ((poly.eval (ground.getAt poly.pZero nodes 3).1
        (BPair.ofNat (h + 2))).mul (BPair.ofNat (2 * (h + 3)))).oneValue
      ((poly.eval (ground.getAt poly.pZero nodes 3).2
        (BPair.ofNat (h + 2))).mul
        (BPair.ofNat (c2hat.dfQ (channels.rowDualB (h + 3))))) := by
  rw [dfq_dualB h, ← dfq_dual h]
  exact nodeDual_read h

/-- The `ω₂ + ω₂*` middle value ties at the channel table's
Casimir column, from the width `d = h + 4`: `2 d_f - 2`. -/
theorem nodeOmega_read (h : Nat) :
    ((poly.eval (ground.getAt poly.pZero nodes 4).1
        (BPair.ofNat (h + 3))).mul (BPair.ofNat (2 * (h + 4)))).oneValue
      ((poly.eval (ground.getAt poly.pZero nodes 4).2
        (BPair.ofNat (h + 3))).mul
        (BPair.ofNat (c2hat.dfQ (channels.rowOmega (h + 4))))) := by
  rw [dfq_omega h]
  refine tie_read (u := (h + 4) + (h + 2)) (v := 1)
    (eval_twoVal 0 2 (h + 3) ((h + 4) + (h + 2))
      (by
        rw [Nat.zero_add, Nat.mul_succ (h + 3) 1, Nat.mul_one]
        show h + 3 + (h + 3) = Nat.succ (h + 3) + (h + 2)
        rw [Nat.succ_add (h + 3) (h + 2)]
        exact rfl))
    (eval_const 1 _) ?_
  rw [Nat.one_mul, Nat.mul_comm ((h + 4) + (h + 2)) (2 * (h + 4)),
    ground.mulAssoc 2 (h + 4) ((h + 4) + (h + 2)),
    Nat.left_distrib (h + 4) (h + 4) (h + 2),
    Nat.left_distrib 2 ((h + 4) * (h + 4)) ((h + 4) * (h + 2))]

/-- The cleared Lagrange interpolant at a node: the coefficient
list of `Π_{j ≠ k} (x - c_j)` over the polynomial-pair carrier at
the withdrawn node's co-list, constant first — the projection
onto one Casimir value a polynomial in `E_link`, entered cleared
at the node differences' product (`con:units`' Lagrange read;
`def:ground`'s homogeneity principle at the clearing scale). -/
def lagNum (k : Nat) : List poly.PPair :=
  (nodes.eraseIdx k).foldl (fun acc c =>
    poly.mulLO poly.ppairOps acc
      [poly.pMul lap.negP c, poly.pOne])
    [poly.pOne]

/-- A coefficient list's Horner read at a polynomial-pair
argument, the interpolant's own evaluation over the pair
carrier — `elim.evalLO` at the pair operations. -/
def lagEval (cs : List poly.PPair) (x : poly.PPair) : poly.PPair :=
  elim.evalLO poly.ppairOps cs x

/-- A coefficient list's Horner fold along the shared-link
Casimir: `p(Δ_L) s`, the constant's scale joined to the insertion
of the tail's fold (`prop:link`'s action), each level collected at
its key list (`states.collect`, `rem:kernel`'s projection — the
combination the occupancy family over the wirings, every fold
reading the collected form at the key folds' own values). -/
def lagApply (F : states.FList) :
    List poly.PPair → states.Comb → states.Comb
  | [], _ => []
  | c0 :: rest, s =>
    states.collect
      (lap.scaleComb c0 s ++ link.linkComb F (lagApply F rest s))

/-- The two-plaquette module pair's site, the `U` pair joined to
the `V` pair — `con:twoplaq`'s site extended at the second
variable's pair. -/
def siteQ12 : states.FList := twoplaq.extSite true twoplaq.siteQ1

/-- The module pair's state, `q₁ q₂` — the magnetic multiplication
of the first module's presentation at the second's pair
(`con:twoplaq`'s product read). -/
def q12 : states.Comb :=
  twoplaq.mulAdj twoplaq.phiAdj

/-- The projected two-plaquette state at a middle Casimir value:
the cleared interpolant's Horner fold at the module pair, the
`(adj, k, adj)`-network's presentation. -/
def chanState (k : Nat) : states.Comb :=
  lagApply siteQ12 (lagNum k) q12

/-- The clearing scale at a node, the node differences' product
`Π_{j ≠ k} (c_k - c_j)` over the pair carrier — the entry's own
scale, one value across it (`def:ground`'s homogeneity
principle). -/
def lagScale (k : Nat) : poly.PPair :=
  (nodes.eraseIdx k).foldl (fun acc c =>
    poly.pMul acc
      (poly.pAdd (ground.getAt poly.pZero nodes k)
        (poly.pMul lap.negP c)))
    poly.pOne

/-- The interpolant's node read: at its own node the cleared
interpolant's Horner read is the clearing scale, the node
differences' product, generic in the residue. -/
theorem lag_diag : ((List.range 5).all (fun k =>
    decide (genericlift.crossNull
      (lagEval (lagNum k) (ground.getAt poly.pZero nodes k))
      (lagScale k)))) = true := by decide +kernel

/-- The interpolant's off-node reads: at every withdrawn node the
cleared interpolant's Horner read is the pair carrier's null, one
factor of the product the node's own gap — the projection onto
one Casimir value reading every further value to the sum's unit,
generic in the residue. -/
theorem lag_null : ((List.range 5).all (fun k =>
    (List.range 5).all (fun j =>
      (j == k) || decide (genericlift.crossNull
        (lagEval (lagNum k) (ground.getAt poly.pZero nodes j))
        poly.pZero)))) = true := by decide +kernel

/-- The interpolant's node reads: at its own node the cleared
interpolant's Horner read sits off the pair carrier's null — the
clearing scale's occupancy at the channel distances' occupied
gaps, the scale's own read `lag_diag`. -/
theorem lag_occ : ((List.range 5).all (fun k =>
    !(decide (genericlift.crossNull
      (lagEval (lagNum k) (ground.getAt poly.pZero nodes k))
      poly.pZero)))) = true := by decide +kernel

/-- The within-pair middle matrix's entry at two middle Casimir
values: the projected state at the first against the magnetic
multiplication of the projected state at the second, the first
plaquette's `χ_X` at the extended site, the pairing `prop:wg`'s
— computable per entry by the `E_link` interpolant, the
tetrahedral list the node list's own square. -/
def kMid (k' k : Nat) : poly.PPair :=
  wg.pairFull siteQ12 (twoplaq.extSite false siteQ12)
    (chanState k') (twoplaq.mulAdj (chanState k))

end network
