import MassGap.Elim
/-!
`lem:sectorspan` — the sector's span read at the window matrices.

Multiplication by a window ground is adjoint to its involution
image's: the involution's matrix at the label index is the
transpose (the `statespace` convention, `prop:repring`'s fourth
read), so the pairing of an element against a multiplied one reads
the transposed multiplication against the element (`adj_read`,
both sides the one evaluation of the joined product), the
multiplied element's window the product window's at its own row
count (`prop:leastwindow`).

A ground's involution image is a ground (`invol_ground`): the
involution keeps the pencil, so the multiplication matrix commutes
with the level gap's, and the kernel read transports across that
commutation — the gap's action on the multiplied element is the
multiplication's action on the gap's, at the sum's unit
throughout.

The span read at a window and a ground is the product matrix's
rank at the window's dimension (`spanRead`, `def:elim`'s pivot
count at the stated matrix, its rows over the product window's
list and its columns over the window's), one decidable read.

A window element perpendicular to every word image sits in the
product matrix's kernel (`perp_kernel`): the perpendicularity
pairs the element against every row at the sum's unit, and the
product's every coordinate is that pairing's own read, the window
list's coordinate instance of the positive pairing's clause.  The
word sector's window projection fills the window exactly at the
span read (`fills` with `occupied_off`), `def:elim`'s kernel tier
the derivation: at the full rank the kernel list is vacant and the
vacant family's span reads the unit tail outright, so a
perpendicular element of the order is at the sum's unit; below the
full rank the kernel list's first member is a perpendicular
element off the unit family, its pivot-free coordinate the crossed
pivots' product, which sits off the sum's unit at every matrix.
-/

namespace sectorspan
open ground elim

/-- The span read: the product matrix's rank at the window's
dimension, `def:elim`'s pivot count at the stated matrix, the rows
over the product window's list at the window's width. -/
def spanRead (n : Nat) (S : Mat) : Prop :=
  rowsLen n S ∧ elim.rank S = n

instance (n : Nat) (S : Mat) : Decidable (spanRead n S) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The adjoint display: the pairing against a multiplied element
reads the transposed multiplication's own pairing, the transpose
the involution image's matrix at the label index, the multiplied
element at the product window's row count. -/
theorem adj_read (m n : Nat) (P : Mat) (hPl : P.length = m)
    (hPr : rowsLen n P) (w x : List BPair) (hw : w.length = m)
    (hx : x.length = n) :
    (dotP w (matVec P x)).oneValue
      (dotP (matVec (transposeM P) w) x) := by
  rw [dotP_comm w (matVec P x),
    dotP_comm (matVec (transposeM P) w) x]
  exact dotP_matVec_transpose n P x w hPr hx (hw.trans hPl.symm)

/-- A ground's involution image is a ground: at the two matrices'
commutation the gap's action on the multiplied element is the
multiplication's on the gap's, and the kernel read transports
across it. -/
theorem invol_ground (n : Nat) (Et J : Mat) (hEl : Et.length = n)
    (hEr : rowsLen n Et) (hJl : J.length = n) (hJr : rowsLen n J)
    (hcomm : matOneValue (matMul Et J) (matMul J Et))
    (psi : List BPair) (hp : psi.length = n)
    (hker : poly.unitTail (matVec Et psi)) :
    poly.unitTail (matVec Et (matVec J psi)) := by
  have hEJ : rowsLen J.length Et := by
    rw [hJl]
    exact hEr
  have hJE : rowsLen Et.length J := by
    rw [hEl]
    exact hJr
  have h1 : poly.oneValue (matVec Et (matVec J psi))
      (matVec (matMul Et J) psi) :=
    matVec_comp Et J psi n hJr hp hEJ
  have h2 : poly.oneValue (matVec (matMul Et J) psi)
      (matVec (matMul J Et) psi) :=
    matVec_matOne (matMul Et J) (matMul J Et) psi hcomm
  have h3 : poly.oneValue (matVec J (matVec Et psi))
      (matVec (matMul J Et) psi) :=
    matVec_comp J Et psi n hEr hp hJE
  exact poly.oneValue_unitTail
    (poly.oneValue_trans h1
      (poly.oneValue_trans h2 (poly.oneValue_symm h3)))
    (matVec_null J (matVec Et psi) hker)

/-- The perpendicular element sits in the product matrix's kernel:
the element pairs every word image at the sum's unit, and the
product's every coordinate is that pairing's own read — the window
list's coordinate instance of the positive pairing's clause. -/
theorem perp_kernel (S : Mat) (v : List BPair)
    (hp : ∀ i, i < S.length →
      (dotP v (ground.getAt ([] : List BPair) S i)).oneValue
        BPair.unit) :
    poly.unitTail (matVec S v) := by
  refine elim.unitTail_of_getAt (matVec S v) ?_
  intro i hi
  rw [show (matVec S v).length = S.length from ground.length_map _ S]
    at hi
  rw [show matVec S v = S.map (fun r => dotN r v) from rfl,
    ground.getAt_map ([] : List BPair) BPair.unit _ S i hi]
  refine BPair.oneValue_trans (dotN_read _ v) ?_
  rw [dotP_comm (ground.getAt ([] : List BPair) S i) v]
  exact hp i hi

/-- At the span read the projection fills the window exactly: a
window element perpendicular to every word image sits in the
product matrix's kernel, the kernel list is vacant at the full
rank, and the vacant family's span reads the unit tail, so the
element is at the sum's unit throughout. -/
theorem fills (n : Nat) (S : Mat) (hsr : spanRead n S)
    (v : List BPair) (hv : v.length = n)
    (hp : ∀ i, i < S.length →
      (dotP v (ground.getAt ([] : List BPair) S i)).oneValue
        BPair.unit) :
    poly.unitTail v := by
  obtain ⟨hrows, hr⟩ := hsr
  have hperp : poly.unitTail (matVec S v) := perp_kernel S v hp
  have hlen : (kernelList n S).length + rank S = n :=
    kernelList_length n S hrows
  rw [hr] at hlen
  have hz : (kernelList n S).length = 0 :=
    ground.addCancelR n (hlen.trans (Nat.zero_add n).symm)
  have hnil : kernelList n S = [] :=
    ground.nil_of_length_zero (kernelList n S) hz
  have hspan := kernelList_span n S hrows v hv hperp
  rw [hnil] at hspan
  exact spanRel_nil_unit n v hspan

/-- Below the span read the projection leaves the window: the
kernel list's first member is a perpendicular element of the
order whose pivot-free coordinate is the crossed pivots' product,
off the sum's unit, so the member is off the unit family. -/
theorem occupied_off (n : Nat) (S : Mat) (hrows : rowsLen n S)
    (hr : elim.rank S < n) :
    ∃ v : List BPair, v.length = n
      ∧ poly.unitTail (matVec S v) ∧ ¬ poly.unitTail v := by
  have hlen : (kernelList n S).length + rank S = n :=
    kernelList_length n S hrows
  have hpos : 0 < (kernelList n S).length := by
    cases hk : (kernelList n S).length with
    | zero =>
      rw [hk, Nat.zero_add] at hlen
      refine absurd hr ?_
      rw [hlen]
      exact Nat.lt_irrefl n
    | succ k => exact Nat.succ_pos k
  refine ⟨ground.getAt [] (kernelList n S) 0, ?_, ?_, ?_⟩
  · exact rowsLen_getAt (kernelList n S) 0
      (kernelList_rowsLen n S) hpos
  · exact kernelList_members n S hrows 0 hpos
  · intro hu
    exact pivotProd_off S
      (BPair.oneValue_trans
        (BPair.oneValue_symm (kernelList_coords n S hrows 0 hpos).1)
        (poly.getAt_unitTail hu
          (ground.getAt 0 (freeCols n S) 0)))

end sectorspan
