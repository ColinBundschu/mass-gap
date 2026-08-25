import MassGap.Fiberdec
import MassGap.Form
/-!
`thm:restoration`, first tier — the signed coordinate
permutations' action at the torus family (`con:lattice`'s field).
A member of `B_d` is a permutation `p` of the directions with a
flip family `f`, and it acts on the window's keys through the
site map (`bdSite`, the digits carried to the permuted directions
with a flipped direction's digit read at its complement to the
side) and the link map (`bdLink`, the key `(direction, site)` at
the permuted direction's own, a flipped direction's link re-keyed
at the backward step so that its traversal reverses).  The
reversal family (`bdRev`) reads which links the member traverses
backwards, and the index action is `fiberdec.dualConf` at this
map and family — the labels dualized exactly at the reversed
traversals, the orientation reversal of `con:lattice`'s field at
the theorem's own reading that a signed permutation reverses link
orientations and so dualizes labels.

The index-level reads are the three the theorem's `E`- and
`M`-fix sentences consume (`fiberdec.dualContentFixed`,
`dualOccFixed`, `dualIdxFixed` at this member's map and reversal
family, the translation's own reads their vacant instances): the
content is fixed at the action, the electric fold blind to the
dualization at the interface's Casimir read
(`fusion.casDualLaw`); the occupancy is fixed, the vertex data
transported along the vertex permutation the link map induces
with the incoming links' dualization reading the reversal; and
the index maps within itself.  The link map's further reads are
the translation's own family at this map — the permutation read
with its witness, and the conjugation of a direction's
translation into the permuted direction's own
(`fiberdec.intertwineRead`), a flip carrying a translation to its
inverse at the backward step — with the plaquette set read at the
boundary field's own cyclic words (`bdPlaqRead` over `ground.rotAt`, `revWord`, `cycEq` and `moveWord`): every boundary's image word,
its traversal bits carried across the reversal family, is a
stored plaquette's cyclic word, a rotation joining it to the word
or to its reversal.

The second tier is the matrix the theorem's congruence sentence
reads at, and the momentum transform's carrier.  The index action
enters as a matrix on a stated window index
(`fiberdec.dualMat`, the unit line at its head over the
relabeling's indicator rows, the translation's own matrix its
vacant instance) — so that a member's congruence on the window's electric
matrix is the theorem's `E`-fix read entrywise, and a window whose
multiplicity reads one carries the ground line at `thm:SO`'s
character clause.  The congruence sentence's determinant read sits
beside it: `relabelRead` is the moved pencil's entrywise reading —
every entry the source's at the moved row and column keys, with
`relabelRead_at` its extraction at a row and a column key — and
`relabel_det` reads the two determinants at one value through
`def:elim`'s exchanged reads, the assignment fold reindexed along
the relabeling with the row and the column exchanges composing at
an even join.  The transform is the read family at the
translate monomials: the keys of one direction row below the side
(`places.keyBox` at the range alphabet), the box of per-argument
key lists at a stated argument count (`argBox`, `ground.keyBox`'s
list-alphabet instance), and the moved key at a signed member
(`bdKey`) — the exponent read off the permuted direction, a
flipped direction's at its complement to the side, the wrap's own
read at `lem:fiberdec`'s `T^L = 1`.  The theorem's sentence that a
lattice symmetry moves a translate read to the moved keys' own is
`transformMoved`, the moved family reading the family at every key
of the box, with `transformFixed` its diagonal at one member.
-/

namespace restoration
open ground lattice fusion carrier fiberdec

/-! The signed coordinate permutations at the torus window: the
site map, the link map with its reversal family, and the index
action they carry. -/

/-- The site's digits carried to the permuted directions, a
flipped direction's digit at its complement to the side, the
origin fixed. -/
def bdSite (d L : Nat) (p : Nat → Nat) (f : Nat → Bool) (s : Nat) : Nat :=
  (List.range d).foldl (fun acc e =>
    acc + (if f e then (L - fiberdec.digitAt L e s) % L
      else fiberdec.digitAt L e s) * L ^ (p e)) 0

/-- The link at `(direction, site)` to the permuted direction at
the moved site; a flipped direction's link re-keyed at the
backward step, its traversal reversed (the orientation reversal of
`con:lattice`'s field). -/
def bdLink (d L : Nat) (p : Nat → Nat) (f : Nat → Bool) (l : Nat) : Nat :=
  if f (l / L ^ d) then
    (p (l / L ^ d)) * L ^ d
      + fiberdec.shiftSiteInv L (p (l / L ^ d)) (bdSite d L p f (l % L ^ d))
  else (p (l / L ^ d)) * L ^ d + bdSite d L p f (l % L ^ d)

/-- The reversal family, the flipped directions' links. -/
def bdRev (d L : Nat) (f : Nat → Bool) (l : Nat) : Bool := f (l / L ^ d)

/-- The boundary traversed backwards: the word reversed with every
traversal bit flipped, the field's orientation reversal. -/
def revWord (w : List (Nat × Bool)) : List (Nat × Bool) :=
  (w.reverse).map (fun e => (e.1, !e.2))

/-- Two boundary words one plaquette reading: the words equal, or
a rotation joining the first to the second or to its reversal —
the cyclic word at either traversal. -/
def cycEq (w w' : List (Nat × Bool)) : Bool :=
  w == w'
    || (List.range w'.length).any (fun k => w == ground.rotAt k w')
    || (List.range w'.length).any (fun k => w == ground.rotAt k (revWord w'))

/-- The moved boundary word: each link at its image key with the
traversal bit carried across the reversal family. -/
def moveWord (t : Nat → Nat) (rev : Nat → Bool)
    (w : List (Nat × Bool)) : List (Nat × Bool) :=
  w.map (fun e => (t e.1, xor e.2 (rev e.1)))

/-- The plaquette set moved into itself at the cyclic reading:
every boundary's image word is a stored plaquette's own cyclic
word (`con:lattice`'s field, the signed member permuting the
plaquette set with the orientation reversal). -/
def bdPlaqRead (R : Region) (t : Nat → Nat) (rev : Nat → Bool) :
    Prop :=
  (R.plaqs.all (fun w =>
    R.plaqs.any (fun w' => cycEq (moveWord t rev w) w'))) = true

instance (R : Region) (t : Nat → Nat) (rev : Nat → Bool) :
    Decidable (bdPlaqRead R t rev) :=
  inferInstanceAs (Decidable (_ = _))

/-- The relabeled window pencil at a stated permutation: every
entry the source's at the moved row and column keys, the
relabeling's own read. -/
def relabelRead (n : Nat) (M M' : elim.Mat) (q : List Nat) : Prop :=
  ((List.range n).all (fun i =>
    let row' := ground.getAt [] M' i
    let row := ground.getAt [] M (ground.getAt 0 q i)
    (List.range n).all (fun j =>
      decide ((ground.getAt BPair.unit row' j).oneValue
        (ground.getAt BPair.unit row (ground.getAt 0 q j)))))) = true

instance (n : Nat) (M M' : elim.Mat) (q : List Nat) :
    Decidable (relabelRead n M M' q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The relabeling read at a row and a column key below the
count. -/
theorem relabelRead_at (n : Nat) (M M' : elim.Mat) (q : List Nat)
    (h : relabelRead n M M' q) (i j : Nat) (hi : i < n) (hj : j < n) :
    (ground.getAt BPair.unit (ground.getAt [] M' i) j).oneValue
      (ground.getAt BPair.unit
        (ground.getAt [] M (ground.getAt 0 q i))
        (ground.getAt 0 q j)) :=
  of_decide_eq_true
    (ground.all_range_read n (ground.all_range_read n h i hi) j hj)

/-- The relabeled pencil's determinant reads the source's, the
theorem's determinant agreement at the window level, the
characteristic polynomials' coefficientwise read
`split.pminor_reindex`'s. -/
theorem relabel_det (n : Nat) (M M' : elim.Mat) (q : List Nat)
    (hq : 0 < ground.countOf q
      (places.monomialsAt (List.replicate n 1)))
    (hM : M.length = n) (hM' : M'.length = n)
    (h : relabelRead n M M' q) :
    (elim.detL M').oneValue (elim.detL M) :=
  elim.detL_reindex n M M' q hq hM hM'
    (fun i j hi hj => relabelRead_at n M M' q h i j hi hj)

/-- The per-argument key lists, the box at a stated argument
count: the key lists' own box over the one-direction rows
(`ground.keyBox` at `places.keyBox`'s alphabet). -/
def argBox (d L m : Nat) : List (List (List Nat)) :=
  ground.keyBox m (places.keyBox d L)

/-- The moved translate key at a signed member, read at the
member's direction witness (the backward map, `permRead`'s own
convention): the exponent read off the permuted direction, a
flipped direction's at its complement to the side, the wrap's own
read (`thm:restoration`'s momentum transform, the flip reading a
key to its balance partner at the wrap).  The witness convention
is the conjugation's own tie (`keyMoveRead`): the member's link
map carries a composite shift to the moved key's composite. -/
def bdKey (d L : Nat) (p' : Nat → Nat) (f : Nat → Bool)
    (ks : List Nat) : List Nat :=
  (List.range d).map (fun e' =>
    if f (p' e') then (L - ground.getAt 0 ks (p' e')) % L
    else ground.getAt 0 ks (p' e'))

/-- The moved key's conjugation tie: the member's link map carries
each key list's composite shift to the moved key's own, the read
over the key rows — the witness convention's one discriminating
read. -/
def keyMoveRead (R : Region) (d L : Nat) (g : Nat → Nat)
    (p' : Nat → Nat) (f : Nat → Bool) : Prop :=
  ((places.keyBox d L).all (fun ks =>
    decide (fiberdec.intertwineRead R g (fiberdec.compShift d L ks)
      (fiberdec.compShift d L (bdKey d L p' f ks))))) = true

instance (R : Region) (d L : Nat) (g p' : Nat → Nat)
    (f : Nat → Bool) : Decidable (keyMoveRead R d L g p' f) :=
  inferInstanceAs (Decidable (_ = _))

/-- A lattice symmetry moves a translate read to the moved keys'
own: the moved family reads the family at every key of the box,
the transform's coefficient identities. -/
def transformMoved (d L m : Nat) (w w' : List (List Nat) → BPair)
    (p' : Nat → Nat) (f : Nat → Bool) : Prop :=
  ((argBox d L m).all (fun ks =>
    decide (BPair.oneValue (w' (ks.map (bdKey d L p' f))) (w ks)))) = true

instance (d L m : Nat) (w w' : List (List Nat) → BPair)
    (p' : Nat → Nat) (f : Nat → Bool) :
    Decidable (transformMoved d L m w w' p' f) :=
  inferInstanceAs (Decidable (_ = _))

/-- The transform fixed at a member: the one family at its own
moved keys, `transformMoved`'s diagonal. -/
def transformFixed (d L m : Nat) (w : List (List Nat) → BPair)
    (p' : Nat → Nat) (f : Nat → Bool) : Prop :=
  transformMoved d L m w w p' f

instance (d L m : Nat) (w : List (List Nat) → BPair)
    (p' : Nat → Nat) (f : Nat → Bool) :
    Decidable (transformFixed d L m w p' f) :=
  inferInstanceAs (Decidable (transformMoved d L m w w p' f))

/-- The self-dual theta at the label calculus: the complement
arithmetic reads the adjoint back (`prop:form`'s `dualL_theta`),
the interface law at every fundamental count from two. -/
theorem thetaSelfDual_all (d : Nat) (hd : 2 ≤ d) :
    fusion.thetaSelfDual (fusion.dataA d) := by
  show (fusion.dataA d).eqL
    ((fusion.dataA d).dual (fusion.dataA d).theta)
    (fusion.dataA d).theta = true
  rw [show (fusion.dataA d).dual (fusion.dataA d).theta
      = (fusion.dataA d).theta from form.dualL_theta d hd]
  exact (fusion.dataA d).eqLRefl _

/-! The invariant half's carrier: the momenta as formal
coordinates.  A degree-`D` monomial at `m` arguments and `d`
directions is a grid — one exponent list of length `d` per
argument, the rows' totals summing to `D` — and `momBox`
enumerates them, exactly at those three reads (`momBox_reads` the
members' own, `mem_momBox` the converse).  Two moves act on a
coefficient family `c` over the grids: a reflection at a
coordinate `i` carries a monomial whose `i`-count (`dirTot`) is
odd to its balance partner, so an invariant family's coefficient
there is the sum's unit; a transposition of two coordinates
(`swapDirs`, the entries `i` and `j` exchanged in every row)
moves the grid, and an invariant family's coefficients agree
across the move.  `bdInvAt` is the two moves' joint read at a
stated argument count, direction count and degree, with
`bdInv_vanish` and `bdInv_swap` its two extractions at a member
of the box.  The families the theorem displays are the pairwise
inner products (`ipGrid`, `ipFam`), the diagonal quartic
(`quGrid`, `quFam`), and a product of two inner products
(`prodIP`), whose coefficient at a grid counts the splittings of
that grid into one monomial from each factor across the
monomials' product (`addG`, the grids' entrywise join). -/

/-- The momentum grids at an argument count, a direction count and
a degree: one exponent list per argument, the per-argument degrees
summing to the stated total — `thm:restoration`'s formal
coordinates, one matched list per argument. -/
def momBox : Nat → Nat → Nat → List (List (List Nat))
  | 0, _, 0 => [[]]
  | 0, _, _ + 1 => []
  | m + 1, d, D => (List.range (D + 1)).flatMap (fun j =>
      (momBox m d (D - j)).flatMap (fun g =>
        (places.allContents d j).map (fun row => row :: g)))

/-- A grid's total degree along one coordinate: the exponents at
that coordinate summed over the arguments. -/
def dirTot (i : Nat) (g : List (List Nat)) : Nat :=
  ground.sumNat (g.map (fun row => ground.getAt 0 row i))

/-- The coordinate transposition's action on a grid: the entries
at the two coordinates exchanged in every argument's row. -/
def swapDirs (i j : Nat) (g : List (List Nat)) : List (List Nat) :=
  g.map (places.swapPair i j)

/-- The two settling moves' read at a coefficient family over the
grids of a stated argument count, direction count and degree: at
every grid, a coordinate of odd total forces the coefficient to
the sum's unit (the reflection), and the coefficient at a
transposed grid is the coefficient's own value (the
transposition) — `thm:restoration`'s invariance. -/
def bdInvAt (m d D : Nat) (c : List (List Nat) → BPair) : Prop :=
  ((momBox m d D).all (fun g =>
    ((List.range d).all (fun i =>
      dirTot i g % 2 == 0
        || decide ((c g).oneValue BPair.unit)))
    && ((List.range d).all (fun i => (List.range d).all (fun j =>
      !decide (i < j)
        || decide ((c (swapDirs i j g)).oneValue (c g))))))) = true

instance (m d D : Nat) (c : List (List Nat) → BPair) :
    Decidable (bdInvAt m d D c) :=
  inferInstanceAs (Decidable (_ = _))

/-- The grids' entrywise join, the monomials' product: exponents
add at every argument and coordinate. -/
def addG (g h : List (List Nat)) : List (List Nat) :=
  List.zipWith (List.zipWith Nat.add) g h

/-- The monomial of the pairwise inner product `K^(r)·K^(s)` at a
coordinate: the argument `r`'s and the argument `s`'s exponent at
that coordinate raised by one each, the diagonal `r = s` reading
the square. -/
def ipGrid (m d r s i : Nat) : List (List Nat) :=
  ground.matOf m d (fun t k =>
    (if t == r && k == i then 1 else 0)
      + (if t == s && k == i then 1 else 0))

/-- The pairwise inner product's coefficient family: the unit
occupancy at each of its own monomials, the sum's unit off
them. -/
def ipFam (m d r s : Nat) (g : List (List Nat)) : BPair :=
  if (List.range d).any (fun i => g == ipGrid m d r s i)
  then BPair.ofNat 1 else BPair.unit

/-- The diagonal quartic's monomial at a coordinate: the argument
`r`'s exponent at that coordinate raised by four. -/
def quGrid (m d r i : Nat) : List (List Nat) :=
  ground.matOf m d (fun t k =>
    if t == r && k == i then 4 else 0)

/-- The diagonal quartic's coefficient family: the unit occupancy
at each of its own monomials, the sum's unit off them. -/
def quFam (m d r : Nat) (g : List (List Nat)) : BPair :=
  if (List.range d).any (fun i => g == quGrid m d r i)
  then BPair.ofNat 1 else BPair.unit

/-- The cross monomial at one argument's first two coordinates
paired: the two squares' product, `K_i^2K_j^2`'s grid
(`thm:restoration`'s degree-four clause). -/
def crossG (d i j : Nat) : List (List Nat) :=
  addG (ipGrid 1 d 0 0 i) (ipGrid 1 d 0 0 j)

/-- Two inner products' product family: the coefficient at a grid
is the splitting count, the pairs of coordinates whose two
monomials join entrywise to that grid. -/
def prodIP (m d r s t u : Nat) (g : List (List Nat)) : BPair :=
  BPair.ofNat (ground.sumNat ((List.range d).flatMap (fun i =>
    (List.range d).map (fun j =>
      if g == addG (ipGrid m d r s i) (ipGrid m d t u j)
      then 1 else 0))))

/-- The grid enumeration's members carry the stated argument
count, the stated direction count at every row, and the stated
total degree. -/
theorem momBox_reads : ∀ (m d D : Nat) (g : List (List Nat)),
    0 < ground.countOf g (momBox m d D) →
    g.length = m ∧ (g.all (fun row => row.length == d)) = true
      ∧ ground.sumNat (g.map ground.sumNat) = D
  | 0, d, 0, g, h => by
    by_cases hg : g = []
    · rw [hg]
      exact ⟨rfl, rfl, rfl⟩
    · have h0 : ground.countOf g (momBox 0 d 0) = 0 :=
        ground.countOf_head_ne hg []
      rw [h0] at h
      exact absurd h (Nat.lt_irrefl 0)
  | 0, _, _ + 1, _, h => absurd h (Nat.lt_irrefl 0)
  | m + 1, d, D, g, h => by
    have hmem : g ∈ (List.range (D + 1)).flatMap (fun j =>
        (momBox m d (D - j)).flatMap (fun g =>
          (places.allContents d j).map (fun row => row :: g))) :=
      ground.mem_of_countOf_pos g _ h
    match ground.mem_flatMap_of _ (List.range (D + 1)) g hmem with
    | ⟨jj, hjm, hj2⟩ =>
      match ground.mem_flatMap_of _ (momBox m d (D - jj)) g hj2 with
      | ⟨t, htm, hr2⟩ =>
        match ground.mem_map_of _ (places.allContents d jj) g hr2 with
        | ⟨row, hrm, hcons⟩ =>
          have hjD : jj ≤ D := Nat.le_of_lt_succ
            (ground.ltOfMemRange hjm)
          have hrow := places.allContents_reads d jj row
            (ground.countOf_pos_of_mem hrm)
          have hIH := momBox_reads m d (D - jj) t
            (ground.countOf_pos_of_mem htm)
          refine ⟨?_, ?_, ?_⟩
          · rw [← hcons]
            show t.length + 1 = m + 1
            rw [hIH.1]
          · rw [← hcons]
            show ((row.length == d)
              && t.all (fun row => row.length == d)) = true
            refine ground.andIntroB ?_ hIH.2.1
            rw [hrow.1]
            exact ground.eqBeqOf rfl
          · rw [← hcons]
            show ground.sumNat row
              + ground.sumNat (t.map ground.sumNat) = D
            rw [hrow.2, hIH.2.2, Nat.add_comm jj (D - jj)]
            exact ground.subAdd hjD

/-- The grid enumeration is complete: a list of exponent rows at
the stated argument count and direction count is a member of the
box at its own total degree. -/
theorem mem_momBox : ∀ (m d D : Nat) (g : List (List Nat)),
    g.length = m → (g.all (fun row => row.length == d)) = true →
    ground.sumNat (g.map ground.sumNat) = D →
    0 < ground.countOf g (momBox m d D)
  | 0, d, D, [], _, _, hs => by
    have hD : D = 0 := Eq.symm hs
    rw [hD]
    show 0 < ground.countOf ([] : List (List Nat))
      (([] : List (List Nat)) :: ([] : List (List (List Nat))))
    rw [ground.countOf_head ([] : List (List Nat))
      ([] : List (List (List Nat)))]
    exact Nat.succ_pos _
  | 0, _, _, _ :: _, hl, _, _ => Nat.noConfusion hl
  | _ + 1, _, _, [], hl, _, _ => Nat.noConfusion hl
  | m + 1, d, D, row :: t, hl, ha, hs => by
    have hsplit := ground.andSplitB (show ((row.length == d)
      && t.all (fun row => row.length == d)) = true from ha)
    have hrl : row.length = d := ground.beqEqOf hsplit.1
    have hsum : ground.sumNat row
        + ground.sumNat (t.map ground.sumNat) = D := hs
    have hjD : ground.sumNat row ≤ D := Nat.le.intro hsum
    have hrest : ground.sumNat (t.map ground.sumNat)
        = D - ground.sumNat row := by
      rw [← hsum, ground.addSubSelfL]
    have hfold : ground.sumNat row = row.foldl (fun a b => a + b) 0 := by
      show ground.famFold Nat.add 0 (fun x => x) row
        = row.foldl (fun a b => a + b) 0
      rw [ground.foldlSum (fun b => b) row 0, Nat.zero_add]
    have hmemrow : row ∈ places.allContents d (ground.sumNat row) := by
      rw [hfold]
      exact places.mem_allContents d row hrl
    have hmemt : t ∈ momBox m d (D - ground.sumNat row) :=
      ground.mem_of_countOf_pos t _
        (mem_momBox m d (D - ground.sumNat row) t
          (Nat.succ.inj hl) hsplit.2 hrest)
    refine ground.countOf_pos_of_mem ?_
    show (row :: t) ∈ (List.range (D + 1)).flatMap (fun j =>
      (momBox m d (D - j)).flatMap (fun g =>
        (places.allContents d j).map (fun row => row :: g)))
    refine ground.mem_flatMap_to _ (a := ground.sumNat row)
      (ground.memRange (Nat.lt_succ_of_le hjD)) ?_
    show (row :: t) ∈ (momBox m d (D - ground.sumNat row)).flatMap
      (fun g => (places.allContents d (ground.sumNat row)).map
        (fun row => row :: g))
    refine ground.mem_flatMap_to _ (a := t) hmemt ?_
    show (row :: t) ∈ (places.allContents d (ground.sumNat row)).map
      (fun row => row :: t)
    exact ground.mem_map_to (fun row => row :: t) hmemrow

/-- The reflection clause extracted: at a member of the box with
an odd total along a coordinate, an invariant family's coefficient
is the sum's unit — `thm:restoration`'s balance-partner reading. -/
theorem bdInv_vanish (m d D : Nat) (c : List (List Nat) → BPair)
    (h : bdInvAt m d D c) (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox m d D)) (i : Nat) (hi : i < d)
    (hodd : dirTot i g % 2 = 1) : (c g).oneValue BPair.unit := by
  have hread := ground.all_of_mem _ (momBox m d D) h g
    (ground.mem_of_countOf_pos g _ hg)
  have hs := ground.andSplitB hread
  have h1 := ground.all_range_read d hs.1 i hi
  rw [hodd] at h1
  have h2 : decide ((c g).oneValue BPair.unit) = true := h1
  exact of_decide_eq_true h2

/-- The transposition clause extracted: at a member of the box, an
invariant family reads one value at the grid and at the grid moved
by a transposition of two coordinates. -/
theorem bdInv_swap (m d D : Nat) (c : List (List Nat) → BPair)
    (h : bdInvAt m d D c) (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox m d D)) (i j : Nat)
    (hij : i < j) (hj : j < d) :
    (c (swapDirs i j g)).oneValue (c g) := by
  have hread := ground.all_of_mem _ (momBox m d D) h g
    (ground.mem_of_countOf_pos g _ hg)
  have hs := ground.andSplitB hread
  have h1 := ground.all_range_read d hs.2 i (Nat.lt_trans hij hj)
  have h2 := ground.all_range_read d h1 j hj
  rw [decide_eq_true hij] at h2
  have h3 : decide ((c (swapDirs i j g)).oneValue (c g)) = true := h2
  exact of_decide_eq_true h3

/-! The named families' invariance: the pairwise inner product, the
diagonal quartic and a product of two inner products each read the
two settling moves at every grid of their own degree's box
(`thm:restoration`'s displayed coefficient families).  The
mechanism is one shape.  A grid built from an entry formula over
the two ranges (`ground.matOf`) carries the transposition by reindexing
the formula's coordinate along `ground.swapIx` (`matOf_swapDirs`),
so each named monomial moves to the named monomial at the
transposed coordinate and each family's matching test is blind to
the move; and the same formula reads the coordinate totals
(`dirTot_matOf`) and the total degree (`deg_matOf`) off one
indicator sum, so a matched grid's total along a coordinate is
either nothing or the grid's own degree, which the box pins. -/

/-- A conjoined test's read splits at its second member. -/
private theorem ite_and_right (b1 b2 : Bool) (a : Nat) :
    (if b1 && b2 then a else 0)
      = if b2 then (if b1 then a else 0) else 0 := by
  cases b1 <;> cases b2 <;> rfl

/-- Two tests each holding the other are one test. -/
private theorem boolEqOfImp : ∀ {p q : Bool}, (p = true → q = true) →
    (q = true → p = true) → p = q
  | true, true, _, _ => rfl
  | true, false, h1, _ => Bool.noConfusion (h1 rfl)
  | false, true, _, h2 => Bool.noConfusion (h2 rfl)
  | false, false, _, _ => rfl

/-- A refused occupancy fold reads its every key refused. -/
private theorem any_range_false (d : Nat) (f : Nat → Bool)
    (h : ((List.range d).any f) = false) (i : Nat) (hi : i < d) :
    f i = false := by
  have hnot := ground.all_range_read d
    (ground.all_not_of_any_false f (List.range d) h) i hi
  cases hf : f i with
  | false => rfl
  | true =>
    rw [hf] at hnot
    exact Bool.noConfusion hnot

/-- A family vacant at every member totals to nothing. -/
private theorem sumNat_map_zero_mem {α : Type} (f : α → Nat) :
    ∀ l : List α, (∀ x, x ∈ l → f x = 0) →
      ground.sumNat (l.map f) = 0
  | [], _ => rfl
  | a :: t, h => by
    show f a + ground.sumNat (t.map f) = 0
    rw [h a (List.Mem.head t),
      sumNat_map_zero_mem f t (fun x hx => h x (List.Mem.tail a hx))]

/-- The one-hot family's total over the key range: the stated value
at a key below the count, nothing beyond it. -/
private theorem sumNat_ind_range (r a m : Nat) :
    ground.sumNat ((List.range m).map (fun t => if t == r then a else 0))
      = if r < m then a else 0 := by
  rw [ground.sumMap (fun t => if t == r then a else 0) (List.range m),
    ground.famFold_congr_all Nat.add 0
      (fun t => if t == r then a else 0)
      (fun t => if r == t then a else 0)
      (fun t => by rw [ground.beqSymm t r]) (List.range m)]
  by_cases h : r < m
  · rw [if_pos h]
    exact ground.famFold_pickBeqRange r a m h
  · rw [if_neg h]
    refine ground.famFold_rangeZero _ m (fun x hx => ?_)
    rw [ground.neBeqOf (fun he : r = x => h (he ▸ hx))]
    exact rfl

/-- The key range's total is blind to a transposition of two
keys. -/
private theorem sumNat_range_swapIx (d a b : Nat) (ha : a < d) (hb : b < d)
    (h : Nat → Nat) :
    ground.sumNat ((List.range d).map h)
      = ground.sumNat ((List.range d).map
          (fun x => h (ground.swapIx a b x))) := by
  rw [ground.sumMap h (List.range d),
    ground.sumMap (fun x => h (ground.swapIx a b x)) (List.range d)]
  exact ground.famFold_reindex Nat.add 0 Nat.add_comm Nat.add_assoc h
    (ground.distinctList_range d)
    (fun x _ => ground.swapIx_invol a b x)
    (fun x _ => ground.swapIx_invol a b x)
    (fun x hx => ground.countOf_pos_of_mem (ground.memRange
      (ground.swapIx_lt ha hb x (ground.ltOfMem hx))))
    (fun x hx => ground.countOf_pos_of_mem (ground.memRange
      (ground.swapIx_lt ha hb x (ground.ltOfMem hx))))

/-- A keyed union's total is the per-key totals' own. -/
private theorem sumNat_flatMap {α : Type} (G : α → List Nat)
    (l : List α) :
    ground.sumNat (l.flatMap G)
      = ground.sumNat (l.map (fun x => ground.sumNat (G x))) :=
  (ground.famFold_flatMap (fun x => x) G l).trans
    (ground.famFold_map Nat.add 0 (fun x => x)
      (fun x => ground.sumNat (G x)) l).symm

/-- A grid comparison's truth is the grids' equality, the nested
list carrier's own decidable read. -/
private theorem gridBeqEq :
    ∀ {u w : List (List Nat)}, (u == w) = true → u = w
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | a :: u, b :: w, h => by
    have hs := ground.andSplitB
      (show ((a == b) && ((u : List (List Nat)) == w)) = true from h)
    rw [ground.listBeqEq hs.1, gridBeqEq hs.2]

/-- A grid's comparison against itself is true. -/
private theorem gridEqBeq : ∀ u : List (List Nat), (u == u) = true
  | [] => rfl
  | a :: u => by
    show ((a == a) && ((u : List (List Nat)) == u)) = true
    rw [ground.listEqBeq a, gridEqBeq u]
    rfl

/-- A row over the key range carries a transposition of two keys by
reindexing the read. -/
private theorem swapPair_map_range (d a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (f : Nat → Nat) :
    places.swapPair a b ((List.range d).map f)
      = (List.range d).map (fun k => f (ground.swapIx a b k)) := by
  have hlen : ((List.range d).map f).length = d := by
    rw [ground.length_map, ground.length_range]
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [places.length_swapPair, hlen, ground.length_map,
      ground.length_range]
  · intro p hp
    rw [places.length_swapPair, hlen] at hp
    rw [ground.getAt_map_range 0 (fun k => f (ground.swapIx a b k)) d p,
      if_pos hp]
    by_cases hpa : p = a
    · rw [hpa, places.getAt_swapPair_fst _ hab
        (by rw [hlen]; exact ha) (by rw [hlen]; exact hb),
        ground.getAt_map_range 0 f d b, if_pos hb, ground.swapIx_fst]
    · by_cases hpb : p = b
      · rw [hpb, places.getAt_swapPair_snd _ hab
          (by rw [hlen]; exact ha) (by rw [hlen]; exact hb),
          ground.getAt_map_range 0 f d a, if_pos ha,
          ground.swapIx_snd (fun he => hab he.symm)]
      · rw [places.getAt_swapPair_ne _ (by rw [hlen]; exact ha)
          (by rw [hlen]; exact hb) hpa hpb,
          ground.getAt_map_range 0 f d p, if_pos hp,
          ground.swapIx_off hpa hpb]

/-- The coordinate transposition moves a grid to the grid at the
reindexed entry formula. -/
private theorem matOf_swapDirs (m d a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (F : Nat → Nat → Nat) :
    swapDirs a b (ground.matOf m d F)
      = ground.matOf m d (fun t k => F t (ground.swapIx a b k)) := by
  show ((List.range m).map (fun t => (List.range d).map (F t))).map
      (places.swapPair a b)
    = (List.range m).map (fun t => (List.range d).map
        (fun k => F t (ground.swapIx a b k)))
  rw [ground.map_map]
  exact ground.map_congr_all _ _
    (fun t => swapPair_map_range d a b hab ha hb (F t)) (List.range m)

/-- The transposition is an involution on the grids. -/
private theorem swapDirs_swapDirs (a b : Nat) (g : List (List Nat)) :
    swapDirs a b (swapDirs a b g) = g := by
  show (g.map (places.swapPair a b)).map (places.swapPair a b) = g
  rw [ground.map_map, ground.map_congr_all _ (fun x => x)
    (fun x => places.swapPair_swapPair a b x) g, ground.map_id g]

/-- The grids' entrywise join at two entry formulas is the grid at
their pointwise sum. -/
private theorem addG_matOf (m d : Nat) (F G : Nat → Nat → Nat) :
    addG (ground.matOf m d F) (ground.matOf m d G)
      = ground.matOf m d (fun t k => F t k + G t k) := by
  show List.zipWith (List.zipWith Nat.add)
      ((List.range m).map (fun t => (List.range d).map (F t)))
      ((List.range m).map (fun t => (List.range d).map (G t)))
    = (List.range m).map (fun t => (List.range d).map
        (fun k => F t k + G t k))
  rw [ground.zipWith_map_map (List.zipWith Nat.add)
    (fun t => (List.range d).map (F t))
    (fun t => (List.range d).map (G t)) (List.range m)]
  exact ground.map_congr_all _ _
    (fun t => ground.zipWith_map_map Nat.add (F t) (G t) (List.range d))
    (List.range m)

/-- A grid's total along a coordinate is the entry formula's own
total at that coordinate. -/
private theorem dirTot_matOf (m d i : Nat) (hi : i < d)
    (F : Nat → Nat → Nat) :
    dirTot i (ground.matOf m d F)
      = ground.sumNat ((List.range m).map (fun t => F t i)) := by
  show ground.sumNat
      (((List.range m).map (fun t => (List.range d).map (F t))).map
        (fun row => ground.getAt 0 row i))
    = ground.sumNat ((List.range m).map (fun t => F t i))
  rw [ground.map_map]
  exact congrArg ground.sumNat (ground.map_congr_all _ _
    (fun t => by
      rw [ground.getAt_map_range 0 (F t) d i, if_pos hi])
    (List.range m))

/-- A grid's total degree is the entry formula's row totals'
own. -/
private theorem deg_matOf (m d : Nat) (F : Nat → Nat → Nat) :
    ground.sumNat ((ground.matOf m d F).map ground.sumNat)
      = ground.sumNat ((List.range m).map
          (fun t => ground.sumNat ((List.range d).map (F t)))) :=
  congrArg ground.sumNat
    (ground.map_map (fun t => (List.range d).map (F t)) ground.sumNat
      (List.range m))

/-- The pairwise inner product's entry formula. -/
private def ipEnt (r s c t k : Nat) : Nat :=
  (if t == r && k == c then 1 else 0)
    + (if t == s && k == c then 1 else 0)

/-- The pairwise inner product's monomial is the grid at its entry
formula. -/
private theorem ipGrid_matOf (m d r s c : Nat) :
    ipGrid m d r s c = ground.matOf m d (ipEnt r s c) := rfl

/-- The diagonal quartic's entry formula. -/
private def quEnt (r c t k : Nat) : Nat :=
  if t == r && k == c then 4 else 0

/-- The diagonal quartic's monomial is the grid at its entry
formula. -/
private theorem quGrid_matOf (m d r c : Nat) :
    quGrid m d r c = ground.matOf m d (quEnt r c) := rfl

/-- A transposition moves the matching coordinate across the
comparison. -/
private theorem beq_swapIx (a b k c : Nat) :
    ((ground.swapIx a b k == c) : Bool) = (k == ground.swapIx a b c) := by
  by_cases h : ground.swapIx a b k = c
  · rw [ground.eqBeqOf h, ground.eqBeqOf (show k = ground.swapIx a b c from
      by rw [← h, ground.swapIx_invol a b k])]
  · rw [ground.neBeqOf h, ground.neBeqOf
      (show ¬ k = ground.swapIx a b c from fun he =>
        h (by rw [he, ground.swapIx_invol a b c]))]

/-- The inner product's entry formula reindexes its coordinate
across a transposition. -/
private theorem ipEnt_swapIx (r s c a b t k : Nat) :
    ipEnt r s c t (ground.swapIx a b k)
      = ipEnt r s (ground.swapIx a b c) t k := by
  show (if t == r && ground.swapIx a b k == c then 1 else 0)
      + (if t == s && ground.swapIx a b k == c then 1 else 0)
    = (if t == r && k == ground.swapIx a b c then 1 else 0)
      + (if t == s && k == ground.swapIx a b c then 1 else 0)
  rw [beq_swapIx a b k c]

/-- The quartic's entry formula reindexes its coordinate across a
transposition. -/
private theorem quEnt_swapIx (r c a b t k : Nat) :
    quEnt r c t (ground.swapIx a b k) = quEnt r (ground.swapIx a b c) t k := by
  show (if t == r && ground.swapIx a b k == c then 4 else 0)
    = (if t == r && k == ground.swapIx a b c then 4 else 0)
  rw [beq_swapIx a b k c]

/-- The transposition carries an inner product's monomial to the
monomial at the transposed coordinate. -/
private theorem swapDirs_ipGrid (m d r s c a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) :
    swapDirs a b (ipGrid m d r s c)
      = ipGrid m d r s (ground.swapIx a b c) := by
  rw [ipGrid_matOf m d r s c,
    matOf_swapDirs m d a b hab ha hb (ipEnt r s c),
    ipGrid_matOf m d r s (ground.swapIx a b c)]
  exact ground.matOf_congr m d _ _ (fun t k _ _ => ipEnt_swapIx r s c a b t k)

/-- The transposition carries the quartic's monomial to the
monomial at the transposed coordinate. -/
private theorem swapDirs_quGrid (m d r c a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) :
    swapDirs a b (quGrid m d r c)
      = quGrid m d r (ground.swapIx a b c) := by
  rw [quGrid_matOf m d r c,
    matOf_swapDirs m d a b hab ha hb (quEnt r c),
    quGrid_matOf m d r (ground.swapIx a b c)]
  exact ground.matOf_congr m d _ _ (fun t k _ _ => quEnt_swapIx r c a b t k)

/-- The transposition carries a product monomial to the product of
the transposed monomials. -/
private theorem swapDirs_addG_ip (m d r s t u a b i j : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) :
    swapDirs a b (addG (ipGrid m d r s i) (ipGrid m d t u j))
      = addG (ipGrid m d r s (ground.swapIx a b i))
          (ipGrid m d t u (ground.swapIx a b j)) := by
  rw [ipGrid_matOf m d r s i, ipGrid_matOf m d t u j,
    addG_matOf m d (ipEnt r s i) (ipEnt t u j),
    matOf_swapDirs m d a b hab ha hb
      (fun t' k => ipEnt r s i t' k + ipEnt t u j t' k),
    ipGrid_matOf m d r s (ground.swapIx a b i),
    ipGrid_matOf m d t u (ground.swapIx a b j),
    addG_matOf m d (ipEnt r s (ground.swapIx a b i))
      (ipEnt t u (ground.swapIx a b j))]
  refine ground.matOf_congr m d _ _ (fun t' k _ _ => ?_)
  show ipEnt r s i t' (ground.swapIx a b k)
      + ipEnt t u j t' (ground.swapIx a b k)
    = ipEnt r s (ground.swapIx a b i) t' k
      + ipEnt t u (ground.swapIx a b j) t' k
  rw [ipEnt_swapIx r s i a b t' k, ipEnt_swapIx t u j a b t' k]

/-- The inner product's monomial has total degree the count of its
two arguments below the argument count. -/
private theorem ipGrid_deg (m d r s c : Nat) (hc : c < d) :
    ground.sumNat ((ipGrid m d r s c).map ground.sumNat)
      = (if r < m then 1 else 0) + (if s < m then 1 else 0) := by
  have hinner : ∀ t : Nat,
      ground.sumNat ((List.range d).map (ipEnt r s c t))
        = (if t == r then 1 else 0) + (if t == s then 1 else 0) := by
    intro t
    rw [ground.map_congr_all (ipEnt r s c t)
        (fun k => (if k == c then (if t == r then 1 else 0) else 0)
          + (if k == c then (if t == s then 1 else 0) else 0))
        (fun k => by
          show (if t == r && k == c then 1 else 0)
              + (if t == s && k == c then 1 else 0)
            = (if k == c then (if t == r then 1 else 0) else 0)
              + (if k == c then (if t == s then 1 else 0) else 0)
          rw [ite_and_right (t == r) (k == c) 1,
            ite_and_right (t == s) (k == c) 1])
        (List.range d),
      sumNat_map_add
        (fun k => if k == c then (if t == r then 1 else 0) else 0)
        (fun k => if k == c then (if t == s then 1 else 0) else 0)
        (List.range d),
      sumNat_ind_range c (if t == r then 1 else 0) d,
      sumNat_ind_range c (if t == s then 1 else 0) d,
      if_pos hc, if_pos hc]
  rw [ipGrid_matOf m d r s c, deg_matOf m d (ipEnt r s c),
    ground.map_congr_all
      (fun t => ground.sumNat ((List.range d).map (ipEnt r s c t)))
      (fun t => (if t == r then 1 else 0) + (if t == s then 1 else 0))
      hinner (List.range m),
    sumNat_map_add (fun t => if t == r then 1 else 0)
      (fun t => if t == s then 1 else 0) (List.range m),
    sumNat_ind_range r 1 m, sumNat_ind_range s 1 m]

/-- The inner product's monomial reads its own degree along its own
coordinate. -/
private theorem ipGrid_dirTot_at (m d r s c : Nat) (hc : c < d) :
    dirTot c (ipGrid m d r s c)
      = (if r < m then 1 else 0) + (if s < m then 1 else 0) := by
  rw [ipGrid_matOf m d r s c, dirTot_matOf m d c hc (ipEnt r s c),
    ground.map_congr_all (fun t => ipEnt r s c t c)
      (fun t => (if t == r then 1 else 0) + (if t == s then 1 else 0))
      (fun t => by
        show (if t == r && c == c then 1 else 0)
            + (if t == s && c == c then 1 else 0)
          = (if t == r then 1 else 0) + (if t == s then 1 else 0)
        rw [ite_and_right (t == r) (c == c) 1,
          ite_and_right (t == s) (c == c) 1,
          ground.eqBeqOf (rfl : c = c)]
        rfl)
      (List.range m),
    sumNat_map_add (fun t => if t == r then 1 else 0)
      (fun t => if t == s then 1 else 0) (List.range m),
    sumNat_ind_range r 1 m, sumNat_ind_range s 1 m]

/-- The inner product's monomial is vacant along every further
coordinate. -/
private theorem ipGrid_dirTot_off (m d r s c i : Nat) (hi : i < d)
    (hic : ¬ i = c) : dirTot i (ipGrid m d r s c) = 0 := by
  rw [ipGrid_matOf m d r s c, dirTot_matOf m d i hi (ipEnt r s c)]
  refine sumNat_map_zero_mem _ (List.range m) (fun t _ => ?_)
  show (if t == r && i == c then 1 else 0)
      + (if t == s && i == c then 1 else 0) = 0
  rw [ite_and_right (t == r) (i == c) 1,
    ite_and_right (t == s) (i == c) 1, ground.neBeqOf hic]
  rfl

/-- The quartic's monomial reads four along its own coordinate at
an argument below the count. -/
private theorem quGrid_dirTot_at (m d r c : Nat) (hc : c < d) :
    dirTot c (quGrid m d r c) = if r < m then 4 else 0 := by
  rw [quGrid_matOf m d r c, dirTot_matOf m d c hc (quEnt r c),
    ground.map_congr_all (fun t => quEnt r c t c)
      (fun t => if t == r then 4 else 0)
      (fun t => by
        show (if t == r && c == c then 4 else 0)
          = if t == r then 4 else 0
        rw [ite_and_right (t == r) (c == c) 4,
          ground.eqBeqOf (rfl : c = c)]
        rfl)
      (List.range m),
    sumNat_ind_range r 4 m]

/-- The quartic's monomial is vacant along every further
coordinate. -/
private theorem quGrid_dirTot_off (m d r c i : Nat) (hi : i < d)
    (hic : ¬ i = c) : dirTot i (quGrid m d r c) = 0 := by
  rw [quGrid_matOf m d r c, dirTot_matOf m d i hi (quEnt r c)]
  refine sumNat_map_zero_mem _ (List.range m) (fun t _ => ?_)
  show (if t == r && i == c then 4 else 0) = 0
  rw [ite_and_right (t == r) (i == c) 4, ground.neBeqOf hic]
  rfl

/-- A product monomial's total degree is the two factors' own. -/
private theorem deg_addG_ip (m d r s t u i j : Nat) :
    ground.sumNat
        ((addG (ipGrid m d r s i) (ipGrid m d t u j)).map ground.sumNat)
      = ground.sumNat ((ipGrid m d r s i).map ground.sumNat)
        + ground.sumNat ((ipGrid m d t u j).map ground.sumNat) := by
  rw [ipGrid_matOf m d r s i, ipGrid_matOf m d t u j,
    addG_matOf m d (ipEnt r s i) (ipEnt t u j),
    deg_matOf m d (fun t' k => ipEnt r s i t' k + ipEnt t u j t' k),
    deg_matOf m d (ipEnt r s i), deg_matOf m d (ipEnt t u j),
    ground.map_congr_all
      (fun t' => ground.sumNat ((List.range d).map
        (fun k => ipEnt r s i t' k + ipEnt t u j t' k)))
      (fun t' => ground.sumNat ((List.range d).map (ipEnt r s i t'))
        + ground.sumNat ((List.range d).map (ipEnt t u j t')))
      (fun t' => sumNat_map_add (ipEnt r s i t') (ipEnt t u j t')
        (List.range d))
      (List.range m)]
  exact sumNat_map_add
    (fun t' => ground.sumNat ((List.range d).map (ipEnt r s i t')))
    (fun t' => ground.sumNat ((List.range d).map (ipEnt t u j t')))
    (List.range m)

/-- A product monomial's total along a coordinate is the two
factors' own. -/
private theorem dirTot_addG_ip (m d r s t u i j p : Nat) (hp : p < d) :
    dirTot p (addG (ipGrid m d r s i) (ipGrid m d t u j))
      = dirTot p (ipGrid m d r s i) + dirTot p (ipGrid m d t u j) := by
  rw [ipGrid_matOf m d r s i, ipGrid_matOf m d t u j,
    addG_matOf m d (ipEnt r s i) (ipEnt t u j),
    dirTot_matOf m d p hp
      (fun t' k => ipEnt r s i t' k + ipEnt t u j t' k),
    dirTot_matOf m d p hp (ipEnt r s i),
    dirTot_matOf m d p hp (ipEnt t u j)]
  exact sumNat_map_add (fun t' => ipEnt r s i t' p)
    (fun t' => ipEnt t u j t' p) (List.range m)

/-- The inner product's degree is at most two. -/
private theorem ip_deg_le (m r s : Nat) :
    (if r < m then 1 else 0) + (if s < m then 1 else 0) ≤ 2 := by
  by_cases h1 : r < m
  · by_cases h2 : s < m
    · rw [if_pos h1, if_pos h2]
      exact Nat.le_refl 2
    · rw [if_pos h1, if_neg h2]
      exact Nat.le_succ 1
  · by_cases h2 : s < m
    · rw [if_neg h1, if_pos h2]
      exact Nat.le_succ 1
    · rw [if_neg h1, if_neg h2]
      exact Nat.zero_le 2

/-- Two counts at most two summing to four are each two. -/
private theorem eq_two_of_sum_four (x y : Nat) (hx : x ≤ 2) (hy : y ≤ 2)
    (h : x + y = 4) : x = 2 := by
  refine Nat.le_antisymm hx ?_
  have h1 : x + y ≤ x + 2 := Nat.add_le_add_left hy x
  rw [h] at h1
  exact ground.leCancelR 2 (show 2 + 2 ≤ x + 2 from h1)

/-- The comparison against an inner product's monomial reindexes
its coordinate across a transposition. -/
private theorem ipBeq_swap (m d r s a b k : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (g : List (List Nat)) :
    (swapDirs a b g == ipGrid m d r s k)
      = (g == ipGrid m d r s (ground.swapIx a b k)) := by
  refine boolEqOfImp (fun h => ?_) (fun h => ?_)
  · rw [show g = ipGrid m d r s (ground.swapIx a b k) from by
      rw [← swapDirs_swapDirs a b g, gridBeqEq h,
        swapDirs_ipGrid m d r s k a b hab ha hb]]
    exact gridEqBeq _
  · rw [show swapDirs a b g = ipGrid m d r s k from by
      rw [gridBeqEq h, swapDirs_ipGrid m d r s (ground.swapIx a b k) a b
        hab ha hb, ground.swapIx_invol a b k]]
    exact gridEqBeq _

/-- The comparison against the quartic's monomial reindexes its
coordinate across a transposition. -/
private theorem quBeq_swap (m d r a b k : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (g : List (List Nat)) :
    (swapDirs a b g == quGrid m d r k)
      = (g == quGrid m d r (ground.swapIx a b k)) := by
  refine boolEqOfImp (fun h => ?_) (fun h => ?_)
  · rw [show g = quGrid m d r (ground.swapIx a b k) from by
      rw [← swapDirs_swapDirs a b g, gridBeqEq h,
        swapDirs_quGrid m d r k a b hab ha hb]]
    exact gridEqBeq _
  · rw [show swapDirs a b g = quGrid m d r k from by
      rw [gridBeqEq h, swapDirs_quGrid m d r (ground.swapIx a b k) a b
        hab ha hb, ground.swapIx_invol a b k]]
    exact gridEqBeq _

/-- The comparison against a product monomial reindexes both
coordinates across a transposition. -/
private theorem prodBeq_swap (m d r s t u a b i j : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (g : List (List Nat)) :
    (swapDirs a b g == addG (ipGrid m d r s i) (ipGrid m d t u j))
      = (g == addG (ipGrid m d r s (ground.swapIx a b i))
          (ipGrid m d t u (ground.swapIx a b j))) := by
  refine boolEqOfImp (fun h => ?_) (fun h => ?_)
  · rw [show g = addG (ipGrid m d r s (ground.swapIx a b i))
        (ipGrid m d t u (ground.swapIx a b j)) from by
      rw [← swapDirs_swapDirs a b g, gridBeqEq h,
        swapDirs_addG_ip m d r s t u a b i j hab ha hb]]
    exact gridEqBeq _
  · rw [show swapDirs a b g
        = addG (ipGrid m d r s i) (ipGrid m d t u j) from by
      rw [gridBeqEq h, swapDirs_addG_ip m d r s t u a b
        (ground.swapIx a b i) (ground.swapIx a b j) hab ha hb,
        ground.swapIx_invol a b i, ground.swapIx_invol a b j]]
    exact gridEqBeq _

/-- The inner product family's matching fold is blind to a
transposition. -/
private theorem ipAny_swap (m d r s a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (g : List (List Nat)) :
    ((List.range d).any (fun k => swapDirs a b g == ipGrid m d r s k))
      = ((List.range d).any (fun k => g == ipGrid m d r s k)) := by
  refine boolEqOfImp (fun h => ?_) (fun h => ?_)
  · obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) h
    refine ground.any_of_mem _ (ground.memRange (ground.swapIx_lt ha hb k
      (ground.ltOfMemRange hkm))) ?_
    rw [ipBeq_swap m d r s a b k hab ha hb g] at hkb
    exact hkb
  · obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) h
    refine ground.any_of_mem _ (ground.memRange (ground.swapIx_lt ha hb k
      (ground.ltOfMemRange hkm))) ?_
    rw [ipBeq_swap m d r s a b (ground.swapIx a b k) hab ha hb g,
      ground.swapIx_invol a b k]
    exact hkb

/-- The quartic family's matching fold is blind to a
transposition. -/
private theorem quAny_swap (m d r a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (g : List (List Nat)) :
    ((List.range d).any (fun k => swapDirs a b g == quGrid m d r k))
      = ((List.range d).any (fun k => g == quGrid m d r k)) := by
  refine boolEqOfImp (fun h => ?_) (fun h => ?_)
  · obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) h
    refine ground.any_of_mem _ (ground.memRange (ground.swapIx_lt ha hb k
      (ground.ltOfMemRange hkm))) ?_
    rw [quBeq_swap m d r a b k hab ha hb g] at hkb
    exact hkb
  · obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) h
    refine ground.any_of_mem _ (ground.memRange (ground.swapIx_lt ha hb k
      (ground.ltOfMemRange hkm))) ?_
    rw [quBeq_swap m d r a b (ground.swapIx a b k) hab ha hb g,
      ground.swapIx_invol a b k]
    exact hkb

/-- The inner product family reads one value across a
transposition. -/
private theorem ipFam_swap (m d r s a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (g : List (List Nat)) :
    ipFam m d r s (swapDirs a b g) = ipFam m d r s g := by
  show (if (List.range d).any (fun i => swapDirs a b g == ipGrid m d r s i)
      then BPair.ofNat 1 else BPair.unit)
    = (if (List.range d).any (fun i => g == ipGrid m d r s i)
      then BPair.ofNat 1 else BPair.unit)
  rw [ipAny_swap m d r s a b hab ha hb g]

/-- The quartic family reads one value across a transposition. -/
private theorem quFam_swap (m d r a b : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) (g : List (List Nat)) :
    quFam m d r (swapDirs a b g) = quFam m d r g := by
  show (if (List.range d).any (fun i => swapDirs a b g == quGrid m d r i)
      then BPair.ofNat 1 else BPair.unit)
    = (if (List.range d).any (fun i => g == quGrid m d r i)
      then BPair.ofNat 1 else BPair.unit)
  rw [quAny_swap m d r a b hab ha hb g]

/-- The inner product family is the sum's unit off its own
monomials. -/
private theorem ipFam_vac (m d r s : Nat) (g : List (List Nat))
    (h : ((List.range d).any (fun i => g == ipGrid m d r s i)) = false) :
    ipFam m d r s g = BPair.unit := by
  show (if (List.range d).any (fun i => g == ipGrid m d r s i)
    then BPair.ofNat 1 else BPair.unit) = BPair.unit
  rw [h]
  rfl

/-- The quartic family is the sum's unit off its own monomials. -/
private theorem quFam_vac (m d r : Nat) (g : List (List Nat))
    (h : ((List.range d).any (fun i => g == quGrid m d r i)) = false) :
    quFam m d r g = BPair.unit := by
  show (if (List.range d).any (fun i => g == quGrid m d r i)
    then BPair.ofNat 1 else BPair.unit) = BPair.unit
  rw [h]
  rfl

/-- The splitting count over the two coordinate ranges. -/
private def dblSum (d : Nat) (f : Nat → Nat → Nat) : Nat :=
  ground.sumNat ((List.range d).flatMap (fun i =>
    (List.range d).map (fun j => f i j)))

/-- The splitting count is the per-coordinate counts' total. -/
private theorem dblSum_fold (d : Nat) (f : Nat → Nat → Nat) :
    dblSum d f = ground.sumNat ((List.range d).map
      (fun i => ground.sumNat ((List.range d).map (fun j => f i j)))) :=
  sumNat_flatMap (fun i => (List.range d).map (fun j => f i j))
    (List.range d)

/-- Two counting families agreeing at every coordinate pair count
alike. -/
private theorem dblSum_congr (d : Nat) (f h : Nat → Nat → Nat)
    (hfh : ∀ i j, f i j = h i j) : dblSum d f = dblSum d h := by
  show ground.sumNat ((List.range d).flatMap
      (fun i => (List.range d).map (fun j => f i j)))
    = ground.sumNat ((List.range d).flatMap
      (fun i => (List.range d).map (fun j => h i j)))
  rw [ground.flatMap_congr_all _
    (fun i => (List.range d).map (fun j => h i j))
    (fun i => ground.map_congr_all _ _ (fun j => hfh i j) (List.range d))
    (List.range d)]

/-- The splitting count is blind to a transposition of the two
coordinate ranges. -/
private theorem dblSum_swapIx (d a b : Nat) (ha : a < d) (hb : b < d)
    (f : Nat → Nat → Nat) :
    dblSum d f = dblSum d (fun i j =>
      f (ground.swapIx a b i) (ground.swapIx a b j)) := by
  rw [dblSum_fold d f, dblSum_fold d (fun i j =>
      f (ground.swapIx a b i) (ground.swapIx a b j)),
    sumNat_range_swapIx d a b ha hb
      (fun i => ground.sumNat ((List.range d).map (fun j => f i j)))]
  refine congrArg ground.sumNat
    (ground.map_congr_all _ _ (fun i => ?_) (List.range d))
  exact sumNat_range_swapIx d a b ha hb
    (fun j => f (ground.swapIx a b i) j)

/-- The product family is the sum's unit off its own product
monomials. -/
private theorem prodIP_vac (m d r s t u : Nat) (g : List (List Nat))
    (h : ((List.range d).any (fun i => (List.range d).any (fun j =>
      g == addG (ipGrid m d r s i) (ipGrid m d t u j)))) = false) :
    prodIP m d r s t u g = BPair.unit := by
  have hz : dblSum d (fun i j =>
      if g == addG (ipGrid m d r s i) (ipGrid m d t u j)
      then 1 else 0) = 0 := by
    rw [dblSum_fold d (fun i j =>
      if g == addG (ipGrid m d r s i) (ipGrid m d t u j) then 1 else 0)]
    refine sumNat_map_zero_mem _ (List.range d) (fun i him => ?_)
    have hin := any_range_false d _ h i
      (ground.ltOfMemRange him)
    refine sumNat_map_zero_mem _ (List.range d) (fun j hjm => ?_)
    rw [any_range_false d _ hin j
      (ground.ltOfMemRange hjm)]
    rfl
  show BPair.ofNat (dblSum d (fun i j =>
    if g == addG (ipGrid m d r s i) (ipGrid m d t u j)
    then 1 else 0)) = BPair.unit
  rw [hz]
  rfl

/-- The two settling moves' read at a family: the reflection clause
at every member of the box and the transposition clause at every
grid. -/
private theorem bdInvAt_intro (m d D : Nat) (c : List (List Nat) → BPair)
    (hA : ∀ g : List (List Nat), 0 < ground.countOf g (momBox m d D) →
      ∀ i, i < d →
        (dirTot i g % 2 == 0 || decide ((c g).oneValue BPair.unit)) = true)
    (hB : ∀ (g : List (List Nat)) (i j : Nat), i < j → j < d →
      (c (swapDirs i j g)).oneValue (c g)) :
    bdInvAt m d D c := by
  show ((momBox m d D).all (fun g =>
    ((List.range d).all (fun i =>
      dirTot i g % 2 == 0 || decide ((c g).oneValue BPair.unit)))
    && ((List.range d).all (fun i => (List.range d).all (fun j =>
      !decide (i < j)
        || decide ((c (swapDirs i j g)).oneValue (c g))))))) = true
  refine ground.all_of_getAt ([] : List (List Nat)) _ (momBox m d D) ?_
  intro k hk
  have hcnt : 0 < ground.countOf
      (ground.getAt ([] : List (List Nat)) (momBox m d D) k)
      (momBox m d D) :=
    ground.countOf_pos_of_mem (ground.mem_getAt _ (momBox m d D) k hk)
  refine ground.andIntroB
    (ground.all_range_intro d (fun i hi => hA _ hcnt i hi)) ?_
  refine ground.all_range_intro d (fun i _ => ?_)
  refine ground.all_range_intro d (fun j hj => ?_)
  by_cases hij : i < j
  · rw [decide_eq_true hij, decide_eq_true (hB _ i j hij hj)]
    rfl
  · rw [decide_eq_false hij]
    rfl

/-- The pairwise inner product's family is invariant at its degree:
its monomials carry an even total along every coordinate — the two
arguments' exponents, which the box's degree pins at two — and its
matching fold is blind to a transposition
(`thm:restoration`'s invariance at `K^(r)·K^(s)`). -/
theorem ipFam_inv (m d r s : Nat) : bdInvAt m d 2 (ipFam m d r s) := by
  refine bdInvAt_intro m d 2 (ipFam m d r s) ?_ ?_
  · intro g hg i hi
    cases hany : ((List.range d).any (fun k => g == ipGrid m d r s k)) with
    | false =>
      rw [ipFam_vac m d r s g hany,
        decide_eq_true (BPair.oneValue_refl BPair.unit)]
      exact Bool.or_true _
    | true =>
      obtain ⟨c, hcm, hcb⟩ := ground.mem_of_any _ (List.range d) hany
      have hcd : c < d := ground.ltOfMemRange hcm
      have hgc : g = ipGrid m d r s c := gridBeqEq hcb
      have hdeg : (if r < m then 1 else 0) + (if s < m then 1 else 0) = 2 := by
        rw [← ipGrid_deg m d r s c hcd, ← hgc]
        exact (momBox_reads m d 2 g hg).2.2
      have hpar : (dirTot i g % 2 == 0) = true := by
        by_cases hic : i = c
        · rw [hgc, hic, ipGrid_dirTot_at m d r s c hcd, hdeg]
          rfl
        · rw [hgc, ipGrid_dirTot_off m d r s c i hi hic]
          rfl
      rw [hpar]
      rfl
  · intro g i j hij hj
    exact BPair.oneValue_of_eq (ipFam_swap m d r s i j (Nat.ne_of_lt hij)
      (Nat.lt_trans hij hj) hj g)

/-- The diagonal quartic's family is invariant at its degree: its
monomials carry four or nothing along every coordinate and its
matching fold is blind to a transposition
(`thm:restoration`'s invariance at the quartic). -/
theorem quFam_inv (m d r : Nat) : bdInvAt m d 4 (quFam m d r) := by
  refine bdInvAt_intro m d 4 (quFam m d r) ?_ ?_
  · intro g _ i hi
    cases hany : ((List.range d).any (fun k => g == quGrid m d r k)) with
    | false =>
      rw [quFam_vac m d r g hany,
        decide_eq_true (BPair.oneValue_refl BPair.unit)]
      exact Bool.or_true _
    | true =>
      obtain ⟨c, hcm, hcb⟩ := ground.mem_of_any _ (List.range d) hany
      have hcd : c < d := ground.ltOfMemRange hcm
      have hgc : g = quGrid m d r c := gridBeqEq hcb
      have hpar : (dirTot i g % 2 == 0) = true := by
        by_cases hic : i = c
        · rw [hgc, hic, quGrid_dirTot_at m d r c hcd]
          by_cases hrm : r < m
          · rw [if_pos hrm]
            rfl
          · rw [if_neg hrm]
            rfl
        · rw [hgc, quGrid_dirTot_off m d r c i hi hic]
          rfl
      rw [hpar]
      rfl
  · intro g i j hij hj
    exact BPair.oneValue_of_eq (quFam_swap m d r i j (Nat.ne_of_lt hij)
      (Nat.lt_trans hij hj) hj g)

/-- Two inner products' product family is invariant at its degree:
a product monomial's total along a coordinate is the two factors'
own, each factor's degree two at the box's degree four, and the
splitting count is blind to a transposition, which reindexes both
coordinate ranges along the same involution
(`thm:restoration`'s invariance at the product). -/
theorem prodIP_inv (m d r s t u : Nat) :
    bdInvAt m d 4 (prodIP m d r s t u) := by
  refine bdInvAt_intro m d 4 (prodIP m d r s t u) ?_ ?_
  · intro g hg p hp
    cases hany : ((List.range d).any (fun i => (List.range d).any
        (fun j => g == addG (ipGrid m d r s i) (ipGrid m d t u j)))) with
    | false =>
      rw [prodIP_vac m d r s t u g hany,
        decide_eq_true (BPair.oneValue_refl BPair.unit)]
      exact Bool.or_true _
    | true =>
      obtain ⟨i0, hi0m, hi0⟩ := ground.mem_of_any _ (List.range d) hany
      have hi0d : i0 < d := ground.ltOfMemRange hi0m
      obtain ⟨j0, hj0m, hj0⟩ := ground.mem_of_any _ (List.range d) hi0
      have hj0d : j0 < d := ground.ltOfMemRange hj0m
      have hgc : g = addG (ipGrid m d r s i0) (ipGrid m d t u j0) :=
        gridBeqEq hj0
      have hdegsum : ((if r < m then 1 else 0) + (if s < m then 1 else 0))
          + ((if t < m then 1 else 0) + (if u < m then 1 else 0)) = 4 := by
        rw [← ipGrid_deg m d r s i0 hi0d, ← ipGrid_deg m d t u j0 hj0d,
          ← deg_addG_ip m d r s t u i0 j0, ← hgc]
        exact (momBox_reads m d 4 g hg).2.2
      have hX : (if r < m then 1 else 0) + (if s < m then 1 else 0) = 2 :=
        eq_two_of_sum_four _ _ (ip_deg_le m r s) (ip_deg_le m t u) hdegsum
      have hY : (if t < m then 1 else 0) + (if u < m then 1 else 0) = 2 :=
        eq_two_of_sum_four _ _ (ip_deg_le m t u) (ip_deg_le m r s)
          (by rw [Nat.add_comm]; exact hdegsum)
      have hAt : dirTot p (ipGrid m d r s i0) = (if p = i0 then 2 else 0) := by
        by_cases hpi : p = i0
        · rw [if_pos hpi, hpi, ipGrid_dirTot_at m d r s i0 hi0d, hX]
        · rw [if_neg hpi, ipGrid_dirTot_off m d r s i0 p hp hpi]
      have hBt : dirTot p (ipGrid m d t u j0) = (if p = j0 then 2 else 0) := by
        by_cases hpj : p = j0
        · rw [if_pos hpj, hpj, ipGrid_dirTot_at m d t u j0 hj0d, hY]
        · rw [if_neg hpj, ipGrid_dirTot_off m d t u j0 p hp hpj]
      have hpar : (dirTot p g % 2 == 0) = true := by
        rw [hgc, dirTot_addG_ip m d r s t u i0 j0 p hp, hAt, hBt]
        by_cases hpi : p = i0
        · by_cases hpj : p = j0
          · rw [if_pos hpi, if_pos hpj]
            rfl
          · rw [if_pos hpi, if_neg hpj]
            rfl
        · by_cases hpj : p = j0
          · rw [if_neg hpi, if_pos hpj]
            rfl
          · rw [if_neg hpi, if_neg hpj]
            rfl
      rw [hpar]
      rfl
  · intro g a b hab hbd
    have had : a < d := Nat.lt_trans hab hbd
    have hcount : dblSum d (fun i j => if swapDirs a b g
          == addG (ipGrid m d r s i) (ipGrid m d t u j) then 1 else 0)
        = dblSum d (fun i j => if g
          == addG (ipGrid m d r s i) (ipGrid m d t u j) then 1 else 0) := by
      rw [dblSum_congr d
        (fun i j => if swapDirs a b g
          == addG (ipGrid m d r s i) (ipGrid m d t u j) then 1 else 0)
        (fun i j => if g == addG (ipGrid m d r s (ground.swapIx a b i))
          (ipGrid m d t u (ground.swapIx a b j)) then 1 else 0)
        (fun i j => by
          rw [prodBeq_swap m d r s t u a b i j (Nat.ne_of_lt hab) had hbd g])]
      exact (dblSum_swapIx d a b had hbd
        (fun i j => if g == addG (ipGrid m d r s i) (ipGrid m d t u j)
          then 1 else 0)).symm
    refine BPair.oneValue_of_eq ?_
    show BPair.ofNat (dblSum d (fun i j => if swapDirs a b g
        == addG (ipGrid m d r s i) (ipGrid m d t u j) then 1 else 0))
      = BPair.ofNat (dblSum d (fun i j => if g
        == addG (ipGrid m d r s i) (ipGrid m d t u j) then 1 else 0))
    rw [hcount]

/-! The degree-two span: at the box's degree two an invariant
family's coefficient is read off the pairwise inner products'
coefficients alone (`thm:restoration`'s rings-coincide clause).
The mechanism is the box's own arithmetic.  A grid of the box is
the grid at its entry reads (`matOf_entOf`), so its total degree
and its coordinate totals are one double fold exchanged
(`ground.famFold_swap`); at degree two the coordinate totals sum
to two, so an even family of them holds one coordinate at two and
the rest vacant, and within that coordinate the two units sit at
one argument or at two.  Either way the grid is a pairwise inner
product's monomial at two arguments in order (`deg2_classify`),
those monomials are distinct data (`ipGrid_inj`), and the
transposition carries the monomial's coordinate to the first
(`bdInv_swap` at the named grids) — so the guarded double sum over
the ordered argument pairs holds exactly one term off the sum's
unit and the coefficient is that term's own. -/

/-- A count below two off the vacant reads the unit. -/
private theorem lt_two_cases : ∀ {a : Nat}, a < 2 → ¬ a = 0 → a = 1
  | 0, _, h0 => absurd rfl h0
  | 1, _, _ => rfl
  | k + 2, h, _ =>
    absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))
      (Nat.not_succ_le_zero k)

/-- A count off the even class reads the odd remainder. -/
private theorem mod_two_odd {n : Nat} (h : ¬ n % 2 = 0) : n % 2 = 1 :=
  lt_two_cases (ground.natDivRead n 2 (Nat.succ_pos 1)).2 h

/-- An even count above the vacant reads at or above two. -/
private theorem two_le_of_even_pos {n : Nat} (he : n % 2 = 0)
    (hp : 0 < n) : 2 ≤ n := by
  cases Nat.lt_or_ge n 2 with
  | inr hge => exact hge
  | inl hlt =>
    rw [lt_two_cases hlt (fun h0 => Nat.lt_irrefl 0 (h0 ▸ hp))] at he
    exact absurd he (by decide +kernel)

/-- A count between the unit and two is one of them. -/
private theorem one_or_two : ∀ {n : Nat}, 0 < n → n ≤ 2 → n = 1 ∨ n = 2
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, _ => Or.inl rfl
  | 2, _, _ => Or.inr rfl
  | k + 3, _, h =>
    absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))
      (Nat.not_succ_le_zero k)

/-- A joined unit is never vacant. -/
private theorem one_add_ne_zero (x : Nat) : ¬ 1 + x = 0 := by
  rw [Nat.add_comm]
  exact fun h => Nat.noConfusion h

/-- A fold reading its whole total at one occupied key is vacant at
every further occupied key. -/
private theorem fold_rest_zero {α : Type} [DecidableEq α] (F : α → Nat)
    (l : List α) (i : α) (hc : 0 < ground.countOf i l)
    (h : ground.famFold Nat.add 0 F l = F i)
    (x : α) (hx : 0 < ground.countOf x l) (hxi : ¬ x = i) : F x = 0 := by
  have hsplit : ground.famFold Nat.add 0 F l
      = F i + ground.famFold Nat.add 0 F (ground.eraseFirst i l) :=
    ground.famFold_eraseFirst Nat.add 0 Nat.add_comm Nat.add_assoc F l i hc
  rw [h] at hsplit
  have hz : ground.famFold Nat.add 0 F (ground.eraseFirst i l) = 0 :=
    (ground.addCancelL (F i) (by rw [Nat.add_zero]; exact hsplit)).symm
  have hmem : x ∈ ground.eraseFirst i l :=
    ground.mem_of_countOf_pos x _ (by
      rw [ground.countOf_eraseFirst_ne l i x hxi]
      exact hx)
  have hle := ground.famFold_mem_le F (ground.eraseFirst i l) x hmem
  rw [hz] at hle
  exact Nat.le_antisymm hle (Nat.zero_le _)

/-- A grid's entry at an argument and a coordinate. -/
private def entOf (g : List (List Nat)) (t k : Nat) : Nat :=
  ground.getAt 0 (ground.getAt ([] : List Nat) g t) k

/-- A grid at the box's shape is the grid at its own entry
reads. -/
private theorem matOf_entOf (m d : Nat) (g : List (List Nat))
    (hl : g.length = m)
    (ha : (g.all (fun row => row.length == d)) = true) :
    g = ground.matOf m d (entOf g) := by
  have hrow : ∀ t, 0 < ground.countOf t (List.range m) →
      (List.range d).map (entOf g t)
        = ground.getAt ([] : List Nat) g t := by
    intro t ht
    have hmem : ground.getAt ([] : List Nat) g t ∈ g :=
      ground.mem_getAt _ g t (by rw [hl]; exact ground.ltOfMem ht)
    exact ground.range_map_getAt 0 d _
      (ground.beqEqOf (ground.all_of_mem _ g ha _ hmem))
  show g = (List.range m).map (fun t => (List.range d).map (entOf g t))
  rw [ground.map_congr_members (fun t => (List.range d).map (entOf g t))
      (ground.getAt ([] : List Nat) g) (List.range m) hrow,
    ground.range_map_getAt ([] : List Nat) m g hl]

/-- A grid whose entries read the pairwise inner product's own is
that monomial. -/
private theorem matOf_eq_ipGrid (m d : Nat) (E : Nat → Nat → Nat)
    (t t' i : Nat)
    (h : ∀ a, a < m → ∀ k, k < d → E a k = ipEnt t t' i a k) :
    ground.matOf m d E = ipGrid m d t t' i := by
  rw [ipGrid_matOf m d t t' i]
  exact ground.matOf_congr m d E (ipEnt t t' i) (fun a c hac hcc => h a hac c hcc)

/-- The inner product's entry formula at its own coordinate reads
the two arguments' matches. -/
private theorem ipEnt_at (t t' c a k : Nat) (hk : k = c) :
    ipEnt t t' c a k
      = (if a == t then 1 else 0) + (if a == t' then 1 else 0) := by
  show (if a == t && k == c then 1 else 0)
      + (if a == t' && k == c then 1 else 0)
    = (if a == t then 1 else 0) + (if a == t' then 1 else 0)
  rw [ite_and_right (a == t) (k == c) 1,
    ite_and_right (a == t') (k == c) 1, ground.eqBeqOf hk]
  rfl

/-- The inner product's entry formula is vacant off its own
coordinate. -/
private theorem ipEnt_off (t t' c a k : Nat) (hk : ¬ k = c) :
    ipEnt t t' c a k = 0 := by
  show (if a == t && k == c then 1 else 0)
      + (if a == t' && k == c then 1 else 0) = 0
  rw [ite_and_right (a == t) (k == c) 1,
    ite_and_right (a == t') (k == c) 1, ground.neBeqOf hk]
  rfl

/-- A two-argument indicator holding its second argument is above
the vacant. -/
private theorem ind_snd_ne_zero (a x : Nat) :
    ¬ ((if a == x then 1 else 0) + (if a == a then 1 else 0) = 0) := by
  rw [ground.eqBeqOf (rfl : a = a)]
  intro hc
  exact one_add_ne_zero (if a == x then 1 else 0)
    (by rw [Nat.add_comm]; exact hc)

/-- A two-argument indicator above the vacant names one of its
arguments. -/
private theorem ind_pair_cases (a x y : Nat)
    (h : ¬ ((if a == x then 1 else 0) + (if a == y then 1 else 0) = 0)) :
    a = x ∨ a = y := by
  by_cases hx : a = x
  · exact Or.inl hx
  · by_cases hy : a = y
    · exact Or.inr hy
    · refine absurd ?_ h
      rw [ground.neBeqOf hx, ground.neBeqOf hy]
      rfl

/-- Two argument pairs in order carrying one indicator read name
the same two arguments. -/
private theorem pair_eq_of_ind (m t t' r s : Nat) (ht : t ≤ t')
    (ht'm : t' < m) (hr : r ≤ s) (hsm : s < m)
    (h : ∀ a, a < m →
      (if a == t then 1 else 0) + (if a == t' then 1 else 0)
        = (if a == r then 1 else 0) + (if a == s then 1 else 0)) :
    t = r ∧ t' = s := by
  have ht'le : t' ≤ s := by
    have hne : ¬ ((if t' == r then 1 else 0)
        + (if t' == s then 1 else 0) = 0) := by
      rw [← h t' ht'm]
      exact ind_snd_ne_zero t' t
    cases ind_pair_cases t' r s hne with
    | inl he => exact Nat.le_trans (Nat.le_of_eq he) hr
    | inr he => exact Nat.le_of_eq he
  have hsle : s ≤ t' := by
    have hne : ¬ ((if s == t then 1 else 0)
        + (if s == t' then 1 else 0) = 0) := by
      rw [h s hsm]
      exact ind_snd_ne_zero s r
    cases ind_pair_cases s t t' hne with
    | inl he => exact Nat.le_trans (Nat.le_of_eq he) ht
    | inr he => exact Nat.le_of_eq he
  have hts : t' = s := Nat.le_antisymm ht'le hsle
  refine ⟨?_, hts⟩
  have hcancel := h t (Nat.lt_of_le_of_lt ht ht'm)
  rw [hts] at hcancel
  have hone : (if t == t then 1 else 0) = (if t == r then 1 else 0) :=
    ground.addCancelR (if t == s then 1 else 0) hcancel
  rw [ground.eqBeqOf (rfl : t = t)] at hone
  by_cases htr : t = r
  · exact htr
  · rw [ground.neBeqOf htr] at hone
    exact absurd (show (1 : Nat) = 0 from hone)
      (fun hc => Nat.noConfusion hc)

/-- The inner product's monomials are distinct data: at arguments
below the count in order and a coordinate below the direction
count the monomial names its own two arguments and its own
coordinate. -/
private theorem ipGrid_inj (m d t t' r s i k : Nat)
    (ht : t ≤ t') (ht'm : t' < m) (hid : i < d)
    (hr : r ≤ s) (hsm : s < m)
    (he : ipGrid m d t t' i = ipGrid m d r s k) :
    t = r ∧ t' = s ∧ i = k := by
  have htm : t < m := Nat.lt_of_le_of_lt ht ht'm
  have hent : ∀ a, a < m → ∀ c, c < d →
      ipEnt t t' i a c = ipEnt r s k a c := by
    intro a ha c hc
    rw [← ground.matOf_entry ([] : List Nat) 0 m d (ipEnt t t' i) a c ha hc,
      ← ground.matOf_entry ([] : List Nat) 0 m d (ipEnt r s k) a c ha hc,
      ← ipGrid_matOf m d t t' i, ← ipGrid_matOf m d r s k, he]
  have hik : i = k := by
    by_cases hc : i = k
    · exact hc
    · have hz := hent t htm i hid
      rw [ipEnt_at t t' i t i rfl, ipEnt_off r s k t i hc,
        ground.eqBeqOf (rfl : t = t)] at hz
      exact absurd hz (fun hcc => one_add_ne_zero _ hcc)
  have hpair := pair_eq_of_ind m t t' r s ht ht'm hr hsm (fun a ha => by
    have hz := hent a ha i hid
    rw [ipEnt_at t t' i a i rfl, hik, ipEnt_at r s k a k rfl] at hz
    exact hz)
  exact ⟨hpair.1, hpair.2, hik⟩

/-- A column occupied twice at one argument and vacant elsewhere
reads the pairwise inner product's entries at the repeated
argument. -/
private theorem ent_diag_read (m d : Nat) (E : Nat → Nat → Nat)
    (t i : Nat) (hEt : E t i = 2)
    (hzero : ∀ a, a < m → ¬ a = t → E a i = 0)
    (hoff : ∀ a, a < m → ∀ k, k < d → ¬ k = i → E a k = 0) :
    ground.matOf m d E = ipGrid m d t t i := by
  refine matOf_eq_ipGrid m d E t t i (fun a ha k hk => ?_)
  by_cases hki : k = i
  · rw [hki, ipEnt_at t t i a i rfl]
    by_cases hat : a = t
    · rw [hat, hEt, ground.eqBeqOf (rfl : t = t)]
      rfl
    · rw [hzero a ha hat, ground.neBeqOf hat]
      rfl
  · rw [hoff a ha k hk hki, ipEnt_off t t i a k hki]

/-- A column occupied once at each of two distinct arguments and
vacant elsewhere reads the pairwise inner product's entries. -/
private theorem ent_pair_read (m d : Nat) (E : Nat → Nat → Nat)
    (t t' i : Nat) (hne : ¬ t = t')
    (hEt : E t i = 1) (hEt' : E t' i = 1)
    (hzero : ∀ a, a < m → ¬ a = t → ¬ a = t' → E a i = 0)
    (hoff : ∀ a, a < m → ∀ k, k < d → ¬ k = i → E a k = 0) :
    ground.matOf m d E = ipGrid m d t t' i := by
  refine matOf_eq_ipGrid m d E t t' i (fun a ha k hk => ?_)
  by_cases hki : k = i
  · rw [hki, ipEnt_at t t' i a i rfl]
    by_cases hat : a = t
    · rw [hat, hEt, ground.eqBeqOf (rfl : t = t), ground.neBeqOf hne]
      rfl
    · by_cases hat' : a = t'
      · rw [hat', hEt', ground.eqBeqOf (rfl : t' = t'),
          ground.neBeqOf (fun hc => hne hc.symm)]
        rfl
      · rw [hzero a ha hat hat', ground.neBeqOf hat, ground.neBeqOf hat']
        rfl
  · rw [hoff a ha k hk hki, ipEnt_off t t' i a k hki]

/-- A degree-two entry formula at even coordinate totals reads a
pairwise inner product's monomial: the coordinate totals exchange
with the argument totals, so one coordinate carries the whole
degree and its column holds two units, at one argument or at
two. -/
private theorem deg2_classify_ent (m d : Nat) (E : Nat → Nat → Nat)
    (hdeg : ground.sumNat ((ground.matOf m d E).map ground.sumNat) = 2)
    (heven : ∀ i, i < d → dirTot i (ground.matOf m d E) % 2 = 0) :
    ∃ t t' i, t ≤ t' ∧ t' < m ∧ i < d
      ∧ ground.matOf m d E = ipGrid m d t t' i := by
  have hdegF : ground.famFold Nat.add 0
      (fun t => ground.famFold Nat.add 0 (E t) (List.range d))
      (List.range m) = 2 := by
    rw [← hdeg, deg_matOf m d E,
      ground.sumMap
        (fun t => ground.sumNat ((List.range d).map (E t))) (List.range m)]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun t => (ground.sumMap (E t) (List.range d)).symm)
      (List.range m)
  have hswap : ground.famFold Nat.add 0
      (fun i => ground.famFold Nat.add 0 (fun t => E t i) (List.range m))
      (List.range d) = 2 := by
    rw [← ground.famFold_swap E (List.range m) (List.range d)]
    exact hdegF
  have hcolT : ∀ i, i < d → dirTot i (ground.matOf m d E)
      = ground.famFold Nat.add 0 (fun t => E t i) (List.range m) := by
    intro i hi
    rw [dirTot_matOf m d i hi E,
      ground.sumMap (fun t => E t i) (List.range m)]
  obtain ⟨i0, hi0m, hi0p⟩ := ground.famFold_pos_witness
    (fun i => ground.famFold Nat.add 0 (fun t => E t i) (List.range m))
    (List.range d) (by rw [hswap]; exact Nat.succ_pos 1)
  have hi0d : i0 < d := ground.ltOfMem hi0m
  have hcol2 : ground.famFold Nat.add 0 (fun t => E t i0) (List.range m)
      = 2 := by
    refine Nat.le_antisymm ?_ (two_le_of_even_pos ?_ hi0p)
    · rw [← hswap]
      exact ground.famFold_mem_le
        (fun i => ground.famFold Nat.add 0 (fun t => E t i) (List.range m))
        (List.range d) i0 (ground.mem_of_countOf_pos _ _ hi0m)
    · rw [← hcolT i0 hi0d]
      exact heven i0 hi0d
  have hpickcol : ground.famFold Nat.add 0
      (fun i => ground.famFold Nat.add 0 (fun t => E t i) (List.range m))
      (List.range d)
      = ground.famFold Nat.add 0 (fun t => E t i0) (List.range m) := by
    rw [hswap, hcol2]
  have hoffcol : ∀ k, k < d → ¬ k = i0 →
      ground.famFold Nat.add 0 (fun t => E t k) (List.range m) = 0 :=
    fun k hk hki => fold_rest_zero _ (List.range d) i0 hi0m hpickcol k
      (ground.countOf_range_pos hk) hki
  have hentzero : ∀ a, a < m → ∀ k, k < d → ¬ k = i0 → E a k = 0 := by
    intro a ha k hk hki
    have hle := ground.famFold_mem_le (fun t => E t k) (List.range m) a
      (ground.memRange ha)
    rw [hoffcol k hk hki] at hle
    exact Nat.le_antisymm hle (Nat.zero_le _)
  obtain ⟨t0, ht0m, ht0p⟩ := ground.famFold_pos_witness (fun t => E t i0)
    (List.range m) (by rw [hcol2]; exact Nat.succ_pos 1)
  have ht0lt : t0 < m := ground.ltOfMem ht0m
  have ht0le : E t0 i0 ≤ 2 := by
    have hle := ground.famFold_mem_le (fun t => E t i0) (List.range m) t0
      (ground.mem_of_countOf_pos _ _ ht0m)
    rw [hcol2] at hle
    exact hle
  cases one_or_two ht0p ht0le with
  | inr hE2 =>
    refine ⟨t0, t0, i0, Nat.le_refl t0, ht0lt, hi0d, ?_⟩
    refine ent_diag_read m d E t0 i0 hE2 (fun a ha hat => ?_) hentzero
    exact fold_rest_zero (fun t => E t i0) (List.range m) t0 ht0m
      (by rw [hcol2, hE2]) a (ground.countOf_range_pos ha) hat
  | inl hE1 =>
    have hsplitrow : ground.famFold Nat.add 0 (fun t => E t i0)
        (List.range m)
        = E t0 i0 + ground.famFold Nat.add 0 (fun t => E t i0)
            (ground.eraseFirst t0 (List.range m)) :=
      ground.famFold_eraseFirst Nat.add 0 Nat.add_comm Nat.add_assoc
        (fun t => E t i0) (List.range m) t0 ht0m
    rw [hcol2, hE1] at hsplitrow
    have hrest : ground.famFold Nat.add 0 (fun t => E t i0)
        (ground.eraseFirst t0 (List.range m)) = 1 :=
      (ground.addCancelL 1 (show (1 : Nat) + 1 = 1 + _ from hsplitrow)).symm
    obtain ⟨t1, ht1m, ht1p⟩ := ground.famFold_pos_witness (fun t => E t i0)
      (ground.eraseFirst t0 (List.range m))
      (by rw [hrest]; exact Nat.succ_pos 0)
    have ht1ne : ¬ t1 = t0 := by
      intro hee
      have hz : ground.countOf t0
          (ground.eraseFirst t0 (List.range m)) = 0 := by
        have hs := ground.countOf_eraseFirst_self (List.range m) t0
          (ground.countOf_range_pos ht0lt)
        rw [ground.countOf_range_one ht0lt] at hs
        exact (Nat.succ.inj hs).symm
      rw [hee, hz] at ht1m
      exact absurd ht1m (Nat.lt_irrefl 0)
    have ht1lt : t1 < m := ground.ltOfMem
      (by rw [← ground.countOf_eraseFirst_ne (List.range m) t0 t1 ht1ne]
          exact ht1m)
    have hE1' : E t1 i0 = 1 := by
      have hle := ground.famFold_mem_le (fun t => E t i0)
        (ground.eraseFirst t0 (List.range m)) t1
        (ground.mem_of_countOf_pos _ _ ht1m)
      rw [hrest] at hle
      exact Nat.le_antisymm hle ht1p
    have hrest0 : ∀ a, a < m → ¬ a = t0 → ¬ a = t1 → E a i0 = 0 := by
      intro a ha hat0 hat1
      refine fold_rest_zero (fun t => E t i0)
        (ground.eraseFirst t0 (List.range m)) t1 ht1m
        (by rw [hrest, hE1']) a ?_ hat1
      rw [ground.countOf_eraseFirst_ne (List.range m) t0 a hat0]
      exact ground.countOf_range_pos ha
    cases Nat.lt_or_ge t0 t1 with
    | inl hlt =>
      exact ⟨t0, t1, i0, Nat.le_of_lt hlt, ht1lt, hi0d,
        ent_pair_read m d E t0 t1 i0 (fun hc => ht1ne hc.symm) hE1 hE1'
          hrest0 hentzero⟩
    | inr hge =>
      exact ⟨t1, t0, i0, hge, ht0lt, hi0d,
        ent_pair_read m d E t1 t0 i0 ht1ne hE1' hE1
          (fun a ha h1 h2 => hrest0 a ha h2 h1) hentzero⟩

/-- A degree-two grid of the box at even coordinate totals is a
pairwise inner product's monomial at two arguments in order. -/
private theorem deg2_classify (m d : Nat) (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox m d 2))
    (heven : ∀ i, i < d → dirTot i g % 2 = 0) :
    ∃ t t' i, t ≤ t' ∧ t' < m ∧ i < d ∧ g = ipGrid m d t t' i := by
  have hreads := momBox_reads m d 2 g hg
  have hgE : g = ground.matOf m d (entOf g) :=
    matOf_entOf m d g hreads.1 hreads.2.1
  obtain ⟨t, t', i, h1, h2, h3, h4⟩ :=
    deg2_classify_ent m d (entOf g)
      (by rw [← hgE]; exact hreads.2.2)
      (fun i hi => by rw [← hgE]; exact heven i hi)
  exact ⟨t, t', i, h1, h2, h3, by rw [hgE]; exact h4⟩

/-- The ordered argument pairs' term list: one term per pair of
arguments below the count in order. -/
private def guardedSpan (m : Nat) (P : Nat → Nat → BPair) : List BPair :=
  (List.range m).flatMap (fun r => (List.range m).flatMap (fun s =>
    if r ≤ s then [P r s] else []))

/-- The term list's fold is the guarded double fold over the two
argument ranges. -/
private theorem guardedSpan_fold (m : Nat) (P : Nat → Nat → BPair) :
    (BPair.sum (guardedSpan m P)).oneValue
      (ground.famFold BPair.add BPair.unit (fun r =>
        ground.famFold BPair.add BPair.unit (fun s =>
          if r ≤ s then P r s else BPair.unit) (List.range m))
        (List.range m)) := by
  refine BPair.oneValue_trans
    (BPair.sum_flatMap (fun r => (List.range m).flatMap (fun s =>
      if r ≤ s then [P r s] else [])) (List.range m)) ?_
  refine ground.foldB_congr_members _ _ (List.range m) (fun r _ => ?_)
  refine BPair.oneValue_trans
    (BPair.sum_flatMap (fun s => if r ≤ s then [P r s] else [])
      (List.range m)) ?_
  refine ground.foldB_congr_members _ _ (List.range m) (fun s _ => ?_)
  by_cases hrs : r ≤ s
  · rw [if_pos hrs, if_pos hrs]
    exact BPair.unit_add (P r s)
  · rw [if_neg hrs, if_neg hrs]
    exact BPair.oneValue_refl BPair.unit

/-- A term list at the sum's unit on every ordered pair folds to
the sum's unit. -/
private theorem guardedSpan_unit (m : Nat) (P : Nat → Nat → BPair)
    (h : ∀ r s, r < m → s < m → r ≤ s → (P r s).oneValue BPair.unit) :
    (BPair.sum (guardedSpan m P)).oneValue BPair.unit := by
  refine BPair.oneValue_trans (guardedSpan_fold m P) ?_
  refine ground.foldB_nullRange _ m (fun r hr => ?_)
  refine ground.foldB_nullRange _ m (fun s hs => ?_)
  by_cases hrs : r ≤ s
  · rw [if_pos hrs]
    exact h r s hr hs hrs
  · rw [if_neg hrs]
    exact BPair.oneValue_refl BPair.unit

/-- A term list at the sum's unit off one ordered pair folds to
that pair's own term. -/
private theorem guardedSpan_pick (m : Nat) (P : Nat → Nat → BPair)
    (t t' : Nat) (htt' : t ≤ t') (htm : t < m) (ht'm : t' < m) (X : BPair)
    (hon : (P t t').oneValue X)
    (hoff : ∀ r s, r < m → s < m → r ≤ s → ¬ (r = t ∧ s = t') →
      (P r s).oneValue BPair.unit) :
    (BPair.sum (guardedSpan m P)).oneValue X := by
  refine BPair.oneValue_trans (guardedSpan_fold m P) ?_
  refine ground.foldB_pickRange _ t X m htm ?_ ?_
  · refine ground.foldB_pickRange _ t' X m ht'm ?_ ?_
    · rw [if_pos htt']
      exact hon
    · intro s hs hst'
      by_cases hts : t ≤ s
      · rw [if_pos hts]
        exact hoff t s htm hs hts (fun hc => hst' hc.2)
      · rw [if_neg hts]
        exact BPair.oneValue_refl BPair.unit
  · intro r hr hrt
    refine ground.foldB_nullRange _ m (fun s hs => ?_)
    by_cases hrs : r ≤ s
    · rw [if_pos hrs]
      exact hoff r s hr hs hrs
        (fun hc => hrt hc.1)
    · rw [if_neg hrs]
      exact BPair.oneValue_refl BPair.unit

/-- The degree-two span: an invariant family's coefficient at a
grid of the degree-two box is the guarded sum over the ordered
argument pairs of the family's coefficient at that pair's first
monomial against the pair's inner product family read at the grid.
Off the even class the grid's odd coordinate sends both sides to
the sum's unit; on it the grid is one pairwise monomial
(`deg2_classify`), the transposition carries its coordinate to the
first, and the sum's every further term reads the sum's unit at
the monomials' distinctness (`ipGrid_inj`) —
`thm:restoration`'s rings-coincide clause. -/
theorem deg2_span (m d : Nat) (c : List (List Nat) → BPair)
    (h : bdInvAt m d 2 c) (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox m d 2)) :
    (c g).oneValue (BPair.sum ((List.range m).flatMap (fun r =>
      (List.range m).flatMap (fun s =>
        if r ≤ s then
          [c (ipGrid m d r s 0) * ipFam m d r s g]
        else [])))) := by
  show (c g).oneValue (BPair.sum (guardedSpan m
    (fun r s => c (ipGrid m d r s 0) * ipFam m d r s g)))
  cases hodd : ((List.range d).any (fun i => !(dirTot i g % 2 == 0))) with
  | true =>
    obtain ⟨i, him, hib⟩ := ground.mem_of_any _ (List.range d) hodd
    have hid : i < d := ground.ltOfMemRange him
    have hne : ¬ dirTot i g % 2 = 0 := by
      intro he
      rw [he] at hib
      exact Bool.noConfusion hib
    refine BPair.oneValue_trans
      (bdInv_vanish m d 2 c h g hg i hid (mod_two_odd hne))
      (BPair.oneValue_symm ?_)
    refine guardedSpan_unit m _ (fun r s hrm hsm _ => ?_)
    show (c (ipGrid m d r s 0) * ipFam m d r s g).oneValue BPair.unit
    have hvac : ipFam m d r s g = BPair.unit := by
      refine ipFam_vac m d r s g ?_
      cases hany : ((List.range d).any
          (fun i => g == ipGrid m d r s i)) with
      | false => rfl
      | true =>
        obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) hany
        have hkd : k < d := ground.ltOfMemRange hkm
        have hgk : g = ipGrid m d r s k := gridBeqEq hkb
        refine absurd (show dirTot i g % 2 = 0 from ?_) hne
        by_cases hik : i = k
        · rw [hgk, hik, ipGrid_dirTot_at m d r s k hkd,
            if_pos hrm, if_pos hsm]
        · rw [hgk, ipGrid_dirTot_off m d r s k i hid hik]
    rw [hvac]
    exact BPair.mul_unit _
  | false =>
    have heven : ∀ i, i < d → dirTot i g % 2 = 0 := by
      intro i hi
      have hf := any_range_false d _ hodd i hi
      cases hv : (dirTot i g % 2 == 0) with
      | true => exact ground.beqEqOf hv
      | false =>
        rw [hv] at hf
        exact Bool.noConfusion hf
    obtain ⟨t, t', i0, htt', ht'm, hi0d, hgeq⟩ :=
      deg2_classify m d g hg heven
    have htm : t < m := Nat.lt_of_le_of_lt htt' ht'm
    have htrans : (c g).oneValue (c (ipGrid m d t t' 0)) := by
      by_cases hi0 : i0 = 0
      · rw [hgeq, hi0]
        exact BPair.oneValue_refl _
      · have hmove : swapDirs 0 i0 (ipGrid m d t t' i0)
            = ipGrid m d t t' 0 := by
          rw [swapDirs_ipGrid m d t t' i0 0 i0 (fun he => hi0 he.symm)
              (Nat.lt_of_le_of_lt (Nat.zero_le i0) hi0d) hi0d,
            ground.swapIx_snd hi0]
        have hsw := bdInv_swap m d 2 c h (ipGrid m d t t' i0)
          (by rw [← hgeq]; exact hg) 0 i0
          (Nat.pos_of_ne_zero hi0) hi0d
        rw [hmove] at hsw
        rw [hgeq]
        exact BPair.oneValue_symm hsw
    refine BPair.oneValue_trans htrans (BPair.oneValue_symm ?_)
    refine guardedSpan_pick m _ t t' htt' htm ht'm
      (c (ipGrid m d t t' 0)) ?_ ?_
    · show (c (ipGrid m d t t' 0) * ipFam m d t t' g).oneValue
        (c (ipGrid m d t t' 0))
      have hocc : ipFam m d t t' g = BPair.ofNat 1 := by
        show (if (List.range d).any (fun i => g == ipGrid m d t t' i)
          then BPair.ofNat 1 else BPair.unit) = BPair.ofNat 1
        rw [ground.any_of_mem _ (ground.memRange hi0d)
          (show (g == ipGrid m d t t' i0) = true from by
            rw [hgeq]
            exact gridEqBeq _)]
        rfl
      rw [hocc]
      exact BPair.mul_ofNat_one _
    · intro r s hrm hsm hrs hpair
      show (c (ipGrid m d r s 0) * ipFam m d r s g).oneValue BPair.unit
      have hvac : ipFam m d r s g = BPair.unit := by
        refine ipFam_vac m d r s g ?_
        cases hany : ((List.range d).any
            (fun i => g == ipGrid m d r s i)) with
        | false => rfl
        | true =>
          obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) hany
          have hgk : ipGrid m d t t' i0 = ipGrid m d r s k := by
            rw [← hgeq]
            exact gridBeqEq hkb
          obtain ⟨h1, h2, _⟩ := ipGrid_inj m d t t' r s i0 k htt' ht'm
            hi0d hrs hsm hgk
          exact absurd ⟨h1.symm, h2.symm⟩ hpair
      rw [hvac]
      exact BPair.mul_unit _


/-! The degree-four span at one argument: at the box's degree four
an invariant family's doubled coefficient is read off two
coefficients alone, the cross monomial's and the quartic's
(`thm:restoration`'s rings-coincide clause one degree up).  The
mechanism is the degree-two walk's own at the coordinate
arithmetic.  A grid of the box at one argument is one row, and its
coordinate totals are that row's entries (`dirTot_matOf1`), so at
the even class the entries are evens summing to four: one
coordinate at four — the quartic's monomial — or two coordinates
at two — the cross monomial, the pairwise inner product's two
monomials joined (`deg4_classify`).  The transposition carries the
quartic's monomial to the first coordinate in one move and the
cross monomial to the first two in two (`bdInv_swap` at the named
grids, the second move at the moved grid's own membership), and at
each the two families read their counts off the splittings: the
quartic's monomial holds one splitting and the cross monomial two
(`prodIP_qu`, `prodIP_cross`).  The cross coefficient enters the
display against its own memberwise swap, so it withdraws to the
sum's unit at the quartic's monomial (`swap_join_read`) and doubles
at the cross monomial — the two reads the identity's two sides. -/

/-- A key below the unit count is the first. -/
private theorem lt_one_zero : ∀ {t : Nat}, t < 1 → t = 0
  | 0, _ => rfl
  | k + 1, h =>
    absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero k)

/-- A joined pair is never vacant. -/
private theorem add_two_ne_zero (x : Nat) : ¬ x + 2 = 0 :=
  fun hc => Nat.noConfusion hc

/-- A pair joined on the left is never vacant. -/
private theorem two_add_ne_zero (x : Nat) : ¬ 2 + x = 0 := by
  rw [Nat.add_comm]
  exact add_two_ne_zero x

/-- An even count between two and four is one of them. -/
private theorem two_or_four : ∀ {n : Nat},
    n % 2 = 0 → 2 ≤ n → n ≤ 4 → n = 2 ∨ n = 4
  | 0, _, h, _ => absurd h (by decide +kernel)
  | 1, _, h, _ => absurd h (by decide +kernel)
  | 2, _, _, _ => Or.inl rfl
  | 3, h, _, _ => absurd h (by decide +kernel)
  | 4, _, _, _ => Or.inr rfl
  | k + 5, _, _, h =>
    absurd (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
      (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))))
      (Nat.not_succ_le_zero k)

/-- The doubled occupancy joined with itself reads the quartic's. -/
private theorem ite_four_split (b : Bool) :
    (if b then (4 : Nat) else 0)
      = ((if b then 1 else 0) + (if b then 1 else 0))
        + ((if b then 1 else 0) + (if b then 1 else 0)) := by
  cases b <;> rfl

/-- A guarded pair of tests at most one of which holds splits its
occupancy into the two guarded counts. -/
private theorem ite_or_split (b1 b2 b3 b4 : Bool)
    (h : ¬ (b2 = true ∧ b4 = true)) :
    (if (b1 && b2) || (b3 && b4) then (1 : Nat) else 0)
      = (if b2 then (if b1 then 1 else 0) else 0)
        + (if b4 then (if b3 then 1 else 0) else 0) := by
  cases b2 with
  | true =>
    cases b4 with
    | true => exact absurd ⟨rfl, rfl⟩ h
    | false => cases b1 <;> cases b3 <;> rfl
  | false => cases b4 <;> cases b1 <;> cases b3 <;> rfl

/-- The grid at an entry formula carries the direction count at
every argument's row. -/
private theorem matOf_rows (m d : Nat) (F : Nat → Nat → Nat) :
    ((ground.matOf m d F).all (fun row => row.length == d)) = true := by
  show (((List.range m).map (fun t => (List.range d).map (F t))).all
    (fun row => row.length == d)) = true
  rw [ground.all_map (fun t => (List.range d).map (F t))
    (fun row => row.length == d) (List.range m)]
  refine ground.all_range_intro m (fun t _ => ?_)
  show (((List.range d).map (F t)).length == d) = true
  rw [ground.length_map, ground.length_range]
  exact ground.eqBeqOf rfl

/-- A grid at one argument reads its coordinate total at the entry
formula's own entry. -/
private theorem dirTot_matOf1 (d i : Nat) (hi : i < d)
    (F : Nat → Nat → Nat) : dirTot i (ground.matOf 1 d F) = F 0 i := by
  rw [dirTot_matOf 1 d i hi F]
  rfl

/-- A grid at one argument reads its total degree at its row's
own. -/
private theorem deg_matOf1 (d : Nat) (F : Nat → Nat → Nat) :
    ground.sumNat ((ground.matOf 1 d F).map ground.sumNat)
      = ground.sumNat ((List.range d).map (F 0)) := by
  rw [deg_matOf 1 d F]
  rfl

/-- The pairwise inner product's entry formula at the one argument
reads the doubled occupancy at its own coordinate. -/
private theorem ipEnt_row0 (i k : Nat) :
    ipEnt 0 0 i 0 k = if k == i then 2 else 0 := by
  show (if (0 : Nat) == 0 && k == i then 1 else 0)
      + (if (0 : Nat) == 0 && k == i then 1 else 0)
    = if k == i then 2 else 0
  rw [ite_and_right ((0 : Nat) == 0) (k == i) 1]
  by_cases hki : k = i
  · rw [ground.eqBeqOf hki]
    rfl
  · rw [ground.neBeqOf hki]
    rfl

/-- The quartic's entry formula at the one argument reads its
degree at its own coordinate. -/
private theorem quEnt_row0 (i k : Nat) :
    quEnt 0 i 0 k = if k == i then 4 else 0 := by
  show (if (0 : Nat) == 0 && k == i then 4 else 0)
    = if k == i then 4 else 0
  rw [ite_and_right ((0 : Nat) == 0) (k == i) 4]
  by_cases hki : k = i
  · rw [ground.eqBeqOf hki]
    rfl
  · rw [ground.neBeqOf hki]
    rfl

/-- The cross monomial's entry formula: the two pairwise inner
products' entries joined. -/
private def crossEnt (i j : Nat) (t k : Nat) : Nat :=
  ipEnt 0 0 i t k + ipEnt 0 0 j t k

/-- The cross monomial is the grid at its entry formula. -/
private theorem crossG_matOf (d i j : Nat) :
    crossG d i j
      = ground.matOf 1 d (crossEnt i j) := by
  show addG (ipGrid 1 d 0 0 i) (ipGrid 1 d 0 0 j)
    = ground.matOf 1 d (crossEnt i j)
  rw [ipGrid_matOf 1 d 0 0 i, ipGrid_matOf 1 d 0 0 j]
  exact addG_matOf 1 d (ipEnt 0 0 i) (ipEnt 0 0 j)

/-- The cross monomial's entry formula at the one argument reads
the doubled occupancies at its two coordinates. -/
private theorem crossEnt_row0 (i j k : Nat) :
    crossEnt i j 0 k
      = (if k == i then 2 else 0) + (if k == j then 2 else 0) := by
  show ipEnt 0 0 i 0 k + ipEnt 0 0 j 0 k
    = (if k == i then 2 else 0) + (if k == j then 2 else 0)
  rw [ipEnt_row0 i k, ipEnt_row0 j k]

/-- The quartic's monomial reads its degree at its own coordinate
and nothing at the others. -/
private theorem quGrid_ent (d k c : Nat) (hc : c < d) :
    ground.getAt 0 (ground.getAt ([] : List Nat) (quGrid 1 d 0 k) 0) c
      = if c == k then 4 else 0 := by
  rw [quGrid_matOf 1 d 0 k,
    ground.matOf_entry ([] : List Nat) 0 1 d (quEnt 0 k) 0 c (Nat.succ_pos 0) hc]
  exact quEnt_row0 k c

/-- The cross monomial reads the doubled occupancies at its two
coordinates. -/
private theorem crossG_ent (d i j c : Nat) (hc : c < d) :
    ground.getAt 0 (ground.getAt ([] : List Nat)
        (crossG d i j) 0) c
      = (if c == i then 2 else 0) + (if c == j then 2 else 0) := by
  rw [crossG_matOf d i j,
    ground.matOf_entry ([] : List Nat) 0 1 d (crossEnt i j) 0 c (Nat.succ_pos 0) hc]
  exact crossEnt_row0 i j c

/-- The quartic's monomial is the splitting at its own argument
and coordinate repeated. -/
private theorem quGrid_eq_addG (m d r c : Nat) :
    quGrid m d r c = addG (ipGrid m d r r c) (ipGrid m d r r c) := by
  rw [ipGrid_matOf m d r r c, addG_matOf m d (ipEnt r r c) (ipEnt r r c),
    quGrid_matOf m d r c]
  refine ground.matOf_congr m d (quEnt r c) _ (fun t l _ _ => ?_)
  show (if t == r && l == c then (4 : Nat) else 0)
    = ((if t == r && l == c then 1 else 0)
        + (if t == r && l == c then 1 else 0))
      + ((if t == r && l == c then 1 else 0)
        + (if t == r && l == c then 1 else 0))
  exact ite_four_split (t == r && l == c)

/-- A splitting is blind to its two factors' order. -/
private theorem addG_ip_comm (m d r s t u i j : Nat) :
    addG (ipGrid m d r s i) (ipGrid m d t u j)
      = addG (ipGrid m d t u j) (ipGrid m d r s i) := by
  rw [ipGrid_matOf m d r s i, ipGrid_matOf m d t u j,
    addG_matOf m d (ipEnt r s i) (ipEnt t u j),
    addG_matOf m d (ipEnt t u j) (ipEnt r s i)]
  refine ground.matOf_congr m d _ _ (fun t' l _ _ => ?_)
  show ipEnt r s i t' l + ipEnt t u j t' l
    = ipEnt t u j t' l + ipEnt r s i t' l
  rw [Nat.add_comm]

/-- The quartic's monomial is the cross monomial at a repeated
coordinate. -/
private theorem quGrid_eq_crossG (d k : Nat) :
    quGrid 1 d 0 k = crossG d k k :=
  quGrid_eq_addG 1 d 0 k

/-- The cross monomial is blind to its two coordinates' order. -/
private theorem crossG_comm (d a b : Nat) :
    crossG d a b = crossG d b a :=
  addG_ip_comm 1 d 0 0 0 0 a b

/-- A doubled occupancy read at a coordinate names one of the two
carried coordinates. -/
private theorem two_ind_cases (x u v : Nat)
    (h : (2 : Nat)
      = (if x == u then 2 else 0) + (if x == v then 2 else 0)) :
    x = u ∨ x = v := by
  by_cases hu : x = u
  · exact Or.inl hu
  · by_cases hv : x = v
    · exact Or.inr hv
    · rw [ground.neBeqOf hu, ground.neBeqOf hv] at h
      exact absurd (show (2 : Nat) = 0 from h)
        (fun hc => Nat.noConfusion hc)

/-- The comparison of the quartic's monomial against a splitting:
the splitting's two coordinates are the quartic's own. -/
private theorem qu_beq_cross (d i j k : Nat) (hi : i < d)
    (hj : j < d) :
    (quGrid 1 d 0 k == crossG d i j)
      = ((i == k) && (j == k)) := by
  refine boolEqOfImp (fun hb => ?_) (fun hb => ?_)
  · have heq := gridBeqEq hb
    have hik : i = k := by
      by_cases hc : i = k
      · exact hc
      · refine absurd ?_ (two_add_ne_zero (if i == j then 2 else 0))
        have h1 : ground.getAt 0 (ground.getAt ([] : List Nat)
              (quGrid 1 d 0 k) 0) i
            = ground.getAt 0 (ground.getAt ([] : List Nat)
              (crossG d i j) 0) i := by
          rw [heq]
        rw [quGrid_ent d k i hi, crossG_ent d i j i hi,
          ground.neBeqOf hc, ground.eqBeqOf (rfl : i = i)] at h1
        exact (show (0 : Nat) = 2 + (if i == j then 2 else 0) from h1).symm
    have hjk : j = k := by
      by_cases hc : j = k
      · exact hc
      · refine absurd ?_ (add_two_ne_zero (if j == i then 2 else 0))
        have h1 : ground.getAt 0 (ground.getAt ([] : List Nat)
              (quGrid 1 d 0 k) 0) j
            = ground.getAt 0 (ground.getAt ([] : List Nat)
              (crossG d i j) 0) j := by
          rw [heq]
        rw [quGrid_ent d k j hj, crossG_ent d i j j hj,
          ground.neBeqOf hc, ground.eqBeqOf (rfl : j = j)] at h1
        exact (show (0 : Nat) = (if j == i then 2 else 0) + 2 from h1).symm
    rw [ground.eqBeqOf hik, ground.eqBeqOf hjk]
    rfl
  · have hs := ground.andSplitB hb
    rw [ground.beqEqOf hs.1, ground.beqEqOf hs.2, ← quGrid_eq_crossG d k]
    exact gridEqBeq _

/-- The comparison of two splittings: the second's two coordinates
are the first's, in either order. -/
private theorem cross_beq_cross (d a b i j : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) :
    (crossG d a b
        == crossG d i j)
      = (((i == a) && (j == b)) || ((i == b) && (j == a))) := by
  refine boolEqOfImp (fun hbe => ?_) (fun hbe => ?_)
  · have heq := gridBeqEq hbe
    have hent : ∀ c, c < d →
        (if c == a then 2 else 0) + (if c == b then 2 else 0)
          = (if c == i then 2 else 0) + (if c == j then 2 else 0) := by
      intro c hc
      rw [← crossG_ent d a b c hc, ← crossG_ent d i j c hc, heq]
    have hA : (2 : Nat)
        = (if a == i then 2 else 0) + (if a == j then 2 else 0) := by
      have h1 := hent a ha
      rw [ground.eqBeqOf (rfl : a = a), ground.neBeqOf hab] at h1
      exact h1
    have hB : (2 : Nat)
        = (if b == i then 2 else 0) + (if b == j then 2 else 0) := by
      have h1 := hent b hb
      rw [ground.neBeqOf (fun hc => hab hc.symm),
        ground.eqBeqOf (rfl : b = b)] at h1
      exact h1
    cases two_ind_cases a i j hA with
    | inl hai =>
      have hbi : ¬ b = i := fun he => hab (hai.trans he.symm)
      cases two_ind_cases b i j hB with
      | inl hc => exact absurd hc hbi
      | inr hbj =>
        rw [ground.eqBeqOf hai.symm, ground.eqBeqOf hbj.symm]
        rfl
    | inr haj =>
      have hbj : ¬ b = j := fun he => hab (haj.trans he.symm)
      cases two_ind_cases b i j hB with
      | inl hbi =>
        rw [ground.eqBeqOf hbi.symm, ground.eqBeqOf haj.symm]
        cases ((i == a) && (j == b)) <;> rfl
      | inr hc => exact absurd hc hbj
  · cases h1 : ((i == a) && (j == b)) with
    | true =>
      have hs := ground.andSplitB h1
      rw [ground.beqEqOf hs.1, ground.beqEqOf hs.2]
      exact gridEqBeq _
    | false =>
      rw [h1] at hbe
      have hs := ground.andSplitB
        (show ((i == b) && (j == a)) = true from hbe)
      rw [ground.beqEqOf hs.1, ground.beqEqOf hs.2, crossG_comm d a b]
      exact gridEqBeq _

/-- The quartic's monomial holds a splitting exactly at the pair of
coordinates both at its own. -/
private theorem qu_cross_ind (d i j k : Nat) (hi : i < d)
    (hj : j < d) :
    (if quGrid 1 d 0 k == crossG d i j
      then (1 : Nat) else 0)
      = if j == k then (if i == k then 1 else 0) else 0 := by
  rw [qu_beq_cross d i j k hi hj, ite_and_right (i == k) (j == k) 1]

/-- A splitting's occupancy at a cross monomial splits into its two
coordinate orders. -/
private theorem cross_cross_ind (d a b i j : Nat) (hab : ¬ a = b)
    (ha : a < d) (hb : b < d) :
    (if crossG d a b
        == crossG d i j
      then (1 : Nat) else 0)
      = (if j == b then (if i == a then 1 else 0) else 0)
        + (if j == a then (if i == b then 1 else 0) else 0) := by
  rw [cross_beq_cross d a b i j hab ha hb]
  refine ite_or_split (i == a) (j == b) (i == b) (j == a) (fun hc => ?_)
  exact hab ((ground.beqEqOf hc.2).symm.trans (ground.beqEqOf hc.1))

/-- The quartic's monomial carries one splitting: the coordinate
pair both at its own. -/
private theorem prodIP_qu (d k : Nat) (hk : k < d) :
    prodIP 1 d 0 0 0 0 (quGrid 1 d 0 k) = BPair.ofNat 1 := by
  have hinner : ∀ i, 0 < ground.countOf i (List.range d) →
      ground.sumNat ((List.range d).map (fun j =>
        if quGrid 1 d 0 k == crossG d i j
        then 1 else 0))
        = (if i == k then 1 else 0) := by
    intro i hi
    have hid : i < d := ground.ltOfMem hi
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun j => if quGrid 1 d 0 k
        == crossG d i j then 1 else 0)
      (fun j => if j == k then (if i == k then 1 else 0) else 0)
      (List.range d)
      (fun j hj => qu_cross_ind d i j k hid (ground.ltOfMem hj)))) ?_
    rw [sumNat_ind_range k (if i == k then 1 else 0) d, if_pos hk]
  have hcount : dblSum d (fun i j =>
      if quGrid 1 d 0 k == crossG d i j
      then 1 else 0) = 1 := by
    refine Eq.trans (dblSum_fold d _) ?_
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun i => ground.sumNat ((List.range d).map (fun j =>
        if quGrid 1 d 0 k == crossG d i j
        then 1 else 0)))
      (fun i => if i == k then 1 else 0) (List.range d) hinner)) ?_
    rw [sumNat_ind_range k 1 d, if_pos hk]
  show BPair.ofNat (dblSum d (fun i j =>
    if quGrid 1 d 0 k == crossG d i j
    then 1 else 0)) = BPair.ofNat 1
  rw [hcount]

/-- The cross monomial carries two splittings: its two coordinates
in either order. -/
private theorem prodIP_cross (d a b : Nat) (hab : ¬ a = b) (ha : a < d)
    (hb : b < d) :
    prodIP 1 d 0 0 0 0 (crossG d a b)
      = BPair.ofNat 2 := by
  have hinner : ∀ i, 0 < ground.countOf i (List.range d) →
      ground.sumNat ((List.range d).map (fun j =>
        if crossG d a b
          == crossG d i j then 1 else 0))
        = (if i == a then 1 else 0) + (if i == b then 1 else 0) := by
    intro i _
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun j => if crossG d a b
        == crossG d i j then 1 else 0)
      (fun j => (if j == b then (if i == a then 1 else 0) else 0)
        + (if j == a then (if i == b then 1 else 0) else 0))
      (List.range d)
      (fun j _ => cross_cross_ind d a b i j hab ha hb))) ?_
    refine Eq.trans (sumNat_map_add
      (fun j => if j == b then (if i == a then 1 else 0) else 0)
      (fun j => if j == a then (if i == b then 1 else 0) else 0)
      (List.range d)) ?_
    rw [sumNat_ind_range b (if i == a then 1 else 0) d,
      sumNat_ind_range a (if i == b then 1 else 0) d, if_pos hb, if_pos ha]
  have hcount : dblSum d (fun i j =>
      if crossG d a b
        == crossG d i j
      then 1 else 0) = 2 := by
    refine Eq.trans (dblSum_fold d _) ?_
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun i => ground.sumNat ((List.range d).map (fun j =>
        if crossG d a b
          == crossG d i j then 1 else 0)))
      (fun i => (if i == a then 1 else 0) + (if i == b then 1 else 0))
      (List.range d) hinner)) ?_
    refine Eq.trans (sumNat_map_add (fun i => if i == a then 1 else 0)
      (fun i => if i == b then 1 else 0) (List.range d)) ?_
    rw [sumNat_ind_range a 1 d, sumNat_ind_range b 1 d, if_pos ha, if_pos hb]
  show BPair.ofNat (dblSum d (fun i j =>
    if crossG d a b
      == crossG d i j
    then 1 else 0)) = BPair.ofNat 2
  rw [hcount]

/-- The quartic family is occupied at its own monomial. -/
private theorem quFam_qu (d k : Nat) (hk : k < d) :
    quFam 1 d 0 (quGrid 1 d 0 k) = BPair.ofNat 1 := by
  show (if (List.range d).any (fun i => quGrid 1 d 0 k == quGrid 1 d 0 i)
    then BPair.ofNat 1 else BPair.unit) = BPair.ofNat 1
  rw [ground.any_of_mem _ (ground.memRange hk)
    (gridEqBeq (quGrid 1 d 0 k))]
  rfl

/-- The quartic family is the sum's unit at a cross monomial: two
distinct coordinates carry no quartic. -/
private theorem quFam_cross (d i j : Nat) (hij : ¬ i = j) (hi : i < d)
    (hj : j < d) :
    quFam 1 d 0 (crossG d i j)
      = BPair.unit := by
  refine quFam_vac 1 d 0 _ ?_
  cases hany : ((List.range d).any (fun k =>
      crossG d i j == quGrid 1 d 0 k)) with
  | false => rfl
  | true =>
    obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) hany
    have hkd : k < d := ground.ltOfMemRange hkm
    have hbeq : (quGrid 1 d 0 k
        == crossG d i j) = true := by
      rw [← gridBeqEq hkb]
      exact gridEqBeq _
    rw [qu_beq_cross d i j k hi hj] at hbeq
    have hs := ground.andSplitB hbeq
    exact absurd ((ground.beqEqOf hs.1).trans
      (ground.beqEqOf hs.2).symm) hij

/-- The quartic's monomial has total degree four at an argument
below the argument count. -/
private theorem quGrid_deg (m d r c : Nat) (hc : c < d) :
    ground.sumNat ((quGrid m d r c).map ground.sumNat)
      = if r < m then 4 else 0 := by
  have hinner : ∀ t : Nat,
      ground.sumNat ((List.range d).map (quEnt r c t))
        = (if t == r then 4 else 0) := by
    intro t
    rw [ground.map_congr_all (quEnt r c t)
        (fun k => if k == c then (if t == r then 4 else 0) else 0)
        (fun k => by
          show (if t == r && k == c then (4 : Nat) else 0)
            = if k == c then (if t == r then 4 else 0) else 0
          rw [ite_and_right (t == r) (k == c) 4])
        (List.range d),
      sumNat_ind_range c (if t == r then 4 else 0) d, if_pos hc]
  rw [quGrid_matOf m d r c, deg_matOf m d (quEnt r c),
    ground.map_congr_all
      (fun t => ground.sumNat ((List.range d).map (quEnt r c t)))
      (fun t => if t == r then 4 else 0) hinner (List.range m),
    sumNat_ind_range r 4 m]

/-- The quartic's monomial at a coordinate below the direction
count is a member of the degree-four box at one argument. -/
private theorem mem_quGrid (d k : Nat) (hk : k < d) :
    0 < ground.countOf (quGrid 1 d 0 k) (momBox 1 d 4) := by
  refine mem_momBox 1 d 4 (quGrid 1 d 0 k) ?_ ?_ ?_
  · rw [quGrid_matOf 1 d 0 k]
    exact ground.matOf_length 1 d (quEnt 0 k)
  · rw [quGrid_matOf 1 d 0 k]
    exact matOf_rows 1 d (quEnt 0 k)
  · rw [quGrid_deg 1 d 0 k hk, if_pos (Nat.succ_pos 0)]

/-- The cross monomial at two coordinates below the direction count
is a member of the degree-four box at one argument. -/
private theorem mem_crossG (d i j : Nat) (hi : i < d) (hj : j < d) :
    0 < ground.countOf (crossG d i j)
      (momBox 1 d 4) := by
  refine mem_momBox 1 d 4 _ ?_ ?_ ?_
  · rw [crossG_matOf d i j]
    exact ground.matOf_length 1 d (crossEnt i j)
  · rw [crossG_matOf d i j]
    exact matOf_rows 1 d (crossEnt i j)
  · show ground.sumNat ((addG (ipGrid 1 d 0 0 i)
        (ipGrid 1 d 0 0 j)).map ground.sumNat) = 4
    rw [deg_addG_ip 1 d 0 0 0 0 i j, ipGrid_deg 1 d 0 0 i hi,
      ipGrid_deg 1 d 0 0 j hj, if_pos (Nat.succ_pos 0)]

/-- The pairwise inner product's monomial at one argument reads two
along its own coordinate and nothing at the others. -/
private theorem ip1_dirTot (d i p : Nat) (hi : i < d) (hp : p < d) :
    dirTot p (ipGrid 1 d 0 0 i) = if p = i then 2 else 0 := by
  by_cases hpi : p = i
  · rw [if_pos hpi, hpi, ipGrid_dirTot_at 1 d 0 0 i hi,
      if_pos (Nat.succ_pos 0)]
  · rw [if_neg hpi, ipGrid_dirTot_off 1 d 0 0 i p hp hpi]

/-- The quartic's monomial at one argument reads four along its own
coordinate and nothing at the others. -/
private theorem qu1_dirTot (d k p : Nat) (hk : k < d) (hp : p < d) :
    dirTot p (quGrid 1 d 0 k) = if p = k then 4 else 0 := by
  by_cases hpk : p = k
  · rw [if_pos hpk, hpk, quGrid_dirTot_at 1 d 0 k hk,
      if_pos (Nat.succ_pos 0)]
  · rw [if_neg hpk, quGrid_dirTot_off 1 d 0 k p hp hpk]

/-- The cross monomial's total along a coordinate is its two
factors' own. -/
private theorem cross_dirTot (d i j p : Nat) (hi : i < d) (hj : j < d)
    (hp : p < d) :
    dirTot p (crossG d i j)
      = (if p = i then 2 else 0) + (if p = j then 2 else 0) := by
  show dirTot p (addG (ipGrid 1 d 0 0 i) (ipGrid 1 d 0 0 j))
    = (if p = i then 2 else 0) + (if p = j then 2 else 0)
  rw [dirTot_addG_ip 1 d 0 0 0 0 i j p hp, ip1_dirTot d i p hi hp,
    ip1_dirTot d j p hj hp]

/-- The product family is the sum's unit at a grid of odd total
along a coordinate: every splitting's grid is even at every
coordinate. -/
private theorem prodIP_odd (d : Nat) (g : List (List Nat)) (p : Nat)
    (hp : p < d) (hodd : ¬ dirTot p g % 2 = 0) :
    prodIP 1 d 0 0 0 0 g = BPair.unit := by
  refine prodIP_vac 1 d 0 0 0 0 g ?_
  cases hany : ((List.range d).any (fun i => (List.range d).any (fun j =>
      g == addG (ipGrid 1 d 0 0 i) (ipGrid 1 d 0 0 j)))) with
  | false => rfl
  | true =>
    obtain ⟨i, him, hi2⟩ := ground.mem_of_any _ (List.range d) hany
    have hid : i < d := ground.ltOfMemRange him
    obtain ⟨j, hjm, hjb⟩ := ground.mem_of_any _ (List.range d) hi2
    have hjd : j < d := ground.ltOfMemRange hjm
    refine absurd (show dirTot p g % 2 = 0 from ?_) hodd
    rw [gridBeqEq hjb]
    show dirTot p (crossG d i j) % 2 = 0
    rw [cross_dirTot d i j p hid hjd hp]
    by_cases hpi : p = i
    · by_cases hpj : p = j
      · rw [if_pos hpi, if_pos hpj]
      · rw [if_pos hpi, if_neg hpj]
    · by_cases hpj : p = j
      · rw [if_neg hpi, if_pos hpj]
      · rw [if_neg hpi, if_neg hpj]

/-- The quartic family is the sum's unit at a grid of odd total
along a coordinate: its monomials are even at every coordinate. -/
private theorem quFam_odd (d : Nat) (g : List (List Nat)) (p : Nat)
    (hp : p < d) (hodd : ¬ dirTot p g % 2 = 0) :
    quFam 1 d 0 g = BPair.unit := by
  refine quFam_vac 1 d 0 g ?_
  cases hany : ((List.range d).any (fun k => g == quGrid 1 d 0 k)) with
  | false => rfl
  | true =>
    obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) hany
    have hkd : k < d := ground.ltOfMemRange hkm
    refine absurd (show dirTot p g % 2 = 0 from ?_) hodd
    rw [gridBeqEq hkb, qu1_dirTot d k p hkd hp]
    by_cases hpk : p = k
    · rw [if_pos hpk]
    · rw [if_neg hpk]

/-- A row holding its whole degree at one coordinate reads the
quartic's monomial. -/
private theorem ent_qu_read (d : Nat) (E : Nat → Nat → Nat) (i : Nat)
    (hE : E 0 i = 4) (hz : ∀ k, k < d → ¬ k = i → E 0 k = 0) :
    ground.matOf 1 d E = quGrid 1 d 0 i := by
  rw [quGrid_matOf 1 d 0 i]
  refine ground.matOf_congr 1 d E (quEnt 0 i) (fun t k ht hk => ?_)
  rw [lt_one_zero ht, quEnt_row0 i k]
  by_cases hki : k = i
  · rw [hki, hE, ground.eqBeqOf (rfl : i = i)]
    rfl
  · rw [hz k hk hki, ground.neBeqOf hki]
    rfl

/-- A row holding two at each of two distinct coordinates reads the
cross monomial. -/
private theorem ent_cross_read (d : Nat) (E : Nat → Nat → Nat)
    (i j : Nat) (hij : ¬ i = j) (hEi : E 0 i = 2) (hEj : E 0 j = 2)
    (hz : ∀ k, k < d → ¬ k = i → ¬ k = j → E 0 k = 0) :
    ground.matOf 1 d E = crossG d i j := by
  rw [crossG_matOf d i j]
  refine ground.matOf_congr 1 d E (crossEnt i j) (fun t k ht hk => ?_)
  rw [lt_one_zero ht, crossEnt_row0 i j k]
  by_cases hki : k = i
  · rw [hki, hEi, ground.eqBeqOf (rfl : i = i), ground.neBeqOf hij]
    rfl
  · by_cases hkj : k = j
    · rw [hkj, hEj, ground.eqBeqOf (rfl : j = j),
        ground.neBeqOf (fun hc => hij hc.symm)]
      rfl
    · rw [hz k hk hki hkj, ground.neBeqOf hki, ground.neBeqOf hkj]
      rfl

/-- A degree-four grid of the box at one argument whose coordinate
totals are all even is the quartic's monomial at one coordinate or
the cross monomial at two: the row's even entries sum to four, so
one entry carries four or two entries carry two each. -/
private theorem deg4_classify (d : Nat) (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox 1 d 4))
    (heven : ∀ i, i < d → dirTot i g % 2 = 0) :
    (∃ k, k < d ∧ g = quGrid 1 d 0 k)
      ∨ (∃ i j, i < j ∧ j < d
          ∧ g = crossG d i j) := by
  have hreads := momBox_reads 1 d 4 g hg
  have hgE : g = ground.matOf 1 d (entOf g) :=
    matOf_entOf 1 d g hreads.1 hreads.2.1
  have hF : ground.famFold Nat.add 0 (entOf g 0) (List.range d) = 4 := by
    rw [← ground.sumMap (entOf g 0) (List.range d),
      ← deg_matOf1 d (entOf g), ← hgE]
    exact hreads.2.2
  have hEv : ∀ i, i < d → entOf g 0 i % 2 = 0 := by
    intro i hi
    rw [← dirTot_matOf1 d i hi (entOf g), ← hgE]
    exact heven i hi
  obtain ⟨i0, hi0m, hi0p⟩ := ground.famFold_pos_witness (entOf g 0)
    (List.range d) (by rw [hF]; exact Nat.succ_pos 3)
  have hi0d : i0 < d := ground.ltOfMem hi0m
  have hi0le : entOf g 0 i0 ≤ 4 := by
    have hle := ground.famFold_mem_le (entOf g 0) (List.range d) i0
      (ground.mem_of_countOf_pos _ _ hi0m)
    rw [hF] at hle
    exact hle
  cases two_or_four (hEv i0 hi0d)
      (two_le_of_even_pos (hEv i0 hi0d) hi0p) hi0le with
  | inr hE4 =>
    refine Or.inl ⟨i0, hi0d, ?_⟩
    rw [hgE]
    refine ent_qu_read d (entOf g) i0 hE4 (fun k hk hki => ?_)
    exact fold_rest_zero (entOf g 0) (List.range d) i0 hi0m
      (by rw [hF, hE4]) k (ground.countOf_range_pos hk) hki
  | inl hE2 =>
    have hsplit : ground.famFold Nat.add 0 (entOf g 0) (List.range d)
        = entOf g 0 i0 + ground.famFold Nat.add 0 (entOf g 0)
            (ground.eraseFirst i0 (List.range d)) :=
      ground.famFold_eraseFirst Nat.add 0 Nat.add_comm Nat.add_assoc
        (entOf g 0) (List.range d) i0 hi0m
    rw [hF, hE2] at hsplit
    have hrest : ground.famFold Nat.add 0 (entOf g 0)
        (ground.eraseFirst i0 (List.range d)) = 2 :=
      (ground.addCancelL 2 (show (2 : Nat) + 2 = 2 + _ from hsplit)).symm
    obtain ⟨j0, hj0m, hj0p⟩ := ground.famFold_pos_witness (entOf g 0)
      (ground.eraseFirst i0 (List.range d))
      (by rw [hrest]; exact Nat.succ_pos 1)
    have hj0ne : ¬ j0 = i0 := by
      intro hee
      have hz : ground.countOf i0
          (ground.eraseFirst i0 (List.range d)) = 0 := by
        have hs := ground.countOf_eraseFirst_self (List.range d) i0
          (ground.countOf_range_pos hi0d)
        rw [ground.countOf_range_one hi0d] at hs
        exact (Nat.succ.inj hs).symm
      rw [hee, hz] at hj0m
      exact absurd hj0m (Nat.lt_irrefl 0)
    have hj0d : j0 < d := ground.ltOfMem
      (by rw [← ground.countOf_eraseFirst_ne (List.range d) i0 j0 hj0ne]
          exact hj0m)
    have hj0le : entOf g 0 j0 ≤ 2 := by
      have hle := ground.famFold_mem_le (entOf g 0)
        (ground.eraseFirst i0 (List.range d)) j0
        (ground.mem_of_countOf_pos _ _ hj0m)
      rw [hrest] at hle
      exact hle
    have hEj2 : entOf g 0 j0 = 2 :=
      Nat.le_antisymm hj0le
        (two_le_of_even_pos (hEv j0 hj0d) hj0p)
    have hrest0 : ∀ k, k < d → ¬ k = i0 → ¬ k = j0 →
        entOf g 0 k = 0 := by
      intro k hk hki hkj
      refine fold_rest_zero (entOf g 0)
        (ground.eraseFirst i0 (List.range d)) j0 hj0m
        (by rw [hrest, hEj2]) k ?_ hkj
      rw [ground.countOf_eraseFirst_ne (List.range d) i0 k hki]
      exact ground.countOf_range_pos hk
    cases Nat.lt_or_ge i0 j0 with
    | inl hlt =>
      refine Or.inr ⟨i0, j0, hlt, hj0d, ?_⟩
      rw [hgE]
      exact ent_cross_read d (entOf g) i0 j0 (Nat.ne_of_lt hlt) hE2 hEj2
        hrest0
    | inr hge =>
      have hlt : j0 < i0 := Nat.lt_of_le_of_ne hge hj0ne
      refine Or.inr ⟨j0, i0, hlt, hi0d, ?_⟩
      rw [hgE]
      exact ent_cross_read d (entOf g) j0 i0 (Nat.ne_of_lt hlt) hEj2 hE2
        (fun k hk h1 h2 => hrest0 k hk h2 h1)

/-- A datum joined with its memberwise swap reads the sum's
unit. -/
private theorem add_swap_null (x : BPair) :
    (x + x.swap).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_comm x x.swap))
    (BPair.swap_add_null (BPair.oneValue_refl x))

/-- A datum, a further sum and the datum's swap join to that sum's
own read. -/
private theorem swap_join_read (x y : BPair) :
    (x + (y + x.swap)).oneValue y :=
  BPair.oneValue_trans
    (BPair.oneValue_of_eq (by
      rw [BPair.add_comm y x.swap, ← BPair.add_assoc]))
    (BPair.oneValue_trans
      (BPair.add_congr (add_swap_null x) (BPair.oneValue_refl y))
      (BPair.unit_add y))

/-- The count two scales a datum to its own doubling. -/
private theorem mul_ofNat_two (x : BPair) :
    (x * BPair.ofNat 2).oneValue (x + x) := by
  refine BPair.oneValue_trans
    (BPair.mul_congr (BPair.oneValue_refl x)
      (show (BPair.ofNat 2).oneValue (BPair.ofNat 1 + BPair.ofNat 1)
        from BPair.ofNat_add 1 1)) ?_
  rw [BPair.left_distrib]
  exact BPair.add_congr (BPair.mul_ofNat_one x) (BPair.mul_ofNat_one x)

/-- A doubled datum is the datum rescaled by two. -/
private theorem add_self_scale (x : BPair) :
    x + x = x.scale (Pos.one + Pos.one) := by
  show BPair.mk (x.fst + x.fst) (x.snd + x.snd)
    = BPair.mk (x.fst * (Pos.one + Pos.one)) (x.snd * (Pos.one + Pos.one))
  rw [ground.left_distrib, ground.left_distrib, ground.mul_one,
    ground.mul_one]

/-- A doubled datum at the sum's unit is the datum's own read: the
rescaling reflects the balance. -/
private theorem add_self_unit {x : BPair}
    (h : (x + x).oneValue BPair.unit) : x.oneValue BPair.unit := by
  refine BPair.scale_cancel (w := Pos.one + Pos.one) ?_
  rw [← add_self_scale x]
  refine BPair.oneValue_trans h ?_
  show Pos.one + (BPair.unit.scale (Pos.one + Pos.one)).snd
    = (BPair.unit.scale (Pos.one + Pos.one)).fst + Pos.one
  show Pos.one + Pos.one * (Pos.one + Pos.one)
    = Pos.one * (Pos.one + Pos.one) + Pos.one
  exact ground.add_comm _ _

/-- The degree-four span at one argument: an invariant family's
doubled coefficient at a grid of the degree-four box is the cross
monomial's coefficient scaled by the grid's splitting count, joined
with the quartic's doubled coefficient against the cross
coefficient's memberwise swap scaled by the quartic family's read.
Off the even class the grid's odd coordinate sends both sides to
the sum's unit; on it the grid is the quartic's monomial or the
cross monomial (`deg4_classify`), the transposition carries it to
the named grid, and the two families read the splitting counts one
and two — the cross coefficient withdrawing against its swap at
the quartic's monomial and doubling at the cross monomial.  No
bound on the direction count is assumed: at one direction the
cross grid degenerates off the box and its coefficient still
withdraws, and at none the box is empty. -/
theorem deg4_span (d : Nat) (c : List (List Nat) → BPair)
    (h : bdInvAt 1 d 4 c) (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox 1 d 4)) :
    (c g + c g).oneValue
      (c (crossG d 0 1)
          * prodIP 1 d 0 0 0 0 g
        + (c (quGrid 1 d 0 0) + c (quGrid 1 d 0 0)
            + (c (crossG d 0 1)).swap)
          * quFam 1 d 0 g) := by
  cases hodd : ((List.range d).any (fun i => !(dirTot i g % 2 == 0))) with
  | true =>
    obtain ⟨p, hpm, hpb⟩ := ground.mem_of_any _ (List.range d) hodd
    have hpd : p < d := ground.ltOfMemRange hpm
    have hne : ¬ dirTot p g % 2 = 0 := by
      intro he
      rw [he] at hpb
      exact Bool.noConfusion hpb
    have hcg : (c g).oneValue BPair.unit :=
      bdInv_vanish 1 d 4 c h g hg p hpd (mod_two_odd hne)
    rw [prodIP_odd d g p hpd hne, quFam_odd d g p hpd hne]
    refine BPair.oneValue_trans (BPair.add_congr hcg hcg) ?_
    refine BPair.oneValue_trans (BPair.unit_add BPair.unit) ?_
    exact BPair.oneValue_symm (BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_unit _) (BPair.mul_unit _))
      (BPair.unit_add BPair.unit))
  | false =>
    have heven : ∀ i, i < d → dirTot i g % 2 = 0 := by
      intro i hi
      have hf := any_range_false d _ hodd i hi
      cases hv : (dirTot i g % 2 == 0) with
      | true => exact ground.beqEqOf hv
      | false =>
        rw [hv] at hf
        exact Bool.noConfusion hf
    cases deg4_classify d g hg heven with
    | inl hqu =>
      obtain ⟨k, hkd, hgk⟩ := hqu
      have htr : (c g).oneValue (c (quGrid 1 d 0 0)) := by
        by_cases hk0 : k = 0
        · rw [hgk, hk0]
          exact BPair.oneValue_refl _
        · have hmove : swapDirs 0 k (quGrid 1 d 0 k) = quGrid 1 d 0 0 := by
            rw [swapDirs_quGrid 1 d 0 k 0 k (fun he => hk0 he.symm)
                (Nat.lt_of_le_of_lt (Nat.zero_le k) hkd) hkd,
              ground.swapIx_snd hk0]
          have hsw := bdInv_swap 1 d 4 c h (quGrid 1 d 0 k)
            (by rw [← hgk]; exact hg) 0 k (Nat.pos_of_ne_zero hk0) hkd
          rw [hmove] at hsw
          rw [hgk]
          exact BPair.oneValue_symm hsw
      rw [show prodIP 1 d 0 0 0 0 g = BPair.ofNat 1 from by
          rw [hgk]; exact prodIP_qu d k hkd,
        show quFam 1 d 0 g = BPair.ofNat 1 from by
          rw [hgk]; exact quFam_qu d k hkd]
      refine BPair.oneValue_trans (BPair.add_congr htr htr) ?_
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr (BPair.mul_ofNat_one _) (BPair.mul_ofNat_one _))
        (swap_join_read _ _))
    | inr hcr =>
      obtain ⟨i, j, hij, hjd, hgij⟩ := hcr
      have hid : i < d := Nat.lt_trans hij hjd
      have hj0 : ¬ j = 0 := fun he =>
        Nat.not_succ_le_zero i (he ▸ hij)
      have hji : ¬ j = i := fun he => Nat.lt_irrefl i (he ▸ hij)
      have hstep1 : (c (crossG d 0 j)).oneValue
          (c g) := by
        by_cases hi0 : i = 0
        · rw [hgij, hi0]
          exact BPair.oneValue_refl _
        · have hmove : swapDirs 0 i
              (crossG d i j)
              = crossG d 0 j := by
            show swapDirs 0 i
                (addG (ipGrid 1 d 0 0 i) (ipGrid 1 d 0 0 j))
              = addG (ipGrid 1 d 0 0 0) (ipGrid 1 d 0 0 j)
            rw [swapDirs_addG_ip 1 d 0 0 0 0 0 i i j
                (fun he => hi0 he.symm)
                (Nat.lt_of_le_of_lt (Nat.zero_le i) hid) hid,
              ground.swapIx_snd hi0, ground.swapIx_off hj0 hji]
          have hsw := bdInv_swap 1 d 4 c h
            (crossG d i j)
            (by rw [← hgij]; exact hg) 0 i (Nat.pos_of_ne_zero hi0) hid
          rw [hmove] at hsw
          rw [hgij]
          exact hsw
      have hstep2 : (c (addG (ipGrid 1 d 0 0 0)
            (ipGrid 1 d 0 0 1))).oneValue
          (c (crossG d 0 j)) := by
        by_cases hj1 : j = 1
        · rw [hj1]
          exact BPair.oneValue_refl _
        · have h1j : 1 < j := Nat.lt_of_le_of_ne
            (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le i)) hij)
            (fun he => hj1 he.symm)
          have hmove : swapDirs 1 j
              (crossG d 0 j)
              = crossG d 0 1 := by
            show swapDirs 1 j
                (addG (ipGrid 1 d 0 0 0) (ipGrid 1 d 0 0 j))
              = addG (ipGrid 1 d 0 0 0) (ipGrid 1 d 0 0 1)
            rw [swapDirs_addG_ip 1 d 0 0 0 0 1 j 0 j
                (Nat.ne_of_lt h1j) (Nat.lt_trans h1j hjd) hjd,
              ground.swapIx_off (show ¬ (0 : Nat) = 1 by decide +kernel)
                (fun he => hj0 he.symm),
              ground.swapIx_snd hj1]
          have hsw := bdInv_swap 1 d 4 c h
            (crossG d 0 j)
            (mem_crossG d 0 j (Nat.lt_of_le_of_lt (Nat.zero_le j) hjd)
              hjd) 1 j h1j hjd
          rw [hmove] at hsw
          exact hsw
      have htr : (c g).oneValue
          (c (crossG d 0 1)) :=
        BPair.oneValue_symm (BPair.oneValue_trans hstep2 hstep1)
      rw [show prodIP 1 d 0 0 0 0 g = BPair.ofNat 2 from by
          rw [hgij]
          exact prodIP_cross d i j (Nat.ne_of_lt hij) hid hjd,
        show quFam 1 d 0 g = BPair.unit from by
          rw [hgij]
          exact quFam_cross d i j (Nat.ne_of_lt hij) hid hjd]
      refine BPair.oneValue_trans (BPair.add_congr htr htr) ?_
      exact BPair.oneValue_symm (BPair.oneValue_trans
        (BPair.add_congr (mul_ofNat_two _) (BPair.mul_unit _))
        (BPair.add_unit _))

/-- The two quartic invariants are independent: a combination at
the sum's unit on the degree-four box reads each coefficient at
that unit — the quartic's monomial ties the coefficients' join to
the unit, and the cross monomial reads the product family's
doubling there, the doubling reflecting to the coefficient
(`thm:restoration`'s multiplicity at the join `1 + 1 = 2`). -/
theorem deg4_indep (d : Nat) (hd : 2 ≤ d) (a b : BPair)
    (h : ∀ g : List (List Nat), 0 < ground.countOf g (momBox 1 d 4) →
      (a * quFam 1 d 0 g + b * prodIP 1 d 0 0 0 0 g).oneValue
        BPair.unit) :
    a.oneValue BPair.unit ∧ b.oneValue BPair.unit := by
  have h0d : 0 < d := Nat.lt_of_lt_of_le (by decide +kernel) hd
  have h1d : 1 < d := Nat.lt_of_lt_of_le (by decide +kernel) hd
  have hA := h (quGrid 1 d 0 0) (mem_quGrid d 0 h0d)
  rw [quFam_qu d 0 h0d, prodIP_qu d 0 h0d] at hA
  have hab : (a + b).oneValue BPair.unit :=
    BPair.oneValue_trans
      (BPair.oneValue_symm (BPair.add_congr (BPair.mul_ofNat_one a)
        (BPair.mul_ofNat_one b)))
      hA
  have hB := h (crossG d 0 1) (mem_crossG d 0 1 h0d h1d)
  rw [quFam_cross d 0 1 (by decide +kernel) h0d h1d,
    prodIP_cross d 0 1 (by decide +kernel) h0d h1d] at hB
  have hbb : (b + b).oneValue BPair.unit :=
    BPair.oneValue_trans (BPair.oneValue_symm (mul_ofNat_two b))
      (BPair.oneValue_trans
        (BPair.oneValue_symm (BPair.unit_add (b * BPair.ofNat 2)))
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_symm (BPair.mul_unit a))
            (BPair.oneValue_refl (b * BPair.ofNat 2)))
          hB))
  have hb : b.oneValue BPair.unit := add_self_unit hbb
  refine ⟨?_, hb⟩
  exact BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.add_unit a))
    (BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl a)
        (BPair.oneValue_symm hb))
      hab)

/-! The product span's break at every argument count
(`thm:restoration`'s two independent quartic invariants).  The two
witness grids are the diagonal quartic's monomial at the first
argument and first coordinate and the cross monomial at the first
argument's first two coordinates: each carries its whole degree
four in the first argument's row, so the four arguments' matches
against that row total four (`rowSum_addG_ip`) and a splitting
into two pairwise inner products matching either witness places
every one of its four arguments at the first (`quad_zero_of_four`)
— every further key of the quadruple family reads the sum's unit
there.  The surviving key's splitting count is one at the quartic's
monomial and two at the cross monomial, read off the coordinate
totals (`qu0_beq_split`, `cross01_beq_split`), and the quadruple
keyed union's fold collapses onto that key at both witnesses
(`quadSum_pick`).  The two reads tie the first coefficient to the
count one at the quartic's monomial and, through the doubling, to
the sum's unit at the cross monomial — a pair of reads no
coefficient carries. -/

/-- A grid's row at an argument below the argument count is the
entry formula's own row total. -/
private theorem rowSum_matOf (m d a : Nat) (ha : a < m)
    (F : Nat → Nat → Nat) :
    ground.sumNat (ground.getAt ([] : List Nat) (ground.matOf m d F) a)
      = ground.sumNat ((List.range d).map (F a)) := by
  show ground.sumNat (ground.getAt ([] : List Nat)
      ((List.range m).map (fun t => (List.range d).map (F t))) a)
    = ground.sumNat ((List.range d).map (F a))
  rw [ground.getAt_map_range ([] : List Nat)
    (fun t => (List.range d).map (F t)) m a, if_pos ha]

/-- The pairwise inner product's entry formula totals a row at its
two arguments' matches. -/
private theorem ipEnt_rowSum (d r s c a : Nat) (hc : c < d) :
    ground.sumNat ((List.range d).map (ipEnt r s c a))
      = (if a == r then 1 else 0) + (if a == s then 1 else 0) := by
  rw [ground.map_congr_all (ipEnt r s c a)
      (fun k => (if k == c then (if a == r then 1 else 0) else 0)
        + (if k == c then (if a == s then 1 else 0) else 0))
      (fun k => by
        show (if a == r && k == c then 1 else 0)
            + (if a == s && k == c then 1 else 0)
          = (if k == c then (if a == r then 1 else 0) else 0)
            + (if k == c then (if a == s then 1 else 0) else 0)
        rw [ite_and_right (a == r) (k == c) 1,
          ite_and_right (a == s) (k == c) 1])
      (List.range d),
    sumNat_map_add
      (fun k => if k == c then (if a == r then 1 else 0) else 0)
      (fun k => if k == c then (if a == s then 1 else 0) else 0)
      (List.range d),
    sumNat_ind_range c (if a == r then 1 else 0) d,
    sumNat_ind_range c (if a == s then 1 else 0) d,
    if_pos hc, if_pos hc]

/-- The quartic's entry formula totals a row at its own argument's
match. -/
private theorem quEnt_rowSum (d r c a : Nat) (hc : c < d) :
    ground.sumNat ((List.range d).map (quEnt r c a))
      = (if a == r then 4 else 0) := by
  rw [ground.map_congr_all (quEnt r c a)
      (fun k => if k == c then (if a == r then 4 else 0) else 0)
      (fun k => by
        show (if a == r && k == c then (4 : Nat) else 0)
          = if k == c then (if a == r then 4 else 0) else 0
        rw [ite_and_right (a == r) (k == c) 4])
      (List.range d),
    sumNat_ind_range c (if a == r then 4 else 0) d, if_pos hc]

/-- A product monomial's row at an argument below the count reads
its four arguments' matches. -/
private theorem rowSum_addG_ip (m d r s t u i j a : Nat) (ha : a < m)
    (hi : i < d) (hj : j < d) :
    ground.sumNat (ground.getAt ([] : List Nat)
        (addG (ipGrid m d r s i) (ipGrid m d t u j)) a)
      = ((if a == r then 1 else 0) + (if a == s then 1 else 0))
        + ((if a == t then 1 else 0) + (if a == u then 1 else 0)) := by
  rw [ipGrid_matOf m d r s i, ipGrid_matOf m d t u j,
    addG_matOf m d (ipEnt r s i) (ipEnt t u j),
    rowSum_matOf m d a ha
      (fun t' k => ipEnt r s i t' k + ipEnt t u j t' k),
    sumNat_map_add (ipEnt r s i a) (ipEnt t u j a) (List.range d),
    ipEnt_rowSum d r s i a hi, ipEnt_rowSum d t u j a hj]

/-- The quartic's monomial carries its whole degree in its own
argument's row. -/
private theorem rowSum_quGrid (m d r c a : Nat) (ha : a < m) (hc : c < d) :
    ground.sumNat (ground.getAt ([] : List Nat) (quGrid m d r c) a)
      = (if a == r then 4 else 0) := by
  rw [quGrid_matOf m d r c, rowSum_matOf m d a ha (quEnt r c),
    quEnt_rowSum d r c a hc]

/-- An occupancy read is at most one. -/
private theorem ind_le_one (b : Bool) : (if b then (1 : Nat) else 0) ≤ 1 := by
  cases b with
  | false => exact Nat.zero_le 1
  | true => exact Nat.le_refl 1

/-- Two counts at most one summing to two are each one. -/
private theorem eq_one_of_sum_two (x y : Nat) (hx : x ≤ 1) (hy : y ≤ 1)
    (h : x + y = 2) : x = 1 := by
  refine Nat.le_antisymm hx ?_
  have h1 : x + y ≤ x + 1 := Nat.add_le_add_left hy x
  rw [h] at h1
  exact ground.leCancelR 1 (show 1 + 1 ≤ x + 1 from h1)

/-- An occupancy read at the count one names its key. -/
private theorem eq_of_ind_one {x y : Nat}
    (h : (if x == y then (1 : Nat) else 0) = 1) : x = y :=
  ground.beqEqOf (ground.ind_one h)

/-- Four occupancy reads at the first key totalling four place
every one of the four keys at the first. -/
private theorem quad_zero_of_four {r s t u : Nat}
    (h : ((if (0 : Nat) == r then 1 else 0)
          + (if (0 : Nat) == s then 1 else 0))
        + ((if (0 : Nat) == t then 1 else 0)
          + (if (0 : Nat) == u then 1 else 0)) = 4) :
    r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0 := by
  have hle : ∀ x y : Nat, (if (0 : Nat) == x then 1 else 0)
      + (if (0 : Nat) == y then 1 else 0) ≤ 2 :=
    fun x y => Nat.add_le_add (ind_le_one ((0 : Nat) == x))
      (ind_le_one ((0 : Nat) == y))
  have hrs : (if (0 : Nat) == r then 1 else 0)
      + (if (0 : Nat) == s then 1 else 0) = 2 :=
    eq_two_of_sum_four _ _ (hle r s) (hle t u) h
  have htu : (if (0 : Nat) == t then 1 else 0)
      + (if (0 : Nat) == u then 1 else 0) = 2 := by
    rw [hrs] at h
    exact ground.addCancelL 2
      (show 2 + ((if (0 : Nat) == t then 1 else 0)
        + (if (0 : Nat) == u then 1 else 0)) = 2 + 2 from h)
  have hr1 : (if (0 : Nat) == r then 1 else 0) = 1 :=
    eq_one_of_sum_two _ _ (ind_le_one ((0 : Nat) == r))
      (ind_le_one ((0 : Nat) == s)) hrs
  have hs1 : (if (0 : Nat) == s then 1 else 0) = 1 :=
    eq_one_of_sum_two _ _ (ind_le_one ((0 : Nat) == s))
      (ind_le_one ((0 : Nat) == r)) (by rw [Nat.add_comm]; exact hrs)
  have ht1 : (if (0 : Nat) == t then 1 else 0) = 1 :=
    eq_one_of_sum_two _ _ (ind_le_one ((0 : Nat) == t))
      (ind_le_one ((0 : Nat) == u)) htu
  have hu1 : (if (0 : Nat) == u then 1 else 0) = 1 :=
    eq_one_of_sum_two _ _ (ind_le_one ((0 : Nat) == u))
      (ind_le_one ((0 : Nat) == t)) (by rw [Nat.add_comm]; exact htu)
  exact ⟨(eq_of_ind_one hr1).symm, (eq_of_ind_one hs1).symm,
    (eq_of_ind_one ht1).symm, (eq_of_ind_one hu1).symm⟩

/-- The product family is the sum's unit at a grid refusing every
splitting. -/
private theorem prodIP_off (m d r s t u : Nat) (g : List (List Nat))
    (h : ∀ i, i < d → ∀ j, j < d →
      ¬ g = addG (ipGrid m d r s i) (ipGrid m d t u j)) :
    prodIP m d r s t u g = BPair.unit := by
  refine prodIP_vac m d r s t u g ?_
  cases hany : ((List.range d).any (fun i => (List.range d).any (fun j =>
      g == addG (ipGrid m d r s i) (ipGrid m d t u j)))) with
  | false => rfl
  | true =>
    obtain ⟨i, him, hib⟩ := ground.mem_of_any _ (List.range d) hany
    have hid : i < d := ground.ltOfMemRange him
    obtain ⟨j, hjm, hjb⟩ := ground.mem_of_any _ (List.range d) hib
    have hjd : j < d := ground.ltOfMemRange hjm
    exact absurd (gridBeqEq hjb) (h i hid j hjd)

/-- A grid carrying its whole degree four in the first argument's
row refuses every splitting off the first argument: the four
arguments' matches total that row, so a matched splitting places
each of them at the first argument. -/
private theorem prodIP_row0_off (m d r s t u : Nat) (hm : 0 < m)
    (g : List (List Nat))
    (hrow : ground.sumNat (ground.getAt ([] : List Nat) g 0) = 4)
    (hne : ¬ (r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0)) :
    prodIP m d r s t u g = BPair.unit := by
  refine prodIP_off m d r s t u g (fun i hi j hj hgs => hne ?_)
  refine quad_zero_of_four ?_
  rw [← rowSum_addG_ip m d r s t u i j 0 hm hi hj, ← hgs]
  exact hrow

/-- The pairwise inner product's monomial at the first argument
twice reads two along its own coordinate and nothing further. -/
private theorem ip00_dirTot (m d c p : Nat) (hm : 0 < m) (hc : c < d)
    (hp : p < d) :
    dirTot p (ipGrid m d 0 0 c) = if p = c then 2 else 0 := by
  by_cases hpc : p = c
  · rw [if_pos hpc, hpc, ipGrid_dirTot_at m d 0 0 c hc, if_pos hm]
  · rw [if_neg hpc, ipGrid_dirTot_off m d 0 0 c p hp hpc]

/-- The quartic's monomial at the first argument reads four along
its own coordinate and nothing further. -/
private theorem qu0_dirTot (m d c p : Nat) (hm : 0 < m) (hc : c < d)
    (hp : p < d) :
    dirTot p (quGrid m d 0 c) = if p = c then 4 else 0 := by
  by_cases hpc : p = c
  · rw [if_pos hpc, hpc, quGrid_dirTot_at m d 0 c hc, if_pos hm]
  · rw [if_neg hpc, quGrid_dirTot_off m d 0 c p hp hpc]

/-- A splitting at the first argument reads two along each of its
two coordinates. -/
private theorem cross00_dirTot (m d i j p : Nat) (hm : 0 < m) (hi : i < d)
    (hj : j < d) (hp : p < d) :
    dirTot p (addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j))
      = (if p = i then 2 else 0) + (if p = j then 2 else 0) := by
  rw [dirTot_addG_ip m d 0 0 0 0 i j p hp, ip00_dirTot m d i p hm hi hp,
    ip00_dirTot m d j p hm hj hp]

/-- A doubled coordinate read at a coordinate names one of the two
carried coordinates, at the coordinates' own equality. -/
private theorem two_of_pair_cases (x u v : Nat)
    (h : (2 : Nat) = (if x = u then 2 else 0) + (if x = v then 2 else 0)) :
    x = u ∨ x = v := by
  by_cases hu : x = u
  · exact Or.inl hu
  · by_cases hv : x = v
    · exact Or.inr hv
    · rw [if_neg hu, if_neg hv] at h
      exact absurd (show (2 : Nat) = 0 from h) (fun hc => Nat.noConfusion hc)


/-- The quartic's monomial at the first argument and coordinate
holds a splitting exactly at the coordinate pair both at its
own. -/
private theorem qu0_beq_split (m d i j : Nat) (hm : 0 < m) (hd : 0 < d)
    (hi : i < d) (hj : j < d) :
    (quGrid m d 0 0 == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j))
      = ((i == 0) && (j == 0)) := by
  refine boolEqOfImp (fun hb => ?_) (fun hb => ?_)
  · have heq := gridBeqEq hb
    have hi0 : i = 0 := by
      by_cases hc : i = 0
      · exact hc
      · have h1 : dirTot i (quGrid m d 0 0)
            = dirTot i (addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)) := by
          rw [heq]
        rw [qu0_dirTot m d 0 i hm hd hi, if_neg hc,
          cross00_dirTot m d i j i hm hi hj hi,
          if_pos (rfl : i = i)] at h1
        exact absurd
          (show (0 : Nat) = 2 + (if i = j then 2 else 0) from h1).symm
          (two_add_ne_zero (if i = j then 2 else 0))
    have hj0 : j = 0 := by
      by_cases hc : j = 0
      · exact hc
      · have h1 : dirTot j (quGrid m d 0 0)
            = dirTot j (addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)) := by
          rw [heq]
        rw [qu0_dirTot m d 0 j hm hd hj, if_neg hc,
          cross00_dirTot m d i j j hm hi hj hj,
          if_pos (rfl : j = j)] at h1
        exact absurd
          (show (0 : Nat) = (if j = i then 2 else 0) + 2 from h1).symm
          (add_two_ne_zero (if j = i then 2 else 0))
    rw [ground.eqBeqOf hi0, ground.eqBeqOf hj0]
    rfl
  · have hs := ground.andSplitB hb
    rw [ground.beqEqOf hs.1, ground.beqEqOf hs.2, ← quGrid_eq_addG m d 0 0]
    exact gridEqBeq _

/-- The cross monomial at the first argument's first two
coordinates holds a splitting exactly at that coordinate pair in
either order. -/
private theorem cross01_beq_split (m d i j : Nat) (hm : 0 < m)
    (hd0 : 0 < d) (hd1 : 1 < d) (hi : i < d) (hj : j < d) :
    (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)
        == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j))
      = (((i == 0) && (j == 1)) || ((i == 1) && (j == 0))) := by
  refine boolEqOfImp (fun hb => ?_) (fun hb => ?_)
  · have heq := gridBeqEq hb
    have hA : (2 : Nat) = (if (0 : Nat) = i then 2 else 0)
        + (if (0 : Nat) = j then 2 else 0) := by
      have h1 : dirTot 0 (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
          = dirTot 0 (addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)) := by
        rw [heq]
      rw [cross00_dirTot m d 0 1 0 hm hd0 hd1 hd0,
        cross00_dirTot m d i j 0 hm hi hj hd0,
        if_pos (rfl : (0 : Nat) = 0),
        if_neg (show ¬ (0 : Nat) = 1 from fun hc => Nat.noConfusion hc)] at h1
      exact h1
    have hB : (2 : Nat) = (if (1 : Nat) = i then 2 else 0)
        + (if (1 : Nat) = j then 2 else 0) := by
      have h1 : dirTot 1 (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
          = dirTot 1 (addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)) := by
        rw [heq]
      rw [cross00_dirTot m d 0 1 1 hm hd0 hd1 hd1,
        cross00_dirTot m d i j 1 hm hi hj hd1,
        if_neg (show ¬ (1 : Nat) = 0 from fun hc => Nat.noConfusion hc),
        if_pos (rfl : (1 : Nat) = 1)] at h1
      exact h1
    cases two_of_pair_cases 0 i j hA with
    | inl h0i =>
      cases two_of_pair_cases 1 i j hB with
      | inl h1i =>
        exact absurd (h0i.trans h1i.symm) (fun hc => Nat.noConfusion hc)
      | inr h1j =>
        rw [ground.eqBeqOf h0i.symm, ground.eqBeqOf h1j.symm]
        rfl
    | inr h0j =>
      cases two_of_pair_cases 1 i j hB with
      | inl h1i =>
        rw [ground.eqBeqOf h1i.symm, ground.eqBeqOf h0j.symm]
        cases ((i == 0) && (j == 1)) <;> rfl
      | inr h1j =>
        exact absurd (h0j.trans h1j.symm) (fun hc => Nat.noConfusion hc)
  · cases h1 : ((i == 0) && (j == 1)) with
    | true =>
      have hs := ground.andSplitB h1
      rw [ground.beqEqOf hs.1, ground.beqEqOf hs.2]
      exact gridEqBeq _
    | false =>
      rw [h1] at hb
      have hs := ground.andSplitB
        (show ((i == 1) && (j == 0)) = true from hb)
      rw [ground.beqEqOf hs.1, ground.beqEqOf hs.2,
        addG_ip_comm m d 0 0 0 0 0 1]
      exact gridEqBeq _

/-- The quartic's monomial at the first argument and coordinate
carries one splitting. -/
private theorem prodIP_qu0 (m d : Nat) (hm : 0 < m) (hd : 0 < d) :
    prodIP m d 0 0 0 0 (quGrid m d 0 0) = BPair.ofNat 1 := by
  have hinner : ∀ i, 0 < ground.countOf i (List.range d) →
      ground.sumNat ((List.range d).map (fun j =>
        if quGrid m d 0 0 == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)
        then 1 else 0))
        = (if i == 0 then 1 else 0) := by
    intro i hi
    have hid : i < d := ground.ltOfMem hi
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun j => if quGrid m d 0 0
        == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j) then 1 else 0)
      (fun j => if j == 0 then (if i == 0 then 1 else 0) else 0)
      (List.range d)
      (fun j hj => by
        rw [qu0_beq_split m d i j hm hd hid (ground.ltOfMem hj),
          ite_and_right (i == 0) (j == 0) 1]))) ?_
    rw [sumNat_ind_range 0 (if i == 0 then 1 else 0) d, if_pos hd]
  have hcount : dblSum d (fun i j =>
      if quGrid m d 0 0 == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)
      then 1 else 0) = 1 := by
    refine Eq.trans (dblSum_fold d _) ?_
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun i => ground.sumNat ((List.range d).map (fun j =>
        if quGrid m d 0 0 == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)
        then 1 else 0)))
      (fun i => if i == 0 then 1 else 0) (List.range d) hinner)) ?_
    rw [sumNat_ind_range 0 1 d, if_pos hd]
  show BPair.ofNat (dblSum d (fun i j =>
    if quGrid m d 0 0 == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)
    then 1 else 0)) = BPair.ofNat 1
  rw [hcount]

/-- The cross monomial at the first argument's first two
coordinates carries two splittings. -/
private theorem prodIP_cross01 (m d : Nat) (hm : 0 < m) (hd0 : 0 < d)
    (hd1 : 1 < d) :
    prodIP m d 0 0 0 0 (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
      = BPair.ofNat 2 := by
  have hinner : ∀ i, 0 < ground.countOf i (List.range d) →
      ground.sumNat ((List.range d).map (fun j =>
        if addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)
          == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j) then 1 else 0))
        = (if i == 0 then 1 else 0) + (if i == 1 then 1 else 0) := by
    intro i hi
    have hid : i < d := ground.ltOfMem hi
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun j => if addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)
        == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j) then 1 else 0)
      (fun j => (if j == 1 then (if i == 0 then 1 else 0) else 0)
        + (if j == 0 then (if i == 1 then 1 else 0) else 0))
      (List.range d)
      (fun j hj => by
        rw [cross01_beq_split m d i j hm hd0 hd1 hid (ground.ltOfMem hj)]
        refine ite_or_split (i == 0) (j == 1) (i == 1) (j == 0)
          (fun hc => ?_)
        exact absurd ((ground.beqEqOf hc.1).symm.trans
          (ground.beqEqOf hc.2)) (fun hcc => Nat.noConfusion hcc)))) ?_
    refine Eq.trans (sumNat_map_add
      (fun j => if j == 1 then (if i == 0 then 1 else 0) else 0)
      (fun j => if j == 0 then (if i == 1 then 1 else 0) else 0)
      (List.range d)) ?_
    rw [sumNat_ind_range 1 (if i == 0 then 1 else 0) d,
      sumNat_ind_range 0 (if i == 1 then 1 else 0) d, if_pos hd1, if_pos hd0]
  have hcount : dblSum d (fun i j =>
      if addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)
        == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)
      then 1 else 0) = 2 := by
    refine Eq.trans (dblSum_fold d _) ?_
    refine Eq.trans (congrArg ground.sumNat (ground.map_congr_members
      (fun i => ground.sumNat ((List.range d).map (fun j =>
        if addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)
          == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j) then 1 else 0)))
      (fun i => (if i == 0 then 1 else 0) + (if i == 1 then 1 else 0))
      (List.range d) hinner)) ?_
    refine Eq.trans (sumNat_map_add (fun i => if i == 0 then 1 else 0)
      (fun i => if i == 1 then 1 else 0) (List.range d)) ?_
    rw [sumNat_ind_range 0 1 d, sumNat_ind_range 1 1 d, if_pos hd0, if_pos hd1]
  show BPair.ofNat (dblSum d (fun i j =>
    if addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)
      == addG (ipGrid m d 0 0 i) (ipGrid m d 0 0 j)
    then 1 else 0)) = BPair.ofNat 2
  rw [hcount]

/-- The quartic family is occupied at its own first monomial. -/
private theorem quFam_qu0 (m d : Nat) (hd : 0 < d) :
    quFam m d 0 (quGrid m d 0 0) = BPair.ofNat 1 := by
  show (if (List.range d).any (fun i => quGrid m d 0 0 == quGrid m d 0 i)
    then BPair.ofNat 1 else BPair.unit) = BPair.ofNat 1
  rw [ground.any_of_mem _ (ground.memRange hd) (gridEqBeq (quGrid m d 0 0))]
  rfl

/-- The quartic family is the sum's unit at the cross monomial:
that grid reads two along the first coordinate, off the quartic's
own four and nothing. -/
private theorem quFam_cross01 (m d : Nat) (hm : 0 < m) (hd0 : 0 < d)
    (hd1 : 1 < d) :
    quFam m d 0 (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
      = BPair.unit := by
  refine quFam_vac m d 0 _ ?_
  cases hany : ((List.range d).any (fun k =>
      addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1) == quGrid m d 0 k)) with
  | false => rfl
  | true =>
    obtain ⟨k, hkm, hkb⟩ := ground.mem_of_any _ (List.range d) hany
    have hkd : k < d := ground.ltOfMemRange hkm
    have h1 : dirTot 0 (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
        = dirTot 0 (quGrid m d 0 k) := by
      rw [gridBeqEq hkb]
    rw [cross00_dirTot m d 0 1 0 hm hd0 hd1 hd0,
      if_pos (rfl : (0 : Nat) = 0),
      if_neg (show ¬ (0 : Nat) = 1 from fun hc => Nat.noConfusion hc),
      qu0_dirTot m d k 0 hm hkd hd0] at h1
    by_cases hk : (0 : Nat) = k
    · rw [if_pos hk] at h1
      exact absurd (show (2 : Nat) = 4 from h1) (by decide +kernel)
    · rw [if_neg hk] at h1
      exact absurd (show (2 : Nat) = 0 from h1) (by decide +kernel)

/-- The quartic's monomial at the first argument and coordinate is
a member of the degree-four box. -/
private theorem mem_quGrid0 (m d : Nat) (hm : 0 < m) (hd : 0 < d) :
    0 < ground.countOf (quGrid m d 0 0) (momBox m d 4) := by
  refine mem_momBox m d 4 (quGrid m d 0 0) ?_ ?_ ?_
  · rw [quGrid_matOf m d 0 0]
    exact ground.matOf_length m d (quEnt 0 0)
  · rw [quGrid_matOf m d 0 0]
    exact matOf_rows m d (quEnt 0 0)
  · rw [quGrid_deg m d 0 0 hd, if_pos hm]

/-- The cross monomial at the first argument's first two
coordinates is a member of the degree-four box. -/
private theorem mem_cross01 (m d : Nat) (hm : 0 < m) (hd0 : 0 < d)
    (hd1 : 1 < d) :
    0 < ground.countOf (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
      (momBox m d 4) := by
  refine mem_momBox m d 4 _ ?_ ?_ ?_
  · rw [ipGrid_matOf m d 0 0 0, ipGrid_matOf m d 0 0 1,
      addG_matOf m d (ipEnt 0 0 0) (ipEnt 0 0 1)]
    exact ground.matOf_length m d _
  · rw [ipGrid_matOf m d 0 0 0, ipGrid_matOf m d 0 0 1,
      addG_matOf m d (ipEnt 0 0 0) (ipEnt 0 0 1)]
    exact matOf_rows m d _
  · rw [deg_addG_ip m d 0 0 0 0 0 1, ipGrid_deg m d 0 0 0 hd0,
      ipGrid_deg m d 0 0 1 hd1, if_pos hm]

/-- The quartic's monomial carries its whole degree in the first
argument's row. -/
private theorem row0_quGrid0 (m d : Nat) (hm : 0 < m) (hd : 0 < d) :
    ground.sumNat (ground.getAt ([] : List Nat) (quGrid m d 0 0) 0) = 4 :=
  rowSum_quGrid m d 0 0 0 hm hd

/-- The cross monomial carries its whole degree in the first
argument's row. -/
private theorem row0_cross01 (m d : Nat) (hm : 0 < m) (hd0 : 0 < d)
    (hd1 : 1 < d) :
    ground.sumNat (ground.getAt ([] : List Nat)
      (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)) 0) = 4 :=
  rowSum_addG_ip m d 0 0 0 0 0 1 0 hm hd0 hd1

/-- A keyed union's balance sum over the key range collapses onto
the first key's own. -/
private theorem sumFlat_pick (m : Nat) (hm : 0 < m) (K : Nat → List BPair)
    (X : BPair) (hon : (BPair.sum (K 0)).oneValue X)
    (hoff : ∀ k, k < m → ¬ k = 0 → (BPair.sum (K k)).oneValue BPair.unit) :
    (BPair.sum ((List.range m).flatMap K)).oneValue X :=
  BPair.oneValue_trans (BPair.sum_flatMap K (List.range m))
    (ground.foldB_pickRange (fun k => BPair.sum (K k)) 0 X m hm hon hoff)

/-- A keyed union's balance sum over the key range is the sum's
unit at a per-key unit read. -/
private theorem sumFlat_null (m : Nat) (K : Nat → List BPair)
    (hoff : ∀ k, k < m → (BPair.sum (K k)).oneValue BPair.unit) :
    (BPair.sum ((List.range m).flatMap K)).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.sum_flatMap K (List.range m))
    (ground.foldB_nullRange (fun k => BPair.sum (K k)) m hoff)

/-- A mapped family's balance sum over the key range collapses
onto the first key's own. -/
private theorem sumMap_pick (m : Nat) (hm : 0 < m) (F : Nat → BPair)
    (X : BPair) (hon : (F 0).oneValue X)
    (hoff : ∀ k, k < m → ¬ k = 0 → (F k).oneValue BPair.unit) :
    (BPair.sum ((List.range m).map F)).oneValue X :=
  BPair.oneValue_trans (BPair.sum_map F (List.range m))
    (ground.foldB_pickRange F 0 X m hm hon hoff)

/-- A mapped family's balance sum over the key range is the sum's
unit at a per-key unit read. -/
private theorem sumMap_null (m : Nat) (F : Nat → BPair)
    (hoff : ∀ k, k < m → (F k).oneValue BPair.unit) :
    (BPair.sum ((List.range m).map F)).oneValue BPair.unit :=
  BPair.oneValue_trans (BPair.sum_map F (List.range m))
    (ground.foldB_nullRange F m hoff)

/-- The quadruple keyed union's balance sum collapses onto the
first key at every one of its four coordinates: the family reads
the sum's unit at every further key, so each of the four folds
withdraws its tail. -/
private theorem quadSum_pick (m : Nat) (hm : 0 < m)
    (Q : Nat → Nat → Nat → Nat → BPair) (X : BPair)
    (hon : (Q 0 0 0 0).oneValue X)
    (hoff : ∀ r s t u, r < m → s < m → t < m → u < m →
      ¬ (r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0) →
      (Q r s t u).oneValue BPair.unit) :
    (BPair.sum ((List.range m).flatMap (fun r =>
      (List.range m).flatMap (fun s =>
        (List.range m).flatMap (fun t =>
          (List.range m).map (fun u => Q r s t u)))))).oneValue X := by
  refine sumFlat_pick m hm _ X ?_ (fun r hr hr0 => ?_)
  · refine sumFlat_pick m hm _ X ?_ (fun s hs hs0 => ?_)
    · refine sumFlat_pick m hm _ X ?_ (fun t ht ht0 => ?_)
      · refine sumMap_pick m hm _ X hon (fun u hu hu0 => ?_)
        exact hoff 0 0 0 u hm hm hm hu (fun hc => hu0 hc.2.2.2)
      · refine sumMap_null m _ (fun u hu => ?_)
        exact hoff 0 0 t u hm hm ht hu (fun hc => ht0 hc.2.2.1)
    · refine sumFlat_null m _ (fun t ht => sumMap_null m _ (fun u hu => ?_))
      exact hoff 0 s t u hm hs ht hu (fun hc => hs0 hc.2.1)
  · refine sumFlat_null m _ (fun s hs =>
      sumFlat_null m _ (fun t ht => sumMap_null m _ (fun u hu => ?_)))
    exact hoff r s t u hr hs ht hu (fun hc => hr0 hc.1)

/-- The quartic breaks the product span at every argument count:
at one argument or more and two directions or more no coefficient
family over the argument quadruples carries the diagonal quartic
against the pairwise inner products' products.  The two witness
grids are the quartic's own monomial at the first argument and the
cross monomial at that argument's first two coordinates; both
carry the whole degree in the first argument's row, so every
quadruple off the first argument reads the sum's unit
(`prodIP_row0_off`) and the display collapses onto the first
quadruple's coefficient (`quadSum_pick`).  There the quartic
family reads the count one against the splitting count one at the
first witness, tying that coefficient to the count one, and the
sum's unit against the splitting count two at the second, tying
its doubling — and with it the coefficient itself — to the sum's
unit.  The count one sits off that unit. -/
theorem quartic_breaks (m d : Nat) (hm : 1 ≤ m) (hd : 2 ≤ d)
    (w : Nat → Nat → Nat → Nat → BPair) :
    ¬ (∀ g : List (List Nat), 0 < ground.countOf g (momBox m d 4) →
      (quFam m d 0 g).oneValue
        (BPair.sum ((List.range m).flatMap (fun r =>
          (List.range m).flatMap (fun s =>
            (List.range m).flatMap (fun t =>
              (List.range m).map (fun u =>
                w r s t u * prodIP m d r s t u g))))))) := by
  intro H
  have hm0 : 0 < m := hm
  have hd0 : 0 < d := Nat.lt_of_lt_of_le (by decide +kernel) hd
  have hd1 : 1 < d := Nat.lt_of_lt_of_le (by decide +kernel) hd
  have hoffQ : ∀ (g : List (List Nat)),
      ground.sumNat (ground.getAt ([] : List Nat) g 0) = 4 →
      ∀ r s t u, ¬ (r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0) →
      (w r s t u * prodIP m d r s t u g).oneValue BPair.unit :=
    fun g hrow r s t u hne => by
      rw [prodIP_row0_off m d r s t u hm0 g hrow hne]
      exact BPair.mul_unit _
  have hA := H (quGrid m d 0 0) (mem_quGrid0 m d hm0 hd0)
  rw [quFam_qu0 m d hd0] at hA
  have hwA : (BPair.ofNat 1).oneValue (w 0 0 0 0) :=
    BPair.oneValue_trans hA
      (quadSum_pick m hm0
        (fun r s t u => w r s t u * prodIP m d r s t u (quGrid m d 0 0))
        (w 0 0 0 0)
        (by
          rw [prodIP_qu0 m d hm0 hd0]
          exact BPair.mul_ofNat_one _)
        (fun r s t u _ _ _ _ hne =>
          hoffQ (quGrid m d 0 0) (row0_quGrid0 m d hm0 hd0) r s t u hne))
  have hB := H (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
    (mem_cross01 m d hm0 hd0 hd1)
  rw [quFam_cross01 m d hm0 hd0 hd1] at hB
  have hwB : BPair.unit.oneValue (w 0 0 0 0 + w 0 0 0 0) :=
    BPair.oneValue_trans hB
      (quadSum_pick m hm0
        (fun r s t u => w r s t u * prodIP m d r s t u
          (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1)))
        (w 0 0 0 0 + w 0 0 0 0)
        (by
          rw [prodIP_cross01 m d hm0 hd0 hd1]
          exact mul_ofNat_two _)
        (fun r s t u _ _ _ _ hne =>
          hoffQ (addG (ipGrid m d 0 0 0) (ipGrid m d 0 0 1))
            (row0_cross01 m d hm0 hd0 hd1) r s t u hne))
  exact BPair.ofNat_one_off
    (BPair.oneValue_trans hwA
      (add_self_unit (BPair.oneValue_symm hwB)))

/-- A fold at an odd read holds an odd member, the walk its own
witness. -/
private theorem fold_odd_witness (F : Nat → Nat) :
    ∀ l : List Nat, (ground.famFold Nat.add 0 F l) % 2 = 1 →
      ∃ x, 0 < ground.countOf x l ∧ F x % 2 = 1
  | [], h => absurd (show (0 : Nat) = 1 from h) (by decide +kernel)
  | a :: t, h => by
    by_cases ha : F a % 2 = 0
    · have ht : (ground.famFold Nat.add 0 F t) % 2 = 1 := by
        rw [show ground.famFold Nat.add 0 F (a :: t)
            = F a + ground.famFold Nat.add 0 F t from rfl,
          ← ground.modAdd (F a) (ground.famFold Nat.add 0 F t) 2,
          ha, Nat.zero_add,
          ground.modOfLt ((ground.famFold Nat.add 0 F t) % 2) 2
            (ground.natDivRead (ground.famFold Nat.add 0 F t) 2
              (Nat.succ_pos 1)).2] at h
        exact h
      obtain ⟨x, hxm, hxo⟩ := fold_odd_witness F t ht
      exact ⟨x, ground.countOf_cons_pos hxm, hxo⟩
    · exact ⟨a, by rw [ground.countOf_head]; exact Nat.succ_pos _,
        mod_two_odd ha⟩

/-- A box member's coordinate totals fold to its degree, the
grid's double fold exchanged. -/
private theorem dirTot_fold_deg (m d D : Nat) (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox m d D)) :
    ground.famFold Nat.add 0 (fun i => dirTot i g)
      (List.range d) = D := by
  obtain ⟨hl, ha, hs⟩ := momBox_reads m d D g hg
  have hE := matOf_entOf m d g hl ha
  have hs' : ground.sumNat
      ((ground.matOf m d (entOf g)).map ground.sumNat) = D := by
    rw [← hE]
    exact hs
  have hdegF : ground.famFold Nat.add 0
      (fun t => ground.famFold Nat.add 0 (fun i => entOf g t i)
        (List.range d)) (List.range m) = D := by
    rw [← hs', deg_matOf m d (entOf g),
      ground.sumMap
        (fun t => ground.sumNat ((List.range d).map (entOf g t)))
        (List.range m)]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun t => (ground.sumMap (entOf g t) (List.range d)).symm)
      (List.range m)
  have hcolT : ∀ i, 0 < ground.countOf i (List.range d) →
      dirTot i g
        = ground.famFold Nat.add 0 (fun t => entOf g t i)
            (List.range m) := by
    intro i hi
    rw [show dirTot i g = dirTot i (ground.matOf m d (entOf g)) from
        by rw [← hE],
      dirTot_matOf m d i (ground.ltOfMem hi) (entOf g),
      ground.sumMap (fun t => entOf g t i) (List.range m)]
  rw [ground.famFold_congr_members Nat.add 0 _ _ (List.range d) hcolT,
    ← ground.famFold_swap (fun t i => entOf g t i)
      (List.range m) (List.range d)]
  exact hdegF

/-- An odd degree's every invariant reads equal members at every
monomial: the coordinate totals join to the degree with one member
odd, and the reflection's clause reads the coefficient there
(`thm:restoration`'s rate clause, the first breaking invariant two
even degrees up). -/
theorem oddDeg_vanish (m d D : Nat) (hD : D % 2 = 1)
    (c : List (List Nat) → BPair) (h : bdInvAt m d D c)
    (g : List (List Nat))
    (hg : 0 < ground.countOf g (momBox m d D)) :
    (c g).oneValue BPair.unit := by
  have hfold : (ground.famFold Nat.add 0 (fun i => dirTot i g)
      (List.range d)) % 2 = 1 := by
    rw [dirTot_fold_deg m d D g hg]
    exact hD
  obtain ⟨i, him, hio⟩ :=
    fold_odd_witness (fun i => dirTot i g) (List.range d) hfold
  exact bdInv_vanish m d D c h g hg i (ground.ltOfMem him) hio

end restoration
