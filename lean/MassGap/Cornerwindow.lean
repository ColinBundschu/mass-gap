import MassGap.Lattice
import MassGap.Coeff
import MassGap.Inertia
/-!
`con:cornerwindow` — the square window's data at two directions or
beyond, each a read of the window's finite lists.

The window is the box of side `L`: the sites are the naturals below
`(L + 1)^d` at positional base-`(L + 1)` arithmetic, the coordinate
at a direction the site key's digit there (`coordAt`, the first
position the digit nought), and one step along a direction adds
the direction's stride (`stepAt`).  A link is a direction with a
site whose coordinate there sits below the side (`linkList`, the
key its position in the list), a plaquette a plane, the lower
direction first, with a corner site whose two plane coordinates sit
below the side (`plaqList`), its boundary word the base link, the
corner's link in the lower direction, forward, then the higher
direction's link at the corner moved one step in the lower direction
forward, and the lower direction's link at the corner moved one step
in the higher direction with the higher direction's link at the
corner, both backward (`plaqWord`), and a cube three directions in
order with a corner (`cubeList`), the counts `#ℓ`, `#p` and the
cubes' derived at every window, the plaquettes' at two directions or
beyond and the cubes' at three, at the further directions' count
(`linkCount_read`, `plaqCount_read`, `cubeCount_read`: the box count
at the constrained directions, `ground.boxCount_read`, the planes'
and cube types' counts the binomials `ground.pairFold_eq_pasc`,
`ground.tripleFold_eq_pasc`), and the keys
reading their members (`linkKey_read`, `plaqKey_read`) at the sites'
step reads (`stepAt_lt`, `coordAt_step`, `coordAt_step_ne`).  The region is `con:lattice`'s
interface at those lists (`boxRegion`), the coloring the
coordinates' sum's parity.

The incidence `K` is the plaquette-link list at the traversals'
signs (`incid`, the sign fold over the boundary word at a link key,
`signAt`), the Gram `Δ = K Kᵀ` (`gram`), and the cubes' boundaries
`N` the plaquette-cube list at the faces' signs (`cubeBd`): the
sign one at the face at the cube's corner in its two lower
directions, and the further five faces at the signs at which the
six boundary words fold to the sum's unit at every link
(`cubeFaces`), the fold read `Kᵀ N ≡ 0` (`bdRead`) derived at every
window (`bdRead_all`: each link of a cube sits on two faces at
exchanged traversals, `bdEntry`, the entry read `incid_entry` and
the keyed fold's exchange `ground.bsum_keyFold_linear`).  The kernel
dimension is the pivot-free count of `Kᵀ` at the plaquette count
(`kerDim`, `def:elim`'s descent), the kernel list `N₀` the cubes'
boundaries' collection, one member joined per refusal in the
corners' order (`kerList`, `lem:lowerspan`'s collection), independent
(`kerList_indep`) with its Gram determinant off the sum's unit
(`projDen_off`), each member pairing every link at the sum's unit
(`kerList_ker`), and spanning the kernel by the descent in the last
direction (`kernel_bd_span`, `kerList_span`): a kernel vector
supported on the window one position shorter at a direction and a
level (`levelB`, the plaquettes whose coordinates beyond the
direction sit at the first position, whose plane sits within the
directions at or below it, and whose corner's coordinate at the
direction, raised by one at a plane through the direction, sits at
or below the level) moves by the cubes' boundaries' combination at
the cubes of the direction with their corners at the level, each at
its top face's read (`topCoef`, `stepV`, the entry `stepV_key` at
`cubes_holding`), to a kernel vector supported at the level below
(`descent_step`): the top faces withdraw at their cubes' boundaries
(`stepV_top`), the faces through the direction at the level read off
the top links' kernel reads at the stepped vector, the transposed
incidence's read at the plane folds (`colRead_planes`, the column
read `colRead` folded over the planes through the link's direction)
holding the face's balance partner alone, every further plaquette on
the link at a corner one beyond the level (`stepped_above`,
`stepped_back`, `stepped_face_read`), and every plaquette off the
level above keeps the unit (`stepV_off`); the level descends to the
first position and the direction to the first (`descent_all`), where
the window holds no plaquette.  The kernel list's count is then the
kernel dimension, two independent lists inside one span
(`kerList_length`, `elim.span_count_eq` against `elim.kernelList`).
The range projector `Π = 1 - N₀ (N₀ᵀN₀)⁻¹ N₀ᵀ` enters cleared at the
kernel list's Gram determinant `D` (`projDen`), `D Π` the identity's
multiple less the kernel list against its Gram's adjugate
(`proj`, the adjugate at `def:elim`'s bordered descent,
`elim.adjMD`), the identity at two directions where the kernel
list is vacant; its reads are the decided reads `projSymRead` (the
symmetry), `projIdemRead` (the idempotence `(DΠ)(DΠ) ≡ D (DΠ)`),
`projGramRead` (`Δ (DΠ) ≡ D Δ`) and `projKerRead` (`(DΠ) N₀ ≡ 0`),
each derived at every window (`projSymRead_all`, `projIdemRead_all`,
`projGramRead_all`, `projKerRead_all`) at the adjugate identity
`adj(G) G ≡ D 1` (`elim.adjM_col_diag`, `elim.adjM_col_off` at
`elim.adjMD_cofVec`) and the adjugate's symmetry at the symmetric
Gram (`elim.cofVec_symm`): at an occupied kernel list
`D Π ≡ D 1 - N₀ adj(G) N₀ᵀ` (`proj_bridge`) with
`N₀ adj(G) N₀ᵀ N₀ ≡ D N₀` (`proj_core`) and the Gram against `N₀`
vacant (`gramKer_null`), and at the vacant list `D Π ≡ D 1`
(`proj_vacant`).

The roots' bracket, the upper side: the Gram's form sits at or below
`8g` times the self-pairing at every plaquette vector (`gramCap`, the
abstract read `incidCap`: at an incidence whose rows' squares fold to
at most four and whose columns' occupancy folds sit at or below `m`
(`colFold`), `Kᵀ W`'s self-pairing sits at or below `4m |W|²`, the
squared Cauchy–Schwarz at the count per link,
`coeff.bsum_sq_le_count`), the row read derived at every window
(`rowSq_read`, `rowSqRead_all`: a plaquette's row is its boundary
word's signs over the link keys, `incid_row`, at four distinct keys)
and the column read derived at every window as well
(`colCountRead`, `colCountRead_all`: a link's column at the incidence's
entry read `incid_entry_link` holds at most two plaquettes per plane
through the link's direction, the link's tail's and the corner
stepped back, `ground.bsum_range_le_one`, and the planes through a
direction count twice the direction gap, `ground.bsum_range_sides`),
so the roots' bracket `gramCap` reads at every window.

The roots' bracket, the lower side, at the Hodge fold: the Gram
joined to the cubes' boundaries' Gram, `Δ + N Nᵀ`, the cubes' Gram the
rows' Gram (`cubeGram`, `elim.gramM`), reads entry by entry
the differences' Grams summed over the plane types and the directions
(`diffMat`, the consecutive differences along a direction on a plane
type's plaquettes, a Dirichlet fold along a plane direction and a
Neumann fold along a further one; `hodgeMat`, `hodgeRead`, derived at
every window as `hodgeRead_all`: the Gram's entry at the incidence's
four reads `gram_entry`, the cubes' Gram's entry at the faces' signs
`cubeGram_entry` folded over the cubes holding the plaquette
`cubes_holding`, the differences' Gram's entry `diffGram_entry`, and the
six plaquette-pair classes, one plane, a shared lower direction, the
two crossed pairs, a shared higher direction and disjoint planes, each
one Bool-atom shape read); so at a plaquette vector the Gram's form
joined to `Nᵀ W`'s self-pairing is the Hodge fold (`hodgeFold`,
`hodgeForm_read` at the forms `inertia.quadForm_gramM` and
`inertia.quadForm_msum`), the Gram's form alone at a range member
(`hodgeForm_range`).  The Dirichlet folds telescope line by line: the
sites fold over a direction's lines (`siteOnLine`, `bsum_site_split`),
the difference operator's read at a site (`diffAt`, `diff_entry`) is
the line's difference (`lineDiff`), each value the differences' fold
from the end and its square at or below the count against the squares
(`line_telescope`, `coeff.bsum_sq_le_count`), so a plane's squares'
fold sits at or below the side's square against the differences' fold
along either plane direction (`plane_sq_le`) and the Poincaré read
`2 Wᵀ W ≤ L² Wᵀ Δ W` holds at every range member (`poincare_read`), the
pair `[L² : 2]`'s comparison at its clearing.

The identity is one mechanism one cell degree up: the four-cells
`(a, b, c, e, s)` (`fourCellList`), the cube key `cubeKey`, a
four-cell's eight cubes at their signs (`fourCellCubes`, one at the
cube at the corner in the three lower directions), the four-cells'
boundaries `N₄` (`fourCellBd`) with `N N₄ ≡ 0` entrywise
(`bdRead4`, `bdRead4_all` through `bdEntry4`), the cubes' Gram `NᵀN`
(`cubesGram`) and the four-cells' Gram `N₄N₄ᵀ` (`fourCellGram`), the
differences along a direction on a cube type (`diffMat3`,
`diffFold3`), the Hodge fold at cubes (`hodgeFold3`, `hodgeMat3`) and
the identity `NᵀN + N₄N₄ᵀ ≡ hodgeMat3` (`hodgeRead3`, `hodgeRead3_all`
through `hodge3_entry` at the cube pairs' classes: one type, one
shared plane at its nine placements, at most one shared direction),
the cubes' Gram's form at a range member the Hodge fold's
(`hodgeForm3_range`), the Dirichlet telescope along each of the type's
directions (`cube_sq_le` through `line_telescope`), and the cubes'
Poincaré read `3 zᵀ z ≤ L² zᵀ NᵀN z` at every chain the four-cells'
boundaries pair at the sum's unit (`cubePoincare_read`).

The profile `W` sits on the first two directions' plane at every
position of the further directions, `W_p = w_x w_y` at the corner's
plane coordinates and `w_b = b (L + 1 - b)` (`wAt`, `profile`), in
the range at three directions or beyond (`profRangeRead`, derived at
every window as `profRangeRead_all`: a cube's two faces on the plane
read one value at exchanged signs, `profile_entry`), with the
two closed sums in the side, the parabola's squares at
`30 Σ w_b² = L (L + 1)(L + 2)(L² + 2L + 2)` and the consecutive
margins' squares at `3 Σ ⟨w_{b+1} : w_b⟩² = L (L + 1)(L + 2)`
(`profSq_closed`, `profDiff_closed`, each the power sums' closed
reads at one polynomial identity, the margin `ground.marg`), and the
mode read `Wᵀ Δ W = e_W Wᵀ W` at `e_W = [20 : L² + 2L + 2]`
(`modeRead`), derived at every window (`modeRead_all`): the Gram's
form is the transposed incidence's image's self-pairing
(`inertia.quadForm_matMulT`), the image's entry at a link is the
profile's step margin along the other plane direction (`profCol_read`,
the column read `colRead` at the profile's entries `profAt` with the
stepped-back site `ground.stepBack`), the links' fold reindexes over
the link list at its keys (`linkList_distinct`, `linkKey_of_getAt`) and
folds over the box's two plane digits (`ground.bsum_box_two_ofNat`) to
the two closed sums' products (`profGram_read`, `profSelf_read`), the
identity in the side one polynomial read at the closed sums.

The counts: the comb tree's root path of a site ascends the
directions in their order (`rootPath`, the links at the site's
prefix coordinates); a boundary link's loop region is the columns
descended in the later directions at the plaquette's corners, one
column of width one per descent, vacant at the two corner links
(`loopRegion`), its count `n_{ℓp}` at or below `gL`
(`regionCapRead`), and the cover: a plaquette sits in at most
`[2 : (g + 1) L] #p` regions (`coverRead`) and the regions' counts
fold to at most `[2g : g + 1] #p` over the pairs whose region holds
one plaquette (`regionFold`, `regionSumRead`).
-/

namespace cornerwindow
open ground lattice elim inertia

/-! The keys: the sites at positional base-`(L + 1)` arithmetic. -/

/-- The coordinate of a site at a direction: the site key's digit
at the base `L + 1`, the first position nought (`ground.baseDigit`). -/
def coordAt (L e s : Nat) : Nat := ground.baseDigit (L + 1) e s

/-- The site moved one step along a direction. -/
def stepAt (L e s : Nat) : Nat := s + (L + 1) ^ e

/-- The site's prefix at a direction: the coordinates below the
direction kept, the further ones at the first position. -/
def prefixAt (L e s : Nat) : Nat := s % (L + 1) ^ e

/-- The sites of the window, the naturals below `(L + 1)^d`. -/
def sites (d L : Nat) : List Nat := List.range ((L + 1) ^ d)

/-- The coordinates' sum at a site, the two-coloring's read
(`ground.digitSum` at the base `L + 1`). -/
def coordSum (d L s : Nat) : Nat := ground.digitSum (L + 1) d s

/-! The lists: the links, the plaquettes and the cubes, each keyed
by its position in its list. -/

/-- The links: a direction with a site whose coordinate there sits
below the side, the tail the site and the head its step. -/
def linkList (d L : Nat) : List (Nat × Nat) :=
  (List.range d).flatMap (fun e => (sites d L).filterMap (fun s =>
    if coordAt L e s < L then some (e, s) else none))

/-- The link key at a direction and a site, the link's position in
the list. -/
def linkKey (d L e s : Nat) : Nat := posBy pairBeq (e, s) (linkList d L)

/-- The links' count `#ℓ`. -/
def linkCount (d L : Nat) : Nat := (linkList d L).length

/-- The plaquettes: a plane, the lower direction first, with a
corner site whose two plane coordinates sit below the side. -/
def plaqList (d L : Nat) : List (Nat × Nat × Nat) :=
  (List.range d).flatMap (fun a => (List.range d).flatMap (fun k =>
    if a < k then
      (sites d L).filterMap (fun s =>
        if coordAt L a s < L && coordAt L k s < L then some (a, k, s)
        else none)
    else []))

/-- The plaquette key at a plane and a corner, the plaquette's
position in the list. -/
def plaqKey (d L a k s : Nat) : Nat := posBy tripleBeq (a, k, s) (plaqList d L)

/-- The plaquettes' count `#p`. -/
def plaqCount (d L : Nat) : Nat := (plaqList d L).length

/-- A plaquette's boundary word: the base link, the corner's link in
the lower direction, forward; the higher direction's link at the
corner moved one step in the lower direction, forward; the lower
direction's link at the corner moved one step in the higher
direction, backward; and the higher direction's link at the corner,
backward, the cyclic word closing at the corner. -/
def plaqWord (d L : Nat) (p : Nat × Nat × Nat) : List (Nat × Bool) :=
  [(linkKey d L p.1 p.2.2, true),
   (linkKey d L p.2.1 (stepAt L p.1 p.2.2), true),
   (linkKey d L p.1 (stepAt L p.2.1 p.2.2), false),
   (linkKey d L p.2.1 p.2.2, false)]

/-- The cubes: three directions in order with a corner site whose
three coordinates sit below the side. -/
def cubeList (d L : Nat) : List (Nat × Nat × Nat × Nat) :=
  (List.range d).flatMap (fun a => (List.range d).flatMap (fun b =>
    (List.range d).flatMap (fun c =>
      if a < b && b < c then
        (sites d L).filterMap (fun s =>
          if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L
          then some (a, b, c, s) else none)
      else [])))

/-- The cubes' count. -/
def cubeCount (d L : Nat) : Nat := (cubeList d L).length

/-! The counts' displays: `#ℓ`, `#p` and the cubes' count at the
direction gap, the box count at the constrained directions
(`ground.boxCount_read`) against the pairs' and triples' counts. -/

/-- The links' count at the direction gap: the directions against
the side and the base's power at the further directions. -/
theorem linkCount_read (g L : Nat) : linkCount (g + 1) L = (g + 1) * (L * (L + 1) ^ g) := by
  show ((List.range (g + 1)).flatMap (fun e => (sites (g + 1) L).filterMap (fun s =>
    if coordAt L e s < L then some (e, s) else none))).length = _
  rw [length_flatMap, famFold_congr_members Nat.add 0 _ (fun _ => L * (L + 1) ^ g)
    (List.range (g + 1)) (fun e he => ?_), famFold_const, length_range]
  rw [filterMap_iteP, length_map]
  have hc : (sites (g + 1) L).filter (fun s => decide (coordAt L e s < L))
      = (List.range ((L + 1) ^ (g + 1))).filter (fun s =>
          (List.range (g + 1)).all (fun e' =>
            !(([e] : List Nat).any (fun x => e' == x)) || decide (baseDigit (L + 1) e' s < L))) :=
    filter_congr _ _ (fun s => by
      rw [all_range_pickList (fun e' => decide (baseDigit (L + 1) e' s < L)) [e] (g + 1)
        (fun x hx => by
          cases hx with
          | head => exact ltOfCountRange he
          | tail _ h => nomatch h)]
      show decide (baseDigit (L + 1) e s < L) = (decide (baseDigit (L + 1) e s < L) && true)
      exact (Bool.and_true _).symm) _
  rw [hc]
  show boxCount (L + 1) (g + 1) L (fun e' => ([e] : List Nat).any (fun x => e' == x)) = _
  rw [boxCount_read]
  have h1 : ((List.range (g + 1)).filter
      (fun e' => ([e] : List Nat).any (fun x => e' == x))).length = 1 := by
    rw [filter_congr _ (fun x => x == e) (fun x => by
      show (x == e || false) = (x == e)
      exact Bool.or_false _) _]
    exact length_filter_beq e (g + 1) (ltOfCountRange he)
  rw [h1, powOne, Nat.succ_sub_succ, Nat.sub_zero]

/-- The plaquettes' count at the direction gap: the planes' count
against the side's square and the base's power at the further
directions, `2 #p = (h + 1) (h + 2) L² (L + 1)^{(h + 1)-1}`. -/
theorem plaqCount_read (h L : Nat) :
    2 * plaqCount (h + 2) L = (h + 1) * (h + 2) * (L * L * (L + 1) ^ h) := by
  have hX : ∀ a k, a < h + 2 → k < h + 2 → a < k →
      ((sites (h + 2) L).filterMap (fun s =>
        if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none)).length
      = L * L * (L + 1) ^ h := by
    intro a k ha hk hak
    rw [filterMap_ite, length_map]
    have hc : (sites (h + 2) L).filter (fun s => decide (coordAt L a s < L) && decide (coordAt L k s < L))
        = (List.range ((L + 1) ^ (h + 2))).filter (fun s =>
            (List.range (h + 2)).all (fun e' =>
              !(([a, k] : List Nat).any (fun x => e' == x)) || decide (baseDigit (L + 1) e' s < L))) :=
      filter_congr _ _ (fun s => by
        rw [all_range_pickList (fun e' => decide (baseDigit (L + 1) e' s < L)) [a, k] (h + 2)
          (fun x hx => by
            cases hx with
            | head => exact ha
            | tail _ h =>
              cases h with
              | head => exact hk
              | tail _ h' => nomatch h')]
        show (decide (baseDigit (L + 1) a s < L) && decide (baseDigit (L + 1) k s < L))
          = (decide (baseDigit (L + 1) a s < L) && (decide (baseDigit (L + 1) k s < L) && true))
        rw [Bool.and_true]) _
    rw [hc]
    show boxCount (L + 1) (h + 2) L (fun e' => ([a, k] : List Nat).any (fun x => e' == x)) = _
    rw [boxCount_read]
    have h2 : ((List.range (h + 2)).filter
        (fun e' => ([a, k] : List Nat).any (fun x => e' == x))).length = 2 := by
      rw [filter_congr _ (fun x => x == a || x == k) (fun x => by
        show (x == a || (x == k || false)) = (x == a || x == k)
        rw [Bool.or_false]) _]
      exact length_filter_beq2 a k (h + 2) ha hk hak
    rw [h2, sqRead, Nat.succ_sub_succ, Nat.succ_sub_succ, Nat.sub_zero]
  show 2 * ((List.range (h + 2)).flatMap (fun a => (List.range (h + 2)).flatMap (fun k =>
    if a < k then (sites (h + 2) L).filterMap (fun s =>
      if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none) else []))).length = _
  rw [length_flatMap]
  have hin : ∀ a, 0 < countOf a (List.range (h + 2)) →
      ((List.range (h + 2)).flatMap (fun k =>
        if a < k then (sites (h + 2) L).filterMap (fun s =>
          if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none) else [])).length
      = L * L * (L + 1) ^ h
        * famFold Nat.add 0 (fun k => cond (decide (a < k)) 1 0) (List.range (h + 2)) := by
    intro a ha
    rw [length_flatMap, famFold_mul]
    refine famFold_congr_members Nat.add 0 _ _ (List.range (h + 2)) (fun k hk => ?_)
    by_cases h : a < k
    · rw [if_pos h, decide_eq_true h, hX a k (ltOfCountRange ha) (ltOfCountRange hk) h]
      exact (Nat.mul_one _).symm
    · rw [if_neg h, decide_eq_false h]
      rfl
  rw [famFold_congr_members Nat.add 0 _ _ (List.range (h + 2)) hin, ← famFold_mul]
  show 2 * (L * L * (L + 1) ^ h * pairFold (h + 2)) = _
  have hp : 2 * pairFold (h + 2) = (h + 1) * (h + 2) := by
    refine addCancelR (h + 2) ?_
    rw [pairFold_eq_pasc, pasc_two_read]
    exact polEq [h]
      (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))))
      (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2))))
      (by decide +kernel)
  rw [← mulAssoc 2, Nat.mul_comm 2, mulAssoc, hp, Nat.mul_comm]

/-- The cubes' count at the direction gap's successor: the cube
types' count against the side's cube and the base's power at the
further directions, `6 #c = (h + 1) (h + 2) (h + 3) L³ (L + 1)^{(h + 1)-1}`. -/
theorem cubeCount_read (h L : Nat) :
    6 * cubeCount (h + 3) L = (h + 1) * (h + 2) * (h + 3) * (L * L * L * (L + 1) ^ h) := by
  have hX : ∀ a b c, a < h + 3 → b < h + 3 → c < h + 3 → a < b → b < c →
      ((sites (h + 3) L).filterMap (fun s =>
        if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L then some (a, b, c, s)
        else none)).length
      = L * L * L * (L + 1) ^ h := by
    intro a b c ha hb hc hab hbc
    rw [filterMap_ite, length_map]
    have hcg : (sites (h + 3) L).filter (fun s =>
          decide (coordAt L a s < L) && decide (coordAt L b s < L) && decide (coordAt L c s < L))
        = (List.range ((L + 1) ^ (h + 3))).filter (fun s =>
            (List.range (h + 3)).all (fun e' =>
              !(([a, b, c] : List Nat).any (fun x => e' == x)) || decide (baseDigit (L + 1) e' s < L))) :=
      filter_congr _ _ (fun s => by
        rw [all_range_pickList (fun e' => decide (baseDigit (L + 1) e' s < L)) [a, b, c] (h + 3)
          (fun x hx => by
            cases hx with
            | head => exact ha
            | tail _ h =>
              cases h with
              | head => exact hb
              | tail _ h' =>
                cases h' with
                | head => exact hc
                | tail _ h'' => nomatch h'')]
        show (decide (baseDigit (L + 1) a s < L) && decide (baseDigit (L + 1) b s < L)
            && decide (baseDigit (L + 1) c s < L))
          = (decide (baseDigit (L + 1) a s < L) && (decide (baseDigit (L + 1) b s < L)
            && (decide (baseDigit (L + 1) c s < L) && true)))
        rw [Bool.and_true, Bool.and_assoc]) _
    rw [hcg]
    show boxCount (L + 1) (h + 3) L (fun e' => ([a, b, c] : List Nat).any (fun x => e' == x)) = _
    rw [boxCount_read]
    have h3 : ((List.range (h + 3)).filter
        (fun e' => ([a, b, c] : List Nat).any (fun x => e' == x))).length = 3 := by
      rw [filter_congr _ (fun x => x == a || x == b || x == c) (fun x => by
        show (x == a || (x == b || (x == c || false))) = (x == a || x == b || x == c)
        rw [Bool.or_false, Bool.or_assoc]) _]
      exact length_filter_beq3 a b c (h + 3) ha hb hc hab hbc
    rw [h3, pow3Read, Nat.succ_sub_succ, Nat.succ_sub_succ, Nat.succ_sub_succ, Nat.sub_zero]
  show 6 * ((List.range (h + 3)).flatMap (fun a => (List.range (h + 3)).flatMap (fun b =>
    (List.range (h + 3)).flatMap (fun c =>
      if a < b && b < c then (sites (h + 3) L).filterMap (fun s =>
        if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L then some (a, b, c, s)
        else none) else [])))).length = _
  rw [length_flatMap]
  have hin : ∀ a, 0 < countOf a (List.range (h + 3)) →
      ((List.range (h + 3)).flatMap (fun b => (List.range (h + 3)).flatMap (fun c =>
        if a < b && b < c then (sites (h + 3) L).filterMap (fun s =>
          if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L then some (a, b, c, s)
          else none) else []))).length
      = L * L * L * (L + 1) ^ h
        * famFold Nat.add 0 (fun b => famFold Nat.add 0
            (fun c => cond (decide (a < b) && decide (b < c)) 1 0) (List.range (h + 3)))
          (List.range (h + 3)) := by
    intro a ha
    rw [length_flatMap, famFold_mul]
    refine famFold_congr_members Nat.add 0 _ _ (List.range (h + 3)) (fun b hb => ?_)
    rw [length_flatMap, famFold_mul]
    refine famFold_congr_members Nat.add 0 _ _ (List.range (h + 3)) (fun c hc => ?_)
    by_cases h : (decide (a < b) && decide (b < c)) = true
    · have hab := (andSplitB h).1
      have hbc := (andSplitB h).2
      rw [if_pos h, hX a b c (ltOfCountRange ha) (ltOfCountRange hb) (ltOfCountRange hc)
        (of_decide_eq_true hab) (of_decide_eq_true hbc), h]
      exact (Nat.mul_one _).symm
    · rw [if_neg h]
      cases hv : (decide (a < b) && decide (b < c)) with
      | true => exact absurd hv h
      | false => rfl
  rw [famFold_congr_members Nat.add 0 _ _ (List.range (h + 3)) hin, ← famFold_mul]
  show 6 * (L * L * L * (L + 1) ^ h * tripleFold (h + 3)) = _
  have ht : 6 * tripleFold (h + 3) = (h + 1) * (h + 2) * (h + 3) := by
    refine addCancelR (3 * ((h + 3) * (h + 3))) ?_
    rw [tripleFold_eq_pasc, pasc_three_read]
    exact polEq [h]
      (Pol.add (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 3))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 3)))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 3)))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 3)))))
      (Pol.add (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 3)))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 3))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 3))))))
      (by decide +kernel)
  rw [← mulAssoc 6, Nat.mul_comm 6, mulAssoc, ht, Nat.mul_comm]

/-! The window's sites and keys: a stepped site's coordinates and
its place in the box, and the links' and plaquettes' keys at their
lists. -/

/-- A stepped site stays in the box at a coordinate below the side. -/
theorem stepAt_lt (d L a s : Nat) (ha : a < d) (hs : s < (L + 1) ^ d) (hc : coordAt L a s < L) :
    stepAt L a s < (L + 1) ^ d :=
  stepLtPow (L + 1) a d s (Nat.succ_pos L) hs ha (Nat.succ_lt_succ hc)

/-- The stepped coordinate at the step's own direction. -/
theorem coordAt_step (L a s : Nat) (hc : coordAt L a s < L) :
    coordAt L a (stepAt L a s) = coordAt L a s + 1 :=
  baseDigit_step (L + 1) a s (Nat.succ_pos L) (Nat.succ_lt_succ hc)

/-- The coordinates off the step's direction are kept. -/
theorem coordAt_step_ne (L a e s : Nat) (hc : coordAt L a s < L) (hne : ¬ e = a) :
    coordAt L e (stepAt L a s) = coordAt L e s := by
  cases Nat.lt_or_ge e a with
  | inl h =>
    show baseDigit (L + 1) e (s + (L + 1) ^ a) = baseDigit (L + 1) e s
    rw [← Nat.one_mul ((L + 1) ^ a)]
    exact baseDigit_add_high (L + 1) e a s 1 (Nat.succ_pos L) h
  | inr h =>
    have h' : a < e := Nat.lt_of_le_of_ne h (fun hae => hne hae.symm)
    exact baseDigit_step_high (L + 1) a e s (Nat.succ_pos L) (Nat.succ_lt_succ hc) h'

/-- A link at a direction below the count, a site of the box and a
coordinate below the side is a member of the link list. -/
theorem link_mem (d L e s : Nat) (he : e < d) (hs : s < (L + 1) ^ d) (hc : coordAt L e s < L) :
    (e, s) ∈ linkList d L :=
  mem_flatMap_to _ (memRange he) (mem_filterMap_to _ (memRange hs) (if_pos hc))

/-- The link key of a member sits below the links' count. -/
theorem linkKey_lt (d L e s : Nat) (he : e < d) (hs : s < (L + 1) ^ d) (hc : coordAt L e s < L) :
    linkKey d L e s < linkCount d L :=
  posBy_lt_of_hit pairBeq (e, s) (linkList d L) ⟨(e, s), link_mem d L e s he hs hc, pairBeq_refl _⟩

/-- The link list at a member's key reads the member. -/
theorem linkKey_read (d L e s : Nat) (he : e < d) (hs : s < (L + 1) ^ d) (hc : coordAt L e s < L) :
    getAt (0, 0) (linkList d L) (linkKey d L e s) = (e, s) :=
  (pairBeq_read _ _ (getAt_posBy (0, 0) pairBeq (e, s) (linkList d L)
    ⟨(e, s), link_mem d L e s he hs hc, pairBeq_refl _⟩)).symm

/-- Two members at one link key are one link. -/
theorem linkKey_inj (d L e s e' s' : Nat) (he : e < d) (hs : s < (L + 1) ^ d)
    (hc : coordAt L e s < L) (he' : e' < d) (hs' : s' < (L + 1) ^ d) (hc' : coordAt L e' s' < L)
    (h : linkKey d L e s = linkKey d L e' s') : e = e' ∧ s = s' := by
  have h1 := linkKey_read d L e s he hs hc
  rw [h, linkKey_read d L e' s' he' hs' hc'] at h1
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg Prod.snd h1).symm⟩

/-- A member of the link list is a link: a direction below the
count with a site whose coordinate there sits below the side. -/
theorem link_of_mem (d L : Nat) (x : Nat × Nat) (h : x ∈ linkList d L) :
    x.1 < d ∧ x.2 < (L + 1) ^ d ∧ coordAt L x.1 x.2 < L := by
  obtain ⟨e, he, he'⟩ := mem_flatMap_of _ _ _ h
  have hed : e < d := ltOfMemRange he
  obtain ⟨s, hs, hf⟩ := mem_filterMap_of _ _ _ he'
  have hsd : s < (L + 1) ^ d := ltOfMemRange hs
  by_cases hc : coordAt L e s < L
  · rw [if_pos hc] at hf
    have hp : (e, s) = x := Option.some.inj hf
    rw [← hp]
    exact ⟨hed, hsd, hc⟩
  · rw [if_neg hc] at hf
    exact nomatch (show (none : Option (Nat × Nat)) = some x from hf)

/-- The link list holds each link once. -/
theorem linkList_distinct (d L : Nat) : distinctList (linkList d L) := by
  intro x hx
  show countOf x ((List.range d).flatMap (fun e => (sites d L).filterMap (fun s =>
    if coordAt L e s < L then some (e, s) else none))) ≤ 1
  rw [countOf_flatMap]
  refine famFold_le_one_at _ x.1 (List.range d) ?_ ?_
    (distinctList_all (distinctList_range d) x.1)
  · intro e _ hne
    refine countOf_zero_of_not_mem (fun hm => hne ?_)
    obtain ⟨s, _, hf⟩ := mem_filterMap_of _ _ _ hm
    by_cases hcs : coordAt L e s < L
    · rw [if_pos hcs] at hf
      exact congrArg Prod.fst (Option.some.inj hf)
    · rw [if_neg hcs] at hf
      exact nomatch (show (none : Option (Nat × Nat)) = some x from hf)
  · refine countOf_filterMap_le_one _ x (sites d L)
      (fun a => distinctList_all (distinctList_range _) a) ?_
    intro a b _ _ hfa hfb
    have ha : a = x.2 := by
      by_cases hca : coordAt L x.1 a < L
      · rw [if_pos hca] at hfa
        exact congrArg Prod.snd (Option.some.inj hfa)
      · rw [if_neg hca] at hfa
        exact nomatch (show (none : Option (Nat × Nat)) = some x from hfa)
    have hb : b = x.2 := by
      by_cases hcb : coordAt L x.1 b < L
      · rw [if_pos hcb] at hfb
        exact congrArg Prod.snd (Option.some.inj hfb)
      · rw [if_neg hcb] at hfb
        exact nomatch (show (none : Option (Nat × Nat)) = some x from hfb)
    rw [ha, hb]

/-- The link at a place keys to its place. -/
theorem linkKey_of_getAt (d L l : Nat) (hl : l < linkCount d L) :
    linkKey d L (getAt (0, 0) (linkList d L) l).1 (getAt (0, 0) (linkList d L) l).2 = l := by
  have hx : getAt (0, 0) (linkList d L) l ∈ linkList d L := mem_getAt (0, 0) (linkList d L) l hl
  generalize hxe : getAt (0, 0) (linkList d L) l = x at hx
  have hcount : countOf x (linkList d L) = 1 :=
    Nat.le_antisymm (linkList_distinct d L x hx) (countOf_pos_of_mem hx)
  have hfilt : ((linkList d L).filter (fun b => pairBeq x b)).length = 1 := by
    rw [length_filterBy]
    refine Eq.trans ?_ hcount
    show famFold Nat.add 0 (fun a => cond (pairBeq x a) 1 0) (linkList d L)
      = famFold Nat.add 0 (fun a => cond (decide (x = a)) 1 0) (linkList d L)
    refine famFold_congr_members Nat.add 0 _ _ (linkList d L) (fun a _ => ?_)
    cases hpa : pairBeq x a with
    | true =>
      rw [pairBeq_read x a hpa, decide_eq_true rfl]
    | false =>
      have hne : ¬ x = a := fun h => by
        rw [h, pairBeq_refl] at hpa
        exact Bool.noConfusion hpa
      rw [decide_eq_false hne]
  have h := (posBy_once pairBeq x (linkList d L) hfilt l hl).1 (by
    show pairBeq x (getAt (0, 0) (linkList d L) l) = true
    rw [hxe]
    exact pairBeq_refl x)
  cases x with
  | mk e s => exact h

/-- A plaquette at a plane below the count and a corner of the box
with both plane coordinates below the side is a member of the
plaquette list. -/
theorem plaq_mem (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) : (a, k, s) ∈ plaqList d L := by
  refine mem_flatMap_to _ (memRange (Nat.lt_trans hak hk)) (mem_flatMap_to _ (memRange hk) ?_)
  show (a, k, s) ∈ (if a < k then (sites d L).filterMap (fun s =>
    if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none) else [])
  rw [if_pos hak]
  refine mem_filterMap_to _ (memRange hs) ?_
  show (if (decide (coordAt L a s < L) && decide (coordAt L k s < L)) = true then some (a, k, s)
    else none) = some (a, k, s)
  rw [decide_eq_true hca, decide_eq_true hck]
  rfl

/-- The plaquette key of a member sits below the plaquettes' count. -/
theorem plaqKey_lt (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) : plaqKey d L a k s < plaqCount d L :=
  posBy_lt_of_hit tripleBeq (a, k, s) (plaqList d L)
    ⟨(a, k, s), plaq_mem d L a k s hak hk hs hca hck, tripleBeq_refl _⟩

/-- The plaquette list at a member's key reads the member. -/
theorem plaqKey_read (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) :
    getAt (0, 0, 0) (plaqList d L) (plaqKey d L a k s) = (a, k, s) :=
  (tripleBeq_read _ _ (getAt_posBy (0, 0, 0) tripleBeq (a, k, s) (plaqList d L)
    ⟨(a, k, s), plaq_mem d L a k s hak hk hs hca hck, tripleBeq_refl _⟩)).symm




/-- The square window as `con:lattice`'s region: the links at their
tails and steps, the plaquettes at their boundary words, and the
coloring at the coordinates' sum's parity. -/
def boxRegion (d L : Nat) : Region :=
  { links := linkCount d L,
    verts := (L + 1) ^ d,
    tail := (linkList d L).map (fun l => l.2),
    head := (linkList d L).map (fun l => stepAt L l.1 l.2),
    plaqs := (plaqList d L).map (plaqWord d L),
    color := (sites d L).map (fun s => coordSum d L s % 2 == 0),
    tailLen := ground.length_map _ _,
    headLen := ground.length_map _ _ }

/-- The direction gap `g` at `g + 1 = d`. -/
def dirGap (d : Nat) : Nat := d - 1

/-! The incidence, the Gram and the cubes' boundaries. -/

/-- A boundary word's sign at a link key: one at a forward traversal,
its balance partner at a backward one, the sum's unit off the
word, the keyed fold over the word's entries (`ground.keyFoldB`). -/
def signAt (w : List (Nat × Bool)) (l : Nat) : BPair :=
  keyFoldB (fun a b => a == b) l
    (w.map (fun e => (e.1, if e.2 then BPair.ofNat 1 else (BPair.ofNat 1).swap)))

/-- The incidence `K`: the plaquette-link list at the traversals'
signs. -/
def incid (d L : Nat) : Mat :=
  (boxRegion d L).plaqs.map (fun w =>
    (List.range (linkCount d L)).map (signAt w))

/-- The plaquettes' Gram `Δ = K Kᵀ`. -/
def gram (d L : Nat) : Mat := matMul (incid d L) (transposeM (incid d L))

/-- The incidence's row count is the plaquettes'. -/
theorem incid_length (d L : Nat) : (incid d L).length = plaqCount d L := by
  show (List.map (fun w => (List.range (linkCount d L)).map (signAt w))
    (List.map (plaqWord d L) (plaqList d L))).length = (plaqList d L).length
  rw [ground.length_map, ground.length_map]

/-- The incidence's rows sit at the links' count. -/
theorem incid_rows (d L : Nat) : rowsLen (linkCount d L) (incid d L) := by
  refine rowsLen_map _ _ _ (fun w _ => ?_)
  show ((List.range (linkCount d L)).map _).length = _
  rw [ground.length_map, ground.length_range]

/-- A cube's six faces at their signs: one at the face at the
cube's corner in its two lower directions, and the signs at which
the six boundary words fold to the sum's unit at every link, each
link of the cube on two faces at exchanged traversals. -/
def cubeFaces (d L : Nat) (c : Nat × Nat × Nat × Nat) :
    List (Nat × BPair) :=
  [(plaqKey d L c.1 c.2.1 c.2.2.2, BPair.ofNat 1),
   (plaqKey d L c.1 c.2.1 (stepAt L c.2.2.1 c.2.2.2), (BPair.ofNat 1).swap),
   (plaqKey d L c.1 c.2.2.1 c.2.2.2, (BPair.ofNat 1).swap),
   (plaqKey d L c.1 c.2.2.1 (stepAt L c.2.1 c.2.2.2), BPair.ofNat 1),
   (plaqKey d L c.2.1 c.2.2.1 c.2.2.2, BPair.ofNat 1),
   (plaqKey d L c.2.1 c.2.2.1 (stepAt L c.1 c.2.2.2), (BPair.ofNat 1).swap)]

/-- A face list's sign at a plaquette key, the sum's unit off the
list, the keyed fold (`ground.keyFoldB`). -/
def faceSign (fs : List (Nat × BPair)) (p : Nat) : BPair :=
  keyFoldB (fun a b => a == b) p fs

/-- The cubes' boundaries `N`: the plaquette-cube list at the faces'
signs. -/
def cubeBd (d L : Nat) : Mat :=
  (List.range (plaqCount d L)).map (fun p =>
    (cubeList d L).map (fun c => faceSign (cubeFaces d L c) p))

/-- The cubes' boundaries' row count is the plaquettes'. -/
theorem cubeBd_length (d L : Nat) : (cubeBd d L).length = plaqCount d L := by
  show ((List.range (plaqCount d L)).map _).length = _
  rw [ground.length_map, ground.length_range]

/-- The cubes' boundaries' rows sit at the cubes' count. -/
theorem cubeBd_rows (d L : Nat) : rowsLen (cubeCount d L) (cubeBd d L) := by
  refine rowsLen_map _ _ _ (fun p _ => ?_)
  show ((cubeList d L).map _).length = _
  rw [ground.length_map]
  rfl

/-- The cubes' boundaries' entry at a plaquette's place and a cube's
place: the faces' sign of the cube at the plaquette. -/
theorem cubeBd_entry (d L p c : Nat) (hp : p < plaqCount d L) (hc : c < cubeCount d L) :
    getAt BPair.unit (getAt [] (cubeBd d L) p) c
      = faceSign (cubeFaces d L (getAt (0, 0, 0, 0) (cubeList d L) c)) p := by
  show getAt BPair.unit (getAt [] ((List.range (plaqCount d L)).map (fun p =>
    (cubeList d L).map (fun C => faceSign (cubeFaces d L C) p))) p) c = _
  rw [getAt_map 0 [] _ _ p (by rw [ground.length_range]; exact hp), getAt_range _ p hp,
    getAt_map (0, 0, 0, 0) BPair.unit _ _ c hc]

/-- The cubes' boundaries' Gram `N Nᵀ`, the rows' Gram. -/
def cubeGram (d L : Nat) : Mat := gramM (cubeBd d L)

/-- The cubes' boundaries' Gram's count is the plaquettes'. -/
theorem cubeGram_length (d L : Nat) : (cubeGram d L).length = plaqCount d L := by
  show (gramBy dotP (cubeBd d L)).length = _
  rw [length_gramBy, cubeBd_length]

/-- The cubes' boundaries' Gram's rows read the plaquettes' count. -/
theorem cubeGram_rows (d L : Nat) : rowsLen (plaqCount d L) (cubeGram d L) := by
  show rowsLen _ (gramBy dotP (cubeBd d L))
  rw [← cubeBd_length d L]
  exact rowsLen_gramBy _ _

/-- The boundaries' fold read: `Kᵀ N` reads the sum's unit
entrywise. -/
def bdRead (d L : Nat) : Prop :=
  matNull (matMul (transposeM (incid d L)) (cubeBd d L))

instance instCornerwindow1 (d L : Nat) : Decidable (bdRead d L) :=
  inferInstanceAs (Decidable (matNull _))

/-- The kernel dimension of `Kᵀ` at the plaquette count, the
pivot-free count of the descent. -/
def kerDim (d L : Nat) : Nat := kernelDim (plaqCount d L) (transposeM (incid d L))

/-- The kernel list `N₀`: the cubes' boundaries' collection, one
member joined per refusal in the corners' order, the refusal the
joined Gram's determinant at the descent (`elim.collectW`), each
member a plaquette vector. -/
def kerList (d L : Nat) : Mat := collectW (plaqCount d L) (transposeM (cubeBd d L))

/-- The kernel list's Gram determinant `D`, the range projector's
clearing, at the descent. -/
def projDen (d L : Nat) : BPair := detD (gramM (kerList d L))

/-- The cleared range projector `D Π`: the identity at `D` less the
kernel list against its Gram's adjugate, entry by entry. -/
def proj (d L : Nat) : Mat :=
  matOf (plaqCount d L) (plaqCount d L) (fun i j =>
    (if i == j then projDen d L else BPair.unit)
      + (dotP (getAt [] (transposeM (kerList d L)) i)
          (matVec (adjMD (gramM (kerList d L)))
            (getAt [] (transposeM (kerList d L)) j))).swap)

/-- The projector's symmetry, the solve's own. -/
def projSymRead (d L : Nat) : Prop := symmRead (proj d L)

instance instCornerwindow2 (d L : Nat) : Decidable (projSymRead d L) :=
  inferInstanceAs (Decidable (symmRead _))

/-- The projector's idempotence at the clearing:
`(DΠ)(DΠ) ≡ D (DΠ)`. -/
def projIdemRead (d L : Nat) : Prop :=
  matOneValue (matMul (proj d L) (proj d L)) (matScaleB (projDen d L) (proj d L))

instance instCornerwindow3 (d L : Nat) : Decidable (projIdemRead d L) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The Gram against the projector at the clearing: `Δ (DΠ) ≡ D Δ`,
the kernel list pairing the Gram at the sum's unit. -/
def projGramRead (d L : Nat) : Prop :=
  matOneValue (matMul (gram d L) (proj d L)) (matScaleB (projDen d L) (gram d L))

instance instCornerwindow4 (d L : Nat) : Decidable (projGramRead d L) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The projector against the kernel list reads the sum's unit. -/
def projKerRead (d L : Nat) : Prop :=
  matNull (matMul (proj d L) (transposeM (kerList d L)))

instance instCornerwindow5 (d L : Nat) : Decidable (projKerRead d L) :=
  inferInstanceAs (Decidable (matNull _))

/-! The roots' bracket. -/

/-- The window's row read: every plaquette's incidence row folds its
entries' squares to four, the boundary's link count, the Gram's
diagonal. -/
def rowSqRead (d L : Nat) : Prop :=
  ((List.range (plaqCount d L)).all (fun p =>
    decide ((dotP (getAt [] (incid d L) p) (getAt [] (incid d L) p)).oneValue
      (BPair.ofNat 4)))) = true

instance instCornerwindow6 (d L : Nat) : Decidable (rowSqRead d L) :=
  inferInstanceAs (Decidable (_ = _))

/-! The incidence's rows: a plaquette's row is its boundary word's
signs over the link keys, and its squares fold to four at the
word's four distinct keys. -/

/-- A member of the plaquette list is a plane below the count at a
corner of the box with both plane coordinates below the side. -/
theorem plaq_of_mem (d L : Nat) (p : Nat × Nat × Nat) (h : p ∈ plaqList d L) :
    p.1 < p.2.1 ∧ p.2.1 < d ∧ p.2.2 < (L + 1) ^ d
      ∧ coordAt L p.1 p.2.2 < L ∧ coordAt L p.2.1 p.2.2 < L := by
  obtain ⟨a, _, ha⟩ := mem_flatMap_of _ _ _ h
  obtain ⟨k, hk, hk'⟩ := mem_flatMap_of _ _ _ ha
  have hkd : k < d := ltOfMemRange hk
  by_cases hak : a < k
  · rw [if_pos hak] at hk'
    obtain ⟨s, hs, hf⟩ := mem_filterMap_of _ _ _ hk'
    have hsd : s < (L + 1) ^ d := ltOfMemRange hs
    by_cases hc : (decide (coordAt L a s < L) && decide (coordAt L k s < L)) = true
    · rw [if_pos hc] at hf
      have hp : (a, k, s) = p := Option.some.inj hf
      rw [← hp]
      have hcs := andSplitB hc
      exact ⟨hak, hkd, hsd, of_decide_eq_true hcs.1, of_decide_eq_true hcs.2⟩
    · rw [if_neg hc] at hf
      exact nomatch (show (none : Option (Nat × Nat × Nat)) = some p from hf)
  · rw [if_neg hak] at hk'
    exact nomatch hk'

/-- A member of a plane's plaquette family sits in the plane. -/
theorem plaq_mem_plane (d L a k : Nat) (q : Nat × Nat × Nat)
    (hq : q ∈ (if a < k then (sites d L).filterMap (fun s =>
      if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none) else [])) :
    q.1 = a ∧ q.2.1 = k := by
  by_cases hak : a < k
  · rw [if_pos hak] at hq
    obtain ⟨s, _, hf⟩ := mem_filterMap_of _ _ _ hq
    by_cases hc : (decide (coordAt L a s < L) && decide (coordAt L k s < L)) = true
    · rw [if_pos hc] at hf
      have hp : (a, k, s) = q := Option.some.inj hf
      rw [← hp]
      exact ⟨rfl, rfl⟩
    · rw [if_neg hc] at hf
      exact nomatch (show (none : Option (Nat × Nat × Nat)) = some q from hf)
  · rw [if_neg hak] at hq
    exact nomatch hq

/-- The Gram's count is the plaquettes'. -/
theorem gram_length (d L : Nat) : (gram d L).length = plaqCount d L := by
  show (matMul (incid d L) (transposeM (incid d L))).length = _
  rw [length_matMul, incid_length]

/-- The Gram's rows read the plaquettes' count. -/
theorem gram_rows (d L : Nat) : rowsLen (plaqCount d L) (gram d L) := by
  show rowsLen _ (matMul (incid d L) (transposeM (incid d L)))
  refine rowsLen_matMul_of _ _ (fun h0 => ?_) ?_
  · rw [length_transposeM (incid d L) (incid_rows d L) h0]
    rw [incid_length] at h0
    obtain ⟨hak, hkd, hsd, hca, _⟩ := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) 0 h0)
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (linkKey_lt d L _ _ (Nat.lt_trans hak hkd) hsd hca)
  · rw [← incid_length d L]
    exact rowsLen_transposeM _

/-! The plaquette keys: two members at one key are one plaquette, the
keys' comparison reads the data's, the list holds each plaquette once
and the plaquette at a place keys to its place. -/

/-- Two members at one plaquette key are one plaquette. -/
theorem plaqKey_inj (d L a k s a' k' s' : Nat) (hak : a < k) (hk : k < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hck : coordAt L k s < L)
    (hak' : a' < k') (hk' : k' < d) (hs' : s' < (L + 1) ^ d)
    (hca' : coordAt L a' s' < L) (hck' : coordAt L k' s' < L)
    (h : plaqKey d L a k s = plaqKey d L a' k' s') : a = a' ∧ k = k' ∧ s = s' := by
  have h1 := plaqKey_read d L a k s hak hk hs hca hck
  rw [h, plaqKey_read d L a' k' s' hak' hk' hs' hca' hck'] at h1
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg (fun q : Nat × Nat × Nat => q.2.1) h1).symm,
    (congrArg (fun q : Nat × Nat × Nat => q.2.2) h1).symm⟩

/-- Two valid plaquettes' keys read one key exactly at one plane and
one corner. -/
theorem plaqKey_beq (d L a k s a' k' s' : Nat) (hak : a < k) (hk : k < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hck : coordAt L k s < L)
    (hak' : a' < k') (hk' : k' < d) (hs' : s' < (L + 1) ^ d)
    (hca' : coordAt L a' s' < L) (hck' : coordAt L k' s' < L) :
    (plaqKey d L a k s == plaqKey d L a' k' s') = (a == a' && k == k' && s == s') := by
  cases haa : (a == a') with
  | true =>
    cases hkk : (k == k') with
    | true =>
      cases hss : (s == s') with
      | true =>
        rw [← beqEqOf haa, ← beqEqOf hkk, ← beqEqOf hss]
        exact eqBeqOf rfl
      | false =>
        show (plaqKey d L a k s == plaqKey d L a' k' s') = false
        refine neBeqOf (fun h => ?_)
        have h3 := (plaqKey_inj d L a k s a' k' s' hak hk hs hca hck hak' hk' hs' hca' hck' h).2.2
        rw [eqBeqOf h3] at hss
        exact Bool.noConfusion hss
    | false =>
      show (plaqKey d L a k s == plaqKey d L a' k' s') = false
      refine neBeqOf (fun h => ?_)
      have h2 := (plaqKey_inj d L a k s a' k' s' hak hk hs hca hck hak' hk' hs' hca' hck' h).2.1
      rw [eqBeqOf h2] at hkk
      exact Bool.noConfusion hkk
  | false =>
    show (plaqKey d L a k s == plaqKey d L a' k' s') = false
    refine neBeqOf (fun h => ?_)
    have h1 := (plaqKey_inj d L a k s a' k' s' hak hk hs hca hck hak' hk' hs' hca' hck' h).1
    rw [eqBeqOf h1] at haa
    exact Bool.noConfusion haa

/-- The plaquette list holds each plaquette once. -/
theorem plaqList_distinct (d L : Nat) : distinctList (plaqList d L) := by
  intro x hx
  show countOf x ((List.range d).flatMap (fun a => (List.range d).flatMap (fun k =>
    if a < k then (sites d L).filterMap (fun s =>
      if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none) else []))) ≤ 1
  rw [countOf_flatMap]
  refine famFold_le_one_at _ x.1 (List.range d) ?_ ?_
    (distinctList_all (distinctList_range d) x.1)
  · intro a _ hne
    refine countOf_zero_of_not_mem (fun hm => hne ?_)
    obtain ⟨k, _, hk⟩ := mem_flatMap_of _ _ _ hm
    exact (plaq_mem_plane d L a k x hk).1.symm
  · rw [countOf_flatMap]
    refine famFold_le_one_at _ x.2.1 (List.range d) ?_ ?_
      (distinctList_all (distinctList_range d) x.2.1)
    · intro k _ hne
      refine countOf_zero_of_not_mem (fun hm => hne ?_)
      exact (plaq_mem_plane d L x.1 k x hm).2.symm
    · by_cases hak : x.1 < x.2.1
      · rw [if_pos hak]
        refine countOf_filterMap_le_one _ x (sites d L)
          (fun a => distinctList_all (distinctList_range _) a) ?_
        intro a b _ _ hfa hfb
        have ha : a = x.2.2 := by
          by_cases hca : (decide (coordAt L x.1 a < L) && decide (coordAt L x.2.1 a < L)) = true
          · rw [if_pos hca] at hfa
            exact congrArg (fun q : Nat × Nat × Nat => q.2.2) (Option.some.inj hfa)
          · rw [if_neg hca] at hfa
            exact nomatch (show (none : Option (Nat × Nat × Nat)) = some x from hfa)
        have hb : b = x.2.2 := by
          by_cases hcb : (decide (coordAt L x.1 b < L) && decide (coordAt L x.2.1 b < L)) = true
          · rw [if_pos hcb] at hfb
            exact congrArg (fun q : Nat × Nat × Nat => q.2.2) (Option.some.inj hfb)
          · rw [if_neg hcb] at hfb
            exact nomatch (show (none : Option (Nat × Nat × Nat)) = some x from hfb)
        rw [ha, hb]
      · rw [if_neg hak]
        exact Nat.zero_le 1

/-- The plaquette at a place keys to its place. -/
theorem plaqKey_of_getAt (d L p : Nat) (hp : p < plaqCount d L) :
    plaqKey d L (getAt (0, 0, 0) (plaqList d L) p).1 (getAt (0, 0, 0) (plaqList d L) p).2.1
      (getAt (0, 0, 0) (plaqList d L) p).2.2 = p := by
  have hx : getAt (0, 0, 0) (plaqList d L) p ∈ plaqList d L :=
    mem_getAt (0, 0, 0) (plaqList d L) p hp
  generalize hxe : getAt (0, 0, 0) (plaqList d L) p = x at hx
  have hcount : countOf x (plaqList d L) = 1 :=
    Nat.le_antisymm (plaqList_distinct d L x hx) (countOf_pos_of_mem hx)
  have hfilt : ((plaqList d L).filter (fun b => tripleBeq x b)).length = 1 := by
    rw [length_filterBy]
    refine Eq.trans ?_ hcount
    show famFold Nat.add 0 (fun a => cond (tripleBeq x a) 1 0) (plaqList d L)
      = famFold Nat.add 0 (fun a => cond (decide (x = a)) 1 0) (plaqList d L)
    refine famFold_congr_members Nat.add 0 _ _ (plaqList d L) (fun a _ => ?_)
    cases hpa : tripleBeq x a with
    | true =>
      rw [tripleBeq_read x a hpa, decide_eq_true rfl]
    | false =>
      have hne : ¬ x = a := fun h => by
        rw [h, tripleBeq_refl] at hpa
        exact Bool.noConfusion hpa
      rw [decide_eq_false hne]
  have h := (posBy_once tripleBeq x (plaqList d L) hfilt p hp).1 (by
    show tripleBeq x (getAt (0, 0, 0) (plaqList d L) p) = true
    rw [hxe]
    exact tripleBeq_refl x)
  cases x with
  | mk a q' =>
    cases q' with
    | mk k s => exact h

/-! The plaquette and cube lists' folds: a read over the plaquettes
folds over the planes and the sites at the corners, a read over the
cubes at their places is the read over the cube list and folds over
the direction triples and the sites at the corners. -/

/-- A read over the plaquette list folds over the planes, the lower
direction first, and the sites at the plane's corners. -/
theorem bsum_plaq_planes (d L : Nat) (F : Nat × Nat × Nat → BPair) :
    (bsum F (plaqList d L)).oneValue
      (bsum (fun a => bsum (fun k => if a < k then
        bsum (fun s => if coordAt L a s < L && coordAt L k s < L then F (a, k, s) else BPair.unit)
          (List.range ((L + 1) ^ d)) else BPair.unit) (List.range d)) (List.range d)) := by
  delta plaqList
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun a _ => ?_)
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun k _ => ?_)
  by_cases hak : a < k
  · rw [if_pos hak, if_pos hak]
    refine BPair.oneValue_trans (famFold_filterMap_ov bpairFoldLaws _ F (sites d L)) ?_
    refine bsum_congr_range_ov _ _ ((L + 1) ^ d) (fun s _ => ?_)
    cases hc : (decide (coordAt L a s < L) && decide (coordAt L k s < L)) with
    | true => exact BPair.oneValue_refl _
    | false => exact BPair.oneValue_refl _
  · rw [if_neg hak, if_neg hak]
    exact BPair.oneValue_refl _

/-- A read over the cubes at their places is the read over the cube
list. -/
theorem bsum_cube_places (d L : Nat) (F : Nat × Nat × Nat × Nat → BPair) :
    bsum (fun c => F (getAt (0, 0, 0, 0) (cubeList d L) c)) (List.range (cubeCount d L))
      = bsum F (cubeList d L) := by
  rw [← bsum_map F (getAt (0, 0, 0, 0) (cubeList d L)) (List.range (cubeCount d L)),
    range_map_getAt (0, 0, 0, 0) (cubeCount d L) (cubeList d L) rfl]

/-- A read over the cube list folds over the direction triples in
order and the sites at the cubes' corners. -/
theorem bsum_cube_triples (d L : Nat) (F : Nat × Nat × Nat × Nat → BPair) :
    (bsum F (cubeList d L)).oneValue
      (bsum (fun a => bsum (fun b => bsum (fun c => if a < b && b < c then
        bsum (fun s => if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L
          then F (a, b, c, s) else BPair.unit) (List.range ((L + 1) ^ d))
        else BPair.unit) (List.range d)) (List.range d)) (List.range d)) := by
  delta cubeList
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun a _ => ?_)
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun b _ => ?_)
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun c _ => ?_)
  cases hab : (decide (a < b) && decide (b < c)) with
  | true =>
    refine BPair.oneValue_trans (famFold_filterMap_ov bpairFoldLaws _ F (sites d L)) ?_
    refine bsum_congr_range_ov _ _ ((L + 1) ^ d) (fun s _ => ?_)
    cases hc : (decide (coordAt L a s < L) && decide (coordAt L b s < L)
        && decide (coordAt L c s < L)) with
    | true => exact BPair.oneValue_refl _
    | false => exact BPair.oneValue_refl _
  | false => exact BPair.oneValue_refl _

/-- A plaquette vector read off the plaquette data at a plaquette's
key reads the data's value. -/
theorem plaqVec_entry (d L : Nat) (V : Nat × Nat × Nat → BPair) (a k s : Nat) (hak : a < k)
    (hk : k < d) (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hck : coordAt L k s < L) :
    getAt BPair.unit ((plaqList d L).map V) (plaqKey d L a k s) = V (a, k, s) := by
  rw [getAt_map (0, 0, 0) BPair.unit V _ _ (plaqKey_lt d L a k s hak hk hs hca hck),
    plaqKey_read d L a k s hak hk hs hca hck]

/-! The window's sites: a guarded read over the sites keyed to a
stated site reads the site's own, and keyed to a stated site's step
back along a direction reads the stepped-back site where the site's
coordinate there is occupied. -/

/-- A guarded read over the sites keyed to a site picks the site. -/
theorem bsum_site_beq (d L : Nat) (H : Nat → Bool) (X : Nat → BPair) (s0 : Nat)
    (hs0 : s0 < (L + 1) ^ d) :
    (bsum (fun c => if H c && c == s0 then X c else BPair.unit) (List.range ((L + 1) ^ d))).oneValue
      (if H s0 then X s0 else BPair.unit) := by
  refine BPair.oneValue_trans (bsum_range_at _ X s0 _ hs0 (fun c _ hc => beqEqOf (andSplitB hc).2))
    ?_
  rw [eqBeqOf (rfl : s0 = s0), Bool.and_true]
  exact BPair.oneValue_refl _

/-- A guarded read over the sites keyed to a site's step back along a
direction, the guard within the coordinate below the side, picks the
stepped-back site at an occupied coordinate and reads the sum's unit
at the first position. -/
theorem bsum_site_step (d L j : Nat) (H : Nat → Bool) (hH : ∀ c, H c = true → coordAt L j c < L)
    (X : Nat → BPair) (s0 : Nat) (hs0 : s0 < (L + 1) ^ d) :
    (bsum (fun c => if H c && stepAt L j c == s0 then X c else BPair.unit)
      (List.range ((L + 1) ^ d))).oneValue
      (if 0 < coordAt L j s0 then
        (if H (s0 - (L + 1) ^ j) then X (s0 - (L + 1) ^ j) else BPair.unit) else BPair.unit) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  cases Nat.eq_zero_or_pos (coordAt L j s0) with
  | inl hz =>
    have hn : ¬ 0 < coordAt L j s0 := by
      rw [hz]
      exact Nat.lt_irrefl 0
    rw [if_neg hn]
    refine bsum_range_none _ X _ (fun c _ => ?_)
    cases hst : (stepAt L j c == s0) with
    | false => exact Bool.and_false _
    | true =>
      cases hc : H c with
      | false => rfl
      | true =>
        have e1 : coordAt L j s0 = coordAt L j c + 1 := by
          rw [← beqEqOf hst]
          exact baseDigit_step (L + 1) j c hL (Nat.succ_lt_succ (hH c hc))
        rw [hz] at e1
        exact Nat.noConfusion e1
  | inr hpos =>
    rw [if_pos hpos]
    obtain ⟨hs0e, _, _⟩ := stepBack (L + 1) j s0 hL hpos
    have hlt : s0 - (L + 1) ^ j < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs0
    refine BPair.oneValue_trans (bsum_range_at _ X (s0 - (L + 1) ^ j) _ hlt (fun c _ hc => ?_)) ?_
    · refine addCancelR ((L + 1) ^ j) ?_
      rw [hs0e]
      exact beqEqOf (andSplitB hc).2
    · rw [eqBeqOf (show stepAt L j (s0 - (L + 1) ^ j) = s0 from hs0e), Bool.and_true]
      exact BPair.oneValue_refl _

/-- A read over the plaquettes supported on the first two
directions' plane folds over the sites at the plane's corners. -/
theorem bsum_plaq_plane (d L : Nat) (h1 : 1 < d) (F : Nat × Nat × Nat → BPair)
    (hoff : ∀ q, q ∈ plaqList d L → ¬ (q.1 = 0 ∧ q.2.1 = 1) → (F q).oneValue BPair.unit) :
    (bsum F (plaqList d L)).oneValue
      (bsum (fun s => if coordAt L 0 s < L && coordAt L 1 s < L then F (0, 1, s) else BPair.unit)
        (List.range ((L + 1) ^ d))) := by
  have h0 : 0 < d := Nat.lt_trans Nat.zero_lt_one h1
  refine BPair.oneValue_trans (bsum_plaq_planes d L F) ?_
  refine BPair.oneValue_trans (bsum_range_pick _ 0 d h0 (fun a ha ha0 => ?_)) ?_
  · refine foldB_null _ (List.range d) (fun k hk => ?_)
    refine BPair.oneValue_trans (ite_congr_prop _ (fun hak => foldB_null _
      (List.range ((L + 1) ^ d)) (fun s hs => ?_))) (BPair.oneValue_of_eq (ite_prop_unit _))
    refine BPair.oneValue_trans (ite_congr_prop _ (fun hc => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    exact hoff (a, k, s) (plaq_mem d L a k s hak (ltOfCountRange hk) (ltOfCountRange hs)
      (of_decide_eq_true (andSplitB hc).1) (of_decide_eq_true (andSplitB hc).2))
      (fun h => ha0 h.1)
  refine BPair.oneValue_trans (bsum_range_pick _ 1 d h1 (fun k hk hk1 => ?_)) ?_
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun h0k => foldB_null _
      (List.range ((L + 1) ^ d)) (fun s hs => ?_))) (BPair.oneValue_of_eq (ite_prop_unit _))
    refine BPair.oneValue_trans (ite_congr_prop _ (fun hc => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    exact hoff (0, k, s) (plaq_mem d L 0 k s h0k hk (ltOfCountRange hs)
      (of_decide_eq_true (andSplitB hc).1) (of_decide_eq_true (andSplitB hc).2))
      (fun h => hk1 h.2)
  rw [if_pos Nat.zero_lt_one]
  exact BPair.oneValue_refl _

/-- The plaquette list at the side nought is vacant. -/
theorem plaqList_side_zero (d : Nat) : plaqList d 0 = [] :=
  eq_nil_of_countOf _ (fun x => countOf_zero_of_not_mem
    (fun hx => Nat.not_lt_zero _ (plaq_of_mem d 0 x hx).2.2.2.1))

/-- The incidence's row at a plaquette: the signs at the
plaquette's boundary word over the link keys. -/
theorem incid_row (d L p : Nat) (hp : p < plaqCount d L) :
    getAt [] (incid d L) p
      = (List.range (linkCount d L)).map
          (signAt (plaqWord d L (getAt (0, 0, 0) (plaqList d L) p))) := by
  show getAt [] ((List.map (plaqWord d L) (plaqList d L)).map
    (fun w => (List.range (linkCount d L)).map (signAt w))) p = _
  rw [getAt_map [] [] _ _ p (by rw [length_map]; exact hp), getAt_map (0, 0, 0) [] _ _ p hp]

/-- A site sits off its step. -/
theorem step_ne (L k s : Nat) : ¬ s = stepAt L k s :=
  Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.pow_pos (Nat.succ_pos L)))

private theorem sqOne : (BPair.ofNat 1 * BPair.ofNat 1).oneValue (BPair.ofNat 1) := by
  decide +kernel

private theorem fourOnes : (BPair.ofNat 1 + (BPair.ofNat 1 + (BPair.ofNat 1
    + (BPair.ofNat 1 + BPair.unit)))).oneValue (BPair.ofNat 4) := by
  decide +kernel

/-- The incidence's row at a plaquette folds its entries' squares to
four, the boundary's link count: the Gram's diagonal
(`con:cornerwindow`). -/
theorem rowSq_read (d L p : Nat) (hp : p < plaqCount d L) :
    (dotP (getAt [] (incid d L) p) (getAt [] (incid d L) p)).oneValue (BPair.ofNat 4) := by
  rw [incid_row d L p hp]
  have hpl := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
  generalize hq : getAt (0, 0, 0) (plaqList d L) p = q at hpl ⊢
  obtain ⟨hak, hkd, hsd, hca, hck⟩ := hpl
  cases q with
  | mk a q' =>
  cases q' with
  | mk k s =>
  have had : a < d := Nat.lt_trans hak hkd
  have hne : ¬ k = a := fun h => Nat.ne_of_lt hak h.symm
  have hne' : ¬ a = k := Nat.ne_of_lt hak
  -- the four links' validity
  have v1 := linkKey_lt d L a s had hsd hca
  have v2 := linkKey_lt d L k (stepAt L a s) hkd (stepAt_lt d L a s had hsd hca)
    (by rw [coordAt_step_ne L a k s hca hne]; exact hck)
  have v3 := linkKey_lt d L a (stepAt L k s) had (stepAt_lt d L k s hkd hsd hck)
    (by rw [coordAt_step_ne L k a s hck hne']; exact hca)
  have v4 := linkKey_lt d L k s hkd hsd hck
  -- the keys pairwise distinct
  have i1 : linkKey d L a s = linkKey d L k (stepAt L a s) → False := fun h =>
    hne' (linkKey_inj d L a s k (stepAt L a s) had hsd hca hkd (stepAt_lt d L a s had hsd hca)
      (by rw [coordAt_step_ne L a k s hca hne]; exact hck) h).1
  have i2 : linkKey d L a s = linkKey d L a (stepAt L k s) → False := fun h =>
    step_ne L k s (linkKey_inj d L a s a (stepAt L k s) had hsd hca had
      (stepAt_lt d L k s hkd hsd hck) (by rw [coordAt_step_ne L k a s hck hne']; exact hca) h).2
  have i3 : linkKey d L a s = linkKey d L k s → False := fun h =>
    hne' (linkKey_inj d L a s k s had hsd hca hkd hsd hck h).1
  have i4 : linkKey d L k (stepAt L a s) = linkKey d L a (stepAt L k s) → False := fun h =>
    hne (linkKey_inj d L k (stepAt L a s) a (stepAt L k s) hkd (stepAt_lt d L a s had hsd hca)
      (by rw [coordAt_step_ne L a k s hca hne]; exact hck) had (stepAt_lt d L k s hkd hsd hck)
      (by rw [coordAt_step_ne L k a s hck hne']; exact hca) h).1
  have i5 : linkKey d L k (stepAt L a s) = linkKey d L k s → False := fun h =>
    step_ne L a s (linkKey_inj d L k (stepAt L a s) k s hkd (stepAt_lt d L a s had hsd hca)
      (by rw [coordAt_step_ne L a k s hca hne]; exact hck) hkd hsd hck h).2.symm
  have i6 : linkKey d L a (stepAt L k s) = linkKey d L k s → False := fun h =>
    hne' (linkKey_inj d L a (stepAt L k s) k s had (stepAt_lt d L k s hkd hsd hck)
      (by rw [coordAt_step_ne L k a s hck hne']; exact hca) hkd hsd hck h).1
  have hlen : ((List.range (linkCount d L)).map (signAt (plaqWord d L (a, k, s)))).length
      = linkCount d L := by
    rw [length_map, length_range]
  rw [dotP_fold (linkCount d L) _ _ hlen hlen]
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun l =>
    keyFoldB (fun a b => a == b) l ((plaqWord d L (a, k, s)).map
      (fun e => (e.1, if e.2 then BPair.ofNat 1 else (BPair.ofNat 1).swap)))
    * keyFoldB (fun a b => a == b) l ((plaqWord d L (a, k, s)).map
      (fun e => (e.1, if e.2 then BPair.ofNat 1 else (BPair.ofNat 1).swap))))
    (linkCount d L) (fun l hl => by
      rw [getAt_map 0 BPair.unit _ _ l (by rw [length_range]; exact hl), getAt_range _ l hl]
      exact BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_trans (bsum_keyFold_sq (linkCount d L) _ ?_ ?_) ?_
  · intro f hf
    cases hf with
    | head => exact v1
    | tail _ hf =>
      cases hf with
      | head => exact v2
      | tail _ hf =>
        cases hf with
        | head => exact v3
        | tail _ hf =>
          cases hf with
          | head => exact v4
          | tail _ hf => nomatch hf
  · intro x hx
    show countOf x [linkKey d L a s, linkKey d L k (stepAt L a s),
      linkKey d L a (stepAt L k s), linkKey d L k s] ≤ 1
    cases hx with
    | head =>
      rw [countOf_head, countOf_head_ne i1, countOf_head_ne i2, countOf_head_ne i3]
      exact Nat.le_refl 1
    | tail _ hx =>
      cases hx with
      | head =>
        rw [countOf_head_ne (fun h => i1 h.symm), countOf_head, countOf_head_ne i4,
          countOf_head_ne i5]
        exact Nat.le_refl 1
      | tail _ hx =>
        cases hx with
        | head =>
          rw [countOf_head_ne (fun h => i2 h.symm), countOf_head_ne (fun h => i4 h.symm),
            countOf_head, countOf_head_ne i6]
          exact Nat.le_refl 1
        | tail _ hx =>
          cases hx with
          | head =>
            rw [countOf_head_ne (fun h => i3 h.symm), countOf_head_ne (fun h => i5 h.symm),
              countOf_head_ne (fun h => i6 h.symm), countOf_head]
            exact Nat.le_refl 1
          | tail _ hx => nomatch hx
  · show (BPair.ofNat 1 * BPair.ofNat 1 + (BPair.ofNat 1 * BPair.ofNat 1
      + ((BPair.ofNat 1).swap * (BPair.ofNat 1).swap
        + ((BPair.ofNat 1).swap * (BPair.ofNat 1).swap + BPair.unit)))).oneValue (BPair.ofNat 4)
    exact BPair.oneValue_trans (BPair.add_congr sqOne (BPair.add_congr sqOne
      (BPair.add_congr swapOne_sq (BPair.add_congr swapOne_sq (BPair.oneValue_refl _))))) fourOnes

/-- The row read holds at every window, the diagonal's four. -/
theorem rowSqRead_all (d L : Nat) : rowSqRead d L :=
  all_range_intro (plaqCount d L) (fun p hp => decide_eq_true (rowSq_read d L p hp))

/-! The boundaries' fold at every window: a cube's six faces read a
link at two faces with exchanged traversals, so `Kᵀ N` reads the
sum's unit entrywise. -/

/-- A member of the cube list: three directions in order below the
count at a corner of the box with the three coordinates below the
side. -/
theorem cube_of_mem (d L : Nat) (c : Nat × Nat × Nat × Nat) (h : c ∈ cubeList d L) :
    c.1 < c.2.1 ∧ c.2.1 < c.2.2.1 ∧ c.2.2.1 < d ∧ c.2.2.2 < (L + 1) ^ d
      ∧ coordAt L c.1 c.2.2.2 < L ∧ coordAt L c.2.1 c.2.2.2 < L
      ∧ coordAt L c.2.2.1 c.2.2.2 < L := by
  obtain ⟨a, _, ha⟩ := mem_flatMap_of _ _ _ h
  obtain ⟨b, _, hb⟩ := mem_flatMap_of _ _ _ ha
  obtain ⟨c', hc, hc'⟩ := mem_flatMap_of _ _ _ hb
  have hcd : c' < d := ltOfMemRange hc
  by_cases hab : (decide (a < b) && decide (b < c')) = true
  · rw [if_pos hab] at hc'
    obtain ⟨s, hs, hf⟩ := mem_filterMap_of _ _ _ hc'
    have hsd : s < (L + 1) ^ d := ltOfMemRange hs
    by_cases hco : (decide (coordAt L a s < L) && decide (coordAt L b s < L)
        && decide (coordAt L c' s < L)) = true
    · rw [if_pos hco] at hf
      have hp : (a, b, c', s) = c := Option.some.inj hf
      rw [← hp]
      have h1 := andSplitB hab
      have h2 := andSplitB hco
      have h3 := andSplitB h2.1
      exact ⟨of_decide_eq_true h1.1, of_decide_eq_true h1.2, hcd, hsd, of_decide_eq_true h3.1,
        of_decide_eq_true h3.2, of_decide_eq_true h2.2⟩
    · rw [if_neg hco] at hf
      exact nomatch (show (none : Option (Nat × Nat × Nat × Nat)) = some c from hf)
  · rw [if_neg hab] at hc'
    exact nomatch hc'

/-- Two steps exchange. -/
theorem stepAt_comm (L a b s : Nat) : stepAt L a (stepAt L b s) = stepAt L b (stepAt L a s) :=
  Nat.add_right_comm s ((L + 1) ^ b) ((L + 1) ^ a)

/-- Two steps along one direction read one key exactly at one key. -/
theorem beq_step (L j x y : Nat) : (stepAt L j x == stepAt L j y) = (x == y) := by
  cases h : (x == y) with
  | true =>
    rw [beqEqOf h]
    exact eqBeqOf rfl
  | false =>
    refine neBeqOf (fun he => ?_)
    have := addCancelR ((L + 1) ^ j) he
    rw [eqBeqOf this] at h
    exact Bool.noConfusion h

/-- The incidence's entry at a plaquette's place and a link key. -/
theorem incid_entry_at (d L p l : Nat) (hp : p < plaqCount d L) (hl : l < linkCount d L) :
    getAt BPair.unit (getAt [] (incid d L) p) l
      = signAt (plaqWord d L (getAt (0, 0, 0) (plaqList d L) p)) l := by
  rw [incid_row d L p hp, getAt_map 0 BPair.unit _ _ l (by rw [length_range]; exact hl),
    getAt_range _ l hl]

/-- The incidence's entry at a plaquette's key and a link key: the
boundary word's sign at the link. -/
theorem incid_entry (d L a k s l : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (hl : l < linkCount d L) :
    getAt BPair.unit (getAt [] (incid d L) (plaqKey d L a k s)) l
      = signAt (plaqWord d L (a, k, s)) l := by
  rw [incid_entry_at d L _ l (plaqKey_lt d L a k s hak hk hs hca hck) hl,
    plaqKey_read d L a k s hak hk hs hca hck]

/-- A guarded read at two cubes at opposite products folds to the
sum's unit. -/
private theorem pairNull (g : Bool) (s σ s' σ' : BPair)
    (h : (s * σ + s' * σ').oneValue BPair.unit) :
    ((if g then s else BPair.unit) * σ
      + (if g then s' else BPair.unit) * σ').oneValue BPair.unit := by
  cases g with
  | true => exact h
  | false => exact BPair.add_units (BPair.unit_mul σ) (BPair.unit_mul σ')

/-- The boundaries' fold at a cube and a link: the six faces' signs
at the link fold to the sum's unit, each link of the cube on two
faces at exchanged traversals. -/
theorem bdEntry (d L : Nat) (c : Nat × Nat × Nat × Nat) (hc : c ∈ cubeList d L)
    (l : Nat) (hl : l < linkCount d L) :
    (bsum (fun p => getAt BPair.unit (getAt [] (incid d L) p) l * faceSign (cubeFaces d L c) p)
      (List.range (plaqCount d L))).oneValue BPair.unit := by
  have hcl := cube_of_mem d L c hc
  cases c with
  | mk a c1 =>
  cases c1 with
  | mk b c2 =>
  cases c2 with
  | mk c' s =>
  obtain ⟨hab, hbc, hcd, hsd, hca, hcb, hcc⟩ := hcl
  have hbd : b < d := Nat.lt_trans hbc hcd
  have had : a < d := Nat.lt_trans hab hbd
  have hac : a < c' := Nat.lt_trans hab hbc
  have nab : ¬ a = b := Nat.ne_of_lt hab
  have nac : ¬ a = c' := Nat.ne_of_lt hac
  have nbc : ¬ b = c' := Nat.ne_of_lt hbc
  have sC := stepAt_lt d L c' s hcd hsd hcc
  have sB := stepAt_lt d L b s hbd hsd hcb
  have sA := stepAt_lt d L a s had hsd hca
  have caC : coordAt L a (stepAt L c' s) < L := by
    rw [coordAt_step_ne L c' a s hcc nac]
    exact hca
  have cbC : coordAt L b (stepAt L c' s) < L := by
    rw [coordAt_step_ne L c' b s hcc nbc]
    exact hcb
  have caB : coordAt L a (stepAt L b s) < L := by
    rw [coordAt_step_ne L b a s hcb nab]
    exact hca
  have ccB : coordAt L c' (stepAt L b s) < L := by
    rw [coordAt_step_ne L b c' s hcb (fun h => nbc h.symm)]
    exact hcc
  have cbA : coordAt L b (stepAt L a s) < L := by
    rw [coordAt_step_ne L a b s hca (fun h => nab h.symm)]
    exact hcb
  have ccA : coordAt L c' (stepAt L a s) < L := by
    rw [coordAt_step_ne L a c' s hca (fun h => nac h.symm)]
    exact hcc
  show (bsum (fun p => getAt BPair.unit (getAt [] (incid d L) p) l
    * keyFoldB (fun a b => a == b) p (cubeFaces d L (a, b, c', s)))
      (List.range (plaqCount d L))).oneValue BPair.unit
  refine BPair.oneValue_trans (bsum_keyFold_linear (plaqCount d L) _
    (cubeFaces d L (a, b, c', s)) ?_) ?_
  · intro f hf
    cases hf with
    | head => exact plaqKey_lt d L a b s hab hbd hsd hca hcb
    | tail _ hf =>
      cases hf with
      | head => exact plaqKey_lt d L a b (stepAt L c' s) hab hbd sC caC cbC
      | tail _ hf =>
        cases hf with
        | head => exact plaqKey_lt d L a c' s hac hcd hsd hca hcc
        | tail _ hf =>
          cases hf with
          | head => exact plaqKey_lt d L a c' (stepAt L b s) hac hcd sB caB ccB
          | tail _ hf =>
            cases hf with
            | head => exact plaqKey_lt d L b c' s hbc hcd hsd hcb hcc
            | tail _ hf =>
              cases hf with
              | head => exact plaqKey_lt d L b c' (stepAt L a s) hbc hcd sA cbA ccA
              | tail _ hf => nomatch hf
  · show (getAt BPair.unit (getAt [] (incid d L) (plaqKey d L a b s)) l * BPair.ofNat 1
      + (getAt BPair.unit (getAt [] (incid d L) (plaqKey d L a b (stepAt L c' s))) l
          * (BPair.ofNat 1).swap
      + (getAt BPair.unit (getAt [] (incid d L) (plaqKey d L a c' s)) l * (BPair.ofNat 1).swap
      + (getAt BPair.unit (getAt [] (incid d L) (plaqKey d L a c' (stepAt L b s))) l
          * BPair.ofNat 1
      + (getAt BPair.unit (getAt [] (incid d L) (plaqKey d L b c' s)) l * BPair.ofNat 1
      + (getAt BPair.unit (getAt [] (incid d L) (plaqKey d L b c' (stepAt L a s))) l
          * (BPair.ofNat 1).swap
      + BPair.unit)))))).oneValue BPair.unit
    rw [incid_entry d L a b s l hab hbd hsd hca hcb hl,
      incid_entry d L a b (stepAt L c' s) l hab hbd sC caC cbC hl,
      incid_entry d L a c' s l hac hcd hsd hca hcc hl,
      incid_entry d L a c' (stepAt L b s) l hac hcd sB caB ccB hl,
      incid_entry d L b c' s l hbc hcd hsd hcb hcc hl,
      incid_entry d L b c' (stepAt L a s) l hbc hcd sA cbA ccA hl]
    show (((if linkKey d L a s == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L b (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L a (stepAt L b s) == l then (BPair.ofNat 1).swap else BPair.unit) + ((if linkKey d L b s == l then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))) * BPair.ofNat 1 + (((if linkKey d L a (stepAt L c' s) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L b (stepAt L a (stepAt L c' s)) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L a (stepAt L b (stepAt L c' s)) == l then (BPair.ofNat 1).swap else BPair.unit) + ((if linkKey d L b (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))) * (BPair.ofNat 1).swap + (((if linkKey d L a s == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L c' (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L a (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit) + ((if linkKey d L c' s == l then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))) * (BPair.ofNat 1).swap + (((if linkKey d L a (stepAt L b s) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L c' (stepAt L a (stepAt L b s)) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L a (stepAt L c' (stepAt L b s)) == l then (BPair.ofNat 1).swap else BPair.unit) + ((if linkKey d L c' (stepAt L b s) == l then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))) * BPair.ofNat 1 + (((if linkKey d L b s == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L c' (stepAt L b s) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L b (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit) + ((if linkKey d L c' s == l then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))) * BPair.ofNat 1 + (((if linkKey d L b (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L c' (stepAt L b (stepAt L a s)) == l then BPair.ofNat 1 else BPair.unit) + ((if linkKey d L b (stepAt L c' (stepAt L a s)) == l then (BPair.ofNat 1).swap else BPair.unit) + ((if linkKey d L c' (stepAt L a s) == l then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))) * (BPair.ofNat 1).swap + (BPair.unit))))))).oneValue BPair.unit
    rw [stepAt_comm L c' a s, stepAt_comm L c' b s, stepAt_comm L b a s]
    refine BPair.oneValue_trans (polEqB
      [(if linkKey d L a s == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L b (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L a (stepAt L b s) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L b s == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L a (stepAt L c' s) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L b (stepAt L a (stepAt L c' s)) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L a (stepAt L b (stepAt L c' s)) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L b (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L a s == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L c' (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L a (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L c' s == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L a (stepAt L b s) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L c' (stepAt L a (stepAt L b s)) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L a (stepAt L b (stepAt L c' s)) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L c' (stepAt L b s) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L b s == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L c' (stepAt L b s) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L b (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L c' s == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L b (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L c' (stepAt L a (stepAt L b s)) == l then BPair.ofNat 1 else BPair.unit),
      (if linkKey d L b (stepAt L a (stepAt L c' s)) == l then (BPair.ofNat 1).swap else BPair.unit),
      (if linkKey d L c' (stepAt L a s) == l then (BPair.ofNat 1).swap else BPair.unit),
      BPair.ofNat 1,
      (BPair.ofNat 1).swap,
      BPair.unit]
      (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 26)))))) (Pol.mon (Mon.var 24))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.var 5)) (Pol.add (Pol.mon (Mon.var 6)) (Pol.add (Pol.mon (Mon.var 7)) (Pol.mon (Mon.var 26)))))) (Pol.mon (Mon.var 25))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 8)) (Pol.add (Pol.mon (Mon.var 9)) (Pol.add (Pol.mon (Mon.var 10)) (Pol.add (Pol.mon (Mon.var 11)) (Pol.mon (Mon.var 26)))))) (Pol.mon (Mon.var 25))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 12)) (Pol.add (Pol.mon (Mon.var 13)) (Pol.add (Pol.mon (Mon.var 14)) (Pol.add (Pol.mon (Mon.var 15)) (Pol.mon (Mon.var 26)))))) (Pol.mon (Mon.var 24))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 16)) (Pol.add (Pol.mon (Mon.var 17)) (Pol.add (Pol.mon (Mon.var 18)) (Pol.add (Pol.mon (Mon.var 19)) (Pol.mon (Mon.var 26)))))) (Pol.mon (Mon.var 24))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 20)) (Pol.add (Pol.mon (Mon.var 21)) (Pol.add (Pol.mon (Mon.var 22)) (Pol.add (Pol.mon (Mon.var 23)) (Pol.mon (Mon.var 26)))))) (Pol.mon (Mon.var 25))) (Pol.mon (Mon.var 26))))))))
      (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 24))) (Pol.mul (Pol.mon (Mon.var 8)) (Pol.mon (Mon.var 25)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 24))) (Pol.mul (Pol.mon (Mon.var 20)) (Pol.mon (Mon.var 25)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 24))) (Pol.mul (Pol.mon (Mon.var 12)) (Pol.mon (Mon.var 24)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 24))) (Pol.mul (Pol.mon (Mon.var 16)) (Pol.mon (Mon.var 24)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 25))) (Pol.mul (Pol.mon (Mon.var 10)) (Pol.mon (Mon.var 25)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 5)) (Pol.mon (Mon.var 25))) (Pol.mul (Pol.mon (Mon.var 22)) (Pol.mon (Mon.var 25)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 6)) (Pol.mon (Mon.var 25))) (Pol.mul (Pol.mon (Mon.var 14)) (Pol.mon (Mon.var 24)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 7)) (Pol.mon (Mon.var 25))) (Pol.mul (Pol.mon (Mon.var 18)) (Pol.mon (Mon.var 24)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 9)) (Pol.mon (Mon.var 25))) (Pol.mul (Pol.mon (Mon.var 23)) (Pol.mon (Mon.var 25)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 11)) (Pol.mon (Mon.var 25))) (Pol.mul (Pol.mon (Mon.var 19)) (Pol.mon (Mon.var 24)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 13)) (Pol.mon (Mon.var 24))) (Pol.mul (Pol.mon (Mon.var 21)) (Pol.mon (Mon.var 25)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 15)) (Pol.mon (Mon.var 24))) (Pol.mul (Pol.mon (Mon.var 17)) (Pol.mon (Mon.var 24)))) (Pol.add (Pol.mul (Pol.mon (Mon.var 26)) (Pol.mon (Mon.var 24))) (Pol.add (Pol.mul (Pol.mon (Mon.var 26)) (Pol.mon (Mon.var 24))) (Pol.add (Pol.mul (Pol.mon (Mon.var 26)) (Pol.mon (Mon.var 24))) (Pol.add (Pol.mul (Pol.mon (Mon.var 26)) (Pol.mon (Mon.var 25))) (Pol.add (Pol.mul (Pol.mon (Mon.var 26)) (Pol.mon (Mon.var 25))) (Pol.add (Pol.mul (Pol.mon (Mon.var 26)) (Pol.mon (Mon.var 25))) (Pol.mon (Mon.var 26))))))))))))))))))))
      (by decide +kernel)) ?_
    show (((if linkKey d L a s == l then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if linkKey d L a s == l then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if linkKey d L b (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if linkKey d L b (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if linkKey d L a (stepAt L b s) == l then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if linkKey d L a (stepAt L b s) == l then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if linkKey d L b s == l then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if linkKey d L b s == l then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if linkKey d L a (stepAt L c' s) == l then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if linkKey d L a (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if linkKey d L b (stepAt L a (stepAt L c' s)) == l then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if linkKey d L b (stepAt L a (stepAt L c' s)) == l then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if linkKey d L a (stepAt L b (stepAt L c' s)) == l then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if linkKey d L a (stepAt L b (stepAt L c' s)) == l then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if linkKey d L b (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if linkKey d L b (stepAt L c' s) == l then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if linkKey d L c' (stepAt L a s) == l then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if linkKey d L c' (stepAt L a s) == l then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if linkKey d L c' s == l then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if linkKey d L c' s == l then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if linkKey d L c' (stepAt L a (stepAt L b s)) == l then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if linkKey d L c' (stepAt L a (stepAt L b s)) == l then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if linkKey d L c' (stepAt L b s) == l then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if linkKey d L c' (stepAt L b s) == l then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + ((BPair.unit * BPair.ofNat 1 + (BPair.unit * BPair.ofNat 1 + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit)))))))))))))))))))).oneValue BPair.unit
    exact BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.oneValue_refl _))))))))))))))))))

/-- A window with plaquette count nought holds no cube: a cube's
corner face is a plaquette. -/
private theorem cubeCount_zero (d L : Nat) (hz : plaqCount d L = 0) : cubeCount d L = 0 := by
  rcases Nat.eq_zero_or_pos (cubeCount d L) with hc | hc
  · exact hc
  · obtain ⟨hab, hbc, hcd, hsd, hca, hcb, _⟩ :=
      cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) 0 hc)
    have hk := plaqKey_lt d L _ _ _ hab (Nat.lt_trans hbc hcd) hsd hca hcb
    rw [hz] at hk
    exact absurd hk (Nat.not_lt_zero _)

/-- The transposed cubes' boundaries' count is the cubes' at every
window: at an occupied plaquette count by the rows' width, and at
plaquette count nought both counts read nought. -/
private theorem cubeBdT_length (d L : Nat) :
    (transposeM (cubeBd d L)).length = cubeCount d L := by
  rcases Nat.eq_zero_or_pos (plaqCount d L) with hz | hp
  · have hnil : cubeBd d L = [] := by
      show (List.range (plaqCount d L)).map _ = []
      rw [hz]
      rfl
    rw [hnil, cubeCount_zero d L hz]
    rfl
  · exact length_transposeM _ (cubeBd_rows d L) (by rw [cubeBd_length]; exact hp)

/-- The boundaries' fold read holds at every window: `Kᵀ N` reads the
sum's unit entrywise, each link of a cube on two faces at exchanged
traversals (`con:cornerwindow`). -/
theorem bdRead_all (d L : Nat) : bdRead d L := by
  show matNull (matMul (transposeM (incid d L)) (cubeBd d L))
  have hlen := incid_length d L
  have hK := incid_rows d L
  have hNlen := cubeBd_length d L
  have hN := cubeBd_rows d L
  cases hI : incid d L with
  | nil => exact trivial
  | cons r t =>
    have hpos : 0 < (r :: t).length := Nat.succ_pos _
    rw [hI] at hlen hK
    have hKt : (transposeM (r :: t)).length = linkCount d L := length_transposeM _ hK hpos
    have hNt : (transposeM (cubeBd d L)).length = cubeCount d L := cubeBdT_length d L
    refine matNull_map_idx [] _ (transposeM (r :: t)) (fun i hi => ?_)
    have hi' : i < linkCount d L := by rw [← hKt]; exact hi
    refine poly.unitTail_of_getAt (fun k => ?_)
    cases Nat.lt_or_ge k (transposeM (cubeBd d L)).length with
    | inr hk =>
      rw [getAt_over _ _ k (by rw [ground.length_map]; exact hk)]
      exact BPair.oneValue_refl _
    | inl hk =>
      have hk' : k < cubeCount d L := by rw [← hNt]; exact hk
      rw [getAt_map [] BPair.unit _ _ k hk]
      refine BPair.oneValue_trans (dotN_read _ _) ?_
      have hr1 : (getAt [] (transposeM (r :: t)) i).length = plaqCount d L := by
        rw [rowsLen_getAt _ i (rowsLen_transposeM (r :: t)) hi]
        exact hlen
      have hr2 : (getAt [] (transposeM (cubeBd d L)) k).length = plaqCount d L := by
        rw [rowsLen_getAt _ k (rowsLen_transposeM (cubeBd d L)) hk]
        exact hNlen
      rw [dotP_fold (plaqCount d L) _ _ hr1 hr2]
      refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun p =>
        getAt BPair.unit (getAt [] (incid d L) p) i
          * faceSign (cubeFaces d L (getAt (0, 0, 0, 0) (cubeList d L) k)) p)
        (plaqCount d L) (fun p hp => ?_)) ?_
      · rw [getAt_transposeM BPair.unit (r :: t) hK i p hi' (by rw [hlen]; exact hp),
          getAt_transposeM BPair.unit (cubeBd d L) hN k p hk' (by rw [hNlen]; exact hp), ← hI,
          cubeBd_entry d L p k hp hk']
        exact BPair.oneValue_refl _
      · exact bdEntry d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) k hk') i hi'

/-! A link's column read: the moved vector's entry at a link key over
the plaquettes holding the link. -/

/-- Two valid links' keys read one key exactly at one direction and
one site. -/
theorem linkKey_beq (d L a s e s' : Nat) (ha : a < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (he : e < d) (hs' : s' < (L + 1) ^ d)
    (hce : coordAt L e s' < L) :
    (linkKey d L a s == linkKey d L e s') = (a == e && s == s') := by
  cases hae : (a == e) with
  | true =>
    cases hss : (s == s') with
    | true =>
      rw [beqEqOf hae, beqEqOf hss]
      exact eqBeqOf rfl
    | false =>
      show (linkKey d L a s == linkKey d L e s') = false
      refine neBeqOf (fun h => ?_)
      have h2 := (linkKey_inj d L a s e s' ha hs hca he hs' hce h).2
      rw [eqBeqOf h2] at hss
      exact Bool.noConfusion hss
  | false =>
    show (linkKey d L a s == linkKey d L e s') = false
    refine neBeqOf (fun h => ?_)
    have h1 := (linkKey_inj d L a s e s' ha hs hca he hs' hce h).1
    rw [eqBeqOf h1] at hae
    exact Bool.noConfusion hae

/-- A sign's read against a member folds the sign into the member's
side: one at a forward traversal, the memberwise swap backward. -/
private theorem iteMul (c : Bool) (x : BPair) :
    ((if c then BPair.ofNat 1 else BPair.unit) * x).oneValue (if c then x else BPair.unit)
      ∧ ((if c then (BPair.ofNat 1).swap else BPair.unit) * x).oneValue
          (if c then x.swap else BPair.unit) := by
  cases c with
  | true =>
    exact ⟨BPair.ofNat_one_mul x, BPair.oneValue_trans
      (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_swap x (BPair.ofNat 1)))
        (swap_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
          (BPair.ofNat_one_mul x))))⟩
  | false => exact ⟨BPair.unit_mul x, BPair.unit_mul x⟩

/-- A read over the links at their places is the read over the link
list. -/
theorem bsum_link_places (d L : Nat) (F : Nat × Nat → BPair) :
    bsum (fun l => F (getAt (0, 0) (linkList d L) l)) (List.range (linkCount d L))
      = bsum F (linkList d L) := by
  rw [← bsum_map F (getAt (0, 0) (linkList d L)) (List.range (linkCount d L)),
    range_map_getAt (0, 0) (linkCount d L) (linkList d L) rfl]

/-- A read over the link list folds over the directions and the
sites at the links. -/
theorem bsum_link_sites (d L : Nat) (F : Nat × Nat → BPair) :
    (bsum F (linkList d L)).oneValue
      (bsum (fun e => bsum (fun s => if coordAt L e s < L then F (e, s) else BPair.unit)
        (List.range ((L + 1) ^ d))) (List.range d)) := by
  show (bsum F ((List.range d).flatMap (fun e => (sites d L).filterMap (fun s =>
    if coordAt L e s < L then some (e, s) else none)))).oneValue _
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun e _ => ?_)
  refine BPair.oneValue_trans (famFold_filterMap_ov bpairFoldLaws _ _ (sites d L)) ?_
  refine bsum_congr_range_ov _ _ ((L + 1) ^ d) (fun s _ => ?_)
  by_cases hc : coordAt L e s < L
  · rw [if_pos hc, if_pos hc]
    exact BPair.oneValue_refl _
  · rw [if_neg hc, if_neg hc]
    exact BPair.oneValue_refl _

/-- A read over the plaquettes at their places is the read over the
plaquette list. -/
theorem bsum_plaq_places (d L : Nat) (F : Nat × Nat × Nat → BPair) :
    bsum (fun p => F (getAt (0, 0, 0) (plaqList d L) p)) (List.range (plaqCount d L))
      = bsum F (plaqList d L) := by
  rw [← bsum_map F (getAt (0, 0, 0) (plaqList d L)) (List.range (plaqCount d L)),
    range_map_getAt (0, 0, 0) (plaqCount d L) (plaqList d L) rfl]

/-- The incidence's entry at a plaquette's place and a link's key:
the four boundary reads holding the link, the base link and the
corner's higher link forward and the two further links backward. -/
theorem incid_entry_link (d L p e s' : Nat) (hp : p < plaqCount d L) (he : e < d)
    (hs' : s' < (L + 1) ^ d) (hce : coordAt L e s' < L) :
    getAt BPair.unit (getAt [] (incid d L) p) (linkKey d L e s')
      = (if (getAt (0, 0, 0) (plaqList d L) p).1 == e
            && (getAt (0, 0, 0) (plaqList d L) p).2.2 == s' then BPair.ofNat 1 else BPair.unit)
        + ((if (getAt (0, 0, 0) (plaqList d L) p).2.1 == e
            && stepAt L (getAt (0, 0, 0) (plaqList d L) p).1 (getAt (0, 0, 0) (plaqList d L) p).2.2
              == s' then BPair.ofNat 1 else BPair.unit)
        + ((if (getAt (0, 0, 0) (plaqList d L) p).1 == e
            && stepAt L (getAt (0, 0, 0) (plaqList d L) p).2.1 (getAt (0, 0, 0) (plaqList d L) p).2.2
              == s' then (BPair.ofNat 1).swap else BPair.unit)
        + ((if (getAt (0, 0, 0) (plaqList d L) p).2.1 == e
            && (getAt (0, 0, 0) (plaqList d L) p).2.2 == s' then (BPair.ofNat 1).swap
            else BPair.unit) + BPair.unit))) := by
  rw [incid_entry_at d L p _ hp (linkKey_lt d L e s' he hs' hce)]
  have hpl := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
  generalize hq : getAt (0, 0, 0) (plaqList d L) p = q at hpl ⊢
  obtain ⟨hak, hkd, hsd, hca, hck⟩ := hpl
  cases q with
  | mk a q' =>
  cases q' with
  | mk k s =>
  have had : a < d := Nat.lt_trans hak hkd
  have hne : ¬ k = a := fun h => Nat.ne_of_lt hak h.symm
  have hne' : ¬ a = k := Nat.ne_of_lt hak
  show (if linkKey d L a s == linkKey d L e s' then BPair.ofNat 1 else BPair.unit)
    + ((if linkKey d L k (stepAt L a s) == linkKey d L e s' then BPair.ofNat 1 else BPair.unit)
    + ((if linkKey d L a (stepAt L k s) == linkKey d L e s' then (BPair.ofNat 1).swap
        else BPair.unit)
    + ((if linkKey d L k s == linkKey d L e s' then (BPair.ofNat 1).swap else BPair.unit)
    + BPair.unit))) = _
  rw [linkKey_beq d L a s e s' had hsd hca he hs' hce,
    linkKey_beq d L k (stepAt L a s) e s' hkd (stepAt_lt d L a s had hsd hca)
      (by rw [coordAt_step_ne L a k s hca hne]; exact hck) he hs' hce,
    linkKey_beq d L a (stepAt L k s) e s' had (stepAt_lt d L k s hkd hsd hck)
      (by rw [coordAt_step_ne L k a s hck hne']; exact hca) he hs' hce,
    linkKey_beq d L k s e s' hkd hsd hck he hs' hce]

/-- A link's column read: the moved vector's entry at a link's key,
at a plaquette vector read off the plaquette data, folds over the
plaquette list the four boundary reads holding the link, the base
link and the corner's higher link forward and the two further
links backward. -/
theorem colRead (d L e s' : Nat) (he : e < d) (hs' : s' < (L + 1) ^ d)
    (hce : coordAt L e s' < L) (V : Nat × Nat × Nat → BPair) :
    (getAt BPair.unit (matVec (transposeM (incid d L)) ((plaqList d L).map V))
      (linkKey d L e s')).oneValue
      (bsum (fun q =>
        (if q.1 == e && q.2.2 == s' then V q else BPair.unit)
        + ((if q.2.1 == e && stepAt L q.1 q.2.2 == s' then V q else BPair.unit)
        + ((if q.1 == e && stepAt L q.2.1 q.2.2 == s' then (V q).swap else BPair.unit)
        + (if q.2.1 == e && q.2.2 == s' then (V q).swap else BPair.unit)))) (plaqList d L)) := by
  have hl : linkKey d L e s' < linkCount d L := linkKey_lt d L e s' he hs' hce
  have hlen := incid_length d L
  have hK := incid_rows d L
  have hV : ((plaqList d L).map V).length = plaqCount d L := by
    rw [ground.length_map]
    rfl
  -- the sum over the plaquette list as the sum over the places
  refine BPair.oneValue_trans ?_ (BPair.oneValue_of_eq (bsum_plaq_places d L _))
  cases hI : incid d L with
  | nil =>
    -- the plaquette list vacant, both sides the sum's unit
    have h0 : plaqCount d L = 0 := by
      rw [← hlen, hI]
      rfl
    rw [h0]
    exact BPair.oneValue_refl _
  | cons r t =>
    rw [hI] at hlen hK
    have hpos : 0 < (r :: t).length := Nat.succ_pos _
    refine BPair.oneValue_trans (getAt_matVec_transposeM (r :: t) hK hpos _
      (by rw [hV]; exact hlen.symm) _ hl) ?_
    rw [hlen]
    refine bsum_congr_range_ov _ _ (plaqCount d L) (fun p hp => ?_)
    rw [← hI, incid_entry_link d L p e s' hp he hs' hce,
      getAt_map (0, 0, 0) BPair.unit V _ p hp,
      BPair.right_distrib, BPair.right_distrib, BPair.right_distrib, BPair.right_distrib]
    refine BPair.add_congr (iteMul _ _).1 (BPair.add_congr (iteMul _ _).1
      (BPair.add_congr (iteMul _ _).2 ?_))
    exact BPair.oneValue_trans (BPair.add_congr (iteMul _ _).2 (BPair.unit_mul _))
      (BPair.add_unit _)



/-- A plane's site fold of the four boundary reads at a link: the
plane through the link's direction as its lower direction reads the
plaquette at the link's tail forward and the plaquette stepped back
along the higher direction backward; the plane through the link's
direction as its higher direction reads the plaquette stepped back
along the lower direction forward and the plaquette at the tail
backward; and a plane off the direction reads the sum's unit. -/
private theorem plane_col (d L e s' a k : Nat) (hak : a < k)
    (hs' : s' < (L + 1) ^ d) (hce : coordAt L e s' < L) (V : Nat × Nat × Nat → BPair) :
    (bsum (fun s => if coordAt L a s < L && coordAt L k s < L then
        (if a == e && s == s' then V (a, k, s) else BPair.unit)
        + ((if k == e && stepAt L a s == s' then V (a, k, s) else BPair.unit)
        + ((if a == e && stepAt L k s == s' then (V (a, k, s)).swap else BPair.unit)
        + (if k == e && s == s' then (V (a, k, s)).swap else BPair.unit)))
      else BPair.unit) (List.range ((L + 1) ^ d))).oneValue
      ((if a == e then
          (if decide (coordAt L k s' < L) then V (a, k, s') else BPair.unit)
          + (if 0 < coordAt L k s' then (V (a, k, s' - (L + 1) ^ k)).swap else BPair.unit)
        else BPair.unit)
      + (if k == e then
          (if 0 < coordAt L a s' then V (a, k, s' - (L + 1) ^ a) else BPair.unit)
          + (if decide (coordAt L a s' < L) then (V (a, k, s')).swap else BPair.unit)
        else BPair.unit)) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  have hak' : ¬ a = k := Nat.ne_of_lt hak
  cases hae : (a == e) with
  | true =>
    have hae' : a = e := beqEqOf hae
    have hke : (k == e) = false := by
      refine neBeqOf (fun h => hak' ?_)
      rw [hae', h]
    rw [hke]
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s =>
      (if (coordAt L a s < L && coordAt L k s < L) && s == s' then V (a, k, s) else BPair.unit)
      + (if (coordAt L a s < L && coordAt L k s < L) && stepAt L k s == s' then (V (a, k, s)).swap
          else BPair.unit)) _ (fun s _ => ?_)) ?_
    · repeat rw [Bool.true_and]
      repeat rw [Bool.false_and]
      repeat rw [iteB_false]
      rw [← ite_ite_and (coordAt L a s < L && coordAt L k s < L) (s == s'),
        ← ite_ite_and (coordAt L a s < L && coordAt L k s < L) (stepAt L k s == s')]
      refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (ite_add_unit _ _ _)
      exact BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_trans (BPair.unit_add _)
        (BPair.add_unit _))
    refine BPair.oneValue_trans (foldB_add _ _ _) ?_
    refine BPair.oneValue_trans (BPair.add_congr
      (bsum_site_beq d L (fun s => coordAt L a s < L && coordAt L k s < L) (fun s => V (a, k, s)) s' hs')
      (bsum_site_step d L k (fun s => coordAt L a s < L && coordAt L k s < L)
        (fun c hc => of_decide_eq_true (andSplitB hc).2) (fun s => (V (a, k, s)).swap) s' hs')) ?_
    refine BPair.oneValue_symm (BPair.oneValue_trans (BPair.add_unit _) ?_)
    subst hae'
    rw [iteB_true, decide_eq_true hce, Bool.true_and]
    refine BPair.add_congr (BPair.oneValue_refl _) (ite_congr_prop _ (fun hpos => ?_))
    obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) k s' hL hpos
    have hca : coordAt L a (s' - (L + 1) ^ k) < L := by
      rw [show coordAt L a (s' - (L + 1) ^ k) = coordAt L a s' from hoff a hak']
      exact hce
    have hck : coordAt L k (s' - (L + 1) ^ k) < L := by
      have h := baseDigit_lt (L + 1) k s' hL
      rw [← hd] at h
      exact Nat.lt_of_succ_lt_succ h
    rw [decide_eq_true hca, decide_eq_true hck]
    exact BPair.oneValue_refl _
  | false =>
    cases hke : (k == e) with
    | true =>
      have hke' : k = e := beqEqOf hke
      refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s =>
        (if (coordAt L a s < L && coordAt L k s < L) && stepAt L a s == s' then V (a, k, s)
            else BPair.unit)
        + (if (coordAt L a s < L && coordAt L k s < L) && s == s' then (V (a, k, s)).swap
            else BPair.unit)) _ (fun s _ => ?_)) ?_
      · repeat rw [Bool.true_and]
        repeat rw [Bool.false_and]
        repeat rw [iteB_false]
        rw [← ite_ite_and (coordAt L a s < L && coordAt L k s < L) (stepAt L a s == s'),
          ← ite_ite_and (coordAt L a s < L && coordAt L k s < L) (s == s')]
        refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (ite_add_unit _ _ _)
        exact BPair.oneValue_trans (BPair.unit_add _)
          (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_add _))
      refine BPair.oneValue_trans (foldB_add _ _ _) ?_
      refine BPair.oneValue_trans (BPair.add_congr
        (bsum_site_step d L a (fun s => coordAt L a s < L && coordAt L k s < L)
          (fun c hc => of_decide_eq_true (andSplitB hc).1) (fun s => V (a, k, s)) s' hs')
        (bsum_site_beq d L (fun s => coordAt L a s < L && coordAt L k s < L)
          (fun s => (V (a, k, s)).swap) s' hs')) ?_
      refine BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) ?_)
      subst hke'
      rw [iteB_true, decide_eq_true hce, Bool.and_true]
      refine BPair.add_congr (ite_congr_prop _ (fun hpos => ?_)) (BPair.oneValue_refl _)
      obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) a s' hL hpos
      have hck : coordAt L k (s' - (L + 1) ^ a) < L := by
        rw [show coordAt L k (s' - (L + 1) ^ a) = coordAt L k s' from
          hoff k (fun h => hak' h.symm)]
        exact hce
      have hca : coordAt L a (s' - (L + 1) ^ a) < L := by
        have h := baseDigit_lt (L + 1) a s' hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [decide_eq_true hca, decide_eq_true hck]
      exact BPair.oneValue_refl _
    | false =>
      refine BPair.oneValue_trans (foldB_nullRange _ _ (fun s _ => ?_)) ?_
      · repeat rw [Bool.false_and]
        repeat rw [iteB_false]
        refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => BPair.add_units
          (BPair.oneValue_refl _) (BPair.add_units (BPair.oneValue_refl _)
            (BPair.unit_add _)))) ?_
        exact BPair.oneValue_of_eq (ite_prop_unit _)
      · exact BPair.oneValue_symm (BPair.unit_add _)

/-- The transposed incidence against a plaquette vector read off
the plaquette data at a link, the four boundary reads folded over
the planes through the link's direction: at every higher direction
the plaquette at the link's tail forward and the plaquette stepped
back along that direction backward, and at every lower direction the
plaquette stepped back along that direction forward and the
plaquette at the tail backward, each at its corner's occupancy. -/
theorem colRead_planes (d L e s' : Nat) (he : e < d) (hs' : s' < (L + 1) ^ d)
    (hce : coordAt L e s' < L) (V : Nat × Nat × Nat → BPair) :
    (getAt BPair.unit (matVec (transposeM (incid d L)) ((plaqList d L).map V))
      (linkKey d L e s')).oneValue
      (bsum (fun k => if decide (e < k) then
          (if decide (coordAt L k s' < L) then V (e, k, s') else BPair.unit)
          + (if 0 < coordAt L k s' then (V (e, k, s' - (L + 1) ^ k)).swap else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun a => if decide (a < e) then
          (if 0 < coordAt L a s' then V (a, e, s' - (L + 1) ^ a) else BPair.unit)
          + (if decide (coordAt L a s' < L) then (V (a, e, s')).swap else BPair.unit)
        else BPair.unit) (List.range d)) := by
  refine BPair.oneValue_trans (colRead d L e s' he hs' hce V) ?_
  refine BPair.oneValue_trans (bsum_plaq_planes d L _) ?_
  -- each plane's site fold at the plane's column read
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun a => bsum (fun k => if a < k then
      (if a == e then
          (if decide (coordAt L k s' < L) then V (a, k, s') else BPair.unit)
          + (if 0 < coordAt L k s' then (V (a, k, s' - (L + 1) ^ k)).swap else BPair.unit)
        else BPair.unit)
      + (if k == e then
          (if 0 < coordAt L a s' then V (a, k, s' - (L + 1) ^ a) else BPair.unit)
          + (if decide (coordAt L a s' < L) then (V (a, k, s')).swap else BPair.unit)
        else BPair.unit) else BPair.unit) (List.range d)) d (fun a _ =>
    bsum_congr_range_ov _ _ d (fun k _ => ite_congr_prop _ (fun hak =>
      plane_col d L e s' a k hak hs' hce V)))) ?_
  -- the two guards split, the first picking the direction as the lower one and the
  -- second as the higher one
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun a =>
      bsum (fun k => if a < k then (if a == e then
          (if decide (coordAt L k s' < L) then V (a, k, s') else BPair.unit)
          + (if 0 < coordAt L k s' then (V (a, k, s' - (L + 1) ^ k)).swap else BPair.unit)
        else BPair.unit) else BPair.unit) (List.range d)
      + bsum (fun k => if a < k then (if k == e then
          (if 0 < coordAt L a s' then V (a, k, s' - (L + 1) ^ a) else BPair.unit)
          + (if decide (coordAt L a s' < L) then (V (a, k, s')).swap else BPair.unit)
        else BPair.unit) else BPair.unit) (List.range d)) d (fun a _ =>
    BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun k _ => ite_add_unit_prop _ _ _))
      (foldB_add _ _ _))) ?_
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr ?_ ?_
  · -- the lower direction picked at the link's direction
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun a => if a == e then
        bsum (fun k => if a < k then
          (if decide (coordAt L k s' < L) then V (a, k, s') else BPair.unit)
          + (if 0 < coordAt L k s' then (V (a, k, s' - (L + 1) ^ k)).swap else BPair.unit)
        else BPair.unit) (List.range d) else BPair.unit) d (fun a _ => ?_)) ?_
    · cases hae : (a == e) with
      | true =>
        rw [iteB_true]
        exact bsum_congr_range_ov _ _ d (fun k _ => ite_congr_prop _ (fun _ => by
          rw [iteB_true]
          exact BPair.oneValue_refl _))
      | false =>
        rw [iteB_false]
        refine foldB_nullRange _ d (fun k _ => ?_)
        refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => by
          rw [iteB_false]
          exact BPair.oneValue_refl _)) ?_
        exact BPair.oneValue_of_eq (ite_prop_unit _)
    refine BPair.oneValue_trans (bsum_range_at (fun a => a == e) _ e d he
      (fun a _ ha => beqEqOf ha)) ?_
    rw [eqBeqOf (rfl : e = e), iteB_true]
    refine bsum_congr_range_ov _ _ d (fun k _ => ?_)
    rw [ite_decide (e < k)]
    exact BPair.oneValue_refl _
  · -- the higher direction picked at the link's direction, the folds exchanged
    refine BPair.oneValue_trans (bsum_swap _ (List.range d) (List.range d)) ?_
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun k => if k == e then
        bsum (fun a => if a < k then
          (if 0 < coordAt L a s' then V (a, k, s' - (L + 1) ^ a) else BPair.unit)
          + (if decide (coordAt L a s' < L) then (V (a, k, s')).swap else BPair.unit)
        else BPair.unit) (List.range d) else BPair.unit) d (fun k _ => ?_)) ?_
    · cases hke : (k == e) with
      | true =>
        rw [iteB_true]
        exact bsum_congr_range_ov _ _ d (fun a _ => ite_congr_prop _ (fun _ => by
          rw [iteB_true]
          exact BPair.oneValue_refl _))
      | false =>
        rw [iteB_false]
        refine foldB_nullRange _ d (fun a _ => ?_)
        refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => by
          rw [iteB_false]
          exact BPair.oneValue_refl _)) ?_
        exact BPair.oneValue_of_eq (ite_prop_unit _)
    refine BPair.oneValue_trans (bsum_range_at (fun k => k == e) _ e d he
      (fun k _ hk => beqEqOf hk)) ?_
    rw [eqBeqOf (rfl : e = e), iteB_true]
    refine bsum_congr_range_ov _ _ d (fun a _ => ?_)
    rw [ite_decide (a < e)]
    exact BPair.oneValue_refl _

/-- A column's occupancy fold: one per occupied entry over the
rows, the plaquettes holding the link. -/
def colFold (K : Mat) (l : Nat) : BPair :=
  bsum (fun p => if (getAt BPair.unit (getAt [] K p) l).oneValue BPair.unit
    then BPair.unit else BPair.ofNat 1) (List.range K.length)

/-- The window's column read: a link sits on at most `2g`
plaquettes. -/
def colCountRead (d L : Nat) : Prop :=
  ((List.range (linkCount d L)).all (fun l =>
    decide (colFold (incid d L) l ≤ BPair.ofNat (2 * dirGap d)))) = true

instance instCornerwindow7 (d L : Nat) : Decidable (colCountRead d L) :=
  inferInstanceAs (Decidable (_ = _))

/-- The occupancy read of a link's column at a plaquette sits at or
below the four boundary indicators holding the link. -/
private theorem occFour (c1 c2 c3 c4 : Bool) :
    (if ((if c1 then BPair.ofNat 1 else BPair.unit)
        + ((if c2 then BPair.ofNat 1 else BPair.unit)
        + ((if c3 then (BPair.ofNat 1).swap else BPair.unit)
        + ((if c4 then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit)))).oneValue BPair.unit
      then BPair.unit else BPair.ofNat 1)
      ≤ (if c1 then BPair.ofNat 1 else BPair.unit) + ((if c2 then BPair.ofNat 1 else BPair.unit)
        + ((if c3 then BPair.ofNat 1 else BPair.unit) + (if c4 then BPair.ofNat 1 else BPair.unit))) := by
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> decide

/-- A plane's plaquettes holding a link: at most two, one at the
link's tail and one stepped back along the plane's other direction,
and the sum's unit at a plane off the link's direction. -/
private theorem planeCol (d L a k e s' : Nat) :
    bsum (fun q : Nat × Nat × Nat => (if q.1 == e && q.2.2 == s' then BPair.ofNat 1 else BPair.unit)
        + ((if q.2.1 == e && stepAt L q.1 q.2.2 == s' then BPair.ofNat 1 else BPair.unit)
        + ((if q.1 == e && stepAt L q.2.1 q.2.2 == s' then BPair.ofNat 1 else BPair.unit)
        + (if q.2.1 == e && q.2.2 == s' then BPair.ofNat 1 else BPair.unit))))
      (if a < k then (sites d L).filterMap (fun s =>
        if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none) else [])
      ≤ (if (a == e || k == e) && decide (a < k) then BPair.ofNat 2 else BPair.unit) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  by_cases hak : a < k
  · rw [if_pos hak, decide_eq_true hak, Bool.and_true]
    refine leB_congr_left (BPair.oneValue_symm (famFold_filterMap_ov bpairFoldLaws _ _ (sites d L)))
      ?_
    -- the two single-key reads at the plane through the link's direction
    have hone : ∀ (P : Nat → Bool) (Q : Nat → Bool),
        (∀ s t, s < (L + 1) ^ d → t < (L + 1) ^ d → Q s = true → Q t = true → s = t) →
        bsum (fun s => if P s && Q s then BPair.ofNat 1 else BPair.unit)
          (List.range ((L + 1) ^ d)) ≤ BPair.ofNat 1 := fun P Q hQ =>
      bsum_range_le_one (fun s => P s && Q s) _ (fun s t hs ht hs' ht' =>
        hQ s t hs ht (andSplitB hs').2 (andSplitB ht').2)
    have hkey : ∀ s t, s < (L + 1) ^ d → t < (L + 1) ^ d → (s == s') = true → (t == s') = true →
        s = t := fun s t _ _ hs ht => (beqEqOf hs).trans (beqEqOf ht).symm
    have hstep : ∀ c s t, s < (L + 1) ^ d → t < (L + 1) ^ d → (stepAt L c s == s') = true →
        (stepAt L c t == s') = true → s = t := fun c s t _ _ hs ht =>
      addCancelR ((L + 1) ^ c) ((beqEqOf hs).trans (beqEqOf ht).symm)
    by_cases hae : a = e
    · rw [hae, eqBeqOf rfl, Bool.true_or]
      have hke : ¬ k = e := fun h => Nat.ne_of_lt hak (hae.trans h.symm)
      rw [if_pos rfl]
      refine leB_trans (bsum_le _ (fun s =>
        (if (decide (coordAt L e s < L) && decide (coordAt L k s < L)) && (s == s')
          then BPair.ofNat 1 else BPair.unit)
        + (if (decide (coordAt L e s < L) && decide (coordAt L k s < L)) && (stepAt L k s == s')
          then BPair.ofNat 1 else BPair.unit)) _ (fun s _ => ?_)) ?_
      · cases hv : (decide (coordAt L e s < L) && decide (coordAt L k s < L)) with
        | true =>
          show (if e == e && s == s' then BPair.ofNat 1 else BPair.unit)
            + ((if k == e && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit)
            + ((if e == e && stepAt L k s == s' then BPair.ofNat 1 else BPair.unit)
            + (if k == e && s == s' then BPair.ofNat 1 else BPair.unit)))
            ≤ (if (s == s') = true then BPair.ofNat 1 else BPair.unit)
              + (if (stepAt L k s == s') = true then BPair.ofNat 1 else BPair.unit)
          rw [eqBeqOf (rfl : e = e), neBeqOf hke]
          cases (s == s') <;> cases (stepAt L k s == s') <;> cases (stepAt L e s == s') <;> decide
        | false =>
          show BPair.unit ≤ BPair.unit + BPair.unit
          exact leB_congr_right (BPair.oneValue_symm (BPair.add_unit _)) (leB_refl _)
      refine leB_congr_left (BPair.oneValue_symm (foldB_add _ _ _)) ?_
      refine leB_congr_right (BPair.oneValue_symm (BPair.ofNat_add 1 1)) ?_
      exact leB_add (hone _ _ hkey) (hone _ _ (hstep k))
    · by_cases hke : k = e
      · rw [hke, eqBeqOf rfl, Bool.or_true, if_pos rfl]
        refine leB_trans (bsum_le _ (fun s =>
          (if (decide (coordAt L a s < L) && decide (coordAt L e s < L)) && (stepAt L a s == s')
            then BPair.ofNat 1 else BPair.unit)
          + (if (decide (coordAt L a s < L) && decide (coordAt L e s < L)) && (s == s')
            then BPair.ofNat 1 else BPair.unit)) _ (fun s _ => ?_)) ?_
        · cases hv : (decide (coordAt L a s < L) && decide (coordAt L e s < L)) with
          | true =>
            show (if a == e && s == s' then BPair.ofNat 1 else BPair.unit)
              + ((if e == e && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit)
              + ((if a == e && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit)
              + (if e == e && s == s' then BPair.ofNat 1 else BPair.unit)))
              ≤ (if (stepAt L a s == s') = true then BPair.ofNat 1 else BPair.unit)
                + (if (s == s') = true then BPair.ofNat 1 else BPair.unit)
            rw [eqBeqOf (rfl : e = e), neBeqOf hae]
            cases (stepAt L a s == s') <;> cases (s == s') <;> cases (stepAt L e s == s') <;> decide
          | false =>
            show BPair.unit ≤ BPair.unit + BPair.unit
            exact leB_congr_right (BPair.oneValue_symm (BPair.add_unit _)) (leB_refl _)
        refine leB_congr_left (BPair.oneValue_symm (foldB_add _ _ _)) ?_
        refine leB_congr_right (BPair.oneValue_symm (BPair.ofNat_add 1 1)) ?_
        exact leB_add (hone _ _ (hstep a)) (hone _ _ hkey)
      · rw [neBeqOf hae, neBeqOf hke, Bool.or_false,
          if_neg (fun hc => Bool.noConfusion hc)]
        refine leB_congr_left (BPair.oneValue_symm (famFold_unit_ov bpairFoldLaws _
          (fun s => ?_) _)) (leB_refl _)
        cases hv : (decide (coordAt L a s < L) && decide (coordAt L k s < L)) with
        | true =>
          show ((if a == e && s == s' then BPair.ofNat 1 else BPair.unit)
            + ((if k == e && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit)
            + ((if a == e && stepAt L k s == s' then BPair.ofNat 1 else BPair.unit)
            + (if k == e && s == s' then BPair.ofNat 1 else BPair.unit)))).oneValue BPair.unit
          rw [neBeqOf hae, neBeqOf hke]
          cases (s == s') <;> cases (stepAt L a s == s') <;> cases (stepAt L k s == s') <;> decide
        | false => exact BPair.oneValue_refl _
  · rw [if_neg hak, decide_eq_false hak, Bool.and_false, if_neg (fun hc => Bool.noConfusion hc)]
    exact leB_refl _

/-- The window's column read at every window: a link sits on at
most `2g` plaquettes, two in each plane through its direction. -/
theorem colCountRead_all (d L : Nat) : colCountRead d L := by
  refine all_range_intro _ (fun l hl => decide_eq_true ?_)
  have hx := link_of_mem d L _ (mem_getAt (0, 0) (linkList d L) l hl)
  rw [← linkKey_of_getAt d L l hl]
  generalize getAt (0, 0) (linkList d L) l = x at hx ⊢
  obtain ⟨he, hs', hce⟩ := hx
  cases x with
  | mk e s' =>
  show bsum (fun p => if (getAt BPair.unit (getAt [] (incid d L) p) (linkKey d L e s')).oneValue
    BPair.unit then BPair.unit else BPair.ofNat 1) (List.range (incid d L).length)
    ≤ BPair.ofNat (2 * dirGap d)
  rw [incid_length]
  generalize hG : (fun q : Nat × Nat × Nat =>
    (if q.1 == e && q.2.2 == s' then BPair.ofNat 1 else BPair.unit)
      + ((if q.2.1 == e && stepAt L q.1 q.2.2 == s' then BPair.ofNat 1 else BPair.unit)
      + ((if q.1 == e && stepAt L q.2.1 q.2.2 == s' then BPair.ofNat 1 else BPair.unit)
      + (if q.2.1 == e && q.2.2 == s' then BPair.ofNat 1 else BPair.unit)))) = G
  refine leB_trans (bsum_le _ (fun p => G (getAt (0, 0, 0) (plaqList d L) p)) _
    (fun p hp => ?_)) ?_
  · rw [incid_entry_link d L p e s' (ltOfCountRange hp) he hs' hce, ← hG]
    exact occFour _ _ _ _
  refine leB_congr_left (BPair.oneValue_of_eq (bsum_plaq_places d L G).symm) ?_
  rw [← hG]
  show bsum _ ((List.range d).flatMap (fun a => (List.range d).flatMap (fun k =>
    if a < k then (sites d L).filterMap (fun s =>
      if coordAt L a s < L && coordAt L k s < L then some (a, k, s) else none) else [])))
    ≤ _
  refine leB_congr_left (BPair.oneValue_symm (famFold_flatMap_ov bpairFoldLaws _ _ (List.range d)))
    ?_
  refine leB_trans (bsum_le _ (fun a => bsum (fun k =>
    if (a == e || k == e) && decide (a < k) then BPair.ofNat 2 else BPair.unit) (List.range d))
    _ (fun a _ => ?_)) ?_
  · refine leB_congr_left (BPair.oneValue_symm (famFold_flatMap_ov bpairFoldLaws _ _
      (List.range d))) ?_
    exact bsum_le _ _ _ (fun k _ => planeCol d L a k e s')
  -- the count of the planes through the link's direction
  refine leB_congr_left (BPair.oneValue_symm (bsum_congr_range_ov _ (fun a => bsum (fun k =>
    (if a == e && decide (a < k) then BPair.ofNat 2 else BPair.unit)
    + (if k == e && decide (a < k) then BPair.ofNat 2 else BPair.unit)) (List.range d)) d
    (fun a _ => bsum_congr_range_ov _ _ d (fun k _ => ?_)))) ?_
  · cases hae : (a == e) <;> cases hke : (k == e) <;> cases hak : decide (a < k) <;>
      first
      | decide
      | exact absurd (of_decide_eq_true hak)
          (by rw [beqEqOf hae, beqEqOf hke]; exact Nat.lt_irrefl e)
  refine leB_congr_left (BPair.oneValue_symm (bsum_congr_range_ov _ _ d (fun a _ =>
    foldB_add _ _ (List.range d)))) ?_
  refine leB_congr_left (BPair.oneValue_symm (foldB_add _ _ (List.range d))) ?_
  -- the first fold picks the link's direction, the second folds the further directions
  refine leB_congr_left (BPair.oneValue_symm (BPair.add_congr
    (bsum_range_pick _ e d he (fun a _ hae => ?_))
    (BPair.oneValue_trans (bsum_swap (fun a k =>
      if k == e && decide (a < k) then BPair.ofNat 2 else BPair.unit) (List.range d) (List.range d))
      (bsum_range_pick _ e d he (fun k _ hke => ?_))))) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun k => ?_) _
    rw [neBeqOf hae, Bool.false_and]
    exact BPair.oneValue_refl _
  · refine famFold_unit_ov bpairFoldLaws _ (fun a => ?_) _
    rw [neBeqOf hke, Bool.false_and]
    exact BPair.oneValue_refl _
  rw [eqBeqOf (rfl : e = e)]
  refine leB_congr_left (foldB_add _ _ (List.range d)) ?_
  refine leB_congr_left (BPair.oneValue_symm (bsum_congr_range_ov _ (fun k =>
    (if e < k then BPair.ofNat 2 else BPair.unit) + (if k < e then BPair.ofNat 2 else BPair.unit))
    d (fun k _ => ?_))) ?_
  · by_cases h1 : e < k
    · by_cases h2 : k < e
      · exact absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl e)
      · rw [decide_eq_true h1, decide_eq_false h2, if_pos h1, if_neg h2]
        decide
    · by_cases h2 : k < e
      · rw [decide_eq_false h1, decide_eq_true h2, if_neg h1, if_pos h2]
        decide
      · rw [decide_eq_false h1, decide_eq_false h2, if_neg h1, if_neg h2]
        decide
  refine leB_congr_left (BPair.oneValue_symm (bsum_range_sides e (BPair.ofNat 2) d he)) ?_
  refine leB_congr_left (BPair.oneValue_symm (foldB_const (BPair.ofNat 2) (List.range (d - 1))))
    ?_
  rw [ground.length_range]
  show BPair.ofNat (d - 1) * BPair.ofNat 2 ≤ BPair.ofNat (2 * (d - 1))
  refine leB_congr_left (BPair.oneValue_symm ?_) (leB_refl _)
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
  exact BPair.oneValue_symm (BPair.ofNat_mul 2 (d - 1))

/-- The incidence cap (`con:cornerwindow`'s roots' bracket, the upper
side): at an incidence whose rows' squares fold to at most four and
whose columns' occupancy folds sit at or below `m`, the Gram's form
at a vector sits at or below `4m` times the vector's self-pairing —
per link the squared Cauchy--Schwarz at the count, the products'
squares collected per row at the row's squares fold. -/
theorem incidCap (n m : Nat) (K : Mat) (hK : rowsLen n K)
    (hrow : ∀ p, p < K.length →
      dotP (getAt [] K p) (getAt [] K p) ≤ BPair.ofNat 4)
    (hcol : ∀ l, l < n → colFold K l ≤ BPair.ofNat m)
    (W : List BPair) (hW : W.length = K.length) :
    quadForm (matMul K (transposeM K)) W ≤ BPair.ofNat (4 * m) * dotN W W := by
  cases K with
  | nil =>
    cases W with
    | nil =>
      show BPair.unit ≤ BPair.ofNat (4 * m) * BPair.unit
      exact unitLeMul (unitLeOfNat _) (leB_refl _)
    | cons a l => exact Nat.noConfusion (show Nat.succ l.length = 0 from hW)
  | cons k0 kt =>
  generalize hKe : k0 :: kt = K at hK hrow hcol hW ⊢
  have h0 : 0 < K.length := by rw [← hKe]; exact Nat.succ_pos _
  have hKt : rowsLen K.length (transposeM K) := rowsLen_transposeM K
  have hKtl : (transposeM K).length = n := length_transposeM K hK h0
  have hy : (matVec (transposeM K) W).length = n := by
    rw [matVec_length, hKtl]
  -- the entries: the column's key reads
  let kk : Nat → Nat → BPair := fun p l => getAt BPair.unit (getAt [] K p) l
  let ww : Nat → BPair := fun p => getAt BPair.unit W p
  -- the form is the moved vector's self-pairing
  have h1 := quadForm_matMulT n K hK W hW
  -- the moved vector's entries: the columns' folds
  have hyl : ∀ l, l < n → (getAt BPair.unit (matVec (transposeM K) W) l).oneValue
      (bsum (fun p => kk p l * ww p) (List.range K.length)) :=
    fun l hl => getAt_matVec_transposeM K hK h0 W hW l hl
  -- the self-pairing as the columns' squared folds
  have h2 : (dotN (matVec (transposeM K) W) (matVec (transposeM K) W)).oneValue
      (bsum (fun l => bsum (fun p => kk p l * ww p) (List.range K.length)
        * bsum (fun p => kk p l * ww p) (List.range K.length)) (List.range n)) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    rw [dotP_fold n _ _ hy hy]
    exact bsum_congr_range_ov _ _ n (fun l hl => BPair.mul_congr (hyl l hl) (hyl l hl))
  -- per link the squared Cauchy--Schwarz at the count
  have h3 : bsum (fun l => bsum (fun p => kk p l * ww p) (List.range K.length)
        * bsum (fun p => kk p l * ww p) (List.range K.length)) (List.range n)
      ≤ bsum (fun l => BPair.ofNat m
        * bsum (fun p => (kk p l * ww p) * (kk p l * ww p)) (List.range K.length))
        (List.range n) := by
    refine bsum_le _ _ (List.range n) (fun l hl => ?_)
    have hln : l < n := ltOfCountRange hl
    refine leB_trans (coeff.bsum_sq_le_count K.length (fun p => kk p l) ww) ?_
    refine leB_mul_mono (foldB_nonneg _ _ (fun i _ => unitLeOfSide (sq_side _)))
      (unitLeOfNat m) ?_ (leB_refl _)
    exact hcol l hln
  -- the products' squares collected per row
  have h4 : (bsum (fun l => BPair.ofNat m
        * bsum (fun p => (kk p l * ww p) * (kk p l * ww p)) (List.range K.length))
        (List.range n)).oneValue
      (BPair.ofNat m * bsum (fun p => ww p * ww p
        * bsum (fun l => kk p l * kk p l) (List.range n)) (List.range K.length)) := by
    refine BPair.oneValue_trans (foldB_mul_left (BPair.ofNat m) _ (List.range n)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    refine BPair.oneValue_trans
      (bsum_swap (fun l p => (kk p l * ww p) * (kk p l * ww p)) (List.range n)
        (List.range K.length)) ?_
    refine bsum_congr_range_ov _ _ K.length (fun p _ => ?_)
    refine BPair.oneValue_trans (bsum_congr_range_ov _
      (fun l => ww p * ww p * (kk p l * kk p l)) n (fun l _ =>
        BPair.oneValue_of_eq (by
          rw [BPair.mul_mul_mul_comm (kk p l) (ww p) (kk p l) (ww p),
            BPair.mul_comm (kk p l * kk p l) (ww p * ww p)]))) ?_
    exact foldB_mul_left (ww p * ww p) _ (List.range n)
  -- each row's squares fold at or below four
  have h5 : bsum (fun p => ww p * ww p * bsum (fun l => kk p l * kk p l) (List.range n))
        (List.range K.length)
      ≤ bsum (fun p => ww p * ww p * BPair.ofNat 4) (List.range K.length) := by
    refine bsum_le _ _ (List.range K.length) (fun p hp => ?_)
    have hpP : p < K.length := ltOfCountRange hp
    refine leB_mulR (unitLeOfSide (sq_side (ww p))) ?_
    have hr : (getAt [] K p).length = n := rowsLen_getAt K p hK hpP
    have := hrow p hpP
    rw [dotP_fold n _ _ hr hr] at this
    exact this
  have h6 : (bsum (fun p => ww p * ww p * BPair.ofNat 4) (List.range K.length)).oneValue
      (BPair.ofNat 4 * dotN W W) := by
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun p => BPair.ofNat 4 * (ww p * ww p))
      K.length (fun p _ => BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
    refine BPair.oneValue_trans (foldB_mul_left (BPair.ofNat 4) _ (List.range K.length)) ?_
    refine BPair.mul_congr (BPair.oneValue_refl _) ?_
    show (bsum (fun p => ww p * ww p) (List.range K.length)).oneValue (dotN W W)
    refine BPair.oneValue_symm (BPair.oneValue_trans (dotN_read W W) ?_)
    rw [dotP_fold K.length W W hW hW]
    exact BPair.oneValue_refl _
  have hfin : quadForm (matMul K (transposeM K)) W
      ≤ BPair.ofNat m * (BPair.ofNat 4 * dotN W W) := by
    refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans h1 h2)) ?_
    refine leB_trans h3 ?_
    refine leB_congr_left (BPair.oneValue_symm h4) ?_
    refine leB_mulR (unitLeOfNat m) ?_
    exact leB_congr_right h6 h5
  refine leB_congr_right ?_ hfin
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_assoc _ _ _).symm) ?_
  refine BPair.mul_congr_left ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _)) ?_
  exact BPair.oneValue_symm (BPair.ofNat_mul 4 m)

/-- The window's roots' bracket, the upper side: the Gram's form
sits at or below `8g` times the self-pairing at every plaquette
vector, `Δ ⪯ 8g`, at the window's row and column reads. -/
theorem gramCap (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L) :
    quadForm (gram d L) W ≤ BPair.ofNat (8 * dirGap d) * dotN W W := by
  have hlen := incid_length d L
  have hK := incid_rows d L
  have h := incidCap (linkCount d L) (2 * dirGap d) (incid d L) hK
    (fun p hp => leB_congr_right
      (of_decide_eq_true (all_range_read _ (rowSqRead_all d L) p (by rw [← hlen]; exact hp)))
      (leB_refl _))
    (fun l hl => of_decide_eq_true (all_range_read _ (colCountRead_all d L) l hl))
    W (by rw [hW, hlen])
  refine leB_congr_right ?_ h
  refine BPair.mul_congr_left (BPair.oneValue_of_eq ?_)
  rw [← ground.mulAssoc 4 2 (dirGap d)]

/-! The roots' bracket, the lower side: the Hodge fold.  The Gram
joined to the cubes' boundaries' Gram reads the differences' Grams
entry by entry, the Gram's form joined to `Nᵀ W`'s self-pairing is
the Hodge fold, the Dirichlet folds telescope line by line, and the
Poincaré read holds at every range member. -/

/-! The entries: the incidence's four reads of a plaquette at a link,
the cubes' boundaries' six reads of a cube at a plaquette, and the
Gram's and the cubes' Gram's entries at two plaquettes. -/

/-- The four boundary reads of a plaquette at a direction and a site:
the base link and the corner's higher link forward, the two further
links backward (`incid_entry_link`'s value). -/
private def linkInd (L : Nat) (q : Nat × Nat × Nat) (e t : Nat) : BPair :=
  (if q.1 == e && q.2.2 == t then BPair.ofNat 1 else BPair.unit)
    + ((if q.2.1 == e && stepAt L q.1 q.2.2 == t then BPair.ofNat 1 else BPair.unit)
    + ((if q.1 == e && stepAt L q.2.1 q.2.2 == t then (BPair.ofNat 1).swap else BPair.unit)
    + ((if q.2.1 == e && q.2.2 == t then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit)))

/-- The six face reads of a cube at a plaquette's data, the faces at
`cubeFaces`' signs. -/
private def faceInd (L : Nat) (c : Nat × Nat × Nat × Nat) (a k s : Nat) : BPair :=
  (if c.1 == a && c.2.1 == k && c.2.2.2 == s then BPair.ofNat 1 else BPair.unit)
  + ((if c.1 == a && c.2.1 == k && stepAt L c.2.2.1 c.2.2.2 == s then (BPair.ofNat 1).swap
      else BPair.unit)
  + ((if c.1 == a && c.2.2.1 == k && c.2.2.2 == s then (BPair.ofNat 1).swap else BPair.unit)
  + ((if c.1 == a && c.2.2.1 == k && stepAt L c.2.1 c.2.2.2 == s then BPair.ofNat 1 else BPair.unit)
  + ((if c.2.1 == a && c.2.2.1 == k && c.2.2.2 == s then BPair.ofNat 1 else BPair.unit)
  + ((if c.2.1 == a && c.2.2.1 == k && stepAt L c.1 c.2.2.2 == s then (BPair.ofNat 1).swap
      else BPair.unit)
  + BPair.unit)))))

/-- The faces' sign at a valid cube and a valid plaquette's key reads
the six face reads at the data. -/
private theorem faceSign_read (d L x y z c a k s : Nat) (hxy : x < y) (hyz : y < z) (hz : z < d)
    (hc : c < (L + 1) ^ d) (hcx : coordAt L x c < L) (hcy : coordAt L y c < L)
    (hcz : coordAt L z c < L) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) :
    faceSign (cubeFaces d L (x, y, z, c)) (plaqKey d L a k s) = faceInd L (x, y, z, c) a k s := by
  have hyd : y < d := Nat.lt_trans hyz hz
  have hxd : x < d := Nat.lt_trans hxy hyd
  have hxz : x < z := Nat.lt_trans hxy hyz
  have nxy : ¬ x = y := Nat.ne_of_lt hxy
  have nxz : ¬ x = z := Nat.ne_of_lt hxz
  have nyz : ¬ y = z := Nat.ne_of_lt hyz
  have sZ := stepAt_lt d L z c hz hc hcz
  have sY := stepAt_lt d L y c hyd hc hcy
  have sX := stepAt_lt d L x c hxd hc hcx
  have cxZ : coordAt L x (stepAt L z c) < L := by
    rw [coordAt_step_ne L z x c hcz nxz]
    exact hcx
  have cyZ : coordAt L y (stepAt L z c) < L := by
    rw [coordAt_step_ne L z y c hcz nyz]
    exact hcy
  have cxY : coordAt L x (stepAt L y c) < L := by
    rw [coordAt_step_ne L y x c hcy nxy]
    exact hcx
  have czY : coordAt L z (stepAt L y c) < L := by
    rw [coordAt_step_ne L y z c hcy (fun h => nyz h.symm)]
    exact hcz
  have cyX : coordAt L y (stepAt L x c) < L := by
    rw [coordAt_step_ne L x y c hcx (fun h => nxy h.symm)]
    exact hcy
  have czX : coordAt L z (stepAt L x c) < L := by
    rw [coordAt_step_ne L x z c hcx (fun h => nxz h.symm)]
    exact hcz
  show (if plaqKey d L x y c == plaqKey d L a k s then BPair.ofNat 1 else BPair.unit)
    + ((if plaqKey d L x y (stepAt L z c) == plaqKey d L a k s then (BPair.ofNat 1).swap
        else BPair.unit)
    + ((if plaqKey d L x z c == plaqKey d L a k s then (BPair.ofNat 1).swap else BPair.unit)
    + ((if plaqKey d L x z (stepAt L y c) == plaqKey d L a k s then BPair.ofNat 1 else BPair.unit)
    + ((if plaqKey d L y z c == plaqKey d L a k s then BPair.ofNat 1 else BPair.unit)
    + ((if plaqKey d L y z (stepAt L x c) == plaqKey d L a k s then (BPair.ofNat 1).swap
        else BPair.unit)
    + BPair.unit))))) = _
  rw [plaqKey_beq d L x y c a k s hxy hyd hc hcx hcy hak hk hs hca hck,
    plaqKey_beq d L x y (stepAt L z c) a k s hxy hyd sZ cxZ cyZ hak hk hs hca hck,
    plaqKey_beq d L x z c a k s hxz hz hc hcx hcz hak hk hs hca hck,
    plaqKey_beq d L x z (stepAt L y c) a k s hxz hz sY cxY czY hak hk hs hca hck,
    plaqKey_beq d L y z c a k s hyz hz hc hcy hcz hak hk hs hca hck,
    plaqKey_beq d L y z (stepAt L x c) a k s hyz hz sX cyX czX hak hk hs hca hck]
  rfl

/-- The Gram's entry at two plaquettes: the first's boundary word's
signs against the incidence's four reads of the second at the first's
four links. -/
private theorem gram_entry (d L p q : Nat) (hp : p < plaqCount d L) (hq : q < plaqCount d L) :
    (getAt BPair.unit (getAt [] (gram d L) p) q).oneValue
      (linkInd L (getAt (0, 0, 0) (plaqList d L) q) (getAt (0, 0, 0) (plaqList d L) p).1
          (getAt (0, 0, 0) (plaqList d L) p).2.2 * BPair.ofNat 1
      + (linkInd L (getAt (0, 0, 0) (plaqList d L) q) (getAt (0, 0, 0) (plaqList d L) p).2.1
          (stepAt L (getAt (0, 0, 0) (plaqList d L) p).1 (getAt (0, 0, 0) (plaqList d L) p).2.2)
          * BPair.ofNat 1
      + (linkInd L (getAt (0, 0, 0) (plaqList d L) q) (getAt (0, 0, 0) (plaqList d L) p).1
          (stepAt L (getAt (0, 0, 0) (plaqList d L) p).2.1 (getAt (0, 0, 0) (plaqList d L) p).2.2)
          * (BPair.ofNat 1).swap
      + (linkInd L (getAt (0, 0, 0) (plaqList d L) q) (getAt (0, 0, 0) (plaqList d L) p).2.1
          (getAt (0, 0, 0) (plaqList d L) p).2.2 * (BPair.ofNat 1).swap + BPair.unit)))) := by
  have hlen := incid_length d L
  have hK := incid_rows d L
  have hpK : p < (incid d L).length := by rw [hlen]; exact hp
  have hqK : q < (incid d L).length := by rw [hlen]; exact hq
  have hpos : 0 < (incid d L).length := Nat.lt_of_le_of_lt (Nat.zero_le p) hpK
  have hpl := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
  generalize hP : getAt (0, 0, 0) (plaqList d L) p = P at hpl ⊢
  obtain ⟨hak, hkd, hsd, hca, hck⟩ := hpl
  cases P with
  | mk a q' =>
  cases q' with
  | mk k s =>
  have had : a < d := Nat.lt_trans hak hkd
  have hne : ¬ k = a := fun h => Nat.ne_of_lt hak h.symm
  have hne' : ¬ a = k := Nat.ne_of_lt hak
  have v1 := linkKey_lt d L a s had hsd hca
  have sA := stepAt_lt d L a s had hsd hca
  have sK := stepAt_lt d L k s hkd hsd hck
  have ckA : coordAt L k (stepAt L a s) < L := by
    rw [coordAt_step_ne L a k s hca hne]
    exact hck
  have caK : coordAt L a (stepAt L k s) < L := by
    rw [coordAt_step_ne L k a s hck hne']
    exact hca
  have v2 := linkKey_lt d L k (stepAt L a s) hkd sA ckA
  have v3 := linkKey_lt d L a (stepAt L k s) had sK caK
  have v4 := linkKey_lt d L k s hkd hsd hck
  have hlink : 0 < linkCount d L := Nat.lt_of_le_of_lt (Nat.zero_le _) v1
  show (getAt BPair.unit (getAt [] (matMul (incid d L) (transposeM (incid d L))) p) q).oneValue _
  rw [getAt_matMul _ _ p hpK, transposeM_transposeM (incid d L) hK hlink hpos,
    getAt_map [] BPair.unit _ _ q hqK]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_fold (linkCount d L) _ _ (rowsLen_getAt _ p hK hpK) (rowsLen_getAt _ q hK hqK)]
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun l =>
    getAt BPair.unit (getAt [] (incid d L) q) l
      * keyFoldB (fun a b => a == b) l ((plaqWord d L (a, k, s)).map
          (fun e => (e.1, if e.2 then BPair.ofNat 1 else (BPair.ofNat 1).swap))))
    (linkCount d L) (fun l hl => by
      rw [incid_entry_at d L p l hp hl, hP]
      exact BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
  refine BPair.oneValue_trans (bsum_keyFold_linear (linkCount d L) _ _ ?_) ?_
  · intro f hf
    cases hf with
    | head => exact v1
    | tail _ hf =>
      cases hf with
      | head => exact v2
      | tail _ hf =>
        cases hf with
        | head => exact v3
        | tail _ hf =>
          cases hf with
          | head => exact v4
          | tail _ hf => nomatch hf
  show (getAt BPair.unit (getAt [] (incid d L) q) (linkKey d L a s) * BPair.ofNat 1
    + (getAt BPair.unit (getAt [] (incid d L) q) (linkKey d L k (stepAt L a s)) * BPair.ofNat 1
    + (getAt BPair.unit (getAt [] (incid d L) q) (linkKey d L a (stepAt L k s)) * (BPair.ofNat 1).swap
    + (getAt BPair.unit (getAt [] (incid d L) q) (linkKey d L k s) * (BPair.ofNat 1).swap
    + BPair.unit)))).oneValue _
  rw [incid_entry_link d L q a s hq had hsd hca,
    incid_entry_link d L q k (stepAt L a s) hq hkd sA ckA,
    incid_entry_link d L q a (stepAt L k s) hq had sK caK,
    incid_entry_link d L q k s hq hkd hsd hck]
  exact BPair.oneValue_refl _

/-- The cubes' boundaries' Gram's entry at two plaquettes: the fold
over the cubes of the two faces' signs' product. -/
theorem cubeGram_entry (d L p q : Nat) (hp : p < plaqCount d L) (hq : q < plaqCount d L) :
    (getAt BPair.unit (getAt [] (cubeGram d L) p) q).oneValue
      (bsum (fun C => faceSign (cubeFaces d L C) p * faceSign (cubeFaces d L C) q)
        (cubeList d L)) := by
  have hNlen := cubeBd_length d L
  have hN := cubeBd_rows d L
  have hpN : p < (cubeBd d L).length := by rw [hNlen]; exact hp
  have hqN : q < (cubeBd d L).length := by rw [hNlen]; exact hq
  show (getAt BPair.unit (getAt [] (gramM (cubeBd d L)) p) q).oneValue _
  rw [gramM_entry _ p q hpN hqN,
    dotP_fold (cubeCount d L) _ _ (rowsLen_getAt _ p hN hpN) (rowsLen_getAt _ q hN hqN),
    ← bsum_cube_places d L (fun C => faceSign (cubeFaces d L C) p * faceSign (cubeFaces d L C) q)]
  refine bsum_congr_range_ov _ _ _ (fun c hc => ?_)
  rw [cubeBd_entry d L p c hp hc, cubeBd_entry d L q c hq hc]
  exact BPair.oneValue_refl _

/-! The cubes holding a plaquette: the faces' sign of every cube at
the plaquette against a read of the cube folds to the reads at the
cubes holding it, two per further direction, the cube at the
plaquette's corner and the cube at the corner stepped back along the
direction, at the faces' signs. -/

/-- The triple fold over the cubes' data at a summand. -/
private def tripleSum (d L : Nat) (T : Nat → Nat → Nat → Nat → BPair) : BPair :=
  bsum (fun x => bsum (fun y => bsum (fun z => if decide (x < y) && decide (y < z) then
    bsum (fun c => if decide (coordAt L x c < L) && decide (coordAt L y c < L)
        && decide (coordAt L z c < L) then T x y z c else BPair.unit) (List.range ((L + 1) ^ d))
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)

/-- The triple fold's congruence at valid cubes. -/
private theorem tripleSum_congr (d L : Nat) (T T' : Nat → Nat → Nat → Nat → BPair)
    (h : ∀ x y z c, x < y → y < z → z < d → c < (L + 1) ^ d → coordAt L x c < L →
      coordAt L y c < L → coordAt L z c < L → (T x y z c).oneValue (T' x y z c)) :
    (tripleSum d L T).oneValue (tripleSum d L T') := by
  refine bsum_congr_range_ov _ _ d (fun x _ => bsum_congr_range_ov _ _ d (fun y _ =>
    bsum_congr_range_ov _ _ d (fun z hz => ?_)))
  refine ite_congr_prop _ (fun hg => ?_)
  refine bsum_congr_range_ov _ _ _ (fun c hc => ite_congr_prop _ (fun hH => ?_))
  have hg' := andSplitB hg
  have hH' := andSplitB hH
  have hH'' := andSplitB hH'.1
  exact h x y z c (of_decide_eq_true hg'.1) (of_decide_eq_true hg'.2) hz hc
    (of_decide_eq_true hH''.1) (of_decide_eq_true hH''.2) (of_decide_eq_true hH'.2)

/-- The triple fold splits over a summands' sum. -/
private theorem tripleSum_add (d L : Nat) (T T' : Nat → Nat → Nat → Nat → BPair) :
    (tripleSum d L (fun x y z c => T x y z c + T' x y z c)).oneValue
      (tripleSum d L T + tripleSum d L T') := by
  refine bsum_split _ _ _ d (fun x _ => bsum_split _ _ _ d (fun y _ =>
    bsum_split _ _ _ d (fun z _ => ?_)))
  refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (ite_add_unit _ _ _)
  refine BPair.oneValue_trans (bsum_congr_range_ov _ _ _ (fun c _ => ite_add_unit _ _ _))
    (foldB_add _ _ _)

/-- The triple fold at the unit summand reads the unit. -/
private theorem tripleSum_unit (d L : Nat) :
    (tripleSum d L (fun _ _ _ _ => BPair.unit)).oneValue BPair.unit := by
  refine famFold_unit_ov bpairFoldLaws _ (fun x => famFold_unit_ov bpairFoldLaws _ (fun y =>
    famFold_unit_ov bpairFoldLaws _ (fun z => ?_) _) _) _
  cases (decide (x < y) && decide (y < z)) with
  | false => exact BPair.oneValue_refl _
  | true =>
    refine famFold_unit_ov bpairFoldLaws _ (fun c => ?_) _
    cases (decide (coordAt L x c < L) && decide (coordAt L y c < L) && decide (coordAt L z c < L)) with
    | false => exact BPair.oneValue_refl _
    | true => exact BPair.oneValue_refl _

/-- A double fold of guarded units over the directions at a refused
first direction reads the unit. -/
private theorem doubleUnit (d : Nat) (P : Nat → Nat → Bool) (F : Nat → Nat → BPair)
    (h : ∀ y z, (F y z).oneValue BPair.unit) :
    (bsum (fun y => bsum (fun z => if P y z then F y z else BPair.unit) (List.range d))
      (List.range d)).oneValue BPair.unit := by
  refine famFold_unit_ov bpairFoldLaws _ (fun y => famFold_unit_ov bpairFoldLaws _ (fun z => ?_) _) _
  cases P y z with
  | false => exact BPair.oneValue_refl _
  | true => exact h y z

/-- The first face's fold: the cubes at the corner holding the
plaquette as their lower-plane face, one per further direction beyond
the plane. -/
private theorem faceFold1 (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (G : Nat × Nat × Nat × Nat → BPair) :
    (tripleSum d L (fun x y z c => if x == a && y == k && c == s then G (x, y, z, c)
        else BPair.unit)).oneValue
      (bsum (fun z => if decide (k < z) then
        (if decide (coordAt L z s < L) then G (a, k, z, s) else BPair.unit) else BPair.unit)
        (List.range d)) := by
  have had : a < d := Nat.lt_trans hak hk
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    if decide (x < y) && decide (y < z) then
      (if (decide (coordAt L x s < L) && decide (coordAt L y s < L) && decide (coordAt L z s < L))
          && (x == a && y == k) then G (x, y, z, s) else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) d (fun x _ => bsum_congr_range_ov _ _ d
      (fun y _ => bsum_congr_range_ov _ _ d (fun z _ => ite_congr_prop _ (fun _ => ?_))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun c =>
      if (decide (coordAt L x c < L) && decide (coordAt L y c < L) && decide (coordAt L z c < L))
        && (x == a && y == k) && c == s then G (x, y, z, c) else BPair.unit) _ (fun c _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_beq d L _ _ s hs
  -- the direction folds pick the plane
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine doubleUnit d _ _ (fun y z => ?_)
    rw [neBeqOf hxa, Bool.false_and, Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ k d hk (fun y _ hyk => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun z => ?_) _
    cases (decide (a < y) && decide (y < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hyk, Bool.and_false, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun z _ => ?_)
  rw [decide_eq_true hak, Bool.true_and, decide_eq_true hca, decide_eq_true hck, Bool.true_and,
    Bool.true_and, eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), Bool.and_true, Bool.and_true]
  exact BPair.oneValue_refl _

/-- The six face reads against a member split into the six guarded
reads of the member at the faces' signs. -/
private theorem faceInd_mul (L x y z c a k s : Nat) (g : BPair) :
    (faceInd L (x, y, z, c) a k s * g).oneValue
      ((if x == a && y == k && c == s then g else BPair.unit)
      + ((if x == a && y == k && stepAt L z c == s then g.swap else BPair.unit)
      + ((if x == a && z == k && c == s then g.swap else BPair.unit)
      + ((if x == a && z == k && stepAt L y c == s then g else BPair.unit)
      + ((if y == a && z == k && c == s then g else BPair.unit)
      + ((if y == a && z == k && stepAt L x c == s then g.swap else BPair.unit)
      + BPair.unit)))))) := by
  delta faceInd
  rw [BPair.right_distrib, BPair.right_distrib, BPair.right_distrib, BPair.right_distrib,
    BPair.right_distrib, BPair.right_distrib]
  exact BPair.add_congr (iteMul _ _).1 (BPair.add_congr (iteMul _ _).2
    (BPair.add_congr (iteMul _ _).2 (BPair.add_congr (iteMul _ _).1
    (BPair.add_congr (iteMul _ _).1 (BPair.add_congr (iteMul _ _).2 (BPair.unit_mul g))))))

/-- The second face's fold: the cubes at the corner stepped back along
a further direction beyond the plane, holding the plaquette as their
upper lower-plane face. -/
private theorem faceFold2 (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (G : Nat × Nat × Nat × Nat → BPair) :
    (tripleSum d L (fun x y z c => if x == a && y == k && stepAt L z c == s then (G (x, y, z, c)).swap
        else BPair.unit)).oneValue
      (bsum (fun z => if decide (k < z) then
        (if 0 < coordAt L z s then (G (a, k, z, s - (L + 1) ^ z)).swap else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have had : a < d := Nat.lt_trans hak hk
  have hL : 0 < L + 1 := Nat.succ_pos L
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    if decide (x < y) && decide (y < z) then
      (if 0 < coordAt L z s then
        (if (decide (coordAt L x (s - (L + 1) ^ z) < L) && decide (coordAt L y (s - (L + 1) ^ z) < L)
            && decide (coordAt L z (s - (L + 1) ^ z) < L)) && (x == a && y == k)
          then (G (x, y, z, s - (L + 1) ^ z)).swap else BPair.unit)
        else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) d (fun x _ => bsum_congr_range_ov _ _ d
      (fun y _ => bsum_congr_range_ov _ _ d (fun z _ => ite_congr_prop _ (fun _ => ?_))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun c =>
      if (decide (coordAt L x c < L) && decide (coordAt L y c < L) && decide (coordAt L z c < L))
        && (x == a && y == k) && stepAt L z c == s then (G (x, y, z, c)).swap else BPair.unit) _
      (fun c _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_step d L z _ (fun c hc => of_decide_eq_true (andSplitB (andSplitB hc).1).2) _ s hs
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine doubleUnit d _ _ (fun y z => ?_)
    rw [neBeqOf hxa, Bool.false_and, Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ k d hk (fun y _ hyk => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun z => ?_) _
    cases (decide (a < y) && decide (y < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hyk, Bool.and_false, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun z _ => ?_)
  rw [decide_eq_true hak, Bool.true_and, eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), Bool.and_true]
  refine ite_congr_prop _ (fun hkz => ?_)
  refine ite_congr_prop _ (fun hpos => ?_)
  have hkz' : k < z := of_decide_eq_true hkz
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) z s hL hpos
  have hza : coordAt L a (s - (L + 1) ^ z) = coordAt L a s :=
    hoff a (Nat.ne_of_lt (Nat.lt_trans hak hkz'))
  have hzk : coordAt L k (s - (L + 1) ^ z) = coordAt L k s := hoff k (Nat.ne_of_lt hkz')
  have hzz : coordAt L z (s - (L + 1) ^ z) < L := by
    have h := baseDigit_lt (L + 1) z s hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  rw [hza, hzk, decide_eq_true hca, decide_eq_true hck, decide_eq_true hzz, iteB_of_true]
  · exact BPair.oneValue_refl _
  · rfl

/-- The third face's fold: the cubes at the corner holding the
plaquette as their outer-plane face, one per direction between the
plane's. -/
private theorem faceFold3 (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (G : Nat × Nat × Nat × Nat → BPair) :
    (tripleSum d L (fun x y z c => if x == a && z == k && c == s then (G (x, y, z, c)).swap
        else BPair.unit)).oneValue
      (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if decide (coordAt L y s < L) then (G (a, y, k, s)).swap else BPair.unit) else BPair.unit)
        (List.range d)) := by
  have had : a < d := Nat.lt_trans hak hk
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    if decide (x < y) && decide (y < z) then
      (if (decide (coordAt L x s < L) && decide (coordAt L y s < L) && decide (coordAt L z s < L))
          && (x == a && z == k) then (G (x, y, z, s)).swap else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) d (fun x _ => bsum_congr_range_ov _ _ d
      (fun y _ => bsum_congr_range_ov _ _ d (fun z _ => ite_congr_prop _ (fun _ => ?_))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun c =>
      if (decide (coordAt L x c < L) && decide (coordAt L y c < L) && decide (coordAt L z c < L))
        && (x == a && z == k) && c == s then (G (x, y, z, c)).swap else BPair.unit) _ (fun c _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_beq d L _ _ s hs
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine doubleUnit d _ _ (fun y z => ?_)
    rw [neBeqOf hxa, Bool.false_and, Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun y _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ k d hk (fun z _ hzk => ?_)) ?_
  · cases (decide (a < y) && decide (y < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzk, Bool.and_false, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), Bool.and_true, decide_eq_true hca,
    decide_eq_true hck, Bool.true_and, Bool.and_true, Bool.and_true]
  exact BPair.oneValue_refl _

/-- The fourth face's fold: the cubes at the corner stepped back along
a direction between the plane's, holding the plaquette as their upper
outer-plane face. -/
private theorem faceFold4 (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (G : Nat × Nat × Nat × Nat → BPair) :
    (tripleSum d L (fun x y z c => if x == a && z == k && stepAt L y c == s then G (x, y, z, c)
        else BPair.unit)).oneValue
      (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if 0 < coordAt L y s then G (a, y, k, s - (L + 1) ^ y) else BPair.unit) else BPair.unit)
        (List.range d)) := by
  have had : a < d := Nat.lt_trans hak hk
  have hL : 0 < L + 1 := Nat.succ_pos L
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    if decide (x < y) && decide (y < z) then
      (if 0 < coordAt L y s then
        (if (decide (coordAt L x (s - (L + 1) ^ y) < L) && decide (coordAt L y (s - (L + 1) ^ y) < L)
            && decide (coordAt L z (s - (L + 1) ^ y) < L)) && (x == a && z == k)
          then G (x, y, z, s - (L + 1) ^ y) else BPair.unit)
        else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) d (fun x _ => bsum_congr_range_ov _ _ d
      (fun y _ => bsum_congr_range_ov _ _ d (fun z _ => ite_congr_prop _ (fun _ => ?_))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun c =>
      if (decide (coordAt L x c < L) && decide (coordAt L y c < L) && decide (coordAt L z c < L))
        && (x == a && z == k) && stepAt L y c == s then G (x, y, z, c) else BPair.unit) _
      (fun c _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_step d L y _ (fun c hc => of_decide_eq_true (andSplitB (andSplitB (andSplitB hc).1).1).2)
      _ s hs
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine doubleUnit d _ _ (fun y z => ?_)
    rw [neBeqOf hxa, Bool.false_and, Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun y _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ k d hk (fun z _ hzk => ?_)) ?_
  · cases (decide (a < y) && decide (y < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzk, Bool.and_false, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), Bool.and_true]
  refine ite_congr_prop _ (fun hg => ?_)
  refine ite_congr_prop _ (fun hpos => ?_)
  have hay : a < y := of_decide_eq_true (andSplitB hg).1
  have hyk : y < k := of_decide_eq_true (andSplitB hg).2
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) y s hL hpos
  have hya : coordAt L a (s - (L + 1) ^ y) = coordAt L a s := hoff a (Nat.ne_of_lt hay)
  have hyk' : coordAt L k (s - (L + 1) ^ y) = coordAt L k s :=
    hoff k (fun h => Nat.ne_of_lt hyk h.symm)
  have hyy : coordAt L y (s - (L + 1) ^ y) < L := by
    have h := baseDigit_lt (L + 1) y s hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  rw [hya, hyk', decide_eq_true hca, decide_eq_true hck, decide_eq_true hyy, iteB_of_true]
  · exact BPair.oneValue_refl _
  · rfl

/-- The fifth face's fold: the cubes at the corner holding the
plaquette as their upper-plane face, one per direction below the
plane's. -/
private theorem faceFold5 (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (G : Nat × Nat × Nat × Nat → BPair) :
    (tripleSum d L (fun x y z c => if y == a && z == k && c == s then G (x, y, z, c)
        else BPair.unit)).oneValue
      (bsum (fun x => if decide (x < a) then
        (if decide (coordAt L x s < L) then G (x, a, k, s) else BPair.unit) else BPair.unit)
        (List.range d)) := by
  have had : a < d := Nat.lt_trans hak hk
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    if decide (x < y) && decide (y < z) then
      (if (decide (coordAt L x s < L) && decide (coordAt L y s < L) && decide (coordAt L z s < L))
          && (y == a && z == k) then G (x, y, z, s) else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) d (fun x _ => bsum_congr_range_ov _ _ d
      (fun y _ => bsum_congr_range_ov _ _ d (fun z _ => ite_congr_prop _ (fun _ => ?_))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun c =>
      if (decide (coordAt L x c < L) && decide (coordAt L y c < L) && decide (coordAt L z c < L))
        && (y == a && z == k) && c == s then G (x, y, z, c) else BPair.unit) _ (fun c _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_beq d L _ _ s hs
  refine bsum_congr_range_ov _ _ d (fun x _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun y _ hya => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun z => ?_) _
    cases (decide (x < y) && decide (y < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hya, Bool.false_and, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ k d hk (fun z _ hzk => ?_)) ?_
  · cases (decide (x < a) && decide (a < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzk, Bool.and_false, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hak, Bool.and_true, eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), Bool.and_true,
    decide_eq_true hca, decide_eq_true hck, Bool.and_true, Bool.and_true, Bool.and_true]
  exact BPair.oneValue_refl _

/-- The sixth face's fold: the cubes at the corner stepped back along
a direction below the plane's, holding the plaquette as their upper
upper-plane face. -/
private theorem faceFold6 (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (G : Nat × Nat × Nat × Nat → BPair) :
    (tripleSum d L (fun x y z c => if y == a && z == k && stepAt L x c == s then (G (x, y, z, c)).swap
        else BPair.unit)).oneValue
      (bsum (fun x => if decide (x < a) then
        (if 0 < coordAt L x s then (G (x, a, k, s - (L + 1) ^ x)).swap else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have had : a < d := Nat.lt_trans hak hk
  have hL : 0 < L + 1 := Nat.succ_pos L
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    if decide (x < y) && decide (y < z) then
      (if 0 < coordAt L x s then
        (if (decide (coordAt L x (s - (L + 1) ^ x) < L) && decide (coordAt L y (s - (L + 1) ^ x) < L)
            && decide (coordAt L z (s - (L + 1) ^ x) < L)) && (y == a && z == k)
          then (G (x, y, z, s - (L + 1) ^ x)).swap else BPair.unit)
        else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) d (fun x _ => bsum_congr_range_ov _ _ d
      (fun y _ => bsum_congr_range_ov _ _ d (fun z _ => ite_congr_prop _ (fun _ => ?_))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun c =>
      if (decide (coordAt L x c < L) && decide (coordAt L y c < L) && decide (coordAt L z c < L))
        && (y == a && z == k) && stepAt L x c == s then (G (x, y, z, c)).swap else BPair.unit) _
      (fun c _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_step d L x _ (fun c hc => of_decide_eq_true (andSplitB (andSplitB (andSplitB hc).1).1).1)
      _ s hs
  refine bsum_congr_range_ov _ _ d (fun x _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun y _ hya => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun z => ?_) _
    cases (decide (x < y) && decide (y < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hya, Bool.false_and, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ k d hk (fun z _ hzk => ?_)) ?_
  · cases (decide (x < a) && decide (a < z)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzk, Bool.and_false, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hak, Bool.and_true, eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), Bool.and_true]
  refine ite_congr_prop _ (fun hxa => ?_)
  refine ite_congr_prop _ (fun hpos => ?_)
  have hxa' : x < a := of_decide_eq_true hxa
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) x s hL hpos
  have hxa2 : coordAt L a (s - (L + 1) ^ x) = coordAt L a s :=
    hoff a (fun h => Nat.ne_of_lt hxa' h.symm)
  have hxk : coordAt L k (s - (L + 1) ^ x) = coordAt L k s :=
    hoff k (fun h => Nat.ne_of_lt (Nat.lt_trans hxa' hak) h.symm)
  have hxx : coordAt L x (s - (L + 1) ^ x) < L := by
    have h := baseDigit_lt (L + 1) x s hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  rw [hxa2, hxk, decide_eq_true hca, decide_eq_true hck, decide_eq_true hxx, iteB_of_true]
  · exact BPair.oneValue_refl _
  · rfl

/-- Six members regroup at the sum's associativity, the unit joined. -/
private theorem regroup6 (A1 A2 A3 A4 A5 A6 : BPair) :
    (A1 + A2 + (A3 + A4 + (A5 + A6))).oneValue
      (A1 + (A2 + (A3 + (A4 + (A5 + (A6 + BPair.unit)))))) := by
  rw [BPair.add_assoc A1 A2, BPair.add_assoc A3 A4]
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (BPair.add_unit A6))))))

/-- The cubes holding a plaquette: the faces' sign of every cube at the
plaquette's key against a read of the cube folds to the reads at the
cubes holding it, two per further direction at the faces' signs, the
cube at the plaquette's corner and the cube at the corner stepped back
along the direction, the second occupied exactly where the corner's
coordinate there is occupied. -/
theorem cubes_holding (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (G : Nat × Nat × Nat × Nat → BPair) :
    (bsum (fun C => faceSign (cubeFaces d L C) (plaqKey d L a k s) * G C) (cubeList d L)).oneValue
      (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then G (a, k, z, s) else BPair.unit)
          + (if 0 < coordAt L z s then (G (a, k, z, s - (L + 1) ^ z)).swap else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (G (a, y, k, s)).swap else BPair.unit)
          + (if 0 < coordAt L y s then G (a, y, k, s - (L + 1) ^ y) else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then G (x, a, k, s) else BPair.unit)
          + (if 0 < coordAt L x s then (G (x, a, k, s - (L + 1) ^ x)).swap else BPair.unit)
        else BPair.unit) (List.range d))) := by
  refine BPair.oneValue_trans (bsum_cube_triples d L _) ?_
  show (tripleSum d L (fun x y z c => faceSign (cubeFaces d L (x, y, z, c)) (plaqKey d L a k s)
    * G (x, y, z, c))).oneValue _
  refine BPair.oneValue_trans (tripleSum_congr d L _ (fun x y z c =>
    (if x == a && y == k && c == s then G (x, y, z, c) else BPair.unit)
      + ((if x == a && y == k && stepAt L z c == s then (G (x, y, z, c)).swap else BPair.unit)
      + ((if x == a && z == k && c == s then (G (x, y, z, c)).swap else BPair.unit)
      + ((if x == a && z == k && stepAt L y c == s then G (x, y, z, c) else BPair.unit)
      + ((if y == a && z == k && c == s then G (x, y, z, c) else BPair.unit)
      + ((if y == a && z == k && stepAt L x c == s then (G (x, y, z, c)).swap else BPair.unit)
      + BPair.unit))))))
    (fun x y z c hxy hyz hz hc hcx hcy hcz => by
      rw [faceSign_read d L x y z c a k s hxy hyz hz hc hcx hcy hcz hak hk hs hca hck]
      exact faceInd_mul L x y z c a k s _)) ?_
  refine BPair.oneValue_trans (tripleSum_add d L _ _) ?_
  refine BPair.oneValue_trans (BPair.add_congr (faceFold1 d L a k s hak hk hs hca hck G)
    (BPair.oneValue_trans (tripleSum_add d L _ _) (BPair.add_congr (faceFold2 d L a k s hak hk hs hca hck G)
    (BPair.oneValue_trans (tripleSum_add d L _ _) (BPair.add_congr (faceFold3 d L a k s hak hk hs hca hck G)
    (BPair.oneValue_trans (tripleSum_add d L _ _) (BPair.add_congr (faceFold4 d L a k s hak hk hs hca hck G)
    (BPair.oneValue_trans (tripleSum_add d L _ _) (BPair.add_congr (faceFold5 d L a k s hak hk hs hca hck G)
    (BPair.oneValue_trans (tripleSum_add d L _ _) (BPair.add_congr (faceFold6 d L a k s hak hk hs hca hck G)
    (tripleSum_unit d L)))))))))))) ?_
  -- the pieces regroup at the three direction ranges
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun z _ => ite_add_unit _ _ _)) (foldB_add _ _ _))
    (BPair.add_congr
      (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun y _ => ite_add_unit _ _ _)) (foldB_add _ _ _))
      (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun x _ => ite_add_unit _ _ _)) (foldB_add _ _ _)))) ?_
  exact regroup6 _ _ _ _ _ _

/-! The Hodge fold: the consecutive differences along a direction on
a plane type's plaquettes, their squares' fold, the fold summed over
the plane types and the directions, and the fold's matrix. -/

/-- The consecutive differences along a direction on a plane type's
plaquettes: the site-plaquette list, at a site the plaquette of the
plane type at the site against the plaquette at the site stepped back
along the direction, the balance partner, the row occupied throughout
along a plane direction (the Dirichlet fold's differences at the
sum's unit beyond both ends) and off the first position along a
further direction (the Neumann fold's interior differences). -/
def diffMat (d L a k j : Nat) : Mat :=
  (sites d L).map (fun t =>
    (plaqList d L).map (fun q =>
      if (j == a || j == k) || decide (0 < coordAt L j t) then
        (if q.1 == a && q.2.1 == k && q.2.2 == t then BPair.ofNat 1 else BPair.unit)
        + (if q.1 == a && q.2.1 == k && decide (0 < coordAt L j t) && stepAt L j q.2.2 == t
            then (BPair.ofNat 1).swap else BPair.unit)
      else BPair.unit))

/-- The differences' squares' fold along a direction on a plane type
at a plaquette vector: a Dirichlet fold along a plane direction, a
Neumann fold along a further one. -/
def diffFold (d L a k j : Nat) (W : List BPair) : BPair :=
  dotN (matVec (diffMat d L a k j) W) (matVec (diffMat d L a k j) W)

/-- The Hodge fold at a plaquette vector: plane type by plane type the
two Dirichlet folds joined to the Neumann folds in the further
directions. -/
def hodgeFold (d L : Nat) (W : List BPair) : BPair :=
  bsum (fun a => bsum (fun k => if a < k then
    bsum (fun j => diffFold d L a k j W) (List.range d) else BPair.unit) (List.range d))
    (List.range d)

/-- The Hodge fold's matrix: the differences' Grams summed over the
plane types and the directions. -/
def hodgeMat (d L : Nat) : Mat :=
  msum (plaqCount d L) (fun a => msum (plaqCount d L) (fun k => if a < k then
    msum (plaqCount d L) (fun j => matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j))
      (List.range d)
    else nullMat (plaqCount d L) (plaqCount d L)) (List.range d)) (List.range d)

/-- The Hodge identity's read: the Gram joined to the cubes'
boundaries' Gram reads the Hodge fold's matrix entrywise. -/
def hodgeRead (d L : Nat) : Prop :=
  matOneValue (matAdd (gram d L) (cubeGram d L)) (hodgeMat d L)

instance instCornerwindow13 (d L : Nat) : Decidable (hodgeRead d L) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The differences' row count is the sites'. -/
theorem diffMat_length (d L a k j : Nat) : (diffMat d L a k j).length = (L + 1) ^ d := by
  show ((List.range ((L + 1) ^ d)).map _).length = _
  rw [ground.length_map, ground.length_range]

/-- The differences' rows sit at the plaquettes' count. -/
theorem diffMat_rows (d L a k j : Nat) : rowsLen (plaqCount d L) (diffMat d L a k j) := by
  refine rowsLen_map _ _ _ (fun t _ => ?_)
  show ((plaqList d L).map _).length = _
  rw [ground.length_map]
  rfl

/-- The differences' entry at a site and a plaquette's place. -/
theorem diffMat_entry (d L a k j t p : Nat) (ht : t < (L + 1) ^ d) (hp : p < plaqCount d L) :
    getAt BPair.unit (getAt [] (diffMat d L a k j) t) p
      = (if (j == a || j == k) || decide (0 < coordAt L j t) then
          (if (getAt (0, 0, 0) (plaqList d L) p).1 == a && (getAt (0, 0, 0) (plaqList d L) p).2.1 == k
              && (getAt (0, 0, 0) (plaqList d L) p).2.2 == t then BPair.ofNat 1 else BPair.unit)
          + (if (getAt (0, 0, 0) (plaqList d L) p).1 == a
              && (getAt (0, 0, 0) (plaqList d L) p).2.1 == k && decide (0 < coordAt L j t)
              && stepAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 == t
              then (BPair.ofNat 1).swap else BPair.unit)
        else BPair.unit) := by
  show getAt BPair.unit (getAt [] ((List.range ((L + 1) ^ d)).map (fun t =>
    (plaqList d L).map (fun q =>
      if (j == a || j == k) || decide (0 < coordAt L j t) then
        (if q.1 == a && q.2.1 == k && q.2.2 == t then BPair.ofNat 1 else BPair.unit)
        + (if q.1 == a && q.2.1 == k && decide (0 < coordAt L j t) && stepAt L j q.2.2 == t
            then (BPair.ofNat 1).swap else BPair.unit)
      else BPair.unit))) t) p = _
  rw [getAt_map 0 [] _ _ t (by rw [ground.length_range]; exact ht), getAt_range _ t ht,
    getAt_map (0, 0, 0) BPair.unit _ _ p hp]

/-- A fold of one guarded read at a stated guard reads the fold under
the guard. -/
private theorem bsum_ite_const (c : Bool) (F : Nat → BPair) (l : List Nat) :
    (bsum (fun t => if c then F t else BPair.unit) l).oneValue
      (if c then bsum F l else BPair.unit) := by
  cases c with
  | true => exact BPair.oneValue_refl _
  | false => exact famFold_unit_ov bpairFoldLaws _ (fun _ => BPair.oneValue_refl _) _

/-- The differences' entries' product at a site and two plaquettes'
data: the four guarded reads at the plane type's guards. -/
private theorem diffProd (L a k j t a1 k1 s a2 k2 s' : Nat) :
    ((if (j == a || j == k) || decide (0 < coordAt L j t) then
      (if (a1 == a && k1 == k) && s == t then BPair.ofNat 1 else BPair.unit)
      + (if ((a1 == a && k1 == k) && decide (0 < coordAt L j t)) && stepAt L j s == t
          then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
    * (if (j == a || j == k) || decide (0 < coordAt L j t) then
      (if (a2 == a && k2 == k) && s' == t then BPair.ofNat 1 else BPair.unit)
      + (if ((a2 == a && k2 == k) && decide (0 < coordAt L j t)) && stepAt L j s' == t
          then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)).oneValue
      (if (a1 == a && k1 == k) && (a2 == a && k2 == k) then
        (if ((j == a || j == k) || decide (0 < coordAt L j t)) && (s == t && s' == t)
          then BPair.ofNat 1 else BPair.unit)
        + ((if ((j == a || j == k) || decide (0 < coordAt L j t))
              && ((decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t)
          then (BPair.ofNat 1).swap else BPair.unit)
        + ((if ((j == a || j == k) || decide (0 < coordAt L j t))
              && (s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t))
          then (BPair.ofNat 1).swap else BPair.unit)
        + (if ((j == a || j == k) || decide (0 < coordAt L j t))
              && ((decide (0 < coordAt L j t) && stepAt L j s == t)
                && (decide (0 < coordAt L j t) && stepAt L j s' == t))
          then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) := by
  cases hPg : (a1 == a && k1 == k) with
  | false =>
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    cases ((j == a || j == k) || decide (0 < coordAt L j t)) with
    | false => exact BPair.unit_mul _
    | true =>
      show ((BPair.unit + BPair.unit) * _).oneValue BPair.unit
      exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.add_unit _)) (BPair.unit_mul _)
  | true =>
  cases hQg : (a2 == a && k2 == k) with
  | false =>
    repeat rw [Bool.and_false]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    cases ((j == a || j == k) || decide (0 < coordAt L j t)) with
    | false => exact BPair.mul_unit _
    | true =>
      show (_ * (BPair.unit + BPair.unit)).oneValue BPair.unit
      exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (BPair.add_unit _))
        (BPair.mul_unit _)
  | true =>
  repeat rw [Bool.true_and]
  rw [iteB_true]
  refine BPair.oneValue_trans (ite_mul_ite_and _ _ _ _) ?_
  rw [Bool.and_self]
  refine BPair.oneValue_trans (ite_congr_prop (A' :=
    ((if s == t && s' == t then BPair.ofNat 1 * BPair.ofNat 1 else BPair.unit)
    + (if (decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t
        then (BPair.ofNat 1).swap * BPair.ofNat 1 else BPair.unit))
    + ((if s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t)
        then BPair.ofNat 1 * (BPair.ofNat 1).swap else BPair.unit)
    + (if (decide (0 < coordAt L j t) && stepAt L j s == t)
          && (decide (0 < coordAt L j t) && stepAt L j s' == t)
        then (BPair.ofNat 1).swap * (BPair.ofNat 1).swap else BPair.unit))) _ (fun _ => ?_)) ?_
  · rw [BPair.left_distrib, BPair.right_distrib, BPair.right_distrib]
    exact BPair.add_congr (BPair.add_congr (ite_mul_ite_and _ _ _ _) (ite_mul_ite_and _ _ _ _))
      (BPair.add_congr (ite_mul_ite_and _ _ _ _) (ite_mul_ite_and _ _ _ _))
  refine BPair.oneValue_trans (ite_add_unit _ _ _) ?_
  refine BPair.oneValue_trans (BPair.add_congr (ite_add_unit _ _ _) (ite_add_unit _ _ _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
  refine BPair.add_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _))
    (ite_congr_prop _ (fun _ => BPair.ofNat_one_mul _))) ?_
  refine BPair.add_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _))
    (ite_congr_prop _ (fun _ => BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.ofNat_one_mul _)))) ?_
  refine BPair.add_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _))
    (ite_congr_prop _ (fun _ => BPair.ofNat_one_mul _))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _)) ?_
  exact ite_congr_prop _ (fun _ => swapOne_sq)

/-- The four guarded reads fold over the sites to the differences'
Gram's entry: the diagonal at the row's guard joined to the coordinate
below the side, the successor at a coordinate below the side and the
predecessor at an occupied coordinate. -/
private theorem diffSum_read (d L a k j s s' : Nat) (hj : j < d) (hs : s < (L + 1) ^ d) :
    (bsum (fun t =>
      (if ((j == a || j == k) || decide (0 < coordAt L j t)) && (s == t && s' == t)
        then BPair.ofNat 1 else BPair.unit)
      + ((if ((j == a || j == k) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t)
        then (BPair.ofNat 1).swap else BPair.unit)
      + ((if ((j == a || j == k) || decide (0 < coordAt L j t))
            && (s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t))
        then (BPair.ofNat 1).swap else BPair.unit)
      + (if ((j == a || j == k) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j s == t)
              && (decide (0 < coordAt L j t) && stepAt L j s' == t))
        then BPair.ofNat 1 else BPair.unit)))) (List.range ((L + 1) ^ d))).oneValue
      ((if ((j == a || j == k) || decide (0 < coordAt L j s)) && s' == s
          then BPair.ofNat 1 else BPair.unit)
      + ((if decide (coordAt L j s < L) && s' == stepAt L j s
          then (BPair.ofNat 1).swap else BPair.unit)
      + ((if decide (0 < coordAt L j s) && stepAt L j s' == s
          then (BPair.ofNat 1).swap else BPair.unit)
      + (if decide (coordAt L j s < L) && s' == s then BPair.ofNat 1 else BPair.unit)))) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  -- the two reads at the site itself
  have hS1 : (bsum (fun t => if ((j == a || j == k) || decide (0 < coordAt L j t))
      && (s == t && s' == t) then BPair.ofNat 1 else BPair.unit) (List.range ((L + 1) ^ d))).oneValue
      (if ((j == a || j == k) || decide (0 < coordAt L j s)) && s' == s
        then BPair.ofNat 1 else BPair.unit) := by
    refine BPair.oneValue_trans (bsum_range_at _ _ s _ hs (fun t _ ht =>
      (beqEqOf (andSplitB (andSplitB ht).2).1).symm)) ?_
    rw [eqBeqOf (rfl : s = s), Bool.true_and]
    exact BPair.oneValue_refl _
  have hS2 : (bsum (fun t => if ((j == a || j == k) || decide (0 < coordAt L j t))
      && (s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t))
      then (BPair.ofNat 1).swap else BPair.unit) (List.range ((L + 1) ^ d))).oneValue
      (if decide (0 < coordAt L j s) && stepAt L j s' == s
        then (BPair.ofNat 1).swap else BPair.unit) := by
    refine BPair.oneValue_trans (bsum_range_at _ _ s _ hs (fun t _ ht =>
      (beqEqOf (andSplitB (andSplitB ht).2).1).symm)) ?_
    rw [eqBeqOf (rfl : s = s), Bool.true_and,
      ite_and_absorb _ _ (fun h => by rw [(andSplitB h).1]; exact Bool.or_true _)]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr hS1 ?_
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  cases Nat.lt_or_ge (coordAt L j s) L with
  | inr hge =>
    have hnl : ¬ coordAt L j s < L := Nat.not_lt_of_ge hge
    have htop : coordAt L j s + 1 = L + 1 :=
      congrArg Nat.succ (Nat.le_antisymm (Nat.le_of_lt_succ (baseDigit_lt (L + 1) j s hL)) hge)
    have hstep : ∀ t, (stepAt L j s == t) = true → decide (0 < coordAt L j t) = false := by
      intro t ht
      rw [← beqEqOf ht]
      have h0 : coordAt L j (stepAt L j s) = 0 := baseDigit_step_top (L + 1) j s hL htop
      rw [h0]
      exact decide_eq_false (Nat.lt_irrefl 0)
    rw [decide_eq_false hnl, Bool.false_and, Bool.false_and, iteB_false, iteB_false]
    refine BPair.add_congr (bsum_range_none _ _ _ (fun t _ => ?_)) ?_
    · cases hc : (((j == a || j == k) || decide (0 < coordAt L j t))
          && ((decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t)) with
      | false => rfl
      | true =>
        have h1 := andSplitB (andSplitB (andSplitB hc).2).1
        rw [hstep t h1.2] at h1
        exact Bool.noConfusion h1.1
    refine BPair.oneValue_trans (foldB_add _ _ _) ?_
    refine BPair.add_congr hS2 (bsum_range_none _ _ _ (fun t _ => ?_))
    cases hc : (((j == a || j == k) || decide (0 < coordAt L j t))
        && ((decide (0 < coordAt L j t) && stepAt L j s == t)
          && (decide (0 < coordAt L j t) && stepAt L j s' == t))) with
    | false => rfl
    | true =>
      have h1 := andSplitB (andSplitB (andSplitB hc).2).1
      rw [hstep t h1.2] at h1
      exact Bool.noConfusion h1.1
  | inl hlt =>
    have hsl := stepAt_lt d L j s hj hs hlt
    have hcs : coordAt L j (stepAt L j s) = coordAt L j s + 1 := coordAt_step L j s hlt
    have hpos : decide (0 < coordAt L j (stepAt L j s)) = true := by
      rw [hcs]
      exact decide_eq_true (Nat.succ_pos _)
    rw [decide_eq_true hlt, Bool.true_and, Bool.true_and]
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_trans (bsum_range_at _ _ (stepAt L j s) _ hsl (fun t _ ht =>
        (beqEqOf (andSplitB (andSplitB (andSplitB ht).2).1).2).symm)) ?_
      rw [hpos, Bool.or_true, Bool.true_and, eqBeqOf (rfl : stepAt L j s = stepAt L j s),
        Bool.and_true, Bool.true_and]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (foldB_add _ _ _) ?_
    refine BPair.add_congr hS2 ?_
    refine BPair.oneValue_trans (bsum_range_at _ _ (stepAt L j s) _ hsl (fun t _ ht =>
      (beqEqOf (andSplitB (andSplitB (andSplitB ht).2).1).2).symm)) ?_
    rw [hpos, Bool.or_true, Bool.true_and, eqBeqOf (rfl : stepAt L j s = stepAt L j s),
      Bool.and_true, Bool.true_and, Bool.true_and, beq_step]
    exact BPair.oneValue_refl _

/-- The differences' Gram's entry at two plaquettes of the plane type:
the diagonal reads one at the row's guard joined to one at the
coordinate below the side, and the two consecutive keys read the
balance partner of one, the successor at a coordinate below the side
and the predecessor at an occupied coordinate; the sum's unit off the
plane type. -/
theorem diffGram_entry (d L a k j p q : Nat) (hj : j < d) (hp : p < plaqCount d L)
    (hq : q < plaqCount d L) :
    (getAt BPair.unit (getAt [] (matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j)) p)
      q).oneValue
      (if ((getAt (0, 0, 0) (plaqList d L) p).1 == a && (getAt (0, 0, 0) (plaqList d L) p).2.1 == k)
          && ((getAt (0, 0, 0) (plaqList d L) q).1 == a && (getAt (0, 0, 0) (plaqList d L) q).2.1 == k)
        then
        (if ((j == a || j == k) || decide (0 < coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2))
            && (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
          then BPair.ofNat 1 else BPair.unit)
        + ((if decide (coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 < L)
            && (getAt (0, 0, 0) (plaqList d L) q).2.2 == stepAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + ((if decide (0 < coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2)
            && stepAt L j (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + (if decide (coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 < L)
            && (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
          then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  have hBl := diffMat_length d L a k j
  have hB := diffMat_rows d L a k j
  have hpos : 0 < (diffMat d L a k j).length := by
    rw [hBl]
    exact Nat.pow_pos hL
  have hBt : (transposeM (diffMat d L a k j)).length = plaqCount d L := length_transposeM _ hB hpos
  have hpT : p < (transposeM (diffMat d L a k j)).length := by rw [hBt]; exact hp
  have hqT : q < (transposeM (diffMat d L a k j)).length := by rw [hBt]; exact hq
  rw [getAt_matMul _ _ p hpT, getAt_map [] BPair.unit _ _ q hqT]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  have hBtr : rowsLen ((L + 1) ^ d) (transposeM (diffMat d L a k j)) := by
    rw [← hBl]
    exact rowsLen_transposeM _
  rw [dotP_fold ((L + 1) ^ d) _ _ (rowsLen_getAt _ p hBtr hpT) (rowsLen_getAt _ q hBtr hqT)]
  have hpl := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
    if ((getAt (0, 0, 0) (plaqList d L) p).1 == a && (getAt (0, 0, 0) (plaqList d L) p).2.1 == k)
        && ((getAt (0, 0, 0) (plaqList d L) q).1 == a && (getAt (0, 0, 0) (plaqList d L) q).2.1 == k)
      then
      (if ((j == a || j == k) || decide (0 < coordAt L j t))
          && ((getAt (0, 0, 0) (plaqList d L) p).2.2 == t && (getAt (0, 0, 0) (plaqList d L) q).2.2 == t)
        then BPair.ofNat 1 else BPair.unit)
      + ((if ((j == a || j == k) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 == t)
              && (getAt (0, 0, 0) (plaqList d L) q).2.2 == t)
        then (BPair.ofNat 1).swap else BPair.unit)
      + ((if ((j == a || j == k) || decide (0 < coordAt L j t))
            && ((getAt (0, 0, 0) (plaqList d L) p).2.2 == t && (decide (0 < coordAt L j t)
              && stepAt L j (getAt (0, 0, 0) (plaqList d L) q).2.2 == t))
        then (BPair.ofNat 1).swap else BPair.unit)
      + (if ((j == a || j == k) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 == t)
              && (decide (0 < coordAt L j t) && stepAt L j (getAt (0, 0, 0) (plaqList d L) q).2.2 == t))
        then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) _ (fun t ht => by
    rw [getAt_transposeM BPair.unit _ hB p t hp (by rw [hBl]; exact ht),
      getAt_transposeM BPair.unit _ hB q t hq (by rw [hBl]; exact ht),
      diffMat_entry d L a k j t p ht hp, diffMat_entry d L a k j t q ht hq]
    exact diffProd L a k j t _ _ _ _ _ _)) ?_
  refine BPair.oneValue_trans (bsum_ite_const _ _ _) ?_
  refine ite_congr_prop _ (fun _ => ?_)
  exact diffSum_read d L a k j _ _ hj hpl.2.2.1

/-- The differences' Gram's shape at a plane type and a direction. -/
private theorem diffGram_shape (d L a k j : Nat) :
    rowsLen (plaqCount d L) (matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j))
      ∧ (matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j)).length = plaqCount d L := by
  have hBl := diffMat_length d L a k j
  have hB := diffMat_rows d L a k j
  have hpos : 0 < (diffMat d L a k j).length := by
    rw [hBl]
    exact Nat.pow_pos (Nat.succ_pos L)
  have hBt : (transposeM (diffMat d L a k j)).length = plaqCount d L :=
    length_transposeM _ hB hpos
  refine ⟨?_, ?_⟩
  · rw [← hBt]
    exact rowsLen_matMul _ _
  · rw [length_matMul, hBt]

/-- The plane type's summand's shape. -/
private theorem hodgePlane_shape (d L a k : Nat) :
    rowsLen (plaqCount d L) (if a < k then
        msum (plaqCount d L) (fun j => matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j))
          (List.range d) else nullMat (plaqCount d L) (plaqCount d L))
      ∧ (if a < k then
        msum (plaqCount d L) (fun j => matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j))
          (List.range d) else nullMat (plaqCount d L) (plaqCount d L)).length = plaqCount d L := by
  by_cases h : a < k
  · rw [if_pos h]
    exact msum_shape _ _ (fun j => diffGram_shape d L a k j) _
  · rw [if_neg h]
    exact ⟨rowsLen_nullMat _ _, length_nullMat _ _⟩

/-- The Hodge fold's matrix is square at the plaquettes' count. -/
theorem hodgeMat_shape (d L : Nat) :
    rowsLen (plaqCount d L) (hodgeMat d L) ∧ (hodgeMat d L).length = plaqCount d L :=
  msum_shape _ _ (fun a => msum_shape _ _ (hodgePlane_shape d L a) _) _

/-- The Hodge fold's matrix's entry: the fold over the plane types
and the directions of the differences' Grams' entries. -/
theorem hodgeMat_entry (d L p q : Nat) (hp : p < plaqCount d L) (hq : q < plaqCount d L) :
    getAt BPair.unit (getAt [] (hodgeMat d L) p) q
      = bsum (fun a => bsum (fun k => if a < k then
          bsum (fun j => getAt BPair.unit (getAt []
            (matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j)) p) q) (List.range d)
          else BPair.unit) (List.range d)) (List.range d) := by
  show getAt BPair.unit (getAt [] (msum (plaqCount d L) (fun a => msum (plaqCount d L) (fun k =>
    if a < k then msum (plaqCount d L)
      (fun j => matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j)) (List.range d)
    else nullMat (plaqCount d L) (plaqCount d L)) (List.range d)) (List.range d)) p) q = _
  rw [entry_msum _ _ p q hp hq _ (fun a _ => msum_shape _ _ (hodgePlane_shape d L a) _)]
  refine famFold_congr_members BPair.add BPair.unit _ _ (List.range d) (fun a _ => ?_)
  rw [entry_msum _ _ p q hp hq _ (fun k _ => hodgePlane_shape d L a k)]
  refine famFold_congr_members BPair.add BPair.unit _ _ (List.range d) (fun k _ => ?_)
  by_cases h : a < k
  · rw [if_pos h, if_pos h, entry_msum _ _ p q hp hq _ (fun j _ => diffGram_shape d L a k j)]
    rfl
  · rw [if_neg h, if_neg h]
    show getAt BPair.unit (getAt [] (List.replicate (plaqCount d L)
      (List.replicate (plaqCount d L) BPair.unit)) p) q = _
    rw [getAt_replicate [] _ _ p hp, getAt_replicate BPair.unit _ _ q hq]

/-- The cubes holding a plaquette read a second valid plaquette's faces'
signs as its six face reads at the data. -/
private theorem holding_faceInd (d L a k s a' k' s' : Nat) (hak : a < k) (hk : k < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hck : coordAt L k s < L)
    (hak' : a' < k') (hk' : k' < d) (hs' : s' < (L + 1) ^ d)
    (hca' : coordAt L a' s' < L) (hck' : coordAt L k' s' < L) :
    (bsum (fun z => if decide (k < z) then
        (if decide (coordAt L z s < L) then faceSign (cubeFaces d L (a, k, z, s)) (plaqKey d L a' k' s')
          else BPair.unit)
        + (if 0 < coordAt L z s
          then (faceSign (cubeFaces d L (a, k, z, s - (L + 1) ^ z)) (plaqKey d L a' k' s')).swap
          else BPair.unit)
      else BPair.unit) (List.range d)
    + (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if decide (coordAt L y s < L)
          then (faceSign (cubeFaces d L (a, y, k, s)) (plaqKey d L a' k' s')).swap else BPair.unit)
        + (if 0 < coordAt L y s
          then faceSign (cubeFaces d L (a, y, k, s - (L + 1) ^ y)) (plaqKey d L a' k' s')
          else BPair.unit)
      else BPair.unit) (List.range d)
    + bsum (fun x => if decide (x < a) then
        (if decide (coordAt L x s < L) then faceSign (cubeFaces d L (x, a, k, s)) (plaqKey d L a' k' s')
          else BPair.unit)
        + (if 0 < coordAt L x s
          then (faceSign (cubeFaces d L (x, a, k, s - (L + 1) ^ x)) (plaqKey d L a' k' s')).swap
          else BPair.unit)
      else BPair.unit) (List.range d))).oneValue
    (bsum (fun z => if decide (k < z) then
        (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a' k' s' else BPair.unit)
        + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a' k' s').swap
          else BPair.unit)
      else BPair.unit) (List.range d)
    + (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' k' s').swap else BPair.unit)
        + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' k' s' else BPair.unit)
      else BPair.unit) (List.range d)
    + bsum (fun x => if decide (x < a) then
        (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' k' s' else BPair.unit)
        + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' k' s').swap
          else BPair.unit)
      else BPair.unit) (List.range d))) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  have had : a < d := Nat.lt_trans hak hk
  refine BPair.add_congr (bsum_congr_range_ov _ _ d (fun z hz => ?_))
    (BPair.add_congr (bsum_congr_range_ov _ _ d (fun y hy => ?_))
      (bsum_congr_range_ov _ _ d (fun x hx => ?_)))
  · refine ite_congr_prop _ (fun hkz => ?_)
    have hkz' : k < z := of_decide_eq_true hkz
    refine BPair.add_congr (ite_congr_prop _ (fun hcz => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · rw [faceSign_read d L a k z s a' k' s' hak hkz' hz hs hca hck (of_decide_eq_true hcz)
        hak' hk' hs' hca' hck']
      exact BPair.oneValue_refl _
    · obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) z s hL hpos
      have hlt : s - (L + 1) ^ z < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs
      have hza : coordAt L a (s - (L + 1) ^ z) < L := by
        rw [show coordAt L a (s - (L + 1) ^ z) = coordAt L a s from
          hoff a (Nat.ne_of_lt (Nat.lt_trans hak hkz'))]
        exact hca
      have hzk : coordAt L k (s - (L + 1) ^ z) < L := by
        rw [show coordAt L k (s - (L + 1) ^ z) = coordAt L k s from hoff k (Nat.ne_of_lt hkz')]
        exact hck
      have hzz : coordAt L z (s - (L + 1) ^ z) < L := by
        have h := baseDigit_lt (L + 1) z s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [faceSign_read d L a k z _ a' k' s' hak hkz' hz hlt hza hzk hzz hak' hk' hs' hca' hck']
      exact BPair.oneValue_refl _
  · refine ite_congr_prop _ (fun hg => ?_)
    have hay : a < y := of_decide_eq_true (andSplitB hg).1
    have hyk : y < k := of_decide_eq_true (andSplitB hg).2
    refine BPair.add_congr (ite_congr_prop _ (fun hcy => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · rw [faceSign_read d L a y k s a' k' s' hay hyk hk hs hca (of_decide_eq_true hcy) hck
        hak' hk' hs' hca' hck']
      exact BPair.oneValue_refl _
    · obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) y s hL hpos
      have hlt : s - (L + 1) ^ y < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs
      have hya : coordAt L a (s - (L + 1) ^ y) < L := by
        rw [show coordAt L a (s - (L + 1) ^ y) = coordAt L a s from hoff a (Nat.ne_of_lt hay)]
        exact hca
      have hyk' : coordAt L k (s - (L + 1) ^ y) < L := by
        rw [show coordAt L k (s - (L + 1) ^ y) = coordAt L k s from
          hoff k (fun h => Nat.ne_of_lt hyk h.symm)]
        exact hck
      have hyy : coordAt L y (s - (L + 1) ^ y) < L := by
        have h := baseDigit_lt (L + 1) y s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [faceSign_read d L a y k _ a' k' s' hay hyk hk hlt hya hyy hyk' hak' hk' hs' hca' hck']
      exact BPair.oneValue_refl _
  · refine ite_congr_prop _ (fun hxa => ?_)
    have hxa' : x < a := of_decide_eq_true hxa
    refine BPair.add_congr (ite_congr_prop _ (fun hcx => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · rw [faceSign_read d L x a k s a' k' s' hxa' hak hk hs (of_decide_eq_true hcx) hca hck
        hak' hk' hs' hca' hck']
      exact BPair.oneValue_refl _
    · obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) x s hL hpos
      have hlt : s - (L + 1) ^ x < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs
      have hxa2 : coordAt L a (s - (L + 1) ^ x) < L := by
        rw [show coordAt L a (s - (L + 1) ^ x) = coordAt L a s from
          hoff a (fun h => Nat.ne_of_lt hxa' h.symm)]
        exact hca
      have hxk : coordAt L k (s - (L + 1) ^ x) < L := by
        rw [show coordAt L k (s - (L + 1) ^ x) = coordAt L k s from
          hoff k (fun h => Nat.ne_of_lt (Nat.lt_trans hxa' hak) h.symm)]
        exact hck
      have hxx : coordAt L x (s - (L + 1) ^ x) < L := by
        have h := baseDigit_lt (L + 1) x s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [faceSign_read d L x a k _ a' k' s' hxa' hak hk hlt hxx hxa2 hxk hak' hk' hs' hca' hck']
      exact BPair.oneValue_refl _

/-- The Hodge fold's matrix's entry at two plaquettes: the differences'
Grams' entries summed over the directions at the first's plane type,
the sum's unit at a second plaquette off the plane type. -/
private theorem hodgeMat_entry_plane (d L p q : Nat) (hp : p < plaqCount d L)
    (hq : q < plaqCount d L) :
    (getAt BPair.unit (getAt [] (hodgeMat d L) p) q).oneValue
      (if (getAt (0, 0, 0) (plaqList d L) q).1 == (getAt (0, 0, 0) (plaqList d L) p).1
          && (getAt (0, 0, 0) (plaqList d L) q).2.1 == (getAt (0, 0, 0) (plaqList d L) p).2.1 then
        bsum (fun j =>
          (if ((j == (getAt (0, 0, 0) (plaqList d L) p).1 || j == (getAt (0, 0, 0) (plaqList d L) p).2.1)
              || decide (0 < coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2))
              && (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
            then BPair.ofNat 1 else BPair.unit)
          + ((if decide (coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 < L)
              && (getAt (0, 0, 0) (plaqList d L) q).2.2
                == stepAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2
            then (BPair.ofNat 1).swap else BPair.unit)
          + ((if decide (0 < coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2)
              && stepAt L j (getAt (0, 0, 0) (plaqList d L) q).2.2
                == (getAt (0, 0, 0) (plaqList d L) p).2.2
            then (BPair.ofNat 1).swap else BPair.unit)
          + (if decide (coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 < L)
              && (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
            then BPair.ofNat 1 else BPair.unit)))) (List.range d)
      else BPair.unit) := by
  rw [hodgeMat_entry d L p q hp hq]
  have hpl := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun a => bsum (fun k => if a < k then
    bsum (fun j => if ((getAt (0, 0, 0) (plaqList d L) p).1 == a
          && (getAt (0, 0, 0) (plaqList d L) p).2.1 == k)
        && ((getAt (0, 0, 0) (plaqList d L) q).1 == a && (getAt (0, 0, 0) (plaqList d L) q).2.1 == k)
      then
        (if ((j == a || j == k) || decide (0 < coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2))
            && (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
          then BPair.ofNat 1 else BPair.unit)
        + ((if decide (coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 < L)
            && (getAt (0, 0, 0) (plaqList d L) q).2.2 == stepAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + ((if decide (0 < coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2)
            && stepAt L j (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + (if decide (coordAt L j (getAt (0, 0, 0) (plaqList d L) p).2.2 < L)
            && (getAt (0, 0, 0) (plaqList d L) q).2.2 == (getAt (0, 0, 0) (plaqList d L) p).2.2
          then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) (List.range d) else BPair.unit) (List.range d)) d (fun a _ =>
    bsum_congr_range_ov _ _ d (fun k _ => ite_congr_prop _ (fun _ =>
      bsum_congr_range_ov _ _ d (fun j hj => diffGram_entry d L a k j p q hj hp hq))))) ?_
  generalize hP : getAt (0, 0, 0) (plaqList d L) p = P at hpl ⊢
  generalize hQ : getAt (0, 0, 0) (plaqList d L) q = Q
  obtain ⟨hak, hkd, hsd, hca, hck⟩ := hpl
  cases P with
  | mk a P' =>
  cases P' with
  | mk k s =>
  cases Q with
  | mk a' Q' =>
  cases Q' with
  | mk k' s' =>
  have had : a < d := Nat.lt_trans hak hkd
  show (bsum (fun a2 => bsum (fun k2 => if a2 < k2 then bsum (fun j =>
    if (a == a2 && k == k2) && (a' == a2 && k' == k2) then _ else BPair.unit) (List.range d)
    else BPair.unit) (List.range d)) (List.range d)).oneValue
    (if a' == a && k' == k then _ else BPair.unit)
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun a2 _ ha2 => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun k2 => ?_) _
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun j => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf (fun h => ha2 h.symm), Bool.false_and, Bool.false_and, iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ k d hkd (fun k2 _ hk2 => ?_)) ?_
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun j => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf (fun h => hk2 h.symm), Bool.and_false, Bool.false_and, iteB_false]
    exact BPair.oneValue_refl _
  rw [if_pos hak, eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), Bool.and_true, Bool.true_and]
  exact bsum_ite_const _ _ _

/-! The Hodge identity's case reads: the face reads of a cube at a
plaquette's data reduce at the directions' comparisons, the stepped-back
corner's reads convert to the plaquette's step reads, and the guards
absorb at the plaquettes' validity. -/

/-- Five units fold to the unit. -/
private theorem units5 :
    (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))).oneValue BPair.unit := by
  decide

/-- A cube's face reads at a plaquette off every face read the unit. -/
private theorem faceInd_unit (L x y z c a' k' s' : Nat) (h12 : (x == a' && y == k') = false)
    (h34 : (x == a' && z == k') = false) (h56 : (y == a' && z == k') = false) :
    (faceInd L (x, y, z, c) a' k' s').oneValue BPair.unit := by
  delta faceInd
  rw [h12, h34, h56]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  decide

/-- A cube's face reads at a plaquette of its lower plane type: the
plaquette at the corner forward, at the corner stepped along the third
direction backward. -/
private theorem faceInd_12 (L x y z c a' k' s' : Nat) (h12 : (x == a' && y == k') = true)
    (h34 : (x == a' && z == k') = false) (h56 : (y == a' && z == k') = false) :
    (faceInd L (x, y, z, c) a' k' s').oneValue
      ((if c == s' then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L z c == s' then (BPair.ofNat 1).swap else BPair.unit)) := by
  delta faceInd
  rw [h12, h34, h56]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) units5) (BPair.add_unit _))

/-- A cube's face reads at a plaquette of its outer plane type: the
plaquette at the corner backward, at the corner stepped along the
middle direction forward. -/
private theorem faceInd_34 (L x y z c a' k' s' : Nat) (h12 : (x == a' && y == k') = false)
    (h34 : (x == a' && z == k') = true) (h56 : (y == a' && z == k') = false) :
    (faceInd L (x, y, z, c) a' k' s').oneValue
      ((if c == s' then (BPair.ofNat 1).swap else BPair.unit)
        + (if stepAt L y c == s' then BPair.ofNat 1 else BPair.unit)) := by
  delta faceInd
  rw [h12, h34, h56]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  refine BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _) ?_)
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _))
        (BPair.add_unit _))) (BPair.add_unit _))

/-- A cube's face reads at a plaquette of its upper plane type: the
plaquette at the corner forward, at the corner stepped along the first
direction backward. -/
private theorem faceInd_56 (L x y z c a' k' s' : Nat) (h12 : (x == a' && y == k') = false)
    (h34 : (x == a' && z == k') = false) (h56 : (y == a' && z == k') = true) :
    (faceInd L (x, y, z, c) a' k' s').oneValue
      ((if c == s' then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L x c == s' then (BPair.ofNat 1).swap else BPair.unit)) := by
  delta faceInd
  rw [h12, h34, h56]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  refine BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _)
    (BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _) ?_)))
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)

/-- The stepped-back corner keyed to a site reads the site's step
keyed to the corner's own. -/
private theorem beq_stepBack (L j s s' : Nat) (hpos : 0 < coordAt L j s) :
    ((s - (L + 1) ^ j == s') = (stepAt L j s' == s)) := by
  obtain ⟨hs0e, _, _⟩ := stepBack (L + 1) j s (Nat.succ_pos L) hpos
  rw [beqSymm (s - (L + 1) ^ j) s', ← beq_step L j, show stepAt L j (s - (L + 1) ^ j) = s from hs0e]

/-- The stepped-back corner's step along a second direction keyed to a
site reads the site's step keyed to the corner's step along the second
direction. -/
private theorem beq_step_stepBack (L j k s s' : Nat) (hpos : 0 < coordAt L j s) :
    ((stepAt L k (s - (L + 1) ^ j) == s') = (stepAt L j s' == stepAt L k s)) := by
  obtain ⟨hs0e, _, _⟩ := stepBack (L + 1) j s (Nat.succ_pos L) hpos
  rw [beqSymm (stepAt L k (s - (L + 1) ^ j)) s', ← beq_step L j, stepAt_comm L j k,
    show stepAt L j (s - (L + 1) ^ j) = s from hs0e]

/-- A read at a plaquette's key against the site reads the key's
coordinate below the side at a second direction of the plaquette. -/
private theorem guard_of_beq (L j s s' : Nat) (hc : coordAt L j s' < L) (h : (s' == s) = true) :
    decide (coordAt L j s < L) = true := by
  rw [← beqEqOf h]
  exact decide_eq_true hc

/-- A read at a plaquette's key against a step off the direction reads
the key's coordinate below the side there. -/
private theorem guard_of_beq_step (L j k s s' : Nat) (hck : coordAt L k s < L) (hjk : ¬ j = k)
    (hc : coordAt L j s' < L) (h : (s' == stepAt L k s) = true) :
    decide (coordAt L j s < L) = true := by
  rw [beqEqOf h, coordAt_step_ne L k j s hck hjk] at hc
  exact decide_eq_true hc

/-- A step of a plaquette's key along its own direction keyed to a site
reads the site's coordinate there occupied. -/
private theorem occ_of_step_beq (L j s s' : Nat) (hc : coordAt L j s' < L)
    (h : (stepAt L j s' == s) = true) : 0 < coordAt L j s := by
  rw [← beqEqOf h, coordAt_step L j s' hc]
  exact Nat.succ_pos _

/-- A step along a plaquette's direction keyed to a step off it reads
the site's coordinate there occupied. -/
private theorem occ_of_step_beq_step (L j k s s' : Nat) (hck : coordAt L k s < L) (hjk : ¬ j = k)
    (hc : coordAt L j s' < L) (h : (stepAt L j s' == stepAt L k s) = true) :
    0 < coordAt L j s := by
  have e : coordAt L j (stepAt L k s) = coordAt L j (stepAt L j s') := by rw [beqEqOf h]
  rw [coordAt_step_ne L k j s hck hjk, coordAt_step L j s' hc] at e
  rw [e]
  exact Nat.succ_pos _

/-- The piece's guarded pair at a corner swapped reads the swapped
members. -/
private theorem swap_pair (A C : Bool) (x y : BPair) :
    ((if A then x else BPair.unit) + (if C then y else BPair.unit)).swap
      = (if A then x.swap else BPair.unit) + (if C then y.swap else BPair.unit) := by
  rw [← BPair.swap_add, ite_swap, ite_swap]

/-- A guarded read over a piece's directions, each summand the unit,
reads the unit. -/
private theorem piece_unit (d : Nat) (P : Nat → Bool) (g1 : Nat → Bool) (g2 : Nat → Prop)
    [∀ j, Decidable (g2 j)] (F G : Nat → BPair) (hF : ∀ j, P j = true → (F j).oneValue BPair.unit)
    (hG : ∀ j, P j = true → (G j).oneValue BPair.unit) :
    (bsum (fun j => if P j then (if g1 j then F j else BPair.unit)
      + (if g2 j then G j else BPair.unit) else BPair.unit) (List.range d)).oneValue BPair.unit := by
  refine famFold_unit_ov bpairFoldLaws _ (fun j => ?_) _
  refine BPair.oneValue_trans (ite_congr_prop _ (fun hP => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hF j hP)) (BPair.oneValue_of_eq (ite_prop_unit _)))
    (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hG j hP))
      (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)

/-- The plaquette-pair shape at two plaquettes sharing the lower
direction: the incidence's four reads against the one cube's two reads
fold to the unit. -/
private theorem shape2 (A B C D : Bool) :
    (((if A then BPair.ofNat 1 else BPair.unit)
        + (BPair.unit + ((if B then (BPair.ofNat 1).swap else BPair.unit)
          + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + (((if C then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if D then (BPair.ofNat 1).swap else BPair.unit)
            + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
        + BPair.unit)))
      + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if C then BPair.ofNat 1 else BPair.unit))
        + ((if B then BPair.ofNat 1 else BPair.unit) + (if D then (BPair.ofNat 1).swap else BPair.unit))
        + (BPair.unit + BPair.unit))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- A guarded pair of reads at the corner absorbs its guard into the
reads, each read at the plaquettes' validity holding the guard. -/
private theorem absorb_pair (g A C : Bool) (hA : A = true → g = true) (hC : C = true → g = true)
    (x y : BPair) :
    (if g then (if A then x else BPair.unit) + (if C then y else BPair.unit) else BPair.unit).oneValue
      ((if A then x else BPair.unit) + (if C then y else BPair.unit)) := by
  refine BPair.oneValue_trans (ite_add_unit _ _ _) ?_
  rw [ite_ite_and, ite_ite_and, ite_and_absorb _ _ hA, ite_and_absorb _ _ hC]
  exact BPair.oneValue_refl _

/-- A guarded pair of reads at a stated guard absorbs the guard into
the reads, each read holding the guard. -/
private theorem absorb_pair_prop (P : Prop) [Decidable P] (A C : Bool) (hA : A = true → P)
    (hC : C = true → P) (x y : BPair) :
    (if P then (if A then x else BPair.unit) + (if C then y else BPair.unit) else BPair.unit).oneValue
      ((if A then x else BPair.unit) + (if C then y else BPair.unit)) := by
  by_cases hP : P
  · rw [if_pos hP]
    exact BPair.oneValue_refl _
  · rw [if_neg hP]
    cases hA' : A with
    | true => exact absurd (hA hA') hP
    | false =>
      cases hC' : C with
      | true => exact absurd (hC hC') hP
      | false => exact BPair.oneValue_symm (BPair.add_unit _)

set_option maxHeartbeats 800000 in
/-- The second case: two plaquettes sharing the lower direction at
distinct planes, the incidence's reads at the shared link against the
one cube's two face reads. -/
private theorem hodge_case2 (d L a k s k' s' : Nat) (hak : a < k) (hck : coordAt L k s < L)
    (hak' : a < k') (hkd' : k' < d) (hck' : coordAt L k' s' < L) (hkk : ¬ k' = k) :
    (linkInd L (a, k', s') a s * BPair.ofNat 1
      + (linkInd L (a, k', s') k (stepAt L a s) * BPair.ofNat 1
      + (linkInd L (a, k', s') a (stepAt L k s) * (BPair.ofNat 1).swap
      + (linkInd L (a, k', s') k s * (BPair.ofNat 1).swap + BPair.unit)))
      + (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a k' s' else BPair.unit)
          + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a k' s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a k' s').swap else BPair.unit)
          + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a k' s' else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a k' s' else BPair.unit)
          + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a k' s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)))).oneValue BPair.unit := by
  have nka : ¬ k = a := fun h => Nat.ne_of_lt hak h.symm
  have nk'a : ¬ k' = a := fun h => Nat.ne_of_lt hak' h.symm
  have nk'k : ¬ k' = k := hkk
  have hkk'b : (k == k') = false := neBeqOf (fun h => hkk h.symm)
  have h12 : (a == a && k == k') = false := by
    rw [eqBeqOf (rfl : a = a), Bool.true_and]
    exact hkk'b
  have h56z : ∀ z, (k == a && z == k') = false := fun z => by
    rw [neBeqOf nka, Bool.false_and]
  -- the piece off the plane's directions reads the unit
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a k' s' else BPair.unit)
      + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a k' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun x hg => ?_) (fun x hg => ?_)
    · have hxa : x < a := of_decide_eq_true hg
      exact faceInd_unit L x a k s a k' s' (by rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and]) h12
    · have hxa : x < a := of_decide_eq_true hg
      exact swap_congr (faceInd_unit L x a k _ a k' s'
        (by rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and]) h12)
  -- the plane pair's reduced form, one piece occupied
  have hP : ∀ (c : Nat), (0 < coordAt L k' s) → c = s - (L + 1) ^ k' →
      ((if c == s' then (BPair.ofNat 1).swap else BPair.unit)
        + (if stepAt L k c == s' then BPair.ofNat 1 else BPair.unit)).swap.oneValue
      ((if stepAt L k' s' == s then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L k' s' == stepAt L k s then (BPair.ofNat 1).swap else BPair.unit)) := by
    intro c hpos hc
    rw [hc, swap_pair, BPair.swap_swap, beq_stepBack L k' s s' hpos,
      beq_step_stepBack L k' k s s' hpos]
    exact BPair.oneValue_refl _
  cases Nat.lt_or_ge k k' with
  | inl hkk' =>
    have hz : (bsum (fun z => if decide (k < z) then
        (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a k' s' else BPair.unit)
        + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a k' s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L k' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L k s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L k' s then
          (if stepAt L k' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L k' s' == stepAt L k s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ k' d hkd' (fun z _ hzk' => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ c, (faceInd L (a, k, z, c) a k' s').oneValue BPair.unit := fun c =>
          faceInd_unit L a k z c a k' s' h12
            (by rw [eqBeqOf (rfl : a = a), Bool.true_and]; exact neBeqOf hzk') (h56z z)
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s)) (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hkk', iteB_true]
        have h34 : (a == a && k' == k') = true := by
          rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : k' = k')]
          rfl
        refine BPair.add_congr (ite_congr_prop _ (fun _ => faceInd_34 L a k k' s a k' s' h12 h34 (h56z k')))
          (ite_congr_prop _ (fun hpos => ?_))
        exact BPair.oneValue_trans (swap_congr (faceInd_34 L a k k' _ a k' s' h12 h34 (h56z k')))
          (hP _ hpos rfl)
    have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a k' s').swap else BPair.unit)
        + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a k' s' else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ y, (decide (a < y) && decide (y < k)) = true →
          ∀ c, (faceInd L (a, y, k, c) a k' s').oneValue BPair.unit := fun y hg c =>
        faceInd_unit L a y k c a k' s'
          (by rw [eqBeqOf (rfl : a = a), Bool.true_and]
              exact neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true (andSplitB hg).2) hkk')))
          h12 (by rw [neBeqOf (fun h => Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).1) h.symm),
            Bool.false_and])
      exact piece_unit d _ _ _ _ _ (fun y hg => swap_congr (hf y hg s)) (fun y hg => hf y hg _)
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr hz (BPair.add_congr hy hx))) ?_
    delta linkInd
    rw [eqBeqOf (rfl : a = a), neBeqOf nk'a, neBeqOf (Nat.ne_of_lt hak), neBeqOf nk'k]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    rw [beqSymm s s', beqSymm (stepAt L k s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (BPair.add_congr
        (absorb_pair _ _ _ (guard_of_beq L k' s s' hck')
          (guard_of_beq_step L k' k s s' hck nk'k hck') _ _)
        (absorb_pair_prop _ _ _ (occ_of_step_beq L k' s s' hck')
          (occ_of_step_beq_step L k' k s s' hck nk'k hck') _ _))
      (BPair.oneValue_refl _))) ?_
    exact shape2 _ _ _ _
  | inr hge =>
    have hk'k : k' < k := Nat.lt_of_le_of_ne hge hkk
    have hz : (bsum (fun z => if decide (k < z) then
        (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a k' s' else BPair.unit)
        + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a k' s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ z, decide (k < z) = true →
          ∀ c, (faceInd L (a, k, z, c) a k' s').oneValue BPair.unit := fun z hg c =>
        faceInd_unit L a k z c a k' s' h12
          (by rw [eqBeqOf (rfl : a = a), Bool.true_and]
              exact neBeqOf (fun h =>
                Nat.ne_of_lt (Nat.lt_trans hk'k (of_decide_eq_true hg)) h.symm))
          (h56z z)
      exact piece_unit d _ _ _ _ _ (fun z hg => hf z hg s) (fun z hg => swap_congr (hf z hg _))
    have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a k' s').swap else BPair.unit)
        + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a k' s' else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L k' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L k s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L k' s then
          (if stepAt L k' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L k' s' == stepAt L k s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ k' d hkd' (fun y _ hyk' => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun hg => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
        have hay : a < y := of_decide_eq_true (andSplitB hg).1
        have hf : ∀ c, (faceInd L (a, y, k, c) a k' s').oneValue BPair.unit := fun c =>
          faceInd_unit L a y k c a k' s'
            (by rw [eqBeqOf (rfl : a = a), Bool.true_and]; exact neBeqOf hyk')
            h12 (by rw [neBeqOf (fun h => Nat.ne_of_lt hay h.symm), Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hak', decide_eq_true hk'k, Bool.and_true, iteB_true]
        have h12' : (a == a && k' == k') = true := by
          rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : k' = k')]
          rfl
        have h56' : (k' == a && k == k') = false := by
          rw [neBeqOf nk'a, Bool.false_and]
        refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
        · refine BPair.oneValue_trans (swap_congr (faceInd_12 L a k' k s a k' s' h12' h12 h56')) ?_
          rw [swap_pair, BPair.swap_swap]
          exact BPair.oneValue_refl _
        · refine BPair.oneValue_trans (faceInd_12 L a k' k _ a k' s' h12' h12 h56') ?_
          rw [beq_stepBack L k' s s' hpos, beq_step_stepBack L k' k s s' hpos]
          exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr hz (BPair.add_congr hy hx))) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.add_unit _)
        (BPair.oneValue_symm (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit BPair.unit))
          (BPair.add_unit _)))))) ?_
    delta linkInd
    rw [eqBeqOf (rfl : a = a), neBeqOf nk'a, neBeqOf (Nat.ne_of_lt hak), neBeqOf nk'k]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    rw [beqSymm s s', beqSymm (stepAt L k s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (BPair.add_congr
        (absorb_pair _ _ _ (guard_of_beq L k' s s' hck')
          (guard_of_beq_step L k' k s s' hck nk'k hck') _ _)
        (absorb_pair_prop _ _ _ (occ_of_step_beq L k' s s' hck')
          (occ_of_step_beq_step L k' k s s' hck nk'k hck') _ _))
      (BPair.oneValue_refl _))) ?_
    exact shape2 _ _ _ _

/-- The plaquette-pair shape at two plaquettes sharing the first's
higher direction as the second's lower. -/
private theorem shape3 (A B C D : Bool) :
    ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + (((if C then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if D then (BPair.ofNat 1).swap else BPair.unit)
            + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
      + (((if A then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if B then (BPair.ofNat 1).swap else BPair.unit)
            + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap + BPair.unit)))
      + (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
        + ((if B then (BPair.ofNat 1).swap else BPair.unit) + (if D then BPair.ofNat 1 else BPair.unit))
        + (BPair.unit + BPair.unit))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The plaquette-pair shape at two plaquettes sharing the first's
lower direction as the second's higher. -/
private theorem shape4 (A B C D : Bool) :
    ((BPair.unit + ((if B then BPair.ofNat 1 else BPair.unit)
        + (BPair.unit + ((if A then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit))))
        * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + ((BPair.unit + ((if D then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if C then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit))))
          * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
        + BPair.unit)))
      + (BPair.unit + (BPair.unit
        + (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
        + ((if B then (BPair.ofNat 1).swap else BPair.unit) + (if D then BPair.ofNat 1 else BPair.unit)))))).oneValue
      BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The plaquette-pair shape at two plaquettes sharing the higher
direction at distinct planes. -/
private theorem shape5 (A B C D : Bool) :
    ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + ((BPair.unit + ((if D then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if C then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit))))
          * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
      + ((BPair.unit + ((if B then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if A then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit))))
          * (BPair.ofNat 1).swap + BPair.unit)))
      + (BPair.unit
        + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if C then BPair.ofNat 1 else BPair.unit))
        + ((if B then BPair.ofNat 1 else BPair.unit)
          + (if D then (BPair.ofNat 1).swap else BPair.unit))))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The plaquette-pair shape at two plaquettes of disjoint planes. -/
private theorem shape6 :
    ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
        + BPair.unit)))
      + (BPair.unit + (BPair.unit + BPair.unit))).oneValue BPair.unit := by
  decide

set_option maxHeartbeats 800000 in
/-- The third case: two plaquettes, the second's lower direction the
first's higher, the incidence's reads at the shared link against the
one cube's two face reads. -/
private theorem hodge_case3 (d L a k s k' s' : Nat) (hak : a < k) (hca : coordAt L a s < L)
    (hkk' : k < k') (hkd' : k' < d) (hck' : coordAt L k' s' < L) :
    (linkInd L (k, k', s') a s * BPair.ofNat 1
      + (linkInd L (k, k', s') k (stepAt L a s) * BPair.ofNat 1
      + (linkInd L (k, k', s') a (stepAt L k s) * (BPair.ofNat 1).swap
      + (linkInd L (k, k', s') k s * (BPair.ofNat 1).swap + BPair.unit)))
      + (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) k k' s' else BPair.unit)
          + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) k k' s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) k k' s').swap else BPair.unit)
          + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) k k' s' else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) k k' s' else BPair.unit)
          + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) k k' s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)))).oneValue BPair.unit := by
  have nak : ¬ a = k := Nat.ne_of_lt hak
  have nk'a : ¬ k' = a := fun h => Nat.ne_of_lt (Nat.lt_trans hak hkk') h.symm
  have nk'k : ¬ k' = k := fun h => Nat.ne_of_lt hkk' h.symm
  have hak_f : (a == k) = false := neBeqOf nak
  have hz : (bsum (fun z => if decide (k < z) then
      (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) k k' s' else BPair.unit)
      + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) k k' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L k' s < L) then
        (if s == s' then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L k' s then
        (if stepAt L k' s' == s then (BPair.ofNat 1).swap else BPair.unit)
          + (if stepAt L k' s' == stepAt L a s then BPair.ofNat 1 else BPair.unit)
        else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ k' d hkd' (fun z _ hzk' => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ c, (faceInd L (a, k, z, c) k k' s').oneValue BPair.unit := fun c =>
        faceInd_unit L a k z c k k' s' (by rw [hak_f, Bool.false_and]) (by rw [hak_f, Bool.false_and])
          (by rw [eqBeqOf (rfl : k = k), Bool.true_and]; exact neBeqOf hzk')
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s)) (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true hkk', iteB_true]
      have h56 : (k == k && k' == k') = true := by
        rw [eqBeqOf (rfl : k = k), eqBeqOf (rfl : k' = k')]
        rfl
      have h12 : (a == k && k == k') = false := by rw [hak_f, Bool.false_and]
      have h34 : (a == k && k' == k') = false := by rw [hak_f, Bool.false_and]
      refine BPair.add_congr (ite_congr_prop _ (fun _ => faceInd_56 L a k k' s k k' s' h12 h34 h56))
        (ite_congr_prop _ (fun hpos => ?_))
      refine BPair.oneValue_trans (swap_congr (faceInd_56 L a k k' _ k k' s' h12 h34 h56)) ?_
      rw [swap_pair, BPair.swap_swap, beq_stepBack L k' s s' hpos, beq_step_stepBack L k' a s s' hpos]
      exact BPair.oneValue_refl _
  have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
      (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) k k' s').swap else BPair.unit)
      + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) k k' s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun y hg => ?_) (fun y hg => ?_)
    · have hyk : y < k := of_decide_eq_true (andSplitB hg).2
      exact swap_congr (faceInd_unit L a y k s k k' s' (by rw [hak_f, Bool.false_and])
        (by rw [hak_f, Bool.false_and]) (by rw [neBeqOf (Nat.ne_of_lt hyk), Bool.false_and]))
    · have hyk : y < k := of_decide_eq_true (andSplitB hg).2
      exact faceInd_unit L a y k _ k k' s' (by rw [hak_f, Bool.false_and])
        (by rw [hak_f, Bool.false_and]) (by rw [neBeqOf (Nat.ne_of_lt hyk), Bool.false_and])
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) k k' s' else BPair.unit)
      + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) k k' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun x hg => ?_) (fun x hg => ?_)
    · have hxk : x < k := Nat.lt_trans (of_decide_eq_true hg) hak
      exact faceInd_unit L x a k s k k' s' (by rw [neBeqOf (Nat.ne_of_lt hxk), Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt hxk), Bool.false_and]) (by rw [hak_f, Bool.false_and])
    · have hxk : x < k := Nat.lt_trans (of_decide_eq_true hg) hak
      exact swap_congr (faceInd_unit L x a k _ k k' s' (by rw [neBeqOf (Nat.ne_of_lt hxk), Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt hxk), Bool.false_and]) (by rw [hak_f, Bool.false_and]))
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr hz (BPair.add_congr hy hx))) ?_
  delta linkInd
  rw [eqBeqOf (rfl : k = k), neBeqOf nk'a, neBeqOf (fun h => nak h.symm), neBeqOf nk'k]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  rw [beqSymm s s', beqSymm (stepAt L a s) s']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
    (BPair.add_congr
      (absorb_pair _ _ _ (guard_of_beq L k' s s' hck')
        (guard_of_beq_step L k' a s s' hca nk'a hck') _ _)
      (absorb_pair_prop _ _ _ (occ_of_step_beq L k' s s' hck')
        (occ_of_step_beq_step L k' a s s' hca nk'a hck') _ _))
    (BPair.oneValue_refl _))) ?_
  exact shape3 _ _ _ _

set_option maxHeartbeats 800000 in
/-- The fourth case: two plaquettes, the second's higher direction the
first's lower, the incidence's reads at the shared link against the
one cube's two face reads. -/
private theorem hodge_case4 (d L a k s a' s' : Nat) (hak : a < k) (hkd : k < d)
    (hck : coordAt L k s < L) (ha'a : a' < a) (hca' : coordAt L a' s' < L) :
    (linkInd L (a', a, s') a s * BPair.ofNat 1
      + (linkInd L (a', a, s') k (stepAt L a s) * BPair.ofNat 1
      + (linkInd L (a', a, s') a (stepAt L k s) * (BPair.ofNat 1).swap
      + (linkInd L (a', a, s') k s * (BPair.ofNat 1).swap + BPair.unit)))
      + (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a' a s' else BPair.unit)
          + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a' a s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' a s').swap else BPair.unit)
          + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' a s' else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' a s' else BPair.unit)
          + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' a s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)))).oneValue BPair.unit := by
  have ha'd : a' < d := Nat.lt_trans ha'a (Nat.lt_trans hak hkd)
  have naa' : ¬ a = a' := fun h => Nat.ne_of_lt ha'a h.symm
  have nka' : ¬ k = a' := fun h => Nat.ne_of_lt (Nat.lt_trans ha'a hak) h.symm
  have na'k : ¬ a' = k := Nat.ne_of_lt (Nat.lt_trans ha'a hak)
  have haa'_f : (a == a') = false := neBeqOf naa'
  have hka'_f : (k == a') = false := neBeqOf nka'
  have hz : (bsum (fun z => if decide (k < z) then
      (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a' a s' else BPair.unit)
      + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a' a s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun z _ => ?_) (fun z _ => ?_)
    · exact faceInd_unit L a k z s a' a s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hka'_f, Bool.false_and])
    · exact swap_congr (faceInd_unit L a k z _ a' a s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hka'_f, Bool.false_and]))
  have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
      (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' a s').swap else BPair.unit)
      + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' a s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun y hg => ?_) (fun y hg => ?_)
    · have hay : a' < y := Nat.lt_trans ha'a (of_decide_eq_true (andSplitB hg).1)
      exact swap_congr (faceInd_unit L a y k s a' a s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and])
        (by rw [neBeqOf (fun h => Nat.ne_of_lt hay h.symm), Bool.false_and]))
    · have hay : a' < y := Nat.lt_trans ha'a (of_decide_eq_true (andSplitB hg).1)
      exact faceInd_unit L a y k _ a' a s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and])
        (by rw [neBeqOf (fun h => Nat.ne_of_lt hay h.symm), Bool.false_and])
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' a s' else BPair.unit)
      + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' a s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L a' s < L) then
        (if s == s' then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L k s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L a' s then
        (if stepAt L a' s' == s then (BPair.ofNat 1).swap else BPair.unit)
          + (if stepAt L a' s' == stepAt L k s then BPair.ofNat 1 else BPair.unit)
        else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ a' d ha'd (fun x _ hxa' => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ c, (faceInd L (x, a, k, c) a' a s').oneValue BPair.unit := fun c =>
        faceInd_unit L x a k c a' a s' (by rw [neBeqOf hxa', Bool.false_and])
          (by rw [neBeqOf hxa', Bool.false_and]) (by rw [haa'_f, Bool.false_and])
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s)) (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true ha'a, iteB_true]
      have h12 : (a' == a' && a == a) = true := by
        rw [eqBeqOf (rfl : a' = a'), eqBeqOf (rfl : a = a)]
        rfl
      have h34 : (a' == a' && k == a) = false := by
        rw [neBeqOf (fun h => Nat.ne_of_lt hak h.symm), Bool.and_false]
      have h56 : (a == a' && k == a) = false := by rw [haa'_f, Bool.false_and]
      refine BPair.add_congr (ite_congr_prop _ (fun _ => faceInd_12 L a' a k s a' a s' h12 h34 h56))
        (ite_congr_prop _ (fun hpos => ?_))
      refine BPair.oneValue_trans (swap_congr (faceInd_12 L a' a k _ a' a s' h12 h34 h56)) ?_
      rw [swap_pair, BPair.swap_swap, beq_stepBack L a' s s' hpos, beq_step_stepBack L a' k s s' hpos]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr hz (BPair.add_congr hy hx))) ?_
  delta linkInd
  rw [eqBeqOf (rfl : a = a), neBeqOf (fun h => naa' h.symm), neBeqOf (Nat.ne_of_lt hak),
    neBeqOf na'k]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  rw [beqSymm s s', beqSymm (stepAt L k s) s']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
    (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (absorb_pair _ _ _ (guard_of_beq L a' s s' hca')
        (guard_of_beq_step L a' k s s' hck na'k hca') _ _)
      (absorb_pair_prop _ _ _ (occ_of_step_beq L a' s s' hca')
        (occ_of_step_beq_step L a' k s s' hck na'k hca') _ _))))) ?_
  exact shape4 _ _ _ _

set_option maxHeartbeats 800000 in
/-- The fifth case: two plaquettes sharing the higher direction at
distinct planes, the incidence's reads at the shared link against the
one cube's two face reads. -/
private theorem hodge_case5 (d L a k s a' s' : Nat) (hak : a < k) (hkd : k < d)
    (hca : coordAt L a s < L) (ha'k : a' < k) (hca' : coordAt L a' s' < L) (haa : ¬ a' = a) :
    (linkInd L (a', k, s') a s * BPair.ofNat 1
      + (linkInd L (a', k, s') k (stepAt L a s) * BPair.ofNat 1
      + (linkInd L (a', k, s') a (stepAt L k s) * (BPair.ofNat 1).swap
      + (linkInd L (a', k, s') k s * (BPair.ofNat 1).swap + BPair.unit)))
      + (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a' k s' else BPair.unit)
          + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a' k s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' k s').swap else BPair.unit)
          + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' k s' else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' k s' else BPair.unit)
          + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' k s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)))).oneValue BPair.unit := by
  have ha'd : a' < d := Nat.lt_trans ha'k hkd
  have nka' : ¬ k = a' := fun h => Nat.ne_of_lt ha'k h.symm
  have na'a : ¬ a' = a := haa
  have haa'_f : (a == a') = false := neBeqOf (fun h => haa h.symm)
  have hka'_f : (k == a') = false := neBeqOf nka'
  have hakb_f : (a == k) = false := neBeqOf (Nat.ne_of_lt hak)
  have hz : (bsum (fun z => if decide (k < z) then
      (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a' k s' else BPair.unit)
      + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a' k s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun z _ => ?_) (fun z _ => ?_)
    · exact faceInd_unit L a k z s a' k s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hka'_f, Bool.false_and])
    · exact swap_congr (faceInd_unit L a k z _ a' k s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hka'_f, Bool.false_and]))
  -- the shared-direction piece at the corner reads
  have hP : ∀ c, 0 < coordAt L a' s → c = s - (L + 1) ^ a' →
      ((if c == s' then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L a c == s' then (BPair.ofNat 1).swap else BPair.unit)).oneValue
      ((if stepAt L a' s' == s then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L a' s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)) := by
    intro c hpos hc
    rw [hc, beq_stepBack L a' s s' hpos, beq_step_stepBack L a' a s s' hpos]
    exact BPair.oneValue_refl _
  have hmain : ∀ Pz Py Px : BPair, Pz.oneValue BPair.unit →
      (Py + Px).oneValue
        ((if decide (coordAt L a' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L a' s then
          (if stepAt L a' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L a' s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) →
      (linkInd L (a', k, s') a s * BPair.ofNat 1
        + (linkInd L (a', k, s') k (stepAt L a s) * BPair.ofNat 1
        + (linkInd L (a', k, s') a (stepAt L k s) * (BPair.ofNat 1).swap
        + (linkInd L (a', k, s') k s * (BPair.ofNat 1).swap + BPair.unit)))
        + (Pz + (Py + Px))).oneValue BPair.unit := by
    intro Pz Py Px hPz hPyx
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (BPair.add_congr hPz hPyx)) ?_
    delta linkInd
    rw [eqBeqOf (rfl : k = k), neBeqOf (fun h => na'a h), neBeqOf (fun h => Nat.ne_of_lt hak h.symm),
      neBeqOf (Nat.ne_of_lt ha'k)]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    rw [beqSymm s s', beqSymm (stepAt L a s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (BPair.oneValue_refl _) (BPair.add_congr
        (absorb_pair _ _ _ (guard_of_beq L a' s s' hca')
          (guard_of_beq_step L a' a s s' hca na'a hca') _ _)
        (absorb_pair_prop _ _ _ (occ_of_step_beq L a' s s' hca')
          (occ_of_step_beq_step L a' a s s' hca na'a hca') _ _)))) ?_
    exact shape5 _ _ _ _
  cases Nat.lt_or_ge a' a with
  | inl ha'a =>
    have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' k s').swap else BPair.unit)
        + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' k s' else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      refine piece_unit d _ _ _ _ _ (fun y hg => ?_) (fun y hg => ?_)
      · have hay : a' < y := Nat.lt_trans ha'a (of_decide_eq_true (andSplitB hg).1)
        exact swap_congr (faceInd_unit L a y k s a' k s' (by rw [haa'_f, Bool.false_and])
          (by rw [haa'_f, Bool.false_and])
          (by rw [neBeqOf (fun h => Nat.ne_of_lt hay h.symm), Bool.false_and]))
      · have hay : a' < y := Nat.lt_trans ha'a (of_decide_eq_true (andSplitB hg).1)
        exact faceInd_unit L a y k _ a' k s' (by rw [haa'_f, Bool.false_and])
          (by rw [haa'_f, Bool.false_and])
          (by rw [neBeqOf (fun h => Nat.ne_of_lt hay h.symm), Bool.false_and])
    have hx : (bsum (fun x => if decide (x < a) then
        (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' k s' else BPair.unit)
        + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' k s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L a' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L a' s then
          (if stepAt L a' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L a' s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ a' d ha'd (fun x _ hxa' => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ c, (faceInd L (x, a, k, c) a' k s').oneValue BPair.unit := fun c =>
          faceInd_unit L x a k c a' k s' (by rw [neBeqOf hxa', Bool.false_and])
            (by rw [neBeqOf hxa', Bool.false_and]) (by rw [haa'_f, Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s)) (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true ha'a, iteB_true]
        have h12 : (a' == a' && a == k) = false := by rw [hakb_f, Bool.and_false]
        have h34 : (a' == a' && k == k) = true := by
          rw [eqBeqOf (rfl : a' = a'), eqBeqOf (rfl : k = k)]
          rfl
        have h56 : (a == a' && k == k) = false := by rw [haa'_f, Bool.false_and]
        refine BPair.add_congr (ite_congr_prop _ (fun _ => faceInd_34 L a' a k s a' k s' h12 h34 h56))
          (ite_congr_prop _ (fun hpos => ?_))
        refine BPair.oneValue_trans (swap_congr (faceInd_34 L a' a k _ a' k s' h12 h34 h56)) ?_
        rw [swap_pair, BPair.swap_swap]
        exact hP _ hpos rfl
    refine hmain _ _ _ hz ?_
    exact BPair.oneValue_trans (BPair.add_congr hy hx) (BPair.unit_add _)
  | inr hge =>
    have haa' : a < a' := Nat.lt_of_le_of_ne hge (fun h => haa h.symm)
    have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
        (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' k s').swap else BPair.unit)
        + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' k s' else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L a' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L a' s then
          (if stepAt L a' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L a' s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ a' d ha'd (fun y _ hya' => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ c, (faceInd L (a, y, k, c) a' k s').oneValue BPair.unit := fun c =>
          faceInd_unit L a y k c a' k s' (by rw [haa'_f, Bool.false_and])
            (by rw [haa'_f, Bool.false_and]) (by rw [neBeqOf hya', Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true haa', decide_eq_true ha'k, Bool.and_true, iteB_true]
        have h12 : (a == a' && a' == k) = false := by rw [haa'_f, Bool.false_and]
        have h34 : (a == a' && k == k) = false := by rw [haa'_f, Bool.false_and]
        have h56 : (a' == a' && k == k) = true := by
          rw [eqBeqOf (rfl : a' = a'), eqBeqOf (rfl : k = k)]
          rfl
        refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
        · refine BPair.oneValue_trans (swap_congr (faceInd_56 L a a' k s a' k s' h12 h34 h56)) ?_
          rw [swap_pair, BPair.swap_swap]
          exact BPair.oneValue_refl _
        · exact BPair.oneValue_trans (faceInd_56 L a a' k _ a' k s' h12 h34 h56) (hP _ hpos rfl)
    have hx : (bsum (fun x => if decide (x < a) then
        (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' k s' else BPair.unit)
        + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' k s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      refine piece_unit d _ _ _ _ _ (fun x hg => ?_) (fun x hg => ?_)
      · have hxa' : x < a' := Nat.lt_trans (of_decide_eq_true hg) haa'
        exact faceInd_unit L x a k s a' k s' (by rw [neBeqOf (Nat.ne_of_lt hxa'), Bool.false_and])
          (by rw [neBeqOf (Nat.ne_of_lt hxa'), Bool.false_and]) (by rw [haa'_f, Bool.false_and])
      · have hxa' : x < a' := Nat.lt_trans (of_decide_eq_true hg) haa'
        exact swap_congr (faceInd_unit L x a k _ a' k s'
          (by rw [neBeqOf (Nat.ne_of_lt hxa'), Bool.false_and])
          (by rw [neBeqOf (Nat.ne_of_lt hxa'), Bool.false_and]) (by rw [haa'_f, Bool.false_and]))
    refine hmain _ _ _ hz ?_
    exact BPair.oneValue_trans (BPair.add_congr hy hx) (BPair.add_unit _)

set_option maxHeartbeats 800000 in
/-- The sixth case: two plaquettes of disjoint planes, every read the
unit. -/
private theorem hodge_case6 (d L a k s a' k' s' : Nat)
    (haa : ¬ a' = a) (hkk : ¬ k' = k) (hak2 : ¬ a' = k) (hka : ¬ k' = a) :
    (linkInd L (a', k', s') a s * BPair.ofNat 1
      + (linkInd L (a', k', s') k (stepAt L a s) * BPair.ofNat 1
      + (linkInd L (a', k', s') a (stepAt L k s) * (BPair.ofNat 1).swap
      + (linkInd L (a', k', s') k s * (BPair.ofNat 1).swap + BPair.unit)))
      + (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a' k' s' else BPair.unit)
          + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a' k' s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' k' s').swap else BPair.unit)
          + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' k' s' else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' k' s' else BPair.unit)
          + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' k' s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)))).oneValue BPair.unit := by
  have haa'_f : (a == a') = false := neBeqOf (fun h => haa h.symm)
  have hka'_f : (k == a') = false := neBeqOf (fun h => hak2 h.symm)
  have hkk'_f : (k == k') = false := neBeqOf (fun h => hkk h.symm)
  have hak'_f : (a == k') = false := neBeqOf (fun h => hka h.symm)
  have hz : (bsum (fun z => if decide (k < z) then
      (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a' k' s' else BPair.unit)
      + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a' k' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun z _ => ?_) (fun z _ => ?_)
    · exact faceInd_unit L a k z s a' k' s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hka'_f, Bool.false_and])
    · exact swap_congr (faceInd_unit L a k z _ a' k' s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hka'_f, Bool.false_and]))
  have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
      (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a' k' s').swap else BPair.unit)
      + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a' k' s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun y _ => ?_) (fun y _ => ?_)
    · exact swap_congr (faceInd_unit L a y k s a' k' s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hkk'_f, Bool.and_false]))
    · exact faceInd_unit L a y k _ a' k' s' (by rw [haa'_f, Bool.false_and])
        (by rw [haa'_f, Bool.false_and]) (by rw [hkk'_f, Bool.and_false])
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a' k' s' else BPair.unit)
      + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a' k' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine piece_unit d _ _ _ _ _ (fun x _ => ?_) (fun x _ => ?_)
    · exact faceInd_unit L x a k s a' k' s' (by rw [hak'_f, Bool.and_false])
        (by rw [hkk'_f, Bool.and_false]) (by rw [haa'_f, Bool.false_and])
    · exact swap_congr (faceInd_unit L x a k _ a' k' s' (by rw [hak'_f, Bool.and_false])
        (by rw [hkk'_f, Bool.and_false]) (by rw [haa'_f, Bool.false_and]))
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr hz (BPair.add_congr hy hx))) ?_
  delta linkInd
  rw [neBeqOf haa, neBeqOf hka, neBeqOf hak2, neBeqOf hkk]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  exact shape6

/-- A guarded read's congruence off its guard. -/
private theorem ite_else_congr {A A' : BPair} (c : Bool) (h : c = false → A.oneValue A') :
    (if c then BPair.unit else A).oneValue (if c then BPair.unit else A') := by
  cases hc : c with
  | true => exact BPair.oneValue_refl _
  | false => exact h hc

/-- The three direction pieces, beyond the plane's higher direction,
between the plane's directions and below the lower, fold to the fold
over the directions off the plane's two. -/
private theorem bsum_three_pieces (F : Nat → BPair) (a k d : Nat) (hak : a < k) :
    (bsum (fun z => if decide (k < z) then F z else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then F y else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then F x else BPair.unit) (List.range d))).oneValue
      (bsum (fun j => if j == a || j == k then BPair.unit else F j) (List.range d)) := by
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun j =>
    (if decide (k < j) then F j else BPair.unit)
    + ((if decide (a < j) && decide (j < k) then F j else BPair.unit)
    + (if decide (j < a) then F j else BPair.unit))) d (fun j _ => ?_)) ?_
  · cases Nat.lt_or_ge j a with
    | inl hja =>
      rw [neBeqOf (Nat.ne_of_lt hja), neBeqOf (Nat.ne_of_lt (Nat.lt_trans hja hak)), Bool.or_false,
        iteB_false_else, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hja hak))),
        decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hja)), Bool.false_and, decide_eq_true hja,
        iteB_true]
      repeat rw [iteB_false]
      exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))
    | inr hge =>
      cases Nat.lt_or_ge a j with
      | inr hge' =>
        have hja : j = a := Nat.le_antisymm hge' hge
        rw [hja, eqBeqOf (rfl : a = a), Bool.true_or, iteB_true_else,
          decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hak)), decide_eq_false (Nat.lt_irrefl a),
          Bool.false_and]
        repeat rw [iteB_false]
        exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))
      | inl haj =>
        cases Nat.lt_or_ge j k with
        | inl hjk =>
          rw [neBeqOf (fun h => Nat.ne_of_lt haj h.symm), neBeqOf (Nat.ne_of_lt hjk), Bool.or_false,
            iteB_false_else, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hjk)),
            decide_eq_true haj, decide_eq_true hjk,
            decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt haj)), Bool.true_and, iteB_true]
          repeat rw [iteB_false]
          exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) (BPair.add_unit _))
        | inr hge'' =>
          cases Nat.lt_or_ge k j with
          | inr hge3 =>
            have hjk : j = k := Nat.le_antisymm hge3 hge''
            rw [hjk, eqBeqOf (rfl : k = k), Bool.or_true, iteB_true_else,
              decide_eq_false (Nat.lt_irrefl k), decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hak)),
              Bool.and_false]
            repeat rw [iteB_false]
            exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))
          | inl hkj =>
            rw [neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hak hkj) h.symm),
              neBeqOf (fun h => Nat.ne_of_lt hkj h.symm), Bool.or_false, iteB_false_else,
              decide_eq_true hkj, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hkj)),
              Bool.and_false, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hak hkj))),
              iteB_true]
            repeat rw [iteB_false]
            exact BPair.oneValue_symm (BPair.oneValue_trans
              (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)) (BPair.add_unit _))
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) (foldB_add _ _ _)

/-- The off-plane direction's shape: the piece's two guarded pairs
against the differences' Gram's four reads. -/
private theorem shapeF (g1 g2 A B C : Bool) :
    (((if g1 && A then BPair.ofNat 1 else BPair.unit)
        + (if g1 && B then (BPair.ofNat 1).swap else BPair.unit))
      + ((if g2 && C then (BPair.ofNat 1).swap else BPair.unit)
        + (if g2 && A then BPair.ofNat 1 else BPair.unit))).oneValue
      ((if g2 && A then BPair.ofNat 1 else BPair.unit)
        + ((if g1 && B then (BPair.ofNat 1).swap else BPair.unit)
        + ((if g2 && C then (BPair.ofNat 1).swap else BPair.unit)
        + (if g1 && A then BPair.ofNat 1 else BPair.unit)))) := by
  cases g1 <;> cases g2 <;> cases A <;> cases B <;> cases C <;> decide

/-- The one-plane shape: the incidence's four reads at the plane's own
two directions against the differences' Grams' reads there. -/
private theorem shape1 (A B C D E : Bool) :
    (((if A then BPair.ofNat 1 else BPair.unit)
        + (BPair.unit + ((if B then (BPair.ofNat 1).swap else BPair.unit)
          + (BPair.unit + BPair.unit)))) * BPair.ofNat 1
      + ((BPair.unit + ((if A then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if C then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit))))
          * BPair.ofNat 1
      + (((if D then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if A then (BPair.ofNat 1).swap else BPair.unit)
            + (BPair.unit + BPair.unit)))) * (BPair.ofNat 1).swap
      + ((BPair.unit + ((if E then BPair.ofNat 1 else BPair.unit)
          + (BPair.unit + ((if A then (BPair.ofNat 1).swap else BPair.unit) + BPair.unit))))
          * (BPair.ofNat 1).swap + BPair.unit)))).oneValue
      (((if A then BPair.ofNat 1 else BPair.unit)
        + ((if C then (BPair.ofNat 1).swap else BPair.unit)
        + ((if E then (BPair.ofNat 1).swap else BPair.unit)
        + (if A then BPair.ofNat 1 else BPair.unit))))
      + ((if A then BPair.ofNat 1 else BPair.unit)
        + ((if D then (BPair.ofNat 1).swap else BPair.unit)
        + ((if B then (BPair.ofNat 1).swap else BPair.unit)
        + (if A then BPair.ofNat 1 else BPair.unit))))) := by
  cases A <;> cases B <;> cases C <;> cases D <;> cases E <;> decide

set_option maxHeartbeats 1600000 in
/-- The first case: two plaquettes of one plane type, the diagonal at
four joined to the cubes holding the plaquette and the consecutive
keys at the balance partner of one. -/
private theorem hodge_case1 (d L a k s s' : Nat) (hak : a < k) (hkd : k < d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (hca' : coordAt L a s' < L)
    (hck' : coordAt L k s' < L) :
    (linkInd L (a, k, s') a s * BPair.ofNat 1
      + (linkInd L (a, k, s') k (stepAt L a s) * BPair.ofNat 1
      + (linkInd L (a, k, s') a (stepAt L k s) * (BPair.ofNat 1).swap
      + (linkInd L (a, k, s') k s * (BPair.ofNat 1).swap + BPair.unit)))
      + (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a k s' else BPair.unit)
          + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a k s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a k s').swap else BPair.unit)
          + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a k s' else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a k s' else BPair.unit)
          + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a k s').swap
            else BPair.unit)
        else BPair.unit) (List.range d)))).oneValue
      (bsum (fun j =>
        (if ((j == a || j == k) || decide (0 < coordAt L j s)) && s' == s
          then BPair.ofNat 1 else BPair.unit)
        + ((if decide (coordAt L j s < L) && s' == stepAt L j s
          then (BPair.ofNat 1).swap else BPair.unit)
        + ((if decide (0 < coordAt L j s) && stepAt L j s' == s
          then (BPair.ofNat 1).swap else BPair.unit)
        + (if decide (coordAt L j s < L) && s' == s then BPair.ofNat 1 else BPair.unit))))
        (List.range d)) := by
  have had : a < d := Nat.lt_trans hak hkd
  have nka : ¬ k = a := fun h => Nat.ne_of_lt hak h.symm
  have nak : ¬ a = k := Nat.ne_of_lt hak
  have h12t : (a == a && k == k) = true := by
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k)]
    rfl
  -- the pieces' common summand
  let F : Nat → BPair := fun j =>
    (if decide (coordAt L j s < L) then
      (if s' == s then BPair.ofNat 1 else BPair.unit)
        + (if s' == stepAt L j s then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
    + (if 0 < coordAt L j s then
      (if stepAt L j s' == s then (BPair.ofNat 1).swap else BPair.unit)
        + (if s' == s then BPair.ofNat 1 else BPair.unit) else BPair.unit)
  have hback : ∀ j, 0 < coordAt L j s →
      ((if s - (L + 1) ^ j == s' then (BPair.ofNat 1).swap else BPair.unit)
        + (if stepAt L j (s - (L + 1) ^ j) == s' then BPair.ofNat 1 else BPair.unit)).oneValue
      ((if stepAt L j s' == s then (BPair.ofNat 1).swap else BPair.unit)
        + (if s' == s then BPair.ofNat 1 else BPair.unit)) := by
    intro j hpos
    rw [beq_stepBack L j s s' hpos, beq_step_stepBack L j j s s' hpos, beq_step]
    exact BPair.oneValue_refl _
  have hz : (bsum (fun z => if decide (k < z) then
      (if decide (coordAt L z s < L) then faceInd L (a, k, z, s) a k s' else BPair.unit)
      + (if 0 < coordAt L z s then (faceInd L (a, k, z, s - (L + 1) ^ z) a k s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      (bsum (fun z => if decide (k < z) then F z else BPair.unit) (List.range d)) := by
    refine bsum_congr_range_ov _ _ d (fun z _ => ite_congr_prop _ (fun hkz => ?_))
    have hkz' : k < z := of_decide_eq_true hkz
    have h34 : (a == a && z == k) = false := by
      rw [eqBeqOf (rfl : a = a), Bool.true_and]
      exact neBeqOf (fun h => Nat.ne_of_lt hkz' h.symm)
    have h56 : (k == a && z == k) = false := by rw [neBeqOf nka, Bool.false_and]
    refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · refine BPair.oneValue_trans (faceInd_12 L a k z s a k s' h12t h34 h56) ?_
      rw [beqSymm s s', beqSymm (stepAt L z s) s']
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (swap_congr (faceInd_12 L a k z _ a k s' h12t h34 h56)) ?_
      rw [swap_pair, BPair.swap_swap]
      exact hback z hpos
  have hy : (bsum (fun y => if decide (a < y) && decide (y < k) then
      (if decide (coordAt L y s < L) then (faceInd L (a, y, k, s) a k s').swap else BPair.unit)
      + (if 0 < coordAt L y s then faceInd L (a, y, k, s - (L + 1) ^ y) a k s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      (bsum (fun y => if decide (a < y) && decide (y < k) then F y else BPair.unit) (List.range d)) := by
    refine bsum_congr_range_ov _ _ d (fun y _ => ite_congr_prop _ (fun hg => ?_))
    have hay : a < y := of_decide_eq_true (andSplitB hg).1
    have hyk : y < k := of_decide_eq_true (andSplitB hg).2
    have h12 : (a == a && y == k) = false := by
      rw [eqBeqOf (rfl : a = a), Bool.true_and]
      exact neBeqOf (Nat.ne_of_lt hyk)
    have h56 : (y == a && k == k) = false := by
      rw [neBeqOf (fun h => Nat.ne_of_lt hay h.symm), Bool.false_and]
    refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · refine BPair.oneValue_trans (swap_congr (faceInd_34 L a y k s a k s' h12 h12t h56)) ?_
      rw [swap_pair, BPair.swap_swap, beqSymm s s', beqSymm (stepAt L y s) s']
      exact BPair.oneValue_refl _
    · exact BPair.oneValue_trans (faceInd_34 L a y k _ a k s' h12 h12t h56) (hback y hpos)
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then faceInd L (x, a, k, s) a k s' else BPair.unit)
      + (if 0 < coordAt L x s then (faceInd L (x, a, k, s - (L + 1) ^ x) a k s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      (bsum (fun x => if decide (x < a) then F x else BPair.unit) (List.range d)) := by
    refine bsum_congr_range_ov _ _ d (fun x _ => ite_congr_prop _ (fun hg => ?_))
    have hxa : x < a := of_decide_eq_true hg
    have h12 : (x == a && a == k) = false := by rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and]
    have h34 : (x == a && k == k) = false := by rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and]
    refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · refine BPair.oneValue_trans (faceInd_56 L x a k s a k s' h12 h34 h12t) ?_
      rw [beqSymm s s', beqSymm (stepAt L x s) s']
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (swap_congr (faceInd_56 L x a k _ a k s' h12 h34 h12t)) ?_
      rw [swap_pair, BPair.swap_swap]
      exact hback x hpos
  -- the pieces merge over the directions off the plane
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans (BPair.add_congr hz (BPair.add_congr hy hx))
      (bsum_three_pieces F a k d hak))) ?_
  -- the differences' Grams' reads at the plane's two directions and off them
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (bsum_range_pick_two _ a k d had hkd nak))
  refine BPair.oneValue_trans ?_ (BPair.oneValue_of_eq (BPair.add_assoc _ _ _))
  refine BPair.add_congr ?_ (bsum_congr_range_ov _ _ d (fun j _ => ite_else_congr _ (fun hj => ?_)))
  · -- the incidence's reads against the two plane directions' Grams
    delta linkInd
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k), neBeqOf nka, neBeqOf nak, beq_step, beq_step]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    refine BPair.oneValue_trans (shape1 _ _ _ _ _) ?_
    rw [show (a, k, s').snd.snd = s' from rfl, show (a, k, s').fst = a from rfl,
      show (a, k, s').snd.fst = k from rfl]
    repeat rw [Bool.true_or]
    repeat rw [Bool.false_or]
    repeat rw [Bool.true_or]
    rw [decide_eq_true hca, decide_eq_true hck]
    repeat rw [Bool.true_and]
    rw [ite_and_absorb _ _ (fun h => decide_eq_true (occ_of_step_beq L a s s' hca' h)),
      ite_and_absorb _ _ (fun h => decide_eq_true (occ_of_step_beq L k s s' hck' h))]
    exact BPair.oneValue_refl _
  · -- a direction off the plane
    rw [hj, Bool.false_or]
    show ((if decide (coordAt L j s < L) then
        (if s' == s then BPair.ofNat 1 else BPair.unit)
          + (if s' == stepAt L j s then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L j s then
        (if stepAt L j s' == s then (BPair.ofNat 1).swap else BPair.unit)
          + (if s' == s then BPair.ofNat 1 else BPair.unit) else BPair.unit)).oneValue _
    rw [← ite_decide (0 < coordAt L j s)]
    refine BPair.oneValue_trans (BPair.add_congr (ite_add_unit _ _ _) (ite_add_unit _ _ _)) ?_
    rw [ite_ite_and, ite_ite_and, ite_ite_and, ite_ite_and]
    exact shapeF _ _ _ _ _

/-- The Hodge identity entry by entry: the Gram joined to the cubes'
boundaries' Gram reads the Hodge fold's matrix at every plaquette
pair, the six pair classes each at its own read. -/
theorem hodge_entry (d L p q : Nat) (hp : p < plaqCount d L) (hq : q < plaqCount d L) :
    (getAt BPair.unit (getAt [] (matAdd (gram d L) (cubeGram d L)) p) q).oneValue
      (getAt BPair.unit (getAt [] (hodgeMat d L) p) q) := by
  rw [entry_matAdd (gram d L) (cubeGram d L) (plaqCount d L) (gram_rows d L) (cubeGram_rows d L)
    p q (by rw [gram_length]; exact hp) (by rw [cubeGram_length]; exact hp) hq]
  refine BPair.oneValue_trans
    (BPair.add_congr (gram_entry d L p q hp hq) (cubeGram_entry d L p q hp hq)) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (hodgeMat_entry_plane d L p q hp hq))
  have hpl := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
  have hql := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) q hq)
  have hpk := plaqKey_of_getAt d L p hp
  have hqk := plaqKey_of_getAt d L q hq
  generalize hP : getAt (0, 0, 0) (plaqList d L) p = P at hpl hpk ⊢
  generalize hQ : getAt (0, 0, 0) (plaqList d L) q = Q at hql hqk ⊢
  obtain ⟨hak, hkd, hsd, hca, hck⟩ := hpl
  obtain ⟨hak', hkd', hsd', hca', hck'⟩ := hql
  cases P with
  | mk a P' =>
  cases P' with
  | mk k s =>
  cases Q with
  | mk a' Q' =>
  cases Q' with
  | mk k' s' =>
  have hpk' : plaqKey d L a k s = p := hpk
  have hqk' : plaqKey d L a' k' s' = q := hqk
  rw [← hpk', ← hqk']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans (cubes_holding d L a k s hak hkd hsd hca hck
        (fun C => faceSign (cubeFaces d L C) (plaqKey d L a' k' s')))
      (holding_faceInd d L a k s a' k' s' hak hkd hsd hca hck hak' hkd' hsd' hca' hck'))) ?_
  show (linkInd L (a', k', s') a s * BPair.ofNat 1
      + (linkInd L (a', k', s') k (stepAt L a s) * BPair.ofNat 1
      + (linkInd L (a', k', s') a (stepAt L k s) * (BPair.ofNat 1).swap
      + (linkInd L (a', k', s') k s * (BPair.ofNat 1).swap + BPair.unit))) + _).oneValue
    (if a' == a && k' == k then _ else BPair.unit)
  cases haa : (a' == a) with
  | true =>
    have e : a = a' := (beqEqOf haa).symm
    subst e
    rw [Bool.true_and]
    cases hkk : (k' == k) with
    | true =>
      have e : k = k' := (beqEqOf hkk).symm
      subst e
      rw [iteB_true]
      exact hodge_case1 d L a k s s' hak hkd hca hck hca' hck'
    | false =>
      rw [iteB_false]
      exact hodge_case2 d L a k s k' s' hak hck hak' hkd' hck' (neOfBeq hkk)
  | false =>
    rw [Bool.false_and, iteB_false]
    cases hkk : (k' == k) with
    | true =>
      have e : k = k' := (beqEqOf hkk).symm
      subst e
      exact hodge_case5 d L a k s a' s' hak hkd hca hak' hca' (neOfBeq haa)
    | false =>
      cases hak2 : (a' == k) with
      | true =>
        have e : k = a' := (beqEqOf hak2).symm
        subst e
        exact hodge_case3 d L a k s k' s' hak hca hak' hkd' hck'
      | false =>
        cases hka : (k' == a) with
        | true =>
          have e : a = k' := (beqEqOf hka).symm
          subst e
          exact hodge_case4 d L a k s a' s' hak hkd hck hak' hca'
        | false =>
          exact hodge_case6 d L a k s a' k' s' (neOfBeq haa) (neOfBeq hkk)
            (neOfBeq hak2) (neOfBeq hka)

/-- The Hodge identity holds at every direction count and side. -/
theorem hodgeRead_all (d L : Nat) : hodgeRead d L :=
  matOne_of_entries _ _ (plaqCount d L)
    (by rw [length_matAdd _ _ (by rw [gram_length, cubeGram_length]), gram_length])
    (rowsLen_matAdd _ _ _ (gram_rows d L) (cubeGram_rows d L))
    (hodgeMat_shape d L).2 (hodgeMat_shape d L).1
    (fun p q hp hq => hodge_entry d L p q hp hq)

/-- The differences' Gram's form is the differences' squares' fold. -/
theorem diffGram_form (d L a k j : Nat) (W : List BPair) (hW : W.length = plaqCount d L) :
    (quadForm (matMul (transposeM (diffMat d L a k j)) (diffMat d L a k j)) W).oneValue
      (diffFold d L a k j W) := by
  have hBl := diffMat_length d L a k j
  have hB := diffMat_rows d L a k j
  have hpos : 0 < (diffMat d L a k j).length := by
    rw [hBl]
    exact Nat.pow_pos (Nat.succ_pos L)
  have hBt : (transposeM (diffMat d L a k j)).length = plaqCount d L :=
    length_transposeM _ hB hpos
  cases Nat.eq_zero_or_pos (plaqCount d L) with
  | inl h0 =>
    have hWn : W = [] := by
      cases W with
      | nil => rfl
      | cons a l => rw [h0] at hW; exact Nat.noConfusion hW
    have hT : transposeM (diffMat d L a k j) = [] := by
      rw [h0] at hBt
      cases hT : transposeM (diffMat d L a k j) with
      | nil => rfl
      | cons r t => rw [hT] at hBt; exact Nat.noConfusion hBt
    rw [hWn, hT]
    exact BPair.oneValue_symm (dotN_nullR _ _ (matVec_null _ _ trivial))
  | inr hpos' =>
    have hKt : transposeM (transposeM (diffMat d L a k j)) = diffMat d L a k j :=
      transposeM_transposeM _ hB hpos' hpos
    have h := quadForm_matMulT (diffMat d L a k j).length (transposeM (diffMat d L a k j))
      (rowsLen_transposeM _) W (by rw [hW, hBt])
    rw [hKt] at h
    exact h

/-- The Hodge fold's matrix's form is the Hodge fold. -/
theorem hodgeForm (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L) :
    (quadForm (hodgeMat d L) W).oneValue (hodgeFold d L W) := by
  refine BPair.oneValue_trans (quadForm_msum _ _
    (fun a => msum_shape _ _ (hodgePlane_shape d L a) _) W hW _) ?_
  refine bsum_congr_range_ov _ _ d (fun a _ => ?_)
  refine BPair.oneValue_trans (quadForm_msum _ _ (hodgePlane_shape d L a) W hW _) ?_
  refine bsum_congr_range_ov _ _ d (fun k _ => ?_)
  by_cases h : a < k
  · rw [if_pos h, if_pos h]
    refine BPair.oneValue_trans (quadForm_msum _ _ (fun j => diffGram_shape d L a k j) W hW _) ?_
    exact bsum_congr_range_ov _ _ d (fun j _ => diffGram_form d L a k j W hW)
  · rw [if_neg h, if_neg h]
    exact dotN_nullR W _ (matVec_nullMat _ _ W)

/-- The Gram's form joined to the cubes' boundaries' image's
self-pairing is the Hodge fold, `Wᵀ Δ W + |Nᵀ W|² = ` the fold. -/
theorem hodgeForm_read (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L) :
    (quadForm (gram d L) W
      + dotN (matVec (transposeM (cubeBd d L)) W) (matVec (transposeM (cubeBd d L)) W)).oneValue
      (hodgeFold d L W) := by
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (quadForm_gramM (cubeCount d L) (cubeBd d L) (cubeBd_rows d L) W
      (by rw [hW, cubeBd_length])))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm (quadForm_add (gram d L) (cubeGram d L) W
    (by rw [gram_length, hW]) (by rw [hW]; exact gram_rows d L)
    (by rw [cubeGram_length, hW]) (by rw [hW]; exact cubeGram_rows d L))) ?_
  exact BPair.oneValue_trans (quadForm_matOne _ _ W (hodgeRead_all d L)) (hodgeForm d L W hW)

/-- At a range member, the cubes' boundaries pairing it at the sum's
unit, the Gram's form is the Hodge fold's. -/
theorem hodgeForm_range (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hker : poly.unitTail (matVec (transposeM (cubeBd d L)) W)) :
    (quadForm (gram d L) W).oneValue (hodgeFold d L W) :=
  BPair.oneValue_trans (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) (dotN_nullR _ _ hker)) (BPair.add_unit _)))
    (hodgeForm_read d L W hW)

/-- The line's site: the key above a direction, the position along
it and the digits below it, at the positional arithmetic. -/
def siteOnLine (L j hi x lo : Nat) : Nat := hi * (L + 1) ^ (j + 1) + (x * (L + 1) ^ j + lo)

/-- The next position along the line is the site's step. -/
theorem siteOnLine_step (L j hi x lo : Nat) :
    siteOnLine L j hi (x + 1) lo = stepAt L j (siteOnLine L j hi x lo) := by
  show hi * (L + 1) ^ (j + 1) + ((x + 1) * (L + 1) ^ j + lo)
    = hi * (L + 1) ^ (j + 1) + (x * (L + 1) ^ j + lo) + (L + 1) ^ j
  rw [Nat.succ_mul, Nat.add_right_comm (x * (L + 1) ^ j) ((L + 1) ^ j) lo,
    Nat.add_assoc (hi * (L + 1) ^ (j + 1)) (x * (L + 1) ^ j + lo) ((L + 1) ^ j)]

/-- The line's site reads its position at the direction. -/
theorem coordAt_siteOnLine (L j hi x lo : Nat) (hx : x < L + 1) (hlo : lo < (L + 1) ^ j) :
    coordAt L j (siteOnLine L j hi x lo) = x := by
  show baseDigit (L + 1) j (hi * (L + 1) ^ (j + 1) + (x * (L + 1) ^ j + lo)) = x
  rw [baseDigit_split_low (L + 1) j (j + 1) hi _ (Nat.succ_pos L) (Nat.lt_succ_self j),
    baseDigit_split_top (L + 1) j x lo (Nat.succ_pos L) hlo hx]

/-- The line's site reads a further direction's coordinate at the
line's first position. -/
theorem coordAt_siteOnLine_off (L j c hi x lo : Nat) (hc : ¬ c = j) (hx : x < L + 1)
    (hlo : lo < (L + 1) ^ j) :
    coordAt L c (siteOnLine L j hi x lo) = coordAt L c (siteOnLine L j hi 0 lo) := by
  have hb : 0 < L + 1 := Nat.succ_pos L
  show baseDigit (L + 1) c (hi * (L + 1) ^ (j + 1) + (x * (L + 1) ^ j + lo))
    = baseDigit (L + 1) c (hi * (L + 1) ^ (j + 1) + (0 * (L + 1) ^ j + lo))
  cases Nat.lt_or_ge c j with
  | inl hcj =>
    rw [baseDigit_split_low (L + 1) c (j + 1) hi _ hb (Nat.lt_succ_of_lt hcj),
      baseDigit_split_low (L + 1) c (j + 1) hi _ hb (Nat.lt_succ_of_lt hcj),
      baseDigit_split_low (L + 1) c j x lo hb hcj, baseDigit_split_low (L + 1) c j 0 lo hb hcj]
  | inr hge =>
    have hlt : j < c := Nat.lt_of_le_of_ne hge (fun h => hc h.symm)
    obtain ⟨k, hk⟩ := Nat.le.dest hlt
    rw [← hk, baseDigit_split_beyond (L + 1) (j + 1) k hi _ hb (splitLtPow (L + 1) j x lo hlo hx),
      baseDigit_split_beyond (L + 1) (j + 1) k hi _ hb (splitLtPow (L + 1) j 0 lo hlo hb)]

/-- The sites' fold over a direction's lines: the key above the
direction, the position along it and the digits below it. -/
theorem bsum_site_split (d L j : Nat) (hj : j < d) (G : Nat → BPair) :
    (bsum G (List.range ((L + 1) ^ d))).oneValue
      (bsum (fun hi => bsum (fun x => bsum (fun lo => G (siteOnLine L j hi x lo))
        (List.range ((L + 1) ^ j))) (List.range (L + 1)))
        (List.range ((L + 1) ^ (d - (j + 1))))) := by
  have hd : (L + 1) ^ d = (L + 1) ^ (d - (j + 1)) * (L + 1) ^ (j + 1) := by
    rw [← powAdd, Nat.add_comm (d - (j + 1)) (j + 1), natAddSubCancel hj]
  rw [hd, range_mul]
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ (List.range _)) ?_
  refine bsum_congr_range_ov _ _ _ (fun hi _ => ?_)
  rw [famFold_map BPair.add BPair.unit, range_pow_succ]
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws _ _ (List.range _)) ?_
  refine bsum_congr_range_ov _ _ _ (fun x _ => ?_)
  rw [famFold_map BPair.add BPair.unit]
  exact BPair.oneValue_refl _

/-- The Dirichlet fold's line: the consecutive differences along a
line, the sum's unit beyond both ends. -/
def lineDiff (L : Nat) (V : Nat → BPair) (c : Bool) (x : Nat) : BPair :=
  (if c && decide (x < L) then V x else BPair.unit)
    + (if 0 < x then (if c && decide (x - 1 < L) then (V (x - 1)).swap else BPair.unit)
      else BPair.unit)

/-- The line's read is the differences' fold from the end. -/
private theorem line_partial (L : Nat) (V : Nat → BPair) :
    ∀ x : Nat, x < L → (bsum (lineDiff L V true) (List.range (x + 1))).oneValue (V x)
  | 0, hx => by
    show (lineDiff L V true 0 + BPair.unit).oneValue (V 0)
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    show ((if true && decide (0 < L) then V 0 else BPair.unit)
      + (if 0 < 0 then (if true && decide (0 - 1 < L) then (V (0 - 1)).swap else BPair.unit)
        else BPair.unit)).oneValue (V 0)
    rw [Bool.true_and, decide_eq_true hx, if_neg (Nat.lt_irrefl 0), iteB_true]
    exact BPair.add_unit _
  | x + 1, hx => by
    refine BPair.oneValue_trans (foldB_range_snoc _ (x + 1)) ?_
    refine BPair.oneValue_trans (BPair.add_congr (line_partial L V x (Nat.lt_of_succ_lt hx))
      (BPair.oneValue_refl _)) ?_
    show (V x + ((if true && decide (x + 1 < L) then V (x + 1) else BPair.unit)
      + (if 0 < x + 1 then
        (if true && decide (x + 1 - 1 < L) then (V (x + 1 - 1)).swap else BPair.unit)
        else BPair.unit))).oneValue (V (x + 1))
    rw [Bool.true_and, Bool.true_and, decide_eq_true hx, if_pos (Nat.succ_pos x), iteB_true,
      show x + 1 - 1 = x from rfl, decide_eq_true (Nat.lt_of_succ_lt hx), iteB_true,
      BPair.add_comm (V (x + 1)) (V x).swap, ← BPair.add_assoc]
    exact BPair.oneValue_trans (BPair.add_congr (BPair.add_swap_null _) (BPair.oneValue_refl _))
      (BPair.unit_add _)

/-- One line of the Dirichlet fold: the values' squares' fold along
the line sits at or below the side's square against the
differences' squares' fold, each value the differences' fold from
the end and its square at or below the count against the squares
(Construction con:coeff's Cauchy--Schwarz at the count). -/
theorem line_telescope (L : Nat) (V : Nat → BPair) (c : Bool) :
    bsum (fun x => if c && decide (x < L) then V x * V x else BPair.unit) (List.range (L + 1))
      ≤ BPair.ofNat (L * L)
        * bsum (fun x => lineDiff L V c x * lineDiff L V c x) (List.range (L + 1)) := by
  have hT : BPair.unit
      ≤ bsum (fun x => lineDiff L V c x * lineDiff L V c x) (List.range (L + 1)) :=
    foldB_nonneg_mem _ _ (fun _ _ => unitLeSq _)
  cases c with
  | false =>
    refine leB_congr_left (BPair.oneValue_symm (famFold_unit_ov bpairFoldLaws _ (fun x => ?_) _))
      ?_
    · rw [Bool.false_and, iteB_false]
      exact BPair.oneValue_refl _
    · exact leB_unit_mul _ hT
  | true =>
    have hsnoc : (bsum (fun x => if true && decide (x < L) then V x * V x else BPair.unit)
        (List.range (L + 1))).oneValue
        (bsum (fun x => if true && decide (x < L) then V x * V x else BPair.unit)
          (List.range L)) := by
      refine BPair.oneValue_trans (foldB_range_snoc _ L) ?_
      rw [Bool.true_and, decide_eq_false (Nat.lt_irrefl L), iteB_false]
      exact BPair.add_unit _
    refine leB_congr_left (BPair.oneValue_symm hsnoc) ?_
    refine leB_trans (bsum_le _ (fun _ => BPair.ofNat L
      * bsum (fun x => lineDiff L V true x * lineDiff L V true x) (List.range (L + 1))) _
      (fun x hx => ?_)) ?_
    · have hxL : x < L := ltOfCountRange hx
      rw [Bool.true_and, decide_eq_true hxL, iteB_true]
      refine leB_congr_left (BPair.mul_congr (line_partial L V x hxL) (line_partial L V x hxL)) ?_
      have hcs := coeff.bsum_sq_le_count (x + 1) (fun _ => BPair.ofNat 1) (lineDiff L V true)
      have h1 : ¬ (BPair.ofNat 1).oneValue BPair.unit := by decide
      have hcount : (bsum (fun _ => if (BPair.ofNat 1).oneValue BPair.unit then BPair.unit
          else BPair.ofNat 1) (List.range (x + 1))).oneValue (BPair.ofNat (x + 1)) := by
        refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun _ => BPair.ofNat 1) _
          (fun _ _ => by rw [if_neg h1]; exact BPair.oneValue_refl _)) ?_
        refine BPair.oneValue_trans (foldB_const _ _) ?_
        rw [length_range]
        exact BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
          (BPair.ofNat_one_mul _)
      have hmono := bsum_range_mono (fun i => lineDiff L V true i * lineDiff L V true i)
        (fun _ => unitLeSq _) (x + 1) (L - x)
      have e : x + 1 + (L - x) = L + 1 := by
        rw [Nat.add_right_comm, natAddSubCancel (Nat.le_of_lt hxL)]
      rw [e] at hmono
      refine leB_trans (leB_congr
        (BPair.mul_congr (bsum_congr_range_ov _ _ _ (fun i _ => BPair.ofNat_one_mul _))
          (bsum_congr_range_ov _ _ _ (fun i _ => BPair.ofNat_one_mul _)))
        (BPair.mul_congr hcount (bsum_congr_range_ov _ _ _
          (fun i _ => BPair.mul_congr (BPair.ofNat_one_mul _) (BPair.ofNat_one_mul _)))) hcs) ?_
      exact leB_mul_mono (foldB_nonneg_mem _ _ (fun _ _ => unitLeSq _)) (unitLeOfNat _)
        (leB_ofNat hxL) hmono
    · refine leB_congr_right ?_ (leB_refl _)
      refine BPair.oneValue_trans (foldB_const _ _) ?_
      rw [length_range]
      exact BPair.oneValue_symm (BPair.ofNat_mul_mul L L _)

/-- The difference operator's read at a site on a plane type along a
direction: the plane's plaquette at the site joined to the balance
partner of the plane's plaquette one step back along the direction
at an occupied coordinate. -/
def diffAt (d L a k j : Nat) (W : List BPair) (t : Nat) : BPair :=
  (if decide (coordAt L a t < L) && decide (coordAt L k t < L)
    then getAt BPair.unit W (plaqKey d L a k t) else BPair.unit)
  + (if 0 < coordAt L j t then
    (if decide (coordAt L a (t - (L + 1) ^ j) < L) && decide (coordAt L k (t - (L + 1) ^ j) < L)
      then (getAt BPair.unit W (plaqKey d L a k (t - (L + 1) ^ j))).swap else BPair.unit)
    else BPair.unit)

/-- The difference operator against a plaquette vector reads, at a
site, its read there under the row's guard. -/
theorem diff_entry (d L a k j t : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hak : a < k) (hkd : k < d) (ht : t < (L + 1) ^ d) :
    (getAt BPair.unit (matVec (diffMat d L a k j) W) t).oneValue
      (if (j == a || j == k) || decide (0 < coordAt L j t) then diffAt d L a k j W t
        else BPair.unit) := by
  have hb : 0 < L + 1 := Nat.succ_pos L
  have had : a < d := Nat.lt_trans hak hkd
  have hDl := diffMat_length d L a k j
  have hDr := diffMat_rows d L a k j
  have htD : t < (diffMat d L a k j).length := by
    rw [hDl]
    exact ht
  rw [getAt_matVec _ _ t htD]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_fold (plaqCount d L) _ _ (rowsLen_getAt _ t hDr htD) hW]
  -- the entries against the vector's reads at the keys
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun p =>
    if (j == a || j == k) || decide (0 < coordAt L j t) then
      (fun P : Nat × Nat × Nat =>
        (if P.1 == a && P.2.1 == k && P.2.2 == t
          then getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2) else BPair.unit)
        + (if P.1 == a && P.2.1 == k && decide (0 < coordAt L j t) && stepAt L j P.2.2 == t
          then (getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2)).swap else BPair.unit))
        (getAt (0, 0, 0) (plaqList d L) p)
    else BPair.unit) _ (fun p hp => ?_)) ?_
  · rw [diffMat_entry d L a k j t p ht hp]
    have hw : getAt BPair.unit W p = getAt BPair.unit W (plaqKey d L
        (getAt (0, 0, 0) (plaqList d L) p).1 (getAt (0, 0, 0) (plaqList d L) p).2.1
        (getAt (0, 0, 0) (plaqList d L) p).2.2) := by
      rw [plaqKey_of_getAt d L p hp]
    rw [hw]
    refine BPair.oneValue_trans (ite_mul_unit _ _ _) (ite_congr_prop _ (fun _ => ?_))
    rw [BPair.right_distrib]
    exact BPair.add_congr (iteMul _ _).1 (iteMul _ _).2
  refine BPair.oneValue_trans (bsum_ite_const _ _ _) (ite_congr_prop _ (fun _ => ?_))
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (bsum_plaq_places d L
    (fun P : Nat × Nat × Nat =>
      (if P.1 == a && P.2.1 == k && P.2.2 == t
        then getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2) else BPair.unit)
      + (if P.1 == a && P.2.1 == k && decide (0 < coordAt L j t) && stepAt L j P.2.2 == t
        then (getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2)).swap else BPair.unit)))) ?_
  refine BPair.oneValue_trans (bsum_plaq_planes d L _) ?_
  -- the planes' reads at the plane's own keys
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun a' => bsum (fun k' => if a' < k' then
    bsum (fun s => if decide (coordAt L a' s < L) && decide (coordAt L k' s < L) then
      (if a' == a && k' == k && s == t then getAt BPair.unit W (plaqKey d L a' k' s)
        else BPair.unit)
      + (if a' == a && k' == k && decide (0 < coordAt L j t) && stepAt L j s == t
        then (getAt BPair.unit W (plaqKey d L a' k' s)).swap else BPair.unit)
      else BPair.unit) (List.range ((L + 1) ^ d)) else BPair.unit) (List.range d)) d
    (fun a' _ => bsum_congr_range_ov _ _ d (fun k' _ => ite_congr_prop _ (fun _ =>
      bsum_congr_range_ov _ _ _ (fun s _ => ite_congr_prop _ (fun _ => BPair.oneValue_refl _)))))) ?_
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun a' _ ha' => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun k' => ?_) _
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun s => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf ha']
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    exact BPair.add_unit _
  refine BPair.oneValue_trans (bsum_range_pick _ k d hkd (fun k' _ hk' => ?_)) ?_
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun s => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf hk']
    repeat rw [Bool.and_false]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    exact BPair.add_unit _
  rw [if_pos hak, eqBeqOf (rfl : a = a), eqBeqOf (rfl : k = k)]
  repeat rw [Bool.true_and]
  -- the plane guard distributes, and the two reads at the site and its predecessor
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s =>
    (if (decide (coordAt L a s < L) && decide (coordAt L k s < L)) && s == t
      then getAt BPair.unit W (plaqKey d L a k s) else BPair.unit)
    + (if (decide (coordAt L a s < L) && decide (coordAt L k s < L))
        && (decide (0 < coordAt L j t) && stepAt L j s == t)
      then (getAt BPair.unit W (plaqKey d L a k s)).swap else BPair.unit)) _ (fun s _ => ?_)) ?_
  · refine BPair.oneValue_trans (ite_add_unit _ _ _) ?_
    rw [ite_ite_and, ite_ite_and]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr (bsum_site_beq d L _ _ t ht) ?_
  cases hc : decide (0 < coordAt L j t) with
  | false =>
    rw [if_neg (of_decide_eq_false hc)]
    refine famFold_unit_ov bpairFoldLaws _ (fun s => ?_) _
    rw [Bool.false_and, Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  | true =>
    have hpos : 0 < coordAt L j t := of_decide_eq_true hc
    rw [if_pos hpos]
    obtain ⟨hs0, _, _⟩ := stepBack (L + 1) j t hb hpos
    have hlt : t - (L + 1) ^ j < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.sub_le t _) ht
    refine BPair.oneValue_trans (bsum_range_at _ _ (t - (L + 1) ^ j) _ hlt (fun s _ hs => ?_)) ?_
    · have hst : stepAt L j s = t := beqEqOf (andSplitB (andSplitB hs).2).2
      refine addCancelR ((L + 1) ^ j) ?_
      rw [hs0]
      exact hst
    · rw [Bool.true_and, eqBeqOf (show stepAt L j (t - (L + 1) ^ j) = t from hs0), Bool.and_true]
      exact BPair.oneValue_refl _

/-- The differences' squares' fold sits at or above the sum's unit. -/
theorem diffFold_unitLe (d L a k j : Nat) (W : List BPair) :
    BPair.unit ≤ diffFold d L a k j W :=
  leB_congr_right (BPair.oneValue_symm (dotN_read _ _)) (unitLeOfSide (dotP_self_side _))

/-- Along a line the difference operator's reads are the line's
differences. -/
private theorem line_diff_read (d L a k j : Nat) (W : List BPair) (hi lo : Nat)
    (hlo : lo < (L + 1) ^ j) (κ : Bool)
    (hκ : ∀ x, x < L + 1 → (decide (coordAt L a (siteOnLine L j hi x lo) < L)
      && decide (coordAt L k (siteOnLine L j hi x lo) < L)) = (κ && decide (x < L)))
    (x : Nat) (hx : x < L + 1) :
    (diffAt d L a k j W (siteOnLine L j hi x lo)).oneValue
      (lineDiff L (fun y => getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi y lo))) κ x) := by
  have hb : 0 < L + 1 := Nat.succ_pos L
  show ((if decide (coordAt L a (siteOnLine L j hi x lo) < L)
        && decide (coordAt L k (siteOnLine L j hi x lo) < L)
      then getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi x lo)) else BPair.unit)
    + (if 0 < coordAt L j (siteOnLine L j hi x lo) then
      (if decide (coordAt L a (siteOnLine L j hi x lo - (L + 1) ^ j) < L)
          && decide (coordAt L k (siteOnLine L j hi x lo - (L + 1) ^ j) < L)
        then (getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi x lo - (L + 1) ^ j))).swap
        else BPair.unit)
      else BPair.unit)).oneValue
    ((if κ && decide (x < L) then getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi x lo))
      else BPair.unit)
    + (if 0 < x then
      (if κ && decide (x - 1 < L)
        then (getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi (x - 1) lo))).swap
        else BPair.unit)
      else BPair.unit))
  rw [hκ x hx, coordAt_siteOnLine L j hi x lo hx hlo]
  refine BPair.add_congr (BPair.oneValue_refl _) (ite_congr_prop _ (fun hpos => ?_))
  have hx1 : x - 1 + 1 = x := Nat.succ_pred_eq_of_pos hpos
  have hsite : siteOnLine L j hi x lo = stepAt L j (siteOnLine L j hi (x - 1) lo) := by
    rw [← siteOnLine_step, hx1]
  have hpos' : 0 < coordAt L j (siteOnLine L j hi x lo) := by
    rw [coordAt_siteOnLine L j hi x lo hx hlo]
    exact hpos
  have hback : siteOnLine L j hi x lo - (L + 1) ^ j = siteOnLine L j hi (x - 1) lo := by
    refine addCancelR ((L + 1) ^ j) ?_
    rw [(stepBack (L + 1) j _ hb hpos').1]
    exact hsite
  rw [hback, hκ (x - 1) (Nat.lt_of_le_of_lt (Nat.sub_le x 1) hx)]
  exact BPair.oneValue_refl _

/-- One line's values' squares against its differences' squares. -/
private theorem line_read (d L a k j : Nat) (W : List BPair) (hi lo : Nat)
    (hlo : lo < (L + 1) ^ j) (κ : Bool)
    (hκ : ∀ x, x < L + 1 → (decide (coordAt L a (siteOnLine L j hi x lo) < L)
      && decide (coordAt L k (siteOnLine L j hi x lo) < L)) = (κ && decide (x < L))) :
    bsum (fun x => if decide (coordAt L a (siteOnLine L j hi x lo) < L)
        && decide (coordAt L k (siteOnLine L j hi x lo) < L)
      then getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi x lo))
        * getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi x lo)) else BPair.unit)
      (List.range (L + 1))
      ≤ BPair.ofNat (L * L) * bsum (fun x => diffAt d L a k j W (siteOnLine L j hi x lo)
        * diffAt d L a k j W (siteOnLine L j hi x lo)) (List.range (L + 1)) := by
  refine leB_congr (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun x hx => ?_)))
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun x hx => ?_))))
    (line_telescope L (fun y => getAt BPair.unit W (plaqKey d L a k (siteOnLine L j hi y lo))) κ)
  · rw [hκ x hx]
    exact BPair.oneValue_refl _
  · exact BPair.mul_congr (line_diff_read d L a k j W hi lo hlo κ hκ x hx)
      (line_diff_read d L a k j W hi lo hlo κ hκ x hx)

/-- A plane's values' squares' fold sits at or below the side's square
against the differences' fold along either of the plane's directions:
the Dirichlet fold telescopes line by line. -/
theorem plane_sq_le (d L a k j : Nat) (hak : a < k) (hkd : k < d) (hj : j = a ∨ j = k)
    (W : List BPair) (hW : W.length = plaqCount d L) :
    bsum (fun s => if coordAt L a s < L && coordAt L k s < L
        then getAt BPair.unit W (plaqKey d L a k s) * getAt BPair.unit W (plaqKey d L a k s)
        else BPair.unit) (List.range ((L + 1) ^ d))
      ≤ BPair.ofNat (L * L) * diffFold d L a k j W := by
  have hjd : j < d := by
    cases hj with
    | inl h => rw [h]; exact Nat.lt_trans hak hkd
    | inr h => rw [h]; exact hkd
  have hRG : (j == a || j == k) = true := by
    cases hj with
    | inl h => rw [h, eqBeqOf (rfl : a = a)]; rfl
    | inr h => rw [h, eqBeqOf (rfl : k = k)]; exact Bool.or_true _
  have hD : (diffFold d L a k j W).oneValue
      (bsum (fun t => diffAt d L a k j W t * diffAt d L a k j W t) (List.range ((L + 1) ^ d))) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    rw [dotP_fold ((L + 1) ^ d) _ _ (by rw [matVec_length, diffMat_length])
      (by rw [matVec_length, diffMat_length])]
    refine bsum_congr_range_ov _ _ _ (fun t ht => ?_)
    have he := diff_entry d L a k j t W hW hak hkd ht
    rw [hRG, Bool.true_or, iteB_true] at he
    exact BPair.mul_congr he he
  refine leB_congr_right (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hD)) ?_
  refine leB_congr (BPair.oneValue_symm (bsum_site_split d L j hjd _))
    (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (bsum_site_split d L j hjd _)))
    ?_
  refine leB_congr (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun hi _ => bsum_swap _ _ _)))
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun hi _ => bsum_swap _ _ _)))) ?_
  refine leB_congr_right (BPair.oneValue_trans
    (bsum_congr_range_ov _ _ _ (fun hi _ => foldB_mul_left _ _ _)) (foldB_mul_left _ _ _)) ?_
  refine bsum_le _ _ _ (fun hi _ => bsum_le _ _ _ (fun lo hlo => ?_))
  have hlo' : lo < (L + 1) ^ j := ltOfCountRange hlo
  cases hj with
  | inl hja =>
    subst hja
    refine line_read d L j k j W hi lo hlo' (decide (coordAt L k (siteOnLine L j hi 0 lo) < L))
      (fun x hx => ?_)
    rw [coordAt_siteOnLine L j hi x lo hx hlo',
      coordAt_siteOnLine_off L j k hi x lo (fun h => Nat.ne_of_lt hak h.symm) hx hlo', Bool.and_comm]
  | inr hjk =>
    subst hjk
    refine line_read d L a j j W hi lo hlo' (decide (coordAt L a (siteOnLine L j hi 0 lo) < L))
      (fun x hx => ?_)
    rw [coordAt_siteOnLine L j hi x lo hx hlo',
      coordAt_siteOnLine_off L j a hi x lo (Nat.ne_of_lt hak) hx hlo']

/-- A constant through the planes' fold. -/
private theorem const_planes (c : BPair) (G : Nat → Nat → BPair) (d : Nat) :
    (c * bsum (fun a => bsum (fun k => if a < k then G a k else BPair.unit) (List.range d))
      (List.range d)).oneValue
      (bsum (fun a => bsum (fun k => if a < k then c * G a k else BPair.unit) (List.range d))
        (List.range d)) := by
  refine BPair.oneValue_symm (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun a _ => ?_))
    (foldB_mul_left _ _ _))
  refine BPair.oneValue_trans (bsum_congr_range_ov _
    (fun k => c * (if a < k then G a k else BPair.unit)) d (fun k _ => ?_)) (foldB_mul_left _ _ _)
  exact BPair.oneValue_trans (ite_congr_prop _ (fun _ => BPair.oneValue_of_eq (BPair.mul_comm c _)))
    (BPair.oneValue_trans (BPair.oneValue_symm (ite_mul_unit _ _ _))
      (BPair.oneValue_of_eq (BPair.mul_comm _ c)))

/-- The Poincaré read at a range member, the cubes' boundaries
pairing it at the sum's unit: `2 Wᵀ W ≤ L² Wᵀ Δ W`, the pair
`[L² : 2]`'s comparison at its clearing; the self-pairing at or
below the side's square against either plane direction's
differences' fold, and at or below half the side's square against
the two folds' join under the Hodge fold. -/
theorem poincare_read (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hker : poly.unitTail (matVec (transposeM (cubeBd d L)) W)) :
    BPair.ofNat 2 * dotN W W ≤ BPair.ofNat (L * L) * quadForm (gram d L) W := by
  have hself : (dotN W W).oneValue (bsum (fun a => bsum (fun k => if a < k then
      bsum (fun s => if coordAt L a s < L && coordAt L k s < L
        then getAt BPair.unit W (plaqKey d L a k s) * getAt BPair.unit W (plaqKey d L a k s)
        else BPair.unit) (List.range ((L + 1) ^ d)) else BPair.unit) (List.range d))
      (List.range d)) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    rw [dotP_fold (plaqCount d L) W W hW hW]
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun p =>
      (fun P : Nat × Nat × Nat => getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2)
        * getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2)) (getAt (0, 0, 0) (plaqList d L) p)) _
      (fun p hp => ?_)) ?_
    · have hw : getAt BPair.unit W p = getAt BPair.unit W (plaqKey d L
          (getAt (0, 0, 0) (plaqList d L) p).1 (getAt (0, 0, 0) (plaqList d L) p).2.1
          (getAt (0, 0, 0) (plaqList d L) p).2.2) := by
        rw [plaqKey_of_getAt d L p hp]
      rw [hw]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (bsum_plaq_places d L
      (fun P : Nat × Nat × Nat => getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2)
        * getAt BPair.unit W (plaqKey d L P.1 P.2.1 P.2.2)))) ?_
    refine BPair.oneValue_trans (bsum_plaq_planes d L _) ?_
    exact bsum_congr_range_ov _ _ d (fun a _ => bsum_congr_range_ov _ _ d (fun k _ =>
      ite_congr_prop _ (fun _ => bsum_congr_range_ov _ _ _ (fun s _ =>
        ite_congr_prop _ (fun _ => BPair.oneValue_refl _)))))
  refine leB_congr_left (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hself)) ?_
  refine leB_congr_right (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (hodgeForm_range d L W hW hker))) ?_
  refine leB_congr (BPair.oneValue_symm (const_planes _ _ d))
    (BPair.oneValue_symm (const_planes _ _ d)) ?_
  refine bsum_le _ _ _ (fun a _ => bsum_le _ _ _ (fun k hk => ite_le_prop _ (fun hak => ?_)))
  have hkd : k < d := ltOfCountRange hk
  have had : a < d := Nat.lt_trans hak hkd
  have hDa := plane_sq_le d L a k a hak hkd (Or.inl rfl) W hW
  have hDk := plane_sq_le d L a k k hak hkd (Or.inr rfl) W hW
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans (ofNat_succ_mul 1 _)
    (BPair.add_congr (BPair.ofNat_one_mul _) (BPair.oneValue_refl _)))) ?_
  refine leB_trans (leB_add hDa hDk) ?_
  refine leB_congr_left (BPair.oneValue_of_eq (BPair.left_distrib _ _ _)) ?_
  refine leB_mulR (unitLeOfNat _) ?_
  refine leB_congr_right
    (BPair.oneValue_symm (bsum_range_pick_two _ a k d had hkd (Nat.ne_of_lt hak))) ?_
  refine leB_add (leB_refl _) (leB_congr_left (BPair.add_unit _) (leB_add (leB_refl _) ?_))
  refine foldB_nonneg_mem _ _ (fun j _ => ?_)
  cases hg : (j == a || j == k) with
  | true => exact leB_refl _
  | false => exact diffFold_unitLe d L a k j W

/-! The four-cells: four directions in order with a corner site, the
cube key, the four-cells' boundaries `N₄` and the two cube Grams. -/

/-- The four-cells: four directions in order with a corner site whose
four coordinates sit below the side. -/
def fourCellList (d L : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range d).flatMap (fun a => (List.range d).flatMap (fun b =>
    (List.range d).flatMap (fun c => (List.range d).flatMap (fun e =>
      if a < b && b < c && c < e then
        (sites d L).filterMap (fun s =>
          if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L && coordAt L e s < L
          then some (a, b, c, e, s) else none)
      else []))))

/-- The four-cells' count. -/
def fourCellCount (d L : Nat) : Nat := (fourCellList d L).length

/-- The cube key at three directions and a corner, the cube's position
in the list. -/
def cubeKey (d L a b c s : Nat) : Nat := posBy quadBeq (a, b, c, s) (cubeList d L)

/-- A four-cell's eight cubes at their signs: one at the cube at the
four-cell's corner in its three lower directions, and the signs at
which the eight cubes' boundaries fold to the sum's unit at every
plaquette, each plaquette of the four-cell on two cubes at exchanged
signs. -/
def fourCellCubes (d L : Nat) (f : Nat × Nat × Nat × Nat × Nat) : List (Nat × BPair) :=
  [(cubeKey d L f.1 f.2.1 f.2.2.1 f.2.2.2.2, BPair.ofNat 1),
   (cubeKey d L f.1 f.2.1 f.2.2.1 (stepAt L f.2.2.2.1 f.2.2.2.2), (BPair.ofNat 1).swap),
   (cubeKey d L f.1 f.2.1 f.2.2.2.1 f.2.2.2.2, (BPair.ofNat 1).swap),
   (cubeKey d L f.1 f.2.1 f.2.2.2.1 (stepAt L f.2.2.1 f.2.2.2.2), BPair.ofNat 1),
   (cubeKey d L f.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2, BPair.ofNat 1),
   (cubeKey d L f.1 f.2.2.1 f.2.2.2.1 (stepAt L f.2.1 f.2.2.2.2), (BPair.ofNat 1).swap),
   (cubeKey d L f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2, (BPair.ofNat 1).swap),
   (cubeKey d L f.2.1 f.2.2.1 f.2.2.2.1 (stepAt L f.1 f.2.2.2.2), BPair.ofNat 1)]

/-- The four-cells' boundaries `N₄`: the cube-cell list at the cubes'
signs. -/
def fourCellBd (d L : Nat) : Mat :=
  (List.range (cubeCount d L)).map (fun c =>
    (fourCellList d L).map (fun f => faceSign (fourCellCubes d L f) c))

/-- The cubes' Gram `NᵀN`, the rows' Gram of the transposed cubes'
boundaries, each row a cube's boundary as a plaquette vector. -/
def cubesGram (d L : Nat) : Mat := gramM (transposeM (cubeBd d L))

/-- The four-cells' boundaries' Gram `N₄ N₄ᵀ`, the rows' Gram. -/
def fourCellGram (d L : Nat) : Mat := gramM (fourCellBd d L)

/-- The four-cells' boundaries' fold read: `N N₄` reads the sum's
unit entrywise. -/
def bdRead4 (d L : Nat) : Prop := matNull (matMul (cubeBd d L) (fourCellBd d L))

instance instCornerwindow20 (d L : Nat) : Decidable (bdRead4 d L) :=
  inferInstanceAs (Decidable (matNull _))

/-! The cube keys: a member of the cube list, the key's bounds and
read, two members at one key one cube, the keys' comparison at the
data, the list distinct and the cube at a place keyed to its
place. -/

/-- A valid cube is a member of the cube list. -/
theorem cube_mem (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) : (a, b, c, s) ∈ cubeList d L := by
  refine mem_flatMap_to _ (memRange (Nat.lt_trans hab (Nat.lt_trans hbc hc)))
    (mem_flatMap_to _ (memRange (Nat.lt_trans hbc hc)) (mem_flatMap_to _ (memRange hc) ?_))
  show (a, b, c, s) ∈ (if a < b && b < c then (sites d L).filterMap (fun s =>
    if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L then some (a, b, c, s)
    else none) else [])
  have hab' : (decide (a < b) && decide (b < c)) = true := by
    rw [decide_eq_true hab, decide_eq_true hbc]
    rfl
  rw [if_pos hab']
  refine mem_filterMap_to _ (memRange hs) ?_
  show (if (decide (coordAt L a s < L) && decide (coordAt L b s < L)
      && decide (coordAt L c s < L)) = true then some (a, b, c, s) else none) = some (a, b, c, s)
  rw [decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc]
  rfl

/-- The cube key of a member sits below the cubes' count. -/
theorem cubeKey_lt (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) : cubeKey d L a b c s < cubeCount d L :=
  posBy_lt_of_hit quadBeq (a, b, c, s) (cubeList d L)
    ⟨(a, b, c, s), cube_mem d L a b c s hab hbc hc hs hca hcb hcc, quadBeq_refl _⟩

/-- The cube list at a member's key reads the member. -/
theorem cubeKey_read (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) :
    getAt (0, 0, 0, 0) (cubeList d L) (cubeKey d L a b c s) = (a, b, c, s) :=
  (quadBeq_read _ _ (getAt_posBy (0, 0, 0, 0) quadBeq (a, b, c, s) (cubeList d L)
    ⟨(a, b, c, s), cube_mem d L a b c s hab hbc hc hs hca hcb hcc, quadBeq_refl _⟩)).symm

/-- Two members at one cube key are one cube. -/
theorem cubeKey_inj (d L a b c s a' b' c' s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (hab' : a' < b') (hbc' : b' < c') (hc' : c' < d)
    (hs' : s' < (L + 1) ^ d) (hca' : coordAt L a' s' < L) (hcb' : coordAt L b' s' < L)
    (hcc' : coordAt L c' s' < L) (h : cubeKey d L a b c s = cubeKey d L a' b' c' s') :
    a = a' ∧ b = b' ∧ c = c' ∧ s = s' := by
  have h1 := cubeKey_read d L a b c s hab hbc hc hs hca hcb hcc
  rw [h, cubeKey_read d L a' b' c' s' hab' hbc' hc' hs' hca' hcb' hcc'] at h1
  exact ⟨(congrArg Prod.fst h1).symm, (congrArg (fun q : Nat × Nat × Nat × Nat => q.2.1) h1).symm,
    (congrArg (fun q : Nat × Nat × Nat × Nat => q.2.2.1) h1).symm,
    (congrArg (fun q : Nat × Nat × Nat × Nat => q.2.2.2) h1).symm⟩

/-- Two valid cubes' keys read one key exactly at one type and one
corner. -/
theorem cubeKey_beq (d L a b c s a' b' c' s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (hab' : a' < b') (hbc' : b' < c') (hc' : c' < d)
    (hs' : s' < (L + 1) ^ d) (hca' : coordAt L a' s' < L) (hcb' : coordAt L b' s' < L)
    (hcc' : coordAt L c' s' < L) :
    (cubeKey d L a b c s == cubeKey d L a' b' c' s') = (a == a' && b == b' && c == c' && s == s') := by
  cases haa : (a == a') with
  | true =>
    cases hbb : (b == b') with
    | true =>
      cases hcc2 : (c == c') with
      | true =>
        cases hss : (s == s') with
        | true =>
          rw [← beqEqOf haa, ← beqEqOf hbb, ← beqEqOf hcc2, ← beqEqOf hss]
          exact eqBeqOf rfl
        | false =>
          show (cubeKey d L a b c s == cubeKey d L a' b' c' s') = false
          refine neBeqOf (fun h => ?_)
          have h4 := (cubeKey_inj d L a b c s a' b' c' s' hab hbc hc hs hca hcb hcc hab' hbc' hc' hs' hca' hcb' hcc' h).2.2.2
          rw [eqBeqOf h4] at hss
          exact Bool.noConfusion hss
      | false =>
        show (cubeKey d L a b c s == cubeKey d L a' b' c' s') = false
        refine neBeqOf (fun h => ?_)
        have h3 := (cubeKey_inj d L a b c s a' b' c' s' hab hbc hc hs hca hcb hcc hab' hbc' hc' hs' hca' hcb' hcc' h).2.2.1
        rw [eqBeqOf h3] at hcc2
        exact Bool.noConfusion hcc2
    | false =>
      show (cubeKey d L a b c s == cubeKey d L a' b' c' s') = false
      refine neBeqOf (fun h => ?_)
      have h2 := (cubeKey_inj d L a b c s a' b' c' s' hab hbc hc hs hca hcb hcc hab' hbc' hc' hs' hca' hcb' hcc' h).2.1
      rw [eqBeqOf h2] at hbb
      exact Bool.noConfusion hbb
  | false =>
    show (cubeKey d L a b c s == cubeKey d L a' b' c' s') = false
    refine neBeqOf (fun h => ?_)
    have h1 := (cubeKey_inj d L a b c s a' b' c' s' hab hbc hc hs hca hcb hcc hab' hbc' hc' hs' hca' hcb' hcc' h).1
    rw [eqBeqOf h1] at haa
    exact Bool.noConfusion haa

/-- A member of a direction triple's cube family sits at the triple. -/
private theorem cube_mem_triple (d L a b c : Nat) (q : Nat × Nat × Nat × Nat)
    (hq : q ∈ (if a < b && b < c then (sites d L).filterMap (fun s =>
      if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L then some (a, b, c, s)
      else none) else [])) :
    q.1 = a ∧ q.2.1 = b ∧ q.2.2.1 = c := by
  by_cases hab : (decide (a < b) && decide (b < c)) = true
  · rw [if_pos hab] at hq
    obtain ⟨s, _, hf⟩ := mem_filterMap_of _ _ _ hq
    by_cases hc : (decide (coordAt L a s < L) && decide (coordAt L b s < L)
        && decide (coordAt L c s < L)) = true
    · rw [if_pos hc] at hf
      have hp : (a, b, c, s) = q := Option.some.inj hf
      rw [← hp]
      exact ⟨rfl, rfl, rfl⟩
    · rw [if_neg hc] at hf
      exact nomatch (show (none : Option (Nat × Nat × Nat × Nat)) = some q from hf)
  · rw [if_neg hab] at hq
    exact nomatch hq

/-- The cube list holds each cube once. -/
theorem cubeList_distinct (d L : Nat) : distinctList (cubeList d L) := by
  intro x hx
  show countOf x ((List.range d).flatMap (fun a => (List.range d).flatMap (fun b =>
    (List.range d).flatMap (fun c =>
      if a < b && b < c then
        (sites d L).filterMap (fun s =>
          if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L
          then some (a, b, c, s) else none)
      else [])))) ≤ 1
  rw [countOf_flatMap]
  refine famFold_le_one_at _ x.1 (List.range d) ?_ ?_
    (distinctList_all (distinctList_range d) x.1)
  · intro a _ hne
    refine countOf_zero_of_not_mem (fun hm => hne ?_)
    obtain ⟨b, _, hb⟩ := mem_flatMap_of _ _ _ hm
    obtain ⟨c, _, hc⟩ := mem_flatMap_of _ _ _ hb
    exact (cube_mem_triple d L a b c x hc).1.symm
  · rw [countOf_flatMap]
    refine famFold_le_one_at _ x.2.1 (List.range d) ?_ ?_
      (distinctList_all (distinctList_range d) x.2.1)
    · intro b _ hne
      refine countOf_zero_of_not_mem (fun hm => hne ?_)
      obtain ⟨c, _, hc⟩ := mem_flatMap_of _ _ _ hm
      exact (cube_mem_triple d L x.1 b c x hc).2.1.symm
    · rw [countOf_flatMap]
      refine famFold_le_one_at _ x.2.2.1 (List.range d) ?_ ?_
        (distinctList_all (distinctList_range d) x.2.2.1)
      · intro c _ hne
        refine countOf_zero_of_not_mem (fun hm => hne ?_)
        exact (cube_mem_triple d L x.1 x.2.1 c x hm).2.2.symm
      · by_cases hab : (decide (x.1 < x.2.1) && decide (x.2.1 < x.2.2.1)) = true
        · rw [if_pos hab]
          refine countOf_filterMap_le_one _ x (sites d L)
            (fun a => distinctList_all (distinctList_range _) a) ?_
          intro a b _ _ hfa hfb
          have ha : a = x.2.2.2 := by
            by_cases hca : (decide (coordAt L x.1 a < L) && decide (coordAt L x.2.1 a < L)
              && decide (coordAt L x.2.2.1 a < L)) = true
            · rw [if_pos hca] at hfa
              exact congrArg (fun q : Nat × Nat × Nat × Nat => q.2.2.2) (Option.some.inj hfa)
            · rw [if_neg hca] at hfa
              exact nomatch (show (none : Option (Nat × Nat × Nat × Nat)) = some x from hfa)
          have hb : b = x.2.2.2 := by
            by_cases hcb : (decide (coordAt L x.1 b < L) && decide (coordAt L x.2.1 b < L)
              && decide (coordAt L x.2.2.1 b < L)) = true
            · rw [if_pos hcb] at hfb
              exact congrArg (fun q : Nat × Nat × Nat × Nat => q.2.2.2) (Option.some.inj hfb)
            · rw [if_neg hcb] at hfb
              exact nomatch (show (none : Option (Nat × Nat × Nat × Nat)) = some x from hfb)
          rw [ha, hb]
        · rw [if_neg hab]
          exact Nat.zero_le 1

/-- The cube at a place keys to its place. -/
theorem cubeKey_of_getAt (d L c : Nat) (hc : c < cubeCount d L) :
    cubeKey d L (getAt (0, 0, 0, 0) (cubeList d L) c).1 (getAt (0, 0, 0, 0) (cubeList d L) c).2.1
      (getAt (0, 0, 0, 0) (cubeList d L) c).2.2.1 (getAt (0, 0, 0, 0) (cubeList d L) c).2.2.2 = c := by
  have hx : getAt (0, 0, 0, 0) (cubeList d L) c ∈ cubeList d L :=
    mem_getAt (0, 0, 0, 0) (cubeList d L) c hc
  generalize hxe : getAt (0, 0, 0, 0) (cubeList d L) c = x at hx
  have hcount : countOf x (cubeList d L) = 1 :=
    Nat.le_antisymm (cubeList_distinct d L x hx) (countOf_pos_of_mem hx)
  have hfilt : ((cubeList d L).filter (fun b => quadBeq x b)).length = 1 := by
    rw [length_filterBy]
    refine Eq.trans ?_ hcount
    show famFold Nat.add 0 (fun a => cond (quadBeq x a) 1 0) (cubeList d L)
      = famFold Nat.add 0 (fun a => cond (decide (x = a)) 1 0) (cubeList d L)
    refine famFold_congr_members Nat.add 0 _ _ (cubeList d L) (fun a _ => ?_)
    cases hpa : quadBeq x a with
    | true =>
      rw [quadBeq_read x a hpa, decide_eq_true rfl]
    | false =>
      have hne : ¬ x = a := fun h => by
        rw [h, quadBeq_refl] at hpa
        exact Bool.noConfusion hpa
      rw [decide_eq_false hne]
  have h := (posBy_once quadBeq x (cubeList d L) hfilt c hc).1 (by
    show quadBeq x (getAt (0, 0, 0, 0) (cubeList d L) c) = true
    rw [hxe]
    exact quadBeq_refl x)
  cases x with
  | mk a q' =>
    cases q' with
    | mk b q'' =>
      cases q'' with
      | mk c' s => exact h

/-! The four-cell list: its members, and a read over it folds over the
direction quadruples in order and the corners. -/

/-- A member of the four-cell list: four directions in order below the
count at a corner of the box with the four coordinates below the
side. -/
theorem fourCell_of_mem (d L : Nat) (f : Nat × Nat × Nat × Nat × Nat) (h : f ∈ fourCellList d L) :
    f.1 < f.2.1 ∧ f.2.1 < f.2.2.1 ∧ f.2.2.1 < f.2.2.2.1 ∧ f.2.2.2.1 < d
      ∧ f.2.2.2.2 < (L + 1) ^ d
      ∧ coordAt L f.1 f.2.2.2.2 < L ∧ coordAt L f.2.1 f.2.2.2.2 < L
      ∧ coordAt L f.2.2.1 f.2.2.2.2 < L ∧ coordAt L f.2.2.2.1 f.2.2.2.2 < L := by
  obtain ⟨a, _, ha⟩ := mem_flatMap_of _ _ _ h
  obtain ⟨b, _, hb⟩ := mem_flatMap_of _ _ _ ha
  obtain ⟨c, _, hc⟩ := mem_flatMap_of _ _ _ hb
  obtain ⟨e, he, he'⟩ := mem_flatMap_of _ _ _ hc
  have hed : e < d := ltOfMemRange he
  by_cases habc : (decide (a < b) && decide (b < c) && decide (c < e)) = true
  · rw [if_pos habc] at he'
    obtain ⟨s, hs, hf⟩ := mem_filterMap_of _ _ _ he'
    have hsd : s < (L + 1) ^ d := ltOfMemRange hs
    by_cases hco : (decide (coordAt L a s < L) && decide (coordAt L b s < L)
        && decide (coordAt L c s < L) && decide (coordAt L e s < L)) = true
    · rw [if_pos hco] at hf
      have hp : (a, b, c, e, s) = f := Option.some.inj hf
      rw [← hp]
      have h1 := andSplitB habc
      have h1' := andSplitB h1.1
      have h2 := andSplitB hco
      have h3 := andSplitB h2.1
      have h4 := andSplitB h3.1
      exact ⟨of_decide_eq_true h1'.1, of_decide_eq_true h1'.2, of_decide_eq_true h1.2, hed, hsd,
        of_decide_eq_true h4.1, of_decide_eq_true h4.2, of_decide_eq_true h3.2,
        of_decide_eq_true h2.2⟩
    · rw [if_neg hco] at hf
      exact nomatch (show (none : Option (Nat × Nat × Nat × Nat × Nat)) = some f from hf)
  · rw [if_neg habc] at he'
    exact nomatch he'

/-- A read over the four-cell places is the read over the list. -/
theorem bsum_fourCell_places (d L : Nat) (F : Nat × Nat × Nat × Nat × Nat → BPair) :
    bsum (fun f => F (getAt (0, 0, 0, 0, 0) (fourCellList d L) f)) (List.range (fourCellCount d L))
      = bsum F (fourCellList d L) := by
  rw [← bsum_map F (getAt (0, 0, 0, 0, 0) (fourCellList d L)) (List.range (fourCellCount d L)),
    range_map_getAt (0, 0, 0, 0, 0) (fourCellCount d L) (fourCellList d L) rfl]

/-- A read over the four-cell list folds over the direction quadruples
in order and the sites at the corners. -/
theorem bsum_fourCell_quads (d L : Nat) (F : Nat × Nat × Nat × Nat × Nat → BPair) :
    (bsum F (fourCellList d L)).oneValue
      (bsum (fun a => bsum (fun b => bsum (fun c => bsum (fun e =>
        if a < b && b < c && c < e then
          bsum (fun s => if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L
              && coordAt L e s < L then F (a, b, c, e, s) else BPair.unit)
            (List.range ((L + 1) ^ d))
        else BPair.unit) (List.range d)) (List.range d)) (List.range d)) (List.range d)) := by
  delta fourCellList
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun a _ => ?_)
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun b _ => ?_)
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun c _ => ?_)
  refine BPair.oneValue_trans (famFold_flatMap_ov bpairFoldLaws F _ (List.range d)) ?_
  refine bsum_congr_range_ov _ _ d (fun e _ => ?_)
  cases habc : (decide (a < b) && decide (b < c) && decide (c < e)) with
  | true =>
    refine BPair.oneValue_trans (famFold_filterMap_ov bpairFoldLaws _ F (sites d L)) ?_
    refine bsum_congr_range_ov _ _ ((L + 1) ^ d) (fun s _ => ?_)
    cases hco : (decide (coordAt L a s < L) && decide (coordAt L b s < L)
        && decide (coordAt L c s < L) && decide (coordAt L e s < L)) with
    | true => exact BPair.oneValue_refl _
    | false => exact BPair.oneValue_refl _
  | false => exact BPair.oneValue_refl _

/-! The four-cells' boundaries' shape and entries, the two Grams'
shapes, and the boundaries' fold read `N N₄ ≡ 0` at every window. -/

/-- The four-cells' boundaries' row count is the cubes'. -/
theorem fourCellBd_length (d L : Nat) : (fourCellBd d L).length = cubeCount d L := by
  show ((List.range (cubeCount d L)).map _).length = _
  rw [ground.length_map, ground.length_range]

/-- The four-cells' boundaries' rows sit at the four-cells' count. -/
theorem fourCellBd_rows (d L : Nat) : rowsLen (fourCellCount d L) (fourCellBd d L) := by
  refine rowsLen_map _ _ _ (fun c _ => ?_)
  show ((fourCellList d L).map _).length = _
  rw [ground.length_map]
  rfl

/-- The four-cells' boundaries' entry at a cube's place and a
four-cell's place: the cubes' sign of the four-cell at the cube. -/
theorem fourCellBd_entry (d L c f : Nat) (hc : c < cubeCount d L) (hf : f < fourCellCount d L) :
    getAt BPair.unit (getAt [] (fourCellBd d L) c) f
      = faceSign (fourCellCubes d L (getAt (0, 0, 0, 0, 0) (fourCellList d L) f)) c := by
  show getAt BPair.unit (getAt [] ((List.range (cubeCount d L)).map (fun c =>
    (fourCellList d L).map (fun F => faceSign (fourCellCubes d L F) c))) c) f = _
  rw [getAt_map 0 [] _ _ c (by rw [ground.length_range]; exact hc), getAt_range _ c hc,
    getAt_map (0, 0, 0, 0, 0) BPair.unit _ _ f hf]

/-- The cubes' Gram's count is the cubes'. -/
theorem cubesGram_length (d L : Nat) : (cubesGram d L).length = cubeCount d L := by
  show (gramBy dotP (transposeM (cubeBd d L))).length = _
  rw [length_gramBy, cubeBdT_length]

/-- The cubes' Gram's rows read the cubes' count. -/
theorem cubesGram_rows (d L : Nat) : rowsLen (cubeCount d L) (cubesGram d L) := by
  show rowsLen _ (gramBy dotP (transposeM (cubeBd d L)))
  rw [← cubeBdT_length d L]
  exact rowsLen_gramBy _ _

/-- The four-cells' boundaries' Gram's count is the cubes'. -/
theorem fourCellGram_length (d L : Nat) : (fourCellGram d L).length = cubeCount d L := by
  show (gramBy dotP (fourCellBd d L)).length = _
  rw [length_gramBy, fourCellBd_length]

/-- The four-cells' boundaries' Gram's rows read the cubes' count. -/
theorem fourCellGram_rows (d L : Nat) : rowsLen (cubeCount d L) (fourCellGram d L) := by
  show rowsLen _ (gramBy dotP (fourCellBd d L))
  rw [← fourCellBd_length d L]
  exact rowsLen_gramBy _ _

/-- The boundaries' fold at a four-cell and a plaquette: the eight
cubes' faces' signs at the plaquette fold to the sum's unit, each
plaquette of the four-cell on two cubes at exchanged signs. -/
theorem bdEntry4 (d L : Nat) (f : Nat × Nat × Nat × Nat × Nat) (hf : f ∈ fourCellList d L)
    (p : Nat) (hp : p < plaqCount d L) :
    (bsum (fun c => getAt BPair.unit (getAt [] (cubeBd d L) p) c * faceSign (fourCellCubes d L f) c)
      (List.range (cubeCount d L))).oneValue BPair.unit := by
  have hfl := fourCell_of_mem d L f hf
  have hpl := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
  have hpk := plaqKey_of_getAt d L p hp
  generalize hP : getAt (0, 0, 0) (plaqList d L) p = P at hpl hpk
  obtain ⟨hak', hk'd, hs'd, hca', hck'⟩ := hpl
  cases P with
  | mk a' q1 =>
  cases q1 with
  | mk k' s' =>
  subst hpk
  cases f with
  | mk a f1 =>
  cases f1 with
  | mk b f2 =>
  cases f2 with
  | mk c' f3 =>
  cases f3 with
  | mk e s =>
  obtain ⟨hab, hbc, hce, hed, hsd, hca, hcb, hcc, hcE⟩ := hfl
  have hcd : c' < d := Nat.lt_trans hce hed
  have hbd : b < d := Nat.lt_trans hbc hcd
  have had : a < d := Nat.lt_trans hab hbd
  have hac : a < c' := Nat.lt_trans hab hbc
  have hae : a < e := Nat.lt_trans hac hce
  have hbe : b < e := Nat.lt_trans hbc hce
  have nab : ¬ a = b := Nat.ne_of_lt hab
  have nac : ¬ a = c' := Nat.ne_of_lt hac
  have nae : ¬ a = e := Nat.ne_of_lt hae
  have nbc : ¬ b = c' := Nat.ne_of_lt hbc
  have nbe : ¬ b = e := Nat.ne_of_lt hbe
  have nce : ¬ c' = e := Nat.ne_of_lt hce
  have sE := stepAt_lt d L e s hed hsd hcE
  have sC := stepAt_lt d L c' s hcd hsd hcc
  have sB := stepAt_lt d L b s hbd hsd hcb
  have sA := stepAt_lt d L a s had hsd hca
  have caE : coordAt L a (stepAt L e s) < L := by
    rw [coordAt_step_ne L e a s hcE nae]
    exact hca
  have cbE : coordAt L b (stepAt L e s) < L := by
    rw [coordAt_step_ne L e b s hcE nbe]
    exact hcb
  have ccE : coordAt L c' (stepAt L e s) < L := by
    rw [coordAt_step_ne L e c' s hcE nce]
    exact hcc
  have caC : coordAt L a (stepAt L c' s) < L := by
    rw [coordAt_step_ne L c' a s hcc nac]
    exact hca
  have cbC : coordAt L b (stepAt L c' s) < L := by
    rw [coordAt_step_ne L c' b s hcc nbc]
    exact hcb
  have ceC : coordAt L e (stepAt L c' s) < L := by
    rw [coordAt_step_ne L c' e s hcc (fun h => nce h.symm)]
    exact hcE
  have caB : coordAt L a (stepAt L b s) < L := by
    rw [coordAt_step_ne L b a s hcb nab]
    exact hca
  have ccB : coordAt L c' (stepAt L b s) < L := by
    rw [coordAt_step_ne L b c' s hcb (fun h => nbc h.symm)]
    exact hcc
  have ceB : coordAt L e (stepAt L b s) < L := by
    rw [coordAt_step_ne L b e s hcb (fun h => nbe h.symm)]
    exact hcE
  have cbA : coordAt L b (stepAt L a s) < L := by
    rw [coordAt_step_ne L a b s hca (fun h => nab h.symm)]
    exact hcb
  have ccA : coordAt L c' (stepAt L a s) < L := by
    rw [coordAt_step_ne L a c' s hca (fun h => nac h.symm)]
    exact hcc
  have ceA : coordAt L e (stepAt L a s) < L := by
    rw [coordAt_step_ne L a e s hca (fun h => nae h.symm)]
    exact hcE
  have K1 := cubeKey_lt d L a b c' s hab hbc hcd hsd hca hcb hcc
  have K2 := cubeKey_lt d L a b c' (stepAt L e s) hab hbc hcd sE caE cbE ccE
  have K3 := cubeKey_lt d L a b e s hab hbe hed hsd hca hcb hcE
  have K4 := cubeKey_lt d L a b e (stepAt L c' s) hab hbe hed sC caC cbC ceC
  have K5 := cubeKey_lt d L a c' e s hac hce hed hsd hca hcc hcE
  have K6 := cubeKey_lt d L a c' e (stepAt L b s) hac hce hed sB caB ccB ceB
  have K7 := cubeKey_lt d L b c' e s hbc hce hed hsd hcb hcc hcE
  have K8 := cubeKey_lt d L b c' e (stepAt L a s) hbc hce hed sA cbA ccA ceA
  show (bsum (fun c => getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s')) c
    * keyFoldB (fun a b => a == b) c (fourCellCubes d L (a, b, c', e, s)))
      (List.range (cubeCount d L))).oneValue BPair.unit
  refine BPair.oneValue_trans (bsum_keyFold_linear (cubeCount d L) _
    (fourCellCubes d L (a, b, c', e, s)) ?_) ?_
  · intro g hg
    cases hg with
    | head => exact K1
    | tail _ hg =>
      cases hg with
      | head => exact K2
      | tail _ hg =>
        cases hg with
        | head => exact K3
        | tail _ hg =>
          cases hg with
          | head => exact K4
          | tail _ hg =>
            cases hg with
            | head => exact K5
            | tail _ hg =>
              cases hg with
              | head => exact K6
              | tail _ hg =>
                cases hg with
                | head => exact K7
                | tail _ hg =>
                  cases hg with
                  | head => exact K8
                  | tail _ hg => nomatch hg
  · show (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s')) (cubeKey d L a b c' s)
        * BPair.ofNat 1
      + (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s'))
          (cubeKey d L a b c' (stepAt L e s)) * (BPair.ofNat 1).swap
      + (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s')) (cubeKey d L a b e s)
          * (BPair.ofNat 1).swap
      + (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s'))
          (cubeKey d L a b e (stepAt L c' s)) * BPair.ofNat 1
      + (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s')) (cubeKey d L a c' e s)
          * BPair.ofNat 1
      + (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s'))
          (cubeKey d L a c' e (stepAt L b s)) * (BPair.ofNat 1).swap
      + (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s')) (cubeKey d L b c' e s)
          * (BPair.ofNat 1).swap
      + (getAt BPair.unit (getAt [] (cubeBd d L) (plaqKey d L a' k' s'))
          (cubeKey d L b c' e (stepAt L a s)) * BPair.ofNat 1
      + BPair.unit)))))))).oneValue BPair.unit
    rw [cubeBd_entry d L _ _ hp K1, cubeKey_read d L a b c' s hab hbc hcd hsd hca hcb hcc,
      cubeBd_entry d L _ _ hp K2, cubeKey_read d L a b c' (stepAt L e s) hab hbc hcd sE caE cbE ccE,
      cubeBd_entry d L _ _ hp K3, cubeKey_read d L a b e s hab hbe hed hsd hca hcb hcE,
      cubeBd_entry d L _ _ hp K4, cubeKey_read d L a b e (stepAt L c' s) hab hbe hed sC caC cbC ceC,
      cubeBd_entry d L _ _ hp K5, cubeKey_read d L a c' e s hac hce hed hsd hca hcc hcE,
      cubeBd_entry d L _ _ hp K6, cubeKey_read d L a c' e (stepAt L b s) hac hce hed sB caB ccB ceB,
      cubeBd_entry d L _ _ hp K7, cubeKey_read d L b c' e s hbc hce hed hsd hcb hcc hcE,
      cubeBd_entry d L _ _ hp K8, cubeKey_read d L b c' e (stepAt L a s) hbc hce hed sA cbA ccA ceA,
      faceSign_read d L a b c' s a' k' s' hab hbc hcd hsd hca hcb hcc hak' hk'd hs'd hca' hck',
      faceSign_read d L a b c' (stepAt L e s) a' k' s' hab hbc hcd sE caE cbE ccE hak' hk'd hs'd hca' hck',
      faceSign_read d L a b e s a' k' s' hab hbe hed hsd hca hcb hcE hak' hk'd hs'd hca' hck',
      faceSign_read d L a b e (stepAt L c' s) a' k' s' hab hbe hed sC caC cbC ceC hak' hk'd hs'd hca' hck',
      faceSign_read d L a c' e s a' k' s' hac hce hed hsd hca hcc hcE hak' hk'd hs'd hca' hck',
      faceSign_read d L a c' e (stepAt L b s) a' k' s' hac hce hed sB caB ccB ceB hak' hk'd hs'd hca' hck',
      faceSign_read d L b c' e s a' k' s' hbc hce hed hsd hcb hcc hcE hak' hk'd hs'd hca' hck',
      faceSign_read d L b c' e (stepAt L a s) a' k' s' hbc hce hed sA cbA ccA ceA hak' hk'd hs'd hca' hck']
    delta faceInd
    show (((if a == a' && b == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if a == a' && b == k' && stepAt L c' s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && c' == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && c' == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && c' == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * BPair.ofNat 1 + (((if a == a' && b == k' && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit) + ((if a == a' && b == k' && stepAt L c' (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && c' == k' && stepAt L b (stepAt L e s) == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && c' == k' && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && c' == k' && stepAt L a (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * (BPair.ofNat 1).swap + (((if a == a' && b == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if a == a' && b == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * (BPair.ofNat 1).swap + (((if a == a' && b == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) + ((if a == a' && b == k' && stepAt L e (stepAt L c' s) == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && stepAt L c' s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && stepAt L b (stepAt L c' s) == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && e == k' && stepAt L a (stepAt L c' s) == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * BPair.ofNat 1 + (((if a == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if a == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * BPair.ofNat 1 + (((if a == a' && c' == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) + ((if a == a' && c' == k' && stepAt L e (stepAt L b s) == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if a == a' && e == k' && stepAt L c' (stepAt L b s) == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && stepAt L a (stepAt L b s) == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * (BPair.ofNat 1).swap + (((if b == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if b == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if b == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * (BPair.ofNat 1).swap + (((if b == a' && c' == k' && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) + ((if b == a' && c' == k' && stepAt L e (stepAt L a s) == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if b == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) + ((if b == a' && e == k' && stepAt L c' (stepAt L a s) == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) + ((if c' == a' && e == k' && stepAt L b (stepAt L a s) == s' then (BPair.ofNat 1).swap else BPair.unit) + (BPair.unit))))))) * BPair.ofNat 1 + (BPair.unit))))))))).oneValue BPair.unit
    rw [stepAt_comm L e c' s, stepAt_comm L e b s, stepAt_comm L c' b s, stepAt_comm L e a s,
      stepAt_comm L c' a s, stepAt_comm L b a s]
    refine BPair.oneValue_trans (polEqB
      [(if a == a' && b == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if a == a' && b == k' && stepAt L c' s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && c' == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && c' == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && c' == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && b == k' && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit),
      (if a == a' && b == k' && stepAt L c' (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && c' == k' && stepAt L b (stepAt L e s) == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && c' == k' && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && c' == k' && stepAt L a (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && b == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if a == a' && b == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && b == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit),
      (if a == a' && b == k' && stepAt L c' (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && stepAt L c' s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && stepAt L b (stepAt L c' s) == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && e == k' && stepAt L a (stepAt L c' s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if a == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && c' == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit),
      (if a == a' && c' == k' && stepAt L b (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if a == a' && e == k' && stepAt L b (stepAt L c' s) == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && stepAt L a (stepAt L b s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if b == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if b == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if b == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if b == a' && c' == k' && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit),
      (if b == a' && c' == k' && stepAt L a (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if b == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit),
      (if b == a' && e == k' && stepAt L a (stepAt L c' s) == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit),
      (if c' == a' && e == k' && stepAt L a (stepAt L b s) == s' then (BPair.ofNat 1).swap else BPair.unit),
      BPair.ofNat 1,
      (BPair.ofNat 1).swap,
      BPair.unit]
      (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.add (Pol.mon (Mon.var 2)) (Pol.add (Pol.mon (Mon.var 3)) (Pol.add (Pol.mon (Mon.var 4)) (Pol.add (Pol.mon (Mon.var 5)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 48))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 6)) (Pol.add (Pol.mon (Mon.var 7)) (Pol.add (Pol.mon (Mon.var 8)) (Pol.add (Pol.mon (Mon.var 9)) (Pol.add (Pol.mon (Mon.var 10)) (Pol.add (Pol.mon (Mon.var 11)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 12)) (Pol.add (Pol.mon (Mon.var 13)) (Pol.add (Pol.mon (Mon.var 14)) (Pol.add (Pol.mon (Mon.var 15)) (Pol.add (Pol.mon (Mon.var 16)) (Pol.add (Pol.mon (Mon.var 17)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 18)) (Pol.add (Pol.mon (Mon.var 19)) (Pol.add (Pol.mon (Mon.var 20)) (Pol.add (Pol.mon (Mon.var 21)) (Pol.add (Pol.mon (Mon.var 22)) (Pol.add (Pol.mon (Mon.var 23)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 48))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 24)) (Pol.add (Pol.mon (Mon.var 25)) (Pol.add (Pol.mon (Mon.var 26)) (Pol.add (Pol.mon (Mon.var 27)) (Pol.add (Pol.mon (Mon.var 28)) (Pol.add (Pol.mon (Mon.var 29)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 48))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 30)) (Pol.add (Pol.mon (Mon.var 31)) (Pol.add (Pol.mon (Mon.var 32)) (Pol.add (Pol.mon (Mon.var 33)) (Pol.add (Pol.mon (Mon.var 34)) (Pol.add (Pol.mon (Mon.var 35)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 36)) (Pol.add (Pol.mon (Mon.var 37)) (Pol.add (Pol.mon (Mon.var 38)) (Pol.add (Pol.mon (Mon.var 39)) (Pol.add (Pol.mon (Mon.var 40)) (Pol.add (Pol.mon (Mon.var 41)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 42)) (Pol.add (Pol.mon (Mon.var 43)) (Pol.add (Pol.mon (Mon.var 44)) (Pol.add (Pol.mon (Mon.var 45)) (Pol.add (Pol.mon (Mon.var 46)) (Pol.add (Pol.mon (Mon.var 47)) (Pol.mon (Mon.var 50)))))))) (Pol.mon (Mon.var 48))) (Pol.mon (Mon.var 50))))))))))
      (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 12)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 6)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 13)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 18)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 7)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 19)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 24)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 8)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 25)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 14)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 26)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 20)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 27)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 30)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 9)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 31)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 15)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 32)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 21)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 33)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 4)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 36)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 10)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 37)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 16)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 38)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 22)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 39)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 28)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 40)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 34)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 41)) (Pol.mon (Mon.var 49)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 5)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 42)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 11)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 43)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 17)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 44)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 23)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 45)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 29)) (Pol.mon (Mon.var 48))) (Pol.mul (Pol.mon (Mon.var 46)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 35)) (Pol.mon (Mon.var 49))) (Pol.mul (Pol.mon (Mon.var 47)) (Pol.mon (Mon.var 48)))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 48))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 48))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 48))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 49))) (Pol.add (Pol.mul (Pol.mon (Mon.var 50)) (Pol.mon (Mon.var 48))) (Pol.mon (Mon.var 50))))))))))))))))))))))))))))))))))
      (by decide +kernel)) ?_
    show (((if a == a' && b == k' && s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if a == a' && b == k' && s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if a == a' && b == k' && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if a == a' && b == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if a == a' && b == k' && stepAt L c' s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if a == a' && b == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if a == a' && b == k' && stepAt L c' (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if a == a' && b == k' && stepAt L c' (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if a == a' && c' == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if a == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if a == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if a == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if a == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if a == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if a == a' && e == k' && stepAt L c' s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if a == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if a == a' && c' == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if a == a' && c' == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if a == a' && c' == k' && stepAt L b (stepAt L e s) == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if a == a' && c' == k' && stepAt L b (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if a == a' && e == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if a == a' && e == k' && stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if a == a' && e == k' && stepAt L b (stepAt L c' s) == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if a == a' && e == k' && stepAt L b (stepAt L c' s) == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if b == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if b == a' && c' == k' && s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if b == a' && c' == k' && stepAt L e s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if b == a' && c' == k' && stepAt L e s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if b == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if b == a' && e == k' && s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if b == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if b == a' && e == k' && stepAt L c' s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if c' == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1 + (if c' == a' && e == k' && s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap) + (((if c' == a' && e == k' && stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) * (BPair.ofNat 1).swap + (if c' == a' && e == k' && stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap) + (((if b == a' && c' == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if b == a' && c' == k' && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if b == a' && c' == k' && stepAt L a (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if b == a' && c' == k' && stepAt L a (stepAt L e s) == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if b == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if b == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (((if b == a' && e == k' && stepAt L a (stepAt L c' s) == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if b == a' && e == k' && stepAt L a (stepAt L c' s) == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if c' == a' && e == k' && stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1 + (if c' == a' && e == k' && stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) * BPair.ofNat 1) + (((if c' == a' && e == k' && stepAt L a (stepAt L b s) == s' then (BPair.ofNat 1).swap else BPair.unit) * (BPair.ofNat 1).swap + (if c' == a' && e == k' && stepAt L a (stepAt L b s) == s' then (BPair.ofNat 1).swap else BPair.unit) * BPair.ofNat 1) + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1 + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1 + (BPair.unit))))))))))))))))))))))))))))))))).oneValue BPair.unit
    exact BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (pairNull _ _ _ _ _ (by decide +kernel))
      (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) (BPair.oneValue_refl _))))))))))))))))))))))))))))))))

/-- The four-cells' boundaries' fold read holds at every window:
`N N₄` reads the sum's unit entrywise. -/
theorem bdRead4_all (d L : Nat) : bdRead4 d L := by
  show matNull (matMul (cubeBd d L) (fourCellBd d L))
  have hNlen := cubeBd_length d L
  have hN := cubeBd_rows d L
  have hN4len := fourCellBd_length d L
  have hN4 := fourCellBd_rows d L
  refine matNull_map_idx [] _ (cubeBd d L) (fun i hi => ?_)
  have hi' : i < plaqCount d L := by rw [← hNlen]; exact hi
  refine poly.unitTail_of_getAt (fun k => ?_)
  cases Nat.lt_or_ge k (transposeM (fourCellBd d L)).length with
  | inr hk =>
    rw [getAt_over _ _ k (by rw [ground.length_map]; exact hk)]
    exact BPair.oneValue_refl _
  | inl hk =>
    have hk' : k < fourCellCount d L := by
      cases hF : fourCellBd d L with
      | nil =>
        rw [hF] at hk
        exact absurd hk (Nat.not_lt_zero k)
      | cons r t =>
        rw [hF] at hk hN4
        rw [length_transposeM _ hN4 (Nat.succ_pos _)] at hk
        exact hk
    rw [getAt_map [] BPair.unit _ _ k hk]
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    have hr1 : (getAt [] (cubeBd d L) i).length = cubeCount d L := rowsLen_getAt _ i hN hi
    have hr2 : (getAt [] (transposeM (fourCellBd d L)) k).length = cubeCount d L := by
      rw [rowsLen_getAt _ k (rowsLen_transposeM (fourCellBd d L)) hk]
      exact hN4len
    rw [dotP_fold (cubeCount d L) _ _ hr1 hr2]
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun c =>
      getAt BPair.unit (getAt [] (cubeBd d L) i) c
        * faceSign (fourCellCubes d L (getAt (0, 0, 0, 0, 0) (fourCellList d L) k)) c)
      (cubeCount d L) (fun c hc => ?_)) ?_
    · rw [getAt_transposeM BPair.unit (fourCellBd d L) hN4 k c hk' (by rw [hN4len]; exact hc),
        fourCellBd_entry d L c k hc hk']
      exact BPair.oneValue_refl _
    · exact bdEntry4 d L _ (mem_getAt (0, 0, 0, 0, 0) (fourCellList d L) k hk') i hi'


/-! The entries: the cubes' Gram's entry at two cubes, the first's six
faces' signs against the cubes' boundaries' six reads of the second
at the first's faces; the four-cells' boundaries' eight reads of a
four-cell at a cube; and the four-cells' Gram's entry. -/

/-- The cubes' Gram's entry at two cubes: the first's faces' signs
against the second's face reads at the first's six faces. -/
theorem cubesGram_entry (d L p q : Nat) (hp : p < cubeCount d L)
    (hq : q < cubeCount d L) :
    (getAt BPair.unit (getAt [] (cubesGram d L) p) q).oneValue
      (faceInd L (getAt (0, 0, 0, 0) (cubeList d L) q) (getAt (0, 0, 0, 0) (cubeList d L) p).1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.1 (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          * BPair.ofNat 1
      + (faceInd L (getAt (0, 0, 0, 0) (cubeList d L) q) (getAt (0, 0, 0, 0) (cubeList d L) p).1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.1
          (stepAt L (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1
            (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2) * (BPair.ofNat 1).swap
      + (faceInd L (getAt (0, 0, 0, 0) (cubeList d L) q) (getAt (0, 0, 0, 0) (cubeList d L) p).1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1 (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          * (BPair.ofNat 1).swap
      + (faceInd L (getAt (0, 0, 0, 0) (cubeList d L) q) (getAt (0, 0, 0, 0) (cubeList d L) p).1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1
          (stepAt L (getAt (0, 0, 0, 0) (cubeList d L) p).2.1
            (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2) * BPair.ofNat 1
      + (faceInd L (getAt (0, 0, 0, 0) (cubeList d L) q) (getAt (0, 0, 0, 0) (cubeList d L) p).2.1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1 (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          * BPair.ofNat 1
      + (faceInd L (getAt (0, 0, 0, 0) (cubeList d L) q) (getAt (0, 0, 0, 0) (cubeList d L) p).2.1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1
          (stepAt L (getAt (0, 0, 0, 0) (cubeList d L) p).1
            (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2) * (BPair.ofNat 1).swap
      + BPair.unit)))))) := by
  have hNlen := cubeBd_length d L
  have hN := cubeBd_rows d L
  have hpl := cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) p hp)
  have hql := cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) q hq)
  generalize hP : getAt (0, 0, 0, 0) (cubeList d L) p = P at hpl ⊢
  generalize hQ : getAt (0, 0, 0, 0) (cubeList d L) q = Q at hql ⊢
  obtain ⟨hab, hbc, hcd, hsd, hca, hcb, hcc⟩ := hpl
  obtain ⟨hxy, hyz, hzd, htd, htx, hty, htz⟩ := hql
  cases P with
  | mk a c1 =>
  cases c1 with
  | mk b c2 =>
  cases c2 with
  | mk c' s =>
  cases Q with
  | mk x q1 =>
  cases q1 with
  | mk y q2 =>
  cases q2 with
  | mk z t =>
  have hbd : b < d := Nat.lt_trans hbc hcd
  have had : a < d := Nat.lt_trans hab hbd
  have hac : a < c' := Nat.lt_trans hab hbc
  have nab : ¬ a = b := Nat.ne_of_lt hab
  have nac : ¬ a = c' := Nat.ne_of_lt hac
  have nbc : ¬ b = c' := Nat.ne_of_lt hbc
  have sC := stepAt_lt d L c' s hcd hsd hcc
  have sB := stepAt_lt d L b s hbd hsd hcb
  have sA := stepAt_lt d L a s had hsd hca
  have caC : coordAt L a (stepAt L c' s) < L := by
    rw [coordAt_step_ne L c' a s hcc nac]
    exact hca
  have cbC : coordAt L b (stepAt L c' s) < L := by
    rw [coordAt_step_ne L c' b s hcc nbc]
    exact hcb
  have caB : coordAt L a (stepAt L b s) < L := by
    rw [coordAt_step_ne L b a s hcb nab]
    exact hca
  have ccB : coordAt L c' (stepAt L b s) < L := by
    rw [coordAt_step_ne L b c' s hcb (fun h => nbc h.symm)]
    exact hcc
  have cbA : coordAt L b (stepAt L a s) < L := by
    rw [coordAt_step_ne L a b s hca (fun h => nab h.symm)]
    exact hcb
  have ccA : coordAt L c' (stepAt L a s) < L := by
    rw [coordAt_step_ne L a c' s hca (fun h => nac h.symm)]
    exact hcc
  have v1 := plaqKey_lt d L a b s hab hbd hsd hca hcb
  have v2 := plaqKey_lt d L a b (stepAt L c' s) hab hbd sC caC cbC
  have v3 := plaqKey_lt d L a c' s hac hcd hsd hca hcc
  have v4 := plaqKey_lt d L a c' (stepAt L b s) hac hcd sB caB ccB
  have v5 := plaqKey_lt d L b c' s hbc hcd hsd hcb hcc
  have v6 := plaqKey_lt d L b c' (stepAt L a s) hbc hcd sA cbA ccA
  have hNt : (transposeM (cubeBd d L)).length = cubeCount d L := cubeBdT_length d L
  have hpT : p < (transposeM (cubeBd d L)).length := by rw [hNt]; exact hp
  have hqT : q < (transposeM (cubeBd d L)).length := by rw [hNt]; exact hq
  have hr1 : (getAt [] (transposeM (cubeBd d L)) p).length = plaqCount d L := by
    rw [rowsLen_getAt _ p (rowsLen_transposeM (cubeBd d L)) hpT]
    exact hNlen
  have hr2 : (getAt [] (transposeM (cubeBd d L)) q).length = plaqCount d L := by
    rw [rowsLen_getAt _ q (rowsLen_transposeM (cubeBd d L)) hqT]
    exact hNlen
  show (getAt BPair.unit (getAt [] (gramM (transposeM (cubeBd d L))) p) q).oneValue _
  rw [gramM_entry _ p q hpT hqT, dotP_fold (plaqCount d L) _ _ hr1 hr2]
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun pl =>
    faceSign (cubeFaces d L (x, y, z, t)) pl
      * keyFoldB (fun a b => a == b) pl (cubeFaces d L (a, b, c', s)))
    (plaqCount d L) (fun pl hpl => by
      rw [getAt_transposeM BPair.unit (cubeBd d L) hN p pl hp (by rw [hNlen]; exact hpl),
        getAt_transposeM BPair.unit (cubeBd d L) hN q pl hq (by rw [hNlen]; exact hpl),
        cubeBd_entry d L pl p hpl hp, cubeBd_entry d L pl q hpl hq, hP, hQ]
      exact BPair.oneValue_of_eq (BPair.mul_comm _ _))) ?_
  refine BPair.oneValue_trans (bsum_keyFold_linear (plaqCount d L) _ _ ?_) ?_
  · intro f hf
    cases hf with
    | head => exact v1
    | tail _ hf =>
      cases hf with
      | head => exact v2
      | tail _ hf =>
        cases hf with
        | head => exact v3
        | tail _ hf =>
          cases hf with
          | head => exact v4
          | tail _ hf =>
            cases hf with
            | head => exact v5
            | tail _ hf =>
              cases hf with
              | head => exact v6
              | tail _ hf => nomatch hf
  show (faceSign (cubeFaces d L (x, y, z, t)) (plaqKey d L a b s) * BPair.ofNat 1
    + (faceSign (cubeFaces d L (x, y, z, t)) (plaqKey d L a b (stepAt L c' s)) * (BPair.ofNat 1).swap
    + (faceSign (cubeFaces d L (x, y, z, t)) (plaqKey d L a c' s) * (BPair.ofNat 1).swap
    + (faceSign (cubeFaces d L (x, y, z, t)) (plaqKey d L a c' (stepAt L b s)) * BPair.ofNat 1
    + (faceSign (cubeFaces d L (x, y, z, t)) (plaqKey d L b c' s) * BPair.ofNat 1
    + (faceSign (cubeFaces d L (x, y, z, t)) (plaqKey d L b c' (stepAt L a s)) * (BPair.ofNat 1).swap
    + BPair.unit)))))).oneValue _
  rw [faceSign_read d L x y z t a b s hxy hyz hzd htd htx hty htz hab hbd hsd hca hcb,
    faceSign_read d L x y z t a b (stepAt L c' s) hxy hyz hzd htd htx hty htz hab hbd sC caC cbC,
    faceSign_read d L x y z t a c' s hxy hyz hzd htd htx hty htz hac hcd hsd hca hcc,
    faceSign_read d L x y z t a c' (stepAt L b s) hxy hyz hzd htd htx hty htz hac hcd sB caB ccB,
    faceSign_read d L x y z t b c' s hxy hyz hzd htd htx hty htz hbc hcd hsd hcb hcc,
    faceSign_read d L x y z t b c' (stepAt L a s) hxy hyz hzd htd htx hty htz hbc hcd sA cbA ccA]
  exact BPair.oneValue_refl _

/-- The eight cube reads of a four-cell at a cube's data, the cubes at
`fourCellCubes`' signs. -/
private def cubeInd (L : Nat) (f : Nat × Nat × Nat × Nat × Nat) (a b c s : Nat) : BPair :=
  (if f.1 == a && f.2.1 == b && f.2.2.1 == c && f.2.2.2.2 == s then BPair.ofNat 1 else BPair.unit)
  + ((if f.1 == a && f.2.1 == b && f.2.2.1 == c && stepAt L f.2.2.2.1 f.2.2.2.2 == s
      then (BPair.ofNat 1).swap else BPair.unit)
  + ((if f.1 == a && f.2.1 == b && f.2.2.2.1 == c && f.2.2.2.2 == s then (BPair.ofNat 1).swap
      else BPair.unit)
  + ((if f.1 == a && f.2.1 == b && f.2.2.2.1 == c && stepAt L f.2.2.1 f.2.2.2.2 == s
      then BPair.ofNat 1 else BPair.unit)
  + ((if f.1 == a && f.2.2.1 == b && f.2.2.2.1 == c && f.2.2.2.2 == s then BPair.ofNat 1
      else BPair.unit)
  + ((if f.1 == a && f.2.2.1 == b && f.2.2.2.1 == c && stepAt L f.2.1 f.2.2.2.2 == s
      then (BPair.ofNat 1).swap else BPair.unit)
  + ((if f.2.1 == a && f.2.2.1 == b && f.2.2.2.1 == c && f.2.2.2.2 == s then (BPair.ofNat 1).swap
      else BPair.unit)
  + ((if f.2.1 == a && f.2.2.1 == b && f.2.2.2.1 == c && stepAt L f.1 f.2.2.2.2 == s
      then BPair.ofNat 1 else BPair.unit)
  + BPair.unit)))))))

/-- The cubes' sign at a valid four-cell and a valid cube's key reads
the eight cube reads at the data. -/
private theorem cubeSign_read (d L x y z w t a b c s : Nat) (hxy : x < y) (hyz : y < z)
    (hzw : z < w) (hw : w < d) (ht : t < (L + 1) ^ d) (htx : coordAt L x t < L)
    (hty : coordAt L y t < L) (htz : coordAt L z t < L) (htw : coordAt L w t < L)
    (hab : a < b) (hbc : b < c) (hc : c < d) (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L)
    (hcb : coordAt L b s < L) (hcc : coordAt L c s < L) :
    faceSign (fourCellCubes d L (x, y, z, w, t)) (cubeKey d L a b c s)
      = cubeInd L (x, y, z, w, t) a b c s := by
  have hzd : z < d := Nat.lt_trans hzw hw
  have hyd : y < d := Nat.lt_trans hyz hzd
  have hxd : x < d := Nat.lt_trans hxy hyd
  have hxz : x < z := Nat.lt_trans hxy hyz
  have hxw : x < w := Nat.lt_trans hxz hzw
  have hyw : y < w := Nat.lt_trans hyz hzw
  have nxy : ¬ x = y := Nat.ne_of_lt hxy
  have nxz : ¬ x = z := Nat.ne_of_lt hxz
  have nxw : ¬ x = w := Nat.ne_of_lt hxw
  have nyz : ¬ y = z := Nat.ne_of_lt hyz
  have nyw : ¬ y = w := Nat.ne_of_lt hyw
  have nzw : ¬ z = w := Nat.ne_of_lt hzw
  have sW := stepAt_lt d L w t hw ht htw
  have sZ := stepAt_lt d L z t hzd ht htz
  have sY := stepAt_lt d L y t hyd ht hty
  have sX := stepAt_lt d L x t hxd ht htx
  have cxW : coordAt L x (stepAt L w t) < L := by
    rw [coordAt_step_ne L w x t htw nxw]
    exact htx
  have cyW : coordAt L y (stepAt L w t) < L := by
    rw [coordAt_step_ne L w y t htw nyw]
    exact hty
  have czW : coordAt L z (stepAt L w t) < L := by
    rw [coordAt_step_ne L w z t htw nzw]
    exact htz
  have cxZ : coordAt L x (stepAt L z t) < L := by
    rw [coordAt_step_ne L z x t htz nxz]
    exact htx
  have cyZ : coordAt L y (stepAt L z t) < L := by
    rw [coordAt_step_ne L z y t htz nyz]
    exact hty
  have cwZ : coordAt L w (stepAt L z t) < L := by
    rw [coordAt_step_ne L z w t htz (fun h => nzw h.symm)]
    exact htw
  have cxY : coordAt L x (stepAt L y t) < L := by
    rw [coordAt_step_ne L y x t hty nxy]
    exact htx
  have czY : coordAt L z (stepAt L y t) < L := by
    rw [coordAt_step_ne L y z t hty (fun h => nyz h.symm)]
    exact htz
  have cwY : coordAt L w (stepAt L y t) < L := by
    rw [coordAt_step_ne L y w t hty (fun h => nyw h.symm)]
    exact htw
  have cyX : coordAt L y (stepAt L x t) < L := by
    rw [coordAt_step_ne L x y t htx (fun h => nxy h.symm)]
    exact hty
  have czX : coordAt L z (stepAt L x t) < L := by
    rw [coordAt_step_ne L x z t htx (fun h => nxz h.symm)]
    exact htz
  have cwX : coordAt L w (stepAt L x t) < L := by
    rw [coordAt_step_ne L x w t htx (fun h => nxw h.symm)]
    exact htw
  show (if cubeKey d L x y z t == cubeKey d L a b c s then BPair.ofNat 1 else BPair.unit)
    + ((if cubeKey d L x y z (stepAt L w t) == cubeKey d L a b c s then (BPair.ofNat 1).swap
        else BPair.unit)
    + ((if cubeKey d L x y w t == cubeKey d L a b c s then (BPair.ofNat 1).swap else BPair.unit)
    + ((if cubeKey d L x y w (stepAt L z t) == cubeKey d L a b c s then BPair.ofNat 1
        else BPair.unit)
    + ((if cubeKey d L x z w t == cubeKey d L a b c s then BPair.ofNat 1 else BPair.unit)
    + ((if cubeKey d L x z w (stepAt L y t) == cubeKey d L a b c s then (BPair.ofNat 1).swap
        else BPair.unit)
    + ((if cubeKey d L y z w t == cubeKey d L a b c s then (BPair.ofNat 1).swap else BPair.unit)
    + ((if cubeKey d L y z w (stepAt L x t) == cubeKey d L a b c s then BPair.ofNat 1
        else BPair.unit)
    + BPair.unit))))))) = _
  rw [cubeKey_beq d L x y z t a b c s hxy hyz hzd ht htx hty htz hab hbc hc hs hca hcb hcc,
    cubeKey_beq d L x y z (stepAt L w t) a b c s hxy hyz hzd sW cxW cyW czW hab hbc hc hs hca hcb hcc,
    cubeKey_beq d L x y w t a b c s hxy hyw hw ht htx hty htw hab hbc hc hs hca hcb hcc,
    cubeKey_beq d L x y w (stepAt L z t) a b c s hxy hyw hw sZ cxZ cyZ cwZ hab hbc hc hs hca hcb hcc,
    cubeKey_beq d L x z w t a b c s hxz hzw hw ht htx htz htw hab hbc hc hs hca hcb hcc,
    cubeKey_beq d L x z w (stepAt L y t) a b c s hxz hzw hw sY cxY czY cwY hab hbc hc hs hca hcb hcc,
    cubeKey_beq d L y z w t a b c s hyz hzw hw ht hty htz htw hab hbc hc hs hca hcb hcc,
    cubeKey_beq d L y z w (stepAt L x t) a b c s hyz hzw hw sX cyX czX cwX hab hbc hc hs hca hcb hcc]
  rfl

/-- The four-cells' Gram's entry at two cubes: the four-cells' signs
at both, folded over the four-cells. -/
theorem fourCellGram_entry (d L p q : Nat) (hp : p < cubeCount d L) (hq : q < cubeCount d L) :
    (getAt BPair.unit (getAt [] (fourCellGram d L) p) q).oneValue
      (bsum (fun f => faceSign (fourCellCubes d L f) p * faceSign (fourCellCubes d L f) q)
        (fourCellList d L)) := by
  have hNlen := fourCellBd_length d L
  have hN := fourCellBd_rows d L
  have hpN : p < (fourCellBd d L).length := by rw [hNlen]; exact hp
  have hqN : q < (fourCellBd d L).length := by rw [hNlen]; exact hq
  show (getAt BPair.unit (getAt [] (gramM (fourCellBd d L)) p) q).oneValue _
  rw [gramM_entry _ p q hpN hqN,
    dotP_fold (fourCellCount d L) _ _ (rowsLen_getAt _ p hN hpN) (rowsLen_getAt _ q hN hqN),
    ← bsum_fourCell_places d L
      (fun f => faceSign (fourCellCubes d L f) p * faceSign (fourCellCubes d L f) q)]
  refine bsum_congr_range_ov _ _ _ (fun f hf => ?_)
  rw [fourCellBd_entry d L p f hp hf, fourCellBd_entry d L q f hq hf]
  exact BPair.oneValue_refl _

/-! The four-cells holding a cube: the cubes' sign of every four-cell
at the cube against a read of the four-cell folds to the reads at the
four-cells holding it, two per further direction, the four-cell at the
cube's corner and the four-cell at the corner stepped back along the
direction, at the cubes' signs. -/

/-- The quadruple fold over the four-cells' data at a summand. -/
private def quadSum (d L : Nat) (T : Nat → Nat → Nat → Nat → Nat → BPair) : BPair :=
  bsum (fun x => bsum (fun y => bsum (fun z => bsum (fun w =>
    if decide (x < y) && decide (y < z) && decide (z < w) then
      bsum (fun t => if decide (coordAt L x t < L) && decide (coordAt L y t < L)
          && decide (coordAt L z t < L) && decide (coordAt L w t < L) then T x y z w t
        else BPair.unit) (List.range ((L + 1) ^ d))
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) (List.range d)

/-- The quadruple fold's congruence at valid four-cells. -/
private theorem quadSum_congr (d L : Nat) (T T' : Nat → Nat → Nat → Nat → Nat → BPair)
    (h : ∀ x y z w t, x < y → y < z → z < w → w < d → t < (L + 1) ^ d → coordAt L x t < L →
      coordAt L y t < L → coordAt L z t < L → coordAt L w t < L →
      (T x y z w t).oneValue (T' x y z w t)) :
    (quadSum d L T).oneValue (quadSum d L T') := by
  refine bsum_congr_range_ov _ _ d (fun x _ => bsum_congr_range_ov _ _ d (fun y _ =>
    bsum_congr_range_ov _ _ d (fun z _ => bsum_congr_range_ov _ _ d (fun w hw => ?_))))
  refine ite_congr_prop _ (fun hg => ?_)
  refine bsum_congr_range_ov _ _ _ (fun t ht => ite_congr_prop _ (fun hH => ?_))
  have hg' := andSplitB hg
  have hg'' := andSplitB hg'.1
  have hH' := andSplitB hH
  have hH'' := andSplitB hH'.1
  have hH''' := andSplitB hH''.1
  exact h x y z w t (of_decide_eq_true hg''.1) (of_decide_eq_true hg''.2) (of_decide_eq_true hg'.2)
    hw ht (of_decide_eq_true hH'''.1) (of_decide_eq_true hH'''.2) (of_decide_eq_true hH''.2)
    (of_decide_eq_true hH'.2)

/-- The quadruple fold splits over a summands' sum. -/
private theorem quadSum_add (d L : Nat) (T T' : Nat → Nat → Nat → Nat → Nat → BPair) :
    (quadSum d L (fun x y z w t => T x y z w t + T' x y z w t)).oneValue
      (quadSum d L T + quadSum d L T') := by
  refine bsum_split _ _ _ d (fun x _ => bsum_split _ _ _ d (fun y _ =>
    bsum_split _ _ _ d (fun z _ => bsum_split _ _ _ d (fun w _ => ?_))))
  refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (ite_add_unit _ _ _)
  refine BPair.oneValue_trans (bsum_congr_range_ov _ _ _ (fun t _ => ite_add_unit _ _ _))
    (foldB_add _ _ _)

/-- The quadruple fold at the unit summand reads the unit. -/
private theorem quadSum_unit (d L : Nat) :
    (quadSum d L (fun _ _ _ _ _ => BPair.unit)).oneValue BPair.unit := by
  refine famFold_unit_ov bpairFoldLaws _ (fun x => famFold_unit_ov bpairFoldLaws _ (fun y =>
    famFold_unit_ov bpairFoldLaws _ (fun z => famFold_unit_ov bpairFoldLaws _ (fun w => ?_) _) _) _) _
  cases (decide (x < y) && decide (y < z) && decide (z < w)) with
  | false => exact BPair.oneValue_refl _
  | true =>
    refine famFold_unit_ov bpairFoldLaws _ (fun t => ?_) _
    cases (decide (coordAt L x t < L) && decide (coordAt L y t < L) && decide (coordAt L z t < L)
        && decide (coordAt L w t < L)) with
    | false => exact BPair.oneValue_refl _
    | true => exact BPair.oneValue_refl _

/-- A triple fold of guarded units over the directions at a refused
first direction reads the unit. -/
private theorem tripleUnit (d : Nat) (P : Nat → Nat → Nat → Bool) (F : Nat → Nat → Nat → BPair)
    (h : ∀ y z w, (F y z w).oneValue BPair.unit) :
    (bsum (fun y => bsum (fun z => bsum (fun w => if P y z w then F y z w else BPair.unit)
      (List.range d)) (List.range d)) (List.range d)).oneValue BPair.unit :=
  famFold_unit_ov bpairFoldLaws _ (fun y => doubleUnit d (P y) (F y) (h y)) _

/-- The eight cube reads against a member split into the eight guarded
reads of the member at the cubes' signs. -/
private theorem cubeInd_mul (L x y z w t a b c s : Nat) (g : BPair) :
    (cubeInd L (x, y, z, w, t) a b c s * g).oneValue
      ((if x == a && y == b && z == c && t == s then g else BPair.unit)
      + ((if x == a && y == b && z == c && stepAt L w t == s then g.swap else BPair.unit)
      + ((if x == a && y == b && w == c && t == s then g.swap else BPair.unit)
      + ((if x == a && y == b && w == c && stepAt L z t == s then g else BPair.unit)
      + ((if x == a && z == b && w == c && t == s then g else BPair.unit)
      + ((if x == a && z == b && w == c && stepAt L y t == s then g.swap else BPair.unit)
      + ((if y == a && z == b && w == c && t == s then g.swap else BPair.unit)
      + ((if y == a && z == b && w == c && stepAt L x t == s then g else BPair.unit)
      + BPair.unit)))))))) := by
  delta cubeInd
  rw [BPair.right_distrib, BPair.right_distrib, BPair.right_distrib, BPair.right_distrib,
    BPair.right_distrib, BPair.right_distrib, BPair.right_distrib, BPair.right_distrib]
  exact BPair.add_congr (iteMul _ _).1 (BPair.add_congr (iteMul _ _).2
    (BPair.add_congr (iteMul _ _).2 (BPair.add_congr (iteMul _ _).1
    (BPair.add_congr (iteMul _ _).1 (BPair.add_congr (iteMul _ _).2
    (BPair.add_congr (iteMul _ _).2 (BPair.add_congr (iteMul _ _).1 (BPair.unit_mul g))))))))

/-- The first cube's fold: the four-cells at the corner holding the
cube as their lower cube, one per further direction beyond the
cube's. -/
private theorem cubeFold1 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if x == a && y == b && z == c && t == s then G (x, y, z, w, t)
        else BPair.unit)).oneValue
      (bsum (fun e => if decide (c < e) then
        (if decide (coordAt L e s < L) then G (a, b, c, e, s) else BPair.unit) else BPair.unit)
        (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if (decide (coordAt L x s < L) && decide (coordAt L y s < L)
            && decide (coordAt L z s < L) && decide (coordAt L w s < L))
          && (x == a && y == b && z == c) then G (x, y, z, w, s) else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (x == a && y == b && z == c) && t == s then G (x, y, z, w, t) else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_beq d L _ _ s hs
  -- the direction folds pick the type
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine tripleUnit d _ _ (fun y z w => ?_)
    rw [neBeqOf hxa]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun y _ hyb => ?_)) ?_
  · refine doubleUnit d _ _ (fun z w => ?_)
    rw [neBeqOf hyb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun z _ hzc => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun w => ?_) _
    cases (decide (a < b) && decide (b < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzc, Bool.and_false, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun w _ => ?_)
  rw [decide_eq_true hab, decide_eq_true hbc, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  repeat rw [Bool.true_and]
  exact BPair.oneValue_refl _

/-- The second cube's fold: the four-cells at the corner stepped back
along a further direction beyond the cube's, holding the cube as
their upper lower cube. -/
private theorem cubeFold2 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if x == a && y == b && z == c && stepAt L w t == s then (G (x, y, z, w, t)).swap
        else BPair.unit)).oneValue
      (bsum (fun e => if decide (c < e) then
        (if 0 < coordAt L e s then (G (a, b, c, e, s - (L + 1) ^ e)).swap else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  have hL : 0 < L + 1 := Nat.succ_pos L
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if 0 < coordAt L w s then
        (if (decide (coordAt L x (s - (L + 1) ^ w) < L) && decide (coordAt L y (s - (L + 1) ^ w) < L)
            && decide (coordAt L z (s - (L + 1) ^ w) < L) && decide (coordAt L w (s - (L + 1) ^ w) < L))
            && (x == a && y == b && z == c) then (G (x, y, z, w, (s - (L + 1) ^ w))).swap else BPair.unit)
        else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (x == a && y == b && z == c) && stepAt L w t == s then (G (x, y, z, w, t)).swap else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_step d L w _ (fun t ht => of_decide_eq_true (andSplitB (andSplitB ht).1).2) _ s hs
  -- the direction folds pick the type
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine tripleUnit d _ _ (fun y z w => ?_)
    rw [neBeqOf hxa]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun y _ hyb => ?_)) ?_
  · refine doubleUnit d _ _ (fun z w => ?_)
    rw [neBeqOf hyb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun z _ hzc => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun w => ?_) _
    cases (decide (a < b) && decide (b < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzc, Bool.and_false, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun w _ => ?_)
  rw [decide_eq_true hab, decide_eq_true hbc]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  refine ite_congr_prop _ (fun hg => ?_)
  refine ite_congr_prop _ (fun hpos => ?_)
  have hcw : c < w := of_decide_eq_true hg
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) w s hL hpos
  have hva : coordAt L a (s - (L + 1) ^ w) = coordAt L a s := hoff a (Nat.ne_of_lt (Nat.lt_trans (Nat.lt_trans hab hbc) hcw))
  have hvb : coordAt L b (s - (L + 1) ^ w) = coordAt L b s := hoff b (Nat.ne_of_lt (Nat.lt_trans hbc hcw))
  have hvc : coordAt L c (s - (L + 1) ^ w) = coordAt L c s := hoff c (Nat.ne_of_lt hcw)
  have hvv : coordAt L w (s - (L + 1) ^ w) < L := by
    have h := baseDigit_lt (L + 1) w s hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  rw [hva, hvb, hvc, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc,
    decide_eq_true hvv, iteB_of_true]
  · exact BPair.oneValue_refl _
  · rfl

/-- The third cube's fold: the four-cells at the corner holding the
cube as their outer-upper cube, one per direction between the cube's
second and third. -/
private theorem cubeFold3 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if x == a && y == b && w == c && t == s then (G (x, y, z, w, t)).swap
        else BPair.unit)).oneValue
      (bsum (fun y => if decide (b < y) && decide (y < c) then
        (if decide (coordAt L y s < L) then (G (a, b, y, c, s)).swap else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if (decide (coordAt L x s < L) && decide (coordAt L y s < L)
            && decide (coordAt L z s < L) && decide (coordAt L w s < L))
          && (x == a && y == b && w == c) then (G (x, y, z, w, s)).swap else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (x == a && y == b && w == c) && t == s then (G (x, y, z, w, t)).swap else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_beq d L _ _ s hs
  -- the direction folds pick the type
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine tripleUnit d _ _ (fun y z w => ?_)
    rw [neBeqOf hxa]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun y _ hyb => ?_)) ?_
  · refine doubleUnit d _ _ (fun z w => ?_)
    rw [neBeqOf hyb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun z _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun w _ hwc => ?_)) ?_
  · cases (decide (a < b) && decide (b < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hwc, Bool.and_false, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hab, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  repeat rw [Bool.true_and]
  exact BPair.oneValue_refl _

/-- The fourth cube's fold: the four-cells at the corner stepped back
along a direction between the cube's second and third, holding the
cube as their upper outer-upper cube. -/
private theorem cubeFold4 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if x == a && y == b && w == c && stepAt L z t == s then G (x, y, z, w, t)
        else BPair.unit)).oneValue
      (bsum (fun y => if decide (b < y) && decide (y < c) then
        (if 0 < coordAt L y s then G (a, b, y, c, s - (L + 1) ^ y) else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  have hL : 0 < L + 1 := Nat.succ_pos L
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if 0 < coordAt L z s then
        (if (decide (coordAt L x (s - (L + 1) ^ z) < L) && decide (coordAt L y (s - (L + 1) ^ z) < L)
            && decide (coordAt L z (s - (L + 1) ^ z) < L) && decide (coordAt L w (s - (L + 1) ^ z) < L))
            && (x == a && y == b && w == c) then G (x, y, z, w, (s - (L + 1) ^ z)) else BPair.unit)
        else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (x == a && y == b && w == c) && stepAt L z t == s then G (x, y, z, w, t) else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_step d L z _ (fun t ht => of_decide_eq_true (andSplitB (andSplitB (andSplitB ht).1).1).2) _ s hs
  -- the direction folds pick the type
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine tripleUnit d _ _ (fun y z w => ?_)
    rw [neBeqOf hxa]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun y _ hyb => ?_)) ?_
  · refine doubleUnit d _ _ (fun z w => ?_)
    rw [neBeqOf hyb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun z _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun w _ hwc => ?_)) ?_
  · cases (decide (a < b) && decide (b < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hwc, Bool.and_false, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hab]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  refine ite_congr_prop _ (fun hg => ?_)
  refine ite_congr_prop _ (fun hpos => ?_)
  have hbz : b < z := of_decide_eq_true (andSplitB hg).1
  have hzc : z < c := of_decide_eq_true (andSplitB hg).2
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) z s hL hpos
  have hva : coordAt L a (s - (L + 1) ^ z) = coordAt L a s := hoff a (Nat.ne_of_lt (Nat.lt_trans hab hbz))
  have hvb : coordAt L b (s - (L + 1) ^ z) = coordAt L b s := hoff b (Nat.ne_of_lt hbz)
  have hvc : coordAt L c (s - (L + 1) ^ z) = coordAt L c s := hoff c (fun h => Nat.ne_of_lt hzc h.symm)
  have hvv : coordAt L z (s - (L + 1) ^ z) < L := by
    have h := baseDigit_lt (L + 1) z s hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  rw [hva, hvb, hvc, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc,
    decide_eq_true hvv, iteB_of_true]
  · exact BPair.oneValue_refl _
  · rfl

/-- The fifth cube's fold: the four-cells at the corner holding the
cube as their outer-lower cube, one per direction between the cube's
first and second. -/
private theorem cubeFold5 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if x == a && z == b && w == c && t == s then G (x, y, z, w, t)
        else BPair.unit)).oneValue
      (bsum (fun y => if decide (a < y) && decide (y < b) then
        (if decide (coordAt L y s < L) then G (a, y, b, c, s) else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if (decide (coordAt L x s < L) && decide (coordAt L y s < L)
            && decide (coordAt L z s < L) && decide (coordAt L w s < L))
          && (x == a && z == b && w == c) then G (x, y, z, w, s) else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (x == a && z == b && w == c) && t == s then G (x, y, z, w, t) else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_beq d L _ _ s hs
  -- the direction folds pick the type
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine tripleUnit d _ _ (fun y z w => ?_)
    rw [neBeqOf hxa]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun y _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun z _ hzb => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun w => ?_) _
    cases (decide (a < y) && decide (y < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun w _ hwc => ?_)) ?_
  · cases (decide (a < y) && decide (y < b) && decide (b < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hwc, Bool.and_false, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hbc, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  repeat rw [Bool.true_and]
  exact BPair.oneValue_refl _

/-- The sixth cube's fold: the four-cells at the corner stepped back
along a direction between the cube's first and second, holding the
cube as their upper outer-lower cube. -/
private theorem cubeFold6 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if x == a && z == b && w == c && stepAt L y t == s then (G (x, y, z, w, t)).swap
        else BPair.unit)).oneValue
      (bsum (fun y => if decide (a < y) && decide (y < b) then
        (if 0 < coordAt L y s then (G (a, y, b, c, s - (L + 1) ^ y)).swap else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  have hL : 0 < L + 1 := Nat.succ_pos L
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if 0 < coordAt L y s then
        (if (decide (coordAt L x (s - (L + 1) ^ y) < L) && decide (coordAt L y (s - (L + 1) ^ y) < L)
            && decide (coordAt L z (s - (L + 1) ^ y) < L) && decide (coordAt L w (s - (L + 1) ^ y) < L))
            && (x == a && z == b && w == c) then (G (x, y, z, w, (s - (L + 1) ^ y))).swap else BPair.unit)
        else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (x == a && z == b && w == c) && stepAt L y t == s then (G (x, y, z, w, t)).swap else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_step d L y _ (fun t ht => of_decide_eq_true (andSplitB (andSplitB (andSplitB (andSplitB ht).1).1).1).2) _ s hs
  -- the direction folds pick the type
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun x _ hxa => ?_)) ?_
  · refine tripleUnit d _ _ (fun y z w => ?_)
    rw [neBeqOf hxa]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine bsum_congr_range_ov _ _ d (fun y _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun z _ hzb => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun w => ?_) _
    cases (decide (a < y) && decide (y < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun w _ hwc => ?_)) ?_
  · cases (decide (a < y) && decide (y < b) && decide (b < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hwc, Bool.and_false, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hbc]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  refine ite_congr_prop _ (fun hg => ?_)
  refine ite_congr_prop _ (fun hpos => ?_)
  have hay : a < y := of_decide_eq_true (andSplitB hg).1
  have hyb : y < b := of_decide_eq_true (andSplitB hg).2
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) y s hL hpos
  have hva : coordAt L a (s - (L + 1) ^ y) = coordAt L a s := hoff a (Nat.ne_of_lt hay)
  have hvb : coordAt L b (s - (L + 1) ^ y) = coordAt L b s := hoff b (fun h => Nat.ne_of_lt hyb h.symm)
  have hvc : coordAt L c (s - (L + 1) ^ y) = coordAt L c s := hoff c (fun h => Nat.ne_of_lt (Nat.lt_trans hyb hbc) h.symm)
  have hvv : coordAt L y (s - (L + 1) ^ y) < L := by
    have h := baseDigit_lt (L + 1) y s hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  rw [hva, hvb, hvc, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc,
    decide_eq_true hvv, iteB_of_true]
  · exact BPair.oneValue_refl _
  · rfl

/-- The seventh cube's fold: the four-cells at the corner holding the
cube as their upper cube, one per direction below the cube's. -/
private theorem cubeFold7 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if y == a && z == b && w == c && t == s then (G (x, y, z, w, t)).swap
        else BPair.unit)).oneValue
      (bsum (fun x => if decide (x < a) then
        (if decide (coordAt L x s < L) then (G (x, a, b, c, s)).swap else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if (decide (coordAt L x s < L) && decide (coordAt L y s < L)
            && decide (coordAt L z s < L) && decide (coordAt L w s < L))
          && (y == a && z == b && w == c) then (G (x, y, z, w, s)).swap else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (y == a && z == b && w == c) && t == s then (G (x, y, z, w, t)).swap else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_beq d L _ _ s hs
  -- the direction folds pick the type
  refine bsum_congr_range_ov _ _ d (fun x _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun y _ hya => ?_)) ?_
  · refine doubleUnit d _ _ (fun z w => ?_)
    rw [neBeqOf hya]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun z _ hzb => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun w => ?_) _
    cases (decide (x < a) && decide (a < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun w _ hwc => ?_)) ?_
  · cases (decide (x < a) && decide (a < b) && decide (b < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hwc, Bool.and_false, Bool.and_false, iteB_false]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hab, decide_eq_true hbc, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  repeat rw [Bool.true_and]
  exact BPair.oneValue_refl _

/-- The eighth cube's fold: the four-cells at the corner stepped back
along a direction below the cube's, holding the cube as their upper
upper cube. -/
private theorem cubeFold8 (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (quadSum d L (fun x y z w t => if y == a && z == b && w == c && stepAt L x t == s then G (x, y, z, w, t)
        else BPair.unit)).oneValue
      (bsum (fun x => if decide (x < a) then
        (if 0 < coordAt L x s then G (x, a, b, c, s - (L + 1) ^ x) else BPair.unit)
        else BPair.unit) (List.range d)) := by
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  have hL : 0 < L + 1 := Nat.succ_pos L
  -- the site fold picks the corner
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun x => bsum (fun y => bsum (fun z =>
    bsum (fun w => if decide (x < y) && decide (y < z) && decide (z < w) then
      (if 0 < coordAt L x s then
        (if (decide (coordAt L x (s - (L + 1) ^ x) < L) && decide (coordAt L y (s - (L + 1) ^ x) < L)
            && decide (coordAt L z (s - (L + 1) ^ x) < L) && decide (coordAt L w (s - (L + 1) ^ x) < L))
            && (y == a && z == b && w == c) then G (x, y, z, w, (s - (L + 1) ^ x)) else BPair.unit)
        else BPair.unit)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)) d (fun x _ =>
      bsum_congr_range_ov _ _ d (fun y _ => bsum_congr_range_ov _ _ d (fun z _ =>
        bsum_congr_range_ov _ _ d (fun w _ => ite_congr_prop _ (fun _ => ?_)))))) ?_
  · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
      if (decide (coordAt L x t < L) && decide (coordAt L y t < L)
            && decide (coordAt L z t < L) && decide (coordAt L w t < L))
          && (y == a && z == b && w == c) && stepAt L x t == s then G (x, y, z, w, t) else BPair.unit) _
      (fun t _ => by
        rw [ite_ite_and, ← Bool.and_assoc]
        exact BPair.oneValue_refl _)) ?_
    exact bsum_site_step d L x _ (fun t ht => of_decide_eq_true (andSplitB (andSplitB (andSplitB (andSplitB ht).1).1).1).1) _ s hs
  -- the direction folds pick the type
  refine bsum_congr_range_ov _ _ d (fun x _ => ?_)
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun y _ hya => ?_)) ?_
  · refine doubleUnit d _ _ (fun z w => ?_)
    rw [neBeqOf hya]
    repeat rw [Bool.false_and]
    rw [Bool.and_false, iteB_false, ite_prop_unit]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun z _ hzb => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun w => ?_) _
    cases (decide (x < a) && decide (a < z) && decide (z < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hzb, Bool.and_false, Bool.false_and, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun w _ hwc => ?_)) ?_
  · cases (decide (x < a) && decide (a < b) && decide (b < w)) with
    | false => exact BPair.oneValue_refl _
    | true =>
      rw [neBeqOf hwc, Bool.and_false, Bool.and_false, iteB_false, ite_prop_unit]
      exact BPair.oneValue_refl _
  rw [decide_eq_true hab, decide_eq_true hbc]
  repeat rw [Bool.true_and]
  rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.and_true]
  refine ite_congr_prop _ (fun hg => ?_)
  refine ite_congr_prop _ (fun hpos => ?_)
  have hxa : x < a := of_decide_eq_true hg
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) x s hL hpos
  have hva : coordAt L a (s - (L + 1) ^ x) = coordAt L a s := hoff a (fun h => Nat.ne_of_lt hxa h.symm)
  have hvb : coordAt L b (s - (L + 1) ^ x) = coordAt L b s := hoff b (fun h => Nat.ne_of_lt (Nat.lt_trans hxa hab) h.symm)
  have hvc : coordAt L c (s - (L + 1) ^ x) = coordAt L c s := hoff c (fun h => Nat.ne_of_lt (Nat.lt_trans (Nat.lt_trans hxa hab) hbc) h.symm)
  have hvv : coordAt L x (s - (L + 1) ^ x) < L := by
    have h := baseDigit_lt (L + 1) x s hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  rw [hva, hvb, hvc, decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc,
    decide_eq_true hvv, iteB_of_true]
  · exact BPair.oneValue_refl _
  · rfl

/-- Eight members regroup at the sum's associativity, the unit joined. -/
private theorem regroup8 (A1 A2 A3 A4 A5 A6 A7 A8 : BPair) :
    (A1 + A2 + (A3 + A4 + (A5 + A6 + (A7 + A8)))).oneValue
      (A1 + (A2 + (A3 + (A4 + (A5 + (A6 + (A7 + (A8 + BPair.unit)))))))) := by
  rw [BPair.add_assoc A1 A2, BPair.add_assoc A3 A4, BPair.add_assoc A5 A6]
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (BPair.add_unit A8))))))))

/-- The four-cells holding a cube: the cubes' sign of every four-cell
at the cube's key against a read of the four-cell folds to the reads
at the four-cells holding it, two per further direction at the cubes'
signs, the four-cell at the cube's corner and the four-cell at the
corner stepped back along the direction, the second occupied exactly
where the corner's coordinate there is occupied. -/
theorem fourCells_holding (d L a b c s : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (G : Nat × Nat × Nat × Nat × Nat → BPair) :
    (bsum (fun f => faceSign (fourCellCubes d L f) (cubeKey d L a b c s) * G f)
      (fourCellList d L)).oneValue
      (bsum (fun e => if decide (c < e) then
          (if decide (coordAt L e s < L) then G (a, b, c, e, s) else BPair.unit)
          + (if 0 < coordAt L e s then (G (a, b, c, e, s - (L + 1) ^ e)).swap else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (b < y) && decide (y < c) then
          (if decide (coordAt L y s < L) then (G (a, b, y, c, s)).swap else BPair.unit)
          + (if 0 < coordAt L y s then G (a, b, y, c, s - (L + 1) ^ y) else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < b) then
          (if decide (coordAt L y s < L) then G (a, y, b, c, s) else BPair.unit)
          + (if 0 < coordAt L y s then (G (a, y, b, c, s - (L + 1) ^ y)).swap else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then (G (x, a, b, c, s)).swap else BPair.unit)
          + (if 0 < coordAt L x s then G (x, a, b, c, s - (L + 1) ^ x) else BPair.unit)
        else BPair.unit) (List.range d)))) := by
  refine BPair.oneValue_trans (bsum_fourCell_quads d L _) ?_
  show (quadSum d L (fun x y z w t => faceSign (fourCellCubes d L (x, y, z, w, t)) (cubeKey d L a b c s)
    * G (x, y, z, w, t))).oneValue _
  refine BPair.oneValue_trans (quadSum_congr d L _ (fun x y z w t =>
    (if x == a && y == b && z == c && t == s then G (x, y, z, w, t) else BPair.unit)
      + ((if x == a && y == b && z == c && stepAt L w t == s then (G (x, y, z, w, t)).swap
          else BPair.unit)
      + ((if x == a && y == b && w == c && t == s then (G (x, y, z, w, t)).swap else BPair.unit)
      + ((if x == a && y == b && w == c && stepAt L z t == s then G (x, y, z, w, t) else BPair.unit)
      + ((if x == a && z == b && w == c && t == s then G (x, y, z, w, t) else BPair.unit)
      + ((if x == a && z == b && w == c && stepAt L y t == s then (G (x, y, z, w, t)).swap
          else BPair.unit)
      + ((if y == a && z == b && w == c && t == s then (G (x, y, z, w, t)).swap else BPair.unit)
      + ((if y == a && z == b && w == c && stepAt L x t == s then G (x, y, z, w, t) else BPair.unit)
      + BPair.unit))))))))
    (fun x y z w t hxy hyz hzw hw ht htx hty htz htw => by
      rw [cubeSign_read d L x y z w t a b c s hxy hyz hzw hw ht htx hty htz htw hab hbc hc hs hca hcb hcc]
      exact cubeInd_mul L x y z w t a b c s _)) ?_
  refine BPair.oneValue_trans (quadSum_add d L _ _) ?_
  refine BPair.oneValue_trans (BPair.add_congr (cubeFold1 d L a b c s hab hbc hc hs hca hcb hcc G)
    (BPair.oneValue_trans (quadSum_add d L _ _)
    (BPair.add_congr (cubeFold2 d L a b c s hab hbc hc hs hca hcb hcc G)
    (BPair.oneValue_trans (quadSum_add d L _ _)
    (BPair.add_congr (cubeFold3 d L a b c s hab hbc hc hs hca hcb hcc G)
    (BPair.oneValue_trans (quadSum_add d L _ _)
    (BPair.add_congr (cubeFold4 d L a b c s hab hbc hc hs hca hcb hcc G)
    (BPair.oneValue_trans (quadSum_add d L _ _)
    (BPair.add_congr (cubeFold5 d L a b c s hab hbc hc hs hca hcb hcc G)
    (BPair.oneValue_trans (quadSum_add d L _ _)
    (BPair.add_congr (cubeFold6 d L a b c s hab hbc hc hs hca hcb hcc G)
    (BPair.oneValue_trans (quadSum_add d L _ _)
    (BPair.add_congr (cubeFold7 d L a b c s hab hbc hc hs hca hcb hcc G)
    (BPair.oneValue_trans (quadSum_add d L _ _)
    (BPair.add_congr (cubeFold8 d L a b c s hab hbc hc hs hca hcb hcc G)
    (quadSum_unit d L)))))))))))))))) ?_
  -- the pieces regroup at the four direction ranges
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (BPair.add_congr
    (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun e _ => ite_add_unit _ _ _)) (foldB_add _ _ _))
    (BPair.add_congr
      (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun y _ => ite_add_unit _ _ _)) (foldB_add _ _ _))
      (BPair.add_congr
        (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun y _ => ite_add_unit _ _ _)) (foldB_add _ _ _))
        (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun x _ => ite_add_unit _ _ _))
          (foldB_add _ _ _))))) ?_
  exact regroup8 _ _ _ _ _ _ _ _

/-! The Hodge fold at cubes: the consecutive differences along a
direction on a cube type's cubes, their squares' fold, the fold
summed over the cube types and the directions, and the fold's
matrix. -/

/-- The consecutive differences along a direction on a cube type's
cubes: the site-cube list, at a site the cube of the type at the
site against the cube at the site stepped back along the direction,
the balance partner, the row occupied throughout along a cube
direction (the Dirichlet fold's differences at the sum's unit beyond
both ends) and off the first position along a further direction (the
Neumann fold's interior differences). -/
def diffMat3 (d L a b c j : Nat) : Mat :=
  (sites d L).map (fun t =>
    (cubeList d L).map (fun q =>
      if ((j == a || j == b) || j == c) || decide (0 < coordAt L j t) then
        (if q.1 == a && q.2.1 == b && q.2.2.1 == c && q.2.2.2 == t then BPair.ofNat 1
          else BPair.unit)
        + (if q.1 == a && q.2.1 == b && q.2.2.1 == c && decide (0 < coordAt L j t)
            && stepAt L j q.2.2.2 == t then (BPair.ofNat 1).swap else BPair.unit)
      else BPair.unit))

/-- The differences' squares' fold along a direction on a cube type at
a cube vector: a Dirichlet fold along a cube direction, a Neumann fold
along a further one. -/
def diffFold3 (d L a b c j : Nat) (z : List BPair) : BPair :=
  dotN (matVec (diffMat3 d L a b c j) z) (matVec (diffMat3 d L a b c j) z)

/-- The Hodge fold at a cube vector: cube type by cube type the three
Dirichlet folds joined to the Neumann folds in the further
directions. -/
def hodgeFold3 (d L : Nat) (z : List BPair) : BPair :=
  bsum (fun a => bsum (fun b => bsum (fun c => if a < b && b < c then
    bsum (fun j => diffFold3 d L a b c j z) (List.range d) else BPair.unit) (List.range d))
    (List.range d)) (List.range d)

/-- The Hodge fold's matrix at cubes: the differences' Grams summed
over the cube types and the directions. -/
def hodgeMat3 (d L : Nat) : Mat :=
  msum (cubeCount d L) (fun a => msum (cubeCount d L) (fun b => msum (cubeCount d L) (fun c =>
    if a < b && b < c then
      msum (cubeCount d L) (fun j => matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j))
        (List.range d)
    else nullMat (cubeCount d L) (cubeCount d L)) (List.range d)) (List.range d)) (List.range d)

/-- The Hodge identity's read at cubes: the cubes' Gram joined to the
four-cells' boundaries' Gram reads the Hodge fold's matrix
entrywise. -/
def hodgeRead3 (d L : Nat) : Prop :=
  matOneValue (matAdd (cubesGram d L) (fourCellGram d L)) (hodgeMat3 d L)

instance instCornerwindow21 (d L : Nat) : Decidable (hodgeRead3 d L) :=
  inferInstanceAs (Decidable (matOneValue _ _))

/-- The differences' row count is the sites'. -/
theorem diffMat3_length (d L a b c j : Nat) : (diffMat3 d L a b c j).length = (L + 1) ^ d := by
  show ((List.range ((L + 1) ^ d)).map _).length = _
  rw [ground.length_map, ground.length_range]

/-- The differences' rows sit at the cubes' count. -/
theorem diffMat3_rows (d L a b c j : Nat) : rowsLen (cubeCount d L) (diffMat3 d L a b c j) := by
  refine rowsLen_map _ _ _ (fun t _ => ?_)
  show ((cubeList d L).map _).length = _
  rw [ground.length_map]
  rfl

/-- The differences' entry at a site and a cube's place. -/
theorem diffMat3_entry (d L a b c j t q : Nat) (ht : t < (L + 1) ^ d) (hq : q < cubeCount d L) :
    getAt BPair.unit (getAt [] (diffMat3 d L a b c j) t) q
      = (if ((j == a || j == b) || j == c) || decide (0 < coordAt L j t) then
          (if (getAt (0, 0, 0, 0) (cubeList d L) q).1 == a
              && (getAt (0, 0, 0, 0) (cubeList d L) q).2.1 == b
              && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.1 == c
              && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == t then BPair.ofNat 1 else BPair.unit)
          + (if (getAt (0, 0, 0, 0) (cubeList d L) q).1 == a
              && (getAt (0, 0, 0, 0) (cubeList d L) q).2.1 == b
              && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.1 == c && decide (0 < coordAt L j t)
              && stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == t
              then (BPair.ofNat 1).swap else BPair.unit)
        else BPair.unit) := by
  show getAt BPair.unit (getAt [] ((List.range ((L + 1) ^ d)).map (fun t =>
    (cubeList d L).map (fun q =>
      if ((j == a || j == b) || j == c) || decide (0 < coordAt L j t) then
        (if q.1 == a && q.2.1 == b && q.2.2.1 == c && q.2.2.2 == t then BPair.ofNat 1
          else BPair.unit)
        + (if q.1 == a && q.2.1 == b && q.2.2.1 == c && decide (0 < coordAt L j t)
            && stepAt L j q.2.2.2 == t then (BPair.ofNat 1).swap else BPair.unit)
      else BPair.unit))) t) q = _
  rw [getAt_map 0 [] _ _ t (by rw [ground.length_range]; exact ht), getAt_range _ t ht,
    getAt_map (0, 0, 0, 0) BPair.unit _ _ q hq]

/-- The differences' Gram's shape at a cube type and a direction. -/
private theorem diffGram3_shape (d L a b c j : Nat) :
    rowsLen (cubeCount d L) (matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j))
      ∧ (matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j)).length = cubeCount d L := by
  have hBl := diffMat3_length d L a b c j
  have hB := diffMat3_rows d L a b c j
  have hpos : 0 < (diffMat3 d L a b c j).length := by
    rw [hBl]
    exact Nat.pow_pos (Nat.succ_pos L)
  have hBt : (transposeM (diffMat3 d L a b c j)).length = cubeCount d L :=
    length_transposeM _ hB hpos
  refine ⟨?_, ?_⟩
  · rw [← hBt]
    exact rowsLen_matMul _ _
  · rw [length_matMul, hBt]

/-- The cube type's summand's shape. -/
private theorem hodgeType3_shape (d L a b c : Nat) :
    rowsLen (cubeCount d L) (if a < b && b < c then
        msum (cubeCount d L) (fun j => matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j))
          (List.range d) else nullMat (cubeCount d L) (cubeCount d L))
      ∧ (if a < b && b < c then
        msum (cubeCount d L) (fun j => matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j))
          (List.range d) else nullMat (cubeCount d L) (cubeCount d L)).length = cubeCount d L := by
  by_cases h : (decide (a < b) && decide (b < c)) = true
  · rw [if_pos h]
    exact msum_shape _ _ (fun j => diffGram3_shape d L a b c j) _
  · rw [if_neg h]
    exact ⟨rowsLen_nullMat _ _, length_nullMat _ _⟩

/-- The Hodge fold's matrix at cubes is square at the cubes' count. -/
theorem hodgeMat3_shape (d L : Nat) :
    rowsLen (cubeCount d L) (hodgeMat3 d L) ∧ (hodgeMat3 d L).length = cubeCount d L := by
  exact msum_shape _ _ (fun a => msum_shape _ _ (fun b =>
    msum_shape _ _ (hodgeType3_shape d L a b) _) _) _

/-- The Hodge fold's matrix's entry at cubes: the fold over the cube
types and the directions of the differences' Grams' entries. -/
theorem hodgeMat3_entry (d L p q : Nat) (hp : p < cubeCount d L) (hq : q < cubeCount d L) :
    getAt BPair.unit (getAt [] (hodgeMat3 d L) p) q
      = bsum (fun a => bsum (fun b => bsum (fun c => if a < b && b < c then
          bsum (fun j => getAt BPair.unit (getAt []
            (matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j)) p) q) (List.range d)
          else BPair.unit) (List.range d)) (List.range d)) (List.range d) := by
  show getAt BPair.unit (getAt [] (msum (cubeCount d L) (fun a => msum (cubeCount d L) (fun b =>
    msum (cubeCount d L) (fun c => if a < b && b < c then
      msum (cubeCount d L)
        (fun j => matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j)) (List.range d)
      else nullMat (cubeCount d L) (cubeCount d L)) (List.range d)) (List.range d)) (List.range d)) p) q
    = _
  rw [entry_msum _ _ p q hp hq _ (fun a _ => msum_shape _ _ (fun b =>
    msum_shape _ _ (hodgeType3_shape d L a b) _) _)]
  refine famFold_congr_members BPair.add BPair.unit _ _ (List.range d) (fun a _ => ?_)
  rw [entry_msum _ _ p q hp hq _ (fun b _ => msum_shape _ _ (hodgeType3_shape d L a b) _)]
  refine famFold_congr_members BPair.add BPair.unit _ _ (List.range d) (fun b _ => ?_)
  rw [entry_msum _ _ p q hp hq _ (fun c _ => hodgeType3_shape d L a b c)]
  refine famFold_congr_members BPair.add BPair.unit _ _ (List.range d) (fun c _ => ?_)
  by_cases h : (decide (a < b) && decide (b < c)) = true
  · rw [if_pos h, if_pos h, entry_msum _ _ p q hp hq _ (fun j _ => diffGram3_shape d L a b c j)]
    rfl
  · rw [if_neg h, if_neg h]
    show getAt BPair.unit (getAt [] (List.replicate (cubeCount d L)
      (List.replicate (cubeCount d L) BPair.unit)) p) q = _
    rw [getAt_replicate [] _ _ p hp, getAt_replicate BPair.unit _ _ q hq]


/-- The differences' entries' product at a site and two cubes' data:
the four guarded reads at the cube type's guards. -/
private theorem diffProd3 (L a b c j t a1 b1 c1 s a2 b2 c2 s' : Nat) :
    ((if ((j == a || j == b) || j == c) || decide (0 < coordAt L j t) then
      (if (a1 == a && b1 == b && c1 == c) && s == t then BPair.ofNat 1 else BPair.unit)
      + (if ((a1 == a && b1 == b && c1 == c) && decide (0 < coordAt L j t)) && stepAt L j s == t
          then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
    * (if ((j == a || j == b) || j == c) || decide (0 < coordAt L j t) then
      (if (a2 == a && b2 == b && c2 == c) && s' == t then BPair.ofNat 1 else BPair.unit)
      + (if ((a2 == a && b2 == b && c2 == c) && decide (0 < coordAt L j t)) && stepAt L j s' == t
          then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)).oneValue
      (if (a1 == a && b1 == b && c1 == c) && (a2 == a && b2 == b && c2 == c) then
        (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t)) && (s == t && s' == t)
          then BPair.ofNat 1 else BPair.unit)
        + ((if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
              && ((decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t)
          then (BPair.ofNat 1).swap else BPair.unit)
        + ((if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
              && (s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t))
          then (BPair.ofNat 1).swap else BPair.unit)
        + (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
              && ((decide (0 < coordAt L j t) && stepAt L j s == t)
                && (decide (0 < coordAt L j t) && stepAt L j s' == t))
          then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) := by
  cases hPg : (a1 == a && b1 == b && c1 == c) with
  | false =>
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    cases (((j == a || j == b) || j == c) || decide (0 < coordAt L j t)) with
    | false => exact BPair.unit_mul _
    | true =>
      show ((BPair.unit + BPair.unit) * _).oneValue BPair.unit
      exact BPair.oneValue_trans (BPair.mul_congr_left (BPair.add_unit _)) (BPair.unit_mul _)
  | true =>
  cases hQg : (a2 == a && b2 == b && c2 == c) with
  | false =>
    repeat rw [Bool.and_false]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    cases (((j == a || j == b) || j == c) || decide (0 < coordAt L j t)) with
    | false => exact BPair.mul_unit _
    | true =>
      show (_ * (BPair.unit + BPair.unit)).oneValue BPair.unit
      exact BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _) (BPair.add_unit _))
        (BPair.mul_unit _)
  | true =>
  repeat rw [Bool.true_and]
  rw [iteB_true]
  refine BPair.oneValue_trans (ite_mul_ite_and _ _ _ _) ?_
  rw [Bool.and_self]
  refine BPair.oneValue_trans (ite_congr_prop (A' :=
    ((if s == t && s' == t then BPair.ofNat 1 * BPair.ofNat 1 else BPair.unit)
    + (if (decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t
        then (BPair.ofNat 1).swap * BPair.ofNat 1 else BPair.unit))
    + ((if s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t)
        then BPair.ofNat 1 * (BPair.ofNat 1).swap else BPair.unit)
    + (if (decide (0 < coordAt L j t) && stepAt L j s == t)
          && (decide (0 < coordAt L j t) && stepAt L j s' == t)
        then (BPair.ofNat 1).swap * (BPair.ofNat 1).swap else BPair.unit))) _ (fun _ => ?_)) ?_
  · rw [BPair.left_distrib, BPair.right_distrib, BPair.right_distrib]
    exact BPair.add_congr (BPair.add_congr (ite_mul_ite_and _ _ _ _) (ite_mul_ite_and _ _ _ _))
      (BPair.add_congr (ite_mul_ite_and _ _ _ _) (ite_mul_ite_and _ _ _ _))
  refine BPair.oneValue_trans (ite_add_unit _ _ _) ?_
  refine BPair.oneValue_trans (BPair.add_congr (ite_add_unit _ _ _) (ite_add_unit _ _ _)) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc _ _ _)) ?_
  refine BPair.add_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _))
    (ite_congr_prop _ (fun _ => BPair.ofNat_one_mul _))) ?_
  refine BPair.add_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _))
    (ite_congr_prop _ (fun _ => BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.mul_comm _ _))
      (BPair.ofNat_one_mul _)))) ?_
  refine BPair.add_congr (BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _))
    (ite_congr_prop _ (fun _ => BPair.ofNat_one_mul _))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (ite_ite_and _ _ _)) ?_
  exact ite_congr_prop _ (fun _ => swapOne_sq)

/-- The four guarded reads fold over the sites to the differences'
Gram's entry: the diagonal at the row's guard joined to the coordinate
below the side, the successor at a coordinate below the side and the
predecessor at an occupied coordinate. -/
private theorem diffSum_read3 (d L a b c j s s' : Nat) (hj : j < d) (hs : s < (L + 1) ^ d) :
    (bsum (fun t =>
      (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t)) && (s == t && s' == t)
        then BPair.ofNat 1 else BPair.unit)
      + ((if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t)
        then (BPair.ofNat 1).swap else BPair.unit)
      + ((if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
            && (s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t))
        then (BPair.ofNat 1).swap else BPair.unit)
      + (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j s == t)
              && (decide (0 < coordAt L j t) && stepAt L j s' == t))
        then BPair.ofNat 1 else BPair.unit)))) (List.range ((L + 1) ^ d))).oneValue
      ((if (((j == a || j == b) || j == c) || decide (0 < coordAt L j s)) && s' == s
          then BPair.ofNat 1 else BPair.unit)
      + ((if decide (coordAt L j s < L) && s' == stepAt L j s
          then (BPair.ofNat 1).swap else BPair.unit)
      + ((if decide (0 < coordAt L j s) && stepAt L j s' == s
          then (BPair.ofNat 1).swap else BPair.unit)
      + (if decide (coordAt L j s < L) && s' == s then BPair.ofNat 1 else BPair.unit)))) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  -- the two reads at the site itself
  have hS1 : (bsum (fun t => if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
      && (s == t && s' == t) then BPair.ofNat 1 else BPair.unit) (List.range ((L + 1) ^ d))).oneValue
      (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j s)) && s' == s
        then BPair.ofNat 1 else BPair.unit) := by
    refine BPair.oneValue_trans (bsum_range_at _ _ s _ hs (fun t _ ht =>
      (beqEqOf (andSplitB (andSplitB ht).2).1).symm)) ?_
    rw [eqBeqOf (rfl : s = s), Bool.true_and]
    exact BPair.oneValue_refl _
  have hS2 : (bsum (fun t => if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
      && (s == t && (decide (0 < coordAt L j t) && stepAt L j s' == t))
      then (BPair.ofNat 1).swap else BPair.unit) (List.range ((L + 1) ^ d))).oneValue
      (if decide (0 < coordAt L j s) && stepAt L j s' == s
        then (BPair.ofNat 1).swap else BPair.unit) := by
    refine BPair.oneValue_trans (bsum_range_at _ _ s _ hs (fun t _ ht =>
      (beqEqOf (andSplitB (andSplitB ht).2).1).symm)) ?_
    rw [eqBeqOf (rfl : s = s), Bool.true_and,
      ite_and_absorb _ _ (fun h => by rw [(andSplitB h).1]; exact Bool.or_true _)]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr hS1 ?_
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  cases Nat.lt_or_ge (coordAt L j s) L with
  | inr hge =>
    have hnl : ¬ coordAt L j s < L := Nat.not_lt_of_ge hge
    have htop : coordAt L j s + 1 = L + 1 :=
      congrArg Nat.succ (Nat.le_antisymm (Nat.le_of_lt_succ (baseDigit_lt (L + 1) j s hL)) hge)
    have hstep : ∀ t, (stepAt L j s == t) = true → decide (0 < coordAt L j t) = false := by
      intro t ht
      rw [← beqEqOf ht]
      have h0 : coordAt L j (stepAt L j s) = 0 := baseDigit_step_top (L + 1) j s hL htop
      rw [h0]
      exact decide_eq_false (Nat.lt_irrefl 0)
    rw [decide_eq_false hnl, Bool.false_and, Bool.false_and, iteB_false, iteB_false]
    refine BPair.add_congr (bsum_range_none _ _ _ (fun t _ => ?_)) ?_
    · cases hc : ((((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
          && ((decide (0 < coordAt L j t) && stepAt L j s == t) && s' == t)) with
      | false => rfl
      | true =>
        have h1 := andSplitB (andSplitB (andSplitB hc).2).1
        rw [hstep t h1.2] at h1
        exact Bool.noConfusion h1.1
    refine BPair.oneValue_trans (foldB_add _ _ _) ?_
    refine BPair.add_congr hS2 (bsum_range_none _ _ _ (fun t _ => ?_))
    cases hc : ((((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
        && ((decide (0 < coordAt L j t) && stepAt L j s == t)
          && (decide (0 < coordAt L j t) && stepAt L j s' == t))) with
    | false => rfl
    | true =>
      have h1 := andSplitB (andSplitB (andSplitB hc).2).1
      rw [hstep t h1.2] at h1
      exact Bool.noConfusion h1.1
  | inl hlt =>
    have hsl := stepAt_lt d L j s hj hs hlt
    have hcs : coordAt L j (stepAt L j s) = coordAt L j s + 1 := coordAt_step L j s hlt
    have hpos : decide (0 < coordAt L j (stepAt L j s)) = true := by
      rw [hcs]
      exact decide_eq_true (Nat.succ_pos _)
    rw [decide_eq_true hlt, Bool.true_and, Bool.true_and]
    refine BPair.add_congr ?_ ?_
    · refine BPair.oneValue_trans (bsum_range_at _ _ (stepAt L j s) _ hsl (fun t _ ht =>
        (beqEqOf (andSplitB (andSplitB (andSplitB ht).2).1).2).symm)) ?_
      rw [hpos, Bool.or_true, Bool.true_and, eqBeqOf (rfl : stepAt L j s = stepAt L j s),
        Bool.and_true, Bool.true_and]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (foldB_add _ _ _) ?_
    refine BPair.add_congr hS2 ?_
    refine BPair.oneValue_trans (bsum_range_at _ _ (stepAt L j s) _ hsl (fun t _ ht =>
      (beqEqOf (andSplitB (andSplitB (andSplitB ht).2).1).2).symm)) ?_
    rw [hpos, Bool.or_true, Bool.true_and, eqBeqOf (rfl : stepAt L j s = stepAt L j s),
      Bool.and_true, Bool.true_and, Bool.true_and, beq_step]
    exact BPair.oneValue_refl _

/-- The differences' Gram's entry at two cubes: the sites' fold of the
two differences' reads, the fold at the first cube's type alone. -/
theorem diffGram3_entry (d L a b c j p q : Nat) (hj : j < d) (hp : p < cubeCount d L)
    (hq : q < cubeCount d L) :
    (getAt BPair.unit (getAt [] (matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j)) p) q).oneValue
      (if ((getAt (0, 0, 0, 0) (cubeList d L) p).1 == a && (getAt (0, 0, 0, 0) (cubeList d L) p).2.1 == b
          && (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1 == c)
          && ((getAt (0, 0, 0, 0) (cubeList d L) q).1 == a && (getAt (0, 0, 0, 0) (cubeList d L) q).2.1 == b
          && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.1 == c) then
        (if (((j == a || j == b) || j == c)
              || decide (0 < coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2))
            && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then BPair.ofNat 1 else BPair.unit)
        + ((if decide (coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 < L)
            && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2
              == stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + ((if decide (0 < coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2)
            && stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2
              == (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + (if decide (coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 < L)
            && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  have hBl := diffMat3_length d L a b c j
  have hB := diffMat3_rows d L a b c j
  have hpos : 0 < (diffMat3 d L a b c j).length := by
    rw [hBl]
    exact Nat.pow_pos hL
  have hBt : (transposeM (diffMat3 d L a b c j)).length = cubeCount d L :=
    length_transposeM _ hB hpos
  have hpT : p < (transposeM (diffMat3 d L a b c j)).length := by rw [hBt]; exact hp
  have hqT : q < (transposeM (diffMat3 d L a b c j)).length := by rw [hBt]; exact hq
  rw [getAt_matMul _ _ p hpT, getAt_map [] BPair.unit _ _ q hqT]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  have hBtr : rowsLen ((L + 1) ^ d) (transposeM (diffMat3 d L a b c j)) := by
    rw [← hBl]
    exact rowsLen_transposeM _
  rw [dotP_fold ((L + 1) ^ d) _ _ (rowsLen_getAt _ p hBtr hpT) (rowsLen_getAt _ q hBtr hqT)]
  have hpl := cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) p hp)
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun t =>
    if ((getAt (0, 0, 0, 0) (cubeList d L) p).1 == a && (getAt (0, 0, 0, 0) (cubeList d L) p).2.1 == b && (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1 == c)
        && ((getAt (0, 0, 0, 0) (cubeList d L) q).1 == a && (getAt (0, 0, 0, 0) (cubeList d L) q).2.1 == b && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.1 == c)
      then
      (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
          && ((getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 == t && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == t)
        then BPair.ofNat 1 else BPair.unit)
      + ((if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 == t)
              && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == t)
        then (BPair.ofNat 1).swap else BPair.unit)
      + ((if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
            && ((getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 == t && (decide (0 < coordAt L j t)
              && stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == t))
        then (BPair.ofNat 1).swap else BPair.unit)
      + (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j t))
            && ((decide (0 < coordAt L j t) && stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 == t)
              && (decide (0 < coordAt L j t) && stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == t))
        then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) _ (fun t ht => by
    rw [getAt_transposeM BPair.unit _ hB p t hp (by rw [hBl]; exact ht),
      getAt_transposeM BPair.unit _ hB q t hq (by rw [hBl]; exact ht),
      diffMat3_entry d L a b c j t p ht hp, diffMat3_entry d L a b c j t q ht hq]
    exact diffProd3 L a b c j t _ _ _ _ _ _ _ _)) ?_
  refine BPair.oneValue_trans (bsum_ite_const _ _ _) ?_
  refine ite_congr_prop _ (fun _ => ?_)
  exact diffSum_read3 d L a b c j _ _ hj hpl.2.2.2.1


/-! The Hodge identity's case reads at cubes: the two Grams' reads at
a cube pair reduce at the types' comparisons to the differences'
Grams' reads at one type and to the sum's unit at distinct types, the
pair in one four-cell alone where the types share a plane. -/

/-- The cubes' Gram's six reads of a cube at a cube's data,
`cubesGram_entry`'s value at the data. -/
private def gramInd3 (L : Nat) (Q : Nat × Nat × Nat × Nat) (a b c s : Nat) : BPair :=
  faceInd L Q a b s * BPair.ofNat 1
  + (faceInd L Q a b (stepAt L c s) * (BPair.ofNat 1).swap
  + (faceInd L Q a c s * (BPair.ofNat 1).swap
  + (faceInd L Q a c (stepAt L b s) * BPair.ofNat 1
  + (faceInd L Q b c s * BPair.ofNat 1
  + (faceInd L Q b c (stepAt L a s) * (BPair.ofNat 1).swap + BPair.unit)))))

/-- The four-cells holding a cube read at a second cube's data,
`fourCells_holding`'s value at the cubes' signs. -/
private def holdInd3 (d L a b c s a' b' c' s' : Nat) : BPair :=
  bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a' b' c' s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a' b' c' s').swap
        else BPair.unit)
    else BPair.unit) (List.range d)
  + (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) a' b' c' s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) a' b' c' s'
        else BPair.unit)
    else BPair.unit) (List.range d)
  + (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) a' b' c' s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) a' b' c' s').swap
        else BPair.unit)
    else BPair.unit) (List.range d)
  + bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) a' b' c' s').swap
        else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) a' b' c' s'
        else BPair.unit)
    else BPair.unit) (List.range d)))

/-- The Hodge fold's matrix's read at two cubes of one type: the
differences' Grams' reads over the directions. -/
private def hodgeInd3 (d L a b c s s' : Nat) : BPair :=
  bsum (fun j =>
    (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j s)) && s' == s
      then BPair.ofNat 1 else BPair.unit)
    + ((if decide (coordAt L j s < L) && s' == stepAt L j s then (BPair.ofNat 1).swap
      else BPair.unit)
    + ((if decide (0 < coordAt L j s) && stepAt L j s' == s then (BPair.ofNat 1).swap
      else BPair.unit)
    + (if decide (coordAt L j s < L) && s' == s then BPair.ofNat 1 else BPair.unit))))
    (List.range d)

/-- The Hodge fold's matrix's entry at cubes reads at the types: the
differences' Grams' reads at one type, the sum's unit at distinct
types. -/
private theorem hodgeMat3_entry_type (d L p q : Nat) (hp : p < cubeCount d L)
    (hq : q < cubeCount d L) :
    (getAt BPair.unit (getAt [] (hodgeMat3 d L) p) q).oneValue
      (if (getAt (0, 0, 0, 0) (cubeList d L) q).1 == (getAt (0, 0, 0, 0) (cubeList d L) p).1
          && (getAt (0, 0, 0, 0) (cubeList d L) q).2.1 == (getAt (0, 0, 0, 0) (cubeList d L) p).2.1
          && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.1 == (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1
        then hodgeInd3 d L (getAt (0, 0, 0, 0) (cubeList d L) p).1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.1 (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2
        else BPair.unit) := by
  rw [hodgeMat3_entry d L p q hp hq]
  have hpl := cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) p hp)
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun a => bsum (fun b => bsum (fun c =>
    if a < b && b < c then
      bsum (fun j => if ((getAt (0, 0, 0, 0) (cubeList d L) p).1 == a && (getAt (0, 0, 0, 0) (cubeList d L) p).2.1 == b
            && (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1 == c)
          && ((getAt (0, 0, 0, 0) (cubeList d L) q).1 == a && (getAt (0, 0, 0, 0) (cubeList d L) q).2.1 == b
            && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.1 == c) then
        (if (((j == a || j == b) || j == c) || decide (0 < coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2))
            && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then BPair.ofNat 1 else BPair.unit)
        + ((if decide (coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 < L)
            && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + ((if decide (0 < coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2)
            && stepAt L j (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then (BPair.ofNat 1).swap else BPair.unit)
        + (if decide (coordAt L j (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2 < L)
            && (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2 == (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2
          then BPair.ofNat 1 else BPair.unit)))
      else BPair.unit) (List.range d)
    else BPair.unit) (List.range d)) (List.range d)) d (fun a _ =>
    bsum_congr_range_ov _ _ d (fun b _ => bsum_congr_range_ov _ _ d (fun c _ => ite_congr_prop _ (fun _ =>
      bsum_congr_range_ov _ _ d (fun j hj => diffGram3_entry d L a b c j p q hj hp hq)))))) ?_
  generalize hP : getAt (0, 0, 0, 0) (cubeList d L) p = P at hpl ⊢
  generalize hQ : getAt (0, 0, 0, 0) (cubeList d L) q = Q
  obtain ⟨hab, hbc, hcd, _, _, _, _⟩ := hpl
  cases P with
  | mk a P' =>
  cases P' with
  | mk b P'' =>
  cases P'' with
  | mk c s =>
  cases Q with
  | mk a' Q' =>
  cases Q' with
  | mk b' Q'' =>
  cases Q'' with
  | mk c' s' =>
  have hbd : b < d := Nat.lt_trans hbc hcd
  have had : a < d := Nat.lt_trans hab hbd
  show (bsum (fun a2 => bsum (fun b2 => bsum (fun c2 => if decide (a2 < b2) && decide (b2 < c2) then
    bsum (fun j => if (a == a2 && b == b2 && c == c2) && (a' == a2 && b' == b2 && c' == c2) then _
      else BPair.unit) (List.range d)
    else BPair.unit) (List.range d)) (List.range d)) (List.range d)).oneValue
    (if a' == a && b' == b && c' == c then _ else BPair.unit)
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun a2 _ ha2 => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun b2 => famFold_unit_ov bpairFoldLaws _ (fun c2 => ?_) _) _
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun j => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf (fun h => ha2 h.symm)]
    repeat rw [Bool.false_and]
    rw [iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun b2 _ hb2 => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun c2 => ?_) _
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun j => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf (fun h => hb2 h.symm), Bool.and_false]
    repeat rw [Bool.false_and]
    rw [iteB_false]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hcd (fun c2 _ hc2 => ?_)) ?_
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun j => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf (fun h => hc2 h.symm), Bool.and_false, Bool.false_and, iteB_false]
    exact BPair.oneValue_refl _
  have hg : (decide (a < b) && decide (b < c)) = true := by
    rw [decide_eq_true hab, decide_eq_true hbc]
    rfl
  rw [if_pos hg, eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.true_and]
  exact bsum_ite_const _ _ _

/-- Three units fold to the unit. -/
private theorem units3 : (BPair.unit + (BPair.unit + BPair.unit)).oneValue BPair.unit := by
  decide

/-- Seven units fold to the unit. -/
private theorem units7 :
    (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
      + BPair.unit)))))).oneValue BPair.unit := by
  decide

/-- A four-cell's cube reads at a cube of its three lower directions:
the cube at the corner forward, at the corner stepped along the fourth
direction backward. -/
private theorem cubeInd_12 (L x y z w t a' b' c' s' : Nat)
    (h123 : (x == a' && y == b' && z == c') = true) (h124 : (x == a' && y == b' && w == c') = false)
    (h134 : (x == a' && z == b' && w == c') = false) (h234 : (y == a' && z == b' && w == c') = false) :
    (cubeInd L (x, y, z, w, t) a' b' c' s').oneValue
      ((if t == s' then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L w t == s' then (BPair.ofNat 1).swap else BPair.unit)) := by
  delta cubeInd
  rw [h123, h124, h134, h234]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) units7) (BPair.add_unit _))

/-- A four-cell's cube reads at a cube of its two lower directions and
its fourth: the cube at the corner backward, at the corner stepped
along the third direction forward. -/
private theorem cubeInd_34 (L x y z w t a' b' c' s' : Nat)
    (h123 : (x == a' && y == b' && z == c') = false) (h124 : (x == a' && y == b' && w == c') = true)
    (h134 : (x == a' && z == b' && w == c') = false) (h234 : (y == a' && z == b' && w == c') = false) :
    (cubeInd L (x, y, z, w, t) a' b' c' s').oneValue
      ((if t == s' then (BPair.ofNat 1).swap else BPair.unit)
        + (if stepAt L z t == s' then BPair.ofNat 1 else BPair.unit)) := by
  delta cubeInd
  rw [h123, h124, h134, h234]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  refine BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _) ?_)
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) units5) (BPair.add_unit _))

/-- A four-cell's cube reads at a cube of its first direction and its
two upper: the cube at the corner forward, at the corner stepped along
the second direction backward. -/
private theorem cubeInd_56 (L x y z w t a' b' c' s' : Nat)
    (h123 : (x == a' && y == b' && z == c') = false) (h124 : (x == a' && y == b' && w == c') = false)
    (h134 : (x == a' && z == b' && w == c') = true) (h234 : (y == a' && z == b' && w == c') = false) :
    (cubeInd L (x, y, z, w, t) a' b' c' s').oneValue
      ((if t == s' then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L y t == s' then (BPair.ofNat 1).swap else BPair.unit)) := by
  delta cubeInd
  rw [h123, h124, h134, h234]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  refine BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _)
    (BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _) ?_)))
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) units3) (BPair.add_unit _))

/-- A four-cell's cube reads at a cube of its three upper directions:
the cube at the corner backward, at the corner stepped along the first
direction forward. -/
private theorem cubeInd_78 (L x y z w t a' b' c' s' : Nat)
    (h123 : (x == a' && y == b' && z == c') = false) (h124 : (x == a' && y == b' && w == c') = false)
    (h134 : (x == a' && z == b' && w == c') = false) (h234 : (y == a' && z == b' && w == c') = true) :
    (cubeInd L (x, y, z, w, t) a' b' c' s').oneValue
      ((if t == s' then (BPair.ofNat 1).swap else BPair.unit)
        + (if stepAt L x t == s' then BPair.ofNat 1 else BPair.unit)) := by
  delta cubeInd
  rw [h123, h124, h134, h234]
  repeat rw [Bool.true_and]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  refine BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _)
    (BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _)
      (BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _) ?_)))))
  exact BPair.add_congr (BPair.oneValue_refl _) (BPair.add_unit _)

/-- The four-cells holding a cube read a second valid cube's cubes'
signs as its eight cube reads at the data. -/
private theorem holding_cubeInd (d L a b c s a' b' c' s' : Nat) (hab : a < b) (hbc : b < c)
    (hc : c < d) (hs : s < (L + 1) ^ d) (hca : coordAt L a s < L) (hcb : coordAt L b s < L)
    (hcc : coordAt L c s < L) (hab' : a' < b') (hbc' : b' < c') (hc' : c' < d)
    (hs' : s' < (L + 1) ^ d) (hca' : coordAt L a' s' < L) (hcb' : coordAt L b' s' < L)
    (hcc' : coordAt L c' s' < L) :
    (bsum (fun e => if decide (c < e) then
        (if decide (coordAt L e s < L)
          then faceSign (fourCellCubes d L (a, b, c, e, s)) (cubeKey d L a' b' c' s') else BPair.unit)
        + (if 0 < coordAt L e s
          then (faceSign (fourCellCubes d L (a, b, c, e, s - (L + 1) ^ e)) (cubeKey d L a' b' c' s')).swap
          else BPair.unit)
      else BPair.unit) (List.range d)
    + (bsum (fun y => if decide (b < y) && decide (y < c) then
        (if decide (coordAt L y s < L)
          then (faceSign (fourCellCubes d L (a, b, y, c, s)) (cubeKey d L a' b' c' s')).swap
          else BPair.unit)
        + (if 0 < coordAt L y s
          then faceSign (fourCellCubes d L (a, b, y, c, s - (L + 1) ^ y)) (cubeKey d L a' b' c' s')
          else BPair.unit)
      else BPair.unit) (List.range d)
    + (bsum (fun y => if decide (a < y) && decide (y < b) then
        (if decide (coordAt L y s < L)
          then faceSign (fourCellCubes d L (a, y, b, c, s)) (cubeKey d L a' b' c' s') else BPair.unit)
        + (if 0 < coordAt L y s
          then (faceSign (fourCellCubes d L (a, y, b, c, s - (L + 1) ^ y)) (cubeKey d L a' b' c' s')).swap
          else BPair.unit)
      else BPair.unit) (List.range d)
    + bsum (fun x => if decide (x < a) then
        (if decide (coordAt L x s < L)
          then (faceSign (fourCellCubes d L (x, a, b, c, s)) (cubeKey d L a' b' c' s')).swap
          else BPair.unit)
        + (if 0 < coordAt L x s
          then faceSign (fourCellCubes d L (x, a, b, c, s - (L + 1) ^ x)) (cubeKey d L a' b' c' s')
          else BPair.unit)
      else BPair.unit) (List.range d)))).oneValue (holdInd3 d L a b c s a' b' c' s') := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  delta holdInd3
  refine BPair.add_congr (bsum_congr_range_ov _ _ d (fun e he => ?_))
    (BPair.add_congr (bsum_congr_range_ov _ _ d (fun y _ => ?_))
      (BPair.add_congr (bsum_congr_range_ov _ _ d (fun y _ => ?_))
        (bsum_congr_range_ov _ _ d (fun x _ => ?_))))
  · refine ite_congr_prop _ (fun hce => ?_)
    have hce' : c < e := of_decide_eq_true hce
    refine BPair.add_congr (ite_congr_prop _ (fun hco => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · rw [cubeSign_read d L a b c e s a' b' c' s' hab hbc hce' he hs hca hcb hcc
        (of_decide_eq_true hco) hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _
    · obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) e s hL hpos
      have hlt : s - (L + 1) ^ e < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs
      have hea : coordAt L a (s - (L + 1) ^ e) < L := by
        rw [show coordAt L a (s - (L + 1) ^ e) = coordAt L a s from
          hoff a (Nat.ne_of_lt (Nat.lt_trans hab (Nat.lt_trans hbc hce')))]
        exact hca
      have heb : coordAt L b (s - (L + 1) ^ e) < L := by
        rw [show coordAt L b (s - (L + 1) ^ e) = coordAt L b s from
          hoff b (Nat.ne_of_lt (Nat.lt_trans hbc hce'))]
        exact hcb
      have hec : coordAt L c (s - (L + 1) ^ e) < L := by
        rw [show coordAt L c (s - (L + 1) ^ e) = coordAt L c s from hoff c (Nat.ne_of_lt hce')]
        exact hcc
      have hee : coordAt L e (s - (L + 1) ^ e) < L := by
        have h := baseDigit_lt (L + 1) e s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [cubeSign_read d L a b c e _ a' b' c' s' hab hbc hce' he hlt hea heb hec hee
        hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _
  · refine ite_congr_prop _ (fun hg => ?_)
    have hby : b < y := of_decide_eq_true (andSplitB hg).1
    have hyc : y < c := of_decide_eq_true (andSplitB hg).2
    refine BPair.add_congr (ite_congr_prop _ (fun hco => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · rw [cubeSign_read d L a b y c s a' b' c' s' hab hby hyc hc hs hca hcb
        (of_decide_eq_true hco) hcc hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _
    · obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) y s hL hpos
      have hlt : s - (L + 1) ^ y < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs
      have hya : coordAt L a (s - (L + 1) ^ y) < L := by
        rw [show coordAt L a (s - (L + 1) ^ y) = coordAt L a s from
          hoff a (Nat.ne_of_lt (Nat.lt_trans hab hby))]
        exact hca
      have hyb : coordAt L b (s - (L + 1) ^ y) < L := by
        rw [show coordAt L b (s - (L + 1) ^ y) = coordAt L b s from hoff b (Nat.ne_of_lt hby)]
        exact hcb
      have hyc' : coordAt L c (s - (L + 1) ^ y) < L := by
        rw [show coordAt L c (s - (L + 1) ^ y) = coordAt L c s from
          hoff c (fun h => Nat.ne_of_lt hyc h.symm)]
        exact hcc
      have hyy : coordAt L y (s - (L + 1) ^ y) < L := by
        have h := baseDigit_lt (L + 1) y s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [cubeSign_read d L a b y c _ a' b' c' s' hab hby hyc hc hlt hya hyb hyy hyc'
        hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _
  · refine ite_congr_prop _ (fun hg => ?_)
    have hay : a < y := of_decide_eq_true (andSplitB hg).1
    have hyb : y < b := of_decide_eq_true (andSplitB hg).2
    refine BPair.add_congr (ite_congr_prop _ (fun hco => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · rw [cubeSign_read d L a y b c s a' b' c' s' hay hyb hbc hc hs hca
        (of_decide_eq_true hco) hcb hcc hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _
    · obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) y s hL hpos
      have hlt : s - (L + 1) ^ y < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs
      have hya : coordAt L a (s - (L + 1) ^ y) < L := by
        rw [show coordAt L a (s - (L + 1) ^ y) = coordAt L a s from hoff a (Nat.ne_of_lt hay)]
        exact hca
      have hyb' : coordAt L b (s - (L + 1) ^ y) < L := by
        rw [show coordAt L b (s - (L + 1) ^ y) = coordAt L b s from
          hoff b (fun h => Nat.ne_of_lt hyb h.symm)]
        exact hcb
      have hyc : coordAt L c (s - (L + 1) ^ y) < L := by
        rw [show coordAt L c (s - (L + 1) ^ y) = coordAt L c s from
          hoff c (fun h => Nat.ne_of_lt (Nat.lt_trans hyb hbc) h.symm)]
        exact hcc
      have hyy : coordAt L y (s - (L + 1) ^ y) < L := by
        have h := baseDigit_lt (L + 1) y s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [cubeSign_read d L a y b c _ a' b' c' s' hay hyb hbc hc hlt hya hyy hyb' hyc
        hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _
  · refine ite_congr_prop _ (fun hxa => ?_)
    have hxa' : x < a := of_decide_eq_true hxa
    refine BPair.add_congr (ite_congr_prop _ (fun hco => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · rw [cubeSign_read d L x a b c s a' b' c' s' hxa' hab hbc hc hs (of_decide_eq_true hco)
        hca hcb hcc hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _
    · obtain ⟨hs0e, hd, hoff⟩ := stepBack (L + 1) x s hL hpos
      have hlt : s - (L + 1) ^ x < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.le.intro hs0e) hs
      have hxa2 : coordAt L a (s - (L + 1) ^ x) < L := by
        rw [show coordAt L a (s - (L + 1) ^ x) = coordAt L a s from
          hoff a (fun h => Nat.ne_of_lt hxa' h.symm)]
        exact hca
      have hxb : coordAt L b (s - (L + 1) ^ x) < L := by
        rw [show coordAt L b (s - (L + 1) ^ x) = coordAt L b s from
          hoff b (fun h => Nat.ne_of_lt (Nat.lt_trans hxa' hab) h.symm)]
        exact hcb
      have hxc : coordAt L c (s - (L + 1) ^ x) < L := by
        rw [show coordAt L c (s - (L + 1) ^ x) = coordAt L c s from
          hoff c (fun h => Nat.ne_of_lt (Nat.lt_trans hxa' (Nat.lt_trans hab hbc)) h.symm)]
        exact hcc
      have hxx : coordAt L x (s - (L + 1) ^ x) < L := by
        have h := baseDigit_lt (L + 1) x s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      rw [cubeSign_read d L x a b c _ a' b' c' s' hxa' hab hbc hc hlt hxx hxa2 hxb hxc
        hab' hbc' hc' hs' hca' hcb' hcc']
      exact BPair.oneValue_refl _

/-- The four direction pieces, beyond the type's third direction,
between its second and third, between its first and second and below
the first, fold to the fold over the directions off the type's
three. -/
private theorem bsum_four_pieces (F : Nat → BPair) (a b c d : Nat) (hab : a < b) (hbc : b < c) :
    (bsum (fun e => if decide (c < e) then F e else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (b < y) && decide (y < c) then F y else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < b) then F y else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then F x else BPair.unit) (List.range d)))).oneValue
      (bsum (fun j => if (j == a || j == b) || j == c then BPair.unit else F j) (List.range d)) := by
  have hac : a < c := Nat.lt_trans hab hbc
  refine BPair.oneValue_symm ?_
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun j =>
    (if decide (c < j) then F j else BPair.unit)
    + ((if decide (b < j) && decide (j < c) then F j else BPair.unit)
    + ((if decide (a < j) && decide (j < b) then F j else BPair.unit)
    + (if decide (j < a) then F j else BPair.unit)))) d (fun j _ => ?_)) ?_
  · rcases Nat.lt_trichotomy j a with hja | hja | haj
    · -- below the first direction
      rw [neBeqOf (Nat.ne_of_lt hja), neBeqOf (Nat.ne_of_lt (Nat.lt_trans hja hab)),
        neBeqOf (Nat.ne_of_lt (Nat.lt_trans hja hac)), Bool.or_false, Bool.or_false, iteB_false_else,
        decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hja hac))),
        decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hja hab))),
        decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hja)), decide_eq_true hja, iteB_true]
      repeat rw [Bool.false_and]
      repeat rw [iteB_false]
      exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
        (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _)))
    · -- the first direction
      rw [hja, eqBeqOf (rfl : a = a)]
      repeat rw [Bool.true_or]
      rw [iteB_true_else, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hac)),
        decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hab)), decide_eq_false (Nat.lt_irrefl a)]
      repeat rw [Bool.false_and]
      repeat rw [iteB_false]
      exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
        (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _)))
    · rcases Nat.lt_trichotomy j b with hjb | hjb | hbj
      · -- between the first and the second
        rw [neBeqOf (fun h => Nat.ne_of_lt haj h.symm), neBeqOf (Nat.ne_of_lt hjb),
          neBeqOf (Nat.ne_of_lt (Nat.lt_trans hjb hbc)), Bool.or_false, Bool.or_false,
          iteB_false_else, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hjb hbc))),
          decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hjb)), decide_eq_true haj,
          decide_eq_true hjb, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt haj)), Bool.true_and,
          iteB_true]
        repeat rw [Bool.false_and]
        repeat rw [iteB_false]
        exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
          (BPair.oneValue_trans (BPair.unit_add _) (BPair.add_unit _)))
      · -- the second direction
        rw [hjb, eqBeqOf (rfl : b = b), Bool.or_true, Bool.true_or, iteB_true_else,
          decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hbc)), decide_eq_false (Nat.lt_irrefl b),
          decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hab))]
        repeat rw [Bool.false_and]
        repeat rw [Bool.and_false]
        repeat rw [iteB_false]
        exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
          (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _)))
      · rcases Nat.lt_trichotomy j c with hjc | hjc | hcj
        · -- between the second and the third
          rw [neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hab hbj) h.symm),
            neBeqOf (fun h => Nat.ne_of_lt hbj h.symm), neBeqOf (Nat.ne_of_lt hjc), Bool.or_false,
            Bool.or_false, iteB_false_else, decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hjc)),
            decide_eq_true hbj, decide_eq_true hjc, decide_eq_true (Nat.lt_trans hab hbj),
            decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hbj)),
            decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hab hbj))), Bool.true_and,
            Bool.and_false, iteB_true]
          repeat rw [iteB_false]
          exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
            (BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_add _))
              (BPair.add_unit _)))
        · -- the third direction
          rw [hjc, eqBeqOf (rfl : c = c), Bool.or_true, iteB_true_else,
            decide_eq_false (Nat.lt_irrefl c), decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hbc)),
            decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hac))]
          repeat rw [Bool.and_false]
          repeat rw [iteB_false]
          exact BPair.oneValue_symm (BPair.oneValue_trans (BPair.unit_add _)
            (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _)))
        · -- beyond the third direction
          rw [neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hac hcj) h.symm),
            neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hbc hcj) h.symm),
            neBeqOf (fun h => Nat.ne_of_lt hcj h.symm), Bool.or_false, Bool.or_false,
            iteB_false_else, decide_eq_true hcj, decide_eq_true (Nat.lt_trans hbc hcj),
            decide_eq_true (Nat.lt_trans hac hcj),
            decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt hcj)),
            decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hbc hcj))),
            decide_eq_false (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hac hcj))), iteB_true]
          repeat rw [Bool.and_false]
          repeat rw [iteB_false]
          exact BPair.oneValue_symm (BPair.oneValue_trans
            (BPair.add_congr (BPair.oneValue_refl _)
              (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))) (BPair.add_unit _))
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr (BPair.oneValue_refl _) ?_
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  exact BPair.add_congr (BPair.oneValue_refl _) (foldB_add _ _ _)

/-- The one-type shape: the six face reads at the type's three planes
against the differences' Grams' reads at the type's three
directions. -/
private theorem shapeType (A Aa Ab Ac Ba Bb Bc : Bool) :
    (((if A then BPair.ofNat 1 else BPair.unit)
        + (if Bc then (BPair.ofNat 1).swap else BPair.unit)) * BPair.ofNat 1
      + (((if Ac then BPair.ofNat 1 else BPair.unit)
        + (if A then (BPair.ofNat 1).swap else BPair.unit)) * (BPair.ofNat 1).swap
      + (((if A then (BPair.ofNat 1).swap else BPair.unit)
        + (if Bb then BPair.ofNat 1 else BPair.unit)) * (BPair.ofNat 1).swap
      + (((if Ab then (BPair.ofNat 1).swap else BPair.unit)
        + (if A then BPair.ofNat 1 else BPair.unit)) * BPair.ofNat 1
      + (((if A then BPair.ofNat 1 else BPair.unit)
        + (if Ba then (BPair.ofNat 1).swap else BPair.unit)) * BPair.ofNat 1
      + (((if Aa then BPair.ofNat 1 else BPair.unit)
        + (if A then (BPair.ofNat 1).swap else BPair.unit)) * (BPair.ofNat 1).swap
      + BPair.unit)))))).oneValue
      (((if A then BPair.ofNat 1 else BPair.unit)
        + ((if Aa then (BPair.ofNat 1).swap else BPair.unit)
        + ((if Ba then (BPair.ofNat 1).swap else BPair.unit)
        + (if A then BPair.ofNat 1 else BPair.unit))))
      + (((if A then BPair.ofNat 1 else BPair.unit)
        + ((if Ab then (BPair.ofNat 1).swap else BPair.unit)
        + ((if Bb then (BPair.ofNat 1).swap else BPair.unit)
        + (if A then BPair.ofNat 1 else BPair.unit))))
      + ((if A then BPair.ofNat 1 else BPair.unit)
        + ((if Ac then (BPair.ofNat 1).swap else BPair.unit)
        + ((if Bc then (BPair.ofNat 1).swap else BPair.unit)
        + (if A then BPair.ofNat 1 else BPair.unit)))))) := by
  cases A <;> cases Aa <;> cases Ab <;> cases Ac <;> cases Ba <;> cases Bb <;> cases Bc <;> decide

/-- The first case: two cubes of one type, the six face reads at the
shared faces against the four-cells' reads at the further directions,
the differences' Grams' reads at every direction. -/
private theorem hodge3_same (d L a b c s s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hca : coordAt L a s < L) (hcb : coordAt L b s < L) (hcc : coordAt L c s < L)
    (hca' : coordAt L a s' < L) (hcb' : coordAt L b s' < L) (hcc' : coordAt L c s' < L) :
    (gramInd3 L (a, b, c, s') a b c s + holdInd3 d L a b c s a b c s').oneValue
      (hodgeInd3 d L a b c s s') := by
  have had : a < d := Nat.lt_trans hab (Nat.lt_trans hbc hc)
  have hbd : b < d := Nat.lt_trans hbc hc
  have nab : ¬ a = b := Nat.ne_of_lt hab
  have nba : ¬ b = a := fun h => nab h.symm
  have nbc : ¬ b = c := Nat.ne_of_lt hbc
  have ncb : ¬ c = b := fun h => nbc h.symm
  have nac : ¬ a = c := Nat.ne_of_lt (Nat.lt_trans hab hbc)
  have nca : ¬ c = a := fun h => nac h.symm
  have h12t : (a == a && b == b) = true := by
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b)]
    rfl
  have h123t : (a == a && b == b && c == c) = true := by
    rw [h12t, eqBeqOf (rfl : c = c)]
    rfl
  -- the six face reads at the type's three planes
  have hg : (gramInd3 L (a, b, c, s') a b c s).oneValue
      (((if s' == s then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L c s' == s then (BPair.ofNat 1).swap else BPair.unit)) * BPair.ofNat 1
      + (((if s' == stepAt L c s then BPair.ofNat 1 else BPair.unit)
        + (if s' == s then (BPair.ofNat 1).swap else BPair.unit)) * (BPair.ofNat 1).swap
      + (((if s' == s then (BPair.ofNat 1).swap else BPair.unit)
        + (if stepAt L b s' == s then BPair.ofNat 1 else BPair.unit)) * (BPair.ofNat 1).swap
      + (((if s' == stepAt L b s then (BPair.ofNat 1).swap else BPair.unit)
        + (if s' == s then BPair.ofNat 1 else BPair.unit)) * BPair.ofNat 1
      + (((if s' == s then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L a s' == s then (BPair.ofNat 1).swap else BPair.unit)) * BPair.ofNat 1
      + (((if s' == stepAt L a s then BPair.ofNat 1 else BPair.unit)
        + (if s' == s then (BPair.ofNat 1).swap else BPair.unit)) * (BPair.ofNat 1).swap
      + BPair.unit)))))) := by
    have h34ab : (a == a && c == b) = false := by rw [neBeqOf ncb, Bool.and_false]
    have h56ab : (b == a && c == b) = false := by rw [neBeqOf nba, Bool.false_and]
    have h12ac : (a == a && b == c) = false := by rw [neBeqOf nbc, Bool.and_false]
    have h34ac : (a == a && c == c) = true := by
      rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : c = c)]
      rfl
    have h56ac : (b == a && c == c) = false := by rw [neBeqOf nba, Bool.false_and]
    have h12bc : (a == b && b == c) = false := by rw [neBeqOf nab, Bool.false_and]
    have h34bc : (a == b && c == c) = false := by rw [neBeqOf nab, Bool.false_and]
    have h56bc : (b == b && c == c) = true := by
      rw [eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
      rfl
    delta gramInd3
    refine BPair.oneValue_trans (BPair.add_congr
      (BPair.mul_congr (faceInd_12 L a b c s' a b s h12t h34ab h56ab) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_12 L a b c s' a b _ h12t h34ab h56ab) (BPair.oneValue_refl _))
        (BPair.add_congr
          (BPair.mul_congr (faceInd_34 L a b c s' a c s h12ac h34ac h56ac) (BPair.oneValue_refl _))
          (BPair.add_congr
            (BPair.mul_congr (faceInd_34 L a b c s' a c _ h12ac h34ac h56ac) (BPair.oneValue_refl _))
            (BPair.add_congr
              (BPair.mul_congr (faceInd_56 L a b c s' b c s h12bc h34bc h56bc) (BPair.oneValue_refl _))
              (BPair.add_congr
                (BPair.mul_congr (faceInd_56 L a b c s' b c _ h12bc h34bc h56bc)
                  (BPair.oneValue_refl _))
                (BPair.oneValue_refl _))))))) ?_
    rw [beq_step, beq_step, beq_step]
    exact BPair.oneValue_refl _
  -- the pieces' common summand
  let F : Nat → BPair := fun j =>
    (if decide (coordAt L j s < L) then
      (if s' == s then BPair.ofNat 1 else BPair.unit)
        + (if s' == stepAt L j s then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
    + (if 0 < coordAt L j s then
      (if stepAt L j s' == s then (BPair.ofNat 1).swap else BPair.unit)
        + (if s' == s then BPair.ofNat 1 else BPair.unit) else BPair.unit)
  have hback : ∀ j, 0 < coordAt L j s →
      ((if s - (L + 1) ^ j == s' then (BPair.ofNat 1).swap else BPair.unit)
        + (if stepAt L j (s - (L + 1) ^ j) == s' then BPair.ofNat 1 else BPair.unit)).oneValue
      ((if stepAt L j s' == s then (BPair.ofNat 1).swap else BPair.unit)
        + (if s' == s then BPair.ofNat 1 else BPair.unit)) := by
    intro j hpos
    rw [beq_stepBack L j s s' hpos, beq_step_stepBack L j j s s' hpos, beq_step]
    exact BPair.oneValue_refl _
  have he : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a b c s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a b c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      (bsum (fun e => if decide (c < e) then F e else BPair.unit) (List.range d)) := by
    refine bsum_congr_range_ov _ _ d (fun e _ => ite_congr_prop _ (fun hce => ?_))
    have hce' : c < e := of_decide_eq_true hce
    have h124 : (a == a && b == b && e == c) = false := by
      rw [h12t, Bool.true_and]
      exact neBeqOf (fun h => Nat.ne_of_lt hce' h.symm)
    have h134 : (a == a && c == b && e == c) = false := by
      rw [neBeqOf ncb, Bool.and_false, Bool.false_and]
    have h234 : (b == a && c == b && e == c) = false := by
      rw [neBeqOf nba, Bool.false_and, Bool.false_and]
    refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · refine BPair.oneValue_trans (cubeInd_12 L a b c e s a b c s' h123t h124 h134 h234) ?_
      rw [beqSymm s s', beqSymm (stepAt L e s) s']
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans
        (swap_congr (cubeInd_12 L a b c e _ a b c s' h123t h124 h134 h234)) ?_
      rw [swap_pair, BPair.swap_swap]
      exact hback e hpos
  have hy1 : (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) a b c s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) a b c s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      (bsum (fun y => if decide (b < y) && decide (y < c) then F y else BPair.unit)
        (List.range d)) := by
    refine bsum_congr_range_ov _ _ d (fun y _ => ite_congr_prop _ (fun hg => ?_))
    have hby : b < y := of_decide_eq_true (andSplitB hg).1
    have hyc : y < c := of_decide_eq_true (andSplitB hg).2
    have h123 : (a == a && b == b && y == c) = false := by
      rw [h12t, Bool.true_and]
      exact neBeqOf (Nat.ne_of_lt hyc)
    have h134 : (a == a && y == b && c == c) = false := by
      rw [neBeqOf (fun h => Nat.ne_of_lt hby h.symm), Bool.and_false, Bool.false_and]
    have h234 : (b == a && y == b && c == c) = false := by
      rw [neBeqOf nba, Bool.false_and, Bool.false_and]
    refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · refine BPair.oneValue_trans
        (swap_congr (cubeInd_34 L a b y c s a b c s' h123 h123t h134 h234)) ?_
      rw [swap_pair, BPair.swap_swap, beqSymm s s', beqSymm (stepAt L y s) s']
      exact BPair.oneValue_refl _
    · exact BPair.oneValue_trans (cubeInd_34 L a b y c _ a b c s' h123 h123t h134 h234)
        (hback y hpos)
  have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) a b c s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) a b c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      (bsum (fun y => if decide (a < y) && decide (y < b) then F y else BPair.unit)
        (List.range d)) := by
    refine bsum_congr_range_ov _ _ d (fun y _ => ite_congr_prop _ (fun hg => ?_))
    have hay : a < y := of_decide_eq_true (andSplitB hg).1
    have hyb : y < b := of_decide_eq_true (andSplitB hg).2
    have h123 : (a == a && y == b && b == c) = false := by
      rw [neBeqOf (Nat.ne_of_lt hyb), Bool.and_false, Bool.false_and]
    have h124 : (a == a && y == b && c == c) = false := by
      rw [neBeqOf (Nat.ne_of_lt hyb), Bool.and_false, Bool.false_and]
    have h234 : (y == a && b == b && c == c) = false := by
      rw [neBeqOf (fun h => Nat.ne_of_lt hay h.symm), Bool.false_and, Bool.false_and]
    refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · refine BPair.oneValue_trans (cubeInd_56 L a y b c s a b c s' h123 h124 h123t h234) ?_
      rw [beqSymm s s', beqSymm (stepAt L y s) s']
      exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans
        (swap_congr (cubeInd_56 L a y b c _ a b c s' h123 h124 h123t h234)) ?_
      rw [swap_pair, BPair.swap_swap]
      exact hback y hpos
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) a b c s').swap
        else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) a b c s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      (bsum (fun x => if decide (x < a) then F x else BPair.unit) (List.range d)) := by
    refine bsum_congr_range_ov _ _ d (fun x _ => ite_congr_prop _ (fun hg => ?_))
    have hxa : x < a := of_decide_eq_true hg
    have h123 : (x == a && a == b && b == c) = false := by
      rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and, Bool.false_and]
    have h124 : (x == a && a == b && c == c) = false := by
      rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and, Bool.false_and]
    have h134 : (x == a && b == b && c == c) = false := by
      rw [neBeqOf (Nat.ne_of_lt hxa), Bool.false_and, Bool.false_and]
    refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
    · refine BPair.oneValue_trans
        (swap_congr (cubeInd_78 L x a b c s a b c s' h123 h124 h134 h123t)) ?_
      rw [swap_pair, BPair.swap_swap, beqSymm s s', beqSymm (stepAt L x s) s']
      exact BPair.oneValue_refl _
    · exact BPair.oneValue_trans (cubeInd_78 L x a b c _ a b c s' h123 h124 h134 h123t)
        (hback x hpos)
  -- the pieces merge over the directions off the type
  have hh : (holdInd3 d L a b c s a b c s').oneValue
      (bsum (fun j => if (j == a || j == b) || j == c then BPair.unit else F j) (List.range d)) := by
    delta holdInd3
    exact BPair.oneValue_trans (BPair.add_congr he (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))
      (bsum_four_pieces F a b c d hab hbc)
  refine BPair.oneValue_trans (BPair.add_congr hg hh) ?_
  -- the differences' Grams' reads at the type's three directions and off them
  delta hodgeInd3
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (bsum_range_pick_three _ a b c d had hbd hc nab nac nbc))
  refine BPair.oneValue_trans ?_ (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.add_assoc _ _ _))
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_of_eq (BPair.add_assoc _ _ _))))
  refine BPair.add_congr ?_ (bsum_congr_range_ov _ _ d (fun j _ => ite_else_congr _ (fun hj => ?_)))
  · -- the face reads against the three type directions' Grams
    refine BPair.oneValue_trans (shapeType _ _ _ _ _ _ _) ?_
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c), neBeqOf nab,
      neBeqOf nac, neBeqOf nba, neBeqOf nbc, neBeqOf nca, neBeqOf ncb]
    repeat rw [Bool.true_or]
    repeat rw [Bool.false_or]
    repeat rw [Bool.true_or]
    rw [decide_eq_true hca, decide_eq_true hcb, decide_eq_true hcc]
    repeat rw [Bool.true_and]
    rw [ite_and_absorb _ _ (fun h => decide_eq_true (occ_of_step_beq L a s s' hca' h)),
      ite_and_absorb _ _ (fun h => decide_eq_true (occ_of_step_beq L b s s' hcb' h)),
      ite_and_absorb _ _ (fun h => decide_eq_true (occ_of_step_beq L c s s' hcc' h))]
    exact BPair.oneValue_refl _
  · -- a direction off the type
    rw [hj, Bool.false_or]
    show ((if decide (coordAt L j s < L) then
        (if s' == s then BPair.ofNat 1 else BPair.unit)
          + (if s' == stepAt L j s then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L j s then
        (if stepAt L j s' == s then (BPair.ofNat 1).swap else BPair.unit)
          + (if s' == s then BPair.ofNat 1 else BPair.unit) else BPair.unit)).oneValue _
    rw [← ite_decide (0 < coordAt L j s)]
    refine BPair.oneValue_trans (BPair.add_congr (ite_add_unit _ _ _) (ite_add_unit _ _ _)) ?_
    rw [ite_ite_and, ite_ite_and, ite_ite_and, ite_ite_and]
    exact shapeF _ _ _ _ _


/-- A four-cell's cube reads at a cube off every direction triple read
the unit. -/
private theorem cubeInd_unit (L x y z w t a' b' c' s' : Nat)
    (h123 : (x == a' && y == b' && z == c') = false) (h124 : (x == a' && y == b' && w == c') = false)
    (h134 : (x == a' && z == b' && w == c') = false) (h234 : (y == a' && z == b' && w == c') = false) :
    (cubeInd L (x, y, z, w, t) a' b' c' s').oneValue BPair.unit := by
  delta cubeInd
  rw [h123, h124, h134, h234]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  decide

/-- The four pieces at one occupied piece, the first, fold to it. -/
private theorem hold1 (V : BPair) :
    (V + (BPair.unit + (BPair.unit + BPair.unit))).oneValue V :=
  BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans (BPair.unit_add _) (BPair.unit_add _))) (BPair.add_unit _)

/-- The four pieces at one occupied piece, the second, fold to it. -/
private theorem hold2 (V : BPair) :
    (BPair.unit + (V + (BPair.unit + BPair.unit))).oneValue V :=
  BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) (BPair.unit_add _)) (BPair.add_unit _))

/-- The four pieces at one occupied piece, the third, fold to it. -/
private theorem hold3 (V : BPair) :
    (BPair.unit + (BPair.unit + (V + BPair.unit))).oneValue V :=
  BPair.oneValue_trans (BPair.unit_add _) (BPair.oneValue_trans (BPair.unit_add _)
    (BPair.add_unit _))

/-- A triple conjunction refused at its outer pair is refused. -/
private theorem and_mid (x y z : Bool) (h : (x && z) = false) : ((x && y) && z) = false := by
  cases x with
  | false => rw [Bool.false_and, Bool.false_and]
  | true =>
    cases z with
    | false => rw [Bool.and_false]
    | true => exact Bool.noConfusion h

/-- A triple conjunction refused at its upper pair is refused. -/
private theorem and_left (x y z : Bool) (h : (y && z) = false) : ((x && y) && z) = false := by
  cases x with
  | false => rw [Bool.false_and, Bool.false_and]
  | true =>
    rw [Bool.true_and]
    exact h

/-- The cube-pair shape at two cubes sharing the first's lower plane
as the second's lower plane: the two lower faces' reads against the
one four-cell's two cube reads fold to the unit. -/
private theorem shapeCaseA (A B C D : Bool) :
    (((if A then BPair.ofNat 1 else BPair.unit) + ((if B then (BPair.ofNat 1).swap else BPair.unit)
        + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))))) * BPair.ofNat 1
      + (((if C then BPair.ofNat 1 else BPair.unit) + ((if D then (BPair.ofNat 1).swap else BPair.unit)
        + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit))))))
          * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap + BPair.unit)))))
      + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if C then BPair.ofNat 1 else BPair.unit))
        + ((if B then BPair.ofNat 1 else BPair.unit)
          + (if D then (BPair.ofNat 1).swap else BPair.unit)))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at two cubes sharing the first's lower plane
as the second's outer plane. -/
private theorem shapeCaseB (A B C D : Bool) :
    ((BPair.unit + (BPair.unit + ((if A then (BPair.ofNat 1).swap else BPair.unit)
        + ((if B then BPair.ofNat 1 else BPair.unit) + (BPair.unit + (BPair.unit + BPair.unit))))))
          * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + ((if C then (BPair.ofNat 1).swap else BPair.unit)
        + ((if D then BPair.ofNat 1 else BPair.unit) + (BPair.unit + (BPair.unit + BPair.unit))))))
          * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap + BPair.unit)))))
      + (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
        + ((if B then (BPair.ofNat 1).swap else BPair.unit)
          + (if D then BPair.ofNat 1 else BPair.unit)))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at two cubes sharing the first's outer plane
as the second's lower plane. -/
private theorem shapeCaseC (A B C D : Bool) :
    ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap
      + (((if A then BPair.ofNat 1 else BPair.unit) + ((if B then (BPair.ofNat 1).swap else BPair.unit)
        + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit))))))
          * (BPair.ofNat 1).swap
      + (((if C then BPair.ofNat 1 else BPair.unit) + ((if D then (BPair.ofNat 1).swap else BPair.unit)
        + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap + BPair.unit)))))
      + (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
        + ((if B then (BPair.ofNat 1).swap else BPair.unit)
          + (if D then BPair.ofNat 1 else BPair.unit)))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at two cubes sharing the first's outer plane
as the second's outer plane. -/
private theorem shapeCaseD (A B C D : Bool) :
    ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + ((if A then (BPair.ofNat 1).swap else BPair.unit)
        + ((if B then BPair.ofNat 1 else BPair.unit) + (BPair.unit + (BPair.unit + BPair.unit))))))
          * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + ((if C then (BPair.ofNat 1).swap else BPair.unit)
        + ((if D then BPair.ofNat 1 else BPair.unit) + (BPair.unit + (BPair.unit + BPair.unit))))))
          * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap + BPair.unit)))))
      + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if C then BPair.ofNat 1 else BPair.unit))
        + ((if B then BPair.ofNat 1 else BPair.unit)
          + (if D then (BPair.ofNat 1).swap else BPair.unit)))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at two cubes sharing at most one direction:
every read the unit. -/
private theorem shapeOff :
    ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * BPair.ofNat 1
      + ((BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit + (BPair.unit
          + BPair.unit)))))) * (BPair.ofNat 1).swap + BPair.unit)))))
      + (BPair.unit + (BPair.unit + (BPair.unit + BPair.unit)))).oneValue BPair.unit := by
  decide

/-- Two cubes sharing the plane of their two lower directions, the
second's third direction beyond the first's or below it: the shared
plane's face reads against the one four-cell's two cube reads fold to
the unit. -/
private theorem hodge3_caseA (d L a b c s c' s' : Nat) (hab : a < b) (hbc : b < c)
    (hcc : coordAt L c s < L)
    (hbc' : b < c') (hc' : c' < d)
    (hcc' : coordAt L c' s' < L) (hne : ¬ c' = c) :
    (gramInd3 L (a, b, c', s') a b c s + holdInd3 d L a b c s a b c' s').oneValue BPair.unit := by
  have nba : ¬ b = a := fun h => Nat.ne_of_lt hab h.symm
  have ncb : ¬ c = b := fun h => Nat.ne_of_lt hbc h.symm
  have nc'b : ¬ c' = b := fun h => Nat.ne_of_lt hbc' h.symm
  have ncc' : ¬ c = c' := fun h => hne h.symm
  have hf123 : (a == a && b == b && c == c') = false := by
    rw [neBeqOf ncc', Bool.and_false]
  -- the six face reads against the four pieces' reads at the one four-cell
  have hV : ∀ P1 P2 P3 P4 : BPair, (P1 + (P2 + (P3 + P4))).oneValue
      ((if decide (coordAt L c' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L c s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L c' s then
          (if stepAt L c' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L c' s' == stepAt L c s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) →
      (gramInd3 L (a, b, c', s') a b c s + (P1 + (P2 + (P3 + P4)))).oneValue BPair.unit := by
    intro P1 P2 P3 P4 hP
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) hP) ?_
    delta gramInd3 faceInd
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), neBeqOf nc'b, neBeqOf hne,
      neBeqOf (Nat.ne_of_lt hbc), neBeqOf nba, neBeqOf (Nat.ne_of_lt hab)]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    rw [beqSymm s s', beqSymm (stepAt L c s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (absorb_pair _ _ _ (guard_of_beq L c' s s' hcc')
        (guard_of_beq_step L c' c s s' hcc hne hcc') _ _)
      (absorb_pair_prop _ _ _ (occ_of_step_beq L c' s s' hcc')
        (occ_of_step_beq_step L c' c s s' hcc hne hcc') _ _))) ?_
    exact shapeCaseA _ _ _ _
  -- the pieces between the lower directions and below the first read the unit
  have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) a b c' s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) a b c' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (a < y) && decide (y < b)) = true →
        ∀ t, (cubeInd L (a, y, b, c, t) a b c' s').oneValue BPair.unit := fun y hg t =>
      cubeInd_unit L a y b c t a b c' s'
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).2)), Bool.and_false,
          Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).2)), Bool.and_false,
          Bool.false_and])
        hf123
        (by rw [neBeqOf (fun h => Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).1) h.symm),
          Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => hf y hg s) (fun y hg => swap_congr (hf y hg _))
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) a b c' s').swap else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) a b c' s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ x, decide (x < a) = true →
        ∀ t, (cubeInd L (x, a, b, c, t) a b c' s').oneValue BPair.unit := fun x hg t =>
      cubeInd_unit L x a b c t a b c' s'
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        hf123
    exact piece_unit d _ _ _ _ _ (fun x hg => swap_congr (hf x hg s)) (fun x hg => hf x hg _)
  delta holdInd3
  refine hV _ _ _ _ ?_
  cases Nat.lt_or_ge c c' with
  | inl hcc'lt =>
    -- the four-cell at the second's third direction beyond the first's
    have hz : (bsum (fun e => if decide (c < e) then
        (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a b c' s' else BPair.unit)
        + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a b c' s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L c' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L c s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L c' s then
          (if stepAt L c' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L c' s' == stepAt L c s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ c' d hc' (fun e _ hec' => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
          (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ t, (cubeInd L (a, b, c, e, t) a b c' s').oneValue BPair.unit := fun t =>
          cubeInd_unit L a b c e t a b c' s' hf123
            (by rw [neBeqOf hec', Bool.and_false])
            (by rw [neBeqOf ncb, Bool.and_false, Bool.false_and])
            (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hcc'lt, iteB_true]
        have h124 : (a == a && b == b && c' == c') = true := by
          rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c' = c')]
          rfl
        have h134 : (a == a && c == b && c' == c') = false := by
          rw [neBeqOf ncb, Bool.and_false, Bool.false_and]
        have h234 : (b == a && c == b && c' == c') = false := by
          rw [neBeqOf nba, Bool.false_and, Bool.false_and]
        refine BPair.add_congr (ite_congr_prop _ (fun _ =>
            cubeInd_34 L a b c c' s a b c' s' hf123 h124 h134 h234))
          (ite_congr_prop _ (fun hpos => ?_))
        refine BPair.oneValue_trans (swap_congr
          (cubeInd_34 L a b c c' _ a b c' s' hf123 h124 h134 h234)) ?_
        rw [swap_pair, BPair.swap_swap, beq_stepBack L c' s s' hpos,
          beq_step_stepBack L c' c s s' hpos]
        exact BPair.oneValue_refl _
    have hy1 : (bsum (fun y => if decide (b < y) && decide (y < c) then
        (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) a b c' s').swap
          else BPair.unit)
        + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) a b c' s'
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ y, (decide (b < y) && decide (y < c)) = true →
          ∀ t, (cubeInd L (a, b, y, c, t) a b c' s').oneValue BPair.unit := fun y hg t =>
        cubeInd_unit L a b y c t a b c' s'
          (by rw [neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true (andSplitB hg).2) hcc'lt)),
            Bool.and_false])
          hf123
          (by rw [neBeqOf ncc', Bool.and_false])
          (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
      exact piece_unit d _ _ _ _ _ (fun y hg => swap_congr (hf y hg s)) (fun y hg => hf y hg _)
    exact BPair.oneValue_trans (BPair.add_congr hz (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))
      (hold1 _)
  | inr hge =>
    have hc'c : c' < c := Nat.lt_of_le_of_ne hge hne
    -- the four-cell at the second's third direction between the first's upper two
    have hz : (bsum (fun e => if decide (c < e) then
        (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a b c' s' else BPair.unit)
        + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a b c' s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ e, decide (c < e) = true →
          ∀ t, (cubeInd L (a, b, c, e, t) a b c' s').oneValue BPair.unit := fun e hg t =>
        cubeInd_unit L a b c e t a b c' s' hf123
          (by rw [neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hc'c (of_decide_eq_true hg)) h.symm),
            Bool.and_false])
          (by rw [neBeqOf ncb, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
      exact piece_unit d _ _ _ _ _ (fun e hg => hf e hg s) (fun e hg => swap_congr (hf e hg _))
    have hy1 : (bsum (fun y => if decide (b < y) && decide (y < c) then
        (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) a b c' s').swap
          else BPair.unit)
        + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) a b c' s'
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L c' s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L c s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L c' s then
          (if stepAt L c' s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L c' s' == stepAt L c s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ c' d hc' (fun y _ hyc' => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
          (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ t, (cubeInd L (a, b, y, c, t) a b c' s').oneValue BPair.unit := fun t =>
          cubeInd_unit L a b y c t a b c' s'
            (by rw [neBeqOf hyc', Bool.and_false])
            hf123
            (by rw [neBeqOf ncc', Bool.and_false])
            (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hbc', decide_eq_true hc'c, Bool.and_true, iteB_true]
        have h123 : (a == a && b == b && c' == c') = true := by
          rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c' = c')]
          rfl
        have h134 : (a == a && c' == b && c == c') = false := by
          rw [neBeqOf nc'b, Bool.and_false, Bool.false_and]
        have h234 : (b == a && c' == b && c == c') = false := by
          rw [neBeqOf nba, Bool.false_and, Bool.false_and]
        refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
        · refine BPair.oneValue_trans (swap_congr
            (cubeInd_12 L a b c' c s a b c' s' h123 hf123 h134 h234)) ?_
          rw [swap_pair, BPair.swap_swap]
          exact BPair.oneValue_refl _
        · refine BPair.oneValue_trans (cubeInd_12 L a b c' c _ a b c' s' h123 hf123 h134 h234) ?_
          rw [beq_stepBack L c' s s' hpos, beq_step_stepBack L c' c s s' hpos]
          exact BPair.oneValue_refl _
    exact BPair.oneValue_trans (BPair.add_congr hz (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))
      (hold2 _)

/-- Two cubes sharing the first's lower plane at the second's outer
plane, the second's middle direction between. -/
private theorem hodge3_caseB (d L a b c s y s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hcc : coordAt L c s < L)
    (hay : a < y) (hyb : y < b) (hcy' : coordAt L y s' < L)
    :
    (gramInd3 L (a, y, b, s') a b c s + holdInd3 d L a b c s a y b s').oneValue BPair.unit := by
  have nba : ¬ b = a := fun h => Nat.ne_of_lt hab h.symm
  have nyb : ¬ y = b := Nat.ne_of_lt hyb
  have nby : ¬ b = y := fun h => nyb h.symm
  have nya : ¬ y = a := fun h => Nat.ne_of_lt hay h.symm
  have nyc : ¬ y = c := Nat.ne_of_lt (Nat.lt_trans hyb hbc)
  have ncy : ¬ c = y := fun h => nyc h.symm
  have hyd : y < d := Nat.lt_trans (Nat.lt_trans hyb hbc) hc
  -- the six face reads against the four pieces' reads at the one four-cell
  have hV : ∀ P1 P2 P3 P4 : BPair, (P1 + (P2 + (P3 + P4))).oneValue
      ((if decide (coordAt L y s < L) then
          (if s == s' then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L c s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L y s then
          (if stepAt L y s' == s then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L y s' == stepAt L c s then BPair.ofNat 1 else BPair.unit)
          else BPair.unit)) →
      (gramInd3 L (a, y, b, s') a b c s + (P1 + (P2 + (P3 + P4)))).oneValue BPair.unit := by
    intro P1 P2 P3 P4 hP
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) hP) ?_
    delta gramInd3 faceInd
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), neBeqOf nyb, neBeqOf nya, neBeqOf nyc,
      neBeqOf (Nat.ne_of_lt hbc), neBeqOf (Nat.ne_of_lt hab)]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    rw [beqSymm s s', beqSymm (stepAt L c s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (absorb_pair _ _ _ (guard_of_beq L y s s' hcy')
        (guard_of_beq_step L y c s s' hcc nyc hcy') _ _)
      (absorb_pair_prop _ _ _ (occ_of_step_beq L y s s' hcy')
        (occ_of_step_beq_step L y c s s' hcc nyc hcy') _ _))) ?_
    exact shapeCaseB _ _ _ _
  -- the pieces beyond the third direction, between the upper two and below the first read the unit
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a y b s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a y b s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ e t, (cubeInd L (a, b, c, e, t) a y b s').oneValue BPair.unit := fun e t =>
      cubeInd_unit L a b c e t a y b s'
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf ncy, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun e _ => hf e s) (fun e _ => swap_congr (hf e _))
  have hy1 : (bsum (fun y1 => if decide (b < y1) && decide (y1 < c) then
      (if decide (coordAt L y1 s < L) then (cubeInd L (a, b, y1, c, s) a y b s').swap
        else BPair.unit)
      + (if 0 < coordAt L y1 s then cubeInd L (a, b, y1, c, s - (L + 1) ^ y1) a y b s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y1, (decide (b < y1) && decide (y1 < c)) = true →
        ∀ t, (cubeInd L (a, b, y1, c, t) a y b s').oneValue BPair.unit := fun y1 hg t =>
      cubeInd_unit L a b y1 c t a y b s'
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hyb (of_decide_eq_true (andSplitB hg).1))
            h.symm), Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y1 hg => swap_congr (hf y1 hg s)) (fun y1 hg => hf y1 hg _)
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) a y b s').swap else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) a y b s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ x, decide (x < a) = true →
        ∀ t, (cubeInd L (x, a, b, c, t) a y b s').oneValue BPair.unit := fun x hg t =>
      cubeInd_unit L x a b c t a y b s'
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun x hg => swap_congr (hf x hg s)) (fun x hg => hf x hg _)
  -- the four-cell at the second's middle direction between the first's lower two
  have hy2 : (bsum (fun y2 => if decide (a < y2) && decide (y2 < b) then
      (if decide (coordAt L y2 s < L) then cubeInd L (a, y2, b, c, s) a y b s' else BPair.unit)
      + (if 0 < coordAt L y2 s then (cubeInd L (a, y2, b, c, s - (L + 1) ^ y2) a y b s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L y s < L) then
          (if s == s' then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L c s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L y s then
          (if stepAt L y s' == s then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L y s' == stepAt L c s then BPair.ofNat 1 else BPair.unit)
          else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ y d hyd (fun y2 _ hy2y => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ t, (cubeInd L (a, y2, b, c, t) a y b s').oneValue BPair.unit := fun t =>
        cubeInd_unit L a y2 b c t a y b s'
          (by rw [neBeqOf hy2y, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf hy2y, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s))
          (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true hay, decide_eq_true hyb, Bool.and_true, iteB_true]
      have h123 : (a == a && y == y && b == b) = true := by
        rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : y = y), eqBeqOf (rfl : b = b)]
        rfl
      have h124 : (a == a && y == y && c == b) = false := by
        rw [neBeqOf (fun h => Nat.ne_of_lt hbc h.symm), Bool.and_false]
      have h134 : (a == a && b == y && c == b) = false := by
        rw [neBeqOf (fun h => Nat.ne_of_lt hbc h.symm), Bool.and_false]
      have h234 : (y == a && b == y && c == b) = false := by
        rw [neBeqOf nya, Bool.false_and, Bool.false_and]
      refine BPair.add_congr (ite_congr_prop _ (fun _ =>
          cubeInd_12 L a y b c s a y b s' h123 h124 h134 h234))
        (ite_congr_prop _ (fun hpos => ?_))
      refine BPair.oneValue_trans (swap_congr
        (cubeInd_12 L a y b c _ a y b s' h123 h124 h134 h234)) ?_
      rw [swap_pair, BPair.swap_swap, beq_stepBack L y s s' hpos, beq_step_stepBack L y c s s' hpos]
      exact BPair.oneValue_refl _
  delta holdInd3
  refine hV _ _ _ _ ?_
  exact BPair.oneValue_trans (BPair.add_congr hz (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))
    (hold3 _)

/-- Two cubes sharing the first's outer plane at the second's lower
plane, the second's third direction beyond. -/
private theorem hodge3_caseC (d L a b c s c' s' : Nat) (hab : a < b) (hbc : b < c)
    (hcb : coordAt L b s < L)
    (hcc'lt : c < c') (hc' : c' < d)
    (hcc'' : coordAt L c' s' < L) :
    (gramInd3 L (a, c, c', s') a b c s + holdInd3 d L a b c s a c c' s').oneValue BPair.unit := by
  have nab : ¬ a = b := Nat.ne_of_lt hab
  have nba : ¬ b = a := fun h => nab h.symm
  have nbc : ¬ b = c := Nat.ne_of_lt hbc
  have ncb : ¬ c = b := fun h => nbc h.symm
  have nca : ¬ c = a := fun h => Nat.ne_of_lt (Nat.lt_trans hab hbc) h.symm
  have nc'c : ¬ c' = c := fun h => Nat.ne_of_lt hcc'lt h.symm
  have nc'b : ¬ c' = b := fun h => Nat.ne_of_lt (Nat.lt_trans hbc hcc'lt) h.symm
  -- the six face reads against the four pieces' reads at the one four-cell
  have hV : ∀ P1 P2 P3 P4 : BPair, (P1 + (P2 + (P3 + P4))).oneValue
      ((if decide (coordAt L c' s < L) then
          (if s == s' then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L c' s then
          (if stepAt L c' s' == s then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L c' s' == stepAt L b s then BPair.ofNat 1 else BPair.unit)
          else BPair.unit)) →
      (gramInd3 L (a, c, c', s') a b c s + (P1 + (P2 + (P3 + P4)))).oneValue BPair.unit := by
    intro P1 P2 P3 P4 hP
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) hP) ?_
    delta gramInd3 faceInd
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : c = c), neBeqOf ncb, neBeqOf nc'b, neBeqOf nca,
      neBeqOf nc'c, neBeqOf nab]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    rw [beqSymm s s', beqSymm (stepAt L b s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (absorb_pair _ _ _ (guard_of_beq L c' s s' hcc'')
        (guard_of_beq_step L c' b s s' hcb nc'b hcc'') _ _)
      (absorb_pair_prop _ _ _ (occ_of_step_beq L c' s s' hcc'')
        (occ_of_step_beq_step L c' b s s' hcb nc'b hcc'') _ _))) ?_
    exact shapeCaseC _ _ _ _
  -- the four-cell at the second's third direction beyond the first's
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a c c' s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a c c' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L c' s < L) then
          (if s == s' then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L c' s then
          (if stepAt L c' s' == s then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L c' s' == stepAt L b s then BPair.ofNat 1 else BPair.unit)
          else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ c' d hc' (fun e _ hec' => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ t, (cubeInd L (a, b, c, e, t) a c c' s').oneValue BPair.unit := fun t =>
        cubeInd_unit L a b c e t a c c' s'
          (by rw [neBeqOf nbc, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nbc, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf hec', Bool.and_false])
          (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s))
          (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true hcc'lt, iteB_true]
      have h123 : (a == a && b == c && c == c') = false := by
        rw [neBeqOf nbc, Bool.and_false, Bool.false_and]
      have h124 : (a == a && b == c && c' == c') = false := by
        rw [neBeqOf nbc, Bool.and_false, Bool.false_and]
      have h134 : (a == a && c == c && c' == c') = true := by
        rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : c = c), eqBeqOf (rfl : c' = c')]
        rfl
      have h234 : (b == a && c == c && c' == c') = false := by
        rw [neBeqOf nba, Bool.false_and, Bool.false_and]
      refine BPair.add_congr (ite_congr_prop _ (fun _ =>
          cubeInd_56 L a b c c' s a c c' s' h123 h124 h134 h234))
        (ite_congr_prop _ (fun hpos => ?_))
      refine BPair.oneValue_trans (swap_congr
        (cubeInd_56 L a b c c' _ a c c' s' h123 h124 h134 h234)) ?_
      rw [swap_pair, BPair.swap_swap, beq_stepBack L c' s s' hpos,
        beq_step_stepBack L c' b s s' hpos]
      exact BPair.oneValue_refl _
  -- the pieces between the upper two, between the lower two and below the first read the unit
  have hy1 : (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) a c c' s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) a c c' s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (b < y) && decide (y < c)) = true →
        ∀ t, (cubeInd L (a, b, y, c, t) a c c' s').oneValue BPair.unit := fun y hg t =>
      cubeInd_unit L a b y c t a c c' s'
        (by rw [neBeqOf nbc, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nbc, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).2)), Bool.and_false,
          Bool.false_and])
        (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => swap_congr (hf y hg s)) (fun y hg => hf y hg _)
  have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) a c c' s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) a c c' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (a < y) && decide (y < b)) = true →
        ∀ t, (cubeInd L (a, y, b, c, t) a c c' s').oneValue BPair.unit := fun y hg t =>
      cubeInd_unit L a y b c t a c c' s'
        (by rw [neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true (andSplitB hg).2) hbc)),
          Bool.and_false, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true (andSplitB hg).2) hbc)),
          Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nbc, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf (fun h => Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).1) h.symm),
          Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => hf y hg s) (fun y hg => swap_congr (hf y hg _))
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) a c c' s').swap else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) a c c' s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ x, decide (x < a) = true →
        ∀ t, (cubeInd L (x, a, b, c, t) a c c' s').oneValue BPair.unit := fun x hg t =>
      cubeInd_unit L x a b c t a c c' s'
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf nbc, Bool.and_false, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun x hg => swap_congr (hf x hg s)) (fun x hg => hf x hg _)
  delta holdInd3
  refine hV _ _ _ _ ?_
  exact BPair.oneValue_trans (BPair.add_congr hz (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))
    (hold1 _)

/-- Two cubes sharing the first's outer plane at the second's outer
plane, the middle directions distinct. -/
private theorem hodge3_caseD (d L a b c s y s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hcb : coordAt L b s < L)
    (hay : a < y) (hyc : y < c) (hne : ¬ y = b)
    (hcy' : coordAt L y s' < L) :
    (gramInd3 L (a, y, c, s') a b c s + holdInd3 d L a b c s a y c s').oneValue BPair.unit := by
  have nab : ¬ a = b := Nat.ne_of_lt hab
  have nba : ¬ b = a := fun h => nab h.symm
  have ncb : ¬ c = b := fun h => Nat.ne_of_lt hbc h.symm
  have nby : ¬ b = y := fun h => hne h.symm
  have nya : ¬ y = a := fun h => Nat.ne_of_lt hay h.symm
  have nyc : ¬ y = c := Nat.ne_of_lt hyc
  have ncy : ¬ c = y := fun h => nyc h.symm
  have hyd : y < d := Nat.lt_trans hyc hc
  -- the six face reads against the four pieces' reads at the one four-cell
  have hV : ∀ P1 P2 P3 P4 : BPair, (P1 + (P2 + (P3 + P4))).oneValue
      ((if decide (coordAt L y s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L y s then
          (if stepAt L y s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L y s' == stepAt L b s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) →
      (gramInd3 L (a, y, c, s') a b c s + (P1 + (P2 + (P3 + P4)))).oneValue BPair.unit := by
    intro P1 P2 P3 P4 hP
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) hP) ?_
    delta gramInd3 faceInd
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : c = c), neBeqOf hne, neBeqOf ncb, neBeqOf nya,
      neBeqOf nyc, neBeqOf nab]
    repeat rw [Bool.true_and]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    rw [beqSymm s s', beqSymm (stepAt L b s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (absorb_pair _ _ _ (guard_of_beq L y s s' hcy')
        (guard_of_beq_step L y b s s' hcb hne hcy') _ _)
      (absorb_pair_prop _ _ _ (occ_of_step_beq L y s s' hcy')
        (occ_of_step_beq_step L y b s s' hcb hne hcy') _ _))) ?_
    exact shapeCaseD _ _ _ _
  -- the pieces beyond the third direction and below the first read the unit
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a y c s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a y c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ e t, (cubeInd L (a, b, c, e, t) a y c s').oneValue BPair.unit := fun e t =>
      cubeInd_unit L a b c e t a y c s'
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf ncy, Bool.and_false, Bool.false_and])
        (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun e _ => hf e s) (fun e _ => swap_congr (hf e _))
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) a y c s').swap else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) a y c s' else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ x, decide (x < a) = true →
        ∀ t, (cubeInd L (x, a, b, c, t) a y c s').oneValue BPair.unit := fun x hg t =>
      cubeInd_unit L x a b c t a y c s'
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true hg)), Bool.false_and, Bool.false_and])
        (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun x hg => swap_congr (hf x hg s)) (fun x hg => hf x hg _)
  delta holdInd3
  refine hV _ _ _ _ ?_
  cases Nat.lt_or_ge y b with
  | inl hyb =>
    -- the four-cell at the second's middle direction between the first's lower two
    have hy1 : (bsum (fun y1 => if decide (b < y1) && decide (y1 < c) then
        (if decide (coordAt L y1 s < L) then (cubeInd L (a, b, y1, c, s) a y c s').swap
          else BPair.unit)
        + (if 0 < coordAt L y1 s then cubeInd L (a, b, y1, c, s - (L + 1) ^ y1) a y c s'
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ y1, (decide (b < y1) && decide (y1 < c)) = true →
          ∀ t, (cubeInd L (a, b, y1, c, t) a y c s').oneValue BPair.unit := fun y1 hg t =>
        cubeInd_unit L a b y1 c t a y c s'
          (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hyb (of_decide_eq_true (andSplitB hg).1))
              h.symm), Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
      exact piece_unit d _ _ _ _ _ (fun y1 hg => swap_congr (hf y1 hg s)) (fun y1 hg => hf y1 hg _)
    have hy2 : (bsum (fun y2 => if decide (a < y2) && decide (y2 < b) then
        (if decide (coordAt L y2 s < L) then cubeInd L (a, y2, b, c, s) a y c s' else BPair.unit)
        + (if 0 < coordAt L y2 s then (cubeInd L (a, y2, b, c, s - (L + 1) ^ y2) a y c s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L y s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L y s then
          (if stepAt L y s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L y s' == stepAt L b s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ y d hyd (fun y2 _ hy2y => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
          (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ t, (cubeInd L (a, y2, b, c, t) a y c s').oneValue BPair.unit := fun t =>
          cubeInd_unit L a y2 b c t a y c s'
            (by rw [neBeqOf hy2y, Bool.and_false, Bool.false_and])
            (by rw [neBeqOf hy2y, Bool.and_false, Bool.false_and])
            (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
            (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hay, decide_eq_true hyb, Bool.and_true, iteB_true]
        have h123 : (a == a && y == y && b == c) = false := by
          rw [neBeqOf (Nat.ne_of_lt hbc), Bool.and_false]
        have h124 : (a == a && y == y && c == c) = true := by
          rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : y = y), eqBeqOf (rfl : c = c)]
          rfl
        have h134 : (a == a && b == y && c == c) = false := by
          rw [neBeqOf nby, Bool.and_false, Bool.false_and]
        have h234 : (y == a && b == y && c == c) = false := by
          rw [neBeqOf nya, Bool.false_and, Bool.false_and]
        refine BPair.add_congr (ite_congr_prop _ (fun _ =>
            cubeInd_34 L a y b c s a y c s' h123 h124 h134 h234))
          (ite_congr_prop _ (fun hpos => ?_))
        refine BPair.oneValue_trans (swap_congr
          (cubeInd_34 L a y b c _ a y c s' h123 h124 h134 h234)) ?_
        rw [swap_pair, BPair.swap_swap, beq_stepBack L y s s' hpos, beq_step_stepBack L y b s s' hpos]
        exact BPair.oneValue_refl _
    exact BPair.oneValue_trans (BPair.add_congr hz (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))
      (hold3 _)
  | inr hge =>
    have hby : b < y := Nat.lt_of_le_of_ne hge nby
    -- the four-cell at the second's middle direction between the first's upper two
    have hy1 : (bsum (fun y1 => if decide (b < y1) && decide (y1 < c) then
        (if decide (coordAt L y1 s < L) then (cubeInd L (a, b, y1, c, s) a y c s').swap
          else BPair.unit)
        + (if 0 < coordAt L y1 s then cubeInd L (a, b, y1, c, s - (L + 1) ^ y1) a y c s'
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L y s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L b s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L y s then
          (if stepAt L y s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L y s' == stepAt L b s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ y d hyd (fun y1 _ hy1y => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
          (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ t, (cubeInd L (a, b, y1, c, t) a y c s').oneValue BPair.unit := fun t =>
          cubeInd_unit L a b y1 c t a y c s'
            (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
            (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
            (by rw [neBeqOf hy1y, Bool.and_false, Bool.false_and])
            (by rw [neBeqOf nba, Bool.false_and, Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hby, decide_eq_true hyc, Bool.and_true, iteB_true]
        have h123 : (a == a && b == y && y == c) = false := by
          rw [neBeqOf nby, Bool.and_false, Bool.false_and]
        have h124 : (a == a && b == y && c == c) = false := by
          rw [neBeqOf nby, Bool.and_false, Bool.false_and]
        have h134 : (a == a && y == y && c == c) = true := by
          rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : y = y), eqBeqOf (rfl : c = c)]
          rfl
        have h234 : (b == a && y == y && c == c) = false := by
          rw [neBeqOf nba, Bool.false_and, Bool.false_and]
        refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
        · refine BPair.oneValue_trans (swap_congr
            (cubeInd_56 L a b y c s a y c s' h123 h124 h134 h234)) ?_
          rw [swap_pair, BPair.swap_swap]
          exact BPair.oneValue_refl _
        · refine BPair.oneValue_trans (cubeInd_56 L a b y c _ a y c s' h123 h124 h134 h234) ?_
          rw [beq_stepBack L y s s' hpos, beq_step_stepBack L y b s s' hpos]
          exact BPair.oneValue_refl _
    have hy2 : (bsum (fun y2 => if decide (a < y2) && decide (y2 < b) then
        (if decide (coordAt L y2 s < L) then cubeInd L (a, y2, b, c, s) a y c s' else BPair.unit)
        + (if 0 < coordAt L y2 s then (cubeInd L (a, y2, b, c, s - (L + 1) ^ y2) a y c s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ y2, (decide (a < y2) && decide (y2 < b)) = true →
          ∀ t, (cubeInd L (a, y2, b, c, t) a y c s').oneValue BPair.unit := fun y2 hg t =>
        cubeInd_unit L a y2 b c t a y c s'
          (by rw [neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true (andSplitB hg).2) hby)),
            Bool.and_false, Bool.false_and])
          (by rw [neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true (andSplitB hg).2) hby)),
            Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
          (by rw [neBeqOf nby, Bool.and_false, Bool.false_and])
      exact piece_unit d _ _ _ _ _ (fun y2 hg => hf y2 hg s) (fun y2 hg => swap_congr (hf y2 hg _))
    exact BPair.oneValue_trans (BPair.add_congr hz (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))
      (hold2 _)

/-- The cube-pair shape at the first's upper plane as the second's
lower: the two face reads at the shared plane against the one
four-cell's two cube reads at the further direction beyond fold to the
unit. -/
private theorem shapeCaseE (A B C D : Bool) :
    (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
      + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
      + (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
          * BPair.ofNat 1
      + (((if B then BPair.ofNat 1 else BPair.unit) + (if D then (BPair.ofNat 1).swap else BPair.unit))
          * (BPair.ofNat 1).swap + BPair.unit)))))
      + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if B then BPair.ofNat 1 else BPair.unit))
        + ((if C then BPair.ofNat 1 else BPair.unit) + (if D then (BPair.ofNat 1).swap else BPair.unit))
        + (BPair.unit + (BPair.unit + BPair.unit)))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at the first's upper plane as the second's
outer: the two face reads at the shared plane against the one
four-cell's two cube reads at the middle direction between fold to
the unit. -/
private theorem shapeCaseF (A B C D : Bool) :
    (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
      + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
      + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if C then BPair.ofNat 1 else BPair.unit))
          * BPair.ofNat 1
      + (((if B then (BPair.ofNat 1).swap else BPair.unit) + (if D then BPair.ofNat 1 else BPair.unit))
          * (BPair.ofNat 1).swap + BPair.unit)))))
      + (BPair.unit
        + (((if A then BPair.ofNat 1 else BPair.unit) + (if B then (BPair.ofNat 1).swap else BPair.unit))
          + ((if C then (BPair.ofNat 1).swap else BPair.unit) + (if D then BPair.ofNat 1 else BPair.unit))
        + (BPair.unit + BPair.unit)))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at the first's lower plane as the second's
upper: the two face reads at the shared plane against the one
four-cell's two cube reads at the direction below fold to the unit. -/
private theorem shapeCaseG (A B C D : Bool) :
    (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
        * BPair.ofNat 1
      + (((if B then BPair.ofNat 1 else BPair.unit) + (if D then (BPair.ofNat 1).swap else BPair.unit))
        * (BPair.ofNat 1).swap
      + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
      + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap + BPair.unit)))))
      + (BPair.unit + (BPair.unit + (BPair.unit
        + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if B then BPair.ofNat 1 else BPair.unit))
          + ((if C then BPair.ofNat 1 else BPair.unit)
            + (if D then (BPair.ofNat 1).swap else BPair.unit))))))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at the first's outer plane as the second's
upper: the two face reads at the shared plane against the one
four-cell's two cube reads at the direction below fold to the unit. -/
private theorem shapeCaseH (A B C D : Bool) :
    (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
      + (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
          * (BPair.ofNat 1).swap
      + (((if B then BPair.ofNat 1 else BPair.unit) + (if D then (BPair.ofNat 1).swap else BPair.unit))
          * BPair.ofNat 1
      + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap + BPair.unit)))))
      + (BPair.unit + (BPair.unit + (BPair.unit
        + (((if A then BPair.ofNat 1 else BPair.unit) + (if B then (BPair.ofNat 1).swap else BPair.unit))
          + ((if C then (BPair.ofNat 1).swap else BPair.unit)
            + (if D then BPair.ofNat 1 else BPair.unit))))))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- The cube-pair shape at the first's upper plane as the second's
upper: the two face reads at the shared plane against the one
four-cell's two cube reads at the second's first direction fold to
the unit. -/
private theorem shapeCaseI (A B C D : Bool) :
    (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
      + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
      + (((if A then BPair.ofNat 1 else BPair.unit) + (if C then (BPair.ofNat 1).swap else BPair.unit))
          * BPair.ofNat 1
      + (((if B then BPair.ofNat 1 else BPair.unit) + (if D then (BPair.ofNat 1).swap else BPair.unit))
          * (BPair.ofNat 1).swap + BPair.unit)))))
      + (BPair.unit + (BPair.unit
        + (((if A then (BPair.ofNat 1).swap else BPair.unit) + (if B then BPair.ofNat 1 else BPair.unit))
          + ((if C then BPair.ofNat 1 else BPair.unit)
            + (if D then (BPair.ofNat 1).swap else BPair.unit)))))).oneValue BPair.unit := by
  cases A <;> cases B <;> cases C <;> cases D <;> decide

/-- Two cubes sharing the first's upper plane at the second's lower
plane, the second's third direction beyond. -/
private theorem hodge3_caseE (d L a b c s c' s' : Nat) (hab : a < b) (hbc : b < c)
    (hca : coordAt L a s < L)
    (hcc'lt : c < c') (hc' : c' < d)
    (hcc'' : coordAt L c' s' < L) :
    (gramInd3 L (b, c, c', s') a b c s + holdInd3 d L a b c s b c c' s').oneValue BPair.unit := by
  have nc'a : ¬ c' = a :=
    fun h => Nat.ne_of_lt (Nat.lt_trans hab (Nat.lt_trans hbc hcc'lt)) h.symm
  have hba_f : (b == a) = false := neBeqOf (fun h => Nat.ne_of_lt hab h.symm)
  have hca_f : (c == a) = false := neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hab hbc) h.symm)
  have hab_f : (a == b) = false := neBeqOf (Nat.ne_of_lt hab)
  -- the second cube's face reads at a plaquette of the first's two lower planes
  have hfu : ∀ k' s'', (faceInd L (b, c, c', s') a k' s'').oneValue BPair.unit := fun k' s'' =>
    faceInd_unit L b c c' s' a k' s'' (by rw [hba_f, Bool.false_and])
      (by rw [hba_f, Bool.false_and]) (by rw [hca_f, Bool.false_and])
  have h12 : (b == b && c == c) = true := by
    rw [eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
    rfl
  have h34 : (b == b && c' == c) = false := by
    rw [neBeqOf (fun h => Nat.ne_of_lt hcc'lt h.symm), Bool.and_false]
  have h56 : (c == b && c' == c) = false := by
    rw [neBeqOf (fun h => Nat.ne_of_lt hbc h.symm), Bool.false_and]
  have hg : (gramInd3 L (b, c, c', s') a b c s).oneValue
      (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
        + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
        + (((if s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L c' s' == s then (BPair.ofNat 1).swap else BPair.unit)) * BPair.ofNat 1
        + (((if s' == stepAt L a s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L c' s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit))
            * (BPair.ofNat 1).swap + BPair.unit)))))) := by
    delta gramInd3
    exact BPair.add_congr (BPair.mul_congr (hfu b s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu b _) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu c s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu c _) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_12 L b c c' s' b c s h12 h34 h56) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_12 L b c c' s' b c _ h12 h34 h56) (BPair.oneValue_refl _))
        (BPair.oneValue_refl _))))))
  -- the four-cell at the further direction beyond holds both cubes
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) b c c' s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) b c c' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L c' s < L) then
        (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
          + (if stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L c' s then
        (if stepAt L c' s' == s then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L c' s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
        else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ c' d hc' (fun e _ hec' => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ s0, (cubeInd L (a, b, c, e, s0) b c c' s').oneValue BPair.unit := fun s0 =>
        cubeInd_unit L a b c e s0 b c c' s' (by rw [hab_f, Bool.false_and, Bool.false_and])
          (by rw [hab_f, Bool.false_and, Bool.false_and])
          (by rw [hab_f, Bool.false_and, Bool.false_and])
          (by rw [neBeqOf hec', Bool.and_false])
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s))
          (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true hcc'lt, iteB_true]
      have h234 : (b == b && c == c && c' == c') = true := by
        rw [eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c), eqBeqOf (rfl : c' = c')]
        rfl
      have h1 : (a == b && b == c && c == c') = false := by
        rw [hab_f, Bool.false_and, Bool.false_and]
      have h2 : (a == b && b == c && c' == c') = false := by
        rw [hab_f, Bool.false_and, Bool.false_and]
      have h3 : (a == b && c == c && c' == c') = false := by
        rw [hab_f, Bool.false_and, Bool.false_and]
      refine BPair.add_congr
        (ite_congr_prop _ (fun _ => cubeInd_78 L a b c c' s b c c' s' h1 h2 h3 h234))
        (ite_congr_prop _ (fun hpos => ?_))
      refine BPair.oneValue_trans
        (swap_congr (cubeInd_78 L a b c c' _ b c c' s' h1 h2 h3 h234)) ?_
      rw [swap_pair, BPair.swap_swap, beq_stepBack L c' s s' hpos,
        beq_step_stepBack L c' a s s' hpos]
      exact BPair.oneValue_refl _
  have hy : (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) b c c' s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) b c c' s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (b < y) && decide (y < c)) = true →
        ∀ s0, (cubeInd L (a, b, y, c, s0) b c c' s').oneValue BPair.unit := fun y hg s0 =>
      cubeInd_unit L a b y c s0 b c c' s' (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).2)), Bool.and_false,
          Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => swap_congr (hf y hg s)) (fun y hg => hf y hg _)
  have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) b c c' s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) b c c' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (a < y) && decide (y < b)) = true →
        ∀ s0, (cubeInd L (a, y, b, c, s0) b c c' s').oneValue BPair.unit := fun y hg s0 =>
      cubeInd_unit L a y b c s0 b c c' s' (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).2)), Bool.false_and,
          Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => hf y hg s) (fun y hg => swap_congr (hf y hg _))
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) b c c' s').swap
        else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) b c c' s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ x, decide (x < a) = true →
        ∀ s0, (cubeInd L (x, a, b, c, s0) b c c' s').oneValue BPair.unit := fun x hg s0 =>
      have hxb : (x == b) = false :=
        neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true hg) hab))
      cubeInd_unit L x a b c s0 b c c' s' (by rw [hxb, Bool.false_and, Bool.false_and])
        (by rw [hxb, Bool.false_and, Bool.false_and])
        (by rw [hxb, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun x hg => swap_congr (hf x hg s)) (fun x hg => hf x hg _)
  delta holdInd3
  refine BPair.oneValue_trans (BPair.add_congr hg
    (BPair.add_congr hz (BPair.add_congr hy (BPair.add_congr hy2 hx)))) ?_
  rw [beqSymm s s', beqSymm (stepAt L a s) s']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
    (BPair.add_congr
      (absorb_pair _ _ _ (guard_of_beq L c' s s' hcc'')
        (guard_of_beq_step L c' a s s' hca nc'a hcc'') _ _)
      (absorb_pair_prop _ _ _ (occ_of_step_beq L c' s s' hcc'')
        (occ_of_step_beq_step L c' a s s' hca nc'a hcc'') _ _))
    (BPair.oneValue_refl _))) ?_
  exact shapeCaseE _ _ _ _

/-- Two cubes sharing the first's upper plane at the second's outer
plane, the second's middle direction between. -/
private theorem hodge3_caseF (d L a b c s y s' : Nat) (hab : a < b) (hc : c < d)
    (hca : coordAt L a s < L)
    (hby : b < y) (hyc : y < c) (hcy' : coordAt L y s' < L)
    :
    (gramInd3 L (b, y, c, s') a b c s + holdInd3 d L a b c s b y c s').oneValue BPair.unit := by
  have hyd : y < d := Nat.lt_trans hyc hc
  have nya : ¬ y = a := fun h => Nat.ne_of_lt (Nat.lt_trans hab hby) h.symm
  have hba_f : (b == a) = false := neBeqOf (fun h => Nat.ne_of_lt hab h.symm)
  have hya_f : (y == a) = false := neBeqOf nya
  have hab_f : (a == b) = false := neBeqOf (Nat.ne_of_lt hab)
  have hyc_f : (y == c) = false := neBeqOf (Nat.ne_of_lt hyc)
  have hcy_f : (c == y) = false := neBeqOf (fun h => Nat.ne_of_lt hyc h.symm)
  have hyb_f : (y == b) = false := neBeqOf (fun h => Nat.ne_of_lt hby h.symm)
  -- the second cube's face reads at a plaquette of the first's two lower planes
  have hfu : ∀ k' s'', (faceInd L (b, y, c, s') a k' s'').oneValue BPair.unit := fun k' s'' =>
    faceInd_unit L b y c s' a k' s'' (by rw [hba_f, Bool.false_and])
      (by rw [hba_f, Bool.false_and]) (by rw [hya_f, Bool.false_and])
  have h12 : (b == b && y == c) = false := by rw [hyc_f, Bool.and_false]
  have h34 : (b == b && c == c) = true := by
    rw [eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
    rfl
  have h56 : (y == b && c == c) = false := by rw [hyb_f, Bool.false_and]
  have hg : (gramInd3 L (b, y, c, s') a b c s).oneValue
      (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
        + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
        + (((if s' == s then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L y s' == s then BPair.ofNat 1 else BPair.unit)) * BPair.ofNat 1
        + (((if s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L y s' == stepAt L a s then BPair.ofNat 1 else BPair.unit))
            * (BPair.ofNat 1).swap + BPair.unit)))))) := by
    delta gramInd3
    exact BPair.add_congr (BPair.mul_congr (hfu b s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu b _) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu c s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu c _) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_34 L b y c s' b c s h12 h34 h56) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_34 L b y c s' b c _ h12 h34 h56) (BPair.oneValue_refl _))
        (BPair.oneValue_refl _))))))
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) b y c s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) b y c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ e, decide (c < e) = true →
        ∀ s0, (cubeInd L (a, b, c, e, s0) b y c s').oneValue BPair.unit := fun e _ s0 =>
      cubeInd_unit L a b c e s0 b y c s' (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hcy_f, Bool.and_false, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun e hg => hf e hg s) (fun e hg => swap_congr (hf e hg _))
  -- the four-cell at the middle direction between holds both cubes
  have hy : (bsum (fun y2 => if decide (b < y2) && decide (y2 < c) then
      (if decide (coordAt L y2 s < L) then (cubeInd L (a, b, y2, c, s) b y c s').swap
        else BPair.unit)
      + (if 0 < coordAt L y2 s then cubeInd L (a, b, y2, c, s - (L + 1) ^ y2) b y c s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L y s < L) then
        (if s == s' then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L a s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L y s then
        (if stepAt L y s' == s then (BPair.ofNat 1).swap else BPair.unit)
          + (if stepAt L y s' == stepAt L a s then BPair.ofNat 1 else BPair.unit)
        else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ y d hyd (fun y2 _ hy2y => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ s0, (cubeInd L (a, b, y2, c, s0) b y c s').oneValue BPair.unit := fun s0 =>
        cubeInd_unit L a b y2 c s0 b y c s' (by rw [hab_f, Bool.false_and, Bool.false_and])
          (by rw [hab_f, Bool.false_and, Bool.false_and])
          (by rw [hab_f, Bool.false_and, Bool.false_and])
          (by rw [neBeqOf hy2y, Bool.and_false, Bool.false_and])
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true hby, decide_eq_true hyc, Bool.and_true, iteB_true]
      have h234 : (b == b && y == y && c == c) = true := by
        rw [eqBeqOf (rfl : b = b), eqBeqOf (rfl : y = y), eqBeqOf (rfl : c = c)]
        rfl
      have h1 : (a == b && b == y && y == c) = false := by
        rw [hab_f, Bool.false_and, Bool.false_and]
      have h2 : (a == b && b == y && c == c) = false := by
        rw [hab_f, Bool.false_and, Bool.false_and]
      have h3 : (a == b && y == y && c == c) = false := by
        rw [hab_f, Bool.false_and, Bool.false_and]
      refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
      · refine BPair.oneValue_trans
          (swap_congr (cubeInd_78 L a b y c s b y c s' h1 h2 h3 h234)) ?_
        rw [swap_pair, BPair.swap_swap]
        exact BPair.oneValue_refl _
      · refine BPair.oneValue_trans (cubeInd_78 L a b y c _ b y c s' h1 h2 h3 h234) ?_
        rw [beq_stepBack L y s s' hpos, beq_step_stepBack L y a s s' hpos]
        exact BPair.oneValue_refl _
  have hy2 : (bsum (fun y2 => if decide (a < y2) && decide (y2 < b) then
      (if decide (coordAt L y2 s < L) then cubeInd L (a, y2, b, c, s) b y c s' else BPair.unit)
      + (if 0 < coordAt L y2 s then (cubeInd L (a, y2, b, c, s - (L + 1) ^ y2) b y c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y2, (decide (a < y2) && decide (y2 < b)) = true →
        ∀ s0, (cubeInd L (a, y2, b, c, s0) b y c s').oneValue BPair.unit := fun y2 hg s0 =>
      cubeInd_unit L a y2 b c s0 b y c s' (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
        (by rw [neBeqOf (Nat.ne_of_lt (of_decide_eq_true (andSplitB hg).2)), Bool.false_and,
          Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y2 hg => hf y2 hg s) (fun y2 hg => swap_congr (hf y2 hg _))
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) b y c s').swap
        else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) b y c s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ x, decide (x < a) = true →
        ∀ s0, (cubeInd L (x, a, b, c, s0) b y c s').oneValue BPair.unit := fun x hg s0 =>
      have hxb : (x == b) = false :=
        neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true hg) hab))
      cubeInd_unit L x a b c s0 b y c s' (by rw [hxb, Bool.false_and, Bool.false_and])
        (by rw [hxb, Bool.false_and, Bool.false_and])
        (by rw [hxb, Bool.false_and, Bool.false_and])
        (by rw [hab_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun x hg => swap_congr (hf x hg s)) (fun x hg => hf x hg _)
  delta holdInd3
  refine BPair.oneValue_trans (BPair.add_congr hg
    (BPair.add_congr hz (BPair.add_congr hy (BPair.add_congr hy2 hx)))) ?_
  rw [beqSymm s s', beqSymm (stepAt L a s) s']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
    (BPair.oneValue_refl _) (BPair.add_congr
      (BPair.add_congr
        (absorb_pair _ _ _ (guard_of_beq L y s s' hcy')
          (guard_of_beq_step L y a s s' hca nya hcy') _ _)
        (absorb_pair_prop _ _ _ (occ_of_step_beq L y s s' hcy')
          (occ_of_step_beq_step L y a s s' hca nya hcy') _ _))
      (BPair.oneValue_refl _)))) ?_
  exact shapeCaseF _ _ _ _

/-- Two cubes sharing the first's lower plane at the second's upper
plane, the second's first direction below. -/
private theorem hodge3_caseG (d L a b c s x s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hcc : coordAt L c s < L)
    (hxa : x < a) (hcx' : coordAt L x s' < L)
    :
    (gramInd3 L (x, a, b, s') a b c s + holdInd3 d L a b c s x a b s').oneValue BPair.unit := by
  have hxd : x < d := Nat.lt_trans hxa (Nat.lt_trans hab (Nat.lt_trans hbc hc))
  have nxc : ¬ x = c := Nat.ne_of_lt (Nat.lt_trans hxa (Nat.lt_trans hab hbc))
  have hxa_f : (x == a) = false := neBeqOf (Nat.ne_of_lt hxa)
  have hxb_f : (x == b) = false := neBeqOf (Nat.ne_of_lt (Nat.lt_trans hxa hab))
  have hax_f : (a == x) = false := neBeqOf (fun h => Nat.ne_of_lt hxa h.symm)
  have hbx_f : (b == x) = false := neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hxa hab) h.symm)
  have hab_f : (a == b) = false := neBeqOf (Nat.ne_of_lt hab)
  have hbc_f : (b == c) = false := neBeqOf (Nat.ne_of_lt hbc)
  have hcb_f : (c == b) = false := neBeqOf (fun h => Nat.ne_of_lt hbc h.symm)
  have hba_f : (b == a) = false := neBeqOf (fun h => Nat.ne_of_lt hab h.symm)
  have h12 : (x == a && a == b) = false := by rw [hxa_f, Bool.false_and]
  have h34 : (x == a && b == b) = false := by rw [hxa_f, Bool.false_and]
  have h56 : (a == a && b == b) = true := by
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b)]
    rfl
  -- the second cube's face reads at a plaquette of the first's two upper planes
  have hfu1 : ∀ s'', (faceInd L (x, a, b, s') a c s'').oneValue BPair.unit := fun s'' =>
    faceInd_unit L x a b s' a c s'' (by rw [hxa_f, Bool.false_and])
      (by rw [hxa_f, Bool.false_and]) (by rw [hbc_f, Bool.and_false])
  have hfu2 : ∀ s'', (faceInd L (x, a, b, s') b c s'').oneValue BPair.unit := fun s'' =>
    faceInd_unit L x a b s' b c s'' (by rw [hxb_f, Bool.false_and])
      (by rw [hxb_f, Bool.false_and]) (by rw [hab_f, Bool.false_and])
  have hg : (gramInd3 L (x, a, b, s') a b c s).oneValue
      (((if s' == s then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L x s' == s then (BPair.ofNat 1).swap else BPair.unit)) * BPair.ofNat 1
        + (((if s' == stepAt L c s then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L x s' == stepAt L c s then (BPair.ofNat 1).swap else BPair.unit))
          * (BPair.ofNat 1).swap
        + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
        + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap + BPair.unit)))))) := by
    delta gramInd3
    exact BPair.add_congr
      (BPair.mul_congr (faceInd_56 L x a b s' a b s h12 h34 h56) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_56 L x a b s' a b _ h12 h34 h56) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu1 s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu1 _) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu2 s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu2 _) (BPair.oneValue_refl _))
        (BPair.oneValue_refl _))))))
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) x a b s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) x a b s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ e, decide (c < e) = true →
        ∀ s0, (cubeInd L (a, b, c, e, s0) x a b s').oneValue BPair.unit := fun e _ s0 =>
      cubeInd_unit L a b c e s0 x a b s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hbx_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun e hg => hf e hg s) (fun e hg => swap_congr (hf e hg _))
  have hy : (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) x a b s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) x a b s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (b < y) && decide (y < c)) = true →
        ∀ s0, (cubeInd L (a, b, y, c, s0) x a b s').oneValue BPair.unit := fun y _ s0 =>
      cubeInd_unit L a b y c s0 x a b s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hbx_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => swap_congr (hf y hg s)) (fun y hg => hf y hg _)
  have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) x a b s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) x a b s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (a < y) && decide (y < b)) = true →
        ∀ s0, (cubeInd L (a, y, b, c, s0) x a b s').oneValue BPair.unit := fun y hg s0 =>
      have hyx : (y == x) = false := neBeqOf (fun h =>
        Nat.ne_of_lt (Nat.lt_trans hxa (of_decide_eq_true (andSplitB hg).1)) h.symm)
      cubeInd_unit L a y b c s0 x a b s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hyx, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => hf y hg s) (fun y hg => swap_congr (hf y hg _))
  -- the four-cell at the direction below holds both cubes
  have hx : (bsum (fun x2 => if decide (x2 < a) then
      (if decide (coordAt L x2 s < L) then (cubeInd L (x2, a, b, c, s) x a b s').swap
        else BPair.unit)
      + (if 0 < coordAt L x2 s then cubeInd L (x2, a, b, c, s - (L + 1) ^ x2) x a b s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L x s < L) then
        (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
          + (if stepAt L c s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L x s then
        (if stepAt L x s' == s then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L x s' == stepAt L c s then (BPair.ofNat 1).swap else BPair.unit)
        else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ x d hxd (fun x2 _ hx2x => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ s0, (cubeInd L (x2, a, b, c, s0) x a b s').oneValue BPair.unit := fun s0 =>
        cubeInd_unit L x2 a b c s0 x a b s' (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
          (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
          (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
          (by rw [hax_f, Bool.false_and, Bool.false_and])
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true hxa, iteB_true]
      have h123 : (x == x && a == a && b == b) = true := by
        rw [eqBeqOf (rfl : x = x), eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b)]
        rfl
      have h2 : (x == x && a == a && c == b) = false := by rw [hcb_f, Bool.and_false]
      have h3 : (x == x && b == a && c == b) = false := by
        rw [hba_f, Bool.and_false, Bool.false_and]
      have h4 : (a == x && b == a && c == b) = false := by
        rw [hax_f, Bool.false_and, Bool.false_and]
      refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
      · refine BPair.oneValue_trans
          (swap_congr (cubeInd_12 L x a b c s x a b s' h123 h2 h3 h4)) ?_
        rw [swap_pair, BPair.swap_swap]
        exact BPair.oneValue_refl _
      · refine BPair.oneValue_trans (cubeInd_12 L x a b c _ x a b s' h123 h2 h3 h4) ?_
        rw [beq_stepBack L x s s' hpos, beq_step_stepBack L x c s s' hpos]
        exact BPair.oneValue_refl _
  delta holdInd3
  refine BPair.oneValue_trans (BPair.add_congr hg
    (BPair.add_congr hz (BPair.add_congr hy (BPair.add_congr hy2 hx)))) ?_
  rw [beqSymm s s', beqSymm (stepAt L c s) s']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
    (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (BPair.oneValue_refl _) (BPair.add_congr
        (absorb_pair _ _ _ (guard_of_beq L x s s' hcx')
          (guard_of_beq_step L x c s s' hcc nxc hcx') _ _)
        (absorb_pair_prop _ _ _ (occ_of_step_beq L x s s' hcx')
          (occ_of_step_beq_step L x c s s' hcc nxc hcx') _ _)))))) ?_
  exact shapeCaseG _ _ _ _

/-- Two cubes sharing the first's outer plane at the second's upper
plane, the second's first direction below. -/
private theorem hodge3_caseH (d L a b c s x s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hcb : coordAt L b s < L)
    (hxa : x < a) (hcx' : coordAt L x s' < L)
    :
    (gramInd3 L (x, a, c, s') a b c s + holdInd3 d L a b c s x a c s').oneValue BPair.unit := by
  have hxd : x < d := Nat.lt_trans hxa (Nat.lt_trans hab (Nat.lt_trans hbc hc))
  have nxb : ¬ x = b := Nat.ne_of_lt (Nat.lt_trans hxa hab)
  have hxa_f : (x == a) = false := neBeqOf (Nat.ne_of_lt hxa)
  have hxb_f : (x == b) = false := neBeqOf nxb
  have hax_f : (a == x) = false := neBeqOf (fun h => Nat.ne_of_lt hxa h.symm)
  have hbx_f : (b == x) = false := neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hxa hab) h.symm)
  have hab_f : (a == b) = false := neBeqOf (Nat.ne_of_lt hab)
  have hbc_f : (b == c) = false := neBeqOf (Nat.ne_of_lt hbc)
  have hcb_f : (c == b) = false := neBeqOf (fun h => Nat.ne_of_lt hbc h.symm)
  have hba_f : (b == a) = false := neBeqOf (fun h => Nat.ne_of_lt hab h.symm)
  have h12 : (x == a && a == c) = false := by rw [hxa_f, Bool.false_and]
  have h34 : (x == a && c == c) = false := by rw [hxa_f, Bool.false_and]
  have h56 : (a == a && c == c) = true := by
    rw [eqBeqOf (rfl : a = a), eqBeqOf (rfl : c = c)]
    rfl
  -- the second cube's face reads at a plaquette of the first's lower and upper planes
  have hfu1 : ∀ s'', (faceInd L (x, a, c, s') a b s'').oneValue BPair.unit := fun s'' =>
    faceInd_unit L x a c s' a b s'' (by rw [hxa_f, Bool.false_and])
      (by rw [hxa_f, Bool.false_and]) (by rw [hcb_f, Bool.and_false])
  have hfu2 : ∀ s'', (faceInd L (x, a, c, s') b c s'').oneValue BPair.unit := fun s'' =>
    faceInd_unit L x a c s' b c s'' (by rw [hxb_f, Bool.false_and])
      (by rw [hxb_f, Bool.false_and]) (by rw [hab_f, Bool.false_and])
  have hg : (gramInd3 L (x, a, c, s') a b c s).oneValue
      (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
        + (((if s' == s then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L x s' == s then (BPair.ofNat 1).swap else BPair.unit)) * (BPair.ofNat 1).swap
        + (((if s' == stepAt L b s then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L x s' == stepAt L b s then (BPair.ofNat 1).swap else BPair.unit))
          * BPair.ofNat 1
        + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap + BPair.unit)))))) := by
    delta gramInd3
    exact BPair.add_congr (BPair.mul_congr (hfu1 s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu1 _) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_56 L x a c s' a c s h12 h34 h56) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_56 L x a c s' a c _ h12 h34 h56) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu2 s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu2 _) (BPair.oneValue_refl _))
        (BPair.oneValue_refl _))))))
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) x a c s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) x a c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ e, decide (c < e) = true →
        ∀ s0, (cubeInd L (a, b, c, e, s0) x a c s').oneValue BPair.unit := fun e _ s0 =>
      cubeInd_unit L a b c e s0 x a c s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hbx_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun e hg => hf e hg s) (fun e hg => swap_congr (hf e hg _))
  have hy : (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) x a c s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) x a c s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (b < y) && decide (y < c)) = true →
        ∀ s0, (cubeInd L (a, b, y, c, s0) x a c s').oneValue BPair.unit := fun y _ s0 =>
      cubeInd_unit L a b y c s0 x a c s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hbx_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => swap_congr (hf y hg s)) (fun y hg => hf y hg _)
  have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) x a c s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) x a c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (a < y) && decide (y < b)) = true →
        ∀ s0, (cubeInd L (a, y, b, c, s0) x a c s').oneValue BPair.unit := fun y hg s0 =>
      have hyx : (y == x) = false := neBeqOf (fun h =>
        Nat.ne_of_lt (Nat.lt_trans hxa (of_decide_eq_true (andSplitB hg).1)) h.symm)
      cubeInd_unit L a y b c s0 x a c s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hyx, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => hf y hg s) (fun y hg => swap_congr (hf y hg _))
  -- the four-cell at the direction below holds both cubes
  have hx : (bsum (fun x2 => if decide (x2 < a) then
      (if decide (coordAt L x2 s < L) then (cubeInd L (x2, a, b, c, s) x a c s').swap
        else BPair.unit)
      + (if 0 < coordAt L x2 s then cubeInd L (x2, a, b, c, s - (L + 1) ^ x2) x a c s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue
      ((if decide (coordAt L x s < L) then
        (if s == s' then BPair.ofNat 1 else BPair.unit)
          + (if stepAt L b s == s' then (BPair.ofNat 1).swap else BPair.unit) else BPair.unit)
      + (if 0 < coordAt L x s then
        (if stepAt L x s' == s then (BPair.ofNat 1).swap else BPair.unit)
          + (if stepAt L x s' == stepAt L b s then BPair.ofNat 1 else BPair.unit)
        else BPair.unit)) := by
    refine BPair.oneValue_trans (bsum_range_pick _ x d hxd (fun x2 _ hx2x => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      have hf : ∀ s0, (cubeInd L (x2, a, b, c, s0) x a c s').oneValue BPair.unit := fun s0 =>
        cubeInd_unit L x2 a b c s0 x a c s' (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
          (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
          (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
          (by rw [hax_f, Bool.false_and, Bool.false_and])
      refine BPair.oneValue_trans (BPair.add_congr
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
          (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
          (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
    · rw [decide_eq_true hxa, iteB_true]
      have h1 : (x == x && a == a && b == c) = false := by rw [hbc_f, Bool.and_false]
      have h124 : (x == x && a == a && c == c) = true := by
        rw [eqBeqOf (rfl : x = x), eqBeqOf (rfl : a = a), eqBeqOf (rfl : c = c)]
        rfl
      have h3 : (x == x && b == a && c == c) = false := by
        rw [hba_f, Bool.and_false, Bool.false_and]
      have h4 : (a == x && b == a && c == c) = false := by
        rw [hax_f, Bool.false_and, Bool.false_and]
      refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_)) (ite_congr_prop _ (fun hpos => ?_))
      · refine BPair.oneValue_trans
          (swap_congr (cubeInd_34 L x a b c s x a c s' h1 h124 h3 h4)) ?_
        rw [swap_pair, BPair.swap_swap]
        exact BPair.oneValue_refl _
      · refine BPair.oneValue_trans (cubeInd_34 L x a b c _ x a c s' h1 h124 h3 h4) ?_
        rw [beq_stepBack L x s s' hpos, beq_step_stepBack L x b s s' hpos]
        exact BPair.oneValue_refl _
  delta holdInd3
  refine BPair.oneValue_trans (BPair.add_congr hg
    (BPair.add_congr hz (BPair.add_congr hy (BPair.add_congr hy2 hx)))) ?_
  rw [beqSymm s s', beqSymm (stepAt L b s) s']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
    (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (BPair.oneValue_refl _) (BPair.add_congr
        (absorb_pair _ _ _ (guard_of_beq L x s s' hcx')
          (guard_of_beq_step L x b s s' hcb nxb hcx') _ _)
        (absorb_pair_prop _ _ _ (occ_of_step_beq L x s s' hcx')
          (occ_of_step_beq_step L x b s s' hcb nxb hcx') _ _)))))) ?_
  exact shapeCaseH _ _ _ _

/-- Two cubes sharing the first's upper plane at the second's upper
plane, the first directions distinct. -/
private theorem hodge3_caseI (d L a b c s x s' : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hca : coordAt L a s < L)
    (hxb : x < b) (hne : ¬ x = a) (hcx' : coordAt L x s' < L)
    :
    (gramInd3 L (x, b, c, s') a b c s + holdInd3 d L a b c s x b c s').oneValue BPair.unit := by
  have hxd : x < d := Nat.lt_trans hxb (Nat.lt_trans hbc hc)
  have hxb_f : (x == b) = false := neBeqOf (Nat.ne_of_lt hxb)
  have hxa_f : (x == a) = false := neBeqOf hne
  have hax_f : (a == x) = false := neBeqOf (fun h => hne h.symm)
  have hbx_f : (b == x) = false := neBeqOf (fun h => Nat.ne_of_lt hxb h.symm)
  have hab_f : (a == b) = false := neBeqOf (Nat.ne_of_lt hab)
  have hba_f : (b == a) = false := neBeqOf (fun h => Nat.ne_of_lt hab h.symm)
  have h12 : (x == b && b == c) = false := by rw [hxb_f, Bool.false_and]
  have h34 : (x == b && c == c) = false := by rw [hxb_f, Bool.false_and]
  have h56 : (b == b && c == c) = true := by
    rw [eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
    rfl
  -- the second cube's face reads at a plaquette of the first's two lower planes
  have hfu : ∀ k' s'', (faceInd L (x, b, c, s') a k' s'').oneValue BPair.unit := fun k' s'' =>
    faceInd_unit L x b c s' a k' s'' (by rw [hxa_f, Bool.false_and])
      (by rw [hxa_f, Bool.false_and]) (by rw [hba_f, Bool.false_and])
  have hg : (gramInd3 L (x, b, c, s') a b c s).oneValue
      (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
        + (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
        + (((if s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L x s' == s then (BPair.ofNat 1).swap else BPair.unit)) * BPair.ofNat 1
        + (((if s' == stepAt L a s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L x s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit))
            * (BPair.ofNat 1).swap + BPair.unit)))))) := by
    delta gramInd3
    exact BPair.add_congr (BPair.mul_congr (hfu b s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu b _) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu c s) (BPair.oneValue_refl _))
      (BPair.add_congr (BPair.mul_congr (hfu c _) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_56 L x b c s' b c s h12 h34 h56) (BPair.oneValue_refl _))
      (BPair.add_congr
        (BPair.mul_congr (faceInd_56 L x b c s' b c _ h12 h34 h56) (BPair.oneValue_refl _))
        (BPair.oneValue_refl _))))))
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) x b c s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) x b c s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ e, decide (c < e) = true →
        ∀ s0, (cubeInd L (a, b, c, e, s0) x b c s').oneValue BPair.unit := fun e _ s0 =>
      cubeInd_unit L a b c e s0 x b c s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hbx_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun e hg => hf e hg s) (fun e hg => swap_congr (hf e hg _))
  have hy : (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) x b c s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) x b c s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y, (decide (b < y) && decide (y < c)) = true →
        ∀ s0, (cubeInd L (a, b, y, c, s0) x b c s').oneValue BPair.unit := fun y _ s0 =>
      cubeInd_unit L a b y c s0 x b c s' (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hax_f, Bool.false_and, Bool.false_and])
        (by rw [hbx_f, Bool.false_and, Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun y hg => swap_congr (hf y hg s)) (fun y hg => hf y hg _)
  -- the stepped-back corner's reads at the four-cell holding both cubes
  have hP : ∀ s0, 0 < coordAt L x s → s0 = s - (L + 1) ^ x →
      ((if s0 == s' then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L a s0 == s' then (BPair.ofNat 1).swap else BPair.unit)).oneValue
      ((if stepAt L x s' == s then BPair.ofNat 1 else BPair.unit)
        + (if stepAt L x s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)) := by
    intro s0 hpos hs0
    rw [hs0, beq_stepBack L x s s' hpos, beq_step_stepBack L x a s s' hpos]
    exact BPair.oneValue_refl _
  -- the one four-cell's two reads against the face reads, at either
  -- placement of the second's first direction
  have hmain : ∀ Pz Py Py2 Px : BPair, Pz.oneValue BPair.unit → Py.oneValue BPair.unit →
      (Py2 + Px).oneValue
        ((if decide (coordAt L x s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L x s then
          (if stepAt L x s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L x s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) →
      (gramInd3 L (x, b, c, s') a b c s + (Pz + (Py + (Py2 + Px)))).oneValue BPair.unit := by
    intro Pz Py Py2 Px hPz hPy hR
    refine BPair.oneValue_trans (BPair.add_congr hg
      (BPair.add_congr hPz (BPair.add_congr hPy hR))) ?_
    rw [beqSymm s s', beqSymm (stepAt L a s) s']
    refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
      (BPair.oneValue_refl _) (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_congr
        (absorb_pair _ _ _ (guard_of_beq L x s s' hcx')
          (guard_of_beq_step L x a s s' hca hne hcx') _ _)
        (absorb_pair_prop _ _ _ (occ_of_step_beq L x s s' hcx')
          (occ_of_step_beq_step L x a s s' hca hne hcx') _ _))))) ?_
    exact shapeCaseI _ _ _ _
  delta holdInd3
  cases Nat.lt_or_ge x a with
  | inl hxa =>
    have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
        (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) x b c s' else BPair.unit)
        + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) x b c s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ y, (decide (a < y) && decide (y < b)) = true →
          ∀ s0, (cubeInd L (a, y, b, c, s0) x b c s').oneValue BPair.unit := fun y hg s0 =>
        have hyx : (y == x) = false := neBeqOf (fun h =>
          Nat.ne_of_lt (Nat.lt_trans hxa (of_decide_eq_true (andSplitB hg).1)) h.symm)
        cubeInd_unit L a y b c s0 x b c s' (by rw [hax_f, Bool.false_and, Bool.false_and])
          (by rw [hax_f, Bool.false_and, Bool.false_and])
          (by rw [hax_f, Bool.false_and, Bool.false_and])
          (by rw [hyx, Bool.false_and, Bool.false_and])
      exact piece_unit d _ _ _ _ _ (fun y hg => hf y hg s) (fun y hg => swap_congr (hf y hg _))
    have hx : (bsum (fun x2 => if decide (x2 < a) then
        (if decide (coordAt L x2 s < L) then (cubeInd L (x2, a, b, c, s) x b c s').swap
          else BPair.unit)
        + (if 0 < coordAt L x2 s then cubeInd L (x2, a, b, c, s - (L + 1) ^ x2) x b c s'
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L x s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L x s then
          (if stepAt L x s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L x s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ x d hxd (fun x2 _ hx2x => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
          (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ s0, (cubeInd L (x2, a, b, c, s0) x b c s').oneValue BPair.unit := fun s0 =>
          cubeInd_unit L x2 a b c s0 x b c s'
            (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
            (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
            (by rw [neBeqOf hx2x, Bool.false_and, Bool.false_and])
            (by rw [hax_f, Bool.false_and, Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf s)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf _))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hxa, iteB_true]
        have h1 : (x == x && a == b && b == c) = false := by
          rw [hab_f, Bool.and_false, Bool.false_and]
        have h2 : (x == x && a == b && c == c) = false := by
          rw [hab_f, Bool.and_false, Bool.false_and]
        have h134 : (x == x && b == b && c == c) = true := by
          rw [eqBeqOf (rfl : x = x), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
          rfl
        have h4 : (a == x && b == b && c == c) = false := by
          rw [hax_f, Bool.false_and, Bool.false_and]
        refine BPair.add_congr (ite_congr_prop _ (fun _ => ?_))
          (ite_congr_prop _ (fun hpos => ?_))
        · refine BPair.oneValue_trans
            (swap_congr (cubeInd_56 L x a b c s x b c s' h1 h2 h134 h4)) ?_
          rw [swap_pair, BPair.swap_swap]
          exact BPair.oneValue_refl _
        · exact BPair.oneValue_trans (cubeInd_56 L x a b c _ x b c s' h1 h2 h134 h4)
            (hP _ hpos rfl)
    refine hmain _ _ _ _ hz hy ?_
    exact BPair.oneValue_trans (BPair.add_congr hy2 hx) (BPair.unit_add _)
  | inr hge =>
    have hax : a < x := Nat.lt_of_le_of_ne hge (fun h => hne h.symm)
    have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
        (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) x b c s' else BPair.unit)
        + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) x b c s').swap
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue
        ((if decide (coordAt L x s < L) then
          (if s == s' then (BPair.ofNat 1).swap else BPair.unit)
            + (if stepAt L a s == s' then BPair.ofNat 1 else BPair.unit) else BPair.unit)
        + (if 0 < coordAt L x s then
          (if stepAt L x s' == s then BPair.ofNat 1 else BPair.unit)
            + (if stepAt L x s' == stepAt L a s then (BPair.ofNat 1).swap else BPair.unit)
          else BPair.unit)) := by
      refine BPair.oneValue_trans (bsum_range_pick _ x d hxd (fun y _ hyx => ?_)) ?_
      · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_))
          (BPair.oneValue_of_eq (ite_prop_unit _))
        have hf : ∀ s0, (cubeInd L (a, y, b, c, s0) x b c s').oneValue BPair.unit := fun s0 =>
          cubeInd_unit L a y b c s0 x b c s' (by rw [hax_f, Bool.false_and, Bool.false_and])
            (by rw [hax_f, Bool.false_and, Bool.false_and])
            (by rw [hax_f, Bool.false_and, Bool.false_and])
            (by rw [neBeqOf hyx, Bool.false_and, Bool.false_and])
        refine BPair.oneValue_trans (BPair.add_congr
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => hf s))
            (BPair.oneValue_of_eq (ite_prop_unit _)))
          (BPair.oneValue_trans (ite_congr_prop _ (fun _ => swap_congr (hf _)))
            (BPair.oneValue_of_eq (ite_prop_unit _)))) (BPair.add_unit _)
      · rw [decide_eq_true hax, decide_eq_true hxb, Bool.and_true, iteB_true]
        have h1 : (a == x && x == b && b == c) = false := by
          rw [hax_f, Bool.false_and, Bool.false_and]
        have h2 : (a == x && x == b && c == c) = false := by
          rw [hax_f, Bool.false_and, Bool.false_and]
        have h3 : (a == x && b == b && c == c) = false := by
          rw [hax_f, Bool.false_and, Bool.false_and]
        have h234 : (x == x && b == b && c == c) = true := by
          rw [eqBeqOf (rfl : x = x), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
          rfl
        refine BPair.add_congr
          (ite_congr_prop _ (fun _ => cubeInd_78 L a x b c s x b c s' h1 h2 h3 h234))
          (ite_congr_prop _ (fun hpos => ?_))
        refine BPair.oneValue_trans
          (swap_congr (cubeInd_78 L a x b c _ x b c s' h1 h2 h3 h234)) ?_
        rw [swap_pair, BPair.swap_swap]
        exact hP _ hpos rfl
    have hx : (bsum (fun x2 => if decide (x2 < a) then
        (if decide (coordAt L x2 s < L) then (cubeInd L (x2, a, b, c, s) x b c s').swap
          else BPair.unit)
        + (if 0 < coordAt L x2 s then cubeInd L (x2, a, b, c, s - (L + 1) ^ x2) x b c s'
          else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit := by
      have hf : ∀ x2, decide (x2 < a) = true →
          ∀ s0, (cubeInd L (x2, a, b, c, s0) x b c s').oneValue BPair.unit := fun x2 hg s0 =>
        have hx2x : (x2 == x) = false :=
          neBeqOf (Nat.ne_of_lt (Nat.lt_trans (of_decide_eq_true hg) hax))
        cubeInd_unit L x2 a b c s0 x b c s' (by rw [hx2x, Bool.false_and, Bool.false_and])
          (by rw [hx2x, Bool.false_and, Bool.false_and])
          (by rw [hx2x, Bool.false_and, Bool.false_and])
          (by rw [hax_f, Bool.false_and, Bool.false_and])
      exact piece_unit d _ _ _ _ _ (fun x2 hg => swap_congr (hf x2 hg s)) (fun x2 hg => hf x2 hg _)
    refine hmain _ _ _ _ hz hy ?_
    exact BPair.oneValue_trans (BPair.add_congr hy2 hx) (BPair.add_unit _)

/-- Two cubes sharing at most one direction: every face read and every
four-cell read is the unit. -/
private theorem hodge3_off (d L a b c s a' b' c' s' : Nat)
    (h1 : (a' == a && b' == b) = false) (h2 : (a' == a && b' == c) = false)
    (h3 : (a' == b && b' == c) = false) (h4 : (a' == a && c' == b) = false)
    (h5 : (a' == a && c' == c) = false) (h6 : (a' == b && c' == c) = false)
    (h7 : (b' == a && c' == b) = false) (h8 : (b' == a && c' == c) = false)
    (h9 : (b' == b && c' == c) = false) :
    (gramInd3 L (a', b', c', s') a b c s + holdInd3 d L a b c s a' b' c' s').oneValue BPair.unit := by
  -- the refused pairs read at the four-cells' own orientation
  have h1' : (a == a' && b == b') = false := by
    rw [beqSymm a a', beqSymm b b']
    exact h1
  have h2' : (a == a' && c == b') = false := by
    rw [beqSymm a a', beqSymm c b']
    exact h2
  have h3' : (b == a' && c == b') = false := by
    rw [beqSymm b a', beqSymm c b']
    exact h3
  have h4' : (a == a' && b == c') = false := by
    rw [beqSymm a a', beqSymm b c']
    exact h4
  have h5' : (a == a' && c == c') = false := by
    rw [beqSymm a a', beqSymm c c']
    exact h5
  have h6' : (b == a' && c == c') = false := by
    rw [beqSymm b a', beqSymm c c']
    exact h6
  have h7' : (a == b' && b == c') = false := by
    rw [beqSymm a b', beqSymm b c']
    exact h7
  have h8' : (a == b' && c == c') = false := by
    rw [beqSymm a b', beqSymm c c']
    exact h8
  have h9' : (b == b' && c == c') = false := by
    rw [beqSymm b b', beqSymm c c']
    exact h9
  -- every piece reads the unit
  have hz : (bsum (fun e => if decide (c < e) then
      (if decide (coordAt L e s < L) then cubeInd L (a, b, c, e, s) a' b' c' s' else BPair.unit)
      + (if 0 < coordAt L e s then (cubeInd L (a, b, c, e, s - (L + 1) ^ e) a' b' c' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ e t, (cubeInd L (a, b, c, e, t) a' b' c' s').oneValue BPair.unit := fun e t =>
      cubeInd_unit L a b c e t a' b' c' s' (by rw [h1', Bool.false_and])
        (by rw [h1', Bool.false_and]) (by rw [h2', Bool.false_and]) (by rw [h3', Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun e _ => hf e s) (fun e _ => swap_congr (hf e _))
  have hy1 : (bsum (fun y => if decide (b < y) && decide (y < c) then
      (if decide (coordAt L y s < L) then (cubeInd L (a, b, y, c, s) a' b' c' s').swap
        else BPair.unit)
      + (if 0 < coordAt L y s then cubeInd L (a, b, y, c, s - (L + 1) ^ y) a' b' c' s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y t, (cubeInd L (a, b, y, c, t) a' b' c' s').oneValue BPair.unit := fun y t =>
      cubeInd_unit L a b y c t a' b' c' s' (by rw [h1', Bool.false_and])
        (by rw [h1', Bool.false_and]) (and_mid _ _ _ h5') (and_mid _ _ _ h6')
    exact piece_unit d _ _ _ _ _ (fun y _ => swap_congr (hf y s)) (fun y _ => hf y _)
  have hy2 : (bsum (fun y => if decide (a < y) && decide (y < b) then
      (if decide (coordAt L y s < L) then cubeInd L (a, y, b, c, s) a' b' c' s' else BPair.unit)
      + (if 0 < coordAt L y s then (cubeInd L (a, y, b, c, s - (L + 1) ^ y) a' b' c' s').swap
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ y t, (cubeInd L (a, y, b, c, t) a' b' c' s').oneValue BPair.unit := fun y t =>
      cubeInd_unit L a y b c t a' b' c' s' (and_mid _ _ _ h4') (and_mid _ _ _ h5')
        (by rw [h1', Bool.false_and]) (and_left _ _ _ h9')
    exact piece_unit d _ _ _ _ _ (fun y _ => hf y s) (fun y _ => swap_congr (hf y _))
  have hx : (bsum (fun x => if decide (x < a) then
      (if decide (coordAt L x s < L) then (cubeInd L (x, a, b, c, s) a' b' c' s').swap
        else BPair.unit)
      + (if 0 < coordAt L x s then cubeInd L (x, a, b, c, s - (L + 1) ^ x) a' b' c' s'
        else BPair.unit)
      else BPair.unit) (List.range d)).oneValue BPair.unit := by
    have hf : ∀ x t, (cubeInd L (x, a, b, c, t) a' b' c' s').oneValue BPair.unit := fun x t =>
      cubeInd_unit L x a b c t a' b' c' s' (and_left _ _ _ h7') (and_left _ _ _ h8')
        (and_left _ _ _ h9') (by rw [h1', Bool.false_and])
    exact piece_unit d _ _ _ _ _ (fun x _ => swap_congr (hf x s)) (fun x _ => hf x _)
  delta holdInd3
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.add_congr hz (BPair.add_congr hy1 (BPair.add_congr hy2 hx)))) ?_
  delta gramInd3 faceInd
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
  repeat rw [Bool.false_and]
  repeat rw [iteB_false]
  exact shapeOff

/-- The Hodge identity at cubes entry by entry: the cubes' Gram joined
to the four-cells' boundaries' Gram reads the Hodge fold's matrix at
every cube pair, the pair classes each at its own read. -/
theorem hodge3_entry (d L p q : Nat) (hp : p < cubeCount d L) (hq : q < cubeCount d L) :
    (getAt BPair.unit (getAt [] (matAdd (cubesGram d L) (fourCellGram d L)) p) q).oneValue
      (getAt BPair.unit (getAt [] (hodgeMat3 d L) p) q) := by
  rw [entry_matAdd (cubesGram d L) (fourCellGram d L) (cubeCount d L) (cubesGram_rows d L)
    (fourCellGram_rows d L) p q (by rw [cubesGram_length]; exact hp)
    (by rw [fourCellGram_length]; exact hp) hq]
  refine BPair.oneValue_trans
    (BPair.add_congr (cubesGram_entry d L p q hp hq) (fourCellGram_entry d L p q hp hq)) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm (hodgeMat3_entry_type d L p q hp hq))
  have hpl := cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) p hp)
  have hql := cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) q hq)
  have hpk := cubeKey_of_getAt d L p hp
  have hqk := cubeKey_of_getAt d L q hq
  generalize hP : getAt (0, 0, 0, 0) (cubeList d L) p = P at hpl hpk ⊢
  generalize hQ : getAt (0, 0, 0, 0) (cubeList d L) q = Q at hql hqk ⊢
  obtain ⟨hab, hbc, hc, hsd, hca, hcb, hcc⟩ := hpl
  obtain ⟨hab', hbc', hc', hsd', hca', hcb', hcc'⟩ := hql
  cases P with
  | mk a P' =>
  cases P' with
  | mk b P'' =>
  cases P'' with
  | mk c s =>
  cases Q with
  | mk a' Q' =>
  cases Q' with
  | mk b' Q'' =>
  cases Q'' with
  | mk c' s' =>
  have hpk' : cubeKey d L a b c s = p := hpk
  have hqk' : cubeKey d L a' b' c' s' = q := hqk
  rw [← hpk', ← hqk']
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_trans (fourCells_holding d L a b c s hab hbc hc hsd hca hcb hcc
        (fun f => faceSign (fourCellCubes d L f) (cubeKey d L a' b' c' s')))
      (holding_cubeInd d L a b c s a' b' c' s' hab hbc hc hsd hca hcb hcc hab' hbc' hc' hsd'
        hca' hcb' hcc'))) ?_
  show (gramInd3 L (a', b', c', s') a b c s + holdInd3 d L a b c s a' b' c' s').oneValue
    (if a' == a && b' == b && c' == c then hodgeInd3 d L a b c s s' else BPair.unit)
  cases haa : (a' == a) with
  | true =>
    have e : a = a' := (beqEqOf haa).symm
    subst e
    rw [Bool.true_and]
    cases hbb : (b' == b) with
    | true =>
      have e : b = b' := (beqEqOf hbb).symm
      subst e
      rw [Bool.true_and]
      cases hcc2 : (c' == c) with
      | true =>
        have e : c = c' := (beqEqOf hcc2).symm
        subst e
        rw [iteB_true]
        exact hodge3_same d L a b c s s' hab hbc hc hca hcb hcc hca' hcb' hcc'
      | false =>
        rw [iteB_false]
        exact hodge3_caseA d L a b c s c' s' hab hbc hcc hbc' hc' hcc' (neOfBeq hcc2)
    | false =>
      rw [Bool.false_and, iteB_false]
      cases hcb2 : (c' == b) with
      | true =>
        have e : b = c' := (beqEqOf hcb2).symm
        subst e
        exact hodge3_caseB d L a b c s b' s' hab hbc hc hcc hab' hbc' hcb'
      | false =>
        cases hbc2 : (b' == c) with
        | true =>
          have e : c = b' := (beqEqOf hbc2).symm
          subst e
          exact hodge3_caseC d L a b c s c' s' hab hbc hcb hbc' hc' hcc'
        | false =>
          cases hcc2 : (c' == c) with
          | true =>
            have e : c = c' := (beqEqOf hcc2).symm
            subst e
            exact hodge3_caseD d L a b c s b' s' hab hbc hc hcb hab' hbc' (neOfBeq hbb) hcb'
          | false =>
            exact hodge3_off d L a b c s a b' c' s' (by rw [hbb, Bool.and_false]) (by rw [hbc2, Bool.and_false])
              (by rw [neBeqOf (Nat.ne_of_lt hab), Bool.false_and]) (by rw [hcb2, Bool.and_false])
              (by rw [hcc2, Bool.and_false]) (by rw [neBeqOf (Nat.ne_of_lt hab), Bool.false_and])
              (by rw [hcb2, Bool.and_false]) (by rw [hcc2, Bool.and_false])
              (by rw [hcc2, Bool.and_false])
  | false =>
    rw [Bool.false_and, Bool.false_and, iteB_false]
    cases hab2 : (a' == b) with
    | true =>
      have e : b = a' := (beqEqOf hab2).symm
      subst e
      cases hbc2 : (b' == c) with
      | true =>
        have e : c = b' := (beqEqOf hbc2).symm
        subst e
        exact hodge3_caseE d L a b c s c' s' hab hbc hca hbc' hc' hcc'
      | false =>
        cases hcc2 : (c' == c) with
        | true =>
          have e : c = c' := (beqEqOf hcc2).symm
          subst e
          exact hodge3_caseF d L a b c s b' s' hab hc hca hab' hbc' hcb'
        | false =>
          have nba : (b' == a) = false :=
            neBeqOf (fun h => Nat.ne_of_lt (Nat.lt_trans hab hab') h.symm)
          exact hodge3_off d L a b c s b b' c' s' (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
            (by rw [hbc2, Bool.and_false]) (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
            (by rw [hcc2, Bool.and_false]) (by rw [nba, Bool.false_and]) (by rw [nba, Bool.false_and])
            (by rw [hcc2, Bool.and_false])
    | false =>
      cases hba : (b' == a) with
      | true =>
        have e : a = b' := (beqEqOf hba).symm
        subst e
        cases hcb2 : (c' == b) with
        | true =>
          have e : b = c' := (beqEqOf hcb2).symm
          subst e
          exact hodge3_caseG d L a b c s a' s' hab hbc hc hcc hab' hca'
        | false =>
          cases hcc2 : (c' == c) with
          | true =>
            have e : c = c' := (beqEqOf hcc2).symm
            subst e
            exact hodge3_caseH d L a b c s a' s' hab hbc hc hcb hab' hca'
          | false =>
            exact hodge3_off d L a b c s a' a c' s' (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
              (by rw [hab2, Bool.false_and]) (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
              (by rw [hab2, Bool.false_and]) (by rw [hcb2, Bool.and_false])
              (by rw [hcc2, Bool.and_false]) (by rw [hcc2, Bool.and_false])
      | false =>
        cases hbb : (b' == b) with
        | true =>
          have e : b = b' := (beqEqOf hbb).symm
          subst e
          cases hcc2 : (c' == c) with
          | true =>
            have e : c = c' := (beqEqOf hcc2).symm
            subst e
            exact hodge3_caseI d L a b c s a' s' hab hbc hc hca hab' (neOfBeq haa) hca'
          | false =>
            exact hodge3_off d L a b c s a' b c' s' (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
              (by rw [hab2, Bool.false_and]) (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
              (by rw [hab2, Bool.false_and]) (by rw [hba, Bool.false_and]) (by rw [hba, Bool.false_and])
              (by rw [hcc2, Bool.and_false])
        | false =>
          exact hodge3_off d L a b c s a' b' c' s' (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
            (by rw [hab2, Bool.false_and]) (by rw [haa, Bool.false_and]) (by rw [haa, Bool.false_and])
            (by rw [hab2, Bool.false_and]) (by rw [hba, Bool.false_and]) (by rw [hba, Bool.false_and])
            (by rw [hbb, Bool.false_and])


/-- The Hodge identity at cubes holds at every direction count and
side. -/
theorem hodgeRead3_all (d L : Nat) : hodgeRead3 d L := by
  exact matOne_of_entries _ _ (cubeCount d L)
    (by rw [length_matAdd _ _ (by rw [cubesGram_length, fourCellGram_length]), cubesGram_length])
    (rowsLen_matAdd _ _ _ (cubesGram_rows d L) (fourCellGram_rows d L))
    (hodgeMat3_shape d L).2 (hodgeMat3_shape d L).1
    (fun p q hp hq => hodge3_entry d L p q hp hq)


/-- The differences' Gram's form is the differences' squares' fold. -/
theorem diffGram3_form (d L a b c j : Nat) (z : List BPair) (hz : z.length = cubeCount d L) :
    (quadForm (matMul (transposeM (diffMat3 d L a b c j)) (diffMat3 d L a b c j)) z).oneValue
      (diffFold3 d L a b c j z) := by
  have hBl := diffMat3_length d L a b c j
  have hB := diffMat3_rows d L a b c j
  have hpos : 0 < (diffMat3 d L a b c j).length := by
    rw [hBl]
    exact Nat.pow_pos (Nat.succ_pos L)
  have hBt : (transposeM (diffMat3 d L a b c j)).length = cubeCount d L :=
    length_transposeM _ hB hpos
  cases Nat.eq_zero_or_pos (cubeCount d L) with
  | inl h0 =>
    have hzn : z = [] := by
      cases z with
      | nil => rfl
      | cons x l => rw [h0] at hz; exact Nat.noConfusion hz
    have hT : transposeM (diffMat3 d L a b c j) = [] := by
      rw [h0] at hBt
      cases hT : transposeM (diffMat3 d L a b c j) with
      | nil => rfl
      | cons r t => rw [hT] at hBt; exact Nat.noConfusion hBt
    rw [hzn, hT]
    exact BPair.oneValue_symm (dotN_nullR _ _ (matVec_null _ _ trivial))
  | inr hpos' =>
    have hKt : transposeM (transposeM (diffMat3 d L a b c j)) = diffMat3 d L a b c j :=
      transposeM_transposeM _ hB hpos' hpos
    have h := quadForm_matMulT (diffMat3 d L a b c j).length (transposeM (diffMat3 d L a b c j))
      (rowsLen_transposeM _) z (by rw [hz, hBt])
    rw [hKt] at h
    exact h

/-- The Hodge fold's matrix's form at cubes is the Hodge fold. -/
theorem hodgeForm3 (d L : Nat) (z : List BPair) (hz : z.length = cubeCount d L) :
    (quadForm (hodgeMat3 d L) z).oneValue (hodgeFold3 d L z) := by
  refine BPair.oneValue_trans (quadForm_msum _ _
    (fun a => msum_shape _ _ (fun b => msum_shape _ _ (hodgeType3_shape d L a b) _) _) z hz _) ?_
  refine bsum_congr_range_ov _ _ d (fun a _ => ?_)
  refine BPair.oneValue_trans (quadForm_msum _ _
    (fun b => msum_shape _ _ (hodgeType3_shape d L a b) _) z hz _) ?_
  refine bsum_congr_range_ov _ _ d (fun b _ => ?_)
  refine BPair.oneValue_trans (quadForm_msum _ _ (hodgeType3_shape d L a b) z hz _) ?_
  refine bsum_congr_range_ov _ _ d (fun c _ => ?_)
  by_cases h : (decide (a < b) && decide (b < c)) = true
  · rw [if_pos h, if_pos h]
    refine BPair.oneValue_trans (quadForm_msum _ _ (fun j => diffGram3_shape d L a b c j) z hz _) ?_
    exact bsum_congr_range_ov _ _ d (fun j _ => diffGram3_form d L a b c j z hz)
  · rw [if_neg h, if_neg h]
    exact dotN_nullR z _ (matVec_nullMat _ _ z)

/-- The cubes' Gram's form joined to the four-cells' boundaries'
image's self-pairing is the Hodge fold, `|N z|² + |N₄ᵀ z|² = ` the
fold. -/
theorem hodgeForm3_read (d L : Nat) (z : List BPair) (hz : z.length = cubeCount d L) :
    (quadForm (cubesGram d L) z
      + dotN (matVec (transposeM (fourCellBd d L)) z) (matVec (transposeM (fourCellBd d L)) z)).oneValue
      (hodgeFold3 d L z) := by
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (quadForm_gramM (fourCellCount d L) (fourCellBd d L) (fourCellBd_rows d L) z
      (by rw [hz, fourCellBd_length])))) ?_
  refine BPair.oneValue_trans (BPair.oneValue_symm (quadForm_add (cubesGram d L) (fourCellGram d L) z
    (by rw [cubesGram_length, hz]) (by rw [hz]; exact cubesGram_rows d L)
    (by rw [fourCellGram_length, hz]) (by rw [hz]; exact fourCellGram_rows d L))) ?_
  exact BPair.oneValue_trans (quadForm_matOne _ _ z (hodgeRead3_all d L)) (hodgeForm3 d L z hz)

/-- At a member of the cubes' range, the four-cells' boundaries pairing
it at the sum's unit, the cubes' Gram's form is the Hodge fold's. -/
theorem hodgeForm3_range (d L : Nat) (z : List BPair) (hz : z.length = cubeCount d L)
    (hker : poly.unitTail (matVec (transposeM (fourCellBd d L)) z)) :
    (quadForm (cubesGram d L) z).oneValue (hodgeFold3 d L z) :=
  BPair.oneValue_trans (BPair.oneValue_symm (BPair.oneValue_trans
    (BPair.add_congr (BPair.oneValue_refl _) (dotN_nullR _ _ hker)) (BPair.add_unit _)))
    (hodgeForm3_read d L z hz)

/-! The Dirichlet folds at cubes telescope line by line, and the
Poincaré read at the cubes' range. -/

/-- The difference operator's read at a site on a cube type: the
vector's read at the cube at the site against its read at the cube at
the site stepped back along the direction. -/
def diffAt3 (d L a b c j : Nat) (z : List BPair) (t : Nat) : BPair :=
  (if decide (coordAt L a t < L) && decide (coordAt L b t < L) && decide (coordAt L c t < L)
    then getAt BPair.unit z (cubeKey d L a b c t) else BPair.unit)
  + (if 0 < coordAt L j t then
    (if decide (coordAt L a (t - (L + 1) ^ j) < L) && decide (coordAt L b (t - (L + 1) ^ j) < L)
        && decide (coordAt L c (t - (L + 1) ^ j) < L)
      then (getAt BPair.unit z (cubeKey d L a b c (t - (L + 1) ^ j))).swap else BPair.unit)
    else BPair.unit)

/-- The difference operator against a cube vector reads, at a site,
its read there under the row's guard. -/
theorem diff3_entry (d L a b c j t : Nat) (z : List BPair) (hz : z.length = cubeCount d L)
    (hab : a < b) (hbc : b < c) (hc : c < d) (ht : t < (L + 1) ^ d) :
    (getAt BPair.unit (matVec (diffMat3 d L a b c j) z) t).oneValue
      (if ((j == a || j == b) || j == c) || decide (0 < coordAt L j t) then diffAt3 d L a b c j z t
        else BPair.unit) := by
  have hb : 0 < L + 1 := Nat.succ_pos L
  have hbd : b < d := Nat.lt_trans hbc hc
  have had : a < d := Nat.lt_trans hab hbd
  have hDl := diffMat3_length d L a b c j
  have hDr := diffMat3_rows d L a b c j
  have htD : t < (diffMat3 d L a b c j).length := by
    rw [hDl]
    exact ht
  rw [getAt_matVec _ _ t htD]
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_fold (cubeCount d L) _ _ (rowsLen_getAt _ t hDr htD) hz]
  -- the entries against the vector's reads at the keys
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun q =>
    if ((j == a || j == b) || j == c) || decide (0 < coordAt L j t) then
      (fun Q : Nat × Nat × Nat × Nat =>
        (if Q.1 == a && Q.2.1 == b && Q.2.2.1 == c && Q.2.2.2 == t
          then getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2) else BPair.unit)
        + (if Q.1 == a && Q.2.1 == b && Q.2.2.1 == c && decide (0 < coordAt L j t)
            && stepAt L j Q.2.2.2 == t
          then (getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2)).swap else BPair.unit))
        (getAt (0, 0, 0, 0) (cubeList d L) q)
    else BPair.unit) _ (fun q hq => ?_)) ?_
  · rw [diffMat3_entry d L a b c j t q ht hq]
    have hw : getAt BPair.unit z q = getAt BPair.unit z (cubeKey d L
        (getAt (0, 0, 0, 0) (cubeList d L) q).1 (getAt (0, 0, 0, 0) (cubeList d L) q).2.1
        (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.1 (getAt (0, 0, 0, 0) (cubeList d L) q).2.2.2) := by
      rw [cubeKey_of_getAt d L q hq]
    rw [hw]
    refine BPair.oneValue_trans (ite_mul_unit _ _ _) (ite_congr_prop _ (fun _ => ?_))
    rw [BPair.right_distrib]
    exact BPair.add_congr (iteMul _ _).1 (iteMul _ _).2
  refine BPair.oneValue_trans (bsum_ite_const _ _ _) (ite_congr_prop _ (fun _ => ?_))
  refine BPair.oneValue_trans (BPair.oneValue_of_eq (bsum_cube_places d L
    (fun Q : Nat × Nat × Nat × Nat =>
        (if Q.1 == a && Q.2.1 == b && Q.2.2.1 == c && Q.2.2.2 == t
          then getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2) else BPair.unit)
        + (if Q.1 == a && Q.2.1 == b && Q.2.2.1 == c && decide (0 < coordAt L j t)
            && stepAt L j Q.2.2.2 == t
          then (getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2)).swap else BPair.unit)))) ?_
  refine BPair.oneValue_trans (bsum_cube_triples d L _) ?_
  -- the types' reads at the type's own keys
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun a' => bsum (fun b' => bsum (fun c' =>
    if a' < b' && b' < c' then
      bsum (fun s => if decide (coordAt L a' s < L) && decide (coordAt L b' s < L)
          && decide (coordAt L c' s < L) then
        (if a' == a && b' == b && c' == c && s == t then getAt BPair.unit z (cubeKey d L a' b' c' s)
          else BPair.unit)
        + (if a' == a && b' == b && c' == c && decide (0 < coordAt L j t) && stepAt L j s == t
          then (getAt BPair.unit z (cubeKey d L a' b' c' s)).swap else BPair.unit)
        else BPair.unit) (List.range ((L + 1) ^ d)) else BPair.unit) (List.range d)) (List.range d)) d
    (fun a' _ => bsum_congr_range_ov _ _ d (fun b' _ => bsum_congr_range_ov _ _ d (fun c' _ =>
      ite_congr_prop _ (fun _ => bsum_congr_range_ov _ _ _ (fun s _ =>
        ite_congr_prop _ (fun _ => BPair.oneValue_refl _))))))) ?_
  refine BPair.oneValue_trans (bsum_range_pick _ a d had (fun a' _ ha' => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun b' => ?_) _
    refine famFold_unit_ov bpairFoldLaws _ (fun c' => ?_) _
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun s => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf ha']
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    exact BPair.add_unit _
  refine BPair.oneValue_trans (bsum_range_pick _ b d hbd (fun b' _ hb' => ?_)) ?_
  · refine famFold_unit_ov bpairFoldLaws _ (fun c' => ?_) _
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun s => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf hb']
    repeat rw [Bool.and_false]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    exact BPair.add_unit _
  refine BPair.oneValue_trans (bsum_range_pick _ c d hc (fun c' _ hc' => ?_)) ?_
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => famFold_unit_ov bpairFoldLaws _
      (fun s => ?_) _)) (BPair.oneValue_of_eq (ite_prop_unit _))
    refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [neBeqOf hc']
    repeat rw [Bool.and_false]
    repeat rw [Bool.false_and]
    repeat rw [iteB_false]
    exact BPair.add_unit _
  have hg : (decide (a < b) && decide (b < c)) = true := by
    rw [decide_eq_true hab, decide_eq_true hbc]
    rfl
  rw [if_pos hg, eqBeqOf (rfl : a = a), eqBeqOf (rfl : b = b), eqBeqOf (rfl : c = c)]
  repeat rw [Bool.true_and]
  -- the type guard distributes, and the two reads at the site and its predecessor
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s =>
    (if (decide (coordAt L a s < L) && decide (coordAt L b s < L) && decide (coordAt L c s < L))
        && s == t
      then getAt BPair.unit z (cubeKey d L a b c s) else BPair.unit)
    + (if (decide (coordAt L a s < L) && decide (coordAt L b s < L) && decide (coordAt L c s < L))
        && (decide (0 < coordAt L j t) && stepAt L j s == t)
      then (getAt BPair.unit z (cubeKey d L a b c s)).swap else BPair.unit)) _ (fun s _ => ?_)) ?_
  · refine BPair.oneValue_trans (ite_add_unit _ _ _) ?_
    rw [ite_ite_and, ite_ite_and]
    exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (foldB_add _ _ _) ?_
  refine BPair.add_congr (bsum_site_beq d L _ _ t ht) ?_
  cases hcj : decide (0 < coordAt L j t) with
  | false =>
    rw [if_neg (of_decide_eq_false hcj)]
    refine famFold_unit_ov bpairFoldLaws _ (fun s => ?_) _
    rw [Bool.false_and, Bool.and_false, iteB_false]
    exact BPair.oneValue_refl _
  | true =>
    have hpos : 0 < coordAt L j t := of_decide_eq_true hcj
    rw [if_pos hpos]
    obtain ⟨hs0, _, _⟩ := stepBack (L + 1) j t hb hpos
    have hlt : t - (L + 1) ^ j < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.sub_le t _) ht
    refine BPair.oneValue_trans (bsum_range_at _ _ (t - (L + 1) ^ j) _ hlt (fun s _ hs => ?_)) ?_
    · have hst : stepAt L j s = t := beqEqOf (andSplitB (andSplitB hs).2).2
      refine addCancelR ((L + 1) ^ j) ?_
      rw [hs0]
      exact hst
    · rw [Bool.true_and, eqBeqOf (show stepAt L j (t - (L + 1) ^ j) = t from hs0), Bool.and_true]
      exact BPair.oneValue_refl _

/-- The differences' squares' fold sits at or above the sum's unit. -/
theorem diffFold3_unitLe (d L a b c j : Nat) (z : List BPair) :
    BPair.unit ≤ diffFold3 d L a b c j z :=
  leB_congr_right (BPair.oneValue_symm (dotN_read _ _)) (unitLeOfSide (dotP_self_side _))

/-- Along a line the difference operator's reads are the line's
differences. -/
private theorem line_diff_read3 (d L a b c j : Nat) (z : List BPair) (hi lo : Nat)
    (hlo : lo < (L + 1) ^ j) (κ : Bool)
    (hκ : ∀ x, x < L + 1 → (decide (coordAt L a (siteOnLine L j hi x lo) < L)
      && decide (coordAt L b (siteOnLine L j hi x lo) < L)
      && decide (coordAt L c (siteOnLine L j hi x lo) < L)) = (κ && decide (x < L)))
    (x : Nat) (hx : x < L + 1) :
    (diffAt3 d L a b c j z (siteOnLine L j hi x lo)).oneValue
      (lineDiff L (fun y => getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi y lo))) κ x) := by
  have hb : 0 < L + 1 := Nat.succ_pos L
  show ((if decide (coordAt L a (siteOnLine L j hi x lo) < L)
        && decide (coordAt L b (siteOnLine L j hi x lo) < L)
        && decide (coordAt L c (siteOnLine L j hi x lo) < L)
      then getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi x lo)) else BPair.unit)
    + (if 0 < coordAt L j (siteOnLine L j hi x lo) then
      (if decide (coordAt L a (siteOnLine L j hi x lo - (L + 1) ^ j) < L)
          && decide (coordAt L b (siteOnLine L j hi x lo - (L + 1) ^ j) < L)
          && decide (coordAt L c (siteOnLine L j hi x lo - (L + 1) ^ j) < L)
        then (getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi x lo - (L + 1) ^ j))).swap
        else BPair.unit)
      else BPair.unit)).oneValue
    ((if κ && decide (x < L) then getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi x lo))
      else BPair.unit)
    + (if 0 < x then
      (if κ && decide (x - 1 < L)
        then (getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi (x - 1) lo))).swap
        else BPair.unit)
      else BPair.unit))
  rw [hκ x hx, coordAt_siteOnLine L j hi x lo hx hlo]
  refine BPair.add_congr (BPair.oneValue_refl _) (ite_congr_prop _ (fun hpos => ?_))
  have hx1 : x - 1 + 1 = x := Nat.succ_pred_eq_of_pos hpos
  have hsite : siteOnLine L j hi x lo = stepAt L j (siteOnLine L j hi (x - 1) lo) := by
    rw [← siteOnLine_step, hx1]
  have hpos' : 0 < coordAt L j (siteOnLine L j hi x lo) := by
    rw [coordAt_siteOnLine L j hi x lo hx hlo]
    exact hpos
  have hback : siteOnLine L j hi x lo - (L + 1) ^ j = siteOnLine L j hi (x - 1) lo := by
    refine addCancelR ((L + 1) ^ j) ?_
    rw [(stepBack (L + 1) j _ hb hpos').1]
    exact hsite
  rw [hback, hκ (x - 1) (Nat.lt_of_le_of_lt (Nat.sub_le x 1) hx)]
  exact BPair.oneValue_refl _

/-- One line's values' squares against its differences' squares. -/
private theorem line_read3 (d L a b c j : Nat) (z : List BPair) (hi lo : Nat)
    (hlo : lo < (L + 1) ^ j) (κ : Bool)
    (hκ : ∀ x, x < L + 1 → (decide (coordAt L a (siteOnLine L j hi x lo) < L)
      && decide (coordAt L b (siteOnLine L j hi x lo) < L)
      && decide (coordAt L c (siteOnLine L j hi x lo) < L)) = (κ && decide (x < L))) :
    bsum (fun x => if decide (coordAt L a (siteOnLine L j hi x lo) < L)
        && decide (coordAt L b (siteOnLine L j hi x lo) < L)
        && decide (coordAt L c (siteOnLine L j hi x lo) < L)
      then getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi x lo))
        * getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi x lo)) else BPair.unit)
      (List.range (L + 1))
      ≤ BPair.ofNat (L * L) * bsum (fun x => diffAt3 d L a b c j z (siteOnLine L j hi x lo)
        * diffAt3 d L a b c j z (siteOnLine L j hi x lo)) (List.range (L + 1)) := by
  refine leB_congr (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun x hx => ?_)))
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun x hx => ?_))))
    (line_telescope L (fun y => getAt BPair.unit z (cubeKey d L a b c (siteOnLine L j hi y lo))) κ)
  · rw [hκ x hx]
    exact BPair.oneValue_refl _
  · exact BPair.mul_congr (line_diff_read3 d L a b c j z hi lo hlo κ hκ x hx)
      (line_diff_read3 d L a b c j z hi lo hlo κ hκ x hx)

/-- A cube type's values' squares' fold sits at or below the side's
square against the differences' fold along any of the type's three
directions: the Dirichlet fold telescopes line by line. -/
theorem cube_sq_le (d L a b c j : Nat) (hab : a < b) (hbc : b < c) (hc : c < d)
    (hj : j = a ∨ j = b ∨ j = c) (z : List BPair) (hz : z.length = cubeCount d L) :
    bsum (fun s => if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L
        then getAt BPair.unit z (cubeKey d L a b c s) * getAt BPair.unit z (cubeKey d L a b c s)
        else BPair.unit) (List.range ((L + 1) ^ d))
      ≤ BPair.ofNat (L * L) * diffFold3 d L a b c j z := by
  have hjd : j < d := by
    cases hj with
    | inl h => rw [h]; exact Nat.lt_trans hab (Nat.lt_trans hbc hc)
    | inr h =>
      cases h with
      | inl h => rw [h]; exact Nat.lt_trans hbc hc
      | inr h => rw [h]; exact hc
  have hRG : ((j == a || j == b) || j == c) = true := by
    cases hj with
    | inl h => rw [h, eqBeqOf (rfl : a = a)]; rfl
    | inr h =>
      cases h with
      | inl h => rw [h, eqBeqOf (rfl : b = b), Bool.or_true]; rfl
      | inr h => rw [h, eqBeqOf (rfl : c = c)]; exact Bool.or_true _
  have hD : (diffFold3 d L a b c j z).oneValue
      (bsum (fun t => diffAt3 d L a b c j z t * diffAt3 d L a b c j z t)
        (List.range ((L + 1) ^ d))) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    rw [dotP_fold ((L + 1) ^ d) _ _ (by rw [matVec_length, diffMat3_length])
      (by rw [matVec_length, diffMat3_length])]
    refine bsum_congr_range_ov _ _ _ (fun t ht => ?_)
    have he := diff3_entry d L a b c j t z hz hab hbc hc ht
    rw [hRG, Bool.true_or, iteB_true] at he
    exact BPair.mul_congr he he
  refine leB_congr_right (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hD)) ?_
  refine leB_congr (BPair.oneValue_symm (bsum_site_split d L j hjd _))
    (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm (bsum_site_split d L j hjd _)))
    ?_
  refine leB_congr (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun hi _ => bsum_swap _ _ _)))
    (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (bsum_congr_range_ov _ _ _ (fun hi _ => bsum_swap _ _ _)))) ?_
  refine leB_congr_right (BPair.oneValue_trans
    (bsum_congr_range_ov _ _ _ (fun hi _ => foldB_mul_left _ _ _)) (foldB_mul_left _ _ _)) ?_
  refine bsum_le _ _ _ (fun hi _ => bsum_le _ _ _ (fun lo hlo => ?_))
  have hlo' : lo < (L + 1) ^ j := ltOfCountRange hlo
  cases hj with
  | inl hja =>
    subst hja
    refine line_read3 d L j b c j z hi lo hlo'
      (decide (coordAt L b (siteOnLine L j hi 0 lo) < L)
        && decide (coordAt L c (siteOnLine L j hi 0 lo) < L)) (fun x hx => ?_)
    rw [coordAt_siteOnLine L j hi x lo hx hlo',
      coordAt_siteOnLine_off L j b hi x lo (fun h => Nat.ne_of_lt hab h.symm) hx hlo',
      coordAt_siteOnLine_off L j c hi x lo (fun h => Nat.ne_of_lt (Nat.lt_trans hab hbc) h.symm)
        hx hlo']
    rw [Bool.and_assoc, Bool.and_comm]
  | inr hjbc =>
    cases hjbc with
    | inl hjb =>
      subst hjb
      refine line_read3 d L a j c j z hi lo hlo'
        (decide (coordAt L a (siteOnLine L j hi 0 lo) < L)
          && decide (coordAt L c (siteOnLine L j hi 0 lo) < L)) (fun x hx => ?_)
      rw [coordAt_siteOnLine L j hi x lo hx hlo',
        coordAt_siteOnLine_off L j a hi x lo (Nat.ne_of_lt hab) hx hlo',
        coordAt_siteOnLine_off L j c hi x lo (fun h => Nat.ne_of_lt hbc h.symm) hx hlo']
      rw [Bool.and_right_comm]
    | inr hjc =>
      subst hjc
      refine line_read3 d L a b j j z hi lo hlo'
        (decide (coordAt L a (siteOnLine L j hi 0 lo) < L)
          && decide (coordAt L b (siteOnLine L j hi 0 lo) < L)) (fun x hx => ?_)
      rw [coordAt_siteOnLine L j hi x lo hx hlo',
        coordAt_siteOnLine_off L j a hi x lo (Nat.ne_of_lt (Nat.lt_trans hab hbc)) hx hlo',
        coordAt_siteOnLine_off L j b hi x lo (Nat.ne_of_lt hbc) hx hlo']

/-- A constant through the cube types' fold. -/
private theorem const_types (c : BPair) (G : Nat → Nat → Nat → BPair) (d : Nat) :
    (c * bsum (fun a => bsum (fun b => bsum (fun e => if a < b && b < e then G a b e else BPair.unit)
      (List.range d)) (List.range d)) (List.range d)).oneValue
      (bsum (fun a => bsum (fun b => bsum (fun e => if a < b && b < e then c * G a b e else BPair.unit)
        (List.range d)) (List.range d)) (List.range d)) := by
  refine BPair.oneValue_symm (BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun a _ => ?_))
    (foldB_mul_left _ _ _))
  refine BPair.oneValue_trans (bsum_congr_range_ov _ _ d (fun b _ => ?_)) (foldB_mul_left _ _ _)
  refine BPair.oneValue_trans (bsum_congr_range_ov _
    (fun e => c * (if a < b && b < e then G a b e else BPair.unit)) d (fun e _ => ?_))
    (foldB_mul_left _ _ _)
  exact BPair.oneValue_trans (ite_congr_prop _ (fun _ => BPair.oneValue_of_eq (BPair.mul_comm c _)))
    (BPair.oneValue_trans (BPair.oneValue_symm (ite_mul_unit _ _ _))
      (BPair.oneValue_of_eq (BPair.mul_comm _ c)))

/-- The Poincaré read at a member of the cubes' range, the four-cells'
boundaries pairing it at the sum's unit: `3 zᵀ z ≤ L² zᵀ NᵀN z`, the
pair `[L² : 3]`'s comparison at its clearing; the self-pairing at or
below the side's square against any of the type's three directions'
differences' folds, and at or below a third of the side's square
against the three folds' join under the Hodge fold. -/
theorem cubePoincare_read (d L : Nat) (z : List BPair) (hz : z.length = cubeCount d L)
    (hker : poly.unitTail (matVec (transposeM (fourCellBd d L)) z)) :
    BPair.ofNat 3 * dotN z z ≤ BPair.ofNat (L * L) * quadForm (cubesGram d L) z := by
  have hself : (dotN z z).oneValue (bsum (fun a => bsum (fun b => bsum (fun c =>
      if a < b && b < c then
        bsum (fun s => if coordAt L a s < L && coordAt L b s < L && coordAt L c s < L
          then getAt BPair.unit z (cubeKey d L a b c s) * getAt BPair.unit z (cubeKey d L a b c s)
          else BPair.unit) (List.range ((L + 1) ^ d))
      else BPair.unit) (List.range d)) (List.range d)) (List.range d)) := by
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    rw [dotP_fold (cubeCount d L) z z hz hz]
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun p =>
      (fun Q : Nat × Nat × Nat × Nat => getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2)
        * getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2))
        (getAt (0, 0, 0, 0) (cubeList d L) p)) _ (fun p hp => ?_)) ?_
    · have hw : getAt BPair.unit z p = getAt BPair.unit z (cubeKey d L
          (getAt (0, 0, 0, 0) (cubeList d L) p).1 (getAt (0, 0, 0, 0) (cubeList d L) p).2.1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.1
          (getAt (0, 0, 0, 0) (cubeList d L) p).2.2.2) := by
        rw [cubeKey_of_getAt d L p hp]
      rw [hw]
      exact BPair.oneValue_refl _
    refine BPair.oneValue_trans (BPair.oneValue_of_eq (bsum_cube_places d L
      (fun Q : Nat × Nat × Nat × Nat => getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2)
        * getAt BPair.unit z (cubeKey d L Q.1 Q.2.1 Q.2.2.1 Q.2.2.2)))) ?_
    refine BPair.oneValue_trans (bsum_cube_triples d L _) ?_
    exact bsum_congr_range_ov _ _ d (fun a _ => bsum_congr_range_ov _ _ d (fun b _ =>
      bsum_congr_range_ov _ _ d (fun c _ => ite_congr_prop _ (fun _ =>
        bsum_congr_range_ov _ _ _ (fun s _ => ite_congr_prop _ (fun _ => BPair.oneValue_refl _))))))
  refine leB_congr_left (BPair.mul_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hself)) ?_
  refine leB_congr_right (BPair.mul_congr (BPair.oneValue_refl _)
    (BPair.oneValue_symm (hodgeForm3_range d L z hz hker))) ?_
  refine leB_congr (BPair.oneValue_symm (const_types _ _ d))
    (BPair.oneValue_symm (const_types _ _ d)) ?_
  refine bsum_le _ _ _ (fun a _ => bsum_le _ _ _ (fun b _ => bsum_le _ _ _ (fun c hc =>
    ite_le_prop _ (fun habc => ?_))))
  have hcd : c < d := ltOfCountRange hc
  have hab : a < b := of_decide_eq_true (andSplitB habc).1
  have hbc : b < c := of_decide_eq_true (andSplitB habc).2
  have hbd : b < d := Nat.lt_trans hbc hcd
  have had : a < d := Nat.lt_trans hab hbd
  have hDa := cube_sq_le d L a b c a hab hbc hcd (Or.inl rfl) z hz
  have hDb := cube_sq_le d L a b c b hab hbc hcd (Or.inr (Or.inl rfl)) z hz
  have hDc := cube_sq_le d L a b c c hab hbc hcd (Or.inr (Or.inr rfl)) z hz
  -- three against the self-pairing is the self-pairing three times
  refine leB_congr_left (BPair.oneValue_symm (BPair.oneValue_trans (ofNat_succ_mul 2 _)
    (BPair.add_congr (BPair.oneValue_trans (ofNat_succ_mul 1 _)
      (BPair.add_congr (BPair.ofNat_one_mul _) (BPair.oneValue_refl _)))
      (BPair.oneValue_refl _)))) ?_
  refine leB_trans (leB_add (leB_add hDa hDb) hDc) ?_
  refine leB_congr_left (BPair.oneValue_trans (BPair.oneValue_of_eq (BPair.left_distrib _ _ _))
    (BPair.add_congr (BPair.oneValue_of_eq (BPair.left_distrib _ _ _)) (BPair.oneValue_refl _))) ?_
  refine leB_mulR (unitLeOfNat _) ?_
  refine leB_congr_right (BPair.oneValue_symm (bsum_range_pick_three _ a b c d had hbd hcd
    (Nat.ne_of_lt hab) (Nat.ne_of_lt (Nat.lt_trans hab hbc)) (Nat.ne_of_lt hbc))) ?_
  refine leB_congr_left (BPair.oneValue_of_eq (BPair.add_assoc _ _ _).symm) ?_
  refine leB_add (leB_refl _) (leB_add (leB_refl _)
    (leB_congr_left (BPair.add_unit _) (leB_add (leB_refl _) ?_)))
  refine foldB_nonneg_mem _ _ (fun j _ => ?_)
  cases hg : ((j == a || j == b) || j == c) with
  | true => exact leB_refl _
  | false => exact diffFold3_unitLe d L a b c j z

/-! The kernel and the range: the kernel list's independence and
count, the descent in the last direction spanning the kernel at the
cubes' boundaries, and the range projector's four reads at the
adjugate identity. -/

/-- The cubes' boundaries' columns, the rows of the transposed list,
read the plaquettes' count. -/
theorem cubeBdT_rows (d L : Nat) : rowsLen (plaqCount d L) (transposeM (cubeBd d L)) := by
  have h := rowsLen_transposeM (cubeBd d L)
  rw [cubeBd_length] at h
  exact h

/-- The kernel list is independent, one member joined per refusal. -/
theorem kerList_indep (d L : Nat) : indepRows (plaqCount d L) (kerList d L) := by
  show indepRows _ (collectW _ (transposeM (cubeBd d L)))
  rw [collectW_eq _ _ (cubeBdT_rows d L)]
  exact collect_indep _ _ (cubeBdT_rows d L)

/-- The kernel list's rows read the plaquettes' count. -/
theorem kerList_rows (d L : Nat) : rowsLen (plaqCount d L) (kerList d L) :=
  (kerList_indep d L).1

/-- Every kernel list member sits in the cubes' boundaries' span. -/
theorem kerList_mem_span (d L m : Nat) (hm : m < (kerList d L).length) :
    spanRel (plaqCount d L) (transposeM (cubeBd d L)) (getAt [] (kerList d L) m) := by
  have hw : kerList d L = collectOf (plaqCount d L) (transposeM (cubeBd d L)) :=
    collectW_eq _ _ (cubeBdT_rows d L)
  rw [hw] at hm ⊢
  exact collect_row_span _ _ (cubeBdT_rows d L) m hm

/-- The kernel list's Gram determinant, the projector's clearing,
sits off the sum's unit at the independence. -/
theorem projDen_off (d L : Nat) : ¬ (projDen d L).oneValue BPair.unit :=
  fun h => indep_det _ _ (kerList_indep d L)
    (BPair.oneValue_trans (BPair.oneValue_symm (detD_eq _ (gramM_sq _))) h)

/-- The transposed incidence against a kernel list member reads the
sum's unit: the member sits in the cubes' boundaries' span and each
boundary pairs every link at that unit. -/
theorem kerList_ker (d L m : Nat) (hm : m < (kerList d L).length) :
    poly.unitTail (matVec (transposeM (incid d L)) (getAt [] (kerList d L) m)) := by
  have hN := cubeBdT_rows d L
  obtain ⟨c₀, cs, hc₀, hcs, hcomb⟩ := span_elim (kerList_mem_span d L m hm)
  have hcol : ∀ k, k < (transposeM (cubeBd d L)).length →
      poly.unitTail (matVec (transposeM (incid d L)) (getAt [] (transposeM (cubeBd d L)) k)) := by
    intro k hk
    refine unitTail_of_getAt _ (fun l hl => ?_)
    rw [matVec_length] at hl
    rw [getAt_matVec _ _ l hl]
    have hb := matNull_getAt _ (bdRead_all d L) l k
    rw [entry_matMul _ _ l k hl hk] at hb
    exact hb
  refine unitTail_unscale c₀ hc₀ _ ?_
  refine poly.oneValue_unitTail (poly.oneValue_symm (matVec_vecScale_free _ c₀ _)) ?_
  refine poly.oneValue_unitTail (matVec_congr _ _ _ hcomb) ?_
  refine poly.oneValue_unitTail (matVec_combo _ _ cs _ hN) ?_
  refine unitTail_combo_rows _ cs _ (fun k hk => ?_)
  rw [ground.length_map] at hk
  rw [getAt_map [] [] _ _ k hk]
  exact hcol k hk

/-! The descent in the last direction: the window one position
shorter at a direction and a level, the level's read, and the
kernel's span read at the cubes' boundaries. -/

/-- The window one position shorter at a direction and a level: a
plaquette whose coordinates beyond the direction sit at the first
position, whose plane sits within the directions at or below it,
and whose corner's coordinate at the direction, raised by one at a
plane through the direction, sits at or below the level. -/
private def levelB (d L j t : Nat) (q : Nat × Nat × Nat) : Bool :=
  (List.range d).all (fun i => !decide (j < i) || decide (coordAt L i q.2.2 = 0))
    && decide (q.2.1 ≤ j)
    && decide (coordAt L j q.2.2 + (if q.2.1 == j then 1 else 0) ≤ t)

/-- The level's read: the three clauses. -/
private theorem levelB_read (d L j t : Nat) (q : Nat × Nat × Nat) :
    levelB d L j t q = true ↔
      (∀ i, j < i → i < d → coordAt L i q.2.2 = 0) ∧ q.2.1 ≤ j
        ∧ coordAt L j q.2.2 + (if q.2.1 == j then 1 else 0) ≤ t := by
  constructor
  · intro h
    have h1 := andSplitB h
    have h2 := andSplitB h1.1
    refine ⟨fun i hji hid => ?_, of_decide_eq_true h2.2, of_decide_eq_true h1.2⟩
    have h3 := all_range_read d h2.1 i hid
    rw [decide_eq_true hji] at h3
    exact of_decide_eq_true h3
  · intro ⟨h1, h2, h3⟩
    show ((List.range d).all (fun i => !decide (j < i) || decide (coordAt L i q.2.2 = 0))
      && decide (q.2.1 ≤ j) && decide (coordAt L j q.2.2 + (if q.2.1 == j then 1 else 0) ≤ t))
      = true
    rw [decide_eq_true h2, decide_eq_true h3, Bool.and_true, Bool.and_true]
    refine all_range_intro d (fun i hi => ?_)
    by_cases hji : j < i
    · rw [decide_eq_true (h1 i hji hi)]
      exact Bool.or_true _
    · rw [decide_eq_false hji]
      rfl


/-- The descent's coefficient at a cube: at a cube whose highest
direction is the descent's with its corner at the level, the
plaquette vector's read at the cube's top face, the face of the two
lower directions at the corner stepped along the descent's
direction; the sum's unit at every further cube. -/
private def topCoef (d L j t : Nat) (W : List BPair) (C : Nat × Nat × Nat × Nat) : BPair :=
  if C.2.2.1 == j && coordAt L j C.2.2.2 == t
    then getAt BPair.unit W (plaqKey d L C.1 C.2.1 (stepAt L j C.2.2.2)) else BPair.unit

/-- The descent's family over the cube places: the cube's boundary
scaled at its coefficient, the unit family off the cubes. -/
private def stepFam (d L j t : Nat) (W : List BPair) (c : Nat) : List BPair :=
  if c < cubeCount d L then
    vecScale (topCoef d L j t W (getAt (0, 0, 0, 0) (cubeList d L) c))
      (getAt [] (transposeM (cubeBd d L)) c)
  else List.replicate (plaqCount d L) BPair.unit

/-- The descent's combination of the cubes' boundaries. -/
private def stepV (d L j t : Nat) (W : List BPair) : List BPair :=
  vsum (plaqCount d L) (stepFam d L j t W) (List.range (cubeCount d L))

private theorem stepFam_len (d L j t : Nat) (W : List BPair) :
    ∀ c, (stepFam d L j t W c).length = plaqCount d L := by
  intro c
  delta stepFam
  by_cases hc : c < cubeCount d L
  · rw [if_pos hc, length_vecScale]
    exact rowsLen_getAt _ c (cubeBdT_rows d L) (by rw [cubeBdT_length d L]; exact hc)
  · rw [if_neg hc]
    exact length_replicate _ _

private theorem stepV_len (d L j t : Nat) (W : List BPair) :
    (stepV d L j t W).length = plaqCount d L :=
  length_vsum _ _ _ (fun c _ => stepFam_len d L j t W c)

/-- The descent's combination's entry at a plaquette's place: the
cubes' faces' signs at the plaquette against the coefficients,
folded over the cubes. -/
private theorem stepV_entry (d L j t : Nat) (W : List BPair)
    (p : Nat) (hp : p < plaqCount d L) :
    (getAt BPair.unit (stepV d L j t W) p).oneValue
      (bsum (fun C => faceSign (cubeFaces d L C) p * topCoef d L j t W C) (cubeList d L)) := by
  refine BPair.oneValue_trans (vsum_entry _ _ (stepFam_len d L j t W) _ p hp) ?_
  rw [← bsum_cube_places d L (fun C => faceSign (cubeFaces d L C) p * topCoef d L j t W C)]
  refine bsum_congr_range_ov _ _ _ (fun c hc => ?_)
  delta stepFam
  rw [if_pos hc, getAt_vecScale _ _ p (by
    rw [rowsLen_getAt _ c (cubeBdT_rows d L) (by rw [cubeBdT_length d L]; exact hc)]
    exact hp),
    getAt_transposeM BPair.unit _ (cubeBd_rows d L) c p hc (by rw [cubeBd_length]; exact hp),
    cubeBd_entry d L p c hp hc]
  exact BPair.oneValue_of_eq (BPair.mul_comm _ _)

/-- The descent's combination's entry at a plaquette's key: the
cubes holding the plaquette at their coefficients. -/
private theorem stepV_key (d L j t : Nat) (W : List BPair)
    (a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) :
    (getAt BPair.unit (stepV d L j t W) (plaqKey d L a k s)).oneValue
      (bsum (fun z => if decide (k < z) then
          (if decide (coordAt L z s < L) then topCoef d L j t W (a, k, z, s) else BPair.unit)
          + (if 0 < coordAt L z s then (topCoef d L j t W (a, k, z, s - (L + 1) ^ z)).swap
            else BPair.unit)
        else BPair.unit) (List.range d)
      + (bsum (fun y => if decide (a < y) && decide (y < k) then
          (if decide (coordAt L y s < L) then (topCoef d L j t W (a, y, k, s)).swap else BPair.unit)
          + (if 0 < coordAt L y s then topCoef d L j t W (a, y, k, s - (L + 1) ^ y) else BPair.unit)
        else BPair.unit) (List.range d)
      + bsum (fun x => if decide (x < a) then
          (if decide (coordAt L x s < L) then topCoef d L j t W (x, a, k, s) else BPair.unit)
          + (if 0 < coordAt L x s then (topCoef d L j t W (x, a, k, s - (L + 1) ^ x)).swap
            else BPair.unit)
        else BPair.unit) (List.range d))) :=
  BPair.oneValue_trans (stepV_entry d L j t W _ (plaqKey_lt d L a k s hak hk hs hca hck))
    (cubes_holding d L a k s hak hk hs hca hck _)

/-- The descent's combination pairs every link at the sum's unit:
each cube's boundary does. -/
private theorem stepV_ker (d L j t : Nat) (W : List BPair) :
    poly.unitTail (matVec (transposeM (incid d L)) (stepV d L j t W)) := by
  refine poly.oneValue_unitTail (matVec_vsum _ _ _ (stepFam_len d L j t W) _) ?_
  refine vsum_null _ _ (fun c => matVec_length _ _) _ (fun c _ => ?_)
  delta stepFam
  by_cases hc : c < cubeCount d L
  · rw [if_pos hc]
    refine poly.oneValue_unitTail (matVec_vecScale_free _ _ _) ?_
    refine unitTail_vecScale _ _ ?_
    refine unitTail_of_getAt _ (fun l hl => ?_)
    rw [matVec_length] at hl
    rw [getAt_matVec _ _ l hl]
    have hb := matNull_getAt _ (bdRead_all d L) l c
    rw [entry_matMul _ _ l c hl (by rw [cubeBdT_length d L]; exact hc)] at hb
    exact hb
  · rw [if_neg hc]
    exact matVec_units _ _

/-- The descent's combination sits in the cubes' boundaries' span. -/
private theorem stepV_span (d L j t : Nat) (W : List BPair) :
    spanRel (plaqCount d L) (transposeM (cubeBd d L)) (stepV d L j t W) := by
  refine vsum_span _ _ (cubeBdT_rows d L) _ (stepFam_len d L j t W) (fun c => ?_) _
  delta stepFam
  by_cases hc : c < cubeCount d L
  · rw [if_pos hc]
    refine spanRel_scale _ _ _ _ (cubeBdT_rows d L) ?_ ?_
    · exact rowsLen_getAt _ c (cubeBdT_rows d L) (by rw [cubeBdT_length d L]; exact hc)
    · exact spanRel_getAt _ _ c (by rw [cubeBdT_length d L]; exact hc) (cubeBdT_rows d L)
  · rw [if_neg hc]
    exact spanRel_null _ _ _ (poly.unitTail_replicate _) (cubeBdT_rows d L) (length_replicate _ _)


/-- The coefficient at a cube off the descent's direction is the
sum's unit. -/
private theorem topCoef_dir (d L j t : Nat) (W : List BPair) (C : Nat × Nat × Nat × Nat)
    (h : ¬ C.2.2.1 = j) : topCoef d L j t W C = BPair.unit := by
  delta topCoef
  rw [neBeqOf h, Bool.false_and]
  rfl

/-- The coefficient at a cube whose corner sits off the level is the
sum's unit. -/
private theorem topCoef_lev (d L j t : Nat) (W : List BPair) (C : Nat × Nat × Nat × Nat)
    (h : ¬ coordAt L j C.2.2.2 = t) : topCoef d L j t W C = BPair.unit := by
  delta topCoef
  rw [neBeqOf h, Bool.and_false]
  rfl

/-- The coefficient at a cube of the descent's direction with its
corner at the level is the vector's read at the cube's top face. -/
private theorem topCoef_on (d L j t : Nat) (W : List BPair) (C : Nat × Nat × Nat × Nat)
    (h1 : C.2.2.1 = j) (h2 : coordAt L j C.2.2.2 = t) :
    topCoef d L j t W C = getAt BPair.unit W (plaqKey d L C.1 C.2.1 (stepAt L j C.2.2.2)) := by
  delta topCoef
  rw [eqBeqOf h1, eqBeqOf h2]
  rfl

/-- The descent's combination at a top face, a plaquette off the
descent's direction with its corner one step beyond the level: the
balance partner of the vector's read there, the cube below the face
alone contributing at its face's sign. -/
private theorem stepV_top (d L j t : Nat) (W : List BPair)
    (a k s : Nat) (hak : a < k) (hkj : k < j) (hj : j < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (hcj : coordAt L j s = t + 1) :
    (getAt BPair.unit (stepV d L j t W) (plaqKey d L a k s)).oneValue
      (getAt BPair.unit W (plaqKey d L a k s)).swap := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  have hkd : k < d := Nat.lt_trans hkj hj
  have hkj' : ¬ k = j := Nat.ne_of_lt hkj
  refine BPair.oneValue_trans (stepV_key d L j t W a k s hak hkd hs hca hck) ?_
  -- the second and third sums read the unit, the cubes off the direction
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.add_units
    (foldB_nullRange _ d (fun y _ => ?_)) (foldB_nullRange _ d (fun x _ => ?_)))) ?_
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [topCoef_dir d L j t W (a, y, k, s) hkj', topCoef_dir d L j t W (a, y, k, s - (L + 1) ^ y) hkj',
      show (BPair.unit).swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
    exact BPair.unit_add _
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [topCoef_dir d L j t W (x, a, k, s) hkj', topCoef_dir d L j t W (x, a, k, s - (L + 1) ^ x) hkj',
      show (BPair.unit).swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
    exact BPair.unit_add _
  refine BPair.oneValue_trans (BPair.add_unit _) ?_
  -- the first sum picks the cube below the face along the descent's direction
  refine BPair.oneValue_trans (bsum_range_pick _ j d hj (fun z _ hzj => ?_)) ?_
  · refine BPair.oneValue_trans (ite_congr_prop _ (fun _ => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _))
    rw [topCoef_dir d L j t W (a, k, z, s) hzj, topCoef_dir d L j t W (a, k, z, s - (L + 1) ^ z) hzj,
      show (BPair.unit).swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
    exact BPair.unit_add _
  rw [if_pos (decide_eq_true hkj)]
  have hpos : 0 < coordAt L j s := by rw [hcj]; exact Nat.succ_pos t
  obtain ⟨hs0e, hd, _⟩ := stepBack (L + 1) j s hL hpos
  have hlev : coordAt L j (s - (L + 1) ^ j) = t := by
    have hd' : coordAt L j (s - (L + 1) ^ j) + 1 = coordAt L j s := hd
    rw [hcj] at hd'
    exact Nat.succ.inj hd'
  rw [topCoef_lev d L j t W (a, k, j, s) (by rw [hcj]; exact Nat.succ_ne_self t), ite_prop_unit,
    if_pos hpos, topCoef_on d L j t W (a, k, j, s - (L + 1) ^ j) rfl hlev,
    show stepAt L j (s - (L + 1) ^ j) = s from hs0e]
  exact BPair.unit_add _


/-- A plaquette vector is the map of its reads at the plaquette
keys over the plaquette list. -/
private theorem vec_as_map (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L) :
    W = (plaqList d L).map (fun q => getAt BPair.unit W (plaqKey d L q.1 q.2.1 q.2.2)) := by
  refine getAt_ext BPair.unit _ _ (by rw [length_map]; exact hW) (fun p hp => ?_)
  rw [hW] at hp
  rw [getAt_map (0, 0, 0) BPair.unit _ _ p hp, plaqKey_of_getAt d L p hp]

/-- A level read refused at a plaquette whose coordinate at the
direction, raised at a plane through it, exceeds the level. -/
private theorem levelB_off_high (d L j t : Nat) (q : Nat × Nat × Nat)
    (h : t < coordAt L j q.2.2 + (if q.2.1 == j then 1 else 0)) :
    levelB d L j t q = false := by
  cases hl : levelB d L j t q with
  | true => exact absurd ((levelB_read d L j t q).1 hl).2.2 (Nat.not_le_of_gt h)
  | false => rfl

/-- A level read refused at a plaquette whose plane sits beyond the
direction. -/
private theorem levelB_off_plane (d L j t : Nat) (q : Nat × Nat × Nat) (h : j < q.2.1) :
    levelB d L j t q = false := by
  cases hl : levelB d L j t q with
  | true => exact absurd ((levelB_read d L j t q).1 hl).2.1 (Nat.not_le_of_gt h)
  | false => rfl

/-- A level read refused at a plaquette with an occupied coordinate
beyond the direction. -/
private theorem levelB_off_above (d L j t : Nat) (q : Nat × Nat × Nat) (i : Nat) (hji : j < i)
    (hid : i < d) (h : ¬ coordAt L i q.2.2 = 0) : levelB d L j t q = false := by
  cases hl : levelB d L j t q with
  | true => exact absurd (((levelB_read d L j t q).1 hl).1 i hji hid) h
  | false => rfl

/-- The supported vector reads the unit at a valid plaquette off the
level. -/
private theorem supp_read (d L j t : Nat) (W : List BPair)
    (hsup : ∀ p, p < plaqCount d L → levelB d L j t (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit)
    (a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L)
    (hoff : levelB d L j t (a, k, s) = false) :
    (getAt BPair.unit W (plaqKey d L a k s)).oneValue BPair.unit := by
  refine hsup _ (plaqKey_lt d L a k s hak hk hs hca hck) ?_
  rw [plaqKey_read d L a k s hak hk hs hca hck]
  exact hoff


/-- A refused level read: an occupied coordinate beyond the
direction, a plane beyond the direction, or the corner's coordinate
raised at a plane through it beyond the level. -/
private theorem levelB_false_cases (d L j t : Nat) (q : Nat × Nat × Nat)
    (h : levelB d L j t q = false) :
    (∃ i, j < i ∧ i < d ∧ ¬ coordAt L i q.2.2 = 0) ∨ j < q.2.1
      ∨ t < coordAt L j q.2.2 + (if q.2.1 == j then 1 else 0) := by
  delta levelB at h
  cases hall : (List.range d).all (fun i => !decide (j < i) || decide (coordAt L i q.2.2 = 0)) with
  | false =>
    obtain ⟨i, hi, hfi⟩ := exists_of_all_false _ _ hall
    refine Or.inl ⟨i, ?_, ltOfMemRange hi, ?_⟩
    · cases hji : decide (j < i) with
      | true => exact of_decide_eq_true hji
      | false =>
        rw [hji] at hfi
        exact Bool.noConfusion hfi
    · intro hc
      rw [decide_eq_true hc, Bool.or_true] at hfi
      exact Bool.noConfusion hfi
  | true =>
    rw [hall, Bool.true_and] at h
    cases hkj : decide (q.2.1 ≤ j) with
    | false => exact Or.inr (Or.inl (Nat.gt_of_not_le (of_decide_eq_false hkj)))
    | true =>
      rw [hkj, Bool.true_and] at h
      exact Or.inr (Or.inr (Nat.gt_of_not_le (of_decide_eq_false h)))

/-- The coefficient at a cube reads the sum's unit where the cube's
top face is off the level above, or the cube sits off the direction
or off the level. -/
private theorem topCoef_unit_of (d L j t : Nat) (W : List BPair)
    (hsup : ∀ p, p < plaqCount d L →
      levelB d L j (t + 1) (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit)
    (x y z c : Nat) (hxy : x < y) (hyz : y < z) (hz : z < d) (hc : c < (L + 1) ^ d)
    (hcx : coordAt L x c < L) (hcy : coordAt L y c < L) (hcz : coordAt L z c < L)
    (hoff : z = j → coordAt L j c = t → levelB d L j (t + 1) (x, y, stepAt L j c) = false) :
    (topCoef d L j t W (x, y, z, c)).oneValue BPair.unit := by
  by_cases hzj : z = j
  · by_cases hct : coordAt L j c = t
    · rw [topCoef_on d L j t W (x, y, z, c) hzj hct]
      have hcj : coordAt L j c < L := by rw [← hzj]; exact hcz
      have hxj : ¬ x = j := Nat.ne_of_lt (Nat.lt_of_lt_of_eq (Nat.lt_trans hxy hyz) hzj)
      have hyj : ¬ y = j := Nat.ne_of_lt (Nat.lt_of_lt_of_eq hyz hzj)
      refine supp_read d L j (t + 1) W hsup x y _ hxy (Nat.lt_trans hyz hz)
        (stepAt_lt d L j c (by rw [← hzj]; exact hz) hc hcj) ?_ ?_ (hoff hzj hct)
      · rw [coordAt_step_ne L j x c hcj hxj]
        exact hcx
      · rw [coordAt_step_ne L j y c hcj hyj]
        exact hcy
    · rw [topCoef_lev d L j t W (x, y, z, c) hct]
      exact BPair.oneValue_refl _
  · rw [topCoef_dir d L j t W (x, y, z, c) hzj]
    exact BPair.oneValue_refl _

/-- The coefficient at a cube of the descent's direction reads the
unit at a plaquette off the level above by an occupied coordinate
beyond the direction: the cube's top face shares the coordinate. -/
private theorem topCoef_unit_above (d L j t : Nat) (W : List BPair)
    (hsup : ∀ p, p < plaqCount d L →
      levelB d L j (t + 1) (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit)
    (x y z c : Nat) (hxy : x < y) (hyz : y < z) (hz : z < d) (hc : c < (L + 1) ^ d)
    (hcx : coordAt L x c < L) (hcy : coordAt L y c < L) (hcz : coordAt L z c < L)
    (i : Nat) (hji : j < i) (hid : i < d) (hne : ¬ coordAt L i c = 0) :
    (topCoef d L j t W (x, y, z, c)).oneValue BPair.unit := by
  refine topCoef_unit_of d L j t W hsup x y z c hxy hyz hz hc hcx hcy hcz (fun hzj _ => ?_)
  refine levelB_off_above d L j (t + 1) (x, y, stepAt L j c) i hji hid ?_
  show ¬ coordAt L i (stepAt L j c) = 0
  rw [coordAt_step_ne L j i c (by rw [← hzj]; exact hcz) (Nat.ne_of_gt hji)]
  exact hne

/-- The descent's combination reads the sum's unit at a plaquette
off the level above: every cube holding it either sits off the
direction or the level, or has its top face off the level above. -/
private theorem stepV_off (d L j t : Nat) (W : List BPair)
    (hsup : ∀ p, p < plaqCount d L →
      levelB d L j (t + 1) (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit)
    (a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L)
    (hviol : (∃ i, j < i ∧ i < d ∧ ¬ coordAt L i s = 0) ∨ j < k
      ∨ t + 1 < coordAt L j s + (if k == j then 1 else 0)) :
    (getAt BPair.unit (stepV d L j t W) (plaqKey d L a k s)).oneValue BPair.unit := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  refine BPair.oneValue_trans (stepV_key d L j t W a k s hak hk hs hca hck) ?_
  refine BPair.add_units (foldB_nullRange _ d (fun z hzd => ?_))
    (BPair.add_units (foldB_nullRange _ d (fun y hyd => ?_)) (foldB_nullRange _ d (fun x hxd => ?_)))
  · -- the cubes beyond the plane
    refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hkz => ?_))
      (BPair.oneValue_of_eq (ite_prop_unit _))
    have hkz' : k < z := of_decide_eq_true hkz
    refine BPair.add_units (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _
      (fun hcz => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _)))
      (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hpos => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _)))
    · rcases hviol with ⟨i, hji, hid, hne⟩ | hjk | hhigh
      · exact topCoef_unit_above d L j t W hsup a k z s hak hkz' hzd hs hca hck
          (of_decide_eq_true hcz) i hji hid hne
      · refine topCoef_unit_of d L j t W hsup a k z s hak hkz' hzd hs hca hck
          (of_decide_eq_true hcz) (fun hzj _ => ?_)
        exact absurd (Nat.lt_of_lt_of_eq (Nat.lt_trans hjk hkz') hzj) (Nat.lt_irrefl j)
      · refine topCoef_unit_of d L j t W hsup a k z s hak hkz' hzd hs hca hck
          (of_decide_eq_true hcz) (fun hzj hct => ?_)
        have hkj : ¬ k = j := Nat.ne_of_lt (Nat.lt_of_lt_of_eq hkz' hzj)
        rw [hct, neBeqOf hkj] at hhigh
        exact absurd (show t + 1 < t + 0 from hhigh) (by
          rw [Nat.add_zero]
          exact Nat.not_lt_of_ge (Nat.le_succ t))
    · obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) z s hL hpos
      have hlt : s - (L + 1) ^ z < (L + 1) ^ d :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) hs
      have hcz' : coordAt L z (s - (L + 1) ^ z) < L := by
        have h := baseDigit_lt (L + 1) z s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      have hca' : coordAt L a (s - (L + 1) ^ z) < L := by
        rw [show coordAt L a (s - (L + 1) ^ z) = coordAt L a s from
          hoff a (Nat.ne_of_lt (Nat.lt_trans hak hkz'))]
        exact hca
      have hck' : coordAt L k (s - (L + 1) ^ z) < L := by
        rw [show coordAt L k (s - (L + 1) ^ z) = coordAt L k s from hoff k (Nat.ne_of_lt hkz')]
        exact hck
      show (topCoef d L j t W (a, k, z, s - (L + 1) ^ z)).swap.oneValue BPair.unit.swap
      refine swap_congr ?_
      rcases hviol with ⟨i, hji, hid, hne⟩ | hjk | hhigh
      · refine topCoef_unit_of d L j t W hsup a k z _ hak hkz' hzd hlt hca' hck' hcz'
          (fun hzj _ => ?_)
        refine levelB_off_above d L j (t + 1) (a, k, stepAt L j (s - (L + 1) ^ z)) i hji hid ?_
        show ¬ coordAt L i (stepAt L j (s - (L + 1) ^ z)) = 0
        rw [coordAt_step_ne L j i _ (by rw [← hzj]; exact hcz') (Nat.ne_of_gt hji),
          show coordAt L i (s - (L + 1) ^ z) = coordAt L i s from
            hoff i (Nat.ne_of_gt (show z < i by rw [hzj]; exact hji))]
        exact hne
      · refine topCoef_unit_of d L j t W hsup a k z _ hak hkz' hzd hlt hca' hck' hcz'
          (fun hzj _ => ?_)
        exact absurd (Nat.lt_of_lt_of_eq (Nat.lt_trans hjk hkz') hzj) (Nat.lt_irrefl j)
      · refine topCoef_unit_of d L j t W hsup a k z _ hak hkz' hzd hlt hca' hck' hcz'
          (fun hzj hct => ?_)
        have hkj : ¬ k = j := Nat.ne_of_lt (Nat.lt_of_lt_of_eq hkz' hzj)
        have hd' : coordAt L j (s - (L + 1) ^ z) + 1 = coordAt L j s := by rw [← hzj]; exact hd
        rw [hct] at hd'
        rw [← hd', neBeqOf hkj] at hhigh
        exact absurd (show t + 1 < t + 1 + 0 from hhigh) (by
          rw [Nat.add_zero]
          exact Nat.lt_irrefl _)
  · -- the cubes at a middle direction
    refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hg => ?_))
      (BPair.oneValue_of_eq (ite_prop_unit _))
    have hay : a < y := of_decide_eq_true (andSplitB hg).1
    have hyk : y < k := of_decide_eq_true (andSplitB hg).2
    refine BPair.add_units (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _
      (fun hcy => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _)))
      (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hpos => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _)))
    · show (topCoef d L j t W (a, y, k, s)).swap.oneValue BPair.unit.swap
      refine swap_congr ?_
      rcases hviol with ⟨i, hji, hid, hne⟩ | hjk | hhigh
      · exact topCoef_unit_above d L j t W hsup a y k s hay hyk hk hs hca (of_decide_eq_true hcy)
          hck i hji hid hne
      · refine topCoef_unit_of d L j t W hsup a y k s hay hyk hk hs hca (of_decide_eq_true hcy) hck
          (fun hkj _ => ?_)
        exact absurd (Nat.lt_of_lt_of_eq hjk hkj) (Nat.lt_irrefl j)
      · refine topCoef_unit_of d L j t W hsup a y k s hay hyk hk hs hca (of_decide_eq_true hcy) hck
          (fun hkj hct => ?_)
        rw [hct, eqBeqOf hkj] at hhigh
        exact absurd (show t + 1 < t + 1 from hhigh) (Nat.lt_irrefl _)
    · obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) y s hL hpos
      have hlt : s - (L + 1) ^ y < (L + 1) ^ d :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) hs
      have hcy' : coordAt L y (s - (L + 1) ^ y) < L := by
        have h := baseDigit_lt (L + 1) y s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      have hca' : coordAt L a (s - (L + 1) ^ y) < L := by
        rw [show coordAt L a (s - (L + 1) ^ y) = coordAt L a s from hoff a (Nat.ne_of_lt hay)]
        exact hca
      have hck' : coordAt L k (s - (L + 1) ^ y) < L := by
        rw [show coordAt L k (s - (L + 1) ^ y) = coordAt L k s from hoff k (Nat.ne_of_gt hyk)]
        exact hck
      rcases hviol with ⟨i, hji, hid, hne⟩ | hjk | hhigh
      · refine topCoef_unit_of d L j t W hsup a y k _ hay hyk hk hlt hca' hcy' hck'
          (fun hkj _ => ?_)
        refine levelB_off_above d L j (t + 1) (a, y, stepAt L j (s - (L + 1) ^ y)) i hji hid ?_
        show ¬ coordAt L i (stepAt L j (s - (L + 1) ^ y)) = 0
        rw [coordAt_step_ne L j i _ (by rw [← hkj]; exact hck') (Nat.ne_of_gt hji),
          show coordAt L i (s - (L + 1) ^ y) = coordAt L i s from
            hoff i (Nat.ne_of_gt (Nat.lt_trans (Nat.lt_of_lt_of_eq hyk hkj) hji))]
        exact hne
      · refine topCoef_unit_of d L j t W hsup a y k _ hay hyk hk hlt hca' hcy' hck'
          (fun hkj _ => ?_)
        exact absurd (Nat.lt_of_lt_of_eq hjk hkj) (Nat.lt_irrefl j)
      · refine topCoef_unit_of d L j t W hsup a y k _ hay hyk hk hlt hca' hcy' hck'
          (fun hkj hct => ?_)
        have hyj : ¬ y = j := Nat.ne_of_lt (Nat.lt_of_lt_of_eq hyk hkj)
        rw [show coordAt L j (s - (L + 1) ^ y) = coordAt L j s from
          hoff j (fun h => hyj h.symm)] at hct
        rw [hct, eqBeqOf hkj] at hhigh
        exact absurd (show t + 1 < t + 1 from hhigh) (Nat.lt_irrefl _)
  · -- the cubes at a lower direction
    refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hg => ?_))
      (BPair.oneValue_of_eq (ite_prop_unit _))
    have hxa : x < a := of_decide_eq_true hg
    refine BPair.add_units (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _
      (fun hcx => ?_)) (BPair.oneValue_of_eq (ite_prop_unit _)))
      (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hpos => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _)))
    · rcases hviol with ⟨i, hji, hid, hne⟩ | hjk | hhigh
      · exact topCoef_unit_above d L j t W hsup x a k s hxa hak hk hs (of_decide_eq_true hcx) hca
          hck i hji hid hne
      · refine topCoef_unit_of d L j t W hsup x a k s hxa hak hk hs (of_decide_eq_true hcx) hca hck
          (fun hkj _ => ?_)
        exact absurd (Nat.lt_of_lt_of_eq hjk hkj) (Nat.lt_irrefl j)
      · refine topCoef_unit_of d L j t W hsup x a k s hxa hak hk hs (of_decide_eq_true hcx) hca hck
          (fun hkj hct => ?_)
        rw [hct, eqBeqOf hkj] at hhigh
        exact absurd (show t + 1 < t + 1 from hhigh) (Nat.lt_irrefl _)
    · obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) x s hL hpos
      have hlt : s - (L + 1) ^ x < (L + 1) ^ d :=
        Nat.lt_of_le_of_lt (Nat.sub_le _ _) hs
      have hcx' : coordAt L x (s - (L + 1) ^ x) < L := by
        have h := baseDigit_lt (L + 1) x s hL
        rw [← hd] at h
        exact Nat.lt_of_succ_lt_succ h
      have hca' : coordAt L a (s - (L + 1) ^ x) < L := by
        rw [show coordAt L a (s - (L + 1) ^ x) = coordAt L a s from hoff a (Nat.ne_of_gt hxa)]
        exact hca
      have hck' : coordAt L k (s - (L + 1) ^ x) < L := by
        rw [show coordAt L k (s - (L + 1) ^ x) = coordAt L k s from
          hoff k (Nat.ne_of_gt (Nat.lt_trans hxa hak))]
        exact hck
      show (topCoef d L j t W (x, a, k, s - (L + 1) ^ x)).swap.oneValue BPair.unit.swap
      refine swap_congr ?_
      rcases hviol with ⟨i, hji, hid, hne⟩ | hjk | hhigh
      · refine topCoef_unit_of d L j t W hsup x a k _ hxa hak hk hlt hcx' hca' hck'
          (fun hkj _ => ?_)
        refine levelB_off_above d L j (t + 1) (x, a, stepAt L j (s - (L + 1) ^ x)) i hji hid ?_
        show ¬ coordAt L i (stepAt L j (s - (L + 1) ^ x)) = 0
        rw [coordAt_step_ne L j i _ (by rw [← hkj]; exact hck') (Nat.ne_of_gt hji),
          show coordAt L i (s - (L + 1) ^ x) = coordAt L i s from
            hoff i (Nat.ne_of_gt (Nat.lt_trans (Nat.lt_of_lt_of_eq (Nat.lt_trans hxa hak) hkj) hji))]
        exact hne
      · refine topCoef_unit_of d L j t W hsup x a k _ hxa hak hk hlt hcx' hca' hck'
          (fun hkj _ => ?_)
        exact absurd (Nat.lt_of_lt_of_eq hjk hkj) (Nat.lt_irrefl j)
      · refine topCoef_unit_of d L j t W hsup x a k _ hxa hak hk hlt hcx' hca' hck'
          (fun hkj hct => ?_)
        have hxj : ¬ x = j := Nat.ne_of_lt (Nat.lt_of_lt_of_eq (Nat.lt_trans hxa hak) hkj)
        rw [show coordAt L j (s - (L + 1) ^ x) = coordAt L j s from
          hoff j (fun h => hxj h.symm)] at hct
        rw [hct, eqBeqOf hkj] at hhigh
        exact absurd (show t + 1 < t + 1 from hhigh) (Nat.lt_irrefl _)


/-- The stepped vector reads the sum's unit at a plaquette whose
corner's coordinate at the descent's direction sits one beyond the
level: at a plane below the direction a top face, the vector's read
withdrawn at its cube's boundary's multiple; at a plane through or
beyond the direction a plaquette off the level above, the vector and
the combination each at the unit. -/
private theorem stepped_above (d L j t : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hsup : ∀ p, p < plaqCount d L →
      levelB d L j (t + 1) (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit)
    (a k s : Nat) (hak : a < k) (hk : k < d) (hj : j < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) (hcj : coordAt L j s = t + 1) :
    (getAt BPair.unit (vecAdd W (stepV d L j t W)) (plaqKey d L a k s)).oneValue BPair.unit := by
  have hp := plaqKey_lt d L a k s hak hk hs hca hck
  rw [getAt_vecAdd _ _ _ (by rw [hW]; exact hp) (by rw [stepV_len d L j t W]; exact hp)]
  rcases Nat.lt_trichotomy k j with hkj | hkj | hkj
  · exact BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
      (stepV_top d L j t W a k s hak hkj hj hs hca hck hcj)) (BPair.add_swap_null _)
  · have hh : t + 1 < coordAt L j s + (if k == j then 1 else 0) := by
      rw [hcj, eqBeqOf hkj]
      show t + 1 < t + 1 + 1
      exact Nat.lt_succ_self _
    exact BPair.add_units (supp_read d L j (t + 1) W hsup a k s hak hk hs hca hck
        (levelB_off_high d L j (t + 1) (a, k, s) hh))
      (stepV_off d L j t W hsup a k s hak hk hs hca hck (Or.inr (Or.inr hh)))
  · exact BPair.add_units (supp_read d L j (t + 1) W hsup a k s hak hk hs hca hck
        (levelB_off_plane d L j (t + 1) (a, k, s) hkj))
      (stepV_off d L j t W hsup a k s hak hk hs hca hck (Or.inr (Or.inl hkj)))

/-- The stepped vector reads the sum's unit at a plaquette of a plane
off the descent's direction at a corner stepped back along one of
the plane's directions from a corner one beyond the level: the
stepped-back corner sits one beyond the level as well. -/
private theorem stepped_back (d L j t : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hsup : ∀ p, p < plaqCount d L →
      levelB d L j (t + 1) (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit)
    (a k z s' : Nat) (hak : a < k) (hk : k < d) (hj : j < d) (hs' : s' < (L + 1) ^ d)
    (hzj : ¬ z = j) (hzpos : 0 < coordAt L z s')
    (hz : (z = a ∧ coordAt L k s' < L) ∨ (z = k ∧ coordAt L a s' < L))
    (hcj : coordAt L j s' = t + 1) :
    (getAt BPair.unit (vecAdd W (stepV d L j t W))
      (plaqKey d L a k (s' - (L + 1) ^ z))).oneValue BPair.unit := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  obtain ⟨_, hd, hoff⟩ := stepBack (L + 1) z s' hL hzpos
  have hlt : s' - (L + 1) ^ z < (L + 1) ^ d := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hs'
  have hcz : coordAt L z (s' - (L + 1) ^ z) < L := by
    have h := baseDigit_lt (L + 1) z s' hL
    rw [← hd] at h
    exact Nat.lt_of_succ_lt_succ h
  have hcj' : coordAt L j (s' - (L + 1) ^ z) = t + 1 :=
    (hoff j (fun h => hzj h.symm)).trans hcj
  refine stepped_above d L j t W hW hsup a k _ hak hk hj hlt ?_ ?_ hcj'
  · rcases hz with ⟨hz, _⟩ | ⟨hz, hca⟩
    · rw [← hz]
      exact hcz
    · rw [show coordAt L a (s' - (L + 1) ^ z) = coordAt L a s' from
        hoff a (fun h => Nat.ne_of_lt hak (h.trans hz))]
      exact hca
  · rcases hz with ⟨hz, hck⟩ | ⟨hz, _⟩
    · rw [show coordAt L k (s' - (L + 1) ^ z) = coordAt L k s' from
        hoff k (fun h => Nat.ne_of_gt hak (h.trans hz))]
      exact hck
    · rw [← hz]
      exact hcz

/-- The stepped vector reads the sum's unit at a plaquette through the
descent's direction with its corner at the level: the top link, the
lower direction's link at the corner stepped along the descent's
direction, pairs the stepped vector at the sum's unit, and every
further plaquette on the link sits one beyond the level, so the
link's read holds the plaquette's balance partner alone. -/
private theorem stepped_face_read (d L j t : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hker' : poly.unitTail (matVec (transposeM (incid d L)) (vecAdd W (stepV d L j t W))))
    (hsup : ∀ p, p < plaqCount d L →
      levelB d L j (t + 1) (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit)
    (e s : Nat) (hej : e < j) (hj : j < d) (hs : s < (L + 1) ^ d)
    (hce : coordAt L e s < L) (hcj : coordAt L j s = t) (htL : t < L) :
    (getAt BPair.unit (vecAdd W (stepV d L j t W)) (plaqKey d L e j s)).oneValue BPair.unit := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  have hW'l : (vecAdd W (stepV d L j t W)).length = plaqCount d L :=
    length_vecAdd _ _ _ hW (stepV_len d L j t W)
  have hed : e < d := Nat.lt_trans hej hj
  have hej' : ¬ e = j := Nat.ne_of_lt hej
  have hcj' : coordAt L j s < L := by rw [hcj]; exact htL
  have hs' : stepAt L j s < (L + 1) ^ d := stepAt_lt d L j s hj hs hcj'
  have hce' : coordAt L e (stepAt L j s) < L := by
    rw [coordAt_step_ne L j e s hcj' hej']
    exact hce
  have hcj'' : coordAt L j (stepAt L j s) = t + 1 := by
    rw [coordAt_step L j s hcj', hcj]
  have hpos : 0 < coordAt L j (stepAt L j s) := by rw [hcj'']; exact Nat.succ_pos t
  have hback : stepAt L j s - (L + 1) ^ j = s := by
    obtain ⟨h1, _, _⟩ := stepBack (L + 1) j (stepAt L j s) hL hpos
    exact addCancelR ((L + 1) ^ j) h1
  -- the top link's kernel read at the stepped vector, expanded at the planes
  have hk := poly.getAt_unitTail hker' (linkKey d L e (stepAt L j s))
  rw [vec_as_map d L _ hW'l] at hk
  have hsum := BPair.oneValue_trans (BPair.oneValue_symm (colRead_planes d L e (stepAt L j s)
    hed hs' hce' (fun q => getAt BPair.unit (vecAdd W (stepV d L j t W))
      (plaqKey d L q.1 q.2.1 q.2.2)))) hk
  -- the planes through the link at a higher direction: the descent's direction holds
  -- the plaquette's balance partner, every further plane the unit
  have hK : (bsum (fun k => if decide (e < k) then
      (if decide (coordAt L k (stepAt L j s) < L)
        then getAt BPair.unit (vecAdd W (stepV d L j t W)) (plaqKey d L e k (stepAt L j s))
        else BPair.unit)
      + (if 0 < coordAt L k (stepAt L j s)
        then (getAt BPair.unit (vecAdd W (stepV d L j t W))
          (plaqKey d L e k (stepAt L j s - (L + 1) ^ k))).swap
        else BPair.unit) else BPair.unit) (List.range d)).oneValue
      (getAt BPair.unit (vecAdd W (stepV d L j t W)) (plaqKey d L e j s)).swap := by
    refine BPair.oneValue_trans (bsum_range_pick _ j d hj (fun k hkd hkj => ?_)) ?_
    · refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hek => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      have hek' : e < k := of_decide_eq_true hek
      refine BPair.add_units (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _
        (fun hck => stepped_above d L j t W hW hsup e k _ hek' hkd hj hs' hce'
          (of_decide_eq_true hck) hcj'')) (BPair.oneValue_of_eq (ite_prop_unit _)))
        (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hkpos => ?_))
          (BPair.oneValue_of_eq (ite_prop_unit _)))
      show (getAt BPair.unit (vecAdd W (stepV d L j t W))
        (plaqKey d L e k (stepAt L j s - (L + 1) ^ k))).swap.oneValue BPair.unit.swap
      exact swap_congr (stepped_back d L j t W hW hsup e k k _ hek' hkd hj hs' hkj hkpos
        (Or.inr ⟨rfl, hce'⟩) hcj'')
    rw [if_pos (decide_eq_true hej), if_pos hpos, hback]
    refine BPair.oneValue_trans (BPair.add_congr (ite_congr_prop (A' := BPair.unit) _
      (fun hlt => stepped_above d L j t W hW hsup e j _ hej hj hj hs' hce'
        (of_decide_eq_true hlt) hcj'')) (BPair.oneValue_refl _)) ?_
    rw [ite_prop_unit]
    exact BPair.unit_add _
  -- the planes through the link at a lower direction read the unit
  have hA : (bsum (fun a => if decide (a < e) then
      (if 0 < coordAt L a (stepAt L j s)
        then getAt BPair.unit (vecAdd W (stepV d L j t W))
          (plaqKey d L a e (stepAt L j s - (L + 1) ^ a))
        else BPair.unit)
      + (if decide (coordAt L a (stepAt L j s) < L)
        then (getAt BPair.unit (vecAdd W (stepV d L j t W)) (plaqKey d L a e (stepAt L j s))).swap
        else BPair.unit) else BPair.unit) (List.range d)).oneValue BPair.unit := by
    refine foldB_nullRange _ d (fun a _ => ?_)
    refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hae => ?_))
      (BPair.oneValue_of_eq (ite_prop_unit _))
    have hae' : a < e := of_decide_eq_true hae
    have haj : ¬ a = j := Nat.ne_of_lt (Nat.lt_trans hae' hej)
    refine BPair.add_units (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _
      (fun hapos => stepped_back d L j t W hW hsup a e a _ hae' hed hj hs' haj hapos
        (Or.inl ⟨rfl, hce'⟩) hcj'')) (BPair.oneValue_of_eq (ite_prop_unit _)))
      (BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun hca => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _)))
    show (getAt BPair.unit (vecAdd W (stepV d L j t W))
      (plaqKey d L a e (stepAt L j s))).swap.oneValue BPair.unit.swap
    exact swap_congr (stepped_above d L j t W hW hsup a e _ hae' hed hj hs'
      (of_decide_eq_true hca) hce' hcj'')
  -- the link's read is the plaquette's balance partner, at the sum's unit
  have hX : (getAt BPair.unit (vecAdd W (stepV d L j t W)) (plaqKey d L e j s)).swap.oneValue
      BPair.unit :=
    BPair.oneValue_trans (BPair.oneValue_symm hK)
      (BPair.oneValue_trans (BPair.oneValue_symm (BPair.add_unit _))
        (BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _) (BPair.oneValue_symm hA))
          hsum))
  exact swap_congr hX

/-- The descent's step: a kernel vector supported at the level above
moves by the cubes' boundaries' combination to a kernel vector
supported at the level, the top faces withdrawn at their cubes'
boundaries and the faces through the direction at the level read
off by the top links' kernel reads at the stepped vector. -/
private theorem descent_step (d L j t : Nat) (hj : j < d) (W : List BPair)
    (hW : W.length = plaqCount d L)
    (hker : poly.unitTail (matVec (transposeM (incid d L)) W))
    (hsup : ∀ p, p < plaqCount d L →
      levelB d L j (t + 1) (getAt (0, 0, 0) (plaqList d L) p) = false →
      (getAt BPair.unit W p).oneValue BPair.unit) :
    ∃ W' : List BPair, W'.length = plaqCount d L
      ∧ poly.unitTail (matVec (transposeM (incid d L)) W')
      ∧ (∀ p, p < plaqCount d L →
          levelB d L j t (getAt (0, 0, 0) (plaqList d L) p) = false →
          (getAt BPair.unit W' p).oneValue BPair.unit)
      ∧ (spanRel (plaqCount d L) (transposeM (cubeBd d L)) W'
          → spanRel (plaqCount d L) (transposeM (cubeBd d L)) W) := by
  have hVl := stepV_len d L j t W
  have hN := cubeBdT_rows d L
  have hker' : poly.unitTail (matVec (transposeM (incid d L)) (vecAdd W (stepV d L j t W))) :=
    poly.oneValue_unitTail (matVec_vecAdd_free _ _ _ (hW.trans hVl.symm))
      (unitTail_vecAdd_of hker (stepV_ker d L j t W))
  refine ⟨vecAdd W (stepV d L j t W), length_vecAdd _ _ _ hW hVl, hker', ?_, ?_⟩
  · intro p hp hoff
    have hq := plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)
    have hpk := plaqKey_of_getAt d L p hp
    generalize hqe : getAt (0, 0, 0) (plaqList d L) p = q at hq hpk hoff
    obtain ⟨hak, hkd, hs, hca, hck⟩ := hq
    cases q with
    | mk a q' =>
    cases q' with
    | mk k s =>
    have hpk' : plaqKey d L a k s = p := hpk
    rw [← hpk']
    cases hl : levelB d L j (t + 1) (a, k, s) with
    | false =>
      rw [getAt_vecAdd _ _ _ (by rw [hW, hpk']; exact hp) (by rw [hVl, hpk']; exact hp)]
      have hWp : (getAt BPair.unit W (plaqKey d L a k s)).oneValue BPair.unit := by
        rw [hpk']
        exact hsup p hp (by rw [hqe]; exact hl)
      exact BPair.add_units hWp (stepV_off d L j t W hsup a k s hak hkd hs hca hck
        (levelB_false_cases d L j (t + 1) (a, k, s) hl))
    | true =>
      obtain ⟨hab, hkj, hlev⟩ := (levelB_read d L j (t + 1) (a, k, s)).1 hl
      rcases levelB_false_cases d L j t (a, k, s) hoff with ⟨i, hji, hid, hne⟩ | hjk | hhigh
      · exact absurd (hab i hji hid) hne
      · exact absurd hjk (Nat.not_lt_of_ge hkj)
      · by_cases hkj' : k = j
        · rw [eqBeqOf hkj'] at hlev hhigh
          have hcj : coordAt L j s = t := by
            have h1 : coordAt L j s + 1 ≤ t + 1 := hlev
            have h2 : t < coordAt L j s + 1 := hhigh
            exact Nat.le_antisymm (Nat.le_of_succ_le_succ h1) (Nat.le_of_lt_succ h2)
          have htL : t < L := by rw [← hcj, ← hkj']; exact hck
          subst hkj'
          exact stepped_face_read d L k t W hW hker' hsup a s hak hkd hs hca hcj htL
        · rw [neBeqOf hkj'] at hlev hhigh
          have hkj'' : k < j := Nat.lt_of_le_of_ne hkj hkj'
          have hcj : coordAt L j s = t + 1 := by
            have h1 : coordAt L j s + 0 ≤ t + 1 := hlev
            have h2 : t < coordAt L j s + 0 := hhigh
            rw [Nat.add_zero] at h1 h2
            exact Nat.le_antisymm h1 h2
          exact stepped_above d L j t W hW hsup a k s hak hkd hj hs hca hck hcj
  · intro hsp
    have hV := stepV_span d L j t W
    have hswap : spanRel (plaqCount d L) (transposeM (cubeBd d L)) ((stepV d L j t W).map BPair.swap) :=
      spanRel_congr _ _ _ _ (poly.oneValue_symm (swapMap_scale _))
        (spanRel_scale _ _ _ _ hN hVl hV) (by rw [ground.length_map]; exact hVl)
    refine spanRel_congr _ _ _ _ ?_ (spanRel_add _ _ _ _ hN (length_vecAdd _ _ _ hW hVl)
      (by rw [ground.length_map]; exact hVl) hsp hswap) hW
    rw [vecAdd_assoc]
    exact vecAdd_null_right _ _ (by
      rw [length_vecAdd _ _ (plaqCount d L) hVl (by rw [ground.length_map]; exact hVl), hW])
      (vecAdd_swap_unitTail _)

/-- The level at the first position along a direction sits within
the level at the side along the direction below, at a valid
plaquette. -/
private theorem levelB_down (d L j : Nat) (q : Nat × Nat × Nat) (hq : q ∈ plaqList d L)
    (h : levelB d L (j + 1) 0 q = true) : levelB d L j L q = true := by
  obtain ⟨hab, hkj, hlev⟩ := (levelB_read d L (j + 1) 0 q).1 h
  obtain ⟨hak, hkd, _, _, hck⟩ := plaq_of_mem d L q hq
  have hkj' : ¬ q.2.1 = j + 1 := fun he => by
    rw [eqBeqOf he] at hlev
    exact absurd (show coordAt L (j + 1) q.2.2 + 1 ≤ 0 from hlev) (Nat.not_le_of_gt (Nat.succ_pos _))
  rw [neBeqOf hkj'] at hlev
  have hlev' : coordAt L (j + 1) q.2.2 + 0 ≤ 0 := hlev
  rw [Nat.add_zero] at hlev'
  have hz : coordAt L (j + 1) q.2.2 = 0 := Nat.le_antisymm hlev' (Nat.zero_le _)
  refine (levelB_read d L j L q).2 ⟨fun i hji hid => ?_, Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hkj hkj'), ?_⟩
  · rcases Nat.lt_or_ge (j + 1) i with hi | hi
    · exact hab i hi hid
    · rw [Nat.le_antisymm hi hji]
      exact hz
  · by_cases hkj'' : q.2.1 = j
    · rw [eqBeqOf hkj'']
      rw [hkj''] at hck
      show coordAt L j q.2.2 + 1 ≤ L
      exact hck
    · rw [neBeqOf hkj'']
      show coordAt L j q.2.2 + 0 ≤ L
      rw [Nat.add_zero]
      exact Nat.le_of_lt_succ (baseDigit_lt (L + 1) j q.2.2 (Nat.succ_pos L))

/-- The descent: a kernel vector supported at a direction and a level
sits in the cubes' boundaries' span, the level descending to the
first position and the direction to the first, where the window
holds no plaquette. -/
private theorem descent_all (d L : Nat) :
    ∀ j, j < d → ∀ t (W : List BPair), W.length = plaqCount d L →
      poly.unitTail (matVec (transposeM (incid d L)) W) →
      (∀ p, p < plaqCount d L →
        levelB d L j t (getAt (0, 0, 0) (plaqList d L) p) = false →
        (getAt BPair.unit W p).oneValue BPair.unit) →
      spanRel (plaqCount d L) (transposeM (cubeBd d L)) W := by
  intro j
  induction j with
  | zero =>
    intro _ t W hW _ hsup
    refine spanRel_null _ _ _ (unitTail_of_getAt W (fun p hp => ?_)) (cubeBdT_rows d L) hW
    rw [hW] at hp
    refine hsup p hp (levelB_off_plane d L 0 t _ ?_)
    exact Nat.lt_of_le_of_lt (Nat.zero_le _)
      (plaq_of_mem d L _ (mem_getAt (0, 0, 0) (plaqList d L) p hp)).1
  | succ j ih =>
    intro hj t
    induction t with
    | zero =>
      intro W hW hker hsup
      refine ih (Nat.lt_of_succ_lt hj) L W hW hker (fun p hp hoff => hsup p hp ?_)
      cases hl : levelB d L (j + 1) 0 (getAt (0, 0, 0) (plaqList d L) p) with
      | true =>
        rw [levelB_down d L j _ (mem_getAt (0, 0, 0) (plaqList d L) p hp) hl] at hoff
        exact Bool.noConfusion hoff
      | false => rfl
    | succ t iht =>
      intro W hW hker hsup
      obtain ⟨W', hW', hker', hsup', himp⟩ := descent_step d L (j + 1) t hj W hW hker hsup
      exact himp (iht W' hW' hker' hsup')

/-- A plaquette combination pairing every link at the sum's unit is a
combination of the cubes' boundaries, by the descent in the last
direction: at two directions or beyond every kernel member sits in
the cubes' boundaries' span. -/
theorem kernel_bd_span (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hker : poly.unitTail (matVec (transposeM (incid d L)) W)) :
    spanRel (plaqCount d L) (transposeM (cubeBd d L)) W := by
  rcases Nat.eq_zero_or_pos (plaqCount d L) with hn | hn
  · have hW0 : W = [] := List.eq_nil_of_length_eq_zero (hW.trans hn)
    rw [hW0] at hW ⊢
    exact spanRel_null _ _ _ trivial (cubeBdT_rows d L) hW
  · cases d with
    | zero =>
      have h0 : plaqCount 0 L = 0 := rfl
      rw [h0] at hn
      exact absurd hn (Nat.lt_irrefl 0)
    | succ d' =>
      refine descent_all (d' + 1) L d' (Nat.lt_succ_self d') L W hW hker (fun p hp hoff => ?_)
      have hq := plaq_of_mem (d' + 1) L _ (mem_getAt (0, 0, 0) (plaqList (d' + 1) L) p hp)
      generalize hqe : getAt (0, 0, 0) (plaqList (d' + 1) L) p = q at hq hoff
      obtain ⟨hak, hkd, _, _, hck⟩ := hq
      have htrue : levelB (d' + 1) L d' L q = true := by
        refine (levelB_read (d' + 1) L d' L _).2 ⟨fun i hji hid => ?_, Nat.le_of_lt_succ hkd, ?_⟩
        · exact absurd (Nat.lt_of_lt_of_le hji (Nat.le_of_lt_succ hid)) (Nat.lt_irrefl d')
        · by_cases hkj : q.2.1 = d'
          · rw [eqBeqOf hkj]
            rw [hkj] at hck
            show coordAt L d' q.2.2 + 1 ≤ L
            exact hck
          · rw [neBeqOf hkj]
            show coordAt L d' q.2.2 + 0 ≤ L
            rw [Nat.add_zero]
            exact Nat.le_of_lt_succ (baseDigit_lt (L + 1) d' _ (Nat.succ_pos L))
      rw [htrue] at hoff
      exact Bool.noConfusion hoff

/-- Every kernel member sits in the kernel list's span: the list is
the cubes' boundaries' collection, spanning every boundary. -/
theorem kerList_span (d L : Nat) (W : List BPair) (hW : W.length = plaqCount d L)
    (hker : poly.unitTail (matVec (transposeM (incid d L)) W)) :
    spanRel (plaqCount d L) (kerList d L) W := by
  have hN := cubeBdT_rows d L
  show spanRel _ (collectW _ (transposeM (cubeBd d L))) W
  rw [collectW_eq _ _ hN]
  exact spanRel_trans _ _ _ W hN (collect_rowsLen _ _ hN) (collect_span_row _ _ hN)
    (kernel_bd_span d L W hW hker)

/-- The kernel list's count is the kernel dimension: the list and the
descent's kernel list are two independent lists inside one span. -/
theorem kerList_length (d L : Nat) : (kerList d L).length = kerDim d L := by
  have hKT : rowsLen (plaqCount d L) (transposeM (incid d L)) :=
    rowsLen_cast (incid_length d L) (rowsLen_transposeM _)
  show (kerList d L).length = kernelDim (plaqCount d L) (transposeM (incid d L))
  rw [← kernelList_dim]
  refine span_count_eq _ _ _ (kerList_rows d L) (kernelList_rowsLen _ _) (kerList_indep d L)
    (kernelList_indep _ _ hKT) (fun k hk => ?_) (fun k hk => ?_)
  · exact kernelList_span _ _ hKT _ (rowsLen_getAt _ k (kerList_rows d L) hk) (kerList_ker d L k hk)
  · exact kerList_span d L _ (rowsLen_getAt _ k (kernelList_rowsLen _ _) hk)
      (kernelList_members _ _ hKT k hk)

/-- The kernel list's transpose's row at a plaquette's place reads the
list's count as its width, the vacant list's rows vacant. -/
private theorem kerListT_row_len (d L i : Nat) (hi : i < plaqCount d L) :
    (getAt [] (transposeM (kerList d L)) i).length = (kerList d L).length := by
  cases hK : kerList d L with
  | nil => rfl
  | cons r t =>
    have hK0 : rowsLen (plaqCount d L) (r :: t) := by rw [← hK]; exact kerList_rows d L
    have hl : (transposeM (r :: t)).length = plaqCount d L :=
      length_transposeM _ hK0 (Nat.succ_pos _)
    exact rowsLen_getAt _ i (rowsLen_transposeM (r :: t)) (by rw [hl]; exact hi)

/-- The descent adjugate of the kernel list's Gram is symmetric, the
cofactor family of a symmetric square (`elim.cofVec_symm`). -/
private theorem adjMD_symm (d L : Nat) :
    matOneValue (transposeM (adjMD (gramM (kerList d L)))) (adjMD (gramM (kerList d L))) := by
  have hind := kerList_indep d L
  have hGl : (gramM (kerList d L)).length = (kerList d L).length := length_gramBy dotP _
  have hGsq : sqAt (gramM (kerList d L)) (kerList d L).length := by
    refine sqAt_of hGl ?_
    have h := gramM_sq (kerList d L)
    rw [hGl] at h
    exact h
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  cases hr : (kerList d L).length with
  | zero =>
    have hA : adjMD (gramM (kerList d L)) = [] := List.eq_nil_of_length_eq_zero (hAl.trans hr)
    rw [hA]
    exact trivial
  | succ r' =>
    have hpos : 0 < (kerList d L).length := by rw [hr]; exact Nat.succ_pos r'
    have hTl : (transposeM (adjMD (gramM (kerList d L)))).length = (kerList d L).length :=
      length_transposeM _ hAr (by rw [hAl]; exact hpos)
    refine matOne_of_entries _ _ (kerList d L).length hTl
      (rowsLen_cast hAl (rowsLen_transposeM _)) hAl hAr (fun i j hi hj => ?_)
    rw [getAt_transposeM BPair.unit _ hAr i j hi (by rw [hAl]; exact hj)]
    refine BPair.oneValue_trans (adjMD_cofVec _ _ hind j i hj hi) ?_
    refine BPair.oneValue_trans (cofVec_symm _ hGsq (fun a b ha hb =>
      gramM_symm _ a b ha hb) i j hi hj) ?_
    exact BPair.oneValue_symm (adjMD_cofVec _ _ hind i j hi hj)

/-- The projector's entry at two plaquettes' places. -/
private theorem proj_entry (d L i j : Nat) (hi : i < plaqCount d L) (hj : j < plaqCount d L) :
    getAt BPair.unit (getAt [] (proj d L) i) j
      = (if i == j then projDen d L else BPair.unit)
        + (dotP (getAt [] (transposeM (kerList d L)) i)
            (matVec (adjMD (gramM (kerList d L)))
              (getAt [] (transposeM (kerList d L)) j))).swap :=
  matOf_entry [] BPair.unit _ _ _ i j hi hj

/-- The projector's row count and rows read the plaquettes' count. -/
theorem proj_length (d L : Nat) : (proj d L).length = plaqCount d L := matOf_length _ _ _

theorem proj_rows (d L : Nat) : rowsLen (plaqCount d L) (proj d L) := rowsLen_matOf _ _ _

/-- The projector's symmetry at every window: the adjugate's
symmetry at the kernel list's Gram. -/
theorem projSymRead_all (d L : Nat) : projSymRead d L := by
  show matOneValue (proj d L) (transposeM (proj d L))
  have hPl := proj_length d L
  have hPr := proj_rows d L
  cases hn : plaqCount d L with
  | zero =>
    have hP : proj d L = [] := List.eq_nil_of_length_eq_zero (hPl.trans hn)
    rw [hP]
    exact trivial
  | succ n' =>
    have hpos : 0 < plaqCount d L := by rw [hn]; exact Nat.succ_pos n'
    have hTl : (transposeM (proj d L)).length = plaqCount d L :=
      length_transposeM _ hPr (by rw [hPl]; exact hpos)
    obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
    refine matOne_of_entries _ _ (plaqCount d L) hPl hPr hTl
      (rowsLen_cast hPl (rowsLen_transposeM _)) (fun i j hi hj => ?_)
    rw [getAt_transposeM BPair.unit _ hPr i j hi (by rw [hPl]; exact hj),
      proj_entry d L i j hi hj, proj_entry d L j i hj hi]
    refine BPair.add_congr ?_ (swap_congr ?_)
    · by_cases hij : i = j
      · rw [eqBeqOf hij, eqBeqOf hij.symm]
        exact BPair.oneValue_refl _
      · rw [neBeqOf hij, neBeqOf (fun h => hij h.symm)]
        exact BPair.oneValue_refl _
    · refine BPair.oneValue_trans (BPair.oneValue_of_eq (dotP_comm _ _)) ?_
      exact dotP_matVec_sym (adjMD (gramM (kerList d L))) (sqAt_of hAl hAr) (adjMD_symm d L)
        (getAt [] (transposeM (kerList d L)) j) (getAt [] (transposeM (kerList d L)) i)
        (kerListT_row_len d L j hj) (kerListT_row_len d L i hi)



/-- The descent adjugate against the Gram reads the clearing's
multiple of the identity, the adjugate identity at the kernel list's
Gram (`elim.adjM_col_diag`, `elim.adjM_col_off`). -/
private theorem adjGram_read (d L : Nat) (hr : 0 < (kerList d L).length) :
    matOneValue (matMul (adjMD (gramM (kerList d L))) (gramM (kerList d L)))
      (matScaleB (projDen d L) (idMat (kerList d L).length)) := by
  have hind := kerList_indep d L
  have hGl : (gramM (kerList d L)).length = (kerList d L).length := length_gramBy dotP _
  have hGr : rowsLen (kerList d L).length (gramM (kerList d L)) := by
    have h := gramM_sq (kerList d L)
    rw [hGl] at h
    exact h
  have hGsq : sqAt (gramM (kerList d L)) (kerList d L).length := sqAt_of hGl hGr
  have hGpos : 0 < (gramM (kerList d L)).length := by rw [hGl]; exact hr
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hadj : matOneValue (adjMD (gramM (kerList d L))) (adjM (gramM (kerList d L))) := by
    refine matOne_of_entries _ _ (kerList d L).length hAl hAr
      ((adjM_len _ hGpos).trans hGl) (rowsLen_cast hGl (adjM_rowsLen _)) (fun i j hi hj => ?_)
    rw [adjM_read _ i j (by rw [hGl]; exact hi) (by rw [hGl]; exact hj)]
    exact adjMD_cofVec _ _ hind i j hi hj
  have hMl : (matMul (adjMD (gramM (kerList d L))) (gramM (kerList d L))).length
      = (kerList d L).length := (length_matMul _ _).trans hAl
  refine matOne_trans (matMul_congrL _ _ _ hadj) ?_
  refine matOne_of_entries _ _ (kerList d L).length ((length_matMul _ _).trans ((adjM_len _ hGpos).trans hGl))
    (rowsLen_matMul_of _ _ (fun _ => hGpos) hGr)
    ((length_scaleB _ _).trans (length_idMat _)) (rowsLen_scaleB _ _ _ (rowsLen_idMat _))
    (fun i j hi hj => ?_)
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
    (entry_scaleId (projDen d L) (kerList d L).length i j hi hj))
  by_cases hij : i = j
  · rw [if_pos hij.symm, hij]
    refine BPair.oneValue_trans (adjM_col_diag _ hGsq j hj) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (detD_eq _ (gramM_sq _))) ?_
    exact BPair.oneValue_symm (BPair.mul_ofNat_one _)
  · rw [if_neg (show ¬ j = i from fun h => hij h.symm)]
    refine BPair.oneValue_trans (adjM_col_off _ hGsq i j hi hj hij) ?_
    exact BPair.oneValue_symm (BPair.mul_unit _)

/-- The kernel list against its transpose reads its Gram. -/
private theorem kerGram_read (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matOneValue (matMul (kerList d L) (transposeM (kerList d L))) (gramM (kerList d L)) := by
  have hK0 := kerList_rows d L
  have hGl : (gramM (kerList d L)).length = (kerList d L).length := length_gramBy dotP _
  have hGr : rowsLen (kerList d L).length (gramM (kerList d L)) := by
    have h := gramM_sq (kerList d L)
    rw [hGl] at h
    exact h
  have hTT : transposeM (transposeM (kerList d L)) = kerList d L :=
    transposeM_transposeM _ hK0 hn hr
  have hMr : rowsLen (kerList d L).length (matMul (kerList d L) (transposeM (kerList d L))) := by
    have h := rowsLen_matMul (kerList d L) (transposeM (kerList d L))
    rw [hTT] at h
    exact h
  refine matOne_of_entries _ _ (kerList d L).length (length_matMul _ _) hMr hGl hGr
    (fun i j hi hj => ?_)
  rw [entry_matMul _ _ i j hi (by rw [hTT]; exact hj), hTT, gramM_entry _ i j hi hj]
  exact dotN_read _ _

/-- The Gram against the kernel list's transpose reads the vacant
family: each member pairs every link at the sum's unit. -/
private theorem gramKer_null (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matNull (matMul (gram d L) (transposeM (kerList d L))) := by
  have hK0 := kerList_rows d L
  have hKl := incid_length d L
  have hK := incid_rows d L
  have hKpos : 0 < (incid d L).length := by rw [hKl]; exact hn
  have hKTl : (transposeM (incid d L)).length = linkCount d L := length_transposeM _ hK hKpos
  have hKTr : rowsLen (plaqCount d L) (transposeM (incid d L)) :=
    rowsLen_cast hKl (rowsLen_transposeM _)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hN0r : rowsLen (kerList d L).length (transposeM (kerList d L)) := rowsLen_transposeM _
  have hTT : transposeM (transposeM (kerList d L)) = kerList d L :=
    transposeM_transposeM _ hK0 hn hr
  have hlpos : 0 < linkCount d L := by
    have h := rowSq_read d L 0 hn
    cases hl : linkCount d L with
    | zero =>
      have hrow : (getAt [] (incid d L) 0).length = 0 := by
        rw [rowsLen_getAt _ 0 hK (by rw [hKl]; exact hn), hl]
      have hnil : getAt [] (incid d L) 0 = [] := List.eq_nil_of_length_eq_zero hrow
      rw [hnil] at h
      exact absurd h (by decide +kernel)
    | succ _ => exact Nat.succ_pos _
  -- the transposed incidence against the kernel list's transpose is vacant
  have hnull : matNull (matMul (transposeM (incid d L)) (transposeM (kerList d L))) := by
    refine matNull_of_getAt _ (fun l hl => ?_)
    rw [length_matMul, hKTl] at hl
    have hrow : (getAt [] (matMul (transposeM (incid d L)) (transposeM (kerList d L))) l).length
        = (kerList d L).length := by
      have h := rowsLen_matMul (transposeM (incid d L)) (transposeM (kerList d L))
      rw [hTT] at h
      exact rowsLen_getAt _ l h (by rw [length_matMul, hKTl]; exact hl)
    refine poly.unitTail_of_getAt (fun m => ?_)
    by_cases hm : m < (kerList d L).length
    · rw [entry_matMul _ _ l m (by rw [hKTl]; exact hl) (by rw [hTT]; exact hm), hTT,
        ← getAt_matVec _ _ l (by rw [hKTl]; exact hl)]
      exact poly.getAt_unitTail (kerList_ker d L m hm) l
    · rw [getAt_over BPair.unit _ m (by rw [hrow]; exact Nat.le_of_not_lt hm)]
      exact BPair.oneValue_refl _
  show matNull (matMul (matMul (incid d L) (transposeM (incid d L))) (transposeM (kerList d L)))
  refine matNull_congr (matMul_assoc _ _ _ hK hKTr hN0r hKTl hN0l hlpos hn) ?_
  exact matNull_matMul _ (matNull_transposeM _ hnull) _



/-- The projector's bridge at an occupied kernel list and window:
the projector's cleared read is the clearing's identity less the
list's transpose against the adjugate against the list, entry by
entry, `D Π ≡ D 1 - N₀ (adj G) N₀ᵀ`. -/
private theorem proj_bridge (d L : Nat) (hr : 0 < (kerList d L).length) :
    matOneValue (proj d L)
      (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
        (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) := by
  have hK0 := kerList_rows d L
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length = (kerList d L).length :=
    (length_matMul _ _).trans hAl
  have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
    rowsLen_cast hN0l (rowsLen_matMul _ _)
  have hAKTl : (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length
      = plaqCount d L := length_transposeM _ hAKr (by rw [hAKl]; exact hr)
  have hMl : (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length = plaqCount d L :=
    (length_matMul _ _).trans hN0l
  have hMr : rowsLen (plaqCount d L) (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))) :=
    rowsLen_cast hAKTl (rowsLen_matMul _ _)
  have hSl : (matScaleB (projDen d L) (idMat (plaqCount d L))).length = plaqCount d L :=
    (length_scaleB _ _).trans (length_idMat _)
  have hSr : rowsLen (plaqCount d L) (matScaleB (projDen d L) (idMat (plaqCount d L))) :=
    rowsLen_scaleB _ _ _ (rowsLen_idMat _)
  have hsMr : rowsLen (plaqCount d L) (matSwap (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) := rowsLen_matSwap _ _ hMr
  have hsMl : (matSwap (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = plaqCount d L :=
    (length_matSwap _).trans hMl
  have hRl : (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
      (matSwap (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L))))).length = plaqCount d L := by
    rw [length_matAdd _ _ (hSl.trans hsMl.symm), hSl]
  have hRr : rowsLen (plaqCount d L) (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
      (matSwap (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) :=
    rowsLen_matAdd _ _ _ hSr hsMr
  refine matOne_of_entries (proj d L) _ (plaqCount d L) (proj_length d L) (proj_rows d L)
    hRl hRr (fun i j hi hj => ?_)
  have e1 := proj_entry d L i j hi hj
  have e2 := entry_matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
    (matSwap (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) (plaqCount d L) hSr hsMr i j
    (by rw [hSl]; exact hi) (by rw [hsMl]; exact hi) hj
  have e3 := entry_matSwap (matMul (transposeM (kerList d L))
    (matMul (adjMD (gramM (kerList d L))) (kerList d L))) (plaqCount d L) hMr i j
    (by rw [hMl]; exact hi) hj
  have e4 := entry_matMul (transposeM (kerList d L))
    (matMul (adjMD (gramM (kerList d L))) (kerList d L)) i j (by rw [hN0l]; exact hi)
    (by rw [hAKTl]; exact hj)
  refine BPair.oneValue_trans (BPair.oneValue_of_eq e1) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_of_eq e2.symm)
  refine BPair.add_congr ?_ ?_
  · refine BPair.oneValue_trans (delta_scale (projDen d L) i j) ?_
    exact BPair.oneValue_symm (entry_scaleId (projDen d L) (plaqCount d L) i j hi hj)
  · refine BPair.oneValue_trans ?_ (BPair.oneValue_of_eq e3.symm)
    refine swap_congr ?_
    refine BPair.oneValue_trans ?_ (BPair.oneValue_of_eq e4.symm)
    refine BPair.oneValue_trans (BPair.oneValue_symm (dotN_read _ _)) (dotN_congrR _ _ _ ?_)
    have hrowT : (getAt [] (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))) j).length
        = (kerList d L).length :=
      (rowsLen_getAt _ j (rowsLen_transposeM _) (by rw [hAKTl]; exact hj)).trans hAKl
    have hrowV : (matVec (adjMD (gramM (kerList d L))) (getAt [] (transposeM (kerList d L)) j)).length
        = (kerList d L).length := (matVec_length _ _).trans hAl
    refine poly.ov_of_getAt (fun a => ?_)
    by_cases ha : a < (kerList d L).length
    · have f1 := getAt_transposeM BPair.unit (matMul (adjMD (gramM (kerList d L))) (kerList d L))
        hAKr j a hj (by rw [hAKl]; exact ha)
      have f2 := entry_matMul (adjMD (gramM (kerList d L))) (kerList d L) a j
        (by rw [hAl]; exact ha) (by rw [hN0l]; exact hj)
      have f3 := getAt_matVec (adjMD (gramM (kerList d L))) (getAt [] (transposeM (kerList d L)) j)
        a (by rw [hAl]; exact ha)
      exact BPair.oneValue_of_eq (f3.trans (f2.symm.trans f1.symm))
    · have g1 := getAt_over BPair.unit
        (matVec (adjMD (gramM (kerList d L))) (getAt [] (transposeM (kerList d L)) j)) a
        (by rw [hrowV]; exact Nat.le_of_not_lt ha)
      have g2 := getAt_over BPair.unit
        (getAt [] (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))) j) a
        (by rw [hrowT]; exact Nat.le_of_not_lt ha)
      exact BPair.oneValue_of_eq (g1.trans g2.symm)

/-- The adjugate against the list, against the list's transpose:
the clearing's multiple of the identity, `(adj G) K₀ N₀ ≡ D 1` at
the Gram's read and the adjugate identity. -/
private theorem akn_read (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matOneValue (matMul (matMul (adjMD (gramM (kerList d L))) (kerList d L))
        (transposeM (kerList d L)))
      (matScaleB (projDen d L) (idMat (kerList d L).length)) := by
  have hK0 := kerList_rows d L
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hN0r : rowsLen (kerList d L).length (transposeM (kerList d L)) := rowsLen_transposeM _
  have hTT : transposeM (transposeM (kerList d L)) = kerList d L :=
    transposeM_transposeM _ hK0 hn hr
  have hGl : (gramM (kerList d L)).length = (kerList d L).length := length_gramBy dotP _
  have hGr : rowsLen (kerList d L).length (gramM (kerList d L)) := by
    have h := gramM_sq (kerList d L)
    rw [hGl] at h
    exact h
  have hKNl : (matMul (kerList d L) (transposeM (kerList d L))).length = (kerList d L).length :=
    length_matMul _ _
  have hKNr : rowsLen (kerList d L).length (matMul (kerList d L) (transposeM (kerList d L))) := by
    have h := rowsLen_matMul (kerList d L) (transposeM (kerList d L))
    rw [hTT] at h
    exact h
  refine matOne_trans (matMul_assoc (adjMD (gramM (kerList d L))) (kerList d L)
    (transposeM (kerList d L)) hAr hK0 hN0r rfl hN0l hr hn) ?_
  refine matOne_trans (matMul_congrR (adjMD (gramM (kerList d L))) _ _ hKNr hGr hKNl hGl
    (kerGram_read d L hr hn)) ?_
  exact adjGram_read d L hr

/-- The kernel list's transpose against the adjugate against the
list, against the transpose: the clearing's multiple of the
transpose, `N₀ (adj G) N₀ᵀ N₀ ≡ D N₀` at the adjugate identity. -/
private theorem proj_core (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matOneValue (matMul (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L))) (transposeM (kerList d L)))
      (matScaleB (projDen d L) (transposeM (kerList d L))) := by
  have hK0 := kerList_rows d L
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hN0r : rowsLen (kerList d L).length (transposeM (kerList d L)) := rowsLen_transposeM _
  have hTT : transposeM (transposeM (kerList d L)) = kerList d L :=
    transposeM_transposeM _ hK0 hn hr
  have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length = (kerList d L).length :=
    (length_matMul _ _).trans hAl
  have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
    rowsLen_cast hN0l (rowsLen_matMul _ _)
  have hAKNl : (matMul (matMul (adjMD (gramM (kerList d L))) (kerList d L))
      (transposeM (kerList d L))).length = (kerList d L).length :=
    (length_matMul _ _).trans hAKl
  have hAKNr : rowsLen (kerList d L).length (matMul (matMul (adjMD (gramM (kerList d L)))
      (kerList d L)) (transposeM (kerList d L))) := by
    have h := rowsLen_matMul (matMul (adjMD (gramM (kerList d L))) (kerList d L))
      (transposeM (kerList d L))
    rw [hTT] at h
    exact h
  have hSl : (matScaleB (projDen d L) (idMat (kerList d L).length)).length = (kerList d L).length :=
    (length_scaleB _ _).trans (length_idMat _)
  have hSr : rowsLen (kerList d L).length (matScaleB (projDen d L) (idMat (kerList d L).length)) :=
    rowsLen_scaleB _ _ _ (rowsLen_idMat _)
  refine matOne_trans (matMul_assoc (transposeM (kerList d L))
    (matMul (adjMD (gramM (kerList d L))) (kerList d L)) (transposeM (kerList d L))
    hN0r hAKr hN0r hAKl hN0l hr hn) ?_
  refine matOne_trans (matMul_congrR (transposeM (kerList d L)) _ _ hAKNr hSr hAKNl hSl
    (akn_read d L hr hn)) ?_
  refine matOne_trans (matMul_scaleR _ _ _ _ (rowsLen_idMat _)) ?_
  exact matOne_scaleB _ (matMul_idR _ _ hN0r hN0l hr hn)

/-- The projector against the kernel list reads the sum's unit at
every window: at an occupied kernel list the clearing's multiple of
the list's transpose against its own balance partner, and at the
vacant list the product's rows vacant. -/
theorem projKerRead_all (d L : Nat) : projKerRead d L := by
  show matNull (matMul (proj d L) (transposeM (kerList d L)))
  cases hK : kerList d L with
  | nil => exact matNull_matMul [] trivial _
  | cons k0 kt =>
    have hr : 0 < (kerList d L).length := by rw [hK]; exact Nat.succ_pos _
    rw [← hK]
    cases hn : plaqCount d L with
    | zero =>
      have hP : proj d L = [] := List.eq_nil_of_length_eq_zero ((proj_length d L).trans hn)
      rw [hP]
      exact trivial
    | succ n' =>
      have hn' : 0 < plaqCount d L := by rw [hn]; exact Nat.succ_pos n'
      have hK0 := kerList_rows d L
      obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
      have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
      have hN0r : rowsLen (kerList d L).length (transposeM (kerList d L)) := rowsLen_transposeM _
      have hTT : transposeM (transposeM (kerList d L)) = kerList d L :=
        transposeM_transposeM _ hK0 hn' hr
      have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length
          = (kerList d L).length := (length_matMul _ _).trans hAl
      have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
        rowsLen_cast hN0l (rowsLen_matMul _ _)
      have hAKTl : (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length
          = plaqCount d L := length_transposeM _ hAKr (by rw [hAKl]; exact hr)
      have hMr : rowsLen (plaqCount d L) (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))) :=
        rowsLen_cast hAKTl (rowsLen_matMul _ _)
      have hSr : rowsLen (plaqCount d L) (matScaleB (projDen d L) (idMat (plaqCount d L))) :=
        rowsLen_scaleB _ _ _ (rowsLen_idMat _)
      have hSNr : rowsLen (kerList d L).length
          (matMul (matScaleB (projDen d L) (idMat (plaqCount d L))) (transposeM (kerList d L))) := by
        have h := rowsLen_matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (transposeM (kerList d L))
        rw [hTT] at h
        exact h
      have hMNr : rowsLen (kerList d L).length (matMul (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))) (transposeM (kerList d L))) := by
        have h := rowsLen_matMul (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))) (transposeM (kerList d L))
        rw [hTT] at h
        exact h
      refine matNull_congr (matMul_congrL _ _ (transposeM (kerList d L)) (proj_bridge d L hr)) ?_
      refine matNull_congr (matMul_addL (plaqCount d L) (transposeM (kerList d L))
        (by rw [hTT]; exact hK0) _ _ hSr (rowsLen_matSwap _ _ hMr)) ?_
      rw [matMul_swapL]
      refine matNull_congr (matAdd_cong2 (kerList d L).length _ _
        (matScaleB (projDen d L) (transposeM (kerList d L)))
        (matSwap (matScaleB (projDen d L) (transposeM (kerList d L))))
        hSNr (rowsLen_matSwap _ _ hMNr)
        (rowsLen_scaleB _ _ _ hN0r) (rowsLen_matSwap _ _ (rowsLen_scaleB _ _ _ hN0r)) ?_
        (matSwap_congr (proj_core d L hr hn'))) (matNull_add_swap _)
      refine matOne_trans (matMul_scaleL _ _ _) ?_
      exact matOne_scaleB _ (idMat_matMul _ _ hN0r hN0l hn')

/-- The projector at a vacant kernel list is the clearing's identity,
the identity at two directions. -/
private theorem proj_vacant (d L : Nat) (hK : kerList d L = []) :
    matOneValue (proj d L) (matScaleB (projDen d L) (idMat (plaqCount d L))) := by
  refine matOne_of_entries _ _ (plaqCount d L) (proj_length d L) (proj_rows d L)
    ((length_scaleB _ _).trans (length_idMat _)) (rowsLen_scaleB _ _ _ (rowsLen_idMat _))
    (fun i j hi hj => ?_)
  have e1 := proj_entry d L i j hi hj
  rw [hK] at e1
  refine BPair.oneValue_trans (BPair.oneValue_of_eq e1) ?_
  refine BPair.oneValue_trans ?_ (BPair.oneValue_symm
    (entry_scaleId (projDen d L) (plaqCount d L) i j hi hj))
  refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
    (show ((dotP (getAt [] (transposeM ([] : Mat)) i)
      (matVec (adjMD (gramM ([] : Mat))) (getAt [] (transposeM ([] : Mat)) j))).swap).oneValue
      BPair.unit from BPair.oneValue_refl _)) ?_
  exact BPair.oneValue_trans (BPair.add_unit _) (delta_scale (projDen d L) i j)

/-- The Gram against the projector at the clearing reads the
clearing's multiple of the Gram at every window: at an occupied
kernel list the Gram against the list's transpose is vacant, and at
the vacant list the projector is the clearing's identity. -/
theorem projGramRead_all (d L : Nat) : projGramRead d L := by
  show matOneValue (matMul (gram d L) (proj d L)) (matScaleB (projDen d L) (gram d L))
  have hΔl := gram_length d L
  have hΔr := gram_rows d L
  cases hn : plaqCount d L with
  | zero =>
    have hG : gram d L = [] := List.eq_nil_of_length_eq_zero (hΔl.trans hn)
    rw [hG]
    exact trivial
  | succ n' =>
    have hn' : 0 < plaqCount d L := by rw [hn]; exact Nat.succ_pos n'
    have hSl : (matScaleB (projDen d L) (idMat (plaqCount d L))).length = plaqCount d L :=
      (length_scaleB _ _).trans (length_idMat _)
    have hSr : rowsLen (plaqCount d L) (matScaleB (projDen d L) (idMat (plaqCount d L))) :=
      rowsLen_scaleB _ _ _ (rowsLen_idMat _)
    have hΔS : matOneValue (matMul (gram d L) (matScaleB (projDen d L) (idMat (plaqCount d L))))
        (matScaleB (projDen d L) (gram d L)) := by
      refine matOne_trans (matMul_scaleR _ _ _ _ (rowsLen_idMat _)) ?_
      exact matOne_scaleB _ (matMul_idR _ _ hΔr hΔl hn' hn')
    cases hK : kerList d L with
    | nil =>
      refine matOne_trans (matMul_congrR (gram d L) _ _ (proj_rows d L) hSr (proj_length d L) hSl
        (proj_vacant d L hK)) hΔS
    | cons k0 kt =>
      have hr : 0 < (kerList d L).length := by rw [hK]; exact Nat.succ_pos _
      have hK0 := kerList_rows d L
      obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
      have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
      have hN0r : rowsLen (kerList d L).length (transposeM (kerList d L)) := rowsLen_transposeM _
      have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length
          = (kerList d L).length := (length_matMul _ _).trans hAl
      have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
        rowsLen_cast hN0l (rowsLen_matMul _ _)
      have hAKTl : (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length
          = plaqCount d L := length_transposeM _ hAKr (by rw [hAKl]; exact hr)
      have hMl : (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length = plaqCount d L :=
        (length_matMul _ _).trans hN0l
      have hMr : rowsLen (plaqCount d L) (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))) :=
        rowsLen_cast hAKTl (rowsLen_matMul _ _)
      have hsMl : (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = plaqCount d L :=
        (length_matSwap _).trans hMl
      have hsMr : rowsLen (plaqCount d L) (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) := rowsLen_matSwap _ _ hMr
      have hRl : (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matSwap (matMul (transposeM (kerList d L))
            (matMul (adjMD (gramM (kerList d L))) (kerList d L))))).length = plaqCount d L := by
        rw [length_matAdd _ _ (hSl.trans hsMl.symm), hSl]
      have hRr : rowsLen (plaqCount d L) (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matSwap (matMul (transposeM (kerList d L))
            (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) :=
        rowsLen_matAdd _ _ _ hSr hsMr
      -- Δ Π ≡ Δ (D 1 - N₀ A K₀) ≡ Δ (D 1) + (Δ N₀ A K₀)ˇ, the second summand vacant
      refine matOne_trans (matMul_congrR (gram d L) _ _ (proj_rows d L) hRr (proj_length d L) hRl
        (proj_bridge d L hr)) ?_
      refine matOne_trans (matMul_addR _ _ hSr hsMr (hSl.trans hsMl.symm) (by rw [hSl]; exact hn')
        (gram d L) (by rw [hSl]; exact hΔr)) ?_
      rw [matMul_swap]
      have hnull : matNull (matMul (gram d L) (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) := by
        refine matNull_congr (matOne_symm (matMul_assoc (gram d L) (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)) hΔr hN0r hAKr hN0l hAKl hn' hr)) ?_
        exact matNull_mul_left _ _ (gramKer_null d L hr hn')
      have hΔSl : (matMul (gram d L) (matScaleB (projDen d L) (idMat (plaqCount d L)))).length
          = plaqCount d L := (length_matMul _ _).trans hΔl
      have hΔSr : rowsLen (plaqCount d L)
          (matMul (gram d L) (matScaleB (projDen d L) (idMat (plaqCount d L)))) :=
        rowsLen_cast (length_transposeM _ hSr (by rw [hSl]; exact hn')) (rowsLen_matMul _ _)
      have hΔMl : (matMul (gram d L) (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = plaqCount d L :=
        (length_matMul _ _).trans hΔl
      have hΔMr : rowsLen (plaqCount d L) (matMul (gram d L) (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) :=
        rowsLen_cast (length_transposeM _ hMr (by rw [hMl]; exact hn')) (rowsLen_matMul _ _)
      refine matOne_trans (matAdd_cong2 (plaqCount d L) _ _ (matScaleB (projDen d L) (gram d L))
        (matSwap (matMul (gram d L) (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))))
        hΔSr (rowsLen_matSwap _ _ hΔMr) (rowsLen_scaleB _ _ _ hΔr) (rowsLen_matSwap _ _ hΔMr)
        hΔS (matOne_refl _)) ?_
      exact matAdd_nullR _ _ (sqAt_of ((length_scaleB _ _).trans hΔl) (rowsLen_scaleB _ _ _ hΔr))
        (sqAt_of ((length_matSwap _).trans hΔMl) (rowsLen_matSwap _ _ hΔMr))
        (matNull_matSwap _ hnull)

/-- The adjugate against the list, against the cross term: the
clearing's multiple of the adjugate against the list,
`(adj G) K₀ (N₀ (adj G) K₀) ≡ D (adj G) K₀`. -/
private theorem crossInner_read (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matOneValue (matMul (matMul (adjMD (gramM (kerList d L))) (kerList d L))
      (matMul (transposeM (kerList d L)) (matMul (adjMD (gramM (kerList d L))) (kerList d L))))
      (matScaleB (projDen d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L))) := by
  have hK0 := kerList_rows d L
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hN0r : rowsLen (kerList d L).length (transposeM (kerList d L)) := rowsLen_transposeM _
  have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length
      = (kerList d L).length := (length_matMul _ _).trans hAl
  have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
    rowsLen_cast hN0l (rowsLen_matMul _ _)
  refine matOne_trans (matOne_symm (matMul_assoc
    (matMul (adjMD (gramM (kerList d L))) (kerList d L)) (transposeM (kerList d L))
    (matMul (adjMD (gramM (kerList d L))) (kerList d L)) hAKr hN0r hAKr hN0l hAKl hn hr)) ?_
  refine matOne_trans (matMul_congrL _ _ _ (akn_read d L hr hn)) ?_
  refine matOne_trans (matMul_scaleL _ _ _) ?_
  exact matOne_scaleB _ (idMat_matMul _ _ hAKr hAKl hr)

/-- The cross term's square: the list's transpose against the
adjugate against the list, squared, is the clearing's multiple of
itself, `M M ≡ D M` at the adjugate identity. -/
private theorem crossSq_read (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matOneValue (matMul (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L)))
        (matMul (transposeM (kerList d L)) (matMul (adjMD (gramM (kerList d L))) (kerList d L))))
      (matScaleB (projDen d L) (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) := by
  have hK0 := kerList_rows d L
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hN0r : rowsLen (kerList d L).length (transposeM (kerList d L)) := rowsLen_transposeM _
  have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length
      = (kerList d L).length := (length_matMul _ _).trans hAl
  have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
    rowsLen_cast hN0l (rowsLen_matMul _ _)
  have hAKTl : (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length
      = plaqCount d L := length_transposeM _ hAKr (by rw [hAKl]; exact hr)
  have hMl : (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length = plaqCount d L :=
    (length_matMul _ _).trans hN0l
  have hMr : rowsLen (plaqCount d L) (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))) :=
    rowsLen_cast hAKTl (rowsLen_matMul _ _)
  have hMTl : (transposeM (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = plaqCount d L :=
    length_transposeM _ hMr (by rw [hMl]; exact hn)
  have hinl : (matMul (matMul (adjMD (gramM (kerList d L))) (kerList d L))
      (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = (kerList d L).length :=
    (length_matMul _ _).trans hAKl
  have hinr : rowsLen (plaqCount d L) (matMul (matMul (adjMD (gramM (kerList d L))) (kerList d L))
      (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) :=
    rowsLen_cast hMTl (rowsLen_matMul _ _)
  refine matOne_trans (matMul_assoc (transposeM (kerList d L))
    (matMul (adjMD (gramM (kerList d L))) (kerList d L))
    (matMul (transposeM (kerList d L)) (matMul (adjMD (gramM (kerList d L))) (kerList d L)))
    hN0r hAKr hMr hAKl hMl hr hn) ?_
  refine matOne_trans (matMul_congrR (transposeM (kerList d L)) _ _ hinr
    (rowsLen_scaleB _ _ _ hAKr) hinl ((length_scaleB _ _).trans hAKl)
    (crossInner_read d L hr hn)) ?_
  exact matMul_scaleR _ _ _ _ hAKr

/-- The swapped cross term's two products, against the clearing's
identity and against itself, fold to the vacant family:
`Mˇ (D 1) + Mˇ Mˇ ≡ (D M)ˇ + D M`. -/
private theorem idem_swapPart (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matNull (matAdd (matMul (matSwap (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L))))
        (matScaleB (projDen d L) (idMat (plaqCount d L))))
      (matMul (matSwap (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L))))
        (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))))) := by
  have hK0 := kerList_rows d L
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length
      = (kerList d L).length := (length_matMul _ _).trans hAl
  have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
    rowsLen_cast hN0l (rowsLen_matMul _ _)
  have hAKTl : (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length
      = plaqCount d L := length_transposeM _ hAKr (by rw [hAKl]; exact hr)
  have hMl : (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length = plaqCount d L :=
    (length_matMul _ _).trans hN0l
  have hMr : rowsLen (plaqCount d L) (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))) :=
    rowsLen_cast hAKTl (rowsLen_matMul _ _)
  have hMTl : (transposeM (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = plaqCount d L :=
    length_transposeM _ hMr (by rw [hMl]; exact hn)
  have hSl : (matScaleB (projDen d L) (idMat (plaqCount d L))).length = plaqCount d L :=
    (length_scaleB _ _).trans (length_idMat _)
  have hSr : rowsLen (plaqCount d L) (matScaleB (projDen d L) (idMat (plaqCount d L))) :=
    rowsLen_scaleB _ _ _ (rowsLen_idMat _)
  have hSTl : (transposeM (matScaleB (projDen d L) (idMat (plaqCount d L)))).length
      = plaqCount d L := length_transposeM _ hSr (by rw [hSl]; exact hn)
  have hMS : matOneValue (matMul (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))
      (matScaleB (projDen d L) (idMat (plaqCount d L))))
      (matScaleB (projDen d L) (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) :=
    matOne_trans (matMul_scaleR _ _ _ _ (rowsLen_idMat _))
      (matOne_scaleB _ (matMul_idR _ _ hMr hMl hn hn))
  have hMSr : rowsLen (plaqCount d L) (matMul (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))
      (matScaleB (projDen d L) (idMat (plaqCount d L)))) :=
    rowsLen_cast hSTl (rowsLen_matMul _ _)
  have hMMr : rowsLen (plaqCount d L) (matMul (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))
      (matMul (transposeM (kerList d L)) (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) :=
    rowsLen_cast hMTl (rowsLen_matMul _ _)
  have hDMr : rowsLen (plaqCount d L) (matScaleB (projDen d L) (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) := rowsLen_scaleB _ _ _ hMr
  rw [matMul_swapL, matMul_swapL, matMul_swap, matSwap_matSwap]
  refine matNull_congr (matAdd_cong2 (plaqCount d L) _ _
    (matSwap (matScaleB (projDen d L) (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))))
    (matScaleB (projDen d L) (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))))
    (rowsLen_matSwap _ _ hMSr) hMMr (rowsLen_matSwap _ _ hDMr) hDMr
    (matSwap_congr hMS) (crossSq_read d L hr hn)) ?_
  exact matNull_swap_add (matOne_refl _)

/-- The clearing's identity's two products, against itself and
against the swapped cross term, fold to the clearing's multiple of
the projector's cleared read: `(D 1)(D 1) + (D 1) Mˇ ≡ D (D 1 + Mˇ)`. -/
private theorem idem_idPart (d L : Nat) (hr : 0 < (kerList d L).length)
    (hn : 0 < plaqCount d L) :
    matOneValue (matAdd (matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
        (matScaleB (projDen d L) (idMat (plaqCount d L))))
        (matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matSwap (matMul (transposeM (kerList d L))
            (matMul (adjMD (gramM (kerList d L))) (kerList d L))))))
      (matScaleB (projDen d L) (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
        (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))))) := by
  have hK0 := kerList_rows d L
  obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
  have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
  have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length
      = (kerList d L).length := (length_matMul _ _).trans hAl
  have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
    rowsLen_cast hN0l (rowsLen_matMul _ _)
  have hAKTl : (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length
      = plaqCount d L := length_transposeM _ hAKr (by rw [hAKl]; exact hr)
  have hMl : (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length = plaqCount d L :=
    (length_matMul _ _).trans hN0l
  have hMr : rowsLen (plaqCount d L) (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))) :=
    rowsLen_cast hAKTl (rowsLen_matMul _ _)
  have hsMl : (matSwap (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = plaqCount d L :=
    (length_matSwap _).trans hMl
  have hsMr : rowsLen (plaqCount d L) (matSwap (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) := rowsLen_matSwap _ _ hMr
  have hsMTl : (transposeM (matSwap (matMul (transposeM (kerList d L))
      (matMul (adjMD (gramM (kerList d L))) (kerList d L))))).length = plaqCount d L :=
    length_transposeM _ hsMr (by rw [hsMl]; exact hn)
  have hSl : (matScaleB (projDen d L) (idMat (plaqCount d L))).length = plaqCount d L :=
    (length_scaleB _ _).trans (length_idMat _)
  have hSr : rowsLen (plaqCount d L) (matScaleB (projDen d L) (idMat (plaqCount d L))) :=
    rowsLen_scaleB _ _ _ (rowsLen_idMat _)
  have hSTl : (transposeM (matScaleB (projDen d L) (idMat (plaqCount d L)))).length
      = plaqCount d L := length_transposeM _ hSr (by rw [hSl]; exact hn)
  have hSS : matOneValue (matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
      (matScaleB (projDen d L) (idMat (plaqCount d L))))
      (matScaleB (projDen d L) (matScaleB (projDen d L) (idMat (plaqCount d L)))) :=
    matOne_trans (matMul_scaleL _ _ _) (matOne_scaleB _ (idMat_matMul _ _ hSr hSl hn))
  have hSsM : matOneValue (matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
      (matSwap (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L)))))
      (matScaleB (projDen d L) (matSwap (matMul (transposeM (kerList d L))
        (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) :=
    matOne_trans (matMul_scaleL _ _ _) (matOne_scaleB _ (idMat_matMul _ _ hsMr hsMl hn))
  refine matOne_trans (matAdd_cong2 (plaqCount d L) _ _ _ _
    (rowsLen_cast hSTl (rowsLen_matMul _ _)) (rowsLen_cast hsMTl (rowsLen_matMul _ _))
    (rowsLen_scaleB _ _ _ hSr) (rowsLen_scaleB _ _ _ hsMr) hSS hSsM) ?_
  exact matOne_symm (matScaleB_sum _ _ _)

/-- The projector's idempotence at the clearing at every window:
`(DΠ)(DΠ) ≡ D (DΠ)`, the cross term's square at the adjugate
identity and the identity's square at the clearing's square. -/
theorem projIdemRead_all (d L : Nat) : projIdemRead d L := by
  show matOneValue (matMul (proj d L) (proj d L)) (matScaleB (projDen d L) (proj d L))
  cases hn : plaqCount d L with
  | zero =>
    have hP : proj d L = [] := List.eq_nil_of_length_eq_zero ((proj_length d L).trans hn)
    rw [hP]
    exact trivial
  | succ n' =>
    have hn' : 0 < plaqCount d L := by rw [hn]; exact Nat.succ_pos n'
    have hPl := proj_length d L
    have hPr := proj_rows d L
    have hSl : (matScaleB (projDen d L) (idMat (plaqCount d L))).length = plaqCount d L :=
      (length_scaleB _ _).trans (length_idMat _)
    have hSr : rowsLen (plaqCount d L) (matScaleB (projDen d L) (idMat (plaqCount d L))) :=
      rowsLen_scaleB _ _ _ (rowsLen_idMat _)
    cases hK : kerList d L with
    | nil =>
      have hv := proj_vacant d L hK
      have hSS : matOneValue (matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matScaleB (projDen d L) (idMat (plaqCount d L))))
          (matScaleB (projDen d L) (matScaleB (projDen d L) (idMat (plaqCount d L)))) :=
        matOne_trans (matMul_scaleL _ _ _) (matOne_scaleB _ (idMat_matMul _ _ hSr hSl hn'))
      refine matOne_trans (matMul_congrL _ _ (proj d L) hv) ?_
      refine matOne_trans (matMul_congrR _ _ _ hPr hSr hPl hSl hv) ?_
      exact matOne_trans hSS (matOne_scaleB _ (matOne_symm hv))
    | cons k0 kt =>
      have hr : 0 < (kerList d L).length := by rw [hK]; exact Nat.succ_pos _
      have hK0 := kerList_rows d L
      obtain ⟨hAl, hAr⟩ := adjMD_gram_shape (kerList d L)
      have hN0l : (transposeM (kerList d L)).length = plaqCount d L := length_transposeM _ hK0 hr
      have hAKl : (matMul (adjMD (gramM (kerList d L))) (kerList d L)).length
          = (kerList d L).length := (length_matMul _ _).trans hAl
      have hAKr : rowsLen (plaqCount d L) (matMul (adjMD (gramM (kerList d L))) (kerList d L)) :=
        rowsLen_cast hN0l (rowsLen_matMul _ _)
      have hAKTl : (transposeM (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length
          = plaqCount d L := length_transposeM _ hAKr (by rw [hAKl]; exact hr)
      have hMl : (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))).length = plaqCount d L :=
        (length_matMul _ _).trans hN0l
      have hMr : rowsLen (plaqCount d L) (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))) :=
        rowsLen_cast hAKTl (rowsLen_matMul _ _)
      have hsMl : (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))).length = plaqCount d L :=
        (length_matSwap _).trans hMl
      have hsMr : rowsLen (plaqCount d L) (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L)))) := rowsLen_matSwap _ _ hMr
      have hSTr : rowsLen (plaqCount d L) (transposeM (matScaleB (projDen d L)
          (idMat (plaqCount d L)))) := rowsLen_cast hSl (rowsLen_transposeM _)
      have hSTl : (transposeM (matScaleB (projDen d L) (idMat (plaqCount d L)))).length
          = plaqCount d L := length_transposeM _ hSr (by rw [hSl]; exact hn')
      have hsMTr : rowsLen (plaqCount d L) (transposeM (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) :=
        rowsLen_cast hsMl (rowsLen_transposeM _)
      have hsMTl : (transposeM (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))))).length = plaqCount d L :=
        length_transposeM _ hsMr (by rw [hsMl]; exact hn')
      have hRl : (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matSwap (matMul (transposeM (kerList d L))
            (matMul (adjMD (gramM (kerList d L))) (kerList d L))))).length = plaqCount d L := by
        rw [length_matAdd _ _ (hSl.trans hsMl.symm), hSl]
      have hRr : rowsLen (plaqCount d L) (matAdd (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matSwap (matMul (transposeM (kerList d L))
            (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) :=
        rowsLen_matAdd _ _ _ hSr hsMr
      have hbr := proj_bridge d L hr
      have hSSr : rowsLen (plaqCount d L) (matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matScaleB (projDen d L) (idMat (plaqCount d L)))) :=
        rowsLen_cast hSTl (rowsLen_matMul _ _)
      have hsMSr : rowsLen (plaqCount d L) (matMul (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))))
          (matScaleB (projDen d L) (idMat (plaqCount d L)))) :=
        rowsLen_cast hSTl (rowsLen_matMul _ _)
      have hSsMr : rowsLen (plaqCount d L) (matMul (matScaleB (projDen d L) (idMat (plaqCount d L)))
          (matSwap (matMul (transposeM (kerList d L))
            (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) :=
        rowsLen_cast hsMTl (rowsLen_matMul _ _)
      have hsMsMr : rowsLen (plaqCount d L) (matMul (matSwap (matMul (transposeM (kerList d L))
          (matMul (adjMD (gramM (kerList d L))) (kerList d L))))
          (matSwap (matMul (transposeM (kerList d L))
            (matMul (adjMD (gramM (kerList d L))) (kerList d L))))) :=
        rowsLen_cast hsMTl (rowsLen_matMul _ _)
      -- Π Π ≡ P P at the bridge, P P the four products regrouped
      refine matOne_trans (matMul_congrL _ _ (proj d L) hbr) ?_
      refine matOne_trans (matMul_congrR _ _ _ hPr hRr hPl hRl hbr) ?_
      refine matOne_trans (matMul_addR _ _ hSr hsMr (hSl.trans hsMl.symm) (by rw [hSl]; exact hn')
        _ (by rw [hSl]; exact hRr)) ?_
      refine matOne_trans (matAdd_cong2 (plaqCount d L) _ _ _ _
        (rowsLen_cast hSTl (rowsLen_matMul _ _)) (rowsLen_cast hsMTl (rowsLen_matMul _ _))
        (rowsLen_matAdd _ _ _ hSSr hsMSr) (rowsLen_matAdd _ _ _ hSsMr hsMsMr)
        (matMul_addL (plaqCount d L) _ hSTr _ _ hSr hsMr)
        (matMul_addL (plaqCount d L) _ hsMTr _ _ hSr hsMr)) ?_
      rw [matAdd_shuffle]
      refine matOne_trans (matAdd_nullR _ _ (sqAt_of (length_matAdd _ _ (
        ((length_matMul _ _).trans hSl).trans ((length_matMul _ _).trans hSl).symm) |>.trans
          ((length_matMul _ _).trans hSl)) (rowsLen_matAdd _ _ _ hSSr hSsMr))
        (sqAt_of (length_matAdd _ _ (
          ((length_matMul _ _).trans hsMl).trans ((length_matMul _ _).trans hsMl).symm) |>.trans
          ((length_matMul _ _).trans hsMl)) (rowsLen_matAdd _ _ _ hsMSr hsMsMr))
        (idem_swapPart d L hr hn')) ?_
      exact matOne_trans (idem_idPart d L hr hn') (matOne_scaleB _ (matOne_symm hbr))

/-! The profile. -/

/-- The parabola `w_b = b (L + 1 - b)`, the sum's unit at `b = 0` and
`b = L + 1`. -/
def wAt (L b : Nat) : Nat := b * (L + 1 - b)

/-- The profile's entry at a plaquette: the parabolas' product at
the corner's plane coordinates on the first two directions' plane,
the sum's unit off it. -/
def profAt (L : Nat) (p : Nat × Nat × Nat) : BPair :=
  if p.1 == 0 && p.2.1 == 1 then
    BPair.ofNat (wAt L (coordAt L 0 p.2.2 + 1) * wAt L (coordAt L 1 p.2.2 + 1))
  else BPair.unit

/-- The profile `W`: `w_x w_y` at a plaquette of the first two
directions' plane at its corner's plane coordinates, the sum's unit
off that plane. -/
def profile (d L : Nat) : List BPair := (plaqList d L).map (profAt L)

/-- The profile's entry off the first two directions' plane is the
sum's unit. -/
theorem profAt_off (L : Nat) (q : Nat × Nat × Nat) (hq : ¬ (q.1 = 0 ∧ q.2.1 = 1)) :
    profAt L q = BPair.unit := by
  show (if q.1 == 0 && q.2.1 == 1 then _ else BPair.unit) = BPair.unit
  cases hb : (q.1 == 0 && q.2.1 == 1) with
  | true => exact absurd ⟨beqEqOf (andSplitB hb).1, beqEqOf (andSplitB hb).2⟩ hq
  | false => rfl

/-- The profile's length is the plaquettes' count. -/
theorem profile_length (d L : Nat) : (profile d L).length = plaqCount d L := by
  show ((plaqList d L).map (profAt L)).length = _
  rw [ground.length_map]
  rfl

/-- The profile in the range: the cubes' boundaries pair it at the
sum's unit. -/
def profRangeRead (d L : Nat) : Prop :=
  poly.unitTail (matVec (transposeM (cubeBd d L)) (profile d L))

instance instCornerwindow8 (d L : Nat) : Decidable (profRangeRead d L) :=
  poly.decUnitTail _

/-! The profile's range read at every window. -/

/-- The profile's entry at a plaquette's key: the parabolas' product
at the corner's plane coordinates on the first two directions'
plane, the sum's unit off it. -/
theorem profile_entry (d L a k s : Nat) (hak : a < k) (hk : k < d) (hs : s < (L + 1) ^ d)
    (hca : coordAt L a s < L) (hck : coordAt L k s < L) :
    getAt BPair.unit (profile d L) (plaqKey d L a k s)
      = (if a == 0 && k == 1 then
          BPair.ofNat (wAt L (coordAt L 0 s + 1) * wAt L (coordAt L 1 s + 1))
        else BPair.unit) :=
  plaqVec_entry d L (profAt L) a k s hak hk hs hca hck

/-- The profile in the range at every window: a cube's two faces on
the first two directions' plane read one value at exchanged signs
and its further faces sit off the support. -/
theorem profRangeRead_all (d L : Nat) : profRangeRead d L := by
  show poly.unitTail (matVec (transposeM (cubeBd d L)) (profile d L))
  have hNlen := cubeBd_length d L
  have hN := cubeBd_rows d L
  have hW := profile_length d L
  cases hNc : cubeBd d L with
  | nil => exact trivial
  | cons r t =>
    rw [hNc] at hNlen hN
    have hpos : 0 < (r :: t).length := Nat.succ_pos _
    have hNt : (transposeM (r :: t)).length = cubeCount d L := length_transposeM _ hN hpos
    refine unitTail_of_getAt (matVec (transposeM (r :: t)) (profile d L)) (fun k hk => ?_)
    have hk' : k < (transposeM (r :: t)).length := by
      rw [matVec_length] at hk
      exact hk
    have hkc : k < cubeCount d L := by
      rw [← hNt]
      exact hk'
    refine BPair.oneValue_trans (getAt_matVec_transposeM (r :: t) hN hpos (profile d L)
      (by rw [hW]; exact hNlen.symm) k hkc) ?_
    rw [hNlen]
    refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun p =>
      getAt BPair.unit (profile d L) p
        * keyFoldB (fun a b => a == b) p (cubeFaces d L (getAt (0, 0, 0, 0) (cubeList d L) k)))
      (plaqCount d L) (fun p hp => ?_)) ?_
    · rw [← hNc, cubeBd_entry d L p k hp hkc]
      exact BPair.oneValue_of_eq (BPair.mul_comm _ _)
    · have hcl := cube_of_mem d L _ (mem_getAt (0, 0, 0, 0) (cubeList d L) k hkc)
      generalize hq : getAt (0, 0, 0, 0) (cubeList d L) k = c at hcl ⊢
      cases c with
      | mk a c1 =>
      cases c1 with
      | mk b c2 =>
      cases c2 with
      | mk c' s =>
      obtain ⟨hab, hbc, hcd, hsd, hca, hcb, hcc⟩ := hcl
      have hbd : b < d := Nat.lt_trans hbc hcd
      have had : a < d := Nat.lt_trans hab hbd
      have hac : a < c' := Nat.lt_trans hab hbc
      have nab : ¬ a = b := Nat.ne_of_lt hab
      have nac : ¬ a = c' := Nat.ne_of_lt hac
      have nbc : ¬ b = c' := Nat.ne_of_lt hbc
      have sC := stepAt_lt d L c' s hcd hsd hcc
      have sB := stepAt_lt d L b s hbd hsd hcb
      have sA := stepAt_lt d L a s had hsd hca
      have caC : coordAt L a (stepAt L c' s) < L := by
        rw [coordAt_step_ne L c' a s hcc nac]
        exact hca
      have cbC : coordAt L b (stepAt L c' s) < L := by
        rw [coordAt_step_ne L c' b s hcc nbc]
        exact hcb
      have caB : coordAt L a (stepAt L b s) < L := by
        rw [coordAt_step_ne L b a s hcb nab]
        exact hca
      have ccB : coordAt L c' (stepAt L b s) < L := by
        rw [coordAt_step_ne L b c' s hcb (fun h => nbc h.symm)]
        exact hcc
      have cbA : coordAt L b (stepAt L a s) < L := by
        rw [coordAt_step_ne L a b s hca (fun h => nab h.symm)]
        exact hcb
      have ccA : coordAt L c' (stepAt L a s) < L := by
        rw [coordAt_step_ne L a c' s hca (fun h => nac h.symm)]
        exact hcc
      refine BPair.oneValue_trans (bsum_keyFold_linear (plaqCount d L) _
        (cubeFaces d L (a, b, c', s)) ?_) ?_
      · intro f hf
        cases hf with
        | head => exact plaqKey_lt d L a b s hab hbd hsd hca hcb
        | tail _ hf =>
          cases hf with
          | head => exact plaqKey_lt d L a b (stepAt L c' s) hab hbd sC caC cbC
          | tail _ hf =>
            cases hf with
            | head => exact plaqKey_lt d L a c' s hac hcd hsd hca hcc
            | tail _ hf =>
              cases hf with
              | head => exact plaqKey_lt d L a c' (stepAt L b s) hac hcd sB caB ccB
              | tail _ hf =>
                cases hf with
                | head => exact plaqKey_lt d L b c' s hbc hcd hsd hcb hcc
                | tail _ hf =>
                  cases hf with
                  | head => exact plaqKey_lt d L b c' (stepAt L a s) hbc hcd sA cbA ccA
                  | tail _ hf => nomatch hf
      · show (getAt BPair.unit (profile d L) (plaqKey d L a b s) * BPair.ofNat 1
          + (getAt BPair.unit (profile d L) (plaqKey d L a b (stepAt L c' s)) * (BPair.ofNat 1).swap
          + (getAt BPair.unit (profile d L) (plaqKey d L a c' s) * (BPair.ofNat 1).swap
          + (getAt BPair.unit (profile d L) (plaqKey d L a c' (stepAt L b s)) * BPair.ofNat 1
          + (getAt BPair.unit (profile d L) (plaqKey d L b c' s) * BPair.ofNat 1
          + (getAt BPair.unit (profile d L) (plaqKey d L b c' (stepAt L a s)) * (BPair.ofNat 1).swap
          + BPair.unit)))))).oneValue BPair.unit
        rw [profile_entry d L a b s hab hbd hsd hca hcb,
          profile_entry d L a b (stepAt L c' s) hab hbd sC caC cbC,
          profile_entry d L a c' s hac hcd hsd hca hcc,
          profile_entry d L a c' (stepAt L b s) hac hcd sB caB ccB,
          profile_entry d L b c' s hbc hcd hsd hcb hcc,
          profile_entry d L b c' (stepAt L a s) hbc hcd sA cbA ccA]
        have h3 : (a == 0 && c' == 1) = false := by
          cases hc1 : (c' == 1) with
          | false => exact Bool.and_false _
          | true =>
            have hc : c' = 1 := beqEqOf hc1
            rw [hc] at hbc
            exact absurd (Nat.lt_of_lt_of_le hab (Nat.le_of_lt_succ hbc)) (Nat.not_lt_zero a)
        have h5 : (b == 0 && c' == 1) = false := by
          cases hb0 : (b == 0) with
          | false => exact Bool.false_and _
          | true =>
            have hb : b = 0 := beqEqOf hb0
            rw [hb] at hab
            exact absurd hab (Nat.not_lt_zero a)
        rw [h3, h5]
        have htail : (BPair.unit * (BPair.ofNat 1).swap + (BPair.unit * BPair.ofNat 1
            + (BPair.unit * BPair.ofNat 1 + (BPair.unit * (BPair.ofNat 1).swap
              + BPair.unit)))).oneValue BPair.unit :=
          BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _)
            (BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _)
              (BPair.oneValue_refl _))))
        cases h01 : (a == 0 && b == 1) with
        | false =>
          exact BPair.add_units (BPair.unit_mul _) (BPair.add_units (BPair.unit_mul _) htail)
        | true =>
          have hs01 := andSplitB h01
          have ha0 : a = 0 := beqEqOf hs01.1
          have hb1 : b = 1 := beqEqOf hs01.2
          have hc0 : ¬ (0 : Nat) = c' := fun h => nac (ha0.trans h)
          have hc1 : ¬ (1 : Nat) = c' := fun h => nbc (hb1.trans h)
          rw [coordAt_step_ne L c' 0 s hcc hc0, coordAt_step_ne L c' 1 s hcc hc1]
          refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.add_congr (BPair.oneValue_refl _) htail)) ?_
          refine BPair.oneValue_trans (BPair.add_congr (BPair.oneValue_refl _)
            (BPair.add_unit _)) ?_
          rw [BPair.mul_swap]
          exact BPair.add_swap_null _


/-- The mode read `Wᵀ Δ W = e_W Wᵀ W` at `e_W = [20 : L² + 2L + 2]`,
cross-multiplied. -/
def modeRead (d L : Nat) : Prop :=
  (BPair.ofNat (L * L + 2 * L + 2) * quadForm (gram d L) (profile d L)).oneValue
    (BPair.ofNat 20 * dotN (profile d L) (profile d L))

instance instCornerwindow9 (d L : Nat) : Decidable (modeRead d L) :=
  inferInstanceAs (Decidable (BPair.oneValue _ _))

/-! The profile's two closed sums in the side: the parabola's
squares and its consecutive differences' squares, each the power
sums' closed reads at one polynomial identity. -/

/-- The parabola at the endpoint's gap: at `b + c = L + 1`,
`w_b = b c`. -/
private theorem wAt_gap (L b c : Nat) (h : b + c = L + 1) : wAt L b = b * c := by
  show b * (L + 1 - b) = b * c
  rw [← h, addSubSelfL b c]

/-- The parabola's square against the cube's key:
`w_b² + 2 (L + 1) b³ = (L + 1)² b² + b⁴`, the endpoint split at the
gap. -/
private theorem wAt_sq (L b : Nat) (hb : b ≤ L) :
    wAt L b * wAt L b + 2 * (L + 1) * (b * b * b)
      = (L + 1) * (L + 1) * (b * b) + b * b * b * b := by
  obtain ⟨c, hc0⟩ := Nat.le.dest (Nat.le_succ_of_le hb)
  have hc : b + c = L + 1 := hc0
  rw [wAt_gap L b c hc, ← hc]
  exact polEq [b, c]
    (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))) (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0)))))
    (Pol.add (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1)))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))))
    (by decide +kernel)

/-- The parabola's squares' closed sum over the side,
`30 Σ_{b=1}^{L} w_b² = L (L + 1)(L + 2)(L² + 2L + 2)`. -/
theorem profSq_closed (L : Nat) :
    30 * ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
      = L * (L + 1) * (L + 2) * (L * L + 2 * L + 2) := by
  -- the per-term identity summed over the side
  have hsum : ground.sumNat ((List.range L).map (fun j =>
        wAt L (j + 1) * wAt L (j + 1) + 2 * (L + 1) * ((j + 1) * (j + 1) * (j + 1))))
      = ground.sumNat ((List.range L).map (fun j =>
        (L + 1) * (L + 1) * ((j + 1) * (j + 1)) + (j + 1) * (j + 1) * (j + 1) * (j + 1))) :=
    sumNat_congr_range _ _ L (fun j hj => wAt_sq L (j + 1) hj)
  rw [sumNat_map_add, sumNat_map_add,
    ← sumNat_scale (2 * (L + 1)) (fun j => (j + 1) * (j + 1) * (j + 1)),
    ← sumNat_scale ((L + 1) * (L + 1)) (fun j => (j + 1) * (j + 1))] at hsum
  -- the power sums at the products
  have S2 : ground.sumNat ((List.range L).map (fun j => (j + 1) * (j + 1))) = powSum 2 L :=
    sumNat_congr_range _ _ L (fun j _ => (ground.sqRead (j + 1)).symm)
  have S3 : ground.sumNat ((List.range L).map (fun j => (j + 1) * (j + 1) * (j + 1)))
      = powSum 3 L :=
    sumNat_congr_range _ _ L (fun j _ => (ground.pow3Read (j + 1)).symm)
  have S4 : ground.sumNat ((List.range L).map (fun j => (j + 1) * (j + 1) * (j + 1) * (j + 1)))
      = powSum 4 L :=
    sumNat_congr_range _ _ L (fun j _ => (ground.pow4Read (j + 1)).symm)
  rw [S2, S3, S4] at hsum
  have h2 : 6 * powSum 2 L = 2 * (L * L * L) + 3 * (L * L) + L := by
    rw [powSum2_closed, ground.pow3Read, ground.sqRead]
  have h3 : 4 * powSum 3 L = L * L * L * L + 2 * (L * L * L) + L * L := by
    rw [powSum3_closed, ground.pow4Read, ground.pow3Read, ground.sqRead]
  have h4 : 30 * powSum 4 L + L = 6 * (L * L * L * L * L) + 15 * (L * L * L * L) + 10 * (L * L * L) := by
    rw [powSum4_closed, ground.pow5Read, ground.pow4Read, ground.pow3Read]
  -- the identity multiplied through at thirty
  have key : 30 * (ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
        + 2 * (L + 1) * powSum 3 L) + L
      = 30 * ((L + 1) * (L + 1) * powSum 2 L + powSum 4 L) + L := by
    rw [hsum]
  have e1 : ∀ (Sw S3 : Nat), 30 * (Sw + 2 * (L + 1) * S3) + L
      = 30 * Sw + (15 * (L + 1) * (4 * S3) + L) := fun Sw S3 =>
    polEq [L, Sw, S3]
      (Pol.add (Pol.mul (Pol.mon (Mon.cst 30)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.mon (Mon.var 2))))) (Pol.mon (Mon.var 0)))
      (Pol.add (Pol.mul (Pol.mon (Mon.cst 30)) (Pol.mon (Mon.var 1))) (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 15)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.mon (Mon.var 2)))) (Pol.mon (Mon.var 0))))
      (by decide +kernel)
  have e2 : ∀ (S2 S4 : Nat), 30 * ((L + 1) * (L + 1) * S2 + S4) + L
      = 5 * ((L + 1) * (L + 1)) * (6 * S2) + (30 * S4 + L) := fun S2 S4 =>
    polEq [L, S2, S4]
      (Pol.add (Pol.mul (Pol.mon (Mon.cst 30)) (Pol.add (Pol.mul (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2)))) (Pol.mon (Mon.var 0)))
      (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 5)) (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))) (Pol.mul (Pol.mon (Mon.cst 6)) (Pol.mon (Mon.var 1)))) (Pol.add (Pol.mul (Pol.mon (Mon.cst 30)) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 0))))
      (by decide +kernel)
  rw [e1, e2, h3, h4, h2] at key
  refine addCancelR (15 * (L + 1) * (L * L * L * L + 2 * (L * L * L) + L * L) + L) ?_
  rw [key]
  refine (polEq [L]
    (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 0)))) (Pol.mon (Mon.cst 2)))) (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 15)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.add (Pol.add (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))))) (Pol.mon (Mon.var 0))))
    (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 5)) (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))))) (Pol.mon (Mon.var 0)))) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 6)) (Pol.mul (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.cst 15)) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))))) (Pol.mul (Pol.mon (Mon.cst 10)) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0))))))
    (by decide +kernel)).symm

/-- The consecutive parabolas' margin at the side's gap: at `b ≤ L`
the margin of `w_{b+1}` against `w_b` is the margin of `L` against
`2b`, the display `w_{b+1} + 2b = w_b + L`. -/
private theorem wAt_diff (L b : Nat) (hb : b ≤ L) :
    marg (wAt L (b + 1)) (wAt L b) = marg L (2 * b) := by
  obtain ⟨c, hc⟩ := Nat.le.dest hb
  have h1 : wAt L (b + 1) = (b + 1) * c := by
    show (b + 1) * (L + 1 - (b + 1)) = (b + 1) * c
    rw [← hc, Nat.add_right_comm b c 1, addSubSelfL (b + 1) c]
  have h2 : wAt L b = b * (c + 1) := by
    show b * (L + 1 - b) = b * (c + 1)
    rw [← hc, Nat.add_assoc b c 1, addSubSelfL b (c + 1)]
  have hD : (b + 1) * c + 2 * b = b * (c + 1) + (b + c) :=
    polEq [b, c]
      (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 0))))
      (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 1)))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))))
      (by decide +kernel)
  rw [h1, h2, ← marg_add ((b + 1) * c) (b * (c + 1)) (2 * b), hD,
    Nat.add_comm (b * (c + 1)) (b + c), Nat.add_comm (b * (c + 1)) (2 * b),
    marg_add (b + c) (2 * b) (b * (c + 1)), hc]

/-- The consecutive differences' squares' closed sum over the side,
`3 Σ_{b=0}^{L} ⟨w_{b+1} : w_b⟩² = L (L + 1)(L + 2)`, the margins'
squares at the parabola's steps. -/
theorem profDiff_closed (L : Nat) :
    3 * ground.sumNat ((List.range (L + 1)).map (fun b =>
        marg (wAt L (b + 1)) (wAt L b) ^ 2))
      = L * (L + 1) * (L + 2) := by
  have hsum : ground.sumNat ((List.range (L + 1)).map (fun b =>
        marg (wAt L (b + 1)) (wAt L b) ^ 2 + 2 * L * (2 * b)))
      = ground.sumNat ((List.range (L + 1)).map (fun b => L * L + 2 * b * (2 * b))) :=
    sumNat_congr_range _ _ (L + 1) (fun b hb => by
      rw [wAt_diff L b (Nat.le_of_lt_succ hb)]
      exact margSqNat L (2 * b))
  rw [sumNat_map_add, sumNat_map_add] at hsum
  have hc : ground.sumNat ((List.range (L + 1)).map (fun _ => L * L)) = (L + 1) * (L * L) := by
    rw [ground.sumMap, famFold_const (L * L) (List.range (L + 1)), ground.length_range]
  have hb1 : ground.sumNat ((List.range (L + 1)).map (fun b => 2 * L * (2 * b)))
      = 4 * L * powSum 1 L := by
    rw [ground.sumNat_range_cons, Nat.mul_zero, Nat.zero_add,
      sumNat_congr_range _ (fun j => 4 * L * (j + 1) ^ 1) L (fun j _ => by
        rw [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
        exact polEq [L, j]
          (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 1)))))
          (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.mon (Mon.var 0))) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mon (Mon.cst 1))))
          (by decide +kernel)),
      ← sumNat_scale (4 * L) (fun j => (j + 1) ^ 1)]
    rfl
  have hb2 : ground.sumNat ((List.range (L + 1)).map (fun b => 2 * b * (2 * b)))
      = 4 * powSum 2 L := by
    rw [ground.sumNat_range_cons, Nat.mul_zero, Nat.zero_add,
      sumNat_congr_range _ (fun j => 4 * (j + 1) ^ 2) L (fun j _ => by
        rw [ground.sqRead]
        exact polEq [j]
          (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))))
          (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))))
          (by decide +kernel)),
      ← sumNat_scale 4 (fun j => (j + 1) ^ 2)]
    rfl
  rw [hc, hb1, hb2] at hsum
  have h1 : 2 * powSum 1 L = L * L + L := by
    rw [powSum1_closed, ground.sqRead]
  have h2 : 6 * powSum 2 L = 2 * (L * L * L) + 3 * (L * L) + L := by
    rw [powSum2_closed, ground.pow3Read, ground.sqRead]
  have key : 3 * (ground.sumNat ((List.range (L + 1)).map (fun b =>
        marg (wAt L (b + 1)) (wAt L b) ^ 2)) + 4 * L * powSum 1 L)
      = 3 * ((L + 1) * (L * L) + 4 * powSum 2 L) := by
    rw [hsum]
  have e1 : ∀ (Sm S1 : Nat), 3 * (Sm + 4 * L * S1) = 3 * Sm + 6 * L * (2 * S1) := fun Sm S1 =>
    polEq [L, Sm, S1]
      (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.add (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 2)))))
      (Pol.add (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mul (Pol.mon (Mon.cst 6)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 2)))))
      (by decide +kernel)
  have e2 : ∀ (S2 : Nat), 3 * ((L + 1) * (L * L) + 4 * S2) = 3 * (L + 1) * (L * L) + 2 * (6 * S2) :=
    fun S2 => polEq [L, S2]
      (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.add (Pol.mul (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.cst 4)) (Pol.mon (Mon.var 1)))))
      (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mul (Pol.mon (Mon.cst 6)) (Pol.mon (Mon.var 1)))))
      (by decide +kernel)
  rw [e1, e2, h1, h2] at key
  refine addCancelR (6 * L * (L * L + L)) ?_
  rw [key]
  exact (polEq [L]
    (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 2)))) (Pol.mul (Pol.mul (Pol.mon (Mon.cst 6)) (Pol.mon (Mon.var 0))) (Pol.add (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0)))))
    (Pol.add (Pol.mul (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.add (Pol.mon (Mon.var 0)) (Pol.mon (Mon.cst 1)))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.add (Pol.add (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 0)))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))))) (Pol.mon (Mon.var 0)))))
    (by decide +kernel)).symm

/-! The mode read at every window: the transposed incidence against
the profile read link by link, the links' fold reindexed over the
link list at its keys and folded over the box's two plane digits to
the two closed sums. -/

/-- The parabola at the side's successor and at nought reads the
sum's unit. -/
private theorem wAt_ends (L : Nat) : wAt L (L + 1) = 0 ∧ wAt L 0 = 0 := by
  refine ⟨?_, ?_⟩
  · show (L + 1) * (L + 1 - (L + 1)) = 0
    rw [Nat.sub_self, Nat.mul_zero]
  · show 0 * (L + 1 - 0) = 0
    rw [Nat.zero_mul]

/-- The transposed incidence against the profile at a link of the
window, a direction below the count at a site whose coordinate there
sits below the side, at two directions or beyond, the window's
frame, the read refused at one direction (the check module's pin):
at a link in the first direction the profile's step margin along
the second direction at the corner's first parabola, at a link in
the second direction the step margin along the first direction at
the corner's second parabola, the members swapped, and the sum's
unit at a link in a further direction. -/
theorem profCol_read (d L e s' : Nat) (h1 : 1 < d) (he : e < d) (hs' : s' < (L + 1) ^ d)
    (hce : coordAt L e s' < L) :
    (getAt BPair.unit (matVec (transposeM (incid d L)) (profile d L)) (linkKey d L e s')).oneValue
      (if e == 0 then
        BPair.ofCounts (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s' + 1))
          (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s'))
      else if e == 1 then
        BPair.ofCounts (wAt L (coordAt L 0 s') * wAt L (coordAt L 1 s' + 1))
          (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s' + 1))
      else BPair.unit) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  refine BPair.oneValue_trans (colRead_planes d L e s' he hs' hce (profAt L)) ?_
  match e, he, hce with
  | 0, _, hce =>
    -- the planes through the first direction: the first two directions' plane alone
    refine BPair.oneValue_trans (BPair.add_congr (bsum_range_pick _ 1 d h1 (fun k _ hk1 => ?_))
      (foldB_nullRange _ d (fun a _ => ?_))) ?_
    · refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      rw [profAt_off L (0, k, s') (fun h => hk1 (show k = 1 from h.2)),
        profAt_off L (0, k, s' - (L + 1) ^ k) (fun h => hk1 (show k = 1 from h.2)),
        show BPair.unit.swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
      exact BPair.unit_add _
    · rw [decide_eq_false (Nat.not_lt_zero a), iteB_false]
      exact BPair.oneValue_refl _
    rw [if_pos (decide_eq_true Nat.zero_lt_one)]
    refine BPair.oneValue_trans (BPair.add_unit _) ?_
    show ((if decide (coordAt L 1 s' < L) = true then
        BPair.ofNat (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s' + 1)) else BPair.unit)
      + (if 0 < coordAt L 1 s' then
        (BPair.ofNat (wAt L (coordAt L 0 (s' - (L + 1) ^ 1) + 1)
          * wAt L (coordAt L 1 (s' - (L + 1) ^ 1) + 1))).swap else BPair.unit)).oneValue
      (BPair.ofNat (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s' + 1))
        + (BPair.ofNat (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s'))).swap)
    refine BPair.add_congr ?_ ?_
    · -- the base link's own plaquette
      cases Nat.lt_or_ge (coordAt L 1 s') L with
      | inl hc1 =>
        rw [if_pos (decide_eq_true hc1)]
        exact BPair.oneValue_refl _
      | inr hc1 =>
        have hc1' : coordAt L 1 s' = L :=
          Nat.le_antisymm (Nat.le_of_lt_succ (baseDigit_lt (L + 1) 1 s' hL)) hc1
        rw [if_neg (fun h => absurd (of_decide_eq_true h) (Nat.not_lt_of_ge hc1)), hc1',
          (wAt_ends L).1, Nat.mul_zero]
        exact BPair.oneValue_symm BPair.ofNat_zero
    · -- the plaquette below along the second direction
      cases Nat.eq_zero_or_pos (coordAt L 1 s') with
      | inl hz =>
        rw [if_neg (by rw [hz]; exact Nat.lt_irrefl 0), hz, (wAt_ends L).2, Nat.mul_zero]
        exact BPair.oneValue_symm (swap_congr BPair.ofNat_zero)
      | inr hpos =>
        obtain ⟨_, hd1, hoff⟩ := stepBack (L + 1) 1 s' hL hpos
        have hc0 : coordAt L 0 (s' - (L + 1) ^ 1) = coordAt L 0 s' :=
          hoff 0 (fun h => Nat.noConfusion h)
        have hd1' : coordAt L 1 (s' - (L + 1) ^ 1) + 1 = coordAt L 1 s' := hd1
        rw [if_pos hpos, hc0, hd1']
        exact BPair.oneValue_refl _
  | 1, _, hce =>
    -- the planes through the second direction: the first two directions' plane at the
    -- lower direction alone
    refine BPair.oneValue_trans (BPair.add_congr (foldB_nullRange _ d (fun k _ => ?_))
      (bsum_range_pick _ 0 d (Nat.lt_trans Nat.zero_lt_one h1) (fun a _ ha0 => ?_))) ?_
    · refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      rw [profAt_off L (1, k, s') (fun h => Nat.noConfusion h.1),
        profAt_off L (1, k, s' - (L + 1) ^ k) (fun h => Nat.noConfusion h.1),
        show BPair.unit.swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
      exact BPair.unit_add _
    · refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      rw [profAt_off L (a, 1, s' - (L + 1) ^ a) (fun h => ha0 h.1),
        profAt_off L (a, 1, s') (fun h => ha0 h.1),
        show BPair.unit.swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
      exact BPair.unit_add _
    rw [if_pos (decide_eq_true Nat.zero_lt_one)]
    refine BPair.oneValue_trans (BPair.unit_add _) ?_
    show ((if 0 < coordAt L 0 s' then
        BPair.ofNat (wAt L (coordAt L 0 (s' - (L + 1) ^ 0) + 1)
          * wAt L (coordAt L 1 (s' - (L + 1) ^ 0) + 1)) else BPair.unit)
      + (if decide (coordAt L 0 s' < L) = true then
        (BPair.ofNat (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s' + 1))).swap
        else BPair.unit)).oneValue
      (BPair.ofNat (wAt L (coordAt L 0 s') * wAt L (coordAt L 1 s' + 1))
        + (BPair.ofNat (wAt L (coordAt L 0 s' + 1) * wAt L (coordAt L 1 s' + 1))).swap)
    refine BPair.add_congr ?_ ?_
    · -- the plaquette behind along the first direction
      cases Nat.eq_zero_or_pos (coordAt L 0 s') with
      | inl hz =>
        rw [if_neg (by rw [hz]; exact Nat.lt_irrefl 0), hz, (wAt_ends L).2, Nat.zero_mul]
        exact BPair.oneValue_symm BPair.ofNat_zero
      | inr hpos =>
        obtain ⟨_, hd0, hoff⟩ := stepBack (L + 1) 0 s' hL hpos
        have hc1 : coordAt L 1 (s' - (L + 1) ^ 0) = coordAt L 1 s' :=
          hoff 1 (fun h => Nat.noConfusion h)
        have hd0' : coordAt L 0 (s' - (L + 1) ^ 0) + 1 = coordAt L 0 s' := hd0
        rw [if_pos hpos, hc1, hd0']
        exact BPair.oneValue_refl _
    · -- the corner's own plaquette, backward
      cases Nat.lt_or_ge (coordAt L 0 s') L with
      | inl hc0 =>
        rw [if_pos (decide_eq_true hc0)]
        exact BPair.oneValue_refl _
      | inr hc0 =>
        have hc0' : coordAt L 0 s' = L :=
          Nat.le_antisymm (Nat.le_of_lt_succ (baseDigit_lt (L + 1) 0 s' hL)) hc0
        rw [if_neg (fun h => absurd (of_decide_eq_true h) (Nat.not_lt_of_ge hc0)), hc0',
          (wAt_ends L).1, Nat.zero_mul]
        exact BPair.oneValue_symm (swap_congr BPair.ofNat_zero)
  | k + 2, _, _ =>
    -- a further direction: every plane through it sits off the first two directions' plane
    show (bsum (fun k' => if decide (k + 2 < k') then
        (if decide (coordAt L k' s' < L) then profAt L (k + 2, k', s') else BPair.unit)
        + (if 0 < coordAt L k' s' then (profAt L (k + 2, k', s' - (L + 1) ^ k')).swap
          else BPair.unit) else BPair.unit) (List.range d)
      + bsum (fun a => if decide (a < k + 2) then
        (if 0 < coordAt L a s' then profAt L (a, k + 2, s' - (L + 1) ^ a) else BPair.unit)
        + (if decide (coordAt L a s' < L) then (profAt L (a, k + 2, s')).swap else BPair.unit)
        else BPair.unit) (List.range d)).oneValue BPair.unit
    refine BPair.add_units (foldB_nullRange _ d (fun k' _ => ?_)) (foldB_nullRange _ d (fun a _ => ?_))
    · refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      rw [profAt_off L (k + 2, k', s') (fun h => Nat.noConfusion h.1),
        profAt_off L (k + 2, k', s' - (L + 1) ^ k') (fun h => Nat.noConfusion h.1),
        show BPair.unit.swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
      exact BPair.unit_add _
    · refine BPair.oneValue_trans (ite_congr_prop (A' := BPair.unit) _ (fun _ => ?_))
        (BPair.oneValue_of_eq (ite_prop_unit _))
      rw [profAt_off L (a, k + 2, s' - (L + 1) ^ a) (fun h => Nat.noConfusion (show k + 2 = 1 from h.2) (fun h' => Nat.noConfusion h')),
        profAt_off L (a, k + 2, s') (fun h => Nat.noConfusion (show k + 2 = 1 from h.2) (fun h' => Nat.noConfusion h')),
        show BPair.unit.swap = BPair.unit from rfl, ite_prop_unit, ite_prop_unit]
      exact BPair.unit_add _

/-- The plane's squares fold: the guarded double fold of the
parabolas' products' squares is the parabola's squares' sum
squared. -/
private theorem planeSq_fold (L : Nat) :
    famFold Nat.add 0 (fun y => if decide (y < L) = true then
      famFold Nat.add 0 (fun x => if decide (x < L) = true then
        (wAt L (x + 1) * wAt L (y + 1)) * (wAt L (x + 1) * wAt L (y + 1)) else 0)
        (List.range (L + 1)) else 0) (List.range (L + 1))
    = famFold Nat.add 0 (fun j => wAt L (j + 1) * wAt L (j + 1)) (List.range L)
      * famFold Nat.add 0 (fun j => wAt L (j + 1) * wAt L (j + 1)) (List.range L) := by
  rw [famFold_range_lt, ← famFold_mulR]
  refine famFold_congr_members Nat.add 0 _ _ (List.range L) (fun y _ => ?_)
  rw [famFold_range_lt, famFold_mul]
  refine famFold_congr_members Nat.add 0 _ _ (List.range L) (fun x _ => ?_)
  exact polEq [wAt L (x + 1), wAt L (y + 1)]
    (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))))
    (Pol.mul (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))))
    (by decide +kernel)

/-- The plane's first-direction fold: the guarded double fold at a
first-coordinate read against a second-coordinate read is the two
folds' product. -/
private theorem planeMode_fold (L : Nat) (a m : Nat → Nat) :
    famFold Nat.add 0 (fun y => if true = true then
      famFold Nat.add 0 (fun x => if decide (x < L) = true then a x * m y else 0)
        (List.range (L + 1)) else 0) (List.range (L + 1))
    = famFold Nat.add 0 a (List.range L) * famFold Nat.add 0 m (List.range (L + 1)) := by
  rw [famFold_mul]
  refine famFold_congr_members Nat.add 0 _ _ (List.range (L + 1)) (fun y _ => ?_)
  rw [if_pos rfl, famFold_range_lt, famFold_mulR]

/-- The plane's second-direction fold: the guarded double fold at a
second-coordinate read against a first-coordinate read is the two
folds' product. -/
private theorem planeMode_fold' (L : Nat) (a m : Nat → Nat) :
    famFold Nat.add 0 (fun y => if decide (y < L) = true then
      famFold Nat.add 0 (fun x => if true = true then a y * m x else 0)
        (List.range (L + 1)) else 0) (List.range (L + 1))
    = famFold Nat.add 0 a (List.range L) * famFold Nat.add 0 m (List.range (L + 1)) := by
  rw [famFold_range_lt, ← famFold_mulR]
  refine famFold_congr_members Nat.add 0 _ _ (List.range L) (fun y _ => ?_)
  rw [famFold_mul]
  refine famFold_congr_members Nat.add 0 _ _ (List.range (L + 1)) (fun x _ => ?_)
  rw [if_pos rfl]

/-- The profile's self-pairing at every window of two directions or
beyond, `h` the further directions' count: the parabola's squares'
sum squared against the further directions' count. -/
theorem profSelf_read (h L : Nat) :
    (dotN (profile (h + 2) L) (profile (h + 2) L)).oneValue
      (BPair.ofNat ((L + 1) ^ h
        * (ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
          * ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))))) := by
  have hL : 0 < L + 1 := Nat.succ_pos L
  have h1 : 1 < h + 2 := Nat.succ_lt_succ (Nat.succ_pos h)
  have hW := profile_length (h + 2) L
  refine BPair.oneValue_trans (dotN_read _ _) ?_
  rw [dotP_fold (plaqCount (h + 2) L) _ _ hW hW,
    show profile (h + 2) L = (plaqList (h + 2) L).map (profAt L) from rfl]
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun p =>
    profAt L (getAt (0, 0, 0) (plaqList (h + 2) L) p)
      * profAt L (getAt (0, 0, 0) (plaqList (h + 2) L) p)) _ (fun p hp => by
    rw [getAt_map (0, 0, 0) BPair.unit (profAt L) _ p hp]
    exact BPair.oneValue_refl _)) ?_
  rw [bsum_plaq_places (h + 2) L (fun q => profAt L q * profAt L q)]
  refine BPair.oneValue_trans (bsum_plaq_plane (h + 2) L h1 _ (fun q _ hoff => by
    rw [profAt_off L q hoff]
    exact BPair.unit_mul _)) ?_
  refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s =>
    if decide (coordAt L 0 s < L) && decide (coordAt L 1 s < L) then
      BPair.ofNat ((wAt L (coordAt L 0 s + 1) * wAt L (coordAt L 1 s + 1))
        * (wAt L (coordAt L 0 s + 1) * wAt L (coordAt L 1 s + 1)))
    else BPair.unit) _ (fun s _ => ?_)) ?_
  · cases hP : (decide (coordAt L 0 s < L) && decide (coordAt L 1 s < L)) with
    | true => exact BPair.oneValue_symm (BPair.ofNat_mul _ _)
    | false => exact BPair.oneValue_refl _
  refine BPair.oneValue_trans (bsum_box_two_ofNat (L + 1) hL (fun x => decide (x < L))
    (fun y => decide (y < L)) (fun x y => (wAt L (x + 1) * wAt L (y + 1))
      * (wAt L (x + 1) * wAt L (y + 1))) h) ?_
  refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
  rw [sumMap]
  exact congrArg ((L + 1) ^ h * ·) (planeSq_fold L)

/-- The transposed incidence against the profile, its self-pairing
at every window of two directions or beyond, `h` the further
directions' count: the two directions' consecutive differences'
folds, each the parabola's squares' sum against the margins'
squares' sum at the further directions' count. -/
theorem profGram_read (h L : Nat) :
    (dotN (matVec (transposeM (incid (h + 2) L)) (profile (h + 2) L))
      (matVec (transposeM (incid (h + 2) L)) (profile (h + 2) L))).oneValue
      (BPair.ofNat ((L + 1) ^ h
        * (ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
          * ground.sumNat ((List.range (L + 1)).map (fun b =>
              marg (wAt L (b + 1)) (wAt L b) ^ 2)))
        + (L + 1) ^ h
        * (ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
          * ground.sumNat ((List.range (L + 1)).map (fun b =>
              marg (wAt L (b + 1)) (wAt L b) ^ 2))))) := by
  have hb : 0 < L + 1 := Nat.succ_pos L
  have h1 : 1 < h + 2 := Nat.succ_lt_succ (Nat.succ_pos h)
  have h0 : 0 < h + 2 := Nat.succ_pos _
  have hK := incid_rows (h + 2) L
  -- the incidence occupied at a positive side, and the read at the side nought
  have hsplit : 0 < (incid (h + 2) L).length ∨ L = 0 := by
    cases L with
    | zero => exact Or.inr rfl
    | succ L' =>
      refine Or.inl ?_
      rw [incid_length]
      have hb' : 0 < L' + 1 + 1 := Nat.succ_pos _
      have hm : (0, 1, 0) ∈ plaqList (h + 2) (L' + 1) :=
        plaq_mem (h + 2) (L' + 1) 0 1 0 Nat.zero_lt_one h1 (Nat.pow_pos hb')
          (by rw [show coordAt (L' + 1) 0 0 = 0 from
                baseDigit_of_lt (L' + 1 + 1) 0 0 hb' (Nat.pow_pos hb')]
              exact Nat.succ_pos L')
          (by rw [show coordAt (L' + 1) 1 0 = 0 from
                baseDigit_of_lt (L' + 1 + 1) 1 0 hb' (Nat.pow_pos hb')]
              exact Nat.succ_pos L')
      show 0 < (plaqList (h + 2) (L' + 1)).length
      cases hp : plaqList (h + 2) (L' + 1) with
      | nil => rw [hp] at hm; exact nomatch hm
      | cons _ _ => exact Nat.succ_pos _
  cases hsplit with
  | inr hL0 =>
    subst hL0
    have hp : plaqList (h + 2) 0 = [] := plaqList_side_zero (h + 2)
    have hi : incid (h + 2) 0 = [] := by
      show ((plaqList (h + 2) 0).map _).map _ = []
      rw [hp]
      rfl
    have hpr : profile (h + 2) 0 = [] := by
      show (plaqList (h + 2) 0).map (profAt 0) = []
      rw [hp]
      rfl
    rw [hi, hpr, show ground.sumNat ((List.range 0).map (fun j => wAt 0 (j + 1) * wAt 0 (j + 1)))
      = 0 from rfl, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    exact BPair.oneValue_refl _
  | inl hpos =>
    have hy : (matVec (transposeM (incid (h + 2) L)) (profile (h + 2) L)).length
        = linkCount (h + 2) L := by
      rw [matVec_length, length_transposeM _ hK hpos]
    refine BPair.oneValue_trans (dotN_read _ _) ?_
    rw [dotP_fold (linkCount (h + 2) L) _ _ hy hy]
    -- the fold over the link keys as the fold over the links
    have hre : ∀ G : Nat → BPair, (bsum G (List.range (linkCount (h + 2) L))).oneValue
        (bsum (fun e => bsum (fun s => if coordAt L e s < L then G (linkKey (h + 2) L e s)
          else BPair.unit) (List.range ((L + 1) ^ (h + 2)))) (List.range (h + 2))) := by
      intro G
      refine BPair.oneValue_trans (bsum_congr_range_ov G (fun l => G (linkKey (h + 2) L
        (getAt (0, 0) (linkList (h + 2) L) l).1 (getAt (0, 0) (linkList (h + 2) L) l).2)) _
        (fun l hl => by
          rw [linkKey_of_getAt (h + 2) L l hl]
          exact BPair.oneValue_refl _)) ?_
      rw [bsum_link_places (h + 2) L (fun x => G (linkKey (h + 2) L x.1 x.2))]
      exact bsum_link_sites (h + 2) L _
    refine BPair.oneValue_trans (hre _) ?_
    -- the further directions' columns read the unit
    refine BPair.oneValue_trans (bsum_range_prefix _ 2 (h + 2) (Nat.le_add_left 2 h)
      (fun e he2 hed => ?_)) ?_
    · refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun _ => BPair.unit) _
        (fun s hs => ?_)) (famFold_unit_ov bpairFoldLaws _ (fun _ => BPair.oneValue_refl _) _)
      by_cases hc : coordAt L e s < L
      · rw [if_pos hc]
        have hcol := profCol_read (h + 2) L e s h1 hed hs hc
        have hne0 : ¬ e = 0 := fun h => by
          rw [h] at he2
          exact absurd he2 (by decide)
        have hne1 : ¬ e = 1 := fun h => by
          rw [h] at he2
          exact absurd he2 (by decide)
        rw [neBeqOf hne0, neBeqOf hne1, if_neg (fun hc => Bool.noConfusion hc),
          if_neg (fun hc => Bool.noConfusion hc)] at hcol
        exact BPair.oneValue_trans (BPair.mul_congr hcol hcol) (BPair.unit_mul _)
      · rw [if_neg hc]
        exact BPair.oneValue_refl _
    -- the first direction's column
    have hY0 : (bsum (fun s => if coordAt L 0 s < L then
        getAt BPair.unit (matVec (transposeM (incid (h + 2) L)) (profile (h + 2) L))
          (linkKey (h + 2) L 0 s)
        * getAt BPair.unit (matVec (transposeM (incid (h + 2) L)) (profile (h + 2) L))
          (linkKey (h + 2) L 0 s) else BPair.unit) (List.range ((L + 1) ^ (h + 2)))).oneValue
        (BPair.ofNat ((L + 1) ^ h
          * (famFold Nat.add 0 (fun j => wAt L (j + 1) * wAt L (j + 1)) (List.range L)
            * famFold Nat.add 0 (fun b => marg (wAt L (b + 1)) (wAt L b) ^ 2)
              (List.range (L + 1))))) := by
      refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s =>
        if decide (coordAt L 0 s < L) && true then
          BPair.ofNat ((wAt L (coordAt L 0 s + 1) * wAt L (coordAt L 0 s + 1))
            * marg (wAt L (coordAt L 1 s + 1)) (wAt L (coordAt L 1 s)) ^ 2)
        else BPair.unit) _ (fun s hs => ?_)) ?_
      · by_cases hc : coordAt L 0 s < L
        · rw [if_pos hc, decide_eq_true hc]
          have hcol : (getAt BPair.unit (matVec (transposeM (incid (h + 2) L))
              (profile (h + 2) L)) (linkKey (h + 2) L 0 s)).oneValue
              (BPair.ofCounts (wAt L (coordAt L 0 s + 1) * wAt L (coordAt L 1 s + 1))
                (wAt L (coordAt L 0 s + 1) * wAt L (coordAt L 1 s))) :=
            profCol_read (h + 2) L 0 s h1 h0 hs hc
          refine BPair.oneValue_trans (BPair.mul_congr hcol hcol) ?_
          refine BPair.oneValue_trans (BPair.oneValue_symm (margSq_read _ _)) ?_
          refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
          rw [marg_mul_left, sqRead, sqRead]
          exact polEq [wAt L (coordAt L 0 s + 1), marg (wAt L (coordAt L 1 s + 1)) (wAt L (coordAt L 1 s))]
            (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))))
            (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))
            (by decide +kernel)
        · rw [if_neg hc, decide_eq_false hc]
          exact BPair.oneValue_refl _
      refine BPair.oneValue_trans (bsum_box_two_ofNat (L + 1) hb (fun x => decide (x < L))
        (fun _ => true) (fun x y => (wAt L (x + 1) * wAt L (x + 1))
          * marg (wAt L (y + 1)) (wAt L y) ^ 2) h) ?_
      refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
      exact congrArg ((L + 1) ^ h * ·) (planeMode_fold L _ _)
    -- the second direction's column
    have hY1 : (bsum (fun s => if coordAt L 1 s < L then
        getAt BPair.unit (matVec (transposeM (incid (h + 2) L)) (profile (h + 2) L))
          (linkKey (h + 2) L 1 s)
        * getAt BPair.unit (matVec (transposeM (incid (h + 2) L)) (profile (h + 2) L))
          (linkKey (h + 2) L 1 s) else BPair.unit) (List.range ((L + 1) ^ (h + 2)))).oneValue
        (BPair.ofNat ((L + 1) ^ h
          * (famFold Nat.add 0 (fun j => wAt L (j + 1) * wAt L (j + 1)) (List.range L)
            * famFold Nat.add 0 (fun b => marg (wAt L (b + 1)) (wAt L b) ^ 2)
              (List.range (L + 1))))) := by
      refine BPair.oneValue_trans (bsum_congr_range_ov _ (fun s =>
        if true && decide (coordAt L 1 s < L) then
          BPair.ofNat ((wAt L (coordAt L 1 s + 1) * wAt L (coordAt L 1 s + 1))
            * marg (wAt L (coordAt L 0 s + 1)) (wAt L (coordAt L 0 s)) ^ 2)
        else BPair.unit) _ (fun s hs => ?_)) ?_
      · by_cases hc : coordAt L 1 s < L
        · rw [if_pos hc, decide_eq_true hc]
          have hcol : (getAt BPair.unit (matVec (transposeM (incid (h + 2) L))
              (profile (h + 2) L)) (linkKey (h + 2) L 1 s)).oneValue
              (BPair.ofCounts (wAt L (coordAt L 0 s) * wAt L (coordAt L 1 s + 1))
                (wAt L (coordAt L 0 s + 1) * wAt L (coordAt L 1 s + 1))) :=
            profCol_read (h + 2) L 1 s h1 h1 hs hc
          refine BPair.oneValue_trans (BPair.mul_congr hcol hcol) ?_
          refine BPair.oneValue_trans (BPair.oneValue_symm (margSq_read _ _)) ?_
          refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
          rw [Nat.mul_comm (wAt L (coordAt L 0 s)) (wAt L (coordAt L 1 s + 1)),
            Nat.mul_comm (wAt L (coordAt L 0 s + 1)) (wAt L (coordAt L 1 s + 1)),
            marg_mul_left, margComm (wAt L (coordAt L 0 s)), sqRead, sqRead]
          exact polEq [wAt L (coordAt L 1 s + 1), marg (wAt L (coordAt L 0 s + 1)) (wAt L (coordAt L 0 s))]
            (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 1))))
            (Pol.mul (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mon (Mon.var 0))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))
            (by decide +kernel)
        · rw [if_neg hc, decide_eq_false hc]
          exact BPair.oneValue_refl _
      refine BPair.oneValue_trans (bsum_box_two_ofNat (L + 1) hb (fun _ => true)
        (fun y => decide (y < L)) (fun x y => (wAt L (y + 1) * wAt L (y + 1))
          * marg (wAt L (x + 1)) (wAt L x) ^ 2) h) ?_
      refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
      exact congrArg ((L + 1) ^ h * ·) (planeMode_fold' L _ _)
    -- the two columns' folds join
    refine BPair.oneValue_trans (foldB_range_snoc _ 1) ?_
    refine BPair.oneValue_trans (BPair.add_congr (foldB_range_snoc _ 0) (BPair.oneValue_refl _)) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.add_congr (BPair.oneValue_refl _) hY0)
      hY1) ?_
    refine BPair.oneValue_trans (BPair.add_congr (BPair.unit_add _) (BPair.oneValue_refl _)) ?_
    rw [sumMap, sumMap]
    exact BPair.oneValue_symm (BPair.ofNat_add _ _)

/-- The mode read's identity in the side: at the two closed sums,
`(L² + 2L + 2) · 2 (L + 1)^h S₂ S_d = 20 (L + 1)^h S₂²`. -/
private theorem modeIdentity (L h : Nat) :
    (L * L + 2 * L + 2) * ((L + 1) ^ h
        * (ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
          * ground.sumNat ((List.range (L + 1)).map (fun b =>
              marg (wAt L (b + 1)) (wAt L b) ^ 2)))
        + (L + 1) ^ h
        * (ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
          * ground.sumNat ((List.range (L + 1)).map (fun b =>
              marg (wAt L (b + 1)) (wAt L b) ^ 2))))
      = 20 * ((L + 1) ^ h
        * (ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1)))
          * ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1))))) := by
  have h30 := profSq_closed L
  have h3 := profDiff_closed L
  generalize hS2 : ground.sumNat ((List.range L).map (fun j => wAt L (j + 1) * wAt L (j + 1))) = S2
    at h30 ⊢
  generalize hSd : ground.sumNat ((List.range (L + 1)).map (fun b =>
    marg (wAt L (b + 1)) (wAt L b) ^ 2)) = Sd at h3 ⊢
  refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos 2) ?_
  have e1 : 3 * ((L * L + 2 * L + 2) * ((L + 1) ^ h * (S2 * Sd) + (L + 1) ^ h * (S2 * Sd)))
      = (L * L + 2 * L + 2) * (2 * (L + 1) ^ h * S2 * (3 * Sd)) :=
    polEq [L * L + 2 * L + 2, (L + 1) ^ h, S2, Sd]
      (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.add (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3)))) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mul (Pol.mon (Mon.var 2)) (Pol.mon (Mon.var 3)))))))
      (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mon (Mon.var 3)))))
      (by decide +kernel)
  rw [e1, h3]
  have e2 : (L * L + 2 * L + 2) * (2 * (L + 1) ^ h * S2 * (L * (L + 1) * (L + 2)))
      = 2 * (L + 1) ^ h * S2 * (L * (L + 1) * (L + 2) * (L * L + 2 * L + 2)) :=
    polEq [L * L + 2 * L + 2, (L + 1) ^ h, S2, L * (L + 1) * (L + 2)]
      (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mon (Mon.var 3))))
      (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 1))) (Pol.mon (Mon.var 2))) (Pol.mul (Pol.mon (Mon.var 3)) (Pol.mon (Mon.var 0))))
      (by decide +kernel)
  rw [e2, ← h30]
  exact polEq [(L + 1) ^ h, S2]
    (Pol.mul (Pol.mul (Pol.mul (Pol.mon (Mon.cst 2)) (Pol.mon (Mon.var 0))) (Pol.mon (Mon.var 1))) (Pol.mul (Pol.mon (Mon.cst 30)) (Pol.mon (Mon.var 1))))
    (Pol.mul (Pol.mon (Mon.cst 3)) (Pol.mul (Pol.mon (Mon.cst 20)) (Pol.mul (Pol.mon (Mon.var 0)) (Pol.mul (Pol.mon (Mon.var 1)) (Pol.mon (Mon.var 1))))))
    (by decide +kernel)

/-- The mode read at every window: `Wᵀ Δ W = e_W Wᵀ W` at
`e_W = [20 : L² + 2L + 2]`, the Gram's form at the profile the two
directions' consecutive differences' folds against the profile's
self-pairing at the two closed sums, and both reads the sum's unit
at one direction or fewer. -/
theorem modeRead_all (d L : Nat) : modeRead d L := by
  match d with
  | 0 =>
    show (BPair.ofNat _ * BPair.unit).oneValue (BPair.ofNat 20 * BPair.unit)
    exact BPair.oneValue_trans (BPair.mul_unit _) (BPair.oneValue_symm (BPair.mul_unit _))
  | 1 =>
    show (BPair.ofNat _ * BPair.unit).oneValue (BPair.ofNat 20 * BPair.unit)
    exact BPair.oneValue_trans (BPair.mul_unit _) (BPair.oneValue_symm (BPair.mul_unit _))
  | h + 2 =>
    have hW : (profile (h + 2) L).length = (incid (h + 2) L).length := by
      rw [incid_length, profile_length]
    show (BPair.ofNat _ * quadForm (matMul (incid (h + 2) L) (transposeM (incid (h + 2) L)))
      (profile (h + 2) L)).oneValue _
    refine BPair.oneValue_trans (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_trans (quadForm_matMulT _ _ (incid_rows (h + 2) L) _ hW)
        (profGram_read h L))) ?_
    refine BPair.oneValue_trans (BPair.oneValue_symm (BPair.ofNat_mul _ _)) ?_
    refine BPair.oneValue_trans ?_ (BPair.mul_congr (BPair.oneValue_refl _)
      (BPair.oneValue_symm (profSelf_read h L)))
    refine BPair.oneValue_trans ?_ (BPair.ofNat_mul 20 _)
    exact BPair.oneValue_of_eq (congrArg BPair.ofNat (modeIdentity L h))

/-! The counts: the comb tree's root paths and the loop regions. -/

/-- A site's root path: the links ascending the directions in their
order, at each direction the links along it from the first position
to the site's coordinate at the site's prefix. -/
def rootPath (d L s : Nat) : List Nat :=
  (List.range d).flatMap (fun e =>
    (List.range (coordAt L e s)).map (fun j =>
      linkKey d L e (prefixAt L e s + j * (L + 1) ^ e)))

/-- The descent's column at a direction beyond a plane direction: the
plaquettes of the two directions' plane at the corner's prefix, one
per position below the corner's coordinate. -/
def descentColumn (d L a e s : Nat) : List Nat :=
  (List.range (coordAt L e s)).map (fun j =>
    plaqKey d L a e (prefixAt L e s + j * (L + 1) ^ e))

/-- A boundary link's loop region at a plaquette: vacant at the two
corner links, and at a far link the columns descended in the
directions beyond the link's moved direction, one column of width
one per descent. -/
def loopRegion (d L : Nat) (p : Nat × Nat × Nat) (i : Nat) : List Nat :=
  if i == 1 then
    (List.range d).flatMap (fun e =>
      if p.1 < e then descentColumn d L p.1 e p.2.2 else [])
  else if i == 2 then
    (List.range d).flatMap (fun e =>
      if p.2.1 < e then descentColumn d L p.2.1 e p.2.2 else [])
  else []

/-- The region's count `n_{ℓp}` at or below `gL` at every plaquette
and boundary link. -/
def regionCapRead (d L : Nat) : Prop :=
  ((plaqList d L).all (fun p => (List.range 4).all (fun i =>
    decide ((loopRegion d L p i).length ≤ dirGap d * L)))) = true

instance instCornerwindow10 (d L : Nat) : Decidable (regionCapRead d L) :=
  inferInstanceAs (Decidable (_ = _))

/-- The regions holding a plaquette, over the plaquettes and their
boundary links. -/
def coverAt (d L q : Nat) : Nat :=
  ground.sumNat ((plaqList d L).map (fun p =>
    ground.sumNat ((List.range 4).map (fun i =>
      if (loopRegion d L p i).any (fun x => x == q) then 1 else 0))))

/-- The cover read: a plaquette sits in at most `[2 : (g + 1) L] #p`
regions. -/
def coverRead (d L : Nat) : Prop :=
  ((List.range (plaqCount d L)).all (fun q =>
    decide ((dirGap d + 1) * L * coverAt d L q ≤ 2 * plaqCount d L))) = true

instance instCornerwindow11 (d L : Nat) : Decidable (coverRead d L) :=
  inferInstanceAs (Decidable (_ = _))

/-- The regions' counts folded over the pairs whose region holds a
stated plaquette. -/
def regionFold (d L q : Nat) : Nat :=
  ground.sumNat ((plaqList d L).map (fun p =>
    ground.sumNat ((List.range 4).map (fun i =>
      if (loopRegion d L p i).any (fun x => x == q) then (loopRegion d L p i).length
      else 0))))

/-- The regions' counts fold to at most `[2g : g + 1] #p` over the
pairs whose region holds one plaquette, at every plaquette. -/
def regionSumRead (d L : Nat) : Prop :=
  ((List.range (plaqCount d L)).all (fun q =>
    decide ((dirGap d + 1) * regionFold d L q ≤ 2 * dirGap d * plaqCount d L))) = true

instance instCornerwindow12 (d L : Nat) : Decidable (regionSumRead d L) :=
  inferInstanceAs (Decidable (_ = _))

end cornerwindow
