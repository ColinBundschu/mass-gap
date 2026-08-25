import MassGap.Places
import MassGap.Elim
/-!
`con:units` — the matrix units act on the power by the Leibniz sum,
one summand per place: `E_{ij}` re-reads each place holding letter
`j` at letter `i`.  On a monomial basis the action is a matrix of
counts, and the commutator table
`[E_{ab}, E_{cd}] + δ_{da} E_{cb} = δ_{bc} E_{ad}` reads as matrix
identities on the power, the check module's instances.  A raising
`E_{i,i+1}` moves the content one letter-pair step up the dominance
order; the stacked adjacent raisings at a content are the block
count's elimination datum (`def:blockcount`).  The table is proven
at the monomial level (`act_comm`): the two composed Leibniz
actions' output counts differ by the contraction reads at every
target monomial, the δ-conditions spelled in the orders the
expansions produce.  The matrix tier reads the counts through the
content bases: the entry characterization (`matUnitAt_read`, the
entry the Leibniz count at the row's monomial through the scatter
at the arithmetic rank), the transpose read `E_{ij}ᵀ = E_{ji}` at
the monomial pairing (`countOf_unitAct_swap`), and the grading's
diagonal (`countOf_unitAct_diag`).  The scatter's guard is the
target content's own read — the output's degree and occupancy
family against `muTo`, `places.countOf_monomialsAt` the enumeration
carrying the equal count — so the column fold decides an output's
membership at the content datum and never at the enumeration it
would have to build; where no output of any source monomial meets
that read the compression is the null map
(`matUnitAt_null_offcontent`, every column at its seed).
The composed actions' counts convolve over the moved content's
enumeration (`countOf_unitAct_comp`, the matrix product's own read
through the collect-by-count fold), and the matrix tier's lifts of
`act_comm` are landed at stated enumerations with the content
hypotheses the output kit discharges: the composed product's read
(`matUnit_comp_read`), the single unit as the composites' crossed
join (`matVec_comm_read`, the gap descent's read), the table's own
join uniform (`matVec_table_read`, `act_comm` lifted to the
coordinate vectors with the two delta terms guarded by their
letters' coincidence, each guard's content hypothesis taken only
where it fires — the two reads below are its dead- and live-delta
instances), the disjoint
pairs' exchange (`matVec_swap_read`) and the adjacent pair's
`[E,F] = H` exchange at the crossed diagonal scalars
(`matVec_pair_read`), the grading's scalar action
(`matVec_diag_read`) and the transpose's letter exchange
(`matUnit_transpose_read`) — `lem:lowerspan`'s closure their first
consumer, with `lem:strings`' sl2 pairs and `lem:casimir`'s
commutation the arrivals.  The action's own letter reads sit
beside them: the consumed letter missed at a head
(`unitAct_cons_miss`), the vacant action at an unoccupied letter
(`unitAct_nil_of_zero`), and the unit matrix's null action there
(`matVec_null_unocc`).
-/

namespace units
open ground places

/-- The Leibniz action of `E_{ij}` on a monomial: one output per
place reading `j`, that place re-read at `i`. -/
def unitAct (i j : Nat) : List Nat → List (List Nat)
  | [] => []
  | a :: t =>
    (if a == j then [i :: t] else [])
      ++ (unitAct i j t).map (fun m => a :: m)

/-- The unit's matrix between stated monomial bases: the entry at a
target and a source the count of Leibniz summands reading the
target. -/
def matUnit (tgt src : List (List Nat)) (i j : Nat) : elim.Mat :=
  tgt.map (fun t => src.map (fun s =>
    BPair.ofNat (ground.countOf t (unitAct i j s))))

/-- The scatter at a key: the read added into a coordinate list. -/
def scatterAt : Nat → BPair → List BPair → List BPair
  | _, _, [] => []
  | 0, x, a :: t => (a + x) :: t
  | n + 1, x, a :: t => a :: scatterAt n x t

/-- The unit's matrix between content bases at the arithmetic rank:
one scatter per Leibniz summand, the columns transposed onto the
row keys.  The summand's guard is the target content's own read —
the degree and the occupancy family (`places.countOf_monomialsAt`
the enumeration's equal count) — so an output off the target's
basis contributes nothing: the compression between two contents the
action does not connect is the null map, `con:units`' grading. -/
def matUnitAt (muTo muFrom : List Nat) (i j : Nat) : elim.Mat :=
  elim.transposeM ((monomialsAt muFrom).map (fun s =>
    (unitAct i j s).foldl
      (fun col m =>
        if m.length = sumNat muTo ∧ content muTo.length m = muTo then
          scatterAt (rankOf m muTo) (BPair.ofNat 1) col
        else col)
      ((monomialsAt muTo).map (fun _ => BPair.unit))))

/-- The letter-pair move up at an adjacent place pair: the count at
`i` raised by one, the count at `i+1` lowered by one. -/
def moveUp (i : Nat) : List Nat → List Nat
  | [] => []
  | a :: t =>
    match i with
    | 0 =>
      match t with
      | [] => [a + 1]
      | b :: t' => (a + 1) :: (b - 1) :: t'
    | n + 1 => a :: moveUp n t

/-- The letter-pair move down at an adjacent place pair: the count
at `i` lowered by one, the count at `i+1` raised by one. -/
def moveDn (i : Nat) : List Nat → List Nat
  | [] => []
  | a :: t =>
    match i with
    | 0 =>
      match t with
      | [] => [a - 1]
      | b :: t' => (a - 1) :: (b + 1) :: t'
    | n + 1 => a :: moveDn n t

/-- The adjacent lowering keeps the content's total at an occupied
letter inside the width. -/
theorem sumNat_moveDn : ∀ (j : Nat) (mu : List Nat),
    j + 1 < mu.length → 0 < ground.getAt 0 mu j →
    ground.sumNat (moveDn j mu) = ground.sumNat mu
  | 0, [], h, _ => absurd h (Nat.not_lt_zero 1)
  | 0, [_], h, _ => absurd h (Nat.lt_irrefl 1)
  | 0, a :: b :: t, _, hocc => by
    show a - 1 + (b + 1 + ground.sumNat t)
      = a + (b + ground.sumNat t)
    rw [← Nat.add_assoc (a - 1) (b + 1) (ground.sumNat t),
      ground.subOneJoin a b hocc,
      Nat.add_assoc a b (ground.sumNat t)]
  | j + 1, [], h, _ => absurd h (Nat.not_lt_zero (j + 2))
  | j + 1, c :: t, h, hocc => by
    show c + ground.sumNat (moveDn j t) = c + ground.sumNat t
    rw [sumNat_moveDn j t (Nat.lt_of_succ_lt_succ h) hocc]

/-- The letter-pair move keeps the length. -/
theorem length_moveDn : ∀ (j : Nat) (nu : List Nat),
    (moveDn j nu).length = nu.length
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | j + 1, _ :: t => congrArg Nat.succ (length_moveDn j t)

/-- The adjacent raising keeps the length. -/
theorem length_moveUp : ∀ (j : Nat) (nu : List Nat),
    (moveUp j nu).length = nu.length
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | j + 1, _ :: t => congrArg Nat.succ (length_moveUp j t)

/-- The one-box removals, the covered shapes: a column of length one
dropped, or an occupied column shortened by one — the adjacent
raising's occupancy read at the column multiset, one member per
occupied length. -/
def removals (s : Shape) : List Shape :=
  (match s with
   | [] => []
   | a :: t => if 0 < a then [(a - 1) :: t] else [])
  ++ (List.range (s.length - 1)).flatMap (fun i =>
      if 0 < ground.getAt 0 s (i + 1) then [moveUp i s] else [])

/-- The removal family's count splits at the head: the lowered
head's own member against the fold of the raised deeper keys, the
join's two arms `countOf`-additive. -/
theorem removals_split (b : Nat) (s' : List Nat) (t : Shape) :
    ground.countOf t (removals (b :: s'))
      = ground.countOf t (if 0 < b then [(b - 1) :: s'] else [])
        + ground.famFold Nat.add 0
            (fun j => ground.countOf t
              (if 0 < ground.getAt 0 (b :: s') (j + 1) then
                [moveUp j (b :: s')] else []))
            (List.range s'.length) := by
  show ground.countOf t ((if 0 < b then [(b - 1) :: s'] else [])
      ++ (List.range ((b :: s').length - 1)).flatMap
        (fun i => if 0 < ground.getAt 0 (b :: s') (i + 1) then
          [moveUp i (b :: s')] else [])) = _
  rw [ground.countOf_append, ground.countOf_flatMap]
  rfl

/-- The adjacent raising raises its own key's count. -/
theorem getAt_moveUp_self : ∀ (j : Nat) (nu : List Nat),
    j < nu.length →
    ground.getAt 0 (moveUp j nu) j
      = ground.getAt 0 nu j + 1
  | 0, [], h => absurd h (Nat.lt_irrefl 0)
  | _ + 1, [], h => absurd h (Nat.not_lt_zero _)
  | 0, [_], _ => rfl
  | 0, _ :: _ :: _, _ => rfl
  | j + 1, _ :: t, h =>
    getAt_moveUp_self j t (Nat.lt_of_succ_lt_succ h)

/-- The adjacent raise lowers the successor key's count, the
subtraction saturating at the vacant key. -/
theorem getAt_moveUp_next : ∀ (j : Nat) (s : List Nat),
    ground.getAt 0 (moveUp j s) (j + 1)
      = ground.getAt 0 s (j + 1) - 1
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | j + 1, _ :: t => getAt_moveUp_next j t

/-- The adjacent lowering lowers its own key's count, the
subtraction saturating at the vacant key. -/
theorem getAt_moveDn_self : ∀ (j : Nat) (s : List Nat),
    ground.getAt 0 (moveDn j s) j = ground.getAt 0 s j - 1
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | j + 1, _ :: t => getAt_moveDn_self j t

/-- The adjacent raise keeps every count off its own key and the
successor. -/
theorem getAt_moveUp_ne : ∀ (j : Nat) (s : List Nat) (k : Nat),
    ¬ k = j → ¬ k = j + 1 →
    ground.getAt 0 (moveUp j s) k = ground.getAt 0 s k
  | 0, [], _, _, _ => rfl
  | _ + 1, [], _, _, _ => rfl
  | 0, [_], 0, h0, _ => absurd rfl h0
  | 0, [_], _ + 1, _, _ => rfl
  | 0, _ :: _ :: _, 0, h0, _ => absurd rfl h0
  | 0, _ :: _ :: _, 1, _, h1 => absurd rfl h1
  | 0, _ :: _ :: _, _ + 2, _, _ => rfl
  | _ + 1, _ :: _, 0, _, _ => rfl
  | j + 1, _ :: t, k + 1, h0, h1 =>
    getAt_moveUp_ne j t k (fun he => h0 (congrArg Nat.succ he))
      (fun he => h1 (congrArg Nat.succ he))

/-- The adjacent lowering keeps every count off its own key and the
successor. -/
theorem getAt_moveDn_ne : ∀ (j : Nat) (s : List Nat) (k : Nat),
    ¬ k = j → ¬ k = j + 1 →
    ground.getAt 0 (moveDn j s) k = ground.getAt 0 s k
  | 0, [], _, _, _ => rfl
  | _ + 1, [], _, _, _ => rfl
  | 0, [_], 0, h0, _ => absurd rfl h0
  | 0, [_], _ + 1, _, _ => rfl
  | 0, _ :: _ :: _, 0, h0, _ => absurd rfl h0
  | 0, _ :: _ :: _, 1, _, h1 => absurd rfl h1
  | 0, _ :: _ :: _, _ + 2, _, _ => rfl
  | _ + 1, _ :: _, 0, _, _ => rfl
  | j + 1, _ :: t, k + 1, h0, h1 =>
    getAt_moveDn_ne j t k (fun he => h0 (congrArg Nat.succ he))
      (fun he => h1 (congrArg Nat.succ he))

/-- The adjacent lowering raises the successor key's count. -/
theorem getAt_moveDn_next : ∀ (j : Nat) (nu : List Nat),
    j + 1 < nu.length →
    ground.getAt 0 (moveDn j nu) (j + 1)
      = ground.getAt 0 nu (j + 1) + 1
  | 0, [], h => absurd h (Nat.not_lt_zero 1)
  | 0, [_], h => absurd h (Nat.lt_irrefl 1)
  | 0, _ :: _ :: _, _ => rfl
  | j + 1, [], h => absurd h (Nat.not_lt_zero (j + 2))
  | j + 1, _ :: t, h =>
    getAt_moveDn_next j t (Nat.lt_of_succ_lt_succ h)

/-- The raising reads the lowering back at an occupied key. -/
theorem moveUp_moveDn : ∀ (j : Nat) (nu : List Nat),
    j + 1 < nu.length → 0 < ground.getAt 0 nu j →
    moveUp j (moveDn j nu) = nu
  | 0, [], h, _ => absurd h (Nat.not_lt_zero 1)
  | 0, [_], h, _ => absurd h (Nat.lt_irrefl 1)
  | 0, a :: b :: t, _, ho => by
    have hsub : a - 1 + 1 = a := ground.subAdd ho
    show (a - 1 + 1) :: b :: t = a :: b :: t
    rw [hsub]
  | j + 1, [], h, _ => absurd h (Nat.not_lt_zero (j + 2))
  | j + 1, a :: t, h, ho => by
    show a :: moveUp j (moveDn j t) = a :: t
    rw [moveUp_moveDn j t (Nat.lt_of_succ_lt_succ h) ho]

/-- The lowering reads the raising back at an occupied successor
key. -/
theorem moveDn_moveUp : ∀ (j : Nat) (nu : List Nat),
    j + 1 < nu.length → 0 < ground.getAt 0 nu (j + 1) →
    moveDn j (moveUp j nu) = nu
  | 0, [], h, _ => absurd h (Nat.not_lt_zero 1)
  | 0, [_], h, _ => absurd h (Nat.lt_irrefl 1)
  | 0, a :: b :: t, _, ho => by
    have hsub : b - 1 + 1 = b := ground.subAdd ho
    show a :: (b - 1 + 1) :: t = a :: b :: t
    rw [hsub]
  | j + 1, [], h, _ => absurd h (Nat.not_lt_zero (j + 2))
  | j + 1, a :: t, h, ho => by
    show a :: moveDn j (moveUp j t) = a :: t
    rw [moveDn_moveUp j t (Nat.lt_of_succ_lt_succ h) ho]

/-- The head's raise passes the adjacent raise. -/
theorem bumpAt0_moveUp : ∀ (j : Nat) (s : Shape),
    ground.bumpAt 0 (moveUp j s) = moveUp j (ground.bumpAt 0 s)
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | _ + 1, _ :: _ => rfl


/-- The head's lowering passes the adjacent lowering. -/
theorem dipAt0_moveDn : ∀ (j : Nat) (s : Shape),
    ground.dipAt 0 (moveDn j s) = moveDn j (ground.dipAt 0 s)
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | _ + 1, _ :: _ => rfl

/-- The adjacent raise fixes the vacant list at every key. -/
theorem moveUp_nil : ∀ j : Nat, moveUp j [] = ([] : List Nat)
  | 0 => rfl
  | _ + 1 => rfl

/-- The adjacent lowering fixes the vacant list at every key. -/
theorem moveDn_nil : ∀ j : Nat, moveDn j [] = ([] : List Nat)
  | 0 => rfl
  | _ + 1 => rfl

/-- The adjacent raise and lowering at distinct keys pass each
other. -/
theorem moveUp_moveDn_comm : ∀ (j' j : Nat) (s : List Nat),
    ¬ j' = j →
    moveUp j' (moveDn j s)
      = moveDn j (moveUp j' s)
  | 0, 0, [], _ => rfl
  | 0, _ + 1, [], _ => rfl
  | _ + 1, 0, [], _ => rfl
  | _ + 1, _ + 1, [], _ => rfl
  | 0, 0, _ :: _, hne => absurd rfl hne
  | 0, j + 1, [a], _ => by
    show moveUp 0 (a :: moveDn j [])
      = (a + 1) :: moveDn j []
    rw [moveDn_nil j]
    rfl
  | 0, j + 1, a :: b :: t', _ => by
    have hh : moveDn (j + 1) (moveUp 0 (a :: b :: t'))
        = (a + 1) :: ground.dipAt 0 (moveDn j (b :: t')) := by
      show (a + 1) :: moveDn j (ground.dipAt 0 (b :: t'))
        = (a + 1) :: ground.dipAt 0 (moveDn j (b :: t'))
      rw [dipAt0_moveDn j (b :: t')]
    rw [hh]
    show moveUp 0 (a :: moveDn j (b :: t'))
      = (a + 1) :: ground.dipAt 0 (moveDn j (b :: t'))
    match hu : moveDn j (b :: t') with
    | [] =>
      have hl := units.length_moveDn j (b :: t')
      rw [hu] at hl
      exact Nat.noConfusion hl
    | _ :: _ => rfl
  | j + 1, 0, [a], _ => by
    show (a - 1) :: moveUp j []
      = moveDn 0 (a :: moveUp j [])
    rw [moveUp_nil j]
    rfl
  | j + 1, 0, a :: b :: t', _ => by
    have hh : moveUp (j + 1) (moveDn 0 (a :: b :: t'))
        = (a - 1) :: ground.bumpAt 0 (moveUp j (b :: t')) := by
      show (a - 1) :: moveUp j (ground.bumpAt 0 (b :: t'))
        = (a - 1) :: ground.bumpAt 0 (moveUp j (b :: t'))
      rw [bumpAt0_moveUp j (b :: t')]
    rw [hh]
    show (a - 1) :: ground.bumpAt 0 (moveUp j (b :: t'))
      = moveDn 0 (a :: moveUp j (b :: t'))
    match hu : moveUp j (b :: t') with
    | [] =>
      have hl := units.length_moveUp j (b :: t')
      rw [hu] at hl
      exact Nat.noConfusion hl
    | _ :: _ => rfl
  | j' + 1, j + 1, a :: t, hne =>
    congrArg (List.cons a) (moveUp_moveDn_comm j' j t
      (fun he => hne (congrArg Nat.succ he)))

/-- The head's growth raises the row list at its first key. -/
theorem rowList_grow (a : Nat) (t : List Nat) :
    rowList ((a + 1) :: t) = ground.bumpAt 0 (rowList (a :: t)) := by
  show (a + 1 + sumNat t) :: rowList t
    = (a + sumNat t + 1) :: rowList t
  rw [Nat.add_right_comm a 1 (sumNat t)]

/-- The adjacent lowering at an occupied key raises the row list at
the successor key. -/
theorem rowList_moveDn : ∀ (j : Nat) (s : Shape),
    j + 1 < s.length → 0 < ground.getAt 0 s j →
    rowList (moveDn j s) = ground.bumpAt (j + 1) (rowList s)
  | 0, [], hj, _ => absurd hj (Nat.not_lt_zero 1)
  | 0, [_], hj, _ => absurd hj (Nat.lt_irrefl 1)
  | 0, a :: b :: t, _, ho => by
    show (a - 1 + (b + 1 + sumNat t)) :: (b + 1 + sumNat t) :: rowList t
      = (a + (b + sumNat t)) :: (b + sumNat t + 1) :: rowList t
    rw [← Nat.add_assoc (a - 1) (b + 1) (sumNat t),
      ground.subOneJoin a b ho, Nat.add_assoc a b (sumNat t),
      Nat.add_right_comm b 1 (sumNat t)]
  | j + 1, [], hj, _ => absurd hj (Nat.not_lt_zero (j + 2))
  | j + 1, a :: t, hj, ho => by
    have hjt : j + 1 < t.length := Nat.lt_of_succ_lt_succ hj
    have hot : 0 < ground.getAt 0 t j := ho
    show (a + sumNat (moveDn j t)) :: rowList (moveDn j t)
      = (a + sumNat t) :: ground.bumpAt (j + 1) (rowList t)
    rw [sumNat_moveDn j t hjt hot, rowList_moveDn j t hjt hot]


/-- The adjacent raising at an occupied successor key lowers the
row list at the successor key, the lowering move's own inverse
read. -/
theorem rowList_moveUp (j : Nat) (s : Shape) (hj : j + 1 < s.length)
    (ho : 0 < ground.getAt 0 s (j + 1)) :
    rowList (moveUp j s) = ground.dipAt (j + 1) (rowList s) := by
  have hlen : j + 1 < (moveUp j s).length := by
    rw [length_moveUp]; exact hj
  have hocc : 0 < ground.getAt 0 (moveUp j s) j := by
    rw [getAt_moveUp_self j s (Nat.lt_of_succ_lt hj)]
    exact Nat.succ_pos _
  have hdn : rowList (moveDn j (moveUp j s))
      = ground.bumpAt (j + 1) (rowList (moveUp j s)) :=
    rowList_moveDn j (moveUp j s) hlen hocc
  rw [moveDn_moveUp j s hj ho] at hdn
  rw [hdn, ground.dipAt_bumpAt_self]

/-- The stacked adjacent raisings at a content: rows the raised
contents' monomials per occupied move, columns the content's own,
the block count's elimination datum. -/
def stackedRaise (mu : List Nat) : elim.Mat :=
  (List.range (mu.length - 1)).flatMap (fun i =>
    if 0 < ground.getAt 0 mu (i + 1) then
      matUnitAt (moveUp i mu) mu i (i + 1)
    else [])

/-! The action's letter reads: the consumed letter missed at a
head, and the whole action vacant at an unoccupied letter. -/

/-- The action skips a head that is not the consumed letter: every
output keeps that head and the action runs on the tail. -/
theorem unitAct_cons_miss (i x a : Nat) (t : List Nat)
    (h : ¬ x = a) :
    unitAct i x (a :: t)
      = (unitAct i x t).map (fun m => a :: m) := by
  show ((if a == x then [i :: t] else [])
    ++ (unitAct i x t).map (fun m => a :: m)) = _
  cases hb : a == x with
  | true => exact absurd (ground.beqEqOf hb).symm h
  | false =>
    rw [if_neg (fun hc : (false : Bool) = true =>
      Bool.noConfusion hc)]
    rfl

/-- The action at an unoccupied consumed letter has no output. -/
theorem unitAct_nil_of_zero (i x : Nat) : ∀ t : List Nat,
    ground.countOf x t = 0 → unitAct i x t = []
  | [], _ => rfl
  | a :: t, h => by
    have hxa : ¬ x = a := by
      intro he
      rw [he, ground.countOf_head] at h
      exact Nat.noConfusion h
    have hz : ground.countOf x t = 0 := by
      rw [← ground.countOf_head_ne hxa t]
      exact h
    rw [unitAct_cons_miss i x a t hxa, unitAct_nil_of_zero i x t hz]
    rfl

/-- The consumed letter hit at a head: the head's own output
leads and the tail's outputs keep the head. -/
theorem unitAct_cons_hit (i x a : Nat) (t : List Nat)
    (h : x = a) :
    unitAct i x (a :: t)
      = (i :: t) :: (unitAct i x t).map
        (fun m => a :: m) := by
  show ((if a == x then [i :: t] else [])
    ++ (unitAct i x t).map (fun m => a :: m)) = _
  rw [show (a == x) = true from ground.eqBeqOf h.symm, if_pos rfl]
  rfl

/-- The action splits over a concatenation by the Leibniz read:
the outputs at the first part keep the second whole, and the
outputs at the second keep the first. -/
theorem unitAct_append (i x : Nat) : ∀ (p q : List Nat),
    unitAct i x (p ++ q)
      = (unitAct i x p).map (fun m => m ++ q)
        ++ (unitAct i x q).map (fun m => p ++ m)
  | [], q => by
    show unitAct i x q
      = [] ++ (unitAct i x q).map (fun m => [] ++ m)
    rw [ground.map_congr_all (fun m => ([] : List Nat) ++ m)
        (fun m => m) (fun _ => rfl) (unitAct i x q),
      ground.map_id]
    rfl
  | a :: p, q => by
    by_cases hxa : x = a
    · rw [show (a :: p) ++ q = a :: (p ++ q) from rfl,
        unitAct_cons_hit i x a (p ++ q) hxa,
        unitAct_cons_hit i x a p hxa]
      show (i :: (p ++ q))
          :: (unitAct i x (p ++ q)).map (fun m => a :: m)
        = ((((i :: p) ++ q)
            :: ((unitAct i x p).map (fun m => a :: m)).map
              (fun m => m ++ q))
          ++ (unitAct i x q).map (fun m => (a :: p) ++ m))
      rw [unitAct_append i x p q, ground.map_append,
        ground.map_map, ground.map_map, ground.map_map]
      rfl
    · rw [show (a :: p) ++ q = a :: (p ++ q) from rfl,
        unitAct_cons_miss i x a (p ++ q) hxa,
        unitAct_cons_miss i x a p hxa,
        unitAct_append i x p q, ground.map_append,
        ground.map_map, ground.map_map, ground.map_map]
      rfl

/-! The commutator table at the monomial level
(`con:units`' display): the composed Leibniz actions' output
counts differ by the contraction reads,
`[E_{ab}, E_{cd}] + δ_{da} E_{cb} = δ_{bc} E_{ad}`, one count
identity per target monomial — the matrix tier reads it through
the content bases. -/

private theorem if_cons_gen (y a : Nat) (u' m' : List Nat)
    (x : Nat) :
    (if (y :: u' : List Nat) = a :: m' then x else 0)
      = if y = a then (if u' = m' then x else 0) else 0 := by
  by_cases hy : y = a
  · rw [if_pos hy]
    by_cases hu : u' = m'
    · rw [if_pos hu, if_pos (by rw [hy, hu])]
    · rw [if_neg hu,
        if_neg (fun hc : (y :: u' : List Nat) = a :: m' =>
          hu (List.cons.inj hc).2)]
  · rw [if_neg hy,
      if_neg (fun hc : (y :: u' : List Nat) = a :: m' =>
        hy (List.cons.inj hc).1)]

private theorem countOf_nil_act : ∀ (i j : Nat) (m : List Nat),
    ground.countOf ([] : List Nat) (unitAct i j m) = 0
  | _, _, [] => rfl
  | i, j, x :: r => by
    show ground.countOf []
      ((if x == j then [i :: r] else [])
        ++ (unitAct i j r).map (fun m => x :: m)) = 0
    rw [ground.countOf_append, ground.countOf_nil_consMap]
    cases hb : x == j with
    | true =>
      rw [if_pos rfl]
      show (if ([] : List Nat) = i :: r then 1 else 0) + 0 + 0 = 0
      rw [if_neg (fun hc : ([] : List Nat) = i :: r => nomatch hc)]
    | false =>
      rw [if_neg (fun hc : (false : Bool) = true =>
        Bool.noConfusion hc)]
      rfl

private theorem countOf_act_cons (i j x y : Nat)
    (r u' : List Nat) :
    ground.countOf (y :: u') (unitAct i j (x :: r))
      = (if x == j then (if (y :: u' : List Nat) = i :: r
          then 1 else 0) else 0)
        + (if y = x then ground.countOf u' (unitAct i j r)
          else 0) := by
  show ground.countOf (y :: u')
    ((if x == j then [i :: r] else [])
      ++ (unitAct i j r).map (fun m => x :: m)) = _
  rw [ground.countOf_append,
    ground.countOf_consMap y x (unitAct i j r) u']
  cases hb : x == j with
  | true =>
    rw [if_pos rfl, if_pos rfl,
      ground.countOf_cons (y :: u') (i :: r) ([] : List (List Nat))]
    show (if (y :: u' : List Nat) = i :: r then 1 else 0) + 0
        + (if y = x then ground.countOf u' (unitAct i j r) else 0)
      = (if (y :: u' : List Nat) = i :: r then 1 else 0)
        + (if y = x then ground.countOf u' (unitAct i j r) else 0)
    rw [Nat.add_zero]
  | false =>
    rw [if_neg (fun hc : (false : Bool) = true =>
        Bool.noConfusion hc),
      if_neg (fun hc : (false : Bool) = true =>
        Bool.noConfusion hc)]
    rfl

private theorem countOf_flatMap_consMap (a b x y : Nat)
    (u' : List Nat) : ∀ ms : List (List Nat),
    ground.countOf (y :: u')
        ((ms.map (fun m => x :: m)).flatMap (unitAct a b))
      = (if x == b then
          (if y = a then ground.countOf u' ms else 0) else 0)
        + (if y = x then
          ground.countOf u' (ms.flatMap (unitAct a b)) else 0)
  | [] => by
    show (0 : Nat)
      = (if x == b then (if y = a then 0 else 0) else 0)
        + (if y = x then 0 else 0)
    rw [ite_self, ite_self, ite_self]
  | m' :: ms' => by
    show ground.countOf (y :: u') (unitAct a b (x :: m')
        ++ ((ms'.map (fun m => x :: m)).flatMap (unitAct a b)))
      = _
    rw [ground.countOf_append, countOf_act_cons a b x y m' u',
      countOf_flatMap_consMap a b x y u' ms',
      if_cons_gen y a u' m' 1,
      show ground.countOf u' ((m' :: ms').flatMap (unitAct a b))
          = ground.countOf u' (unitAct a b m')
            + ground.countOf u' (ms'.flatMap (unitAct a b)) from
        ground.countOf_append u' _ _,
      ground.countOf_cons u' m' ms',
      Nat.add_add_add_comm, ground.if_add ((x == b) = true),
      ground.if_add (y = a), ground.if_add (y = x)]

/-- The commutator table at the monomial level: the two composed
Leibniz actions' output counts differ by the contraction reads,
`E_{ab} E_{cd} + δ_{da} E_{cb} = E_{cd} E_{ab} + δ_{bc} E_{ad}`
counted at every target monomial. -/
theorem act_comm (a b c d : Nat) : ∀ (m u : List Nat),
    ground.countOf u ((unitAct c d m).flatMap (unitAct a b))
      + (if a == d then ground.countOf u (unitAct c b m) else 0)
    = ground.countOf u ((unitAct a b m).flatMap (unitAct c d))
      + (if c == b then ground.countOf u (unitAct a d m) else 0)
  | [], u => by
    show (0 : Nat) + (if a == d then 0 else 0)
      = 0 + (if c == b then 0 else 0)
    rw [ite_self, ite_self]
  | x :: r, [] => by
    rw [show ground.countOf ([] : List Nat)
        ((unitAct c d (x :: r)).flatMap (unitAct a b)) = 0 from
        countOf_nil_flatMap a b _,
      show ground.countOf ([] : List Nat)
        ((unitAct a b (x :: r)).flatMap (unitAct c d)) = 0 from
        countOf_nil_flatMap c d _,
      countOf_nil_act c b (x :: r), countOf_nil_act a d (x :: r),
      ite_self, ite_self]
  | x :: r, y :: u' => by
    have hAC : ground.countOf (y :: u')
        ((unitAct c d (x :: r)).flatMap (unitAct a b))
        = (if x == d then
            ((if c == b then
              (if (y :: u' : List Nat) = a :: r then 1 else 0)
              else 0)
            + (if y = c then
              ground.countOf u' (unitAct a b r) else 0)) else 0)
          + ((if x == b then
              (if y = a then
                ground.countOf u' (unitAct c d r) else 0) else 0)
            + (if y = x then ground.countOf u'
              ((unitAct c d r).flatMap (unitAct a b)) else 0)) := by
      show ground.countOf (y :: u')
        (((if x == d then [c :: r] else [])
          ++ (unitAct c d r).map (fun m => x :: m)).flatMap
          (unitAct a b)) = _
      rw [ground.flatMap_append (unitAct a b),
        ground.countOf_append,
        countOf_flatMap_consMap a b x y u' (unitAct c d r)]
      cases hb : x == d with
      | true =>
        rw [if_pos rfl, if_pos rfl]
        show ground.countOf (y :: u')
            (unitAct a b (c :: r) ++ []) + _ = _
        rw [ground.append_nil (unitAct a b (c :: r)),
          countOf_act_cons a b c y r u']
      | false =>
        rw [if_neg (fun hc : (false : Bool) = true =>
            Bool.noConfusion hc),
          if_neg (fun hc : (false : Bool) = true =>
            Bool.noConfusion hc)]
        rfl
    have hCA : ground.countOf (y :: u')
        ((unitAct a b (x :: r)).flatMap (unitAct c d))
        = (if x == b then
            ((if a == d then
              (if (y :: u' : List Nat) = c :: r then 1 else 0)
              else 0)
            + (if y = a then
              ground.countOf u' (unitAct c d r) else 0)) else 0)
          + ((if x == d then
              (if y = c then
                ground.countOf u' (unitAct a b r) else 0) else 0)
            + (if y = x then ground.countOf u'
              ((unitAct a b r).flatMap (unitAct c d)) else 0)) := by
      show ground.countOf (y :: u')
        (((if x == b then [a :: r] else [])
          ++ (unitAct a b r).map (fun m => x :: m)).flatMap
          (unitAct c d)) = _
      rw [ground.flatMap_append (unitAct c d),
        ground.countOf_append,
        countOf_flatMap_consMap c d x y u' (unitAct a b r)]
      cases hb : x == b with
      | true =>
        rw [if_pos rfl, if_pos rfl]
        show ground.countOf (y :: u')
            (unitAct c d (a :: r) ++ []) + _ = _
        rw [ground.append_nil (unitAct c d (a :: r)),
          countOf_act_cons c d a y r u']
      | false =>
        rw [if_neg (fun hc : (false : Bool) = true =>
            Bool.noConfusion hc),
          if_neg (fun hc : (false : Bool) = true =>
            Bool.noConfusion hc)]
        rfl
    rw [hAC, hCA, countOf_act_cons c b x y r u',
      countOf_act_cons a d x y r u']
    rw [← ground.if_add ((x == d) = true)
        (if c == b then
          (if (y :: u' : List Nat) = a :: r then 1 else 0) else 0)
        (if y = c then ground.countOf u' (unitAct a b r) else 0),
      ← ground.if_add ((x == b) = true)
        (if a == d then
          (if (y :: u' : List Nat) = c :: r then 1 else 0) else 0)
        (if y = a then ground.countOf u' (unitAct c d r) else 0),
      ← ground.if_add ((a == d) = true)
        (if x == b then
          (if (y :: u' : List Nat) = c :: r then 1 else 0) else 0)
        (if y = x then ground.countOf u' (unitAct c b r) else 0),
      ← ground.if_add ((c == b) = true)
        (if x == d then
          (if (y :: u' : List Nat) = a :: r then 1 else 0) else 0)
        (if y = x then ground.countOf u' (unitAct a d r) else 0),
      ground.if_swap ((a == d) = true) ((x == b) = true)
        (if (y :: u' : List Nat) = c :: r then 1 else 0),
      ground.if_swap ((c == b) = true) ((x == d) = true)
        (if (y :: u' : List Nat) = a :: r then 1 else 0),
      ground.if_swap ((a == d) = true) (y = x)
        (ground.countOf u' (unitAct c b r)),
      ground.if_swap ((c == b) = true) (y = x)
        (ground.countOf u' (unitAct a d r))]
    have hIH : (if y = x then ground.countOf u'
          ((unitAct c d r).flatMap (unitAct a b)) else 0)
        + (if y = x then
          (if a == d then
            ground.countOf u' (unitAct c b r) else 0) else 0)
      = (if y = x then ground.countOf u'
          ((unitAct a b r).flatMap (unitAct c d)) else 0)
        + (if y = x then
          (if c == b then
            ground.countOf u' (unitAct a d r) else 0) else 0) := by
      rw [ground.if_add (y = x), ground.if_add (y = x),
        act_comm a b c d r u']
    rw [shuffleL
        (if x == d then (if c == b then
          (if (y :: u' : List Nat) = a :: r then 1 else 0)
          else 0) else 0)
        (if x == d then
          (if y = c then ground.countOf u' (unitAct a b r) else 0)
          else 0)
        (if x == b then
          (if y = a then ground.countOf u' (unitAct c d r) else 0)
          else 0)
        (if y = x then ground.countOf u'
          ((unitAct c d r).flatMap (unitAct a b)) else 0)
        (if x == b then (if a == d then
          (if (y :: u' : List Nat) = c :: r then 1 else 0)
          else 0) else 0)
        (if y = x then
          (if a == d then
            ground.countOf u' (unitAct c b r) else 0) else 0),
      hIH]
    exact (shuffleR
      (if x == b then (if a == d then
        (if (y :: u' : List Nat) = c :: r then 1 else 0)
        else 0) else 0)
      (if x == b then
        (if y = a then ground.countOf u' (unitAct c d r) else 0)
        else 0)
      (if x == d then
        (if y = c then ground.countOf u' (unitAct a b r) else 0)
        else 0)
      (if y = x then ground.countOf u'
        ((unitAct a b r).flatMap (unitAct c d)) else 0)
      (if x == d then (if c == b then
        (if (y :: u' : List Nat) = a :: r then 1 else 0)
        else 0) else 0)
      (if y = x then
        (if c == b then
          ground.countOf u' (unitAct a d r) else 0) else 0)).symm
  where
    countOf_nil_flatMap (a b : Nat) : ∀ ms : List (List Nat),
        ground.countOf ([] : List Nat)
          (ms.flatMap (unitAct a b)) = 0
      | [] => rfl
      | m' :: ms' => by
        show ground.countOf [] (unitAct a b m'
          ++ ms'.flatMap (unitAct a b)) = 0
        rw [ground.countOf_append, countOf_nil_act a b m',
          countOf_nil_flatMap a b ms']
    shuffleL (t1 t2 t3 t4 u1 u2 : Nat) :
        ((t1 + t2) + (t3 + t4)) + (u1 + u2)
          = ((t1 + t2 + t3) + u1) + (t4 + u2) := by
      rw [← Nat.add_assoc (t1 + t2) t3 t4,
        Nat.add_assoc (t1 + t2 + t3) t4 (u1 + u2),
        Nat.add_left_comm t4 u1 u2,
        ← Nat.add_assoc (t1 + t2 + t3) u1 (t4 + u2)]
    shuffleR (u1 t3 t2 t4 t1 v2 : Nat) :
        ((u1 + t3) + (t2 + t4)) + (t1 + v2)
          = ((t1 + t2 + t3) + u1) + (t4 + v2) := by
      rw [Nat.add_assoc (u1 + t3) (t2 + t4) (t1 + v2),
        Nat.add_add_add_comm t2 t4 t1 v2,
        ← Nat.add_assoc (u1 + t3) (t2 + t1) (t4 + v2),
        Nat.add_comm u1 t3, Nat.add_comm t2 t1,
        Nat.add_comm (t3 + u1) (t1 + t2),
        ← Nat.add_assoc (t1 + t2) t3 u1]

/-- Composed Leibniz counts convolve over a base holding the
mid outputs once each: the flatMap's count at the target is the
mid members' multiplicity-weighted fold, the matrix product's own
read. -/
theorem countOf_unitAct_comp (i j k l : Nat) (muMid : List Nat)
    (s t : List Nat)
    (hout : ∀ m, 0 < ground.countOf m (unitAct k l s) →
      ground.countOf m (monomialsAt muMid) = 1) :
    ground.countOf t ((unitAct k l s).flatMap (unitAct i j))
      = ground.famFold Nat.add 0
        (fun m => ground.countOf m (unitAct k l s)
          * ground.countOf t (unitAct i j m))
        (monomialsAt muMid) := by
  rw [ground.countOf_flatMap t (unitAct i j) (unitAct k l s),
    ground.famFold_countCollect
      (fun m => ground.countOf t (unitAct i j m))
      (unitAct k l s) (monomialsAt muMid) hout]

/-! The matrix tier (`con:units`): the unit's matrix between
content bases reads the Leibniz counts entrywise — the scatter at
the arithmetic rank against the positional read (`con:places`'
rank tier) — the transpose exchanges the letter pair, and the
composed actions' matrix identities read the monomial table
through the entries. -/

/-- An output's length reads the source's, the Leibniz sum's
per-place re-read. -/
theorem length_unitAct_out (i j : Nat) : ∀ (s m : List Nat),
    0 < ground.countOf m (unitAct i j s) → m.length = s.length
  | [], m, h => absurd h (Nat.lt_irrefl 0)
  | a :: t, m, h => by
    rw [show unitAct i j (a :: t)
        = (if a == j then [i :: t] else [])
          ++ (unitAct i j t).map (fun m' => a :: m') from rfl,
      ground.countOf_append] at h
    have hmap : 0 < ground.countOf m
        ((unitAct i j t).map (fun m' => a :: m')) →
        m.length = (a :: t).length := by
      intro hh
      match m with
      | [] =>
        rw [ground.countOf_nil_consMap] at hh
        exact absurd hh (Nat.lt_irrefl 0)
      | y :: m' =>
        rw [ground.countOf_consMap y a _ m'] at hh
        by_cases hy : y = a
        · rw [if_pos hy] at hh
          exact congrArg Nat.succ (length_unitAct_out i j t m' hh)
        · rw [if_neg hy] at hh
          exact absurd hh (Nat.lt_irrefl 0)
    cases hb : a == j with
    | true =>
      rw [hb, if_pos rfl] at h
      match ground.posOr h with
      | Or.inl hh =>
        by_cases hmc : m = i :: t
        · rw [hmc]
          rfl
        · rw [ground.countOf_cons m (i :: t) ([] : List (List Nat)),
            if_neg hmc] at hh
          exact absurd hh (Nat.lt_irrefl 0)
      | Or.inr hh => exact hmap hh
    | false =>
      rw [hb, if_neg (fun hc : (false : Bool) = true =>
        Bool.noConfusion hc)] at h
      rw [show ground.countOf m ([] : List (List Nat)) = 0 from rfl,
        Nat.zero_add] at h
      exact hmap h

/-- An output's content moves by the letter pair: the count at the
withdrawn letter joins one against the source's, the count at the
entered letter one beyond, every other letter's kept. -/
theorem countOf_unitAct_out (i j x : Nat) : ∀ (s m : List Nat),
    0 < ground.countOf m (unitAct i j s) →
    ground.countOf x m + (if x = j then 1 else 0)
      = ground.countOf x s + (if x = i then 1 else 0)
  | [], m, h => absurd h (Nat.lt_irrefl 0)
  | a :: t, m, h => by
    rw [show unitAct i j (a :: t)
        = (if a == j then [i :: t] else [])
          ++ (unitAct i j t).map (fun m' => a :: m') from rfl,
      ground.countOf_append] at h
    have hmap : 0 < ground.countOf m
        ((unitAct i j t).map (fun m' => a :: m')) →
        ground.countOf x m + (if x = j then 1 else 0)
          = ground.countOf x (a :: t)
            + (if x = i then 1 else 0) := by
      intro hh
      match m with
      | [] =>
        rw [ground.countOf_nil_consMap] at hh
        exact absurd hh (Nat.lt_irrefl 0)
      | y :: m' =>
        rw [ground.countOf_consMap y a _ m'] at hh
        by_cases hy : y = a
        · rw [if_pos hy] at hh
          rw [ground.countOf_cons x y m', ground.countOf_cons x a t,
            hy, Nat.add_assoc, countOf_unitAct_out i j x t m' hh,
            ← Nat.add_assoc]
        · rw [if_neg hy] at hh
          exact absurd hh (Nat.lt_irrefl 0)
    cases hb : a == j with
    | true =>
      rw [hb, if_pos rfl] at h
      match ground.posOr h with
      | Or.inl hh =>
        have hm : m = i :: t := by
          by_cases hmc : m = i :: t
          · exact hmc
          · rw [ground.countOf_cons m (i :: t) ([] : List (List Nat)),
              if_neg hmc] at hh
            exact absurd hh (Nat.lt_irrefl 0)
        rw [hm, ground.beqEqOf hb, ground.countOf_cons x i t,
          ground.countOf_cons x j t]
        exact addSwapEnds _ _ _
      | Or.inr hh => exact hmap hh
    | false =>
      rw [hb, if_neg (fun hc : (false : Bool) = true =>
        Bool.noConfusion hc)] at h
      rw [show ground.countOf m ([] : List (List Nat)) = 0 from rfl,
        Nat.zero_add] at h
      exact hmap h

/-- The scatter keeps the coordinate list's length. -/
theorem length_scatterAt :
    ∀ (n : Nat) (x : BPair) (l : List BPair),
      (scatterAt n x l).length = l.length
  | 0, _, [] => rfl
  | _ + 1, _, [] => rfl
  | 0, _, _ :: _ => rfl
  | n + 1, x, _ :: t => congrArg Nat.succ (length_scatterAt n x t)

/-- The scatter's entry read: the key's entry gains the value,
every other kept. -/
theorem getAt_scatterAt (u : BPair) :
    ∀ (n : Nat) (x : BPair) (l : List BPair) (p : Nat),
      p < l.length →
      ground.getAt u (scatterAt n x l) p
        = if p = n then ground.getAt u l p + x
          else ground.getAt u l p
  | _, _, [], p, hp => absurd hp (Nat.not_lt_zero p)
  | 0, x, a :: t, 0, _ => by rw [if_pos rfl]; rfl
  | 0, x, a :: t, p + 1, _ => by
    rw [if_neg (fun hc : p + 1 = 0 => Nat.noConfusion hc)]
    rfl
  | n + 1, x, a :: t, 0, _ => by
    rw [if_neg (fun hc : 0 = n + 1 => Nat.noConfusion hc)]
    rfl
  | n + 1, x, a :: t, p + 1, hp => by
    show ground.getAt u (scatterAt n x t) p = _
    rw [getAt_scatterAt u n x t p (Nat.lt_of_succ_lt_succ hp)]
    by_cases h : p = n
    · rw [if_pos h, if_pos (congrArg Nat.succ h)]
      rfl
    · rw [if_neg h, if_neg (fun hc => h (Nat.succ.inj hc))]
      rfl

private theorem length_scatFold (muTo : List Nat) :
    ∀ (outs : List (List Nat)) (col : List BPair),
      (outs.foldl (fun col m =>
        if m.length = sumNat muTo ∧ content muTo.length m = muTo then
          scatterAt (rankOf m muTo) (BPair.ofNat 1) col
        else col) col).length
        = col.length
  | [], _ => rfl
  | m :: ms, col => by
    show (ms.foldl _
      (if m.length = sumNat muTo ∧ content muTo.length m = muTo then
        scatterAt (rankOf m muTo) (BPair.ofNat 1) col
      else col)).length = _
    by_cases hm : m.length = sumNat muTo
        ∧ content muTo.length m = muTo
    · rw [if_pos hm, length_scatFold muTo ms _, length_scatterAt]
    · rw [if_neg hm, length_scatFold muTo ms _]

private theorem getAt_scatFold (muTo : List Nat) :
    ∀ (outs : List (List Nat)) (col : List BPair) (p : Nat),
      (∀ m, 0 < ground.countOf m outs →
        m.length = sumNat muTo ∧ content muTo.length m = muTo) →
      p < col.length →
      (ground.getAt BPair.unit (outs.foldl (fun col m =>
          if m.length = sumNat muTo
              ∧ content muTo.length m = muTo then
            scatterAt (rankOf m muTo) (BPair.ofNat 1) col
          else col) col)
        p).oneValue
      (ground.getAt BPair.unit col p
        + BPair.ofNat (ground.countOf p
            (outs.map (fun m => rankOf m muTo))))
  | [], col, p, _, _ =>
    BPair.oneValue_symm
      (BPair.add_unit (ground.getAt BPair.unit col p))
  | m :: ms, col, p, hall, hp => by
    have hallTail : ∀ m', 0 < ground.countOf m' ms →
        m'.length = sumNat muTo
          ∧ content muTo.length m' = muTo := by
      intro m' h'
      refine hall m' (Nat.lt_of_lt_of_le h' ?_)
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    have hmIn : m.length = sumNat muTo
        ∧ content muTo.length m = muTo := by
      refine hall m ?_
      rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
      exact Nat.succ_pos _
    show (ground.getAt BPair.unit (ms.foldl _
        (if m.length = sumNat muTo
            ∧ content muTo.length m = muTo then
          scatterAt (rankOf m muTo) (BPair.ofNat 1) col
        else col)) p).oneValue
      (ground.getAt BPair.unit col p
        + BPair.ofNat (ground.countOf p
            (rankOf m muTo :: ms.map (fun m => rankOf m muTo))))
    rw [ground.countOf_cons, if_pos hmIn]
    have hlen : p < (scatterAt (rankOf m muTo)
        (BPair.ofNat 1) col).length := by
      rw [length_scatterAt]
      exact hp
    refine BPair.oneValue_trans
      (getAt_scatFold muTo ms _ p hallTail hlen) ?_
    rw [getAt_scatterAt BPair.unit (rankOf m muTo)
      (BPair.ofNat 1) col p hp]
    by_cases hpr : p = rankOf m muTo
    · rw [if_pos hpr, if_pos hpr, BPair.add_assoc]
      exact BPair.add_congr
        (BPair.oneValue_refl (ground.getAt BPair.unit col p))
        (BPair.oneValue_symm (BPair.ofNat_add 1
          (ground.countOf p (ms.map (fun m => rankOf m muTo)))))
    · rw [if_neg hpr, if_neg hpr, Nat.zero_add]
      exact BPair.oneValue_refl _

private theorem countRk_eq (muTo : List Nat) (p : Nat)
    (hp : p < (monomialsAt muTo).length) :
    ∀ outs : List (List Nat),
      (∀ m, 0 < ground.countOf m outs →
        m.length = sumNat muTo ∧ content muTo.length m = muTo) →
      ground.countOf p (outs.map (fun m => rankOf m muTo))
        = ground.countOf
            (ground.getAt [] (monomialsAt muTo) p) outs
  | [], _ => rfl
  | m :: ms, hm => by
    have hmm : m.length = sumNat muTo
        ∧ content muTo.length m = muTo := by
      refine hm m ?_
      rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
      exact Nat.succ_pos _
    have hms : ∀ m', 0 < ground.countOf m' ms →
        m'.length = sumNat muTo
          ∧ content muTo.length m' = muTo := by
      intro m' h'
      refine hm m' (Nat.lt_of_lt_of_le h' ?_)
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    show ground.countOf p
        (rankOf m muTo :: ms.map (fun m => rankOf m muTo))
      = ground.countOf (ground.getAt [] (monomialsAt muTo) p) (m :: ms)
    rw [ground.countOf_cons, ground.countOf_cons,
      countRk_eq muTo p hp ms hms]
    by_cases hpr : p = rankOf m muTo
    · rw [if_pos hpr, if_pos (by
        rw [hpr]
        exact (rankOf_read m muTo hmm.1 hmm.2).2)]
    · rw [if_neg hpr, if_neg (fun hc => hpr
        (ground.getAt_inj_distinct [] (monomialsAt muTo)
          (monomialsAt_distinct muTo) p (rankOf m muTo) hp
          (rankOf_read m muTo hmm.1 hmm.2).1
          (hc.trans (rankOf_read m muTo hmm.1 hmm.2).2.symm)))]

/-- The unit matrix's entry read (`con:units`' matrix tier): at a
row key of the target enumeration and a column key of the source's,
the entry is the Leibniz count — the outputs reading the row's
monomial — the scatter at the arithmetic rank against the
positional read. -/
theorem matUnitAt_read (muTo muFrom : List Nat) (i j : Nat)
    (hout : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (p q : Nat) (hp : p < (monomialsAt muTo).length)
    (hq : q < (monomialsAt muFrom).length) :
    (ground.getAt BPair.unit
        (ground.getAt [] (matUnitAt muTo muFrom i j) p) q).oneValue
      (BPair.ofNat (ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (unitAct i j (ground.getAt [] (monomialsAt muFrom) q)))) := by
  have hcolLen : ∀ s : List Nat,
      ((unitAct i j s).foldl (fun col m =>
        if m.length = sumNat muTo ∧ content muTo.length m = muTo then
          scatterAt (rankOf m muTo) (BPair.ofNat 1) col
        else col)
        ((monomialsAt muTo).map (fun _ => BPair.unit))).length
      = (monomialsAt muTo).length := by
    intro s
    rw [length_scatFold muTo (unitAct i j s) _, ground.length_map]
  rw [show matUnitAt muTo muFrom i j
      = elim.transposeM ((monomialsAt muFrom).map (fun s =>
          (unitAct i j s).foldl (fun col m =>
            if m.length = sumNat muTo
                ∧ content muTo.length m = muTo then
              scatterAt (rankOf m muTo) (BPair.ofNat 1) col
            else col)
          ((monomialsAt muTo).map (fun _ => BPair.unit))))
      from rfl,
    elim.getAt_transposeM BPair.unit
      ((monomialsAt muFrom).map (fun s =>
        (unitAct i j s).foldl (fun col m =>
          if m.length = sumNat muTo
              ∧ content muTo.length m = muTo then
            scatterAt (rankOf m muTo) (BPair.ofNat 1) col
          else col)
        ((monomialsAt muTo).map (fun _ => BPair.unit))))
      (elim.rowsLen_map _ (monomialsAt muTo).length
        (monomialsAt muFrom) (fun x _ => hcolLen x))
      p q hp
      (by
        rw [ground.length_map]
        exact hq),
    ground.getAt_map ([] : List Nat) ([] : List BPair) _
      (monomialsAt muFrom) q hq]
  have hs : 0 < ground.countOf
      (ground.getAt [] (monomialsAt muFrom) q)
      (monomialsAt muFrom) :=
    ground.countOf_getAt_pos [] (monomialsAt muFrom) q hq
  have hpseed : p < ((monomialsAt muTo).map
      (fun _ => BPair.unit)).length := by
    rw [ground.length_map]
    exact hp
  refine BPair.oneValue_trans
    (getAt_scatFold muTo
      (unitAct i j (ground.getAt [] (monomialsAt muFrom) q))
      ((monomialsAt muTo).map (fun _ => BPair.unit)) p
      (fun m hm =>
        hout (ground.getAt [] (monomialsAt muFrom) q) m hs hm)
      hpseed) ?_
  rw [ground.getAt_map ([] : List Nat) BPair.unit
      (fun _ => BPair.unit) (monomialsAt muTo) p hp,
    countRk_eq muTo p hp
      (unitAct i j (ground.getAt [] (monomialsAt muFrom) q))
      (fun m hm =>
        hout (ground.getAt [] (monomialsAt muFrom) q) m hs hm)]
  exact BPair.unit_add _

private theorem unitTail_seed {α : Type} :
    ∀ l : List α, poly.unitTail (l.map (fun _ => BPair.unit))
  | [] => trivial
  | _ :: t => ⟨BPair.oneValue_refl BPair.unit, unitTail_seed t⟩

private theorem scatFold_off (muTo : List Nat) :
    ∀ (outs : List (List Nat)) (col : List BPair),
      (∀ m, 0 < ground.countOf m outs →
        ¬ (m.length = sumNat muTo
          ∧ content muTo.length m = muTo)) →
      outs.foldl (fun col m =>
        if m.length = sumNat muTo ∧ content muTo.length m = muTo then
          scatterAt (rankOf m muTo) (BPair.ofNat 1) col
        else col) col
        = col
  | [], _, _ => rfl
  | m :: ms, col, hall => by
    have hm : ¬ (m.length = sumNat muTo
        ∧ content muTo.length m = muTo) := by
      refine hall m ?_
      rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
      exact Nat.succ_pos _
    have htail : ∀ m', 0 < ground.countOf m' ms →
        ¬ (m'.length = sumNat muTo
          ∧ content muTo.length m' = muTo) := by
      intro m' h'
      refine hall m' (Nat.lt_of_lt_of_le h' ?_)
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    show ms.foldl _
      (if m.length = sumNat muTo ∧ content muTo.length m = muTo then
        scatterAt (rankOf m muTo) (BPair.ofNat 1) col
      else col) = col
    rw [if_neg hm]
    exact scatFold_off muTo ms col htail

private theorem matNull_cols (muTo muFrom : List Nat) (i j : Nat)
    (hoff : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i j s) →
      ¬ (m.length = sumNat muTo
        ∧ content muTo.length m = muTo)) :
    ∀ src : List (List Nat),
      (∀ s, 0 < ground.countOf s src →
        0 < ground.countOf s (monomialsAt muFrom)) →
      elim.matNull (src.map (fun s =>
        (unitAct i j s).foldl (fun col m =>
          if m.length = sumNat muTo
              ∧ content muTo.length m = muTo then
            scatterAt (rankOf m muTo) (BPair.ofNat 1) col
          else col)
        ((monomialsAt muTo).map (fun _ => BPair.unit))))
  | [], _ => trivial
  | s :: t, hall => by
    have hs : 0 < ground.countOf s (monomialsAt muFrom) := by
      refine hall s ?_
      rw [ground.countOf_cons, if_pos rfl, Nat.add_comm]
      exact Nat.succ_pos _
    have htail : ∀ s', 0 < ground.countOf s' t →
        0 < ground.countOf s' (monomialsAt muFrom) := by
      intro s' h'
      refine hall s' (Nat.lt_of_lt_of_le h' ?_)
      rw [ground.countOf_cons]
      exact Nat.le_add_left _ _
    refine ⟨?_, matNull_cols muTo muFrom i j hoff t htail⟩
    show poly.unitTail ((unitAct i j s).foldl (fun col m =>
        if m.length = sumNat muTo
            ∧ content muTo.length m = muTo then
          scatterAt (rankOf m muTo) (BPair.ofNat 1) col
        else col)
      ((monomialsAt muTo).map (fun _ => BPair.unit)))
    rw [scatFold_off muTo (unitAct i j s) _
      (fun m hm => hoff s m hs hm)]
    exact unitTail_seed (monomialsAt muTo)

/-- The unit matrix's null read (`con:units`' grading): where no
Leibniz output of any source monomial sits at the target content,
every column keeps its seed and the compression is the null map —
the matrix between two contents the action does not connect. -/
theorem matUnitAt_null_offcontent (muTo muFrom : List Nat) (i j : Nat)
    (hoff : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i j s) →
      ¬ (m.length = sumNat muTo ∧ content muTo.length m = muTo)) :
    elim.matNull (matUnitAt muTo muFrom i j) :=
  elim.matNull_transposeM _
    (matNull_cols muTo muFrom i j hoff (monomialsAt muFrom)
      (fun _ h => h))

private theorem beqIfEq (a b x : Nat) :
    (if a == b then x else 0) = if a = b then x else 0 := by
  cases hb : a == b with
  | true => rw [if_pos rfl, if_pos (ground.beqEqOf hb)]
  | false =>
    rw [if_neg (fun hc : (false : Bool) = true =>
        Bool.noConfusion hc),
      if_neg (fun he : a = b =>
        Bool.noConfusion ((ground.eqBeqOf he).symm.trans hb))]

private theorem if_eqSymm {α : Type} [DecidableEq α] (a b : α)
    (x : Nat) :
    (if a = b then x else 0) = if b = a then x else 0 := by
  by_cases h : a = b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hc => h hc.symm)]

/-- The transpose read: the letter pair exchanged, the counts
symmetric — `⟨E_{ij} s, m⟩ = ⟨s, E_{ji} m⟩` at the monomial
pairing. -/
theorem countOf_unitAct_swap (i j : Nat) :
    ∀ (s m : List Nat),
      ground.countOf m (unitAct i j s)
        = ground.countOf s (unitAct j i m)
  | [], [] => rfl
  | [], y :: m' => (countOf_nil_act j i (y :: m')).symm
  | a :: s', [] => countOf_nil_act i j (a :: s')
  | a :: s', y :: m' => by
    rw [countOf_act_cons i j a y s' m',
      countOf_act_cons j i y a m' s',
      if_cons_gen y i m' s' 1, if_cons_gen a j s' m' 1,
      beqIfEq a j, beqIfEq y i,
      ground.if_swap (a = j) (y = i)
        (if m' = s' then 1 else 0),
      if_eqSymm m' s' 1,
      countOf_unitAct_swap i j s' m']
    by_cases hya : y = a
    · rw [if_pos hya, if_pos hya.symm]
    · rw [if_neg hya, if_neg (fun hc : a = y => hya hc.symm)]

/-- The diagonal read: the equal-lettered unit repeats its source,
the count the letter's own occupancy — `E_{ii}` the grading's
read. -/
theorem countOf_unitAct_diag (i : Nat) :
    ∀ (m u : List Nat),
      ground.countOf u (unitAct i i m)
        = if u = m then ground.countOf i m else 0
  | [], u => by
    show (0 : Nat) = if u = [] then ground.countOf i [] else 0
    by_cases h : u = ([] : List Nat)
    · rw [if_pos h]
      rfl
    · rw [if_neg h]
  | a :: t, [] => by
    rw [countOf_nil_act i i (a :: t),
      if_neg (fun hc : ([] : List Nat) = a :: t => nomatch hc)]
  | a :: t, y :: u' => by
    rw [countOf_act_cons i i a y t u',
      if_cons_gen y i u' t 1, beqIfEq a i,
      countOf_unitAct_diag i t u',
      if_cons_gen y a u' t (ground.countOf i (a :: t)),
      ground.countOf_cons i a t]
    by_cases hya : y = a
    · rw [if_pos hya, if_pos hya]
      by_cases hut : u' = t
      · rw [if_pos hut, if_pos hut, if_pos hut]
        by_cases hai : a = i
        · rw [if_pos hai, if_pos (hya.trans hai), if_pos hai.symm]
        · rw [if_neg hai, if_neg (fun hc : i = a => hai hc.symm),
            Nat.zero_add]
      · rw [if_neg hut, if_neg hut, if_neg hut,
          ite_self (c := y = i) 0, ite_self (c := a = i) 0,
          Nat.add_zero]
    · rw [if_neg hya, if_neg hya, Nat.add_zero]
      by_cases hai : a = i
      · by_cases hyi : y = i
        · exact absurd (hyi.trans hai.symm) hya
        · rw [if_pos hai, if_neg hyi]
      · rw [if_neg hai]

/-- The unit matrix's row count is the target enumeration's
length. -/
theorem length_matUnitAt (muTo muFrom : List Nat) (i j : Nat) :
    (matUnitAt muTo muFrom i j).length
      = (monomialsAt muTo).length := by
  refine elim.length_transposeM _
    (elim.rowsLen_map _ (monomialsAt muTo).length
      (monomialsAt muFrom) (fun s _ => by
        rw [length_scatFold muTo (unitAct i j s) _,
          ground.length_map])) ?_
  rw [ground.length_map]
  exact monomialsAt_occupied muFrom

/-- The unit matrix's action has the target basis's length, the
row count's own read at every coordinate family. -/
theorem matVec_matUnitAt_length (muTo muFrom : List Nat)
    (i j : Nat) (x : List BPair) :
    (elim.matVec (matUnitAt muTo muFrom i j) x).length
      = (monomialsAt muTo).length := by
  rw [elim.matVec_length, length_matUnitAt]

/-! The commutator table's matrix tier: the composed units' product
read, the single unit's action as the composites' crossed join, the
diagonal's occupancy scalar, and the transpose's letter exchange —
the closure tier's consumption at stated enumerations, the content
hypotheses discharged by the output kit at the instantiations. -/

/-- The unit matrix's rows: each of the transpose's column lists
carries the source enumeration's own length (`con:units`' matrix
at the stated key lists). -/
theorem rowsLen_matUnitAt (muTo muFrom : List Nat)
    (i j : Nat) :
    elim.rowsLen (monomialsAt muFrom).length
      (matUnitAt muTo muFrom i j) := by
  have h := elim.rowsLen_transposeM
    ((monomialsAt muFrom).map (fun s =>
      (unitAct i j s).foldl
        (fun col m =>
          if m.length = sumNat muTo
              ∧ content muTo.length m = muTo then
            scatterAt (rankOf m muTo) (BPair.ofNat 1) col
          else col)
        ((monomialsAt muTo).map (fun _ => BPair.unit))))
  rw [ground.length_map] at h
  exact h

private theorem rowsLen_matMul (S T : elim.Mat) (n : Nat)
    (hT : elim.rowsLen n T) (hT0 : 0 < T.length) :
    elim.rowsLen n (elim.matMul S T) :=
  elim.rowsLen_map (fun r => (elim.transposeM T).map (fun c => elim.dotN r c)) n S (fun x _ => (fun _ => by
      rw [ground.length_map, elim.length_transposeM T hT hT0]) x)

private theorem matOneValue_of_rows (n : Nat) : ∀ A B : elim.Mat,
    A.length = B.length → elim.rowsLen n A → elim.rowsLen n B →
    (∀ p, p < A.length → ∀ q, q < n →
      (ground.getAt BPair.unit (ground.getAt [] A p) q).oneValue
        (ground.getAt BPair.unit (ground.getAt [] B p) q)) →
    elim.matOneValue A B
  | [], [], _, _, _, _ => True.intro
  | [], _ :: _, h, _, _, _ => Nat.noConfusion h
  | _ :: _, [], h, _, _, _ => Nat.noConfusion h
  | a :: A', b :: B', hl, hA, hB, hent =>
    And.intro
      (poly.oneValue_of_entries a b (Eq.trans hA.1 hB.1.symm)
        (fun q hq => hent 0 (Nat.succ_pos _) q
          (Eq.subst hA.1 hq)))
      (matOneValue_of_rows n A' B' (Nat.succ.inj hl) hA.2 hB.2
        (fun p hp q hq => hent (p + 1) (Nat.succ_lt_succ hp) q hq))

private theorem swapRearr {x y z : BPair} (h : x.oneValue (y + z)) :
    z.oneValue (x + y.swap) := by
  have h' : x.fst + (y.snd + z.snd) = y.fst + z.fst + x.snd := h
  show z.fst + (x.snd + y.fst) = x.fst + y.snd + z.snd
  have e1 : z.fst + (x.snd + y.fst) = y.fst + z.fst + x.snd := by
    rw [ground.add_comm x.snd y.fst, ← ground.add_assoc,
      ground.add_comm z.fst y.fst]
  rw [e1, ground.add_assoc x.fst y.snd z.snd]
  exact h'.symm

private theorem dotP_delta (c : BPair) :
    ∀ (t : Nat) (r x : List BPair), t < r.length →
      (ground.getAt BPair.unit r t).oneValue c →
      (∀ s, s < r.length → ¬ s = t →
        (ground.getAt BPair.unit r s).oneValue BPair.unit) →
      (elim.dotP r x).oneValue (c * ground.getAt BPair.unit x t)
  | t, [], _, ht, _, _ => absurd ht (Nat.not_lt_zero t)
  | 0, _ :: _, [], _, _, _ => BPair.oneValue_symm (BPair.mul_unit c)
  | _ + 1, _ :: _, [], _, _, _ =>
    BPair.oneValue_symm (BPair.mul_unit c)
  | 0, _ :: r', b :: x', _, hc, hu =>
    BPair.oneValue_trans
      (BPair.add_congr (BPair.mul_congr hc (BPair.oneValue_refl b))
        (elim.dotP_null_tail_left r' x'
          (elim.unitTail_of_getAt r'
            (fun s hs => hu (s + 1) (Nat.succ_lt_succ hs)
              (fun hcc => Nat.noConfusion hcc)))))
      (BPair.add_unit (c * b))
  | n + 1, _ :: r', b :: x', ht, hc, hu =>
    BPair.oneValue_trans
      (BPair.add_congr
        (BPair.oneValue_trans
          (BPair.mul_congr
            (hu 0 (Nat.succ_pos _) (fun hcc => Nat.noConfusion hcc))
            (BPair.oneValue_refl b))
          (BPair.unit_mul b))
        (dotP_delta c n r' x' (Nat.lt_of_succ_lt_succ ht) hc
          (fun s hs hne => hu (s + 1) (Nat.succ_lt_succ hs)
            (fun hcc => hne (Nat.succ.inj hcc)))))
      (BPair.unit_add (c * ground.getAt BPair.unit x' n))

private theorem dotP_swapSplit : ∀ r a b x : List BPair,
    r.length = a.length → a.length = b.length →
    (∀ q, q < r.length →
      (ground.getAt BPair.unit r q).oneValue
        (ground.getAt BPair.unit a q
          + (ground.getAt BPair.unit b q).swap)) →
    (elim.dotP r x).oneValue
      (elim.dotP a x + (elim.dotP b x).swap)
  | [], [], [], _, _, _, _ =>
    BPair.oneValue_symm (BPair.add_unit BPair.unit)
  | [], [], _ :: _, _, _, hab, _ => Nat.noConfusion hab
  | [], _ :: _, _, _, hra, _, _ => Nat.noConfusion hra
  | _ :: _, [], _, _, hra, _, _ => Nat.noConfusion hra
  | _ :: _, _ :: _, [], _, _, hab, _ => Nat.noConfusion hab
  | _ :: _, _ :: _, _ :: _, [], _, _, _ =>
    BPair.oneValue_symm (BPair.add_unit BPair.unit)
  | rh :: rt, ah :: at', bh :: bt, xh :: xt, hra, hab, hent => by
    have hIH := dotP_swapSplit rt at' bt xt (Nat.succ.inj hra)
      (Nat.succ.inj hab)
      (fun q hq => hent (q + 1) (Nat.succ_lt_succ hq))
    have hh : rh.oneValue (ah + bh.swap) := hent 0 (Nat.succ_pos _)
    have hsw : (bh * xh).swap = bh.swap * xh := by
      rw [BPair.mul_comm bh xh, ← BPair.mul_swap xh bh,
        BPair.mul_comm xh bh.swap]
    show (rh * xh + elim.dotP rt xt).oneValue
      (ah * xh + elim.dotP at' xt
        + (bh * xh + elim.dotP bt xt).swap)
    rw [← BPair.swap_add (bh * xh) (elim.dotP bt xt),
      BPair.add_add_comm (ah * xh) (elim.dotP at' xt)
        ((bh * xh).swap) ((elim.dotP bt xt).swap),
      hsw, ← BPair.right_distrib ah bh.swap xh]
    exact BPair.add_congr
      (BPair.mul_congr hh (BPair.oneValue_refl xh)) hIH

private theorem comm_rows (Mij MA MB : elim.Mat) (n L : Nat)
    (x : List BPair) (hlij : Mij.length = L) (hla : MA.length = L)
    (hlb : MB.length = L) (hrij : elim.rowsLen n Mij)
    (hra : elim.rowsLen n MA) (hrb : elim.rowsLen n MB)
    (hent : ∀ p, p < L → ∀ q, q < n →
      (ground.getAt BPair.unit (ground.getAt [] Mij p) q).oneValue
        (ground.getAt BPair.unit (ground.getAt [] MA p) q
          + (ground.getAt BPair.unit
              (ground.getAt [] MB p) q).swap)) :
    poly.oneValue (elim.matVec Mij x)
      (elim.vecAdd (elim.matVec MA x)
        ((elim.matVec MB x).map BPair.swap)) := by
  have hml : (elim.matVec MA x).length
      = ((elim.matVec MB x).map BPair.swap).length := by
    rw [ground.length_map, elim.matVec_length, elim.matVec_length,
      hla, hlb]
  refine poly.oneValue_of_entries _ _ ?_ (fun p hp => ?_)
  · rw [elim.matVec_length, hlij, elim.length_vecAdd _ _ _ rfl hml.symm,
      elim.matVec_length, hla]
  · have hpL : p < L := by
      rw [elim.matVec_length, hlij] at hp
      exact hp
    have hpA : p < (elim.matVec MA x).length := by
      rw [elim.matVec_length, hla]
      exact hpL
    have hpB : p < (elim.matVec MB x).length := by
      rw [elim.matVec_length, hlb]
      exact hpL
    have hrowij : (ground.getAt [] Mij p).length = n :=
      elim.rowsLen_getAt Mij p hrij (by rw [hlij]; exact hpL)
    have hrowa : (ground.getAt [] MA p).length = n :=
      elim.rowsLen_getAt MA p hra (by rw [hla]; exact hpL)
    have hrowb : (ground.getAt [] MB p).length = n :=
      elim.rowsLen_getAt MB p hrb (by rw [hlb]; exact hpL)
    rw [elim.getAt_matVec Mij x p (by rw [hlij]; exact hpL),
      elim.getAt_vecAdd _ _ p hpA
        (by rw [ground.length_map]; exact hpB),
      ground.getAt_map BPair.unit BPair.unit BPair.swap
        (elim.matVec MB x) p hpB,
      elim.getAt_matVec MA x p (by rw [hla]; exact hpL),
      elim.getAt_matVec MB x p (by rw [hlb]; exact hpL)]
    exact BPair.oneValue_trans (elim.dotN_read _ _)
      (BPair.oneValue_trans
        (dotP_swapSplit _ _ _ x (by rw [hrowij, hrowa])
          (by rw [hrowa, hrowb])
          (fun q hq => hent p hpL q (by rw [hrowij] at hq; exact hq)))
        (BPair.add_congr (BPair.oneValue_symm (elim.dotN_read _ _))
          (ground.swap_congr (BPair.oneValue_symm (elim.dotN_read _ _)))))

/-- The composed units' matrix product reads the composed Leibniz
count entrywise, the convolution collected over the middle
enumeration. -/
theorem matUnit_comp_read (muTo muMid muFrom : List Nat)
    (i j k l : Nat)
    (houtKL : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct k l s) →
      ground.countOf m (monomialsAt muMid) = 1)
    (houtIJ : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muMid) →
      0 < ground.countOf m (unitAct i j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (p q : Nat) (hp : p < (monomialsAt muTo).length)
    (hq : q < (monomialsAt muFrom).length) :
    (ground.getAt BPair.unit
        (ground.getAt []
          (elim.matMul (matUnitAt muTo muMid i j)
            (matUnitAt muMid muFrom k l)) p) q).oneValue
      (BPair.ofNat (ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        ((unitAct k l
          (ground.getAt [] (monomialsAt muFrom) q)).flatMap
          (unitAct i j)))) := by
  have hqcnt : 0 < ground.countOf
      (ground.getAt [] (monomialsAt muFrom) q) (monomialsAt muFrom) :=
    ground.countOf_getAt_pos [] (monomialsAt muFrom) q hq
  have houtKL' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct k l s) →
      m.length = sumNat muMid ∧ content muMid.length m = muMid := by
    intro s m hs hm
    have h1 := houtKL s m hs hm
    rw [countOf_monomialsAt muMid m] at h1
    by_cases hcc : m.length = sumNat muMid
        ∧ content muMid.length m = muMid
    · exact hcc
    · rw [if_neg hcc] at h1
      exact Nat.noConfusion h1
  have hArows : elim.rowsLen (monomialsAt muMid).length
      (matUnitAt muTo muMid i j) := rowsLen_matUnitAt muTo muMid i j
  have hBrows : elim.rowsLen (monomialsAt muFrom).length
      (matUnitAt muMid muFrom k l) :=
    rowsLen_matUnitAt muMid muFrom k l
  have hBlen : (matUnitAt muMid muFrom k l).length
      = (monomialsAt muMid).length := length_matUnitAt muMid muFrom k l
  have hpA : p < (matUnitAt muTo muMid i j).length := by
    rw [length_matUnitAt]
    exact hp
  have hqT : q
      < (elim.transposeM (matUnitAt muMid muFrom k l)).length := by
    rw [elim.length_transposeM _ hBrows (by
      rw [hBlen]
      exact monomialsAt_occupied muMid)]
    exact hq
  rw [show elim.matMul (matUnitAt muTo muMid i j)
        (matUnitAt muMid muFrom k l)
      = (matUnitAt muTo muMid i j).map (fun r =>
          (elim.transposeM (matUnitAt muMid muFrom k l)).map
            (fun c => elim.dotN r c)) from rfl,
    ground.getAt_map ([] : List BPair) ([] : List BPair) _
      (matUnitAt muTo muMid i j) p hpA,
    ground.getAt_map ([] : List BPair) BPair.unit _
      (elim.transposeM (matUnitAt muMid muFrom k l)) q hqT]
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (elim.dotP_ofNat_fold
      (fun m => ground.countOf
        (ground.getAt [] (monomialsAt muTo) p) (unitAct i j m))
      (fun m => ground.countOf m
        (unitAct k l (ground.getAt [] (monomialsAt muFrom) q)))
      (monomialsAt muMid) _ _
      (elim.rowsLen_getAt (n := (monomialsAt muMid).length)
        (matUnitAt muTo muMid i j) p hArows hpA)
      (by
        rw [elim.rowsLen_getAt (n := (matUnitAt muMid muFrom k l).length)
          (elim.transposeM (matUnitAt muMid muFrom k l)) q
          (elim.rowsLen_transposeM
            (matUnitAt muMid muFrom k l)) hqT, hBlen])
      (fun r hr => matUnitAt_read muTo muMid i j houtIJ p r hp hr)
      (fun r hr => by
        rw [elim.getAt_transposeM BPair.unit
          (matUnitAt muMid muFrom k l) hBrows q r hq
          (by rw [hBlen]; exact hr)]
        exact matUnitAt_read muMid muFrom k l houtKL' r q hr hq)) ?_
  refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
  rw [countOf_unitAct_comp i j k l muMid
      (ground.getAt [] (monomialsAt muFrom) q)
      (ground.getAt [] (monomialsAt muTo) p)
      (fun m hm => houtKL (ground.getAt [] (monomialsAt muFrom) q) m
        hqcnt hm),
    ground.famFold_congr_all Nat.add 0
      (fun m => ground.countOf m
          (unitAct k l (ground.getAt [] (monomialsAt muFrom) q))
        * ground.countOf (ground.getAt [] (monomialsAt muTo) p)
          (unitAct i j m))
      (fun m => ground.countOf
          (ground.getAt [] (monomialsAt muTo) p) (unitAct i j m)
        * ground.countOf m
          (unitAct k l (ground.getAt [] (monomialsAt muFrom) q)))
      (fun m => Nat.mul_comm _ _) (monomialsAt muMid)]

/-- The commutator's vector read at distinct letters: the single
unit's action is the two composites' crossed join, the second
composite entering at the memberwise swap (`con:units`' table at
the coordinate vectors). -/
theorem matVec_comm_read (muTo muMidA muMidB muFrom : List Nat)
    (i k j : Nat) (hij : ¬ i = j)
    (hKJ : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct k j s) →
      m.length = sumNat muMidA ∧ content muMidA.length m = muMidA)
    (hIK : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muMidA) →
      0 < ground.countOf m (unitAct i k s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (hIK' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i k s) →
      m.length = sumNat muMidB ∧ content muMidB.length m = muMidB)
    (hKJ' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muMidB) →
      0 < ground.countOf m (unitAct k j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (hIJ : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (x : List BPair) (hx : x.length = (monomialsAt muFrom).length) :
    poly.oneValue
      (elim.matVec (matUnitAt muTo muFrom i j) x)
      (elim.vecAdd
        (elim.matVec (matUnitAt muTo muMidA i k)
          (elim.matVec (matUnitAt muMidA muFrom k j) x))
        ((elim.matVec (matUnitAt muTo muMidB k j)
          (elim.matVec (matUnitAt muMidB muFrom i k) x)).map
          BPair.swap)) := by
  have honeA : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct k j s) →
      ground.countOf m (monomialsAt muMidA) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muMidA m, if_pos (hKJ s m hs hm)]
  have honeB : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i k s) →
      ground.countOf m (monomialsAt muMidB) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muMidB m, if_pos (hIK' s m hs hm)]
  have hfrom0 : 0 < (matUnitAt muMidA muFrom k j).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muMidA
  have hfrom0' : 0 < (matUnitAt muMidB muFrom i k).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muMidB
  have hAmv : poly.oneValue
      (elim.matVec (matUnitAt muTo muMidA i k)
        (elim.matVec (matUnitAt muMidA muFrom k j) x))
      (elim.matVec (elim.matMul (matUnitAt muTo muMidA i k)
        (matUnitAt muMidA muFrom k j)) x) :=
    elim.matVec_comp (matUnitAt muTo muMidA i k)
      (matUnitAt muMidA muFrom k j) x (monomialsAt muFrom).length
      (rowsLen_matUnitAt muMidA muFrom k j) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt muTo muMidA i k)
  have hBmv : poly.oneValue
      (elim.matVec (matUnitAt muTo muMidB k j)
        (elim.matVec (matUnitAt muMidB muFrom i k) x))
      (elim.matVec (elim.matMul (matUnitAt muTo muMidB k j)
        (matUnitAt muMidB muFrom i k)) x) :=
    elim.matVec_comp (matUnitAt muTo muMidB k j)
      (matUnitAt muMidB muFrom i k) x (monomialsAt muFrom).length
      (rowsLen_matUnitAt muMidB muFrom i k) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt muTo muMidB k j)
  have hcore : poly.oneValue
      (elim.matVec (matUnitAt muTo muFrom i j) x)
      (elim.vecAdd
        (elim.matVec (elim.matMul (matUnitAt muTo muMidA i k)
          (matUnitAt muMidA muFrom k j)) x)
        ((elim.matVec (elim.matMul (matUnitAt muTo muMidB k j)
          (matUnitAt muMidB muFrom i k)) x).map BPair.swap)) := by
    refine comm_rows _ _ _ (monomialsAt muFrom).length
      (monomialsAt muTo).length x (length_matUnitAt muTo muFrom i j)
      (by rw [elim.length_matMul, length_matUnitAt])
      (by rw [elim.length_matMul, length_matUnitAt])
      (rowsLen_matUnitAt muTo muFrom i j)
      (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muMidA muFrom k j)
        hfrom0)
      (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muMidB muFrom i k)
        hfrom0')
      (fun p hp q hq => ?_)
    have hac := act_comm i k k j
      (ground.getAt [] (monomialsAt muFrom) q)
      (ground.getAt [] (monomialsAt muTo) p)
    rw [if_neg (fun hcc => hij (ground.beqEqOf hcc)),
      if_pos (ground.eqBeqOf (rfl : k = k)), Nat.add_zero] at hac
    have hAB : (BPair.ofNat (ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        ((unitAct k j (ground.getAt [] (monomialsAt muFrom) q)).flatMap
          (unitAct i k)))).oneValue
      (BPair.ofNat (ground.countOf
          (ground.getAt [] (monomialsAt muTo) p)
          ((unitAct i k
            (ground.getAt [] (monomialsAt muFrom) q)).flatMap
            (unitAct k j)))
        + BPair.ofNat (ground.countOf
          (ground.getAt [] (monomialsAt muTo) p)
          (unitAct i j
            (ground.getAt [] (monomialsAt muFrom) q)))) := by
      rw [hac]
      exact BPair.ofNat_add _ _
    exact BPair.oneValue_trans
      (matUnitAt_read muTo muFrom i j hIJ p q hp hq)
      (BPair.oneValue_trans (swapRearr hAB)
        (BPair.add_congr
          (BPair.oneValue_symm (matUnit_comp_read muTo muMidA muFrom
            i k k j honeA hIK p q hp hq))
          (ground.swap_congr (BPair.oneValue_symm
            (matUnit_comp_read muTo muMidB muFrom k j i k honeB hKJ'
              p q hp hq)))))
  refine poly.oneValue_trans hcore
    (elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_symm hAmv)
      (poly.swapMap_oneValue (poly.oneValue_symm hBmv)) ?_ ?_)
  · rw [elim.matVec_length, elim.matVec_length, elim.length_matMul]
  · rw [ground.length_map, ground.length_map, elim.matVec_length,
      elim.matVec_length, elim.length_matMul]

/-- The equal-lettered unit acts as the letter's occupancy scalar
on a content's coordinates, the grading's read. -/
theorem matVec_diag_read (mu : List Nat) (p : Nat)
    (hp : p < mu.length) (x : List BPair)
    (hx : x.length = (monomialsAt mu).length) :
    poly.oneValue (elim.matVec (matUnitAt mu mu p p) x)
      (elim.vecScale (BPair.ofNat (ground.getAt 0 mu p)) x) := by
  have hmem : ∀ s : List Nat, 0 < ground.countOf s (monomialsAt mu) →
      s.length = sumNat mu ∧ content mu.length s = mu := by
    intro s hs
    rw [countOf_monomialsAt mu s] at hs
    by_cases hcc : s.length = sumNat mu ∧ content mu.length s = mu
    · exact hcc
    · rw [if_neg hcc] at hs
      exact absurd hs (Nat.lt_irrefl 0)
  have hout : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct p p s) →
      m.length = sumNat mu ∧ content mu.length m = mu := by
    intro s m hs hm
    rw [countOf_unitAct_diag p s m] at hm
    by_cases hms : m = s
    · rw [hms]
      exact hmem s hs
    · rw [if_neg hms] at hm
      exact absurd hm (Nat.lt_irrefl 0)
  have hcnt : ∀ s : List Nat, 0 < ground.countOf s (monomialsAt mu) →
      ground.countOf p s = ground.getAt 0 mu p := by
    intro s hs
    rw [← (hmem s hs).2,
      show content mu.length s
        = (List.range mu.length).map
          (fun t => ground.countOf t s) from rfl,
      ground.getAt_map 0 0 (fun t => ground.countOf t s)
        (List.range mu.length) p (by rw [length_range]; exact hp),
      getAt_range mu.length p hp]
  have hdiag : ∀ t, t < (monomialsAt mu).length →
      (ground.getAt BPair.unit
        (ground.getAt [] (matUnitAt mu mu p p) t) t).oneValue
        (BPair.ofNat (ground.getAt 0 mu p)) := by
    intro t ht
    refine BPair.oneValue_trans
      (matUnitAt_read mu mu p p hout t t ht ht)
      (BPair.oneValue_of_eq (congrArg BPair.ofNat ?_))
    rw [countOf_unitAct_diag p (ground.getAt [] (monomialsAt mu) t)
      (ground.getAt [] (monomialsAt mu) t), if_pos rfl]
    exact hcnt (ground.getAt [] (monomialsAt mu) t)
      (ground.countOf_getAt_pos [] (monomialsAt mu) t ht)
  have hoff : ∀ t s, t < (monomialsAt mu).length →
      s < (monomialsAt mu).length → ¬ s = t →
      (ground.getAt BPair.unit
        (ground.getAt [] (matUnitAt mu mu p p) t) s).oneValue
        BPair.unit := by
    intro t s ht hs hne
    have hz : ground.countOf (ground.getAt [] (monomialsAt mu) t)
        (unitAct p p (ground.getAt [] (monomialsAt mu) s)) = 0 := by
      rw [countOf_unitAct_diag p (ground.getAt [] (monomialsAt mu) s)
        (ground.getAt [] (monomialsAt mu) t),
        if_neg (fun hcc => hne (ground.getAt_inj_distinct []
          (monomialsAt mu) (monomialsAt_distinct mu) t s ht hs
          hcc).symm)]
    exact BPair.oneValue_trans
      (matUnitAt_read mu mu p p hout t s ht hs)
      (BPair.oneValue_of_eq (congrArg BPair.ofNat hz))
  refine poly.oneValue_of_entries _ _ ?_ (fun t ht => ?_)
  · rw [elim.matVec_length, length_matUnitAt,
      show elim.vecScale (BPair.ofNat (ground.getAt 0 mu p)) x
        = x.map (fun y => BPair.ofNat (ground.getAt 0 mu p) * y)
        from rfl, ground.length_map, hx]
  · have htL : t < (monomialsAt mu).length := by
      rw [elim.matVec_length, length_matUnitAt] at ht
      exact ht
    have htM : t < (matUnitAt mu mu p p).length := by
      rw [length_matUnitAt]
      exact htL
    rw [elim.getAt_matVec (matUnitAt mu mu p p) x t htM,
      show elim.vecScale (BPair.ofNat (ground.getAt 0 mu p)) x
        = x.map (fun y => BPair.ofNat (ground.getAt 0 mu p) * y)
        from rfl,
      ground.getAt_map BPair.unit BPair.unit
        (fun y => BPair.ofNat (ground.getAt 0 mu p) * y) x t
        (by rw [hx]; exact htL)]
    have hrow : (ground.getAt [] (matUnitAt mu mu p p) t).length
        = (monomialsAt mu).length :=
      elim.rowsLen_getAt (n := (monomialsAt mu).length) (matUnitAt mu mu p p) t
        (rowsLen_matUnitAt mu mu p p) htM
    refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
    exact dotP_delta (BPair.ofNat (ground.getAt 0 mu p)) t
      (ground.getAt [] (matUnitAt mu mu p p) t) x
      (by rw [hrow]; exact htL) (hdiag t htL)
      (fun s hs hne => hoff t s htL (by rw [hrow] at hs; exact hs) hne)

/-- The unit's matrix transposes to the exchanged letters', the
monomial pairing's read. -/
theorem matUnit_transpose_read (muTo muFrom : List Nat) (i j : Nat)
    (hout : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (hout' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muTo) →
      0 < ground.countOf m (unitAct j i s) →
      m.length = sumNat muFrom ∧ content muFrom.length m = muFrom) :
    elim.matOneValue (elim.transposeM (matUnitAt muTo muFrom i j))
      (matUnitAt muFrom muTo j i) := by
  have hML : (matUnitAt muTo muFrom i j).length
      = (monomialsAt muTo).length := length_matUnitAt muTo muFrom i j
  have hMrows : elim.rowsLen (monomialsAt muFrom).length
      (matUnitAt muTo muFrom i j) := rowsLen_matUnitAt muTo muFrom i j
  have hTlen : (elim.transposeM (matUnitAt muTo muFrom i j)).length
      = (monomialsAt muFrom).length :=
    elim.length_transposeM _ hMrows (by
      rw [hML]
      exact monomialsAt_occupied muTo)
  refine matOneValue_of_rows (monomialsAt muTo).length _ _ ?_ ?_
    (rowsLen_matUnitAt muFrom muTo j i) ?_
  · rw [hTlen, length_matUnitAt]
  · have hr := elim.rowsLen_transposeM
      (matUnitAt muTo muFrom i j)
    rw [hML] at hr
    exact hr
  · intro p hp q hq
    have hpF : p < (monomialsAt muFrom).length := by
      rw [hTlen] at hp
      exact hp
    rw [elim.getAt_transposeM BPair.unit (matUnitAt muTo muFrom i j)
      hMrows p q hpF (by rw [hML]; exact hq)]
    exact BPair.oneValue_trans
      (matUnitAt_read muTo muFrom i j hout q p hq hpF)
      (BPair.oneValue_trans
        (BPair.oneValue_of_eq (congrArg BPair.ofNat
          (countOf_unitAct_swap i j
            (ground.getAt [] (monomialsAt muFrom) p)
            (ground.getAt [] (monomialsAt muTo) q))))
        (BPair.oneValue_symm
          (matUnitAt_read muFrom muTo j i hout' p q hpF hq)))


/-! The exchange tier at the letter pairs: disjoint units commute
outright, and the adjacent pair's raising through lowering against
the lowering through raising exchange at the crossed diagonal
scalars — `con:units`' table read on the coordinate vectors, the
content's letter bound discharging the occupancy scalar at every
letter the enumeration reaches. -/

private theorem dotP_congrL : ∀ r1 r2 x : List BPair,
    r1.length = r2.length →
    (∀ q, q < r1.length →
      (ground.getAt BPair.unit r1 q).oneValue
        (ground.getAt BPair.unit r2 q)) →
    (elim.dotP r1 x).oneValue (elim.dotP r2 x)
  | [], [], _, _, _ => BPair.oneValue_refl _
  | [], _ :: _, _, h, _ => Nat.noConfusion h
  | _ :: _, [], _, h, _ => Nat.noConfusion h
  | _ :: _, _ :: _, [], _, _ => BPair.oneValue_refl _
  | _ :: r1', _ :: r2', b :: x', h, hent =>
    BPair.add_congr
      (BPair.mul_congr (hent 0 (Nat.succ_pos _))
        (BPair.oneValue_refl b))
      (dotP_congrL r1' r2' x' (Nat.succ.inj h)
        (fun q hq => hent (q + 1) (Nat.succ_lt_succ hq)))

private theorem dotP_cross (c1 c2 : BPair) :
    ∀ (t : Nat) (r1 r2 x : List BPair), t < r1.length →
      r1.length = r2.length →
      (ground.getAt BPair.unit r1 t + c1).oneValue
        (ground.getAt BPair.unit r2 t + c2) →
      (∀ s, s < r1.length → ¬ s = t →
        (ground.getAt BPair.unit r1 s).oneValue
          (ground.getAt BPair.unit r2 s)) →
      (elim.dotP r1 x + c1 * ground.getAt BPair.unit x t).oneValue
        (elim.dotP r2 x + c2 * ground.getAt BPair.unit x t)
  | t, [], _, _, ht, _, _, _ => absurd ht (Nat.not_lt_zero t)
  | _, _ :: _, [], _, _, hl, _, _ => Nat.noConfusion hl
  | _, _ :: _, _ :: _, [], _, _, _, _ =>
    BPair.oneValue_trans
      (BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl BPair.unit)
          (BPair.mul_unit c1))
        (BPair.add_unit BPair.unit))
      (BPair.oneValue_symm
        (BPair.oneValue_trans
          (BPair.add_congr (BPair.oneValue_refl BPair.unit)
            (BPair.mul_unit c2))
          (BPair.add_unit BPair.unit)))
  | 0, _ :: r1', _ :: r2', b :: x', _, hl, hhit, hoff => by
    have hIH := dotP_congrL r1' r2' x' (Nat.succ.inj hl)
      (fun q hq => hoff (q + 1) (Nat.succ_lt_succ hq)
        (fun hc => Nat.noConfusion hc))
    have e1 : ∀ a c : BPair, a * b + elim.dotP r1' x' + c * b
        = (a + c) * b + elim.dotP r1' x' := by
      intro a c
      rw [BPair.add_assoc,
        BPair.add_comm (elim.dotP r1' x') (c * b),
        ← BPair.add_assoc, ← BPair.right_distrib]
    have e2 : ∀ a c : BPair, a * b + elim.dotP r2' x' + c * b
        = (a + c) * b + elim.dotP r2' x' := by
      intro a c
      rw [BPair.add_assoc,
        BPair.add_comm (elim.dotP r2' x') (c * b),
        ← BPair.add_assoc, ← BPair.right_distrib]
    rw [show elim.dotP (_ :: r1') (b :: x')
        = _ * b + elim.dotP r1' x' from rfl,
      show elim.dotP (_ :: r2') (b :: x')
        = _ * b + elim.dotP r2' x' from rfl,
      show ground.getAt BPair.unit (b :: x') 0 = b from rfl,
      e1 _ c1, e2 _ c2]
    exact BPair.add_congr
      (BPair.mul_congr hhit (BPair.oneValue_refl b)) hIH
  | n + 1, a1 :: r1', a2 :: r2', b :: x', ht, hl, hhit, hoff => by
    have hIH := dotP_cross c1 c2 n r1' r2' x'
      (Nat.lt_of_succ_lt_succ ht) (Nat.succ.inj hl) hhit
      (fun s hs hne => hoff (s + 1) (Nat.succ_lt_succ hs)
        (fun hc => hne (Nat.succ.inj hc)))
    show (a1 * b + elim.dotP r1' x'
        + c1 * ground.getAt BPair.unit x' n).oneValue
      (a2 * b + elim.dotP r2' x'
        + c2 * ground.getAt BPair.unit x' n)
    rw [BPair.add_assoc, BPair.add_assoc]
    exact BPair.add_congr
      (BPair.mul_congr
        (hoff 0 (Nat.succ_pos _) (fun hc => Nat.noConfusion hc))
        (BPair.oneValue_refl b)) hIH

private theorem cross_rows (MA MB : elim.Mat) (c1 c2 : BPair)
    (n : Nat) (x : List BPair) (hla : MA.length = n)
    (hlb : MB.length = n) (hra : elim.rowsLen n MA)
    (hrb : elim.rowsLen n MB) (hx : x.length = n)
    (hhit : ∀ p, p < n →
      (ground.getAt BPair.unit (ground.getAt [] MA p) p
          + c1).oneValue
        (ground.getAt BPair.unit (ground.getAt [] MB p) p + c2))
    (hoff : ∀ p, p < n → ∀ q, q < n → ¬ q = p →
      (ground.getAt BPair.unit (ground.getAt [] MA p) q).oneValue
        (ground.getAt BPair.unit (ground.getAt [] MB p) q)) :
    poly.oneValue
      (elim.vecAdd (elim.matVec MA x) (elim.vecScale c1 x))
      (elim.vecAdd (elim.matVec MB x) (elim.vecScale c2 x)) := by
  have hsc : ∀ c : BPair, (elim.vecScale c x).length = n := by
    intro c
    show (x.map (fun y => c * y)).length = n
    rw [ground.length_map, hx]
  have hA : (elim.matVec MA x).length
      = (elim.vecScale c1 x).length := by
    rw [elim.matVec_length, hla, hsc]
  have hB : (elim.matVec MB x).length
      = (elim.vecScale c2 x).length := by
    rw [elim.matVec_length, hlb, hsc]
  refine poly.oneValue_of_entries _ _ ?_ (fun p hp => ?_)
  · rw [elim.length_vecAdd _ _ _ rfl hA.symm,
      elim.length_vecAdd _ _ _ rfl hB.symm,
      elim.matVec_length, elim.matVec_length, hla, hlb]
  · have hpn : p < n := by
      rw [elim.length_vecAdd _ _ _ rfl hA.symm, elim.matVec_length,
        hla] at hp
      exact hp
    have hpA : p < (elim.matVec MA x).length := by
      rw [elim.matVec_length, hla]
      exact hpn
    have hpB : p < (elim.matVec MB x).length := by
      rw [elim.matVec_length, hlb]
      exact hpn
    have hpx : p < x.length := by
      rw [hx]
      exact hpn
    have hrowa : (ground.getAt [] MA p).length = n :=
      elim.rowsLen_getAt MA p hra (by rw [hla]; exact hpn)
    have hrowb : (ground.getAt [] MB p).length = n :=
      elim.rowsLen_getAt MB p hrb (by rw [hlb]; exact hpn)
    rw [elim.getAt_vecAdd _ _ p hpA (by rw [hsc]; exact hpn),
      elim.getAt_vecAdd _ _ p hpB (by rw [hsc]; exact hpn),
      elim.getAt_matVec MA x p (by rw [hla]; exact hpn),
      elim.getAt_matVec MB x p (by rw [hlb]; exact hpn),
      show elim.vecScale c1 x = x.map (fun y => c1 * y) from rfl,
      show elim.vecScale c2 x = x.map (fun y => c2 * y) from rfl,
      ground.getAt_map BPair.unit BPair.unit (fun y => c1 * y) x p
        hpx,
      ground.getAt_map BPair.unit BPair.unit (fun y => c2 * y) x p
        hpx]
    exact BPair.oneValue_trans
      (BPair.add_congr (elim.dotN_read _ _) (BPair.oneValue_refl _))
      (BPair.oneValue_trans
        (dotP_cross c1 c2 p (ground.getAt [] MA p)
          (ground.getAt [] MB p) x (by rw [hrowa]; exact hpn)
          (by rw [hrowa, hrowb]) (hhit p hpn)
          (fun s hs hne =>
            hoff p hpn s (by rw [hrowa] at hs; exact hs) hne))
        (BPair.add_congr
          (BPair.oneValue_symm (elim.dotN_read _ _))
          (BPair.oneValue_refl _)))

private theorem getAt_beyond {α : Type} (d : α) :
    ∀ (l : List α) (i : Nat), ¬ i < l.length →
      ground.getAt d l i = d
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd (Nat.succ_pos _) h
  | _ :: t, i + 1, h =>
    getAt_beyond d t i (fun hlt => h (Nat.succ_lt_succ hlt))

private theorem count_read (mu : List Nat) (p : Nat) (s : List Nat)
    (hl : s.length = sumNat mu) (hc : content mu.length s = mu) :
    ground.countOf p s = ground.getAt 0 mu p := by
  by_cases hp : p < mu.length
  · rw [← hc,
      show content mu.length s
        = (List.range mu.length).map
          (fun t => ground.countOf t s) from rfl,
      ground.getAt_map 0 0 (fun t => ground.countOf t s)
        (List.range mu.length) p (by rw [length_range]; exact hp),
      getAt_range mu.length p hp]
  · rw [getAt_beyond 0 mu p hp]
    match Nat.eq_zero_or_pos (ground.countOf p s) with
    | .inl hz => exact hz
    | .inr hpos =>
      exact absurd (places.mem_lt_of_content mu.length s
        (by rw [hc]; exact hl.symm) p hpos) hp

/-- Disjoint units commute: at letters off both delta conditions
the two composition orders read one value (`con:units`' table). -/
theorem matVec_swap_read (muA muB muTo muFrom : List Nat)
    (a b c d : Nat) (had : ¬ a = d) (hcb : ¬ c = b)
    (hCD : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct c d s) →
      m.length = sumNat muA ∧ content muA.length m = muA)
    (hAB : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muA) →
      0 < ground.countOf m (unitAct a b s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (hAB' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct a b s) →
      m.length = sumNat muB ∧ content muB.length m = muB)
    (hCD' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muB) →
      0 < ground.countOf m (unitAct c d s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (x : List BPair) (hx : x.length = (monomialsAt muFrom).length) :
    poly.oneValue
      (elim.matVec (matUnitAt muTo muA a b)
        (elim.matVec (matUnitAt muA muFrom c d) x))
      (elim.matVec (matUnitAt muTo muB c d)
        (elim.matVec (matUnitAt muB muFrom a b) x)) := by
  have honeCD : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct c d s) →
      ground.countOf m (monomialsAt muA) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muA m, if_pos (hCD s m hs hm)]
  have honeAB : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct a b s) →
      ground.countOf m (monomialsAt muB) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muB m, if_pos (hAB' s m hs hm)]
  have hf0 : 0 < (matUnitAt muA muFrom c d).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muA
  have hf0' : 0 < (matUnitAt muB muFrom a b).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muB
  have hAmv : poly.oneValue
      (elim.matVec (matUnitAt muTo muA a b)
        (elim.matVec (matUnitAt muA muFrom c d) x))
      (elim.matVec (elim.matMul (matUnitAt muTo muA a b)
        (matUnitAt muA muFrom c d)) x) :=
    elim.matVec_comp _ _ x (monomialsAt muFrom).length
      (rowsLen_matUnitAt muA muFrom c d) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt muTo muA a b)
  have hBmv : poly.oneValue
      (elim.matVec (matUnitAt muTo muB c d)
        (elim.matVec (matUnitAt muB muFrom a b) x))
      (elim.matVec (elim.matMul (matUnitAt muTo muB c d)
        (matUnitAt muB muFrom a b)) x) :=
    elim.matVec_comp _ _ x (monomialsAt muFrom).length
      (rowsLen_matUnitAt muB muFrom a b) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt muTo muB c d)
  refine poly.oneValue_trans hAmv
    (poly.oneValue_trans ?_ (poly.oneValue_symm hBmv))
  refine elim.matVec_rows_congr (monomialsAt muFrom).length _ _
    (by rw [elim.length_matMul, length_matUnitAt,
      elim.length_matMul, length_matUnitAt])
    (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muA muFrom c d) hf0)
    (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muB muFrom a b) hf0')
    (fun p hp q hq => ?_) x
  have hp' : p < (monomialsAt muTo).length := by
    rw [elim.length_matMul, length_matUnitAt] at hp
    exact hp
  have hac := act_comm a b c d
    (ground.getAt [] (monomialsAt muFrom) q)
    (ground.getAt [] (monomialsAt muTo) p)
  rw [if_neg (fun hcc => had (ground.beqEqOf hcc)),
    if_neg (fun hcc => hcb (ground.beqEqOf hcc)),
    Nat.add_zero, Nat.add_zero] at hac
  exact BPair.oneValue_trans
    (matUnit_comp_read muTo muA muFrom a b c d honeCD hAB p q hp' hq)
    (BPair.oneValue_trans
      (BPair.oneValue_of_eq (congrArg BPair.ofNat hac))
      (BPair.oneValue_symm
        (matUnit_comp_read muTo muB muFrom c d a b honeAB hCD'
          p q hp' hq)))

/-! The table's join, uniform: `con:units`' display transcribed
once at the vector level, the two guarded delta terms entering
where the letters coincide.  `matVec_swap_read` above is its
dead-delta instance (both guards refused, the replicate terms the
sum's unit); the pair reads are its live-delta ones at the shared
letters.  The proof is `act_comm`'s own count identity lifted entry
by entry — the composed product's read on each side and the delta
matrix's own, the refused guard's null matrix reading the count
zero. -/

/-- The delta term's matrix at a guard: the unit matrix where the
letters coincide, the null matrix where they do not. -/
private def delMat (muTo muFrom : List Nat) (g : Prop) [Decidable g]
    (e f : Nat) : elim.Mat :=
  if g then matUnitAt muTo muFrom e f
  else List.replicate (monomialsAt muTo).length
    (List.replicate (monomialsAt muFrom).length BPair.unit)

private theorem length_delMat (muTo muFrom : List Nat) (g : Prop)
    [Decidable g] (e f : Nat) :
    (delMat muTo muFrom g e f).length
      = (monomialsAt muTo).length := by
  show (if g then matUnitAt muTo muFrom e f
    else List.replicate (monomialsAt muTo).length
      (List.replicate (monomialsAt muFrom).length
        BPair.unit)).length = _
  by_cases hgv : g
  · rw [if_pos hgv]
    exact length_matUnitAt muTo muFrom e f
  · rw [if_neg hgv]
    exact ground.length_replicate _ _

private theorem rowsLen_delMat (muTo muFrom : List Nat) (g : Prop)
    [Decidable g] (e f : Nat) :
    elim.rowsLen (monomialsAt muFrom).length
      (delMat muTo muFrom g e f) := by
  show elim.rowsLen (monomialsAt muFrom).length
    (if g then matUnitAt muTo muFrom e f
      else List.replicate (monomialsAt muTo).length
        (List.replicate (monomialsAt muFrom).length BPair.unit))
  by_cases hgv : g
  · rw [if_pos hgv]
    exact rowsLen_matUnitAt muTo muFrom e f
  · rw [if_neg hgv]
    exact elim.rowsLen_replicate (monomialsAt muFrom).length _

private theorem entry_delMat (muTo muFrom : List Nat) (g : Prop)
    [Decidable g] (e f : Nat)
    (hout : g → ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct e f s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (p q : Nat) (hp : p < (monomialsAt muTo).length)
    (hq : q < (monomialsAt muFrom).length) :
    (ground.getAt BPair.unit
        (ground.getAt [] (delMat muTo muFrom g e f) p) q).oneValue
      (BPair.ofNat (if g then ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (unitAct e f (ground.getAt [] (monomialsAt muFrom) q))
        else 0)) := by
  show (ground.getAt BPair.unit (ground.getAt []
      (if g then matUnitAt muTo muFrom e f
        else List.replicate (monomialsAt muTo).length
          (List.replicate (monomialsAt muFrom).length BPair.unit))
      p) q).oneValue _
  by_cases hgv : g
  · rw [if_pos hgv, if_pos hgv]
    exact matUnitAt_read muTo muFrom e f (hout hgv) p q hp hq
  · rw [if_neg hgv, if_neg hgv,
      ground.getAt_replicate ([] : List BPair) _ _ p hp,
      ground.getAt_replicate BPair.unit _ _ q hq]
    exact BPair.oneValue_refl _

private theorem vec_delMat (muTo muFrom : List Nat) (g : Prop)
    [Decidable g] (e f : Nat) (x : List BPair) :
    poly.oneValue
      (if g then elim.matVec (matUnitAt muTo muFrom e f) x
        else List.replicate (monomialsAt muTo).length BPair.unit)
      (elim.matVec (delMat muTo muFrom g e f) x) := by
  show poly.oneValue _ (elim.matVec (if g then
    matUnitAt muTo muFrom e f
    else List.replicate (monomialsAt muTo).length
      (List.replicate (monomialsAt muFrom).length BPair.unit)) x)
  by_cases hgv : g
  · rw [if_pos hgv, if_pos hgv]
    exact poly.oneValue_refl _
  · rw [if_neg hgv, if_neg hgv]
    exact poly.unitTail_oneValue (poly.unitTail_replicate _)
      (elim.matVec_replicate_null _ _ x)

private theorem lenVec_delMat (muTo muFrom : List Nat) (g : Prop)
    [Decidable g] (e f : Nat) (x : List BPair) :
    (if g then elim.matVec (matUnitAt muTo muFrom e f) x
      else List.replicate (monomialsAt muTo).length
        BPair.unit).length = (monomialsAt muTo).length := by
  by_cases hgv : g
  · rw [if_pos hgv, elim.matVec_length]
    exact length_matUnitAt muTo muFrom e f
  · rw [if_neg hgv]
    exact ground.length_replicate _ _

private theorem add_rows (MA MC MB MD : elim.Mat) (n L : Nat)
    (x : List BPair) (hx : x.length = n)
    (hla : MA.length = L) (hlc : MC.length = L)
    (hlb : MB.length = L) (hld : MD.length = L)
    (hra : elim.rowsLen n MA) (hrc : elim.rowsLen n MC)
    (hrb : elim.rowsLen n MB) (hrd : elim.rowsLen n MD)
    (hent : ∀ p, p < L → ∀ q, q < n →
      (ground.getAt BPair.unit (ground.getAt [] MA p) q
          + ground.getAt BPair.unit
            (ground.getAt [] MC p) q).oneValue
        (ground.getAt BPair.unit (ground.getAt [] MB p) q
          + ground.getAt BPair.unit
            (ground.getAt [] MD p) q)) :
    poly.oneValue
      (elim.vecAdd (elim.matVec MA x) (elim.matVec MC x))
      (elim.vecAdd (elim.matVec MB x) (elim.matVec MD x)) := by
  have hAC : (elim.matVec MA x).length
      = (elim.matVec MC x).length := by
    rw [elim.matVec_length, elim.matVec_length, hla, hlc]
  have hBD : (elim.matVec MB x).length
      = (elim.matVec MD x).length := by
    rw [elim.matVec_length, elim.matVec_length, hlb, hld]
  refine poly.oneValue_of_entries _ _ ?_ (fun p hp => ?_)
  · rw [elim.length_vecAdd _ _ _ rfl hAC.symm,
      elim.length_vecAdd _ _ _ rfl hBD.symm,
      elim.matVec_length, elim.matVec_length, hla, hlb]
  · have hpL : p < L := by
      rw [elim.length_vecAdd _ _ _ rfl hAC.symm, elim.matVec_length,
        hla] at hp
      exact hp
    have hrow : ∀ (M : elim.Mat), M.length = L →
        elim.rowsLen n M →
        (ground.getAt ([] : List BPair) M p).length = x.length := by
      intro M hl hr
      rw [elim.rowsLen_getAt M p hr (by rw [hl]; exact hpL), hx]
    have hwid : ∀ (M : elim.Mat), M.length = L →
        elim.rowsLen n M →
        (ground.getAt ([] : List BPair) M p).length = n :=
      fun M hl hr => elim.rowsLen_getAt M p hr (by rw [hl]; exact hpL)
    have hsplit : ∀ (M M' : elim.Mat), M.length = L →
        M'.length = L →
        elim.rowsLen n M → elim.rowsLen n M' →
        (ground.getAt BPair.unit
            (elim.vecAdd (elim.matVec M x) (elim.matVec M' x))
            p).oneValue
          (elim.dotP (elim.vecAdd (ground.getAt [] M p)
            (ground.getAt [] M' p)) x) := by
      intro M M' hl hl' hr hr'
      rw [elim.getAt_vecAdd _ _ p
          (by rw [elim.matVec_length, hl]; exact hpL)
          (by rw [elim.matVec_length, hl']; exact hpL),
        elim.getAt_matVec M x p (by rw [hl]; exact hpL),
        elim.getAt_matVec M' x p (by rw [hl']; exact hpL)]
      refine BPair.oneValue_symm (BPair.oneValue_trans
        (elim.dotP_vecAdd_left _ _ x
          (Nat.le_of_eq (Eq.symm (hrow M hl hr)))
          (Nat.le_of_eq (Eq.symm (hrow M' hl' hr')))) ?_)
      exact BPair.add_congr
        (BPair.oneValue_symm (elim.dotN_read _ x))
        (BPair.oneValue_symm (elim.dotN_read _ x))
    refine BPair.oneValue_trans (hsplit MA MC hla hlc hra hrc) ?_
    refine BPair.oneValue_trans ?_
      (BPair.oneValue_symm (hsplit MB MD hlb hld hrb hrd))
    refine dotP_congrL _ _ x ?_ (fun q hq => ?_)
    · rw [elim.length_vecAdd _ _ _ rfl
        ((hwid MC hlc hrc).trans (hwid MA hla hra).symm),
        elim.length_vecAdd _ _ _ rfl
          ((hwid MD hld hrd).trans (hwid MB hlb hrb).symm),
        hwid MA hla hra, hwid MB hlb hrb]
    · have hqn : q < n := by
        rw [elim.length_vecAdd _ _ _ rfl
            ((hwid MC hlc hrc).trans (hwid MA hla hra).symm),
          hwid MA hla hra] at hq
        exact hq
      rw [elim.getAt_vecAdd _ _ q
          (by rw [hwid MA hla hra]; exact hqn)
          (by rw [hwid MC hlc hrc]; exact hqn),
        elim.getAt_vecAdd _ _ q
          (by rw [hwid MB hlb hrb]; exact hqn)
          (by rw [hwid MD hld hrd]; exact hqn)]
      exact hent p hpL q hqn

/-- `con:units`' table at the coordinate vectors, uniform: the two
composition orders join at the guarded delta terms,
`E_{ab} E_{cd} + δ_{ad} E_{cb} = E_{cd} E_{ab} + δ_{bc} E_{ad}`,
each delta's content hypothesis taken only where its letters
coincide.  `matVec_swap_read` is the dead-delta instance. -/
theorem matVec_table_read (muA muB muTo muFrom : List Nat)
    (a b c d : Nat)
    (hCD : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct c d s) →
      m.length = sumNat muA ∧ content muA.length m = muA)
    (hAB : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muA) →
      0 < ground.countOf m (unitAct a b s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (hAB' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct a b s) →
      m.length = sumNat muB ∧ content muB.length m = muB)
    (hCD' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muB) →
      0 < ground.countOf m (unitAct c d s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (hAD : a = d → ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct c b s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (hBC : b = c → ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct a d s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo)
    (x : List BPair) (hx : x.length = (monomialsAt muFrom).length) :
    poly.oneValue
      (elim.vecAdd
        (elim.matVec (matUnitAt muTo muA a b)
          (elim.matVec (matUnitAt muA muFrom c d) x))
        (if a = d then elim.matVec (matUnitAt muTo muFrom c b) x
          else List.replicate (monomialsAt muTo).length
            BPair.unit))
      (elim.vecAdd
        (elim.matVec (matUnitAt muTo muB c d)
          (elim.matVec (matUnitAt muB muFrom a b) x))
        (if b = c then elim.matVec (matUnitAt muTo muFrom a d) x
          else List.replicate (monomialsAt muTo).length
            BPair.unit)) := by
  have honeCD : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct c d s) →
      ground.countOf m (monomialsAt muA) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muA m, if_pos (hCD s m hs hm)]
  have honeAB : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct a b s) →
      ground.countOf m (monomialsAt muB) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muB m, if_pos (hAB' s m hs hm)]
  have hf0 : 0 < (matUnitAt muA muFrom c d).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muA
  have hf0' : 0 < (matUnitAt muB muFrom a b).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muB
  have hAmv : poly.oneValue
      (elim.matVec (matUnitAt muTo muA a b)
        (elim.matVec (matUnitAt muA muFrom c d) x))
      (elim.matVec (elim.matMul (matUnitAt muTo muA a b)
        (matUnitAt muA muFrom c d)) x) :=
    elim.matVec_comp _ _ x (monomialsAt muFrom).length
      (rowsLen_matUnitAt muA muFrom c d) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt muTo muA a b)
  have hBmv : poly.oneValue
      (elim.matVec (matUnitAt muTo muB c d)
        (elim.matVec (matUnitAt muB muFrom a b) x))
      (elim.matVec (elim.matMul (matUnitAt muTo muB c d)
        (matUnitAt muB muFrom a b)) x) :=
    elim.matVec_comp _ _ x (monomialsAt muFrom).length
      (rowsLen_matUnitAt muB muFrom a b) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt muTo muB c d)
  refine poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      hAmv (vec_delMat muTo muFrom (a = d) c b x)
      (by rw [elim.matVec_length, elim.matVec_length,
        elim.length_matMul])
      ((lenVec_delMat muTo muFrom (a = d) c b x).trans
        (by rw [elim.matVec_length, length_delMat]))) ?_
  refine poly.oneValue_trans ?_
    (poly.oneValue_symm (elim.polyOne_vecAdd _ _ _ _
      hBmv (vec_delMat muTo muFrom (b = c) a d x)
      (by rw [elim.matVec_length, elim.matVec_length,
        elim.length_matMul])
      ((lenVec_delMat muTo muFrom (b = c) a d x).trans
        (by rw [elim.matVec_length, length_delMat]))))
  refine add_rows _ _ _ _ (monomialsAt muFrom).length
    (monomialsAt muTo).length x hx
    (by rw [elim.length_matMul, length_matUnitAt])
    (length_delMat muTo muFrom (a = d) c b)
    (by rw [elim.length_matMul, length_matUnitAt])
    (length_delMat muTo muFrom (b = c) a d)
    (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muA muFrom c d) hf0)
    (rowsLen_delMat muTo muFrom (a = d) c b)
    (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muB muFrom a b) hf0')
    (rowsLen_delMat muTo muFrom (b = c) a d)
    (fun p hp q hq => ?_)
  have hac := act_comm a b c d
    (ground.getAt [] (monomialsAt muFrom) q)
    (ground.getAt [] (monomialsAt muTo) p)
  refine BPair.oneValue_trans
    (BPair.add_congr
      (matUnit_comp_read muTo muA muFrom a b c d honeCD hAB
        p q hp hq)
      (entry_delMat muTo muFrom (a = d) c b hAD p q hp hq)) ?_
  refine BPair.oneValue_trans ?_
    (BPair.oneValue_symm (BPair.add_congr
      (matUnit_comp_read muTo muB muFrom c d a b honeAB hCD'
        p q hp hq)
      (entry_delMat muTo muFrom (b = c) a d hBC p q hp hq)))
  refine BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.ofNat_add _ _)) ?_
  refine BPair.oneValue_trans ?_ (BPair.ofNat_add _ _)
  refine BPair.oneValue_of_eq (congrArg BPair.ofNat ?_)
  rw [show (if a = d then ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (unitAct c b (ground.getAt [] (monomialsAt muFrom) q))
      else 0)
      = (if a == d then ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (unitAct c b (ground.getAt [] (monomialsAt muFrom) q))
      else 0) from by
      by_cases hgv : a = d
      · rw [if_pos hgv, if_pos (ground.eqBeqOf hgv)]
      · rw [if_neg hgv, if_neg (fun hb => hgv (ground.beqEqOf hb))],
    show (if b = c then ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (unitAct a d (ground.getAt [] (monomialsAt muFrom) q))
      else 0)
      = (if c == b then ground.countOf
        (ground.getAt [] (monomialsAt muTo) p)
        (unitAct a d (ground.getAt [] (monomialsAt muFrom) q))
      else 0) from by
      by_cases hgv : b = c
      · rw [if_pos hgv, if_pos (ground.eqBeqOf hgv.symm)]
      · rw [if_neg hgv,
          if_neg (fun hb => hgv (ground.beqEqOf hb).symm)]]
  exact hac

/-- The adjacent pair's exchange: the raising through the lowering
against the lowering through the raising, the two diagonal scalars
crossed — `[E, F] = H` at the letter pair, the round trip reading
the source content (`con:units`' table). -/
theorem matVec_pair_read (mu muA muB : List Nat) (j : Nat)
    (hDn : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct (j + 1) j s) →
      m.length = sumNat muA ∧ content muA.length m = muA)
    (hUp : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muA) →
      0 < ground.countOf m (unitAct j (j + 1) s) →
      m.length = sumNat mu ∧ content mu.length m = mu)
    (hUp' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct j (j + 1) s) →
      m.length = sumNat muB ∧ content muB.length m = muB)
    (hDn' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muB) →
      0 < ground.countOf m (unitAct (j + 1) j s) →
      m.length = sumNat mu ∧ content mu.length m = mu)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    poly.oneValue
      (elim.vecAdd
        (elim.matVec (matUnitAt mu muA j (j + 1))
          (elim.matVec (matUnitAt muA mu (j + 1) j) x))
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 mu (j + 1))) x))
      (elim.vecAdd
        (elim.matVec (matUnitAt mu muB (j + 1) j)
          (elim.matVec (matUnitAt muB mu j (j + 1)) x))
        (elim.vecScale (BPair.ofNat (ground.getAt 0 mu j)) x)) := by
  have hmem : ∀ s : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      s.length = sumNat mu ∧ content mu.length s = mu := by
    intro s hs
    rw [countOf_monomialsAt mu s] at hs
    by_cases hcc : s.length = sumNat mu ∧ content mu.length s = mu
    · exact hcc
    · rw [if_neg hcc] at hs
      exact absurd hs (Nat.lt_irrefl 0)
  have honeDn : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct (j + 1) j s) →
      ground.countOf m (monomialsAt muA) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muA m, if_pos (hDn s m hs hm)]
  have honeUp : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct j (j + 1) s) →
      ground.countOf m (monomialsAt muB) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muB m, if_pos (hUp' s m hs hm)]
  have hf0 : 0 < (matUnitAt muA mu (j + 1) j).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muA
  have hf0' : 0 < (matUnitAt muB mu j (j + 1)).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muB
  have hAmv : poly.oneValue
      (elim.matVec (matUnitAt mu muA j (j + 1))
        (elim.matVec (matUnitAt muA mu (j + 1) j) x))
      (elim.matVec (elim.matMul (matUnitAt mu muA j (j + 1))
        (matUnitAt muA mu (j + 1) j)) x) :=
    elim.matVec_comp _ _ x (monomialsAt mu).length
      (rowsLen_matUnitAt muA mu (j + 1) j) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt mu muA j (j + 1))
  have hBmv : poly.oneValue
      (elim.matVec (matUnitAt mu muB (j + 1) j)
        (elim.matVec (matUnitAt muB mu j (j + 1)) x))
      (elim.matVec (elim.matMul (matUnitAt mu muB (j + 1) j)
        (matUnitAt muB mu j (j + 1))) x) :=
    elim.matVec_comp _ _ x (monomialsAt mu).length
      (rowsLen_matUnitAt muB mu j (j + 1)) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt mu muB (j + 1) j)
  have hcore : poly.oneValue
      (elim.vecAdd
        (elim.matVec (elim.matMul (matUnitAt mu muA j (j + 1))
          (matUnitAt muA mu (j + 1) j)) x)
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 mu (j + 1))) x))
      (elim.vecAdd
        (elim.matVec (elim.matMul (matUnitAt mu muB (j + 1) j)
          (matUnitAt muB mu j (j + 1))) x)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 mu j)) x)) := by
    refine cross_rows _ _ _ _ (monomialsAt mu).length x
      (by rw [elim.length_matMul, length_matUnitAt])
      (by rw [elim.length_matMul, length_matUnitAt])
      (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muA mu (j + 1) j)
        hf0)
      (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muB mu j (j + 1))
        hf0')
      hx (fun p hp => ?_) (fun p hp q hq hne => ?_)
    · have hmp : 0 < ground.countOf
          (ground.getAt [] (monomialsAt mu) p) (monomialsAt mu) :=
        ground.countOf_getAt_pos [] (monomialsAt mu) p hp
      have hcm := hmem _ hmp
      have hac := act_comm j (j + 1) (j + 1) j
        (ground.getAt [] (monomialsAt mu) p)
        (ground.getAt [] (monomialsAt mu) p)
      rw [if_pos (ground.eqBeqOf (rfl : j = j)),
        if_pos (ground.eqBeqOf (rfl : j + 1 = j + 1)),
        countOf_unitAct_diag (j + 1)
          (ground.getAt [] (monomialsAt mu) p)
          (ground.getAt [] (monomialsAt mu) p), if_pos rfl,
        countOf_unitAct_diag j
          (ground.getAt [] (monomialsAt mu) p)
          (ground.getAt [] (monomialsAt mu) p), if_pos rfl,
        count_read mu (j + 1) _ hcm.1 hcm.2,
        count_read mu j _ hcm.1 hcm.2] at hac
      exact BPair.oneValue_trans
        (BPair.add_congr
          (matUnit_comp_read mu muA mu j (j + 1) (j + 1) j
            honeDn hUp p p hp hp)
          (BPair.oneValue_refl _))
        (BPair.oneValue_trans
          (BPair.oneValue_symm (BPair.ofNat_add _ _))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (congrArg BPair.ofNat hac))
            (BPair.oneValue_trans (BPair.ofNat_add _ _)
              (BPair.add_congr
                (BPair.oneValue_symm
                  (matUnit_comp_read mu muB mu (j + 1) j j (j + 1)
                    honeUp hDn' p p hp hp))
                (BPair.oneValue_refl _)))))
    · have hne' : ¬ ground.getAt [] (monomialsAt mu) p
          = ground.getAt [] (monomialsAt mu) q := fun hcc =>
        hne (ground.getAt_inj_distinct [] (monomialsAt mu)
          (monomialsAt_distinct mu) p q hp hq hcc).symm
      have hac := act_comm j (j + 1) (j + 1) j
        (ground.getAt [] (monomialsAt mu) q)
        (ground.getAt [] (monomialsAt mu) p)
      rw [if_pos (ground.eqBeqOf (rfl : j = j)),
        if_pos (ground.eqBeqOf (rfl : j + 1 = j + 1)),
        countOf_unitAct_diag (j + 1)
          (ground.getAt [] (monomialsAt mu) q)
          (ground.getAt [] (monomialsAt mu) p), if_neg hne',
        countOf_unitAct_diag j
          (ground.getAt [] (monomialsAt mu) q)
          (ground.getAt [] (monomialsAt mu) p), if_neg hne',
        Nat.add_zero, Nat.add_zero] at hac
      exact BPair.oneValue_trans
        (matUnit_comp_read mu muA mu j (j + 1) (j + 1) j
          honeDn hUp p q hp hq)
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (congrArg BPair.ofNat hac))
          (BPair.oneValue_symm
            (matUnit_comp_read mu muB mu (j + 1) j j (j + 1)
              honeUp hDn' p q hp hq)))
  exact poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      hAmv (poly.oneValue_refl _)
      (by rw [elim.matVec_length, elim.matVec_length,
        elim.length_matMul])
      rfl)
    (poly.oneValue_trans hcore
      (elim.polyOne_vecAdd _ _ _ _
        (poly.oneValue_symm hBmv) (poly.oneValue_refl _)
        (by
          rw [elim.matVec_length, elim.matVec_length,
            elim.length_matMul])
        rfl))


/-- The general pair's exchange: the raising through the lowering
against the lowering through the raising at any two distinct
letters, the two diagonal scalars crossed, the round trip reading
the source content (`con:units`' table, the adjacent read's
generalization). -/
theorem matVec_gpair_read (mu muA muB : List Nat) (i j : Nat)
    (hDn : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct j i s) →
      m.length = sumNat muA ∧ content muA.length m = muA)
    (hUp : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muA) →
      0 < ground.countOf m (unitAct i j s) →
      m.length = sumNat mu ∧ content mu.length m = mu)
    (hUp' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct i j s) →
      m.length = sumNat muB ∧ content muB.length m = muB)
    (hDn' : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muB) →
      0 < ground.countOf m (unitAct j i s) →
      m.length = sumNat mu ∧ content mu.length m = mu)
    (x : List BPair) (hx : x.length = (monomialsAt mu).length) :
    poly.oneValue
      (elim.vecAdd
        (elim.matVec (matUnitAt mu muA i j)
          (elim.matVec (matUnitAt muA mu j i) x))
        (elim.vecScale (BPair.ofNat (ground.getAt 0 mu j)) x))
      (elim.vecAdd
        (elim.matVec (matUnitAt mu muB j i)
          (elim.matVec (matUnitAt muB mu i j) x))
        (elim.vecScale (BPair.ofNat (ground.getAt 0 mu i)) x)) := by
  have hmem : ∀ s : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      s.length = sumNat mu ∧ content mu.length s = mu := by
    intro s hs
    rw [countOf_monomialsAt mu s] at hs
    by_cases hcc : s.length = sumNat mu ∧ content mu.length s = mu
    · exact hcc
    · rw [if_neg hcc] at hs
      exact absurd hs (Nat.lt_irrefl 0)
  have honeDn : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct j i s) →
      ground.countOf m (monomialsAt muA) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muA m, if_pos (hDn s m hs hm)]
  have honeUp : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt mu) →
      0 < ground.countOf m (unitAct i j s) →
      ground.countOf m (monomialsAt muB) = 1 := by
    intro s m hs hm
    rw [countOf_monomialsAt muB m, if_pos (hUp' s m hs hm)]
  have hf0 : 0 < (matUnitAt muA mu j i).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muA
  have hf0' : 0 < (matUnitAt muB mu i j).length := by
    rw [length_matUnitAt]
    exact monomialsAt_occupied muB
  have hAmv : poly.oneValue
      (elim.matVec (matUnitAt mu muA i j)
        (elim.matVec (matUnitAt muA mu j i) x))
      (elim.matVec (elim.matMul (matUnitAt mu muA i j)
        (matUnitAt muA mu j i)) x) :=
    elim.matVec_comp _ _ x (monomialsAt mu).length
      (rowsLen_matUnitAt muA mu j i) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt mu muA i j)
  have hBmv : poly.oneValue
      (elim.matVec (matUnitAt mu muB j i)
        (elim.matVec (matUnitAt muB mu i j) x))
      (elim.matVec (elim.matMul (matUnitAt mu muB j i)
        (matUnitAt muB mu i j)) x) :=
    elim.matVec_comp _ _ x (monomialsAt mu).length
      (rowsLen_matUnitAt muB mu i j) hx
      (by
        rw [length_matUnitAt]
        exact rowsLen_matUnitAt mu muB j i)
  have hcore : poly.oneValue
      (elim.vecAdd
        (elim.matVec (elim.matMul (matUnitAt mu muA i j)
          (matUnitAt muA mu j i)) x)
        (elim.vecScale
          (BPair.ofNat (ground.getAt 0 mu j)) x))
      (elim.vecAdd
        (elim.matVec (elim.matMul (matUnitAt mu muB j i)
          (matUnitAt muB mu i j)) x)
        (elim.vecScale (BPair.ofNat (ground.getAt 0 mu i)) x)) := by
    refine cross_rows _ _ _ _ (monomialsAt mu).length x
      (by rw [elim.length_matMul, length_matUnitAt])
      (by rw [elim.length_matMul, length_matUnitAt])
      (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muA mu j i)
        hf0)
      (rowsLen_matMul _ _ _ (rowsLen_matUnitAt muB mu i j)
        hf0')
      hx (fun p hp => ?_) (fun p hp q hq hne => ?_)
    · have hmp : 0 < ground.countOf
          (ground.getAt [] (monomialsAt mu) p) (monomialsAt mu) :=
        ground.countOf_getAt_pos [] (monomialsAt mu) p hp
      have hcm := hmem _ hmp
      have hac := act_comm i j j i
        (ground.getAt [] (monomialsAt mu) p)
        (ground.getAt [] (monomialsAt mu) p)
      rw [if_pos (ground.eqBeqOf (rfl : i = i)),
        if_pos (ground.eqBeqOf (rfl : j = j)),
        countOf_unitAct_diag j
          (ground.getAt [] (monomialsAt mu) p)
          (ground.getAt [] (monomialsAt mu) p), if_pos rfl,
        countOf_unitAct_diag i
          (ground.getAt [] (monomialsAt mu) p)
          (ground.getAt [] (monomialsAt mu) p), if_pos rfl,
        count_read mu j _ hcm.1 hcm.2,
        count_read mu i _ hcm.1 hcm.2] at hac
      exact BPair.oneValue_trans
        (BPair.add_congr
          (matUnit_comp_read mu muA mu i j j i
            honeDn hUp p p hp hp)
          (BPair.oneValue_refl _))
        (BPair.oneValue_trans
          (BPair.oneValue_symm (BPair.ofNat_add _ _))
          (BPair.oneValue_trans
            (BPair.oneValue_of_eq (congrArg BPair.ofNat hac))
            (BPair.oneValue_trans (BPair.ofNat_add _ _)
              (BPair.add_congr
                (BPair.oneValue_symm
                  (matUnit_comp_read mu muB mu j i i j
                    honeUp hDn' p p hp hp))
                (BPair.oneValue_refl _)))))
    · have hne' : ¬ ground.getAt [] (monomialsAt mu) p
          = ground.getAt [] (monomialsAt mu) q := fun hcc =>
        hne (ground.getAt_inj_distinct [] (monomialsAt mu)
          (monomialsAt_distinct mu) p q hp hq hcc).symm
      have hac := act_comm i j j i
        (ground.getAt [] (monomialsAt mu) q)
        (ground.getAt [] (monomialsAt mu) p)
      rw [if_pos (ground.eqBeqOf (rfl : i = i)),
        if_pos (ground.eqBeqOf (rfl : j = j)),
        countOf_unitAct_diag j
          (ground.getAt [] (monomialsAt mu) q)
          (ground.getAt [] (monomialsAt mu) p), if_neg hne',
        countOf_unitAct_diag i
          (ground.getAt [] (monomialsAt mu) q)
          (ground.getAt [] (monomialsAt mu) p), if_neg hne',
        Nat.add_zero, Nat.add_zero] at hac
      exact BPair.oneValue_trans
        (matUnit_comp_read mu muA mu i j j i
          honeDn hUp p q hp hq)
        (BPair.oneValue_trans
          (BPair.oneValue_of_eq (congrArg BPair.ofNat hac))
          (BPair.oneValue_symm
            (matUnit_comp_read mu muB mu j i i j
              honeUp hDn' p q hp hq)))
  exact poly.oneValue_trans
    (elim.polyOne_vecAdd _ _ _ _
      hAmv (poly.oneValue_refl _)
      (by rw [elim.matVec_length, elim.matVec_length,
        elim.length_matMul])
      rfl)
    (poly.oneValue_trans hcore
      (elim.polyOne_vecAdd _ _ _ _
        (poly.oneValue_symm hBmv) (poly.oneValue_refl _)
        (by
          rw [elim.matVec_length, elim.matVec_length,
            elim.length_matMul])
        rfl))

/-! The unit matrix's null read: at a consumed letter unoccupied in
the source content no place reads the letter, so the action sits at
the sum's unit at every vector. -/

/-- The vacant content's action reaches no monomial: an occupied
count at the unit-content family's single member forces the vacant
word, whose moved list is vacant in turn. -/
theorem no_out_zero (n i j : Nat) (s m : List Nat)
    (hs : 0 < ground.countOf s
      (places.monomialsAt (List.replicate n 0)))
    (hm : 0 < ground.countOf m (unitAct i j s)) : False := by
  rw [places.monomialsAt_sum_zero _ (sumNat_replicate_zero n)]
    at hs
  have hsnil : s = ([] : List Nat) := by
    by_cases h : s = ([] : List Nat)
    · exact h
    · rw [ground.countOf_cons s ([] : List Nat) ([] : List (List Nat)),
        if_neg h] at hs
      exact absurd hs (Nat.lt_irrefl 0)
  rw [hsnil] at hm
  exact absurd hm (Nat.lt_irrefl 0)

/-- The action at an unoccupied consumed letter is null: every
matrix entry sits at the sum's unit, at every vector. -/
theorem matVec_null_unocc (muTo muFrom : List Nat)
    (i j : Nat) (hz : ground.getAt 0 muFrom j = 0)
    (x : List BPair) :
    poly.unitTail (elim.matVec (matUnitAt muTo muFrom i j) x) := by
  have hzero := places.letter_zero muFrom j hz
  have hout : ∀ s m : List Nat,
      0 < ground.countOf s (monomialsAt muFrom) →
      0 < ground.countOf m (unitAct i j s) →
      m.length = sumNat muTo ∧ content muTo.length m = muTo := by
    intro s m hs hm
    rw [unitAct_nil_of_zero i j s (hzero s hs)] at hm
    exact absurd hm (Nat.lt_irrefl 0)
  refine elim.matVec_unitRows _ _ ?_
  intro p hp
  rw [length_matUnitAt] at hp
  refine elim.unitTail_of_getAt _ ?_
  intro q hq
  rw [elim.rowsLen_getAt _ p (rowsLen_matUnitAt muTo muFrom i j)
      (by rw [length_matUnitAt]; exact hp)] at hq
  refine BPair.oneValue_trans
    (matUnitAt_read muTo muFrom i j hout p q hp hq) ?_
  rw [unitAct_nil_of_zero i j (ground.getAt [] (monomialsAt muFrom) q)
      (hzero _ (ground.countOf_getAt_pos []
        (monomialsAt muFrom) q hq))]
  exact BPair.oneValue_refl BPair.unit

/-! The stacked raisings' frame and its per-raising reads: the
stacked datum's rows at the content's monomial width, and the
stacked action's unit tail read at each occupied adjacent move, in
both directions (`def:blockcount`'s elimination datum against
`con:units`' raisings). -/

/-- The guarded block at a passing guard is the block, at a failing
one the vacant datum. -/
private theorem rowsLen_guard (n : Nat) : ∀ (c : Prop)
    (inst : Decidable c) (M : elim.Mat), elim.rowsLen n M →
    elim.rowsLen n (@ite _ c inst M [])
  | _, isTrue _, _, h => h
  | _, isFalse _, _, _ => trivial

/-- The guarded block's action reads the unit tail where the guard
passes. -/
private theorem matVec_guard_of (x : List BPair) : ∀ (c : Prop)
    (inst : Decidable c) (M : elim.Mat),
    (c → poly.unitTail (elim.matVec M x)) →
    poly.unitTail (elim.matVec (@ite _ c inst M []) x)
  | _, isTrue hc, _, h => h hc
  | _, isFalse _, _, _ => trivial

/-- The guarded block's unit tail gives the block's where the guard
passes. -/
private theorem matVec_guard_to (x : List BPair) : ∀ (c : Prop)
    (inst : Decidable c) (M : elim.Mat),
    poly.unitTail (elim.matVec (@ite _ c inst M []) x) → c →
    poly.unitTail (elim.matVec M x)
  | _, isTrue _, _, h, _ => h
  | _, isFalse hn, _, _, hc => absurd hc hn

/-- The stacked datum over a stated index family reads the source
content's monomial width, block by block. -/
private theorem rowsLen_stackGo (mu : List Nat) : ∀ l : List Nat,
    elim.rowsLen (monomialsAt mu).length
      (l.flatMap (fun i =>
        if 0 < ground.getAt 0 mu (i + 1) then
          matUnitAt (moveUp i mu) mu i (i + 1)
        else []))
  | [] => trivial
  | a :: t =>
    elim.rowsLen_append (monomialsAt mu).length
      (rowsLen_guard (monomialsAt mu).length _ _ _
        (rowsLen_matUnitAt (moveUp a mu) mu a (a + 1)))
      (rowsLen_stackGo mu t)

/-- The stacked rows at the content's monomial width, each block's
rows the unit action's (`matUnitAt`'s own width read). -/
theorem rowsLen_stackedRaise : ∀ (mu : List Nat),
    elim.rowsLen (places.monomialsAt mu).length (stackedRaise mu) :=
  fun mu => rowsLen_stackGo mu (List.range (mu.length - 1))

/-- The stacked action over a stated index family assembles from
the occupied blocks' reads. -/
private theorem stackGo_of (mu : List Nat) (x : List BPair) :
    ∀ l : List Nat,
    (∀ k, k < l.length →
      0 < ground.getAt 0 mu (ground.getAt 0 l k + 1) →
      poly.unitTail (elim.matVec
        (matUnitAt (moveUp (ground.getAt 0 l k) mu) mu
          (ground.getAt 0 l k) (ground.getAt 0 l k + 1)) x)) →
    poly.unitTail (elim.matVec
      (l.flatMap (fun i =>
        if 0 < ground.getAt 0 mu (i + 1) then
          matUnitAt (moveUp i mu) mu i (i + 1)
        else [])) x)
  | [], _ => trivial
  | a :: t, h => by
    show poly.unitTail (elim.matVec
      ((if 0 < ground.getAt 0 mu (a + 1) then
          matUnitAt (moveUp a mu) mu a (a + 1)
        else [])
        ++ t.flatMap (fun i =>
          if 0 < ground.getAt 0 mu (i + 1) then
            matUnitAt (moveUp i mu) mu i (i + 1)
          else [])) x)
    rw [elim.matVec_append]
    refine elim.unitTail_append
      (matVec_guard_of x _ _ _ (h 0 (Nat.succ_pos t.length))) ?_
    exact stackGo_of mu x t
      (fun k hk => h (k + 1) (Nat.succ_lt_succ hk))

/-- The stacked action over a stated index family gives each
occupied block's read back. -/
private theorem stackGo_to (mu : List Nat) (x : List BPair) :
    ∀ l : List Nat,
    poly.unitTail (elim.matVec
      (l.flatMap (fun i =>
        if 0 < ground.getAt 0 mu (i + 1) then
          matUnitAt (moveUp i mu) mu i (i + 1)
        else [])) x) →
    ∀ k, k < l.length →
      0 < ground.getAt 0 mu (ground.getAt 0 l k + 1) →
      poly.unitTail (elim.matVec
        (matUnitAt (moveUp (ground.getAt 0 l k) mu) mu
          (ground.getAt 0 l k) (ground.getAt 0 l k + 1)) x)
  | [], _, k, hk, _ => absurd hk (Nat.not_lt_zero k)
  | a :: t, h, k, hk, hocc => by
    have h' : poly.unitTail (elim.matVec
        ((if 0 < ground.getAt 0 mu (a + 1) then
            matUnitAt (moveUp a mu) mu a (a + 1)
          else [])
          ++ t.flatMap (fun i =>
            if 0 < ground.getAt 0 mu (i + 1) then
              matUnitAt (moveUp i mu) mu i (i + 1)
            else [])) x) := h
    rw [elim.matVec_append] at h'
    obtain ⟨hhd, htl⟩ := elim.unitTail_append_split _ _ h'
    match k, hk, hocc with
    | 0, _, hocc0 => exact matVec_guard_to x _ _ _ hhd hocc0
    | k + 1, hk', hocck =>
      exact stackGo_to mu x t htl k (Nat.lt_of_succ_lt_succ hk') hocck

/-- The stacked read assembles from the occupied moves' reads. -/
theorem stackedRaise_of : ∀ (mu : List Nat) (x : List BPair),
    (∀ i, i + 1 < mu.length → 0 < ground.getAt 0 mu (i + 1) →
      poly.unitTail (elim.matVec
        (matUnitAt (moveUp i mu) mu i (i + 1)) x)) →
    poly.unitTail (elim.matVec (stackedRaise mu) x) := by
  intro mu x h
  refine stackGo_of mu x (List.range (mu.length - 1)) ?_
  intro k hk
  rw [ground.length_range] at hk
  rw [ground.getAt_range (mu.length - 1) k hk]
  exact h k (ground.succ_lt_of_lt_pred hk)

/-- The stacked read gives each occupied move's read back. -/
theorem stackedRaise_to : ∀ (mu : List Nat) (x : List BPair),
    poly.unitTail (elim.matVec (stackedRaise mu) x) →
    ∀ i, i + 1 < mu.length → 0 < ground.getAt 0 mu (i + 1) →
      poly.unitTail (elim.matVec
        (matUnitAt (moveUp i mu) mu i (i + 1)) x) := by
  intro mu x h i hi hocc
  have hlt : i < mu.length - 1 := Nat.le_pred_of_lt hi
  have hk : i < (List.range (mu.length - 1)).length := by
    rw [ground.length_range]
    exact hlt
  have hgo := stackGo_to mu x (List.range (mu.length - 1)) h i hk
  rw [ground.getAt_range (mu.length - 1) i hlt] at hgo
  exact hgo hocc

end units
