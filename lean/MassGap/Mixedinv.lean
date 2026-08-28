import MassGap.Blockcount
import MassGap.Fusiondata
import MassGap.Pieri
import MassGap.Pathsquare
/-!
`lem:mixedinv` — the block count is the path count: `M ⊗ V`
exhausts over the blocks and `W_μ ⊗ V` fuses by one boxes
(`lem:pieri`), so at every power
`N_λ(V^{⊗ k+1}) = Σ_{μ→λ} N_μ(V^{⊗ k})` over the shapes with one
box removed, the unit power the scalars' line: `N_λ(V^{⊗ k})` is
the path count (`pathsquare.pathCount`, `lem:pathsquare`'s
recursion), and the identity with `def:blockcount`'s
kernel-dimension count is the stated decidable read `read`, its
instances the check module's pins.  The general theorem `readAll`
closes that read at every shape: the power's monomial pool exhausts
over its tops, each top's block fuses by one boxes at `lem:pieri`'s
row, the removals read that row backwards at the matched widths
(`pathsquare.row_removals`), and the collapsed fold is the path
fold one degree below (`pathsquare.pathCount_step`), the vacant
degree the scalars' own line.  The lemma's invariant-span clause
closes here whole: the carrier tier `permMat`/`flatF` with the
independence `perm_indep` and the Gram `perm_gram` at the cycle
count `d^{#cycles}`, and the span theorem `perm_span` — an
invariant enters as its matrix family at the stated frames and
moved reads, a family with null values at the exhaustion's tops is
null (the provenance walk at the moved reads, the blocks' span,
and the identity rows the coordinates), each top's value is a top
(the moved read at the top's null raising image), the stacked top
values map the flats' independent list into the raising kernels'
joined span, and the kernels' count is the factorial (the
occupancy regrouped over the distinct contents, the collapsed fold
over the shapes, and `lem:pathsquare`'s square sum), so a family
off the permutations' span would extend the independent list one
past the count — its consumer the pairing's permutation
presentation (`prop:wg`).
-/

namespace mixedinv
open ground places

/-- The block count is the path count: the stated read at
`def:blockcount`'s kernel-dimension count. -/
def read (s : Shape) : Prop := blockcount.countPower s = pathsquare.pathCount s

instance (s : Shape) : Decidable (read s) :=
  inferInstanceAs (Decidable (_ = _))

/-! The power's monomial pool (`con:places`' composition of the
powers): the fused carrier at the fundamental block with its
stated data, and the identity family's rows the coordinates every
place of a content carries. -/

/-- The power's monomial pool: the scalars' line at the vacant
content, each further power the fused pool at the fundamental
block (`con:places`' composition of the powers, the spanning
lists' tensors). -/
private def monPool (d : Nat) : Nat → List blockcount.HVec
  | 0 => [⟨List.replicate d 0, [ground.BPair.ofNat 1]⟩]
  | k + 1 =>
    blockcount.fusedAt (monPool d k)
      (blockcount.blockSpan (pieri.oneBox d))

/-- The vacant power's one member, the scalars' line. -/
private theorem monPool_zero_mem (d : Nat) :
    ∀ x ∈ monPool d 0,
      x = (⟨List.replicate d 0, [ground.BPair.ofNat 1]⟩
        : blockcount.HVec) := by
  intro x hx
  have hx' : x ∈ [(⟨List.replicate d 0, [ground.BPair.ofNat 1]⟩
      : blockcount.HVec)] := hx
  cases hx' with
  | head => rfl
  | tail _ h => nomatch h

/-- The pool's stated data at a positive letter count: every
member sized at its content's enumeration, of the stated width and
of the power's own degree, with every distinct letter pair's
action settled in the pool. -/
private theorem monPool_pack (d : Nat) (hd : 0 < d) (k : Nat) :
    (∀ x ∈ monPool d k, blockcount.sized x)
      ∧ (∀ x ∈ monPool d k, x.content.length = d)
      ∧ (∀ x ∈ monPool d k, ground.sumNat x.content = k)
      ∧ (∀ x ∈ monPool d k, ∀ i, i < d → ∀ j, j < d → ¬ i = j →
          blockcount.settledAt (monPool d k) (blockcount.act i j x)) := by
  have hdeg1 : degree (pieri.oneBox d) = 1 := by
    match d, hd with
    | n + 1, _ => exact degree_unitAt n
  have hszB : ∀ w ∈ blockcount.blockSpan (pieri.oneBox d),
      blockcount.sized w := (lowerspan.spanReads (pieri.oneBox d)).1
  have hwidB : ∀ w ∈ blockcount.blockSpan (pieri.oneBox d),
      w.content.length = d := fun w hw =>
    (blockcount.blockSpan_width (pieri.oneBox d) w hw).trans
      (pieri.length_oneBox d)
  have hdegB : ∀ w ∈ blockcount.blockSpan (pieri.oneBox d),
      sumNat w.content = 1 := fun w hw =>
    (blockcount.blockSpan_degree (pieri.oneBox d) w hw).trans hdeg1
  have hclB : ∀ w ∈ blockcount.blockSpan (pieri.oneBox d),
      ∀ i, i < d → ∀ j, j < d → ¬ i = j →
        blockcount.settledAt (blockcount.blockSpan (pieri.oneBox d))
          (blockcount.act i j w) := by
    intro w hw i hi j hj hij
    exact lowerspan.act_closed_def (pieri.oneBox d) i j
      (by rw [pieri.length_oneBox d]; exact hi)
      (by rw [pieri.length_oneBox d]; exact hj) hij w hw
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [monPool_zero_mem d x hx]
      show (1 : Nat) = (monomialsAt (List.replicate d 0)).length
      rw [monomialsAt_sum_zero (List.replicate d 0)
        (sumNat_replicate_zero d)]
      rfl
    · intro x hx
      rw [monPool_zero_mem d x hx]
      exact ground.length_replicate 0 d
    · intro x hx
      rw [monPool_zero_mem d x hx]
      exact sumNat_replicate_zero d
    · intro x hx i hi j hj hij
      rw [monPool_zero_mem d x hx]
      refine Or.inl (blockcount.allU_of_unitTail _ ?_)
      show poly.unitTail (elim.matVec
        (units.matUnitAt (blockcount.moveAt i j (List.replicate d 0))
          (List.replicate d 0) i j) [ground.BPair.ofNat 1])
      exact units.matVec_null_unocc _ (List.replicate d 0) i j
        (ground.getAt_replicate_self 0 d j) [ground.BPair.ofNat 1]
  | succ k ih =>
    have hstep : monPool d (k + 1)
        = blockcount.fusedAt (monPool d k)
            (blockcount.blockSpan (pieri.oneBox d)) := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstep]
      exact blockcount.fusedAt_sized _ _
    · rw [hstep]
      exact blockcount.fusedAt_width d (monPool d k) _ ih.2.1 hwidB
    · rw [hstep]
      exact blockcount.fusedAt_degree d k 1 (monPool d k) _ ih.2.1
        hwidB ih.2.2.1 hdegB
    · rw [hstep]
      exact blockcount.fused_closed d (monPool d k) _ ih.1 hszB
        ih.2.1 hwidB ih.2.2.2 hclB

/-! The occurrence tier: the identity family's row at a place of a
content is a pool member, the coordinate basis read one place at a
time.  The letter last written splits the place's monomial, the
withdrawn content carries the induction, and the fused tensor
against the fundamental block's own member reads the place back. -/

/-- The content of a word extended by one letter: that letter's
unit family joins the prefix's content. -/
private theorem content_snoc (d : Nat) (m' : List Nat) (i : Nat) :
    content d (m' ++ [i])
      = List.zipWith (fun a b => a + b) (content d m')
        (unitAt d i) := by
  rw [content_append d m' [i], content_unitAt d i]

/-- A letter's unit family joined to a family of the stated width
raises that family at the letter. -/
private theorem zipWith_unitAt (d i : Nat) (hi : i < d)
    (c : List Nat) (hc : c.length = d) :
    List.zipWith (fun a b => a + b) c (unitAt d i)
      = ground.bumpAt i c := by
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_zipWith (fun a b => a + b) c (unitAt d i) d hc
      (length_unitAt d i), ground.length_bumpAt i c, hc]
  · intro q hq
    rw [ground.length_zipWith (fun a b => a + b) c (unitAt d i) d hc
      (length_unitAt d i)] at hq
    rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) c (unitAt d i) q
        (by rw [hc]; exact hq) (by rw [length_unitAt d i]; exact hq),
      getAt_unitAt d i q, if_pos hq]
    by_cases hqi : q = i
    · rw [hqi, if_pos rfl,
        ground.getAt_bumpAt_self i c (by rw [hc]; exact hi)]
    · rw [if_neg hqi, ground.getAt_bumpAt_ne i c q hqi, Nat.add_zero]

/-- The sum's unit is its own representative. -/
private theorem norm_unit :
    ground.BPair.unit.norm = ground.BPair.unit := by decide +kernel

/-- The unit family's representatives are its own. -/
private theorem map_norm_units (n : Nat) :
    (List.replicate n ground.BPair.unit).map ground.BPair.norm
      = List.replicate n ground.BPair.unit := by
  rw [ground.map_replicate ground.BPair.norm ground.BPair.unit n,
    norm_unit]

/-- A scatter onto the unit family sets one key: at a datum whose
join with the unit represents the product's one the representatives
are the identity family's own row. -/
private theorem scatter_replicate (c : ground.BPair)
    (hc : (ground.BPair.unit + c).norm = ground.BPair.ofPos .one) :
    ∀ (n r : Nat), r < n →
      (units.scatterAt r c (List.replicate n ground.BPair.unit)).map
          ground.BPair.norm
        = List.set (List.replicate n ground.BPair.unit) r
            (ground.BPair.ofPos .one)
  | 0, r, hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, 0, _ => by
    show (ground.BPair.unit + c).norm
        :: (List.replicate n ground.BPair.unit).map ground.BPair.norm
      = ground.BPair.ofPos .one :: List.replicate n ground.BPair.unit
    rw [hc, map_norm_units n]
  | n + 1, r + 1, hr => by
    show ground.BPair.unit.norm
        :: (units.scatterAt r c
            (List.replicate n ground.BPair.unit)).map ground.BPair.norm
      = ground.BPair.unit
        :: List.set (List.replicate n ground.BPair.unit) r
            (ground.BPair.ofPos .one)
    rw [norm_unit,
      scatter_replicate c hc n r (Nat.lt_of_succ_lt_succ hr)]

/-- A pass whose step fixes its accumulator at the unit coordinate
reads its seed over a unit family. -/
private theorem foldl_zip_allU {β : Type}
    (F : β → List Nat × ground.BPair → β)
    (hskip : ∀ (a : β) (mm : List Nat),
      F a (mm, ground.BPair.unit) = a) :
    ∀ (B : List (List Nat)) (a : β),
      (List.zipWith (fun m x => (m, x)) B
        (List.replicate B.length ground.BPair.unit)).foldl F a = a
  | [], _ => rfl
  | b :: t, a => by
    show (List.zipWith (fun m x => (m, x)) t
        (List.replicate t.length ground.BPair.unit)).foldl F
        (F a (b, ground.BPair.unit)) = a
    rw [hskip a b]
    exact foldl_zip_allU F hskip t a

/-- The same pass against the identity family's row reads the one
live key's step alone. -/
private theorem foldl_zip_unit {β : Type}
    (F : β → List Nat × ground.BPair → β) :
    ∀ (B : List (List Nat)) (r : Nat), r < B.length → ∀ a : β,
      (∀ (a' : β) (mm : List Nat), F a' (mm, ground.BPair.unit) = a') →
      (List.zipWith (fun m x => (m, x)) B
          (List.set (List.replicate B.length ground.BPair.unit) r
            (ground.BPair.ofPos .one))).foldl F a
        = F a (ground.getAt [] B r, ground.BPair.ofPos .one)
  | [], r, hr, _, _ => absurd hr (Nat.not_lt_zero r)
  | b :: t, 0, _, a, hskip => by
    show (List.zipWith (fun m x => (m, x)) t
        (List.replicate t.length ground.BPair.unit)).foldl F
        (F a (b, ground.BPair.ofPos .one))
      = F a (b, ground.BPair.ofPos .one)
    exact foldl_zip_allU F hskip t _
  | b :: t, r + 1, hr, a, hskip => by
    show (List.zipWith (fun m x => (m, x)) t
        (List.set (List.replicate t.length ground.BPair.unit) r
          (ground.BPair.ofPos .one))).foldl F
        (F a (b, ground.BPair.unit))
      = F a (ground.getAt [] t r, ground.BPair.ofPos .one)
    rw [hskip a b]
    exact foldl_zip_unit F t r (Nat.lt_of_succ_lt_succ hr) a hskip

/-- The tensor's outer pass at an identity row against the
fundamental block's member: one scatter, at the place of the row's
own monomial extended by the block's letter. -/
private theorem tensor_row_fold (d i : Nat) (hi : i < d)
    (nu' : List Nat) (r : Nat) (hr : r < (monomialsAt nu').length)
    (mu : List Nat) (seed : List ground.BPair) :
    (List.zipWith (fun m x => (m, x)) (monomialsAt nu')
        (List.set
          (List.replicate (monomialsAt nu').length ground.BPair.unit)
          r (ground.BPair.ofPos .one))).foldl
      (fun acc p =>
        if p.2.isUnitRep then acc
        else
          (List.zipWith (fun m x => (m, x)) (monomialsAt (unitAt d i))
              [ground.BPair.ofNat 1]).foldl
            (fun acc2 q =>
              if q.2.isUnitRep then acc2
              else units.scatterAt (rankOf (p.1 ++ q.1) mu)
                (p.2 * q.2) acc2)
            acc)
      seed
      = units.scatterAt
          (rankOf (ground.getAt [] (monomialsAt nu') r ++ [i]) mu)
          (ground.BPair.ofPos .one * ground.BPair.ofNat 1) seed := by
  rw [monomialsAt_unitAt d i hi]
  exact foldl_zip_unit _ (monomialsAt nu') r hr seed (fun _ _ => rfl)

/-- The fused tensor of a content's identity row with the
fundamental block's member at a letter: the raised content with the
identity row at the extended monomial's own place. -/
private theorem tensor_unit_row (d i : Nat) (hi : i < d)
    (nu nu' : List Nat)
    (hzip : List.zipWith (fun a b => a + b) nu' (unitAt d i) = nu)
    (r : Nat) (hr : r < (monomialsAt nu').length)
    (j : Nat) (hj : j < (monomialsAt nu).length)
    (hjr : rankOf (ground.getAt [] (monomialsAt nu') r ++ [i]) nu
      = j) :
    blockcount.tensorH
        (⟨nu', ground.getAt []
          (elim.idList (monomialsAt nu').length) r⟩
          : blockcount.HVec)
        (⟨unitAt d i, [ground.BPair.ofNat 1]⟩ : blockcount.HVec)
      = (⟨nu, ground.getAt []
          (elim.idList (monomialsAt nu).length) j⟩
          : blockcount.HVec) := by
  rw [elim.idList_getAt (monomialsAt nu').length r hr,
    elim.idList_getAt (monomialsAt nu).length j hj]
  show (⟨List.zipWith (fun a b => a + b) nu' (unitAt d i),
      ((List.zipWith (fun m x => (m, x)) (monomialsAt nu')
          (List.set
            (List.replicate (monomialsAt nu').length ground.BPair.unit)
            r (ground.BPair.ofPos .one))).foldl
        (fun acc p =>
          if p.2.isUnitRep then acc
          else
            (List.zipWith (fun m x => (m, x))
                (monomialsAt (unitAt d i))
                [ground.BPair.ofNat 1]).foldl
              (fun acc2 q =>
                if q.2.isUnitRep then acc2
                else units.scatterAt
                  (rankOf (p.1 ++ q.1)
                    (List.zipWith (fun a b => a + b) nu' (unitAt d i)))
                  (p.2 * q.2) acc2)
              acc)
        ((monomialsAt (List.zipWith (fun a b => a + b) nu'
            (unitAt d i))).map
          (fun _ => ground.BPair.unit))).map ground.BPair.norm⟩
      : blockcount.HVec)
    = ⟨nu, List.set
        (List.replicate (monomialsAt nu).length ground.BPair.unit) j
        (ground.BPair.ofPos .one)⟩
  rw [hzip, tensor_row_fold d i hi nu' r hr nu _, hjr,
    ground.map_const ground.BPair.unit (monomialsAt nu),
    scatter_replicate (ground.BPair.ofPos .one * ground.BPair.ofNat 1)
      (by decide +kernel) (monomialsAt nu).length j hj]

/-- The occurrence read: at every content of the stated width and
degree, the identity family's row at every place of that content's
enumeration is a member of the power's pool. -/
private theorem monPool_occ (d : Nat) (hd : 0 < d) :
    ∀ (k : Nat) (nu : List Nat), nu.length = d →
      ground.sumNat nu = k →
      ∀ j, j < (places.monomialsAt nu).length →
        (⟨nu, ground.getAt []
            (elim.idList (places.monomialsAt nu).length) j⟩
          : blockcount.HVec) ∈ monPool d k := by
  intro k
  induction k with
  | zero =>
    intro nu hlen hsum j hj
    have hnu : nu = List.replicate d 0 := by
      rw [← hlen]
      exact replicate_of_sum_zero nu hsum
    subst hnu
    have hmz : monomialsAt (List.replicate d 0) = [[]] :=
      monomialsAt_sum_zero _ (sumNat_replicate_zero d)
    rw [hmz] at hj
    rw [hmz]
    match j, hj with
    | 0, _ => exact List.Mem.head _
    | q + 1, hq =>
      exact absurd (Nat.lt_of_succ_lt_succ hq) (Nat.not_lt_zero q)
  | succ k ih =>
    intro nu hlen hsum j hj
    have hmc := member_conditions
      (ground.countOf_getAt_pos [] (monomialsAt nu) j hj)
    have hmlen : (ground.getAt [] (monomialsAt nu) j).length = k + 1 := by
      rw [hmc.1, hsum]
    have hmcont : content d (ground.getAt [] (monomialsAt nu) j) = nu := by
      rw [← hlen]
      exact hmc.2
    obtain ⟨m', i, hsnoc, hm'len⟩ := ground.snoc_split k _ hmlen
    have hcpos : 0 < ground.countOf i
        (ground.getAt [] (monomialsAt nu) j) := by
      rw [hsnoc, ground.countOf_append i m' [i]]
      rw [ground.countOf_cons i i ([] : List Nat), if_pos rfl]
      show 0 < ground.countOf i m' + (1 + 0)
      rw [Nat.add_zero]
      exact Nat.succ_pos _
    have hid : i < d :=
      mem_lt_of_content d (ground.getAt [] (monomialsAt nu) j)
        (by rw [hmcont, hsum]; exact hmlen.symm) i hcpos
    have hcz : content d (ground.getAt [] (monomialsAt nu) j)
        = List.zipWith (fun a b => a + b) (content d m')
          (unitAt d i) := by
      rw [hsnoc, content_snoc d m' i]
    have hbump : nu = ground.bumpAt i (content d m') := by
      rw [← hmcont, hcz,
        zipWith_unitAt d i hid (content d m') (content_length d m')]
    have hnu' : ground.dipAt i nu = content d m' := by
      rw [hbump, ground.dipAt_bumpAt_self i (content d m')]
    have hocc : 0 < ground.getAt 0 nu i := by
      rw [← hmcont, getAt_contentAt d _ i hid]
      exact hcpos
    have hlen' : (ground.dipAt i nu).length = d := by
      rw [ground.length_dipAt i nu, hlen]
    have hsum' : sumNat (ground.dipAt i nu) = k := by
      have h := sumNat_dipAt i nu hocc
      rw [hsum] at h
      exact Nat.succ.inj h
    have hrk := rankOf_read m' (ground.dipAt i nu)
      (by rw [hsum']; exact hm'len)
      (by rw [hlen', hnu'])
    have hIH := ih (ground.dipAt i nu) hlen' hsum'
      (rankOf m' (ground.dipAt i nu)) hrk.1
    have hfund : blockcount.blockSpan (pieri.oneBox d)
        = (List.range d).map (fun q =>
            (⟨unitAt d q, [ground.BPair.ofNat 1]⟩
              : blockcount.HVec)) :=
      blockcount.blockSpan_fund d hd
    have hmemB : (⟨unitAt d i, [ground.BPair.ofNat 1]⟩
        : blockcount.HVec)
        ∈ blockcount.blockSpan (pieri.oneBox d) := by
      rw [hfund]
      have hget : ground.getAt (⟨[], []⟩ : blockcount.HVec)
          ((List.range d).map (fun q =>
            (⟨unitAt d q, [ground.BPair.ofNat 1]⟩
              : blockcount.HVec))) i
          = ⟨unitAt d i, [ground.BPair.ofNat 1]⟩ := by
        rw [getAt_map_range (⟨[], []⟩ : blockcount.HVec) _ d i,
          if_pos hid]
      rw [← hget]
      refine ground.mem_of_countOf_pos _ _
        (ground.countOf_getAt_pos _ _ i ?_)
      rw [ground.length_mapRange]
      exact hid
    have htens := tensor_unit_row d i hid nu (ground.dipAt i nu)
      (by
        rw [hnu',
          zipWith_unitAt d i hid (content d m') (content_length d m')]
        exact hbump.symm)
      (rankOf m' (ground.dipAt i nu)) hrk.1 j hj
      (by rw [hrk.2, ← hsnoc]; exact rankOf_getAt nu j hj)
    rw [show monPool d (k + 1)
        = blockcount.fusedAt (monPool d k)
            (blockcount.blockSpan (pieri.oneBox d)) from rfl,
      ← htens]
    exact ground.mem_flatMap_to _ hIH
      (ground.mem_map_to (blockcount.tensorH _) hmemB)

/-! The power bridge: the pool's count at a content and the
content summand's own coordinate basis are two stated bases of one
span, so `def:blockcount`'s kernel dimension reads one count. -/

/-- The coordinate pool at a content: one member per monomial, the
identity family's rows. -/
private def idPool (nu : List Nat) : List blockcount.HVec :=
  (List.range (places.monomialsAt nu).length).map
    (fun j => ⟨nu, ground.getAt []
      (elim.idList (places.monomialsAt nu).length) j⟩)

/-- The coordinate pool's group at its own content is the identity
family: every member is kept and the rows are the family's own. -/
private theorem groupAt_idPool (nu : List Nat) :
    blockcount.groupAt (idPool nu) nu
      = elim.idList (monomialsAt nu).length := by
  have hfil : (idPool nu).filter (fun w => w.content == nu)
      = idPool nu := by
    refine ground.filter_all _ (idPool nu) ?_
    intro x hx
    match ground.mem_map_of _ (List.range (monomialsAt nu).length) x
        hx with
    | ⟨q, _, hq⟩ =>
      rw [← hq]
      exact ground.listEqBeq nu
  show ((idPool nu).filter (fun w => w.content == nu)).map
      blockcount.HVec.coords = _
  rw [hfil]
  show ((List.range (monomialsAt nu).length).map
      (fun j => (⟨nu, ground.getAt []
        (elim.idList (monomialsAt nu).length) j⟩
        : blockcount.HVec))).map blockcount.HVec.coords = _
  rw [ground.map_map _ blockcount.HVec.coords
    (List.range (monomialsAt nu).length)]
  exact range_map_getAt ([] : List ground.BPair)
    (monomialsAt nu).length (elim.idList (monomialsAt nu).length)
    (elim.length_idList _)

/-- The coordinate pool's members are sized: the identity family's
rows read the content enumeration's width. -/
private theorem idPool_sized (nu : List Nat) :
    ∀ x ∈ idPool nu, blockcount.sized x := by
  intro x hx
  match ground.mem_map_of _ (List.range (monomialsAt nu).length) x
      hx with
  | ⟨q, hqm, hq⟩ =>
    rw [← hq]
    show (ground.getAt []
        (elim.idList (monomialsAt nu).length) q).length
      = (monomialsAt nu).length
    exact elim.rowsLen_getAt _ q (elim.rowsLen_idList _)
      (by
        rw [elim.length_idList]
        exact ltOfMemRange hqm)

/-- The power bridge: the pool's count at a content is
`def:blockcount`'s kernel dimension on the content summand's own
coordinates — two stated bases of one span read one kernel
dimension. -/
private theorem monPool_bridge (d : Nat) (hd : 0 < d) (k : Nat)
    (lam : places.Shape) (hlen : lam.length = d)
    (hdeg : places.degree lam = k) :
    blockcount.countAt (monPool d k) (places.rowList lam)
      = blockcount.countPower lam := by
  have hnud : (rowList lam).length = d := by
    rw [length_rowList lam, hlen]
  have hnuk : sumNat (rowList lam) = k := hdeg
  have hpack := monPool_pack d hd k
  have hstep1 : blockcount.countAt (monPool d k) (rowList lam)
      = blockcount.countAt (idPool (rowList lam)) (rowList lam) := by
    refine blockcount.countAt_congr (rowList lam) (monPool d k)
      (idPool (rowList lam)) hpack.1 (idPool_sized (rowList lam))
      ?_ ?_
    · intro q hq
      rw [groupAt_idPool (rowList lam)]
      exact elim.span_of_full _ _ _ (elim.length_idList _)
        (elim.indepRows_idList _)
        (elim.rowsLen_getAt _ q
          (blockcount.rowsLen_groupAt (rowList lam) (monPool d k)
            hpack.1) hq)
    · intro q hq
      rw [groupAt_idPool (rowList lam)] at hq
      rw [elim.length_idList] at hq
      rw [groupAt_idPool (rowList lam)]
      exact blockcount.span_of_mem
        ((monPool d k).filter (fun w => w.content == rowList lam))
        (rowList lam)
        (⟨rowList lam, ground.getAt []
          (elim.idList (monomialsAt (rowList lam)).length) q⟩
          : blockcount.HVec)
        (ground.mem_filter_to _
          (monPool_occ d hd k (rowList lam) hnud hnuk q hq)
          (ground.listEqBeq (rowList lam)))
        (blockcount.rowsLen_groupAt (rowList lam) (monPool d k)
          hpack.1)
  rw [hstep1]
  show elim.kernelDim
      (elim.collectOf (monomialsAt (rowList lam)).length
        (blockcount.groupAt (idPool (rowList lam))
          (rowList lam))).length
      (elim.crossM (units.stackedRaise (rowList lam))
        (elim.collectOf (monomialsAt (rowList lam)).length
          (blockcount.groupAt (idPool (rowList lam))
            (rowList lam))))
    = _
  rw [groupAt_idPool (rowList lam),
    elim.collect_keep _ _ (elim.indepRows_idList _),
    elim.length_idList,
    elim.kernelDim_idList (monomialsAt (rowList lam)).length
      (units.stackedRaise (rowList lam))
      (units.rowsLen_stackedRaise (rowList lam))]
  rfl

/-! The recursion's tier: the vacant degree's unit count, the
adjacent moves' roundtrips at an occupied pair, the removals as
`lem:pieri`'s row read backwards, and the descent itself — the
pool's exhaustion over its tops against the fundamental block's
one-box rows, the fold collapsing onto the removals. -/

/-- The vacant content's stacked raisings are row-free: every key
sits at the floor, so every adjacent move's guard refuses. -/
private theorem stackedRaise_vac (mu : List Nat) (h : sumNat mu = 0) :
    units.stackedRaise mu = [] := by
  have hr : mu = List.replicate mu.length 0 :=
    replicate_of_sum_zero mu h
  have hz : ∀ p, ground.getAt 0 mu p = 0 := by
    intro p
    rw [hr]
    exact ground.getAt_replicate_zero mu.length p
  show (List.range (mu.length - 1)).flatMap (fun i =>
      if 0 < ground.getAt 0 mu (i + 1) then
        units.matUnitAt (units.moveUp i mu) mu i (i + 1)
      else []) = []
  refine ground.flatMap_nil _ (List.range (mu.length - 1)) ?_
  intro x _
  refine if_neg ?_
  rw [hz (x + 1)]
  exact Nat.lt_irrefl 0

/-- The vacant degree's block count is the scalars' line: the
content's enumeration is the empty word alone and the stacked
raisings are row-free, so the kernel is the whole column. -/
private theorem countPower_vac (s : Shape)
    (h : places.degree s = 0) : blockcount.countPower s = 1 := by
  have hmz : monomialsAt (rowList s) = [[]] :=
    monomialsAt_sum_zero (rowList s) h
  show elim.kernelDim (monomialsAt (rowList s)).length
      (units.stackedRaise (rowList s)) = 1
  rw [hmz, stackedRaise_vac (rowList s) h]
  show (1 : Nat) - elim.rank ([] : elim.Mat) = 1
  rw [elim.rank_null ([] : elim.Mat)
    (fun k hk => absurd hk (Nat.not_lt_zero k))]

/-- The collapse: a distinct content index whose weight vanishes
off the index reads a family of shapes summand by summand, each
shape picking its own row list's weight. -/
private theorem fold_collapse (W : List Nat → Nat)
    (D : List (List Nat))
    (hle : ∀ mu, ground.countOf mu D ≤ 1)
    (hoff : ∀ mu, ground.countOf mu D = 0 → W mu = 0)
    (hrl : ∀ mu, 0 < ground.countOf mu D →
      rowList (places.shapeOf mu) = mu) :
    ∀ R : List Shape,
      ground.famFold Nat.add 0
          (fun mu => W mu * ground.countOf (places.shapeOf mu) R) D
        = ground.famFold Nat.add 0 (fun x => W (rowList x)) R
  | [] => by
    show ground.famFold Nat.add 0
      (fun mu => W mu * ground.countOf (places.shapeOf mu)
        ([] : List Shape)) D = 0
    refine ground.famFold_zero _ ?_ D
    intro mu
    show W mu * 0 = 0
    rw [Nat.mul_zero]
  | x :: R => by
    have hstep : ∀ mu, 0 < ground.countOf mu D →
        W mu * ground.countOf (places.shapeOf mu) (x :: R)
          = (if mu = rowList x then W mu else 0)
            + W mu * ground.countOf (places.shapeOf mu) R := by
      intro mu hmu
      have hrlm := hrl mu hmu
      rw [ground.countOf_cons, Nat.left_distrib]
      by_cases hsx : places.shapeOf mu = x
      · have hmx : mu = rowList x := by
          rw [← hsx]
          exact hrlm.symm
        rw [if_pos hsx, if_pos hmx, Nat.mul_one]
      · have hmx : ¬ mu = rowList x := by
          intro hm
          refine hsx ?_
          rw [hm]
          exact places.shapeOf_rowList x
        rw [if_neg hsx, if_neg hmx, Nat.mul_zero]
    have h1 : ground.famFold Nat.add 0
        (fun mu => W mu * ground.countOf (places.shapeOf mu) (x :: R)) D
      = ground.famFold Nat.add 0
        (fun mu => (if mu = rowList x then W mu else 0)
          + W mu * ground.countOf (places.shapeOf mu) R) D :=
      ground.famFold_congr_members Nat.add 0 _ _ D hstep
    have h2 : ground.famFold Nat.add 0
        (fun mu => (if mu = rowList x then W mu else 0)
          + W mu * ground.countOf (places.shapeOf mu) R) D
      = ground.famFold Nat.add 0
          (fun mu => if mu = rowList x then W mu else 0) D
        + ground.famFold Nat.add 0
          (fun mu => W mu * ground.countOf (places.shapeOf mu) R) D :=
      ground.famFold_add_split _ _ D
    have h3 : ground.famFold Nat.add 0
        (fun mu => if mu = rowList x then W mu else 0) D
      = W (rowList x) := by
      match Nat.eq_zero_or_pos (ground.countOf (rowList x) D) with
      | .inl hz =>
        rw [ground.famFold_pickZero W (rowList x) D hz, hoff _ hz]
      | .inr hp =>
        exact ground.famFold_pick W (rowList x) D
          (Nat.le_antisymm (hle (rowList x)) hp)
    show ground.famFold Nat.add 0
        (fun mu => W mu * ground.countOf (places.shapeOf mu) (x :: R)) D
      = W (rowList x)
        + ground.famFold Nat.add 0 (fun y => W (rowList y)) R
    rw [h1, h2, h3, fold_collapse W D hle hoff hrl R]

/-- The recursion at a positive width: the block count in the
power is the path recursion's own value at the degree's fuel — the
pool exhausts over its tops, each top's block fuses by one boxes
at `lem:pieri`'s row, the mirror reads the row as the target's
removals, and the collapsed fold is the path fold below. -/
private theorem readGo (d : Nat) (hd : 0 < d) :
    ∀ (k : Nat) (s : Shape), s.length = d →
      places.degree s = k → blockcount.countPower s = pathsquare.pathCount s := by
  have hszB : ∀ w ∈ blockcount.blockSpan (pieri.oneBox d),
      blockcount.sized w := (lowerspan.spanReads (pieri.oneBox d)).1
  have hwidB : ∀ w ∈ blockcount.blockSpan (pieri.oneBox d),
      w.content.length = d := fun w hw =>
    (blockcount.blockSpan_width (pieri.oneBox d) w hw).trans
      (pieri.length_oneBox d)
  have hclB : ∀ w ∈ blockcount.blockSpan (pieri.oneBox d),
      ∀ i, i < d → ∀ j, j < d → ¬ i = j →
        blockcount.settledAt (blockcount.blockSpan (pieri.oneBox d))
          (blockcount.act i j w) := by
    intro w hw i hi j hj hij
    exact lowerspan.act_closed_def (pieri.oneBox d) i j
      (by rw [pieri.length_oneBox d]; exact hi)
      (by rw [pieri.length_oneBox d]; exact hj) hij w hw
  have hiC : blockcount.indepAll (blockcount.blockSpan (pieri.oneBox d)) :=
    (lowerspan.spanReads (pieri.oneBox d)).2.1
  intro k
  induction k with
  | zero =>
    intro s _ hdeg
    rw [countPower_vac s hdeg, pathsquare.pathCount_vac s hdeg]
  | succ k ih =>
    intro s hlen hdeg
    have hpack := monPool_pack d hd k
    have hexp : blockcount.countAt (monPool d (k + 1)) (rowList s)
        = ground.famFold Nat.add 0
            (fun mu => blockcount.countAt (monPool d k) mu
              * blockcount.countAt (blockcount.fusedAt
                  (blockcount.blockSpan (places.shapeOf mu))
                  (blockcount.blockSpan (pieri.oneBox d)))
                (rowList s))
            (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
              blockcount.HVec.content)) :=
      blockcount.countAt_fused_exhaust d k (monPool d k) hpack.1
        hpack.2.1 hpack.2.2.1 hpack.2.2.2
        (blockcount.blockSpan (pieri.oneBox d)) hszB hwidB hclB hiC
        (rowList s)
    have hmemD : ∀ mu, 0 < ground.countOf mu
        (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content)) →
        mu ∈ (blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content := by
      intro mu hmu
      exact ground.mem_of_dedupL (ground.mem_of_countOf_pos _ _ hmu)
    have hrlD : ∀ mu, 0 < ground.countOf mu
        (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content)) →
        rowList (places.shapeOf mu) = mu := by
      intro mu hmu
      exact blockcount.exhaust_rowList_shapeOf d (monPool d k) hpack.1
        hpack.2.1 hpack.2.2.2 mu (hmemD mu hmu)
    have hwidD : ∀ mu, 0 < ground.countOf mu
        (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content)) → mu.length = d := by
      intro mu hmu
      exact blockcount.exhaust_width d (monPool d k) hpack.1
        hpack.2.1 hpack.2.2.2 mu (hmemD mu hmu)
    have hpoint : ∀ mu, 0 < ground.countOf mu
        (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content)) →
        blockcount.countAt (monPool d k) mu
            * blockcount.countAt (blockcount.fusedAt
                (blockcount.blockSpan (places.shapeOf mu))
                (blockcount.blockSpan (pieri.oneBox d)))
              (rowList s)
          = blockcount.countAt (monPool d k) mu
            * ground.countOf (places.shapeOf mu) (units.removals s) := by
      intro mu hmu
      have hshl : (places.shapeOf mu).length = d := by
        rw [places.length_shapeOf mu]
        exact hwidD mu hmu
      have hfc := blockcount.fusionCount_countAt (places.shapeOf mu)
        (pieri.oneBox d) s (by rw [pieri.length_oneBox d, hshl])
      have hpr : blockcount.fusionCount (places.shapeOf mu)
          (pieri.oneBox (places.shapeOf mu).length) s
          = ground.countOf s (pieri.row (places.shapeOf mu)) :=
        pieri.readAll (places.shapeOf mu) s (by rw [hshl]; exact hd)
          (by rw [hshl]; exact hlen)
      have hpr' : blockcount.fusionCount (places.shapeOf mu)
          (pieri.oneBox d) s
          = ground.countOf s (pieri.row (places.shapeOf mu)) := by
        rw [← congrArg pieri.oneBox hshl]
        exact hpr
      have hmir := pathsquare.row_removals (places.shapeOf mu) s
      rw [← hfc, hpr', hmir]
    have hcol := fold_collapse (blockcount.countAt (monPool d k))
      (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content))
      (fun mu => ground.countOf_dedupL_le mu _)
      (by
        intro mu hz
        rw [blockcount.countAt_exhaust d (monPool d k) hpack.1 hpack.2.1
            hpack.2.2.2 mu,
          blockcount.occ_eq_countOf mu
            (blockcount.exhaust d (monPool d k))]
        match Nat.eq_zero_or_pos (ground.countOf mu
            ((blockcount.exhaust d (monPool d k)).map
              blockcount.HVec.content)) with
        | .inl h0 => exact h0
        | .inr hp =>
          have hcc : 0 < ground.countOf mu
              (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
                blockcount.HVec.content)) :=
            ground.countOf_pos_of_mem
              (ground.mem_dedupL (ground.mem_of_countOf_pos mu _ hp))
          rw [hz] at hcc
          exact absurd hcc (Nat.lt_irrefl 0))
      hrlD (units.removals s)
    have hIH : ground.famFold Nat.add 0
        (fun y => blockcount.countAt (monPool d k) (rowList y))
        (units.removals s)
      = ground.famFold Nat.add 0 pathsquare.pathCount
          (units.removals s) := by
      refine ground.famFold_congr_members Nat.add 0 _ _
        (units.removals s) ?_
      intro y hy
      obtain ⟨hdy, hly⟩ := pathsquare.degree_removals s y hy
      have hdy' : places.degree y = k := by
        rw [hdeg] at hdy
        exact Nat.succ.inj hdy
      have hlyd : y.length = d := by
        rw [hly]
        exact hlen
      rw [monPool_bridge d hd k y hlyd hdy']
      exact ih y hlyd hdy'
    rw [← monPool_bridge d hd (k + 1) s hlen hdeg, hexp,
      ground.famFold_congr_members Nat.add 0 _ _ _ hpoint, hcol, hIH,
      pathsquare.pathCount_step s k hdeg]

/-- The block count is the path count at every shape: the power
exhausts over the blocks, each block fuses by one boxes, and the
recursion descends the degree — `lem:mixedinv`'s first tier as the
read's general theorem. -/
theorem readAll (s : Shape) : read s := by
  match hk : places.degree s with
  | 0 =>
    show blockcount.countPower s = pathsquare.pathCount s
    rw [countPower_vac s hk, pathsquare.pathCount_vac s hk]
  | q + 1 =>
    have hpos : 0 < s.length := by
      match s, hk with
      | [], hk => exact Nat.noConfusion (hk : (0 : Nat) = q + 1)
      | _ :: t, _ => exact Nat.succ_pos t.length
    exact readGo s.length hpos (q + 1) s rfl hk

/-! `lem:mixedinv`'s carrier tier: the place permutations' matrices
on the content summands, their flat forms over the content
enumeration, each family's equivariance under the units' moves
(`con:places`' place symmetry), and the flat forms' independence
at `k ≤ d` — the invariant span's stated spanning data. -/

/-- A place permutation's matrix at a content: the row's monomial
against the permuted display of the column's, one unit entry per
row — the place action's matrix on the content summand. -/
def permMat (σ mu : List Nat) : elim.Mat :=
  let mons := places.monomialsAt mu
  mons.map (fun m =>
    mons.map (fun m' =>
      if m' = places.expo m σ then ground.BPair.ofNat 1
      else ground.BPair.unit))

/-- A matrix family's flat form: the blocks' entries concatenated
over the content enumeration, the form's own coordinates. -/
def flatF (d k : Nat) (T : List Nat → elim.Mat) : List ground.BPair :=
  (places.allContents d k).flatMap (fun mu => (T mu).flatMap (fun r => r))

/-- The flat form's width: one coordinate per pair of a content's
monomials, over the content enumeration. -/
def mixWidth (d k : Nat) : Nat :=
  ground.famFold Nat.add 0
    (fun mu =>
      let n := (places.monomialsAt mu).length
      n * n)
    (places.allContents d k)

/-- The permutation family's flat forms, one per place permutation:
the mixed carrier's stated spanning list. -/
def permFlats (d k : Nat) : elim.Mat :=
  (places.perms k).map (fun σ => flatF d k (permMat σ))

/-! The permuted display's kit: the length and entry reads, the
content preserved, the enumeration membership, the sized roundtrips
through the inverse assignment, and the identity word reading the
permutation back. -/

/-- The permuted display's length is the assignment's own. -/
private theorem expo_length (m p : List Nat) :
    (places.expo m p).length = p.length := by
  show (p.map (ground.getAt 0 m)).length = p.length
  rw [ground.length_map]

/-- The permuted display of a sized word carries the word's own
letter counts: the display rearranges the entries. -/
private theorem expo_content (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    (m : List Nat) (hm : m.length = k) (x : Nat) :
    ground.countOf x (places.expo m σ) = ground.countOf x m := by
  show ground.countOf x (σ.map (ground.getAt 0 m)) = _
  rw [ground.countOf_map_famFold x (ground.getAt 0 m) σ,
    ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun q => if x = ground.getAt 0 m q then 1 else 0) σ
      (List.range k) (places.perm_counts_range k hσ),
    ← ground.countOf_map_famFold x (ground.getAt 0 m) (List.range k),
    ground.range_map_getAt 0 k m hm]

/-- The permuted display of an enumeration member is a member,
once: the display keeps the degree and the content. -/
private theorem countOf_expo_monomialsAt (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    {mu : List Nat} (hsum : ground.sumNat mu = k)
    {m : List Nat}
    (hm : 0 < ground.countOf m (places.monomialsAt mu)) :
    ground.countOf (places.expo m σ) (places.monomialsAt mu) = 1 := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := places.perm_member_reads hσ
  obtain ⟨hml, hmc⟩ := places.member_conditions hm
  have hmk : m.length = k := by rw [hml, hsum]
  have hcont : places.content mu.length (places.expo m σ)
      = places.content mu.length m := by
    show (List.range mu.length).map
        (fun i => ground.countOf i (places.expo m σ))
      = (List.range mu.length).map (fun i => ground.countOf i m)
    exact ground.map_congr_all _ _
      (fun i => expo_content k hσ m hmk i) (List.range mu.length)
  rw [places.countOf_monomialsAt,
    if_pos ⟨by rw [expo_length, hlen, hsum], by rw [hcont, hmc]⟩]

/-- The sized roundtrip: the permuted display read back through the
inverse assignment recovers the word. -/
private theorem expo_roundtrip (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    (m : List Nat) (hm : m.length = k) :
    places.expo (places.expo m σ) (places.invPerm k σ) = m := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := places.perm_member_reads hσ
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [expo_length, places.length_invPerm, hm]
  · intro t ht
    rw [expo_length, places.length_invPerm] at ht
    rw [places.getAt_expo (places.expo m σ) (places.invPerm k σ) t
        (by rw [places.length_invPerm]; exact ht),
      places.getAt_invPerm k σ ht,
      places.getAt_expo m σ (places.posOf t σ)
        (places.posOf_lt t σ (hocc t ht)),
      places.getAt_posOf t σ (hocc t ht)]

/-- The mirror roundtrip: the inverse display read back through the
assignment recovers the word. -/
private theorem expo_roundtrip' (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    (m : List Nat) (hm : m.length = k) :
    places.expo (places.expo m (places.invPerm k σ)) σ = m := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := places.perm_member_reads hσ
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [expo_length, hlen, hm]
  · intro t ht
    rw [expo_length, hlen] at ht
    have hσt : ground.getAt 0 σ t < k :=
      hval _ (ground.countOf_getAt_pos 0 σ t (by rw [hlen]; exact ht))
    rw [places.getAt_expo (places.expo m (places.invPerm k σ)) σ t
        (by rw [hlen]; exact ht),
      places.getAt_expo m (places.invPerm k σ) (ground.getAt 0 σ t)
        (by rw [places.length_invPerm]; exact hσt),
      places.getAt_invPerm k σ hσt,
      places.posOf_getAt hdist t (by rw [hlen]; exact ht)]

/-- The identity word's permuted display is the permutation itself:
each place reads its own letter. -/
private theorem expo_range_id (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k)) :
    places.expo (List.range k) σ = σ := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := places.perm_member_reads hσ
  refine ground.getAt_ext 0 _ _ (by rw [expo_length, hlen]) ?_
  intro t ht
  rw [expo_length] at ht
  rw [places.getAt_expo (List.range k) σ t ht,
    ground.getAt_range k _
      (hval _ (ground.countOf_getAt_pos 0 σ t ht))]

/-! The Leibniz count's positional read and its transport across
the display: the outputs reading a word are the places holding the
withdrawn letter whose re-read is the word, and the indicator's
fold reindexes along the permutation. -/

/-- The Leibniz count positionally: the indicator's fold over the
key range, each place holding the withdrawn letter and re-read at
the entered one. -/
private theorem countAct_fold (i j : Nat) :
    ∀ (w u : List Nat),
      ground.countOf u (units.unitAct i j w)
        = ground.famFold Nat.add 0
            (fun q => if ground.getAt 0 w q = j
                ∧ u = List.set w q i then 1 else 0)
            (List.range w.length)
  | [], _ => rfl
  | a :: t, u => by
    show ground.countOf u
        ((if a == j then [i :: t] else [])
          ++ (units.unitAct i j t).map (fun m => a :: m))
      = ground.famFold Nat.add 0
          (fun q => if ground.getAt 0 (a :: t) q = j
              ∧ u = List.set (a :: t) q i then 1 else 0)
          (List.range (t.length + 1))
    rw [ground.countOf_append, ground.range_cons t.length]
    show ground.countOf u (if a == j then [i :: t] else [])
        + ground.countOf u
            ((units.unitAct i j t).map (fun m => a :: m))
      = (if a = j ∧ u = i :: t then 1 else 0)
        + ground.famFold Nat.add 0
            (fun q => if ground.getAt 0 (a :: t) q = j
                ∧ u = List.set (a :: t) q i then 1 else 0)
            ((List.range t.length).map (fun q => q + 1))
    rw [ground.famFold_map Nat.add 0
        (fun q => if ground.getAt 0 (a :: t) q = j
            ∧ u = List.set (a :: t) q i then 1 else 0)
        (fun q => q + 1) (List.range t.length)]
    have hhead : ground.countOf u (if a == j then [i :: t] else [])
        = if a = j ∧ u = i :: t then 1 else 0 := by
      by_cases haj : a = j
      · rw [if_pos (ground.eqBeqOf haj)]
        rw [ground.countOf_cons u (i :: t) ([] : List (List Nat))]
        show (if u = i :: t then 1 else 0) + 0
          = if a = j ∧ u = i :: t then 1 else 0
        by_cases hu : u = i :: t
        · rw [if_pos hu, if_pos ⟨haj, hu⟩]
        · rw [if_neg hu, if_neg (fun hc => hu hc.2)]
      · rw [if_neg (fun hc => haj (ground.beqEqOf hc)),
          if_neg (fun hc => haj hc.1)]
        rfl
    have htail : ground.countOf u
        ((units.unitAct i j t).map (fun m => a :: m))
        = ground.famFold Nat.add 0
            (fun q => if ground.getAt 0 t q = j
                ∧ u = a :: List.set t q i then 1 else 0)
            (List.range t.length) := by
      match u with
      | [] =>
        rw [ground.countOf_nil_consMap a (units.unitAct i j t)]
        refine (ground.famFold_zero _ ?_ (List.range t.length)).symm
        intro q
        exact if_neg (fun hc => nomatch hc.2)
      | b :: u' =>
        rw [ground.countOf_consMap b a (units.unitAct i j t) u']
        by_cases hba : b = a
        · rw [if_pos hba, countAct_fold i j t u']
          refine ground.famFold_congr_all Nat.add 0 _ _ ?_
            (List.range t.length)
          intro q
          by_cases h1 : ground.getAt 0 t q = j
          · by_cases h2 : u' = List.set t q i
            · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h1, by rw [hba, h2]⟩]
            · rw [if_neg (fun hc => h2 hc.2),
                if_neg (fun hc => h2 (List.cons.inj hc.2).2)]
          · rw [if_neg (fun hc => h1 hc.1),
              if_neg (fun hc => h1 hc.1)]
        · rw [if_neg hba]
          refine (ground.famFold_zero _ ?_ (List.range t.length)).symm
          intro q
          exact if_neg (fun hc => hba (List.cons.inj hc.2).1)
    rw [hhead, htail]
    rfl

/-- The update commutes with the display: writing the permuted
display at a place is the display of the word written at that
place's letter. -/
private theorem set_expo (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    (w : List Nat) (hw : w.length = k) (q : Nat) (hq : q < k)
    (i : Nat) :
    List.set (places.expo w σ) q i
      = places.expo (List.set w (ground.getAt 0 σ q) i) σ := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := places.perm_member_reads hσ
  have hσq : ground.getAt 0 σ q < k :=
    hval _ (ground.countOf_getAt_pos 0 σ q (by rw [hlen]; exact hq))
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [ground.length_set, expo_length, expo_length]
  · intro t ht
    rw [ground.length_set, expo_length, hlen] at ht
    by_cases htq : t = q
    · rw [htq,
        ground.getAt_set_self 0 i (places.expo w σ) q
          (by rw [expo_length, hlen]; exact hq),
        places.getAt_expo (List.set w (ground.getAt 0 σ q) i) σ q
          (by rw [hlen]; exact hq),
        ground.getAt_set_self 0 i w (ground.getAt 0 σ q)
          (by rw [hw]; exact hσq)]
    · have hσne : ¬ ground.getAt 0 σ t = ground.getAt 0 σ q := by
        intro he
        refine htq ?_
        have h1 := places.posOf_getAt hdist t (by rw [hlen]; exact ht)
        have h2 := places.posOf_getAt hdist q (by rw [hlen]; exact hq)
        rw [← h1, he, h2]
      rw [ground.getAt_set_ne 0 (places.expo w σ) q t i htq,
        places.getAt_expo w σ t (by rw [hlen]; exact ht),
        places.getAt_expo (List.set w (ground.getAt 0 σ q) i) σ t
          (by rw [hlen]; exact ht),
        ground.getAt_set_ne 0 w (ground.getAt 0 σ q)
          (ground.getAt 0 σ t) i hσne]

/-- The Leibniz count transports across the display: the outputs
reading a permuted target against a permuted source are the
underlying pair's own, the positional fold reindexed along the
permutation. -/
private theorem countAct_expo (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    (i j : Nat) (u w : List Nat) (hu : u.length = k)
    (hw : w.length = k) :
    ground.countOf (places.expo u σ)
        (units.unitAct i j (places.expo w σ))
      = ground.countOf u (units.unitAct i j w) := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := places.perm_member_reads hσ
  have hpoint : ∀ q, 0 < ground.countOf q (List.range k) →
      (if ground.getAt 0 (places.expo w σ) q = j
          ∧ places.expo u σ = List.set (places.expo w σ) q i
        then 1 else 0)
      = (if ground.getAt 0 w (ground.getAt 0 σ q) = j
          ∧ u = List.set w (ground.getAt 0 σ q) i
        then 1 else 0) := by
    intro q hq
    have hqk : q < k := ground.ltOfMem hq
    have hc1 : ground.getAt 0 (places.expo w σ) q
        = ground.getAt 0 w (ground.getAt 0 σ q) :=
      places.getAt_expo w σ q (by rw [hlen]; exact hqk)
    have hc2 : (places.expo u σ = List.set (places.expo w σ) q i)
        ↔ (u = List.set w (ground.getAt 0 σ q) i) := by
      constructor
      · intro he
        rw [set_expo k hσ w hw q hqk i] at he
        have h2 := congrArg
          (fun z => places.expo z (places.invPerm k σ)) he
        rw [expo_roundtrip k hσ u hu,
          expo_roundtrip k hσ (List.set w (ground.getAt 0 σ q) i)
            (by rw [ground.length_set, hw])] at h2
        exact h2
      · intro he
        rw [he, set_expo k hσ w hw q hqk i]
    by_cases h1 : ground.getAt 0 w (ground.getAt 0 σ q) = j
    · by_cases h2 : u = List.set w (ground.getAt 0 σ q) i
      · rw [if_pos ⟨by rw [hc1]; exact h1, hc2.mpr h2⟩,
          if_pos ⟨h1, h2⟩]
      · rw [if_neg (fun hc => h2 (hc2.mp hc.2)),
          if_neg (fun hc => h2 hc.2)]
    · rw [if_neg (fun hc => h1 (by rw [← hc1]; exact hc.1)),
        if_neg (fun hc => h1 hc.1)]
  refine Eq.trans
    (countAct_fold i j (places.expo w σ) (places.expo u σ)) ?_
  refine Eq.trans ?_ (countAct_fold i j w u).symm
  rw [expo_length, hlen, hw]
  refine Eq.trans
    (ground.famFold_congr_members Nat.add 0 _ _ (List.range k)
      hpoint) ?_
  exact Eq.trans
    (ground.famFold_getAt Nat.add 0
      (fun p => if ground.getAt 0 w p = j
          ∧ u = List.set w p i then 1 else 0) 0 σ k hlen)
    (ground.famFold_relist Nat.add 0 Nat.add_comm Nat.add_assoc
      (fun p => if ground.getAt 0 w p = j
          ∧ u = List.set w p i then 1 else 0) σ (List.range k)
      (places.perm_counts_range k hσ))

/-- The moved count across the display: the target read against the
column's inverse display is the target's display against the column
— at an occupied withdrawn letter by the sized transport, at a
vacant one both actions empty. -/
private theorem countAct_moved (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    {mu : List Nat} (hsum : ground.sumNat mu = k)
    (i j : Nat) (hi : i < mu.length) {vp wq : List Nat}
    (hvp : 0 < ground.countOf vp
      (places.monomialsAt (blockcount.moveAt i j mu)))
    (hwq : 0 < ground.countOf wq (places.monomialsAt mu)) :
    ground.countOf vp
        (units.unitAct i j (places.expo wq (places.invPerm k σ)))
      = ground.countOf (places.expo vp σ) (units.unitAct i j wq) := by
  obtain ⟨hlen, hdist, hval, hocc⟩ := places.perm_member_reads hσ
  have hτ : 0 < ground.countOf (places.invPerm k σ) (places.perms k) :=
    places.invPerm_member k hσ
  have hwql : wq.length = k :=
    (places.member_conditions hwq).1.trans hsum
  by_cases hoccj : 0 < ground.getAt 0 mu j
  · have hd : ground.sumNat (ground.dipAt j mu) + 1
        = ground.sumNat mu := ground.sumNat_dipAt j mu hoccj
    have hb : ground.sumNat (blockcount.moveAt i j mu)
        = ground.sumNat (ground.dipAt j mu) + 1 := by
      show ground.sumNat (ground.bumpAt i (ground.dipAt j mu)) = _
      exact ground.sumNat_bumpAt i (ground.dipAt j mu)
        (by rw [ground.length_dipAt]; exact hi)
    have hsum' : ground.sumNat (blockcount.moveAt i j mu) = k := by
      rw [hb, hd, hsum]
    have hvpl : vp.length = k :=
      (places.member_conditions hvp).1.trans hsum'
    have hstep := countAct_expo k hτ i j (places.expo vp σ) wq
      (by rw [expo_length, hlen]) hwql
    rw [expo_roundtrip k hσ vp hvpl] at hstep
    exact hstep
  · have hz : ground.getAt 0 mu j = 0 :=
      match Nat.eq_zero_or_pos (ground.getAt 0 mu j) with
      | .inl h => h
      | .inr h => absurd h hoccj
    have hstar : 0 < ground.countOf
        (places.expo wq (places.invPerm k σ))
        (places.monomialsAt mu) := by
      rw [countOf_expo_monomialsAt k hτ hsum hwq]
      exact Nat.succ_pos 0
    rw [units.unitAct_nil_of_zero i j
        (places.expo wq (places.invPerm k σ))
        (places.letter_zero mu j hz _ hstar),
      units.unitAct_nil_of_zero i j wq
        (places.letter_zero mu j hz wq hwq)]
    rfl

/-! The permutation matrix's frames and entry read, with the
composite entries: the unit matrix against the permutation matrix
collapses at the permuted column, the permutation matrix against
the unit matrix at the permuted row, and the moved count equates
them. -/

/-- The permutation matrix's row count is the enumeration's. -/
private theorem length_permMat (σ mu : List Nat) :
    (permMat σ mu).length = (places.monomialsAt mu).length := by
  show ((places.monomialsAt mu).map _).length = _
  rw [ground.length_map]

/-- The permutation matrix is square at the enumeration's width. -/
private theorem rowsLen_permMat (σ mu : List Nat) :
    elim.rowsLen (places.monomialsAt mu).length (permMat σ mu) := by
  show elim.rowsLen (places.monomialsAt mu).length
    ((places.monomialsAt mu).map (fun m =>
      (places.monomialsAt mu).map (fun m' =>
        if m' = places.expo m σ then ground.BPair.ofNat 1
        else ground.BPair.unit)))
  exact elim.rowsLen_map _ _ _ (fun m _ => ground.length_map _ _)

/-- The permutation matrix's entry: one exactly where the column's
monomial is the row's permuted display. -/
private theorem permMat_entry (σ mu : List Nat) (r c : Nat)
    (hr : r < (places.monomialsAt mu).length)
    (hc : c < (places.monomialsAt mu).length) :
    ground.getAt ground.BPair.unit
        (ground.getAt [] (permMat σ mu) r) c
      = if ground.getAt [] (places.monomialsAt mu) c
          = places.expo (ground.getAt [] (places.monomialsAt mu) r) σ
        then ground.BPair.ofNat 1 else ground.BPair.unit := by
  show ground.getAt ground.BPair.unit
      (ground.getAt [] ((places.monomialsAt mu).map (fun m =>
        (places.monomialsAt mu).map (fun m' =>
          if m' = places.expo m σ then ground.BPair.ofNat 1
          else ground.BPair.unit))) r) c = _
  rw [ground.getAt_map ([] : List Nat) ([] : List ground.BPair) _
      (places.monomialsAt mu) r hr,
    ground.getAt_map ([] : List Nat) ground.BPair.unit _
      (places.monomialsAt mu) c hc]

/-- The left composite's entry: the unit matrix against the
permutation matrix collapses at the permuted column — the Leibniz
count at the column's word read through the inverse display. -/
private theorem entry_left (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    {mu : List Nat} (hsum : ground.sumNat mu = k)
    (i j : Nat) (hi : i < mu.length) (hij : ¬ i = j) (p q : Nat)
    (hp : p < (places.monomialsAt (blockcount.moveAt i j mu)).length)
    (hq : q < (places.monomialsAt mu).length) :
    (ground.getAt ground.BPair.unit
        (ground.getAt []
          (elim.matMul
            (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
            (permMat σ mu)) p) q).oneValue
      (ground.BPair.ofNat (ground.countOf
        (ground.getAt []
          (places.monomialsAt (blockcount.moveAt i j mu)) p)
        (units.unitAct i j
          (places.expo (ground.getAt [] (places.monomialsAt mu) q)
            (places.invPerm k σ))))) := by
  obtain ⟨hσlen, hσdist, hσval, hσocc⟩ := places.perm_member_reads hσ
  have hτ : 0 < ground.countOf (places.invPerm k σ)
      (places.perms k) := places.invPerm_member k hσ
  have hwq : 0 < ground.countOf
      (ground.getAt [] (places.monomialsAt mu) q)
      (places.monomialsAt mu) :=
    ground.countOf_getAt_pos [] (places.monomialsAt mu) q hq
  have hwql : (ground.getAt [] (places.monomialsAt mu) q).length
      = k := (places.member_conditions hwq).1.trans hsum
  have hmstar : ground.countOf
      (places.expo (ground.getAt [] (places.monomialsAt mu) q)
        (places.invPerm k σ)) (places.monomialsAt mu) = 1 :=
    countOf_expo_monomialsAt k hτ hsum hwq
  have hout := blockcount.out_gen mu i j hi hij
  have hUrows := units.rowsLen_matUnitAt
    (blockcount.moveAt i j mu) mu i j
  have hUlen := units.length_matUnitAt
    (blockcount.moveAt i j mu) mu i j
  have hProws := rowsLen_permMat σ mu
  have hPlen := length_permMat σ mu
  have hP0 : 0 < (permMat σ mu).length := by
    rw [hPlen]
    exact places.monomialsAt_occupied mu
  have hpU : p < (units.matUnitAt
      (blockcount.moveAt i j mu) mu i j).length := by
    rw [hUlen]
    exact hp
  have hqT : q < (elim.transposeM (permMat σ mu)).length := by
    rw [elim.length_transposeM (permMat σ mu) hProws hP0]
    exact hq
  rw [show elim.matMul
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
        (permMat σ mu)
      = (units.matUnitAt (blockcount.moveAt i j mu) mu i j).map
          (fun r => (elim.transposeM (permMat σ mu)).map
            (fun c => elim.dotN r c)) from rfl,
    ground.getAt_map ([] : List ground.BPair)
      ([] : List ground.BPair) _
      (units.matUnitAt (blockcount.moveAt i j mu) mu i j) p hpU,
    ground.getAt_map ([] : List ground.BPair) ground.BPair.unit _
      (elim.transposeM (permMat σ mu)) q hqT]
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (elim.dotP_ofNat_fold
      (fun m => ground.countOf
        (ground.getAt []
          (places.monomialsAt (blockcount.moveAt i j mu)) p)
        (units.unitAct i j m))
      (fun m => if ground.getAt [] (places.monomialsAt mu) q
          = places.expo m σ then 1 else 0)
      (places.monomialsAt mu) _ _
      (elim.rowsLen_getAt _ p hUrows hpU)
      (by
        rw [elim.rowsLen_getAt (elim.transposeM (permMat σ mu)) q
            (elim.rowsLen_transposeM (permMat σ mu)) hqT, hPlen])
      (fun r hr => units.matUnitAt_read
        (blockcount.moveAt i j mu) mu i j hout p r hp hr)
      (fun r hr => by
        rw [elim.getAt_transposeM ground.BPair.unit (permMat σ mu)
            hProws q r hq (by rw [hPlen]; exact hr),
          permMat_entry σ mu r q hr hq]
        by_cases hcase : ground.getAt [] (places.monomialsAt mu) q
            = places.expo (ground.getAt []
              (places.monomialsAt mu) r) σ
        · rw [if_pos hcase, if_pos hcase]
          exact BPair.oneValue_refl _
        · rw [if_neg hcase, if_neg hcase]
          exact BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_of_eq (congrArg ground.BPair.ofNat ?_)
  refine Eq.trans
    (ground.famFold_congr_members Nat.add 0 _
      (fun m => if m = places.expo
          (ground.getAt [] (places.monomialsAt mu) q)
          (places.invPerm k σ) then
        ground.countOf
          (ground.getAt []
            (places.monomialsAt (blockcount.moveAt i j mu)) p)
          (units.unitAct i j m)
      else 0)
      (places.monomialsAt mu) ?_) ?_
  · intro m hm
    have hml : m.length = k :=
      (places.member_conditions hm).1.trans hsum
    by_cases hcond : ground.getAt [] (places.monomialsAt mu) q
        = places.expo m σ
    · have hmm : m = places.expo
          (ground.getAt [] (places.monomialsAt mu) q)
          (places.invPerm k σ) := by
        rw [hcond]
        exact (expo_roundtrip k hσ m hml).symm
      rw [if_pos hcond, Nat.mul_one, if_pos hmm]
    · have hne : ¬ m = places.expo
          (ground.getAt [] (places.monomialsAt mu) q)
          (places.invPerm k σ) := fun hmm => hcond (by
        rw [hmm]
        exact (expo_roundtrip' k hσ
          (ground.getAt [] (places.monomialsAt mu) q) hwql).symm)
      rw [if_neg hcond, Nat.mul_zero, if_neg hne]
  · exact ground.famFold_pick _ _ (places.monomialsAt mu) hmstar

/-- The right composite's entry: the permutation matrix against the
unit matrix collapses at the permuted row — the Leibniz count of
the row's display at the column's word. -/
private theorem entry_right (k : Nat) {σ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    {mu : List Nat} (hsum : ground.sumNat mu = k)
    (i j : Nat) (hi : i < mu.length) (hij : ¬ i = j) (p q : Nat)
    (hp : p < (places.monomialsAt (blockcount.moveAt i j mu)).length)
    (hq : q < (places.monomialsAt mu).length) :
    (ground.getAt ground.BPair.unit
        (ground.getAt []
          (elim.matMul (permMat σ (blockcount.moveAt i j mu))
            (units.matUnitAt (blockcount.moveAt i j mu) mu i j))
          p) q).oneValue
      (ground.BPair.ofNat (ground.countOf
        (places.expo (ground.getAt []
          (places.monomialsAt (blockcount.moveAt i j mu)) p) σ)
        (units.unitAct i j
          (ground.getAt [] (places.monomialsAt mu) q)))) := by
  obtain ⟨hσlen, hσdist, hσval, hσocc⟩ := places.perm_member_reads hσ
  have hwq : 0 < ground.countOf
      (ground.getAt [] (places.monomialsAt mu) q)
      (places.monomialsAt mu) :=
    ground.countOf_getAt_pos [] (places.monomialsAt mu) q hq
  have hout := blockcount.out_gen mu i j hi hij
  have hUrows := units.rowsLen_matUnitAt
    (blockcount.moveAt i j mu) mu i j
  have hUlen := units.length_matUnitAt
    (blockcount.moveAt i j mu) mu i j
  have hU0 : 0 < (units.matUnitAt
      (blockcount.moveAt i j mu) mu i j).length := by
    rw [hUlen]
    exact places.monomialsAt_occupied (blockcount.moveAt i j mu)
  have hP'rows := rowsLen_permMat σ (blockcount.moveAt i j mu)
  have hP'len := length_permMat σ (blockcount.moveAt i j mu)
  have hpP' : p < (permMat σ (blockcount.moveAt i j mu)).length := by
    rw [hP'len]
    exact hp
  have hqTU : q < (elim.transposeM (units.matUnitAt
      (blockcount.moveAt i j mu) mu i j)).length := by
    rw [elim.length_transposeM _ hUrows hU0]
    exact hq
  rw [show elim.matMul (permMat σ (blockcount.moveAt i j mu))
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
      = (permMat σ (blockcount.moveAt i j mu)).map
          (fun r => (elim.transposeM (units.matUnitAt
            (blockcount.moveAt i j mu) mu i j)).map
            (fun c => elim.dotN r c)) from rfl,
    ground.getAt_map ([] : List ground.BPair)
      ([] : List ground.BPair) _
      (permMat σ (blockcount.moveAt i j mu)) p hpP',
    ground.getAt_map ([] : List ground.BPair) ground.BPair.unit _
      (elim.transposeM (units.matUnitAt
        (blockcount.moveAt i j mu) mu i j)) q hqTU]
  refine BPair.oneValue_trans (elim.dotN_read _ _) ?_
  refine BPair.oneValue_trans
    (elim.dotP_ofNat_fold
      (fun m => if m = places.expo (ground.getAt []
          (places.monomialsAt (blockcount.moveAt i j mu)) p) σ
        then 1 else 0)
      (fun m => ground.countOf m (units.unitAct i j
        (ground.getAt [] (places.monomialsAt mu) q)))
      (places.monomialsAt (blockcount.moveAt i j mu)) _ _
      (by
        rw [elim.rowsLen_getAt _ p hP'rows hpP'])
      (by
        rw [elim.rowsLen_getAt _ q
            (elim.rowsLen_transposeM _) hqTU, hUlen])
      (fun r hr => by
        rw [permMat_entry σ (blockcount.moveAt i j mu) p r hp hr]
        by_cases hcase : ground.getAt []
            (places.monomialsAt (blockcount.moveAt i j mu)) r
            = places.expo (ground.getAt []
              (places.monomialsAt (blockcount.moveAt i j mu)) p) σ
        · rw [if_pos hcase, if_pos hcase]
          exact BPair.oneValue_refl _
        · rw [if_neg hcase, if_neg hcase]
          exact BPair.oneValue_refl _)
      (fun r hr => by
        rw [elim.getAt_transposeM ground.BPair.unit _ hUrows q r hq
            (by rw [hUlen]; exact hr)]
        exact units.matUnitAt_read
          (blockcount.moveAt i j mu) mu i j hout r q hr hq)) ?_
  refine BPair.oneValue_of_eq (congrArg ground.BPair.ofNat ?_)
  by_cases hoccj : 0 < ground.getAt 0 mu j
  · have hd : ground.sumNat (ground.dipAt j mu) + 1
        = ground.sumNat mu := ground.sumNat_dipAt j mu hoccj
    have hb : ground.sumNat (blockcount.moveAt i j mu)
        = ground.sumNat (ground.dipAt j mu) + 1 := by
      show ground.sumNat (ground.bumpAt i (ground.dipAt j mu)) = _
      exact ground.sumNat_bumpAt i (ground.dipAt j mu)
        (by rw [ground.length_dipAt]; exact hi)
    have hsum' : ground.sumNat (blockcount.moveAt i j mu) = k := by
      rw [hb, hd, hsum]
    have hvp : 0 < ground.countOf (ground.getAt []
        (places.monomialsAt (blockcount.moveAt i j mu)) p)
        (places.monomialsAt (blockcount.moveAt i j mu)) :=
      ground.countOf_getAt_pos []
        (places.monomialsAt (blockcount.moveAt i j mu)) p hp
    have hmdag : ground.countOf
        (places.expo (ground.getAt []
          (places.monomialsAt (blockcount.moveAt i j mu)) p) σ)
        (places.monomialsAt (blockcount.moveAt i j mu)) = 1 :=
      countOf_expo_monomialsAt k hσ hsum' hvp
    refine Eq.trans
      (ground.famFold_congr_members Nat.add 0 _
        (fun m => if m = places.expo (ground.getAt []
            (places.monomialsAt (blockcount.moveAt i j mu)) p) σ
          then ground.countOf m (units.unitAct i j
            (ground.getAt [] (places.monomialsAt mu) q))
          else 0)
        (places.monomialsAt (blockcount.moveAt i j mu)) ?_) ?_
    · intro m _
      by_cases hm : m = places.expo (ground.getAt []
          (places.monomialsAt (blockcount.moveAt i j mu)) p) σ
      · rw [if_pos hm, if_pos hm, Nat.one_mul]
      · rw [if_neg hm, if_neg hm, Nat.zero_mul]
    · exact ground.famFold_pick _ _
        (places.monomialsAt (blockcount.moveAt i j mu)) hmdag
  · have hz : ground.getAt 0 mu j = 0 :=
      match Nat.eq_zero_or_pos (ground.getAt 0 mu j) with
      | .inl h => h
      | .inr h => absurd h hoccj
    rw [units.unitAct_nil_of_zero i j
        (ground.getAt [] (places.monomialsAt mu) q)
        (places.letter_zero mu j hz _ hwq)]
    exact ground.famFold_zero _ (fun m => Nat.mul_zero _) _

set_option linter.unusedVariables false in
/-- A place permutation's family is equivariant: the moved read at
every letter pair and every coordinate vector, the units' Leibniz
sum place-symmetric (`con:places`).  The letter bounds are
`con:units`' index frame — the proof reads only the raise's bound
through the width, so `hj` is read by no step — and the membership
`hσ` is load-bearing with its refusal committed; the check module
records the held binders beside it. -/
theorem permMat_moved (k : Nat) (σ : List Nat)
    (hσ : 0 < ground.countOf σ (places.perms k))
    (d : Nat) (mu : List Nat)
    (hmu : 0 < ground.countOf mu (places.allContents d k))
    (i j : Nat) (hi : i < d) (hj : j < d) (hij : ¬ i = j)
    (x : List ground.BPair)
    (hx : x.length = (places.monomialsAt mu).length) :
    poly.oneValue
      (elim.matVec (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
        (elim.matVec (permMat σ mu) x))
      (elim.matVec (permMat σ (blockcount.moveAt i j mu))
        (elim.matVec (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
          x)) := by
  obtain ⟨hlen, hsum⟩ := places.allContents_reads d k mu hmu
  have hi' : i < mu.length := by rw [hlen]; exact hi
  have hUrows := units.rowsLen_matUnitAt
    (blockcount.moveAt i j mu) mu i j
  have hUlen := units.length_matUnitAt
    (blockcount.moveAt i j mu) mu i j
  have hU0 : 0 < (units.matUnitAt
      (blockcount.moveAt i j mu) mu i j).length := by
    rw [hUlen]
    exact places.monomialsAt_occupied (blockcount.moveAt i j mu)
  have hProws := rowsLen_permMat σ mu
  have hPlen := length_permMat σ mu
  have hP0 : 0 < (permMat σ mu).length := by
    rw [hPlen]
    exact places.monomialsAt_occupied mu
  have hP'rows := rowsLen_permMat σ (blockcount.moveAt i j mu)
  have hP'len := length_permMat σ (blockcount.moveAt i j mu)
  have h1 := elim.matVec_comp
    (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
    (permMat σ mu) x (places.monomialsAt mu).length hProws hx
    (by rw [hPlen]; exact hUrows)
  have h2 := elim.matVec_comp (permMat σ (blockcount.moveAt i j mu))
    (units.matUnitAt (blockcount.moveAt i j mu) mu i j) x
    (places.monomialsAt mu).length hUrows hx
    (by rw [hUlen]; exact hP'rows)
  have h3 : poly.oneValue
      (elim.matVec (elim.matMul
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
        (permMat σ mu)) x)
      (elim.matVec (elim.matMul
        (permMat σ (blockcount.moveAt i j mu))
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j)) x) := by
    refine elim.matVec_rows_congr (places.monomialsAt mu).length _ _
      ?_ ?_ ?_ ?_ x
    · rw [elim.length_matMul, elim.length_matMul, hUlen, hP'len]
    · exact elim.rowsLen_cast
        (elim.length_transposeM (permMat σ mu) hProws hP0)
        (elim.rowsLen_matMul _ _)
    · exact elim.rowsLen_cast
        (elim.length_transposeM _ hUrows hU0)
        (elim.rowsLen_matMul _ _)
    · intro p hp q hq
      rw [elim.length_matMul, hUlen] at hp
      refine BPair.oneValue_trans
        (entry_left k hσ hsum i j hi' hij p q hp hq) ?_
      refine BPair.oneValue_trans
        (BPair.oneValue_of_eq (congrArg ground.BPair.ofNat
          (countAct_moved k hσ hsum i j hi'
            (ground.countOf_getAt_pos []
              (places.monomialsAt (blockcount.moveAt i j mu)) p hp)
            (ground.countOf_getAt_pos []
              (places.monomialsAt mu) q hq)))) ?_
      exact BPair.oneValue_symm
        (entry_right k hσ hsum i j hi' hij p q hp hq)
  exact poly.oneValue_trans h1
    (poly.oneValue_trans h3 (poly.oneValue_symm h2))

/-! The independence tier: the distinct-letter content and its
probe blocks, the flat pairings collapsing at the one live block
and the one live row, and the coefficient extraction at the
identity word's row — each permutation's flat form reading its own
probe alone. -/

/-- The content enumeration holds each family at most once. -/
private theorem countOf_allContents_le : ∀ (d k : Nat) (mu : List Nat),
    ground.countOf mu (places.allContents d k) ≤ 1
  | 0, 0, mu => by
    show ground.countOf mu ([] :: []) ≤ 1
    rw [ground.countOf_cons]
    by_cases hm : mu = []
    · rw [if_pos hm]
      exact Nat.le_refl 1
    · rw [if_neg hm]
      exact Nat.le_succ 0
  | 0, _ + 1, _ => Nat.le_succ 0
  | d + 1, k, mu => by
    show ground.countOf mu ((List.range (k + 1)).flatMap (fun j =>
      (places.allContents d (k - j)).map (fun m => j :: m))) ≤ 1
    rw [ground.countOf_flatMap mu _ (List.range (k + 1))]
    match mu with
    | [] =>
      rw [ground.famFold_congr_all Nat.add 0 _ (fun _ => (0 : Nat))
          (fun j => ground.countOf_nil_consMap j
            (places.allContents d (k - j)))
          (List.range (k + 1)),
        ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (List.range (k + 1))]
      exact Nat.le_succ 0
    | a :: m =>
      rw [ground.famFold_congr_all Nat.add 0 _
          (fun j => if j = a then
            ground.countOf m (places.allContents d (k - j)) else 0)
          (fun j => by
            rw [ground.countOf_consMap a j
              (places.allContents d (k - j)) m]
            by_cases hja : a = j
            · rw [if_pos hja, if_pos hja.symm]
            · rw [if_neg hja, if_neg (fun he => hja he.symm)])
          (List.range (k + 1))]
      match Nat.eq_zero_or_pos
          (ground.countOf a (List.range (k + 1))) with
      | .inl hz =>
        rw [ground.famFold_pickZero
          (fun j => ground.countOf m (places.allContents d (k - j)))
          a (List.range (k + 1)) hz]
        exact Nat.le_succ 0
      | .inr hpos =>
        have h1 : ground.countOf a (List.range (k + 1)) = 1 := by
          rw [ground.countOf_range] at hpos ⊢
          by_cases ha : a < k + 1
          · rw [if_pos ha]
          · rw [if_neg ha] at hpos
            exact absurd hpos (Nat.lt_irrefl 0)
        rw [ground.famFold_pick
          (fun j => ground.countOf m (places.allContents d (k - j)))
          a (List.range (k + 1)) h1]
        exact countOf_allContents_le d (k - a) m

/-- The accumulating sum is the box fold at the seed. -/
private theorem foldl_sumNat : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun x y => x + y) a = a + ground.sumNat l
  | [], a => (Nat.add_zero a).symm
  | b :: t, a => by
    show t.foldl (fun x y => x + y) (a + b)
      = a + (b + ground.sumNat t)
    rw [foldl_sumNat t (a + b), Nat.add_assoc]

/-- The distinct-letter content: each of the first `k` letters
once, the further letters vacant. -/
private def muStar (d k : Nat) : List Nat :=
  ground.onesRows k (d - k)

/-- The distinct-letter content's width is the letter count. -/
private theorem length_muStar (d k : Nat) (hk : k ≤ d) :
    (muStar d k).length = d := by
  show (List.replicate k 1 ++ List.replicate (d - k) 0).length = d
  rw [ground.length_append, ground.length_replicate,
    ground.length_replicate, Nat.add_comm, ground.subAdd hk]

/-- The distinct-letter content's degree is the box count. -/
private theorem sumNat_muStar (d k : Nat) :
    ground.sumNat (muStar d k) = k := by
  show ground.sumNat
    (List.replicate k 1 ++ List.replicate (d - k) 0) = k
  rw [ground.sumNat_append, ground.sumNat_replicate_one,
    ground.sumNat_replicate_zero, Nat.add_zero]

/-- The distinct-letter content's entries: one below the box count,
vacant beyond. -/
private theorem getAt_muStar (d k x : Nat) :
    ground.getAt 0 (muStar d k) x = if x < k then 1 else 0 :=
  ground.getAt_onesRows k (d - k) x

/-- A word of the box count's length holding each of the first `k`
letters once carries the distinct-letter content's conditions. -/
private theorem cond_muStar (d k : Nat) (w : List Nat)
    (hw : w.length = k)
    (hcounts : ∀ x, ground.countOf x w = if x < k then 1 else 0) :
    w.length = ground.sumNat (muStar d k)
      ∧ places.content (muStar d k).length w = muStar d k := by
  refine ⟨by rw [hw, sumNat_muStar], ?_⟩
  refine ground.getAt_ext 0 _ _ ?_ ?_
  · rw [places.content_length]
  · intro x hx
    rw [places.content_length] at hx
    rw [places.getAt_contentAt (muStar d k).length w x hx,
      hcounts x, getAt_muStar d k x]

/-- The distinct-letter content is enumerated once. -/
private theorem countOf_muStar_allContents (d k : Nat) (hk : k ≤ d) :
    ground.countOf (muStar d k) (places.allContents d k) = 1 := by
  have hmem := places.mem_allContents d (muStar d k)
    (length_muStar d k hk)
  have hfold : (muStar d k).foldl (fun a b => a + b) 0 = k := by
    rw [foldl_sumNat (muStar d k) 0, Nat.zero_add, sumNat_muStar]
  rw [hfold] at hmem
  exact Nat.le_antisymm (countOf_allContents_le d k (muStar d k))
    (ground.countOf_pos_of_mem hmem)

/-- A flattened matrix of unit-tail rows is a unit tail. -/
private theorem unitTail_flat_rows : ∀ (G : elim.Mat),
    (∀ s, s < G.length → poly.unitTail (ground.getAt [] G s)) →
    poly.unitTail (G.flatMap (fun r => r))
  | [], _ => trivial
  | _ :: G, h =>
    elim.unitTail_append (h 0 (Nat.succ_pos _))
      (unitTail_flat_rows G
        (fun s hs => h (s + 1) (Nat.succ_lt_succ hs)))

/-- A flattened family of unit-tail blocks is a unit tail. -/
private theorem unitTail_flatMap {α : Type} [DecidableEq α]
    (g : α → List ground.BPair) :
    ∀ A : List α,
      (∀ a, 0 < ground.countOf a A → poly.unitTail (g a)) →
      poly.unitTail (A.flatMap g)
  | [], _ => trivial
  | a :: A, h =>
    elim.unitTail_append
      (h a (by rw [ground.countOf_head]; exact Nat.succ_pos _))
      (unitTail_flatMap g A
        (fun b hb => h b (ground.countOf_cons_pos hb)))

/-- A flattened matrix's width: one entry per row pair at the
stated row width. -/
private theorem length_flat_rows (M : elim.Mat) (n : Nat)
    (h : elim.rowsLen n M) :
    (M.flatMap (fun r => r)).length = M.length * n :=
  elim.length_flatCat n M h

/-- A framed family's flat form length is the squares' fold. -/
private theorem length_flatF_go (S : List Nat → elim.Mat) :
    ∀ L : List (List Nat),
      (∀ mu ∈ L, elim.rowsLen (places.monomialsAt mu).length
        (S mu)) →
      (∀ mu ∈ L, (S mu).length = (places.monomialsAt mu).length) →
      (L.flatMap (fun mu =>
        (S mu).flatMap (fun r => r))).length
        = ground.famFold Nat.add 0
            (fun mu => (places.monomialsAt mu).length
              * (places.monomialsAt mu).length) L
  | [], _, _ => rfl
  | mu :: L, hr, hl => by
    show (elim.flatCat (S mu)
      ++ L.flatMap (fun nu => (S nu).flatMap (fun r => r))).length
      = (places.monomialsAt mu).length
          * (places.monomialsAt mu).length
        + ground.famFold Nat.add 0 _ L
    rw [ground.length_append,
      elim.length_flatCat (places.monomialsAt mu).length (S mu)
        (hr mu (List.Mem.head L)),
      hl mu (List.Mem.head L),
      length_flatF_go S L
        (fun nu hn => hr nu (List.Mem.tail mu hn))
        (fun nu hn => hl nu (List.Mem.tail mu hn))]

/-- A permutation's flat form sits at the stated width, the
general's own read. -/
private theorem length_flatF_permMat (d k : Nat) (σ : List Nat) :
    (flatF d k (permMat σ)).length = mixWidth d k := by
  show ((places.allContents d k).flatMap
      (fun mu => (permMat σ mu).flatMap (fun r => r))).length = _
  exact length_flatF_go (permMat σ) (places.allContents d k)
    (fun mu _ => rowsLen_permMat σ mu)
    (fun mu _ => length_permMat σ mu)

/-- A content's vacant block: the unit family at every row. -/
private def unitBlock (mu : List Nat) : elim.Mat :=
  (places.monomialsAt mu).map (fun _ =>
    List.replicate (places.monomialsAt mu).length ground.BPair.unit)

private theorem length_unitBlock (mu : List Nat) :
    (unitBlock mu).length = (places.monomialsAt mu).length := by
  show ((places.monomialsAt mu).map _).length = _
  rw [ground.length_map]

private theorem rowsLen_unitBlock (mu : List Nat) :
    elim.rowsLen (places.monomialsAt mu).length (unitBlock mu) := by
  show elim.rowsLen _ ((places.monomialsAt mu).map _)
  exact elim.rowsLen_map _ _ _
    (fun _ _ => ground.length_replicate _ _)

private theorem getAt_unitBlock (mu : List Nat) (s : Nat)
    (hs : s < (places.monomialsAt mu).length) :
    ground.getAt [] (unitBlock mu) s
      = List.replicate (places.monomialsAt mu).length
          ground.BPair.unit := by
  show ground.getAt [] ((places.monomialsAt mu).map _) s = _
  rw [ground.getAt_map ([] : List Nat) ([] : List ground.BPair) _
      (places.monomialsAt mu) s hs]

private theorem unitTail_flat_unitBlock (mu : List Nat) :
    poly.unitTail ((unitBlock mu).flatMap (fun r => r)) := by
  refine unitTail_flat_rows (unitBlock mu) ?_
  intro s hs
  rw [length_unitBlock] at hs
  rw [getAt_unitBlock mu s hs]
  exact poly.unitTail_replicate _

/-- The probe at a permutation: the single-entry block reading the
identity word's row at the permutation's own column on the
distinct-letter content, vacant elsewhere. -/
private def probeB (d k : Nat) (σ0 mu : List Nat) : elim.Mat :=
  if mu = muStar d k then
    List.set (unitBlock mu) (places.rankOf (List.range k) mu)
      (List.set
        (List.replicate (places.monomialsAt mu).length
          ground.BPair.unit)
        (places.rankOf σ0 mu) (ground.BPair.ofNat 1))
  else unitBlock mu

private theorem probeB_on (d k : Nat) (σ0 : List Nat) :
    probeB d k σ0 (muStar d k)
      = List.set (unitBlock (muStar d k))
          (places.rankOf (List.range k) (muStar d k))
          (List.set
            (List.replicate
              (places.monomialsAt (muStar d k)).length
              ground.BPair.unit)
            (places.rankOf σ0 (muStar d k)) (ground.BPair.ofNat 1)) :=
  if_pos rfl

private theorem probeB_off (d k : Nat) (σ0 mu : List Nat)
    (hne : ¬ mu = muStar d k) :
    probeB d k σ0 mu = unitBlock mu :=
  if_neg hne

private theorem length_probeB (d k : Nat) (σ0 mu : List Nat) :
    (probeB d k σ0 mu).length = (places.monomialsAt mu).length := by
  by_cases hmu : mu = muStar d k
  · rw [hmu, probeB_on, ground.length_set, length_unitBlock]
  · rw [probeB_off d k σ0 mu hmu, length_unitBlock]

private theorem rowsLen_probeB (d k : Nat) (σ0 mu : List Nat) :
    elim.rowsLen (places.monomialsAt mu).length
      (probeB d k σ0 mu) := by
  by_cases hmu : mu = muStar d k
  · rw [hmu, probeB_on]
    refine elim.rowsLen_set _ _ _ (rowsLen_unitBlock (muStar d k)) ?_
    rw [ground.length_set, ground.length_replicate]
  · rw [probeB_off d k σ0 mu hmu]
    exact rowsLen_unitBlock mu

/-- The pairing of two flattened block families collapses at the
one live block: the off blocks' probes sit at the unit tail. -/
private theorem dotP_blocks_delta {α : Type} [DecidableEq α]
    (f g : α → List ground.BPair) (a0 : α) :
    ∀ A : List α,
      (∀ a, 0 < ground.countOf a A → (f a).length = (g a).length) →
      (∀ a, 0 < ground.countOf a A → ¬ a = a0 →
        poly.unitTail (g a)) →
      ground.countOf a0 A = 1 →
      (elim.dotP (A.flatMap f) (A.flatMap g)).oneValue
        (elim.dotP (f a0) (g a0))
  | [], _, _, h1 => Nat.noConfusion h1
  | a :: A, hlen, hoff, h1 => by
    have hha : 0 < ground.countOf a (a :: A) := by
      rw [ground.countOf_head]
      exact Nat.succ_pos _
    show (elim.dotP (f a ++ A.flatMap f)
      (g a ++ A.flatMap g)).oneValue _
    refine BPair.oneValue_trans
      (elim.dotP_append (f a) (g a) (A.flatMap f) (A.flatMap g)
        (hlen a hha)) ?_
    by_cases haa : a = a0
    · have hz : ground.countOf a0 A = 0 := by
        rw [haa, ground.countOf_head] at h1
        exact Nat.succ.inj h1
      have htail : poly.unitTail (A.flatMap g) :=
        unitTail_flatMap g A (fun b hb =>
          hoff b (ground.countOf_cons_pos hb) (fun hb0 => by
            rw [hb0, hz] at hb
            exact absurd hb (Nat.lt_irrefl 0)))
      refine BPair.oneValue_trans
        (BPair.add_congr (BPair.oneValue_refl _)
          (elim.dotP_null_tail_right _ _ htail)) ?_
      refine BPair.oneValue_trans (BPair.add_unit _) ?_
      rw [haa]
      exact BPair.oneValue_refl _
    · have h1' : ground.countOf a0 A = 1 := by
        rw [ground.countOf_head_ne (fun he => haa he.symm) A] at h1
        exact h1
      refine BPair.oneValue_trans
        (BPair.add_congr
          (elim.dotP_null_tail_right _ _ (hoff a hha haa))
          (dotP_blocks_delta f g a0 A
            (fun b hb => hlen b (ground.countOf_cons_pos hb))
            (fun b hb hb0 =>
              hoff b (ground.countOf_cons_pos hb) hb0) h1')) ?_
      exact BPair.unit_add _

/-- The pairing of two flattened matrices collapses at the one live
row: every other row of the probe sits at the unit tail. -/
private theorem dotP_rows_delta :
    ∀ (F G : elim.Mat) (t : Nat),
      F.length = G.length →
      (∀ s, s < F.length →
        (ground.getAt [] F s).length
          = (ground.getAt [] G s).length) →
      (∀ s, s < G.length → ¬ s = t →
        poly.unitTail (ground.getAt [] G s)) →
      t < F.length →
      (elim.dotP (F.flatMap (fun r => r))
          (G.flatMap (fun r => r))).oneValue
        (elim.dotP (ground.getAt [] F t) (ground.getAt [] G t))
  | [], _, t, _, _, _, ht => absurd ht (Nat.not_lt_zero t)
  | _ :: _, [], _, hl, _, _, _ => Nat.noConfusion hl
  | r :: F, s :: G, 0, _, hrow, hoff, _ => by
    show (elim.dotP (r ++ F.flatMap (fun r => r))
        (s ++ G.flatMap (fun r => r))).oneValue (elim.dotP r s)
    refine BPair.oneValue_trans
      (elim.dotP_append r s _ _ (hrow 0 (Nat.succ_pos _))) ?_
    have htail : poly.unitTail (G.flatMap (fun r => r)) :=
      unitTail_flat_rows G (fun q hq =>
        hoff (q + 1) (Nat.succ_lt_succ hq)
          (fun hc => Nat.noConfusion hc))
    refine BPair.oneValue_trans
      (BPair.add_congr (BPair.oneValue_refl _)
        (elim.dotP_null_tail_right _ _ htail)) ?_
    exact BPair.add_unit _
  | r :: F, s :: G, t + 1, hl, hrow, hoff, ht => by
    show (elim.dotP (r ++ F.flatMap (fun r => r))
        (s ++ G.flatMap (fun r => r))).oneValue
      (elim.dotP (ground.getAt [] F t) (ground.getAt [] G t))
    refine BPair.oneValue_trans
      (elim.dotP_append r s _ _ (hrow 0 (Nat.succ_pos _))) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr
        (elim.dotP_null_tail_right r s
          (hoff 0 (Nat.succ_pos _) (fun hc => Nat.noConfusion hc)))
        (dotP_rows_delta F G t (Nat.succ.inj hl)
          (fun q hq => hrow (q + 1) (Nat.succ_lt_succ hq))
          (fun q hq hqt => hoff (q + 1) (Nat.succ_lt_succ hq)
            (fun hc => hqt (Nat.succ.inj hc)))
          (Nat.lt_of_succ_lt_succ ht))) ?_
    exact BPair.unit_add _

/-- A permutation's flat form against a probe reads the agreement:
one exactly when the probe's permutation is the form's own. -/
private theorem dotP_probe_flat (d k : Nat) (hk : k ≤ d)
    {σ0 σ' : List Nat}
    (h0 : 0 < ground.countOf σ0 (places.perms k))
    (h' : 0 < ground.countOf σ' (places.perms k)) :
    (elim.dotP (flatF d k (permMat σ'))
        (flatF d k (probeB d k σ0))).oneValue
      (if σ0 = σ' then ground.BPair.ofNat 1
       else ground.BPair.unit) := by
  obtain ⟨h0len, h0dist, h0val, h0occ⟩ := places.perm_member_reads h0
  have hcondR := cond_muStar d k (List.range k) (ground.length_range k)
    (fun x => ground.countOf_range x k)
  have hr0 := places.rankOf_read (List.range k) (muStar d k)
    hcondR.1 hcondR.2
  have hcondS := cond_muStar d k σ0 h0len
    (fun x => (places.perm_counts_range k h0 x).trans
      (ground.countOf_range x k))
  have hc0 := places.rankOf_read σ0 (muStar d k) hcondS.1 hcondS.2
  refine BPair.oneValue_trans
    (dotP_blocks_delta
      (fun mu => (permMat σ' mu).flatMap (fun r => r))
      (fun mu => (probeB d k σ0 mu).flatMap (fun r => r))
      (muStar d k) (places.allContents d k)
      (fun mu _ => by
        rw [length_flat_rows (permMat σ' mu)
            (places.monomialsAt mu).length (rowsLen_permMat σ' mu),
          length_permMat,
          length_flat_rows (probeB d k σ0 mu)
            (places.monomialsAt mu).length
            (rowsLen_probeB d k σ0 mu),
          length_probeB])
      (fun mu _ hne => by
        rw [probeB_off d k σ0 mu hne]
        exact unitTail_flat_unitBlock mu)
      (countOf_muStar_allContents d k hk)) ?_
  rw [probeB_on d k σ0]
  refine BPair.oneValue_trans
    (dotP_rows_delta (permMat σ' (muStar d k))
      (List.set (unitBlock (muStar d k))
        (places.rankOf (List.range k) (muStar d k))
        (List.set
          (List.replicate
            (places.monomialsAt (muStar d k)).length
            ground.BPair.unit)
          (places.rankOf σ0 (muStar d k)) (ground.BPair.ofNat 1)))
      (places.rankOf (List.range k) (muStar d k))
      (by rw [length_permMat, ground.length_set, length_unitBlock])
      (fun s hs => by
        rw [length_permMat] at hs
        rw [elim.rowsLen_getAt (permMat σ' (muStar d k)) s
            (rowsLen_permMat σ' (muStar d k))
            (by rw [length_permMat]; exact hs)]
        by_cases hsr : s = places.rankOf (List.range k) (muStar d k)
        · rw [hsr, ground.getAt_set_self ([] : List ground.BPair) _
              (unitBlock (muStar d k))
              (places.rankOf (List.range k) (muStar d k))
              (by rw [length_unitBlock]; exact hr0.1),
            ground.length_set, ground.length_replicate]
        · rw [ground.getAt_set_ne ([] : List ground.BPair)
              (unitBlock (muStar d k))
              (places.rankOf (List.range k) (muStar d k)) s _ hsr,
            getAt_unitBlock (muStar d k) s hs,
            ground.length_replicate]
      )
      (fun s hs hsr => by
        rw [ground.length_set, length_unitBlock] at hs
        rw [ground.getAt_set_ne ([] : List ground.BPair)
            (unitBlock (muStar d k))
            (places.rankOf (List.range k) (muStar d k)) s _ hsr,
          getAt_unitBlock (muStar d k) s hs]
        exact poly.unitTail_replicate _)
      (by rw [length_permMat]; exact hr0.1)) ?_
  rw [ground.getAt_set_self ([] : List ground.BPair) _
      (unitBlock (muStar d k))
      (places.rankOf (List.range k) (muStar d k))
      (by rw [length_unitBlock]; exact hr0.1)]
  refine BPair.oneValue_trans
    (elim.dotP_oneIndex
      (ground.getAt [] (permMat σ' (muStar d k))
        (places.rankOf (List.range k) (muStar d k)))
      (List.set
        (List.replicate
          (places.monomialsAt (muStar d k)).length
          ground.BPair.unit)
        (places.rankOf σ0 (muStar d k)) (ground.BPair.ofNat 1))
      (places.rankOf σ0 (muStar d k))
      (by
        rw [elim.rowsLen_getAt (permMat σ' (muStar d k)) _
            (rowsLen_permMat σ' (muStar d k))
            (by rw [length_permMat]; exact hr0.1),
          ground.length_set, ground.length_replicate])
      (by rw [ground.length_set, ground.length_replicate]; exact hc0.1)
      (fun q hq hqc => by
        rw [ground.length_set, ground.length_replicate] at hq
        rw [ground.getAt_set_ne ground.BPair.unit
            (List.replicate
              (places.monomialsAt (muStar d k)).length
              ground.BPair.unit)
            (places.rankOf σ0 (muStar d k)) q (ground.BPair.ofNat 1) hqc,
          ground.getAt_replicate_self ground.BPair.unit _ q]
        exact BPair.oneValue_refl _)) ?_
  rw [ground.getAt_set_self ground.BPair.unit (ground.BPair.ofNat 1)
      (List.replicate
        (places.monomialsAt (muStar d k)).length
        ground.BPair.unit)
      (places.rankOf σ0 (muStar d k))
      (by rw [ground.length_replicate]; exact hc0.1)]
  refine BPair.oneValue_trans (BPair.mul_ofNat_one _) ?_
  rw [permMat_entry σ' (muStar d k)
      (places.rankOf (List.range k) (muStar d k))
      (places.rankOf σ0 (muStar d k)) hr0.1 hc0.1,
    hr0.2, hc0.2, expo_range_id k h']
  exact BPair.oneValue_refl _

/-- The permutation families are independent at the form
coordinates: at `k ≤ d` the `k!` flat forms read distinct monomials
on the distinct-letter content, `lem:mixedinv`'s independence
clause. -/
theorem perm_indep (d k : Nat) (hk : k ≤ d) :
    elim.indepRows (mixWidth d k) (permFlats d k) := by
  have hLn : elim.rowsLen (mixWidth d k) (permFlats d k) := by
    show elim.rowsLen _
      ((places.perms k).map (fun σ => flatF d k (permMat σ)))
    exact elim.rowsLen_map _ _ _
      (fun σ _ => length_flatF_permMat d k σ)
  have hLlen : (permFlats d k).length = (places.perms k).length := by
    show ((places.perms k).map _).length = _
    rw [ground.length_map]
  refine elim.indep_intro _ _ hLn ?_
  intro cs hcs hnull
  refine elim.unitTail_of_getAt cs ?_
  intro s hs
  have hsL : s < (places.perms k).length := by
    rw [← hLlen, ← hcs]
    exact hs
  have hsF : s < (permFlats d k).length := by
    rw [hLlen]
    exact hsL
  have hσs : 0 < ground.countOf
      (ground.getAt [] (places.perms k) s) (places.perms k) :=
    ground.countOf_getAt_pos [] (places.perms k) s hsL
  have hrow : ∀ q, q < (places.perms k).length →
      ground.getAt ([] : List ground.BPair) (permFlats d k) q
        = flatF d k (permMat
            (ground.getAt ([] : List Nat) (places.perms k) q)) := by
    intro q hq
    show ground.getAt ([] : List ground.BPair)
        ((places.perms k).map (fun σ => flatF d k (permMat σ))) q = _
    rw [ground.getAt_map ([] : List Nat) ([] : List ground.BPair) _
        (places.perms k) q hq]
  have hVread : ∀ q, q < (places.perms k).length →
      (ground.getAt ground.BPair.unit
          ((permFlats d k).map (fun row =>
            elim.dotP (flatF d k (probeB d k
              (ground.getAt [] (places.perms k) s))) row)) q).oneValue
        (if ground.getAt [] (places.perms k) s
            = ground.getAt [] (places.perms k) q
          then ground.BPair.ofNat 1 else ground.BPair.unit) := by
    intro q hq
    have hqF : q < (permFlats d k).length := by
      rw [hLlen]
      exact hq
    rw [ground.getAt_map ([] : List ground.BPair) ground.BPair.unit _
        (permFlats d k) q hqF, hrow q hq,
      elim.dotP_comm]
    exact dotP_probe_flat d k hk hσs
      (ground.countOf_getAt_pos [] (places.perms k) q hq)
  have h1 : (elim.dotP
      (flatF d k (probeB d k (ground.getAt [] (places.perms k) s)))
      (elim.combo (mixWidth d k) cs (permFlats d k))).oneValue
      ground.BPair.unit :=
    elim.dotP_null_tail_right _ _ hnull
  have h2 := elim.dotP_combo cs (permFlats d k)
    (flatF d k (probeB d k (ground.getAt [] (places.perms k) s)))
    (mixWidth d k) hLn
  have h3 : (elim.dotP cs
      ((permFlats d k).map (fun row =>
        elim.dotP (flatF d k (probeB d k
          (ground.getAt [] (places.perms k) s))) row))).oneValue
      ground.BPair.unit :=
    BPair.oneValue_trans (BPair.oneValue_symm h2) h1
  have h4 := elim.dotP_oneIndex cs
    ((permFlats d k).map (fun row =>
      elim.dotP (flatF d k (probeB d k
        (ground.getAt [] (places.perms k) s))) row)) s
    (by rw [ground.length_map, ← hcs])
    (by rw [ground.length_map]; exact hsF)
    (fun q hq hqs => by
      rw [ground.length_map, hLlen] at hq
      refine BPair.oneValue_trans (hVread q hq) ?_
      rw [if_neg (fun he => hqs (ground.getAt_inj_distinct
        ([] : List Nat) (places.perms k)
        (places.monomialsAt_distinct (List.replicate k 1))
        q s hq hsL he.symm))]
      exact BPair.oneValue_refl _)
  have h5 : (ground.getAt ground.BPair.unit
      ((permFlats d k).map (fun row =>
        elim.dotP (flatF d k (probeB d k
          (ground.getAt [] (places.perms k) s))) row)) s).oneValue
      (ground.BPair.ofNat 1) := by
    refine BPair.oneValue_trans (hVread s hsL) ?_
    rw [if_pos rfl]
    exact BPair.oneValue_refl _
  exact BPair.oneValue_trans
    (BPair.oneValue_symm (BPair.oneValue_trans h4
      (BPair.oneValue_trans
        (BPair.mul_congr (BPair.oneValue_refl _) h5)
        (BPair.mul_ofNat_one _)))) h3

/-! `lem:mixedinv`'s Gram tier: two permutation families' forms
pair at the agreement count — the double fold over the content
enumeration collapsing each row pair at the one shared column —
the agreement per word is the fixed-word condition at the composed
permutation, and the fixed words are counted one free letter per
cycle of `places.cyclesOf` — `d^{#cycles}`, the Gram's entry. -/

/-- The pairing of two flattened block families is the per-block
counts' fold: each block pair reads its own count and the seams
add. -/
private theorem dotP_flat_fam {α : Type} [DecidableEq α]
    (f g : α → List ground.BPair) (F : α → Nat) :
    ∀ A : List α,
      (∀ a, 0 < ground.countOf a A → (f a).length = (g a).length) →
      (∀ a, 0 < ground.countOf a A →
        (elim.dotP (f a) (g a)).oneValue (ground.BPair.ofNat (F a))) →
      (elim.dotP (A.flatMap f) (A.flatMap g)).oneValue
        (ground.BPair.ofNat (ground.famFold Nat.add 0 F A))
  | [], _, _ => BPair.oneValue_refl _
  | a :: A, hlen, hdot => by
    have hha : 0 < ground.countOf a (a :: A) := by
      rw [ground.countOf_head]
      exact Nat.succ_pos _
    show (elim.dotP (f a ++ A.flatMap f) (g a ++ A.flatMap g)).oneValue
      (ground.BPair.ofNat (F a + ground.famFold Nat.add 0 F A))
    refine BPair.oneValue_trans
      (elim.dotP_append (f a) (g a) _ _ (hlen a hha)) ?_
    refine BPair.oneValue_trans
      (BPair.add_congr (hdot a hha)
        (dotP_flat_fam f g F A
          (fun b hb => hlen b (ground.countOf_cons_pos hb))
          (fun b hb => hdot b (ground.countOf_cons_pos hb)))) ?_
    exact BPair.oneValue_symm
      (BPair.ofNat_add (F a) (ground.famFold Nat.add 0 F A))

/-- Two permutation rows at one monomial pair at the display
agreement: both rows are unit scatters at enumerated columns, so
the dot collapses at the first row's one live column — occupied on
the second exactly when the two permuted displays agree. -/
private theorem dotP_row_agree (k : Nat) {σ τ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    {mu : List Nat} (hsum : ground.sumNat mu = k)
    {m : List Nat}
    (hm : 0 < ground.countOf m (places.monomialsAt mu)) :
    (elim.dotP
        ((places.monomialsAt mu).map (fun m' =>
          if m' = places.expo m σ then ground.BPair.ofNat 1
          else ground.BPair.unit))
        ((places.monomialsAt mu).map (fun m' =>
          if m' = places.expo m τ then ground.BPair.ofNat 1
          else ground.BPair.unit))).oneValue
      (ground.BPair.ofNat
        (if places.expo m σ = places.expo m τ then 1 else 0)) := by
  refine BPair.oneValue_trans
    (elim.dotP_ofNat_fold
      (fun m' => if m' = places.expo m σ then 1 else 0)
      (fun m' => if m' = places.expo m τ then 1 else 0)
      (places.monomialsAt mu) _ _
      (ground.length_map _ _) (ground.length_map _ _)
      (fun t ht => by
        rw [ground.getAt_map ([] : List Nat) ground.BPair.unit _
            (places.monomialsAt mu) t ht]
        by_cases hc : ground.getAt [] (places.monomialsAt mu) t
            = places.expo m σ
        · rw [if_pos hc, if_pos hc]
          exact BPair.oneValue_refl _
        · rw [if_neg hc, if_neg hc]
          exact BPair.oneValue_refl _)
      (fun t ht => by
        rw [ground.getAt_map ([] : List Nat) ground.BPair.unit _
            (places.monomialsAt mu) t ht]
        by_cases hc : ground.getAt [] (places.monomialsAt mu) t
            = places.expo m τ
        · rw [if_pos hc, if_pos hc]
          exact BPair.oneValue_refl _
        · rw [if_neg hc, if_neg hc]
          exact BPair.oneValue_refl _)) ?_
  refine BPair.oneValue_of_eq (congrArg ground.BPair.ofNat ?_)
  refine Eq.trans
    (ground.famFold_congr_all Nat.add 0 _
      (fun m' => if m' = places.expo m σ then
        (if m' = places.expo m τ then 1 else 0) else 0)
      (fun m' => by
        by_cases h1 : m' = places.expo m σ
        · rw [if_pos h1, if_pos h1, Nat.one_mul]
        · rw [if_neg h1, if_neg h1, Nat.zero_mul])
      (places.monomialsAt mu)) ?_
  exact ground.famFold_pick _ _ (places.monomialsAt mu)
    (countOf_expo_monomialsAt k hσ hsum hm)

/-- The Gram's double fold: two permutation families' forms pair
at the per-content agreement counts' fold over the content
enumeration, each block's rows collapsing pairwise at the display
agreement. -/
private theorem dotP_gram_fold (d k : Nat) {σ : List Nat} (τ : List Nat)
    (hσ : 0 < ground.countOf σ (places.perms k)) :
    (elim.dotP (flatF d k (permMat σ)) (flatF d k (permMat τ))).oneValue
      (ground.BPair.ofNat (ground.famFold Nat.add 0
        (fun mu => ground.famFold Nat.add 0
          (fun m => if places.expo m σ = places.expo m τ then 1 else 0)
          (places.monomialsAt mu))
        (places.allContents d k))) := by
  refine dotP_flat_fam
    (fun mu => (permMat σ mu).flatMap (fun r => r))
    (fun mu => (permMat τ mu).flatMap (fun r => r))
    _ (places.allContents d k) ?_ ?_
  · intro mu _
    rw [length_flat_rows (permMat σ mu)
        (places.monomialsAt mu).length (rowsLen_permMat σ mu),
      length_flat_rows (permMat τ mu)
        (places.monomialsAt mu).length (rowsLen_permMat τ mu),
      length_permMat, length_permMat]
  · intro mu hmu
    have hsum : ground.sumNat mu = k := (places.allContents_reads d k mu hmu).2
    show (elim.dotP
        (((places.monomialsAt mu).map (fun m =>
          (places.monomialsAt mu).map (fun m' =>
            if m' = places.expo m σ then ground.BPair.ofNat 1
            else ground.BPair.unit))).flatMap (fun r => r))
        (((places.monomialsAt mu).map (fun m =>
          (places.monomialsAt mu).map (fun m' =>
            if m' = places.expo m τ then ground.BPair.ofNat 1
            else ground.BPair.unit))).flatMap (fun r => r))).oneValue _
    rw [ground.flatMap_map _ (fun r => r) (places.monomialsAt mu),
      ground.flatMap_map _ (fun r => r) (places.monomialsAt mu)]
    refine dotP_flat_fam _ _
      (fun m => if places.expo m σ = places.expo m τ then 1 else 0)
      (places.monomialsAt mu)
      (fun m _ => by rw [ground.length_map, ground.length_map]) ?_
    intro m hmm
    exact dotP_row_agree k hσ hsum hmm

/-! The fixed-word tier: the display agreement of two permutations
is the fixed-word condition at their composed assignment — the
inverse display's places reindex the agreement — and the
composition is itself an enumeration member. -/

/-- The display agreement is the fixed-word condition: two
permuted displays of a sized word agree exactly when the word is
fixed by the composed assignment — the inverse display's places
carrying the agreement across the reindex. -/
private theorem agree_iff_fixed (k : Nat) {σ τ : List Nat}
    (hσ : 0 < ground.countOf σ (places.perms k))
    (hτ : 0 < ground.countOf τ (places.perms k))
    (m : List Nat) (hm : m.length = k) :
    places.expo m σ = places.expo m τ
      ↔ m = places.expo m (places.expo σ (places.invPerm k τ)) := by
  obtain ⟨hσlen, hσdist, hσval, hσocc⟩ := places.perm_member_reads hσ
  obtain ⟨hτlen, hτdist, hτval, hτocc⟩ := places.perm_member_reads hτ
  constructor
  · intro he
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [expo_length, expo_length, places.length_invPerm, hm]
    · intro i hi
      rw [hm] at hi
      have hq : places.posOf i τ < k := by
        rw [← hτlen]
        exact places.posOf_lt i τ (hτocc i hi)
      have hgi := congrArg
        (fun z => ground.getAt 0 z (places.posOf i τ)) he
      rw [places.getAt_expo m σ (places.posOf i τ)
            (by rw [hσlen]; exact hq),
          places.getAt_expo m τ (places.posOf i τ)
            (by rw [hτlen]; exact hq),
          places.getAt_posOf i τ (hτocc i hi)] at hgi
      rw [places.getAt_expo m (places.expo σ (places.invPerm k τ)) i
            (by rw [expo_length, places.length_invPerm]; exact hi),
        places.getAt_expo σ (places.invPerm k τ) i
          (by rw [places.length_invPerm]; exact hi),
        places.getAt_invPerm k τ hi, ← hgi]
  · intro hf
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [expo_length, expo_length, hσlen, hτlen]
    · intro q hq
      rw [expo_length, hσlen] at hq
      have hτq : ground.getAt 0 τ q < k :=
        hτval _ (ground.countOf_getAt_pos 0 τ q (by rw [hτlen]; exact hq))
      have hgi := congrArg
        (fun z => ground.getAt 0 z (ground.getAt 0 τ q)) hf
      rw [places.getAt_expo m (places.expo σ (places.invPerm k τ))
            (ground.getAt 0 τ q)
            (by rw [expo_length, places.length_invPerm]; exact hτq),
        places.getAt_expo σ (places.invPerm k τ)
          (ground.getAt 0 τ q)
          (by rw [places.length_invPerm]; exact hτq),
        places.getAt_invPerm k τ hτq,
        places.posOf_getAt hτdist q (by rw [hτlen]; exact hq)] at hgi
      rw [places.getAt_expo m σ q (by rw [hσlen]; exact hq),
        places.getAt_expo m τ q (by rw [hτlen]; exact hq), ← hgi]

/-! The word enumeration: the flattened content pool lists each
sized word of bounded letters exactly once — the word's own content
names its one block and the block holds it once. -/

/-- A word within the alphabet carries its whole length in its
content: the letter counts over the range collect every entry. -/
private theorem sumNat_content_of_lt (d : Nat) (w : List Nat)
    (hlt : ∀ x, 0 < ground.countOf x w → x < d) :
    ground.sumNat (places.content d w) = w.length := by
  show ground.sumNat
    ((List.range d).map (fun i => ground.countOf i w)) = w.length
  show ground.famFold Nat.add 0 (fun x => x)
    ((List.range d).map (fun i => ground.countOf i w)) = w.length
  rw [ground.famFold_map Nat.add 0 (fun x => x)
      (fun i => ground.countOf i w) (List.range d)]
  exact ground.countOf_partition w (List.range d)
    (ground.distinctList_range d)
    (fun x hx => ground.memRange
      (hlt x (ground.countOf_pos_of_mem hx)))

/-- The pool's count at a word: the content enumeration's own count
at the word's content when the word carries the stated degree,
vacant otherwise. -/
private theorem countOf_pool (d k : Nat) (w : List Nat) :
    ground.countOf w ((places.allContents d k).flatMap places.monomialsAt)
      = if w.length = k
        then ground.countOf (places.content d w) (places.allContents d k)
        else 0 := by
  rw [ground.countOf_flatMap w places.monomialsAt
    (places.allContents d k)]
  by_cases hw : w.length = k
  · rw [if_pos hw]
    have hpoint : ∀ mu, 0 < ground.countOf mu (places.allContents d k) →
        ground.countOf w (places.monomialsAt mu)
          = if mu = places.content d w then 1 else 0 := by
      intro mu hmu
      obtain ⟨hmul, hmus⟩ := places.allContents_reads d k mu hmu
      rw [places.countOf_monomialsAt]
      by_cases hc : mu = places.content d w
      · rw [if_pos hc,
          if_pos ⟨by rw [hmus, hw], by rw [hmul, ← hc]⟩]
      · refine (if_neg ?_).trans (if_neg hc).symm
        intro hcond
        refine hc ?_
        rw [← hcond.2, hmul]
    rw [ground.famFold_congr_members Nat.add 0 _
      (fun mu => if mu = places.content d w then 1 else 0)
      (places.allContents d k) hpoint]
    match Nat.eq_zero_or_pos
        (ground.countOf (places.content d w) (places.allContents d k)) with
    | .inl hz =>
      rw [hz]
      exact ground.famFold_pickZero (fun _ => 1)
        (places.content d w) (places.allContents d k) hz
    | .inr hp =>
      have h1 : ground.countOf (places.content d w)
          (places.allContents d k) = 1 :=
        Nat.le_antisymm
          (countOf_allContents_le d k (places.content d w)) hp
      rw [h1]
      exact ground.famFold_pick (fun _ => 1)
        (places.content d w) (places.allContents d k) h1
  · rw [if_neg hw]
    have hpoint : ∀ mu, 0 < ground.countOf mu (places.allContents d k) →
        ground.countOf w (places.monomialsAt mu) = 0 := by
      intro mu hmu
      obtain ⟨_, hmus⟩ := places.allContents_reads d k mu hmu
      rw [places.countOf_monomialsAt]
      refine if_neg ?_
      intro hcond
      refine hw ?_
      rw [hcond.1, hmus]
    rw [ground.famFold_congr_members Nat.add 0 _ (fun _ => (0 : Nat))
      (places.allContents d k) hpoint]
    exact ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
      (places.allContents d k)

/-- The pool holds every word at most once. -/
private theorem countOf_pool_le (d k : Nat) (w : List Nat) :
    ground.countOf w
      ((places.allContents d k).flatMap places.monomialsAt) ≤ 1 := by
  rw [countOf_pool d k w]
  by_cases hw : w.length = k
  · rw [if_pos hw]
    exact countOf_allContents_le d k (places.content d w)
  · rw [if_neg hw]
    exact Nat.le_succ 0

/-- The pool holds each sized word of bounded letters exactly
once. -/
private theorem countOf_pool_one (d k : Nat) (w : List Nat)
    (hlen : w.length = k)
    (hlt : ∀ x, 0 < ground.countOf x w → x < d) :
    ground.countOf w
      ((places.allContents d k).flatMap places.monomialsAt) = 1 := by
  rw [countOf_pool d k w, if_pos hlen]
  have hmem := places.mem_allContents d (places.content d w)
    (places.content_length d w)
  have hfold : (places.content d w).foldl (fun a b => a + b) 0 = k := by
    rw [foldl_sumNat (places.content d w) 0, Nat.zero_add,
      sumNat_content_of_lt d w hlt, hlen]
  rw [hfold] at hmem
  exact Nat.le_antisymm
    (countOf_allContents_le d k (places.content d w))
    (ground.countOf_pos_of_mem hmem)

/-- A pool member is a sized word within the alphabet. -/
private theorem pool_reads (d k : Nat) (m : List Nat)
    (h : 0 < ground.countOf m
      ((places.allContents d k).flatMap places.monomialsAt)) :
    m.length = k ∧ (∀ x, 0 < ground.countOf x m → x < d) := by
  match ground.mem_flatMap_of places.monomialsAt
      (places.allContents d k) m (ground.mem_of_countOf_pos m _ h) with
  | ⟨mu, hmu, hmm⟩ =>
    obtain ⟨hmul, hmus⟩ := places.allContents_reads d k mu
      (ground.countOf_pos_of_mem hmu)
    obtain ⟨hml, hmc⟩ := places.member_conditions
      (ground.countOf_pos_of_mem hmm)
    have hcd : places.content d m = mu := by
      rw [← hmul]
      exact hmc
    refine ⟨by rw [hml, hmus], ?_⟩
    refine places.mem_lt_of_content d m ?_
    rw [hcd, hmus, hml, hmus]

/-! The free-letter writer: one letter per cycle scattered over the
cycle's places builds a fixed word, and the fixed words are exactly
the writer's images over the choice enumeration — the choices read
back at the cycle heads. -/

/-- The cycle writer: one letter set at every stated place. -/
private def setAll : List Nat → Nat → List Nat → List Nat
  | [], _, w => w
  | p :: c, a, w => setAll c a (List.set w p a)

/-- The cycle writer keeps the width. -/
private theorem length_setAll :
    ∀ (c : List Nat) (a : Nat) (w : List Nat),
      (setAll c a w).length = w.length
  | [], _, _ => rfl
  | p :: c, a, w => by
    show (setAll c a (List.set w p a)).length = w.length
    rw [length_setAll c a (List.set w p a), ground.length_set]

/-- Off the cycle the writer keeps the entries. -/
private theorem getAt_setAll_off :
    ∀ (c : List Nat) (a : Nat) (w : List Nat) (p : Nat),
      ground.countOf p c = 0 →
      ground.getAt 0 (setAll c a w) p = ground.getAt 0 w p
  | [], _, _, _, _ => rfl
  | q :: c, a, w, p, hp => by
    have hp' : (if p = q then 1 else 0) + ground.countOf p c = 0 :=
      (ground.countOf_cons p q c).symm.trans hp
    have hif : (if p = q then 1 else 0) = 0 :=
      Nat.eq_zero_of_add_eq_zero_right hp'
    have hpq : ¬ p = q := by
      intro he
      rw [if_pos he] at hif
      exact Nat.noConfusion hif
    have hpc : ground.countOf p c = 0 :=
      Nat.eq_zero_of_add_eq_zero_left hp'
    show ground.getAt 0 (setAll c a (List.set w q a)) p = _
    rw [getAt_setAll_off c a (List.set w q a) p hpc,
      ground.getAt_set_ne 0 w q p a hpq]

/-- On the cycle the writer reads its letter. -/
private theorem getAt_setAll_mem :
    ∀ (c : List Nat) (a : Nat) (w : List Nat) (p : Nat),
      0 < ground.countOf p c → p < w.length →
      ground.getAt 0 (setAll c a w) p = a
  | [], _, _, _, hp, _ => absurd hp (Nat.lt_irrefl 0)
  | q :: c, a, w, p, hp, hw => by
    show ground.getAt 0 (setAll c a (List.set w q a)) p = a
    match Nat.eq_zero_or_pos (ground.countOf p c) with
    | .inr hpc =>
      exact getAt_setAll_mem c a (List.set w q a) p hpc
        (by rw [ground.length_set]; exact hw)
    | .inl hz =>
      have hpq : p = q := by
        by_cases hpq : p = q
        · exact hpq
        · have h0 : ground.countOf p (q :: c) = 0 := by
            rw [ground.countOf_cons, if_neg hpq, hz]
          rw [h0] at hp
          exact absurd hp (Nat.lt_irrefl 0)
      rw [getAt_setAll_off c a (List.set w q a) p hz, hpq,
        ground.getAt_set_self 0 a w q (by rw [← hpq]; exact hw)]

/-- The free-letter writer: each cycle's places set at its own
choice over the seed. -/
private def fillCyc : List (List Nat) → List Nat → List Nat → List Nat
  | [], _, w => w
  | _ :: _, [], w => w
  | c :: cs, a :: u, w => fillCyc cs u (setAll c a w)

/-- The writer keeps the width. -/
private theorem length_fillCyc :
    ∀ (cs : List (List Nat)) (u : List Nat) (w : List Nat),
      (fillCyc cs u w).length = w.length
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | c :: cs, a :: u, w => by
    show (fillCyc cs u (setAll c a w)).length = w.length
    rw [length_fillCyc cs u (setAll c a w), length_setAll]

/-- Off every cycle the writer keeps the entries. -/
private theorem fillCyc_off :
    ∀ (cs : List (List Nat)) (u : List Nat) (w : List Nat) (p : Nat),
      ground.countOf p (cs.flatMap (fun c => c)) = 0 →
      ground.getAt 0 (fillCyc cs u w) p = ground.getAt 0 w p
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | c :: cs, a :: u, w, p, hp => by
    have hp' : ground.countOf p (c ++ cs.flatMap (fun c => c)) = 0 := hp
    rw [ground.countOf_append] at hp'
    show ground.getAt 0 (fillCyc cs u (setAll c a w)) p = _
    rw [fillCyc_off cs u (setAll c a w) p
        (Nat.eq_zero_of_add_eq_zero_left hp'),
      getAt_setAll_off c a w p (Nat.eq_zero_of_add_eq_zero_right hp')]

/-- A cycle's member joins the flattening. -/
private theorem flat_of_cycle :
    ∀ (cs : List (List Nat)) (t : Nat) (p : Nat), t < cs.length →
      0 < ground.countOf p (ground.getAt [] cs t) →
      0 < ground.countOf p (cs.flatMap (fun c => c))
  | [], t, _, ht, _ => absurd ht (Nat.not_lt_zero t)
  | _ :: _, 0, p, _, hp => ground.countOf_append_left p _ hp
  | _ :: cs, t + 1, p, ht, hp =>
    ground.countOf_append_right p _
      (flat_of_cycle cs t p (Nat.lt_of_succ_lt_succ ht) hp)

/-- A member of the flattening names its cycle's key. -/
private theorem flat_index :
    ∀ (cs : List (List Nat)) (p : Nat),
      0 < ground.countOf p (cs.flatMap (fun c => c)) →
      ∃ t, t < cs.length
        ∧ 0 < ground.countOf p (ground.getAt [] cs t)
  | [], _, hp => absurd hp (Nat.lt_irrefl 0)
  | c :: cs, p, hp => by
    match ground.countOf_append_split p c (cs.flatMap (fun c => c)) hp with
    | .inl h => exact ⟨0, Nat.succ_pos _, h⟩
    | .inr h =>
      match flat_index cs p h with
      | ⟨t, ht, hc⟩ => exact ⟨t + 1, Nat.succ_lt_succ ht, hc⟩

/-- At a disjoint cycle family of matched width, the writer reads
each cycle's own choice at each of its places. -/
private theorem fillCyc_read :
    ∀ (cs : List (List Nat)) (u : List Nat) (w : List Nat),
      cs.length = u.length →
      (∀ q, ground.countOf q (cs.flatMap (fun c => c)) ≤ 1) →
      ∀ t, t < cs.length →
      ∀ p, 0 < ground.countOf p (ground.getAt [] cs t) →
        p < w.length →
        ground.getAt 0 (fillCyc cs u w) p = ground.getAt 0 u t
  | [], _, _, _, _, t, ht, _, _, _ => absurd ht (Nat.not_lt_zero t)
  | _ :: _, [], _, hlen, _, _, _, _, _, _ => Nat.noConfusion hlen
  | c :: cs, a :: u, w, hlen, hdist, 0, _, p, hp, hw => by
    have hflat : ground.countOf p (cs.flatMap (fun c => c)) = 0 := by
      have h1 : 1 + ground.countOf p (cs.flatMap (fun c => c))
          ≤ ground.countOf p c
            + ground.countOf p (cs.flatMap (fun c => c)) :=
        Nat.add_le_add_right hp _
      have h2 : ground.countOf p c
          + ground.countOf p (cs.flatMap (fun c => c)) ≤ 1 := by
        rw [← ground.countOf_append]
        exact hdist p
      have h3 : ground.countOf p (cs.flatMap (fun c => c)) + 1
          ≤ 0 + 1 := by
        rw [Nat.zero_add, Nat.add_comm]
        exact Nat.le_trans h1 h2
      exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ h3)
    show ground.getAt 0 (fillCyc cs u (setAll c a w)) p = a
    rw [fillCyc_off cs u (setAll c a w) p hflat,
      getAt_setAll_mem c a w p hp hw]
  | c :: cs, a :: u, w, hlen, hdist, t + 1, ht, p, hp, hw => by
    have hflat : 0 < ground.countOf p (cs.flatMap (fun c => c)) :=
      flat_of_cycle cs t p (Nat.lt_of_succ_lt_succ ht) hp
    have hpc : ground.countOf p c = 0 := by
      have h1 : ground.countOf p c + 1
          ≤ ground.countOf p c
            + ground.countOf p (cs.flatMap (fun c => c)) :=
        Nat.add_le_add_left hflat _
      have h2 : ground.countOf p c
          + ground.countOf p (cs.flatMap (fun c => c)) ≤ 1 := by
        rw [← ground.countOf_append]
        exact hdist p
      have h3 : ground.countOf p c + 1 ≤ 0 + 1 := by
        rw [Nat.zero_add]
        exact Nat.le_trans h1 h2
      exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ h3)
    show ground.getAt 0 (fillCyc cs u (setAll c a w)) p
      = ground.getAt 0 u t
    refine fillCyc_read cs u (setAll c a w) (Nat.succ.inj hlen)
      (fun q => Nat.le_trans (Nat.le_add_left _ _)
        (by rw [← ground.countOf_append]; exact hdist q))
      t (Nat.lt_of_succ_lt_succ ht) p hp ?_
    rw [length_setAll]
    exact hw

/-! The choice enumeration: `places.allMon` holds each bounded
sized word exactly once and counts at the letter power. -/

/-- The choice enumeration holds each bounded sized word once. -/
private theorem countOf_allMon_one (d : Nat) :
    ∀ (n : Nat) (u : List Nat), u.length = n →
      (∀ x, 0 < ground.countOf x u → x < d) →
      ground.countOf u (places.allMon d n) = 1
  | 0, [], _, _ => rfl
  | 0, _ :: _, hlen, _ => Nat.noConfusion hlen
  | _ + 1, [], hlen, _ => Nat.noConfusion hlen
  | n + 1, a :: u, hlen, hlt => by
    show ground.countOf (a :: u) ((List.range d).flatMap (fun i =>
      (places.allMon d n).map (fun m => i :: m))) = 1
    rw [ground.countOf_flatMap]
    rw [ground.famFold_congr_all Nat.add 0 _
      (fun i => if i = a then
        ground.countOf u (places.allMon d n) else 0)
      (fun i => by
        rw [ground.countOf_consMap a i (places.allMon d n) u]
        by_cases hai : a = i
        · rw [if_pos hai, if_pos hai.symm]
        · rw [if_neg hai, if_neg (fun he => hai he.symm)])
      (List.range d)]
    have had : a < d := hlt a (by
      rw [ground.countOf_head]
      exact Nat.succ_pos _)
    rw [ground.famFold_pick
      (fun _ => ground.countOf u (places.allMon d n)) a
      (List.range d) (ground.countOf_range_one had)]
    exact countOf_allMon_one d n u (Nat.succ.inj hlen)
      (fun x hx => hlt x (ground.countOf_cons_pos hx))

/-- A choice member is a bounded sized word. -/
private theorem allMon_reads (d : Nat) :
    ∀ (n : Nat) (u : List Nat),
      0 < ground.countOf u (places.allMon d n) →
      u.length = n ∧ (∀ x, 0 < ground.countOf x u → x < d)
  | 0, u, h => by
    have hu : u = [] := by
      by_cases hu : u = []
      · exact hu
      · have hz : ground.countOf u (places.allMon d 0) = 0 :=
          ground.countOf_head_ne hu []
        rw [hz] at h
        exact absurd h (Nat.lt_irrefl 0)
    rw [hu]
    exact ⟨rfl, fun _ hx => absurd hx (Nat.lt_irrefl 0)⟩
  | n + 1, u, h => by
    match ground.mem_flatMap_of _ (List.range d) u
        (ground.mem_of_countOf_pos u _ h) with
    | ⟨i, him, hum⟩ =>
      match ground.mem_map_of _ (places.allMon d n) u hum with
      | ⟨m, hmm, hcons⟩ =>
        have hid : i < d :=
          ground.ltOfMemRange him
        have hIH := allMon_reads d n m (ground.countOf_pos_of_mem hmm)
        refine ⟨?_, ?_⟩
        · rw [← hcons]
          show m.length + 1 = n + 1
          rw [hIH.1]
        · intro x hx
          rw [← hcons] at hx
          by_cases hxi : x = i
          · rw [hxi]
            exact hid
          · rw [ground.countOf_head_ne hxi] at hx
            exact hIH.2 x hx

/-- The choice enumeration counts at the letter power. -/
private theorem length_allMon (d : Nat) :
    ∀ n : Nat, (places.allMon d n).length = d ^ n
  | 0 => rfl
  | n + 1 => by
    show ((List.range d).flatMap (fun i =>
      (places.allMon d n).map (fun m => i :: m))).length = d ^ (n + 1)
    rw [ground.length_flatMap _ (List.range d),
      ground.famFold_congr_members Nat.add 0 _
        (fun _ => (places.allMon d n).length) (List.range d)
        (fun _ _ => ground.length_map _ _),
      ground.famFold_const _ (List.range d), ground.length_range,
      length_allMon d n]
    show d * d ^ n = d ^ n * d
    exact Nat.mul_comm d (d ^ n)

/-- A fixed word is constant along the iterates: each step reads
the fixed-point condition once. -/
private theorem fixed_iter (k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (places.perms k))
    (w : List Nat) (hfix : w = places.expo w π) :
    ∀ (t j : Nat), j < k →
      ground.getAt 0 w (iterP π t j) = ground.getAt 0 w j := by
  obtain ⟨hπlen, _, _, _⟩ := places.perm_member_reads hπ
  have hpt : ∀ q, q < k →
      ground.getAt 0 w (ground.getAt 0 π q) = ground.getAt 0 w q := by
    intro q hq
    have h := congrArg (fun z => ground.getAt 0 z q) hfix
    rw [places.getAt_expo w π q (by rw [hπlen]; exact hq)] at h
    exact h.symm
  intro t
  induction t with
  | zero => exact fun _ _ => rfl
  | succ t ih =>
    intro j hj
    show ground.getAt 0 w (ground.getAt 0 π (iterP π t j)) = _
    rw [hpt (iterP π t j) (iterP_lt k hπ t j hj)]
    exact ih j hj

/-- The fixed-word count is the cycle power: over the word pool a
word fixed by the assignment carries one free letter per cycle —
the writer a bijection with the choice enumeration, the choices
read back at the cycle heads — so the indicator's fold is
`d^{#cycles}`. -/
private theorem fixed_count (d k : Nat) {π : List Nat}
    (hπ : 0 < ground.countOf π (places.perms k)) :
    ground.famFold Nat.add 0
      (fun m => if m = places.expo m π then 1 else 0)
      ((places.allContents d k).flatMap places.monomialsAt)
      = d ^ (places.cyclesOf π).length := by
  obtain ⟨hπlen, _, _, _⟩ := places.perm_member_reads hπ
  obtain ⟨hcd, hccov, hcpack⟩ := cycles_pack k hπ
  have hfillfix : ∀ u, 0 < ground.countOf u
      (places.allMon d (places.cyclesOf π).length) →
      fillCyc (places.cyclesOf π) u (List.replicate k 0)
        = places.expo
            (fillCyc (places.cyclesOf π) u (List.replicate k 0)) π := by
    intro u hu
    obtain ⟨hul, _⟩ := allMon_reads d _ u hu
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [expo_length, hπlen, length_fillCyc, ground.length_replicate]
    · intro q hq
      rw [length_fillCyc, ground.length_replicate] at hq
      rw [places.getAt_expo _ π q (by rw [hπlen]; exact hq)]
      match flat_index _ q (hccov q hq) with
      | ⟨t, ht, hqc⟩ =>
        have hcmem := hcpack (ground.getAt [] (places.cyclesOf π) t)
          (ground.countOf_getAt_pos [] _ t ht)
        have hπq : 0 < ground.countOf (ground.getAt 0 π q)
            (ground.getAt [] (places.cyclesOf π) t) :=
          hcmem.2.2.1 q hqc
        rw [fillCyc_read _ u _ hul.symm hcd t ht q hqc
            (by rw [ground.length_replicate]; exact hq),
          fillCyc_read _ u _ hul.symm hcd t ht _ hπq
            (by rw [ground.length_replicate]; exact hcmem.2.1 _ hπq)]
  have hround : ∀ m, m.length = k → m = places.expo m π →
      fillCyc (places.cyclesOf π)
        ((places.cyclesOf π).map (fun c =>
          ground.getAt 0 m (ground.getAt 0 c 0)))
        (List.replicate k 0) = m := by
    intro m hml hmfix
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [length_fillCyc, ground.length_replicate, hml]
    · intro q hq
      rw [length_fillCyc, ground.length_replicate] at hq
      match flat_index _ q (hccov q hq) with
      | ⟨t, ht, hqc⟩ =>
        have hcmem := hcpack (ground.getAt [] (places.cyclesOf π) t)
          (ground.countOf_getAt_pos [] _ t ht)
        rw [fillCyc_read _ _ _ (by rw [ground.length_map]) hcd t ht
            q hqc (by rw [ground.length_replicate]; exact hq),
          ground.getAt_map ([] : List Nat) 0 _ (places.cyclesOf π) t ht]
        match hcmem.2.2.2 q hqc with
        | ⟨s, hqs⟩ =>
          have hhead_lt : ground.getAt 0
              (ground.getAt [] (places.cyclesOf π) t) 0 < k :=
            hcmem.2.1 _ (ground.countOf_getAt_pos 0 _ 0 hcmem.1)
          rw [hqs, fixed_iter k hπ m hmfix s _ hhead_lt]
  have huniq : ∀ (m u : List Nat), 0 < ground.countOf u
      (places.allMon d (places.cyclesOf π).length) →
      m = fillCyc (places.cyclesOf π) u (List.replicate k 0) →
      (places.cyclesOf π).map (fun c =>
        ground.getAt 0 m (ground.getAt 0 c 0)) = u := by
    intro m u hu hm
    obtain ⟨hul, _⟩ := allMon_reads d _ u hu
    refine ground.getAt_ext 0 _ _ ?_ ?_
    · rw [ground.length_map, hul]
    · intro t ht
      rw [ground.length_map] at ht
      have hcmem := hcpack (ground.getAt [] (places.cyclesOf π) t)
        (ground.countOf_getAt_pos [] _ t ht)
      have hhead_mem : 0 < ground.countOf
          (ground.getAt 0 (ground.getAt [] (places.cyclesOf π) t) 0)
          (ground.getAt [] (places.cyclesOf π) t) :=
        ground.countOf_getAt_pos 0 _ 0 hcmem.1
      rw [ground.getAt_map ([] : List Nat) 0 _ (places.cyclesOf π) t ht,
        hm, fillCyc_read _ u _ hul.symm hcd t ht _ hhead_mem
          (by rw [ground.length_replicate]
              exact hcmem.2.1 _ hhead_mem)]
  refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
    (fun m => ground.countOf m
      ((places.allMon d (places.cyclesOf π).length).map
        (fun u => fillCyc (places.cyclesOf π) u (List.replicate k 0))))
    ((places.allContents d k).flatMap places.monomialsAt) ?_) ?_
  · intro m hm
    obtain ⟨hml, hmlt⟩ := pool_reads d k m hm
    by_cases hfix : m = places.expo m π
    · rw [if_pos hfix]
      have hrb_letters : ∀ x, 0 < ground.countOf x
          ((places.cyclesOf π).map (fun c =>
            ground.getAt 0 m (ground.getAt 0 c 0))) → x < d := by
        intro x hx
        match ground.getAt_of_mem 0
            (ground.mem_of_countOf_pos _ _ hx) with
        | ⟨t, ht, hte⟩ =>
          rw [ground.length_map] at ht
          rw [ground.getAt_map ([] : List Nat) 0 _
            (places.cyclesOf π) t ht] at hte
          have hcmem := hcpack (ground.getAt [] (places.cyclesOf π) t)
            (ground.countOf_getAt_pos [] _ t ht)
          have hhead_lt : ground.getAt 0
              (ground.getAt [] (places.cyclesOf π) t) 0 < k :=
            hcmem.2.1 _ (ground.countOf_getAt_pos 0 _ 0 hcmem.1)
          rw [← hte]
          exact hmlt _ (ground.countOf_getAt_pos 0 m _
            (by rw [hml]; exact hhead_lt))
      have hiff : ∀ v, 0 < ground.countOf v
          (places.allMon d (places.cyclesOf π).length) →
          (m = fillCyc (places.cyclesOf π) v (List.replicate k 0)
            ↔ (places.cyclesOf π).map (fun c =>
                ground.getAt 0 m (ground.getAt 0 c 0)) = v) := by
        intro v hv
        constructor
        · exact huniq m v hv
        · intro hrb
          rw [← hrb]
          exact (hround m hml hfix).symm
      have h1 := ground.countOf_map_iff
        (fun u => fillCyc (places.cyclesOf π) u (List.replicate k 0))
        (places.allMon d (places.cyclesOf π).length) m
        ((places.cyclesOf π).map (fun c =>
          ground.getAt 0 m (ground.getAt 0 c 0))) hiff
      have h2 := countOf_allMon_one d (places.cyclesOf π).length
        ((places.cyclesOf π).map (fun c =>
          ground.getAt 0 m (ground.getAt 0 c 0)))
        (ground.length_map _ _) hrb_letters
      rw [h1, h2]
    · rw [if_neg hfix]
      refine (ground.countOf_map_none _ m
        (places.allMon d (places.cyclesOf π).length) ?_).symm
      intro u hu hfe
      refine hfix ?_
      have hf := hfillfix u hu
      rw [hfe] at hf
      exact hf
  refine Eq.trans (ground.countOf_partition
    ((places.allMon d (places.cyclesOf π).length).map
      (fun u => fillCyc (places.cyclesOf π) u (List.replicate k 0)))
    ((places.allContents d k).flatMap places.monomialsAt)
    (fun x _ => countOf_pool_le d k x) ?_) ?_
  · intro w hw
    match ground.mem_map_of _
        (places.allMon d (places.cyclesOf π).length) w hw with
    | ⟨u, hum, hue⟩ =>
      obtain ⟨hul, hult⟩ := allMon_reads d _ u
        (ground.countOf_pos_of_mem hum)
      have hwlen : w.length = k := by
        rw [← hue, length_fillCyc, ground.length_replicate]
      have hwlt : ∀ x, 0 < ground.countOf x w → x < d := by
        intro x hx
        rw [← hue] at hx
        match ground.getAt_of_mem 0
            (ground.mem_of_countOf_pos _ _ hx) with
        | ⟨p, hp, hpe⟩ =>
          rw [length_fillCyc, ground.length_replicate] at hp
          match flat_index _ p (hccov p hp) with
          | ⟨t, ht, hqc⟩ =>
            rw [fillCyc_read _ u _ hul.symm hcd t ht p hqc
                (by rw [ground.length_replicate]; exact hp)] at hpe
            rw [← hpe]
            exact hult _ (ground.countOf_getAt_pos 0 u t
              (by rw [hul]; exact ht))
      refine ground.mem_of_countOf_pos _ _ ?_
      rw [countOf_pool_one d k w hwlen hwlt]
      exact Nat.succ_pos 0
  · rw [ground.length_map]
    exact length_allMon d (places.cyclesOf π).length

/-- The permutation Gram is the cycle count: two permutation
families' forms pair at `d^{#cycles(σ τ^T)}`, one free letter per
cycle — `lem:mixedinv`'s Gram clause at the form coordinates. -/
theorem perm_gram (d k : Nat) (σ τ : List Nat)
    (hσ : 0 < ground.countOf σ (places.perms k))
    (hτ : 0 < ground.countOf τ (places.perms k)) :
    (elim.dotP (flatF d k (permMat σ)) (flatF d k (permMat τ))).oneValue
      (ground.BPair.ofNat
        (d ^ (places.cyclesOf
          (places.expo σ (places.invPerm k τ))).length)) := by
  have hπ := places.expo_member k hσ (places.invPerm_member k hτ)
  refine BPair.oneValue_trans (dotP_gram_fold d k τ hσ) ?_
  refine BPair.oneValue_of_eq (congrArg ground.BPair.ofNat ?_)
  refine Eq.trans (ground.famFold_flatMap _ places.monomialsAt
    (places.allContents d k)).symm (Eq.trans ?_ (fixed_count d k hπ))
  refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
  intro m hm
  obtain ⟨hml, _⟩ := pool_reads d k m hm
  by_cases hag : places.expo m σ = places.expo m τ
  · rw [if_pos hag, if_pos ((agree_iff_fixed k hσ hτ m hml).mp hag)]
  · rw [if_neg hag,
      if_neg (fun hf => hag ((agree_iff_fixed k hσ hτ m hml).mpr hf))]


/-! `lem:mixedinv`'s span theorem: every invariant of the mixed
power sits in the place permutations' span.  The family enters at
its frames and moved reads, the statement's own binders; the twins
below name the two shapes as plumbing, definitionally the inline
spelling.  The proof is the tex's exchange: the injectivity walk
(a family whose every top value is the sum's unit is null), the
values' top reads, the stacked images inside the raising kernels'
joined span, and the count at the shapes' square sum. -/

/-- The family's frames: one square matrix per occupied content,
at the content's monomials. -/
private def sqAt (d k : Nat) (T : List Nat → elim.Mat) : Prop :=
  ∀ mu, 0 < ground.countOf mu (places.allContents d k) →
    elim.rowsLen (places.monomialsAt mu).length (T mu)
      ∧ (T mu).length = (places.monomialsAt mu).length

/-- The family's moved reads: the unit action at the family's
value is the family's read of the acted vector, `lem:blockirr`'s
matrix families at every distinct letter pair. -/
private def movedAt (d k : Nat) (T : List Nat → elim.Mat) : Prop :=
  ∀ mu, 0 < ground.countOf mu (places.allContents d k) →
    ∀ (i j : Nat), i < d → j < d → ¬ i = j →
    ∀ x : List ground.BPair,
      x.length = (places.monomialsAt mu).length →
    poly.oneValue
      (elim.matVec
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
        (elim.matVec (T mu) x))
      (elim.matVec (T (blockcount.moveAt i j mu))
        (elim.matVec
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j) x))

/-- An occupied group names a pool member at its content. -/
private theorem group_mem (pool : List blockcount.HVec)
    (mu : List Nat)
    (h : ¬ blockcount.groupAt pool mu = []) :
    ∃ z ∈ pool, z.content = mu := by
  match hfl : pool.filter (fun w => w.content == mu) with
  | [] =>
    refine absurd ?_ h
    show (pool.filter (fun w => w.content == mu)).map
      blockcount.HVec.coords = []
    rw [hfl]
    rfl
  | z :: zt =>
    have hz : z ∈ pool.filter (fun w => w.content == mu) := by
      rw [hfl]
      exact List.Mem.head zt
    match ground.mem_filter_of _ pool z hz with
    | ⟨hzp, hzc⟩ => exact ⟨z, hzp, ground.listBeqEq hzc⟩

/-- An exhaust member's content reads: the stated width, the
power's degree, and the enumeration's occupancy. -/
private theorem exhaust_reads (d k : Nat) (hd : 0 < d) :
    ∀ t ∈ blockcount.exhaust d (monPool d k),
      t.content.length = d ∧ ground.sumNat t.content = k
        ∧ 0 < ground.countOf t.content (places.allContents d k) := by
  intro t ht
  have hpack := monPool_pack d hd k
  obtain ⟨hsz, hwid, hnu, hup⟩ :=
    blockcount.exhaust_top d (monPool d k) hpack.1 hpack.2.1
      hpack.2.2.2 t ht
  have htB : t ∈ blockcount.blockOf d t := by
    match blockcount.seedSpan_prov d (lowerspan.ht t.content) t with
    | ⟨tail, heq, _⟩ =>
      show t ∈ blockcount.blockOf d t
      rw [show blockcount.blockOf d t = t :: tail from heq]
      exact List.Mem.head tail
  have htJ : t ∈ blockcount.blockJoin d
      (blockcount.exhaust d (monPool d k)) :=
    ground.mem_flatMap_to (blockcount.blockOf d) ht htB
  obtain ⟨_, _, hst⟩ :=
    blockcount.exhaust_settle d (monPool d k) hpack.1 hpack.2.1
      hpack.2.2.2 t htJ
  have hsum : ground.sumNat t.content = k := by
    match hst with
    | Or.inl hu =>
      exact absurd (blockcount.unitTail_of_allU t.coords hu) hnu
    | Or.inr hsp =>
      match hgr : blockcount.groupAt (monPool d k) t.content with
      | [] =>
        rw [hgr] at hsp
        exact absurd (elim.spanRel_nil_unit _ _ hsp) hnu
      | y :: ys =>
        match group_mem (monPool d k) t.content
            (fun he => nomatch hgr.symm.trans he) with
        | ⟨z, hzp, hzc⟩ =>
          rw [← hzc]
          exact hpack.2.2.1 z hzp
  refine ⟨hwid, hsum, ground.countOf_pos_of_mem ?_⟩
  have hmem := places.mem_allContents d t.content hwid
  rw [foldl_sumNat t.content 0, Nat.zero_add, hsum] at hmem
  exact hmem

/-- A content of the stated width and degree is occupied in the
enumeration. -/
private theorem content_occ (d k : Nat) (mu : List Nat)
    (hw : mu.length = d) (hs : ground.sumNat mu = k) :
    0 < ground.countOf mu (places.allContents d k) := by
  refine ground.countOf_pos_of_mem ?_
  have hmem := places.mem_allContents d mu hw
  rw [foldl_sumNat mu 0, Nat.zero_add, hs] at hmem
  exact hmem

/-- The injectivity walk's block half: at null values on the
exhaust's tops, every member of the produced blocks' join reads a
null value — `lem:blockirr`(ii)'s induction at the block's
provenance, each lowering's value the moved read at the prior
null. -/
private theorem join_null (d k : Nat) (hd : 0 < d)
    (T : List Nat → elim.Mat) (hmv : movedAt d k T)
    (htops : ∀ t ∈ blockcount.exhaust d (monPool d k),
      poly.unitTail (elim.matVec (T t.content) t.coords)) :
    ∀ y ∈ blockcount.blockJoin d
        (blockcount.exhaust d (monPool d k)),
      poly.unitTail (elim.matVec (T y.content) y.coords) := by
  intro y hy
  match ground.mem_flatMap_of (blockcount.blockOf d) _ y hy with
  | ⟨t, ht, hyB⟩ =>
    have hpack := monPool_pack d hd k
    have hszt : blockcount.sized t :=
      (blockcount.exhaust_top d (monPool d k) hpack.1 hpack.2.1
        hpack.2.2.2 t ht).1
    obtain ⟨hwt, hst, _⟩ := exhaust_reads d k hd t ht
    match blockcount.seedSpan_prov d (lowerspan.ht t.content) t with
    | ⟨tail, heq, hprov⟩ =>
      have hyT : y ∈ t :: tail := by
        rw [show blockcount.blockOf d t = t :: tail from heq] at hyB
        exact hyB
      have hall := blockcount.prov_all d t tail
        (fun x => (x.content.length = d
            ∧ ground.sumNat x.content = k
            ∧ blockcount.sized x)
          ∧ poly.unitTail (elim.matVec (T x.content) x.coords))
        hprov
        ⟨⟨hwt, hst, hszt⟩, htops t ht⟩
        ?_ y hyT
      · exact hall.2
      · intro x w j hjd hq hlw
        obtain ⟨⟨hxw, hxs, hxz⟩, hxv⟩ := hq
        have hg : 0 < ground.getAt 0 x.content j := by
          by_cases hg : 0 < ground.getAt 0 x.content j
          · exact hg
          · rw [show blockcount.lowerH j x = none from if_neg hg]
              at hlw
            exact nomatch hlw
        have hwe := blockcount.lowerH_eq hlw
        have hj : j < d := Nat.lt_trans (Nat.lt_succ_self j) hjd
        have hij : ¬ j + 1 = j := Nat.succ_ne_self j
        have hocc : 0 < ground.countOf x.content
            (places.allContents d k) :=
          content_occ d k x.content hxw hxs
        have hxz' : x.coords.length
            = (places.monomialsAt x.content).length := hxz
        have hchain := hmv x.content hocc (j + 1) j hjd hj hij
          x.coords hxz'
        rw [blockcount.moveAt_moveDn j x.content] at hchain
        have hnullL : poly.unitTail
            (elim.matVec
              (units.matUnitAt (units.moveDn j x.content)
                x.content (j + 1) j)
              (elim.matVec (T x.content) x.coords)) :=
          elim.matVec_null _ _ hxv
        have hnullR := poly.unitTail_oneValue_right hnullL hchain
        rw [hwe]
        refine ⟨⟨?_, ?_, ?_⟩, hnullR⟩
        · show (units.moveDn j x.content).length = d
          rw [units.length_moveDn]
          exact hxw
        · show ground.sumNat (units.moveDn j x.content) = k
          rw [units.sumNat_moveDn j x.content
            (by rw [hxw]; exact hjd) hg]
          exact hxs
        · show (elim.matVec
              (units.matUnitAt (units.moveDn j x.content)
                x.content (j + 1) j) x.coords).length
            = (places.monomialsAt
                (units.moveDn j x.content)).length
          exact units.matVec_matUnitAt_length _ _ (j + 1) j
            x.coords

/-- The injectivity walk's pool half: at null values on the
exhaust's tops, every pool member reads a null value — the blocks
span the carrier, and the value's combination collapses at the
null rows. -/
private theorem pool_null (d k : Nat) (hd : 0 < d)
    (T : List Nat → elim.Mat) (hmv : movedAt d k T)
    (htops : ∀ t ∈ blockcount.exhaust d (monPool d k),
      poly.unitTail (elim.matVec (T t.content) t.coords)) :
    ∀ x ∈ monPool d k,
      poly.unitTail (elim.matVec (T x.content) x.coords) := by
  intro x hx
  have hpack := monPool_pack d hd k
  have hsp := blockcount.exhaust_span d (monPool d k) hpack.1
    hpack.2.1 x hx
  have hjn := join_null d k hd T hmv htops
  obtain ⟨c0, cs, hc0, hcl, hone⟩ := elim.span_elim hsp
  have hrows : ∀ q,
      q < (blockcount.groupAt
        (blockcount.blockJoin d
          (blockcount.exhaust d (monPool d k)))
        x.content).length →
      poly.unitTail (elim.matVec (T x.content)
        (ground.getAt []
          (blockcount.groupAt
            (blockcount.blockJoin d
              (blockcount.exhaust d (monPool d k)))
            x.content) q)) := by
    intro q hq
    have hqm := ground.mem_getAt ([] : List ground.BPair) _ q hq
    match ground.mem_map_of blockcount.HVec.coords _ _ hqm with
    | ⟨z, hzf, hzc⟩ =>
      match ground.mem_filter_of _ _ z hzf with
      | ⟨hzj, hzb⟩ =>
        have hzcon : z.content = x.content := ground.listBeqEq hzb
        rw [← hzc, ← hzcon]
        exact hjn z hzj
  have hszJ : ∀ v ∈ blockcount.blockJoin d
      (blockcount.exhaust d (monPool d k)), blockcount.sized v :=
    fun v hv =>
      (blockcount.exhaust_settle d (monPool d k) hpack.1 hpack.2.1
        hpack.2.2.2 v hv).1
  have hG : elim.rowsLen (places.monomialsAt x.content).length
      (blockcount.groupAt
        (blockcount.blockJoin d
          (blockcount.exhaust d (monPool d k))) x.content) :=
    blockcount.rowsLen_groupAt x.content _ hszJ
  have himg : poly.unitTail
      (elim.combo (T x.content).length cs
        ((blockcount.groupAt
            (blockcount.blockJoin d
              (blockcount.exhaust d (monPool d k)))
            x.content).map (elim.matVec (T x.content)))) := by
    refine elim.unitTail_combo_rows _ cs _ ?_
    intro q hq
    rw [ground.length_map] at hq
    rw [ground.getAt_map ([] : List ground.BPair)
      ([] : List ground.BPair) (elim.matVec (T x.content)) _ q hq]
    exact hrows q hq
  have hxlen : x.coords.length
      = (places.monomialsAt x.content).length := hpack.1 x hx
  have hchain : poly.oneValue
      (elim.matVec (T x.content) (elim.vecScale c0 x.coords))
      (elim.combo (T x.content).length cs
        ((blockcount.groupAt
            (blockcount.blockJoin d
              (blockcount.exhaust d (monPool d k)))
            x.content).map (elim.matVec (T x.content)))) := by
    refine poly.oneValue_trans
      (elim.matVec_congr (T x.content) _ _ hone) ?_
    have hG' : elim.rowsLen x.coords.length
        (blockcount.groupAt
          (blockcount.blockJoin d
            (blockcount.exhaust d (monPool d k))) x.content) := by
      rw [hxlen]
      exact hG
    exact elim.matVec_combo (T x.content) x.coords.length cs _ hG'
  have hnull1 : poly.unitTail
      (elim.matVec (T x.content) (elim.vecScale c0 x.coords)) :=
    poly.oneValue_unitTail hchain himg
  have hnull2 : poly.unitTail
      (elim.vecScale c0 (elim.matVec (T x.content) x.coords)) :=
    poly.unitTail_oneValue_right hnull1
      (elim.matVec_vecScale_free (T x.content) c0 x.coords)
  exact elim.unitTail_unscale c0 hc0 _ hnull2

/-- A null-valued family's form coordinates read the unit tail:
the matrices' entries are the values at the identity rows, pool
members at every occupied content. -/
private theorem flat_null (d k : Nat) (hd : 0 < d)
    (T : List Nat → elim.Mat) (hsq : sqAt d k T)
    (hpool : ∀ x ∈ monPool d k,
      poly.unitTail (elim.matVec (T x.content) x.coords)) :
    poly.unitTail (flatF d k T) := by
  refine unitTail_flatMap _ (places.allContents d k) ?_
  intro mu hmu
  obtain ⟨hlen, hsum⟩ := places.allContents_reads d k mu hmu
  obtain ⟨hrw, hln⟩ := hsq mu hmu
  refine unitTail_flat_rows (T mu) ?_
  intro p hp
  have hplen : (ground.getAt [] (T mu) p).length
      = (places.monomialsAt mu).length :=
    elim.rowsLen_getAt _ p hrw hp
  refine elim.unitTail_of_getAt _ ?_
  intro q hq
  rw [hplen] at hq
  have hvq := monPool_occ d hd k mu hlen hsum q hq
  have hnull := hpool _ hvq
  have hentry : (ground.getAt ground.BPair.unit
      (elim.matVec (T mu)
        (ground.getAt []
          (elim.idList (places.monomialsAt mu).length) q))
      p).oneValue ground.BPair.unit := by
    exact poly.getAt_unitTail hnull p
  rw [elim.getAt_matVec (T mu) _ p hp] at hentry
  have hrow := elim.dotN_idList_entry
    (places.monomialsAt mu).length (ground.getAt [] (T mu) p)
    hplen q hq
  exact ground.BPair.oneValue_trans
    (ground.BPair.oneValue_symm hrow) hentry

/-- The values are tops: at an exhaust top the family's value has
null stacked raisings — each raising of the value is the moved
read at the top's own null raising image. -/
private theorem val_top (d k : Nat) (hd : 0 < d)
    (T : List Nat → elim.Mat) (hmv : movedAt d k T) :
    ∀ t ∈ blockcount.exhaust d (monPool d k),
      poly.unitTail (elim.matVec (units.stackedRaise t.content)
        (elim.matVec (T t.content) t.coords)) := by
  intro t ht
  have hpack := monPool_pack d hd k
  obtain ⟨hsz, hwid, _, hup⟩ :=
    blockcount.exhaust_top d (monPool d k) hpack.1 hpack.2.1
      hpack.2.2.2 t ht
  obtain ⟨_, _, hocc⟩ := exhaust_reads d k hd t ht
  refine units.stackedRaise_of t.content _ ?_
  intro i hi hgo
  have hid : i + 1 < d := by
    rw [← hwid]
    exact hi
  have hiD : i < d := Nat.lt_trans (Nat.lt_succ_self i) hid
  have hne : ¬ i = i + 1 :=
    fun he => absurd he.symm (Nat.succ_ne_self i)
  have hszt : t.coords.length
      = (places.monomialsAt t.content).length := hsz
  have hchain := hmv t.content hocc i (i + 1) hiD hid hne
    t.coords hszt
  rw [blockcount.moveAt_moveUp i t.content] at hchain
  have hnullR : poly.unitTail
      (elim.matVec (T (units.moveUp i t.content))
        (elim.matVec
          (units.matUnitAt (units.moveUp i t.content)
            t.content i (i + 1)) t.coords)) := by
    refine elim.matVec_null _ _ ?_
    have hact := hup (i + 1) hid i (Nat.lt_succ_self i)
    show poly.unitTail
      (elim.matVec
        (units.matUnitAt (units.moveUp i t.content)
          t.content i (i + 1)) t.coords)
    rw [← blockcount.moveAt_moveUp i t.content]
    exact hact
  exact poly.oneValue_unitTail hchain hnullR

/-- The stacked width: one coordinate block per top, at the top's
content enumeration. -/
private def stackW : List blockcount.HVec → Nat
  | [] => 0
  | t :: ws => (places.monomialsAt t.content).length + stackW ws

/-- The stacked top values: the family's value at each top,
concatenated in the exhaustion's order. -/
private def stackF (T : List Nat → elim.Mat) :
    List blockcount.HVec → List ground.BPair
  | [] => []
  | t :: ws => elim.matVec (T t.content) t.coords ++ stackF T ws

/-- The raising kernels' joined list: each top's kernel list
padded into its own coordinate block. -/
private def kersAt : List blockcount.HVec → elim.Mat
  | [] => []
  | t :: ws =>
    (elim.kernelList (places.monomialsAt t.content).length
        (units.stackedRaise t.content)).map
      (fun r => r ++ List.replicate (stackW ws) ground.BPair.unit)
    ++ (kersAt ws).map
      (fun r =>
        List.replicate (places.monomialsAt t.content).length
          ground.BPair.unit ++ r)

/-- The stacked values' length at framed blocks. -/
private theorem length_stackF (T : List Nat → elim.Mat) :
    ∀ ws : List blockcount.HVec,
      (∀ t ∈ ws, (T t.content).length
        = (places.monomialsAt t.content).length) →
      (stackF T ws).length = stackW ws
  | [], _ => rfl
  | t :: ws, h => by
    show (elim.matVec (T t.content) t.coords ++ stackF T ws).length
      = (places.monomialsAt t.content).length + stackW ws
    rw [ground.length_append, elim.matVec_length,
      h t (List.Mem.head ws),
      length_stackF T ws (fun z hz => h z (List.Mem.tail t hz))]

/-- The joined kernel list's rows sit at the stacked width. -/
private theorem rowsLen_kersAt : ∀ ws : List blockcount.HVec,
    elim.rowsLen (stackW ws) (kersAt ws)
  | [] => trivial
  | t :: ws => by
    show elim.rowsLen
      ((places.monomialsAt t.content).length + stackW ws) _
    refine elim.rowsLen_append _ ?_ ?_
    · refine elim.rowsLen_map _ _ _ ?_
      intro r hr
      rw [ground.length_append, ground.length_replicate,
        elim.rowsLen_of_mem (elim.kernelList_rowsLen _ _) hr]
    · refine elim.rowsLen_map _ _ _ ?_
      intro r hr
      rw [ground.length_append, ground.length_replicate,
        elim.rowsLen_of_mem (rowsLen_kersAt ws) hr]

/-- The joined kernel list's length: the kernel dimensions'
fold. -/
private theorem length_kersAt : ∀ ws : List blockcount.HVec,
    (kersAt ws).length
      = ground.famFold Nat.add 0
          (fun t => elim.kernelDim
            (places.monomialsAt t.content).length
            (units.stackedRaise t.content)) ws
  | [] => rfl
  | t :: ws => by
    show ((elim.kernelList (places.monomialsAt t.content).length
        (units.stackedRaise t.content)).map _
      ++ (kersAt ws).map _).length
      = elim.kernelDim (places.monomialsAt t.content).length
          (units.stackedRaise t.content)
        + ground.famFold Nat.add 0 _ ws
    rw [ground.length_append, ground.length_map, ground.length_map,
      elim.kernelList_dim, length_kersAt ws]

/-- The stacked values sit in the joined kernels' span: per top
the value is a kernel member of its own stacked raisings, the
kernel list spans it, and the padded spans join blockwise. -/
private theorem stack_span (T : List Nat → elim.Mat) :
    ∀ ws : List blockcount.HVec,
      (∀ t ∈ ws, (T t.content).length
        = (places.monomialsAt t.content).length) →
      (∀ t ∈ ws, poly.unitTail
        (elim.matVec (units.stackedRaise t.content)
          (elim.matVec (T t.content) t.coords))) →
      elim.spanRel (stackW ws) (kersAt ws) (stackF T ws)
  | [], _, _ =>
    elim.spanRel_null 0 [] [] trivial trivial rfl
  | t :: ws, hf, hk => by
    have hlen : (elim.matVec (T t.content) t.coords).length
        = (places.monomialsAt t.content).length := by
      rw [elim.matVec_length]
      exact hf t (List.Mem.head ws)
    have hsp1 : elim.spanRel (places.monomialsAt t.content).length
        (elim.kernelList (places.monomialsAt t.content).length
          (units.stackedRaise t.content))
        (elim.matVec (T t.content) t.coords) :=
      elim.kernelList_span _ _
        (units.rowsLen_stackedRaise t.content) _ hlen
        (hk t (List.Mem.head ws))
    have hsp1p := elim.spanRel_padR
      (places.monomialsAt t.content).length (stackW ws) _ _ hsp1
    have hIH := stack_span T ws
      (fun z hz => hf z (List.Mem.tail t hz))
      (fun z hz => hk z (List.Mem.tail t hz))
    have hIHp := elim.spanRel_padL
      (places.monomialsAt t.content).length (stackW ws) _ _ hIH
    have hlen2 : (stackF T ws).length = stackW ws :=
      length_stackF T ws (fun z hz => hf z (List.Mem.tail t hz))
    have hL1 : elim.rowsLen
        ((places.monomialsAt t.content).length + stackW ws)
        ((elim.kernelList (places.monomialsAt t.content).length
          (units.stackedRaise t.content)).map
          (fun r => r ++ List.replicate (stackW ws)
            ground.BPair.unit)) := hsp1p.1
    have hL2 : elim.rowsLen
        ((places.monomialsAt t.content).length + stackW ws)
        ((kersAt ws).map
          (fun r => List.replicate
            (places.monomialsAt t.content).length
            ground.BPair.unit ++ r)) := hIHp.1
    have hj1 : elim.spanRel
        ((places.monomialsAt t.content).length + stackW ws)
        (kersAt (t :: ws))
        (elim.matVec (T t.content) t.coords
          ++ List.replicate (stackW ws) ground.BPair.unit) := by
      refine elim.spanRel_append_comm _ _ _ _ hL2 hL1 ?_
      exact elim.spanRel_mono_left _ _ _ _ hL2 hL1 hsp1p
    have hj2 : elim.spanRel
        ((places.monomialsAt t.content).length + stackW ws)
        (kersAt (t :: ws))
        (List.replicate (places.monomialsAt t.content).length
          ground.BPair.unit ++ stackF T ws) :=
      elim.spanRel_mono_left _ _ _ _ hL1 hL2 hIHp
    have hadd := elim.spanRel_add _ _ _ _
      (elim.rowsLen_append _ hL1 hL2)
      hj1.2.1 hj2.2.1 hj1 hj2
    refine elim.spanRel_congr _ _ _ _ ?_ hadd ?_
    · refine poly.oneValue_trans
        (elim.vecAdd_append _ _ _ _
          (by rw [hlen, ground.length_replicate])) ?_
      refine poly.oneValue_append _ _ _ _ ?_ ?_ ?_
      · rw [elim.length_vecAdd _ _
          (places.monomialsAt t.content).length hlen
          (ground.length_replicate _ _), hlen]
      · exact elim.vecAdd_null_right _ _
          (by rw [hlen, ground.length_replicate])
          (poly.unitTail_replicate _)
      · exact elim.vecAdd_null_left _ _
          (by rw [ground.length_replicate, hlen2])
          (poly.unitTail_replicate _)
    · show (elim.matVec (T t.content) t.coords
        ++ stackF T ws).length = _
      rw [ground.length_append, hlen, hlen2]
      rfl

/-! The combination kit: the matrices' entrywise combination with
its shape, action, and flattening reads — `lem:mixedinv`'s
families combining at the entries, the action's row fold reading
each entry once, private plumbing over `def:elim`'s calculus. -/

/-- The rows' scale: every row at the scalar's multiple. -/
private def scaleRows (c : ground.BPair) (M : elim.Mat) : elim.Mat :=
  M.map (elim.vecScale c)

/-- The matrices' combination at stated shape: entrywise, the
rows' scaled sum, seeded at the null matrix. -/
private def comboRows (r w : Nat) :
    List ground.BPair → List elim.Mat → elim.Mat
  | _, [] => elim.nullMat r w
  | [], _ => elim.nullMat r w
  | c :: cs, M :: Ms =>
    elim.matAdd (scaleRows c M) (comboRows r w cs Ms)

/-- The scaled rows' count is the family's own. -/
private theorem length_scaleRows (c : ground.BPair) (M : elim.Mat) :
    (scaleRows c M).length = M.length :=
  ground.length_map (elim.vecScale c) M

/-- The scaled rows keep the stated width. -/
private theorem rowsLen_scaleRows (w : Nat) (c : ground.BPair) :
    ∀ M : elim.Mat, elim.rowsLen w M → elim.rowsLen w (scaleRows c M)
  | [], _ => trivial
  | a :: M, h =>
    ⟨(elim.length_vecScale c a).trans h.1,
     rowsLen_scaleRows w c M h.2⟩

/-- The vacant coefficient list combines to the null matrix at
every family. -/
private theorem comboRows_nilL (r w : Nat) :
    ∀ Ms : List elim.Mat, comboRows r w [] Ms = elim.nullMat r w
  | [] => rfl
  | _ :: _ => rfl

/-- The combination's row count. -/
private theorem length_comboRows (r w : Nat) :
    ∀ (cs : List ground.BPair) (Ms : List elim.Mat),
      (∀ M, M ∈ Ms → M.length = r) →
      (comboRows r w cs Ms).length = r := by
  intro cs
  induction cs with
  | nil =>
    intro Ms _
    rw [comboRows_nilL r w Ms]
    exact elim.length_nullMat r w
  | cons c cs ih =>
    intro Ms
    cases Ms with
    | nil =>
      intro _
      exact elim.length_nullMat r w
    | cons M Ms =>
      intro h
      have hM : M.length = r := h M (List.Mem.head Ms)
      have hrest : ∀ M', M' ∈ Ms → M'.length = r :=
        fun M' hM' => h M' (List.Mem.tail M hM')
      have hA : (scaleRows c M).length = r :=
        (length_scaleRows c M).trans hM
      have hB : (comboRows r w cs Ms).length = r := ih Ms hrest
      show (elim.matAdd (scaleRows c M) (comboRows r w cs Ms)).length = r
      rw [elim.length_matAdd _ _ (hA.trans hB.symm)]
      exact hA

/-- The combination's row widths. -/
private theorem rowsLen_comboRows (r w : Nat) :
    ∀ (cs : List ground.BPair) (Ms : List elim.Mat),
      (∀ M, M ∈ Ms → M.length = r ∧ elim.rowsLen w M) →
      elim.rowsLen w (comboRows r w cs Ms) := by
  intro cs
  induction cs with
  | nil =>
    intro Ms _
    rw [comboRows_nilL r w Ms]
    exact elim.rowsLen_nullMat r w
  | cons c cs ih =>
    intro Ms
    cases Ms with
    | nil =>
      intro _
      exact elim.rowsLen_nullMat r w
    | cons M Ms =>
      intro h
      have hM : M.length = r ∧ elim.rowsLen w M := h M (List.Mem.head Ms)
      have hrest : ∀ M', M' ∈ Ms → M'.length = r ∧ elim.rowsLen w M' :=
        fun M' hM' => h M' (List.Mem.tail M hM')
      show elim.rowsLen w
        (elim.matAdd (scaleRows c M) (comboRows r w cs Ms))
      exact elim.rowsLen_matAdd w _ _
        (rowsLen_scaleRows w c M hM.2) (ih Ms hrest)

/-- The scaled rows' action is the action's own scale. -/
private theorem matVec_scaleRows (c : ground.BPair) :
    ∀ (M : elim.Mat) (x : List ground.BPair),
      poly.oneValue (elim.matVec (scaleRows c M) x)
        (elim.vecScale c (elim.matVec M x))
  | [], _ => trivial
  | a :: M, x => ⟨elim.dotN_scaleRow_free c a x, matVec_scaleRows c M x⟩

/-- The action reads the combination memberwise: the combined
matrix's value is the members' values' combination. -/
private theorem matVec_comboRows (r w : Nat) :
    ∀ (cs : List ground.BPair) (Ms : List elim.Mat)
      (x : List ground.BPair),
      (∀ M, M ∈ Ms → M.length = r ∧ elim.rowsLen w M) →
      poly.oneValue (elim.matVec (comboRows r w cs Ms) x)
        (elim.combo r cs (Ms.map (fun M => elim.matVec M x))) := by
  intro cs
  induction cs with
  | nil =>
    intro Ms x _
    rw [comboRows_nilL r w Ms]
    show poly.oneValue (elim.matVec (elim.nullMat r w) x)
      (List.replicate r BPair.unit)
    exact poly.unitTail_oneValue (elim.matVec_nullMat r w x)
      (poly.unitTail_replicate r)
  | cons c cs ih =>
    intro Ms
    cases Ms with
    | nil =>
      intro x _
      show poly.oneValue (elim.matVec (elim.nullMat r w) x)
        (List.replicate r BPair.unit)
      exact poly.unitTail_oneValue (elim.matVec_nullMat r w x)
        (poly.unitTail_replicate r)
    | cons M Ms =>
      intro x h
      have hM : M.length = r ∧ elim.rowsLen w M := h M (List.Mem.head Ms)
      have hrest : ∀ M', M' ∈ Ms → M'.length = r ∧ elim.rowsLen w M' :=
        fun M' hM' => h M' (List.Mem.tail M hM')
      have hrows : elim.rowsLen r (Ms.map (fun M => elim.matVec M x)) :=
        elim.rowsLen_map _ r Ms (fun M' hM' =>
          (elim.matVec_length M' x).trans (hrest M' hM').1)
      show poly.oneValue
        (elim.matVec (elim.matAdd (scaleRows c M)
          (comboRows r w cs Ms)) x)
        (elim.vecAdd (elim.vecScale c (elim.matVec M x))
          (elim.combo r cs (Ms.map (fun M => elim.matVec M x))))
      refine poly.oneValue_trans
        (elim.matVec_add_free w (scaleRows c M) (comboRows r w cs Ms) x
          (rowsLen_scaleRows w c M hM.2)
          (rowsLen_comboRows r w cs Ms hrest)) ?_
      refine elim.polyOne_vecAdd _ _ _ _
        (matVec_scaleRows c M x) (ih Ms x hrest) ?_ ?_
      · rw [elim.matVec_length, elim.length_vecScale, elim.matVec_length]
        exact length_scaleRows c M
      · rw [elim.matVec_length,
          length_comboRows r w cs Ms (fun M' hM' => (hrest M' hM').1),
          elim.length_combo r cs _ hrows]

/-- The null matrix's flat sits at the unit tail. -/
private theorem unitTail_flatCat_null (w : Nat) :
    ∀ r : Nat, poly.unitTail (elim.flatCat (elim.nullMat r w))
  | 0 => trivial
  | r + 1 =>
    elim.unitTail_append (poly.unitTail_replicate w)
      (unitTail_flatCat_null w r)

/-- The entrywise sum's flat is the flats' memberwise sum. -/
private theorem flatCat_matAdd (w : Nat) :
    ∀ A B : elim.Mat, elim.rowsLen w A → elim.rowsLen w B →
      elim.flatCat (elim.matAdd A B) = elim.vecAdd (elim.flatCat A) (elim.flatCat B)
  | [], _, _, _ => rfl
  | a :: A, [], _, _ =>
    (elim.vecAdd_comm (a ++ elim.flatCat A) ([] : List ground.BPair)).symm
  | a :: A, b :: B, ha, hb => by
    show elim.vecAdd a b ++ elim.flatCat (elim.matAdd A B)
      = elim.vecAdd (a ++ elim.flatCat A) (b ++ elim.flatCat B)
    rw [elim.vecAdd_app a (elim.flatCat A) b (elim.flatCat B)
        (ha.1.trans hb.1.symm),
      flatCat_matAdd w A B ha.2 hb.2]

/-- The scaled rows' flat is the flat's own scale. -/
private theorem flatCat_scaleRows (c : ground.BPair) :
    ∀ M : elim.Mat, elim.flatCat (scaleRows c M) = elim.vecScale c (elim.flatCat M)
  | [] => rfl
  | a :: M => by
    show elim.vecScale c a ++ elim.flatCat (scaleRows c M)
      = elim.vecScale c (a ++ elim.flatCat M)
    rw [flatCat_scaleRows c M, elim.vecScale_append c a (elim.flatCat M)]

/-- The flattened combination is the flats' combination. -/
private theorem flatCat_comboRows (r w : Nat) :
    ∀ (cs : List ground.BPair) (Ms : List elim.Mat),
      (∀ M, M ∈ Ms → M.length = r ∧ elim.rowsLen w M) →
      poly.oneValue (elim.flatCat (comboRows r w cs Ms))
        (elim.combo (r * w) cs (Ms.map elim.flatCat)) := by
  intro cs
  induction cs with
  | nil =>
    intro Ms _
    rw [comboRows_nilL r w Ms]
    show poly.oneValue (elim.flatCat (elim.nullMat r w))
      (List.replicate (r * w) BPair.unit)
    exact poly.unitTail_oneValue (unitTail_flatCat_null w r)
      (poly.unitTail_replicate (r * w))
  | cons c cs ih =>
    intro Ms
    cases Ms with
    | nil =>
      intro _
      show poly.oneValue (elim.flatCat (elim.nullMat r w))
        (List.replicate (r * w) BPair.unit)
      exact poly.unitTail_oneValue (unitTail_flatCat_null w r)
        (poly.unitTail_replicate (r * w))
    | cons M Ms =>
      intro h
      have hM : M.length = r ∧ elim.rowsLen w M := h M (List.Mem.head Ms)
      have hrest : ∀ M', M' ∈ Ms → M'.length = r ∧ elim.rowsLen w M' :=
        fun M' hM' => h M' (List.Mem.tail M hM')
      have hrows : elim.rowsLen (r * w) (Ms.map elim.flatCat) :=
        elim.rowsLen_map elim.flatCat (r * w) Ms (fun M' hM' =>
          (elim.length_flatCat w M' (hrest M' hM').2).trans
            (congrArg (fun t => t * w) (hrest M' hM').1))
      show poly.oneValue
        (elim.flatCat (elim.matAdd (scaleRows c M) (comboRows r w cs Ms)))
        (elim.vecAdd (elim.vecScale c (elim.flatCat M))
          (elim.combo (r * w) cs (Ms.map elim.flatCat)))
      rw [flatCat_matAdd w (scaleRows c M) (comboRows r w cs Ms)
          (rowsLen_scaleRows w c M hM.2)
          (rowsLen_comboRows r w cs Ms hrest),
        flatCat_scaleRows c M]
      refine elim.polyOne_vecAdd _ _ _ _
        (poly.oneValue_refl _) (ih Ms hrest) rfl ?_
      rw [elim.length_flatCat w (comboRows r w cs Ms)
          (rowsLen_comboRows r w cs Ms hrest),
        length_comboRows r w cs Ms (fun M' hM' => (hrest M' hM').1),
        elim.length_combo (r * w) cs (Ms.map elim.flatCat) hrows]

/-- The columnwise append: two combinations at one coefficient
list join to the zipped rows' combination. -/
private theorem combo_zipApp (n m : Nat) :
    ∀ (cs : List ground.BPair) (X Y : elim.Mat),
      elim.rowsLen n X → elim.rowsLen m Y → X.length = Y.length →
      poly.oneValue (elim.combo n cs X ++ elim.combo m cs Y)
        (elim.combo (n + m) cs
          (List.zipWith (fun a b => a ++ b) X Y)) := by
  intro cs
  induction cs with
  | nil =>
    intro X Y _ _ _
    show poly.oneValue
      (List.replicate n BPair.unit ++ List.replicate m BPair.unit)
      (List.replicate (n + m) BPair.unit)
    exact poly.unitTail_oneValue
      (elim.unitTail_append (poly.unitTail_replicate n)
        (poly.unitTail_replicate m))
      (poly.unitTail_replicate (n + m))
  | cons c cs ih =>
    intro X Y hX hY hl
    cases X with
    | nil =>
      cases Y with
      | nil =>
        show poly.oneValue
          (List.replicate n BPair.unit ++ List.replicate m BPair.unit)
          (List.replicate (n + m) BPair.unit)
        exact poly.unitTail_oneValue
          (elim.unitTail_append (poly.unitTail_replicate n)
            (poly.unitTail_replicate m))
          (poly.unitTail_replicate (n + m))
      | cons b Y => exact Nat.noConfusion hl
    | cons a X =>
      cases Y with
      | nil => exact Nat.noConfusion hl
      | cons b Y =>
        have hXn : (elim.combo n cs X).length = n :=
          elim.length_combo n cs X hX.2
        have hYm : (elim.combo m cs Y).length = m :=
          elim.length_combo m cs Y hY.2
        have hsa : (elim.vecScale c a).length = n :=
          (elim.length_vecScale c a).trans hX.1
        have hrow : elim.rowsLen (n + m)
            (List.zipWith (fun p q => p ++ q) X Y) :=
          elim.rowsLen_rowJoin n m hX.2 hY.2
        have hjoin :
            elim.vecAdd (elim.vecScale c a) (elim.combo n cs X)
              ++ elim.vecAdd (elim.vecScale c b) (elim.combo m cs Y)
            = elim.vecAdd (elim.vecScale c a ++ elim.vecScale c b)
                (elim.combo n cs X ++ elim.combo m cs Y) :=
          (elim.vecAdd_app (elim.vecScale c a) (elim.vecScale c b)
            (elim.combo n cs X) (elim.combo m cs Y)
            (hsa.trans hXn.symm)).symm
        show poly.oneValue
          (elim.vecAdd (elim.vecScale c a) (elim.combo n cs X)
            ++ elim.vecAdd (elim.vecScale c b) (elim.combo m cs Y))
          (elim.vecAdd (elim.vecScale c (a ++ b))
            (elim.combo (n + m) cs
              (List.zipWith (fun p q => p ++ q) X Y)))
        rw [hjoin, elim.vecScale_append c a b]
        refine elim.polyOne_vecAdd _ _ _ _ (poly.oneValue_refl _)
          (ih X Y hX.2 hY.2 (Nat.succ.inj hl)) rfl ?_
        rw [ground.length_append (elim.combo n cs X) (elim.combo m cs Y),
          hXn, hYm,
          elim.length_combo (n + m) cs
            (List.zipWith (fun p q => p ++ q) X Y) hrow]
/-- A combination at pointwise one-value rows reads one value. -/
private theorem combo_rows_congr (n : Nat) :
    ∀ (cs : List ground.BPair) (A B : elim.Mat),
      elim.rowsLen n A → elim.rowsLen n B →
      A.length = B.length →
      (∀ q, q < A.length →
        poly.oneValue (ground.getAt [] A q) (ground.getAt [] B q)) →
      poly.oneValue (elim.combo n cs A) (elim.combo n cs B)
  | [], _, _, _, _, _, _ => poly.oneValue_refl _
  | _ :: _, [], [], _, _, _, _ => poly.oneValue_refl _
  | _ :: _, [], _ :: _, _, _, hl, _ => nomatch hl
  | _ :: _, _ :: _, [], _, _, hl, _ => nomatch hl
  | c :: cs, a :: A, b :: B, hA, hB, hl, h => by
    show poly.oneValue
      (elim.vecAdd (elim.vecScale c a) (elim.combo n cs A))
      (elim.vecAdd (elim.vecScale c b) (elim.combo n cs B))
    refine elim.polyOne_vecAdd _ _ _ _
      (elim.vecScale_oneValue c _ _ (h 0 (Nat.succ_pos _)))
      (combo_rows_congr n cs A B hA.2 hB.2 (Nat.succ.inj hl)
        (fun q hq => h (q + 1) (Nat.succ_lt_succ hq)))
      ?_ ?_
    · rw [elim.length_vecScale, elim.length_vecScale, hA.1, hB.1]
    · rw [elim.length_combo n cs A hA.2,
        elim.length_combo n cs B hB.2]

/-- The statement's family list: the permutation families with the
stated one joined. -/
private def famList (k : Nat) (T : List Nat → elim.Mat) :
    List (List Nat → elim.Mat) :=
  (places.perms k).map permMat ++ [T]

/-- The family list's frames member by member. -/
private theorem fam_frames (d k : Nat) (T : List Nat → elim.Mat)
    (hsq : sqAt d k T) :
    ∀ S ∈ famList k T, sqAt d k S := by
  intro S hS
  cases ground.mem_append_of _ _ hS with
  | inl hm =>
    match ground.mem_map_of permMat _ S hm with
    | ⟨σ, _, hσS⟩ =>
      intro mu _
      rw [← hσS]
      exact ⟨rowsLen_permMat σ mu, length_permMat σ mu⟩
  | inr hm =>
    have hm' : S ∈ [T] := hm
    cases hm' with
    | head => exact hsq
    | tail _ hn => exact nomatch hn

/-- The family list's moved reads member by member. -/
private theorem fam_moved (d k : Nat) (T : List Nat → elim.Mat)
    (hmv : movedAt d k T) :
    ∀ S ∈ famList k T, movedAt d k S := by
  intro S hS
  cases ground.mem_append_of _ _ hS with
  | inl hm =>
    match ground.mem_map_of permMat _ S hm with
    | ⟨σ, hσ, hσS⟩ =>
      intro mu hmu i j hi hj hij x hx
      rw [← hσS]
      exact permMat_moved k σ (ground.countOf_pos_of_mem hσ) d mu
        hmu i j hi hj hij x hx
  | inr hm =>
    have hm' : S ∈ [T] := hm
    cases hm' with
    | head => exact hmv
    | tail _ hn => exact nomatch hn

/-- The combined family at stated coefficients: the entrywise
combination per content. -/
private def famC (ds : List ground.BPair)
    (Ss : List (List Nat → elim.Mat)) (mu : List Nat) : elim.Mat :=
  comboRows (places.monomialsAt mu).length
    (places.monomialsAt mu).length ds (Ss.map (fun S => S mu))

/-- The evaluated members' frames at an occupied content. -/
private theorem fam_mats (d k : Nat)
    (Ss : List (List Nat → elim.Mat)) (hf : ∀ S ∈ Ss, sqAt d k S)
    (mu : List Nat)
    (hmu : 0 < ground.countOf mu (places.allContents d k)) :
    ∀ M ∈ Ss.map (fun S => S mu),
      M.length = (places.monomialsAt mu).length
        ∧ elim.rowsLen (places.monomialsAt mu).length M := by
  intro M hM
  match ground.mem_map_of
      (fun (S : List Nat → elim.Mat) => S mu) _ M hM with
  | ⟨S, hS, hSM⟩ =>
    rw [← hSM]
    exact ⟨(hf S hS mu hmu).2, (hf S hS mu hmu).1⟩

/-- The combined family's frames. -/
private theorem famC_frames (d k : Nat) (ds : List ground.BPair)
    (Ss : List (List Nat → elim.Mat))
    (hf : ∀ S ∈ Ss, sqAt d k S) : sqAt d k (famC ds Ss) := by
  intro mu hmu
  have hM := fam_mats d k Ss hf mu hmu
  exact ⟨rowsLen_comboRows _ _ ds _ hM,
    length_comboRows _ _ ds _ (fun M hMm => (hM M hMm).1)⟩

/-- The combined family's moved reads: the unit action passes
through the combination memberwise, the illegal move null on both
sides. -/
private theorem famC_moved (d k : Nat) (ds : List ground.BPair)
    (Ss : List (List Nat → elim.Mat))
    (hf : ∀ S ∈ Ss, sqAt d k S) (hm : ∀ S ∈ Ss, movedAt d k S) :
    movedAt d k (famC ds Ss) := by
  intro mu hmu i j hi hj hij x hx
  match Nat.eq_zero_or_pos (ground.getAt 0 mu j) with
  | .inl hz =>
    exact poly.unitTail_oneValue
      (units.matVec_null_unocc _ mu i j hz _)
      (elim.matVec_null _ _ (units.matVec_null_unocc _ mu i j hz x))
  | .inr hocc =>
    obtain ⟨hlen, hsum⟩ := places.allContents_reads d k mu hmu
    have hi' : i < mu.length := by rw [hlen]; exact hi
    have hmu' : 0 < ground.countOf (blockcount.moveAt i j mu)
        (places.allContents d k) := by
      refine content_occ d k _ ?_ ?_
      · rw [blockcount.length_moveAt, hlen]
      · rw [blockcount.sumNat_moveAt i j mu hi' hocc]
        exact hsum
    have hMmu := fam_mats d k Ss hf mu hmu
    have hMmu' := fam_mats d k Ss hf _ hmu'
    have hUlen := units.length_matUnitAt
      (blockcount.moveAt i j mu) mu i j
    have hVrows : elim.rowsLen (places.monomialsAt mu).length
        (Ss.map (fun S => elim.matVec (S mu) x)) := by
      refine elim.rowsLen_map _ _ _ ?_
      intro S hS
      rw [elim.matVec_length]
      exact (hf S hS mu hmu).2
    have step1 : poly.oneValue
        (elim.matVec
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
          (elim.matVec (famC ds Ss mu) x))
        (elim.matVec
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
          (elim.combo (places.monomialsAt mu).length ds
            ((Ss.map (fun S => S mu)).map
              (fun M => elim.matVec M x)))) :=
      elim.matVec_congr _ _ _
        (matVec_comboRows _ _ ds _ x hMmu)
    have step2 : poly.oneValue
        (elim.matVec
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
          (elim.combo (places.monomialsAt mu).length ds
            ((Ss.map (fun S => S mu)).map
              (fun M => elim.matVec M x))))
        (elim.combo
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j).length
          ds
          (((Ss.map (fun S => S mu)).map
              (fun M => elim.matVec M x)).map
            (elim.matVec
              (units.matUnitAt (blockcount.moveAt i j mu)
                mu i j)))) := by
      refine elim.matVec_combo _ _ ds _ ?_
      rw [ground.map_map]
      exact hVrows
    rw [ground.map_map] at step1
    rw [ground.map_map, ground.map_map] at step2
    have hBrows : elim.rowsLen
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j).length
        (Ss.map (fun S =>
          elim.matVec (S (blockcount.moveAt i j mu))
            (elim.matVec
              (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
              x))) := by
      refine elim.rowsLen_map _ _ _ ?_
      intro S hS
      rw [elim.matVec_length, hUlen]
      exact (hf S hS _ hmu').2
    have hArows : elim.rowsLen
        (units.matUnitAt (blockcount.moveAt i j mu) mu i j).length
        (Ss.map (fun S =>
          elim.matVec
            (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
            (elim.matVec (S mu) x))) := by
      refine elim.rowsLen_map _ _ _ ?_
      intro S hS
      rw [elim.matVec_length]
    have step3 : poly.oneValue
        (elim.combo
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j).length
          ds
          (Ss.map (fun S =>
            elim.matVec
              (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
              (elim.matVec (S mu) x))))
        (elim.combo
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j).length
          ds
          (Ss.map (fun S =>
            elim.matVec (S (blockcount.moveAt i j mu))
              (elim.matVec
                (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
                x)))) := by
      refine combo_rows_congr _ ds _ _ hArows hBrows
        (by rw [ground.length_map, ground.length_map]) ?_
      intro q hq
      rw [ground.length_map] at hq
      have hgm := ground.getAt_map
        (fun _ => elim.nullMat 0 0)
        ([] : List ground.BPair)
        (fun S => elim.matVec
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
          (elim.matVec (S mu) x)) Ss q hq
      have hgm' := ground.getAt_map
        (fun _ => elim.nullMat 0 0)
        ([] : List ground.BPair)
        (fun S => elim.matVec (S (blockcount.moveAt i j mu))
          (elim.matVec
            (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
            x)) Ss q hq
      rw [hgm, hgm']
      exact hm _ (ground.mem_getAt _ Ss q hq) mu hmu i j hi hj hij
        x hx
    have step4 : poly.oneValue
        (elim.matVec (famC ds Ss (blockcount.moveAt i j mu))
          (elim.matVec
            (units.matUnitAt (blockcount.moveAt i j mu) mu i j) x))
        (elim.combo
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j).length
          ds
          (Ss.map (fun S =>
            elim.matVec (S (blockcount.moveAt i j mu))
              (elim.matVec
                (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
                x)))) := by
      have h4 := matVec_comboRows
        (places.monomialsAt (blockcount.moveAt i j mu)).length
        (places.monomialsAt (blockcount.moveAt i j mu)).length ds
        (Ss.map (fun S => S (blockcount.moveAt i j mu)))
        (elim.matVec
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j) x)
        hMmu'
      rw [ground.map_map] at h4
      rw [hUlen]
      exact h4
    exact poly.oneValue_trans step1
      (poly.oneValue_trans step2
        (poly.oneValue_trans step3 (poly.oneValue_symm step4)))

/-- A vacant-width combination is the vacant list. -/
private theorem combo_zero_null (ds : List ground.BPair)
    (L : elim.Mat) (hL : elim.rowsLen 0 L) :
    poly.unitTail (elim.combo 0 ds L) := by
  refine elim.unitTail_of_getAt _ ?_
  intro p hp
  rw [elim.length_combo 0 ds L hL] at hp
  exact absurd hp (Nat.not_lt_zero p)

/-- The stacked values read the combination memberwise. -/
private theorem stackF_comboF (d k : Nat) (ds : List ground.BPair)
    (Ss : List (List Nat → elim.Mat))
    (hf : ∀ S ∈ Ss, sqAt d k S) :
    ∀ ws : List blockcount.HVec,
      (∀ t ∈ ws, 0 < ground.countOf t.content
        (places.allContents d k)) →
      poly.oneValue (stackF (famC ds Ss) ws)
        (elim.combo (stackW ws) ds
          (Ss.map (fun S => stackF S ws)))
  | [], _ => by
    refine poly.unitTail_oneValue trivial ?_
    refine combo_zero_null ds _ ?_
    refine elim.rowsLen_map _ _ _ ?_
    intro S _
    rfl
  | t :: ws, hws => by
    have hmu := hws t (List.Mem.head ws)
    have hM := fam_mats d k Ss hf t.content hmu
    have hws' : ∀ z ∈ ws, 0 < ground.countOf z.content
        (places.allContents d k) :=
      fun z hz => hws z (List.Mem.tail t hz)
    have hArows : elim.rowsLen
        (places.monomialsAt t.content).length
        (Ss.map (fun S => elim.matVec (S t.content) t.coords)) := by
      refine elim.rowsLen_map _ _ _ ?_
      intro S hS
      rw [elim.matVec_length]
      exact (hf S hS t.content hmu).2
    have hBrows : elim.rowsLen (stackW ws)
        (Ss.map (fun S => stackF S ws)) := by
      refine elim.rowsLen_map _ _ _ ?_
      intro S hS
      exact length_stackF S ws
        (fun z hz => (hf S hS z.content (hws' z hz)).2)
    have h1 : poly.oneValue
        (elim.matVec (famC ds Ss t.content) t.coords)
        (elim.combo (places.monomialsAt t.content).length ds
          (Ss.map (fun S => elim.matVec (S t.content) t.coords)))
        := by
      have h0 := matVec_comboRows
        (places.monomialsAt t.content).length
        (places.monomialsAt t.content).length ds
        (Ss.map (fun S => S t.content)) t.coords hM
      rw [ground.map_map] at h0
      exact h0
    have h2 := stackF_comboF d k ds Ss hf ws hws'
    have hlen1 : (elim.matVec (famC ds Ss t.content)
        t.coords).length
        = (places.monomialsAt t.content).length := by
      rw [elim.matVec_length]
      exact length_comboRows _ _ ds _ (fun M hMm => (hM M hMm).1)
    have happ : poly.oneValue
        (stackF (famC ds Ss) (t :: ws))
        (elim.combo (places.monomialsAt t.content).length ds
            (Ss.map (fun S => elim.matVec (S t.content) t.coords))
          ++ elim.combo (stackW ws) ds
            (Ss.map (fun S => stackF S ws))) := by
      show poly.oneValue
        (elim.matVec (famC ds Ss t.content) t.coords
          ++ stackF (famC ds Ss) ws) _
      refine poly.oneValue_append _ _ _ _ ?_ h1 h2
      rw [hlen1, elim.length_combo _ ds _ hArows]
    have hzip := combo_zipApp
      (places.monomialsAt t.content).length (stackW ws) ds
      _ _ hArows hBrows
      (by rw [ground.length_map, ground.length_map])
    rw [ground.zipWith_map_map (fun a b => a ++ b)
      (fun S => elim.matVec (S t.content) t.coords)
      (fun S => stackF S ws) Ss] at hzip
    refine poly.oneValue_trans happ ?_
    show poly.oneValue _
      (elim.combo
        ((places.monomialsAt t.content).length + stackW ws) ds
        (Ss.map (fun S =>
          elim.matVec (S t.content) t.coords ++ stackF S ws)))
    exact hzip

/-- The form coordinates read the combination memberwise. -/
private theorem flatF_comboF (d k : Nat) (ds : List ground.BPair)
    (Ss : List (List Nat → elim.Mat))
    (hf : ∀ S ∈ Ss, sqAt d k S) :
    ∀ L : List (List Nat),
      (∀ mu ∈ L, 0 < ground.countOf mu (places.allContents d k)) →
      poly.oneValue
        (L.flatMap (fun mu =>
          (famC ds Ss mu).flatMap (fun r => r)))
        (elim.combo
          (ground.famFold Nat.add 0
            (fun mu => (places.monomialsAt mu).length
              * (places.monomialsAt mu).length) L)
          ds
          (Ss.map (fun S =>
            L.flatMap (fun mu => (S mu).flatMap (fun r => r)))))
  | [], _ => by
    refine poly.unitTail_oneValue trivial ?_
    refine combo_zero_null ds _ ?_
    refine elim.rowsLen_map _ _ _ ?_
    intro S _
    rfl
  | mu :: L, hL => by
    have hmu := hL mu (List.Mem.head L)
    have hM := fam_mats d k Ss hf mu hmu
    have hL' : ∀ nu ∈ L, 0 < ground.countOf nu
        (places.allContents d k) :=
      fun nu hn => hL nu (List.Mem.tail mu hn)
    have hArows : elim.rowsLen
        ((places.monomialsAt mu).length
          * (places.monomialsAt mu).length)
        (Ss.map (fun S => (S mu).flatMap (fun r => r))) := by
      refine elim.rowsLen_map _ _ _ ?_
      intro S hS
      show (elim.flatCat (S mu)).length = _
      rw [elim.length_flatCat (places.monomialsAt mu).length
          (S mu) (hf S hS mu hmu).1,
        (hf S hS mu hmu).2]
    have hBrows : elim.rowsLen
        (ground.famFold Nat.add 0
          (fun nu => (places.monomialsAt nu).length
            * (places.monomialsAt nu).length) L)
        (Ss.map (fun S =>
          L.flatMap (fun nu => (S nu).flatMap (fun r => r)))) := by
      refine elim.rowsLen_map _ _ _ ?_
      intro S hS
      exact length_flatF_go S L
        (fun nu hn => (hf S hS nu (hL' nu hn)).1)
        (fun nu hn => (hf S hS nu (hL' nu hn)).2)
    have h1 : poly.oneValue
        ((famC ds Ss mu).flatMap (fun r => r))
        (elim.combo
          ((places.monomialsAt mu).length
            * (places.monomialsAt mu).length) ds
          (Ss.map (fun S => (S mu).flatMap (fun r => r)))) := by
      have h0 := flatCat_comboRows
        (places.monomialsAt mu).length
        (places.monomialsAt mu).length ds
        (Ss.map (fun S => S mu)) hM
      rw [ground.map_map] at h0
      exact h0
    have h2 := flatF_comboF d k ds Ss hf L hL'
    have hlen1 : ((famC ds Ss mu).flatMap
        (fun r => r)).length
        = (places.monomialsAt mu).length
          * (places.monomialsAt mu).length := by
      show (elim.flatCat (comboRows (places.monomialsAt mu).length
        (places.monomialsAt mu).length ds
        (Ss.map (fun S => S mu)))).length = _
      rw [elim.length_flatCat (places.monomialsAt mu).length _
          (rowsLen_comboRows _ _ ds _ hM),
        length_comboRows _ _ ds _ (fun M hMm => (hM M hMm).1)]
    have happ : poly.oneValue
        ((mu :: L).flatMap (fun nu =>
          (famC ds Ss nu).flatMap (fun r => r)))
        (elim.combo
            ((places.monomialsAt mu).length
              * (places.monomialsAt mu).length) ds
            (Ss.map (fun S => (S mu).flatMap (fun r => r)))
          ++ elim.combo
            (ground.famFold Nat.add 0
              (fun nu => (places.monomialsAt nu).length
                * (places.monomialsAt nu).length) L) ds
            (Ss.map (fun S =>
              L.flatMap (fun nu =>
                (S nu).flatMap (fun r => r))))) := by
      show poly.oneValue
        ((famC ds Ss mu).flatMap (fun r => r)
          ++ L.flatMap (fun nu =>
            (famC ds Ss nu).flatMap (fun r => r))) _
      refine poly.oneValue_append _ _ _ _ ?_ h1 h2
      rw [hlen1, elim.length_combo _ ds _ hArows]
    have hzip := combo_zipApp
      ((places.monomialsAt mu).length
        * (places.monomialsAt mu).length)
      (ground.famFold Nat.add 0
        (fun nu => (places.monomialsAt nu).length
          * (places.monomialsAt nu).length) L)
      ds _ _ hArows hBrows
      (by rw [ground.length_map, ground.length_map])
    rw [ground.zipWith_map_map (fun a b => a ++ b)
      (fun S => (S mu).flatMap (fun r => r))
      (fun S => L.flatMap (fun nu =>
        (S nu).flatMap (fun r => r))) Ss] at hzip
    refine poly.oneValue_trans happ ?_
    show poly.oneValue _
      (elim.combo
        ((places.monomialsAt mu).length
            * (places.monomialsAt mu).length
          + ground.famFold Nat.add 0
            (fun nu => (places.monomialsAt nu).length
              * (places.monomialsAt nu).length) L) ds
        (Ss.map (fun S =>
          (S mu).flatMap (fun r => r)
            ++ L.flatMap (fun nu =>
              (S nu).flatMap (fun r => r)))))
    exact hzip

/-- A null stacked read is null block by block. -/
private theorem stackF_null_parts (C : List Nat → elim.Mat) :
    ∀ ws : List blockcount.HVec,
      poly.unitTail (stackF C ws) →
      ∀ t ∈ ws, poly.unitTail
        (elim.matVec (C t.content) t.coords)
  | [], _, t, ht => nomatch ht
  | z :: ws, h, t, ht => by
    have hsplit := elim.unitTail_append_split
      (elim.matVec (C z.content) z.coords) (stackF C ws) h
    cases ht with
    | head => exact hsplit.1
    | tail _ hm => exact stackF_null_parts C ws hsplit.2 t hm

/-- The stacked images' independence: a null combination names the
combined family, null outright by the walk at its null top values,
so its form coordinates are the flats' null combination and the
coefficients read back at the flats' independence. -/
private theorem stack_indep (d k : Nat) (hd : 0 < d)
    (T : List Nat → elim.Mat) (hsq : sqAt d k T)
    (hmv : movedAt d k T)
    (hind : elim.indepRows (mixWidth d k)
      ((famList k T).map (flatF d k))) :
    elim.indepRows (stackW (blockcount.exhaust d (monPool d k)))
      ((famList k T).map
        (fun S => stackF S (blockcount.exhaust d (monPool d k))))
    := by
  have hocc : ∀ t ∈ blockcount.exhaust d (monPool d k),
      0 < ground.countOf t.content (places.allContents d k) :=
    fun t ht => (exhaust_reads d k hd t ht).2.2
  have hfr := fam_frames d k T hsq
  have hmo := fam_moved d k T hmv
  have hrows : elim.rowsLen
      (stackW (blockcount.exhaust d (monPool d k)))
      ((famList k T).map
        (fun S => stackF S
          (blockcount.exhaust d (monPool d k)))) := by
    refine elim.rowsLen_map _ _ _ ?_
    intro S hS
    exact length_stackF S _
      (fun t ht => (hfr S hS t.content (hocc t ht)).2)
  refine elim.indep_intro _ _ hrows ?_
  intro ds hdl hnull
  have h1 := stackF_comboF d k ds (famList k T) hfr
    (blockcount.exhaust d (monPool d k)) hocc
  have hstack : poly.unitTail
      (stackF (famC ds (famList k T))
        (blockcount.exhaust d (monPool d k))) :=
    poly.oneValue_unitTail h1 hnull
  have htops := stackF_null_parts (famC ds (famList k T)) _ hstack
  have hCsq := famC_frames d k ds (famList k T) hfr
  have hCmv := famC_moved d k ds (famList k T) hfr hmo
  have hpool := pool_null d k hd (famC ds (famList k T)) hCmv htops
  have hflat := flat_null d k hd (famC ds (famList k T)) hCsq hpool
  have h2 := flatF_comboF d k ds (famList k T) hfr
    (places.allContents d k)
    (fun mu hm => ground.countOf_pos_of_mem hm)
  have hcnull : poly.unitTail
      (elim.combo (mixWidth d k) ds
        ((famList k T).map (fun S => flatF d k S))) := by
    refine poly.unitTail_oneValue_right ?_ h2
    exact hflat
  refine elim.indep_elim hind ds ?_ hcnull
  rw [hdl, ground.length_map, ground.length_map]

/-- The joined kernel list's count at the exhaustion is the
factorial: the kernel dimensions regroup over the distinct
contents, each content's occupancy is its own block count, the
collapsed fold runs over the shapes, and the square sum closes at
the path counts. -/
private theorem kers_count (d k : Nat) (hd : 0 < d) (hk : k ≤ d) :
    (kersAt (blockcount.exhaust d (monPool d k))).length
      = ground.factorial k := by
  have hpack := monPool_pack d hd k
  have hcnt : ∀ mu : List Nat,
      ground.countOf mu
        ((blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content)
      = blockcount.countAt (monPool d k) mu := by
    intro mu
    rw [← blockcount.occ_eq_countOf mu
        (blockcount.exhaust d (monPool d k)),
      ← blockcount.countAt_exhaust d (monPool d k) hpack.1
        hpack.2.1 hpack.2.2.2 mu]
  have hrlD : ∀ mu, 0 < ground.countOf mu
      (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content)) →
      places.rowList (places.shapeOf mu) = mu := by
    intro mu hmu
    exact blockcount.exhaust_rowList_shapeOf d (monPool d k)
      hpack.1 hpack.2.1 hpack.2.2.2 mu
      (ground.mem_of_dedupL (ground.mem_of_countOf_pos _ _ hmu))
  have hreads : ∀ mu, 0 < ground.countOf mu
      (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content)) →
      (places.shapeOf mu).length = d
        ∧ places.degree (places.shapeOf mu) = k := by
    intro mu hmu
    match ground.mem_map_of blockcount.HVec.content _ mu
        (ground.mem_of_dedupL
          (ground.mem_of_countOf_pos _ _ hmu)) with
    | ⟨t, ht, htc⟩ =>
      obtain ⟨hw, hs, _⟩ := exhaust_reads d k hd t ht
      constructor
      · rw [places.length_shapeOf mu, ← htc]
        exact hw
      · show ground.sumNat
          (places.rowList (places.shapeOf mu)) = k
        rw [hrlD mu hmu, ← htc]
        exact hs
  have hcongr1 : ground.famFold Nat.add 0
      (fun mu => ground.countOf mu
          ((blockcount.exhaust d (monPool d k)).map
            blockcount.HVec.content)
        * elim.kernelDim (places.monomialsAt mu).length
          (units.stackedRaise mu))
      (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content))
      = ground.famFold Nat.add 0
        (fun mu => (blockcount.countAt (monPool d k) mu
            * elim.kernelDim (places.monomialsAt mu).length
              (units.stackedRaise mu))
          * ground.countOf (places.shapeOf mu)
            (places.allShapes d k))
        (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content)) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
    intro mu hmu
    obtain ⟨hshl, hdeg⟩ := hreads mu hmu
    have hsm : ground.countOf (places.shapeOf mu)
        (places.allShapes d k) = 1 := by
      refine Nat.le_antisymm (places.countOf_allShapes_le d k _) ?_
      refine ground.countOf_pos_of_mem ?_
      have hm := places.mem_allShapes d (places.shapeOf mu) hshl
      rw [hdeg] at hm
      exact hm
    rw [hcnt mu, hsm, Nat.mul_one]
  have hoff : ∀ mu, ground.countOf mu
      (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content)) = 0 →
      blockcount.countAt (monPool d k) mu
        * elim.kernelDim (places.monomialsAt mu).length
          (units.stackedRaise mu) = 0 := by
    intro mu hz
    match Nat.eq_zero_or_pos (ground.countOf mu
        ((blockcount.exhaust d (monPool d k)).map
          blockcount.HVec.content)) with
    | .inl h0 =>
      rw [← hcnt mu, h0, Nat.zero_mul]
    | .inr hp =>
      have hcc : 0 < ground.countOf mu
          (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
            blockcount.HVec.content)) :=
        ground.countOf_pos_of_mem
          (ground.mem_dedupL (ground.mem_of_countOf_pos mu _ hp))
      rw [hz] at hcc
      exact absurd hcc (Nat.lt_irrefl 0)
  have hcongr2 : ground.famFold Nat.add 0
      (fun s => blockcount.countAt (monPool d k)
          (places.rowList s)
        * elim.kernelDim
          (places.monomialsAt (places.rowList s)).length
          (units.stackedRaise (places.rowList s)))
      (places.allShapes d k)
      = ground.famFold Nat.add 0
        (fun s => pathsquare.pathCount s * pathsquare.pathCount s)
        (places.allShapes d k) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ _ ?_
    intro s hs
    have hmem := ground.mem_of_countOf_pos _ _ hs
    obtain ⟨hsl, hsd⟩ := places.allShapes_sound d k s hmem
    have hb := monPool_bridge d hd k s hsl hsd
    show blockcount.countAt (monPool d k) (places.rowList s)
        * elim.kernelDim
          (places.monomialsAt (places.rowList s)).length
          (units.stackedRaise (places.rowList s))
      = pathsquare.pathCount s * pathsquare.pathCount s
    have hr : blockcount.countPower s = pathsquare.pathCount s :=
      readAll s
    rw [hb, show elim.kernelDim
        (places.monomialsAt (places.rowList s)).length
        (units.stackedRaise (places.rowList s))
      = blockcount.countPower s from rfl, hr]
  rw [length_kersAt,
    (ground.famFold_map Nat.add 0
      (fun mu => elim.kernelDim (places.monomialsAt mu).length
        (units.stackedRaise mu))
      blockcount.HVec.content
      (blockcount.exhaust d (monPool d k))).symm,
    ground.famFold_partition _
      ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content)
      (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content))
      (fun x _ => ground.countOf_dedupL_le x _)
      (fun x hx => ground.mem_dedupL hx),
    hcongr1,
    fold_collapse
      (fun mu => blockcount.countAt (monPool d k) mu
        * elim.kernelDim (places.monomialsAt mu).length
          (units.stackedRaise mu))
      (ground.dedupL ((blockcount.exhaust d (monPool d k)).map
        blockcount.HVec.content))
      (fun mu => ground.countOf_dedupL_le mu _) hoff hrlD
      (places.allShapes d k),
    hcongr2]
  exact pathsquare.squareSum d k hk

/-- The invariants sit in the place permutations' span,
`lem:mixedinv`'s span clause: a family at the stated frames and
moved reads off the span would extend the independent flat forms
one past the count — the stacked top values map the extended list
to an independent list inside the raising kernels' joined span,
whose count is the factorial — against the exchange. -/
theorem perm_span (d k : Nat) (hk : k ≤ d)
    (T : List Nat → elim.Mat)
    (hsq : ∀ mu, 0 < ground.countOf mu (places.allContents d k) →
      elim.rowsLen (places.monomialsAt mu).length (T mu)
        ∧ (T mu).length = (places.monomialsAt mu).length)
    (hmv : ∀ mu, 0 < ground.countOf mu (places.allContents d k) →
      ∀ (i j : Nat), i < d → j < d → ¬ i = j →
      ∀ x : List ground.BPair,
        x.length = (places.monomialsAt mu).length →
      poly.oneValue
        (elim.matVec
          (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
          (elim.matVec (T mu) x))
        (elim.matVec (T (blockcount.moveAt i j mu))
          (elim.matVec
            (units.matUnitAt (blockcount.moveAt i j mu) mu i j)
            x))) :
    elim.spanRel (mixWidth d k) (permFlats d k) (flatF d k T) := by
  have hlenT : (flatF d k T).length = mixWidth d k := by
    show ((places.allContents d k).flatMap (fun mu =>
      (T mu).flatMap (fun r => r))).length = mixWidth d k
    exact length_flatF_go T (places.allContents d k)
      (fun mu hm => (hsq mu (ground.countOf_pos_of_mem hm)).1)
      (fun mu hm => (hsq mu (ground.countOf_pos_of_mem hm)).2)
  match d, hk with
  | 0, hk =>
    match k, hk with
    | 0, _ =>
      exact elim.span_of_full (mixWidth 0 0) (permFlats 0 0)
        (flatF 0 0 T) rfl (perm_indep 0 0 (Nat.le_refl 0)) hlenT
  | d' + 1, hk =>
    have hd : 0 < d' + 1 := Nat.succ_pos d'
    match (inferInstance : Decidable (elim.spanRel
        (mixWidth (d' + 1) k) (permFlats (d' + 1) k)
        (flatF (d' + 1) k T))) with
    | isTrue h => exact h
    | isFalse hns =>
      have hind0 := perm_indep (d' + 1) k hk
      have hext := elim.indep_extend (mixWidth (d' + 1) k)
        (permFlats (d' + 1) k) (flatF (d' + 1) k T)
        hind0.1 hlenT hind0 hns
      have hfl : (famList k T).map (flatF (d' + 1) k)
          = permFlats (d' + 1) k ++ [flatF (d' + 1) k T] := by
        show ((places.perms k).map permMat ++ [T]).map
          (flatF (d' + 1) k) = _
        rw [ground.map_append, ground.map_map]
        rfl
      have hindF : elim.indepRows (mixWidth (d' + 1) k)
          ((famList k T).map (flatF (d' + 1) k)) := by
        rw [hfl]
        exact hext
      have hstind := stack_indep (d' + 1) k hd T hsq hmv hindF
      have hocc : ∀ t ∈ blockcount.exhaust (d' + 1)
          (monPool (d' + 1) k),
          0 < ground.countOf t.content
            (places.allContents (d' + 1) k) :=
        fun t ht => (exhaust_reads (d' + 1) k hd t ht).2.2
      have hfr := fam_frames (d' + 1) k T hsq
      have hmo := fam_moved (d' + 1) k T hmv
      have hA : elim.rowsLen
          (stackW (blockcount.exhaust (d' + 1)
            (monPool (d' + 1) k)))
          ((famList k T).map
            (fun S => stackF S (blockcount.exhaust (d' + 1)
              (monPool (d' + 1) k)))) := by
        refine elim.rowsLen_map _ _ _ ?_
        intro S hS
        exact length_stackF S _
          (fun t ht => (hfr S hS t.content (hocc t ht)).2)
      have hmem : ∀ q, q < ((famList k T).map
          (fun S => stackF S (blockcount.exhaust (d' + 1)
            (monPool (d' + 1) k)))).length →
          elim.spanRel
            (stackW (blockcount.exhaust (d' + 1)
              (monPool (d' + 1) k)))
            (kersAt (blockcount.exhaust (d' + 1)
              (monPool (d' + 1) k)))
            (ground.getAt [] ((famList k T).map
              (fun S => stackF S (blockcount.exhaust (d' + 1)
                (monPool (d' + 1) k)))) q) := by
        intro q hq
        rw [ground.length_map] at hq
        rw [ground.getAt_map
          (fun _ => elim.nullMat 0 0) ([] : List ground.BPair)
          (fun S => stackF S (blockcount.exhaust (d' + 1)
            (monPool (d' + 1) k))) (famList k T) q hq]
        have hSm := ground.mem_getAt
          (fun _ => elim.nullMat 0 0) (famList k T) q hq
        refine stack_span _ _ ?_ ?_
        · exact fun t ht =>
            (hfr _ hSm t.content (hocc t ht)).2
        · exact val_top (d' + 1) k hd _ (hmo _ hSm)
      have hle := elim.span_count_le
        (stackW (blockcount.exhaust (d' + 1) (monPool (d' + 1) k)))
        ((famList k T).map
          (fun S => stackF S (blockcount.exhaust (d' + 1)
            (monPool (d' + 1) k))))
        (kersAt (blockcount.exhaust (d' + 1) (monPool (d' + 1) k)))
        hA (rowsLen_kersAt _) hstind hmem
      rw [ground.length_map, kers_count (d' + 1) k hd hk] at hle
      have hll : (famList k T).length
          = ground.factorial k + 1 := by
        show ((places.perms k).map permMat ++ [T]).length
          = ground.factorial k + 1
        rw [ground.length_append, ground.length_map,
          places.length_perms k]
        rfl
      rw [hll] at hle
      exact absurd hle (Nat.lt_irrefl (ground.factorial k))

end mixedinv
