import MassGap.Blockcount
import MassGap.Casimir
import MassGap.Fusiondata
import MassGap.Memberchar
/-!
`cor:steinberg` — the product's block counts by the alternant
pairs: at shapes `a`, `b`, `c`,
`N^c_{ab} + Σ_{σ odd} mult_a(ν_σ) = Σ_{σ even} mult_a(ν_σ)` at the
tie `ν_σ + σ(b + u) = c + u`, `σ` over the place permutations at
the swap grading and `u` the unit set's sorted display
(`con:places`).  The two graded sums are computations: the displays
`b + u` and `c + u` as counts (`places.display`, the beta-set's
sorted display at its `con:places` home), the tie's lattice
solution an occupancy read per permutation — the componentwise gap
of the target's display against the permuted one
(`ground.tieGap`), absent at any reversed entry
— and the multiplicity the block span's occupancy at the content,
`def:blockcount`'s carrier content-graded.  The count is the sums'
gap, the derived fast read, and the identity with
`def:blockcount`'s kernel-dimension count is the stated decidable
read `read`, its instances the check module's pins; the general
theorem `readAll` closes the display at any two shapes of one
width, the alternant layer's own reading (`thm:weylchar`), so the
fast read is the block count outright there (`count_fusion`,
the display withdrawn at the shared graded sum).

The member tier stands beneath it: `prodFam` the tensor product's
content data, `memberAt` the member display at a stated channel
top, and `memberRead` the member half's theorem — the display
derived from `thm:memberchar`'s per-key balance consumed twice,
the `b`-identity folded over the `a`-family at the withdrawn keys
and each channel's identity at the shifted key itself, the
exhaustion read splitting the product family over the channels
and the channel tops closing the display at the top's count.
-/

namespace steinberg
open ground places blockcount sertables assembly memberchar

/-- The two graded sums at the ties at a stated multiplicity read,
the even then the odd, one fold over the place permutations: the
factor's content read enters as the statement's own datum — the
block span's occupancy at the definitional route (`gradedSums`),
`lem:adjchar`'s content formula at the adjoint's. -/
def sumsWith (mult : List Nat → Nat) (d : Nat) (b c : Shape) :
    Nat × Nat :=
  let bu := display b
  let cu := display c
  (places.perms d).foldl
    (fun acc p =>
      match ground.tieGap cu (places.expo bu p) with
      | none => acc
      | some m =>
        if parity p then (acc.1, acc.2 + mult m)
        else (acc.1 + mult m, acc.2))
    (0, 0)

/-- The two graded sums at the definitional multiplicity, the block
span's content occupancy, the span read once. -/
def gradedSums (a b c : Shape) : Nat × Nat :=
  let span := blockcount.blockSpan a
  sumsWith (blockcount.occupancyAt span) a.length b c

/-- The fusion count as the sums' gap, the derived fast read. -/
def count (a b c : Shape) : Nat :=
  let s := gradedSums a b c
  s.1 - s.2

/-- `cor:steinberg`'s display at the definitional count:
`N^c_{ab} + Σ_odd = Σ_even`, decidable, the two sums read off the
one pair. -/
def read (a b c : Shape) : Prop :=
  let s := gradedSums a b c
  blockcount.fusionCount a b c + s.2 = s.1

instance (a b c : Shape) : Decidable (read a b c) :=
  inferInstanceAs (Decidable (_ = _))


/-! The general theorem's tier (`readAll`): `cor:steinberg`'s
display at any two shapes of one width.  The product
`a_u · ch_a · ch_b` reads twice at the monomial `x^{c+u}` — once as
`ch_a · a_{b+u}`, the `b`-alternant's shifted counts folded against
the `a`-block's occupancies, and once as the fused pool's channels,
`Σ_{c'} N^{c'}_{ab} a_{c'+u}` — and the two readings share the
product's own graded coefficient at the fused occupancy family, so
the shared pair cancels and the Kronecker read of the strictly
descending displays closes the display at the channel `c`.  The
tier's kit: the two graded sums as parity-guarded folds
(`sumsWith_split`), the fused occupancy at the first factor's gaps
(`occ_fusedAt`), the graded coefficient's family, pointwise, scale
and gap-shift reads, and the crossed fold at a factor's occupancy
family (`crossB_occ`). -/

/-- The pair-valued accumulating fold reads its two family folds,
each at its own seed. -/
private theorem foldl_pair (g h : List Nat → Nat) :
    ∀ (l : List (List Nat)) (a b : Nat),
      l.foldl (fun acc p => (acc.1 + g p, acc.2 + h p)) (a, b)
        = (a + ground.famFold Nat.add 0 g l,
           b + ground.famFold Nat.add 0 h l)
  | [], a, b => by
    show ((a, b) : Nat × Nat) = (a + 0, b + 0)
    rw [Nat.add_zero, Nat.add_zero]
  | p :: t, a, b => by
    show t.foldl (fun acc q => (acc.1 + g q, acc.2 + h q))
        (a + g p, b + h p)
      = (a + (g p + ground.famFold Nat.add 0 g t),
         b + (h p + ground.famFold Nat.add 0 h t))
    rw [foldl_pair g h t (a + g p) (b + h p),
      Nat.add_assoc a (g p) (ground.famFold Nat.add 0 g t),
      Nat.add_assoc b (h p) (ground.famFold Nat.add 0 h t)]

/-- The two graded sums as the parity-guarded folds: the
accumulating pass over the place permutations reads, side by side,
the even and odd folds of the tie's multiplicity at the permuted
display (`thm:weylchar`'s own spelling of `cor:steinberg`'s two
sums). -/
theorem sumsWith_split (mult : List Nat → Nat) (d : Nat)
    (b c : Shape) :
    sumsWith mult d b c
      = (ground.famFold Nat.add 0
          (fun p => if parity p = false then
            weylchar.multAtGap mult (display c)
              (places.expo (display b) p) else 0)
          (places.perms d),
        ground.famFold Nat.add 0
          (fun p => if parity p = true then
            weylchar.multAtGap mult (display c)
              (places.expo (display b) p) else 0)
          (places.perms d)) := by
  have hstep : ∀ (acc : Nat × Nat) (p : List Nat),
      (match ground.tieGap (display c)
          (p.map (ground.getAt 0 (display b))) with
        | none => acc
        | some m =>
          if parity p then (acc.1, acc.2 + mult m)
          else (acc.1 + mult m, acc.2))
      = (acc.1 + (if parity p = false then
            weylchar.multAtGap mult (display c)
              (places.expo (display b) p) else 0),
         acc.2 + (if parity p = true then
            weylchar.multAtGap mult (display c)
              (places.expo (display b) p) else 0)) := by
    intro acc p
    show (match ground.tieGap (display c)
        (p.map (ground.getAt 0 (display b))) with
      | none => acc
      | some m =>
        if parity p then (acc.1, acc.2 + mult m)
        else (acc.1 + mult m, acc.2))
      = (acc.1 + (if parity p = false then
          (match ground.tieGap (display c)
              (p.map (ground.getAt 0 (display b))) with
            | some nu => mult nu
            | none => 0) else 0),
         acc.2 + (if parity p = true then
          (match ground.tieGap (display c)
              (p.map (ground.getAt 0 (display b))) with
            | some nu => mult nu
            | none => 0) else 0))
    cases hg : ground.tieGap (display c)
        (p.map (ground.getAt 0 (display b))) with
    | none =>
      cases hp : parity p with
      | false =>
        show acc
          = (acc.1 + (if (false : Bool) = false then (0 : Nat) else 0),
             acc.2 + (if (false : Bool) = true then (0 : Nat) else 0))
        rw [if_pos (rfl : (false : Bool) = false),
          if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh),
          Nat.add_zero, Nat.add_zero]
      | true =>
        show acc
          = (acc.1 + (if (true : Bool) = false then (0 : Nat) else 0),
             acc.2 + (if (true : Bool) = true then (0 : Nat) else 0))
        rw [if_neg (fun hh : (true : Bool) = false => Bool.noConfusion hh),
          if_pos (rfl : (true : Bool) = true),
          Nat.add_zero, Nat.add_zero]
    | some m =>
      cases hp : parity p with
      | false =>
        show (acc.1 + mult m, acc.2)
          = (acc.1 + (if (false : Bool) = false then mult m else 0),
             acc.2 + (if (false : Bool) = true then mult m else 0))
        rw [if_pos (rfl : (false : Bool) = false),
          if_neg (fun hh : (false : Bool) = true => Bool.noConfusion hh),
          Nat.add_zero]
      | true =>
        show (acc.1, acc.2 + mult m)
          = (acc.1 + (if (true : Bool) = false then mult m else 0),
             acc.2 + (if (true : Bool) = true then mult m else 0))
        rw [if_neg (fun hh : (true : Bool) = false => Bool.noConfusion hh),
          if_pos (rfl : (true : Bool) = true),
          Nat.add_zero]
  show (monomialsAt (List.replicate d 1)).foldl
      (fun acc p =>
        match ground.tieGap (display c)
            (p.map (ground.getAt 0 (display b))) with
        | none => acc
        | some m =>
          if parity p then (acc.1, acc.2 + mult m)
          else (acc.1 + mult m, acc.2))
      (0, 0)
    = (ground.famFold Nat.add 0
        (fun p => if parity p = false then
          weylchar.multAtGap mult (display c)
            (places.expo (display b) p) else 0)
        (monomialsAt (List.replicate d 1)),
      ground.famFold Nat.add 0
        (fun p => if parity p = true then
          weylchar.multAtGap mult (display c)
            (places.expo (display b) p) else 0)
        (monomialsAt (List.replicate d 1)))
  rw [ground.foldl_congr _ _ hstep (monomialsAt (List.replicate d 1)) (0, 0),
    foldl_pair _ _ (monomialsAt (List.replicate d 1)) 0 0,
    Nat.zero_add, Nat.zero_add]

/-- The fused pool's occupancy at a content: each member of the
first factor withdraws its own content from the key and the second
factor's occupancy at the gap is that member's contribution, the
contents adding over the tensor (`lem:blockcount`(iii)'s fused
carrier at matched widths). -/
private theorem occ_fusedAt (d : Nat) (A B : List HVec)
    (hwidA : ∀ v ∈ A, v.content.length = d)
    (hwidB : ∀ w ∈ B, w.content.length = d) :
    ∀ mu : List Nat,
      occ mu (fusedAt A B)
        = ground.famFold Nat.add 0
            (fun v => match ground.tieGap mu v.content with
              | some w => occ w B
              | none => 0) A := by
  intro mu
  have hten : ∀ v : HVec, v.content.length = d →
      ∀ B' : List HVec, (∀ w ∈ B', w.content.length = d) →
        occ mu (B'.map (tensorH v))
          = match ground.tieGap mu v.content with
            | some w => occ w B'
            | none => 0 := by
    intro v hv
    cases hg : ground.tieGap mu v.content with
    | none =>
      intro B'
      induction B' with
      | nil => intro _; rfl
      | cons x t ih =>
        intro hB'
        have hxd : x.content.length = d := hB' x (List.Mem.head t)
        have hzt : occ mu (t.map (tensorH v)) = 0 :=
          ih (fun y hy => hB' y (List.Mem.tail x hy))
        show (if (tensorH v x).content = mu then 1 else 0)
            + occ mu (t.map (tensorH v)) = 0
        rw [if_neg (fun he : (tensorH v x).content = mu => by
            have hz : List.zipWith (fun a b => a + b) v.content x.content
                = mu := he
            have hzl : (List.zipWith (fun a b => a + b)
                v.content x.content).length = d :=
              ground.length_zipWith (fun a b => a + b) v.content x.content d
                hv hxd
            have hml : mu.length = d := by rw [← hz]; exact hzl
            have hcon : ground.tieGap mu v.content = some x.content :=
              ground.tieGap_make mu v.content x.content
                (by rw [hml]; exact hxd) (by rw [hml]; exact hv)
                (fun i hi => by
                  have hid : i < d := by rw [← hml]; exact hi
                  rw [← hz, ground.getAt_zipWith 0 0 0 (fun a b => a + b)
                      v.content x.content i (by rw [hv]; exact hid)
                      (by rw [hxd]; exact hid),
                    Nat.add_comm (ground.getAt 0 x.content i)
                      (ground.getAt 0 v.content i)])
            rw [hg] at hcon
            exact nomatch hcon),
          Nat.zero_add, hzt]
    | some w =>
      obtain ⟨hwl, hvl, hent⟩ := ground.tieGap_reads mu v.content w hg
      have hml : mu.length = d := by rw [← hvl]; exact hv
      intro B'
      induction B' with
      | nil => intro _; rfl
      | cons x t ih =>
        intro hB'
        have hxd : x.content.length = d := hB' x (List.Mem.head t)
        have iht : occ mu (t.map (tensorH v)) = occ w t :=
          ih (fun y hy => hB' y (List.Mem.tail x hy))
        have hfwd : (tensorH v x).content = mu → x.content = w := by
          intro he
          have hz : List.zipWith (fun a b => a + b) v.content x.content
              = mu := he
          refine ground.getAt_ext 0 x.content w
            (hxd.trans (hwl.trans hml).symm) ?_
          intro i hi
          have hid : i < d := by rw [← hxd]; exact hi
          have h2 := hent i (by rw [hml]; exact hid)
          rw [← hz, ground.getAt_zipWith 0 0 0 (fun a b => a + b)
              v.content x.content i (by rw [hv]; exact hid)
              (by rw [hxd]; exact hid),
            Nat.add_comm (ground.getAt 0 w i)
              (ground.getAt 0 v.content i)] at h2
          exact (ground.addCancelL _ h2).symm
        have hbwd : x.content = w → (tensorH v x).content = mu := by
          intro hc
          show List.zipWith (fun a b => a + b) v.content x.content = mu
          have hzl : (List.zipWith (fun a b => a + b)
              v.content x.content).length = d :=
            ground.length_zipWith (fun a b => a + b) v.content x.content d
              hv hxd
          refine ground.getAt_ext 0 _ mu (hzl.trans hml.symm) ?_
          intro i hi
          have hid : i < d := by rw [← hzl]; exact hi
          rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) v.content x.content i
              (by rw [hv]; exact hid) (by rw [hxd]; exact hid), hc,
            Nat.add_comm (ground.getAt 0 v.content i)
              (ground.getAt 0 w i)]
          exact hent i (by rw [hml]; exact hid)
        show (if (tensorH v x).content = mu then 1 else 0)
            + occ mu (t.map (tensorH v))
          = (if x.content = w then 1 else 0) + occ w t
        by_cases hc : x.content = w
        · rw [if_pos hc, if_pos (hbwd hc), iht]
        · rw [if_neg hc, if_neg (fun he => hc (hfwd he)), iht]
  rw [occ_eq_countOf mu (fusedAt A B)]
  show ground.countOf mu
      ((A.flatMap (fun v => B.map (tensorH v))).map HVec.content) = _
  rw [ground.map_flatMap (fun v => B.map (tensorH v)) HVec.content A,
    ground.countOf_flatMap mu
      (fun v => (B.map (tensorH v)).map HVec.content) A]
  refine ground.famFold_congr_members Nat.add 0 _ _ A (fun v hvm => ?_)
  rw [← occ_eq_countOf mu (B.map (tensorH v))]
  exact hten v (hwidA v (ground.mem_of_countOf_pos v A hvm)) B hwidB

/-- The tie's composition: a solution withdrawn in two steps
solves the one tie at the joined gaps, the intermediate key the two
withdrawals' own sum. -/
private theorem tieGap_chain {y e m z w : List Nat}
    (h1 : ground.tieGap y e = some m)
    (h2 : ground.tieGap m z = some w) :
    ∃ yv, ground.tieGap y z = some yv
      ∧ ground.tieGap yv e = some w := by
  obtain ⟨hml, hel, hent1⟩ := ground.tieGap_reads y e m h1
  obtain ⟨hwl, hzl, hent2⟩ := ground.tieGap_reads m z w h2
  have hwy : w.length = y.length := hwl.trans hml
  have hzy : z.length = y.length := hzl.trans hml
  have hyvl : (List.zipWith (fun a b => a + b) w e).length = y.length :=
    ground.length_zipWith (fun a b => a + b) w e y.length hwy hel
  refine ⟨List.zipWith (fun a b => a + b) w e, ?_, ?_⟩
  · refine ground.tieGap_make y z _ hyvl hzy (fun i hi => ?_)
    rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) w e i
        (by rw [hwy]; exact hi) (by rw [hel]; exact hi),
      Nat.add_assoc (ground.getAt 0 w i) (ground.getAt 0 e i)
        (ground.getAt 0 z i),
      Nat.add_comm (ground.getAt 0 e i) (ground.getAt 0 z i),
      ← Nat.add_assoc (ground.getAt 0 w i) (ground.getAt 0 z i)
        (ground.getAt 0 e i),
      hent2 i (by rw [hml]; exact hi)]
    exact hent1 i hi
  · refine ground.tieGap_make _ e w (hwy.trans hyvl.symm)
      (hel.trans hyvl.symm) (fun i hi => ?_)
    have hiy : i < y.length := by rw [← hyvl]; exact hi
    rw [ground.getAt_zipWith 0 0 0 (fun a b => a + b) w e i
      (by rw [hwy]; exact hiy) (by rw [hel]; exact hiy)]

/-- The product's graded coefficient at a further withdrawal: a
multiplicity read at a fixed gap moves the key by that gap — the
coefficient at the moved key, the count's unit where the move is
absent. -/
private theorem prodCount_gapMult (mult : List Nat → Nat)
    (z : List Nat) (d : Nat) (y : List Nat) (side : Bool) :
    weylchar.prodCount
        (fun mu => match ground.tieGap mu z with
          | some w => mult w
          | none => 0) d y side
      = match ground.tieGap y z with
        | some yv => weylchar.prodCount mult d yv side
        | none => 0 := by
  show ground.famFold Nat.add 0
      (fun p => if parity p = side then
        (match ground.tieGap y (places.expo (unitDisp d) p) with
          | some m => (match ground.tieGap m z with
              | some w => mult w
              | none => 0)
          | none => 0) else 0)
      (places.perms d)
    = (match ground.tieGap y z with
      | some yv => weylchar.prodCount mult d yv side
      | none => 0)
  cases hz : ground.tieGap y z with
  | none =>
    show ground.famFold Nat.add 0
        (fun p => if parity p = side then
          (match ground.tieGap y (places.expo (unitDisp d) p) with
            | some m => (match ground.tieGap m z with
                | some w => mult w
                | none => 0)
            | none => 0) else 0)
        (places.perms d) = 0
    refine ground.famFold_zero _ (fun p => ?_) (places.perms d)
    by_cases hs : parity p = side
    · rw [if_pos hs]
      cases hm : ground.tieGap y (places.expo (unitDisp d) p) with
      | none => rfl
      | some m =>
        show (match ground.tieGap m z with
            | some w => mult w
            | none => 0) = 0
        cases hmz : ground.tieGap m z with
        | none => rfl
        | some w =>
          obtain ⟨yv, hyv, _⟩ := tieGap_chain hm hmz
          exact nomatch hyv.symm.trans hz
    · rw [if_neg hs]
  | some yv =>
    show ground.famFold Nat.add 0
        (fun p => if parity p = side then
          (match ground.tieGap y (places.expo (unitDisp d) p) with
            | some m => (match ground.tieGap m z with
                | some w => mult w
                | none => 0)
            | none => 0) else 0)
        (places.perms d)
      = ground.famFold Nat.add 0
        (fun p => if parity p = side then
          (match ground.tieGap yv (places.expo (unitDisp d) p) with
            | some w => mult w
            | none => 0) else 0)
        (places.perms d)
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun p => ?_)
      (places.perms d)
    by_cases hs : parity p = side
    · rw [if_pos hs, if_pos hs]
      cases hw : ground.tieGap yv (places.expo (unitDisp d) p) with
      | none =>
        show (match ground.tieGap y (places.expo (unitDisp d) p) with
            | some m => (match ground.tieGap m z with
                | some w => mult w
                | none => 0)
            | none => 0) = 0
        cases hm : ground.tieGap y (places.expo (unitDisp d) p) with
        | none => rfl
        | some m =>
          show (match ground.tieGap m z with
              | some w => mult w
              | none => 0) = 0
          cases hmz : ground.tieGap m z with
          | none => rfl
          | some w =>
            obtain ⟨yv', hyv', hyve⟩ := tieGap_chain hm hmz
            have hyy : yv' = yv := Option.some.inj (hyv'.symm.trans hz)
            rw [hyy] at hyve
            exact nomatch hyve.symm.trans hw
      | some w =>
        obtain ⟨m, hm, hmz⟩ := tieGap_chain hz hw
        cases hm2 : ground.tieGap y (places.expo (unitDisp d) p) with
        | none => exact nomatch hm.symm.trans hm2
        | some m2 =>
          have hmm : m2 = m := Option.some.inj (hm2.symm.trans hm)
          show (match ground.tieGap m2 z with
              | some w' => mult w'
              | none => 0) = mult w
          cases hmz2 : ground.tieGap m2 z with
          | none =>
            rw [hmm] at hmz2
            exact nomatch hmz.symm.trans hmz2
          | some w2 =>
            show mult w2 = mult w
            rw [hmm] at hmz2
            rw [Option.some.inj (hmz2.symm.trans hmz)]
    · rw [if_neg hs, if_neg hs]

/-- The content occupancy as its indicator's fold over the
pool. -/
private theorem occ_famFold (m : List Nat) (A : List HVec) :
    occ m A = ground.famFold Nat.add 0
      (fun v => if v.content = m then 1 else 0) A := by
  rw [occ_eq_countOf m A,
    ground.countOf_fold m (A.map HVec.content),
    ground.famFold_map Nat.add 0
      (fun x => if m = x then (1 : Nat) else 0) HVec.content A]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun v => ?_) A
  by_cases hc : v.content = m
  · rw [if_pos hc.symm, if_pos hc]
  · rw [if_neg (fun hh => hc hh.symm), if_neg hc]

/-- The crossed read at a stated occupancy family: the graded fold
of the tie's occupancy multiplicity against a display is the
family's members' own shifted alternant counts, each member's
content withdrawn from the key and the count's unit where the
withdrawal is absent. -/
private theorem crossB_occ (A : List HVec) (d : Nat)
    (bu y : List Nat) (side : Bool) :
    ground.famFold Nat.add 0
        (fun p => if parity p = side then
          weylchar.multAtGap (fun m => occ m A) y
            (places.expo bu p) else 0)
        (places.perms d)
      = ground.famFold Nat.add 0
          (fun v => match ground.tieGap y v.content with
            | some w => weylchar.sideCount d bu w side
            | none => 0) A := by
  have hstep : ∀ p : List Nat,
      (if parity p = side then
        weylchar.multAtGap (fun m => occ m A) y (places.expo bu p)
        else 0)
      = ground.famFold Nat.add 0
        (fun v => if parity p = side then
          (match ground.tieGap y (places.expo bu p) with
            | some nu => if v.content = nu then 1 else 0
            | none => 0) else 0) A := by
    intro p
    by_cases hs : parity p = side
    · show (if parity p = side then
          (match ground.tieGap y (places.expo bu p) with
            | some nu => occ nu A
            | none => 0) else 0)
        = ground.famFold Nat.add 0
          (fun v => if parity p = side then
            (match ground.tieGap y (places.expo bu p) with
              | some nu => if v.content = nu then 1 else 0
              | none => 0) else 0) A
      rw [if_pos hs]
      cases hg : ground.tieGap y (places.expo bu p) with
      | none =>
        show (0 : Nat) = ground.famFold Nat.add 0
          (fun _ => if parity p = side then (0 : Nat) else 0) A
        exact (ground.famFold_zero _ (fun _ => if_pos hs) A).symm
      | some nu =>
        show occ nu A = ground.famFold Nat.add 0
          (fun v => if parity p = side then
            (if v.content = nu then 1 else 0) else 0) A
        rw [occ_famFold nu A]
        exact ground.famFold_congr_all Nat.add 0 _ _
          (fun _ => (if_pos hs).symm) A
    · show (if parity p = side then
          weylchar.multAtGap (fun m => occ m A) y (places.expo bu p)
          else 0)
        = ground.famFold Nat.add 0
          (fun v => if parity p = side then
            (match ground.tieGap y (places.expo bu p) with
              | some nu => if v.content = nu then 1 else 0
              | none => 0) else 0) A
      rw [if_neg hs]
      exact (ground.famFold_zero _ (fun _ => if_neg hs) A).symm
  rw [ground.famFold_congr_all Nat.add 0 _ _ hstep (places.perms d),
    ground.famFold_swap
      (fun p v => if parity p = side then
        (match ground.tieGap y (places.expo bu p) with
          | some nu => if v.content = nu then 1 else 0
          | none => 0) else 0) (places.perms d) A]
  refine ground.famFold_congr_all Nat.add 0 _ _ (fun v => ?_) A
  cases hv : ground.tieGap y v.content with
  | none =>
    show ground.famFold Nat.add 0
        (fun p => if parity p = side then
          (match ground.tieGap y (places.expo bu p) with
            | some nu => if v.content = nu then 1 else 0
            | none => 0) else 0) (places.perms d) = 0
    refine ground.famFold_zero _ (fun p => ?_) (places.perms d)
    by_cases hs : parity p = side
    · rw [if_pos hs]
      cases hg : ground.tieGap y (places.expo bu p) with
      | none => rfl
      | some nu =>
        show (if v.content = nu then 1 else 0) = 0
        refine if_neg (fun hc => ?_)
        obtain ⟨hnl, hel, hent2⟩ :=
          ground.tieGap_reads y (places.expo bu p) nu hg
        have hmk : ground.tieGap y v.content
            = some (places.expo bu p) :=
          ground.tieGap_make y v.content (places.expo bu p) hel
            (by rw [hc]; exact hnl)
            (fun i hi => by
              rw [hc, Nat.add_comm (ground.getAt 0 (places.expo bu p) i)
                (ground.getAt 0 nu i)]
              exact hent2 i hi)
        exact nomatch hmk.symm.trans hv
    · rw [if_neg hs]
  | some w =>
    obtain ⟨hwl, hvl, hent⟩ := ground.tieGap_reads y v.content w hv
    show ground.famFold Nat.add 0
        (fun p => if parity p = side then
          (match ground.tieGap y (places.expo bu p) with
            | some nu => if v.content = nu then 1 else 0
            | none => 0) else 0) (places.perms d)
      = ground.famFold Nat.add 0
        (fun p => if parity p = side then
          (if places.expo bu p = w then 1 else 0) else 0)
        (places.perms d)
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun p => ?_)
      (places.perms d)
    by_cases hs : parity p = side
    · rw [if_pos hs, if_pos hs]
      cases hg : ground.tieGap y (places.expo bu p) with
      | none =>
        show (0 : Nat) = if places.expo bu p = w then 1 else 0
        refine (if_neg (fun he : places.expo bu p = w => ?_)).symm
        have hmk : ground.tieGap y w = some v.content :=
          ground.tieGap_make y w v.content hvl hwl (fun i hi => by
            rw [Nat.add_comm (ground.getAt 0 v.content i)
              (ground.getAt 0 w i)]
            exact hent i hi)
        rw [he] at hg
        exact nomatch hmk.symm.trans hg
      | some nu =>
        obtain ⟨hnl, hel, hent2⟩ :=
          ground.tieGap_reads y (places.expo bu p) nu hg
        have hfwd : v.content = nu → places.expo bu p = w := by
          intro hc
          refine ground.getAt_ext 0 _ w (hel.trans hwl.symm) ?_
          intro i hi
          have hiy : i < y.length := by rw [← hel]; exact hi
          have e1 := hent2 i hiy
          have e2 := hent i hiy
          rw [hc, Nat.add_comm (ground.getAt 0 w i)
            (ground.getAt 0 nu i)] at e2
          exact ground.addCancelL _ (e1.trans e2.symm)
        have hbwd : places.expo bu p = w → v.content = nu := by
          intro hc
          refine ground.getAt_ext 0 _ nu (hvl.trans hnl.symm) ?_
          intro i hi
          have hiy : i < y.length := by rw [← hvl]; exact hi
          have e1 := hent2 i hiy
          have e2 := hent i hiy
          rw [hc, Nat.add_comm (ground.getAt 0 nu i)
            (ground.getAt 0 w i)] at e1
          exact (ground.addCancelL _ (e1.trans e2.symm)).symm
        show (if v.content = nu then 1 else 0)
          = if places.expo bu p = w then 1 else 0
        by_cases hc : v.content = nu
        · rw [if_pos hc, if_pos (hfwd hc)]
        · rw [if_neg hc, if_neg (fun he => hc (hbwd he))]
    · rw [if_neg hs, if_neg hs]


/-- The Kronecker read at the sorted displays: the alternant's
graded count at a dominant list's own shape against a stated
shape's display reads one exactly at the even side of the matching
row list and the count's unit everywhere else — both displays
descend strictly (`places.display_desc`), so the sorted spelling's
uniqueness parts them (`weylchar.sideCount_desc_self`,
`weylchar.sideCount_desc_ne`), and the displays agree exactly at
the row lists' own agreement, the unit display cancelling
entrywise. -/
private theorem sideCount_shapeOf (d : Nat) (c : Shape)
    (hcd : c.length = d) (nu : List Nat)
    (hnu : rowList (shapeOf nu) = nu) (hnd : nu.length = d)
    (side : Bool) :
    weylchar.sideCount d (display (shapeOf nu)) (display c) side
      = if nu = rowList c ∧ side = false then 1 else 0 := by
  have hsl : (shapeOf nu).length = d :=
    (places.length_shapeOf nu).trans hnd
  have hrl : (rowList c).length = d :=
    (places.length_rowList c).trans hcd
  have hud : (unitDisp d).length = d :=
    (places.length_display (List.replicate d 0)).trans
      (ground.length_replicate 0 d)
  have hdn : display (shapeOf nu)
      = List.zipWith (fun l u => l + u) nu (unitDisp d) := by
    rw [weylchar.display_zip (shapeOf nu), hnu, hsl]
  have hdc : display c
      = List.zipWith (fun l u => l + u) (rowList c) (unitDisp d) := by
    rw [weylchar.display_zip c, hcd]
  have hiff : display (shapeOf nu) = display c ↔ nu = rowList c := by
    constructor
    · intro he
      rw [hdn, hdc] at he
      refine ground.getAt_ext 0 nu (rowList c) (hnd.trans hrl.symm) ?_
      intro i hi
      have hid : i < d := by rw [← hnd]; exact hi
      have h1 : ground.getAt 0 nu i + ground.getAt 0 (unitDisp d) i
          = ground.getAt 0 (rowList c) i
            + ground.getAt 0 (unitDisp d) i := by
        rw [← ground.getAt_zipWith 0 0 0 (fun l u => l + u) nu (unitDisp d) i
            (by rw [hnd]; exact hid) (by rw [hud]; exact hid),
          ← ground.getAt_zipWith 0 0 0 (fun l u => l + u) (rowList c)
            (unitDisp d) i (by rw [hrl]; exact hid)
            (by rw [hud]; exact hid), he]
      exact ground.addCancelR _ h1
    · intro he
      rw [hdn, hdc, he]
  by_cases he : display (shapeOf nu) = display c
  · have hlc : (display c).length = d :=
      (places.length_display c).trans hcd
    obtain ⟨h0, h1⟩ := weylchar.sideCount_desc_self hlc
      (fun i hi => places.display_desc c i (by rw [hcd]; exact hi))
    rw [he]
    cases side with
    | false => rw [h0, if_pos ⟨hiff.mp he, rfl⟩]
    | true => rw [h1, if_neg (fun hh => Bool.noConfusion hh.2)]
  · rw [weylchar.sideCount_desc_ne
        ((places.length_display (shapeOf nu)).trans hsl)
        ((places.length_display c).trans hcd)
        (fun i hi =>
          places.display_desc (shapeOf nu) i (by rw [hsl]; exact hi))
        (fun i hi => places.display_desc c i (by rw [hcd]; exact hi))
        (fun hq => he hq.symm) side,
      if_neg (fun hh => he (hiff.mpr hh.1))]

/-- The product's graded coefficient at the fused occupancy family,
read over the channels (`cor:steinberg`'s second reading): the
fused pool's graded dimension is its channels' counts against the
channel blocks' occupancies (`blockcount.gradedDim_countAt` at
`blockcount.dimAt_occ`), each channel contributes `thm:weylchar`'s
identity at its own shape, and the channels' shifted alternant
counts collapse at the Kronecker read — the count's unit at every
channel but `c`'s own row list, whose weight is the fusion count
(`blockcount.fusionCount_countAt`). -/
private theorem middle_channels (a b c : Shape)
    (hba : b.length = a.length) (hca : c.length = a.length) :
    weylchar.prodCount
        (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
        a.length (display c) false
      = weylchar.prodCount
          (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
          a.length (display c) true
        + fusionCount a b c := by
  obtain ⟨hszP, hwidP, hclP, hiP⟩ := fusedSpan_pack a b hba
  have hrlS := exhaust_rowList_shapeOf a.length
    (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP
  have hwd : ∀ nu ∈ ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content),
      nu.length = a.length := by
    intro nu hnu
    exact exhaust_width a.length
      (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP nu
      (ground.mem_of_dedupL hnu)
  -- the coefficient over the channels
  have hsplit : ∀ side : Bool,
      weylchar.prodCount
          (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
          a.length (display c) side
        = ground.famFold Nat.add 0
          (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
            * weylchar.prodCount
              (fun mu => occ mu (blockSpan (shapeOf nu)))
              a.length (display c) side)
          (ground.dedupL ((exhaust a.length
            (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) := by
    intro side
    rw [weylchar.prodCount_congr
        (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
        (fun mu => ground.famFold Nat.add 0
          (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
            * occ mu (blockSpan (shapeOf nu)))
          (ground.dedupL ((exhaust a.length
            (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)))
        (fun mu => (dimAt_occ
            (fusedAt (blockSpan a) (blockSpan b)) hiP mu).symm.trans
          (gradedDim_countAt a.length
            (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP mu))
        a.length (display c) side,
      weylchar.prodCount_famFold
        (fun nu mu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * occ mu (blockSpan (shapeOf nu)))
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
        a.length (display c) side]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun nu => weylchar.prodCount_scale
        (countAt (fusedAt (blockSpan a) (blockSpan b)) nu)
        (fun mu => occ mu (blockSpan (shapeOf nu)))
        a.length (display c) side)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
  -- the channel's own identity at its shape
  have hidn : ∀ nu ∈ ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content),
      weylchar.prodCount (fun mu => occ mu (blockSpan (shapeOf nu)))
          a.length (display c) false
        + weylchar.sideCount a.length (display (shapeOf nu))
            (display c) true
      = weylchar.prodCount (fun mu => occ mu (blockSpan (shapeOf nu)))
          a.length (display c) true
        + weylchar.sideCount a.length (display (shapeOf nu))
            (display c) false := by
    intro nu hnu
    have hsl : (shapeOf nu).length = a.length :=
      (places.length_shapeOf nu).trans (hwd nu hnu)
    have hb' : weylchar.prodCount
          (fun chi => ground.countOf chi
            ((blockSpan (shapeOf nu)).map HVec.content))
          (shapeOf nu).length (display c) false
        + weylchar.sideCount (shapeOf nu).length
            (display (shapeOf nu)) (display c) true
      = weylchar.prodCount
          (fun chi => ground.countOf chi
            ((blockSpan (shapeOf nu)).map HVec.content))
          (shapeOf nu).length (display c) true
        + weylchar.sideCount (shapeOf nu).length
            (display (shapeOf nu)) (display c) false :=
      weylchar.identityRead (shapeOf nu)
        ((blockSpan (shapeOf nu)).map HVec.content)
        (casimir.recRead_def (shapeOf nu))
        (strings.symRead_def (shapeOf nu))
        (lowerspan.supportRead_def (shapeOf nu))
        (lowerspan.topRead_def (shapeOf nu)) (display c)
    rw [hsl, weylchar.prodCount_congr
        (fun chi => ground.countOf chi
          ((blockSpan (shapeOf nu)).map HVec.content))
        (fun mu => occ mu (blockSpan (shapeOf nu)))
        (fun mu => (occ_eq_countOf mu
          (blockSpan (shapeOf nu))).symm)
        a.length (display c) false,
      weylchar.prodCount_congr
        (fun chi => ground.countOf chi
          ((blockSpan (shapeOf nu)).map HVec.content))
        (fun mu => occ mu (blockSpan (shapeOf nu)))
        (fun mu => (occ_eq_countOf mu
          (blockSpan (shapeOf nu))).symm)
        a.length (display c) true] at hb'
    exact hb'
  -- the channels' shifted alternant counts at the Kronecker read
  have hkron : ∀ nu ∈ ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content),
      ∀ side : Bool,
      weylchar.sideCount a.length (display (shapeOf nu))
          (display c) side
        = if nu = rowList c ∧ side = false then 1 else 0 :=
    fun nu hnu side => sideCount_shapeOf a.length c hca nu
      (hrlS nu (ground.mem_of_dedupL hnu)) (hwd nu hnu) side
  -- the weighted identities summed over the channels
  have hfold : ground.famFold Nat.add 0
      (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.prodCount
            (fun mu => occ mu (blockSpan (shapeOf nu)))
            a.length (display c) false
        + countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.sideCount a.length (display (shapeOf nu))
            (display c) true)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
    = ground.famFold Nat.add 0
      (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.prodCount
            (fun mu => occ mu (blockSpan (shapeOf nu)))
            a.length (display c) true
        + countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.sideCount a.length (display (shapeOf nu))
            (display c) false)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) := by
    refine ground.famFold_congr_members Nat.add 0 _ _ _ (fun nu hnu => ?_)
    rw [← Nat.left_distrib, ← Nat.left_distrib,
      hidn nu (ground.mem_of_countOf_pos nu _ hnu)]
  -- the odd channel counts vanish
  have hzero : ground.famFold Nat.add 0
      (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
        * weylchar.sideCount a.length (display (shapeOf nu))
          (display c) true)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) = 0 := by
    refine ground.famFold_congr_members Nat.add 0 _ (fun _ => (0 : Nat)) _
      (fun nu hnu => ?_) |>.trans
      (ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl) _)
    rw [hkron nu (ground.mem_of_countOf_pos nu _ hnu) true,
      if_neg (fun hh => Bool.noConfusion hh.2), Nat.mul_zero]
  -- the even channel counts collapse at the stated channel
  have heven : ground.famFold Nat.add 0
      (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
        * weylchar.sideCount a.length (display (shapeOf nu))
          (display c) false)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
      = fusionCount a b c := by
    have hpick : ground.famFold Nat.add 0
        (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.sideCount a.length (display (shapeOf nu))
            (display c) false)
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
        = ground.famFold Nat.add 0
          (fun nu => if nu = rowList c then
            countAt (fusedAt (blockSpan a) (blockSpan b)) nu else 0)
          (ground.dedupL ((exhaust a.length
            (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) := by
      refine ground.famFold_congr_members Nat.add 0 _ _ _ (fun nu hnu => ?_)
      rw [hkron nu (ground.mem_of_countOf_pos nu _ hnu) false]
      by_cases hc : nu = rowList c
      · rw [if_pos hc, if_pos ⟨hc, rfl⟩, Nat.mul_one]
      · rw [if_neg hc, if_neg (fun hh => hc hh.1), Nat.mul_zero]
    rw [hpick, fusionCount_countAt a b c hba]
    match Nat.eq_zero_or_pos (ground.countOf (rowList c)
      (ground.dedupL ((exhaust a.length
        (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))) with
    | Or.inr hp =>
      rw [ground.famFold_pick
        (countAt (fusedAt (blockSpan a) (blockSpan b))) (rowList c) _
        (Nat.le_antisymm (ground.countOf_dedupL_le (rowList c) _) hp)]
    | Or.inl h0 =>
      rw [ground.famFold_pickZero
        (countAt (fusedAt (blockSpan a) (blockSpan b))) (rowList c) _ h0,
        countAt_exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b)) hszP hwidP hclP (rowList c),
        occ_eq_countOf (rowList c)
          (exhaust a.length (fusedAt (blockSpan a) (blockSpan b)))]
      match Nat.eq_zero_or_pos (ground.countOf (rowList c)
        ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) with
      | Or.inl hz => exact hz.symm
      | Or.inr hq =>
        exact absurd (ground.countOf_pos_of_mem
          (ground.mem_dedupL (ground.mem_of_countOf_pos (rowList c) _ hq)))
          (by rw [h0]; exact Nat.lt_irrefl 0)
  have hbal : ground.famFold Nat.add 0
        (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.prodCount
            (fun mu => occ mu (blockSpan (shapeOf nu)))
            a.length (display c) false)
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
      + ground.famFold Nat.add 0
        (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.sideCount a.length (display (shapeOf nu))
            (display c) true)
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
    = ground.famFold Nat.add 0
        (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.prodCount
            (fun mu => occ mu (blockSpan (shapeOf nu)))
            a.length (display c) true)
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content))
      + ground.famFold Nat.add 0
        (fun nu => countAt (fusedAt (blockSpan a) (blockSpan b)) nu
          * weylchar.sideCount a.length (display (shapeOf nu))
            (display c) false)
        (ground.dedupL ((exhaust a.length
          (fusedAt (blockSpan a) (blockSpan b))).map HVec.content)) := by
    rw [← ground.famFold_add_split, ← ground.famFold_add_split]
    exact hfold
  rw [hzero, Nat.add_zero] at hbal
  rw [hsplit false, hsplit true, ← heven]
  exact hbal


/-- The product's graded coefficient at the fused occupancy family,
read as the `a`-block against the shifted `b`-alternant
(`cor:steinberg`'s first reading): the fused occupancy at a key
splits over the `a`-block's members at their own withdrawn contents
(`occ_fusedAt`), so the coefficient is the `b`-block's coefficients
at the withdrawn keys (`prodCount_gapMult`); at each member
`thm:weylchar`'s identity at `b` balances that coefficient against
the `b`-alternant's shifted counts, and those counts are the two
graded sums themselves (`crossB_occ` at `sumsWith_split`). -/
private theorem middle_factor (a b c : Shape)
    (hba : b.length = a.length) :
    weylchar.prodCount
        (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
        a.length (display c) false
        + (gradedSums a b c).2
      = weylchar.prodCount
          (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
          a.length (display c) true
        + (gradedSums a b c).1 := by
  have hmult : ∀ y e : List Nat,
      weylchar.multAtGap (occupancyAt (blockSpan a)) y e
        = weylchar.multAtGap (fun m => occ m (blockSpan a)) y e := by
    intro y e
    show (match ground.tieGap y e with
        | some nu => occupancyAt (blockSpan a) nu
        | none => 0)
      = (match ground.tieGap y e with
        | some nu => occ nu (blockSpan a)
        | none => 0)
    cases hg : ground.tieGap y e with
    | none => rfl
    | some nu => exact occupancyAt_eq_occ nu (blockSpan a)
  have hgs : gradedSums a b c
      = (ground.famFold Nat.add 0
          (fun p => if parity p = false then
            weylchar.multAtGap (fun m => occ m (blockSpan a)) (display c)
              (places.expo (display b) p) else 0)
          (places.perms a.length),
        ground.famFold Nat.add 0
          (fun p => if parity p = true then
            weylchar.multAtGap (fun m => occ m (blockSpan a)) (display c)
              (places.expo (display b) p) else 0)
          (places.perms a.length)) := by
    show sumsWith (occupancyAt (blockSpan a)) a.length b c = _
    rw [sumsWith_split (occupancyAt (blockSpan a)) a.length b c]
    have hc : ∀ side : Bool, ground.famFold Nat.add 0
        (fun p => if parity p = side then
          weylchar.multAtGap (occupancyAt (blockSpan a)) (display c)
            (places.expo (display b) p) else 0)
        (places.perms a.length)
      = ground.famFold Nat.add 0
        (fun p => if parity p = side then
          weylchar.multAtGap (fun m => occ m (blockSpan a)) (display c)
            (places.expo (display b) p) else 0)
        (places.perms a.length) := by
      intro side
      refine ground.famFold_congr_all Nat.add 0 _ _ (fun p => ?_)
        (places.perms a.length)
      by_cases hs : parity p = side
      · rw [if_pos hs, if_pos hs, hmult]
      · rw [if_neg hs, if_neg hs]
    rw [hc false, hc true]
  have hmid : ∀ side : Bool,
      weylchar.prodCount
          (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
          a.length (display c) side
        = ground.famFold Nat.add 0
          (fun v => match ground.tieGap (display c) v.content with
            | some yv => weylchar.prodCount
                (fun m => occ m (blockSpan b)) a.length yv side
            | none => 0)
          (blockSpan a) := by
    intro side
    rw [weylchar.prodCount_congr _ _
        (occ_fusedAt a.length (blockSpan a) (blockSpan b)
          (blockSpan_width a)
          (fun w hw => (blockSpan_width b w hw).trans hba))
        a.length (display c) side,
      weylchar.prodCount_famFold
        (fun v mu => match ground.tieGap mu v.content with
          | some w => occ w (blockSpan b)
          | none => 0)
        (blockSpan a) a.length (display c) side]
    exact ground.famFold_congr_all Nat.add 0 _ _
      (fun v => prodCount_gapMult (fun m => occ m (blockSpan b))
        v.content a.length (display c) side) (blockSpan a)
  have hvid : ∀ v : HVec,
      (match ground.tieGap (display c) v.content with
        | some yv => weylchar.prodCount (fun m => occ m (blockSpan b))
            a.length yv false
        | none => 0)
      + (match ground.tieGap (display c) v.content with
        | some w => weylchar.sideCount a.length (display b) w true
        | none => 0)
      = (match ground.tieGap (display c) v.content with
        | some yv => weylchar.prodCount (fun m => occ m (blockSpan b))
            a.length yv true
        | none => 0)
      + (match ground.tieGap (display c) v.content with
        | some w => weylchar.sideCount a.length (display b) w false
        | none => 0) := by
    intro v
    cases hg : ground.tieGap (display c) v.content with
    | none => rfl
    | some yv =>
      show weylchar.prodCount (fun m => occ m (blockSpan b))
            a.length yv false
          + weylchar.sideCount a.length (display b) yv true
        = weylchar.prodCount (fun m => occ m (blockSpan b))
            a.length yv true
          + weylchar.sideCount a.length (display b) yv false
      have hb' : weylchar.prodCount
            (fun chi => ground.countOf chi
              ((blockSpan b).map HVec.content))
            b.length yv false
          + weylchar.sideCount b.length (display b) yv true
        = weylchar.prodCount
            (fun chi => ground.countOf chi
              ((blockSpan b).map HVec.content))
            b.length yv true
          + weylchar.sideCount b.length (display b) yv false :=
        weylchar.identityRead b ((blockSpan b).map HVec.content)
          (casimir.recRead_def b) (strings.symRead_def b)
          (lowerspan.supportRead_def b) (lowerspan.topRead_def b) yv
      rw [hba, weylchar.prodCount_congr
          (fun chi => ground.countOf chi
            ((blockSpan b).map HVec.content))
          (fun m => occ m (blockSpan b))
          (fun mu => (occ_eq_countOf mu (blockSpan b)).symm)
          a.length yv false,
        weylchar.prodCount_congr
          (fun chi => ground.countOf chi
            ((blockSpan b).map HVec.content))
          (fun m => occ m (blockSpan b))
          (fun mu => (occ_eq_countOf mu (blockSpan b)).symm)
          a.length yv true] at hb'
      exact hb'
  rw [hgs]
  show weylchar.prodCount
        (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
        a.length (display c) false
      + ground.famFold Nat.add 0
        (fun p => if parity p = true then
          weylchar.multAtGap (fun m => occ m (blockSpan a)) (display c)
            (places.expo (display b) p) else 0)
        (places.perms a.length)
    = weylchar.prodCount
        (fun mu => occ mu (fusedAt (blockSpan a) (blockSpan b)))
        a.length (display c) true
      + ground.famFold Nat.add 0
        (fun p => if parity p = false then
          weylchar.multAtGap (fun m => occ m (blockSpan a)) (display c)
            (places.expo (display b) p) else 0)
        (places.perms a.length)
  rw [hmid false, hmid true,
    crossB_occ (blockSpan a) a.length (display b) (display c) true,
    crossB_occ (blockSpan a) a.length (display b) (display c) false,
    ← ground.famFold_add_split, ← ground.famFold_add_split]
  exact ground.famFold_congr_all Nat.add 0 _ _ hvid (blockSpan a)

/-- `cor:steinberg`'s display at any two shapes of one width: the
fusion count joins the odd graded sum to the even one at the ties
`ν_σ + σ(b + u) = c + u`.  The product `a_u · ch_a · ch_b` reads
twice at the monomial `x^{c+u}`.  Read as `ch_a · a_{b+u}`,
`thm:weylchar`'s identity at `b` enters once at each `a`-member's
withdrawn key and the shifted alternant's counts collect at the two
graded sums (`middle_factor`).  Read as the fused pool's channels,
`Σ_{c'} N^{c'}_{ab} a_{c'+u}`, the same identity enters at each
channel's own shape and the channels' shifted counts collapse at
the Kronecker read of the strictly descending displays, leaving the
stated channel's own fusion count (`middle_channels`).  The two
readings share the product's graded coefficient at the fused
occupancy family, so the shared pair cancels and the display
stands. -/
theorem readAll (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) : read a b c := by
  show fusionCount a b c + (gradedSums a b c).2
    = (gradedSums a b c).1
  have h2 := middle_factor a b c hba
  rw [middle_channels a b c hba hca, Nat.add_assoc] at h2
  exact ground.addCancelL _ h2

/-- The derived fast count reads the kernel-dimension count at
matched widths, the display's gap withdrawn at the shared graded
sum. -/
theorem count_fusion (a b c : Shape) (hba : b.length = a.length)
    (hca : c.length = a.length) :
    count a b c = blockcount.fusionCount a b c := by
  have h : blockcount.fusionCount a b c + (gradedSums a b c).2
      = (gradedSums a b c).1 := readAll a b c hba hca
  show (gradedSums a b c).1 - (gradedSums a b c).2
    = blockcount.fusionCount a b c
  rw [← h]
  exact ground.addSubSelfR _ _


/-! The member tier: `cor:steinberg`'s member display over
`thm:memberchar`'s per-key balance.  The product family carries the
two multiplicity families' memberwise joins, the member display the
top's count against the two graded convolution counts at the shifted
key, and the theorem transcribes the tex's own route — the product
read per key as the `b`-identity folded over the `a`-family and as
the channels' fold, the shared product counts cancelling and the
channel tops closing the display. -/

/-- The product family: the two multiplicity families' memberwise
joins at the normed spelling, the contents' sums — the tensor
product's content data (`cor:steinberg`'s member sentence). -/
def prodFam (La Lb : List (List BPair)) : List (List BPair) :=
  La.flatMap (fun p => Lb.map (fun q => poly.pnorm (elim.vecAdd p q)))

/-- `cor:steinberg`'s member display at a stated channel top: the
top's count among the channel tops joins the odd convolution count
to the even one at the shifted key. -/
def memberAt (t : gentable.Table) (Wb : List (List BPair × Bool))
    (La : List (List BPair)) (cVs : List (List BPair))
    (cV : List BPair) : Prop :=
  ground.countOf cV cVs
    + memberchar.convCount Wb La
        (poly.pnorm (elim.vecAdd cV (rhoV t))) true
    = memberchar.convCount Wb La
        (poly.pnorm (elim.vecAdd cV (rhoV t))) false

instance (t : gentable.Table) (Wb : List (List BPair × Bool))
    (La : List (List BPair)) (cVs : List (List BPair))
    (cV : List BPair) : Decidable (memberAt t Wb La cVs cV) :=
  inferInstanceAs (Decidable (_ = _))

/-- The product family's shape read: a memberwise join of two
framed members sits at the rank's order at its own representative —
the order the summands' own and the representative the join's. -/
private theorem prodFam_shape (t : gentable.Table)
    (La Lb : List (List BPair))
    (hmsha : mShapeRead t La) (hmshb : mShapeRead t Lb) :
    mShapeRead t (prodFam La Lb) := by
  intro mu hmu
  obtain ⟨p, hp, hmem⟩ := ground.mem_flatMap_of
    (fun p => Lb.map (fun q => poly.pnorm (elim.vecAdd p q))) La mu hmu
  obtain ⟨q, hq, hqe⟩ := ground.mem_map_of
    (fun q => poly.pnorm (elim.vecAdd p q)) Lb mu hmem
  refine ⟨?_, ?_⟩
  · rw [← hqe, poly.pnorm_length,
      elim.length_vecAdd p q t.rank (hmsha p hp).1 (hmshb q hq).1]
  · rw [← hqe]
    exact poly.pnorm_pnorm _

/-- The shifted alternant's counts folded over the `a`-family: the
family-first read of the graded product, `wCount` the count pair's
spelling (`memberchar.convCount_wFold`, the general). -/
private theorem wCount_shiftFold (t : gentable.Table)
    (Wb : List (List BPair × Bool)) (La : List (List BPair))
    (hwshb : wShapeRead t Wb) (hmsha : mShapeRead t La)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) (s : Bool) :
    ground.famFold Nat.add 0
      (fun p => wCount Wb
        (poly.pnorm (elim.vecAdd y (poly.neg p))) s) La
      = memberchar.convCount Wb La y s :=
  (memberchar.convCount_wFold t Wb La hwshb hmsha y hy hyn s).symm


/-- The convolution's counts folded over the `a`-family: the
`b`-family's convolution counts at the withdrawn keys collect at the
product family's own count at the key.  Per graded member the
product family's count splits over the flattened join — the map
layer collapsing at the move correspondence
(`assembly.addKey_iff`) — and the two withdrawals commute at the
key, the folds exchanging over the graded list and the family. -/
private theorem convCount_shiftFold (t : gentable.Table)
    (W : List (List BPair × Bool)) (Lb La : List (List BPair))
    (hwsh : wShapeRead t W) (hmshb : mShapeRead t Lb)
    (hmsha : mShapeRead t La)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) (s : Bool) :
    ground.famFold Nat.add 0
      (fun p => memberchar.convCount W Lb
        (poly.pnorm (elim.vecAdd y (poly.neg p))) s) La
      = memberchar.convCount W (prodFam La Lb) y s := by
  have hshift : ∀ u : List BPair, u.length = t.rank →
      (poly.pnorm (elim.vecAdd y (poly.neg u))).length = t.rank := by
    intro u hu
    exact (poly.pnorm_length _).trans (elim.length_vecAdd y _ t.rank hy
      ((ground.length_map BPair.swap u).trans hu))
  have hkey : ∀ u v : List BPair, u.length = t.rank → v.length = t.rank →
      poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd y (poly.neg u)))
        (poly.neg v))
      = poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd y (poly.neg v)))
        (poly.neg u)) := by
    intro u v hu hv
    have hnu : (poly.neg u).length = t.rank :=
      (ground.length_map BPair.swap u).trans hu
    have hnv : (poly.neg v).length = t.rank :=
      (ground.length_map BPair.swap v).trans hv
    rw [elim.pnorm_vecAdd_left (elim.vecAdd y (poly.neg u)) (poly.neg v)
        (by rw [elim.length_vecAdd y _ t.rank hy hnu, hnv]),
      elim.pnorm_vecAdd_left (elim.vecAdd y (poly.neg v)) (poly.neg u)
        (by rw [elim.length_vecAdd y _ t.rank hy hnv, hnu]),
      elim.vecAdd_assoc y (poly.neg u) (poly.neg v),
      elim.vecAdd_assoc y (poly.neg v) (poly.neg u),
      elim.vecAdd_comm (poly.neg u) (poly.neg v)]
  have hsplit : ∀ vp : List BPair × Bool, 0 < ground.countOf vp W →
      ground.countOf (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
          (prodFam La Lb)
      = ground.famFold Nat.add 0
        (fun p => ground.countOf (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) (poly.neg p))) Lb)
        La := by
    intro vp hvp
    obtain ⟨hkl, _⟩ := hwsh vp (ground.mem_of_countOf_pos vp W hvp)
    refine Eq.trans (ground.countOf_fold
      (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) (prodFam La Lb)) ?_
    refine Eq.trans (ground.famFold_flatMap
      (fun x => if poly.pnorm (elim.vecAdd y (poly.neg vp.1)) = x
        then (1 : Nat) else 0)
      (fun p => Lb.map (fun q => poly.pnorm (elim.vecAdd p q))) La) ?_
    refine ground.famFold_congr_members Nat.add 0 _ _ La (fun p hp => ?_)
    obtain ⟨hpl, _⟩ := hmsha p (ground.mem_of_countOf_pos p La hp)
    show ground.famFold Nat.add 0
        (fun x => if poly.pnorm (elim.vecAdd y (poly.neg vp.1)) = x
          then (1 : Nat) else 0)
        (Lb.map (fun q => poly.pnorm (elim.vecAdd p q)))
      = ground.countOf (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) (poly.neg p))) Lb
    refine Eq.trans (ground.countOf_fold
      (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
      (Lb.map (fun q => poly.pnorm (elim.vecAdd p q)))).symm ?_
    refine ground.countOf_map_iff (fun q => poly.pnorm (elim.vecAdd p q)) Lb
      (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
      (poly.pnorm (elim.vecAdd (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
        (poly.neg p))) (fun q hq => ?_)
    obtain ⟨hql, hqn⟩ := hmshb q (ground.mem_of_countOf_pos q Lb hq)
    have hiff := assembly.addKey_iff t.rank
      (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) p q
      (hshift vp.1 hkl) (poly.pnorm_pnorm _) hpl hql hqn
    exact Iff.intro (fun h => hiff.mp h.symm) (fun h => (hiff.mpr h).symm)
  have hM : memberchar.convCount W (prodFam La Lb) y s
      = ground.famFold Nat.add 0
        (fun p => ground.famFold Nat.add 0
          (fun vp : List BPair × Bool => if vp.2 = s then
            ground.countOf (poly.pnorm (elim.vecAdd
              (poly.pnorm (elim.vecAdd y (poly.neg p))) (poly.neg vp.1))) Lb
            else 0) W) La := by
    rw [memberchar.convCount_countOf t W (prodFam La Lb) hwsh
      (prodFam_shape t La Lb hmsha hmshb) y hy hyn s]
    have step1 : ground.famFold Nat.add 0
        (fun vp : List BPair × Bool => if vp.2 = s then
          ground.countOf (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
            (prodFam La Lb) else 0) W
        = ground.famFold Nat.add 0
          (fun vp : List BPair × Bool => if vp.2 = s then
            ground.famFold Nat.add 0
              (fun p => ground.countOf (poly.pnorm (elim.vecAdd
                (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
                (poly.neg p))) Lb) La
            else 0) W := by
      refine ground.famFold_congr_members Nat.add 0 _ _ W (fun vp hvp => ?_)
      by_cases hb : vp.2 = s
      · rw [if_pos hb, if_pos hb, hsplit vp hvp]
      · rw [if_neg hb, if_neg hb]
    have step2 := ground.famFold_guard_swap
      (fun vp : List BPair × Bool => vp.2 = s)
      (fun vp p => ground.countOf (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
        (poly.neg p))) Lb) W La
    have step3 : ground.famFold Nat.add 0
        (fun p => ground.famFold Nat.add 0
          (fun vp : List BPair × Bool => if vp.2 = s then
            ground.countOf (poly.pnorm (elim.vecAdd
              (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
              (poly.neg p))) Lb else 0) W) La
        = ground.famFold Nat.add 0
          (fun p => ground.famFold Nat.add 0
            (fun vp : List BPair × Bool => if vp.2 = s then
              ground.countOf (poly.pnorm (elim.vecAdd
                (poly.pnorm (elim.vecAdd y (poly.neg p)))
                (poly.neg vp.1))) Lb else 0) W) La := by
      refine ground.famFold_congr_members Nat.add 0 _ _ La (fun p hp => ?_)
      obtain ⟨hpl, _⟩ := hmsha p (ground.mem_of_countOf_pos p La hp)
      refine ground.famFold_congr_members Nat.add 0 _ _ W (fun vp hvp => ?_)
      obtain ⟨hkl, _⟩ := hwsh vp (ground.mem_of_countOf_pos vp W hvp)
      rw [hkey vp.1 p hkl hpl]
    exact step1.trans (step2.trans step3)
  refine Eq.trans ?_ hM.symm
  refine ground.famFold_congr_members Nat.add 0 _ _ La (fun p hp => ?_)
  obtain ⟨hpl, _⟩ := hmsha p (ground.mem_of_countOf_pos p La hp)
  exact memberchar.convCount_countOf t W Lb hwsh hmshb
    (poly.pnorm (elim.vecAdd y (poly.neg p))) (hshift p hpl)
    (poly.pnorm_pnorm _) s

/-- The product family's convolution count splits over the
channels: at an exhaustion read — every key's count in the product
family the channels' counts' sum — the count is the channels' own
convolution counts' fold, the graded fold exchanged with the
channel fold and each channel's count read back at its own shape. -/
private theorem convCount_chanFold (t : gentable.Table)
    (W : List (List BPair × Bool)) (La Lb : List (List BPair))
    (Ls : List (List (List BPair)))
    (hwsh : wShapeRead t W)
    (hmshp : mShapeRead t (prodFam La Lb))
    (hch : ∀ k, k < Ls.length →
      mShapeRead t (ground.getAt [] Ls k))
    (hexh : ∀ v : List BPair, ground.countOf v (prodFam La Lb)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') Ls)
    (y : List BPair) (hy : y.length = t.rank)
    (hyn : poly.pnorm y = y) (s : Bool) :
    memberchar.convCount W (prodFam La Lb) y s
      = ground.famFold Nat.add 0
          (fun L' => memberchar.convCount W L' y s) Ls := by
  rw [memberchar.convCount_countOf t W (prodFam La Lb) hwsh hmshp y hy hyn s]
  have step1 : ground.famFold Nat.add 0
      (fun vp : List BPair × Bool => if vp.2 = s then
        ground.countOf (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))
          (prodFam La Lb) else 0) W
      = ground.famFold Nat.add 0
        (fun vp : List BPair × Bool => if vp.2 = s then
          ground.famFold Nat.add 0
            (fun L' => ground.countOf
              (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L') Ls
          else 0) W := by
    refine ground.famFold_congr_all Nat.add 0 _ _ (fun vp => ?_) W
    by_cases hb : vp.2 = s
    · rw [if_pos hb, if_pos hb,
        hexh (poly.pnorm (elim.vecAdd y (poly.neg vp.1)))]
    · rw [if_neg hb, if_neg hb]
  have step2 := ground.famFold_guard_swap
    (fun vp : List BPair × Bool => vp.2 = s)
    (fun vp L' => ground.countOf
      (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L') W Ls
  have step3 : ground.famFold Nat.add 0
      (fun L' => ground.famFold Nat.add 0
        (fun vp : List BPair × Bool => if vp.2 = s then
          ground.countOf (poly.pnorm (elim.vecAdd y (poly.neg vp.1))) L'
          else 0) W) Ls
      = ground.famFold Nat.add 0
        (fun L' => memberchar.convCount W L' y s) Ls := by
    refine ground.famFold_congr_members Nat.add 0 _ _ Ls (fun L' hL' => ?_)
    obtain ⟨k, hk, hke⟩ := ground.getAt_of_mem ([] : List (List BPair))
      (ground.mem_of_countOf_pos L' Ls hL')
    have hmsh' : mShapeRead t L' := by
      rw [← hke]
      exact hch k hk
    exact (memberchar.convCount_countOf t W L' hwsh hmsh' y hy hyn s).symm
  exact step1.trans (step2.trans step3)

/-- The shift parts the top contents: two dominant top contents
whose shifted keys agree are one key, the shift read back at `ρ`'s
own withdrawal (`assembly.addKey_iff`). -/
private theorem top_inj (t : gentable.Table) (cV cV' : List BPair)
    (h1 : lamRead t cV) (h2 : lamRead t cV')
    (he : poly.pnorm (elim.vecAdd cV (rhoV t))
      = poly.pnorm (elim.vecAdd cV' (rhoV t))) : cV = cV' := by
  have hrl : (rhoV t).length = t.rank :=
    ground.length_replicate (BPair.ofNat 1) t.rank
  have hkl : (poly.pnorm (elim.vecAdd cV (rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd cV _ t.rank h1.1 hrl)
  have hkl' : (poly.pnorm (elim.vecAdd cV' (rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd cV' _ t.rank h2.1 hrl)
  have e1 : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg (rhoV t))) = cV :=
    assembly.addKey_solve t.rank
      (poly.pnorm (elim.vecAdd cV (rhoV t))) (rhoV t) cV hkl
      (poly.pnorm_pnorm _) hrl h1.1 h1.2.1 rfl
  have e2 : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd cV' (rhoV t))) (poly.neg (rhoV t))) = cV' :=
    assembly.addKey_solve t.rank
      (poly.pnorm (elim.vecAdd cV' (rhoV t))) (rhoV t) cV' hkl'
      (poly.pnorm_pnorm _) hrl h2.1 h2.2.1 rfl
  have e3 : poly.pnorm (elim.vecAdd
      (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg (rhoV t))) = cV' := by
    rw [he]
    exact e2
  exact e1.symm.trans e3

/-- The channel tops' fold at a stated top: the channels' even
counts at the top's shifted key join the top's own count among the
channel tops to their odd counts.  The channel at the top reads one
and none (`assembly.wTopAt`) at the keys' agreement; every other
channel reads its two counts at one value (`assembly.wRegRead`) off
its own top, the separation the shift's injectivity (`top_inj`) and
the strict dominance `shifted_reg` consumed here at `hcV`, so the
read binds no further hypothesis. -/
private theorem chanFold_top (t : gentable.Table)
    (Ws : List (List (List BPair × Bool)))
    (cVs : List (List BPair)) (cV : List BPair)
    (hcV : lamRead t cV)
    (hch : ∀ k, k < cVs.length →
      lamRead t (ground.getAt [] cVs k)
      ∧ wTopAt (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd (ground.getAt [] cVs k)
            (rhoV t)))
      ∧ wRegRead t (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd (ground.getAt [] cVs k)
            (rhoV t)))) :
    ground.famFold Nat.add 0
      (fun k => wCount (ground.getAt [] Ws k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
      (List.range cVs.length)
      = ground.countOf cV cVs + ground.famFold Nat.add 0
        (fun k => wCount (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
        (List.range cVs.length) := by
  have hreg := shifted_reg t cV hcV
  have hpt : ground.famFold Nat.add 0
      (fun k => wCount (ground.getAt [] Ws k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
      (List.range cVs.length)
      = ground.famFold Nat.add 0
        (fun k => (if cV = ground.getAt [] cVs k then 1 else 0)
          + wCount (ground.getAt [] Ws k)
            (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
        (List.range cVs.length) := by
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range cVs.length) (fun k hk => ?_)
    have hkl : k < cVs.length := ground.ltOfMem hk
    obtain ⟨hlam, htop, hrg⟩ := hch k hkl
    by_cases hc : cV = ground.getAt [] cVs k
    · rw [if_pos hc]
      have hkey : poly.pnorm (elim.vecAdd cV (rhoV t))
          = poly.pnorm (elim.vecAdd (ground.getAt [] cVs k) (rhoV t)) := by
        rw [hc]
      show ground.countOf (poly.pnorm (elim.vecAdd cV (rhoV t)), false)
          (ground.getAt [] Ws k)
        = 1 + ground.countOf (poly.pnorm (elim.vecAdd cV (rhoV t)), true)
          (ground.getAt [] Ws k)
      rw [hkey, htop.1, htop.2]
    · rw [if_neg hc, Nat.zero_add]
      have hne : poly.pnorm (elim.vecAdd cV (rhoV t))
          ≠ poly.pnorm (elim.vecAdd (ground.getAt [] cVs k) (rhoV t)) :=
        fun hq => hc (top_inj t cV (ground.getAt [] cVs k) hcV hlam hq)
      show ground.countOf (poly.pnorm (elim.vecAdd cV (rhoV t)), false)
          (ground.getAt [] Ws k)
        = ground.countOf (poly.pnorm (elim.vecAdd cV (rhoV t)), true)
          (ground.getAt [] Ws k)
      match Nat.eq_zero_or_pos (ground.countOf
        (poly.pnorm (elim.vecAdd cV (rhoV t)), true)
        (ground.getAt [] Ws k)) with
      | Or.inr hp =>
        exact (hrg (poly.pnorm (elim.vecAdd cV (rhoV t)), true)
          (ground.mem_of_countOf_pos _ _ hp) hreg hne).symm
      | Or.inl h0 =>
        match Nat.eq_zero_or_pos (ground.countOf
          (poly.pnorm (elim.vecAdd cV (rhoV t)), false)
          (ground.getAt [] Ws k)) with
        | Or.inr hp1 =>
          exact (hrg (poly.pnorm (elim.vecAdd cV (rhoV t)), false)
            (ground.mem_of_countOf_pos _ _ hp1) hreg hne).symm
        | Or.inl h1 => rw [h0, h1]
  have hind : ground.famFold Nat.add 0
      (fun k => if cV = ground.getAt [] cVs k then 1 else 0)
      (List.range cVs.length)
      = ground.countOf cV cVs := by
    exact (ground.famFold_getAt Nat.add 0
      (fun x => if cV = x then (1 : Nat) else 0)
      [] cVs cVs.length rfl).trans (ground.countOf_fold cV cVs).symm
  rw [hpt, ground.famFold_add_split
    (fun k => if cV = ground.getAt [] cVs k then (1 : Nat) else 0)
    (fun k => wCount (ground.getAt [] Ws k)
      (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
    (List.range cVs.length), hind]

/-- `cor:steinberg`'s member display: the tensor product's content
count at a stated top joins the odd convolution count to the even
one at the shifted key.  The product `a_ρ ch_a ch_b` reads per key
twice.  Read as `ch_a · a_{b+ρ}`, the `b`-identity
(`memberchar.identityRead`) enters once at each `a`-member's
withdrawn key and the two folds collect at the product family and at
the `a`-family's own convolution (`convCount_shiftFold`,
`wCount_shiftFold`).  Read as the channels' fold, the same identity
enters at the key itself per channel and the exhaustion read splits
the product family over the channels (`convCount_chanFold`).  The
two balances share the product family's graded counts, so the shared
pair cancels; at the key `pnorm (cV + ρ)` the channels' own tops
read one and none at the stated top and one value off it
(`chanFold_top`), which is the display.  The witness families and
the channel orbit data enter through the per-channel reads alone,
their frames those reads' own. -/
theorem memberRead (t : gentable.Table) (F : FundData)
    (W : List (List BPair × Bool)) (wits : List (List Nat))
    (Lb : List (List BPair)) (witsb : List (List Nat))
    (bV : List BPair)
    (Wb : List (List BPair × Bool)) (witsWb : List (List Nat))
    (La : List (List BPair))
    (Ls : List (List (List BPair)))
    (witss : List (List (List Nat)))
    (cVs : List (List BPair))
    (Ws : List (List (List BPair × Bool)))
    (witsWs : List (List (List Nat)))
    (cV : List BPair)
    (hshape : fundShape t F) (hgram : gramRead t F)
    (hgsym : gramSymRead F) (hsp : simplePosRead t F)
    (hsq : reflSquareRead t) (hpsq : permSquareRead t F)
    (hpi : permImageRead t F) (hrd : rhoDotRead t F)
    (hform : reflFormRead t F)
    (hwsh : wShapeRead t W) (hclose : wCloseRead t W)
    (hdom : wDomRead t W wits) (htop : wTopRead t W)
    (hmshb : mShapeRead t Lb) (hsymb : symRead t Lb)
    (hsuppb : supportRead t Lb witsb bV) (htopb : topRead Lb bV)
    (hlamb : lamRead t bV) (hrecb : recRead t F W Lb bV)
    (hwshb : wShapeRead t Wb) (hcloseb : wCloseRead t Wb)
    (hdomb : wDomAt t Wb witsWb
      (poly.pnorm (elim.vecAdd bV (rhoV t))))
    (htopb' : wTopAt Wb (poly.pnorm (elim.vecAdd bV (rhoV t))))
    (hregb : wRegRead t Wb (poly.pnorm (elim.vecAdd bV (rhoV t))))
    (hmsha : mShapeRead t La)
    (hlL : Ls.length = cVs.length)
    (hch : ∀ k, k < cVs.length →
      mShapeRead t (ground.getAt [] Ls k)
      ∧ symRead t (ground.getAt [] Ls k)
      ∧ supportRead t (ground.getAt [] Ls k)
          (ground.getAt [] witss k) (ground.getAt [] cVs k)
      ∧ topRead (ground.getAt [] Ls k) (ground.getAt [] cVs k)
      ∧ lamRead t (ground.getAt [] cVs k)
      ∧ recRead t F W (ground.getAt [] Ls k)
          (ground.getAt [] cVs k)
      ∧ wShapeRead t (ground.getAt [] Ws k)
      ∧ wCloseRead t (ground.getAt [] Ws k)
      ∧ wDomAt t (ground.getAt [] Ws k)
          (ground.getAt [] witsWs k)
          (poly.pnorm (elim.vecAdd (ground.getAt [] cVs k)
            (rhoV t)))
      ∧ wTopAt (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd (ground.getAt [] cVs k)
            (rhoV t)))
      ∧ wRegRead t (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd (ground.getAt [] cVs k)
            (rhoV t))))
    (hexh1 : ∀ v ∈ prodFam La Lb,
      ground.countOf v (prodFam La Lb)
        = ground.famFold Nat.add 0
            (fun L' => ground.countOf v L') Ls)
    (hexh2 : ∀ k, k < Ls.length → ∀ v ∈ ground.getAt [] Ls k,
      ground.countOf v (prodFam La Lb)
        = ground.famFold Nat.add 0
            (fun L' => ground.countOf v L') Ls)
    (hcV : lamRead t cV) :
    memberAt t Wb La cVs cV := by
  have hkl : (poly.pnorm (elim.vecAdd cV (rhoV t))).length = t.rank :=
    (poly.pnorm_length _).trans (elim.length_vecAdd cV _ t.rank hcV.1
      (ground.length_replicate (BPair.ofNat 1) t.rank))
  have hkn : poly.pnorm (poly.pnorm (elim.vecAdd cV (rhoV t)))
      = poly.pnorm (elim.vecAdd cV (rhoV t)) := poly.pnorm_pnorm _
  -- the product family's shape and the channels' own
  have hmshp : mShapeRead t (prodFam La Lb) :=
    prodFam_shape t La Lb hmsha hmshb
  have hchLs : ∀ k, k < Ls.length → mShapeRead t (ground.getAt [] Ls k) :=
    fun k hk => (hch k (by rw [← hlL]; exact hk)).1
  -- the channel fold's bridge from the list to its key family
  have hbrL : ∀ f : List (List BPair) → Nat,
      ground.famFold Nat.add 0 f Ls
      = ground.famFold Nat.add 0 (fun k => f (ground.getAt [] Ls k))
        (List.range Ls.length) := by
    intro f
    exact (ground.famFold_getAt Nat.add 0 f [] Ls Ls.length rfl).symm
  have hbr : ∀ f : List (List BPair) → Nat,
      ground.famFold Nat.add 0 f Ls
      = ground.famFold Nat.add 0 (fun k => f (ground.getAt [] Ls k))
        (List.range cVs.length) := by
    intro f
    rw [← hlL]
    exact hbrL f
  -- the exhaustion read at every key
  have hexh : ∀ v : List BPair, ground.countOf v (prodFam La Lb)
      = ground.famFold Nat.add 0
          (fun L' => ground.countOf v L') Ls := by
    intro v
    match Nat.eq_zero_or_pos (ground.countOf v (prodFam La Lb)) with
    | Or.inr hp =>
      exact hexh1 v (ground.mem_of_countOf_pos v (prodFam La Lb) hp)
    | Or.inl h0 =>
      by_cases hex : ∃ k, k + 1 < Ls.length + 1
          ∧ 0 < ground.countOf v (ground.getAt [] Ls k)
      · obtain ⟨k, hk, hpos⟩ := hex
        exact hexh2 k (Nat.lt_of_succ_lt_succ hk) v
          (ground.mem_of_countOf_pos v (ground.getAt [] Ls k) hpos)
      · have hz : ∀ k, 0 < ground.countOf k (List.range Ls.length) →
            ground.countOf v (ground.getAt [] Ls k) = 0 := by
          intro k hk
          match Nat.eq_zero_or_pos
            (ground.countOf v (ground.getAt [] Ls k)) with
          | Or.inl hzz => exact hzz
          | Or.inr hpp =>
            exact absurd ⟨k, Nat.succ_lt_succ (ground.ltOfMem hk), hpp⟩ hex
        rw [h0]
        refine (Eq.trans (hbrL (fun L' => ground.countOf v L')) ?_).symm
        refine Eq.trans (ground.famFold_congr_members Nat.add 0 _
          (fun _ => 0) (List.range Ls.length) hz) ?_
        exact ground.famFold_zero (fun _ => (0 : Nat)) (fun _ => rfl)
          (List.range Ls.length)
  -- the b-identity folded over the a-family
  have hfold1 : ground.famFold Nat.add 0
      (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false
        + wCount Wb (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true) La
      = ground.famFold Nat.add 0
        (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true
          + wCount Wb (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false)
        La :=
    ground.famFold_congr_all Nat.add 0 _ _
      (fun p => memberchar.identityRead t F W wits Lb witsb bV Wb witsWb
        hshape hgram hgsym hsp hsq hpsq hpi hrd hform hwsh hclose hdom
        htop hmshb hsymb hsuppb htopb hlamb hwshb hcloseb hdomb htopb'
        hregb hrecb (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p)))) La
  have hs1 : ground.famFold Nat.add 0
      (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false
        + wCount Wb (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true) La
      = ground.famFold Nat.add 0
          (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false) La
        + ground.famFold Nat.add 0
          (fun p => wCount Wb (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true) La :=
    ground.famFold_add_split
      (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false)
      (fun p => wCount Wb (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true) La
  have hs2 : ground.famFold Nat.add 0
      (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true
        + wCount Wb (poly.pnorm (elim.vecAdd
          (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false) La
      = ground.famFold Nat.add 0
          (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true) La
        + ground.famFold Nat.add 0
          (fun p => wCount Wb (poly.pnorm (elim.vecAdd
            (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false) La :=
    ground.famFold_add_split
      (fun p => memberchar.convCount W Lb (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) true)
      (fun p => wCount Wb (poly.pnorm (elim.vecAdd
        (poly.pnorm (elim.vecAdd cV (rhoV t))) (poly.neg p))) false) La
  have hbal1 := hs1.symm.trans (hfold1.trans hs2)
  rw [convCount_shiftFold t W Lb La hwsh hmshb hmsha
      (poly.pnorm (elim.vecAdd cV (rhoV t))) hkl hkn false,
    convCount_shiftFold t W Lb La hwsh hmshb hmsha
      (poly.pnorm (elim.vecAdd cV (rhoV t))) hkl hkn true,
    wCount_shiftFold t Wb La hwshb hmsha
      (poly.pnorm (elim.vecAdd cV (rhoV t))) hkl hkn false,
    wCount_shiftFold t Wb La hwshb hmsha
      (poly.pnorm (elim.vecAdd cV (rhoV t))) hkl hkn true] at hbal1
  -- the channels' identities folded over the tops
  have hfold3 : ground.famFold Nat.add 0
      (fun k => memberchar.convCount W (ground.getAt [] Ls k)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) false
        + wCount (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
      (List.range cVs.length)
      = ground.famFold Nat.add 0
        (fun k => memberchar.convCount W (ground.getAt [] Ls k)
            (poly.pnorm (elim.vecAdd cV (rhoV t))) true
          + wCount (ground.getAt [] Ws k)
            (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
        (List.range cVs.length) := by
    refine ground.famFold_congr_members Nat.add 0 _ _
      (List.range cVs.length) (fun k hk => ?_)
    have hkc : k < cVs.length := ground.ltOfMem hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hch k hkc
    exact memberchar.identityRead t F W wits (ground.getAt [] Ls k)
      (ground.getAt [] witss k) (ground.getAt [] cVs k)
      (ground.getAt [] Ws k) (ground.getAt [] witsWs k)
      hshape hgram hgsym hsp hsq hpsq hpi hrd hform hwsh hclose hdom
      htop h1 h2 h3 h4 h5 h7 h8 h9 h10 h11 h6
      (poly.pnorm (elim.vecAdd cV (rhoV t)))
  have hs3 : ground.famFold Nat.add 0
      (fun k => memberchar.convCount W (ground.getAt [] Ls k)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) false
        + wCount (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
      (List.range cVs.length)
      = ground.famFold Nat.add 0
          (fun k => memberchar.convCount W (ground.getAt [] Ls k)
            (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
          (List.range cVs.length)
        + ground.famFold Nat.add 0
          (fun k => wCount (ground.getAt [] Ws k)
            (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
          (List.range cVs.length) :=
    ground.famFold_add_split
      (fun k => memberchar.convCount W (ground.getAt [] Ls k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
      (fun k => wCount (ground.getAt [] Ws k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
      (List.range cVs.length)
  have hs4 : ground.famFold Nat.add 0
      (fun k => memberchar.convCount W (ground.getAt [] Ls k)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) true
        + wCount (ground.getAt [] Ws k)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
      (List.range cVs.length)
      = ground.famFold Nat.add 0
          (fun k => memberchar.convCount W (ground.getAt [] Ls k)
            (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
          (List.range cVs.length)
        + ground.famFold Nat.add 0
          (fun k => wCount (ground.getAt [] Ws k)
            (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
          (List.range cVs.length) :=
    ground.famFold_add_split
      (fun k => memberchar.convCount W (ground.getAt [] Ls k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
      (fun k => wCount (ground.getAt [] Ws k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) false)
      (List.range cVs.length)
  have hchan : ∀ s : Bool, ground.famFold Nat.add 0
      (fun k => memberchar.convCount W (ground.getAt [] Ls k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) s)
      (List.range cVs.length)
      = memberchar.convCount W (prodFam La Lb)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) s := by
    intro s
    refine Eq.trans ?_ (convCount_chanFold t W La Lb Ls hwsh hmshp hchLs
      hexh (poly.pnorm (elim.vecAdd cV (rhoV t))) hkl hkn s).symm
    exact (hbr (fun L' => memberchar.convCount W L'
      (poly.pnorm (elim.vecAdd cV (rhoV t))) s)).symm
  have hbal2 := hs3.symm.trans (hfold3.trans hs4)
  rw [hchan false, hchan true] at hbal2
  -- the tops' own read against the channel counts
  have hP6 := chanFold_top t Ws cVs cV hcV
    (fun k hk => match hch k hk with
      | ⟨_, _, _, _, h5, _, _, _, _, h10, h11⟩ => ⟨h5, h10, h11⟩)
  -- the two balances chain at the shared product fold
  have hA : memberchar.convCount W (prodFam La Lb)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) false
      = memberchar.convCount W (prodFam La Lb)
          (poly.pnorm (elim.vecAdd cV (rhoV t))) true
        + ground.countOf cV cVs := by
    refine ground.addCancelR (ground.famFold Nat.add 0
      (fun k => wCount (ground.getAt [] Ws k)
        (poly.pnorm (elim.vecAdd cV (rhoV t))) true)
      (List.range cVs.length)) ?_
    rw [hbal2, hP6, Nat.add_assoc]
  show ground.countOf cV cVs
      + memberchar.convCount Wb La
        (poly.pnorm (elim.vecAdd cV (rhoV t))) true
    = memberchar.convCount Wb La
        (poly.pnorm (elim.vecAdd cV (rhoV t))) false
  refine ground.addCancelL (memberchar.convCount W (prodFam La Lb)
    (poly.pnorm (elim.vecAdd cV (rhoV t))) true) ?_
  rw [← Nat.add_assoc, ← hA]
  exact hbal1

end steinberg
