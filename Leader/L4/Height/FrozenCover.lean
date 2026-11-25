import Leader.L4.Height.ChainRepair
import Leader.L4.Height.Throughput

namespace L4.Height.Recover.ChainTwo

open Classical
open L4.Compiler.Native
open L4.Height

set_option maxRecDepth 8192
set_option maxHeartbeats 40000000

noncomputable section

/-! ## Shortest paths on the cycle -/

/-- Clockwise edge distance from `a` to `v`, in `[0,m)`. -/
def cwDist {m : Nat} (a v : Fin m) : Nat :=
  (v.val + m - a.val) % m

theorem cwDist_lt {m : Nat} (hm : 0 < m) (a v : Fin m) :
    cwDist a v < m := by
  unfold cwDist
  exact Nat.mod_lt _ hm

/-- The vertices strictly after `a` on a clockwise walk of `k` edges. -/
def clockwisePath {m : Nat} (hm : 0 < m) :
    Fin m → Nat → List (Fin m)
  | _, 0 => []
  | a, k + 1 =>
      right hm a :: clockwisePath hm (right hm a) k

/-- The vertices strictly after `a` on a counter-clockwise walk of `k` edges. -/
def counterclockwisePath {m : Nat} (hm : 0 < m) :
    Fin m → Nat → List (Fin m)
  | _, 0 => []
  | a, k + 1 =>
      left hm a :: counterclockwisePath hm (left hm a) k

private theorem clockwisePath_length {m : Nat} (hm : 0 < m) :
    ∀ (a : Fin m) (k : Nat),
      (clockwisePath hm a k).length = k := by
  intro a k
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      simp only [clockwisePath, List.length_cons, ih]

private theorem counterclockwisePath_length {m : Nat} (hm : 0 < m) :
    ∀ (a : Fin m) (k : Nat),
      (counterclockwisePath hm a k).length = k := by
  intro a k
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      simp only [counterclockwisePath, List.length_cons, ih]

/-- Every list vertex is adjacent to its predecessor, beginning at `a`. -/
def ConsecutiveAdjacent {m : Nat} (hm : 0 < m) :
    Fin m → List (Fin m) → Prop
  | _, [] => True
  | a, v :: rest =>
      StageThree.Neighbor hm a v ∧
        ConsecutiveAdjacent hm v rest

private theorem clockwisePath_adjacent {m : Nat} (hm : 0 < m) :
    ∀ (a : Fin m) (k : Nat),
      ConsecutiveAdjacent hm a (clockwisePath hm a k) := by
  intro a k
  induction k generalizing a with
  | zero =>
      trivial
  | succ k ih =>
      simp only [clockwisePath, ConsecutiveAdjacent]
      exact ⟨Or.inr rfl, ih (right hm a)⟩

private theorem counterclockwisePath_adjacent {m : Nat} (hm : 0 < m) :
    ∀ (a : Fin m) (k : Nat),
      ConsecutiveAdjacent hm a (counterclockwisePath hm a k) := by
  intro a k
  induction k generalizing a with
  | zero =>
      trivial
  | succ k ih =>
      simp only [counterclockwisePath, ConsecutiveAdjacent]
      exact ⟨Or.inl rfl, ih (left hm a)⟩

/-- The chosen shortest arc, excluding its first vertex `a` and including one
vertex for every traversed edge. Ties are resolved clockwise. -/
def shortestPath {m : Nat} (hm : 0 < m)
    (a v : Fin m) : List (Fin m) :=
  let d := cwDist a v
  if d ≤ m - d then
    clockwisePath hm a d
  else
    counterclockwisePath hm a (m - d)

/-- The selected path has at most half the cycle length. -/
theorem shortestPath_length_le_half {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    (shortestPath hm a v).length ≤ m / 2 := by
  change
    (if cwDist a v ≤ m - cwDist a v then
      clockwisePath hm a (cwDist a v)
    else
      counterclockwisePath hm a (m - cwDist a v)).length ≤ m / 2
  split
  next hcw =>
    rw [clockwisePath_length]
    have hd := cwDist_lt hm a v
    have hsum : cwDist a v + (m - cwDist a v) = m :=
      Nat.add_sub_of_le (Nat.le_of_lt hd)
    omega
  next hccw =>
    rw [counterclockwisePath_length]
    have hd := cwDist_lt hm a v
    have hsum : cwDist a v + (m - cwDist a v) = m :=
      Nat.add_sub_of_le (Nat.le_of_lt hd)
    omega

/-- Consecutive selected vertices follow physical cycle edges. -/
theorem shortestPath_consecutive {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    ConsecutiveAdjacent hm a (shortestPath hm a v) := by
  change ConsecutiveAdjacent hm a
    (if cwDist a v ≤ m - cwDist a v then
      clockwisePath hm a (cwDist a v)
    else
      counterclockwisePath hm a (m - cwDist a v))
  split
  · exact clockwisePath_adjacent hm a _
  · exact counterclockwisePath_adjacent hm a _

/-! ## Successive sites on a shortest path are distinct -/

private theorem right_left_cycle {m : Nat} (hm : 0 < m) (i : Fin m) :
    right hm (left hm i) = i := by
  apply Fin.ext
  by_cases hzero : i.val = 0
  · simp only [right, left]
    rw [hzero]
    simp only [Nat.zero_add]
    have hmone : m - 1 < m := by omega
    rw [Nat.mod_eq_of_lt hmone]
    have he : m - 1 + 1 = m := by omega
    rw [he, Nat.mod_self]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hzero
    have hlt : i.val - 1 < m := by omega
    have hl : (i.val + m - 1) % m = i.val - 1 := by
      have he : i.val + m - 1 = (i.val - 1) + m := by omega
      rw [he, Nat.add_mod]
      simp [Nat.mod_eq_of_lt hlt]
    simp only [left, hl, right]
    have he : i.val - 1 + 1 = i.val := by omega
    rw [he, Nat.mod_eq_of_lt i.isLt]

private theorem right_ne_self {m : Nat} (hm : 0 < m)
    (hmone : m ≠ 1) (i : Fin m) :
    right hm i ≠ i := by
  intro heq
  have hv := congrArg Fin.val heq
  change (i.val + 1) % m = i.val at hv
  by_cases hlt : i.val + 1 < m
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have hwrap : i.val + 1 = m := by omega
    rw [hwrap, Nat.mod_self] at hv
    have hi0 : i.val = 0 := by omega
    have hm1 : m = 1 := by omega
    exact hmone hm1

private theorem left_ne_self {m : Nat} (hm : 0 < m)
    (hmone : m ≠ 1) (i : Fin m) :
    left hm i ≠ i := by
  intro heq
  have hright := congrArg (right hm) heq
  rw [right_left_cycle hm i] at hright
  exact (right_ne_self hm hmone i) hright.symm

/-- Only consecutive repetitions matter for strict sequential service: after a
hit, a different next site cannot be satisfied by the same `lastAct`. -/
def SuccessiveDistinct {β : Type} : List β → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      a ≠ b ∧ SuccessiveDistinct (b :: rest)

private theorem successiveDistinct_tail {β : Type} {a : β} :
    ∀ {rest : List β},
      SuccessiveDistinct (a :: rest) → SuccessiveDistinct rest := by
  intro rest h
  cases rest with
  | nil =>
      trivial
  | cons b rest =>
      cases rest with
      | nil =>
          trivial
      | cons c rest =>
          exact h.2

private theorem successiveDistinct_head_ne {β : Type}
    {a b : β} {rest : List β}
    (h : SuccessiveDistinct (a :: b :: rest)) :
    a ≠ b := by
  exact h.1

private theorem clockwisePath_successive {m : Nat} (hm : 0 < m)
    (hmone : m ≠ 1) :
    ∀ (a : Fin m) (k : Nat),
      SuccessiveDistinct (clockwisePath hm a k) := by
  intro a k
  induction k generalizing a with
  | zero =>
      trivial
  | succ k ih =>
      cases k with
      | zero =>
          trivial
      | succ k =>
          change
            right hm a ≠ right hm (right hm a) ∧
              SuccessiveDistinct
                (clockwisePath hm (right hm a) (Nat.succ k))
          constructor
          · intro heq
            exact (right_ne_self hm hmone (right hm a)) heq.symm
          · exact ih (right hm a)

private theorem counterclockwisePath_successive {m : Nat} (hm : 0 < m)
    (hmone : m ≠ 1) :
    ∀ (a : Fin m) (k : Nat),
      SuccessiveDistinct (counterclockwisePath hm a k) := by
  intro a k
  induction k generalizing a with
  | zero =>
      trivial
  | succ k ih =>
      cases k with
      | zero =>
          trivial
      | succ k =>
          change
            left hm a ≠ left hm (left hm a) ∧
              SuccessiveDistinct
                (counterclockwisePath hm (left hm a) (Nat.succ k))
          constructor
          · intro heq
            exact (left_ne_self hm hmone (left hm a)) heq.symm
          · exact ih (left hm a)

private theorem shortestPath_successive {m : Nat} (hm : 0 < m)
    (a v : Fin m) :
    SuccessiveDistinct (shortestPath hm a v) := by
  by_cases hOne : m = 1
  · subst m
    have hlen := shortestPath_length_le_half hm a v
    have hhalf : (1 : Nat) / 2 = 0 := by decide
    rw [hhalf] at hlen
    have hz : (shortestPath hm a v).length = 0 := by omega
    cases hp : shortestPath hm a v with
    | nil =>
        trivial
    | cons z zs =>
        rw [hp] at hz
        simp only [List.length_cons] at hz
        omega
  · change SuccessiveDistinct
      (if cwDist a v ≤ m - cwDist a v then
        clockwisePath hm a (cwDist a v)
      else
        counterclockwisePath hm a (m - cwDist a v))
    split
    · exact clockwisePath_successive hm hOne a _
    · exact counterclockwisePath_successive hm hOne a _

/-! ## Ordered activations and the deterministic cap interface -/

/-- The sites in `path` occur, in order, among the activated owners. -/
def OrderedAlong {m : Nat}
    (acts : List (Fin m × Bool)) (path : List (Fin m)) : Prop :=
  path.Sublist (acts.map Prod.fst)

private theorem nil_sublist {β : Type} :
    ∀ xs : List β, ([] : List β).Sublist xs := by
  intro xs
  induction xs with
  | nil =>
      exact List.Sublist.slnil
  | cons x xs ih =>
      exact List.Sublist.cons x ih

private theorem orderedAlong_nil {m : Nat}
    (acts : List (Fin m × Bool)) :
    OrderedAlong acts [] := by
  unfold OrderedAlong
  exact nil_sublist _

private theorem orderedAlong_skip {m : Nat}
    {acts : List (Fin m × Bool)} {path : List (Fin m)}
    (act : Fin m × Bool) (h : OrderedAlong acts path) :
    OrderedAlong (act :: acts) path := by
  unfold OrderedAlong at h ⊢
  simp only [List.map_cons]
  exact List.Sublist.cons (Prod.fst act) h

private theorem orderedAlong_take {m : Nat}
    {acts : List (Fin m × Bool)} {path : List (Fin m)}
    {i : Fin m} {delta : Bool} (h : OrderedAlong acts path) :
    OrderedAlong ((i, delta) :: acts) (i :: path) := by
  unfold OrderedAlong at h ⊢
  simp only [List.map_cons]
  exact List.Sublist.cons_cons i h

/-- The deterministic path-cap theorem to be supplied by CAPCOVER. -/
def CapInterface {m : Nat} (B M D : Nat) (hm : 0 < m) : Prop :=
  ∀ (c : Fin m → NativeRecord) (acts : List (Fin m × Bool)),
    StageThree.Quiet M hm c →
    StageTwo.WellFormed M c →
    (∀ a v, OrderedAlong acts (shortestPath hm a v)) →
    StageThree.Frozen M D hm
      (StageThree.runActivations B M hm c acts)

/-! ## Projection of scheduler words to effective native activations -/

/-- Effective native activations generated while consuming a scheduler word. -/
def activations
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) :
    α → Thru.Word n → List (Fin m × Bool)
  | _, [] => []
  | x, e :: u =>
      match C.act x e with
      | none => activations C (C.next x e) u
      | some p => p :: activations C (C.next x e) u

/-- The endpoint native configuration is exactly the effective activation run. -/
theorem cfg_runWord
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) :
    ∀ (x : α) (u : Thru.Word n),
      C.cfg (L4.Height.runWord C.next x u) =
        StageThree.runActivations B M hm (C.cfg x)
          (activations C x u) := by
  intro x u
  induction u generalizing x with
  | nil =>
      rfl
  | cons e u ih =>
      change
        C.cfg (L4.Height.runWord C.next (C.next x e) u) =
          StageThree.runActivations B M hm (C.cfg x)
            (activations C x (e :: u))
      rw [ih (C.next x e)]
      cases hact : C.act x e with
      | none =>
          have hc := C.cfg_next x e
          simp only [hact] at hc
          simp only [activations, hact]
          rw [hc]
      | some p =>
          rcases p with ⟨i, delta⟩
          have hc := C.cfg_next x e
          simp only [hact] at hc
          simp only [activations, hact, StageThree.runActivations]
          rw [hc]

/-- A served successor records an actual effective activation. -/
private theorem act_of_served_next
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (x : α) (e : Fin n) (i : Fin m)
    (hserved : C.served i (C.next x e)) :
    ∃ delta, C.act x e = some (i, delta) := by
  unfold Chain.ClockChain.served at hserved
  rw [C.last_next x e] at hserved
  cases hact : C.act x e with
  | none =>
      simp [hact] at hserved
  | some p =>
      rcases p with ⟨j, delta⟩
      have hji : j = i := by
        simpa [hact] using hserved
      subst j
      exact ⟨delta, rfl⟩

private theorem served_exclusive
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    {i j : Fin m} (hij : i ≠ j) (y : α)
    (hi : C.served i y) :
    ¬ C.served j y := by
  intro hj
  unfold Chain.ClockChain.served at hi hj
  have he : (some i : Option (Fin m)) = some j := hi.symm.trans hj
  have hij' : i = j := by
    cases he
    rfl
  exact hij hij'

/-- Quietness and WellFormedness persist along every scheduler word. -/
private theorem qu_run
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (hM : StageTwo.ClockParams M) :
    ∀ (x : α), Chain.QuSet C x → ∀ u : Thru.Word n,
      Chain.QuSet C (L4.Height.runWord C.next x u) := by
  intro x hx u
  induction u generalizing x with
  | nil =>
      simpa [L4.Height.runWord] using hx
  | cons e u ih =>
      have hn := Chain.qu_closed C hM x e hx
      simpa [L4.Height.runWord] using
        (ih (C.next x e) hn)

/-! ## Strict ordered path waits -/

/-- Only the first query needs an unconditional scheduler step. Subsequent
queries are ordinary sequential waits. -/
noncomputable def headSeq {α : Type} {n : Nat}
    (next : α → Fin n → α) :
    List (α → Prop) → α → Thru.Word n → Nat
  | [], _, _ => 0
  | _ :: _, _, [] => 0
  | A :: As, x, e :: u =>
      Nat.succ (Thru.seqWait next (A :: As) (next x e) u)

private theorem seqWait_no_queries
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (x : α) (u : Thru.Word n) :
    Thru.seqWait next [] x u = 0 := by
  calc
    Thru.seqWait next [] x u =
        Thru.seqWait next [fun _ : α => True] x u :=
      (Thru.seqWait_cons_of_hit next
        (fun _ : α => True) [] x trivial u).symm
    _ = Thru.wait next (fun _ : α => True) x u :=
      Thru.seqWait_single next (fun _ : α => True) x u
    _ = 0 := Thru.wait_of_hit next
      (fun _ : α => True) x trivial u

private theorem headSeq_eq_seqWait_of_head_not
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (A : α → Prop)
    (As : List (α → Prop)) (x : α) (u : Thru.Word n)
    (hnot : ¬ A x) :
    headSeq next (A :: As) x u =
      Thru.seqWait next (A :: As) x u := by
  cases u with
  | nil =>
      simp [headSeq, Thru.seqWait_nil]
  | cons e u =>
      simp only [headSeq]
      rw [Thru.seqWait_cons_step next A As x hnot e u]
      simp only [Nat.one_add]

/-- Completion of a strict path wait witnesses the ordered activation
subsequence in the same strict prefix. -/
private theorem headSeq_ordered
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) :
    ∀ (u : Thru.Word n) (sites : List (Fin m))
      (x : α) (k : Nat),
      SuccessiveDistinct sites →
      headSeq C.next (sites.map C.served) x u ≤ k →
      k < u.length →
      OrderedAlong (activations C x (u.take k)) sites := by
  intro u
  induction u with
  | nil =>
      intro sites x k _hdist _hwait hk
      simp only [List.length_nil] at hk
      omega
  | cons e u ih =>
      intro sites x k hdist hwait hk
      cases sites with
      | nil =>
          exact orderedAlong_nil _
      | cons i is =>
          cases k with
          | zero =>
              simp only [List.map_cons, headSeq] at hwait
              omega
          | succ k =>
              have hkTail : k < u.length := by
                simp only [List.length_cons] at hk
                omega
              have hseq :
                  Thru.seqWait C.next
                      (C.served i :: is.map C.served)
                      (C.next x e) u ≤ k := by
                simp only [List.map_cons, headSeq] at hwait
                omega
              by_cases hi : C.served i (C.next x e)
              · rw [Thru.seqWait_cons_of_hit C.next (C.served i)
                    (is.map C.served) (C.next x e) hi u] at hseq
                have heq :
                    headSeq C.next (is.map C.served)
                        (C.next x e) u =
                      Thru.seqWait C.next (is.map C.served)
                        (C.next x e) u := by
                  cases is with
                  | nil =>
                      simpa [headSeq] using
                        (seqWait_no_queries C.next (C.next x e) u).symm
                  | cons j js =>
                      have hij : i ≠ j :=
                        successiveDistinct_head_ne hdist
                      have hjnot : ¬ C.served j (C.next x e) :=
                        served_exclusive C hij (C.next x e) hi
                      simpa only [List.map_cons] using
                        (headSeq_eq_seqWait_of_head_not C.next
                          (C.served j) (js.map C.served)
                          (C.next x e) u hjnot)
                have hhead :
                    headSeq C.next (is.map C.served)
                      (C.next x e) u ≤ k := by
                  rw [heq]
                  exact hseq
                have hdistTail : SuccessiveDistinct is :=
                  successiveDistinct_tail hdist
                have htail :=
                  ih is (C.next x e) k hdistTail hhead hkTail
                obtain ⟨delta, hact⟩ :=
                  act_of_served_next C x e i hi
                have htaken :=
                  orderedAlong_take (i := i) (delta := delta) htail
                simpa only [List.take_succ_cons, activations, hact] using htaken
              · have heq :=
                  headSeq_eq_seqWait_of_head_not C.next
                    (C.served i) (is.map C.served)
                    (C.next x e) u hi
                have hhead :
                    headSeq C.next
                        (C.served i :: is.map C.served)
                        (C.next x e) u ≤ k := by
                  rw [heq]
                  exact hseq
                have htail :=
                  ih (i :: is) (C.next x e) k hdist hhead hkTail
                cases hact : C.act x e with
                | none =>
                    simpa only [List.take_succ_cons, activations, hact] using htail
                | some p =>
                    have hskip := orderedAlong_skip p htail
                    simpa only [List.take_succ_cons, activations, hact] using hskip

/-! ## Sharp `4^length` exponential moment for the strict first query -/

private theorem one_plus_exp_le_two (q L : Nat) (hL : 1 ≤ L) :
    2 ^ ((1 + q) / L) ≤ 2 * 2 ^ (q / L) := by
  by_cases hOne : L = 1
  · subst L
    simp only [Nat.div_one, Nat.add_comm 1 q, Nat.pow_succ]
    omega
  · have hsplit := Thru.div_add_le 1 q L hL
    have hlarge : 1 < L := by omega
    have hzero : 1 / L = 0 := Nat.div_eq_of_lt hlarge
    have hdiv : (1 + q) / L ≤ q / L + 1 := by
      simpa only [hzero, Nat.zero_add] using hsplit
    have hp := Nat.pow_le_pow_right
      (by omega : 0 < (2 : Nat)) hdiv
    calc
      2 ^ ((1 + q) / L) ≤ 2 ^ (q / L + 1) := hp
      _ = 2 * 2 ^ (q / L) := by
        rw [Nat.pow_succ]
        omega

private theorem seqWait_moment_sharp_raw
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (A : α → Prop) (As : List (α → Prop))
    (hMoment : ∀ Q, Q ∈ A :: As → ∀ y,
      Thru.MomentAt next Q L y) :
    ∀ x t,
      Thru.wordSum
          (fun u => 2 ^ (Thru.seqWait next (A :: As) x u / L)) t ≤
        2 * 4 ^ As.length * n ^ t := by
  induction As generalizing A with
  | nil =>
      intro x t
      have hfirst := Thru.momentAt_raw next A L x
        (hMoment A (by simp) x) t
      simpa [Thru.seqWait_single] using hfirst
  | cons B Bs ih =>
      intro x t
      have hMomentTail :
          ∀ Q, Q ∈ B :: Bs → ∀ y,
            Thru.MomentAt next Q L y := by
        intro Q hQ y
        exact hMoment Q (by simp [hQ]) y
      have hTail : ∀ y r,
          Thru.wordSum
              (fun u =>
                2 ^ (Thru.seqWait next (B :: Bs) y u / L)) r ≤
            (2 * 4 ^ Bs.length) * n ^ r :=
        ih (A := B) hMomentTail
      have hC : 1 ≤ 2 * 4 ^ Bs.length := by
        have hp : 0 < (4 : Nat) ^ Bs.length :=
          Nat.pow_pos (by decide)
        omega
      have hsplit := Thru.splitCost_sum_le next A (B :: Bs) L
        (2 * 4 ^ Bs.length) hTail hC 0 x t
      have hsplit' :
          Thru.wordSum (Thru.splitCost next A (B :: Bs) L 0 x) t ≤
            (2 * 4 ^ Bs.length) *
              Thru.wordSum
                (fun u => 2 ^ (Thru.wait next A x u / L)) t := by
        simpa using hsplit
      have hpoint : ∀ u,
          2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L) ≤
            2 * Thru.splitCost next A (B :: Bs) L 0 x u := by
        intro u
        simpa using
          (Thru.seqExp_le_splitCost next A (B :: Bs) L hL 0 x u)
      have hpref :
          Thru.wordSum
              (fun u =>
                2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L)) t ≤
            2 * Thru.wordSum
              (Thru.splitCost next A (B :: Bs) L 0 x) t := by
        calc
          Thru.wordSum
              (fun u =>
                2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L)) t ≤
            Thru.wordSum
              (fun u =>
                2 * Thru.splitCost next A (B :: Bs) L 0 x u) t :=
              Thru.wordSum_mono _ _ hpoint t
          _ = 2 * Thru.wordSum
              (Thru.splitCost next A (B :: Bs) L 0 x) t :=
            Thru.wordSum_mul_left _ _ _
      have hfirst := Thru.momentAt_raw next A L x
        (hMoment A (by simp) x) t
      calc
        Thru.wordSum
            (fun u =>
              2 ^ (Thru.seqWait next (A :: B :: Bs) x u / L)) t ≤
          2 * Thru.wordSum
            (Thru.splitCost next A (B :: Bs) L 0 x) t := hpref
        _ ≤ 2 * ((2 * 4 ^ Bs.length) *
              Thru.wordSum
                (fun u => 2 ^ (Thru.wait next A x u / L)) t) :=
          Nat.mul_le_mul_left 2 hsplit'
        _ ≤ 2 * ((2 * 4 ^ Bs.length) * (2 * n ^ t)) :=
          Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left (2 * 4 ^ Bs.length) hfirst)
        _ = 2 * 4 ^ (B :: Bs).length * n ^ t := by
          simp only [List.length_cons]
          have hFour : (2 : Nat) * 2 = 4 := by decide
          rw [Nat.pow_succ, ← hFour]
          ac_rfl

private theorem sum_ofFn_const (n c : Nat) :
    (List.ofFn (fun _ : Fin n => c)).sum = n * c := by
  induction n with
  | zero =>
      simp [List.ofFn_zero]
  | succ n ih =>
      rw [List.ofFn_succ, List.sum_cons, ih, Nat.succ_mul]
      exact Nat.add_comm _ _

private theorem headSeq_moment_raw
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat) (hL : 1 ≤ L)
    (A : α → Prop) (As : List (α → Prop))
    (hMoment : ∀ Q, Q ∈ A :: As → ∀ y,
      Thru.MomentAt next Q L y) :
    ∀ x t,
      Thru.wordSum
          (fun u => 2 ^ (headSeq next (A :: As) x u / L)) t ≤
        4 ^ (A :: As).length * n ^ t := by
  intro x t
  cases t with
  | zero =>
      simp only [Thru.wordSum, headSeq, Nat.zero_div,
        Nat.pow_zero, Nat.mul_one]
      have hp : 0 < (4 : Nat) ^ (A :: As).length :=
        Nat.pow_pos (by decide)
      omega
  | succ t =>
      have hEach : ∀ e : Fin n,
          Thru.wordSum
              (fun v =>
                2 ^ (headSeq next (A :: As) x (e :: v) / L)) t ≤
            4 ^ (A :: As).length * n ^ t := by
        intro e
        have hpoint : ∀ v,
            2 ^ (headSeq next (A :: As) x (e :: v) / L) ≤
              2 * 2 ^
                (Thru.seqWait next (A :: As) (next x e) v / L) := by
          intro v
          simpa only [headSeq, Nat.one_add] using
            (one_plus_exp_le_two
              (Thru.seqWait next (A :: As) (next x e) v) L hL)
        have hsum := Thru.wordSum_mono
          (fun v =>
            2 ^ (headSeq next (A :: As) x (e :: v) / L))
          (fun v =>
            2 * 2 ^
              (Thru.seqWait next (A :: As) (next x e) v / L))
          hpoint t
        rw [Thru.wordSum_mul_left] at hsum
        have hseq := seqWait_moment_sharp_raw next L hL A As
          hMoment (next x e) t
        calc
          Thru.wordSum
              (fun v =>
                2 ^ (headSeq next (A :: As) x (e :: v) / L)) t ≤
            2 * Thru.wordSum
              (fun v =>
                2 ^
                  (Thru.seqWait next (A :: As) (next x e) v / L)) t := hsum
          _ ≤ 2 * (2 * 4 ^ As.length * n ^ t) :=
            Nat.mul_le_mul_left 2 hseq
          _ = 4 ^ (A :: As).length * n ^ t := by
            simp only [List.length_cons]
            have hFour : (2 : Nat) * 2 = 4 := by decide
            rw [Nat.pow_succ, ← hFour]
            ac_rfl
      simp only [Thru.wordSum]
      calc
        (List.ofFn (fun e : Fin n =>
          Thru.wordSum
              (fun v =>
                2 ^ (headSeq next (A :: As) x (e :: v) / L)) t)).sum ≤
          (List.ofFn (fun _ : Fin n =>
            4 ^ (A :: As).length * n ^ t)).sum := by
              apply Thru.ofFn_sum_le
              exact hEach
        _ = n * (4 ^ (A :: As).length * n ^ t) :=
          sum_ofFn_const n _
        _ = 4 ^ (A :: As).length * n ^ Nat.succ t := by
          rw [Nat.pow_succ]
          ac_rfl

private theorem headSeq_moment_all_scales
    {α : Type} {n : Nat}
    (next : α → Fin n → α) (L : Nat)
    (queries : List (α → Prop))
    (hMoment : ∀ Q, Q ∈ queries → ∀ y,
      Thru.MomentAt next Q L y)
    (x : α) (t : Nat) :
    Thru.wordSum
        (fun u => 2 ^ (Nat.min (headSeq next queries x u) t / L)) t ≤
      4 ^ queries.length * n ^ t := by
  cases queries with
  | nil =>
      simp [headSeq, Thru.wordSum_const_one]
  | cons A As =>
      by_cases hL : 1 ≤ L
      · have hraw := headSeq_moment_raw next L hL A As
          hMoment x t
        have hpoint : ∀ u,
            2 ^ (Nat.min (headSeq next (A :: As) x u) t / L) ≤
              2 ^ (headSeq next (A :: As) x u / L) := by
          intro u
          have hd :
              Nat.min (headSeq next (A :: As) x u) t / L ≤
                headSeq next (A :: As) x u / L :=
            Nat.div_le_div_right (c := L) (Nat.min_le_left _ _)
          exact Nat.pow_le_pow_right (by omega : 0 < (2 : Nat)) hd
        exact Nat.le_trans
          (Thru.wordSum_mono _ _ hpoint t) hraw
      · have hzero : L = 0 := by omega
        subst L
        simp only [Nat.div_zero, Nat.pow_zero]
        rw [Thru.wordSum_const_one]
        have hp : 1 ≤ 4 ^ (A :: As).length := by
          have hpos : 0 < (4 : Nat) ^ (A :: As).length :=
            Nat.pow_pos (by decide)
          omega
        simpa only [Nat.one_mul] using
          (Nat.mul_le_mul_right (n ^ t) hp)

/-! ## Pair-indexed service family -/

def pathQueries
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm)
    (path : List (Fin m)) : List (α → Prop) :=
  path.map C.served

noncomputable def pairWait
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α)
    (a v : Fin m) : Thru.Word n → Nat :=
  fun u => headSeq C.next
    (pathQueries C (shortestPath hm a v)) x u

noncomputable def frozenFunctions
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α) :
    List (Thru.Word n → Nat) :=
  (List.finRange m).flatMap (fun a =>
    (List.finRange m).map (fun v => pairWait C x a v))

private theorem flatMap_length {β γ : Type}
    (xs : List β) (f : β → List γ) (r : Nat)
    (hf : ∀ y, y ∈ xs → (f y).length = r) :
    (xs.flatMap f).length = xs.length * r := by
  induction xs with
  | nil =>
      simp
  | cons y ys ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_cons]
      rw [hf y (by simp)]
      rw [ih (by
        intro z hz
        exact hf z (by simp [hz]))]
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

theorem frozenFunctions_length
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α) :
    (frozenFunctions C x).length = m * m := by
  unfold frozenFunctions
  rw [flatMap_length _ _ m (by
    intro a ha
    simp only [List.length_map, List.length_finRange])]
  simp only [List.length_finRange]

private theorem pairWait_mem
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α)
    (a v : Fin m) :
    pairWait C x a v ∈ frozenFunctions C x := by
  unfold frozenFunctions
  rw [List.mem_flatMap]
  refine ⟨a, List.mem_finRange a, ?_⟩
  exact List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩

private theorem pairWait_moment
    {α : Type} {n m B M L : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y)
    (a v : Fin m) (t : Nat) :
    Thru.wordSum
        (fun u =>
          2 ^ (Nat.min (pairWait C x a v u) t / L)) t ≤
      4 ^ (m / 2) * n ^ t := by
  have hQueries :
      ∀ Q, Q ∈ pathQueries C (shortestPath hm a v) → ∀ y,
        Thru.MomentAt C.next Q L y := by
    intro Q hQ y
    unfold pathQueries at hQ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hQ
    exact hMom i y
  have hs := headSeq_moment_all_scales C.next L
    (pathQueries C (shortestPath hm a v)) hQueries x t
  have hlen :
      (pathQueries C (shortestPath hm a v)).length ≤ m / 2 := by
    unfold pathQueries
    rw [List.length_map]
    exact shortestPath_length_le_half hm a v
  have hp :
      4 ^ (pathQueries C (shortestPath hm a v)).length ≤
        4 ^ (m / 2) :=
    Nat.pow_le_pow_right (by decide : 0 < (4 : Nat)) hlen
  unfold pairWait
  exact Nat.le_trans hs (Nat.mul_le_mul_right (n ^ t) hp)

private theorem le_maxWait_of_mem {n : Nat}
    (W : Thru.Word n → Nat) :
    ∀ Ws, W ∈ Ws → ∀ u, W u ≤ Thru.maxWait Ws u := by
  intro Ws hW u
  induction Ws with
  | nil =>
      cases hW
  | cons V Vs ih =>
      simp only [List.mem_cons] at hW
      simp only [Thru.maxWait]
      rcases hW with rfl | htail
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

private theorem pairWait_ordered
    {α : Type} {n m B M : Nat} {hm : 0 < m}
    (C : Chain.ClockChain α n m B M hm) (x : α)
    (a v : Fin m) (u : Thru.Word n) (k : Nat)
    (hwait : pairWait C x a v u ≤ k)
    (hk : k < u.length) :
    OrderedAlong (activations C x (u.take k))
      (shortestPath hm a v) := by
  unfold pairWait pathQueries at hwait
  exact headSeq_ordered C u (shortestPath hm a v) x k
    (shortestPath_successive hm a v) hwait hk

/-! ## The strict frozen-stage cover -/

/-- Ordered strict services along every selected shortest path establish the
stage-two frozen cut. -/
theorem frozen_stage_cover
    {α : Type} {n m B M L : Nat} (hm : 0 < m)
    (C : Chain.ClockChain α n m B M hm)
    (hcap : CapInterface B M (m / 2) hm)
    (hM : StageTwo.ClockParams M)
    (hMom : ∀ i y, Thru.MomentAt C.next (C.served i) L y) :
    StageCoverStrict C.next (Chain.QuSet C) (Chain.FrSet C (m / 2))
      L (m * m) (4 ^ (m / 2)) := by
  unfold StageCoverStrict
  intro x hx
  let Ws := frozenFunctions C x
  refine ⟨Ws, ?_, ?_, ?_⟩
  · dsimp [Ws]
    exact frozenFunctions_length C x
  · intro W hW t
    dsimp [Ws] at hW
    unfold frozenFunctions at hW
    rw [List.mem_flatMap] at hW
    obtain ⟨a, ha, hWa⟩ := hW
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hWa
    exact pairWait_moment C x hMom a v t
  · intro u k hmax hk
    have hqu := qu_run C hM x hx (u.take k)
    have hordered :
        ∀ a v,
          OrderedAlong (activations C x (u.take k))
            (shortestPath hm a v) := by
      intro a v
      let W := pairWait C x a v
      have hWmem : W ∈ Ws := by
        dsimp [Ws, W]
        exact pairWait_mem C x a v
      have hWle := le_maxWait_of_mem W Ws hWmem u
      have hWk : W u ≤ k := Nat.le_trans hWle hmax
      exact pairWait_ordered C x a v u k hWk hk
    have hfreeze0 :=
      hcap (C.cfg x) (activations C x (u.take k))
        hx.1 hx.2 hordered
    have hcfg := cfg_runWord C x (u.take k)
    have hfreeze :
        StageThree.Frozen M (m / 2) hm
          (C.cfg (L4.Height.runWord C.next x (u.take k))) := by
      rw [hcfg]
      exact hfreeze0
    unfold Chain.FrSet
    exact ⟨hqu, hfreeze⟩

#print axioms L4.Height.Recover.ChainTwo.shortestPath_length_le_half
#print axioms L4.Height.Recover.ChainTwo.shortestPath_consecutive
#print axioms L4.Height.Recover.ChainTwo.cfg_runWord
#print axioms L4.Height.Recover.ChainTwo.frozen_stage_cover

end

end L4.Height.Recover.ChainTwo

