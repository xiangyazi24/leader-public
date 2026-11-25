import Leader.L4.RankSupplier

/-! Ordered dependency paths in the finite open FIFO line. -/
namespace L4.QueueDAG
open GGTiming
open scoped List

/-- The unfolded binary dependency DAG. A leaf is an already satisfied
threshold, and a fork is a mark needed strictly after both dependencies. -/
inductive Tree (n : Nat) where
  | done
  | fork (edge : Fin n) (left right : Tree n)

/-- All required ordered paths, indexed by (possibly duplicate) leaves. -/
def Tree.paths {n : Nat} : Tree n → List (List (Fin n))
  | .done => [[]]
  | .fork e a b => (a.paths ++ b.paths).map (· ++ [e])

/-- Maximum length of a dependency path. -/
def Tree.depth {n : Nat} : Tree n → Nat
  | .done => 0
  | .fork _ a b => max a.depth b.depth + 1

theorem Tree.paths_nonempty {n : Nat} (t : Tree n) : t.paths ≠ [] := by
  cases t with
  | done => simp [Tree.paths]
  | fork e a b =>
    have ha := paths_nonempty a
    simp [Tree.paths, ha]

theorem Tree.path_span {n : Nat} (t : Tree n) :
    ∀ p ∈ t.paths, p.length ≤ t.depth := by
  induction t with
  | done => simp [Tree.paths, Tree.depth]
  | fork e a b ha hb =>
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [List.mem_append] at hq
    simp only [Tree.depth, List.length_append, List.length_cons, List.length_nil]
    rcases hq with hq|hq
    · exact Nat.succ_le_succ (Nat.le_trans (ha q hq) (Nat.le_max_left _ _))
    · exact Nat.succ_le_succ (Nat.le_trans (hb q hq) (Nat.le_max_right _ _))

theorem Tree.path_count {n : Nat} (t : Tree n) :
    t.paths.length ≤ 2^t.depth := by
  induction t with
  | done => simp [Tree.paths, Tree.depth]
  | fork e a b ha hb =>
    simp only [Tree.paths, Tree.depth, List.length_map, List.length_append, Nat.pow_succ]
    have h₁ := Nat.le_trans ha (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_max_left a.depth b.depth))
    have h₂ := Nat.le_trans hb (Nat.pow_le_pow_right (by decide : 0 < 2)
      (Nat.le_max_right a.depth b.depth))
    omega

private theorem run_paths_map {n : Nat} (ps : List (List (Fin n))) (w : List (Fin n)) :
    runMarks advance ps w = ps.map (fun p => runMarks pathStep p w) := by
  induction w generalizing ps with
  | nil => simp [runMarks]
  | cons a w ih => simp [runMarks, advance, ih, List.map_map, Function.comp_def]

private theorem path_step_iff {n : Nat} (p w : List (Fin n)) :
    runMarks pathStep p w = [] ↔ p <+ w := by
  induction w generalizing p with
  | nil => simp [runMarks]
  | cons a w ih =>
    cases p with
    | nil =>
      rw [runMarks, pathStep, ih]; simp
    | cons b p =>
      by_cases h : a = b
      · subst b
        simp [runMarks, pathStep, ih]
      · simp only [runMarks, pathStep, h, if_false, ih]
        constructor
        · exact List.Sublist.cons a
        · intro hh
          cases hh with
          | cons _ hs => exact hs
          | cons_cons _ hs => contradiction

/-- Greedy path clocks recognize ordered subsequences of the raw tape. -/
theorem paths_finished_iff {n : Nat} (ps : List (List (Fin n))) (w : List (Fin n)) :
    finished (runMarks advance ps w) ↔ ∀ p ∈ ps, p <+ w := by
  rw [run_paths_map]
  constructor
  · intro h p hp
    exact (path_step_iff p w).mp (h _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  · intro h q hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    exact (path_step_iff p w).mpr (h p hp)

private theorem strip_last {α : Type} {p w : List α} {a e : α}
    (h : p ++ [a] <+ w ++ [e]) : p <+ w ∧ (a = e ∨ p ++ [a] <+ w) := by
  obtain ⟨u,v,hs,hu,hv⟩ := List.sublist_append_iff.mp h
  have he : v = [] ∨ v = [e] := by
    cases hv with
    | cons _ hh => exact .inl (List.sublist_nil.mp hh)
    | cons_cons _ hh => simp [List.sublist_nil.mp hh]
  rcases he with rfl|rfl
  · rw [List.append_nil] at hs
    subst u
    exact ⟨(List.sublist_append_left _ _).trans hu, .inr hu⟩
  · have eq : p = u ∧ a = e := by
      have hrev := congrArg List.reverse hs
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.cons.injEq] at hrev
      exact ⟨by simpa using congrArg List.reverse hrev.2, hrev.1⟩
    exact ⟨eq.1 ▸ hu, .inl eq.2⟩

/-- A proof that a tree's nodes are legitimate local thresholds of a
transition system. At a fork, a nominated mark after both prerequisites
guarantees the parent; done leaves cost no mark. -/
inductive Sound {α : Type} {n : Nat} (next : α → Fin n → α) (good : α → Prop) :
    Tree n → (α → Prop) → Prop where
  | done (P : α → Prop) (start : ∀ x, good x → P x) : Sound next good .done P
  | fork (e : Fin n) (a b : Tree n) (A B P : α → Prop)
      (left : Sound next good a A) (right : Sound next good b B)
      (preserve : ∀ x f, good x → P x → P (next x f))
      (commit : ∀ x, good x → A x → B x → P (next x e)) :
      Sound next good (.fork e a b) P

private theorem reverse_word_induction {β : Type} {P : List β → Prop}
    (w : List β) (nil : P []) (snoc : ∀ u e, P u → P (u ++ [e])) : P w := by
  have h (u : List β) : P u.reverse := by
    induction u with
    | nil => exact nil
    | cons e u ih => rw [List.reverse_cons]; exact snoc _ _ ih
  simpa using h w.reverse

/-- If all DAG paths completed, its threshold has occurred. Recursing
on a tape prefix rather than taking independent passage times ensures the
last mark comes *strictly after* both prerequisite completions. -/
theorem Sound.of_paths {α : Type} {n : Nat} {next : α → Fin n → α}
    {good P : α → Prop} {tree : Tree n} (h : Sound next good tree P)
    (keep : ∀ x e, good x → good (next x e)) (x : α) (hx : good x)
    (w : List (Fin n)) (hw : finished (runMarks advance tree.paths w)) :
    P (runMarks next x w) := by
  have hg (u : List (Fin n)) : good (runMarks next x u) := by
    suffices ∀ y, good y → good (runMarks next y u) by exact this x hx
    induction u with
    | nil => exact fun _ h => h
    | cons e u ih => intro y hy; exact ih _ (keep y e hy)
  induction h generalizing w with
  | done _ h => exact h _ (hg w)
  | fork e a b A B P hA hB hp hc ia ib =>
    induction w using reverse_word_induction with
    | nil =>
      have hh := (paths_finished_iff _ _).mp hw
      obtain ⟨q,hq⟩ : ∃ q, q ∈ a.paths := by
        cases ht : a.paths with
        | nil => exact False.elim (a.paths_nonempty ht)
        | cons h t => exact ⟨h,by simp⟩
      have hz := hh (q++[e]) (List.mem_map.mpr ⟨q,List.mem_append_left _ hq,rfl⟩)
      simp at hz
    | snoc u f ih =>
      have hh := (paths_finished_iff _ _).mp hw
      rw [runMarks_append]
      change P (next (runMarks next x u) f)
      by_cases hfe : e = f
      · subst f
        apply hc _ (hg u)
        · apply ia u ((paths_finished_iff _ _).mpr ?_)
          intro q hq
          exact (strip_last (hh _ (List.mem_map.mpr ⟨q,List.mem_append_left _ hq,rfl⟩))).1
        · apply ib u ((paths_finished_iff _ _).mpr ?_)
          intro q hq
          exact (strip_last (hh _ (List.mem_map.mpr ⟨q,List.mem_append_right _ hq,rfl⟩))).1
      · apply hp _ f (hg u)
        apply ih ((paths_finished_iff _ _).mpr ?_)
        intro q hq
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
        exact (strip_last (hh _ hq)).2.resolve_left hfe


/-- Virtual service marks selected by the old physical state. A skipped mark
still advances that state; it is absent only from the virtual path trace. -/
def servedMarks {α : Type} {n : Nat}
    (next : α → Fin n → α) (enabled : α → Bool) (x : α) :
    List (Fin n) → List (Fin n)
  | [] => []
  | e :: w =>
      let tail := servedMarks next enabled (next x e) w
      if enabled x then e :: tail else tail

theorem servedMarks_snoc {α : Type} {n : Nat}
    (next : α → Fin n → α) (enabled : α → Bool) (x : α)
    (w : List (Fin n)) (e : Fin n) :
    servedMarks next enabled x (w ++ [e]) = servedMarks next enabled x w ++
      (if enabled (runMarks next x w) then [e] else []) := by
  induction w generalizing x with
  | nil => simp [servedMarks,runMarks] <;> rfl
  | cons a w ih =>
    simp only [List.cons_append,servedMarks,runMarks,ih]
    split <;> rfl

/-- A threshold tree on the original physical marks. Its preserve premise
covers both skipped and served marks; only commit needs an enabled gate. -/
inductive GatedSound {α : Type} {n : Nat} (next : α → Fin n → α)
    (good : α → Prop) (enabled : α → Bool) : Tree n → (α → Prop) → Prop where
  | done (P : α → Prop) (start : ∀ x, good x → P x) :
      GatedSound next good enabled .done P
  | fork (e : Fin n) (a b : Tree n) (A B P : α → Prop)
      (left : GatedSound next good enabled a A) (right : GatedSound next good enabled b B)
      (preserve : ∀ x f, good x → P x → P (next x f))
      (commit : ∀ x, good x → enabled x = true → A x → B x → P (next x e)) :
      GatedSound next good enabled (.fork e a b) P

/-- A completed virtual path and its physical state use exactly one raw
word, even if skipped letters change the physical state or its geometry. -/
theorem GatedSound.of_paths {α : Type} {n : Nat} {next : α → Fin n → α}
    {good P : α → Prop} {enabled : α → Bool} {tree : Tree n}
    (h : GatedSound next good enabled tree P)
    (keep : ∀ x e, good x → good (next x e)) (x : α) (hx : good x)
    (w : List (Fin n))
    (hw : finished (runMarks advance tree.paths (servedMarks next enabled x w))) :
    P (runMarks next x w) := by
  have hg (u : List (Fin n)) : good (runMarks next x u) := by
    suffices ∀ y, good y → good (runMarks next y u) by exact this x hx
    induction u with
    | nil => exact fun _ h => h
    | cons e u ih => intro y hy; exact ih _ (keep y e hy)
  induction h generalizing w with
  | done _ h => exact h _ (hg w)
  | fork e a b A B P hA hB hp hc ia ib =>
    induction w using reverse_word_induction with
    | nil =>
      have hh := (paths_finished_iff _ _).mp hw
      obtain ⟨q,hq⟩ : ∃ q, q ∈ a.paths := by
        cases ht : a.paths with
        | nil => exact False.elim (a.paths_nonempty ht)
        | cons h t => exact ⟨h,by simp⟩
      have hz := hh (q++[e]) (List.mem_map.mpr ⟨q,List.mem_append_left _ hq,rfl⟩)
      simp [servedMarks] at hz
    | snoc u f ih =>
      rw [servedMarks_snoc] at hw
      rw [runMarks_append]
      change P (next (runMarks next x u) f)
      cases hgate : enabled (runMarks next x u) with
      | false =>
        apply hp _ f (hg u)
        apply ih
        simpa only [hgate,Bool.false_eq_true,if_false,List.append_nil] using hw
      | true =>
        have hfull : finished (runMarks advance (Tree.fork e a b).paths
            (servedMarks next enabled x u ++ [f])) := by
          simpa [hgate] using hw
        have hh := (paths_finished_iff _ _).mp hfull
        by_cases hfe : e = f
        · subst f
          apply hc _ (hg u) hgate
          · apply ia u ((paths_finished_iff _ _).mpr ?_)
            intro q hq
            exact (strip_last (hh _ (List.mem_map.mpr ⟨q,List.mem_append_left _ hq,rfl⟩))).1
          · apply ib u ((paths_finished_iff _ _).mpr ?_)
            intro q hq
            exact (strip_last (hh _ (List.mem_map.mpr ⟨q,List.mem_append_right _ hq,rfl⟩))).1
        · apply hp _ f (hg u)
          apply ih ((paths_finished_iff _ _).mpr ?_)
          intro q hq
          obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
          exact (strip_last (hh _ hq)).2.resolve_left hfe

#print axioms GatedSound.of_paths

/-- Height-threshold grid of an open FIFO line with sites 1 through m
and edges 0 through m. For edge i to reach level k, predecessor edge
i−1 must already have reached k (when present) and successor edge i+1
must have reached k−1 (when present). -/
def fifoTree {n : Nat} (m : Nat) (edge : Nat → Fin n) :
    Nat → Nat → Nat → Tree n
  | 0, _, _ => .done
  | fuel+1, i, k =>
    if k = 0 then .done
    else .fork (edge i)
      (if i = 0 then .done else fifoTree m edge fuel (i-1) k)
      (if i < m then fifoTree m edge fuel (i+1) (k-1) else .done)

theorem fifoTree_span {n : Nat} (m : Nat) (edge : Nat → Fin n)
    (fuel i k : Nat) : (fifoTree m edge fuel i k).depth ≤ fuel := by
  induction fuel generalizing i k with
  | zero => simp [fifoTree, Tree.depth]
  | succ fuel ih =>
    by_cases hk : k = 0
    · simp [fifoTree, hk, Tree.depth]
    · simp only [fifoTree,hk,if_false,Tree.depth]
      apply Nat.succ_le_succ
      apply Nat.max_le.mpr
      constructor <;> split <;> first | exact ih _ _ | exact Nat.zero_le _

/-- The open-FIFO height clock needs precisely these local implications.
No probabilistic or independence premise enters the grid. -/
structure HeightRules {α : Type} {n : Nat} (next : α → Fin n → α)
    (good : α → Prop) (height : α → Nat → Nat) (m : Nat) (edge : Nat → Fin n) : Prop where
  mono : ∀ x e i, good x → i ≤ m → height x i ≤ height (next x e) i
  commit : ∀ x i k, good x → i ≤ m → 0 < k →
    (0 < i → k ≤ height x (i-1)) →
    (i < m → k-1 ≤ height x (i+1)) →
    k ≤ height (next x (edge i)) i

theorem fifoTree_sound {α : Type} {n : Nat} {next : α → Fin n → α}
    {good : α → Prop} {height : α → Nat → Nat} {m : Nat} {edge : Nat → Fin n}
    (rule : HeightRules next good height m edge) (fuel i k : Nat)
    (hi : i ≤ m) (hfuel : 2*k+i ≤ fuel) :
    Sound next good (fifoTree m edge fuel i k) (fun x => k ≤ height x i) := by
  induction fuel generalizing i k with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    exact .done _ (fun _ _ => Nat.zero_le _)
  | succ fuel ih =>
    by_cases hk : k = 0
    · subst k
      simp only [fifoTree,if_true]
      exact .done _ (fun _ _ => Nat.zero_le _)
    · simp only [fifoTree,hk,if_false]
      apply Sound.fork _ _ _ (fun x => 0 < i → k ≤ height x (i-1))
        (fun x => i < m → k-1 ≤ height x (i+1)) _
      · by_cases he : i = 0
        · simp only [he, if_true]
          exact .done _ (by omega)
        · rw [if_neg he]
          have hh := ih (i-1) k (by omega) (by omega)
          simpa only [show 0 < i from by omega, true_implies] using hh
      · by_cases he : i < m
        · rw [if_pos he]
          have hh := ih (i+1) (k-1) (by omega) (by omega)
          simpa only [he, true_implies] using hh
        · rw [if_neg he]
          exact .done _ (by omega)
      · exact fun x e hx hp => Nat.le_trans hp (rule.mono x e i hx hi)
      · exact fun x hx => rule.commit x i k hx hi (by omega)

/-- Explicit path family for the k-th outlet departure (when the outlet
height starts at zero). At m=n−2 and k=n the span is 3n−2. -/
def outletPaths {n : Nat} (m : Nat) (edge : Nat → Fin n) (k : Nat) :
    List (List (Fin n)) := (fifoTree m edge (2*k+m) m k).paths

theorem outletPaths_span {n : Nat} (m : Nat) (edge : Nat → Fin n) (k : Nat) :
    ∀ p ∈ outletPaths m edge k, p.length ≤ 2*k+m := by
  intro p hp
  exact Nat.le_trans (Tree.path_span _ p hp) (fifoTree_span ..)

theorem outletPaths_count {n : Nat} (m : Nat) (edge : Nat → Fin n) (k : Nat) :
    (outletPaths m edge k).length ≤ 2^(2*k+m+1) := by
  refine Nat.le_trans (Tree.path_count _) (Nat.pow_le_pow_right (by decide) ?_)
  exact Nat.le_trans (fifoTree_span ..) (Nat.le_succ _)

/-- Each complete common-mark dependency family certifies k outlet
departures in any process satisfying the elementary height rules. -/
theorem outletPaths_complete {α : Type} {n : Nat} {next : α → Fin n → α}
    {good : α → Prop} {height : α → Nat → Nat} {m : Nat} {edge : Nat → Fin n}
    (rule : HeightRules next good height m edge) (keep : ∀ x e, good x → good (next x e))
    (x : α) (hx : good x) (k : Nat) (w : List (Fin n))
    (hw : finished (runMarks advance (outletPaths m edge k) w)) :
    k ≤ height (runMarks next x w) m :=
  (fifoTree_sound rule (2*k+m) m k (Nat.le_refl _) (Nat.le_refl _)).of_paths
    keep x hx w hw

open RankSupplier

private def ahead (f : Nat → Nat) (cut : Nat) : Nat → Nat
  | 0 => 0
  | a+1 => ahead f cut a + if cut < a then f a else 0

private theorem ahead_add (f g : Nat → Nat) (cut cap : Nat) :
    ahead (fun j => f j+g j) cut cap = ahead f cut cap + ahead g cut cap := by
  induction cap with
  | zero => rfl
  | succ a ih => simp only [ahead,ih]; by_cases h : cut<a <;> simp [h] <;> omega

private theorem ahead_single (i cut cap : Nat) :
    ahead (fun j => if j=i then 1 else 0) cut cap = if cut < i ∧ i < cap then 1 else 0 := by
  induction cap with
  | zero => simp [ahead]
  | succ a ih =>
    simp only [ahead,ih]
    by_cases hi : a=i <;> by_cases hc : cut<i <;> by_cases ha : i<a <;>
      by_cases ht : cut<a <;> simp [hi,hc,ha,ht] <;> omega

private theorem ahead_near (f : Nat → Nat) (i cap : Nat) (hi : i<cap) :
    ahead f i cap + f i = ahead f (i-1) cap ∨ i=0 := by
  by_cases hz : i=0
  · exact .inr hz
  left
  induction cap with
  | zero => omega
  | succ a ih =>
    by_cases h : i=a
    · subst a
      have hzero (k : Nat) (hk : k≤i) : ahead f (i-1) k = ahead f i k := by
        induction k with
        | zero => rfl
        | succ k ih =>
          simp only [ahead, ih (by omega), if_neg (show ¬i-1<k by omega),
            if_neg (show ¬i<k by omega)]
      simp [ahead,hzero i (Nat.le_refl _),show i-1<i by omega]
    · have h0 := ih (by omega)
      simp only [ahead,if_pos (show i<a by omega),if_pos (show i-1<a by omega)]
      omega

private def valStock {n : Nat} (z : Virtual n) (i : Nat) : Nat :=
  if h : i<n then (z.stock ⟨i,h⟩).toNat else 0

/-- Cumulative currents initialized by the number of residents strictly
after the indexed edge. Their differences are the resident bits, and the
current at the outlet is exactly the counter of actual virtual departures. -/
def current {n : Nat} (z : Virtual n) (i : Nat) : Nat :=
  z.departures + ahead (valStock z) i (n-1)

private theorem current_adjacent {n : Nat} (z : Virtual n) (i : Nat)
    (hi : 0 < i) (hb : i < n-1) :
    current z i + valStock z i = current z (i-1) := by
  have hh := (ahead_near (valStock z) i (n-1) hb).resolve_right (by omega)
  unfold current
  omega

private theorem valStock_le {n : Nat} (z : Virtual n) (i : Nat) :
    valStock z i ≤ 1 := by
  unfold valStock
  split
  · cases z.stock _ <;> decide
  · decide

theorem current_outlet {n : Nat} (z : Virtual n) :
    current z (n-2) = z.departures := by
  have h : ∀ cap, cap ≤ n-1 → ahead (valStock z) (n-2) cap = 0 := by
    intro cap
    induction cap with
    | zero => simp [ahead]
    | succ a ih =>
      intro hk
      simp [ahead,ih (by omega),show ¬ n-2<a by omega]
  simp [current,h _ (Nat.le_refl _)]

private theorem find_edge {n : Nat} (v i : Fin n) :
    (List.finRange n).find? (fun j => liftedSite v j.val == liftedSite v i.val) = some i := by
  have h : ∀ j : Fin n, (liftedSite v j.val == liftedSite v i.val) = (j==i) := by
    intro j
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨fun hh => Fin.ext (liftedSite_inj v j.isLt i.isLt hh),fun hh => congrArg (fun x : Fin n => liftedSite v x.val) hh⟩
  have hf : (fun j : Fin n => liftedSite v j.val == liftedSite v i.val) = (· == i) := funext h
  rw [hf]
  cases hh : (List.finRange n).find? (· == i) with
  | none => exact False.elim ((List.find?_eq_none.mp hh) i (List.mem_finRange i) (by simp))
  | some j =>
    have hj := List.find?_some hh
    exact congrArg some (beq_iff_eq.mp hj)

private theorem ahead_diff (f g : Nat → Nat) (remove add : Nat → Nat)
    (cut cap : Nat) (h : ∀ j, g j + remove j = f j + add j) :
    ahead g cut cap + ahead remove cut cap = ahead f cut cap + ahead add cut cap := by
  rw [← ahead_add, ← ahead_add]
  exact congrArg (fun a => ahead a cut cap) (funext h)

private def unitAt (i j : Nat) : Nat := if j=i then 1 else 0

private theorem zero_ahead (cut cap : Nat) : ahead (fun _ => 0) cut cap = 0 := by
  induction cap with
  | zero => rfl
  | succ a ih => simp [ahead,ih]

/-- Exact change rule for the cumulative currents: injection, transfer,
and deletion each increase only the serviced edge, when its FIFO move
actually occurs. -/
theorem current_virtualStep {n : Nat} (hn : 4 ≤ n) (v : Fin n)
    (z : Virtual n) (i j : Nat) (hi : i ≤ n-2) (hj : j ≤ n-2) :
    current (virtualStep v z (liftedSite v i)) j = current z j +
      (if j=i ∧ (i=0 ∨ valStock z i=1) ∧ (i=n-2 ∨ valStock z (i+1)=0) then 1 else 0) := by
  let fi : Fin n := ⟨i,by omega⟩
  let fj : Fin n := ⟨i+1,by omega⟩
  have fiV : fi.val = i := rfl
  have fjV : fj.val = i+1 := rfl
  have hs : valStock z i = (z.stock fi).toNat := by simp [valStock, fi, show i<n by omega]
  have ht : valStock z (i+1) = (z.stock fj).toNat := by simp [valStock, fj, show i+1<n by omega]
  unfold virtualStep
  rw [show liftedSite v i = liftedSite v fi.val from rfl, find_edge]
  simp only [fiV, dif_pos (show i+1<n by omega)]
  change current
      (if i=0 then ⟨fun l => if l=fj then true else z.stock l,z.departures⟩
       else if !z.stock fi then z
       else if fj.val+1=n then ⟨fun l => if l=fi then false else z.stock l,z.departures+1⟩
       else if z.stock fj then z
       else ⟨fun l => if l=fi then false else if l=fj then true else z.stock l,z.departures⟩) j = _
  have hFi (a : Nat) (ha : a<n) :
      (⟨a,ha⟩ : Fin n) = fi ↔ a=i := ⟨fun H => congrArg Fin.val H, fun H => Fin.ext H⟩
  have hFj (a : Nat) (ha : a<n) :
      (⟨a,ha⟩ : Fin n) = fj ↔ a=i+1 := ⟨fun H => congrArg Fin.val H, fun H => Fin.ext H⟩
  by_cases hzero : i=0
  · rw [if_pos hzero]
    let y : Virtual n := ⟨fun l => if l=fj then true else z.stock l,z.departures⟩
    change current y j = _
    cases hbit : z.stock fj
    · have hh : ∀ a, valStock y a + 0 = valStock z a + unitAt (i+1) a := by
        intro a
        by_cases ha : a<n
        · by_cases hf : a=i+1
          · subst a; simp [valStock,y,unitAt,ha,hbit,fj]
          · simp [valStock,y,unitAt,ha,hFj,hf]
        · simp [valStock,ha,unitAt,show a≠i+1 by omega]
      have hd := ahead_diff _ _ _ _ j (n-1) hh
      rw [zero_ahead, show ahead (unitAt (i+1)) j (n-1) =
        (if j < i+1 ∧ i+1<n-1 then 1 else 0) from ahead_single ..] at hd
      have hstock : valStock z (i+1) = 0 := by rw [ht,hbit]; rfl
      have hcond : (i=0 ∨ valStock z i=1) ∧ (i=n-2 ∨ valStock z (i+1)=0) :=
        ⟨.inl hzero,.inr hstock⟩
      change z.departures+ahead (valStock y) j (n-1) =
        z.departures+ahead (valStock z) j (n-1)+_ 
      by_cases hji : j=i
      · simp only [hji,hcond.1,hcond.2,and_self,if_true]
        simp [hji, show i+1<n-1 by omega] at hd
        omega
      · rw [if_neg (fun h => hji h.1)]
        have hnj : ¬ j<i+1 := by omega
        simp [hnj] at hd
        omega
    · have hy : y=z := by
        cases z with
        | mk zstock dep =>
          have hb : zstock fj = true := hbit
          simp only [y,Virtual.mk.injEq,and_true]
          funext a
          by_cases ha : a=fj <;> simp [ha,hb]
      rw [hy]
      have hstock : valStock z (i+1) = 1 := by rw [ht,hbit]; rfl
      rw [if_neg (fun h => h.2.2.elim (by omega) (by omega)),Nat.add_zero]
  · rw [if_neg hzero]
    cases hbit : z.stock fi
    · simp [hbit,hs,hzero]
    · simp only [Bool.not_true,Bool.false_eq_true,if_false]
      by_cases hout : i=n-2
      · have hof : fj.val+1=n := by omega
        rw [if_pos hof]
        let y : Virtual n := ⟨fun l => if l=fi then false else z.stock l,z.departures+1⟩
        change current y j = _
        have hh : ∀ a, valStock y a + unitAt i a = valStock z a + 0 := by
          intro a
          by_cases ha : a<n
          · by_cases hf : a=i
            · subst a; simp [valStock,y,unitAt,ha,hbit,fi]
            · simp [valStock,y,unitAt,ha,hFi,hf]
          · simp [valStock,ha,unitAt,show a≠i by omega]
        have hd := ahead_diff _ _ _ _ j (n-1) hh
        rw [zero_ahead, show ahead (unitAt i) j (n-1) =
          (if j<i ∧ i<n-1 then 1 else 0) from ahead_single ..] at hd
        have hstock : valStock z i = 1 := by rw [hs,hbit]; rfl
        have hcond : (i=0 ∨ valStock z i=1) ∧ (i=n-2 ∨ valStock z (i+1)=0) :=
          ⟨.inr hstock,.inl hout⟩
        change z.departures+1+ahead (valStock y) j (n-1) =
          z.departures+ahead (valStock z) j (n-1)+_
        by_cases hji : j=i
        · rw [if_pos ⟨hji,hcond⟩]
          subst j
          simp at hd
          omega
        · rw [if_neg (fun h => hji h.1)]
          simp [show j<i by omega,show i<n-1 by omega] at hd
          omega
      · have hof : ¬ fj.val+1=n := by omega
        rw [if_neg hof]
        cases hnew : z.stock fj
        · simp only [Bool.false_eq_true,if_false]
          let y : Virtual n := ⟨fun l => if l=fi then false else if l=fj then true else z.stock l,z.departures⟩
          change current y j = _
          have hh : ∀ a, valStock y a + unitAt i a = valStock z a + unitAt (i+1) a := by
            intro a
            by_cases ha : a<n
            · by_cases hf : a=i
              · subst a; simp [valStock,y,unitAt,ha,hbit,fi]
              · by_cases hf' : a=i+1
                · subst a; simp [valStock,y,unitAt,ha,hFi,hnew,fj]
                · simp [valStock,y,unitAt,ha,hFi,hFj,hf,hf']
            · simp [valStock,ha,unitAt,show a≠i by omega,show a≠i+1 by omega]
          have hd := ahead_diff _ _ _ _ j (n-1) hh
          rw [show ahead (unitAt i) j (n-1) =
            (if j<i ∧ i<n-1 then 1 else 0) from ahead_single ..,
            show ahead (unitAt (i+1)) j (n-1) =
            (if j<i+1 ∧ i+1<n-1 then 1 else 0) from ahead_single ..] at hd
          have hstock : valStock z i = 1 := by rw [hs,hbit]; rfl
          have hstock' : valStock z (i+1) = 0 := by rw [ht,hnew]; rfl
          have hcond : (i=0 ∨ valStock z i=1) ∧ (i=n-2 ∨ valStock z (i+1)=0) :=
            ⟨.inr hstock,.inr hstock'⟩
          change z.departures+ahead (valStock y) j (n-1) =
            z.departures+ahead (valStock z) j (n-1)+_
          simp only [show i<n-1 by omega,show i+1<n-1 by omega,and_true] at hd
          by_cases hji : j=i
          · rw [if_pos ⟨hji,hcond⟩]
            subst j
            simp at hd
            omega
          · rw [if_neg (fun h => hji h.1)]
            by_cases hjl : j<i
            · simp [hjl,show j<i+1 by omega] at hd; omega
            · simp [hjl,show ¬ j<i+1 by omega] at hd; omega
        · simp [hnew,ht,hout]


private theorem current_mono {n : Nat} (hn : 4 ≤ n) (v e : Fin n) (z : Virtual n)
    (j : Nat) (hj : j≤n-2) : current z j ≤ current (virtualStep v z e) j := by
  cases h : (List.finRange n).find? (fun j => liftedSite v j.val == e) with
  | none =>
    have hh : virtualStep v z e = z := by simp [virtualStep,h]
    rw [hh]; exact Nat.le_refl _
  | some i =>
    have hb : (liftedSite v i.val == e) = true :=
      List.find?_some (p := fun j : Fin n => liftedSite v j.val == e) h
    have he := beq_iff_eq.mp hb
    by_cases hi : i.val ≤ n-2
    · rw [← he,current_virtualStep hn v z _ j hi hj]
      exact Nat.le_add_right _ _
    · have hh : virtualStep v z e = z := by
        simp [virtualStep,h,show ¬ i.val+1<n by omega]
      rw [hh]; exact Nat.le_refl _

/-- Literal RankSupplier.Virtual implements the local dependency-grid
rules, including its sink and source boundaries and irrelevant marks. -/
theorem virtual_height_rules {n : Nat} (hn : 4 ≤ n) (v : Fin n) :
    HeightRules (virtualStep v) (fun _ => True) current (n-2) (liftedSite v) := by
  refine ⟨fun z e i _ hi => current_mono hn v e z i hi, ?_⟩
  intro z i k _ hi hk left right
  by_cases hdone : k ≤ current z i
  · exact Nat.le_trans hdone (current_mono hn v _ z i hi)
  · have bound : k-1 ≤ current z i := by
      by_cases hz : 0<i
      · have ha := current_adjacent z i hz (by omega)
        have hb := valStock_le z i
        have hc := left hz
        omega
      · have ha := current_adjacent z (i+1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at ha
        have hc := right (by omega)
        omega
    have hleft : i=0 ∨ valStock z i=1 := by
      by_cases hz : 0<i
      · right
        have ha := current_adjacent z i hz (by omega)
        have hb := valStock_le z i
        have hc := left hz
        omega
      · exact .inl (by omega)
    have hright : i=n-2 ∨ valStock z (i+1)=0 := by
      by_cases hz : i<n-2
      · right
        have ha := current_adjacent z (i+1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at ha
        have hc := right hz
        omega
      · exact .inl (by omega)
    rw [current_virtualStep hn v z i i hi hi,if_pos ⟨rfl,hleft,hright⟩]
    omega

/-- Fixed-supplier virtual FIFO certificate. The unfolded dependency
family controls common marks, from arbitrary virtual initial occupancy
and without any independence between paths. -/
theorem virtual_outlet_paths {n : Nat} (hn : 4 ≤ n) (v : Fin n) (z : Virtual n) :
    ∃ (L : Nat) (paths : List (List (Fin n))), L ≤ 4*n ∧
      (∀ q ∈ paths, q.length ≤ L) ∧ paths.length ≤ 2^(L+1) ∧
      ∀ w, finished (runMarks GGTiming.advance paths w) →
        n ≤ (runMarks (virtualStep v) z w).departures := by
  refine ⟨2*n+(n-2),outletPaths (n-2) (liftedSite v) n,by omega,
    outletPaths_span (n-2) (liftedSite v) n,outletPaths_count ..,?_⟩
  intro w hw
  have h := outletPaths_complete (virtual_height_rules hn v)
    (fun _ _ _ => True.intro) z True.intro n w hw
  rwa [current_outlet] at h

end L4.QueueDAG

#print axioms L4.QueueDAG.outletPaths_complete
#print axioms L4.QueueDAG.current_virtualStep
#print axioms L4.QueueDAG.virtual_outlet_paths
