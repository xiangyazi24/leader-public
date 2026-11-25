import Leader.L4.ShortFiveParked
import Leader.L4.PhysicalShortSheet
import Leader.L4.ShortNORCover

namespace L4.ShortFiveWatchReplay
open AllSizeProtocol PhysicalCustody ShortResetMIS1Ring ShortResetChart ShortResetCycle
open ShortResetWatch ShortSimulLocal PhysicalShortSheet

def labels {n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h) : List (Fin n) :=
  WatchedUnionIID.chartsWatch (List.ofFn cs)

def Covered {n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h) (q : Fin n) : Prop :=
  ∃ i : Fin 5, ∃ j : Nat, j<(cs i).L ∧ q=nextAt (cs i).root j

def Internal {n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h) (e : Fin n) : Prop :=
  Covered cs e ∧ Covered cs (rightNeighbor e)

def Agree {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h) (x y : Raw s n) : Prop :=
  ∀ q, Covered cs q → (x q).mis1=(y q).mis1

theorem watch_card {n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (small : ∀ i, (cs i).L≤9) : (labels cs).length≤50 := by
  have B := WatchedUnionIID.chartsWatch_bound (List.ofFn cs) (fun C E=>by
    obtain ⟨i,I⟩ := List.mem_ofFn.mp E
    rw [←I]
    exact small i)
  simpa only [labels,List.length_ofFn] using B

theorem included {n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h) (i : Fin 5)
    (e : Fin n) (H : e ∈ watch (cs i)) : e∈labels cs :=
  List.mem_flatMap.mpr ⟨cs i,List.mem_ofFn.mpr ⟨i,rfl⟩,H⟩

theorem outside_agree {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (x : Raw s n) (e : Fin n) (E : e∉labels cs) : Agree cs (rawNext s x e) x := by
  rintro q ⟨i,j,J,rfl⟩
  exact outside_byte (cs i) x e (fun H=>E (included cs i e H)) j J

private theorem agree_trans {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (x y z : Raw s n) (A : Agree cs x y) (B : Agree cs y z) : Agree cs x z :=
  fun q Q=>(A q Q).trans (B q Q)

/-- The pair-local replay guarantee is needed only at matched
prescribed-word labels. Unmatched watched labels end the attempt. -/
theorem internal_step_agrees {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (x y : Raw s n) (X : Fiber h x) (Y : Fiber h y)
    (A : Agree cs x y) (e : Fin n) (E : Internal cs e) :
    Agree cs (rawNext s x e) (rawNext s y e) := by
  let r := rightNeighbor e
  have L : mask .mis1 x e=mask .mis1 y e := (X.2 e).trans (Y.2 e).symm
  have R : mask .mis1 x r=mask .mis1 y r := (X.2 r).trans (Y.2 r).symm
  have P := exact_raw_step .mis1 x e
  have Q := exact_raw_step .mis1 y e
  intro q J
  have Px := congrFun P q
  have Qy := congrFun Q q
  change (rawNext s x e q).mis1=_ at Px
  change (rawNext s y e q).mis1=_ at Qy
  rw [Px,Qy]
  unfold sliceStep
  dsimp only
  change (if q=e then _ else if q=r then _ else _)=(if q=e then _ else if q=r then _ else _)
  simp only [bytes]
  rw [L,R,A e E.1,A r E.2,A q J]

def keep {n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h) (w : List (Fin n)) :
    List (Fin n) :=
  w.filter (fun e=>decide (e∈labels cs))

/-- Outside labels are still executed; they stutter only under the
covered-byte observation. This conclusion deliberately compares
just the target view and not the full physical configuration. -/
theorem same_filtered_replay {s n : Nat} {h : Fin n → Bool} (cs : Fin 5 → Chart h)
    (N : 5≤n) (x y : Raw s n) (X : Fiber h x) (Y : Fiber h y) (A : Agree cs x y)
    (w u : List (Fin n)) (word : keep cs w=u) (ok : ∀ e∈u, Internal cs e) :
    Agree cs (rawRun x w) (rawRun y u) := by
  have closed (z : Raw s n) (e : Fin n) (Z : Fiber h z) : Fiber h (rawNext s z e) :=
    ⟨h2_ready_closed N z e Z.1,fun q=>(H1.raw_h1_selected_frozen N z e q Z.1.1).trans (Z.2 q)⟩
  induction w generalizing x y u with
  | nil =>
    subst u
    exact A
  | cons e w ih =>
    by_cases W : e∈labels cs
    · have E : e::keep cs w=u := by simpa [keep,W] using word
      rw [←E] at ok ⊢
      exact ih _ _ (closed x e X) (closed y e Y)
        (internal_step_agrees cs x y X Y A e (ok e (by simp))) _ rfl
        (fun z Z=>ok z (List.mem_cons_of_mem e Z))
    · have E : keep cs w=u := by simpa [keep,W] using word
      exact ih _ _ (closed x e X) Y
        (agree_trans cs _ _ _ (outside_agree cs x e W) A) _ E ok

/-- If an explicitly certified local classifier fires in the prescribed
word, it also fires on the unchanged physical tape. Every spectator
mark and all endpoint/cut positions remain in the proof. -/
theorem publication_on_original_word {s n : Nat} {J : Type} {h : Fin n → Bool}
    (cs : Fin 5 → Chart h) (N : 5≤n) (classify : Raw s n → Fin n → Option J)
    (pairLocal : ∀ x y e, Fiber h x → Fiber h y → Agree cs x y → Internal cs e →
      classify x e=classify y e)
    (x y : Raw s n) (X : Fiber h x) (Y : Fiber h y) (A : Agree cs x y)
    (w u : List (Fin n)) (word : keep cs w=u) (ok : ∀ e∈u, Internal cs e)
    (j : J) (event : j∈ShortNORCover.publications (rawNext s) classify y u) :
    j∈ShortNORCover.publications (rawNext s) classify x w := by
  have closed (z : Raw s n) (e : Fin n) (Z : Fiber h z) : Fiber h (rawNext s z e) :=
    ⟨h2_ready_closed N z e Z.1,fun q=>(H1.raw_h1_selected_frozen N z e q Z.1.1).trans (Z.2 q)⟩
  induction w generalizing x y u with
  | nil =>
    have U : u=[] := word.symm
    rw [U] at event
    exact (List.not_mem_nil event).elim
  | cons e w ih =>
    by_cases W : e∈labels cs
    · have E : e::keep cs w=u := by simpa [keep,W] using word
      rw [←E] at ok event
      have I := ok e (by simp)
      have same := pairLocal x y e X Y A I
      simp only [ShortNORCover.publications,same]
      simp only [ShortNORCover.publications] at event
      have tail (T : j∈ShortNORCover.publications (rawNext s) classify (rawNext s y e) (keep cs w)) :=
        ih _ _ (closed x e X) (closed y e Y) (internal_step_agrees cs x y X Y A e I) _ rfl
          (fun z Z=>ok z (List.mem_cons_of_mem e Z)) T
      cases C : classify y e
      · simp only [C] at event
        exact tail event
      · simp only [C] at event
        rcases List.mem_cons.mp event with B|B
        · exact List.mem_cons.mpr (.inl B)
        · exact List.mem_cons.mpr (.inr (tail B))
    · have E : keep cs w=u := by simpa [keep,W] using word
      have T := ih _ _ (closed x e X) Y
        (agree_trans cs _ _ _ (outside_agree cs x e W) A) _ E ok event
      unfold ShortNORCover.publications
      cases classify x e
      · exact T
      · exact List.mem_cons_of_mem _ T

#print axioms watch_card
#print axioms included
#print axioms outside_agree
#print axioms internal_step_agrees
#print axioms same_filtered_replay
#print axioms publication_on_original_word
end L4.ShortFiveWatchReplay
