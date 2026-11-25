import Leader.L4.Height.ObserverGeometry
import Leader.L4.Height.ObserverTrip
import Leader.L4.Height.ObserverBudget
import Leader.L4.EntranceCover

namespace L4.Height.ObserverRank
open ObserverDirty ObserverTrip ObserverGeometry
variable {n : Nat} {X : Type} {r : Fin n}
noncomputable section

inductive Cursor (n : Nat) where
  | cover (todo : List (Fin n))
  | dirty (phase : Phase n)
  | trip (stage : Stage)

abbrev allEdges (n : Nat) := List.ofFn (fun e : Fin n => e)
def initialPhase (hn : 0<n) : Phase n := .outward (firstHop hn)

def transition (hn : 0<n) (m : Machine X r) (x : X) (e : Fin n) : Cursor n → Cursor n
  | .cover todo =>
    let t := EntranceCover.advance todo e
    if t=[] then .dirty (initialPhase hn) else .cover t
  | .dirty p =>
    let k := index r e
    if Launches (m.line x) k then .trip (.out 0) else .dirty (p.advance hn (m.line x) k)
  | .trip t => .trip (ObserverTrip.advance (m.line x) (index r e) t)

def debt (m : Machine X r) (x : X) : Cursor n → Nat
  | .cover todo => todo.length + (2*n+4) + (2*n+3)
  | .dirty p => p.debt (m.line x) + (2*n+3)
  | .trip t => rank n t

abbrev physical (m : Machine X r) (x : X) (e : Fin n) := m.next x (index r e)

def Cert (m : Machine X r) (covered : List (Fin n) → X → Prop) (x : X) : Cursor n → Prop
  | .cover todo => todo≠[] ∧ covered todo x
  | .dirty p => covered [] x ∧ p≠.launched ∧ p.cert (m.line x)
  | .trip t => covered [] x ∧ Shape n (m.line x) t ∧ Sound m x t

theorem certified_step (hn : 2≤n) (m : Machine X r) (G : List (Fin n) → X → Prop)
    (latch : ∀ t x e, G t x → G (EntranceCover.advance t e) (physical m x e))
    (x : X) (e : Fin n) (c : Cursor n) (h : Cert m G x c) :
    Cert m G (physical m x e) (transition (by omega) m x e c) := by
  let k := index r e
  have pos : 0<n := by omega
  cases c with
  | cover todo =>
    have C := latch todo x e h.2
    by_cases eq : EntranceCover.advance todo e=[]
    · rw [eq] at C
      simpa [transition,eq,Cert,initialPhase,C] using
        (initial_dirty pos (m.line (physical m x e))).1
    · simpa only [transition,if_neg eq,Cert] using And.intro eq C
  | dirty p =>
    have C : G [] (physical m x e) := latch [] x e h.1
    by_cases launch : Launches (m.line x) k
    · have sh := sound_after_launch m hn x k launch
      simpa only [transition,(show k=index r e from rfl).symm,if_pos launch,Cert] using And.intro C sh
    · have res := dirty_advance hn (m.line x) p k (m.turnBit x k) h.2.2 h.2.1
      have live : p.advance pos (m.line x) k≠.launched := by
        intro eq
        exact ((advance_launched_iff pos _ _ _).1 eq).elim h.2.1 launch
      change Cert m G (m.next x k) (if Launches _ k then _ else .dirty _)
      rw [if_neg launch]
      exact ⟨C,live,m.line_update x k ▸ res.1⟩
  | trip t =>
    exact ⟨latch [] x e h.1,machine_shape_step m hn x k t h.2.1,
      sound_step m hn x k t h.2.1 h.2.2⟩

private theorem cover_lengths {todo : List (Fin n)} {e : Fin n} :
    (EntranceCover.advance todo e).length ≤ todo.length := by
  cases todo with
  | nil => exact Nat.le_refl _
  | cons a tail => by_cases h : e=a <;> simp [EntranceCover.advance,h]

private theorem cover_debt (hn : 0<n) (m : Machine X r) (x : X) (todo : List (Fin n)) (e : Fin n) :
    debt m (physical m x e) (transition hn m x e (.cover todo)) =
      (EntranceCover.advance todo e).length+(2*n+4)+(2*n+3) := by
  by_cases eq : EntranceCover.advance todo e=[]
  · simp [transition,eq,debt,initialPhase,(initial_dirty hn _).2]
  · simp [transition,eq,debt]

private theorem dirty_debt (hn : 0<n) (m : Machine X r) (x : X) (p : Phase n) (e : Fin n) :
    debt m (physical m x e) (transition hn m x e (.dirty p)) =
      (p.advance hn (m.line x) (index r e)).debt (m.line (physical m x e))+(2*n+3) := by
  by_cases H : Launches (m.line x) (index r e)
  · simp [transition,H,debt,rank,Phase.advance,Phase.debt]
  · simp [transition,H,debt]

def Running : Cursor n → Prop
  | .trip .idle => False
  | .trip (.out _) | .trip (.back _) | .trip .pending | .dirty _ | .cover _ => True

private theorem trip_live {s : Stage} (H : Running (.trip s : Cursor n)) : s≠.idle := by
  intro eq; subst s; exact H

theorem comparison (hn : 2≤n) (m : Machine X r) (G : List (Fin n) → X → Prop)
    (x : X) (c : Cursor n) (h : Cert m G x c) (live : Running c) :
    (∀ e, debt m (physical m x e) (transition (by omega) m x e c) ≤ debt m x c) ∧
    (∃ e, debt m (physical m x e) (transition (by omega) m x e c) < debt m x c) := by
  have pos : 0<n := by omega
  cases c with
  | cover todo =>
    constructor
    · intro e
      rw [cover_debt]
      exact Nat.add_le_add_right (Nat.add_le_add_right cover_lengths _) _
    · cases todo with
      | nil => exact (h.1 rfl).elim
      | cons a tail =>
        refine ⟨a,?_⟩
        rw [cover_debt]; simp [debt,EntranceCover.advance]
  | dirty p =>
    have W (e : Fin n) := (dirty_advance hn (m.line x) p (index r e) (m.turnBit x (index r e)) h.2.2 h.2.1).2
    constructor
    · intro e
      rw [dirty_debt]
      change _ ≤ p.debt (m.line x)+(2*n+3)
      simp only [physical,m.line_update]
      exact Nat.add_le_add_right (W e).1 _
    · let k := p.nominate pos (m.line x)
      refine ⟨edge r k,?_⟩
      rw [dirty_debt]
      have strict := (W (edge r k)).2 (index_edge r k)
      change _ < p.debt (m.line x) + (2*n+3)
      simp only [physical,m.line_update]
      omega
  | trip t =>
    refine ⟨fun e => rank_step (index r e) h.2.1 (trip_live live),?_⟩
    obtain ⟨k,hk⟩ := nominated_step hn h.2.1 (trip_live live)
    refine ⟨edge r k,?_⟩
    change rank n (ObserverTrip.advance (m.line x) (index r (edge r k)) t) < rank n t
    rwa [index_edge]

/-- The three phase credits live on one original edge clock. -/
theorem observer_ghost {S : Type} (hn : 4≤n) (m : Machine X r)
    (raw : S → Fin n → S) (F : X → S)
    (comm : ∀ x e, F (physical m x e)=raw (F x) e)
    (G : List (Fin n) → X → Prop)
    (latch : ∀ t x e, G t x → G (EntranceCover.advance t e) (physical m x e))
    (P : S → Prop)
    (cut : ∀ x, G [] x → Shape n (m.line x) .idle → Sound m x .idle → P (F x))
    (start : X) (initial : G (allEdges n) start) :
    ∃ (Y : Type) (N : Y → Fin n → Y) (project : Y → S) (d : Y → Nat) (y : Y),
      project y=F start ∧ d y≤5*n+7 ∧
      (∀ z e, project (N z e)=raw (project z) e) ∧
      (∀ z e, ¬ P (project z) → d (N z e)≤d z) ∧
      (∀ z, ¬ P (project z) → ∃ e, d (N z e)+1≤d z) := by
  let Y := {z : X × Cursor n // Cert m G z.1 z.2}
  let N (z : Y) (e : Fin n) : Y :=
    ⟨(physical m z.val.1 e,transition (by omega) m z.val.1 e z.val.2),
      certified_step (by omega) m G latch _ _ _ z.property⟩
  let y : Y := ⟨(start,.cover (allEdges n)),by
    refine ⟨?_,initial⟩
    intro eq
    have L := congrArg List.length eq
    simp [allEdges] at L
    omega⟩
  have live (z : Y) (miss : ¬ P (F z.val.1)) : Running z.val.2 := by
    obtain ⟨⟨x,c⟩,hz⟩ := z
    cases c with
    | cover t => exact True.intro
    | dirty p => exact True.intro
    | trip t =>
      cases t with
      | idle => exact (miss (cut _ hz.1 hz.2.1 hz.2.2)).elim
      | out _ | back _ | pending => exact True.intro
  refine ⟨Y,N,fun z => F z.val.1,fun z => debt m z.val.1 z.val.2,y,rfl,?_,
    fun z e => comm _ e,?_,?_⟩
  · simp [y,debt,allEdges] <;> omega
  · intro z e miss
    exact (comparison (by omega) m G _ _ z.property (live z miss)).1 e
  · intro z miss
    exact (comparison (by omega) m G _ _ z.property (live z miss)).2

end
end L4.Height.ObserverRank
