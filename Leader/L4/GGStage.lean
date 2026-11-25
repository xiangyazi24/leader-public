import Leader.L4.GGStockPhysical
import Leader.L4.GGTiming

/-! Literal stopped two-ghost preparation interface. The three coordinates
are proof-side lifts, not protocol fields. -/
namespace L4.GGStage

structure Heads where
  i : Nat
  j : Nat
  k : Nat
  deriving DecidableEq

structure Obs (p c n : Nat) where
  config : Config p c n
  heads : Heads
  stopped : Bool

/-- `d` is a clockwise bond coordinate; its responder heads any carried
mark. The root at lift 0 uses the incoming-offset n−1. -/
def incoming {n : Nat} (base : Fin n) (d : Nat) : Fin n :=
  liftedSite base (d+n-1)

theorem incoming_right {n : Nat} (base : Fin n) (d : Nat) :
    rightNeighbor (incoming base d) = liftedSite base d := by
  have hn : 0 < n := Nat.zero_lt_of_lt base.isLt
  unfold incoming
  rw [← liftedSite_succ,show d+n-1+1=d+n by omega]
  apply Fin.ext
  change (base.val+(d+n))%n = (base.val+d)%n
  rw [← Nat.add_assoc]
  exact Nat.add_mod_right _ _

def rootAt {p c n : Nat} (x : Config p c n) (base : Fin n) (d : Nat) : Prop :=
  (x (incoming base d)).mark = true

def AmbientConsecutive {p c n : Nat} (x : Config p c n) (base : Fin n) (a : Heads) : Prop :=
  a.i < a.j ∧ a.j < a.k ∧ a.k < a.i+n ∧
    rootAt x base a.i ∧ rootAt x base a.j ∧ rootAt x base a.k ∧
    (∀ d, a.i < d → d < a.j → ¬ rootAt x base d) ∧
    (∀ d, a.j < d → d < a.k → ¬ rootAt x base d)

def InitialCut {p c n : Nat} (x : Config p c n) (base : Fin n) (a : Heads) : Prop :=
  MCOV x ∧ COV x ∧ 2*(a.k-a.i)+2 < n ∧ AmbientConsecutive x base a ∧
    (x (liftedSite base a.i)).leader = false ∧ (x (liftedSite base a.j)).leader = false

def init {p c n : Nat} (x : Config p c n) (a : Heads) : Obs p c n := ⟨x,a,false⟩

def moved {p c n : Nat} (x : Config p c n) (base e : Fin n) (d : Nat) : Bool :=
  (e == incoming base d) && geometricPay (x e) (x (rightNeighbor e))

/-- An incoming paid move retires the donor identity if its new head
already has a mark on its incoming bond. MCOV covers existing leaders
or defects there too. -/
def retires {p c n : Nat} (x : Config p c n) (base e : Fin n) (d : Nat) : Bool :=
  moved x base e d && (x (liftedSite base d)).mark

/-- Freeze the heads at the first stopping mark, so counts refer only to
the strict pre-stop prefix. The physical row on that mark is still run. -/
def advance {p c n : Nat} (base : Fin n) (s : Obs p c n) (e : Fin n) : Obs p c n :=
  if s.stopped then s else
    let x := s.config
    let y := step x e
    let a := s.heads
    let ni := a.i + (moved x base e a.i).toNat
    let nj := a.j + (moved x base e a.j).toNat
    let nk := a.k + (moved x base e a.k).toNat
    let stop := retires x base e a.i || retires x base e a.j || retires x base e a.k ||
      (y (liftedSite base ni)).leader || (y (liftedSite base nj)).leader
    if stop then ⟨y,a,true⟩ else ⟨y,⟨ni,nj,nk⟩,false⟩

def observe {p c n : Nat} (x : Config p c n) (base : Fin n) (a : Heads)
    (w : List (Fin n)) : Obs p c n :=
  GGTiming.runMarks (advance base) (init x a) w

/-- First-stage literal drain: stop, or no stock in the entire retained
half-open corridor [i,j), including the possible marked payer at j−1. -/
def Drained {p c n : Nat} (base : Fin n) (s : Obs p c n) : Prop :=
  s.stopped = true ∨
    ∀ d, s.heads.i ≤ d → d < s.heads.j →
      (s.config (liftedSite base d)).stock = false

/-- Preparation additionally requires removing inherited break rails
in the retained corridor. This is not claimed by the drain clock. -/
def Prepared {p c n : Nat} (base : Fin n) (s : Obs p c n) : Prop :=
  s.stopped = true ∨
    ∀ d, s.heads.i ≤ d → d < s.heads.j →
      (s.config (liftedSite base d)).stock = false ∧
        (s.config (liftedSite base d)).rail ≠ .x

theorem heads_mono_step {p c n : Nat} (base : Fin n) (s : Obs p c n) (e : Fin n) :
    s.heads.i ≤ (advance base s e).heads.i ∧
    s.heads.j ≤ (advance base s e).heads.j ∧
    s.heads.k ≤ (advance base s e).heads.k := by
  unfold advance
  split
  · exact ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _⟩
  · dsimp only
    split
    · exact ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _⟩
    · exact ⟨Nat.le_add_right _ _,Nat.le_add_right _ _,Nat.le_add_right _ _⟩

theorem heads_mono_word {p c n : Nat} (base : Fin n) (s : Obs p c n) (w : List (Fin n)) :
    let t := GGTiming.runMarks (advance base) s w
    s.heads.i ≤ t.heads.i ∧ s.heads.j ≤ t.heads.j ∧ s.heads.k ≤ t.heads.k := by
  induction w generalizing s with
  | nil => exact ⟨Nat.le_refl _,Nat.le_refl _,Nat.le_refl _⟩
  | cons e w ih =>
    obtain ⟨hi,hj,hk⟩ := heads_mono_step base s e
    obtain ⟨hi',hj',hk'⟩ := ih (advance base s e)
    exact ⟨Nat.le_trans hi hi',Nat.le_trans hj hj',Nat.le_trans hk hk'⟩

/-- Chronological projection of literal j movement marks, excluding the
first terminal event. Retained records contain the old two heads and the
edge actually selected by the scheduler. -/
structure PaymentStamp (n : Nat) where
  j : Nat
  k : Nat
  selected : Fin n

def payments {p c n : Nat} (base : Fin n) (s : Obs p c n) :
    List (Fin n) → List (PaymentStamp n)
  | [] => []
  | e::w =>
    let t := advance base s e
    let tail := payments base t w
    if s.heads.j < t.heads.j then ⟨s.heads.j,s.heads.k,e⟩ :: tail else tail

private theorem j_le_add_one {p c n : Nat} (base : Fin n) (s : Obs p c n) (e : Fin n) :
    (advance base s e).heads.j ≤ s.heads.j+1 := by
  unfold advance
  split
  · exact Nat.le_add_right _ _
  · dsimp only
    split
    · exact Nat.le_add_right _ _
    · cases hb : moved s.config base e s.heads.j <;> simp

theorem payments_length {p c n : Nat} (base : Fin n) (s : Obs p c n) (w : List (Fin n)) :
    (payments base s w).length + s.heads.j =
      (GGTiming.runMarks (advance base) s w).heads.j := by
  induction w generalizing s with
  | nil => simp [payments,GGTiming.runMarks]
  | cons e w ih =>
    have hlow := (heads_mono_step base s e).2.1
    have hhi := j_le_add_one base s e
    have hk := ih (advance base s e)
    simp only [payments,GGTiming.runMarks]
    split
    · simp only [List.length_cons]; omega
    · omega

/-- The payment head is selected on its actual incoming edge and P3
really succeeds on that old configuration. This does not yet identify
the label of the spent stock. -/
theorem j_increase_is_literal {p c n : Nat} (base : Fin n) (s : Obs p c n)
    (e : Fin n) (h : s.heads.j < (advance base s e).heads.j) :
    (advance base s e).stopped = false ∧ s.stopped = false ∧
      e = incoming base s.heads.j ∧ geometricPay (s.config e)
        (s.config (rightNeighbor e)) = true := by
  unfold advance at h ⊢
  split at h
  · exact False.elim (Nat.lt_irrefl _ h)
  · rename_i hS
    simp only [hS]
    dsimp only at h ⊢
    split at h
    · exact False.elim (Nat.lt_irrefl _ h)
    · rename_i hT
      simp only [hT, if_false, Bool.false_eq_true, true_and]
      have hm : moved s.config base e s.heads.j = true := by
        cases hp : moved s.config base e s.heads.j
        · simp [hp] at h
        · rfl
      unfold moved at hm
      simpa [Bool.or_eq_true,Bool.and_eq_true, beq_iff_eq] using hm

/-- A proof-side ancestry lift must identify each actual mark in order,
not merely exhibit the right number of abstract payments. -/
inductive MatchPayments {n s : Nat} (base : Fin n) :
    List (PaymentStamp n) → List (GGStock.PaidJ s) → Prop
  | nil : MatchPayments base [] []
  | cons {a z tail labels} :
      a.j = z.j → a.k = z.k → a.selected = liftedSite base z.donor →
      MatchPayments base tail labels → MatchPayments base (a::tail) (z::labels)

theorem MatchPayments.length_eq {n s : Nat} {base : Fin n}
    {a : List (PaymentStamp n)} {z : List (GGStock.PaidJ s)}
    (h : MatchPayments base a z) : a.length = z.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ ih => simp [ih]

/-- Remaining ancestry obligation instantiated on the literal sequence
of selected marks. The independent stock-token invariant must supply it. -/
def LiteralStockProjection {p c n : Nat} (x : Config p c n) (base : Fin n) (a : Heads) : Prop :=
  ∀ w, InitialCut x base a →
    ∃ labels : List (GGStock.PaidJ (a.k-a.i)),
      MatchPayments base (payments base (init x a) w) labels ∧
        GGStock.CreditTrace (List.finRange (a.k-a.i)) labels

/-- The unresolved physical projection attaches a real paid-mark witness
and a consumed initial token to every tracked strict-prefix j increment.
The interval parameter and count are computed from literal rows. -/
def ProjectsStock {p c n : Nat} (x : Config p c n) (base : Fin n) (a : Heads) : Prop :=
  GGStockPhysical.ProjectsGGStock
    (fun w : List (Fin n) => (observe x base a w).heads.j-a.j)
    (fun _ => InitialCut x base a) (a.k-a.i)

theorem projectsStock_of_literal {p c n : Nat} (x : Config p c n) (base : Fin n)
    (a : Heads) (h : LiteralStockProjection x base a) : ProjectsStock x base a := by
  intro w hcut
  obtain ⟨labels,hm,hc⟩ := h w hcut
  have hn := payments_length base (init x a) w
  change (payments base (init x a) w).length + a.j = (observe x base a w).heads.j at hn
  rw [hm.length_eq] at hn
  exact ⟨labels,by change (observe x base a w).heads.j-a.j = labels.length; omega,hc⟩

theorem displacement_of_stock {p c n : Nat} (x : Config p c n) (base : Fin n) (a : Heads)
    (h : InitialCut x base a) (hStock : ProjectsStock x base a) (w : List (Fin n)) :
    let z := (observe x base a w).heads
    z.j ≤ a.j+(a.k-a.i) ∧ z.j-z.i ≤ 2*(a.k-a.i) := by
  have hp := GGStockPhysical.projected_paid_count_le
    (fun w : List (Fin n) => (observe x base a w).heads.j-a.j)
    (fun _ => InitialCut x base a) (a.k-a.i) hStock w h
  have hm := heads_mono_word base (init x a) w
  change a.i ≤ (observe x base a w).heads.i ∧
    a.j ≤ (observe x base a w).heads.j ∧ a.k ≤ (observe x base a w).heads.k at hm
  have hab := h.2.2.2.1.1
  have hbc := h.2.2.2.1.2.1
  dsimp only
  omega

/-- Final unresolved timing certificate, separate from stock ancestry.
Completion of the named predictable path construction must force literal
preparedness from the actual initial cut. -/
structure Certificate {p c n : Nat} (x : Config p c n) (base : Fin n) (a : Heads) where
  paths : List (List (Fin n))
  L : Nat
  length_bound : ∀ q ∈ paths, q.length ≤ L
  path_bound : paths.length ≤ 2^(L+1)
  forces : ∀ w : List (Fin n),
    GGTiming.finished (GGTiming.runMarks GGTiming.advance paths w) →
      Drained base (observe x base a w)

theorem expected_of_certificate {p c n : Nat} (x : Config p c n) (base : Fin n)
    (a : Heads) (C : Certificate x base a) :
    IIDExpectedHittingTimeAtMost (advance base) (Drained base) (init x a)
      (4*n*(C.L+1)) := by
  exact GGTiming.hittingTime_of_path_certificate (advance base) (Drained base) (init x a)
    (Nat.zero_lt_of_lt base.isLt) C.paths C.L C.length_bound C.path_bound C.forces

#print axioms payments_length
#print axioms j_increase_is_literal
#print axioms projectsStock_of_literal
#print axioms incoming_right
#print axioms heads_mono_word
#print axioms displacement_of_stock
#print axioms expected_of_certificate

end L4.GGStage
