import Leader.L4.WindowA0Route
import Leader.L4.WindowFourHeadTrace

/-! The actual A0 observer, independent of the restart counters.
Pinned original IDs and actual raw edge actions never get replaced
by the residual-cleanup abstraction. -/
namespace L4.WindowA0Ledger
open SevenTagCharge WindowA0Route WindowFourHeadTrace

structure Scope (n : Nat) where
  group : List (Fin n)
  iTag : Fin n
  jTag : Fin n
  kTag : Fin n
  iIn : iTag∈group
  jIn : jTag∈group
  kIn : kTag∈group

structure State (p c n : Nat) where
  ledger : Ledger p c n
  iSlot : Fin n
  jSlot : Fin n
  kSlot : Fin n
  reason : Option (WindowLocal.Event n)

def next {p c n : Nat} (S : Scope n) (x : State p c n) (e : Fin n) :
    State p c n :=
  let y := advance x.ledger e
  match x.reason with
  | some r => { x with ledger:=y, reason:=some r }
  | none =>
    let r := routeTwo S.group S.iTag S.jTag x.ledger e
    if r=.keep then
      ⟨y,landing x.ledger e x.iSlot,landing x.ledger e x.jSlot,landing x.ledger e x.kSlot,none⟩
    else
      { x with ledger:=y, reason:=some r }

def done {p c n : Nat} (x : State p c n) : Prop := x.reason.isSome

theorem physical_step {p c n : Nat} (S : Scope n) (x : State p c n) (e : Fin n) :
    (next S x e).ledger=advance x.ledger e := by
  cases h : x.reason with
  | none => simp only [next,h]; split <;> rfl
  | some r => simp only [next,h]

theorem physical_marks {p c n : Nat} (S : Scope n) (x : State p c n) (w : List (Fin n)) :
    (GGTiming.runMarks (next S) x w).ledger=observe x.ledger w := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    change (GGTiming.runMarks (next S) (next S x e) w).ledger = observe (advance x.ledger e) w
    rw [ih,physical_step]

theorem terminal_sticky {p c n : Nat} (S : Scope n) (x : State p c n) (e : Fin n)
    (h : done x) : (next S x e).reason=x.reason := by
  cases hr : x.reason with
  | none => simp [done,hr] at h
  | some r => simp [next,hr]

def Live {p c n : Nat} (z0 : Config p c n) (S : Scope n) (x : State p c n) : Prop :=
  Valid x.ledger z0 ∧ x.reason=none ∧
    x.ledger.slots x.iSlot=some S.iTag ∧ x.ledger.slots x.jSlot=some S.jTag ∧
    x.ledger.slots x.kSlot=some S.kTag ∧
    (x.ledger.config (rightNeighbor x.iSlot)).leader=false ∧
    (x.ledger.config (rightNeighbor x.jSlot)).leader=false

private theorem landing_head {p c n : Nat} (z : Ledger p c n) (e s : Fin n) :
    landing z e s = (if e=s then WindowLocal.landingSlot z.config e else s) := by
  by_cases h : e=s
  · subst s
    unfold landing moves WindowLocal.landingSlot
    simp
  · simp [landing,moves,h]

theorem live_or_terminal {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : Scope n) (x : State p c n) (e : Fin n) (hx : Live z0 S x) :
    done (next S x e) ∨ Live z0 S (next S x e) := by
  obtain ⟨hz,hStart,hi,hj,hk,hlI,hlJ⟩ := hx
  let r := routeTwo S.group S.iTag S.jTag x.ledger e
  by_cases h : r=.keep
  · right
    have hout : next S x e = ⟨advance x.ledger e,
        landing x.ledger e x.iSlot,landing x.ledger e x.jSlot,landing x.ledger e x.kSlot,none⟩ := by
      simp [next,hStart,r,h]
    have hKeep : WindowLocal.selectedGroupLoss S.group x.ledger e=none :=
      empty_group_loss_of_two_keep x.ledger S.group S.iTag S.jTag e h
    have ht (s a : Fin n) (ha : a∈S.group) (hs : x.ledger.slots s=some a) :
        (advance x.ledger e).slots (landing x.ledger e s)=some a :=
      tracked_landing hn x.ledger S.group e s a hz.covers ha hs hKeep
    have hgh (s a : Fin n) (ha : a∈S.group) (hs : x.ledger.slots s=some a)
        (hg : (x.ledger.config (rightNeighbor s)).leader=false)
        (hR : WindowLocal.route S.group [] (some a) x.ledger e=.keep) :
        ((advance x.ledger e).config (rightNeighbor (landing x.ledger e s))).leader=false := by
      rw [landing_head]
      exact ghost_after_keep hn x.ledger S.group a s e hz ha hs hg hR
    have HH := (keep_iff S.group S.iTag S.jTag x.ledger e).mp h
    exact hout.symm ▸ ⟨valid_step hn _ _ _ hz,rfl,ht _ _ S.iIn hi,ht _ _ S.jIn hj,ht _ _ S.kIn hk,
      hgh _ _ S.iIn hi hlI HH.1,hgh _ _ S.jIn hj hlJ HH.2⟩
  · left
    simp [done,next,hStart,r,h]

theorem physical_exit_iff {p c n : Nat} (S : Scope n) (x : State p c n) (e : Fin n)
    (h : x.reason=none) :
    done (next S x e) ↔ routeTwo S.group S.iTag S.jTag x.ledger e ≠ .keep := by
  unfold next
  simp only [h,done]
  split <;> simp_all

/-- Choose exactly window members 1,2,3 from the original roster. -/
def scopeOf {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x)) : Scope n := by
  let R := WindowRoster.roster x
  have H (k : Fin 7) : R (liftedSite i k.val) ∈ window7 R i :=
    List.mem_map.mpr ⟨k,List.mem_finRange k,rfl⟩
  exact ⟨window7 R i,R (liftedSite i 1),R (liftedSite i 2),R (liftedSite i 3), H 1,H 2,H 3⟩

def startOf {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x)) : State p c n :=
  let S := scopeOf x i
  ⟨SevenTagCharge.initial x,S.iTag,S.jTag,S.kTag,none⟩

theorem initial_live {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (hm : MCOV x) (hc : COV x)
    (h1 : (x (WindowSpan.rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (WindowSpan.rootSite x (liftedSite i 2))).leader=false) :
    Live x (scopeOf x i) (startOf x i) := by
  have mark (k : Nat) : (x (WindowRoster.roster x (liftedSite i k))).mark=true :=
    (WindowRoster.roster_exact x _).mp ⟨liftedSite i k,rfl⟩
  have slot (k : Nat) :
      (SevenTagCharge.initial x).slots (WindowRoster.roster x (liftedSite i k))=
        some (WindowRoster.roster x (liftedSite i k)) := by
    simp [SevenTagCharge.initial,initSlots,mark k]
  exact ⟨valid_init x hm hc,rfl,slot 1,slot 2,slot 3,h1,h2⟩

theorem run_live_or_done {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : Scope n) (x : State p c n) (w : List (Fin n))
    (h : done x ∨ Live z0 S x) :
    done (GGTiming.runMarks (next S) x w) ∨ Live z0 S (GGTiming.runMarks (next S) x w) := by
  induction w generalizing x with
  | nil => exact h
  | cons e w ih =>
    apply ih
    rcases h with h|h
    · left
      have H := terminal_sticky S x e h
      unfold done at *
      rw [H]
      exact h
    · exact live_or_terminal hn S x e h

end L4.WindowA0Ledger
