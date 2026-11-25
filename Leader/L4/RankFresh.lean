import Leader.L4.Closure
import Leader.L4.TenureOrigins
import Leader.L4.RankPhysical

namespace L4.RankFresh
open L4

@[simp] private theorem bullet_beq (a b : Bullet) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide
@[simp] private theorem bullet_beq_false (a b : Bullet) : (a == b) = false ↔ a ≠ b := by
  cases a <;> cases b <;> decide
@[simp] private theorem signal_beq (a b : Signal) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide
@[simp] private theorem signal_beq_false (a b : Signal) : (a == b) = false ↔ a ≠ b := by
  cases a <;> cases b <;> decide
@[simp] private theorem initMark {p c : Nat} (u : Site p c) :
    (fireInitiator u).mark = u.mark := by
  unfold fireInitiator
  split <;> rfl

/-- One incoming mark cannot kill or unshield a shielded leader whose
own pre-signal is not the ordinary returning colour. -/
theorem supplier_incoming {p c : Nat} (u v : Site p c)
    (hl : v.leader = true) (hh : v.shield = true) (hs : v.signal ≠ .one) :
    (pairStep u v).2.leader = true ∧
    (pairStep u v).2.shield = true ∧ (pairStep u v).2.signal = .zero := by
  have hF : (fireResponder v).leader = true ∧
      (fireResponder v).shield = true ∧ (fireResponder v).signal = .zero := by
    cases s : v.signal <;> simp_all [fireResponder]
  have hPrefix : (stepPrefix u v).2.leader = true ∧
      (stepPrefix u v).2.shield = true ∧ (stepPrefix u v).2.signal = .zero := by
    unfold stepPrefix native
    generalize h₁ : fireInitiator (materialize u v) = a
    generalize h₂ : fireResponder v = b at hF ⊢
    obtain ⟨hL,hH,hS⟩ := hF
    cases hB : a.bullet <;>
      simp [impact,hB,hL,hH,hS,followerBullet,payment]
  unfold pairStep
  generalize hp : stepPrefix u v = w at hPrefix ⊢
  cases w with
  | mk a b =>
    obtain ⟨hL,hH,hS⟩ := hPrefix
    dsimp at hL hH hS
    simp [patrolWrite,finishBirth,pinned,hL,hH,hS]

/-- A service into a marked ghost emits urgent colour even on a paid P3
move. The instruction which emits signal 2 comes before payment. -/
theorem ghost_feedback {p c : Nat} (u v : Site p c)
    (hm : u.mark = true) (hl : v.leader = false) :
    (pairStep u v).1.signal = .two := by
  let a := fireInitiator (materialize u v)
  have hA : a.mark = true := by simp [a,materialize,hm]
  have hprefix : (stepPrefix u v).1.signal = .two := by
    unfold stepPrefix native
    have hF : fireResponder v = v := by simp [fireResponder,hl]
    rw [hF]
    generalize hw : fireInitiator (materialize u v) = w
    have hW : w.mark = true := by simpa [a,hw] using hA
    cases hB : w.bullet <;> cases hS : w.signal <;>
      cases hStock : w.stock <;> cases hLeader : w.leader <;>
      simp [impact,hl,pinned,hW,followerBullet,hB,hS,Signal.max,payment,payer,hStock,hLeader]
  unfold pairStep
  generalize hp : stepPrefix u v = w at hprefix ⊢
  cases w with
  | mk a b =>
    dsimp [patrolWrite,finishBirth] at *
    split <;> exact hprefix

/-- Exact launch condition for an unshielded target at the end of a
one-edge or multi-edge attack. N1's dummy action precedes the impact. -/
theorem ready_live_impact {p c : Nat} (u v : Site p c)
    (hv : v.leader = true) (hs : v.signal = .one)
    (hu : (fireInitiator (materialize u v)).bullet = .live) :
    (stepPrefix u v).2.leader = false ∧ (stepPrefix u v).2.signal = .zero ∧
      (stepPrefix u v).1.signal = .two := by
  let a := fireInitiator (materialize u v)
  have hA : a.mark = true := by simp [a,materialize,hv]
  have hF : fireResponder v =
      {v with bullet := .dummy, shield := false, signal := .zero} := by
    simp [fireResponder,hv,hs]
  unfold stepPrefix native
  rw [hF]
  generalize h₁ : fireInitiator (materialize u v) = w at hu ⊢
  have hm : w.mark = true := by simpa [a,h₁] using hA
  cases hS : w.signal <;> cases hStock : w.stock <;> cases hLeader : w.leader <;>
    simp [impact,followerBullet,hu,hv,hm,hS,pinned,payment,payer,Signal.max,hStock,hLeader]

/-- A frontier is a color-two site or an occupied zero-signal site.
The bullet can be dummy, live or an existing collider. It is a signal
separator, not a lineage label. -/
def Frontier {p c : Nat} (s : Site p c) : Prop :=
  s.signal = .two ∨ (s.bullet ≠ .none ∧ s.signal = .zero)

structure OrdinaryProtection {p c : Nat} (u v a b : Site p c) : Prop where
  clean : u.signal ≠ .one → v.signal ≠ .one →
    a.signal ≠ .one ∧ b.signal ≠ .one
  shield : u.shield = true → a.shield = true
  frontLeft : Frontier u → a.signal ≠ .one ∧ (Frontier a ∨ Frontier b)
  frontRight : Frontier v → Frontier b

private def ordinaryNative {p c : Nat} (u v : Site p c) : Site p c × Site p c :=
  let a := fireInitiator u
  if a.bullet == .none then ({ a with signal := a.signal.max v.signal }, v)
  else
    ({ a with bullet := .none, signal := a.signal.max .zero },
      { v with signal := .zero, bullet := (if v.bullet == .none then a.bullet else v.bullet) })

private theorem onOrdinary {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hl : v.leader = false) :
    native u v = ordinaryNative u v := by
  unfold native ordinaryNative
  cases hb : (fireInitiator u).bullet <;>
    simp [fireResponder,impact,hl,pinned,hm,followerBullet,hb]

private theorem onProtection {p c : Nat} (u v : Site p c) :
    OrdinaryProtection u v (ordinaryNative u v).1 (ordinaryNative u v).2 := by
  unfold ordinaryNative fireInitiator
  split
  · cases hV : v.bullet <;> constructor <;> simp [Frontier,hV,Signal.max]
  · cases hB : u.bullet <;> cases hS : u.signal <;>
      cases hV : v.bullet <;> cases hT : v.signal <;>
      constructor <;> simp [Frontier,hB,hS,hV,hT,Signal.max]

private def trim {p c : Nat} (u : Site p c) : Site p c :=
  {u with stock := false, source := .off, rail := .e}

private theorem trim_protection {p c : Nat} (u v a b : Site p c) :
    OrdinaryProtection u v (trim a) (trim b) ↔ OrdinaryProtection u v a b := by
  constructor <;> intro h <;> exact ⟨h.clean,h.shield,h.frontLeft,h.frontRight⟩

private theorem ordinary_trim {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hl : v.leader = false)
    (hd : defect u v = false) :
    trim (pairStep u v).1 = trim (ordinaryNative u v).1 ∧
      trim (pairStep u v).2 = trim (ordinaryNative u v).2 := by
  have hM : materialize u v = u := by simp [materialize,hm,hl,hd]
  let w := ordinaryNative u v
  have hW : stepPrefix u v = payment w.1 w.2 := by
    simp only [stepPrefix,hM,onOrdinary u v hm hl,w]
  have hNative : w.1.mark = false ∧ w.2.leader = false := by
    dsimp only [w,ordinaryNative]
    cases (fireInitiator u).bullet <;> simp [hm,hl]
  obtain ⟨hm',hl'⟩ := hNative
  change trim (pairStep u v).1 = trim w.1 ∧ trim (pairStep u v).2 = trim w.2
  unfold pairStep
  rw [hW]
  cases hs : w.2.stock <;> cases hp : payer w.1 <;>
    simp [payment,hm',hl',hs,hp,finishBirth,patrolWrite,pinned,trim]

/-- Ordinary service preserves a clean prefix and a signal separator.
A left separator may stay or move to the responder; a right separator
cannot be destroyed by collision. -/
theorem ordinary_protection {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hl : v.leader = false) (hd : defect u v = false) :
    OrdinaryProtection u v (pairStep u v).1 (pairStep u v).2 := by
  apply (trim_protection u v _ _).mp
  obtain ⟨ha,hb⟩ := ordinary_trim u v hm hl hd
  rw [ha,hb]
  exact (trim_protection u v _ _).mpr (onProtection u v)

/-- On an actual covered killing mark, both signal outputs are forced:
urgent feedback is installed at the donor and the victim is cleared.
This does not require stock to be absent or require a long corridor. -/
theorem covered_kill_feedback {p c : Nat} (u v : Site p c)
    (hl : v.leader = true) (hoff : v.source = .off)
    (hk : (pairStep u v).2.leader = false) :
    (pairStep u v).1.signal = .two ∧ (pairStep u v).2.signal = .zero := by
  obtain ⟨_,hkB,hkS⟩ := (TenureOrigins.covered_leader_loss_iff u v hl hoff).mp hk
  let a := fireInitiator (materialize u v)
  let b := fireResponder v
  have haM : a.mark = true := by simp [a,materialize,hl]
  have haB : a.bullet = .live := by
    change (fireInitiator (materialize u v)).bullet = .live
    unfold materialize
    simp only [hl,Bool.true_or,if_true]
    unfold fireInitiator at hkB ⊢
    split <;> simp_all
  have hbL : b.leader = true := by
    dsimp [b]
    cases he : v.signal <;> simp [fireResponder,hl,he]
  have hbZ : b.signal = .zero := by
    dsimp [b]
    cases he : v.signal <;> simp_all [fireResponder]
  have hbS : b.shield = false := hkS
  have hprefix : (stepPrefix u v).1.signal = .two ∧ (stepPrefix u v).2.signal = .zero := by
    unfold stepPrefix native
    generalize hA : fireInitiator (materialize u v) = A at haM haB ⊢
    generalize hB : fireResponder v = B at hbL hbZ hbS ⊢
    have haM' : A.mark = true := by
      change (fireInitiator (materialize u v)).mark = true at haM
      simpa only [hA] using haM
    have haB' : A.bullet = .live := by
      change (fireInitiator (materialize u v)).bullet = .live at haB
      simpa only [hA] using haB
    have hbL' : B.leader = true := by
      change (fireResponder v).leader = true at hbL
      simpa only [hB] using hbL
    have hbZ' : B.signal = .zero := by
      change (fireResponder v).signal = .zero at hbZ
      simpa only [hB] using hbZ
    have hbS' : B.shield = false := by
      change (fireResponder v).shield = false at hbS
      simpa only [hB] using hbS
    cases hs : A.signal <;> cases ht : A.stock <;> cases hL : A.leader <;>
      simp [impact,followerBullet,pinned,haM',haB',hbL',hbZ',hbS',
        hs,ht,hL,payment,payer,Signal.max]
  unfold pairStep
  generalize hQ : stepPrefix u v = w at hprefix ⊢
  cases w with
  | mk l r =>
    obtain ⟨hL,hR⟩ := hprefix
    dsimp at hL hR
    dsimp [patrolWrite,finishBirth]
    split <;> simp [hL,hR]

/-- An outgoing service cannot change its initiator's leader bit; it
can turn on its shield, but cannot turn it off. -/
theorem outgoing_leader_shield {p c : Nat} (u v : Site p c) (hh : u.shield = true) :
    (pairStep u v).1.leader = u.leader ∧ (pairStep u v).1.shield = true := by
  let a := fireInitiator (materialize u v)
  let b := fireResponder v
  let t := impact a b
  let w := followerBullet (pinned t.1 t.2) t.1 t.2
  have hM : (materialize u v).leader = u.leader ∧ (materialize u v).shield = true := by
    unfold materialize
    split <;> exact ⟨rfl,hh⟩
  have hA : a.leader = u.leader ∧ a.shield = true := by
    dsimp [a]
    unfold fireInitiator
    split
    · exact ⟨hM.1,rfl⟩
    · exact hM
  have hT : t.1.leader = u.leader ∧ t.1.shield = true := by
    dsimp only [t]
    unfold impact
    split
    · split <;> exact hA
    · exact hA
  have hW : w.1.leader = u.leader ∧ w.1.shield = true := by
    dsimp only [w]
    unfold followerBullet
    split
    · split <;> exact hT
    · exact hT
  have hpre : (stepPrefix u v).1.leader = u.leader ∧ (stepPrefix u v).1.shield = true := by
    let emitted := if w.2.leader then Signal.one
      else if pinned t.1 t.2 then Signal.two else w.2.signal
    change (payment { w.1 with signal := w.1.signal.max emitted } w.2).1.leader = u.leader ∧
      (payment { w.1 with signal := w.1.signal.max emitted } w.2).1.shield = true
    unfold payment
    split
    · exact hW
    · split
      · exact hW
      · split <;> exact hW
  unfold pairStep
  generalize hX : stepPrefix u v = q at hpre ⊢
  cases q with
  | mk l r =>
    dsimp [patrolWrite,finishBirth] at *
    split <;> exact hpre

private theorem right_ne_self {n : Nat} (hn : 4 ≤ n) (i : Fin n) :
    rightNeighbor i ≠ i := by
  intro he
  have h' : liftedSite i 1 = liftedSite i 0 := by
    simpa [liftedSite_succ,liftedSite_zero] using he
  have hf := liftedSite_inj i (by omega : 1<n) (by omega : 0<n) h'
  omega

/-- Ring-level one-step source survival. The explicit first-bond premise
is exactly what the moving corridor separator discharges. -/
theorem supplier_step {p c n : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (y e : Fin n) (hc : MCOV x)
    (hl : (x y).leader = true) (hh : (x y).shield = true)
    (hs : (x y).signal ≠ .one) (hv : (x (rightNeighbor y)).leader = false)
    (hf : (x y).mark = false → (x (rightNeighbor y)).signal ≠ .one ∨ Frontier (x y)) :
    ((step x e) y).leader = true ∧ ((step x e) y).shield = true ∧
      ((step x e) y).signal ≠ .one := by
  by_cases he : e = y
  · subst e
    obtain ⟨hL,hH⟩ := outgoing_leader_shield (x y) (x (rightNeighbor y)) hh
    have hS : (pairStep (x y) (x (rightNeighbor y))).1.signal ≠ .one := by
      cases hm : (x y).mark
      · have hdef : defect (x y) (x (rightNeighbor y)) = false := by
          have hr : (x (rightNeighbor y)).residue = nextResidue (x y).residue := by
            by_cases heq : (x (rightNeighbor y)).residue = nextResidue (x y).residue
            · exact heq
            · have hh := hc y (Or.inr heq)
              rw [hm] at hh
              contradiction
          simp [defect,hr]
        have hO := ordinary_protection (x y) (x (rightNeighbor y)) hm hv hdef
        rcases hf hm with hgood | hfront
        · exact (hO.clean hs hgood).1
        · exact (hO.frontLeft hfront).1
      · rw [ghost_feedback (x y) (x (rightNeighbor y)) hm hv]
        decide
    simpa [step,hl] using And.intro hL (And.intro hH hS)
  · by_cases hr : y = rightNeighbor e
    · subst y
      obtain ⟨hL,hH,hS⟩ := supplier_incoming (x e) (x (rightNeighbor e)) hl hh hs
      have hd : (pairStep (x e) (x (rightNeighbor e))).2.signal ≠ .one := by rw [hS]; decide
      simpa [step,right_ne_self hn e] using And.intro hL (And.intro hH hd)
    · simpa [step,Ne.symm he,hr] using And.intro hl (And.intro hh hs)

theorem supplier_incoming_frontier {p c : Nat} (u v : Site p c)
    (hl : v.leader = true) (hh : v.shield = true) (hf : Frontier v) :
    Frontier (pairStep u v).2 := by
  have ht : (fireResponder v).leader = true ∧ (fireResponder v).shield = true ∧
      Frontier (fireResponder v) := by
    cases hs : v.signal <;> simp_all [fireResponder,Frontier]
  have hp : (stepPrefix u v).2.leader = true ∧ Frontier (stepPrefix u v).2 := by
    unfold stepPrefix native
    generalize e₁ : fireInitiator (materialize u v) = a
    generalize e₂ : fireResponder v = b at ht ⊢
    obtain ⟨hbL,hbS,hbF⟩ := ht
    cases hb : a.bullet <;>
      simp [impact,hb,hbL,hbS,followerBullet,payment,hbF]
  unfold pairStep
  generalize hq : stepPrefix u v = q at hp ⊢
  cases q with
  | mk a b =>
    obtain ⟨hL,hF⟩ := hp
    dsimp at hL hF
    simp [finishBirth,patrolWrite,pinned,hL,Frontier] at *
    exact hF

/-- Formal source-to-ghost geometry. The donor offset is d and the
followed ghost is at offset d+1. -/
structure Corridor {p c n : Nat} (x : Config p c n) (y : Fin n) (d : Nat) : Prop where
  first : FirstMark x y d
  gap : d+1 < n
  ghost : (x (liftedSite y (d+1))).leader = false
  leader : (x y).leader = true
  shield : (x y).shield = true
  separator : ∃ j : Nat, j ≤ d ∧ Frontier (x (liftedSite y j)) ∧
    ∀ i : Nat, i ≤ j → (x (liftedSite y i)).signal ≠ .one

private theorem ordinaryAt {p c n : Nat} {x : Config p c n} {y : Fin n}
    {d i : Nat} (hc : MCOV x) (h : Corridor x y d) (hi : i < d) :
    OrdinaryProtection (x (liftedSite y i)) (x (liftedSite y (i+1)))
      (pairStep (x (liftedSite y i)) (x (liftedSite y (i+1)))).1
      (pairStep (x (liftedSite y i)) (x (liftedSite y (i+1)))).2 := by
  have hm : (x (liftedSite y i)).mark = false := Bool.eq_false_iff.mpr (h.first.before i hi)
  have hL : (x (rightNeighbor (liftedSite y i))).leader = false :=
    Bool.eq_false_iff.mpr (fun hb => h.first.before i hi (hc _ (Or.inl hb)))
  have hR : (x (rightNeighbor (liftedSite y i))).residue = nextResidue (x (liftedSite y i)).residue := by
    by_cases hr : (x (rightNeighbor (liftedSite y i))).residue = nextResidue (x (liftedSite y i)).residue
    · exact hr
    · exact False.elim (h.first.before i hi (hc _ (Or.inr hr)))
  rw [liftedSite_succ]
  exact ordinary_protection _ _ hm hL (by simp [defect,hR])

private theorem lift_ne {n : Nat} {y : Fin n} {i j : Nat}
    (hi : i < n) (hj : j < n) (h : i ≠ j) : liftedSite y i ≠ liftedSite y j :=
  fun he => h (liftedSite_inj y hi hj he)

/-- One-step source protection from an actual pre-mark separator,
without assuming that the victim remains a ghost on the next mark. -/
theorem corridor_supplier_step {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (y e : Fin n) (hc : MCOV x) (h : Corridor x y d) :
    ((step x e) y).leader = true ∧ ((step x e) y).shield = true ∧
      ((step x e) y).signal ≠ .one := by
  obtain ⟨j,hjd,hF,hS⟩ := h.separator
  apply supplier_step hn x y e hc h.leader h.shield
  · simpa [liftedSite_zero] using hS 0 (by omega)
  · cases d with
    | zero => simpa [liftedSite_succ,liftedSite_zero] using h.ghost
    | succ d =>
      have hm : (x y).mark ≠ true := by
        simpa [liftedSite_zero] using h.first.before 0 (by omega)
      exact Bool.eq_false_iff.mpr (fun ht => hm (hc y (Or.inl ht)))
  · intro _
    cases j with
    | zero => exact Or.inr (by simpa [liftedSite_zero] using hF)
    | succ j =>
      exact Or.inl (by simpa [liftedSite_succ,liftedSite_zero] using hS 1 (by omega))

private theorem frontier_ne_one {p c : Nat} {z : Site p c} (h : Frontier z) :
    z.signal ≠ .one := by
  intro he
  rcases h with h | ⟨_,h⟩ <;> rw [he] at h <;> contradiction

/-- A literal physical mark transports the protected prefix. The
resulting separator is still within the old victim's donor, so it
also works if the victim takes a paid step clockwise. -/
theorem corridor_separator_step {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (y e : Fin n) (hc : MCOV x) (h : Corridor x y d) :
    ∃ j : Nat, j ≤ d ∧ Frontier ((step x e) (liftedSite y j)) ∧
      ∀ i : Nat, i ≤ j → ((step x e) (liftedSite y i)).signal ≠ .one := by
  obtain ⟨j,hj,hf,hs⟩ := h.separator
  let a := liftedSite y
  have left (k : Nat) : step x (a k) (a k) = (pairStep (x (a k)) (x (a (k+1)))).1 := by
    simp [a,step,liftedSite_succ]
  have right (k : Nat) : step x (a k) (a (k+1)) = (pairStep (x (a k)) (x (a (k+1)))).2 := by
    simp [a,step,liftedSite_succ,right_ne_self hn]
  have back (k : Nat) (he : rightNeighbor e = a (k+1)) : e = a k := by
    have hq := congrArg RearTrace.predecessor he
    simpa [a,liftedSite_succ,RearTrace.predecessor_right] using hq
  have boundary (he : e = a d) : Frontier (step x e (a d)) := by
    subst e
    rw [left d]
    exact Or.inl (ghost_feedback _ _ h.first.marked h.ghost)
  have clean (i : Nat) (hi : i ≤ j) : (step x e (a i)).signal ≠ .one := by
    by_cases ho : e = a i
    · rw [ho,left i]
      by_cases hN : i = j
      · subst i
        by_cases hD : j = d
        · subst j
          rw [ghost_feedback _ _ h.first.marked h.ghost]
          decide
        · exact ((ordinaryAt hc h (by omega : j < d)).frontLeft hf).1
      · exact ((ordinaryAt hc h (by omega : i < d)).clean (hs i hi) (hs (i+1) (by omega))).1
    · by_cases hr : rightNeighbor e = a i
      · cases i with
        | zero =>
          simp only [a,liftedSite_zero]
          exact (corridor_supplier_step hn x y e hc h).2.2
        | succ k =>
          rw [back k hr,right k]
          exact ((ordinaryAt hc h (by omega : k < d)).clean (hs k (by omega)) (hs (k+1) hi)).2
      · simpa [step,Ne.symm ho,Ne.symm hr] using hs i hi
  by_cases ho : e = a j
  · by_cases hD : j = d
    · subst j
      exact ⟨d,by omega,boundary ho,clean⟩
    · obtain ⟨_,hmove⟩ := (ordinaryAt hc h (by omega : j < d)).frontLeft hf
      rcases hmove with hStay | hGo
      · refine ⟨j,hj,?_,clean⟩
        rw [ho,left j]
        exact hStay
      · have hAt : Frontier (step x e (a (j+1))) := by simpa [ho,right j] using hGo
        refine ⟨j+1,by omega,hAt,?_⟩
        intro i hi
        by_cases hi' : i ≤ j
        · exact clean i hi'
        · have heC : i = j+1 := by omega
          rw [heC]
          exact frontier_ne_one hAt
  · refine ⟨j,hj,?_,clean⟩
    by_cases hr : rightNeighbor e = a j
    · cases j with
      | zero =>
        have hr' : rightNeighbor e = y := by simpa [a,liftedSite_zero] using hr
        have ht := supplier_incoming_frontier (x e) (x y) h.leader h.shield
          (by simpa [a,liftedSite_zero] using hf)
        have hne : y ≠ e := by rw [←hr']; exact right_ne_self hn e
        simpa [a,liftedSite_zero,step,hne,hr'] using ht
      | succ k =>
        rw [back k hr,right k]
        exact (ordinaryAt hc h (by omega : k < d)).frontRight hf
    · change Frontier (step x e (a j))
      rw [show step x e (a j) = x (a j) by
        unfold step
        rw [if_neg (Ne.symm ho),if_neg (Ne.symm hr)]]
      exact hf

#print axioms corridor_separator_step

#print axioms corridor_supplier_step

#print axioms outgoing_leader_shield
#print axioms supplier_step

#print axioms covered_kill_feedback

#print axioms ordinary_protection

#print axioms supplier_incoming
#print axioms ghost_feedback
#print axioms ready_live_impact

end L4.RankFresh
