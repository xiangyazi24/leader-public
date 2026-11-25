import Leader.L4.TripleResidual
import Leader.L4.FixedResidual
import Leader.L4.FreshSeparation

/-! Literal native rows for root-free-sector preparation and sealing.
All facts here concern the complete physical row, including payment and patrol. -/
namespace L4.TriplePrep

@[simp] private theorem beq_bullet_none (b : Bullet) : (b == .none) = true ↔ b = .none := by
  cases b <;> decide
@[simp] private theorem beq_bullet_none_false (b : Bullet) : (b == .none) = false ↔ b ≠ .none := by
  cases b <;> decide
@[simp] private theorem beq_signal_zero (b : Signal) : (b == .zero) = true ↔ b = .zero := by
  cases b <;> decide
@[simp] private theorem beq_signal_zero_false (b : Signal) : (b == .zero) = false ↔ b ≠ .zero := by
  cases b <;> decide

private theorem pay_native {p c : Nat} (a b : Site p c) :
    ((payment a b).1.bullet, (payment a b).1.signal, (payment a b).1.shield,
      (payment a b).2.bullet, (payment a b).2.signal, (payment a b).2.shield,
      (payment a b).2.leader) =
    (a.bullet, a.signal, a.shield, b.bullet, b.signal, b.shield, b.leader) := by
  unfold payment
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

private theorem payload_last {p c : Nat} (u v : Site p c)
    (h : (stepPrefix u v).1.mark = false ∨ (stepPrefix u v).2.leader = true) :
    ((pairStep u v).1.bullet, (pairStep u v).1.signal, (pairStep u v).1.shield,
      (pairStep u v).2.bullet, (pairStep u v).2.signal, (pairStep u v).2.shield,
      (pairStep u v).2.leader) =
    ((stepPrefix u v).1.bullet, (stepPrefix u v).1.signal, (stepPrefix u v).1.shield,
      (stepPrefix u v).2.bullet, (stepPrefix u v).2.signal, (stepPrefix u v).2.shield,
      (stepPrefix u v).2.leader) := by
  unfold pairStep
  generalize stepPrefix u v = w at h ⊢
  rcases w with ⟨a,b⟩
  rcases h with h | h <;> dsimp only at h ⊢ <;> simp [patrolWrite,finishBirth,pinned,h]

private theorem ordinary_no_birth {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hv : v.leader = false) :
    (stepPrefix u v).1.mark = false := by
  have hmat : materialize u v = u := by simp [materialize,defect,hm,hr,hv]
  have hf : fireResponder v = v := by simp [fireResponder,hv]
  unfold stepPrefix native
  rw [hmat,hf]
  generalize hi : fireInitiator u = a
  have ha : a.mark = false := by
    rw [← hi]; unfold fireInitiator; split <;> exact hm
  rw [show impact a v = (a,v) by simp [impact,hv]]
  cases hb : a.bullet <;> simp [pinned,ha,hv,followerBullet,hb,payment] <;> split <;> rfl

/-- Ordinary-edge payload equals the native payload, independent of stock
and every timer/rail byte. This includes arbitrary inherited signals or bullets. -/
theorem ordinary_native_payload {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hv : v.leader = false) :
    ((pairStep u v).1.bullet, (pairStep u v).1.signal, (pairStep u v).1.shield,
      (pairStep u v).2.bullet, (pairStep u v).2.signal, (pairStep u v).2.shield,
      (pairStep u v).2.leader) =
    ((native u v).1.bullet, (native u v).1.signal, (native u v).1.shield,
      (native u v).2.bullet, (native u v).2.signal, (native u v).2.shield,
      (native u v).2.leader) := by
  have hp := payload_last u v (.inl (ordinary_no_birth u v hm hr hv))
  have hmat : materialize u v = u := by simp [materialize,defect,hm,hr,hv]
  rw [hp]
  simpa [stepPrefix,hmat] using pay_native (native u v).1 (native u v).2

/-- A quiet donor cannot acquire a bullet from its right. Its signal samples
the ordinary responder, including a zero-signaled front as a separator. -/
theorem ordinary_empty_donor {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hv : v.leader = false) (hb : u.bullet = .none)
    (hu : u.leader = false ∨ u.signal = .zero) :
    (pairStep u v).1.bullet = .none ∧
    (pairStep u v).1.signal = Signal.max u.signal v.signal ∧
    (pairStep u v).2.bullet = v.bullet ∧
    (pairStep u v).2.signal = v.signal := by
  have hf : fireInitiator u = u := by
    rcases hu with h | h <;> simp [fireInitiator,h]
  have q := ordinary_native_payload u v hm hr hv
  simp [native, hf, fireResponder,hv,impact,pinned,hm,followerBullet,hb] at q
  exact ⟨q.1,q.2.1,q.2.2.2.1,q.2.2.2.2.1⟩

/-- Ready or urgent outgoing source fires live. An older resident may
replace the proof identity but is still a nonempty front with a zero trail. -/
theorem outgoing_first_front {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hv : v.leader = false) (hu : u.leader = true) (hs : u.signal ≠ .zero) :
    (pairStep u v).1.bullet = .none ∧ (pairStep u v).1.signal = .zero ∧
    (pairStep u v).1.shield = true ∧
    (pairStep u v).2.bullet = (if v.bullet = .none then .live else v.bullet) ∧
    (pairStep u v).2.signal = .zero := by
  have hf : fireInitiator u = {u with bullet := .live, shield := true, signal := .zero} := by
    cases h : u.signal <;> simp_all [fireInitiator]
  have q := ordinary_native_payload u v hm hr hv
  simp [native,hf,hv,fireResponder,impact,pinned,hm,followerBullet,Signal.max] at q
  exact ⟨q.1,q.2.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1⟩

/-- A surviving leader boundary is a perfect separator. Its output is
N1 on its own old payload, irrespective of the incoming donor; in the
opposite direction it supplies one after absorbing any donor bullet.
This covers incoming launch at the prepared sector's source and the
terminal return at its target, even when both are on the same mark. -/
theorem surviving_terminal {p c : Nat} (u v : Site p c)
    (hv : v.leader = true)
    (hs : (fireInitiator u).bullet ≠ .live ∨ (fireResponder v).shield = true) :
    (pairStep u v).1.bullet = .none ∧
    (pairStep u v).1.signal = Signal.max (fireInitiator u).signal .one ∧
    (pairStep u v).1.shield = (fireInitiator u).shield ∧
    (pairStep u v).2.bullet = (fireResponder v).bullet ∧
    (pairStep u v).2.signal = (fireResponder v).signal ∧
    (pairStep u v).2.shield = (fireResponder v).shield ∧
    (pairStep u v).2.leader = true := by
  have hmat : materialize u v = {u with mark := true} := by simp [materialize,hv]
  have hi : fireInitiator (materialize u v) = {fireInitiator u with mark := true} := by
    rw [hmat]
    unfold fireInitiator
    split <;> rfl
  have hl : (fireResponder v).leader = true := by
    cases h : v.signal <;> simp [fireResponder,hv,h]
  have hPrefix :
      ((stepPrefix u v).1.bullet, (stepPrefix u v).1.signal, (stepPrefix u v).1.shield,
       (stepPrefix u v).2.bullet, (stepPrefix u v).2.signal, (stepPrefix u v).2.shield,
       (stepPrefix u v).2.leader) =
      (.none,Signal.max (fireInitiator u).signal .one,(fireInitiator u).shield,
       (fireResponder v).bullet,(fireResponder v).signal,(fireResponder v).shield,true) := by
    unfold stepPrefix native
    rw [hi]
    generalize hA : fireInitiator u = a at hs ⊢
    generalize hB : fireResponder v = b at hl hs ⊢
    cases h : a.bullet
    · simp [h,impact,hl,followerBullet,payment]
    · simp [h,impact,hl,followerBullet,payment,show (Bullet.dummy == Bullet.live) = false by decide]
    · have hh : b.shield = true := hs.resolve_left (by simp [h])
      simp [h,impact,hl,followerBullet,payment,hh]
  have hL : (stepPrefix u v).2.leader = true :=
    congrArg (fun q => q.2.2.2.2.2.2) hPrefix
  have h := (payload_last u v (.inr hL)).trans hPrefix
  simpa only [Prod.mk.injEq] using h

/-- Specialization to a successful READY incoming orientation. The
resulting stationary front is a dummy, the source is zero/unshielded
and remains a leader. -/
theorem ready_incoming_dummy {p c : Nat} (u v : Site p c)
    (hv : v.leader = true) (h1 : v.signal = .one)
    (hs : (fireInitiator u).bullet ≠ .live) :
    (pairStep u v).2.bullet = .dummy ∧
    (pairStep u v).2.signal = .zero ∧
    (pairStep u v).2.shield = false ∧ (pairStep u v).2.leader = true := by
  simpa [fireResponder,hv,h1] using (surviving_terminal u v hv (.inl hs)).2.2.2

/-- Incoming exterior traffic cannot alter the payload of a zero-signal
source except by ending the trial through actual death. -/
theorem zero_incoming_stable {p c : Nat} (u v : Site p c)
    (hv : v.leader = true) (h0 : v.signal = .zero)
    (hs : (fireInitiator u).bullet ≠ .live ∨ v.shield = true) :
    (pairStep u v).2.bullet = v.bullet ∧
    (pairStep u v).2.signal = .zero ∧
    (pairStep u v).2.shield = v.shield ∧ (pairStep u v).2.leader = true := by
  have hs' : (fireInitiator u).bullet ≠ .live ∨ (fireResponder v).shield = true := by
    simpa [fireResponder,hv,h0] using hs
  simpa [fireResponder,hv,h0] using (surviving_terminal u v hv hs').2.2.2


open TripleResidual

/-- A launched clearing front and the swept zero/empty prefix. No
hypothesis whatsoever is imposed on native fields strictly ahead. -/
structure ZeroFront {p c n : Nat} (x : Config p c n) (s : Fin n) (q : Nat) : Prop where
  signal : (x (liftedSite s q)).signal = .zero
  bullet : (x (liftedSite s q)).bullet ≠ .none
  swept : ∀ j, j < q → (x (liftedSite s j)).signal = .zero ∧
    (x (liftedSite s j)).bullet = .none

private theorem separate_neighbor {n : Nat} (hn : 4 ≤ n) (e : Fin n) : rightNeighbor e ≠ e := by
  intro h
  have he : liftedSite e 1 = liftedSite e 0 := by simpa [liftedSite_succ,liftedSite_zero] using h
  have hh := liftedSite_inj e (by omega : 1<n) (by omega : 0<n) he
  omega

private theorem terminal_safe {p c n : Nat} (x : Config p c n) (e : Fin n)
    (hl : (x (rightNeighbor e)).leader = true) (he : event x e = false) :
    (fireInitiator (x e)).bullet ≠ .live ∨
    (fireResponder (x (rightNeighbor e))).shield = true := by
  have hd := (Bool.or_eq_false_iff.mp he).1
  by_cases hf : (fireInitiator (x e)).bullet = .live
  · right
    cases hs : (fireResponder (x (rightNeighbor e))).shield
    · have hk := (death_iff_nativeKill x e).mpr ⟨hl,hf,hs⟩
      simp [hd] at hk
    · rfl
  · exact .inl hf

private theorem sector_ordinary {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d) {j : Nat} (hj : j < d) :
    (x (liftedSite s j)).mark = false ∧
    (x (rightNeighbor (liftedSite s j))).residue = nextResidue (x (liftedSite s j)).residue ∧
    (x (rightNeighbor (liftedSite s j))).leader = false := by
  have h := coveredOrdinary hc ((covered_noRoot_iff hm).mpr
    (Bool.eq_false_iff.mpr (hF.before j hj)))
  exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- Before the nominated forward edge, every other raw edge preserves
the entire swept trail and the front at its present offset, or stops.
In particular this allows arbitrary traffic into the source from outside. -/
theorem zeroFront_wait {p c n d q : Nat} (_hn : 4 ≤ n) (x : Config p c n)
    (s e : Fin n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (_hD : d+1<n) (hL : (x s).leader = true) (hQ : q ≤ d)
    (h : ZeroFront x s q) (he : event x e = false) (hw : e ≠ liftedSite s q) :
    ZeroFront (step x e) s q := by
  have prop : ∀ j, j ≤ q →
      (step x e (liftedSite s j)).signal = .zero ∧
      (step x e (liftedSite s j)).bullet = (x (liftedSite s j)).bullet := by
    intro j hj
    have sig : ∀ i, i ≤ q → (x (liftedSite s i)).signal = .zero := by
      intro i hi
      by_cases hEq : i = q
      · subst i; exact h.signal
      · exact (h.swept i (by omega)).1
    by_cases hE : liftedSite s j = e
    · have hjq : j < q := by
        by_cases H : j < q
        · exact H
        have eq : j = q := by omega
        subst j
        exact (hw hE.symm).elim
      have hO := sector_ordinary x s hm hc hF (show j < d by omega)
      have hh := ordinary_empty_donor _ _ hO.1 hO.2.1 hO.2.2 (h.swept j hjq).2 (.inr (sig j hj))
      have hr' : (x (rightNeighbor (liftedSite s j))).signal = .zero := by
        rw [← liftedSite_succ]; exact sig (j+1) (by omega)
      rw [sig j hj,hr'] at hh
      have hb := (h.swept j hjq).2
      rw [← hE]
      simpa [step,Signal.max,hb] using And.intro hh.2.1 hh.1
    · by_cases hR : liftedSite s j = rightNeighbor e
      · cases j with
        | zero =>
          have hl : (x (rightNeighbor e)).leader = true := by rw [← hR,liftedSite_zero]; exact hL
          have hz : (x (rightNeighbor e)).signal = .zero := hR ▸ sig 0 (Nat.zero_le _)
          have hS := terminal_safe x e hl he
          rw [show fireResponder (x (rightNeighbor e)) = x (rightNeighbor e) by simp [fireResponder,hl,hz]] at hS
          have hh := zero_incoming_stable _ _ hl hz hS
          simpa only [step,if_neg hE,if_pos hR] using
            (show (pairStep (x e) (x (rightNeighbor e))).2.signal = .zero ∧
              (pairStep (x e) (x (rightNeighbor e))).2.bullet = (x (liftedSite s 0)).bullet from
              ⟨hh.2.1,hR.symm ▸ hh.1⟩)
        | succ j =>
          have hE' : liftedSite s j = e := FreshSeparation.succ_inj (by simpa [liftedSite_succ] using hR)
          have hO := sector_ordinary x s hm hc hF (show j < d by omega)
          have hh := ordinary_empty_donor _ _ hO.1 hO.2.1 hO.2.2
            (h.swept j (by omega)).2 (.inr (sig j (by omega)))
          rw [← liftedSite_succ s j] at hh
          rw [sig (j+1) hj] at hh
          have hh' : (pairStep (x e) (x (rightNeighbor e))).2.signal = .zero ∧
              (pairStep (x e) (x (rightNeighbor e))).2.bullet = (x (liftedSite s (j+1))).bullet := by
            rw [← hE',← liftedSite_succ]
            exact ⟨hh.2.2.2,hh.2.2.1⟩
          simpa only [step,if_neg hE,if_pos hR] using hh'
      · simpa only [step,if_neg hE,if_neg hR] using And.intro (sig j hj) (rfl :
          (x (liftedSite s j)).bullet = (x (liftedSite s j)).bullet)
  exact ⟨(prop q (Nat.le_refl _)).1, fun hb => h.bullet
    ((prop q (Nat.le_refl _)).2.symm.trans hb), fun j hj =>
    ⟨(prop j (by omega)).1,(prop j (by omega)).2.trans (h.swept j hj).2⟩⟩


/-- The nominated interior mark extends the protected prefix by one, with
collisions transferring the witness to the old resident at the new site. -/
theorem zeroFront_progress {p c n d q : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (s : Fin n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hD : d+1<n) (hQ : q < d) (h : ZeroFront x s q) :
    ZeroFront (step x (liftedSite s q)) s (q+1) := by
  let e := liftedSite s q
  have ho := sector_ordinary x s hm hc hF hQ
  have hp := ordinary_front_step _ _ ho.1 ho.2.1 ho.2.2 h.signal h.bullet
  have hR : liftedSite s (q+1) = rightNeighbor e := liftedSite_succ s q
  have hne : rightNeighbor e ≠ e := separate_neighbor hn e
  have hpost : step x e (liftedSite s (q+1)) = (pairStep (x e) (x (rightNeighbor e))).2 := by
    simp [step,hR,hne]
  refine ⟨hpost ▸ hp.2.2.2, ?_, ?_⟩
  · rw [hpost,hp.2.1]
    split
    · exact h.bullet
    · rename_i hbad
      exact fun hEq => hbad (by simp [hEq])
  · intro j hj
    by_cases hjq : j = q
    · subst j
      simpa [step,e] using And.intro hp.2.2.1 hp.1
    · have hE : liftedSite s j ≠ e := fun he => hjq (liftedSite_inj s (by omega) (by omega) he)
      have hN : liftedSite s j ≠ rightNeighbor e := by
        rw [← hR]
        intro hh
        have hEq := liftedSite_inj s (by omega : j<n) (by omega : q+1<n) hh
        omega
      change (step x e (liftedSite s j)).signal = _ ∧ (step x e (liftedSite s j)).bullet = _
      simpa only [step,if_neg hE,if_neg hN] using h.swept j (by omega)

def ReturnSeed {p c n : Nat} (x : Config p c n) (s : Fin n) (d : Nat) : Prop :=
  ((x (liftedSite s d)).signal = .one ∧ (x (liftedSite s d)).bullet = .none) ∧
    ∀ j, j < d → (x (liftedSite s j)).signal = .zero ∧ (x (liftedSite s j)).bullet = .none

/-- At the terminal mark, either the trial stops or the whole open sector
is bullet-free and the last offset now carries return colour one. -/
theorem zeroFront_terminal {p c n d : Nat} (x : Config p c n)
    (s : Fin n) (hD : d+1<n) (h : ZeroFront x s d)
    (hl : (x (liftedSite s (d+1))).leader = true)
    (hs : event x (liftedSite s d) = false) :
    ReturnSeed (step x (liftedSite s d)) s d := by
  let e := liftedSite s d
  have hR : liftedSite s (d+1) = rightNeighbor e := liftedSite_succ s d
  have hL : (x (rightNeighbor e)).leader = true := hR ▸ hl
  have hh := surviving_terminal _ _ hL (terminal_safe x e hL hs)
  have hi : fireInitiator (x e) = x e := by simp [fireInitiator,e,h.signal]
  rw [hi] at hh
  have hSig : (x e).signal = .zero := h.signal
  rw [hSig] at hh
  refine ⟨?_,?_⟩
  · simpa [step,e,Signal.max] using And.intro hh.2.1 hh.1
  · intro j hj
    have hE : liftedSite s j ≠ e := by
      intro hEq
      have h' := liftedSite_inj s (by omega : j<n) (by omega : d<n) hEq
      omega
    have hN : liftedSite s j ≠ rightNeighbor e := by
      rw [← hR]
      intro hEq
      have h' := liftedSite_inj s (by omega : j<n) hD hEq
      omega
    change (step x e (liftedSite s j)).signal = _ ∧ (step x e (liftedSite s j)).bullet = _
    simpa only [step,if_neg hE,if_neg hN] using h.swept j hj

#print axioms ordinary_native_payload
#print axioms surviving_terminal
#print axioms zeroFront_wait
#print axioms zeroFront_progress
#print axioms zeroFront_terminal


/-- The nearest one is tracked while the suffix is only required to be binary. -/
structure ReturnFront {p c n : Nat} (x : Config p c n) (s : Fin n) (d q : Nat) : Prop where
  le : q ≤ d
  empty : ∀ j, j ≤ d → (x (liftedSite s j)).bullet = .none
  binary : ∀ j, j ≤ d → (x (liftedSite s j)).signal ≠ .two
  one : (x (liftedSite s q)).signal = .one
  before : ∀ j, j < q → (x (liftedSite s j)).signal = .zero

theorem ReturnSeed.front {p c n d : Nat} {x : Config p c n} {s : Fin n}
    (h : ReturnSeed x s d) : ReturnFront x s d d := by
  refine ⟨Nat.le_refl _, ?_, ?_, h.1.1, fun j hj => (h.2 j hj).1⟩
  · intro j hj
    by_cases he : j = d
    · subst j; exact h.1.2
    · exact (h.2 j (by omega)).2
  · intro j hj
    by_cases he : j = d
    · subst j; simp [h.1.1]
    · simp [(h.2 j (by omega)).1]

private theorem max_binary {u v : Signal} (hU : u ≠ .two) (hV : v ≠ .two) :
    Signal.max u v ≠ .two := by
  cases u <;> cases v <;> simp_all [Signal.max]

private theorem max_one {u : Signal} (h : u ≠ .two) : Signal.max .one u = .one := by
  cases u <;> simp_all [Signal.max]

/-- Exact pointwise physical projection while a return front is nonready:
every site remains bullet-free; just the selected sector donor samples
from its successor. The true terminal supplies one independently of its
own activity, and an incoming exterior mark cannot write the sealed sector. -/
theorem empty_sector_snapshot {p c n d : Nat} (x : Config p c n)
    (s e : Fin n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader = true) (hT : (x (liftedSite s (d+1))).leader = true)
    (hB : ∀ i, i ≤ d → (x (liftedSite s i)).bullet = .none)
    (h0 : (x (liftedSite s 0)).signal = .zero)
    (he : event x e = false) (j : Nat) (hj : j ≤ d) :
    let y := if j = d then Signal.one else (x (liftedSite s (j+1))).signal
    (step x e (liftedSite s j)).bullet = .none ∧
    (step x e (liftedSite s j)).signal =
      if liftedSite s j = e then Signal.max (x (liftedSite s j)).signal y
      else (x (liftedSite s j)).signal := by
  dsimp only
  let y := if j = d then Signal.one else (x (liftedSite s (j+1))).signal
  have no_fire (i : Nat) (hi : i ≤ d) : (x (liftedSite s i)).leader = false ∨
      (x (liftedSite s i)).signal = .zero := by
    cases i with
    | zero => exact .inr (h0)
    | succ i =>
      exact .inl (by simpa [liftedSite_succ] using
        (sector_ordinary x s hm hc hF (show i < d by omega)).2.2)
  by_cases hE : liftedSite s j = e
  · simp only [if_pos hE]
    by_cases hJ : j = d
    · subst j
      have hV : (x (rightNeighbor (liftedSite s d))).leader = true := by
        simpa [liftedSite_succ] using hT
      have hN : fireInitiator (x (liftedSite s d)) = x (liftedSite s d) := by
        rcases no_fire d (Nat.le_refl _) with ha | ha <;> simp [fireInitiator,ha]
      have ht := surviving_terminal _ _ hV (.inl (by rw [hN,hB d (Nat.le_refl _)]; decide))
      rw [hN] at ht
      rw [← hE]
      simpa [step] using And.intro ht.1 ht.2.1
    · have H := sector_ordinary x s hm hc hF (show j < d by omega)
      have ht := ordinary_empty_donor _ _ H.1 H.2.1 H.2.2 (hB j hj) (no_fire j hj)
      rw [← hE]
      simpa [step,hJ,liftedSite_succ] using And.intro ht.1 ht.2.1
  · simp only [if_neg hE]
    by_cases hR : liftedSite s j = rightNeighbor e
    · cases j with
      | zero =>
        have hl : (x (rightNeighbor e)).leader = true := by rw [← hR,liftedSite_zero]; exact hL
        have hz : (x (rightNeighbor e)).signal = .zero := hR ▸ h0
        have hS := terminal_safe x e hl he
        rw [show fireResponder (x (rightNeighbor e)) = x (rightNeighbor e) by simp [fireResponder,hl,hz]] at hS
        have hi := zero_incoming_stable _ _ hl hz hS
        refine ⟨?_,?_⟩
        · simpa only [step,if_neg hE,if_pos hR] using hi.1.trans (hR ▸ hB 0 (by omega))
        · simpa only [step,if_neg hE,if_pos hR] using hi.2.1.trans (h0).symm
      | succ j =>
        have hE' : liftedSite s j = e := FreshSeparation.succ_inj (by simpa [liftedSite_succ] using hR)
        have hO := sector_ordinary x s hm hc hF (show j < d by omega)
        have hi := ordinary_empty_donor _ _ hO.1 hO.2.1 hO.2.2 (hB j (by omega)) (no_fire j (by omega))
        simp only [step,if_neg hE,if_pos hR]
        rw [← hE',← liftedSite_succ]
        simpa only [liftedSite_succ] using (And.intro (hi.2.2.1.trans (by simpa [liftedSite_succ] using hB (j+1) hj)) hi.2.2.2)
    · simpa [step,hE,hR] using hB j hj

theorem return_snapshot {p c n d q : Nat} (x : Config p c n)
    (s e : Fin n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader = true) (hT : (x (liftedSite s (d+1))).leader = true)
    (h : ReturnFront x s d (q+1)) (he : event x e = false) (j : Nat) (hj : j ≤ d) :
    let y := if j = d then Signal.one else (x (liftedSite s (j+1))).signal
    (step x e (liftedSite s j)).bullet = .none ∧
    (step x e (liftedSite s j)).signal =
      if liftedSite s j = e then Signal.max (x (liftedSite s j)).signal y
      else (x (liftedSite s j)).signal :=
  empty_sector_snapshot x s e hm hc hF hL hT h.empty (h.before 0 (by omega)) he j hj

/-- A return moves uniquely on its nominated predecessor mark. The phase
with nearest one at zero is READY. -/
theorem returnFront_step {p c n d q : Nat} (x : Config p c n)
    (s e : Fin n) (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (_hD : d+1<n) (hL : (x s).leader = true) (hT : (x (liftedSite s (d+1))).leader = true)
    (h : ReturnFront x s d (q+1)) (he : event x e = false) :
    ReturnFront (step x e) s d (if e = liftedSite s q then q else q+1) := by
  have hDq := h.le
  let r := if e = liftedSite s q then q else q+1
  have hr : r ≤ d := by dsimp [r]; split <;> omega
  have snap := return_snapshot x s e hm hc hF hL hT h he
  have both (j : Nat) (hj : j ≤ d) : (if j = d then Signal.one else
      (x (liftedSite s (j+1))).signal) ≠ .two := by
    split
    · decide
    · exact h.binary (j+1) (by omega)
  refine ⟨hr, fun j hj => (snap j hj).1, ?_, ?_, ?_⟩
  · intro j hj
    rw [(snap j hj).2]
    split
    · exact max_binary (h.binary j hj) (both j hj)
    · exact h.binary j hj
  · change (step x e (liftedSite s r)).signal = .one
    rw [(snap r hr).2]
    by_cases hh : e = liftedSite s q
    · have hqd : q ≠ d := by omega
      simp [r,hh,hqd,h.before q (by omega),h.one,Signal.max]
    · simp only [r,if_neg hh,h.one]
      split
      · exact max_one (both (q+1) hDq)
      · rfl
  · intro j hj
    change j < r at hj
    have hjD : j ≤ d := by omega
    rw [(snap j hjD).2]
    have hjQ : j < q+1 := by dsimp [r] at hj; split at hj <;> omega
    rw [h.before j hjQ]
    split
    · rename_i hh
      have hjq : j < q := by
        by_cases heq : e = liftedSite s q
        · simpa [r,heq] using hj
        · have hne : j ≠ q := by
            intro H; subst j; exact heq hh.symm
          omega
      have hjd : j ≠ d := by omega
      simp [hjd,h.before (j+1) (by omega),Signal.max]
    · rfl

#print axioms returnFront_step


/-- A ready source met on its incoming mark starts a zero-signal clearing
front immediately, or there is an actual global event on this mark. -/
theorem sourceIncoming_starts_front {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (e s : Fin n) (hR : rightNeighbor e = s) (hL : (x s).leader = true)
    (hS : (x s).signal ≠ .zero) (he : event x e = false) :
    ZeroFront (step x e) s 0 ∧
    ((step x e s).bullet, (step x e s).shield) =
      if (x s).signal = .one then (.dummy,false) else (.live,true) := by
  subst s
  have hh := surviving_terminal _ _ hL (terminal_safe x e hL he)
  have hr : rightNeighbor e ≠ e := separate_neighbor hn e
  have hpost : step x e (rightNeighbor e) = (pairStep (x e) (x (rightNeighbor e))).2 := by simp [step,hr]
  cases H : (x (rightNeighbor e)).signal
  · exact (hS H).elim
  · have hb : (step x e (rightNeighbor e)).bullet = .dummy := by
      simpa [hpost,fireResponder,hL,H] using hh.2.2.2.1
    have hz : (step x e (rightNeighbor e)).signal = .zero := by
      simpa [hpost,fireResponder,hL,H] using hh.2.2.2.2.1
    have hs : (step x e (rightNeighbor e)).shield = false := by
      simpa [hpost,fireResponder,hL,H] using hh.2.2.2.2.2.1
    refine ⟨⟨?_,?_,fun j hj => (by omega : False).elim⟩,?_⟩
    · simpa [liftedSite_zero] using hz
    · simp [liftedSite_zero,hb]
    · simp [hb,hs]
  · have hb : (step x e (rightNeighbor e)).bullet = .live := by
      simpa [hpost,fireResponder,hL,H] using hh.2.2.2.1
    have hz : (step x e (rightNeighbor e)).signal = .zero := by
      simpa [hpost,fireResponder,hL,H] using hh.2.2.2.2.1
    have hs : (step x e (rightNeighbor e)).shield = true := by
      simpa [hpost,fireResponder,hL,H] using hh.2.2.2.2.2.1
    refine ⟨⟨?_,?_,fun j hj => (by omega : False).elim⟩,?_⟩
    · simpa [liftedSite_zero] using hz
    · simp [liftedSite_zero,hb]
    · simp [hb,hs]

/-- The outgoing launch starts at offset one when the sector has an
interior site, rather than consuming another artificial launcher mark. -/
theorem sourceOutgoing_starts_front {p c n d : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (s : Fin n) (hm : MCOV x) (hc : COV x)
    (hF : FirstMark x s d) (hD : 0 < d)
    (hL : (x s).leader = true) (hS : (x s).signal ≠ .zero) :
    ZeroFront (step x s) s 1 ∧ (step x s s).shield = true := by
  have hO := sector_ordinary x s hm hc hF hD
  rw [liftedSite_zero] at hO
  have hp := outgoing_first_front _ _ hO.1 hO.2.1 hO.2.2 hL hS
  have hR : liftedSite s 1 = rightNeighbor s := by rw [show 1 = 0+1 by rfl,liftedSite_succ,liftedSite_zero]
  have hn' : rightNeighbor s ≠ s := separate_neighbor hn s
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · simpa [step,hR,hn'] using hp.2.2.2.2
  · rw [show step x s (liftedSite s 1) = (pairStep (x s) (x (rightNeighbor s))).2 by
          simp [step,hR,hn'],hp.2.2.2.1]
    split
    · decide
    · assumption
  · intro j hj
    have : j = 0 := by omega
    subst j
    simpa [step,liftedSite_zero] using And.intro hp.2.1 hp.1
  · simpa [step] using hp.2.2.1

/-- No fabricated return hit on an adjacent outgoing launch: due to
N0 before N2 and N5, a surviving target immediately provides READY. -/
theorem sourceOutgoing_adjacent_ready {p c n : Nat} (x : Config p c n)
    (s : Fin n) (hL : (x s).leader = true) (hT : (x (rightNeighbor s)).leader = true)
    (hS : (x s).signal ≠ .zero) (he : event x s = false) :
    ReturnFront (step x s) s 0 0 ∧ (step x s s).shield = true := by
  have hp := surviving_terminal _ _ hT (terminal_safe x s hT he)
  have hr : fireInitiator (x s) = { x s with bullet := .live, shield := true, signal := .zero } := by
    cases hh : (x s).signal <;> simp_all [fireInitiator]
  rw [hr] at hp
  have hb : (step x s s).bullet = .none := by simpa [step] using hp.1
  have hs : (step x s s).signal = .one := by simpa [step,Signal.max] using hp.2.1
  refine ⟨⟨Nat.le_refl _, ?_,?_,?_,?_⟩,?_⟩
  · intro j hj; have : j=0 := by omega
    simpa [this,liftedSite_zero] using hb
  · intro j hj; have : j=0 := by omega
    simp [this,liftedSite_zero,hs]
  · simpa [liftedSite_zero] using hs
  · intro j hj
    omega
  · simpa [step] using hp.2.2.1

#print axioms sourceIncoming_starts_front
#print axioms sourceOutgoing_starts_front
#print axioms sourceOutgoing_adjacent_ready

inductive PrepPhase where
  | forward (q : Nat)
  | backward (q : Nat)
  deriving DecidableEq

private def prepNom {n : Nat} (s : Fin n) : PrepPhase → Fin n
  | .forward q => liftedSite s q
  | .backward q => liftedSite s (q-1)

private def prepTick {n : Nat} (s : Fin n) (d : Nat) (ph : PrepPhase) (e : Fin n) : PrepPhase :=
  if e = prepNom s ph then match ph with
    | .forward q => if q < d then .forward (q+1) else .backward d
    | .backward q => .backward (q-1)
  else ph

private def prepBudget (d : Nat) : PrepPhase → Nat
  | .forward q => 2*d+1-q
  | .backward q => q

private def prepOK {p c n : Nat} (s : Fin n) (d : Nat)
    (x : Config p c n) : PrepPhase → Prop
  | .forward q => q ≤ d ∧ ZeroFront x s q
  | .backward q => ReturnFront x s d q

private def prepared {p c n : Nat} (s : Fin n) (d : Nat) (y : Obs p c n) : Prop :=
  y.stopped = true ∨ ReturnFront y.config s d 0

private theorem prepOnce {p c n : Nat} (s : Fin n) (d : Nat) (e : Fin n)
    (y : Obs p c n) (ph : PrepPhase) (hn : 4 ≤ n) (hD : d+1<n)
    (hG : MCOV y.config ∧ COV y.config ∧ FirstMark y.config s d ∧
      (y.config s).leader = true ∧ (y.config (liftedSite s (d+1))).leader = true)
    (hCert : prepOK s d y.config ph) (hLive : ¬ prepared s d y)
    (hE : (advance y e).stopped = false) :
    (MCOV (advance y e).config ∧ COV (advance y e).config ∧
      FirstMark (advance y e).config s d ∧ ((advance y e).config s).leader = true ∧
      ((advance y e).config (liftedSite s (d+1))).leader = true) ∧
      prepOK s d (advance y e).config (prepTick s d ph e) := by
  have hy : y.stopped = false := by
    cases h : y.stopped
    · rfl
    · exact (hLive (.inl h)).elim
  have hN : event y.config e = false := by simpa [advance,hy] using hE
  rcases hG with ⟨hm,hc,hF,hL,hT⟩
  have cv := EntranceCover.cover_closed hn y.config e ⟨hm,hc⟩
  simp only [advance,hy,Bool.false_eq_true,if_false]
  refine ⟨⟨cv.1,cv.2,no_event_sector hn _ _ _ hm hc hN hL hT hF hD,
    no_event_preserves_leader hn _ _ _ hc hN hL,
    no_event_preserves_leader hn _ _ _ hc hN hT⟩,?_⟩
  cases ph with
  | forward q =>
    obtain ⟨hq,hFront⟩ := hCert
    by_cases hHit : e = liftedSite s q
    · subst e
      by_cases hLt : q < d
      · simpa [prepTick,prepNom,hLt,prepOK] using
          And.intro (show q+1 ≤ d by omega) (zeroFront_progress hn _ s hm hc hF hD hLt hFront)
      · have hEq : q = d := by omega
        subst q
        simpa [prepTick,prepNom,prepOK] using (zeroFront_terminal _ s hD hFront hT hN).front
    · simpa [prepTick,prepNom,prepOK,hHit] using
        And.intro hq (zeroFront_wait hn _ s e hm hc hF hD hL hq hFront hN hHit)
  | backward q =>
    cases q with
    | zero => exact (hLive (.inr hCert)).elim
    | succ q =>
      by_cases he : e = liftedSite s q <;>
        simpa [prepTick,prepNom,prepOK,he] using returnFront_step _ s e hm hc hF hD hL hT hCert hN

private theorem prepBudget_step {p c n : Nat} (s : Fin n) (d : Nat) (x : Config p c n)
    (ph : PrepPhase) (e : Fin n) (h : prepOK s d x ph)
    (hz : ph ≠ .backward 0) :
    prepBudget d (prepTick s d ph e) + (if e = prepNom s ph then 1 else 0) ≤
      prepBudget d ph := by
  cases ph with
  | forward q =>
    have hq : q ≤ d := h.1
    by_cases he : e = liftedSite s q
    · by_cases hlt : q < d <;> simp [prepTick,prepNom,prepBudget,he,hlt] <;> omega
    · simp [prepTick,prepNom,prepBudget,he]
  | backward q =>
    have hq : 0 < q := by cases q <;> simp_all
    by_cases he : e = liftedSite s (q-1)
    · simp [prepTick,prepNom,prepBudget,he]; omega
    · simp [prepTick,prepNom,prepBudget,he]

/-- The actual projected phase clock. The auxiliary phase never changes
which physical mark is executed. Its freeze at first READY affects only
the proof phase; the physical projection continues to execute the row. -/
private noncomputable def prepNext {p c n : Nat} (s : Fin n) (d : Nat)
    (q : PrepPhase × Obs p c n) (e : Fin n) : PrepPhase × Obs p c n := by
  classical
  exact (if prepared s d q.2 then q.1 else prepTick s d q.1 e,advance q.2 e)

open TaggedTail

private theorem sum_cons {n : Nat} (f : Fin (n+1) → Nat) :
    sumEdge f = f 0 + sumEdge (fun e : Fin n => f e.succ) := by
  simp [sumEdge,List.ofFn_succ]

private theorem sum_monotone {n : Nat} (f g : Fin n → Nat)
    (h : ∀ e, f e ≤ g e) : sumEdge f ≤ sumEdge g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [sum_cons f,sum_cons g]
    exact Nat.add_le_add (h 0) (ih _ _ (fun e => h e.succ))

private theorem sum_add {n : Nat} (f g : Fin n → Nat) :
    sumEdge (fun e => f e + g e) = sumEdge f + sumEdge g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_cons,sum_cons f,sum_cons g,ih]; omega

private theorem sum_mul {n : Nat} (f : Fin n → Nat) (a : Nat) :
    sumEdge (fun e => a * f e) = a * sumEdge f := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_cons,sum_cons f,ih,Nat.mul_add]

private theorem sum_const (n a : Nat) : sumEdge (fun _ : Fin n => a) = n*a := by
  induction n with
  | zero => simp [sumEdge]
  | succ n ih => rw [sum_cons,ih,Nat.succ_mul,Nat.add_comm]

private theorem sum_one_at {n : Nat} (i : Fin n) :
    sumEdge (fun e => if e = i then 1 else 0) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [sum_cons]
      have hz : (fun e : Fin n => if e.succ = (0 : Fin (n+1)) then 1 else 0) =
          (fun _ : Fin n => 0) := by funext e; simp [Fin.succ_ne_zero]
      rw [hz,sum_const]
      simp
    · rw [sum_cons,if_neg (Ne.symm (Fin.succ_ne_zero j))]
      have hh : (fun e : Fin n => if e.succ = j.succ then 1 else 0) =
          (fun e : Fin n => if e = j then 1 else 0) := by funext e; simp
      rw [hh,ih,Nat.zero_add]

/-- Actual uniform-edge time from a just-launched clearing front through
the swept return to READY, or an earlier physical stop. No independence
assumption is made about nominations. If the launch was outgoing, use
q=1; if incoming, use q=0. The target is an actual physical sector state. -/
theorem expected_ready_after_front {p c n d q : Nat}
    (x : Config p c n) (s : Fin n) (hn : 4 ≤ n) (hD : d+1<n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hS : (x s).leader = true) (hT : (x (liftedSite s (d+1))).leader = true)
    (hq : q ≤ d) (h : ZeroFront x s q) :
    IIDExpectedHittingTimeAtMost advance (fun y => y.stopped = true ∨ ReturnFront y.config s d 0)
      (init x) (n*(2*d+1-q)) := by
  classical
  let target := fun (z : PrepPhase × Obs p c n) => prepared s d z.2
  let start : PrepPhase × Obs p c n := (.forward q,init x)
  let next := prepNext s d (p:=p) (c:=c)
  let good := fun (z : PrepPhase × Obs p c n) =>
      target z ∨ ((MCOV z.2.config ∧ COV z.2.config ∧
      FirstMark z.2.config s d ∧ (z.2.config s).leader = true ∧
      (z.2.config (liftedSite s (d+1))).leader = true) ∧ prepOK s d z.2.config z.1)
  let B := fun (z : PrepPhase × Obs p c n) => if target z then 0 else prepBudget d z.1
  have advance_cert : ∀ z e, good z → ¬ target z →
      good (next z e) ∧ B (next z e) + (if e = prepNom s z.1 then 1 else 0) ≤ B z := by
    intro z e hz hLive
    have hCert := hz.resolve_left hLive
    have hNz : z.1 ≠ .backward 0 := by
      intro hz
      exact hLive (.inr (by simpa [prepOK,hz] using hCert.2))
    have hbudget := prepBudget_step s d z.2.config z.1 e hCert.2 hNz
    have hNextBudget : B (next z e) ≤ prepBudget d (prepTick s d z.1 e) := by
      dsimp only [B]
      split
      · omega
      · simp [next,prepNext,show ¬ prepared s d z.2 from hLive]
    refine ⟨?_,?_⟩
    · by_cases hGo : (advance z.2 e).stopped = true
      · exact .inl (.inl hGo)
      · have hGo' : (advance z.2 e).stopped = false := Bool.eq_false_iff.mpr hGo
        have hh := prepOnce s d e z.2 z.1 hn hD hCert.1 hCert.2 hLive hGo'
        exact .inr (by simpa [next,prepNext,show ¬ prepared s d z.2 from hLive] using hh)
    · exact Nat.le_trans (Nat.add_le_add_right hNextBudget _) (by simpa [B,hLive] using hbudget)
  have hbound : ∀ t z, good z → iidHitCost next target t z ≤ (n*B z)*n^t := by
    intro t
    induction t with
    | zero => intro z _; simp [iidHitCost]
    | succ t ih =>
      intro z hz
      by_cases ht : target z
      · rw [iidHitCost_of_target _ _ _ ht]; omega
      · rw [iidHitCost,if_neg ht]
        change n^(t+1) + sumEdge (fun e : Fin n => iidHitCost next target t (next z e)) ≤ _
        have hb := sum_monotone
          (fun e => B (next z e) + if e = prepNom s z.1 then 1 else 0)
          (fun _ => B z) (fun e => (advance_cert z e hz ht).2)
        rw [sum_add,sum_one_at,sum_const] at hb
        have hs := sum_monotone _ _ (fun e => ih (next z e) (advance_cert z e hz ht).1)
        have hm' : sumEdge (fun e => (n*B (next z e))*n^t) =
            n^(t+1) * sumEdge (fun e => B (next z e)) := by
          rw [← sum_mul]
          apply congrArg sumEdge
          funext e
          rw [Nat.pow_succ]
          ac_rfl
        have hfin := Nat.mul_le_mul_left (n^(t+1)) hb
        rw [Nat.mul_add,Nat.mul_one] at hfin
        calc
          _ ≤ n^(t+1) + sumEdge (fun e => (n*B (next z e))*n^t) := Nat.add_le_add_left hs _
          _ = n^(t+1) * sumEdge (fun e => B (next z e)) + n^(t+1) := by rw [hm',Nat.add_comm]
          _ ≤ n^(t+1)*(n*B z) := hfin
          _ = _ := Nat.mul_comm _ _
  intro t
  have hp := EntranceCover.iidHitCost_le_of_projection advance next (prepared s d) target
    Prod.snd (fun _ _ => rfl) (fun _ h => h) t start
  have hgood : good start := .inr ⟨⟨hm,hc,hF,hS,hT⟩,hq,h⟩
  have hb : B start ≤ 2*d+1-q := by dsimp [B]; split <;> simp [start,prepBudget]
  exact Nat.le_trans hp (Nat.le_trans (hbound t start hgood)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)))

#print axioms expected_ready_after_front


/-- In dirty preparation, follow the *first nonzero* source signal
back to zero, not necessarily a one. Offset d+1 is a virtual one supplied
by the actual living terminal; it requires no field assumption at the target. -/
structure DirtyReturn {p c n : Nat} (x : Config p c n) (s : Fin n) (d q : Nat) : Prop where
  le : q ≤ d+1
  empty : ∀ j, j ≤ d → (x (liftedSite s j)).bullet = .none
  positive : q ≤ d → (x (liftedSite s q)).signal ≠ .zero
  before : ∀ j, j < q → (x (liftedSite s j)).signal = .zero

private theorem max_nonzero {u : Signal} (v : Signal) (h : u ≠ .zero) :
    Signal.max u v ≠ .zero := by cases u <;> cases v <;> simp_all [Signal.max]

private theorem zero_max (u : Signal) : Signal.max .zero u = u := by cases u <;> rfl

/-- Empty dirty sector: the nearest positive colour crosses exactly its
preceding edge, even when it is an inherited two. Non-nominated marks
allow arbitrary updates past that witness. At q=0 the source is ready. -/
theorem dirtyReturn_step {p c n d q : Nat} (x : Config p c n) (s e : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d) (_hD : d+1<n)
    (hL : (x s).leader = true) (hT : (x (liftedSite s (d+1))).leader = true)
    (h : DirtyReturn x s d (q+1)) (he : event x e = false) :
    DirtyReturn (step x e) s d (if e = liftedSite s q then q else q+1) := by
  have hqd : q ≤ d := by have := h.le; omega
  let r := if e = liftedSite s q then q else q+1
  have hr : r ≤ d+1 := by dsimp [r]; split <;> omega
  have snap := empty_sector_snapshot x s e hm hc hF hL hT h.empty (h.before 0 (by omega)) he
  refine ⟨hr,fun j hj => (snap j hj).1, ?_,?_⟩
  · intro hj
    change r ≤ d at hj
    change (step x e (liftedSite s r)).signal ≠ .zero
    rw [(snap r hj).2]
    by_cases hh : e = liftedSite s q
    · rw [if_pos (by simp [r,hh] : liftedSite s r = e)]
      simp only [r,if_pos hh,h.before q (by omega),zero_max]
      by_cases hEq : q = d
      · simp [hEq]
      · simpa [hEq] using h.positive (by omega : q+1 ≤ d)
    · simp only [r,if_neg hh]
      have h' : q+1 ≤ d := by simpa [r,hh] using hj
      split
      · exact max_nonzero _ (h.positive h')
      · exact h.positive h'
  · intro j hj
    change j < r at hj
    have hjD : j ≤ d := by omega
    rw [(snap j hjD).2]
    have hjQ : j < q+1 := by dsimp [r] at hj; split at hj <;> omega
    rw [h.before j hjQ]
    split
    · rename_i hh
      have hjq : j < q := by
        by_cases heq : e = liftedSite s q
        · simpa [r,heq] using hj
        · have hne : j ≠ q := by
            intro H
            subst j
            exact heq hh.symm
          omega
      have hjd : j ≠ d := by omega
      simp [hjd,h.before (j+1) (by omega),Signal.max]
    · rfl

theorem dirtyReturn_exists {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (h : ∀ j, j ≤ d → (x (liftedSite s j)).bullet = .none) :
    ∃ q, DirtyReturn x s d q := by
  classical
  have H (t k : Nat) (hk : k+t = d+1) :
      (∀ j, j < k → (x (liftedSite s j)).signal = .zero) → ∃ q, DirtyReturn x s d q := by
    induction t generalizing k with
    | zero =>
      intro hb
      exact ⟨k,by omega,h,fun hh => (by omega : False).elim,hb⟩
    | succ t ih =>
      intro hb
      by_cases hp : (x (liftedSite s k)).signal = .zero
      · apply ih (k+1) (by omega)
        intro j hj
        by_cases hEq : j = k
        · simpa [hEq] using hp
        · exact hb j (by omega)
      · exact ⟨k,by omega,h,fun _ => hp,hb⟩
  exact H (d+1) 0 (by omega) (by intro j hj; omega)

#print axioms dirtyReturn_step
#print axioms dirtyReturn_exists
end L4.TriplePrep
