import Leader.L4.WindowLocal

/-! Native sector rows localized from TriplePrep. Only actual endpoint
kill exclusions are used; exterior rank reductions are permitted. -/
namespace L4.WindowLocalNative

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

open WindowLocal

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
    (hl : (x (rightNeighbor e)).leader = true) (he : nativeDeath x e = false) :
    (fireInitiator (x e)).bullet ≠ .live ∨
    (fireResponder (x (rightNeighbor e))).shield = true := by
  by_cases hf : (fireInitiator (x e)).bullet = .live
  · right
    cases hs : (fireResponder (x (rightNeighbor e))).shield
    · have hk := (nativeDeath_iff x e).mpr ⟨hl,hf,hs⟩
      simp [he] at hk
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
    (h : ZeroFront x s q) (he : rightNeighbor e = s → nativeDeath x e = false) (hw : e ≠ liftedSite s q) :
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
          have hS := terminal_safe x e hl (he (by simpa only [liftedSite_zero] using hR.symm))
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

private theorem ordinary_front_step {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue)
    (hl : v.leader = false) (hN : u.signal = .zero) (hF : u.bullet ≠ .none) :
    (pairStep u v).1.bullet = .none ∧
    (pairStep u v).2.bullet = (if v.bullet == .none then u.bullet else v.bullet) ∧
    (pairStep u v).1.signal = .zero ∧ (pairStep u v).2.signal = .zero := by
  have hf : fireInitiator u = u := by simp [fireInitiator,hN]
  have q := ordinary_native_payload u v hm hr hl
  simp [native,hf,fireResponder,hl,impact,pinned,hm,followerBullet,hF,hN,Signal.max] at q
  exact ⟨q.1,by simpa using q.2.2.2.1,q.2.1,q.2.2.2.2.1⟩

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
    (hs : nativeDeath x (liftedSite s d) = false) :
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
    (he : rightNeighbor e = s → nativeDeath x e = false) (j : Nat) (hj : j ≤ d) :
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
        have hS := terminal_safe x e hl (he (by simpa only [liftedSite_zero] using hR.symm))
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
    (h : ReturnFront x s d (q+1)) (he : rightNeighbor e = s → nativeDeath x e = false) (j : Nat) (hj : j ≤ d) :
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
    (h : ReturnFront x s d (q+1)) (he : rightNeighbor e = s → nativeDeath x e = false) :
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

/-- A ready source met on its incoming mark starts a zero-signal clearing
front immediately, or there is an actual global event on this mark. -/
theorem sourceIncoming_starts_front {p c n : Nat} (hn : 4 ≤ n) (x : Config p c n)
    (e s : Fin n) (hR : rightNeighbor e = s) (hL : (x s).leader = true)
    (hS : (x s).signal ≠ .zero) (he : nativeDeath x e = false) :
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
    (hS : (x s).signal ≠ .zero) (he : nativeDeath x s = false) :
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

/-- In dirty preparation, follow the first nonzero source signal
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
    (h : DirtyReturn x s d (q+1)) (he : rightNeighbor e = s → nativeDeath x e = false) :
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

open SevenTagCharge in
/-- Native phase refinement on one actual retained sector. The monitored
window can continue past an unrelated kill or retirement, even while
the preparation front or return is active. -/
theorem scoped_sweep_or_return_step {p c n : Nat}
    (hn : 4 ≤ n) (x : Config p c n) (z : Ledger p c n)
    (group cert : List (Fin n)) (target : Option (Fin n)) (e l r s t : Fin n)
    (d : Nat) (hD : d+1<n)
    (hValid : Valid z x) (hSubset : cert ⊆ group) (hL : l ∈ cert) (hR : r ∈ cert)
    (hSector : CertifiedSector z l r s t d)
    (hKeep : route group cert target z e = Event.keep) :
    let u := rightNeighbor s
    let y := (SevenTagCharge.advance z e).config
    CertifiedSector (SevenTagCharge.advance z e) l r s t d ∧
    (∀ q, q ≤ d → ZeroFront z.config u q →
      if e = liftedSite u q then
        if q < d then ZeroFront y u (q+1) else ReturnFront y u d d
      else ZeroFront y u q) ∧
    (∀ q, ReturnFront z.config u d (q+1) →
      ReturnFront y u d (if e = liftedSite u q then q else q+1)) ∧
    (∀ q, DirtyReturn z.config u d (q+1) →
      DirtyReturn y u d (if e = liftedSite u q then q else q+1)) := by
  let u := rightNeighbor s
  have noS : rightNeighbor e = u → nativeDeath z.config e = false :=
    certified_no_death_on_keep hn x z group cert target e s l
      hValid hSubset hL hSector.left_live hKeep
  have noT : rightNeighbor e = liftedSite u (d+1) → nativeDeath z.config e = false := by
    rw [hSector.terminal_site]
    exact certified_no_death_on_keep hn x z group cert target e t r
      hValid hSubset hR hSector.right_live hKeep
  have liveS : (z.config u).leader = true := hSector.left_live.2
  have liveT : (z.config (liftedSite u (d+1))).leader = true := by
    rw [hSector.terminal_site]
    exact hSector.right_live.2
  refine ⟨certifiedSector_keep hn x z group cert target e l r s t d hValid hSubset hL hR hSector hKeep,?_,?_,?_⟩
  · intro q hq hFront
    by_cases hE : e = liftedSite u q
    · rw [if_pos hE]
      subst e
      by_cases hQ : q < d
      · rw [if_pos hQ]
        exact zeroFront_progress hn z.config u hValid.markCover hValid.sourceCover hSector.gap hD hQ hFront
      · rw [if_neg hQ]
        have hqD : q = d := by omega
        subst q
        have hK := noT (liftedSite_succ u d).symm
        exact (zeroFront_terminal z.config u hD hFront liveT hK).front
    · rw [if_neg hE]
      exact zeroFront_wait hn z.config u e hValid.markCover hValid.sourceCover hSector.gap hD
        liveS hq hFront noS hE
  · intro q hs
    exact returnFront_step z.config u e hValid.markCover hValid.sourceCover hSector.gap hD liveS liveT hs noS
  · intro q hs
    exact dirtyReturn_step z.config u e hValid.markCover hValid.sourceCover hSector.gap hD liveS liveT hs noS

structure LeastBullet {p c n : Nat} (x : Config p c n) (s : Fin n) (q : Nat) : Prop where
  occupied : (x (liftedSite s q)).bullet ≠ .none
  before : ∀ j, j < q → (x (liftedSite s j)).bullet = .none

private theorem ordinary_bullet_transport {p c : Nat} (u v : Site p c)
    (hm : u.mark = false) (hr : v.residue = nextResidue u.residue) (hl : v.leader = false)
    (hNoFire : u.leader = false ∨ u.signal = .zero) (hB : u.bullet ≠ .none) :
    (pairStep u v).1.bullet = .none ∧ (pairStep u v).2.bullet ≠ .none := by
  have hf : fireInitiator u = u := by rcases hNoFire with h | h <;> simp [fireInitiator,h]
  have q := ordinary_native_payload u v hm hr hl
  simp [native,hf,fireResponder,hl,impact,pinned,hm,followerBullet,hB] at q
  refine ⟨q.1,?_⟩
  rw [q.2.2.2.1]
  split
  · exact hB
  · assumption

/-- Dirty leftmost-front phase, on its nominated forward mark. A
follower's own inherited two is allowed; only at the source does this
use the nonreadiness assumption to forbid a replacement N0 firing. -/
theorem leastBullet_progress {p c n d q : Nat} (hn : 4 ≤ n)
    (x : Config p c n) (s : Fin n) (hm : MCOV x) (hc : COV x)
    (hF : FirstMark x s d) (hD : d+1<n) (hQ : q<d)
    (h0 : (x s).signal = .zero) (h : LeastBullet x s q) :
    LeastBullet (step x (liftedSite s q)) s (q+1) := by
  let e := liftedSite s q
  have ho := sector_ordinary x s hm hc hF hQ
  have hN : (x e).leader = false ∨ (x e).signal = .zero := by
    cases q with
    | zero => exact .inr (by simpa [e,liftedSite_zero] using h0)
    | succ q =>
      have hg := sector_ordinary x s hm hc hF (show q<d by omega)
      exact .inl (by simpa [e,liftedSite_succ] using hg.2.2)
  have hp := ordinary_bullet_transport _ _ ho.1 ho.2.1 ho.2.2 hN h.occupied
  have hR : liftedSite s (q+1) = rightNeighbor e := liftedSite_succ s q
  have hn' := separate_neighbor hn e
  refine ⟨?_,?_⟩
  · have hPost : step x e (liftedSite s (q+1)) = (pairStep (x e) (x (rightNeighbor e))).2 := by
      simp [step,hR,hn']
    rw [hPost]
    exact hp.2
  · intro j hj
    by_cases he : j=q
    · subst j
      simpa [step,e] using hp.1
    · have hx : liftedSite s j ≠ e := fun H => he (liftedSite_inj s (by omega) (by omega) H)
      have hy : liftedSite s j ≠ rightNeighbor e := by
        rw [← hR]
        intro H
        have hEq := liftedSite_inj s (by omega : j<n) (by omega : q+1<n) H
        omega
      change (step x e (liftedSite s j)).bullet = .none
      simpa only [step,if_neg hx,if_neg hy] using h.before j (by omega)

/-- On all nonnominated marks the least bullet keeps its offset and no
new bullet gets into the vacated left prefix. The source can become
ready on this mark; until then the same least bullet remains usable. -/
theorem leastBullet_wait {p c n d q : Nat} (x : Config p c n) (s e : Fin n)
    (hm : MCOV x) (hc : COV x) (hF : FirstMark x s d)
    (hL : (x s).leader = true) (h0 : (x s).signal = .zero) (hq : q≤d)
    (h : LeastBullet x s q) (he : rightNeighbor e = s → nativeDeath x e = false)
    (hw : e ≠ liftedSite s q) : LeastBullet (step x e) s q := by
  have noFire (j : Nat) (hj : j≤q) :
      (x (liftedSite s j)).leader = false ∨ (x (liftedSite s j)).signal = .zero := by
    cases j with
    | zero => exact .inr (by simpa [liftedSite_zero] using h0)
    | succ j =>
      exact .inl (by simpa [liftedSite_succ] using
        (sector_ordinary x s hm hc hF (show j<d by omega)).2.2)
  have prop (j : Nat) (hj : j≤q) :
      (step x e (liftedSite s j)).bullet = (x (liftedSite s j)).bullet := by
    by_cases hE : liftedSite s j = e
    · have hjq : j<q := by
        by_cases H : j=q
        · subst j; exact (hw hE.symm).elim
        · omega
      have ho := sector_ordinary x s hm hc hF (show j<d by omega)
      have hh := ordinary_empty_donor _ _ ho.1 ho.2.1 ho.2.2 (h.before j hjq) (noFire j hj)
      rw [← hE]
      simpa [step] using hh.1.trans (h.before j hjq).symm
    · by_cases hR : liftedSite s j = rightNeighbor e
      · cases j with
        | zero =>
          have hr : rightNeighbor e = s := by simpa [liftedSite_zero] using hR.symm
          have hl : (x (rightNeighbor e)).leader = true := hr ▸ hL
          have hz : (x (rightNeighbor e)).signal = .zero := hr ▸ h0
          have hS := terminal_safe x e hl (he hr)
          rw [show fireResponder (x (rightNeighbor e)) = x (rightNeighbor e) by simp [fireResponder,hl,hz]] at hS
          have hh := zero_incoming_stable _ _ hl hz hS
          simpa only [step,if_neg hE,if_pos hR] using hh.1.trans
            (congrArg (fun i => (x i).bullet) hR.symm)
        | succ j =>
          have hE' : liftedSite s j = e := FreshSeparation.succ_inj (by simpa [liftedSite_succ] using hR)
          have hO := sector_ordinary x s hm hc hF (show j < d by omega)
          have hh := ordinary_empty_donor _ _ hO.1 hO.2.1 hO.2.2
            (h.before j (by omega)) (noFire j (by omega))
          simp only [step,if_neg hE,if_pos hR]
          rw [← hE',← liftedSite_succ]
          simpa only [liftedSite_succ] using hh.2.2.1
      · simp only [step,if_neg hE,if_neg hR]
  exact ⟨fun hb => h.occupied ((prop q (Nat.le_refl _)).symm.trans hb),
    fun j hj => (prop j (by omega)).trans (h.before j hj)⟩

/-- Last nominated forward mark empties a dirty sector. The donor may
hold inherited colour two; this statement does not mistakenly assert
that the resulting first return is necessarily binary. -/
theorem leastBullet_terminal {p c n d : Nat} (x : Config p c n) (s : Fin n)
    (hD : d+1<n) (h : LeastBullet x s d)
    (hL : (x (liftedSite s (d+1))).leader = true)
    (hn : nativeDeath x (liftedSite s d) = false) :
    ∀ j, j≤d → (step x (liftedSite s d) (liftedSite s j)).bullet = .none := by
  let e := liftedSite s d
  have hR : liftedSite s (d+1) = rightNeighbor e := liftedSite_succ s d
  have hl : (x (rightNeighbor e)).leader = true := hR ▸ hL
  have hp := surviving_terminal _ _ hl (terminal_safe x e hl hn)
  intro j hj
  by_cases he : j=d
  · subst j
    simpa [step,e] using hp.1
  · have hx : liftedSite s j ≠ e := fun H => he (liftedSite_inj s (by omega) (by omega) H)
    have hy : liftedSite s j ≠ rightNeighbor e := by
      rw [← hR]
      intro H
      have hEq := liftedSite_inj s (by omega : j<n) hD H
      omega
    change (step x e (liftedSite s j)).bullet = .none
    simpa only [step,if_neg hx,if_neg hy] using h.before j (by omega)

end L4.WindowLocalNative
