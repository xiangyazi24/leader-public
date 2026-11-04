import Leader.L3.Sealed

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

set_option autoImplicit false
set_option Elab.async false

/-!
A source-relative observation is used only to prove facts about
nativeE. Its correspondence with the actual selected OLD pair is
proved below. There is no modified physical protocol or scheduler.

Ready launches start new excursions and are deliberately not charged
to the old Ready quota. Every non-Ready step is nonincreasing; a hit
on its nominated edge decreases the quota by at least one, including
when that step reaches Ready. Endpoint deletions stop the assertion.
-/

namespace SealedCloseProof

inductive Stage where
  | ready
  | bullet (live : Bool) (position : Nat)
  | returning (position : Nat)
  deriving DecidableEq

structure Word where
  bullet : Nat → Fin 3
  signal : Nat → Bool
  shield : Bool

def kind (live : Bool) : Fin 3 := if live then 2 else 1

private theorem kind_ne_zero (live : Bool) : kind live ≠ 0 := by
  cases live <;> decide +kernel

def fromPhase {n : Nat} : SealedPhase n → Stage
  | .ready => .ready
  | .dummy p => .bullet false p.val
  | .live p => .bullet true p.val
  | .returning q => .returning q.val

def rank (d : Nat) : Stage → Nat
  | .ready => 0
  | .bullet _ p => 2 * d - p - 1
  | .returning q => q

def nominated : Stage → Nat
  | .ready => 0
  | .bullet _ p => p
  | .returning q => q - 1

def Holds (d : Nat) (w : Word) : Stage → Prop
  | .ready =>
      w.signal 0 = true ∧ ∀ k, k < d → w.bullet k = 0
  | .bullet live p =>
      p < d ∧
      (∀ k, k < d → w.bullet k = if k = p then kind live else 0) ∧
      w.shield = live ∧
      ∀ k, k ≤ p → w.signal k = false
  | .returning q =>
      0 < q ∧ q < d ∧
      (∀ k, k < d → w.bullet k = 0) ∧
      w.signal 0 = false ∧ w.signal q = true ∧
      ∀ k, 0 < k → k < q → w.signal k = false

def word (X : Nat → CertNative) : Word :=
  { bullet := fun k => (X k).b
    signal := fun k => (X k).sg
    shield := (X 0).sh }

def cells {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) : Nat → CertNative :=
  fun k => N (sealedSite ring a k)

def view {n : Nat} (ring : DirectedRing n)
    (N : Fin n → CertNative) (a : Fin n) : Word :=
  word (cells ring N a)

def Agree (d : Nat) (u v : Word) : Prop :=
  u.shield = v.shield ∧
    ∀ k, k < d →
      u.bullet k = v.bullet k ∧ u.signal k = v.signal k

private theorem agree_trans {d : Nat} {u v w : Word}
    (h : Agree d u v) (g : Agree d v w) : Agree d u w := by
  refine ⟨h.1.trans g.1, ?_⟩
  intro k hk
  exact ⟨(h.2 k hk).1.trans (g.2 k hk).1,
    (h.2 k hk).2.trans (g.2 k hk).2⟩

private theorem agree_of_cells {d : Nat}
    (hd : 0 < d) (X Y : Nat → CertNative)
    (h : ∀ k, k < d → X k = Y k) :
    Agree d (word X) (word Y) := by
  refine ⟨congrArg CertNative.sh (h 0 hd), ?_⟩
  intro k hk
  exact ⟨congrArg CertNative.b (h k hk),
    congrArg CertNative.sg (h k hk)⟩

private theorem holds_of_agree {d : Nat} {u v : Word}
    (hd : 0 < d) (h : Agree d u v) (s : Stage)
    (hv : Holds d v s) : Holds d u s := by
  cases s with
  | ready =>
      refine ⟨(h.2 0 hd).2.trans hv.1, ?_⟩
      intro k hk
      exact (h.2 k hk).1.trans (hv.2 k hk)
  | bullet live p =>
      rcases hv with ⟨hp, hb, hh, hs⟩
      refine ⟨hp, ?_, h.1.trans hh, ?_⟩
      · intro k hk
        exact (h.2 k hk).1.trans (hb k hk)
      · intro k hk
        exact (h.2 k (by omega)).2.trans (hs k hk)
  | returning q =>
      rcases hv with ⟨hq, hqd, hb, hz, hs, hbefore⟩
      refine ⟨hq, hqd, ?_, (h.2 0 hd).2.trans hz,
        (h.2 q hqd).2.trans hs, ?_⟩
      · intro k hk
        exact (h.2 k hk).1.trans (hb k hk)
      · intro k hk hlt
        exact (h.2 k (by omega)).2.trans (hbefore k hk hlt)

private theorem no_bullet_iff {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hdn : d < n) :
    (∀ k, k < d → (view ring N a).bullet k = 0) ↔
      SealedNoBullet ring N a d := by
  constructor
  · intro h k hk
    exact h k.val hk
  · intro h k hk
    exact h ⟨k, Nat.lt_trans hk hdn⟩ hk

private theorem unique_bullet_iff {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hdn : d < n)
    (p : Fin n) (v : Fin 3) :
    (p.val < d ∧ ∀ k, k < d →
      (view ring N a).bullet k = if k = p.val then v else 0) ↔
      SealedUniqueBullet ring N a d p v := by
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨hp, ?_, ?_⟩
    · have hself :
          (sealedAt ring N a p).b =
            if p.val = p.val then v else 0 :=
        hb p.val hp
      rw [if_pos rfl] at hself
      exact hself
    · intro k hk hkp
      have hne : k.val ≠ p.val := by
        intro he
        exact hkp (Fin.ext he)
      have hcell :
          (sealedAt ring N a k).b =
            if k.val = p.val then v else 0 :=
        hb k.val hk
      rw [if_neg hne] at hcell
      exact hcell
  · rintro ⟨hp, hb, hother⟩
    refine ⟨hp, ?_⟩
    intro k hk
    by_cases he : k = p.val
    · subst k
      change (sealedAt ring N a p).b =
        if p.val = p.val then v else 0
      rw [if_pos rfl]
      exact hb
    · have hi : (⟨k, Nat.lt_trans hk hdn⟩ : Fin n) ≠ p := by
        intro h
        exact he (congrArg Fin.val h)
      change (sealedAt ring N a ⟨k, Nat.lt_trans hk hdn⟩).b =
        if k = p.val then v else 0
      rw [if_neg he]
      exact hother ⟨k, Nat.lt_trans hk hdn⟩ hk hi

private theorem zero_trail_iff {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (p : Fin n) :
    (∀ k, k ≤ p.val → (view ring N a).signal k = false) ↔
      SealedZeroTrail ring N a p := by
  constructor
  · intro h k hk
    exact h k.val hk
  · intro h k hk
    have hkn : k < n := Nat.lt_of_le_of_lt hk p.isLt
    exact h ⟨k, hkn⟩ hk

private theorem phase_view {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hdn : d < n)
    (phase : SealedPhase n) :
    Holds d (view ring N a) (fromPhase phase) ↔
      SealedPhaseHolds ring N a d phase := by
  cases phase with
  | ready =>
      constructor
      · intro h
        exact ⟨h.1, (no_bullet_iff ring N a d hdn).1 h.2⟩
      · intro h
        exact ⟨h.1, (no_bullet_iff ring N a d hdn).2 h.2⟩
  | dummy p =>
      constructor
      · rintro ⟨hp, hb, hh, hs⟩
        exact ⟨(unique_bullet_iff ring N a d hdn p 1).1 ⟨hp, hb⟩,
          hh, (zero_trail_iff ring N a p).1 hs⟩
      · rintro ⟨hb, hh, hs⟩
        have hu := (unique_bullet_iff ring N a d hdn p 1).2 hb
        exact ⟨hu.1, hu.2, hh, (zero_trail_iff ring N a p).2 hs⟩
  | live p =>
      constructor
      · rintro ⟨hp, hb, hh, hs⟩
        exact ⟨(unique_bullet_iff ring N a d hdn p 2).1 ⟨hp, hb⟩,
          hh, (zero_trail_iff ring N a p).1 hs⟩
      · rintro ⟨hb, hh, hs⟩
        have hu := (unique_bullet_iff ring N a d hdn p 2).2 hb
        exact ⟨hu.1, hu.2, hh, (zero_trail_iff ring N a p).2 hs⟩
  | returning q =>
      constructor
      · rintro ⟨hq, hqd, hb, hz, hs, hbefore⟩
        refine ⟨(no_bullet_iff ring N a d hdn).1 hb, hz,
          by omega, hqd, hs, ?_⟩
        intro k hk hlt
        exact hbefore k.val hk hlt
      · rintro ⟨hb, hz, hq, hqd, hs, hbefore⟩
        refine ⟨by omega, hqd, (no_bullet_iff ring N a d hdn).2 hb,
          hz, hs, ?_⟩
        intro k hk hlt
        exact hbefore ⟨k, Nat.lt_trans hlt q.isLt⟩ hk hlt

private theorem realize {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (hdn : d < n)
    (s : Stage) (hs : Holds d (view ring N a) s) :
    ∃ phase : SealedPhase n,
      SealedPhaseHolds ring N a d phase ∧ fromPhase phase = s := by
  cases s with
  | ready =>
      exact ⟨.ready, (phase_view ring N a d hdn .ready).1 hs, rfl⟩
  | bullet live p =>
      let fp : Fin n := ⟨p, Nat.lt_trans hs.1 hdn⟩
      cases live with
      | false =>
          exact ⟨.dummy fp,
            (phase_view ring N a d hdn (.dummy fp)).1 hs, rfl⟩
      | true =>
          exact ⟨.live fp,
            (phase_view ring N a d hdn (.live fp)).1 hs, rfl⟩
  | returning q =>
      let fq : Fin n := ⟨q, Nat.lt_trans hs.2.1 hdn⟩
      exact ⟨.returning fq,
        (phase_view ring N a d hdn (.returning fq)).1 hs, rfl⟩

private theorem phase_rank {n : Nat} (d : Nat) (p : SealedPhase n) :
    rank d (fromPhase p) = SealedPhaseProgress d p := by
  cases p <;> rfl

private theorem phase_edge {n : Nat}
    (ring : DirectedRing n) (a : Fin n) (p : SealedPhase n) :
    sealedSite ring a (nominated (fromPhase p)) =
      SealedPhaseEdge ring a p := by
  cases p with
  | ready => exact sealedSite_zero ring a
  | dummy p => rfl
  | live p => rfl
  | returning q => rfl

private theorem phase_nonready {n : Nat} (p : SealedPhase n)
    (h : p ≠ .ready) : fromPhase p ≠ .ready := by
  cases p with
  | ready => exact False.elim (h rfl)
  | dummy p => intro he; cases he
  | live p => intro he; cases he
  | returning q => intro he; cases he

private theorem nominated_lt {d : Nat} {w : Word} {s : Stage}
    (hd : 0 < d) (hs : Holds d w s) : nominated s < d := by
  cases s with
  | ready => exact hd
  | bullet live p => exact hs.1
  | returning q =>
      have hq := hs.1
      have hqd := hs.2.1
      change q - 1 < d
      omega

/-! Pure finite-sector observation updates. Their literal native-row
correspondence is proved later; they are not assumed transitions. -/

def quiet (d r : Nat) (w : Word) : Word :=
  { w with signal := fun k =>
      if k = r then
        w.signal r || (if r + 1 = d then true else w.signal (r + 1))
      else w.signal k }

def advance (r : Nat) (v : Fin 3) (w : Word) : Word :=
  { w with
    bullet := fun k =>
      if k = r then 0 else if k = r + 1 then v else w.bullet k
    signal := fun k =>
      if k = r ∨ k = r + 1 then false else w.signal k }

def absorb (r : Nat) (w : Word) : Word :=
  { w with
    bullet := fun k => if k = r then 0 else w.bullet k
    signal := fun k => if k = r then true else w.signal k }

def incomingStage : Stage → Stage
  | .ready => .bullet false 0
  | s => s

def incomingWord (s : Stage) (w : Word) : Word :=
  match s with
  | .ready =>
      { bullet := fun k => if k = 0 then 1 else w.bullet k
        signal := fun k => if k = 0 then false else w.signal k
        shield := false }
  | _ => w

def insideStage (d : Nat) (s : Stage) (r : Nat) : Stage :=
  match s with
  | .ready =>
      if r = 0 then
        if d = 1 then .ready else .bullet true 1
      else .ready
  | .bullet live p =>
      if r = p then
        if p + 1 = d then
          if p = 0 then .ready else .returning p
        else .bullet live (p + 1)
      else .bullet live p
  | .returning q =>
      if r + 1 = q then
        if r = 0 then .ready else .returning r
      else .returning q

def insideWord (d : Nat) (s : Stage) (r : Nat) (w : Word) : Word :=
  match s with
  | .ready =>
      if r = 0 then
        if d = 1 then absorb 0 { w with shield := true }
        else advance 0 2 { w with shield := true }
      else quiet d r w
  | .bullet live p =>
      if r = p then
        if p + 1 = d then absorb p w
        else advance p (kind live) w
      else quiet d r w
  | .returning _ => quiet d r w

private theorem quiet_ready (d r : Nat) (w : Word)
    (hr : r ≠ 0) (h : Holds d w .ready) :
    Holds d (quiet d r w) .ready := by
  refine ⟨?_, h.2⟩
  have hne : 0 ≠ r := Ne.symm hr
  simpa only [quiet, if_neg hne] using h.1

private theorem quiet_bullet (d r p : Nat) (live : Bool) (w : Word)
    (hrp : r ≠ p) (h : Holds d w (.bullet live p)) :
    Holds d (quiet d r w) (.bullet live p) := by
  rcases h with ⟨hp, hb, hh, hs⟩
  refine ⟨hp, hb, hh, ?_⟩
  intro k hk
  by_cases he : k = r
  · subst k
    have hn : r + 1 ≠ d := by omega
    have hz := hs r (by omega)
    have hznext := hs (r + 1) (by omega)
    change
      (if r = r then
        w.signal r || (if r + 1 = d then true else w.signal (r + 1))
       else w.signal r) = false
    rw [if_pos rfl, if_neg hn, hz, hznext]
    rfl
  · simpa only [quiet, if_neg he] using hs k hk

private theorem advance_bullet (d p : Nat) (live : Bool) (w : Word)
    (hpnext : p + 1 < d) (h : Holds d w (.bullet live p)) :
    Holds d (advance p (kind live) w) (.bullet live (p + 1)) := by
  rcases h with ⟨hp, hb, hh, hs⟩
  refine ⟨hpnext, ?_, hh, ?_⟩
  · intro k hk
    by_cases he : k = p
    · subst k
      have hn : p ≠ p + 1 := by omega
      change
        (if p = p then (0 : Fin 3)
         else if p = p + 1 then kind live else w.bullet p) =
          if p = p + 1 then kind live else 0
      rw [if_pos rfl, if_neg hn]
    · by_cases hn : k = p + 1
      · simp only [advance, if_neg he, if_pos hn]
      · simpa only [advance, if_neg he, if_neg hn] using hb k hk
  · intro k hk
    by_cases he : k = p ∨ k = p + 1
    · simp only [advance, if_pos he]
    · have hkp : k ≤ p := by omega
      simpa only [advance, if_neg he] using hs k hkp

private theorem absorbed_empty (d p : Nat) (live : Bool) (w : Word)
    (h : Holds d w (.bullet live p)) :
    ∀ k, k < d → (absorb p w).bullet k = 0 := by
  intro k hk
  by_cases he : k = p
  · simp only [absorb, if_pos he]
  · simpa only [absorb, if_neg he] using h.2.1 k hk

private theorem absorb_bullet_ready (d : Nat) (live : Bool) (w : Word)
    (h : Holds d w (.bullet live 0)) :
    Holds d (absorb 0 w) .ready := by
  exact ⟨rfl, absorbed_empty d 0 live w h⟩

private theorem absorb_bullet_return (d p : Nat) (live : Bool) (w : Word)
    (hp : 0 < p) (h : Holds d w (.bullet live p)) :
    Holds d (absorb p w) (.returning p) := by
  refine ⟨hp, h.1, absorbed_empty d p live w h, ?_, ?_, ?_⟩
  · have hn : 0 ≠ p := by omega
    simpa only [absorb, if_neg hn] using h.2.2.2 0 (Nat.zero_le p)
  · change (if p = p then true else w.signal p) = true
    rw [if_pos rfl]
  · intro k hk hkp
    have hn : k ≠ p := by omega
    simpa only [absorb, if_neg hn] using h.2.2.2 k (by omega)

private theorem absorb_ready (d : Nat) (w : Word)
    (h : Holds d w .ready) : Holds d (absorb 0 w) .ready := by
  refine ⟨rfl, ?_⟩
  intro k hk
  by_cases he : k = 0
  · simp only [absorb, if_pos he]
  · simpa only [absorb, if_neg he] using h.2 k hk

private theorem launch_ready (d : Nat) (w : Word)
    (hd : 1 < d) (h : Holds d w .ready) :
    Holds d (advance 0 2 { w with shield := true }) (.bullet true 1) := by
  refine ⟨hd, ?_, rfl, ?_⟩
  · intro k hk
    by_cases hz : k = 0
    · subst k
      simp [advance, kind]
    · by_cases ho : k = 1
      · simp [advance, kind, hz, ho]
      · simpa only [advance, if_neg hz, if_neg ho] using h.2 k hk
  · intro k hk
    have he : k = 0 ∨ k = 1 := by omega
    simpa only [advance, Nat.zero_add, if_pos he]

private theorem quiet_return (d r q : Nat) (w : Word)
    (h : Holds d w (.returning q)) :
    Holds d (quiet d r w)
      (if r + 1 = q then
        if r = 0 then .ready else .returning r
       else .returning q) := by
  rcases h with ⟨hq, hqd, hb, hz, hsig, hbefore⟩
  by_cases hhit : r + 1 = q
  · rw [if_pos hhit]
    have hterminal : r + 1 ≠ d := by omega
    by_cases hrzero : r = 0
    · rw [if_pos hrzero]
      subst r
      refine ⟨?_, hb⟩
      have hsone : w.signal 1 = true := by
        have he : q = 1 := by omega
        simpa only [he] using hsig
      change
        (if (0 : Nat) = 0 then
          w.signal 0 || (if 0 + 1 = d then true else w.signal (0 + 1))
         else w.signal 0) = true
      rw [if_pos rfl, if_neg hterminal, hz, hsone]
      rfl
    · rw [if_neg hrzero]
      refine ⟨by omega, by omega, hb, ?_, ?_, ?_⟩
      · have hn : 0 ≠ r := by omega
        simpa only [quiet, if_neg hn] using hz
      · have hsnext : w.signal (r + 1) = true := by
          rw [hhit]
          exact hsig
        change
          (if r = r then
            w.signal r ||
              (if r + 1 = d then true else w.signal (r + 1))
           else w.signal r) = true
        rw [if_pos rfl, if_neg hterminal, hsnext, Bool.or_true]
      · intro k hk hkr
        have hne : k ≠ r := by omega
        simpa only [quiet, if_neg hne] using
          hbefore k hk (by omega)
  · rw [if_neg hhit]
    refine ⟨hq, hqd, hb, ?_, ?_, ?_⟩
    · by_cases hrzero : r = 0
      · subst r
        have hqbig : 1 < q := by omega
        have hterminal : (0 : Nat) + 1 ≠ d := by omega
        have hsone := hbefore 1 (by decide +kernel) hqbig
        change
          (if (0 : Nat) = 0 then
            w.signal 0 ||
              (if 0 + 1 = d then true else w.signal (0 + 1))
           else w.signal 0) = false
        rw [if_pos rfl, if_neg hterminal, hz, hsone]
        rfl
      · have hn : 0 ≠ r := by omega
        simpa only [quiet, if_neg hn] using hz
    · by_cases hqr : q = r
      · subst r
        change
          (if q = q then
            w.signal q ||
              (if q + 1 = d then true else w.signal (q + 1))
           else w.signal q) = true
        rw [if_pos rfl, hsig]
        rfl
      · simpa only [quiet, if_neg hqr] using hsig
    · intro k hk hkq
      by_cases he : k = r
      · subst k
        have hnext : r + 1 < q := by omega
        have hterminal : r + 1 ≠ d := by omega
        have hsleft := hbefore r hk hkq
        have hsright := hbefore (r + 1) (by omega) hnext
        change
          (if r = r then
            w.signal r ||
              (if r + 1 = d then true else w.signal (r + 1))
           else w.signal r) = false
        rw [if_pos rfl, if_neg hterminal, hsleft, hsright]
        rfl
      · simpa only [quiet, if_neg he] using hbefore k hk hkq

private theorem incoming_preserves (d : Nat) (w : Word) (s : Stage)
    (hd : 0 < d) (h : Holds d w s) :
    Holds d (incomingWord s w) (incomingStage s) := by
  cases s with
  | ready =>
      refine ⟨hd, ?_, rfl, ?_⟩
      · intro k hk
        by_cases he : k = 0
        · simp [incomingWord, kind, he]
        · simpa only [incomingWord, if_neg he] using h.2 k hk
      · intro k hk
        have he : k = 0 := by omega
        simp [incomingWord, he]
  | bullet live p => exact h
  | returning q => exact h

private theorem incoming_same (s : Stage) (h : s ≠ .ready) :
    incomingStage s = s := by
  cases s with
  | ready => exact False.elim (h rfl)
  | bullet live p => rfl
  | returning q => rfl

private theorem inside_preserves (d r : Nat) (w : Word) (s : Stage)
    (hd : 0 < d) (hr : r < d) (h : Holds d w s) :
    Holds d (insideWord d s r w) (insideStage d s r) := by
  cases s with
  | ready =>
      by_cases hrzero : r = 0
      · subst r
        by_cases hdshort : d = 1
        · have hh : Holds d { w with shield := true } .ready :=
            ⟨h.1, h.2⟩
          simpa only [insideWord, insideStage, ite_true,
            if_pos hdshort] using absorb_ready d _ hh
        · simpa only [insideWord, insideStage, ite_true,
            if_neg hdshort] using launch_ready d w (by omega) h
      · simpa only [insideWord, insideStage, if_neg hrzero] using
          quiet_ready d r w hrzero h
  | bullet live p =>
      by_cases hrp : r = p
      · subst r
        by_cases hlast : p + 1 = d
        · by_cases hpzero : p = 0
          · subst p
            simpa only [insideWord, insideStage, ite_true,
              if_pos hlast] using absorb_bullet_ready d live w h
          · simpa only [insideWord, insideStage, ite_true,
              if_pos hlast, if_neg hpzero] using
              absorb_bullet_return d p live w (by omega) h
        · have hnext : p + 1 < d := by have hp := h.1; omega
          simpa only [insideWord, insideStage, ite_true,
            if_neg hlast] using advance_bullet d p live w hnext h
      · simpa only [insideWord, insideStage, if_neg hrp] using
          quiet_bullet d r p live w hrp h
  | returning q =>
      exact quiet_return d r q w h

private theorem inside_progress (d r : Nat) (w : Word) (s : Stage)
    (h : Holds d w s) (hnr : s ≠ .ready) :
    rank d (insideStage d s r) ≤ rank d s ∧
      (r = nominated s → rank d (insideStage d s r) + 1 ≤ rank d s) := by
  cases s with
  | ready => exact False.elim (hnr rfl)
  | bullet live p =>
      have hp : p < d := h.1
      by_cases hrp : r = p
      · have hstrict : rank d (insideStage d (.bullet live p) r) + 1 ≤
            rank d (.bullet live p) := by
          by_cases hlast : p + 1 = d
          · by_cases hpzero : p = 0
            · simp only [insideStage, if_pos hrp, if_pos hlast,
                if_pos hpzero, rank]
              omega
            · simp only [insideStage, if_pos hrp, if_pos hlast,
                if_neg hpzero, rank]
              omega
          · simp only [insideStage, if_pos hrp, if_neg hlast, rank]
            omega
        exact ⟨by omega, fun _ => hstrict⟩
      · simp only [insideStage, if_neg hrp, rank, nominated]
        exact ⟨Nat.le_refl _, fun he => False.elim (hrp he)⟩
  | returning q =>
      have hq : 0 < q := h.1
      by_cases hhit : r + 1 = q
      · have hstrict : rank d (insideStage d (.returning q) r) + 1 ≤ q := by
          by_cases hrzero : r = 0
          · simp only [insideStage, if_pos hhit, if_pos hrzero, rank]
            omega
          · simp only [insideStage, if_pos hhit, if_neg hrzero, rank]
            omega
        exact ⟨by change rank d (insideStage d (.returning q) r) ≤ q; omega,
          fun _ => hstrict⟩
      · simp only [insideStage, if_neg hhit, rank, nominated]
        refine ⟨Nat.le_refl _, ?_⟩
        intro he
        have hbad : r + 1 = q := by omega
        exact False.elim (hhit hbad)

/-! Literal OLD-pair evaluation. The finite leader-row split only
resolves old Boolean flags and the three possible source bullets.
Symbolic native guards are evaluated with if_pos/if_neg; closed
branches reduce definitionally. Final simplification is restricted
to computed output fields. -/

private theorem fin_back (b : Fin 3) : certFinThree b.val = b := by
  unfold certFinThree
  rw [dif_pos b.isLt]

private theorem fin_empty : certFinThree 0 = (0 : Fin 3) := rfl

private theorem fin_one : certFinThree 1 = (1 : Fin 3) := rfl
private theorem fin_dummy : certFinThree 1 = (1 : Fin 3) := rfl
private theorem fin_live : certFinThree 2 = (2 : Fin 3) := rfl

private theorem fin_cases (b : Fin 3) : b = 0 ∨ b = 1 ∨ b = 2 := by
  rcases b with ⟨v, hv⟩
  rcases v with _ | _ | _ | v
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

private theorem row_quiet (x y : CertNative)
    (hf : (x.l && x.sg) = false) (hb : x.b = 0)
    (hy : y.l = false) :
    certLiteralEPair x y =
      ({ x with b := 0, sg := x.sg || y.sg }, y) := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  change xb = 0 at hb
  change yl = false at hy
  change (xl && xs) = false at hf
  subst xb
  subst yl
  have hnf : ¬ (xl && xs) = true := by
    intro he
    rw [hf] at he
    cases he
  unfold certLiteralEPair
  dsimp only
  rw [if_neg hnf]
  change
    (({ l := xl, b := certFinThree 0, sh := xh,
        sg := (xs || ys) || false } : CertNative),
     ({ l := false, b := certFinThree yb.val, sh := yh, sg := ys } : CertNative)) =
      (({ l := xl, b := 0, sh := xh, sg := xs || ys } : CertNative),
       ({ l := false, b := yb, sh := yh, sg := ys } : CertNative))
  rw [fin_back yb, Bool.or_false, fin_empty]

private theorem row_move (x y : CertNative)
    (hx : x.sg = false) (hb : x.b ≠ 0)
    (hy : y.l = false) (hyb : y.b = 0) :
    certLiteralEPair x y =
      ({ x with b := 0, sg := false },
       { y with b := x.b, sg := false }) := by
  have hpos : 0 < x.b.val := by
    have hne : x.b.val ≠ 0 := by
      intro hz
      exact hb (Fin.ext hz)
    omega
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  change xs = false at hx
  change yl = false at hy
  change yb = 0 at hyb
  subst xs
  subst yl
  subst yb
  change 0 < xb.val at hpos
  have hnf : ¬ (xl && false) = true := by
    cases xl <;> decide +kernel
  unfold certLiteralEPair
  dsimp only
  rw [if_neg hnf]
  dsimp only
  rw [if_pos hpos]
  change
    (({ l := xl, b := 0, sh := xh, sg := false } : CertNative),
     ({ l := false, b := certFinThree xb.val, sh := yh, sg := false } : CertNative)) =
      (({ l := xl, b := 0, sh := xh, sg := false } : CertNative),
       ({ l := false, b := xb, sh := yh, sg := false } : CertNative))
  rw [fin_back xb]

private theorem row_launch (x y : CertNative)
    (hl : x.l = true) (hs : x.sg = true)
    (hy : y.l = false) (hyb : y.b = 0) :
    certLiteralEPair x y =
      ({ l := true, b := 0, sh := true, sg := false },
       { y with b := 2, sg := false }) := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  change xl = true at hl
  change xs = true at hs
  change yl = false at hy
  change yb = 0 at hyb
  subst xl
  subst xs
  subst yl
  subst yb
  rfl

private theorem row_leader (x y : CertNative)
    (hy : y.l = true)
    (hsurvive : (certLiteralEPair x y).2.l = true) :
    certLiteralEPair x y =
      ({ l := x.l, b := 0,
         sh := if x.l && x.sg then true else x.sh, sg := true },
       { l := true, b := if y.sg then 1 else y.b,
         sh := if y.sg then false else y.sh, sg := false }) := by
  rcases x with ⟨xl, xb, xh, xs⟩
  rcases y with ⟨yl, yb, yh, ys⟩
  change yl = true at hy
  subst yl
  unfold certLiteralEPair at hsurvive ⊢
  dsimp only at hsurvive ⊢
  by_cases hf : (xl && xs) = true
  · have hshield :
        (if xl && xs then true else xh) = true :=
      if_pos hf
    rw [hshield]
    rw [if_pos hf] at hsurvive ⊢
    cases ys <;> cases yh
    all_goals
      dsimp only at hsurvive ⊢
    all_goals
      first
      | contradiction
      | simp [fin_back, fin_empty, fin_one, hf] at hsurvive ⊢
  · have hshield :
        (if xl && xs then true else xh) = xh :=
      if_neg hf
    rw [hshield]
    rw [if_neg hf] at hsurvive ⊢
    rcases fin_cases xb with rfl | rfl | rfl <;>
      cases ys <;> cases yh
    all_goals
      dsimp only at hsurvive ⊢
    all_goals
      first
      | contradiction
      | simp [fin_back, fin_empty, fin_one, hf] at hsurvive ⊢

/-! Sector-restricted observations of a computed pair. -/

def pair (X : Nat → CertNative) (r : Nat)
    (out : CertNative × CertNative) : Nat → CertNative :=
  fun k => if k = r then out.1
    else if k = r + 1 then out.2 else X k

def incomingCells (X : Nat → CertNative)
    (out : CertNative × CertNative) : Nat → CertNative :=
  fun k => if k = 0 then out.2 else X k

private theorem terminal_pair_model
    (X : Nat → CertNative) (d r : Nat)
    (out : CertNative × CertNative) (hend : r + 1 = d)
    (hb : out.1.b = 0) (hs : out.1.sg = true) :
    Agree d (word (pair X r out))
      (absorb r { word X with
        shield := if r = 0 then out.1.sh else (word X).shield }) := by
  constructor
  · by_cases hrzero : r = 0
    · subst r
      simp [word, pair, absorb]
    · have hzero : 0 ≠ r := by omega
      simp [word, pair, absorb, hrzero, hzero]
  · intro k hk
    have hnext : k ≠ r + 1 := by omega
    by_cases he : k = r
    · subst k
      simp [word, pair, absorb, hb, hs]
    · simp [word, pair, absorb, he, hnext]

private theorem pair_absorb_model
    (X : Nat → CertNative) (d r : Nat) (hend : r + 1 = d)
    (hf : ((X r).l && (X r).sg) = false)
    (hy : (X (r + 1)).l = true)
    (hsurvive : (certLiteralEPair (X r) (X (r + 1))).2.l = true) :
    Agree d (word (pair X r (certLiteralEPair (X r) (X (r + 1)))))
      (absorb r (word X)) := by
  let out := certLiteralEPair (X r) (X (r + 1))
  have hrow := row_leader (X r) (X (r + 1)) hy hsurvive
  have hb : out.1.b = 0 := by simp only [out, hrow]
  have hs : out.1.sg = true := by simp only [out, hrow]
  have hh : out.1.sh = (X r).sh := by
    simp only [out, hrow, hf,
      if_neg (by decide +kernel : ¬ (false : Bool) = true)]
  have hshield :
      (if r = 0 then out.1.sh else (word X).shield) = (word X).shield := by
    by_cases hz : r = 0
    · subst r
      rw [if_pos rfl]
      exact hh
    · rw [if_neg hz]
  have h := terminal_pair_model X d r out hend hb hs
  simpa only [hshield] using h

private theorem pair_quiet_model
    (X : Nat → CertNative) (d r : Nat) (hr : r < d)
    (hf : ((X r).l && (X r).sg) = false) (hb : (X r).b = 0)
    (hy : (X (r + 1)).l = decide (r + 1 = d))
    (hsurvive : r + 1 = d →
      (certLiteralEPair (X r) (X (r + 1))).2.l = true) :
    Agree d (word (pair X r (certLiteralEPair (X r) (X (r + 1)))))
      (quiet d r (word X)) := by
  by_cases hend : r + 1 = d
  · have hyl : (X (r + 1)).l = true :=
      hy.trans (by simp [hend])
    have hrow := row_leader (X r) (X (r + 1)) hyl (hsurvive hend)
    simp only [hf, if_neg (by decide +kernel : ¬ (false : Bool) = true)] at hrow
    rw [hrow]
    constructor
    · by_cases hz : r = 0
      · subst r
        simp [word, pair, quiet]
      · have hzero : 0 ≠ r := by omega
        simp [word, pair, quiet, hzero]
    · intro k hk
      have hnext : k ≠ r + 1 := by omega
      by_cases he : k = r
      · subst k
        simp [word, pair, quiet, hb, hend]
      · simp [word, pair, quiet, he, hnext]
  · have hyl : (X (r + 1)).l = false :=
      hy.trans (by simp [hend])
    rw [row_quiet (X r) (X (r + 1)) hf hb hyl]
    constructor
    · by_cases hz : r = 0
      · subst r
        simp [word, pair, quiet]
      · have hzero : 0 ≠ r := by omega
        simp [word, pair, quiet, hzero]
    · intro k hk
      by_cases he : k = r
      · subst k
        simp [word, pair, quiet, hb, hend]
      · by_cases hnext : k = r + 1
        · subst k
          have hne : r + 1 ≠ r := by omega
          simp [word, pair, quiet, hne]
        · simp [word, pair, quiet, he, hnext]

private theorem pair_move_model
    (X : Nat → CertNative) (d r : Nat)
    (hx : (X r).sg = false) (hb : (X r).b ≠ 0)
    (hy : (X (r + 1)).l = false) (hyb : (X (r + 1)).b = 0) :
    Agree d (word (pair X r (certLiteralEPair (X r) (X (r + 1)))))
      (advance r (X r).b (word X)) := by
  rw [row_move (X r) (X (r + 1)) hx hb hy hyb]
  constructor
  · by_cases hz : r = 0
    · subst r
      simp [word, pair, advance]
    · have hzero : 0 ≠ r := by omega
      simp [word, pair, advance, hzero]
  · intro k hk
    by_cases he : k = r
    · subst k
      simp [word, pair, advance]
    · by_cases hnext : k = r + 1
      · subst k
        have hne : r + 1 ≠ r := by omega
        simp [word, pair, advance, hne]
      · simp [word, pair, advance, he, hnext]

private theorem pair_launch_model
    (X : Nat → CertNative) (d : Nat)
    (hl : (X 0).l = true) (hs : (X 0).sg = true)
    (hy : (X 1).l = false) (hyb : (X 1).b = 0) :
    Agree d (word (pair X 0 (certLiteralEPair (X 0) (X 1))))
      (advance 0 2 { word X with shield := true }) := by
  rw [row_launch (X 0) (X 1) hl hs hy hyb]
  constructor
  · simp [word, pair, advance]
  · intro k hk
    by_cases hz : k = 0
    · subst k
      simp [word, pair, advance]
    · by_cases ho : k = 1
      · subst k
        simp [word, pair, advance]
      · simp [word, pair, advance, hz, ho]

private theorem pair_ready_terminal_model
    (X : Nat → CertNative)
    (hl : (X 0).l = true) (hs : (X 0).sg = true)
    (hy : (X 1).l = true)
    (hsurvive : (certLiteralEPair (X 0) (X 1)).2.l = true) :
    Agree 1 (word (pair X 0 (certLiteralEPair (X 0) (X 1))))
      (absorb 0 { word X with shield := true }) := by
  let out := certLiteralEPair (X 0) (X 1)
  have hrow := row_leader (X 0) (X 1) hy hsurvive
  have hb : out.1.b = 0 := by simp only [out, hrow]
  have hsg : out.1.sg = true := by simp only [out, hrow]
  have hh : out.1.sh = true := by
    change (certLiteralEPair (X 0) (X 1)).1.sh = true
    rw [hrow]
    change (if (X 0).l && (X 0).sg then true else (X 0).sh) = true
    rw [hl, hs]
    rfl
  have hshield :
      (if (0 : Nat) = 0 then
        (certLiteralEPair (X 0) (X 1)).1.sh
       else (word X).shield) = true := by
    rw [if_pos rfl]
    change out.1.sh = true
    exact hh
  have h := terminal_pair_model X 1 0 out rfl hb hsg
  change
    Agree 1 (word (pair X 0 (certLiteralEPair (X 0) (X 1))))
      (absorb 0 { word X with shield :=
        if (0 : Nat) = 0 then
          (certLiteralEPair (X 0) (X 1)).1.sh
        else (word X).shield }) at h
  rw [hshield] at h
  exact h

private theorem internal_model
    (X : Nat → CertNative) (d r : Nat) (s : Stage)
    (hd : 0 < d) (hr : r < d)
    (hroot : (X 0).l = true)
    (hinner : ∀ k, 0 < k → k < d → (X k).l = false)
    (hend : (X d).l = true)
    (hsurvive : r + 1 = d →
      (certLiteralEPair (X r) (X (r + 1))).2.l = true)
    (h : Holds d (word X) s) :
    Agree d (word (pair X r (certLiteralEPair (X r) (X (r + 1)))))
      (insideWord d s r (word X)) := by
  have hy : (X (r + 1)).l = decide (r + 1 = d) := by
    by_cases ht : r + 1 = d
    · simpa [ht] using hend
    · have hl : (X (r + 1)).l = false :=
        hinner (r + 1) (by omega) (by omega)
      simpa [ht] using hl
  have inactive (hz : (word X).signal 0 = false) :
      ((X r).l && (X r).sg) = false := by
    by_cases hrzero : r = 0
    · subst r
      change (X 0).sg = false at hz
      rw [hz, Bool.and_false]
    · rw [hinner r (by omega) hr, Bool.false_and]
  cases s with
  | ready =>
      by_cases hrzero : r = 0
      · subst r
        by_cases hdshort : d = 1
        · subst d
          have hs : (X 0).sg = true := h.1
          change Agree 1
            (word (pair X 0 (certLiteralEPair (X 0) (X 1))))
            (absorb 0 { word X with shield := true })
          exact pair_ready_terminal_model X hroot hs hend (hsurvive rfl)
        · have hone : 1 < d := by omega
          have hs : (X 0).sg = true := h.1
          have hb : (X 1).b = 0 := h.2 1 hone
          change Agree d
            (word (pair X 0 (certLiteralEPair (X 0) (X 1))))
            (if d = 1 then absorb 0 { word X with shield := true }
             else advance 0 2 { word X with shield := true })
          rw [if_neg hdshort]
          exact pair_launch_model X d hroot hs
            (hinner 1 (by decide +kernel) hone) hb
      · have hf : ((X r).l && (X r).sg) = false := by
          rw [hinner r (by omega) hr, Bool.false_and]
        have hb : (X r).b = 0 := h.2 r hr
        simpa only [insideWord, if_neg hrzero] using
          pair_quiet_model X d r hr hf hb hy hsurvive
  | bullet live p =>
      have hz : (word X).signal 0 = false := h.2.2.2 0 (Nat.zero_le p)
      by_cases hrp : r = p
      · subst r
        have hb : (X p).b = kind live := by
          have hbullet := h.2.1 p h.1
          change (X p).b = (if p = p then kind live else 0) at hbullet
          rw [if_pos rfl] at hbullet
          exact hbullet
        have hbn : (X p).b ≠ 0 := by
          rw [hb]
          exact kind_ne_zero live
        by_cases hlast : p + 1 = d
        · have hl : (X (p + 1)).l = true := by
            rw [hlast]
            exact hend
          rw [insideWord, if_pos rfl, if_pos hlast]
          exact pair_absorb_model X d p hlast (inactive hz) hl
            (hsurvive hlast)
        · have hnext : p + 1 < d := by have hp := h.1; omega
          have hne : p + 1 ≠ p := by omega
          have hyb : (X (p + 1)).b = 0 := by
            have hbullet := h.2.1 (p + 1) hnext
            change (X (p + 1)).b =
              (if p + 1 = p then kind live else 0) at hbullet
            rw [if_neg hne] at hbullet
            exact hbullet
          have hmove := pair_move_model X d p
            (h.2.2.2 p (Nat.le_refl p)) hbn
            (hinner (p + 1) (by omega) hnext) hyb
          rw [hb] at hmove
          rw [insideWord, if_pos rfl, if_neg hlast]
          exact hmove
      · have hb : (X r).b = 0 := by
          have hbullet := h.2.1 r hr
          change (X r).b = (if r = p then kind live else 0) at hbullet
          rw [if_neg hrp] at hbullet
          exact hbullet
        simpa only [insideWord, if_neg hrp] using
          pair_quiet_model X d r hr (inactive hz) hb hy hsurvive
  | returning q =>
      have hz : (word X).signal 0 = false := h.2.2.2.1
      have hb : (X r).b = 0 := h.2.2.1 r hr
      exact pair_quiet_model X d r hr (inactive hz) hb hy hsurvive

private theorem incoming_model
    (X : Nat → CertNative) (left : CertNative) (d : Nat) (s : Stage)
    (hroot : (X 0).l = true)
    (hsurvive : (certLiteralEPair left (X 0)).2.l = true)
    (h : Holds d (word X) s) :
    Agree d (word (incomingCells X (certLiteralEPair left (X 0))))
      (incomingWord s (word X)) := by
  rw [row_leader left (X 0) hroot hsurvive]
  cases s with
  | ready =>
      have hs : (X 0).sg = true := h.1
      constructor
      · simp [word, incomingCells, incomingWord, hs]
      · intro k hk
        by_cases hz : k = 0
        · subst k
          simp [word, incomingCells, incomingWord, hs]
        · simp [word, incomingCells, incomingWord, hz]
  | bullet live p =>
      have hs : (X 0).sg = false := h.2.2.2 0 (Nat.zero_le p)
      constructor
      · simp [word, incomingCells, incomingWord, hs]
      · intro k hk
        by_cases hz : k = 0
        · subst k
          simp [word, incomingCells, incomingWord, hs]
        · simp [word, incomingCells, incomingWord, hz]
  | returning q =>
      have hs : (X 0).sg = false := h.2.2.2.1
      constructor
      · simp [word, incomingCells, incomingWord, hs]
      · intro k hk
        by_cases hz : k = 0
        · subst k
          simp [word, incomingCells, incomingWord, hs]
        · simp [word, incomingCells, incomingWord, hz]

/-! Actual ring geometry and OLD-pair correspondence. -/

def position {n : Nat} (ring : DirectedRing n)
    (a i : Fin n) : Fin n :=
  ⟨PPL.cyclicOffset ring a i, Nat.mod_lt _ ring.hn⟩

private theorem position_site {n : Nat}
    (ring : DirectedRing n) (a k : Fin n) :
    position ring a (sealedSite ring a k.val) = k := by
  apply Fin.ext
  have ha := a.isLt
  have hk := k.isLt
  change (((a.val + k.val) % n + n - a.val) % n) = k.val
  by_cases hs : a.val + k.val < n
  · rw [Nat.mod_eq_of_lt hs]
    have he : a.val + k.val + n - a.val = n + k.val := by omega
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  · have hge : n ≤ a.val + k.val := by omega
    have hlt : a.val + k.val - n < n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    have he : a.val + k.val - n + n - a.val = k.val := by omega
    rw [he, Nat.mod_eq_of_lt hk]

private theorem site_position {n : Nat}
    (ring : DirectedRing n) (a i : Fin n) :
    sealedSite ring a (position ring a i).val = i := by
  apply Fin.ext
  have ha := a.isLt
  have hi := i.isLt
  change (a.val + ((i.val + n - a.val) % n)) % n = i.val
  by_cases hle : a.val ≤ i.val
  · have he : i.val + n - a.val = n + (i.val - a.val) := by omega
    rw [he, Nat.add_mod_left,
      Nat.mod_eq_of_lt (by omega : i.val - a.val < n)]
    have hh : a.val + (i.val - a.val) = i.val := by omega
    rw [hh, Nat.mod_eq_of_lt hi]
  · have hlt : i.val + n - a.val < n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hh : a.val + (i.val + n - a.val) = i.val + n := by omega
    rw [hh, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private theorem site_inj {n : Nat}
    (ring : DirectedRing n) (a : Fin n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    sealedSite ring a i = sealedSite ring a j ↔ i = j := by
  constructor
  · intro h
    have he := congrArg (position ring a) h
    have hleft := position_site ring a (⟨i, hi⟩ : Fin n)
    have hright := position_site ring a (⟨j, hj⟩ : Fin n)
    rw [hleft, hright] at he
    exact congrArg Fin.val he
  · intro h
    subst j
    rfl

private theorem site_full {n : Nat}
    (ring : DirectedRing n) (a : Fin n) : sealedSite ring a n = a := by
  apply Fin.ext
  change (a.val + n) % n = a.val
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt a.isLt]

private theorem site_succ {n : Nat}
    (ring : DirectedRing n) (a : Fin n) (k : Nat) :
    sealedSite ring a (k + 1) = ring.rightNeighbor (sealedSite ring a k) := by
  apply Fin.ext
  change (a.val + (k + 1)) % n = ((a.val + k) % n + 1) % n
  calc
    (a.val + (k + 1)) % n = (a.val + k + 1) % n :=
      congrArg (fun z => z % n) (by omega)
    _ = ((a.val + k) % n + 1) % n := (Nat.mod_add_mod _ _ _).symm

private theorem native_inside_at {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (r k : Nat) (hr : r + 1 < n) (hk : k < n) :
    nativeE ring N (sealedSite ring a r) (sealedSite ring a k) =
      pair (cells ring N a) r
        (certLiteralEPair (cells ring N a r) (cells ring N a (r + 1))) k := by
  have hleft := site_inj ring a k r hk (by omega)
  have hright := site_inj ring a k (r + 1) hk hr
  simp only [nativeE, ← site_succ, pair, cells, hleft, hright]

private theorem disjoint_relative {n : Nat}
    (ring : DirectedRing n) (a : Fin n) (d r : Nat)
    (hdr : d ≤ r) (hr : r + 1 < n) :
    SealedEdgeDisjoint ring a d (sealedSite ring a r) := by
  intro k hk
  constructor
  · intro he
    have hv := (site_inj ring a k.val r k.isLt (by omega)).1 he
    omega
  · intro he
    have he' : sealedSite ring a k.val = sealedSite ring a (r + 1) :=
      he.trans (site_succ ring a r).symm
    have hv := (site_inj ring a k.val (r + 1) k.isLt hr).1 he'
    omega

private theorem native_incoming_at {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d k : Nat) (hd : 0 < d) (hdn : d < n) (hk : k < d) :
    nativeE ring N (sealedSite ring a (n - 1)) (sealedSite ring a k) =
      incomingCells (cells ring N a)
        (certLiteralEPair (N (sealedSite ring a (n - 1))) (N a)) k := by
  have hn : 0 < n := ring.hn
  have hin : n - 1 < n := by omega
  have hkn : k < n := by omega
  have hnext : ring.rightNeighbor (sealedSite ring a (n - 1)) = a := by
    calc
      ring.rightNeighbor (sealedSite ring a (n - 1)) =
          sealedSite ring a (n - 1 + 1) := (site_succ ring a (n - 1)).symm
      _ = sealedSite ring a n := congrArg (sealedSite ring a) (by omega)
      _ = a := site_full ring a
  have hleft : sealedSite ring a k ≠ sealedSite ring a (n - 1) := by
    intro he
    have hv := (site_inj ring a k (n - 1) hkn hin).1 he
    omega
  have hright : sealedSite ring a k = a ↔ k = 0 := by
    have h := site_inj ring a k 0 hkn hn
    simpa only [sealedSite_zero] using h
  simp only [nativeE, hnext, if_neg hleft, hright, incomingCells, cells]

private theorem native_internal_agree {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d r : Nat) (s : Stage)
    (hc : ConsecutiveNative ring N a b d)
    (hr : r < d)
    (hb : (nativeE ring N (sealedSite ring a r) b).l = true)
    (hs : Holds d (view ring N a) s) :
    Agree d (view ring (nativeE ring N (sealedSite ring a r)) a)
      (insideWord d s r (view ring N a)) := by
  rcases hc with ⟨hdpos, hdn, hsite, haold, hbold, hbetween⟩
  let X := cells ring N a
  have hd : 0 < d := by omega
  have hrn : r + 1 < n := by omega
  have hlocal :
      Agree d (view ring (nativeE ring N (sealedSite ring a r)) a)
        (word (pair X r (certLiteralEPair (X r) (X (r + 1))))) := by
    apply agree_of_cells hd
    intro k hk
    exact native_inside_at ring N a r k hrn (by omega)
  have hroot : (X 0).l = true := by
    simpa only [X, cells, sealedSite_zero] using haold
  have hinner : ∀ k, 0 < k → k < d → (X k).l = false := by
    intro k hk hkd
    exact hbetween ⟨k, by omega⟩ hk hkd
  have hend : (X d).l = true := by
    change (N (sealedSite ring a d)).l = true
    rw [← hsite]
    exact hbold
  have hsurvive : r + 1 = d →
      (certLiteralEPair (X r) (X (r + 1))).2.l = true := by
    intro he
    have hright := native_inside_at ring N a r (r + 1) hrn hrn
    have hne : r + 1 ≠ r := by omega
    simp only [pair, if_neg hne, if_pos rfl] at hright
    have hbs : b = sealedSite ring a (r + 1) := by
      rw [he]
      exact hsite
    have hphys :
        (nativeE ring N (sealedSite ring a r)
          (sealedSite ring a (r + 1))).l = true := by
      rw [← hbs]
      exact hb
    exact (congrArg CertNative.l hright).symm.trans hphys
  exact agree_trans hlocal
    (internal_model X d r s hd hr hroot hinner hend hsurvive hs)

private theorem native_incoming_agree {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (s : Stage)
    (hc : ConsecutiveNative ring N a b d)
    (ha : (nativeE ring N (sealedSite ring a (n - 1)) a).l = true)
    (hs : Holds d (view ring N a) s) :
    Agree d (view ring (nativeE ring N (sealedSite ring a (n - 1))) a)
      (incomingWord s (view ring N a)) := by
  rcases hc with ⟨hdpos, hdn, hsite, haold, hbold, hbetween⟩
  have hd : 0 < d := by omega
  let X := cells ring N a
  let left := N (sealedSite ring a (n - 1))
  have hroot : (X 0).l = true := by
    simpa only [X, cells, sealedSite_zero] using haold
  have hright := native_incoming_at ring N a d 0 hd hdn hd
  simp only [sealedSite_zero, incomingCells, if_pos rfl] at hright
  have hsactual : (certLiteralEPair left (N a)).2.l = true :=
    (congrArg CertNative.l hright).symm.trans ha
  have hsurvive : (certLiteralEPair left (X 0)).2.l = true := by
    simpa only [X, cells, sealedSite_zero] using hsactual
  have hlocal :
      Agree d (view ring (nativeE ring N (sealedSite ring a (n - 1))) a)
        (word (incomingCells X (certLiteralEPair left (X 0)))) := by
    apply agree_of_cells hd
    intro k hk
    simpa only [X, left, cells, sealedSite_zero] using
      native_incoming_at ring N a d k hd hdn hk
  exact agree_trans hlocal (incoming_model X left d s hroot hsurvive hs)

end SealedCloseProof

/-! Public all-edge statements for the original pinned predicates. -/

/-- The surviving-endpoint step theorem. Progress is charged only
from a non-Ready old phase. The conclusion also includes finishing
an excursion at Ready, whose successor progress is zero. -/
theorem sealed_close_step_with_progress {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n) (phase : SealedPhase n)
    (hc : ConsecutiveNative ring N a b d)
    (hp : SealedPhaseHolds ring N a d phase)
    (ha : (nativeE ring N e a).l = true)
    (hb : (nativeE ring N e b).l = true) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring (nativeE ring N e) a d nextPhase ∧
      (phase ≠ .ready →
        SealedPhaseProgress d nextPhase ≤ SealedPhaseProgress d phase ∧
        (e = SealedPhaseEdge ring a phase →
          SealedPhaseProgress d nextPhase + 1 ≤ SealedPhaseProgress d phase)) := by
  open SealedCloseProof in
  let s := fromPhase phase
  have hd : 0 < d := by have h := hc.1; omega
  have hdn : d < n := hc.2.1
  have hs : SealedCloseProof.Holds d (SealedCloseProof.view ring N a) s :=
    (SealedCloseProof.phase_view ring N a d hdn phase).2 hp
  have finish (t : SealedCloseProof.Stage)
      (ht : SealedCloseProof.Holds d
        (SealedCloseProof.view ring (nativeE ring N e) a) t)
      (hprogress : s ≠ .ready →
        SealedCloseProof.rank d t ≤ SealedCloseProof.rank d s ∧
        (e = sealedSite ring a (SealedCloseProof.nominated s) →
          SealedCloseProof.rank d t + 1 ≤ SealedCloseProof.rank d s)) :
      ∃ nextPhase : SealedPhase n,
        SealedPhaseHolds ring (nativeE ring N e) a d nextPhase ∧
        (phase ≠ .ready →
          SealedPhaseProgress d nextPhase ≤ SealedPhaseProgress d phase ∧
          (e = SealedPhaseEdge ring a phase →
            SealedPhaseProgress d nextPhase + 1 ≤ SealedPhaseProgress d phase)) := by
    obtain ⟨nextPhase, hn, he⟩ :=
      SealedCloseProof.realize ring (nativeE ring N e) a d hdn t ht
    refine ⟨nextPhase, hn, ?_⟩
    intro hnr
    have hsne : s ≠ .ready := SealedCloseProof.phase_nonready phase hnr
    have hg := hprogress hsne
    have hrnew : SealedCloseProof.rank d t =
        SealedPhaseProgress d nextPhase := by
      calc
        SealedCloseProof.rank d t =
            SealedCloseProof.rank d (SealedCloseProof.fromPhase nextPhase) :=
          congrArg (SealedCloseProof.rank d) he.symm
        _ = SealedPhaseProgress d nextPhase :=
          SealedCloseProof.phase_rank d nextPhase
    have hrold : SealedCloseProof.rank d s = SealedPhaseProgress d phase :=
      SealedCloseProof.phase_rank d phase
    constructor
    · simpa only [hrnew, hrold] using hg.1
    · intro hedge
      have heSite : e = sealedSite ring a (SealedCloseProof.nominated s) :=
        hedge.trans (SealedCloseProof.phase_edge ring a phase).symm
      simpa only [hrnew, hrold] using hg.2 heSite
  let r := SealedCloseProof.position ring a e
  have hrn : r.val < n := r.isLt
  have he : sealedSite ring a r.val = e :=
    SealedCloseProof.site_position ring a e
  have hnom : SealedCloseProof.nominated s < d :=
    SealedCloseProof.nominated_lt hd hs
  by_cases hr : r.val < d
  · have hb' : (nativeE ring N (sealedSite ring a r.val) b).l = true := by
      simpa only [he] using hb
    have hword : SealedCloseProof.Agree d
        (SealedCloseProof.view ring (nativeE ring N e) a)
        (SealedCloseProof.insideWord d s r.val (SealedCloseProof.view ring N a)) := by
      simpa only [he] using
        SealedCloseProof.native_internal_agree ring N a b d r.val s hc hr hb' hs
    have ht := SealedCloseProof.holds_of_agree hd hword
      (SealedCloseProof.insideStage d s r.val)
      (SealedCloseProof.inside_preserves d r.val
        (SealedCloseProof.view ring N a) s hd hr hs)
    apply finish (SealedCloseProof.insideStage d s r.val) ht
    intro hnr
    have hg := SealedCloseProof.inside_progress d r.val
      (SealedCloseProof.view ring N a) s hs hnr
    refine ⟨hg.1, ?_⟩
    intro hedge
    have hindex : r.val = SealedCloseProof.nominated s :=
      (SealedCloseProof.site_inj ring a r.val
        (SealedCloseProof.nominated s) hrn (by omega)).1 (he.trans hedge)
    exact hg.2 hindex
  · have hnomne : e ≠ sealedSite ring a (SealedCloseProof.nominated s) := by
      intro hedge
      have hindex := (SealedCloseProof.site_inj ring a r.val
        (SealedCloseProof.nominated s) hrn (by omega)).1 (he.trans hedge)
      omega
    by_cases hwrap : r.val + 1 = n
    · have hrend : r.val = n - 1 := by omega
      have heIn : sealedSite ring a (n - 1) = e :=
        (congrArg (sealedSite ring a) hrend).symm.trans he
      have ha' :
          (nativeE ring N (sealedSite ring a (n - 1)) a).l = true := by
        simpa only [heIn] using ha
      have hword : SealedCloseProof.Agree d
          (SealedCloseProof.view ring (nativeE ring N e) a)
          (SealedCloseProof.incomingWord s (SealedCloseProof.view ring N a)) := by
        simpa only [heIn] using
          SealedCloseProof.native_incoming_agree ring N a b d s hc ha' hs
      have ht := SealedCloseProof.holds_of_agree hd hword
        (SealedCloseProof.incomingStage s)
        (SealedCloseProof.incoming_preserves d
          (SealedCloseProof.view ring N a) s hd hs)
      apply finish (SealedCloseProof.incomingStage s) ht
      intro hnr
      have hsame := SealedCloseProof.incoming_same s hnr
      refine ⟨?_, ?_⟩
      · simpa only [hsame] using Nat.le_refl (SealedCloseProof.rank d s)
      · intro hedge
        exact False.elim (hnomne hedge)
    · have hnext : r.val + 1 < n := by omega
      have hdisjoint : SealedEdgeDisjoint ring a d e := by
        rw [← he]
        exact SealedCloseProof.disjoint_relative ring a d r.val (by omega) hnext
      refine ⟨phase, sealed_phase_frame ring N a d hd e phase hdisjoint hp, ?_⟩
      intro hnr
      refine ⟨Nat.le_refl _, ?_⟩
      intro hedge
      exact False.elim
        (hnomne (hedge.trans (SealedCloseProof.phase_edge ring a phase).symm))

/-- Corrected closure (A), for every selected physical edge. -/
theorem sealed_all_edge_closed {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hs : Sealed ring N a d) :
    (nativeE ring N e a).l = false ∨
    (nativeE ring N e b).l = false ∨
    Sealed ring (nativeE ring N e) a d := by
  cases ha : (nativeE ring N e a).l with
  | false => exact Or.inl rfl
  | true =>
      cases hb : (nativeE ring N e b).l with
      | false => exact Or.inr (Or.inl rfl)
      | true =>
          obtain ⟨phase, hp⟩ := hs
          obtain ⟨nextPhase, hn, _⟩ :=
            sealed_close_step_with_progress ring N a b d e phase hc hp ha hb
          exact Or.inr (Or.inr ⟨nextPhase, hn⟩)

/-- Corrected non-Ready-to-non-Ready progress (B). A separate Ready
arrival is not an obstruction: the stronger step theorem above
already gives its zero successor quota. -/
theorem sealed_nonready_excursion_progress {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n) (phase : SealedPhase n)
    (hc : ConsecutiveNative ring N a b d)
    (hp : SealedPhaseHolds ring N a d phase)
    (hnr : phase ≠ .ready)
    (ha : (nativeE ring N e a).l = true)
    (hb : (nativeE ring N e b).l = true)
    (hnotready : ¬ SealedCleanReady ring (nativeE ring N e) a d) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring (nativeE ring N e) a d nextPhase ∧
      nextPhase ≠ .ready ∧
      SealedPhaseProgress d nextPhase ≤ SealedPhaseProgress d phase ∧
      (e = SealedPhaseEdge ring a phase →
        SealedPhaseProgress d nextPhase + 1 ≤ SealedPhaseProgress d phase) := by
  obtain ⟨nextPhase, hn, hprogress⟩ :=
    sealed_close_step_with_progress ring N a b d e phase hc hp ha hb
  refine ⟨nextPhase, hn, ?_, (hprogress hnr).1, (hprogress hnr).2⟩
  intro he
  subst nextPhase
  exact hnotready hn

/-- The two sectors are updated by the very same physical service.
This includes an edge which enters one source and is simultaneously
the last edge of the complementary sector; no second nativeE is run. -/
theorem sealed_two_sector_survival {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (dA dB : Nat) (e : Fin n)
    (hcA : ConsecutiveNative ring N a b dA)
    (hcB : ConsecutiveNative ring N b a dB)
    (hsA : Sealed ring N a dA) (hsB : Sealed ring N b dB)
    (ha : (nativeE ring N e a).l = true)
    (hb : (nativeE ring N e b).l = true) :
    Sealed ring (nativeE ring N e) a dA ∧
    Sealed ring (nativeE ring N e) b dB := by
  obtain ⟨pA, hpA⟩ := hsA
  obtain ⟨pB, hpB⟩ := hsB
  obtain ⟨qA, hqA, _⟩ :=
    sealed_close_step_with_progress ring N a b dA e pA hcA hpA ha hb
  obtain ⟨qB, hqB, _⟩ :=
    sealed_close_step_with_progress ring N b a dB e pB hcB hpB hb ha
  exact ⟨⟨qA, hqA⟩, ⟨qB, hqB⟩⟩

/-- Internal collisions cannot occur in any of the four sealed
phases. Preparation's multiple-bullet collision argument is not an
extra closure case: it belongs to the earlier, unsealed stage. -/
theorem sealed_no_distinct_sector_bullets {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a : Fin n) (d : Nat) (phase : SealedPhase n)
    (hp : SealedPhaseHolds ring N a d phase)
    (i j : Fin n) (hi : i.val < d) (hj : j.val < d)
    (hbi : (sealedAt ring N a i).b ≠ 0)
    (hbj : (sealedAt ring N a j).b ≠ 0) : i = j := by
  have unique (p : Fin n) (v : Fin 3)
      (h : SealedUniqueBullet ring N a d p v) : i = j := by
    have hip : i = p := by
      by_cases he : i = p
      · exact he
      · exact False.elim (hbi (h.2.2 i hi he))
    have hjp : j = p := by
      by_cases he : j = p
      · exact he
      · exact False.elim (hbj (h.2.2 j hj he))
    exact hip.trans hjp.symm
  cases phase with
  | ready => exact False.elim (hbi (hp.2 i hi))
  | dummy p => exact unique p 1 hp.1
  | live p => exact unique p 2 hp.1
  | returning q => exact False.elim (hbi (hp.1 i hi))

end L3


/-! ## Exact stage table of a surviving native edge.

The cases are exactly those of
sealed_close_step_with_progress, including cyclic predecessor wrap.
The theorem is about the original nativeE row, not an abstract
observation transition or an edited protocol. -/

namespace L3

open K2ArbitraryElimination.FiniteAccounting
open FiniteUniformStoppingTree

/-- The successor stage selected by a physical ring edge.  In the
interior (offset r < d) use the internal table; for the unique
incoming edge (offset r = n-1) use the incoming table; otherwise
the sector is framed and its stage is unchanged. -/
def sealedCloseTable {n : Nat} (ring : DirectedRing n)
    (a : Fin n) (d : Nat) (e : Fin n)
    (phase : SealedPhase n) : SealedCloseProof.Stage :=
  let r := SealedCloseProof.position ring a e
  if r.val < d then
    SealedCloseProof.insideStage d
      (SealedCloseProof.fromPhase phase) r.val
  else if r.val + 1 = n then
    SealedCloseProof.incomingStage (SealedCloseProof.fromPhase phase)
  else SealedCloseProof.fromPhase phase

/-- Exact successor-stage strengthening of sealed_close_step_with_progress.
Every conclusion is about one literal nativeE service and assumes
survival of both physical endpoints. -/
theorem sealed_close_step_stage {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (e : Fin n) (phase : SealedPhase n)
    (hc : ConsecutiveNative ring N a b d)
    (hp : SealedPhaseHolds ring N a d phase)
    (ha : (nativeE ring N e a).l = true)
    (hb : (nativeE ring N e b).l = true) :
    ∃ nextPhase : SealedPhase n,
      SealedPhaseHolds ring (nativeE ring N e) a d nextPhase ∧
      SealedCloseProof.fromPhase nextPhase =
        sealedCloseTable ring a d e phase := by
  let s := SealedCloseProof.fromPhase phase
  have hd : 0 < d := by
    have h := hc.1
    omega
  have hdn : d < n := hc.2.1
  have hs : SealedCloseProof.Holds d
      (SealedCloseProof.view ring N a) s :=
    (SealedCloseProof.phase_view ring N a d hdn phase).2 hp
  let r := SealedCloseProof.position ring a e
  have hrn : r.val < n := r.isLt
  have he : sealedSite ring a r.val = e :=
    SealedCloseProof.site_position ring a e
  by_cases hr : r.val < d
  · have hb' :
        (nativeE ring N (sealedSite ring a r.val) b).l = true := by
      simpa only [he] using hb
    have hword : SealedCloseProof.Agree d
        (SealedCloseProof.view ring (nativeE ring N e) a)
        (SealedCloseProof.insideWord d s r.val
          (SealedCloseProof.view ring N a)) := by
      simpa only [he] using
        SealedCloseProof.native_internal_agree
          ring N a b d r.val s hc hr hb' hs
    have ht : SealedCloseProof.Holds d
        (SealedCloseProof.view ring (nativeE ring N e) a)
        (SealedCloseProof.insideStage d s r.val) :=
      SealedCloseProof.holds_of_agree hd hword
        (SealedCloseProof.insideStage d s r.val)
        (SealedCloseProof.inside_preserves d r.val
          (SealedCloseProof.view ring N a) s hd hr hs)
    obtain ⟨nextPhase, hnext, hstage⟩ :=
      SealedCloseProof.realize ring (nativeE ring N e) a d
        hdn (SealedCloseProof.insideStage d s r.val) ht
    refine ⟨nextPhase, hnext, ?_⟩
    change SealedCloseProof.fromPhase nextPhase =
      if r.val < d then
        SealedCloseProof.insideStage d s r.val
      else if r.val + 1 = n then
        SealedCloseProof.incomingStage s
      else s
    simpa only [if_pos hr] using hstage
  · by_cases hwrap : r.val + 1 = n
    · have hrend : r.val = n - 1 := by omega
      have heIn : sealedSite ring a (n - 1) = e :=
        (congrArg (sealedSite ring a) hrend).symm.trans he
      have ha' :
          (nativeE ring N (sealedSite ring a (n - 1)) a).l = true := by
        simpa only [heIn] using ha
      have hword : SealedCloseProof.Agree d
          (SealedCloseProof.view ring (nativeE ring N e) a)
          (SealedCloseProof.incomingWord s
            (SealedCloseProof.view ring N a)) := by
        simpa only [heIn] using
          SealedCloseProof.native_incoming_agree
            ring N a b d s hc ha' hs
      have ht : SealedCloseProof.Holds d
          (SealedCloseProof.view ring (nativeE ring N e) a)
          (SealedCloseProof.incomingStage s) :=
        SealedCloseProof.holds_of_agree hd hword
          (SealedCloseProof.incomingStage s)
          (SealedCloseProof.incoming_preserves d
            (SealedCloseProof.view ring N a) s hd hs)
      obtain ⟨nextPhase, hnext, hstage⟩ :=
        SealedCloseProof.realize ring (nativeE ring N e) a d
          hdn (SealedCloseProof.incomingStage s) ht
      refine ⟨nextPhase, hnext, ?_⟩
      change SealedCloseProof.fromPhase nextPhase =
        if r.val < d then
          SealedCloseProof.insideStage d s r.val
        else if r.val + 1 = n then
          SealedCloseProof.incomingStage s
        else s
      simpa only [if_neg hr, if_pos hwrap] using hstage
    · have hnext : r.val + 1 < n := by omega
      have hdisjoint : SealedEdgeDisjoint ring a d e := by
        rw [← he]
        exact SealedCloseProof.disjoint_relative
          ring a d r.val (by omega) hnext
      refine ⟨phase, sealed_phase_frame
        ring N a d hd e phase hdisjoint hp, ?_⟩
      change s =
        if r.val < d then
          SealedCloseProof.insideStage d s r.val
        else if r.val + 1 = n then
          SealedCloseProof.incomingStage s
        else s
      simp only [if_neg hr, if_neg hwrap]

/-- Consecutive endpoints are distinct because 0 < d < n. -/
theorem sealed_consecutive_endpoints_ne {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat)
    (hc : ConsecutiveNative ring N a b d) : a ≠ b := by
  intro hab
  have hzero : 0 < n := ring.hn
  have hsite :
      sealedSite ring a 0 = sealedSite ring a d := by
    rw [sealedSite_zero, ← hc.2.2.1]
    exact hab
  have heq := (SealedCloseProof.site_inj ring a 0 d
    hzero hc.2.1).1 hsite
  have hd1 := hc.1
  omega

/-- The phase's nominated physical edge has precisely its nominated
source-relative offset. This is the bridge between the Stage table
and the original per-edge quota / Bellman scheduler. -/
theorem sealed_close_nominated_position {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (phase : SealedPhase n)
    (hc : ConsecutiveNative ring N a b d)
    (hp : SealedPhaseHolds ring N a d phase) :
    (SealedCloseProof.position ring a
      (SealedPhaseEdge ring a phase)).val =
        SealedCloseProof.nominated
          (SealedCloseProof.fromPhase phase) := by
  have hd : 0 < d := by have h := hc.1; omega
  have hdn : d < n := hc.2.1
  have hholds : SealedCloseProof.Holds d
      (SealedCloseProof.view ring N a)
      (SealedCloseProof.fromPhase phase) :=
    (SealedCloseProof.phase_view ring N a d hdn phase).2 hp
  have hnom : SealedCloseProof.nominated
      (SealedCloseProof.fromPhase phase) < n :=
    Nat.lt_trans
      (SealedCloseProof.nominated_lt hd hholds) hdn
  have heq :=
    SealedCloseProof.position_site ring a
      (⟨SealedCloseProof.nominated
        (SealedCloseProof.fromPhase phase), hnom⟩ : Fin n)
  have hsite := SealedCloseProof.phase_edge ring a phase
  rw [hsite] at heq
  exact congrArg Fin.val heq

/-- The terminal edge of a sealed sector is the edge entering its
right endpoint, including the wraparound and two-leader cases. -/
theorem sealed_close_last_bullet_enters_right {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (p : Fin n)
    (hc : ConsecutiveNative ring N a b d)
    (hlast : p.val + 1 = d) :
    ring.rightNeighbor (SealedPhaseEdge ring a (.live p)) = b := by
  calc
    ring.rightNeighbor (SealedPhaseEdge ring a (.live p)) =
      sealedSite ring a (p.val + 1) := by
        simpa only [SealedPhaseEdge] using
          (SealedCloseProof.site_succ ring a p.val).symm
    _ = sealedSite ring a d := by rw [hlast]
    _ = b := hc.2.2.1.symm

/-- The nominated physical edge is strictly inside the half-open
sector and hence is never its terminal leader's outgoing edge. -/
theorem sealed_close_nominated_ne_right {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (phase : SealedPhase n)
    (hc : ConsecutiveNative ring N a b d)
    (hp : SealedPhaseHolds ring N a d phase) :
    SealedPhaseEdge ring a phase ≠ b := by
  intro he
  have hd : 0 < d := by have h := hc.1; omega
  have hdn : d < n := hc.2.1
  have hholds : SealedCloseProof.Holds d
      (SealedCloseProof.view ring N a)
      (SealedCloseProof.fromPhase phase) :=
    (SealedCloseProof.phase_view ring N a d hdn phase).2 hp
  have hnom := SealedCloseProof.nominated_lt hd hholds
  have hsite : sealedSite ring a
      (SealedCloseProof.nominated
        (SealedCloseProof.fromPhase phase)) = sealedSite ring a d := by
    calc
      sealedSite ring a
          (SealedCloseProof.nominated
            (SealedCloseProof.fromPhase phase)) =
        SealedPhaseEdge ring a phase :=
          SealedCloseProof.phase_edge ring a phase
      _ = b := he
      _ = sealedSite ring a d := hc.2.2.1
  have hidx := (SealedCloseProof.site_inj ring a
    (SealedCloseProof.nominated
      (SealedCloseProof.fromPhase phase)) d
    (by omega : SealedCloseProof.nominated
      (SealedCloseProof.fromPhase phase) < n) hdn).1 hsite
  omega

/-- The last site of the cyclic source-relative enumeration is the
real physical predecessor of its source, for arbitrary wraparound. -/
theorem sealed_close_last_site_left {n : Nat}
    (ring : DirectedRing n) (a : Fin n) :
    sealedSite ring a (n - 1) = ring.leftNeighbor a := by
  apply Fin.ext
  change (a.val + (n - 1)) % n = (a.val + n - 1) % n
  have h : a.val + (n - 1) = a.val + n - 1 := by
    have hn := ring.hn
    omega
  rw [h]

/-- Exact incoming-edge classifier for the stage table. -/
theorem sealed_close_incoming_iff {n : Nat}
    (ring : DirectedRing n) (a e : Fin n) :
    (SealedCloseProof.position ring a e).val + 1 = n ↔
      e = ring.leftNeighbor a := by
  constructor
  · intro hr
    have hp := SealedCloseProof.site_position ring a e
    have hidx :
        (SealedCloseProof.position ring a e).val = n - 1 := by omega
    calc
      e = sealedSite ring a
          (SealedCloseProof.position ring a e).val := hp.symm
      _ = sealedSite ring a (n - 1) := by rw [hidx]
      _ = ring.leftNeighbor a := sealed_close_last_site_left ring a
  · intro he
    subst e
    have hp := SealedCloseProof.position_site ring a
      (⟨n - 1, by have h := ring.hn; omega⟩ : Fin n)
    rw [sealed_close_last_site_left] at hp
    have hv := congrArg Fin.val hp
    change (SealedCloseProof.position ring a
      (ring.leftNeighbor a)).val = n - 1 at hv
    omega

/-- Recover a physical edge from its source-relative offset. -/
theorem sealed_close_edge_of_position {n : Nat}
    (ring : DirectedRing n) (a e : Fin n) (r : Nat)
    (hr : (SealedCloseProof.position ring a e).val = r) :
    e = sealedSite ring a r := by
  calc
    e = sealedSite ring a
        (SealedCloseProof.position ring a e).val :=
      (SealedCloseProof.site_position ring a e).symm
    _ = sealedSite ring a r := by rw [hr]

/-- Public bound for the nominated stage offset, avoiding use of
private SealedCloseProof proof internals from importing files. -/
theorem sealed_close_nominated_lt {n : Nat}
    (ring : DirectedRing n) (N : Fin n → CertNative)
    (a b : Fin n) (d : Nat) (phase : SealedPhase n)
    (hc : ConsecutiveNative ring N a b d)
    (hp : SealedPhaseHolds ring N a d phase) :
    SealedCloseProof.nominated
      (SealedCloseProof.fromPhase phase) < d := by
  have hd : 0 < d := by have h := hc.1; omega
  have hdn : d < n := hc.2.1
  have hholds : SealedCloseProof.Holds d
      (SealedCloseProof.view ring N a)
      (SealedCloseProof.fromPhase phase) :=
    (SealedCloseProof.phase_view ring N a d hdn phase).2 hp
  exact SealedCloseProof.nominated_lt hd hholds

end L3
