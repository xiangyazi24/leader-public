import Leader.Wu.Authorization.CheckReadyStep

/-!
# A finite sweep of an internal CHECK-ready interval

This is a positional composition of `ready_step` on the original AuthF
protocol.  The first cell is already a lineage departure; all following
cells in the selected interval are ready.  A word of internal physical edges
either reaches a leader or a real path hole, or releases the entire interval.
No equal-root or terminal row is used.
-/
namespace PPLLAuthCheckReadySweep

open PPLL PPLLAuthF PPLLAuthCheckComponent PPLLAuthCheckComponentFrame
open PPLLAuthCheckComponentStep PPLLAuthGenDrain
open PPLLAuthResetDrain (authRun)

set_option autoImplicit false

variable {n ψ : Nat}

private abbrev cellAt (ring : DirectedRing n) (g k : Nat)
    (C : Fin n → AuthState ψ) : AuthState ψ := C (bcell ring ψ g k)

/-- An untouched ready successor; its control mark is deliberately arbitrary. -/
def ReadyAt (ring : DirectedRing n) (g k : Nat) (γ : ProvColor)
    (C : Fin n → AuthState ψ) : Prop :=
  (cellAt ring g k C).core.state = .CHECK_ready ∧
  (∃ bit, (cellAt ring g k C).core.path = .some k bit) ∧
  (cellAt ring g k C).core.path2 = none ∧
  (cellAt ring g k C).path_mark = γ

/-- A released cell retains the exact path it held at the start of the word. -/
def DoneAt (ring : DirectedRing n) (g k : Nat) (γ : ProvColor)
    (C0 C : Fin n → AuthState ψ) : Prop :=
  (cellAt ring g k C).core.state = .depart ∧
  (cellAt ring g k C).core.path = (cellAt ring g k C0).core.path ∧
  (∃ bit, (cellAt ring g k C).core.path = .some k bit) ∧
  (cellAt ring g k C).core.path2 = none ∧
  (cellAt ring g k C).path_mark = γ ∧
  (cellAt ring g k C).ctrl_mark = γ

/-- The processed interval is `[start,cur]`; all other block cells and every
cell outside the block still have their initial values. -/
def Inv (ring : DirectedRing n) (g start cur : Nat) (γ : ProvColor)
    (C0 C : Fin n → AuthState ψ) : Prop :=
  Std C ∧ Out ring ψ g C0 C ∧
  (∀ k, k < ψ → (k < start ∨ cur < k) → cellAt ring g k C = cellAt ring g k C0) ∧
  (∀ k, start ≤ k → k ≤ cur → DoneAt ring g k γ C0 C)

/-- A missing main path anywhere in the actual configuration. -/
def Hole (C : Fin n → AuthState ψ) : Prop :=
  ∃ i, (C i).core.path = .bot

private theorem right_ready (ring : DirectedRing n) (g start cur stop : Nat)
    (γ : ProvColor) (C0 C : Fin n → AuthState ψ)
    (hstart : start ≤ cur) (hcur : cur < stop) (hstop : stop < ψ - 1)
    (hI : Inv ring g start cur γ C0 C)
    (hR : ∀ k, start < k → k ≤ stop → ReadyAt ring g k γ C0) :
    ReadyAt ring g (cur + 1) γ C := by
  obtain ⟨_,_,hf,_⟩ := hI
  have he : cellAt ring g (cur + 1) C = cellAt ring g (cur + 1) C0 :=
    hf (cur + 1) (by omega) (Or.inr (by omega))
  change (cellAt ring g (cur + 1) C).core.state = .CHECK_ready ∧
    (∃ bit, (cellAt ring g (cur + 1) C).core.path = .some (cur + 1) bit) ∧
    (cellAt ring g (cur + 1) C).core.path2 = none ∧
    (cellAt ring g (cur + 1) C).path_mark = γ
  rw [he]
  exact hR (cur + 1) (by omega) (by omega)

/-- One actual internal edge advances the released prefix, unless it reaches
the ordinary leader/hole target. -/
theorem sweep_step (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start cur stop : Nat} {γ : ProvColor}
    {C0 C : Fin n → AuthState ψ}
    (hg : g * ψ + ψ ≤ n) (hstart : start ≤ cur) (hcur : cur < stop)
    (hstop : stop < ψ - 1)
    (hI : Inv ring g start cur γ C0 C)
    (hR : ∀ k, start < k → k ≤ stop → ReadyAt ring g k γ C0) :
    Rch hp κ cfg ring C 1
      (fun D => Hole D ∨ Inv ring g start (cur + 1) γ C0 D) := by
  obtain ⟨hS,hO,hFrame,hDone⟩ := hI
  have hk : cur + 1 < ψ := by omega
  have hL := hDone cur hstart (Nat.le_refl _)
  have hRt := right_ready ring g start cur stop γ C0 C hstart hcur hstop
    ⟨hS,hO,hFrame,hDone⟩ hR
  have hexL : ∃ bit, (cellAt ring g cur C).core.path = .some cur bit := hL.2.2.1
  have hexR : ∃ bit, (cellAt ring g (cur + 1) C).core.path = .some (cur + 1) bit := hRt.2.1
  let bl := Classical.choose hexL
  let br := Classical.choose hexR
  have hRow : ReadyBoundary (cellAt ring g cur C) (cellAt ring g (cur + 1) C)
      cur bl br := by
    rcases hL with ⟨hls,hlp,_,hlt,hlpm,hlcm⟩
    rcases hRt with ⟨hrs,_,hrt,hrpm⟩
    have hbl : (cellAt ring g cur C).core.path = .some cur bl := Classical.choose_spec hexL
    have hbr : (cellAt ring g (cur + 1) C).core.path = .some (cur + 1) br := Classical.choose_spec hexR
    have hloc := hS (bcell ring ψ g cur)
    have hroc := hS (bcell ring ψ g (cur + 1))
    have hkl : (cellAt ring g cur C).core.label.val = cur := by
      have hv := hloc.2.2
      rw [bcell_val ring hg (by omega), bcell_mod g cur (by omega)] at hv
      exact hv
    have hkr : (cellAt ring g (cur + 1) C).core.label.val = cur + 1 := by
      have hv := hroc.2.2
      rw [bcell_val ring hg hk, bcell_mod g (cur + 1) hk] at hv
      exact hv
    constructor
    · exact hkl
    · exact hkr
    · omega
    · exact hbl
    · exact hbr
    · exact hls
    · exact hrs
    · exact hlt
    · exact hrt
    · exact hloc.1
    · exact hroc.1
    · exact hloc.2.1
    · exact hroc.2.1
    · exact hrpm.trans hlpm.symm
    · exact hlcm.trans hlpm.symm
  apply Rch_mono hp κ cfg ring (Nat.le_refl _) _
    (step_block hp κ cfg ring hg hS hO hk)
  intro D hPost
  obtain ⟨hSD,hOD,e1,e2,eo⟩ := hPost
  have hq := ready_step hp κ (cellAt ring g cur C) (cellAt ring g (cur + 1) C)
    cur bl br hRow
  generalize hqdef : PPLLAuthF.pipeline hp κ cfg
    (cellAt ring g cur C) (cellAt ring g (cur + 1) C) = q at e1 e2 hq
  rcases hq with hTarget | hCont
  · left
    rcases hTarget with hLeadL | hTarget
    · have hf := (hSD (bcell ring ψ g cur)).1
      have he := congrArg (fun u : AuthState ψ => u.core.leader) e1
      cases (hf.symm.trans (he.trans hLeadL))
    rcases hTarget with hLeadR | hHole
    · have hf := (hSD (bcell ring ψ g (cur + 1))).1
      have he := congrArg (fun u : AuthState ψ => u.core.leader) e2
      cases (hf.symm.trans (he.trans hLeadR))
    rcases hHole with hHole | hHole
    · exact ⟨bcell ring ψ g cur,
        (congrArg (fun u : AuthState ψ => u.core.path) e1).trans hHole⟩
    · exact ⟨bcell ring ψ g (cur + 1),
        (congrArg (fun u : AuthState ψ => u.core.path) e2).trans hHole⟩
  · right
    rcases hCont.released with ⟨sl,sr,pl,pr,p2l,p2r,cl,cr,ml,mr⟩
    refine ⟨hSD,hOD,?_,?_⟩
    · intro k hk0 hk1
      have hOld : k < start ∨ cur < k := by rcases hk1 with h | h <;> omega
      change D (bcell ring ψ g k) = C0 (bcell ring ψ g k)
      rw [eo k hk0 (by omega) (by omega)]
      exact hFrame k hk0 hOld
    · intro k hs hc
      by_cases hkc : k = cur
      · subst k
        unfold DoneAt cellAt
        rw [e1]
        rcases hL with ⟨_,hOrigin,⟨bit,hbl⟩,_,hlpm,_⟩
        exact ⟨sl,pl.trans hOrigin,⟨bit,pl.trans hbl⟩,p2l,
          ml.trans hlpm,cl.trans (ml.trans hlpm)⟩
      · by_cases hkn : k = cur + 1
        · subst k
          unfold DoneAt cellAt
          rw [e2]
          rcases hRt with ⟨_,⟨br,hbr⟩,_,hrpm⟩
          have hOrig : cellAt ring g (cur + 1) C = cellAt ring g (cur + 1) C0 :=
            hFrame (cur + 1) (by omega) (Or.inr (by omega))
          have hOrigPath := congrArg (fun u : AuthState ψ => u.core.path) hOrig
          exact ⟨sr,pr.trans hOrigPath,⟨br,pr.trans hbr⟩,
            p2r,mr.trans hrpm,cr.trans (mr.trans hrpm)⟩
        · unfold DoneAt cellAt
          rw [eo k (by omega) hkc hkn]
          exact hDone k hs (by omega)

/-- A ready interval needs at most one original physical-edge service per
ready cell. A target may stop the word early; otherwise the entire interval
is lineage-depart and all unserved cells retain their input values. -/
theorem sweep_iter (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start stop : Nat} {γ : ProvColor}
    {C0 : Fin n → AuthState ψ}
    (hg : g * ψ + ψ ≤ n) (hstart : start < stop)
    (hstop : stop < ψ - 1) (hStd : Std C0)
    (hFirst : DoneAt ring g start γ C0 C0)
    (hReady : ∀ k, start < k → k ≤ stop → ReadyAt ring g k γ C0) :
    Rch hp κ cfg ring C0 (stop - start)
      (fun D => Hole D ∨ Inv ring g start stop γ C0 D) := by
  have hInit : Inv ring g start start γ C0 C0 := by
    refine ⟨hStd,?_,?_,?_⟩
    · intro i _; rfl
    · intro k _ _; rfl
    · intro k hs hk
      have : k = start := by omega
      subst k; exact hFirst
  have hiter : ∀ (d t : Nat) (C : Fin n → AuthState ψ),
      start ≤ t → t + d ≤ stop → Inv ring g start t γ C0 C →
      Rch hp κ cfg ring C d
        (fun D => Hole D ∨ Inv ring g start (t + d) γ C0 D) := by
    intro d
    induction d with
    | zero =>
        intro t C _ _ hI
        exact Rch_now hp κ cfg ring (Or.inr (by simpa using hI))
    | succ d ih =>
        intro t C hst htd hI
        have ht : t < stop := by omega
        have h1 := sweep_step hp κ ring hg hst ht hstop hI hReady
        have hb : Rch hp κ cfg ring C (1 + d)
            (fun D => Hole D ∨ Inv ring g start (t + 1 + d) γ C0 D) :=
          Rch_bind hp κ cfg ring h1 (fun D hD => by
          rcases hD with hHole | hInv
          · exact Rch_now hp κ cfg ring (L := d)
              (P := fun E => Hole E ∨ Inv ring g start (t + 1 + d) γ C0 E)
              (Or.inl hHole)
          · exact ih (t + 1) D (by omega) (by omega) hInv)
        have hlen : 1 + d = d + 1 := by omega
        have hpos : t + 1 + d = t + (d + 1) := by omega
        rw [hlen, hpos] at hb
        exact hb
  have h := hiter (stop - start) start C0 (Nat.le_refl _) (by omega) hInit
  apply Rch_mono hp κ cfg ring (Nat.le_refl _) _ h
  intro D hD
  have ht : start + (stop - start) = stop := by omega
  simpa [ht] using hD

#print axioms sweep_step
#print axioms sweep_iter

end PPLLAuthCheckReadySweep
