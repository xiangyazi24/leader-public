import Leader.Wu.Authorization.CheckReadySweep
import Leader.Wu.Authorization.CheckReadyVerdictRelease
-- PROVISIONAL supplied overlay 570e:
import Leader.Wu.Authorization.CheckUnsupportedWave
-- PROVISIONAL supplied overlay 9d6f:
import Leader.Wu.Authorization.CheckTerminalFamily
import Leader.Wu.Authorization.CheckTerminalWord

namespace PPLLAuthCheckSixSweep

open PPLL PPLLAuthF PPLLAuthCheckComponent PPLLAuthCheckComponentFrame
open PPLLAuthCheckComponentStep PPLLAuthGenDrain
open PPLLAuthCheckReadySweep (DoneAt Inv Hole)
open PPLLAuthCheckTerminalConsume
  (TerminalPending pipeline_terminal_pending_right_hole)
open PPLLAuthCheckTerminalMacro
  (authRun_one_left authRun_one_right authRun_one_other
   authRun_two_right authRun_two_other)
open PPLLAuthResetDrain (authRun)

set_option autoImplicit false

variable {n ψ : Nat}

private abbrev A (ring : DirectedRing n) (g k : Nat)
    (C : Fin n → AuthState ψ) : AuthState ψ := C (bcell ring ψ g k)

/-- Exactly six states; compare2 is deliberately absent. -/
def SixState (s : MainState) : Prop :=
  s = .CHECK_ready ∨ s = .equal ∨
    (s = .larger ∨ s = .less) ∨ (s = .lock ∨ s = .compare1)

def SixAt (ring : DirectedRing n) (g k : Nat) (γ : ProvColor)
    (C : Fin n → AuthState ψ) : Prop :=
  SixState (A ring g k C).core.state ∧
  (∃ bit, (A ring g k C).core.path = .some k bit) ∧
  (A ring g k C).core.path2 = none ∧ (A ring g k C).path_mark = γ

/-- Sources of the actual word lie in [lo,hi); affected cells lie in [lo,hi]. -/
def Span (ring : DirectedRing n) (ψ g lo hi : Nat) (w : List (Fin n)) : Prop :=
  ∀ e, e ∈ w → ∃ k, lo ≤ k ∧ k < hi ∧ e = bcell ring ψ g k

private theorem span_mono {ring : DirectedRing n} {g lo hi lo' hi' : Nat}
    {w : List (Fin n)} (h : Span ring ψ g lo hi w)
    (hl : lo' ≤ lo) (hh : hi ≤ hi') : Span ring ψ g lo' hi' w := by
  intro e he
  obtain ⟨k,hk,ht,eq⟩ := h e he
  exact ⟨k,by omega,by omega,eq⟩

private theorem span_append {ring : DirectedRing n} {g lo hi : Nat}
    {u v : List (Fin n)} (hu : Span ring ψ g lo hi u)
    (hv : Span ring ψ g lo hi v) : Span ring ψ g lo hi (u ++ v) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hu e he
  · exact hv e he

private theorem run_other (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (i : Fin n) : ∀ w : List (Fin n),
    (∀ e, e ∈ w → i ≠ e ∧ i ≠ ring.rightNeighbor e) →
    ∀ C : Fin n → AuthState ψ, (authRun hp κ cfg ring C w) i = C i := by
  intro w
  induction w with
  | nil => intro _ C; rfl
  | cons e w ih =>
    intro h C
    have h0 := h e (by simp)
    have ht : ∀ f, f ∈ w → i ≠ f ∧ i ≠ ring.rightNeighbor f := by
      intro f hf
      exact h f (by simp [hf])
    change (authRun hp κ cfg ring C ([e] ++ w)) i = C i
    rw [authRun_app]
    exact (ih ht (authRun hp κ cfg ring C [e])).trans
      (authRun_one_other hp κ cfg ring C e i h0.1 h0.2)

/-- Whole-state frame, independent of whether the word reaches a target. -/
theorem word_frame (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g lo hi : Nat} {w : List (Fin n)}
    (hg : g * ψ + ψ ≤ n) (hhi : hi < ψ)
    (hw : Span ring ψ g lo hi w) (C : Fin n → AuthState ψ) :
    Out ring ψ g C (authRun hp κ cfg ring C w) ∧
    (∀ k, k < ψ → (k < lo ∨ hi < k) →
      A ring g k (authRun hp κ cfg ring C w) = A ring g k C) := by
  constructor
  · intro i ho
    refine run_other hp κ ring i w ?_ C
    intro e he
    obtain ⟨k,_,hk,rfl⟩ := hw e he
    refine ⟨ho k (by omega),?_⟩
    rw [rn_bcell]
    exact ho (k+1) (by omega)
  · intro k hk ho
    refine run_other hp κ ring (bcell ring ψ g k) w ?_ C
    intro e he
    obtain ⟨j,hj,hj',rfl⟩ := hw e he
    refine ⟨bcell_ne ring hg hk (by omega)
      (by rcases ho with h | h <;> omega),?_⟩
    rw [rn_bcell]
    exact bcell_ne ring hg hk (by omega)
      (by rcases ho with h | h <;> omega)

private theorem target_global (C : Fin n → AuthState ψ) (a b : Fin n)
    (h : Target (C a,C b)) : Ldr C ∨ Hole C := by
  rcases h with hl | hr | hh
  · exact Or.inl ⟨a,hl⟩
  · exact Or.inl ⟨b,hr⟩
  · rcases hh with hl | hr
    · exact Or.inr ⟨a,hl⟩
    · exact Or.inr ⟨b,hr⟩

/-- Lift the existing Continuing record through the physical two-cell update. -/
private theorem advance_inv (ring : DirectedRing n)
    {g start t br : Nat} {γ : ProvColor}
    {C0 C D : Fin n → AuthState ψ}
    (hg : g * ψ + ψ ≤ n) (hs : start ≤ t) (hk : t+1 < ψ)
    (hI : Inv ring g start t γ C0 C)
    (rp : (A ring g (t+1) C).core.path = .some (t+1) br)
    (rm : (A ring g (t+1) C).path_mark = γ)
    (hc : Continuing (A ring g t C) (A ring g (t+1) C)
      (A ring g t D,A ring g (t+1) D))
    (hf : ∀ i, i ≠ bcell ring ψ g t → i ≠ bcell ring ψ g (t+1) → D i = C i) :
    Inv ring g start (t+1) γ C0 D := by
  obtain ⟨hS,hO,hF,hDone⟩ := hI
  rcases hc.released with ⟨sl,sr,pl,pr,tl,tr,cl,cr,ml,mr⟩
  have other : ∀ k, k < ψ → k ≠ t → k ≠ t+1 → A ring g k D = A ring g k C := by
    intro k hkp hkt hk1
    exact hf _ (bcell_ne ring hg hkp (by omega) hkt)
      (bcell_ne ring hg hkp hk hk1)
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i = bcell ring ψ g t
    · subst i
      exact ⟨hc.left_follower,hc.left_reset,
        (congrArg Fin.val hc.left_label).trans (hS _).2.2⟩
    · by_cases hj : i = bcell ring ψ g (t+1)
      · subst i
        exact ⟨hc.right_follower,hc.right_reset,
          (congrArg Fin.val hc.right_label).trans (hS _).2.2⟩
      · rw [hf i hi hj]
        exact hS i
  · intro i hi
    rw [hf i (hi t (by omega)) (hi (t+1) hk)]
    exact hO i hi
  · intro k hkp ho
    have hkt : k ≠ t := by rcases ho with h | h <;> omega
    have hk1 : k ≠ t+1 := by rcases ho with h | h <;> omega
    exact (other k hkp hkt hk1).trans
      (hF k hkp (by rcases ho with h | h <;> omega))
  · intro k hsk hkt
    by_cases he : k = t
    · subst k
      rcases hDone t hs (Nat.le_refl _) with ⟨_,hor,⟨bl,hp⟩,_,hm,_⟩
      exact ⟨sl,pl.trans hor,⟨bl,pl.trans hp⟩,tl,
        ml.trans hm,cl.trans (ml.trans hm)⟩
    · by_cases he' : k = t+1
      · subst k
        have hor := hF (t+1) hk (Or.inr (by omega))
        exact ⟨sr,pr.trans (congrArg (fun u : AuthState ψ => u.core.path) hor),
          ⟨br,pr.trans rp⟩,tr,mr.trans rm,cr.trans (mr.trans rm)⟩
      · change (A ring g k D).core.state = .depart ∧
          (A ring g k D).core.path = (A ring g k C0).core.path ∧
          (∃ bit, (A ring g k D).core.path = .some k bit) ∧
          (A ring g k D).core.path2 = none ∧
          (A ring g k D).path_mark = γ ∧ (A ring g k D).ctrl_mark = γ
        rw [other k (by omega) he he']
        exact hDone k hsk (by omega)

private theorem one_step (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start t : Nat} {γ : ProvColor} {C0 C : Fin n → AuthState ψ}
    (hg : g * ψ + ψ ≤ n) (hs : start ≤ t) (hi : t+1 < ψ-1)
    (hI : Inv ring g start t γ C0 C) (hR : SixAt ring g (t+1) γ C) :
    let D := authRun hp κ cfg ring C [bcell ring ψ g t]
    Ldr D ∨ Hole D ∨ Inv ring g start (t+1) γ C0 D := by
  have hk : t+1 < ψ := by omega
  let a := bcell ring ψ g t
  let b := bcell ring ψ g (t+1)
  let D := authRun hp κ cfg ring C [a]
  have row := std_row ring hg hk hI.1
  rcases hI.2.2.2 t hs (Nat.le_refl _) with ⟨ls,_,⟨bl,lp⟩,lt,lm,lc⟩
  rcases hR with ⟨rs,⟨br,rp⟩,rt,rm⟩
  have hq : Target (PPLLAuthF.pipeline hp κ cfg (C a) (C b)) ∨
      Continuing (C a) (C b) (PPLLAuthF.pipeline hp κ cfg (C a) (C b)) := by
    rcases rs with hr | he | hv | hw
    · exact ready_step hp κ (C a) (C b) t bl br
        ⟨row.lk,row.rk,by omega,lp,rp,ls,hr,lt,rt,row.ll,row.rl,
          row.lr,row.rr,rm.trans lm.symm,lc.trans lm.symm⟩
    · exact PPLLAuthCheckComponentEqual.equal_step hp κ (C a) (C b) t bl br
        ⟨row.lk,row.rk,by omega,lp,rp,ls,he,lt,rt,row.ll,row.rl,
          row.lr,row.rr,rm.trans lm.symm,lc.trans lm.symm⟩
    · exact PPLLAuthCheckComponentVerdict.verdict_step hp κ (C a) (C b) t bl br
        ⟨row.lk,row.rk,by omega,lp,rp,ls,hv,lt,rt,row.ll,row.rl,
          row.lr,row.rr,rm.trans lm.symm,lc.trans lm.symm⟩
    · exact PPLLAuthCheckUnsupportedWave.unsupported_wave_step
        hp κ (C a) (C b) t bl br γ
        ⟨row.lk,row.rk,by omega,lp,rp,ls,hw,lt,rt,row.ll,row.rl,
          row.lr,row.rr,lm,rm,lc.trans lm.symm⟩
  have hn : 1 < n := by omega
  have hnext : ring.rightNeighbor a = b := rn_bcell ring g t
  have el := authRun_one_left hp κ cfg ring C a
  have er := authRun_one_right hp κ cfg ring hn C a
  rw [hnext] at el er
  generalize PPLLAuthF.pipeline hp κ cfg (C a) (C b) = q at hq el er
  change D a = q.1 at el
  change D b = q.2 at er
  have hpair : Target (D a,D b) ∨ Continuing (C a) (C b) (D a,D b) := by
    rw [el,er]
    exact hq
  have hf : ∀ i, i ≠ a → i ≠ b → D i = C i := by
    intro i hia hib
    exact authRun_one_other hp κ cfg ring C a i hia
      (by simpa only [hnext] using hib)
  rcases hpair with ht | hc
  · rcases target_global D a b ht with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (advance_inv ring hg hs hk hI rp rm hc hf))

private theorem sweep_aux (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start stop : Nat} {γ : ProvColor} {C0 : Fin n → AuthState ψ}
    (hg : g * ψ + ψ ≤ n) (hstop : stop < ψ-1)
    (hSix : ∀ k, start < k → k ≤ stop → SixAt ring g k γ C0) :
    ∀ (d t : Nat) (C : Fin n → AuthState ψ), start ≤ t → t+d ≤ stop →
      Inv ring g start t γ C0 C →
      ∃ w : List (Fin n), w.length ≤ d ∧ Span ring ψ g t (t+d) w ∧
        (Ldr (authRun hp κ cfg ring C w) ∨ Hole (authRun hp κ cfg ring C w) ∨
          Inv ring g start (t+d) γ C0 (authRun hp κ cfg ring C w)) := by
  intro d
  induction d with
  | zero =>
    intro t C _ _ hI
    refine ⟨[],by simp,?_,Or.inr (Or.inr (by simpa [authRun] using hI))⟩
    intro e he
    cases he
  | succ d ih =>
    intro t C hst htd hI
    let e := bcell ring ψ g t
    let D := authRun hp κ cfg ring C [e]
    have he := hI.2.2.1 (t+1) (by omega) (Or.inr (by omega))
    have hR : SixAt ring g (t+1) γ C := by
      change A ring g (t+1) C = A ring g (t+1) C0 at he
      unfold SixAt
      rw [he]
      exact hSix (t+1) (by omega) (by omega)
    have hs := one_step hp κ ring hg hst (by omega) hI hR
    change Ldr D ∨ Hole D ∨ Inv ring g start (t+1) γ C0 D at hs
    have hsingle : Span ring ψ g t (t+(d+1)) [e] := by
      intro f hf
      have hfe : f = e := by simpa using hf
      subst f
      exact ⟨t,Nat.le_refl _,by omega,rfl⟩
    rcases hs with hl | hh | hJ
    · exact ⟨[e],by simp,hsingle,Or.inl hl⟩
    · exact ⟨[e],by simp,hsingle,Or.inr (Or.inl hh)⟩
    · obtain ⟨w,hw,hW,hout⟩ := ih (t+1) D (by omega) (by omega) hJ
      refine ⟨[e] ++ w,?_,span_append hsingle
        (span_mono hW (by omega) (by omega)),?_⟩
      · simp only [List.length_append,List.length_cons,List.length_nil]
        omega
      · rw [authRun_app]
        have hpos : t+1+d = t+(d+1) := by omega
        simpa only [hpos] using hout

/-- Strict untouched suffix remains available for the terminal producer. -/
theorem sweep_word (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start stop : Nat} {γ : ProvColor} {C0 : Fin n → AuthState ψ}
    (hg : g * ψ + ψ ≤ n) (hs : start ≤ stop) (ht : stop < ψ-1)
    (hS : Std C0) (hA : DoneAt ring g start γ C0 C0)
    (hSix : ∀ k, start < k → k ≤ stop → SixAt ring g k γ C0) :
    ∃ w : List (Fin n), w.length ≤ stop-start ∧ Span ring ψ g start stop w ∧
      (Ldr (authRun hp κ cfg ring C0 w) ∨ Hole (authRun hp κ cfg ring C0 w) ∨
        Inv ring g start stop γ C0 (authRun hp κ cfg ring C0 w)) := by
  have hI : Inv ring g start start γ C0 C0 := by
    refine ⟨hS,?_,?_,?_⟩
    · intro i _; rfl
    · intro k _ _; rfl
    · intro k hsk hks
      have he : k = start := by omega
      subst k
      exact hA
  have h := sweep_aux hp κ ring hg ht hSix (stop-start) start C0
    (Nat.le_refl _) (by omega) hI
  have he : start+(stop-start) = stop := by omega
  simpa only [he] using h

theorem sweep_iter (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start stop : Nat} {γ : ProvColor} {C0 : Fin n → AuthState ψ}
    (hg : g * ψ + ψ ≤ n) (hs : start ≤ stop) (ht : stop < ψ-1)
    (hS : Std C0) (hA : DoneAt ring g start γ C0 C0)
    (hSix : ∀ k, start < k → k ≤ stop → SixAt ring g k γ C0) :
    Rch hp κ cfg ring C0 (stop-start)
      (fun D => Hole D ∨ Inv ring g start stop γ C0 D) := by
  obtain ⟨w,hw,_,ho⟩ := sweep_word hp κ ring hg hs ht hS hA hSix
  exact ⟨w,hw,ho⟩

/-- TerminalMacro's same-edge construction, with the six-state producer. -/
theorem terminal_six_word (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    (hn : 1 < n) (C : Fin n → AuthState ψ) (e : Fin n) (bl br : Nat)
    (h : PPLLAuthCheckTerminalReady.TerminalReady (C e) (C (ring.rightNeighbor e)) bl br ∨
      PPLLAuthCheckTerminalFamily.Boundary (C e) (C (ring.rightNeighbor e)) bl br) :
    ∃ w : List (Fin n), (w = [e] ∨ w = [e,e]) ∧ w.length ≤ 2 ∧
      (∀ i, i ≠ e → i ≠ ring.rightNeighbor e → (authRun hp κ cfg ring C w) i = C i) ∧
      (Target ((authRun hp κ cfg ring C w) e,
        (authRun hp κ cfg ring C w) (ring.rightNeighbor e)) ∨
       (w = [e] ∧ Continuing (C e) (C (ring.rightNeighbor e))
         ((authRun hp κ cfg ring C w) e,
          (authRun hp κ cfg ring C w) (ring.rightNeighbor e)))) := by
  have hq := PPLLAuthCheckTerminalFamily.terminal_step
    hp κ (C e) (C (ring.rightNeighbor e)) bl br h
  have el := authRun_one_left hp κ cfg ring C e
  have er := authRun_one_right hp κ cfg ring hn C e
  generalize PPLLAuthF.pipeline hp κ cfg (C e) (C (ring.rightNeighbor e)) = q at hq el er
  rcases hq with ht | hc | he
  · refine ⟨[e],Or.inl rfl,by simp,?_,Or.inl ?_⟩
    · intro i hia hib
      exact authRun_one_other hp κ cfg ring C e i hia hib
    · rw [el,er]
      exact ht
  · refine ⟨[e],Or.inl rfl,by simp,?_,Or.inr ⟨rfl,?_⟩⟩
    · intro i hia hib
      exact authRun_one_other hp κ cfg ring C e i hia hib
    · rw [el,er]
      exact hc
  · have hh := pipeline_terminal_pending_right_hole hp κ q.1 q.2 bl br he
    have hpR : ((authRun hp κ cfg ring C [e,e]) (ring.rightNeighbor e)).core.path = .bot := by
      rw [authRun_two_right hp κ cfg ring hn C e,el,er]
      exact hh
    refine ⟨[e,e],Or.inr rfl,by simp,?_,Or.inl ?_⟩
    · intro i hia hib
      exact authRun_two_other hp κ cfg ring C e i hia hib
    · exact Or.inr (Or.inr (Or.inr hpR))

private theorem terminal_from_inv (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start : Nat} {γ : ProvColor} {C0 C : Fin n → AuthState ψ}
    (hwidth : 2 ≤ ψ) (hg : g * ψ + ψ ≤ n) (hs : start ≤ ψ-2)
    (hI : Inv ring g start (ψ-2) γ C0 C) (hT : SixAt ring g (ψ-1) γ C0) :
    ∃ w : List (Fin n), w.length ≤ 2 ∧ Span ring ψ g (ψ-2) (ψ-1) w ∧
      (Ldr (authRun hp κ cfg ring C w) ∨ Hole (authRun hp κ cfg ring C w) ∨
        Inv ring g start (ψ-1) γ C0 (authRun hp κ cfg ring C w)) := by
  have hadd : ψ-2+1 = ψ-1 := by omega
  have hk : ψ-2+1 < ψ := by omega
  let a := bcell ring ψ g (ψ-2)
  let b := bcell ring ψ g (ψ-1)
  have hnext : ring.rightNeighbor a = b := by
    dsimp only [a,b]
    rw [rn_bcell,hadd]
  have hor := hI.2.2.1 (ψ-1) (by omega) (Or.inr (by omega))
  have hR : SixAt ring g (ψ-1) γ C := by
    change A ring g (ψ-1) C = A ring g (ψ-1) C0 at hor
    unfold SixAt
    rw [hor]
    exact hT
  rcases hI.2.2.2 (ψ-2) hs (Nat.le_refl _) with ⟨ls,_,⟨bl,lp⟩,lt,lm,lc⟩
  rcases hR with ⟨rs,⟨br,rp⟩,rt,rm⟩
  have row := std_row ring hg hk hI.1
  rw [hadd] at row
  have hrs : (C b).core.state = .CHECK_ready ∨
      PPLLAuthCheckTerminalFamily.FamilyState (C b).core.state := by
    simpa only [SixState,PPLLAuthCheckTerminalFamily.FamilyState,or_assoc] using rs
  have ht : PPLLAuthCheckTerminalReady.TerminalReady (C a) (C b) bl br ∨
      PPLLAuthCheckTerminalFamily.Boundary (C a) (C b) bl br := by
    rcases hrs with hr | hr
    · exact Or.inl ⟨hwidth,row.lk,row.rk.trans hadd,lp,rp,ls,hr,lt,rt,
        row.ll,row.rl,row.lr,row.rr,rm.trans lm.symm,lc.trans lm.symm⟩
    · exact Or.inr ⟨hwidth,row.lk,row.rk.trans hadd,lp,rp,ls,hr,lt,rt,
        row.ll,row.rl,row.lr,row.rr,rm.trans lm.symm,lc.trans lm.symm⟩
  obtain ⟨w,hshape,hlen,hf,hout⟩ := terminal_six_word hp κ ring (by omega) C a bl br
    (by simpa only [hnext] using ht)
  rw [hnext] at hf hout
  have hspan : Span ring ψ g (ψ-2) (ψ-1) w := by
    intro e he
    have heq : e = a := by
      rcases hshape with hw | hw <;> simpa [hw] using he
    subst e
    exact ⟨ψ-2,Nat.le_refl _,by omega,rfl⟩
  refine ⟨w,hlen,hspan,?_⟩
  generalize authRun hp κ cfg ring C w = D at hf hout ⊢
  rcases hout with ht | ⟨_,hc⟩
  · rcases target_global D a b ht with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have ha := advance_inv ring hg hs hk hI
      (by simpa only [hadd] using rp) (by simpa only [hadd] using rm)
      (by simpa only [hadd] using hc) (by simpa only [hadd] using hf)
    exact Or.inr (Or.inr (by simpa only [hadd] using ha))

private theorem progress_raw (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start : Nat} {γ : ProvColor} {C0 : Fin n → AuthState ψ}
    (hwidth : 2 ≤ ψ) (hg : g * ψ + ψ ≤ n) (hs : start ≤ ψ-2)
    (hS : Std C0) (hA : DoneAt ring g start γ C0 C0)
    (hSix : ∀ k, start < k → k < ψ → SixAt ring g k γ C0) :
    ∃ w : List (Fin n), w.length ≤ (ψ-2-start)+2 ∧ Span ring ψ g start (ψ-1) w ∧
      (Ldr (authRun hp κ cfg ring C0 w) ∨ Hole (authRun hp κ cfg ring C0 w) ∨
        Inv ring g start (ψ-1) γ C0 (authRun hp κ cfg ring C0 w)) := by
  obtain ⟨u,hu,su,hout⟩ := sweep_word hp κ ring hg hs (by omega) hS hA
    (fun k hk hk' => hSix k hk (by omega))
  rcases hout with hl | hh | hI
  · exact ⟨u,by omega,span_mono su (Nat.le_refl _) (by omega),Or.inl hl⟩
  · exact ⟨u,by omega,span_mono su (Nat.le_refl _) (by omega),Or.inr (Or.inl hh)⟩
  · obtain ⟨v,hv,sv,hend⟩ := terminal_from_inv hp κ ring hwidth hg hs hI
      (hSix (ψ-1) (by omega) (by omega))
    refine ⟨u ++ v,?_,?_,?_⟩
    · rw [List.length_append]
      omega
    · exact span_append (span_mono su (Nat.le_refl _) (by omega))
        (span_mono sv hs (Nat.le_refl _))
    · rw [authRun_app]
      exact hend

/-- Actual population word; outside/pre-start frames hold even at a target. -/
theorem six_terminal_word (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start : Nat} {γ : ProvColor} {C0 : Fin n → AuthState ψ}
    (hwidth : 2 ≤ ψ) (hg : g * ψ + ψ ≤ n) (hs : start ≤ ψ-2)
    (hS : Std C0) (hA : DoneAt ring g start γ C0 C0)
    (hSix : ∀ k, start < k → k < ψ → SixAt ring g k γ C0) :
    ∃ w : List (Fin n), w.length ≤ (ψ-2-start)+2 ∧ Span ring ψ g start (ψ-1) w ∧
      Out ring ψ g C0 (authRun hp κ cfg ring C0 w) ∧
      (∀ k, k < ψ → (k < start ∨ ψ-1 < k) →
        A ring g k (authRun hp κ cfg ring C0 w) = A ring g k C0) ∧
      (Ldr (authRun hp κ cfg ring C0 w) ∨ Hole (authRun hp κ cfg ring C0 w) ∨
        Inv ring g start (ψ-1) γ C0 (authRun hp κ cfg ring C0 w)) := by
  obtain ⟨w,hw,hspan,ho⟩ := progress_raw hp κ ring hwidth hg hs hS hA hSix
  have hf := word_frame hp κ ring hg (by omega : ψ-1 < ψ) hspan C0
  exact ⟨w,hw,hspan,hf.1,hf.2,ho⟩

/-- Existing Rch/Inv interface, with no cleanliness or interleaving assumption. -/
theorem six_terminal_progress (hp : ψ > 0) (κ : Nat) (ring : DirectedRing n)
    {g start : Nat} {γ : ProvColor} {C0 : Fin n → AuthState ψ}
    (hwidth : 2 ≤ ψ) (hg : g * ψ + ψ ≤ n) (hs : start ≤ ψ-2)
    (hS : Std C0) (hA : DoneAt ring g start γ C0 C0)
    (hSix : ∀ k, start < k → k < ψ → SixAt ring g k γ C0) :
    Rch hp κ cfg ring C0 ((ψ-2-start)+2)
      (fun D => Hole D ∨ Inv ring g start (ψ-1) γ C0 D) := by
  obtain ⟨w,hw,_,_,_,ho⟩ := six_terminal_word hp κ ring hwidth hg hs hS hA hSix
  exact ⟨w,hw,ho⟩

/-- A source assignment, not a generator-reachability claim. -/
def fixture4 (i : Fin 4) : AuthState 4 :=
  { core :=
      { leader := false, probe := false, phase := false, bit := false,
        wait := true,
        state := if i.val = 0 then .depart else if i.val = 1 then .larger
          else if i.val = 2 then .lock else .compare1,
        path := .some i.val 0, reset := false, carry := false, count := 0,
        label := i, h_field := false, path2 := none, path3 := none,
        path4 := none, path5 := none, p := false, p_carry := false,
        reset_cmd := false, echo := false, signal_B := 0, bullet := 0,
        shield := false, write_state := .none, write := .none,
        last := false, last_set := false, last_unset := false,
        b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false },
    path_mark := 0, ctrl_mark := if i.val = 0 then 0 else 2,
    path2_scope := .session, path2_mark := 2, path4_mark := 0, path5_mark := 0 }

theorem fixture4_std : Std fixture4 := by
  intro i
  exact ⟨rfl,rfl,(Nat.mod_eq_of_lt i.isLt).symm⟩

theorem fixture4_entrance (ring : DirectedRing 4) :
    Std fixture4 ∧ DoneAt ring 0 0 0 fixture4 fixture4 ∧
    (∀ k, 0 < k → k < 4 → SixAt ring 0 k 0 fixture4) := by
  refine ⟨fixture4_std,?_,?_⟩
  · exact ⟨rfl,rfl,⟨0,rfl⟩,rfl,rfl,rfl⟩
  · intro k hk hk'
    have he : k = 1 ∨ k = 2 ∨ k = 3 := by omega
    have hv3 : (3 : Fin 4).val = 3 := rfl
    rcases he with rfl | rfl | rfl <;>
      simp [SixAt,SixState,A,bcell,fixture4,hv3]

theorem fixture4_progress (κ : Nat) (ring : DirectedRing 4) :
    Rch (by omega : 4 > 0) κ cfg ring fixture4 4
      (fun D => Hole D ∨ Inv ring 0 0 3 0 fixture4 D) := by
  obtain ⟨hs,ha,hr⟩ := fixture4_entrance ring
  exact six_terminal_progress (by omega) κ ring
    (g := 0) (start := 0) (γ := 0) (by omega) (by omega) (by omega) hs ha hr

#print axioms PPLLAuthCheckUnsupportedWave.unsupported_wave_step
#print axioms PPLLAuthCheckTerminalFamily.terminal_step
#print axioms word_frame
#print axioms sweep_iter
#print axioms terminal_six_word
#print axioms six_terminal_word
#print axioms six_terminal_progress
#print axioms fixture4_entrance
#print axioms fixture4_progress

end PPLLAuthCheckSixSweep
