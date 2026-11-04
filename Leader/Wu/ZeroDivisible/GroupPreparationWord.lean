import Leader.Wu.ZeroDivisible.PenultimatePreparationRows
import Leader.Wu.ZeroDivisible.InternalPreparationRows
import Leader.Wu.ZeroDivisible.TerminalDrain
import Leader.Wu.ZeroDivisible.ResetDrain

/-!
# Actual bounded preparation of a selected physical group

The row contracts are instantiated from the frozen full-pipeline theorems.
A stopped forward/reverse induction carries original holder paths and empty
comparison slots, without any ancillary-field invariant. Terminal carry E
uses one immediate D1 row; its early stop fits the same total word bound.
-/
namespace PPLLAstraR5PrepWord
open PPLL PPLLAstraR5Repair PPLLAstraR5ResetDrain
set_option autoImplicit false

/-- Total local-to-physical index map; all scheduled indices lie below psi. -/
def cell {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q) (j : Nat) : Fin (q*ψ) :=
  ⟨(g.val*ψ+j)%(q*ψ),Nat.mod_lt _ ring.hn⟩

private theorem cell_bound {q ψ : Nat} (g : Fin q) {j : Nat} (hj : j < ψ) :
    g.val*ψ+j < q*ψ := by
  have hg : g.val+1 ≤ q := by omega
  have hm := Nat.mul_le_mul_right ψ hg
  simp only [Nat.add_mul,Nat.one_mul] at hm
  omega
private theorem cell_val {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    {j : Nat} (hj : j < ψ) : (cell ring g j).val = g.val*ψ+j := by
  simp only [cell,Nat.mod_eq_of_lt (cell_bound g hj)]
private theorem cell_inj {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    {i j : Nat} (hi : i < ψ) (hj : j < ψ) (h : cell ring g i = cell ring g j) : i=j := by
  have he := congrArg Fin.val h
  rw [cell_val ring g hi,cell_val ring g hj] at he
  omega
private theorem cell_next {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    {i : Nat} (hi : i+1 < ψ) : ring.rightNeighbor (cell ring g i) = cell ring g (i+1) := by
  apply Fin.ext
  change ((cell ring g i).val+1)%(q*ψ) = (cell ring g (i+1)).val
  rw [cell_val ring g (by omega),cell_val ring g hi]
  have hb := cell_bound g hi
  simpa [Nat.add_assoc] using Nat.mod_eq_of_lt hb

/-- An observed global leader or main-path hole is a stopping target. -/
def Target {n ψ : Nat} (C : Fin n → AgentState ψ) : Prop :=
  (∃ x,(C x).leader=true) ∨ ∃ x,(C x).path=.bot

/-- Entrance shape of the selected group, with arbitrary path payloads. -/
def OwnTF {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (C : Fin (q*ψ) → AgentState ψ) : Prop :=
  ∀ j,j<ψ → (C (cell ring g j)).label.val=j ∧
    (∃ b,(C (cell ring g j)).path=.some j b) ∧ (C (cell ring g j)).path2=none

/-- Exact original holder labels and paths, with token-free selected slots. -/
def Frame {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (C0 C : Fin (q*ψ) → AgentState ψ) : Prop :=
  ∀ j,j<ψ → (C (cell ring g j)).label=(C0 (cell ring g j)).label ∧
    (C (cell ring g j)).path=(C0 (cell ring g j)).path ∧ (C (cell ring g j)).path2=none

/-- Basin B only constrains the selected block; other physical cells are raw. -/
def Basin {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (C : Fin (q*ψ) → AgentState ψ) : Prop :=
  OwnTF ring g C ∧ PrepInternal.Locked (C (cell ring g 0)).state ∧
  (∀ j,1≤j → j<ψ-2 → PrepInternal.Mid (C (cell ring g j)).state) ∧
  PrepRows.PenState (C (cell ring g (ψ-2))).state ∧
  (C (cell ring g (ψ-1))).state=.compare2

/-- The selected block is C1 throughout its nonterminal prefix and C2 at its
terminal, with exact entrance holder paths and token-free slots. -/
def Prepared {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (C0 C : Fin (q*ψ) → AgentState ψ) : Prop :=
  Frame ring g C0 C ∧
  (∀ j,j<ψ-1 → (C (cell ring g j)).state=.compare1) ∧
  (C (cell ring g (ψ-1))).state=.compare2

/-- Every scheduled edge lies wholly inside the selected physical group. -/
def InternalWord {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (w : List (Fin (q*ψ))) : Prop :=
  ∀ e, e ∈ w → ∃ j, j+1<ψ ∧ e=cell ring g j

/-- A physical cell outside the selected group. -/
def Outside {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (x : Fin (q*ψ)) : Prop :=
  ∀ j, j<ψ → x≠cell ring g j

private def Forward {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (C0 : Fin (q*ψ) → AgentState ψ) (k : Nat) (C : Fin (q*ψ) → AgentState ψ) : Prop :=
  Frame ring g C0 C ∧ (C (cell ring g (ψ-1))).state=.compare2 ∧
  (∀ j,j≤ψ-2 → j≤k → PrepInternal.Locked (C (cell ring g j)).state) ∧
  (∀ j,j≤ψ-2 → k<j → PrepInternal.Mid (C (cell ring g j)).state)
private def Reverse {q ψ : Nat} (ring : DirectedRing (q*ψ)) (g : Fin q)
    (C0 : Fin (q*ψ) → AgentState ψ) (k : Nat) (C : Fin (q*ψ) → AgentState ψ) : Prop :=
  Frame ring g C0 C ∧ (C (cell ring g (ψ-1))).state=.compare2 ∧
  (∀ j,j<ψ-2-k → PrepInternal.Locked (C (cell ring g j)).state) ∧
  (∀ j,ψ-2-k≤j → j≤ψ-2 → (C (cell ring g j)).state=.compare1)

private theorem followers {n ψ : Nat} {C : Fin n → AgentState ψ} (h : ¬ Target C)
    (x : Fin n) : (C x).leader=false := by
  cases he : (C x).leader
  · rfl
  · exact False.elim (h (Or.inl ⟨x,he⟩))
private theorem frame_self {q ψ : Nat} {ring : DirectedRing (q*ψ)} {g : Fin q}
    {C : Fin (q*ψ) → AgentState ψ} (h : OwnTF ring g C) : Frame ring g C C := by
  intro j hj
  exact ⟨rfl,rfl,(h j hj).2.2⟩
private theorem frame_own {q ψ : Nat} {ring : DirectedRing (q*ψ)} {g : Fin q}
    {C0 C : Fin (q*ψ) → AgentState ψ} (h0 : OwnTF ring g C0)
    (h : Frame ring g C0 C) : OwnTF ring g C := by
  intro j hj
  rcases h0 j hj with ⟨hlab,⟨b,hp⟩,ht⟩
  rcases h j hj with ⟨hlabel,hpath,htoken⟩
  exact ⟨by rw [hlabel]; exact hlab,⟨b,hpath.trans hp⟩,htoken⟩

private abbrev edgeStep {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (i : Nat)
    (C : Fin (q*ψ) → AgentState ψ) := (protocol hp κ c).step ring C (cell ring g i)

private theorem step_left {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) {i : Nat} (hi : i+1<ψ)
    (C : Fin (q*ψ) → AgentState ψ) :
    edgeStep hp κ c ring g i C (cell ring g i) =
      (pipeline hp κ c (C (cell ring g i)) (C (cell ring g (i+1)))).1 := by
  simp [edgeStep,PPLLAstraR5ResetDrain.protocol,PopulationProtocol.step,cell_next ring g hi]
private theorem step_right {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) {i : Nat} (hi : i+1<ψ)
    (C : Fin (q*ψ) → AgentState ψ) :
    edgeStep hp κ c ring g i C (cell ring g (i+1)) =
      (pipeline hp κ c (C (cell ring g i)) (C (cell ring g (i+1)))).2 := by
  have hn : cell ring g (i+1) ≠ cell ring g i := by
    intro he; have := cell_inj ring g hi (by omega) he; omega
  simp [edgeStep,PPLLAstraR5ResetDrain.protocol,PopulationProtocol.step,cell_next ring g hi,hn]
private theorem step_other {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) {i j : Nat}
    (hi : i+1<ψ) (hj : j<ψ) (hji : j≠i) (hjr : j≠i+1)
    (C : Fin (q*ψ) → AgentState ψ) :
    edgeStep hp κ c ring g i C (cell ring g j) = C (cell ring g j) := by
  have he : cell ring g j ≠ cell ring g i := fun h => hji (cell_inj ring g hj (by omega) h)
  have hr : cell ring g j ≠ cell ring g (i+1) := fun h => hjr (cell_inj ring g hj hi h)
  simp [edgeStep,PPLLAstraR5ResetDrain.protocol,PopulationProtocol.step,cell_next ring g hi,he,hr]

private theorem step_frame {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) {i : Nat} (hi : i+1<ψ)
    (C0 C : Fin (q*ψ) → AgentState ψ) (h : Frame ring g C0 C)
    (hf : PrepRows.ExactFrame (C (cell ring g i)) (C (cell ring g (i+1)))
      (pipeline hp κ c (C (cell ring g i)) (C (cell ring g (i+1))))) :
    Frame ring g C0 (edgeStep hp κ c ring g i C) := by
  intro j hj
  by_cases hl : j=i
  · subst j
    rw [step_left hp κ c ring g hi]
    exact ⟨hf.1.trans (h i (by omega)).1,hf.2.2.1.trans (h i (by omega)).2.1,hf.2.2.2.2.1⟩
  by_cases hr : j=i+1
  · subst j
    rw [step_right hp κ c ring g hi]
    exact ⟨hf.2.1.trans (h (i+1) hi).1,hf.2.2.2.1.trans (h (i+1) hi).2.1,hf.2.2.2.2.2⟩
  rw [step_other hp κ c ring g hi hj hl hr]
  exact h j hj

private theorem pair_hole_target {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) {i : Nat} (hi : i+1<ψ)
    (C : Fin (q*ψ) → AgentState ψ)
    (h : (pipeline hp κ c (C (cell ring g i)) (C (cell ring g (i+1)))).1.path=.bot ∨
      (pipeline hp κ c (C (cell ring g i)) (C (cell ring g (i+1)))).2.path=.bot) :
    Target (edgeStep hp κ c ring g i C) := by
  right
  rcases h with h | h
  · exact ⟨cell ring g i,by rw [step_left hp κ c ring g hi]; exact h⟩
  · exact ⟨cell ring g (i+1),by rw [step_right hp κ c ring g hi]; exact h⟩

private theorem run_append {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing n) (C : Fin n → AgentState ψ) (u v : List (Fin n)) :
    run hp κ c ring C (u++v) = run hp κ c ring (run hp κ c ring C u) v := by
  induction u generalizing C with
  | nil => rfl
  | cons e es ih => exact ih _
private theorem internal_effect {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) {i : Nat} (hi : i≤ψ-3)
    (C0 C : Fin (q*ψ) → AgentState ψ) (h0 : OwnTF ring g C0)
    (hf : Frame ring g C0 C) (hnt : ¬ Target C)
    (hl : PrepInternal.Locked (C (cell ring g i)).state)
    (hr : PrepInternal.Mid (C (cell ring g (i+1))).state) :
    let D := edgeStep hp κ c ring g i C
    Target D ∨ (Frame ring g C0 D ∧
      (D (cell ring g i)).state=PrepInternal.leftResult (C (cell ring g i)).state (C (cell ring g (i+1))).state ∧
      (D (cell ring g (i+1))).state=PrepInternal.rightResult (C (cell ring g (i+1))).state) := by
  have ho := frame_own h0 hf
  rcases ho i (by omega) with ⟨lli,⟨bL,pl⟩,tl⟩
  rcases ho (i+1) (by omega) with ⟨rli,⟨bR,pr⟩,tr⟩
  have hh := PrepInternal.internal_row hp h4 κ c i hi
    (C (cell ring g i)) (C (cell ring g (i+1))) bL bR lli rli pl pr tl tr
    (followers hnt _) (followers hnt _) hl hr
  rcases hh with hh | hh | ⟨hframe,hleft,hright⟩
  · exact Or.inl (pair_hole_target hp κ c ring g (by omega) C (Or.inl hh))
  · exact Or.inl (pair_hole_target hp κ c ring g (by omega) C (Or.inr hh))
  · refine Or.inr ⟨step_frame hp κ c ring g (by omega) C0 C hf hframe,?_,?_⟩
    · rw [step_left hp κ c ring g (by omega)]; exact hleft
    · rw [step_right hp κ c ring g (by omega)]; exact hright

private theorem forward_step {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 : Fin (q*ψ) → AgentState ψ)
    (h0 : OwnTF ring g C0) {k : Nat} (hk : k<ψ-2)
    (C : Fin (q*ψ) → AgentState ψ) (h : Forward ring g C0 k C) (hnt : ¬Target C) :
    Target (edgeStep hp κ c ring g k C) ∨
      Forward ring g C0 (k+1) (edgeStep hp κ c ring g k C) := by
  have hl := h.2.2.1 k (by omega) (by omega)
  have hr := h.2.2.2 (k+1) (by omega) (by omega)
  have he := internal_effect hp h4 κ c ring g (by omega) C0 C h0 h.1 hnt hl hr
  rcases he with he | ⟨hf,hleft,hright⟩
  · exact Or.inl he
  right
  let D := edgeStep hp κ c ring g k C
  have hL : PrepInternal.Locked (D (cell ring g k)).state := by
    rw [hleft]
    rcases hl with hl | hl <;> rcases hr with hr | hr | hr <;>
      simp [PrepInternal.Locked,PrepInternal.leftResult,hl,hr]
  have hR : PrepInternal.Locked (D (cell ring g (k+1))).state := by
    rw [hright]
    rcases hr with hr | hr | hr <;> simp [PrepInternal.Locked,PrepInternal.rightResult,hr]
  refine ⟨hf,?_,?_,?_⟩
  · rw [step_other hp κ c ring g (by omega) (by omega) (by omega) (by omega)]
    exact h.2.1
  · intro j hj hjk
    by_cases hji : j=k
    · subst j; exact hL
    by_cases hjr : j=k+1
    · subst j; exact hR
    rw [step_other hp κ c ring g (by omega) (by omega) hji hjr]
    exact h.2.2.1 j hj (by omega)
  · intro j hj hjk
    rw [step_other hp κ c ring g (by omega) (by omega) (by omega) (by omega)]
    exact h.2.2.2 j hj (by omega)

private theorem reverse_step {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 : Fin (q*ψ) → AgentState ψ)
    (h0 : OwnTF ring g C0) {k : Nat} (hk : k<ψ-2)
    (C : Fin (q*ψ) → AgentState ψ) (h : Reverse ring g C0 k C) (hnt : ¬Target C) :
    Target (edgeStep hp κ c ring g (ψ-3-k) C) ∨
      Reverse ring g C0 (k+1) (edgeStep hp κ c ring g (ψ-3-k) C) := by
  let i := ψ-3-k
  have hii : i≤ψ-3 := by omega
  have hinext : i+1=ψ-2-k := by omega
  have hinew : ψ-2-(k+1)=i := by omega
  have hl := h.2.2.1 i (by omega)
  have hr := h.2.2.2 (i+1) (by omega) (by omega)
  have he := internal_effect hp h4 κ c ring g hii C0 C h0 h.1 hnt hl (Or.inr (Or.inr hr))
  rcases he with he | ⟨hf,hleft,hright⟩
  · exact Or.inl he
  right
  let D := edgeStep hp κ c ring g i C
  have hL : (D (cell ring g i)).state=.compare1 := by
    rw [hleft]
    rcases hl with hl | hl <;> simp [PrepInternal.leftResult,hl,hr]
  have hR : (D (cell ring g (i+1))).state=.compare1 := by
    rw [hright]; simp [PrepInternal.rightResult,hr]
  refine ⟨hf,?_,?_,?_⟩
  · rw [step_other hp κ c ring g (by omega) (by omega) (by omega) (by omega)]
    exact h.2.1
  · intro j hj
    rw [step_other hp κ c ring g (by omega) (by omega) (by omega) (by omega)]
    exact h.2.2.1 j (by omega)
  · intro j hj hjmax
    by_cases hji : j=i
    · subst j; exact hL
    by_cases hjr : j=i+1
    · subst j; exact hR
    rw [step_other hp κ c ring g (by omega) (by omega) hji hjr]
    exact h.2.2.2 j (by omega) hjmax

private theorem iterate {n ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing n) (N : Nat) (P : Nat → (Fin n → AgentState ψ) → Prop)
    (edge : Nat → Fin n) (Good : Fin n → Prop)
    (edge_good : ∀ k,k<N → Good (edge k))
    (next : ∀ k,k<N → ∀ C,P k C → ¬Target C →
      Target ((protocol hp κ c).step ring C (edge k)) ∨
      P (k+1) ((protocol hp κ c).step ring C (edge k)))
    (k m : Nat) (hkm : k+m≤N) (C : Fin n → AgentState ψ) (h : P k C) :
    ∃ w : List (Fin n),w.length≤m ∧
      (∀ e, e∈w → Good e) ∧
      (Target (run hp κ c ring C w) ∨ P (k+m) (run hp κ c ring C w)) := by
  classical
  induction m generalizing k C with
  | zero => exact ⟨[],by simp,by simp,Or.inr (by simpa [run] using h)⟩
  | succ m ih =>
    by_cases ht : Target C
    · exact ⟨[],by simp,by simp,Or.inl ht⟩
    have hn := next k (by omega) C h ht
    rcases hn with hn | hn
    · exact ⟨[edge k],by simp,by simpa using edge_good k (by omega),Or.inl hn⟩
    · rcases ih (k+1) (by omega) ((protocol hp κ c).step ring C (edge k)) hn with ⟨w,hw,hgood,hend⟩
      refine ⟨edge k::w,by simp; omega,?_,?_⟩
      · intro e he
        rcases List.mem_cons.mp he with he | he
        · simpa [he] using edge_good k (by omega)
        · exact hgood e he
      have he : k+1+m=k+(m+1) := by omega
      simpa only [run,he] using hend

private theorem terminal_effect {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 C : Fin (q*ψ) → AgentState ψ)
    (h0 : OwnTF ring g C0) (hf : Frame ring g C0 C) (hnt : ¬Target C)
    (hl : PrepRows.PenState (C (cell ring g (ψ-2))).state)
    (hr : (C (cell ring g (ψ-1))).state=.compare2) :
    let D := edgeStep hp κ c ring g (ψ-2) C
    Target D ∨ (Frame ring g C0 D ∧
      (((D (cell ring g (ψ-2))).state=PrepRows.penResult (C (cell ring g (ψ-2))).state ∧
        (D (cell ring g (ψ-1))).state=.compare2) ∨
       ((D (cell ring g (ψ-2))).state=.depart ∧
        (D (cell ring g (ψ-1))).state=.eliminate_signal))) := by
  have hi : ψ-2+1=ψ-1 := by omega
  have ho := frame_own h0 hf
  rcases ho (ψ-2) (by omega) with ⟨lli,⟨bL,pl⟩,tl⟩
  rcases ho (ψ-1) (by omega) with ⟨rli,⟨bR,pr⟩,tr⟩
  have hh := PrepRows.penultimate_row hp h4 κ c
    (C (cell ring g (ψ-2))) (C (cell ring g (ψ-1))) bL bR lli rli pl pr tl tr
    (followers hnt _) (followers hnt _) hl hr
  have heL := step_left hp κ c ring g (i:=ψ-2) (by omega) C
  have heR := step_right hp κ c ring g (i:=ψ-2) (by omega) C
  simp only [hi] at heL heR
  rcases hh with hh | hh | ⟨hframe,hstate⟩
  · left
    exact pair_hole_target hp κ c ring g (i:=ψ-2) (by omega) C (Or.inl (by simpa only [hi] using hh))
  · left
    exact pair_hole_target hp κ c ring g (i:=ψ-2) (by omega) C (Or.inr (by simpa only [hi] using hh))
  · right
    refine ⟨step_frame hp κ c ring g (i:=ψ-2) (by omega) C0 C hf (by simpa only [hi] using hframe),?_⟩
    rw [heL,heR]
    exact hstate

private theorem drain_target {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C : Fin (q*ψ) → AgentState ψ)
    (ho : OwnTF ring g C)
    (hl : (C (cell ring g (ψ-2))).state=.depart)
    (hr : (C (cell ring g (ψ-1))).state=.eliminate_signal) :
    Target (edgeStep hp κ c ring g (ψ-2) C) := by
  have hi : ψ-2+1=ψ-1 := by omega
  have hh := PPLLAstraR5TerminalDrain.terminal_drain hp κ c
    (C (cell ring g (ψ-2))) (C (cell ring g (ψ-1))) h4
    (ho (ψ-2) (by omega)).1 (ho (ψ-1) (by omega)).1 hr (by rw [hl]; decide)
  exact pair_hole_target hp κ c ring g (i:=ψ-2) (by omega) C
    (Or.inr (by simpa only [hi] using hh))
private theorem first_forward {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 : Fin (q*ψ) → AgentState ψ)
    (h : Basin ring g C0)
    (hf : Frame ring g C0 (edgeStep hp κ c ring g (ψ-2) C0))
    (hl : (edgeStep hp κ c ring g (ψ-2) C0 (cell ring g (ψ-2))).state=
      PrepRows.penResult (C0 (cell ring g (ψ-2))).state)
    (hr : (edgeStep hp κ c ring g (ψ-2) C0 (cell ring g (ψ-1))).state=.compare2) :
    Forward ring g C0 0 (edgeStep hp κ c ring g (ψ-2) C0) := by
  refine ⟨hf,hr,?_,?_⟩
  · intro j hj hj0
    have hjz : j=0 := by omega
    subst j
    rw [step_other hp κ c ring g (by omega) (by omega) (by omega) (by omega)]
    exact h.2.1
  · intro j hj hj0
    by_cases hje : j=ψ-2
    · subst j
      rw [hl]
      rcases h.2.2.2.1 with hs | hs | hs | hs <;>
        simp [PrepRows.penResult,PrepInternal.Mid,hs]
    · rw [step_other hp κ c ring g (by omega) (by omega) hje (by omega)]
      exact h.2.2.1 j (by omega) (by omega)

private theorem second_reverse {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 C : Fin (q*ψ) → AgentState ψ)
    (h : Forward ring g C0 (ψ-2) C)
    (hf : Frame ring g C0 (edgeStep hp κ c ring g (ψ-2) C))
    (hl : (edgeStep hp κ c ring g (ψ-2) C (cell ring g (ψ-2))).state=
      PrepRows.penResult (C (cell ring g (ψ-2))).state)
    (hr : (edgeStep hp κ c ring g (ψ-2) C (cell ring g (ψ-1))).state=.compare2) :
    Reverse ring g C0 0 (edgeStep hp κ c ring g (ψ-2) C) := by
  refine ⟨hf,hr,?_,?_⟩
  · intro j hj
    rw [step_other hp κ c ring g (by omega) (by omega) (by omega) (by omega)]
    exact h.2.2.1 j (by omega) (by omega)
  · intro j hj hjmax
    have hje : j=ψ-2 := by omega
    subst j
    rw [hl]
    rcases h.2.2.1 (ψ-2) (by omega) (by omega) with hs | hs <;>
      simp [PrepRows.penResult,hs]

private theorem reverse_prepared {q ψ : Nat} (h4 : 4≤ψ)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 C : Fin (q*ψ) → AgentState ψ)
    (h : Reverse ring g C0 (ψ-2) C) : Prepared ring g C0 C := by
  refine ⟨h.1,?_,h.2.1⟩
  intro j hj
  exact h.2.2.2 j (by omega) (by omega)

private theorem prepare_run {q ψ : Nat} (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 : Fin (q*ψ) → AgentState ψ)
    (hB : Basin ring g C0) :
    ∃ w : List (Fin (q*ψ)),w.length≤2*ψ-2 ∧ InternalWord ring g w ∧
      (Target (run hp κ c ring C0 w) ∨ Prepared ring g C0 (run hp κ c ring C0 w)) := by
  classical
  have hgood : ∀ j, j+1<ψ → ∃ k, k+1<ψ ∧ cell ring g j=cell ring g k :=
    fun j hj => ⟨j,hj,rfl⟩
  have hegood : ∃ j, j+1<ψ ∧ cell ring g (ψ-2)=cell ring g j :=
    hgood (ψ-2) (by omega)
  have hcons (e : Fin (q*ψ)) (he : ∃ j, j+1<ψ ∧ e=cell ring g j)
      (w : List (Fin (q*ψ))) (hw : InternalWord ring g w) :
      InternalWord ring g (e::w) := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · simpa [h] using he
    · exact hw x h
  have happ (u v : List (Fin (q*ψ)))
      (hu : InternalWord ring g u) (hv : InternalWord ring g v) :
      InternalWord ring g (u++v) := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hu x h
    · exact hv x h
  have hsingle : InternalWord ring g [cell ring g (ψ-2)] :=
    hcons _ hegood [] (by intro x hx; cases hx)
  by_cases ht : Target C0
  · exact ⟨[],by simp,by simp [InternalWord],Or.inl (by simpa [run] using ht)⟩
  let e := cell ring g (ψ-2)
  let D := edgeStep hp κ c ring g (ψ-2) C0
  have hA := terminal_effect hp h4 κ c ring g C0 C0 hB.1 (frame_self hB.1) ht hB.2.2.2.1 hB.2.2.2.2
  rcases hA with hstop | ⟨hfd,hstate⟩
  · exact ⟨[e],by simp; omega,hsingle,Or.inl hstop⟩
  rcases hstate.symm with ⟨hleft,hright⟩ | ⟨hleft,hright⟩
  · have hstop := drain_target hp h4 κ c ring g D (frame_own hB.1 hfd) hleft hright
    exact ⟨[e,e],by simp; omega,hcons _ hegood [e] hsingle,Or.inl hstop⟩
  have hF : Forward ring g C0 0 D := first_forward hp h4 κ c ring g C0 hB hfd hleft hright
  have hforward := iterate hp κ c ring (ψ-2) (Forward ring g C0)
    (fun k => cell ring g k)
    (fun e => ∃ j, j+1<ψ ∧ e=cell ring g j)
    (fun k hk => hgood k (by omega))
    (fun k hk C h hn => forward_step hp h4 κ c ring g C0 hB.1 hk C h hn)
    0 (ψ-2) (by omega) D hF
  rcases hforward with ⟨wf,hwf,hgoodf,hendf⟩
  have hsupportf : InternalWord ring g wf := hgoodf
  let E := run hp κ c ring D wf
  have hrunF : run hp κ c ring C0 (e::wf) = E := rfl
  rcases hendf with hstop | hfe
  · refine ⟨e::wf,by simp; omega,hcons _ hegood wf hsupportf,Or.inl ?_⟩
    exact hstop
  have hFE : Forward ring g C0 (ψ-2) E := by simpa only [Nat.zero_add] using hfe
  by_cases htE : Target E
  · exact ⟨e::wf,by simp; omega,hcons _ hegood wf hsupportf,Or.inl htE⟩
  let F := edgeStep hp κ c ring g (ψ-2) E
  have hleftE : PrepRows.PenState (E (cell ring g (ψ-2))).state := by
    rcases hFE.2.2.1 (ψ-2) (by omega) (by omega) with hs | hs
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr hs))
  have hC := terminal_effect hp h4 κ c ring g C0 E hB.1 hFE.1 htE hleftE hFE.2.1
  have hrunC : run hp κ c ring C0 ((e::wf)++[e]) = F := by
    rw [run_append,hrunF]; rfl
  rcases hC with hstop | ⟨hff,hstate⟩
  · refine ⟨(e::wf)++[e],by simp; omega,happ _ _ (hcons _ hegood wf hsupportf) hsingle,Or.inl ?_⟩
    rw [hrunC]; exact hstop
  rcases hstate.symm with ⟨hleftF,hrightF⟩ | ⟨hleftF,hrightF⟩
  · have hstop := drain_target hp h4 κ c ring g F (frame_own hB.1 hff) hleftF hrightF
    refine ⟨((e::wf)++[e])++[e],by simp; omega,
      happ _ _ (happ _ _ (hcons _ hegood wf hsupportf) hsingle) hsingle,Or.inl ?_⟩
    rw [run_append,hrunC]
    exact hstop
  have hR : Reverse ring g C0 0 F := second_reverse hp h4 κ c ring g C0 E hFE hff hleftF hrightF
  have hreverse := iterate hp κ c ring (ψ-2) (Reverse ring g C0)
    (fun k => cell ring g (ψ-3-k))
    (fun e => ∃ j, j+1<ψ ∧ e=cell ring g j)
    (fun k hk => hgood (ψ-3-k) (by omega))
    (fun k hk C h hn => reverse_step hp h4 κ c ring g C0 hB.1 hk C h hn)
    0 (ψ-2) (by omega) F hR
  rcases hreverse with ⟨wr,hwr,hgoodr,hendr⟩
  refine ⟨((e::wf)++[e])++wr,by simp; omega,
    happ _ _ (happ _ _ (hcons _ hegood wf hsupportf) hsingle) hgoodr,?_⟩
  rw [run_append,hrunC]
  rcases hendr with hstop | hfinal
  · exact Or.inl hstop
  · right
    apply reverse_prepared h4 ring g C0 _
    simpa only [Nat.zero_add] using hfinal

private theorem internal_step_outside {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C : Fin (q*ψ) → AgentState ψ)
    {j : Nat} (hj : j+1<ψ) (x : Fin (q*ψ)) (hx : Outside ring g x) :
    (protocol hp κ c).step ring C (cell ring g j) x=C x := by
  have hl : x≠cell ring g j := hx j (by omega)
  have hr : x≠cell ring g (j+1) := hx (j+1) hj
  simp [PPLLAstraR5ResetDrain.protocol,PopulationProtocol.step,cell_next ring g hj,hl,hr]

/-- All unselected physical cells are unchanged by an internal-edge word. -/
theorem run_outside_of_internal {q ψ : Nat} (hp : ψ>0) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q)
    (C0 : Fin (q*ψ) → AgentState ψ) (w : List (Fin (q*ψ)))
    (hw : InternalWord ring g w) (x : Fin (q*ψ)) (hx : Outside ring g x) :
    run hp κ c ring C0 w x=C0 x := by
  induction w generalizing C0 with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨j,hj,he⟩ := hw e (by simp)
    have htail : InternalWord ring g es := by
      intro a ha
      exact hw a (by simp [ha])
    subst e
    have hstep := internal_step_outside hp κ c ring g C0 hj x hx
    simpa only [run] using (ih _ htail).trans hstep

/-- Preparation with the actual constructed internal-edge schedule and an
exact full-state frame on every physical cell outside the selected group. -/
theorem exists_preparation_word_supported {q ψ : Nat}
    (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 : Fin (q*ψ) → AgentState ψ)
    (hB : Basin ring g C0) :
    ∃ w : List (Fin (q*ψ)),w.length≤2*ψ-2 ∧
      InternalWord ring g w ∧
      (protocol hp κ c).Reachable ring C0 (run hp κ c ring C0 w) ∧
      (∀ x, Outside ring g x → run hp κ c ring C0 w x=C0 x) ∧
      (Target (run hp κ c ring C0 w) ∨ Prepared ring g C0 (run hp κ c ring C0 w)) := by
  rcases prepare_run hp h4 κ c ring g C0 hB with ⟨w,hw,hsupport,hend⟩
  exact ⟨w,hw,hsupport,run_reachable hp κ c ring C0 w,
    fun x hx => run_outside_of_internal hp κ c ring g C0 w hsupport x hx,hend⟩

/-- An actual R5 physical edge word of length at most 2*psi-2 prepares the
selected basin-B group, or reaches a global leader/hole. The endpoint is
reachable for that same protocol. Every row interface is instantiated from
its verified actual-pipeline theorem; there are no assumed local contracts.
Unselected cells and all ancillary fields are unrestricted. -/
theorem exists_preparation_word {q ψ : Nat}
    (hp : ψ>0) (h4 : 4≤ψ) (κ : Nat) (c : Cfg)
    (ring : DirectedRing (q*ψ)) (g : Fin q) (C0 : Fin (q*ψ) → AgentState ψ)
    (hB : Basin ring g C0) :
    ∃ w : List (Fin (q*ψ)),w.length≤2*ψ-2 ∧
      (protocol hp κ c).Reachable ring C0 (run hp κ c ring C0 w) ∧
      (Target (run hp κ c ring C0 w) ∨ Prepared ring g C0 (run hp κ c ring C0 w)) := by
  rcases exists_preparation_word_supported hp h4 κ c ring g C0 hB with
    ⟨w,hw,_,hreach,_,hend⟩
  exact ⟨w,hw,hreach,hend⟩

#print axioms exists_preparation_word_supported
#print axioms run_outside_of_internal
#print axioms exists_preparation_word
end PPLLAstraR5PrepWord
