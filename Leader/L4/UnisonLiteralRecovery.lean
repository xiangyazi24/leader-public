import Leader.L4.UnisonLocalProofs
import Leader.L4.UnisonRing
import Leader.L4.UnisonRecovery

namespace L4.UnisonLiteralRecovery
open UnisonRows UnisonRing UnisonLocalProofs

/-- The stage interface discharged by the actual signed poll. -/
def literalRows {m : Nat} (R : Ring m) (P : Int) (hP : 0<P) :
    UnisonStages.Rows (UnisonRing.State m) m where
  P := P
  value := fun x i => (x i).value
  error := fun x i => (x i).err=true
  next := UnisonRing.step R P
  near := fun u v => Near R v u
  symm := near_symm R
  good := CfgValid P
  quiet := Quiet R P
  legal := Leg R P
  good_step := valid_step R P hP
  quiet_step := quiet_step R P hP
  frame := fun x e v h => by rw [step_other R P x e v h]; exact ⟨rfl,Iff.rfl⟩
  negative := fun x v hx he => (hx v).2.2 he
  error_step := by
    intro x v _ hq he
    rw [step_here] at he ⊢
    have h := error_poll P (x (R.left v)) (x v) (x (R.right v)) (hq v) he
    rcases h with hf|⟨u,hu,hE,hV,hLt⟩
    · exact .inl hf
    · rcases hu with rfl|rfl
      · exact .inr ⟨R.left v, .inl rfl, hE,hV,hLt⟩
      · exact .inr ⟨R.right v,.inr rfl, hE,hV,hLt⟩
  raise_step := by
    intro x u v hx _ hn he hu
    rw [step_here]
    exact poll_keeps_error_ceiling P _ _ _ (x u) hP (hx u) he
      (hn.elim (fun e => .inl (congrArg x e)) (fun e => .inr (congrArg x e))) hu
  prop_on_gap := by
    intro x u v _ hq hn he hN hlt
    rw [step_here]
    exact propagate_gap P _ _ _ (x u)
      (hn.elim (fun e => .inl (congrArg x e)) (fun e => .inr (congrArg x e)))
      (hq v) he hN hlt
  no_correct_lower_gap := by
    intro x u v hx hq hn he hE
    have hn' := near_symm R hn
    exact correct_low_neighbor P _ _ _ (x v)
      (hn'.elim (fun e => .inl (congrArg x e)) (fun e => .inr (congrArg x e)))
      (hq u) (Bool.eq_false_iff.mpr he) ((hx v).2.2 hE)
  clear := by
    intro x v _ hq hE hb hM
    rw [step_here]
    exact fun he => by
      have h := clear_at_max P (x (R.left v)) (x v) (x (R.right v)) (hq v) hE
        (fun u hu => by
          rcases hu with rfl|rfl
          · exact hb (R.left v) (.inl rfl)
          · exact hb (R.right v) (.inr rfl))
        (fun u hu hU => by
          rcases hu with rfl|rfl
          · exact hM (R.left v) (.inl rfl) hU
          · exact hM (R.right v) (.inr rfl) hU)
      rw [h] at he
      cases he
  quiet_no_errors := fun x hv hQ hE => UnisonRing.leg_of_quiet_correct R P x hv hQ
    (fun i => Bool.eq_false_iff.mpr (hE i))

theorem literal_conditions {m : Nat} (R : Ring m) (P : Int) (hm : 0<m) (hP : (m:Int)<P) :
    UnisonRecovery.Conditions (literalRows R P (by omega)) := by
  have h : 0<P := by omega
  refine ⟨hm,hP,fun x v hv => (hv v).1,?_,quiet_cover R P h⟩
  intro x hv hq v he hv'
  obtain ⟨u,hu,hE,hV⟩ := error_descent P (x (R.left v)) (x v) (x (R.right v)) (hq v) he hv'
  rcases hu with rfl|rfl
  · exact ⟨R.left v,.inl rfl,hE,hV⟩
  · exact ⟨R.right v,.inr rfl,hE,hV⟩

/-- Given raw same-mark projection to the literal serial cycle, the
normalized signed clock reaches LEG after at most 2m+1 covers. Each
cover uses the exact common-label all-centre service estimate. -/
theorem cycle_recovery {β : Type} {n m : Nat} (hm : 3≤m) (P : Int) (hP : (m:Int)<P)
    {next : β → Fin n → β} {I : β → Prop}
    (J : UnisonCover.SerialProjection next (UnisonRing.step (cycle m hm) P) I)
    (μ c : Nat) (hμ : 0<μ) (hn : 0<n) (hg : 2*m≤2^c)
    (service : ∀ i x, I x → IIDExpectedHittingTimeAtMost
      (FastExpEvent.flagNext next (fun y e => J.pub y e=some i)) (fun z => z.2=true) (x,false) μ)
    (x : β) (hx : I x) (hValid : CfgValid P (J.project x)) :
    IIDExpectedHittingTimeAtMost next (fun y => Leg (cycle m hm) P (J.project y)) x
      ((2*m+1)*((2*μ)*(c+1))) :=
  UnisonRecovery.physical_mean (literalRows (cycle m hm) P (by omega))
    (literal_conditions (cycle m hm) P (by omega) hP) J μ c hμ hn hg service x hx hValid

/-- The raw bounded clock slice allows malformed error/status pairs.
Each read normalizes before the emitted biased row is evaluated. -/
def RawInRange {m : Nat} (P : Int) (x : UnisonRing.State m) : Prop :=
  ∀ i, 0≤(x i).value ∧ (x i).value<2*P

def decodeRing {m : Nat} (P : Int) (x : UnisonRing.State m) : UnisonRing.State m :=
  fun i => decodeBiased P (x i)

def rawAtomic {m : Nat} (R : Ring m) (P : Int) (x : UnisonRing.State m) (e : Fin m) :
    UnisonRing.State m := fun i =>
  if i=e then (biasedRow P (normalizeBiased P (x (R.left e)))
    (normalizeBiased P (x e)) (normalizeBiased P (x (R.right e)))).2 else x i

private theorem decode_of_bias (P : Int) (x : Clock) (hx : Valid P x) :
    decodeBiased P (bias P x)=x := by
  cases x with
  | mk e v =>
    cases e with
    | false => simp [decodeBiased,bias,normalizeBiased]
    | true =>
      have hN : v<0 := hx.2.2 rfl
      have h' : ¬P≤v+P := by omega
      simp [decodeBiased,bias,normalizeBiased,h']

theorem raw_decode_step {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : UnisonRing.State m) (e : Fin m) (hx : RawInRange P x) :
    decodeRing P (rawAtomic R P x e)=UnisonRing.step R P (decodeRing P x) e := by
  funext i
  by_cases h : i=e
  · subst i
    simp only [decodeRing,rawAtomic,if_true,step_here,normalize_is_bias_decode,biased_signed_commutes]
    have hp := poll_valid P (decodeBiased P (x (R.left e))) (decodeBiased P (x e))
      (decodeBiased P (x (R.right e))) hP
      (decodeBiased_valid P _ hP (hx _)) (decodeBiased_valid P _ hP (hx _))
      (decodeBiased_valid P _ hP (hx _))
    exact decode_of_bias P _ hp
  · simp [decodeRing,rawAtomic,h,UnisonRing.step]

theorem raw_range_step {m : Nat} (R : Ring m) (P : Int) (hP : 0<P)
    (x : UnisonRing.State m) (e : Fin m) (hx : RawInRange P x) :
    RawInRange P (rawAtomic R P x e) := by
  intro i
  by_cases h : i=e
  · subst i
    simp only [rawAtomic,if_true,normalize_is_bias_decode,biased_signed_commutes]
    simp only [bias]
    have hp := poll_valid P (decodeBiased P (x (R.left e))) (decodeBiased P (x e))
      (decodeBiased P (x (R.right e))) hP
      (decodeBiased_valid P _ hP (hx _)) (decodeBiased_valid P _ hP (hx _))
      (decodeBiased_valid P _ hP (hx _))
    change 0≤(poll P _ _ _).value+P ∧ (poll P _ _ _).value+P<2*P
    have hl := hp.1
    have hu := hp.2.1
    omega
  · simpa [rawAtomic,h] using hx i

/-- Deterministic corollary for any prescribed succession of
complete covers. This is stronger than testing permutations. -/
theorem serial_covers_recover {m : Nat} (hm : 3≤m) (P : Int) (hP : (m:Int)<P)
    (x : UnisonRing.State m) (hx : CfgValid P x)
    (ws : List (List (Fin m))) (hLen : ws.length=2*m+1)
    (hCover : ∀ w∈ws, UnisonCover.Covers w) :
    Leg (cycle m hm) P (ws.foldl (UnisonCover.runAtomic (UnisonRing.step (cycle m hm) P)) x) := by
  let S := literalRows (cycle m hm) P (by omega)
  have K := literal_conditions (cycle m hm) P (by omega) hP
  have go (ws : List (List (Fin m))) (y : UnisonRing.State m) (j : Nat)
      (hLast : j+ws.length≤2*m+1) (hy : UnisonRecovery.phase S j y)
      (hw : ∀ w∈ws, UnisonCover.Covers w) :
      UnisonRecovery.phase S (j+ws.length)
        (ws.foldl (UnisonCover.runAtomic (UnisonRing.step (cycle m hm) P)) y) := by
    induction ws generalizing y j with
    | nil => simpa using hy
    | cons w rest ih =>
      have hJ : j<2*m+1 := by simp at hLast; omega
      have hRound := UnisonRecovery.phase_round S K j hJ y w hy (hw w (by simp))
      have h := ih (UnisonCover.runAtomic (UnisonRing.step (cycle m hm) P) y w)
        (j+1) (by simp at hLast; omega) hRound (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      simpa only [List.foldl_cons,List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have h := go ws x 0 (by simp [hLen]) (by simpa [UnisonRecovery.phase,S,literalRows] using hx) hCover
  simp only [Nat.zero_add,hLen] at h
  exact UnisonRecovery.final_legal S K _ h

end L4.UnisonLiteralRecovery

