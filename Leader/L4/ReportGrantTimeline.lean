import Leader.L4.ReportLeaseOwner

namespace L4.ReportGrantTimeline
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetRawHooks
open ReportLeaseGrants ReportJoinedGrants ReportByteRows

variable {s n : Nat}

private theorem canonical_empty (g : BStarShort.GrantView) (j : Fin 3)
    (E : g.old j=false) : g.canonical j=false := by
  by_cases J : j=1
  · subst j
    simp [BStarShort.GrantView.canonical,E]
  · cases C : g.old 1 <;> simp [BStarShort.GrantView.canonical,C,J,E]

/-- Even an incompatible inherited grant state cannot create a held
bit on an incoming mark. The only gain is actual outgoing arbitration. -/
theorem gain_at_old_win (d : Sheet) (N : 1<n) (x : Raw s n)
    (e i : Fin n) (j : Fin 3)
    (H : lower d (oldHeaders (rows s) (x i))=true)
    (NotHeld : rawGrant d x i j=false)
    (Gain : rawGrant d (rawNext s x e) i j=true) :
    e=i ∧ (oldView (params d s) true (selectBytes d (x i))).win j=true := by
  by_cases L : e=i
  · subst e
    exact ⟨rfl,(raw_outgoing_fresh_exact d x i (edge_sep N i) H j NotHeld).symm.trans Gain⟩
  · by_cases R : i=rightNeighbor e
    · subst i
      have A := (raw_grant_rows d x e (edge_sep N e) j).2
      rw [H,if_pos rfl] at A
      change rawGrant d (rawNext s x e) (rightNeighbor e) j =
        (oldView (params d s) true (selectBytes d (x (rightNeighbor e)))).canonical j at A
      have C := canonical_empty (oldView (params d s) true
        (selectBytes d (x (rightNeighbor e)))) j NotHeld
      rw [Gain,C] at A
      contradiction
    · unfold rawGrant at Gain
      rw [ReportRawProjection.raw_spectator x e i (Ne.symm L) R] at Gain
      have A : rawGrant d x i j=true := Gain
      rw [NotHeld] at A
      contradiction

/-- The bit is held at every prefix, including both endpoints. -/
def HeldAlong (d : Sheet) (i : Fin n) (j : Fin 3) :
    Raw s n → List (Fin n) → Prop
  | x,[] => rawGrant d x i j=true
  | x,e::w => rawGrant d x i j=true ∧ HeldAlong d i j (rawNext s x e) w

theorem held_at_end_splits (d : Sheet) (i : Fin n) (j : Fin 3)
    (x : Raw s n) (w : List (Fin n))
    (H : rawGrant d (rawRun x w) i j=true) :
    HeldAlong d i j x w ∨
    ∃ pre post e, w=pre++e::post ∧ rawGrant d (rawRun x pre) i j=false ∧
      HeldAlong d i j (rawNext s (rawRun x pre) e) post := by
  induction w generalizing x with
  | nil => exact .inl H
  | cons e w ih =>
    rcases ih (rawNext s x e) H with A|⟨pre,post,k,E,Z,T⟩
    · cases B : rawGrant d x i j with
      | true => exact .inl ⟨B,A⟩
      | false => exact .inr ⟨[],w,e,rfl,B,A⟩
    · exact .inr ⟨e::pre,post,k,by rw [E]; rfl,Z,T⟩

theorem held_start (d : Sheet) (i : Fin n) (j : Fin 3)
    (x : Raw s n) (w : List (Fin n)) (H : HeldAlong d i j x w) :
    rawGrant d x i j=true := by
  cases w
  · exact H
  · exact H.1

/-- Backward search on the same finite tape, not a resampling argument.
If the endpoint has a grant and the bit was absent at the seed, the
last uninterrupted hold starts on a real old winning incidence.
This does not by itself authenticate the old ACQ payload. -/
theorem last_win_after_clear (d : Sheet) (N : 1<n) (i : Fin n) (j : Fin 3)
    (x : Raw s n) (w : List (Fin n))
    (headers : ∀ pre, (∃ suf,w=pre++suf) →
      lower d (oldHeaders (rows s) (rawRun x pre i))=true)
    (Empty : rawGrant d x i j=false) (H : rawGrant d (rawRun x w) i j=true) :
    ∃ pre post, w=pre++i::post ∧
      rawGrant d (rawRun x pre) i j=false ∧
      (oldView (params d s) true (selectBytes d (rawRun x pre i))).win j=true ∧
      HeldAlong d i j (rawNext s (rawRun x pre) i) post := by
  rcases held_at_end_splits d i j x w H with A|⟨pre,post,e,E,Z,T⟩
  · have M := held_start d i j x w A
    rw [Empty] at M
    contradiction
  · obtain ⟨rfl,W⟩ := gain_at_old_win d N (rawRun x pre) e i j
      (headers pre ⟨e::post,E⟩) Z (held_start d i j _ post T)
    exact ⟨pre,post,E,Z,W,T⟩

#print axioms gain_at_old_win
#print axioms last_win_after_clear
end L4.ReportGrantTimeline
