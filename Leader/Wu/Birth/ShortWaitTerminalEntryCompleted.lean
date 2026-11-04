import Leader.Wu.Birth.ShortWaitTerminalEntryInterleaving

namespace BirthShortWaitTerminalEntryInterleaving

open PPLL PPLLRepair
open BirthShortWaitDomainWitness
open BirthShortWait BirthShortWaitProjection BirthShortWaitRawRing
open BirthWaitClockMass
open BirthWaitClockMass.Line
open BirthWaitClockMass.RawRing
open BirthWaitClockMass.ResetEntry
open BirthShortWaitTerminalEntryRepair

set_option autoImplicit false
set_option Elab.async false

private theorem completed_key_label {psi width : Nat}
    (u : AgentState psi) (v : AgentState width)
    (h : BirthShortWaitRawRing.KeyAgree u v) :
    u.label.val = v.label.val := by
  unfold BirthShortWaitRawRing.KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.label h

private theorem completed_key_carry {psi width : Nat}
    (u : AgentState psi) (v : AgentState width)
    (h : BirthShortWaitRawRing.KeyAgree u v) :
    u.carry = v.carry := by
  unfold BirthShortWaitRawRing.KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.carry h

private theorem completed_key_reset {psi width : Nat}
    (u : AgentState psi) (v : AgentState width)
    (h : BirthShortWaitRawRing.KeyAgree u v) :
    u.reset = v.reset := by
  unfold BirthShortWaitRawRing.KeyAgree at h
  simpa [WaitKey.ofState] using congrArg WaitKey.reset h

/-- On any physical line initiator, a completed short-line state makes the
repaired row equal to the frozen old row.  Internals use the active-label
branch; the physical width terminal uses exactly the completed Line bits. -/
private theorem entryRawStep_eq_old_of_line {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : BirthShortWaitRawRing.State (psi := psi) hw hfit)
    (e : Fin n) (he : e.val < width) :
    entryRawStep hpsi hw hle hfit cap S.conf e =
      BirthShortWaitRawRing.rawStep hpsi hw hle hfit cap S.conf e := by
  let i : Fin width := ⟨e.val, he⟩
  have hei : e = site hfit i := by
    apply Fin.ext
    rfl
  rw [hei]
  by_cases ht : i.val = width - 1
  · have hit : i = Line.last hw := by
      apply Fin.ext
      simpa only [Line.last] using ht
    have hk := S.agree i
    have hlabel :
        (S.conf (site hfit i)).label =
          widthTerminal (by omega : 0 < width) hle := by
      apply Fin.ext
      have hv := completed_key_label _ _ hk
      have hl := congrArg Fin.val (S.line.label i)
      simp only [widthTerminal]
      omega
    have hc : (S.conf (site hfit i)).carry = false := by
      calc
        (S.conf (site hfit i)).carry = (S.line.cell i).carry :=
          completed_key_carry _ _ hk
        _ = (S.line.cell (Line.last hw)).carry := by rw [hit]
        _ = false := S.line.terminal_carry
    have hz : (S.conf (site hfit i)).reset = false := by
      exact (completed_key_reset _ _ hk).trans (S.line.reset_clear i)
    have hrow := waitWidthEntry_eq_old_of_terminal_clean
      hpsi hw hle cap
      (S.conf (site hfit i))
      (S.conf ((ring hfit).rightNeighbor (site hfit i)))
      hlabel hc hz
    unfold entryRawStep BirthShortWaitRawRing.rawStep
    rw [hrow]
  · have hi : i.val < width - 1 := by
      have hii := i.isLt
      omega
    let j : Fin width := ⟨i.val + 1, by omega⟩
    have hright :
        (ring hfit).rightNeighbor (site hfit i) = site hfit j := by
      apply Fin.ext
      rw [right_of_safe hfit (site hfit i) (site_ne_rootIncoming hfit i)]
      rfl
    have hl : (S.conf (site hfit i)).label.val < width := by
      have hk := completed_key_label _ _ (S.agree i)
      have hv := congrArg Fin.val (S.line.label i)
      have hii := i.isLt
      omega
    have hr :
        (S.conf ((ring hfit).rightNeighbor (site hfit i))).label.val < width := by
      rw [hright]
      have hk := completed_key_label _ _ (S.agree j)
      have hv := congrArg Fin.val (S.line.label j)
      have hjj := j.isLt
      omega
    have hrow := waitWidthEntry_eq_old_of_active_labels
      hpsi (by omega : 0 < width) hle cap
      (S.conf (site hfit i))
      (S.conf ((ring hfit).rightNeighbor (site hfit i))) hl hr
    unfold entryRawStep BirthShortWaitRawRing.rawStep
    rw [hrow]

/-- One root-incoming-free repaired physical letter preserves the completed
cross-carrier State.  If its initiator is on the line, reuse the frozen old
safeStep after the exact local row equality above.  If it is beyond the line,
the repaired update is kept literally and cannot touch a line cell. -/
theorem entryCompleted_safeStep {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : BirthShortWaitRawRing.State (psi := psi) hw hfit)
    (e : Fin n) (he : e ≠ rootIncoming hfit) :
    ∃ T : BirthShortWaitRawRing.State (psi := psi) hw hfit,
      T.conf = entryRawStep hpsi hw hle hfit cap S.conf e := by
  by_cases hline : e.val < width
  · let se : BirthShortWaitRawRing.SafeEdge hfit := ⟨e, he⟩
    let T := BirthShortWaitRawRing.safeStep hpsi hw hle hfit cap S se
    refine ⟨T, ?_⟩
    change (BirthShortWaitRawRing.safeStep hpsi hw hle hfit cap S se).conf =
      entryRawStep hpsi hw hle hfit cap S.conf e
    rw [BirthShortWaitRawRing.safeStep_conf]
    dsimp only [se]
    exact (entryRawStep_eq_old_of_line hpsi hw hle hfit cap S e hline).symm
  · have hge : width ≤ e.val := by omega
    refine ⟨{
      conf := entryRawStep hpsi hw hle hfit cap S.conf e
      line := S.line
      agree := ?_ }, rfl⟩
    intro i
    have hrval := right_of_safe hfit e he
    have hne : site hfit i ≠ e := by
      intro h
      have hv := congrArg Fin.val h
      have hii := i.isLt
      simp only [site] at hv
      omega
    have hnr : site hfit i ≠ (ring hfit).rightNeighbor e := by
      intro h
      have hv := congrArg Fin.val h
      rw [hrval] at hv
      have hii := i.isLt
      simp only [site] at hv
      omega
    unfold entryRawStep
    rw [updatePair_other S.conf e ((ring hfit).rightNeighbor e)
      (site hfit i) _ hne hnr]
    exact S.agree i

/-- Arbitrary root-incoming-free repaired suffixes preserve the completed
State, with the resulting physical configuration exactly the literal
`entryRawRun`.  No equality to the old `rawRun` is asserted. -/
theorem entryCompleted_safeRun {psi width n : Nat}
    (hpsi : 0 < psi) (hw : 2 ≤ width) (hle : width ≤ psi)
    (hfit : width < n) (cap : Nat)
    (S : BirthShortWaitRawRing.State (psi := psi) hw hfit)
    (es : List (Fin n)) (hkill : rootIncoming hfit ∉ es) :
    ∃ T : BirthShortWaitRawRing.State (psi := psi) hw hfit,
      T.conf = entryRawRun hpsi hw hle hfit cap S.conf es := by
  induction es generalizing S with
  | nil => exact ⟨S, rfl⟩
  | cons e es ih =>
      have he : e ≠ rootIncoming hfit := by
        intro h
        apply hkill
        simp [h]
      have ht : rootIncoming hfit ∉ es := by
        intro hm
        exact hkill (List.mem_cons_of_mem e hm)
      rcases entryCompleted_safeStep hpsi hw hle hfit cap S e he with
        ⟨S1, h1⟩
      rcases ih S1 ht with ⟨T, hT⟩
      refine ⟨T, ?_⟩
      simp only [entryRawRun]
      rw [← h1]
      exact hT

end BirthShortWaitTerminalEntryInterleaving

#print axioms BirthShortWaitTerminalEntryInterleaving.entryCompleted_safeStep
#print axioms BirthShortWaitTerminalEntryInterleaving.entryCompleted_safeRun
