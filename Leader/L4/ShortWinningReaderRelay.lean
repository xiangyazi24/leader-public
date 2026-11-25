import Leader.L4.ShortReaderTrace
import Leader.L4.ShortReadGrantCapture

namespace L4.ShortWinningReaderRelay
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1
open ShortResetMIS1Ring ShortResetRow ShortReaderTrace ShortReaderMIS1
open PhysicalShortGrantCoherence

/-- In the literal old-view allocator, a reader win already rules out an
old writer. This does not need grant coherence or any prior trace. -/
theorem winning_reader_no_old_writer (hv : Bool) (u v : BitVec 96) (j : Fin 3)
    (which : j=0 ∨ j=2) (W : readWins true hv u v j=true) :
    u.getLsbD 90=false := by
  rw [readWins_header] at W
  have old : (headerGrantView u).old 1=u.getLsbD 90 := rfl
  by_cases H : u.getLsbD 90=true
  · have C : (headerGrantView u).canonical 1=true := by
      unfold BStarShort.GrantView.canonical
      rw [old,H]
      decide
    have J : (j == 1)=false := by
      rcases which with rfl|rfl <;> decide
    simp [BStarShort.GrantView.win,J,C] at W
  · exact Bool.eq_false_iff.mpr H

/-- Relay the exact OLD value sampled on a winning reader departure,
through arbitrary real continuation marks which do not release that lane.
No assumption is made about either neighbour's ownership or traffic. -/
theorem winning_reader_protected_to_release {s n : Nat} (N : 5≤n)
    (x : Raw s n) (e : Fin n) (j : Fin 3) (which : j=0 ∨ j=2)
    (C : H2WithCoherentGrants x) (H : header x e=true)
    (W : readWins true (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j=true)
    (w : List (Fin n))
    (R : NoOwnerReleaseBefore e j (rawNext s x e) w) :
    ((rawRun (rawNext s x e) w e).mis1.getLsbD (91-j.val)=true) ∧
    selectedValue (rawRun (rawNext s x e) w e).mis1=selectedValue (x e).mis1 := by
  have A := ShortReadGrantCapture.capture_winner_has_grant x e j H W
  have F := winning_reader_no_old_writer _ _ _ j which W
  have V := no_writer_frame_raw x e e (MISByteCodec.lane 92 1 (by decide)) (.inr ⟨by decide,by decide⟩) H F
  have B := no_writer_frame_raw x e e (MISByteCodec.lane 87 2 (by decide)) (.inl ⟨by decide,by decide⟩) H F
  have H' : header (rawNext s x e) e=true :=
    (raw_h1_selected_frozen N x e e C.1.1).trans H
  have T := protected_reader_run N (rawNext s x e) e j which w
    (h2grant_closed N x e C) H' A R
  refine ⟨T.1,T.2.trans ?_⟩
  unfold selectedValue
  rw [B,V]

/-- The corresponding payload slot still names the currently selected
value at the protected physical reader. This is a local payload
equation, not a claim about the ancestry of a later returning packet. -/
theorem captured_bit_current_to_release {s n : Nat} (N : 5≤n)
    (x : Raw s n) (e : Fin n) (j : Fin 3) (which : j=0 ∨ j=2)
    (C : H2WithCoherentGrants x) (H : header x e=true)
    (W : readWins true (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j=true)
    (w : List (Fin n)) (R : NoOwnerReleaseBefore e j (rawNext s x e) w)
    (p : Nat) (P : p<128) :
    (((readCapture (x e).mis1 j p) >>> (2-j.val))%2==1)=
      selectedValue (rawRun (rawNext s x e) w e).mis1 := by
  rw [(winning_reader_protected_to_release N x e j which C H W w R).2,selectedValue_eq]
  exact (readCapture_native (x e).mis1 j p P).2

#print axioms captured_bit_current_to_release
#print axioms winning_reader_no_old_writer
#print axioms winning_reader_protected_to_release
end L4.ShortWinningReaderRelay
