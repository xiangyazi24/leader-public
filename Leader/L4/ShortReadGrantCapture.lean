import Leader.L4.ShortReadCaptureRaw
import Leader.L4.ShortGrantRaw

namespace L4.ShortReadGrantCapture
open AllSizeProtocol MISByteCodec PhysicalCustody
open ShortResetMIS1Ring ShortResetRow ShortGrantRaw

/-- Capturing and acquiring occur on the same immutable-header mark;
a header's actual post-mark grant is true for each winning READ lane. -/
theorem capture_winner_has_grant {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3)
    (H : header x e=true)
    (W : readWins true (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j=true) :
    (rawNext s x e e).mis1.getLsbD (91-j.val)=true := by
  rw [outgoing_grant_at x e H j]
  rw [readWins_header] at W
  unfold BStarShort.GrantView.nextValue
  rw [show (headerGrantView (x e).mis1).header=true from rfl]
  simp [W]

#print axioms capture_winner_has_grant
end L4.ShortReadGrantCapture
