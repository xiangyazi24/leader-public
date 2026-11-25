import Leader.L4.ShortGrantRaw

namespace L4.ShortGrantFrames
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetRow ShortGrantRaw
open ShortResetMIS1Ring (header)

/-- Canonical normalization becomes idempotent on a coherent triple. -/
theorem canonical_eq_old (u : BitVec 96) (C : Coherent u) (j : Fin 3) :
    (headerGrantView u).canonical j = u.getLsbD (91-j.val) := by
  let g := headerGrantView u
  have B : g.old 1=u.getLsbD 90 := rfl
  by_cases W : u.getLsbD 90=true
  · have R := C W
    have J : j=0 ∨ j=1 ∨ j=2 := by
      have L := j.isLt
      rcases (show j.val=0 ∨ j.val=1 ∨ j.val=2 by omega) with A|A|A
      · exact Or.inl (Fin.ext A)
      · exact Or.inr (Or.inl (Fin.ext A))
      · exact Or.inr (Or.inr (Fin.ext A))
    change (if g.old 1 then j==1 else g.old j) = _
    rw [B,W]
    rcases J with rfl|rfl|rfl
    · exact R.1.symm
    · exact W.symm
    · exact R.2.symm
  · change (if g.old 1 then j==1 else g.old j) = _
    rw [B,if_neg W]
    rfl

theorem incoming_coherent_grant_frame {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true)
    (C : Coherent (x (rightNeighbor e)).mis1) (j : Fin 3) :
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD (91-j.val)=
      (x (rightNeighbor e)).mis1.getLsbD (91-j.val) :=
  (incoming_grant_at x e sep eligible j).trans (canonical_eq_old _ C j)

/-- Once coherent, an old grant remains held on its outgoing mark
unless that exact incidence performs a release. -/
theorem outgoing_coherent_grant_hold {s n : Nat} (x : Raw s n) (e : Fin n)
    (eligible : header x e=true) (C : Coherent (x e).mis1) (j : Fin 3)
    (G : (x e).mis1.getLsbD (91-j.val)=true)
    (R : (headerGrantView (x e).mis1).release j=false) :
    (rawNext s x e e).mis1.getLsbD (91-j.val)=true := by
  have H : (headerGrantView (x e).mis1).header=true := rfl
  have D := (canonical_eq_old _ C j).trans G
  rw [outgoing_grant_at x e eligible j]
  simp only [BStarShort.GrantView.nextValue,H,if_true,D,R,Bool.not_false,Bool.and_true,Bool.true_or]

end L4.ShortGrantFrames
