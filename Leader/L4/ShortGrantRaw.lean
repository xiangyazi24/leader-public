import Leader.L4.ShortResetMIS1Ring
import Leader.L4.ShortResetRow

namespace L4.ShortGrantRaw
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetRow
open ShortResetMIS1Ring (header pairHeader pairIn)

/-- A writer and either reader may not simultaneously hold grants at
this header. Two readers may coexist. -/
def Coherent (u : BitVec 96) : Prop :=
  u.getLsbD 90 = true → u.getLsbD 91 = false ∧ u.getLsbD 89 = false

private theorem receiver_canonical (g : BStarShort.GrantView)
    (C : g.canonical 1=true) : g.canonical 0=false ∧ g.canonical 2=false := by
  cases A : g.old 1
  · simp [BStarShort.GrantView.canonical,A] at C
  · simp [BStarShort.GrantView.canonical,A]

private theorem outgoing_view_coherent (g : BStarShort.GrantView) (H : g.header=true)
    (C : g.nextValue 1=true) : g.nextValue 0=false ∧ g.nextValue 2=false := by
  by_cases A : g.canonical 1=true
  · obtain ⟨B,D⟩ := receiver_canonical g A
    simp [BStarShort.GrantView.nextValue,H,BStarShort.GrantView.win,A,B,D]
  · have N : g.canonical 1=false := Bool.eq_false_iff.mpr A
    have W : g.centerWin=true := by
      simpa [BStarShort.GrantView.nextValue,H,BStarShort.GrantView.win,N] using C
    have E := W
    unfold BStarShort.GrantView.centerWin at E
    have B : g.canonical 0=false := by
      have Y := (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp E).1).1).2
      simpa using Y
    have D : g.canonical 2=false := by
      have Y := (Bool.and_eq_true_iff.mp E).2
      simpa using Y
    simp [BStarShort.GrantView.nextValue,H,BStarShort.GrantView.win,W,B,D]

private theorem grant_work_left {s n : Nat} (x : Raw s n) (e : Fin n) (i : Nat) (B : i<93) :
    (rawNext s x e e).mis1.getLsbD i =
      (((BStarShort.shortMIS (pairHeader x e) (pairIn x e)).1.apply (x e).mis1)).getLsbD i := by
  have h : ¬ShortGeo.mis.owned i := fun F => by have V := F.1; change 93≤i at V; omega
  rw [show rawNext s x e e=(largePair (rows s) (x e,x (rightNeighbor e))).1 by
    simp [rawNext,AllSizeS1Geometry.step]]
  exact (ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) _ h).1

private theorem grant_work_right {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (i : Nat) (B : i<93) :
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD i =
      (((BStarShort.shortMIS (pairHeader x e) (pairIn x e)).2.apply
        (x (rightNeighbor e)).mis1)).getLsbD i := by
  have h : ¬ShortGeo.mis.owned i := fun F => by have V := F.1; change 93≤i at V; omega
  rw [show rawNext s x e (rightNeighbor e)=(largePair (rows s) (x e,x (rightNeighbor e))).2 by
    simp [rawNext,AllSizeS1Geometry.step,Ne.symm sep]]
  exact (ShortGeo.work_agrees_outside _ 3 (pairHeader x e) (pairIn x e)
    (BStarShort.shortMIS (pairHeader x e) (pairIn x e)) _ h).2

/-- On an actual outgoing mark, the left header's full grant equation is
the old-view canonical/release/acquire update. -/
theorem outgoing_grant_at {s n : Nat} (x : Raw s n) (e : Fin n)
    (eligible : header x e=true) (j : Fin 3) :
    (rawNext s x e e).mis1.getLsbD (91-j.val)=(headerGrantView (x e).mis1).nextValue j := by
  rw [grant_work_left x e (91-j.val) (by omega)]
  simpa only [pairHeader,pairIn,eligible] using
    grant_left_short (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j

/-- Incoming route and any old-pair COMMIT do not alter the receiver's
grant lane beyond canonical normalization of its own old vector. -/
theorem incoming_grant_at {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true) (j : Fin 3) :
    (rawNext s x e (rightNeighbor e)).mis1.getLsbD (91-j.val)=
      (headerGrantView (x (rightNeighbor e)).mis1).canonical j := by
  rw [grant_work_right x e sep (91-j.val) (by omega)]
  simpa only [pairHeader,pairIn,eligible] using
    grant_right_short (header x e) (x e).mis1 (x (rightNeighbor e)).mis1 j

theorem outgoing_coherent_at {s n : Nat} (x : Raw s n) (e : Fin n)
    (eligible : header x e=true) : Coherent (rawNext s x e e).mis1 := by
  intro W
  have G := outgoing_grant_at x e eligible
  have E0 : (rawNext s x e e).mis1.getLsbD 91=(headerGrantView (x e).mis1).nextValue 0 := G 0
  have E1 : (rawNext s x e e).mis1.getLsbD 90=(headerGrantView (x e).mis1).nextValue 1 := G 1
  have E2 : (rawNext s x e e).mis1.getLsbD 89=(headerGrantView (x e).mis1).nextValue 2 := G 2
  rw [E0,E2]
  exact outgoing_view_coherent _ rfl (E1.symm.trans W)

theorem incoming_coherent_at {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x (rightNeighbor e)=true) :
    Coherent (rawNext s x e (rightNeighbor e)).mis1 := by
  intro W
  have G := incoming_grant_at x e sep eligible
  have E0 : (rawNext s x e (rightNeighbor e)).mis1.getLsbD 91=
    (headerGrantView (x (rightNeighbor e)).mis1).canonical 0 := G 0
  have E1 : (rawNext s x e (rightNeighbor e)).mis1.getLsbD 90=
    (headerGrantView (x (rightNeighbor e)).mis1).canonical 1 := G 1
  have E2 : (rawNext s x e (rightNeighbor e)).mis1.getLsbD 89=
    (headerGrantView (x (rightNeighbor e)).mis1).canonical 2 := G 2
  rw [E0,E2]
  exact receiver_canonical _ (E1.symm.trans W)

theorem coherent_next_at {s n : Nat} (x : Raw s n) (e i : Fin n)
    (sep : e≠rightNeighbor e) (eligible : header x i=true) (old : Coherent (x i).mis1) :
    Coherent (rawNext s x e i).mis1 := by
  by_cases E : i=e
  · subst i
    exact outgoing_coherent_at x e eligible
  by_cases R : i=rightNeighbor e
  · subst i
    exact incoming_coherent_at x e sep eligible
  · rw [ShortResetMIS1Ring.reset_remote_frame_raw x e i E R]
    exact old

#print axioms outgoing_grant_at
#print axioms incoming_grant_at
#print axioms outgoing_coherent_at
#print axioms incoming_coherent_at
#print axioms coherent_next_at
end L4.ShortGrantRaw
