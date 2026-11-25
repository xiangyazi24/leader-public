import Leader.L4.ShortGrantFrames

namespace L4.ShortGrantPersistence
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortGrantRaw BStarShort

private theorem old_eq_wire (b : BitVec 96) (j : Fin 3) :
    (headerGrantView b).old j=b.getLsbD (91-j.val) := rfl

private theorem canonical_absent (g : GrantView) (j : Fin 3) (old : g.old j=false) :
    g.canonical j=false := by
  unfold GrantView.canonical
  by_cases H : g.old 1=true
  · have J : j≠1 := fun E=>by subst j; rw [H] at old; contradiction
    simp [H,J]
  · simp [H,old]

private theorem win_absent (g : GrantView) (j : Fin 3) (no : g.ask j=false) : g.win j=false := by
  by_cases J : j=1
  · subst j
    simp [GrantView.win,GrantView.centerWin,no]
  · simp [GrantView.win,J,no]

/-- No other owner's packet can create a previously absent grant at
this lane. Only this lane's own departing ACQ may set it. -/
theorem absent_until_ask {s n : Nat} (x : Raw s n) (e i : Fin n) (j : Fin 3)
    (sep : e≠rightNeighbor e) (head : header x i=true)
    (old : (x i).mis1.getLsbD (91-j.val)=false)
    (no : e=i → (headerGrantView (x i).mis1).ask j=false) :
    (rawNext s x e i).mis1.getLsbD (91-j.val)=false := by
  let g := headerGrantView (x i).mis1
  have cap : g.canonical j=false := canonical_absent g j old
  by_cases L : i=e
  · subst i
    rw [outgoing_grant_at x e head j]
    have W := win_absent (headerGrantView (x e).mis1) j (no rfl)
    exact show (headerGrantView (x e).mis1).nextValue j=false by
      change g.nextValue j=false
      unfold GrantView.nextValue
      rw [show g.header=true from rfl,if_pos rfl,cap]
      simp only [Bool.false_and,Bool.false_or]
      exact W
  · by_cases R : i=rightNeighbor e
    · subst i
      rw [incoming_grant_at x e sep head j]
      exact cap
    · rw [reset_remote_frame_raw x e i L R]
      exact old

/-- A held coherent grant persists until its own literal
release, independently of the state of other packet lanes. -/
theorem held_until_release {s n : Nat} (x : Raw s n) (e i : Fin n) (j : Fin 3)
    (sep : e≠rightNeighbor e) (head : header x i=true)
    (C : Coherent (x i).mis1)
    (held : (x i).mis1.getLsbD (91-j.val)=true)
    (no : e=i → (headerGrantView (x i).mis1).release j=false) :
    (rawNext s x e i).mis1.getLsbD (91-j.val)=true := by
  by_cases L : i=e
  · subst i
    exact ShortGrantFrames.outgoing_coherent_grant_hold x e head C j held (no rfl)
  · by_cases R : i=rightNeighbor e
    · subst i
      exact (ShortGrantFrames.incoming_coherent_grant_frame x e sep head C j).trans held
    · rw [reset_remote_frame_raw x e i L R]
      exact held

#print axioms absent_until_ask
#print axioms held_until_release
end L4.ShortGrantPersistence
