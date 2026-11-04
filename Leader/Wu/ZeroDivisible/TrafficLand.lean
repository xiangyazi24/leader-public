import Leader.Wu.ZeroDivisible.TrafficMove

/-!
# Coordinate bounds for the actual R1 reader landers

The numerical scale is the agent parameter psi, and weights are the same
ones as TrafficMove. Each holder has its own occupied main path; its payload
and all saved token fields remain arbitrary Nats. Neither leaders nor main
states are restricted. These results concern the landers, not the preceding
wave emitter or the complete R5 row.
-/
namespace PPLLAstraR5TrafficLand
open PPLL PPLLFableDesignR1
set_option autoImplicit false

/-- One holder's contribution to TrafficMove's first coordinate at scale psi. -/
def P {ψ : Nat} (u : AgentState ψ) : Nat :=
  match u.path2 with
  | none => 0
  | some t => PPLLAstraR5TrafficMove.weight ψ u.label.val t

/-- One holder's count of zero-position readers, excluding verdict controls. -/
def Z {ψ : Nat} (u : AgentState ψ) : Nat :=
  match u.path2 with
  | none => 0
  | some t => if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0

/-- Indicator that the specified lander consumes its action at position zero. -/
def fires {ψ : Nat} (action : Nat) (u : AgentState ψ) : Nat :=
  match u.path2 with
  | none => 0
  | some t => if t.action == action && t.position == 0 then 1 else 0

/-- The holder's occupied path label is its physical label; the payload is raw. -/
def Own {ψ : Nat} (u : AgentState ψ) : Prop := ∃ b,u.path=.some u.label.val b

/-- Strict lexicographic decrease of the same two numerical coordinates. -/
def LexLt {ψ : Nat} (v u : AgentState ψ) : Prop :=
  P v<P u ∨ (P v=P u ∧ Z v<Z u)

/-- The holder decomposition is literally the shared pair potential. -/
theorem pair_coordinates {ψ : Nat} (l r : AgentState ψ) :
    PPLLAstraR5TrafficMove.potential ψ l r = (P l+P r,Z l+Z r) := by
  cases hl : l.path2 <;> cases hr : r.path2 <;>
    simp [PPLLAstraR5TrafficMove.potential,P,Z,hl,hr]

private theorem fires_bound {ψ : Nat} (a : Nat) (u : AgentState ψ) : fires a u≤1 := by
  unfold fires
  split
  · omega
  · split <;> omega

private theorem reader_positive (ψ j : Nat) (t : Path2Info)
    (ha : t.action=1 ∨ t.action=2) :
    ψ+1≤PPLLAstraR5TrafficMove.weight ψ j t := by
  have hr := PPLLAstraR5TrafficArithmetic.readerRank_pos ψ t
  rw [← PPLLAstraR5TrafficMove.readerRank_eq] at hr
  have hm := Nat.mul_le_mul_left (ψ+1) (show 1≤PPLLAstraR5TrafficMove.readerRank ψ t by omega)
  simp only [Nat.mul_one] at hm
  rcases ha with ha | ha <;> simpa [PPLLAstraR5TrafficMove.weight,ha] using hm

private theorem control3_bound (ψ j : Nat) (hj : j<ψ) :
    PPLLAstraR5TrafficMove.weight ψ j ⟨0,0,0,3⟩≤ψ := by
  simp only [PPLLAstraR5TrafficMove.weight,Nat.reduceBEq,Bool.false_or,Bool.false_eq_true,
    if_false,if_true]
  split <;> rename_i h <;> simp_all <;> omega

private theorem control4_bound (ψ j : Nat) (hj : j<ψ) :
    PPLLAstraR5TrafficMove.weight ψ j ⟨0,0,0,4⟩≤ψ := by
  simp [PPLLAstraR5TrafficMove.weight]
  omega

private theorem backward_weight (ψ j oldBit newBit : Nat) :
    PPLLAstraR5TrafficMove.weight ψ j ⟨j,newBit,ψ,1⟩ =
      PPLLAstraR5TrafficMove.weight ψ j ⟨j,oldBit,0,2⟩ := by
  rfl

private theorem forward_weight (ψ j bit : Nat) (hj : j<ψ-1) :
    PPLLAstraR5TrafficMove.weight ψ j ⟨j+1,0,ψ-1,2⟩ =
      PPLLAstraR5TrafficMove.weight ψ j ⟨j,bit,0,1⟩ := by
  have hr := PPLLAstraR5TrafficArithmetic.forward_turnaround ψ j bit hj
  change PPLLAstraR5TrafficMove.readerRank ψ ⟨j+1,0,ψ-1,2⟩ =
    PPLLAstraR5TrafficMove.readerRank ψ ⟨j,bit,0,1⟩ at hr
  simp only [PPLLAstraR5TrafficMove.weight,Nat.reduceBEq,Bool.false_or,Bool.true_or,if_true]
  rw [hr]

/-- Backward landing never increases P and removes exactly the active A2-zero
reader. Authentic turnaround preserves P, even with an arbitrary path payload. -/
theorem backward_coordinates {ψ : Nat} (h4 : 4≤ψ) (u : AgentState ψ) (ho : Own u) :
    P (landBackward u)≤P u ∧ Z (landBackward u)+fires 2 u=Z u := by
  rcases ho with ⟨b,hpath⟩
  cases ht : u.path2 with
  | none => simp [landBackward,ht,P,Z,fires]
  | some t =>
    rcases t with ⟨tl,tb,tp,ta⟩
    by_cases ha : ta=2 ∧ tp=0
    · rcases ha with ⟨rfl,rfl⟩
      by_cases hm : tl=u.label.val
      · subst tl
        have hw := backward_weight ψ u.label.val tb b
        have hp : ψ≠0 := by omega
        simpa [landBackward,ht,hpath,P,Z,fires,PPLLAstraR5TrafficMove.weight,
          PPLLAstraR5TrafficMove.readerRank,hp] using And.intro (Nat.le_of_eq hw) (show 0+1=1 by rfl)
      · simp [landBackward,ht,hpath,hm,P,Z,fires,PPLLAstraR5TrafficMove.weight]
    · have hf : (ta==2 && tp==0)=false := by simp_all
      simp [landBackward,ht,hpath,ha,P,Z,fires,hf]

/-- Forward landing never increases P and removes exactly the active A1-zero
reader, including terminal leader assignment. Own-path matching bounds only
the carried path label; saved labels, bits and positions remain unrestricted. -/
theorem forward_coordinates {ψ : Nat} (h4 : 4≤ψ) (κ : Nat) (u : AgentState ψ) (ho : Own u) :
    P (landForward κ false true u)≤P u ∧ Z (landForward κ false true u)+fires 1 u=Z u := by
  rcases ho with ⟨b,hpath⟩
  cases ht : u.path2 with
  | none => simp [landForward,ht,P,Z,fires]
  | some t =>
    rcases t with ⟨tl,tb,tp,ta⟩
    by_cases ha : ta=1 ∧ tp=0
    · rcases ha with ⟨rfl,rfl⟩
      by_cases hm : tl=u.label.val ∧ waveState u.state=true
      · rcases hm with ⟨rfl,hstate⟩
        by_cases hb : tb=(if u.bit then 1 else 0)
        · by_cases hj : u.label.val=ψ-1
          · simp [landForward,ht,hpath,hstate,hb,hj,P,Z,fires,PPLLAstraR5TrafficMove.weight]
          · have hjlt : u.label.val<ψ-1 := by have := u.label.isLt; omega
            have hw := forward_weight ψ u.label.val tb hjlt
            have hp : ψ-1≠0 := by omega
            simpa [landForward,ht,hpath,hstate,hb,hj,P,Z,fires,hp] using
              And.intro (Nat.le_of_eq hw) (show 0+1=1 by rfl)
        · have hold := reader_positive ψ u.label.val ⟨u.label.val,tb,0,1⟩ (Or.inl rfl)
          by_cases hgt : tb>(if u.bit then 1 else 0)
          · have hnew := control4_bound ψ u.label.val u.label.isLt
            have hle : PPLLAstraR5TrafficMove.weight ψ u.label.val ⟨0,0,0,4⟩ ≤
                PPLLAstraR5TrafficMove.weight ψ u.label.val ⟨u.label.val,tb,0,1⟩ := by omega
            simpa [landForward,ht,hpath,hstate,hb,hgt,P,Z,fires] using
              And.intro hle (show 0+1=1 by rfl)
          · have hnew := control3_bound ψ u.label.val u.label.isLt
            have hle : PPLLAstraR5TrafficMove.weight ψ u.label.val ⟨0,0,0,3⟩ ≤
                PPLLAstraR5TrafficMove.weight ψ u.label.val ⟨u.label.val,tb,0,1⟩ := by omega
            simpa [landForward,ht,hpath,hstate,hb,hgt,P,Z,fires] using
              And.intro hle (show 0+1=1 by rfl)
      · simp [landForward,ht,hpath,hm,P,Z,fires,PPLLAstraR5TrafficMove.weight]
    · have hf : (ta==1 && tp==0)=false := by simp_all
      simp [landForward,ht,hpath,ha,P,Z,fires,hf]

private theorem inactive_backward {ψ : Nat} (u : AgentState ψ) (h : fires 2 u=0) :
    landBackward u=u := by
  cases ht : u.path2 with
  | none => simp [landBackward,ht]
  | some t =>
    have ha : ¬(t.action=2 ∧ t.position=0) := by
      intro ha; simp [fires,ht,ha.1,ha.2] at h
    cases hp : u.path <;> simp [landBackward,ht,hp,ha]

private theorem inactive_forward {ψ : Nat} (κ : Nat) (u : AgentState ψ) (h : fires 1 u=0) :
    landForward κ false true u=u := by
  cases ht : u.path2 with
  | none => simp [landForward,ht]
  | some t =>
    have ha : ¬(t.action=1 ∧ t.position=0) := by
      intro ha; simp [fires,ht,ha.1,ha.2] at h
    cases hp : u.path <;> simp [landForward,ht,hp,ha]

private theorem strict_of_coordinates {ψ : Nat} (a : Nat) (u v : AgentState ψ)
    (hc : P v≤P u ∧ Z v+fires a u=Z u) (hf : fires a u=1) : LexLt v u := by
  unfold LexLt
  by_cases h : P v<P u
  · exact Or.inl h
  · right; constructor <;> omega

/-- A backward lander strictly decreases (P,Z) exactly on an A2 at position zero. -/
theorem backward_strict_iff {ψ : Nat} (h4 : 4≤ψ) (u : AgentState ψ) (ho : Own u) :
    LexLt (landBackward u) u ↔ fires 2 u=1 := by
  constructor
  · intro hs
    have hb := fires_bound 2 u
    by_cases hf : fires 2 u=0
    · rw [inactive_backward u hf] at hs
      simp [LexLt] at hs
    · omega
  · exact strict_of_coordinates 2 u _ (backward_coordinates h4 u ho)

/-- A forward lander strictly decreases (P,Z) exactly on an A1 at position zero;
this includes the branch that sets the holder's leader bit. -/
theorem forward_strict_iff {ψ : Nat} (h4 : 4≤ψ) (κ : Nat) (u : AgentState ψ) (ho : Own u) :
    LexLt (landForward κ false true u) u ↔ fires 1 u=1 := by
  constructor
  · intro hs
    have hb := fires_bound 1 u
    by_cases hf : fires 1 u=0
    · rw [inactive_forward κ u hf] at hs
      simp [LexLt] at hs
    · omega
  · exact strict_of_coordinates 1 u _ (forward_coordinates h4 κ u ho)

/-- Independent landers preserve the pair coordinate bound and pay exactly
one Z unit for each already-zero reader on its correct landing side. -/
theorem pair_landing_coordinates {ψ : Nat} (h4 : 4≤ψ) (κ : Nat) (l r : AgentState ψ)
    (hl : Own l) (hr : Own r) :
    PPLLAstraR5TrafficMove.P (landBackward l) (landForward κ false true r)≤
      PPLLAstraR5TrafficMove.P l r ∧
    PPLLAstraR5TrafficMove.Z (landBackward l) (landForward κ false true r)+fires 2 l+fires 1 r=
      PPLLAstraR5TrafficMove.Z l r := by
  have hb := backward_coordinates h4 l hl
  have hf := forward_coordinates h4 κ r hr
  simp only [PPLLAstraR5TrafficMove.P,PPLLAstraR5TrafficMove.Z,pair_coordinates]
  constructor <;> omega

#print axioms backward_coordinates
#print axioms forward_coordinates
#print axioms backward_strict_iff
#print axioms forward_strict_iff
#print axioms pair_landing_coordinates
end PPLLAstraR5TrafficLand
