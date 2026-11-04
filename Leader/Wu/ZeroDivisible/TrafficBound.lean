import Leader.Wu.ZeroDivisible.TrafficRank

/-! Bounds for the actual shared traffic rank at a legal initial holder. -/
namespace PPLLAstraR5TrafficBound
open PPLL PPLLAstraR5TrafficMove
set_option autoImplicit false

private abbrev R (ψ : Nat) : Nat := 2*ψ^2-ψ+2

private theorem reader_pos (ψ : Nat) (t : Path2Info) :
    0 < readerRank ψ t := by
  rw [PPLLAstraR5TrafficMove.readerRank_eq]
  exact PPLLAstraR5TrafficArithmetic.readerRank_pos ψ t

private theorem reader_upper (ψ : Nat) (t : Path2Info) (h4 : 4≤ψ)
    (hpos : t.position≤ψ) : readerRank ψ t≤R ψ := by
  rw [PPLLAstraR5TrafficMove.readerRank_eq]
  exact PPLLAstraR5TrafficArithmetic.readerRank_le ψ t h4 hpos

private theorem zero_gap (ψ : Nat) (t : Path2Info) (h4 : 4≤ψ)
    (hz : t.position=0) : readerRank ψ t+1≤R ψ := by
  let t' : Path2Info := {t with position:=ψ}
  have heq : readerRank ψ t + ψ = readerRank ψ t' := by
    simp [readerRank,t',hz]
    omega
  have hu := reader_upper ψ t' h4 (by simp [t'])
  omega

private theorem control_upper (ψ j : Nat) (h4 : 4≤ψ) (hj : j<ψ)
    (t : Path2Info) (ha : t.action=3 ∨ t.action=4) :
    weight ψ j t ≤ ψ := by
  rcases ha with h | h
  · by_cases hterm : j=ψ-1
    · simp [weight,h,hterm]
      omega
    · have hlt : j+1<ψ := by omega
      simp [weight,h,hterm]
      omega
  · have hs : ψ-1-j≤ψ-1 := Nat.sub_le _ _
    simp [weight,h]
    omega

private theorem control_pos (ψ j : Nat) (t : Path2Info)
    (ha : t.action=3 ∨ t.action=4) : 0<weight ψ j t := by
  rcases ha with h | h <;> simp [weight,h] <;> omega

private theorem reader_weight (ψ j : Nat) (t : Path2Info)
    (ha : t.action=1 ∨ t.action=2) :
    weight ψ j t=(ψ+1)*readerRank ψ t := by
  rcases ha with h | h <;> simp [weight,h]

private theorem rank_cap_at_least_one (ψ : Nat) (h4 : 4≤ψ) : 1≤R ψ := by
  let t : Path2Info := ⟨0,0,0,1⟩
  have hp := reader_pos ψ t
  have hu := reader_upper ψ t h4 (by simp [t])
  omega

private theorem zero_scalar_bound (ψ : Nat) (t : Path2Info) (h4 : 4≤ψ)
    (hz : t.position=0) :
    3*((ψ+1)*readerRank ψ t)+1 ≤ 3*((ψ+1)*R ψ) := by
  have hg := zero_gap ψ t h4 hz
  have hm := Nat.mul_le_mul_left (ψ+1) hg
  have hm2 : (ψ+1)*readerRank ψ t+(ψ+1) ≤ (ψ+1)*R ψ := by
    calc
      _ = (ψ+1)*(readerRank ψ t+1) := by rw [Nat.mul_add,Nat.mul_one]
      _ ≤ (ψ+1)*R ψ := hm
  omega

/-- Every allowed resident token has positive scalar traffic rank, with no
bounds on its saved label, bit, or position. -/
theorem cellRank_pos_of_present {ψ : Nat} (u : AgentState ψ)
    (hok : OkSlot u.path2) (hp : u.path2≠none) :
    0<PPLLAstraR5GlobalTraffic.cellRank u := by
  cases ht : u.path2 with
  | none => exact False.elim (hp ht)
  | some t =>
    have ha := hok t ht
    have hact : t.action=1 ∨ t.action=2 ∨ t.action=3 ∨ t.action=4 := by
      unfold Ok at ha
      omega
    have hw : 0<weight ψ u.label.val t := by
      rcases hact with h | h | h | h
      · rw [reader_weight ψ u.label.val t (Or.inl h)]
        have hr := reader_pos ψ t
        exact Nat.mul_pos (by omega) hr
      · rw [reader_weight ψ u.label.val t (Or.inr h)]
        have hr := reader_pos ψ t
        exact Nat.mul_pos (by omega) hr
      · exact control_pos ψ u.label.val t (Or.inl h)
      · exact control_pos ψ u.label.val t (Or.inr h)
    simp only [PPLLAstraR5GlobalTraffic.cellRank,PPLLAstraR5TrafficLand.P,
      PPLLAstraR5TrafficLand.Z,ht]
    omega

/-- Initial bounded-domain cap on the existing per-agent scalar rank. -/
private theorem cellRank_le_aux {ψ κ : Nat} (h4 : 4≤ψ) (u : AgentState ψ)
    (hd : AgentState.inProtocolDomain κ u) (hok : OkSlot u.path2) :
    PPLLAstraR5GlobalTraffic.cellRank u ≤ 3*((ψ+1)*R ψ) := by
  cases ht : u.path2 with
  | none =>
    simp [PPLLAstraR5GlobalTraffic.cellRank,PPLLAstraR5TrafficLand.P,
      PPLLAstraR5TrafficLand.Z,ht]
  | some t =>
    have hpos : t.position≤ψ := by
      unfold AgentState.inProtocolDomain at hd
      simp only [ht] at hd
      exact hd.2.2.1.2.2.1
    have ha := hok t ht
    have hact : t.action=1 ∨ t.action=2 ∨ t.action=3 ∨ t.action=4 := by
      unfold Ok at ha
      omega
    have hr1 : 1≤R ψ := rank_cap_at_least_one ψ h4
    have hj := u.label.isLt
    simp only [PPLLAstraR5GlobalTraffic.cellRank,PPLLAstraR5TrafficLand.P,
      PPLLAstraR5TrafficLand.Z,ht]
    rcases hact with h | h | h | h
    · have hw := reader_weight ψ u.label.val t (Or.inl h)
      have hr := reader_upper ψ t h4 hpos
      by_cases hz : t.position=0
      · have hg := zero_gap ψ t h4 hz
        have zval : (if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0)=1 := by
          simp [h,hz]
        rw [hw,zval]
        exact zero_scalar_bound ψ t h4 hz
      · rw [hw]
        have zval : (if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0)=0 := by
          simp [hz]
        rw [zval]
        simp only [Nat.add_zero]
        exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (ψ+1) hr)
    · have hw := reader_weight ψ u.label.val t (Or.inr h)
      have hr := reader_upper ψ t h4 hpos
      by_cases hz : t.position=0
      · have hg := zero_gap ψ t h4 hz
        have zval : (if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0)=1 := by
          simp [h,hz]
        rw [hw,zval]
        exact zero_scalar_bound ψ t h4 hz
      · rw [hw]
        have zval : (if (t.action == 1 || t.action == 2) && t.position == 0 then 1 else 0)=0 := by
          simp [hz]
        rw [zval]
        simp only [Nat.add_zero]
        exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (ψ+1) hr)
    · have hw := control_upper ψ u.label.val h4 hj t (Or.inl h)
      have hb : ψ≤(ψ+1)*R ψ := by
        have hm := Nat.mul_le_mul_left (ψ+1) hr1
        simp only [Nat.mul_one] at hm
        omega
      simp [h]
      exact Nat.mul_le_mul_left 3 (Nat.le_trans hw hb)
    · have hw := control_upper ψ u.label.val h4 hj t (Or.inr h)
      have hb : ψ≤(ψ+1)*R ψ := by
        have hm := Nat.mul_le_mul_left (ψ+1) hr1
        simp only [Nat.mul_one] at hm
        omega
      simp [h]
      exact Nat.mul_le_mul_left 3 (Nat.le_trans hw hb)

theorem cellRank_le_domain {ψ κ : Nat} (h4 : 4≤ψ) (u : AgentState ψ)
    (hd : AgentState.inProtocolDomain κ u) (hok : OkSlot u.path2) :
    PPLLAstraR5GlobalTraffic.cellRank u ≤ 3*(ψ+1)*(2*ψ^2-ψ+2) := by
  simpa only [R, Nat.mul_assoc] using cellRank_le_aux h4 u hd hok

/-- A legal A2 token at its maximum reader position attains the cap at ψ=4. -/
def boundWitness : AgentState 4 :=
  { leader := false, probe := false, phase := false, bit := false,
    wait := false, state := .none, path := .bot,
    reset := false, carry := false, count := 0,
    label := ⟨0, by decide⟩, h_field := false,
    path2 := some ⟨0,0,4,2⟩,
    path3 := none, path4 := none, path5 := none,
    p := false, p_carry := false, reset_cmd := false, echo := false,
    signal_B := ⟨0, by decide⟩, bullet := ⟨0, by decide⟩,
    shield := false, write_state := .none, write := .none,
    last := false, last_set := false, last_unset := false,
    b_carry := false, gen_ws := false, ws_echo := false, signal_ws := false }

theorem boundWitness_domain : AgentState.inProtocolDomain 0 boundWitness := by
  simp [AgentState.inProtocolDomain,boundWitness]

theorem boundWitness_ok : OkSlot boundWitness.path2 := by
  intro t ht
  change some (⟨0,0,4,2⟩ : Path2Info)=some t at ht
  have heq := Option.some.inj ht
  subst t
  simp [Ok]

theorem boundWitness_attains :
    PPLLAstraR5GlobalTraffic.cellRank boundWitness =
      3*(4+1)*(2*4^2-4+2) := by
  decide

theorem bounded_witness_attains :
    AgentState.inProtocolDomain 0 boundWitness ∧
    OkSlot boundWitness.path2 ∧
    PPLLAstraR5GlobalTraffic.cellRank boundWitness =
      3*(4+1)*(2*4^2-4+2) := by
  exact ⟨boundWitness_domain,boundWitness_ok,boundWitness_attains⟩

#print axioms cellRank_pos_of_present
#print axioms cellRank_le_domain
#print axioms bounded_witness_attains
end PPLLAstraR5TrafficBound
