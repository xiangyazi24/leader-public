import Leader.L4.Height.ClockMeanAlt

namespace L4.Height.FencePathEnvelope

open Classical

private theorem path_count_le (H : Nat) :
    2*H*H*2^(2*H-1) ≤ 2^(4*H+1) := by
  have h := Thru.self_le_two_pow H
  have q : 2*H*H ≤ 2*2^H*2^H :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 h) h
  have d : 2*H-1≤2*H := Nat.sub_le _ _
  calc
    _ ≤ 2*2^H*2^H*2^(2*H) :=
      Nat.mul_le_mul q (Nat.pow_le_pow_right (by decide : 0<2) d)
    _ = (2^H*2^H)*(2^(2*H)*2^1) := by rw [Nat.pow_one]; ac_rfl
    _ = 2^(4*H+1) := by
      rw [←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]
      congr 1
      omega

/-- A finite two-line crossing envelope. The family lists dependency
paths, not independent experiments: all costs are evaluated on the
very same finite raw candidate word. Each node may use at most two
adapted strict stop queries. The accepted factor-16 query bound and
the dyadic maximum conversion give ample room below 128 n H. -/
theorem two_line_mean {S : Type} {n : Nat}
    (next : S→Fin n→S) (x : S) (H horizon : Nat) (hn : 0<n) (hH : 0<H)
    (paths : List (List (S→Prop))) (hne : paths≠[])
    (count : paths.length≤2*H*H*2^(2*H-1))
    (length : ∀ qs,qs∈paths→qs.length≤2*(2*H-1))
    (perQuery : ∀ qs,qs∈paths→∀ A,A∈qs→∀ y,Thru.MomentAt next A (4*n) y)
    (actual : Thru.Word n→Nat)
    (dominated : ∀ w, actual w≤min
      (Thru.maxWait (paths.map (fun qs=>strictSeq next qs x)) w) horizon) :
    Thru.wordSum actual horizon≤92*n*H*n^horizon := by
  let L := 4*n
  let Ws := paths.map (fun qs=>strictSeq next qs x)
  let M := 2^(16*H)
  have L0 : 1≤L := by dsimp [L]; omega
  have wsne : Ws≠[] := fun e=>hne (List.map_eq_nil_iff.mp e)
  have pathM (W : Thru.Word n→Nat) (mem : W∈Ws) :
      Thru.wordSum (fun u=>2^(min (W u) horizon/L)) horizon≤M*n^horizon := by
    obtain ⟨qs,belongs,rfl⟩ := List.mem_map.mp mem
    have h := strictSeq_moment next L L0 qs (perQuery qs belongs) x horizon
    have len := length qs belongs
    have hp := Nat.pow_le_pow_right (by decide : 0<16) (show qs.length≤4*H by omega)
    have E : 16^(4*H)=M := by
      change (2^4)^(4*H)=2^(16*H)
      rw [←Nat.pow_mul]
      congr 1
      omega
    rw [E] at hp
    exact Nat.le_trans h (Nat.mul_le_mul_right _ hp)
  have maxM := Thru.max_moment_bound Ws wsne L M horizon pathM
  have countWs : Ws.length≤2^(4*H+1) := by
    unfold Ws
    rw [List.length_map]
    exact Nat.le_trans count (path_count_le H)
  have p : Thru.wordSum (fun w=>2^(actual w/L)) horizon≤2^(20*H+1)*n^horizon := by
    apply Nat.le_trans (Thru.wordSum_mono _ _ (fun w=>
      Nat.pow_le_pow_right (by decide : 0<2) (Nat.div_le_div_right (dominated w))) horizon)
    apply Nat.le_trans maxM
    apply Nat.le_trans (Nat.mul_le_mul_right _ countWs)
    apply Nat.le_of_eq
    unfold M
    rw [←Nat.mul_assoc,←Nat.pow_add]
    congr 2
    omega
  have avg := Thru.mean_of_moment actual L (20*H+1) horizon L0 p
  apply Nat.le_trans avg
  apply Nat.mul_le_mul_right
  have h : 4*(20*H+1+2)≤92*H := by omega
  exact Nat.le_trans (Nat.le_of_eq (by dsimp [L]; ac_rfl))
    (Nat.le_trans (Nat.mul_le_mul_left n h) (Nat.le_of_eq (by ac_rfl)))

end L4.Height.FencePathEnvelope
