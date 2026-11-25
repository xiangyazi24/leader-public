import Leader.L4.BStarLiteralDeadlineSplit
import Leader.L4.BStarRawBlockDrift
import Leader.L4.BStarRawPublicationHistory

namespace L4.BStarRawDeadlineBridge
open BStarRawBlockDrift Height
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarAcquireAnchors BStarLongFixedRouting BStarCycleGeometry
open BStarPhysicalIncrementLedger BStarIncrementLedger BStarPhysicalLiftAlignment
open BStarPhysicalLegitimate BStarPhysicalCoset BStarEpochLift BStarGrantWriterHistory
open BStarNativePointwise BStarNativePortGeometry BStarNativeNeedLift Compiler.Native
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- Literal target publication on the original old-pair initiator mark.
This tests the selected write intent, not whether visible bytes changed. -/
def BlockPublishes (x : X) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∃ lead rest, w=lead++i::rest ∧ ¬NoPublication hp (run x lead) i i

theorem blockPublishes_iff_history (x : X) (i : Fin n) (w : List (Fin n)) :
    BlockPublishes hp x i w ↔ BStarRawPublicationHistory.Publishes hp x i w := Iff.rfl

theorem least_publishes_inc {base x : X} (hh : ∃ i,oldH6 B base i=true)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P)
    (L : ClockLegit hp base hh x) (time : Fin n→Nat)
    (R : RepresentsCoset hp base x P time) (C : Coherent hh time)
    (i : Header (oldH6 B base))
    (least : ∀ q : Fin 3, time i.val≤time (neighborHeader hh i q).val)
    (pub : ¬NoPublication hp x i.val i.val) :
    incAt hp base hh x i.val=some i.val := by
  let recd := fun j : Header (oldH6 B base)=>readRecord (r:=r) x j.val
  have front (q : Fin 3) : atFront (modulus r) (recd i) (recd (neighborHeader hh i q))=true := by
    let j := neighborHeader hh i q
    have H := L.2 i q
    change Adjacent (modulus r) (recd i).tick (recd j).tick at H
    have lo : time i.val ≤ time j.val := least q
    have hi : time j.val ≤ time i.val+1 := (C i q).2
    rcases H with a|a|a
    · simpa [atFront] using (show (recd j).tick = (recd i).tick ∨ (recd j).tick = successor (modulus r) (recd i).tick from Or.inl a.symm)
    · simpa [atFront] using (show (recd j).tick = (recd i).tick ∨ (recd j).tick = successor (modulus r) (recd i).tick from Or.inr a.symm)
    · have bad := congrArg (fun z : Nat=>z%P%32) a
      have wrap := BStarBiasedLift.successor_mod P (recd j).tick pos
      have dv (z : Nat) : z%P%32=z%32 := Nat.mod_mod_of_dvd z period
      have rx : (recd i).tick%P = time i.val%P := (R i).2
      have ry : (recd j).tick%P = time j.val%P := (R j).2
      change (successor (modulus r) (recd j).tick)%P%32=(recd i).tick%P%32 at bad
      rw [M,wrap,rx,Nat.add_mod (recd j).tick 1 P,ry,←Nat.add_mod,dv,dv] at bad
      omega
  unfold incAt
  rw [dif_pos i.property,if_neg pub]
  change (match nativeClock (modulus r) (recd (neighborHeader hh i 0))
      (recd (neighborHeader hh i 1)) (recd (neighborHeader hh i 2)) with
    | .inc _ => some i.val
    | _ => none)=some i.val
  rw [self_port hh i,correct_adjacent_row _ _ _ _ (L.1 _) (L.1 _) (L.1 _) (L.2 i 0) (L.2 i 2),
    front 0,front 2]
  rfl

private theorem minimum_from {α : Type} (f : α→Nat) (a : α) :
    ∃ b, f b≤f a ∧ ∀ c,f b≤f c := by
  have search (k : Nat) : ∀ a, f a=k → ∃ b, f b≤f a ∧ ∀ c,f b≤f c := by
    induction k using Nat.strongRecOn with
    | ind k IH =>
      intro a eq
      by_cases small : ∃ b,f b<f a
      · obtain ⟨b,L⟩ := small
        obtain ⟨c,U,H⟩ := IH (f b) (eq ▸ L) b rfl
        exact ⟨c,by omega,H⟩
      · exact ⟨a,Nat.le_refl _,fun c=>Nat.le_of_not_gt (fun l=>small ⟨c,l⟩)⟩
  exact search (f a) a rfl

private theorem trace_mono (base initial : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (a b : List (Fin n)) (i : Fin n) :
    traceCount hp base initial hh start a i≤traceCount hp base initial hh start (a++b) i := by
  rw [count_concat]
  unfold traceCount
  exact count_monotone (traceCount hp base initial hh start a) (tapeInc hp base hh (run initial a) b) i (Nat.zero_le b.length)

/-- At every actual suffix prefix below the target, service of an old
globally least owner increases that owner's original-epoch lift. -/
theorem block_lifts {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P) (start : Fin n→Nat)
    (history a b : List (Fin n))
    (good : ∀ z : List (Fin n),
      let w := history++z
      ClockLegit hp base hh (run initial w) ∧
      RepresentsCoset hp base (run initial w) P (traceCount hp base initial hh start w) ∧
      Coherent hh (traceCount hp base initial hh start w))
    (i : Header (oldH6 B base))
    (least : ∀ j : Header (oldH6 B base),
      traceCount hp base initial hh start (history++a) i.val ≤
        traceCount hp base initial hh start (history++a) j.val)
    (service : BlockPublishes hp (run initial (history++a)) i.val b) :
    traceCount hp base initial hh start (history++a) i.val+1 ≤
      traceCount hp base initial hh start (history++(a++b)) i.val := by
  obtain ⟨l,f,rfl,H⟩ := service
  let C := traceCount hp base initial hh start
  let pre := (history++a)++l
  have mono := trace_mono hp base initial hh start (history++a) l i.val
  change C (history++a) i.val≤C pre i.val at mono
  have tail := trace_mono hp base initial hh start (pre++[i.val]) f i.val
  have eq : (pre++[i.val])++f=history++(a++(l++i.val::f)) := by
    simp [pre,List.append_assoc]
  rw [eq] at tail
  change C (pre++[i.val]) i.val≤C (history++(a++(l++i.val::f))) i.val at tail
  have diag : C pre i.val≤C (pre++[i.val]) i.val :=
    trace_mono hp base initial hh start pre [i.val] i.val
  by_cases moved : C (history++a) i.val < C pre i.val
  · change C (history++a) i.val+1 ≤ C (history++(a++(l++i.val::f))) i.val
    omega
  have P0 := good (a++l)
  rw [←List.append_assoc] at P0
  have still : C pre i.val=C (history++a) i.val := Nat.le_antisymm (Nat.le_of_not_gt moved) mono
  have chosen (q : Fin 3) : C pre i.val≤C pre (neighborHeader hh i q).val := by
    have N := trace_mono hp base initial hh start (history++a) l (neighborHeader hh i q).val
    change C (history++a) (neighborHeader hh i q).val≤C pre (neighborHeader hh i q).val at N
    rw [still]
    exact Nat.le_trans (least _) N
  rw [←BStarResetSchedule.run_append] at H
  have incr := least_publishes_inc hp hh P M pos period P0.1 (C pre) P0.2.1 P0.2.2 i chosen H
  have gain : C (pre++[i.val]) i.val=C pre i.val+1 := by
    unfold C traceCount
    rw [count_append_mark,incr,if_pos rfl]
  change C (history++a) i.val+1 ≤ C (history++(a++(l++i.val::f))) i.val
  omega

private theorem spike_sum {m : Nat} (k : Fin m) :
    (List.ofFn (fun j : Fin m=>if j=k then (1:Nat) else 0)).sum=1 := by
  induction m with
  | zero => exact Fin.elim0 k
  | succ m ih =>
    refine Fin.cases ?_ (fun t=>?_) k
    · rw [List.ofFn_succ,List.sum_cons]
      have z := sum_ofFn_eq (fun j : Fin m=>if j.succ=(0:Fin (m+1)) then (1:Nat) else 0)
        (fun _=>0) (fun j=>if_neg (by intro E; have K := congrArg Fin.val E; simp at K))
      rw [z,sum_ofFn_const,Nat.mul_zero,Nat.add_zero]
      rfl
    · rw [List.ofFn_succ,List.sum_cons]
      have off : (0:Fin (m+1)) ≠ t.succ := by intro E; have K := congrArg Fin.val E; simp at K
      simp only [off,Fin.succ_inj,if_false,Nat.zero_add]
      exact ih t

/-- Convert literal target publication block mass on the original
custody suffix to missed-cap+1 mass. The block provider sees the entire
fixed old raw history; no erasure of inherited in-flight commands is used. -/
theorem raw_missed_mass {base initial : X} (hh : ∃ i,oldH6 B base i=true)
    (P : Nat) (M : modulus r=2*P) (pos : 0<P) (period : 32∣P) (start : Fin n→Nat)
    (history : List (Fin n))
    (good : ∀ z : List (Fin n),
      let w := history++z
      ClockLegit hp base hh (run initial w) ∧
      RepresentsCoset hp base (run initial w) P (traceCount hp base initial hh start w) ∧
      Coherent hh (traceCount hp base initial hh start w))
    (cap lower block q blocks extra : Nat)
    (startLower : ∀ i : Header (oldH6 B base),
      lower≤traceCount hp base initial hh start history i.val)
    (service : ∀ a (i : Header (oldH6 B base)),
      traceCount hp base initial hh start (history++a) i.val≤cap →
      (∀ j : Header (oldH6 B base), traceCount hp base initial hh start (history++a) i.val≤
          traceCount hp base initial hh start (history++a) j.val) →
      n^block ≤ q*wordSum (massInd (BlockPublishes hp (run initial (history++a)) i.val)) block) :
    blocks*wordSum (massInd (fun w=>∃ i : Header (oldH6 B base),
      traceCount hp base initial hh start (history++w) i.val≤cap)) (blocks*block+extra) ≤
      q*(total (oldH6 B base)*(cap+1-lower))*n^(blocks*block+extra) := by
  let m := total (oldH6 B base)
  let T := fun (a : List (Fin n)) (i : Header (oldH6 B base))=>
    traceCount hp base initial hh start (history++a) i.val
  let d := fun (a : List (Fin n)) (j : Fin m)=>cap+1-T a (atIndex hh j)
  let D := fun a=>(List.ofFn (d a)).sum
  let Miss := fun a=> ∃ i,T a i≤cap
  have mono (a b : List (Fin n)) (i : Header (oldH6 B base)) : T a i≤T (a++b) i := by
    dsimp [T]
    rw [←List.append_assoc]
    exact trace_mono hp base initial hh start (history++a) b i.val
  have dm (a b : List (Fin n)) (j : Fin m) : d (a++b) j≤d a j :=
    Nat.sub_le_sub_left (mono a b _) _
  have char (a : List (Fin n)) : 0<D a ↔ Miss a := by
    constructor
    · intro H
      refine Classical.byContradiction fun N => ?_
      have Z (j : Fin m) : d a j=0 := by
        have h : ¬T a (atIndex hh j)≤cap := fun l=>N ⟨_,l⟩
        dsimp [d]
        omega
      have eq := (sum_ofFn_eq (d a) (fun _=>0) Z).trans (sum_ofFn_const m 0)
      change D a=m*0 at eq
      omega
    · intro H
      obtain ⟨i,L⟩ := H
      let k := index hh i
      have U : 1≤d a k := by
        change 1≤cap+1-T a (atIndex hh (index hh i))
        rw [atIndex_index]
        omega
      have L := sum_ofFn_le (fun j=>if j=k then 1 else 0) (d a) (fun j=>by
        by_cases E : j=k
        · simp only [E]; exact U
        · simp [E])
      have one := spike_sum k
      rw [one] at L
      exact L
  let least := fun (a : List (Fin n)) (H : 0<D a)=>
    Classical.choose (minimum_from (T a) (Classical.choose ((char a).mp H)))
  have leLeast (a : List (Fin n)) (H : 0<D a) (i) : T a (least a H)≤T a i :=
    (Classical.choose_spec (minimum_from (T a) (Classical.choose ((char a).mp H)))).2 i
  have under (a : List (Fin n)) (H : 0<D a) : T a (least a H)≤cap :=
    Nat.le_trans (leLeast a H _) (Classical.choose_spec ((char a).mp H))
  let S := fun a b=>∃ H : 0<D a, BlockPublishes hp (run initial (history++a)) (least a H).val b
  have spend (a b : List (Fin n)) (_ : b.length=block) (H : S a b) (_ : 0<D a) :
      D (a++b)+1≤D a := by
    obtain ⟨h,H⟩ := H
    let i := least a h
    let k := index hh i
    have raise : T a i+1≤T (a++b) i :=
      block_lifts hp hh P M pos period start history a b good i (leLeast a h) H
    have pay : d (a++b) k+1≤d a k := by
      change cap+1-T (a++b) (atIndex hh (index hh i))+1≤cap+1-T a (atIndex hh (index hh i))
      rw [atIndex_index]
      have U := under a h
      change T a i≤cap at U
      omega
    have tt := sum_ofFn_le (fun j=>d (a++b) j+(if j=k then 1 else 0))
      (d a) (fun j=>by
        by_cases E : j=k
        · simpa [E] using pay
        · simpa [E] using dm a b j)
    rw [sum_ofFn_add] at tt
    have one := spike_sum k
    rw [one] at tt
    exact tt
  have countService (a : List (Fin n)) (H : 0<D a) :
      n^block≤q*wordSum (massInd (S a)) block := by
    apply Nat.le_trans (service a (least a H) (under a H) (leLeast a H))
    apply Nat.mul_le_mul_left
    apply wordSum_mono
    intro b
    by_cases A : BlockPublishes hp (run initial (history++a)) (least a H).val b
    · have yes : S a b := ⟨H,A⟩
      simp [massInd,A,yes]
    · simp [massInd,A]
  have result := miss_bound D S block q (fun a b=>sum_ofFn_le _ _ (dm a b))
    spend countService blocks extra
  have initBound : D [] ≤ m*(cap+1-lower) := by
    have W := sum_ofFn_le (d []) (fun _=>cap+1-lower) (fun j=>by
      have A := startLower (atIndex hh j)
      apply Nat.sub_le_sub_left
      simpa [T] using A)
    rwa [sum_ofFn_const] at W
  have eq := wordSum_congr (massInd Miss) (massInd (fun w=>0<D w)) (fun w=>by
    have i := char w
    by_cases H : Miss w
    · simp [massInd,H,i.mpr H]
    · simp [massInd,H,mt i.mp H]) (blocks*block+extra)
  change blocks*wordSum (massInd Miss) (blocks*block+extra) ≤ _
  rw [eq]
  exact Nat.le_trans result (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left q initBound))

end L4.BStarRawDeadlineBridge
