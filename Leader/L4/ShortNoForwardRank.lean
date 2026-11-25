import Leader.L4.ShortDirtySweep
import Leader.L4.ShortDirtyMIS1Ring
import Leader.L4.ShortResetCycle
import Leader.L4.ShortPacketTag
import Leader.L4.ShortResetWatch

namespace L4.ShortNoForwardRank
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring ShortResetRow
open ShortDirtySweep ShortResetWatch
open ShortDirtyMIS1Ring ShortResetCycle ShortResetForwardH2 ShortResetChart ShortPacketTag

set_option maxRecDepth 8192
set_option maxHeartbeats 2500000

private theorem kind_lt {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) (j : Nat) :
    kind C x j<4 := by
  unfold kind slot oldK
  dsimp only
  rw [inherited_decode_tag]
  exact (BitVec.extractLsb' 17 2 _).isLt

private theorem kind_of_bytes {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x y : Raw s n) (j : Nat)
    (frame : bits C.route y j=bits C.route x j) : kind C y j=kind C x j := by
  unfold kind slot oldK
  dsimp only
  change (decode _ (bits C.route y j)).tag=(decode _ (bits C.route x j)).tag
  rw [frame]
  exact no_kind_change _ _ _

private theorem kind_of_normal {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x y : Raw s n) (j : Nat)
    (frame : bits C.route y j=normalizedNoForward (header x (nextAt C.root j))
      (x (nextAt C.root j)).mis1 (C.route.port j)) : kind C y j=kind C x j := by
  unfold normalizedNoForward at frame
  dsimp only at frame
  split at frame
  · unfold kind slot oldK
    dsimp only
    change (decode _ (bits C.route y j)).tag=(decode _ (bits C.route x j)).tag
    rw [frame]
    exact encode_decoded_tag _ _ _
  · exact kind_of_bytes C x y j frame

private theorem kind_of_E {s n : Nat} {h : Fin n→Bool} (C : Chart h) (y : Raw s n) (j : Nat)
    (frame : bits C.route y j=encode E) : kind C y j=0 := by
  have H := slot_of_bits C.route y j E ShortResetFlow.empty_decode frame
  exact congrArg Token.tag H

private theorem kind_of_reply {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x y : Raw s n)
    (i j : Nat) (reply : kind C x j=3)
    (frame : bits C.route y i=encode (slot C.route x j)) : kind C y i=3 := by
  unfold kind slot oldK at reply ⊢
  dsimp only at reply ⊢
  change (decode _ (bits C.route y i)).tag=3
  rw [frame]
  exact (encode_decoded_tag _ _ _).trans reply

private theorem hold_except {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n)
    (i j : Nat) (I : i<C.L) (J : j<C.L) (A : j≠i) (B : j≠i+1) :
    kind C (rawNext s x (nextAt C.root i)) j=kind C x j := by
  apply kind_of_bytes
  unfold bits
  apply congrArg ((kField (C.route.port j)).read)
  apply reset_remote_frame_raw
  · exact fun E=>A (nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) E)
  · change nextAt C.root j≠nextAt C.root (i+1)
    exact fun E=>B (nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
      (by have := C.length_lt; omega) E)

private def mass (m : Nat) (f : Nat → Nat) : Nat :=
  ((List.range m).map f).sum

private theorem mass_succ (m : Nat) (f : Nat → Nat) :
    mass (m+1) f = mass m f + f m := by
  simp [mass,List.range_succ]

private theorem mass_eq (m : Nat) (f g : Nat→Nat)
    (A : ∀ j, j<m → f j=g j) : mass m f=mass m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [mass_succ,mass_succ,ih (fun j J=>A j (by omega)),A m (by omega)]

private theorem mass_le (m : Nat) (f g : Nat→Nat)
    (A : ∀ j, j<m → f j≤g j) : mass m f≤mass m g := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    rw [mass_succ,mass_succ]
    exact Nat.add_le_add (ih (fun j J=>A j (by omega))) (A m (by omega))

private theorem mass_one (m i : Nat) (f g : Nat→Nat) (I : i<m)
    (O : ∀ j, j<m → j≠i → f j=g j) (B : f i<g i) : mass m f<mass m g := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [mass_succ,mass_succ]
    by_cases E : i=m
    · subst i
      rw [mass_eq m f g (fun j J=>O j (by omega) (by omega))]
      omega
    · rw [O m (by omega) (by omega)]
      have H := ih (by omega) (fun j J K=>O j (by omega) K)
      omega

private theorem mass_two (m i : Nat) (f g : Nat→Nat) (I : i+1<m)
    (O : ∀ j, j<m → j≠i → j≠i+1 → f j=g j)
    (B : f i+f (i+1)<g i+g (i+1)) : mass m f<mass m g := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [mass_succ,mass_succ]
    by_cases E : m=i+1
    · subst m
      rw [mass_succ,mass_succ,mass_eq i f g (fun j J=>O j (by omega) (by omega) (by omega))]
      omega
    · rw [O m (by omega) (by omega) E]
      have H := ih (by omega) (fun j J K R=>O j (by omega) K R)
      omega

def cost (i t : Nat) : Nat :=
  if t=3 then 2*i+2 else if t=1 then 1 else 0

/-- Uses only the actual chart MIS1 byte projection. -/
def rankBytes {n : Nat} {h : Fin n→Bool} (C : Chart h) (v : Fin C.L → BitVec 96) : Nat :=
  mass C.L (fun i => if I : i<C.L then
    cost i (((kField (lane C.a C.b i)).read (v ⟨i,I⟩)).extractLsb' 17 2).toNat else 0)

theorem rankBytes_eq {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n) :
    rankBytes C (projection C x) = mass C.L (fun i => cost i (kind C x i)) := by
  unfold rankBytes
  apply mass_eq
  intro i I
  rw [dif_pos I]
  congr 1
  exact (inherited_decode_tag _ _).symm

theorem rankBytes_le {n : Nat} {h : Fin n→Bool} (C : Chart h) (v : Fin C.L → BitVec 96) :
    rankBytes C v ≤ 2*C.L*C.L := by
  have H : ∀ m, mass m (fun _=>2*C.L)=2*C.L*m := by
    intro m
    induction m with
    | zero => simp [mass]
    | succ m ih => rw [mass_succ,ih,Nat.mul_succ]
  rw [←H]
  apply mass_le
  intro j J
  rw [dif_pos J]
  unfold cost
  split
  · omega
  · split <;> omega

private theorem sep_at {n : Nat} {h : Fin n→Bool} (C : Chart h) (i : Nat)
    (I : i<C.L) : nextAt C.root i≠rightNeighbor (nextAt C.root i) := by
  intro H
  have Z : nextAt C.root i=nextAt C.root (i+1) := H
  have J := nextAt_injective_under _ _ _ (by have := C.length_lt; omega)
    (by have := C.length_lt; omega) Z
  omega

private theorem nominee_mem {n : Nat} {h : Fin n→Bool} (C : Chart h) (i : Nat)
    (I : i<C.L) : nextAt C.root i ∈ watch C :=
  (mem_watch _ _).2 (.inr ⟨i,I,rfl⟩)

private theorem for_reply {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (i : Nat) (I : i+1<C.L)
    (frozen : ∀ q, header x q=h q) (nf : NoForward C x)
    (rep : kind C x (i+1)=3) :
    let e := nextAt C.root i
    let y := rawNext s x e
    NoForward C y ∧ rankBytes C (projection C y)<rankBytes C (projection C x) := by
  dsimp only
  let e := nextAt C.root i
  let y := rawNext s x e
  have iL : i<C.L := by omega
  have d : destination (header x (rightNeighbor e)) (C.route.port i)=some (C.route.port (i+1)) := by
    simpa only [Chart.route,if_pos I] using C.actual_dst x frozen i iL
  have B := dirty_nonforward_reply_raw x e (sep_at C i iL) _ _ d (nf i iL) rep
  have left := kind_of_reply C x y i (i+1) rep B.1
  have right := kind_of_E C y (i+1) B.2
  constructor
  · intro j J
    by_cases A : j=i
    · subst j; change kind C y _ ≠ 2; omega
    · by_cases B : j=i+1
      · subst j; change kind C y _ ≠ 2; omega
      · rw [hold_except C x i j iL J A B]
        exact nf j J
  · rw [rankBytes_eq,rankBytes_eq]
    apply mass_two _ i _ _ I
    · intro j J A B
      rw [hold_except C x i j iL J A B]
    · rw [left,right,rep]
      unfold cost
      simp
      omega

private theorem for_trail {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (i : Nat) (I : i<C.L)
    (frozen : ∀ q, header x q=h q) (nf : NoForward C x)
    (trail : kind C x i=1) (empty : i+1<C.L → kind C x (i+1)=0) :
    let e := nextAt C.root i
    let y := rawNext s x e
    NoForward C y ∧ rankBytes C (projection C y)<rankBytes C (projection C x) := by
  dsimp only
  let e := nextAt C.root i
  let y := rawNext s x e
  have old := nf i I
  have H : kind C y i=0 ∧ (i+1<C.L → kind C y (i+1)=0) := by
    by_cases J : i+1<C.L
    · have d : destination (header x (rightNeighbor e)) (C.route.port i)=some (C.route.port (i+1)) := by
        simpa only [Chart.route,if_pos J] using C.actual_dst x frozen i I
      have B := dirty_nonforward_empty_raw x e (sep_at C i I) _ _ d old (empty J)
      have b : bits C.route y i=if kind C x i=1 then encode E else
          normalizedNoForward (header x e) (x e).mis1 (C.route.port i) := B.1
      rw [if_pos trail] at b
      exact ⟨kind_of_E C y i b, fun _ => (kind_of_normal C x y (i+1) B.2).trans (empty J)⟩
    · have d : destination (header x (rightNeighbor e)) (C.route.port i)=none := by
        simpa only [Chart.route,if_neg J] using C.actual_dst x frozen i I
      have b : bits C.route y i=if kind C x i=1 then encode E else
          normalizedNoForward (header x e) (x e).mis1 (C.route.port i) :=
        dirty_nonforward_terminal_raw x e (sep_at C i I) _ d old
      rw [if_pos trail] at b
      exact ⟨kind_of_E C y i b,fun bad=>(J bad).elim⟩
  have same (j : Nat) (J : j<C.L) (A : j≠i) : kind C y j=kind C x j := by
    by_cases B : j=i+1
    · subst j
      exact (H.2 J).trans (empty J).symm
    · exact hold_except C x i j I J A B
  constructor
  · intro j J
    by_cases A : j=i
    · subst j
      change kind C y i ≠ 2
      rw [H.1]
      decide
    · rw [same j J A]
      exact nf j J
  · rw [rankBytes_eq,rankBytes_eq]
    apply mass_one _ i _ _ I
    · intro j J A
      rw [same j J A]
    · change cost i (kind C y i) < cost i (kind C x i)
      simp [H.1,trail,cost]

private theorem last_below (P : Nat→Prop) (m : Nat) (X : ∃ i, i<m ∧ P i) :
    ∃ i, i<m ∧ P i ∧ ∀ j, i<j → j<m → ¬ P j := by
  classical
  induction m with
  | zero => obtain ⟨i,I,_⟩ := X; omega
  | succ m ih =>
    by_cases H : P m
    · exact ⟨m,by omega,H,fun _ _ _=>by omega⟩
    · obtain ⟨i,I,F⟩ := X
      have K : i<m := by
        by_cases J : i<m
        · exact J
        · exfalso
          have e : i=m := by omega
          exact H (e ▸ F)
      obtain ⟨k,J,G,Q⟩ := ih ⟨i,K,F⟩
      exact ⟨k,by omega,G,fun j U V=>by
        by_cases E : j=m
        · exact E ▸ H
        · exact Q j U (by omega)⟩

/-- A real chart WAIT rail with no forward bytes and a root trail
has a nominated watched edge decreasing the byte-only rail rank.
The nominated edge preserves absence of forward bytes and is outgoing
from a chart slot, so is not the owner's root door. -/
theorem nominate_noForward {s n : Nat} {h : Fin n→Bool} (C : Chart h)
    (x : Raw s n) (frozen : ∀ q, header x q=h q)
    (nf : NoForward C x) (held : kind C x 0=1) :
    ∃ i : Nat, i<C.L ∧ nextAt C.root i∈watch C ∧
      NoForward C (rawNext s x (nextAt C.root i)) ∧
      rankBytes C (projection C (rawNext s x (nextAt C.root i))) <
        rankBytes C (projection C x) := by
  classical
  by_cases D : ∃ j, 0<j ∧ j<C.L ∧ kind C x j=3
  · obtain ⟨j,J,K,R⟩ := D
    cases j with
    | zero => omega
    | succ i =>
      have F := for_reply C x i K frozen nf R
      exact ⟨i,by omega,nominee_mem C i (by omega),F⟩
  · obtain ⟨i,I,T,H⟩ := last_below (fun j=>kind C x j=1) C.L ⟨0,C.positive,held⟩
    have E (J : i+1<C.L) : kind C x (i+1)=0 := by
      have U := kind_lt C x (i+1)
      have A := nf (i+1) J
      have B := H (i+1) (by omega) J
      have K : kind C x (i+1)≠3 := fun Z=>D ⟨i+1,by omega,J,Z⟩
      change kind C x (i+1)≠1 at B
      omega
    exact ⟨i,I,nominee_mem C i I,for_trail C x i I frozen nf T E⟩

end L4.ShortNoForwardRank
