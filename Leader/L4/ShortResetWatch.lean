import Leader.L4.ShortResetCycle

namespace L4.ShortResetWatch
open AllSizeProtocol MISByteCodec PhysicalCustody PhysicalCustody.H1
open ShortResetChart ShortResetCycle ShortResetMIS1Ring ShortResetForwardH2

/-- Exact alphabet of marks incident to the L slots of one owner:
the root inbound edge, then the L successive outgoing edges. -/
def watch {n : Nat} {h : Fin n → Bool} (C : Chart h) : List (Fin n) :=
  incoming C.root :: List.ofFn (fun i : Fin C.L => nextAt C.root i.val)

theorem watch_length {n : Nat} {h : Fin n → Bool} (C : Chart h) :
    (watch C).length=C.L+1 := by simp [watch]

theorem watch_bound {n : Nat} {h : Fin n → Bool} (C : Chart h) (B : C.L≤9) :
    (watch C).length≤10 := by rw [watch_length]; omega

theorem watch_nodup {n : Nat} {h : Fin n → Bool} (C : Chart h) :
    (watch C).Nodup := by
  unfold watch
  apply List.nodup_cons.mpr
  constructor
  · intro H
    obtain ⟨i,I⟩ := List.mem_ofFn.mp H
    have F : nextAt C.root (i.val+1)=nextAt C.root 0 :=
      (congrArg rightNeighbor I).trans (incoming_spec C.root)
    have L := C.length_lt
    have J := i.isLt
    have K := nextAt_injective_under C.root (i.val+1) 0 (by omega) (by omega) F
    omega
  · rw [List.Nodup,List.pairwise_iff_getElem]
    intro i j I J IJ
    simp only [List.getElem_ofFn]
    intro E
    have L := C.length_lt
    simp only [List.length_ofFn] at I J
    have G := nextAt_injective_under C.root i j (Nat.lt_trans I L) (Nat.lt_trans J L) E
    omega

private theorem right_inj {n : Nat} {u v : Fin n} (E : rightNeighbor u=rightNeighbor v) :
    u=v := by
  apply Fin.ext
  have F := congrArg Fin.val E
  change (u.val+1)%n=(v.val+1)%n at F
  have a := u.isLt
  have b := v.isLt
  by_cases U : u.val+1<n
  · rw [Nat.mod_eq_of_lt U] at F
    by_cases V : v.val+1<n
    · rw [Nat.mod_eq_of_lt V] at F; omega
    · rw [show v.val+1=n by omega,Nat.mod_self] at F; omega
  · rw [show u.val+1=n by omega,Nat.mod_self] at F
    by_cases V : v.val+1<n
    · rw [Nat.mod_eq_of_lt V] at F; omega
    · omega

theorem mem_watch {n : Nat} {h : Fin n → Bool} (C : Chart h) (e : Fin n) :
    e∈watch C ↔ e=incoming C.root ∨ ∃ i : Nat, i<C.L ∧ e=nextAt C.root i := by
  simp only [watch,List.mem_cons,List.mem_ofFn]
  constructor
  · intro H
    rcases H with H|⟨i,E⟩
    · exact .inl H
    · exact .inr ⟨i.val,i.isLt,E.symm⟩
  · intro H
    rcases H with H|⟨i,I,E⟩
    · exact .inl H
    · exact .inr ⟨⟨i,I⟩,E.symm⟩

theorem watch_incident {n : Nat} {h : Fin n → Bool} (C : Chart h) (e : Fin n) :
    e∈watch C ↔ ∃ i : Nat, i<C.L ∧
      (nextAt C.root i=e ∨ nextAt C.root i=rightNeighbor e) := by
  rw [mem_watch]
  constructor
  · intro H
    rcases H with H|⟨i,I,H⟩
    · exact ⟨0,C.positive,.inr (by rw [H,incoming_spec]; rfl)⟩
    · exact ⟨i,I,.inl H.symm⟩
  · rintro ⟨i,I,H|H⟩
    · exact .inr ⟨i,I,H.symm⟩
    · cases i with
      | zero => exact .inl (right_inj (H.symm.trans (incoming_spec C.root).symm))
      | succ j => exact .inr ⟨j,by omega,(right_inj H).symm⟩

/-- Outside marks do not modify any MIS1 byte of the owner chart. This
includes the entirety of the owner's root PC, banks, grants and lanes.
No condition on the bytes or protocol phase is needed. -/
theorem outside_byte {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (E : e∉watch C) (i : Nat) (I : i<C.L) :
    (rawNext s x e (nextAt C.root i)).mis1=(x (nextAt C.root i)).mis1 :=
  reset_remote_frame_raw x e _ (fun H=>E ((watch_incident C e).mpr ⟨i,I,.inl H⟩))
    (fun H=>E ((watch_incident C e).mpr ⟨i,I,.inr H⟩))

theorem outside_root {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (E : e∉watch C) :
    (rawNext s x e C.root).mis1=(x C.root).mis1 :=
  outside_byte C x e E 0 C.positive

/-- The chart projection includes full MIS1 bytes, and hence every chart
slot and both phase and opcode bits of the actual root. -/
def projection {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) :
    Fin C.L → BitVec 96 := fun i => (x (nextAt C.root i.val)).mis1

theorem outside_projection {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (E : e∉watch C) :
    projection C (rawNext s x e)=projection C x :=
  funext (fun i=>outside_byte C x e E i.val i.isLt)

theorem outside_slot {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (E : e∉watch C) (i : Nat) (I : i<C.L) :
    bits C.route (rawNext s x e) i=bits C.route x i := by
  change (kField (lane C.a C.b i)).read (rawNext s x e (nextAt C.root i)).mis1=_
  rw [outside_byte C x e E i I]
  rfl

theorem outside_pc {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (E : e∉watch C) :
    get (rawNext s x e C.root).mis1 81 2 (by decide)=get (x C.root).mis1 81 2 (by decide) ∧
    get (rawNext s x e C.root).mis1 78 3 (by decide)=get (x C.root).mis1 78 3 (by decide) := by
  rw [outside_root C x e E]
  exact ⟨rfl,rfl⟩

/-- Any intervening segment on the actual tape consisting solely of outside
marks stutters under projection. This does not claim that deleting those
marks before replay leaves future boundary effects unchanged. -/
theorem outside_word {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (E : ∀ e∈w,e∉watch C) :
    projection C (rawRun x w)=projection C x := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    exact (ih (rawNext s x e) (fun f H=>E f (List.mem_cons_of_mem e H))).trans
      (outside_projection C x e (E e (by simp)))

end L4.ShortResetWatch
