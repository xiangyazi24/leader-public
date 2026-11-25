import Leader.L4.ReportOwnerProvenanceTransport

/-! The complete all-non-door structural reverse branch of one
generated owner command. Payload/lease witness semantics are separate. -/
namespace L4.ReportOwnerReverseShape
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportOwnerProvenanceTransport

variable {s n : Nat} {h : Fin n→Bool}

def backTag (k i : Nat) : Nat := if i<k then 1 else if i=k then 3 else 0

def Reverse (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop :=
  k<C.L ∧ ∀ i,i<C.L→(tok d C x i).tag=backTag k i

private theorem not_front {k i : Nat} : backTag k i≠2 := by
  unfold backTag
  split
  · decide
  · split <;> decide

private theorem reply_iff {k i : Nat} : backTag k i=3 ↔ i=k := by
  unfold backTag
  by_cases E : i=k
  · subst i; simp
  · simp only [E,if_false,iff_false]
    split <;> decide

private theorem no_clear {k i : Nat} :
    ¬(backTag k i=1 ∧ backTag k (i+1)=0) := by
  rintro ⟨A,B⟩
  have I : i<k := by
    by_cases E : i<k
    · exact E
    · simp [backTag,E] at A
      split at A <;> contradiction
  by_cases D : i+1=k
  · simp [backTag,D] at B
  · have E : i+1<k := by omega
    simp [backTag,E] at B

private theorem unaffected {i j : Nat} (A : i≠j) (B : i≠j+1) :
    backTag j i=backTag (j+1) i := by
  have C : i<j ↔ i<j+1 := by omega
  simp only [backTag,C,A,B,if_false]

/-- For a genuine single D shape a non-door mark either keeps the
reply at its old occurrence or moves it one step back. There is no
right-to-left replay followed by a second update on the same mark. -/
theorem non_door_step (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop}
    (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : Reverse d C x k)
    (e : Fin n) (D0 : e≠door C) :
    let y := rawNext s x e
    Reverse d C y k ∨ ∃ j, k=j+1 ∧ e=out C j ∧ Reverse d C y j := by
  dsimp only
  let y := rawNext s x e
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x e X
  by_cases A : ∃ j,j<C.L ∧ e=out C j
  · obtain ⟨j,J,rfl⟩ := A
    have local_frame (i : Nat) (I : i<C.L) (E : i≠j) (F0 : i≠j+1) :
        tok d C (rawNext s x (out C j)) i=tok d C x i :=
      decoded_frame d C hh G x _ X Y i I (raw_link_frame d C x j i J I E F0)
    by_cases V : j+1<C.L
    · have LF : (tok d C x j).tag≠2 := (R.2 j J) ▸ not_front
      by_cases K : j+1=k
      · right
        refine ⟨j,K.symm,rfl,J,?_⟩
        have DR : (tok d C x (j+1)).tag=3 := (R.2 (j+1) V).trans (reply_iff.mpr K)
        have ⟨P,S⟩ := reverse_locations d C x N (CF.mask x X) j V LF DR
        intro i I
        by_cases E : i=j
        · subst i
          simpa [backTag] using P
        · by_cases H : i=j+1
          · subst i
            rw [S]
            simp [backTag,MISByteCodec.E]
          · rw [local_frame i I E H,R.2 i I,←K,unaffected E H]
      · left
        refine ⟨R.1,?_⟩
        have NR : (tok d C x (j+1)).tag≠3 := (R.2 (j+1) V) ▸ (fun A=>K (reply_iff.mp A))
        have NC : ¬((tok d C x j).tag=1 ∧ (tok d C x (j+1)).tag=0) := by
          rw [R.2 j J,R.2 (j+1) V]
          exact no_clear
        have ⟨P,S⟩ := idle_internal_tags d C hh G F N x X j V LF NR NC
        intro i I
        by_cases E : i=j
        · subst i
          exact P.trans (R.2 _ J)
        · by_cases H : i=j+1
          · subst i
            exact S.trans (R.2 _ V)
          · rw [local_frame i I E H,R.2 i I]
    · left
      refine ⟨R.1,?_⟩
      have E0 : j+1=C.L := by omega
      have LF : (tok d C x j).tag≠2 := (R.2 j J) ▸ not_front
      have LT : (tok d C x j).tag≠1 := by
        rw [R.2 j J]
        have NK : ¬j<k := by have B := R.1; omega
        simp [backTag,NK]
        split <;> decide
      have P := idle_end_tag d C hh G F N x X j E0 LF LT
      intro i I
      by_cases E : i=j
      · subst i
        exact P.trans (R.2 _ J)
      · rw [local_frame i I E (by omega),R.2 i I]
  · left
    refine ⟨R.1,?_⟩
    intro i I
    have W := raw_off_frame d C x e D0 (fun j J H=>A ⟨j,J,H⟩) i I
    rw [decoded_frame d C hh G x y X Y i I W,R.2 i I]

end L4.ReportOwnerReverseShape
