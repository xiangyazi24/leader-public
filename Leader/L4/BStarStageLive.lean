import Leader.L4.BStarBankCapture

/-! STAGE ownership is only relevant at an active digit or its header.
No claim about provenance is needed for inert K0/K2 transports. -/
namespace L4.BStarStageLive
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongPublication
open BStarLongOutgoing BStarLongToken BStarBankCapture

def StageLiveOwned (g : LongGeometry) (j : Fin 11) (x : BitVec LW)
    (b : Fin 3) (p : Payload) : Prop :=
  j.val=1 → p.fault=0 → (g.axes.h6 || g.inside)=true →
  p.opcode.toNat=BStarLongCommand.stageOp →
    ∀ d, BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/2^18))=some d →
      (g.axes.h6 && !actual x d)=false → d.old=b

theorem outgoing_live_protects (g : LongGeometry) (j : Fin 11) (x : BitVec LW)
    (p : Payload) (b : Fin 3) (H : StageLiveOwned g j x b p)
    (no : (execute g j x p).published=none) :
    Protected b (execute g j x p).row := by
  simp only [execute,hold,refuse] at no ⊢
  split
  · exact frame_empty _
  rename_i enabled
  split
  · exact frame_compose (frame_stage_field _ _) (frame_seal_field _ _)
  split
  · rename_i hop
    split
    · exact frame_empty _
    · rename_i d hd
      split
      · exact frame_empty _
      · rename_i allowed
        by_cases hp : (g.axes.h6 || g.inside)=true
        · have en : (j.val != 1 || p.fault != 0)=false := Bool.eq_false_iff.mpr enabled
          have both := Bool.or_eq_false_iff.mp en
          have hj : j.val=1 := by
            apply Classical.not_not.mp
            intro ne
            have bad : (j.val != 1)=true := bne_iff_ne.mpr ne
            rw [bad] at both
            exact Bool.noConfusion both.1
          have hf : p.fault=0 := by
            apply Classical.not_not.mp
            intro e
            have bad : (p.fault != 0)=true := bne_iff_ne.mpr e
            rw [bad] at both
            exact Bool.noConfusion both.2
          have E := H hj hf hp (beq_iff_eq.mp hop) d hd (Bool.eq_false_iff.mpr allowed)
          have ⟨n0,n1⟩ := complement_ne d (decode_valid hd)
          rw [← E]
          exact stage_frames d g.axes.h6 g.inside x p.argument.toNat d.old n0 n1
        · have both := Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr hp)
          change Protected b (stagePatch g.axes.h6 g.inside x d p.argument.toNat)
          simp only [stagePatch,both.1,both.2,Bool.false_eq_true,if_false,
            List.nil_append,fuse,List.foldl_nil]
          exact frame_empty _
  split
  · split
    · exact frame_empty _
    · split
      · exact frame_seal_field _ _
      · exact frame_empty _
  split
  · split
    · exact frame_empty _
    · split
      · rename_i d hd hlo
        split
        · rename_i yes
          have Hc : (commit g.axes.h6 j x d ⟨p.argument.toNat%4,hlo⟩).2=none := by
            simp_all only [Bool.false_eq_true,if_true,if_false,dif_pos]
          simp [Hc] at yes
        · exact frame_empty _
      · exact frame_empty _
  · exact frame_empty _

end L4.BStarStageLive
