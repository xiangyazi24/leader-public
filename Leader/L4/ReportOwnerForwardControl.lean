import Leader.L4.ReportOwnerForwardLocations
import Leader.L4.ReportOwnerReverseControl

namespace L4.ReportOwnerForwardControl
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportOwnerProvenanceTransport ReportOwnerForwardLocations ReportOwnerReverseControl
open ReportPrelaunchClock ReportPrelaunchDoorLift ReportOwnerDoorProjection
open ReportByteRows ReportRawProjection

variable {s n : Nat} {h : Fin n→Bool}

def ForwardWait (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Prop :=
  LegalWait d C x ∧ Forward d C x k

private theorem tok_root_pub (d : Sheet) (C : Chart h) (x : Raw s n) :
    tok d C x 0=publicationToken (params d s) true (selectBytes d (x C.root)) 0 := by
  rw [root_tok,prelaunch_root_decode]

/-- While the cursor is on the forward leg (including the root itself),
the actual owner-door WAIT mark is inert on the PC and cursor shape. -/
theorem door_holds (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat)
    (R : ForwardWait d C x k) : ForwardWait d C (rawNext s x (door C)) k := by
  let p := params d s
  let y := rawNext s x (door C)
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have CF := cached_fibre d N hh Q F
  have Y : Cached d hh Q y := CF.closed x _ X
  have H : t.tag=1 ∨ t.tag=2 := by
    dsimp [t,p,v]
    rw [←tok_root_pub d C x,R.2.2 0 C.positive]
    by_cases K : k=0
    · subst k; exact .inr rfl
    · exact .inl (by simp [frontTag,show 0<k by omega])
  have P : sourcePhase p v=2 := R.1.1
  have O : sourceOpcode p v≤commitOp p := R.1.2
  have W := raw_door_final d C x N (CF.mask x X)
  have CP := W.1.trans (prelaunch_hold_controls p v t P O H)
  have WR := W.2
  change resetTokenRead p (selectBytes d (y C.root)) 0=
    (match (source p v t).2 with
    | none => prelaunchDoorNormWire p v
    | some q => resetTokenWire p q) at WR
  rw [prelaunch_wait_hold p v t P O H] at WR
  have RT : (tok d C y 0).tag=(tok d C x 0).tag := by
    rw [root_tok d C y,tok_root_pub d C x,WR]
    exact prelaunch_door_norm_tag p v
  refine ⟨⟨?_,?_⟩,R.2.1,?_⟩
  · exact (congrArg Prod.fst CP).trans P
  · change (controlWork p (selectBytes d (y C.root))).2≤commitOp p
    rw [CP]
    exact O
  · intro i I
    by_cases Z : i=0
    · subst i; exact RT.trans (R.2.2 0 I)
    · have Pos : 0<i := by omega
      rw [decoded_frame d C hh G x y X Y i I (raw_door_frame d C x i Pos I)]
      exact R.2.2 i I

/-- Every physical mark preserves the well-formed forward phase, moves
the cursor one chart occurrence, or turns at the end to ReverseWait. -/
theorem all_mark (d : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (G : GapInput h) {Q : Raw s n→Prop} (F : Fibre (h:=h) d Q) (N : 1<n)
    (x : Raw s n) (X : Cached d hh Q x) (k : Nat) (R : ForwardWait d C x k)
    (e : Fin n) :
    let y := rawNext s x e
    ForwardWait d C y k ∨ (e=out C k ∧
      (ForwardWait d C y (k+1) ∨ (k+1=C.L ∧ ReverseWait d C y k))) := by
  dsimp only
  by_cases D : e=door C
  · subst e
    exact .inl (door_holds d C hh G F N x X k R)
  · have CF := cached_fibre d N hh Q F
    have P : LegalWait d C (rawNext s x e) := by
      unfold LegalWait
      rw [raw_nondoor_control d C x e N (CF.mask x X) D]
      exact R.1
    rcases non_door_step d C hh G F N x X k R.2 e D with S|⟨E,S|⟨J,S⟩⟩
    · exact .inl ⟨P,S⟩
    · exact .inr ⟨E,.inl ⟨P,S⟩⟩
    · exact .inr ⟨E,.inr ⟨J,P,S⟩⟩

end L4.ReportOwnerForwardControl
