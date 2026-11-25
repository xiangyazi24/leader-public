import Leader.L4.ReportIndexedSourcePrefix

namespace L4.ReportSealAckTape
open AllSizeProtocol PhysicalCustody ShortResetCycle ReportResetBarrier
open ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportOwnerCommandRail
open ReportOwnerIssueControl ReportOwnerReverseControl ReportOwnerForwardControl
open ReportOwnerDoorProjection ReportOwnerForwardLocations
open ReportOwnerAcquireReturn ReportIndexedSourcePrefix ReportSealDescriptor

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem seal_next (p : Params) {b : Nat} (H : PreviewNextOp p.digits (sealOp p) b) :
    b=commitOp p := by
  generalize eq : sealOp p = a at H
  unfold sealOp at eq
  cases H <;> unfold commitOp <;> omega

theorem commit_no_next (p : Params) {b : Nat}
    (H : PreviewNextOp p.digits (commitOp p) b) : False := by
  generalize eq : commitOp p = a at H
  unfold commitOp at eq
  cases H <;> omega

theorem commit_only_holds (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (P : (readPC d C x).2=commitOp (params d s)) :
    (readPC d C (rawRun x w)).2=commitOp (params d s) ∧
      file d C (rawRun x w)=file d C x ∧ l=[] := by
  induction T with
  | nil => exact ⟨P,rfl,rfl⟩
  | hold H _ IH =>
      obtain ⟨R,W,L⟩ := IH (H.1.trans P)
      exact ⟨R,W.trans H.2,L⟩
  | credit H _ _ =>
      have V := H.2.2.2.2.2.2.2.1
      rw [P] at V
      exact (commit_no_next (params d s) V).elim

/-- The one real SEAL ACK in an original positive tape. It is a
successful consumed old root D, not an inferred opcode/phase match. -/
theorem seal_credit_split (d : Sheet) (C : Chart h) (x : Raw s n)
    (w : List (Fin n)) (l : List Receipt) (T : AckTape d C x w l)
    (P : (readPC d C x).2=sealOp (params d s))
    (E : (readPC d C (rawRun x w)).2=commitOp (params d s)) :
    ∃ pre post : List (Fin n), w=pre++door C::post ∧
      let old := rawRun x pre
      let issued := rawNext s old (door C)
      (readPC d C old).2=sealOp (params d s) ∧
      file d C old=file d C x ∧
      CreditAt d C old (door C) ∧ readPC d C issued=(1,commitOp (params d s)) ∧
      AckTape d C issued post [] ∧ file d C (rawRun x w)=file d C issued := by
  induction T with
  | nil z =>
      change (readPC d C z).2=commitOp (params d s) at E
      rw [P] at E
      simp only [sealOp,commitOp] at E
      omega
  | @hold x e w l H _ IH =>
      obtain ⟨u,v,W,D,S,A,B,F,G⟩ := IH (H.1.trans P) E
      exact ⟨e::u,v,congrArg (List.cons e) W,D,S.trans H.2,A,B,F,G⟩
  | @credit x e w l H T _ =>
      rcases H with ⟨De,R,Tag,Op,Live,Ok,Ph,Next,F⟩
      subst e
      have H : CreditAt d C x (door C) := ⟨rfl,R,Tag,Op,Live,Ok,Ph,Next,F⟩
      have K : (readPC d C (rawNext s x (door C))).2=commitOp (params d s) := by
        rw [P] at Next
        exact seal_next _ Next
      obtain ⟨_,B,L⟩ := commit_only_holds d C _ w l T K
      subst l
      exact ⟨[],w,rfl,P,rfl,H,Prod.ext Ph K,T,B⟩

theorem ack_on_original_tape (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (X : Cached d hh Q x)
    (A : StrongSerial d C x) (w : List (Fin n)) (NR : NoRestartTape d C x w)
    (P : (readPC d C x).2=sealOp (params d s))
    (E : (readPC d C (rawRun x w)).2=commitOp (params d s)) :
    ∃ pre post : List (Fin n), w=pre++door C::post ∧
      let old := rawRun x pre
      let issued := rawNext s old (door C)
      (readPC d C old).2=sealOp (params d s) ∧ CreditAt d C old (door C) ∧
      LegalIssue d C issued ∧ readPC d C issued=(1,commitOp (params d s)) ∧
      descriptor (params d s) (selectBytes d (issued C.root))=
        descriptor (params d s) (selectBytes d (x C.root)) ∧
      descriptor (params d s) (selectBytes d ((rawRun x w) C.root))=
        descriptor (params d s) (selectBytes d (x C.root)) := by
  have Phase : (readPC d C x).1=1 ∨ (readPC d C x).1=2 := by
    rcases A.1 with I|⟨k,I⟩|⟨k,I⟩
    · exact .inl I.2.1
    · exact .inr I.1.1
    · exact .inr I.1.1
  have PC : PostAcqPC (params d s) (readPC d C x) := by
    refine ⟨Phase,?_,?_⟩ <;> rw [P] <;> simp only [sealOp,commitOp,cmpOp] <;> omega
  obtain ⟨l,T⟩ := ack_tape_run d C N hh G F digit x X A PC w NR
  obtain ⟨pre,post,W,OP,File,Credit,PC',_,EqEnd⟩ := seal_credit_split d C x w l T P E
  let y := rawRun x pre
  have Y := (strong_run d C N hh G F digit x X A pre).1
  have K := Credit
  obtain ⟨_,Rev,_,Match,Live,Ok,_,_,_⟩ := K
  have Mat := Match.trans OP
  obtain ⟨_,I,_,Desc⟩ := raw_seal_ack_keeps_descriptor d C hh G F N y Y
    Rev OP Mat Live Ok digit
  have L : LegalIssue d C (rawNext s y (door C)) := by
    exact ⟨by rw [PC']; unfold commitOp; omega,I⟩
  have Out := (descriptor_of_file_eq (params d s) _ _ EqEnd).trans
    (Desc.trans (descriptor_of_file_eq (params d s) _ _ File))
  exact ⟨pre,post,W,OP,Credit,L,PC',Desc.trans (descriptor_of_file_eq (params d s) _ _ File),Out⟩

#print axioms seal_next
#print axioms commit_no_next
#print axioms commit_only_holds
#print axioms seal_credit_split
#print axioms ack_on_original_tape
end L4.ReportSealAckTape
