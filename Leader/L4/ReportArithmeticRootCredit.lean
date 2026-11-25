import Leader.L4.ReportIndexedSourcePrefix
import Leader.L4.ReportOwnerIndexedFlight
import Leader.L4.ReportPrelaunchDoorProducer

namespace L4.ReportArithmeticRootCredit
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart
open ReportResetBarrier ReportResetRawHooks ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportByteRows ReportPrelaunchClock ReportPrelaunchDoorLift ReportOwnerCommandRail
open ReportOwnerAcquireReturn ReportOwnerIndexedFlight ReportIndexedSourcePrefix
open ReportOwnerDoorProjection ReportOwnerReverseControl

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n → Prop}

theorem preview_changes_opcode {m a b : Nat} (P : PreviewNextOp m a b) : b≠a := by
  cases P <;> omega

/-- A healthy actual root D in the arithmetic interval is credited by
its literal next source-door activation. It cannot be classified as
a hold and does not require a supplied no-restart on this mark. -/
theorem healthy_root_credit (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (Digit : 0<(params d s).digits)
    (x : Raw s n) (X : Cached d hh Q x) (A : StrongSerial d C x)
    (PC : PostAcqPC (params d s) (readPC d C x))
    (I : ItemNineInputs) (B : 2≤(params d s).beta)
    (M : ItemNineAt (params d s) I (readPC d C x).2
      (item9Read (params d s) (selectBytes d (x C.root))))
    (R : ReverseWait d C x 0) (Match : (tok d C x 0).opcode=(readPC d C x).2)
    (Live : (tok d C x 0).fault=false) (ND : (tok d C x 0).outcome≠1)
    (U : (readPC d C x).2<commitOp (params d s)) :
    CreditAt d C x (door C) ∧ (readPC d C (rawNext s x (door C))).2≠0 := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  let y := rawNext s x (door C)
  have E : tok d C x 0=t := by rw [root_tok,←prelaunch_root_decode]
  have Tag : t.tag=3 := by rw [←E,R.2.2 0 C.positive]; rfl
  have NZ := item9_good_reply_no_retry p I v t (readPC d C x).2 B R.1.1 rfl Tag
    (E ▸ Match) (E ▸ Live) (E ▸ ND) U M
  have W : readPC d C y=acqSourcePC p v t :=
    (raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)).1
  have NZ' : (readPC d C y).2≠0 := by rw [W]; exact NZ
  refine ⟨?_,NZ'⟩
  rcases mark_credit_or_hold d C N hh G F Digit x X A PC (door C) NZ' with Hold|Credit
  · obtain ⟨_,_,_,b,Step,Res⟩ := indexed_credit p v t R.1.1 R.1.2 Tag NZ Digit
    have Y := congrArg Prod.snd (W.trans Res)
    exact (preview_changes_opcode Step (Y.symm.trans Hold.1)).elim
  · exact Credit

end L4.ReportArithmeticRootCredit
