import Leader.L4.ReportOwnerIssueControl
import Leader.L4.ReportLeaseTwoCoverLift

namespace L4.ReportOwnerSerial
open AllSizeProtocol PhysicalCustody
open ShortResetCycle ReportResetBarrier ReportResetRawHooks
open ReportOwnerResetDrain ReportPrelaunchK1Geometry
open ReportPrelaunchClock ReportOwnerProvenanceTransport ReportOwnerDoorProjection ReportPrelaunchDoorLift
open ReportOwnerIssueControl ReportOwnerForwardControl ReportOwnerReverseControl
open ReportByteRows ReportRawProjection

variable {s n : Nat} {h : Fin n → Bool} {Q : Raw s n→Prop}

def Serial (d : Sheet) (C : Chart h) (x : Raw s n) : Prop :=
  LegalIssue d C x ∨ (∃ k,ForwardWait d C x k) ∨ ∃ k,ReverseWait d C x k

theorem seed_at_genuine_receipt (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (w : List (Fin n))
    (R : Generated d C x w .done) : Serial d C (rawRun x w) := by
  obtain ⟨_,A⟩ := cached_genuine_full_parked d C N hh F x X w R
  have B := pc_fields d C (rawRun x w) .issue1 (by decide) A.1.1
  left
  have b0 : readPC d C (rawRun x w)=(1,1) := B
  refine ⟨?_,congrArg Prod.fst b0,?_⟩
  · rw [b0]
    unfold commitOp
    omega
  · intro k K
    rw [tok_wire,A.1.2.1 k K]
    rw [show canon (params d s) .empty=resetTokenWire (params d s) MISByteCodec.E from rfl,drain_decode_E]
    rfl

private theorem legal_on_consume (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (R : ReverseWait d C x 0)
    (digit : 0<(params d s).digits) : LegalIssue d C (rawNext s x (door C)) := by
  let p := params d s
  let v := selectBytes d (x C.root)
  let t := publicationToken p true v 0
  have RT : t.tag=3 := by
    have K := R.2.2 0 C.positive
    rw [root_tok,←prelaunch_root_decode] at K
    exact K
  have M := prelaunch_wait_controls p v t R.1.1 R.1.2
    (by rw [RT]; decide) (by rw [RT]; decide) digit
  have W := (raw_door_final d C x N ((cached_fibre d N hh Q F).mask x X)).1
  have H (a : Nat) (A : controlWork p ((liftSourcePatch p (source p v t).1).apply v)=(1,a)) :
      (readPC d C (rawNext s x (door C))).2=a := congrArg Prod.snd (W.trans A)
  refine ⟨?_,door_consumes_root d C hh G F N x X R digit⟩
  rcases M with M | ⟨a,B,M⟩
  · rw [H 0 M]
    exact Nat.zero_le _
  · rw [H a M]
    have L := (previewNextOp_bounds B).2
    unfold commitOp
    change a<4*(params d s).digits+5 at L
    omega

/-- After a genuine own RESET completion the structural one-command
rail is closed on every original mark. No foreign owner cleanliness is
assumed. This result only tracks decoded tags and legal PC; it neither
authenticates captured bytes nor attributes a concurrent grant. -/
theorem all_mark (d : Sheet) (C : Chart h) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : Raw s n) (X : Cached d hh Q x) (R : Serial d C x)
    (digit : 0<(params d s).digits) (e : Fin n) :
    Serial d C (rawNext s x e) := by
  rcases R with I|⟨k,I⟩|⟨k,I⟩
  · by_cases D : e=door C
    · subst e
      rcases door_step d C hh G F N x X I with R|⟨A,_⟩
      · left
        exact ⟨by rw [R.1]; exact Nat.zero_le _,R.2⟩
      · exact .inr (.inl ⟨0,A⟩)
    · exact .inl (nondoor_preserves d C hh G F N x X I e D).1
  · rcases ReportOwnerForwardControl.all_mark d C hh G F N x X k I e with A|⟨_,A|⟨_,A⟩⟩
    · exact .inr (.inl ⟨k,A⟩)
    · exact .inr (.inl ⟨k+1,A⟩)
    · exact .inr (.inr ⟨k,A⟩)
  · rcases ReportOwnerReverseControl.all_mark d C hh G F N x X k I digit e with A|⟨j,_,_,A⟩|⟨K,D,_⟩
    · exact .inr (.inr ⟨k,A⟩)
    · exact .inr (.inr ⟨j,A⟩)
    · subst k e
      exact .inl (legal_on_consume d C N hh G F x X I digit)

def AllSerial (d : Sheet) (hh : ∃ i,h i=true) (Q : Raw s n→Prop)
    (G : GapInput h) (x : Raw s n) : Prop :=
  Cached d hh Q x ∧ ∀ C∈ReportPrelaunchAllOwners.ownerCharts G,Serial d C x

theorem all_serial_closed (d : Sheet) (N : 1<n)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (digit : 0<(params d s).digits) (x : Raw s n) (e : Fin n)
    (A : AllSerial d hh Q G x) : AllSerial d hh Q G (rawNext s x e) := by
  exact ⟨(cached_fibre d N hh Q F).closed x e A.1,fun C M =>
    all_mark d C N hh G F x A.1 (A.2 C M) digit e⟩

/-- One chronological RESET cover suffices for the structural rail
invariant at all owners. This is not full Good8, which additionally
needs to retire captures made before all owners had genuine rails. -/
theorem all_serial_from_cached (d : Sheet) (N : 1<n) (S : 0<s)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (x : {x : Raw s n // Cached d hh Q x}) :
    IIDExpectedHittingTimeAtMost (rawNext s) (AllSerial d hh Q G) x.val
      (ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits*n^2) := by
  let advance := ReportPrelaunchTwoCovers.advance d hh F N
  let phase := fun C : Chart h => ReportOwnerReceiptClock.next d C (cached_fibre d N hh Q F)
  let goal := fun (_ : Chart h) (z : ReportOwnerReceiptClock.State (Cached d hh Q)) =>
    ReportOwnerReceiptClock.done z
  let fresh : Option Stage := none
  let sites := ReportPrelaunchAllOwners.ownerCharts G
  let next := SequentialMarkClock.step advance phase goal fresh
  let start := SequentialMarkClock.start fresh sites x
  let K := ReportResetEventClock.resetCoefficient (3*G.B) (params d s).digits
  have digit := ReportPrelaunchDoorProducer.digits_positive d S
  have phys : ∀ C w e,(phase C w e).1=advance w.1 e := fun _ _ _ => rfl
  have project : ∀ z e,(next z e).raw.val=rawNext s z.raw.val e := by
    intro z e
    unfold next
    rw [SequentialMarkClock.step_raw _ _ _ _ phys]
    rfl
  have initial (C : Chart h) (y : {x : Raw s n // Cached d hh Q x}) :
      ¬goal C (y,fresh) := ReportOwnerReceiptClock.initial_not_done y
  have bound := SequentialMarkClock.expected advance phase goal fresh (fun _=>True) phys
    (fun _ _ _=>trivial) (n*K) (fun C y _=>initial C y)
    (fun C y _=>ReportPrelaunchDoorReady.receipt_mean d C N S hh G Q F y)
    sites x trivial
  have H := MonitorRawBridge.expected_of_monitor_words (rawNext s) next
    (fun z => z.raw.val) SequentialMarkClock.finished (AllSerial d hh Q G)
    project start (by
      intro word done
      have before : SequentialMarkClock.BeforeCurrent goal start := by
        unfold SequentialMarkClock.BeforeCurrent start SequentialMarkClock.start
        cases sites with
        | nil => trivial
        | cons C _ => exact initial C x
      have W := SequentialMarkClock.first_hit_receipts_of_finished advance phase goal fresh
        initial start word before done
      have R : SequentialMarkClock.FirstHitReceipts phase goal fresh (sites++[]) (x,fresh) word := by
        rw [List.append_nil]
        exact W
      obtain ⟨u,v,E,U,_⟩ := ReportResetCovers.split_first_cut advance phase goal fresh phys sites [] x word R
      have A : AllSerial d hh Q G (rawRun x.val u) := by
        have lift (y : Raw s n) (w : List (Fin n)) (Y : Cached d hh Q y) :
            Cached d hh Q (rawRun y w) := by
          induction w generalizing y with
          | nil => exact Y
          | cons e w ih => exact ih _ ((cached_fibre d N hh Q F).closed y e Y)
        refine ⟨lift _ u x.property,?_⟩
        apply ReportLeaseTwoCoverLift.exact_cover_supplies d N hh F (fun _ => True)
          (fun _ _ _ _ => trivial) (Serial d) _ _ sites x trivial u U
        · exact fun C y w Y _ P=>seed_at_genuine_receipt d C N hh F y Y w P
        · exact fun C y e Y T=>all_mark d C N hh G F y Y T digit e
      have runs (y : Raw s n) (w : List (Fin n)) :
          SequentialMarkClock.run (rawNext s) y w=rawRun y w := by
        induction w generalizing y with
        | nil => rfl
        | cons e w ih => exact ih (rawNext s y e)
      have stepper (y : Raw s n) (w : List (Fin n)) (a : AllSerial d hh Q G y) :
          AllSerial d hh Q G (rawRun y w) := by
        induction w generalizing y with
        | nil => exact a
        | cons e w ih => exact ih _ (all_serial_closed d N hh G F digit y e a)
      rw [show start.raw.val=x.val from rfl,runs,E,ShortOwnerEpochJS.raw_append]
      exact stepper _ v A) _ bound
  have len : sites.length≤n := ReportPrelaunchAllOwners.owner_charts_length G
  have up : sites.length*(n*K)≤K*n^2 := by
    calc
      _ ≤ n*(n*K) := Nat.mul_le_mul_right _ len
      _ = _ := by rw [Nat.pow_two]; ac_rfl
  intro t
  exact Nat.le_trans (H t) (Nat.mul_le_mul_right _ up)

end L4.ReportOwnerSerial
