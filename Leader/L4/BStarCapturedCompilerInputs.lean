import Leader.L4.BStarAcquisitionToStage
import Leader.L4.BStarAliasRoster
import Leader.L4.BStarAliasPaired
import Leader.L4.BStarCommitChoiceHistory

namespace L4.BStarCapturedCompilerInputs
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongDoor BStarLongWork BStarLongToken
open BStarAcquireReadout BStarAcquireDigits BStarCaptureDoorHistory BStarAliasFold
open BStarLongArithmetic BStarLongCommand L4.Compiler.Native

/-- Decode the 9-bit block in compiler order (most-significant bit first).
This uses the exact offsets of the literal alias, not a new sample. -/
theorem header_bit (x : BitVec LW) (q : Fin 3) (i : Fin 9) :
    ((capturedHeader q i).read x).toNat=
      (((headerBlock q).read x).getLsbD (8-i.val)).toNat := by
  have E : (capturedHeader q i).read x=
      BitVec.ofBool (((headerBlock q).read x).getLsbD (8-i.val)) := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have K : k=0 := by omega
    subst k
    have j : 8-i.val<9 := by omega
    simp [Field.read,capturedHeader,headerBlock,j]
  simpa using congrArg BitVec.toNat E

/-- Header data for the compiler is pinned to the original ACQUIRE
reply. Word inputs may be separately obtained by authenticated COPY. -/
def receiptBank (f : Payload) (words : Fin 3 → Fin 9 → Nat) : Bank :=
  ⟨words,fun q i => (BitVec.ofNat 9 (fieldsAt f q).2).getLsbD (8-i.val)⟩

theorem alias_from_receipt (x : BitVec LW) (f : Payload)
    (words : Fin 3 → Fin 9 → Nat)
    (H : ∀ q, ((headerBlock q).read x).toNat=(fieldsAt f q).2)
    (q : Fin 3) (i : Fin 9) (xs : Pending) :
    aliasValue x xs (.header q i)=some (((receiptBank f words).hdr q i).toNat) := by
  have E : (headerBlock q).read x=BitVec.ofNat 9 (fieldsAt f q).2 := by
    rw [←H q]
    simp
  change some (((capturedHeader q i).read x).toNat)=_
  rw [header_bit,E]
  rfl

theorem roster_from_receipt (x : BitVec LW) (f : Payload)
    (words : Fin 3 → Fin 9 → Nat)
    (H : ∀ q, ((headerBlock q).read x).toNat=(fieldsAt f q).2)
    {k : Nat} (hk : k<395) :
    Segment (receiptBank f words) x BStarAliasRoster.literalCmp
      (BStarAliasRoster.start k+1) (BStarAliasRoster.suffix k) := by
  apply BStarAliasRoster.roster_segment _ _ hk
  intro q i
  exact Option.some.inj (alias_from_receipt x f words H q i [])

/-- PC13 begins the literal compiler with a unit argument.
The captured selector is first injected by the center-load family. -/
theorem first_source_initial (x : BitVec LW) : initial 13 x=some 0 := rfl

theorem center_load_initial (x : BitVec LW) (op : Nat)
    (K : arithKind op=some .centerLoad)
    (lo : 13≤op) (hi : op<408) :
    initial op x=if ((capturedSelector 1).read x).toNat=3 then none
      else some ((capturedSelector 1).read x).toNat := by
  have A : op≠acquire := by unfold acquire; omega
  have C : op≠copyLoad := by unfold copyLoad; omega
  have S : op≠stageOp := by unfold stageOp; omega
  have T : op≠sealOp := by unfold sealOp; omega
  have F : op≠commitOp := by unfold commitOp; omega
  simp [initial,A,C,S,T,F,beq_iff_eq,K]

theorem first_center_load : arithKind 37=some .centerLoad := by decide

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- On a no-restart computation word the per-incidence fields,
including all nine individual header bits, equal those at its start. -/
theorem retain_blocks (x : X) (root : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (live : BStarGeneratedBandScan.LiveWord hp root x w) (q : Fin 3) :
    let a : BitVec LW := (x root).long
    let b : BitVec LW := ((run x w) root).long
    (capturedSelector q).read b=(capturedSelector q).read a ∧
      (headerBlock q).read b=(headerBlock q).read a := by
  dsimp only
  obtain ⟨H,C,_⟩ := word_capture_hold hp x root w sep (fun u e v E => (live u e v E).2)
  let a : BitVec LW := (x root).long
  let b : BitVec LW := ((run x w) root).long
  have hh : capturedHeaders.read b=capturedHeaders.read a := H
  have cc : captures.read b=captures.read a := C
  have field {m k : Nat} (f : Field LW m) (g : Field LW k) (L : f.offset≤g.offset)
      (U : g.offset+k≤f.offset+m) (E : f.read b=f.read a) :
      g.read b=g.read a := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have j : g.offset-f.offset+i<m := by omega
    have h := congrArg (fun z : BitVec m => z.getLsbD (g.offset-f.offset+i)) E
    have R : f.offset+(g.offset-f.offset+i)=g.offset+i := by omega
    simpa only [Field.read,BitVec.getLsbD_extractLsb',hi,j,decide_true,Bool.true_and,R] using h
  exact ⟨field captures (capturedSelector q) (by simp [captures,capturedSelector])
    (by change 2189+2*(2-q.val)+2≤2189+6; omega) cc,
    field capturedHeaders (headerBlock q) (by simp [capturedHeaders,headerBlock])
      (by change 2162+9*(2-q.val)+9≤2162+27; omega) hh⟩

/-- All actual old snapshots on the accepted calculation tape use
the very same packed ACQUIRE reply. This covers the source-side
alias reads on the same marked physical receipt as acceptFile. -/
theorem every_cut_from_receipt (x : X) (root : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (live : BStarGeneratedBandScan.LiveWord hp root x w)
    (f : Payload) (A : BStarAcquireJoined.snapshot (x root).long=BStarAcquireLanding.expected f)
    (pre tail : List (Fin n)) (W : w=pre++tail) :
    ∀ q : Fin 3,
      let y : BitVec LW := (run x pre root).long
      (((capturedSelector q).read y).toNat,((headerBlock q).read y).toNat)=fieldsAt f q := by
  intro q
  have L : BStarGeneratedBandScan.LiveWord hp root x pre := by
    intro a e b E
    have D : w=a++e::(b++tail) := by rw [W,E,List.append_assoc]; rfl
    exact live a e (b++tail) D
  have R := retain_blocks hp x root pre sep L q
  have E := source_fields_payload (x root).long f A q
  let y : BitVec LW := (run x pre root).long
  let old : BitVec LW := (x root).long
  change (((capturedSelector q).read y).toNat,((headerBlock q).read y).toNat)=fieldsAt f q
  have S : (capturedSelector q).read y=(capturedSelector q).read old := R.1
  have H : (headerBlock q).read y=(headerBlock q).read old := R.2
  rw [S,H]
  exact E

/-- Each actual arithmetic cut discharges all captured-header
premises of the checked accepted alias roster. This is independent
of the packed numeral proof for the physical arithmetic head. -/
theorem roster_at_cut (x : X) (root : Fin n) (w : List (Fin n))
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (live : BStarGeneratedBandScan.LiveWord hp root x w)
    (f : Payload) (A : BStarAcquireJoined.snapshot (x root).long=BStarAcquireLanding.expected f)
    (pre tail : List (Fin n)) (W : w=pre++tail)
    (words : Fin 3 → Fin 9 → Nat) {k : Nat} (hk : k<395) :
    let y : BitVec LW := (run x pre root).long
    Segment (receiptBank f words) y BStarAliasRoster.literalCmp
      (BStarAliasRoster.start k+1) (BStarAliasRoster.suffix k) := by
  apply roster_from_receipt _ f words _ hk
  intro q
  exact congrArg Prod.snd (every_cut_from_receipt hp x root w sep live f A pre tail W q)

/-- A literal center-load issue samples the retained center selector.
The first such issue is PC37; PC13 merely starts the compiler. -/
theorem joined_center_load (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (hdr : (oldHeaders B x.2).h6=true)
    (valid : LongDoorGuard.valid manifest x.2.long=true)
    (phase : (ctrlPhase.read x.2.long).toNat=1)
    (op : Nat) (pc : (ctrlOp.read x.2.long).toNat=op)
    (K : arithKind op=some .centerLoad) (lo : 13≤op) (hi : op<408)
    (f : Payload)
    (sel : ((capturedSelector 1).read x.2.long).toNat=(fieldsAt f 1).1)
    (good : (fieldsAt f 1).1<3) :
    atSite (largePair B x).2.long 0=forward op (fieldsAt f 1).1 := by
  let raw : BitVec LW := x.2.long
  have S : ((capturedSelector 1).read raw).toNat=(fieldsAt f 1).1 := sel
  have P : (ctrlOp.read raw).toNat=op := pc
  have A : initial (ctrlOp.read raw).toNat raw=some (fieldsAt f 1).1 := by
    rw [P,center_load_initial raw op K lo hi,S,if_neg (by omega)]
  have E := BStarResetControllerEntry.exact_issue_any_token
    k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x hdr valid phase
  change BStarResetControllerEntry.snapshot (largePair B x).2.long=
    (match initial (ctrlOp.read raw).toNat raw with
     | none => ((.empty,1),0)
     | some a => ((forward (ctrlOp.read raw).toNat a,2),ctrlOp.read raw)) at E
  rw [A,P] at E
  exact congrArg (fun v => v.1.1) E

private theorem ack12_nonrestart (old : BitVec LW) (f : Payload) :
    afterReply 12 f old≠faultRestart := by
  rw [BStarAliasRoster.first_receipt]
  intro eq
  have T := congrArg (fun (q : Patch LW) => ctrlOp.read (q.apply old)) eq
  have opEq : ctrlOp.read (((schedule 13).compose ((scalarFile.assign 0).compose (need.assign 0))).apply old)=
      BitVec.ofNat 9 13 := by
    simp only [Patch.compose_apply]
    rw [Field.read_other_assign ctrlOp need _ _ (.inr (by decide)),
      Field.read_other_assign ctrlOp scalarFile _ _ (.inr (by decide))]
    exact congrArg (fun a : (Token × BitVec 2) × BitVec 9 => a.2)
      (BStarJoinedControllerReturn.snapshot_schedule 13 old)
  rw [opEq] at T
  have repair : ctrlOp.read (faultRestart.apply old)=0 :=
    (LongDoorGuard.repair_values manifest old).2.1
  rw [repair] at T
  exact (by decide : (13 : BitVec 9)≠0) T

/-- Actual matched ACK at PC12 zeros the whole scalar file, keeps the
same captured selector/header inputs, and steps to the true first
compiler instruction. -/
theorem joined_ack12_scalar (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (f : Payload) (hdr : (oldHeaders B x.2).h6=true)
    (valid : LongDoorGuard.valid manifest x.2.long=true)
    (phase : (ctrlPhase.read x.2.long).toNat=2)
    (pc : (ctrlOp.read x.2.long).toNat=12)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=12) :
    scalarFile.read (largePair B x).2.long=0 := by
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have P : (ctrlOp.read raw.2).toNat=12 := pc
  have V : LongDoorGuard.valid manifest raw.2=true := valid
  have W := BStarCommitChoiceHistory.reply_work g raw f hdr V phase 12 P R F O (by decide)
  rw [BStarAliasRoster.first_receipt] at W
  have project : scalarFile.read (largePair B x).2.long=
      scalarFile.read (patchPair (longWork g raw) raw).2 := by
    change scalarFile.read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      ((longWork g raw).2.compose (longScratch g raw).2)).apply raw.2)=_
    simp only [LongDoorGuard.guard,V,Bool.not_true,Bool.and_false,Bool.false_eq_true,if_false,
      Patch.compose_apply]
    exact Field.read_other_assign scalarFile offField _ _ (.inl (by decide))
  have Z : scalarFile.read (largePair B x).2.long=0 := by
    rw [project]
    exact BStarAliasPaired.door_field scalarFile (by decide) (by decide) g raw hdr _ W (fun _ => 0)
      (fun y => by
        unfold schedule setToken
        simp only [Patch.compose_apply]
        rw [Field.read_other_assign scalarFile need _ _ (.inl (by decide)),Field.read_assign])
  exact Z

/-- Actual matched ACK at PC12 zeros the whole scalar file, keeps the
same captured selector/header inputs, and steps to the true first
compiler instruction. -/
theorem joined_ack12 (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (f : Payload) (hdr : (oldHeaders B x.2).h6=true)
    (valid : LongDoorGuard.valid manifest x.2.long=true)
    (phase : (ctrlPhase.read x.2.long).toNat=2)
    (pc : (ctrlOp.read x.2.long).toNat=12)
    (R : bind (longGeometry B x.2) 0 (atSite x.2.long 0)=.reply f)
    (F : f.fault=0) (O : f.opcode.toNat=12) :
    let y := (largePair B x).2.long
    BStarResetControllerEntry.snapshot y=((.empty,1),BitVec.ofNat 9 13) ∧
      scalarFile.read y=0 ∧ capturedHeaders.read y=capturedHeaders.read x.2.long ∧
      captures.read y=captures.read x.2.long := by
  dsimp only
  let g := Pair.map (longGeometry B) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  have P : (ctrlOp.read raw.2).toNat=12 := pc
  have V : LongDoorGuard.valid manifest raw.2=true := valid
  have E := BStarLiteralPC.joined_reply_PC k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x f hdr valid phase R
  have A : BStarLiteralPC.pcNext raw.2 f=13 := by
    simp only [BStarLiteralPC.pcNext,P,F,O,bne_self_eq_false,Bool.false_or,Bool.false_eq_true,if_false]
    rfl
  change BStarResetControllerEntry.snapshot (largePair B x).2.long=
    ((.empty,1),BitVec.ofNat 9 (BStarLiteralPC.pcNext raw.2 f)) at E
  rw [A] at E
  have RR : bind g.2 0 (atSite raw.2 0)=.reply f := R
  have ph : (ctrlPhase.read raw.2).toNat=2 := phase
  have N : BStarAcquireFrame.Normal raw.2 (oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))) := by
    have decision : oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.write (afterReply 12 f raw.2) := by
      rw [RR]
      simp [oldDoor,V,ph,P,F,O,show (arithKind 12).isSome=false by decide]
    rw [decision]
    exact .reply 12 f (by decide) (ack12_nonrestart raw.2 f)
  refine ⟨E,joined_ack12_scalar hp x f hdr valid phase pc R F O,?_⟩
  exact joined_normal hp x hdr valid N

end L4.BStarCapturedCompilerInputs
