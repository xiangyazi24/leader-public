import Leader.L4.BStarReplyBack

/-! Turn-to-source arithmetic receipt and its exact outward digit tape. -/
namespace L4.BStarNumericHitSweep
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongLayout BStarLongDoor BStarLongArithmetic BStarLongRegisters
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain BStarResetChartTouch
open BStarResetMarkAdapter BStarResetRailRing BStarOwnerLaunchOrigin BStarGeneratedOwner
open BStarAcquireForwardTrace BStarSeparatingRail BStarLongEvents
open BStarNumericCarry BStarNumericReceipt BStarNumericChronology BStarNumericConsecutive

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
  (r:=r) (c:=c) (p:=p) (c₁:=c₁)

open BStarLongSignatures in
private theorem nodes_in_range : tourNodes.all (fun i => decide (i<474))=true := by
  decide +kernel

theorem exists_node {op : Nat} (lo : 13≤op) (hi : op<408) :
    ∃ i code, nodeOf op=some i ∧ BStarLongArithmetic.get i=some code := by
  have h : op-13<BStarLongSignatures.tourNodes.length := by
    rw [actual_table_lengths.1]; omega
  let i := BStarLongSignatures.tourNodes[op-13]
  have hi : i<474 := of_decide_eq_true (List.all_eq_true.mp nodes_in_range _
    (List.getElem_mem h))
  have H : i<L4.Compiler.Native.literal.length := by
    rw [actual_table_lengths.2]; exact hi
  refine ⟨i,L4.Compiler.Native.literal[i]'H,?_,?_⟩
  · unfold nodeOf
    rw [if_neg (Nat.not_lt.mpr lo),List.getElem?_eq_getElem h]
  · unfold BStarLongArithmetic.get
    exact List.getElem?_eq_getElem H

/-- The accepted digit sweep plus projections onto the genuine
live file immediately after launch and immediately before K10 turn. -/
def Sweep (base y : X) (addr : Nat → Pos n) (len op : Nat) (w : List (Fin n))
    (i : Nat) (code : L4.Compiler.Native.Code) : Prop :=
    ∃ ds : List D, Aligned hp base addr len op y 0 w len ds ∧
    let visits := ds.filter (significant hp base addr)
    let digit := fun d : D => physicalDigit (geom hp d) (byte d) i code d.offer
    let updated := fun d : D => (digit d).1.apply (byte d)
    ∃ tokens : Nat → Payload,
      (∀ j : Fin visits.length, tokens j.val=visits[j.val].offer) ∧
      BStarPhysicalWordSem.DigitSweep
        (fun j : Fin visits.length => geom hp visits[j.val])
        (fun j : Fin visits.length => byte visits[j.val])
        (fun j : Fin visits.length => updated visits[j.val]) i code tokens ∧
      ∀ j : Fin visits.length, ∀ reg,
        (numeric reg).read (byte visits[j.val])=(numeric reg).read (y visits[j.val].mark).long ∧
        (numeric reg).read (updated visits[j.val]) =
          (numeric reg).read ((run y w) visits[j.val].mark).long

/-- The actual matching numeric return certifies health for the
literal selected K10 offer and all significant outward marks.
The caller supplies the selected row, not packet health or code. -/
theorem of_selected {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {turn door : Fin n} {pre ret : List (Fin n)}
    (F : Found hp base (fun j => S.getD j fall) len op x pre (.out len))
    (T : BusyOnly hp base (fun j => S.getD j fall) len op
      (step (run x pre) turn) (.back len) ret (.back 0))
    (H : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len
      (run (step (run x pre) turn) ret) door op)
    (lo : 13≤op) (hi : op<408)
    (C : CommandClaim) (v : Payload) (K : C.source.occurrence.val=10)
    (hd : C.destination=none) (endAddr : S.getD len fall=address turn C.source)
    (sel : let y := run x pre
      (C,.advance v)∈actualOffers (oldPair B y turn) ((y turn).long,(y (rightNeighbor turn)).long)) :
    (let z := run (step (run x pre) turn) ret
     let a := (S.getD 0 fall).1
     bind (longGeometry B (z a)) 0 (atSite (z a).long 0)=.reply (output v)) ∧
    ∃ before launch after i code,
      pre=before++launch::after ∧ nodeOf op=some i ∧ get i=some code ∧
      Sweep hp base (step (run x before) launch) (fun j => S.getD j fall) len op after i code := by
  obtain ⟨health,hcode,_⟩ :=
    BStarReplyBack.numeric_selected_from_hit hp chart sep T H lo hi C v K hd endAddr sel
  obtain ⟨⟨q,Q,N,E⟩,R⟩ := BStarNumericTerminal.selected_return hp chart sep T C v K hd endAddr sel health
  refine ⟨R,?_⟩
  obtain ⟨u,w,e,split,_,_,_,P⟩ := F
  obtain ⟨i,code,Nd,J⟩ := exists_node lo hi
  have Y : run x pre = run (step (run x u) e) w := by
    rw [split,BStarResetSchedule.run_append]
    rfl
  have m : nodeOf q.opcode.toNat=some i := by rw [E,hcode,Nd]
  exact ⟨u,e,w,i,code,split,Nd,J,
    BStarNumericHealthy.successful_sweep hp chart sep P (Nat.le_refl _) q (Y ▸ Q) N i code m J⟩

#print axioms exists_node
#print axioms of_selected
end L4.BStarNumericHitSweep
