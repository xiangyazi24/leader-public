import Leader.L4.BStarGeneratedPCAncestry

namespace L4.BStarSerialTourDebt
open AllSizeProtocol BStarTrace BStarLongWork BStarLongDoor BStarLongToken BStarLongCommand BStarLongLayout
open BStarLiteralPC BStarResetControllerProgress BStarArithmeticControllerReturn
open BStarGeneratedPCAncestry

/-- Number of possible paid command tours before the first accepted
cycle-ending RREL. Opcodes 3 through 412 are before the reset/return
band. A restart to zero is not itself a release. -/
def toursLeft (op : Nat) : Nat := if op<3 then 3-op else 416-op

theorem toursLeft_bounds {op : Nat} (bound : op<413) :
    1≤toursLeft op ∧ toursLeft op≤413 := by
  unfold toursLeft
  split <;> omega

private theorem old_order (x : BitVec LW) (f : Payload)
    (bound : (ctrlOp.read x).toNat<413) :
    pcNext x f=0 ∨ ((ctrlOp.read x).toNat<pcNext x f ∧ pcNext x f<413) := by
  simp only [pcNext]
  split
  · exact .inl rfl
  · split
    · rename_i arithmetic
      have hr := (arithmetic_range (ctrlOp.read x).toNat arithmetic).2
      rcases successor_order x (ctrlOp.read x).toNat hr with E|F
      · exact .inl E
      · exact .inr ⟨by omega,by omega⟩
    · exact ordinary_progress x _ f bound

/-- During the three reset tours, a matching healthy reply advances
exactly one PC. A malformed or mismatched reset is not silently
classified as successful progress. -/
theorem reset_pcNext (x : BitVec LW) (f : Payload)
    (phase : (ctrlOp.read x).toNat<3) (healthy : f.fault=0)
    (same : f.opcode.toNat=(ctrlOp.read x).toNat) :
    pcNext x f=(ctrlOp.read x).toNat+1 := by
  have band : (ctrlOp.read x).toNat=0 ∨ (ctrlOp.read x).toNat=1 ∨ (ctrlOp.read x).toNat=2 := by omega
  rcases band with op|op|op
  all_goals simp [pcNext,healthy,same,op,nextOrdinary,arithKind]

/-- Every generated consume saves one tour or witnesses actual RREL.
The caller supplies matching healthy replies on the reset sub-band
only; faulty data/control replies outside it can reset to zero. -/
theorem pcNext_pays_or_release (x : BitVec LW) (f : Payload)
    (bound : (ctrlOp.read x).toNat<413)
    (reset : (ctrlOp.read x).toNat<3 →
      f.fault=0 ∧ f.opcode.toNat=(ctrlOp.read x).toNat) :
    ((ctrlOp.read x).toNat=2 ∧ pcNext x f=3) ∨
      toursLeft (pcNext x f)+1≤toursLeft (ctrlOp.read x).toNat := by
  let op := (ctrlOp.read x).toNat
  by_cases low : op<3
  · obtain ⟨ok,same⟩ := reset low
    have eq : pcNext x f=op+1 := reset_pcNext x f low ok same
    change (op=2 ∧ pcNext x f=3) ∨ toursLeft (pcNext x f)+1≤toursLeft op
    rw [eq]
    by_cases last : op=2
    · exact .inl ⟨last,by omega⟩
    · right
      rw [toursLeft,toursLeft,if_pos (by omega : op+1<3),if_pos low]
      omega
  · change (op=2 ∧ pcNext x f=3) ∨ toursLeft (pcNext x f)+1≤toursLeft op
    right
    rcases old_order x f bound with reset|⟨H,U⟩
    · rw [reset,toursLeft,toursLeft,if_pos (by decide : (0:Nat)<3),if_neg low]
      change op<413 at bound
      omega
    · change op<pcNext x f at H
      rw [toursLeft,toursLeft,if_neg (by omega : ¬pcNext x f<3),if_neg low]
      omega

open BStarLongToken BStarGeneratedOwner BStarSeparatingRail BStarLongClaims
open BStarAcquireVisitOrder BStarLongTransport

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B

/-- The tour debt law at one actual generated consume mark. The
exception is precisely the old 2 -> clean source 3 release boundary,
not a source reset or the publication event. -/
theorem consume_pays_or_release {base x : X} {addr : Nat→Pos n} {len op : Nat} {e : Fin n}
    (root : (addr 0).2=0) (head : (oldHeaders B (x (addr 0).1)).h6=true)
    (sep : e≠rightNeighbor e)
    (cur : Current hp base addr len x (.busy op (.back 0)))
    (evt : Event hp addr len x e (.busy op (.back 0)) .idle)
    (reset : ∀ f, op<3 →
      bind (longGeometry B (x (addr 0).1)) 0 (atSite (x (addr 0).1).long 0)=.reply f →
      f.fault=0 ∧ f.opcode.toNat=op) :
    let q := (ctrlOp.read (step x e (addr 0).1).long).toNat
    (op=2 ∧ q=3) ∨ toursLeft q+1≤toursLeft op := by
  dsimp only
  obtain ⟨f,F,E⟩ := consume_pc hp root head sep cur evt
  have oldpc : (ctrlOp.read (x (addr 0).1).long).toNat=op := cur.1.2.2.2
  have valid : LongDoorGuard.valid manifest (x (addr 0).1).long=true := cur.1.2.1
  have bound : (ctrlOp.read (x (addr 0).1).long).toNat<413 := by
    unfold LongDoorGuard.valid at valid
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp valid).2
  have H := pcNext_pays_or_release (x (addr 0).1).long f bound (fun low=>by
    rw [oldpc] at low ⊢
    exact reset f low F)
  rw [oldpc] at H
  rw [E]
  exact H

#print axioms consume_pays_or_release
#print axioms pcNext_pays_or_release
end L4.BStarSerialTourDebt
