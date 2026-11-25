import Leader.L4.BStarDirtyReplySweep
import Leader.L4.BStarClearanceIndexedWait
import Leader.L4.BStarSeparatorControl

namespace L4.BStarClearanceSource
set_option maxRecDepth 1200
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongCommand
open BStarH6WordChart
open BStarLongDoor BStarResetControllerEntry BStarAcquireWaitControl BStarDirtyReplySweep

def Held (w : BitVec LW) : Prop :=
  LongDoorGuard.valid manifest w=true ∧ (ctrlPhase.read w).toNat=2 ∧
    (atSite w 0=.trail ∨ ∃ p, atSite w 0=.forward p)

def Issue (w : BitVec LW) : Prop :=
  LongDoorGuard.valid manifest w=true ∧ (ctrlPhase.read w).toNat=1

def Launch (w y : BitVec LW) : Prop :=
  Issue w ∧ ∃ a, initial (ctrlOp.read w).toNat w=some a ∧
    snapshot y=((forward (ctrlOp.read w).toNat a,2),ctrlOp.read w)

theorem issue_of_snapshot {w : BitVec LW} {op : Nat} (O : op<413)
    (H : snapshot w=((.empty,1),BitVec.ofNat 9 op)) : Issue w := by
  have P : ctrlPhase.read w=(1 : BitVec 2) := congrArg (fun q => q.1.2) H
  have OPC : ctrlOp.read w=BitVec.ofNat 9 op := congrArg (fun q => q.2) H
  have E : op % 512=op := Nat.mod_eq_of_lt (by omega)
  have N : (ctrlOp.read w).toNat=op := by
    exact (congrArg (fun v : BitVec 9 => v.toNat) OPC).trans E
  have one : (ctrlPhase.read w).toNat=1 := by rw [P]; rfl
  constructor
  · change ((((ctrlPhase.read w).toNat == 1) || ((ctrlPhase.read w).toNat == 2)) &&
      decide ((ctrlOp.read w).toNat<413))=true
    simp [one,N,O]
  · exact one

private theorem valid_phase (w : BitVec LW) (V : LongDoorGuard.valid manifest w=true) :
    (ctrlPhase.read w).toNat=1 ∨ (ctrlPhase.read w).toNat=2 := by
  have E := (Bool.and_eq_true_iff.mp V).1
  exact (Bool.or_eq_true_iff.mp E).imp beq_iff_eq.mp beq_iff_eq.mp

theorem rstop_args (w : BitVec LW) : initial 0 w=some 0 := by rfl

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

/-- One actual source mark outside held WAIT either launches an
identified command or installs an empty legal ISSUE. An inherited
reply may advance the opcode but it is not itself a launch. -/
theorem dirty_source (x : X) (root : Fin n)
    (st : oldH6 B x root=true) (distinct : ∀ e : Fin n, e≠rightNeighbor e)
    (N : ¬Held (x root).long) :
    let e := RearTrace.predecessor root
    let w := (x root).long
    let y := (AllSizeS1Geometry.step B x e root).long
    Launch w y ∨ ∃ op<413, snapshot y=((.empty,1),BitVec.ofNat 9 op) := by
  dsimp only
  let e := RearTrace.predecessor root
  let w := (x root).long
  let pair := (x e,x (rightNeighbor e))
  have R : rightNeighbor e=root := RearTrace.right_predecessor root
  have Z : (AllSizeS1Geometry.step B x e root).long=(largePair B pair).2.long := by
    simp only [pair,AllSizeS1Geometry.step,←R,if_neg (Ne.symm (distinct e)),if_true]
  have H : (oldHeaders B pair.2).h6=true := by
    change (oldHeaders B (x (rightNeighbor e))).h6=true
    rw [R]; exact st
  have W : pair.2.long=w := by change (x (rightNeighbor e)).long=_; rw [R]
  change Launch w (AllSizeS1Geometry.step B x e root).long ∨ _
  rw [Z]
  cases V : LongDoorGuard.valid manifest w with
  | false =>
    exact .inr ⟨0,by decide,guard_restart k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair H (W.symm ▸ V)⟩
  | true =>
    rcases valid_phase w V with I|I
    · have P := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair H (W.symm ▸ V) (W.symm ▸ I)
      rw [W] at P
      cases A : initial (ctrlOp.read w).toNat w with
      | none =>
        rw [A] at P
        exact .inr ⟨0,by decide,P⟩
      | some a =>
        rw [A] at P
        exact .inl ⟨⟨V,I⟩,a,A,P⟩
    · cases K : atSite w 0 with
      | trail => exact (N ⟨V,I,.inl K⟩).elim
      | forward pay => exact (N ⟨V,I,.inr ⟨pay,K⟩⟩).elim
      | empty =>
        have P := exact_empty_entry k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair H (W.symm ▸ K)
        rcases P with ⟨_,S⟩|⟨a,_,phase,_,_⟩
        · exact .inr ⟨0,by decide,S⟩
        · rw [W,I] at phase
          contradiction
      | reply pay =>
        obtain ⟨op,H',Y⟩ := wait_raw_reply k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair pay H
          (W.symm ▸ V) (W.symm ▸ I) (W.symm ▸ K)
        exact .inr ⟨op,(H'.elim (fun h => h.symm ▸ (by decide : 0<413)) And.right),Y⟩

private theorem issue_outcome (x : X) (root : Fin n)
    (st : oldH6 B x root=true) (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (I : Issue (x root).long) :
    let e := RearTrace.predecessor root
    let w := (x root).long
    let y := (AllSizeS1Geometry.step B x e root).long
    snapshot y =
      match initial (ctrlOp.read w).toNat w with
      | none => ((.empty,1),0)
      | some a => ((forward (ctrlOp.read w).toNat a,2),ctrlOp.read w) := by
  dsimp only
  let e := RearTrace.predecessor root
  have R : rightNeighbor e=root := RearTrace.right_predecessor root
  have Q := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
    (by rw [R]; exact st) (by rw [R]; exact I.1) (by rw [R]; exact I.2)
  change snapshot (AllSizeS1Geometry.step B x e root).long=_
  rw [show AllSizeS1Geometry.step B x e root=(largePair B (x e,x (rightNeighbor e))).2 by
    simp only [AllSizeS1Geometry.step,←R,if_neg (Ne.symm (distinct e)),if_true]]
  rw [R] at Q ⊢
  exact Q

/-- Once the source is not held, at most three successive incoming
marks suffice for a genuinely issued command. This is a constructed
word, not a claim that every three incident marks serve the source. -/
theorem nonheld_three (root : Fin n) (x : X)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e)
    (N : ¬Held (x root).long)
    (st : oldH6 B x root=true)
    (fixed : let step := fun y => AllSizeS1Geometry.step B y (RearTrace.predecessor root)
      oldH6 B (step x) root=true ∧ oldH6 B (step (step x)) root=true) :
    let step := fun y => AllSizeS1Geometry.step B y (RearTrace.predecessor root)
    Launch (x root).long (step x root).long ∨
      Launch (step x root).long (step (step x) root).long ∨
      Launch (step (step x) root).long (step (step (step x)) root).long := by
  dsimp only
  let f := fun y => AllSizeS1Geometry.step B y (RearTrace.predecessor root)
  let x₁ := f x
  let x₂ := f x₁
  obtain L|⟨op,O,P⟩ := dirty_source hp x root st distinct N
  · exact .inl L
  have I₁ : Issue (x₁ root).long := issue_of_snapshot O P
  have C := issue_outcome hp x₁ root fixed.1 distinct I₁
  dsimp only at C
  cases A : initial (ctrlOp.read (x₁ root).long).toNat (x₁ root).long with
  | some a =>
    rw [A] at C
    exact .inr (.inl ⟨I₁,a,A,C⟩)
  | none =>
    rw [A] at C
    have C0 : snapshot (x₂ root).long=((.empty,1),BitVec.ofNat 9 0) := C
    have I₂ := issue_of_snapshot (by decide : 0<413) C0
    have op0 : (ctrlOp.read (x₂ root).long).toNat=0 :=
      congrArg (fun q : (Token × BitVec 2) × BitVec 9 => q.2.toNat) C0
    have args : initial (ctrlOp.read (x₂ root).long).toNat (x₂ root).long=some 0 := by
      exact (congrArg (fun k => initial k (x₂ root).long) op0).trans (rstop_args _)
    have E := issue_outcome hp x₂ root fixed.2 distinct I₂
    dsimp only at E
    rw [args] at E
    exact .inr (.inr ⟨I₂,0,args,E⟩)

open BStarLongClaims BStarLongTransport BStarLongEvents

/-- The stopping state is tested before choosing the mark. Thus a held
source certifies the WAIT hold premise for every mark, not merely the
nomination. Absent genuine WAIT, the preceding three-mark lemma applies. -/
theorem held_before (x : X) (root e : Fin n) (hold : Held (x root).long) :
    BStarClearanceIndexedWait.BeforeOwnService hp x root e := by
  intro R
  obtain ⟨V,I,T⟩ := hold
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have RO : readK raw (BStarLongClaims.R 0)=atSite (x root).long 0 := by
    change atSite (x (rightNeighbor e)).long 0=_
    rw [R]
  refine ⟨by rw [R]; exact V,by rw [R]; exact I,?_⟩
  change bound g (readK raw) (BStarLongClaims.R 0)=.trail ∨
    ∃ q, bound g (readK raw) (BStarLongClaims.R 0)=.forward q
  change bind g.2 0 (readK raw (BStarLongClaims.R 0))=.trail ∨
    ∃ q, bind g.2 0 (readK raw (BStarLongClaims.R 0))=.forward q
  rw [RO]
  rcases T with ht|⟨pay,hp⟩
  · rw [ht]
    exact .inl rfl
  · rw [hp]
    exact .inr (bind_forward_class g.2 0 pay)

end L4.BStarClearanceSource
