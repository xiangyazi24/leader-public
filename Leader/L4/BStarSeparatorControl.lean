import Leader.L4.BStarResetControllerEntry
import Leader.L4.BStarResetChartService

/-! Control for an arbitrary newly issued tour, not just reset opcodes.
The owner door stays in the same WAIT until its outstanding command
returns; only the old K0 class, not payload equality, is needed. -/
namespace L4.BStarSeparatorControl
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongDoor BStarLongTransport BStarAcquireWaitControl
open BStarResetControllerEntry BStarResetRailRing BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarResetMarkAdapter BStarResetChartTouch BStarResetChartService BStarLongFixedRouting
open BStarSeparatingRail BStarCommitIssue

def anyTag : BStarSeparatingRail.Tag where
  F t := ∃ p, t=.forward p
  D t := ∃ p, t=.reply p

theorem bound_F (g : LongGeometry) (j : Fin 11) (p : Payload) :
    anyTag.F (bind g j (.forward p)) := by
  simp only [BStarLongCommand.bind]
  repeat first | exact ⟨_,rfl⟩ | split

theorem bound_D (g : LongGeometry) (j : Fin 11) (p : Payload) :
    anyTag.D (bind g j (.reply p)) := by
  simp only [BStarLongCommand.bind]
  split
  · exact ⟨_,rfl⟩
  · split <;> exact ⟨_,rfl⟩

theorem joined_wait_right (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b x.2).h6=true →
    LongDoorGuard.valid manifest x.2.long=true →
    (ctrlPhase.read x.2.long).toNat=2 →
    (atSite x.2.long 0=.trail ∨ anyTag.F (atSite x.2.long 0)) →
    control (largePair b x).2.long=control x.2.long := by
  dsimp only
  intro hh valid ph front
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  exact (joined_control k₁ k₂ t₂ J₁ J₂ r c p c₁ hp x valid).trans
    (door_projection g raw hh [] (f:=id) (by
      have E : oldDoor raw.2 (bind g.2 0 (atSite raw.2 0))=.hold := by
        rcases front with T|⟨v,F⟩
        · rw [show atSite raw.2 0=.trail from T]
          exact wait_holds_trail _ valid ph
        · rw [show atSite raw.2 0=.forward v from F]
          obtain ⟨u,U⟩ := bound_F g.2 0 v
          rw [U]
          exact wait_holds_forward _ _ valid ph
      change (match oldDoor raw.2 (bind g.2 0 (atSite raw.2 0)) with
      | .hold => (⟨[],[],[]⟩ : Selected)
      | .write q => ⟨[],[(true,q)],[]⟩
      | .acceptTour op p => ⟨[],[(true,BStarLongArithmetic.acceptFile raw.2 op p)],[]⟩).work=[]
      rw [E]) (fun _ => rfl))

theorem step_wait (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    {n : Nat} (x : Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁))
    (e i : Fin n) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    (oldHeaders b (x i)).h6=true →
    LongDoorGuard.valid manifest (x i).long=true →
    (ctrlPhase.read (x i).long).toNat=2 →
    (atSite (x i).long 0=.trail ∨ anyTag.F (atSite (x i).long 0)) →
    control (AllSizeS1Geometry.step b x e i).long=control (x i).long := by
  dsimp only
  intro hh v ph front
  by_cases E : i=e
  · subst i
    simpa only [AllSizeS1Geometry.step,if_true] using
      BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) hh
  · by_cases J : i=rightNeighbor e
    · subst i
      simpa only [AllSizeS1Geometry.step,if_neg E,if_true] using
        joined_wait_right k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) hh v ph front
    · simp only [AllSizeS1Geometry.step,if_neg E,if_neg J]

theorem before_receipt {len : Nat} {rail : BStarSeparatingRail.Rail} {z : Cursor}
    (G : Good anyTag len rail z) (live : z≠.back 0) :
    rail 0=.trail ∨ anyTag.F (rail 0) := by
  cases z with
  | out k =>
    by_cases Z : k=0
    · subst k; exact .inr G.2.1
    · exact .inl (G.2.2 0 (Nat.pos_of_ne_zero Z))
  | back k =>
    have K : k≠0 := fun Z => live (by rw [Z])
    exact .inl (G.2.2.1 0 (Nat.pos_of_ne_zero K))

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "XX" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)

theorem issue_chart {base x : XX} {hh : ∃ i, oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fallback : Pos n}
    (C : Chart hp base hh o S len fallback)
    (same : ∀ i, Layout B base i=Layout B x i)
    (distinct : ∀ e : Fin n,e≠rightNeighbor e) :
    let adr := fun j => S.getD j fallback
    let root := (adr 0).1
    let e := RearTrace.predecessor root
    let y := AllSizeS1Geometry.step B x e
    let w := (x root).long
    let op := (ctrlOp.read w).toNat
    LongDoorGuard.valid manifest w=true → (ctrlPhase.read w).toNat=1 →
    ((initial op w=none ∧ snapshot (y root).long=((.empty,1),0)) ∨
      (∃ a, initial op w=some a ∧ project adr y 0=forward op a ∧
        Good anyTag len (project adr y) (.out 0) ∧ control (y root).long=(2,ctrlOp.read w))) := by
  dsimp only
  intro V P
  let adr := fun j => S.getD j fallback
  let root := (adr 0).1
  let e := RearTrace.predecessor root
  let y := AllSizeS1Geometry.step B x e
  let w := (x root).long
  let op := (ctrlOp.read w).toNat
  have R : rightNeighbor e=root := RearTrace.right_predecessor root
  obtain ⟨H,K⟩ := root_header hp C same
  have E := exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e))
    (by rw [R]; exact H) (by rw [R]; exact V) (by rw [R]; exact P)
  have Y : y root=(largePair B (x e,x (rightNeighbor e))).2 := by
    simp only [y, AllSizeS1Geometry.step, ←R,if_neg (Ne.symm (distinct e)),if_true]
  rw [←Y,R] at E
  change snapshot (y root).long=(match initial op w with
    | none => ((.empty,1),0)
    | some a => ((forward op a,2),ctrlOp.read w)) at E
  cases I : initial op w with
  | none => rw [I] at E; exact .inl ⟨rfl,E⟩
  | some a =>
    rw [I] at E
    have K0 : atCursor y (adr 0)=atSite (y root).long 0 := by
      change atSite (y root).long (adr 0).2=_
      rw [K]
    have F : project adr y 0=forward op a := K0.trans (congrArg (fun s => s.1.1) E)
    refine .inr ⟨a,rfl,F,⟨Nat.zero_le _,?_,?_⟩,?_⟩
    · exact ⟨_,F⟩
    · intro j L
      omega
    · have P₂ : ctrlPhase.read (y root).long=2 := congrArg (fun s => s.1.2) E
      have Pₒ : ctrlOp.read (y root).long=ctrlOp.read w := congrArg (fun s => s.2) E
      exact Prod.ext P₂ Pₒ

end L4.BStarSeparatorControl
