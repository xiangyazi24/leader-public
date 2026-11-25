import Leader.L4.BStarCopyFenceCuts
import Leader.L4.BStarCopyCleanupOriginal
import Leader.L4.BStarCopyLeftFenceHold
import Leader.L4.BStarCopyAttemptBand

namespace L4.BStarCopySetupCuts
open BStarCopyFenceCuts
open BStarLongCommand
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarGeneratedPCAncestry
open BStarGeneratedBandScan BStarNativeReceiptTape BStarOwnerLaunchOrigin
open BStarCopyGateAuthority BStarOwnerControlHistory BStarResetChartService
open BStarCopyAttemptBand (band_step_exact)
open BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem original_setup {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q origin)
    (fiber : ∀ y,Q y → ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    {w : List (Fin n)}
    (A : BStarPostCutAttempt.AttemptPrefix hp base origin (fun j=>S.getD j fall) len w) :
    let addr := fun j=>S.getD j fall
    ∃ (lead before8 before9 before10 fence num tail : List (Fin n))
      (ack5 ack8 ack9 ack10 ack11 ack12 : Fin n) (m : Mode),
      w=lead++ack5::(before8++ack8::(before9++ack9::(before10++ack10::(fence++ack11::(num++ack12::tail))))) ∧
      let entry := step (play origin lead) ack5
      let from8 := step (play entry before8) ack8
      let from9 := step (play from8 before9) ack9
      let from10 := step (play from9 before10) ack10
      let from11 := step (play from10 fence) ack11
      GeneratedOwner hp base addr len origin .idle lead (.busy acquire (.back 0)) ∧
      Event hp addr len (play origin lead) ack5 (.busy acquire (.back 0)) .idle ∧
      pc entry (addr 0).1=6 ∧
      GeneratedOwner hp base addr len entry .idle before8 (.busy 8 (.back 0)) ∧
      Found hp base addr len 8 entry before8 (.back 0) ∧
      Hit hp base addr len (play entry before8) ack8 8 ∧
      GeneratedOwner hp base addr len from8 .idle before9 (.busy 9 (.back 0)) ∧
      Found hp base addr len 9 from8 before9 (.back 0) ∧
      Hit hp base addr len (play from8 before9) ack9 9 ∧
      GeneratedOwner hp base addr len from9 .idle before10 (.busy 10 (.back 0)) ∧
      Found hp base addr len 10 from9 before10 (.back 0) ∧
      Hit hp base addr len (play from9 before10) ack10 10 ∧
      GeneratedOwner hp base addr len from10 .idle fence (.busy 11 (.back 0)) ∧
      Hit hp base addr len (play from10 fence) ack11 11 ∧
      GeneratedOwner hp base addr len from11 .idle num (.busy 12 (.back 0)) ∧
      Found hp base addr len 12 from11 num (.back 0) ∧
      Hit hp base addr len (play from11 num) ack12 12 ∧
      GeneratedOwner hp base addr len (step (play from11 num) ack12) .idle tail m := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  have stable (x : X) (l : List (Fin n)) (J : Q x) : Q (play x l) := by
    induction l generalizing x with
    | nil => exact J
    | cons e w ih => exact ih _ (closed _ e J)
  obtain ⟨lead,mid,late,hold,a5,pick,op,W,prior,receipt,P6,
    first,finish,M,P408,live,_⟩ := A
  let old := play origin lead
  let entry := step old a5
  have oldInv : Q old := stable origin lead I
  have oldCurrent := BStarGeneratedTapeCuts.at_end hp prior
  have own : a5=RearTrace.predecessor root := by cases receipt with | consume _ e _ => exact e
  obtain ⟨mode,evt,C⟩ := current_step hp chart Q fiber (fun y q e => closed y e q) sep oldInv a5 _ oldCurrent
  have entered : Current hp base addr len entry .idle := by
    cases evt with
    | transit _ _ _ h _ => exact (h rfl).elim
    | arrived_hold _ n => exact (n own).elim
    | consume _ _ _ => exact C
  have fresh : Q entry := closed _ _ oldInv
  obtain ⟨bm,T,_,_⟩ := generated_word hp chart Q fiber (fun y q e => closed y e q) sep first .idle fresh entered
  have V : LiveAt hp chart entry first := by
    intro p q E
    refine ⟨fiber _ (stable entry p fresh),?_⟩
    cases q with
    | nil =>
      have F : first=p := by simpa using E
      rw [←F]
      change pc (play entry first) root=408 at P408
      change 6≤pc (play entry first) root ∧ pc (play entry first) root≤408
      rw [P408]
      decide
    | cons e q => exact (live p e q E).1
  have high : 12<pc (play entry first) root := by
    change pc (play entry first) root=408 at P408
    rw [P408]
    decide
  obtain ⟨before8,a8,after8,W8,G8,H8,T8,V8⟩ :=
    ack_at hp chart sep T V 8 (by change pc entry root≤8; change pc entry root=6 at P6; omega) (show 8<pc (play entry first) root by omega)
  let x8 := step (play entry before8) a8
  have eq8 : play entry first=play x8 after8 := by
    rw [W8,BStarResetSchedule.run_append]
    rfl
  have pc9 : pc x8 root=9 := H8.2.2.2.1
  obtain ⟨b9,b10,f,num,remain,a9,a10,a11,a12,E,F⟩ :=
    from_compiler_band hp chart sep T8 V8 (show pc x8 root≤9 from Nat.le_of_eq pc9) (eq8 ▸ high)
  obtain ⟨_,Tail,_,_⟩ := generated_word hp chart Q fiber (fun y q e => closed y e q) sep (finish++pick::hold) bm
    (stable entry first fresh) (BStarGeneratedTapeCuts.at_end hp T)
  obtain ⟨G9,H9,G10,H10,G11,H11,G12,launch,H12,End⟩ := F
  let x9 := step (play x8 b9) a9
  let x10 := step (play x9 b10) a10
  let x11 := step (play x10 f) a11
  let x12 := step (play x11 num) a12
  have cutEq : play x12 remain=play entry first := by
    rw [eq8,E,BStarResetSchedule.run_append]
    change play x12 remain=play x9 (b10++a10::(f++a11::(num++a12::remain)))
    rw [BStarResetSchedule.run_append]
    change play x12 remain=play x10 (f++a11::(num++a12::remain))
    rw [BStarResetSchedule.run_append]
    change play x12 remain=play x11 (num++a12::remain)
    rw [BStarResetSchedule.run_append]
    rfl
  have join {x : X} {a b c : Mode} {u v : List (Fin n)}
      (R : GeneratedOwner hp base addr len x a u b)
      (P : GeneratedOwner hp base addr len (play x u) b v c) :
      GeneratedOwner hp base addr len x a (u++v) c := by
    induction R with
    | endpoint _ => exact P
    | next I E _ ih => exact .next I E (ih P)
  have final := join End (cutEq.symm ▸ Tail)
  refine ⟨lead,before8,b9,b10,f,num,remain++(finish++pick::hold),a5,a8,a9,a10,a11,a12,_,?_,
    prior,receipt,P6,G8,from_idle hp G8,H8,G9,from_idle hp G9,H9,
    G10,from_idle hp G10,H10,G11,H11,G12,launch,H12,final⟩
  rw [W,M,W8,E]
  simp only [List.append_assoc,List.cons_append]

end L4.BStarCopySetupCuts
