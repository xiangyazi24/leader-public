import Leader.L4.Height.FreshCaptureSelectors
import Leader.L4.Height.FreshSetupTours
import Leader.L4.Height.FreshAdmissionStart

namespace L4.Height.FreshSetupProgress
open AllSizeProtocol PhysicalCustody ProductionCustody ProductionCycles
open BStarLongDoor BStarH6WordChart BStarResetChartTouch BStarGeneratedOwner
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarSteeredLikelihood FreshFirstAcquire

variable {s n : Nat}
local notation "hp" => (show 0<2 by decide)

variable {x : Raw s n} {g : CustodyWitness x}
local notation "h" => oldH6 (rows s) g.base

/-- Every physical change of PC during preparation is the matching
healthy receipt. The release supplies selector legality at opcode 8. -/
theorem setup_change (P : Production g) (o : Owners h) (a : Word n) (e : Fin n)
    (paid : accepted g o a e) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall)
    (idle : Current hp g.base (fun j=>S.getD j fall) len (rawNext s (rawRun x a) e) .idle)
    (w : Word n) (f : Fin n) :
    let z := rawNext s (rawRun x a) e
    let y := rawRun z w
    let i := (S.getD 0 fall).1
    let op := PC y i
    6≤op → op<10 → PC (rawNext s y f) i≠op →
      BStarNativeReceiptTape.Hit hp g.base (fun j=>S.getD j fall) len y f op := by
  dsimp only
  let z := rawNext s (rawRun x a) e
  let y := rawRun z w
  let root := (S.getD 0 fall).1
  let op := PC y root
  intro lo hi changePC
  have list : FreshSetupTours.Setup op ∨ op=8 := by
    unfold FreshSetupTours.Setup
    change 6≤op at lo
    change op<10 at hi
    omega
  have defined : initial op (y root).long≠none := by
    rcases list with (six|seven|nine)|eight
    · rw [six]; exact fun H=>Option.some_ne_none 0 (show some 0=none from H)
    · rw [seven]; exact fun H=>Option.some_ne_none 0 (show some 0=none from H)
    · rw [nine]; exact fun H=>Option.some_ne_none 0 (show some 0=none from H)
    · have E : root=(endpoint h g.hh o 0).1 := congrArg Prod.fst C.root
      have band : BStarGeneratedBandScan.Band y (endpoint h g.hh o 0).1 := by
        have old : BStarGeneratedBandScan.Band y root := by
          change 6≤op ∧ op≤408
          omega
        exact (congrArg (BStarGeneratedBandScan.Band y) E).mp old
      have H := (FreshCaptureSelectors.legal_on_band P o a e paid w band).2
      rw [eight]
      have target : initial 8 (y (endpoint h g.hh o 0).1).long≠none :=
        fun bad => Option.some_ne_none _ (H.symm.trans bad)
      exact (congrArg (fun i : Fin n => initial 8 (y i).long≠none) E).mpr target
  have Q := g.closed _ e (ready_run P a).1
  obtain ⟨G,M⟩ := FreshAdmissionStart.return_of_change g P C Q idle w f op defined rfl changePC
  rcases list with simple|load
  · exact FreshSetupTours.setup_receipt hp C (separation P) op simple w f G M
  · change BStarNativeReceiptTape.Hit hp g.base (fun j=>S.getD j fall) len y f op
    rw [load] at G M ⊢
    exact FreshSetupTours.load_receipt hp C (separation P) w f G M

/-- A fresh word going from ISSUE6 to an eventual RESET2 must first
cross ENABLE to ISSUE10. The intervening old marks all stay in preparation. -/
theorem enter_inject (P : Production g) (o : Owners h) (a : Word n) (e : Fin n)
    (paid : accepted g o a e) {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp g.base g.hh o S len fall)
    (idle : Current hp g.base (fun j=>S.getD j fall) len (rawNext s (rawRun x a) e) .idle)
    (lead w : Word n) :
    let z := rawNext s (rawRun x a) e
    let root := (S.getD 0 fall).1
    let entry := rawRun z lead
    PC entry root=6 → PC (rawRun entry w) root=2 →
      ∃ u f v,w=u++f::v ∧
        BStarNativeReceiptTape.Hit hp g.base (fun j=>S.getD j fall) len (rawRun entry u) f 9 ∧
        ∀ a j b,u++[f]=a++j::b → 6≤PC (rawRun entry a) root ∧ PC (rawRun entry a) root<10 := by
  dsimp only
  let z := rawNext s (rawRun x a) e
  let entry := rawRun z lead
  let root := (S.getD 0 fall).1
  intro issued reset
  let reg := fun k : Nat=>6≤k ∧ k<10
  obtain ⟨u,f,v,W,old,out,allOld⟩ := first_outside reg entry root w
    (by rw [show PC entry root=6 from issued]; decide)
    (by rw [show PC (rawRun entry w) root=2 from reset]; decide)
  let k := PC (rawRun entry u) root
  have bounds : 6≤k ∧ k<10 := old
  have gap : PC (rawNext s (rawRun entry u) f) root≠k := fun eq=>out (eq ▸ old)
  have replay : rawRun z (lead++u)=rawRun entry u := BStarResetSchedule.run_append (rawNext s) z lead u
  have receipt := setup_change P o a e paid C idle (lead++u) f
  change 6≤PC (rawRun z (lead++u)) root → _ at receipt
  rw [replay] at receipt
  have hit := receipt bounds.1 bounds.2 gap
  have next : PC (rawNext s (rawRun entry u) f) root=k+1 := hit.2.2.2.1
  have outside : ¬(6≤k+1 ∧ k+1<10) := fun p=>out (next ▸ p)
  have atNine : k=9 := by omega
  exact ⟨u,f,v,W,atNine ▸ (show BStarNativeReceiptTape.Hit hp g.base
    (fun j=>S.getD j fall) len (rawRun entry u) f k from hit),allOld⟩

end L4.Height.FreshSetupProgress
