import Leader.L4.PhysicalRaceCutAdapters
import Leader.L4.BStarOwnerRecoveryPass
import Leader.L4.PhysicalCustodyTwoPass

namespace L4.PhysicalSixRaceReplay
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarLongToken BStarLongDoor BStarLongCommand BStarH6WordChart
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarAcquireAnchors
open BStarLongFixedRouting BStarAcquireForwardTrace BStarResetChartTouch
open BStarResetChartService BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarSeparatingRail BStarAcquireWaitControl
open BStarGeneratedOwner BStarClearanceSource BStarSeparatorControl
open PhysicalEligibleReply PhysicalRacePrefixes PhysicalRaceCutAdapters
open BStarResetHealthyService BStarAcquireRailCoverage BStarResetHealthyCycle

local notation "hp" => (show 0<2 by decide)

def pairWord {n : Nat} (d : Fin n) (a b : List (Fin n)) : List (Fin n) :=
  a++d::(b++[d])

private theorem commute_tail {n : Nat} {a b : List (Fin n)} (L : Commuted a b)
    (tail : List (Fin n)) : Commuted (a++tail) (b++tail) := by
  induction L with
  | refl => exact .refl _
  | trans _ _ ih ih' => exact .trans ih ih'
  | swap pre post e d H =>
    simpa only [List.append_assoc,List.cons_append] using Commuted.swap pre (post++tail) e d H

private theorem runQ {s n : Nat} (Q : Raw s n→Prop)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (w : List (Fin n)) (x : Raw s n) (I : Q x) :
    Q (rawRun x w) := by
  induction w generalizing x with
  | nil => exact I
  | cons e w ih => exact ih _ (closed _ _ I)

private theorem raw_append {s n : Nat} (x : Raw s n) (a b : List (Fin n)) :
    rawRun x (a++b)=rawRun (rawRun x a) b :=
  BStarResetSchedule.run_append _ _ _ _

private theorem stage_run {s n : Nat} {addr : Nat→Pos n} {len op : Nat}
    {x y : Raw s n} {w : List (Fin n)}
    (S : Stage hp addr len op x w y) : y=rawRun x w := by
  obtain ⟨_,_,I,_⟩ := S
  exact I

/-- The six successful observations are enough for one common replay
of the separator and the three healthy reset stages. All healthy
journeys in the premises start at the actual sampled cut, not replay
cuts. The separator and the last stage spend one success each, the
two middle consume→launch boundaries spend two each. -/
theorem recovered_of_six_cuts {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len op : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : Raw s n→Prop) (fiber : ∀ y,Q y→∀ j,Layout (rows s) base j=Layout (rows s) y j)
    (closed : ∀ y e,Q y→Q (rawNext s y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (head : ∀ i, let g := longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair (rows s) base i; continuation g.1 g.2=true)
    (qx : Q x) (u v gS res t₀ a₀ b₀ t₁ a₁ b₁ t₂ gF : List (Fin n)) :
    let addr := fun j=>S.getD j fall
    let root := (addr 0).1
    let d := RearTrace.predecessor root
    let before := rawRun x u
    let launched := rawNext s before d
    let arrived := rawRun launched v
    let actualS := rawRun arrived (gS++[d])
    let seed := rawRun actualS res
    let initial := rawNext s seed d
    let actual₀ := rawRun initial t₀
    let next₁ := rawRun actual₀ (pairWord d a₀ b₀)
    let actual₁ := rawRun next₁ t₁
    let next₂ := rawRun actual₁ (pairWord d a₁ b₁)
    let actual := u++[d]++v++(gS++[d])++res++[d]++t₀++pairWord d a₀ b₀++
      t₁++pairWord d a₁ b₁++t₂++(gF++[d])
    Launch (before root).long (launched root).long →
    Seen (rawNext s) (project addr) anyTag len launched (.out 0) v (.back 0) →
    Waiting hp base root op arrived → Clean (project addr) anyTag len arrived →
    Ready addr len 0 seed →
    Seen (rawNext s) (project addr) (healthyTag 0) len initial (.out 0) t₀ (.back 0) →
    Seen (rawNext s) (project addr) (healthyTag 1) len next₁ (.out 0) t₁ (.back 0) →
    Seen (rawNext s) (project addr) (healthyTag 2) len next₂ (.out 0) t₂ (.back 0) →
    (∀ e∈gS,DisjointMarks e d) →
    (∀ e∈a₀,DisjointMarks e d) → (∀ e∈b₀,DisjointMarks e d) →
    (∀ e∈a₁,DisjointMarks e d) → (∀ e∈b₁,DisjointMarks e d) →
    (∀ e∈gF,DisjointMarks e d) →
    ∃ credit, Commuted actual (credit++gF) ∧
      BStarOwnerRecoveryPass.Recovered hp base hh o x credit := by
  dsimp only
  intro launchedSep seenSep wait clean ready seen₀ seen₁ seen₂ AS A₀ B₀ A₁ B₁ AF
  let addr := fun j=>S.getD j fall
  let d := RearTrace.predecessor (addr 0).1
  let before := rawRun x u
  let launched := rawNext s before d
  let arrived := rawRun launched v
  let sepEnd := rawNext s arrived d
  let actualS := rawRun arrived (gS++[d])
  let seed := rawRun actualS res
  let old₀ := rawRun (rawNext s seed d) t₀
  let y₁ := rawNext s old₀ d
  let f₁ := rawNext s y₁ d
  let gap₀ := a₀++b₀
  let path₁ := gap₀++t₁
  let old₁ := rawRun f₁ path₁
  let y₂ := rawNext s old₁ d
  let f₂ := rawNext s y₂ d
  let gap₁ := a₁++b₁
  let path₂ := gap₁++t₂
  let old₂ := rawRun f₂ path₂
  let y₃ := rawNext s old₂ d
  let w₀ := d::(t₀++[d])
  let w₁ := d::(path₁++[d])
  let w₂ := d::(path₂++[d])
  let resid := gS++res
  let credit := u++(d::(v++[d]))++resid++w₀++w₁++w₂
  have qArr : Q arrived := runQ Q closed _ _ (closed _ _ (runQ Q closed _ _ qx))
  have qS : Q seed := runQ Q closed _ _ (runQ Q closed _ _ qArr)
  have L₀ : Launched base addr len 0 (rawNext s seed d) := PhysicalEligibleReply.launch C Q fiber closed sep (by decide) qS ready
  have E₀ := eligible_of_seen C Q fiber closed (by decide : (0 : Nat)<3) (closed _ _ qS) L₀ t₀ seen₀
  have R₁ : Ready addr len 1 y₁ := PhysicalEligibleReply.consume C (by decide) sep E₀.2
  have q₁ : Q y₁ := closed _ _ E₀.1
  have L₁ := PhysicalEligibleReply.launch C Q fiber closed sep (by decide : (1 : Nat)<3) q₁ R₁
  have G₀ : ∀ e∈gap₀,DisjointMarks e d := fun e J=>(List.mem_append.mp J).elim (A₀ e) (B₀ e)
  have P₁ := launched_gap_seen C Q fiber closed sep head cont (by decide : (1 : Nat)<3)
    (closed _ _ q₁) L₁ gap₀ G₀
  have T₁ : Seen (rawNext s) (project addr) (healthyTag 1) len f₁ (.out 0) path₁ (.back 0) :=
    append_next_seen (y:=old₀) A₀ B₀ P₁.1 seen₁
  have E₁ := eligible_of_seen C Q fiber closed (by decide : (1 : Nat)<3) (closed _ _ q₁) L₁ path₁ T₁
  have R₂ : Ready addr len 2 y₂ := PhysicalEligibleReply.consume C (by decide) sep E₁.2
  have q₂ : Q y₂ := closed _ _ E₁.1
  have L₂ := PhysicalEligibleReply.launch C Q fiber closed sep (by decide : (2 : Nat)<3) q₂ R₂
  have G₁ : ∀ e∈gap₁,DisjointMarks e d := fun e J=>(List.mem_append.mp J).elim (A₁ e) (B₁ e)
  have P₂ := launched_gap_seen C Q fiber closed sep head cont (by decide : (2 : Nat)<3)
    (closed _ _ q₂) L₂ gap₁ G₁
  have Old₁ : rawRun (rawRun old₀ (pairWord d a₀ b₀)) t₁ = old₁ := by
    dsimp only [old₁,path₁]
    rw [show rawRun old₀ (pairWord d a₀ b₀)=rawRun f₁ gap₀ from
          middle_race_endpoint old₀ d a₀ b₀ A₀ B₀]
    exact (BStarResetSchedule.run_append _ _ _ _).symm
  have sampled₂ : Seen (rawNext s) (project addr) (healthyTag 2) len
      (rawRun old₁ (pairWord d a₁ b₁)) (.out 0) t₂ (.back 0) := by
    rw [←Old₁]
    exact seen₂
  have T₂ : Seen (rawNext s) (project addr) (healthyTag 2) len f₂ (.out 0) path₂ (.back 0) :=
    append_next_seen (y:=old₁) A₁ B₁ P₂.1 sampled₂
  have E₂ := eligible_of_seen C Q fiber closed (by decide : (2 : Nat)<3) (closed _ _ q₂) L₂ path₂ T₂
  have phase₀ := ready.2.1
  have phase₁ := R₁.2.1
  have phase₂ := R₂.2.1
  have S₀ : Stage hp addr len 0 seed w₀ y₁ :=
    ⟨t₀,rfl,(raw_append (rawNext s seed d) t₀ [d]).symm,phase₀,ready.2.2,seen₀,E₀.2.2.2⟩
  have S₁ : Stage hp addr len 1 y₁ w₁ y₂ :=
    ⟨path₁,rfl,(raw_append (rawNext s y₁ d) path₁ [d]).symm,phase₁,R₁.2.2,T₁,E₁.2.2.2⟩
  have S₂ : Stage hp addr len 2 y₂ w₂ y₃ :=
    ⟨path₂,rfl,(raw_append (rawNext s y₂ d) path₂ [d]).symm,phase₂,R₂.2.2,T₂,E₂.2.2.2⟩
  have cutSep : actualS=rawRun sepEnd gS := by
    have K := rawRun_of_commuted arrived (bubble_door gS [] d AS)
    change rawRun arrived (gS++[d])=rawRun arrived (d::gS)
    simpa only [List.append_nil] using K
  have cutSeed : seed=rawRun sepEnd resid := by
    change rawRun actualS res=rawRun sepEnd (gS++res)
    rw [cutSep]
    exact (BStarResetSchedule.run_append _ _ _ _).symm
  have creditEnd : rawRun x credit=y₃ := by
    dsimp only [credit]
    rw [raw_append,raw_append,raw_append,raw_append,raw_append]
    have F : rawRun before (d::(v++[d]))=sepEnd := by
      change rawRun launched (v++[d])=sepEnd
      exact BStarResetSchedule.run_append _ _ _ _
    have F' : rawRun x (u++(d::(v++[d])))=sepEnd :=
      (raw_append x u _).trans F
    rw [F',←cutSep,←stage_run S₀,←stage_run S₁,←stage_run S₂]
  refine ⟨credit,?_,S,len,fall,C,u,v,resid,w₀,w₁,w₂,y₁,y₂,rfl,
    launchedSep,seenSep,clean,?_,S₁,?_⟩
  · have bubblePair (a b t : List (Fin n)) (A : ∀ e∈a,DisjointMarks e d)
        (B : ∀ e∈b,DisjointMarks e d) :
        Commuted (pairWord d a b ++ t) (d::d::((a++b)++t)) := by
      have H := bubble_door a (b++d::t) d A
      have K := commute_prefix [d]
        (bubble_door (a++b) t d (fun e J=>(List.mem_append.mp J).elim (A e) (B e)))
      refine Commuted.trans (v:=d::(a++(b++d::t))) ?_ ?_
      · simpa only [pairWord,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using H
      · simpa only [List.append_assoc,List.cons_append,List.nil_append,List.singleton_append] using K
    let pS := u++[d]++v
    let p₀ := pS++[d]++gS++res++[d]++t₀
    let p₁ := p₀++[d,d]++gap₀++t₁
    let p₂ := p₁++[d,d]++gap₁++t₂
    have BS := commute_prefix pS (bubble_door gS
      (res++[d]++t₀++pairWord d a₀ b₀++t₁++pairWord d a₁ b₁++t₂++(gF++[d])) d AS)
    have B0 := commute_prefix p₀ (bubblePair a₀ b₀
      (t₁++pairWord d a₁ b₁++t₂++(gF++[d])) A₀ B₀)
    have B1 := commute_prefix p₁ (bubblePair a₁ b₁ (t₂++(gF++[d])) A₁ B₁)
    have BF := commute_prefix p₂ (bubble_door gF [] d AF)
    simp only [p₂,p₁,p₀,pS,gap₀,gap₁,credit,w₀,w₁,w₂,resid,path₁,path₂,
      List.append_assoc,List.cons_append,List.nil_append,List.append_nil] at BS B0 B1 BF ⊢
    exact Commuted.trans BS (Commuted.trans B0 (Commuted.trans B1 BF))
  · change Stage hp addr len 0 (rawRun sepEnd resid) w₀ y₁
    rw [←cutSeed]
    exact S₀
  · rw [←creditEnd] at S₂
    exact S₂

/-- Exact replay credit starts at zero and ends at the final replayed
consume, strictly before any retained tail is counted as credit. -/
theorem recovered_prefix_credit {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true} {o : Owners (oldH6 (rows s) base)}
    {credit tail : List (Fin n)}
    (R : BStarOwnerRecoveryPass.Recovered hp base hh o x credit) :
    0<credit.length ∧ BStarRecoveryPass.Credit (rawNext s)
      (BStarOwnerRecoveryPass.Recovered hp base hh) o x (credit++tail) 0 credit.length := by
  have positive : 0<credit.length := by
    obtain ⟨S,len,fall,_,u,v,r,w₀,w₁,w₂,_,_,W,_⟩ := R
    rw [W]
    simp only [List.length_append,List.length_cons]
    omega
  exact ⟨positive,[],credit,tail,rfl,rfl,rfl,R⟩

theorem replay_holds_credit {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true} {o : Owners (oldH6 (rows s) base)}
    {sample credit tail : List (Fin n)}
    (C : Commuted sample (credit++tail))
    (R : BStarOwnerRecoveryPass.Recovered hp base hh o x credit) :
    ∃ replay, Commuted sample replay ∧
      HoldsCredit (BStarOwnerRecoveryPass.Recovered hp base hh) o x replay := by
  obtain ⟨L,H⟩ := recovered_prefix_credit (tail:=tail) R
  exact ⟨credit++tail,C,0,credit.length,L,H⟩

end L4.PhysicalSixRaceReplay
