import Leader.L4.Height.FenceLineTransfer
import Leader.L4.Height.ProductionWidths
import Leader.L4.Height.FenceCoverage
import Leader.L4.Height.CandidateResidence
import Leader.L4.Height.GateResidence

namespace L4.Height.ProductionFence
open AllSizeProtocol BStarH6WordChart BStarLongClaims BStarLongWork BStarTrace
open BStarAcquireLiteralChain BStarAcquireVisitOrder BStarResetChartTouch BStarGeneratedOwner
open BStarLongFixedRouting BStarLongPackets BStarClearanceDataChart
open FenceEmbedding FenceProduction FenceLineTransfer OpenFenceLine
open Classical
noncomputable section

def labels {n : Nat} (play : List (Fin n) → Fin n → Fin n) :
    List (Fin n) → List (Fin n) → List (Fin n)
  | _,[] => []
  | a,e::w => play a e :: labels play (a++[e]) w

private theorem labels_join {n : Nat} (f : List (Fin n) → Fin n → Fin n) (a u v : List (Fin n)) :
    labels f a (u++v)=labels f a u++labels f (a++u) v := by
  induction u generalizing a with
  | nil => simp [labels]
  | cons e u ih => simp only [List.cons_append,labels,ih,List.append_assoc,List.nil_append]

private theorem zero_at (u : Nat → Bool) {h : Nat} (clear : occupiedCount u h=0)
    (k : Nat) (positive : 0<k) (small : k≤h) : u k=false := by
  induction h with
  | zero => omega
  | succ h ih =>
    change occupiedCount u h+(u (h+1)).toNat=0 at clear
    by_cases endAt : k=h+1
    · subst k
      cases e : u (h+1) <;> simp [e] at *
    · exact ih (by omega) (by omega)

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "raw" => BStarResetSchedule.run step

private def stock (base : X) (play : List (Fin n) → Fin n → Fin n) (a : List (Fin n)) :=
  (labels play [] a).foldl (fun u e => comparisonNext hp base e u) (fun _ _ => true)

private theorem stock_next (base : X) (f : List (Fin n) → Fin n → Fin n) (a : List (Fin n)) (e : Fin n) :
    stock hp base f (a++[e])=comparisonNext hp base (f a e) (stock hp base f a) := by
  simp [stock,labels_join,labels,List.foldl_append]

private theorem frozen_run (base x : X) (w : List (Fin n)) (u : Fin n → Sheet → Bool)
    (fixed : ∀ v j,Layout B base j=Layout B (raw x v) j) :
    comparisonRun hp x u w=w.foldl (fun old e => comparisonNext hp base e old) u := by
  induction w generalizing x u with
  | nil => rfl
  | cons e w ih =>
    change comparisonRun hp (step x e) (comparisonNext hp x e u) w=_
    rw [←comparison_fiber hp (show ∀ j,Layout B base j=Layout B x j from fixed [])]
    exact ih _ _ (fun v j => fixed (e::v) j)

/-- The actual busy command can be acknowledged early. Otherwise the two full
comparisons dominate each represented mobile of this owner on the same tape. -/
theorem drain_or_exit {base origin : X} {hh : ∃ i,oldH6 B base i=true} {o : Owners (oldH6 B base)}
    {S : List (Pos n)} {len : Nat} {fall : Pos n} (C : Chart hp base hh o S len fall)
    (Q : X → Prop) (fiber : ∀ y,Q y → ∀ j,Layout B base j=Layout B y j)
    (keep : ∀ y,Q y → ∀ e,Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (initial : Q origin) (clean : Current hp base (fun j=>S.getD j fall) len origin .idle)
    (past : List (Fin n)) {u v width H : Nat}
    (L : BStarCopyLeftStrip.Strip B base (S.getD 0 fall).1 u width)
    (R : BStarCopyLeftStrip.Strip B base (S.getD len fall).1 v width)
    (leftSize : u+width≤H) (rightSize : v+width≤H)
    (play : List (Fin n) → Fin n → Fin n) (twice : Twice play) :
    let hi := (S.getD 0 fall).1
    let mid := (S.getD len fall).1
    let addr := fun j => S.getD j fall
    let busy := fun a => ∃ z, Current hp base addr len (raw origin (past++a)) (.busy 11 z)
    let covered := fun i sh =>
      (∃ k,0<k ∧ k≤u+width ∧ (BStarCopyRightStrip.addr hi (k-1),BStarCopyLeftStrip.rail u (k-1))=(i,sh)) ∨
      (∃ k,0<k ∧ k≤v+width ∧ (BStarCopyRightStrip.addr mid (v+width-k),returnRail v (v+width-k))=(i,sh))
    Clearance H (pairedPaths (u+width) (v+width) (leftBond hi) (rightBond mid (v+width))) (fun a =>
      let w := labels play [] a
      (∃ pre rest,w=pre++rest ∧ ¬busy pre) ∨ ∀ i sh, dataOwner (oldH6 B base) i sh=o.val →
        covered i sh → (readLane (Sheet.index sh) (raw origin (past++w) i).long).mobile=.empty) := by
  dsimp only
  let l := u+width
  let rlen := v+width
  let hi := (S.getD 0 fall).1
  let mid := (S.getD len fall).1
  let left := leftStock hi u
  let right := rightStock mid v rlen
  let atW := stock hp base play
  have countsL (a : List (Fin n)) : occupiedCount (left (atW a)) l=count l (leftBond hi) play a l := by
    apply transfer (stock:=fun b => left (atW b)) <;> try exact Nat.le_refl _
    · intro k _ _; rfl
    · intro b e k pos small
      dsimp only [atW]
      rw [stock_next]
      exact left_balance hp L sep (play b e) _ k pos small
  have countsR (a : List (Fin n)) : occupiedCount (right (atW a)) rlen=count rlen (rightBond mid rlen) play a rlen := by
    apply transfer (stock:=fun b => right (atW b)) <;> try exact Nat.le_refl _
    · intro k _ _; rfl
    · intro b e k pos small
      dsimp only [atW]
      rw [stock_next]
      exact right_balance hp R sep (play b e) _ k pos small
  have clock := paired_clearance (Nat.add_pos_left L.seam_pos _) (Nat.add_pos_left R.seam_pos _)
    leftSize rightSize (leftBond hi) (rightBond mid rlen) play twice
  have qword (a : List (Fin n)) : Q (raw origin a) := by
    obtain ⟨_,_,q,_⟩ := generated_word hp C Q fiber keep sep a .idle initial clean
    exact q
  apply clock.mono
  intro a drain
  classical
  by_cases early : ∃ pre rest, labels play [] a=pre++rest ∧
      ¬∃ z,Current hp base (fun j=>S.getD j fall) len (raw origin (past++pre)) (.busy 11 z)
  · exact .inl early
  · right
    let w := labels play [] a
    have scope (b : List (Fin n)) (e : Fin n) (c : List (Fin n)) (cut : w=b++e::c) :=
      generated_word hp C Q fiber keep sep (past++b) .idle initial clean
    have dom := busy_fence_comparison_word hp C sep past w (fun _ _ => true) (by
      intro b e c cut
      obtain ⟨z,I⟩ := Classical.not_not.mp (fun missing => early ⟨b,e::c,cut,missing⟩)
      obtain ⟨d,G,q,J⟩ := scope b e c cut
      have same := current_mode_unique hp d (.busy 11 z) J I
      exact ⟨fiber _ q,z,same ▸ G,I⟩) (fun _ _ _ _ => rfl)
    have fixed (b : List (Fin n)) (j : Fin n) :
        Layout B base j=Layout B (raw (raw origin past) b) j := by
      rw [←BStarResetSchedule.run_append]
      exact fiber _ (qword (past++b)) j
    rw [frozen_run hp base _ _ _ fixed] at dom
    intro i sh owned represented
    have below := dom i sh owned
    change MobileBelow _ (atW a i sh) at below
    have empty : atW a i sh=false := by
      rcases represented with ⟨k,pos,small,eq⟩|⟨k,pos,small,eq⟩
      · have E := zero_at _ ((countsL a).trans drain.1) k pos small
        change atW a _ _=false at E
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        exact E
      · have E := zero_at _ ((countsR a).trans drain.2) k pos small
        change atW a _ _=false at E
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
        exact E
    exact Classical.not_not.mp (fun nonempty => Bool.noConfusion (empty.symm.trans (below nonempty)))

open PhysicalCustody ProductionCustody BStarSteeredLikelihood

def finished {s n : Nat} (base x : Raw s n) (o : Owners (oldH6 (rows s) base))
    (S : List (Pos n)) (len : Nat) (fall : Pos n) (w : List (Fin n)) : Prop :=
  (∃ pre rest,w=pre++rest ∧ ¬∃ z,Current (show 0<2 by decide) base (fun j => S.getD j fall) len
    (rawRun x pre) (.busy 11 z)) ∨
  ∀ i sh, dataOwner (oldH6 (rows s) base) i sh=o.val →
    activeSheet (longGeometry (rows s) (base i)) sh=true →
    (readLane (Sheet.index sh) (rawRun x w i).long).mobile=.empty

/-- The FENCE comparison from any production custody query, with no supplied
chart, old data order, prepared packets, or assumed physical progress. -/
theorem clearance_at_custody {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (o : Owners (oldH6 (rows s) g.base)) (play : List (Fin n) → Fin n → Fin n) (two : Twice play) :
    ∃ S len fall u v, Chart (show 0<2 by decide) g.base g.hh o S len fall ∧
      let l := u+radWidth s
      let rlen := v+radWidth s
      Clearance (2*width g) (pairedPaths l rlen (leftBond (S.getD 0 fall).1)
        (rightBond (S.getD len fall).1 rlen))
        (fun a => finished g.base x o S len fall (labels play [] a)) := by
  let ok : 0<2 := by decide
  obtain ⟨pre,mid,tail,S,len,fall,tape,_,C,_,m,G,_⟩ := generated_at_every_history P o []
  let z := rawRun (rawRun g.initial pre) mid
  let before := tail++g.past
  have qz : g.Q z := ProductionCustody.keep g _ mid (ProductionCustody.keep g _ pre g.init)
  have origin := BStarGeneratedTapeCuts.at_start ok G
  have atX : rawRun z before=x := by
    dsimp only [z,before]
    rw [show rawRun (rawRun (rawRun g.initial pre) mid) (tail++g.past)=
      rawRun g.initial (pre++(mid++(tail++g.past))) from
      (BStarResetSchedule.run_append (rawNext s) _ _ _).symm.trans
      (BStarResetSchedule.run_append (rawNext s) _ _ _).symm]
    have tapes : pre++(mid++(tail++g.past))=(g.u++g.v)++g.past := by simp only [tape,List.append_assoc]
    rw [tapes,g.here]
  have replay (a : List (Fin n)) : rawRun z (before++a)=rawRun x a :=
    (BStarResetSchedule.run_append (rawNext s) _ _ _).trans (congrArg (fun y => rawRun y a) atX)
  obtain ⟨u,v,L,R,join,capL,capR⟩ := two_strips ok C (radWidth s) (width g)
    (radius_pos P) g.flags g.notShort (terminal_le_width g) g.charts
  have cost := drain_or_exit ok C g.Q g.fiber (fun y q e => g.closed y e q) (separation P)
    qz origin before L R capL capR play two
  refine ⟨S,len,fall,u,v,C,?_⟩
  apply cost.mono
  intro a cleared
  rcases cleared with ⟨u',v',eq,off⟩|empty
  · refine .inl ⟨u',v',eq,?_⟩
    change ¬∃ z',Current ok g.base (fun j=>S.getD j fall) len (rawRun x u') (.busy 11 z')
    rw [←replay u']
    exact off
  · right
    intro i sh own active
    have mem := FenceCoverage.cover ok C L R join (fun j => (g.flags j).1) i sh active own
    have E := empty i sh own mem
    change (readLane (Sheet.index sh) (rawRun z (before++labels play [] a) i).long).mobile=.empty at E
    rw [replay] at E
    exact E

theorem drain_at_custody {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (o : Owners (oldH6 (rows s) g.base)) (play : List (Fin n) → Fin n → Fin n) (two : Twice play) :
    ∃ S len fall,Chart (show 0<2 by decide) g.base g.hh o S len fall ∧
      IIDExpectedHittingTimeAtMost FenceComparison.mark
        (fun a => finished g.base x o S len fall (labels play [] a)) [] (128*n*(2*width g)) := by
  obtain ⟨S,len,fall,u,v,C,clear⟩ := clearance_at_custody P o play two
  exact ⟨S,len,fall,C,clear.expected (Nat.mul_pos (by decide) (width_bounds g).1) []⟩

/-- Actual five-owner steered candidate law from an arbitrary stopped prefix.
The controller retains its existing history at FENCE entry. -/
theorem steered_drain {s n : Nat} {x : Raw s n} {g : CustodyWitness x} (P : Production g)
    (target o : Owners (oldH6 (rows s) g.base)) (phase : Fin 5 → Word n → Prop) (a : Word n) :
    let R := ProductionClients.redirect g target (CandidateResidence.live (g:=g) target phase)
    let e := emit (chooseBy R) [] a
    let play := fun b => chooseBy R (emit (chooseBy R) [] (a++b))
    ∃ S len fall, Chart (show 0<2 by decide) g.base g.hh o S len fall ∧
      IIDExpectedHittingTimeAtMost FenceComparison.mark
        (fun w => finished g.base (rawRun x e) o S len fall (labels play [] w)) [] (128*n*(2*width g)) := by
  let R := ProductionClients.redirect g target (CandidateResidence.live (g:=g) target phase)
  let emitted := emit (chooseBy R) [] a
  let play (b : Word n) := chooseBy R (emit (chooseBy R) [] (a++b))
  have two : Twice play := by
    intro b e mid
    obtain ⟨u,f,v,eq,out⟩ := CandidateResidence.candidates_supply_bonds P target phase (a++b) e mid
    exact ⟨u,f,v,eq,by simpa only [play,List.append_assoc] using out⟩
  exact drain_at_custody (production_extend P emitted) o play two

#print axioms steered_drain
#print axioms drain_or_exit
end
end L4.Height.ProductionFence
