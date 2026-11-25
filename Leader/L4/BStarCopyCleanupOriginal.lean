import Leader.L4.BStarCopyCleanupCuts
import Leader.L4.BStarCopyRightMiddle

namespace L4.BStarCopyCleanupOriginal
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongCommandData BStarLongPrep BStarLongPackets
open BStarH6WordChart BStarLongFixedRouting BStarResetChartTouch BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarAcquireAnchors BStarClearanceDataChart
open BStarResetMarkAdapter BStarGeneratedOwner BStarGeneratedBandScan BStarOwnerLaunchOrigin
open BStarCopyCleanupFrame BStarCopyCleanupCoverage BStarCopyEntryGates BStarCopyGateAuthority

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

open BStarCopyAttemptBand BStarGeneratedTapeCuts BStarCopyDrainedHistory BStarCopyCleanupWindow
open BStarSeparatingRail BStarResetChartService BStarSeparatorControl BStarResetControllerEntry BStarOwnerControlHistory

open BStarCopyCleanupCuts

theorem prefix_pc_le {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (valid : ∀ a b,w=a++b →
      (∀ i, Layout B base i=Layout B (play x a) i) ∧ Band (play x a) (S.getD 0 fall).1)
    (a b : List (Fin n)) (E : w=a++b) :
    pc (play x a) (S.getD 0 fall).1≤pc (play x w) (S.getD 0 fall).1 := by
  obtain ⟨_,_,suffix⟩ := BStarGeneratedTapeCuts.split hp a b (E ▸ G)
  rw [E,BStarResetSchedule.run_append]
  apply band_word hp chart sep suffix
  intro u v W
  have I := valid (a++u) v (by rw [E,W,List.append_assoc])
  rwa [BStarResetSchedule.run_append] at I

/-- All owner gates are closed at any actual recovered PC7 or PC8
cut reached from clean ISSUE6, without pre-assigned lane visits. -/
theorem stopped_original {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (valid : ∀ a b,w=a++b →
      (∀ i, Layout B base i=Layout B (play x a) i) ∧ Band (play x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1≤6)
    (done : 6<pc (play x w) (S.getD 0 fall).1)
    (cap : pc (play x w) (S.getD 0 fall).1<9) :
    ClosedOwner hp base (play x w) o.val := by
  obtain ⟨pre,ack,tail,W,H,event,new⟩ := accepted_cut hp chart sep G valid 6 init done
  obtain ⟨lead,back,turn,pay,A,F,Fpay,healthy,op⟩ :=
    accepted_cleanup_terminal hp chart sep 6 (by decide) H event new
  obtain ⟨u,tour,launch,T,_,_,_,out⟩ := F
  let before := u++[launch]
  let later := turn::(back++ack::tail)
  have all : w=before++(tour++later) := by rw [W,A,T]; simp [before,later,List.append_assoc]
  have E1 : play x before=step (play x u) launch := by
    rw [BStarResetSchedule.run_append]; rfl
  have E2 : play (play x before) tour=play x lead := by
    rw [←BStarResetSchedule.run_append step x before tour,T]; simp [before,List.append_assoc]
  have result := stopped hp chart sep tour later (E1.symm ▸ out) pay (E2.symm ▸ Fpay) healthy op
  have whole : play (play x before) (tour++later)=play x w := by rw [←BStarResetSchedule.run_append step x before (tour++later),←all]
  rw [whole] at result
  apply result (fun i => (valid w [] (List.append_nil _).symm).1 i)
  intro a e b Z q win own
  have WW : w=(before++a)++e::b := by rw [all,Z,←List.append_assoc]
  obtain ⟨mid,GH,C⟩ := history_prefix hp (before++a) (e::b) (WW ▸ G)
  have small := Nat.lt_of_le_of_lt (prefix_pc_le hp chart sep G valid (before++a) (e::b) WW) cap
  have w' : q∈(arbitration (round (oldPair B (play x (before++a)) e)
    (((play x (before++a)) e).long,((play x (before++a)) (rightNeighbor e)).long)).prep).1 := by
    simpa only [BStarResetSchedule.run_append] using win
  exact no_enable_before_9 hp chart sep GH C (valid _ _ WW).1 small e q w' own

open BStarCopyPreIssueEmpty

/-- The actual accepted CLEAR7 cut has no active owned mobile or
retained bytes, from the same recovered ISSUE6 prefix. -/
theorem cleared_original {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {m : Mode} {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w m)
    (valid : ∀ a b,w=a++b →
      (∀ i, Layout B base i=Layout B (play x a) i) ∧ Band (play x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1≤6)
    (done : pc (play x w) (S.getD 0 fall).1=8) :
    DrainedOwner hp base (play x w) o.val := by
  obtain ⟨pre,ack,tail,W,H,event,new⟩ :=
    accepted_cut hp chart sep G valid 7 (by omega) (by omega)
  obtain ⟨lead,back,turn,pay,A,F,Fpay,healthy,op⟩ :=
    accepted_cleanup_terminal hp chart sep 7 (by decide) H event new
  obtain ⟨u,tour,launch,T,_,_,issue7,out⟩ := F
  change pc (play x u) (S.getD 0 fall).1=7 at issue7
  let before := u++[launch]
  let later := turn::(back++ack::tail)
  have all : w=before++(tour++later) := by rw [W,A,T]; simp [before,later,List.append_assoc]
  have E1 : play x before=step (play x u) launch := by rw [BStarResetSchedule.run_append]; rfl
  have E2 : play (play x before) tour=play x lead := by
    rw [←BStarResetSchedule.run_append step x before tour,T]; simp [before,List.append_assoc]
  have result := cleared hp chart sep tour later (E1.symm ▸ out) pay (E2.symm ▸ Fpay) healthy op
  have whole : play (play x before) (tour++later)=play x w := by
    rw [←BStarResetSchedule.run_append step x before (tour++later),←all]
  rw [whole] at result
  apply result
  · intro a b Z
    have WW : w=(before++a)++b := by rw [all,Z,←List.append_assoc]
    simpa only [BStarResetSchedule.run_append] using (valid _ _ WW).1
  · intro a e b Z
    have WW : w=(before++a)++e::b := by rw [all,Z,←List.append_assoc]
    obtain ⟨mid,GH,C⟩ := history_prefix hp (before++a) (e::b) (WW ▸ G)
    have valid' (i j : List (Fin n)) (P : before++a=i++j) :
        (∀ k,Layout B base k=Layout B (play x i) k) ∧ Band (play x i) (S.getD 0 fall).1 :=
      valid i (j++e::b) (by rw [WW,P,List.append_assoc])
    have U : before++a=u++launch::a := by simp [before,List.append_assoc]
    have mn := prefix_pc_le hp chart sep GH valid' u (launch::a) U
    have mx := prefix_pc_le hp chart sep G valid (before++a) (e::b) WW
    have stopped := stopped_original hp chart sep GH valid' init (by omega) (by omega)
    simpa only [BStarResetSchedule.run_append] using stopped
  · intro a e b Z
    have WW : w=(before++a)++e::b := by rw [all,Z,←List.append_assoc]
    obtain ⟨mid,GH,C⟩ := history_prefix hp (before++a) (e::b) (WW ▸ G)
    have mx := prefix_pc_le hp chart sep G valid (before++a) (e::b) WW
    have Q := no_inject_before_10 hp chart sep GH C (valid _ _ WW).1 (by omega) e
    simpa only [BStarResetSchedule.run_append] using Q

/-- Complete same-word STOP6/CLEAR7 initialization at an actual idle
PC10 cut, including arbitrary idle-PC10 waits before ISSUE10. No
mobile or retained bytes on the active owner sheets are assumed. -/
theorem drained_original_issue10 {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (G : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (valid : ∀ a b,w=a++b →
      (∀ i, Layout B base i=Layout B (play x a) i) ∧ Band (play x a) (S.getD 0 fall).1)
    (init : pc x (S.getD 0 fall).1≤6)
    (done : pc (play x w) (S.getD 0 fall).1=10) :
    DrainedOwner hp base (play x w) o.val := by
  obtain ⟨pre,ack,tail,W,_,_,next⟩ := accepted_cut hp chart sep G valid 7 (by omega) (by omega)
  let lead := pre++[ack]
  have wSplit : w=lead++tail := by rw [W]; simp [lead,List.append_assoc]
  have h8 : pc (play x lead) (S.getD 0 fall).1=8 := by
    rw [show play x lead=step (play x pre) ack from by rw [BStarResetSchedule.run_append]; rfl]
    exact next
  obtain ⟨_,H,_⟩ := BStarGeneratedTapeCuts.split hp lead tail (wSplit ▸ G)
  have leadOK (a b : List (Fin n)) (E : lead=a++b) :
      (∀ i,Layout B base i=Layout B (play x a) i) ∧ Band (play x a) (S.getD 0 fall).1 :=
    valid a (b++tail) (by simp only [wSplit,E,List.append_assoc])
  have drained := cleared_original hp chart sep H leadOK init h8
  rw [wSplit,BStarResetSchedule.run_append]
  apply drained_word hp tail o.val sep drained
  · intro a b E
    have WW : w=(lead++a)++b := by simp only [wSplit,E,List.append_assoc]
    simpa only [BStarResetSchedule.run_append] using (valid (lead++a) b WW).1
  · intro a e b E
    rw [←BStarResetSchedule.run_append]
    have WW : w=(lead++a)++e::b := by simp only [wSplit,E,List.append_assoc]
    obtain ⟨mode,HH,suffix⟩ := BStarGeneratedTapeCuts.split hp (lead++a) (e::b) (WW ▸ G)
    have C := BStarGeneratedTapeCuts.at_end hp HH
    let root := (S.getD 0 fall).1
    have mx := prefix_pc_le hp chart sep G valid (lead++a) (e::b) WW
    change pc (play x (lead++a)) root≤pc (play x w) root at mx
    change pc (play x w) root=10 at done
    by_cases small : pc (play x (lead++a)) root<10
    · exact no_inject_before_10 hp chart sep HH C (valid _ _ WW).1 small e
    · have equal : pc (play x (lead++a)) root=10 := by omega
      cases mode with
      | idle =>
        intro a win own
        have Q := BStarCopyOwnedFrozen.safe_idle hp chart (valid _ _ WW).1 e
          (site e a.claim.lane.side) a.claim.lane.occurrence own C.2
        have K : a.claim.lane=⟨a.claim.lane.side,a.claim.lane.occurrence⟩ := by cases a.claim.lane; rfl
        rcases Q a.claim.lane.side rfl a win K with H|H|H <;> rw [H] <;> decide
      | busy j z =>
        have j10 : j=10 := C.1.2.2.2.symm.trans equal
        subst j
        apply False.elim (BStarCopyRightMiddle.busy10_never_idle hp chart sep suffix ?_ z rfl)
        intro u v U
        have all : w=((lead++a)++u)++v := by simp only [WW,U,List.append_assoc]
        have look := prefix_pc_le hp chart sep G valid ((lead++a)++u) v all
        have lower : pc (play x (lead++a)) root≤pc (play (play x (lead++a)) u) root := by
          obtain ⟨_,piece,_⟩ := BStarGeneratedTapeCuts.split hp u v (U ▸ suffix)
          apply band_word hp chart sep piece
          intro c d Q
          have replay : w=((lead++a)++c)++(d++v) := by rw [all,Q]; simp [List.append_assoc]
          simpa only [BStarResetSchedule.run_append] using valid ((lead++a)++c) (d++v) replay
        rw [BStarResetSchedule.run_append step x (lead++a) u] at look
        change pc (play (play x (lead++a)) u) root≤pc (play x w) root at look
        change 8≤pc (play (play x (lead++a)) u) root ∧ pc (play (play x (lead++a)) u) root≤10
        exact ⟨by omega,by omega⟩

end L4.BStarCopyCleanupOriginal
