import Leader.L4.WindowA0GapOneTrace

namespace L4.WindowA0GapOneJoin
open FixedResidual RootedAssembly WindowFiveStages WindowA0GapOneWord
open WindowA0GapOneTrace

def tripRank {Q : Nat} : Trip Q → Nat
  | .init => 0
  | .count k => k.val+1

/-- On a continuing acceptance the door table gives the *exact*
successor leg, not an existential arbitrary COUNT value. -/
theorem relaunch_exact {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (i : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (q : Trip (2*c))
    (hc : 0<2*c)
    (ha : WindowA0ClosedEntry.Admitted z0 S (rightNeighbor i) H z)
    (hNo : ¬ WindowA0Ledger.done z.tag) (D : DoorResult i q z.tag) :
    z.gap=1 ∧ ∃ (k : Fin (2*c)), k.val=tripRank q ∧
      WindowA0ApproachOwned.Physical (rightNeighbor i) (.count k) z 0 := by
  obtain ⟨hg,k,K⟩ := relaunch_physical hn S i H z q hc ha hNo D
  refine ⟨hg,k,?_,K⟩
  have hS := K.1
  change (z.tag.ledger.config (rightNeighbor i)).source=.await k at hS
  cases q with
  | init =>
    have B : (z.tag.ledger.config (rightNeighbor i)).source=.await ⟨0,hc⟩ := by
      simpa [waitingFor,inward,door_init_accept hc] using D.source
    have he : k=(⟨0,hc⟩ : Fin (2*c)) := Source.await.inj (hS.symm.trans B)
    exact congrArg Fin.val he
  | count j =>
    by_cases hh : j.val+1<2*c
    · have B : (z.tag.ledger.config (rightNeighbor i)).source=.await ⟨j.val+1,hh⟩ := by
        simpa [waitingFor,inward,door_count_accept j hh] using D.source
      have he : k=(⟨j.val+1,hh⟩ : Fin (2*c)) := Source.await.inj (hS.symm.trans B)
      exact congrArg Fin.val he
    · have B : (z.tag.ledger.config (rightNeighbor i)).source=.off := by
        simpa [waitingFor,inward,door_terminal_accept j hh] using D.source
      cases hS.symm.trans B

def physicalAfter {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) (w : Word n) : WindowA0ClosedEntry.State p c n :=
  GGTiming.runMarks (WindowA0ClosedEntry.next S) z w

def continues {p c n : Nat} (J : Fin n) (q : Trip (2*c))
    (y : WindowA0ClosedEntry.State p c n) : Prop :=
  y.gap=1 ∧ ∃ k : Fin (2*c), k.val=tripRank q ∧
    WindowA0ApproachOwned.Physical J (.count k) y 0

/-- The terminal prefix of the two-hit physical experiment either
routed a scope exit, spoiled the attempt, or already owns the next
numbered COUNT launch on that same raw mark. -/
theorem exact_handoff {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (z : WindowA0ClosedEntry.State p c n)
    (i : Fin n) (H : Nat) (q : Trip (2*c)) (hc : 0<2*c)
    (ha : WindowA0ClosedEntry.Admitted z0 S (rightNeighbor i) H z)
    (F : FrameAt z0 S i q 0 z.tag) (w : Word n)
    (hw : FirstExit (fun v => stopped (observe S i z.tag v)) w)
    (ok : ¬failed (observe S i z.tag w)) :
    WindowA0Ledger.done (physicalAfter S z w).tag ∨
      continues (rightNeighbor i) q (physicalAfter S z w) := by
  have he : (observe S i z.tag w).1=(physicalAfter S z w).tag := observe_actual S i z w
  cases hp : (observe S i z.tag w).2 with
  | waiting k => have h := hw.2; simp [stopped,WindowA0ReleaseCredit.done,hp] at h
  | failed => exact (ok hp).elim
  | success =>
    rcases success_word hn S i q z.tag F w hw hp with hd|hs
    · rw [he] at hd
      exact .inl hd
    · rw [he] at hs
      by_cases hd : WindowA0Ledger.done (physicalAfter S z w).tag
      · exact .inl hd
      · exact .inr (relaunch_exact hn S i H (physicalAfter S z w) q hc
          (WindowA0ClosedEntry.close_word hn S (rightNeighbor i) H z w ha) hd hs)

/-- The stage itself fails upon the first spoiler. A successful
nonterminal door service is a handoff, not a failed or globally
terminal trial. -/
def trialDecision {p c n : Nat} (S : WindowA0Ledger.Scope n)
    (z : WindowA0ClosedEntry.State p c n) (i : Fin n) (w : Word n) : Prop :=
  WindowA0Ledger.done (physicalAfter S z w).tag ∨ failed (observe S i z.tag w)

def handoff {p c n : Nat} (S : WindowA0Ledger.Scope n) (z : WindowA0ClosedEntry.State p c n)
    (i : Fin n) (q : Trip (2*c)) (w : Word n) : Prop :=
  WindowA0Ledger.done (physicalAfter S z w).tag ∨
    continues (rightNeighbor i) q (physicalAfter S z w)

def exactCreditLayer {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (z : WindowA0ClosedEntry.State p c n)
    (i : Fin n) (H : Nat) (q : Trip (2*c)) (hc : 0<2*c)
    (ha : WindowA0ClosedEntry.Admitted z0 S (rightNeighbor i) H z)
    (F : FrameAt z0 S i q 0 z.tag) :
    WindowA0AttemptCredit.Layer wordNext (trialDecision S z i)
      (fun w => w=[]) (handoff S z i q) 216 :=
  creditLayer hn S i z.tag _ _ (by
    intro w hw r
    rcases clean_word hn S i q z.tag F w hw with ⟨h,_⟩ | h | ⟨_,_,hp,E⟩
    · simp [stopped,WindowA0ReleaseCredit.done,h]
    · simp [stopped,WindowA0ReleaseCredit.done,h]
    · rcases r with r|r
      · have he := observe_actual S i z w
        change (observe S i z.tag w).1=(physicalAfter S z w).tag at he
        rw [←he] at r
        simp [WindowA0Ledger.done,E.live.2.1] at r
      · simp [failed,hp] at r)
    (fun w h hp => exact_handoff hn S z i H q hc ha F w h (by simp [failed,hp]))

def exactTimingLayer {p c n : Nat} {z0 : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (z : WindowA0ClosedEntry.State p c n)
    (i : Fin n) (H : Nat) (q : Trip (2*c)) (hc : 0<2*c)
    (ha : WindowA0ClosedEntry.Admitted z0 S (rightNeighbor i) H z)
    (F : FrameAt z0 S i q 0 z.tag) :
    WindowA0Trial.TimedLayer wordNext (trialDecision S z i)
      (fun w => w=[]) (handoff S z i q) (n*2) :=
  timingLayer S i z.tag _ _
    (fun _ _ h => .inr h)
    (fun w h hp => exact_handoff hn S z i H q hc ha F w h (by simp [failed,hp]))

#print axioms exactCreditLayer
#print axioms exactTimingLayer
#print axioms relaunch_exact
#print axioms exact_handoff
end L4.WindowA0GapOneJoin
