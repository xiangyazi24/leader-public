import Leader.L4.BStarPacePhysicalCharge
import Leader.L4.BStarPaceLedger

namespace L4.BStarPaceChartLedger
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireAnchors BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetMarkAdapter BStarResetChartTouch
open BStarSeparatingRail BStarGeneratedOwner BStarPacePhysicalCharge
open BStarPaceLedger BStarPaceCount BStarSeparatorControl BStarResetSchedule
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

/-- Nominate the physical link of the current outbound PACE cursor.
This depends on the old history, not on a future outcome. It is safe
to charge every hit of that label even if a particular hit stutters. -/
noncomputable def rawCharge (base initial : X) (addr : Nat→Pos n) (len : Nat)
    (a : List (Fin n)) (e : Fin n) : Nat :=
  if ∃ k, Current hp base addr len (run initial a) (.busy 3 (.out k)) ∧
    linkAt hp (run initial a) e addr len k then 1 else 0

/-- At a fixed old prefix at most one logical label can incur an
outbound PACE charge for the owner. -/
theorem rawCharge_unique (base initial : X) (addr : Nat→Pos n) (len : Nat)
    (a : List (Fin n)) (e f : Fin n)
    (E : rawCharge hp base initial addr len a e>0)
    (F : rawCharge hp base initial addr len a f>0) : e=f := by
  unfold rawCharge at E F
  split at E
  · rename_i known
    rcases known with ⟨k,cur,lk⟩
    split at F
    · rename_i known'
      rcases known' with ⟨j,cur',lj⟩
      have K := BStarOwnerControlHistory.pointed_unique_forward
        (project addr (run initial a)) len k cur.2.1 cur.2.2 j cur'.2.1.1
      obtain rfl := K.mp cur'.2.1.2.1
      exact link_label_unique hp (fun _=>rfl) addr len j e f lk lj
    · omega
  · omega

/-- An actual one-mark event spends at least its outbound-progress
credit on the predictable raw label classifier. -/
theorem actual_event_le_charge {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (a : List (Fin n)) (e : Fin n) (he : e≠rightNeighbor e) (z d : Cursor)
    (cur : Current hp base (fun j=>S.getD j fall) len (run initial a) (.busy 3 z))
    (E : Event hp (fun j=>S.getD j fall) len (run initial a) e (.busy 3 z) (.busy 3 d)) :
    forwardΔ z d≤rawCharge hp base initial (fun j=>S.getD j fall) len a e := by
  cases z with
  | back _ => simp [forwardΔ]
  | out k =>
    cases d with
    | back _ => simp [forwardΔ]
    | out j =>
      by_cases H : j=k+1
      · subst j
        have link := (advance_on_link hp C e he k cur E).1
        rw [rawCharge,if_pos (show ∃ k, Current hp base (fun j=>S.getD j fall) len
          (run initial a) (.busy 3 (.out k)) ∧
          linkAt hp (run initial a) e (fun j=>S.getD j fall) len k from ⟨k,cur,link⟩)]
        simp [forwardΔ]
      · simp [forwardΔ,H]

/-- The physical refinement of complete_pace_charge. The oath to
charge forward advances is not an external premise: the actual old
Current and one-mark Event prove it on each step. The interval starts
at the exact raw prefix of this genuine launch and ends idle. -/
theorem actual_complete_pace_charge {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (a w : List (Fin n))
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len (run initial a)
      (.busy 3 (.out 0)) w .idle) :
    len≤charges (rawCharge hp base initial (fun j=>S.getD j fall) len) a w := by
  let addr := fun j=>S.getD j fall
  let charge := rawCharge hp base initial addr len
  have aux (w : List (Fin n)) (a : List (Fin n)) (z : Cursor)
      (G : GeneratedOwner hp base addr len (run initial a) (.busy 3 z) w .idle) :
      len≤outwardCredit len z+charges charge a w := by
    induction w generalizing a z with
    | nil => cases G
    | cons e w ih =>
      by_cases done : z=.back 0
      · simp [done,outwardCredit]
      · cases G with
        | next cur event tail =>
          cases event with
          | transit _ z d live one =>
            have new : run initial (a++[e])=step (run initial a) e := by
              rw [BStarResetSchedule.run_append]
              rfl
            rw [←new] at tail
            have T := ih (a++[e]) d tail
            have spent := actual_event_le_charge hp C a e (sep e) z d cur
              (.transit 3 z d live one)
            have cost : outwardCredit len z + forwardΔ z d = outwardCredit len d := by
              cases one with
              | cons _ _ a _ term =>
                cases term
                exact telescope a
            change forwardΔ z d≤charge a e at spent
            rw [charges]
            omega
          | arrived_hold _ _ => exact (done rfl).elim
          | consume _ _ _ => exact (done rfl).elim
  simpa [outwardCredit,charge,addr] using aux w a (.out 0) G

#print axioms rawCharge_unique
#print axioms actual_event_le_charge
#print axioms actual_complete_pace_charge
end L4.BStarPaceChartLedger

