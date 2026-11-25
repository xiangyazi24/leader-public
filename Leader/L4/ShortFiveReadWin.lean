import Leader.L4.ShortFiveLaneHeaders
import Leader.L4.ShortReadFlight

namespace L4.ShortFiveReadWin
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1 ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetRow ShortResetForwardH2 MISByteCodec
open ShortSimultaneousOrder ShortFiveWinningWord ShortFiveLaneHeaders

variable {s n : Nat}

theorem absent_before_departure (x : Raw s n) (N : 5≤n) (X : H2Ready x)
    (i : Fin n) (H : header x i=true) (j : Fin 3)
    (old : (x i).mis1.getLsbD (91-j.val)=false) (w : List (Fin n)) (never : i∉w) :
    ((rawRun x w i).mis1).getLsbD (91-j.val)=false := by
  induction w generalizing x with
  | nil => exact old
  | cons e w ih =>
    have step := ShortGrantPersistence.absent_until_ask x e i j (edge_sep (by omega) e) H old
      (fun E => False.elim (never (by simp [E])))
    have H' := (raw_h1_selected_frozen N x e i X.1).trans H
    exact ih _ (h2_ready_closed N x e X) H' step (fun E => never (List.mem_cons_of_mem _ E))

private theorem grant_old_bit (u : BitVec 96) (j : Fin 3) :
    (headerGrantView u).old j=u.getLsbD (91-j.val) := by
  rfl

theorem read_wins_no_rival (x : Raw s n) (e : Fin n) (j : Fin 3) (p : Nat)
    (H : header x e=true) (F : oldK true (x e).mis1 j=readFront p)
    (empty : ∀ k : Fin 3, (x e).mis1.getLsbD (91-k.val)=false)
    (asks : ∀ k : Fin 3, k≠j → (headerGrantView (x e).mis1).ask k=false) :
    readWins (header x e) (header x (rightNeighbor e)) (x e).mis1 (x (rightNeighbor e)).mis1 j=true := by
  rw [H,readWins_header]
  let g := headerGrantView (x e).mis1
  have A : g.ask j=true := by
    change ((oldK true (x e).mis1 j).tag==2 && !(oldK true (x e).mis1 j).fault &&
      (oldK true (x e).mis1 j).opcode==3)=true
    rw [F]
    rfl
  have R : g.release j=false := by
    change ((oldK true (x e).mis1 j).tag==2 && !(oldK true (x e).mis1 j).fault &&
      (oldK true (x e).mis1 j).opcode==0)=false
    rw [F]
    rfl
  have O (k : Fin 3) : g.old k=false := (grant_old_bit _ k).trans (empty k)
  have C (k : Fin 3) : g.canonical k=false := by simp [BStarShort.GrantView.canonical,O]
  change g.win j=true
  by_cases J : j=1
  · subst j
    simp [BStarShort.GrantView.win,BStarShort.GrantView.centerWin,A,R,C]
  · have N := asks 1 (Ne.symm J)
    change g.ask 1=false at N
    simp [BStarShort.GrantView.win,BStarShort.GrantView.centerWin,A,R,C,J,N]

/-- For each original READ forward departure at a selected header, the
five-rival fence plus no earlier own departure forces the literal win bit. -/
theorem target_read_departure_wins (x : Raw s n) (X : H2Ready x) (N : 21<n)
    (r : Fin n) (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root=nextAt r (offset (header x) r i.val))
    (P : ShortFiveParked.FiveParked cs x) (w : List (Fin n))
    (watchOnly : ∀ e∈w, e∈ShortResetWatch.watch (cs 2))
    (j : Fin 3) (p : Nat)
    (own : let e := nextAt (cs 2).root (offset (header x) (cs 2).root j.val)
      ((rawRun x w e).mis1).getLsbD (91-j.val)=false)
    (F : let e := nextAt (cs 2).root (offset (header x) (cs 2).root j.val)
      oldK true (rawRun x w e).mis1 j=readFront p) :
    let e := nextAt (cs 2).root (offset (header x) (cs 2).root j.val)
    let y := rawRun x w
    readWins (header y e) (header y (rightNeighbor e)) (y e).mis1 (y (rightNeighbor e)).mis1 j=true := by
  let e := nextAt (cs 2).root (offset (header x) (cs 2).root j.val)
  let y := rawRun x w
  have H : header y e=true := ((header_run (by omega) x X.1 w).2 e).trans
    (chart_selected_port x X.1 (by omega) (cs 2) j).2.1
  have R := rival_header_asks_and_grants x X N r cs roots P w watchOnly j
  apply read_wins_no_rival y e j p H F
  · intro k
    by_cases K : k=j
    · simpa [K] using own
    · exact (R k K).2
  · intro k K
    exact (R k K).1

end L4.ShortFiveReadWin
