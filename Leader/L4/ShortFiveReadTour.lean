import Leader.L4.ShortFiveReadWin
import Leader.L4.ShortReadCaptureTrace
import Leader.L4.ShortReadReturnPC
import Leader.L4.ShortPhaseRank

namespace L4.ShortFiveReadTour
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1 ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetRow ShortResetForwardH2 MISByteCodec
open ShortSimultaneousOrder ShortFiveWinningWord ShortFiveWordEntry ShortFiveLaneHeaders ShortFiveReadWin
open ShortReadFlight ShortReadForward ShortReadReturnHop ShortReadResult
set_option maxRecDepth 12000

variable {s n : Nat} {h : Fin n → Bool}

private def bitAt (x j : Nat) : Bool := (x >>> j)%2==1

private theorem raw_app (x : Raw s n) (u v : List (Fin n)) :
    rawRun x (u++v)=rawRun (rawRun x u) v := by
  induction u generalizing x with
  | nil => rfl
  | cons e u ih => exact ih (rawNext s x e)

private theorem trace_app (C : Chart h) (x : Raw s n) (f : Flight) (u v : List (Fin n)) :
    trace C x f (u++v)=trace C (rawRun x u) (trace C x f u) v := by
  induction u generalizing x f with
  | nil => rfl
  | cons e w ih => exact ih (rawNext s x e) (next C x e f)

def forwardPrefix (C : Chart h) (k : Nat) : List (Fin n) :=
  (List.range k).map (nextAt C.root)

private theorem prefix_watch (C : Chart h) (k : Nat) (K : k≤C.L) :
    ∀ e∈forwardPrefix C k, e∈ShortResetWatch.watch C := by
  intro e V
  obtain ⟨i,I,rfl⟩ := List.mem_map.mp V
  exact (ShortResetWatch.mem_watch C _).2 (.inr ⟨i,by have := List.mem_range.mp I; omega,rfl⟩)

private theorem not_departed (C : Chart h) (k : Nat) (K : k<C.L) :
    nextAt C.root k ∉ RearTrace.predecessor C.root :: forwardPrefix C k := by
  intro E
  have L := C.length_lt
  rcases List.mem_cons.mp E with E|E
  · have H : nextAt C.root (k+1)=nextAt C.root 0 :=
      (congrArg rightNeighbor E).trans (RearTrace.right_predecessor _)
    have Q := nextAt_injective_under C.root _ _ (by omega) (by omega) H
    omega
  · obtain ⟨i,I,E⟩ := List.mem_map.mp E
    have B := List.mem_range.mp I
    have Q := nextAt_injective_under C.root _ _ (by omega) (by omega) E
    omega

private theorem canonical_front (C : Chart h) (x : Raw s n) (k p : Nat)
    (A : Forward C.route x k p) :
    oldK (header x (nextAt C.root k)) (x (nextAt C.root k)).mis1 (C.route.port k)=readFront p :=
  slot_of_bits C.route x k _ (fun z=>decode_front z p A.2.1) A.2.2.2.2.1

/-- At the k-th READ forward mark, only the target may ask, and its old
grant is still absent because this physical departure did not occur
earlier in this READ tour. Every selected header capture succeeds. -/
theorem read_mark_wins (x : Raw s n) (X : H2Ready x) (N : 21<n) (r : Fin n)
    (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root=nextAt r (offset (header x) r i.val))
    (P : ShortFiveParked.FiveParked cs x)
    (g : Nat) (gp : 0<g) (gL : g+1<(cs 2).L) (gates : ShortAdmitFlight.FixedGate (s:=s) (cs 2) g)
    (k p : Nat)
    (A : let C := cs 2
      let y := rawRun x ((tour C ++ admit C g) ++
        (RearTrace.predecessor C.root :: forwardPrefix C k))
      Forward C.route y k p) :
    let C := cs 2
    let e := nextAt C.root k
    let y := rawRun x ((tour C ++ admit C g) ++
      (RearTrace.predecessor C.root :: forwardPrefix C k))
    header y e=true →
    readWins (header y e) (header y (rightNeighbor e)) (y e).mis1 (y (rightNeighbor e)).mis1
      (C.route.port k)=true := by
  dsimp only at A ⊢
  let C := cs 2
  let w := tour C ++ admit C g
  let t := RearTrace.predecessor C.root :: forwardPrefix C k
  let y := rawRun x (w++t)
  let e := nextAt C.root k
  intro H
  have K : k<C.L := A.1
  have hd : header x e=true := ((header_run (by omega) x X.1 (w++t)).2 e).symm.trans H
  obtain ⟨j,J⟩ := chart_header_coordinates x X.1 (by omega) C k K hd
  have tag : C.route.port k=j := by
    rw [J]
    exact (chart_selected_port x X.1 (by omega) C j).2.2
  have xw : H2Ready (rawRun x w) := ready_run (by omega) x X w
  have xwh : header (rawRun x w) e=true := ((header_run (by omega) x X.1 w).2 e).trans hd
  have before := (winning_entry C x (by omega) X (fun _=>rfl) (P 2) g gp gL gates).1 k K hd
  have E : (rawRun x w e).mis1.getLsbD (91-j.val)=false := by
    change (rawRun x w e).mis1.getLsbD (91-(C.route.port k).val)=false at before
    rwa [tag] at before
  have O := absent_before_departure _ (by omega) xw e xwh j E t (not_departed C k K)
  have old := canonical_front C y k p A
  change oldK (header y e) (y e).mis1 (C.route.port k)=_ at old
  rw [H,tag] at old
  have W : ∀ f∈w++t, f∈ShortResetWatch.watch C := by
    intro f F
    rcases List.mem_append.mp F with F|F
    · rcases List.mem_append.mp F with F|F
      · exact tour_watch C f F
      · exact admit_watch C g gL f F
    · rcases List.mem_cons.mp F with E|E
      · subst f
        refine (ShortResetWatch.mem_watch C _).2 (.inl ?_)
        have Q := congrArg RearTrace.predecessor (incoming_spec C.root)
        rwa [RearTrace.predecessor_right,eq_comm] at Q
      · exact prefix_watch C k (by omega) f E
  have ef : e=nextAt C.root (offset (header x) C.root j.val) := congrArg (nextAt C.root) J
  have Z := target_read_departure_wins x X N r cs roots P (w++t) W j p
    (by rw [←ef,raw_app]; exact O) (by rw [←ef]; exact old)
  dsimp only at Z
  rw [←ef] at Z
  change readWins (header y e) (header y (rightNeighbor e)) (y e).mis1 (y (rightNeighbor e)).mis1
      (C.route.port k)=true
  rwa [tag]


private theorem before_from_live_last (C : Chart h) (x : Raw s n) (f : Flight)
    (v : List (Fin n)) (d : Fin n) (L : live (trace C x f v)) :
    beforeConsume C x f (v++[d]) := by
  have absorbing (z : Raw s n) (b : Bool) (p : Fin 64) (w : List (Fin n)) :
      trace C z (.consumed b p) w=.consumed b p := by
    induction w generalizing z with
    | nil => rfl
    | cons e w ih => exact ih (rawNext s z e)
  induction v generalizing x f with
  | nil => exact ⟨L,trivial⟩
  | cons e v ih =>
    have F : live f := by
      cases f
      · trivial
      · trivial
      · rename_i b p
        rw [absorbing] at L
        exact L
    exact ⟨F,ih _ _ L⟩

private theorem read_back_sweep (C : Chart h) (x : Raw s n) (k : Nat) (won : Bool) (out : Fin 64) :
    trace C x (.returning k won out) ((List.range k).reverse.map (nextAt C.root)) =
      .returning 0 won out := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ,List.reverse_append,List.map_append]
    simpa [trace,next,nextStage] using ih (rawNext s x (nextAt C.root k))

private theorem live_prefix (C : Chart h) (x : Raw s n) (f : Flight)
    (u v : List (Fin n)) (B : beforeConsume C x f (u++v)) :
    beforeConsume C x f u := by
  induction u generalizing x f with
  | nil => trivial
  | cons e u ih => exact ⟨B.1,ih _ _ B.2⟩

/-- The literal third tour from the original five-Parked cut returns a
positive D3 and leaves the checked consumer's actual capture ledger. -/
theorem successful_read_inputs (x : Raw s n) (X : H2Ready x) (N : 21<n) (r : Fin n)
    (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root=nextAt r (offset (header x) r i.val))
    (P : ShortFiveParked.FiveParked cs x)
    (g : Nat) (gp : 0<g) (gL : g+1<(cs 2).L) (gates : ShortAdmitFlight.FixedGate (s:=s) (cs 2) g) :
    let C := cs 2
    let z := rawRun x (tour C ++ admit C g)
    let d := RearTrace.predecessor C.root
    let w := helloBody C ++ [d]
    beforeConsume C (rawNext s z d) (.forward 0 64) w ∧
      ∃ out : Fin 64, trace C (rawNext s z d) (.forward 0 64) w=.consumed true out ∧
        ShortClearLaunch.ClearIssue C (rawRun z (d::w)) 4 := by
  dsimp only
  let C := cs 2
  let u := tour C ++ admit C g
  let z := rawRun x u
  let d := RearTrace.predecessor C.root
  let start := rawNext s z d
  have zready := ready_run (by omega) x X u
  have zheads := (header_run (by omega) x X.1 u).2
  have clear := (winning_entry C x (by omega) X (fun _=>rfl) (P 2) g gp gL gates).2
  have POS := C.positive
  have L0 := C.length_lt
  have phase (k : Nat) (K : k<C.L) :
      ∃ p, trace C start (.forward 0 64) (forwardPrefix C k)=.forward k p ∧
        Forward C.route (rawRun start (forwardPrefix C k)) k p ∧ bitAt p 6=true := by
    induction k with
    | zero =>
      refine ⟨64,rfl,forward_from_actual_issue3 C z zheads clear,by decide⟩
    | succ k ih =>
      obtain ⟨p,T,F,S⟩ := ih (by omega)
      let y := rawRun start (forwardPrefix C k)
      let e := nextAt C.root k
      let j := C.route.port k
      let q := hopPacket y e j (C.route.port (k+1))
      have E : forwardPrefix C (k+1) = forwardPrefix C k ++ [e] := by
        simp [forwardPrefix,List.range_succ,e]
      have state : y=rawRun x (u++(d::forwardPrefix C k)) :=
        (raw_app x u (d::forwardPrefix C k)).symm
      have heads := (header_run (by omega) x X.1 (u++(d::forwardPrefix C k))).2
      rw [←state] at heads
      have f := canonical_front C y k p F
      have win (H : header y e=true) :
          readWins (header y e) (header y (rightNeighbor e)) (y e).mis1 (y (rightNeighbor e)).mis1 j=true := by
        rw [state] at H ⊢
        exact read_mark_wins x X N r cs roots P g gp gL gates k p (by dsimp only; rw [←state]; exact F) H
      have bounds : (oldK (header y e) (y e).mis1 j).payload<128 := by rw [f]; exact F.2.1
      have qOK := read_forwardPacket_sticky (header y e) (header y (rightNeighbor e)) (y e).mis1 (y (rightNeighbor e)).mis1
        j (C.route.port (k+1)) (congrArg Token.opcode f) (congrArg Token.fault f) bounds
      change bitAt q.payload 6 = _ at qOK
      rw [f] at qOK
      change bitAt q.payload 6 = (bitAt p 6 && _) at qOK
      rw [S] at qOK
      have Sq : bitAt q.payload 6=true := by
        rw [qOK]
        cases H : header y e
        · rfl
        · have R := win H; rw [H] at R; rw [R]; rfl
      refine ⟨q.payload,?_,?_,Sq⟩
      · rw [E,trace_app,T]
        change next C y e (.forward k p)=_
        simp [next,e,K,q,j]
      · rw [E,raw_app]
        change Forward C.route (rawNext s y e) (k+1) q.payload
        have v := read_flight_active_step C y e (by omega) heads (.forward k p) trivial F
        simpa [next,e,K,q,j,ShortReadFlight.Active] using v
  let k := C.L-1
  obtain ⟨p,T,F,S⟩ := phase k (by dsimp [k]; omega)
  let y := rawRun start (forwardPrefix C k)
  let e := nextAt C.root k
  let j := C.route.port k
  have state : y=rawRun x (u++(d::forwardPrefix C k)) :=
    (raw_app x u (d::forwardPrefix C k)).symm
  have f := canonical_front C y k p F
  have headY := (header_run (by omega) x X.1 (u++(d::forwardPrefix C k))).2
  rw [←state] at headY
  have final : header y e=false :=
    (headY e).trans (ShortReadCaptureGeometry.capture_chart_fields x X.1 C (by omega)).2.2.2.2.2.2.2.1
  let q := replyPacket y e j
  have ok : (q.outcome==0)=true := by
    dsimp only [q,replyPacket]
    rw [read_turnPacket _ _ _ _ _ (congrArg Token.opcode f) (congrArg Token.fault f)]
    rw [f,final]
    simp only [Bool.false_eq_true,if_false]
    change ((if bitAt p 6 then ({tag:=3,opcode:=3,payload:=p%64} : Token)
      else {tag:=3,opcode:=3,outcome:=1}).outcome==0)=true
    rw [S]
    rfl
  have E : forwardPrefix C C.L = forwardPrefix C k ++ [e] := by
    have B : C.L=k+1 := by dsimp [k]; omega
    conv => lhs; arg 2; rw [B]
    simp [forwardPrefix,List.range_succ,e]
  have full : trace C start (.forward 0 64) (forwardPrefix C C.L)=.returning k true (datum q) := by
    rw [E,trace_app,T]
    change next C y e (.forward k p)=_
    have B : ¬k+1<C.L := by dsimp [k]; omega
    simp [next,e,B,q,j,ok]
  have body : trace C start (.forward 0 64) (helloBody C)=.returning 0 true (datum q) := by
    change trace C start (.forward 0 64)
      (forwardPrefix C C.L ++ (List.range k).reverse.map (nextAt C.root))=_
    rw [trace_app,full,read_back_sweep]
  have Bc := before_from_live_last C start (.forward 0 64) (helloBody C) d (by rw [body]; trivial)
  have D : trace C start (.forward 0 64) (helloBody C++[d])=.consumed true (datum q) := by
    rw [trace_app,body]
    simp [trace,next,nextStage,d,RearTrace.right_predecessor]
  let pre := rawRun start (helloBody C)
  have RA := active_through_run C (by omega) (helloBody C) start (.forward 0 64)
    (h2_ready_closed (by omega) z d zready)
    (fun j=>(H1.raw_h1_selected_frozen (by omega) z d j zready.1).trans (zheads j))
    (forward_from_actual_issue3 C z zheads clear)
    (live_prefix C start (.forward 0 64) (helloBody C) [d] Bc)
  rw [body] at RA
  have RR : ShortReadReverseChart.Returning C pre 0 true (datum q) := RA
  have H : header pre C.root=true := by
    have Hstart := h2_ready_closed (by omega : 5≤n) z d zready
    have Q := (header_run (by omega) start Hstart.1 (helloBody C)).2 C.root
    have T := H1.raw_h1_selected_frozen (by omega : 5≤n) z d C.root zready.1
    exact Q.trans (T.trans ((zheads C.root).trans C.rootHeader))
  have E0 := RR.2.2 0 C.positive
  change (kField (lane C.a C.b 0)).read (pre C.root).mis1 =
    encode (ShortReadReverseChart.trailAt true (datum q) 0 0) at E0
  rw [C.rootPort] at E0
  simp only [ShortReadReverseChart.trailAt,Nat.lt_irrefl,if_false,if_true] at E0
  have dR : rightNeighbor d=C.root := RearTrace.right_predecessor _
  have pc := ShortReadReturnPC.consume_pc pre d (edge_sep (by omega) d) (dR.symm ▸ H)
    (dR.symm ▸ RR.2.1) true (datum q) (dR.symm ▸ E0)
  rw [dR] at pc
  change ShortControllerEntrance.pc (rawNext s pre d C.root).mis1 = 12 at pc
  have V := ShortPhaseRank.pc_fields (rawNext s pre d C.root).mis1
  rw [pc] at V
  have low : get (rawNext s pre d C.root).mis1 78 3 (by decide)<8 :=
    (MISByteCodec.lane 78 3 (by decide) |>.read (rawNext s pre d C.root).mis1).isLt
  have Z0 := active_from_clean_issue3 C (by omega) (helloBody C++[d]) z zready zheads clear Bc
  dsimp only at Z0
  rw [D] at Z0
  have Z : ShortEmptyOwnership.Clear C (rawRun z (d::(helloBody C++[d]))) := Z0.1
  have endEq : rawRun z (d::(helloBody C++[d]))=rawNext s pre d := by
    change rawRun start (helloBody C++[d])=_
    exact raw_app start (helloBody C) [d]
  refine ⟨Bc,datum q,D,?_⟩
  change ShortClearLaunch.ClearIssue C (rawRun z (d::(helloBody C++[d]))) 4
  rw [endEq] at Z ⊢
  refine ⟨by decide,Z,?_,?_⟩
  · change get (rawNext s pre d C.root).mis1 81 2 (by decide)=1
    omega
  · change get (rawNext s pre d C.root).mis1 78 3 (by decide)=4
    omega

#print axioms read_mark_wins
#print axioms successful_read_inputs
end L4.ShortFiveReadTour
