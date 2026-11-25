import Leader.L4.Height.AdmissionTour
namespace L4.BStarAdmissionObservationBound
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongWork
open BStarLongCommand BStarLongTransport BStarLongEvents BStarLongRouting
open BStarLongLiteral BStarLongCommandData BStarResetQuiet BStarResetQuietTable
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireForwardTrace BStarAcquireLiteralChain
open BStarLongFixedRouting BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarResetSchedule BStarGeneratedPCAncestry BStarLiteralPC BStarResetControllerProgress
open BStarSeparatingRail BStarSeparatorControl BStarSeparatorQuiet BStarResetQuietAdapter
open BStarGeneratedOwner BStarOwnerLaunchOrigin BStarResetChartService BStarClearanceSource
open BStarLongDoor BStarResetControllerEntry BStarClearanceOffset BStarAdmitIncidentGeometry
open BStarBitParity
open BStarLongLayout (kField)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open L4.Height.AdmissionTour

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step

private theorem run_closed (Q : X→Prop) (closed : ∀ x,Q x→∀ e,Q (step x e))
    (x : X) (qx : Q x) (w : List (Fin n)) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact qx
  | cons e w ih => exact ih (step x e) (closed x qx e)

private theorem split_busy {base x : X} {addr : Nat→Pos n} {len op : Nat}
    {z d : Cursor} (pre post : List (Fin n))
    (P : BusyOnly hp base addr len op x z (pre++post) d) :
    ∃ mid, BusyOnly hp base addr len op x z pre mid ∧
      BusyOnly hp base addr len op (run x pre) mid post d := by
  induction pre generalizing x z with
  | nil => exact ⟨z,.nil (busy_start hp P),P⟩
  | cons e pre ih =>
    cases P with
    | cons I E tail =>
      obtain ⟨mid,L,R⟩ := ih tail
      exact ⟨mid,.cons I E L,R⟩

private theorem front_points_to {base x : X} {addr : Nat→Pos n} {len op j : Nat}
    {d : Cursor} (cur : Current hp base addr len x (.busy op d))
    (J : j≤len) (p : Payload) (F : project addr x j=.forward p) :
    d=.out j := by
  cases d with
  | out k =>
    have eq := (BStarOwnerControlHistory.pointed_unique_forward _ _ _ cur.2.1 cur.2.2 j J).mp ⟨p,F⟩
    exact congrArg Cursor.out eq.symm
  | back k =>
    exact (BStarOwnerControlHistory.pointed_backward_no_forward _ _ _ cur.2.1 j J ⟨p,F⟩).elim

private theorem earliest {α : Type} (P : α→Prop) (w : List α) :
    (∀ e∈w,¬P e) ∨ ∃ pre e post,w=pre++e::post ∧ (∀ f∈pre,¬P f) ∧ P e := by
  classical
  induction w with
  | nil => exact .inl (by simp)
  | cons e w ih =>
    by_cases hit : P e
    · exact .inr ⟨[],e,w,rfl,by simp,hit⟩
    · rcases ih with misses|⟨pre,f,post,eq,skip,found⟩
      · exact .inl (by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hit misses)
      · exact .inr ⟨e::pre,f,post,congrArg (List.cons e) eq,
          by simpa only [List.mem_cons, forall_eq_or_imp] using And.intro hit skip,found⟩

private theorem unchanged_site (x : X) (i : Fin n) (w : List (Fin n))
    (skip : ∀ e∈w,∀ s, BStarAcquireDoorHistory.siteOf e s≠i) :
    run x w i=x i := by
  induction w generalizing x with
  | nil => rfl
  | cons e w ih =>
    have left : i≠e := Ne.symm (skip e List.mem_cons_self .left)
    have right : i≠rightNeighbor e := Ne.symm (skip e List.mem_cons_self .right)
    have frame : step x e i=x i := by simp only [AllSizeS1Geometry.step,if_neg left,if_neg right]
    exact (ih (step x e) (fun a M=>skip a (List.mem_cons_of_mem _ M))).trans frame

/-- A generated tape which returns after arriving at a fresh gate
contains the first incident mark and the next opposite incident mark.
The suffix starts with a completed race on that same chart and tape. -/
theorem gate_observations_for_return_bound {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (Q : X→Prop) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e))
    (ready : ∀ x,Q x→correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) (qx : Q x)
    (i : Fin n) (k : Nat) (K : k≤len) (loc : S.getD k fall=(i,1))
    (ord : BStarH6Ordinal.oldOrdinal B base hh i=2)
    {w : List (Fin n)}
    (P : BusyOnly hp base (fun j=>S.getD j fall) len admit x (.out k) w (.back 0))
    (initial : project (fun j=>S.getD j fall) x k=.forward (atGate 1)) :
    ∃ (pre middle after : List (Fin n)) (first other : Fin n) (s t : Side),
      w=pre++first::(middle++other::after) ∧
      (∀ e∈pre,∀ u,BStarAcquireDoorHistory.siteOf e u≠i) ∧
      BStarAcquireDoorHistory.siteOf first s=i ∧
      t≠s ∧ BStarAcquireDoorHistory.siteOf other t=i ∧
      (∀ e∈middle,∀ u,BStarAcquireDoorHistory.siteOf e u=i → u=s) ∧
      BusyOnly hp base (fun j=>S.getD j fall) len admit x (.out k) pre (.out k) ∧
      Current hp base (fun j=>S.getD j fall) len (run x pre) (.busy admit (.out k)) ∧
      BStarLongCommand.bind (longGeometry B (run x pre i)) 1 (atSite (run x pre i).long 1)=.forward (atGate 1) ∧
      let z := step (run (step (run x pre) first) middle) other
      BusyOnly hp base (fun j=>S.getD j fall) len admit z (.out k) after (.back 0) ∧
        project (fun j=>S.getD j fall) z k=.forward (settledGate (s==.left)) := by
  let addr := fun j=>S.getD j fall
  have loc' : addr k=(i,1) := loc
  have untouched (p : List (Fin n)) (avoid : ∀ e∈p,∀ s,BStarAcquireDoorHistory.siteOf e s≠i) :
      project addr (run x p) k=.forward (atGate 1) := by
    change atSite (run x p (addr k).1).long (addr k).2=_
    rw [loc',unchanged_site hp x i p avoid]
    change atSite (x (addr k).1).long (addr k).2=_ at initial
    rwa [loc'] at initial
  have gateAt (y : X) (qy : Q y) : gate admit 1 (longGeometry B (y i))=true :=
    (selected_gate_iff hp hh (fun j=>(congrArg Prod.fst (fiber y qy j)).symm)
      (ready y qy) i 1 false).mpr ⟨rfl,ord⟩
  rcases earliest (fun e=>∃ s,BStarAcquireDoorHistory.siteOf e s=i) w with none|⟨pre,e,rest,W,skip,s,atS⟩
  · have avoid : ∀ e∈w,∀ s,BStarAcquireDoorHistory.siteOf e s≠i :=
      fun e H s D=>none e H ⟨s,D⟩
    have impossible := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp P) K _ (untouched w avoid)
    cases impossible
  have noHit : ∀ e∈pre,∀ s,BStarAcquireDoorHistory.siteOf e s≠i :=
    fun e H s D=>skip e H ⟨s,D⟩
  let y := run x pre
  have qy : Q y := run_closed hp Q closed x qx pre
  have atY := untouched pre noHit
  obtain ⟨mid,lead,restBusy⟩ := split_busy hp pre (e::rest) (W ▸ P)
  have preBusy := lead
  have atPoint := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp lead) K _ atY
  subst mid
  have cur : Current hp base addr len y (.busy admit (.out k)) := busy_start hp restBusy
  have bindY : BStarLongCommand.bind (longGeometry B (y i)) 1 (atSite (y i).long 1)=.forward (atGate 1) := by
    change atSite (y (addr k).1).long (addr k).2=_ at atY
    rw [loc'] at atY
    rw [atY]
    exact gate_packet_bound _ _ (gateAt y qy) (by decide)
  have qe := closed y qy e
  obtain ⟨rawFirst,_,afterFirst,boundFirst⟩ := BStarGateStutter.observed_race_step
    hp C Q fiber closed sep i e false k qy loc cur (atGate 1) bindY rfl rfl
    (ready y qy) (ready _ qe) (gateAt y qy) s atS (firstCode s) (.inl ⟨rfl,rfl⟩)
  have firstToken : project addr (step y e) k=.forward (atGate (firstCode s)) := by
    change atSite (step y e (addr k).1).long (addr k).2=_
    rw [loc']
    unfold atSite
    rw [rawFirst,decode_encode]
    rfl
  cases restBusy with
  | @cons _ _ next _ _ _ _ _ restBusy =>
    have nextAt := front_points_to hp (busy_start hp restBusy) K _ firstToken
    subst next
    have wait (p : List (Fin n))
        (avoid : ∀ e∈p,∀ t,BStarAcquireDoorHistory.siteOf e t=i → t=s) :=
      BStarGateStutter.first_wait_word hp C Q fiber closed ready sep i false k loc ord
        (atGate (firstCode s)) rfl rfl s rfl p (step y e) qe afterFirst boundFirst rawFirst avoid
    have heldToken (p : List (Fin n)) (avoid : ∀ f∈p,∀ t,BStarAcquireDoorHistory.siteOf f t=i → t=s) :
        project addr (run (step y e) p) k=.forward (atGate (firstCode s)) := by
      change atSite (run (step y e) p (addr k).1).long (addr k).2=_
      rw [loc']
      unfold atSite
      rw [(wait p avoid).2.2,decode_encode]
    rcases earliest (fun f=>∃ t,t≠s ∧ BStarAcquireDoorHistory.siteOf f t=i) rest with
      none|⟨middle,f,after,V,quiet,t,opp,atT⟩
    · have avoid (b : Fin n) (H : b∈rest) (t : Side) (atT : BStarAcquireDoorHistory.siteOf b t=i) :
          t=s := Classical.byContradiction (fun N=>none b H ⟨t,N,atT⟩)
      have impossible := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp restBusy) K _ (heldToken rest avoid)
      cases impossible
    have avoid (b : Fin n) (H : b∈middle) (t : Side) (atT : BStarAcquireDoorHistory.siteOf b t=i) :
        t=s := Classical.byContradiction (fun N=>quiet b H ⟨t,N,atT⟩)
    have accepted := two_race_marks hp C Q fiber closed ready sep i k loc ord qy cur atY
      s t opp e f atS atT middle avoid
    obtain ⟨mid,lead,rem⟩ := split_busy hp middle (f::after) (V ▸ restBusy)
    have ptr := front_points_to hp (BStarAcquireHistoryReturn.busy_end hp lead) K _ (heldToken middle avoid)
    subst mid
    cases rem with
    | @cons _ _ next _ _ _ _ _ afterBusy =>
      have pt := front_points_to hp (busy_start hp afterBusy) K _ accepted.2
      subst next
      exact ⟨pre,middle,after,e,f,s,t,by rw [W,V],noHit,atS,opp,atT,avoid,preBusy,cur,bindY,afterBusy,accepted.2⟩

end L4.BStarAdmissionObservationBound
