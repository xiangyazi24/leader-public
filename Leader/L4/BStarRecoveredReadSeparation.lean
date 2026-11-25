import Leader.L4.BStarPhysicalReserved
import Leader.L4.BStarRecoveredReveal
import Leader.L4.BStarRecoveredReadKeys
import Leader.L4.BStarGateOwnerUnique

namespace L4.BStarRecoveredReadSeparation
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart
open BStarH6Ordinal BStarAcquireLiteralChain BStarAcquireAnchors BStarAcquireVisitOrder
open BStarOwnerRecoveryPass BStarClearanceRaceMark BStarLongFixedRouting
open BStarLongToken BStarLongCommand BStarLongEvents BStarResetMarkAdapter
open BStarClearanceOffset BStarAcquireRailCoverage BStarNeedPrefixFresh
open BStarRecoveredHistory BStarNeedServicePlan BStarFirstActualPublication
open BStarAcquireForwardTrace BStarResetChartTouch BStarBitLabelSwap BStarGateOwnerUnique
open BStarGrantWriterHistory BStarPhysicalPairLaw BStarIncrementLedger BStarPhysicalIncrementLedger
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private theorem run_closed (Q : X→Prop) (closed : ∀ x,Q x→∀ e,Q (step x e))
    {x : X} (I : Q x) (w : List (Fin n)) : Q (run x w) := by
  induction w generalizing x with
  | nil => exact I
  | cons e w ih => exact ih (closed x I e)

private theorem reveal_read {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {start : Fin n→Nat} {past : List (Fin n)} {e center : Fin n} {t : Nat} {bit : Bool}
    (R : BStarRecoveredReveal.reveal hp base x hh start past e=some ((center,t),bit)) :
    ∃ gate s, BStarRecoveredReveal.Ready hp base x hh past gate ∧
      incident gate s=e ∧ ownerAt hp base hh gate=center := by
  classical
  unfold BStarRecoveredReveal.reveal at R
  dsimp only at R
  split at R
  · rename_i W
    let z := Classical.choose W
    have H : Witness (BStarRecoveredReveal.Ready hp base x hh past) e z := Classical.choose_spec W
    exact ⟨z.1,z.2,H.1,H.2,congrArg (fun q=>q.1.1) (Option.some.inj R)⟩
  · contradiction

/-- A generated post-recovery publication lies between any two admitted
same-owner reads. No global custody is needed for the publication
witness itself, and no native clock increment is asserted here. -/
theorem two_reveals_force_publication {base x : X} {hh : ∃ i,oldH6 B base i=true}
    (Q : X→Prop) (I : Q x) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 x)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (start : Fin n→Nat) (prior gap : List (Fin n)) (a b center : Fin n)
    (h₁ h₂ : Nat) (s₁ s₂ : Bool)
    (A : BStarRecoveredReveal.reveal hp base x hh start prior a=some ((center,h₁),s₁))
    (D : BStarRecoveredReveal.reveal hp base x hh start (prior++a::gap) b=some ((center,h₂),s₂)) :
    ∃ u v, a::gap=u++center::v ∧
      BeforePublication hp (run x prior) center u ∧
      ¬NoPublication hp (run x (prior++u)) center center := by
  obtain ⟨i,s,F,label,owner⟩ := reveal_read hp A
  obtain ⟨j,t,H,label',owner'⟩ := reveal_read hp D
  have ord : oldOrdinal B base hh i=4 := F.1.1
  have ord' : oldOrdinal B base hh j=4 := H.1.1
  have ownEq : commandOwner (oldH6 B base) i 1=commandOwner (oldH6 B base) j 1 := by
    rw [←owner_keeps_chart hp base hh i,←owner_keeps_chart hp base hh j,owner,owner']
  have same : i=j := ordinal_owner_inj _ hh i j 1 (ord.trans ord'.symm) ownEq
  subst j
  obtain ⟨fresh,lead,mid,rest,split,R⟩ := F
  let y := run (run x lead) mid
  have snap : run x prior=run y rest := by
    rw [split,BStarResetSchedule.run_append,BStarResetSchedule.run_append]
  have later : run x (prior++a::gap)=run y (rest++a::gap) := by
    rw [BStarResetSchedule.run_append,BStarResetSchedule.run_append,snap]
  obtain ⟨S,len,fall,C,pc,_,mode,T,_,_⟩ := recovered_suffix hp R sep Q
    (run_closed hp Q closed I lead) fiber (fun z e h=>closed z h e) (rest++a::gap)
  let addr := fun k=>S.getD k fall
  have sz := C.length
  have iy : Q y := run_closed hp Q closed (run_closed hp Q closed I lead) mid
  have offsetY : correct (oldH6 B base) hh 5 y := by
    unfold y
    rw [←BStarResetSchedule.run_append]
    exact BStarNativeOffsetTrace.closed_word hp _ hh sep x _ offset (fun h _ _ =>
      funext (fun k => (congrArg Prod.fst (fiber _ (run_closed hp Q closed I h) k)).symm))
  have ownCenter : commandOwner (oldH6 B base) center 1=
      (own (oldH6 B base) hh (i,1)).val := by
    rw [←owner]
    exact owner_keeps_chart hp base hh i
  have headCenter : oldH6 B base center=true := by
    rw [←owner]
    unfold ownerAt
    have bounds := commandOwner_range (oldH6 B base) hh i 1
    exact (Classical.choose (unique_command_header _ hh _ bounds.1 bounds.2 1)).property
  have find (q : Fin n) (ownQ : commandOwner (oldH6 B base) q 1=
      (own (oldH6 B base) hh (i,1)).val) :
      ∃ j<len, S.getD j fall=(q,1) := by
    obtain ⟨j,J,E⟩ := List.mem_iff_getElem.mp (C.cover (q,1) rfl ownQ)
    have loc : S.getD j fall=(q,1) := (List.getElem_eq_getD fall).symm.trans E
    have neq : j≠len := by
      intro h
      rw [h,C.terminal] at loc
      exact (by decide : (10:Fin 11)≠1) (congrArg Prod.snd loc)
    exact ⟨j,by omega,loc⟩
  obtain ⟨k,K,idx⟩ := find center ownCenter
  obtain ⟨g,G,atG⟩ := find i rfl
  have positive : 0<g := by
    apply Nat.pos_of_ne_zero
    intro eq
    rw [eq,C.root] at atG
    exact (by decide : (0:Fin 11)≠1) (congrArg Prod.snd atG)
  obtain ⟨plan⟩ := plan_exists hp C heads cont k g K G
  have notInherited : BStarCommitTailScan.pc y (addr 0).1≠bitOp := by
    change (BStarLongDoor.ctrlOp.read (y (addr 0).1).long).toNat≠bitOp
    rw [show (BStarLongDoor.ctrlOp.read (y (addr 0).1).long).toNat=3 from pc]
    decide
  have raw (z : X) (e : Fin n) (side : Side)
      (Fr : Fresh hp base hh z i) (touch : incident i side=e) :
      RawFirstRead addr g z e := by
    obtain ⟨_,p,F,N,O,R,U,V⟩ := Fr
    refine ⟨p,?_,N,O,R,U,V,?_⟩
    · unfold project
      change atCursor z (S.getD g fall)=_
      rw [atG]
      exact F
    · change e=incident (S.getD g fall).1 .left ∨ e=incident (S.getD g fall).1 .right
      rw [atG,←touch]
      cases side <;> simp
  obtain ⟨u,v,d,s',W,_,quiet,_,published⟩ :=
    two_reads_separated_by_same_need hp C Q fiber closed sep iy offsetY coherent
      center k K idx headCenter ownCenter i g ⟨positive,G⟩ atG ord plan
      rest gap a b (m:=mode) T notInherited
      (snap ▸ raw _ _ s fresh label) (later ▸ raw _ _ t H.1 label')
  refine ⟨u,v,W,snap.symm ▸ quiet,?_⟩
  rw [BStarResetSchedule.run_append,snap]
  intro N
  exact N .left rfl ⟨.left,BStarStageCandidateWrite.candidate d (BStarBitParity.firstBit s')⟩
    (by rw [published]; simp) rfl

open BStarPhysicalReserved

private theorem interval_split {A : Type} (w : List A) (a b : Fin w.length)
    (lt : a.val<b.val) :
    ∃ gap, w.take b.val=w.take a.val++w[a.val]::gap := by
  let w' := w.take b.val
  have h : a.val<w'.length := by
    dsimp [w']
    simp only [List.length_take]
    exact Nat.lt_min.mpr ⟨lt,a.isLt⟩
  refine ⟨w'.drop (a.val+1),?_⟩
  calc
    w.take b.val = w'.take a.val++w'.drop a.val := (List.take_append_drop _ _).symm
    _ = w.take a.val++w[a.val]::w'.drop (a.val+1) := by
      rw [List.drop_eq_getElem_cons h]
      dsimp [w']
      rw [List.getElem_take,List.take_take,Nat.min_eq_left (Nat.le_of_lt lt)]

/-- Whole stopped tapes satisfy the physical separation premise for
their retained reservations; the separative publication need not be
decoded as an increment. -/
theorem separates_stopped_tape {base x : X} {hh : ∃ i,oldH6 B base i=true}
    (Q : X→Prop) (I : Q x) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x,Q x→∀ e,Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 x)
    (coherent : ∀ (x : X), Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (start : Fin n→Nat) (history : List (Fin n)) (i : Fin n) :
    ∀ a b p q, a<b → b<history.length →
      admittedRead hp base x hh start history a=some (i,p) →
      admittedRead hp base x hh start history b=some (i,q) →
      ∃ j,a≤j ∧ j<b ∧ publishes hp x history j i := by
  intro a b coin q lt hb A D
  have ha : a<history.length := Nat.lt_trans lt hb
  obtain ⟨gap,cut⟩ := interval_split (p:=p) history ⟨a,ha⟩ ⟨b,hb⟩ lt
  simp only at cut
  have read (k : Nat) (K : k<history.length) (s : Bool)
      (R : admittedRead hp base x hh start history k=some (i,s)) :
      ∃ level, BStarRecoveredReveal.reveal hp base x hh start (history.take k) history[k]=some ((i,level),s) := by
    unfold admittedRead at R
    rw [dif_pos K] at R
    cases E : BStarRecoveredReveal.reveal hp base x hh start (history.take k) history[k] with
    | none => rw [E] at R; cases R
    | some z =>
      obtain ⟨⟨owner,lev⟩,sgn⟩ := z
      rw [E] at R
      have same : (owner,sgn)=(i,s) := Option.some.inj R
      have o : owner=i := congrArg Prod.fst same
      have h : sgn=s := congrArg Prod.snd same
      exact ⟨lev,by rw [o,h]⟩
  obtain ⟨la,RA⟩ := read a ha coin A
  obtain ⟨lb,RD⟩ := read b hb q D
  rw [cut] at RD
  obtain ⟨u,v,split,_,pub⟩ := two_reveals_force_publication hp Q I fiber closed sep
    offset coherent heads cont start (history.take a) gap history[a] history[b] i la lb coin q RA RD
  have V : history.take b=(history.take a++u)++i::v := by rw [cut,split,List.append_assoc]
  have whole : history=(history.take a++u)++i::(v++history.drop b) := by
    calc
      history = history.take b ++ history.drop b := (List.take_append_drop _ _).symm
      _ = _ := by rw [V]; simp [List.append_assoc]
  let j := (history.take a++u).length
  have jl : j=a+u.length := by simp [j,List.length_take_of_le (Nat.le_of_lt ha)]
  have jlt : j<b := by
    have E := congrArg List.length V
    simp only [List.length_take_of_le (Nat.le_of_lt hb),List.length_append,List.length_cons] at E
    simp only [j,List.length_append]
    omega
  have jh : j<history.length := Nat.lt_trans jlt hb
  have pre : history.take j=history.take a++u :=
    (congrArg (List.take j) whole).trans List.take_append_length
  have mark : history[j]=i := by
    apply Option.some.inj
    rw [←List.getElem?_eq_getElem jh,whole]
    change (((history.take a++u)++i::(v++history.drop b))[(history.take a++u).length]?)=some i
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  refine ⟨j,by omega,jlt,jh,?_⟩
  rw [pre,mark]
  exact pub

end L4.BStarRecoveredReadSeparation
