import Leader.L4.WindowA0ReturnStationary
import Leader.L4.WindowA0ApproachOwned

/-! Same-mark physical acceptance of the genuine return, and the exact
cold-payer condition used by the return observer. -/
namespace L4.WindowA0ReturnStep
open FixedResidual WindowA0ReturnEntry WindowA0ReturnMonitor SevenTagCharge

theorem cold_no_pay {p c : Nat} (u v : Site p c)
    (hL : u.leader=false) (hS : u.stock=false) : geometricPay u v=false := by
  unfold geometricPay native materialize fireInitiator
  simp only [hL]
  unfold impact followerBullet payer
  simp [hS]
  repeat' first | split | rfl | simp_all

theorem ready_no_pay {p c n H} {J : Fin n} {z0 : Config p c n}
    {S : WindowA0Ledger.Scope n} {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} (h : Ready z0 S J H x q d false) :
    geometricPay (x.tag.ledger.config x.tag.iSlot)
      (x.tag.ledger.config (rightNeighbor x.tag.iSlot))=false := by
  obtain ⟨hl,hs⟩ := h.coldBeforeRefill rfl
  exact cold_no_pay _ _ hl hs

def successor {Q : Nat} (q : Trip Q) : Option (Fin Q) :=
  match q with
  | .init => if h : 0<Q then some ⟨0,h⟩ else none
  | .count k => if h : k.val+1<Q then some ⟨k.val+1,h⟩ else none

theorem service_successor {Q : Nat} (hQ : 0<Q) (q : Trip Q) :
    serviceDoor (waitingFor q) (inward q) =
      match successor q with
      | some k => ⟨.await k,.uc,.e,false⟩
      | none => ⟨.off,.e,.e,true⟩ := by
  cases q with
  | init => simpa [successor,hQ,waitingFor,inward] using door_init_accept hQ
  | count k =>
    by_cases hk : k.val+1<Q
    · simpa [successor,hk,waitingFor,inward] using door_count_accept k hk
    · simpa [successor,hk,waitingFor,inward] using door_terminal_accept k hk

/-- On the actual first door acceptance the next COUNT worker is
physically written on that mark, not on a second scheduler draw.
If the accepted COUNT is terminal, the selected ghost becomes living
on this very mark and cannot be kept by the scoped router. -/
theorem accept_boundary {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n}
    {z0 : Config p c n} {S : WindowA0Ledger.Scope n}
    {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool}
    (h : Ready z0 S J H x q d b) (hd : d+1=x.gap) :
    let y := WindowA0ClosedEntry.next S x x.tag.jSlot
    match successor q with
    | some k => (y.tag.ledger.config x.tag.jSlot).rail=.uc ∧
        (y.tag.ledger.config J).source=.await k ∧ (y.tag.ledger.config J).leader=false
    | none => WindowA0Ledger.done y.tag ∧ (y.tag.ledger.config J).leader=true := by
  let a := WindowA0ClosedEntry.cut x
  let e := x.tag.jSlot
  let y := WindowA0ClosedEntry.next S x e
  have HH := (WindowA0ReturnStationary.actual_door hn h).1 hd
  change let t := serviceDoor (waitingFor q) (inward q)
    (y.tag.ledger.config e).rail=t.left ∧
    (y.tag.ledger.config J).source=(if t.fire then .off else t.source) ∧
    (y.tag.ledger.config J).leader=t.fire at HH
  dsimp only at HH
  rw [service_successor hQ q] at HH
  change match successor q with
    | some k => (y.tag.ledger.config e).rail=.uc ∧
        (y.tag.ledger.config J).source=.await k ∧ (y.tag.ledger.config J).leader=false
    | none => WindowA0Ledger.done y.tag ∧ (y.tag.ledger.config J).leader=true
  cases Hs : successor q with
  | some k => simpa [Hs] using HH
  | none =>
    have hl : (y.tag.ledger.config J).leader=true := by simpa [Hs] using HH.2.2
    refine ⟨?_,hl⟩
    by_cases route : WindowA0Route.routeTwo S.group S.iTag S.jTag x.tag.ledger e=.keep
    · have hC := WindowA0ClosedEntry.close hn S J H x e h.admitted
      have run : y.tag.reason=none := by simp [y,WindowA0ClosedEntry.next,WindowA0Ledger.next,h.running,route]
      have hclose := hC.resolve_left (by change ¬WindowA0Ledger.done y.tag; simp [WindowA0Ledger.done,run])
      have hGhost : (y.tag.ledger.config J).leader=false := hclose.1.rightGhost
      rw [hGhost] at hl
      contradiction
    · change WindowA0Ledger.done (WindowA0Ledger.next S x.tag e)
      simp [WindowA0Ledger.done,WindowA0Ledger.next,h.running,route]

/-- A kept, nonterminal acceptance supplies the entire next owned
COUNT corridor on the same raw word. -/
theorem accept_owned {p c n H} (hn : 4≤n) (hQ : 0<2*c) {J : Fin n}
    {z0 : Config p c n} {S : WindowA0Ledger.Scope n}
    {x : WindowA0ClosedEntry.State p c n}
    {q : Trip (2*c)} {d : Nat} {b : Bool} {k : Fin (2*c)}
    (h : Ready z0 S J H x q d b) (hd : d+1=x.gap)
    (hk : successor q=some k)
    (keep : ¬WindowA0Ledger.done (WindowA0ClosedEntry.next S x x.tag.jSlot).tag) :
    let y := WindowA0ClosedEntry.next S x x.tag.jSlot
    WindowA0ClosedEntry.Admitted z0 S J H y ∧
      WindowA0ApproachOwned.Physical J (.count k) y d := by
  let a := WindowA0ClosedEntry.cut x
  let e := x.tag.jSlot
  let y := WindowA0ClosedEntry.next S x e
  obtain ⟨old,L,jr⟩ := h.admitted.resolve_left (by simp [WindowA0Ledger.done,h.running])
  have gl : a.gap<n := old.noWrap
  have gp : 0<a.gap := old.gapPos
  have eqD : a.gap=d+1 := hd.symm
  have ed : e=liftedSite a.top d := by
    apply FreshSeparation.succ_inj
    rw [jr,←liftedSite_succ,←eqD]
    exact old.fixedRight.symm
  have es : e≠x.tag.iSlot := by
    intro E
    have hh := congrArg rightNeighbor (ed.symm.trans E)
    change rightNeighbor (liftedSite a.top d)=a.top at hh
    rw [←liftedSite_succ] at hh
    have := liftedSite_inj a.top (show d+1<n by omega) (show 0<n by omega)
      (hh.trans (liftedSite_zero _).symm)
    omega
  have stay : WindowA0XSweep.topShift x e=0 := by
    simp [WindowA0XSweep.topShift,WindowFourHeadTrace.moves,es]
  obtain ⟨cfg,tp,gp'⟩ := WindowA0XSweep.cut_keep_fields S x e h.running keep
  have t : (WindowA0ClosedEntry.cut y).top=a.top := by
    simpa [y,stay,liftedSite_zero] using tp
  have g : y.gap=d+1 := by
    show (WindowA0ClosedEntry.cut y).gap=d+1
    exact (by simpa only [stay,Nat.sub_zero] using gp' : (WindowA0ClosedEntry.cut y).gap=a.gap).trans eqD
  have launch : (y.tag.ledger.config e).rail=.uc ∧
      (y.tag.ledger.config J).source=.await k ∧ (y.tag.ledger.config J).leader=false := by
    have R := accept_boundary hn hQ h hd
    dsimp only at R
    rw [hk] at R
    exact R
  refine ⟨WindowA0ClosedEntry.close hn S J H x e h.admitted,launch.2.1,?_,?_,?_,?_⟩
  · change d<y.gap; omega
  · change ((WindowA0ClosedEntry.cut y).config (liftedSite (WindowA0ClosedEntry.cut y).top d)).rail=.uc
    rw [t,←ed]; exact launch.1
  · intro i hi hi'
    change i<y.gap at hi'
    omega
  · intro i hi
    have ne₁ : liftedSite a.top i≠e := by
      rw [ed]
      intro E
      have := liftedSite_inj a.top (show i<n by omega) (show d<n by omega) E
      omega
    have ne₂ : liftedSite a.top i≠rightNeighbor e := by
      rw [ed,←liftedSite_succ]
      intro E
      have := liftedSite_inj a.top (show i<n by omega) (show d+1<n by omega) E
      omega
    change WindowA0Machine.Writable (.count k)
      ((WindowA0ClosedEntry.cut y).config (liftedSite (WindowA0ClosedEntry.cut y).top i)).rail
    rw [t]
    change (WindowA0ClosedEntry.cut y).config=step a.config e at cfg
    rw [cfg]
    simp only [step,ne₁,ne₂,if_false]
    rw [h.shape.2 i (by omega)]
    simp [railShape,hi,WindowA0Machine.Writable]

#print axioms cold_no_pay
#print axioms ready_no_pay
#print axioms accept_boundary
#print axioms accept_owned
end L4.WindowA0ReturnStep
