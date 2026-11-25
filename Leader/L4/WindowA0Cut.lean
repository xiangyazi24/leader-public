import Leader.L4.WindowA0StockDrain
import Leader.L4.WindowA0ClosedEntry
import Leader.L4.WindowA0Bridge

/-! A first drained cut chooses its own door on the original scheduler
word. The stock cursor and the restart ledger compute exactly the same
routed reason, and both still execute every physical pair after exit. -/
namespace L4.WindowA0Cut
open SevenTagCharge WindowFourHeadTrace WindowA0Route

abbrev Cursor := WindowA0StockDrain.Cursor

def tag {p c n : Nat} (base : Fin n) (z : Cursor p c n) :
    WindowA0Ledger.State p c n :=
  ⟨z.ledger, GGStage.incoming base z.heads.i, GGStage.incoming base z.heads.j,
    GGStage.incoming base z.heads.k,z.exit⟩

def seed {p c n : Nat} (base : Fin n) (z : Cursor p c n) :
    WindowA0ClosedEntry.State p c n :=
  ⟨tag base z,z.heads.j-z.heads.i⟩

private theorem incoming_move {p c n : Nat} (base : Fin n) (x : Ledger p c n)
    (e : Fin n) (d : Nat) :
    GGStage.incoming base (d+(GGStage.moved x.config base e d).toNat) =
      landing x e (GGStage.incoming base d) := by
  have h : GGStage.moved x.config base e d=true ↔ moves x e (GGStage.incoming base d) := by
    simp [GGStage.moved,moves,Bool.and_eq_true]
  by_cases he : GGStage.moved x.config base e d=true
  · rw [he,Bool.toNat_true,landing,if_pos (h.mp he)]
    apply FreshSeparation.succ_inj
    rw [GGStage.incoming_right,GGStage.incoming_right,liftedSite_succ]
  · have hx : ¬moves x e (GGStage.incoming base d) := fun h' => he (h.mpr h')
    simp [Bool.eq_false_iff.mpr he,landing,hx]

theorem tag_commutes {p c n : Nat} (S : WindowA0Ledger.Scope n) (base : Fin n)
    (z : Cursor p c n) (e : Fin n) :
    tag base (WindowA0StockDrain.next S.group S.iTag S.jTag base z e) =
      WindowA0Ledger.next S (tag base z) e := by
  cases hx : z.exit with
  | some r => simp [tag,WindowA0StockDrain.next,WindowA0Ledger.next,hx]
  | none =>
    by_cases hr : routeTwo S.group S.iTag S.jTag z.ledger e=.keep
    · simp [tag,WindowA0StockDrain.next,WindowA0Ledger.next,hx,hr,incoming_move]
    · simp [tag,WindowA0StockDrain.next,WindowA0Ledger.next,hx,hr]

theorem tag_word {p c n : Nat} (S : WindowA0Ledger.Scope n) (base : Fin n)
    (z : Cursor p c n) (y : WindowA0ClosedEntry.State p c n)
    (hy : y.tag=tag base z) (v : List (Fin n)) :
    (GGTiming.runMarks (WindowA0ClosedEntry.next S) y v).tag =
      tag base (GGTiming.runMarks
        (WindowA0StockDrain.next S.group S.iTag S.jTag base) z v) := by
  induction v generalizing y z with
  | nil => exact hy
  | cons e v ih =>
    apply ih
    change WindowA0Ledger.next S y.tag e=_
    rw [hy,tag_commutes]

theorem reason_word {p c n : Nat} (S : WindowA0Ledger.Scope n) (base : Fin n)
    (z : Cursor p c n) (v : List (Fin n)) :
    (GGTiming.runMarks (WindowA0ClosedEntry.next S) (seed base z) v).tag.reason =
      (GGTiming.runMarks (WindowA0StockDrain.next S.group S.iTag S.jTag base) z v).exit :=
  congrArg WindowA0Ledger.State.reason (tag_word S base z _ rfl v)

/-- The geometric inputs refer to the actual cut produced by entry
preparation; no handed-in restored rail invariant is needed. -/
theorem admitted_of_drained {p c n : Nat} {initial : Config p c n}
    (S : WindowA0Ledger.Scope n) (base : Fin n) (z : Cursor p c n) (H : Nat)
    (hz : WindowA0StockDrain.Continuing initial S.iTag S.jTag S.kTag base z)
    (hd : WindowA0StockDrain.drained base z)
    (bounds : z.heads.i < z.heads.j ∧ z.heads.j-z.heads.i ≤ H ∧ z.heads.j-z.heads.i<n)
    (mc : MCOV z.ledger.config) (cv : COV z.ledger.config)
    (opens : ∀ d, z.heads.i≤d → d+1<z.heads.j →
      (z.ledger.config (liftedSite base d)).mark=false) :
    WindowA0ClosedEntry.Admitted initial S (liftedSite base z.heads.j) H (seed base z) := by
  by_cases done : z.exit.isSome=true
  · exact .inl done
  have none : z.exit=none := by cases he : z.exit <;> simp_all
  obtain ⟨hm,hI,hJ,hK,hIg,hJg⟩ := hz
  obtain ⟨_,empty⟩ := hd.resolve_left done
  have top : (WindowA0ClosedEntry.cut (seed base z)).top=liftedSite base z.heads.i :=
    GGStage.incoming_right ..
  have markOf (i : Nat) (a : Fin n) (ht : z.ledger.slots (GGStage.incoming base i)=some a) :
      (z.ledger.config (GGStage.incoming base i)).mark=true := by
    simpa [ht] using (hm.covers (GGStage.incoming base i)).symm
  refine .inr ⟨?_,⟨hm,none,hI,hJ,hK,?_,?_⟩,GGStage.incoming_right ..⟩
  · refine ⟨bounds.2.1,by change 0<z.heads.j-z.heads.i; omega,bounds.2.2,
      ?_,mc,cv,?_,?_,?_,?_,hJg,?_⟩
    · unfold WindowA0IH.target
      rw [top,RestartGeometry.lift_add]
      change liftedSite base (z.heads.i+(z.heads.j-z.heads.i))=_
      congr 1
      omega
    · change (z.ledger.config
        (GGStage.incoming (WindowA0ClosedEntry.cut (seed base z)).top 0)).mark=true
      rw [top]
      have E : GGStage.incoming (liftedSite base z.heads.i) 0=GGStage.incoming base z.heads.i := by
        apply FreshSeparation.succ_inj
        simp [GGStage.incoming_right,liftedSite_zero]
      rw [E]
      exact markOf _ _ hI
    · change (z.ledger.config
        (liftedSite (WindowA0ClosedEntry.cut (seed base z)).top
          (z.heads.j-z.heads.i-1))).mark=true
      rw [top,RestartGeometry.lift_add,show z.heads.i+(z.heads.j-z.heads.i-1)=z.heads.j-1 by omega]
      have E := WindowA0IH.incoming_succ_lift base (z.heads.j-1)
      rw [show z.heads.j-1+1=z.heads.j by omega] at E
      rw [←E]
      exact markOf _ _ hJ
    · intro d hd
      change d+1<z.heads.j-z.heads.i at hd
      change (z.ledger.config (liftedSite (WindowA0ClosedEntry.cut (seed base z)).top d)).mark=false
      rw [top,RestartGeometry.lift_add]
      exact opens _ (by omega) (by omega)
    · change (z.ledger.config (WindowA0ClosedEntry.cut (seed base z)).top).leader=false
      rw [top]; exact hIg
    · intro d hd
      change d<z.heads.j-z.heads.i at hd
      change (z.ledger.config (liftedSite (WindowA0ClosedEntry.cut (seed base z)).top d)).stock=false
      rw [top,RestartGeometry.lift_add]
      exact empty _ (by omega) (by omega)
  · simpa only [seed,tag,GGStage.incoming_right] using hIg
  · simpa only [seed,tag,GGStage.incoming_right] using hJg

open TripleRenewal RootedAssembly WindowFiveStages in
/-- Glue the concrete stock cursor to the repeatable A0 clock. This
uses a single routed exit over the whole word; a cursor which has already
exited is not restarted by the preparation stage. -/
theorem stock_exit_mean {p c n s : Nat} (hn : 4≤n) (initial : Config p c n)
    (S : WindowA0Ledger.Scope n) (base : Fin n) (z₀ : Cursor p c n)
    (trials : ∀ J H, H≤2*s →
      ∀ z, WindowA0ClosedEntry.Admitted initial S J H z →
      ¬WindowA0Ledger.done z.tag →
      Nonempty (UniformAttempt (WindowA0ClosedEntry.next S)
        (fun x => WindowA0Ledger.done x.tag) (WindowA0ClosedEntry.Admitted initial S J H)
        (WindowA0Restart.attemptCost c n H) (WindowA0Restart.attempts c) z)) :
    let cur := GGTiming.runMarks (WindowA0StockDrain.next S.group S.iTag S.jTag base) z₀
    let prep := fun w => WindowA0StockDrain.drained base (cur w)
    let hit := fun w => (cur w).exit.isSome=true
    IIDExpectedHittingTimeAtMost wordNext prep [] (17*n*(s+1)) →
    (∀ u, FirstExit prep u → ¬hit u →
      let z := cur u
      WindowA0StockDrain.Continuing initial S.iTag S.jTag S.kTag base z ∧
      z.heads.i<z.heads.j ∧ z.heads.j-z.heads.i≤2*s ∧ z.heads.j-z.heads.i<n ∧
      MCOV z.ledger.config ∧ COV z.ledger.config ∧
      (∀ d, z.heads.i≤d → d+1<z.heads.j →
        (z.ledger.config (liftedSite base d)).mark=false)) →
    IIDExpectedHittingTimeAtMost wordNext hit [] (WindowA0Restart.entryK c*n*(s+1)) := by
  intro cur prep hit prepMean geometry
  apply WindowA0Bridge.entry_block_mean_of_cut hn initial S prep hit prepMean _ trials
  intro u hu hh
  obtain ⟨hcont,hi,hgap,hnGap,hm,hc,hop⟩ := geometry u hu hh
  refine ⟨liftedSite base (cur u).heads.j,2*s,seed base (cur u),Nat.le_refl _,?_,?_⟩
  · exact admitted_of_drained S base _ _ hcont hu.2 ⟨hi,hgap,hnGap⟩ hm hc hop
  · intro v hd
    change (GGTiming.runMarks (WindowA0ClosedEntry.next S) (seed base (cur u)) v).tag.reason.isSome=true at hd
    rw [reason_word] at hd
    change (cur (u++v)).exit.isSome=true
    dsimp only [cur]
    rw [GGTiming.runMarks_append]
    exact hd

#print axioms stock_exit_mean
#print axioms tag_commutes
#print axioms tag_word
#print axioms reason_word
#print axioms admitted_of_drained
end L4.WindowA0Cut
