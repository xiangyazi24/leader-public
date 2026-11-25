import Leader.L4.WindowPlan

namespace L4.WindowCappedEntry
open SevenTagCharge WindowA0StockDrain WindowA0EntryJoin WindowA0Entry
open TripleRenewal RootedAssembly WindowFiveStages WindowSpan
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
    IIDExpectedHittingTimeAtMost wordNext hit [] (WindowA0Restart.entryKSharp c*n*(s+1)) := by
  intro cur prep hit prepMean geometry
  apply WindowA0Bridge.entry_mean_of_cut initial S prep hit prepMean _ trials
  intro u hu hh
  obtain ⟨hcont,hi,hgap,hnGap,hm,hc,hop⟩ := geometry u hu hh
  refine ⟨liftedSite base (cur u).heads.j,2*s,WindowA0Cut.seed base (cur u),Nat.le_refl _,?_,?_⟩
  · exact WindowA0Cut.admitted_of_drained S base _ _ hcont hu.2 ⟨hi,hgap,hnGap⟩ hm hc hop
  · intro v hd
    change (GGTiming.runMarks (WindowA0ClosedEntry.next S) (WindowA0Cut.seed base (cur u)) v).tag.reason.isSome=true at hd
    rw [WindowA0Cut.reason_word] at hd
    change (cur (u++v)).exit.isSome=true
    dsimp only [cur]
    rw [GGTiming.runMarks_append]
    exact hd

theorem entry_exit_mean {p c n : Nat} (hn : 4≤n) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hc : COV x) (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false)
    (trials : ∀ J H, H≤2*span x i →
      ∀ z, WindowA0ClosedEntry.Admitted x (entryScope x i) J H z →
      ¬WindowA0Ledger.done z.tag →
      Nonempty (UniformAttempt (WindowA0ClosedEntry.next (entryScope x i))
        (fun x => WindowA0Ledger.done x.tag) (WindowA0ClosedEntry.Admitted x (entryScope x i) J H)
        (WindowA0Restart.attemptCost c n H) (WindowA0Restart.attempts c) z)) :
    let S := entryScope x i
    IIDExpectedHittingTimeAtMost wordNext
      (fun w => (tape S.group S.iTag S.jTag (entryBase x i) (entryCursor x i) w).exit.isSome=true)
      [] (WindowA0Restart.entryKSharp c*n*(span x i+1)) := by
  let S := entryScope x i
  let z := entryCursor x i
  let base := entryBase x i
  refine stock_exit_mean hn x S base z trials
    (entry_drain hn x i hm hc short h1 h2) ?_
  intro u _ he
  let y := tape S.group S.iTag S.jTag base z u
  have H : y.exit=none := by
    change ¬y.exit.isSome=true at he
    cases E : y.exit <;> simp_all
  obtain ⟨C,_,_,_,hu⟩ := entry_continuing x i hm hc short h1 h2
  have A := WindowA0.a0_initialCut x i hm hc short h1 h2
  have hA : GGStage.AmbientConsecutive z.ledger.config base z.heads := A.2.2.2.1
  have F : Framed x S.iTag S.jTag S.kTag base z :=
    ⟨C,hA.1,hA.2.1,WindowA0StockCap.cut_of_ambient _ _ _ _ _ C hA⟩
  obtain ⟨G,Q,M⟩ := trace_keep hn S base z F hc u H
  have P := paid_le_of_noexit hn S.group S.iTag S.jTag S.kTag base z S.iIn S.jIn S.kIn F u H
  change y.heads.j-z.heads.j≤z.heads.k-z.heads.i at P
  change z.heads.k-z.heads.i≤span x i at hu
  have IJ := F.ij
  have JK := F.jk
  have ji := G.ij
  have jk := G.jk
  have W := G.cut.width
  change y.heads.k-y.heads.i-1+1<n at W
  change z.heads.i≤y.heads.i at M
  change y.heads.i<y.heads.j at ji
  change y.heads.j<y.heads.k at jk
  change WindowA0StockDrain.Continuing x S.iTag S.jTag S.kTag base y ∧
    y.heads.i<y.heads.j ∧ y.heads.j-y.heads.i≤2*span x i ∧
    y.heads.j-y.heads.i<n ∧ MCOV y.ledger.config ∧ COV y.ledger.config ∧ _
  exact ⟨G.cont,ji,by omega,by omega,G.cont.1.markCover,Q,noOther_left _ _ _ _ _ G⟩

theorem physical_entry_exit_mean {p c n : Nat} (hn : 5≤n) (hc : 12≤c)
    (x : Config p c n) (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hv : COV x)
    (short : 2*WindowSpan.span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    let S := entryScope x i
    IIDExpectedHittingTimeAtMost wordNext
      (fun w => (tape S.group S.iTag S.jTag (entryBase x i) (entryCursor x i) w).exit.isSome=true)
      [] (WindowA0Restart.entryKSharp c*n*(WindowSpan.span x i+1)) :=
  entry_exit_mean (by omega) x i hm hv short h1 h2 (fun J H h  z hz hl =>
    WindowA0Uniform.physical_attempt hn hc x (entryScope x i) J H (by omega) z hz hl)

theorem entry_clock {p c n : Nat} (hn : 5≤n) (hc : 12≤c) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hv : COV x)
    (short : 2*WindowSpan.span x i+2<n)
    (h1 : (x (WindowSpan.rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (WindowSpan.rootSite x (liftedSite i 2))).leader=false) :
    IIDExpectedHittingTimeAtMost wordNext (WindowA0FirstExit.done x i) []
      (WindowA0Restart.entryKSharp c*n*(WindowSpan.span x i+1)) :=
  physical_entry_exit_mean hn hc x i hm hv short h1 h2

open WindowTransactions WindowOwnership WindowA0Join
noncomputable def entry {p c n : Nat} (hn : 5≤n) (hc : 12≤c)
    (x : Config p c n) (i : Fin (RankPhysical.rank x)) (hq : QuietEntrance x)
    (h7 : 7≤RankPhysical.rank x) (short : 2*WindowSpan.span x i+2<n)
    (he : (WindowOwnership.Front.initial x hq (WindowA0Join.scope x i)).mode=
      .entry (WindowA0Join.scope x i)) :
    Transaction (n:=n) (WindowA0Restart.entryKSharp c) [] (WindowSpan.span x i) := by
  apply geometric x (by omega) hq i h7 [] (by simp only [physical,WindowSpanTrace.selected_start x i h7,Nat.le_refl])
    (WindowA0FirstExit.done x i)
  have G := WindowA0Join.initial_ghosts x i hq he
  exact entry_clock hn hc x i hq.1 hq.2.1 short G.1 G.2

open WindowPlan WindowLatch
variable {p c n : Nat}
variable (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
variable (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))
theorem entry_slot (h5 : 5≤n) (h7 : 7≤RankPhysical.rank x)
    (short : 2*WindowSpan.span x i+2<n) :
    ∀ w h, Allow hp hc hn x hq i 5 w h → ¬done hp hc hn x hq i w →
      Allow hp hc hn x hq i 4 w h ∨
      ∃ T : Transaction (WindowA0Restart.entryKSharp c) w h,
        ∀ u, FirstExit T.hit u → ¬done hp hc hn x hq i (w++u) →
          Allow hp hc hn x hq i 4 (w++u) (T.span u) := by
  intro w h hInit _
  change w=[] ∧ h=WindowSpan.span x i at hInit
  obtain ⟨rfl,rfl⟩ := hInit
  cases E : startMode (z:=SevenTagCharge.initial x) (scope x i) with
  | some P =>
    apply Or.inl
    apply Or.inr
    refine ⟨(by simp only [physical,WindowSpanTrace.selected_start x i h7,Nat.le_refl]),.inr ⟨by decide,?_⟩⟩
    refine ⟨Front.initial x hq (scope x i), P.normalize,rfl,?_,(P.normalize).positive⟩
    simp [Front.initial,E]
  | none =>
    have he : (Front.initial x hq (scope x i)).mode=.entry (scope x i) := by simp [Front.initial,E]
    let T := entry h5 hc x i hq h7 short he
    apply Or.inr
    refine ⟨T,?_⟩
    intro u hu nd
    change ¬done hp hc hn x hq i u at nd
    have HU : FirstExit (WindowA0FirstExit.done x i) u := hu
    apply Or.inr
    refine ⟨?_,.inr ⟨by decide,entry_handoff hp hc hn x hq i he u HU nd⟩⟩
    unfold T entry
    rw [geometric_stamp _ _ _ _ _ _ _ _ _ _ HU]
    exact Nat.le_refl _

end L4.WindowCappedEntry
