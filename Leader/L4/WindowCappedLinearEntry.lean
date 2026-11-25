import Leader.L4.WindowCappedAdvance

namespace L4.WindowCappedLinearEntry
open SevenTagCharge WindowA0StockDrain WindowA0EntryJoin WindowA0Entry
open TripleRenewal RootedAssembly WindowFiveStages WindowSpan WindowA0Bridge

def entryK (c N : Nat) := 64+32*(2*c+3)*N

theorem entry_mean_of_cut {p c n s : Nat}
    (hn : 4≤n) (hc : 0<c) (N : Nat) (hN : n≤N) (short : 2*s+2<n)
    (initial : Config p c n) (scope : WindowA0Ledger.Scope n)
    (prepHit hit : Word n → Prop)
    (prepMean : IIDExpectedHittingTimeAtMost wordNext prepHit [] (17*n*(s+1)))
    (cut : ∀ u, FirstExit prepHit u → ¬hit u →
      ∃ (J : Fin n) (H : Nat) (seed : WindowA0ClosedEntry.State p c n),
        H ≤ 2*s ∧ WindowA0ClosedEntry.Admitted initial scope J H seed ∧
        ∀ v, WindowA0Ledger.done
          (GGTiming.runMarks (WindowA0ClosedEntry.next scope) seed v).tag → hit (u++v)) :
    IIDExpectedHittingTimeAtMost wordNext hit [] (entryK c N*n*(s+1)) := by
  let prep := suffixStage ([] : Word n) prepHit
  let B := 32*(2*c+3)*N*n*(s+1)
  have P : IIDExpectedHittingTimeAtMost prep.next prep.ready prep.start (17*n*(s+1)) := by
    intro t
    change iidHitCost wordNext (FirstExit prepHit) t [] ≤ _
    rw [cost_firstExit prepHit t [] (clean_nil _)]
    exact prepMean t
  have h := expected_with_preparation prep hit _ B P (fun u _ hu hnHit => by
    change FirstExit prepHit u at hu
    change ¬hit u at hnHit
    change IIDExpectedHittingTimeAtMost wordNext hit u B
    obtain ⟨J,H,z,hH,hz,accept⟩ := cut u hu hnHit
    by_cases G : WindowCappedAdvance.goal z
    · have H := accept [] G
      have Hu : hit u := (List.append_nil u) ▸ H
      exact (hnHit Hu).elim
    apply mean_at_prefix _ WindowCappedAdvance.goal hit u z accept
    apply expected_mono (WindowCappedAdvance.drained_mean scope J H hn hc z hz)
    have hg : z.gap≤H := (hz.resolve_left G).1.bounded
    have hE : 8*(2*c+1)≤16*(2*c+3) := by omega
    unfold B
    calc
      _ ≤ (2*(s+1))*(n*(16*(2*c+3)*N)) := Nat.mul_le_mul (by omega)
        (Nat.mul_le_mul_left n (Nat.mul_le_mul hE (by omega)))
      _ = 32*(2*c+3)*N*n*(s+1) := by
        rw [show (32:Nat)=2*16 by decide]
        ac_rfl)
  apply expected_mono h
  change 17*n*(s+1)+32*(2*c+3)*N*n*(s+1) ≤ entryK c N*n*(s+1)
  unfold entryK
  rw [Nat.add_mul,Nat.add_mul]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))) _

theorem stock_exit_mean {p c n s : Nat} (hn : 4≤n) (hc0 : 0<c) (N : Nat) (hN : n≤N) (short : 2*s+2<n) (initial : Config p c n)
    (S : WindowA0Ledger.Scope n) (base : Fin n) (z₀ : Cursor p c n) :
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
    IIDExpectedHittingTimeAtMost wordNext hit [] (entryK c N*n*(s+1)) := by
  intro cur prep hit prepMean geometry
  refine entry_mean_of_cut hn hc0 N hN short initial S prep hit prepMean ?_
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

theorem entry_exit_mean {p c n : Nat} (hn : 4≤n) (hc0 : 0<c) (N : Nat) (hN : n≤N) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hc : COV x) (short : 2*span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    let S := entryScope x i
    IIDExpectedHittingTimeAtMost wordNext
      (fun w => (tape S.group S.iTag S.jTag (entryBase x i) (entryCursor x i) w).exit.isSome=true)
      [] (entryK c N*n*(span x i+1)) := by
  let S := entryScope x i
  let z := entryCursor x i
  let base := entryBase x i
  refine stock_exit_mean hn hc0 N hN short x S base z
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

theorem physical_entry_exit_mean {p c n : Nat} (hn : 5≤n) (hc : 12≤c) (N : Nat) (hN : n≤N)
    (x : Config p c n) (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hv : COV x)
    (short : 2*WindowSpan.span x i+2<n)
    (h1 : (x (rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (rootSite x (liftedSite i 2))).leader=false) :
    let S := entryScope x i
    IIDExpectedHittingTimeAtMost wordNext
      (fun w => (tape S.group S.iTag S.jTag (entryBase x i) (entryCursor x i) w).exit.isSome=true)
      [] (entryK c N*n*(WindowSpan.span x i+1)) :=
  entry_exit_mean (by omega) (by omega) N hN x i hm hv short h1 h2

theorem entry_clock {p c n : Nat} (hn : 5≤n) (hc : 12≤c) (N : Nat) (hN : n≤N) (x : Config p c n)
    (i : Fin (RankPhysical.rank x)) (hm : MCOV x) (hv : COV x)
    (short : 2*WindowSpan.span x i+2<n)
    (h1 : (x (WindowSpan.rootSite x (liftedSite i 1))).leader=false)
    (h2 : (x (WindowSpan.rootSite x (liftedSite i 2))).leader=false) :
    IIDExpectedHittingTimeAtMost wordNext (WindowA0FirstExit.done x i) []
      (entryK c N*n*(WindowSpan.span x i+1)) :=
  physical_entry_exit_mean hn hc N hN x i hm hv short h1 h2

open WindowTransactions WindowOwnership WindowA0Join
noncomputable def entry {p c n : Nat} (hn : 5≤n) (hc : 12≤c) (N : Nat) (hN : n≤N)
    (x : Config p c n) (i : Fin (RankPhysical.rank x)) (hq : QuietEntrance x)
    (h7 : 7≤RankPhysical.rank x) (short : 2*WindowSpan.span x i+2<n)
    (he : (WindowOwnership.Front.initial x hq (WindowA0Join.scope x i)).mode=
      .entry (WindowA0Join.scope x i)) :
    Transaction (n:=n) (entryK c N) [] (WindowSpan.span x i) := by
  apply geometric x (by omega) hq i h7 [] (by simp only [physical,WindowSpanTrace.selected_start x i h7,Nat.le_refl])
    (WindowA0FirstExit.done x i)
  have G := WindowA0Join.initial_ghosts x i hq he
  exact entry_clock hn hc N hN x i hq.1 hq.2.1 short G.1 G.2

open WindowPlan WindowLatch
variable {p c n : Nat}
variable (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
variable (x : Config p c n) (hq : QuietEntrance x) (i : Fin (RankPhysical.rank x))
theorem entry_slot (N : Nat) (hN : n≤N) (h5 : 5≤n) (h7 : 7≤RankPhysical.rank x)
    (short : 2*WindowSpan.span x i+2<n) :
    ∀ w h, Allow hp hc hn x hq i 5 w h → ¬done hp hc hn x hq i w →
      Allow hp hc hn x hq i 4 w h ∨
      ∃ T : Transaction (entryK c N) w h,
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
    let T := entry h5 hc N hN x i hq h7 short he
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

end L4.WindowCappedLinearEntry
