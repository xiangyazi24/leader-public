import Leader.L4.WindowA0Entry
import Leader.L4.WindowA0Cut

/-! The short two-ghost stock cut supplies actual first-entry geometry
for the uniform-attempt continuation on the original word. -/
namespace L4.WindowA0EntryJoin
open WindowA0StockDrain WindowA0Entry SevenTagCharge RootedAssembly
open TripleRenewal WindowSpan

theorem trace_keep {p c n : Nat} {x : Config p c n} (hn : 4≤n)
    (S : WindowA0Ledger.Scope n) (base : Fin n) (z : Cursor p c n)
    (F : Framed x S.iTag S.jTag S.kTag base z)
    (C : COV z.ledger.config) (w : List (Fin n))
    (he : (tape S.group S.iTag S.jTag base z w).exit=none) :
    let y := tape S.group S.iTag S.jTag base z w
    Framed x S.iTag S.jTag S.kTag base y ∧ COV y.ledger.config ∧ z.heads.i≤y.heads.i := by
  induction w generalizing z with
  | nil => exact ⟨F,C,Nat.le_refl _⟩
  | cons e v ih =>
    let y := next S.group S.iTag S.jTag base z e
    have H : (tape S.group S.iTag S.jTag base y v).exit=none := he
    have sticky (z : Cursor p c n) (r : WindowLocal.Event n)
        (h : z.exit=some r) (w : List (Fin n)) :
        (tape S.group S.iTag S.jTag base z w).exit=some r := by
      induction w generalizing z with
      | nil => exact h
      | cons e t ih =>
        change (tape S.group S.iTag S.jTag base (next S.group S.iTag S.jTag base z e) t).exit=some r
        apply ih
        simp [next,h]
    have hy : y.exit=none := by
      cases E : y.exit with
      | none => rfl
      | some r => rw [sticky y r E v] at H; contradiction
    have hz : z.exit=none := by
      cases E : z.exit with
      | none => rfl
      | some r => simp [y,next,E] at hy
    have hr : WindowA0Route.routeTwo S.group S.iTag S.jTag z.ledger e=.keep := by
      by_cases R : WindowA0Route.routeTwo S.group S.iTag S.jTag z.ledger e=.keep
      · exact R
      · simp [y,next,hz,R] at hy
    have hF := framed_keep hn S.group S.iTag S.jTag S.kTag base z e S.iIn S.jIn S.kIn hz hr F
    have hC : COV y.ledger.config := by
      change COV (next S.group S.iTag S.jTag base z e).ledger.config
      rw [projection]
      exact (EntranceCover.cover_closed hn z.ledger.config e ⟨F.cont.1.markCover,C⟩).2
    obtain ⟨hf,hc,hi⟩ := ih y hF hC H
    have M : z.heads.i≤y.heads.i := by
      dsimp only [y]
      rw [(exact_keep S.group S.iTag S.jTag base z e hz hr).1]
      exact Nat.le_add_right ..
    exact ⟨hf,hc,Nat.le_trans M hi⟩

theorem noOther_left {p c n : Nat} {x : Config p c n}
    (a b k base : Fin n) (z : Cursor p c n)
    (F : Framed x a b k base z) (d : Nat) (h₀ : z.heads.i≤d)
    (h₁ : d+1<z.heads.j) :
    (z.ledger.config (liftedSite base d)).mark=false := by
  have H := F.cut.noOther (d-z.heads.i)
  change d-z.heads.i<z.heads.k-z.heads.i-1 →
    d-z.heads.i≠z.heads.j-z.heads.i-1 →
    (z.ledger.config (liftedSite (rightNeighbor (GGStage.incoming base z.heads.i))
      (d-z.heads.i))).mark=false at H
  have hk := F.jk
  specialize H (by omega) (by omega)
  rwa [GGStage.incoming_right,RestartGeometry.lift_add,show z.heads.i+(d-z.heads.i)=d by omega] at H

def entryScope {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x)) :
    WindowA0Ledger.Scope n :=
  let tag := fun j : Nat => WindowRoster.roster x (liftedSite i j)
  ⟨window7 (WindowRoster.roster x) i,tag 1,tag 2,tag 3,
    List.mem_map.mpr ⟨(1 : Fin 7),List.mem_finRange _,rfl⟩,
    List.mem_map.mpr ⟨(2 : Fin 7),List.mem_finRange _,rfl⟩,
    List.mem_map.mpr ⟨(3 : Fin 7),List.mem_finRange _,rfl⟩⟩

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
      [] (WindowA0Restart.entryK c*n*(span x i+1)) := by
  let S := entryScope x i
  let z := entryCursor x i
  let base := entryBase x i
  refine WindowA0Cut.stock_exit_mean hn x S base z trials
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

#print axioms trace_keep
#print axioms noOther_left
#print axioms entry_exit_mean
end L4.WindowA0EntryJoin
