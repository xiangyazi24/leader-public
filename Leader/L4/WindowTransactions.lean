import Leader.L4.WindowA0Join
import Leader.L4.WindowSpanTrace

/-! One physical span observer for all outer stages. Each transaction
gets its own frozen first-exit stamp, read from that same observer. -/
namespace L4.WindowTransactions

open WindowFiveStages RootedAssembly TripleRenewal SevenTagCharge WindowRoster
open WindowSpanTrace WindowRosterTrace WindowFrozenSpan

/-- Genuine span of the original selected window at every raw word.
After the first selected loss the stored endpoint pair is retained. -/
def physical {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x)) :
    Word n → Nat := fun w => span (selected x i w)

noncomputable def geometric {p c n C h : Nat} (x : Config p c n)
    (hn : 4≤n) (hq : QuietEntrance x)
    (i : Fin (RankPhysical.rank x)) (h7 : 7≤RankPhysical.rank x)
    (w : Word n) (hw : physical x i w≤h) (test : Word n → Prop)
    (mean : IIDExpectedHittingTimeAtMost wordNext test [] (C*n*(h+1))) :
    Transaction C w h := by
  let raw := fun u => physical x i (w++u)
  let nom := fun u => (selected x i (w++u)).r
  refine ⟨test,stamp test raw,nom,?_,?_,mean⟩
  · rw [stamp_clean test raw [] (clean_nil test)]
    simpa only [raw,List.append_nil] using hw
  · exact suffix_localStep hn _ _ _ (index_mem x i 0) (index_mem x i 6)
      (selected_distinct x i h7 0 6 (by decide)) _ (selected_init_good x i hq.1 hq.2.1) w test

theorem geometric_stamp {p c n C h : Nat} (x : Config p c n)
    (hn : 4≤n) (hq : QuietEntrance x)
    (i : Fin (RankPhysical.rank x)) (h7 : 7≤RankPhysical.rank x)
    (w : Word n) (hw : physical x i w≤h) (test : Word n → Prop)
    (mean : IIDExpectedHittingTimeAtMost wordNext test [] (C*n*(h+1)))
    (u : Word n) (hu : FirstExit test u) :
    (geometric x hn hq i h7 w hw test mean).span u=physical x i (w++u) := by
  change stamp test (fun v => physical x i (w++v)) u=_
  simpa only [List.append_nil] using stamp_of_cut test (fun v => physical x i (w++v)) u [] hu

def coefficient (c : Nat) : Nat := max (WindowA0Restart.entryK c) 4096

/-- Fully instantiated first outer transaction (when both entry
candidates are ghosts in the actual initial front). Immediate living
candidates are represented by a different initial mode. -/
noncomputable def entry {p c n : Nat} (hn : 5≤n) (hc : 12≤c)
    (x : Config p c n) (i : Fin (RankPhysical.rank x)) (hq : QuietEntrance x)
    (h7 : 7≤RankPhysical.rank x) (short : 2*WindowSpan.span x i+2<n)
    (he : (WindowOwnership.Front.initial x hq (WindowA0Join.scope x i)).mode=
      .entry (WindowA0Join.scope x i)) :
    Transaction (n:=n) (coefficient c) [] (WindowSpan.span x i) := by
  apply geometric x (by omega) hq i h7 [] (by simp only [physical,selected_start x i h7,Nat.le_refl])
    (WindowA0FirstExit.done x i)
  have G := WindowA0Join.initial_ghosts x i hq he
  apply expected_mono (WindowA0FirstExit.entry_clock hn hc x i hq.1 hq.2.1 short G.1 G.2)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))

end L4.WindowTransactions
