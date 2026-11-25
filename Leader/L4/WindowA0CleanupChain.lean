import Leader.L4.WindowA0XSweep
import Leader.L4.WindowA0ReverseSweep

namespace L4.WindowA0CleanupChain
open WindowA0ClosedEntry WindowA0XSweep WindowFourHeadTrace

def XFree {p c n : Nat} (z : WindowA0ClosedEntry.State p c n) : Prop := Clean (cut z) z.gap

theorem xfree_next {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ClosedEntry.State p c n) (e : Fin n) (hz : Admitted initial S J H z)
    (hclean : XFree z) (hkeep : ¬WindowA0Ledger.done (next S z e).tag) :
    XFree (next S z e) := by
  have old : ¬WindowA0Ledger.done z.tag := by
    intro h
    apply hkeep
    change (WindowA0Ledger.next S z.tag e).reason.isSome=true
    rw [WindowA0Ledger.terminal_sticky S z.tag e h]
    exact h
  have ho := hz.resolve_left old
  have hy := (WindowA0ClosedEntry.close hn S J H z e hz).resolve_left hkeep
  obtain ⟨hf,ht,hg⟩ := cut_keep_fields S z e ho.2.1.2.1 hkeep
  have hp (he : rightNeighbor e=(cut z).top) (hh : topShift z e=0) :
      geometricPay ((cut z).config e) ((cut z).config (rightNeighbor e))=false := by
    apply Bool.eq_false_iff.mpr
    intro hp
    have he' : e=z.tag.iSlot := FreshSeparation.succ_inj he
    have H' : moves z.tag.ledger e z.tag.iSlot := ⟨he',hp⟩
    simp [topShift,H'] at hh
  have cap : topShift z e≤1 := by unfold topShift; split <;> omega
  have h := clean_keep_capped hn _ _ e z.gap (topShift z e) ho.1 hy.1
    (Nat.le_refl _) hclean cap hf ht hg hp
  change Clean (cut (next S z e)) (cut (next S z e)).gap
  rw [hg]
  change Clean (cut (next S z e)) (z.gap-topShift z e)
  have hh : ¬(z.gap<(cut z).gap ∧ e=liftedSite (cut z).top z.gap) := by
    change ¬(z.gap<z.gap ∧ _)
    omega
  simpa only [if_neg hh,Nat.add_zero] using h

theorem reverse_keeps_xfree {p c n : Nat} {initial : Config p c n}
    (hn : 4≤n) (S : WindowA0Ledger.Scope n) (J : Fin n) (H : Nat)
    (z : WindowA0ReverseSweep.RevState p c n) (w : List (Fin n))
    (hz : Admitted initial S J H z.physical)
    (hc : WindowA0Ledger.done z.physical.tag ∨ XFree z.physical) :
    let y := GGTiming.runMarks (WindowA0ReverseSweep.revNext S) z w
    WindowA0Ledger.done y.physical.tag ∨ XFree y.physical := by
  induction w generalizing z with
  | nil => exact hc
  | cons e w ih =>
    apply ih _ (WindowA0ClosedEntry.close hn S J H z.physical e hz)
    by_cases hd : WindowA0Ledger.done (WindowA0ClosedEntry.next S z.physical e).tag
    · exact .inl hd
    · right
      apply xfree_next hn S J H z.physical e hz _ hd
      rcases hc with h|h
      · exfalso
        apply hd
        change (WindowA0Ledger.next S z.physical.tag e).reason.isSome=true
        rw [WindowA0Ledger.terminal_sticky S z.physical.tag e h]
        exact h
      · exact h

end L4.WindowA0CleanupChain
