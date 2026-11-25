import Leader.L4.TagUniqueness
import Leader.L4.TaggedGeometry

namespace L4.FreshSeparation

open TaggedTrace

/-- A physical point lies on a closed clockwise source prefix. -/
def OnTrail {n : Nat} (z : Fin n) (d : Nat) (b : Fin n) : Prop :=
  ∃ j : Nat, j ≤ d ∧ liftedSite z j = b

theorem onTrail_end {n : Nat} (z : Fin n) (d : Nat) :
    OnTrail z d (liftedSite z d) := ⟨d, Nat.le_refl _, rfl⟩

theorem lifted_append {n : Nat} (z : Fin n) (i j : Nat) :
    liftedSite (liftedSite z i) j = liftedSite z (i+j) := by
  apply Fin.ext
  simp [liftedSite, Nat.add_assoc]

theorem lifted_cancel_left {n : Nat} (d : Nat) (hd : d < n)
    {a b : Fin n} (h : liftedSite a d = liftedSite b d) : a = b := by
  have hh := congrArg (fun z => liftedSite z (n-d)) h
  rw [lifted_append, lifted_append, show d+(n-d) = n by omega,
    liftedSite_full,liftedSite_full] at hh
  exact hh

theorem succ_inj {n : Nat} {a b : Fin n} (h : rightNeighbor a = rightNeighbor b) :
    a = b := by
  have he (x : Fin n) : liftedSite x 1 = rightNeighbor x := by
    rw [← Nat.zero_add 1, liftedSite_succ, liftedSite_zero]
  by_cases hn : 1 < n
  · apply lifted_cancel_left 1 hn
    simpa only [he] using h
  · have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    omega

/-- A surviving old tag cannot enter a fixed fresh-bullet prefix when its
anchor is a living leader. This uses the actual transport guard. -/
theorem avoid_fixed_prefix {p c1 n : Nat} (x : Config p c1 n)
    (e i b z : Fin n) (d : Nat) (hz : (x z).leader = true)
    (hout : ¬ OnTrail z d i)
    (hs : carrierStep x e (some i) = some b) : ¬ OnTrail z d b := by
  intro hin
  by_cases he : i = e
  · subst i
    obtain ⟨hb,htr⟩ := carrierStep_selected_survives x e b hs
    obtain ⟨j,hj,heq⟩ := hin
    cases j with
    | zero =>
      rw [liftedSite_zero,hb] at heq
      have hl := ((tagTransfer_iff (x e) (x (rightNeighbor e))).mp htr).2.2.1
      rw [← heq, hz] at hl
      contradiction
    | succ j =>
      rw [liftedSite_succ,hb] at heq
      exact hout ⟨j, by omega, succ_inj heq⟩
  · have h := carrierStep_not_selected_stays x e i b he hs
    exact hout (h ▸ hin)

/-- When a fresh bullet advances at its own outgoing edge, an original
survivor outside the old prefix cannot be at the newly appended site:
that site was empty before the joint old-pair service. -/
theorem avoid_extended_prefix {p c1 n : Nat} (x : Config p c1 n)
    (i b z : Fin n) (d : Nat)
    (hold : (x i).bullet = .live)
    (hempty : (x (liftedSite z (d+1))).bullet = .none)
    (hout : ¬ OnTrail z d i)
    (hs : carrierStep x (liftedSite z d) (some i) = some b) :
    ¬ OnTrail z (d+1) b := by
  intro hin
  have hi : i ≠ liftedSite z d := by
    intro h
    exact hout (h ▸ onTrail_end z d)
  have hbi := carrierStep_not_selected_stays x (liftedSite z d) i b hi hs
  subst b
  obtain ⟨j,hj,h⟩ := hin
  by_cases hj' : j ≤ d
  · exact hout ⟨j,hj',h⟩
  · have he : j = d+1 := by omega
    rw [he] at h
    rw [h] at hempty
    rw [hold] at hempty
    contradiction

/-- The first marker ahead of an original tag rules out an unmarked
clockwise gap containing the rooted source of a fresh killer. A fresh
prefix ending at that first marker must contain the original carrier. -/
theorem firstMark_donor_forces_anchor_overlap
    {p c1 n d len : Nat} {x : Config p c1 n} {b : Fin n}
    (hfirst : FirstMark x b d)
    (incoming : Fin n) (hsrc : (x incoming).mark = true)
    (hlen : len < n)
    (he : liftedSite (rightNeighbor incoming) len = liftedSite b d) :
    OnTrail (rightNeighbor incoming) len b := by
  by_cases h : d ≤ len
  · have he' : liftedSite (liftedSite (rightNeighbor incoming) (len-d)) d =
        liftedSite b d := by
      rw [lifted_append,show len-d+d=len by omega,he]
    exact ⟨len-d,by omega, lifted_cancel_left d hfirst.lt he'⟩
  · have he' : liftedSite (rightNeighbor incoming) len =
        liftedSite (liftedSite b (d-len)) len := by
      rw [lifted_append, show d-len+len=d by omega, he]
    have hz := lifted_cancel_left len hlen he'
    have hj : rightNeighbor incoming = rightNeighbor (liftedSite b (d-len-1)) := by
      rw [← liftedSite_succ,show (d-len-1)+1=d-len by omega]
      exact hz
    have hin := succ_inj hj
    have hbad := hfirst.before (d-len-1) (by omega)
    rw [← hin,hsrc] at hbad
    contradiction

end L4.FreshSeparation

