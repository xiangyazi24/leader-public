import Leader.L4.FastExpEvent
import Leader.L4.FastExpMean

namespace L4.FastParallel
open FastExp FastExpEvent TaggedTail

/-- Run every counter on the very same raw edge, with neither an
independent schedule nor a random choice of a path. -/
noncomputable def stepAll {α : Type} {n K : Nat} (next : α → Fin n → α)
    (ev : Fin K → Nat → α → Fin n → Prop) (z : α × (Fin K → Nat)) (e : Fin n) :
    α × (Fin K → Nat) :=
  (next z.1 e,fun i => (sequenceNext next (ev i) (z.1,z.2 i) e).2)

def Domain {α : Type} {K : Nat} (I : α → Prop) (H : Nat) (z : α × (Fin K → Nat)) : Prop :=
  I z.1 ∧ ∀ i,z.2 i≤H

theorem domain_closed {α : Type} {n K : Nat} (next : α → Fin n → α)
    (I : α → Prop) (ev : Fin K → Nat → α → Fin n → Prop) (H : Nat)
    (keep : ∀ x e, I x → I (next x e)) (z : α × (Fin K → Nat)) (e : Fin n)
    (hz : Domain I H z) : Domain I H (stepAll next ev z e) := by
  exact ⟨keep _ e hz.1,fun i =>
    (sequence_closed next I (ev i) H keep (z.1,z.2 i) e ⟨hz.1,hz.2 i⟩).2⟩

theorem done_sticky {α : Type} {n K : Nat} (next : α → Fin n → α)
    (ev : Fin K → Nat → α → Fin n → Prop) (i : Fin K)
    (z : α × (Fin K → Nat)) (e : Fin n) (h : z.2 i=0) :
    (stepAll next ev z e).2 i=0 := by simp [stepAll,sequenceNext,h]

noncomputable def pathCert {α : Type} {n K : Nat} (next : α → Fin n → α)
    (I : α → Prop) (ev : Fin K → Nat → α → Fin n → Prop) (H rate G S : Nat)
    (hr : 0<rate) (hg : 0<G) (hs : 0<S)
    (stage : ∀ i k, EventCert next I (ev i k) rate G S)
    (keep : ∀ x e, I x → I (next x e)) (i : Fin K) :
    ExpCert (stepAll next ev) (Domain I H) (fun z => z.2 i=0) rate (G^H) := by
  let b := sequence next I (ev i) rate G S H hr hg hs (stage i) keep
  let pr := fun z : α × (Fin K → Nat) => (z.1,z.2 i)
  refine ⟨b.scale,b.positive,b.ratePositive,b.gainPositive,fun t z => b.pot t (pr z),?_,?_,?_,?_⟩
  · exact fun t z hz => b.lo t (pr z) ⟨hz.1,hz.2 i⟩
  · exact fun t z hz => b.hi t (pr z) ⟨hz.1,hz.2 i⟩
  · exact fun t z hz hd => b.terminal t (pr z) ⟨hz.1,hz.2 i⟩ hd
  · exact fun t z hz hd => b.drift t (pr z) ⟨hz.1,hz.2 i⟩ hd

private theorem constant_sum (K w : Nat) : sumEdge (fun _ : Fin K => w)=K*w := by
  induction K with
  | zero => simp [sumEdge]
  | succ K ih =>
    simp only [sumEdge,List.ofFn_succ,List.sum_cons] at *
    rw [ih,Nat.succ_mul,Nat.add_comm]

/-- Service-chain bound for K paths of length H. Their service
law may depend on the entire pre-mark state and may correlate fully. -/
theorem all_paths_mean {α : Type} {n K : Nat} (next : α → Fin n → α)
    (I : α → Prop) (ev : Fin K → Nat → α → Fin n → Prop) (H μ c : Nat)
    (hμ : 0<μ) (hn : 0<n) (hc : K*2^H≤2^c)
    (keep : ∀ x e, I x → I (next x e))
    (uniform : ∀ i k x, I x → IIDExpectedHittingTimeAtMost
      (flagNext next (ev i k)) (fun z => z.2=true) (x,false) μ)
    (z : α × (Fin K → Nat)) (hz : Domain I H z) :
    IIDExpectedHittingTimeAtMost (stepAll next ev) (fun z => ∀ i,z.2 i=0) z
      ((2*μ)*(c+1)) := by
  have hr : 0<2*μ := Nat.mul_pos (by decide) hμ
  exact FastExpMean.union_mean hr (fun _ => 2^H)
    (pathCert next I ev H (2*μ) 2 μ hr (by decide) hμ
      (fun i k => service_of_mean next I (ev i k) μ hμ (uniform i k) keep) keep)
    hn (domain_closed next I ev H keep) (done_sticky next ev) c
    (by rw [constant_sum]; exact hc) z hz

end L4.FastParallel
