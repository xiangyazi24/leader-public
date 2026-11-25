import Leader.L4.WindowA0Release

namespace L4.WindowA0Release
open FixedResidual

private theorem at_left {p c n} (x : Config p c n) (base : Fin n) (j : Nat) :
    step x (liftedSite base j) (liftedSite base j) =
    (pairStep (x (liftedSite base j)) (x (liftedSite base (j+1)))).1 := by
  rw [liftedSite_succ]
  simp [step]

private theorem at_right {p c n} (x : Config p c n) (base : Fin n) (j : Nat) (hj : j+1<n) :
    step x (liftedSite base j) (liftedSite base (j+1)) =
    (pairStep (x (liftedSite base j)) (x (liftedSite base (j+1)))).2 := by
  have h : liftedSite base (j+1)≠liftedSite base j := by
    intro H
    have := liftedSite_inj base hj (by omega) H
    omega
  have hc := liftedSite_succ base j
  simp only [step,←hc,h,if_false,if_true]

private theorem at_other {p c n} (x : Config p c n) (base : Fin n) (j k : Nat)
    (hj : j+1<n) (hk : k<n) (h : k≠j) (h' : k≠j+1) :
    step x (liftedSite base j) (liftedSite base k)=x (liftedSite base k) := by
  have h0 : liftedSite base k≠liftedSite base j :=
    fun he => h (liftedSite_inj base hk (by omega) he)
  have h1 : liftedSite base k≠liftedSite base (j+1) :=
    fun he => h' (liftedSite_inj base hk hj he)
  simp only [step,←liftedSite_succ,h0,h1,if_false]

/-- Paid path on the whole ring before the third request: the next
actual pair is the certified release/door pair or a selected top
has already become living. Off-guard interleaving is literal, by
`padded_release_agrees` on this prefix and on the third mark. -/
theorem paid_ring_release {p c n : Nat} (hn : 5≤n) (x : Config p c n) (base : Fin n)
    (q : Trip (2*c))
    (hm : (x (liftedSite base 1)).mark=true)
    (hp : geometricPay (x (liftedSite base 1)) (x (liftedSite base 2))=true)
    (hb : (x (liftedSite base 2)).stock=false)
    (hw : (x (liftedSite base 3)).leader=false) (hws : (x (liftedSite base 3)).stock=false)
    (hwq : (x (liftedSite base 3)).rail=outward q)
    (hv : (x (liftedSite base 4)).leader=false)
    (port : LastPort (x (liftedSite base 3)) (x (liftedSite base 4)) q) :
    let y := run x [liftedSite base 1,liftedSite base 2]
    (y (liftedSite base 3)).leader=true ∨
      Released (y (liftedSite base 3)) (y (liftedSite base 4)) q := by
  simp only [run]
  rw [at_right _ _ 2 (by omega),at_right _ _ 1 (by omega),
    at_other _ _ 1 3 (by omega) (by omega) (by decide) (by decide),
    at_other _ _ 2 4 (by omega) (by omega) (by decide) (by decide),
    at_other _ _ 1 4 (by omega) (by omega) (by decide) (by decide)]
  exact paid_adjacent_release _ _ _ _ q hm hp hb hw hws hwq hv port

/-- Unpaid path on the whole ring: the pinned turn uses the same,
still-disabled donor, unaffected by the first worker hop. -/
theorem unpaid_ring_release {p c n : Nat} (hn : 5≤n) (x : Config p c n) (base : Fin n)
    (q : Trip (2*c))
    (ham : (x (liftedSite base 1)).mark=true) (hal : (x (liftedSite base 1)).leader=false)
    (has : (x (liftedSite base 1)).stock=false)
    (hbm : (x (liftedSite base 2)).mark=false) (hbl : (x (liftedSite base 2)).leader=false)
    (hbs : (x (liftedSite base 2)).stock=false)
    (hwl : (x (liftedSite base 3)).leader=false) (hws : (x (liftedSite base 3)).stock=false)
    (hres : (x (liftedSite base 3)).residue=nextResidue (x (liftedSite base 2)).residue)
    (hoff : (x (liftedSite base 3)).source=.off) (hwq : (x (liftedSite base 3)).rail=outward q)
    (clean : match q with
      | .init => (x (liftedSite base 2)).rail≠.x
      | .count _ => (x (liftedSite base 2)).rail=.e ∨ (x (liftedSite base 2)).rail=.t) :
    let y := run x [liftedSite base 2,liftedSite base 1]
    (y (liftedSite base 2)).leader=true ∨
      Released (y (liftedSite base 2)) (y (liftedSite base 3)) q := by
  simp only [run]
  rw [at_right _ _ 1 (by omega),at_left _ _ 2,
    at_other _ _ 2 1 (by omega) (by omega) (by decide) (by decide),
    at_other _ _ 1 3 (by omega) (by omega) (by decide) (by decide),
    at_right _ _ 2 (by omega)]
  exact unpaid_adjacent_body_release _ _ _ q ham hal has hbm hbl hbs hwl hws
    hres hoff hwq (by cases q <;> exact clean)

end L4.WindowA0Release
#print axioms L4.WindowA0Release.paid_ring_release
#print axioms L4.WindowA0Release.unpaid_ring_release
