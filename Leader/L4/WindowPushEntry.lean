import Leader.L4.WindowSpan
import Leader.L4.WindowA0Push
import Leader.L4.WindowLatch

namespace L4.WindowPushEntry
open WindowA0Push WindowFourHeadCut SevenTagCharge RankSupplier

/-- Lifted offsets concatenate even when the residue crosses zero. -/
theorem lift_add {n : Nat} (v : Fin n) (i j : Nat) :
    liftedSite (liftedSite v i) j=liftedSite v (i+j) := by
  apply Fin.ext
  change (((v.val+i)%n)+j)%n=(v.val+(i+j))%n
  rw [Nat.mod_add_mod, Nat.add_assoc]

/-- Consecutive J/W/K input.  The two sectors use the currently
observed marks and slots, not an order on identifiers. -/
structure RearCut {p c n : Nat} (z : Ledger p c n)
    (j w k a b cTag : Fin n) (bi ci : Nat) : Prop where
  jTag : z.slots j=some a
  wTag : z.slots w=some b
  kTag : z.slots k=some cTag
  firstW : FirstMark z.config (rightNeighbor j) bi
  firstK : FirstMark z.config (rightNeighbor w) ci
  wAt : liftedSite (rightNeighbor j) bi=w
  kAt : liftedSite (rightNeighbor w) ci=k
  noWrap : (bi+1+ci)+1<n

/-- Instantiate the three-head shadow geometry from two actual first marks. -/
theorem rear_geometry {p c n : Nat} {z : Ledger p c n}
    {j w k a b cTag : Fin n} {bi ci : Nat}
    (r : RearCut z j w k a b cTag bi ci) :
    Geometry z j w k a b cTag bi (bi+1+ci) := by
  have hnext : liftedSite (rightNeighbor j) (bi+1)=rightNeighbor w := by
    rw [liftedSite_succ,r.wAt]
  refine ⟨r.jTag,r.wTag,r.kTag,r.wAt,?_,by omega,r.noWrap,?_⟩
  · rw [←lift_add,hnext,r.kAt]
  · intro i hi hne
    by_cases hb : i<bi
    · exact Bool.eq_false_iff.mpr (r.firstW.before i hb)
    · have hbi : bi+1 ≤ i := by omega
      have hci : i-(bi+1)<ci := by omega
      have hi' : liftedSite (rightNeighbor j) i=
          liftedSite (rightNeighbor w) (i-(bi+1)) := by
        rw [← hnext,lift_add,Nat.add_sub_of_le hbi]
      rw [hi']
      exact Bool.eq_false_iff.mpr (r.firstK.before _ hci)

/-- Transport the same old ledger into the push observer, with no physical mark. -/
def start {p c n : Nat} (z : Ledger p c n) (j w k : Fin n)
    (d bi ci : Nat) : WindowA0Push.State p c n :=
  ⟨⟨z,j,w,k,bi,bi+1+ci⟩,d,false⟩

theorem ordinary_entry {p c n : Nat} {initial : Config p c n}
    {z : Ledger p c n} (v : Fin n) (cert : List (Fin n))
    (j w k a b cTag sv label : Fin n) (d bi ci : Nat)
    (hv : Valid z initial) (r : RearCut z j w k a b cTag bi ci)
    (hs : WindowLocal.TaggedLeader z sv label) (hlabel : label∈cert)
    (hsite : rightNeighbor sv=v) (hj : j=liftedSite v d)
    (hnext : FirstMark z.config v d) (hgap : d+1<n)
    (hghost : (z.config (rightNeighbor j)).leader=false) :
    ValidCut initial v cert a b cTag (start z j w k d bi ci) := by
  have hl : Live v (init z.config d) := by
    refine ⟨rfl,hv.markCover,?_,?_,hnext,hgap⟩
    · rw [←hsite]; exact hs.2
    · change (z.config (liftedSite v (d+1))).leader=false
      rw [liftedSite_succ,←hj]; exact hghost
  exact ⟨hv,rear_geometry r,hj,⟨hl,.inl ⟨sv,label,hsite,hlabel,hs⟩⟩⟩

/-- A latched named kill supplies the successor cut's protected supplier
and target location, once the two following sectors are reconstructed. -/
theorem protected_entry {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (E : WindowProtectedOuter.Entry initial g) (cert : List (Fin n))
    (w k b cTag : Fin n) (bi ci : Nat)
    (r : RearCut E.ledger (liftedSite E.supplier E.donor) w k E.victim b cTag bi ci) :
    ValidCut initial E.supplier cert E.victim b cTag
      (start E.ledger (liftedSite E.supplier E.donor) w k E.donor bi ci) := by
  exact ⟨E.auth.1,rear_geometry r,rfl,⟨E.auth.2.1.1,.inr E.auth.2.1⟩⟩

/-- Adjacent current roster addresses furnish both open sectors.  J
and K have distinct tags, so the second gap cannot complete a lap. -/
theorem rear_of_roster {p c n : Nat} {z : Ledger p c n}
    (i : Fin (RankPhysical.rank z.config)) (a b k : Fin n)
    (hJ : z.slots (WindowRoster.roster z.config i)=some a)
    (hW : z.slots (WindowRoster.roster z.config (rightNeighbor i))=some b)
    (hK : z.slots (WindowRoster.roster z.config (rightNeighbor (rightNeighbor i)))=some k)
    (hJW : a≠b) (hJK : a≠k) :
    RearCut z (WindowRoster.roster z.config i)
      (WindowRoster.roster z.config (rightNeighbor i))
      (WindowRoster.roster z.config (rightNeighbor (rightNeighbor i)))
      a b k (WindowSpan.gap z.config i-1)
      (WindowSpan.gap z.config (rightNeighbor i)-1) := by
  open WindowRoster WindowSpan in
  have hb := gap_pos z.config i
  open WindowRoster WindowSpan in
  have hc := gap_pos z.config (rightNeighbor i)
  open WindowRoster WindowSpan in
  have hl : gap z.config i≤n := by
    have := (firstMark_after_roster z.config i).lt
    omega
  open WindowRoster WindowSpan in
  have hlt : gap z.config i<n := by
    by_cases H : gap z.config i=n
    · have H' := wall_at_gap z.config i
      rw [H,liftedSite_full] at H'
      exact False.elim (hJW (Option.some.inj (hJ.symm.trans (H' ▸ hW))))
    · omega
  open WindowRoster WindowSpan in
  have hW' := wall_at_gap z.config i
  open WindowRoster WindowSpan in
  have hK' := wall_at_gap z.config (rightNeighbor i)
  open WindowRoster WindowSpan in
  have hret : liftedSite (roster z.config (rightNeighbor i))
      (n-gap z.config i)=roster z.config i := by
    rw [←hW',lift_add,Nat.add_sub_of_le hl,liftedSite_full]
  open WindowRoster WindowSpan in
  have hret' : liftedSite (rightNeighbor (roster z.config (rightNeighbor i)))
      (n-gap z.config i-1)=roster z.config i := by
    rw [liftedSite_advance,show n-gap z.config i-1+1=n-gap z.config i by omega,hret]
  open WindowRoster WindowSpan in
  have hKfirst := firstMark_after_roster z.config (rightNeighbor i)
  open WindowRoster WindowSpan in
  have hbound := hKfirst.min_le
    (show (z.config (liftedSite (rightNeighbor (roster z.config (rightNeighbor i)))
      (n-gap z.config i-1))).mark=true by
      rw [hret']; exact (roster_exact z.config _).mp ⟨i,rfl⟩)
  open WindowRoster WindowSpan in
  have hsum : gap z.config i+gap z.config (rightNeighbor i)<n := by
    by_cases H : gap z.config i+gap z.config (rightNeighbor i)=n
    · have he : gap z.config (rightNeighbor i)=n-gap z.config i := by omega
      rw [he,hret] at hK'
      exact False.elim (hJK (Option.some.inj (hJ.symm.trans (hK' ▸ hK))))
    · omega
  open WindowRoster WindowSpan in
  refine ⟨hJ,hW,hK,firstMark_after_roster z.config i,hKfirst,?_,?_,by omega⟩
  · rw [liftedSite_advance,show gap z.config i-1+1=gap z.config i by omega,hW']
  · rw [liftedSite_advance,show gap z.config (rightNeighbor i)-1+1=
      gap z.config (rightNeighbor i) by omega,hK']

open WindowRoster WindowSpan in
/-- The ordinary start follows directly from four consecutive current
roster positions and the supplier's certified live bit. -/
theorem ordinary_of_roster {p c n : Nat} {initial : Config p c n}
    {z : Ledger p c n} (cert : List (Fin n)) (i : Fin (RankPhysical.rank z.config))
    (lab a b k : Fin n) (hv : Valid z initial)
    (hs : WindowLocal.TaggedLeader z (roster z.config i) lab)
    (hcert : lab∈cert)
    (hJ : z.slots (roster z.config (rightNeighbor i))=some a)
    (hW : z.slots (roster z.config (rightNeighbor (rightNeighbor i)))=some b)
    (hK : z.slots (roster z.config (rightNeighbor (rightNeighbor (rightNeighbor i))))=some k)
    (h0 : lab≠a) (h1 : a≠b) (h2 : a≠k)
    (hghost : (z.config (rootSite z.config (rightNeighbor i))).leader=false) :
    ValidCut initial (rootSite z.config i) cert a b k
      (start z (roster z.config (rightNeighbor i))
        (roster z.config (rightNeighbor (rightNeighbor i)))
        (roster z.config (rightNeighbor (rightNeighbor (rightNeighbor i))))
        (gap z.config i-1) (gap z.config (rightNeighbor i)-1)
        (gap z.config (rightNeighbor (rightNeighbor i))-1)) := by
  have hpos := gap_pos z.config i
  have H := wall_at_gap z.config i
  have hs' := (firstMark_after_roster z.config i).lt
  have hlt : gap z.config i<n := by
    by_cases he : gap z.config i=n
    · rw [he,liftedSite_full] at H
      exact False.elim (h0 (Option.some.inj (hs.1.symm.trans (H ▸ hJ))))
    · omega
  apply ordinary_entry (rootSite z.config i) cert _ _ _ a b k (roster z.config i) lab
    _ _ _ hv (rear_of_roster (rightNeighbor i) a b k hJ hW hK h1 h2)
    hs hcert rfl _ (firstMark_after_roster z.config i) (by omega) hghost
  change roster z.config (rightNeighbor i)=
    liftedSite (rightNeighbor (roster z.config i)) (gap z.config i-1)
  rw [liftedSite_advance,show gap z.config i-1+1=gap z.config i by omega,H]

open WindowRoster WindowSpan in
/-- The protected entry's donor determines its current roster position;
the supplied roster position cannot name another occurrence of the tag. -/
theorem protected_of_roster {p c n : Nat} {initial : Config p c n} {g : List (Fin n)}
    (E : WindowProtectedOuter.Entry initial g) (cert : List (Fin n))
    (i : Fin (RankPhysical.rank E.ledger.config))
    (b k : Fin n) (hJ : E.ledger.slots (roster E.ledger.config i)=some E.victim)
    (hW : E.ledger.slots (roster E.ledger.config (rightNeighbor i))=some b)
    (hK : E.ledger.slots (roster E.ledger.config (rightNeighbor (rightNeighbor i)))=some k)
    (h1 : E.victim≠b) (h2 : E.victim≠k) :
    ValidCut initial E.supplier cert E.victim b k
      (start E.ledger (roster E.ledger.config i)
        (roster E.ledger.config (rightNeighbor i))
        (roster E.ledger.config (rightNeighbor (rightNeighbor i)))
        E.donor (gap E.ledger.config i-1) (gap E.ledger.config (rightNeighbor i)-1)) := by
  have he : roster E.ledger.config i=liftedSite E.supplier E.donor :=
    E.auth.1.unique _ _ E.victim hJ E.auth.2.2.1
  have hR := rear_of_roster i E.victim b k hJ hW hK h1 h2
  rw [he] at hR ⊢
  exact protected_entry E cert _ _ b k _ _ hR

end L4.WindowPushEntry
