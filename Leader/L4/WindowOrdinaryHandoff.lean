import Leader.L4.WindowOrdinarySlot
import Leader.L4.WindowFrontDone

namespace L4.WindowOrdinaryHandoff
open WindowOwnership WindowOrdinarySlot WindowProtectedOuter WindowLatch
open WindowLocal SevenTagCharge WindowFiveStages RootedAssembly GGTiming

theorem skipOnce_length {p c n} {z : Ledger p c n} {g}
    (P R : Progress z g) (h : P.skipOnce=some R) :
    R.cert.length=P.cert.length+1 := by
  unfold Progress.skipOnce at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
        simp [Progress.attachLiving]
      · cases h
  · cases h

theorem normalize_length_ge {p c n} {z : Ledger p c n} {g}
    (P : Progress z g) : P.cert.length≤P.normalize.cert.length := by
  unfold Progress.normalize
  split
  · exact Nat.le_refl _
  · rename_i R HR
    have hR := skipOnce_length P R HR
    cases h : R.skipOnce with
    | none => simp [hR]
    | some S => have hS := skipOnce_length R S h; simp [hS,hR]; omega

theorem extend_length {p c n} {x : Config p c n} {z : Ledger p c n} {g}
    (P : Progress z g) (hn : 4≤n) (hv : Valid z x) (e a site : Fin n)
    (hr : route g P.cert P.target z e=.targetBirth a site) :
    (P.extend hn hv e a site hr).cert.length=P.cert.length+1 := by
  rcases P with ⟨pre,cert,after,part,owns,hp,hb⟩
  cases after with
  | nil =>
    have ht := (birth_inv z g cert _ e a site hr).2.2.1
    simp [Progress.target] at ht
  | cons b rest =>
    have ht := (birth_inv z g cert _ e a site hr).2.2.1
    have hlen : cert.length<3 := by
      apply Classical.byContradiction; intro h
      simp [Progress.target,h] at ht
    have he : b=a := by simpa [Progress.target,hlen] using ht
    subst b
    simp [Progress.extend]
    generalize E : Progress.target_head _ a ht = G
    cases G
    simp

def Handoff {p c n} {x : Config p c n} {g : List (Fin n)} (cert : List (Fin n))
    (q : Cursor (Front x g) x g) : Prop :=
  WindowFrontDone.done q ∨
    (∃ F P, q=.inl F ∧ F.mode=.owned P ∧ cert.length+1≤P.cert.length) ∨
    ∃ en, q=.inr (startRunning en) ∧ en.victim∈cert

theorem edge_handoff {p c n} {x : Config p c n} {g}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (F : Front x g) (P : Progress F.ledger g) (hm : F.mode=.owned P)
    (e : Fin n) (hne : route g P.cert P.target F.ledger e≠.keep) :
    Handoff P.cert (joinedNext (front hn (WindowOwnership.decide hp hc hn)) (.inl F) e) := by
  unfold joinedNext front WindowOwnership.decide
  simp only [hm]
  split
  · rename_i t heq
    split at heq
    · rename_i hr
      exact (hne hr).elim
    · cases heq
      exact .inl trivial
    · rename_i a pos hr
      cases heq
      have ge := normalize_length_ge (P.extend hn F.valid e a pos hr)
      rw [extend_length P hn F.valid e a pos hr] at ge
      exact .inr (.inl ⟨_,_,rfl,rfl,ge⟩)
    · cases heq
  · rename_i k heq
    split at heq
    · cases heq
    · cases heq
    · cases heq
    · rename_i a pos hr
      cases heq
      let K := (Classical.choice (WindowNamedFront.named_of_route hn F.ledger g
        P.cert P.target e a pos F.valid F.quiet P.owned.contained hr))
      have hmem : a∈P.cert := (WindowNamedFront.death_inv F.ledger g P.cert P.target e a pos hr).2.2.1
      exact .inr (.inr ⟨K.val.entry hn,rfl,by change K.val.victim∈P.cert; rw [K.property.1]; exact hmem⟩)

#print axioms extend_length
#print axioms edge_handoff

/-- Inspect exactly the first terminal mark of an ordinary timed slot.
The handoff refers to the actual joined cursor on the consumed word;
no assertion is made about a later padded endpoint. -/
theorem word_handoff {p c n} {x : Config p c n} {g}
    (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (F : Front x g) (P : Progress F.ledger g) (hm : F.mode=.owned P)
    (a : Fin n) (ht : P.target=some a) (w : Word n)
    (h : FirstExit (fun u => (runMarks (next hp hc hn)
      (Slot.active F P hm rfl ht) u).done) w) :
    Handoff P.cert (runMarks (joinedNext (front hn (WindowOwnership.decide hp hc hn)))
      (.inl F) w) := by
  let seed := Slot.active F P hm rfl ht
  rw [←show seed.physical=.inl F from rfl,←run_physical hp hc hn seed w]
  cases hrev : w.reverse with
  | nil =>
    have E := congrArg List.reverse hrev
    have eq : w=[] := by simpa using E
    subst w
    exact h.2.elim
  | cons e v =>
    have E := congrArg List.reverse hrev
    have eq : w=wordNext v.reverse e := by simpa [wordNext] using E
    subst w
    let u := v.reverse
    let y := runMarks (next hp hc hn) seed u
    have nb : ¬y.done := ((clean_child _ u e).mp h.1).2
    have nd : (next hp hc hn y e).done := by
      have B := h.2
      change (runMarks (next hp hc hn) seed (u++[e])).done at B
      rw [runMarks_append] at B
      exact B
    change Handoff P.cert (runMarks (next hp hc hn) seed (u++[e])).physical
    rw [runMarks_append]
    change Handoff P.cert (next hp hc hn y e).physical
    cases hY : y with
    | stop q => exact (nb (by rw [hY]; trivial)).elim
    | active L R hM hC hA =>
      have nonkeep : route g R.cert R.target L.ledger e≠.keep := by
        intro hr
        rw [hY] at nd
        simp [next,Slot.done,hr] at nd
      rw [next_physical]
      change Handoff P.cert (joinedNext (front hn (WindowOwnership.decide hp hc hn)) (.inl L) e)
      rw [←hC]
      exact edge_handoff hp hc hn L R hM e nonkeep

#print axioms word_handoff
end L4.WindowOrdinaryHandoff
