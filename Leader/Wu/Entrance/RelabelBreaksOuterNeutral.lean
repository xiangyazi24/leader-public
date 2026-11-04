import Leader.Wu.Entrance.PassiveAllOpen

set_option autoImplicit false
set_option Elab.async false

namespace Q13641Finding

open B9Host
open B9SpliceControllerR1Table
open B9SpliceControllerR1TableV6
open B9SpliceControllerR1TableV7
open B9SpliceTableHost

variable {ψ κ τ : Nat}

def OuterNeutralOld
    (u : B9SpliceTableHost.Cell ψ κ τ) : Prop :=
  B9SpliceControllerR1Table.role u.carrier = .none ∧
    u.carrier.repairPending = false ∧
    u.acquireTicket = false

 theorem ordinaryHost_right_ticket_of_relabel
    (host : HostRow (Phys ψ κ τ))
    (l r : B9SpliceTableHost.Cell ψ κ τ)
    (hrel :
      rightFollowerRelabelledV7 r.carrier
        (ordinaryRowH host l.carrier r.carrier).2 = true) :
    (ordinaryHostWriteH host l r).2.acquireTicket = true := by
  simp [ordinaryHostWriteH, hrel, setTicketV6]

 theorem physicalHold_right_ticket_of_relabel
    (host : HostRow (Phys ψ κ τ))
    (l r : B9SpliceTableHost.Cell ψ κ τ)
    (hrel :
      rightFollowerRelabelledV7 r.carrier
        (ordinaryRowH host l.carrier r.carrier).2 = true) :
    (physicalHoldH host l r).2.acquireTicket = true := by
  simp [physicalHoldH, hrel, setTicketV6]

 theorem ordinaryHost_breaks_outerNeutral_of_relabel
    (host : HostRow (Phys ψ κ τ))
    (l r : B9SpliceTableHost.Cell ψ κ τ)
    (_hl : OuterNeutralOld l) (_hr : OuterNeutralOld r)
    (hrel :
      rightFollowerRelabelledV7 r.carrier
        (ordinaryRowH host l.carrier r.carrier).2 = true) :
    ¬ OuterNeutralOld (ordinaryHostWriteH host l r).2 := by
  intro hN
  have ht := ordinaryHost_right_ticket_of_relabel host l r hrel
  have hf := hN.2.2
  rw [hf] at ht
  cases ht

 theorem physicalHold_breaks_outerNeutral_of_relabel
    (host : HostRow (Phys ψ κ τ))
    (l r : B9SpliceTableHost.Cell ψ κ τ)
    (_hl : OuterNeutralOld l) (_hr : OuterNeutralOld r)
    (hrel :
      rightFollowerRelabelledV7 r.carrier
        (ordinaryRowH host l.carrier r.carrier).2 = true) :
    ¬ OuterNeutralOld (physicalHoldH host l r).2 := by
  intro hN
  have ht := physicalHold_right_ticket_of_relabel host l r hrel
  have hf := hN.2.2
  rw [hf] at ht
  cases ht

end Q13641Finding


