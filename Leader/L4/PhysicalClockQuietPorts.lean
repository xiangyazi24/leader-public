import Leader.L4.PhysicalClockPortTransfer
import Leader.L4.Height.QuietBridge

namespace L4.PhysicalClockQuietPorts
open BStarH6WordChart BStarAcquireAnchors
open PhysicalClockPortBase PhysicalClockPortIndex
open L4.Height L4.Height.Recover L4.Compiler.Native

def TickAdjacent (M a b : Nat) : Prop :=
  a=b ∨ successor M a=b ∨ successor M b=a

private theorem successor_edge_of_legitimate {M : Nat} {a b : NativeRecord}
    (ha : a.tick < M) (hb : b.tick < M) (h : StageThree.LegitimateEdge M a b) :
    b.tick = a.tick ∨ b.tick = successor M a.tick ∨ a.tick = successor M b.tick := by
  rcases h with h | h | h | ⟨ha', hb'⟩ | ⟨hb', ha'⟩
  · exact Or.inl h.symm
  · have ht : a.tick ≠ M - 1 := by omega
    exact Or.inr (Or.inl (by simpa [successor, ht] using h.symm))
  · have ht : b.tick ≠ M - 1 := by omega
    exact Or.inr (Or.inr (by simpa [successor, ht] using h.symm))
  · exact Or.inr (Or.inl (by simp [successor, ha', hb']))
  · exact Or.inr (Or.inr (by simp [successor, hb', ha']))


/-- The accepted quiet records give the physical biased-tick relation at
every header and port, including wrap and aliases. `read` is the old
record reader (no logical update or wall-time transfer is used). -/
theorem quiet_ports {n : Nat} {h : Fin n→Bool} (hh : ∃ i,h i=true)
    (M : Nat) (read : Header h → NativeRecord)
    (clean : ∀ i, (read (atIndex hh i)).err=false)
    (quiet : StageThree.Quiet M (total_pos h hh) (fun i=>read (atIndex hh i)))
    (well : StageTwo.WellFormed M (fun i=>read (atIndex hh i))) :
    (∀ i,(read i).err=false) ∧
      ∀ i q,TickAdjacent M (read i).tick (read (neighborHeader hh i q)).tick := by
  constructor
  · intro i
    simpa only [atIndex_index] using clean (index hh i)
  · have edge := StageThree.legitimate_of_correct_quiet (total_pos h hh)
      (fun i=>read (atIndex hh i)) clean quiet
    apply PhysicalClockPortTransfer.of_edges hh (fun i=>(read i).tick) (TickAdjacent M)
    · intro a; exact .inl rfl
    · intro a b H
      rcases H with H|H|H
      · exact .inl H.symm
      · exact .inr (.inr H)
      · exact .inr (.inl H)
    · intro i
      rcases successor_edge_of_legitimate (well i).1 (well (next i)).1 (edge i) with H|H|H
      · exact .inl H.symm
      · exact .inr (.inl H.symm)
      · exact .inr (.inr H.symm)

#print axioms quiet_ports
end L4.PhysicalClockQuietPorts
