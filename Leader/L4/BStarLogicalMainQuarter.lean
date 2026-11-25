import Leader.L4.Height.LogicalVec
import Leader.L4.BStarAlignedLogicalRounds
import Leader.L4.BStarCubePadding

namespace L4.BStarLogicalMainQuarter
open BStarH6WordChart BStarAcquireAnchors BStarNativePortGeometry BStarCycleGeometry
open BStarAlignedLogicalRounds BStarWarmupEventQuarter BStarWarmupReceiptChoice BStarWarmupArrival
open BStarWarmupQuarter BStarWarmupKeys BStarMainLogicalProjection BStarCubePadding
open L4.Compiler.Native L4.Height

variable {n : Nat} {h : Fin n→Bool}

/-- Convert the local public round-major address to the accepted
`LogicalVec.vecRounds` block convention without duplicating its logic. -/
theorem vecRounds_index {Q m : Nat} (a : Bits (Q*m)) :
    vecRounds Q m a=List.ofFn (fun j : Fin Q=>fun i : Fin m=>a (roundIndex j i)) := rfl

/-- The exact main-coordinate cube has the accepted singleton-failure
quarter bound for every bounded logical opening slice. All extra keys
are counted as free, and no physical coverage of them is required. -/
theorem main_bad_list (hh : ∃ i,h i=true)
    (r M : Nat) (period : 32∣M/2)
    (reserve : Key n→Option Bool) (lo opening cap : Nat) (align : opening%32=0)
    (C : cap=opening+32*(2^19*total h)) (height : total h<heightMod r)
    (f : Fin ((2^19*total h)*total h)→Fin (keys reserve opening cap).length)
    (inj : Function.Injective f)
    (key : ∀ j, sumCoordinate reserve lo opening cap
      (logicalKey (total_pos h hh) (fun i=>(atIndex hh i).val) opening j) =
      some ((f j).natAdd (keys reserve lo opening).length))
    (s : Header h→Snapshot)
    (bounded : Bounded (heightMod r) (fun i=>s (atIndex hh i))) :
    ∃ bad : List (Bits (keys reserve opening cap).length), bad.Nodup ∧
      4*bad.length≤2^(keys reserve opening cap).length ∧
      ∀ a : Bits (jointSize reserve lo opening cap),
        main a∈bad ↔ anchorCount (total_pos h hh) (fun j=>
          evolve (neighborHeader hh) (cubeUpdate r reserve lo opening cap (joinList reserve lo opening cap a))
            opening s (cap-opening) (atIndex hh j)) ≠ 1 := by
  classical
  let m := total h
  let q := 2^19*m
  let hm := total_pos h hh
  let seed := fun i=>s (atIndex hh i)
  let shortBad := (allVectors (q*m)).filter (fun a=>
    anchorCount hm (runRounds (heightMod r) hm (vecRounds q m a) seed)≠1)
  have quarter : 4*shortBad.length≤2^(q*m) :=
    logical_quarter_vectors hm height seed bounded
  obtain ⟨bad,nd,fiber,length⟩ := lift_quarter f inj shortBad quarter
  refine ⟨bad,nd,length,?_⟩
  intro a
  rw [fiber]
  have E := aligned_rounds hh r M period reserve lo opening cap align
    (joinList reserve lo opening cap a) s q
  have P := choices_from_main hh reserve lo opening cap q a f key
  let projected : Bits (q*m) := fun j=>main a (f j)
  have V : roundBits (choices hh reserve lo opening cap (joinList reserve lo opening cap a)) opening q =
      vecRounds q m projected := P.trans (vecRounds_index projected).symm
  rw [V] at E
  have L : cap-opening=32*q := by rw [C]; show opening+32*q-opening=32*q; omega
  rw [L,E]
  simp [shortBad,mem_allVectors]
  rfl

end L4.BStarLogicalMainQuarter
