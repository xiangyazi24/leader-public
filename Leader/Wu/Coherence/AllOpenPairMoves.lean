import Std
import Leader.Wu.Coherence.Controller
import Leader.Wu.Coherence.FairCycleRingSix

set_option autoImplicit false
set_option Elab.async false

namespace ZZAllOpenPair

open R2CoherenceV31

private theorem h3 : 0 < 3 := by decide
private theorem h23 : 2 ≤ 3 := by decide

private def literalFollower (lab : Fin 3) : R2.Cell 3 3 48 :=
  let seed := WriterProducerRegression.clean h3 (fun _ => false) lab
  let b := seed.base.core.core
  let b' : BoundedAgentState 3 3 :=
    { b with
      leader := false
      shield := false
      gen_ws := false
      label := lab
      state := .none
      path := .bot
      bit := false
      path2 := none
      path3 := none
      path4 := none
      path5 := none
      p := false
      p_carry := false
      reset_cmd := false
      echo := false
      write_state := .none
      write := .none
      b_carry := false }
  ⟨⟨⟨b', false⟩, 48⟩, 0⟩

/-- The all-open cell with physical label k. -/
private def openCell (k : Fin 3) : Cell 3 3 48 :=
  ⟨literalFollower k, ⟨.open, .none⟩⟩

/-- The successor-labelled all-open pair is NOT fixed: kernel evaluation of the
equality returns false (an earlier trace claim is corrected here). -/
theorem rowV3_open_01_ne :
    rowV3 h3 (by decide : 0 < 2) h23 (openCell 0) (openCell 1) ≠
      (openCell 0, openCell 1) := by
  decide +kernel

/-- The wrap-around all-open pair is NOT fixed either. -/
theorem rowV3_open_20_ne :
    rowV3 h3 (by decide : 0 < 2) h23 (openCell 2) (openCell 0) ≠
      (openCell 2, openCell 0) := by
  decide +kernel

#print axioms rowV3_open_01_ne
#print axioms rowV3_open_20_ne

end ZZAllOpenPair
