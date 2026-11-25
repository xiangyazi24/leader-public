import Leader.L4.ReportOwnerResetDrain

namespace L4.ReportOwnerDoorProjection
open AllSizeProtocol PhysicalCustody ReportResetRawHooks ReportOwnerResetDrain
open ReportByteRows ReportRawProjection ReportResetBarrier ShortResetCycle ShortResetChart

/-- Exact selected sheet's final joined source PC and root K0 on the
physical chart door. No source category is assumed and the other lane
may execute unrelated work on the same physical mark. -/
theorem raw_door_final {s n : Nat} {h : Fin n→Bool}
    (sheet : Sheet) (C : Chart h) (x : Raw s n)
    (N : 1<n) (mask : ∀ i, lower sheet (oldHeaders (rows s) (x i))=h i) :
    let p := params sheet s
    let v := selectBytes sheet (x C.root)
    let y := selectBytes sheet (rawNext s x (door C) C.root)
    let action := source p v (publicationToken p true v 0)
    controlWork p y = controlWork p ((liftSourcePatch p action.1).apply v) ∧
      resetTokenRead p y 0 =
        match action.2 with
        | none => prelaunchDoorNormWire p v
        | some t => resetTokenWire p t := by
  let p := params sheet s
  let e := door C
  let u := selectBytes sheet (x e)
  let v := selectBytes sheet (x C.root)
  have R : rightNeighbor e=C.root := RearTrace.right_predecessor C.root
  have H := raw_token_control sheet x e (edge_sep N e)
  dsimp only at H
  rw [mask e,mask (rightNeighbor e),R,C.rootHeader] at H
  exact ⟨(congrArg (fun z=>z.2.2) H).trans (prelaunch_door_final_control p (h e) u v),
    (congrArg (fun z=>z.2.1 0) H).trans (prelaunch_door_final_wire p (h e) u v)⟩

#print axioms raw_door_final
end L4.ReportOwnerDoorProjection
