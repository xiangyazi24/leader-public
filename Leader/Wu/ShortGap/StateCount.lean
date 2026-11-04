import Leader.Wu.ShortGap.CaptureCommitRows

namespace ShortGapStateCount

open ShortGapLiteralGapRows
open ShortGapCaptureReservation
open ShortGapCaptureCommitRows

private def enumProd {α β : Type} (xs : List α) (ys : List β) :
    List (α × β) :=
  xs.flatMap (fun x => ys.map (fun y => (x, y)))

private theorem enumProd_mem_of_mem
    {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β}
    (hx : x ∈ xs) (hy : y ∈ ys) :
    (x, y) ∈ enumProd xs ys := by
  unfold enumProd
  apply List.mem_flatMap.mpr
  refine ⟨x, hx, ?_⟩
  apply List.mem_map.mpr
  exact ⟨y, hy, rfl⟩

private theorem nodup_map_of_injective
    {α β : Type} (f : α → β) (hf : Function.Injective f)
    {xs : List α} (hxs : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      rw [List.nodup_cons] at hxs
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro hm
        rcases List.mem_map.mp hm with ⟨b, hb, hba⟩
        have hEq : b = a := hf hba
        subst b
        exact hxs.1 hb
      · exact ih hxs.2

private theorem nodup_append_of_disjoint {α : Type} :
    ∀ (xs ys : List α),
      xs.Nodup →
      ys.Nodup →
      (∀ z, z ∈ xs → z ∈ ys → False) →
      (xs ++ ys).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro ys hxs hys hdisj
      simpa using hys
  | cons a xs ih =>
      intro ys hxs hys hdisj
      rw [List.nodup_cons] at hxs
      simp only [List.cons_append, List.nodup_cons]
      constructor
      · intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hxs.1 hm
        · exact hdisj a (by simp) hm
      · apply ih ys hxs.2 hys
        intro z hz hzy
        exact hdisj z (by simp [hz]) hzy

private theorem enumProd_nodup {α β : Type} :
    ∀ (xs : List α) (ys : List β),
      xs.Nodup → ys.Nodup → (enumProd xs ys).Nodup := by
  intro xs
  induction xs with
  | nil =>
      intro ys hxs hys
      simp [enumProd]
  | cons x xs ih =>
      intro ys hxs hys
      rw [List.nodup_cons] at hxs
      change (ys.map (fun y => (x, y)) ++ enumProd xs ys).Nodup
      have hblock : (ys.map (fun y => (x, y))).Nodup := by
        apply nodup_map_of_injective (fun y : β => (x, y))
        · intro y1 y2 h
          exact congrArg Prod.snd h
        · exact hys
      have htail : (enumProd xs ys).Nodup :=
        ih ys hxs.2 hys
      apply nodup_append_of_disjoint _ _ hblock htail
      intro z hzBlock hzTail
      rcases List.mem_map.mp hzBlock with ⟨y, hy, hBlock⟩
      unfold enumProd at hzTail
      rcases List.mem_flatMap.mp hzTail with ⟨x', hx', hzMap⟩
      rcases List.mem_map.mp hzMap with ⟨y', hy', hTail⟩
      have hPair : (x', y') = (x, y) := hTail.trans hBlock.symm
      have hxx : x' = x := congrArg Prod.fst hPair
      apply hxs.1
      simpa [hxx] using hx'

private theorem enumProd_length {α β : Type} :
    ∀ (xs : List α) (ys : List β),
      (enumProd xs ys).length = xs.length * ys.length := by
  intro xs
  induction xs with
  | nil =>
      intro ys
      simp [enumProd]
  | cons x xs ih =>
      intro ys
      change (ys.map (fun y => (x, y)) ++ enumProd xs ys).length =
        (x :: xs).length * ys.length
      rw [List.length_append, List.length_map, ih ys]
      simp [Nat.succ_mul, Nat.add_comm]

/-! ## Literal gap-row types -/

def allChoice : List Choice :=
  [Choice.race, Choice.out1, Choice.in0]

theorem allChoice_complete : ∀ x, x ∈ allChoice := by
  intro x
  cases x <;> simp [allChoice]

theorem allChoice_nodup : allChoice.Nodup := by
  decide

theorem allChoice_length : allChoice.length = 3 := rfl


def allCwPort : List CwPort :=
  [CwPort.toSend, CwPort.waiting, CwPort.heldDenial,
    CwPort.heldCandidate]

theorem allCwPort_complete : ∀ x, x ∈ allCwPort := by
  intro x
  cases x <;> simp [allCwPort]

theorem allCwPort_nodup : allCwPort.Nodup := by
  decide

theorem allCwPort_length : allCwPort.length = 4 := rfl


def allCcwPort : List CcwPort :=
  [CcwPort.free, CcwPort.heldDenial, CcwPort.heldCandidate]

theorem allCcwPort_complete : ∀ x, x ∈ allCcwPort := by
  intro x
  cases x <;> simp [allCcwPort]

theorem allCcwPort_nodup : allCcwPort.Nodup := by
  decide

theorem allCcwPort_length : allCcwPort.length = 3 := rfl


def allSlot : List Slot :=
  [Slot.empty] ++ allChoice.map Slot.decl ++ allChoice.map Slot.reply

theorem allSlot_complete : ∀ x, x ∈ allSlot := by
  intro x
  cases x with
  | empty => simp [allSlot]
  | decl c =>
      have hc := allChoice_complete c
      simp [allSlot, hc]
  | reply c =>
      have hc := allChoice_complete c
      simp [allSlot, hc]

theorem allSlot_nodup : allSlot.Nodup := by
  decide

theorem allSlot_length : allSlot.length = 7 := by
  simp [allSlot, allChoice_length]


private def allAgentRootArgs : List (Choice × (CwPort × CcwPort)) :=
  enumProd allChoice (enumProd allCwPort allCcwPort)

private theorem allAgentRootArgs_nodup : allAgentRootArgs.Nodup := by
  have hPorts : (enumProd allCwPort allCcwPort).Nodup :=
    enumProd_nodup allCwPort allCcwPort
      allCwPort_nodup allCcwPort_nodup
  unfold allAgentRootArgs
  exact enumProd_nodup allChoice (enumProd allCwPort allCcwPort)
    allChoice_nodup hPorts

private theorem allAgentRootArgs_length : allAgentRootArgs.length = 36 := by
  simp [allAgentRootArgs, enumProd_length,
    allChoice_length, allCwPort_length, allCcwPort_length]

private def mkAgentRoot (p : Choice × (CwPort × CcwPort)) : Agent :=
  Agent.root p.1 p.2.1 p.2.2

private theorem mkAgentRoot_injective : Function.Injective mkAgentRoot := by
  intro x y h
  rcases x with ⟨xch, ⟨xcw, xccw⟩⟩
  rcases y with ⟨ych, ⟨ycw, yccw⟩⟩
  injection h with hch hcw hccw
  cases hch
  cases hcw
  cases hccw
  rfl

private theorem agentInterior_injective : Function.Injective Agent.interior := by
  intro x y h
  injection h with hxy

def allAgent : List Agent :=
  allAgentRootArgs.map mkAgentRoot ++ allSlot.map Agent.interior

theorem allAgent_complete : ∀ x, x ∈ allAgent := by
  intro x
  cases x with
  | root ch cw ccw =>
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      refine ⟨(ch, (cw, ccw)), ?_, rfl⟩
      exact enumProd_mem_of_mem (allChoice_complete ch)
        (enumProd_mem_of_mem (allCwPort_complete cw)
          (allCcwPort_complete ccw))
  | interior slot =>
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      exact ⟨slot, allSlot_complete slot, rfl⟩

theorem allAgent_nodup : allAgent.Nodup := by
  have hRoot : (allAgentRootArgs.map mkAgentRoot).Nodup :=
    nodup_map_of_injective mkAgentRoot mkAgentRoot_injective
      allAgentRootArgs_nodup
  have hInterior : (allSlot.map Agent.interior).Nodup :=
    nodup_map_of_injective Agent.interior agentInterior_injective allSlot_nodup
  unfold allAgent
  apply nodup_append_of_disjoint _ _ hRoot hInterior
  intro z hzRoot hzInterior
  rcases List.mem_map.mp hzRoot with ⟨p, hp, hpz⟩
  rcases List.mem_map.mp hzInterior with ⟨slot, hs, hsz⟩
  have hbad : mkAgentRoot p = Agent.interior slot := hpz.trans hsz.symm
  rcases p with ⟨ch, ⟨cw, ccw⟩⟩
  change Agent.root ch cw ccw = Agent.interior slot at hbad
  cases hbad

theorem allAgent_length : allAgent.length = 43 := by
  simp [allAgent, allAgentRootArgs_length, allSlot_length]

/-! ## Capture-reservation types -/

def allOutControl : List OutControl :=
  [OutControl.home, OutControl.proposal, OutControl.finalReady]

theorem allOutControl_complete : ∀ x, x ∈ allOutControl := by
  intro x
  cases x <;> simp [allOutControl]

theorem allOutControl_nodup : allOutControl.Nodup := by
  decide

theorem allOutControl_length : allOutControl.length = 3 := rfl


def allInControl : List InControl :=
  [InControl.open, InControl.reserved, InControl.accepted]

theorem allInControl_complete : ∀ x, x ∈ allInControl := by
  intro x
  cases x <;> simp [allInControl]

theorem allInControl_nodup : allInControl.Nodup := by
  decide

theorem allInControl_length : allInControl.length = 3 := rfl


def allCaptureMessage : List CaptureMessage :=
  [CaptureMessage.proposal, CaptureMessage.finalBack]

theorem allCaptureMessage_complete : ∀ x, x ∈ allCaptureMessage := by
  intro x
  cases x <;> simp [allCaptureMessage]

theorem allCaptureMessage_nodup : allCaptureMessage.Nodup := by
  decide

theorem allCaptureMessage_length : allCaptureMessage.length = 2 := rfl


def allWire : List Wire :=
  allSlot.map Wire.selection ++ allCaptureMessage.map Wire.capture

private theorem wireSelection_injective : Function.Injective Wire.selection := by
  intro x y h
  injection h with hxy

private theorem wireCapture_injective : Function.Injective Wire.capture := by
  intro x y h
  injection h with hxy

theorem allWire_complete : ∀ x, x ∈ allWire := by
  intro x
  cases x with
  | selection slot =>
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      exact ⟨slot, allSlot_complete slot, rfl⟩
  | capture msg =>
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      exact ⟨msg, allCaptureMessage_complete msg, rfl⟩

theorem allWire_nodup : allWire.Nodup := by
  have hSelection : (allSlot.map Wire.selection).Nodup :=
    nodup_map_of_injective Wire.selection wireSelection_injective allSlot_nodup
  have hCapture : (allCaptureMessage.map Wire.capture).Nodup :=
    nodup_map_of_injective Wire.capture wireCapture_injective
      allCaptureMessage_nodup
  unfold allWire
  apply nodup_append_of_disjoint _ _ hSelection hCapture
  intro z hzSelection hzCapture
  rcases List.mem_map.mp hzSelection with ⟨slot, hs, hsz⟩
  rcases List.mem_map.mp hzCapture with ⟨msg, hm, hmz⟩
  have hbad : Wire.selection slot = Wire.capture msg := hsz.trans hmz.symm
  cases hbad

theorem allWire_length : allWire.length = 9 := by
  simp [allWire, allSlot_length, allCaptureMessage_length]


private def allNodeRootArgs :
    List (Choice × (CwPort × (CcwPort × (OutControl × InControl)))) :=
  enumProd allChoice
    (enumProd allCwPort
      (enumProd allCcwPort
        (enumProd allOutControl allInControl)))

private theorem allNodeRootArgs_nodup : allNodeRootArgs.Nodup := by
  have hOutIn : (enumProd allOutControl allInControl).Nodup :=
    enumProd_nodup allOutControl allInControl
      allOutControl_nodup allInControl_nodup
  have hCcwRest :
      (enumProd allCcwPort (enumProd allOutControl allInControl)).Nodup :=
    enumProd_nodup allCcwPort (enumProd allOutControl allInControl)
      allCcwPort_nodup hOutIn
  have hCwRest :
      (enumProd allCwPort
        (enumProd allCcwPort
          (enumProd allOutControl allInControl))).Nodup :=
    enumProd_nodup allCwPort
      (enumProd allCcwPort (enumProd allOutControl allInControl))
      allCwPort_nodup hCcwRest
  unfold allNodeRootArgs
  exact enumProd_nodup allChoice
    (enumProd allCwPort
      (enumProd allCcwPort
        (enumProd allOutControl allInControl)))
    allChoice_nodup hCwRest

private theorem allNodeRootArgs_length : allNodeRootArgs.length = 324 := by
  simp [allNodeRootArgs, enumProd_length,
    allChoice_length, allCwPort_length, allCcwPort_length,
    allOutControl_length, allInControl_length]

private def mkNodeRoot
    (p : Choice × (CwPort × (CcwPort × (OutControl × InControl)))) : Node :=
  Node.root p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

private theorem mkNodeRoot_injective : Function.Injective mkNodeRoot := by
  intro x y h
  rcases x with ⟨xch, ⟨xcw, ⟨xccw, ⟨xout, xin⟩⟩⟩⟩
  rcases y with ⟨ych, ⟨ycw, ⟨yccw, ⟨yout, yin⟩⟩⟩⟩
  injection h with hch hcw hccw hout hin
  cases hch
  cases hcw
  cases hccw
  cases hout
  cases hin
  rfl

private theorem nodeInterior_injective : Function.Injective Node.interior := by
  intro x y h
  injection h with hxy

def allNode : List Node :=
  allNodeRootArgs.map mkNodeRoot ++ allWire.map Node.interior

theorem allNode_complete : ∀ x, x ∈ allNode := by
  intro x
  cases x with
  | root ch cw ccw outgoing incoming =>
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      refine ⟨(ch, (cw, (ccw, (outgoing, incoming)))), ?_, rfl⟩
      exact enumProd_mem_of_mem (allChoice_complete ch)
        (enumProd_mem_of_mem (allCwPort_complete cw)
          (enumProd_mem_of_mem (allCcwPort_complete ccw)
            (enumProd_mem_of_mem (allOutControl_complete outgoing)
              (allInControl_complete incoming))))
  | interior wire =>
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      exact ⟨wire, allWire_complete wire, rfl⟩

theorem allNode_nodup : allNode.Nodup := by
  have hRoot : (allNodeRootArgs.map mkNodeRoot).Nodup :=
    nodup_map_of_injective mkNodeRoot mkNodeRoot_injective
      allNodeRootArgs_nodup
  have hInterior : (allWire.map Node.interior).Nodup :=
    nodup_map_of_injective Node.interior nodeInterior_injective allWire_nodup
  unfold allNode
  apply nodup_append_of_disjoint _ _ hRoot hInterior
  intro z hzRoot hzInterior
  rcases List.mem_map.mp hzRoot with ⟨p, hp, hpz⟩
  rcases List.mem_map.mp hzInterior with ⟨wire, hw, hwz⟩
  have hbad : mkNodeRoot p = Node.interior wire := hpz.trans hwz.symm
  rcases p with ⟨ch, ⟨cw, ⟨ccw, ⟨outgoing, incoming⟩⟩⟩⟩
  change Node.root ch cw ccw outgoing incoming = Node.interior wire at hbad
  cases hbad

theorem allNode_length : allNode.length = 333 := by
  simp [allNode, allNodeRootArgs_length, allWire_length]

/-! ## Capture-commit types -/

def allCommitCtl : List CommitCtl :=
  [CommitCtl.capturing, CommitCtl.protectedFinal, CommitCtl.committing,
    CommitCtl.committedReceived, CommitCtl.clean]

theorem allCommitCtl_complete : ∀ x, x ∈ allCommitCtl := by
  intro x
  cases x <;> simp [allCommitCtl]

theorem allCommitCtl_nodup : allCommitCtl.Nodup := by
  decide

theorem allCommitCtl_length : allCommitCtl.length = 5 := rfl


def allCommitIn : List CommitIn :=
  [CommitIn.unreserved, CommitIn.reserved, CommitIn.committed, CommitIn.clean]

theorem allCommitIn_complete : ∀ x, x ∈ allCommitIn := by
  intro x
  cases x <;> simp [allCommitIn]

theorem allCommitIn_nodup : allCommitIn.Nodup := by
  decide

theorem allCommitIn_length : allCommitIn.length = 4 := rfl


def allCommitCarrier : List CommitCarrier :=
  [CommitCarrier.none, CommitCarrier.commit, CommitCarrier.committedBack]

theorem allCommitCarrier_complete : ∀ x, x ∈ allCommitCarrier := by
  intro x
  cases x <;> simp [allCommitCarrier]

theorem allCommitCarrier_nodup : allCommitCarrier.Nodup := by
  decide

theorem allCommitCarrier_length : allCommitCarrier.length = 3 := rfl


private def allBool : List Bool := [false, true]

private theorem allBool_complete : ∀ x, x ∈ allBool := by
  intro x
  cases x <;> simp [allBool]

private theorem allBool_nodup : allBool.Nodup := by
  decide

private theorem allBool_length : allBool.length = 2 := rfl

private def allCNodeArgs :
    List (Node × (Bool × (CommitCtl × (CommitIn × CommitCarrier)))) :=
  enumProd allNode
    (enumProd allBool
      (enumProd allCommitCtl
        (enumProd allCommitIn allCommitCarrier)))

private theorem allCNodeArgs_length : allCNodeArgs.length = 39960 := by
  simp [allCNodeArgs, enumProd_length,
    allNode_length, allBool_length, allCommitCtl_length,
    allCommitIn_length, allCommitCarrier_length]

private def mkCNode
    (p : Node × (Bool × (CommitCtl × (CommitIn × CommitCarrier)))) : CNode :=
  { raw := p.1
    leader := p.2.1
    outgoing := p.2.2.1
    incoming := p.2.2.2.1
    carrier := p.2.2.2.2 }

private theorem mkCNode_injective : Function.Injective mkCNode := by
  intro x y h
  rcases x with ⟨xr, ⟨xb, ⟨xo, ⟨xi, xc⟩⟩⟩⟩
  rcases y with ⟨yr, ⟨yb, ⟨yo, ⟨yi, yc⟩⟩⟩⟩
  have hr : xr = yr := congrArg CNode.raw h
  have hb : xb = yb := congrArg CNode.leader h
  have ho : xo = yo := congrArg CNode.outgoing h
  have hi : xi = yi := congrArg CNode.incoming h
  have hc : xc = yc := congrArg CNode.carrier h
  cases hr
  cases hb
  cases ho
  cases hi
  cases hc
  rfl

/--
`allCNode` has exactly 39,960 syntactic control states, slightly below the
nominal “about 41k” estimate.  These are TYPE cardinalities: protocol-reachable
states are fewer because the transition invariants exclude many combinations.
None of `Choice`, `CwPort`, `CcwPort`, `Slot`, `Agent`, `OutControl`,
`InControl`, `CaptureMessage`, `Wire`, `Node`, `CommitCtl`, `CommitIn`,
`CommitCarrier`, or `CNode` mentions `n`, `m`, or `h`, so this cardinality is
independent of the ring size, number of roots, and short-gap bound.
-/
def allCNode : List CNode :=
  allCNodeArgs.map mkCNode

theorem allCNode_complete : ∀ x, x ∈ allCNode := by
  intro x
  rcases x with ⟨raw, leader, outgoing, incoming, carrier⟩
  apply List.mem_map.mpr
  refine ⟨(raw, (leader, (outgoing, (incoming, carrier)))), ?_, rfl⟩
  exact enumProd_mem_of_mem (allNode_complete raw)
    (enumProd_mem_of_mem (allBool_complete leader)
      (enumProd_mem_of_mem (allCommitCtl_complete outgoing)
        (enumProd_mem_of_mem (allCommitIn_complete incoming)
          (allCommitCarrier_complete carrier))))

theorem allCNode_nodup : allCNode.Nodup := by
  have hInCarrier :
      (enumProd allCommitIn allCommitCarrier).Nodup :=
    enumProd_nodup allCommitIn allCommitCarrier
      allCommitIn_nodup allCommitCarrier_nodup
  have hCtlRest :
      (enumProd allCommitCtl
        (enumProd allCommitIn allCommitCarrier)).Nodup :=
    enumProd_nodup allCommitCtl
      (enumProd allCommitIn allCommitCarrier)
      allCommitCtl_nodup hInCarrier
  have hBoolRest :
      (enumProd allBool
        (enumProd allCommitCtl
          (enumProd allCommitIn allCommitCarrier))).Nodup :=
    enumProd_nodup allBool
      (enumProd allCommitCtl
        (enumProd allCommitIn allCommitCarrier))
      allBool_nodup hCtlRest
  have hArgs : allCNodeArgs.Nodup :=
    enumProd_nodup allNode
      (enumProd allBool
        (enumProd allCommitCtl
          (enumProd allCommitIn allCommitCarrier)))
      allNode_nodup hBoolRest
  unfold allCNode
  exact nodup_map_of_injective mkCNode mkCNode_injective hArgs

theorem allCNode_length : allCNode.length = 39960 := by
  simp [allCNode, allCNodeArgs_length]

theorem cnode_card_le : allCNode.length ≤ 65536 := by
  rw [allCNode_length]
  decide

#print axioms allChoice_length
#print axioms allCwPort_length
#print axioms allCcwPort_length
#print axioms allSlot_length
#print axioms allAgent_length
#print axioms allOutControl_length
#print axioms allInControl_length
#print axioms allCaptureMessage_length
#print axioms allWire_length
#print axioms allNode_length
#print axioms allCommitCtl_length
#print axioms allCommitIn_length
#print axioms allCommitCarrier_length
#print axioms allCNode_length
#print axioms cnode_card_le

end ShortGapStateCount
