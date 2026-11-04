import Leader.Wu.ShortGap.UnifiedGuards


open ShortGapSpliceCommitCorrected
open ShortGapSpliceDemotion
open ShortGapUnifiedNode
open ShortGapUnifiedGuards


namespace ShortGapUnifiedDispatch


set_option autoImplicit false


/-- The demotion guard reads only fields that `toSNode` preserves, so the
legacy equivalence holds at every unified node, not merely embedded ones. -/
theorem uDemotionEnabled_iff_toSNode (a b : UNode) :
    UDemotionEnabled a b ↔ DemotionEnabled (toSNode a) (toSNode b) := by
  cases a
  cases b
  rfl

/-- Unified dispatcher tag: all old Corrected rules are retained as one branch,
with demotion as the only genuinely new WithDemotion rule. -/
inductive URule where
  | corrected (k : SRuleCorrected)
  | demotion
  deriving DecidableEq


/-- Route through the legacy decidable dispatcher.  The only WithDemotion priority
extension is demotion; otherwise use the already checked Corrected selector. -/
def uRule (a b : UNode) : URule :=
  if DemotionEnabled (toSNode a) (toSNode b) then
    .demotion
  else
    .corrected (spliceRuleCorrected (toSNode a) (toSNode b))


/-- Unified physical row.  Re-embedding through `ofSNode` deliberately writes
no traffic metadata. -/
def uRow (a b : UNode) : UNode × UNode :=
  let r := spliceRowWithDemotion (toSNode a) (toSNode b)
  (ofSNode r.1, ofSNode r.2)


/-- Definitional expansion of the unified row. -/
theorem uRow_eq (a b : UNode) :
    uRow a b =
      (ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).1,
       ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).2) := by
  rfl


/-- Enabled unified demotion agrees simultaneously with the rule tag and the
WithDemotion demotion row.  The first output is the traffic-cleared embedding of the
legacy left input. -/
theorem uRule_demotion (a b : UNode) (h : UDemotionEnabled a b) :
    uRule a b = .demotion ∧
      uRow a b =
        (ofSNode (toSNode a), ofSNode (demote (toSNode b))) := by
  have hd : DemotionEnabled (toSNode a) (toSNode b) :=
    (uDemotionEnabled_iff_toSNode a b).1 h
  constructor
  · unfold uRule
    rw [if_pos hd]
  · have hr := spliceRowWithDemotion_demotes (toSNode a) (toSNode b) hd
    calc
      uRow a b =
          (ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).1,
           ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).2) :=
        uRow_eq a b
      _ = (ofSNode (toSNode a), ofSNode (demote (toSNode b))) := by
        rw [hr]


/-- Off demotion, the unified rule tag is exactly the old Corrected selector. -/
theorem uRule_tag_v2_of_not_demotion
    (a b : UNode) (h : ¬ UDemotionEnabled a b) :
    uRule a b = .corrected (spliceRuleCorrected (toSNode a) (toSNode b)) := by
  have hd : ¬ DemotionEnabled (toSNode a) (toSNode b) := by
    intro hD
    apply h
    exact (uDemotionEnabled_iff_toSNode a b).2 hD
  unfold uRule
  rw [if_neg hd]


/-- Off demotion, the unified row is literally the old Corrected row, re-embedded
with empty traffic on both outputs. -/
theorem uRule_v2_of_not_demotion
    (a b : UNode) (h : ¬ UDemotionEnabled a b) :
    uRow a b =
      (ofSNode (spliceRowCorrected (toSNode a) (toSNode b)).1,
       ofSNode (spliceRowCorrected (toSNode a) (toSNode b)).2) := by
  have hd : ¬ DemotionEnabled (toSNode a) (toSNode b) := by
    intro hD
    apply h
    exact (uDemotionEnabled_iff_toSNode a b).2 hD
  have hr :=
    spliceRowWithDemotion_eq_of_not_demotion (toSNode a) (toSNode b) hd
  calc
    uRow a b =
        (ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).1,
         ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).2) :=
      uRow_eq a b
    _ =
        (ofSNode (spliceRowCorrected (toSNode a) (toSNode b)).1,
         ofSNode (spliceRowCorrected (toSNode a) (toSNode b)).2) := by
      rw [hr]


/-- This dispatcher layer writes no traffic: both physical outputs are created
through `ofSNode`, whose traffic field is `.empty`. -/
theorem uRow_traffic_empty (a b : UNode) :
    (uRow a b).1.traffic = .empty ∧
      (uRow a b).2.traffic = .empty := by
  change
    (ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).1).traffic = .empty ∧
      (ofSNode (spliceRowWithDemotion (toSNode a) (toSNode b)).2).traffic = .empty
  generalize hr : spliceRowWithDemotion (toSNode a) (toSNode b) = r
  cases r with
  | mk x y =>
      cases x
      cases y
      exact ⟨rfl, rfl⟩


end ShortGapUnifiedDispatch


#print axioms ShortGapUnifiedDispatch.uDemotionEnabled_iff_toSNode
#print axioms ShortGapUnifiedDispatch.uRow_eq
#print axioms ShortGapUnifiedDispatch.uRule_demotion
#print axioms ShortGapUnifiedDispatch.uRule_tag_v2_of_not_demotion
#print axioms ShortGapUnifiedDispatch.uRule_v2_of_not_demotion
#print axioms ShortGapUnifiedDispatch.uRow_traffic_empty
