import Leader.Wu.Carrier.ActiveStaging
import Leader.Wu.Carrier.ValidatorPackedCarrier

/-!
# Role-three postcommit route

This file fixes the physical namespace and the proof-side route used after a
fixed active/staging linearization.  The route has eight constant stages and
uses the current `pos : Fin h`; it stores no second position or distance.
Every service lowers an explicit remaining-route debt by exactly one, and the
largest debt is `4*h`.

The encoding occupies only role `3`, controls `27..29`, messages `0..3`, and
the existing post lease `13`.  It is disjoint from all 65 literal QMAT tags.
`taggedLinearizeRootLeader` wraps the existing atomic payload copy and changes
the selected root to this namespace in the same interaction.
-/

namespace PPLLRole3PostRoute

open PPLLFixedActiveStaging
open PPLLLinearCarrierPacking
open PPLLParallelGeometryPacked
open PPLLV2ValidatorPhysicalRefinement

set_option autoImplicit false
set_option warningAsError true

/-- Four clockwise/anticlockwise legs for a source (or no-change) commit and
four for a target commit. -/
inductive PostRoute where
  | sourceRightTwo
  | sourceRightOne
  | sourceLeftTwo
  | sourceLeftOne
  | targetRight
  | targetLeftTwo
  | targetLeftOne
  | targetFinish
  deriving DecidableEq, Repr

inductive RouteDirection where
  | right
  | left
  deriving DecidableEq, Repr

def routeDirection : PostRoute → RouteDirection
  | .sourceRightTwo | .sourceRightOne | .targetRight | .targetFinish =>
      .right
  | .sourceLeftTwo | .sourceLeftOne | .targetLeftTwo | .targetLeftOne =>
      .left

/-- Proof-side remaining service count.  The formulas are chosen so every
regular move, boundary crossing, turn, and final retirement costs one. -/
def routeDebt (h : Nat) : PostRoute → Fin h → Nat
  | .sourceRightTwo, pos => 4 * h - pos.val
  | .sourceRightOne, pos => 3 * h - pos.val
  | .sourceLeftTwo, pos => h + pos.val + 1
  | .sourceLeftOne, pos => pos.val + 1
  | .targetRight, pos => 4 * h - pos.val
  | .targetLeftTwo, pos => 2 * h + pos.val + 1
  | .targetLeftOne, pos => h + pos.val + 1
  | .targetFinish, pos => h - pos.val

abbrev RoutedHead (h : Nat) := PostRoute × Fin h

/-- One designated logical service.  `none` is atomic final retirement.
Turns use the selected boundary edge but leave the outside endpoint framed. -/
def routeService {h : Nat} (hh : 0 < h) : RoutedHead h → Option (RoutedHead h)
  | (.sourceRightTwo, pos) =>
      if hnext : pos.val + 1 < h then
        some (.sourceRightTwo, ⟨pos.val + 1, hnext⟩)
      else some (.sourceRightOne, ⟨0, hh⟩)
  | (.sourceRightOne, pos) =>
      if hnext : pos.val + 1 < h then
        some (.sourceRightOne, ⟨pos.val + 1, hnext⟩)
      else some (.sourceLeftTwo, pos)
  | (.sourceLeftTwo, pos) =>
      if hzero : pos.val = 0 then
        some (.sourceLeftOne, ⟨h - 1, by omega⟩)
      else some (.sourceLeftTwo, ⟨pos.val - 1, by omega⟩)
  | (.sourceLeftOne, pos) =>
      if hzero : pos.val = 0 then none
      else some (.sourceLeftOne, ⟨pos.val - 1, by omega⟩)
  | (.targetRight, pos) =>
      if hnext : pos.val + 1 < h then
        some (.targetRight, ⟨pos.val + 1, hnext⟩)
      else some (.targetLeftTwo, pos)
  | (.targetLeftTwo, pos) =>
      if hzero : pos.val = 0 then
        some (.targetLeftOne, ⟨h - 1, by omega⟩)
      else some (.targetLeftTwo, ⟨pos.val - 1, by omega⟩)
  | (.targetLeftOne, pos) =>
      if hzero : pos.val = 0 then some (.targetFinish, pos)
      else some (.targetLeftOne, ⟨pos.val - 1, by omega⟩)
  | (.targetFinish, pos) =>
      if hnext : pos.val + 1 < h then
        some (.targetFinish, ⟨pos.val + 1, hnext⟩)
      else none

/-- Every nonterminal logical route service consumes exactly one unit of
physical debt. -/
theorem routeService_debt_some {h : Nat} (hh : 0 < h)
    (head next : RoutedHead h) (hnext : routeService hh head = some next) :
    routeDebt h next.1 next.2 + 1 = routeDebt h head.1 head.2 := by
  rcases head with ⟨route, pos⟩
  cases route <;> simp only [routeService] at hnext <;>
    split at hnext <;> cases hnext <;> simp [routeDebt] <;> omega

/-- Final retirement occurs precisely at debt one. -/
theorem routeService_debt_none {h : Nat} (hh : 0 < h)
    (head : RoutedHead h) (hdone : routeService hh head = none) :
    routeDebt h head.1 head.2 = 1 := by
  rcases head with ⟨route, pos⟩
  cases route <;> simp only [routeService] at hdone <;>
    split at hdone <;> cases hdone <;> simp [routeDebt] <;> omega

/-- Every logical route service consumes exactly one unit of physical debt. -/
theorem routeService_debt {h : Nat} (hh : 0 < h) (head : RoutedHead h) :
    match routeService hh head with
    | none => routeDebt h head.1 head.2 = 1
    | some next => routeDebt h next.1 next.2 + 1 =
        routeDebt h head.1 head.2 := by
  cases hservice : routeService hh head with
  | none => exact routeService_debt_none hh head hservice
  | some next => exact routeService_debt_some hh head next hservice

theorem routeDebt_positive {h : Nat} (head : RoutedHead h) :
    0 < routeDebt h head.1 head.2 := by
  rcases head with ⟨route, pos⟩
  cases route <;> simp [routeDebt] <;> omega

theorem routeDebt_le_four_mul {h : Nat} (head : RoutedHead h) :
    routeDebt h head.1 head.2 ≤ 4 * h := by
  rcases head with ⟨route, pos⟩
  cases route <;> simp [routeDebt] <;> omega

theorem routeService_strict {h : Nat} (hh : 0 < h)
    (head next : RoutedHead h) (hnext : routeService hh head = some next) :
    routeDebt h next.1 next.2 < routeDebt h head.1 head.2 := by
  have hdebt := routeService_debt_some hh head next hnext
  omega

/-! ## Literal encoding in the existing packed controls -/

def routeControl : PostRoute → PPLLPairedFivePassCarrier.RootCtl32
  | .sourceRightTwo | .sourceRightOne => ⟨27, by omega⟩
  | .sourceLeftTwo | .sourceLeftOne => ⟨28, by omega⟩
  | .targetRight | .targetLeftTwo | .targetLeftOne | .targetFinish =>
      ⟨29, by omega⟩

def routeMessage : PostRoute → PPLLPairedFivePassCarrier.Msg32
  | .sourceRightTwo | .sourceLeftTwo | .targetRight => 0
  | .sourceRightOne | .sourceLeftOne | .targetLeftTwo => 1
  | .targetLeftOne => 2
  | .targetFinish => 3

def encodePostRoute (base : PackedControl) (route : PostRoute) :
    PackedControl :=
  { base with
    role := stagingRole
    rootCtl := routeControl route
    message := routeMessage route
    trail := postLease }

def decodePostRoute (control : PackedControl) : Option PostRoute :=
  if control.role = stagingRole ∧ control.trail = postLease then
    match control.rootCtl.val, control.message.val with
    | 27, 0 => some .sourceRightTwo
    | 27, 1 => some .sourceRightOne
    | 28, 0 => some .sourceLeftTwo
    | 28, 1 => some .sourceLeftOne
    | 29, 0 => some .targetRight
    | 29, 1 => some .targetLeftTwo
    | 29, 2 => some .targetLeftOne
    | 29, 3 => some .targetFinish
    | _, _ => none
  else none

@[simp] theorem decodePostRoute_encodePostRoute
    (base : PackedControl) (route : PostRoute) :
    decodePostRoute (encodePostRoute base route) = some route := by
  cases route <;>
    simp [decodePostRoute, encodePostRoute, routeControl, routeMessage] <;>
      decide

@[simp] theorem encodePostRoute_activeBit (base : PackedControl)
    (route : PostRoute) :
    (encodePostRoute base route).activeBit = base.activeBit := rfl

@[simp] theorem encodePostRoute_stagingBit (base : PackedControl)
    (route : PostRoute) :
    (encodePostRoute base route).stagingBit = base.stagingBit := rfl

theorem decodeLiteralTag_encodePostRoute (base : PackedControl)
    (route : PostRoute) :
    decodeLiteralTag (encodePostRoute base route).role
        (encodePostRoute base route).rootCtl = none := by
  exact decodeLiteralTag_role_three (routeControl route)

def tagPackedPost {h : Nat} (cell : PackedCell h) (route : PostRoute) :
    PackedCell h :=
  joinPacked (cell.pos, encodePostRoute (splitPacked cell).2 route)

@[simp] theorem tagPackedPost_pos {h : Nat} (cell : PackedCell h)
    (route : PostRoute) : (tagPackedPost cell route).pos = cell.pos := rfl

@[simp] theorem tagPackedPost_activeBit {h : Nat} (cell : PackedCell h)
    (route : PostRoute) :
    (tagPackedPost cell route).activeBit = cell.activeBit := rfl

def initialRoute : Option BlockSide → PostRoute
  | some .target => .targetRight
  | some .source | none => .sourceRightTwo

/-- The actual root/slot-one payload cut, now atomically namespaced as a
role-three post head instead of merely writing numeric control `27`. -/
def taggedLinearizeRootLeader {h : Nat} (site : Option BlockSide)
    (root leader : PackedCell h) : PackedCell h × PackedCell h :=
  let out := linearizeRootLeader root leader
  (tagPackedPost out.1 (initialRoute site), out.2)

@[simp] theorem taggedLinearizeRootLeader_positions {h : Nat}
    (site : Option BlockSide) (root leader : PackedCell h) :
    (taggedLinearizeRootLeader site root leader).1.pos = root.pos ∧
      (taggedLinearizeRootLeader site root leader).2.pos = leader.pos := by
  exact ⟨rfl, rfl⟩

@[simp] theorem taggedLinearizeRootLeader_payload {h : Nat}
    (site : Option BlockSide) (root leader : PackedCell h) :
    (taggedLinearizeRootLeader site root leader).1.activeBit =
        root.stagingBit ∧
      (taggedLinearizeRootLeader site root leader).2.activeBit =
        leader.stagingBit := by
  exact ⟨rfl, rfl⟩

@[simp] theorem taggedLinearizeRootLeader_decodes {h : Nat}
    (site : Option BlockSide) (root leader : PackedCell h) :
    decodePostRoute
        (splitPacked (taggedLinearizeRootLeader site root leader).1).2 =
      some (initialRoute site) := by
  simp [taggedLinearizeRootLeader, tagPackedPost]

theorem role_three_route_uses_no_new_states (h : Nat) :
    (packedCellStates h).values.length = 262144 * h :=
  packedCellStates_length h

#print axioms routeService_debt
#print axioms routeService_strict
#print axioms decodePostRoute_encodePostRoute
#print axioms decodeLiteralTag_encodePostRoute
#print axioms taggedLinearizeRootLeader_payload
#print axioms role_three_route_uses_no_new_states

end PPLLRole3PostRoute
