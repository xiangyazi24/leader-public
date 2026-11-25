import Leader.L4.PhysicalCustodyPassMean

namespace L4.PhysicalCustody
open BStarTrace BStarH6WordChart BStarLongFixedRouting BStarAcquireLiteralChain
open BStarClearanceOffset BStarOwnerRecoveryPass BStarClearanceSettled
local notation "hp" => (show 0<2 by decide)
set_option maxRecDepth 4096

/-- Closed geometry before earning offset correctness or grant coherence. -/
structure PackedFiber {s n : Nat} (x : Raw s n) where
  Q : Raw s n → Prop
  qx : Q x
  closed : ∀ y e, Q y → Q (rawNext s y e)
  layout : ∀ y, Q y → ∀ i, Layout (rows s) x i = Layout (rows s) y i
  geometry : ∀ y, Q y → CustodyGeometry y

/-- This isolates the only two quantitative inputs: production entrance
to persistent geometry, and a genuinely credited local owner recovery
on the sampled history. Five covers and two owner passes are internal. -/
theorem custody_reached_of_geometry_and_owner {s n : Nat}
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (settled : Raw s n → Prop) (Kgeom K : Nat)
    (geometryMean : ∀ x,
      IIDExpectedHittingTimeAtMost (rawNext s) settled x (Kgeom*n^2))
    (packedFiber : ∀ x, settled x → Nonempty (PackedFiber x))
    (localMean : ∀ (z : Raw s n) (g : ReadyAfterCovers z),
      (∀ y,g.Q y → correct (oldH6 (rows s) z) g.hh 5 y ∧ ∀ i,GrantClean y i) →
      ∀ o : Owners (oldH6 (rows s) z), ∀ y, g.Q y →
        IIDExpectedHittingTimeAtMost extendTape
          (firstCredit (HoldsCredit (Recovered hp z g.hh)) o y) [] (K*n*radWidth s))
    (x : Raw s n) :
    IIDExpectedHittingTimeAtMost (rawNext s) Custody x ((Kgeom+5+2*K)*n^2) := by
  apply concrete_conditional_quadratic sep settled Kgeom (2*K) geometryMean ?_ x
  intro z hz
  obtain ⟨F⟩ := packedFiber z hz
  let h := oldH6 (rows s) z
  let hh := (F.geometry z F.qx).hh
  have same (y : Raw s n) (qy : F.Q y) (i : Fin n) : oldH6 (rows s) y i = h i :=
    (congrArg Prod.fst (F.layout y qy i)).symm
  refine ⟨⟨h,hh,F.Q,F.qx,F.closed,same⟩,?_⟩
  intro y hy off clean
  let H := F.geometry y hy
  have O : ∃ h₀ : ∃ i, h i = true, correct h h₀ 5 y := ⟨hh,off⟩
  rw [show h=oldH6 (rows s) y from (funext (same y hy)).symm] at O
  obtain ⟨_,ofs⟩ := O
  have sameY (a : Raw s n) (qa : F.Q a) (i : Fin n) :
      oldH6 (rows s) a i=oldH6 (rows s) y i := (same a qa i).trans (same y hy i).symm
  let g : ReadyAfterCovers y := {
    Q := fun a => (F.Q a ∧ correct (oldH6 (rows s) y) H.hh 5 a) ∧ ∀ i,GrantClean a i
    qz := ⟨⟨hy,ofs⟩,clean⟩
    clean := clean
    closed := fun a e q =>
      ⟨settled_step hp _ H.hh sep F.Q F.closed sameY a e q.1,
        grant_coherent_closed a e (sep e) q.2⟩
    fiber := fun a q i => (F.layout y hy i).symm.trans (F.layout a q.1.1 i)
    hh := H.hh
    offset := ofs
    flags := H.flags
    notShort := H.notShort
    head := H.head
    cont := H.cont
    packed := H.packed
    upperWidth := H.upperWidth
    widthRatio := H.widthRatio
    charts := H.charts
    sep := sep }
  exact two_owner_passes_quadratic g K (localMean y g (fun _ q => ⟨q.1.2,q.2⟩))

end L4.PhysicalCustody
