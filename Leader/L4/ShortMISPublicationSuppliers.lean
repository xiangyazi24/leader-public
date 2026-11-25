import Leader.L4.ShortMISPublicationLift
import Leader.L4.ShortMISSheetRows

namespace L4.ShortMISPublicationSuppliers
open PhysicalCustody ShortMISLift ShortMIS3Entrance ShortMISPublicationLift
open ShortH2RawEntrance

variable {s n : Nat}

/-- Publication-specific historical input. At a real classified mark,
the packet's old bits must come from the protected neighbor reads. -/
def ProtectedRows (G : Geometry s n) : Prop :=
  ∀ x e, Good G.P x → ∀ i,
    classify G.P x e=some i → ProtectedAt G x e i

/-- Publication-specific trajectory input: the designated ingress
mark in the real word reads the old guard on the higher sheet. -/
def FencedWordRows (G : Geometry s n) : Prop :=
  ∀ i x, Good G.P x → FiveParked G.P (G.family i) x → GuardedWordAt G i x

theorem auth (G : Geometry s n) (A : ProtectedRows G) : ShortMISSheetRows.Auth G := by
  intro x e X
  exact auth_if_protected G x e X.1 (A x e X)

theorem win (G : Geometry s n) (N : 2≤G.A) (W : FencedWordRows G) :
    ShortMISSheetRows.Win G := by
  intro i x X F
  exact win_if_guard G N i x X.1 (W i x X F)

def assemble (G : Geometry s n) (N : 2≤G.A) (A : ProtectedRows G) (W : FencedWordRows G) :
    LocalRows G :=
  ShortMISSheetRows.assemble G (auth G A) (win G N W)

theorem mis2_from_h2 (N : 63<n) (x : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x)
    (A : ProtectedRows (mis2Geometry N x H)) (W : FencedWordRows (mis2Geometry N x H)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH3 N) x (K_H3*n^2) :=
  permanent_h3_from_h2 N x H (assemble _ (by change 2≤4; decide) A W)

theorem mis3_from_h3 (N : 189<n) (x : Raw s n)
    (H : PermanentH3 (by omega : 63<n) x)
    (A : ProtectedRows (mis3Geometry N x H)) (W : FencedWordRows (mis3Geometry N x H)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x (K_H4*n^2) :=
  permanent_h4_from_h3 N x H (assemble _ (by change 2≤8; decide) A W)

/-- Mixed layer handoff with exactly the classified/read-history and
designated-word obligations on the two real sheets left explicit. -/
theorem mis23_from_h2 (N : 189<n) (x : Raw s n)
    (H : PermanentH2 (by omega : 21<n) x)
    (A2 : ProtectedRows (mis2Geometry (by omega : 63<n) x H))
    (W2 : FencedWordRows (mis2Geometry (by omega : 63<n) x H))
    (A3 : ∀ (y : Raw s n) (Y : PermanentH3 (by omega : 63<n) y),
      ProtectedRows (mis3Geometry N y Y))
    (W3 : ∀ (y : Raw s n) (Y : PermanentH3 (by omega : 63<n) y),
      FencedWordRows (mis3Geometry N y Y)) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s) (PermanentH4 N) x
      ((K_H3+K_H4)*n^2) :=
  permanent_h4_from_h2 N x H (assemble _ (by change 2≤4; decide) A2 W2)
    (fun y Y=>assemble _ (by change 2≤8; decide) (A3 y Y) (W3 y Y))

end L4.ShortMISPublicationSuppliers
