import Leader.Wu.Entrance.WriterAdmissionResetEcho
import Leader.Wu.Entrance.ExpiryCutWord
import Leader.Wu.Entrance.LocalRulerWord

set_option autoImplicit false
set_option Elab.async false

namespace B6EntranceLawsCensus

open B6EntranceV2 B6EntranceV2K2 B6EntranceV3
open B6EntranceAdmissionV3

variable {n psi kappa tau : Nat} {P : Type}
variable {ring : DirectedRing n}

def WriterLocalProducer
    (WP : WriterProtected ring psi P) : Prop :=
  HostWriterProtectedLocal WP

def BitSilenceProducer
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) : Prop :=
  HostCoreBitSilence host view ring WP

def StaticExpiryProducer
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau) : Prop :=
  HostStaticExpiryTick host view

def WriterAdmissionProducer
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostWriterAdmissionV3 host view ring WP L

def TrafficWordProducer
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostDirectionalTrafficExitEnv host view ring WP L

def ExpiryWordProducer
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostComparisonExpiryWordEnv hpsi h2 host view ring WP L

def K2WordProducer
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostK2ClearableOrLeaderV3 hpsi h2 host view ring WP L

def RulerWordProducer
    (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostRulerWordV2 hpsi host view ring WP L

def RouteWordProducer
    (hpsi : 0 < psi) (host : B9Host.HostRow P)
    (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (L : Nat) : Prop :=
  HostRouteWordV2 hpsi host view ring WP L

def RulerLocalCoverBridge
    (hpsi : 0 < psi) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) : Prop :=
  ∀ (X : Workspace ring psi) (C : PConfig n P),
    K2DrainedAt view WP X C →
    B6Sanitation.RulerNF ring X.core.J (physConfig view C) →
    B6EntranceCompose.CanonicalArc hpsi ring X.core.J (physConfig view C) →
    B6EntranceCompose.LocalCover ring X.core.J (physConfig view C)

theorem corePreparedV2_of_localCoverBridge
    (hpsi : 0 < psi) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P)
    (hBridge : RulerLocalCoverBridge hpsi view WP)
    (X : Workspace ring psi) (C : PConfig n P)
    (hK2 : K2DrainedAt view WP X C)
    (hNF : B6Sanitation.RulerNF ring X.core.J (physConfig view C))
    (hArc : B6EntranceCompose.CanonicalArc
      hpsi ring X.core.J (physConfig view C)) :
    CorePreparedV2 hpsi view WP X C := by
  exact ⟨hK2, hNF, hArc, hBridge X C hK2 hNF hArc⟩


theorem entranceHostLawsV3b_of_stageProducers
    (hpsi : 0 < psi) (h2 : 2 ≤ psi)
    (host : B9Host.HostRow P) (view : P → Phys psi kappa tau)
    (WP : WriterProtected ring psi P) (b : EntranceBudgets)
    (hLocal : WriterLocalProducer WP)
    (hBit : BitSilenceProducer host view WP)
    (hStatic : StaticExpiryProducer host view)
    (hWriter : WriterAdmissionProducer host view WP b.writer.L)
    (hTraffic : TrafficWordProducer host view WP b.traffic.L)
    (hExpiry : ExpiryWordProducer hpsi h2 host view WP b.expiry.L)
    (hK2 : K2WordProducer hpsi h2 host view WP b.k2.L)
    (hRuler : RulerWordProducer hpsi host view WP b.ruler.L)
    (hRoute : RouteWordProducer hpsi host view WP b.route.L) :
    EntranceHostLawsV3b hpsi h2 host view ring WP b := by
  refine {
    writerLocal := ?_
    bitSilence := ?_
    staticExpiry := ?_
    writerAdmission := ?_
    trafficWord := ?_
    expiryWord := ?_
    k2Word := ?_
    rulerWord := ?_
    routeWord := ?_ }
  · simpa [WriterLocalProducer] using hLocal
  · simpa [BitSilenceProducer] using hBit
  · simpa [StaticExpiryProducer] using hStatic
  · simpa [WriterAdmissionProducer] using hWriter
  · simpa [TrafficWordProducer] using hTraffic
  · simpa [ExpiryWordProducer] using hExpiry
  · simpa [K2WordProducer] using hK2
  · simpa [RulerWordProducer] using hRuler
  · simpa [RouteWordProducer] using hRoute


end B6EntranceLawsCensus
