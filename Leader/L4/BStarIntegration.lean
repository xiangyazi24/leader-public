import Leader.L4.BStarTrace
import Leader.L4.BStarShort
import Leader.L4.BStarPublic

/-! Integration checkpoint. This is not a closed b*: the full
long-work producer remains an explicit parameter, separate from the
concrete scratch and public producers. -/
namespace L4.BStarIntegration
open AllSizeProtocol BStarTrace

def productionWithLong (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (long : Row LongGeometry LW) :
    LargeRows (production k₁ k₂ t₂ J₁ J₂ r c p c₁) :=
  bundle (production k₁ k₂ t₂ J₁ J₂ r c p c₁) rfl
    BStarShort.shortMIS (BStarShort.reportWork ⟨k₁+1,1,k₁,J₁⟩)
    (BStarShort.reportWork ⟨2,t₂,k₂,J₂⟩) (BStarShort.widthWork (c:=c) r)
    long ⟨BStarPublic.publicWork hp⟩

theorem production_ports (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (long : Row LongGeometry LW) :
    let b := productionWithLong k₁ k₂ t₂ J₁ J₂ r c p c₁ hp long
    b.mis=BStarShort.shortMIS ∧ b.report1=BStarShort.reportWork ⟨k₁+1,1,k₁,J₁⟩ ∧
      b.report2=BStarShort.reportWork ⟨2,t₂,k₂,J₂⟩ ∧
      b.widthClient=BStarShort.widthWork (c:=c) r ∧ b.longWork=long ∧
      b.longScratch=longScratch ∧ b.shared.ordinaryPublic=BStarPublic.publicWork hp :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms production_ports
end L4.BStarIntegration
