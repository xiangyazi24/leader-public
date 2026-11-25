import Leader.L4.BStarNativeReceiptTape

namespace L4.BStarNativeUniqueHit
open BStarLongWork BStarSeparatingRail BStarAcquireVisitOrder AllSizeProtocol BStarTrace
open BStarNativeReceiptTape BStarGeneratedBandScan BStarGeneratedOwner
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private theorem not_strictly_before {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w pre gap tail : List (Fin n)} {e f : Fin n} {a b : Mode} {op : Nat}
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : CompilerBand hp x (addr 0).1 w)
    (E : w=((pre++[e])++gap)++f::tail)
    (H : Hit hp base addr len (run x pre) e op)
    (Q : Hit hp base addr len (run x ((pre++[e])++gap)) f op) : False := by
  let u := pre++[e]
  have W' : w=u++(gap++f::tail) := by simpa only [u,List.append_assoc] using E
  obtain ⟨_,_,G⟩ := BStarGeneratedTapeCuts.split hp u (gap++f::tail) (W' ▸ T)
  obtain ⟨_,L,_⟩ := BStarGeneratedTapeCuts.split hp gap (f::tail) G
  have F : CompilerBand hp (run x u) (addr 0).1 gap := by
    intro p q P
    have D : w=(u++p)++(q++f::tail) := by simp only [W',P,List.append_assoc]
    have A := band (u++p) (q++f::tail) D
    rwa [BStarResetSchedule.run_append] at A
  have N := end_monotone hp K sep L F
  have earlier : pc (run x u) (addr 0).1=op+1 := by
    unfold u
    rw [BStarResetSchedule.run_append]
    exact H.2.2.2.1
  have last : pc (run (run x u) gap) (addr 0).1=op := by
    rw [←BStarResetSchedule.run_append]
    exact Q.2.2.1
  omega

/-- Two witnesses to one compiler PC Hit on the same uninterrupted owner
word name the same raw consume cut. -/
theorem unique {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w p q u v : List (Fin n)} {e f : Fin n} {a b : Mode} {op : Nat}
    (K : (addr 0).2=0) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : CompilerBand hp x (addr 0).1 w)
    (W : w=p++e::u) (E : w=q++f::v)
    (H : Hit hp base addr len (run x p) e op)
    (Q : Hit hp base addr len (run x q) f op) : p=q ∧ e=f ∧ u=v := by
  have prefixP : p <+: w := ⟨_,W.symm⟩
  have prefixQ : q <+: w := ⟨_,E.symm⟩
  have le (p q u v : List (Fin n)) (e f : Fin n) (W : w=p++e::u) (E : w=q++f::v)
      (H : Hit hp base addr len (run x p) e op)
      (Q : Hit hp base addr len (run x q) f op) : ¬ p.length<q.length := by
    intro lt
    have A : p++[e] <+: w := ⟨u,by simpa only [List.append_assoc,List.singleton_append] using W.symm⟩
    obtain ⟨gap,J⟩ := List.prefix_of_prefix_length_le A (show q <+: w from ⟨_,E.symm⟩)
      (by simp; omega)
    exact not_strictly_before hp K sep T band (by rw [J,E]) H (J.symm ▸ Q)
  have eq : p=q :=
    (List.prefix_of_prefix_length_le prefixP prefixQ (by have L := le q p v u f e E W Q H; omega)).eq_of_length
      (by
        have L := le p q u v e f W E H Q
        have R := le q p v u f e E W Q H
        omega)
  subst q
  have S := List.cons.inj (List.append_cancel_left (W.symm.trans E))
  exact ⟨rfl,S.1,S.2⟩

#print axioms unique
end L4.BStarNativeUniqueHit
