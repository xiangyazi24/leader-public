import Leader.L4.BStarAcquireRailUniqueness
import Leader.L4.BStarH6Ordinal

namespace L4.BStarAcquireRailCoverage
open AllSizeProtocol BStarLongClaims BStarH6WordChart BStarH6Ordinal

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

def active (g : LongGeometry) (k : Fin 11) : Bool :=
  (k.val != 8 && k.val != 9) || g.inside

def incoming (l m r : LongGeometry) (k : Fin 11) : Bool :=
  (orderedCommands (l,m)).any (fun c => c.destination == some (R k)) ||
  (orderedCommands (m,r)).any (fun c => c.destination == some (L k))

def outgoing (l m r : LongGeometry) (k : Fin 11) : Bool :=
  (orderedCommands (l,m)).any (fun c => c.source == R k && c.kind != .door) ||
  (orderedCommands (m,r)).any (fun c => c.source == L k && c.kind != .door)

/-- The two relevant local IN continuation laws: an unfinished
significant prefix must extend on a body edge, and every significant
body site must follow an unfinished significant site. -/
def continuation (x y : LongGeometry) : Bool :=
  (!(x.inside && !x.last) || (!y.axes.h6 && y.inside)) &&
  (!(!y.axes.h6 && y.inside) || (x.inside && !x.last))

/-- Literal selected-claim coverage. On active slots, the only absent
predecessor is source header K0. The terminal header K10 has a
selected service claim (no continuation). Inactive K8/K9 have neither. -/
theorem ports (l m r : LongGeometry)
    (H : (!m.axes.h6 || m.inside) = true) (Hr : (!r.axes.h6 || r.inside) = true)
    (Q : continuation l m = true) (S : continuation m r = true) (k : Fin 11) :
    incoming l m r k = (active m k && !(m.axes.h6 && k.val == 0)) ∧
    outgoing l m r k = active m k := by
  have F (li ll mh mi ml rh ri : Bool) :
      (!mh || mi) = true → (!rh || ri) = true →
      continuation (geo false li ll) (geo mh mi ml) = true →
      continuation (geo mh mi ml) (geo rh ri false) = true →
      ∀ j : Fin 11,
        incoming (geo false li ll) (geo mh mi ml) (geo rh ri false) j =
          (active (geo mh mi ml) j && !(mh && j.val == 0)) ∧
        outgoing (geo false li ll) (geo mh mi ml) (geo rh ri false) j =
          active (geo mh mi ml) j := by
    cases li <;> cases ll <;> cases mh <;> cases mi <;> cases ml <;> cases rh <;> cases ri <;>
      decide +kernel
  exact F l.inside l.last m.axes.h6 m.inside m.last r.axes.h6 r.inside H Hr Q S k

/-- An exact active-slot predecessor or source-door exception. The
witness is drawn from actual ordered claims on the two physical ports. -/
theorem predecessor (l m r : LongGeometry)
    (H : (!m.axes.h6 || m.inside) = true) (Hr : (!r.axes.h6 || r.inside) = true)
    (Q : continuation l m = true) (S : continuation m r = true) (k : Fin 11)
    (ha : active m k = true) (hd : ¬ (m.axes.h6=true ∧ k.val=0)) :
    (∃ C ∈ orderedCommands (l,m), C.destination=some (R k)) ∨
    (∃ C ∈ orderedCommands (m,r), C.destination=some (L k)) := by
  have P := (ports l m r H Hr Q S k).1
  have B : incoming l m r k=true := by
    rw [P,ha]
    cases hh : m.axes.h6
    · rfl
    · have hk : k.val ≠ 0 := fun z => hd ⟨hh,z⟩
      have hf : (k.val == 0) = false := Bool.eq_false_iff.mpr (fun E => hk (beq_iff_eq.mp E))
      simp [hf]
  simpa [incoming,List.any_eq_true] using B

/-- An active slot has a selected continuing or terminal departure;
the source door is excluded from this statement. -/
theorem departure (l m r : LongGeometry)
    (H : (!m.axes.h6 || m.inside) = true) (Hr : (!r.axes.h6 || r.inside) = true)
    (Q : continuation l m = true) (S : continuation m r = true) (k : Fin 11)
    (ha : active m k = true) :
    (∃ C ∈ orderedCommands (l,m), C.source=R k ∧ C.kind≠.door) ∨
    (∃ C ∈ orderedCommands (m,r), C.source=L k ∧ C.kind≠.door) := by
  have B := (ports l m r H Hr Q S k).2.trans ha
  simpa [outgoing,List.any_eq_true] using B

/-- Exact width hypotheses imply the Boolean local coverage premises:
positive r, exact ordinal IN/LAST, and at least r sites per H6 word.
The cached offset and cached successor END are not used. -/
theorem geometry_ports {a : LargeParams} {n r : Nat} (b : LargeRows a)
    (x : Fin n → LargeSite a) (hh : ∃ i, oldH6 b x i=true) (hr : 0<r)
    (flags : ∀ i, let g := longGeometry b (x i)
      g.inside=decide (oldOrdinal b x hh i<r) ∧
      g.last=decide (oldOrdinal b x hh i+1=r))
    (notShort : ∀ i, oldH6 b x (rightNeighbor i)=true → r≤oldOrdinal b x hh i+1) :
    (∀ i, let g := longGeometry b (x i); (!g.axes.h6 || g.inside)=true) ∧
    (∀ i, let g := oldPair b x i; continuation g.1 g.2=true) := by
  constructor
  · intro i
    dsimp only
    change (!oldH6 b x i || (longGeometry b (x i)).inside)=true
    cases H : oldH6 b x i
    · rfl
    · have E : oldOrdinal b x hh i=0 := (ordinal_zero _ hh i).mpr H
      simp [(flags i).1,E,hr]
  · intro i
    let j := rightNeighbor i
    let l := longGeometry b (x i)
    let m := longGeometry b (x j)
    change continuation l m=true
    unfold continuation
    rw [(flags i).1,(flags i).2,(flags j).1]
    change ((!(decide (oldOrdinal b x hh i<r) && !decide (oldOrdinal b x hh i+1=r)) ||
        (!oldH6 b x j && decide (oldOrdinal b x hh j<r))) &&
        (!(!oldH6 b x j && decide (oldOrdinal b x hh j<r)) ||
        (decide (oldOrdinal b x hh i<r) && !decide (oldOrdinal b x hh i+1=r))))=true
    cases T : oldH6 b x j
    · have E : oldOrdinal b x hh j = oldOrdinal b x hh i+1 := ordinal_body _ hh i T
      by_cases U : oldOrdinal b x hh i+1<r
      · have V : oldOrdinal b x hh i<r := by omega
        have W : ¬ oldOrdinal b x hh i+1=r := by omega
        simp [E,U,V,W]
      · by_cases V : oldOrdinal b x hh i<r
        · have W : oldOrdinal b x hh i+1=r := by omega
          simp [E,V,W]
        · simp [E,U,V]
    · have N := notShort i T
      by_cases V : oldOrdinal b x hh i<r
      · have W : oldOrdinal b x hh i+1=r := by omega
        simp [V,W]
      · simp [V]

end L4.BStarAcquireRailCoverage
