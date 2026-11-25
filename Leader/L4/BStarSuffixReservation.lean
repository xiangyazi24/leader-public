import Leader.L4.BStarAdmittedNeedSeparator
import Leader.L4.BStarActualReceiptReservation
import Leader.L4.BStarFrontierReserve

namespace L4.BStarSuffixReservation
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarH6WordChart BStarH6Ordinal
open BStarCustodyCuts BStarLongFixedRouting BStarAcquireRailCoverage BStarClearanceOffset
open BStarPhysicalReserved BStarPhysicalIncrementLedger BStarIncrementLedger BStarEpochLift
open BStarPhysicalPairLaw BStarLiveReservation BStarAdmittedNeedSeparator
open BStarNativeNeedLift

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

/-- The real separator between two admitted reads carries its sealed NEED.
If the separator is after common recovery, the actual INC ledger counts it. -/
theorem separated_by_inc_or_early_pub {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    (u v tail : List (Fin n)) (cuts : CutFacts hp base initial u v)
    (Q : X→Prop) (I : Q initial) (fiber : ∀ x,Q x→∀ i,Layout B base i=Layout B x i)
    (closed : ∀ x e,Q x→Q (step x e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (offset : correct (oldH6 B base) hh 5 initial)
    (coherent : ∀ x,Q x → ∀ i,oldH6 B x i=true →
      BStarLongGrant.conflict (BStarGrantReaderHistory.ports x i)=false)
    (heads : ∀ i, let g := longGeometry B (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i, let g := oldPair B base i; continuation g.1 g.2=true)
    (hr : 3≤r)
    (flags : ∀ i,(longGeometry B (base i)).inside=decide (oldOrdinal B base hh i<r) ∧
      (longGeometry B (base i)).last=decide (oldOrdinal B base hh i+1=r))
    (notShort : ∀ j,oldH6 B base (rightNeighbor j)=true → r≤oldOrdinal B base hh j+1)
    (start : Fin n→Nat) (i : Fin n) :
    let w := (u++v)++tail
    ∀ a b bitA bitB, a<b → b<w.length →
      admittedRead hp base initial hh start w a=some (i,bitA) →
      admittedRead hp base initial hh start w b=some (i,bitB) →
      ∃ j,a≤j ∧ j<b ∧ publishes hp initial w j i ∧
        ((u++v).length≤j → tapeInc hp base hh initial w j=some i) := by
  dsimp only
  intro a b bitA bitB ab hb A D
  obtain ⟨j,aj,jb,J,E,P,d,N,S⟩ := sealed_separator hp Q I fiber
    (fun x hx e=>closed x e hx) sep offset coherent heads cont start _ i a b bitA bitB ab hb A D
  refine ⟨j,aj,jb,⟨J,?_⟩,?_⟩
  · rwa [E]
  · intro late
    rw [tapeInc,dif_pos J,E,List.take_append,List.take_of_length_le late] at *
    exact detects_sealed_need hp u v (tail.take (j-(u++v).length)) cuts hh sep Q I fiber closed i
      P hr flags notShort d N S

/-- A stopped pending read cannot be shadowed by a suffix read at the
same or a smaller key. Any separating publication predating the stop
contradicts pending status; any later separator advances the ledger. -/
theorem reserve_none_of_suffix_read {base initial : X} {hh : ∃ i,oldH6 B base i=true}
    (start : Fin n→Nat) (history future : List (Fin n)) (i : Fin n)
    (separate : ∀ a b c d, a<b → b<(history++future).length →
      admittedRead hp base initial hh start (history++future) a=some (i,c) →
      admittedRead hp base initial hh start (history++future) b=some (i,d) →
      ∃ j,a≤j ∧ j<b ∧ publishes hp initial (history++future) j i ∧
        (history.length≤j → tapeInc hp base hh initial (history++future) j=some i))
    (b : Nat) (bit : Bool) (late : history.length≤b) (Blt : b<(history++future).length)
    (R : admittedRead hp base initial hh start (history++future) b=some (i,bit))
    (level : Nat)
    (levelGe : count start (tapeInc hp base hh initial (history++future)) i b ≤ level) :
    reserveAtKey hp base initial hh start history i level=none := by
  classical
  unfold reserveAtKey
  split
  next eq =>
    unfold cutReserved reserved
    split
    next H =>
      obtain ⟨a,ha,A,N⟩ := Classical.choose_spec H
      have Af := (read_prefix hp base initial hh start history future a ha).trans A
      obtain ⟨j,aj,jb,Pub,Inc⟩ := separate a b (Classical.choose H) bit (by omega) Blt Af R
      have jl : history.length≤j := by
        apply Nat.le_of_not_gt
        intro l
        exact N j aj l ((publication_prefix hp initial history future j i l).mp Pub)
      have M := count_monotone start (tapeInc hp base hh initial (history++future)) i jl
      have U := count_monotone start (tapeInc hp base hh initial (history++future)) i
        (show j+1≤b by omega)
      have W := count_step start (tapeInc hp base hh initial (history++future)) i j (Inc jl)
      have key := count_on_shared_prefix hp base hh initial history [] future start i
      rw [List.append_nil] at key
      change level=count start (tapeInc hp base hh initial history) i history.length at eq
      omega
    next => rfl
  next => rfl


/-- An original suffix observation has its literal index and absolute
INC count; all gates are admitted from common recovery onward. -/
theorem suffix_index
    {base initial : X} {hh : ∃ i,oldH6 B base i=true} {u v : List (Fin n)}
    (cuts : CutFacts hp base initial u v)
    (start : Fin n→Nat) (history future a z : List (Fin n)) (e i : Fin n) (lev : Nat) (b : Bool)
    (H : (u++v) <+: history) (F : future=a++e::z)
    (R : reveal hp base hh initial (ownerAt hp base hh) start (history++a) e=some ((i,lev),b)) :
    (history++a).length < (history++future).length ∧
    admittedRead hp base initial hh start (history++future) (history++a).length=some (i,b) ∧
    lev=count start (tapeInc hp base hh initial (history++future)) i (history++a).length := by
  have W : history++future=(history++a)++e::z := by rw [F,List.append_assoc]
  have L : (history++a).length < (history++future).length := by rw [W]; simp
  have U : ∀ gate,BStarRecoveredReveal.Admitted hp base initial hh (history++a) gate := by
    intro gate
    obtain ⟨s,E⟩ := H
    rw [←E,List.append_assoc]
    exact BStarRecoveredReveal.admitted_append hp (s++a)
      (BStarRecoveredReveal.common_admission hp hh u v cuts gate)
  have A := BStarRecoveredReveal.agrees_if_admitted hp base initial hh start
    (history++a) e (fun g _=>U g)
  have T : (history++future).take (history++a).length=history++a := by
    rw [W]
    exact List.take_append_length
  have E : (history++future)[(history++a).length]=e := by
    apply Option.some.inj
    rw [←List.getElem?_eq_getElem L,W,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
    rfl
  refine ⟨L,?_,?_⟩
  · unfold admittedRead
    rw [dif_pos L,T,E,A,R]
    rfl
  · have C := count_on_shared_prefix hp base hh initial (history++a) [] (e::z) start i
    rw [List.append_nil,←W] at C
    exact (BStarFrontierReserve.revealed_at_count hp base initial hh start (history++a) e i lev b R).trans C

/-- Two post-stop suffix reads of the same natural key have one
position. This uses sealed NEED separation rather than arbitrary
publication or coherence alone. -/
theorem suffix_position_unique
    {base initial : X} {hh : ∃ i,oldH6 B base i=true} {u v : List (Fin n)}
    (cuts : CutFacts hp base initial u v)
    (start : Fin n→Nat) (history future : List (Fin n)) (i : Fin n) (level : Nat)
    (H : (u++v) <+: history)
    (separate : ∀ a b c d, history.length≤a → a<b → b<(history++future).length →
      admittedRead hp base initial hh start (history++future) a=some (i,c) →
      admittedRead hp base initial hh start (history++future) b=some (i,d) →
      ∃ j,a≤j ∧ j<b ∧ tapeInc hp base hh initial (history++future) j=some i) :
    ∀ a e z a' e' z' c c',
      future=a++e::z → future=a'++e'::z' →
      reveal hp base hh initial (ownerAt hp base hh) start (history++a) e=some ((i,level),c) →
      reveal hp base hh initial (ownerAt hp base hh) start (history++a') e'=some ((i,level),c') →
      a.length=a'.length := by
  intro a e z a' e' z' c c' F F' R R'
  obtain ⟨L,A,K⟩ := suffix_index hp cuts start history future a z e i level c H F R
  obtain ⟨L',A',K'⟩ := suffix_index hp cuts start history future a' z' e' i level c' H F' R'
  have impossible : ∀ (a b : Nat) (x y : Bool), history.length≤a → a<b →
      b<(history++future).length →
      admittedRead hp base initial hh start (history++future) a=some (i,x) →
      admittedRead hp base initial hh start (history++future) b=some (i,y) →
      level=count start (tapeInc hp base hh initial (history++future)) i a →
      level=count start (tapeInc hp base hh initial (history++future)) i b → False := by
    intro a b x y late ab blt A D K₁ K₂
    obtain ⟨j,aj,jb,J⟩ := separate a b x y late ab blt A D
    have C := count_step start (tapeInc hp base hh initial (history++future)) i j J
    have m := count_monotone start (tapeInc hp base hh initial (history++future)) i aj
    have M := count_monotone start (tapeInc hp base hh initial (history++future)) i
      (show j+1≤b by omega)
    omega
  rcases Nat.lt_trichotomy (history++a).length (history++a').length with h|h|h
  · exact (impossible _ _ _ _ (by simp) h L' A A' K K').elim
  · simpa only [List.length_append,Nat.add_right_inj] using h
  · exact (impossible _ _ _ _ (by simp) h L A' A K' K).elim

#print axioms separated_by_inc_or_early_pub
#print axioms reserve_none_of_suffix_read
end L4.BStarSuffixReservation
