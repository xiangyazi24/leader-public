import Leader.L4.BStarLongFenceTopology

/-! Owner inverse on a fixed settled word chart. The only geometry
input needed at the selected pair is its old right-header bit:
it says whether the right site belongs to the next chart word. -/
namespace L4.BStarLongFiberOwner
open AllSizeProtocol BStarLongClaims BStarLongFenceTopology

def cmdDispl (j : Fin 11) : Int :=
  ([0,1,2,2,1,0,0,1,2,2,1] : List Int).getD j.val 0

def dataDispl : Sheet → Int
  | .ls => 0
  | .ld => 1
  | .rs => 2
  | .rd => 1

def shift (seam : Bool) : Side → Int
  | .left => 0
  | .right => if seam then 1 else 0

def owner (m word displacement : Int) : Int := (word-displacement)%m
def addressWord (m door displacement : Int) : Int := (door+displacement)%m

theorem owner_inverse (m door disp : Int) :
    owner m (addressWord m door disp) disp=door%m := by
  unfold owner addressWord
  rw [Int.sub_emod,Int.emod_emod,←Int.sub_emod]
  simp

theorem address_inverse (m word disp : Int) :
    addressWord m (owner m word disp) disp=word%m := by
  unfold owner addressWord
  rw [Int.add_emod,Int.emod_emod,←Int.add_emod]
  simp

/-- The cyclic index and its physical offset are independent chart
components. The inverse recovers the issuing door and preserves the
occurrence and old site offset exactly, even when offsets alias
among different occurrences. -/
def encode {A : Type} (m : Int) (d : A → Int)
    (q : Int × A × Nat) : Int × A × Nat :=
  (addressWord m q.1 (d q.2.1),q.2)

def decode {A : Type} (m : Int) (d : A → Int)
    (q : Int × A × Nat) : Int × A × Nat :=
  (owner m q.1 (d q.2.1),q.2)

theorem decode_encode {A : Type} (m : Int) (d : A → Int) (q : Int × A × Nat) :
    decode m d (encode m d q)=(q.1%m,q.2) := by simp [encode,decode,owner_inverse]

theorem encode_decode {A : Type} (m : Int) (d : A → Int) (q : Int × A × Nat) :
    encode m d (decode m d q)=(q.1%m,q.2) := by simp [encode,decode,address_inverse]

private def CRel (seam : Bool) (c : CommandClaim) : Bool :=
  c.destination.all fun r =>
    shift seam c.source.side-cmdDispl c.source.occurrence==shift seam r.side-cmdDispl r.occurrence

private def DRel (seam : Bool) (c : DataClaim) : Bool :=
  c.destination.all fun r =>
    shift seam c.source.side-dataDispl c.source.occurrence==shift seam r.side-dataDispl r.occurrence

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

private theorem relations (x y : LongGeometry) :
    (commandClaims (x,y)).all (CRel y.axes.h6)=true ∧
    (dataClaims (x,y)).all (DRel y.axes.h6)=true := by
  have C : commandClaims (x,y)=commandClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) := rfl
  have D : dataClaims (x,y)=dataClaims (geo false x.inside x.last,geo y.axes.h6 y.inside false) := rfl
  rw [C,D]
  generalize x.inside=xi
  generalize x.last=xl
  generalize y.axes.h6=yh
  generalize y.inside=yi
  cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel

def pairOwner {A : Type} (m leftWord : Int) (seam : Bool) (d : A → Int) (a : At A) :=
  owner m (leftWord+shift seam a.side) (d a.occurrence)

private theorem pairOwner_eq {A : Type} (m word : Int) (sea : Bool) (d : A → Int)
    (a b : At A)
    (h : shift sea a.side-d a.occurrence=shift sea b.side-d b.occurrence) :
    pairOwner m word sea d a=pairOwner m word sea d b := by
  unfold pairOwner owner
  congr 1
  omega

/-- Every selected command move, including both seam visits and the
local K8→K9 turn, preserves the chart's owner. -/
theorem command_owner (g : Pair LongGeometry) (m word : Int) (C : CommandClaim) (r : At (Fin 11))
    (h : C∈orderedCommands g) (hr : C.destination=some r) :
    pairOwner m word g.2.axes.h6 cmdDispl C.source=pairOwner m word g.2.axes.h6 cmdDispl r := by
  have H := List.all_eq_true.mp (relations g.1 g.2).1 C (selected_command_raw g C h)
  unfold CRel at H
  rw [hr] at H
  exact pairOwner_eq m word _ _ _ _ (beq_iff_eq.mp H)

/-- All literal offered packet hops transport only within one decoded
owner, whether or not prep later wins the lane-wide reservation. -/
theorem data_claim_owner (g : Pair LongGeometry) (m word : Int)
    (D : DataClaim) (r : At Sheet)
    (h : D∈dataClaims g) (hr : D.destination=some r) :
    pairOwner m word g.2.axes.h6 dataDispl D.source=pairOwner m word g.2.axes.h6 dataDispl r := by
  have H := List.all_eq_true.mp (relations g.1 g.2).2 D h
  unfold DRel at H
  rw [hr] at H
  exact pairOwner_eq m word _ _ _ _ (beq_iff_eq.mp H)

theorem data_owner (g : Pair LongGeometry) (m word : Int) (Rsv : List (At Sheet))
    (D : DataClaim) (r : At Sheet)
    (h : D∈orderedData g Rsv) (hr : D.destination=some r) :
    pairOwner m word g.2.axes.h6 dataDispl D.source=pairOwner m word g.2.axes.h6 dataDispl r :=
  data_claim_owner g m word D r (selected_data_raw g Rsv D h) hr

private theorem prep_rel (z : LongGeometry) (j : Fin 11) (op : Prep)
    (s : Sheet) (h : s∈prepSites z j op) : dataDispl s=cmdDispl j := by
  have H : ∀ j : Fin 11, (prepSites z j op).all (fun s => dataDispl s==cmdDispl j)=true := by
    have E (j : Fin 11) : prepSites z j op=prepSites (geo false z.inside false) j op := by cases op <;> rfl
    simp only [E]
    generalize z.inside=zi
    cases zi <;> cases op <;> decide +kernel
  exact beq_iff_eq.mp (List.all_eq_true.mp (H j) s h)

theorem prep_owner (g : Pair LongGeometry) (m word : Int)
    (cmd : At (Fin 11)) (op : Prep) (s : Sheet)
    (hs : s∈prepSites (BStarLongCommand.geometry g cmd.side) cmd.occurrence op) :
    pairOwner m word g.2.axes.h6 cmdDispl cmd=
      pairOwner m word g.2.axes.h6 dataDispl ⟨cmd.side,s⟩ := by
  unfold pairOwner
  rw [prep_rel _ _ _ _ hs]

/-- Any candidate prep and offered hop which overlap belong to the
same owner, whether the common address is its sender or receiver. -/
theorem overlap_owner (g : Pair LongGeometry) (m word : Int)
    (cmd : At (Fin 11)) (op : Prep) (s : Sheet)
    (hs : s∈prepSites (BStarLongCommand.geometry g cmd.side) cmd.occurrence op)
    (D : DataClaim) (hd : D∈dataClaims g)
    (hit : (⟨cmd.side,s⟩ : At Sheet)=D.source ∨ D.destination=some ⟨cmd.side,s⟩) :
    pairOwner m word g.2.axes.h6 cmdDispl cmd =
      pairOwner m word g.2.axes.h6 dataDispl D.source := by
  have P := prep_owner g m word cmd op s hs
  rcases hit with h|h
  · exact P.trans (congrArg (pairOwner m word _ dataDispl) h)
  · exact P.trans (data_claim_owner g m word D _ hd h).symm

theorem position_unique {A : Type} (m : Int) (d : A → Int) (q q' : Int × A × Nat)
    (h : q.1%m=q.1) (h' : q'.1%m=q'.1)
    (he : encode m d q=encode m d q') : q=q' := by
  have G := congrArg (decode m d) he
  exact Prod.ext (by simpa only [decode_encode,h,h'] using congrArg Prod.fst G) (by simpa only [decode_encode] using congrArg Prod.snd G)

/-- The prep actually reserved by this immutable raw round originates
in the same owner as any raw hop it suppresses. Using the offered
claim, rather than an already-selected hop, makes overlap meaningful. -/
theorem reserved_overlap_owner (g : Pair LongGeometry) (m word : Int)
    (x : Pair (BitVec BStarTrace.LW)) (s : At Sheet)
    (h : s∈BStarLongPrep.reserved (BStarLongCommandData.round g x).prep)
    (D : DataClaim) (hd : D∈dataClaims g)
    (hit : s=D.source ∨ D.destination=some s) :
    ∃ c p op, (c,BStarLongCommand.Offer.advance p)∈BStarLongCommandData.gated g x ∧
      p.fault=0 ∧ BStarLongCommandData.prepOf p.opcode.toNat=some op ∧
      pairOwner m word g.2.axes.h6 cmdDispl c.source=
        pairOwner m word g.2.axes.h6 dataDispl D.source := by
  obtain ⟨c,p,op,hc,hf,ho,hside,hsite⟩ := reserved_from_old_advance g x s h
  have E : (⟨c.source.side,s.occurrence⟩ : At Sheet)=s := by
    cases s
    simp_all
  exact ⟨c,p,op,hc,hf,ho,overlap_owner g m word c.source op s.occurrence hsite D hd (E ▸ hit)⟩

#print axioms command_owner
#print axioms data_owner
#print axioms overlap_owner
#print axioms reserved_overlap_owner
end L4.BStarLongFiberOwner
