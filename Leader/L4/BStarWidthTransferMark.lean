import Leader.L4.BStarWidthTransferFull

namespace L4.BStarWidthTransferMark
open AllSizeProtocol
open BStarWidthTransfer
  (readSource phaseF opF flagsF tokF)
open BStarWidthTransferDepart (readData lane)
open BStarWidthTransferFull (Cell read step work_transfer)

/-- Typed width cell includes both stored geometry coordinates, rather than
treating the geometry-selected view as a new work register. -/
structure Site (c : Nat) where
  work : Cell
  off : BitVec (ell (c+1))
  successorHeader : BitVec 1

def decode {c : Nat} (x : BitVec (WidthByteRows.W c)) : Site c :=
  ⟨read (c:=c) x, ((ShortGeo.width c).off).read x,
    ((ShortGeo.width c).successor).read x⟩

def mark {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (Site c)) : Pair (Site c) :=
  let i := if h.1 then 0 else min c x.1.off.toNat
  let y := BStarWidthTransferFull.step c r i h (x.1.work,x.2.work)
  (⟨y.1,x.1.off,BitVec.ofNat 1 h.2.toNat⟩,
   ⟨y.2,BitVec.ofNat (ell (c+1)) (if h.2 then 0 else min c (i+1)),x.2.successorHeader⟩)

private theorem field_unaffected {c k : Nat} (f : Field (WidthByteRows.W c) k)
    (bound : f.offset+k≤29) (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c)))
    (q : Pair (Patch (WidthByteRows.W c))) :
    let y := patchPair ((ShortGeo.width c).patches c h x q) x
    let z := patchPair q x
    f.read y.1=f.read z.1 ∧ f.read y.2=f.read z.2 := by
  dsimp only
  constructor <;>
    (apply BitVec.eq_of_getLsbD_eq; intro i hi;
     simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and])
  · apply (ShortGeo.work_agrees_outside (ShortGeo.width c) c h x q (f.offset+i) _).1
    intro E
    have T := E.1
    change 29≤f.offset+i at T
    omega
  · apply (ShortGeo.work_agrees_outside (ShortGeo.width c) c h x q (f.offset+i) _).2
    intro E
    have T := E.1
    change 29≤f.offset+i at T
    omega

private theorem work_unaffected {c : Nat} (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c)))
    (q : Pair (Patch (WidthByteRows.W c))) :
    Pair.map (read (c:=c)) (patchPair ((ShortGeo.width c).patches c h x q) x) =
      Pair.map (read (c:=c)) (patchPair q x) := by
  have P := field_unaffected (phaseF c) (by change 23≤29; decide) h x q
  have O := field_unaffected (opF c) (by change 21≤29; decide) h x q
  have F := field_unaffected (flagsF c) (by change 18≤29; decide) h x q
  have T := field_unaffected (tokF c) (by change 16≤29; decide) h x q
  have D1 := field_unaffected (lane c 1 (by decide)) (by change 29≤29; decide) h x q
  have D2 := field_unaffected (lane c 2 (by decide)) (by change 28≤29; decide) h x q
  have D3 := field_unaffected (lane c 3 (by decide)) (by change 27≤29; decide) h x q
  have D4 := field_unaffected (lane c 4 (by decide)) (by change 26≤29; decide) h x q
  have D5 := field_unaffected (lane c 5 (by decide)) (by change 25≤29; decide) h x q
  have D6 := field_unaffected (lane c 6 (by decide)) (by change 24≤29; decide) h x q
  unfold Pair.map BStarWidthTransferFull.read readSource readData
  rw [P.1,P.2,O.1,O.2,F.1,F.2,T.1,T.2,D1.1,D1.2,D2.1,D2.2,D3.1,D3.2,
    D4.1,D4.2,D5.1,D5.2,D6.1,D6.2]

/-- Full joined WIDTH mark transfer on arbitrary old bytes and old
headers. SuccessorHeader and offset update on opposite endpoints. -/
theorem mark_transfer {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c))) :
    Pair.map (decode (c:=c)) (patchPair ((ShortGeo.width c).patches c h x
      (BStarShort.widthWork (c:=c) r h x)) x) =
      mark r h (Pair.map (decode (c:=c)) x) := by
  let q := BStarShort.widthWork (c:=c) r h x
  let g := ShortGeo.width c
  let y := patchPair (g.patches c h x q) x
  have U := work_unaffected h x q
  have V := U.trans (work_transfer r h x)
  have S1 := g.read_successor c h x q
  have S2 := g.held_successor c h x q
  have O1 := g.held_offset c h x q
  have O2 := g.read_offset c h x q
  have eqOff : g.effective c h.1 x.1 = WidthByteRows.offset h.1 x.1 := rfl
  have O2' : g.off.read y.2 =
      BitVec.ofNat (ell (c+1)) (if h.2 then 0 else min c (WidthByteRows.offset h.1 x.1+1)) := by
    rw [O2]
    unfold ShortGeo.nextOff
    rw [eqOff]
  unfold Pair.map decode mark
  apply Prod.ext
  · change Site.mk (read (c:=c) y.1) (g.off.read y.1) (g.successor.read y.1) = _
    rw [O1,S1]
    have V1 := congrArg Prod.fst V
    rw [show read (c:=c) y.1 = _ from V1]
    rfl
  · change Site.mk (read (c:=c) y.2) (g.off.read y.2) (g.successor.read y.2) = _
    rw [O2',S2]
    have V2 := congrArg Prod.snd V
    rw [show read (c:=c) y.2 = _ from V2]
    rfl

#print axioms mark_transfer
end L4.BStarWidthTransferMark

