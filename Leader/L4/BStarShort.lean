import Leader.L4.ShortByteReadouts
import Leader.L4.MISByteRows
import Leader.L4.ReportByteRows
import Leader.L4.WidthByteRows

/-! Exact short work mask corrections before the
physical geometry join. All decisions read the immutable old pair. -/
namespace L4.BStarShort
open AllSizeProtocol

abbrev Row (w : Nat) := Pair Bool → Pair (BitVec w) → Pair (Patch w)

/-- Remove only assignment support. The original proposed value is not recoded. -/
def erase {w : Nat} (q : Patch w) (m : BitVec w) : Patch w :=
  ⟨q.mask &&& ~~~m,q.value⟩

theorem erase_mask {w : Nat} (q : Patch w) (m : BitVec w) (i : Nat) :
    (erase q m).mask.getLsbD i = (q.mask.getLsbD i && !m.getLsbD i) := by
  by_cases h : i<w
  · simp [erase,h]
  · simp only [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_gt h), Bool.false_and]

/-- A structural grant correction needs only the three grant incidences and
departing RESET/ACQ flags. It does not read a partially patched word. -/
structure GrantView where
  header : Bool
  old : Fin 3 → Bool
  release : Fin 3 → Bool
  ask : Fin 3 → Bool

def GrantView.canonical (g : GrantView) (j : Fin 3) : Bool :=
  if g.old 1 then j==1 else g.old j

def GrantView.conflict (g : GrantView) : Bool :=
  g.old 1 && (g.old 0 || g.old 2)

def GrantView.centerWin (g : GrantView) : Bool :=
  g.ask 1 && !g.release 1 && !g.canonical 0 && !g.canonical 1 && !g.canonical 2

def GrantView.win (g : GrantView) (j : Fin 3) : Bool :=
  if j==1 then g.centerWin
  else !g.centerWin && !g.canonical 1 && g.ask j && !g.canonical j && !g.release j

/-- Cleanup and dirty conflict normalization retain full support.
An otherwise idle incidence does not become a write, unlike a release. -/
def GrantView.drop (g : GrantView) (j : Fin 3) : Bool :=
  g.header && !g.conflict && !(g.release j || g.win j)

/-- Typed grant update on the old snapshot, before byte lowering. -/
def GrantView.nextValue (g : GrantView) (j : Fin 3) : Bool :=
  if g.header then (g.canonical j && !g.release j) || g.win j else false

/-- When an initiator bit is not assigned, the authorization table's
next value is exactly its old Boolean value. -/
theorem GrantView.drop_holds (g : GrantView) (j : Fin 3) (hd : g.drop j=true) :
    g.nextValue j=g.old j := by
  have hd' : g.header=true ∧ g.conflict=false ∧ (g.release j=false ∧ g.win j=false) := by
    simpa [GrantView.drop,Bool.and_assoc] using hd
  obtain ⟨hh,hc,hr,hw⟩ := hd'
  simp only [GrantView.nextValue,hh,if_true,hr,hw,Bool.not_false,Bool.and_true,Bool.or_false]
  unfold GrantView.canonical GrantView.conflict at *
  cases hW : g.old 1
  · simp
  · have H : g.old 0=false ∧ g.old 2=false := by simpa [hW] using hc
    match j with
    | ⟨0,_⟩ => simp [H.1]
    | ⟨1,_⟩ => simp [hW]
    | ⟨2,_⟩ => simp [H.2]

def atBit (w i : Nat) (b : Bool) : BitVec w :=
  if b then (1 : BitVec w) <<< i else 0

def grantErase {w : Nat} (base : Nat) (g : GrantView) : BitVec w :=
  atBit w (base+2) (g.drop 0) ||| atBit w (base+1) (g.drop 1) ||| atBit w base (g.drop 2)

def grantView {w : Nat} (base acq : Nat) (header : Bool) (x : BitVec w)
    (token : Fin 3 → MISByteCodec.Token) : GrantView :=
  let dep := fun op j => (token j).tag==2 && !(token j).fault && (token j).opcode==op
  ⟨header, (fun j => x.getLsbD (base+2-j.val)), dep 0, dep acq⟩

/-- MIS correction, at high-first numerical grant lane 89. -/
def shortMIS : Row 96 := fun h x =>
  let q := MISByteRows.row h x
  let g := grantView 89 3 h.1 x.1 (MISByteCodec.oldK h.1 x.1)
  (erase q.1 (grantErase 89 g),q.2)

/-- Old report K using the same effective offset and gate binding as the
private decoder. The gate belongs only to occurrence one. -/
def reportK (p : ReportByteRows.Params) (h : Bool) (x : BitVec p.w) (j : Fin 3) :
    MISByteCodec.Token :=
  let cap := max 3 p.digits
  let i := if h then 0 else min cap ((x.extractLsb' (ReportByteRows.workW p+1) (ell (cap+1))).toNat)
  ReportByteRows.decode p (j.val==1 && i==2)
    (x.extractLsb' (ReportByteRows.tail p+(2-j.val)*ReportByteRows.tokenW p)
      (ReportByteRows.tokenW p))

/-- Report correction. Both report instances use this row. -/
def reportWork (p : ReportByteRows.Params) : Row p.w := fun h x =>
  let q := ReportByteRows.row p h x
  let g := grantView (ReportByteRows.grantBase p) (ReportByteRows.acqOp p) h.1 x.1
    (reportK p h.1 x.1)
  (erase q.1 (grantErase (ReportByteRows.grantBase p) g),q.2)

/-- A matching valid WAIT receipt other than COMPARE leaves the dormant
result flags untouched, even when WIDTH schedules BEGIN next. -/
def widthHoldFlags {c : Nat} (header : Bool) (x : BitVec (WidthByteRows.W c)) : Bool :=
  let t := WidthByteRows.decode ((WidthByteRows.suffixField c 14 16 (by decide)).read x)
  let phase := WidthByteRows.get (c:=c) x 7 2 (by decide)
  let op := WidthByteRows.get (c:=c) x 9 3 (by decide)
  header && phase==2 && decide (op≤5) && t.tag==3 && !t.fault && t.op==op && op != 2

def widthWork {c : Nat} (r : Nat) : Row (WidthByteRows.W c) := fun h x =>
  let q := WidthByteRows.row (c:=c) r h x
  let m := ((WidthByteRows.suffixField c 12 2 (by decide)).assign (0 : BitVec 2)).mask
  (q.1, if widthHoldFlags (c:=c) h.2 x.2 then erase q.2 m else q.2)

theorem shortMIS_responder (h : Pair Bool) (x : Pair (BitVec 96)) :
    (shortMIS h x).2 = (MISByteRows.row h x).2 := rfl

theorem reportWork_responder (p : ReportByteRows.Params) (h : Pair Bool) (x : Pair (BitVec p.w)) :
    (reportWork p h x).2 = (ReportByteRows.row p h x).2 := rfl

theorem widthWork_initiator {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c))) :
    (widthWork (c:=c) r h x).1 = (WidthByteRows.row (c:=c) r h x).1 := rfl

theorem atBit_support (w k : Nat) (b : Bool) (i : Nat) :
    (atBit w k b).getLsbD i = (b && decide (k=i ∧ i<w)) := by
  cases b
  · simp [atBit]
  · simp only [atBit,if_true,BitVec.getLsbD_shiftLeft,Bool.true_and]
    by_cases lt : i<w <;> by_cases ki : i<k <;> by_cases eq : k=i
    all_goals
      first
      | subst i; simp_all <;> omega
      | have ne : i-k ≠ 0 := by omega
        first | (simp_all <;> omega) | (simp_all [ne] <;> omega)
      | simp_all

/-- Exact bit support: nothing outside the three logical grant addresses
is removed, including on conflict normalization or nonheader cleanup. -/
theorem grantErase_mask {w : Nat} (base : Nat) (g : GrantView) (i : Nat) :
    (grantErase (w:=w) base g).getLsbD i =
      ((g.drop 0 && decide (base+2=i ∧ i<w)) ||
       (g.drop 1 && decide (base+1=i ∧ i<w)) ||
       (g.drop 2 && decide (base=i ∧ i<w))) := by
  simp only [grantErase,BitVec.getLsbD_or,atBit_support]

theorem shortMIS_mask (h : Pair Bool) (x : Pair (BitVec 96)) (i : Nat) :
    (shortMIS h x).1.mask.getLsbD i = ((MISByteRows.row h x).1.mask.getLsbD i &&
      !(grantErase (w:=96) 89 (grantView 89 3 h.1 x.1 (MISByteCodec.oldK h.1 x.1))).getLsbD i) :=
  erase_mask _ _ _

theorem reportWork_mask (p : ReportByteRows.Params) (h : Pair Bool) (x : Pair (BitVec p.w))
    (i : Nat) :
    (reportWork p h x).1.mask.getLsbD i = ((ReportByteRows.row p h x).1.mask.getLsbD i &&
      !(grantErase (w:=p.w) (ReportByteRows.grantBase p)
        (grantView (ReportByteRows.grantBase p) (ReportByteRows.acqOp p) h.1 x.1
          (reportK p h.1 x.1))).getLsbD i) :=
  erase_mask _ _ _

theorem widthWork_mask {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c)))
    (i : Nat) :
    (widthWork (c:=c) r h x).2.mask.getLsbD i =
      ((WidthByteRows.row (c:=c) r h x).2.mask.getLsbD i &&
        !(widthHoldFlags (c:=c) h.2 x.2 && decide (16≤i ∧ i<18))) := by
  have M :
      ((WidthByteRows.suffixField c 12 2 (by decide)).assign (0 : BitVec 2)).mask.getLsbD i =
        decide (16≤i ∧ i<18) := by
    apply Bool.eq_iff_iff.mpr
    rw [Field.inMask]
    change (16≤i ∧ i<18) ↔ decide (16≤i ∧ i<18) = true
    exact Iff.of_eq (decide_eq_true_eq (p := (16≤i ∧ i<18))).symm
  unfold widthWork
  cases H : widthHoldFlags (c:=c) h.2 x.2
  · simp
  · change (erase (WidthByteRows.row (c:=c) r h x).2
        ((WidthByteRows.suffixField c 12 2 (by decide)).assign (0 : BitVec 2)).mask).mask.getLsbD i =
      ((WidthByteRows.row (c:=c) r h x).2.mask.getLsbD i && !decide (16≤i ∧ i<18))
    rw [erase_mask,M]

/-- A narrowed valid receipt preserves the exact raw flags, including
the dormant spare pair 11. -/
theorem widthWork_flags_hold {c : Nat} (r : Nat) (h : Pair Bool)
    (x : Pair (BitVec (WidthByteRows.W c))) (H : widthHoldFlags (c:=c) h.2 x.2=true) :
    WidthByteRows.get (c:=c) ((widthWork (c:=c) r h x).2.apply x.2) 12 2 (by decide) =
      WidthByteRows.get (c:=c) x.2 12 2 (by decide) := by
  unfold WidthByteRows.get Field.read
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  apply Patch.hold
  rw [widthWork_mask,H]
  have address : (16≤(WidthByteRows.suffixField c 12 2 (by decide)).offset+i ∧
      (WidthByteRows.suffixField c 12 2 (by decide)).offset+i<18) := by
    change 16≤16+i ∧ 16+i<18
    omega
  simp [address]

private theorem erase_apply_outside {w : Nat} (q : Patch w) (m old : BitVec w)
    (i : Nat) (h : m.getLsbD i=false) :
    ((erase q m).apply old).getLsbD i=(q.apply old).getLsbD i := by
  have eq : (erase q m).mask.getLsbD i=q.mask.getLsbD i := by simp [erase_mask,h]
  cases hm : q.mask.getLsbD i
  · rw [Patch.hold _ _ _ (eq.trans hm),Patch.hold _ _ _ hm]
  · rw [Patch.write _ _ _ (eq.trans hm),Patch.write _ _ _ hm]
    rfl

/-- Grant filtering changes no output bit outside the initiator's
original three-bit grant field. -/
theorem mis_apply_outside (h : Pair Bool) (x : Pair (BitVec 96)) (i : Nat)
    (hi : i<89 ∨ 92≤i) :
    (((shortMIS h x).1).apply x.1).getLsbD i =
      (((MISByteRows.row h x).1).apply x.1).getLsbD i := by
  apply erase_apply_outside
  rw [grantErase_mask]
  have E0 : 89+2≠i := by omega
  have E1 : 89+1≠i := by omega
  have E2 : 89≠i := by omega
  simp [E0,E1,E2]

/-- The report filter likewise preserves every non-grant raw output. -/
theorem report_apply_outside (p : ReportByteRows.Params) (h : Pair Bool) (x : Pair (BitVec p.w))
    (i : Nat) (hi : i<ReportByteRows.grantBase p ∨ ReportByteRows.grantBase p+3≤i) :
    (((reportWork p h x).1).apply x.1).getLsbD i =
      (((ReportByteRows.row p h x).1).apply x.1).getLsbD i := by
  apply erase_apply_outside
  rw [grantErase_mask]
  have E0 : ReportByteRows.grantBase p+2≠i := by omega
  have E1 : ReportByteRows.grantBase p+1≠i := by omega
  have E2 : ReportByteRows.grantBase p≠i := by omega
  simp [E0,E1,E2]

/-- Width narrowing has no effect on any other raw bit. -/
theorem width_apply_outside {c : Nat} (r : Nat) (h : Pair Bool) (x : Pair (BitVec (WidthByteRows.W c)))
    (i : Nat) (hi : i<16 ∨ 18≤i) :
    (((widthWork (c:=c) r h x).2).apply x.2).getLsbD i =
      (((WidthByteRows.row (c:=c) r h x).2).apply x.2).getLsbD i := by
  unfold widthWork
  split
  · apply erase_apply_outside
    apply Bool.eq_false_iff.mpr
    intro H
    have E := (Field.inMask _ _ _).mp H
    change 16≤i ∧ i<18 at E
    omega
  · rfl

/-- Idempotent RESET writes only its own grant; dirty canonicalization still
owns all grants, and a clean idle header owns none of them. -/
theorem mis_grant_fixtures :
    let reset := MISByteCodec.encode {tag:=2,opcode:=0}
    let u : BitVec 96 := BitVec.ofNat 96 (reset.toNat*2^38)
    let conflict : BitVec 96 := BitVec.ofNat 96 (2^91+2^90)
    (((shortMIS (true,true) (u,0)).1.mask.extractLsb' 89 3).toNat=4) ∧
    (((shortMIS (true,true) (0,0)).1.mask.extractLsb' 89 3).toNat=0) ∧
    (((shortMIS (true,true) (conflict,0)).1.mask.extractLsb' 89 3).toNat=7) := by decide

theorem report_idle_grant_fixture :
    let p : ReportByteRows.Params := ⟨3,1,1,2⟩
    (((reportWork p (true,true) (0,0)).1.mask.extractLsb'
      (ReportByteRows.grantBase p) 3).toNat=0) := by decide

private def widthReceipt (op : Nat) (fault : Bool) : BitVec (WidthByteRows.W 5) :=
  let q := WidthByteRows.control 5 2 op 3
  let r := WidthByteRows.tokenPatch 5 ⟨3,op,0,fault⟩
  (q.compose r).apply 0

/-- Successful WIDTH holds flags, even while scheduling BEGIN. COMPARE
and an invalid WIDTH receipt retain the old flag-write support. -/
theorem width_flag_fixtures :
    let u := widthReceipt 0 false
    let cmp := widthReceipt 2 false
    let bad := widthReceipt 0 true
    let p := (widthWork (c:=5) 3 (true,true) (0,u)).2
    (p.mask.extractLsb' 16 2).toNat=0 ∧
    ((p.apply u).extractLsb' 16 2).toNat=3 ∧
    (((widthWork (c:=5) 3 (true,true) (0,cmp)).2.mask.extractLsb' 16 2).toNat=3) ∧
    (((widthWork (c:=5) 3 (true,true) (0,bad)).2.mask.extractLsb' 16 2).toNat=3) := by decide

#print axioms shortMIS_mask
#print axioms reportWork_mask
#print axioms widthWork_mask
#print axioms width_flag_fixtures

end L4.BStarShort
