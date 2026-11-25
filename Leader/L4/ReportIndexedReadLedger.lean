import Leader.L4.ReportOwnerIndexedFlight
import Leader.L4.ReportChartPartition

namespace L4.ReportIndexedReadLedger
open AllSizeProtocol PhysicalCustody ShortResetCycle ShortResetChart ReportByteRows
open ReportRawProjection ReportOwnerIndexedFlight ReportOwnerProvenanceTransport
open ShortLayerGeometry ReportResetBarrier ReportResetRawHooks
open ReportOwnerResetDrain ReportPrelaunchK1Geometry ReportOwnerForwardLocations
set_option maxHeartbeats 3000000

theorem sample_lo (p : Params) (u : BitVec p.w) (bank : Nat) :
    indexedSample p u bank 2 = min (p.beta-1) ((reportDigitPair p u bank).toNat % 2^d p) := by
  let off := sealBase p+5+(1-bank)*bankW p
  change min (p.beta-1) (u.extractLsb' off (d p)).toNat =
    min (p.beta-1) ((u.extractLsb' off (2*d p)).toNat % 2^d p)
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_mod_of_dvd, Nat.pow_dvd_pow 2 (Nat.le_mul_of_pos_left _ (by decide : 0<2))]

theorem sample_hi (p : Params) (u : BitVec p.w) (bank : Nat) :
    indexedSample p u bank 0 = min (p.beta-1) ((reportDigitPair p u bank).toNat / 2^d p) := by
  let off := sealBase p+5+(1-bank)*bankW p
  change min (p.beta-1) (u.extractLsb' (off+d p) (d p)).toNat =
    min (p.beta-1) ((u.extractLsb' off (2*d p)).toNat / 2^d p)
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 2^(off+d p)=2^off*2^d p from Nat.pow_add 2 off (d p),
    ←Nat.div_div_eq_div_mul]
  have E : 2^(2*d p)=2^(d p)*2^(d p) := by
    rw [←Nat.pow_add,show 2*d p=d p+d p by omega]
  rw [E,Nat.mod_mul_right_div_self]

theorem read_hit_hi (p : Params) (op : Nat) (R : op < writeOp p)
    (hu : Bool) (u : BitVec p.w) (a : IndexedData)
    (H : reportOldOffset p hu u=indexedReadOffset p op) :
    indexedNext p op hu u 0 (some a)=some {a with hi:=indexedSample p u (a.banks/2) 0} := by
  simp [indexedNext,R,H]

theorem read_hit_lo (p : Params) (op : Nat) (R : op < writeOp p)
    (hu : Bool) (u : BitVec p.w) (a : IndexedData)
    (H : reportOldOffset p hu u=indexedReadOffset p op) :
    indexedNext p op hu u 2 (some a)=some {a with lo:=indexedSample p u (a.banks%2) 2} := by
  simp [indexedNext,R,H]

theorem read_nonhit (p : Params) (op : Nat) (R : op < writeOp p)
    (hu : Bool) (u : BitVec p.w) (a : IndexedData) (j : Fin 3)
    (H : ¬(j=0 ∧ reportOldOffset p hu u=indexedReadOffset p op))
    (L : ¬(j=2 ∧ reportOldOffset p hu u=indexedReadOffset p op)) :
    indexedNext p op hu u j (some a)=some a := by
  by_cases O : reportOldOffset p hu u=indexedReadOffset p op
  · have H0 : j ≠ 0 := fun J => H ⟨J,O⟩
    have H2 : j ≠ 2 := fun J => L ⟨J,O⟩
    simp [indexedNext,R,O,H0,H2]
  · simp [indexedNext,R,O]

/-- The exact deposited fields. Only the named half changes; both bank
indices and the untouched half are preserved. This is an old-pair read. -/
def readDeposit (p : Params) (u : BitVec p.w) (a : IndexedData) (port : Fin 3) :
    IndexedData :=
  if port=0 then {a with hi:=indexedSample p u (a.banks/2) 0}
  else {a with lo:=indexedSample p u (a.banks%2) 2}

theorem read_hit_hop (p : Params) (op : Nat) (Range : IndexedOp p op)
    (R : op<writeOp p) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) (J : reset0Destination hv j=some k) (g' : Bool)
    (a : IndexedData) (Q : a.OK p op)
    (A : publicationToken p hu u j=indexedF p op (some a))
    (Port : j=0 ∨ j=2) (H : reportOldOffset p hu u=indexedReadOffset p op) :
    decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)=
      indexedF p op (some (readDeposit p u a j)) := by
  rw [rankIndexed_hop p op Range hu hv u v j k J g' (some a) Q A]
  rcases Port with rfl|rfl
  · rw [read_hit_hi p op R hu u a H]; rfl
  · rw [read_hit_lo p op R hu u a H]; rfl

theorem read_hit_turn (p : Params) (op : Nat) (Range : IndexedOp p op)
    (R : op<writeOp p) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) (J : reset0Destination hv j=none) (g' : Bool)
    (a : IndexedData) (Q : a.OK p op)
    (A : publicationToken p hu u j=indexedF p op (some a))
    (Port : j=0 ∨ j=2) (H : reportOldOffset p hu u=indexedReadOffset p op) :
    decode p g' (resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j)=
      indexedD p op (some (readDeposit p u a j)) := by
  rw [rankIndexed_turn p op Range hu hv u v j J g' (some a) Q A]
  rcases Port with rfl|rfl
  · rw [read_hit_hi p op R hu u a H]; rfl
  · rw [read_hit_lo p op R hu u a H]; rfl

#print axioms read_hit_hop
#print axioms read_hit_turn
#print axioms sample_lo
#print axioms sample_hi
#print axioms read_hit_hi
#print axioms read_hit_lo
#print axioms read_nonhit

variable {s n : Nat} {h : Fin n → Bool}

private theorem stepPayload_reader (d : Sheet) (C : Chart h) (op : Nat)
    (R : op<writeOp (params d s)) (x : Raw s n) (k : Nat) (a : IndexedData) :
    ∃ b, stepPayload d C op x k (some a)=some b ∧ b.banks=a.banks ∧
      b.hi=(if C.route.port k=0 ∧ reportOldOffset (params d s) (h (out C k))
           (bytesL d x (out C k))=indexedReadOffset (params d s) op
        then indexedSample (params d s) (bytesL d x (out C k)) (a.banks/2) 0 else a.hi) ∧
      b.lo=(if C.route.port k=2 ∧ reportOldOffset (params d s) (h (out C k))
           (bytesL d x (out C k))=indexedReadOffset (params d s) op
        then indexedSample (params d s) (bytesL d x (out C k)) (a.banks%2) 2 else a.lo) := by
  unfold stepPayload
  generalize HO : reportOldOffset (params d s) (h (out C k)) (bytesL d x (out C k)) = O
  generalize C.route.port k = j
  by_cases H : O=indexedReadOffset (params d s) op
  · by_cases H0 : j=0
    · exact ⟨{a with hi:=indexedSample (params d s) (bytesL d x (out C k)) (a.banks/2) 0}, by simp [indexedNext,R,HO,H,H0]⟩
    · by_cases H2 : j=2
      · exact ⟨{a with lo:=indexedSample (params d s) (bytesL d x (out C k)) (a.banks%2) 2}, by simp [indexedNext,R,HO,H,H2]⟩
      · exact ⟨a, by simp [indexedNext,R,HO,H,H0,H2]⟩
  · exact ⟨a, by simp [indexedNext,R,HO,H]⟩

/-- A concrete old departure on the same original tape. The witness
    contains the unique chart ordinal and the matching old offset. -/
structure Sample (d : Sheet) (C : Chart h) (op : Nat)
    (x0 : Raw s n) (w : List (Fin n)) (k : Nat) (port : Fin 3)
    (bank value : Nat) : Prop where
  witness : ∃ pre post, w=pre++out C k::post ∧
    C.route.port k=port ∧
    reportOldOffset (params d s) (h (out C k)) (bytesL d (rawRun x0 pre) (out C k))=
      indexedReadOffset (params d s) op ∧
    value=indexedSample (params d s) (bytesL d (rawRun x0 pre) (out C k)) bank port ∧
    ∃ a : IndexedData, FState d C op (rawRun x0 pre) k (some a) ∧
      (if port=0 then a.banks/2 else a.banks%2)=bank

private theorem Sample.snoc {d : Sheet} {C : Chart h} {op : Nat}
    {x0 : Raw s n} {w : List (Fin n)} {k : Nat} {port : Fin 3} {bank value : Nat}
    (S : Sample d C op x0 w k port bank value) (e : Fin n) :
    Sample d C op x0 (w++[e]) k port bank value := by
  obtain ⟨pre,post,E,P,O,V,W⟩ := S.witness
  exact ⟨pre,post++[e],by rw [E,List.append_assoc]; rfl,P,O,V,W⟩

/-- The sole input beyond the literal walk: on any reached old prefix
    a matching offset lives at its designated chart ordinal. -/
def UniqueReaderHits (d : Sheet) (C : Chart h) (op : Nat)
    (x0 : Raw s n) (left right : Nat) : Prop :=
  ∀ (w : List (Fin n)) (k : Nat), k<C.L →
    ((C.route.port k=0 ∧ reportOldOffset (params d s) (h (out C k))
        (bytesL d (rawRun x0 w) (out C k))=indexedReadOffset (params d s) op) ↔ k=left) ∧
    ((C.route.port k=2 ∧ reportOldOffset (params d s) (h (out C k))
        (bytesL d (rawRun x0 w) (out C k))=indexedReadOffset (params d s) op) ↔ k=right)

private def Half (d : Sheet) (C : Chart h) (op : Nat) (x0 : Raw s n)
    (w : List (Fin n)) (k i : Nat) (port : Fin 3) (bank init val : Nat) : Prop :=
  (i<k → Sample d C op x0 w i port bank val) ∧ (k≤i → val=init)

private theorem Half.snoc {d : Sheet} {C : Chart h} {op : Nat} {x0 : Raw s n}
    {w : List (Fin n)} {k i : Nat} {port : Fin 3} {bank init val : Nat}
    (H : Half d C op x0 w k i port bank init val) (e : Fin n) :
    Half d C op x0 (w++[e]) k i port bank init val :=
  ⟨fun K => (H.1 K).snoc e,H.2⟩

private theorem Half.advance {d : Sheet} {C : Chart h} {op : Nat} {x0 : Raw s n}
    {w : List (Fin n)} {k i : Nat} {port : Fin 3} {bank init val val' : Nat}
    (H : Half d C op x0 w k i port bank init val)
    (Ready : ∃ a : IndexedData, FState d C op (rawRun x0 w) k (some a) ∧
      (if port=0 then a.banks/2 else a.banks%2)=bank)
    (A : (C.route.port k=port ∧ reportOldOffset (params d s) (h (out C k))
          (bytesL d (rawRun x0 w) (out C k))=indexedReadOffset (params d s) op) ↔ k=i)
    (B : val'=(if k=i then indexedSample (params d s) (bytesL d (rawRun x0 w) (out C k))
                              bank port else val)) :
    Half d C op x0 (w++[out C k]) (k+1) i port bank init val' := by
  by_cases E : k=i
  · subst i
    obtain ⟨P,O⟩ := A.mpr rfl
    rw [if_pos rfl] at B
    exact ⟨fun _ => ⟨w,[],rfl,P,O,B,Ready⟩,fun K => (by omega : False).elim⟩
  · rw [if_neg E] at B
    subst val'
    exact ⟨fun K => (H.1 (by omega)).snoc _,fun K => H.2 (by omega)⟩

private def Ledger (d : Sheet) (C : Chart h) (op : Nat) (x0 : Raw s n)
    (initial : IndexedData) (left right : Nat) (w : List (Fin n)) (cur : Cursor) : Prop :=
  match cur with
  | .forward k (some a) => a.banks=initial.banks ∧
      Half d C op x0 w k left 0 (initial.banks/2) initial.hi a.hi ∧
      Half d C op x0 w k right 2 (initial.banks%2) initial.lo a.lo
  | .backward _ (some a) => a.banks=initial.banks ∧
      Sample d C op x0 w left 0 (initial.banks/2) a.hi ∧
      Sample d C op x0 w right 2 (initial.banks%2) a.lo
  | _ => False

private theorem ledger_forward_next {d : Sheet} {C : Chart h} {op : Nat} {x0 : Raw s n}
    {initial : IndexedData} {left right : Nat} {w : List (Fin n)} {k : Nat}
    {q : Option IndexedData}
    (R : op<writeOp (params d s)) (Hit : UniqueReaderHits d C op x0 left right)
    (Old : FState d C op (rawRun x0 w) k q) (H : Ledger d C op x0 initial left right w (.forward k q)) :
    Ledger d C op x0 initial left right (w++[out C k])
      (.forward (k+1) (stepPayload d C op (rawRun x0 w) k q)) := by
  cases q with
  | none => exact H.elim
  | some a =>
    obtain ⟨B,Hi,Lo⟩ := H
    obtain ⟨b,E,B',Hi',Lo'⟩ := stepPayload_reader d C op R (rawRun x0 w) k a
    obtain ⟨L,T⟩ := Hit w k Old.shape.2.1
    rw [E]
    refine ⟨B'.trans B, Hi.advance ⟨a,Old,by rw [if_pos (rfl : (0 : Fin 3)=0),B]⟩ L ?_,
      Lo.advance ⟨a,Old,by rw [if_neg (by decide : (2 : Fin 3) ≠ 0),B]⟩ T ?_⟩
    · simpa only [L,B] using Hi'
    · simpa only [T,B] using Lo'

theorem reader_walk_result (d : Sheet) (C : Chart h) (op : Nat) (x0 : Raw s n)
    (initial final : IndexedData) (left right : Nat) (w : List (Fin n))
    (R : op<writeOp (params d s)) (Hit : UniqueReaderHits d C op x0 left right)
    (L : left<C.L) (T : right<C.L)
    (W : Walk d C op x0 (some initial) w (.backward 0 (some final))) :
    final.banks=initial.banks ∧ Sample d C op x0 w left 0 (initial.banks/2) final.hi ∧
      Sample d C op x0 w right 2 (initial.banks%2) final.lo := by
  suffices H : ∀ tape cur, Walk d C op x0 (some initial) tape cur →
      Ledger d C op x0 initial left right tape cur by
    exact H w _ W
  intro tape cur tapeWalk
  induction tapeWalk with
  | seed _ => exact ⟨rfl,⟨fun K => (by omega : False).elim,fun _ => rfl⟩,
      ⟨fun K => (by omega : False).elim,fun _ => rfl⟩⟩
  | @fhold w k q e old new IH =>
    cases q with
    | none => exact IH.elim
    | some a => exact ⟨IH.1,IH.2.1.snoc e,IH.2.2.snoc e⟩
  | hop _ old _ IH => exact ledger_forward_next R Hit old IH
  | @turn w k q _ old K _ IH =>
    have S := ledger_forward_next R Hit old IH
    generalize stepPayload d C op (rawRun x0 w) k q = q' at S ⊢
    cases q' with
    | none => exact S.elim
    | some a => exact ⟨S.1,S.2.1.1 (K ▸ L),S.2.2.1 (K ▸ T)⟩
  | @dhold w k q e _ _ IH =>
    cases q with
    | none => exact IH.elim
    | some a => exact ⟨IH.1,IH.2.1.snoc e,IH.2.2.snoc e⟩
  | @back w j q _ _ IH =>
    cases q with
    | none => exact IH.elim
    | some a => exact ⟨IH.1,IH.2.1.snoc _,IH.2.2.snoc _⟩

#print axioms reader_walk_result

private theorem old_offset_literal (p : Params) (h : Bool) (u : BitVec p.w) :
    reportOldOffset p h u =
      if h then 0 else min (max 3 p.digits) (((ShortGeo.report p.beta p.digits p.streak).off.read u).toNat) := by
  have W := layout_size p
  change reportWidth p.beta p.digits p.streak=workW p+1+ell (max 3 p.digits+1) at W
  change (if h then 0 else min _ ((u.extractLsb' (workW p+1) _).toNat)) =
    (if h then 0 else min _ ((u.extractLsb' (reportWidth p.beta p.digits p.streak -
      ell (max 3 p.digits+1)) _).toNat))
  rw [show reportWidth p.beta p.digits p.streak - ell (max 3 p.digits+1)=workW p+1 by omega]

theorem cached_old_offset (d : Sheet) (hh : ∃ i,h i=true)
    {Q : Raw s n→Prop} (x : Raw s n) (X : Cached d hh Q x) (i : Fin n) :
    reportOldOffset (params d s) (h i) (bytesL d x i)=
      min (max 3 (params d s).digits) (BStarH6Ordinal.ordinal h hh i) := by
  rw [old_offset_literal]
  have H :
      ((ShortGeo.report (params d s).beta (params d s).digits (params d s).streak).off.read
        (bytesL d x i)).toNat = min (max 3 (params d s).digits) (BStarH6Ordinal.ordinal h hh i) := by
    cases d with
    | first => exact (ReportCacheAllSites.raw_fields_correct hh (by decide : 0<3) x X i).1
    | second => exact (ReportCacheAllSites.raw_fields_correct hh
        (by omega : 0<max 3 (ell (radiusTwo s+1))) x X i).1
  rw [H]
  by_cases E : h i=true
  · rw [if_pos E,(BStarH6Ordinal.ordinal_zero h hh i).mpr E,Nat.min_zero]
  · rw [if_neg E,←Nat.min_assoc,Nat.min_self]

theorem reader_geometry (d : Sheet) (hh : ∃ i,h i=true) {Q : Raw s n→Prop}
    (CF : Fibre (h:=h) d Q) (N : 1<n) (x0 : Raw s n) (X : Cached d hh Q x0)
    {r : Fin n} {a b c : Nat} (R : h r=true)
    (F : Gap h r a) (G : Gap h (nextAt r a) b) (I : Gap h (nextAt (nextAt r a) b) c)
    (room : a+b+c<n) (op j : Nat) (J : indexedReadOffset (params d s) op=j)
    (digit : j<(params d s).digits) (A : (params d s).digits≤a) (B : (params d s).digits≤c) :
    let C := chart_of_three R F G I room
    j<C.L ∧ a+b+j<C.L ∧ UniqueReaderHits d C op x0 j (a+b+j) := by
  let C := chart_of_three R F G I room
  have closed (w : List (Fin n)) (x : Raw s n) (Y : Cached d hh Q x) :
      Cached d hh Q (rawRun x w) := by
    induction w generalizing x with
    | nil => exact Y
    | cons e w IH => exact IH _ ((cached_fibre d N hh Q CF).closed x e Y)
  have K (w : List (Fin n)) := closed w x0 X
  have Cap : j<max 3 (params d s).digits := Nat.lt_of_lt_of_le digit (Nat.le_max_right _ _)
  have Geom0 := ReportChartPartition.chart_unique_digit hh R F G I room 0 j Cap (by
    change j<a; omega)
  have Geom2 := ReportChartPartition.chart_unique_digit hh R F G I room 2 j Cap (by
    change j<c; omega)
  have W0 : ReportChartPartition.wordStart a b 0=0 := rfl
  have W2 : ReportChartPartition.wordStart a b 2=a+b := rfl
  rw [W0,Nat.zero_add] at Geom0
  rw [W2] at Geom2
  refine ⟨Geom0.1,Geom2.1,fun w k L => ?_⟩
  rw [cached_old_offset d hh _ (K w),J]
  exact ⟨Geom0.2 k L,Geom2.2 k L⟩

#print axioms cached_old_offset
#print axioms reader_geometry

/-- Full contract-facing sample at the actual old departure. -/
theorem Sample.ready {d : Sheet} {C : Chart h} {op : Nat} {x0 : Raw s n}
    {w : List (Fin n)} {k : Nat} {port : Fin 3} {bank value : Nat}
    (S : Sample d C op x0 w k port bank value) (Range : IndexedOp (params d s) op)
    (Port : port=0 ∨ port=2) :
    ∃ pre post, w=pre++out C k::post ∧ k<C.L ∧ C.route.port k=port ∧
      let x := rawRun x0 pre
      let u := selectBytes d (x (out C k))
      let t := tok d C x k
      t.tag=2 ∧ t.fault=false ∧ t.opcode=op ∧ readyAt d C x k=true ∧
      reportOldOffset (params d s) (h (out C k)) u=indexedReadOffset (params d s) op ∧
      (if port=0 then t.payload/2^(2*ReportByteRows.d (params d s)+1)%2
        else t.payload/2^(2*ReportByteRows.d (params d s))%2)=bank ∧
      value=min ((params d s).beta-1)
        (if port=0 then (reportDigitPair (params d s) u bank).toNat/2^ReportByteRows.d (params d s)
          else (reportDigitPair (params d s) u bank).toNat%2^ReportByteRows.d (params d s)) := by
  obtain ⟨pre,post,E,P,O,V,a,Old,B⟩ := S.witness
  have Ready := rankIndexed_ready _ _ Range _ _ _ _
    ((predecessor_projection d C (rawRun x0 pre) k).symm.trans Old.packet)
  refine ⟨pre,post,E,Old.shape.2.1,P,?_,?_,?_,Ready,O,?_,?_⟩
  all_goals try rw [Old.packet]
  · rfl
  · rfl
  · rfl
  · rcases Port with rfl|rfl
    · dsimp only [indexedF] at *
      rw [if_pos (rfl : (0 : Fin 3)=0)] at B ⊢
      exact (indexed_left_bank _ _ a Old.bound).trans B
    · dsimp only [indexedF] at *
      rw [if_neg (by decide : (2 : Fin 3) ≠ 0)] at B ⊢
      exact (indexed_right_bank _ _ a Old.bound).trans B
  · rcases Port with rfl|rfl
    · rw [if_pos (rfl : (0 : Fin 3)=0)]
      exact V.trans (sample_hi _ _ _)
    · rw [if_neg (by decide : (2 : Fin 3) ≠ 0)]
      exact V.trans (sample_lo _ _ _)

theorem reply_payload (d : Sheet) (C : Chart h) (op : Nat) (x : Raw s n)
    (a : IndexedData) (D : DState d C op x 0 (some a)) (R : op<writeOp (params d s)) :
    (tok d C x 0).payload=a.hi*2^ReportByteRows.d (params d s)+a.lo := by
  rw [D.packet]
  change (if op<writeOp (params d s) then indexedPair (params d s) a else 0)=_
  rw [if_pos R]
  change a.lo+2^ReportByteRows.d (params d s)*a.hi=a.hi*2^ReportByteRows.d (params d s)+a.lo
  rw [Nat.mul_comm (2^ReportByteRows.d (params d s)),Nat.add_comm]

#print axioms Sample.ready
#print axioms reply_payload
end L4.ReportIndexedReadLedger
