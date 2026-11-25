import Leader.L4.Compiler.StagesView
import Leader.L4.Compiler.GeneratedEditBridge

/-! Concrete S8–S10 composition at 226, 233, 243 and 253.
The input file exposes the preceding decoded clocks and snapshots;
later stages can recover the preserved prefix without re-evaluation. -/
namespace L4.Compiler.Native
open Interp

def readSnapshot (regs : List Value) (x d z p h home role approve : Nat)
    (s : Snapshot) : Prop :=
  readReg regs x = .word s.x ∧ readReg regs d = .word s.d ∧
  readReg regs z = .word s.z ∧ readReg regs p = .word s.proposal ∧
  readReg regs h = .boolean s.anchor ∧ readReg regs home = .boolean s.home ∧
  readReg regs role = .boolean s.role ∧ readReg regs approve = .boolean s.approve

def snapshotBound (r : Nat) (s : Snapshot) : Prop :=
  s.x<modulus r ∧ s.d<modulus r ∧ s.z<modulus r ∧ s.proposal<modulus r

theorem snapshotBound_of_record (r : Nat) (bank : Bank) (side : Fin 3) (old : Bool) :
    snapshotBound r (if old then (decodeBank r bank side).prior else
      (decodeBank r bank side).curr) := by
  have hM : heightMod r≤modulus r :=
    Nat.pow_le_pow_right (by decide : 0<16) (by omega)
  have hb := (native_record_bounds r bank side).2
  cases old
  · obtain ⟨x,d,z,p⟩ := hb.2
    exact ⟨Nat.lt_of_lt_of_le x hM,Nat.lt_of_lt_of_le d hM,z,Nat.lt_of_lt_of_le p hM⟩
  · obtain ⟨x,d,z,p⟩ := hb.1
    exact ⟨Nat.lt_of_lt_of_le x hM,Nat.lt_of_lt_of_le d hM,z,Nat.lt_of_lt_of_le p hM⟩

theorem neighborView_bounds (r : Nat) (bank : Bank) (side : Fin 3) (t : Nat) :
    snapshotBound r (neighborView t (decodeBank r bank side)) := by
  unfold neighborView
  split
  · exact snapshotBound_of_record r bank side false
  · exact snapshotBound_of_record r bank side true

theorem readSnapshot_prefix {r : Nat} (T : PrimTable r) (bank : Bank)
    (regs : List Value) (cs : List Code) (x d z p h home role approve : Nat)
    (s : Snapshot)
    (hx : x<regs.length) (hd : d<regs.length) (hz : z<regs.length) (hp : p<regs.length)
    (hh : h<regs.length) (hhm : home<regs.length) (hr : role<regs.length)
    (ha : approve<regs.length)
    (inRegs : readSnapshot regs x d z p h home role approve s) :
    readSnapshot (runCodes T bank regs cs) x d z p h home role approve s := by
  simpa only [readSnapshot,runCodes_prefix _ _ _ _ _ hx,runCodes_prefix _ _ _ _ _ hd,
    runCodes_prefix _ _ _ _ _ hz,runCodes_prefix _ _ _ _ _ hp,runCodes_prefix _ _ _ _ _ hh,
    runCodes_prefix _ _ _ _ _ hhm,runCodes_prefix _ _ _ _ _ hr,runCodes_prefix _ _ _ _ _ ha]
    using inRegs

theorem stageView_snapshot {r : Nat} (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (base : Nat) (hlen : regs.length=base)
    (ty t cx cd cz cp ch chm cr ca ox od oz op oh ohm orl oa : Nat)
    (hty : ty<base) (ht : t<base) (hcx : cx<base) (hcd : cd<base) (hcz : cz<base)
    (hcp : cp<base) (hch : ch<base) (hchm : chm<base) (hcr : cr<base) (hca : ca<base)
    (hox : ox<base) (hod : od<base) (hoz : oz<base) (hop : op<base) (hoh : oh<base)
    (hohm : ohm<base) (horl : orl<base) (hoa : oa<base)
    (y : NativeRecord) (tv : Nat)
    (hy : readReg regs ty = .word y.tick) (hv : readReg regs t = .word tv)
    (hc : readSnapshot regs cx cd cz cp ch chm cr ca y.curr)
    (ho : readSnapshot regs ox od oz op oh ohm orl oa y.prior)
    (byv : y.tick<modulus r) (btv : tv<modulus r)
    (bc : snapshotBound r y.curr) (bo : snapshotBound r y.prior) :
    readSnapshot
      (runCodes T bank regs (stageView base ty t cx cd cz cp ch chm cr ca ox od oz op oh ohm orl oa))
      (base+2) (base+3) (base+4) (base+5) (base+6) (base+7) (base+8) (base+9)
      (neighborView tv y) := by
  obtain ⟨x,d,z,p,h,hm,rl,ap⟩ := hc
  obtain ⟨x',d',z',p',h',hm',rl',ap'⟩ := ho
  obtain ⟨bx,bd,bz,bp⟩ := bc
  obtain ⟨bx',bd',bz',bp'⟩ := bo
  have S := stageView_spec T bank hT regs base hlen ty t cx cd cz cp ch chm cr ca ox od oz op oh ohm orl oa
    hty ht hcx hcd hcz hcp hch hchm hcr hca hox hod hoz hop hoh hohm horl hoa
    y.tick tv y.curr.x y.curr.d y.curr.z y.curr.proposal
    y.prior.x y.prior.d y.prior.z y.prior.proposal
    y.curr.anchor y.curr.home y.curr.role y.curr.approve y.prior.anchor y.prior.home
    y.prior.role y.prior.approve hy hv x d z p h hm rl ap x' d' z' p' h' hm' rl' ap'
    byv btv bx bd bz bp bx' bd' bz' bp'
  by_cases e : y.tick=tv
  · simpa only [neighborView,readSnapshot,if_pos e] using S
  · simpa only [neighborView,readSnapshot,if_neg e] using S

def viewLeft : List Code :=
  stageView 233 29 58 33 34 14 35 21 22 23 24 30 31 10 32 17 18 19 20

def viewRight : List Code :=
  stageView 243 87 58 91 92 72 93 79 80 81 82 88 89 68 90 75 76 77 78

def viewCodes : List Code :=
  stagePhase 226 58 ++ viewLeft ++ viewRight ++ stageNeed 253 137 160 204 217 228 50 43 0

/-- Phase flags are true at exactly the six designated phases, but
the scanned phase itself still ranges over all 32 values. -/
def readPhases (regs : List Value) (phase : Nat) : Prop :=
  ∀ j : Fin 6, readReg regs (227+j.val) = .boolean (decide (phase=j.val))

theorem phase_read {r : Nat} (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (hlen : regs.length=226) (t : Nat)
    (v : readReg regs 58=.word t) (b : t<modulus r) :
    readPhases (runCodes T bank regs (stagePhase 226 58)) (t%32) := by
  have H := stagePhase_spec T bank hT regs 226 hlen 58 (by decide) t v b
  intro j
  obtain ⟨i,hi⟩ := j
  have e : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 := by omega
  rcases e with rfl|rfl|rfl|rfl|rfl|rfl
  · exact H.2.1
  · exact H.2.2.1
  · exact H.2.2.2.1
  · exact H.2.2.2.2.1
  · exact H.2.2.2.2.2.1
  · exact H.2.2.2.2.2.2

/-- Old, already decoded inputs to the concrete view segment. -/
structure ViewInput (r : Nat) (bank : Bank) (regs : List Value)
    (rs pr cl ic : Bool) : Prop where
  len : regs.length=226
  cTick : readReg regs 58=.word (decodeBank r bank 1).tick
  lTick : readReg regs 29=.word (decodeBank r bank 0).tick
  rTick : readReg regs 87=.word (decodeBank r bank 2).tick
  lp : readSnapshot regs 30 31 10 32 17 18 19 20 (decodeBank r bank 0).prior
  lc : readSnapshot regs 33 34 14 35 21 22 23 24 (decodeBank r bank 0).curr
  rp : readSnapshot regs 88 89 68 90 75 76 77 78 (decodeBank r bank 2).prior
  rc : readSnapshot regs 91 92 72 93 79 80 81 82 (decodeBank r bank 2).curr
  cz : readReg regs 43=.word (decodeBank r bank 1).curr.z
  ca : readReg regs 50=.boolean (decodeBank r bank 1).curr.anchor
  zero : readReg regs 0=.word 0
  hrs : readReg regs 137=.boolean rs
  hpr : readReg regs 160=.boolean pr
  hcl : readReg regs 204=.boolean cl
  hic : readReg regs 217=.boolean ic

structure ViewOutput (r : Nat) (bank : Bank) (regs : List Value)
    (rs pr cl ic : Bool) : Prop where
  len : regs.length=264
  phase : readPhases regs ((decodeBank r bank 1).tick%32)
  left : readSnapshot regs 235 236 237 238 239 240 241 242
    (neighborView (decodeBank r bank 1).tick (decodeBank r bank 0))
  right : readSnapshot regs 245 246 247 248 249 250 251 252
    (neighborView (decodeBank r bank 1).tick (decodeBank r bank 2))
  need : readReg regs 263 = .boolean
    (!rs && !pr && !cl && ic && decide ((decodeBank r bank 1).tick%32=1) &&
      (decodeBank r bank 1).curr.anchor && decide ((decodeBank r bank 1).curr.z=0))

set_option maxHeartbeats 1000000 in
theorem view_spec {r : Nat} (T : PrimTable r) (bank : Bank) (hT : PrimSem T bank)
    (regs : List Value) (rs pr cl ic : Bool) (h : ViewInput r bank regs rs pr cl ic) :
    ViewOutput r bank (runCodes T bank regs viewCodes) rs pr cl ic := by
  let C := decodeBank r bank 1
  let L := decodeBank r bank 0
  let R := decodeBank r bank 2
  let A := runCodes T bank regs (stagePhase 226 58)
  let B := runCodes T bank A viewLeft
  let D := runCodes T bank B viewRight
  let E := runCodes T bank D (stageNeed 253 137 160 204 217 228 50 43 0)
  have aLen : A.length=233 := by
    change (runCodes T bank regs _).length=_
    rw [runCodes_length,h.len]
    rfl
  have bLen : B.length=243 := by
    change (runCodes T bank A _).length=_
    rw [runCodes_length,aLen]
    rfl
  have dLen : D.length=253 := by
    change (runCodes T bank B _).length=_
    rw [runCodes_length,bLen]
    rfl
  have eLen : E.length=264 := by
    change (runCodes T bank D _).length=_
    rw [runCodes_length,dLen]
    rfl
  have ah (i : Nat) (hi : i<226) : readReg A i=readReg regs i :=
    runCodes_prefix _ _ _ _ _ (by rwa [h.len])
  have bh (i : Nat) (hi : i<233) : readReg B i=readReg A i :=
    runCodes_prefix _ _ _ _ _ (by rwa [aLen])
  have dh (i : Nat) (hi : i<243) : readReg D i=readReg B i :=
    runCodes_prefix _ _ _ _ _ (by rwa [bLen])
  have eh (i : Nat) (hi : i<253) : readReg E i=readReg D i :=
    runCodes_prefix _ _ _ _ _ (by rwa [dLen])
  have aPh := phase_read T bank hT regs h.len C.tick h.cTick (native_record_bounds r bank 1).1
  have aLc : readSnapshot A 33 34 14 35 21 22 23 24 L.curr := by
    simpa only [readSnapshot, ah _ (by decide : 33<226), ah _ (by decide : 34<226),
      ah _ (by decide : 14<226), ah _ (by decide : 35<226),
      ah _ (by decide : 21<226), ah _ (by decide : 22<226),
      ah _ (by decide : 23<226), ah _ (by decide : 24<226)] using h.lc
  have aLp : readSnapshot A 30 31 10 32 17 18 19 20 L.prior := by
    simpa only [readSnapshot, ah _ (by decide : 30<226), ah _ (by decide : 31<226),
      ah _ (by decide : 10<226), ah _ (by decide : 32<226),
      ah _ (by decide : 17<226), ah _ (by decide : 18<226),
      ah _ (by decide : 19<226), ah _ (by decide : 20<226)] using h.lp
  have bOld (i : Nat) (hi : i<226) : readReg B i=readReg regs i :=
    (bh i (by omega)).trans (ah i hi)
  have bRc : readSnapshot B 91 92 72 93 79 80 81 82 R.curr := by
    simpa only [readSnapshot, bOld _ (by decide : 91<226), bOld _ (by decide : 92<226),
      bOld _ (by decide : 72<226), bOld _ (by decide : 93<226),
      bOld _ (by decide : 79<226), bOld _ (by decide : 80<226),
      bOld _ (by decide : 81<226), bOld _ (by decide : 82<226)] using h.rc
  have bRp : readSnapshot B 88 89 68 90 75 76 77 78 R.prior := by
    simpa only [readSnapshot, bOld _ (by decide : 88<226), bOld _ (by decide : 89<226),
      bOld _ (by decide : 68<226), bOld _ (by decide : 90<226),
      bOld _ (by decide : 75<226), bOld _ (by decide : 76<226),
      bOld _ (by decide : 77<226), bOld _ (by decide : 78<226)] using h.rp
  have bL : readSnapshot B 235 236 237 238 239 240 241 242 (neighborView C.tick L) := by
    exact stageView_snapshot T bank hT A 233 aLen 29 58 33 34 14 35 21 22 23 24
      30 31 10 32 17 18 19 20
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      L C.tick ((ah 29 (by decide)).trans h.lTick) ((ah 58 (by decide)).trans h.cTick)
      aLc aLp (native_record_bounds r bank 0).1 (native_record_bounds r bank 1).1
      (snapshotBound_of_record r bank 0 false) (snapshotBound_of_record r bank 0 true)
  have dR : readSnapshot D 245 246 247 248 249 250 251 252 (neighborView C.tick R) := by
    exact stageView_snapshot T bank hT B 243 bLen 87 58 91 92 72 93 79 80 81 82
      88 89 68 90 75 76 77 78
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      R C.tick ((bOld 87 (by decide)).trans h.rTick) ((bOld 58 (by decide)).trans h.cTick)
      bRc bRp (native_record_bounds r bank 2).1 (native_record_bounds r bank 1).1
      (snapshotBound_of_record r bank 2 false) (snapshotBound_of_record r bank 2 true)
  have dPh : readPhases D (C.tick%32) := by
    intro j
    have jl := j.isLt
    rw [dh _ (by omega),bh _ (by omega)]
    exact aPh j
  have dOld (i : Nat) (hi : i<226) : readReg D i=readReg regs i :=
    (dh i (by omega)).trans (bOld i hi)
  have need :=
    stageNeed_spec T bank hT D 253 dLen 137 160 204 217 228 50 43 0
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      rs pr cl ic (decide (C.tick%32=1)) C.curr.anchor C.curr.z
      ((dOld 137 (by decide)).trans h.hrs) ((dOld 160 (by decide)).trans h.hpr)
      ((dOld 204 (by decide)).trans h.hcl) ((dOld 217 (by decide)).trans h.hic)
      (dPh 1) ((dOld 50 (by decide)).trans h.ca) ((dOld 43 (by decide)).trans h.cz)
      ((dOld 0 (by decide)).trans h.zero) (native_record_bounds r bank 1).2.2.2.2.1
  have runEq : runCodes T bank regs viewCodes=E := by
    simp only [viewCodes,List.append_assoc,runCodes_append]
    rfl
  rw [runEq]
  refine ⟨eLen,?_,?_,?_,need⟩
  · intro j
    have jl := j.isLt
    rw [eh _ (by omega)]
    exact dPh j
  · exact readSnapshot_prefix T bank D _ _ _ _ _ _ _ _ _ _
      (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide)
      (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide)
      (readSnapshot_prefix T bank B _ _ _ _ _ _ _ _ _ _
        (by rw [bLen]; decide) (by rw [bLen]; decide) (by rw [bLen]; decide) (by rw [bLen]; decide)
        (by rw [bLen]; decide) (by rw [bLen]; decide) (by rw [bLen]; decide) (by rw [bLen]; decide) bL)
  · exact readSnapshot_prefix T bank D _ _ _ _ _ _ _ _ _ _
      (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide)
      (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide) (by rw [dLen]; decide) dR

end L4.Compiler.Native
