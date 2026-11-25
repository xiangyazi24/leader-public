import Leader.L4.BStarStopLedger
import Leader.L4.BStarBitPhysicalSwap
import Leader.L4.Height.Couple

namespace L4.BStarPhysicalPairLaw
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
open AllSizeProtocol BStarTrace BStarLongWork BStarLongClaims BStarLongLayout
open BStarH6WordChart BStarH6Ordinal BStarAcquireVisitOrder BStarClearanceRaceMark
open BStarBitParity BStarBitLabelSwap BStarLongToken BStarLongCommand BStarResetMarkAdapter
open BStarPhysicalIncrementLedger BStarIncrementLedger
open L4.Height L4.Height.Couple
open Classical

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "run" => BStarResetSchedule.run (AllSizeS1Geometry.step B)

/-- Exact old-state fresh BIT flags, before either incident edge acts. -/
def Fresh (base : X) (hh : ∃ i,oldH6 B base i=true) (old : X) (i : Fin n) : Prop :=
  oldOrdinal B base hh i=4 ∧
    ∃ p, atSite (old i).long 1=.forward p ∧
      p.fault=0 ∧ p.opcode.toNat=bitOp ∧ p.race=1 ∧ p.outcome=0 ∧ p.argument=0

noncomputable def mate (base : X) (hh : ∃ i,oldH6 B base i=true) (old : X) :
    Fin n→Fin n := swap (Fresh hp base hh old)

theorem mate_twice (base : X) (hh : ∃ i,oldH6 B base i=true) (old : X) (e : Fin n) :
    mate hp base hh old (mate hp base hh old e)=e :=
  swap_twice hh _ (fun _ H=>H.1) e

abbrev Key (n : Nat) := Fin n × Nat

/-- An old-key function can use the entire previous raw tape, never
the selected new letter. `owner` names the chart's COMMIT center. -/
noncomputable def reveal (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (owner : Fin n→Fin n) (start : Fin n→Nat)
    (past : List (Fin n)) (e : Fin n) : Option (Key n × Bool) := by
  classical
  let old := run x past
  exact if H : ∃ z, Witness (Fresh hp base hh old) e z then
    let z := Classical.choose H
    let i := owner z.1
    some ((i,count start (tapeInc hp base hh x past) i past.length),firstBit z.2)
  else none

theorem reveal_incident (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (owner : Fin n→Fin n) (start : Fin n→Nat)
    (past : List (Fin n)) (gate : Fin n) (s : Side) (F : Fresh hp base hh (run x past) gate) :
    reveal hp base hh x owner start past (incident gate s)=
      some ((owner gate,count start (tapeInc hp base hh x past) (owner gate) past.length),firstBit s) := by
  classical
  have H : ∃ z,Witness (Fresh hp base hh (run x past)) (incident gate s) z := ⟨(gate,s),F,rfl⟩
  unfold reveal
  rw [dif_pos H]
  have E := witness_unique hh _ (fun _ A=>A.1) (Classical.choose_spec H)
    (show Witness (Fresh hp base hh (run x past)) (incident gate s) (gate,s) from ⟨F,rfl⟩)
  rw [E]

theorem reveal_mate (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (owner : Fin n→Fin n) (start : Fin n→Nat) (past : List (Fin n))
    (e : Fin n) (k : Key n) (bit : Bool)
    (H : reveal hp base hh x owner start past e=some (k,bit)) :
    reveal hp base hh x owner start past (mate hp base hh (run x past) e)=some (k,!bit) := by
  classical
  by_cases W : ∃ z,Witness (Fresh hp base hh (run x past)) e z
  · obtain ⟨⟨gate,s⟩,F,E⟩ := W
    change incident gate s=e at E
    subst e
    have M : mate hp base hh (run x past) (incident gate s)=incident gate (other s) :=
      swap_incident hh _ (fun _ A=>A.1) F s
    rw [reveal_incident hp base hh x owner start past gate s F] at H
    have equal := Option.some.inj H
    have A : _=k := congrArg Prod.fst equal
    have D : firstBit s=bit := congrArg Prod.snd equal
    rw [←A,←D,M,
      reveal_incident hp base hh x owner start past gate (other s) F]
    cases s <;> rfl
  · have E : reveal hp base hh x owner start past e=none := by
      exact dif_neg W
    rw [E] at H
    cases H

/-- Two copies allow use of the accepted even-alphabet interface
without restricting the size of the real raw scheduler alphabet. -/
def rawLabel {n : Nat} : Fin (n+n) → Fin n := Fin.addCases id id

def doubleMate {n : Nat} (σ : Fin n→Fin n) : Fin (n+n)→Fin (n+n) :=
  Fin.addCases (fun e=>Fin.castAdd n (σ e)) (fun e=>Fin.natAdd n (σ e))

theorem raw_doubleMate {n : Nat} (σ : Fin n→Fin n) (e : Fin (n+n)) :
    rawLabel (doubleMate σ e)=σ (rawLabel e) := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) e <;>
    simp only [doubleMate,rawLabel,Fin.addCases_left,Fin.addCases_right,id_eq]

theorem doubleMate_twice {n : Nat} (σ : Fin n→Fin n) (invol : ∀ e,σ (σ e)=e)
    (e : Fin (n+n)) : doubleMate σ (doubleMate σ e)=e := by
  refine Fin.addCases (fun i=>?_) (fun i=>?_) e <;>
    simp only [doubleMate,Fin.addCases_left,Fin.addCases_right,invol]

noncomputable def source (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (owner : Fin n→Fin n) (start : Fin n→Nat) :
    PairedSource (List (Fin n)) (Key n) (n+n) where
  next past e := past++[rawLabel e]
  bitOf past e := reveal hp base hh x owner start past (rawLabel e)
  flip past := doubleMate (mate hp base hh (run x past))
  half := n
  alphabet_even := by omega
  flip_invol past := doubleMate_twice _ (mate_twice hp base hh (run x past))
  flip_reveal past e k b H := by
    rw [raw_doubleMate]
    exact reveal_mate hp base hh x owner start past (rawLabel e) k b H

/-- The accepted finite prescribed-mass theorem with the literal
old-state BIT selector, conditional on the supplied gate-owner map. -/
theorem physical_prescribed_bound (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (owner : Fin n→Fin n) (start : Fin n→Nat) (history : List (Fin n))
    (keys : List (Key n)) (distinct : keys.Nodup) (wanted : Key n→Bool) (t : Nat) :
    2^keys.length * wordSum
      (fun w=>if FirstPrescribed (source hp base hh x owner start) wanted history keys w
        then 1 else 0) t ≤ (n+n)^t := by
  classical
  exact adaptive_prescribed _ wanted history keys distinct t

open BStarAcquireAnchors BStarGeneratedOwner BStarAcquireLiteralChain BStarResetChartTouch

/-- The physical owner map is the unique H6 header with the gate's
K1 owner; not a key or owner supplied by a future publication. -/
noncomputable def ownerAt (base : X) (hh : ∃ i,oldH6 B base i=true) (gate : Fin n) : Fin n :=
  let h := oldH6 B base
  let key := commandOwner h gate 1
  let range := commandOwner_range h hh gate 1
  (Classical.choose (unique_command_header h hh key range.1 range.2 1)).val

theorem ownerAt_center (base : X) (hh : ∃ i,oldH6 B base i=true)
    (gate center : Fin n) (head : oldH6 B base center=true)
    (sameOwner : commandOwner (oldH6 B base) gate 1=commandOwner (oldH6 B base) center 1) :
    ownerAt hp base hh gate=center := by
  let h := oldH6 B base
  let key := commandOwner h gate 1
  let range := commandOwner_range h hh gate 1
  let spec := Classical.choose_spec (unique_command_header h hh key range.1 range.2 1)
  exact congrArg Subtype.val (spec.2 ⟨center,head⟩ sameOwner.symm).symm

/-- At a generated fresh gate, the two labels used by the source
actually store opposite first-side codes in the selected physical row. -/
theorem mate_writes_opposite {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (fixed : ∀ i,oldH6 B x i=oldH6 B base i)
    (offset : BStarClearanceOffset.correct (oldH6 B base) hh 5 x)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (k : Nat) (idx : S.getD k fall=(i,1))
    (now : Current hp base (fun j=>S.getD j fall) len x (.busy bitOp (.out k)))
    (F : Fresh hp base hh x i) (s : Side) :
    let step := AllSizeS1Geometry.step B
    ∃ v : Payload, atSite (step x (incident i s) i).long 1=.forward {v with race:=firstCode s} ∧
      atSite (step x (mate hp base hh x (incident i s)) i).long 1=
        .forward {v with race:=firstCode (other s)} ∧
      firstBit (other s)= !(firstBit s) := by
  have W : BStarBitPhysicalSwap.Ready hp base hh x i := by
    obtain ⟨ord,v,raw,nofault,opcode,race,outcome,arg⟩ := F
    have admitted := (BStarBitGateGeometry.bit_gate_iff hp hh fixed offset i 1).mpr ⟨rfl,ord⟩
    have decoded : bind (longGeometry B (x i)) 1 (.forward v)=.forward v := by
      have range : 1≤v.race.toNat ∧ v.race.toNat≤5 := by rw [race]; decide
      cases v
      simp_all [BStarLongCommand.bind,bitOp,forwardWidth,admit,cropped,low]
    exact ⟨ord,v,by rw [raw]; exact decoded,nofault,opcode,race⟩
  have E : mate hp base hh x (incident i s)=incident i (other s) :=
    swap_incident hh _ (fun _ H=>H.1) F s
  have M : BStarBitPhysicalSwap.paired hp base hh x (incident i s)=incident i (other s) :=
    swap_incident hh _ (fun _ H=>H.1) W s
  rw [E,←M]
  exact BStarBitPhysicalSwap.paired_first hp C fixed offset sep i k idx now W s

open BStarNeedPrefixFresh

/-- A fresh raw observation at a chart's gate is exactly the raw
old-byte predicate used by the deterministic pairing. -/
theorem raw_at_chart (base old : X) (hh : ∃ i,oldH6 B base i=true)
    (addr : Nat→Pos n) (g : Nat) (gate e : Fin n) (idx : addr g=(gate,1))
    (ord : oldOrdinal B base hh gate=4) :
    RawFirstRead addr g old e ↔
      ∃ s, Fresh hp base hh old gate ∧ incident gate s=e := by
  have proj : project addr old g=atSite (old gate).long 1 := by
    unfold project
    rw [idx]
    rfl
  constructor
  · rintro ⟨v,raw,fault,opcode,race,outcome,arg,L|R⟩
    · exact ⟨.left,⟨ord,v,proj.symm ▸ raw,fault,opcode,race,outcome,arg⟩,
        by rw [idx] at L; exact L.symm⟩
    · exact ⟨.right,⟨ord,v,proj.symm ▸ raw,fault,opcode,race,outcome,arg⟩,
        by rw [idx] at R; exact R.symm⟩
  · rintro ⟨s,F,E⟩
    obtain ⟨_,v,raw,fault,opcode,race,outcome,arg⟩ := F
    refine ⟨v,proj.trans raw,fault,opcode,race,outcome,arg,?_⟩
    rw [idx]
    cases s
    · exact .inl E.symm
    · exact .inr E.symm

/-- The selected index for a chart read is the canonical physical
COMMIT owner's key, evaluated before the incident label. -/
theorem chart_reveal (base x : X) (hh : ∃ i,oldH6 B base i=true)
    (start : Fin n→Nat) (past : List (Fin n))
    (addr : Nat→Pos n) (g : Nat) (gate center e : Fin n) (idx : addr g=(gate,1))
    (ord : oldOrdinal B base hh gate=4) (head : oldH6 B base center=true)
    (sameOwner : commandOwner (oldH6 B base) gate 1=commandOwner (oldH6 B base) center 1)
    (reads : RawFirstRead addr g (run x past) e) :
    ∃ s, incident gate s=e ∧
      reveal hp base hh x (ownerAt hp base hh) start past e=
        some ((center,count start (tapeInc hp base hh x past) center past.length),firstBit s) := by
  obtain ⟨s,F,E⟩ := (raw_at_chart hp base (run x past) hh addr g gate e idx ord).mp reads
  refine ⟨s,E,?_⟩
  rw [←E,reveal_incident hp base hh x (ownerAt hp base hh) start past gate s F,
    ownerAt_center hp base hh gate center head sameOwner]

def firstRaw {n : Nat} (obs : List (Fin n)→Fin n→Option (Key n × Bool))
    (key : Key n) : List (Fin n)→List (Fin n)→Option Bool
  | _, [] => none
  | past,e::tail => match obs past e with
    | none => firstRaw obs key (past++[e]) tail
    | some (j,b) => if j=key then some b else firstRaw obs key (past++[e]) tail

def RawPrescribed {n : Nat} (obs : List (Fin n)→Fin n→Option (Key n × Bool))
    (wanted : Key n→Bool) (history : List (Fin n)) (keys : List (Key n)) (w : List (Fin n)) : Prop :=
  ∀ k,k∈keys→firstRaw obs k history w=some (wanted k)

theorem firstReveal_projects (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (owner : Fin n→Fin n) (start : Fin n→Nat) (k : Key n)
    (w : List (Fin (n+n))) (history : List (Fin n)) :
    firstReveal (source hp base hh x owner start) k history w =
      firstRaw (reveal hp base hh x owner start) k history (w.map rawLabel) := by
  induction w generalizing history with
  | nil => rfl
  | cons e w ih =>
    simp only [firstReveal,List.map_cons,firstRaw,source]
    cases H : reveal hp base hh x owner start history (rawLabel e) with
    | none => exact ih _
    | some kv =>
      obtain ⟨j,b⟩ := kv
      change (if j=k then some b else firstReveal (source hp base hh x owner start) k
        (history++[rawLabel e]) w) = _
      rw [ih]

private theorem sum_scale (c : Nat) (l : List Nat) : (l.map (c * ·)).sum=c*l.sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,Nat.mul_add]

/-- Each real raw word has exactly 2^t copies; projection preserves
finite event mass after dividing by this factor. -/
theorem doubled_wordSum {n : Nat} (f : List (Fin n)→Nat) (t : Nat) :
    wordSum (fun w=>f (w.map rawLabel)) t=2^t*wordSum f t := by
  induction t generalizing f with
  | zero => simp [wordSum]
  | succ t ih =>
    simp only [wordSum,List.map_cons]
    rw [List.ofFn_add]
    have uncast (i : Fin n) : rawLabel (i.castLE (Nat.le_add_right n n))=i :=
      Fin.addCases_left (motive:=fun _=>Fin n) i
    have right (i : Fin n) : rawLabel (Fin.natAdd n i)=i :=
      Fin.addCases_right (motive:=fun _=>Fin n) i
    simp only [uncast,right,List.sum_append]
    have trim : (List.ofFn (fun e : Fin n =>
      wordSum (fun w=>f (e::w.map rawLabel)) t)).sum =
      2^t*(List.ofFn (fun e : Fin n=>wordSum (fun w=>f (e::w)) t)).sum := by
      have eq : (List.ofFn (fun e : Fin n=>wordSum (fun w=>f (e::w.map rawLabel)) t)) =
          (List.ofFn (fun e : Fin n=>2^t*wordSum (fun w=>f (e::w)) t)) := by
        congr 1
        funext e
        exact ih (fun w=>f (e::w))
      rw [eq]
      let g := fun e : Fin n=>wordSum (fun w=>f (e::w)) t
      have mapped : List.ofFn (fun e=>2^t*g e) = (List.ofFn g).map (2^t * ·) := by
        simpa only [Function.comp_def] using
          (List.map_ofFn (f:=g) (g:=(2^t * ·))).symm
      change (List.ofFn (fun e=>2^t*g e)).sum=2^t*(List.ofFn g).sum
      rw [mapped,sum_scale]
    rw [trim,Nat.pow_succ]
    rw [Nat.mul_comm (2^t) 2, Nat.mul_assoc, Nat.two_mul]

/-- Counting theorem on the original n-letter alphabet, including
odd n. No claim that every requested key occurs by horizon t. -/
theorem raw_prescribed_bound (base : X) (hh : ∃ i,oldH6 B base i=true)
    (x : X) (start : Fin n→Nat) (history : List (Fin n))
    (keys : List (Key n)) (distinct : keys.Nodup) (wanted : Key n→Bool) (t : Nat) :
    2^keys.length * wordSum
      (fun w=>if RawPrescribed (reveal hp base hh x (ownerAt hp base hh) start) wanted history keys w
        then 1 else 0) t ≤ n^t := by
  let owner := ownerAt hp base hh
  let f : List (Fin n)→Nat := fun w=>
    if RawPrescribed (reveal hp base hh x owner start) wanted history keys w then 1 else 0
  have bound := physical_prescribed_bound hp base hh x owner start history keys distinct wanted t
  have proj : wordSum (fun w=>if FirstPrescribed (source hp base hh x owner start) wanted history keys w
      then 1 else 0) t = wordSum (fun w=>f (w.map rawLabel)) t := by
    apply wordSum_congr
    intro w
    have agree : FirstPrescribed (source hp base hh x owner start) wanted history keys w ↔
        RawPrescribed (reveal hp base hh x owner start) wanted history keys (w.map rawLabel) := by
      unfold FirstPrescribed RawPrescribed
      simp only [firstReveal_projects]
    unfold f
    by_cases H : RawPrescribed (reveal hp base hh x owner start) wanted history keys (w.map rawLabel)
    · rw [if_pos H,if_pos (agree.mpr H)]
    · rw [if_neg H,if_neg (fun Y=>H (agree.mp Y))]
  rw [proj,doubled_wordSum,←Nat.two_mul,Nat.mul_pow,
    Nat.mul_left_comm (2^keys.length) (2^t)] at bound
  exact Nat.le_of_mul_le_mul_left bound (Nat.pow_pos (by decide))

end L4.BStarPhysicalPairLaw
