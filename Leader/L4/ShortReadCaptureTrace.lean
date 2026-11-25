import Leader.L4.ShortReadFlight
import Leader.L4.ShortReadCaptureBits
import Leader.L4.ShortReadCaptureGeometry

namespace L4.ShortReadCaptureTrace
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetCycle ShortResetChart ShortResetForwardH2
open ShortReadForward ShortReadFlight ShortReadCaptureBits ShortResetRow

structure Sample (s n : Nat) where
  old : Raw s n
  edge : Fin n

abbrev Ledger (s n : Nat) := Fin 3 → Option (Sample s n)

def push {s n : Nat} (a : Ledger s n) (x : Raw s n) (e : Fin n) (j : Fin 3) :
    Ledger s n := fun k=>if k=j ∧ wins x e j=true then some ⟨x,e⟩ else a k

def select {s n : Nat} (samp : Option (Sample s n)) : Bool :=
  match samp with
  | none => false
  | some p => seenSelector p.old p.edge

def value {s n : Nat} (samp : Option (Sample s n)) : Bool :=
  match samp with
  | none => false
  | some p => seenValue p.old p.edge

def Bits {s n : Nat} (a : Ledger s n) (d : Nat) : Prop :=
  ∀ j : Fin 3, bitAt d (5-j.val)=select (a j) ∧ bitAt d (2-j.val)=value (a j)

def Covers {s n : Nat} {h : Fin n → Bool} (C : Chart h) (a : Ledger s n) (i : Nat) : Prop :=
  ∀ k<i, h (nextAt C.root k)=true → (a (C.route.port k)).isSome=true

def advanceLedger {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (f : Flight) (a : Ledger s n) : Ledger s n :=
  match f with
  | .forward i _ => if e=nextAt C.root i then push a x e (C.route.port i) else a
  | _ => a

/-- While a successful return is still possible, all visited old
headers contributed winning samples, and their two payload bits
are exactly those recorded on those actual marks. -/
def Good {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (a : Ledger s n) : Flight → Prop
  | .forward i d => bitAt d 6=true → Bits a d ∧ Covers C a i
  | .returning _ ok d | .consumed ok d => ok=true → Bits a d.val ∧ Covers C a C.L

private theorem covers_push {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (a : Ledger s n) (x : Raw s n) (e : Fin n) (i : Nat)
    (pos : e=nextAt C.root i) (head : header x e=h e)
    (keep : (!header x e || wins x e (C.route.port i))=true)
    (old : Covers C a i) : Covers C (push a x e (C.route.port i)) (i+1) := by
  intro k K H
  by_cases L : k=i
  · subst k
    have X : header x e=true := head.trans (pos.symm ▸ H)
    have A : wins x e (C.route.port i)=true := by simpa [X] using keep
    simp [push,A]
  · have M := old k (by omega) H
    unfold push
    split
    · rfl
    · exact M

private theorem init_bits : ∀ j : Fin 3, bitAt 64 (5-j.val)=false ∧ bitAt 64 (2-j.val)=false := by
  decide

theorem initial {s n : Nat} {h : Fin n → Bool} (C : Chart h) :
    Good (s:=s) C (fun _=>none) (.forward 0 64) := by
  intro _
  refine ⟨init_bits,?_⟩
  intro _ K
  omega

private theorem data_at_front {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (i d : Nat) (E : e=nextAt C.root i)
    (F : Forward C.route x i d) :
    oldK (header x e) (x e).mis1 (C.route.port i)=readFront d := by
  rw [E]
  exact slot_of_bits C.route x i _ (fun g=>decode_front g d F.2.1) F.2.2.2.2.1

private theorem terminal_datum {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3)
    (d : Nat) (F : oldK (header x e) (x e).mis1 j=readFront d)
    (S : ((replyPacket x e j).outcome==0)=true) :
    (datum (replyPacket x e j)).val=(replyPacket x e j).payload := by
  obtain ⟨b,p,H⟩ := reply_canonical x e j d F
  cases b
  · rw [H] at S
    contradiction
  · rw [H]
    exact Nat.mod_eq_of_lt p.isLt

def trace {s n : Nat} {h : Fin n → Bool} (C : Chart h) :
    Raw s n → Flight → Ledger s n → List (Fin n) → Ledger s n
  | _, _, a, [] => a
  | x, f, a, e::w =>
      trace C (rawNext s x e) (ShortReadFlight.next C x e f) (advanceLedger C x e f a) w

private theorem bits_push {s n : Nat} (a : Ledger s n)
    (x : Raw s n) (e : Fin n) (j : Fin 3) (d q : Nat)
    (A : Bits a d) (B : ∀ i : Fin 6, bitAt q i.val=updateBit x e j d i) :
    Bits (push a x e j) q := by
  intro k
  have J := j.isLt
  have K := k.isLt
  have S := B ⟨5-k.val,by omega⟩
  have T := B ⟨2-k.val,by omega⟩
  change bitAt q (5-k.val)=updateBit x e j d ⟨5-k.val,by omega⟩ at S
  change bitAt q (2-k.val)=updateBit x e j d ⟨2-k.val,by omega⟩ at T
  rw [S,T]
  by_cases E : wins x e j=true
  · by_cases Eq : k=j
    · subst k
      have diff : 2-j.val≠5-j.val := by omega
      simp [push,updateBit,E,diff,select,value]
    · have diff : k.val≠j.val := fun D=>Eq (Fin.ext D)
      have s0 : 5-k.val≠5-j.val := by omega
      have s1 : 5-k.val≠2-j.val := by omega
      have v0 : 2-k.val≠5-j.val := by omega
      have v1 : 2-k.val≠2-j.val := by omega
      simpa [push,updateBit,E,Eq,s0,s1,v0,v1] using A k
  · have FF : wins x e j=false := Bool.eq_false_iff.mpr E
    simpa [push,updateBit,FF] using A k

theorem good_step {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (heads : ∀ j,header x j=h j)
    (f : Flight) (A : ShortReadFlight.Active C x f)
    (a : Ledger s n) (G : Good C a f) :
    Good C (advanceLedger C x e f a) (ShortReadFlight.next C x e f) := by
  cases f with
  | consumed => exact G
  | returning i ok d =>
    simp only [ShortReadFlight.next,advanceLedger]
    split <;> exact G
  | forward i d =>
    by_cases E : e=nextAt C.root i
    · have H := data_at_front C x e i d E A
      have P : d<128 := A.2.1
      simp only [ShortReadFlight.next,advanceLedger,if_pos E]
      by_cases L : i+1<C.L
      · rw [if_pos L]
        let j := C.route.port i
        let q := (hopPacket x e j (C.route.port (i+1))).payload
        change bitAt q 6=true → Bits (push a x e j) q ∧ Covers C (push a x e j) (i+1)
        have B := hop_bits x e j (C.route.port (i+1)) d P H
        intro live
        have D : (bitAt d 6 && (!header x e || wins x e j))=true := B.1.symm.trans live
        have both := Bool.and_eq_true_iff.mp D
        have U := G both.1
        exact ⟨bits_push a x e j d q U.1 B.2,covers_push C a x e i E (heads e) both.2 U.2⟩
      · rw [if_neg L]
        have L' : i+1=C.L := by
          have U : i<C.L := A.1
          omega
        let j := C.route.port i
        let t := replyPacket x e j
        change (t.outcome==0)=true →
          Bits (push a x e j) (datum t).val ∧ Covers C (push a x e j) C.L
        have B := terminal_bits x e j d P H
        intro live
        have D : (bitAt d 6 && (!header x e || wins x e j))=true := B.1.symm.trans live
        have both := Bool.and_eq_true_iff.mp D
        have U := G both.1
        rw [terminal_datum x e j d H live,←L']
        exact ⟨bits_push a x e j d t.payload U.1 (B.2 live),
          covers_push C a x e i E (heads e) both.2 U.2⟩
    · simpa only [advanceLedger,ShortReadFlight.next,if_neg E] using G

/-- Both the exact flight and its capture ledger follow the same original
raw tape, without a new observation or packet choice at the turn. -/
theorem good_run {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (w : List (Fin n)) (x : Raw s n) (f : Flight) (a : Ledger s n)
    (H : H2Ready x) (heads : ∀ j,header x j=h j) (A : ShortReadFlight.Active C x f)
    (G : Good C a f) (B : beforeConsume C x f w) :
    ShortReadFlight.Active C (rawRun x w) (ShortReadFlight.trace C x f w) ∧
      Good C (trace C x f a w) (ShortReadFlight.trace C x f w) := by
  induction w generalizing x f a with
  | nil => exact ⟨A,G⟩
  | cons e w ih =>
    have B' : live f ∧ beforeConsume C (rawNext s x e) (ShortReadFlight.next C x e f) w := B
    exact ih (rawNext s x e) (ShortReadFlight.next C x e f) (advanceLedger C x e f a)
      (h2_ready_closed N x e H)
      (fun j=>(H1.raw_h1_selected_frozen N x e j H.1).trans (heads j))
      (read_flight_active_step C x e (by omega) heads f B'.1 A)
      (good_step C x e heads f A a G) B'.2

/-- Literal successful file, with both bits per lane identified by the
actual old-pair sample ledger. Coverage counts owned header departures,
not visits to arbitrary physical sites. -/
theorem successful_file_matches_captures {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (N : 5≤n) (w : List (Fin n)) (x : Raw s n) (H : H2Ready x)
    (heads : ∀ j,header x j=h j) (I : ShortClearLaunch.ClearIssue C x 3)
    (d : Fin 64)
    (B : beforeConsume C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w)
    (D : ShortReadFlight.trace C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w=.consumed true d) :
    let first := RearTrace.predecessor C.root
    let y := rawRun x (first::w)
    let a := trace C (rawNext s x first) (.forward 0 64) (fun _=>none) w
    Covers C a C.L ∧
      ∀ j : Fin 3,
        (ShortReadResult.fileField.read (y C.root).mis1).getLsbD (5-j.val)=select (a j) ∧
        (ShortReadResult.fileField.read (y C.root).mis1).getLsbD (2-j.val)=value (a j) := by
  let first := RearTrace.predecessor C.root
  have G := good_run C N w (rawNext s x first) (.forward 0 64) (fun _=>none)
    (h2_ready_closed N x first H)
    (fun j=>(H1.raw_h1_selected_frozen N x first j H.1).trans (heads j))
    (forward_from_actual_issue3 C x heads I) (initial C) B
  rw [D] at G
  obtain ⟨C0,C1⟩ := G
  have F := C0.2 rfl
  have P := C1 rfl
  dsimp only
  refine ⟨P.2,?_⟩
  intro j
  have Q := P.1 j
  change (ShortReadResult.fileField.read (rawRun (rawNext s x first) w C.root).mis1).getLsbD _=_ ∧
    (ShortReadResult.fileField.read (rawRun (rawNext s x first) w C.root).mis1).getLsbD _=_
  rw [F]
  exact ⟨(low_wire d ⟨5-j.val,by have := j.isLt; omega⟩).trans Q.1,
    (low_wire d ⟨2-j.val,by omega⟩).trans Q.2⟩


private theorem advance_sample {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (e : Fin n) (f : Flight) (a : Ledger s n) (j : Fin 3) (p : Sample s n)
    (H : advanceLedger C x e f a j=some p) :
    a j=some p ∨ ∃ i d, f=.forward i d ∧ e=nextAt C.root i ∧
      C.route.port i=j ∧ wins x e j=true ∧ p=⟨x,e⟩ := by
  cases f with
  | returning => exact .inl H
  | consumed => exact .inl H
  | forward i d =>
    by_cases E : e=nextAt C.root i
    · rw [show advanceLedger C x e (.forward i d) a=push a x e (C.route.port i)
        by simp [advanceLedger,E]] at H
      unfold push at H
      split at H
      · rename_i K
        obtain ⟨J,W⟩ := K
        exact .inr ⟨i,d,rfl,E,J.symm,by rwa [J],(Option.some.inj H).symm⟩
      · exact .inl H
    · exact .inl (by simpa [advanceLedger,E] using H)

/-- Any new ledger entry names an actual old tape prefix, the exact
forward cursor there, and the actual sampled winning mark. -/
theorem sample_origin {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (f : Flight) (a : Ledger s n) (w : List (Fin n))
    (j : Fin 3) (p : Sample s n) (S : trace C x f a w j=some p) :
    a j=some p ∨ ∃ (lead tail : List (Fin n)) (i d : Nat),
      w=lead++p.edge::tail ∧ p.old=rawRun x lead ∧
      ShortReadFlight.trace C x f lead=.forward i d ∧ p.edge=nextAt C.root i ∧
      C.route.port i=j ∧ wins p.old p.edge j=true := by
  induction w generalizing x f a with
  | nil => exact .inl S
  | cons e w ih =>
    have Q : trace C (rawNext s x e) (ShortReadFlight.next C x e f) (advanceLedger C x e f a) w j=some p := S
    rcases ih _ _ _ Q with P|⟨lead,tail,i,d,E,X,F,M,J,W⟩
    · rcases advance_sample C x e f a j p P with K|⟨i,d,F,M,J,W,Eq⟩
      · exact .inl K
      · subst p
        exact .inr ⟨[],w,i,d,rfl,rfl,F,M,J,W⟩
    · refine .inr ⟨e::lead,tail,i,d,?_,X,F,M,J,W⟩
      rw [E]
      rfl

private theorem all_lanes_covered {s n : Nat} (x : Raw s n) (H : H2Ready x)
    (C : Chart (header x)) (N : 9<n) (a : Ledger s n) (A : Covers C a C.L) :
    ∀ j : Fin 3, (a j).isSome=true := by
  obtain ⟨da,db,dc,Da,Db,Dc,L,AB,M,Z,P,Q,_,_⟩ :=
    ShortReadCaptureGeometry.capture_indices x H.1 C N
  intro j
  have J := j.isLt
  have J' : j=0 ∨ j=1 ∨ j=2 := by
    have K : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
    rcases K with S|S|S
    · exact .inl (Fin.ext S)
    · exact .inr (.inl (Fin.ext S))
    · exact .inr (.inr (Fin.ext S))
  rcases J' with rfl|rfl|rfl
  · have B := A 0 C.positive ((M 0 C.positive).mpr (.inl rfl))
    change (a (ShortResetChart.lane C.a C.b 0)).isSome=true at B
    rwa [Z] at B
  · have L' : da<C.L := by omega
    have B := A da L' ((M da L').mpr (.inr (.inl rfl)))
    change (a (ShortResetChart.lane C.a C.b da)).isSome=true at B
    rwa [P] at B
  · have B := A (da+db) AB ((M _ AB).mpr (.inr (.inr rfl)))
    change (a (ShortResetChart.lane C.a C.b (da+db))).isSome=true at B
    rwa [Q] at B

/-- Each of the three stored bit pairs comes from a checked old-header
winning mark in the actual flight. This says nothing about the later
selected byte remaining protected through a subsequent COMMIT. -/
theorem read_return_matches_three_captures {s n : Nat} (x : Raw s n) (H : H2Ready x)
    (C : Chart (header x)) (N : 9<n) (I : ShortClearLaunch.ClearIssue C x 3)
    (w : List (Fin n)) (out : Fin 64)
    (B : beforeConsume C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w)
    (D : ShortReadFlight.trace C (rawNext s x (RearTrace.predecessor C.root)) (.forward 0 64) w=.consumed true out) :
    let door := RearTrace.predecessor C.root
    let y := rawRun x (door::w)
    ∀ j : Fin 3, ∃ (p : Sample s n) (lead tail : List (Fin n)) (i payload : Nat),
      w=lead++p.edge::tail ∧
      p.old=rawRun (rawNext s x door) lead ∧
      ShortReadFlight.trace C (rawNext s x door) (.forward 0 64) lead=.forward i payload ∧
      p.edge=nextAt C.root i ∧ C.route.port i=j ∧ wins p.old p.edge j=true ∧
      (ShortReadResult.fileField.read (y C.root).mis1).getLsbD (5-j.val)=seenSelector p.old p.edge ∧
      (ShortReadResult.fileField.read (y C.root).mis1).getLsbD (2-j.val)=seenValue p.old p.edge := by
  let door := RearTrace.predecessor C.root
  let a := trace C (rawNext s x door) (.forward 0 64) (fun _=>none) w
  have M := successful_file_matches_captures C (by omega) w x H (fun _=>rfl) I out B D
  have A := all_lanes_covered x H C N a M.1
  dsimp only
  intro j
  cases E : a j with
  | none => have T := A j; rw [E] at T; contradiction
  | some p =>
    have F : trace C (rawNext s x door) (.forward 0 64) (fun _=>none) w j=some p := E
    rcases sample_origin C (rawNext s x door) (.forward 0 64) (fun _=>none) w j p F with bad|origin
    · contradiction
    · obtain ⟨lead,tail,i,payload,W,X,T,J,K,win⟩ := origin
      have Q := M.2 j
      change _ = select (a j) ∧ _ = value (a j) at Q
      rw [E] at Q
      exact ⟨p,lead,tail,i,payload,W,X,T,J,K,win,Q.1,Q.2⟩

#print axioms good_step
#print axioms good_run
#print axioms successful_file_matches_captures
#print axioms sample_origin
#print axioms read_return_matches_three_captures
end L4.ShortReadCaptureTrace
