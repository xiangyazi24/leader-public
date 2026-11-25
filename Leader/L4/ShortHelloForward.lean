import Leader.L4.ShortResetCycle
import Leader.L4.ShortControllerMIS1
import Leader.L4.ShortGrantPersistence

namespace L4.ShortHelloForward
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle ShortResetForwardH2

private theorem fwd_decode (g : Bool) : decode g (encode helloForward)=helloForward := by
  cases g <;> decide

private theorem out_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (H : oldK (header x e) (x e).mis1 j=helloForward) :
    (kField j).read (rawNext s x e e).mis1=encode T ∧
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode helloForward := by
  have A := forward_ready_out_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k dst (hello_ready _ _ _ H)
  exact ⟨(work_to_raw x e sep j).1.trans A.1,
    (work_to_raw x e sep k).2.trans (A.2.trans (congrArg encode (hello_forwardPacket _ _ _ _ _ _ H)))⟩

private theorem turn_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=none)
    (H : oldK (header x e) (x e).mis1 j=helloForward) :
    (kField j).read (rawNext s x e e).mis1=encode helloReply := by
  have A := forward_ready_turn_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j dst (hello_ready _ _ _ H)
  exact (work_to_raw x e sep j).1.trans (A.trans (congrArg encode (hello_turnPacket _ _ _ _ _ H)))

private theorem inbound_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=helloForward ∨
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=T) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 :=
  (work_to_raw x e sep k).2.trans (hello_inbound_frame_pair _ _ _ _ _ _ dst trail safe)

private theorem prefix_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=helloForward ∨
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=T) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 :=
  (work_to_raw x e sep j).1.trans (hello_prefix_trail_frame_pair _ _ _ _ _ _ dst trail safe)

private theorem root_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (wait : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=1)
    (safe : oldK true (x (rightNeighbor e)).mis1 0=helloForward ∨
      oldK true (x (rightNeighbor e)).mis1 0=T) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField 0).read (x (rightNeighbor e)).mis1 := by
  have H := (work_to_raw x e sep 0).2
  simp only [pairHeader,head] at H
  exact H.trans (hello_root_inbound_frame_pair _ _ _ wait op safe)

theorem forward_step {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ q, header x q=h q)
    (wait : get (x R.root).mis1 81 2 (by decide)=2)
    (op : get (x R.root).mis1 78 3 (by decide)=1)
    (i : Nat) (I : i<R.length)
    (trails : TrailPrefix R x i) (front : bits R x i=encode helloForward) :
    let y := rawNext s x e
    TrailPrefix R y i ∧
      (if e=nextAt R.root i then
        if i+1<R.length then bits R y i=encode T ∧ bits R y (i+1)=encode helloForward
        else bits R y i=encode helloReply
      else bits R y i=encode helloForward) := by
  dsimp only
  let y := rawNext s x e
  have Tf j J := slot_of_bits R x j T trail_decode (trails j J)
  have Ff := slot_of_bits R x i helloForward fwd_decode front
  have dst (j : Nat) (J : j+1<R.length) :
      destination (header x (rightNeighbor (nextAt R.root j))) (R.port j)=some (R.port (j+1)) := by
    rw [heads]
    exact R.live j J
  have predecessor (j : Nat) (J : 0<j) (h : rightNeighbor e=nextAt R.root j) :
      e=nextAt R.root (j-1) := by
    have E : rightNeighbor (nextAt R.root (j-1))=nextAt R.root j := by
      rw [show j=j-1+1 by omega]; rfl
    have E2 := congrArg RearTrace.predecessor (h.trans E.symm)
    simpa only [RearTrace.predecessor_right] using E2
  have hold_in (j : Nat) (J : j≤i)
      (h' : rightNeighbor e=nextAt R.root j)
      (safe : slot R x j=helloForward ∨ slot R x j=T) :
      (kField (R.port j)).read (y (nextAt R.root j)).mis1=
      (kField (R.port j)).read (x (nextAt R.root j)).mis1 := by
    by_cases zero : j=0
    · subst j
      change rightNeighbor e=R.root at h'
      rw [R.rootPort]
      have hd : header x (rightNeighbor e)=true := by rw [h',heads,R.rootHeader]
      rw [←h']
      have hs : header x R.root=true := by rw [heads,R.rootHeader]
      have S : oldK true (x (rightNeighbor e)).mis1 0=helloForward ∨
          oldK true (x (rightNeighbor e)).mis1 0=T := by
        rw [h',←R.rootPort,←hs]
        exact safe
      exact root_frame_raw x e sep hd (by simpa only [h'] using wait)
        (by simpa only [h'] using op) S
    · let p := j-1
      have ep : e=nextAt R.root p := predecessor j (Nat.pos_of_ne_zero zero) h'
      have P : p+1=j := by dsimp [p]; omega
      have link : destination (header x (rightNeighbor e)) (R.port p)=some (R.port j) := by
        rw [ep,←P]
        have H := dst p (by omega)
        rwa [P] at H ⊢
      rw [←h']
      apply inbound_frame_raw x e sep (R.port p) _ link
      · rw [ep]
        exact Tf p (by omega)
      · rw [h']
        exact safe
  constructor
  · intro j J
    have jt := Tf j J
    apply Eq.trans _ (trails j J)
    unfold bits
    by_cases L : nextAt R.root j=e
    · have K : j+1≤i := by omega
      have safe : slot R x (j+1)=helloForward ∨ slot R x (j+1)=T := by
        rcases Nat.eq_or_lt_of_le K with E|E
        · exact .inl (E.symm ▸ Ff)
        · exact .inr (Tf _ E)
      have H := prefix_frame_raw x e sep (R.port j) (R.port (j+1))
        (by rw [←L]; exact dst j (by omega))
        (by rw [←L]; exact jt)
        (by rw [←L]; exact safe)
      rw [L]
      exact H
    · by_cases K : nextAt R.root j=rightNeighbor e
      · exact hold_in j (by omega) K.symm (.inr jt)
      · have F := reset_remote_frame_raw x e (nextAt R.root j) L K
        exact congrArg ((kField (R.port j)).read) F
  · split
    · rename_i E
      subst e
      split
      · rename_i J
        have H := out_raw x (nextAt R.root i) sep _ _ (dst i J) Ff
        exact H
      · rename_i J
        have E : i=R.length-1 := by omega
        have H := turn_raw x (nextAt R.root i) sep _ (by rw [heads,E]; exact R.turn) Ff
        exact H
    · rename_i E
      apply Eq.trans _ front
      unfold bits
      by_cases K : nextAt R.root i=rightNeighbor e
      · exact hold_in i (by omega) K.symm (.inl Ff)
      · have F := reset_remote_frame_raw x e (nextAt R.root i) (Ne.symm E) K
        exact congrArg ((kField (R.port i)).read) F

def Wait1 {s n : Nat} (x : Raw s n) (r : Fin n) : Prop :=
  get (x r).mis1 81 2 (by decide)=2 ∧ get (x r).mis1 78 3 (by decide)=1

private theorem wait_forward_or_trail {s n : Nat} (x : Raw s n) (r e : Fin n)
    (sep : e≠rightNeighbor e) (hd : header x r=true) (W : Wait1 x r)
    (hold : rightNeighbor e=r →
      oldK true (x r).mis1 0=helloForward ∨ oldK true (x r).mis1 0=T) :
    Wait1 (rawNext s x e) r := by
  by_cases E : r=e
  · subst r
    have K := reset_controller_outgoing_raw x e hd
    exact ⟨K.1.trans W.1,K.2.trans W.2⟩
  by_cases D : rightNeighbor e=r
  · have hd' : header x (rightNeighbor e)=true := D ▸ hd
    let b := (x (rightNeighbor e)).mis1
    let tok := oldK true b 0
    have safe : tok.tag=1 ∨ tok.tag=2 := by
      have S : tok=helloForward ∨ tok=T := by
        change oldK true (x (rightNeighbor e)).mis1 0=helloForward ∨
          oldK true (x (rightNeighbor e)).mis1 0=T
        rw [D]
        exact hold D
      rcases S with h|h
      · exact .inr (by rw [h]; rfl)
      · exact .inl (by rw [h]; rfl)
    have bits : Wait1 x (rightNeighbor e) := D ▸ W
    have op : get b 78 3 (by decide)=1 := bits.2
    have P := source_wait_holds b tok bits.1 (by rw [op]; decide) safe
    obtain ⟨y,A,F⟩ := ShortControllerMIS1.source_door_raw x e sep hd'
    change ∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
      f.read (rawNext s x e (rightNeighbor e)).mis1 =
        f.read (match (source b tok).2 with
          | none => (source b tok).1.apply y
          | some q => (putK 0 q).apply ((source b tok).1.apply y)) at F
    rw [P] at F
    let f := lane 81 2 (by decide)
    let g := lane 78 3 (by decide)
    have Fa := F f (by decide)
    have Fg := F g (by decide)
    have Id : (Patch.empty 96).apply y=y := by
      change y &&& BitVec.allOnes 96 ||| 0=y
      rw [BitVec.and_allOnes]
      exact BitVec.or_zero
    simp only [Id] at Fa Fg
    rw [←D]
    exact ⟨(congrArg BitVec.toNat (Fa.trans (A f (by decide) (by decide)))).trans bits.1,
      (congrArg BitVec.toNat (Fg.trans (A g (by decide) (by decide)))).trans bits.2⟩
  · unfold Wait1
    rw [reset_remote_frame_raw x e r E (Ne.symm D)]
    exact W

/-- A real preterminal HELLO has one forward frontier with trails behind
it. No intervening mark can turn it or advance its source past WAIT1. -/
def BeforeTurn {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (i : Nat) : Prop :=
  i<R.length ∧ Wait1 x R.root ∧ TrailPrefix R x i ∧ bits R x i=encode helloForward

def terminalMark {n : Nat} {h : Fin n → Bool} (R : Route h) : Fin n :=
  nextAt R.root (R.length-1)

def ahead {n : Nat} {h : Fin n → Bool} (R : Route h) (i : Nat) (e : Fin n) : Nat :=
  if e=nextAt R.root i then i+1 else i

theorem before_turn_step {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ j,header x j=h j) (i : Nat) (A : BeforeTurn R x i)
    (notTerminal : e≠terminalMark R) :
    BeforeTurn R (rawNext s x e) (ahead R i e) := by
  obtain ⟨I,W,Tp,Fp⟩ := A
  have H : header x R.root=true := (heads _).trans R.rootHeader
  have B := forward_step R x e sep heads W.1 W.2 i I Tp Fp
  have W' := wait_forward_or_trail x R.root e sep H W (fun _=>by
    have V : slot R x 0=helloForward ∨ slot R x 0=T := by
      by_cases zero : i=0
      · subst i; exact .inl (slot_of_bits R x 0 helloForward fwd_decode Fp)
      · exact .inr (slot_of_bits R x 0 T trail_decode (Tp 0 (by omega)))
    simpa only [slot,nextAt,H,R.rootPort] using V)
  unfold ahead
  by_cases E : e=nextAt R.root i
  · rw [if_pos E]
    have L : i+1<R.length := by
      by_cases K : i+1<R.length
      · exact K
      · have J : i=R.length-1 := by omega
        exact False.elim (notTerminal (E.trans (congrArg (nextAt R.root) J)))
    subst e
    simp only [if_pos L] at B
    refine ⟨L,W',?_,B.2.2⟩
    intro j J
    by_cases eq : j=i
    · simpa only [eq] using B.2.1
    · exact B.1 j (by omega)
  · rw [if_neg E]
    simp only [if_neg E] at B
    exact ⟨I,W',B.1,B.2⟩

theorem before_terminal_run {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (N : 5≤n) (x : Raw s n) (A : H2Ready x)
    (heads : ∀ j,header x j=h j) (i : Nat) (front : BeforeTurn R x i)
    (w : List (Fin n)) (missing : terminalMark R ∉ w) :
    ∃ k, BeforeTurn R (rawRun x w) k := by
  induction w generalizing x i with
  | nil => exact ⟨i,front⟩
  | cons e w ih =>
    have E : e≠terminalMark R := fun h=>missing (by simp [h])
    exact ih (rawNext s x e) (h2_ready_closed N x e A)
      (fun j=>(H1.raw_h1_selected_frozen N x e j A.1).trans (heads j)) _
      (before_turn_step R x e (edge_sep (by omega) e) heads i front E)
      (fun h=>missing (List.mem_cons_of_mem e h))

/-- Once the literal owner door launches HELLO from ISSUE1, a suffix
that never samples the owner's terminal mark cannot take it to ADMIT.
The statement retains all other raw marks and imposes no cleanliness
assumption on the old bytes outside the traversed prefix. -/
theorem from_actual_issue_waits_without_terminal {s n : Nat} {h : Fin n → Bool}
    (R : Route h) (N : 5≤n) (x : Raw s n) (A : H2Ready x)
    (heads : ∀ j, header x j=h j)
    (phase : get (x R.root).mis1 81 2 (by decide)=1)
    (op : get (x R.root).mis1 78 3 (by decide)=1)
    (w : List (Fin n)) (missing : terminalMark R ∉ w) :
    Wait1 (rawRun x (RearTrace.predecessor R.root :: w)) R.root := by
  let d := RearTrace.predecessor R.root
  have D : rightNeighbor d=R.root := RearTrace.right_predecessor _
  have old : header x (rightNeighbor d)=true := by rw [D,heads,R.rootHeader]
  have P := ShortControllerMIS1.issue_fresh_raw x d (edge_sep (by omega) d) old 1
    (by rwa [D]) (by rwa [D]) (by decide)
  dsimp only at P
  rw [D] at P
  let y := rawNext s x d
  have start : BeforeTurn R y 0 := by
    refine ⟨R.positive,⟨P.1,P.2.1⟩,fun j J=>False.elim (by omega),?_⟩
    change (kField (R.port 0)).read (y R.root).mis1=encode helloForward
    rw [R.rootPort]
    exact P.2.2
  obtain ⟨_,G⟩ := before_terminal_run R N y (h2_ready_closed N x d A)
    (fun j=>(H1.raw_h1_selected_frozen N x d j A.1).trans (heads j)) 0 start w missing
  exact G.2.1

def ClearSuffix {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (i : Nat) : Prop :=
  ∀ j, i<j → j<R.length → bits R x j=encode E

theorem clear_suffix_step {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ j,header x j=h j) (i : Nat)
    (C : ClearSuffix R x i) :
    ClearSuffix R (rawNext s x e) (ahead R i e) := by
  intro j J L
  have I : i<j := by
    unfold ahead at J
    split at J <;> omega
  have emptySlot (k : Nat) (lo : i<k) (hi : k<R.length) :
      slot R x k=E := slot_of_bits R x k E empty_decode (C k lo hi)
  have old : bits R x j=encode E := C j I L
  apply Eq.trans _ old
  unfold bits
  by_cases P : nextAt R.root j=e
  · rw [P]
    apply reset_reverse_outbound_frame_raw x e sep _ (.inr (by rw [←P]; exact emptySlot j I L))
    rw [← P]
    change destination (header x (nextAt R.root (j+1))) (R.port j)=none ∨ _
    by_cases K : j+1<R.length
    · exact .inr ⟨R.port (j+1),by rw [heads]; exact R.live j K,emptySlot (j+1) (by omega) K⟩
    · apply Or.inl
      have K' : j=R.length-1 := by omega
      rw [heads, K']
      exact R.turn
  · by_cases Q : nextAt R.root j=rightNeighbor e
    · let p := j-1
      have K : p+1=j := by dsimp [p]; omega
      have Eq : rightNeighbor (nextAt R.root p)=nextAt R.root j := by
        rw [←K]
        rfl
      have E0 : nextAt R.root p=e := by
        have r := congrArg RearTrace.predecessor (Eq.trans Q)
        simpa only [RearTrace.predecessor_right] using r
      have Ip : i<p := by
        by_cases V : i=p
        · have W : e=nextAt R.root i := by rw [V,E0]
          simp only [ahead,W,if_true,V] at J
          omega
        · omega
      rw [Q]
      apply reset_reverse_inbound_frame_raw x e sep (R.port p) _
      · rw [← E0,heads,←K]
        exact R.live p (by omega)
      · exact .inr (by rw [←E0]; exact emptySlot p Ip (by omega))
      · rw [←Q]
        exact emptySlot j I L
    · exact congrArg ((kField (R.port j)).read) (reset_remote_frame_raw x e _ P Q)

def NoGrants {s n : Nat} {h : Fin n → Bool} (R : Route h) (x : Raw s n) : Prop :=
  ∀ j, j<R.length → h (nextAt R.root j)=true →
    (x (nextAt R.root j)).mis1.getLsbD (91-(R.port j).val)=false

/-- An unturned HELLO with a clear suffix cannot acquire any of its
three grants, even with foreign owners active on its two reader sites. -/
theorem no_grants_step {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ j,header x j=h j) (i : Nat) (A : BeforeTurn R x i)
    (C : ClearSuffix R x i) (G : NoGrants R x) :
    NoGrants R (rawNext s x e) := by
  intro j J H
  let q := nextAt R.root j
  let k := R.port j
  have Hd : header x q=true := (heads _).trans H
  refine ShortGrantPersistence.absent_until_ask x e q k sep Hd (G j J H) (fun _=>?_ )
  have X : slot R x j=helloForward ∨ slot R x j=T ∨ slot R x j=E := by
    by_cases L : j<i
    · exact .inr (.inl (slot_of_bits R x j T trail_decode (A.2.2.1 j L)))
    by_cases D : j=i
    · subst j
      exact .inl (slot_of_bits R x i helloForward fwd_decode A.2.2.2)
    · exact .inr (.inr (slot_of_bits R x j E empty_decode (C j (by omega) J)))
  change oldK (header x q) (x q).mis1 k=helloForward ∨
    oldK (header x q) (x q).mis1 k=T ∨ oldK (header x q) (x q).mis1 k=E at X
  rw [Hd] at X
  rcases X with F|T'|E'
  · exact hello_no_ask _ _ F
  · change ((oldK true (x q).mis1 k).tag==2 && !(oldK true (x q).mis1 k).fault &&
      (oldK true (x q).mis1 k).opcode==3)=false
    rw [T']
    rfl
  · change ((oldK true (x q).mis1 k).tag==2 && !(oldK true (x q).mis1 k).fault &&
      (oldK true (x q).mis1 k).opcode==3)=false
    rw [E']
    rfl

theorem clear_grant_free_before_terminal {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (N : 5≤n) (x : Raw s n) (A : H2Ready x)
    (heads : ∀ j,header x j=h j) (i : Nat) (front : BeforeTurn R x i)
    (clear : ClearSuffix R x i) (G : NoGrants R x)
    (w : List (Fin n)) (missing : terminalMark R ∉ w) :
    ∃ k, BeforeTurn R (rawRun x w) k ∧ ClearSuffix R (rawRun x w) k ∧
      NoGrants R (rawRun x w) := by
  induction w generalizing x i with
  | nil => exact ⟨i,front,clear,G⟩
  | cons e w ih =>
    have E : e≠terminalMark R := fun h=>missing (by simp [h])
    have Sep := edge_sep (by omega : 1<n) e
    exact ih (rawNext s x e) (h2_ready_closed N x e A)
      (fun j=>(H1.raw_h1_selected_frozen N x e j A.1).trans (heads j)) _
      (before_turn_step R x e Sep heads i front E) (clear_suffix_step R x e Sep heads i clear)
      (no_grants_step R x e Sep heads i front clear G) (fun h=>missing (List.mem_cons_of_mem e h))

#print axioms no_grants_step
#print axioms clear_grant_free_before_terminal
#print axioms clear_suffix_step
#print axioms from_actual_issue_waits_without_terminal
#print axioms forward_step
#print axioms before_turn_step
#print axioms before_terminal_run
end L4.ShortHelloForward
