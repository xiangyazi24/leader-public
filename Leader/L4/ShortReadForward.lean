import Leader.L4.ShortHelloForward
import Leader.L4.ShortClearLaunch
import Leader.L4.ShortReadReturnHop

namespace L4.ShortReadForward
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle ShortResetForwardH2

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem decode_finite :
    ∀ (g : Bool) (d : Fin 128), decode g (encode (readFront d.val))=readFront d.val := by decide

theorem decode_front (g : Bool) (d : Nat) (L : d<128) :
    decode g (encode (readFront d))=readFront d := decode_finite g ⟨d,L⟩

def hopPacket {s n : Nat} (x : Raw s n) (e : Fin n) (j k : Fin 3) : Token :=
  forwardPacket (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k

def replyPacket {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3) : Token :=
  turnPacket (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j

theorem hop_packet_canonical {s n : Nat} (x : Raw s n) (e : Fin n) (j k : Fin 3)
    (d : Nat) (L : d<128) (H : oldK (header x e) (x e).mis1 j=readFront d) :
    let q := hopPacket x e j k
    q.payload<128 ∧ q=readFront q.payload := by
  have op : (oldK (header x e) (x e).mis1 j).opcode=3 := congrArg Token.opcode H
  have live : (oldK (header x e) (x e).mis1 j).fault=false := congrArg Token.fault H
  have E : (oldK (header x e) (x e).mis1 j).payload<128 := by rw [H]; exact L
  have B := read_forwardPayload_lt (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k op live E
  refine ⟨B,?_⟩
  unfold hopPacket
  rw [read_forwardPacket _ _ _ _ _ _ op live]
  dsimp only
  rw [H]
  rfl

private theorem out_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3) (d : Nat) (L : d<128)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (H : oldK (header x e) (x e).mis1 j=readFront d) :
    let q := (hopPacket x e j k).payload
    q<128 ∧ (kField j).read (rawNext s x e e).mis1=encode T ∧
      (kField k).read (rawNext s x e (rightNeighbor e)).mis1=encode (readFront q) := by
  have A := forward_ready_out_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j k dst
    (read_is_ready _ _ _ (congrArg Token.tag H) (congrArg Token.opcode H))
  have ⟨P,Q⟩ := hop_packet_canonical x e j k d L H
  exact ⟨P,(work_to_raw x e sep j).1.trans A.1,
    (work_to_raw x e sep k).2.trans (A.2.trans (congrArg encode Q))⟩

private theorem turn_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3) (d : Nat)
    (dst : destination (header x (rightNeighbor e)) j=none)
    (H : oldK (header x e) (x e).mis1 j=readFront d) :
    (kField j).read (rawNext s x e e).mis1=encode (replyPacket x e j) := by
  have A := forward_ready_turn_pair (header x e) (header x (rightNeighbor e))
    (x e).mis1 (x (rightNeighbor e)).mis1 j dst
    (read_is_ready _ _ _ (congrArg Token.tag H) (congrArg Token.opcode H))
  exact (work_to_raw x e sep j).1.trans A

private theorem inbound_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (d : Nat) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=readFront d ∨
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=T) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 :=
  (work_to_raw x e sep k).2.trans (read_inbound_frame_pair d _ _ _ _ _ _ dst trail safe)

private theorem prefix_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (d : Nat) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (trail : oldK (header x e) (x e).mis1 j=T)
    (safe : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=readFront d ∨
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=T) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 :=
  (work_to_raw x e sep j).1.trans (read_prefix_trail_frame_pair d _ _ _ _ _ _ dst trail safe)

private theorem root_frame_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (d : Nat) (head : header x (rightNeighbor e)=true)
    (wait : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2)
    (op : get (x (rightNeighbor e)).mis1 78 3 (by decide)=3)
    (safe : oldK true (x (rightNeighbor e)).mis1 0=readFront d ∨
      oldK true (x (rightNeighbor e)).mis1 0=T) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField 0).read (x (rightNeighbor e)).mis1 := by
  have H := (work_to_raw x e sep 0).2
  simp only [pairHeader,head] at H
  exact H.trans (read_root_inbound_frame_pair d _ _ _ wait op safe)

theorem forward_step {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ q, header x q=h q)
    (wait : get (x R.root).mis1 81 2 (by decide)=2)
    (op : get (x R.root).mis1 78 3 (by decide)=3)
    (i : Nat) (I : i<R.length)
    (d : Nat) (D : d<128) (trails : TrailPrefix R x i) (front : bits R x i=encode (readFront d)) :
    let y := rawNext s x e
    TrailPrefix R y i ∧
      (if e=nextAt R.root i then
        if i+1<R.length then
          let q := (hopPacket x (nextAt R.root i) (R.port i) (R.port (i+1))).payload
          q<128 ∧ bits R y i=encode T ∧ bits R y (i+1)=encode (readFront q)
        else bits R y i=encode (replyPacket x (nextAt R.root i) (R.port i))
      else bits R y i=encode (readFront d)) := by
  dsimp only
  let y := rawNext s x e
  have Tf j J := slot_of_bits R x j T trail_decode (trails j J)
  have Ff := slot_of_bits R x i (readFront d) (fun gate=>decode_front gate d D) front
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
      (safe : slot R x j=readFront d ∨ slot R x j=T) :
      (kField (R.port j)).read (y (nextAt R.root j)).mis1=
      (kField (R.port j)).read (x (nextAt R.root j)).mis1 := by
    by_cases zero : j=0
    · subst j
      change rightNeighbor e=R.root at h'
      rw [R.rootPort]
      have hd : header x (rightNeighbor e)=true := by rw [h',heads,R.rootHeader]
      rw [←h']
      have hs : header x R.root=true := by rw [heads,R.rootHeader]
      have S : oldK true (x (rightNeighbor e)).mis1 0=readFront d ∨
          oldK true (x (rightNeighbor e)).mis1 0=T := by
        rw [h',←R.rootPort,←hs]
        exact safe
      exact root_frame_raw x e sep d hd (by simpa only [h'] using wait)
        (by simpa only [h'] using op) S
    · let p := j-1
      have ep : e=nextAt R.root p := predecessor j (Nat.pos_of_ne_zero zero) h'
      have P : p+1=j := by dsimp [p]; omega
      have link : destination (header x (rightNeighbor e)) (R.port p)=some (R.port j) := by
        rw [ep,←P]
        have H := dst p (by omega)
        rwa [P] at H ⊢
      rw [←h']
      apply inbound_frame_raw x e sep d (R.port p) _ link
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
      have safe : slot R x (j+1)=readFront d ∨ slot R x (j+1)=T := by
        rcases Nat.eq_or_lt_of_le K with E|E
        · exact .inl (E.symm ▸ Ff)
        · exact .inr (Tf _ E)
      have H := prefix_frame_raw x e sep d (R.port j) (R.port (j+1))
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
        have H := out_raw x (nextAt R.root i) sep _ _ d D (dst i J) Ff
        exact H
      · rename_i J
        have E : i=R.length-1 := by omega
        have H := turn_raw x (nextAt R.root i) sep _ d (by rw [heads,E]; exact R.turn) Ff
        exact H
    · rename_i E
      apply Eq.trans _ front
      unfold bits
      by_cases K : nextAt R.root i=rightNeighbor e
      · exact hold_in i (by omega) K.symm (.inl Ff)
      · have F := reset_remote_frame_raw x e (nextAt R.root i) (Ne.symm E) K
        exact congrArg ((kField (R.port i)).read) F

def Wait3 {s n : Nat} (x : Raw s n) (r : Fin n) : Prop :=
  get (x r).mis1 81 2 (by decide)=2 ∧ get (x r).mis1 78 3 (by decide)=3

private theorem wait_forward_or_trail {s n : Nat} (x : Raw s n) (r e : Fin n) (data : Nat)
    (sep : e≠rightNeighbor e) (hd : header x r=true) (W : Wait3 x r)
    (hold : rightNeighbor e=r →
      oldK true (x r).mis1 0=readFront data ∨ oldK true (x r).mis1 0=T) :
    Wait3 (rawNext s x e) r := by
  by_cases E : r=e
  · subst r
    have K := reset_controller_outgoing_raw x e hd
    exact ⟨K.1.trans W.1,K.2.trans W.2⟩
  by_cases D : rightNeighbor e=r
  · have hd' : header x (rightNeighbor e)=true := D ▸ hd
    let b := (x (rightNeighbor e)).mis1
    let tok := oldK true b 0
    have safe : tok.tag=1 ∨ tok.tag=2 := by
      have S : tok=readFront data ∨ tok=T := by
        change oldK true (x (rightNeighbor e)).mis1 0=readFront data ∨
          oldK true (x (rightNeighbor e)).mis1 0=T
        rw [D]
        exact hold D
      rcases S with h|h
      · exact .inr (by rw [h]; rfl)
      · exact .inl (by rw [h]; rfl)
    have bits : Wait3 x (rightNeighbor e) := D ▸ W
    have op : get b 78 3 (by decide)=3 := bits.2
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
  · unfold Wait3
    rw [reset_remote_frame_raw x e r E (Ne.symm D)]
    exact W

theorem reply_canonical {s n : Nat} (x : Raw s n) (e : Fin n) (j : Fin 3)
    (d : Nat) (H : oldK (header x e) (x e).mis1 j=readFront d) :
    ∃ ok p, replyPacket x e j=ShortReadReturnHop.readReply ok p := by
  unfold replyPacket
  rw [read_turnPacket _ _ _ _ _ (congrArg Token.opcode H) (congrArg Token.fault H)]
  split <;> split <;> (try split)
  all_goals first
    | exact ⟨true,⟨_,Nat.mod_lt _ (by decide)⟩,rfl⟩
    | exact ⟨false,0,rfl⟩

/-- One variable-payload READ, with old trails behind and an empty suffix. -/
def Forward {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (i d : Nat) : Prop :=
  i<R.length ∧ d<128 ∧ Wait3 x R.root ∧ TrailPrefix R x i ∧
    bits R x i=encode (readFront d) ∧ ShortHelloForward.ClearSuffix R x i

def Turned {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (ok : Bool) (d : Fin 64) : Prop :=
  Wait3 x R.root ∧ TrailPrefix R x (R.length-1) ∧
    bits R x (R.length-1)=encode (ShortReadReturnHop.readReply ok d)

theorem forward_from_actual_issue3 {s n : Nat} {h : Fin n → Bool} (C : Chart h)
    (x : Raw s n) (heads : ∀ j, header x j=h j)
    (I : ShortClearLaunch.ClearIssue C x 3) :
    Forward C.route (rawNext s x (RearTrace.predecessor C.root)) 0 64 := by
  have F := ShortClearLaunch.clean_launch C x heads 3 I
  exact ⟨C.positive,by decide,⟨F.1,F.2.1⟩,fun j J=>False.elim (by omega),F.2.2.1,F.2.2.2⟩

theorem forward_all_mark {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ j, header x j=h j) (i d : Nat) (A : Forward R x i d) :
    let y := rawNext s x e
    if e=nextAt R.root i then
      if i+1<R.length then
        Forward R y (i+1) (hopPacket x e (R.port i) (R.port (i+1))).payload
      else ∃ ok p, Turned R y ok p ∧ replyPacket x e (R.port i)=ShortReadReturnHop.readReply ok p
    else Forward R y i d := by
  obtain ⟨I,D,W,L,F,C⟩ := A
  have B := forward_step R x e sep heads W.1 W.2 i I d D L F
  have W' := wait_forward_or_trail x R.root e d sep ((heads _).trans R.rootHeader) W (fun _=>by
    have V : slot R x 0=readFront d ∨ slot R x 0=T := by
      by_cases E : i=0
      · subst i; exact .inl (slot_of_bits R x 0 _ (fun g=>decode_front g d D) F)
      · exact .inr (slot_of_bits R x 0 T trail_decode (L 0 (by omega)))
    have H := (heads R.root).trans R.rootHeader
    simpa only [slot,nextAt,H,R.rootPort] using V)
  have C' := ShortHelloForward.clear_suffix_step R x e sep heads i C
  dsimp only
  by_cases E : e=nextAt R.root i
  · rw [if_pos E]
    subst e
    by_cases S : i+1<R.length
    · rw [if_pos S]
      simp only [if_pos S] at B
      have T : TrailPrefix R (rawNext s x (nextAt R.root i)) (i+1) := by
        intro j J
        by_cases H : j=i
        · simpa only [H] using B.2.2.1
        · exact B.1 j (by omega)
      exact ⟨S,B.2.1,W',T,B.2.2.2,by simpa [ShortHelloForward.ahead] using C'⟩
    · rw [if_neg S]
      simp only [if_neg S] at B
      have Q := slot_of_bits R x i _ (fun g=>decode_front g d D) F
      obtain ⟨ok,p,P⟩ := reply_canonical x (nextAt R.root i) (R.port i) d Q
      have J : i=R.length-1 := by omega
      rw [P] at B
      refine ⟨ok,p,⟨W',?_,?_⟩,P⟩
      · rw [←J]
        exact B.1
      · rw [←J]
        exact B.2
  · rw [if_neg E]
    simp only [if_neg E] at B
    exact ⟨I,D,W',B.1,B.2,by simpa [ShortHelloForward.ahead,E] using C'⟩

#print axioms decode_front
#print axioms hop_packet_canonical
#print axioms forward_step
#print axioms reply_canonical
#print axioms forward_from_actual_issue3
#print axioms forward_all_mark
end L4.ShortReadForward
