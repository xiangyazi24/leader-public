import Leader.L4.ShortResetCycle
import Leader.L4.ShortControllerMIS1
import Leader.L4.ShortDirtyMIS1Ring
import Leader.L4.ShortEmptyOwnership

namespace L4.ShortCanonicalReverseChart
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 PhysicalCustody
open ShortDirtyMIS1Ring ShortEmptyOwnership
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Exact decoder-stable return bytes, including canonical fault/denial. -/
structure Reply where
  token : Token
  tag : token.tag=3
  decode_encode : ∀ g, decode g (encode token)=token

/-- The fault reply is a legal canonical return cursor. -/
def Reply.fault : Reply := ⟨faultToken 3, rfl, by intro g; cases g <;> decide⟩

def trailAt (p : Reply) (k i : Nat) : Token :=
  if i<k then T else if i=k then p.token else E

def Rev {s n : Nat} (x : Raw s n) (r : Fin n) (a b L k : Nat)
    (p : Reply) : Prop :=
  ∀ i : Nat, i<L → (kField (lane a b i)).read (x (nextAt r i)).mis1=encode (trailAt p k i)

private theorem trail_decode_all (g : Bool) (p : Reply) (k i : Nat) :
    decode g (encode (trailAt p k i))=trailAt p k i := by
  unfold trailAt
  split
  · exact trail_decode g
  · split
    · exact p.decode_encode g
    · exact empty_decode g

private theorem old_at {s n a b L k : Nat} {x : Raw s n} {r : Fin n}
   
    {p : Reply} (H : Rev x r a b L k p) (i : Nat) (I : i<L) :
    oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=trailAt p k i := by
  change decode _ ((kField (lane a b i)).read (x (nextAt r i)).mis1)=_
  rw [H i I,trail_decode_all]

/-- Same physical pair and old snapshot. A canonical D is kept at its old position if the outgoing mark faces the
cleared suffix or the terminal boundary. -/
theorem reverse_outbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (p : Reply) (sep : e≠rightNeighbor e) (j : Fin 3)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=p.token)
    (canon : oldK (header x e) (x e).mis1 j=p.token →
      (kField j).read (x e).mis1=encode p.token)
    (clear : ∀ k, destination (header x (rightNeighbor e)) j=some k →
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 := by
  rcases safe with S|S
  · exact (work_to_raw x e sep j).1.trans
      (reset_reverse_outbound_frame_pair _ _ _ _ _ (.inl S) clear)
  have notFor : (oldK (header x e) (x e).mis1 j).tag≠2 := by rw [S,p.tag]; decide
  cases A : destination (header x (rightNeighbor e)) j with
  | none =>
    have H := dirty_nonforward_terminal_raw x e sep j A notFor
    rw [S] at H
    simpa [normalizedNoForward,S,p.tag,canon S] using H
  | some k =>
    have F := clear k A
    have C : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=0 := by rw [F]; rfl
    have H := (dirty_nonforward_empty_raw x e sep j k A notFor C).1
    rw [S] at H
    simpa [normalizedNoForward,S,p.tag,canon S] using H

theorem reverse_inbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (p : Reply) (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=p.token)
    (clear : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 := by
  have notFor : (oldK (header x e) (x e).mis1 j).tag≠2 := by
    rcases safe with F|F
    · rw [F]; decide
    · rw [F,p.tag]; decide
  have C : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=0 := by rw [clear]; rfl
  have H := (dirty_nonforward_empty_raw x e sep j k dst notFor C).2
  simpa [normalizedNoForward,clear,E] using H

def Dst {s n : Nat} (x : Raw s n) (r : Fin n) (a b L : Nat) : Prop :=
  ∀ i : Nat, i<L → destination (header x (rightNeighbor (nextAt r i))) (lane a b i)
    = if i+1<L then some (lane a b (i+1)) else none

private theorem isTrail {p : Reply} {k i : Nat} (I : i<k) : trailAt p k i=T := by simp [trailAt,I]
private theorem isReply (p : Reply) (k : Nat) : trailAt p k k=p.token := by simp [trailAt]
private theorem isClear {p : Reply} {k i : Nat} (I : k<i) : trailAt p k i=E := by
  simp [trailAt,show ¬i<k by omega,show i≠k by omega]

private theorem side {p : Reply} {k i : Nat} (I : k≤i) : trailAt p k i=E ∨ trailAt p k i=p.token := by
  by_cases E : i=k
  · subst i; exact .inr (isReply p k)
  · exact .inl (isClear (by omega))

private theorem dstSome {s n a b L : Nat} {x : Raw s n} {r : Fin n}
    (D : Dst x r a b L) {i : Nat} (I : i+1<L) :
    destination (header x (rightNeighbor (nextAt r i))) (lane a b i)=
      some (lane a b (i+1)) := by
  simpa [I] using D i (by omega)

/-- Both chart coordinates are updated on a scheduled internal edge.
An unchanged trailing edge, the enabled reply edge, and a cleared
suffix edge are all on the actual joined MIS1 row. -/
theorem internal_edge {s n a b L k i : Nat} {x : Raw s n} {r : Fin n}
   
    {p : Reply} (D : Dst x r a b L) (H : Rev x r a b L k p) (_K : k<L) (I : i+1<L)
    (sep : nextAt r i≠rightNeighbor (nextAt r i)) :
    let j := if i+1=k then i else k
    let y := rawNext s x (nextAt r i)
    (kField (lane a b i)).read (y (nextAt r i)).mis1=encode (trailAt p j i) ∧
    (kField (lane a b (i+1))).read (y (nextAt r (i+1))).mis1=encode (trailAt p j (i+1)) := by
  dsimp only
  have F := dstSome D I
  have A := old_at H i (by omega)
  have B := old_at H (i+1) I
  change oldK (header x (rightNeighbor (nextAt r i))) (x (rightNeighbor (nextAt r i))).mis1 _ = _ at B
  by_cases M : i+1=k
  · rw [if_pos M, isReply, isClear (by omega : i<i+1)]
    rw [isTrail (by omega : i<k)] at A
    rw [show trailAt p k (i+1)=p.token from M.symm ▸ isReply p k] at B
    have no : (oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)).tag≠2 := by rw [A]; decide
    have reply : (oldK (header x (rightNeighbor (nextAt r i)))
        (x (rightNeighbor (nextAt r i))).mis1 (lane a b (i+1))).tag=3 := by exact (congrArg Token.tag B).trans p.tag
    have Y := dirty_nonforward_reply_raw x (nextAt r i) sep _ _ F no reply
    rw [B] at Y
    exact Y
  · rw [if_neg M]
    by_cases P : i+1<k
    · rw [isTrail (by omega : i<k)] at A
      rw [isTrail P] at B
      exact ⟨(reset_prefix_trail_frame_raw _ _ sep _ _ F A (.inr B)).trans (H i (by omega)),
        (reset_inbound_frame_raw _ _ sep _ _ F A (.inr B)).trans (H (i+1) I)⟩
    · have AB : oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=E ∨
          oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=p.token :=
        A ▸ side (by omega)
      rw [isClear (by omega : k<i+1)] at B
      refine ⟨(reverse_outbound_raw _ _ p sep _ AB ?_ ?_).trans (H i (by omega)),
        (reverse_inbound_raw _ _ p sep _ _ F AB B).trans (H (i+1) I)⟩
      · intro EQ
        exact (H i (by omega)).trans (congrArg encode (A.symm.trans EQ))
      intro j J
      rw [F] at J
      cases J
      exact B

theorem terminal_edge {s n a b L k i : Nat} {x : Raw s n} {r : Fin n}
   
    {p : Reply} (D : Dst x r a b L) (H : Rev x r a b L k p) (K : k<L) (I : i+1=L)
    (sep : nextAt r i≠rightNeighbor (nextAt r i)) :
    (kField (lane a b i)).read (rawNext s x (nextAt r i) (nextAt r i)).mis1=
       encode (trailAt p k i) := by
  have F : destination (header x (rightNeighbor (nextAt r i))) (lane a b i)=none := by
    simpa [I] using D i (by omega)
  have A := old_at H i (by omega)
  refine (reverse_outbound_raw _ _ p sep _ (A ▸ side (by omega)) ?_ ?_).trans (H i (by omega))
  · intro EQ
    exact (H i (by omega)).trans (congrArg encode (A.symm.trans EQ))
  intro j J
  rw [F] at J
  cases J

private theorem neighbor_inj {n : Nat} {u v : Fin n} (E : rightNeighbor u=rightNeighbor v) :
    u=v := by
  apply Fin.ext
  have F := congrArg Fin.val E
  change (u.val+1)%n=(v.val+1)%n at F
  have h := u.isLt
  have g := v.isLt
  by_cases U : u.val+1<n
  · rw [Nat.mod_eq_of_lt U] at F
    by_cases V : v.val+1<n
    · rw [Nat.mod_eq_of_lt V] at F; omega
    · rw [show v.val+1=n by omega,Nat.mod_self] at F; omega
  · rw [show u.val+1=n by omega,Nat.mod_self] at F
    by_cases V : v.val+1<n
    · rw [Nat.mod_eq_of_lt V] at F; omega
    · omega

private theorem edge_sep {n : Nat} (N : 1<n) (e : Fin n) : e≠rightNeighbor e := by
  intro E
  have F := congrArg Fin.val E
  change e.val=(e.val+1)%n at F
  have h := e.isLt
  by_cases J : e.val+1<n
  · rw [Nat.mod_eq_of_lt J] at F; omega
  · rw [show e.val+1=n by omega,Nat.mod_self] at F; omega

/-- The enabled return edge moves the cursor back one position. All other
chart coordinates on that actual raw step are physically disjoint. -/
theorem advance {s n a b L k : Nat} {x : Raw s n} {r : Fin n}
   
    {p : Reply} (D : Dst x r a b L) (H : Rev x r a b L (k+1) p) (K : k+1<L)
    (N : 1<n) (LN : L<n) :
    Rev (rawNext s x (nextAt r k)) r a b L k p := by
  have A := internal_edge (i:=k) D H K K (edge_sep N (nextAt r k))
  simp only at A
  intro i I
  by_cases U : i=k
  · subst i; exact A.1
  by_cases V : i=k+1
  · subst i; exact A.2
  have h0 : nextAt r i≠nextAt r k := fun Q=>U (nextAt_injective_under r i k (by omega) (by omega) Q)
  have h1 : nextAt r i≠rightNeighbor (nextAt r k) :=
    fun Q=>V (nextAt_injective_under r i (k+1) (by omega) (by omega) Q)
  rw [reset_remote_frame_raw _ _ _ h0 h1,H i I]
  by_cases X : i<k
  · rw [isTrail X,isTrail (by omega : i<k+1)]
  · rw [isClear (by omega : k<i),isClear (by omega : k+1<i)]

/-- All nonprogress marks preserve the return cursor, provided the separate
root-inbound clause holds. For a live root in WAIT this clause is derived
below when the reply has not arrived; root consumption is a separate case. -/
theorem idle {s n a b L k : Nat} {x : Raw s n} {r e : Fin n}
   
    {p : Reply} (D : Dst x r a b L) (H : Rev x r a b L k p) (K : k<L) (N : 1<n)
    (notMove : ∀ i : Nat, i+1=k → e≠nextAt r i)
    (rootHold : rightNeighbor e=r →
      (kField (lane a b 0)).read (rawNext s x e r).mis1=
        (kField (lane a b 0)).read (x r).mis1) :
    Rev (rawNext s x e) r a b L k p := by
  intro i I
  by_cases U : nextAt r i=e
  · subst e
    by_cases V : i+1<L
    · have A := internal_edge D H K V (edge_sep N (nextAt r i))
      have E : i+1≠k := fun Q=>notMove i Q rfl
      simpa [E] using A.1
    · exact terminal_edge D H K (by omega) (edge_sep N (nextAt r i))
  by_cases V : nextAt r i=rightNeighbor e
  · cases i with
    | zero =>
      change r=rightNeighbor e at V
      exact (rootHold V.symm).trans (H 0 I)
    | succ i =>
      change rightNeighbor (nextAt r i)=rightNeighbor e at V
      have J := neighbor_inj V
      subst e
      have A := internal_edge D H K I (edge_sep N (nextAt r i))
      have E : i+1≠k := fun Q=>notMove i Q rfl
      simpa [E] using A.2
  rw [reset_remote_frame_raw _ _ _ U V,H i I]


def Wait {s n : Nat} (x : Raw s n) (r : Fin n) (op : Nat) : Prop :=
  get (x r).mis1 81 2 (by decide)=2 ∧ get (x r).mis1 78 3 (by decide)=op

theorem wait_held_step {s n : Nat} (x : Raw s n) (r e : Fin n)
    (sep : e≠rightNeighbor e) (hd : header x r=true) {op : Nat} (O : op<7) (W : Wait x r op)
    (hold : rightNeighbor e=r →
      (oldK true (x r).mis1 0).tag=1 ∨ (oldK true (x r).mis1 0).tag=2) :
    Wait (rawNext s x e) r op := by
  by_cases E : r=e
  · subst r
    have K := reset_controller_outgoing_raw x e hd
    exact ⟨K.1.trans W.1,K.2.trans W.2⟩
  by_cases D : rightNeighbor e=r
  · have hd' : header x (rightNeighbor e)=true := D ▸ hd
    let b := (x (rightNeighbor e)).mis1
    let tok := oldK true b 0
    have safe : tok.tag=1 ∨ tok.tag=2 := by
      change (oldK true (x (rightNeighbor e)).mis1 0).tag=1 ∨
        (oldK true (x (rightNeighbor e)).mis1 0).tag=2
      rw [D]
      exact hold D
    have bits : Wait x (rightNeighbor e) op := D ▸ W
    have cmd : get b 78 3 (by decide)=op := bits.2
    have P := source_wait_holds b tok bits.1 (cmd ▸ O) safe
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
  · unfold Wait
    rw [reset_remote_frame_raw x e r E (Ne.symm D)]
    exact W

/-- A WAIT source neither changes its controller nor consumes its
canonical K0 trail when an incoming mark precedes reply arrival. -/
theorem wait_root_trail_holds {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    {op : Nat} (O : op<7) (W : Wait x (rightNeighbor e) op)
    (trail : (kField 0).read (x (rightNeighbor e)).mis1=encode T) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=encode T := by
  let u := (x (rightNeighbor e)).mis1
  have H : oldK true u 0=T := by
    change decode (atGate true u 0) ((kField 0).read (x (rightNeighbor e)).mis1)=T
    rw [trail,trail_decode]
  have tags : (oldK true u 0).tag=1 ∨ (oldK true u 0).tag=2 := by
    rw [H]; exact .inl rfl
  have cmd : get u 78 3 (by decide)=op := W.2
  have O := source_wait_holds u (oldK true u 0) W.1 (cmd ▸ O) tags
  have P := source_door_k0_raw x e sep head
  change (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (match (source u (oldK true u 0)).2 with
       | none => normalizedNoForward true u 0
       | some t => encode t) at P
  rw [O] at P
  exact (by simpa [normalizedNoForward,H,T] using P : _ = (kField 0).read u).trans trail

/-- Current chart and root controller for a reply return whose status
and payload were fixed when the packet turned. -/
def Returning {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (op : Nat) (p : Reply) (k : Nat) : Prop :=
  k<C.L ∧ Wait x C.root op ∧ Rev x C.root C.a C.b C.L k p

/-- Exact local controller response, and clearance of every owned byte slot. -/
def Consumed {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x y : Raw s n)
    (p : Reply) : Prop :=
  (∀ i : Nat, i<C.L → bits C.route y i=encode E) ∧
  ∃ base : BitVec 96,
    (∀ {k : Nat} (f : Field 96 k), 57≤f.offset → f.offset+k≤83 →
      f.read base=f.read (x C.root).mis1) ∧
    (∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
      f.read (y C.root).mis1 =
        f.read ((putK 0 E).apply ((source (x C.root).mis1 p.token).1.apply base)))

/-- On the source controller window, the exact output can be read by applying
the actual source patch directly to the old word: the pair base and K0 write
are both invisible on this window. -/
theorem consumed_controller {s n : Nat} {h : Fin n → Bool} {C : Chart h}
    {x y : Raw s n} {p : Reply} (H : Consumed C x y p)
    {w : Nat} (f : Field 96 w) (A : 57≤f.offset) (B : f.offset+w≤83) :
    f.read (y C.root).mis1 =
      f.read ((source (x C.root).mis1 p.token).1.apply (x C.root).mis1) := by
  obtain ⟨_,base,F,G⟩ := H
  rw [G f (by omega)]
  let U := (source (x C.root).mis1 p.token).1
  change f.read (((kField 0).assign (encode E)).apply (U.apply base))=_
  have sep : (kField 0).offset+19≤f.offset := by change 57≤f.offset; exact A
  rw [Field.read_other_assign f (kField 0) _ _ (.inr sep)]
  have E := F f A B
  apply BitVec.eq_of_getLsbD_eq
  intro i I
  have Q := congrArg (fun v : BitVec w => v.getLsbD i) E
  simp only [Field.read,BitVec.getLsbD_extractLsb',I,decide_true,Bool.true_and] at Q ⊢
  by_cases M : (U.mask.getLsbD (f.offset+i))=true
  · rw [Patch.write _ _ _ M,Patch.write _ _ _ M]
  · have N : U.mask.getLsbD (f.offset+i)=false := by simpa using M
    rw [Patch.hold _ _ _ N,Patch.hold _ _ _ N,Q]

private theorem source_reply {b : BitVec 96} (p : Reply) (hp : get b 81 2 (by decide)=2) :
    (source b p.token).2=some E := by
  unfold source
  dsimp only
  rw [hp,p.tag]
  split <;> simp_all
  split <;> simp_all

/-- Old-pair data at the real incoming consume mark. -/
theorem consume_old {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (hr : rightNeighbor e=C.root) {op : Nat} {p : Reply} (H : Returning C x op p 0) :
    Wait x (rightNeighbor e) op ∧
      (kField 0).read (x (rightNeighbor e)).mis1=encode p.token := by
  have Q := H.2.2 0 C.positive
  change (kField (lane C.a C.b 0)).read (x C.root).mis1=encode (trailAt p 0 0) at Q
  rw [C.rootPort,isReply,←hr] at Q
  exact ⟨hr ▸ H.2.1,Q⟩

theorem consume {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) (e : Fin n)
    (hr : rightNeighbor e=C.root) (head : header x C.root=true)
    {op : Nat} {p : Reply} (H : Returning C x op p 0) :
    Consumed C x (rawNext s x e) p := by
  have sep := edge_sep (by have := C.positive; have := C.length_lt; omega) e
  obtain ⟨W,Q⟩ := consume_old C x e hr H
  have hd : header x (rightNeighbor e)=true := hr ▸ head
  let old := (x (rightNeighbor e)).mis1
  have S : oldK true old 0=p.token := by
    change decode _ ((kField 0).read old)=p.token
    rw [Q,p.decode_encode]
  have Out := source_reply p W.1
  obtain ⟨base,Frame,F⟩ := ShortControllerMIS1.source_door_raw x e sep hd
  change ∀ {k : Nat} (f : Field 96 k), f.offset+k≤93 →
    f.read (rawNext s x e (rightNeighbor e)).mis1 =
      f.read (match (source old (oldK true old 0)).2 with
        | none => (source old (oldK true old 0)).1.apply base
        | some t => (putK 0 t).apply ((source old (oldK true old 0)).1.apply base)) at F
  rw [S,Out] at F
  have A := F (kField 0) (by decide)
  change (kField 0).read (rawNext s x e (rightNeighbor e)).mis1 =
    (kField 0).read (((kField 0).assign (encode E)).apply ((source old p.token).1.apply base)) at A
  rw [Field.read_assign] at A
  refine ⟨?_,?_⟩
  · intro i I
    by_cases Z : i=0
    · subst i
      change (kField (lane C.a C.b 0)).read (rawNext s x e C.root).mis1=_
      rw [C.rootPort,←hr]
      exact A
    · have L := C.length_lt
      have A : nextAt C.root i≠e := by
        intro V
        have F : nextAt C.root (i+1)=nextAt C.root 0 :=
          (congrArg rightNeighbor V).trans hr
        exact (by omega : i+1≠0) (nextAt_injective_under C.root (i+1) 0 (by omega) (by omega) F)
      have B : nextAt C.root i≠rightNeighbor e := by
        intro V
        exact Z (nextAt_injective_under C.root i 0 (by omega) (by omega) (V.trans hr))
      change (kField (lane C.a C.b i)).read (rawNext s x e (nextAt C.root i)).mis1=_
      rw [reset_remote_frame_raw _ _ _ A B,H.2.2 i I,isClear (by omega : 0<i)]
  · rw [←hr]
    exact ⟨base,Frame,F⟩

/-- One exact marked step in the return half. External marks and
nonprogress marks are not deleted: they preserve the full invariant,
whereas the true incoming door at cursor zero consumes the payload. -/
theorem returning_step {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (N : 1<n) (heads : ∀ q, header x q=h q) (e : Fin n) (k : Nat)
    {op : Nat} {p : Reply} (O : op<7) (H : Returning C x op p k) :
    let st := nextStage C e (.rev k)
    match st with
    | .rev l => Returning C (rawNext s x e) op p l
    | .done => Consumed C x (rawNext s x e) p
    | .fwd _ => False := by
  have D : Dst x C.root C.a C.b C.L := C.actual_dst x heads
  have hd : header x C.root=true := (heads C.root).trans C.rootHeader
  have sep := edge_sep N e
  cases k with
  | zero =>
    by_cases J : rightNeighbor e=C.root
    · simpa [nextStage,J] using consume C x e J hd H
    · have W := wait_held_step x C.root e sep hd O H.2.1
        (fun R => False.elim (J R))
      have X := idle (e:=e) D H.2.2 H.1 N (fun i I=>by omega)
        (fun R=>False.elim (J R))
      simpa [nextStage,J] using (show Returning C (rawNext s x e) op p 0 from ⟨H.1,W,X⟩)
  | succ k =>
    have KL : k+1<C.L := H.1
    have old := old_at H.2.2 0 (by omega)
    change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_ at old
    rw [hd,C.rootPort,isTrail (Nat.zero_lt_succ k)] at old
    have W := wait_held_step x C.root e sep hd O H.2.1
      (fun _ => .inl (by rw [old]; rfl))
    by_cases J : e=nextAt C.root k
    · subst e
      have X := advance D H.2.2 H.1 N C.length_lt
      simpa [nextStage] using
        (show Returning C (rawNext s x (nextAt C.root k)) op p k from ⟨by omega,W,X⟩)
    · have X := idle (e:=e) D H.2.2 H.1 N
        (fun i I => by
          have K : i=k := by omega
          subst i
          exact J) (fun R => by
          have hh : header x (rightNeighbor e)=true := R ▸ hd
          have ww : Wait x (rightNeighbor e) op := R ▸ H.2.1
          have t := H.2.2 0 (by omega)
          change (kField (lane C.a C.b 0)).read (x C.root).mis1=encode (trailAt p (k+1) 0) at t
          rw [C.rootPort,isTrail (Nat.zero_lt_succ k),←R] at t
          have P := wait_root_trail_holds x e sep hh O ww t
          rw [C.rootPort,←R]
          exact P.trans t.symm)
      simpa [nextStage,J] using
        (show Returning C (rawNext s x e) op p (k+1) from ⟨H.1,W,X⟩)

#print axioms reverse_outbound_raw
#print axioms reverse_inbound_raw
#print axioms internal_edge
#print axioms terminal_edge
#print axioms wait_held_step
#print axioms wait_root_trail_holds
#print axioms advance
#print axioms idle
#print axioms Reply.fault
#print axioms consumed_controller
#print axioms consume_old
#print axioms consume
#print axioms returning_step
end L4.ShortCanonicalReverseChart
