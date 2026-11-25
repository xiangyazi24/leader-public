import Leader.L4.ShortHelloForward
import Leader.L4.ShortDirtyMIS1Ring
import Leader.L4.ShortEmptyOwnership

namespace L4.ShortHelloReverseChart
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 PhysicalCustody
open ShortDirtyMIS1Ring ShortEmptyOwnership
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def trailAt (k i : Nat) : Token :=
  if i<k then T else if i=k then helloReply else E

def Rev {s n : Nat} (x : Raw s n) (r : Fin n) (a b L k : Nat)
    : Prop :=
  ∀ i : Nat, i<L → (kField (lane a b i)).read (x (nextAt r i)).mis1=encode (trailAt k i)

private theorem trail_decode_all (g : Bool) (k i : Nat) :
    decode g (encode (trailAt k i))=trailAt k i := by
  unfold trailAt
  split
  · exact trail_decode g
  · split
    · exact by cases g <;> decide
    · exact empty_decode g

private theorem old_at {s n a b L k : Nat} {x : Raw s n} {r : Fin n}
   
    (H : Rev x r a b L k) (i : Nat) (I : i<L) :
    oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=trailAt k i := by
  change decode _ ((kField (lane a b i)).read (x (nextAt r i)).mis1)=_
  rw [H i I,trail_decode_all]

/-- Same physical pair and old snapshot. A canonical D (canonical HELLO) is kept at its old position if the outgoing mark faces the
cleared suffix or the terminal boundary. -/
theorem reverse_outbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=helloReply)
    (clear : ∀ k, destination (header x (rightNeighbor e)) j=some k →
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 := by
  rcases safe with S|S
  · exact (work_to_raw x e sep j).1.trans
      (reset_reverse_outbound_frame_pair _ _ _ _ _ (.inl S) clear)
  have notFor : (oldK (header x e) (x e).mis1 j).tag≠2 := by rw [S]; exact (by decide : 3 ≠ 2)
  cases A : destination (header x (rightNeighbor e)) j with
  | none =>
    have H := dirty_nonforward_terminal_raw x e sep j A notFor
    rw [S] at H
    simpa [normalizedNoForward,S,helloReply] using H
  | some k =>
    have F := clear k A
    have C : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=0 := by rw [F]; rfl
    have H := (dirty_nonforward_empty_raw x e sep j k A notFor C).1
    rw [S] at H
    simpa [normalizedNoForward,S,helloReply] using H

theorem reverse_inbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=helloReply)
    (clear : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 := by
  have notFor : (oldK (header x e) (x e).mis1 j).tag≠2 := by
    rcases safe with F|F
    · rw [F]; decide
    · rw [F]; exact (by decide : 3 ≠ 2)
  have C : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=0 := by rw [clear]; rfl
  have H := (dirty_nonforward_empty_raw x e sep j k dst notFor C).2
  simpa [normalizedNoForward,clear,E] using H

def Dst {s n : Nat} (x : Raw s n) (r : Fin n) (a b L : Nat) : Prop :=
  ∀ i : Nat, i<L → destination (header x (rightNeighbor (nextAt r i))) (lane a b i)
    = if i+1<L then some (lane a b (i+1)) else none

private theorem isTrail {k i : Nat} (I : i<k) : trailAt k i=T := by simp [trailAt,I]
private theorem isReply (k : Nat) : trailAt k k=helloReply := by simp [trailAt]
private theorem isClear {k i : Nat} (I : k<i) : trailAt k i=E := by
  simp [trailAt,show ¬i<k by omega,show i≠k by omega]

private theorem side {k i : Nat} (I : k≤i) : trailAt k i=E ∨ trailAt k i=helloReply := by
  by_cases E : i=k
  · subst i; exact .inr (isReply k)
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
   
    (D : Dst x r a b L) (H : Rev x r a b L k) (_K : k<L) (I : i+1<L)
    (sep : nextAt r i≠rightNeighbor (nextAt r i)) :
    let j := if i+1=k then i else k
    let y := rawNext s x (nextAt r i)
    (kField (lane a b i)).read (y (nextAt r i)).mis1=encode (trailAt j i) ∧
    (kField (lane a b (i+1))).read (y (nextAt r (i+1))).mis1=encode (trailAt j (i+1)) := by
  dsimp only
  have F := dstSome D I
  have A := old_at H i (by omega)
  have B := old_at H (i+1) I
  change oldK (header x (rightNeighbor (nextAt r i))) (x (rightNeighbor (nextAt r i))).mis1 _ = _ at B
  by_cases M : i+1=k
  · rw [if_pos M, isReply, isClear (by omega : i<i+1)]
    rw [isTrail (by omega : i<k)] at A
    rw [show trailAt k (i+1)=helloReply from M.symm ▸ isReply k] at B
    have no : (oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)).tag≠2 := by rw [A]; decide
    have reply : (oldK (header x (rightNeighbor (nextAt r i)))
        (x (rightNeighbor (nextAt r i))).mis1 (lane a b (i+1))).tag=3 := by rw [B]; rfl
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
          oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=helloReply :=
        A ▸ side (by omega)
      rw [isClear (by omega : k<i+1)] at B
      refine ⟨(reverse_outbound_raw _ _ sep _ AB ?_).trans (H i (by omega)),
        (reverse_inbound_raw _ _ sep _ _ F AB B).trans (H (i+1) I)⟩
      intro j J
      rw [F] at J
      cases J
      exact B

theorem terminal_edge {s n a b L k i : Nat} {x : Raw s n} {r : Fin n}
   
    (D : Dst x r a b L) (H : Rev x r a b L k) (K : k<L) (I : i+1=L)
    (sep : nextAt r i≠rightNeighbor (nextAt r i)) :
    (kField (lane a b i)).read (rawNext s x (nextAt r i) (nextAt r i)).mis1=
       encode (trailAt k i) := by
  have F : destination (header x (rightNeighbor (nextAt r i))) (lane a b i)=none := by
    simpa [I] using D i (by omega)
  have A := old_at H i (by omega)
  refine (reverse_outbound_raw _ _ sep _ (A ▸ side (by omega)) ?_).trans (H i (by omega))
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
   
    (D : Dst x r a b L) (H : Rev x r a b L (k+1)) (K : k+1<L)
    (N : 1<n) (LN : L<n) :
    Rev (rawNext s x (nextAt r k)) r a b L k := by
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
root-inbound clause holds. For a live root in WAIT0 this clause is derived
below when the reply has not arrived; root consumption is a separate case. -/
theorem idle {s n a b L k : Nat} {x : Raw s n} {r e : Fin n}
   
    (D : Dst x r a b L) (H : Rev x r a b L k) (K : k<L) (N : 1<n)
    (notMove : ∀ i : Nat, i+1=k → e≠nextAt r i)
    (rootHold : rightNeighbor e=r →
      (kField (lane a b 0)).read (rawNext s x e r).mis1=
        (kField (lane a b 0)).read (x r).mis1) :
    Rev (rawNext s x e) r a b L k := by
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

def Wait1 {s n : Nat} (x : Raw s n) (r : Fin n) : Prop :=
  get (x r).mis1 81 2 (by decide)=2 ∧ get (x r).mis1 78 3 (by decide)=1

theorem wait1_held_step {s n : Nat} (x : Raw s n) (r e : Fin n)
    (sep : e≠rightNeighbor e) (hd : header x r=true) (W : Wait1 x r)
    (hold : rightNeighbor e=r →
      (oldK true (x r).mis1 0).tag=1 ∨ (oldK true (x r).mis1 0).tag=2) :
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
      change (oldK true (x (rightNeighbor e)).mis1 0).tag=1 ∨
        (oldK true (x (rightNeighbor e)).mis1 0).tag=2
      rw [D]
      exact hold D
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

/-- A WAIT3 source neither changes its controller nor consumes its
canonical K0 trail when an incoming mark precedes HELLO arrival. -/
theorem wait1_root_trail_holds {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (W : Wait1 x (rightNeighbor e))
    (trail : (kField 0).read (x (rightNeighbor e)).mis1=encode T) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=encode T := by
  let u := (x (rightNeighbor e)).mis1
  have H : oldK true u 0=T := by
    change decode (atGate true u 0) ((kField 0).read (x (rightNeighbor e)).mis1)=T
    rw [trail,trail_decode]
  have tags : (oldK true u 0).tag=1 ∨ (oldK true u 0).tag=2 := by
    rw [H]; exact .inl rfl
  have cmd : get u 78 3 (by decide)=1 := W.2
  have O := source_wait_holds u (oldK true u 0) W.1 (by rw [cmd]; decide) tags
  have P := source_door_k0_raw x e sep head
  change (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (match (source u (oldK true u 0)).2 with
       | none => normalizedNoForward true u 0
       | some t => encode t) at P
  rw [O] at P
  exact (by simpa [normalizedNoForward,H,T] using P : _ = (kField 0).read u).trans trail

/-- Current chart and root controller for a HELLO return whose status
and payload were fixed when the packet turned. -/
def Returning {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (k : Nat) : Prop :=
  k<C.L ∧ Wait1 x C.root ∧ Rev x C.root C.a C.b C.L k

/-- The consumed HELLO leaves the owner chart empty and selects ADMIT ISSUE2. -/
def Consumed {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) : Prop :=
  (∀ i : Nat, i<C.L → bits C.route x i=encode E) ∧
    get (x C.root).mis1 81 2 (by decide)=1 ∧ get (x C.root).mis1 78 3 (by decide)=2

private theorem pc_small {n : Nat} (a : Field 96 n) (b : BitVec 96)
    (lower : 78≤a.offset) (upper : a.offset+n≤83) (v : Nat)
    (V : (a.read ((phaseOp 1 2).apply 0)).toNat=v) :
    (a.read ((phaseOp 1 2).apply b)).toNat=v := by
  have H : a.read ((phaseOp 1 2).apply b)=a.read ((phaseOp 1 2).apply 0) := by
    change a.read (((lane 78 5 (by decide)).assign (10 : BitVec 5)).apply b)=
      a.read (((lane 78 5 (by decide)).assign (10 : BitVec 5)).apply 0)
    apply BitVec.eq_of_getLsbD_eq
    intro i ilt
    have M := ((lane 78 5 (by decide)).inMask (10 : BitVec 5) (a.offset+i)).mpr
      ⟨by change 78≤a.offset+i; omega,by change a.offset+i<83; omega⟩
    simp only [Field.read,BitVec.getLsbD_extractLsb',ilt,decide_true,Bool.true_and]
    rw [Patch.write _ _ _ M,Patch.write _ _ _ M]
  rw [H,V]

/-- Old-pair data at the real incoming consume mark. -/
theorem consume_old {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (e : Fin n) (hr : rightNeighbor e=C.root) (H : Returning C x 0) :
    Wait1 x (rightNeighbor e) ∧
      (kField 0).read (x (rightNeighbor e)).mis1=encode helloReply := by
  have Q := H.2.2 0 C.positive
  change (kField (lane C.a C.b 0)).read (x C.root).mis1=encode (trailAt 0 0) at Q
  rw [C.rootPort,isReply,←hr] at Q
  exact ⟨hr ▸ H.2.1,Q⟩

theorem consume {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n) (e : Fin n)
    (hr : rightNeighbor e=C.root) (head : header x C.root=true)
    (H : Returning C x 0) :
    Consumed C (rawNext s x e) := by
  have sep := edge_sep (by have := C.positive; have := C.length_lt; omega) e
  have Q := H.2.2 0 C.positive
  change (kField (lane C.a C.b 0)).read (x C.root).mis1=encode (trailAt 0 0) at Q
  rw [C.rootPort,isReply,←hr] at Q
  have W : Wait1 x (rightNeighbor e) := hr ▸ H.2.1
  have hd : header x (rightNeighbor e)=true := hr ▸ head
  have A : (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=encode E := by
    have B := source_door_k0_raw x e sep hd
    let old := (x (rightNeighbor e)).mis1
    have S : oldK true old 0=helloReply := by
      change decode _ ((kField 0).read old)=helloReply
      rw [Q]
      generalize atGate true old 0 = g
      cases g <;> decide
    change (kField 0).read (rawNext s x e (rightNeighbor e)).mis1 =
      (match (source old (oldK true old 0)).2 with
       | none => normalizedNoForward true old 0
       | some t => encode t) at B
    rw [S] at B
    have P : get old 81 2 (by decide)=2 := W.1
    have K : get old 78 3 (by decide)=1 := W.2
    simpa [source,P,K,helloReply] using B
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
  · let old := (x (rightNeighbor e)).mis1
    have S : oldK true old 0=helloReply := by
      change decode _ ((kField 0).read old)=helloReply
      rw [Q]
      generalize atGate true old 0 = g
      cases g <;> decide
    obtain ⟨b,_,F⟩ := ShortControllerMIS1.source_door_raw x e sep hd
    let f := lane 81 2 (by decide)
    let g := lane 78 3 (by decide)
    have FF := F f (by decide)
    have FG := F g (by decide)
    have P : get old 81 2 (by decide)=2 := W.1
    have K : get old 78 3 (by decide)=1 := W.2
    have HH : source old (oldK true old 0)=(phaseOp 1 2,some E) := by
      rw [S]
      simp [source,P,K,helloReply]
    change f.read (rawNext s x e (rightNeighbor e)).mis1 =
      f.read (match (source old (oldK true old 0)).2 with
        | none => (source old (oldK true old 0)).1.apply b
        | some t => (putK 0 t).apply ((source old (oldK true old 0)).1.apply b)) at FF
    change g.read (rawNext s x e (rightNeighbor e)).mis1 =
      g.read (match (source old (oldK true old 0)).2 with
        | none => (source old (oldK true old 0)).1.apply b
        | some t => (putK 0 t).apply ((source old (oldK true old 0)).1.apply b)) at FG
    rw [HH] at FF FG
    rw [←hr]
    refine ⟨?_,?_⟩
    · change (f.read (rawNext s x e (rightNeighbor e)).mis1).toNat=1
      rw [FF]
      change (f.read ((kField 0).assign (encode E) |>.apply ((phaseOp 1 2).apply b))).toNat=1
      rw [Field.read_other_assign f (kField 0) _ _ (.inr (by decide))]
      exact pc_small f b (by decide) (by decide) _ (by decide)
    · change (g.read (rawNext s x e (rightNeighbor e)).mis1).toNat=2
      rw [FG]
      change (g.read ((kField 0).assign (encode E) |>.apply ((phaseOp 1 2).apply b))).toNat=2
      rw [Field.read_other_assign g (kField 0) _ _ (.inr (by decide))]
      exact pc_small g b (by decide) (by decide) _ (by decide)

/-- One exact marked step in the return half. External marks and
nonprogress marks are not deleted: they preserve the full invariant,
whereas the true incoming door at cursor zero consumes the payload. -/
theorem returning_step {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (N : 1<n) (heads : ∀ q, header x q=h q) (e : Fin n) (k : Nat)
    (H : Returning C x k) :
    let st := nextStage C e (.rev k)
    match st with
    | .rev l => Returning C (rawNext s x e) l
    | .done => Consumed C (rawNext s x e)
    | .fwd _ => False := by
  have D : Dst x C.root C.a C.b C.L := C.actual_dst x heads
  have hd : header x C.root=true := (heads C.root).trans C.rootHeader
  have sep := edge_sep N e
  cases k with
  | zero =>
    by_cases J : rightNeighbor e=C.root
    · simpa [nextStage,J] using consume C x e J hd H
    · have W := wait1_held_step x C.root e sep hd H.2.1
        (fun R => False.elim (J R))
      have X := idle (e:=e) D H.2.2 H.1 N (fun i I=>by omega)
        (fun R=>False.elim (J R))
      simpa [nextStage,J] using (show Returning C (rawNext s x e) 0 from ⟨H.1,W,X⟩)
  | succ k =>
    have KL : k+1<C.L := H.1
    have old := old_at H.2.2 0 (by omega)
    change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_ at old
    rw [hd,C.rootPort,isTrail (Nat.zero_lt_succ k)] at old
    have W := wait1_held_step x C.root e sep hd H.2.1
      (fun _ => .inl (by rw [old]; rfl))
    by_cases J : e=nextAt C.root k
    · subst e
      have X := advance D H.2.2 H.1 N C.length_lt
      simpa [nextStage] using
        (show Returning C (rawNext s x (nextAt C.root k)) k from ⟨by omega,W,X⟩)
    · have X := idle (e:=e) D H.2.2 H.1 N
        (fun i I => by
          have K : i=k := by omega
          subst i
          exact J) (fun R => by
          have hh : header x (rightNeighbor e)=true := R ▸ hd
          have ww : Wait1 x (rightNeighbor e) := R ▸ H.2.1
          have t := H.2.2 0 (by omega)
          change (kField (lane C.a C.b 0)).read (x C.root).mis1=encode (trailAt (k+1) 0) at t
          rw [C.rootPort,isTrail (Nat.zero_lt_succ k),←R] at t
          have P := wait1_root_trail_holds x e sep hh ww t
          rw [C.rootPort,←R]
          exact P.trans t.symm)
      simpa [nextStage,J] using
        (show Returning C (rawNext s x e) (k+1) from ⟨H.1,W,X⟩)

end L4.ShortHelloReverseChart
