import Leader.L4.ShortAdmitFlightSync
import Leader.L4.ShortDirtyMIS1Ring

namespace L4.ShortAdmitReverse
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow ShortResetMIS1Ring
open ShortResetChart ShortResetCycle ShortResetForwardH2 PhysicalCustody ShortHelloAdmitCodec
open ShortDirtyMIS1Ring ShortEmptyOwnership ShortAdmitFlightSync
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def trailAt (won : Bool) (k i : Nat) : Token :=
  if i<k then T else if i=k then (admitReply won) else E

def RevCells {s n : Nat} (won : Bool) (x : Raw s n) (r : Fin n) (a b L k : Nat)
    : Prop :=
  ∀ i : Nat, i<L → (kField (lane a b i)).read (x (nextAt r i)).mis1=encode (trailAt won k i)

variable {won : Bool}

private theorem trail_decode_all (g : Bool) (k i : Nat) :
    decode g (encode (trailAt won k i))=trailAt won k i := by
  unfold trailAt
  split
  · exact trail_decode g
  · split
    · exact decode_admit_reply g won
    · exact empty_decode g

private theorem old_at {s n a b L k : Nat} {x : Raw s n} {r : Fin n}
   
    (H : RevCells won x r a b L k) (i : Nat) (I : i<L) :
    oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=trailAt won k i := by
  change decode _ ((kField (lane a b i)).read (x (nextAt r i)).mis1)=_
  rw [H i I,trail_decode_all]

/-- Same physical pair and old snapshot. A canonical D (canonical HELLO) is kept at its old position if the outgoing mark faces the
cleared suffix or the terminal boundary. -/
theorem reverse_outbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=(admitReply won))
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
    simpa [normalizedNoForward,S,admitReply] using H
  | some k =>
    have F := clear k A
    have C : (oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k).tag=0 := by rw [F]; rfl
    have H := (dirty_nonforward_empty_raw x e sep j k A notFor C).1
    rw [S] at H
    simpa [normalizedNoForward,S,admitReply] using H

theorem reverse_inbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=(admitReply won))
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

private theorem isTrail {k i : Nat} (I : i<k) : trailAt won k i=T := by simp [trailAt,I]
private theorem isReply (k : Nat) : trailAt won k k=(admitReply won) := by simp [trailAt]
private theorem isClear {k i : Nat} (I : k<i) : trailAt won k i=E := by
  simp [trailAt,show ¬i<k by omega,show i≠k by omega]

private theorem side {k i : Nat} (I : k≤i) : trailAt won k i=E ∨ trailAt won k i=(admitReply won) := by
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
   
    (D : Dst x r a b L) (H : RevCells won x r a b L k) (_K : k<L) (I : i+1<L)
    (sep : nextAt r i≠rightNeighbor (nextAt r i)) :
    let j := if i+1=k then i else k
    let y := rawNext s x (nextAt r i)
    (kField (lane a b i)).read (y (nextAt r i)).mis1=encode (trailAt won j i) ∧
    (kField (lane a b (i+1))).read (y (nextAt r (i+1))).mis1=encode (trailAt won j (i+1)) := by
  dsimp only
  have F := dstSome D I
  have A := old_at H i (by omega)
  have B := old_at H (i+1) I
  change oldK (header x (rightNeighbor (nextAt r i))) (x (rightNeighbor (nextAt r i))).mis1 _ = _ at B
  by_cases M : i+1=k
  · rw [if_pos M, isReply, isClear (by omega : i<i+1)]
    rw [isTrail (by omega : i<k)] at A
    rw [show trailAt won k (i+1)=(admitReply won) from M.symm ▸ isReply k] at B
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
          oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=(admitReply won) :=
        A ▸ side (by omega)
      rw [isClear (by omega : k<i+1)] at B
      refine ⟨(reverse_outbound_raw _ _ sep _ AB ?_).trans (H i (by omega)),
        (reverse_inbound_raw _ _ sep _ _ F AB B).trans (H (i+1) I)⟩
      intro j J
      rw [F] at J
      cases J
      exact B

theorem terminal_edge {s n a b L k i : Nat} {x : Raw s n} {r : Fin n}
   
    (D : Dst x r a b L) (H : RevCells won x r a b L k) (K : k<L) (I : i+1=L)
    (sep : nextAt r i≠rightNeighbor (nextAt r i)) :
    (kField (lane a b i)).read (rawNext s x (nextAt r i) (nextAt r i)).mis1=
       encode (trailAt won k i) := by
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
   
    (D : Dst x r a b L) (H : RevCells won x r a b L (k+1)) (K : k+1<L)
    (N : 1<n) (LN : L<n) :
    RevCells won (rawNext s x (nextAt r k)) r a b L k := by
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
   
    (D : Dst x r a b L) (H : RevCells won x r a b L k) (K : k<L) (N : 1<n)
    (notMove : ∀ i : Nat, i+1=k → e≠nextAt r i)
    (rootHold : rightNeighbor e=r →
      (kField (lane a b 0)).read (rawNext s x e r).mis1=
        (kField (lane a b 0)).read (x r).mis1) :
    RevCells won (rawNext s x e) r a b L k := by
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

theorem wait2_root_trail_holds {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (head : header x (rightNeighbor e)=true)
    (W : Wait2 x (rightNeighbor e))
    (trail : (kField 0).read (x (rightNeighbor e)).mis1=encode T) :
    (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=encode T := by
  let u := (x (rightNeighbor e)).mis1
  have H : oldK true u 0=T := by
    change decode (atGate true u 0) ((kField 0).read (x (rightNeighbor e)).mis1)=T
    rw [trail,trail_decode]
  have tags : (oldK true u 0).tag=1 ∨ (oldK true u 0).tag=2 := by
    rw [H]; exact .inl rfl
  have cmd : get u 78 3 (by decide)=2 := W.2
  have O := source_wait_holds u (oldK true u 0) W.1 (by rw [cmd]; decide) tags
  have P := source_door_k0_raw x e sep head
  change (kField 0).read (rawNext s x e (rightNeighbor e)).mis1=
      (match (source u (oldK true u 0)).2 with
       | none => normalizedNoForward true u 0
       | some t => encode t) at P
  rw [O] at P
  exact (by simpa [normalizedNoForward,H,T] using P : _ = (kField 0).read u).trans trail

def Returning {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (k : Nat) (won : Bool) : Prop :=
  k<C.L ∧ Wait2 x C.root ∧ RevCells won x C.root C.a C.b C.L k

theorem to_sync {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (k : Nat) (won : Bool) (H : Returning C x k won) : Rev C x k won := by
  refine ⟨H.1,H.2.1,?_⟩
  intro j J
  change bits C.route x j = _
  have A : bits C.route x j = encode (trailAt won k j) := H.2.2 j J
  rw [A,trailAt]
  split <;> first | rfl | split <;> rfl

theorem of_sync {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (k : Nat) (won : Bool) (H : Rev C x k won) : Returning C x k won := by
  refine ⟨H.1,H.2.1,?_⟩
  intro j J
  change bits C.route x j = _
  rw [H.2.2 j J,trailAt]
  split <;> first | rfl | split <;> rfl

theorem returning_step {s n : Nat} {h : Fin n → Bool} (C : Chart h) (x : Raw s n)
    (N : 1<n) (heads : ∀ q, header x q=h q) (e : Fin n) (k : Nat)
    (H : Returning C x k won) :
    let st := nextStage C e (.rev k)
    match st with
    | .rev l => Returning C (rawNext s x e) l won
    | .done => ShortClearLaunch.ClearIssue C (rawNext s x e) (if won then 3 else 0)
    | .fwd _ => False := by
  have D : Dst x C.root C.a C.b C.L := C.actual_dst x heads
  have hd : header x C.root=true := (heads C.root).trans C.rootHeader
  have sep := edge_sep N e
  cases k with
  | zero =>
    by_cases J : rightNeighbor e=C.root
    · have E : e=RearTrace.predecessor C.root := by
        have E := congrArg RearTrace.predecessor J
        simpa only [RearTrace.predecessor_right] using E
      subst e
      simpa [nextStage, RearTrace.right_predecessor] using
        consume_all_slots C x heads won (to_sync C x 0 won H)
    · have W := wait2_holds x C.root e sep hd H.2.1
        (fun R => False.elim (J R))
      have X := idle (e:=e) D H.2.2 H.1 N (fun i I=>by omega)
        (fun R=>False.elim (J R))
      simpa [nextStage,J] using (show Returning C (rawNext s x e) 0 won from ⟨H.1,W,X⟩)
  | succ k =>
    have KL : k+1<C.L := H.1
    have old := old_at H.2.2 0 (by omega)
    change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=_ at old
    rw [hd,C.rootPort,isTrail (Nat.zero_lt_succ k)] at old
    have W := wait2_holds x C.root e sep hd H.2.1
      (fun _ => .inl (by rw [old]; rfl))
    by_cases J : e=nextAt C.root k
    · subst e
      have X := advance D H.2.2 H.1 N C.length_lt
      simpa [nextStage] using
        (show Returning C (rawNext s x (nextAt C.root k)) k won from ⟨by omega,W,X⟩)
    · have X := idle (e:=e) D H.2.2 H.1 N
        (fun i I => by
          have K : i=k := by omega
          subst i
          exact J) (fun R => by
          have hh : header x (rightNeighbor e)=true := R ▸ hd
          have ww : Wait2 x (rightNeighbor e) := R ▸ H.2.1
          have t := H.2.2 0 (by omega)
          change (kField (lane C.a C.b 0)).read (x C.root).mis1=encode (trailAt won (k+1) 0) at t
          rw [C.rootPort,isTrail (Nat.zero_lt_succ k),←R] at t
          have P := wait2_root_trail_holds x e sep hh ww t
          rw [C.rootPort,←R]
          exact P.trans t.symm)
      simpa [nextStage,J] using
        (show Returning C (rawNext s x e) (k+1) won from ⟨H.1,W,X⟩)

end L4.ShortAdmitReverse
