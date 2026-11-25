import Leader.L4.ShortResetChart
import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortResetReverseChart
open AllSizeProtocol MISByteCodec ShortResetFlow ShortResetRow ShortResetMIS1Ring
open ShortResetChart PhysicalCustody
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def trailAt (k i : Nat) : Token :=
  if i<k then T else if i=k then resetReply else E

def Rev {s n : Nat} (x : Raw s n) (r : Fin n) (a b L k : Nat) : Prop :=
  ∀ i : Nat, i<L → (kField (lane a b i)).read (x (nextAt r i)).mis1=encode (trailAt k i)

private theorem trail_decode_all (g : Bool) (k i : Nat) :
    decode g (encode (trailAt k i))=trailAt k i := by
  unfold trailAt
  split
  · exact trail_decode g
  · split
    · exact resetReply_decode g
    · exact empty_decode g

private theorem old_at {s n a b L k : Nat} {x : Raw s n} {r : Fin n}
    (H : Rev x r a b L k) (i : Nat) (I : i<L) :
    oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=trailAt k i := by
  change decode _ ((kField (lane a b i)).read (x (nextAt r i)).mis1)=_
  rw [H i I,trail_decode_all]

theorem reverse_outbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j : Fin 3)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=resetReply)
    (clear : ∀ k, destination (header x (rightNeighbor e)) j=some k →
      oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField j).read (rawNext s x e e).mis1=(kField j).read (x e).mis1 :=
  (work_to_raw x e sep j).1.trans (reset_reverse_outbound_frame_pair _ _ _ _ _ safe clear)

theorem reverse_inbound_raw {s n : Nat} (x : Raw s n) (e : Fin n)
    (sep : e≠rightNeighbor e) (j k : Fin 3)
    (dst : destination (header x (rightNeighbor e)) j=some k)
    (safe : oldK (header x e) (x e).mis1 j=E ∨
            oldK (header x e) (x e).mis1 j=resetReply)
    (clear : oldK (header x (rightNeighbor e)) (x (rightNeighbor e)).mis1 k=E) :
    (kField k).read (rawNext s x e (rightNeighbor e)).mis1=
      (kField k).read (x (rightNeighbor e)).mis1 :=
  (work_to_raw x e sep k).2.trans (reset_reverse_inbound_frame_pair _ _ _ _ _ _ dst safe clear)

def Dst {s n : Nat} (x : Raw s n) (r : Fin n) (a b L : Nat) : Prop :=
  ∀ i : Nat, i<L → destination (header x (rightNeighbor (nextAt r i))) (lane a b i)
    = if i+1<L then some (lane a b (i+1)) else none

private theorem isTrail {k i : Nat} (I : i<k) : trailAt k i=T := by simp [trailAt,I]
private theorem isReply (k : Nat) : trailAt k k=resetReply := by simp [trailAt]
private theorem isClear {k i : Nat} (I : k<i) : trailAt k i=E := by
  simp [trailAt,show ¬i<k by omega,show i≠k by omega]

private theorem side {k i : Nat} (I : k≤i) : trailAt k i=E ∨ trailAt k i=resetReply := by
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
    rw [show trailAt k (i+1)=resetReply from M.symm ▸ isReply k] at B
    exact reset_back_raw _ _ sep _ _ F A B
  · rw [if_neg M]
    by_cases P : i+1<k
    · rw [isTrail (by omega : i<k)] at A
      rw [isTrail P] at B
      exact ⟨(reset_prefix_trail_frame_raw _ _ sep _ _ F A (.inr B)).trans (H i (by omega)),
        (reset_inbound_frame_raw _ _ sep _ _ F A (.inr B)).trans (H (i+1) I)⟩
    · have AB : oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=E ∨
          oldK (header x (nextAt r i)) (x (nextAt r i)).mis1 (lane a b i)=resetReply :=
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

/-- Root inbound is harmless before the reply reaches the root; this is the
only chart mark not supplied by an internal-edge or terminal-edge rule. -/
theorem idle_before_arrival {s n a b L k : Nat} {x : Raw s n} {r e : Fin n}
    (D : Dst x r a b L) (H : Rev x r a b L k) (K : k<L) (Kp : 0<k)
    (N : 1<n) (L0 : lane a b 0=0) (head : header x r=true)
    (wait : get (x r).mis1 81 2 (by decide)=2)
    (op : get (x r).mis1 78 3 (by decide)=0)
    (notMove : ∀ i : Nat, i+1=k → e≠nextAt r i) :
    Rev (rawNext s x e) r a b L k := by
  apply idle D H K N notMove
  intro hr
  have q := old_at H 0 (by omega)
  change oldK (header x r) (x r).mis1 _ = _ at q
  rw [L0,head,isTrail Kp] at q
  simp only [L0,←hr] at head wait op q ⊢
  exact reset_root_inbound_frame_raw x e (edge_sep N e) head wait op (.inr q)

/-- After the reply arrives, non-root-inbound marks leave it live. -/
theorem idle_at_root {s n a b L : Nat} {x : Raw s n} {r e : Fin n}
    (D : Dst x r a b L) (H : Rev x r a b L 0) (K : 0<L) (N : 1<n)
    (E : rightNeighbor e≠r) : Rev (rawNext s x e) r a b L 0 :=
  idle D H K N (fun i Q=>by omega) (fun q=>False.elim (E q))

/-- The authenticated root's next inbound mark consumes the root reply.
The actual whole owner chart is clear, and the controller enters ISSUE1. -/
theorem consume {s n a b L : Nat} {x : Raw s n} {r e : Fin n}
    (H : Rev x r a b L 0) (K : 0<L) (N : 1<n) (LN : L<n)
    (L0 : lane a b 0=0) (hr : rightNeighbor e=r) (head : header x r=true)
    (wait : get (x r).mis1 81 2 (by decide)=2)
    (op : get (x r).mis1 78 3 (by decide)=0) :
    (∀ i : Nat, i<L →
      (kField (lane a b i)).read (rawNext s x e (nextAt r i)).mis1=encode E) ∧
    get (rawNext s x e r).mis1 81 2 (by decide)=1 ∧
    get (rawNext s x e r).mis1 78 3 (by decide)=1 := by
  have Q := old_at H 0 K
  change oldK (header x r) (x r).mis1 _ = _ at Q
  rw [L0,head,isReply] at Q
  have h : header x (rightNeighbor e)=true := hr ▸ head
  have w : get (x (rightNeighbor e)).mis1 81 2 (by decide)=2 := hr ▸ wait
  have o : get (x (rightNeighbor e)).mis1 78 3 (by decide)=0 := hr ▸ op
  have q : oldK true (x (rightNeighbor e)).mis1 0=resetReply := hr ▸ Q
  have C := reset_consume_controller_raw x e (edge_sep N e) h w o q
  rw [hr] at C
  refine ⟨?_,C⟩
  intro i I
  by_cases J : i=0
  · subst i
    rw [L0]
    exact hr ▸ reset_consume_raw x e (edge_sep N e) h w o q
  have A : nextAt r i≠e := by
    intro V
    have F : nextAt r (i+1)=nextAt r 0 :=
      (congrArg rightNeighbor V).trans hr
    exact (by omega : i+1≠0) (nextAt_injective_under r (i+1) 0 (by omega) (by omega) F)
  have B : nextAt r i≠rightNeighbor e := by
    intro V
    exact J (nextAt_injective_under r i 0 (by omega) (by omega) (V.trans hr))
  rw [reset_remote_frame_raw _ _ _ A B,H i I,isClear (by omega : 0<i)]

#print axioms reverse_outbound_raw
#print axioms reverse_inbound_raw
#print axioms internal_edge
#print axioms terminal_edge
#print axioms advance
#print axioms idle
#print axioms idle_before_arrival
#print axioms idle_at_root
#print axioms consume
end L4.ShortResetReverseChart
