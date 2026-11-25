import Leader.L4.ShortResetChart
import Leader.L4.ShortResetMIS1Ring

namespace L4.ShortResetForwardH2
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetFlow ShortResetRow
open ShortResetMIS1Ring ShortResetChart
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

structure Route {n : Nat} (rightHeader : Fin n → Bool) where
  root : Fin n
  length : Nat
  positive : 0<length
  port : Nat → Fin 3
  rootPort : port 0=0
  rootHeader : rightHeader root=true
  live : ∀ i, i+1<length →
    destination (rightHeader (rightNeighbor (nextAt root i))) (port i)=some (port (i+1))
  turn : destination (rightHeader (rightNeighbor (nextAt root (length-1)))) (port (length-1))=none
  injectiveOn : ∀ i j, i<length → j<length → nextAt root i=nextAt root j → i=j

def slot {s n : Nat} {h : Fin n → Bool} (R : Route h) (x : Raw s n) (i : Nat) : Token :=
  let q := nextAt R.root i
  oldK (header x q) (x q).mis1 (R.port i)

def bits {s n : Nat} {h : Fin n → Bool} (R : Route h) (x : Raw s n) (i : Nat) : BitVec 19 :=
  (kField (R.port i)).read (x (nextAt R.root i)).mis1

def TrailPrefix {s n : Nat} {h : Fin n → Bool} (R : Route h) (x : Raw s n) (i : Nat) : Prop :=
  ∀ j, j<i → bits R x j=encode T

theorem slot_of_bits {s n : Nat} {h : Fin n → Bool} (R : Route h) (x : Raw s n) (i : Nat)
    (tok : Token) (safe : (∀ gate, decode gate (encode tok)=tok))
    (old : bits R x i=encode tok) : slot R x i=tok := by
  unfold slot oldK
  dsimp only
  change decode _ (bits R x i)=tok
  rw [old]
  exact safe _

/-- Local frontier facts before the turning mark. The caller provides
settled old-H1 geometry and root WAIT0 only until this frontier step. -/
theorem forward_step {s n : Nat} {h : Fin n → Bool} (R : Route h)
    (x : Raw s n) (e : Fin n) (sep : e≠rightNeighbor e)
    (heads : ∀ q, header x q=h q)
    (wait : get (x R.root).mis1 81 2 (by decide)=2)
    (op : get (x R.root).mis1 78 3 (by decide)=0)
    (i : Nat) (I : i<R.length)
    (trails : TrailPrefix R x i) (front : bits R x i=encode resetForward) :
    let y := rawNext s x e
    TrailPrefix R y i ∧
      (if e=nextAt R.root i then
        if i+1<R.length then bits R y i=encode T ∧ bits R y (i+1)=encode resetForward
        else bits R y i=encode resetReply
      else bits R y i=encode resetForward) := by
  dsimp only
  let y := rawNext s x e
  have Tf j J := slot_of_bits R x j T trail_decode (trails j J)
  have Ff := slot_of_bits R x i resetForward resetForward_decode front
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
      (safe : slot R x j=resetForward ∨ slot R x j=T) :
      (kField (R.port j)).read (y (nextAt R.root j)).mis1=
      (kField (R.port j)).read (x (nextAt R.root j)).mis1 := by
    by_cases zero : j=0
    · subst j
      change rightNeighbor e=R.root at h'
      rw [R.rootPort]
      have hd : header x (rightNeighbor e)=true := by rw [h',heads,R.rootHeader]
      rw [←h']
      have hs : header x R.root=true := by rw [heads,R.rootHeader]
      have S : oldK true (x (rightNeighbor e)).mis1 0=resetForward ∨
          oldK true (x (rightNeighbor e)).mis1 0=T := by
        rw [h',←R.rootPort,←hs]
        exact safe
      exact reset_root_inbound_frame_raw x e sep hd (by simpa only [h'] using wait)
        (by simpa only [h'] using op) S
    · let p := j-1
      have ep : e=nextAt R.root p := predecessor j (Nat.pos_of_ne_zero zero) h'
      have P : p+1=j := by dsimp [p]; omega
      have link : destination (header x (rightNeighbor e)) (R.port p)=some (R.port j) := by
        rw [ep,←P]
        have H := dst p (by omega)
        rwa [P] at H ⊢
      rw [←h']
      apply reset_inbound_frame_raw x e sep (R.port p) _ link
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
      have safe : slot R x (j+1)=resetForward ∨ slot R x (j+1)=T := by
        rcases Nat.eq_or_lt_of_le K with E|E
        · exact .inl (E.symm ▸ Ff)
        · exact .inr (Tf _ E)
      have H := reset_prefix_trail_frame_raw x e sep (R.port j) (R.port (j+1))
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
        have H := reset_out_raw x (nextAt R.root i) sep _ _ (dst i J) Ff
        exact H
      · rename_i J
        have E : i=R.length-1 := by omega
        have H := reset_turn_raw x (nextAt R.root i) sep _ (by rw [heads,E]; exact R.turn) Ff
        exact H
    · rename_i E
      apply Eq.trans _ front
      unfold bits
      by_cases K : nextAt R.root i=rightNeighbor e
      · exact hold_in i (by omega) K.symm (.inl Ff)
      · have F := reset_remote_frame_raw x e (nextAt R.root i) (Ne.symm E) K
        exact congrArg ((kField (R.port i)).read) F

/-- A settled maximal H1 arrangement gives every selected source an actual
fixed MIS1 rail with six to nine physical sites. -/
theorem route_exists {s n : Nat} (x : Raw s n) (M : PhysicalCustody.H1.rawMaximal x)
    (r : Fin n) (R : header x r=true) (N : 9<n) :
    ∃ C : Route (header x), C.root=r ∧ 6≤C.length ∧ C.length≤9 := by
  obtain ⟨a,b,c,A,B,C,Z,_,L,T,I⟩ :=
    ShortResetChart.destination_chart M r R N
  let C : Route (header x) :=
    ⟨r,a+b+c,by omega,ShortResetChart.lane a b,Z,R,L,T,
      fun i j hi hj E=>I i j (by omega) (by omega) E⟩
  exact ⟨C,rfl,by change 6≤a+b+c; omega,by change a+b+c≤9; omega⟩

end L4.ShortResetForwardH2
