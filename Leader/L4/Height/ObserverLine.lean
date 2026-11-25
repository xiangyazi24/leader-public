import Leader.L4.Height.ObserverGeometry
import Leader.L4.Height.ObserverPhysical
import Leader.L4.Height.ObserverDecoded

/-! The physical ring read as a directed observer path from the source
door through the counterclockwise sites to the source terminal. -/
namespace L4.Height.ObserverLine
open AllSizeProtocol ObserverPhysical ObserverDirty ObserverGeometry
open ObserverDirty.Decoded (slot control terminalSeen)
noncomputable section
variable {a : LargeParams} {n : Nat}
def token (r : Fin n) (x : Ring a n) (i : Nat) : Nat :=
  if i<n then (slots x (pos r i)).a else if i=n then (slots x r).b else 0
def line (r : Fin n) (x : Ring a n) : Line :=
  ⟨fun i => slot (token r x i),control (slots x r).pc⟩
def before (hp : 0<a.p) (x : Ring a n) (e : Fin n) : Pair Bool :=
  ((pub hp x e).mark,(pub hp x (rightNeighbor e)).mark)
def turn (hp : 0<a.p) (r : Fin n) (x : Ring a n) (k : Fin n) :=
  terminalSeen (slots x (pos r k.val)) (before hp x (edge r k)) (ordinaryMarks hp x (edge r k))

theorem old_source (r k : Fin n) (x : Ring a n) :
    (line r x).slot k.val = slot (slots x (pos r k.val)).a := by
  simp only [line,token,if_pos k.isLt]

theorem old_dest (r k : Fin n) (x : Ring a n) :
    (line r x).slot (k.val+1) =
      slot (if k.val+1=n then (slots x (edge r k)).b else (slots x (edge r k)).a) := by
  have K := k.isLt
  by_cases eq : k.val+1=n
  · simp [line,token,eq,edge,ObserverGeometry.terminal]
  · have lt : k.val+1<n := by omega
    simp [line,token,edge,lt,eq]

theorem ref_value {b : LargeRows a} {r : Fin n} {x : Ring a n} (h : Fixed b x r)
    (i : Fin n) : refBit b x i=decide (i=r) := by
  have H := h [] i
  change refBit b x i=true ↔ i=r at H
  cases E : refBit b x i <;> simp_all

theorem pair_at (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    {r : Fin n} {x : Ring a n} (h : Fixed b x r) (k : Fin n) :
    let e := edge r k
    let j := pos r k.val
    let y := next b x e
    (slots y e,slots y j) = Decoded.pair (slots x e) (slots x j)
      (decide (k.val+1=n)) (decide (k.val=0)) (before hp x e) (ordinaryMarks hp x e) := by
  have H := (joined_step hn b hp bind x (edge r k)).1
  dsimp only at H ⊢
  simp only [responder,ref_value h,ref_value (fixed_step h _),root_dest,root_source] at H
  simpa only [Decoded.pair,before,responder] using H

theorem frame (b : LargeRows a) (x : Ring a n) (r k i : Fin n)
    (hl : i≠edge r k) (hr : i≠pos r k.val) :
    slots (next b x (edge r k)) i=slots x i := by
  simp only [slots,next,AllSizeS1Geometry.step,if_neg hl,responder,if_neg hr]

structure Effects (r : Fin n) (x y : Ring a n) (k : Fin n) (seen : Bool) : Prop where
  link : ((line r y).slot k.val,(line r y).slot (k.val+1)) =
    hop ((line r x).slot k.val) ((line r x).slot (k.val+1))
  incoming : k.val=0 →
    slot (slots y r).b=ObserverDirty.terminal seen (slot (slots x r).b) ∧
    (line r y).pc=commit (line r x).pc
  outgoing : k.val+1=n →
    (slot (slots y r).a,(line r y).pc)=door (line r x).pc (slot (slots x r).a)

theorem effects (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    {r : Fin n} {x : Ring a n} (h : Fixed b x r) (k : Fin n) :
    Effects r x (next b x (edge r k)) k (turn hp r x k) := by
  let e := edge r k
  let j := pos r k.val
  let y := next b x e
  let u := slots x e
  let v := slots x j
  let m := before hp x e
  let z := ordinaryMarks hp x e
  have hu := Decoded.decode_bounded (BStarLapTransfer.get (x e).guard)
  have hv := Decoded.decode_bounded (BStarLapTransfer.get (x j).guard)
  have H := pair_at hn b hp bind h k
  have K := k.isLt
  by_cases last : k.val+1=n
  · have nf : k.val≠0 := by omega
    have E : e=r := (root_dest r k).2 last
    have pair := Decoded.edgeOutgoing u v m z hu hv
    have bLast : decide (k.val+1=n) = true := by simp [last]
    have bFirst : decide (k.val=0) = false := by simp [nf]
    have S : (slots y e,slots y j)=Decoded.pair u v true false m z := by
      simpa only [bLast,bFirst] using H
    have L : slots y e = (Decoded.pair u v true false m z).1 := congrArg Prod.fst S
    have R : slots y j = (Decoded.pair u v true false m z).2 := congrArg Prod.snd S
    refine ⟨?_,fun f => (nf f).elim, fun _ => ?_⟩
    · simp only [old_source,old_dest,if_pos last]
      change (slot (slots y j).a,slot (slots y e).b)=_
      rw [L,R]; exact pair.1
    · change (slot (slots y r).a, control (slots y r).pc)=door (control (slots x r).pc) (slot (slots x r).a)
      rw [← E,L]; exact pair.2
  · by_cases fst : k.val=0
    · have J : j=r := (root_source r k).2 fst
      have pair := Decoded.edgeIncoming u v m z hu hv
      have bLast : decide (k.val+1=n) = false := by simp [last]
      have bFirst : decide (k.val=0) = true := by simp [fst]
      have S : (slots y e,slots y j)=Decoded.pair u v false true m z := by
        simpa only [bLast,bFirst] using H
      have L : slots y e = (Decoded.pair u v false true m z).1 := congrArg Prod.fst S
      have R : slots y j = (Decoded.pair u v false true m z).2 := congrArg Prod.snd S
      refine ⟨?_,fun _ => ?_, fun f => (last f).elim⟩
      · simp only [old_source,old_dest,if_neg last]
        change (slot (slots y j).a,slot (slots y e).a)=_
        rw [L,R]; exact pair.1
      · change slot (slots y r).b=ObserverDirty.terminal (terminalSeen v m z) (slot (slots x r).b) ∧
          control (slots y r).pc=commit (control (slots x r).pc)
        rw [← J,R]; exact pair.2
    · have pair := Decoded.edgeInterior u v m z hu hv
      have bLast : decide (k.val+1=n) = false := by simp [last]
      have bFirst : decide (k.val=0) = false := by simp [fst]
      have S : (slots y e,slots y j)=Decoded.pair u v false false m z := by
        simpa only [bLast,bFirst] using H
      have L : slots y e = (Decoded.pair u v false false m z).1 := congrArg Prod.fst S
      have R : slots y j = (Decoded.pair u v false false m z).2 := congrArg Prod.snd S
      refine ⟨?_,fun f => (fst f).elim, fun f => (last f).elim⟩
      simp only [old_source,old_dest,if_neg last]
      change (slot (slots y j).a,slot (slots y e).a)=_
      rw [L,R]; exact pair

theorem position_frame (r k : Fin n) {i : Nat} (hi : i<n)
    (hleft : i≠k.val) (hright : i≠k.val+1)
    (hdoor : ¬(k.val+1=n ∧ i=0)) :
    pos r i≠edge r k ∧ pos r i≠pos r k.val := by
  have K := k.isLt
  constructor
  · intro eq
    by_cases last : k.val+1=n
    · have H := eq.trans ((root_dest r k).2 last)
      exact hdoor ⟨last,pos_inj r hi (Nat.zero_lt_of_lt k.isLt) (H.trans (first r).symm)⟩
    · exact hright (pos_inj r hi (by omega : k.val+1<n) eq)
  · intro eq; exact hleft (pos_inj r hi k.isLt eq)

theorem idle_root_frame (b : LargeRows a) (r k : Fin n) (x : Ring a n)
    (hfirst : k.val≠0) (hlast : k.val+1≠n) :
    slots (next b x (edge r k)) r=slots x r := by
  apply frame
  · intro h; exact hlast ((root_dest r k).1 h.symm)
  · intro h; exact hfirst ((root_source r k).1 h.symm)

/-- A launch is precisely an outgoing root interaction whose old decoded
control is ISSUE. The decoded bound includes the spare control byte. -/
theorem launch_iff (r k : Fin n) (x : Ring a n) :
    Launches (line r x) k ↔ edge r k = r ∧ (slots x r).pc = 0 := by
  have hb : (slots x r).pc ≤ 2 :=
    (Decoded.decode_bounded (BStarLapTransfer.get (x r).guard)).2.2
  have hc : (slots x r).pc = 0 ∨ (slots x r).pc = 1 ∨ (slots x r).pc = 2 := by
    omega
  change (k.val + 1 = n ∧ control (slots x r).pc = .issue) ↔ _
  rw [root_dest]
  rcases hc with h | h | h <;> simp [h, Decoded.control]

private theorem line_eq (x y : Line) (hs : x.slot = y.slot) (hc : x.pc = y.pc) : x = y := by
  cases x
  cases y
  simp_all

/-- Every physical edge at a permanent reference has the exact decoded
line update, including services of the two distinct root slots. -/
theorem update (hn : 4≤n) (b : LargeRows a) (hp : 0<a.p)
    (bind : b.shared.ordinaryPublic=BStarPublic.publicWork (c₁:=a.c1) hp)
    {r : Fin n} {x : Ring a n} (h : Fixed b x r) (k : Fin n) :
    line r (next b x (edge r k)) = ObserverDirty.move (line r x) k (turn hp r x k) := by
  let y := next b x (edge r k)
  let old := line r x
  let seen := turn hp r x k
  have E := effects hn b hp bind h k
  have K := k.isLt
  have hsmall : 2≤n := by omega
  change line r y = ObserverDirty.move old k seen
  apply line_eq
  · funext i
    by_cases l : i=k.val
    · subst i; rw [move_left]; exact congrArg Prod.fst E.link
    by_cases d : i=k.val+1
    · subst i; rw [move_right]; exact congrArg Prod.snd E.link
    by_cases t : k.val=0 ∧ i=n
    · obtain ⟨f, rfl⟩ := t
      rw [move_terminal hsmall _ _ _ f]
      simpa [line,token,old,y] using (E.incoming f).1
    by_cases aDoor : k.val+1=n ∧ i=0
    · obtain ⟨last,rfl⟩ := aDoor
      rw [move_door hsmall _ _ _ last]
      simpa [old,line,token,first,show 0<n by omega] using congrArg Prod.fst (E.outgoing last)
    rw [move_frame _ _ _ _ l d t aDoor]
    by_cases hi : i<n
    · have P := position_frame r k hi l d aDoor
      have F := frame b x r k _ P.1 P.2
      simp only [line,token,if_pos hi,old,y,F]
    · by_cases eq : i=n
      · subst i
        have N := idle_root_frame b r k x (fun f => t ⟨f,rfl⟩) (fun last => d last.symm)
        simp only [line,token,if_neg (Nat.lt_irrefl n),old,y,N]
      · simp only [line,token,if_neg hi,if_neg eq,old]
  · change (line r y).pc = if k.val+1=n then (door old.pc (old.slot 0)).2
      else if k.val=0 then commit old.pc else old.pc
    by_cases last : k.val+1=n
    · rw [if_pos last]
      simpa [old,line,token,first,show 0<n by omega] using congrArg Prod.snd (E.outgoing last)
    rw [if_neg last]
    by_cases f : k.val=0
    · rw [if_pos f]; exact (E.incoming f).2
    · rw [if_neg f]
      exact congrArg (fun z : BStarLapTransfer.Site => control z.pc) (idle_root_frame b r k x f last)

end
end L4.Height.ObserverLine
