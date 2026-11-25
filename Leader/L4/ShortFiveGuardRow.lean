import Leader.L4.ShortFiveWriteTour
import Leader.L4.ShortClassifiedOwnerAuth
import Leader.L4.ShortCommitMachine
import Leader.L4.ShortSheetProjection
import Leader.L4.ShortBankProjection

namespace L4.ShortFiveGuardRow
open AllSizeProtocol MISByteCodec ShortResetFlow
open ShortResetRow (selectorGuard)
set_option maxRecDepth 12000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/- Exact decomposition of ShortResetRow:9–155. These are private
   proof helpers, not a new transition relation. localRow_eq is rfl. -/

private def selector (x : BitVec 96) : Nat := get x 92 1 (by decide)
private def grant (x : BitVec 96) (j : Fin 3) : Bool := x.getLsbD (91-j.val)
private def bitAt (x j : Nat) : Bool := (x >>> j)%2==1
private def bank (x : BitVec 96) (j : Nat) : Bool := x.getLsbD (88-j)

private def putBank (j : Nat) (b : Bool) : Patch 96 :=
  put (88-j) 1 (by omega) b.toNat

private def putSeal (d : Option Nat) : Patch 96 :=
  put 83 4 (by decide) (match d with | none=>0 | some q=>8+q)

private def grantsPatch (g : Fin 3 → Bool) : Patch 96 :=
  put 89 3 (by decide) (4*(g 0).toNat+2*(g 1).toNat+(g 2).toNat)

private def canonical (x : BitVec 96) (j : Fin 3) : Bool :=
  if grant x 1 then j==1 else grant x j

open L4.MISByteRows (Link)

private def links (header : Bool) : List Link :=
  if header then [⟨0,some 1⟩,⟨1,some 2⟩,⟨2,none⟩] else
    [⟨0,some 0⟩,⟨1,some 1⟩,⟨2,some 2⟩]

private def parked (t : Token) (h : Bool) (x : BitVec 96) (j : Fin 3) : Bool :=
    t.tag==2 && !t.fault && t.opcode==2 && atGate h x j

private def ready (h : Bool) (x : BitVec 96) (j : Fin 3) (t : Token) : Bool :=
  t.tag==2 && !(parked t h x j && t.race<4)

private def raceNext (t : Token) (side : Nat) : Token :=
  if t.race==1 then {t with race:=side} else
    if (t.race==2 || t.race==3) && t.race != side then
      {t with race:=t.race+2} else t

private def terminal (t : Token) : Token :=
  if t.fault || (t.opcode==6 && !t.applied) then faultToken 3
  else if t.opcode==3 then
    if bitAt t.payload 6 then { tag:=3, opcode:=3, payload:=t.payload%64 }
    else { tag:=3, opcode:=3, outcome:=1 }
  else { tag:=3, opcode:=t.opcode, payload:=if t.opcode==2 then t.payload else 0 }

private def arrival (h : Bool) (x : BitVec 96) (j : Fin 3) (t : Token) : Token :=
  if !t.fault && t.opcode==2 && atGate h x j then {t with race:=1} else t

private def setPLane (p k : Nat) (b : Bool) : Nat :=
  if bitAt p k then if b then p else p-2^k
  else if b then p+2^k else p

private def effect (u v : BitVec 96) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (win : Bool) (t : Token) :
    Patch 96 × Patch 96 × Token :=
  let none := Patch.empty 96
  if t.fault then (none,none,t)
  else if t.opcode==6 && hv && j==0 && k==some 1 then
    let ix := (t.payload/2)%2
    if !t.applied && grant v 1 && selector v==t.payload/4 &&
        readSeal v==some t.payload && bank v ix==bitAt t.payload 0 then
      (none,(put 92 1 (by decide) ix).compose (putSeal Option.none),{t with applied:=true})
    else (none,none,faultToken 2)
  else if parked t hu u j then (none,none,{t with race:=0,payload:=t.race-4})
  else if hu && j==1 && t.opcode==0 then (putSeal Option.none,none,t)
  else if hu && t.opcode==3 then
    let p := if win then (setPLane (setPLane t.payload (5-j.val) (selector u==1))
        (2-j.val) (bank u (selector u))) else setPLane t.payload 6 false
    (none,none,{t with payload:=p})
  else if hu && j==1 && (t.opcode==4 || t.opcode==5) then
    let ix := (t.payload/2)%2
    if !(grant u 1 && selector u==t.payload/4) ||
        (t.opcode==5 && bank u ix != bitAt t.payload 0) then (none,none,faultToken 2)
    else if t.opcode==4 then (putBank ix (bitAt t.payload 0),none,t)
    else (putSeal (some t.payload),none,t)
  else (none,none,t)

private def linkStep (hu hv : Bool) (u v : BitVec 96) (win : Fin 3 → Bool)
    (ab : Pair (Patch 96)) (l : Link) : Pair (Patch 96) :=
  let (a,b) := ab
  let fu := oldK hu u
  let fv := oldK hv v
  let j := l.src
  let t := fu j
  if ready hu u j t then
    let (d,e,t') := effect u v hu hv j l.dst (win j) t
    match l.dst with
    | none => ((a.compose d).compose (putK j (terminal t')),b.compose e)
    | some k => ((a.compose d).compose (putK j T),
      (b.compose e).compose (putK k (arrival hv v k t')))
  else
    if t.tag==2 then (a,b)
    else match l.dst with
    | none => (if t.tag==1 then a.compose (putK j E) else a,b)
    | some k =>
      let reply := fv k
      if reply.tag==3 then (a.compose (putK j reply),b.compose (putK k E))
      else if t.tag==1 && reply.tag==0 then (a.compose (putK j E),b)
      else (a,b)

private def rowPrefix (headers : Pair Bool) (old : Pair (BitVec 96)) :
    (Fin 3 → Bool) × Pair (Patch 96) :=
  let hu:=headers.1
  let hv:=headers.2
  let u:=old.1
  let v:=old.2
  let fu := oldK hu u
  let fv := oldK hv v
  let action := fun (j : Fin 3) (op : Nat) =>
    let t := fu j
    hu && ready hu u j t && !t.fault && t.opcode==op
  let rel := fun j => action j 0
  let ask := fun j => action j 3
  let w := !canonical u 0 && !canonical u 1 && !canonical u 2 && ask 1 && !rel 1
  let win := fun j : Fin 3 =>
    if j==1 then w
    else !w && !canonical u 1 && ask j && !canonical u j && !rel j
  let gg := fun j => (canonical u j && !rel j) || win j
  let clear := (resetSource.compose (putSeal none)).compose (grantsPatch fun _ => false)
  let a := if hu then grantsPatch gg else clear
  let b := if hv then
    if grant v 1 && (grant v 0 || grant v 2) then grantsPatch (canonical v) else .empty _
    else clear
  let ru := fun (j : Fin 3) =>
    let t := fu j
    if t.fault then putK j t
    else if parked t hu u j && (t.race==1 || t.race==2) then putK j (raceNext t 3)
    else .empty _
  let rv := fun (j : Fin 3) =>
    let t := fv j
    if t.fault then putK j t
    else if parked t hv v j && (t.race==1 || t.race==3) then putK j (raceNext t 2)
    else .empty _
  let a := ((a.compose (ru 0)).compose (ru 1)).compose (ru 2)
  let b := ((b.compose (rv 0)).compose (rv 1)).compose (rv 2)
  (win,(a,b))

private def rowPost (hv : Bool) (v : BitVec 96) (routed : Pair (Patch 96)) : Pair (Patch 96) :=
  if hv then
    let (p,t) := source v (oldK hv v 0)
    (routed.1,(routed.2.compose p).compose (match t with | none=>.empty _ | some t=>putK 0 t))
  else routed

def localRow (headers : Pair Bool) (old : Pair (BitVec 96)) : Pair (Patch 96) :=
  let (win,p) := rowPrefix headers old
  rowPost headers.2 old.2 ((links headers.2).foldl (linkStep headers.1 headers.2 old.1 old.2 win) p)

theorem localRow_eq (h : Pair Bool) (x : Pair (BitVec 96)) :
    localRow h x=MISByteRows.row h x := rfl

private theorem rowPost_left (hv : Bool) (v : BitVec 96) (q : Pair (Patch 96)) :
    (rowPost hv v q).1=q.1 := by
  cases hv <;> rfl

private def ControllerFrame {w : Nat} (f : Field 96 w) (p : Patch 96) : Prop :=
  ∀ x, f.read (p.apply x) = f.read x

private theorem ctl_empty {w : Nat} (f : Field 96 w) : ControllerFrame f (.empty _) := by
  intro x
  congr 1
  change x &&& BitVec.allOnes 96 ||| 0 = x
  rw [BitVec.and_allOnes]
  exact BitVec.or_zero

private theorem ctl_compose {w : Nat} {f : Field 96 w} {p q : Patch 96}
    (P : ControllerFrame f p) (Q : ControllerFrame f q) : ControllerFrame f (p.compose q) := by
  intro x
  rw [Patch.compose_apply,Q,P]

private theorem ctl_put {w : Nat} {f : Field 96 w} (o l : Nat) (fits : o+l≤96) (v : Nat)
    (B : f.offset+w≤o ∨ o+l≤f.offset) : ControllerFrame f (put o l fits v) := by
  intro x
  exact Field.read_other_assign f (lane o l fits) _ _ B

private theorem ctl_k {w : Nat} {f : Field 96 w} (low : 57≤f.offset) (j : Fin 3)
    (t : Token) : ControllerFrame f (putK j t) := by
  intro x
  apply Field.read_other_assign f (kField j) _ _ (.inr ?_)
  change 19*(2-j.val)+19≤f.offset
  omega

private theorem ctl_norm {w : Nat} (f : Field 96 w) (low : 57≤f.offset)
    (j : Fin 3) (t q : Token) (b : Bool) :
    ControllerFrame f (if t.fault then putK j t else if b then putK j q else Patch.empty 96) := by
  split
  · exact ctl_k low j t
  · cases b
    · exact ctl_empty f
    · exact ctl_k low j q

private theorem effect_left_noncenter {n : Nat} (f : Field 96 n)
    (u v : BitVec 96) (hv : Bool) (l : Link) (w : Bool) (t : Token) (hn : l.src ≠ 1) :
    ControllerFrame f (effect u v true hv l.src l.dst w t).1 := by
  unfold effect
  dsimp only
  have z : (l.src==1)=false := Bool.eq_false_iff.mpr (fun H => hn (beq_iff_eq.mp H))
  simp only [z,Bool.and_false,Bool.false_and,Bool.false_eq_true,if_false]
  split
  · apply ctl_empty
  split
  · split <;> apply ctl_empty
  split
  · apply ctl_empty
  split <;> apply ctl_empty

private theorem stage_seal_prefix_frame {n : Nat} (f : Field 96 n)
    (lo : 57 ≤ f.offset) (hi : f.offset + n ≤ 89) (hv : Bool) (u v : BitVec 96) :
    ControllerFrame f (rowPrefix (true,hv) (u,v)).2.1 := by
  let norm := fun j : Fin 3 =>
    let t := oldK true u j
    if t.fault then putK j t
    else if parked t true u j && (t.race==1 || t.race==2) then putK j (raceNext t 3)
    else .empty _
  have N (j : Fin 3) : ControllerFrame f (norm j) := by
    unfold norm
    dsimp only
    split
    · exact ctl_k lo _ _
    split
    · exact ctl_k lo _ _
    · exact ctl_empty _
  unfold rowPrefix
  dsimp only [Prod.fst, Prod.snd, if_true]
  exact ctl_compose (ctl_compose (ctl_compose
    (ctl_put 89 3 (by decide) _ (.inl hi)) (N 0)) (N 1)) (N 2)

private theorem link_left_read_of_effect {n : Nat} (f : Field 96 n) (low : 57≤f.offset)
    (hv : Bool) (u v : BitVec 96) (w : Fin 3→Bool) (p : Pair (Patch 96)) (l : Link)
    (F : ready true u l.src (oldK true u l.src)=true →
      ControllerFrame f (effect u v true hv l.src l.dst (w l.src) (oldK true u l.src)).1) :
    f.read ((linkStep true hv u v w p l).1.apply u)=f.read (p.1.apply u) := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      f.read ((putK j t).apply x)=f.read x := ctl_k low j t x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · rename_i R
    have H (x : BitVec 96) := F R x
    split <;> simp only [Patch.compose_apply,K,H]
  · split
    · rfl
    · split
      · split <;> first | rfl | simp only [Patch.compose_apply,K]
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> first | rfl | simp only [Patch.compose_apply,K]

private def msf : Field 96 4 := lane 83 4 (by decide)

private theorem msf_reset : ControllerFrame msf resetSource :=
  ctl_put 57 26 (by decide) _ (.inr (by decide))
private theorem msf_phase (op : Nat) : ControllerFrame msf (phaseOp 1 op) :=
  ctl_put 78 5 (by decide) _ (.inr (by decide))

private theorem msf_grant (g : Fin 3→Bool) : ControllerFrame msf (grantsPatch g) :=
  ctl_put 89 3 (by decide) _ (.inl (by decide))

private theorem msf_norm {c : Bool} (t q : Token) (j : Fin 3) :
    ControllerFrame msf (if t.fault then putK j t else if c then putK j q else Patch.empty 96) :=
  ctl_norm msf (by decide) j t q c

private theorem msf_source (v : BitVec 96) (t : Token) :
    ControllerFrame msf (source v t).1 := by
  unfold source
  dsimp only
  split
  · exact msf_reset
  split
  · refine ctl_compose ?_ (ctl_put 81 2 (by decide) 2 (.inr (by decide)))
    split
    · exact msf_reset
    · exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · exact msf_reset
  split
  · exact msf_phase _
  · exact msf_phase _
  · split
    · exact msf_phase _
    · exact msf_reset
  · exact ctl_compose
      (ctl_compose (msf_phase _) (ctl_put 72 6 (by decide) _ (.inr (by decide))))
      (ctl_put 68 4 (by decide) _ (.inr (by decide)))
  · exact msf_phase _
  · exact msf_phase _
  · exact msf_reset

private theorem msf_effect_right (u v : BitVec 96) (hu hv : Bool)
    (j : Fin 3) (k : Option (Fin 3)) (w : Bool) (t : Token)
    (H : t.tag=2 → t.fault=false → t.opcode=6 → hv=true → j=0 →
      k=some 1 → t.applied=false → v.getLsbD 90=true →
      get v 92 1 (by decide)=t.payload/4 → readSeal v=some t.payload →
      v.getLsbD (88-(t.payload/2)%2)=(t.payload%2==1) → False)
    (tag : t.tag=2) :
    ControllerFrame msf (effect u v hu hv j k w t).2.1 := by
  unfold effect
  dsimp only
  split
  · exact ctl_empty _
  · rename_i F
    have hf : t.fault=false := Bool.eq_false_iff.mpr F
    split
    · rename_i C
      simp only [Bool.and_eq_true, beq_iff_eq] at C
      obtain ⟨⟨⟨o,h⟩,j0⟩,k1⟩ := C
      split
      · rename_i G
        change ((!t.applied && v.getLsbD 90 && get v 92 1 (by decide)==t.payload/4 &&
          readSeal v==some t.payload && (v.getLsbD (88-(t.payload/2)%2)==(t.payload%2==1)))=true) at G
        simp only [Bool.and_eq_true, beq_iff_eq] at G
        obtain ⟨⟨⟨⟨a,b⟩,c⟩,d⟩,e⟩ := G
        have ap : t.applied=false := by cases t.applied <;> simp_all
        exact (H tag hf o h j0 k1 ap b c d e).elim
      · exact ctl_empty _
    · split
      · exact ctl_empty _
      · split
        · exact ctl_empty _
        · split
          · exact ctl_empty _
          · split
            · split
              · exact ctl_empty _
              · split <;> exact ctl_empty _
            · exact ctl_empty _

private theorem msf_ready_tag (u : BitVec 96) (hu : Bool) (j : Fin 3) (t : Token)
    (E : ready hu u j t=true) : t.tag=2 := by
  have Q := (Bool.and_eq_true_iff.mp E).1
  exact beq_iff_eq.mp Q

private theorem msf_link_right (hu hv : Bool) (u v : BitVec 96)
    (w : Fin 3→Bool) (p : Pair (Patch 96)) (l : Link) (G : ¬selectorGuard hu u v) :
    msf.read ((linkStep hu hv u v w p l).2.apply v)=msf.read (p.2.apply v) := by
  have K (j : Fin 3) (t : Token) (x : BitVec 96) :
      msf.read ((putK j t).apply x)=msf.read x := ctl_k (by decide) j t x
  rcases p with ⟨a,b⟩
  unfold linkStep
  dsimp only
  split
  · rename_i R
    have H : ControllerFrame msf (effect u v hu hv l.src l.dst (w l.src) (oldK hu u l.src)).2.1 := by
      apply msf_effect_right
      · intro tag hf op _ j0 _ appl writer sel hs banked
        apply G
        change (oldK hu u 0).tag = 2 ∧ _
        simpa only [j0] using And.intro tag (And.intro hf (And.intro op (And.intro appl (And.intro writer (And.intro sel (And.intro hs banked))))))
      · exact msf_ready_tag _ _ _ _ R
    have E (x : BitVec 96) := H x
    split <;> simp only [Patch.compose_apply,K,E]
  · split
    · rfl
    · split
      · split <;> rfl
      · split
        · simp only [Patch.compose_apply,K]
        · split <;> rfl

private theorem msf_post_right (hu : Bool) (v : BitVec 96) (p : Pair (Patch 96)) :
    msf.read ((rowPost hu v p).2.apply v)=msf.read (p.2.apply v) := by
  have K (t : Token) (x : BitVec 96) :
      msf.read ((putK 0 t).apply x)=msf.read x := ctl_k (by decide) 0 t x
  unfold rowPost
  split
  · dsimp only
    rw [Patch.compose_apply,Patch.compose_apply]
    split
    · rw [ctl_empty msf,msf_source]
    · rw [K,msf_source]
  · rfl

/- The left centre link is the only possible bank/seal writer. Work
   through ready and the immutable OLD token. The effect cases below
   are exactly ShortResetRow:57–80. -/
private theorem centre_effect_frame {m : Nat} (f : Field 96 m)
    (u v : BitVec 96) (hv : Bool) (k : Option (Fin 3)) (w : Bool)
    (t : Token)
    (reset : t.opcode=0 → ControllerFrame f (putSeal none))
    (stage : t.opcode=4 → ControllerFrame f
      (putBank ((t.payload/2)%2) (bitAt t.payload 0)))
    (sealCond : t.opcode=5 → ControllerFrame f (putSeal (some t.payload))) :
    ControllerFrame f (effect u v true hv 1 k w t).1 := by
  unfold effect
  dsimp only
  split
  · exact ctl_empty _
  split
  · split <;> exact ctl_empty _
  split
  · exact ctl_empty _
  split
  · rename_i H
    apply reset
    simpa using H
  split
  · exact ctl_empty _
  split
  · rename_i H
    have O : t.opcode=4 ∨ t.opcode=5 := by
      simpa only [Bool.true_and,beq_self_eq_true,Bool.and_true,
        Bool.or_eq_true,beq_iff_eq] using H
    split
    · exact ctl_empty _
    · split
      · rename_i E
        exact stage (beq_iff_eq.mp E)
      · rename_i E
        exact sealCond (O.resolve_left (fun Q=>E (beq_iff_eq.mpr Q)))
  · exact ctl_empty _

/-- An arbitrary field below grants and above the K lanes. Only the
    actual centre link requires a condition on its old token. -/
private theorem left_pair_frame {m : Nat} (f : Field 96 m)
    (lo : 57≤f.offset) (hi : f.offset+m≤89)
    (hv : Bool) (u v : BitVec 96)
    (H : ∀ (k : Option (Fin 3)) (w : Bool),
      ready true u 1 (oldK true u 1)=true →
      ControllerFrame f (effect u v true hv 1 k w (oldK true u 1)).1) :
    f.read ((MISByteRows.row (true,hv) (u,v)).1.apply u)=f.read u := by
  rw [←localRow_eq]
  unfold localRow
  dsimp only
  rw [rowPost_left]
  have P := stage_seal_prefix_frame f lo hi hv u v u
  generalize (rowPrefix (true,hv) (u,v)).1 = w
  generalize (rowPrefix (true,hv) (u,v)).2 = p at P ⊢
  -- CHECK: same literal three-link fold as ShortResetRow:3794–3806.
  cases hv <;> simp only [links,if_true,if_false,Bool.false_eq_true,List.foldl_cons,List.foldl_nil]
  · rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨2,some 2⟩
      (fun _=>effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨1,some 1⟩ (H _ _)]
    rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨0,some 0⟩
      (fun _=>effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    exact P
  · rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨2,none⟩
      (fun _=>effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨1,some 2⟩ (H _ _)]
    rw [link_left_read_of_effect f lo _ _ _ _ _ ⟨0,some 1⟩
      (fun _=>effect_left_noncenter f _ _ _ _ _ _ (by decide))]
    exact P

/-- A fault or non-F cannot stage a bank, even with a writer grant. -/
def BankSafe (t : Token) : Prop :=
  t.tag≠2 ∨ t.fault=true ∨ t.opcode≠4

/-- Outgoing RESET and SEAL are the only seal writers on the left. -/
def SealSafe (t : Token) : Prop :=
  t.tag≠2 ∨ t.fault=true ∨ (t.opcode≠0 ∧ t.opcode≠5)

theorem banks_left_frame (hv : Bool) (u v : BitVec 96)
    (S : BankSafe (oldK true u 1)) :
    (lane 87 2 (by decide)).read ((MISByteRows.row (true,hv) (u,v)).1.apply u)=
      (lane 87 2 (by decide)).read u := by
  apply left_pair_frame _ (by decide) (by decide)
  intro k w R
  let t := oldK true u 1
  have T : t.tag=2 := msf_ready_tag _ _ _ _ R
  rcases S with no|fault|no
  · exact (no T).elim
  · change (oldK true u 1).fault=true at fault
    simp only [effect,fault,if_true]
    exact ctl_empty _
  · apply centre_effect_frame
    · intro _
      exact ctl_put 83 4 (by decide) _ (.inr (by decide))
    · intro O
      exact (no O).elim
    · intro _
      exact ctl_put 83 4 (by decide) _ (.inr (by decide))

theorem seal_left_frame (hv : Bool) (u v : BitVec 96)
    (S : SealSafe (oldK true u 1)) :
    (lane 83 4 (by decide)).read ((MISByteRows.row (true,hv) (u,v)).1.apply u)=
      (lane 83 4 (by decide)).read u := by
  apply left_pair_frame _ (by decide) (by decide)
  intro k w R
  let t := oldK true u 1
  have T : t.tag=2 := msf_ready_tag _ _ _ _ R
  rcases S with no|fault|no
  · exact (no T).elim
  · simp only [effect,fault,if_true]
    exact ctl_empty _
  · apply centre_effect_frame
    · intro O
      exact (no.1 O).elim
    · intro _
      apply ctl_put
      left
      change 87≤88-(t.payload/2)%2
      omega
    · intro O
      exact (no.2 O).elim

/-- The right selected header has no cold-clear prefix. If the
    actual old COMMIT guard fails, its seal is not consumed. -/
theorem seal_right_frame (hu : Bool) (u v : BitVec 96)
    (G : ¬selectorGuard hu u v) :
    (lane 83 4 (by decide)).read ((MISByteRows.row (hu,true) (u,v)).2.apply v)=
      (lane 83 4 (by decide)).read v := by
  rw [←localRow_eq]
  dsimp only [localRow]
  let pre := rowPrefix (hu,true) (u,v)
  have pref : ControllerFrame msf pre.2.2 := by
    have P (b : Bool) : ControllerFrame msf
        (if b then grantsPatch (canonical v) else Patch.empty 96) := by
      cases b
      · exact ctl_empty _
      · exact msf_grant _
    unfold pre rowPrefix
    dsimp only
    simp only [if_true]
    exact ctl_compose (ctl_compose (ctl_compose (P _)
      (ctl_norm msf (by decide) 0 _ _ _)) (ctl_norm msf (by decide) 1 _ _ _))
      (ctl_norm msf (by decide) 2 _ _ _)
  have H (w : Fin 3→Bool) (p : Pair (Patch 96)) (L : List Link) :
      msf.read ((L.foldl (linkStep hu true u v w) p).2.apply v)=msf.read (p.2.apply v) := by
    induction L generalizing p with
    | nil => rfl
    | cons l t IH => exact (IH _).trans (msf_link_right hu true u v w p l G)
  change msf.read ((rowPost true v ((links true).foldl
    (linkStep hu true u v pre.1) pre.2)).2.apply v)=msf.read v
  rw [msf_post_right]
  exact (H _ _ _).trans (pref v)

end L4.ShortFiveGuardRow
