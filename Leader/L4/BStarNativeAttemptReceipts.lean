import Leader.L4.BStarNativeReceiptTape
import Leader.L4.BStarPostCutAttempt

namespace L4.BStarNativeAttemptReceipts
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongLayout BStarLongDoor
open BStarLongCommand BStarH6WordChart BStarGeneratedOwner BStarGeneratedPCAncestry
open BStarAcquireVisitOrder BStarGeneratedTapeCuts BStarOwnerLaunchOrigin BStarLiteralPC
open BStarNativeReceiptTape BStarPostCutAttempt
open BStarAcquireLiteralChain BStarAcquireAnchors BStarLongFixedRouting BStarResetChartTouch

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step
local notation "pc" => BStarGeneratedBandScan.pc

private theorem foreign_pc (x : X) (i e : Fin n)
    (h : oldH6 B x i=true) (away : e≠RearTrace.predecessor i) :
    pc (step x e) i=pc x i := by
  have R : rightNeighbor e≠i := fun E =>
    away ((RearTrace.predecessor_right e).symm.trans (congrArg RearTrace.predecessor E))
  by_cases E : i=e
  · subst i
    let pair := (x e,x (rightNeighbor e))
    have h' : (oldHeaders B pair.1).h6=true := h
    have t := BStarResetWaitRing.joined_left k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair h'
    unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_true]
    exact congrArg (fun y : BitVec 2 × BitVec 9 => y.2.toNat) t
  · unfold BStarGeneratedBandScan.pc
    simp only [AllSizeS1Geometry.step,if_neg E,if_neg (Ne.symm R)]

private theorem reject_pc {x : X} {addr : Nat → Pos n} {e : Fin n}
    (h : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e) (I : BStarClearanceSource.Issue (x (addr 0).1).long)
    (E : e=RearTrace.predecessor (addr 0).1)
    (bad : initial (pc x (addr 0).1) (x (addr 0).1).long=none) :
    pc (step x e) (addr 0).1=0 := by
  have R : rightNeighbor e=(addr 0).1 := E ▸ RearTrace.right_predecessor _
  let pair := (x e,x (rightNeighbor e))
  have hdr : (oldHeaders B pair.2).h6=true := by change oldH6 B x (rightNeighbor e)=true; rwa [R]
  have valid : LongDoorGuard.valid manifest pair.2.long=true := by
    change LongDoorGuard.valid manifest (x (rightNeighbor e)).long=true
    rw [R]; exact I.1
  have phase : (ctrlPhase.read pair.2.long).toNat=1 := by
    change (ctrlPhase.read (x (rightNeighbor e)).long).toNat=1
    rw [R]; exact I.2
  have A := BStarResetControllerEntry.exact_issue_any_token k₁ k₂ t₂ J₁ J₂ r c p c₁ hp pair hdr valid phase
  have bad' : initial (ctrlOp.read pair.2.long).toNat pair.2.long=none := by
    change initial (pc x (rightNeighbor e)) (x (rightNeighbor e)).long=none
    rwa [R]
  rw [bad'] at A
  have eq : step x e (addr 0).1=(largePair B pair).2 := by
    rw [←R]; simp only [AllSizeS1Geometry.step,if_neg (Ne.symm sep),if_true,pair]
  exact congrArg (fun t : _ × BitVec 9 => t.2.toNat) (eq ▸ A)

/-- The one-step accepted native phase either holds PC (including
actual launch) or takes the exact authentic next consume. -/
private theorem step7 {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {a b : Mode}
    (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true) (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a) (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (new : pc (step x e) (addr 0).1≤408)
    (lo : 7≤pc (step x e) (addr 0).1) :
    pc (step x e) (addr 0).1=pc x (addr 0).1 ∨
      ∃ op, a=.busy op (.back 0) ∧ b=.idle ∧ Hit hp base addr len x e op := by
  cases E with
  | idle_hold away => exact .inl (foreign_pc hp x _ e H away)
  | arrived_hold op away => exact .inl (foreign_pc hp x _ e H away)
  | launch own L =>
    exact .inl (congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2)
  | transit op z d live S => exact .inl (J.1.2.2.2.trans I.1.2.2.2.symm)
  | bad_issue own bad =>
    have Z := reject_pc hp H sep I.1 own bad
    omega
  | consume op own clear =>
    have evt : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op own clear
    obtain ⟨eq,f,R,F,O⟩ := consume_to_band hp K H sep I evt lo new
    exact .inr ⟨op,rfl,rfl,I,evt,I.1.2.2.2,eq,own,f,R,F,O⟩

/-- Actual fixed-attempt word: literal H6 and 6..408 at every cut. -/
def MidBand (x : X) (root : Fin n) (w : List (Fin n)) : Prop :=
  ∀ u v,w=u++v → oldH6 B (run x u) root=true ∧
    6≤pc (run x u) root ∧ pc (run x u) root≤408

private theorem step6 {base x : X} {addr : Nat → Pos n} {len : Nat} {e : Fin n}
    {a b : Mode} (K : (addr 0).2=0) (H : oldH6 B x (addr 0).1=true)
    (sep : e≠rightNeighbor e)
    (I : Current hp base addr len x a) (J : Current hp base addr len (step x e) b)
    (E : Event hp addr len x e a b)
    (old : 6≤pc x (addr 0).1) (L : 6≤pc (step x e) (addr 0).1)
    (U : pc (step x e) (addr 0).1≤408) :
    pc (step x e) (addr 0).1=pc x (addr 0).1 ∨
      ∃ op, a=.busy op (.back 0) ∧ b=.idle ∧ Hit hp base addr len x e op := by
  by_cases Q : pc (step x e) (addr 0).1=6
  · cases E with
    | idle_hold away => exact .inl (foreign_pc hp x _ e H away)
    | arrived_hold op away => exact .inl (foreign_pc hp x _ e H away)
    | launch own L =>
      exact .inl (congrArg (fun t : _ × BitVec 9 => t.2.toNat) L.2.choose_spec.2)
    | transit op z d live S => exact .inl (J.1.2.2.2.trans I.1.2.2.2.symm)
    | bad_issue own bad =>
      have Z := reject_pc hp H sep I.1 own bad
      omega
    | consume op own clear =>
      have P : pc x (addr 0).1=op := I.1.2.2.2
      have V := (consume_to_six hp K H sep I (.consume op own clear) Q).1
      omega
  · exact step7 hp K H sep I J E U (by omega)

private theorem sub_band {x : X} {i : Fin n} {w u v : List (Fin n)}
    (M : MidBand hp x i w) (E : w=u++v) :
    MidBand hp x i u ∧ MidBand hp (run x u) i v := by
  constructor
  · intro a b W
    exact M a (b++v) (by rw [E,W,List.append_assoc])
  · intro a b W
    have H := M (u++a) b (by rw [E,W,List.append_assoc])
    rwa [BStarResetSchedule.run_append] at H

/-- Extract a genuine threshold consume and both generated subwords
from the original tape, even when the full tape ends busy. -/
theorem threshold {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : MidBand hp x (addr 0).1 w) (k : Nat)
    (low : pc x (addr 0).1<k+1)
    (high : k+1≤pc (run x w) (addr 0).1) :
    ∃ pre e post, w=pre++e::post ∧
      GeneratedOwner hp base addr len x a pre (.busy k (.back 0)) ∧
      Hit hp base addr len (run x pre) e k ∧
      GeneratedOwner hp base addr len (step (run x pre) e) .idle post b := by
  induction T with
  | endpoint I =>
    simp only [BStarResetSchedule.run] at high
    omega
  | @next x a e w b dest I E T ih =>
    have sub : MidBand hp (step x e) (addr 0).1 w := (sub_band hp band (show e::w=[e]++w by rfl)).2
    have H := band [] (e::w) rfl
    have V := sub [] w rfl
    have old : 6≤pc x (addr 0).1 := H.2.1
    have lo : 6≤pc (step x e) (addr 0).1 := V.2.1
    have hi : pc (step x e) (addr 0).1≤408 := V.2.2
    by_cases C : pc (step x e) (addr 0).1<k+1
    · obtain ⟨pre,m,post,W,F,G,Z⟩ := ih sub C high
      exact ⟨e::pre,m,post,congrArg (List.cons e) W,.next I E F,G,Z⟩
    rcases step6 hp K H.1 (sep e) I (at_start hp T) E old lo hi with st|⟨op,R,J,hit⟩
    · have S : pc (step x e) (addr 0).1=pc x (addr 0).1 := st
      omega
    · have p : pc x (addr 0).1=op := hit.2.2.1
      have q : pc (step x e) (addr 0).1=op+1 := hit.2.2.2.1
      have eq : op=k := by omega
      subst k
      subst a
      subst b
      exact ⟨[],e,w,rfl,.endpoint I,hit,T⟩

theorem mid_monotone {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (band : MidBand hp x (addr 0).1 w) :
    pc x (addr 0).1≤pc (run x w) (addr 0).1 := by
  induction T with
  | endpoint _ => exact Nat.le_refl _
  | @next x a e w b dest I E T ih =>
    have sub := (sub_band hp band (show e::w=[e]++w by rfl)).2
    have H := band [] (e::w) rfl
    have J := sub [] w rfl
    refine Nat.le_trans ?_ (ih sub)
    rcases step6 hp K H.1 (sep e) I (at_start hp T) E H.2.1 J.2.1 J.2.2 with
      same | ⟨op,_,_,hit⟩
    · exact Nat.le_of_eq same.symm
    · have P : pc x (addr 0).1=op := hit.2.2.1
      have Q : pc (step x e) (addr 0).1=op+1 := hit.2.2.2.1
      omega

/-- On the actual generated suffix from a successful ACK12, the
compiler band is forced at each cut by one-step monotonicity. -/
theorem compiler_band_of_mid {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b : Mode} {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x a w b)
    (M : MidBand hp x (addr 0).1 w) (lo : 13≤pc x (addr 0).1) :
    CompilerBand hp x (addr 0).1 w := by
  intro u v W
  obtain ⟨_,A,_⟩ := BStarGeneratedTapeCuts.split hp u v (W ▸ T)
  have P := mid_monotone hp K sep A (sub_band hp M W).1
  exact ⟨(M u v W).1,Nat.le_trans lo P,(M u v W).2.2⟩

private theorem append_step {base x : X} {addr : Nat → Pos n} {len : Nat}
    {a b d : Mode} {w : List (Fin n)} {e : Fin n}
    (T : GeneratedOwner hp base addr len x a w b)
    (I : Current hp base addr len (run x w) b)
    (E : Event hp addr len (run x w) e b d)
    (J : Current hp base addr len (step (run x w) e) d) :
    GeneratedOwner hp base addr len x a (w++[e]) d := by
  induction T with
  | endpoint _ => exact .next I E (.endpoint J)
  | next C G _ ih => exact .next C G (ih I E J)

theorem from_attempt_prefix {base x : X} {addr : Nat → Pos n} {len : Nat}
    {w : List (Fin n)} (K : (addr 0).2=0)
    (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (T : GeneratedOwner hp base addr len x .idle w .idle)
    (head : ∀ u v,w=u++v → oldH6 B (run x u) (addr 0).1=true)
    (A : AttemptPrefix hp base x addr len w) :
    ∃ (beforeAck compiler afterCompiler : List (Fin n)) (ack : Fin n),
      w=beforeAck++ack::(compiler++afterCompiler) ∧
      let state := run x beforeAck
      let start := step state ack
      Hit hp base addr len state ack 12 ∧
      GeneratedOwner hp base addr len start .idle compiler .idle ∧
      pc (run start compiler) (addr 0).1=408 ∧
      NativeTape hp base addr len start 13 compiler 395 ∧
      ∃ pre407 finalMark, compiler=pre407++[finalMark] ∧
        Hit hp base addr len (run start pre407) finalMark 407 := by
  obtain ⟨lead,mid,_,hold,accept,sel,_,W,_,_,pc6,first,finish,M,pc408,live,_⟩ := A
  let start6 := step (run x lead) accept
  change pc start6 (addr 0).1=6 at pc6
  change pc (run start6 first) (addr 0).1=408 at pc408
  let rest := finish++sel::hold
  have splitWord : w=(lead++[accept])++(first++rest) := by
    rw [W,M]
    simp only [rest,List.append_assoc]
    rfl
  obtain ⟨_,_,G⟩ := BStarGeneratedTapeCuts.split hp (lead++[accept]) (first++rest) (splitWord ▸ T)
  have cut6 : run x (lead++[accept])=start6 := by rw [BStarResetSchedule.run_append]; rfl
  rw [cut6] at G
  obtain ⟨_,firstG,_⟩ := BStarGeneratedTapeCuts.split hp first rest G
  have mb : MidBand hp start6 (addr 0).1 first := by
    intro u v H
    cases v with
    | nil =>
      have U : first=u := by simpa using H
      subst u
      have E : w=((lead++[accept])++first)++rest := by simpa only [List.append_assoc] using splitWord
      have HH := head _ _ E
      rw [BStarResetSchedule.run_append,cut6] at HH
      exact ⟨HH,by omega,by omega⟩
    | cons e tail =>
      exact (live u e tail H).2.1 |> fun hh => ⟨hh,(live u e tail H).1⟩
  obtain ⟨toAck,ack,remaining,W13,_,hit12,G13⟩ :=
    threshold hp K sep firstG mb 12 (by omega) (by omega)
  let pre := lead++accept::toAck
  let start := step (run start6 toAck) ack
  have begin : run x pre=run start6 toAck := by rw [BStarResetSchedule.run_append]; rfl
  have pc13 : pc start (addr 0).1=13 := hit12.2.2.2.1
  have B13 : MidBand hp (run start6 toAck) (addr 0).1 (ack::remaining) :=
    (sub_band hp mb W13).2
  have remainingBand : MidBand hp start (addr 0).1 remaining :=
    (sub_band hp B13 (show ack::remaining=[ack]++remaining by rfl)).2
  have last : pc (run start remaining) (addr 0).1=408 := by
    change pc (run start6 first) (addr 0).1=408 at pc408
    rw [W13,BStarResetSchedule.run_append] at pc408
    exact pc408
  have G13' : GeneratedOwner hp base addr len start .idle remaining _ := G13
  obtain ⟨before407,last407,after408,W408,preG,hit407,tail407⟩ :=
    threshold hp K sep G13' remainingBand 407 (by omega) (by omega)
  let compiler := before407++[last407]
  have CG : GeneratedOwner hp base addr len start .idle compiler .idle := by
    exact append_step hp preG hit407.1 hit407.2.1 (at_start hp tail407)
  have C408 : pc (run start compiler) (addr 0).1=408 := by
    rw [show run start compiler=step (run start before407) last407 by
      simp only [compiler,BStarResetSchedule.run_append]; rfl]
    exact hit407.2.2.2.1
  have cband := (sub_band hp remainingBand (show remaining=compiler++after408 by simpa [compiler] using W408)).1
  have H := native_395 hp K sep CG (compiler_band_of_mid hp K sep CG cband (by omega)) pc13 C408
  refine ⟨pre,compiler,after408++rest,ack,?_,begin ▸ hit12,begin ▸ CG,begin ▸ C408,begin ▸ H,before407,last407,rfl,begin ▸ hit407⟩
  rw [splitWord,W13,W408]
  simp only [pre,compiler,List.append_assoc,List.cons_append,List.nil_append]

/-- Chart-facing entry: use only the caller's already available closed
physical fiber for H6; no additional live compiler assumption. -/
theorem from_chart_attempt {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (Q : X → Prop) (I : Q x)
    (fiber : ∀ y,Q y → ∀ i,Layout B base i=Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e)) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle w .idle)
    (A : AttemptPrefix hp base x (fun j => S.getD j fall) len w) :
    let addr := fun j => S.getD j fall
    ∃ (beforeAck compiler afterCompiler : List (Fin n)) (ack : Fin n),
      w=beforeAck++ack::(compiler++afterCompiler) ∧
      let state := run x beforeAck
      let start := step state ack
      Hit hp base addr len state ack 12 ∧
      GeneratedOwner hp base addr len start .idle compiler .idle ∧
      pc (run start compiler) (addr 0).1=408 ∧
      NativeTape hp base addr len start 13 compiler 395 ∧
      ∃ pre407 finalMark, compiler=pre407++[finalMark] ∧
        Hit hp base addr len (run start pre407) finalMark 407 := by
  exact from_attempt_prefix hp (root_cuts hp C Q I closed fiber []).2 sep T
    (fun u _ _ => (root_cuts hp C Q I closed fiber u).1) A

end L4.BStarNativeAttemptReceipts
