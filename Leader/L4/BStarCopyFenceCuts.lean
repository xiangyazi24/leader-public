import Leader.L4.BStarPostCutAttempt
import Leader.L4.BStarCopyLeftFenceHold
import Leader.L4.BStarCopyAttemptBand

namespace L4.BStarCopyFenceCuts
set_option maxRecDepth 4096
open AllSizeProtocol BStarTrace BStarLongWork BStarLongToken BStarLongDoor
open BStarH6WordChart BStarAcquireVisitOrder BStarAcquireLiteralChain
open BStarResetChartTouch BStarGeneratedOwner BStarGeneratedPCAncestry
open BStarGeneratedBandScan BStarNativeReceiptTape BStarOwnerLaunchOrigin
open BStarCopyGateAuthority BStarOwnerControlHistory BStarResetChartService
open BStarCopyAttemptBand (band_step_exact)
open BStarSeparatingRail

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem hit_of_rise {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (layout : ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B x i)
    {m m' : Mode} (e : Fin n)
    (I : Current hp base (fun j=>S.getD j fall) len x m)
    (E : Event hp (fun j=>S.getD j fall) len x e m m')
    (J : Current hp base (fun j=>S.getD j fall) len (step x e) m')
    (old : Band x (S.getD 0 fall).1) (new : Band (step x e) (S.getD 0 fall).1)
    (rise : pc x (S.getD 0 fall).1<pc (step x e) (S.getD 0 fall).1) :
    m=.busy (pc x (S.getD 0 fall).1) (.back 0) ∧ m'=.idle ∧
      Hit hp base (fun j=>S.getD j fall) len x e (pc x (S.getD 0 fall).1) := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  change Band x root at old
  change Band (step x e) root at new
  change pc x root<pc (step x e) root at rise
  cases m with
  | idle =>
    rcases idle_launch_or_hold hp chart layout I.2 sep e I.1 with L|N|H
    · have eq := congrArg (fun t : BitVec 2 × BitVec 9 => t.2.toNat) L.2.2.1
      change pc (step x e) root=pc x root at eq
      omega
    · have eq := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) N.2.2.1
      change pc (step x e) root=0 at eq
      omega
    · obtain ⟨_,⟨_,a,_,snap⟩,_,_⟩ := H
      have eq := congrArg (fun q : (Token × BitVec 2) × BitVec 9 => q.2.toNat) snap
      change pc (step x e) root=pc x root at eq
      omega
  | busy op z =>
    cases E with
    | transit _ _ _ _ _ =>
      have eq := J.1.2.2.2.trans I.1.2.2.2.symm
      change pc (step x e) root=pc x root at eq
      omega
    | arrived_hold _ _ =>
      have eq := J.1.2.2.2.trans I.1.2.2.2.symm
      change pc (step x e) root=pc x root at eq
      omega
    | consume _ atDoor clean =>
      obtain ⟨head,ix⟩ := root_header hp chart layout
      have evt : Event hp addr len x e (.busy op (.back 0)) .idle := .consume op atDoor clean
      have lo := old.1
      obtain ⟨next,f,F,Bd,O⟩ := consume_to_band hp (base:=base) (x:=x) (addr:=addr) (len:=len) (op:=op) (e:=e) ix head (sep e) I evt
        (by change 7≤pc (step x e) root; omega) new.2
      have eq : pc x root=op := I.1.2.2.2
      rw [eq]
      exact ⟨rfl,rfl,I,evt,eq,next,atDoor,f,F,Bd,O⟩

def LiveAt {base : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (_ : Chart hp base hh o S len fall) (x : X) (w : List (Fin n)) : Prop :=
  ∀ u v,w=u++v →
    (∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B (play x u) i) ∧
    Band (play x u) (S.getD 0 fall).1

theorem split_live {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) {u v : List (Fin n)}
    (H : LiveAt hp chart x (u++v)) :
    LiveAt hp chart x u ∧ LiveAt hp chart (play x u) v := by
  constructor
  · intro p q E
    exact H p (q++v) (by rw [E,List.append_assoc])
  · intro p q E
    have A := H (u++p) q (by rw [E,List.append_assoc])
    simpa only [BStarResetSchedule.run_append] using A


/-- First actual successful ACK from an in-band generated owner, with
its chronological prefix and suffix and the physical old reply. -/
theorem first_ack {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {a b : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x a w b)
    (band : LiveAt hp chart x w)
    (rise : pc x (S.getD 0 fall).1<pc (play x w) (S.getD 0 fall).1) :
    ∃ pre e post, w=pre++e::post ∧
      Flat hp x (S.getD 0 fall).1 pre ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x a pre
        (.busy (pc x (S.getD 0 fall).1) (.back 0)) ∧
      Hit hp base (fun j=>S.getD j fall) len (play x pre) e (pc x (S.getD 0 fall).1) ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len (step (play x pre) e) .idle post b ∧
      LiveAt hp chart (step (play x pre) e) post := by
  induction T with
  | @endpoint y m I =>
    exact False.elim (Nat.lt_irrefl (pc y (S.getD 0 fall).1) rise)
  | @next x a e w mid b I E T ih =>
    let root := (S.getD 0 fall).1
    let y := step x e
    have sub : LiveAt hp chart y w := fun u v Q=>band (e::u) v (congrArg (List.cons e) Q)
    have old := band [] (e::w) rfl
    have new := sub [] w rfl
    have start := BStarGeneratedTapeCuts.at_start hp T
    rcases band_step_exact hp chart sep old.1 e I E start old.2 new.2 with same|inc
    · change pc y root=pc x root at same
      have r : pc y root<pc (play y w) root := by
        rwa [same]
      obtain ⟨pre,d,post,W,F,U,H,V,L⟩ := ih sub r
      rw [same] at U H
      refine ⟨e::pre,d,post,congrArg (List.cons e) W,?_,.next I E U,H,V,L⟩
      intro u v Q
      cases u with
      | nil => rfl
      | cons f u =>
        have eq := List.cons.inj Q
        cases eq.1
        exact (F u v eq.2).trans same
    · change pc y root=pc x root+1 at inc
      obtain ⟨A,C,H⟩ := hit_of_rise hp chart sep old.1 e I E start old.2 new.2
        (show pc x root<pc y root by omega)
      subst a
      subst mid
      exact ⟨[],e,w,rfl,(by intro p q W; cases p with | nil => rfl | cons f p => contradiction),
        .endpoint I,H,T,sub⟩


/-- Specialize at the start of the actual PC10 suffix. All cuts refer
to the literal original raw word, including the selected old ACK11
and the later accepted PC12 tour. Its own ISSUE12 follows by genuine
launch provenance, not the equality of the controller's PC field. -/
theorem copy_cuts {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {b : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x .idle w b)
    (band : LiveAt hp chart x w)
    (initial10 : pc x (S.getD 0 fall).1=10)
    (end13 : 12<pc (play x w) (S.getD 0 fall).1) :
    let addr := fun j=>S.getD j fall
    ∃ (before10 fence numeric tail : List (Fin n)) (ack10 ack11 ack12 : Fin n),
      w=before10++ack10::(fence++ack11::(numeric++ack12::tail)) ∧
      let to10 := play x before10
      let from10 := step to10 ack10
      let from11 := step (play from10 fence) ack11
      GeneratedOwner hp base addr len x .idle before10 (.busy 10 (.back 0)) ∧
      Hit hp base addr len to10 ack10 10 ∧
      GeneratedOwner hp base addr len from10 .idle fence (.busy 11 (.back 0)) ∧
      Hit hp base addr len (play from10 fence) ack11 11 ∧
      GeneratedOwner hp base addr len from11 .idle numeric (.busy 12 (.back 0)) ∧
      Found hp base addr len 12 from11 numeric (.back 0) ∧
      Hit hp base addr len (play from11 numeric) ack12 12 ∧
      GeneratedOwner hp base addr len (step (play from11 numeric) ack12) .idle tail b := by
  dsimp only
  let root := (S.getD 0 fall).1
  have init : pc x root=10 := initial10
  change 12<pc (play x w) root at end13
  obtain ⟨pre,a,rest,E,_,A,H,R,L⟩ :=
    first_ack hp chart sep T band (show pc x root<pc (play x w) root by rw [init]; omega)
  change pc x root=10 at init
  rw [init] at A H
  let y := step (play x pre) a
  have ypc : pc y root=11 := H.2.2.2.1
  have wR : play x w=play y rest := by rw [E,BStarResetSchedule.run_append]; rfl
  have gt : 12<pc (play y rest) root := wR ▸ end13
  obtain ⟨fence,c,afterF,F,_,K,Khit,D,LF⟩ :=
    first_ack hp chart sep R L (show pc y root<pc (play y rest) root by rw [ypc]; omega)
  change pc y root=11 at ypc
  rw [ypc] at K Khit
  let z := step (play y fence) c
  have zpc : pc z root=12 := Khit.2.2.2.1
  have wF : play y rest=play z afterF := by rw [F,BStarResetSchedule.run_append]; rfl
  have gtF : 12<pc (play z afterF) root := wF ▸ gt
  obtain ⟨nm,d,last,E2,_,N,Nhit,Q,_⟩ :=
    first_ack hp chart sep D LF (show pc z root<pc (play z afterF) root by rw [zpc]; exact gtF)
  change pc z root=12 at zpc
  rw [zpc] at N Nhit
  refine ⟨pre,fence,nm,last,a,c,d,?_,A,H,K,Khit,N,from_idle hp N,Nhit,Q⟩
  rw [E,F,E2]


/-- Find the genuine accepted receipt of a specified intermediate
in-band PC, on the actual word. Every cut keeps its real owner mode. -/
theorem ack_at {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {a b : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x a w b)
    (band : LiveAt hp chart x w) (op : Nat)
    (initial : pc x (S.getD 0 fall).1≤op)
    (endPC : op<pc (play x w) (S.getD 0 fall).1) :
    ∃ pre e post, w=pre++e::post ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len x a pre (.busy op (.back 0)) ∧
      Hit hp base (fun j=>S.getD j fall) len (play x pre) e op ∧
      GeneratedOwner hp base (fun j=>S.getD j fall) len (step (play x pre) e) .idle post b ∧
      LiveAt hp chart (step (play x pre) e) post := by
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  obtain ⟨pre,e,post,W,P,N⟩ := BStarCopyAttemptBand.exact_crossing hp chart sep T band op initial endPC
  have cast : GeneratedOwner hp base addr len x a (pre++e::post) b := W ▸ T
  obtain ⟨m,M,Q⟩ := BStarGeneratedTapeCuts.split hp pre (e::post) cast
  have scope := (split_live hp chart (W ▸ band : LiveAt hp chart x (pre++e::post))).2
  cases Q with
  | next I E J =>
    have O := scope [] (e::post) rfl
    have V := scope [e] post rfl
    change pc (play x pre) root=op at P
    change pc (step (play x pre) e) root=op+1 at N
    obtain ⟨prev,later,H⟩ := hit_of_rise hp chart sep O.1 e I E
      (BStarGeneratedTapeCuts.at_start hp J) O.2 V.2
      (show pc (play x pre) root<pc (step (play x pre) e) root by rw [P,N]; omega)
    change m=.busy (pc (play x pre) root) (.back 0) at prev
    change Hit hp base addr len (play x pre) e (pc (play x pre) root) at H
    rw [P] at prev H
    subst m
    subst later
    exact ⟨pre,e,post,W,M,H,J,(split_live hp chart (u:=[e]) (v:=post) scope).2⟩

/-- Direct bridge from the successful native compiler band (e.g.
post ACQUIRE PC6 to the exact 408 boundary of a committed attempt).
No separate phase cut or initial PC10 mode is required. -/
theorem from_compiler_band {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {a b : Mode} {w : List (Fin n)}
    (T : GeneratedOwner hp base (fun j=>S.getD j fall) len x a w b)
    (band : LiveAt hp chart x w)
    (start : pc x (S.getD 0 fall).1≤9) (finish : 12<pc (play x w) (S.getD 0 fall).1) :
    let addr := fun j=>S.getD j fall
    ∃ (before9 before10 fence numeric tail : List (Fin n)) (ack9 ack10 ack11 ack12 : Fin n),
      w=before9++ack9::(before10++ack10::(fence++ack11::(numeric++ack12::tail))) ∧
      let y9 := play x before9
      let y10 := step y9 ack9
      let at10 := play y10 before10
      let from10 := step at10 ack10
      let from11 := step (play from10 fence) ack11
      GeneratedOwner hp base addr len x a before9 (.busy 9 (.back 0)) ∧
      Hit hp base addr len y9 ack9 9 ∧
      GeneratedOwner hp base addr len y10 .idle before10 (.busy 10 (.back 0)) ∧
      Hit hp base addr len at10 ack10 10 ∧
      GeneratedOwner hp base addr len from10 .idle fence (.busy 11 (.back 0)) ∧
      Hit hp base addr len (play from10 fence) ack11 11 ∧
      GeneratedOwner hp base addr len from11 .idle numeric (.busy 12 (.back 0)) ∧
      Found hp base addr len 12 from11 numeric (.back 0) ∧
      Hit hp base addr len (play from11 numeric) ack12 12 ∧
      GeneratedOwner hp base addr len (step (play from11 numeric) ack12) .idle tail b := by
  obtain ⟨pre,a9,rest,W,P,H,Tail,Live⟩ :=
    ack_at hp chart sep T band 9 start (Nat.lt_trans (by decide : 9<12) finish)
  have endEq : play x w=play (step (play x pre) a9) rest := by
    rw [W,BStarResetSchedule.run_append]
    rfl
  obtain ⟨before10,fence,numeric,tail,a10,a11,a12,E,F⟩ :=
    copy_cuts hp chart sep Tail Live H.2.2.2.1 (endEq ▸ finish)
  exact ⟨pre,before10,fence,numeric,tail,a9,a10,a11,a12,by rw [W,E],P,H,F⟩


/-- The receipt extraction localizes to the exact successful compiler
interval inside the already authenticated COMMIT attempt prefix. -/
theorem original_attempt {base origin : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : X→Prop) (I : Q origin)
    (fiber : ∀ y,Q y → ∀ i,BStarLongFixedRouting.Layout B base i=BStarLongFixedRouting.Layout B y i)
    (closed : ∀ y e,Q y → Q (step y e))
    {w : List (Fin n)}
    (A : BStarPostCutAttempt.AttemptPrefix hp base origin (fun j=>S.getD j fall) len w) :
    let addr := fun j=>S.getD j fall
    ∃ (lead before9 before10 fence num tail : List (Fin n))
      (ack5 ack9 ack10 ack11 ack12 : Fin n) (m : Mode),
      w=lead++ack5::(before9++ack9::(before10++ack10::(fence++ack11::(num++ack12::tail)))) ∧
      let entry := step (play origin lead) ack5
      let from9 := step (play entry before9) ack9
      let from10 := step (play from9 before10) ack10
      let from11 := step (play from10 fence) ack11
      GeneratedOwner hp base addr len entry .idle before9 (.busy 9 (.back 0)) ∧
      Hit hp base addr len (play entry before9) ack9 9 ∧
      GeneratedOwner hp base addr len from9 .idle before10 (.busy 10 (.back 0)) ∧
      Hit hp base addr len (play from9 before10) ack10 10 ∧
      GeneratedOwner hp base addr len from10 .idle fence (.busy 11 (.back 0)) ∧
      Hit hp base addr len (play from10 fence) ack11 11 ∧
      GeneratedOwner hp base addr len from11 .idle num (.busy 12 (.back 0)) ∧
      Found hp base addr len 12 from11 num (.back 0) ∧
      Hit hp base addr len (play from11 num) ack12 12 ∧
      GeneratedOwner hp base addr len (step (play from11 num) ack12) .idle tail m := by
  dsimp only
  let addr := fun j=>S.getD j fall
  let root := (addr 0).1
  have stable (x : X) (l : List (Fin n)) (J : Q x) : Q (play x l) := by
    induction l generalizing x with
    | nil => exact J
    | cons e w ih => exact ih _ (closed _ e J)
  obtain ⟨lead,mid,late,hold,a5,pick,op,W,prior,receipt,P6,
    first,finish,M,P408,live,_⟩ := A
  let old := play origin lead
  let entry := step old a5
  have oldInv : Q old := stable origin lead I
  have oldCurrent := BStarGeneratedTapeCuts.at_end hp prior
  have own : a5=RearTrace.predecessor root := by cases receipt with | consume _ e _ => exact e
  obtain ⟨mode,evt,C⟩ := current_step hp chart Q fiber (fun y q e => closed y e q) sep oldInv a5 _ oldCurrent
  have entered : Current hp base addr len entry .idle := by
    cases evt with
    | transit _ _ _ h _ => exact (h rfl).elim
    | arrived_hold _ n => exact (n own).elim
    | consume _ _ _ => exact C
  have fresh : Q entry := closed _ _ oldInv
  obtain ⟨bm,T,_,_⟩ := generated_word hp chart Q fiber (fun y q e => closed y e q) sep first .idle fresh entered
  have V : LiveAt hp chart entry first := by
    intro p q E
    refine ⟨fiber _ (stable entry p fresh),?_⟩
    cases q with
    | nil =>
      have F : first=p := by simpa using E
      rw [←F]
      change pc (play entry first) root=408 at P408
      change 6≤pc (play entry first) root ∧ pc (play entry first) root≤408
      rw [P408]
      decide
    | cons e q => exact (live p e q E).1
  have low : pc entry root≤9 := by
    change pc entry root=6 at P6
    rw [P6]
    decide
  have high : 12<pc (play entry first) root := by
    change pc (play entry first) root=408 at P408
    rw [P408]
    decide
  obtain ⟨b9,b10,f,num,remain,a9,a10,a11,a12,E,F⟩ :=
    from_compiler_band hp chart sep T V low high
  obtain ⟨_,Tail,_,_⟩ := generated_word hp chart Q fiber (fun y q e => closed y e q) sep (finish++pick::hold) bm
    (stable entry first fresh) (BStarGeneratedTapeCuts.at_end hp T)
  obtain ⟨G9,H9,G10,H10,G11,H11,G12,launch,H12,End⟩ := F
  let x9 := step (play entry b9) a9
  let x10 := step (play x9 b10) a10
  let x11 := step (play x10 f) a11
  let x12 := step (play x11 num) a12
  have cutEq : play x12 remain=play entry first := by
    rw [E,BStarResetSchedule.run_append]
    change play x12 remain=play x9 (b10++a10::(f++a11::(num++a12::remain)))
    rw [BStarResetSchedule.run_append]
    change play x12 remain=play x10 (f++a11::(num++a12::remain))
    rw [BStarResetSchedule.run_append]
    change play x12 remain=play x11 (num++a12::remain)
    rw [BStarResetSchedule.run_append]
    rfl
  have join {x : X} {a b c : Mode} {u v : List (Fin n)}
      (R : GeneratedOwner hp base addr len x a u b)
      (P : GeneratedOwner hp base addr len (play x u) b v c) :
      GeneratedOwner hp base addr len x a (u++v) c := by
    induction R with
    | endpoint _ => exact P
    | next I E _ ih => exact .next I E (ih P)
  have final := join End (cutEq.symm ▸ Tail)
  refine ⟨lead,b9,b10,f,num,remain++(finish++pick::hold),a5,a9,a10,a11,a12,_,?_,
    G9,H9,G10,H10,G11,H11,G12,launch,H12,final⟩
  rw [W,M,E]
  simp only [List.append_assoc,List.cons_append]

#print axioms hit_of_rise
#print axioms first_ack
#print axioms copy_cuts
#print axioms ack_at
#print axioms from_compiler_band
#print axioms original_attempt
end L4.BStarCopyFenceCuts
