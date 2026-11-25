import Leader.L4.PhysicalSeparatorRace
import Leader.L4.PhysicalHealthyCertificate
import Leader.L4.PhysicalCustodyPassMean

namespace L4.PhysicalOwnerAttempt
open AllSizeProtocol BStarTrace PhysicalCustody BStarLongWork BStarLongClaims
open BStarH6WordChart BStarAcquireLiteralChain BStarLongFixedRouting BStarFenceLineGeometry BStarH6Ordinal
open BStarLongDoor BStarSeparatingRail BStarClearanceResidual BStarClearanceOffset
open BStarAcquireVisitOrder BStarResetChartTouch BStarResetChartService BStarAcquireAnchors
open BStarResetSchedule BStarResetMarkAdapter BStarResetHealthyService BStarAcquireRailCoverage
open BStarSeparatorControl PhysicalEligibleReply PhysicalReceiptCut PhysicalSeparatorRace
open ScoredTapeSerial ScoredTapeCertificates PhysicalHealthyCertificate PhysicalSixRaceReplay
local notation "hp" => (show 0<2 by decide)

def attemptCost (n W len : Nat) : Nat :=
  ((((252*n*W+3*n)+252*n*W)+n)+(412*(n+(252*n*W+n))))+
    ((n+n*(2*len+1)+n*2)+((n*(2*len+1)+n*2)+(n*(2*len+1)+n*1)))

private theorem app {s n : Nat} (x : Raw s n) (u v : Word n) :
    rawRun x (u++v)=rawRun (rawRun x u) v := BStarResetSchedule.run_append _ _ _ _

/-- The full stopped owner attempt binds each new reader at its actual
successful predecessor cut. Each wrong incident label stops the
attempt; no waiting or rereading for a later doublet takes place. -/
noncomputable def owner_attempt {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : Raw s n→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,Layout (rows s) base i=Layout (rows s) q i)
    (closed : ∀ q,Q q→∀ e,Q (rawNext s q e))
    {l d w : Nat} (LF : BStarCopyLeftStrip.Strip (rows s) base (S.getD 0 fall).1 l w)
    (RF : RightFrame (rows s) base (S.getD len fall).1 d w) (dp : 0<d)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry (rows s) (base i)).inside=decide (oldOrdinal (rows s) base hh i<w) ∧
      (longGeometry (rows s) (base i)).last=decide (oldOrdinal (rows s) base hh i+1=w))
    (notShort : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → w≤oldOrdinal (rows s) base hh i+1)
    (hn : 0<n) (hl : 0<l+w) (lc : l+w≤n) (rc : d+w≤n)
    (head : ∀ i,let g:=longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair (rows s) base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 (rows s) base) hh 5 base) (cx : ∀ q,Q q→correct (oldH6 (rows s) base) hh 5 q)
    (W : Nat) (wW : w≤W)
    (width : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → oldOrdinal (rows s) base hh i+1≤W)
    (four : 4≤n) :
    Certificate n 1 729 (attemptCost n W len)
      (firstCredit (HoldsCredit (BStarOwnerRecoveryPass.Recovered hp base hh)) o x) := by
  let addr := fun j=>S.getD j fall
  let d₀ := RearTrace.predecessor (addr 0).1
  let C := separator_from_arbitrary_reader chart sep Q I layout closed LF RF dp seam flags
    notShort hn hl lc rc head cont cb cx W wW width four
  let Z (u : Word n) (r : Word n) := Zero base hh Q addr len (rawRun (rawRun x u) r)
  let C₀ := C.bind hn Z (fun u H=>residual_to_zero_reader chart sep Q layout closed
    LF RF dp seam flags notShort hn hl lc rc head cont cb cx W wW width
    (by obtain ⟨_,_,_,_,_,H⟩ := H; exact H))
  let Ht (u r : Word n) := HealthyPost base (rawRun x u) Q addr len r
  let C₁ := C₀.bind hn Ht (fun u H=>by
    have Y' : Zero base hh Q addr len (rawRun x u) := by
      obtain ⟨v,r,E,_,Y⟩ := H
      rw [E,app]
      exact Y
    exact certificate_from_issue0 chart four Q layout (fun q e H=>closed q H e) sep head cont Y'.1 Y'.2)
  apply C₁.map
  intro w P
  obtain ⟨u0,heal,W,H0,H⟩ := P
  obtain ⟨cut,res, U,Sp,_⟩ := H0
  obtain ⟨receipt,gS,S,rcv,disj,_⟩ := Sp
  obtain ⟨u,v,E,Launch,Seen,Q1,Wait,Clean⟩ := rcv
  obtain ⟨pre,t₀,a₀,b₀,t₁,a₁,b₁,t₂,gF,HW,Ready,V₀,V₁,V₂,A₀,B₀,A₁,B₁,F⟩ :=
    healthy_post_parts H
  have recCut : rawRun x receipt=rawRun (rawNext s (rawRun x u) d₀) v := by
    rw [E,app]; rfl
  rw [recCut] at Wait Clean
  have seed : rawRun (rawRun x u0) pre =
      rawRun (rawRun (rawRun (rawNext s (rawRun x u) d₀) v) (gS++[d₀])) (res++pre) := by
    simp only [U,S,app,recCut] <;> rfl
  rw [seed] at Ready V₀ V₁ V₂
  have A := recovered_of_six_cuts chart Q layout (fun y e H=>closed y H e)
    sep head cont I u v gS (res++pre) t₀ a₀ b₀ t₁ a₁ b₁ t₂ gF
    Launch Seen Wait Clean Ready V₀ V₁ V₂ disj A₀ B₀ A₁ B₁ F
  obtain ⟨credit,comm,R⟩ := A
  have eq : w=u++[d₀]++v++(gS++[d₀])++(res++pre)++[d₀]++t₀++pairWord d₀ a₀ b₀++
      t₁++pairWord d₀ a₁ b₁++t₂++(gF++[d₀]) := by
    rw [W,U,S,E,HW]
    simp only [List.append_assoc,List.cons_append,List.nil_append] <;> rfl
  rw [←eq] at comm
  obtain ⟨r,Cr,HR⟩ := replay_holds_credit comm R
  refine ⟨r,Cr,?_,HR⟩
  obtain ⟨a,b,L,m,q,p,E,F,G,_⟩ := HR
  rw [F,G] at L
  rw [E]
  simp only [List.length_append] at L ⊢
  omega

theorem first_credit_shift_pad {s n : Nat} {X : Type}
    {E : X→Raw s n→Word n→Prop} {o : X} {x : Raw s n} {u v p : Word n}
    (H : firstCredit (HoldsCredit E) o (rawRun x u) v) :
    firstCredit (HoldsCredit E) o x (u++(v++p)) := by
  obtain ⟨r,Comm,Pos,j,k,L,K⟩ := H
  have V := PhysicalCustodyCommonWord.commute_append (Commuted.refl u)
    (PhysicalCustodyCommonWord.commute_suffix p Comm)
  have w := BStarRecoveryPass.credit_append (rawNext s)
    (BStarRecoveryPass.credit_shift (rawNext s) u K) p
  refine ⟨u++(r++p),V,?_,u.length+j,u.length+k,by omega,?_⟩
  · simp only [List.length_append]; omega
  · simpa only [List.append_assoc] using w

/-- Uniform renewal on the literal accumulated tape. Failed attempts
restart at the actual endpoint, with the failed label retained. The
single commuted witness for success is shifted past failed prefixes. -/
theorem owner_credit_expected {s n : Nat} {base x : Raw s n}
    {hh : ∃ i,oldH6 (rows s) base i=true}
    {o : Owners (oldH6 (rows s) base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (Q : Raw s n→Prop) (I : Q x)
    (layout : ∀ q,Q q→∀ i,Layout (rows s) base i=Layout (rows s) q i)
    (closed : ∀ q,Q q→∀ e,Q (rawNext s q e))
    {l d w : Nat} (LF : BStarCopyLeftStrip.Strip (rows s) base (S.getD 0 fall).1 l w)
    (RF : RightFrame (rows s) base (S.getD len fall).1 d w) (dp : 0<d)
    (seam : BStarCopyRightStrip.addr (S.getD 0 fall).1 l=(S.getD len fall).1)
    (flags : ∀ i,(longGeometry (rows s) (base i)).inside=decide (oldOrdinal (rows s) base hh i<w) ∧
      (longGeometry (rows s) (base i)).last=decide (oldOrdinal (rows s) base hh i+1=w))
    (notShort : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → w≤oldOrdinal (rows s) base hh i+1)
    (hn : 0<n) (hl : 0<l+w) (lc : l+w≤n) (rc : d+w≤n)
    (head : ∀ i,let g:=longGeometry (rows s) (base i); (!g.axes.h6 || g.inside)=true)
    (cont : ∀ i,let g:=oldPair (rows s) base i; BStarAcquireRailCoverage.continuation g.1 g.2=true)
    (cb : correct (oldH6 (rows s) base) hh 5 base) (cx : ∀ q,Q q→correct (oldH6 (rows s) base) hh 5 q)
    (W : Nat) (wW : w≤W)
    (width : ∀ i,oldH6 (rows s) base (rightNeighbor i)=true → oldOrdinal (rows s) base hh i+1≤W)
    (four : 4≤n) :
    L4.IIDExpectedHittingTimeAtMost extendTape
      (firstCredit (HoldsCredit (BStarOwnerRecoveryPass.Recovered hp base hh)) o x)
      [] (729*attemptCost n W len) := by
  let Goal := firstCredit (HoldsCredit (BStarOwnerRecoveryPass.Recovered hp base hh)) o x
  let Adm := fun p=>Q (rawRun x p)
  have preserve (z : Raw s n) (w : Word n) (H : Q z) : Q (rawRun z w) := by
    induction w generalizing z with
    | nil => exact H
    | cons e w ih => exact ih _ (closed _ H e)
  apply TripleRenewal.expected_of_uniform_attempts extendTape Goal Adm (attemptCost n W len) 729
    (by decide) _ [] I
  intro pre P notDone
  let R := owner_attempt chart sep Q P layout closed LF RF dp seam flags
    notShort hn hl lc rc head cont cb cx W wW width four
  have complete (z : R.reader.State) (V : R.reader.valid z) (T : R.reader.done z)
      (F : ¬R.reader.reject z) (pad : Word n) : Goal (pre++(R.reader.word z++pad)) :=
    first_credit_shift_pad (R.sound ⟨z,V,T,F⟩)
  have live : ¬R.reader.done R.reader.start := by
    intro T
    by_cases F : R.reader.reject R.reader.start
    · have Z := R.reader.lost _ R.reader.valid_start T F
      rw [R.reader.initial_credit] at Z
      omega
    · have H := complete _ R.reader.valid_start T F []
      rw [R.reader.word_start,List.nil_append,List.append_nil] at H
      exact notDone H
  exact ⟨ScoredTapeRenewal.uniformAttempt R.reader pre Goal Adm live (by decide)
    (fun w=>by change Q (rawRun x (pre++w)); rw [app]; exact preserve _ _ P)
    complete⟩

end L4.PhysicalOwnerAttempt
