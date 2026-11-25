import Leader.L4.BStarNumericCompleteSweep

namespace L4.BStarNumericTailCarry
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongArithmetic BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter BStarResetRailRing
open BStarOwnerLaunchOrigin BStarSeparatingRail BStarAcquireForwardTrace
open BStarNumericCarry BStarNumericContinuity BStarNumericConsecutive BStarNumericChronology
open BStarNumericReceipt BStarLongEvents

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "run" => BStarResetSchedule.run step
local notation "D" => Departure (n:=n) (k₁:=k₁) (k₂:=k₂) (t₂:=t₂) (J₁:=J₁) (J₂:=J₂)
  (r:=r) (c:=c) (p:=p) (c₁:=c₁)

private theorem split_after {base x : X} {addr : Nat → Pos n} {len op k l : Nat}
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base addr len op x k w l ds)
    (d : D) (before after : List D) (E : ds=before++d::after) :
    ∃ pre tail, w=pre++d.mark::tail ∧ run x pre=d.old ∧
      Aligned hp base addr len op (step d.old d.mark) (d.index+1) tail l after := by
  induction A generalizing before with
  | nil _ => cases before <;> contradiction
  | stay _ _ T ih =>
    obtain ⟨pre,tail,W,R,Q⟩ := ih before E
    exact ⟨_::pre,tail,congrArg (List.cons _) W,R,Q⟩
  | @hop x k e w l ds C a p I V U T ih =>
    cases before with
    | nil =>
      obtain ⟨eq,rst⟩ := List.cons.inj E
      subst d
      subst after
      exact ⟨[],w,rfl,rfl,T⟩
    | cons d' before =>
      obtain ⟨pre,tail,W,R,Q⟩ := ih before (List.cons.inj E).2
      exact ⟨e::pre,tail,congrArg (List.cons e) W,R,Q⟩

private theorem pad_after {base x : X} {addr : Nat → Pos n} {len op k l : Nat}
    {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base addr len op x k w l ds)
    (no : ds.filter (significant hp base addr)=[]) :
    ∀ j, k≤j → j<l → (addr j).2.val≠1 ∨ (longGeometry B (base (addr j).1)).inside=false := by
  obtain ⟨_,ind⟩ := (Aligned.to_tape hp A).indices
  intro j J K
  have m : j∈ds.map Departure.index := by
    rw [ind]
    exact List.mem_range'.mpr ⟨j-k,by omega,by simp; omega⟩
  obtain ⟨d,M,E⟩ := List.mem_map.mp m
  have n' : significant hp base addr d=false := by
    cases H : significant hp base addr d
    · rfl
    · have ne := List.mem_filter.mpr ⟨M,H⟩
      rw [no] at ne
      contradiction
  unfold significant at n'
  rw [E] at n'
  cases I : (longGeometry B (base (addr j).1)).inside
  · exact .inr rfl
  · simp [I] at n'
    exact .inl n'

/-- Canonical output of the actual last significant digit is the old
forward at the terminal: the intervening raw labels are proved to be
stays or nonsignificant departures by the authenticated tape. -/
theorem last_to_terminal {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op k : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x k w len ds)
    (q : Payload) (Q : project (fun j => S.getD j fall) (run x w) len=.forward q)
    (H : Numeric q) (i : Nat) (code : L4.Compiler.Native.Code)
    (Nd : nodeOf q.opcode.toNat=some i) (Cd : get i=some code)
    (before : List D) (d : D)
    (last : ds.filter (significant hp base (fun j => S.getD j fall))=before++[d]) :
    (physicalDigit (geom hp d) (byte d) i code d.offer).2=q := by
  obtain ⟨ini,rest,E,_,R⟩ := (List.filter_eq_append_iff
    (L₁:=before) (L₂:=[d])).mp last
  obtain ⟨skipped,tail,Et,_,yes,no⟩ := List.filter_eq_cons_iff.mp R
  have split : ds=(ini++skipped)++d::tail := by rw [E,Et,List.append_assoc]
  obtain ⟨pre,gap,W,Old,T⟩ := split_after hp A d _ _ split
  have M : d∈ds := by rw [split]; simp
  obtain ⟨V,_,bound⟩ := Aligned.record_facts hp A d M
  obtain ⟨one,inside⟩ := Aligned.record_significant hp A d M yes
  have Rdy := BStarNumericHealthy.records_ready hp chart sep A (Nat.le_refl _) q Q H i code Nd Cd d
    (by rw [last]; simp)
  obtain ⟨⟨N,J,F⟩,canon⟩ := Rdy
  let p := (physicalDigit (geom hp d) (byte d) i code d.offer).2
  have L := (digit_record hp _ d V N i code J Cd (sep _) one inside F).2
  have endQ : project (fun j => S.getD j fall) (run (step d.old d.mark) gap) len=.forward q := by
    rw [W,BStarResetSchedule.run_append] at Q
    change project _ (run (step (run x pre) d.mark) gap) len=.forward q at Q
    rwa [Old] at Q
  exact busy_padding hp chart sep (Aligned.busy hp T) (d.index+1) len p q rfl rfl
    (Nat.le_refl _) (pad_after hp T no) L (digit_numeric _ _ _ _ _ N F).1 canon endQ H

/-- A post-sweep selected terminal offer has exactly the last
local output as its canonical bound input. -/
theorem last_to_offer {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op k : Nat} {w : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x k w len ds)
    (q : Payload) (Q : project (fun j => S.getD j fall) (run x w) len=.forward q)
    (H : Numeric q) (i : Nat) (code : L4.Compiler.Native.Code)
    (Nd : nodeOf q.opcode.toNat=some i) (Cd : get i=some code)
    (before : List D) (d : D)
    (last : ds.filter (significant hp base (fun j => S.getD j fall))=before++[d])
    (e : Fin n) (C : CommandClaim) (v : Payload) (Nv : Numeric v)
    (idx : S.getD len fall=address e C.source)
    (sel : let y := run x w
      (C,.advance v)∈actualOffers (oldPair B y e) ((y e).long,(y (rightNeighbor e)).long)) :
    (physicalDigit (geom hp d) (byte d) i code d.offer).2=v := by
  have E := last_to_terminal hp chart sep A q Q H i code Nd Cd before d last
  have R := BStarNumericHealthy.records_ready hp chart sep A (Nat.le_refl _) q Q H i code Nd Cd d
    (by rw [last]; simp)
  have J : ∀ g j, bind g j (.forward q)=.forward q := by
    rw [←E]
    exact R.2
  let y := run x w
  let g := oldPair B y e
  let raw : Pair (BitVec LW) := ((y e).long,(y (rightNeighbor e)).long)
  have b := offer_exact g raw C v sel Nv
  have old := (old_read y e C.source).trans ((congrArg (atCursor y) idx).symm.trans Q)
  unfold BStarLongTransport.bound at b
  rw [old,J] at b
  exact E.trans (Token.forward.inj b)

/-- Last-step projection of the accepted digit sweep; the same
kernel theorem applies also when the output register is scalar-only. -/
theorem sweep_last (visits : List D) (i : Nat) (code : L4.Compiler.Native.Code)
    (tokens : Nat → Payload)
    (initial : ∀ j : Fin visits.length,tokens j.val=visits[j.val].offer)
    (S : BStarPhysicalWordSem.DigitSweep
      (fun j : Fin visits.length => geom hp visits[j.val])
      (fun j : Fin visits.length => byte visits[j.val])
      (fun j : Fin visits.length => ((physicalDigit (geom hp visits[j.val]) (byte visits[j.val])
        i code visits[j.val].offer).1).apply (byte visits[j.val])) i code tokens)
    (before : List D) (d : D) (last : visits=before++[d]) :
    tokens visits.length=(physicalDigit (geom hp d) (byte d) i code d.offer).2 := by
  subst visits
  have h : before.length < (before++[d]).length := by simp
  let j : Fin (before++[d]).length := ⟨before.length,h⟩
  have pair := congrArg Prod.snd (S.step j)
  dsimp only at pair
  rw [initial j] at pair
  have E : (before++[d])[j.val]=d := by
    change (before++[d])[before.length]=d
    simp
  rw [E] at pair
  simpa [j] using pair.symm

/-- The actual native source accepts precisely the codec of the final
DigitSweep token. The final token is not supplied by the caller:
it is the output of the authenticated last old significant mark. -/
theorem receipt_of_sweep {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (chart : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    {op : Nat} {turn door : Fin n} {w ret : List (Fin n)} {ds : List D}
    (A : Aligned hp base (fun j => S.getD j fall) len op x 0 w len ds)
    (T : BusyOnly hp base (fun j => S.getD j fall) len op (step (run x w) turn) (.back len) ret (.back 0))
    (hit : BStarNativeReceiptTape.Hit hp base (fun j => S.getD j fall) len
      (run (step (run x w) turn) ret) door op)
    (lo : 13≤op) (hi : op<408)
    (C : CommandClaim) (v : Payload) (K : C.source.occurrence.val=10) (hd : C.destination=none)
    (idx : S.getD len fall=address turn C.source)
    (sel : let y := run x w
      (C,.advance v)∈actualOffers (oldPair B y turn) ((y turn).long,(y (rightNeighbor turn)).long))
    (i : Nat) (code : L4.Compiler.Native.Code) (Nd : nodeOf op=some i) (Cd : get i=some code)
    (before : List D) (d : D)
    (last : ds.filter (significant hp base (fun j => S.getD j fall))=before++[d])
    (tokens : Nat → Payload) :
    let visits := ds.filter (significant hp base (fun j => S.getD j fall))
    (∀ j : Fin visits.length,tokens j.val=visits[j.val].offer) →
    BStarPhysicalWordSem.DigitSweep
      (fun j : Fin visits.length => geom hp visits[j.val])
      (fun j : Fin visits.length => byte visits[j.val])
      (fun j : Fin visits.length => ((physicalDigit (geom hp visits[j.val]) (byte visits[j.val])
        i code visits[j.val].offer).1).apply (byte visits[j.val])) i code tokens →
    (tokens visits.length=v ∧
      let z := run (step (run x w) turn) ret
      let a := (S.getD 0 fall).1
      bind (longGeometry B (z a)) 0 (atSite (z a).long 0)=.reply (output (tokens visits.length))) := by
  dsimp only
  intro initial sweep
  obtain ⟨N,Op,_⟩ := BStarReplyBack.numeric_selected_from_hit hp chart sep T hit lo hi C v K hd idx sel
  obtain ⟨⟨q,Q,Hq,Eq⟩,R⟩ := BStarNumericTerminal.selected_return hp chart sep T C v K hd idx sel N
  have J : nodeOf q.opcode.toNat=some i := by rw [Eq,Op,Nd]
  have out := last_to_offer hp chart sep A q Q Hq i code J Cd before d last turn C v N idx sel
  have tail := sweep_last hp _ i code tokens initial sweep before d last
  have E := tail.trans out
  exact ⟨E,E.symm ▸ R⟩

end L4.BStarNumericTailCarry
