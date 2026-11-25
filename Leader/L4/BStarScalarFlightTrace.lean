import Leader.L4.BStarScalarFits
import Leader.L4.BStarNativeAttemptReceipts
import Leader.L4.BStarGeneratedBandScan
import Leader.L4.BStarScalarHistory

namespace L4.BStarScalarFlightTrace
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongWork BStarLongToken BStarLongDoor BStarLongCommand
open BStarGeneratedOwner BStarGeneratedPCAncestry BStarGeneratedBandScan BStarScalarHistory
open BStarResetChartService BStarResetMarkAdapter BStarSeparatorControl
open BStarAcquireVisitOrder BStarAcquireLiteralChain BStarH6WordChart
open BStarLongFixedRouting BStarResetChartTouch BStarOwnerControlHistory
open BStarResetControllerEntry BStarClearanceSource BStarAcquireWaitControl
open BStarLiteralPC BStarArithmeticControllerReturn BStarJoinedControllerReturn

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private theorem own_mark {e i : Fin n} (H : rightNeighbor e=i) :
    e=RearTrace.predecessor i := by rw [←H,RearTrace.predecessor_right]

/-- No arithmetic-band stutter of the genuine generated-owner
automaton can be a receipt or a failed issue. -/
theorem quiet_mark {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {e : Fin n} {a b : Mode}
    (I : Current hp base (fun j => S.getD j fall) len x a)
    (E : Event hp (fun j => S.getD j fall) len x e a b)
    (low : 13≤pc (step x e) (S.getD 0 fall).1)
    (high : pc (step x e) (S.getD 0 fall).1≤408)
    (eq : pc (step x e) (S.getD 0 fall).1=pc x (S.getD 0 fall).1) :
    FlightMark hp x (S.getD 0 fall).1 e := by
  let i := (S.getD 0 fall).1
  change 13≤pc (step x e) i at low
  change pc (step x e) i≤408 at high
  change pc (step x e) i=pc x i at eq
  have HH := root_header hp C same
  have foreign (A : e≠RearTrace.predecessor i) : FlightMark hp x i e :=
    ⟨HH.1,fun H => (A (own_mark H)).elim⟩
  cases E with
  | idle_hold ne => exact foreign ne
  | arrived_hold op away => exact foreign away
  | bad_issue own bad =>
    have A := idle_launch_or_hold hp C same I.2 sep e I.1
    rcases A with h|h|h
    · exact (h.1 own).elim
    · have P := congrArg (fun t : (Token × BitVec 2) × BitVec 9 => t.2.toNat) h.2.2.1
      change pc (step x e) i=0 at P
      omega
    · obtain ⟨_,_,N,_⟩ := h.2.1
      rw [bad] at N
      contradiction
  | launch own L =>
    refine ⟨HH.1,fun _ => ⟨L.1.1,.inl ⟨L.1.2,?_,L.2.choose,L.2.choose_spec.1⟩⟩⟩
    change pc x i≠1
    omega
  | transit op z d live seen =>
    refine ⟨HH.1,fun _ => ⟨I.1.2.1,.inr ⟨I.1.2.2.1,?_⟩⟩⟩
    have Q : project (fun j => S.getD j fall) x 0=atSite (x i).long 0 := by
      change atSite (x i).long (S.getD 0 fall).2=_
      rw [HH.2]
    have G := I.2.1
    cases z with
    | out k =>
      cases k with
      | zero =>
        obtain ⟨payload,h⟩ := G.2.1
        rw [Q] at h
        rw [h]
        exact .inr (bound_F _ _ _)
      | succ k =>
        have h := G.2.2 0 (by omega)
        rw [Q] at h
        rw [h]
        exact .inl rfl
    | back k =>
      cases k with
      | zero => exact (live rfl).elim
      | succ k =>
        have h := G.2.2.1 0 (by omega)
        rw [Q] at h
        rw [h]
        exact .inl rfl
  | consume op own clean =>
    have ev : Event hp (fun j => S.getD j fall) len x e (.busy op (.back 0)) .idle :=
      .consume op own clean
    have hdr : (oldHeaders B (x (S.getD 0 fall).1)).h6=true := HH.1
    obtain ⟨f,_,N⟩ := consume_pc hp (base:=base) (x:=x)
      (addr:=fun j => S.getD j fall) (len:=len) (op:=op) (e:=e) HH.2 hdr (sep e) I ev
    change pc (step x e) i=pcNext (x i).long f at N
    have U : pcNext (x i).long f≤408 := N ▸ high
    have L : 7≤pcNext (x i).long f := by omega
    have P := (next_to_band (x i).long f L U).1
    change pcNext (x i).long f=pc x i+1 at P
    change pc (step x e) i=pc x i at eq
    omega

open BStarNativeReceiptTape BStarGeneratedTapeCuts

/-- The literal no-jump prefix carried by each NativeTape.take is an
actual scalar-preserving word. No classification of scheduler edges
external to the genuine generated-owner word is necessary. -/
theorem flat_flight {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ u, ∀ i, Layout B base i=Layout B (run x u) i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {w : List (Fin n)} {a b : Mode}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x a w b)
    (flat : Flat hp x (S.getD 0 fall).1 w)
    (lo : 13≤pc x (S.getD 0 fall).1) (hi : pc x (S.getD 0 fall).1≤408) :
    ∀ u e v,w=u++e::v → FlightMark hp (run x u) (S.getD 0 fall).1 e := by
  intro u e v W
  obtain ⟨m,_,rest⟩ := BStarGeneratedTapeCuts.split hp u (e::v) (W ▸ T)
  have A := flat u (e::v) W
  have H : w=(u++[e])++v := by simpa [List.append_assoc] using W
  have E := flat (u++[e]) v H
  rw [BStarResetSchedule.run_append] at E
  change pc (step (run x u) e) (S.getD 0 fall).1=pc x (S.getD 0 fall).1 at E
  cases rest with
  | next I ev _ =>
    exact quiet_mark hp C (same u) sep I ev (E.symm ▸ lo) (E.symm ▸ hi) (E.trans A.symm)

theorem to_hit_scalar_hold {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ u, ∀ i, Layout B base i=Layout B (run x u) i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {pre : List (Fin n)} {op : Nat} {e : Fin n}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len x .idle pre (.busy op (.back 0)))
    (flat : Flat hp x (S.getD 0 fall).1 pre)
    (hit : Hit hp base (fun j => S.getD j fall) len (run x pre) e op)
    (lo : 13≤op) (hi : op≤407) (j : Nat) :
    BStarLongArithmetic.source (run x pre (S.getD 0 fall).1).long j =
      BStarLongArithmetic.source (x (S.getD 0 fall).1).long j := by
  have E := hit.2.2.1
  have F := flat pre [] (List.append_nil _).symm
  have G : pc x (S.getD 0 fall).1=op := F.symm.trans E
  exact word_scalar_hold hp x (S.getD 0 fall).1 pre sep
    (flat_flight hp C same sep T flat (by omega) (by omega)) j

open BStarScalarFits BStarAliasFold BStarAliasRoster BStarNativeReceiptInduction
open BStarLongArithmetic L4.Compiler.Native L4.Compiler.Interp

private theorem has_kind {k : Nat} (K : k<395) : (arithKind (13+k)).isSome=true := by
  have L : k<BStarLongSignatures.arithmetic.length := by rw [signature_pins.1]; omega
  simp [arithKind,show ¬13+k<13 by omega, L]

/-- The scalar representation transfer from a genuine nonfinal Hit
to the actual old image of the next Hit. Geometry, valid WAIT,
scheduler identity, matching bound reply, no-write intervening marks,
and exact packed width are each discharged by the corresponding
literal receipt/trace theorems. Only live operand semantics remain. -/
theorem hit_scalar_store_next {base x : X} {hh : ∃ i,oldH6 B base i=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall)
    (same : ∀ i, Layout B base i=Layout B x i)
    (sep : ∀ e : Fin n,e≠rightNeighbor e) {e : Fin n} {k : Nat}
    (K : k<394) (c' : Code) (G : get (start k)=some c')
    (hit : Hit hp base (fun j => S.getD j fall) len x e (13+k))
    {pre : List (Fin n)} {next : Fin n}
    (T : GeneratedOwner hp base (fun j => S.getD j fall) len (step x e) .idle pre
      (.busy (13+k+1) (.back 0)))
    (flat : Flat hp (step x e) (S.getD 0 fall).1 pre)
    (nhit : Hit hp base (fun j => S.getD j fall) len (run (step x e) pre) next (13+k+1))
    (nextSame : ∀ u, ∀ i, Layout B base i=Layout B (run (step x e) u) i)
    {r₀ : Nat} (table : PrimTable r₀) (bank : Bank)
    (regs : List Value) (L : regs.length=start k+1)
    (capture : ∀ q i, ((capturedHeader q i).read (x (S.getD 0 fall).1).long).toNat=
      (bank.hdr q i).toNat)
    (M : MuxBound (x (S.getD 0 fall).1).long c')
    (head : ∀ f, bind (longGeometry B (x (S.getD 0 fall).1)) 0
      (atSite (x (S.getD 0 fall).1).long 0)=.reply f →
      PayloadBound c' f.argument.toNat ∧
      WellRep (x (S.getD 0 fall).1).long
        (headPending (x (S.getD 0 fall).1).long k f c') regs literalCmp) :
    WellRep (run (step x e) pre (S.getD 0 fall).1).long []
      (runCodes table bank regs (suffix k)) literalCmp := by
  let i := (S.getD 0 fall).1
  obtain ⟨cur,_,opc,npc,own,f,R,F,O⟩ := hit
  change e=RearTrace.predecessor i at own
  have eq : rightNeighbor e=i := own ▸ RearTrace.right_predecessor _
  have HH := (root_header hp C same).1
  have HN : pc (step x e) i=13+k+1 := npc
  have hb₁ : 13≤pc (step x e) (S.getD 0 fall).1 := by change 13≤pc (step x e) i; omega
  have hb₂ : pc (step x e) (S.getD 0 fall).1≤408 := by change pc (step x e) i≤408; omega
  have flights := flat_flight hp C nextSame sep T flat hb₁ hb₂
  have ⟨pb,rep⟩ := head f R
  have fit := receipt_fit table bank (x i).long (by omega : k<395) f G regs L rep capture pb M
  have alias := roster_alias_run table bank (x i).long (by omega : k<395)
    regs (headPending (x i).long k f c') capture L rep
  have vv := cur.1.2.1
  have ph := cur.1.2.2.1
  -- The next Hit is part of this timeline, rather than a reconstructed launch.
  have nextOp : pc (run (step x e) pre) i=13+k+1 := nhit.2.2.1
  have baseOp : pc (step x e) i=pc (run (step x e) pre) i := by
    exact (flat pre [] (List.append_nil _).symm).symm
  have _ := baseOp.trans nextOp
  dsimp only [i] at eq fit alias
  dsimp only at vv ph opc R
  rw [←eq] at HH vv ph opc R flights fit alias ⊢
  exact receipt_scalar_store hp x e f k c' K G HH vv ph opc R F O (has_kind (by omega))
    pre sep flights _ fit alias

end L4.BStarScalarFlightTrace
