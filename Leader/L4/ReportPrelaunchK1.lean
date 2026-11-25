
import Leader.L4.ReportPrelaunchK1Lift

namespace L4.ReportPrelaunchK1

open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ShortResetCycle ShortResetChart ShortLayerGeometry
open ReportResetBarrier ReportPrelaunchRank ReportPrelaunchClock
open ReportByteRows ReportPrelaunchK1Geometry ReportPrelaunchK1Lift
open BStarH6Ordinal

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

variable {s n : Nat} {h : Fin n→Bool}

private def W (L g i : Nat) (t : Tok) : Nat := rank L g i (label t)

private theorem label_F (t : Tok) (H : t.tag=2) :
    label t=.front t.race t.fault := by simp [label,H]

private theorem label_D (t : Tok) (H : t.tag=3) :
    label t=.reply := by simp [label,H]

private theorem label_T (t : Tok) (H : t.tag=1) :
    label t=.trail := by simp [label,H]

private theorem label_E (t : Tok) (H : t.tag=0) :
    label t=.e := by simp [label,H]

private theorem label_canonT : label MISByteCodec.T=.trail := rfl
private theorem label_canonE : label MISByteCodec.E=.e := rfl

/-- Ready hop pays even if the arbitrary arrival decodes to E/T/D,
    rather than to a healthy or fault F. In fact the row exports the
    exact arrival wire; this inequality does not require its codec fit. -/
private theorem hop_any {L g i : Nat} (J : i+1<L)
    (t z z' : Tok) (F : t.tag=2) :
    rank L g i .trail+W L g (i+1) z'<W L g i t+W L g (i+1) z := by
  unfold W
  rw [label_F t F]
  cases H : label z' with
  | front r f => exact forward_strict J (label z) t.race r t.fault f
  | e =>
    have A := forward_strict (g:=g) J (label z) t.race 0 t.fault true
    have B : rank L g (i+1) .e≤rank L g (i+1) (.front 0 true) := by
      simp [rank]
    omega
  | trail =>
    have A := forward_strict (g:=g) J (label z) t.race 0 t.fault true
    have B : rank L g (i+1) .trail≤rank L g (i+1) (.front 0 true) := by
      simp [rank]; omega
    omega
  | reply =>
    have A := forward_strict (g:=g) J (label z) t.race 0 t.fault true
    have B : rank L g (i+1) .reply≤rank L g (i+1) (.front 0 true) := by
      simp [rank]; omega
    omega

private def RacePays (p : Params) (side : Nat) (g : Bool) (t : Tok) : Prop :=
  healthyAdmit p t ∧ g=true ∧
    (t.race=1 ∨ t.race=(if side=3 then 2 else 3))

private theorem norm_le (p : Params) (L g i : Nat) (a : Bool)
    (w : BitVec (tokenW p)) (side : Nat) (S : side=2 ∨ side=3)
    (G : a=true↔i=g) :
    W L g i (ReportByteRows.decode p a (rankNormWire p side a w))≤
      W L g i (ReportByteRows.decode p a w) := by
  obtain E|⟨gate,T,F,T',F',R⟩ := rank_norm_cases p a w side S
  · rw [E]; exact Nat.le_refl _
  · have E := G.mp gate
    subst i
    unfold W
    rw [label_F _ T,label_F _ T',F,F']
    exact Nat.le_of_lt (gate_race_strict L g _ _ R)

private theorem norm_pays (p : Params) (L g i : Nat) (a : Bool)
    (w : BitVec (tokenW p)) (side : Nat) (S : side=2 ∨ side=3)
    (G : a=true↔i=g)
    (P : RacePays p side a (ReportByteRows.decode p a w)) :
    W L g i (ReportByteRows.decode p a (rankNormWire p side a w))<
      W L g i (ReportByteRows.decode p a w) := by
  obtain ⟨H,G0,R⟩ := P
  have E := G.mp G0
  subst i; subst a
  have N := rank_norm_race p w side S H R
  unfold W
  rw [N,label_F _ H.1]
  have T0 : ({ReportByteRows.decode p true w with
      race:=admitRaceAfter side (ReportByteRows.decode p true w).race} : Tok).tag=2 := H.1
  rw [label_F _ T0]
  change rank L g g (.front (admitRaceAfter side (ReportByteRows.decode p true w).race)
      (ReportByteRows.decode p true w).fault)<
    rank L g g (.front (ReportByteRows.decode p true w).race (ReportByteRows.decode p true w).fault)
  rw [H.2.1]
  apply gate_race_strict
  rcases S with rfl|rfl <;> rcases R with R|R <;>
    simp [RaceAdvance,admitRaceAfter,R]

/-! Use the OLD gates to decode the final token writes of the whole
work row. The raw lifting below proves equality of the actual POST
gates to these old gates, using earned cache and its closure. -/

private def afterL (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j : Fin 3) : Tok :=
  ReportByteRows.decode p (rankGate p hu u j)
    (resetTokenRead p ((row p (hu,hv) (u,v)).1.apply u) j)

private def afterR (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (k : Fin 3) : Tok :=
  ReportByteRows.decode p (rankGate p hv v k)
    (resetTokenRead p ((row p (hu,hv) (u,v)).2.apply v) k)

private def PairPays (p : Params) (hu hv : Bool) (u v : BitVec p.w)
    (j k : Fin 3) : Prop :=
  rankReady p hu u j=true ∨
  ((publicationToken p hu u j).tag≠2 ∧ (publicationToken p hv v k).tag=3) ∨
  ((publicationToken p hu u j).tag=1 ∧ (publicationToken p hv v k).tag=0) ∨
  RacePays p 3 (rankGate p hu u j) (publicationToken p hu u j) ∨
  RacePays p 2 (rankGate p hv v k) (publicationToken p hv v k)

private def EndPays (p : Params) (hu : Bool) (u : BitVec p.w) (j : Fin 3) : Prop :=
  rankReady p hu u j=true ∨ (publicationToken p hu u j).tag=1 ∨
    RacePays p 3 (rankGate p hu u j) (publicationToken p hu u j)

/-- All internal old-pair cases, both endpoint outputs. The first
    alternative is an individual frame/nonincrease. The second
    alternative pays the pair sum, not both individual slots. -/
private theorem local_pair (p : Params) (L g i : Nat) (I : i+1<L)
    (hu hv : Bool) (u v : BitVec p.w) (j k : Fin 3)
    (D : reset0Destination hv j=some k)
    (GL : rankGate p hu u j=true↔i=g)
    (GR : rankGate p hv v k=true↔i+1=g) :
    let a := W L g i (publicationToken p hu u j)
    let b := W L g (i+1) (publicationToken p hv v k)
    let a' := W L g i (afterL p hu hv u v j)
    let b' := W L g (i+1) (afterR p hu hv u v k)
    ((a'≤a ∧ b'≤b) ∨ a'+b'<a+b) ∧
      (PairPays p hu hv u v j k→a'+b'<a+b) := by
  dsimp only
  let t := publicationToken p hu u j
  let z := publicationToken p hv v k
  let t' := afterL p hu hv u v j
  let z' := afterR p hu hv u v k
  let S := W L g i t'+W L g (i+1) z'<W L g i t+W L g (i+1) z
  change ((W L g i t'≤W L g i t ∧ W L g (i+1) z'≤W L g (i+1) z) ∨ S) ∧
    (PairPays p hu hv u v j k→S)
  by_cases R : rankReady p hu u j=true
  · have F : t.tag=2 := (rankReady_iff p hu u j).mp R |>.1
    have E : t'=MISByteCodec.T := by
      unfold t' afterL
      rw [rank_hop_left p hu hv u v j k D R,drain_decode_T]
    have P : S := by
      dsimp [S,W]
      rw [E,label_canonT]
      exact hop_any I t z z' F
    exact ⟨.inr P,fun _=>P⟩
  have NR : rankReady p hu u j=false := Bool.eq_false_iff.mpr R
  by_cases Rev : t.tag≠2 ∧ z.tag=3
  · obtain ⟨A,B⟩ := rank_reverse_pair p hu hv u v j k D Rev.1 Rev.2
    have Q : t'.tag=3 := by
      unfold t' afterL
      rw [A,rankToken_wire,rank_reverse_tag]
      exact Rev.2
    have E : z'=MISByteCodec.E := by
      unfold z' afterR
      rw [B,drain_decode_E]
    have P : S := by
      dsimp [S,W]
      rw [label_D _ Q,E,label_canonE,label_D z Rev.2]
      exact reverse_strict L g i (label t)
    exact ⟨.inr P,fun _=>P⟩
  have IdleR : t.tag=2 ∨ z.tag≠3 := by
    by_cases A : t.tag=2
    · exact .inl A
    · exact .inr (fun B=>Rev ⟨A,B⟩)
  have ER : z'=ReportByteRows.decode p (rankGate p hv v k)
      (rankNormWire p 2 (rankGate p hv v k) (resetTokenRead p v k)) := by
    unfold z' afterR
    rw [rank_idle_right p hu hv u v j k D NR IdleR]
  have WR : W L g (i+1) z'≤W L g (i+1) z := by
    rw [ER,show z=ReportByteRows.decode p (rankGate p hv v k)
      (resetTokenRead p v k) from rankToken_wire p hv v k]
    exact norm_le p L g (i+1) _ _ 2 (.inl rfl) GR
  by_cases Clear : t.tag=1 ∧ z.tag=0
  · have EL : t'=MISByteCodec.E := by
      unfold t' afterL
      rw [rank_clear_left p hu hv u v j Clear.1 (.inr ⟨k,D,Clear.2⟩),
        drain_decode_E]
    have WL : W L g i t'<W L g i t := by
      unfold W
      rw [EL,label_canonE,label_T t Clear.1]
      exact trail_clear_strict L g i
    have P : S := by dsimp [S]; omega
    exact ⟨.inr P,fun _=>P⟩
  have IdleL : t.tag=2 ∨
      (t.tag≠2 ∧ match reset0Destination hv j with
      | none => t.tag≠1
      | some r => (publicationToken p hv v r).tag≠3 ∧
          ¬(t.tag=1 ∧ (publicationToken p hv v r).tag=0)) := by
    by_cases T0 : t.tag=2
    · exact .inl T0
    · refine .inr ⟨T0,?_⟩
      rw [D]
      exact ⟨fun H=>Rev ⟨T0,H⟩,Clear⟩
  have EL : t'=ReportByteRows.decode p (rankGate p hu u j)
      (rankNormWire p 3 (rankGate p hu u j) (resetTokenRead p u j)) := by
    unfold t' afterL
    rw [rank_idle_left p hu hv u v j NR IdleL]
  have WL : W L g i t'≤W L g i t := by
    rw [EL,show t=ReportByteRows.decode p (rankGate p hu u j)
      (resetTokenRead p u j) from rankToken_wire p hu u j]
    exact norm_le p L g i _ _ 3 (.inr rfl) GL
  refine ⟨.inl ⟨WL,WR⟩,?_⟩
  intro P
  rcases P with P|P|P|P|P
  · exact False.elim (R P)
  · exact False.elim (Rev P)
  · exact False.elim (Clear P)
  · have V : W L g i t'<W L g i t := by
      rw [EL,show t=ReportByteRows.decode p (rankGate p hu u j)
        (resetTokenRead p u j) from rankToken_wire p hu u j]
      exact norm_pays p L g i _ _ 3 (.inr rfl) GL P
    dsimp [S]
    omega
  · have V : W L g (i+1) z'<W L g (i+1) z := by
      rw [ER,show z=ReportByteRows.decode p (rankGate p hv v k)
        (resetTokenRead p v k) from rankToken_wire p hv v k]
      exact norm_pays p L g (i+1) _ _ 2 (.inl rfl) GR P
    dsimp [S]
    omega

private theorem local_end (p : Params) (L g i : Nat) (I : i<L)
    (hu hv : Bool) (u v : BitVec p.w) (j : Fin 3)
    (D : reset0Destination hv j=none)
    (G : rankGate p hu u j=true↔i=g) :
    W L g i (afterL p hu hv u v j)≤W L g i (publicationToken p hu u j) ∧
      (EndPays p hu u j→
        W L g i (afterL p hu hv u v j)<W L g i (publicationToken p hu u j)) := by
  let t := publicationToken p hu u j
  let t' := afterL p hu hv u v j
  change W L g i t'≤W L g i t ∧ (EndPays p hu u j→W L g i t'<W L g i t)
  by_cases R : rankReady p hu u j=true
  · have T0 : t.tag=2 := (rankReady_iff p hu u j).mp R |>.1
    have T1 : t'.tag=3 := rank_turn_tag p hu hv u v j D R _
    have P : W L g i t'<W L g i t := by
      unfold W
      rw [label_D t' T1,label_F t T0]
      exact terminal_strict I _ _
    exact ⟨Nat.le_of_lt P,fun _=>P⟩
  have NR : rankReady p hu u j=false := Bool.eq_false_iff.mpr R
  by_cases T0 : t.tag=1
  · have E : t'=MISByteCodec.E := by
      unfold t' afterL
      rw [rank_clear_left p hu hv u v j T0 (.inl D),drain_decode_E]
    have P : W L g i t'<W L g i t := by
      unfold W
      rw [E,label_canonE,label_T t T0]
      exact trail_clear_strict L g i
    exact ⟨Nat.le_of_lt P,fun _=>P⟩
  have H : t.tag=2 ∨ (t.tag≠2 ∧
      match reset0Destination hv j with
      | none => t.tag≠1
      | some r => (publicationToken p hv v r).tag≠3 ∧
          ¬(t.tag=1 ∧ (publicationToken p hv v r).tag=0)) := by
    by_cases A : t.tag=2
    · exact .inl A
    · exact .inr ⟨A,by rw [D]; exact T0⟩
  have E : t'=ReportByteRows.decode p (rankGate p hu u j)
      (rankNormWire p 3 (rankGate p hu u j) (resetTokenRead p u j)) := by
    unfold t' afterL
    rw [rank_idle_left p hu hv u v j NR H]
  have V : t=ReportByteRows.decode p (rankGate p hu u j) (resetTokenRead p u j) :=
    rankToken_wire p hu u j
  rw [E,V]
  refine ⟨norm_le p L g i _ _ 3 (.inr rfl) G,?_⟩
  intro P
  rcases P with P|P|P
  · exact False.elim (R P)
  · exact False.elim (T0 P)
  · exact norm_pays p L g i _ _ 3 (.inr rfl) G P

/-- The concrete paid-event disjunction on the old owner link. The
    first clause has priority over all following clauses. -/
private def pairEvent (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) : Prop :=
  let e := out C i
  PairPays (params sheet s) (h e) (h (rightNeighbor e))
    (bytesL sheet x e) (bytesR sheet x e) (C.route.port i) (C.route.port (i+1))

private def endEvent (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) : Prop :=
  EndPays (params sheet s) (h (out C i)) (bytesL sheet x (out C i)) (C.route.port i)

private def readyAt (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat) : Bool :=
  rankReady (params sheet s) (h (out C i)) (bytesL sheet x (out C i)) (C.route.port i)

private def raceAt (sheet : Sheet) (C : Chart h) (x : Raw s n) (i side : Nat) : Prop :=
  RacePays (params sheet s) side (chartGate sheet C x i)
    (ReportOwnerResetDrain.tok sheet C x i)

private theorem pairEvent_ready (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (R : readyAt sheet C x i=true) : pairEvent sheet C x i := .inl R

private theorem pairEvent_reverse (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (A : (ReportOwnerResetDrain.tok sheet C x i).tag≠2)
    (B : (ReportOwnerResetDrain.tok sheet C x (i+1)).tag=3) :
    pairEvent sheet C x i := .inr (.inl ⟨A,B⟩)

private theorem pairEvent_clear (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (A : (ReportOwnerResetDrain.tok sheet C x i).tag=1)
    (B : (ReportOwnerResetDrain.tok sheet C x (i+1)).tag=0) :
    pairEvent sheet C x i := .inr (.inr (.inl ⟨A,B⟩))

private theorem pairEvent_raceL (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (R : raceAt sheet C x i 3) : pairEvent sheet C x i :=
  .inr (.inr (.inr (.inl R)))

private theorem pairEvent_raceR (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (R : raceAt sheet C x (i+1) 2) : pairEvent sheet C x i :=
  .inr (.inr (.inr (.inr R)))

private theorem endEvent_ready (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (R : readyAt sheet C x i=true) : endEvent sheet C x i := .inl R
private theorem endEvent_clear (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (R : (ReportOwnerResetDrain.tok sheet C x i).tag=1) : endEvent sheet C x i :=
  .inr (.inl R)
private theorem endEvent_race (sheet : Sheet) (C : Chart h) (x : Raw s n) (i : Nat)
    (R : raceAt sheet C x i 3) : endEvent sheet C x i := .inr (.inr R)

/-- Internal two-slot local comparison transferred through actual raw
    pair including the high cache publisher on both post endpoints. -/
private theorem raw_internal (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (i : Nat) (I : i+1<C.L) :
    (Weak sheet C x (rawNext s x (out C i)) ∨ Paid sheet C x (rawNext s x (out C i))) ∧
      (pairEvent sheet C x i→Paid sheet C x (rawNext s x (out C i))) := by
  let e := out C i
  let y := rawNext s x e
  let p := params sheet s
  let j := C.route.port i
  let k := C.route.port (i+1)
  let a : Fin C.L := ⟨i,by omega⟩
  let b : Fin C.L := ⟨i+1,I⟩
  have CF := ReportOwnerResetDrain.cached_fibre sheet N hh Q F
  have Y : ReportOwnerResetDrain.Cached sheet hh Q y := CF.closed x e X
  have G := gate_geometry (s:=s) sheet C hh B (Q:=Q)
  have GL : rankGate p (h e) (bytesL sheet x e) j=true↔i=C.a+2 :=
    G.2.2 x X i a.isLt
  have GR : rankGate p (h (rightNeighbor e)) (bytesR sheet x e) k=true↔i+1=C.a+2 :=
    G.2.2 x X (i+1) I
  have P := raw_pair_wire sheet C x N (CF.mask x X) i
  have TL : ReportOwnerResetDrain.tok sheet C y i=
      afterL p (h e) (h (rightNeighbor e)) (bytesL sheet x e) (bytesR sheet x e) j := by
    rw [tok_wire,gate_frame sheet C hh B x y X Y i a.isLt,P.1]
    rfl
  have TR : ReportOwnerResetDrain.tok sheet C y (i+1)=
      afterR p (h e) (h (rightNeighbor e)) (bytesL sheet x e) (bytesR sheet x e) k := by
    rw [tok_wire,gate_frame sheet C hh B x y X Y (i+1) I,P.2]
    rfl
  have V := local_pair p C.L (C.a+2) i I (h e) (h (rightNeighbor e))
    (bytesL sheet x e) (bytesR sheet x e) j k (internal_dest C i I) GL GR
  have K :
      ((weight sheet C y a≤weight sheet C x a ∧ weight sheet C y b≤weight sheet C x b) ∨
        weight sheet C y a+weight sheet C y b<weight sheet C x a+weight sheet C x b) ∧
      (pairEvent sheet C x i→
        weight sheet C y a+weight sheet C y b<weight sheet C x a+weight sheet C x b) := by
    -- CHECK: weight from ReportOwnerResetDrain.lean:129–131.
    unfold weight
    change ((W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C y i)≤
      W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C x i) ∧
      W C.L (C.a+2) (i+1) (ReportOwnerResetDrain.tok sheet C y (i+1))≤
      W C.L (C.a+2) (i+1) (ReportOwnerResetDrain.tok sheet C x (i+1))) ∨
      W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C y i)+
      W C.L (C.a+2) (i+1) (ReportOwnerResetDrain.tok sheet C y (i+1))<
      W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C x i)+
      W C.L (C.a+2) (i+1) (ReportOwnerResetDrain.tok sheet C x (i+1))) ∧
      (pairEvent sheet C x i→_)
    rw [TL,TR]
    exact V
  exact raw_internal_of_weights sheet C hh B F N x X i I (pairEvent sheet C x i) K

/-- A terminal edge has only one occurrence of this owner chart.
    Its actual right endpoint belongs to a different owner lane. -/
private theorem raw_end (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (i : Nat) (I : i+1=C.L) :
    Weak sheet C x (rawNext s x (out C i)) ∧
      (endEvent sheet C x i→Paid sheet C x (rawNext s x (out C i))) := by
  let e := out C i
  let y := rawNext s x e
  let p := params sheet s
  let j := C.route.port i
  let a : Fin C.L := ⟨i,by omega⟩
  have CF := ReportOwnerResetDrain.cached_fibre sheet N hh Q F
  have Y : ReportOwnerResetDrain.Cached sheet hh Q y := CF.closed x e X
  have G := gate_geometry (s:=s) sheet C hh B (Q:=Q)
  have GL : rankGate p (h e) (bytesL sheet x e) j=true↔i=C.a+2 :=
    G.2.2 x X i a.isLt
  have P := raw_pair_wire sheet C x N (CF.mask x X) i
  have TL : ReportOwnerResetDrain.tok sheet C y i=
      afterL p (h e) (h (rightNeighbor e)) (bytesL sheet x e) (bytesR sheet x e) j := by
    rw [tok_wire,gate_frame sheet C hh B x y X Y i a.isLt,P.1]
    rfl
  have V := local_end p C.L (C.a+2) i a.isLt (h e) (h (rightNeighbor e))
    (bytesL sheet x e) (bytesR sheet x e) j (end_dest C i I) GL
  have K : weight sheet C y a≤weight sheet C x a ∧
      (endEvent sheet C x i→weight sheet C y a<weight sheet C x a) := by
    unfold weight
    change W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C y i)≤
      W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C x i) ∧
      (endEvent sheet C x i→
        W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C y i)<
        W C.L (C.a+2) i (ReportOwnerResetDrain.tok sheet C x i))
    rw [TL]
    exact V
  exact raw_end_of_weights sheet C hh B F N x X i I (endEvent sheet C x i) K

/-- All nondoor marks: either an actual outgoing chart edge, or an
    actual remote mark. The incoming edge of an interior occurrence
    is precisely the preceding outgoing chart edge. -/
theorem nondoor_casesAt (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (e : Fin n) (E : e≠door C) :
    Weak sheet C x (rawNext s x e) ∨ Paid sheet C x (rawNext s x e) := by
  classical
  by_cases H : ∃ i,i<C.L ∧ e=out C i
  · obtain ⟨i,I,rfl⟩ := H
    by_cases J : i+1<C.L
    · exact (raw_internal sheet C hh B F N x X i J).1
    · exact .inl (raw_end sheet C hh B F N x X i (by omega)).1
  · have CF := ReportOwnerResetDrain.cached_fibre sheet N hh Q F
    have Y := CF.closed x e X
    refine .inl ⟨debt_frame sheet C x e N (CF.mask x X) E,?_⟩
    intro i
    exact Nat.le_of_eq (weight_frame sheet C hh B x (rawNext s x e) X Y i
      (raw_off_frame sheet C x e E (fun j J A=>H ⟨j,J,A⟩) i.val i.isLt))

/-- Uniform helper for a ready outgoing mark or the progressing
    outgoing gate normalization, including the terminal case. -/
private theorem outgoing_paid (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (i : Nat) (I : i<C.L)
    (R : readyAt sheet C x i=true ∨ raceAt sheet C x i 3) :
    Paid sheet C x (rawNext s x (out C i)) := by
  by_cases J : i+1<C.L
  · apply (raw_internal sheet C hh B F N x X i J).2
    rcases R with R|R
    · exact pairEvent_ready sheet C x i R
    · exact pairEvent_raceL sheet C x i R
  · apply (raw_end sheet C hh B F N x X i (by omega)).2
    rcases R with R|R
    · exact endEvent_ready sheet C x i R
    · exact endEvent_race sheet C x i R

theorem nondoor_front (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (i : Nat) (I : i<C.L) (T0 : (ReportOwnerResetDrain.tok sheet C x i).tag=2) :
    ∃ e : Fin n,(e=out C i ∨ e=inEdge C i) ∧ e≠door C ∧
      PaidMark sheet C x e := by
  by_cases R : readyAt sheet C x i=true
  · exact ⟨out C i,.inl rfl,Ne.symm (ReportChartPartition.door_not_outgoing C i I),
      .inr (outgoing_paid sheet C hh B F N x X i I (.inl R))⟩
  have NR : readyAt sheet C x i=false := Bool.eq_false_iff.mpr R
  obtain ⟨H,G,L,U⟩ := rank_parked_shape (params sheet s) (h (out C i))
    (bytesL sheet x (out C i)) (C.route.port i) T0 NR
  change healthyAdmit (params sheet s) (ReportOwnerResetDrain.tok sheet C x i) at H
  change chartGate sheet C x i=true at G
  have A := gate_geometry (s:=s) sheet C hh B (Q:=Q)
  have Gi : i=C.a+2 := (A.2.2 x X i I).mp G
  have ip : 0<i := by omega
  have Rs : (ReportOwnerResetDrain.tok sheet C x i).race=1 ∨
      (ReportOwnerResetDrain.tok sheet C x i).race=2 ∨
      (ReportOwnerResetDrain.tok sheet C x i).race=3 := by
    change 1≤(ReportOwnerResetDrain.tok sheet C x i).race at L
    change (ReportOwnerResetDrain.tok sheet C x i).race<4 at U
    omega
  by_cases P : (ReportOwnerResetDrain.tok sheet C x i).race=3
  · let a := i-1
    have J : a+1=i := by dsimp [a]; omega
    have R2 : raceAt sheet C x (a+1) 2 := by
      rw [J]
      exact ⟨H,G,.inr P⟩
    have Pay := (raw_internal sheet C hh B F N x X a (by omega)).2
      (pairEvent_raceR sheet C x a R2)
    refine ⟨out C a,.inr ?_,Ne.symm (ReportChartPartition.door_not_outgoing C a (by omega)),
      .inr Pay⟩
    simp [inEdge,show i≠0 by omega,a]
  · have R3 : raceAt sheet C x i 3 := by
      refine ⟨H,G,?_⟩
      rcases Rs with R|R|R
      · exact .inl R
      · exact .inr R
      · exact False.elim (P R)
    exact ⟨out C i,.inl rfl,Ne.symm (ReportChartPartition.door_not_outgoing C i I),
      .inr (outgoing_paid sheet C hh B F N x X i I (.inr R3))⟩

theorem nondoor_reply (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (NF : ∀ i,i<C.L→(ReportOwnerResetDrain.tok sheet C x i).tag≠2)
    (i : Nat) (I : i<C.L) (P : 0<i)
    (D : (ReportOwnerResetDrain.tok sheet C x i).tag=3) :
    PaidMark sheet C x (inEdge C i) := by
  let a := i-1
  have J : a+1=i := by dsimp [a]; omega
  have Pay := (raw_internal sheet C hh B F N x X a (by omega)).2
    (pairEvent_reverse sheet C x a (NF a (by omega)) (by rw [J]; exact D))
  exact .inr (by simpa [inEdge,show i≠0 by omega,a] using Pay)

theorem nondoor_trail (sheet : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (B : GapInput h) {Q : Raw s n→Prop}
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q)
    (N : 1<n) (x : Raw s n) (X : ReportOwnerResetDrain.Cached sheet hh Q x)
    (NF : ∀ i,i<C.L→(ReportOwnerResetDrain.tok sheet C x i).tag≠2)
    (ND : ∀ i,i<C.L→(ReportOwnerResetDrain.tok sheet C x i).tag≠3)
    (i : Nat) (I : i<C.L) (T0 : (ReportOwnerResetDrain.tok sheet C x i).tag=1)
    (NT : ∀ j,j<C.L→i<j→(ReportOwnerResetDrain.tok sheet C x j).tag≠1) :
    PaidMark sheet C x (out C i) := by
  by_cases J : i+1<C.L
  · have LT : (ReportOwnerResetDrain.tok sheet C x (i+1)).tag<4 := by
      rw [tok_wire]
      exact rank_tag_lt _ _ _
    have E : (ReportOwnerResetDrain.tok sheet C x (i+1)).tag=0 := by
      have A := NF (i+1) J
      have D := ND (i+1) J
      have T := NT (i+1) J (by omega)
      omega
    exact .inr ((raw_internal sheet C hh B F N x X i J).2
      (pairEvent_clear sheet C x i T0 E))
  · exact .inr ((raw_end sheet C hh B F N x X i (by omega)).2
      (endEvent_clear sheet C x i T0))

/-- Exactly the three unresolved source-door obligations are the
    separate source-door cases. No non-door hypothesis remains. -/
structure DoorCases (sheet : Sheet) (C : Chart h) (Q : Raw s n→Prop) : Prop where
  casesAt : ∀ x,Q x→¬Launch sheet C x (door C)→
    Weak sheet C x (rawNext s x (door C)) ∨ Paid sheet C x (rawNext s x (door C))
  reply : ∀ x,Q x→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok sheet C x i).tag≠2)→
    (ReportOwnerResetDrain.tok sheet C x 0).tag=3→PaidMark sheet C x (door C)
  empty : ∀ x,Q x→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok sheet C x i).tag≠2)→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok sheet C x i).tag≠3)→
    (∀ i,i<C.L→(ReportOwnerResetDrain.tok sheet C x i).tag≠1)→
    PaidMark sheet C x (door C)

/-- Complete RowCases assembly. All literal non-door cases and all
    F/trail nominations above are proved, not fields of DoorCases. -/
theorem rowCases (sheet : Sheet) (C : Chart h) (hh : ∃ i,h i=true)
    (B : GapInput h) (Q : Raw s n→Prop)
    (F : ReportOwnerResetDrain.Fibre (h:=h) sheet Q) (N : 1<n)
    (D : DoorCases sheet C (ReportOwnerResetDrain.Cached sheet hh Q)) :
    RowCases sheet C (ReportOwnerResetDrain.Cached sheet hh Q) where
  casesAt := by
    intro x e X L
    by_cases E : e=door C
    · subst e
      exact D.casesAt x X L
    · exact nondoor_casesAt sheet C hh B F N x X e E
  front := by
    intro x X i I H
    obtain ⟨e,E,_,P⟩ := nondoor_front sheet C hh B F N x X i I H
    exact ⟨e,E,P⟩
  reply := by
    intro x X NF i I T
    by_cases Z : i=0
    · subst i
      simpa [inEdge] using D.reply x X NF T
    · exact nondoor_reply sheet C hh B F N x X NF i I (by omega) T
  trail := by
    intro x X NF ND i I T NT
    exact nondoor_trail sheet C hh B F N x X NF ND i I T NT
  empty := D.empty

#print axioms nondoor_casesAt
#print axioms nondoor_front
#print axioms nondoor_reply
#print axioms nondoor_trail
#print axioms rowCases
end L4.ReportPrelaunchK1
namespace L4.ReportPrelaunchK1
open AllSizeProtocol PhysicalCustody ReportResetRawHooks
open ShortResetCycle ShortResetChart ReportResetBarrier ReportPrelaunchClock
open ReportByteRows ReportPrelaunchK1Geometry ReportOwnerResetDrain
variable {s n : Nat} {h : Fin n→Bool} {Q : Raw s n→Prop}

noncomputable def frontLabel (d : Sheet) (C : Chart h) (x : Raw s n) (k : Nat) : Fin n := by
  classical
  exact if healthyAdmit (params d s) (tok d C x k) ∧
      chartGate d C x k=true ∧ (tok d C x k).race=3
    then inEdge C k else out C k

theorem frontLabel_paid (d : Sheet) (C : Chart h)
    (hh : ∃ i,h i=true) (G : GapInput h) (F : Fibre (h:=h) d Q)
    (N : 1<n) (x : Raw s n) (X : Cached d hh Q x)
    (k : Nat) (K : k<C.L) (T : (tok d C x k).tag=2) :
    PaidMark d C x (frontLabel d C x k) := by
  classical
  unfold frontLabel
  by_cases B : healthyAdmit (params d s) (tok d C x k) ∧
      chartGate d C x k=true ∧ (tok d C x k).race=3
  · rw [if_pos B]
    have A := (gate_geometry d C hh G (Q:=Q)).2.2 x X k K
    have E := A.mp B.2.1
    have P : 0<k := by omega
    let j := k-1
    have J : j+1=k := by dsimp [j]; omega
    have R : raceAt d C x (j+1) 2 := by
      rw [J]
      exact ⟨B.1,B.2.1,.inr B.2.2⟩
    have H := (raw_internal d C hh G F N x X j (by omega)).2
      (pairEvent_raceR d C x j R)
    exact .inr (by simpa [inEdge,show k≠0 by omega,j] using H)
  · rw [if_neg B]
    apply Or.inr
    apply outgoing_paid d C hh G F N x X k K
    by_cases R : readyAt d C x k=true
    · exact .inl R
    · have NR := Bool.eq_false_iff.mpr R
      obtain ⟨H,A,L,U⟩ := rank_parked_shape (params d s) (h (out C k))
        (bytesL d x (out C k)) (C.route.port k) T NR
      change healthyAdmit (params d s) (tok d C x k) at H
      change chartGate d C x k=true at A
      change 1≤(tok d C x k).race at L
      change (tok d C x k).race<4 at U
      have R3 : (tok d C x k).race≠3 := fun E=>B ⟨H,A,E⟩
      exact .inr ⟨H,A,by simp; omega⟩

theorem frontLabel_frame (d : Sheet) (C : Chart h) (x y : Raw s n) (k : Nat)
    (T : tok d C y k=tok d C x k)
    (A : chartGate d C y k=chartGate d C x k) :
    frontLabel d C y k=frontLabel d C x k := by
  classical
  simp only [frontLabel,T,A]

#print axioms frontLabel_paid
#print axioms frontLabel_frame
end L4.ReportPrelaunchK1

