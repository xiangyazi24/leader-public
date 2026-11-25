import Leader.L4.WindowOwnership
import Leader.L4.WindowRosterTrace

namespace L4.WindowProgressNormal
open SevenTagCharge WindowLocal WindowOwnership WindowRoster

/-- A continuing owned target was not already a living original slot. -/
def NoLivingTarget {p c n : Nat} {z : Ledger p c n} {g : List (Fin n)}
    (P : Progress z g) : Prop :=
  ∀ a, P.target=some a → ∀ s, z.slots s=some a →
    (z.config (rightNeighbor s)).leader=false

theorem skip_none_quiet {p c n : Nat} {z : Ledger p c n} {g : List (Fin n)}
    (P : Progress z g) (h : P.skipOnce=none) : NoLivingTarget P := by
  intro a ha s hs
  obtain ⟨hb,rest,hR⟩ := P.target_head a ha
  apply Bool.eq_false_iff.mpr
  intro hL
  have ex : ∃ t, TaggedLeader z t a := ⟨s,hs,hL⟩
  unfold Progress.skipOnce at h
  split at h
  · split at h
    · rename_i E
      rw [hR] at E
      contradiction
    · rename_i b xs E
      have eq : a=b := (List.cons.inj (hR.symm.trans E)).1
      subst b
      simp [ex] at h
  · contradiction

theorem skip_some_shape {p c n : Nat} {z : Ledger p c n} {g : List (Fin n)}
    (P R : Progress z g) (h : P.skipOnce=some R) :
    R.before=P.before ∧ R.cert.length=P.cert.length+1 := by
  unfold Progress.skipOnce at h
  split at h
  · split at h
    · contradiction
    · split at h
      · injection h with E
        subst R
        simp [Progress.attachLiving]
      · contradiction
  · contradiction

theorem normalize_before {p c n : Nat} {z : Ledger p c n} {g : List (Fin n)}
    (P : Progress z g) : P.normalize.before=P.before := by
  unfold Progress.normalize
  split
  · rfl
  · rename_i R hr
    cases he : R.skipOnce with
    | none => simpa [he] using (skip_some_shape P R hr).1
    | some S => simpa [he] using (skip_some_shape R S he).1.trans (skip_some_shape P R hr).1

theorem normalize_quiet {p c n : Nat} {z : Ledger p c n} {g : List (Fin n)}
    (P : Progress z g) : NoLivingTarget P.normalize := by
  unfold Progress.normalize
  split
  · exact skip_none_quiet P (by assumption)
  · rename_i R hr
    cases he : R.skipOnce with
    | none => simpa [he] using skip_none_quiet R he
    | some S =>
      simp only [Option.getD_some]
      intro a ha
      have hs := (skip_some_shape R S he).2
      have hr := (skip_some_shape P R hr).2
      have hb := (S.target_head a ha).1
      have hp := P.positive
      omega

theorem extend_before {p c n : Nat} {z : Ledger p c n} {x : Config p c n}
    {g : List (Fin n)} (P : Progress z g) (hn : 4≤n) (V : Valid z x)
    (e a pos : Fin n) (hr : route g P.cert P.target z e=.targetBirth a pos) :
    (P.extend hn V e a pos hr).before=P.before := by
  have ht := (birth_inv z g P.cert P.target e a pos hr).2.2.1
  obtain ⟨hb,rest,hR⟩ := P.target_head a ht
  cases P with
  | mk before cert after partition owned positive bounded =>
    dsimp only at hR
    subst after
    unfold Progress.extend
    dsimp only
    generalize Q : (Progress.target_head _ a ht) = W
    rcases W with ⟨bound, rest', eq⟩
    rfl

theorem handoff_before {p c n : Nat} {z : Ledger p c n} {x : Config p c n}
    {g : List (Fin n)} (A : EntryScope g) (hn : 4≤n) (V : Valid z x)
    (e a pos : Fin n) (hr : WindowA0Route.routeTwo g A.first A.second z e=.targetBirth a pos) :
    (A.handoff hn V e a pos hr).before=A.firstBefore ∨
      (A.handoff hn V e a pos hr).before=A.secondBefore := by
  have W := two_birth_inv z g A.first A.second e a pos hr
  let f (w : (a = A.first ∨ a = A.second) ∧ z.slots e = some a ∧
      birthAt z.config e = true ∧ pos = rightNeighbor e) : Progress (advance z e) g := by
    obtain ⟨_,hs,hb,_⟩ := w
    by_cases first : a=A.first
    · exact initialBirth hn V g A.firstBefore A.firstAfter e a (first.symm ▸ A.firstShape) hs hb
    · have second := W.1.resolve_left first
      exact initialBirth hn V g A.secondBefore A.secondAfter e a (second.symm ▸ A.secondShape) hs hb
  change (f (two_birth_inv z g A.first A.second e a pos hr)).before=A.firstBefore ∨
    (f (two_birth_inv z g A.first A.second e a pos hr)).before=A.secondBefore
  rw [show two_birth_inv z g A.first A.second e a pos hr =
      ⟨W.1,W.2.1,W.2.2.1,W.2.2.2⟩ from Subsingleton.elim _ _]
  dsimp [f]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem old_slot {p c n : Nat} (z : Ledger p c n) (e t a : Fin n)
    (h : (advance z e).slots t=some a) : ∃ s, z.slots s=some a := by
  change slotsStep z.config z.slots e t=some a at h
  unfold slotsStep at h
  split at h
  · unfold SevenTagCharge.move at h
    split at h
    · contradiction
    · split at h
      · cases E : z.slots t with
        | none => exact ⟨e,by simpa [E] using h⟩
        | some b => exact ⟨t,by simpa [E] using h⟩
      · exact ⟨t,h⟩
  · exact ⟨t,h⟩

private theorem keep_without_cert {p c n : Nat} (z : Ledger p c n) (g cert : List (Fin n))
    (target : Option (Fin n)) (e : Fin n) (hNo : selectedGroupLoss g z e=none)
    (hr : route g cert target z e=.keep) : route g [] target z e=.keep := by
  unfold route at hr ⊢
  rw [hNo] at hr ⊢
  dsimp only at hr ⊢
  split
  · rfl
  · rename_i b E
    rw [E] at hr
    dsimp only at hr
    unfold routeKnown at hr
    split at hr
    · contradiction
    · simpa only [routeKnown,List.contains_nil,Bool.and_false,Bool.false_eq_true,if_false] using hr

theorem keep_quiet {p c n : Nat} {z : Ledger p c n} {x : Config p c n}
    {g : List (Fin n)} (P : Progress z g) (hn : 4≤n) (V : Valid z x)
    (e : Fin n) (hr : route g P.cert P.target z e=.keep)
    (H : NoLivingTarget P) : NoLivingTarget (P.onKeep hn V e hr) := by
  intro a ha t ht
  change P.target=some a at ha
  obtain ⟨s,hs⟩ := old_slot z e t a ht
  have hG : a∈g := by
    obtain ⟨_,rest,hrest⟩ := P.target_head a ha
    simp [P.partition,hrest]
  have hNo : selectedGroupLoss g z e=none := by
    unfold route at hr
    split at hr
    · contradiction
    · assumption
  have hSmall := keep_without_cert z g P.cert (some a) e hNo
    ((congrArg (fun T => route g P.cert T z e) ha).symm.trans hr)
  have hNew := WindowFourHeadTrace.tracked_landing hn z g e s a V.covers hG hs hNo
  have hGhost := WindowA0Route.ghost_after_keep hn z g a s e V hG hs (H a ha s hs) hSmall
  by_cases he : e=s
  · subst s
    have A : (advance z e).slots (landingSlot z.config e)=some a := by
      simpa [landingSlot] using hNew
    have E := (valid_step hn z x e V).unique _ _ _ ht A
    rw [E]
    simpa only [advance,if_true,eq_self] using hGhost
  · have A : (advance z e).slots s=some a := by simpa [he] using hNew
    have E := (valid_step hn z x e V).unique _ _ _ ht A
    rw [E]
    simpa only [advance,he,if_false] using hGhost

/-- The original entry choice fixes the cert slice's left endpoint. -/
def Invariant {p c n : Nat} {x : Config p c n} {g : List (Fin n)} (A : EntryScope g)
    (q : WindowLatch.Cursor (Front x g) x g) : Prop :=
  match q with
  | .inr _ => True
  | .inl F => match F.mode with
    | .entry B => B=A
    | .owned P => (P.before=A.firstBefore ∨ P.before=A.secondBefore) ∧ NoLivingTarget P
    | .reward .. => True

private theorem invariant_init {p c n : Nat} {x : Config p c n} {g : List (Fin n)}
    (A : EntryScope g) (hq : QuietEntrance x) :
    Invariant A (.inl (Front.initial x hq A)) := by
  have K : ∀ P, startMode (z:=initial x) A=some P →
      P.before=A.firstBefore ∨ P.before=A.secondBefore := by
    intro P h
    unfold startMode at h
    split at h
    · injection h with E
      subst P
      exact Or.inl rfl
    · split at h
      · injection h with E
        subst P
        exact Or.inr rfl
      · contradiction
  cases E : startMode (z:=initial x) A with
  | none => simp [Front.initial,Invariant,E]
  | some P =>
    simp only [Front.initial,Invariant,E]
    exact ⟨by rw [normalize_before]; exact K P E,normalize_quiet P⟩

theorem invariant_step {p c n : Nat} {x : Config p c n} {g : List (Fin n)}
    (A : EntryScope g) (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (q : WindowLatch.Cursor (Front x g) x g) (e : Fin n)
    (H : Invariant A q) :
    Invariant A (WindowProtectedOuter.joinedNext
      (WindowLatch.front hn (WindowOwnership.decide hp hc hn)) q e) := by
  cases q with
  | inr q => trivial
  | inl F =>
    obtain ⟨z,V,Q,m⟩ := F
    cases m with
    | reward a h => trivial
    | entry B =>
      change B=A at H
      subst B
      unfold WindowProtectedOuter.joinedNext WindowLatch.front WindowOwnership.decide
      dsimp only
      split
      · rename_i s hE E
        split at E
        · injection E with Z
          subst s
          rfl
        · injection E with Z
          subst s
          trivial
        · rename_i a loc r
          injection E with Z
          subst s
          exact ⟨by rw [normalize_before]; exact handoff_before A hn V e a loc r,
            normalize_quiet _⟩
        · rename_i a loc r
          exact (no_entry_death z g A.first A.second e a loc r).elim
      · trivial
    | owned P =>
      change (P.before=A.firstBefore ∨ P.before=A.secondBefore) ∧ NoLivingTarget P at H
      unfold WindowProtectedOuter.joinedNext WindowLatch.front WindowOwnership.decide
      dsimp only
      split
      · rename_i s hE E
        split at E
        · rename_i r
          injection E with Z
          subst s
          exact ⟨H.1,keep_quiet P hn V e r H.2⟩
        · injection E with Z
          subst s
          trivial
        · rename_i a loc r
          injection E with Z
          subst s
          exact ⟨by rw [normalize_before,extend_before P hn V e a loc r]; exact H.1,
            normalize_quiet _⟩
        · contradiction
      · trivial

theorem fold_invariant {p c n : Nat} {x : Config p c n} {g : List (Fin n)}
    (A : EntryScope g) (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (hq : QuietEntrance x) (w : List (Fin n)) :
    Invariant A (fold hp hc hn hq A w) := by
  let f : WindowLatch.Cursor (Front x g) x g → Fin n →
      WindowLatch.Cursor (Front x g) x g := WindowProtectedOuter.joinedNext (WindowLatch.front hn (WindowOwnership.decide hp hc hn))
  have K (q : WindowLatch.Cursor (Front x g) x g) (h : Invariant A q) (u : List (Fin n)) :
      Invariant A (WindowLatch.replay f q u) := by
    induction u generalizing q with
    | nil => exact h
    | cons e u ih => exact ih (f q e) (invariant_step A hp hc hn q e h)
  exact K _ (invariant_init A hq) w

open WindowRosterTrace in
private theorem window_get {p c n : Nat} (x : Config p c n) (i : Fin (RankPhysical.rank x))
    (d : Nat) (h : d<(window7 (roster x) i).length) :
    (window7 (roster x) i)[d]=labels x i d := by
  simp [window7,labels,List.getElem_finRange]

/-- At an active singleton/pair, the actual named predecessor is among
the first four original slots, and the immediately following tag is a ghost. -/
theorem ordinary_cut_of_fold {p c n : Nat} {x : Config p c n}
    (hq : QuietEntrance x) (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (i : Fin (RankPhysical.rank x)) (h7 : 7≤RankPhysical.rank x)
    (A : EntryScope (window7 (roster x) i))
    (h1 : A.firstBefore.length=1) (h2 : A.secondBefore.length=2)
    (w : List (Fin n)) (F : Front x (window7 (roster x) i)) (P : Progress F.ledger _)
    (hF : fold hp hc hn hq A w=.inl F) (hP : F.mode=.owned P)
    (hsmall : P.cert.length<3)
    (hNo : hit F.ledger.losses (window7 (roster x) i)=false) :
    let d := P.before.length+P.cert.length-1
    let a := WindowRosterTrace.labels x i (d+1)
    let b := WindowRosterTrace.labels x i (d+2)
    let k := WindowRosterTrace.labels x i (d+3)
    d≤3 ∧ P.target=some a ∧ ∃ (s : Fin n) (q : WindowA0Push.State p c n), q.cursor.ledger=F.ledger ∧ q.terminal=false ∧
      WindowA0Push.ValidCut x (rightNeighbor s) P.cert a b k q := by
  let g := window7 (roster x) i
  let L := WindowRosterTrace.labels x i
  have hG : g.length=7 := by simp [g,window7]
  have H := fold_invariant A hp hc hn hq w
  rw [hF] at H
  simp only [Invariant,hP] at H
  have hb : P.before.length≤2 := by
    rcases H.1 with E|E <;> simp [E,h1,h2]
  have hpos := P.positive
  let d := P.before.length+P.cert.length-1
  have hd : d+3<7 := by dsimp [d]; omega
  have Hd : d+1=P.before.length+P.cert.length := by dsimp [d]; omega
  have hPart : g=P.before++P.cert++P.after := P.partition
  have hLen : (P.before++P.cert++P.after).length=7 := (congrArg List.length hPart).symm.trans hG
  have hA : 0<P.after.length := by
    have E := congrArg List.length hPart
    simp only [List.length_append,hG] at E
    omega
  obtain ⟨a,rest,hrest⟩ : ∃ a rest, P.after=a::rest := by
    cases E : P.after with
    | nil => simp [E] at hA
    | cons a rest => exact ⟨a,rest,rfl⟩
  have ht : P.target=some a := by simp [Progress.target,hsmall,hrest]
  have HD : ∀ (j : Nat) (hj : j<g.length) (hJ : j<(P.before++P.cert++P.after).length),
      g[j]= (P.before++P.cert++P.after)[j] := by
    intro j hj hJ
    have E := congrArg (fun t : List (Fin n) => t[j]?) hPart
    exact Option.some.inj (by simpa only [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hJ] using E)
  have idA : L (d+1)=a := by
    change WindowRosterTrace.labels x i (d+1)=a
    rw [←window_get x i (d+1) (by change d+1<g.length; omega),
      HD (d+1) (by omega) (by omega), List.getElem_append_right (by simp [Hd])]
    have idx : d + 1 - (P.before ++ P.cert).length = 0 := by simp [Hd]
    have E := congrArg (fun t : List (Fin n) => t[0]?) hrest
    have K : P.after[d+1-(P.before++P.cert).length]?=some a := by
      rw [idx,E]
      rfl
    rw [List.getElem?_eq_getElem (by omega)] at K
    exact Option.some.inj K
  have hC : L d∈P.cert := by
    change WindowRosterTrace.labels x i d∈P.cert
    rw [←window_get x i d (by change d<g.length; omega), HD d (by omega) (by omega)]
    rw [List.getElem_append_left (by simp; omega),List.getElem_append_right (by dsimp [d]; omega)]
    exact List.getElem_mem _
  have hL : F.ledger=observe (initial x) w := by
    have K := fold_ledger hp hc hn hq A w
    rw [hF] at K
    exact K
  obtain ⟨j,R⟩ := WindowRosterTrace.original_window x hn hq.1 hq.2.1 i h7 w
    (by rw [←hL]; exact hNo)
  let t := WindowRosterTrace.labels (observe (initial x) w).config j (d+1)
  have tAt : F.ledger.slots t=some (L (d+1)) := by rw [hL]; exact R ⟨d+1,by omega⟩
  have ht' : P.target=some (L (d+1)) := by rw [idA]; exact ht
  have hT := H.2 (L (d+1)) ht' t tAt
  let s := P.owned.slot (L d)
  have hS := P.owned.live (L d) hC
  have K := WindowRosterTrace.ordinary_push_window x hn hq.1 hq.2.1 i h7 w
    (by rw [←hL]; exact hNo) d hd P.cert hC s t
    (by rw [←hL]; exact hS) (by rw [←hL]; exact tAt) (by rw [←hL]; exact hT)
  obtain ⟨q,hqL,hqT,hqC⟩ := K
  exact ⟨by omega,ht',s,q,hqL.trans hL.symm,hqT,hqC⟩

/-- Exact original coordinates of every owned certified tag. -/
theorem owned_coordinates {p c n : Nat} {x : Config p c n}
    (hq : QuietEntrance x) (hp : 2≤p) (hc : 12≤c) (hn : 4≤n)
    (i : Fin (RankPhysical.rank x)) (A : EntryScope (window7 (roster x) i))
    (h1 : A.firstBefore.length=1) (h2 : A.secondBefore.length=2)
    (w : List (Fin n)) (F : Front x (window7 (roster x) i)) (P : Progress F.ledger _)
    (hF : fold hp hc hn hq A w=.inl F) (hP : F.mode=.owned P) :
    (P.before.length=1 ∨ P.before.length=2) ∧ NoLivingTarget P ∧
      ∀ (j : Nat) (hj : j<P.cert.length),
        P.cert[j]=WindowRosterTrace.labels x i (P.before.length+j) := by
  have H := fold_invariant A hp hc hn hq w
  rw [hF] at H
  simp only [Invariant,hP] at H
  have B : P.before.length=1 ∨ P.before.length=2 := by
    rcases H.1 with E|E
    · left; rwa [E]
    · right; rwa [E]
  refine ⟨B,H.2,?_⟩
  intro j hj
  let d := P.before.length+j
  let g := window7 (roster x) i
  have hG : g.length=7 := by simp [g,window7]
  have hJ : d < (P.before++P.cert++P.after).length := by
    simp only [List.length_append,d]
    omega
  have hg : d<g.length := by dsimp [g]; rw [P.partition]; exact hJ
  have hd : P.before.length≤d := by dsimp [d]; omega
  have hd' : d<(P.before++P.cert).length := by simp [d,hj]
  have D : d-P.before.length=j := by dsimp [d]; omega
  have E := congrArg (fun t : List (Fin n) => t[d]?) P.partition
  change g[d]? = (P.before++P.cert++P.after)[d]? at E
  have G := Option.some.inj (by
    simpa only [List.getElem?_eq_getElem hg,List.getElem?_eq_getElem hJ] using E)
  have S : (P.before++P.cert++P.after)[d]=P.cert[j] := by
    rw [List.getElem_append_left hd',List.getElem_append_right hd]
    have T := congrArg (fun (k : Nat) => P.cert[k]?) D
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj] at T
    exact Option.some.inj T
  exact S.symm.trans (G.symm.trans (window_get x i d hg))

end L4.WindowProgressNormal
