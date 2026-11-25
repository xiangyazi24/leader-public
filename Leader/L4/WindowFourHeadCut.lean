import Leader.L4.WindowFourHeadTrace
import Leader.L4.WindowScopedFourHead
import Leader.L4.RootedFresh

namespace L4.WindowFourHeadCut
open WindowFourHeadTrace SevenTagCharge RearFrontStock

private theorem pay_marks {p c n : Nat} (z : Ledger p c n) (e : Fin n)
    (mc : MCOV z.config)
    (hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true) : (z.config e).mark=true :=
  RearTrace.paid_was_marked mc e hp

/-- Lift coordinate of the retained W slot after the actual mark. -/
def indexAfter {p c n : Nat} (z : Ledger p c n) (e j w : Fin n) (b0 : Nat) : Nat :=
  if moves z e j then b0-1 else if moves z e w then b0+1 else b0

/-- Type-independent cut geometry. A living W keeps the same marked
position; its liveness is a separate physical fact, not part of the
geometric proof for the neighboring gaps. -/
structure Geometry {p c n : Nat} (z : Ledger p c n) (j w k a b cTag : Fin n)
    (b0 d : Nat) : Prop where
  jTag : z.slots j=some a
  wTag : z.slots w=some b
  kTag : z.slots k=some cTag
  wLift : liftedSite (rightNeighbor j) b0=w
  kLift : liftedSite (rightNeighbor j) d=k
  wBefore : b0<d
  width : d+1<n
  noOther : ∀ i, i<d → i≠b0 → (z.config (liftedSite (rightNeighbor j) i)).mark=false

theorem geomOf {p c n : Nat} {z : Ledger p c n} {j w k a b cTag : Fin n}
    {b0 d : Nat} (h : Cut z j w k a b cTag b0 d) :
    Geometry z j w k a b cTag b0 d :=
  ⟨h.jTag,h.wTag,h.kTag,h.wLift,h.kLift,h.wBefore,h.width,h.noOther⟩

theorem geom_step {p c n : Nat} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (e j w k a b cTag : Fin n)
    (b0 d : Nat) (h : Geometry z j w k a b cTag b0 d)
    (mc : MCOV z.config) (ht : Covers z.config z.slots)
    (hA : a∈g) (hB : b∈g) (hC : cTag∈g)
    (hKeep : WindowLocal.selectedGroupLoss g z e=none) :
    Geometry (advance z e) (landing z e j) (landing z e w) (landing z e k) a b cTag
      (indexAfter z e j w b0) (widthAfter z e j k d) := by
  classical
  let r := rightNeighbor j
  have db := h.wBefore
  have dn := h.width
  have jn : liftedSite r (n-1)=j := by
    apply FreshSeparation.succ_inj
    rw [←liftedSite_succ,show n-1+1=n by omega,liftedSite_full]
  have ij {i l : Nat} (hi : i<n) (hl : l<n)
      (he : liftedSite r i=liftedSite r l) : i=l := liftedSite_inj r hi hl he
  have wj : w≠j := fun he => by
    have H := ij (show b0<n by omega) (show n-1<n by omega)
      (h.wLift.trans (he.trans jn.symm))
    omega
  have kj : k≠j := fun he => by
    have H := ij (show d<n by omega) (show n-1<n by omega)
      (h.kLift.trans (he.trans jn.symm))
    omega
  have wk : w≠k := fun he => by
    have H := ij (show b0<n by omega) (show d<n by omega)
      (h.wLift.trans (he.trans h.kLift.symm))
    omega
  have tagJ := tracked_landing hn z g e j a ht hA h.jTag hKeep
  have tagW := tracked_landing hn z g e w b ht hB h.wTag hKeep
  have tagK := tracked_landing hn z g e k cTag ht hC h.kTag hKeep
  have geom : let j' := landing z e j
      let w' := landing z e w
      let k' := landing z e k
      let b' := indexAfter z e j w b0
      let d' := widthAfter z e j k d
      liftedSite (rightNeighbor j') b'=w' ∧ liftedSite (rightNeighbor j') d'=k' ∧
      b'<d' ∧ d'+1<n ∧
      (∀ i, i<d' → i≠b' → (step z.config e (liftedSite (rightNeighbor j') i)).mark=false) := by
    dsimp only
    by_cases hp : geometricPay (z.config e) (z.config (rightNeighbor e))=true
    · by_cases hj : e=j
      · subst e
        simp only [landing,widthAfter,indexAfter,moves,hp,and_true,Ne.symm wj,Ne.symm kj,
          ite_true,if_false]
        have hPos : 0<b0 := by
          have hh := (tracked_paid_transfer hn z g j a ht hA h.jTag hKeep hp).1
          by_cases hz : b0=0
          · have he : r=w := by simpa [hz,liftedSite_zero] using h.wLift
            change z.slots r=none at hh
            rw [he,h.wTag] at hh
            cases hh
          · omega
        refine ⟨?_,?_,by omega,by omega,?_⟩
        · rw [liftedSite_advance,show b0-1+1=b0 by omega]; exact h.wLift
        · rw [liftedSite_advance,show d-1+1=d by omega]; exact h.kLift
        · intro i hi hne
          change (step z.config j (liftedSite (rightNeighbor r) i)).mark=false
          rw [liftedSite_advance,covered_step_mark hn z.config mc j]
          have nn : liftedSite r (i+1)≠r := fun hh => by
            have H := ij (show i+1<n by omega) (show 0<n by omega)
              (hh.trans (liftedSite_zero r).symm)
            omega
          have hh := h.noOther (i+1) (by omega) (by omega)
          change (z.config (liftedSite r (i+1))).mark=false at hh
          by_cases he : liftedSite r (i+1)=j
          · simp [hp,he]
          · rw [if_pos hp,if_neg he]
            change (if liftedSite r (i+1)=r then true else _) = false
            rw [if_neg nn]
            exact hh
      · by_cases hw : e=w
        · subst e
          simp only [landing,widthAfter,indexAfter,moves,hp,and_true,wj,wk,ite_true,if_false]
          have hLt : b0+1<d := by
            have H := (tracked_paid_transfer hn z g w b ht hB h.wTag hKeep hp).1
            by_cases hEq : b0+1=d
            · have he : rightNeighbor w=k := by rw [← h.wLift,←liftedSite_succ,hEq,h.kLift]
              rw [he,h.kTag] at H
              cases H
            · omega
          refine ⟨?_,h.kLift,hLt,dn,?_⟩
          · rw [liftedSite_succ,h.wLift]
          · intro i hi hne
            change (step z.config w (liftedSite r i)).mark=false
            rw [covered_step_mark hn z.config mc w]
            have hNo : liftedSite r i≠rightNeighbor w := fun hh => by
              rw [←h.wLift,←liftedSite_succ] at hh
              exact hne (ij (by omega) (by omega) hh)
            by_cases he : i=b0
            · subst i
              rw [h.wLift]
              simp [hp]
            · by_cases he' : liftedSite r i=w
              · simp [hp,he']
              · simp [hp,he',hNo]
                exact h.noOther i hi he
        · by_cases hk : e=k
          · subst e
            simp only [landing,widthAfter,indexAfter,moves,hp,and_true,kj,Ne.symm wk,ite_true,if_false]
            have hLt : d+2<n := by
              have H := (tracked_paid_transfer hn z g k cTag ht hC h.kTag hKeep hp).1
              by_cases hEq : d+2=n
              · have he : rightNeighbor k=j := by rw [←h.kLift,←liftedSite_succ,show d+1=n-1 by omega,jn]
                rw [he,h.jTag] at H
                cases H
              · omega
            refine ⟨h.wLift,?_,by omega,by omega,?_⟩
            · rw [liftedSite_succ,h.kLift]
            · intro i hi hne
              change (step z.config k (liftedSite r i)).mark=false
              rw [covered_step_mark hn z.config mc k]
              have hNo : liftedSite r i≠rightNeighbor k := fun hh => by
                rw [←h.kLift,←liftedSite_succ] at hh
                have H := ij (show i<n by omega) (show d+1<n by omega) hh
                omega
              by_cases he : i=d
              · subst i
                rw [h.kLift]
                simp [hp]
              · by_cases he' : liftedSite r i=k
                · simp [hp,he']
                · simp [hp,he',hNo]
                  exact h.noOther i (by omega) hne
          · simp only [landing,widthAfter,indexAfter,moves,hp,and_true,hj,hw,hk,if_false]
            refine ⟨h.wLift,h.kLift,db,dn,?_⟩
            intro i hi hne
            change (step z.config e (liftedSite r i)).mark=false
            rw [covered_step_mark hn z.config mc e]
            have hNo : liftedSite r i≠rightNeighbor e := by
              intro he
              cases i with
              | zero =>
                have hH : r=rightNeighbor e := by simpa [liftedSite_zero] using he
                exact hj (FreshSeparation.succ_inj hH.symm)
              | succ i =>
                rw [liftedSite_succ] at he
                have hE : liftedSite r i=e := FreshSeparation.succ_inj he
                by_cases hh : i=b0
                · exact hw (hE.symm.trans (hh.symm ▸ h.wLift))
                · have hm := pay_marks z e mc hp
                  rw [←hE,h.noOther i (by omega) hh] at hm
                  cases hm
            by_cases he : liftedSite r i=e
            · simp [hp,he]
            · simp [hp,he,hNo]
              exact h.noOther i hi hne
    · have hf := Bool.eq_false_iff.mpr hp
      simp only [landing,widthAfter,indexAfter,moves,hf,Bool.false_eq_true,and_false,if_false]
      refine ⟨h.wLift,h.kLift,db,dn,?_⟩
      intro i hi hne
      simpa [covered_step_mark hn z.config mc e _,hf] using h.noOther i hi hne
  exact ⟨tagJ,tagW,tagK,geom.1,geom.2.1,geom.2.2.1,geom.2.2.2.1,geom.2.2.2.2⟩

theorem cut_step {p c n : Nat} (hn : 4≤n)
    (z : Ledger p c n) (g : List (Fin n)) (e j w k a b cTag : Fin n)
    (b0 d : Nat) (h : Cut z j w k a b cTag b0 d)
    (mc : MCOV z.config) (ht : Covers z.config z.slots)
    (hA : a∈g) (hB : b∈g) (hC : cTag∈g)
    (hKeep : WindowLocal.selectedGroupLoss g z e=none)
    (hJ : ((advance z e).config (rightNeighbor (landing z e j))).leader=false)
    (hW : ((advance z e).config (rightNeighbor (landing z e w))).leader=false) :
    Cut (advance z e) (landing z e j) (landing z e w) (landing z e k) a b cTag
      (indexAfter z e j w b0) (widthAfter z e j k d) := by
  have H := geom_step hn z g e j w k a b cTag b0 d (geomOf h) mc ht hA hB hC hKeep
  exact ⟨H.jTag,H.wTag,H.kTag,H.wLift,H.kLift,H.wBefore,H.width,hJ,hW,H.noOther⟩

structure Cursor (p c n : Nat) where
  ledger : Ledger p c n
  j : Fin n
  w : Fin n
  k : Fin n
  index : Nat
  width : Nat

def tick {p c n : Nat} (q : Cursor p c n) (e : Fin n) : Cursor p c n :=
  ⟨advance q.ledger e,landing q.ledger e q.j,landing q.ledger e q.w,landing q.ledger e q.k,
    indexAfter q.ledger e q.j q.w q.index,widthAfter q.ledger e q.j q.k q.width⟩

def wCharge {p c n : Nat} (q : Cursor p c n) (e : Fin n) : Nat :=
  if moves q.ledger e q.w then 1 else 0

def totalW {p c n : Nat} (q : Cursor p c n) : List (Fin n) → Nat
  | [] => 0
  | e::t => wCharge q e + totalW (tick q e) t

/-- These are actual tests of the retained premark and a completed
physical pair. No geometric condition is tested by this observer. -/
inductive GhostKeep {p c n : Nat} (g : List (Fin n)) :
    Cursor p c n → List (Fin n) → Prop where
  | nil {q} : GhostKeep g q []
  | cons {q e t} :
      WindowLocal.selectedGroupLoss g q.ledger e=none →
      ((tick q e).ledger.config (rightNeighbor (tick q e).j)).leader=false →
      ((tick q e).ledger.config (rightNeighbor (tick q e).w)).leader=false →
      GhostKeep g (tick q e) t → GhostKeep g q (e::t)

theorem ghostTrace_of_keep {p c n : Nat} (hn : 4≤n) (g : List (Fin n))
    (a b cTag : Fin n) (ha : a∈g) (hb : b∈g) (hc : cTag∈g)
    (x : Config p c n) (q : Cursor p c n) (w : List (Fin n))
    (hw : GhostKeep g q w) (hv : Valid q.ledger x)
    (hcut : Cut q.ledger q.j q.w q.k a b cTag q.index q.width) :
    GhostTrace g a b cTag q.ledger q.j q.w q.k q.width w (totalW q w) := by
  induction hw with
  | nil => exact .nil
  | @cons q e t hk hJ hW _ ih =>
    have hnext := cut_step hn q.ledger g e q.j q.w q.k a b cTag q.index q.width
      hcut hv.markCover hv.covers ha hb hc hk hJ hW
    exact .cons ⟨q.index,hcut⟩ hv.markCover hv.covers hk
      (ih (valid_step hn q.ledger x e hv) hnext)

theorem retained_ghost_progress_cap {p c n : Nat} (hn : 4≤n) (g : List (Fin n))
    (a b cTag : Fin n) (ha : a∈g) (hb : b∈g) (hc : cTag∈g)
    (x : Config p c n) (q : Cursor p c n) (w : List (Fin n))
    (hw : GhostKeep g q w) (hv : Valid q.ledger x)
    (hcut : Cut q.ledger q.j q.w q.k a b cTag q.index q.width) :
    totalW q w ≤ q.width+1 :=
  (ghostTrace_of_keep hn g a b cTag ha hb hc x q w hw hv hcut).count_le_size hn

/-- This is the continuing window prefix needed for the clock:
only J stays a ghost. W may be born and cannot later move or die. -/
inductive RetainedKeep {p c n : Nat} (g : List (Fin n)) :
    Cursor p c n → List (Fin n) → Prop where
  | nil {q} : RetainedKeep g q []
  | cons {q e t} :
    WindowLocal.selectedGroupLoss g q.ledger e=none →
    ((tick q e).ledger.config (rightNeighbor (tick q e).j)).leader=false →
    RetainedKeep g (tick q e) t → RetainedKeep g q (e::t)

open WindowFourHeadStock in
noncomputable def remaining {p c n : Nat} (q : Cursor p c n) : Int :=
  if (q.ledger.config (rightNeighbor q.w)).leader then 0
  else rearInventory q.ledger.config (rightNeighbor q.j) q.width

open WindowFourHeadStock in
private theorem remaining_nonneg {p c n : Nat} (q : Cursor p c n) : 0≤remaining q := by
  unfold remaining; split
  · decide
  · exact (rearInventory_interval _ _ _).1

open WindowFourHeadStock in
private theorem remaining_le_paid_row {p c n : Nat} (hn : 4≤n)
    (g : List (Fin n)) (a b cTag : Fin n) (ha : a∈g) (hb : b∈g) (hc : cTag∈g)
    (x : Config p c n) (q : Cursor p c n) (e : Fin n)
    (hv : Valid q.ledger x) (hq : QuietEntrance q.ledger.config)
    (hG : Geometry q.ledger q.j q.w q.k a b cTag q.index q.width)
    (hJ : (q.ledger.config (rightNeighbor q.j)).leader=false)
    (hKeep : WindowLocal.selectedGroupLoss g q.ledger e=none) :
    remaining (tick q e)+(wCharge q e : Int)≤remaining q := by
  let z := q.ledger
  have hWmk : (z.config q.w).mark=true := by simpa [hG.wTag] using (hv.covers q.w).symm
  have hJmk : (z.config q.j).mark=true := by simpa [hG.jTag] using (hv.covers q.j).symm
  by_cases hw : (z.config (rightNeighbor q.w)).leader=true
  · have hF : FirstMark z.config (rightNeighbor q.j) q.index := by
      have hD := hG.wBefore
      have hC := hG.width
      refine ⟨by omega,by rwa [hG.wLift],?_⟩
      intro i hi
      rw [hG.noOther i (by omega) (by omega)]
      decide
    obtain ⟨htag,hL⟩ := WindowScopedFourHead.living_after_ghost_stays hn z e q.j q.w b
      hq hv.covers hJmk hJ ⟨hG.wTag,hw⟩ hF hG.wLift
    have hm : ¬moves z e q.w := by
      rintro ⟨he,hP⟩
      have hZ : (advance z e).slots q.w=none := by
        change slotsStep z.config z.slots e q.w=none
        rw [←he,show slotsStep z.config z.slots e=SevenTagCharge.move z.slots e by simp [slotsStep,hP]]
        exact (paid_mover_or_resident hn z.slots e).1
      rw [htag] at hZ
      cases hZ
    have hpost : ((tick q e).ledger.config (rightNeighbor (tick q e).w)).leader=true := by
      change ((advance z e).config (rightNeighbor (landing z e q.w))).leader=true
      simpa only [landing,if_neg hm] using hL
    simp [remaining,wCharge,z,hw,hpost,hm]
  · have hw0 := Bool.eq_false_iff.mpr hw
    have hCut : Cut z q.j q.w q.k a b cTag q.index q.width :=
      ⟨hG.jTag,hG.wTag,hG.kTag,hG.wLift,hG.kLift,hG.wBefore,hG.width,hJ,hw0,hG.noOther⟩
    have H := (tagged_charge hn z g e q.j q.w q.k a b cTag q.index q.width hCut
      hv.markCover hv.covers ha hb hc hKeep).2.2.2
    have HH : rearInventory (tick q e).ledger.config (rightNeighbor (tick q e).j) (tick q e).width+
        (wCharge q e : Int) ≤ rearInventory z.config (rightNeighbor q.j) q.width := by
      simpa only [tick,landing,widthAfter,wCharge,moves] using H
    unfold remaining
    change (if ((tick q e).ledger.config (rightNeighbor (tick q e).w)).leader then 0 else _) + _ ≤
      (if (z.config (rightNeighbor q.w)).leader then 0 else _)
    rw [if_neg hw]
    split
    · exact Int.le_trans (Int.add_le_add_right (rearInventory_interval _ _ _).1 _) HH
    · exact HH

theorem retained_progress_cap {p c n : Nat} {x : Config p c n} (hp : 2≤p) (hc0 : 12≤c)
    (hn : 4≤n) (g : List (Fin n)) (a b cTag : Fin n) (ha : a∈g) (hb : b∈g) (hc : cTag∈g)
    (q : Cursor p c n) (w : List (Fin n))
    (hw : RetainedKeep g q w) (hv : Valid q.ledger x) (hq : QuietEntrance q.ledger.config)
    (hG : Geometry q.ledger q.j q.w q.k a b cTag q.index q.width)
    (hJ : (q.ledger.config (rightNeighbor q.j)).leader=false) :
    totalW q w ≤ q.width+1 := by
  have H : (totalW q w : Int) ≤ remaining q := by
    induction hw with
    | nil =>
      change 0≤remaining _
      exact remaining_nonneg _
    | @cons q e t hg hpost _ ih =>
      have hstep := remaining_le_paid_row hn g a b cTag ha hb hc x q e hv hq hG hJ hg
      have hgeom := geom_step hn q.ledger g e q.j q.w q.k a b cTag q.index q.width hG
        hv.markCover hv.covers ha hb hc hg
      have ht := ih (valid_step hn q.ledger x e hv)
        (RootedFresh.quiet_step q.ledger.config e hp hc0 hn hq) hgeom hpost
      simp only [totalW,Int.natCast_add]
      omega
  unfold remaining at H
  split at H
  · omega
  · have h := WindowFourHeadStock.interval_size_cap q.ledger.config (rightNeighbor q.j) q.width
    omega

end L4.WindowFourHeadCut
