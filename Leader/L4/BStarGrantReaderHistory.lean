import Leader.L4.BStarGrantBirth
import Leader.L4.BStarReaderGrantOrbit

namespace L4.BStarGrantReaderHistory
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongWork
open BStarLongCommand BStarLongGrant BStarLongGrantProjection BStarLongEvents
open BStarCaptureInterval BStarReaderGrantOrbit BStarBankTrace BStarLongPublication
open BStarH6WordChart BStarGrantBirth

theorem win_writer_free (old rel ask : Ports) (j : Fin 3) (ne : j≠1)
    (h : win old rel ask j=true) : old 1=false := by
  have W : (!canonical old 1)=true := by
    unfold win at h
    simp only [if_neg ne,Bool.and_eq_true] at h
    exact h.1.1.1.2
  cases V : old 1 <;> simp_all [canonical]

/-- A writer-free old header, even before our reader is installed, cannot
execute any successful STAGE/COMMIT against its selected bank. -/
theorem writer_free_safe (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side)
    (bank : Fin 3) (head : (geometry g s).axes.h6=true)
    (w : original (BStarLongGrant.atOld x s) 1=false) :
    ∀ o∈offers g x, SafeOffer g x s bank o := by
  apply safe_from_events g x s bank
  · intro c p _ hs
    intro _ _ _ _ d _ H
    have E : ((grant 1).read (BStarLongWork.atOld x c.source)).getLsbD 0=false := by
      change ((grant 1).read (lane (c.source.side==.right) x)).getLsbD 0=false
      rw [hs]
      exact w
    have h : (geometry g c.source.side).axes.h6=true := hs.symm ▸ head
    simp only [h,BStarLongOutgoing.actual,E,Bool.false_and,Bool.not_false,Bool.true_and] at H
    contradiction
  · intro e he side
    obtain ⟨c,p,_,hs,H⟩ := (literal_event_iff g x e).mp he
    obtain ⟨_,_,_,_,d,_,_,K⟩ := H
    have S : c.source.side=s := hs.symm.trans side
    unfold BStarLongPublication.guard typedGuard at K
    have E : ((grant 1).read (BStarLongWork.atOld x c.source)).getLsbD 0=false := by
      change ((grant 1).read (lane (c.source.side==.right) x)).getLsbD 0=false
      rw [S]
      exact w
    simp only [E,Bool.false_and,Bool.and_false,Bool.false_eq_true] at K

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

def ports (z : X) (i : Fin n) : Ports := original (z i).long

private theorem pair_site (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (s : Side) :
    step x e (site e s)=lane (sideFlag s) (largePair B (x e,x (rightNeighbor e))) := by
  cases s <;> simp [AllSizeS1Geometry.step,site,sideFlag,lane,Ne.symm sep]

theorem mark_coherent (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (s : Side) :
    conflict (ports (step x e) (site e s))=false := by
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  let newRaw : Pair (BitVec LW) := Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))
  let os := (BStarLongCommandData.round g raw).offered
  have h (j : Fin 3) : ports (step x e) (site e s) j=grants g raw os s j := by
    have P := joined_grants k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) s j
    change read newRaw s j=BitVec.ofBool (grants g raw os s j) at P
    have E := congrArg (fun z : BitVec 1 => z.getLsbD 0) P
    unfold ports
    rw [pair_site hp x e sep s]
    have H : original (lane (sideFlag s) (largePair B (x e,x (rightNeighbor e)))).long j =
        (read newRaw s j).getLsbD 0 := by cases s <;> rfl
    rw [H]
    rw [E]
    cases grants g raw os s j <;> rfl
  rw [funext h]
  exact result_coherent g raw os s

theorem canonical_of_live (x : X) (i : Fin n) (j : Fin 3)
    (coh : conflict (ports x i)=false) (L : bit x i j≠0) :
    canonical (ports x i) j=true := by
  rw [canonical_clean _ coh]
  have H : (bit x i j).getLsbD 0=true := by
    generalize bit x i j=z at L ⊢
    have E : z=(1 : BitVec 1) := by
      apply BitVec.eq_of_toNat_eq
      have h := z.isLt
      change z.toNat<2 at h
      have N : z.toNat≠0 := fun e => L (BitVec.eq_of_toNat_eq e)
      change z.toNat=1
      omega
    rw [E]
    rfl
  exact H

theorem birth_step (x : X) (e i : Fin n) (sep : e≠rightNeighbor e)
    (j : Fin 3) (ne : j≠1) (bank : Fin 3) (won : WonAt hp x e i j) :
    HeldStep bank (x i).long (step x e i).long ∧
      conflict (ports (step x e) i)=false := by
  obtain ⟨s,E,head,win,_⟩ := won
  subst i
  refine ⟨?_,mark_coherent hp x e sep s⟩
  rw [pair_site hp x e sep s]
  have H := bStar_held_step k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) s bank
    (writer_free_safe _ _ s bank head (win_writer_free _ _ _ j ne win))
  cases s <;> exact H

/-- A touched old nonheader writes zero grants, so continuity across
the current mark alone forces the old touched node to be a header. -/
private theorem live_header (x : X) (e : Fin n) (sep : e≠rightNeighbor e)
    (s : Side) (j : Fin 3) (L : bit (step x e) (site e s) j≠0) :
    (geometry (oldPair B x e) s).axes.h6=true := by
  have H := joined_grants k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) s j
  have Q : bit (step x e) (site e s) j =
      read (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s j := by
    unfold bit
    rw [pair_site hp x e sep s]
    cases s <;> rfl
  change read (Pair.map LargeSite.long (largePair B (x e,x (rightNeighbor e)))) s j =
    BitVec.ofBool (grants (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)
      (BStarLongCommandData.round (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).offered s j) at H
  cases A : (geometry (oldPair B x e) s).axes.h6
  · apply (L (Q.trans (H.trans ?_))).elim
    simp [grants,A]
  · rfl

theorem live_step (x : X) (e i : Fin n) (sep : e≠rightNeighbor e)
    (j : Fin 3) (ne : j≠1) (bank : Fin 3)
    (coh : conflict (ports x i)=false) (now : bit x i j≠0)
    (after : bit (step x e) i j≠0) :
    HeldStep bank (x i).long (step x e i).long ∧ conflict (ports (step x e) i)=false := by
  have touched (s : Side) (E : i=site e s) :
      HeldStep bank (x i).long (step x e i).long ∧ conflict (ports (step x e) i)=false := by
    subst i
    have H := live_header hp x e sep s j after
    have K := canonical_of_live x (site e s) j coh now
    refine ⟨?_,mark_coherent hp x e sep s⟩
    rw [pair_site hp x e sep s]
    have P := (BStarReaderExclusion.bStar_reader_step k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) s j ne bank H (by cases s <;> exact K)).1
    cases s <;> exact P
  by_cases hl : i=e
  · exact touched .left hl
  · by_cases hr : i=rightNeighbor e
    · exact touched .right hr
    · have E : step x e i=x i := by simp [AllSizeS1Geometry.step,hl,hr]
      rw [show (step x e i).long=(x i).long from congrArg LargeSite.long E]
      exact ⟨.noTouch _,by unfold ports; rw [E]; exact coh⟩

theorem live_trace (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (i : Fin n) (j : Fin 3) (ne : j≠1) (bank : Fin 3) (w : List (Fin n))
    (coh : conflict (ports x i)=false) (life : Continuous hp x i j w) :
    HeldTrace bank (x i).long ((run x w) i).long ∧ conflict (ports (run x w) i)=false := by
  induction w generalizing x with
  | nil => exact ⟨.empty _,coh⟩
  | cons e w ih =>
    have M := live_step hp x e i (sep e) j ne bank coh (life [] _ rfl) (life [e] _ rfl)
    have S : Continuous hp (step x e) i j w := by
      intro u v E
      exact life (e::u) v (congrArg (List.cons e) E)
    have T := ih (step x e) M.2 S
    have trans {a b c : BitVec LW} (u : HeldTrace bank a b) (v : HeldTrace bank b c) :
        HeldTrace bank a c := by
      induction v with
      | empty => exact u
      | next f g ih => exact .next ih g
    exact ⟨trans (.next (.empty _) M.1) T.1,T.2⟩

/-- From the old winning mark through every continuous live suffix,
the selector and header-local selected bank readout remain those
of the acquisition snapshot. No body digit custody is asserted. -/
theorem header_interval (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (e i : Fin n) (j : Fin 3) (ne : j≠1)
    (won : WonAt hp x e i j) (w : List (Fin n))
    (life : Continuous hp (step x e) i j w) :
    ∀ u v, w=u++v →
      let init : BitVec LW := (x i).long
      let fin : BitVec LW := ((run (step x e) u) i).long
      readSel fin=readSel init ∧
      payloadView (readSel init) fin=payloadView (readSel init) init ∧
      canonical (ports (run (step x e) u) i) j=true := by
  intro u v E
  dsimp only
  let bank := readSel (x i).long
  have M := birth_step hp x e i (sep e) j ne bank won
  have S : Continuous hp (step x e) i j u := by
    intro a b H
    exact life a (b++v) (by rw [E,H,List.append_assoc])
  have T := live_trace hp sep (step x e) i j ne bank u M.2 S
  have F := held_step_reads M.1
  have G := held_trace_reads T.1
  exact ⟨G.1.trans F.1,G.2.trans F.2,canonical_of_live _ i j T.2 (life u v E)⟩

private theorem raw_readouts (x y : BitVec LW) (S : readSel y=readSel x)
    (V : payloadView (readSel x) y=payloadView (readSel x) x) :
    selectedHeader y=selectedHeader x ∧
      BStarLongGrant.headerBits y=BStarLongGrant.headerBits x := by
  have K := congrArg Prod.snd V
  constructor
  · unfold selectedHeader
    rw [S,K]
  · unfold BStarLongGrant.headerBits
    dsimp only
    rw [S]
    change BitVec.ofNat 9 ((List.finRange 9).foldl
      (fun acc d => 2*acc+((payloadView (readSel x) y).2 d).toNat) 0) = _
    rw [K]
    rfl

theorem header_readout_interval (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (e i : Fin n) (j : Fin 3) (ne : j≠1)
    (won : WonAt hp x e i j) (w : List (Fin n))
    (life : Continuous hp (step x e) i j w) :
    ∀ u v, w=u++v →
      selectedHeader ((run (step x e) u) i).long=selectedHeader (x i).long ∧
      BStarLongGrant.headerBits ((run (step x e) u) i).long=BStarLongGrant.headerBits (x i).long := by
  intro u v E
  have ⟨S,V,_⟩ := header_interval hp sep x e i j ne won w life u v E
  exact raw_readouts _ _ S V

end L4.BStarGrantReaderHistory
