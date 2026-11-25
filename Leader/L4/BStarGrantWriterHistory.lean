import Leader.L4.BStarGrantReaderHistory

namespace L4.BStarGrantWriterHistory
open AllSizeProtocol BStarTrace BStarLongLayout BStarLongClaims BStarLongWork
open BStarLongCommand BStarLongGrant BStarLongGrantProjection BStarLongEvents
open BStarCaptureInterval BStarReaderGrantOrbit BStarBankTrace BStarLongPublication
open BStarH6WordChart BStarGrantBirth

open BStarGrantReaderHistory (writer_free_safe canonical_of_live ports)

theorem win_no_grants (old rel ask : Ports) (h : win old rel ask 1=true) :
    ∀ j : Fin 3, old j=false := by
  have H : (canonical old 0 || canonical old 1 || canonical old 2)=false := by
    simpa [win,Bool.and_eq_true] using (show (!(canonical old 0 || canonical old 1 || canonical old 2))=true from by
      unfold win at h
      simp only [if_true,Bool.and_eq_true] at h
      exact h.1.1)
  cases W : old 1
  · simp [canonical,W,Bool.or_eq_false_iff] at H
    intro j
    have J : j=0 ∨ j=1 ∨ j=2 := by
      have := j.isLt
      omega
    rcases J with rfl|rfl|rfl
    · exact H.1
    · exact W
    · exact H.2
  · simp [canonical,W] at H

theorem header_safe (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Side) (b : Fin 3)
    (head : (geometry g s).axes.h6=true) (sel : readSel (BStarLongGrant.atOld x s)=b)
    (no : ∀ a∈(longTrace g x).publications, a.endpoint≠s) :
    ∀ o∈offers g x, SafeOffer g x s b o := by
  apply safe_from_events g x s b _ no
  intro c p _ hs
  intro _ _ _ _ d _ H
  have h : (geometry g c.source.side).axes.h6=true := hs.symm ▸ head
  have S : readSel (BStarLongWork.atOld x c.source)=b := by
    change readSel (lane (c.source.side==.right) x)=b
    rw [hs]
    exact sel
  simp only [h,Bool.true_and,Bool.not_eq_false',BStarLongOutgoing.actual,Bool.and_eq_true,beq_iff_eq,S] at H
  exact H.2.symm
variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat}
variable (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step B
local notation "run" => BStarResetSchedule.run step

private theorem pair_site (x : X) (e : Fin n) (sep : e≠rightNeighbor e) (s : Side) :
    step x e (site e s)=lane (sideFlag s) (largePair B (x e,x (rightNeighbor e))) := by
  cases s <;> simp [AllSizeS1Geometry.step,site,sideFlag,lane,Ne.symm sep]

def NoPublication (x : X) (e i : Fin n) : Prop :=
  ∀ s : Side, i=site e s →
    ∀ a∈(longTrace (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).publications,
      a.endpoint≠s

def BeforePublication (x : X) (i : Fin n) (w : List (Fin n)) : Prop :=
  ∀ u e v, w=u++e::v → NoPublication hp (run x u) e i
theorem birth_step (x : X) (e i : Fin n) (sep : e≠rightNeighbor e)
    (bank : Fin 3) (won : WonAt hp x e i 1) :
    HeldStep bank (x i).long (step x e i).long ∧
      conflict (ports (step x e) i)=false := by
  obtain ⟨s,E,head,win,_⟩ := won
  subst i
  refine ⟨?_,BStarGrantReaderHistory.mark_coherent hp x e sep s⟩
  rw [pair_site hp x e sep s]
  have H := bStar_held_step k₁ k₂ t₂ J₁ J₂ r c p c₁ hp (x e,x (rightNeighbor e)) s bank
    (writer_free_safe _ _ s bank head ((win_no_grants _ _ _ win) 1))
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
    (bank : Fin 3) (bank_eq : readSel (x i).long=bank) (pre : NoPublication hp x e i)
    (coh : conflict (ports x i)=false) (now : bit x i 1≠0)
    (after : bit (step x e) i 1≠0) :
    HeldStep bank (x i).long (step x e i).long ∧ conflict (ports (step x e) i)=false := by
  have touched (s : Side) (E : i=site e s) :
      HeldStep bank (x i).long (step x e i).long ∧ conflict (ports (step x e) i)=false := by
    subst i
    have H := live_header hp x e sep s 1 after
    refine ⟨?_,BStarGrantReaderHistory.mark_coherent hp x e sep s⟩
    rw [pair_site hp x e sep s]
    have P := bStar_held_step k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
      (x e,x (rightNeighbor e)) s bank (header_safe _ _ s bank H (by cases s <;> exact bank_eq) (pre s rfl))
    cases s <;> exact P
  by_cases hl : i=e
  · exact touched .left hl
  · by_cases hr : i=rightNeighbor e
    · exact touched .right hr
    · have E : step x e i=x i := by simp [AllSizeS1Geometry.step,hl,hr]
      rw [show (step x e i).long=(x i).long from congrArg LargeSite.long E]
      exact ⟨.noTouch _,by unfold ports; rw [E]; exact coh⟩

theorem live_trace (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (i : Fin n) (bank : Fin 3) (w : List (Fin n))
    (bank_eq : readSel (x i).long=bank)
    (coh : conflict (ports x i)=false) (life : Continuous hp x i 1 w)
    (pre : BeforePublication hp x i w) :
    HeldTrace bank (x i).long ((run x w) i).long ∧ conflict (ports (run x w) i)=false := by
  induction w generalizing x with
  | nil => exact ⟨.empty _,coh⟩
  | cons e w ih =>
    have M := live_step hp x e i (sep e) bank bank_eq (pre [] e w rfl)
      coh (life [] _ rfl) (life [e] _ rfl)
    have S : Continuous hp (step x e) i 1 w := by
      intro u v E
      exact life (e::u) v (congrArg (List.cons e) E)
    have P : BeforePublication hp (step x e) i w := by
      intro u k v E
      exact pre (e::u) k v (congrArg (List.cons e) E)
    have T := ih (step x e) ((held_step_reads M.1).1.trans bank_eq) M.2 S P
    have trans {a b c : BitVec LW} (u : HeldTrace bank a b) (v : HeldTrace bank b c) :
        HeldTrace bank a c := by
      induction v with
      | empty => exact u
      | next f g ih => exact .next ih g
    exact ⟨trans (.next (.empty _) M.1) T.1,T.2⟩

/-- The old grant-winning header through any continuous writer-held
prefix with no publication on that physical endpoint. Held STAGE
is allowed, even with arbitrary old descriptor bytes. -/
theorem header_interval (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (x : X) (e i : Fin n) (won : WonAt hp x e i 1) (w : List (Fin n))
    (life : Continuous hp (step x e) i 1 w)
    (pre : BeforePublication hp (step x e) i w) :
    ∀ u v, w=u++v →
      let init : BitVec LW := (x i).long
      let fin : BitVec LW := ((run (step x e) u) i).long
      readSel fin=readSel init ∧
      payloadView (readSel init) fin=payloadView (readSel init) init ∧
      canonical (ports (run (step x e) u) i) 1=true ∧
      ports (run (step x e) u) i 0=false ∧ ports (run (step x e) u) i 2=false := by
  intro u v E
  dsimp only
  let bank := readSel (x i).long
  have M := birth_step hp x e i (sep e) bank won
  have S : Continuous hp (step x e) i 1 u := by
    intro a b H
    exact life a (b++v) (by rw [E,H,List.append_assoc])
  have P : BeforePublication hp (step x e) i u := by
    intro a k b H
    exact pre a k (b++v) (by rw [E,H,List.append_assoc]; rfl)
  have F := held_step_reads M.1
  have T := live_trace hp sep (step x e) i bank u F.1 M.2 S P
  have G := held_trace_reads T.1
  have C := canonical_of_live _ i 1 T.2 (life u v E)
  have C' : ports (run (step x e) u) i 1=true := by
    exact (canonical_clean _ T.2 1).symm.trans C
  have R := T.2
  simp [conflict,C',Bool.or_eq_false_iff] at R
  exact ⟨G.1.trans F.1,G.2.trans F.2,C,R.1,R.2⟩

/-- Physical stopping event: an actual winning advancing COMMIT at
the old header's centre, with the literal old authorization guard.
No selector-preservation claim is made across this mark. -/
theorem stopping_commit (x : X) (e i : Fin n) (stop : ¬ NoPublication hp x e i) :
    ∃ (s : Side) (c : CommandClaim) (q : BStarLongToken.Payload) (b : Fin 3),
      i=site e s ∧ c.source.side=s ∧
      let g := oldPair B x e
      let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
      (c,.advance q)∈actualOffers g raw ∧
      LiteralCommit (geometry g s) c.source (x i).long q b := by
  classical
  unfold NoPublication at stop
  obtain ⟨s,Hs⟩ := Classical.not_forall.mp stop
  have hi : i=site e s := Classical.byContradiction (fun h => Hs (fun eq => (h eq).elim))
  obtain ⟨a,Ha⟩ := Classical.not_forall.mp (fun h => Hs (fun _ => h))
  have ha : a∈(longTrace (oldPair B x e) ((x e).long,(x (rightNeighbor e)).long)).publications :=
    Classical.byContradiction (fun h => Ha (fun v => (h v).elim))
  have H : a.endpoint=s := Classical.byContradiction (fun h => Ha (fun _ => h))
  obtain ⟨c,q,hm,hside,L⟩ := (literal_event_iff _ _ a).mp ha
  have S : c.source.side=s := hside.symm.trans H
  refine ⟨s,c,q,a.bank,hi,S,hm,?_⟩
  rwa [S,show BStarLongWork.atOld ((x e).long,(x (rightNeighbor e)).long) c.source =
    (x i).long from by rw [hi]; change lane (c.source.side==.right) _ = _; rw [S]; cases s <;> rfl] at L

end L4.BStarGrantWriterHistory
