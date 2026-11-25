import Leader.L4.ReportPulseRaw
import Leader.L4.ReportPulseWindow
import Leader.L4.ReportHalfCellClock
import Leader.L4.ReportStickyRawCover

namespace L4.ReportPulseWarmup
open AllSizeProtocol PhysicalCustody ReportByteRows ReportPulseRaw
open ReportPulseWait

-- Extract precisely the all-mark equality used in ReportPulseRaw.wire_mean.
private theorem incoming_unique {n : Nat} (a e b : Fin n)
    (A : rightNeighbor a=b) : b=rightNeighbor e ↔ e=a := by
  constructor
  · intro E
    apply Fin.ext
    have He := e.isLt
    have Ha := a.isLt
    have F := congrArg Fin.val (A.trans E)
    change (a.val+1)%n=(e.val+1)%n at F
    by_cases U : a.val+1<n
    · rw [Nat.mod_eq_of_lt U] at F
      by_cases V : e.val+1<n
      · rw [Nat.mod_eq_of_lt V] at F
        omega
      · rw [show e.val+1=n by omega,Nat.mod_self] at F
        omega
    · rw [show a.val+1=n by omega,Nat.mod_self] at F
      by_cases V : e.val+1<n
      · rw [Nat.mod_eq_of_lt V] at F
        omega
      · rw [show e.val+1=n by omega,Nat.mod_self] at F
        omega
  · rintro rfl
    exact A.symm

private theorem no_outgoing_paint (p : Params) (x : BitVec p.w) :
    paints p true 2 x=false := by
  unfold paints
  dsimp only
  generalize (if ((x.extractLsb' (ell p.streak) 2).toNat==3) then 0
      else (x.extractLsb' (ell p.streak) 2).toNat)=r
  split <;> (first | rfl | split <;> simp_all)

theorem wire_clock_eq {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (y : X) (e : Fin n) (h : Bool) (hy : Q y) :
    ReportPulseDecode.state p (bytes (raw y e))
        (h || countedPaint b p bytes y e) =
      ReportPulseWait.step p.streak a b e
        (ReportPulseDecode.state p (bytes y) h) := by
  have E := incoming_unique a e b A
  by_cases H : e=a
  · have K : b≠e := by exact fun L=>D (H.symm.trans L.symm)
    have J := E.mpr H
    rw [ReportPulseWait.step,if_pos H]
    have T := ReportPulseDecode.state_congr p (bytes (raw y e))
      (pulseApply p true 1 (bytes y))
      (h || countedPaint b p bytes y e)
      (fun i I=>by
        simpa only [if_neg K,if_pos J] using F.bits y e i hy I)
    rw [T,countedPaint,if_pos J]
    exact ReportPulseDecode.clock_eq p P (bytes y) false h
  · have J : b≠rightNeighbor e := fun I=>H (E.mp I)
    by_cases K : e=b
    · rw [ReportPulseWait.step,if_neg H,if_pos K]
      have T := ReportPulseDecode.state_congr p (bytes (raw y e))
        (pulseApply p true 2 (bytes y))
        (h || countedPaint b p bytes y e)
        (fun i I=>by
          simpa only [if_pos K.symm] using F.bits y e i hy I)
      rw [T,countedPaint,if_neg J,←no_outgoing_paint p (bytes y)]
      exact ReportPulseDecode.clock_eq p P (bytes y) true h
    · rw [ReportPulseWait.step,if_neg H,if_neg K]
      have T := ReportPulseDecode.state_congr p (bytes (raw y e))
        (bytes y) (h || countedPaint b p bytes y e)
        (fun i I=>by
          simpa only [if_neg (Ne.symm K),if_neg J] using F.bits y e i hy I)
      rw [T,countedPaint,if_neg J,Bool.or_false]

def readClock {X : Type} (p : Params) (bytes : X → BitVec p.w)
    (x : X) : ReportPulseWait.State :=
  ReportPulseDecode.state p (bytes x) false

def Clean (x : ReportPulseWait.State) : Prop := x.phase=.empty ∧ x.count=0

def cleanBit (x : ReportPulseWait.State) : Bool :=
  decide (x.phase=.empty ∧ x.count=0)

theorem cleanBit_iff (x : ReportPulseWait.State) : cleanBit x=true ↔ Clean x := by
  simp [cleanBit,Clean]

theorem cleanBit_false (x : ReportPulseWait.State) (H : ¬Clean x) :
    cleanBit x=false := by
  exact Bool.eq_false_iff.mpr (fun E=>H ((cleanBit_iff x).mp E))

-- First cut, including the empty prefix. "later" expressly excludes a
-- clean state at the old endpoint of every mark preceding the cut.
inductive FirstCut {X : Type} {n : Nat}
    (raw : X → Fin n → X) (target : X → Prop) :
    X → List (Fin n) → Prop where
  | here (x : X) : target x → FirstCut raw target x []
  | later (x : X) (e : Fin n) (u : List (Fin n)) :
      ¬target x → FirstCut raw target (raw x e) u →
      FirstCut raw target x (e::u)

theorem firstCut_clean {X : Type} {n : Nat}
    {raw : X → Fin n → X} {target : X → Prop}
    {x : X} {u : List (Fin n)} (H : FirstCut raw target x u) :
    target (u.foldl raw x) := by
  induction H with
  | here _ H => exact H
  | later _ _ _ _ _ ih => exact ih

-- A first-cut prefix contains no earlier clean endpoint.
theorem firstCut_no_earlier {X : Type} {n : Nat}
    {raw : X → Fin n → X} {target : X → Prop}
    {x : X} {u : List (Fin n)} (H : FirstCut raw target x u) :
    ∀ v e r, u=v++e::r → ¬target (v.foldl raw x) := by
  induction H with
  | here _ _ =>
    intro v e r E
    have L := congrArg List.length E
    simp at L
  | later x f u N H ih =>
    intro v e r E
    cases v with
    | nil => exact N
    | cons g v =>
      have V : f=g ∧ u=v++e::r := by simpa using E
      rw [←V.1]
      exact ih v e r V.2

theorem wire_run_good {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (x : X) (w : List (Fin n))
    (G : Q x) : Q (w.foldl raw x) := by
  induction w generalizing x with
  | nil => exact G
  | cons e w ih => exact ih (raw x e) (F.stays x e G)

-- The exact finite-word factor, including the old-mark paint latch.
theorem wire_run_eq {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (x : X) (w : List (Fin n)) (h : Bool) (G : Q x) :
    let z := w.foldl (monitor raw (countedPaint b p bytes)) (x,h)
    ReportPulseDecode.state p (bytes z.1) z.2 =
      w.foldl (fun y e=>ReportPulseWait.step p.streak a b e y)
        (ReportPulseDecode.state p (bytes x) h) := by
  induction w generalizing x h with
  | nil => rfl
  | cons e w ih =>
    have T := ih (raw x e) (h || countedPaint b p bytes x e)
      (F.stays x e G)
    simpa only [List.foldl_cons,monitor,wire_clock_eq F a A D P x e h G]
      using T

theorem monitor_base {X : Type} {n : Nat}
    (raw : X → Fin n → X) (paint : X → Fin n → Bool)
    (x : X) (h : Bool) (w : List (Fin n)) :
    (w.foldl (monitor raw paint) (x,h)).1=w.foldl raw x := by
  induction w generalizing x h with
  | nil => rfl
  | cons e w ih => exact ih (raw x e) (h || paint x e)

-- Compare the warm cut to the first incoming-first LOSS.
-- This is the existing J=1 clock with a and b interchanged.
def flip : Phase → Phase
  | .empty => .empty
  | .incoming => .outgoing
  | .outgoing => .incoming

def WarmRel (x y : ReportPulseWait.State) : Prop :=
  y.phase=flip x.phase ∧ y.count=0 ∧ (y.hit=true → Clean x)

private theorem warm_rel_step {n J : Nat} (a b e : Fin n) (D : a≠b)
    (x y : ReportPulseWait.State) (R : WarmRel x y) (Y : y.hit=false) :
    WarmRel (ReportPulseWait.step J a b e x) (ReportPulseWait.step 1 b a e y) := by
  rcases x with ⟨ph,k,h⟩
  rcases y with ⟨ph',k',h'⟩
  rcases R with ⟨Rph,Rk,_⟩
  change ph'=flip ph at Rph
  change k'=0 at Rk
  change h'=false at Y
  subst ph'
  subst k'
  subst h'
  have K : effective 1 0=0 := by decide
  by_cases U : e=a
  ·
    by_cases L : effective J k+1=J <;>
      cases ph <;> simp [WarmRel,Clean,ReportPulseWait.step,side,flip,U,D,L]
  · by_cases V : e=b
    ·
        cases ph <;> simp [WarmRel,Clean,ReportPulseWait.step,side,flip,V,D.symm,K]
    · simp [WarmRel,ReportPulseWait.step,U,V]

/-- Comparison of the exact truncated cost on the unchanged raw alphabet
    to the exact truncated cost of the reversed unit-streak clock. -/
theorem wire_warm_cost_le {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (t : Nat) (x : X) (G : Q x) (z : ReportPulseWait.State)
    (R : WarmRel (readClock p bytes x) z) :
    L4.iidHitCost raw (fun y=>Clean (readClock p bytes y)) t x ≤
      L4.iidHitCost (fun y e=>ReportPulseWait.step 1 b a e y)
        (fun y=>y.hit=true) t z := by
  classical
  induction t generalizing x z with
  | zero => simp [L4.iidHitCost]
  | succ t ih =>
    by_cases C : Clean (readClock p bytes x)
    · rw [L4.iidHitCost_of_target raw _ x C]
      exact Nat.zero_le _
    · have Z : z.hit≠true := fun H=>C (R.2.2 H)
      have Z' : z.hit=false := Bool.eq_false_iff.mpr Z
      simp only [L4.iidHitCost,if_neg C,if_neg Z]
      apply Nat.add_le_add_left
      apply FiniteUniformStoppingTree.ofFn_sum_le
      intro e
      have U := warm_rel_step (J:=p.streak) a b e D (readClock p bytes x) z R Z'
      have E := wire_clock_eq F a A D P x e false G
      change ReportPulseDecode.state p (bytes (raw x e))
        (false || countedPaint b p bytes x e) =
        ReportPulseWait.step p.streak a b e (readClock p bytes x) at E
      rw [←E] at U
      have V : WarmRel (readClock p bytes (raw x e)) (ReportPulseWait.step 1 b a e z) :=
        U -- WarmRel and Clean do not inspect the actual clock hit bit.
      exact ih (raw x e) (F.stays x e G) (ReportPulseWait.step 1 b a e z) V

/-- Time zero is a cut when already clean; otherwise the first clean
    boundary costs at most 4*n, even with arbitrary inherited bytes. -/
theorem wire_warm_mean {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (x : X) (G : Q x) :
    L4.IIDExpectedHittingTimeAtMost raw
      (fun y=>Clean (readClock p bytes y)) x (4*n) := by
  let z : ReportPulseWait.State := ⟨flip (readClock p bytes x).phase,0,false⟩
  have R : WarmRel (readClock p bytes x) z := by
    simp [WarmRel,z]
  have V : potential n 1 z≤4*n := by
    cases E : (readClock p bytes x).phase <;>
      simp [z,E,flip,potential,potential0,effective] <;> omega
  intro t
  exact Nat.le_trans (wire_warm_cost_le F a A D P t x G z R)
    (Nat.le_trans (ReportPulseWait.truncated (J:=1) (by decide) b a D.symm z t)
      (Nat.mul_le_mul_right _ V))

-- Warm monitor latches the first *postmark* clean state, but tests time
-- zero in its initializer. It keeps running every raw mark after a hit.
def warmNext {X : Type} {n : Nat} (raw : X → Fin n → X)
    (p : Params) (bytes : X → BitVec p.w) (z : X×Bool) (e : Fin n) :
    X×Bool :=
  let y := raw z.1 e
  (y,z.2 || cleanBit (readClock p bytes y))

def warmInit {X : Type} (p : Params) (bytes : X → BitVec p.w)
    (x : X) : X×Bool := (x,cleanBit (readClock p bytes x))

theorem warm_factor {X : Type} {n : Nat}
    (raw : X → Fin n → X) (p : Params) (bytes : X → BitVec p.w)
    (t : Nat) (x : X) :
    L4.iidHitCost (warmNext raw p bytes) (fun z=>z.2=true) t
      (warmInit p bytes x) =
    L4.iidHitCost raw (fun y=>Clean (readClock p bytes y)) t x := by
  classical
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    by_cases C : Clean (readClock p bytes x)
    · have B := (cleanBit_iff _).mpr C
      simp [L4.iidHitCost,warmInit,B,C]
    · have B := cleanBit_false _ C
      simp only [L4.iidHitCost,warmInit,B,Bool.false_eq_true,if_false,if_neg C]
      congr 2
      apply congrArg List.ofFn
      funext e
      simpa only [warmNext,warmInit,B,Bool.false_or] using ih (raw x e)

theorem warm_firstCut_exists {X : Type} {n : Nat}
    (raw : X → Fin n → X) (p : Params) (bytes : X → BitVec p.w)
    (x : X) (w : List (Fin n))
    (H : (w.foldl (warmNext raw p bytes) (warmInit p bytes x)).2=true) :
    ∃ u v, w=u++v ∧
      FirstCut raw (fun y=>Clean (readClock p bytes y)) x u := by
  induction w generalizing x with
  | nil =>
    exact ⟨[],[],rfl,.here x ((cleanBit_iff _).mp H)⟩
  | cons e w ih =>
    by_cases C : Clean (readClock p bytes x)
    · exact ⟨[],e::w,rfl,.here x C⟩
    · have B := cleanBit_false _ C
      have E : (w.foldl (warmNext raw p bytes)
          (warmInit p bytes (raw x e))).2=true := by
        simpa only [List.foldl_cons,warmInit,warmNext,B,Bool.false_or]
          using H
      obtain ⟨u,v,W,T⟩ := ih (raw x e) E
      exact ⟨e::u,v,by simp [W],.later x e u C T⟩

-- The sticky monitor makes the old warm-block arithmetic applicable.
theorem wire_warm_tail {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (x : X) (G : Q x) (L j : Nat)
    (fits : j*(3*n*(p.streak+2))≤L) :
    2^j*FourLossStickyClock.badCount
      (fun w=>¬(Height.runWord (warmNext raw p bytes)
        (warmInit p bytes x) w).2=true) L ≤ n^L := by
  let next := warmNext raw p bytes
  let gd := fun z : X×Bool =>
    Q z.1 ∧ (Clean (readClock p bytes z.1) → z.2=true)
  let hit := fun z : X×Bool => z.2=true
  have stay (z : X×Bool) (e : Fin n) (H : gd z) : gd (next z e) := by
    refine ⟨F.stays _ _ H.1,?_⟩
    intro C
    change (z.2 || cleanBit (readClock p bytes (raw z.1 e)))=true
    change Clean (readClock p bytes (raw z.1 e)) at C
    rw [(cleanBit_iff _).mpr C]
    simp
  have keep (z : X×Bool) (e : Fin n) (H : hit z) : hit (next z e) := by
    change z.2=true at H
    simp [hit,next,warmNext,H]
  have mean (z : X×Bool) (H : gd z) :
      Height.IIDExpectedHittingTimeAtMost next hit z (4*n) := by
    rcases z with ⟨y,f⟩
    cases f
    · have C : ¬Clean (readClock p bytes y) := by
        intro C
        have E : false=true := H.2 C
        cases E
      have B := cleanBit_false _ C
      apply mean_in_height
      intro t
      have M := wire_warm_mean F a A D P y H.1 t
      rw [←warm_factor raw p bytes t y] at M
      simpa only [next,hit,warmInit,B] using M
    · intro t
      rw [Height.iidHitCost_of_target next hit (y,true) (show hit (y,true) from rfl)]
      exact Nat.zero_le _
  have I : gd (warmInit p bytes x) :=
    ⟨G,fun C=>(cleanBit_iff _).mpr C⟩
  have N : 0<4*n := by have := a.isLt; omega
  have B : 2*(4*n)≤3*n*(p.streak+2) := by
    calc
      _ = n*8 := by omega
      _ ≤ n*(3*(p.streak+2)) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ac_rfl
  -- CHECK: ReportHalfCellClock.lean: tail_from_uniform_mean; the
  -- predicate argument is the same FourLossStickyClock.badCount.
  exact ReportHalfCellClock.tail_from_uniform_mean next gd hit stay keep
    (4*n) N mean (warmInit p bytes x) I L j
    (Nat.le_trans (Nat.mul_le_mul_left _ B) fits)

-- Explicit round words on the original physical alphabet.
-- No physical mark is erased. A spectator may occur before the first
-- decision or anywhere while waiting for the opposite decision.
inductive Pending {n : Nat} (a b : Fin n) :
    Phase → List (Fin n) → Prop where
  | nil : Pending a b .empty []
  | quiet {ph w e} : Pending a b ph w → e≠a → e≠b →
      Pending a b ph (w++[e])
  | out {w} : Pending a b .empty w → Pending a b .outgoing (w++[b])
  | inc {w} : Pending a b .empty w → Pending a b .incoming (w++[a])
  | outAgain {w} : Pending a b .outgoing w →
      Pending a b .outgoing (w++[b])
  | inAgain {w} : Pending a b .incoming w →
      Pending a b .incoming (w++[a])

-- Each snoc adds one complete outgoing-first round: its actual final
-- incoming mark follows the open outgoing round, not an inherited race.
inductive Wins {n : Nat} (a b : Fin n) : Nat → List (Fin n) → Prop where
  | zero : Wins a b 0 []
  | snoc {k u v} : Wins a b k u → Pending a b .outgoing v →
      Wins a b (k+1) ((u++v)++[a])

def Fresh {n : Nat} (a b : Fin n) (J : Nat)
    (atZero : List (Fin n) → Prop) (w : List (Fin n)) (c : ReportPulseWait.State) : Prop :=
  c.count<J ∧ ∃ u v z, w=(u++v)++z ∧ atZero u ∧
    Wins a b c.count v ∧ Pending a b c.phase z

def Credit {n : Nat} (a b : Fin n) (J : Nat)
    (atZero : List (Fin n) → Prop) (w : List (Fin n)) : Prop :=
  ∃ u v, w=u++v ∧ atZero u ∧ Wins a b J v

theorem fresh_zero {n J : Nat} (a b : Fin n)
    (P : 0<J) (atZero : List (Fin n) → Prop) (w : List (Fin n))
    (U : atZero w) (h : Bool) :
    Fresh a b J atZero w ⟨.empty,0,h⟩ := by
  exact ⟨P,w,[],[],by simp,U,.zero,.nil⟩

/-- Deterministic ancestry on every physical mark. The reset premise
    is only the identification of the new clean endpoint, not an
    assumption that any particular mark is a reset or a win. -/
theorem fresh_step {n J : Nat} (a b e : Fin n) (D : a≠b)
    (P : 0<J) (atZero : List (Fin n) → Prop)
    (w : List (Fin n)) (ph : Phase) (k : Nat)
    (H : Fresh a b J atZero w ⟨ph,k,false⟩)
    (reset : (ReportPulseWait.step J a b e ⟨ph,k,false⟩).phase=.empty →
      (ReportPulseWait.step J a b e ⟨ph,k,false⟩).count=0 → atZero (w++[e])) :
    Fresh a b J atZero (w++[e]) (ReportPulseWait.step J a b e ⟨ph,k,false⟩) ∧
    ((ReportPulseWait.step J a b e ⟨ph,k,false⟩).hit=true →
      Credit a b J atZero (w++[e])) := by
  obtain ⟨K,u,v,z,E,U,V,Z⟩ := H
  change k<J at K
  change Wins a b k v at V
  change Pending a b ph z at Z
  have ke : effective J k=k := by simp [effective,K]
  have hold (ph' : Phase) (H' : Pending a b ph' (z++[e])) :
      Fresh a b J atZero (w++[e]) ⟨ph',k,false⟩ ∧
      ((⟨ph',k,false⟩ : ReportPulseWait.State).hit=true →
        Credit a b J atZero (w++[e])) := by
    refine ⟨⟨K,u,v,z++[e],?_,U,V,H'⟩,?_⟩
    · rw [E]
      simp [List.append_assoc]
    · intro Hbad
      cases Hbad
  by_cases A : e=a
  · subst e
    cases ph with
    | empty =>
      simpa [ReportPulseWait.step,side] using hold .incoming (.inc Z)
    | incoming =>
      simpa [ReportPulseWait.step,side] using hold .incoming (.inAgain Z)
    | outgoing =>
      have W : Wins a b (k+1) ((v++z)++[a]) := .snoc V Z
      have T : w++[a]=u++((v++z)++[a]) := by
        rw [E]
        simp [List.append_assoc]
      by_cases C : k+1=J
      · have S : ReportPulseWait.step J a b a ⟨.outgoing,k,false⟩ =
            ⟨.empty,0,true⟩ := by simp [ReportPulseWait.step,side,ke,C]
        have R := reset (by rw [S]) (by rw [S])
        rw [S]
        refine ⟨fresh_zero a b P atZero _ R true,?_⟩
        intro _
        exact ⟨u,_,T,U,by simpa [C] using W⟩
      · have K' : k+1<J := by omega
        have S : ReportPulseWait.step J a b a ⟨.outgoing,k,false⟩ =
            ⟨.empty,k+1,false⟩ := by simp [ReportPulseWait.step,side,ke,C]
        rw [S]
        refine ⟨⟨K',u,((v++z)++[a]),[],?_,U,W,.nil⟩,?_⟩
        · simpa using T
        · intro Hbad
          cases Hbad
  · by_cases B : e=b
    · subst e
      cases ph with
      | empty =>
        simpa [ReportPulseWait.step,side,D.symm] using hold .outgoing (.out Z)
      | outgoing =>
        simpa [ReportPulseWait.step,side,D.symm] using hold .outgoing (.outAgain Z)
      | incoming =>
        have S : ReportPulseWait.step J a b b ⟨.incoming,k,false⟩ =
            ⟨.empty,0,false⟩ := by simp [ReportPulseWait.step,side,D.symm]
        have R := reset (by rw [S]) (by rw [S])
        rw [S]
        refine ⟨fresh_zero a b P atZero _ R false,?_⟩
        intro Hbad
        cases Hbad
    · simpa [ReportPulseWait.step,A,B] using hold ph (.quiet Z A B)

-- The certificate really describes the race machine from an empty
-- boundary; it is not just a numeric counter tag.
theorem pending_run {n J : Nat} (a b : Fin n) (D : a≠b)
    {ph : Phase} {w : List (Fin n)} (H : Pending a b ph w)
    (k : Nat) (h : Bool) :
    w.foldl (fun y e=>ReportPulseWait.step J a b e y) ⟨.empty,k,h⟩ = ⟨ph,k,h⟩ := by
  -- CHECK: core List.foldl_append simplification, same convention as
  -- ReportStickyRawCover.lean:158 and ReportWindowCounts.lean:35–36.
  induction H <;> simp_all [List.foldl_append,ReportPulseWait.step,side,D.symm]

theorem wins_run {n J : Nat} (a b : Fin n) (D : a≠b) (P : 0<J)
    {k : Nat} {w : List (Fin n)} (W : Wins a b k w) (K : k≤J) :
    w.foldl (fun y e=>ReportPulseWait.step J a b e y) ⟨.empty,0,false⟩ =
      if k=J then ⟨.empty,0,true⟩ else ⟨.empty,k,false⟩ := by
  induction W with
  | zero =>
    simp [show (0:Nat)≠J by omega]
  | @snoc k u v W Z ih =>
    have L : k<J := by omega
    have T := ih (Nat.le_of_lt L)
    rw [if_neg (Nat.ne_of_lt L)] at T
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [T,pending_run (J:=J) a b D Z k false]
    by_cases C : k+1=J <;> simp [ReportPulseWait.step,side,effective,L,C]

-- The actual clean state at the start of the certified suffix.
def cleanAt {X : Type} {n : Nat} (raw : X → Fin n → X)
    (p : Params) (bytes : X → BitVec p.w) (base : X)
    (u : List (Fin n)) : Prop :=
  Clean (readClock p bytes (u.foldl raw base))

/-- This is the all-mark invariant for a literal raw tape with a fixed
    post-warm base. The raw event is evaluated on the OLD actual bytes. -/
theorem wire_fresh_mark {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (base : X) (G : Q base) (w : List (Fin n)) (e : Fin n)
    (H : Fresh a b p.streak (cleanAt raw p bytes base) w
      (readClock p bytes (w.foldl raw base))) :
    Fresh a b p.streak (cleanAt raw p bytes base) (w++[e])
        (readClock p bytes ((w++[e]).foldl raw base)) ∧
    (countedPaint b p bytes (w.foldl raw base) e=true →
      Credit a b p.streak (cleanAt raw p bytes base) (w++[e])) := by
  let y := w.foldl raw base
  have Y : Q y := wire_run_good F base w G
  have E : ReportPulseDecode.state p (bytes (raw y e))
      (countedPaint b p bytes y e) =
      ReportPulseWait.step p.streak a b e (readClock p bytes y) := by
    simpa only [Bool.false_or,readClock] using
      wire_clock_eq F a A D P y e false Y
  have reset
      (Hph : (ReportPulseWait.step p.streak a b e (readClock p bytes y)).phase=.empty)
      (Hk : (ReportPulseWait.step p.streak a b e (readClock p bytes y)).count=0) :
      cleanAt raw p bytes base (w++[e]) := by
    rw [←E] at Hph Hk
    simp only [cleanAt,List.foldl_append,List.foldl_cons,List.foldl_nil,
      readClock,Clean]
    exact ⟨Hph,Hk⟩
  have S := fresh_step a b e D P (cleanAt raw p bytes base) w
    (ReportPulseDecode.phase p (bytes y))
    (ReportPulseDecode.count p (bytes y)) H reset
  change Fresh a b p.streak (cleanAt raw p bytes base) (w++[e])
      (ReportPulseWait.step p.streak a b e (readClock p bytes y)) ∧
    ((ReportPulseWait.step p.streak a b e (readClock p bytes y)).hit=true →
      Credit a b p.streak (cleanAt raw p bytes base) (w++[e])) at S
  rw [←E] at S
  have V : Fresh a b p.streak (cleanAt raw p bytes base) (w++[e])
      (readClock p bytes (raw y e)) := S.1
  constructor
  · simpa only [List.foldl_append,List.foldl_cons,List.foldl_nil,y] using V
  · intro C
    exact S.2 C

theorem wire_fresh_extend {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (base : X) (G : Q base) (w v : List (Fin n))
    (H : Fresh a b p.streak (cleanAt raw p bytes base) w
      (readClock p bytes (w.foldl raw base))) :
    Fresh a b p.streak (cleanAt raw p bytes base) (w++v)
      (readClock p bytes ((w++v).foldl raw base)) := by
  induction v generalizing w with
  | nil => simpa using H
  | cons e v ih =>
    have M := (wire_fresh_mark F a A D P base G w e H).1
    have T := ih (w++[e]) M
    simpa [List.append_assoc] using T

theorem wire_fresh_from_clean {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (base : X) (G : Q base) (C : Clean (readClock p bytes base))
    (v : List (Fin n)) :
    Fresh a b p.streak (cleanAt raw p bytes base) v
      (readClock p bytes (v.foldl raw base)) := by
  have E : readClock p bytes base=⟨.empty,0,false⟩ := by
    rcases C with ⟨Cph,Ck⟩
    -- The readClock hit field is definitionally false.
    unfold readClock ReportPulseDecode.state at *
    simp_all
  have H : Fresh a b p.streak (cleanAt raw p bytes base) []
      (readClock p bytes (([] : List (Fin n)).foldl raw base)) := by
    change Fresh a b p.streak (cleanAt raw p bytes base) []
      (readClock p bytes base)
    rw [E]
    exact fresh_zero a b P _ [] (show cleanAt raw p bytes base [] from C) false
  simpa using wire_fresh_extend F a A D P base G [] v H

/-- Consumer: u is the first clean cut on the actual tape, v the full
    intervening raw tape, and e the next physical mark. No inherited
    event at the cut itself is credited. -/
theorem wire_cut_adapter {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (x : X) (G : Q x) (u v : List (Fin n)) (e : Fin n)
    (cut : FirstCut raw (fun y=>Clean (readClock p bytes y)) x u) :
    let base := u.foldl raw x
    Fresh a b p.streak (cleanAt raw p bytes base) v
        (readClock p bytes (v.foldl raw base)) ∧
    Fresh a b p.streak (cleanAt raw p bytes base) (v++[e])
        (readClock p bytes ((v++[e]).foldl raw base)) ∧
    (countedPaint b p bytes (v.foldl raw base) e=true →
      Credit a b p.streak (cleanAt raw p bytes base) (v++[e])) := by
  let base := u.foldl raw x
  have B : Q base := wire_run_good F x u G
  have C : Clean (readClock p bytes base) := firstCut_clean cut
  have H := wire_fresh_from_clean F a A D P base B C v
  exact ⟨H,wire_fresh_mark F a A D P base B v e H⟩

/-- A credited suffix is an actual raw run from an actual clean old
    endpoint. This exposes the normalized final state with a fresh
    event latch, as well as the raw endpoint projection. -/
theorem credit_raw_run {X : Type} {n : Nat}
    {raw : X → Fin n → X} {b : Fin n} {Q : X → Prop}
    {p : Params} {bytes : X → BitVec p.w}
    (F : Wire raw b Q p bytes) (a : Fin n)
    (A : rightNeighbor a=b) (D : a≠b) (P : 0<p.streak)
    (base : X) (G : Q base) (w : List (Fin n))
    (C : Credit a b p.streak (cleanAt raw p bytes base) w) :
    ∃ u v, w=u++v ∧ cleanAt raw p bytes base u ∧
      Wins a b p.streak v ∧
      let start := u.foldl raw base
      let z := v.foldl (monitor raw (countedPaint b p bytes)) (start,false)
      z.1=w.foldl raw base ∧
        ReportPulseDecode.state p (bytes z.1) z.2=⟨.empty,0,true⟩ := by
  obtain ⟨u,v,E,U,V⟩ := C
  let start := u.foldl raw base
  have B : Q start := wire_run_good F base u G
  have K : ReportPulseDecode.state p (bytes start) false =
      ⟨.empty,0,false⟩ := by
    have H : Clean (readClock p bytes start) := U
    rcases H with ⟨Hph,Hk⟩
    unfold readClock ReportPulseDecode.state at *
    simp_all
  refine ⟨u,v,E,U,V,?_,?_⟩
  · rw [monitor_base,E,List.foldl_append]
  · have T := wire_run_eq F a A D P start v false B
    rw [K,wins_run a b D P V (Nat.le_refl _),if_pos rfl] at T
    exact T

-- Literal report1/report2 wire constructors, exactly the premises of
-- the already compiled report1_mean/report2_mean.
theorem wire1 {s n : Nat} (b : Fin n)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h4=true) :
    Wire (rawNext s) b Q (P1 s) (fun x=>(x b).report1) := by
  refine ⟨stay,?_⟩
  intro y e i hy I
  have E := report1_pulse_raw y e b i I
  rw [frozen y hy] at E
  exact E

theorem wire2 {s n : Nat} (b : Fin n)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h5=true) :
    Wire (rawNext s) b Q (P2 s) (fun x=>(x b).report2) := by
  refine ⟨stay,?_⟩
  intro y e i hy I
  have E := report2_pulse_raw y e b i I
  rw [frozen y hy] at E
  exact E

theorem streak_pos (r : Nat) : 0<streak r := by
  unfold streak
  exact Nat.lt_of_lt_of_le (show 0 < 45 from by decide)
    (Nat.le_trans (Nat.le_add_left 45 _) (Nat.le_add_right _ _))

theorem report1_warm_mean {s n : Nat} (a b : Fin n)
    (A : rightNeighbor a=b) (D : a≠b)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h4=true)
    (x : Raw s n) (G : Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y=>Clean (readClock (P1 s) (fun z=>(z b).report1) y))
      x (4*n) :=
  wire_warm_mean (wire1 b Q stay frozen) a A D (streak_pos s) x G

theorem report2_warm_mean {s n : Nat} (a b : Fin n)
    (A : rightNeighbor a=b) (D : a≠b)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h5=true)
    (x : Raw s n) (G : Q x) :
    L4.IIDExpectedHittingTimeAtMost (rawNext s)
      (fun y=>Clean (readClock (P2 s) (fun z=>(z b).report2) y))
      x (4*n) :=
  wire_warm_mean (wire2 b Q stay frozen) a A D
    (streak_pos (radiusTwo s)) x G

theorem report1_cut_adapter {s n : Nat} (a b : Fin n)
    (A : rightNeighbor a=b) (D : a≠b)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h4=true)
    (x : Raw s n) (G : Q x) (u v : List (Fin n)) (e : Fin n)
    (cut : FirstCut (rawNext s)
      (fun y=>Clean (readClock (P1 s) (fun z=>(z b).report1) y)) x u) :
    let base := u.foldl (rawNext s) x
    Fresh a b (streak s)
      (cleanAt (rawNext s) (P1 s) (fun z=>(z b).report1) base) v
      (readClock (P1 s) (fun z=>(z b).report1) (v.foldl (rawNext s) base)) ∧
    Fresh a b (streak s)
      (cleanAt (rawNext s) (P1 s) (fun z=>(z b).report1) base) (v++[e])
      (readClock (P1 s) (fun z=>(z b).report1) ((v++[e]).foldl (rawNext s) base)) ∧
    (countedPaint b (P1 s) (fun z=>(z b).report1) (v.foldl (rawNext s) base) e=true →
      Credit a b (streak s)
        (cleanAt (rawNext s) (P1 s) (fun z=>(z b).report1) base) (v++[e])) :=
  wire_cut_adapter (wire1 b Q stay frozen) a A D (streak_pos s) x G u v e cut

theorem report2_cut_adapter {s n : Nat} (a b : Fin n)
    (A : rightNeighbor a=b) (D : a≠b)
    (Q : Raw s n → Prop) (stay : ∀ x e, Q x → Q (rawNext s x e))
    (frozen : ∀ x, Q x → (oldHeaders (rows s) (x b)).h5=true)
    (x : Raw s n) (G : Q x) (u v : List (Fin n)) (e : Fin n)
    (cut : FirstCut (rawNext s)
      (fun y=>Clean (readClock (P2 s) (fun z=>(z b).report2) y)) x u) :
    let base := u.foldl (rawNext s) x
    Fresh a b (streak (radiusTwo s))
      (cleanAt (rawNext s) (P2 s) (fun z=>(z b).report2) base) v
      (readClock (P2 s) (fun z=>(z b).report2) (v.foldl (rawNext s) base)) ∧
    Fresh a b (streak (radiusTwo s))
      (cleanAt (rawNext s) (P2 s) (fun z=>(z b).report2) base) (v++[e])
      (readClock (P2 s) (fun z=>(z b).report2) ((v++[e]).foldl (rawNext s) base)) ∧
    (countedPaint b (P2 s) (fun z=>(z b).report2) (v.foldl (rawNext s) base) e=true →
      Credit a b (streak (radiusTwo s))
        (cleanAt (rawNext s) (P2 s) (fun z=>(z b).report2) base) (v++[e])) :=
  wire_cut_adapter (wire2 b Q stay frozen) a A D
    (streak_pos (radiusTwo s)) x G u v e cut

end L4.ReportPulseWarmup

