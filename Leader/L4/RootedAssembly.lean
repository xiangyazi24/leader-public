import Leader.L4.SevenTagCharge
import Leader.L4.Count
import Leader.L4.RearDebt
import Leader.L4.RootedSingleton
import Leader.L4.RootedEntrance

/-! Downstream composition on every ring with a pre-cover
decoded identity. G6 and G7 are stated at the actual unrestricted
modulus domain, not borrowed from the nondivisible headline. -/
namespace L4.RootedAssembly
open TaggedTail RankRenewal RankPhysical TripleRenewal Classical RankBlockContraction SevenTagCharge

/-- The global first-retirement input on the closed quiet domain. -/
def RootedBoundedRank : Prop :=
  ∀ c : Nat, 12≤c → ∃ A : Nat, ∀ {p n : Nat} (x : Config p c n),
    2≤p → 4≤n → QuietEntrance x → 2≤rank x →
      IIDExpectedHittingTimeAtMost step (fun y => rank y<rank x) x (A*n^2)

def wordNext {n : Nat} (w : List (Fin n)) (e : Fin n) : List (Fin n) := w++[e]

def reward {p c n : Nat} (x : Config p c n) (w0 w : List (Fin n)) : Nat :=
  (hit (observe (initial x) w).losses w0).toNat

/-- A chosen cyclic roster/filter and its marginal trial results.
The literal common schedule and all pointwise retirement incidence
are derived rather than fields. -/
structure WindowMarginals {p c n : Nat} (x : Config p c n) (H T : Nat) where
  k : Nat
  roster : Fin k → Fin n
  inj : ∀ i j, roster i = roster j → i=j
  starts : List (Fin k)
  nodup : starts.Nodup
  many : rank x≤starts.length+H
  trial : ∀ i ∈ starts, 12*n^T≤25*endpointSum wordNext
      (reward x (window7 roster i)) T []

/-- Last-two certificate on the original raw word. The loss is
recorded only when one of this window's original tags disappears,
and all such windows use this same transition. -/
def of_marginals {p c n : Nat} {x : Config p c n} {H T : Nat}
    (hn : 4≤n) (hq : QuietEntrance x) (z : WindowMarginals x H T) :
    GroupRewardCertificate x H T := by
  let groups := z.starts.map (window7 z.roster)
  refine { State := List (Fin n)
           start := []
           next := wordNext
           project := run x
           initial := rfl
           projects := fun w e => run_append x w [e]
           events := groups.map (reward x)
           many := by simpa [groups] using z.many
           success := ?_
           incidence := ?_ }
  · intro f hf
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hf
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    exact z.trial i hi
  · intro w
    have h7 := windows7_multiplicity z.roster z.inj z.starts z.nodup
    have h := physical_incidence x hn hq.1 hq.2.1 w groups h7
    change 7*rank (run x w) + ((groups.map (reward x)).map (fun f => f w)).sum ≤ _
    simpa only [List.map_map,Function.comp_def, reward,hits] using h

/-- The local window input after removal of artificial divisibility. -/
def RootedWindowMarginals : Prop :=
  ∀ c : Nat, 12≤c → ∃ B C₀ : Nat, 0<B ∧ 0<C₀ ∧
    ∀ (n L : Nat), 4≤n → 1≤L → L≤n →
    ∃ H : Nat, H*L≤C₀*n ∧
      ∀ {p : Nat} (x : Config p c n), 2≤p → QuietEntrance x →
        Nonempty (WindowMarginals x H (B*n*L))

/-- A stage closure parameter is threaded through the arithmetic, not
assumed by the public rooted theorem. -/
def QuietClosed (p c n : Nat) : Prop :=
  ∀ (x : Config p c n) e, QuietEntrance x → QuietEntrance (step x e)

private def rootedStage {p c n : Nat} (x : Config p c n)
    (hQ : QuietClosed p c n) (hx : QuietEntrance x)
    (ready : Config p c n → Prop) : Stage step x where
  State := Config p c n
  start := x
  next := step
  project := id
  ready := ready
  reachable := QuietEntrance
  projInit := rfl
  projStep := fun _ _ => rfl
  reachStart := hx
  reachStep := fun y e hy => hQ y e hy

/-- Exact one-slab dyadic contraction on physical marks. -/
theorem rooted_half_mean {p c n : Nat} (x : Config p c n)
    (hQ : QuietClosed p c n) (hn : 4≤n) (hx : QuietEntrance x)
    (B C₀ r L : Nat) (hB : 0<B) (hr : 0<r) (hL : 0<L) 
    (hR : rank x≤r) (hscale : 8*C₀*n≤L*r)
    (blocks : ∀ y : Config p c n, QuietEntrance y →
      4*L*endpointSum step rank (B*n*L) y ≤
        (L*rank y+4*C₀*n)*n^(B*n*L)) :
    IIDExpectedHittingTimeAtMost step (fun y => rank y≤r/2) x (4*(B*n*L)) := by
  let S := {y : Config p c n // QuietEntrance y ∧ rank y≤r}
  let lift (y : S) (e : Fin n) : S :=
    ⟨step y.val e,hQ y.val e y.property.1,
      Nat.le_trans (rank_step_le hn y.val e y.property.1.1) y.property.2⟩
  let start : S := ⟨x,hx,hR⟩
  have hh := halfMean lift (fun y => rank y.val) r (B*n*L)
    (Nat.mul_pos (Nat.mul_pos hB (by omega)) hL)
    (fun y e => rank_step_le hn y.val e y.property.1.1) (fun y _ => by
      rw [equal_survival_of_projection step lift (fun z => r/2<rank z)
        (fun z : S => z.val) (fun _ _ => rfl)]
      exact halfBlock_of_affine step rank y.val r L C₀ (B*n*L) hr hL y.property.2 hscale
        (blocks y.val y.property.1)) start
  intro t
  have h := EntranceCover.iidHitCost_le_of_projection step lift
    (fun y => rank y≤r/2) (fun y : S => rank y.val≤r/2)
    (fun y : S => y.val) (fun _ _ => rfl) (fun _ h => h) t start
  exact Nat.le_trans h (hh t)

/-- At most r whole-ring first-retirement trials pay for all remaining
rank changes when the current rank is ≤r. In the dyadic proof r will
be an absolute cutoff, not the initial rank n. -/
theorem rooted_small_rank_cost {p c n : Nat} (hQ : QuietClosed p c n)
    (A : Nat) (retire : ∀ y : Config p c n, QuietEntrance y → 2≤rank y →
      IIDExpectedHittingTimeAtMost step (fun z => rank z<rank y) y (A*n^2))
    (r : Nat) (x : Config p c n) (hx : QuietEntrance x) (hxR : rank x≤r) :
    IIDExpectedHittingTimeAtMost step (fun y => rank y=1) x ((A*n^2)*r) := by
  induction r generalizing x with
  | zero => have h := quiet_rank_pos hx; omega
  | succ r ih =>
    by_cases he : rank x=1
    · intro t; rw [iidHitCost_of_target step (fun y => rank y=1) x he]; exact Nat.zero_le _
    · have h2 : 2≤rank x := by have h := quiet_rank_pos hx; omega
      let s := rootedStage x hQ hx (fun z => rank z<rank x)
      have hh := expected_with_preparation s (fun z => rank z=1) (A*n^2) ((A*n^2)*r)
        (retire x hx h2) (fun y hy hReady _ => ih y hy (by change rank y<rank x at hReady; omega))
      refine expected_mono hh ?_
      rw [Nat.mul_succ,Nat.add_comm]
      exact Nat.le_refl _

private theorem pow2_pos (j : Nat) : 0 < (2 : Nat)^j := Nat.pow_pos (by decide)

private theorem div_half (n j : Nat) :
    n/2^(j+1) = (n/2^j)/2 := by rw [Nat.pow_succ,Nat.div_div_eq_div_mul]

private theorem dyadic_budget (n j : Nat) :
    (n/2^(j+1)+1)+(n-n/2^j+j) ≤ n-n/2^(j+1)+(j+1) := by
  have hj := Nat.div_le_self n (2^j)
  have hk := Nat.div_le_self n (2^(j+1))
  have h := Nat.mul_div_le (n/2^j) 2
  rw [div_half]
  rw [div_half] at hk
  omega

private theorem scale_ge (n M j : Nat) :
    M*n ≤ (n/2^(j+1)+1)*(M*2^(j+1)) := by
  have hh : n≤(n/2^(j+1)+1)*2^(j+1) := by
    have h := Nat.mod_add_div n (2^(j+1))
    have hh := Nat.mod_lt n (pow2_pos (j+1))
    rw [Nat.add_mul,Nat.one_mul]
    rw [Nat.mul_comm (n/2^(j+1)) (2^(j+1))]
    omega
  calc
    _ ≤ M*((n/2^(j+1)+1)*2^(j+1)) := Nat.mul_le_mul_left M hh
    _ = _ := by ac_rfl

private theorem pow2_ge (n : Nat) : n≤(2:Nat)^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := pow2_pos n
    rw [Nat.pow_succ]
    omega

/-- Dyadic absorption with an explicit paper-style coefficient. The
scales are L_j=floor(n/2^j)+1, with rank caps (8*C₀)*2^j.
Starting at j=n is safe and the summable cost still follows from exact
integer telescoping; the many vacuous large caps cost nothing in reality. -/
theorem rooted_rankOne_mean_of_local_data {p c n : Nat} (x : Config p c n)
    (hQ : QuietClosed p c n) (hn : 4≤n) (hx : QuietEntrance x)
    (A B C₀ : Nat) (hB : 0<B) (hC : 0<C₀)
    (retire : ∀ y : Config p c n, QuietEntrance y → 2≤rank y →
      IIDExpectedHittingTimeAtMost step (fun z => rank z<rank y) y (A*n^2))
    (blocks : ∀ (y : Config p c n) (L : Nat), QuietEntrance y → 1≤L → L≤n →
      4*L*endpointSum step rank (B*n*L) y ≤ (L*rank y+4*C₀*n)*n^(B*n*L)) :
    IIDExpectedHittingTimeAtMost step (fun y => rank y=1) x ((8*B+8*C₀*A)*n^2) := by
  let M := 8*C₀
  let q := (A*n^2)*M
  let b := 4*B*n
  have hM : 0<M := by dsimp [M]; omega
  have stages (j : Nat) (z : Config p c n) (hz : QuietEntrance z) (hr : rank z≤M*2^j) :
      IIDExpectedHittingTimeAtMost step (fun y => rank y=1) z (b*(n-n/2^j+j)+q) := by
    induction j generalizing z with
    | zero =>
      simp only [Nat.pow_zero,Nat.div_one,Nat.sub_self,Nat.add_zero,Nat.mul_zero,Nat.zero_add] at *
      exact rooted_small_rank_cost hQ A retire M z hz (by simpa using hr)
    | succ j ih =>
      let r := M*2^(j+1)
      let L := n/2^(j+1)+1
      have hL : 0<L := Nat.succ_pos _
      have hLn : L ≤ n := by
        have hp2 : 1 < (2:Nat)^(j+1) := by
          have hpos := pow2_pos j
          rw [Nat.pow_succ]; omega
        have hh := Nat.div_lt_self (by omega : 0<n) hp2
        dsimp [L]
        omega
      have hR : 0<r := Nat.mul_pos hM (pow2_pos (j+1))
      have hs : 8*C₀*n≤L*r := scale_ge n M j
      have half := rooted_half_mean z hQ hn hz B C₀ r L hB hR hL hr hs
        (fun y hy => blocks y L hy hL hLn)
      let s := rootedStage z hQ hz (fun y => rank y≤r/2)
      have he : r/2=M*2^j := by
        dsimp [r]
        rw [Nat.pow_succ,←Nat.mul_assoc,Nat.mul_div_left _ (by decide)]
      have recomp := expected_with_preparation s (fun y => rank y=1) (4*(B*n*L))
        (b*(n-n/2^j+j)+q) half (fun y hy hr' _ =>
          ih y hy (by change rank y≤r/2 at hr'; rwa [he] at hr'))
      refine expected_mono recomp ?_
      have hbudget := Nat.mul_le_mul_left b (dyadic_budget n j)
      rw [Nat.mul_add] at hbudget
      calc
        _ = (b*L+b*(n-n/2^j+j))+q := by
          have h : 4*(B*n*L)=b*L := by dsimp [b]; ac_rfl
          rw [h,Nat.add_assoc]
        _ ≤ b*(n-n/2^(j+1)+(j+1))+q := Nat.add_le_add_right hbudget _
  have hxR : rank x≤M*2^n :=
    Nat.le_trans (rank_le_size x) (Nat.le_trans (pow2_ge n) (Nat.le_mul_of_pos_left _ hM))
  refine expected_mono (stages n x hx hxR) ?_
  have hbnd : n-n/2^n+n≤2*n := by
    rw [Nat.two_mul]; exact Nat.add_le_add_right (Nat.sub_le ..) _
  calc
    _ ≤ b*(2*n)+q := Nat.add_le_add_right (Nat.mul_le_mul_left _ hbnd) _
    _ = (8*B+8*C₀*A)*n^2 := by
      dsimp [b,q,M]
      rw [Nat.pow_two,Nat.add_mul]
      have he : 4*B*n*(2*n) = (4*2)*B*(n*n) := by ac_rfl
      rw [he,show (4:Nat)*2=8 by decide]
      congr 1
      ac_rfl

private theorem eProjection {α β : Type} {n : Nat} (next : α → Fin n → α)
    (lift : β → Fin n → β) (f : α → Nat) (proj : β → α)
    (h : ∀ z e, proj (lift z e)=next (proj z) e) (T : Nat) (x : β) :
    endpointSum lift (fun z => f (proj z)) T x = endpointSum next f T (proj x) := by
  induction T generalizing x with
  | zero => rfl
  | succ T ih =>
    simp only [endpointSum,ih,h]

/-- Convert the rooted same-word group certificates to the literal
rank endpoint, with the existing affine averaging and 32-fold block. -/
theorem rooted_block_of_groups {p c n : Nat} (hQ : QuietClosed p c n)
    (x : Config p c n) (hx : QuietEntrance x) (B C₀ L H : Nat)
    (hHL : H*L≤C₀*n)
    (group : ∀ y : Config p c n, QuietEntrance y →
      Nonempty (GroupRewardCertificate y H (B*n*L))) :
    4*L*endpointSum step rank ((32*B)*n*L) x ≤
      (L*rank x+4*C₀*n)*n^((32*B)*n*L) := by
  let S := { y : Config p c n // QuietEntrance y }
  let lift (y : S) (e : Fin n) : S :=
    ⟨step y.val e,hQ y.val e y.property⟩
  let start : S := ⟨x,hx⟩
  have one (y : S) : 175*endpointSum lift (fun z => rank z.val) (B*n*L) y≤
      (163*rank y.val+12*H)*n^(B*n*L) := by
    obtain ⟨o⟩ := group y.val y.property
    have hg := one_block_of_group_rewards o.next (fun z => rank (o.project z))
      o.start H (B*n*L) o.events (by rw [o.initial]; exact o.many) o.success
      (fun z => by simpa only [o.initial] using o.incidence z)
    rw [eProjection step o.next rank o.project o.projects,o.initial] at hg
    rw [eProjection step lift rank (fun z : S => z.val) (fun _ _ => rfl)]
    exact hg
  have hh := affine_of_group_blocks lift (fun z => rank z.val) (B*n*L) H L C₀ one hHL start
  rw [eProjection step lift rank (fun z : S => z.val) (fun _ _ => rfl)] at hh
  simpa only [start,Nat.mul_assoc] using hh


open RootedEntrance in
/-- The former cyclic-sum assumption furnishes the decoded witness even
before any ordered cover, because absence of every decoded root makes
MCOV vacuous. -/
theorem rootNonempty_of_not_dvd {p c n : Nat} (x : Config p c n)
    (hn : 4≤n) (hnd : ¬p∣n) : RootNonempty x := by
  exact rooted_of_not_dvd (by omega) x hnd

/-- The all-size public export required at H5: arbitrary native bytes
with a decoded leader, explicit mark, or residue defect, no MCOV
precondition. C is uniform in p, n, and state, for each fixed c. -/
def RootedStatement : Prop :=
  ∀ c : Nat, 12≤c → ∃ C : Nat, ∀ {p n : Nat} (x : Config p c n),
    2≤p → 4≤n → RootedEntrance.RootNonempty x →
      IIDExpectedHittingTimeAtMost step SafeOneLeader x (C*n^2)

/-- The original headline is a mathematical consequence of the rooted
export and the cyclic-sum argument; choose its Cpat conservatively. -/
theorem headline_of_rooted (h : RootedStatement) : row175Statement := by
  intro c hc
  obtain ⟨C,hC⟩ := h c hc
  refine ⟨C,?_⟩
  intro p hp
  refine ⟨stateCount_headline p c,?_⟩
  intro n hn hnd x
  have hh : C*n^2≤(2049+C)*n^2 := Nat.mul_le_mul_right _ (by omega)
  exact expected_mono (hC x hp hn (rootNonempty_of_not_dvd x hn hnd)) hh

private def cutStage {p c n : Nat} (x : Config p c n)
    (reach ready : Config p c n → Prop) (hx : reach x)
    (h : ∀ y e, reach y → reach (step y e)) : Stage step x :=
  ⟨Config p c n,x,step,id,ready,reach,rfl,fun _ _ => rfl,hx,h⟩

/-- All post-cover stages, at the original raw-mark law, use no residue
divisibility. The first-retirement and short-window premises are the
only retained scheduling estimates in this part. -/
theorem rooted_tail_of_windows {p c n : Nat}
    (x : Config p c n) (hn : 4≤n) (hQ : QuietClosed p c n) (hx : QuietEntrance x)
    (A B C₀ S : Nat) (hB : 0<B) (hC : 0<C₀)
    (retire : ∀ y : Config p c n, QuietEntrance y → 2≤rank y →
      IIDExpectedHittingTimeAtMost step (fun z => rank z<rank y) y (A*n^2))
    (group : ∀ (L : Nat), 1≤L → L≤n →
      ∃ H, H*L≤C₀*n ∧ ∀ y : Config p c n, QuietEntrance y →
        Nonempty (WindowMarginals y H (B*n*L)))
    (finish : ∀ y : Config p c n, QuietEntrance y → rank y=1 →
      IIDExpectedHittingTimeAtMost step SafeOneLeader y (S*n^2)) :
    IIDExpectedHittingTimeAtMost step SafeOneLeader x
      ((8*(32*B)+8*C₀*A+S)*n^2) := by
  have block (y : Config p c n) (L : Nat) (hy : QuietEntrance y) (hL : 1≤L) (hLn : L≤n) :
      4*L*endpointSum step rank (32*B*n*L) y ≤ (L*rank y+4*C₀*n)*n^(32*B*n*L) := by
    obtain ⟨H,hHL,h⟩ := group L hL hLn
    apply rooted_block_of_groups hQ y hy B C₀ L H hHL
    intro z hz
    obtain ⟨w⟩ := h z hz
    exact ⟨of_marginals hn hz w⟩
  let s := cutStage x QuietEntrance (fun z => rank z=1) hx hQ
  have pre := rooted_rankOne_mean_of_local_data x hQ hn hx A (32*B) C₀ (by omega) hC retire block
  have hh := expected_with_preparation s SafeOneLeader _ (S*n^2) pre
    (fun y hy hr _ => finish y hy hr)
  simpa only [Nat.add_mul] using hh

/-- Generic public connection of the rooted entrance and downstream
linear-time-per-site budget. Its entrance input admits every decoded
root state, with no normalized-byte premise. -/
theorem rooted_of_stage_means
    (retirement : RootedBoundedRank) (marginal : RootedWindowMarginals)
    (closed : ∀ {p c n}, 2≤p → 12≤c → 4≤n → QuietClosed p c n)
    (entrance : ∀ {p c n} (x : Config p c n), 2≤p → 12≤c → 4≤n →
      RootedEntrance.RootNonempty x →
      IIDExpectedHittingTimeAtMost step QuietEntrance x (2049*n^2))
    (finish : ∀ {p c n} (x : Config p c n), 2≤p → 12≤c → 4≤n →
      QuietEntrance x → rank x=1 →
      IIDExpectedHittingTimeAtMost step SafeOneLeader x ((17+64*(2*c+1))*n^2)) :
    RootedStatement := by
  intro c hc
  obtain ⟨A,hA⟩ := retirement c hc
  obtain ⟨B,C₀,hB,hC,hG⟩ := marginal c hc
  refine ⟨2049+(8*(32*B)+8*C₀*A+(17+64*(2*c+1))),?_⟩
  intro p n x hp hn hx
  let s := cutStage x (fun _ => True) QuietEntrance trivial (fun _ _ _ => trivial)
  have hh := expected_with_preparation s SafeOneLeader (2049*n^2) _
    (entrance x hp hc hn hx) (by
      intro y _ hy _
      exact rooted_tail_of_windows y hn (closed hp hc hn) hy
        A B C₀ (17+64*(2*c+1)) hB hC (fun z hz hr => hA z hp hn hz hr)
        (by
          intro L hL hLn
          obtain ⟨H,hHL,h⟩ := hG n L hn hL hLn
          exact ⟨H,hHL,fun z hz => h z hp hz⟩)
        (fun z hz hr => finish z hp hc hn hz hr))
  simpa only [Nat.add_mul] using hh

/-- The remaining entrance adapter is temporary: the rooted quiet
closure and rank-one finish are supplied by checked literal lemmas. -/
theorem row175_rooted_of_entrance
    (entrance : ∀ {p c n} (x : Config p c n), 2≤p → 12≤c → 4≤n →
      RootedEntrance.RootNonempty x →
      IIDExpectedHittingTimeAtMost step QuietEntrance x (2049*n^2))
    (retirement : RootedBoundedRank) (marginal : RootedWindowMarginals) : RootedStatement :=
  rooted_of_stage_means retirement marginal
    (fun hp hc hn x e h => RootedFresh.quiet_step x e hp hc hn h)
    entrance RootedSingleton.singletonSafeMean

end L4.RootedAssembly

#print axioms L4.RootedAssembly.rootNonempty_of_not_dvd
#print axioms L4.RootedAssembly.headline_of_rooted
#print axioms L4.RootedAssembly.rooted_tail_of_windows
#print axioms L4.RootedAssembly.rooted_of_stage_means

#print axioms L4.RootedAssembly.row175_rooted_of_entrance

namespace L4

/-- The public headline after H5 hands off any nonempty decoded root set.
The only remaining inputs are the rooted G6 retirement and G7
seven-window estimates. In particular neither the entrance nor the
tail assumes that p does not divide n. -/
theorem row175_rooted (retirement : RootedAssembly.RootedBoundedRank)
    (marginal : RootedAssembly.RootedWindowMarginals) :
    RootedAssembly.RootedStatement :=
  RootedAssembly.row175_rooted_of_entrance rooted_rear_entrance_printed retirement marginal

/-- Recover the original nondivisible statement, including its exact
finite alphabet, by supplying the cyclic-sum witness to row175_rooted. -/
theorem row175Statement_of_rooted_stages (retirement : RootedAssembly.RootedBoundedRank)
    (marginal : RootedAssembly.RootedWindowMarginals) : row175Statement :=
  RootedAssembly.headline_of_rooted (row175_rooted retirement marginal)

end L4

#print axioms L4.row175_rooted
#print axioms L4.row175Statement_of_rooted_stages
