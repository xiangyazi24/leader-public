import Leader.L4.ShortFiveWordEntry

namespace L4.ShortFiveRivalFence
open AllSizeProtocol PhysicalCustody PhysicalCustody.H1 ShortResetMIS1Ring
open ShortResetCycle ShortResetChart ShortResetForwardH2 ShortResetFlow MISByteCodec
open ShortResetHelloSplice ShortHelloForward ShortPreReadGrants ShortResetRow
open ShortFiveWinningWord ShortResetWatch ShortSimultaneousOrder

set_option maxRecDepth 8192

variable {s n : Nat} {h : Fin n → Bool}

private theorem parked_no_ask (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (P : Parked C x) : NoAsk C.route x := by
  intro j J H
  have V := slot_of_bits C.route x j E empty_decode (P.1.2.1 j J)
  change oldK (header x (nextAt C.root j)) (x (nextAt C.root j)).mis1 (C.route.port j)=E at V
  have HH : header x (nextAt C.root j)=true := (heads _).trans H
  rw [HH] at V
  exact pre_read_no_ask _ _ (.inl V)

private theorem parked_step (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (e : Fin n) (other : e≠RearTrace.predecessor C.root) (P : Parked C x) :
    Parked C (rawNext s x e) := by
  have N : 1<n := by have := C.positive; have := C.length_lt; omega
  exact ⟨ShortClearLaunch.clear_issue_nondoor C x heads 1 P.1 e other,
    no_ask_keeps_grants_absent C.route x e (edge_sep N e) heads P.2 (parked_no_ask C x heads P)⟩

theorem left_stays_parked (C : Chart h) (x : Raw s n) (N : 5≤n) (X : H2Ready x)
    (heads : ∀ q,header x q=h q) (P : Parked C x) (w : List (Fin n))
    (noMark : RearTrace.predecessor C.root ∉ w) :
    Parked C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact P
  | cons e w ih =>
    have K := parked_step C x heads e (fun E => noMark (by simp [E])) P
    have heads' (q : Fin n) := (raw_h1_selected_frozen N x e q X.1).trans (heads q)
    exact ih _ (h2_ready_closed N x e X) heads' K (fun E => noMark (List.mem_cons_of_mem _ E))

/-- A rival is either still parked or has exactly the HELLO frontier
with empty suffix and absent owner grants. -/
def NoTerminal (C : Chart h) (x : Raw s n) : Prop :=
  Parked C x ∨ ∃ i, BeforeTurn C.route x i ∧ ClearSuffix C.route x i ∧ NoGrants C.route x

theorem right_no_terminal (C : Chart h) (x : Raw s n) (N : 5≤n) (X : H2Ready x)
    (heads : ∀ q,header x q=h q) (P : NoTerminal C x) (w : List (Fin n))
    (noMark : terminalMark C.route ∉ w) :
    NoTerminal C (rawRun x w) := by
  induction w generalizing x with
  | nil => exact P
  | cons e w ih =>
    have missing : e≠terminalMark C.route := fun E => noMark (by simp [E])
    have heads' (q : Fin n) := (raw_h1_selected_frozen N x e q X.1).trans (heads q)
    apply ih _ (h2_ready_closed N x e X) heads' _ (fun E => noMark (List.mem_cons_of_mem _ E))
    rcases P with P|⟨i,F,S,G⟩
    · by_cases E : e=RearTrace.predecessor C.root
      · subst e
        have V := ShortHelloFlight.actual_launch C x heads P
        exact .inr ⟨0,V.2.1,V.2.2,V.1⟩
      · exact .inl (parked_step C x heads e E P)
    · have sep := edge_sep (by omega : 1<n) e
      exact .inr ⟨ahead C.route i e,before_turn_step C.route x e sep heads i F missing,
        clear_suffix_step C.route x e sep heads i S,no_grants_step C.route x e sep heads i F S G⟩

theorem no_terminal_no_ask (C : Chart h) (x : Raw s n) (heads : ∀ q, header x q=h q)
    (P : NoTerminal C x) : NoAsk C.route x := by
  rcases P with P|⟨i,F,S,_⟩
  · exact parked_no_ask C x heads P
  · intro j J H
    have Q : header x (nextAt C.route.root j)=true := (heads _).trans H
    apply pre_read_no_ask
    by_cases K : j<i
    · have V := slot_of_bits C.route x j T trail_decode (F.2.2.1 j K)
      change oldK (header x (nextAt C.route.root j)) _ _ = _ at V
      rw [Q] at V
      exact .inr (.inl V)
    · by_cases E : j=i
      · subst j
        have V := slot_of_bits C.route x i helloForward (fun b =>
          (ShortHelloAdmitCodec.decode_hello b).1) F.2.2.2
        change oldK (header x (nextAt C.route.root i)) _ _ = _ at V
        rw [Q] at V
        exact .inr (.inr (.inl V))
      · have V := slot_of_bits C.route x j MISByteCodec.E empty_decode (S j (by omega) J)
        change oldK (header x (nextAt C.route.root j)) _ _ = _ at V
        rw [Q] at V
        exact .inl V

/-- Raw rival fence on any prefix of, or any word over, the target watch.
A left rival cannot launch; a right rival may launch but cannot finish HELLO.
No rival can issue a READ ask, and all of its own grants remain absent. -/
theorem all_rivals_fenced (x : Raw s n) (X : H2Ready x) (N : 21<n) (r : Fin n)
    (cs : Fin 5 → Chart (header x))
    (roots : ∀ i, (cs i).root=nextAt r (offset (header x) r i.val))
    (P : ShortFiveParked.FiveParked cs x) (w : List (Fin n))
    (watchOnly : ∀ e∈w, e∈watch (cs 2)) :
    ∀ i : Fin 5, i≠2 → NoAsk (cs i).route (rawRun x w) ∧ NoGrants (cs i).route (rawRun x w) := by
  obtain ⟨L,R⟩ := rival_fences x X.1 N r cs roots
  have hold := (header_run (by omega) x X.1 w).2
  intro i I
  have ne : i.val≠2 := fun E => I (Fin.ext E)
  by_cases left : i.val<2
  · have H := left_stays_parked (cs i) x (by omega) X (fun _=>rfl) (P i) w
      (fun E => L i left (watchOnly _ E))
    exact ⟨parked_no_ask (cs i) _ hold H,H.2⟩
  · have H := right_no_terminal (cs i) x (by omega) X (fun _=>rfl) (.inl (P i)) w
      (fun E => R i (by omega) (watchOnly _ E))
    exact ⟨no_terminal_no_ask (cs i) _ hold H, by rcases H with H|⟨_,_,_,H⟩; exact H.2; exact H⟩

end L4.ShortFiveRivalFence
