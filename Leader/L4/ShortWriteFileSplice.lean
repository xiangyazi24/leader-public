import Leader.L4.ShortWriteFlight
import Leader.L4.ShortReadFileHold
import Leader.L4.ShortPhaseRank
import Leader.L4.ShortCommitFlight

namespace L4.ShortWriteFileSplice
open AllSizeProtocol MISByteCodec PhysicalCustody ShortResetMIS1Ring
open ShortResetRow ShortResetFlow ShortResetChart ShortResetCycle ShortResetForwardH2
open ShortWriteCentreWitness ShortWriteChartHop ShortCanonicalReverseChart
open ShortWriteFlight ShortReadFileHold ShortReadResult

def healthy : Flight→Prop
  | .front _ bad | .back _ bad | .done bad => bad=false

theorem healthy_before {s n : Nat} {h : Fin n→Bool} (C : Chart h) (cmd : Cmd)
    (d : Fin 8) (x : Raw s n) (e : Fin n) (f : Flight)
    (H : healthy (next C cmd d x e f)) : healthy f := by
  cases f with
  | done b => exact H
  | back i b =>
    cases K : nextStage C e (.rev i) <;> simpa [next,K,healthy] using H
  | front i b =>
    by_cases M : e=nextAt C.root i
    · by_cases L : i+1<C.L
      · simp only [next,if_pos M,if_pos L,healthy,advanceBad,Bool.or_eq_false_iff] at H
        exact H.1
      · simpa [next,M,L,healthy] using H
    · simpa [next,M,healthy] using H

theorem safe_wait_door {s n : Nat} {h : Fin n→Bool} (C : Chart h) (x : Raw s n)
    (head : header x C.root=true) (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (f : Flight) (L : live f) (B : healthy f) (A : Active C cmd d x f) :
    FileSafe (x C.root).mis1 (oldK true (x C.root).mis1 0) := by
  have O : cmd.op<7 := cmd_bound cmd
  have decodeRoot (t : Token)
      (E : bits C.route x 0=encode t) (H : ∀ b,decode b (encode t)=t) :
      oldK true (x C.root).mis1 0=t := by
    have K := slot_of_bits C.route x 0 t H E
    change oldK (header x C.root) (x C.root).mis1 (lane C.a C.b 0)=t at K
    rwa [head,C.rootPort] at K
  cases f with
  | done _ => exact False.elim L
  | front i bad =>
    obtain ⟨_,W,Tp,P,_⟩ := A
    refine .inr ⟨W.1,(by change get (x C.root).mis1 78 3 (by decide)<7; rw [W.2]; exact O),.inl ?_⟩
    cases i with
    | zero => exact .inr ((congrArg Token.tag (decodeRoot _ P (packet_decode cmd d D bad))).trans (packet_tag cmd d bad))
    | succ i => exact .inl ((congrArg Token.tag (decodeRoot _ (Tp 0 (by omega)) trail_decode)).trans rfl)
  | back i bad =>
    obtain ⟨_,W,Q⟩ := A
    refine .inr ⟨W.1,(by change get (x C.root).mis1 78 3 (by decide)<7; rw [W.2]; exact O),?_⟩
    cases i with
    | zero =>
      change bad=false at B
      subst bad
      have K := Q 0 C.positive
      change bits C.route x 0=encode (trailAt (reply cmd false) 0 0) at K
      have V : bits C.route x 0=encode (reply cmd false).token := by simpa [trailAt] using K
      rw [decodeRoot _ V (reply cmd false).decode_encode]
      right
      change (get (x C.root).mis1 78 3 (by decide)=4 ∨ get (x C.root).mis1 78 3 (by decide)=5) ∧
        (reply cmd false).token.tag=3 ∧
        (reply cmd false).token.opcode=get (x C.root).mis1 78 3 (by decide) ∧
        (reply cmd false).token.fault=false ∧ (reply cmd false).token.outcome≠1
      rw [W.2]
      cases cmd <;> decide
    | succ j =>
      have K := Q 0 C.positive
      change bits C.route x 0=encode (trailAt (reply cmd bad) (j+1) 0) at K
      have V : bits C.route x 0=encode T := by simpa [trailAt] using K
      exact .inl (.inl ((congrArg Token.tag (decodeRoot _ V trail_decode)).trans rfl))

theorem raw_file_step {s n : Nat} (x : Raw s n) (r e : Fin n)
    (N : 1<n) (hd : header x r=true)
    (S : rightNeighbor e=r → FileSafe (x r).mis1 (oldK true (x r).mis1 0)) :
    fileField.read (rawNext s x e r).mis1=fileField.read (x r).mis1 := by
  by_cases E : r=e
  · subst r
    exact outgoing_retains_file x e hd
  · by_cases H : rightNeighbor e=r
    · subst r
      exact safe_door_retains_file x e (edge_sep N e) hd (S rfl)
    · rw [reset_remote_frame_raw x e r E (Ne.symm H)]

theorem generated_retains_actual_file {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X : H2Ready x0) (N : 9<n)
    (cmd : Cmd) (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (f : Flight) (G : Generated x0 C cmd d w f) :
    healthy f → fileField.read (rawRun x0 w C.root).mis1=fileField.read (x0 C.root).mis1 := by
  induction G with
  | launch A _ =>
    intro _
    change fileField.read (rawNext s x0 (RearTrace.predecessor C.root) C.root).mis1=_
    apply raw_file_step x0 _ _ (by omega) C.rootHeader
    intro _
    refine .inl ⟨A.2.2.1,?_,?_⟩
    · change 0<get (x0 C.root).mis1 78 3 (by decide)
      rw [A.2.2.2]
      cases cmd <;> decide
    · change get (x0 C.root).mis1 78 3 (by decide)<7
      rw [A.2.2.2]
      exact cmd_bound cmd
  | @snoc w f e G L IH =>
    intro H
    let x := rawRun x0 w
    have B := healthy_before C cmd d x e f H
    have F := (generated_receipt x0 C X N cmd d D w f G).1
    have hd := ((header_run (by omega) x0 X.1 w).2 C.root).trans C.rootHeader
    have AP : rawRun x0 (w++[e])=rawNext s x e := BStarResetSchedule.run_append _ _ _ _
    rw [AP]
    exact (raw_file_step x C.root e (by omega) hd (fun _=>safe_wait_door C x hd cmd d D f L B F)).trans (IH B)

theorem descriptor_of_same_file (x y : BitVec 96)
    (H : fileField.read y=fileField.read x) : issuedDescriptor y=issuedDescriptor x := by
  have B (i : Nat) (I : i<6) : y.getLsbD (72+i)=x.getLsbD (72+i) := by
    rw [file_bit y i I,file_bit x i I,H]
  have K : get y 76 1 (by decide)=get x 76 1 (by decide) := by
    apply congrArg BitVec.toNat
    apply BitVec.eq_of_getLsbD_eq
    intro i I
    have Z : i=0 := by omega
    subst i
    simp only [MISByteCodec.lane,Field.read,BitVec.getLsbD_extractLsb',show 0<1 by decide,
      decide_true,Bool.true_and,Nat.add_zero]
    exact B 4 (by decide)
  unfold issuedDescriptor
  rw [K,B 2 (by decide),B 0 (by decide)]

theorem seal_to_commit_same_file {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (G : Generated x0 C .seal d w (.done false)) :
    let y := rawRun x0 w
    ShortEmptyOwnership.Clear C y ∧
    ShortControllerEntrance.pc (y C.root).mis1=14 ∧
    SampledEffect .seal d x0 (nextAt C.root C.a) w ∧
    fileField.read (y C.root).mis1=fileField.read (x0 C.root).mis1 ∧
    issuedDescriptor (y C.root).mis1=issuedDescriptor (x0 C.root).mis1 := by
  obtain ⟨A,P,R⟩ := seal_ack_after_centre x0 C X N d D w G
  have F := generated_retains_actual_file x0 C X N .seal d D w _ G rfl
  exact ⟨A,P,R,F,descriptor_of_same_file _ _ F⟩

theorem generated_descriptor {s n : Nat} {x0 : Raw s n} {C : Chart (header x0)}
    {cmd : Cmd} {d : Fin 8} {w : List (Fin n)} {f : Flight}
    (G : Generated x0 C cmd d w f) : d.val=issuedDescriptor (x0 C.root).mis1 := by
  induction G with
  | launch _ K => exact K
  | snoc _ _ _ ih => exact ih

/-- Same-file D5 actually enables the next canonical ISSUE6, and the
first real COMMIT token carries that very descriptor. -/
theorem seal_ack_launches_same_commit {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (G : Generated x0 C .seal d w (.done false)) :
    let y := rawRun x0 w
    ShortClearLaunch.ClearIssue C y 6 ∧
      ShortCommitFlight.Active C d (rawNext s y (RearTrace.predecessor C.root))
        (.front 0 .pending) := by
  let y := rawRun x0 w
  obtain ⟨A,P,_,_,Eq⟩ := seal_to_commit_same_file x0 C X N d D w G
  have W := ShortPhaseRank.pc_fields (y C.root).mis1
  rw [P] at W
  have B : get (y C.root).mis1 78 3 (by decide)<8 :=
    (MISByteCodec.lane 78 3 (by decide) |>.read (y C.root).mis1).isLt
  have H : ShortClearLaunch.ClearIssue C y 6 :=
    ⟨by decide,A,by omega,by omega⟩
  have heads := (header_run (by omega) x0 X.1 w).2
  obtain ⟨d',_,D',F⟩ := ShortCommitFlight.launch C y heads H
  have same : d'=d := Fin.ext (D'.trans (Eq.trans (generated_descriptor G).symm))
  exact ⟨H,same ▸ F⟩

theorem stage_ack_clears_same_seal {s n : Nat} (x0 : Raw s n)
    (C : Chart (header x0)) (X : H2Ready x0) (N : 9<n)
    (d : Fin 8) (D : descValid d.val=true)
    (w : List (Fin n)) (G : Generated x0 C .stage d w (.done false)) :
    let y := rawRun x0 w
    ShortClearLaunch.ClearIssue C y 5 ∧
      fileField.read (y C.root).mis1=fileField.read (x0 C.root).mis1 ∧
      d.val=issuedDescriptor (y C.root).mis1 := by
  let y := rawRun x0 w
  obtain ⟨A,P,_⟩ := stage_ack_after_centre x0 C X N d D w G
  have W := ShortPhaseRank.pc_fields (y C.root).mis1
  rw [P] at W
  have B : get (y C.root).mis1 78 3 (by decide)<8 :=
    (MISByteCodec.lane 78 3 (by decide) |>.read (y C.root).mis1).isLt
  have F := generated_retains_actual_file x0 C X N .stage d D w _ G rfl
  have H : ShortClearLaunch.ClearIssue C y 5 := ⟨by decide,A,by omega,by omega⟩
  exact ⟨H,F,
    (generated_descriptor G).trans (descriptor_of_same_file _ _ F).symm⟩

theorem clear_issue_file_nondoors {s n : Nat} {h : Fin n→Bool}
    (C : Chart h) (x : Raw s n) (X : H2Ready x)
    (heads : ∀ q,header x q=h q) (N : 5≤n)
    (op : Nat) (A : ShortClearLaunch.ClearIssue C x op) (w : List (Fin n))
    (nodoor : ∀ e∈w,e≠RearTrace.predecessor C.root) :
    let y := rawRun x w
    ShortClearLaunch.ClearIssue C y op ∧
      fileField.read (y C.root).mis1=fileField.read (x C.root).mis1 := by
  induction w generalizing x with
  | nil => exact ⟨A,rfl⟩
  | cons e w IH =>
    let y := rawNext s x e
    have D := nodoor e (by simp)
    have B := ShortClearLaunch.clear_issue_nondoor C x heads op A e D
    have heads' (q : Fin n) : header y q=h q :=
      (PhysicalCustody.H1.raw_h1_selected_frozen N x e q X.1).trans (heads q)
    have F := raw_file_step x C.root e (by omega) ((heads _).trans C.rootHeader) (fun E=>False.elim (D (by
      have K := congrArg RearTrace.predecessor E
      simpa only [RearTrace.predecessor_right] using K)))
    obtain ⟨P,Q⟩ := IH y (h2_ready_closed N x e X) heads' B (fun j J=>nodoor j (by simp [J]))
    exact ⟨P,Q.trans F⟩

end L4.ShortWriteFileSplice
