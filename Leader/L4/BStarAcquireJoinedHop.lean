import Leader.L4.BStarAcquireLandingHop
import Leader.L4.BStarLongFenceTopology

namespace L4.BStarAcquireJoinedHop
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongTransport
open BStarLongRouting BStarLongLayout BStarLongWork BStarLongRoutingFrame

private def geo (h i l : Bool) : LongGeometry :=
  ⟨⟨false,false,false,false,false,h⟩,i,l,0,false⟩

/-- The only selected K0 destination is the interior positive K0 hop.
In particular it is not a right-header source-door occurrence. -/
theorem k0_dest (g : Pair LongGeometry) (c : CommandClaim) (a : AtK)
    (hc : c∈orderedCommands g) (hd : c.destination=some a) (h0 : a.occurrence.val=0) :
    a.side=.right ∧ g.2.axes.h6=false := by
  have H := BStarLongFenceTopology.selected_command_raw g c hc
  obtain ⟨x,y⟩ := g
  have test : (commandClaims (x,y)).all (fun q => q.destination.all fun dst =>
        if dst.occurrence.val=0 then dst.side==.right && !y.axes.h6 else true) = true := by
    rw [show commandClaims (x,y)=commandClaims
      (geo false x.inside x.last,geo y.axes.h6 y.inside false) from rfl]
    generalize x.inside=xi
    generalize x.last=xl
    generalize y.axes.h6=yh
    generalize y.inside=yi
    cases xi <;> cases xl <;> cases yh <;> cases yi <;> decide +kernel
  have P := List.all_eq_true.mp test c H
  rw [hd] at P
  have J : a.occurrence=(0 : Fin 11) := Fin.ext h0
  simpa [J] using P

private def KFrame (q : Patch LW) : Prop :=
  ∀ i, 1192≤i → i<1764 → q.mask.getLsbD i=false

private theorem assign_kframe {w : Nat} (f : Field LW w) (v : BitVec w)
    (h : 1764≤f.offset) : KFrame (f.assign v) := by
  intro i hl hh
  apply Bool.eq_false_iff.mpr
  intro hm
  have H := (Field.inMask f v i).mp hm
  omega

private theorem compose_kframe {p q : Patch LW} (hp : KFrame p) (hq : KFrame q) :
    KFrame (p.compose q) := by
  intro i lo hi
  simp [Patch.compose,hp i lo hi,hq i lo hi]

theorem scratch_kframe (g : Pair LongGeometry) (x : Pair (BitVec LW)) (s : Bool) :
    KFrame (lane s (longScratch g x)) := by
  cases s
  · change KFrame ((shField.assign _).compose (seField.assign _))
    exact compose_kframe (assign_kframe _ _ (by decide)) (assign_kframe _ _ (by decide))
  · change KFrame (offField.assign _)
    exact assign_kframe _ _ (by decide)

theorem field_kframe (q : Patch LW) (x : BitVec LW) (j : Fin 11) (h : KFrame q) :
    (kField j).read (q.apply x)=(kField j).read x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Field.read,BitVec.getLsbD_extractLsb',hi,decide_true,Bool.true_and]
  apply Patch.hold
  apply h
  · simp only [kField,kBase]
    have := j.isLt
    omega
  · simp only [kField,kBase]
    have := j.isLt
    omega

theorem guard_frame : Frame (LongDoorGuard.repair manifest) := by
  unfold LongDoorGuard.repair
  exact compose (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))
    (compose (assign _ _ (.inr (by decide))) (assign _ _ (.inr (by decide))))

/-- The actual outer large pair does not alter this selected landing.
At other K occurrences the invalid-door repair is harmless; at K0
the literal selected-hop geometry rules the repair out. -/
theorem joined_acquire_lands (k₁ k₂ t₂ J₁ J₂ r c p c₁ : Nat) (hp : 0<p)
    (x : Pair (LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)))
    (C : CommandClaim) (a : AtK) (pay : Payload) :
    let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
    let g := Pair.map (longGeometry b) x
    let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
    C∈orderedCommands g → C.destination=some a → C.kind≠.door →
    readK raw C.source=.forward pay → BStarAcquireHop.Healthy pay →
    readK (Pair.map LargeSite.long (largePair b x)) a=
      .forward (BStarAcquireHop.argUpdate g raw (BStarLongCommandData.round g raw).offered C pay) := by
  dsimp only
  intro hc hd hn hread hpay
  let b := bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
  let g := Pair.map (longGeometry b) x
  let raw : Pair (BitVec LW) := Pair.map LargeSite.long x
  let w := longWork g raw
  let q := longScratch g raw
  have landed := BStarAcquireLandingHop.raw_acquire_lands g raw C a pay hc hd hn hread hpay
  suffices E : readRaw (Pair.map LargeSite.long (largePair b x)) a =
      readRaw (patchPair w raw) a by
    change decode (readRaw (Pair.map LargeSite.long (largePair b x)) a)=_
    rw [E]
    exact landed
  obtain ⟨side,j⟩ := a
  cases side with
  | left =>
    change (kField j).read ((w.1.compose q.1).apply raw.1)=(kField j).read (w.1.apply raw.1)
    rw [Patch.compose_apply]
    exact field_kframe _ _ _ (scratch_kframe g raw false)
  | right =>
    change (kField j).read ((LongDoorGuard.guard manifest g.2.axes.h6 raw.2
      (w.2.compose q.2)).apply raw.2)=(kField j).read (w.2.apply raw.2)
    have Q : (kField j).read ((w.2.compose q.2).apply raw.2)=(kField j).read (w.2.apply raw.2) := by
      rw [Patch.compose_apply]
      exact field_kframe _ _ _ (scratch_kframe g raw true)
    cases H : g.2.axes.h6
    · rw [LongDoorGuard.no_authority]; exact Q
    · cases V : LongDoorGuard.valid manifest raw.2
      · rw [LongDoorGuard.invalid_override _ _ _ V,Patch.compose_apply]
        have J : j.val≠0 := fun he => by
          have H' := (k0_dest g C ⟨.right,j⟩ hc hd he).2
          rw [H] at H'
          cases H'
        have F := read_frame (raw.1,(w.2.compose q.2).apply raw.2) (R j) J
          (true,LongDoorGuard.repair manifest) guard_frame
        exact F.trans Q
      · rw [LongDoorGuard.valid_no_override _ _ _ V]; exact Q

end L4.BStarAcquireJoinedHop
