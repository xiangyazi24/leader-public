import Leader.L4.BStarLongWork

/-! Literal event characterization at the packed-row boundary. Inherited
COMMIT is intentionally included. This is not a cycle provenance proof. -/
namespace L4.BStarLongEvents
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongArithmetic BStarLongCommand BStarLongPublication

private theorem digit_nonzero_opcode (g : LongGeometry) (x : BitVec LW) (i : Nat)
    (c : L4.Compiler.Native.Code) (p : Payload)
    (h : (physicalDigit g x i c p).2.opcode ≠ 0) :
    (physicalDigit g x i c p).2.opcode=p.opcode := by
  cases c <;> simp [physicalDigit] at *
  split at * <;> simp_all

private theorem visit_nonzero_opcode (g : LongGeometry) (j : Fin 11)
    (x : BitVec LW) (p : Payload)
    (h : (visit g j x p).2.opcode ≠ 0) :
    (visit g j x p).2.opcode=p.opcode := by
  by_cases C : (j.val != 1 || !g.inside || p.fault != 0)=true
  · simp only [visit,C,if_true]
  have Z : (j.val != 1 || !g.inside || p.fault != 0)=false := Bool.eq_false_iff.mpr C
  cases E : nodeOf p.opcode.toNat with
  | none => simp only [visit,Z,Bool.false_eq_true,if_false,E]
  | some i =>
    cases F : get i with
    | none => simp only [visit,Z,Bool.false_eq_true,if_false,E,F] at h
              exact (h rfl).elim
    | some c =>
      simp only [visit,Z,Bool.false_eq_true,if_false,E,F] at h ⊢
      exact digit_nonzero_opcode _ _ _ _ _ h

private theorem commit_no_digit (g : LongGeometry) (j : Fin 11)
    (x : BitVec LW) (p : Payload) (h : p.opcode.toNat=commitOp) :
    visit g j x p=(.empty _,p) := by
  unfold visit
  split
  · rfl
  rw [h]
  have e : nodeOf commitOp=none := by decide +kernel
  rw [e]

def LiteralCommit (g : LongGeometry) (a : At (Fin 11))
    (x : BitVec LW) (p : Payload) (b : Fin 3) : Prop :=
  a.occurrence.val=1 ∧ g.axes.h6=true ∧ p.fault=0 ∧ p.opcode.toNat=commitOp ∧
    ∃ d, BStarLongPublication.decode (BitVec.ofNat 7 (p.argument.toNat/4))=some d ∧
      p.argument.toNat%4=b.val ∧ guard true a.occurrence x d b=true

theorem selected_pub_iff (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (c : CommandClaim) (p : Payload) (e : Publication) :
    e∈(selected g x (c,.advance p)).publications ↔
      e.endpoint=c.source.side ∧ LiteralCommit (geometry g c.source.side) c.source (atOld x c.source) p e.bank := by
  let gg := geometry g c.source.side
  let raw := atOld x c.source
  let j := c.source.occurrence
  let v := visit gg j raw p
  let h := BStarLongOutgoing.execute gg j raw v.2
  change e∈h.published.toList.map (fun b => ⟨c.source.side,b⟩) ↔
    e.endpoint=c.source.side ∧ LiteralCommit gg c.source raw p e.bank
  constructor
  · intro he
    obtain ⟨b,H,E⟩ := List.mem_map.mp he
    subst e
    have H' : h.published=some b := Option.mem_toList.mp H
    have S := BStarLongOutgoing.event_sound gg j raw v.2 b H'
    have neq : v.2.opcode≠0 := by
      intro z
      have := S.2.2.2.1
      simp [z,commitOp] at this
    have hop : p.opcode.toNat=commitOp := by
      rw [←visit_nonzero_opcode gg j raw p neq]
      exact S.2.2.2.1
    have eq : v.2=p := congrArg Prod.snd (commit_no_digit gg j raw p hop)
    rw [eq] at S
    exact ⟨rfl,S⟩
  · rintro ⟨hs,hj,hh,hf,hop,d,hd,hb,hc⟩
    have eq : v.2=p := congrArg Prod.snd (commit_no_digit gg j raw p hop)
    have H : h.published=some e.bank := by
      unfold h
      rw [eq]
      have hj' : j=(1:Fin 11) := Fin.ext hj
      change guard true j raw d e.bank=true at hc
      rw [hj'] at hc ⊢
      rw [BStarLongOutgoing.center_commit gg raw p d e.bank hh hf hop hd hb hc]
    apply List.mem_map.mpr
    refine ⟨e.bank,Option.mem_toList.mpr H,?_⟩
    cases e
    simp_all

private theorem fold_mem (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (L : List CmdOffer) (a : Selected) (e : Publication) :
    e∈(L.foldl (fun acc o => acc.append (selected g x o)) a).publications ↔
      e∈a.publications ∨ ∃ o∈L,e∈(selected g x o).publications := by
  induction L generalizing a with
  | nil => simp
  | cons m ms ih =>
    rw [List.foldl_cons,ih]
    simp only [Selected.append,List.mem_append,List.mem_cons]
    constructor
    · rintro ((A|B)|⟨o,ho,E⟩)
      · exact .inl A
      · exact .inr ⟨m,.inl rfl,B⟩
      · exact .inr ⟨o,.inr ho,E⟩
    · rintro (A|⟨o,(rfl|ho),E⟩)
      · exact .inl (.inl A)
      · exact .inl (.inr E)
      · exact .inr ⟨o,ho,E⟩

def actualOffers (g : Pair LongGeometry) (x : Pair (BitVec LW)) : List CmdOffer :=
  (BStarLongGrant.run g x (BStarLongCommandData.round g x).offered).departures

theorem literal_event_iff (g : Pair LongGeometry) (x : Pair (BitVec LW)) (e : Publication) :
    e∈(longTrace g x).publications ↔
      ∃ c p, (c,.advance p)∈actualOffers g x ∧ e.endpoint=c.source.side ∧
        LiteralCommit (geometry g c.source.side) c.source (atOld x c.source) p e.bank := by
  change e∈((actualOffers g x).foldl
    (fun a o => Selected.append a (selected g x o)) ⟨[],[],[]⟩).publications ↔ _
  rw [fold_mem]
  simp only [List.not_mem_nil,false_or]
  constructor
  · rintro ⟨⟨c,t⟩,ht,he⟩
    match t with
    | .advance p => exact ⟨c,p,ht,(selected_pub_iff g x c p e).mp he⟩
    | .hold | .clear | .reverse _ | .door _ =>
      rw [nonadvancing_no_publication _ _ _ _ (by intro p; simp)] at he
      simp at he
  · rintro ⟨c,p,hm,H⟩
    exact ⟨(c,.advance p),hm,(selected_pub_iff g x c p e).mpr H⟩

def centerClaim (o : CommandClaim) : Bool := o.source.occurrence.val==1

theorem one_center_claim (g : Pair LongGeometry) :
    (orderedCommands g).filter centerClaim=
    [link (L 1) (R (if g.2.axes.h6 then 2 else 1))] := by
  obtain ⟨x,y⟩ := g
  unfold orderedCommands commandClaims ends
  simp only
  generalize x.inside=ix
  generalize x.last=lx
  generalize y.axes.h6=hy
  generalize y.inside=iy
  cases ix <;> cases lx <;> cases hy <;> cases iy <;> decide +kernel

theorem update_claim (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (o : CmdOffer) :
    (BStarLongGrant.update g x os o).1=o.1 := by
  obtain ⟨c,a⟩ := o
  simp only [BStarLongGrant.update]
  split
  · cases a <;> try rfl
    split <;> (first | rfl | (split <;> rfl))
  · rfl

theorem actualOffers_claims (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    (actualOffers g x).map Prod.fst=orderedCommands g := by
  simp only [actualOffers,BStarLongGrant.run,List.map_map,Function.comp_def,
    update_claim,BStarLongCommandData.claims_unchanged]

private theorem selected_pub_length (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) : (selected g x o).publications.length≤1 := by
  obtain ⟨c,t⟩ := o
  cases t with
  | advance p =>
    change (Option.toList _ |>.map _).length≤1
    rw [List.length_map]
    have bound (b : Option (Fin 3)) : b.toList.length≤1 := by
      cases b <;> simp
    exact bound _
  | door t =>
    unfold selected
    dsimp only
    split <;> exact Nat.zero_le _
  | _ => exact Nat.zero_le _

private theorem off_center_no_pub (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (o : CmdOffer) (hc : centerClaim o.1=false) : (selected g x o).publications=[] := by
  obtain ⟨c,t⟩ := o
  cases t with
  | advance p =>
    cases H : (selected g x (c,.advance p)).publications with
    | nil => rfl
    | cons e tail =>
      have hm : e∈(selected g x (c,.advance p)).publications := by simp [H]
      have B := ((selected_pub_iff g x c p e).mp hm).2.1
      simp [centerClaim,B] at hc
  | _ =>
    apply nonadvancing_no_publication
    intro p
    simp

private theorem pub_count (g : Pair LongGeometry) (x : Pair (BitVec LW))
    (os : List CmdOffer) (a : Selected) :
    ((os.foldl (fun acc o => Selected.append acc (selected g x o)) a).publications).length ≤
      a.publications.length + ((os.map Prod.fst).filter centerClaim).length := by
  induction os generalizing a with
  | nil => simp
  | cons o rest ih =>
    rw [List.foldl_cons]
    have E := ih (a.append (selected g x o))
    have e : (a.append (selected g x o)).publications.length=
        a.publications.length+(selected g x o).publications.length := List.length_append
    rw [e] at E
    cases C : centerClaim o.1
    · rw [off_center_no_pub g x o C] at E
      simpa [C] using E
    · simp only [List.map_cons,List.filter_cons,C,if_true,List.length_cons]
      have K := selected_pub_length g x o
      omega

/-- Every mark can publish at most once, regardless of provenance. The
only possible publishing occurrence is the physical initiator's K1. -/
theorem at_most_one_literal_publication (g : Pair LongGeometry) (x : Pair (BitVec LW)) :
    (longTrace g x).publications.length≤1 := by
  change ((actualOffers g x).foldl
    (fun a o => Selected.append a (selected g x o)) (⟨[],[],[]⟩ : Selected)).publications.length≤1
  have h := pub_count g x (actualOffers g x) ⟨[],[],[]⟩
  simpa only [actualOffers_claims,one_center_claim,List.length_nil,Nat.zero_add,List.length_cons] using h

theorem literal_endpoint_left (g : Pair LongGeometry) (x : Pair (BitVec LW)) (e : Publication)
    (hm : e∈(longTrace g x).publications) : e.endpoint=.left := by
  obtain ⟨c,p,m,side,hc, _⟩ := (literal_event_iff g x e).mp hm
  have H : c∈(actualOffers g x).map Prod.fst := List.mem_map.mpr ⟨(c,.advance p),m,rfl⟩
  rw [actualOffers_claims] at H
  have E : c∈(orderedCommands g).filter centerClaim :=
    List.mem_filter.mpr ⟨H,by simp [centerClaim,hc]⟩
  rw [one_center_claim] at E
  simp only [List.mem_singleton] at E
  simpa [E,link,L] using side

end L4.BStarLongEvents
