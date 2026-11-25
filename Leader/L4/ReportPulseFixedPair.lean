import Leader.L4.ReportPulseDisjoint
import Leader.L4.ReportPulseJointCount

namespace L4.ReportPulseFixedPair
open ReportPulseRecode ReportPulseRounds ReportPulseWinsSkeleton ReportPulseDisjoint
open PulseOrientation ReportPulseJointCount
variable {G : Type} [DecidableEq G] {n B J : Nat}

def keys (g h : G) (J p q : Nat) (z : Skeleton G) : List (Nat × G) :=
  ((extract g J (z.take (p+1))).map fun x => (x.1,g)) ++
  ((extract h J (z.take (q+1))).map fun x => (x.1,h))

def KeyGood (B k : Nat) (l : List (Nat × G)) : Prop :=
  l.length=k ∧ (l.map Prod.fst).Nodup ∧ ∀ a∈l,a.1<B

omit [DecidableEq G] in
theorem key_at_mem {k : Nat} {l : List (Nat × G)} (H : KeyGood B k l) (i : Fin k) :
    l[i.val]'(by rw [H.1];exact i.isLt) ∈ l := List.getElem_mem _

noncomputable def keyAt {k : Nat} (B : Nat) (l : List (Nat × G))
    (H : KeyGood B k l) (i : Fin k) : Nat × G :=
  l[i.val]'(by rw [H.1]; exact i.isLt)

noncomputable def index {k : Nat} (K : k≤B) (l : List (Nat × G)) (i : Fin k) : Fin B := by
  classical
  exact if H : KeyGood B k l then ⟨(keyAt B l H i).1,H.2.2 _ (key_at_mem H i)⟩
    else Fin.castLE K i

noncomputable def gate {k : Nat} (B : Nat) (fallback : G) (l : List (Nat × G)) (i : Fin k) : G := by
  classical
  exact if H : KeyGood B k l then (keyAt B l H i).2 else fallback

omit [DecidableEq G] in
theorem index_inj {k : Nat} (K : k≤B) (l : List (Nat × G)) :
    Function.Injective (index K l) := by
  classical
  intro i j E
  unfold index at E
  by_cases H : KeyGood B k l
  · rw [dif_pos H,dif_pos H] at E
    have P := congrArg Fin.val E
    apply Fin.ext
    apply (List.getElem_inj (h₀:=by rw [List.length_map,H.1]; exact i.isLt) (h₁:=by rw [List.length_map,H.1]; exact j.isLt) H.2.1).mp
    simpa only [List.getElem_map,keyAt] using P
  · rw [dif_neg H,dif_neg H] at E
    exact Fin.ext (show i.val=j.val from congrArg (fun k : Fin B=>k.val) E)

theorem key_count (F : List (Fin n)→Prop)
    (put : G×Bool→Fin n) (inj : Function.Injective put) (s : Phase G)
    (p q : Fin B) (g h : G) (pq : p≠q) (K : 2*J≤B)
    (Cert : ∀ w : Word n B,F (List.ofFn w) →
      let z := recoded put s (List.ofFn w)
      let l := keys g h J p.val q.val z
      KeyGood B (2*J) l ∧
      (∀ a∈l, z[a.1]?=some (some (.start a.2)) ∧
        (encodeFin put s (List.ofFn w))[a.1]?=some (put (a.2,true))) ∧
      z[p.val]?=some (some (.complete g)) ∧ z[q.val]?=some (some (.complete h))) :
    2^(2*J)*actualCount F B≤n^(B-2) := by
  classical
  let kf (z : Skeleton G) := keys g h J p.val q.val z
  let a (z : Skeleton G) := index K (kf z)
  let b (z : Skeleton G) := gate (k:=2*J) B g (kf z)
  apply count_on_original_tapes F put inj s a b (fun z=>index_inj K (kf z)) p q g h pq
  · intro w W i
    dsimp only
    rw [show rawKey put (armed s) (recodeWord put s w)=recoded put s (List.ofFn w) by
      unfold rawKey recoded
      rw [ofFn_recodeWord]]
    obtain ⟨H,Tags,_,_⟩ := Cert w W
    unfold a b index gate
    rw [dif_pos H,dif_pos H]
    exact (Tags _ (key_at_mem H i)).1
  · intro w W i
    dsimp only
    rw [show rawKey put (armed s) (recodeWord put s w)=recoded put s (List.ofFn w) by
      unfold rawKey recoded
      rw [ofFn_recodeWord]]
    obtain ⟨H,Tags,_,_⟩ := Cert w W
    unfold a b index gate
    rw [dif_pos H,dif_pos H]
    have E := (Tags _ (key_at_mem H i)).2
    unfold recodeWord
    rw [List.getElem?_eq_getElem (by rw [encodeFin_length,List.length_ofFn]; exact H.2.2 _ (key_at_mem H i))] at E
    exact Option.some.inj E
  · intro w W
    dsimp only
    rw [show rawKey put (armed s) (recodeWord put s w)=recoded put s (List.ofFn w) by
      unfold rawKey recoded
      rw [ofFn_recodeWord]]
    exact (Cert w W).2.2

#print axioms key_count

open AllSizeProtocol ReportByteRows ReportPulseRaw ReportPulseWarmup

omit [DecidableEq G] in
theorem closed_pins (g : G) (J : Nat) (w : Skeleton G)
    (K : 0<J) (H : ClosedRounds g J w) :
    w[w.length-1]?=some (some (.complete g)) := by
  cases H with
  | zero => omega
  | @snoc _ u v _ _ => simp

structure PrefixCert (put : G × Bool → Fin n) (s : Phase G) (g : G) (J : Nat)
    (w : List (Fin n)) : Prop where
  length : (starts put g J s w).length=J
  labels : ∀ i∈starts put g J s w, i<w.length ∧
    (recoded put s w)[i]?=some (some (.start g)) ∧ w[i]?=some (put (g,true))
  pin : (recoded put s w)[w.length-1]?=some (some (.complete g))

theorem certify_prefix {X : Type}
    (put : G × Bool → Fin n) (inj : Function.Injective put) (g : G)
    {raw : X → Fin n → X} {Q : X → Prop} {p : Params} {bytes : X → BitVec p.w}
    (Wire : Wire raw (put (g,true)) Q p bytes)
    (Adj : rightNeighbor (put (g,false))=put (g,true)) (J : 0<p.streak)
    (base : X) (Good : Q base) (s : Phase G)
    (Initial : s g=phaseOf (readClock p bytes base).phase)
    (w : List (Fin n))
    (C : Credit (put (g,false)) (put (g,true)) p.streak (cleanAt raw p bytes base) w) :
    PrefixCert put s g p.streak w := by
  obtain ⟨u,v,E,Cut,Win⟩ := C
  subst w
  have Empty := raw_clean_empty put inj g Wire Adj J base Good s Initial u Cut
  have H := wins_extract put inj g s u v p.streak Empty Win
  refine ⟨?_,?_,?_⟩
  · exact (List.length_map _).trans H.1
  · intro i M
    obtain ⟨pair,A,rfl⟩ := List.mem_map.mp M
    have K := (pair_start_global put inj g s u v pair (H.2 pair A)).2
    exact ⟨K.1,K.2,credit_origin_outgoing put inj g s u v p.streak Empty Win pair A⟩
  · unfold recoded
    rw [skeleton_encodeFin put inj,List.map_append,events_append]
    let es := physicalEvents s (u.map (readLabel put))
    let fs := physicalEvents (physicalRun s (u.map (readLabel put))) (v.map (readLabel put))
    have C := (wins_events put inj g _ Empty Win).2
    have Pin := closed_pins g p.streak fs J C
    have L : fs.length=v.length := (events_length _ _).trans (List.length_map _)
    have U : es.length=u.length := (events_length _ _).trans (List.length_map _)
    have Pos : 0<v.length := by
      cases V : v with
      | nil =>
        have N : fs=[] := List.length_eq_zero_iff.mp (L.trans (congrArg List.length V))
        simp [N] at Pin
      | cons e vs => simp
    change (es++fs)[(u++v).length-1]?=_
    rw [List.getElem?_append_right (by simp only [List.length_append,U]; omega)]
    rw [show (u++v).length-1-es.length=fs.length-1 by simp only [List.length_append,L,U]; omega]
    exact Pin

#print axioms certify_prefix

theorem tag_lift (put : G × Bool → Fin n) (inj : Function.Injective put)
    (s : Phase G) (u v : List (Fin n)) (j : Nat) (J : j<u.length) (e : Event G)
    (H : (recoded put s u)[j]?=some (some e)) :
    (recoded put s (u++v))[j]?=some (some e) := by
  rw [←recoded_prefix put inj s u v,List.getElem?_take,if_pos J] at H
  exact H

theorem certify_keys (put : G×Bool→Fin n) (inj : Function.Injective put)
    (s : Phase G) (g h : G) (p q : Fin B)
    (a b tail : List (Fin n))
    (Lp : a.length=p.val+1) (Lq : (a++b).length=q.val+1)
    (C₀ : PrefixCert put s g J a) (C₁ : PrefixCert put s h J (a++b))
    (Disjoint : ∀ i∈starts put g J s a,i∉starts put h J s (a++b)) :
    let w := (a++b)++tail
    let z := recoded put s w
    let l := keys g h J p.val q.val z
    KeyGood B (2*J) l ∧
      (∀ a∈l, z[a.1]?=some (some (.start a.2)) ∧
        (encodeFin put s w)[a.1]?=some (put (a.2,true))) ∧
      z[p.val]?=some (some (.complete g)) ∧ z[q.val]?=some (some (.complete h)) := by
  dsimp only
  let w := (a++b)++tail
  let z := recoded put s w
  let l₀ := (starts put g J s a).map (fun i => (i,g))
  let l₁ := (starts put h J s (a++b)).map (fun i => (i,h))
  have Ta : z.take (p.val+1)=recoded put s a := by
    rw [←Lp]
    change (recoded put s ((a++b)++tail)).take a.length=_
    rw [List.append_assoc]
    exact recoded_prefix put inj s a (b++tail)
  have Tb : z.take (q.val+1)=recoded put s (a++b) := by
    rw [←Lq]
    exact recoded_prefix put inj s (a++b) tail
  have E : keys g h J p.val q.val z=l₀++l₁ := by
    unfold keys l₀ l₁ starts
    rw [Ta,Tb,List.map_map,List.map_map]
    rfl
  change KeyGood B (2*J) (keys g h J p.val q.val z) ∧ _ ∧ _ ∧ _
  rw [E]
  have Tag : ∀ pair∈l₀++l₁, pair.1<B ∧
      z[pair.1]?=some (some (.start pair.2)) ∧ w[pair.1]?=some (put (pair.2,true)) := by
    intro pair M
    rcases List.mem_append.mp M with M|M
    · obtain ⟨i,S,rfl⟩ := List.mem_map.mp M
      obtain ⟨A,T,O⟩ := C₀.labels i S
      have Eq : w=a++(b++tail) := List.append_assoc ..
      refine ⟨by have := p.isLt; simp only; omega,?_,?_⟩
      · change (recoded put s w)[i]?=_
        rw [Eq]
        exact tag_lift put inj s a (b++tail) i A (.start g) T
      · change w[i]?=_
        rw [Eq,List.getElem?_append_left A]
        exact O
    · obtain ⟨i,S,rfl⟩ := List.mem_map.mp M
      obtain ⟨A,T,O⟩ := C₁.labels i S
      refine ⟨by have := q.isLt; simp only; omega,?_,?_⟩
      · exact tag_lift put inj s (a++b) tail i A (.start h) T
      · change ((a++b)++tail)[i]?=_
        rw [List.getElem?_append_left A]
        exact O
  have Good : KeyGood B (2*J) (l₀++l₁) := by
    refine ⟨?_,?_,fun i M=>(Tag i M).1⟩
    · simp only [l₀,l₁,List.length_append,List.length_map,C₀.length,C₁.length]
      omega
    · have left : l₀.map Prod.fst=starts put g J s a := by simp [l₀,List.map_map,Function.comp_def]
      have right : l₁.map Prod.fst=starts put h J s (a++b) := by simp [l₁,List.map_map,Function.comp_def]
      rw [List.map_append,left,right]
      refine List.nodup_append.mpr ⟨starts_nodup _ _ _ _ _,starts_nodup _ _ _ _ _,?_⟩
      intro i I j K T
      subst j
      exact Disjoint i I K
  refine ⟨Good,?_,?_,?_⟩
  · intro pair M
    have ⟨_,T,O⟩ := Tag pair M
    exact ⟨T,(encodeFin_keeps_starts put inj pair.2 s w pair.1 T).trans O⟩
  · have Pin := C₀.pin
    rw [Lp,show p.val+1-1=p.val by omega] at Pin
    change (recoded put s ((a++b)++tail))[p.val]?=_
    rw [List.append_assoc]
    exact tag_lift put inj s a _ _ (by omega) _ Pin
  · have Pin := C₁.pin
    rw [Lq,show q.val+1-1=q.val by omega] at Pin
    exact tag_lift put inj s (a++b) tail _ (by omega) _ Pin

#print axioms certify_keys

/-- A real clean prefix may precede the WARMUP1 clock's counted suffix. -/
theorem credit_after_warm {X : Type} {raw : X→Fin n→X} {b a : Fin n}
    {Q : X→Prop} {p : Params} {bytes : X→BitVec p.w}
    (F : Wire raw b Q p bytes) (Adj : rightNeighbor a=b) (D : a≠b)
    (J : 0<p.streak) (x : X) (Qx : Q x)
    (u v : List (Fin n)) (e : Fin n)
    (Clean : cleanAt raw p bytes x u)
    (Paint : countedPaint b p bytes ((u++v).foldl raw x) e=true) :
    Credit a b p.streak (cleanAt raw p bytes x) ((u++v)++[e]) := by
  let y := u.foldl raw x
  have Qy := wire_run_good F x u Qx
  have H := wire_fresh_from_clean F a Adj D J y Qy Clean v
  rw [List.foldl_append] at Paint
  obtain ⟨pre,win,E,C,W⟩ := (wire_fresh_mark F a Adj D J y Qy v e H).2 Paint
  refine ⟨u++pre,win,?_,?_,W⟩
  · rw [List.append_assoc,E,List.append_assoc]
  · unfold cleanAt
    rw [List.foldl_append]
    exact C

theorem rebased_starts_lower {X : Type}
    (put : G×Bool→Fin n) (inj : Function.Injective put) (s : Phase G) (g : G)
    {raw : X→Fin n→X} {Q : X→Prop} {p : Params} {bytes : X→BitVec p.w}
    (W : Wire raw (put (g,true)) Q p bytes)
    (Adj : rightNeighbor (put (g,false))=put (g,true)) (J : 0<p.streak)
    (x : X) (Good : Q x) (I : s g=phaseOf (readClock p bytes x).phase)
    (first second : List (Fin n))
    (C : Credit (put (g,false)) (put (g,true)) p.streak
      (cleanAt raw p bytes (first.foldl raw x)) second) :
    ∀ j∈starts put g p.streak s (first++second),first.length≤j := by
  obtain ⟨pre,win,E,Cut,Win⟩ := C
  let u := first++pre
  have L : cleanAt raw p bytes x u := by
    unfold cleanAt u
    rw [List.foldl_append]
    exact Cut
  have S := raw_clean_empty put inj g W Adj J x Good s I u L
  have R := wins_extract put inj g s u win p.streak S Win
  intro j M
  rw [E,←List.append_assoc] at M
  obtain ⟨p',H,rfl⟩ := List.mem_map.mp M
  exact Nat.le_trans (by simp [u]) (pair_start_global put inj g s u win p' (R.2 p' H)).1

/-- One fixed pair of chronological paint locations, with real warm
prefixes in the sampled tape. Equal and distinct gates are both
allowed. For a repeated gate the second warm cut is the first paint,
so no separate second warm certificate is needed. -/
theorem fixed_pair_actual {X : Type} (F : List (Fin n)→Prop)
    (put : G×Bool→Fin n) (inj : Function.Injective put) (s : Phase G)
    {raw : X→Fin n→X} {Q : X→Prop} {p : Params} (bytes : G→X→BitVec p.w)
    (W : ∀ g, Wire raw (put (g,true)) Q p (bytes g))
    (Adj : ∀ g, rightNeighbor (put (g,false))=put (g,true)) (J : 0<p.streak)
    (x : X) (Good : Q x) (I : ∀ g,s g=phaseOf (readClock p (bytes g) x).phase)
    (i j : Fin B) (g h : G) (DifferentPins : i≠j) (K : 2*p.streak≤B)
    (Tape : ∀ w, F w → ∃ u v tail e f,
      w=((u++[e])++(v++[f]))++tail ∧ u.length=i.val ∧ u.length+1+v.length=j.val ∧
      countedPaint (put (g,true)) p (bytes g) (u.foldl raw x) e=true ∧
      countedPaint (put (h,true)) p (bytes h) (((u++[e])++v).foldl raw x) f=true ∧
      (∃ pre rest,u=pre++rest ∧ cleanAt raw p (bytes g) x pre) ∧
      (g≠h → ∃ pre rest,(u++[e])++v=pre++rest ∧ cleanAt raw p (bytes h) x pre)) :
    2^(2*p.streak)*actualCount F B≤n^(B-2) := by
  apply key_count F put inj s i j g h DifferentPins K
  intro w WF
  obtain ⟨u,v,tail,e,f,E,L₁,L₂,P₁,P₂,⟨pre,rest,U,Clean⟩,Warm₂⟩ := Tape (List.ofFn w) WF
  let first := u++[e]
  let second := v++[f]
  have D (g : G) : put (g,false)≠put (g,true) := by
    intro H
    have T := congrArg Prod.snd (inj H)
    contradiction
  have A₀ : Credit (put (g,false)) (put (g,true)) p.streak
      (cleanAt raw p (bytes g) x) first := by
    unfold first
    rw [U] at P₁ ⊢
    exact credit_after_warm (W g) (Adj g) (D g) J x Good pre rest e Clean P₁
  have C₀ := certify_prefix put inj g (W g) (Adj g) J x Good s (I g) first A₀
  have ⟨A₁,Separate⟩ :
      Credit (put (h,false)) (put (h,true)) p.streak
        (cleanAt raw p (bytes h) x) (first++second) ∧
      (∀ k∈starts put g p.streak s first,k∉starts put h p.streak s (first++second)) := by
    by_cases Same : g=h
    · subst h
      have G₁ := wire_run_good (W g) x first Good
      have Clean₁ : ReportPulseWarmup.Clean (readClock p (bytes g) (first.foldl raw x)) := by
        unfold first
        rw [List.foldl_append]
        exact ReportPulseDoubleWarm.actual_paint_clean (W g) _ (Adj g) (D g) J _
          (wire_run_good (W g) x u Good) e P₁
      have P : countedPaint (put (g,true)) p (bytes g) (v.foldl raw (first.foldl raw x)) f=true := by
        rw [←List.foldl_append]
        exact P₂
      have R := (wire_fresh_mark (W g) _ (Adj g) (D g) J _ G₁ v f
        (wire_fresh_from_clean (W g) _ (Adj g) (D g) J _ G₁ Clean₁ v)).2 P
      have Sep := rebased_starts_lower put inj s g (W g) (Adj g) J x Good (I g) first second R
      refine ⟨?_,ordered_starts first.length _ _ (fun k H=>(C₀.labels k H).1) Sep⟩
      obtain ⟨pre',win,V,C,T⟩ := R
      refine ⟨first++pre',win,?_,?_,T⟩
      · change first++(v++[f])=first++pre'++win
        rw [V]
        exact (List.append_assoc first pre' win).symm
      · unfold cleanAt
        rw [List.foldl_append]
        exact C
    · obtain ⟨pre',rest',V,C⟩ := Warm₂ Same
      have B : Credit (put (h,false)) (put (h,true)) p.streak
          (cleanAt raw p (bytes h) x) (first++second) := by
        have H := credit_after_warm (W h) (Adj h) (D h) J x Good pre' rest' f C (V ▸ P₂)
        rw [←V,List.append_assoc] at H
        exact H
      have B' := raw_credit_start_tags put inj h (W h) (Adj h) J x Good s (I h) _ B
      exact ⟨B,distinct_gate_starts put inj s g h Same first second _ _
        (fun k H=>⟨(C₀.labels k H).1,(C₀.labels k H).2.1⟩) (fun k H=>(B' k H).2)⟩
  have C₁ := certify_prefix put inj h (W h) (Adj h) J x Good s (I h) (first++second) A₁
  rw [E]
  exact certify_keys put inj s g h i j first second tail (by simp [first,L₁])
    (by simp only [first,second,List.length_append,List.length_singleton];omega) C₀ C₁ Separate

#print axioms fixed_pair_actual
end L4.ReportPulseFixedPair
