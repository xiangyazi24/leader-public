import Leader.L4.PulseOrientationRaw

namespace L4.ReportPulseJointCount
open PulseOrientation ReportPulseRecode

variable {n B k : Nat} {G : Type} [DecidableEq G]

private def certified {Y : Type} (P : Y→Prop) [DecidablePred P] :
    List Y → List {y // P y}
  | [] => []
  | y::ys => if H : P y then ⟨y,H⟩::certified P ys else certified P ys

private theorem certified_mem {Y : Type} (P : Y→Prop) [DecidablePred P]
    (ys : List Y) (a : {y // P y}) (H : a∈certified P ys) : a.val∈ys := by
  induction ys with
  | nil => simp [certified] at H
  | cons y ys IH =>
    unfold certified at H
    split at H
    · rcases List.mem_cons.mp H with E|E
      · exact List.mem_cons.mpr (.inl (congrArg Subtype.val E))
      · exact List.mem_cons.mpr (.inr (IH E))
    · exact List.mem_cons.mpr (.inr (IH H))

private theorem certified_nodup {Y : Type} (P : Y→Prop) [DecidablePred P]
    (ys : List Y) (H : ys.Nodup) : (certified P ys).Nodup := by
  induction ys with
  | nil => simp [certified]
  | cons y ys IH =>
    obtain ⟨N,D⟩ := List.nodup_cons.mp H
    unfold certified
    split
    · apply List.nodup_cons.mpr
      exact ⟨fun E=>N (certified_mem P ys _ E), IH D⟩
    · exact IH D

private theorem certified_length {Y : Type} (P : Y→Prop) [DecidablePred P] (ys : List Y) :
    (certified P ys).length=(ys.map (fun y=>if P y then 1 else 0)).sum := by
  induction ys with
  | nil => rfl
  | cons y ys IH =>
    by_cases W : P y
    · simp [certified,W,IH,Nat.add_comm]
    · simp [certified,W,IH]

noncomputable def recodeWord (put : G×Bool→Fin n) (s : Phase G) (w : Word n B) : Word n B :=
  fun i => (encodeFin put s (List.ofFn w))[i.val]'(by
    rw [encodeFin_length,List.length_ofFn]
    exact i.isLt)

theorem ofFn_recodeWord (put : G×Bool→Fin n) (s : Phase G) (w : Word n B) :
    List.ofFn (recodeWord put s w)=encodeFin put s (List.ofFn w) := by
  apply List.ext_getElem
  · rw [List.length_ofFn,encodeFin_length,List.length_ofFn]
  · intro i H J
    rw [List.getElem_ofFn]
    rfl

theorem recodeWord_inj (put : G×Bool→Fin n) (inj : Function.Injective put) (s : Phase G) :
    Function.Injective (recodeWord (B:=B) put s) := by
  intro u v E
  have L := congrArg List.ofFn E
  rw [ofFn_recodeWord,ofFn_recodeWord] at L
  have D := congrArg (decodeFin put s) L
  rw [decode_encodeFin put inj,decode_encodeFin put inj] at D
  funext i
  have J := congrArg (fun w : List (Fin n) => w[i.val]?) D
  rw [List.getElem?_ofFn,List.getElem?_ofFn,dif_pos i.isLt,dif_pos i.isLt] at J
  exact Option.some.inj J

noncomputable def actualCount (F : List (Fin n)→Prop) (B : Nat) : Nat := by
  classical
  exact Height.wordSum (fun w=>if F w then 1 else 0) B

/-- Convert the exact recoded injection into a bound on the original
IID word count. The bijection is used only to count originals; it
does not alter the monitored raw scheduler or its publication marks. -/
theorem count_on_original_tapes (F : List (Fin n)→Prop)
    (put : G×Bool→Fin n) (inj : Function.Injective put) (s : Phase G)
    (start : Skeleton G→Fin k→Fin B) (gate : Skeleton G→Fin k→G)
    (distinct : ∀ z,Function.Injective (start z))
    (p q : Fin B) (g₁ g₂ : G) (pq : p≠q)
    (starts : ∀ w : Word n B,F (List.ofFn w)→∀ i,
      let z := rawKey put (armed s) (recodeWord put s w)
      z[(start z i).val]?=some (some (.start (gate z i))))
    (orig : ∀ w : Word n B,F (List.ofFn w)→∀ i,
      let z := rawKey put (armed s) (recodeWord put s w)
      recodeWord put s w (start z i)=put (gate z i,true))
    (pins : ∀ w : Word n B,F (List.ofFn w)→
      let z := rawKey put (armed s) (recodeWord put s w)
      z[p.val]?=some (some (.complete g₁)) ∧ z[q.val]?=some (some (.complete g₂))) :
    2^k*actualCount F B≤n^(B-2) := by
  classical
  let P : Word n B→Prop := fun w=>F (List.ofFn w)
  let A : Word n B→Prop := fun w=>∃ v,P v ∧ recodeWord put s v=w
  let xs := certified P (allWords n B)
  let mapCert (v : {w // P w}) : {w // A w} :=
    ⟨recodeWord put s v.val,⟨v.val,v.property,rfl⟩⟩
  let ys := xs.map mapCert
  have IN : Function.Injective mapCert := by
    intro u v E
    apply Subtype.ext
    exact recodeWord_inj put inj s (congrArg Subtype.val E)
  have Nodup : ys.Nodup :=
    List.Pairwise.map _ (fun _ _ H E=>H (IN E)) (certified_nodup P _ (allWords_nodup n B))
  have S (w : Word n B) (H : A w) :
      ∀ i,(rawKey put (armed s) w)[(start (rawKey put (armed s) w) i).val]?=
        some (some (.start (gate (rawKey put (armed s) w) i))) := by
    obtain ⟨v,V,rfl⟩ := H
    exact starts v V
  have O (w : Word n B) (H : A w) :
      ∀ i,w (start (rawKey put (armed s) w) i)=put (gate (rawKey put (armed s) w) i,true) := by
    obtain ⟨v,V,rfl⟩ := H
    exact orig v V
  have Pn (w : Word n B) (H : A w) :
      (rawKey put (armed s) w)[p.val]?=some (some (.complete g₁)) ∧
        (rawKey put (armed s) w)[q.val]?=some (some (.complete g₂)) := by
    obtain ⟨v,V,rfl⟩ := H
    exact pins v V
  have C := raw_count put inj (armed s) start gate distinct ys Nodup p q g₁ g₂ pq S O Pn
  have E : ys.length=actualCount F B := by
    change (xs.map mapCert).length=_
    rw [List.length_map]
    unfold xs
    rw [certified_length]
    exact allWords_wordSum (fun w=>if F w then 1 else 0) B
  rwa [E] at C

end L4.ReportPulseJointCount
