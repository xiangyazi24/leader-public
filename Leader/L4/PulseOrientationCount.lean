import Leader.L4.PulseOrientation
import Leader.L4.Height.Window
namespace L4.PulseOrientation

private def box (xs : List α) (ys : List β) : List (α × β) :=
  xs.flatMap fun a => ys.map (a, ·)

private theorem mem_box {xs : List α} {ys : List β} {z : α × β} :
    z ∈ box xs ys ↔ z.1 ∈ xs ∧ z.2 ∈ ys := by
  obtain ⟨a,b⟩ := z
  simp [box, List.mem_flatMap, List.mem_map]

private theorem length_box (xs : List α) (ys : List β) :
    (box xs ys).length = xs.length * ys.length := by
  simp [box, List.length_flatMap, List.map_const', List.sum_replicate_nat]

private theorem nodup_box {xs : List α} {ys : List β}
    (X : xs.Nodup) (Y : ys.Nodup) : (box xs ys).Nodup := by
  induction xs with
  | nil => simp [box]
  | cons a xs ih =>
    obtain ⟨na,nx⟩ := List.nodup_cons.mp X
    change (ys.map (a, ·) ++ box xs ys).Nodup
    apply List.nodup_append.mpr
    refine ⟨List.Pairwise.map _ (fun _ _ H E => H (congrArg Prod.snd E)) Y, ih nx, ?_⟩
    intro z hz w hw eq
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hz
    subst w
    exact na (mem_box.mp hw).1

private def consPair {d : Nat} (z : α × (Fin d → α)) : Fin (d+1) → α :=
  Fin.cases z.1 z.2

private theorem consPair_inj {d : Nat} : Function.Injective (consPair (α:=α) (d:=d)) := by
  intro a b h
  apply Prod.ext
  · simpa [consPair] using congrFun h 0
  · funext i
    simpa [consPair] using congrFun h i.succ

private def words (xs : List α) : (d : Nat) → List (Fin d → α)
  | 0 => [Fin.elim0]
  | d+1 => (box xs (words xs d)).map consPair

private theorem words_len (xs : List α) (d : Nat) :
    (words xs d).length=xs.length^d := by
  induction d with
  | zero => simp [words]
  | succ d ih => simp [words,length_box,ih,Nat.pow_succ,Nat.mul_comm]

private theorem words_nodup {xs : List α} (h : xs.Nodup) (d : Nat) :
    (words xs d).Nodup := by
  induction d with
  | zero => simp [words]
  | succ d ih =>
    exact List.Pairwise.map _ (fun _ _ H E => H (consPair_inj E)) (nodup_box h ih)

private theorem mem_words {xs : List α} {d : Nat} (w : Fin d → α)
    (h : ∀ i, w i ∈ xs) : w ∈ words xs d := by
  induction d with
  | zero =>
    apply List.mem_singleton.mpr
    exact funext fun i => Fin.elim0 i
  | succ d ih =>
    apply List.mem_map.mpr
    refine ⟨(w 0, fun i => w i.succ), mem_box.mpr ⟨h 0, ih _ (fun i => h i.succ)⟩, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [consPair]

private def sw [DecidableEq α] (p q i : α) : α :=
  if i=p then q else if i=q then p else i

private theorem sw_left [DecidableEq α] (p q : α) : sw p q p=q := by simp [sw]
private theorem sw_right [DecidableEq α] (p q : α) : sw p q q=p := by
  by_cases h : q=p <;> simp [sw,h]
private theorem sw_inv [DecidableEq α] (p q i : α) : sw p q (sw p q i)=i := by
  by_cases hp : i=p
  · subst i; rw [sw_left,sw_right]
  by_cases hq : i=q
  · subst i; rw [sw_right,sw_left]
  simp [sw,hp,hq]

private theorem sw_inj [DecidableEq α] (p q : α) : Function.Injective (sw p q) := by
  intro a b h
  simpa only [sw_inv] using congrArg (sw p q) h

private theorem two_pin_embed {n B : Nat} (p q : Fin B) (u v : Fin n) (pq : p≠q) :
    ∃ f : {w : Word n B // w p=u ∧ w q=v} → Word n (B-2), Function.Injective f := by
  cases B with
  | zero => exact Fin.elim0 p
  | succ B =>
    cases B with
    | zero => exact False.elim (pq (Fin.ext (by omega)))
    | succ d =>
      let s := sw p 0
      let r := s q
      have r0 : r≠0 := fun E => pq ((sw_inj p 0) ((sw_left p 0).trans E.symm))
      let t := sw r (Fin.succ (0 : Fin (d+1)))
      have t0 : t 0=0 := by
        simp [t,sw,Ne.symm r0]
      have hp : s (t 0)=p := by rw [t0]; exact sw_right p 0
      have hq : s (t (Fin.succ (0 : Fin (d+1))))=q := by
        rw [show t (Fin.succ (0 : Fin (d+1)))=r from sw_right _ _]
        exact sw_inv _ _ _
      refine ⟨fun z i => z.val (s (t i.succ.succ)), ?_⟩
      intro a b e
      apply Subtype.ext
      funext j
      have onto : s (t (t (s j)))=j := by
        rw [show t (t (s j))=s j from sw_inv _ _ _, show s (s j)=j from sw_inv _ _ _]
      rw [←onto]
      generalize t (s j) = i
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [hp,a.property.1,b.property.1]
      · refine Fin.cases ?_ (fun l => ?_) k
        · rw [hq,a.property.2,b.property.2]
        · exact congrFun e l

theorem count_pinned {n B k : Nat} {A : Word n B → Prop}
    (credited : List {w // A w}) (hcredit : credited.Nodup)
    (p q : Fin B) (u v : Fin n) (pq : p≠q)
    (f : ({w // A w} × (Fin k → Bool)) → {w : Word n B // w p=u ∧ w q=v})
    (hf : Function.Injective f) : 2^k * credited.length ≤ n^(B-2) := by
  obtain ⟨g,hg⟩ := two_pin_embed p q u v pq
  let orientations := words [false,true] k
  let src := box credited orientations
  let dest := words (List.finRange n) (B-2)
  have H : (src.map (g ∘ f)).Nodup :=
    List.Pairwise.map _ (fun _ _ ne eq => ne (hf (hg eq))) <|
      nodup_box hcredit (words_nodup (by decide) k)
  have K : src.map (g ∘ f) ⊆ dest := fun {w} _ => mem_words w (fun i => List.mem_finRange (w i))
  have L := H.length_le_of_subset K
  simpa [src, dest, orientations, length_box,words_len,Nat.mul_comm] using L

theorem count_overwrite {B k n : Nat} {S : Type} (M : Model n B k S)
    (A : Word n B→Prop) (credited : List {w // A w}) (hcredit : credited.Nodup)
    (p q : Fin B) (u v : Fin n) (pq : p≠q)
    (orig : ∀ w,A w→Original M w)
    (stable : ∀ w,A w→∀ bits,M.key (overwrite M w bits)=M.key w)
    (pins : ∀ w,A w→w p=u ∧ w q=v)
    (avoid : ∀ w,A w→∀ i,M.start (M.key w) i≠p ∧ M.start (M.key w) i≠q) :
    2^k * credited.length ≤ n^(B-2) := by
  obtain ⟨f,hf⟩ := into_pinned M A p q u v orig stable pins avoid
  exact count_pinned credited hcredit p q u v pq f hf

end L4.PulseOrientation

namespace L4.PulseOrientation
open Height

def allWords (n B : Nat) : List (Word n B) := words (List.finRange n) B

theorem allWords_nodup (n B : Nat) : (allWords n B).Nodup :=
  words_nodup (List.nodup_finRange n) B

private theorem sum_flatMap_map (f : β→Nat) (g : α→List β) (l : List α) :
    ((l.flatMap g).map f).sum=(l.map fun a=>(g a |>.map f).sum).sum := by
  induction l with
  | nil => rfl
  | cons a l IH => simp [List.sum_append,IH]

theorem allWords_wordSum (f : List (Fin n)→Nat) (B : Nat) :
    ((allWords n B).map (f ∘ List.ofFn)).sum=Height.wordSum f B := by
  induction B generalizing f with
  | zero => rfl
  | succ B IH =>
    simp only [allWords,words,List.map_map,box,sum_flatMap_map]
    rw [Height.wordSum]
    have R (g : Fin n→Nat) : (List.finRange n).map g = List.ofFn g := by
      simp [List.finRange,List.map_ofFn,Function.comp_def]
    rw [←R]
    congr 1
    apply List.map_congr_left
    intro e _
    simp only [Function.comp_def,List.ofFn_succ,consPair,Fin.cases_zero,Fin.cases_succ]
    exact IH (fun v=>f (e::v))

end L4.PulseOrientation

