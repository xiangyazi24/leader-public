import Leader.L4.BStarLongCommand

/-! Long K transport and write-intent lowering. A forward's effect has
already resolved its FENCE/cancellation/ARITH/headers before feeding
`advanceK`. This layer does not pretend those operations are passive. -/
namespace L4.BStarLongTransport
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongToken BStarLongCommand
open BStarLongLayout

abbrev AtK := At (Fin 11)
abbrev KWrite := AtK × Token
abbrev ReadK := AtK → Token

def readK (x : Pair (BitVec LW)) : ReadK :=
  fun a => atSite (lane (a.side==.right) x) a.occurrence

def lowerOne (t : KWrite) : Bool × Patch LW :=
  (t.1.side==.right,setToken t.1.occurrence t.2)

def compile (ks : List KWrite) : Pair (Patch LW) :=
  lower (ks.map lowerOne)

def assign (r : ReadK) (u : KWrite) : ReadK :=
  fun a => if a=u.1 then u.2 else r a

theorem read_one (x : Pair (BitVec LW)) (t : KWrite) :
    readK (runWrite x (lowerOne t))=assign (readK x) t := by
  obtain ⟨⟨side,j⟩,token⟩ := t
  funext a
  obtain ⟨s,i⟩ := a
  cases side <;> cases s
  all_goals
    by_cases h : i=j
    · subst j
      simp [readK,runWrite,lowerOne,lane,assign,atSite_after]
    · simp [readK,runWrite,lowerOne,lane,assign,h,other_token_holds]

theorem fold_reads (ks : List KWrite) (x : Pair (BitVec LW)) :
    readK ((ks.map lowerOne).foldl runWrite x) =
      ks.foldl assign (readK x) := by
  induction ks generalizing x with
  | nil => rfl
  | cons a tail ih =>
    simp only [List.map_cons,List.foldl_cons,ih,read_one]

/-- Actual patch projection for arbitrary packed incoming bytes and any
ordered K intents, including overriding an initial canonical fault. -/
theorem exact_k_transfer (ks : List KWrite) (x : Pair (BitVec LW)) :
    readK (patchPair (compile ks) x)=ks.foldl assign (readK x) := by
  rw [compile,lower_apply,fold_reads]

def allSlots : List AtK := (List.finRange 11).map L ++ (List.finRange 11).map R

def bound (g : Pair LongGeometry) (old : ReadK) (a : AtK) : Token :=
  bind (geometry g a.side) a.occurrence (old a)

def isFault : Token → Bool
  | .forward p | .reply p => p.fault==1
  | _ => false

def normalization (g : Pair LongGeometry) (old : ReadK) : List KWrite :=
  (allSlots.filterMap fun a =>
    let b := bound g old a
    if isFault b then some (a,b) else none) ++
  (discarded g).map (fun a => (a,.empty))

/-- Middle step of routing. A request to run the source door or perform
a forward opcode does not get swallowed in this transport function. -/
def direct (c : CommandClaim) : Offer → List KWrite
  | .clear => [(c.source,.empty)]
  | .reverse t => match c.destination with
    | none => []
    | some q => [(c.source,t),(q,.empty)]
  | _ => []

def advanceK (g : Pair LongGeometry) (c : CommandClaim) (p : Payload) : List KWrite :=
  match c.destination with
  | none => [(c.source,finish p)]
  | some q => [(c.source,.trail),
      (q,arrive (geometry g q.side) q.occurrence p)]

def observations (g : Pair LongGeometry) (old : ReadK) (written : List KWrite) : List KWrite :=
  allSlots.filterMap fun a =>
    if written.any (fun q => q.1==a) then none
    else match bound g old a with
      | .forward p => (observe a (geometry g a.side) p).map (fun q => (a,.forward q))
      | _ => none

theorem no_observe_written (g : Pair LongGeometry) (old : ReadK) (ks : List KWrite)
    (a : AtK) (t : Token) (h : ∃ q∈ks,q.1=a) :
    (a,t) ∉ observations g old ks := by
  intro hm
  unfold observations at hm
  obtain ⟨a',_,E⟩ := List.mem_filterMap.mp hm
  have aa : a'=a := by
    split at E
    · contradiction
    split at E
    all_goals simp_all
    exact E.choose_spec.2.1
  subst a'
  have H : ks.any (fun q => q.1==a)=true := by
    obtain ⟨q,hq,e⟩ := h
    apply List.any_eq_true.mpr
    exact ⟨q,hq,beq_iff_eq.mpr e⟩
  simp [H] at E

#print axioms exact_k_transfer
#print axioms no_observe_written
end L4.BStarLongTransport
