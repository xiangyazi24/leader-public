import Leader.L4.BStarSealSafeReplay
import Leader.L4.BStarPublicationBirth

namespace L4.BStarNeedPrefix
open AllSizeProtocol BStarTrace BStarLongClaims BStarLongWork BStarLongToken
open BStarLongCommand BStarLongEvents BStarH6WordChart BStarAcquireVisitOrder
open BStarAcquireLiteralChain BStarResetChartTouch BStarResetMarkAdapter
open BStarGeneratedOwner BStarLongLandingCore BStarLongLiteral
open BStarSealSafeReplay BStarSealOwnerFrame BStarGrantWriterHistory BStarAcquireAnchors

variable {k₁ k₂ t₂ J₁ J₂ r c p c₁ n : Nat} (hp : 0<p)
local notation "B" => bStar k₁ k₂ t₂ J₁ J₂ r c p c₁ hp
local notation "X" => Fin n → LargeSite (production k₁ k₂ t₂ J₁ J₂ r c p c₁)
local notation "step" => AllSizeS1Geometry.step (n:=n) B
local notation "play" => BStarResetSchedule.run step

theorem publication_is_outgoing (x : X) (e i : Fin n)
    (notSilent : ¬NoPublication hp x e i) : e=i := by
  obtain ⟨s,C,p,b,loc,side,sel,lit⟩ := stopping_commit hp x e i notSilent
  let g := oldPair B x e
  let raw : Pair (BitVec LW) := ((x e).long,(x (rightNeighbor e)).long)
  have mem : C∈orderedCommands g := by
    rw [←actualOffers_claims g raw]
    exact List.mem_map.mpr ⟨_,sel,rfl⟩
  have eq := center_of g C mem lit.1
  subst C
  have left : s=.left := side.symm
  subst s
  exact loc.symm

theorem generated_append {base x : X} {addr : Nat→Pos n} {len : Nat}
    {u v : List (Fin n)} {a b c : Mode} (U : GeneratedOwner hp base addr len x a u b)
    (V : GeneratedOwner hp base addr len (play x u) b v c) :
    GeneratedOwner hp base addr len x a (u++v) c := by
  induction U with
  | endpoint _ => exact V
  | next I E _ ih => exact .next I E (ih V)

/-- A matched safe-tail replay has no earlier publication by its own
center. Arbitrary publications elsewhere are allowed. The test is on
the actual outgoing mark and uses its literal owning occurrence. -/
theorem no_earlier_publication {base origin x : X} {hh : ∃ j,oldH6 B base j=true}
    {o : Owners (oldH6 B base)} {S : List (Pos n)} {len : Nat} {fall : Pos n}
    (C : Chart hp base hh o S len fall) (sep : ∀ e : Fin n,e≠rightNeighbor e)
    (i : Fin n) (own : commandOwner (oldH6 B base) i 1=o.val)
    (k : Nat) (K : k≤len) (idx : S.getD k fall=(i,1))
    (lead w : List (Fin n)) (landed : play origin lead=x) (a b : Mode)
    (G : GeneratedOwner hp base (fun j=>S.getD j fall) len origin .idle lead a)
    (R : Replay hp base (fun j=>S.getD j fall) len i k x a w b) :
    BeforePublication hp x i w := by
  intro u e v split
  obtain ⟨m,P,I,F⟩ := before_mark hp R u e v split
  apply Classical.byContradiction
  intro bad
  have eI := publication_is_outgoing hp (play x u) e i bad
  have align : play origin (lead++u)=play x u := by
    rw [BStarResetSchedule.run_append,landed]
  obtain ⟨j,J,siteEq,mode,_⟩ := BStarPublicationBirth.commit_from_owner hp C sep
    (generated_append hp G (landed.symm ▸ P)) (align.symm ▸ I) e i own (align.symm ▸ bad)
  have L := C.length
  have E : j=k := (List.getD_inj (by omega) (by omega) C.nodup).mp (siteEq.trans idx.symm)
  subst j
  exact F.2 eI commitOp (.inr (.inr (.inr rfl))) mode

/-- Appending a completed model service to a prefix is legitimate for
a safety argument: if this prefix contains no same-owner publication,
it ends before the actual publication mark of the extended witness. -/
theorem prefix_before_first_publish (x : X) (i : Fin n)
    (w service pre rest : List (Fin n))
    (split : w++service=pre++i::rest)
    (pub : ¬NoPublication hp (play x pre) i i)
    (prior : BeforePublication hp x i w) :
    w<+:pre := by
  have p₁ : w<+:w++service := ⟨service,rfl⟩
  have p₂ : pre<+:w++service := ⟨i::rest,split.symm⟩
  by_cases H : w.length≤pre.length
  · exact List.prefix_of_prefix_length_le p₁ p₂ H
  · have p₃ : (pre++[i])<+:w++service := ⟨rest,by simpa [List.append_assoc] using split.symm⟩
    have early : pre++[i]<+:w := List.prefix_of_prefix_length_le p₃ p₁ (by simp; omega)
    obtain ⟨l,A⟩ := early
    have exactSplit : w=pre++i::l := by simpa [List.append_assoc] using A.symm
    exact (pub (prior pre i l exactSplit)).elim

end L4.BStarNeedPrefix
