import Leader.L4.BStarFenceCrossing
import Leader.L4.Height.FenceDependencyPaths

namespace L4.BStarFenceCrossingGraph
open BStarFenceShadow
open L4.Height.FenceDependencyPaths (Row Ranked)

abbrev Vertex (k : Nat) := Fin k × Nat

def upstream {k : Nat} (j : Fin k) (m : Nat) : Option (Vertex k) :=
  if h : 0<j.val then if 1<m then some (predIdx j h,m-1) else none else none

def downstream {k : Nat} (j : Fin k) (m : Nat) : Option (Vertex k) :=
  if h : j.val+1<k then some (succIdx j h,m) else none

@[simp] theorem upstream_live {k : Nat} (j : Fin k) (m : Nat)
    (h : 0<j.val) (hm : 1<m) : upstream j m=some (predIdx j h,m-1) := by
  simp [upstream,h,hm]

@[simp] theorem upstream_first {k : Nat} (j : Fin k) (m : Nat)
    (hm : ¬1<m) : upstream j m=none := by
  simp [upstream,hm]

@[simp] theorem upstream_inlet {k : Nat} (j : Fin k) (m : Nat)
    (h : ¬0<j.val) : upstream j m=none := by
  simp [upstream,h]

@[simp] theorem downstream_live {k : Nat} (j : Fin k) (m : Nat)
    (h : j.val+1<k) : downstream j m=some (succIdx j h,m) := by
  simp [downstream,h]

@[simp] theorem downstream_outlet {k : Nat} (j : Fin k) (m : Nat)
    (h : ¬j.val+1<k) : downstream j m=none := by
  simp [downstream,h]

def row {n k : Nat} (port : Fin k→Fin n) (v : Vertex k) : Row (Vertex k) (Fin n) :=
  if v.2=0 then .stop else
    match upstream v.1 v.2, downstream v.1 v.2 with
    | none,none => .source (port v.1)
    | some p,none => .one (port v.1) p
    | none,some q => .one (port v.1) q
    | some p,some q => .two (port v.1) p q

@[simp] theorem row_zero {n k : Nat} (port : Fin k→Fin n) (j : Fin k) :
    row port (j,0)=.stop := by simp [row]

def rank {k : Nat} (v : Vertex k) : Nat :=
  if v.2=0 then 0 else BStarFenceCrossing.depth v.1 v.2-1

theorem rank_pos {k : Nat} (j : Fin k) (m : Nat) (hm : 0<m) :
    0<rank (j,m) := by simp only [rank,if_neg (by omega : m≠0),
      BStarFenceCrossing.depth]; omega

theorem upstream_rank {k : Nat} (j : Fin k) (m : Nat) (a : Vertex k)
    (P : upstream j m=some a) : rank a<rank (j,m) := by
  unfold upstream at P
  split at P
  · rename_i h
    split at P
    · rename_i hm
      obtain rfl := Option.some.inj P
      have H := (BStarFenceCrossing.dependency_depth j m (by omega)).2.1 h
      have L := rank_pos (predIdx j h) (m-1) (by omega)
      simp only [rank,if_neg (by omega : m≠0),if_neg (by omega : m-1≠0)] at L ⊢
      omega
    · contradiction
  · contradiction

theorem downstream_rank {k : Nat} (j : Fin k) (m : Nat) (a : Vertex k)
    (hm : 0<m) (P : downstream j m=some a) : rank a<rank (j,m) := by
  unfold downstream at P
  split at P
  · rename_i h
    obtain rfl := Option.some.inj P
    have H := (BStarFenceCrossing.dependency_depth j m hm).2.2 h
    have L := rank_pos (succIdx j h) m hm
    simp only [rank,if_neg (by omega : m≠0)] at L ⊢
    omega
  · contradiction

theorem ranked {n k : Nat} (port : Fin k→Fin n) : Ranked (row port) rank := by
  intro ⟨j,m⟩
  unfold row
  by_cases M : m=0
  · simp only [if_pos M]
  · simp only [if_neg M]
    cases U : upstream j m <;> cases D : downstream j m
    · exact rank_pos j m (by omega)
    · exact downstream_rank j m _ (by omega) D
    · exact upstream_rank j m _ U
    · exact ⟨upstream_rank j m _ U,downstream_rank j m _ (by omega) D⟩

theorem rank_bound {k : Nat} (j : Fin k) (m : Nat) (M : m≤j.val+1) :
    rank (j,m)≤2*k-1 := by
  have B := BStarFenceCrossing.depth_bound j m M
  unfold rank
  dsimp only
  split <;> omega

theorem sink_rank {k : Nat} (j : Fin k) (J : j.val+1=k) : rank (j,k)=2*k-1 := by
  have K : k≠0 := by omega
  simp only [rank,if_neg K,BStarFenceCrossing.depth]
  omega

def Feasible {k : Nat} (v : Vertex k) : Prop := v.2≤v.1.val+1

theorem upstream_feasible {k : Nat} (j : Fin k) (m : Nat) (v : Vertex k)
    (M : Feasible (j,m)) (P : upstream j m=some v) : Feasible v := by
  unfold upstream at P
  split at P
  · rename_i h
    split at P
    · obtain rfl := Option.some.inj P
      change m-1≤j.val-1+1
      change m≤j.val+1 at M
      omega
    · contradiction
  · contradiction

theorem downstream_feasible {k : Nat} (j : Fin k) (m : Nat) (v : Vertex k)
    (M : Feasible (j,m)) (P : downstream j m=some v) : Feasible v := by
  unfold downstream at P
  split at P
  · obtain rfl := Option.some.inj P
    change m≤j.val+1+1
    change m≤j.val+1 at M
    omega
  · contradiction

/-- The graph keeps all syntactic vertices. Since a feasible target
has only feasible parents, pad the irrelevant cuts by zero to use the
global CorrectCuts interface without claiming impossible crossings. -/
def padCut {k : Nat} (cut : Vertex k → Nat) (v : Vertex k) : Nat :=
  if v.2≤v.1.val+1 then cut v else 0

@[simp] theorem padCut_of_feasible {k : Nat} (cut : Vertex k → Nat) (v : Vertex k)
    (F : Feasible v) : padCut cut v=cut v := if_pos F

theorem correctCuts_of_feasible {n k : Nat} (port : Fin k→Fin n)
    (f : Fin n→Nat→Nat) (start : Nat) (cut : Vertex k→Nat)
    (H : ∀ v, Feasible v → match row port v with
      | .stop => cut v≤start
      | .source a => cut v≤f a start
      | .one a p => cut v≤f a (cut p)
      | .two a p q => cut v≤f a (max (cut p) (cut q))) :
    L4.Height.FenceDependencyPaths.CorrectCuts (row port) f start (padCut cut) := by
  intro ⟨j,m⟩
  by_cases F : Feasible (j,m)
  · rw [padCut_of_feasible cut _ F]
    have D := H (j,m) F
    unfold row at D ⊢
    by_cases M : m=0
    · simpa only [if_pos M] using D
    · simp only [if_neg M] at D ⊢
      cases E : upstream j m <;> cases N : downstream j m
      · simpa only [E,N] using D
      · rename_i q
        change cut (j,m)≤f (port j) (padCut cut q)
        rw [padCut_of_feasible cut _ (downstream_feasible j m _ F N)]
        simpa only [E,N] using D
      · rename_i p
        change cut (j,m)≤f (port j) (padCut cut p)
        rw [padCut_of_feasible cut _ (upstream_feasible j m _ F E)]
        simpa only [E,N] using D
      · rename_i p q
        change cut (j,m)≤f (port j) (max (padCut cut p) (padCut cut q))
        rw [padCut_of_feasible cut _ (upstream_feasible j m _ F E),
            padCut_of_feasible cut _ (downstream_feasible j m _ F N)]
        simpa only [E,N] using D
  · have Z : padCut cut (j,m)=0 := if_neg F
    rw [Z]
    cases E : row port (j,m) <;> exact Nat.zero_le _

end L4.BStarFenceCrossingGraph
