import Leader.L4.BStarLongGrant

/-! Old grants remain attached to their incidence until its own
release. The abstract arbiter is resolved from the old triple, not
from an intermediate state that has already cleared it. -/
namespace L4.BStarGrantRetention
open L4.BStarLongGrant

theorem keep_canonical (old rel ask : Ports) (j : Fin 3)
    (h : canonical old j=true) :
    result old rel ask j = !rel j := by
  have hn : win old rel ask j=false := by
    by_cases e : j=1
    · subst j
      exact writer_no_same_mark_refill _ _ _ (.inr (.inl h))
    · simp [win,e,h]
  simp [result,hn,h]

theorem no_reader_grant_during_writer (old rel ask : Ports)
    (h : canonical old 1=true) (j : Fin 3) (hn : j≠1) :
    result old rel ask j=false := by
  have w : old 1=true := by
    cases e : old 1
    · simp [canonical,e] at h
    · rfl
  simp [result,win,canonical,w,hn]

theorem no_writer_replaces_reader (old rel ask : Ports)
    (j : Fin 3) (hn : j≠1) (h : canonical old j=true) :
    result old rel ask 1=false := by
  have e : old 1=false := by
    cases A : old 1
    · rfl
    · simp [canonical,A,hn] at h
  have ne : j=0 ∨ j=2 := by
    have L := j.isLt
    have I : j.val≠1 := fun v => hn (Fin.ext v)
    rcases (show j.val=0 ∨ j.val=2 by omega) with a|a
    · exact .inl (Fin.ext a)
    · exact .inr (Fin.ext a)
  have denied : win old rel ask 1=false := by
    rcases ne with rfl|rfl
    · exact writer_no_same_mark_refill _ _ _ (.inl h)
    · exact writer_no_same_mark_refill _ _ _ (.inr (.inr h))
  simp [result,canonical,e,denied]

theorem coherent_succ (old rel ask : Ports) : conflict (result old rel ask)=false := by
  by_cases w : canonical old 1=true
  · have zero := no_reader_grant_during_writer old rel ask w 0 (by decide)
    have two := no_reader_grant_during_writer old rel ask w 2 (by decide)
    simp [conflict,zero,two]
  · by_cases r0 : canonical old 0=true
    · simp [conflict,no_writer_replaces_reader old rel ask 0 (by decide) r0]
    · by_cases r2 : canonical old 2=true
      · simp [conflict,no_writer_replaces_reader old rel ask 2 (by decide) r2]
      · have z : canonical old 1=false := Bool.eq_false_iff.mpr w
        have z0 : canonical old 0=false := Bool.eq_false_iff.mpr r0
        have z2 : canonical old 2=false := Bool.eq_false_iff.mpr r2
        have eq : result old rel ask 1=win old rel ask 1 := by simp [result,z]
        cases A : win old rel ask 1
        · simp [conflict,eq,A]
        · have Z j (h : canonical old j=false) (he : j≠1) :
              result old rel ask j=false := by
            have aw : ((!((canonical old 0 || canonical old 1) || canonical old 2)) &&
                ask 1 && !rel 1)=true := by simpa [win] using A
            simp only [result,win,he,if_false,h,aw,Bool.not_true,Bool.false_and,Bool.false_or]
          simp [conflict,eq,A,Z 0 z0 (by decide),Z 2 z2 (by decide)]

end L4.BStarGrantRetention
