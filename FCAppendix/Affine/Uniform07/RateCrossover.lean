import FCAppendix.Affine.Uniform07.RateContinuity

noncomputable section
namespace FCAppendix.Affine.Uniform07
open Set

def sourceZlo : Row → ℝ | .first => 739/1000 | .second => 691/1000

theorem exists_source_rate_crossover (i : Row) :
    ∃ z∈Ioo (sourceZlo i) (sourceZhi i), canonicalRate i z=pureRate i z := by
  have hlohi : sourceZlo i<sourceZhi i := by cases i <;> norm_num [sourceZlo,sourceZhi]
  have hi : sourceZhi i≤x i := by cases i <;> norm_num [sourceZhi,x,xQ]
  have hlo : (1/2:ℝ)≤sourceZlo i := by cases i <;> norm_num [sourceZlo]
  have hsubset : Icc (sourceZlo i) (sourceZhi i) ⊆ Icc (1/2) (sourceZhi i) :=
    fun _ hz => ⟨hlo.trans hz.1,hz.2⟩
  have hxsubset : Icc (sourceZlo i) (sourceZhi i) ⊆ Icc (1/2) (x i) :=
    fun _ hz => ⟨hlo.trans hz.1,hz.2.trans hi⟩
  have hp : ContinuousOn (pureRate i) (Icc (1/2) (x i)) := by
    intro z hz
    exact (pure_rate_derivative i hz).continuousAt.continuousWithinAt
  have hc := ((continuous_source_rate i).mono hsubset).sub (hp.mono hxsubset)
  have hleft : 0<canonicalRate i (sourceZlo i)-pureRate i (sourceZlo i) := by
    cases i
    · exact sub_pos.mpr canonical_lower_endpoint_gap.1
    · exact sub_pos.mpr canonical_lower_endpoint_gap.2
  have hright : canonicalRate i (sourceZhi i)-pureRate i (sourceZhi i)<0 :=
    sub_neg.mpr (no_source_crossover_above_zhi i ⟨le_rfl,hi⟩)
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc' hlohi.le hc ⟨hright.le,hleft.le⟩
  change canonicalRate i z-pureRate i z=0 at hroot
  refine ⟨z,⟨?_,?_⟩,sub_eq_zero.mp hroot⟩
  · by_contra hn
    have he : z=sourceZlo i := le_antisymm (le_of_not_gt hn) hz.1
    rw [he] at hroot
    linarith
  · by_contra hn
    have he : z=sourceZhi i := le_antisymm hz.2 (le_of_not_gt hn)
    rw [he] at hroot
    linarith
end FCAppendix.Affine.Uniform07
