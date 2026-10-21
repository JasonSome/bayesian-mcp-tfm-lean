import FCAppendix.Affine.Uniform07Finishing.Crossover.RateAndError

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open Set Filter Topology

theorem right_increment_derivative_lower
    {f : ℝ→ℝ} {f' b right lower : ℝ}
    (hbr : b< right) (hf : HasDerivAt f f' b)
    (hinc : ∀ z∈Ioo b right, lower*(z-b)≤ f z-f b) :
    lower≤ f' := by
  have hslope : Tendsto (slope f b) (𝓝[>] b) (𝓝 f') :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have hR : ∀ᶠ z in 𝓝[>] b, z< right :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbr)
  have hbound : ∀ᶠ z in 𝓝[>] b, lower≤ slope f b z := by
    filter_upwards [self_mem_nhdsWithin,hR] with z hbz hzr
    change lower≤(z-b)⁻¹*(f z-f b)
    rw [←div_eq_inv_mul]
    exact (le_div_iff₀ (sub_pos.mpr hbz)).2 (hinc z ⟨hbz,hzr⟩)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hslope hbound

def negativePhysicalSourceRate (row : Uniform07.Row) (b : ℝ) : ℝ :=
  -Uniform07.canonicalRate row (b/Uniform07.cutoff row)

theorem physical_source_increment (row : Uniform07.Row) {b b' : ℝ}
    (hb : b∈Icc (Uniform07.cutoff row/2)
      (Uniform07.sourceZhi row*Uniform07.cutoff row))
    (hb' : b'∈Icc (Uniform07.cutoff row/2)
      (Uniform07.sourceZhi row*Uniform07.cutoff row))
    (hbb' : b≤ b') :
    (Uniform07.slopeRatioLower row/500)*(b'-b)≤
      negativePhysicalSourceRate row b'-negativePhysicalSourceRate row b := by
  have ht := Uniform07.cutoff_pos row
  have hnorm {z : ℝ}
      (hz : z∈Icc (Uniform07.cutoff row/2)
        (Uniform07.sourceZhi row*Uniform07.cutoff row)) :
      z/Uniform07.cutoff row∈Icc (1/2:ℝ) (Uniform07.sourceZhi row) := by
    constructor
    · apply (le_div_iff₀ ht).2
      linarith [hz.1]
    · exact (div_le_iff₀ ht).2 hz.2
  have h := Uniform07.source_canonical_increment_lower row (hnorm hb) (hnorm hb')
    (div_le_div_of_nonneg_right hbb' ht.le)
  have hscale : Uniform07.cutoff row*(Uniform07.slopeRatioLower row/500)*
      (b'/Uniform07.cutoff row-b/Uniform07.cutoff row)=
      (Uniform07.slopeRatioLower row/500)*(b'-b) := by
    field_simp [ht.ne']
  rw [hscale] at h
  simpa only [negativePhysicalSourceRate,neg_sub_neg] using h

theorem physical_source_slope_lower (row : Uniform07.Row) {b A : ℝ}
    (hb : b∈Icc (Uniform07.cutoff row/2)
      (Uniform07.sourceZhi row*Uniform07.cutoff row))
    (hA : HasDerivAt (negativePhysicalSourceRate row) A b) :
    Uniform07.slopeRatioLower row/500≤ A := by
  let L := Uniform07.cutoff row/2
  let R := Uniform07.sourceZhi row*Uniform07.cutoff row
  have hLR : L< R := by
    have ht := Uniform07.cutoff_pos row
    have hz : (1/2:ℝ)< Uniform07.sourceZhi row := by
      cases row <;> norm_num [Uniform07.sourceZhi]
    dsimp [L,R]
    nlinarith
  by_cases hbr : b< R
  · apply right_increment_derivative_lower hbr hA
    intro z hz
    exact physical_source_increment row hb ⟨hb.1.trans hz.1.le,hz.2.le⟩ hz.1.le
  · have hbeq : b=R := le_antisymm hb.2 (le_of_not_gt hbr)
    have hLb : L< b := by simpa only [hbeq] using hLR
    have hleft := left_comparison_derivative_lower hLb hA
      (error := -(Uniform07.slopeRatioLower row/500)) (by
        intro z hz
        have h := physical_source_increment row ⟨hz.1.le,hz.2.le.trans hb.2⟩ hb hz.2.le
        linarith)
    simpa only [neg_neg] using hleft

theorem physical_source_slope_lower_within (row : Uniform07.Row) {b A : ℝ}
    (hb : b∈Icc (Uniform07.cutoff row/2)
      (Uniform07.sourceZhi row*Uniform07.cutoff row))
    (hA : HasDerivWithinAt (negativePhysicalSourceRate row) A
      (Icc (Uniform07.cutoff row/2)
        (Uniform07.sourceZhi row*Uniform07.cutoff row)) b) :
    Uniform07.slopeRatioLower row/500≤ A := by
  let L:=Uniform07.cutoff row/2
  let R:=Uniform07.sourceZhi row*Uniform07.cutoff row
  have hLR : L< R := by
    have ht:=Uniform07.cutoff_pos row
    have hz : (1/2:ℝ)< Uniform07.sourceZhi row := by
      cases row <;> norm_num [Uniform07.sourceZhi]
    dsimp [L,R]
    nlinarith
  have hs:=hasDerivWithinAt_iff_tendsto_slope.mp hA
  by_cases hbr : b< R
  · have hfilter : 𝓝[>] b≤𝓝[Icc L R\{b}] b := by
      rw [nhdsWithin]
      apply le_inf nhdsWithin_le_nhds
      apply le_principal_iff.mpr
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbr)] with z hbz hzr
      exact ⟨⟨hb.1.trans hbz.le,hzr.le⟩,by simpa only [mem_singleton_iff] using hbz.ne'⟩
    have hslim : Tendsto (slope (negativePhysicalSourceRate row) b)
        (𝓝[>] b) (𝓝 A) := hs.mono_left hfilter
    have hbound : ∀ᶠ z in 𝓝[>] b,
        Uniform07.slopeRatioLower row/500≤ slope (negativePhysicalSourceRate row) b z := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbr)] with z hbz hzr
      change _≤(z-b)⁻¹*(negativePhysicalSourceRate row z-negativePhysicalSourceRate row b)
      rw [←div_eq_inv_mul]
      exact (le_div_iff₀ (sub_pos.mpr hbz)).mpr
        (physical_source_increment row hb ⟨hb.1.trans hbz.le,hzr.le⟩ hbz.le)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hslim hbound
  · have hbeq : b=R := le_antisymm hb.2 (le_of_not_gt hbr)
    have hlb : L< b := by simpa only [hbeq] using hLR
    have hfilter : 𝓝[<] b≤𝓝[Icc L R\{b}] b := by
      rw [nhdsWithin]
      apply le_inf nhdsWithin_le_nhds
      apply le_principal_iff.mpr
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlb)] with z hzb hlz
      exact ⟨⟨hlz.le,hzb.le.trans hb.2⟩,by simpa only [mem_singleton_iff] using hzb.ne⟩
    have hslim : Tendsto (slope (negativePhysicalSourceRate row) b)
        (𝓝[<] b) (𝓝 A) := hs.mono_left hfilter
    have hbound : ∀ᶠ z in 𝓝[<] b,
        Uniform07.slopeRatioLower row/500≤ slope (negativePhysicalSourceRate row) b z := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hlb)] with z hzb hlz
      have hh:=physical_source_increment row ⟨hlz.le,hzb.le.trans hb.2⟩ hb hzb.le
      change _≤(z-b)⁻¹*(negativePhysicalSourceRate row z-negativePhysicalSourceRate row b)
      rw [←div_eq_inv_mul]
      apply (le_div_iff_of_neg (sub_neg.mpr hzb)).mpr
      linarith
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hslim hbound

theorem finite_physical_rate_separation_from_source (row : Uniform07.Row)
    {b A a m p p' : ℝ}
    (hb : b∈Icc (Uniform07.cutoff row/2)
      (Uniform07.sourceZhi row*Uniform07.cutoff row))
    (hA : HasDerivWithinAt (negativePhysicalSourceRate row) A
      (Icc (Uniform07.cutoff row/2)
        (Uniform07.sourceZhi row*Uniform07.cutoff row)) b)
    (hm : 0< m) (hp : 0< p)
    (ha : |a/m-A|≤ 1/10000)
    (hpure : p'≤(21/10000:ℝ)*m*p) :
    (1+1/4:ℝ)*p'< a*p := by
  apply finite_physical_rate_separation row hm hp ?_ hpure
  have hlower := physical_source_slope_lower_within row hb hA
  have he := (abs_le.mp ha).1
  have hnorm : Uniform07.slopeRatioLower row/500-1/10000≤ a/m := by linarith
  exact (le_div_iff₀ hm).mp hnorm

end FCAppendix.Affine.Uniform07Finishing.Crossover
