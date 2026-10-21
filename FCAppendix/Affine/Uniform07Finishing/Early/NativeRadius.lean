import FCAppendix.Affine.Uniform07Finishing.Early.Scalar

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07

def nativeRadius (row : Row) : ℝ := cutoff row/10000

theorem nativeRadius_pos (row : Row) : 0< nativeRadius row :=
  div_pos (cutoff_pos row) (by norm_num)

theorem demandRatio_gt_one_sixtieth (row : Row) :
    (1/60:ℝ)< demandRatio row := by
  apply Box.lower_real (demandRatioBox_ok row)
  cases row <;> norm_num [demandRatioBox,earlyCutoffBox,
    Box.div,Box.inv,Box.mul,Box.scale,Box.sub,Box.add,Box.neg,Box.point]

theorem nativeRadius_lt_samplingMargin (row : Row) :
    nativeRadius row< samplingMargin row := by
  have ht := cutoff_pos row
  have hr := (demandRatio_gt_one_sixtieth row).le
  have hξ : (2/5:ℝ)≤ xi row := by
    cases row <;> norm_num [xi,xiQ,etaQ]
  have hh := mul_le_mul hξ hr (by norm_num : (0:ℝ)≤ 1/60) (xi_pos row).le
  have hht := mul_le_mul_of_nonneg_left hh ht.le
  simp only [nativeRadius,samplingMargin]
  nlinarith

theorem native_sampling_margin_guards (row : Row) :
    0< nativeRadius row ∧
    ∀Λ : ℝ,(54/100:ℝ)*cutoff row<Λ→
      max (kappa row*bidCap row) ((52/100:ℝ)*cutoff row)<Λ-nativeRadius row ∧
      ∀b : ℝ,0< b→ demandRatio row/4< clip01 ((1-Λ/b)/xi row)→
        Λ+3*nativeRadius row< b := by
  refine ⟨nativeRadius_pos row,?_⟩
  intro Λ hΛ
  have hs := (sampling_margin_guards row).2 Λ hΛ
  have ha := nativeRadius_lt_samplingMargin row
  refine ⟨by linarith [hs.1],?_⟩
  intro b hb hp
  have hh := hs.2 b hb hp
  linarith

theorem kappa_limitingFloor_add_nativeRadius_lt_root_lower (row : Row) :
    kappa row*limitingFloor row+nativeRadius row<(27/50:ℝ)*cutoff row := by
  have h := kappa_limitingFloor_add_samplingMargin_lt_root_lower row
  have ha := nativeRadius_lt_samplingMargin row
  linarith

end FCAppendix.Affine.Uniform07Finishing.Early
