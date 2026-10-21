import FCAppendix.Affine.Uniform07Finishing.Native.UniformUpperLimits
import FCAppendix.Affine.Uniform07Finishing.Native.NativeConditional

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Set Filter Topology

def sourceLowerRootBound (row : Uniform07.Row) : ℝ :=
  (27/50:ℝ)*Uniform07.cutoff row-Early.nativeRadius row

def sourceLowerPriceCeiling (row : Uniform07.Row) : ℝ :=
  (Uniform07.limitingFloor row+sourceLowerRootBound row/Uniform07.kappa row)/2

def sourceLowerMarginalCap (row : Uniform07.Row) : ℝ :=
  max 0 ((1-sourceLowerRootBound row/sourceLowerPriceCeiling row)/Uniform07.xi row)

def sourceLowerSuccessCap (row : Uniform07.Row) : ℝ :=
  1-(1-sourceLowerMarginalCap row)^2/2

theorem source_limiting_floor_positive (row : Uniform07.Row) :
    0< Uniform07.limitingFloor row :=
  (Early.upper_floor_interface row).2.1.trans (Early.upper_floor_interface row).2.2.1

theorem source_root_bound_above_floor_receipt (row : Uniform07.Row) :
    Uniform07.kappa row*Uniform07.limitingFloor row< sourceLowerRootBound row := by
  have h:=Early.kappa_limitingFloor_add_nativeRadius_lt_root_lower row
  dsimp only [sourceLowerRootBound]
  linarith

theorem sourceLowerRootBound_pos (row : Uniform07.Row) :
    0< sourceLowerRootBound row :=
  (mul_pos (source_kappa_pos row) (source_limiting_floor_positive row)).trans
    (source_root_bound_above_floor_receipt row)

theorem sourceLowerPriceCeiling_above_limit (row : Uniform07.Row) :
    Uniform07.limitingFloor row< sourceLowerPriceCeiling row := by
  have h : Uniform07.limitingFloor row< sourceLowerRootBound row/Uniform07.kappa row :=
    (lt_div_iff₀ (source_kappa_pos row)).mpr (by
      simpa only [mul_comm] using source_root_bound_above_floor_receipt row)
  dsimp only [sourceLowerPriceCeiling]
  linarith

theorem sourceLowerPriceCeiling_pos (row : Uniform07.Row) :
    0< sourceLowerPriceCeiling row :=
  (source_limiting_floor_positive row).trans (sourceLowerPriceCeiling_above_limit row)

theorem sourceLowerPriceCeiling_root_guard (row : Uniform07.Row) :
    Uniform07.kappa row*sourceLowerPriceCeiling row< sourceLowerRootBound row := by
  have hk := source_kappa_pos row
  have hq : Uniform07.kappa row*(sourceLowerRootBound row/Uniform07.kappa row)=
      sourceLowerRootBound row := mul_div_cancel₀ _ hk.ne'
  have h := source_root_bound_above_floor_receipt row
  dsimp only [sourceLowerPriceCeiling]
  nlinarith

theorem sourceLowerMarginalCap_bounds (row : Uniform07.Row) :
    0≤ sourceLowerMarginalCap row ∧ sourceLowerMarginalCap row<1 := by
  have hξ := Uniform07.xi_pos row
  have hR := sourceLowerPriceCeiling_pos row
  have hguard := sourceLowerPriceCeiling_root_guard row
  have he := source_kappa_add_xi row
  have hq : Uniform07.kappa row< sourceLowerRootBound row/sourceLowerPriceCeiling row :=
    (lt_div_iff₀ hR).mpr hguard
  have hr : (1-sourceLowerRootBound row/sourceLowerPriceCeiling row)/Uniform07.xi row<1 :=
    (div_lt_one hξ).mpr (by linarith)
  exact ⟨le_max_left _ _,max_lt (by norm_num) hr⟩

theorem sourceLowerSuccessCap_lt_one (row : Uniform07.Row) :
    sourceLowerSuccessCap row<1 := by
  have h:=sq_pos_of_pos (sub_pos.mpr (sourceLowerMarginalCap_bounds row).2)
  dsimp only [sourceLowerSuccessCap]
  linarith

theorem sourceLowerSuccessCap_nonneg (row : Uniform07.Row) :
    0≤ sourceLowerSuccessCap row := by
  have hp:=sourceLowerMarginalCap_bounds row
  have hh:=mul_nonneg hp.1 (sub_nonneg.mpr hp.2.le)
  dsimp only [sourceLowerSuccessCap]
  nlinarith [sq_nonneg (sourceLowerMarginalCap row)]

theorem source_clipped_exposure_le_cap (row : Uniform07.Row) {z b : ℝ}
    (hz : sourceLowerRootBound row≤ z) (hb : b≤ sourceLowerPriceCeiling row) :
    ClippedResidual.exposure (Uniform07.xi row) z b≤ sourceLowerMarginalCap row := by
  have hlo:=sourceLowerRootBound_pos row
  have hz0:=hlo.trans_le hz
  have hξ:=Uniform07.xi_pos row
  have hR:=sourceLowerPriceCeiling_pos row
  by_cases hzb:b≤ z
  · rw [ClippedResidual.exposure_zero hzb]
    exact (sourceLowerMarginalCap_bounds row).1
  · have hzb':z< b:=lt_of_not_ge hzb
    have hb0:=hz0.trans hzb'
    have hguard : (1-Uniform07.xi row)*b≤ z := by
      have hk:1-Uniform07.xi row=Uniform07.kappa row := by
        linarith [source_kappa_add_xi row]
      rw [hk]
      exact ((mul_le_mul_of_nonneg_left hb (source_kappa_pos row).le).trans
        (sourceLowerPriceCeiling_root_guard row).le).trans hz
    rw [ClippedResidual.exposure_of_between hξ hz0 hzb' hguard]
    apply le_trans _ (le_max_right _ _)
    apply div_le_div_of_nonneg_right _ hξ.le
    apply sub_le_sub_left
    apply (div_le_div_iff₀ hR hb0).mpr
    calc
      sourceLowerRootBound row*b≤ sourceLowerRootBound row*sourceLowerPriceCeiling row :=
        mul_le_mul_of_nonneg_left hb hlo.le
      _≤ z*sourceLowerPriceCeiling row := mul_le_mul_of_nonneg_right hz hR.le

theorem source_guarded_exposure_le_cap (row : Uniform07.Row) {Λ z b : ℝ}
    (hΛ : (27/50:ℝ)*Uniform07.cutoff row<Λ)
    (hz : Λ-Early.nativeRadius row≤ z)
    (hb : b≤ sourceLowerPriceCeiling row) :
    ClippedResidual.exposure (Uniform07.xi row) z b≤ sourceLowerMarginalCap row := by
  apply source_clipped_exposure_le_cap row _ hb
  exact (sub_le_sub_right hΛ.le (Early.nativeRadius row)).trans hz

theorem source_eventual_success_constants (row : Uniform07.Row) (u : ℕ→ℝ)
    (hU : Tendsto u atTop
      (𝓝 ((Uniform07.cutoff row-Uniform07.entry row)^2/Uniform07.cutoff row))) :
    ∀ᶠ m in atTop,
      endogenousUpperFloor row u m< sourceLowerPriceCeiling row ∧
      sourceLowerSuccessCap row< source_upper_rank row m (Uniform07.cutoff row) := by
  filter_upwards [
    (source_endogenous_floor_tendsto row u hU).eventually
      (eventually_lt_nhds (sourceLowerPriceCeiling_above_limit row)),
    (source_upper_rank_tendsto_one row).eventually
      (eventually_gt_nhds (sourceLowerSuccessCap_lt_one row))] with m hR hq
  exact ⟨hR,hq⟩

end FCAppendix.Affine.Uniform07Finishing
