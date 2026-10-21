import FCAppendix.Affine.Uniform06.FullFamilyConvergence
import FCAppendix.Affine.Uniform07.SourceLaw

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FullSourceSpecialization
open MeasureTheory Set Filter Topology
open Uniform07 FullJointLaw
open FCAppendix.Affine.ClippedResidual

theorem uniform_scale (i : Row) :
    uniformLaw.map (fun y : ℝ => cutoff i*y)=LowChernoff.conditionalValueLaw i := by
  apply Measure.ext
  intro S hS
  have ht := cutoff_pos i
  have hpre : (fun y : ℝ => cutoff i*y) ⁻¹' S ∩ Icc (0:ℝ) 1=
      (fun y : ℝ => cutoff i*y) ⁻¹' (S ∩ Icc (0:ℝ) (cutoff i)) := by
    ext y
    simp only [mem_inter_iff,mem_preimage,mem_Icc]
    constructor
    · rintro ⟨hy,hy0,hy1⟩
      exact ⟨hy,mul_nonneg ht.le hy0,by nlinarith⟩
    · rintro ⟨hy,hy0,hy1⟩
      exact ⟨hy,(mul_nonneg_iff_of_pos_left ht).mp hy0,by nlinarith⟩
  rw [Measure.map_apply (by fun_prop) hS,uniformLaw,Measure.restrict_apply
    (hS.preimage (by fun_prop)),hpre,Real.volume_preimage_mul_left ht.ne',
    abs_of_pos (inv_pos.mpr ht),LowChernoff.conditionalValueLaw,Measure.smul_apply,
    smul_eq_mul,Measure.restrict_apply hS]
  simp only [one_div]

theorem measurable_normalizedBid (i : Row) : Measurable (normalizedBid i) := by
  unfold normalizedBid
  exact Measurable.ite measurableSet_Iic measurable_id (by fun_prop)

theorem full_joint_uniform_graph (i : Row) :
    (law i:Measure (ℝ × ℝ))=uniformLaw.map
      (fun y => (cutoff i*y,cutoff i*normalizedBid i y)) := by
  change (LowChernoff.conditionalValueLaw i).map (fun v => (v,FullJointLaw.bid i v))=_
  rw [← uniform_scale i,Measure.map_map (show Measurable (fun v : ℝ => (v,FullJointLaw.bid i v)) from
    measurable_id.prodMk (measurable_bid i)) (show Measurable (fun y : ℝ => cutoff i*y) by fun_prop)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy
  exact Prod.ext rfl (bid_scaled i hy)

theorem exposure_normalized_bid (i : Row) {z y : ℝ}
    (hz : z ∈ Icc (1/2:ℝ) (x i)) (hy : y ∈ Icc (0:ℝ) 1) :
    exposure (xi i) z (normalizedBid i y)=normalizedAcceptance i z y := by
  by_cases hyz : y ≤ z
  · have hyx : y ≤ x i := hyz.trans hz.2
    rw [normalizedBid,if_pos hyx,exposure_zero hyz,normalizedAcceptance,if_pos hyz]
  · have hzy := lt_of_not_ge hyz
    have hy0 : 0 < y := (by linarith [hz.1] : 0 < z).trans hzy
    by_cases hyx : y ≤ x i
    · rw [normalizedBid,if_pos hyx,normalizedAcceptance,if_neg hyz,if_pos hyx]
      have hratio : (y-z)/(xi i*y)=pieceP (1/xi i) (z/xi i) y := by
        unfold pieceP
        field_simp [(xi_pos i).ne',hy0.ne']
      unfold exposure
      rw [max_eq_left hzy.le,max_eq_right (sub_nonneg.mpr hzy.le),hratio,
        min_eq_right (low_piece_bounds i hz.1 hzy.le hyx).2]
    · rw [normalizedBid,if_neg hyx,normalizedAcceptance,if_neg hyz,if_neg hyx]
      exact ActiveGraphComponent.exposure_active_normalized i hz ⟨(lt_of_not_ge hyx).le,hy.2⟩

theorem full_lower_exposure_law (i : Row) {z : ℝ}
    (hz : z ∈ Icc (1/2:ℝ) (x i)) :
    MixedLaw.physicalLowerLaw i (z*cutoff i) (law i:Measure (ℝ × ℝ))=lowerSourceLaw i z := by
  have hz0 : 0 < z := by linarith [hz.1]
  have hb : 0 < z*cutoff i := mul_pos hz0 (cutoff_pos i)
  have hg : Measurable (fun y : ℝ => (cutoff i*y,cutoff i*normalizedBid i y)) :=
    (measurable_const.mul measurable_id).prodMk
      (measurable_const.mul (measurable_normalizedBid i))
  have hf : Measurable (fun p : ℝ × ℝ => exposure (xi i) (z*cutoff i) p.2) :=
    (continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd
  rw [MixedLaw.physicalLowerLaw,full_joint_uniform_graph,Measure.map_map hf hg]
  change uniformLaw.map (fun y => exposure (xi i) (z*cutoff i)
    (cutoff i*normalizedBid i y))=uniformLaw.map (normalizedAcceptance i z)
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with y hy
  rw [mul_comm z (cutoff i),LowChernoff.exposure_positive_scaling (xi_pos i) hz0 (cutoff_pos i)]
  exact exposure_normalized_bid i hz hy

theorem upper_demand_marginal : MixedLaw.upperSignLaw.map Prod.fst=Measure.dirac (1/2:ℝ) := by
  rw [MixedLaw.upperSignLaw,Measure.map_add _ _ measurable_fst,Measure.map_smul,Measure.map_smul,
    Measure.map_dirac' measurable_fst,Measure.map_dirac' measurable_fst,← add_smul]
  rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)]
  norm_num

theorem mixed_demand_marginal (i : Row) (ν : Measure ℝ) :
    (MixedLaw.law i ν).map Prod.fst=
      ENNReal.ofReal (1-cutoff i) • Measure.dirac (1/2:ℝ)+ENNReal.ofReal (cutoff i) • ν := by
  rw [MixedLaw.law,Measure.map_add _ _ measurable_fst,Measure.map_smul,Measure.map_smul,upper_demand_marginal,
    MixedLaw.lowerLift,Measure.map_map (g := fun p : ℝ × ℝ => p.1)
      (f := fun x : ℝ => (x,(0:ℝ))) measurable_fst (measurable_id.prodMk measurable_const)]
  simp only [Function.comp_def,Measure.map_id']

theorem full_mixed_demand_law (i : Row) {z : ℝ}
    (hz : z ∈ Icc (1/2:ℝ) (x i)) :
    (MixedLaw.law i (MixedLaw.physicalLowerLaw i (z*cutoff i)
      (law i:Measure (ℝ × ℝ)))).map Prod.fst=sourceLaw i z := by
  rw [full_lower_exposure_law i hz,mixed_demand_marginal]
  rfl

end FCAppendix.Affine.Uniform06.FullSourceSpecialization
