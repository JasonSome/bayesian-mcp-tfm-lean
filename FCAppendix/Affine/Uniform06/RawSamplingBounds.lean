import FCAppendix.Affine.Uniform06.SamplingPopulation
import FCAppendix.Affine.Uniform06.SampledSafeLimit

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawSamplingBounds

open Set MeasureTheory Filter
open scoped Topology BigOperators
open LowBody Uniform07 RawMixedSource RawTiltedSource RawMarkedLaplace
open FCAppendix.Affine.ClippedResidual
open LiteralExperiment SamplingPopulation

lemma rawH_abs_le (i : Row) {b : ℝ} (hb : 0 < b) (r : RowRival) :
    |rawH (xi i) b r| ≤ 1 := by
  have hh := demand_bounds (xi_pos i) hb r
  unfold rawH
  rw [abs_le]
  constructor <;> linarith [hh.1,hh.2]

theorem original_receipt_h_bounds (i : Row) (G : Measure (ℝ × ℝ))
    {U b ε : ℝ} (hU : 0 < U) (hb : 0 < b) (hbU : b ≤ U) (hε : 0 < ε)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) (hreceipt : (1-xi i/2)*U+ε ≤ b)
    (θ : ℝ) (g : GuardData) :
    ∀ᵐ r ∂tiltedSource i G b θ,
      0 ≤ rawH (xi i) b r ∧
      (0 < rawWeight (xi i) g r → ε/(xi i*U) ≤ rawH (xi i) b r) := by
  have hraw : ∀ᵐ r ∂tiltedSource i G b θ,r.1=0 → r.2 ≤ U :=
    (tilted_absolutelyContinuous _ _).ae_le (SourceCoarseIntegral.original_retained_bid_cap i G hcap)
  have hno := TiltedGood.tilted_no_active_tag i G b θ
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  filter_upwards [hraw,hno] with r hr hn
  by_cases ht : r.1=0
  · have hh := FiniteGuards.sampled_h_gap (xi_pos i) hξ1 hU hb (hr ht) hbU hε hreceipt
    have he : rawH (xi i) b r=1/2-exposure (xi i) b r.2 := by
      simp only [rawH,RawMixedSource.demand,if_pos ht]
    rw [he]
    exact ⟨(div_pos hε (mul_pos (xi_pos i) hU)).le.trans hh,fun _ => hh⟩
  · have he : rawH (xi i) b r=0 := by
      simp only [rawH,RawMixedSource.demand,if_neg ht,if_neg hn]
      norm_num
    have hw : rawWeight (xi i) g r=0 := by simp only [rawWeight,if_neg ht]
    simp only [he,hw,lt_self_iff_false,false_implies,le_refl,and_self]

theorem original_sampling_ratio_bounds (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {U b ε θ lo : ℝ}
    (hU : 0 < U) (hb : 0 < b) (hbU : b ≤ U) (hε : 0 < ε)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) (hreceipt : (1-xi i/2)*U+ε ≤ b)
    (hlo : 0 < lo) (hθ : lo ≤ θ) (g : GuardData)
    (hw : 0 < weightMean i G b θ g) :
    0 < selectedMean i G b θ g/weightMean i G b θ g ∧
      selectedMean i G b θ g/weightMean i G b θ g ≤
        Real.exp (-lo*(ε/(xi i*U))) ∧
      Real.exp (-lo*(ε/(xi i*U))) < 1 := by
  letI := tiltedSource_probability i G hb θ
  have hp := original_receipt_h_bounds i G hU hb hbU hε hcap hreceipt θ g
  have hη : 0 < ε/(xi i*U) := div_pos hε (mul_pos (xi_pos i) hU)
  have hh := weighted_laplace_ratio (tiltedSource i G b θ)
    (rawWeight (xi i) g) (rawH (xi i) b)
    (measurable_rawWeight (xi i) g) (measurable_rawH (xi i) b)
    (ae_of_all _ (rawWeight_bounds (xi i) g)) (ae_of_all _ (rawH_abs_le i hb))
    (hlo.trans_le hθ) hη
    (hp.mono fun r hr hne => hr.2
      (lt_of_le_of_ne (rawWeight_bounds (xi i) g r).1 (Ne.symm hne))) hw
  refine ⟨hh.1,hh.2.1.trans ?_,?_⟩
  · apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hθ hη.le]
  · exact Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hlo hη])

end FCAppendix.Affine.Uniform06.RawSamplingBounds
