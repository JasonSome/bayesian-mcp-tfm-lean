import FCAppendix.Affine.Uniform06.FixedPriceEntryIntegral
import FCAppendix.Affine.Uniform06.EntryLiteralModerate
import FCAppendix.Affine.Uniform06.EntryOptimizer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryGoodVelocity
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open LiteralExperiment EntryLiteralResponseGeometry EntryLiteralCanonicalTransfer
open EntryLiteralModerate EntryUntilting FixedPriceRawDerivative FixedPriceEntryGeometry
open EntryMomentAlgebra EntryRawSignMoments
open scoped BigOperators

variable {N C : ℕ}

lemma integral_strict_indicator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {p : Ω → ℝ} (hp : Measurable p) :
    (∫ x,deficitMoment 0 (p x) ∂μ)=μ.real {x | 0 < p x} := by
  have he : (fun x => deficitMoment 0 (p x))=({x | 0 < p x}).indicator (fun _ => (1:ℝ)) := by
    ext x
    simp [deficitMoment_zero,Set.indicator]
  rw [he,integral_indicator_const _ (measurableSet_lt measurable_const hp)]
  simp only [smul_eq_mul,mul_one]

theorem actual_velocity_bound (ν : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs ν i g N C b A U ε c q lo γ w s)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    0 ≤ FixedPriceEntryIntegral.velocity ν i C g b A U ε x ∧
      xi i*b*FixedPriceEntryIntegral.velocity ν i C g b A U ε x ≤
        deficitMoment 0 (response ν i C g b A U ε x) := by
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  by_cases hu : x∈usable ν i g b A U ε
  · have hreg := usable_regularity ν i g h x hu
    have hf : (0:Fin (N+1)) ∈ (patternTemplate C (fun j => (x.1 j).1)).support \
        sampleSet i g b x := Finset.mem_sdiff.mpr ⟨focal_mem C x.1,hreg.1⟩
    have hp := response_bounds ν i g b A U ε x (C := C)
    have hm := MaskedRootDerivative.masked_slope_bounds hξ hξ1 hb
      (patternTemplate C (fun j => (x.1 j).1)) (rowBids 0 x.1) (sampleSet i g b x) 0
    simp only [FixedPriceEntryIntegral.velocity,if_pos hu]
    refine ⟨hm.1,?_⟩
    by_cases hpos : 0 < response ν i C g b A U ε x
    · rw [deficitMoment_zero,if_pos hpos]
      have hh := mul_le_mul_of_nonneg_left hm.2 (mul_pos hξ hb).le
      convert! hh using 1; field_simp [hξ.ne',hb.ne']
    · have hz : response ν i C g b A U ε x=0 := le_antisymm (le_of_not_gt hpos) hp.1
      have hpeq : ActualRootDerivative.marginal (xi i)
          (small (patternTemplate C (fun j => (x.1 j).1)))
          (maskedBids (patternTemplate C (fun j => (x.1 j).1))
            (rowBids 0 x.1) (sampleSet i g b x)) 0 b=0 := by
        rw [← complement_eq_marginal i C x.1 _ hreg.1 b]
        simpa only [response,if_pos hu,complement] using hz
      simp only [MaskedRootDerivative.slope,if_pos hf,ActualRootDerivative.derivative,
        hpeq,lt_self_iff_false,false_and,if_false,mul_zero,deficitMoment_zero,hz,
        lt_self_iff_false,if_false,le_refl]
  · simp [FixedPriceEntryIntegral.velocity,response,hu,deficitMoment_zero]

lemma integrable_velocity (ν : Measure RowRival) [IsProbabilityMeasure ν]
    (i : Row) (g : GuardData) {b A U ε c q lo γ w s : ℝ}
    (h : Inputs ν i g N C b A U ε c q lo γ w s) :
    Integrable (FixedPriceEntryIntegral.velocity ν i C g b A U ε)
      (EntryIIDCentral.rowLaw ν N) := by
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  apply Integrable.of_mem_Icc 0 (1/(xi i*b))
    (FixedPriceEntryIntegral.measurable_velocity ν i C g b A U ε).aemeasurable
  exact ae_of_all _ fun x => by
    have hh := actual_velocity_bound ν i g h x
    refine ⟨hh.1,(le_div_iff₀ (mul_pos (xi_pos i) hb)).mpr ?_⟩
    have hI : deficitMoment 0 (response ν i C g b A U ε x) ≤ 1 := by
      simp only [deficitMoment_zero]
      split_ifs <;> norm_num
    nlinarith [hh.2.trans hI]

theorem original_derivative_and_success_bound (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0 ≤ p.2) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (hcap : ∀ᵐ p ∂G,p.2 ≤ U)
    (h : Inputs (RawMixedSource.source i G) i g N C b A U ε c q lo γ w s)
    (hinterior : b < g.multiplier+g.radius) :
    let ν := RawMixedSource.source i G
    let P := EntryIIDCentral.rowLaw ν N
    let p := response (N := N) ν i C g b A U ε
    let dq := ∫ x,FixedPriceEntryIntegral.velocity ν i C g b A U ε x ∂ P
    HasDerivAt (fun a => canonicalGoodMarginal i G C N g a A U ε) dq b ∧
      0 ≤ dq ∧ xi i*b*dq ≤ P.real {x | 0 < p x} := by
  let ν := RawMixedSource.source i G
  let P := EntryIIDCentral.rowLaw ν N
  let p := response (N := N) ν i C g b A U ε
  let v := FixedPriceEntryIntegral.velocity (N := N) ν i C g b A U ε
  have hI : Integrable (fun x => deficitMoment 0 (p x)) P :=
    Integrable.of_mem_Icc 0 1
      (measurable_deficitMoment (measurable_response ν i C g b A U ε) 0).aemeasurable
        (ae_of_all _ fun x => by
          simp only [deficitMoment_zero]
          split_ifs <;> norm_num)
  have hd := FixedPriceEntryIntegral.original_canonical_good_derivatives i G hnull hnon g hcap h hinterior
  refine ⟨hd.1,integral_nonneg (fun x => (actual_velocity_bound ν i g h x).1),?_⟩
  have hi := integral_mono ((integrable_velocity ν i g h).const_mul (xi i*b)) hI
    (fun x => (actual_velocity_bound ν i g h x).2)
  rw [integral_const_mul,integral_strict_indicator P (measurable_response ν i C g b A U ε)] at hi
  exact hi

section ConditionalCauchy
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem conditional_cauchy (p : Ω → ℝ) (hp : Measurable p)
    (hpb : ∀ x,p x∈Icc (0:ℝ) 1)
    (hP : 0 < μ.real {x | 0 < p x}) :
    (∫ x,p x ∂μ)^2 ≤ μ.real {x | 0 < p x}*(∫ x,(p x)^2 ∂μ) := by
  let I := fun x => deficitMoment 0 (p x)
  let P := μ.real {x | 0 < p x}
  let Q := ∫ x,p x ∂μ
  let a := Q/P
  have hpi : Integrable p μ := Integrable.of_mem_Icc 0 1 hp.aemeasurable (ae_of_all _ hpb)
  have hpi2 : Integrable (fun x => (p x)^2) μ :=
    Integrable.of_mem_Icc 0 1 (hp.pow_const 2).aemeasurable (ae_of_all _ fun x =>
      ⟨sq_nonneg _,by nlinarith [(hpb x).1,(hpb x).2]⟩)
  have hIi : Integrable I μ := Integrable.of_mem_Icc 0 1
    (measurable_deficitMoment hp 0).aemeasurable (ae_of_all _ fun x => by
      dsimp [I]
      simp only [deficitMoment_zero]
      split_ifs <;> norm_num)
  have hsq (x) : (p x-a*I x)^2=(p x)^2-2*a*p x+a^2*I x := by
    by_cases hx : 0 < p x
    · simp only [I,deficitMoment_zero,if_pos hx]
      ring
    · have hz : p x=0 := le_antisymm (le_of_not_gt hx) (hpb x).1
      simp [I,hz,deficitMoment_zero]
  have hn : (0:ℝ) ≤ ∫ x,(p x-a*I x)^2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (p x-a*I x))
  simp_rw [hsq] at hn
  have hsubI : Integrable (fun x => (p x)^2-2*a*p x) μ :=
    hpi2.sub (hpi.const_mul (2*a))
  rw [integral_add hsubI (hIi.const_mul (a^2)),
    integral_sub hpi2 (hpi.const_mul (2*a)),integral_const_mul,integral_const_mul,
    integral_strict_indicator μ hp] at hn
  change 0 ≤ (∫ x,(p x)^2 ∂μ)-2*a*Q+a^2*P at hn
  have hPP : 0 < P := hP
  have hscaled := mul_nonneg hPP.le hn
  dsimp [a] at hscaled
  field_simp [hPP.ne'] at hscaled
  change Q^2 ≤ P*(∫ x,(p x)^2 ∂μ)
  nlinarith only [hscaled,hPP]

end ConditionalCauchy

theorem actual_gap_from_conditional_moments
    {ξ η b P Q R dq δ : ℝ} (hξ : 0 < ξ) (hη : 0 ≤ η)
    (hP : 0 < P) (hR : 0 < R) (hδ : 0 ≤ δ)
    (hderiv : ξ*b*dq ≤ P) (hcauchy : Q^2 ≤ P*R)
    (hratio : η/ξ+Q/P+δ ≤ Q^2/(P*R)) :
    δ*Q^2 ≤ routeGap η b Q dq R := by
  have hDR : η*b*dq ≤ (η/ξ)*P := by
    have ht := mul_le_mul_of_nonneg_left hderiv (div_nonneg hη hξ.le)
    convert! ht using 1; field_simp [hξ.ne']
  have hmain := (le_div_iff₀ (mul_pos hP hR)).mp hratio
  have hfrac : (Q/P)*(P*R)=Q*R := by field_simp [hP.ne']
  have hgap : δ*(P*R) ≤ routeGap η b Q dq R := by
    have hh := mul_le_mul_of_nonneg_right hDR hR.le
    unfold routeGap
    nlinarith [hfrac]
  exact (mul_le_mul_of_nonneg_left hcauchy hδ).trans hgap

end FCAppendix.Affine.Uniform06.EntryGoodVelocity
