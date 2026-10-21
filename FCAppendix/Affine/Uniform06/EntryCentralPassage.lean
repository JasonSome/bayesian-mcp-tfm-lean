import FCAppendix.Affine.Uniform06.EntryCentral
import FCAppendix.Affine.Uniform06.EntryProfileMean
import FCAppendix.Probability.WeakMomentConvergence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryCentralPassage
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Probability
open FCAppendix.Affine.Uniform06
open scoped BigOperators

section General
variable {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
  (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]

lemma integral_abs_le_sqrt_sq {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] {e : Ξ → ℝ} (he : MemLp e 2 P) :
    (∫ ω, |e ω| ∂P) ≤ Real.sqrt (∫ ω, (e ω)^2 ∂P) := by
  have hv := variance_nonneg |e| P
  rw [variance_eq_sub he.abs] at hv
  simp only [Pi.pow_apply,Pi.abs_apply,sq_abs] at hv
  exact (Real.le_sqrt (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => sq_nonneg _)).mpr (by linarith)

lemma L1_tendsto_of_L2 (e : (m : ℕ) → Ω m → ℝ)
    (he : ∀ m, MemLp (e m) 2 (μ m))
    (hL2 : Tendsto (fun m => ∫ ω, (e m ω)^2 ∂μ m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, |e m ω| ∂μ m) atTop (𝓝 0) := by
  exact squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (fun m => integral_abs_le_sqrt_sq (μ m) (he m)) (by simpa using hL2.sqrt)

theorem strict_cdf_tendsto_of_L2
    (F T : (m : ℕ) → Ω m → ℝ) (G : ℝ → ℝ) (hG : Continuous G)
    (hF : ∀ s : ℝ, Tendsto (fun m => (μ m).real {ω | F m ω ≤ s}) atTop (𝓝 (G s)))
    (hint : ∀ m, Integrable (fun ω => (F m ω-T m ω)^2) (μ m))
    (hL2 : Tendsto (fun m => ∫ ω, (F m ω-T m ω)^2 ∂μ m) atTop (𝓝 0))
    (z : ℕ → ℝ) {z0 : ℝ} (hz : Tendsto z atTop (𝓝 z0)) :
    Tendsto (fun m => (μ m).real {ω | T m ω < z m}) atTop (𝓝 (G z0)) := by
  apply moving_threshold_tendsto_of_monotone
    (fun m s => (μ m).real {ω | T m ω < s}) G
    (fun m a b hab => measureReal_mono (fun _ h => h.trans_le hab)) hG ?_ z hz
  intro s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r,hr,hcont⟩ := Metric.continuousAt_iff.mp hG.continuousAt (ε/4) (by positivity)
  let δ := r/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlo : |G (s-2*δ)-G s| < ε/4 := by
    apply (show dist (G (s-2*δ)) (G s) < ε/4 from hcont ?_)
    rw [Real.dist_eq]
    have he : s-2*δ-s=-(2*δ) := by ring
    rw [he,abs_neg,abs_of_pos (by positivity : 0 < 2*δ)]
    dsimp [δ]
    linarith
  have hhi : |G (s+δ)-G s| < ε/4 := by
    apply (show dist (G (s+δ)) (G s) < ε/4 from hcont ?_)
    rw [Real.dist_eq,add_sub_cancel_left,abs_of_pos hδ]
    dsimp [δ]
    linarith
  have heL := (hL2.div_const (δ^2)).eventually_lt_const (show (0:ℝ)/(δ^2)<ε/4 by simpa only [zero_div] using div_pos hε (by norm_num : (0:ℝ)<4))
  have hfL := (Metric.tendsto_nhds.mp (hF (s-2*δ))) (ε/4) (by positivity)
  have hfU := (Metric.tendsto_nhds.mp (hF (s+δ))) (ε/4) (by positivity)
  filter_upwards [heL,hfL,hfU] with m hm hmL hmU
  have hlow := EntryCentral.cdf_lower_of_L2 (μ m) (F m) (T m) (s-δ) δ hδ (hint m)
  have hlow' : (μ m).real {ω | F m ω ≤ s-2*δ}-
      (∫ ω, (F m ω-T m ω)^2 ∂μ m)/δ^2 ≤ (μ m).real {ω | T m ω < s} := by
    have he : s-δ-δ=s-2*δ := by ring
    rw [he] at hlow
    exact hlow.trans (measureReal_mono (fun x (h : T m x ≤ s-δ) => show T m x < s by linarith))
  have hupp := (measureReal_mono (μ := μ m) (show {ω | T m ω< s} ⊆ {ω | T m ω≤ s} from fun x (h : T m x < s) => show T m x ≤ s from h.le)).trans
    (EntryCentral.cdf_upper_of_L2 (μ m) (F m) (T m) s δ hδ (hint m))
  rw [Real.dist_eq] at hmL hmU ⊢
  have hhL := abs_lt.mp hmL
  have hhU := abs_lt.mp hmU
  have hgL := abs_lt.mp hlo
  have hgU := abs_lt.mp hhi
  apply abs_lt.mpr
  constructor <;> linarith

theorem weak_prod_fst {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (F : (m : ℕ) → Ω m → ℝ) (Z : Ξ → ℝ)
    (hFm : ∀ m, Measurable (F m))
    (hF : TendstoInDistribution F atTop Z μ ν) :
    TendstoInDistribution (fun m (x : Ω m × unitInterval) => F m x.1)
      atTop Z (fun m => (μ m).prod volume) ν := by
  refine ⟨fun m => ((hFm m).comp measurable_fst).aemeasurable,hF.aemeasurable_limit,?_⟩
  convert! hF.tendsto using 1
  ext m : 1
  apply ProbabilityMeasure.toMeasure_injective
  change ((μ m).prod (volume : Measure unitInterval)).map (fun x => F m x.1)=(μ m).map (F m)
  change ((μ m).prod (volume : Measure unitInterval)).map (F m ∘ Prod.fst)=(μ m).map (F m)
  rw [← Measure.map_map (hFm m) measurable_fst,
    (measurePreserving_fst (μ := μ m) (ν := (volume : Measure unitInterval))).map_eq]

lemma square_le_one_add_fourth (x : ℝ) : x^2 ≤ 1+x^4 := by
  nlinarith [sq_nonneg (x^2-1)]

lemma gaussian_shortfall_power_memLp (a b z : ℝ) (j : ℕ) :
    MemLp (fun x => (EntryCentralRatio.positiveShortfall z x)^j) 2 (EntryGaussianLaw.law a b) := by
  have h := EntryCentralRatio.positiveShortfall_memLp a b z ((2*j:ℕ):NNReal)
  apply (memLp_two_iff_integrable_sq ((EntryCentralRatio.measurable_positiveShortfall z).pow_const j).aestronglyMeasurable).mpr
  have he (x : ℝ) : ‖EntryCentralRatio.positiveShortfall z x‖^(2*j)=
      ((EntryCentralRatio.positiveShortfall z x)^j)^2 := by
    rw [Real.norm_eq_abs,pow_mul,sq_abs,← pow_mul,Nat.mul_comm 2 j,pow_mul]
  simpa only [he] using h.integrable_norm_pow'

theorem moments_of_actual_scalar_rows
    {a b : ℝ} (ha : 0 < a) (_hb : 0 ≤ b)
    (T : (m : ℕ) → Ω m → ℝ) (hT : ∀ m, Measurable (T m))
    (hweak : TendstoInDistribution T atTop id μ (EntryGaussianLaw.law a b))
    (hprob : ∀ z : ℝ, Tendsto (fun m => (μ m).real {ω | T m ω< z}) atTop
      (𝓝 (cdf (EntryGaussianLaw.law a b) z)))
    (N : ℕ → ℕ) (hN : ∀ m, 0 < N m)
    (X : (m : ℕ) → Fin (N m) → Ω m → ℝ)
    (hmX : ∀ m i, Measurable (X m i))
    (hbX : ∀ m i, ∀ᵐ ω ∂μ m, |X m i ω| ≤ 1)
    (hzX : ∀ m i, ∫ ω, X m i ω ∂μ m=0)
    (hiX : ∀ m, iIndepFun (X m) (μ m))
    (S : (m : ℕ) → Ω m → ℝ) (hSm : ∀ m, Measurable (S m))
    (hS : ∀ m, ∀ᵐ ω ∂μ m, 0 ≤ S m ω)
    (hdecomp : ∀ m ω, T m ω=EntryUI.normalizedSum (X m) ω+S m ω)
    (z : ℕ → ℝ) {z0 : ℝ} (hz : Tendsto z atTop (𝓝 z0)) :
    Tendsto (fun m => (μ m).real {ω | T m ω< z m}) atTop
      (𝓝 (EntryCentralRatio.success a b z0)) ∧
    Tendsto (fun m => ∫ ω, max (z m-T m ω) 0 ∂μ m) atTop
      (𝓝 (EntryCentralRatio.firstMoment a b z0)) ∧
    Tendsto (fun m => ∫ ω, (max (z m-T m ω) 0)^2 ∂μ m) atTop
      (𝓝 (EntryCentralRatio.secondMoment a b z0)) := by
  have hcont : Continuous (cdf (EntryGaussianLaw.law a b)) :=
    continuous_iff_continuousAt.mpr fun s => (EntryConvolution.hasDerivAt_actual_cdf ha b s).continuousAt
  have hP := moving_threshold_tendsto_of_monotone
    (fun m s => (μ m).real {ω | T m ω< s}) _
    (fun m x y hxy => measureReal_mono (fun _ h => h.trans_le hxy)) hcont hprob z hz
  let Q := fun m ω => max (z m-T m ω) 0
  have hQweak : TendstoInDistribution Q atTop (EntryCentralRatio.positiveShortfall z0) μ
      (EntryGaussianLaw.law a b) := by
    simpa only [one_mul,Q,EntryCentralRatio.positiveShortfall,id_eq] using!
      tendstoInDistribution_positivePart_moving μ (EntryGaussianLaw.law a b) T id hT hweak z hz 1
  have hfour m : Integrable (fun ω => (Q m ω)^4) (μ m) ∧
      (∫ ω, (Q m ω)^4 ∂μ m) ≤ 8*(z m)^4+16*FCAppendix.Probability.gaussianMomentConstant 4 2 := by
    simpa only [Q,hdecomp,sub_add_eq_sub_sub] using
      EntryUI.actual_normalized_deficit_fourth_bound (μ m) (hN m) (X m) (hmX m)
        (hbX m) (hzX m) (hiX m) (S m) (hSm m) (hS m) (z m)
  have hQm m : Measurable (Q m) := (measurable_const.sub (hT m)).max measurable_const
  have hLp2 m : MemLp (fun ω => (Q m ω)^2) 2 (μ m) := by
    apply (memLp_two_iff_integrable_sq ((hQm m).pow_const 2).aestronglyMeasurable).mpr
    simpa only [← pow_mul] using (hfour m).1
  have hLp1 m : MemLp (Q m) 2 (μ m) := by
    apply (memLp_two_iff_integrable_sq (hQm m).aestronglyMeasurable).mpr
    apply Integrable.mono' ((integrable_const (1:ℝ)).add (hfour m).1)
      ((hQm m).pow_const 2).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact square_le_one_add_fourth (Q m ω)
  let K := 8*(|z0|+1)^4+16*FCAppendix.Probability.gaussianMomentConstant 4 2
  have hK4 : ∀ᶠ m in atTop, (∫ ω, (Q m ω)^4 ∂μ m) ≤ K := by
    filter_upwards [hz.abs.eventually_lt_const (show |z0| < |z0|+1 by linarith)] with m hm
    apply (hfour m).2.trans
    have hp := pow_le_pow_left₀ (abs_nonneg (z m)) hm.le 4
    have he : |z m|^4=(z m)^4 := by rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
    rw [he] at hp
    dsimp [K]
    nlinarith
  have hK2 : ∀ᶠ m in atTop, (∫ ω, (Q m ω)^2 ∂μ m) ≤ 1+K := by
    filter_upwards [hK4] with m hm
    have hh := integral_mono (hLp1 m).integrable_sq
      ((integrable_const (1:ℝ)).add (hfour m).1) (fun ω => square_le_one_add_fourth (Q m ω))
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const _) (hfour m).1,integral_const,probReal_univ,one_smul] at hh
    linarith
  refine ⟨hP,?_,?_⟩
  · exact integral_tendsto_of_tendstoInDistribution μ (EntryGaussianLaw.law a b)
      Q (EntryCentralRatio.positiveShortfall z0) hQweak hLp1
      (EntryCentralRatio.positiveShortfall_memLp a b z0 2) (1+K) hK2
  · exact moment_tendsto_of_tendstoInDistribution μ (EntryGaussianLaw.law a b)
      Q (EntryCentralRatio.positiveShortfall z0) hQweak 2 hLp2
      (gaussian_shortfall_power_memLp a b z0 2) K (by simpa only [show (2:ℕ)*2=4 by norm_num] using hK4)

theorem central_ratio_of_moments
    (P A B : ℕ → ℝ) {a b z : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hP : Tendsto P atTop (𝓝 (EntryCentralRatio.success a b z)))
    (hA : Tendsto A atTop (𝓝 (EntryCentralRatio.firstMoment a b z)))
    (hB : Tendsto B atTop (𝓝 (EntryCentralRatio.secondMoment a b z))) :
    (∀ᶠ m in atTop, 0 < P m ∧ 0 < A m ∧ 0 < B m) ∧
    Tendsto (fun m => (A m)^2/(P m*B m)) atTop
      (𝓝 ((EntryCentralRatio.firstMoment a b z)^2/
        (EntryCentralRatio.success a b z*EntryCentralRatio.secondMoment a b z))) ∧
    (1/2 : ℝ) ≤ (EntryCentralRatio.firstMoment a b z)^2/
      (EntryCentralRatio.success a b z*EntryCentralRatio.secondMoment a b z) := by
  have hp := EntryCentralRatio.success_pos ha b z
  have hab := EntryCentralRatio.first_second_moment_pos ha b z
  refine ⟨?_,?_,EntryCentralRatio.actual_central_ratio_ge_half ha hb z⟩
  · exact (hP.eventually_const_lt hp).and
      ((hA.eventually_const_lt hab.1).and (hB.eventually_const_lt hab.2))
  · exact (hA.pow 2).div (hP.mul hB) (mul_pos hp hab.2).ne'

end General
end FCAppendix.Affine.Uniform06.EntryCentralPassage
