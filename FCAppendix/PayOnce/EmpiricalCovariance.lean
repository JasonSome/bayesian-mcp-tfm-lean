import FCAppendix.PayOnce.CovarianceTransport
import FCAppendix.Probability.EmpiricalMean

namespace FCAppendix.PayOnce
open MeasureTheory Set Filter Topology

theorem integral_covariance_error_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C : Ω → ℝ) (a : ℝ)
    (hA : Integrable A μ) (hB : Measurable B) (hBb : ∀ ω, B ω ∈ Icc (0 : ℝ) 1)
    (hC : Integrable C μ) :
    |(∫ ω, C ω-A ω*B ω ∂μ)-((∫ ω, C ω ∂μ)-a*(∫ ω, B ω ∂μ))| ≤
      ∫ ω, |A ω-a| ∂μ := by
  have hBI := UnitInterval.integrable μ B hB (fun ω => (hBb ω).1) (fun ω => (hBb ω).2)
  have hBn : ∀ᵐ ω ∂μ, ‖B ω‖ ≤ (1 : ℝ) := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hBb ω).1]
    exact (hBb ω).2
  have hAB := hA.mul_bdd hB.aestronglyMeasurable hBn
  have hE := (hA.sub (integrable_const a)).mul_bdd hB.aestronglyMeasurable hBn
  have he : (∫ ω, (A ω-a)*B ω ∂μ) = (∫ ω, A ω*B ω ∂μ)-a*(∫ ω, B ω ∂μ) := by
    simp_rw [sub_mul]
    rw [integral_sub hAB (hBI.const_mul a), integral_const_mul]
  have hid : (∫ ω, C ω-A ω*B ω ∂μ)-((∫ ω, C ω ∂μ)-a*(∫ ω, B ω ∂μ)) =
      -(∫ ω, (A ω-a)*B ω ∂μ) := by
    rw [integral_sub hC hAB, he]
    ring
  rw [hid, abs_neg]
  calc
    |∫ ω, (A ω-a)*B ω ∂μ| ≤ ∫ ω, |(A ω-a)*B ω| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => (A ω-a)*B ω)
    _ ≤ ∫ ω, |A ω-a| ∂μ := by
      apply integral_mono hE.abs (hA.sub (integrable_const a)).abs
      intro ω
      dsimp only [Pi.sub_apply]
      rw [abs_mul, abs_of_nonneg (hBb ω).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hBb ω).2

theorem tendsto_type_covariance_zero (F : Measure ℝ) [IsProbabilityMeasure F]
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0 : ℝ) 1)
    (Q : ℕ → ℝ → ℝ) (hQ : ∀ t, Measurable (Q t))
    (hQb : ∀ t v, Q t v ∈ Icc (0 : ℝ) 1)
    (hpair : ∀ᵐ z ∂F.prod F, Tendsto (fun t => Q t z.2-Q t z.1) atTop (𝓝 0)) :
    Tendsto (fun t => (∫ v, h v*Q t v ∂F)-(∫ v, h v ∂F)*(∫ v, Q t v ∂F))
      atTop (𝓝 0) := by
  let f : ℕ → ℝ × ℝ → ℝ := fun t z => h z.1*(Q t z.1-Q t z.2)
  have hf (t : ℕ) : Measurable (f t) :=
    (hh.comp measurable_fst).mul (((hQ t).comp measurable_fst).sub ((hQ t).comp measurable_snd))
  have hfb (t : ℕ) (z : ℝ × ℝ) : ‖f t z‖ ≤ 1 := by
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb z.1).1]
    have hd : |Q t z.1-Q t z.2| ≤ 1 := abs_le.mpr
      ⟨by linarith [(hQb t z.1).1, (hQb t z.2).2],
        by linarith [(hQb t z.1).2, (hQb t z.2).1]⟩
    exact (mul_le_mul (hb z.1).2 hd (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hfi (t : ℕ) : Integrable (f t) (F.prod F) :=
    (integrable_const (1 : ℝ)).mono' (hf t).aestronglyMeasurable (Eventually.of_forall (hfb t))
  have hhi := UnitInterval.integrable F h hh (fun v => (hb v).1) (fun v => (hb v).2)
  have hqi (t : ℕ) := UnitInterval.integrable F (Q t) (hQ t)
    (fun v => (hQb t v).1) (fun v => (hQb t v).2)
  have hhqi (t : ℕ) : Integrable (fun v => h v*Q t v) F :=
    hhi.mul_bdd (hQ t).aestronglyMeasurable (Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQb t v).1]
      exact (hQb t v).2)
  have hid (t : ℕ) : (∫ z, f t z ∂F.prod F) =
      (∫ v, h v*Q t v ∂F)-(∫ v, h v ∂F)*(∫ v, Q t v ∂F) := by
    rw [integral_prod _ (hfi t)]
    have hi (v : ℝ) : (∫ w, f t (v,w) ∂F) = h v*Q t v-h v*(∫ w, Q t w ∂F) := by
      dsimp only [f]
      simp_rw [mul_sub]
      rw [integral_sub (integrable_const _) ((hqi t).const_mul _), integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
    simp_rw [hi]
    rw [integral_sub (hhqi t) (hhi.mul_const _), integral_mul_const]
  have hl : ∀ᵐ z ∂F.prod F, Tendsto (fun t => f t z) atTop (𝓝 0) := by
    filter_upwards [hpair] with z hz
    simpa only [f, neg_sub, mul_zero, neg_zero] using hz.neg.const_mul (h z.1)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : ℝ × ℝ => (1 : ℝ))
    (fun t => (hf t).aestronglyMeasurable) (integrable_const _)
    (fun t => Eventually.of_forall (hfb t)) hl
  simpa only [hid, integral_zero] using ht

end FCAppendix.PayOnce

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def profileMeanType (h : ℝ → ℝ) (d : UserProfile m n) : ℝ :=
  (∑ i, h (d i).1.1) / m

noncomputable def profileWeightedSuccess (Γ : FiniteGame m n c Seed) (h : ℝ → ℝ)
    (d : UserProfile m n) : ℝ := (∑ i, h (d i).1.1 * (profileCountLaw Γ d i).success)/m

noncomputable def profileTypeCovariance (Γ : FiniteGame m n c Seed) (h : ℝ → ℝ)
    (d : UserProfile m n) : ℝ := profileWeightedSuccess Γ h d - profileMeanType h d * profileCoverage Γ d

theorem measurable_profileMeanType {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (profileMeanType (m := m) (n := n) h) :=
  (Finset.measurable_sum _ fun i _ => hh.comp
    (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))).div_const m

theorem profileMeanType_bounds (hm : 0 < m) {h : ℝ → ℝ} (hh : ∀ v, h v ∈ Icc (0 : ℝ) 1)
    (d : UserProfile m n) : profileMeanType h d ∈ Icc (0 : ℝ) 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨div_nonneg (Finset.sum_nonneg fun i _ => (hh (d i).1.1).1) hmR.le, ?_⟩
  apply (div_le_one hmR).mpr
  simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => (hh (d i).1.1).2)

theorem integral_draw_value (Γ : FiniteGame m n c Seed) (h : ℝ → ℝ) (hh : Measurable h) :
    (∫ d : UserDraw n, h d.1.1 ∂userLaw Γ) = ∫ v, h v ∂Γ.F := by
  have hp : MeasurePreserving (fun d : UserDraw n => d.1.1) (userLaw Γ) Γ.F :=
    (show MeasurePreserving (Prod.fst : ℝ × JointAction n → ℝ) (Γ.F ⊗ₘ Γ.σ) Γ.F from
      ⟨measurable_fst, Measure.fst_compProd Γ.F Γ.σ⟩).comp
      (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n))
  rw [← hp.map_eq]
  exact (integral_map hp.measurable.aemeasurable hh.aestronglyMeasurable).symm

theorem integral_profileTypeCovariance_error_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0 : ℝ) 1)
    (bid : ℝ → ℝ) (hbid : Measurable bid)
    (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    |(∫ d, profileTypeCovariance Γ h d ∂userProfileLaw Γ)-
      ((∫ v, h v*averageTypeSuccess Γ bid v ∂Γ.F)-
        (∫ v, h v ∂Γ.F)*(∫ v, averageTypeSuccess Γ bid v ∂Γ.F))| ≤ 1/Real.sqrt m := by
  have hMean := UnitInterval.integrable (userProfileLaw Γ) (profileMeanType (m := m) (n := n) h)
    (measurable_profileMeanType hh) (fun d => (profileMeanType_bounds hm hb d).1)
    (fun d => (profileMeanType_bounds hm hb d).2)
  have hWeighted : Integrable (profileWeightedSuccess Γ h) (userProfileLaw Γ) :=
    (integrable_finsetSum _ (fun i _ => integrable_weighted_profile_success Γ i h hh hb)).div_const m
  have he := PayOnce.integral_covariance_error_le (userProfileLaw Γ) (profileMeanType h)
    (profileCoverage Γ) (profileWeightedSuccess Γ h) (∫ v, h v ∂Γ.F) hMean
    (measurable_profileCoverage Γ) (profileCoverage_bounds Γ hm) hWeighted
  change |(∫ d, profileTypeCovariance Γ h d ∂userProfileLaw Γ)-
    ((∫ d, profileWeightedSuccess Γ h d ∂userProfileLaw Γ)-
      (∫ v, h v ∂Γ.F)*(∫ d, profileCoverage Γ d ∂userProfileLaw Γ))| ≤ _ at he
  have hCov : (∫ d, profileCoverage Γ d ∂userProfileLaw Γ) = ∫ v, averageTypeSuccess Γ bid v ∂Γ.F := by
    simpa only [one_mul, profileCoverage] using
      integral_average_weighted_profile_success_eq_type Γ (fun _ => 1) measurable_const
        (fun _ => ⟨by norm_num, le_rfl⟩) bid hbid hpure
  rw [show (∫ d, profileWeightedSuccess Γ h d ∂userProfileLaw Γ) =
    ∫ v, h v*averageTypeSuccess Γ bid v ∂Γ.F from
      integral_average_weighted_profile_success_eq_type Γ h hh hb bid hbid hpure, hCov] at he
  apply he.trans
  have hEmp := Probability.iid_empiricalMean_L1_le (userLaw Γ)
    (hh.comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable 1 zero_le_one
    (Filter.Eventually.of_forall fun d => by
      change |h d.1.1| ≤ 1
      rw [abs_of_nonneg (hb d.1.1).1]
      exact (hb d.1.1).2) m hm
  simpa only [Function.comp_apply, integral_draw_value Γ h hh, profileMeanType, userProfileLaw] using hEmp

theorem tendsto_integral_profileTypeCovariance_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hm : ∀ t, 0 < M t) (hM : Tendsto M atTop atTop)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0 : ℝ) 1)
    (bid : ℕ → ℝ → ℝ) (hbid : ∀ t, Measurable (bid t))
    (hpure : ∀ t, ∀ᵐ v ∂F, ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid n (bid t v))
    (hpair : ∀ᵐ z ∂F.prod F, Tendsto (fun t =>
      averageTypeSuccess (Γ t) (bid t) z.2-averageTypeSuccess (Γ t) (bid t) z.1)
      atTop (𝓝 0)) :
    Tendsto (fun t => ∫ d, profileTypeCovariance (Γ t) h d ∂userProfileLaw (Γ t))
      atTop (𝓝 0) := by
  let A := fun t => (∫ v, h v*averageTypeSuccess (Γ t) (bid t) v ∂F)-
    (∫ v, h v ∂F)*(∫ v, averageTypeSuccess (Γ t) (bid t) v ∂F)
  have hA : Tendsto A atTop (𝓝 0) := PayOnce.tendsto_type_covariance_zero F h hh hb
    (fun t => averageTypeSuccess (Γ t) (bid t))
    (fun t => measurable_averageTypeSuccess (Γ t) (hbid t))
    (fun t v => averageTypeSuccess_bounds (Γ t) (hm t) (bid t) v) hpair
  have hR : Tendsto (fun t => (1 : ℝ)/Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.comp hM))
  have he (t : ℕ) := integral_profileTypeCovariance_error_le (Γ t) (hm t) h hh hb
    (bid t) (hbid t) (by simpa only [hF t] using hpure t)
  simp only [hF] at he
  have hlo : Tendsto (fun t => A t-1/Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hA.sub hR
  have hhi : Tendsto (fun t => A t+1/Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [add_zero] using hA.add hR
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro t
    have hh' := (abs_le.mp (he t)).1
    dsimp only [A]
    linarith
  · intro t
    have hh' := (abs_le.mp (he t)).2
    dsimp only [A]
    linarith

end FCAppendix.Bayes
