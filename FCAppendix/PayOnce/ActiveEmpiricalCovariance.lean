import FCAppendix.PayOnce.ActiveCovarianceTransport

namespace FCAppendix.PayOnce
open MeasureTheory Filter Topology Set

theorem integral_product_mean_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Ω → ℝ) (a : ℝ)
    (hA : Integrable A P) (hB : Measurable B) (hBb : ∀ ω, B ω ∈ Icc (0:ℝ) 1) :
    |(∫ ω, A ω*B ω ∂P)-a*(∫ ω, B ω ∂P)| ≤ ∫ ω, |A ω-a| ∂P := by
  have hh := integral_covariance_error_le P A B (fun _ => 0) a hA hB hBb (integrable_const 0)
  simpa only [zero_sub,integral_neg,integral_zero,neg_sub_neg,abs_sub_comm] using hh

theorem integral_products_difference_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B C D : Ω → ℝ) (a b : ℝ)
    (hA : Integrable A P) (hC : Integrable C P)
    (hB : Measurable B) (hD : Measurable D)
    (hBb : ∀ ω, B ω ∈ Icc (0:ℝ) 1) (hDb : ∀ ω, D ω ∈ Icc (0:ℝ) 1) :
    |(∫ ω, A ω*B ω-C ω*D ω ∂P)-(a*(∫ ω, B ω ∂P)-b*(∫ ω, D ω ∂P))| ≤
      (∫ ω, |A ω-a| ∂P)+(∫ ω, |C ω-b| ∂P) := by
  have hAB : Integrable (fun ω => A ω*B ω) P := hA.mul_bdd hB.aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hBb ω).1]
      exact (hBb ω).2)
  have hCD : Integrable (fun ω => C ω*D ω) P := hC.mul_bdd hD.aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hDb ω).1]
      exact (hDb ω).2)
  rw [integral_sub hAB hCD]
  have he : (∫ ω, A ω*B ω ∂P)-(∫ ω, C ω*D ω ∂P)-
      (a*(∫ ω, B ω ∂P)-b*(∫ ω, D ω ∂P)) =
      ((∫ ω, A ω*B ω ∂P)-a*(∫ ω, B ω ∂P))-
        ((∫ ω, C ω*D ω ∂P)-b*(∫ ω, D ω ∂P)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add
    (integral_product_mean_error_le P A B a hA hB hBb)
    (integral_product_mean_error_le P C D b hC hD hDb))

end FCAppendix.PayOnce

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_profileWeightedSuccess (Γ : FiniteGame m n c Seed)
    {h : ℝ → ℝ} (hh : Measurable h) : Measurable (profileWeightedSuccess Γ h) :=
  (Finset.measurable_sum _ fun i _ =>
    (hh.comp (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))).mul
      (measurable_profile_expect Γ i _)).div_const m

theorem profileWeightedSuccess_bounds (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    {h : ℝ → ℝ} (hb : ∀ v, h v ∈ Icc (0:ℝ) 1) (d : UserProfile m n) :
    profileWeightedSuccess Γ h d ∈ Icc (0:ℝ) 1 := by
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hb _).1 (CountLaw.success_nonneg _)) hmR.le
  · apply (div_le_one hmR).mpr
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => mul_le_one₀ (hb (d i).1.1).2 (CountLaw.success_nonneg (profileCountLaw Γ d i)) (CountLaw.success_le_one _))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh

theorem integral_profileMeanType_error_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0:ℝ) 1) :
    (∫ d, |profileMeanType h d-∫ v, h v ∂Γ.F| ∂userProfileLaw Γ) ≤ 1/Real.sqrt m := by
  have hEmp := Probability.iid_empiricalMean_L1_le (userLaw Γ)
    (hh.comp (measurable_fst.comp measurable_fst)).aestronglyMeasurable 1 zero_le_one
    (Eventually.of_forall fun d => by
      change |h d.1.1| ≤ 1
      rw [abs_of_nonneg (hb d.1.1).1]
      exact (hb d.1.1).2) m hm
  simpa only [Function.comp_apply,integral_draw_value Γ h hh,profileMeanType,userProfileLaw] using hEmp

noncomputable def profileWeightedCovariance (Γ : FiniteGame m n c Seed)
    (s h : ℝ → ℝ) (d : UserProfile m n) : ℝ :=
  profileMeanType s d*profileWeightedSuccess Γ h d-
    profileMeanType h d*profileWeightedSuccess Γ s d

theorem integral_profileWeightedCovariance_error_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (s h : ℝ → ℝ) (hs : Measurable s) (hh : Measurable h)
    (hsb : ∀ v, s v ∈ Icc (0:ℝ) 1) (hhb : ∀ v, h v ∈ Icc (0:ℝ) 1)
    (hsz : ∀ v, v ≤ Γ.g → s v = 0) (hhz : ∀ v, v ≤ Γ.g → h v = 0)
    (bid : ℝ → ℝ) (hbid : Measurable bid)
    (hpure : ∀ᵐ v ∂Γ.F, Γ.g < v → ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    |(∫ d, profileWeightedCovariance Γ s h d ∂userProfileLaw Γ)-
      ((∫ v, s v ∂Γ.F)*(∫ v, h v*averageTypeSuccess Γ bid v ∂Γ.F)-
        (∫ v, h v ∂Γ.F)*(∫ v, s v*averageTypeSuccess Γ bid v ∂Γ.F))| ≤ 2/Real.sqrt m := by
  have hsi := UnitInterval.integrable (userProfileLaw Γ) (profileMeanType (m := m) (n := n) s)
    (measurable_profileMeanType hs) (fun d => (profileMeanType_bounds hm hsb d).1)
    (fun d => (profileMeanType_bounds hm hsb d).2)
  have hhi := UnitInterval.integrable (userProfileLaw Γ) (profileMeanType (m := m) (n := n) h)
    (measurable_profileMeanType hh) (fun d => (profileMeanType_bounds hm hhb d).1)
    (fun d => (profileMeanType_bounds hm hhb d).2)
  have he := PayOnce.integral_products_difference_error_le (userProfileLaw Γ)
    (profileMeanType s) (profileWeightedSuccess Γ h) (profileMeanType h) (profileWeightedSuccess Γ s)
    (∫ v, s v ∂Γ.F) (∫ v, h v ∂Γ.F) hsi hhi
    (measurable_profileWeightedSuccess Γ hh) (measurable_profileWeightedSuccess Γ hs)
    (profileWeightedSuccess_bounds Γ hm hhb) (profileWeightedSuccess_bounds Γ hm hsb)
  rw [integral_average_weighted_profile_success_eq_type_on_positive Γ h hh hhb hhz bid hbid hpure,
    integral_average_weighted_profile_success_eq_type_on_positive Γ s hs hsb hsz bid hbid hpure] at he
  exact he.trans (by
    have h1 := integral_profileMeanType_error_le Γ hm s hs hsb
    have h2 := integral_profileMeanType_error_le Γ hm h hh hhb
    exact (add_le_add h1 h2).trans_eq (by ring))

end FCAppendix.Bayes

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators

theorem tendsto_integral_active_profile_covariance_zero
    {M C : ℕ → ℕ} {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (hm : ∀ t, 0 < M t)
    (hM : Tendsto M atTop atTop) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hpos : F (Ioi g) ≠ 0) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ v, h v ∈ Icc (0:ℝ) 1) (bid : ℕ → ℝ → ℝ) (hbid : ∀ t, Measurable (bid t))
    (hpure : ∀ t, ∀ᵐ v ∂F, g < v → ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid n (bid t v))
    (hpair : ∀ᵐ z ∂(ProbabilityTheory.cond F (Ioi g)).prod (ProbabilityTheory.cond F (Ioi g)),
      Tendsto (fun t => averageTypeSuccess (Γ t) (bid t) z.2-
        averageTypeSuccess (Γ t) (bid t) z.1) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ d, profileWeightedCovariance (Γ t)
      ((Ioi g).indicator (fun _ => 1)) ((Ioi g).indicator h) d ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  let s : ℝ → ℝ := (Ioi g).indicator (fun _ => 1)
  let hI := (Ioi g).indicator h
  have hs : Measurable s := measurable_const.indicator measurableSet_Ioi
  have hIm : Measurable hI := hh.indicator measurableSet_Ioi
  have hsb v : s v ∈ Icc (0:ℝ) 1 := by
    by_cases hv : v ∈ Ioi g <;> simp [s,hv]
  have hIb v : hI v ∈ Icc (0:ℝ) 1 := by
    by_cases hv : v ∈ Ioi g
    · simpa only [hI,indicator_of_mem hv] using hb v
    · simp [hI,hv]
  let A := fun t => F.real (Ioi g)*(∫ v, hI v*averageTypeSuccess (Γ t) (bid t) v ∂F)-
    (∫ v, hI v ∂F)*(∫ v, (Ioi g).indicator (averageTypeSuccess (Γ t) (bid t)) v ∂F)
  have hA : Tendsto A atTop (𝓝 0) := PayOnce.tendsto_active_type_covariance_zero F g hpos h hh hb
    (fun t => averageTypeSuccess (Γ t) (bid t))
    (fun t => measurable_averageTypeSuccess (Γ t) (hbid t))
    (fun t v => averageTypeSuccess_bounds (Γ t) (hm t) (bid t) v) hpair
  have hR : Tendsto (fun t => (2:ℝ)/Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop.comp hM))).const_mul 2
  have he (t : ℕ) : |(∫ d, profileWeightedCovariance (Γ t) s hI d ∂userProfileLaw (Γ t))-A t| ≤
      2/Real.sqrt (M t) := by
    have hp : ∀ᵐ v ∂(Γ t).F, (Γ t).g < v → ∀ᵐ a ∂(Γ t).σ v, a = safeFullBid n (bid t v) := by
      simpa only [hF t,hg t] using hpure t
    have he := integral_profileWeightedCovariance_error_le (Γ t) (hm t) s hI hs hIm hsb hIb
      (fun v hv => by simp [s,mem_Ioi,not_lt_of_ge (by simpa only [hg t] using hv : v ≤ g)])
      (fun v hv => by simp [hI,mem_Ioi,not_lt_of_ge (by simpa only [hg t] using hv : v ≤ g)])
      (bid t) (hbid t) hp
    rw [hF t] at he
    have hsint : (∫ v, s v ∂F) = F.real (Ioi g) := by
      rw [show s = (Ioi g).indicator (fun _ => (1:ℝ)) from rfl,
        integral_indicator measurableSet_Ioi,setIntegral_const,smul_eq_mul,mul_one]
    have hsq (v) : s v*averageTypeSuccess (Γ t) (bid t) v =
        (Ioi g).indicator (averageTypeSuccess (Γ t) (bid t)) v := by
      by_cases hv : v ∈ Ioi g <;> simp [s,hv]
    simpa only [hsint,hsq,A] using he
  have hlo : Tendsto (fun t => A t-2/Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [sub_zero] using hA.sub hR
  have hhi : Tendsto (fun t => A t+2/Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [add_zero] using hA.add hR
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro t
    have hh' := (abs_le.mp (he t)).1
    linarith
  · intro t
    have hh' := (abs_le.mp (he t)).2
    linarith

end FCAppendix.Bayes
