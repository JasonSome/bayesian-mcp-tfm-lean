import FCAppendix.PayOnce.EmpiricalCovariance
import FCAppendix.PayOnce.EffectiveVanishingBid

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem integral_weighted_profile_success_eq_type_on_positive (Γ : FiniteGame m n c Seed)
    (i : Fin m) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0:ℝ) 1)
    (hz : ∀ v, v ≤ Γ.g → h v = 0) (bid : ℝ → ℝ)
    (hpure : ∀ᵐ v ∂Γ.F, Γ.g < v → ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    (∫ d, h (d i).1.1*(profileCountLaw Γ d i).success ∂userProfileLaw Γ) =
      ∫ v, h v*((problem Γ i).outcome (safeFullBid n (bid v))).success ∂Γ.F := by
  rw [integral_weighted_profile_success_eq_interim Γ i h hh hb]
  have hi : Integrable (fun x : ℝ × JointAction n => h x.1*((problem Γ i).outcome x.2).success)
      (Γ.F ⊗ₘ Γ.σ) := by
    apply UnitInterval.integrable _ _ ((hh.comp measurable_fst).mul ((measurable_success Γ i).comp measurable_snd))
    · intro x
      exact mul_nonneg (hb x.1).1 (CountLaw.success_nonneg _)
    · intro x
      exact mul_le_one₀ (hb x.1).2 (CountLaw.success_nonneg _) (CountLaw.success_le_one _)
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [hpure] with v hv
  by_cases hpos : Γ.g < v
  · have he : (fun a : JointAction n => h v*((problem Γ i).outcome a).success) =ᵐ[Γ.σ v]
        fun _ => h v*((problem Γ i).outcome (safeFullBid n (bid v))).success := by
      filter_upwards [hv hpos] with a ha
      rw [ha]
    rw [integral_congr_ae he]
    simp only [integral_const,probReal_univ,one_smul]
  · simp only [hz v (le_of_not_gt hpos),zero_mul,integral_zero]

theorem integral_average_weighted_profile_success_eq_type_on_positive (Γ : FiniteGame m n c Seed)
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0:ℝ) 1)
    (hz : ∀ v, v ≤ Γ.g → h v = 0) (bid : ℝ → ℝ) (hbid : Measurable bid)
    (hpure : ∀ᵐ v ∂Γ.F, Γ.g < v → ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    (∫ d, profileWeightedSuccess Γ h d ∂userProfileLaw Γ) =
      ∫ v, h v*averageTypeSuccess Γ bid v ∂Γ.F := by
  have hi (i : Fin m) : Integrable (fun v => h v*((problem Γ i).outcome (safeFullBid n (bid v))).success) Γ.F := by
    apply UnitInterval.integrable _ _ (hh.mul ((measurable_success Γ i).comp ((measurable_safeFullBid n).comp hbid)))
    · intro v
      exact mul_nonneg (hb v).1 (CountLaw.success_nonneg _)
    · intro v
      exact mul_le_one₀ (hb v).2 (CountLaw.success_nonneg _) (CountLaw.success_le_one _)
  unfold profileWeightedSuccess
  rw [integral_div,integral_finsetSum _ (fun i _ => integrable_weighted_profile_success Γ i h hh hb)]
  simp_rw [integral_weighted_profile_success_eq_type_on_positive Γ _ h hh hb hz bid hpure]
  rw [← integral_finsetSum _ (fun i _ => hi i),← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    simp only [averageTypeSuccess,← Finset.mul_sum,mul_div_assoc]

end FCAppendix.Bayes

namespace FCAppendix.PayOnce
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem integral_indicator_eq_mass_mul_cond {Ω : Type*} [MeasurableSpace Ω]
    (F : Measure Ω) [IsFiniteMeasure F] (S : Set Ω) (hS : MeasurableSet S)
    (hpos : F S ≠ 0) (f : Ω → ℝ) :
    (∫ v, S.indicator f v ∂F) = F.real S*(∫ v, f v ∂ProbabilityTheory.cond F S) := by
  rw [integral_indicator hS,ProbabilityTheory.cond,integral_smul_measure,
    ENNReal.toReal_inv,smul_eq_mul]
  change (∫ v in S, f v ∂F) = (F S).toReal*((F S).toReal⁻¹*(∫ v in S, f v ∂F))
  rw [mul_inv_cancel_left₀ (ENNReal.toReal_ne_zero.mpr ⟨hpos,measure_ne_top _ _⟩)]

theorem active_type_covariance_eq_cond (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hpos : F (Ioi g) ≠ 0) (h Q : ℝ → ℝ) :
    F.real (Ioi g)*(∫ v, (Ioi g).indicator h v*Q v ∂F)-
      (∫ v, (Ioi g).indicator h v ∂F)*(∫ v, (Ioi g).indicator Q v ∂F) =
    (F.real (Ioi g))^2*((∫ v, h v*Q v ∂ProbabilityTheory.cond F (Ioi g))-
      (∫ v, h v ∂ProbabilityTheory.cond F (Ioi g))*(∫ v, Q v ∂ProbabilityTheory.cond F (Ioi g))) := by
  have he (v) : (Ioi g).indicator h v*Q v = (Ioi g).indicator (fun v => h v*Q v) v := by
    by_cases hv : v ∈ Ioi g <;> simp [hv]
  simp_rw [he]
  rw [integral_indicator_eq_mass_mul_cond F _ measurableSet_Ioi hpos,
    integral_indicator_eq_mass_mul_cond F _ measurableSet_Ioi hpos,
    integral_indicator_eq_mass_mul_cond F _ measurableSet_Ioi hpos]
  ring

theorem tendsto_active_type_covariance_zero (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hpos : F (Ioi g) ≠ 0) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0:ℝ) 1)
    (Q : ℕ → ℝ → ℝ) (hQ : ∀ t, Measurable (Q t))
    (hQb : ∀ t v, Q t v ∈ Icc (0:ℝ) 1)
    (hpair : ∀ᵐ z ∂(ProbabilityTheory.cond F (Ioi g)).prod (ProbabilityTheory.cond F (Ioi g)),
      Tendsto (fun t => Q t z.2-Q t z.1) atTop (𝓝 0)) :
    Tendsto (fun t => F.real (Ioi g)*(∫ v, (Ioi g).indicator h v*Q t v ∂F)-
      (∫ v, (Ioi g).indicator h v ∂F)*(∫ v, (Ioi g).indicator (Q t) v ∂F)) atTop (𝓝 0) := by
  haveI := ProbabilityTheory.cond_isProbabilityMeasure hpos
  have ht := tendsto_type_covariance_zero (ProbabilityTheory.cond F (Ioi g)) h hh hb Q hQ hQb hpair
  simp_rw [active_type_covariance_eq_cond F g hpos h]
  simpa only [mul_zero] using ht.const_mul ((F.real (Ioi g))^2)

end FCAppendix.PayOnce
