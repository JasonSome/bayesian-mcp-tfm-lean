import FCAppendix.PayOnce.VanishingBidLaw

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem integral_weighted_profile_success_eq_interim (Γ : FiniteGame m n c Seed)
    (i : Fin m) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0 : ℝ) 1) :
    (∫ d, h (d i).1.1 * (profileCountLaw Γ d i).success ∂userProfileLaw Γ) =
      ∫ x, h x.1 * ((problem Γ i).outcome x.2).success ∂(Γ.F ⊗ₘ Γ.σ) := by
  let f := fun p : (ℝ × JointAction n) × Fin (n+1) => h p.1.1 * successIndicator p.2.val
  have hf : Measurable f := (hh.comp (measurable_fst.comp measurable_fst)).mul
    ((measurable_of_countable (fun q : Fin (n+1) => successIndicator q.val)).comp measurable_snd)
  have hfb (p : (ℝ × JointAction n) × Fin (n+1)) : ‖f p‖ ≤ 1 := by
    dsimp only [f]
    unfold successIndicator
    split_ifs
    · simp only [mul_zero, norm_zero, zero_le_one]
    · rw [mul_one, Real.norm_eq_abs, abs_of_nonneg (hb p.1.1).1]
      exact (hb p.1.1).2
  have hi := integrable_realized_statistic Γ i f hf 1 hfb
  have he (d : UserProfile m n) : h (d i).1.1 * (profileCountLaw Γ d i).success =
      ∫ s, f ((d i).1, playedCount Γ i (d,s)) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw) := by
    rw [CountLaw.success]
    unfold profileCountLaw
    rw [CountLaw.expect_ofMeasure]
    dsimp only [f]
    rw [integral_const_mul]
  calc
    _ = ∫ d, ∫ s, f ((d i).1, playedCount Γ i (d,s))
        ∂Measure.pi (fun _ : Fin n => Γ.seedLaw) ∂userProfileLaw Γ :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = ∫ ω, f ((ω.1 i).1, playedCount Γ i ω) ∂backgroundLaw Γ := by
      exact (integral_prod _ hi).symm
    _ = _ := by
      have htransfer := integral_realized_eq_interim Γ i f hf 1 hfb
      simpa only [f, CountLaw.success, FiniteLaw.expect_const_mul] using htransfer

theorem integral_weighted_profile_success_eq_type (Γ : FiniteGame m n c Seed)
    (i : Fin m) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0 : ℝ) 1)
    (bid : ℝ → ℝ) (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    (∫ d, h (d i).1.1 * (profileCountLaw Γ d i).success ∂userProfileLaw Γ) =
      ∫ v, h v * ((problem Γ i).outcome (safeFullBid n (bid v))).success ∂Γ.F := by
  rw [integral_weighted_profile_success_eq_interim Γ i h hh hb]
  have hi : Integrable (fun x : ℝ × JointAction n => h x.1 * ((problem Γ i).outcome x.2).success)
      (Γ.F ⊗ₘ Γ.σ) := by
    apply UnitInterval.integrable _ _ ((hh.comp measurable_fst).mul ((measurable_success Γ i).comp measurable_snd))
    · intro x
      exact mul_nonneg (hb x.1).1 (CountLaw.success_nonneg _)
    · intro x
      exact mul_le_one₀ (hb x.1).2 (CountLaw.success_nonneg _) (CountLaw.success_le_one _)
  rw [Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [hpure] with v hv
  have he : (fun a : JointAction n => h v * ((problem Γ i).outcome a).success) =ᵐ[Γ.σ v]
      fun _ => h v * ((problem Γ i).outcome (safeFullBid n (bid v))).success := by
    filter_upwards [hv] with a ha
    rw [ha]
  rw [integral_congr_ae he]
  simp only [integral_const, probReal_univ, one_smul]

theorem integrable_weighted_profile_success (Γ : FiniteGame m n c Seed)
    (i : Fin m) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0 : ℝ) 1) :
    Integrable (fun d => h (d i).1.1 * (profileCountLaw Γ d i).success) (userProfileLaw Γ) := by
  apply UnitInterval.integrable _ _
    ((hh.comp (measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i)))).mul
      (measurable_profile_expect Γ i _))
  · intro d
    exact mul_nonneg (hb (d i).1.1).1 (CountLaw.success_nonneg _)
  · intro d
    exact mul_le_one₀ (hb (d i).1.1).2 (CountLaw.success_nonneg _) (CountLaw.success_le_one _)

theorem integral_average_weighted_profile_success_eq_type (Γ : FiniteGame m n c Seed)
    (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ v, h v ∈ Icc (0 : ℝ) 1)
    (bid : ℝ → ℝ) (hbid : Measurable bid)
    (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    (∫ d, (∑ i, h (d i).1.1 * (profileCountLaw Γ d i).success) / m ∂userProfileLaw Γ) =
      ∫ v, h v * averageTypeSuccess Γ bid v ∂Γ.F := by
  have hi (i : Fin m) : Integrable (fun v => h v *
      ((problem Γ i).outcome (safeFullBid n (bid v))).success) Γ.F := by
    apply UnitInterval.integrable _ _ (hh.mul ((measurable_success Γ i).comp ((measurable_safeFullBid n).comp hbid)))
    · intro v
      exact mul_nonneg (hb v).1 (CountLaw.success_nonneg _)
    · intro v
      exact mul_le_one₀ (hb v).2 (CountLaw.success_nonneg _) (CountLaw.success_le_one _)
  rw [integral_div, integral_finsetSum _ (fun i _ => integrable_weighted_profile_success Γ i h hh hb)]
  simp_rw [integral_weighted_profile_success_eq_type Γ _ h hh hb bid hpure]
  rw [← integral_finsetSum _ (fun i _ => hi i), ← integral_div]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  simp only [averageTypeSuccess, ← Finset.mul_sum, mul_div_assoc]

end FCAppendix.Bayes
