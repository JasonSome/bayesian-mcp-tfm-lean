import FCAppendix.Ample.CommonRateActualAdapters
import FCAppendix.Ample.ActualRouteCompactness
import FCAppendix.Finite.ConditionalCountLaw

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped BigOperators ENNReal

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def actualPopulationInclusionMass (Γ : FiniteGame m n c Seed) (j : ℕ) : ℝ :=
  ∫ d, (∑ i : Fin m,
    (profileCountLaw Γ d i).prob (fun r => r.val = j)) / (m : ℝ)
      ∂userProfileLaw Γ

theorem actual_integrable_profile_expect (Γ : FiniteGame m n c Seed)
    (i : Fin m) (f : Fin (n + 1) → ℝ) :
    Integrable (fun d => (profileCountLaw Γ d i).expect f) (userProfileLaw Γ) :=
  Integrable.of_bound (measurable_profile_expect Γ i f).aestronglyMeasurable
    (∑ r, ‖f r‖) (ae_of_all _ fun d => (profileCountLaw Γ d i).norm_expect_le_sum_norm f)

theorem actual_integrable_joint_expect (Γ : FiniteGame m n c Seed)
    (i : Fin m) (f : Fin (n + 1) → ℝ) :
    Integrable (fun x : ℝ × JointAction n => ((problem Γ i).outcome x.2).expect f)
      (Γ.F ⊗ₘ Γ.σ) :=
  FiniteLaw.integrable_expect _ _
    (fun r => (measurable_outcome_mass Γ i r).comp measurable_snd) f

theorem integral_profile_expect_eq_joint_expect (Γ : FiniteGame m n c Seed)
    (i : Fin m) (f : Fin (n + 1) → ℝ) :
    (∫ d, (profileCountLaw Γ d i).expect f ∂userProfileLaw Γ) =
      ∫ x, ((problem Γ i).outcome x.2).expect f ∂(Γ.F ⊗ₘ Γ.σ) := by
  calc
    _ = ∫ ω, f (playedCount Γ i ω) ∂backgroundLaw Γ := by
      unfold profileCountLaw
      simp_rw [CountLaw.expect_ofMeasure]
      exact (integral_prod _ (CountLaw.integrable_comp (backgroundLaw Γ) _
        (measurable_playedCount Γ i) f)).symm
    _ = _ := by
      apply integral_realized_eq_interim Γ i (fun x => f x.2)
        ((measurable_of_countable f).comp measurable_snd) (∑ r, ‖f r‖)
      intro x
      exact Finset.single_le_sum (fun r _ => norm_nonneg (f r)) (Finset.mem_univ x.2)

def actualIdentityCountLaw (Γ : FiniteGame m n c Seed) (i : Fin m) : CountLaw n :=
  FiniteLaw.average (Γ.F ⊗ₘ Γ.σ) (fun x => (problem Γ i).outcome x.2)
    (fun r => (measurable_outcome_mass Γ i r).comp measurable_snd)

theorem actualIdentityCountLaw_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) :
    (actualIdentityCountLaw Γ i).expect f =
      ∫ x, ((problem Γ i).outcome x.2).expect f ∂(Γ.F ⊗ₘ Γ.σ) :=
  FiniteLaw.expect_average _ _ _ _

def actualPopulationCountLaw (Γ : FiniteGame m n c Seed) (hm : 0 < m) : CountLaw n :=
  FiniteLaw.uniformAverage hm (fun i => actualIdentityCountLaw Γ i)

theorem actualPopulationCountLaw_expect (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (f : Fin (n + 1) → ℝ) :
    (actualPopulationCountLaw Γ hm).expect f =
      (∑ i : Fin m, ∫ x, ((problem Γ i).outcome x.2).expect f ∂(Γ.F ⊗ₘ Γ.σ)) / m := by
  rw [actualPopulationCountLaw, FiniteLaw.expect_uniformAverage]
  simp only [actualIdentityCountLaw_expect]

theorem actualPopulationInclusionMass_eq_average_interim
    (Γ : FiniteGame m n c Seed) (j : ℕ) :
    actualPopulationInclusionMass Γ j =
      (∑ i : Fin m, ∫ x, ((problem Γ i).outcome x.2).prob (fun r => r.val = j)
        ∂(Γ.F ⊗ₘ Γ.σ)) / m := by
  classical
  unfold actualPopulationInclusionMass
  simp_rw [FiniteLaw.prob_eq_expect]
  rw [integral_div, integral_finsetSum _
    (fun i _ => actual_integrable_profile_expect Γ i _)]
  simp_rw [integral_profile_expect_eq_joint_expect]

theorem actualPopulationInclusionMass_eq_prob (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (j : ℕ) :
    actualPopulationInclusionMass Γ j =
      (actualPopulationCountLaw Γ hm).prob (fun r => r.val = j) := by
  classical
  rw [actualPopulationInclusionMass_eq_average_interim, FiniteLaw.prob_eq_expect,
    actualPopulationCountLaw_expect]
  simp only [FiniteLaw.prob_eq_expect]

theorem actualPopulationCountLaw_load (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    (actualPopulationCountLaw Γ hm).load = finiteLoad Γ := by
  rw [CountLaw.load, actualPopulationCountLaw_expect, finiteLoad_eq_actual]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  symm
  apply integral_realized_eq_interim Γ i (fun x => (x.2.val : ℝ))
    ((measurable_of_countable (fun r : Fin (n + 1) => (r.val : ℝ))).comp measurable_snd)
    (n : ℝ)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.le_of_lt_succ x.2.isLt)

theorem actualPopulationCountLaw_success (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    (actualPopulationCountLaw Γ hm).success = finiteCoverage Γ := by
  rw [CountLaw.success, actualPopulationCountLaw_expect, finiteCoverage_eq_actual]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (integral_realized_success_eq_interim Γ i).symm

def actualChosenIndicator (j : ℕ) (x : ℝ × JointAction n) : ℝ :=
  if x.2.routeCount = j then 1 else 0

theorem actualChosenIndicator_measurable (j : ℕ) :
    Measurable (actualChosenIndicator (n := n) j) := by
  classical
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const)
    measurable_const measurable_const

theorem actualChosenIndicator_integrable (Γ : FiniteGame m n c Seed) (j : ℕ) :
    Integrable (actualChosenIndicator (n := n) j) (Γ.F ⊗ₘ Γ.σ) := by
  apply Integrable.of_bound (actualChosenIndicator_measurable j).aestronglyMeasurable 1
  filter_upwards [] with x
  dsimp [actualChosenIndicator]
  split <;> norm_num

theorem actualRouteMass_eq_integral_indicator (Γ : FiniteGame m n c Seed) (j : ℕ) :
    actualRouteMass Γ j = ∫ x, actualChosenIndicator j x ∂(Γ.F ⊗ₘ Γ.σ) := by
  classical
  have hset : MeasurableSet {x : ℝ × JointAction n | x.2.routeCount = j} :=
    measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const
  rw [actualRouteMass, ← integral_indicator_one hset]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Set.indicator, actualChosenIndicator]

theorem actual_abs_integral_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (e : ℝ)
    (h : ∀ᵐ x ∂μ, |f x - g x| ≤ e) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ e := by
  have hl := integral_mono_ae (integrable_const (-e)) (hf.sub hg)
    (h.mono fun x hx => (abs_le.mp hx).1)
  have hu := integral_mono_ae (hf.sub hg) (integrable_const e)
    (h.mono fun x hx => (abs_le.mp hx).2)
  simp only [Pi.sub_apply] at hl hu
  rw [integral_sub hf hg] at hl hu
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hl hu
  exact abs_le.mpr ⟨hl, hu⟩

theorem actual_count_indicator_error (μ : CountLaw n) (k j : ℕ) :
    |μ.prob (fun r => r.val = j) - (if k = j then 1 else 0)| ≤
      μ.prob (fun r => r.val ≠ k) := by
  classical
  have hc : μ.prob (fun _ : Fin (n + 1) => k = j) =
      (if k = j then 1 else 0) := by
    by_cases hk : k = j <;> simp [hk]
  simpa only [hc] using μ.coupling_event_bound (fun r => r.val) (fun _ => k) j

theorem actual_identity_count_error_of_copy_error
    (Γ : FiniteGame m n c Seed) (i : Fin m) (e : ℝ)
    (hcopy : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      ((problem Γ i).outcome x.2).prob (fun r => r.val ≠ x.2.routeCount) ≤ e)
    (j : ℕ) :
    |(∫ x, ((problem Γ i).outcome x.2).prob (fun r => r.val = j)
        ∂(Γ.F ⊗ₘ Γ.σ)) - actualRouteMass Γ j| ≤ e := by
  classical
  rw [actualRouteMass_eq_integral_indicator]
  apply actual_abs_integral_sub_le (Γ.F ⊗ₘ Γ.σ) _ _
    (by simpa only [FiniteLaw.prob_eq_expect] using
      actual_integrable_joint_expect Γ i (fun r => if r.val = j then 1 else 0))
    (actualChosenIndicator_integrable Γ j) e
  filter_upwards [hcopy] with x hx
  exact (actual_count_indicator_error ((problem Γ i).outcome x.2) x.2.routeCount j).trans hx

theorem actual_finite_average_error (hm : 0 < m) (u : Fin m → ℝ) (a e : ℝ)
    (h : ∀ i, |u i - a| ≤ e) : |(∑ i, u i) / (m : ℝ) - a| ≤ e := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlo : a - e ≤ (∑ i, u i) / (m : ℝ) := by
    apply (le_div_iff₀ hmR).mpr
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => show a - e ≤ u i by linarith [(abs_le.mp (h i)).1])
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_comm] using hh
  have hhi : (∑ i, u i) / (m : ℝ) ≤ a + e := by
    apply (div_le_iff₀ hmR).mpr
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => show u i ≤ a + e by linarith [(abs_le.mp (h i)).2])
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_comm] using hh
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem actual_count_error_of_copy_error
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (e : ℝ) (he : 0 ≤ e)
    (hcopy : ∀ i : Fin m, ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      ((problem Γ i).outcome x.2).prob (fun r => r.val ≠ x.2.routeCount) ≤ e) :
    ∀ j : ℕ,
      |actualInclusionMass Γ j - actualRouteMass Γ j| ≤ e ∧
      |actualPopulationInclusionMass Γ j - actualRouteMass Γ j| ≤ e := by
  have hcopy' : ∀ i : Fin m, ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      ((problem Γ i).outcome x.2).prob (fun r => r.val ≠ x.2.routeCount) ≤ |e| := by
    simpa only [abs_of_nonneg he] using hcopy
  intro j
  have hi := fun i => actual_identity_count_error_of_copy_error Γ i |e| (hcopy' i) j
  constructor
  · simpa only [actualInclusionMass, dif_pos hm, abs_of_nonneg he] using hi ⟨0, hm⟩
  · rw [actualPopulationInclusionMass_eq_average_interim]
    simpa only [abs_of_nonneg he] using
      actual_finite_average_error hm _ (actualRouteMass Γ j) |e| hi

theorem actual_countLaw_load_sum (μ : CountLaw n) :
    μ.load = ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * μ.prob (fun r => r.val = j) := by
  classical
  have hpoint (r : Fin (n + 1)) :
      (r.val : ℝ) = ∑ j ∈ Finset.Icc 1 n,
        (j : ℝ) * (if r.val = j then (1 : ℝ) else 0) := by
    by_cases hr : r.val = 0
    · rw [hr, Nat.cast_zero]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : (0 : ℕ) ≠ j := by have := (Finset.mem_Icc.mp hj).1; omega
      simp only [if_neg hj0, mul_zero]
    · have hmem : r.val ∈ Finset.Icc 1 n := by
        simp only [Finset.mem_Icc]
        exact ⟨by omega, Nat.le_of_lt_succ r.isLt⟩
      symm
      calc
        _ = (r.val : ℝ) * (if r.val = r.val then (1 : ℝ) else 0) := by
          apply Finset.sum_eq_single r.val
          · intro j hj hjr
            simp only [if_neg (Ne.symm hjr), mul_zero]
          · intro hnot
            exact (hnot hmem).elim
        _ = _ := by simp
  calc
    μ.load = μ.expect (fun r => ∑ j ∈ Finset.Icc 1 n,
        (j : ℝ) * (if r.val = j then (1 : ℝ) else 0)) := μ.expect_congr hpoint
    _ = ∑ j ∈ Finset.Icc 1 n,
        μ.expect (fun r => (j : ℝ) * (if r.val = j then (1 : ℝ) else 0)) :=
      μ.expect_finset_sum _ _
    _ = _ := by simp only [FiniteLaw.expect_const_mul, ← FiniteLaw.prob_eq_expect]

theorem actual_countLaw_success_sum (μ : CountLaw n) :
    μ.success = ∑ j ∈ Finset.Icc 1 n, μ.prob (fun r => r.val = j) := by
  classical
  have hpoint (r : Fin (n + 1)) : successIndicator r.val =
      ∑ j ∈ Finset.Icc 1 n, (if r.val = j then (1 : ℝ) else 0) := by
    by_cases hr : r.val = 0
    · simp only [hr, successIndicator, if_true]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hj0 : (0 : ℕ) ≠ j := by have := (Finset.mem_Icc.mp hj).1; omega
      exact if_neg hj0
    · have hmem : r.val ∈ Finset.Icc 1 n := by
        simp only [Finset.mem_Icc]
        exact ⟨by omega, Nat.le_of_lt_succ r.isLt⟩
      simp only [successIndicator, if_neg hr]
      symm
      calc
        _ = (if r.val = r.val then (1 : ℝ) else 0) := by
          apply Finset.sum_eq_single r.val
          · intro j hj hjr
            exact if_neg (Ne.symm hjr)
          · intro hnot
            exact (hnot hmem).elim
        _ = 1 := if_pos rfl
  calc
    μ.success = μ.expect (fun r => ∑ j ∈ Finset.Icc 1 n,
        (if r.val = j then (1 : ℝ) else 0)) := μ.expect_congr hpoint
    _ = _ := by rw [FiniteLaw.expect_finset_sum]; simp only [← FiniteLaw.prob_eq_expect]

theorem load_as_finite_count_sum (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    finiteLoad Γ = ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * actualPopulationInclusionMass Γ j := by
  rw [← actualPopulationCountLaw_load Γ hm, actual_countLaw_load_sum]
  simp only [actualPopulationInclusionMass_eq_prob Γ hm]

theorem finite_load_as_count_sum (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    finiteLoad Γ = ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * actualPopulationInclusionMass Γ j :=
  load_as_finite_count_sum Γ hm

theorem coverage_as_finite_count_sum (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    finiteCoverage Γ = ∑ j ∈ Finset.Icc 1 n, actualPopulationInclusionMass Γ j := by
  rw [← actualPopulationCountLaw_success Γ hm, actual_countLaw_success_sum]
  simp only [actualPopulationInclusionMass_eq_prob Γ hm]

theorem actualPopulationInclusionMass_bounds (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (j : ℕ) :
    0 ≤ actualPopulationInclusionMass Γ j ∧ actualPopulationInclusionMass Γ j ≤ 1 := by
  rw [actualPopulationInclusionMass_eq_prob Γ hm]
  exact ⟨FiniteLaw.prob_nonneg _ _, FiniteLaw.prob_le_one _ _⟩

theorem actualRouteMass_total (Γ : FiniteGame m n c Seed) :
    (∑ j ∈ Finset.Icc 0 n, actualRouteMass Γ j) = 1 := by
  classical
  simp_rw [actualRouteMass_eq_integral_indicator]
  calc
    _ = ∫ x, ∑ j ∈ Finset.Icc 0 n, actualChosenIndicator j x ∂(Γ.F ⊗ₘ Γ.σ) := by
      symm
      exact integral_finsetSum _ (fun j _ => actualChosenIndicator_integrable Γ j)
    _ = ∫ _x : ℝ × JointAction n, (1 : ℝ) ∂(Γ.F ⊗ₘ Γ.σ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      have hmem : x.2.routeCount ∈ Finset.Icc 0 n :=
        Finset.mem_Icc.mpr ⟨Nat.zero_le _, x.2.routeCount_le⟩
      calc
        _ = actualChosenIndicator x.2.routeCount x := by
          apply Finset.sum_eq_single x.2.routeCount
          · intro j _ hj
            simp only [actualChosenIndicator, if_neg (Ne.symm hj)]
          · intro hnot
            exact (hnot hmem).elim
        _ = 1 := by simp only [actualChosenIndicator, if_true]
    _ = 1 := by simp

theorem actualRouteMass_zero_add_positive (Γ : FiniteGame m n c Seed) :
    actualRouteMass Γ 0 + (∑ j ∈ Finset.Icc 1 n, actualRouteMass Γ j) = 1 := by
  classical
  have hset : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
  have hh := actualRouteMass_total Γ
  rwa [hset, Finset.sum_insert hnot] at hh

theorem zero_route_tendsto_of_participation
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) {h : ℝ}
    (hp : Tendsto (fun t => ∑ j ∈ Finset.Icc 1 n, actualRouteMass (Γ t) j)
      atTop (𝓝 h)) :
    Tendsto (fun t => actualRouteMass (Γ t) 0) atTop (𝓝 (1-h)) := by
  have hs := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp
  apply hs.congr'
  filter_upwards [] with t
  have hh := actualRouteMass_zero_add_positive (Γ t)
  linarith

theorem routeLimit_zero_of_participation
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) {h : ℝ} {pi : ℕ → ℝ}
    (hp : RouteLimit Γ pi)
    (hpart : Tendsto (fun t => ∑ j ∈ Finset.Icc 1 n, actualRouteMass (Γ t) j)
      atTop (𝓝 h)) : pi 0 = 1-h := by
  exact tendsto_nhds_unique (hp 0 (by simp))
    (zero_route_tendsto_of_participation Γ hpart)

theorem actual_countLaw_zero_add_success (μ : CountLaw n) :
    μ.prob (fun r => r.val = 0) + μ.success = 1 := by
  classical
  have hs : μ.success = μ.prob (fun r => r.val ≠ 0) := by
    rw [CountLaw.success, FiniteLaw.prob_eq_expect]
    apply μ.expect_congr
    intro r
    by_cases hr : r.val = 0 <;> simp [successIndicator, hr]
  have hh := μ.prob_compl (fun r => r.val = 0)
  rw [← hs] at hh
  linarith

theorem actualPopulationInclusionMass_zero_add_coverage
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    actualPopulationInclusionMass Γ 0 + finiteCoverage Γ = 1 := by
  rw [actualPopulationInclusionMass_eq_prob Γ hm, ← actualPopulationCountLaw_success Γ hm]
  exact actual_countLaw_zero_add_success _

theorem population_zero_tendsto_of_coverage
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : ∀ᶠ t in atTop, 0 < M t) {Q : ℝ}
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q)) :
    Tendsto (fun t => actualPopulationInclusionMass (Γ t) 0) atTop (𝓝 (1-Q)) := by
  have hs := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hQ
  apply hs.congr'
  filter_upwards [hM] with t ht
  have hh := actualPopulationInclusionMass_zero_add_coverage (Γ t) ht
  linarith

theorem finiteLoad_tendsto_of_population_counts
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : ∀ᶠ t in atTop, 0 < M t) (q : ℕ → ℝ)
    (hq : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => actualPopulationInclusionMass (Γ t) j) atTop (𝓝 (q j))) :
    Tendsto (fun t => finiteLoad (Γ t)) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * q j)) := by
  have hs := tendsto_finsetSum (Finset.Icc 1 n)
    (fun j hj => (hq j hj).const_mul (j : ℝ))
  apply hs.congr'
  filter_upwards [hM] with t ht
  exact (load_as_finite_count_sum (Γ t) ht).symm

theorem finiteCoverage_tendsto_of_population_counts
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : ∀ᶠ t in atTop, 0 < M t) (q : ℕ → ℝ)
    (hq : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => actualPopulationInclusionMass (Γ t) j) atTop (𝓝 (q j))) :
    Tendsto (fun t => finiteCoverage (Γ t)) atTop
      (𝓝 (∑ j ∈ Finset.Icc 1 n, q j)) := by
  have hs := tendsto_finsetSum (Finset.Icc 1 n) hq
  apply hs.congr'
  filter_upwards [hM] with t ht
  exact (coverage_as_finite_count_sum (Γ t) ht).symm

theorem finiteMultiplicity_tendsto_of_load_coverage
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    {L Q : ℝ} (hL : Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 L))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q)) (hQ0 : Q ≠ 0) :
    Tendsto (fun t => finiteMultiplicity (Γ t)) atTop (𝓝 (L / Q)) :=
  hL.div hQ hQ0

theorem conditional_population_count_tendsto
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    {j : ℕ} {p Q : ℝ}
    (hp : Tendsto (fun t => actualPopulationInclusionMass (Γ t) j) atTop (𝓝 p))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q)) (hQ0 : Q ≠ 0) :
    Tendsto (fun t => actualPopulationInclusionMass (Γ t) j / finiteCoverage (Γ t))
      atTop (𝓝 (p / Q)) := hp.div hQ hQ0

end FCAppendix.Bayes
